package org.arend.mcp.libcompactifier

import org.arend.core.definition.ClassField
import org.arend.core.definition.FunctionDefinition
import org.arend.core.definition.ClassDefinition as CoreClassDefinition
import org.arend.core.expr.ClassCallExpression
import org.arend.error.DummyErrorReporter
import org.arend.ext.concrete.definition.FunctionKind
import org.arend.ext.error.ListErrorReporter
import org.arend.ext.module.ModuleLocation
import org.arend.frontend.library.CliServerRequester
import org.arend.frontend.library.FileSourceLibrary
import org.arend.frontend.library.LibraryManager
import org.arend.frontend.library.SourceLibrary
import org.arend.frontend.source.PreludeResourceSource
import org.arend.naming.reference.Referable
import org.arend.naming.reference.TCDefReferable
import org.arend.naming.reference.UnresolvedReference
import org.arend.prelude.Prelude
import org.arend.server.ArendChecker
import org.arend.server.ArendServer
import org.arend.server.impl.ArendServerImpl
import org.arend.term.concrete.Concrete
import org.arend.term.concrete.ConcreteExpressionFactory
import org.arend.term.group.ConcreteGroup
import org.arend.term.group.ConcreteStatement
import org.arend.term.prettyprint.PrettyPrintVisitor
import org.arend.server.ProgressReporter
import org.arend.typechecking.computation.UnstoppableCancellationIndicator
import org.arend.util.FileUtils
import java.nio.file.Files
import java.nio.file.Path
import java.nio.file.Paths
import java.util.Objects
import java.util.function.Supplier
import kotlin.system.exitProcess

object ArendProofCutter {

    /**
     * Returns true if the given ClassFieldImpl's implemented field has a proposition type
     * (i.e., its typechecked result type level is -1).
     */
    private fun isPropositionClassField(field: ClassField): Boolean {
        // resultTypeLevel is a BigInteger upstream; a negative h-level means \Prop, matching
        // SortExpression.isProp(). Previously this compared against the Int -1.
        if (field.resultTypeLevel?.signum()?.let { it < 0 } == true) return true
        if (field.isProperty) return true
        // Check the sort of the field's type in the parent class
        // The parent class sort tracks which fields are Prop
        val parentClass = field.parentClass
        val fieldType = parentClass.getFieldType(field)
        if (fieldType != null) {
            val codomain = fieldType.codomain
            try {
                val sort = codomain?.getSortOfType()
                if (sort != null && sort.isProp) return true
            } catch (_: Exception) {}
        }
        return false
    }

    /**
     * Resolves a reference to a class field to the typechecked [ClassField], if possible.
     */
    private fun resolveClassField(ref: Referable?): ClassField? {
        var r: Referable? = ref
        if (r is UnresolvedReference && r.isResolved) {
            r = r.resolve(null, null, null, null)
        }
        return (r as? TCDefReferable)?.typechecked as? ClassField
    }

    private fun isPropositionField(fieldImpl: Concrete.ClassFieldImpl): Boolean {
        val classField = resolveClassField(fieldImpl.implementedField)
        return classField != null && isPropositionClassField(classField)
    }

    /**
     * Returns the class field implemented by a coclause function definition (`| f x => ...` in a
     * `\cowith` body or `\default f x => ...` in a class), or null if it cannot be determined.
     *
     * The implemented field is only stored on [Concrete.CoClauseFunctionDefinition]; depending on
     * how the group was built, a coclause may instead be a plain [Concrete.FunctionDefinition] that
     * merely has a coclause kind, so we also consult the typechecked definition and, failing that,
     * match by name against the class the enclosing definition implements.
     */
    private fun implementedClassField(def: Concrete.BaseFunctionDefinition): ClassField? {
        if (def is Concrete.CoClauseFunctionDefinition) {
            resolveClassField(def.implementedField)?.let { return it }
        }
        val typechecked = def.data?.typechecked
        if (typechecked is FunctionDefinition) {
            (typechecked.implementedField?.typechecked as? ClassField)?.let { return it }
        }
        val fieldName = def.data?.refName ?: return null
        return enclosingClassOf(def)?.findField { it.name == fieldName }
    }

    /**
     * The class whose fields a coclause definition implements: either the class extended by the
     * enclosing instance/function, or the enclosing class itself for `\default` coclauses.
     */
    private fun enclosingClassOf(def: Concrete.BaseFunctionDefinition): CoreClassDefinition? {
        val parents = listOfNotNull(
            def.useParent,
            def.data?.locatedReferableParent as? TCDefReferable
        )
        for (parent in parents) {
            when (val parentDef = parent.typechecked) {
                is CoreClassDefinition -> return parentDef
                is FunctionDefinition -> (parentDef.resultType as? ClassCallExpression)?.definition?.let { return it }
                else -> {}
            }
        }
        return null
    }

    /**
     * True if the coclause's own typechecked result type is a proposition. Used as a fallback when
     * the implemented field cannot be resolved.
     */
    private fun hasPropositionResultType(def: Concrete.BaseFunctionDefinition): Boolean {
        val typechecked = def.data?.typechecked as? FunctionDefinition ?: return false
        return try {
            typechecked.resultType?.sortOfType?.isProp == true
        } catch (_: Exception) {
            false
        }
    }

    /**
     * Replaces implementations of propositional fields with a goal inside a class extension term
     * (`C { | f => ... }`, possibly wrapped in `\new`), recursively.
     *
     * A definition converted back from core by `ToAbstractVisitor` represents an instance body this
     * way — a [Concrete.TermFunctionBody] holding a [Concrete.NewExpression] — rather than as a
     * [Concrete.CoelimFunctionBody], so its coclauses are not reachable through the other branches.
     */
    private fun cutPropositionalCoclauses(expr: Concrete.Expression?) {
        val classExt = when (expr) {
            is Concrete.NewExpression -> expr.expression as? Concrete.ClassExtExpression
            is Concrete.ClassExtExpression -> expr
            else -> null
        } ?: return
        for (element in classExt.statements) {
            if (element is Concrete.CoClauseFunctionReference) continue
            if (isPropositionField(element)) {
                element.implementation = ConcreteExpressionFactory.cGoal("hidden_proof", null)
            } else {
                cutPropositionalCoclauses(element.implementation)
            }
        }
    }

    fun cutProofs(def: Concrete.GeneralDefinition?): Concrete.GeneralDefinition? {
        // A `\cowith` definition (in particular every `\instance`) keeps its implementations in the
        // result type rather than in the body once it has been converted back from core, so the
        // coclauses to cut live there. A lemma is cut wholesale below, and its statement must stay.
        if (def is Concrete.BaseFunctionDefinition && def.kind != FunctionKind.LEMMA) {
            cutPropositionalCoclauses(def.resultType)
        }
        return when {
            def is Concrete.BaseFunctionDefinition && def.kind == FunctionKind.LEMMA -> {
                val emptyBody = Concrete.TermFunctionBody(null, ConcreteExpressionFactory.cGoal("hidden_proof", null))
                def.copy(def.parameters, emptyBody)
            }
            /* def is Concrete.BaseFunctionDefinition && def.kind == FunctionKind.INSTANCE -> {
                val coElimBody = def.body as? Concrete.CoelimFunctionBody
                if coElimBody == null { def }
                else {

                }
            } */
            def is Concrete.BaseFunctionDefinition && def.kind.isCoclause -> {
                val classField = implementedClassField(def)
                if ((classField != null && isPropositionClassField(classField)) || hasPropositionResultType(def)) {
                    val emptyBody = Concrete.TermFunctionBody(null, ConcreteExpressionFactory.cGoal("hidden_proof", null))
                    def.copy(def.parameters, emptyBody)
                } else def
            }
            def is Concrete.BaseFunctionDefinition && def.body is Concrete.CoelimFunctionBody -> {
                val coelimBody = def.body as Concrete.CoelimFunctionBody
                val typecheckedDef = def.data?.typechecked
                val targetClass = if (typecheckedDef is FunctionDefinition) {
                    (typecheckedDef.resultType as? ClassCallExpression)?.definition
                } else null
                for (element in coelimBody.coClauseElements) {
                    if (element is Concrete.ClassFieldImpl && element !is Concrete.CoClauseFunctionReference) {
                        val fieldName = element.implementedField.textRepresentation()
                        val classField = resolveClassField(element.implementedField)
                            ?: targetClass?.findField { it.name == fieldName }
                        if (classField != null && isPropositionClassField(classField)) {
                            element.implementation = ConcreteExpressionFactory.cGoal("hidden_proof", null)
                        }
                    }
                }
                def
            }
            def is Concrete.BaseFunctionDefinition && def.body is Concrete.TermFunctionBody -> {
                cutPropositionalCoclauses((def.body as Concrete.TermFunctionBody).term)
                def
            }
            def is Concrete.ClassDefinition -> {
                for (element in def.elements) {
                    if (element is Concrete.ClassFieldImpl && element !is Concrete.CoClauseFunctionReference && isPropositionField(element)) {
                        element.implementation = ConcreteExpressionFactory.cGoal("hidden_proof", null)
                    }
                }
                def
            }
            else -> def
        }
    }

    /**
     * Takes a parsed ConcreteGroup and returns a new ConcreteGroup with all proof bodies removed.
     * For each BaseFunctionDefinition, the body is replaced with a goal.
     * For each ClassDefinition, ClassFieldImpl implementations whose field type is a proposition
     * are replaced with a goal.
     */
    fun cutProofs(group: ConcreteGroup, checker: ArendChecker): ConcreteGroup {
        val newStatements = group.statements().map { stmt ->
            if (stmt.group() != null) {
                ConcreteStatement(cutProofs(stmt.group()!!, checker), stmt.command())
            } else {
                stmt
            }
        }
        val newDynamicGroups = group.dynamicGroups().map { cutProofs(it, checker) }

        val def = group.definition()
        val newDef: Concrete.ResolvableDefinition? = cutProofs(def) as? Concrete.ResolvableDefinition

        return ConcreteGroup(group.description(), group.referable(), newDef, newStatements, newDynamicGroups, group.externalParameters())
    }

    /**
     * Takes a ConcreteGroup, cuts all proofs, and returns the pretty-printed result.
     */
    fun cutProofsAndPrint(group: ConcreteGroup, checker: ArendChecker): String {
        val cut = cutProofs(group, checker)
        val builder = StringBuilder()
        val visitor = PrettyPrintVisitor(builder, 0)
        visitor.printStatements(cut.statements())
        return builder.toString()
    }

    @JvmStatic
    fun main(args: Array<String>) {
        try {
            val libDir: Path = args.firstOrNull()?.let { Paths.get(it) } ?: return
            val libraryManager = LibraryManager(ListErrorReporter())
            val server: ArendServer = ArendServerImpl(CliServerRequester(libraryManager), false, false, true)
            server.addReadOnlyModule(
                Prelude.MODULE_LOCATION,
                Supplier { Objects.requireNonNull<ConcreteGroup?>(PreludeResourceSource().loadGroup(DummyErrorReporter.INSTANCE)) })
            server.addErrorReporter(ListErrorReporter())

            val library: SourceLibrary =
                FileSourceLibrary.fromConfigFile(libDir.resolve(FileUtils.LIBRARY_CONFIG_FILE), false, ListErrorReporter())

            libraryManager.updateLibrary(library, server)
            for (modulePath in library.findModules(false)) {
                val module = ModuleLocation(
                    library.libraryName,
                    ModuleLocation.LocationKind.SOURCE,
                    modulePath
                )
                library.getSource(modulePath, false)?.load(server, ListErrorReporter())
                val group: ConcreteGroup = server.getRawGroup(module) ?: exitProcess(1)
                val checker = server.getCheckerFor(listOf(module))
                checker.resolveAll(UnstoppableCancellationIndicator.INSTANCE, ProgressReporter.empty())
                checker.typecheck(UnstoppableCancellationIndicator.INSTANCE, ProgressReporter.empty())

                val result = cutProofsAndPrint(group, checker)
                val outPath = libDir.resolve(".compactifiedLib").let { base ->
                    FileUtils.sourceFile(base, modulePath)
                }
                Files.createDirectories(outPath.parent)
                Files.writeString(outPath, result)
            }
        } catch (e: Exception) {
            e.printStackTrace()
        }
    }
}