import org.apache.commons.cli.*
import org.arend.core.context.binding.EvaluatingBinding
import org.arend.core.definition.CallableDefinition
import org.arend.core.definition.ClassDefinition
import org.arend.core.definition.ClassField
import org.arend.core.definition.Constructor
import org.arend.core.expr.ClassCallExpression
import org.arend.core.expr.DefCallExpression
import org.arend.core.expr.Expression
import org.arend.core.expr.UniverseExpression
import org.arend.core.expr.visitor.FreeVariablesCollector
import org.arend.core.sort.Sort
import org.arend.core.subst.InPlaceLevelSubstVisitor
import org.arend.error.DummyErrorReporter
import org.arend.ext.concrete.expr.ConcreteExpression
import org.arend.ext.core.expr.CoreExpression
import org.arend.ext.core.ops.NormalizationMode
import org.arend.ext.error.ErrorReporter
import org.arend.ext.error.ListErrorReporter
import org.arend.ext.module.FullName
import org.arend.ext.module.LongName
import org.arend.ext.module.ModuleLocation
import org.arend.ext.module.ModulePath
import org.arend.ext.prettyprinting.PrettyPrinterConfig
import org.arend.extImpl.ConcreteFactoryImpl
import org.arend.frontend.library.CliServerRequester
import org.arend.frontend.library.FileSourceLibrary
import org.arend.frontend.library.LibraryManager
import org.arend.frontend.library.SourceLibrary
import org.arend.frontend.source.PreludeResourceSource
import org.arend.frontend.symbol.SignaturePrintVisitor
import org.arend.mcp.libcompactifier.ArendProofCutter
import org.arend.naming.reference.Referable
import org.arend.naming.reference.TCDefReferable
import org.arend.naming.scope.Scope
import org.arend.naming.scope.ScopeFactory
import org.arend.prelude.Prelude
import org.arend.server.ArendChecker
import org.arend.server.ArendServer
import org.arend.server.ProgressReporter
import org.arend.server.impl.ArendServerImpl
import org.arend.term.concrete.Concrete
import org.arend.term.concrete.SearchConcreteVisitor
import org.arend.term.group.ConcreteGroup
import org.arend.term.prettyprint.ToAbstractVisitor
import org.arend.typechecking.computation.UnstoppableCancellationIndicator
import org.arend.typechecking.visitor.ArendCheckerFactory
import org.arend.typechecking.visitor.SearchVisitor
import org.arend.util.FileUtils
import org.json.JSONObject
import java.io.File
import java.nio.file.Path
import java.nio.file.Paths
import java.util.*
import java.util.function.Supplier
import kotlin.system.exitProcess

private fun parseArgs(args: Array<String>): CommandLine? {
  try {
    val cmdOptions = Options()
    cmdOptions.addOption(
      Option.builder("L").longOpt("libdir").hasArg().argName("dir").desc("directory containing libraries").build()
    )

    return DefaultParser().parse(cmdOptions, args)
  } catch (e: ParseException) {
    System.err.println(e.message)
    return null
  }
}

private fun collectDefinitions(expr: Expression, defs: MutableSet<CallableDefinition>) {
  val exprPrinted = expr.toString()
  expr.accept(object : SearchVisitor<Void>() {
    override fun processDefCall(expression: DefCallExpression, param: Void?): CoreExpression.FindAction {
      val name = expression.definition.name
      if (!listOf("Path", "I", "at", "Array", "DArray").contains(name)) { // && expression.definition !is ClassDefinition) {
        if (exprPrinted.contains(name)) {
          defs.add(expression.definition)
        }
      }
      return super.processDefCall(expression, param)
    }
  }, null)
}

private fun collectDefinitionsConcrete(expr: ConcreteExpression, nameResolver: MyNameResolver, defs: MutableSet<CallableDefinition>) {
  if (expr !is Concrete.Expression) return
  expr.accept(object : SearchConcreteVisitor<Void, Void?>() {
    override fun visitReference(expression: Concrete.ReferenceExpression, param: Void?): Void? {
      val definition = nameResolver.resolveReferable(expression.referent)
      if (definition != null) {
        val name = definition.name
        if (!listOf("Path", "I", "at", "Array", "DArray").contains(name) && definition !is ClassDefinition) {
          defs.add(definition)
        }
      }
      return super.visitReference(expression, param)
    }

    override fun visitClassFieldImpl(fieldImpl: Concrete.ClassFieldImpl?, params: Void?): Void? {
      return null
    }
  }, null)
}

class MyNameResolver(private val checker: ArendChecker, private val server: ArendServer, private val modulePath: ModulePath, private val libName: String) {
  private fun ensureTypechecked(tcReferable: TCDefReferable, errorReporter: ErrorReporter) {
    if (tcReferable.typechecked != null) return

    // 1. Get the FullName of the referable
    val fullName = tcReferable.refFullName
    val module = fullName.module ?: return

    // 2. Get a checker for the module containing this definition
    val checker = server.getCheckerFor(listOf(module))

    // 3. Trigger typechecking via the public API
    // This will typecheck the definition and all its dependencies
    checker.typecheck(
      listOf(fullName),
      errorReporter,
      UnstoppableCancellationIndicator.INSTANCE,
      ProgressReporter.empty()
    )
  }

  fun stringToCallableDefinition(fullName: String): CallableDefinition? {
    checker.resolveModules(UnstoppableCancellationIndicator.INSTANCE, ProgressReporter.empty())
    val moduleLocation = server.findModule(modulePath, libName, false, true) ?: return null
    val group = server.getRawGroup(moduleLocation) ?: return null
    val moduleScopeProvider = server.getModuleScopeProvider(libName, false)
    val scope = ScopeFactory.forGroup(group, moduleScopeProvider)
    val path = LongName.fromString(fullName).toList()
    val referable = Scope.resolveName(scope, path)
    val tcReferable = referable as? TCDefReferable
      ?: (referable as? org.arend.ext.reference.DataContainer)?.data as? TCDefReferable
      ?: return null

    var definition = tcReferable.typechecked // goal.typechecker.getCoreDefinition(tcReferable)
    if (definition == null) {
      ensureTypechecked(tcReferable, ListErrorReporter())
      definition = tcReferable.typechecked
    }

    return definition as? CallableDefinition
  }

  fun resolveReferable(referable: Referable): CallableDefinition? {
    val tcReferable = referable as? TCDefReferable
      ?: (referable as? org.arend.ext.reference.DataContainer)?.data as? TCDefReferable
      ?: return null

    var definition = tcReferable.typechecked
    if (definition == null) {
      ensureTypechecked(tcReferable, ListErrorReporter())
      definition = tcReferable.typechecked
    }

    return definition as? CallableDefinition
  }
}

private fun computePremisesAndContext(subexprs: List<SubexprEnvironment>, nameResolver: MyNameResolver) {
  for (expr in subexprs) {
    val relevantContext = HashSet(FreeVariablesCollector.getFreeVariables(expr.coreSubExpr))
    relevantContext.addAll(FreeVariablesCollector.getFreeVariables(expr.expectedType))
    expr.context = relevantContext

    val premises: MutableSet<CallableDefinition> = HashSet()

    collectDefinitions(expr.coreSubExpr, premises)
    collectDefinitions(expr.expectedType, premises)
    collectDefinitionsConcrete(expr.subExpr, nameResolver, premises)

    for (x in relevantContext) {
      collectDefinitions(x.type, premises)
    }

    expr.premises = premises
  }
}

/**
 * Renders the premises of one entry.
 *
 * Classes and records are NOT printed as classes: each one is replaced by its fields,
 * and every field carries a "[field of A, B]" annotation naming every class RELEVANT TO
 * THIS ENTRY (see [relevantClasses]) that contains it — an inherited field is available
 * on each subclass, so `E` shows up as a field of BaseSet, Semigroup, Monoid and CMonoid
 * rather than only of the class declaring it. Fields collected directly from the
 * expression get the same annotation.
 */
private fun renderPremises(env: SubexprEnvironment, server: ArendServer): List<String> {
  val premises = env.premises

  // Directly used fields first, then the remaining fields of the class premises they
  // were collected from; a field is listed once, with all of its owning classes.
  val fields = LinkedHashSet<ClassField>(premises.filterIsInstance<ClassField>())
  for (classDef in premises.filterIsInstance<ClassDefinition>()) fields.addAll(classDef.allFields)

  val classes = relevantClasses(env, fields)

  val lines = ArrayList<String>()
  for (premise in premises) {
    if (premise is ClassDefinition || premise is ClassField) continue
    lines.add(renderPremise(premise, server))
  }
  for (field in fields) {
    val rendered = renderPremise(field, server)
    if (rendered.isBlank()) continue
    lines.add(rendered.trimEnd() + "  [field of " + fieldOwners(field, classes).joinToString(", ") + "]")
  }
  return lines.filter { it.isNotBlank() }
}

/**
 * The classes in play for one entry: those mentioned by it — class premises, the classes
 * declaring the printed fields, the classes those fields are typed by (`| M : CMonoid`),
 * and the classes occurring in the expected type or in a context binding's type — closed
 * under superclasses, since a superclass of a relevant class is relevant as well.
 *
 * Ordered from the most general to the most specific (a class always precedes its
 * subclasses), so that a field annotation reads BaseSet, Semigroup, Monoid, CMonoid.
 */
private fun relevantClasses(env: SubexprEnvironment, fields: Collection<ClassField>): List<ClassDefinition> {
  val mentioned = LinkedHashSet<ClassDefinition>()

  for (premise in env.premises) {
    if (premise is ClassDefinition) mentioned.add(premise)
    if (premise is ClassField) mentioned.add(premise.parentClass)
  }
  for (field in fields) {
    mentioned.add(field.parentClass)
    field.type?.codomain?.let { collectClasses(it, mentioned) }
  }
  collectClasses(env.expectedType, mentioned)
  for (binding in env.context) collectClasses(binding.type, mentioned)

  val closure = LinkedHashSet<ClassDefinition>()
  for (classDef in mentioned) addWithSuperClasses(classDef, closure)
  return closure.sortedWith(compareBy({ superClassCount(it) }, { it.name ?: "" }))
}

private fun addWithSuperClasses(classDef: ClassDefinition, out: MutableSet<ClassDefinition>) {
  if (!out.add(classDef)) return
  for (superClass in classDef.superClasses) addWithSuperClasses(superClass, out)
}

private fun superClassCount(classDef: ClassDefinition): Int {
  val supers = LinkedHashSet<ClassDefinition>()
  addWithSuperClasses(classDef, supers)
  return supers.size
}

private fun collectClasses(expr: Expression, out: MutableSet<ClassDefinition>) {
  expr.accept(object : SearchVisitor<Void>() {
    override fun processDefCall(expression: DefCallExpression, param: Void?): CoreExpression.FindAction {
      (expression.definition as? ClassDefinition)?.let { out.add(it) }
      return super.processDefCall(expression, param)
    }
  }, null)
}

/** The classes a field can be accessed on: the one declaring it, then the relevant classes containing it. */
private fun fieldOwners(field: ClassField, classes: List<ClassDefinition>): List<String> {
  val owners = LinkedHashSet<String>()
  field.parentClass.name?.let { owners.add(it) }
  for (classDef in classes) {
    if (classDef.containsField(field)) classDef.name?.let { owners.add(it) }
  }
  return owners.toList()
}

private fun renderPremise(premise: CallableDefinition, server: ArendServer): String {
  val module = premise.ref.location ?: return ""
  val checker = server.getCheckerFor(listOf(module))

  val group: ConcreteGroup = server.getRawGroup(module) ?: exitProcess(1)

  group.traverseGroup { x ->
    x.definition?.let {
      checker.typecheck(
        FullName(module, it.data.refLongName),
        ArendCheckerFactory.DEFAULT,
        null, ListErrorReporter(), UnstoppableCancellationIndicator.INSTANCE,
        ProgressReporter.empty()
      )
    }
  }

  val concreteDef = ToAbstractVisitor.convert(premise, PrettyPrinterConfig.DEFAULT)
  val truncatedDef = ArendProofCutter.cutProofs(concreteDef) ?: return ""
  // SignaturePrintVisitor.render(truncatedDef)
  val premiseDoc = truncatedDef.prettyPrint(PrettyPrinterConfig.DEFAULT)
  val premiseStr =
    if (premise is Constructor) "$premiseDoc : " + premise.getDataTypeExpression(premise.makeIdLevels())
    else "$premiseDoc"
  return if (premiseStr.startsWith("\\instance") && premiseStr.length > 200) "" else premiseStr
}

private fun writeToJson(subexprs: List<SubexprEnvironment>, tactics: List<String>, server: ArendServer) {
  val jsonEntries = ArrayList<JSONObject>()
  for (i in 0..<subexprs.size) {
    val json = JSONObject()
    json.put("Expected type", subexprs[i].expectedType.normalize(NormalizationMode.RNF).toString())
    json.put("Context", subexprs[i].context.map {
      val type = it.type.normalize(NormalizationMode.RNF).toString()
      val bind = if (it.type is ClassCallExpression) it.name + " : " + type.substringBefore("{") else it.name + " : " + type
      if (it is EvaluatingBinding) bind + " => " + it.expression else bind
    })
    json.put("Premises", renderPremises(subexprs[i], server))
    val lemmaConcrete = ToAbstractVisitor.convert(subexprs[i].lemma, PrettyPrinterConfig.DEFAULT)
    val lemmaSignature = if (lemmaConcrete is Concrete.FunctionDefinition) {
      val factory = ConcreteFactoryImpl(lemmaConcrete.data)
      val sigDef = factory.function(
        lemmaConcrete.ref,
        lemmaConcrete.kind,
        lemmaConcrete.parameters,
        lemmaConcrete.resultType,
        lemmaConcrete.resultTypeLevel,
        factory.body(factory.goal())
      )
      sigDef.prettyPrint(PrettyPrinterConfig.DEFAULT).toString().substringBefore("=> {?}").trim()
    } else {
      lemmaConcrete.prettyPrint(PrettyPrinterConfig.DEFAULT).toString()
    }
    // json.put("Lemma", lemmaSignature)
    json.put("Tactic", tactics[i])
    jsonEntries.add(json)
  }

  val file = File("data.json")
  file.printWriter().use { out ->
    jsonEntries.forEach { obj ->
      out.println(obj.toString(4))
    }
  }
}

fun main(args: Array<String>) {
  try {
    val cmdLine: CommandLine = parseArgs(args) ?: exitProcess(1)
    val libDir: Path = Paths.get(cmdLine.getOptionValues("L")[0])

    val libraryManager = LibraryManager(ListErrorReporter())
    val server: ArendServer = ArendServerImpl(CliServerRequester(libraryManager), false, false, true)
    server.addReadOnlyModule(
      Prelude.MODULE_LOCATION,
      Supplier { Objects.requireNonNull<ConcreteGroup?>(PreludeResourceSource().loadGroup(DummyErrorReporter.INSTANCE)) })
    server.addErrorReporter(ListErrorReporter())

    val requestedLibraries: MutableList<SourceLibrary> = ArrayList()

    val library: SourceLibrary =
      FileSourceLibrary.fromConfigFile(libDir.resolve(FileUtils.LIBRARY_CONFIG_FILE), false, ListErrorReporter())
    requestedLibraries.addLast(library)

    val collectedExpressions: MutableList<SubexprEnvironment> = ArrayList()
    val concreteToCore: MutableMap<Concrete.Expression, Expression> = HashMap()
    val defsToDissect = emptyList<String>()//listOf(
       //"nat_irr-isPrime", "prime-div", "prime-less", "isPrime=>prime")
    val modulesToDissect = listOf("Arith.Prime")
    var currentNameResolver: MyNameResolver? = null
    for (library in requestedLibraries) {
      libraryManager.updateLibrary(library, server)
      for (modulePath in library.findModules(false)) {
        val module = ModuleLocation(
          library.libraryName,
          ModuleLocation.LocationKind.SOURCE,
          modulePath
        )
        if (modulesToDissect.isNotEmpty() && !modulesToDissect.contains(modulePath.toString())) {
          continue
        }
        val checker = server.getCheckerFor(
          listOf(module)
        )
        currentNameResolver = MyNameResolver(checker, server, modulePath, library.libraryName)
        library.getSource(modulePath, false)?.load(server, ListErrorReporter())
        val group: ConcreteGroup = server.getRawGroup(module) ?: exitProcess(1)

        group.traverseGroup { x ->
          x.definition?.let {
            checker.typecheck(
              FullName(module, it.data.refLongName),
              { errorReporter, pool, arendExtension, _ ->
                SubexprCollector(
                  errorReporter,
                  pool,
                  arendExtension,
                  collectedExpressions,
                  concreteToCore,
                  defsToDissect,
                  modulesToDissect
                )
              },
              null, ListErrorReporter(), UnstoppableCancellationIndicator.INSTANCE,
              ProgressReporter.empty()
            )
          }
        }
      }
    }

    // var goals: MutableSet<String> = HashSet()
    val seenExprs: MutableSet<ConcreteExpression> = HashSet()

    for (expr in collectedExpressions) {
      println(expr.subExpr.toString().take(20))
    }

    val filteredExpressions = collectedExpressions.filter { expr ->
      // val expType = expr.expectedType.toString()
      // val seenGoal = goals.contains(expType)
      val seenExpr = seenExprs.contains(expr.subExpr)
      if (seenExpr || expr.expectedType.toString().startsWith("DArray") || expr.subExpr.toString().startsWith("solve")
        || expr.subExpr is Concrete.NewExpression) {
        false
      } else {
        seenExprs.add(expr.subExpr)
        val universeExpr = expr.expectedType.type.normalize(NormalizationMode.WHNF) as? UniverseExpression ?: return@filter false
        universeExpr.sortExpression.isProp
        //  || (universeExpr.sort.hLevel.`var`?.let { it is InferenceLevelVariable } ?: false)
      }
    }

    currentNameResolver?.let { computePremisesAndContext(filteredExpressions, it) }

    println(filteredExpressions.size)

    val tactics = ArrayList<String>()
    val finalExpressions = ArrayList<SubexprEnvironment>()
    var withoutTactic = 0

    for (expr in filteredExpressions) {
      val step = extractStep(expr.subExpr, concreteToCore) ?: continue
      // The step is emitted as a tactic, not as a term; entries the tactic format cannot
      // express are dropped.
      val tactic = currentNameResolver?.let { extractTactic(step, it, concreteToCore, expr.context) }
      if (tactic == null) {
        ++withoutTactic
        continue
      }
      tactics.add(tactic)
      finalExpressions.add(expr)
    }

    println(finalExpressions.size)
    println("$withoutTactic step(s) had no tactic representation and were dropped")

    for (tactic in tactics) {
      println(tactic.replace("\n", " "))
    }

    writeToJson(finalExpressions, tactics, server)

    /*
  while (true) {
      val ind = collectedExpressions.indices.random()
      println(ind)
      println("Expression:")
      println(collectedExpressions[ind].subExpr)
      println("Expected type:")
      println(collectedExpressions[ind].expectedType)
      println("Context:")
      for (binding in collectedExpressions[ind].context) {
          print(binding.name + " : " + binding.typeExpr + ", ")
      }
      println("\nPremises:")
      for (premise in collectedExpressions[ind].premises) {
          val premiseDoc = ToAbstractVisitor.convert(premise, PrettyPrinterConfig.DEFAULT).prettyPrint(PrettyPrinterConfig.DEFAULT)
          print("$premiseDoc, ")
      }
      println()
      println("type 'q' to quit and anything else to continue")
      val input = readln()
      if (input == "q") {
          break
      }
  }*/
  } catch (e: Exception) {
    e.printStackTrace()
  }
}