import org.json.JSONObject
import org.apache.commons.cli.*
import org.arend.core.definition.CallableDefinition
import org.arend.core.definition.ClassDefinition
import org.arend.core.expr.ClassCallExpression
import org.arend.core.expr.DefCallExpression
import org.arend.core.expr.Expression
import org.arend.core.expr.ReferenceExpression
import org.arend.core.expr.visitor.FreeVariablesCollector
import org.arend.error.DummyErrorReporter
import org.arend.ext.core.expr.CoreExpression
import org.arend.ext.error.ListErrorReporter
import org.arend.ext.module.FullName
import org.arend.ext.module.ModuleLocation
import org.arend.ext.prettyprinting.PrettyPrinterConfig
import org.arend.frontend.library.CliServerRequester
import org.arend.frontend.library.FileSourceLibrary
import org.arend.frontend.library.LibraryManager
import org.arend.frontend.library.SourceLibrary
import org.arend.frontend.source.PreludeResourceSource
import org.arend.prelude.Prelude
import org.arend.server.ArendServer
import org.arend.server.ProgressReporter
import org.arend.server.impl.ArendServerImpl
import org.arend.term.abs.Abstract
import org.arend.term.concrete.Concrete
import org.arend.term.concrete.Concrete.ResolvableDefinition
import org.arend.term.group.ConcreteGroup
import org.arend.term.prettyprint.ToAbstractVisitor
import org.arend.typechecking.computation.UnstoppableCancellationIndicator
import org.arend.typechecking.visitor.CheckTypeVisitor
import org.arend.typechecking.visitor.SearchVisitor
import org.arend.util.FileUtils
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
  expr.accept(object : SearchVisitor<Void>() {
    override fun processDefCall(expression: DefCallExpression, param: Void?): CoreExpression.FindAction {
      val name = expression.definition.name
      if (!listOf("Path", "I", "at", "Array", "DArray").contains(name) && expression.definition !is ClassDefinition) {
        defs.add(expression.definition)
      }
      return super.processDefCall(expression, param)
    }
  }, null)
}

private fun computePremisesAndContext(subexprs: List<SubexprEnvironment>) {
  for (expr in subexprs) {
    val relevantContext = HashSet(FreeVariablesCollector.getFreeVariables(expr.coreSubExpr))
    relevantContext.addAll(FreeVariablesCollector.getFreeVariables(expr.expectedType))
    expr.context = relevantContext

    val premises: MutableSet<CallableDefinition> = HashSet()

    collectDefinitions(expr.coreSubExpr, premises)
    collectDefinitions(expr.expectedType, premises)

    expr.premises = premises
  }
}

private fun writeToJson(subexprs: List<SubexprEnvironment>, steps: List<String>) {
  val jsonEntries = ArrayList<JSONObject>()
  for (i in 0..<subexprs.size) {
    val json = JSONObject()
    json.put("Expected type", subexprs[i].expectedType.toString())
    json.put("Context", subexprs[i].context.map {
      val type = it.type.expr.toString()
      if (it.type.expr is ClassCallExpression) it.name + " : " + type.substringBefore("{") else it.name + " : " + type
    })
    json.put("Premises", subexprs[i].premises.map {
      if (!steps[i].contains(it.name) && !subexprs[i].expectedType.toString().contains(it.name)) return@map ""
      val premiseDoc =
        ToAbstractVisitor.convert(it, PrettyPrinterConfig.DEFAULT).prettyPrint(PrettyPrinterConfig.DEFAULT)
      val premiseStr = if (it is ClassDefinition) "$premiseDoc".substringBefore("{") else "$premiseDoc"
      if (premiseStr.startsWith("\\instance") && premiseStr.length > 200) "" else premiseStr
    }.filter { it.isNotBlank() })
    json.put("Expression", steps[i])
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
    for (library in requestedLibraries) {
      libraryManager.updateLibrary(library, server)
      for (modulePath in library.findModules(false)) {
        val module = ModuleLocation(
          library.libraryName,
          ModuleLocation.LocationKind.SOURCE,
          modulePath
        )
        val checker = server.getCheckerFor(
          listOf(module)
        )
        library.getSource(modulePath, false)?.load(server, ListErrorReporter())
        val group: ConcreteGroup = server.getRawGroup(module) ?: exitProcess(1)

        group.traverseGroup { x ->
          x.definition?.let {
            checker.typecheck(
              FullName(module, it.data.refLongName),
              { errorReporter, pool, arendExtension, listener ->
                SubexprCollector(
                  errorReporter,
                  pool,
                  arendExtension,
                  collectedExpressions,
                  concreteToCore
                )
              },
              null, ListErrorReporter(), UnstoppableCancellationIndicator.INSTANCE,
              ProgressReporter.empty<List<ResolvableDefinition?>>()
            )
          }
        }
      }
    }

    var goals: MutableSet<String> = HashSet()

    val filteredExpressions = collectedExpressions.filter { expr ->
      val expType = expr.expectedType.toString()
      val seenGoal = goals.contains(expType)
      if (!seenGoal) {
        goals.add(expType)
      }
      !seenGoal
    }

    computePremisesAndContext(filteredExpressions)

    println(filteredExpressions.size)

    val steps = ArrayList<String>()
    val finalExpressions = ArrayList<SubexprEnvironment>()

    for (expr in filteredExpressions) {
      val step = extractStep(expr.subExpr, concreteToCore) ?: continue
      val stepStr = step.toString().replace("{this}", "")
      /*if (stepStr == expr.subExpr.toString()) {
        println(stepStr)
        println("type 'q' to quit and anything else to continue")
        val input = readln()
        if (input == "q") {
          break
        }
      }*/
      if (stepStr.length < 200 && expr.expectedType.toString().length < 400) {
        steps.add(stepStr)
        finalExpressions.add(expr)
      }
    }

    println(finalExpressions.size)

    writeToJson(finalExpressions, steps)

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
          print(binding.name + " : " + binding.type.expr + ", ")
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