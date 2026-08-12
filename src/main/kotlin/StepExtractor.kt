import org.arend.core.expr.AppExpression
import org.arend.core.expr.ClassCallExpression
import org.arend.core.expr.DefCallExpression
import org.arend.core.expr.Expression
import org.arend.core.expr.UniverseExpression
import org.arend.ext.concrete.expr.ConcreteExpression
import org.arend.ext.core.ops.NormalizationMode
import org.arend.term.concrete.Concrete
import org.arend.term.concrete.ConcreteExpressionFactory

/** The metas of arend-lib that take the equality to rewrite with as an explicit argument. */
private val REWRITE_METAS = setOf("rewrite", "rewriteI", "rewriteEq")

fun extractStep(proof: ConcreteExpression, concreteToCore: Map<Concrete.Expression, Expression>): ConcreteExpression? {
  if (proof is Concrete.AppExpression) {
    val newArgs = ArrayList<Concrete.Argument>()
    if (proof.function.toString() == "mcases") {
      for (arg in proof.arguments) {
        val argExpr = arg.expression
        if (argExpr is Concrete.CaseExpression) {
          newArgs.add(Concrete.Argument(processCase(argExpr), arg.isExplicit))
        } else {
          newArgs.add(arg)
        }
      }
      return Concrete.AppExpression.make(null, proof.function, newArgs)
    }

    val coreArgs = ArrayList<Expression?>()

    for (arg in proof.arguments) {
      val coreArg = concreteToCore[arg.expression]
      //if (coreArg == null) {
        // println(proof)
        // println("didn't find arg")
        // return null
     // }
      coreArgs.add(coreArg)
    }

    // A rewrite meta READS its equality — `rewrite p t` needs p to know what to replace —
    // so that argument is kept even though it is a proof of a proposition. It is the first
    // EXPLICIT one: `rewrite {i_1, ... i_k} p t` pins occurrence indices before it.
    val equalityIdx = if (proof.function.toString() in REWRITE_METAS)
      proof.arguments.indexOfFirst { it.isExplicit } else -1

    var createdNewGoals = false
    for (i in 0..<proof.arguments.size) {
      if (i == equalityIdx) {
        newArgs.add(proof.arguments[i])
        continue
      }

      val coreArg = coreArgs[i]
      if (coreArg != null && coreArg.type !is ClassCallExpression) {
        val universeExpr = coreArg.type.type.normalize(NormalizationMode.WHNF)
        if (universeExpr is UniverseExpression && universeExpr.sortExpression.isProp) {
          if (proof.arguments[i].expression !is Concrete.ReferenceExpression) {
            val goal = ConcreteExpressionFactory.cGoal("", null)
            newArgs.add(Concrete.Argument(goal, proof.arguments[i].isExplicit))
            createdNewGoals = true
            continue
          }
        }
      }
      newArgs.add(proof.arguments[i])
    }
    if (createdNewGoals) {
      return Concrete.AppExpression.make(null, proof.function, newArgs)
    }
  } else if (proof is Concrete.LamExpression) {
    val goal = ConcreteExpressionFactory.cGoal("", null)
    return ConcreteExpressionFactory.cLam(proof.parameters, goal)
  } else if (proof is Concrete.CaseExpression) {
    return processCase(proof)
  } else if (proof is Concrete.TupleExpression) {
    val fieldSteps: MutableList<Concrete.Expression> = ArrayList()
    for (field in proof.fields) {
      val fieldStep = extractStep(field, concreteToCore) as? Concrete.Expression ?: return null
      fieldSteps.add(fieldStep)
    }
    return ConcreteExpressionFactory.cTuple(fieldSteps)
  } else if (proof is Concrete.ProjExpression) {
    val step = extractStep(proof.expression, concreteToCore) as? Concrete.Expression ?: return null
    return ConcreteExpressionFactory.cProj(step, proof.field)
  }
  return proof
}

fun processCase(case: Concrete.CaseExpression): Concrete.CaseExpression {
  val clauses = ArrayList<Concrete.FunctionClause>()
  for (clause in case.clauses) {
    val goal = ConcreteExpressionFactory.cGoal("", null)
    clauses.add(ConcreteExpressionFactory.cClause(clause.patterns, goal))
  }
  return ConcreteExpressionFactory.cCase(case.isSCase, case.arguments, case.resultType, case.resultTypeLevel, clauses)
}

fun getMatchedCoreArgs(args: List<Concrete.Argument>, coreArgs: List<Pair<Expression, Boolean>>): List<Expression>? {
  var concreteInd = 0
  var coreInd = 0
  val matchedArgs = ArrayList<Expression>()
  while (concreteInd < args.size && coreInd < coreArgs.size) {
    if (args[concreteInd].isExplicit && !coreArgs[coreInd].second) {
      ++coreInd
      continue
    }
    if (!args[concreteInd].isExplicit && coreArgs[coreInd].second) {
      //if (args[concreteInd].expression.toString() == "this") {
     //   ++concreteInd
     //   continue
     // }
      println("concrete implicit vs core explicit")
      return null
    }
    matchedArgs.add(coreArgs[coreInd].first)
    ++concreteInd
    ++coreInd
  }
  return matchedArgs
}

fun extractCoreArgsWithExplicitness(coreApp: Expression): List<Pair<Expression, Boolean>> {
  val args = mutableListOf<Pair<Expression, Boolean>>()
  var current: Expression? = coreApp
  while (current is AppExpression) {
    args.add(Pair(current.argument, current.isExplicit))
    current = current.function
  }

  if (current is DefCallExpression) {
    val defCallArgs = current.defCallArguments
    var curParam = current.definition.parameters
    val extraArgs = mutableListOf<Pair<Expression, Boolean>>()
    for (arg in defCallArgs) {
      extraArgs.add(Pair(arg, curParam.isExplicit))
      if (!curParam.hasNext()) {
        break
      }
      curParam = curParam.next
    }
    extraArgs.reverse()
    args.addAll(extraArgs)
  }

  args.reverse()
  return args
}
