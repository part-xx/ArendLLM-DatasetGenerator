import org.arend.core.definition.CallableDefinition
import org.arend.core.expr.*
import org.arend.core.expr.visitor.FreeVariablesCollector
import org.arend.ext.ArendExtension
import org.arend.ext.core.expr.CoreExpression
import org.arend.ext.core.ops.NormalizationMode
import org.arend.ext.error.ErrorReporter
import org.arend.term.concrete.Concrete
import org.arend.typechecking.instance.pool.GlobalInstancePool
import org.arend.typechecking.result.TypecheckingResult
import org.arend.typechecking.visitor.CheckTypeVisitor
import org.arend.typechecking.visitor.SearchVisitor
import java.util.*

class SubexprCollector (errorReporter: ErrorReporter?, pool: GlobalInstancePool?, extension: ArendExtension?, private val collectedExpressions: MutableList<SubexprEnvironment>) : CheckTypeVisitor(errorReporter, pool, extension) {
    private var forbiddenSet: MutableSet<Concrete.Expression> = HashSet()
    private var currentAncestors: MutableList<Concrete.Expression> = ArrayList()

    companion object {
        const val MIN_LENGTH = 2
        const val MAX_LENGTH = 1000
        const val MIN_LEAVES = 10
        const val MAX_LEAVES = 30
    }

    override fun checkExpr(expr: Concrete.Expression?, expectedType: Expression?): TypecheckingResult? {
        if (expr == null) return null
        currentAncestors.addLast(expr)

        val result = super.checkExpr(expr, expectedType)
        currentAncestors.removeLast()
        if (result == null) {
            return null
        }

        /*if (currentAncestors.isNotEmpty() && forbiddenSet.contains(currentAncestors.last())) {
            return result
        }*/

        if (!isSuitable(expr, result)) {
            return result
        }

        // collectedExpressions.addLast(SubexprEnvironment(result.expression, ArrayList(context.values)))

        forbiddenSet.add(expr)
        collectedExpressions.addLast(SubexprEnvironment(expr, result.expression, result.type, HashSet(), HashSet()))
        return result
    }

    private fun isSuitable(expr: Concrete.Expression, coreExpr: TypecheckingResult): Boolean {
        val universeExpr = coreExpr.type.type.normalize(NormalizationMode.WHNF)
        if (universeExpr !is UniverseExpression || !universeExpr.sort.isProp) return false

        if (expr.toString().contains("{!}")) return false

        if (expr.toString().startsWith("_")) return false

        val len = expr.toString().split(" ").filter { it.isNotBlank() }.size

        return len in MIN_LENGTH..MAX_LENGTH
    }

    private fun checkNumLeaves(expr: Concrete.Expression, coreExpr: TypecheckingResult): Boolean {
        var numLeaves = 0

        coreExpr.expression.accept(object: SearchVisitor<Void>() {
            override fun processDefCall(expression: DefCallExpression, param: Void?): CoreExpression.FindAction {
                ++ numLeaves
                return super.processDefCall(expression, param)
            }

            override fun visitInteger(expr: IntegerExpression?, params: Void?): Boolean {
                ++ numLeaves
                return super.visitInteger(expr, params)
            }

            override fun visitReference(expression: ReferenceExpression?, param: Void?): Boolean {
                ++ numLeaves
                return super.visitReference(expression, param)
            }
        }, null)

        return numLeaves in MIN_LEAVES..MAX_LEAVES
    }
}