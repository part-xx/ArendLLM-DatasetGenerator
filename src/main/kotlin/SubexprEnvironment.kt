import org.arend.core.context.binding.Binding
import org.arend.core.definition.CallableDefinition
import org.arend.core.definition.Definition
import org.arend.core.expr.Expression
import org.arend.ext.concrete.expr.ConcreteExpression
import org.arend.typechecking.implicitargs.equations.Equations

// class Binding (val name: String, val type: CoreExpression)

class SubexprEnvironment (val subExpr: ConcreteExpression, val coreSubExpr: Expression, val expectedType: Expression,
                          var context: Set<Binding> = HashSet(), var premises: Set<CallableDefinition> = HashSet(),
                          val lemma: Definition)