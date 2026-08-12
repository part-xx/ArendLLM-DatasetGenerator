import org.arend.core.context.binding.Binding
import org.arend.core.context.param.DependentLink
import org.arend.core.definition.CallableDefinition
import org.arend.core.definition.ClassField
import org.arend.core.definition.Constructor
import org.arend.core.definition.DataDefinition
import org.arend.core.definition.FunctionDefinition
import org.arend.core.expr.ClassCallExpression
import org.arend.core.expr.Expression
import org.arend.core.expr.PiExpression
import org.arend.core.expr.UniverseExpression
import org.arend.ext.core.ops.NormalizationMode
import org.arend.ext.concrete.expr.ConcreteExpression
import org.arend.naming.reference.MetaReferable
import org.arend.term.concrete.Concrete
import org.arend.term.concrete.ConcreteExpressionFactory

/**
 * A second step extractor: it renders the step produced by [extractStep] in the TACTIC
 * format the ArendProofSearch prompt speaks, instead of as an Arend expression.
 *
 *   [APPLY name]   argument values, one per line   [/APPLY]
 *   [REWRITE] equality proof [/REWRITE]
 *   [CASE] expression to split [/CASE]
 *   [INTRO] binder names [/INTRO]
 *   [REFINE] the step as a term whose {?} holes become the next goals [/REFINE]
 *
 * The rendering mirrors how `CliLLMStepGenerator` turns a tactic back into a term, so a
 * tactic here is exactly what the model has to emit to reproduce the step:
 *  - propositional arguments are never listed — the harness always fills them with {?};
 *  - implicit arguments are pinned positionally in {braces}, and since earlier implicits
 *    cannot be skipped only the leading run of pinned implicits is kept;
 *  - a field application is written with dot notation on its instance (`p.isIrr`).
 *
 * Whatever the structured tactics cannot express — a tuple for a \Sigma goal, a projection,
 * a \let/\have, a \case on several expressions, a hole in a non-final argument position, an
 * application of a hypothesis's result — falls back to [REFINE], which states the step as a
 * term with holes. Only steps whose printed form is not valid source (see [refineTactic])
 * have no tactic at all.
 */
fun extractTactic(
  step: ConcreteExpression,
  nameResolver: MyNameResolver,
  concreteToCore: Map<Concrete.Expression, Expression>,
  context: Set<Binding>
): String? {
  val holer = ProofHoler(nameResolver, concreteToCore, context)
  val structured = when (step) {
    is Concrete.LamExpression -> introTactic(step)
    is Concrete.CaseExpression -> caseTactic(step)
    is Concrete.AppExpression -> appTactic(step, nameResolver, holer)
    is Concrete.ReferenceExpression -> applyTactic(step.referent.textRepresentation(), emptyList())
    else -> null
  }
  if (step is Concrete.Expression &&
    verbatimPayloads(holer.strip(step)).any { leafCount(it) > MAX_VERBATIM_LEAVES }) return null

  val tactic = structured ?: refineTactic(step, holer) ?: return null
  // Some steps print back in a form that is not valid source and so cannot be a target, in
  // whichever tag they land: names the typechecker invented for itself (\case … \as x :
  // case_return_arg_1 \return …), and the clause-only case of `mcases`, printed as a \case
  // with no expression to split.
  if (GENERATED_NAME.containsMatchIn(tactic) || SCRUTINEE_LESS_CASE.containsMatchIn(tactic)) return null
  return tactic
}

/**
 * How much a tactic may ask the model to write out verbatim, counted in LEAVES — the
 * references and literals an expression is built from — and not in characters.
 *
 * Everything [ProofHoler] refuses to hole has to be produced in full: a \case scrutinee, a
 * meta's arguments, the head of a projection. Past this size that is no longer one step —
 * `f {x} (\new LDiv { | inv => y | inv-right => inv n=x*y })` is a proof in its own right —
 * so the entry is dropped instead of becoming a target no model could produce in one go.
 *
 * Counting characters would measure arend-lib's naming rather than the step: it rejects the
 * trivial `isCancelable-left {p} {0} {1} idp` (33 characters, 5 leaves) while a denser term
 * written with short names slips through.
 */
private const val MAX_VERBATIM_LEAVES = 7

/** The pieces of [expr] that a tactic would have to carry verbatim, already holed. */
private fun verbatimPayloads(expr: Concrete.Expression): List<Concrete.Expression> = when (expr) {
  // Clause bodies are holes and clause patterns are mechanical, so only the split
  // expressions count here.
  is Concrete.CaseExpression -> expr.arguments.map { it.expression }
  is Concrete.AppExpression ->
    if ((expr.function as? Concrete.ReferenceExpression)?.referent is MetaReferable)
      expr.arguments.map { it.expression }
    else expr.arguments.flatMap { verbatimPayloads(it.expression) }
  is Concrete.ProjExpression -> listOf(expr.expression)
  is Concrete.TupleExpression -> expr.fields.flatMap { verbatimPayloads(it) }
  is Concrete.LamExpression -> verbatimPayloads(expr.body)
  is Concrete.LetExpression ->
    expr.clauses.flatMap { verbatimPayloads(it.term) } + verbatimPayloads(expr.expression)
  is Concrete.NewExpression -> verbatimPayloads(expr.expression)
  is Concrete.ClassExtExpression ->
    expr.statements.flatMap { it.implementation?.let(::verbatimPayloads) ?: emptyList() }
  else -> emptyList()
}

/** The references and literals of [expr]; holes cost the model nothing and are not counted. */
private fun leafCount(expr: Concrete.Expression): Int = when (expr) {
  is Concrete.GoalExpression, is Concrete.HoleExpression -> 0
  is Concrete.AppExpression -> leafCount(expr.function) + expr.arguments.sumOf { leafCount(it.expression) }
  is Concrete.TupleExpression -> expr.fields.sumOf { leafCount(it) }
  is Concrete.ProjExpression -> leafCount(expr.expression)
  is Concrete.LamExpression -> leafCount(expr.body)
  is Concrete.LetExpression -> expr.clauses.sumOf { leafCount(it.term) } + leafCount(expr.expression)
  is Concrete.NewExpression -> leafCount(expr.expression)
  is Concrete.ClassExtExpression ->
    leafCount(expr.baseClassExpression) + expr.statements.sumOf { it.implementation?.let(::leafCount) ?: 0 }
  is Concrete.CaseExpression -> expr.arguments.sumOf { leafCount(it.expression) }
  else -> 1
}

private fun refineTactic(step: ConcreteExpression, holer: ProofHoler): String? {
  val stripped = if (step is Concrete.Expression) holer.strip(step) else step
  val term = flatten(stripped.toString())
  if (term.isEmpty() || term == "{?}") return null // a lone hole is not a step
  return "[REFINE]$term[/REFINE]"
}

/**
 * Replaces every proof of a proposition inside the step with a goal.
 *
 * [APPLY] never takes a propositional argument from the model — the harness always fills it
 * with {?} — and a [REFINE] term follows the same rule: it states the SHAPE of the step and
 * leaves the propositional content to the steps that come after it. Two kinds of position
 * are exempt: the root, which IS the proof of the current goal, and anything that has to
 * elaborate for the term to mean what it says — the function of an application, the head of
 * a projection, the expression a \case splits on.
 *
 * Rebuilt functionally: entries share concrete nodes with one another, so nothing may be
 * mutated in place.
 */
private class ProofHoler(
  private val nameResolver: MyNameResolver,
  private val coreOf: Map<Concrete.Expression, Expression>,
  context: Set<Binding>
) {
  private val bindingTypes: Map<String, Expression> =
    context.mapNotNull { binding -> binding.name?.let { it to binding.type } }.toMap()

  fun strip(expr: Concrete.Expression): Concrete.Expression = when (expr) {
    // A meta READS its arguments — `rewrite p e` needs to see p to know what to rewrite —
    // so a hole there does not leave a subgoal, it breaks the step.
    is Concrete.AppExpression if (expr.function as? Concrete.ReferenceExpression)?.referent is MetaReferable -> expr
    is Concrete.AppExpression -> {
      // An argument is a proof iff the PARAMETER it fills is propositional — the same
      // signature-driven test [APPLY] uses. The argument's own type is only consulted for
      // arguments no parameter could be matched to, because a reference written as an
      // argument has no entry in the core map.
      val params = (expr.function as? Concrete.ReferenceExpression)
        ?.let { nameResolver.resolveReferable(it.referent) }
        ?.let { parametersOf(it) }
        ?: emptyList()
      val paramOf = paramsPerArgument(expr.arguments, params)
      Concrete.AppExpression.make(expr.data, expr.function, expr.arguments.mapIndexed { i, argument ->
        val param = paramOf[i]
        val value = when {
          param != null && isPropositional(param) -> goal()
          param != null -> strip(argument.expression)
          else -> stripOrHole(argument.expression)
        }
        Concrete.Argument(value, argument.isExplicit)
      })
    }
    is Concrete.TupleExpression ->
      ConcreteExpressionFactory.cTuple(expr.fields.map { stripOrHole(it) })
    is Concrete.LamExpression ->
      ConcreteExpressionFactory.cLam(expr.parameters, stripOrHole(expr.body))
    // The head of a projection carries the \Sigma type that gives .1/.2 their meaning, and
    // nothing constrains it from the outside, so it is left exactly as written.
    is Concrete.ProjExpression -> expr
    is Concrete.LetExpression -> Concrete.LetExpression(
      expr.data, expr.isHave, expr.isStrict,
      expr.clauses.map { Concrete.LetClause(it.pattern, it.resultType, stripOrHole(it.term)) },
      stripOrHole(expr.expression)
    )
    is Concrete.NewExpression ->
      Concrete.NewExpression(expr.data, strip(expr.expression))
    is Concrete.ClassExtExpression -> Concrete.ClassExtExpression.make(
      expr.data,
      expr.baseClassExpression,
      Concrete.Coclauses(expr.coclauses.data, expr.statements.map { statement ->
        if (statement is Concrete.CoClauseFunctionReference || statement.implementation == null) statement
        else Concrete.ClassFieldImpl(
          statement.data, statement.implementedField, stripOrHole(statement.implementation), statement.subCoclauses
        )
      })
    )
    else -> expr
  }

  private fun stripOrHole(expr: Concrete.Expression): Concrete.Expression =
    if (isPropositionalProof(expr)) goal() else strip(expr)

  private fun goal(): Concrete.Expression = ConcreteExpressionFactory.cGoal("", null)

  private fun isPropositionalProof(expr: Concrete.Expression): Boolean {
    // A reference to a local hypothesis has no entry in the core map — the elaborator does
    // not route it through checkExpr — so its type comes from the entry's context instead.
    // This is the case that matters most: `ldiv_<= {?} k|n k>n` hides its proofs in `k>n`.
    if (expr is Concrete.ReferenceExpression) {
      val type = bindingTypes[expr.referent.textRepresentation()] ?: return false
      return isPropositionalType(type)
    }
    return isPropositionalType(coreOf[expr]?.type ?: return false)
  }

  /** Same test [extractStep] applies to arguments: a \Prop-sorted type that is not a record. */
  private fun isPropositionalType(type: Expression): Boolean = try {
    if (type is ClassCallExpression) false
    else (type.type.normalize(NormalizationMode.WHNF) as? UniverseExpression)?.sortExpression?.isProp == true
  } catch (_: Exception) {
    false
  }

  /** The parameter each written argument fills, or null where none could be matched. */
  private fun paramsPerArgument(
    arguments: List<Concrete.Argument>,
    params: List<DependentLink>
  ): List<DependentLink?> {
    val matched = arrayOfNulls<DependentLink>(arguments.size)
    var argIdx = 0
    for (param in params) {
      val argument = arguments.getOrNull(argIdx) ?: break
      when {
        argument.isExplicit == param.isExplicit -> matched[argIdx++] = param
        !param.isExplicit -> continue // implicit parameter left to inference
        else -> break // the application does not line up; leave the rest unmatched
      }
    }
    return matched.toList()
  }
}

private val GENERATED_NAME = Regex("""case_(return|additional)_arg""")
private val SCRUTINEE_LESS_CASE = Regex("""\\s?case\s+\\with""")

private fun introTactic(lam: Concrete.LamExpression): String {
  // [INTRO] introduces every binder as an explicit lambda parameter, so only names matter.
  val names = lam.parameters.flatMap { it.names }.map { it ?: "_" }
  return "[INTRO]${names.joinToString(" ")}[/INTRO]"
}

private fun caseTactic(case: Concrete.CaseExpression): String? {
  // [CASE] builds the whole \case itself from ONE split expression.
  val argument = case.arguments.singleOrNull() ?: return null
  val splitExpr = flatten(argument.expression.toString())
  if (splitExpr.contains("{?}")) return null
  return "[CASE]$splitExpr[/CASE]"
}

private fun appTactic(app: Concrete.AppExpression, nameResolver: MyNameResolver, holer: ProofHoler): String? {
  val function = app.function as? Concrete.ReferenceExpression ?: return null
  val name = function.referent.textRepresentation()
  // A meta reads its arguments, so they are passed on exactly as written.
  val isMeta = function.referent is MetaReferable

  if (name == "rewrite") {
    val proof = app.arguments.firstOrNull { it.isExplicit }?.expression?.toString()?.let { flatten(it) } ?: return null
    if (proof.contains("{?}")) return null
    return "[REWRITE]$proof[/REWRITE]"
  }

  val definition = nameResolver.resolveReferable(function.referent)
    // Without a signature nothing can be classified, but the harness passes the arguments
    // of an unknown head through verbatim, so listing them all reproduces the term.
    ?: return applyTactic(name, app.arguments.map { renderArgument(it, holer, isMeta) })

  val params = parametersOf(definition)
  val matched = matchArguments(app.arguments, params) ?: return null

  var head = name
  var start = 0
  var dotNotation = false
  if (definition is ClassField) {
    // The first parameter of a field is its instance: `notInv {p}` is written `p.notInv`.
    val instance = matched.firstOrNull()?.second?.expression?.toString()
    if (instance != null && instance != "this") {
      head = (if (instance.contains(' ')) "($instance)" else instance) + "." + name
      dotNotation = true
    }
    start = 1
  }

  val values = ArrayList<String>()
  // Pinned implicits are re-inserted in front of every explicit argument, so only a run of
  // implicits at the very start of the signature can be pinned: the first gap — or the
  // first explicit parameter — ends it. For a field the instance parameter comes first, so
  // pins line up only once dot notation has consumed it.
  var implicitRunOpen = definition !is ClassField || dotNotation
  var seenExplicitGap = false
  for (index in start until params.size) {
    val param = params[index]
    val argument = matched.getOrNull(index)?.second
    val value = argument?.expression?.takeIf { it !is Concrete.GoalExpression && it !is Concrete.HoleExpression }

    if (!param.isExplicit) {
      if (value == null) implicitRunOpen = false
      else if (implicitRunOpen) values.add("{${render(value, holer, isMeta)}}")
      continue
    }
    implicitRunOpen = false
    if (isPropositional(param)) continue // always auto-filled as a {?} subgoal
    if (value == null) {
      seenExplicitGap = true
      continue
    }
    // Values are consumed in order, so a provided argument after an omitted one would
    // land on the wrong parameter.
    if (seenExplicitGap) return null
    values.add(render(value, holer, isMeta))
  }

  return applyTactic(head, values)
}

private fun applyTactic(name: String, values: List<String>): String? {
  // A hole INSIDE a value is fine — the harness parenthesizes the value and the hole becomes
  // a subgoal. A value that is nothing but a hole is not: `buildTermFromApply` would read it
  // as an implicit pin.
  if (values.any { it == "{?}" }) return null
  val body = if (values.isEmpty()) "\n" else values.joinToString("\n", prefix = "\n", postfix = "\n")
  return "[APPLY $name]$body[/APPLY]"
}

private fun renderArgument(argument: Concrete.Argument, holer: ProofHoler, isMeta: Boolean): String {
  val value = render(argument.expression, holer, isMeta)
  return if (argument.isExplicit) value else "{$value}"
}

/**
 * A value carried by a tactic is subject to the same rule as a [REFINE] term: the proofs of
 * propositions inside it are the job of the following steps, not of this one. Without this a
 * single [APPLY] can end up carrying a whole `\new Irr n { | notInv => \lam … }` instance.
 */
private fun render(value: Concrete.Expression, holer: ProofHoler, isMeta: Boolean): String =
  flatten((if (isMeta) value else holer.strip(value)).toString())

/** The [APPLY] body holds one argument per line, so a value must not span lines itself. */
private fun flatten(value: String): String = value.replace("\\s+".toRegex(), " ").trim()

/**
 * Pairs the written arguments with the parameters they fill. An implicit parameter with no
 * argument was inferred and is simply skipped; an explicit parameter facing an implicit
 * argument (or a leftover argument) means the application does not line up and is rejected.
 */
private fun matchArguments(
  arguments: List<Concrete.Argument>,
  params: List<DependentLink>
): List<Pair<DependentLink, Concrete.Argument?>>? {
  val matched = ArrayList<Pair<DependentLink, Concrete.Argument?>>(params.size)
  var argIdx = 0
  for (param in params) {
    val argument = arguments.getOrNull(argIdx)
    when {
      argument == null -> matched.add(Pair(param, null))
      argument.isExplicit == param.isExplicit -> { matched.add(Pair(param, argument)); argIdx++ }
      !param.isExplicit -> matched.add(Pair(param, null)) // implicit parameter left to inference
      else -> return null
    }
  }
  return if (argIdx == arguments.size) matched else null
}

/** The parameters of a definition, in order; for a field these live in its nested Pi type. */
private fun parametersOf(definition: CallableDefinition): List<DependentLink> {
  val params = ArrayList<DependentLink>()
  if (definition is ClassField) {
    var type: Expression? = definition.type
    while (type is PiExpression) {
      var link: DependentLink = type.parameters
      while (link.hasNext()) { params.add(link); link = link.next }
      type = type.codomain
    }
    return params
  }
  var link: DependentLink? = when (definition) {
    is FunctionDefinition -> definition.parameters
    is Constructor -> definition.parameters
    is DataDefinition -> definition.parameters
    else -> null
  }
  while (link != null && link.hasNext()) { params.add(link); link = link.next }
  return params
}

/**
 * Same classification as the `-si` CLI command the harness reads: a parameter is
 * propositional if its type sorts into \Prop or is an equality.
 */
private fun isPropositional(param: DependentLink): Boolean {
  val type = param.type ?: return false
  if (type.sortOfType?.isProp == true) return true
  return try { type.toEquality() != null } catch (_: Exception) { false }
}
