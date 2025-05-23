/-
Copyright (c) 2023 Mario Carneiro, Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Heather Macbeth
-/
import Lean
import Batteries.Lean.Except
import Batteries.Tactic.Exact
import Mathlib.Tactic.Core
import Mathlib.Tactic.GCongr.ForwardAttr
import Mathlib.Order.Defs.PartialOrder

/-!
# The `gcongr` ("generalized congruence") tactic

The `gcongr` tactic applies "generalized congruence" rules, reducing a relational goal
between a LHS and RHS matching the same pattern to relational subgoals between the differing
inputs to the pattern.  For example,
```
example {a b x c d : ℝ} (h1 : a + 1 ≤ b + 1) (h2 : c + 2 ≤ d + 2) :
    x ^ 2 * a + c ≤ x ^ 2 * b + d := by
  gcongr
  · linarith
  · linarith
```
This example has the goal of proving the relation `≤` between a LHS and RHS both of the pattern
```
x ^ 2 * ?_ + ?_
```
(with inputs `a`, `c` on the left and `b`, `d` on the right); after the use of
`gcongr`, we have the simpler goals `a ≤ b` and `c ≤ d`.

A pattern can be provided explicitly; this is useful if a non-maximal match is desired:
```
example {a b c d x : ℝ} (h : a + c + 1 ≤ b + d + 1) :
    x ^ 2 * (a + c) + 5 ≤ x ^ 2 * (b + d) + 5 := by
  gcongr x ^ 2 * ?_ + 5
  linarith
```

## Sourcing the generalized congruence lemmas

Relevant "generalized congruence" lemmas are declared using the attribute `@[gcongr]`.  For
example, the first example constructs the proof term
```
add_le_add (mul_le_mul_of_nonneg_left _ (pow_bit0_nonneg x 1)) _
```
using the generalized congruence lemmas `add_le_add` and `mul_le_mul_of_nonneg_left`. The term
`pow_bit0_nonneg x 1` is automatically generated by a discharger (see below).

When a lemma is tagged `@[gcongr]`, it is verified that that lemma is of "generalized congruence"
form, `f x₁ y z₁ ∼ f x₂ y z₂`, that is, a relation between the application of a function to two
argument lists, in which the "varying argument" pairs (here `x₁`/`x₂` and `z₁`/`z₂`) are all free
variables. The "varying"/non-"varying" classification of the arguments is recorded (as an array of
booleans), and the `gcongr` tactic will try a lemma only if it matches the goal in relation `∼`,
head function `f` and "varying"/non-"varying" classification for each of the inputs to `f`.  Thus,
for example, all three of the following lemmas are tagged `@[gcongr]` and are used in different
situations according to whether the goal compares constant-left-multiplications,
constant-right-multiplications, or fully varying multiplications:
```
theorem mul_le_mul_of_nonneg_left [Mul α] [Zero α] [Preorder α] [PosMulMono α]
    {a b c : α} (h : b ≤ c) (a0 : 0 ≤ a) :
    a * b ≤ a * c

theorem mul_le_mul_of_nonneg_right [Mul α] [Zero α] [Preorder α] [MulPosMono α]
    {a b c : α} (h : b ≤ c) (a0 : 0 ≤ a) :
    b * a ≤ c * a

theorem mul_le_mul [MulZeroClass α] [Preorder α] [PosMulMono α] [MulPosMono α]
    {a b c d : α} (h₁ : a ≤ b) (h₂ : c ≤ d) (c0 : 0 ≤ c) (b0 : 0 ≤ b) :
    a * c ≤ b * d
```
The advantage of this approach is that the lemmas with fewer "varying" input pairs typically require
fewer side conditions, so the tactic becomes more useful by special-casing them.

There can also be more than one generalized congruence lemma dealing with the same relation, head
function and "varying"/non-"varying" configuration, for example with purely notational head
functions which have different theories when different typeclass assumptions apply.  For example,
the following lemma is stored with the same `@[gcongr]` data as `mul_le_mul` above, and the two
lemmas are simply tried in succession to determine which has the typeclasses relevant to the goal:
```
theorem mul_le_mul' [Mul α] [Preorder α] [MulLeftMono α]
    [MulRightMono α] {a b c d : α} (h₁ : a ≤ b) (h₂ : c ≤ d) :
    a * c ≤ b * d
```

## Resolving goals

The tactic attempts to discharge side goals to the "generalized congruence" lemmas (such as the
side goal `0 ≤ x ^ 2` in the above application of `mul_le_mul_of_nonneg_left`) using the tactic
`gcongr_discharger`, which wraps `positivity` but can also be extended. Side goals not discharged
in this way are left for the user.

The tactic also attempts to discharge "main" goals using the available hypotheses, as well as a
limited amount of forward reasoning.  Such attempts are made *before* descending further into
matching by congruence. The built-in forward-reasoning includes reasoning by symmetry and
reflexivity, and this can be extended by writing tactic extensions tagged with the
`@[gcongr_forward]` attribute.

## Introducing variables and hypotheses

Some natural generalized congruence lemmas have "main" hypotheses which are universally quantified
or have the structure of an implication, for example
```
theorem GCongr.Finset.sum_le_sum [OrderedAddCommMonoid N] {f g : ι → N} {s : Finset ι}
    (h : ∀ (i : ι), i ∈ s → f i ≤ g i) :
    s.sum f ≤ s.sum g
```
The tactic automatically introduces the variable `i✝ : ι` and hypothesis `hi✝ : i✝ ∈ s` in the
subgoal `∀ (i : ι), i ∈ s → f i ≤ g i` generated by applying this lemma.  By default this is done
anonymously, so they are inaccessible in the goal state which results.  The user can name them if
needed using the syntax `gcongr with i hi`.

## Variants

The tactic `rel` is a variant of `gcongr`, intended for teaching.  Local hypotheses are not
used automatically to resolve main goals, but must be invoked by name:
```
example {a b x c d : ℝ} (h1 : a ≤ b) (h2 : c ≤ d) :
    x ^ 2 * a + c ≤ x ^ 2 * b + d := by
  rel [h1, h2]
```
The `rel` tactic is finishing-only: if fails if any main or side goals are not resolved.
-/

namespace Mathlib.Tactic.GCongr
open Lean Meta

/-- Structure recording the data for a "generalized congruence" (`gcongr`) lemma. -/
structure GCongrLemma where
  declName : Name
  mainSubgoals : Array (Nat × Nat)
  varyingArgs : Array Bool
  deriving Inhabited, Repr

/-- Environment extension for "generalized congruence" (`gcongr`) lemmas. -/
initialize gcongrExt : SimpleScopedEnvExtension ((Name × Name × Array Bool) × GCongrLemma)
    (Std.HashMap (Name × Name × Array Bool) (Array GCongrLemma)) ←
  registerSimpleScopedEnvExtension {
    addEntry := fun m (n, lem) => m.insert n ((m.getD n #[]).push lem)
    initial := {}
  }

/-- Attribute marking "generalized congruence" (`gcongr`) lemmas.  Such lemmas must have a
conclusion of a form such as `f x₁ y z₁ ∼ f x₂ y z₂`; that is, a relation between the application of
a function to two argument lists, in which the "varying argument" pairs (here `x₁`/`x₂` and
`z₁`/`z₂`) are all free variables.

The antecedents of such a lemma are classified as generating "main goals" if they are of the form
`x₁ ≈ x₂` for some "varying argument" pair `x₁`/`x₂` (and a possibly different relation `≈` to `∼`),
or more generally of the form `∀ i h h' j h'', f₁ i j ≈ f₂ i j` (say) for some "varying argument"
pair `f₁`/`f₂`. (Other antecedents are considered to generate "side goals".) The index of the
"varying argument" pair corresponding to each "main" antecedent is recorded.

Lemmas involving `<` or `≤` can also be marked `@[bound]` for use in the related `bound` tactic. -/
initialize registerBuiltinAttribute {
  name := `gcongr
  descr := "generalized congruence"
  add := fun decl _ kind ↦ MetaM.run' do
    let declTy := (← getConstInfo decl).type
    withReducible <| forallTelescopeReducing declTy fun xs targetTy => do
    let fail (m : MessageData) := throwError "\
      @[gcongr] attribute only applies to lemmas proving f x₁ ... xₙ ∼ f x₁' ... xₙ'.\n \
      {m} in the conclusion of {declTy}"
    -- verify that conclusion of the lemma is of the form `f x₁ ... xₙ ∼ f x₁' ... xₙ'`
    let .app (.app rel lhs) rhs ← whnf targetTy |
      fail "No relation with at least two arguments found"
    let some relName := rel.getAppFn.constName? | fail "No relation found"
    let (some head, lhsArgs) := lhs.withApp fun e a => (e.constName?, a) |
      fail "LHS is not a function"
    let (some head', rhsArgs) := rhs.withApp fun e a => (e.constName?, a) |
      fail "RHS is not a function"
    unless head == head' && lhsArgs.size == rhsArgs.size do
      fail "LHS and RHS do not have the same head function and arity"
    let mut varyingArgs := #[]
    let mut pairs := #[]
    -- iterate through each pair of corresponding (LHS/RHS) inputs to the head function `head` in
    -- the conclusion of the lemma
    for e1 in lhsArgs, e2 in rhsArgs do
      -- we call such a pair a "varying argument" pair if the LHS/RHS inputs are not defeq
      -- (and not proofs)
      let isEq := (← isDefEq e1 e2) || ((← isProof e1) && (← isProof e2))
      if !isEq then
        let e1 := e1.eta
        let e2 := e2.eta
        -- verify that the "varying argument" pairs are free variables (after eta-reduction)
        unless e1.isFVar && e2.isFVar do fail "Not all arguments are free variables"
        -- add such a pair to the `pairs` array
        pairs := pairs.push (varyingArgs.size, e1, e2)
      -- record in the `varyingArgs` array a boolean (true for varying, false if LHS/RHS are defeq)
      varyingArgs := varyingArgs.push !isEq
    let mut mainSubgoals := #[]
    let mut i := 0
    -- iterate over antecedents `hyp` to the lemma
    for hyp in xs do
      mainSubgoals ← forallTelescopeReducing (← inferType hyp) fun _args hypTy => do
        let mut mainSubgoals := mainSubgoals
        -- pull out the conclusion `hypTy` of the antecedent, and check whether it is of the form
        -- `lhs₁ _ ... _ ≈ rhs₁ _ ... _` (for a possibly different relation `≈` than the relation
        -- `rel` above)
        if let .app (.app _ lhs₁) rhs₁ ← whnf hypTy then
          let lhs₁ := lhs₁.getAppFn
          let rhs₁ := rhs₁.getAppFn
          -- check whether `(lhs₁, rhs₁)` is in some order one of the "varying argument" pairs from
          -- the conclusion to the lemma
          if let some j ← pairs.findM? fun (_, e1, e2) =>
            isDefEq lhs₁ e1 <&&> isDefEq rhs₁ e2 <||>
            isDefEq lhs₁ e2 <&&> isDefEq rhs₁ e1
          then
            -- if yes, record the index of this antecedent as a "main subgoal", together with the
            -- index of the "varying argument" pair it corresponds to
            mainSubgoals := mainSubgoals.push (i, j.1)
        pure mainSubgoals
      i := i + 1
    -- store all the information from this parse of the lemma's structure in a `GCongrLemma`
    gcongrExt.add
      ((relName, head, varyingArgs), { declName := decl, mainSubgoals, varyingArgs }) kind
}

initialize registerTraceClass `Meta.gcongr

syntax "gcongr_discharger" : tactic

/--
This is used as the default side-goal discharger,
it calls the `gcongr_discharger` extensible tactic.
-/
def gcongrDischarger (goal : MVarId) : MetaM Unit := Elab.Term.TermElabM.run' do
  trace[Meta.gcongr] "Attempting to discharge side goal {goal}"
  let [] ← Elab.Tactic.run goal <|
      Elab.Tactic.evalTactic (Unhygienic.run `(tactic| gcongr_discharger))
    | failure

open Elab Tactic

/-- See if the term is `a = b` and the goal is `a ∼ b` or `b ∼ a`, with `∼` reflexive. -/
@[gcongr_forward] def exactRefl : ForwardExt where
  eval h goal := do
    let m ← mkFreshExprMVar none
    goal.assignIfDefEq (← mkAppOptM ``Eq.subst #[h, m])
    goal.applyRfl

/-- See if the term is `a < b` and the goal is `a ≤ b`. -/
@[gcongr_forward] def exactLeOfLt : ForwardExt where
  eval h goal := do goal.assignIfDefEq (← mkAppM ``le_of_lt #[h])

/-- See if the term is `a ∼ b` with `∼` symmetric and the goal is `b ∼ a`. -/
@[gcongr_forward] def symmExact : ForwardExt where
  eval h goal := do (← goal.applySymm).assignIfDefEq h

@[gcongr_forward] def exact : ForwardExt where
  eval e m := m.assignIfDefEq e

/-- Attempt to resolve an (implicitly) relational goal by one of a provided list of hypotheses,
either with such a hypothesis directly or by a limited palette of relational forward-reasoning from
these hypotheses. -/
def _root_.Lean.MVarId.gcongrForward (hs : Array Expr) (g : MVarId) : MetaM Unit :=
  withReducible do
    let s ← saveState
    withTraceNode `Meta.gcongr (fun _ => return m!"gcongr_forward: ⊢ {← g.getType}") do
    -- Iterate over a list of terms
    let tacs := (forwardExt.getState (← getEnv)).2
    for h in hs do
      try
        tacs.firstM fun (n, tac) =>
          withTraceNode `Meta.gcongr (return m!"{·.emoji} trying {n} on {h} : {← inferType h}") do
            tac.eval h g
        return
      catch _ => s.restore
    throwError "gcongr_forward failed"

/--
This is used as the default main-goal discharger,
consisting of running `Lean.MVarId.gcongrForward` (trying a term together with limited
forward-reasoning on that term) on each nontrivial hypothesis.
-/
def gcongrForwardDischarger (goal : MVarId) : MetaM Unit := Elab.Term.TermElabM.run' do
  let mut hs := #[]
  -- collect the nontrivial hypotheses
  for h in ← getLCtx do
    if !h.isImplementationDetail then
      hs := hs.push (.fvar h.fvarId)
  -- run `Lean.MVarId.gcongrForward` on each one
  goal.gcongrForward hs

/-- The core of the `gcongr` tactic.  Parse a goal into the form `(f _ ... _) ∼ (f _ ... _)`,
look up any relevant @[gcongr] lemmas, try to apply them, recursively run the tactic itself on
"main" goals which are generated, and run the discharger on side goals which are generated. If there
is a user-provided template, first check that the template asks us to descend this far into the
match. -/
partial def _root_.Lean.MVarId.gcongr
    (g : MVarId) (template : Option Expr) (names : List (TSyntax ``binderIdent))
    (mainGoalDischarger : MVarId → MetaM Unit := gcongrForwardDischarger)
    (sideGoalDischarger : MVarId → MetaM Unit := gcongrDischarger) :
    MetaM (Bool × List (TSyntax ``binderIdent) × Array MVarId) := g.withContext do
  withTraceNode `Meta.gcongr (fun _ => return m!"gcongr: ⊢ {← g.getType}") do
  match template with
  | none =>
    -- A. If there is no template, try to resolve the goal by the provided tactic
    -- `mainGoalDischarger`, and continue on if this fails.
    try mainGoalDischarger g; return (true, names, #[])
    catch _ => pure ()
  | some tpl =>
    -- B. If there is a template:
    -- (i) if the template is `?_` (or `?_ x1 x2`, created by entering binders)
    -- then try to resolve the goal by the provided tactic `mainGoalDischarger`;
    -- if this fails, stop and report the existing goal.
    if let .mvar mvarId := tpl.getAppFn then
      if let .syntheticOpaque ← mvarId.getKind then
        try mainGoalDischarger g; return (true, names, #[])
        catch _ => return (false, names, #[g])
    -- (ii) if the template is *not* `?_` then continue on.
  -- Check that the goal is of the form `rel (lhsHead _ ... _) (rhsHead _ ... _)`
  let .app (.app rel lhs) rhs ← withReducible g.getType'
    | throwError "gcongr failed, not a relation"
  let some relName := rel.getAppFn.constName?
    | throwError "gcongr failed, relation head {rel} is not a constant"
  let (some lhsHead, lhsArgs) := lhs.withApp fun e a => (e.constName?, a)
    | if template.isNone then return (false, names, #[g])
      throwError "gcongr failed, {lhs} is not a constant"
  let (some rhsHead, rhsArgs) := rhs.withApp fun e a => (e.constName?, a)
    | if template.isNone then return (false, names, #[g])
      throwError "gcongr failed, {rhs} is not a constant"
  -- B. If there is a template, check that it is of the form `tplHead _ ... _` and that
  -- `tplHead = lhsHead = rhsHead`
  let tplArgs ← if let some tpl := template then
    let (some tplHead, tplArgs) := tpl.withApp fun e a => (e.constName?, a)
      | throwError "gcongr failed, {tpl} is not a constant"
    unless tplHead == lhsHead && tplArgs.size == rhsArgs.size do
      throwError "expected {tplHead}, got {lhsHead}\n{lhs}"
    unless tplHead == rhsHead && tplArgs.size == rhsArgs.size do
      throwError "expected {tplHead}, got {rhsHead}\n{rhs}"
    -- and also build an array of `Expr` corresponding to the arguments `_ ... _` to `tplHead` in
    -- the template (these will be used in recursive calls later), and an array of booleans
    -- according to which of these contain `?_`
    tplArgs.mapM fun tpl => do
      let mctx ← getMCtx
      let hasMVar := tpl.findMVar? fun mvarId =>
        if let some mdecl := mctx.findDecl? mvarId then
          mdecl.kind matches .syntheticOpaque
        else
          false
      pure (some tpl, hasMVar.isSome)
  -- A. If there is no template, check that `lhs = rhs`
  else
    unless lhsHead == rhsHead && lhsArgs.size == rhsArgs.size do
      -- (if not, stop and report the existing goal)
      return (false, names, #[g])
    -- and also build an array of booleans according to which arguments `_ ... _` to the head
    -- function differ between the LHS and RHS. We treat always treat proofs as being the same
    -- (even if they have differing types).
    (lhsArgs.zip rhsArgs).mapM fun (lhsArg, rhsArg) => do
      let isSame ← withReducibleAndInstances <|
        return (← isDefEq lhsArg rhsArg) || ((← isProof lhsArg) && (← isProof rhsArg))
      return (none, !isSame)
  -- Name the array of booleans `varyingArgs`: this records which arguments to the head function are
  -- supposed to vary, according to the template (if there is one), and in the absence of a template
  -- to record which arguments to the head function differ between the two sides of the goal.
  let varyingArgs := tplArgs.map (·.2)
  if varyingArgs.all not then
    throwError "try rfl"
  let s ← saveState
  let mut ex? := none
  -- Look up the `@[gcongr]` lemmas whose conclusion has the same relation and head function as
  -- the goal and whether the boolean-array of varying/nonvarying arguments of such
  -- a lemma matches `varyingArgs`.
  for lem in (gcongrExt.getState (← getEnv)).getD (relName, lhsHead, varyingArgs) #[] do
    let gs ← try
      -- Try `apply`-ing such a lemma to the goal.
      Except.ok <$> withReducibleAndInstances (g.apply (← mkConstWithFreshMVarLevels lem.declName))
    catch e => pure (Except.error e)
    match gs with
    | .error e =>
      -- If the `apply` fails, go on to try to apply the next matching lemma.
      -- If all the matching lemmas fail to `apply`, we will report (somewhat arbitrarily) the
      -- error message on the first failure, so stash that.
      ex? := ex? <|> (some (← saveState, e))
      s.restore
    | .ok gs =>
      let some e ← getExprMVarAssignment? g | panic! "unassigned?"
      let args := e.getAppArgs
      let mut subgoals := #[]
      let mut names := names
      -- If the `apply` succeeds, iterate over `(i, j)` belonging to the lemma's `mainSubgoal`
      -- list: here `i` is an index in the lemma's array of antecedents, and `j` is an index in
      -- the array of arguments to the head function in the conclusion of the lemma (this should
      -- be the same as the head function of the LHS and RHS of our goal), such that the `i`-th
      -- antecedent to the lemma is a relation between the LHS and RHS `j`-th inputs to the head
      -- function in the goal.
      for (i, j) in lem.mainSubgoals do
        -- We anticipate that such a "main" subgoal should not have been solved by the `apply` by
        -- unification ...
        let some (.mvar mvarId) := args[i]? | panic! "what kind of lemma is this?"
        -- Introduce all variables and hypotheses in this subgoal.
        let (names2, _vs, mvarId) ← mvarId.introsWithBinderIdents names
        -- B. If there is a template, look up the part of the template corresponding to the `j`-th
        -- input to the head function
        let tpl ← tplArgs[j]!.1.mapM fun e => do
          let (_vs, _, e) ← lambdaMetaTelescope e
          pure e
        -- Recurse: call ourself (`Lean.MVarId.gcongr`) on the subgoal with (if available) the
        -- appropriate template
        let (_, names2, subgoals2) ← mvarId.gcongr tpl names2 mainGoalDischarger sideGoalDischarger
        (names, subgoals) := (names2, subgoals ++ subgoals2)
      let mut out := #[]
      -- Also try the discharger on any "side" (i.e., non-"main") goals which were not resolved
      -- by the `apply`.
      for g in gs do
        if !(← g.isAssigned) && !subgoals.contains g then
          let s ← saveState
          try
            let (_, g') ← g.intros
            sideGoalDischarger g'
          catch _ =>
            s.restore
            out := out.push g
      -- Return all unresolved subgoals, "main" or "side"
      return (true, names, out ++ subgoals)
  -- A. If there is no template, and there was no `@[gcongr]` lemma which matched the goal,
  -- report this goal back.
  if template.isNone then
    return (false, names, #[g])
  let some (sErr, e) := ex?
    -- B. If there is a template, and there was no `@[gcongr]` lemma which matched the template,
    -- fail.
    | throwError "gcongr failed, no @[gcongr] lemma applies for the template portion \
        {template} and the relation {rel}"
  -- B. If there is a template, and there was a `@[gcongr]` lemma which matched the template, but
  -- it was not possible to `apply` that lemma, then report the error message from `apply`-ing that
  -- lemma.
  sErr.restore
  throw e

/-- The `gcongr` tactic applies "generalized congruence" rules, reducing a relational goal
between a LHS and RHS matching the same pattern to relational subgoals between the differing
inputs to the pattern.  For example,
```
example {a b x c d : ℝ} (h1 : a + 1 ≤ b + 1) (h2 : c + 2 ≤ d + 2) :
    x ^ 2 * a + c ≤ x ^ 2 * b + d := by
  gcongr
  · linarith
  · linarith
```
This example has the goal of proving the relation `≤` between a LHS and RHS both of the pattern
```
x ^ 2 * ?_ + ?_
```
(with inputs `a`, `c` on the left and `b`, `d` on the right); after the use of
`gcongr`, we have the simpler goals `a ≤ b` and `c ≤ d`.

A pattern can be provided explicitly; this is useful if a non-maximal match is desired:
```
example {a b c d x : ℝ} (h : a + c + 1 ≤ b + d + 1) :
    x ^ 2 * (a + c) + 5 ≤ x ^ 2 * (b + d) + 5 := by
  gcongr x ^ 2 * ?_ + 5
  linarith
```

The "generalized congruence" rules used are the library lemmas which have been tagged with the
attribute `@[gcongr]`.  For example, the first example constructs the proof term
```
add_le_add (mul_le_mul_of_nonneg_left _ (pow_bit0_nonneg x 1)) _
```
using the generalized congruence lemmas `add_le_add` and `mul_le_mul_of_nonneg_left`.

The tactic attempts to discharge side goals to these "generalized congruence" lemmas (such as the
side goal `0 ≤ x ^ 2` in the above application of `mul_le_mul_of_nonneg_left`) using the tactic
`gcongr_discharger`, which wraps `positivity` but can also be extended. Side goals not discharged
in this way are left for the user. -/
elab "gcongr" template:(colGt term)?
    withArg:((" with " (colGt binderIdent)+)?) : tactic => do
  let g ← getMainGoal
  g.withContext do
  let .app (.app _rel lhs) _rhs ← withReducible g.getType'
    | throwError "gcongr failed, not a relation"
  -- Elaborate the template (e.g. `x * ?_ + _`), if the user gave one
  let template ← template.mapM fun e => do
    Term.elabTerm e (← inferType lhs)
  -- Get the names from the `with x y z` list
  let names := (withArg.raw[1].getArgs.map TSyntax.mk).toList
  -- Time to actually run the core tactic `Lean.MVarId.gcongr`!
  let (progress, _, unsolvedGoalStates) ← g.gcongr template names
  if progress then
    replaceMainGoal unsolvedGoalStates.toList
  else
    throwError "gcongr did not make progress"

/-- The `rel` tactic applies "generalized congruence" rules to solve a relational goal by
"substitution".  For example,
```
example {a b x c d : ℝ} (h1 : a ≤ b) (h2 : c ≤ d) :
    x ^ 2 * a + c ≤ x ^ 2 * b + d := by
  rel [h1, h2]
```
In this example we "substitute" the hypotheses `a ≤ b` and `c ≤ d` into the LHS `x ^ 2 * a + c` of
the goal and obtain the RHS `x ^ 2 * b + d`, thus proving the goal.

The "generalized congruence" rules used are the library lemmas which have been tagged with the
attribute `@[gcongr]`.  For example, the first example constructs the proof term
```
add_le_add (mul_le_mul_of_nonneg_left h1 (pow_bit0_nonneg x 1)) h2
```
using the generalized congruence lemmas `add_le_add` and `mul_le_mul_of_nonneg_left`.  If there are
no applicable generalized congruence lemmas, the tactic fails.

The tactic attempts to discharge side goals to these "generalized congruence" lemmas (such as the
side goal `0 ≤ x ^ 2` in the above application of `mul_le_mul_of_nonneg_left`) using the tactic
`gcongr_discharger`, which wraps `positivity` but can also be extended. If the side goals cannot
be discharged in this way, the tactic fails. -/
syntax "rel" " [" term,* "]" : tactic

elab_rules : tactic
  | `(tactic| rel [$hyps,*]) => do
    let g ← getMainGoal
    g.withContext do
    let hyps ← hyps.getElems.mapM (elabTerm · none)
    let .app (.app _rel lhs) rhs ← withReducible g.getType'
      | throwError "rel failed, goal not a relation"
    unless ← isDefEq (← inferType lhs) (← inferType rhs) do
      throwError "rel failed, goal not a relation"
    -- The core tactic `Lean.MVarId.gcongr` will be run with main-goal discharger being the tactic
    -- consisting of running `Lean.MVarId.gcongrForward` (trying a term together with limited
    -- forward-reasoning on that term) on each of the listed terms.
    let assum g := g.gcongrForward hyps
    -- Time to actually run the core tactic `Lean.MVarId.gcongr`!
    let (_, _, unsolvedGoalStates) ← g.gcongr none [] (mainGoalDischarger := assum)
    match unsolvedGoalStates.toList with
    -- if all goals are solved, succeed!
    | [] => pure ()
    -- if not, fail and report the unsolved goals
    | unsolvedGoalStates => do
      let unsolvedGoals ← @List.mapM MetaM _ _ _ MVarId.getType unsolvedGoalStates
      let g := Lean.MessageData.joinSep (unsolvedGoals.map Lean.MessageData.ofExpr) Format.line
      throwError "rel failed, cannot prove goal by 'substituting' the listed relationships. \
        The steps which could not be automatically justified were:\n{g}"

end GCongr

end Mathlib.Tactic
