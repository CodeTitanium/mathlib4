/-
Copyright (c) 2020 Fox Thomson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fox Thomson
-/
import Mathlib.Computability.DFA
import Mathlib.Data.Fintype.Powerset

/-!
# Nondeterministic Finite Automata
This file contains the definition of a Nondeterministic Finite Automaton (NFA), a state machine
which determines whether a string (implemented as a list over an arbitrary alphabet) is in a regular
set by evaluating the string over every possible path.
We show that DFA's are equivalent to NFA's however the construction from NFA to DFA uses an
exponential number of states.
Note that this definition allows for Automaton with infinite states; a `Fintype` instance must be
supplied for true NFA's.
-/

open Set

open Computability

universe u v


/-- An NFA is a set of states (`σ`), a transition function from state to state labelled by the
  alphabet (`step`), a set of starting states (`start`) and a set of acceptance states (`accept`).
  Note the transition function sends a state to a `Set` of states. These are the states that it
  may be sent to. -/
structure NFA (α : Type u) (σ : Type v) where
  /-- The NFA's transition function -/
  step : σ → α → Set σ
  /-- Set of starting states -/
  start : Set σ
  /-- Set of accepting states -/
  accept : Set σ

variable {α : Type u} {σ σ' : Type v} {s t u : σ} (M : NFA α σ)

namespace NFA

instance : Inhabited (NFA α σ) :=
  ⟨NFA.mk (fun _ _ => ∅) ∅ ∅⟩

/-- `M.stepSet S a` is the union of `M.step s a` for all `s ∈ S`. -/
def stepSet (S : Set σ) (a : α) : Set σ :=
  ⋃ s ∈ S, M.step s a

theorem mem_stepSet (S : Set σ) (a : α) : s ∈ M.stepSet S a ↔ ∃ t ∈ S, s ∈ M.step t a := by
  simp [stepSet]

@[simp]
theorem stepSet_empty (a : α) : M.stepSet ∅ a = ∅ := by simp [stepSet]

@[simp]
theorem stepSet_singleton (a : α) : M.stepSet {s} a = M.step s a := by
  simp [stepSet]

/-- `M.evalFrom S x` computes all possible paths through `M` with input `x` starting at an element
  of `S`. -/
def evalFrom (start : Set σ) : List α → Set σ :=
  List.foldl M.stepSet start

@[simp]
theorem evalFrom_nil (S : Set σ) : M.evalFrom S [] = S :=
  rfl

@[simp]
theorem evalFrom_singleton (S : Set σ) (a : α) : M.evalFrom S [a] = M.stepSet S a :=
  rfl

@[simp]
theorem evalFrom_cons (S : Set σ) (a : α) (x : List α) :
    M.evalFrom S (a :: x) = M.evalFrom (M.stepSet S a) x :=
  rfl

@[simp]
theorem evalFrom_append_singleton (S : Set σ) (x : List α) (a : α) :
    M.evalFrom S (x ++ [a]) = M.stepSet (M.evalFrom S x) a := by
  simp only [evalFrom, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem evalFrom_biUnion {ι : Type*} (t : Set ι) (f : ι → Set σ) (x : List α) :
    M.evalFrom (⋃ i ∈ t, f i) x = ⋃ i ∈ t, M.evalFrom (f i) x := by
  induction x generalizing ι with
  | nil => simp
  | cons a x ih => simp [stepSet, ih]

theorem evalFrom_eq_biUnion (S : Set σ) (x : List α) :
    M.evalFrom S x = ⋃ s ∈ S, M.evalFrom {s} x := by
  simp [← evalFrom_biUnion]

theorem mem_evalFrom_iff_exists {s : σ} {S : Set σ} {x : List α} :
    s ∈ M.evalFrom S x ↔ ∃ t ∈ S, s ∈ M.evalFrom {t} x := by
  rw [evalFrom_eq_biUnion]
  simp

/-- `M.eval x` computes all possible paths though `M` with input `x` starting at an element of
  `M.start`. -/
def eval : List α → Set σ :=
  M.evalFrom M.start

@[simp]
theorem eval_nil : M.eval [] = M.start :=
  rfl

@[simp]
theorem eval_singleton (a : α) : M.eval [a] = M.stepSet M.start a :=
  rfl

@[simp]
theorem eval_append_singleton (x : List α) (a : α) : M.eval (x ++ [a]) = M.stepSet (M.eval x) a :=
  evalFrom_append_singleton _ _ _ _

/-- `M.accepts` is the language of `x` such that there is an accept state in `M.eval x`. -/
def accepts : Language α := {x | ∃ S ∈ M.accept, S ∈ M.eval x}

theorem mem_accepts {x : List α} : x ∈ M.accepts ↔ ∃ S ∈ M.accept, S ∈ M.evalFrom M.start x := by
  rfl

/-- `M.IsPath` represents a traversal in `M` from a start state to an end state by following a list
of transitions in order. -/
@[mk_iff]
inductive IsPath : σ → σ → List α → Prop
  | nil (s : σ) : IsPath s s []
  | cons (t s u : σ) (a : α) (x : List α) :
      t ∈ M.step s a → IsPath t u x → IsPath s u (a :: x)

@[simp]
theorem isPath_nil : M.IsPath s t [] ↔ s = t := by
  rw [isPath_iff]
  simp [eq_comm]

alias ⟨IsPath.eq_of_nil, _⟩ := isPath_nil

@[simp]
theorem isPath_singleton {a : α} : M.IsPath s t [a] ↔ t ∈ M.step s a where
  mp := by
    rintro (_ | ⟨_, _, _, _, _, _, ⟨⟩⟩)
    assumption
  mpr := by tauto

alias ⟨_, IsPath.singleton⟩ := isPath_singleton

theorem isPath_cons_iff (a : α) (x : List α) :
    M.IsPath s u (a :: x) ↔ ∃ t ∈ M.step s a, M.IsPath t u x := by
  rw [isPath_iff]
  simp

theorem isPath_append {x y} :
    M.IsPath s u (x ++ y) ↔ ∃ t, M.IsPath s t x ∧ M.IsPath t u y where
  mp := by
    induction' x with x a ih generalizing s
    · rw [List.nil_append]
      tauto
    · rintro (_ | ⟨t, _, _, _, _, _, h⟩)
      apply ih at h
      tauto
  mpr := by
    intro ⟨t, hx, _⟩
    induction x generalizing s <;> cases hx <;> tauto

theorem mem_evalFrom_iff_exists_path {s₁ s₂ : σ} {x : List α} :
    s₂ ∈ M.evalFrom {s₁} x ↔ M.IsPath s₁ s₂ x := by
  induction x generalizing s₁ with
  | nil =>
    simp
    tauto
  | cons a x ih =>
    rw [isPath_cons_iff, evalFrom_cons, mem_evalFrom_iff_exists]
    simp [← ih]

theorem mem_accepts_iff_exists_path {x : List α} :
    x ∈ M.accepts ↔ ∃ s₁ s₂, s₁ ∈ M.start ∧ s₂ ∈ M.accept ∧ M.IsPath s₁ s₂ x := by
  simp [mem_accepts, M.mem_evalFrom_iff_exists (S := M.start), mem_evalFrom_iff_exists_path]
  tauto

/-- `M.toDFA` is a `DFA` constructed from an `NFA` `M` using the subset construction. The
  states is the type of `Set`s of `M.state` and the step function is `M.stepSet`. -/
def toDFA : DFA α (Set σ) where
  step := M.stepSet
  start := M.start
  accept := { S | ∃ s ∈ S, s ∈ M.accept }

@[simp]
theorem toDFA_correct : M.toDFA.accepts = M.accepts := by
  ext x
  rw [mem_accepts, DFA.mem_accepts]
  constructor <;> · exact fun ⟨w, h2, h3⟩ => ⟨w, h3, h2⟩

theorem pumping_lemma [Fintype σ] {x : List α} (hx : x ∈ M.accepts)
    (hlen : Fintype.card (Set σ) ≤ List.length x) :
    ∃ a b c,
      x = a ++ b ++ c ∧
        a.length + b.length ≤ Fintype.card (Set σ) ∧ b ≠ [] ∧ {a} * {b}∗ * {c} ≤ M.accepts := by
  rw [← toDFA_correct] at hx ⊢
  exact M.toDFA.pumping_lemma hx hlen

end NFA

namespace DFA

/-- `M.toNFA` is an `NFA` constructed from a `DFA` `M` by using the same start and accept
  states and a transition function which sends `s` with input `a` to the singleton `M.step s a`. -/
@[simps] def toNFA (M : DFA α σ') : NFA α σ' where
  step s a := {M.step s a}
  start := {M.start}
  accept := M.accept

@[simp]
theorem toNFA_evalFrom_match (M : DFA α σ) (start : σ) (s : List α) :
    M.toNFA.evalFrom {start} s = {M.evalFrom start s} := by
  change List.foldl M.toNFA.stepSet {start} s = {List.foldl M.step start s}
  induction' s with a s ih generalizing start
  · tauto
  · rw [List.foldl, List.foldl,
      show M.toNFA.stepSet {start} a = {M.step start a} by simp [NFA.stepSet] ]
    tauto

@[simp]
theorem toNFA_correct (M : DFA α σ) : M.toNFA.accepts = M.accepts := by
  ext x
  rw [NFA.mem_accepts, toNFA_start, toNFA_evalFrom_match]
  constructor
  · rintro ⟨S, hS₁, hS₂⟩
    rwa [Set.mem_singleton_iff.mp hS₂] at hS₁
  · exact fun h => ⟨M.eval x, h, rfl⟩

end DFA
