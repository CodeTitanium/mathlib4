/-
Copyright (c) 2021 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Eric Wieser
-/
import Mathlib.Data.Nat.Factors
import Mathlib.Tactic.NormNum.Prime

/-!
# `simproc` for `Nat.primeFactorsList`

Note that since `norm_num` can only produce numerals, we can't use it here.
-/

open Nat

namespace Mathlib.Meta.NormNum

/-- A partial proof of `primeFactorsList`.
Asserts that `l` is a sorted list of primes, lower bounded by a prime `p`, which multiplies to
`n`. -/
def FactorsHelper (n p : ℕ) (l : List ℕ) : Prop :=
  p.Prime → l.Chain (· ≤ ·) p ∧ (∀ a ∈ l, Nat.Prime a) ∧ l.prod = n

/-! The argument explicitness in this section is chosen to make only the numerals in the factors
list appear in the proof term. -/

theorem FactorsHelper.nil {a : ℕ} : FactorsHelper 1 a [] := fun _ =>
  ⟨.nil, List.forall_mem_nil _, List.prod_nil⟩

theorem FactorsHelper.cons_of_le
    {n m : ℕ} (a : ℕ) {b : ℕ} {l : List ℕ} (h₁ : IsNat (b * m) n) (h₂ : a ≤ b)
    (h₃ : minFac b = b) (H : FactorsHelper m b l) : FactorsHelper n a (b :: l) := fun pa =>
  have pb : b.Prime := Nat.prime_def_minFac.2 ⟨le_trans pa.two_le h₂, h₃⟩
  let ⟨f₁, f₂, f₃⟩ := H pb
  ⟨List.Chain.cons h₂ f₁,
    fun _ h => (List.eq_or_mem_of_mem_cons h).elim (fun e => e.symm ▸ pb) (f₂ _),
    by rw [List.prod_cons, f₃, h₁.out, cast_id]⟩

theorem FactorsHelper.cons
    {n m : ℕ} {a : ℕ} (b : ℕ) {l : List ℕ} (h₁ : IsNat (b * m) n) (h₂ : Nat.blt a b)
    (h₃ : IsNat (minFac b) b) (H : FactorsHelper m b l) : FactorsHelper n a (b :: l) :=
  H.cons_of_le _ h₁ (Nat.blt_eq.mp h₂).le h₃.out

theorem FactorsHelper.singleton (n : ℕ) {a : ℕ} (h₁ : Nat.blt a n) (h₂ : IsNat (minFac n) n) :
    FactorsHelper n a [n] :=
  FactorsHelper.nil.cons _ ⟨mul_one _⟩ h₁ h₂

theorem FactorsHelper.cons_self {n m : ℕ} (a : ℕ) {l : List ℕ}
    (h : IsNat (a * m) n) (H : FactorsHelper m a l) :
    FactorsHelper n a (a :: l) := fun pa =>
  H.cons_of_le _ h le_rfl (Nat.prime_def_minFac.1 pa).2 pa

theorem FactorsHelper.singleton_self (a : ℕ) : FactorsHelper a a [a] :=
  FactorsHelper.nil.cons_self _ ⟨mul_one _⟩

theorem FactorsHelper.primeFactorsList_eq {n : ℕ} {l : List ℕ} (H : FactorsHelper n 2 l) :
    Nat.primeFactorsList n = l :=
  let ⟨h₁, h₂, h₃⟩ := H Nat.prime_two
  have := List.chain'_iff_pairwise.1 (@List.Chain'.tail _ _ (_ :: _) h₁)
  (List.eq_of_perm_of_sorted
    (Nat.primeFactorsList_unique h₃ h₂) this (Nat.primeFactorsList_sorted _)).symm

open Lean Elab Tactic Qq

/-- Given `n` and `a` (in expressions `en` and `ea`) corresponding to literals numerals
(in `enl` and `eal`), returns `(l, ⊢ factorsHelper n a l)`. -/
private partial def evalPrimeFactorsListAux
    {en enl : Q(ℕ)} {ea eal : Q(ℕ)} (hn : Q(IsNat $en $enl)) (ha : Q(IsNat $ea $eal)) :
    MetaM ((l : Q(List ℕ)) × Q(FactorsHelper $en $ea $l)) := do
  /-
  In this function we will use the convention that `hm_*` are proof about the _meta_ code;
  these will not actually be used in the construction of the proof, and are simply used to help the
  reader reason about why the proof construction is correct.
  -/
  let n := enl.natLit!
  let ⟨hm_n0⟩ ← if h : 0 < n then pure <| PLift.up h else
    throwError m!"{enl} must be positive"
  let a := eal.natLit!
  let b := n.minFac
  let ⟨hm_ab⟩ ← if h : a ≤ b then pure <| PLift.up h else
    throwError m!"{q($eal < $(enl).minFac)} does not hold"
  if hm_bn : b < n then
    -- the factor is less than `n`, so we are not done; remove it to get `m`
    let m := n / b
    have em : Q(ℕ) := mkRawNatLit m
    have hm : Q(IsNat $em $em) := q(⟨rfl⟩)
    if hm_ba_eq : b = a then
      -- if the factor is our minimum `a`, then recurse without changing the minimum
      have h : Q($eal * $em = $en) :=
        have : a * m = n := by simp [m, ← hm_ba_eq, Nat.mul_div_cancel' (minFac_dvd _)]
        (q(Eq.refl $en) : Expr)
      let hp₁ := q(isNat_mul rfl $ha $hm $h)
      let ⟨el, hp₂⟩ ← evalPrimeFactorsListAux hm ha
      pure ⟨q($ea :: $el), q(($hp₂).cons_self _ $hp₁)⟩
    else
      -- Otherwise when we recurse, we should use `b` as the new minimum factor. Note that
      -- we must use `evalMinFac.core` to get a proof that `b` is what we computed it as.
      have eb : Q(ℕ) := mkRawNatLit b
      have hb : Q(IsNat $eb $eb) := q(⟨rfl⟩)
      have hbm : Q($eb * $em = $en) :=
        have : b * m = n := Nat.mul_div_cancel' (minFac_dvd _)
        (q(Eq.refl $en) : Expr)
      have hp₁ := q(isNat_mul rfl $hb $hm $hbm)
      have hp₂ : Q(Nat.blt $ea $eb = true) :=
        have : a < b := lt_of_le_of_ne hm_ab <| Ne.symm hm_ba_eq
        (q(Eq.refl (true)) : Expr)
      let .isNat _ lit hp₃ ← evalMinFac.core q($eb) q(inferInstance) q($eb) hb b | failure
      assertInstancesCommute
      have : $lit =Q $eb := ⟨⟩
      let ⟨l, p₄⟩ ← evalPrimeFactorsListAux hm hb
      pure ⟨q($eb :: $l), q(($p₄).cons _ $hp₁ $hp₂ $hp₃ )⟩
  else
    -- the factor is our number itself, so we are done
    have hm_bn_eq : b = n := (minFac_le hm_n0).eq_or_lt.resolve_right hm_bn
    if hm_ba : b = a then
      have h : Q($en = $ea) :=
        have : n = a := hm_bn_eq.symm.trans hm_ba
        (q(Eq.refl $en) : Expr)
      pure ⟨q([$ea]), q($h ▸ FactorsHelper.singleton_self $ea)⟩
    else do
      let p₁ : Q(Nat.blt $ea $en = true) :=
        have : a < n := by omega
        (q(Eq.refl true) : Expr)
      let .isNat _ lit p₂ ← evalMinFac.core q($en) q(inferInstance) q($enl) hn n | failure
      have : $lit =Q $en := ⟨⟩
      assertInstancesCommute
      pure ⟨q([$en]), q(FactorsHelper.singleton $en $p₁ $p₂)⟩

/-- Given a natural number `n`, returns `(l, ⊢ Nat.primeFactorsList n = l)`. -/
def evalPrimeFactorsList
    {en enl : Q(ℕ)} (hn : Q(IsNat $en $enl)) :
    MetaM ((l : Q(List ℕ)) × Q(Nat.primeFactorsList $en = $l)) := do
  match enl.natLit! with
  | 0 =>
    have _ : $enl =Q nat_lit 0 := ⟨⟩
    have hen : Q($en = 0) := q($(hn).out)
    return ⟨_, q($hen ▸ Nat.primeFactorsList_zero)⟩
  | 1 =>
    let _ : $enl =Q nat_lit 1 := ⟨⟩
    have hen : Q($en = 1) := q($(hn).out)
    return ⟨_, q($hen ▸ Nat.primeFactorsList_one)⟩
  | _ => do
    have h2 : Q(IsNat 2 (nat_lit 2)) := q(⟨Eq.refl (nat_lit 2)⟩)
    let ⟨l, p⟩ ← Mathlib.Meta.NormNum.evalPrimeFactorsListAux hn h2
    return ⟨l, q(($p).primeFactorsList_eq)⟩

end Mathlib.Meta.NormNum

open Qq Mathlib.Meta.NormNum

/-- A simproc for terms of the form `Nat.primeFactorsList (OfNat.ofNat n)`. -/
simproc Nat.primeFactorsList_ofNat (Nat.primeFactorsList _) := fun e => do
  let ⟨1, ~q(List ℕ), ~q(Nat.primeFactorsList (OfNat.ofNat $e))⟩ ← inferTypeQ e | return .continue
  let hn : Q(IsNat (OfNat.ofNat $e) $e) := q(⟨rfl⟩)
  let ⟨l, p⟩ ← evalPrimeFactorsList hn
  return .done { expr := l, proof? := p }
