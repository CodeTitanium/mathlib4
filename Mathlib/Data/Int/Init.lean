/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad
-/
import Batteries.Logic
import Batteries.Tactic.Init
import Mathlib.Data.Int.Notation
import Mathlib.Data.Nat.Notation
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.TypeStar

/-!
# Basic operations on the integers

This file contains some basic lemmas about integers.

See note [foundational algebra order theory].

This file should not depend on anything defined in Mathlib (except for notation), so that it can be
upstreamed to Batteries easily.
-/

open Nat

namespace Int
variable {a b c d m n : ℤ}

section Order

protected lemma le_rfl : a ≤ a := a.le_refl
protected lemma lt_or_lt_of_ne : a ≠ b → a < b ∨ b < a := Int.lt_or_gt_of_ne
protected lemma lt_or_le (a b : ℤ) : a < b ∨ b ≤ a := by rw [← Int.not_lt]; exact Decidable.em _
protected lemma le_or_lt (a b : ℤ) : a ≤ b ∨ b < a := (b.lt_or_le a).symm
protected lemma lt_asymm : a < b → ¬ b < a := by rw [Int.not_lt]; exact Int.le_of_lt
protected lemma le_of_eq (hab : a = b) : a ≤ b := by rw [hab]; exact Int.le_rfl
protected lemma ge_of_eq (hab : a = b) : b ≤ a := Int.le_of_eq hab.symm
protected lemma le_antisymm_iff : a = b ↔ a ≤ b ∧ b ≤ a :=
  ⟨fun h ↦ ⟨Int.le_of_eq h, Int.ge_of_eq h⟩, fun h ↦ Int.le_antisymm h.1 h.2⟩
protected lemma le_iff_eq_or_lt : a ≤ b ↔ a = b ∨ a < b := by omega

protected lemma le_iff_lt_or_eq : a ≤ b ↔ a < b ∨ a = b := by rw [Int.le_iff_eq_or_lt, or_comm]

end Order

-- TODO: Tag in Lean
attribute [simp] natAbs_pos

protected lemma one_pos : 0 < (1 : Int) := Int.zero_lt_one

protected lemma one_ne_zero : (1 : ℤ) ≠ 0 := by decide

protected lemma one_nonneg : 0 ≤ (1 : ℤ) := Int.le_of_lt Int.zero_lt_one

protected theorem neg_eq_neg {a b : ℤ} (h : -a = -b) : a = b := Int.neg_inj.1 h

@[simp high]
protected lemma neg_pos : 0 < -a ↔ a < 0 := ⟨Int.neg_of_neg_pos, Int.neg_pos_of_neg⟩

@[simp high]
protected lemma neg_nonneg : 0 ≤ -a ↔ a ≤ 0 := ⟨Int.nonpos_of_neg_nonneg, Int.neg_nonneg_of_nonpos⟩

@[simp high]
protected lemma neg_neg_iff_pos : -a < 0 ↔ 0 < a := ⟨Int.pos_of_neg_neg, Int.neg_neg_of_pos⟩

@[deprecated (since := "2025-03-07")] alias neg_nonpos_iff_nonneg := Int.neg_nonpos_iff

@[simp high]
protected lemma sub_pos : 0 < a - b ↔ b < a := ⟨Int.lt_of_sub_pos, Int.sub_pos_of_lt⟩

@[simp high]
protected lemma sub_nonneg : 0 ≤ a - b ↔ b ≤ a := ⟨Int.le_of_sub_nonneg, Int.sub_nonneg_of_le⟩

protected theorem ofNat_add_out (m n : ℕ) : ↑m + ↑n = (↑(m + n) : ℤ) := rfl

protected theorem ofNat_mul_out (m n : ℕ) : ↑m * ↑n = (↑(m * n) : ℤ) := rfl

protected theorem ofNat_add_one_out (n : ℕ) : ↑n + (1 : ℤ) = ↑(succ n) := rfl

@[simp] lemma ofNat_eq_natCast (n : ℕ) : Int.ofNat n = n := rfl

@[norm_cast] lemma natCast_inj {m n : ℕ} : (m : ℤ) = (n : ℤ) ↔ m = n := ofNat_inj

@[simp, norm_cast] lemma natAbs_cast (n : ℕ) : natAbs ↑n = n := rfl

@[norm_cast]
protected lemma natCast_sub {n m : ℕ} : n ≤ m → (↑(m - n) : ℤ) = ↑m - ↑n := ofNat_sub

@[simp high] lemma natCast_eq_zero {n : ℕ} : (n : ℤ) = 0 ↔ n = 0 := by omega

lemma natCast_ne_zero {n : ℕ} : (n : ℤ) ≠ 0 ↔ n ≠ 0 := by omega

lemma natCast_ne_zero_iff_pos {n : ℕ} : (n : ℤ) ≠ 0 ↔ 0 < n := by omega

@[simp high] lemma natCast_pos {n : ℕ} : (0 : ℤ) < n ↔ 0 < n := by omega

lemma natCast_succ_pos (n : ℕ) : 0 < (n.succ : ℤ) := natCast_pos.2 n.succ_pos

@[simp high] lemma natCast_nonpos_iff {n : ℕ} : (n : ℤ) ≤ 0 ↔ n = 0 := by omega

lemma natCast_nonneg (n : ℕ) : 0 ≤ (n : ℤ) := ofNat_le.2 (Nat.zero_le _)

@[simp] lemma sign_natCast_add_one (n : ℕ) : sign (n + 1) = 1 := rfl

@[simp, norm_cast] lemma cast_id {n : ℤ} : Int.cast n = n := rfl

protected lemma two_mul : ∀ n : ℤ, 2 * n = n + n
  | (n : ℕ) => by norm_cast; exact n.two_mul
  | -[n+1] => by
    change (2 : ℕ) * (_ : ℤ) = _
    rw [Int.ofNat_mul_negSucc, Nat.two_mul, ofNat_add, Int.neg_add]
    rfl

protected lemma mul_le_mul_iff_of_pos_right (ha : 0 < a) : b * a ≤ c * a ↔ b ≤ c :=
  ⟨(le_of_mul_le_mul_right · ha), (Int.mul_le_mul_of_nonneg_right · (Int.le_of_lt ha))⟩

protected lemma mul_nonneg_iff_of_pos_right (hb : 0 < b) : 0 ≤ a * b ↔ 0 ≤ a := by
  simpa using (Int.mul_le_mul_iff_of_pos_right hb : 0 * b ≤ a * b ↔ 0 ≤ a)

/-! ### succ and pred -/

/-- Immediate successor of an integer: `succ n = n + 1` -/
def succ (a : ℤ) := a + 1

/-- Immediate predecessor of an integer: `pred n = n - 1` -/
def pred (a : ℤ) := a - 1

lemma pred_succ (a : ℤ) : pred (succ a) = a := Int.add_sub_cancel _ _

lemma succ_pred (a : ℤ) : succ (pred a) = a := Int.sub_add_cancel _ _

lemma neg_succ (a : ℤ) : -succ a = pred (-a) := Int.neg_add

lemma succ_neg_succ (a : ℤ) : succ (-succ a) = -a := by rw [neg_succ, succ_pred]

lemma neg_pred (a : ℤ) : -pred a = succ (-a) := by
  rw [← Int.neg_eq_comm.mp (neg_succ (-a)), Int.neg_neg]

lemma pred_neg_pred (a : ℤ) : pred (-pred a) = -a := by rw [neg_pred, pred_succ]

lemma pred_nat_succ (n : ℕ) : pred (Nat.succ n) = n := pred_succ n

lemma neg_nat_succ (n : ℕ) : -(Nat.succ n : ℤ) = pred (-n) := neg_succ n

lemma succ_neg_natCast_succ (n : ℕ) : succ (-Nat.succ n) = -n := succ_neg_succ n

@[norm_cast] lemma natCast_pred_of_pos {n : ℕ} (h : 0 < n) : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by
  cases n; cases h; simp [ofNat_succ]

lemma lt_succ_self (a : ℤ) : a < succ a := by unfold succ; omega

lemma pred_self_lt (a : ℤ) : pred a < a := by unfold pred; omega

lemma le_add_one_iff : m ≤ n + 1 ↔ m ≤ n ∨ m = n + 1 := by omega

lemma sub_one_lt_iff : m - 1 < n ↔ m ≤ n := by omega

lemma le_sub_one_iff : m ≤ n - 1 ↔ m < n := by omega

section
open Lean.Omega.Int

/-!
The following few lemmas are proved in the core implementation of the `omega` tactic. We expose
them here with nice user-facing names.
-/

protected lemma add_le_iff_le_sub : a + b ≤ c ↔ a ≤ c - b := add_le_iff_le_sub ..
protected lemma le_add_iff_sub_le : a ≤ b + c ↔ a - c ≤ b := le_add_iff_sub_le ..
protected lemma add_le_zero_iff_le_neg : a + b ≤ 0 ↔ a ≤ - b := add_le_zero_iff_le_neg ..
protected lemma add_le_zero_iff_le_neg' : a + b ≤ 0 ↔ b ≤ -a := add_le_zero_iff_le_neg' ..
protected lemma add_nonnneg_iff_neg_le : 0 ≤ a + b ↔ -b ≤ a := add_nonnneg_iff_neg_le ..
protected lemma add_nonnneg_iff_neg_le' : 0 ≤ a + b ↔ -a ≤ b := add_nonnneg_iff_neg_le' ..

end

/--
Induction on integers: prove a proposition `p i` by proving the base case `p 0`,
the upwards induction step `p i → p (i + 1)` and the downwards induction step `p (-i) → p (-i - 1)`.

It is used as the default induction principle for the `induction` tactic.
-/
@[elab_as_elim, induction_eliminator] protected lemma induction_on {p : ℤ → Prop} (i : ℤ)
    (hz : p 0) (hp : ∀ i : ℕ, p i → p (i + 1)) (hn : ∀ i : ℕ, p (-i) → p (-i - 1)) : p i := by
  cases i with
  | ofNat i =>
    induction i with
    | zero => exact hz
    | succ i ih => exact hp _ ih
  | negSucc i =>
    suffices ∀ n : ℕ, p (-n) from this (i + 1)
    intro n; induction n with
    | zero => simp [hz]
    | succ n ih => simpa [ofNat_succ, Int.neg_add, Int.sub_eq_add_neg] using hn _ ih

section inductionOn'

variable {C : ℤ → Sort*} (z b : ℤ)
  (H0 : C b) (Hs : ∀ k, b ≤ k → C k → C (k + 1)) (Hp : ∀ k ≤ b, C k → C (k - 1))

/-- Inductively define a function on `ℤ` by defining it at `b`, for the `succ` of a number greater
than `b`, and the `pred` of a number less than `b`. -/
@[elab_as_elim] protected def inductionOn' : C z :=
  cast (congrArg C <| show b + (z - b) = z by rw [Int.add_comm, z.sub_add_cancel b]) <|
  match z - b with
  | .ofNat n => pos n
  | .negSucc n => neg n
where
  /-- The positive case of `Int.inductionOn'`. -/
  pos : ∀ n : ℕ, C (b + n)
  | 0 => cast (by simp) H0
  | n+1 => cast (by rw [Int.add_assoc]; rfl) <|
    Hs _ (Int.le_add_of_nonneg_right (ofNat_nonneg _)) (pos n)

  /-- The negative case of `Int.inductionOn'`. -/
  neg : ∀ n : ℕ, C (b + -[n+1])
  | 0 => Hp _ Int.le_rfl H0
  | n+1 => by
    refine cast (by rw [Int.add_sub_assoc]; rfl) (Hp _ (Int.le_of_lt ?_) (neg n))
    omega

variable {z b H0 Hs Hp}

lemma inductionOn'_self : b.inductionOn' b H0 Hs Hp = H0 :=
  cast_eq_iff_heq.mpr <| .symm <| by rw [b.sub_self, ← cast_eq_iff_heq]; rfl

lemma inductionOn'_sub_one (hz : z ≤ b) :
    (z - 1).inductionOn' b H0 Hs Hp = Hp z hz (z.inductionOn' b H0 Hs Hp) := by
  apply cast_eq_iff_heq.mpr
  obtain ⟨n, hn⟩ := Int.eq_negSucc_of_lt_zero (show z - 1 - b < 0 by omega)
  rw [hn]
  obtain _|n := n
  · change _ = -1 at hn
    have : z = b := by omega
    subst this; rw [inductionOn'_self]; exact heq_of_eq rfl
  · have : z = b + -[n+1] := by rw [Int.negSucc_eq] at hn ⊢; omega
    subst this
    refine (cast_heq _ _).trans ?_
    congr
    symm
    rw [Int.inductionOn', cast_eq_iff_heq, show b + -[n+1] - b = -[n+1] by omega]

end inductionOn'

/-- Inductively define a function on `ℤ` by defining it on `ℕ` and extending it from `n` to `-n`. -/
@[elab_as_elim] protected def negInduction {C : ℤ → Sort*} (nat : ∀ n : ℕ, C n)
    (neg : (∀ n : ℕ, C n) → ∀ n : ℕ, C (-n)) : ∀ n : ℤ, C n
  | .ofNat n => nat n
  | .negSucc n => neg nat <| n + 1

/-- See `Int.inductionOn'` for an induction in both directions. -/
protected lemma le_induction {P : ℤ → Prop} {m : ℤ} (h0 : P m)
    (h1 : ∀ n : ℤ, m ≤ n → P n → P (n + 1)) (n : ℤ) : m ≤ n → P n := by
  refine Int.inductionOn' n m ?_ ?_ ?_
  · intro
    exact h0
  · intro k hle hi _
    exact h1 k hle (hi hle)
  · intro k hle _ hle'
    omega

/-- See `Int.inductionOn'` for an induction in both directions. -/
protected theorem le_induction_down {P : ℤ → Prop} {m : ℤ} (h0 : P m)
    (h1 : ∀ n : ℤ, n ≤ m → P n → P (n - 1)) (n : ℤ) : n ≤ m → P n :=
  Int.inductionOn' n m (fun _ ↦ h0) (fun k hle _ hle' ↦ by omega)
    fun k hle hi _ ↦ h1 k hle (hi hle)

section strongRec

variable {P : ℤ → Sort*} (lt : ∀ n < m, P n) (ge : ∀ n ≥ m, (∀ k < n, P k) → P n)

/-- A strong recursor for `Int` that specifies explicit values for integers below a threshold,
and is analogous to `Nat.strongRec` for integers on or above the threshold. -/
@[elab_as_elim] protected def strongRec (n : ℤ) : P n := by
  refine if hnm : n < m then lt n hnm else ge n (by omega) (n.inductionOn' m lt ?_ ?_)
  · intro _n _ ih l _
    exact if hlm : l < m then lt l hlm else ge l (by omega) fun k _ ↦ ih k (by omega)
  · exact fun n _ hn l _ ↦ hn l (by omega)

variable {lt ge}
lemma strongRec_of_lt (hn : n < m) : m.strongRec lt ge n = lt n hn := dif_pos _

end strongRec

/-! ### mul -/

-- We want to use these lemmas earlier than the lemmas simp can prove them with

@[simp high] protected lemma mul_le_mul_left (ha : 0 < a) : a * b ≤ a * c ↔ b ≤ c where
  mp hbc := Int.le_of_mul_le_mul_left hbc ha
  mpr hbc := Int.mul_le_mul_of_nonneg_left hbc <| Int.le_of_lt ha

@[simp high] protected lemma mul_le_mul_right (ha : 0 < a) : b * a ≤ c * a ↔ b ≤ c where
  mp hbc := Int.le_of_mul_le_mul_right hbc ha
  mpr hbc := Int.mul_le_mul_of_nonneg_right hbc <| Int.le_of_lt ha

@[simp high] protected lemma mul_lt_mul_left (ha : 0 < a) : a * b < a * c ↔ b < c where
  mp hbc := Int.lt_of_mul_lt_mul_left hbc <| Int.le_of_lt ha
  mpr hbc := Int.mul_lt_mul_of_pos_left hbc ha

@[simp high] protected lemma mul_lt_mul_right (ha : 0 < a) : b * a < c * a ↔ b < c where
  mp hbc := Int.lt_of_mul_lt_mul_right hbc <| Int.le_of_lt ha
  mpr hbc := Int.mul_lt_mul_of_pos_right hbc ha

@[simp high] protected lemma mul_le_mul_left_of_neg (ha : a < 0) :
    a * b ≤ a * c ↔ c ≤ b := by
  rw [← Int.neg_le_neg_iff, Int.neg_mul_eq_neg_mul, Int.neg_mul_eq_neg_mul,
    Int.mul_le_mul_left <| Int.neg_pos.2 ha]

@[simp high] protected lemma mul_le_mul_right_of_neg (ha : a < 0) :
    b * a ≤ c * a ↔ c ≤ b := by
  rw [← Int.neg_le_neg_iff, Int.neg_mul_eq_mul_neg, Int.neg_mul_eq_mul_neg,
    Int.mul_le_mul_right <| Int.neg_pos.2 ha]

@[simp high] protected lemma mul_lt_mul_left_of_neg (ha : a < 0) :
    a * b < a * c ↔ c < b := by
  rw [← Int.neg_lt_neg_iff, Int.neg_mul_eq_neg_mul, Int.neg_mul_eq_neg_mul,
    Int.mul_lt_mul_left <| Int.neg_pos.2 ha]

@[simp high] protected lemma mul_lt_mul_right_of_neg (ha : a < 0) :
    b * a < c * a ↔ c < b := by
  rw [← Int.neg_lt_neg_iff, Int.neg_mul_eq_mul_neg, Int.neg_mul_eq_mul_neg,
    Int.mul_lt_mul_right <| Int.neg_pos.2 ha]

/-! ### nat abs -/

-- TODO: Rename `natAbs_ofNat` to `natAbs_natCast`
@[simp] lemma natAbs_ofNat' (n : ℕ) : natAbs (ofNat n) = n := rfl

lemma natAbs_add_of_nonneg : ∀ {a b : Int}, 0 ≤ a → 0 ≤ b → natAbs (a + b) = natAbs a + natAbs b
  | ofNat _, ofNat _, _, _ => rfl

lemma natAbs_add_of_nonpos {a b : Int} (ha : a ≤ 0) (hb : b ≤ 0) :
    natAbs (a + b) = natAbs a + natAbs b := by
  omega

lemma natAbs_pow (n : ℤ) (k : ℕ) : Int.natAbs (n ^ k) = Int.natAbs n ^ k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Int.pow_succ, natAbs_mul, Nat.pow_succ, ih, Nat.mul_comm]

lemma natAbs_sq (x : ℤ) : (x.natAbs : ℤ) ^ 2 = x ^ 2 := by
  simp [Int.pow_succ, Int.pow_zero, Int.natAbs_mul_self']

alias natAbs_pow_two := natAbs_sq

theorem sign_mul_self_eq_natAbs : ∀ a : Int, sign a * a = natAbs a
  | 0      => rfl
  | Nat.succ _ => Int.one_mul _
  | -[_+1] => (Int.neg_eq_neg_one_mul _).symm

/-! ### `/` -/

@[simp, norm_cast] lemma natCast_div (m n : ℕ) : ((m / n : ℕ) : ℤ) = m / n := rfl

lemma natCast_ediv (m n : ℕ) : ((m / n : ℕ) : ℤ) = ediv m n := rfl

lemma ediv_of_neg_of_pos {a b : ℤ} (Ha : a < 0) (Hb : 0 < b) : ediv a b = -((-a - 1) / b + 1) :=
  match a, b, eq_negSucc_of_lt_zero Ha, eq_succ_of_zero_lt Hb with
  | _, _, ⟨m, rfl⟩, ⟨n, rfl⟩ => by
    rw [show (- -[m+1] : ℤ) = (m + 1 : ℤ) by rfl]; rw [Int.add_sub_cancel]; rfl

/-! ### mod -/

@[simp, norm_cast] lemma natCast_mod (m n : ℕ) : (↑(m % n) : ℤ) = ↑m % ↑n := rfl

lemma add_emod_eq_add_mod_right {m n k : ℤ} (i : ℤ) (H : m % n = k % n) :
    (m + i) % n = (k + i) % n := by rw [← emod_add_emod, ← emod_add_emod k, H]

@[simp] lemma neg_emod_two (i : ℤ) : -i % 2 = i % 2 := by omega

lemma div_le_iff_of_dvd_of_pos (hb : 0 < b) (hba : b ∣ a) : a / b ≤ c ↔ a ≤ b * c := by
  obtain ⟨x, rfl⟩ := hba; simp [*, Int.ne_of_gt]

lemma div_le_iff_of_dvd_of_neg (hb : b < 0) (hba : b ∣ a) : a / b ≤ c ↔ b * c ≤ a := by
  obtain ⟨x, rfl⟩ := hba; simp [*, Int.ne_of_lt]

lemma div_lt_iff_of_dvd_of_pos (hb : 0 < b) (hba : b ∣ a) : a / b < c ↔ a < b * c := by
  obtain ⟨x, rfl⟩ := hba; simp [*, Int.ne_of_gt]

lemma div_lt_iff_of_dvd_of_neg (hb : b < 0) (hba : b ∣ a) : a / b < c ↔ b * c < a := by
  obtain ⟨x, rfl⟩ := hba; simp [*, Int.ne_of_lt]

lemma le_div_iff_of_dvd_of_pos (hc : 0 < c) (hcb : c ∣ b) : a ≤ b / c ↔ c * a ≤ b := by
  obtain ⟨x, rfl⟩ := hcb; simp [*, Int.ne_of_gt]

lemma le_div_iff_of_dvd_of_neg (hc : c < 0) (hcb : c ∣ b) : a ≤ b / c ↔ b ≤ c * a := by
  obtain ⟨x, rfl⟩ := hcb; simp [*, Int.ne_of_lt]

lemma lt_div_iff_of_dvd_of_pos (hc : 0 < c) (hcb : c ∣ b) : a < b / c ↔ c * a < b := by
  obtain ⟨x, rfl⟩ := hcb; simp [*, Int.ne_of_gt]

lemma lt_div_iff_of_dvd_of_neg (hc : c < 0) (hcb : c ∣ b) : a < b / c ↔ b < c * a := by
  obtain ⟨x, rfl⟩ := hcb; simp [*, Int.ne_of_lt]

lemma div_le_div_iff_of_dvd_of_pos_of_pos (hb : 0 < b) (hd : 0 < d) (hba : b ∣ a)
    (hdc : d ∣ c) : a / b ≤ c / d ↔ d * a ≤ c * b := by
  obtain ⟨⟨x, rfl⟩, y, rfl⟩ := hba, hdc
  simp [*, Int.ne_of_lt, Int.ne_of_gt, d.mul_assoc, b.mul_comm]

lemma div_le_div_iff_of_dvd_of_pos_of_neg (hb : 0 < b) (hd : d < 0) (hba : b ∣ a) (hdc : d ∣ c) :
    a / b ≤ c / d ↔ c * b ≤ d * a := by
  obtain ⟨⟨x, rfl⟩, y, rfl⟩ := hba, hdc
  simp [*, Int.ne_of_lt, Int.ne_of_gt, d.mul_assoc, b.mul_comm]

lemma div_le_div_iff_of_dvd_of_neg_of_pos (hb : b < 0) (hd : 0 < d) (hba : b ∣ a)  (hdc : d ∣ c) :
    a / b ≤ c / d ↔ c * b ≤ d * a := by
  obtain ⟨⟨x, rfl⟩, y, rfl⟩ := hba, hdc
  simp [*, Int.ne_of_lt, Int.ne_of_gt, d.mul_assoc, b.mul_comm]

lemma div_le_div_iff_of_dvd_of_neg_of_neg (hb : b < 0) (hd : d < 0) (hba : b ∣ a) (hdc : d ∣ c) :
    a / b ≤ c / d ↔ d * a ≤ c * b := by
  obtain ⟨⟨x, rfl⟩, y, rfl⟩ := hba, hdc
  simp [*, Int.ne_of_lt, Int.ne_of_gt, d.mul_assoc, b.mul_comm]

lemma div_lt_div_iff_of_dvd_of_pos (hb : 0 < b) (hd : 0 < d) (hba : b ∣ a) (hdc : d ∣ c) :
    a / b < c / d ↔ d * a < c * b := by
  obtain ⟨⟨x, rfl⟩, y, rfl⟩ := hba, hdc
  simp [*, Int.ne_of_lt, Int.ne_of_gt, d.mul_assoc, b.mul_comm]

lemma div_lt_div_iff_of_dvd_of_pos_of_neg (hb : 0 < b) (hd : d < 0) (hba : b ∣ a) (hdc : d ∣ c) :
    a / b < c / d ↔ c * b < d * a := by
  obtain ⟨⟨x, rfl⟩, y, rfl⟩ := hba, hdc
  simp [*, Int.ne_of_lt, Int.ne_of_gt, d.mul_assoc, b.mul_comm]

lemma div_lt_div_iff_of_dvd_of_neg_of_pos (hb : b < 0) (hd : 0 < d) (hba : b ∣ a) (hdc : d ∣ c) :
    a / b < c / d ↔ c * b < d * a := by
  obtain ⟨⟨x, rfl⟩, y, rfl⟩ := hba, hdc
  simp [*, Int.ne_of_lt, Int.ne_of_gt, d.mul_assoc, b.mul_comm]

lemma div_lt_div_iff_of_dvd_of_neg_of_neg (hb : b < 0) (hd : d < 0) (hba : b ∣ a) (hdc : d ∣ c) :
    a / b < c / d ↔ d * a < c * b := by
  obtain ⟨⟨x, rfl⟩, y, rfl⟩ := hba, hdc
  simp [*, Int.ne_of_lt, Int.ne_of_gt, d.mul_assoc, b.mul_comm]

/-! ### properties of `/` and `%` -/

lemma emod_two_eq_zero_or_one (n : ℤ) : n % 2 = 0 ∨ n % 2 = 1 := by omega

/-! ### dvd -/

attribute [simp] Int.dvd_zero Int.dvd_mul_left Int.dvd_mul_right

protected lemma mul_dvd_mul : a ∣ b → c ∣ d → a * c ∣ b * d
  | ⟨e, he⟩, ⟨f, hf⟩ => ⟨e * f, by simp [he, hf, Int.mul_assoc, Int.mul_left_comm, Nat.mul_comm]⟩

protected lemma mul_dvd_mul_left (a : ℤ) (h : b ∣ c) : a * b ∣ a * c := Int.mul_dvd_mul a.dvd_refl h

protected lemma mul_dvd_mul_right (a : ℤ) (h : b ∣ c) : b * a ∣ c * a :=
  Int.mul_dvd_mul h a.dvd_refl

lemma dvd_mul_of_div_dvd (h : b ∣ a) (hdiv : a / b ∣ c) : a ∣ b * c := by
  obtain ⟨e, rfl⟩ := hdiv
  rw [← Int.mul_assoc, Int.mul_comm _ (a / b), Int.ediv_mul_cancel h]
  exact Int.dvd_mul_right a e

@[simp] lemma div_dvd_iff_dvd_mul (h : b ∣ a) (hb : b ≠ 0) : a / b ∣ c ↔ a ∣ b * c :=
  exists_congr <| fun d ↦ by
  have := Int.dvd_trans (Int.dvd_mul_left _ _) (Int.mul_dvd_mul_left d h)
  rw [eq_comm, Int.mul_comm, ← Int.mul_ediv_assoc d h, Int.ediv_eq_iff_eq_mul_right hb this,
    Int.mul_comm, eq_comm]

lemma mul_dvd_of_dvd_div (hcb : c ∣ b) (h : a ∣ b / c) : c * a ∣ b :=
  have ⟨d, hd⟩ := h
  ⟨d, by simpa [Int.mul_comm, Int.mul_left_comm] using Int.eq_mul_of_ediv_eq_left hcb hd⟩

lemma dvd_div_of_mul_dvd (h : a * b ∣ c) : b ∣ c / a := by
  obtain rfl | ha := Decidable.em (a = 0)
  · simp
  · obtain ⟨d, rfl⟩ := h
    simp [Int.mul_assoc, ha]

@[simp] lemma dvd_div_iff_mul_dvd (hbc : c ∣ b) : a ∣ b / c ↔ c * a ∣ b :=
  ⟨mul_dvd_of_dvd_div hbc, dvd_div_of_mul_dvd⟩

lemma ediv_dvd_ediv : ∀ {a b c : ℤ}, a ∣ b → b ∣ c → b / a ∣ c / a
  | a, _, _, ⟨b, rfl⟩, ⟨c, rfl⟩ =>
    if az : a = 0 then by simp [az]
    else by
      rw [Int.mul_ediv_cancel_left _ az, Int.mul_assoc, Int.mul_ediv_cancel_left _ az]
      apply Int.dvd_mul_right

/-- If `n > 0` then `m` is not divisible by `n` iff it is between `n * k` and `n * (k + 1)`
  for some `k`. -/
lemma exists_lt_and_lt_iff_not_dvd (m : ℤ) (hn : 0 < n) :
    (∃ k, n * k < m ∧ m < n * (k + 1)) ↔ ¬n ∣ m := by
  refine ⟨?_, fun h ↦ ?_⟩
  · rintro ⟨k, h1k, h2k⟩ ⟨l, rfl⟩
    replace h1k := lt_of_mul_lt_mul_left h1k (by omega)
    replace h2k := lt_of_mul_lt_mul_left h2k (by omega)
    rw [Int.lt_add_one_iff, ← Int.not_lt] at h2k
    exact h2k h1k
  · rw [dvd_iff_emod_eq_zero, ← Ne] at h
    rw [← emod_add_ediv m n]
    refine ⟨m / n, Int.lt_add_of_pos_left _ ?_, ?_⟩
    · have := emod_nonneg m (Int.ne_of_gt hn)
      omega
    · rw [Int.add_comm _ (1 : ℤ), Int.mul_add, Int.mul_one]
      exact Int.add_lt_add_right (emod_lt_of_pos _ hn) _

lemma natAbs_ediv_of_dvd (a b : ℤ) (H : b ∣ a) : natAbs (a / b) = natAbs a / natAbs b := by
  if h : b = 0 then
    simp_all
  else
    simp [natAbs_ediv, H, h]

lemma dvd_of_mul_dvd_mul_left (ha : a ≠ 0) (h : a * m ∣ a * n) : m ∣ n := by
  obtain ⟨b, hb⟩ := h
  rw [Int.mul_assoc, Int.mul_eq_mul_left_iff ha] at hb
  exact ⟨_, hb⟩

lemma dvd_of_mul_dvd_mul_right (ha : a ≠ 0) (h : m * a ∣ n * a) : m ∣ n :=
  dvd_of_mul_dvd_mul_left ha (by simpa [Int.mul_comm] using h)

lemma eq_mul_div_of_mul_eq_mul_of_dvd_left (hb : b ≠ 0) (hbc : b ∣ c) (h : b * a = c * d) :
    a = c / b * d := by
  obtain ⟨k, rfl⟩ := hbc
  rw [Int.mul_ediv_cancel_left _ hb]
  rwa [Int.mul_assoc, Int.mul_eq_mul_left_iff hb] at h

lemma ofNat_add_negSucc_of_ge {m n : ℕ} (h : n.succ ≤ m) :
    ofNat m + -[n+1] = ofNat (m - n.succ) := by
  rw [negSucc_eq, ofNat_eq_natCast, ofNat_eq_natCast, ← Int.natCast_one, ← Int.natCast_add,
    ← Int.sub_eq_add_neg, ← Int.natCast_sub h]

/-! #### `/` and ordering -/

lemma natAbs_eq_of_dvd_dvd (hmn : m ∣ n) (hnm : n ∣ m) : natAbs m = natAbs n :=
  Nat.dvd_antisymm (natAbs_dvd_natAbs.2 hmn) (natAbs_dvd_natAbs.2 hnm)

lemma ediv_dvd_of_dvd (hmn : m ∣ n) : n / m ∣ n := by
  obtain rfl | hm := Decidable.em (m = 0)
  · simpa using hmn
  · obtain ⟨a, ha⟩ := hmn
    simp [ha, Int.mul_ediv_cancel_left _ hm, Int.dvd_mul_left]

lemma le_iff_pos_of_dvd (ha : 0 < a) (hab : a ∣ b) : a ≤ b ↔ 0 < b :=
  ⟨Int.lt_of_lt_of_le ha, (Int.le_of_dvd · hab)⟩

lemma le_add_iff_lt_of_dvd_sub (ha : 0 < a) (hab : a ∣ c - b) : a + b ≤ c ↔ b < c := by
  rw [Int.add_le_iff_le_sub, ← Int.sub_pos, le_iff_pos_of_dvd ha hab]

/-! ### sign -/

lemma sign_natCast_of_ne_zero {n : ℕ} (hn : n ≠ 0) : Int.sign n = 1 := sign_ofNat_of_nonzero hn

lemma sign_add_eq_of_sign_eq : ∀ {m n : ℤ}, m.sign = n.sign → (m + n).sign = n.sign := by
  have : (1 : ℤ) ≠ -1 := by decide
  rintro ((_ | m) | m) ((_ | n) | n) <;> simp [this, this.symm] <;> omega

/-! ### toNat -/

@[simp] lemma toNat_natCast (n : ℕ) : toNat ↑n = n := rfl

@[simp] lemma toNat_natCast_add_one {n : ℕ} : ((n : ℤ) + 1).toNat = n + 1 := rfl

@[simp]
lemma lt_toNat {m : ℕ} : m < toNat n ↔ (m : ℤ) < n := by rw [← Int.not_le, ← Nat.not_le, toNat_le]

lemma lt_of_toNat_lt {a b : ℤ} (h : toNat a < toNat b) : a < b :=
  (toNat_lt_toNat <| lt_toNat.1 <| Nat.lt_of_le_of_lt (Nat.zero_le _) h).1 h

@[simp] lemma toNat_pred_coe_of_pos {i : ℤ} (h : 0 < i) : ((i.toNat - 1 : ℕ) : ℤ) = i - 1 := by
  simp only [lt_toNat, Int.cast_ofNat_Int, h, natCast_pred_of_pos, Int.le_of_lt h, toNat_of_nonneg]

theorem toNat_sub_of_le {a b : ℤ} (h : b ≤ a) : (toNat (a - b) : ℤ) = a - b :=
  Int.toNat_of_nonneg (Int.sub_nonneg_of_le h)

lemma toNat_lt'' {n : ℕ} (hn : n ≠ 0) : m.toNat < n ↔ m < n := by
  rw [← toNat_lt_toNat, toNat_natCast]; omega

/-- The modulus of an integer by another as a natural. Uses the E-rounding convention. -/
def natMod (m n : ℤ) : ℕ := (m % n).toNat

lemma natMod_lt {n : ℕ} (hn : n ≠ 0) : m.natMod n < n :=
  (toNat_lt'' hn).2 <| emod_lt_of_pos _ <| by omega

attribute [simp] Int.natCast_pow

/-- For use in `Mathlib.Tactic.NormNum.Pow` -/
@[simp] lemma pow_eq (m : ℤ) (n : ℕ) : m.pow n = m ^ n := rfl

end Int
