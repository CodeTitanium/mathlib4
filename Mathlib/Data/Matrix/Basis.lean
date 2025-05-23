/-
Copyright (c) 2020 Jalex Stark. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jalex Stark, Kim Morrison, Eric Wieser, Oliver Nash, Wen Yang
-/
import Mathlib.Data.Matrix.Basic

/-!
# Matrices with a single non-zero element.

This file provides `Matrix.stdBasisMatrix`. The matrix `Matrix.stdBasisMatrix i j c` has `c`
at position `(i, j)`, and zeroes elsewhere.
-/

assert_not_exists Matrix.trace

variable {l m n o : Type*}
variable {R α β : Type*}

namespace Matrix

variable [DecidableEq l] [DecidableEq m] [DecidableEq n] [DecidableEq o]

section Zero
variable [Zero α]

/-- `stdBasisMatrix i j a` is the matrix with `a` in the `i`-th row, `j`-th column,
and zeroes elsewhere.
-/
def stdBasisMatrix (i : m) (j : n) (a : α) : Matrix m n α :=
  of <| fun i' j' => if i = i' ∧ j = j' then a else 0

theorem stdBasisMatrix_eq_of_single_single (i : m) (j : n) (a : α) :
    stdBasisMatrix i j a = Matrix.of (Pi.single i (Pi.single j a)) := by
  ext a b
  unfold stdBasisMatrix
  by_cases hi : i = a <;> by_cases hj : j = b <;> simp [*]

@[simp]
theorem of_symm_stdBasisMatrix (i : m) (j : n) (a : α) :
    of.symm (stdBasisMatrix i j a) = Pi.single i (Pi.single j a) :=
  congr_arg of.symm <| stdBasisMatrix_eq_of_single_single i j a

@[simp]
theorem smul_stdBasisMatrix [SMulZeroClass R α] (r : R) (i : m) (j : n) (a : α) :
    r • stdBasisMatrix i j a = stdBasisMatrix i j (r • a) := by
  unfold stdBasisMatrix
  ext
  simp [smul_ite]

@[simp]
theorem stdBasisMatrix_zero (i : m) (j : n) : stdBasisMatrix i j (0 : α) = 0 := by
  unfold stdBasisMatrix
  ext
  simp

@[simp]
lemma transpose_stdBasisMatrix (i : m) (j : n) (a : α) :
    (stdBasisMatrix i j a)ᵀ = stdBasisMatrix j i a := by
  aesop (add unsafe unfold stdBasisMatrix)

@[simp]
lemma map_stdBasisMatrix (i : m) (j : n) (a : α) {β : Type*} [Zero β]
    {F : Type*} [FunLike F α β] [ZeroHomClass F α β] (f : F) :
    (stdBasisMatrix i j a).map f = stdBasisMatrix i j (f a) := by
  aesop (add unsafe unfold stdBasisMatrix)

end Zero

theorem stdBasisMatrix_add [AddZeroClass α] (i : m) (j : n) (a b : α) :
    stdBasisMatrix i j (a + b) = stdBasisMatrix i j a + stdBasisMatrix i j b := by
  ext
  simp only [stdBasisMatrix, of_apply]
  split_ifs with h <;> simp [h]

theorem mulVec_stdBasisMatrix [NonUnitalNonAssocSemiring α] [Fintype m]
    (i : n) (j : m) (c : α) (x : m → α) :
    mulVec (stdBasisMatrix i j c) x = Function.update (0 : n → α) i (c * x j) := by
  ext i'
  simp [stdBasisMatrix, mulVec, dotProduct]
  rcases eq_or_ne i i' with rfl|h
  · simp
  simp [h, h.symm]

theorem matrix_eq_sum_stdBasisMatrix [AddCommMonoid α] [Fintype m] [Fintype n] (x : Matrix m n α) :
    x = ∑ i : m, ∑ j : n, stdBasisMatrix i j (x i j) := by
  ext i j
  rw [← Fintype.sum_prod_type']
  simp [stdBasisMatrix, Matrix.sum_apply, Matrix.of_apply, ← Prod.mk_inj]

theorem stdBasisMatrix_eq_single_vecMulVec_single [MulZeroOneClass α] (i : m) (j : n) :
    stdBasisMatrix i j (1 : α) = vecMulVec (Pi.single i 1) (Pi.single j 1) := by
  ext i' j'
  simp [-mul_ite, stdBasisMatrix, vecMulVec, ite_and, Pi.single_apply, eq_comm]

-- todo: the old proof used fintypes, I don't know `Finsupp` but this feels generalizable
@[elab_as_elim]
protected theorem induction_on'
    [AddCommMonoid α] [Finite m] [Finite n] {P : Matrix m n α → Prop} (M : Matrix m n α)
    (h_zero : P 0) (h_add : ∀ p q, P p → P q → P (p + q))
    (h_std_basis : ∀ (i : m) (j : n) (x : α), P (stdBasisMatrix i j x)) : P M := by
  cases nonempty_fintype m; cases nonempty_fintype n
  rw [matrix_eq_sum_stdBasisMatrix M, ← Finset.sum_product']
  apply Finset.sum_induction _ _ h_add h_zero
  · intros
    apply h_std_basis

@[elab_as_elim]
protected theorem induction_on
    [AddCommMonoid α] [Finite m] [Finite n] [Nonempty m] [Nonempty n]
    {P : Matrix m n α → Prop} (M : Matrix m n α) (h_add : ∀ p q, P p → P q → P (p + q))
    (h_std_basis : ∀ i j x, P (stdBasisMatrix i j x)) : P M :=
  Matrix.induction_on' M
    (by
      inhabit m
      inhabit n
      simpa using h_std_basis default default 0)
    h_add h_std_basis

/-- `Matrix.stdBasisMatrix` as a bundled additive map. -/
@[simps]
def stdBasisMatrixAddMonoidHom [AddCommMonoid α] (i : m) (j : n) : α →+ Matrix m n α where
  toFun := stdBasisMatrix i j
  map_zero' := stdBasisMatrix_zero _ _
  map_add' _ _ := stdBasisMatrix_add _ _ _ _

variable (R)
/-- `Matrix.stdBasisMatrix` as a bundled linear map. -/
@[simps!]
def stdBasisMatrixLinearMap [Semiring R] [AddCommMonoid α] [Module R α] (i : m) (j : n) :
    α →ₗ[R] Matrix m n α where
  __ := stdBasisMatrixAddMonoidHom i j
  map_smul' _ _:= smul_stdBasisMatrix _ _ _ _ |>.symm

section ext

/-- Additive maps from finite matrices are equal if they agree on the standard basis.

See note [partially-applied ext lemmas]. -/
@[local ext]
theorem ext_addMonoidHom
    [Finite m] [Finite n] [AddCommMonoid α] [AddCommMonoid β] ⦃f g : Matrix m n α →+ β⦄
    (h : ∀ i j, f.comp (stdBasisMatrixAddMonoidHom i j) = g.comp (stdBasisMatrixAddMonoidHom i j)) :
    f = g := by
  cases nonempty_fintype m
  cases nonempty_fintype n
  ext x
  rw [matrix_eq_sum_stdBasisMatrix x]
  simp_rw [map_sum]
  congr! 2
  exact DFunLike.congr_fun (h _ _) _

/-- Linear maps from finite matrices are equal if they agree on the standard basis.

See note [partially-applied ext lemmas]. -/
@[local ext]
theorem ext_linearMap
    [Finite m] [Finite n][Semiring R] [AddCommMonoid α] [AddCommMonoid β] [Module R α] [Module R β]
    ⦃f g : Matrix m n α →ₗ[R] β⦄
    (h : ∀ i j, f ∘ₗ stdBasisMatrixLinearMap R i j = g ∘ₗ stdBasisMatrixLinearMap R i j) :
    f = g :=
  LinearMap.toAddMonoidHom_injective <| ext_addMonoidHom fun i j =>
    congrArg LinearMap.toAddMonoidHom <| h i j

end ext

namespace StdBasisMatrix

section

variable [Zero α] (i : m) (j : n) (c : α) (i' : m) (j' : n)

@[simp]
theorem apply_same : stdBasisMatrix i j c i j = c :=
  if_pos (And.intro rfl rfl)

@[simp]
theorem apply_of_ne (h : ¬(i = i' ∧ j = j')) : stdBasisMatrix i j c i' j' = 0 := by
  simp only [stdBasisMatrix, and_imp, ite_eq_right_iff, of_apply]
  tauto

@[simp]
theorem apply_of_row_ne {i i' : m} (hi : i ≠ i') (j j' : n) (a : α) :
    stdBasisMatrix i j a i' j' = 0 := by simp [hi]

@[simp]
theorem apply_of_col_ne (i i' : m) {j j' : n} (hj : j ≠ j') (a : α) :
    stdBasisMatrix i j a i' j' = 0 := by simp [hj]

end

section
variable [Zero α] (i j : n) (c : α)

@[simp]
theorem diag_zero (h : j ≠ i) : diag (stdBasisMatrix i j c) = 0 :=
  funext fun _ => if_neg fun ⟨e₁, e₂⟩ => h (e₂.trans e₁.symm)

@[simp]
theorem diag_same : diag (stdBasisMatrix i i c) = Pi.single i c := by
  ext j
  by_cases hij : i = j <;> (try rw [hij]) <;> simp [hij]

end

section mul
variable [Fintype m] [NonUnitalNonAssocSemiring α] (c : α)

omit [DecidableEq n] in
@[simp]
theorem mul_left_apply_same (i : l) (j : m) (b : n) (M : Matrix m n α) :
    (stdBasisMatrix i j c * M) i b = c * M j b := by simp [mul_apply, stdBasisMatrix]

omit [DecidableEq l] in
@[simp]
theorem mul_right_apply_same (i : m) (j : n) (a : l) (M : Matrix l m α) :
    (M * stdBasisMatrix i j c) a j = M a i * c := by simp [mul_apply, stdBasisMatrix, mul_comm]

omit [DecidableEq n] in
@[simp]
theorem mul_left_apply_of_ne (i : l) (j : m) (a : l) (b : n) (h : a ≠ i) (M : Matrix m n α) :
    (stdBasisMatrix i j c * M) a b = 0 := by simp [mul_apply, h.symm]

omit [DecidableEq l] in
@[simp]
theorem mul_right_apply_of_ne (i : m) (j : n) (a : l) (b : n) (hbj : b ≠ j) (M : Matrix l m α) :
    (M * stdBasisMatrix i j c) a b = 0 := by simp [mul_apply, hbj.symm]

@[simp]
theorem mul_same (i : l) (j : m) (k : n) (d : α) :
    stdBasisMatrix i j c * stdBasisMatrix j k d = stdBasisMatrix i k (c * d) := by
  ext a b
  simp only [mul_apply, stdBasisMatrix, boole_mul]
  by_cases h₁ : i = a <;> by_cases h₂ : k = b <;> simp [h₁, h₂]

@[simp]
theorem stdBasisMatrix_mul_mul_stdBasisMatrix [Fintype n]
    (i : l) (i' : m) (j' : n) (j : o) (a : α) (x : Matrix m n α) (b : α) :
    stdBasisMatrix i i' a * x * stdBasisMatrix j' j b = stdBasisMatrix i j (a * x i' j' * b) := by
  ext i'' j''
  simp only [mul_apply, stdBasisMatrix, boole_mul]
  by_cases h₁ : i = i'' <;> by_cases h₂ : j = j'' <;> simp [h₁, h₂]

@[simp]
theorem mul_of_ne (i : l) (j k : m) {l : n} (h : j ≠ k) (d : α) :
    stdBasisMatrix i j c * stdBasisMatrix k l d = 0 := by
  ext a b
  simp only [mul_apply, boole_mul, stdBasisMatrix, of_apply]
  by_cases h₁ : i = a
  · simp [h₁, h, Finset.sum_eq_zero]
  · simp [h₁]

end mul

end StdBasisMatrix

section Commute

variable [Fintype n] [Semiring α]

theorem row_eq_zero_of_commute_stdBasisMatrix {i j k : n} {M : Matrix n n α}
    (hM : Commute (stdBasisMatrix i j 1) M) (hkj : k ≠ j) : M j k = 0 := by
  have := ext_iff.mpr hM i k
  aesop

theorem col_eq_zero_of_commute_stdBasisMatrix {i j k : n} {M : Matrix n n α}
    (hM : Commute (stdBasisMatrix i j 1) M) (hki : k ≠ i) : M k i = 0 := by
  have := ext_iff.mpr hM k j
  aesop

theorem diag_eq_of_commute_stdBasisMatrix {i j : n} {M : Matrix n n α}
    (hM : Commute (stdBasisMatrix i j 1) M) : M i i = M j j := by
  have := ext_iff.mpr hM i j
  aesop

/-- `M` is a scalar matrix if it commutes with every non-diagonal `stdBasisMatrix`. -/
theorem mem_range_scalar_of_commute_stdBasisMatrix {M : Matrix n n α}
    (hM : Pairwise fun i j => Commute (stdBasisMatrix i j 1) M) :
    M ∈ Set.range (Matrix.scalar n) := by
  cases isEmpty_or_nonempty n
  · exact ⟨0, Subsingleton.elim _ _⟩
  obtain ⟨i⟩ := ‹Nonempty n›
  refine ⟨M i i, Matrix.ext fun j k => ?_⟩
  simp only [scalar_apply]
  obtain rfl | hkl := Decidable.eq_or_ne j k
  · rw [diagonal_apply_eq]
    obtain rfl | hij := Decidable.eq_or_ne i j
    · rfl
    · exact diag_eq_of_commute_stdBasisMatrix (hM hij)
  · rw [diagonal_apply_ne _ hkl]
    obtain rfl | hij := Decidable.eq_or_ne i j
    · rw [col_eq_zero_of_commute_stdBasisMatrix (hM hkl.symm) hkl]
    · rw [row_eq_zero_of_commute_stdBasisMatrix (hM hij) hkl.symm]

theorem mem_range_scalar_iff_commute_stdBasisMatrix {M : Matrix n n α} :
    M ∈ Set.range (Matrix.scalar n) ↔ ∀ (i j : n), i ≠ j → Commute (stdBasisMatrix i j 1) M := by
  refine ⟨fun ⟨r, hr⟩ i j _ => hr ▸ Commute.symm ?_, mem_range_scalar_of_commute_stdBasisMatrix⟩
  rw [scalar_commute_iff]
  simp

/-- `M` is a scalar matrix if and only if it commutes with every `stdBasisMatrix`. -/
theorem mem_range_scalar_iff_commute_stdBasisMatrix' {M : Matrix n n α} :
    M ∈ Set.range (Matrix.scalar n) ↔ ∀ (i j : n), Commute (stdBasisMatrix i j 1) M := by
  refine ⟨fun ⟨r, hr⟩ i j => hr ▸ Commute.symm ?_,
    fun hM => mem_range_scalar_iff_commute_stdBasisMatrix.mpr <| fun i j _ => hM i j⟩
  rw [scalar_commute_iff]
  simp

end Commute

end Matrix
