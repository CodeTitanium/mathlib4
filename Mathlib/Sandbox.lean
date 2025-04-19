import Mathlib

section IsQuadraticExtension

open IntermediateField

theorem Algebra.norm_eq_norm_adjoin0 {K : Type*} {L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (x : L) :
    Algebra.norm K x = Algebra.norm K (AdjoinSimple.gen K x) ^ Module.finrank K⟮x⟯ L := by
  rw [← Algebra.norm_norm (S := K⟮x⟯)]
  conv in x => rw [← AdjoinSimple.algebraMap_gen K x]
  rw [Algebra.norm_algebraMap, MonoidHom.map_pow]

theorem norm_adjoinSimpleGen {K : Type*} {L : Type*} [Field K] [Field L]
    [Algebra K L] {x : L} (hx : IsIntegral K x) :
    Algebra.norm K (IntermediateField.AdjoinSimple.gen K x) =
      (-1) ^ (minpoly K x).natDegree * (minpoly K x).coeff 0 := by
  simpa [minpoly_gen K x] using
    Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly <| adjoin.powerBasis hx

theorem norm_eq_mul_minpoly_coeff_zero_pow (K : Type*) {L : Type*} [Field K] [Field L]
    [Algebra K L] [FiniteDimensional K L] (x : L) :
    Algebra.norm K x =
      ((-1) ^ (minpoly K x).natDegree * (minpoly K x).coeff 0) ^ Module.finrank (↥K⟮x⟯) L := by
  rw [Algebra.norm_eq_norm_adjoin0, norm_adjoinSimpleGen]
  exact Algebra.IsIntegral.isIntegral x

theorem IntermediateField.isSimpleOrder_of_finrank_prime {K L : Type*} [Field K] [Field L]
    [Algebra K L] (hp : Nat.Prime (Module.finrank K L)) :
    IsSimpleOrder (IntermediateField K L) := by
  have : Algebra.IsAlgebraic K L := by
    have : Module.Finite K L := Module.finite_of_finrank_pos <| Nat.Prime.pos hp
    exact Algebra.IsAlgebraic.of_finite K L
  rw [OrderIso.isSimpleOrder_iff subalgebraEquivIntermediateField.symm]
  exact Subalgebra.isSimpleOrder_of_finrank_prime K L hp

theorem IntermediateField.isSimpleOrder_of_finrank {K L : Type*} [Field K] [Field L]
    [Algebra K L] (h : Module.finrank K L = 2) :
    IsSimpleOrder (IntermediateField K L) :=
  IntermediateField.isSimpleOrder_of_finrank_prime (h ▸ Nat.prime_two)

example {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [Module.Free R S]
    [Module.Finite R S] (x : S) : (Algebra.lmul R S x).charpoly.aeval x = 0 := by
  convert LinearMap.congr_fun (LinearMap.mul R S x).aeval_self_charpoly 1
  simp_rw [Polynomial.aeval_endomorphism]
  simp_rw [← Algebra.coe_lmul_eq_mul, ← map_pow, Algebra.coe_lmul_eq_mul, LinearMap.mul_apply_apply,
    mul_one]
  rw [Polynomial.aeval_eq_smeval, Polynomial.smeval_def]
  rfl

example (F K : Type*) [Field F] [Field K] [NeZero (2 : F)] [h : IsQuadraticExtension F K] :
    ∃ x : K, x ^ 2 ∈ (algebraMap F K).range ∧ F⟮x⟯ = ⊤ := by
  obtain ⟨x, hx₁, hx₂⟩ : ∃ x, x ≠ 0 ∧ Algebra.trace F K x = 0 := sorry
  let B := Algebra.adjoin.powerBasis (K := F) (x := x) (Algebra.IsIntegral.isIntegral x)
  have : F⟮x⟯ = ⊤ := by
    have := (IntermediateField.isSimpleOrder_of_finrank h.finrank_eq_two).eq_bot_or_eq_top F⟮x⟯
    refine this.resolve_left ?_
    by_contra h
    rw [adjoin_simple_eq_bot_iff, mem_bot] at h
    obtain ⟨a, rfl⟩ := h
    rw [Algebra.trace_algebraMap, nsmul_eq_mul, mul_eq_zero] at hx₂
    rw [ne_eq, map_eq_zero] at hx₁
    simp_rw [hx₁, or_false, h.finrank_eq_two, Nat.cast_ofNat] at hx₂
    exact two_ne_zero hx₂
  have h₁ : B.dim = 2 := by
    unfold B
    rw [Algebra.adjoin.powerBasis_dim]
    rw [Field.primitive_element_iff_minpoly_natDegree_eq] at this
    rw [this]
    exact h.finrank_eq_two
  have h₂ : (minpoly F x).natDegree = 2 := sorry
  have h₃ : Module.finrank F⟮x⟯ K = 1 := sorry
  rw [← this]
  refine ⟨x, ?_, ?_⟩
  · refine ⟨- Algebra.norm F x, ?_⟩
--    rw [Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly, map_neg, map_mul, map_pow]
--    simp [h₁]
    have h := congr_arg ((↑) : _ → K) (minpoly.aeval F x)
    rw [Polynomial.aeval_eq_sum_range] at h
    rw [h₂] at h
    -- rw [PowerBasis.natDegree_minpoly, h₁] at h
    rw [@Finset.sum_range] at h
    rw [Fin.sum_univ_three] at h
    simp only [Nat.reduceAdd, Fin.isValue, Fin.val_zero, pow_zero, Fin.val_one, pow_one,
      Fin.val_two] at h
    rw [show (minpoly F x).coeff 2 = 1 by sorry, one_smul] at h
    have t₁ := trace_eq_finrank_mul_minpoly_nextCoeff F x
    rw [h₃, Nat.cast_one, mul_neg, one_mul] at t₁
    rw [Polynomial.nextCoeff_of_natDegree_pos sorry, h₂, show 2 - 1 = 1 by norm_num, hx₂,
      zero_eq_neg] at t₁
    rw [t₁, zero_smul, add_zero] at h
    have t₂ := norm_eq_mul_minpoly_coeff_zero_pow F x
    rw [h₂, h₃] at t₂
    simp only [even_two, Even.neg_pow, one_pow, one_mul, pow_one] at t₂
    rw [← t₂] at h
    rw [← neg_eq_iff_add_eq_zero] at h
    rw [← h]
    simp only [map_neg, neg_inj]
    rw [Algebra.algebraMap_eq_smul_one]
  · rfl







#exit
    have t₀ := Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly B
    rw [h₁, neg_one_sq, one_mul] at t₀

    simp only [one_smul, map_pow, map_zero] at h
    rw [← t₀] at h
    rw [Subalgebra.coe_add, Subalgebra.coe_add, Subalgebra.coe_pow] at h
    have t₁ := trace_eq_finrank_mul_minpoly_nextCoeff F x
--    have t₁ := PowerBasis.trace_gen_eq_nextCoeff_minpoly B
    simp only [SetLike.val_smul, OneMemClass.coe_one, ZeroMemClass.coe_zero] at h

    let e : F⟮x⟯ ≃ₐ[F] K := by
      let f := IntermediateField.equivOfEq this
      exact (f.trans topEquiv)
    rw [← neg_eq_iff_add_eq_zero] at h
    rw [← h]

    have : Algebra.trace F (Algebra.adjoin F {x}) B.gen = Algebra.trace F K x := by
      have := Algebra.trace_eq_of_algEquiv e.symm x
      rw [← this]






    sorry
  · sorry


  let B := h.finrank_eq_two ▸ Module.finBasis F K
  obtain ⟨x, hx₁, hx₂⟩ : ∃ x, x ∉ (algebraMap F K).range ∧ Algebra.trace F K x = 0 := sorry
  refine ⟨x, ?_, ?_⟩
  use Algebra.norm F x
  rw [Algebra.norm_eq_matrix_det B]
  rw [Matrix.det_fin_two]

  have := Algebra.norm_one_add_smul (1 : F) x
  simp at this
  obtain ⟨r, hr⟩ := this

  let V := B.toMatrixEquiv

  sorry

end IsQuadraticExtension
