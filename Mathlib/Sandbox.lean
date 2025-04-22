import Mathlib

section IsQuadraticExtension

open IntermediateField

-- theorem Algebra.norm_eq_norm_adjoin0 {K : Type*} {L : Type*} [Field K] [Field L] [Algebra K L]
--     [FiniteDimensional K L] (x : L) :
--     Algebra.norm K x = Algebra.norm K (AdjoinSimple.gen K x) ^ Module.finrank K⟮x⟯ L := by
--   rw [← Algebra.norm_norm (S := K⟮x⟯)]
--   conv in x => rw [← AdjoinSimple.algebraMap_gen K x]
--   rw [Algebra.norm_algebraMap, MonoidHom.map_pow]

-- theorem norm_adjoinSimpleGen {K : Type*} {L : Type*} [Field K] [Field L]
--     [Algebra K L] {x : L} (hx : IsIntegral K x) :
--     Algebra.norm K (IntermediateField.AdjoinSimple.gen K x) =
--       (-1) ^ (minpoly K x).natDegree * (minpoly K x).coeff 0 := by
--   simpa [minpoly_gen K x] using
--     Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly <| adjoin.powerBasis hx

-- theorem norm_eq_mul_minpoly_coeff_zero_pow (K : Type*) {L : Type*} [Field K] [Field L]
--     [Algebra K L] [FiniteDimensional K L] (x : L) :
--     Algebra.norm K x =
--       ((-1) ^ (minpoly K x).natDegree * (minpoly K x).coeff 0) ^ Module.finrank (↥K⟮x⟯) L := by
--   rw [Algebra.norm_eq_norm_adjoin, norm_adjoinSimpleGen]
--   exact Algebra.IsIntegral.isIntegral x

-- variable {K L : Type*} [Field K] [Field L]
--     [Algebra K L] in
-- #synth CompleteLattice (IntermediateField K L)

-- theorem IntermediateField.isSimpleOrder_of_finrank_prime {K L : Type*} [Field K] [Field L]
--     [Algebra K L] (hp : Nat.Prime (Module.finrank K L)) :
--     IsSimpleOrder (IntermediateField K L) := by
--   have : Algebra.IsAlgebraic K L := by
--     have : Module.Finite K L := Module.finite_of_finrank_pos <| Nat.Prime.pos hp
--     exact Algebra.IsAlgebraic.of_finite K L
--   rw [OrderIso.isSimpleOrder_iff subalgebraEquivIntermediateField.symm]
--   exact Subalgebra.isSimpleOrder_of_finrank_prime K L hp

-- theorem IntermediateField.isSimpleOrder_of_finrank {K L : Type*} [Field K] [Field L]
--     [Algebra K L] (h : Module.finrank K L = 2) :
--     IsSimpleOrder (IntermediateField K L) :=
--   IntermediateField.isSimpleOrder_of_finrank_prime (h ▸ Nat.prime_two)

-- example {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [Module.Free R S]
--     [Module.Finite R S] (x : S) : (Algebra.lmul R S x).charpoly.aeval x = 0 := by
--   convert LinearMap.congr_fun (LinearMap.mul R S x).aeval_self_charpoly 1
--   simp_rw [Polynomial.aeval_endomorphism]
--   simp_rw [← Algebra.coe_lmul_eq_mul, ← map_pow, Algebra.coe_lmul_eq_mul, LinearMap.mul_apply_apply,
--     mul_one]
--   rw [Polynomial.aeval_eq_smeval, Polynomial.smeval_def]
--   rfl

theorem IsQuadraticExtension.exists_sq_mem_and_eq_top (F K : Type*) [Field F] [Field K]
    [NeZero (2 : F)] [h : IsQuadraticExtension F K] :
    ∃ x : K, x ^ 2 ∈ (algebraMap F K).range ∧ F⟮x⟯ = ⊤ := by
  obtain ⟨y, hy⟩ := exists_linearIndependent_pair_of_one_lt_finrank
    (h.finrank_eq_two ▸ one_lt_two) one_ne_zero
  let x := y - algebraMap F K ((Algebra.trace F K y) / 2)
  have hx₀ : x ≠ 0 := by
    contrapose! hy
    simp only [LinearIndependent.pair_iff, not_forall, _root_.not_imp, exists_prop, not_and]
    refine ⟨-((Algebra.trace F K) y / 2), 1, ?_, fun _ ↦ one_ne_zero⟩
    rwa [add_comm, one_smul, neg_smul, ← sub_eq_add_neg, ← Algebra.algebraMap_eq_smul_one]
  have hx₁ : Algebra.trace F K x = 0 := by
    rw [map_sub, Algebra.trace_algebraMap, h.finrank_eq_two, nsmul_eq_mul, Nat.cast_ofNat,
        ← mul_div_assoc, mul_div_cancel_left₀ _ two_ne_zero, sub_self]
  have hx₂ : F⟮x⟯ = ⊤ := by
    refine ((isSimpleOrder_of_finrank_prime
      (h.finrank_eq_two ▸ Nat.prime_two)).eq_bot_or_eq_top F⟮x⟯).resolve_left ?_
    by_contra h₀
    obtain ⟨a , ha⟩ := mem_bot.mp <| adjoin_simple_eq_bot_iff.mp h₀
    rw [← ha, Algebra.trace_algebraMap, nsmul_eq_mul, h.finrank_eq_two, Nat.cast_ofNat,
      mul_eq_zero_iff_left two_ne_zero] at hx₁
    simp_all
  have hx₃ : (minpoly F x).natDegree = 2 :=
    (h.finrank_eq_two ▸ Field.primitive_element_iff_minpoly_natDegree_eq F x).mp (hx₂)
  have hx₄ : (minpoly F x).coeff 1 = 0 := by
    have := trace_eq_finrank_mul_minpoly_nextCoeff F x
    rwa [hx₂, IntermediateField.finrank_top, Nat.cast_one, mul_neg, one_mul,
      Polynomial.nextCoeff_of_natDegree_pos (Nat.lt_of_sub_eq_succ hx₃), hx₃, hx₁,
      zero_eq_neg] at this
  have hx₅ : (minpoly F x).coeff 0 = Algebra.norm F x := by
    have := Algebra.norm_eq_mul_minpoly_coeff_zero_pow F x
    rwa [hx₂, IntermediateField.finrank_top, pow_one, hx₃, neg_one_sq, one_mul, eq_comm] at this
  refine ⟨x, ⟨-(Algebra.norm F x), ?_⟩, hx₂⟩
  have h_eq := congr_arg ((↑) : _ → K) (minpoly.aeval F x)
  rwa [Polynomial.aeval_eq_sum_range, hx₃, Finset.sum_range, Fin.sum_univ_three, Fin.val_zero,
    Fin.val_one, Fin.val_two, pow_zero, pow_one, ← hx₃, Polynomial.Monic.coeff_natDegree
    (minpoly.monic (Algebra.IsIntegral.isIntegral x)), hx₃, one_smul, hx₄, zero_smul, add_zero,
    ← neg_eq_iff_add_eq_zero, hx₅, ← Algebra.algebraMap_eq_smul_one, ← map_neg] at h_eq

end IsQuadraticExtension
