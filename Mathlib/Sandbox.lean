import Mathlib.NumberTheory.NumberField.Units.Basic

section misc

open Polynomial

theorem Polynomial.splits_of_degree_two {K L : Type*} [Field K] [Field L] (i : K →+* L)
    {f : Polynomial K} (hf₁ : f.natDegree = 2) (hf₂ : ∃ x : L, eval₂ i x f = 0) :
    Splits i f := by
  have hf₀ : f ≠ 0 := ne_zero_of_natDegree_gt (hf₁ ▸ zero_lt_two)
  obtain ⟨x, hx⟩ := hf₂
  rw [← mem_roots_map_of_injective i.injective hf₀, mem_roots'] at hx
  have h : (map i f /ₘ (X - C x)).natDegree = 1 := by
    rw [natDegree_divByMonic _ (monic_X_sub_C x), natDegree_map, hf₁, natDegree_X_sub_C]
  rw [← splits_id_iff_splits, ← mul_divByMonic_eq_iff_isRoot.mpr hx.2]
  exact (splits_mul_iff _ (X_sub_C_ne_zero x) (by simp [ne_zero_of_natDegree_gt, h])).mpr
    ⟨splits_X_sub_C  _, splits_of_natDegree_le_one (RingHom.id L) (by rw [h])⟩

theorem normal_of_rank_eq_two (F K : Type*) [Field F] [Field K] [Algebra F K]
    (h : Module.finrank F K = 2) :
    Normal F K :=
{ isAlgebraic := by
    have : Module.Finite F K := Module.finite_of_finrank_eq_succ h
    exact fun x ↦ Algebra.IsAlgebraic.isAlgebraic x
  splits' := by
    have : FiniteDimensional F K := Module.finite_of_finrank_eq_succ h
    intro x
    obtain h | h := le_iff_lt_or_eq.mp (h ▸ minpoly.natDegree_le x)
    · exact Polynomial.splits_of_natDegree_le_one _ (by rwa [Nat.le_iff_lt_add_one])
    · exact Polynomial.splits_of_degree_two _ h ⟨x, minpoly.aeval F x⟩ }

end misc

noncomputable section

open NumberField InfinitePlace ComplexEmbedding Units

class IsCMExtension (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] : Prop where
  isTotallyComplex : IsTotallyComplex L
  isTotallyReal : IsTotallyReal K
  quadratic : Module.finrank K L = 2

namespace IsCMExtension

open scoped ComplexConjugate

variable (K L : Type*) [Field L] [NumberField L] [Field K] [NumberField K] [Algebra K L]

instance [IsCMExtension K L] : IsGalois K L :=
{ to_isSeparable := Algebra.IsSeparable.of_integral K L
  to_normal := normal_of_rank_eq_two _ _ quadratic }

variable {L}

theorem exists_isConj [hcm : IsCMExtension K L] (φ : L →+* ℂ) :
    ∃ σ : L ≃ₐ[K] L, IsConj φ σ :=
  exists_isConj_of_not_isUnramified <|
    not_isUnramified_iff.mpr ⟨hcm.isTotallyComplex.isComplex _, hcm.isTotallyReal.isReal _⟩

variable {K} in
theorem isConj_eq_isConj [hcm : IsCMExtension K L] {φ ψ : L →+* ℂ} {σ τ : L ≃ₐ[K] L}
    (hφ : IsConj φ σ) (hψ : IsConj ψ τ) : σ = τ := by
  have : Fintype.card (L ≃ₐ[K] L) = 2 := hcm.quadratic ▸ IsGalois.card_aut_eq_finrank K L
  rw [← Nat.card_eq_fintype_card, Nat.card_eq_two_iff' 1] at this
  apply ExistsUnique.unique this
  · by_contra h
    rw [h, isConj_one_iff, ← isReal_mk_iff] at hφ
    exact not_isComplex_iff_isReal.mpr hφ (hcm.isTotallyComplex.isComplex _)
  · by_contra h
    rw [h, isConj_one_iff, ← isReal_mk_iff] at hψ
    exact not_isComplex_iff_isReal.mpr hψ (hcm.isTotallyComplex.isComplex _)

def complexConj [IsCMExtension K L] : L ≃ₐ[K] L :=
  (exists_isConj K (Classical.choice (inferInstance : Nonempty _))).choose

theorem isConj_complexConj [IsCMExtension K L] (φ : L →+* ℂ) :
    IsConj φ (complexConj K) := by
  obtain ⟨σ, hσ⟩ := exists_isConj K φ
  have := (exists_isConj K (Classical.choice (inferInstance : Nonempty (L →+* ℂ)))).choose_spec
  rwa [isConj_eq_isConj hσ this] at hσ

theorem complexConj_apply [IsCMExtension K L] (φ : L →+* ℂ) (x : L) :
    φ (complexConj K x) = conj (φ x) := by
  rw [IsConj.eq (isConj_complexConj K φ), RCLike.star_def]

variable (L) in
def realUnits : Subgroup (𝓞 L)ˣ := (Units.map (algebraMap (𝓞 K) (𝓞 L)).toMonoidHom).range

theorem finiteIndex_realUnits [IsCMExtension K L] :
    (realUnits K L).FiniteIndex := by
  rw [Subgroup.finiteIndex_iff, Subgroup.index_ne_zero_iff_finite]
  


example [IsCMExtension K L] : 1 = 0 := by
  have : ((Units.map (algebraMap (𝓞 K) (𝓞 L)).toMonoidHom).range ⊔ torsion L).index ≤ 2 := sorry





end IsCMExtension
