import Mathlib.NumberTheory.NumberField.Units.Basic
import Mathlib.RingTheory.RootsOfUnity.Complex

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

theorem IntermediateField.fixedField_top {F : Type*} [Field F] {E : Type*} [Field E] [Algebra F E]
    [FiniteDimensional F E] [IsGalois F E] :
    fixedField (⊤ : Subgroup (E ≃ₐ[F] E)) = ⊥ :=
  IsGalois.intermediateFieldEquivSubgroup.symm.map_bot

theorem IntermediateField.fixedField_bot {F : Type*} [Field F] {E : Type*} [Field E] [Algebra F E]
    [FiniteDimensional F E] [IsGalois F E] :
    fixedField (⊥ : Subgroup (E ≃ₐ[F] E)) = ⊤ :=
  IsGalois.intermediateFieldEquivSubgroup.symm.map_top

theorem Complex.conj_rootsOfUnity {ζ : ℂˣ} {n : ℕ} [NeZero n] (hζ : ζ ∈ rootsOfUnity n ℂ) :
    (starRingEnd ℂ) ζ = ζ⁻¹ := by
  rw [← Units.mul_eq_one_iff_eq_inv, conj_mul', norm_eq_one_of_mem_rootsOfUnity hζ, ofReal_one,
    one_pow]

end misc

noncomputable section

open NumberField InfinitePlace ComplexEmbedding NumberField.Units

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
theorem isConj_ne_one [hcm : IsCMExtension K L] {φ : L →+* ℂ} {σ : L ≃ₐ[K] L} (hφ : IsConj φ σ) :
    σ ≠ 1 := by
  by_contra h
  rw [h, isConj_one_iff, ← isReal_mk_iff] at hφ
  exact not_isComplex_iff_isReal.mpr hφ  (hcm.isTotallyComplex.isComplex _)

variable {K} in
theorem isConj_eq_isConj [hcm : IsCMExtension K L] {φ ψ : L →+* ℂ} {σ τ : L ≃ₐ[K] L}
    (hφ : IsConj φ σ) (hψ : IsConj ψ τ) : σ = τ := by
  have : Fintype.card (L ≃ₐ[K] L) = 2 := hcm.quadratic ▸ IsGalois.card_aut_eq_finrank K L
  rw [← Nat.card_eq_fintype_card, Nat.card_eq_two_iff' 1] at this
  exact ExistsUnique.unique this (isConj_ne_one hφ) (isConj_ne_one hψ)

def complexConj [IsCMExtension K L] : L ≃ₐ[K] L :=
  (exists_isConj K (Classical.choice (inferInstance : Nonempty _))).choose

def ringOfIntegersComplexConj [IsCMExtension K L] : (𝓞 L) ≃ₐ[𝓞 K] (𝓞 L) :=
  RingOfIntegers.mapAlgEquiv (complexConj K)

@[simp]
theorem coe_ringOfIntegersComplexConj [IsCMExtension K L] (x : 𝓞 L) :
    (ringOfIntegersComplexConj K x : L) = complexConj K (x : L) := rfl

def unitsComplexConj [IsCMExtension K L] : (𝓞 L)ˣ ≃* (𝓞 L)ˣ :=
  Units.mapEquiv (ringOfIntegersComplexConj K).toMulEquiv

@[simp]
theorem coe_unitsComplexConj [IsCMExtension K L] (x : (𝓞 L)ˣ) :
    (unitsComplexConj K x : 𝓞 L) = ringOfIntegersComplexConj K (x : 𝓞 L) := rfl

theorem isConj_complexConj [IsCMExtension K L] (φ : L →+* ℂ) :
    IsConj φ (complexConj K) := by
  obtain ⟨σ, hσ⟩ := exists_isConj K φ
  have := (exists_isConj K (Classical.choice (inferInstance : Nonempty (L →+* ℂ)))).choose_spec
  rwa [isConj_eq_isConj hσ this] at hσ

theorem complexConj_ne_one [IsCMExtension K L] :
    complexConj K ≠ (1 : L ≃ₐ[K] L) :=
  isConj_ne_one (exists_isConj K (Classical.choice (inferInstance : Nonempty _))).choose_spec

@[simp]
theorem complexEmbedding_complexConj [IsCMExtension K L] (φ : L →+* ℂ) (x : L) :
    φ (complexConj K x) = conj (φ x) := by
  rw [IsConj.eq (isConj_complexConj K φ), RCLike.star_def]

protected theorem Units.complexEmbedding_complexConj [IsCMExtension K L] (φ : L →+* ℂ)
    (u : (𝓞 L)ˣ) :
    Units.complexEmbedding φ (unitsComplexConj K u) =
      (Units.map (starRingEnd ℂ)) (Units.complexEmbedding φ u) := by
  simp [Units.ext_iff]

@[simp]
theorem unitsComplexConj_torsion [IsCMExtension K L] (ζ : torsion L) :
    unitsComplexConj K (ζ : (𝓞 L)ˣ) = ζ⁻¹ := by
  let φ : L →+* ℂ := Classical.choice (inferInstance : Nonempty _)
  rw [← (Units.complexEmbedding_injective φ).eq_iff, Units.complexEmbedding_complexConj,
    Units.ext_iff, Units.coe_map, MonoidHom.coe_coe, Subgroup.coe_inv, MonoidHom.map_inv,
    Complex.conj_rootsOfUnity (n := torsionOrder L)]
  rw [← map_complexEmbedding_torsion]
  exact Subgroup.apply_coe_mem_map _ (torsion L) ζ

@[simp]
theorem infinitePlace_complexConj [IsCMExtension K L] (w : InfinitePlace L) (x : L) :
    w (complexConj K x) = w x := by
  rw [← norm_embedding_eq, complexEmbedding_complexConj, Complex.norm_conj, norm_embedding_eq]

@[simp]
theorem complexConj_apply_apply [IsCMExtension K L] (x : L) :
    complexConj K (complexConj K x) = x := by
  let φ : L →+* ℂ := Classical.choice (inferInstance : Nonempty _)
  rw [← φ.injective.eq_iff, complexEmbedding_complexConj, complexEmbedding_complexConj,
    Complex.conj_conj]

theorem galoisGroup_eq [hcm : IsCMExtension K L] :
    (⊤ : Subgroup (L ≃ₐ[K] L)).carrier = {1, complexConj K} := by
  classical
  refine (Set.eq_of_subset_of_card_le ?_ ?_).symm
  · intro x
    simp
  · rw [Fintype.card_subtype]
    simp_rw [Subgroup.mem_carrier]
    simp only [Subgroup.mem_top, Finset.filter_True, Finset.card_univ, Fintype.card_ofFinset,
      Set.toFinset_singleton]
    rw [IsGalois.card_aut_eq_finrank, hcm.quadratic]
    refine le_of_eq ?_
    rw [eq_comm]
    refine Finset.card_pair ?_
    exact (complexConj_ne_one K).symm

theorem complexConj_eq_self_iff [IsCMExtension K L] (x : L) :
    complexConj K x = x ↔ x ∈ (algebraMap K L).range := by
  convert (IntermediateField.mem_fixedField_iff (⊤ : Subgroup (L ≃ₐ[K] L)) x).symm using 1
  · simp only [← Subgroup.mem_carrier, galoisGroup_eq, Set.mem_insert_iff, Set.mem_singleton_iff,
      forall_eq_or_imp, AlgEquiv.one_apply, forall_eq, true_and]
  · rw [IntermediateField.fixedField_top, IntermediateField.mem_bot, RingHom.mem_range,
      Set.mem_range]

theorem ringOfIntegersComplexConj_eq_self_iff [IsCMExtension K L] (x : 𝓞 L) :
    ringOfIntegersComplexConj K x = x ↔ x ∈ (algebraMap (𝓞 K) (𝓞 L)).range := by
  rw [← RingOfIntegers.eq_iff, coe_ringOfIntegersComplexConj, complexConj_eq_self_iff,
    RingOfIntegers.coe_eq_algebraMap, RingHom.mem_range, RingHom.mem_range]
  refine ⟨fun ⟨a, ha⟩ ↦ ⟨⟨a, ?_⟩, RingOfIntegers.eq_iff.mp ha⟩, ?_⟩
  · exact (isIntegral_algebraMap_iff
        (FaithfulSMul.algebraMap_injective K L)).mp (ha ▸ RingOfIntegers.isIntegral_coe x)
  · rintro ⟨a, rfl⟩
    exact ⟨a, rfl⟩

variable (L) in
def realUnits : Subgroup (𝓞 L)ˣ := (Units.map (algebraMap (𝓞 K) (𝓞 L)).toMonoidHom).range

theorem unitsComplexConj_eq_self_iff [IsCMExtension K L] (u : (𝓞 L)ˣ) :
    unitsComplexConj K u = u ↔ u ∈ realUnits K L := by
  rw [← Units.eq_iff, coe_unitsComplexConj, ringOfIntegersComplexConj_eq_self_iff, realUnits,
    RingHom.mem_range, RingHom.toMonoidHom_eq_coe, MonoidHom.mem_range]
  refine ⟨fun ⟨x, hx⟩ ↦
    ⟨(isUnit_iff_isUnit_algebraMap.mpr (hx ▸ u.isUnit)).unit, Units.ext_iff.mpr hx⟩, ?_⟩
  rintro ⟨x, rfl⟩
  exact ⟨x, rfl⟩

variable (L) in
def index_realUnits : ℕ := (realUnits K L ⊔ torsion L).index

def unitsMulComplexConjInv [IsCMExtension K L] : (𝓞 L)ˣ →* torsion L where
  toFun := fun u ↦ ⟨u * (unitsComplexConj K u)⁻¹, (mem_torsion L).mpr fun _ ↦ by simp⟩
  map_one' := by simp
  map_mul' := by
    intro x y
    simp only [map_mul, mul_inv_rev, MulMemClass.mk_mul_mk, Subtype.mk.injEq]
    rw [mul_comm ((unitsComplexConj K) y)⁻¹, mul_mul_mul_comm]

@[simp]
theorem unitsMulComplexConjInv_apply [IsCMExtension K L] (u : (𝓞 L)ˣ) :
    unitsMulComplexConjInv K u = u * (unitsComplexConj K u)⁻¹ := rfl

theorem unitsMulComplexConjInv_ker [IsCMExtension K L] :
    (unitsMulComplexConjInv K).ker = realUnits K L := by
  ext
  rw [MonoidHom.mem_ker, Subtype.ext_iff_val, unitsMulComplexConjInv_apply, OneMemClass.coe_one,
    mul_inv_eq_one, eq_comm, unitsComplexConj_eq_self_iff]

theorem index_unitsMulComplexConjInv_range [IsCMExtension K L] :
    (unitsMulComplexConjInv K (L := L)).range.index ∣ 2 := by
  let H := (⊤ : Subgroup (torsion L)).map (powMonoidHom 2)
  have : H.index = 2 := by
    unfold H
    rw [Subgroup.index_map]
    simp

    sorry
  rw [← this]
  apply Subgroup.index_dvd_of_le
  unfold H
  rintro _ ⟨ζ, _, rfl⟩
  refine ⟨ζ, ?_⟩
  rw [Subtype.ext_iff_val]
  simp [pow_two]











theorem index_realUnits_eq [IsCMExtension K L] :
    index_realUnits K L = 1 ∨ index_realUnits K L = 2 := by
  let φ : (𝓞 L)ˣ →* sorry







end IsCMExtension
