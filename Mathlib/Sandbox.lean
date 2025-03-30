import Mathlib.NumberTheory.NumberField.Units.Basic
import Mathlib.RingTheory.RootsOfUnity.Complex

set_option linter.style.header false

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

@[to_additive]
theorem Subgroup.index_range {G : Type*} [Group G] {f : G →* G} [hf : f.ker.FiniteIndex] :
    f.range.index = Nat.card f.ker := by
  suffices f.range.index * f.ker.index = Nat.card f.ker * f.ker.index by
    simpa [mul_eq_mul_right_iff, hf.finiteIndex, or_false] using this
  rw [card_mul_index f.ker, index_ker, mul_comm, card_mul_index]

@[to_additive]
theorem IsCyclic.card_powMonoidHom_range {G : Type*} [CommGroup G] [hG : IsCyclic G] [Fintype G]
    (d : ℕ) :
    Nat.card (powMonoidHom d : G →* G).range = Fintype.card G / (Fintype.card G).gcd d := by
  obtain ⟨g, h⟩ := exists_zpow_surjective G
  have : (powMonoidHom d).range = Subgroup.zpowers (g ^ d) := by
    rw [show g ^ d = powMonoidHom d g by rfl, ← MonoidHom.map_zpowers,
      (Subgroup.eq_top_iff' (Subgroup.zpowers g)).mpr h,  ← MonoidHom.range_eq_map]
  rw [this, Nat.card_zpowers, orderOf_pow, orderOf_eq_card_of_forall_mem_zpowers h,
    Nat.card_eq_fintype_card]

@[to_additive]
theorem IsCyclic.index_powMonoidHom_ker {G : Type*} [CommGroup G] [hG : IsCyclic G] [Fintype G]
    (d : ℕ) :
    (powMonoidHom d : G →* G).ker.index = Fintype.card G / (Fintype.card G).gcd d := by
  rw [Subgroup.index_ker, card_powMonoidHom_range]

@[to_additive]
theorem IsCyclic.card_powMonoidHom_ker {G : Type*} [CommGroup G] [hG : IsCyclic G] [Fintype G]
    (d : ℕ) :
    Nat.card (powMonoidHom d : G →* G).ker = (Fintype.card G).gcd d := by
  have h : ↑(Fintype.card G / (Fintype.card G).gcd d) ≠ (0 : ℚ) :=
    Nat.cast_ne_zero.mpr <| Nat.div_ne_zero_iff.mpr
      ⟨Nat.gcd_ne_zero_left Fintype.card_ne_zero, Nat.gcd_le_left d Fintype.card_pos⟩
  have := Subgroup.card_mul_index (powMonoidHom d : G →* G).ker
  rwa [index_powMonoidHom_ker, Nat.card_eq_fintype_card (α := G), ← Nat.cast_inj (R := ℚ),
    Nat.cast_mul, ← eq_div_iff h, ← Nat.cast_div (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left _ _)) h,
    Nat.div_div_self (Nat.gcd_dvd_left _ _) Fintype.card_ne_zero, Nat.cast_inj] at this

@[to_additive]
theorem IsCyclic.index_powMonoidHom_range {G : Type*} [CommGroup G] [hG : IsCyclic G] [Fintype G]
    (d : ℕ) :
    (powMonoidHom d : G →* G).range.index = (Fintype.card G).gcd d := by
  rw [Subgroup.index_range, card_powMonoidHom_ker]

end misc

noncomputable section

open NumberField InfinitePlace ComplexEmbedding NumberField.Units

class IsCM (F K : Type*) [Field F] [NumberField F] [Field K] [NumberField K]
    [Algebra F K] : Prop where
  isTotallyComplex : IsTotallyComplex K
  isTotallyReal : IsTotallyReal F
  quadratic : Module.finrank F K = 2

namespace IsCM

open scoped ComplexConjugate

variable (F K : Type*) [Field F] [NumberField F] [Field K] [NumberField K] [Algebra F K]

instance [IsCM F K] : IsGalois F K :=
{ to_isSeparable := Algebra.IsSeparable.of_integral _ _
  to_normal := normal_of_rank_eq_two _ _ quadratic }

variable {K}

variable [hcm : IsCM F K]

theorem exists_isConj (φ : K →+* ℂ) :
    ∃ σ : K ≃ₐ[F] K, IsConj φ σ :=
  exists_isConj_of_not_isUnramified <|
    not_isUnramified_iff.mpr ⟨hcm.isTotallyComplex.isComplex _, hcm.isTotallyReal.isReal _⟩

variable {F} in
theorem isConj_ne_one {φ : K →+* ℂ} {σ : K ≃ₐ[F] K} (hφ : IsConj φ σ) :
    σ ≠ 1 := by
  by_contra h
  rw [h, isConj_one_iff, ← isReal_mk_iff] at hφ
  exact not_isComplex_iff_isReal.mpr hφ  (hcm.isTotallyComplex.isComplex _)

variable {F} in
theorem isConj_eq_isConj {φ ψ : K →+* ℂ} {σ τ : K ≃ₐ[F] K}
    (hφ : IsConj φ σ) (hψ : IsConj ψ τ) : σ = τ := by
  have : Fintype.card (K ≃ₐ[F] K) = 2 := hcm.quadratic ▸ IsGalois.card_aut_eq_finrank F K
  rw [← Nat.card_eq_fintype_card, Nat.card_eq_two_iff' 1] at this
  exact ExistsUnique.unique this (isConj_ne_one hφ) (isConj_ne_one hψ)

def complexConj : K ≃ₐ[F] K :=
  (exists_isConj F (Classical.choice (inferInstance : Nonempty _))).choose

def ringOfIntegersComplexConj : (𝓞 K) ≃ₐ[𝓞 F] (𝓞 K) :=
  RingOfIntegers.mapAlgEquiv (complexConj F)

@[simp]
theorem coe_ringOfIntegersComplexConj (x : 𝓞 K) :
    (ringOfIntegersComplexConj F x : K) = complexConj F (x : K) := rfl

def unitsComplexConj : (𝓞 K)ˣ ≃* (𝓞 K)ˣ :=
  Units.mapEquiv (ringOfIntegersComplexConj F).toMulEquiv

@[simp]
theorem coe_unitsComplexConj (x : (𝓞 K)ˣ) :
    (unitsComplexConj F x : 𝓞 K) = ringOfIntegersComplexConj F (x : 𝓞 K) := rfl

theorem isConj_complexConj (φ : K →+* ℂ) :
    IsConj φ (complexConj F) := by
  obtain ⟨σ, hσ⟩ := exists_isConj F φ
  have := (exists_isConj F (Classical.choice (inferInstance : Nonempty (K →+* ℂ)))).choose_spec
  rwa [isConj_eq_isConj hσ this] at hσ

theorem complexConj_ne_one :
    complexConj F ≠ (1 : K ≃ₐ[F] K) :=
  isConj_ne_one (exists_isConj F (Classical.choice (inferInstance : Nonempty _))).choose_spec

@[simp]
theorem complexEmbedding_complexConj (φ : K →+* ℂ) (x : K) :
    φ (complexConj F x) = conj (φ x) := by
  rw [IsConj.eq (isConj_complexConj F φ), RCLike.star_def]

protected theorem Units.complexEmbedding_complexConj (φ : K →+* ℂ) (u : (𝓞 K)ˣ) :
    Units.complexEmbedding φ (unitsComplexConj F u) =
      (Units.map (starRingEnd ℂ)) (Units.complexEmbedding φ u) := by
  simp [Units.ext_iff]

@[simp]
theorem unitsComplexConj_torsion (ζ : torsion K) :
    unitsComplexConj F (ζ : (𝓞 K)ˣ) = ζ⁻¹ := by
  let φ : K →+* ℂ := Classical.choice (inferInstance : Nonempty _)
  rw [← (Units.complexEmbedding_injective φ).eq_iff, Units.complexEmbedding_complexConj,
    Units.ext_iff, Units.coe_map, MonoidHom.coe_coe, Subgroup.coe_inv, MonoidHom.map_inv,
    Complex.conj_rootsOfUnity (n := torsionOrder K)]
  rw [← map_complexEmbedding_torsion]
  exact Subgroup.apply_coe_mem_map _ (torsion K) ζ

@[simp]
theorem infinitePlace_complexConj (w : InfinitePlace K) (x : K) :
    w (complexConj F x) = w x := by
  rw [← norm_embedding_eq, complexEmbedding_complexConj, Complex.norm_conj, norm_embedding_eq]

@[simp]
theorem complexConj_apply_apply (x : K) :
    complexConj F (complexConj F x) = x := by
  let φ : K →+* ℂ := Classical.choice (inferInstance : Nonempty _)
  rw [← φ.injective.eq_iff, complexEmbedding_complexConj, complexEmbedding_complexConj,
    Complex.conj_conj]

theorem galoisGroup_eq : -- Refactor this lemma
    (⊤ : Subgroup (K ≃ₐ[F] K)).carrier = {1, complexConj F} := by
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
    exact (complexConj_ne_one F).symm

theorem complexConj_eq_self_iff (x : K) :
    complexConj F x = x ↔ x ∈ (algebraMap F K).range := by
  convert (IntermediateField.mem_fixedField_iff (⊤ : Subgroup (K ≃ₐ[F] K)) x).symm using 1
  · simp only [← Subgroup.mem_carrier, galoisGroup_eq, Set.mem_insert_iff, Set.mem_singleton_iff,
      forall_eq_or_imp, AlgEquiv.one_apply, forall_eq, true_and]
  · rw [IntermediateField.fixedField_top, IntermediateField.mem_bot, RingHom.mem_range,
      Set.mem_range]

theorem ringOfIntegersComplexConj_eq_self_iff (x : 𝓞 K) :
    ringOfIntegersComplexConj F x = x ↔ x ∈ (algebraMap (𝓞 F) (𝓞 K)).range := by
  rw [← RingOfIntegers.eq_iff, coe_ringOfIntegersComplexConj, complexConj_eq_self_iff,
    RingOfIntegers.coe_eq_algebraMap, RingHom.mem_range, RingHom.mem_range]
  refine ⟨fun ⟨a, ha⟩ ↦ ⟨⟨a, ?_⟩, RingOfIntegers.eq_iff.mp ha⟩, ?_⟩
  · exact (isIntegral_algebraMap_iff
        (FaithfulSMul.algebraMap_injective F K)).mp (ha ▸ RingOfIntegers.isIntegral_coe x)
  · rintro ⟨a, rfl⟩
    exact ⟨a, rfl⟩

variable (K) in
def realUnits : Subgroup (𝓞 K)ˣ := (Units.map (algebraMap (𝓞 F) (𝓞 K)).toMonoidHom).range

theorem unitsComplexConj_eq_self_iff (u : (𝓞 K)ˣ) :
    unitsComplexConj F u = u ↔ u ∈ realUnits F K := by
  rw [← Units.eq_iff, coe_unitsComplexConj, ringOfIntegersComplexConj_eq_self_iff, realUnits,
    RingHom.mem_range, RingHom.toMonoidHom_eq_coe, MonoidHom.mem_range]
  refine ⟨fun ⟨x, hx⟩ ↦
    ⟨(isUnit_iff_isUnit_algebraMap.mpr (hx ▸ u.isUnit)).unit, Units.ext_iff.mpr hx⟩, ?_⟩
  rintro ⟨x, rfl⟩
  exact ⟨x, rfl⟩

variable (K) in
abbrev index_realUnits : ℕ := (torsion K ⊔ realUnits F K).index

def unitsMulComplexConjInv : (𝓞 K)ˣ →* torsion K where
  toFun := fun u ↦ ⟨u * (unitsComplexConj F u)⁻¹, (mem_torsion K).mpr fun _ ↦ by simp⟩
  map_one' := by simp
  map_mul' x y := by
    simp only [map_mul, mul_inv_rev, MulMemClass.mk_mul_mk, Subtype.mk.injEq]
    rw [mul_comm ((unitsComplexConj F) y)⁻¹, mul_mul_mul_comm]

@[simp]
theorem unitsMulComplexConjInv_apply (u : (𝓞 K)ˣ) :
    unitsMulComplexConjInv F u = u * (unitsComplexConj F u)⁻¹ := rfl

theorem unitsMulComplexConjInv_apply_torsion (ζ : torsion K) :
    unitsMulComplexConjInv F ζ = ζ ^ 2 := by
  refine Subtype.eq ?_
  simp [pow_two]

variable (K) in
theorem unitsMulComplexConjInv_ker :
    (unitsMulComplexConjInv F).ker = realUnits F K := by
  ext
  rw [MonoidHom.mem_ker, Subtype.ext_iff_val, unitsMulComplexConjInv_apply, OneMemClass.coe_one,
    mul_inv_eq_one, eq_comm, unitsComplexConj_eq_self_iff]

variable (K) in
theorem index_unitsMulComplexConjInv_range :
    (unitsMulComplexConjInv F (K := K)).range.index ∣ 2 := by
  have : (powMonoidHom 2 : _ →* torsion K).range.index = 2 := by
    rw [IsCyclic.index_powMonoidHom_range, ← Nat.gcd_eq_right_iff_dvd]
    exact Even.two_dvd <| even_torsionOrder K
  rw [← this]
  refine Subgroup.index_dvd_of_le ?_
  rintro _ ⟨ζ, _, rfl⟩
  refine ⟨ζ, ?_⟩
  rw [Subtype.ext_iff_val]
  simp [pow_two]

variable (K) in
theorem map_unitsMulComplexConjInv_torsion :
    Subgroup.map (unitsMulComplexConjInv F) (torsion K) = (powMonoidHom 2).range := by
  ext
  constructor
  · rintro ⟨u, hu, rfl⟩
    refine ⟨⟨u, hu⟩, ?_⟩
    rw [powMonoidHom_apply, ← unitsMulComplexConjInv_apply_torsion F]
  · rintro ⟨η, rfl⟩
    refine ⟨η, η.prop, ?_⟩
    rw [unitsMulComplexConjInv_apply_torsion, powMonoidHom_apply]

variable (K) in
theorem index_realUnits_mul_eq :
    index_realUnits F K * (unitsMulComplexConjInv F : (𝓞 K)ˣ →* torsion K).range.index = 2 := by
  convert (Subgroup.index_map (torsion K) (unitsMulComplexConjInv F : (𝓞 K)ˣ →* torsion K)).symm
  · rw [unitsMulComplexConjInv_ker]
  · rw [map_unitsMulComplexConjInv_torsion, IsCyclic.index_powMonoidHom_range, Nat.gcd_eq_right]
    exact even_iff_two_dvd.mp (even_torsionOrder K)

variable (K) in
theorem index_realUnits_eq :
    index_realUnits F K = 1 ∨ index_realUnits F K = 2 := by
  have h₁ := index_realUnits_mul_eq F K
  obtain h₂ | h₂ := (Nat.dvd_prime Nat.prime_two).mp <| index_unitsMulComplexConjInv_range F K
  · exact Or.inr <| by rwa [h₂, mul_one] at h₁
  · exact Or.inl <| by rwa [h₂, Nat.mul_left_eq_self_iff zero_lt_two] at h₁

variable (K) in
theorem index_realUnits_eq_two_iff :
    index_realUnits F K = 2 ↔
      ∃ u : (𝓞 K)ˣ, Subgroup.zpowers (unitsMulComplexConjInv F u) = ⊤ := by
  have : (∃ u : (𝓞 K)ˣ, Subgroup.zpowers (unitsMulComplexConjInv F u) = ⊤) ↔
      (unitsMulComplexConjInv F : _ →* torsion K).range.index = 1 := by
    constructor
    · intro ⟨u, hu⟩
      refine Subgroup.index_eq_one.mpr ?_
      rw [← MonoidHom.map_zpowers] at hu
      have := Subgroup.map_le_range (unitsMulComplexConjInv F) (Subgroup.zpowers u)
      rw [hu] at this
      exact top_le_iff.mp this
    · intro h
      rw [Subgroup.index_eq_one, MonoidHom.range_eq_top] at h
      obtain ⟨ζ, hζ⟩ := exists_zpow_surjective (torsion K)
      obtain ⟨u, rfl⟩ := h ζ
      refine ⟨u, ?_⟩
      rw [← MonoidHom.map_zpowers]
      refine (Subgroup.eq_top_iff' _).mpr fun η ↦ ?_
      simp_rw [Subgroup.mem_map, Subgroup.exists_mem_zpowers, map_zpow]
      exact hζ η
  rw [this]
  have := index_realUnits_mul_eq F K
  constructor
  · intro h
    rwa [h, Nat.mul_right_eq_self_iff zero_lt_two] at this
  · intro h
    rwa [h, mul_one] at this


end IsCM
