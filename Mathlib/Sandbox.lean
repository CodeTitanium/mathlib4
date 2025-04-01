import Mathlib.NumberTheory.NumberField.Units.Regulator
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

@[to_additive]
theorem MulAction.mem_fixedBy_pow {M : Type*} [Monoid M] {α : Type*} [MulAction M α] {m : M}
    {a : α} (h : a ∈ fixedBy α m) (n : ℕ) :
    a ∈ fixedBy α (m ^ n) := by
  induction n with
  | zero => simp
  | succ n hi => rw [pow_succ, mem_fixedBy, mul_smul, h, hi]

@[to_additive]
theorem MulAction.mem_fixedBy_zpow {G : Type*} [Group G] {α : Type*} [MulAction G α] {g : G}
    {a : α} (h : a ∈ fixedBy α g) (n : ℤ) :
    a ∈ fixedBy α (g ^ n) := by
  induction n with
  | hz => simp
  | hp i hi => rw [zpow_add, zpow_one, mem_fixedBy, mul_smul, h, hi]
  | hn i hi =>
      rw [← fixedBy_inv] at h
      rw [zpow_sub, zpow_one, mem_fixedBy, mul_smul, h, hi]

@[to_additive]
theorem MulAction.mem_fixedBy_powers_iff_mem_fixedBy {M : Type*} [Monoid M] {α : Type*}
    [MulAction M α] {m : M} {a : α} :
    (∀ n, a ∈ fixedBy α (m ^ n)) ↔ a ∈ fixedBy α m :=
  ⟨fun h ↦ by simpa using h 1, fun h n ↦ mem_fixedBy_pow h n⟩

@[to_additive]
theorem MulAction.mem_fixedBy_zpowers_iff_mem_fixedBy {G : Type*} [Group G] {α : Type*}
    [MulAction G α] {g : G} {a : α} :
    (∀ n : ℤ, a ∈ fixedBy α (g ^ n)) ↔ a ∈ fixedBy α g :=
  ⟨fun h ↦ by simpa using h 1, fun h n ↦ mem_fixedBy_zpow h n⟩

theorem CommMonoid.map_torsion_le {M M' : Type*} [CommMonoid M] [CommMonoid M'] (f : M →* M') :
    Submonoid.map f (CommMonoid.torsion M) ≤ CommMonoid.torsion M' := by
  rintro _ ⟨x, hx, rfl⟩
  exact MonoidHom.isOfFinOrder _ hx

open NumberField

example {k : Type*} [Field k] {K : Type*} [Field K] [Algebra k K] [Algebra.IsAlgebraic k K]
    (w : InfinitePlace K) (x : k) :
    w (algebraMap k K x) = w.comap (algebraMap k K) x := rfl

end misc

noncomputable section

open NumberField InfinitePlace ComplexEmbedding NumberField.Units

-- use extends
class IsCM (F K : Type*) [Field F] [NumberField F] [Field K] [NumberField K]
    [Algebra F K] : Prop
  extends IsTotallyReal F, IsTotallyComplex K where
  finrank_eq_two' : Module.finrank F K = 2

namespace IsCM

open scoped ComplexConjugate

variable (F K : Type*) [Field F] [NumberField F] [Field K] [NumberField K] [Algebra F K]

theorem isTotallyComplex [IsCM F K] :
    IsTotallyComplex K := toIsTotallyComplex F

theorem isTotallyReal [IsCM F K] :
    IsTotallyReal F := toIsTotallyReal K

theorem finrank_eq_two [IsCM F K] :
    Module.finrank F K = 2 := finrank_eq_two'

variable [IsCM F K]

instance  : IsGalois F K :=
{ to_isSeparable := Algebra.IsSeparable.of_integral _ _
  to_normal := normal_of_rank_eq_two _ _ (finrank_eq_two  F K) }

variable {K}

theorem exists_isConj (φ : K →+* ℂ) :
    ∃ σ : K ≃ₐ[F] K, IsConj φ σ :=
  exists_isConj_of_not_isUnramified <|
    not_isUnramified_iff.mpr ⟨(isTotallyComplex F K).isComplex _, (isTotallyReal F K).isReal _⟩

variable {F} in
theorem isConj_ne_one {φ : K →+* ℂ} {σ : K ≃ₐ[F] K} (hφ : IsConj φ σ) :
    σ ≠ 1 := by
  by_contra h
  rw [h, isConj_one_iff, ← isReal_mk_iff] at hφ
  exact not_isComplex_iff_isReal.mpr hφ  ((isTotallyComplex F K).isComplex _)

variable {F} in
theorem isConj_eq_isConj {φ ψ : K →+* ℂ} {σ τ : K ≃ₐ[F] K}
    (hφ : IsConj φ σ) (hψ : IsConj ψ τ) : σ = τ := by
  have : Fintype.card (K ≃ₐ[F] K) = 2 := (finrank_eq_two F K) ▸ IsGalois.card_aut_eq_finrank F K
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

variable (K) in
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
  exact isConj_apply_apply (isConj_complexConj F φ) x

variable (K) in
theorem orderOf_complexConj :
    orderOf (complexConj F : K ≃ₐ[F] K) = 2 :=
  orderOf_eq_prime_iff.mpr ⟨by ext; simp, complexConj_ne_one F K⟩

variable (K) in
theorem zpowers_complexConj_eq_top :
    Subgroup.zpowers (complexConj F : K ≃ₐ[F] K) = ⊤ := by
  refine Subgroup.eq_top_of_card_eq _ ?_
  rw [Nat.card_zpowers, orderOf_complexConj, Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank,
    finrank_eq_two]

theorem complexConj_eq_self_iff (x : K) :
    complexConj F x = x ↔ x ∈ (algebraMap F K).range := by
  convert (IntermediateField.mem_fixedField_iff (⊤ : Subgroup (K ≃ₐ[F] K)) x).symm using 1
  · rw [← zpowers_complexConj_eq_top, Subgroup.forall_mem_zpowers]
    exact (MulAction.mem_fixedBy_zpowers_iff_mem_fixedBy
      (g := (complexConj F : K ≃ₐ[F] K)) (a := x)).symm
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
abbrev indexRealUnits : ℕ := (realUnits F K ⊔ torsion K).index

def unitsMulComplexConjInv : (𝓞 K)ˣ →* torsion K where
  toFun := fun u ↦ ⟨u * (unitsComplexConj F u)⁻¹, (mem_torsion K).mpr fun _ ↦ by simp⟩
  map_one' := by simp
  map_mul' x y := by
    simp only [map_mul, mul_inv_rev, MulMemClass.mk_mul_mk, Subtype.mk.injEq]
    rw [mul_comm ((unitsComplexConj F) y)⁻¹, mul_mul_mul_comm]

@[simp]
theorem unitsMulComplexConjInv_apply (u : (𝓞 K)ˣ) :
    unitsMulComplexConjInv F u = u * (unitsComplexConj F u)⁻¹ := rfl

@[simp]
theorem unitsMulComplexConjInv_apply_torsion (ζ : torsion K) :
    unitsMulComplexConjInv F ζ = ζ ^ 2 :=
  Subtype.eq <| by simp [pow_two]

variable (K)

theorem unitsMulComplexConjInv_ker :
    (unitsMulComplexConjInv F).ker = realUnits F K := by
  ext
  rw [MonoidHom.mem_ker, Subtype.ext_iff_val, unitsMulComplexConjInv_apply, OneMemClass.coe_one,
    mul_inv_eq_one, eq_comm, unitsComplexConj_eq_self_iff]

theorem index_unitsMulComplexConjInv_range_dvd :
    (unitsMulComplexConjInv F (K := K)).range.index ∣ 2 := by
  suffices (powMonoidHom 2 : _ →* torsion K).range.index = 2 by
    refine this ▸ Subgroup.index_dvd_of_le ?_
    rintro _ ⟨ζ, _, rfl⟩
    exact ⟨ζ, Subtype.ext_iff_val.mpr (by simp [pow_two])⟩
  rw [IsCyclic.index_powMonoidHom_range, ← Nat.gcd_eq_right_iff_dvd]
  exact Even.two_dvd <| even_torsionOrder K

theorem map_unitsMulComplexConjInv_torsion :
    Subgroup.map (unitsMulComplexConjInv F) (torsion K) = (powMonoidHom 2).range := by
  rw [← MonoidHom.restrict_range]
  exact congr_arg (MonoidHom.range ·) (MonoidHom.ext fun _ ↦ by simp [pow_two])

theorem indexRealUnits_mul_eq :
    indexRealUnits F K * (unitsMulComplexConjInv F : (𝓞 K)ˣ →* torsion K).range.index = 2 := by
  rw [indexRealUnits, sup_comm]
  convert (Subgroup.index_map (torsion K) (unitsMulComplexConjInv F : (𝓞 K)ˣ →* torsion K)).symm
  · rw [unitsMulComplexConjInv_ker]
  · rw [map_unitsMulComplexConjInv_torsion, IsCyclic.index_powMonoidHom_range, Nat.gcd_eq_right]
    exact even_iff_two_dvd.mp (even_torsionOrder K)

theorem indexRealUnits_eq_one_or_two :
    indexRealUnits F K = 1 ∨ indexRealUnits F K = 2 := by
  have h₁ := indexRealUnits_mul_eq F K
  obtain h₂ | h₂ := (Nat.dvd_prime Nat.prime_two).mp <| index_unitsMulComplexConjInv_range_dvd F K
  · exact Or.inr <| by rwa [h₂, mul_one] at h₁
  · exact Or.inl <| by rwa [h₂, Nat.mul_left_eq_self_iff zero_lt_two] at h₁

theorem indexRealUnits_eq_two_iff :
    indexRealUnits F K = 2 ↔
      ∃ u : (𝓞 K)ˣ, Subgroup.zpowers (unitsMulComplexConjInv F u) = ⊤ := by
  suffices (∃ u : (𝓞 K)ˣ, Subgroup.zpowers (unitsMulComplexConjInv F u) = ⊤) ↔
      (unitsMulComplexConjInv F : _ →* torsion K).range.index = 1 by
    rw [this]
    have h_eq := indexRealUnits_mul_eq F K
    refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
    · rwa [h, Nat.mul_right_eq_self_iff zero_lt_two] at h_eq
    · rwa [h, mul_one] at h_eq
  refine ⟨fun ⟨u, hu⟩ ↦ Subgroup.index_eq_one.mpr (top_le_iff.mp ?_), fun h ↦ ?_⟩
  · refine le_of_eq_of_le ?_ ((Subgroup.zpowers u).map_le_range (unitsMulComplexConjInv F))
    rw [MonoidHom.map_zpowers, ← hu]
  · obtain ⟨ζ, hζ⟩ := exists_zpow_surjective (torsion K)
    rw [Subgroup.index_eq_one, MonoidHom.range_eq_top] at h
    obtain ⟨u, rfl⟩ := h ζ
    exact ⟨u, (Subgroup.eq_top_iff' _).mpr hζ⟩

theorem card_infinitePlace_eq_card_infinitePlace :
    Fintype.card (InfinitePlace K) = Fintype.card (InfinitePlace F) := by
  rw [card_eq_nrRealPlaces_add_nrComplexPlaces, card_eq_nrRealPlaces_add_nrComplexPlaces,
    nrRealPlaces_eq_zero_iff.mpr (isTotallyComplex F K), zero_add,
    nrComplexPlaces_eq_zero_iff.mpr (isTotallyReal F K), add_zero, ← IsTotallyReal.finrank,
    ← Nat.mul_left_cancel_iff zero_lt_two, ← IsTotallyComplex.finrank,
    ← Module.finrank_mul_finrank ℚ F K, finrank_eq_two F K, mul_comm]

theorem units_rank_eq_units_rank :
    rank K = rank F := by
  rw [rank, rank, card_infinitePlace_eq_card_infinitePlace F K]

def equivInfinitePlace :
    InfinitePlace K ≃ InfinitePlace F :=
  Equiv.ofBijective (fun w ↦ w.comap (algebraMap F K))
    <| (Fintype.bijective_iff_surjective_and_card _).mpr
      ⟨comap_surjective, card_infinitePlace_eq_card_infinitePlace F K⟩

@[simp]
theorem equivInfinitePlace_apply (w : InfinitePlace K) :
    equivInfinitePlace F K w = w.comap (algebraMap F K) := rfl

@[simp]
theorem equivInfinitePlace_symm_apply (w : InfinitePlace F) (x : F) :
    (equivInfinitePlace F K).symm w (algebraMap F K x) = w x := by
  have : (equivInfinitePlace F K).symm w (algebraMap F K x) =
    ((equivInfinitePlace F K).symm w).comap (algebraMap F K) x := rfl
  rw [this, ← equivInfinitePlace_apply, Equiv.apply_symm_apply]

def realFundSystem : Fin (rank K) → (𝓞 K)ˣ :=
  fun i ↦ (Units.map (algebraMap (𝓞 F) (𝓞 K)).toMonoidHom)
    (fundSystem F (finCongr (units_rank_eq_units_rank F K) i))

theorem closure_realFundSystem_sup_torsion :
    Subgroup.closure (Set.range (realFundSystem F K)) ⊔ torsion K = realUnits F K ⊔ torsion K := by
  rw [realUnits, MonoidHom.range_eq_map, ← closure_fundSystem_sup_torsion_eq_top]
  rw [Subgroup.map_sup, sup_assoc]
  have : Subgroup.map (Units.map ↑(algebraMap (𝓞 F) (𝓞 K))) (torsion F) ≤ torsion K := by
    exact CommMonoid.map_torsion_le _
  rw [RingHom.toMonoidHom_eq_coe]
  rw [sup_eq_right.mpr this]
  rw [MonoidHom.map_closure]
  congr
  ext
  simp [realFundSystem, Equiv.exists_congr_left (finCongr (units_rank_eq_units_rank F K))]

open dirichletUnitTheorem

example : regulator K / regulator F = 2 ^ rank K * (indexRealUnits F K : ℝ)⁻¹ := by
  classical
  let e : Fin (rank K) ≃ Fin (rank F) := finCongr (units_rank_eq_units_rank F K)
  let w₁ := (equivInfinitePlace F K).symm w₀
  let f : {w : InfinitePlace K  // w ≠ w₁} ≃ {w : InfinitePlace F // w ≠ w₀} :=
    (equivInfinitePlace F K).subtypeEquiv fun w ↦ by rw [not_iff_not, Equiv.eq_symm_apply]
  have f_apply (w : {w // w ≠ w₀}) : f.symm w = (equivInfinitePlace F K).symm w.1 := rfl
  let g := (e.trans (equivFinRank F)).trans f.symm
  have : regOfFamily (realFundSystem F K) = 2 ^ rank K * regulator F := by
    rw [regulator_eq_regOfFamily_fundSystem, regOfFamily_eq_det _ w₁ g.symm, regOfFamily_eq_det']
    rw [show (2 : ℝ) ^ rank K = |∏ w : {w : InfinitePlace F // w ≠ w₀}, 2| by
      rw [Finset.prod_const, abs_pow, abs_of_pos zero_lt_two, units_rank_eq_units_rank F K, rank]
      simp]
    rw [← abs_mul]
    rw [← Matrix.det_mul_column]
    rw [← Matrix.det_reindex_self f]
    congr
    ext i w
    simp_rw [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.of_apply, logEmbedding_component,
      f_apply]
    rw [show algebraMap (𝓞 K) K _ = algebraMap F K _ by rfl]
    rw [finCongr_apply, equivInfinitePlace_symm_apply]
    simp [f, g, e]
  have t0 := regOfFamily_div_regulator (realFundSystem F K)
  rw [indexRealUnits]
  have t1 : Subgroup.closure (Set.range (realFundSystem F K)) ⊔ torsion K =
    realUnits F K ⊔ torsion K := closure_realFundSystem_sup_torsion F K
  rw [← t1]
  rw [← t0]
  rw [this]
  rw [inv_div]
  rw [← mul_div_assoc, mul_div_mul_comm, div_self, one_mul]
  exact Ne.symm (NeZero.ne' (2 ^ rank K))

end IsCM
