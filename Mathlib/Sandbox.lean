import Mathlib.NumberTheory.NumberField.Units.Regulator
import Mathlib.RingTheory.RootsOfUnity.Complex

set_option linter.style.header false

section IsQuadraticExtension

theorem AlgHom.card_le (F K : Type*) [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] :
    Fintype.card (K →ₐ[F] K) ≤ Module.finrank F K :=
  Module.finrank_linearMap_self F K K ▸ finrank_algHom F K

#find_home AlgHom.card_le

theorem AlgEquiv.card_le (F K : Type*) [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] :
    Fintype.card (K ≃ₐ[F] K) ≤ Module.finrank F K :=
  Fintype.ofEquiv_card (algEquivEquivAlgHom F K).toEquiv.symm ▸ AlgHom.card_le F K

class IsQuadraticExtension (F K : Type*) [CommSemiring F] [Semiring K]
  extends Algebra F K where
  finrank_eq_two : Module.finrank F K = 2

#find_home! IsQuadraticExtension
instance (F K : Type*) [Field F] [CommRing K] [h : IsQuadraticExtension F K] :
    FiniteDimensional F K :=
  Module.finite_of_finrank_eq_succ h.finrank_eq_two

instance (F K : Type*) [Field F] [Field K] [h : IsQuadraticExtension F K] : Normal F K :=
  normal_of_finrank_eq_two F K h.finrank_eq_two

instance (F K : Type*) [Field F] [Field K] [h : IsQuadraticExtension F K] :
    IsCyclic (K ≃ₐ[F] K) := by
  have := h.finrank_eq_two ▸ AlgEquiv.card_le F K
  interval_cases h : Fintype.card (K ≃ₐ[F] K)
  · simp_all
  · exact @isCyclic_of_subsingleton _ _ (Fintype.card_le_one_iff_subsingleton.mp h.le)
  · rw [← Nat.card_eq_fintype_card] at h
    exact isCyclic_of_prime_card h

end IsQuadraticExtension

section maximalRealSubfield

open NumberField

variable (K : Type*) [Field K] [NumberField K]

def maximalRealSubfield : Subfield K where
  carrier := {x | ∀ φ : K →+* ℂ, star (φ x) = φ x}
  mul_mem' := by
    intro _ _ hx hy _
    rw [map_mul, star_mul, hx, hy, mul_comm]
  one_mem' := by simp
  add_mem' := by
    intro x y hx hy φ
    rw [map_add, star_add, hx, hy]
  zero_mem' := by simp
  neg_mem' := by simp
  inv_mem' := by simp

example : IsTotallyReal (maximalRealSubfield K) := by
  refine { isReal := ?_ }
  intro w
  rw [InfinitePlace.isReal_iff, ComplexEmbedding.isReal_iff]
  ext ⟨x, hx⟩
  rw [RingHom.star_apply]
  letI := w.embedding.toAlgebra
  let φ : K →+* ℂ := (IsAlgClosed.lift (M := ℂ) (R := (maximalRealSubfield K))).toRingHom
  have hφ : w.embedding ⟨x, hx⟩ = φ x :=
    (RingHom.congr_fun (AlgHom.comp_algebraMap_of_tower (maximalRealSubfield K)
      IsAlgClosed.lift) ⟨x, hx⟩).symm
  rw [hφ, hx]

example (E : Subfield K) [h : IsTotallyReal E] :
    E ≤ maximalRealSubfield K := by
  intro x hx
  intro φ
  let ψ := φ.comp E.subtype
  have : φ x = ψ ⟨x, hx⟩ := by exact rfl
  rw [this]
  rw [isTotallyReal_iff] at h
  have := h (InfinitePlace.mk ψ)
  rw [InfinitePlace.isReal_mk_iff] at this
  rw [ComplexEmbedding.isReal_iff] at this
  exact RingHom.congr_fun this _

end maximalRealSubfield

section IntermediateField

variable (K : Type*) [Field K] [CharZero K]

def SubfieldEquivRatIntermediateField : Subfield K ≃o IntermediateField ℚ K where
  toFun F := F.toIntermediateField fun _ ↦ SubfieldClass.ratCast_mem F _
  invFun E := E.toSubfield
  left_inv _ := by ext; simp [Subfield.toIntermediateField ]
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

theorem mem_SubfieldEquivRatIntermediateField_iff (S : Subfield K) (x : K) :
    x ∈ S ↔ x ∈ SubfieldEquivRatIntermediateField K S := Iff.rfl

@[simps!]
def RingEquiv.subfieldEquivRatIntermediateField (S : Subfield K) :
    S ≃+* SubfieldEquivRatIntermediateField K S := .refl S

end IntermediateField

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

open NumberField ComplexEmbedding

variable {k : Type*} [Field k] {K : Type*} [Field K] [Algebra k K]

theorem ComplexEmbedding.IsConj_iff (φ : K →+* ℂ) (σ : K ≃ₐ[k] K) :
    IsConj φ σ ↔ ∀ x, φ (σ x) = star (φ x) := by
  simp [ComplexEmbedding.IsConj, conjugate, eq_comm, RingHom.ext_iff]

theorem ComplexEmbedding.IsConj_comp_of_isConj {φ : K →+* ℂ} {σ : K ≃ₐ[k] K} (hφ : IsConj φ σ)
    (f : K ≃ₐ[k] K) :
    IsConj (φ.comp f.symm) (f * σ * f.symm) := by
  rw [ComplexEmbedding.IsConj_iff] at hφ ⊢
  simp [AlgEquiv.mul_apply, RCLike.star_def]
  intro _
  simp [hφ]

theorem IntermediateField.mem_fixingSubgroup_iff {F : Type*} [Field F] {E : Type*} [Field E]
    [Algebra F E] (K : IntermediateField F E) (σ : E ≃ₐ[F] E) :
    σ ∈ K.fixingSubgroup ↔ ∀ x ∈ K, σ x = x := by
  simp [fixingSubgroup, _root_.mem_fixingSubgroup_iff, SetLike.mem_coe, AlgEquiv.smul_def]

variable [IsGalois k K]

theorem ComplexEmbedding.exists_mul_mul_symm_eq_of_isConj_isConj {φ ψ : K →+* ℂ}
    (h : φ.comp (algebraMap k K) = ψ.comp (algebraMap k K))
    {σ τ : K ≃ₐ[k] K} (hφ : IsConj φ σ) (hψ : IsConj ψ τ) :
    ∃ f, f * σ * f.symm = τ := by
  have := exists_comp_symm_eq_of_comp_eq φ ψ (k := k) h
  obtain ⟨f, hf⟩ := this
  refine ⟨f, ?_⟩
  rw [← hf] at hψ
  have := ComplexEmbedding.IsConj_comp_of_isConj hφ f
  exact (IsConj.ext hψ this).symm

-- theorem IntermediateField.finrank_eq_one_iff' {F : Type*} [Field F] {E : Type*} [Field E]
--     [Algebra F E] {K : IntermediateField F E} :
--     Module.finrank K E = 1 ↔ K = ⊤ := by



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

instance [IsCM F K] : IsGalois F K :=
{ to_isSeparable := Algebra.IsSeparable.of_integral _ _
  to_normal := normal_of_rank_eq_two _ _ (finrank_eq_two  F K) }

variable {K}

theorem exists_isConj [IsTotallyReal F] [IsTotallyComplex K] [IsGalois F K] (φ : K →+* ℂ) :
    ∃ σ : K ≃ₐ[F] K, IsConj φ σ :=
  exists_isConj_of_not_isUnramified <|
    not_isUnramified_iff.mpr ⟨IsTotallyComplex.isComplex _, IsTotallyReal.isReal _⟩

omit [NumberField F] in
variable {F} in
theorem isConj_ne_one [IsTotallyComplex K] {φ : K →+* ℂ} {σ : K ≃ₐ[F] K} (hφ : IsConj φ σ) :
    σ ≠ 1 := by
  by_contra h
  rw [h, isConj_one_iff, ← isReal_mk_iff] at hφ
  exact not_isComplex_iff_isReal.mpr hφ (IsTotallyComplex.isComplex _)

variable [IsCM F K]

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
  refine ⟨fun ⟨x, hx⟩ ↦ ?_, ?_⟩
  have := hx ▸ u.isUnit
  rw [isUnit_map_iff] at this
  sorry
  sorry

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
  have : regOfFamily (realFundSystem F K) = 2 ^ rank K * regulator F := by
    let W₀ := (equivInfinitePlace F K).symm w₀
    let f : {w : InfinitePlace K  // w ≠ W₀} ≃ {w : InfinitePlace F // w ≠ w₀} :=
      (equivInfinitePlace F K).subtypeEquiv fun w ↦ by rw [not_iff_not, Equiv.eq_symm_apply]
    let g := ((finCongr (units_rank_eq_units_rank F K)).trans (equivFinRank F)).trans f.symm
    rw [show (2 : ℝ) ^ rank K = |∏ w : {w : InfinitePlace F // w ≠ w₀}, 2| by
      rw [Finset.prod_const, abs_pow, abs_of_pos zero_lt_two, units_rank_eq_units_rank F K, rank]
      simp]
    rw [regulator_eq_regOfFamily_fundSystem, regOfFamily_eq_det _ W₀ g.symm, regOfFamily_eq_det',
      ← abs_mul, ← Matrix.det_mul_column, ← Matrix.det_reindex_self f, Matrix.reindex_apply]
    congr; ext i w
    rw [Matrix.submatrix_apply, Matrix.of_apply, Matrix.of_apply,
      show f.symm w = (equivInfinitePlace F K).symm w.1 by rfl,
      show algebraMap (𝓞 K) K _ = algebraMap F K _ by rfl, equivInfinitePlace_symm_apply]
    simp [f, g]
  rw [indexRealUnits, ← closure_realFundSystem_sup_torsion, ←
    regOfFamily_div_regulator (realFundSystem F K), this, inv_div, ← mul_div_assoc,
    mul_div_mul_comm, div_self (by positivity), one_mul]

section Abelian

variable (F K : Type*) [Field F] [Field K] [Algebra F K]

-- variable (K : Type*) [Field K] [NumberField K] -- [IsGalois ℚ K]

theorem toto {σ : K ≃ₐ[F] K} {φ : K →+* ℂ} (hσ : IsConj φ σ) (E : IntermediateField F K) :
    IsReal (φ.comp (algebraMap E K)) ↔ σ ∈ IntermediateField.fixingSubgroup E := by
  rw [ComplexEmbedding.isReal_iff, IntermediateField.mem_fixingSubgroup_iff]
  rw [RingHom.ext_iff]
  rw [IsConj_iff] at hσ
  simp_rw [conjugate_coe_eq, RingHom.coe_comp, Function.comp_apply]
  simp_rw [starRingEnd_apply, ← hσ]
  have : Function.Injective φ := by exact RingHom.injective φ
  simp_rw [this.eq_iff]
  simp

def maximalRealSubfield : IntermediateField F K :=
  .fixedField (Subgroup.closure {σ : K ≃ₐ[F] K | ∃ φ : K →+* ℂ, IsConj φ σ})

theorem maximalRealSubfield_ne_top {φ : K →+* ℂ} {σ : K ≃ₐ[F] K}
    (hφ : ¬ ComplexEmbedding.IsReal φ) (hσ : IsConj φ σ):
    maximalRealSubfield F K ≠ ⊤ := by
  by_contra h
  simp_rw [IntermediateField.ext_iff, IntermediateField.mem_top, iff_true, maximalRealSubfield,
    IntermediateField.mem_fixedField_iff] at h
  have : σ ∈ Subgroup.closure {σ : K ≃ₐ[F] K | ∃ φ : K →+* ℂ, IsConj φ σ} := by
    apply Subgroup.subset_closure
    refine ⟨φ, hσ⟩
  have := fun x ↦ h x σ this
  have : σ = 1 := by
    exact AlgEquiv.ext this
  rw [this, isConj_one_iff] at hσ
  exact hφ hσ

instance isTotallyReal_maximalRealSubfield [NumberField F] [NumberField K] [IsTotallyReal F]
    [IsGalois F K] :
    IsTotallyReal (maximalRealSubfield F K) := by
  refine ⟨fun w ↦ ?_⟩
  letI := w.embedding.toAlgebra
  let φ : K →+* ℂ := (IsAlgClosed.lift (M := ℂ) (R := (maximalRealSubfield F K))).toRingHom
  have hφ : w.embedding = φ.comp (algebraMap _ K) := by
    simp only [AlgHom.toRingHom_eq_coe, AlgHom.comp_algebraMap_of_tower, φ, this]
    simp only [RingHom.algebraMap_toAlgebra, this, φ]
  obtain h | h := isReal_or_isComplex (.mk φ)
  · have : w = (InfinitePlace.mk φ).comap (algebraMap _ K) := by
      rw [comap_mk, ← hφ, mk_embedding]
    rw [this]
    exact IsReal.comap _ h
  · refine InfinitePlace.isReal_iff.mpr ?_
    rw [hφ]
    have : ∃ σ : K ≃ₐ[F] K, IsConj φ σ := by
      apply exists_isConj_of_not_isUnramified
      rw [not_isUnramified_iff]
      refine ⟨h, ?_⟩
      exact IsTotallyReal.isReal _
    obtain ⟨σ, hσ⟩ := this
    rw [toto _ _ hσ]
    rw [maximalRealSubfield]
    rw [IntermediateField.fixingSubgroup_fixedField]
    apply Subgroup.subset_closure
    exact ⟨_, hσ⟩

theorem _root_.NumberField.IsTotallyReal.le_maximalRealSubfield [NumberField F] [NumberField K]
    (E : IntermediateField F K) (h : IsTotallyReal E) : E ≤ maximalRealSubfield F K := by
  rw [IsTotallyReal_iff] at h
  rw [maximalRealSubfield]
  rw [IntermediateField.le_iff_le]
  rw [Subgroup.closure_le]
  rintro σ ⟨φ, hσ⟩
  rw [SetLike.mem_coe]
  rw [← toto _ _ hσ]
  rw [← isReal_mk_iff]
  exact h _

-- variable {τ : K ≃ₐ[F] K} (hτ : ∀ φ : K →+* ℂ, IsConj φ τ) [FiniteDimensional F K]

-- example (φ : K →+* ℂ) (hφ : ¬ IsReal φ):
--     Module.finrank (maximalRealSubfield F K) K = 2 := by
--   classical
--   rw [maximalRealSubfield]
--   rw [IntermediateField.finrank_fixedField_eq_card]
--   have : {σ | ∃ φ, ComplexEmbedding.IsConj φ σ} = {τ} := by
--     ext σ
--     constructor
--     · intro ⟨φ, hφ⟩
--       exact (IsConj.ext_iff hφ).mpr (hτ φ)
--     · intro h
--       refine ⟨φ, ?_⟩
--       rw [h]
--       exact hτ φ
--   rw [this]
--   rw [← Subgroup.zpowers_eq_closure]
--   rw [Fintype.card_zpowers]
--   rw [orderOf_isConj (hτ φ), if_neg hφ]

variable [NumberField F] [NumberField K] [IsTotallyReal F] [IsTotallyComplex K]

theorem isCM_maximalRealSubfield_of_forall_isConj [IsGalois F K] {τ : K ≃ₐ[F] K}
    (hτ : ∀ φ : K →+* ℂ, IsConj φ τ) :
    IsCM (maximalRealSubfield F K) K := ⟨by
  classical
  obtain φ := (Classical.choice (inferInstance : Nonempty (K →+* ℂ)))
  have : {σ | ∃ φ, ComplexEmbedding.IsConj φ σ} = {τ} :=
    Set.ext fun σ ↦ ⟨fun ⟨φ, hφ⟩ ↦ (IsConj.ext_iff hφ).mpr (hτ φ), fun h ↦ ⟨φ, h ▸ hτ φ⟩⟩
  rw [maximalRealSubfield, IntermediateField.finrank_fixedField_eq_card, this,
    ← Subgroup.zpowers_eq_closure, Fintype.card_zpowers, orderOf_isConj (hτ φ), if_neg]
  exact isComplex_mk_iff.mp <| IsTotallyComplex.isComplex _⟩

-- class IsAbelianGalois (K L : Type*) [Field K] [Field L] [Algebra K L] extends
--   IsGalois K L, Std.Commutative (α := L ≃ₐ[K] L) (· * ·)

-- instance (K L : Type*) [Field K] [Field L] [Algebra K L] [IsAbelianGalois K L] :
--     CommGroup (L ≃ₐ[K] L) where
--   mul_comm := Std.Commutative.comm

class IsMulCommutative (M : Type*) [Mul M] : Prop where
  is_comm : Std.Commutative (α := M) (· * ·)

instance {G : Type*} [Group G] [IsMulCommutative G] :
     CommGroup G where
   mul_comm := IsMulCommutative.is_comm.comm

instance [IsGalois ℚ K] [IsMulCommutative (K ≃ₐ[ℚ] K)]:
    IsCM (maximalRealSubfield ℚ K) K := by
  obtain ψ := (Classical.choice (inferInstance : Nonempty (K →+* ℂ)))
  obtain ⟨τ, hτ⟩ := exists_isConj ℚ ψ
  have : ∀ φ : K →+* ℂ, IsConj φ τ := by
    intro φ
    obtain ⟨f, rfl⟩ := ComplexEmbedding.exists_comp_symm_eq_of_comp_eq (k := ℚ) ψ φ (by ext; simp)
    have := ComplexEmbedding.IsConj_comp_of_isConj hτ f
    rwa [mul_comm, ← AlgEquiv.aut_inv, inv_mul_cancel_left] at this
  exact isCM_maximalRealSubfield_of_forall_isConj ℚ K this

example [h : IsCM F K] :
    F ≃ₐ[ℚ] maximalRealSubfield ℚ K := by
  let f := AlgEquiv.ofInjectiveField (algebraMap F K).toRatAlgHom
  let F₁ : IntermediateField ℚ K := (algebraMap F K).fieldRange.toIntermediateField (by
    intro x
    refine RingHom.mem_fieldRange.mpr ?_
    use x
    simp only [map_ratCast, eq_ratCast])
  let e : F ≃ₐ[ℚ] F₁ := by
    unfold F₁
    exact f
  have h₁ : IsTotallyReal F₁ := IsTotallyReal.ofRingEquiv f.toRingEquiv
  have h₂ : IsCM F₁ K := by
    refine { toIsTotallyReal := h₁, toIsTotallyComplex := inferInstance, finrank_eq_two' := ?_ }
    unfold F₁
    rw [← h.finrank_eq_two']
    have := Algebra.rank_eq_of_equiv_equiv f.toRingEquiv (RingEquiv.refl K) ?_
    rw [Module.finrank, Module.finrank, this]
    rfl
    ext
    simp [f]
    rfl
  have := h₁.le_maximalRealSubfield
  have : F₁ = maximalRealSubfield ℚ K := by
    refine IntermediateField.eq_of_le_of_finrank_le' this ?_
    rw [IsCM.finrank_eq_two]
    refine (Nat.two_le_iff (Module.finrank (maximalRealSubfield ℚ K) K)).mpr ⟨?_, ?_⟩
    · exact Module.finrank_pos.ne'
    · by_contra h
      have h₁ := IntermediateField.eq_of_le_of_finrank_eq' (F := maximalRealSubfield ℚ K) (E := ⊤)
        le_top ?_
      obtain φ := (Classical.choice (inferInstance : Nonempty (K →+* ℂ)))
      obtain ⟨σ, hσ⟩ := exists_isConj F φ
      let τ := σ.restrictScalars ℚ
      have hτ : ComplexEmbedding.IsConj φ τ := by
        refine (IsConj.ext_iff hσ).mp ?_
        rfl
      have hφ : ¬ IsReal φ := by
        rw [← @isComplex_mk_iff]
        exact IsTotallyComplex.isComplex _
      have :=  maximalRealSubfield_ne_top ℚ K hφ hτ
      exact this h₁


--      rw [(AlgEquiv.restrictScalars_injective ℚ).eq_iff] at h₁

--      have := (maximalRealSubfield_ne_top ℚ ?_ hτ)
      rw [h]
      exact IntermediateField.finrank_top.symm
  let g : F₁ ≃ₐ[ℚ] maximalRealSubfield ℚ K := by
    exact IntermediateField.equivOfEq this
  let j := e.trans g
  exact j


end Abelian

end IsCM
