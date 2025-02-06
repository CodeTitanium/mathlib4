import Mathlib

open nonZeroDivisors IsLocalization Algebra IsFractionRing

theorem map_le_nonZeroDivisors_of_faithfulSMul {A : Type*} (B : Type*) [CommSemiring A]
    [CommSemiring B] [Algebra A B] [NoZeroDivisors B] [FaithfulSMul A B] {S : Submonoid A}
    (hS : S ≤ A⁰) : Algebra.algebraMapSubmonoid B S ≤ B⁰ :=
  map_le_nonZeroDivisors_of_injective _ (FaithfulSMul.algebraMap_injective A B) hS

variable {R S : Type*} [CommRing R] [IsDomain R] [CommRing S] [IsDomain S] [Algebra R S]
  {P : Ideal R} [P.IsPrime]

attribute [local instance] FractionRing.liftAlgebra

local notation3 "K" => FractionRing R
local notation3 "L" => FractionRing S
local notation3 "P'" => Algebra.algebraMapSubmonoid S P.primeCompl
local notation3 "Rₚ" => Localization.AtPrime P
local notation3 "Sₚ" => Localization P'

instance [NoZeroSMulDivisors R S] [Module.Finite R S] [IsIntegrallyClosed S] :
    IsLocalization (algebraMapSubmonoid S R⁰) L :=
  IsIntegralClosure.isLocalization _ K _ _

instance [Module.Finite R S] [IsIntegrallyClosed S] [NoZeroSMulDivisors R S] :
    FiniteDimensional K L :=
  Module.Finite_of_isLocalization R S _ _ R⁰

variable [FaithfulSMul R S]

noncomputable instance : Algebra Sₚ L :=
  (map _ (T := S⁰) (RingHom.id S)
    (map_le_nonZeroDivisors_of_faithfulSMul _ P.primeCompl_le_nonZeroDivisors)).toAlgebra

instance : IsScalarTower S Sₚ L :=
  localization_isScalarTower_of_submonoid_le _ _ _ _
    (map_le_nonZeroDivisors_of_faithfulSMul _ P.primeCompl_le_nonZeroDivisors)

instance : IsFractionRing Rₚ K :=
  isFractionRing_of_isDomain_of_isLocalization P.primeCompl _ _

instance : IsFractionRing Sₚ L :=
  isFractionRing_of_isDomain_of_isLocalization P' _ _

noncomputable instance : Algebra Rₚ L :=
  (IsLocalization.lift (M := P.primeCompl) (g := algebraMap R L) <|
    fun ⟨x, hx⟩ ↦ by simpa using fun h ↦ hx <| by simp [h]).toAlgebra
