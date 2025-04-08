import Mathlib.NumberTheory.GaussSum
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.Cyclotomic.Gal
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.NumberTheory.Cyclotomic.CyclotomicCharacter

set_option linter.style.header false

noncomputable section
variable {K : Type*} [Field K] [CharZero K] {p : ℕ+} [hp : Fact (Nat.Prime p)]
  [IsCyclotomicExtension {p} ℚ K]

def artinMap : (ZMod p)ˣ ≃* (K ≃ₐ[ℚ] K) :=
  (IsCyclotomicExtension.autEquivPow K (Polynomial.cyclotomic.irreducible_rat p.pos)).symm
