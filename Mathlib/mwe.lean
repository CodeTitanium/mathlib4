import Mathlib.FieldTheory.Galois.Basic

variable (F E : Type*) [Field F] [Field E] [Algebra F E] [IsGalois F E]
  [Subgroup.IsCommutative (⊤ : Subgroup (E ≃ₐ[F] E))]
