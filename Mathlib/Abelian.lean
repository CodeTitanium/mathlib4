import Mathlib.FieldTheory.Galois.Basic

variable (E F : Type*) [Field E] [Field F] [Algebra F E] [IsGalois F E]
  [IsMulCommutative (E ≃ₐ[F] E)]

#synth CommGroup (E ≃ₐ[F] E) -- CommGroup.ofIsMulCommutative
