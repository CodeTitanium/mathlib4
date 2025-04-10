import Mathlib.FieldTheory.Galois.Basic

variable (E F : Type*) [Field E] [Field F] [IsGalois F E] [IsMulCommutative (E ≃ₐ[F] E)]

#synth CommGroup (E ≃ₐ[F] E)
