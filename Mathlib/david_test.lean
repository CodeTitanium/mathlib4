import Mathlib.MeasureTheory.Group.Measure

open MeasureTheory ENNReal

variable {G : Type*} {mG : MeasurableSpace G}

variable [Group G] [MeasurableMul₂ G] [MeasurableInv G] (μ : Measure G)

variable {f g : G → ℝ≥0∞} {y z : G}

-- Doesn't Work!
example (hf : AEMeasurable f μ) (hg : AEMeasurable g μ):
    AEMeasurable (fun x ↦ f x * g (x⁻¹ * (y⁻¹ * z))) μ := by
  set_option trace.Meta.Tactic.fun_prop true in
  fun_prop

example (hf : AEMeasurable f μ) (hg : AEMeasurable g μ):
    AEMeasurable (fun x ↦ f x * g (x⁻¹ * (y⁻¹ * z))) μ := by
  apply hf.mul (hg.comp_quasiMeasurePreserving _)

  --apply (quasiMeasurePreserving_mul_right _ _).comp (quasiMeasurePreserving_inv μ)

-- Works!
example (hf : Measurable f) (hg : Measurable g):
    Measurable (fun x ↦ f x * g (x⁻¹ * (y⁻¹ * z))) := by fun_prop
