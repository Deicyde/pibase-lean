module

public import Mathlib.SetTheory.Cardinal.Continuum
public import Mathlib.Topology.Defs.Basic
public import PiBaseLean.Properties.Bundled.Defs

@[expose] public section

open TopologicalSpace Set Cardinal

namespace PiBase

/- 209. Density ≤ 𝔠 -/
class DensityLeContinuum (X : Type*) [TopologicalSpace X] : Prop where
  ex_dense : ∃ s : Set X, Dense s ∧ #s ≤ 𝔠

end PiBase

namespace PiBase.Formal

def P209 : Property where
  toPred := DensityLeContinuum
  well_defined φ h := by
    obtain ⟨s, hDense, hLe⟩ := h.ex_dense
    refine ⟨φ '' s, ?_, ?_⟩
    · intro y
      have hmem : φ.symm y ∈ closure s := hDense (φ.symm y)
      have hmem' : y ∈ φ '' closure s := by
        rw [Set.mem_image]
        exact ⟨φ.symm y, hmem, φ.apply_symm_apply y⟩
      rw [φ.image_closure] at hmem'
      exact hmem'
    · have hEq : #(φ '' s) = #s := Cardinal.mk_image_eq φ.injective
      calc #(φ '' s) = #s := hEq
        _ ≤ 𝔠 := hLe

end PiBase.Formal
