module

public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.Homeomorph.Lemmas
public import PiBaseLean.Properties.Bundled.Defs

@[expose] public section

open Topology Set TopologicalSpace

universe u

namespace PiBase

/- 112. Submetrizable space -/
class SubmetrizableSpace (X : Type u) [τ : TopologicalSpace X] : Prop where
  le_metrizable : ∃ m : MetricSpace X, τ ≤ m.toUniformSpace.toTopologicalSpace

end PiBase

namespace PiBase.Formal

def P112 : Property where
  toPred := SubmetrizableSpace
  well_defined {X Y} _ _ φ h := by
    obtain ⟨mX, hm⟩ := h.le_metrizable
    let mY : MetricSpace Y := MetricSpace.induced φ.symm φ.symm.injective mX
    refine ⟨⟨mY, ?_⟩⟩
    have h_ind : mY.toUniformSpace.toTopologicalSpace =
        TopologicalSpace.induced (φ.symm : Y → X) mX.toUniformSpace.toTopologicalSpace := rfl
    intro s hs
    rw [h_ind] at hs
    obtain ⟨u, hu, hus⟩ :=
      (isOpen_induced_iff (t := mX.toUniformSpace.toTopologicalSpace) (f := φ.symm)).mp hs
    rw [← hus]
    exact (hm u hu).preimage φ.symm.continuous

end PiBase.Formal
