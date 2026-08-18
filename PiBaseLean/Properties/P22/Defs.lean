module

public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import PiBaseLean.Properties.Bundled.Defs

@[expose] public section

open Topology Set Function

namespace PiBase

/- 22. PseudocompactSpace -/
class PseudocompactSpace (X : Type*) [TopologicalSpace X] : Prop where
  pseudocompact : ∀ (f : X → ℝ), Continuous f → BddBelow (range f) ∧ BddAbove (range f)

end PiBase

namespace PiBase.Formal

def P22 : Property where
  toPred := PseudocompactSpace
  well_defined φ h := by
    constructor
    intro f hf
    have hfφ : Continuous (f ∘ φ) := hf.comp φ.continuous
    obtain ⟨hBddBelow, hBddAbove⟩ := h.pseudocompact (f ∘ φ) hfφ
    have hRange : range (f ∘ φ) = range f := by
      rw [Set.range_comp, EquivLike.range_eq_univ, Set.image_univ]
    exact ⟨hRange ▸ hBddBelow, hRange ▸ hBddAbove⟩

end PiBase.Formal
