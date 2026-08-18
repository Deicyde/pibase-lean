module

public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import PiBaseLean.Properties.Bundled.Defs

@[expose] public section

open Topology Set Function Filter TopologicalSpace

namespace PiBase

/- 60. Strongly connected -/
class StronglyConnectedSpace (X : Type*) [TopologicalSpace X] : Prop where
  strongly_connected : ∀ f : X → ℝ, Continuous f → ∃ r : ℝ, f = Function.const X r

end PiBase

namespace PiBase.Formal

def P60 : Property where
  toPred := StronglyConnectedSpace
  well_defined φ h := by
    constructor
    intro f hf
    have hfφ : Continuous (f ∘ φ) := hf.comp φ.continuous
    obtain ⟨r, hr⟩ := h.strongly_connected (f ∘ φ) hfφ
    refine ⟨r, ?_⟩
    funext y
    have hy : ∃ x, φ x = y := φ.surjective y
    obtain ⟨x, rfl⟩ := hy
    have : (f ∘ φ) x = r := by
      have h1 : (f ∘ φ) = Function.const _ r := hr
      exact congr_fun h1 x
    exact this

end PiBase.Formal
