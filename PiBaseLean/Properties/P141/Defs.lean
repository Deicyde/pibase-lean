module

public import Mathlib.Topology.Compactness.CompactlyGeneratedSpace
public import PiBaseLean.Properties.Bundled.Defs

@[expose] public section

open Topology Set Function Filter TopologicalSpace

universe u

namespace PiBase

/- 141. k₂-space -/
#check CompactlyGeneratedSpace

end PiBase

namespace PiBase.Formal

def P141 : Property where
  toPred := CompactlyGeneratedSpace
  well_defined φ h := by
    have hX : CompactlyGeneratedSpace _ := h
    apply compactlyGeneratedSpace_of_isClosed
    intro s hs
    have h_pre_closed : IsClosed (φ ⁻¹' s) := by
      have : CompactlyGeneratedSpace _ := hX
      apply CompactlyGeneratedSpace.isClosed'
      intro K _ _ _ f hf
      have h_eq : f ⁻¹' (φ ⁻¹' s) = (φ ∘ f) ⁻¹' s := by ext; simp
      rw [h_eq]
      exact hs K (φ ∘ f) (φ.continuous.comp hf)
    have h_eq : s = φ '' (φ ⁻¹' s) := (φ.image_preimage s).symm
    rw [h_eq]
    exact φ.isClosed_image.mpr h_pre_closed

end PiBase.Formal
