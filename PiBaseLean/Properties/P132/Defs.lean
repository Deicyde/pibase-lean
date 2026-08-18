module

public import Mathlib.Topology.GDelta.Basic
public import PiBaseLean.Properties.Bundled.Defs

@[expose] public section

open Topology Set Function Filter TopologicalSpace

universe u

namespace PiBase

/- 132. Gδ space -/
class GδSpace (X : Type u) [TopologicalSpace X] : Prop where
  closed_gdelta : ∀ ⦃s : Set X⦄, IsClosed s → IsGδ s

end PiBase

namespace PiBase.Formal

def P132 : Property where
  toPred := GδSpace
  well_defined φ h := by
    constructor
    intro s hs
    -- pull closed s in Y back to X via φ
    have h1 : IsClosed (φ ⁻¹' s) := φ.isClosed_preimage.mpr hs
    have h2 : IsGδ (φ ⁻¹' s) := h.closed_gdelta h1
    -- push forward Gδ via φ.symm using IsGδ.preimage; s = φ '' (φ ⁻¹' s) = φ.symm ⁻¹' (φ ⁻¹' s)
    convert IsGδ.preimage φ.symm.continuous h2 using 1
    rw [← φ.image_eq_preimage_symm]
    exact (φ.image_preimage s).symm

end PiBase.Formal
