module

public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.Homeomorph.Lemmas
public import PiBaseLean.Properties.Bundled.Defs

@[expose] public section

open Topology Set Function Filter TopologicalSpace

universe u

namespace PiBase

/- 170. k₁-Hausdorff -/
class K1T2Space (X : Type u) [TopologicalSpace X] : Prop where
  compact_t2 (s : Set X) : IsCompact s → T2Space s

end PiBase

namespace PiBase.Formal

def P170 : Property where
  toPred := K1T2Space
  well_defined φ h := by
    constructor
    intro s hs
    -- Pull compact s ⊆ Y back to X via φ.symm; compactness preserved by continuous image
    have hK : IsCompact (φ.symm '' s) := hs.image φ.symm.continuous
    have hT2 : T2Space (φ.symm '' s) := h.compact_t2 _ hK
    -- Restricted homeomorphism (φ.symm '' s) ≃ₜ s transports T₂
    have e : (φ.symm '' s : Set _) ≃ₜ (s : Set _) := (φ.symm.image s).symm
    exact e.t2Space (X := (φ.symm '' s : Set _)) (Y := (s : Set _))

end PiBase.Formal
