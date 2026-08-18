module

public import Mathlib.Topology.Connected.Basic
public import PiBaseLean.Properties.Bundled.Defs

@[expose] public section

open Topology Set Function

namespace PiBase

/- 196. Hereditarily connected -/
class HereditarilyConnected (X : Type*) [TopologicalSpace X] : Prop where
  subset_connected (s : Set X) : IsPreconnected s

end PiBase

namespace PiBase.Formal

def P196 : Property where
  toPred := HereditarilyConnected
  well_defined φ h := by
    constructor
    intro t
    have h1 := h.subset_connected (φ ⁻¹' t)
    have h2 := h1.image φ φ.continuous.continuousOn
    rwa [φ.image_preimage t] at h2

end PiBase.Formal
