module

public import PiBaseLean.AdditionalDefs.Meta
public import PiBaseLean.Properties.P88.Defs

@[expose] public section

open Topology Set Function Filter TopologicalSpace

namespace PiBase

/- 108. Hereditarily collectionwise normal -/
class HereditarilyCollectionwiseNormalSpace (X : Type*) [TopologicalSpace X] : Prop where
  hereditarily_collectionwise_normal : Hereditarily CollectionwiseNormalSpace X

end PiBase

namespace PiBase.Formal

def P108 : Property where
  toPred := HereditarilyCollectionwiseNormalSpace
  well_defined φ h := by
    constructor
    intro s
    have hX := h.hereditarily_collectionwise_normal (φ ⁻¹' s)
    exact Formal.P88.well_defined (IsHomeo.subset_preimage φ s).some hX

end PiBase.Formal
