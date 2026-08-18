module

public import PiBaseLean.AdditionalDefs.Meta
public import PiBaseLean.Properties.P88.Defs

@[expose] public section

namespace PiBase

open Topology Filter Set Function

section Meta

universe u

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

theorem WellDefined.collectionwiseNormalSpace : WellDefined CollectionwiseNormalSpace :=
  fun {_ _} _ _ h hX => Formal.P88.well_defined h.some hX

end Meta

end PiBase
