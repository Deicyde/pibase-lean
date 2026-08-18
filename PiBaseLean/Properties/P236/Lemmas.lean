module

public import PiBaseLean.AdditionalDefs.Meta
public import PiBaseLean.Properties.P236.Defs

@[expose] public section

namespace PiBase

open Topology Filter Set Function TopologicalSpace

section Meta


variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

theorem WellDefined.locallyNEuclideanHalfSpace : WellDefined LocallyNEuclideanHalfSpace :=
  fun {_ _} _ _ h hX => Formal.P236.well_defined h.some hX

end Meta

end PiBase
