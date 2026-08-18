module

public import PiBaseLean.AdditionalDefs.Meta
public import PiBaseLean.Properties.P96.Defs

@[expose] public section

namespace PiBase

open Topology Filter Set Function TopologicalSpace

section Meta


variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

theorem WellDefined.locallyArcConnectedSpace : WellDefined LocallyArcConnectedSpace :=
  fun {_ _} _ _ h hX => Formal.P96.well_defined h.some hX

end Meta

end PiBase
