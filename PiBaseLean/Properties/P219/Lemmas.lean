module

public import PiBaseLean.AdditionalDefs.Meta
public import PiBaseLean.Properties.P219.Defs

@[expose] public section

namespace PiBase

open Topology Filter Set Function TopologicalSpace

section Meta

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

theorem WellDefined.torontoSpace : WellDefined TorontoSpace :=
  fun hXY hX => Formal.P219.well_defined hXY.some hX

end Meta

end PiBase
