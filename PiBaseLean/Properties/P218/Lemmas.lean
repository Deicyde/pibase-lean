module

public import PiBaseLean.AdditionalDefs.Meta
public import PiBaseLean.Properties.P218.Defs

@[expose] public section

namespace PiBase

open Topology Filter Set Function TopologicalSpace

section Meta

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

theorem WellDefined.ultranormalSpace : WellDefined UltranormalSpace :=
  fun hXY hX => Formal.P218.well_defined hXY.some hX

end Meta

end PiBase
