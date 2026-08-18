module

public import PiBaseLean.AdditionalDefs.Meta
public import PiBaseLean.Properties.P221.Defs

@[expose] public section

namespace PiBase

open Topology Filter Set Function TopologicalSpace

section Meta

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

theorem WellDefined.dieudonneCompleteSpace : WellDefined DieudonneCompleteSpace :=
  fun {_X _Y} _ _ hXY hX => Formal.P221.well_defined hXY.some hX

end Meta

end PiBase
