module

public import PiBaseLean.AdditionalDefs.Meta
public import PiBaseLean.Properties.P217.Defs

@[expose] public section

namespace PiBase

open Topology Filter Set Function TopologicalSpace

section Meta

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

theorem WellDefined.stronglyZeroDimensionalSpace : WellDefined StronglyZeroDimensionalSpace :=
  fun hXY hX => Formal.P217.well_defined hXY.some hX

end Meta

end PiBase
