module

public import PiBaseLean.AdditionalDefs.Meta
public import PiBaseLean.Properties.P107.Defs

@[expose] public section

namespace PiBase

open Topology Filter Set Function TopologicalSpace

section Meta

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

theorem WellDefined.hasClosedPoint : WellDefined HasClosedPoint :=
  fun {_ _} _ _ h hX => Formal.P107.well_defined h.some hX

end Meta

end PiBase
