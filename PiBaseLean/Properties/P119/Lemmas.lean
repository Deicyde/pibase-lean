module

public import PiBaseLean.AdditionalDefs.Meta
public import PiBaseLean.Properties.P119.Defs

@[expose] public section

namespace PiBase

open Topology Filter Set Function TopologicalSpace

section Meta

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

theorem WellDefined.stoneanSpace : WellDefined StoneanSpace :=
  fun {_ _} _ _ h hX => Formal.P119.well_defined h.some hX

end Meta

end PiBase
