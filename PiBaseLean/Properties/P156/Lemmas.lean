module

public import PiBaseLean.AdditionalDefs.Meta
public import PiBaseLean.Properties.P156.Defs

@[expose] public section

namespace PiBase

open Topology Filter Set Function TopologicalSpace

universe u

section Meta

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

theorem WellDefined.kRothbergerSpace : WellDefined KRothbergerSpace :=
  fun {_ _} _ _ h hX => Formal.P156.well_defined h.some hX

end Meta

end PiBase

