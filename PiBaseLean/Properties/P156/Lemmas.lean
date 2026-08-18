module

public import PiBaseLean.AdditionalDefs.Meta
public import PiBaseLean.Properties.P156.Defs

@[expose] public section

namespace PiBase

open Topology Filter Set Function TopologicalSpace

universe u

section Meta

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

theorem Homeomorph.kRothbergerSpace [h : KRothbergerSpace X] (f : X ≃ₜ Y) : KRothbergerSpace Y :=
  Formal.P156.well_defined f h

theorem WellDefined.kRothbergerSpace : WellDefined KRothbergerSpace :=
  fun {_ _} _ _ h hX => Homeomorph.kRothbergerSpace h.some

end Meta

end PiBase

