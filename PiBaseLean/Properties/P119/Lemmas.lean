module

public import PiBaseLean.AdditionalDefs.Meta
public import PiBaseLean.Properties.P119.Defs

@[expose] public section

namespace PiBase

open Topology Filter Set Function TopologicalSpace

section Meta

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

theorem Homeomorph.stoneanSpace [h : StoneanSpace X] (f : X ≃ₜ Y) : StoneanSpace Y :=
  Formal.P119.well_defined f h

theorem WellDefined.stoneanSpace : WellDefined StoneanSpace :=
  fun {_ _} _ _ h hX => Homeomorph.stoneanSpace h.some

end Meta

end PiBase
