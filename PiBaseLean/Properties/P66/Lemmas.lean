module

public import PiBaseLean.AdditionalDefs.Meta
public import PiBaseLean.Properties.P66.Defs

@[expose] public section

namespace PiBase

open Topology Filter Set Function TopologicalSpace

universe u

section Meta

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

theorem Homeomorph.mengerSpace [h : MengerSpace X] (f : X ≃ₜ Y) : MengerSpace Y :=
  Formal.P66.well_defined f h

theorem WellDefined.mengerSpace : WellDefined MengerSpace :=
  fun {_ _} _ _ h hX => Homeomorph.mengerSpace h.some

end Meta

end PiBase
