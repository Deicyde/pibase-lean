module

public import PiBaseLean.AdditionalDefs.Meta
public import PiBaseLean.Properties.P126.Defs

@[expose] public section

namespace PiBase

open Topology Filter Set Function TopologicalSpace

section Meta

universe u

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

theorem Homeomorph.doorSpace [h : DoorSpace X] (f : X ≃ₜ Y) : DoorSpace Y :=
  Formal.P126.well_defined f h

theorem WellDefined.doorSpace : WellDefined DoorSpace :=
  fun {_ _} _ _ h hX => Homeomorph.doorSpace h.some

end Meta

end PiBase
