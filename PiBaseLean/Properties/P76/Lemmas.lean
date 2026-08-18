module

public import PiBaseLean.AdditionalDefs.Meta
public import PiBaseLean.Properties.P76.Defs

@[expose] public section

namespace PiBase

open Topology Filter Set Function TopologicalSpace

section Meta

universe u

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

theorem Homeomorph.proximalSpace [h : ProximalSpace X] (f : X ≃ₜ Y) : ProximalSpace Y :=
  Formal.P76.well_defined f h

theorem WellDefined.proximalSpace : WellDefined ProximalSpace :=
  fun {_ _} _ _ h _ => Homeomorph.proximalSpace h.some

end Meta

end PiBase
