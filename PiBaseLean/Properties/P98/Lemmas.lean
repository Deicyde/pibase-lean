module

public import PiBaseLean.AdditionalDefs.Meta
public import PiBaseLean.Properties.P98.Defs

@[expose] public section

namespace PiBase

open Topology Filter Set Function TopologicalSpace

section Meta

universe u

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

theorem Homeomorph.kω1Space [h : kω1Space X] (f : X ≃ₜ Y) : kω1Space Y :=
  Formal.P98.well_defined f h

theorem WellDefined.kω1Space : WellDefined kω1Space :=
  fun {_ _} _ _ h _ => Homeomorph.kω1Space h.some

end Meta

end PiBase
