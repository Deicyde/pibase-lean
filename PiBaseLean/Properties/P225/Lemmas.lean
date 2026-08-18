module

public import PiBaseLean.AdditionalDefs.Meta
public import PiBaseLean.Properties.P225.Defs

@[expose] public section

namespace PiBase

open Topology Filter Set Function TopologicalSpace

section Meta

universe u

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

theorem Homeomorph.lCSpace [h : LCSpace X] (f : X ≃ₜ Y) : LCSpace Y :=
  Formal.P225.well_defined f h

theorem WellDefined.lCSpace : WellDefined LCSpace :=
  fun {_ _} _ _ h _ => Homeomorph.lCSpace h.some

end Meta

end PiBase
