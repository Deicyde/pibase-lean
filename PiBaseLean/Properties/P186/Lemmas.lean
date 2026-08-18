module

public import PiBaseLean.AdditionalDefs.Meta
public import PiBaseLean.Properties.P186.Defs

@[expose] public section

namespace PiBase

open Topology Filter Set Function TopologicalSpace

section Meta

universe u

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

theorem Homeomorph.embedsInTopologicalWGroupSpace [h : EmbedsInTopologicalWGroupSpace X]
    (f : X ≃ₜ Y) : EmbedsInTopologicalWGroupSpace Y :=
  Formal.P186.well_defined f h

theorem WellDefined.embedsInTopologicalWGroupSpace : WellDefined EmbedsInTopologicalWGroupSpace :=
  fun {_ _} _ _ h _ => Homeomorph.embedsInTopologicalWGroupSpace h.some

end Meta

end PiBase

