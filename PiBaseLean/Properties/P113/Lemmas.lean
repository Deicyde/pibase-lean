module

public import PiBaseLean.AdditionalDefs.Meta
public import PiBaseLean.Properties.P113.Defs

@[expose] public section

namespace PiBase

open Topology Filter Set Function TopologicalSpace

section Meta

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

theorem Homeomorph.mooreSpace [h : MooreSpace X] (f : X ≃ₜ Y) : MooreSpace Y :=
  Formal.P113.well_defined f h

theorem WellDefined.mooreSpace : WellDefined MooreSpace :=
  fun {_ _} _ _ h _ => Homeomorph.mooreSpace h.some

end Meta

end PiBase
