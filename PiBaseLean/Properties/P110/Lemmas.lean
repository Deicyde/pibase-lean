module

public import PiBaseLean.AdditionalDefs.Meta
public import PiBaseLean.Properties.P110.Defs

@[expose] public section

namespace PiBase

open Topology Filter Set Function TopologicalSpace

section Meta

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

theorem Homeomorph.developableSpace [h : DevelopableSpace X] (f : X ≃ₜ Y) : DevelopableSpace Y :=
  Formal.P110.well_defined f h

theorem WellDefined.developableSpace : WellDefined DevelopableSpace :=
  fun {_ _} _ _ h _ => Homeomorph.developableSpace h.some

end Meta

end PiBase
