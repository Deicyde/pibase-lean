module

public import PiBaseLean.AdditionalDefs.Meta
public import PiBaseLean.Properties.P102.Defs

@[expose] public section

namespace PiBase

open Topology Filter Set Function TopologicalSpace

section Meta

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

theorem Homeomorph.semimetrizableSpace [h : SemimetrizableSpace X] (f : X ≃ₜ Y) :
    SemimetrizableSpace Y :=
  Formal.P102.well_defined f h

theorem WellDefined.semimetrizableSpace : WellDefined SemimetrizableSpace :=
  fun {_ _} _ _ h _ => Homeomorph.semimetrizableSpace h.some

end Meta

end PiBase
