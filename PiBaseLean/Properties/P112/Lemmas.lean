module

public import PiBaseLean.AdditionalDefs.Meta
public import PiBaseLean.Properties.P112.Defs

@[expose] public section

namespace PiBase

open Topology Filter Set Function TopologicalSpace

section Meta

universe u

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

theorem Homeomorph.submetrizableSpace [h : SubmetrizableSpace X] (f : X ≃ₜ Y) :
    SubmetrizableSpace Y :=
  Formal.P112.well_defined f h

theorem WellDefined.submetrizableSpace : WellDefined SubmetrizableSpace :=
  fun {_ _} _ _ h _ => Homeomorph.submetrizableSpace h.some

end Meta

end PiBase
