module

public import PiBaseLean.AdditionalDefs.Meta
public import PiBaseLean.Properties.P68.Defs

@[expose] public section

namespace PiBase

open Topology Filter Set Function TopologicalSpace

universe u

section Meta

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

theorem Homeomorph.rothbergerSpace [h : RothbergerSpace X] (f : X ≃ₜ Y) : RothbergerSpace Y :=
  Formal.P68.well_defined f h

theorem WellDefined.rothbergerSpace : WellDefined RothbergerSpace :=
  fun {_ _} _ _ h hX => Homeomorph.rothbergerSpace h.some

end Meta

end PiBase
