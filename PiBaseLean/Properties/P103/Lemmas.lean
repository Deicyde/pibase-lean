module

public import PiBaseLean.AdditionalDefs.Meta
public import PiBaseLean.Properties.P103.Defs

@[expose] public section

namespace PiBase

open Topology Filter Set Function TopologicalSpace

section Meta

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

theorem Homeomorph.stronglyKcSpace [h : StronglyKcSpace X] (f : X ≃ₜ Y) : StronglyKcSpace Y :=
  Formal.P103.well_defined f h

theorem WellDefined.stronglyKcSpace : WellDefined StronglyKcSpace :=
  fun {_ _} _ _ h hX => Homeomorph.stronglyKcSpace h.some

end Meta

end PiBase
