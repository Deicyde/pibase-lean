module

public import PiBaseLean.AdditionalDefs.Meta
public import PiBaseLean.Properties.P24.Defs

@[expose] public section

namespace PiBase

open Topology Filter Set Function TopologicalSpace

section Meta

universe u

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

theorem Homeomorph.locallyRelativelyCompactSpace [h : LocallyRelativelyCompactSpace X]
    (f : X ≃ₜ Y) : LocallyRelativelyCompactSpace Y :=
  Formal.P24.well_defined f h

theorem WellDefined.locallyRelativelyCompactSpace : WellDefined LocallyRelativelyCompactSpace :=
  fun {_ _} _ _ h hX => Homeomorph.locallyRelativelyCompactSpace h.some

end Meta

end PiBase
