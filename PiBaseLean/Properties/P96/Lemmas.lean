module

public import PiBaseLean.AdditionalDefs.Meta
public import PiBaseLean.Properties.P96.Defs

@[expose] public section

namespace PiBase

open Topology Filter Set Function TopologicalSpace

section Meta

universe u

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

theorem Homeomorph.locallyArcConnectedSpace [h : LocallyArcConnectedSpace X]
    (f : X ≃ₜ Y) : LocallyArcConnectedSpace Y :=
  Formal.P96.well_defined f h

theorem WellDefined.locallyArcConnectedSpace : WellDefined LocallyArcConnectedSpace :=
  fun {_ _} _ _ h hX => Homeomorph.locallyArcConnectedSpace h.some

end Meta

end PiBase
