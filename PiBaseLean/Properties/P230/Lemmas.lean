module

public import PiBaseLean.AdditionalDefs.Meta
public import PiBaseLean.Properties.P230.Defs

@[expose] public section

namespace PiBase

open Topology Filter Set Function TopologicalSpace

section Meta

universe u

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

theorem Homeomorph.locallySimplyConnectedSpace [h : LocallySimplyConnectedSpace X]
    (f : X ≃ₜ Y) : LocallySimplyConnectedSpace Y :=
  Formal.P230.well_defined f h

theorem WellDefined.locallySimplyConnectedSpace : WellDefined LocallySimplyConnectedSpace :=
  fun {_ _} _ _ h hX => Homeomorph.locallySimplyConnectedSpace h.some

end Meta

end PiBase
