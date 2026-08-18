module

public import PiBaseLean.AdditionalDefs.Meta
public import PiBaseLean.Properties.P85.Defs

@[expose] public section

namespace PiBase

open Topology Filter Set Function TopologicalSpace

section Meta

universe u

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

theorem Homeomorph.basicallyDisconnectedSpace [h : BasicallyDisconnectedSpace X] (f : X ≃ₜ Y) :
    BasicallyDisconnectedSpace Y :=
  Formal.P85.well_defined f h

theorem WellDefined.basicallyDisconnectedSpace : WellDefined BasicallyDisconnectedSpace :=
  fun {_ _} _ _ h hX => Homeomorph.basicallyDisconnectedSpace h.some

end Meta

end PiBase
