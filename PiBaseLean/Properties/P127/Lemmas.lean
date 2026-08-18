module

public import PiBaseLean.AdditionalDefs.Meta
public import PiBaseLean.Properties.P127.Defs

@[expose] public section

namespace PiBase

open Topology Filter Set Function TopologicalSpace

universe u

section Meta

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

theorem Homeomorph.dowkerSpace [h : DowkerSpace X] (f : X ≃ₜ Y) : DowkerSpace Y :=
  Formal.P127.well_defined f h

theorem WellDefined.dowkerSpace : WellDefined DowkerSpace :=
  fun {_ _} _ _ h hX => Formal.P127.well_defined h.some hX

end Meta

end PiBase
