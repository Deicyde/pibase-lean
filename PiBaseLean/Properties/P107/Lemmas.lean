module

public import PiBaseLean.AdditionalDefs.Meta
public import PiBaseLean.Properties.P107.Defs

@[expose] public section

namespace PiBase

open Topology Filter Set Function TopologicalSpace

section Meta

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

theorem Homeomorph.hasClosedPoint [h : HasClosedPoint X] (f : X ≃ₜ Y) : HasClosedPoint Y :=
  Formal.P107.well_defined f h

theorem WellDefined.hasClosedPoint : WellDefined HasClosedPoint :=
  fun {_ _} _ _ h hX => Homeomorph.hasClosedPoint h.some

end Meta

end PiBase
