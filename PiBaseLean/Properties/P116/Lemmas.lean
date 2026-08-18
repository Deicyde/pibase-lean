module

public import PiBaseLean.AdditionalDefs.Meta
public import PiBaseLean.Properties.P116.Defs

@[expose] public section

namespace PiBase

open Topology Filter Set Function TopologicalSpace

section Meta

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

theorem Homeomorph.polishSpace [h : PolishSpace X] (f : X ≃ₜ Y) : PolishSpace Y :=
  Formal.P116.well_defined f h

theorem WellDefined.polishSpace : WellDefined PolishSpace :=
  fun {_ _} _ _ h hX => Homeomorph.polishSpace h.some

end Meta

end PiBase
