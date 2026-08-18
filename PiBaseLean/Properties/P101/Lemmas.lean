module

public import PiBaseLean.AdditionalDefs.Meta
public import PiBaseLean.Properties.P101.Defs

@[expose] public section

namespace PiBase

open Topology Filter Set Function TopologicalSpace

section Meta

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

theorem Homeomorph.hasClosedRetract [h : HasClosedRetract X] (f : X ≃ₜ Y) : HasClosedRetract Y :=
  Formal.P101.well_defined f h

theorem WellDefined.hasClosedRetract : WellDefined HasClosedRetract :=
  fun {_ _} _ _ h hX => Homeomorph.hasClosedRetract h.some

end Meta

end PiBase
