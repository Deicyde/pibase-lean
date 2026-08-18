module

public import PiBaseLean.AdditionalDefs.Meta
public import PiBaseLean.Properties.P106.Defs

@[expose] public section

namespace PiBase

open Topology Filter Set Function TopologicalSpace

section Meta

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

theorem Homeomorph.hasGδDiagonal [h : HasGδDiagonal X] (f : X ≃ₜ Y) : HasGδDiagonal Y :=
  Formal.P106.well_defined f h

theorem WellDefined.hasGδDiagonal : WellDefined HasGδDiagonal :=
  fun {_ _} _ _ h hX => Homeomorph.hasGδDiagonal h.some

end Meta

end PiBase
