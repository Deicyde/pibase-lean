module

public import PiBaseLean.AdditionalDefs.Meta
public import PiBaseLean.Properties.P25.Defs

@[expose] public section

namespace PiBase

open Topology Filter Set Function TopologicalSpace

section Meta

universe u

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

theorem Homeomorph.exhaustibleByCompacts [h : ExhaustibleByCompacts X] (f : X ≃ₜ Y) :
    ExhaustibleByCompacts Y :=
  Formal.P25.well_defined f h

theorem WellDefined.exhaustibleByCompacts : WellDefined ExhaustibleByCompacts :=
  fun {_ _} _ _ hX h => Homeomorph.exhaustibleByCompacts hX.some

end Meta

end PiBase
