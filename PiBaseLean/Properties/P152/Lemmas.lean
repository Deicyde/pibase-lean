module

public import PiBaseLean.AdditionalDefs.Meta
public import PiBaseLean.Properties.P152.Defs

@[expose] public section

namespace PiBase

open Topology Filter Set Function TopologicalSpace

section Meta

universe u

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

theorem Homeomorph.markovRothbergerSpace [h : MarkovRothbergerSpace X] (f : X ≃ₜ Y) :
    MarkovRothbergerSpace Y :=
  Formal.P152.well_defined f h

theorem WellDefined.markovRothbergerSpace : WellDefined MarkovRothbergerSpace :=
  fun {_ _} _ _ hXY _hX => Homeomorph.markovRothbergerSpace hXY.some

end Meta

end PiBase
