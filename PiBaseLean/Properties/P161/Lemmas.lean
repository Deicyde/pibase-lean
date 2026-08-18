module

public import PiBaseLean.AdditionalDefs.Meta
public import PiBaseLean.Properties.P161.Defs

@[expose] public section

namespace PiBase

open Topology Filter Set Function TopologicalSpace

section Meta

universe u

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

theorem Homeomorph.markovKMengerSpace [h : MarkovKMengerSpace X] (f : X ≃ₜ Y) :
    MarkovKMengerSpace Y :=
  Formal.P161.well_defined f h

theorem WellDefined.markovKMengerSpace : WellDefined MarkovKMengerSpace :=
  fun {_ _} _ _ hXY _hX => Homeomorph.markovKMengerSpace hXY.some

end Meta

end PiBase
