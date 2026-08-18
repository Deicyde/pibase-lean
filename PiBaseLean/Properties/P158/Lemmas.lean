module

public import PiBaseLean.AdditionalDefs.Meta
public import PiBaseLean.Properties.P158.Defs

@[expose] public section

namespace PiBase

open Topology Filter Set Function TopologicalSpace

section Meta

universe u

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

theorem Homeomorph.markovKRothbergerSpace [h : MarkovKRothbergerSpace X] (f : X ≃ₜ Y) :
    MarkovKRothbergerSpace Y :=
  Formal.P158.well_defined f h

theorem WellDefined.markovKRothbergerSpace : WellDefined MarkovKRothbergerSpace :=
  fun {_ _} _ _ hXY _hX => Homeomorph.markovKRothbergerSpace hXY.some

end Meta

end PiBase
