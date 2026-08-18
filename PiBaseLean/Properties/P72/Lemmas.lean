module

public import PiBaseLean.AdditionalDefs.Meta
public import PiBaseLean.Properties.P72.Defs

@[expose] public section

namespace PiBase

open Topology Filter Set Function TopologicalSpace

section Meta

universe u

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

theorem Homeomorph.twoMarkovMengerSpace [h : TwoMarkovMengerSpace X] (f : X ≃ₜ Y) :
    TwoMarkovMengerSpace Y :=
  Formal.P72.well_defined f h

theorem WellDefined.twoMarkovMengerSpace : WellDefined TwoMarkovMengerSpace :=
  fun {_ _} _ _ h _ => Homeomorph.twoMarkovMengerSpace h.some

end Meta

end PiBase
