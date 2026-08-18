module

public import PiBaseLean.AdditionalDefs.Meta
public import PiBaseLean.Properties.P70.Defs

@[expose] public section

namespace PiBase

open Topology Filter Set Function TopologicalSpace

section Meta

universe u

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

theorem Homeomorph.markovMengerSpace [h : MarkovMengerSpace X] (f : X ≃ₜ Y) :
    MarkovMengerSpace Y :=
  Formal.P70.well_defined f h

theorem WellDefined.markovMengerSpace : WellDefined MarkovMengerSpace :=
  fun {_ _} _ _ h _ => Homeomorph.markovMengerSpace h.some

end Meta

end PiBase
