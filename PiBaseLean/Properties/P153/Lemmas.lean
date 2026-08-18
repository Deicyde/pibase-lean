module

public import PiBaseLean.AdditionalDefs.Meta
public import PiBaseLean.Properties.P153.Defs

@[expose] public section

namespace PiBase

open Topology Filter Set Function TopologicalSpace

universe u

section Meta

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

theorem Homeomorph.omegaMengerSpace [h : OmegaMengerSpace X] (f : X ≃ₜ Y) : OmegaMengerSpace Y :=
  Formal.P153.well_defined f h

theorem WellDefined.omegaMengerSpace : WellDefined OmegaMengerSpace :=
  fun {_ _} _ _ h hX => Homeomorph.omegaMengerSpace h.some

end Meta

end PiBase
