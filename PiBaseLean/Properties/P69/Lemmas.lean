module

public import PiBaseLean.AdditionalDefs.Meta
public import PiBaseLean.Properties.P69.Defs

@[expose] public section

namespace PiBase

open Topology Filter Set Function TopologicalSpace

section Meta

universe u

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

theorem Homeomorph.strategicMengerSpace [h : StrategicMengerSpace X] (f : X ≃ₜ Y) :
    StrategicMengerSpace Y :=
  Formal.P69.well_defined f h

theorem WellDefined.strategicMengerSpace : WellDefined StrategicMengerSpace :=
  fun {_ _} _ _ h _ => Homeomorph.strategicMengerSpace h.some

end Meta

end PiBase
