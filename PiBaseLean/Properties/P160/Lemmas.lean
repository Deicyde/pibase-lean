module

public import PiBaseLean.AdditionalDefs.Meta
public import PiBaseLean.Properties.P160.Defs

@[expose] public section

namespace PiBase

open Topology Filter Set Function TopologicalSpace

section Meta

universe u

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

theorem Homeomorph.strategicallyKMengerSpace [h : StrategicallyKMengerSpace X] (f : X ≃ₜ Y) :
    StrategicallyKMengerSpace Y :=
  Formal.P160.well_defined f h

theorem WellDefined.strategicallyKMengerSpace : WellDefined StrategicallyKMengerSpace :=
  fun {_ _} _ _ hXY _hX => Homeomorph.strategicallyKMengerSpace hXY.some

end Meta

end PiBase
