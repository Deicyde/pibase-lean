module

public import PiBaseLean.AdditionalDefs.Meta
public import PiBaseLean.Properties.P151.Defs

@[expose] public section

namespace PiBase

open Topology Filter Set Function TopologicalSpace

section Meta

universe u

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

theorem Homeomorph.strategicallyRothbergerSpace [h : StrategicallyRothbergerSpace X] (f : X ≃ₜ Y) :
    StrategicallyRothbergerSpace Y :=
  Formal.P151.well_defined f h

theorem WellDefined.strategicallyRothbergerSpace : WellDefined StrategicallyRothbergerSpace :=
  fun {_ _} _ _ hXY _hX => Homeomorph.strategicallyRothbergerSpace hXY.some

end Meta

end PiBase
