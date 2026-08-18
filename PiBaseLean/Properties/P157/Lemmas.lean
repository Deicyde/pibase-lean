module

public import PiBaseLean.AdditionalDefs.Meta
public import PiBaseLean.Properties.P157.Defs

@[expose] public section

namespace PiBase

open Topology Filter Set Function TopologicalSpace

section Meta

universe u

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

theorem Homeomorph.strategicallyKRothbergerSpace [h : StrategicallyKRothbergerSpace X]
    (f : X ≃ₜ Y) : StrategicallyKRothbergerSpace Y :=
  Formal.P157.well_defined f h

theorem WellDefined.strategicallyKRothbergerSpace : WellDefined StrategicallyKRothbergerSpace :=
  fun {_ _} _ _ hXY _hX => Homeomorph.strategicallyKRothbergerSpace hXY.some

end Meta

end PiBase
