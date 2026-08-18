module

public import PiBaseLean.AdditionalDefs.Meta
public import PiBaseLean.Properties.P157.Defs

@[expose] public section

namespace PiBase

open Topology Filter Set Function TopologicalSpace

section Meta

universe u

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

theorem WellDefined.strategicallyKRothbergerSpace : WellDefined StrategicallyKRothbergerSpace :=
  fun {_ _} _ _ h hX => Formal.P157.well_defined h.some hX

end Meta

end PiBase
