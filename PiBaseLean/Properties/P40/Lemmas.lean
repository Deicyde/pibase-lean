module

public import PiBaseLean.AdditionalDefs.Meta
public import PiBaseLean.Properties.P40.Defs

@[expose] public section

namespace PiBase

open Topology Filter Set Function TopologicalSpace

section Meta

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

theorem WellDefined.ultraconnectedSpace : WellDefined UltraconnectedSpace :=
  fun {X Y} _ _ φ h => Formal.P40.well_defined φ.some h

end Meta

end PiBase
