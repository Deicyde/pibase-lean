module

public import PiBaseLean.AdditionalDefs.Meta
public import PiBaseLean.Properties.P43.Defs

@[expose] public section

namespace PiBase

open Topology Filter Set Function TopologicalSpace

section Meta

universe u

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

theorem WellDefined.locallyInjPathConnectedSpace : WellDefined LocallyInjPathConnectedSpace :=
  fun {_ _} _ _ h hX => Formal.P43.well_defined h.some hX

end Meta

end PiBase
