module

public import PiBaseLean.AdditionalDefs.Meta
public import PiBaseLean.Properties.P94.Defs

@[expose] public section

namespace PiBase

open Topology Filter Set Function TopologicalSpace

section Meta

universe u

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

theorem WellDefined.locallyFiniteSpace : WellDefined LocallyFiniteSpace :=
  fun {_ _} _ _ h hX => Formal.P94.well_defined h.some hX

end Meta

end PiBase
