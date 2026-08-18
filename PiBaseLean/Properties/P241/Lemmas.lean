module

public import PiBaseLean.AdditionalDefs.Meta
public import PiBaseLean.Properties.P241.Defs

@[expose] public section

namespace PiBase

open Topology Filter Set Function TopologicalSpace

section Meta

universe u

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

theorem WellDefined.locallyEuclideanHalfLine : WellDefined LocallyEuclideanHalfLine :=
  fun {_ _} _ _ h hX => Formal.P241.well_defined h.some hX

end Meta

end PiBase
