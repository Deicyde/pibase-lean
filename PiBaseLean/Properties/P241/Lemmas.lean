module

public import PiBaseLean.AdditionalDefs.Meta
public import PiBaseLean.Properties.P241.Defs

@[expose] public section

namespace PiBase

open Topology Filter Set Function TopologicalSpace

section Meta

universe u

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

theorem Homeomorph.locallyEuclideanHalfLine [h : LocallyEuclideanHalfLine X] (f : X ≃ₜ Y) :
    LocallyEuclideanHalfLine Y :=
  Formal.P241.well_defined f h

theorem WellDefined.locallyEuclideanHalfLine : WellDefined LocallyEuclideanHalfLine :=
  fun {_ _} _ _ h hX ↦ Homeomorph.locallyEuclideanHalfLine h.some

end Meta

end PiBase
