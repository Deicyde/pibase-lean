module

public import PiBaseLean.AdditionalDefs.Meta
public import PiBaseLean.Properties.P235.Defs

@[expose] public section

namespace PiBase

open Topology Filter Set Function TopologicalSpace

section Meta

universe u

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

theorem Homeomorph.locallyEuclideanHalfSpace [h : LocallyEuclideanHalfSpace X] (f : X ≃ₜ Y) :
    LocallyEuclideanHalfSpace Y :=
  Formal.P235.well_defined f h

theorem WellDefined.locallyEuclideanHalfSpace : WellDefined LocallyEuclideanHalfSpace :=
  fun {_ _} _ _ h hX ↦ Homeomorph.locallyEuclideanHalfSpace h.some

end Meta

end PiBase
