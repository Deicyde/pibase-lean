module

public import PiBaseLean.AdditionalDefs.Meta
public import PiBaseLean.Properties.P236.Defs

@[expose] public section

namespace PiBase

open Topology Filter Set Function TopologicalSpace

section Meta

universe u

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

theorem Homeomorph.locallyNEuclideanHalfSpace [h : LocallyNEuclideanHalfSpace X] (f : X ≃ₜ Y) :
    LocallyNEuclideanHalfSpace Y :=
  Formal.P236.well_defined f h

theorem WellDefined.locallyNEuclideanHalfSpace : WellDefined LocallyNEuclideanHalfSpace :=
  fun {_ _} _ _ h hX ↦ Homeomorph.locallyNEuclideanHalfSpace h.some

end Meta

end PiBase
