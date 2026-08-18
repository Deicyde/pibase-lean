module

public import PiBaseLean.AdditionalDefs.Meta
public import PiBaseLean.Properties.P123.Defs

@[expose] public section

namespace PiBase

open Topology Filter Set Function TopologicalSpace

section Meta

universe u

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

theorem Homeomorph.locallyNEuclideanSpace [h : LocallyNEuclideanSpace X] (f : X ≃ₜ Y) :
    LocallyNEuclideanSpace Y :=
  Formal.P123.well_defined f h

theorem WellDefined.locallyNEuclideanSpace : WellDefined LocallyNEuclideanSpace :=
  fun {_ _} _ _ h hX ↦ Homeomorph.locallyNEuclideanSpace h.some

end Meta

end PiBase
