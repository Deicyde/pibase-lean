module

public import PiBaseLean.AdditionalDefs.Meta
public import PiBaseLean.Properties.P122.Defs

@[expose] public section

namespace PiBase

open Topology Filter Set Function TopologicalSpace

section Meta

universe u

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

theorem Homeomorph.locallyEuclideanSpace [h : LocallyEuclideanSpace X] (f : X ≃ₜ Y) :
    LocallyEuclideanSpace Y :=
  Formal.P122.well_defined f h

theorem WellDefined.locallyEuclideanSpace : WellDefined LocallyEuclideanSpace :=
  fun {_ _} _ _ h hX ↦ Homeomorph.locallyEuclideanSpace h.some

end Meta

end PiBase
