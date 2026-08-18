module

public import PiBaseLean.AdditionalDefs.Meta
public import PiBaseLean.Properties.P86.Defs

@[expose] public section

namespace PiBase

open Topology Filter Set Function TopologicalSpace

section Meta

universe u

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

theorem Homeomorph.homogeneousSpace [h : HomogeneousSpace X] (f : X ≃ₜ Y) : HomogeneousSpace Y :=
  Formal.P86.well_defined f h

theorem WellDefined.homogeneousSpace : WellDefined HomogeneousSpace :=
  fun {_ _} _ _ h hX => Homeomorph.homogeneousSpace h.some

end Meta

end PiBase
