module

public import PiBaseLean.AdditionalDefs.Meta
public import PiBaseLean.Properties.P191.Defs

@[expose] public section

namespace PiBase

open Topology Filter Set Function TopologicalSpace

section Meta

universe u

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

theorem Homeomorph.hasGδSingletons [h : HasGδSingletons X] (f : X ≃ₜ Y) : HasGδSingletons Y :=
  Formal.P191.well_defined f h

theorem WellDefined.hasGδSingletons : WellDefined HasGδSingletons :=
  fun {_ _} _ _ h hX => Homeomorph.hasGδSingletons (h := hX) h.some

end Meta

end PiBase
