module

public import PiBaseLean.AdditionalDefs.Meta
public import PiBaseLean.Properties.P138.Defs

@[expose] public section

namespace PiBase

open Topology Filter Set Function TopologicalSpace

section Meta

universe u

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

theorem Homeomorph.countablyManyContinuousSelfMaps [h : CountablyManyContinuousSelfMaps X] (f : X ≃ₜ Y) :
    CountablyManyContinuousSelfMaps Y :=
  Formal.P138.well_defined f h

theorem WellDefined.countablyManyContinuousSelfMaps : WellDefined CountablyManyContinuousSelfMaps :=
  fun {_ _} _ _ h hX => Homeomorph.countablyManyContinuousSelfMaps h.some

end Meta

end PiBase
