module

public import PiBaseLean.AdditionalDefs.Meta
public import PiBaseLean.Properties.P168.Defs

@[expose] public section

namespace PiBase

open Topology Filter Set Function TopologicalSpace

section Meta

universe u

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

theorem Homeomorph.countableSetsDiscrete [h : CountableSetsDiscrete X]
    (f : X ≃ₜ Y) : CountableSetsDiscrete Y :=
  Formal.P168.well_defined f h

theorem WellDefined.countableSetsDiscrete : WellDefined CountableSetsDiscrete :=
  fun {_ _} _ _ h hX => Formal.P168.well_defined h.some hX

end Meta

end PiBase
