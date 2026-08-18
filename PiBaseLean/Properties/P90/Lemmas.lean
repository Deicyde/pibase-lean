module

public import PiBaseLean.AdditionalDefs.Meta
public import PiBaseLean.Properties.P90.Defs

@[expose] public section

namespace PiBase

open Topology Filter Set Function TopologicalSpace

section Meta

universe u

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

theorem Homeomorph.alexandrovDiscrete [h : AlexandrovDiscrete X] (f : X ≃ₜ Y) : AlexandrovDiscrete Y :=
  Formal.P90.well_defined f h

theorem WellDefined.alexandrovDiscrete : WellDefined AlexandrovDiscrete :=
  fun {_ _} _ _ h hX => Homeomorph.alexandrovDiscrete h.some

end Meta

end PiBase
