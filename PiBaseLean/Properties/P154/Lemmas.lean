module

public import PiBaseLean.AdditionalDefs.Meta
public import PiBaseLean.Properties.P154.Defs

@[expose] public section

namespace PiBase

open Topology Filter Set Function TopologicalSpace

universe u

section Meta

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

theorem Homeomorph.goSpace [h : GoSpace X] (f : X ≃ₜ Y) : GoSpace Y :=
  Formal.P154.well_defined f h

theorem WellDefined.goSpace : WellDefined GoSpace :=
  fun {_ _} _ _ h hX => Homeomorph.goSpace h.some

end Meta

end PiBase
