module

public import PiBaseLean.AdditionalDefs.Meta
public import PiBaseLean.Properties.P193.Defs

@[expose] public section

namespace PiBase

open Topology Filter Set Function TopologicalSpace

section Meta

universe u

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

theorem Homeomorph.shrinkingSpace [h : ShrinkingSpace X] (f : X ≃ₜ Y) : ShrinkingSpace Y :=
  Formal.P193.well_defined f h

theorem WellDefined.shrinkingSpace : WellDefined ShrinkingSpace :=
  fun {_ _} _ _ h hX => Formal.P193.well_defined h.some hX

end Meta

end PiBase
