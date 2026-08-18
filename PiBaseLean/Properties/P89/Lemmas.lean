module

public import PiBaseLean.AdditionalDefs.Meta
public import PiBaseLean.Properties.P89.Defs

@[expose] public section

namespace PiBase

open Topology Filter Set Function TopologicalSpace

section Meta

universe u

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

theorem Homeomorph.fixedPointSpace [h : FixedPointSpace X] (f : X ≃ₜ Y) : FixedPointSpace Y :=
  Formal.P89.well_defined f h

theorem WellDefined.fixedPointSpace : WellDefined FixedPointSpace :=
  fun {_ _} _ _ h hX => Homeomorph.fixedPointSpace h.some

end Meta

end PiBase
