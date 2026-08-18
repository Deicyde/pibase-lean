module

public import PiBaseLean.AdditionalDefs.Meta
public import PiBaseLean.Properties.P147.Defs

@[expose] public section

namespace PiBase

open Topology Filter Set Function TopologicalSpace

universe u

section Meta

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

theorem Homeomorph.pSpace [h : PSpace X] (f : X ≃ₜ Y) : PSpace Y :=
  Formal.P147.well_defined f h

theorem WellDefined.pSpace : WellDefined PSpace :=
  fun {_ _} _ _ h hX => Homeomorph.pSpace h.some

end Meta

end PiBase
