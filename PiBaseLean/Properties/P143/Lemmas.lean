module

public import PiBaseLean.AdditionalDefs.Meta
public import PiBaseLean.Properties.P143.Defs

@[expose] public section

namespace PiBase

open Topology Filter Set Function TopologicalSpace

universe u

section Meta

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

theorem Homeomorph.weakT2Space [h : WeakT2Space X] (f : X ≃ₜ Y) : WeakT2Space Y :=
  Formal.P143.well_defined f h

theorem WellDefined.weakT2Space : WellDefined WeakT2Space :=
  fun {_ _} _ _ h hX => Homeomorph.weakT2Space h.some

end Meta

end PiBase
