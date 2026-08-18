module

public import PiBaseLean.AdditionalDefs.Meta
public import PiBaseLean.Properties.P128.Defs

@[expose] public section

namespace PiBase

open Topology Filter Set Function TopologicalSpace

universe u

section Meta

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

theorem Homeomorph.kLindelofSpace [h : KLindelofSpace X] (f : X ≃ₜ Y) : KLindelofSpace Y :=
  Formal.P128.well_defined f h

theorem WellDefined.kLindelofSpace : WellDefined KLindelofSpace :=
  fun {_ _} _ _ h hX => Homeomorph.kLindelofSpace h.some

end Meta

end PiBase
