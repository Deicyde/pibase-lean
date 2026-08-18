module

public import PiBaseLean.AdditionalDefs.Meta
public import PiBaseLean.Properties.P100.Defs

@[expose] public section

namespace PiBase

open Topology Filter Set Function TopologicalSpace

section Meta

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

theorem Homeomorph.kcSpace [h : KcSpace X] (f : X ≃ₜ Y) : KcSpace Y :=
  Formal.P100.well_defined f h

theorem WellDefined.kcSpace : WellDefined KcSpace :=
  fun {_ _} _ _ h hX => Homeomorph.kcSpace h.some

end Meta

end PiBase
