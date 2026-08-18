module

public import PiBaseLean.AdditionalDefs.Meta
public import PiBaseLean.Properties.P223.Defs

@[expose] public section

namespace PiBase

open Topology Filter Set Function TopologicalSpace

section Meta

universe u

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

theorem Homeomorph.locallyContractibleSpace [h : LocallyContractibleSpace X]
    (f : X ≃ₜ Y) : LocallyContractibleSpace Y :=
  Formal.P223.well_defined f h

theorem WellDefined.locallyContractibleSpace : WellDefined LocallyContractibleSpace :=
  fun {_ _} _ _ h hX => Homeomorph.locallyContractibleSpace h.some

end Meta

end PiBase
