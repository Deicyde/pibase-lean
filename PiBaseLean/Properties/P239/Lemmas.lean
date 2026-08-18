module

public import PiBaseLean.AdditionalDefs.Meta
public import PiBaseLean.Properties.P239.Defs

@[expose] public section

namespace PiBase

open Topology Filter Set Function TopologicalSpace

section Meta

universe u

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

theorem Homeomorph.semilocallyContractibleSpace [h : SemilocallyContractibleSpace X]
    (f : X ≃ₜ Y) : SemilocallyContractibleSpace Y :=
  Formal.P239.well_defined f h

theorem WellDefined.semilocallyContractibleSpace : WellDefined SemilocallyContractibleSpace :=
  fun {_ _} _ _ h hX => Homeomorph.semilocallyContractibleSpace h.some

end Meta

end PiBase
