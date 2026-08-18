module

public import PiBaseLean.AdditionalDefs.Meta
public import PiBaseLean.Properties.P224.Defs

@[expose] public section

namespace PiBase

open Topology Filter Set Function TopologicalSpace

section Meta

universe u

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

theorem Homeomorph.weaklyLocallyContractibleSpace [h : WeaklyLocallyContractibleSpace X]
    (f : X ≃ₜ Y) : WeaklyLocallyContractibleSpace Y :=
  Formal.P224.well_defined f h

theorem WellDefined.weaklyLocallyContractibleSpace : WellDefined WeaklyLocallyContractibleSpace :=
  fun {_ _} _ _ h hX => Homeomorph.weaklyLocallyContractibleSpace h.some

end Meta

end PiBase

