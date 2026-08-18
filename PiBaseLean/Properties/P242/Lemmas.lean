module

public import PiBaseLean.AdditionalDefs.Meta
public import PiBaseLean.Properties.P242.Defs

@[expose] public section

namespace PiBase

open Topology Filter Set Function TopologicalSpace

section Meta

universe u

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

theorem Homeomorph.weaklyContractibleSpace [h : WeaklyContractibleSpace X] (f : X ≃ₜ Y) :
    WeaklyContractibleSpace Y :=
  Formal.P242.well_defined f h

theorem WellDefined.weaklyContractibleSpace : WellDefined WeaklyContractibleSpace :=
  fun {_ _} _ _ h hX => Formal.P242.well_defined h.some hX

end Meta

end PiBase
