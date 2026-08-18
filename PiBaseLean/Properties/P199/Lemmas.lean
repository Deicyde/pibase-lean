module

public import PiBaseLean.AdditionalDefs.Meta
public import PiBaseLean.Properties.P199.Defs

@[expose] public section

namespace PiBase

open Topology Filter Set Function TopologicalSpace

section Meta

universe u

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

theorem Homeomorph.contractibleSpace [h : ContractibleSpace X] (φ : X ≃ₜ Y) :
    ContractibleSpace Y :=
  Formal.P199.well_defined φ h

theorem WellDefined.contractibleSpace : WellDefined ContractibleSpace :=
  fun {_ _} _ _ h _ => Homeomorph.contractibleSpace h.some

end Meta

end PiBase
