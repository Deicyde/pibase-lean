module

public import PiBaseLean.AdditionalDefs.Meta
public import PiBaseLean.Properties.P179.Defs

@[expose] public section

namespace PiBase

open Topology Filter Set Function TopologicalSpace

section Meta

universe u

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

theorem Homeomorph.alephZeroSpace [AlephZeroSpace X] (f : X ≃ₜ Y) : AlephZeroSpace Y :=
  PiBase.Formal.P179.well_defined f ‹_›

theorem WellDefined.alephZeroSpace : WellDefined AlephZeroSpace :=
  fun {_ _} _ _ h _ ↦ Homeomorph.alephZeroSpace h.some

end Meta

end PiBase
