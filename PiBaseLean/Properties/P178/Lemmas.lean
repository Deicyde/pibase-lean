module

public import PiBaseLean.AdditionalDefs.Meta
public import PiBaseLean.Properties.P178.Defs

@[expose] public section

namespace PiBase

open Topology Filter Set Function TopologicalSpace

section Meta

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

theorem Homeomorph.alephSpace [h : AlephSpace X] (f : X ≃ₜ Y) : AlephSpace Y :=
  Formal.P178.well_defined f h

theorem WellDefined.alephSpace : WellDefined AlephSpace :=
  fun {_ _} _ _ h _ => Homeomorph.alephSpace h.some

end Meta

end PiBase
