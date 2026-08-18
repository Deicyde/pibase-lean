module

public import PiBaseLean.AdditionalDefs.Meta
public import PiBaseLean.Properties.P179.Defs

@[expose] public section

namespace PiBase

open Topology Filter Set Function TopologicalSpace

section Meta


variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

theorem WellDefined.alephZeroSpace : WellDefined AlephZeroSpace :=
  fun {_ _} _ _ h hX => PiBase.Formal.P179.well_defined h.some hX

end Meta

end PiBase
