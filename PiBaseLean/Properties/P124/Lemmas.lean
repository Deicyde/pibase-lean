module

public import PiBaseLean.AdditionalDefs.Meta
public import PiBaseLean.Properties.P124.Defs

@[expose] public section

namespace PiBase

open Topology Filter Set Function TopologicalSpace

section Meta


variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

theorem WellDefined.topologicalNManifold : WellDefined TopologicalNManifold :=
  fun {_ _} _ _ h hX => PiBase.Formal.P124.well_defined h.some hX

end Meta

end PiBase
