module

public import PiBaseLean.AdditionalDefs.Meta
public import PiBaseLean.Properties.P145.Defs

@[expose] public section

namespace PiBase

open Topology Filter Set Function TopologicalSpace


section Meta

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

theorem WellDefined.stronglyParacompactSpace : WellDefined StronglyParacompactSpace :=
  fun {_ _} _ _ h hX => Formal.P145.well_defined h.some hX

end Meta

end PiBase
