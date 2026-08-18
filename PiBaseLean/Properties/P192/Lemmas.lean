module

public import PiBaseLean.AdditionalDefs.Meta
public import PiBaseLean.Properties.P192.Defs

@[expose] public section

namespace PiBase

open Topology Filter Set Function TopologicalSpace

section Meta

universe u

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

theorem WellDefined.quasiSober : WellDefined QuasiSober :=
  fun {_ _} _ _ h hX => Formal.P192.well_defined h.some hX

end Meta

end PiBase
