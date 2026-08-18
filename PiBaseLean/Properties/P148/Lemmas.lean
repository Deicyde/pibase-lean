module

public import PiBaseLean.AdditionalDefs.Meta
public import PiBaseLean.Properties.P148.Defs

@[expose] public section

namespace PiBase

open Topology Filter Set Function TopologicalSpace

universe u

section Meta

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

theorem WellDefined.cWGH : WellDefined CWGH :=
  fun {_ _} _ _ h hX => Formal.P148.well_defined h.some hX

end Meta

end PiBase
