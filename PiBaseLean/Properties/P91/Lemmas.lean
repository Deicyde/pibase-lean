module

public import PiBaseLean.AdditionalDefs.Meta
public import PiBaseLean.Properties.P91.Defs

@[expose] public section

namespace PiBase

open Topology Filter Set Function TopologicalSpace

section Meta

universe u

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

theorem WellDefined.eberleinCompactSpace : WellDefined EberleinCompactSpace :=
  fun {_ _} _ _ h hX => Formal.P91.well_defined h.some hX

end Meta

end PiBase
