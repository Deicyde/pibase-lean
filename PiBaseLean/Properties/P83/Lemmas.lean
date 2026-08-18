module

public import PiBaseLean.AdditionalDefs.Meta
public import PiBaseLean.Properties.P83.Defs

@[expose] public section

namespace PiBase

open Topology Filter Set Function TopologicalSpace

section Meta

universe u

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

theorem Homeomorph.metaLindelofSpace [h : MetaLindelofSpace X] (f : X ≃ₜ Y) : MetaLindelofSpace Y :=
  Formal.P83.well_defined f h

theorem WellDefined.metaLindelofSpace : WellDefined MetaLindelofSpace :=
  fun {_ _} _ _ h hX => Formal.P83.well_defined h.some hX

end Meta

end PiBase
