module

public import PiBaseLean.AdditionalDefs.Meta
public import PiBaseLean.Properties.P120.Defs

@[expose] public section

namespace PiBase

open Topology Filter Set Function TopologicalSpace

section Meta

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

theorem Homeomorph.locallyOrderableSpace [h : LocallyOrderableSpace X] (f : X ≃ₜ Y) :
    LocallyOrderableSpace Y :=
  Formal.P120.well_defined f h

theorem WellDefined.locallyOrderableSpace : WellDefined LocallyOrderableSpace :=
  fun {_ _} _ _ h _ => Homeomorph.locallyOrderableSpace h.some

end Meta

end PiBase
