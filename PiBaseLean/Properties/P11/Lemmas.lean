module

public import PiBaseLean.AdditionalDefs.Meta
public import PiBaseLean.Properties.P11.Defs

@[expose] public section

namespace PiBase

open Topology Filter Set Function TopologicalSpace

section Meta

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

theorem Homeomorph.regularSpace [RegularSpace X] (f : X ≃ₜ Y) : RegularSpace Y :=
  f.symm.isInducing.regularSpace

theorem WellDefined.regularSpace : WellDefined RegularSpace :=
  fun {_ _} _ _ h _ => Homeomorph.regularSpace h.some

end Meta

end PiBase
