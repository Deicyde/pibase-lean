module

public import PiBaseLean.AdditionalDefs.Meta
public import PiBaseLean.Properties.P232.Defs

@[expose] public section

namespace PiBase

open Topology Filter Set Function TopologicalSpace

section Meta

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

theorem Homeomorph.lC1 (f : X ≃ₜ Y) [LC1 X] : LC1 Y :=
  lC1_of_homeomorph f inferInstance

theorem WellDefined.lC1 : WellDefined LC1 :=
  fun {_ _} _ _ h _ => Homeomorph.lC1 h.some

end Meta

end PiBase
