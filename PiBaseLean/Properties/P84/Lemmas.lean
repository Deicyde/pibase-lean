module

public import PiBaseLean.AdditionalDefs.Meta
public import PiBaseLean.Properties.P84.Defs

@[expose] public section

namespace PiBase

open Topology Filter Set Function TopologicalSpace

section Meta

universe u

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

theorem Homeomorph.locallyT2Space [h : LocallyT2Space X] (f : X ≃ₜ Y) : LocallyT2Space Y :=
  Formal.P84.well_defined f h

theorem WellDefined.locallyT2Space : WellDefined LocallyT2Space :=
  fun {_ _} _ _ h hX => Homeomorph.locallyT2Space h.some

end Meta

end PiBase
