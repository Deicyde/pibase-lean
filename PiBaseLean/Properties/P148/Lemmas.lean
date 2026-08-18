module

public import PiBaseLean.AdditionalDefs.Meta
public import PiBaseLean.Properties.P148.Defs

@[expose] public section

namespace PiBase

open Topology Filter Set Function TopologicalSpace

universe u

section Meta

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

theorem Homeomorph.cWGH [h : CWGH X] (f : X ≃ₜ Y) : CWGH Y :=
  Formal.P148.well_defined f h

theorem WellDefined.cWGH : WellDefined CWGH :=
  fun {_ _} _ _ h _ => Homeomorph.cWGH h.some

end Meta

end PiBase
