module

public import PiBaseLean.AdditionalDefs.Meta
public import PiBaseLean.Properties.P177.Defs

@[expose] public section

namespace PiBase

open Topology Filter Set Function TopologicalSpace

section Meta

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

theorem Homeomorph.sigmaSpace [h : SigmaSpace X] (f : X ≃ₜ Y) : SigmaSpace Y :=
  Formal.P177.well_defined f h

theorem WellDefined.sigmaSpace : WellDefined SigmaSpace :=
  fun {_ _} _ _ h _ => Homeomorph.sigmaSpace h.some

end Meta

end PiBase
