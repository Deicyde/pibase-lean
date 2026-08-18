module

public import PiBaseLean.AdditionalDefs.Meta
public import PiBaseLean.Properties.P71.Defs

@[expose] public section

namespace PiBase

open Topology Filter Set Function TopologicalSpace

section Meta

universe u

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

theorem Homeomorph.sigmaRelativelyCompactSpace [h : SigmaRelativelyCompactSpace X]
    (f : X ≃ₜ Y) : SigmaRelativelyCompactSpace Y :=
  Formal.P71.well_defined f h

theorem WellDefined.sigmaRelativelyCompactSpace : WellDefined SigmaRelativelyCompactSpace :=
  fun {_ _} _ _ h hX => Homeomorph.sigmaRelativelyCompactSpace h.some

end Meta

end PiBase
