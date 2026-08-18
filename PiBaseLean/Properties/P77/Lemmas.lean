module

public import PiBaseLean.AdditionalDefs.Meta
public import PiBaseLean.Properties.P77.Defs

@[expose] public section

namespace PiBase

open Topology Filter Set Function TopologicalSpace

section Meta

universe u

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

theorem Homeomorph.corsonCompactSpace [h : CorsonCompactSpace X] (f : X ≃ₜ Y) :
    CorsonCompactSpace Y :=
  Formal.P77.well_defined f h

theorem WellDefined.corsonCompactSpace : WellDefined CorsonCompactSpace :=
  fun {_ _} _ _ h _ => Homeomorph.corsonCompactSpace h.some

end Meta

end PiBase
