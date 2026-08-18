module

public import PiBaseLean.AdditionalDefs.Meta
public import PiBaseLean.Properties.P63.Defs

@[expose] public section

namespace PiBase

open Topology Filter Set Function TopologicalSpace

section Meta

universe u

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

theorem Homeomorph.cechCompleteSpace [h : CechCompleteSpace X] (f : X ≃ₜ Y) :
    CechCompleteSpace Y :=
  Formal.P63.well_defined f h

theorem WellDefined.cechCompleteSpace : WellDefined CechCompleteSpace :=
  fun {_ _} _ _ h hX => Formal.P63.well_defined h.some hX

end Meta

end PiBase
