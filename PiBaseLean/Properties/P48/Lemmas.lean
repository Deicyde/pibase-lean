module

public import PiBaseLean.AdditionalDefs.Meta
public import PiBaseLean.Properties.P48.Defs

@[expose] public section

namespace PiBase

open Topology Filter Set Function TopologicalSpace

section Meta

universe u

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

theorem Homeomorph.totallySeparatedSpace [h : TotallySeparatedSpace X] (f : X ≃ₜ Y) :
    TotallySeparatedSpace Y :=
  Formal.P48.well_defined f h

theorem WellDefined.totallySeparatedSpace : WellDefined TotallySeparatedSpace :=
  fun {_ _} _ _ h _ => Homeomorph.totallySeparatedSpace h.some

end Meta

end PiBase
