module

public import PiBaseLean.AdditionalDefs.Meta
public import PiBaseLean.Properties.P95.Defs

@[expose] public section

namespace PiBase

open Topology Filter Set Function TopologicalSpace

section Meta

universe u

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

theorem Homeomorph.arcConnectedSpace [h : ArcConnectedSpace X] (f : X ≃ₜ Y) :
    ArcConnectedSpace Y :=
  Formal.P95.well_defined f h

theorem WellDefined.arcConnectedSpace : WellDefined ArcConnectedSpace :=
  fun {_ _} _ _ h _ => Homeomorph.arcConnectedSpace h.some

end Meta

end PiBase
