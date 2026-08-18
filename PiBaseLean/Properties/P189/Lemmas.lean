module

public import PiBaseLean.AdditionalDefs.Meta
public import PiBaseLean.Properties.P189.Defs

@[expose] public section

namespace PiBase

open Topology Filter Set Function TopologicalSpace

section Meta

universe u

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

theorem Homeomorph.sigmaConnectedSpace [h : SigmaConnectedSpace X] (f : X ≃ₜ Y) :
    SigmaConnectedSpace Y :=
  Formal.P189.well_defined f h

theorem WellDefined.sigmaConnectedSpace : WellDefined SigmaConnectedSpace :=
  fun {_ _} _ _ h _ => Homeomorph.sigmaConnectedSpace h.some

end Meta

end PiBase
