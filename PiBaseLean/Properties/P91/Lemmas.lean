module

public import PiBaseLean.AdditionalDefs.Meta
public import PiBaseLean.Properties.P91.Defs

@[expose] public section

namespace PiBase

open Topology Filter Set Function TopologicalSpace

section Meta

universe u

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

theorem Homeomorph.eberleinCompactSpace [h : EberleinCompactSpace X] (f : X ≃ₜ Y) :
    EberleinCompactSpace Y :=
  Formal.P91.well_defined f h

theorem WellDefined.eberleinCompactSpace : WellDefined EberleinCompactSpace :=
  fun {_ _} _ _ h _ => Homeomorph.eberleinCompactSpace h.some

end Meta

end PiBase
