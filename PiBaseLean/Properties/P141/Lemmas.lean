module

public import PiBaseLean.AdditionalDefs.Meta
public import PiBaseLean.Properties.P141.Defs

@[expose] public section

namespace PiBase

open Topology Filter Set Function TopologicalSpace

section Meta

universe u

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

theorem Homeomorph.compactlyGeneratedSpace [h : CompactlyGeneratedSpace X] (f : X ≃ₜ Y) :
    CompactlyGeneratedSpace Y :=
  Formal.P141.well_defined f h

theorem WellDefined.compactlyGeneratedSpace : WellDefined CompactlyGeneratedSpace :=
  fun {_ _} _ _ h _ => Homeomorph.compactlyGeneratedSpace h.some

end Meta

end PiBase
