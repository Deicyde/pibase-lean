module

public import PiBaseLean.AdditionalDefs.Meta
public import PiBaseLean.Properties.P140.Defs

@[expose] public section

namespace PiBase

open Topology Filter Set Function TopologicalSpace

section Meta

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

theorem Homeomorph.compactlyCoherentSpace [h : CompactlyCoherentSpace X] (f : X ≃ₜ Y) :
    CompactlyCoherentSpace Y :=
  Formal.P140.well_defined f h

theorem WellDefined.compactlyCoherentSpace : WellDefined CompactlyCoherentSpace :=
  fun {_ _} _ _ h _ => Homeomorph.compactlyCoherentSpace h.some

end Meta

end PiBase
