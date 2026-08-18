module

public import PiBaseLean.AdditionalDefs.Meta
public import PiBaseLean.Properties.P111.Defs

@[expose] public section

namespace PiBase

open Topology Filter Set Function TopologicalSpace

section Meta

universe u

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

theorem Homeomorph.hemicompactSpace [h : HemicompactSpace X] (f : X ≃ₜ Y) : HemicompactSpace Y :=
  Formal.P111.well_defined f h

theorem WellDefined.hemicompactSpace : WellDefined HemicompactSpace :=
  fun {_ _} _ _ h _ => Homeomorph.hemicompactSpace h.some

end Meta

end PiBase
