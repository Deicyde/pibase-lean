module

public import PiBaseLean.AdditionalDefs.Meta
public import PiBaseLean.Properties.P194.Defs

@[expose] public section

namespace PiBase

open Topology Filter Set Function TopologicalSpace

section Meta

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

theorem Homeomorph.submetacompactSpace [h : SubmetacompactSpace X] (f : X ≃ₜ Y) :
    SubmetacompactSpace Y :=
  Formal.P194.well_defined f h

theorem WellDefined.submetacompactSpace : WellDefined SubmetacompactSpace :=
  fun {_ _} _ _ h _ => Homeomorph.submetacompactSpace h.some

end Meta

end PiBase
