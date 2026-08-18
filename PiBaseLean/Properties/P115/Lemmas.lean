module

public import PiBaseLean.AdditionalDefs.Meta
public import PiBaseLean.Properties.P115.Defs

@[expose] public section

namespace PiBase

open Topology Filter Set Function TopologicalSpace

section Meta

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

theorem Homeomorph.subparacompactSpace [h : SubparacompactSpace X] (f : X ≃ₜ Y) : SubparacompactSpace Y :=
  Formal.P115.well_defined f h

theorem WellDefined.subparacompactSpace : WellDefined SubparacompactSpace :=
  fun {_ _} _ _ h _ => Homeomorph.subparacompactSpace h.some

end Meta

end PiBase
