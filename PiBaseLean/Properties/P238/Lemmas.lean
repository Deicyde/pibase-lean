module

public import PiBaseLean.AdditionalDefs.Meta
public import PiBaseLean.Properties.P238.Defs

@[expose] public section

namespace PiBase

open Topology Filter Set Function TopologicalSpace

section Meta

universe u

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

theorem Homeomorph.hasRealTVSTopology [h : HasRealTVSTopology X] (f : X ≃ₜ Y) :
    HasRealTVSTopology Y :=
  Formal.P238.well_defined f h

theorem WellDefined.hasRealTVSTopology : WellDefined HasRealTVSTopology :=
  fun {_ _} _ _ h _ => Homeomorph.hasRealTVSTopology h.some

end Meta

end PiBase
