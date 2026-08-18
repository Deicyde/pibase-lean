module

public import PiBaseLean.AdditionalDefs.Meta
public import PiBaseLean.Properties.P136.Defs

@[expose] public section

namespace PiBase

open Topology Filter Set Function TopologicalSpace
universe u
section Meta
variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

theorem Homeomorph.anticompactSpace [h : AnticompactSpace X] (f : X ≃ₜ Y) : AnticompactSpace Y :=
  Formal.P136.well_defined f h

theorem WellDefined.anticompactSpace : WellDefined AnticompactSpace :=
  fun {_ _} _ _ h hX => Homeomorph.anticompactSpace h.some

end Meta

end PiBase
