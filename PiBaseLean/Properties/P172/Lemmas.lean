module

public import PiBaseLean.AdditionalDefs.Meta
public import PiBaseLean.Properties.P172.Defs

@[expose] public section

namespace PiBase

open Topology Filter Set Function TopologicalSpace

section Meta

universe u

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

theorem Homeomorph.radialSpace [h : RadialSpace X] (f : X ≃ₜ Y) : RadialSpace Y :=
  Formal.P172.well_defined f h

theorem WellDefined.radialSpace : WellDefined RadialSpace :=
  fun {_ _} _ _ h _ => Homeomorph.radialSpace h.some

end Meta

end PiBase
