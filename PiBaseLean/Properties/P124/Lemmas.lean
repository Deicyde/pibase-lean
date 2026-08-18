module

public import PiBaseLean.AdditionalDefs.Meta
public import PiBaseLean.Properties.P124.Defs

@[expose] public section

namespace PiBase

open Topology Filter Set Function TopologicalSpace

section Meta

universe u

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

theorem Homeomorph.topologicalNManifold [h : TopologicalNManifold X] (f : X ≃ₜ Y) :
    TopologicalNManifold Y :=
  PiBase.Formal.P124.well_defined f h

theorem WellDefined.topologicalNManifold : WellDefined TopologicalNManifold :=
  fun {_ _} _ _ h hX ↦ Homeomorph.topologicalNManifold h.some

end Meta

end PiBase
