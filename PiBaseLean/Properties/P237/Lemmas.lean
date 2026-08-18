module

public import PiBaseLean.AdditionalDefs.Meta
public import PiBaseLean.Properties.P237.Defs

@[expose] public section

namespace PiBase

open Topology Filter Set Function TopologicalSpace

section Meta

universe u

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

theorem Homeomorph.topologicalNManifoldWithBoundary [h : TopologicalNManifoldWithBoundary X]
    (f : X ≃ₜ Y) : TopologicalNManifoldWithBoundary Y :=
  Formal.P237.well_defined f h

theorem WellDefined.topologicalNManifoldWithBoundary :
    WellDefined TopologicalNManifoldWithBoundary :=
  fun {_ _} _ _ h hX ↦ Homeomorph.topologicalNManifoldWithBoundary h.some

end Meta

end PiBase
