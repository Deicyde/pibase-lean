module

public import PiBaseLean.AdditionalDefs.Meta
public import PiBaseLean.Properties.P142.Defs

@[expose] public section

namespace PiBase

open Topology Filter Set Function TopologicalSpace

section Meta

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

theorem Homeomorph.k3Space [h : K3Space X] (f : X ≃ₜ Y) : K3Space Y :=
  Formal.P142.well_defined f h

theorem WellDefined.k3Space : WellDefined K3Space :=
  fun {_ _} _ _ h _ => Homeomorph.k3Space h.some

end Meta

end PiBase
