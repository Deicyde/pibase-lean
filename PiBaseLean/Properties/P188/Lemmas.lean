module

public import PiBaseLean.AdditionalDefs.Meta
public import PiBaseLean.Properties.P188.Defs

@[expose] public section

namespace PiBase

open Topology Filter Set Function TopologicalSpace

section Meta

universe u

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

theorem Homeomorph.continuumSpace [h : ContinuumSpace X] (f : X ≃ₜ Y) : ContinuumSpace Y :=
  Formal.P188.well_defined f h

theorem WellDefined.continuumSpace : WellDefined ContinuumSpace :=
  fun {_ _} _ _ h hX => Homeomorph.continuumSpace (h := hX) h.some

end Meta

end PiBase
