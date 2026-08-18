module

public import PiBaseLean.AdditionalDefs.Meta
public import PiBaseLean.Properties.P87.Defs

@[expose] public section

namespace PiBase

open Topology Filter Set Function TopologicalSpace

section Meta

universe u

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

theorem Homeomorph.hasGroupTopology [h : HasGroupTopology X] (f : X ≃ₜ Y) : HasGroupTopology Y :=
  Formal.P87.well_defined f h

theorem WellDefined.hasGroupTopology : WellDefined HasGroupTopology :=
  fun {_ _} _ _ h hX => Homeomorph.hasGroupTopology h.some

end Meta

end PiBase
