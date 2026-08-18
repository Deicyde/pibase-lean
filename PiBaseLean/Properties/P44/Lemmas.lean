module

public import PiBaseLean.AdditionalDefs.Meta
public import PiBaseLean.Properties.P44.Defs

@[expose] public section

namespace PiBase

open Topology Filter Set Function TopologicalSpace

universe u

section Meta

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

theorem Homeomorph.biconnectedSpace [h : BiconnectedSpace X] (f : X ≃ₜ Y) : BiconnectedSpace Y :=
  Formal.P44.well_defined f h

theorem WellDefined.biconnectedSpace : WellDefined BiconnectedSpace :=
  fun {_ _} _ _ h hX => Formal.P44.well_defined h.some hX

end Meta

end PiBase
