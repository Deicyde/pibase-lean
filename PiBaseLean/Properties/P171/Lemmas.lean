module

public import PiBaseLean.AdditionalDefs.Meta
public import PiBaseLean.Properties.P171.Defs

@[expose] public section

namespace PiBase

open Topology Filter Set Function TopologicalSpace

section Meta

universe u

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

theorem Homeomorph.k2T2Space [h : K2T2Space X] (f : X ≃ₜ Y) : K2T2Space Y :=
  Formal.P171.well_defined f h

theorem WellDefined.k2T2Space : WellDefined K2T2Space :=
  fun {_ _} _ _ h hX => Formal.P171.well_defined h.some hX

end Meta

end PiBase
