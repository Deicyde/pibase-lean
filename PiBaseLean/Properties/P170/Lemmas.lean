module

public import PiBaseLean.AdditionalDefs.Meta
public import PiBaseLean.Properties.P170.Defs

@[expose] public section

namespace PiBase

open Topology Filter Set Function TopologicalSpace

section Meta

universe u

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

theorem Homeomorph.k1T2Space [h : K1T2Space X] (f : X ≃ₜ Y) : K1T2Space Y :=
  Formal.P170.well_defined f h

theorem WellDefined.k1T2Space : WellDefined K1T2Space :=
  fun {_ _} _ _ h hX ↦ Formal.P170.well_defined h.some hX

end Meta

end PiBase
