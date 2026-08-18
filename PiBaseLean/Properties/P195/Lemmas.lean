module

public import PiBaseLean.AdditionalDefs.Meta
public import PiBaseLean.Properties.P195.Defs

@[expose] public section

namespace PiBase

open Topology Filter Set Function TopologicalSpace

section Meta

universe u

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

theorem Homeomorph.stoneSpace [h : StoneSpace X] (φ : X ≃ₜ Y) : StoneSpace Y :=
  Formal.P195.well_defined φ h

theorem WellDefined.stoneSpace : WellDefined StoneSpace :=
  fun {_ _} _ _ h _ => Homeomorph.stoneSpace h.some

end Meta

end PiBase
