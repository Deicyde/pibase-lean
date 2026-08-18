module

public import PiBaseLean.AdditionalDefs.Meta
public import PiBaseLean.Properties.P74.Defs

@[expose] public section

namespace PiBase

open Topology Filter Set Function TopologicalSpace

section Meta

universe u

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

theorem Homeomorph.cosmicSpace [h : CosmicSpace X] (φ : X ≃ₜ Y) : CosmicSpace Y :=
  Formal.P74.well_defined φ h

theorem WellDefined.cosmicSpace : WellDefined CosmicSpace :=
  fun {_ _} _ _ h _ => Homeomorph.cosmicSpace h.some

end Meta

end PiBase
