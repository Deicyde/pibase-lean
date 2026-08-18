module

public import PiBaseLean.AdditionalDefs.Meta
public import PiBaseLean.Properties.P36.Defs

@[expose] public section

namespace PiBase

open Topology Filter Set Function TopologicalSpace

section Meta

universe u

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

theorem WellDefined.preconnectedSpace : WellDefined PreconnectedSpace :=
  fun {X Y} _ _ φ _ => by
    constructor
    convert isPreconnected_range φ.some.continuous
    simp only [EquivLike.range_eq_univ]

theorem Homeomorph.preconnectedSpace [PreconnectedSpace X] (f : X ≃ₜ Y) : PreconnectedSpace Y :=
  WellDefined.preconnectedSpace ⟨f⟩ inferInstance

end Meta

end PiBase
