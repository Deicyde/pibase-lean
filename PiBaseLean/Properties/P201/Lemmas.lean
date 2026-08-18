module

public import PiBaseLean.AdditionalDefs.Meta
public import PiBaseLean.Properties.P201.Defs

@[expose] public section

namespace PiBase

open Topology Filter Set Function TopologicalSpace

section Meta

universe u

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

theorem Homeomorph.hasGenericPoint [h : HasGenericPoint X] (φ : X ≃ₜ Y) : HasGenericPoint Y :=
  Formal.P201.well_defined φ h

theorem WellDefined.hasGenericPoint : WellDefined HasGenericPoint :=
  fun {_ _} _ _ h _ => Homeomorph.hasGenericPoint h.some

end Meta

end PiBase
