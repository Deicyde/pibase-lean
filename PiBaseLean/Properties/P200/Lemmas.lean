module

public import PiBaseLean.Properties.P200.Defs
public import PiBaseLean.AdditionalDefs.Meta

@[expose] public section

namespace PiBase

open Topology Filter

variable (X : Type*) [TopologicalSpace X]

/-- A nonempty, pre simply connected space is connected. -/
instance instSimplyConnectedSpaceOfPresimplyConnectedSpaceOfNonempty [h : PresimplyConnectedSpace X]
    [h' : Nonempty X] : SimplyConnectedSpace X := by
  rcases h.presimplyconnected with h|h
  · infer_instance
  · exact h

/-- A nonempty, pre simply connected space is connected. -/
example [h : PresimplyConnectedSpace X]
    [h' : Nonempty X] : SimplyConnectedSpace X := by
  rcases h.presimplyconnected with h|h
  · infer_instance
  · exact h

/-- A simply connected space is pre simply connected. -/
theorem SimplyConnectedSpace.presimplyConnectedSpace [h : SimplyConnectedSpace X] :
    PresimplyConnectedSpace X where
  presimplyconnected := .inr h

section Meta

universe u

theorem Homeomorph.presimplyConnectedSpace {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    [h : PresimplyConnectedSpace X] (φ : X ≃ₜ Y) : PresimplyConnectedSpace Y :=
  Formal.P200.well_defined φ h

theorem WellDefined.presimplyConnectedSpace : WellDefined PresimplyConnectedSpace :=
  fun {_ _} _ _ h _ => Homeomorph.presimplyConnectedSpace h.some

end Meta

end PiBase
