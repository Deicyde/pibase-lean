module

public import PiBaseLean.AdditionalDefs.Meta
public import PiBaseLean.Properties.P137.Defs

@[expose] public section

namespace PiBase

open Topology Filter Set Function TopologicalSpace

section Meta

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

theorem Homeomorph.isEmpty [IsEmpty X] (f : X ≃ₜ Y) : IsEmpty Y :=
  f.toEquiv.isEmpty_congr.mp ‹_›

theorem WellDefined.isEmpty : WellDefined (fun X => IsEmpty X) :=
  fun {_ _} _ _ h _ ↦ Homeomorph.isEmpty h.some

end Meta

end PiBase
