module

public import PiBaseLean.AdditionalDefs.Meta
public import PiBaseLean.Properties.P190.Defs

@[expose] public section

namespace PiBase

open Topology Filter Set Function TopologicalSpace

section Meta

universe u

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

theorem Homeomorph.ordinalSpace [OrdinalSpace X] (f : X ≃ₜ Y) : OrdinalSpace Y :=
  Formal.P190.well_defined f ‹_›

theorem WellDefined.ordinalSpace : WellDefined OrdinalSpace :=
  fun {_ _} _ _ h _ => Homeomorph.ordinalSpace h.some

end Meta

end PiBase
