module

public import PiBaseLean.AdditionalDefs.Meta
public import PiBaseLean.Properties.P114.Defs

@[expose] public section

namespace PiBase

open Topology Filter Set Function TopologicalSpace

section Meta

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

theorem Homeomorph.cardEqAlephOne [h : CardEqAlephOne X] (f : X ≃ₜ Y) : CardEqAlephOne Y :=
  Formal.P114.well_defined f h

theorem WellDefined.cardEqAlephOne : WellDefined (fun (X : Type u) => CardEqAlephOne X) :=
  fun {_ _} _ _ h hX => Homeomorph.cardEqAlephOne h.some

end Meta

end PiBase
