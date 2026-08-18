module

public import PiBaseLean.AdditionalDefs.Meta
public import PiBaseLean.Properties.P175.Defs

@[expose] public section

namespace PiBase

open Topology Filter Set Function TopologicalSpace
open Cardinal

universe u

section Meta

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

theorem Homeomorph.cardGeThree [h : CardGeThree X] (f : X ≃ₜ Y) : CardGeThree Y where
  card_ge := by
    rw [← Cardinal.mk_congr f.toEquiv]
    exact h.card_ge

theorem WellDefined.cardGeThree : WellDefined fun X => CardGeThree X :=
  fun {_ _} _ _ h _ ↦ Homeomorph.cardGeThree h.some

end Meta

end PiBase
