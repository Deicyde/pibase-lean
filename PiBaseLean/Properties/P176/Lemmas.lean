module

public import PiBaseLean.AdditionalDefs.Meta
public import PiBaseLean.Properties.P176.Defs

@[expose] public section

namespace PiBase

open Topology Filter Set Function TopologicalSpace
open Cardinal

universe u

section Meta

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

theorem Homeomorph.cardGeFour [h : CardGeFour X] (f : X ≃ₜ Y) : CardGeFour Y where
  card_ge := by
    rw [← Cardinal.mk_congr f.toEquiv]
    exact h.card_ge

theorem WellDefined.cardGeFour : WellDefined fun X => CardGeFour X :=
  fun {_ _} _ _ h _ ↦ Homeomorph.cardGeFour h.some

end Meta

end PiBase
