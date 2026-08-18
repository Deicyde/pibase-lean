module

public import PiBaseLean.AdditionalDefs.Meta
public import PiBaseLean.Properties.P58.Defs

@[expose] public section

namespace PiBase

open Topology Filter Set Function TopologicalSpace
open Cardinal

section Meta

universe u

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

theorem Homeomorph.cardLtContinuum [h : CardLtContinuum X] (f : X ≃ₜ Y) :
    CardLtContinuum Y where
  card_lt := by
    rw [← Cardinal.mk_congr f.toEquiv]
    exact h.card_lt

theorem WellDefined.cardLtContinuum :
    WellDefined (fun (X : Type u) => CardLtContinuum X) :=
  fun {X Y} [TopologicalSpace X] [TopologicalSpace Y] h _ ↦
    Homeomorph.cardLtContinuum (X := X) h.some

end Meta

end PiBase
