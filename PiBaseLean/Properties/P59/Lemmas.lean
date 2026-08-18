module

public import PiBaseLean.AdditionalDefs.Meta
public import PiBaseLean.Properties.P59.Defs

@[expose] public section

namespace PiBase

open Topology Filter Set Function TopologicalSpace
open Cardinal

section Meta

universe u

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

theorem Homeomorph.cardLePowerContinuum [h : CardLePowerContinuum X]
    (f : X ≃ₜ Y) : CardLePowerContinuum Y where
  card_le := by
    rw [← Cardinal.mk_congr f.toEquiv]
    exact h.card_le

theorem WellDefined.cardLePowerContinuum :
    WellDefined (fun (X : Type u) => CardLePowerContinuum X) :=
  fun {X Y} [TopologicalSpace X] [TopologicalSpace Y] h _ ↦
    Homeomorph.cardLePowerContinuum (X := X) h.some

end Meta

end PiBase
