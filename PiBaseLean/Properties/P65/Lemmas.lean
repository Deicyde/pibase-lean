module

public import PiBaseLean.AdditionalDefs.Meta
public import PiBaseLean.Properties.P65.Defs

@[expose] public section

namespace PiBase

open Topology Filter Set Function TopologicalSpace
open Cardinal

section Meta

universe u

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

theorem Homeomorph.cardEqContinuum [h : CardEqContinuum X] (f : X ≃ₜ Y) :
    CardEqContinuum Y where
  card_eq := by
    rw [← Cardinal.mk_congr f.toEquiv]
    exact h.card_eq

theorem WellDefined.cardEqContinuum :
    WellDefined (fun (X : Type u) => CardEqContinuum X) :=
  fun {X Y} [TopologicalSpace X] [TopologicalSpace Y] h _ ↦
    Homeomorph.cardEqContinuum (X := X) h.some

end Meta

end PiBase
