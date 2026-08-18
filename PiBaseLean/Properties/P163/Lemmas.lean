module

public import PiBaseLean.AdditionalDefs.Meta
public import PiBaseLean.Properties.P163.Defs
public import Mathlib.SetTheory.Cardinal.Continuum

@[expose] public section

namespace PiBase

open Topology Filter Set Function TopologicalSpace
open Cardinal

section Meta

universe u

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

theorem Homeomorph.cardLeContinuum [h : CardLeContinuum X] (f : X ≃ₜ Y) :
    CardLeContinuum Y where
  card_le := by
    rw [← Cardinal.mk_congr f.toEquiv]
    exact h.card_le

theorem WellDefined.cardLeContinuum :
    WellDefined (fun (X : Type u) => CardLeContinuum X) :=
  fun {X Y} [TopologicalSpace X] [TopologicalSpace Y] h _ ↦
    Homeomorph.cardLeContinuum (X := X) h.some

end Meta

end PiBase
