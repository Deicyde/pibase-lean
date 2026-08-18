module

public import Mathlib.Order.Filter.AtTopBot.Defs
public import Mathlib.Topology.Defs.Filter
public import PiBaseLean.Properties.Bundled.Defs

@[expose] public section

open Topology Set Function Filter TopologicalSpace

namespace PiBase

/- 99. US -/
class UsSpace (X : Type*) [TopologicalSpace X] : Prop where
  us : ∀ (f : ℕ → X) (a b : X), Tendsto f atTop (𝓝 a) → Tendsto f atTop (𝓝 b) → a = b

end PiBase

namespace PiBase.Formal

def P99 : Property where
  toPred := UsSpace
  well_defined φ h := by
    constructor
    intro f a b ha hb
    have ha' : Filter.Tendsto (φ.symm ∘ f) Filter.atTop (𝓝 (φ.symm a)) :=
      (φ.symm.continuous.continuousAt (x := a)).tendsto.comp ha
    have hb' : Filter.Tendsto (φ.symm ∘ f) Filter.atTop (𝓝 (φ.symm b)) :=
      (φ.symm.continuous.continuousAt (x := b)).tendsto.comp hb
    have heq : φ.symm a = φ.symm b := h.us (φ.symm ∘ f) _ _ ha' hb'
    calc a = φ (φ.symm a) := (φ.apply_symm_apply a).symm
      _ = φ (φ.symm b) := by rw [heq]
      _ = b := φ.apply_symm_apply b

end PiBase.Formal
