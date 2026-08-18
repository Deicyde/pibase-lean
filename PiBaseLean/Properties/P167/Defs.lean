module

public import Mathlib.Order.Filter.AtTopBot.Defs
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Homeomorph.Lemmas
public import PiBaseLean.Properties.Bundled.Defs

@[expose] public section

open Topology Set Function Filter TopologicalSpace

universe u

namespace PiBase

/- 167. Sequentially discrete -/
class SeqDiscreteSpace (X : Type u) [TopologicalSpace X] : Prop where
  tendsto_constant : ∀ᵉ (s : ℕ → X) (x : X), Tendsto s atTop (𝓝 x) → ∀ᶠ n in atTop, s n = x

end PiBase

namespace PiBase.Formal

def P167 : Property where
  toPred := SeqDiscreteSpace
  well_defined φ h := by
    constructor
    intro s y hy
    have h_tend : Tendsto (φ.symm ∘ s) atTop (𝓝 (φ.symm y)) :=
      (φ.symm.continuous.continuousAt (x := y)).tendsto.comp hy
    have h_ev := h.tendsto_constant (φ.symm ∘ s) (φ.symm y) h_tend
    exact h_ev.mono fun n hn => φ.symm.injective hn

end PiBase.Formal
