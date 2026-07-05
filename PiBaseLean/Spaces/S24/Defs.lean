module

public import Mathlib.Topology.Order
public import Mathlib.Data.Real.Basic

public import PiBaseLean.Spaces.Bundled.Defs

@[expose] public section

open Topology

namespace PiBase.Spaces
namespace S24

/- Space 24: Modified Fort space on ℝ.
See https://topology.pi-base.org/spaces/S000024.
Carrier `ℝ ⊕ Bool` (thought of as `ℝ ∪ {∞₁, ∞₂}` with `∞₁ = inr true` and
`∞₂ = inr false`); every point of ℝ is isolated, and the open neighborhoods
of each `∞ᵢ` are the cofinite subsets of the carrier containing that point. -/

/-- Modified Fort space on ℝ (pi-Base S24): the carrier is `ℝ ⊕ Bool`, i.e.
`ℝ ∪ {∞₁, ∞₂}` with the two extra points `∞₁ = Sum.inr true` and
`∞₂ = Sum.inr false`. -/
def S24 : Type := ℝ ⊕ Bool

/-- The generating open sets: every singleton of a real point, together with
every cofinite set containing `∞₁ = inr true`, together with every cofinite
set containing `∞₂ = inr false`. -/
instance : TopologicalSpace S24 :=
  TopologicalSpace.generateFrom
    ({s : Set (ℝ ⊕ Bool) | ∃ x : ℝ, s = {Sum.inl x}} ∪
      {s : Set (ℝ ⊕ Bool) | Sum.inr true ∈ s ∧ sᶜ.Finite} ∪
      {s : Set (ℝ ⊕ Bool) | Sum.inr false ∈ s ∧ sᶜ.Finite})

end S24
end PiBase.Spaces

namespace PiBase.Formal

/-- π-Base S24 as a bundled `Space` (carrier + topology). -/
noncomputable def S24 : Space := ⟨PiBase.Spaces.S24.S24, inferInstance⟩

end PiBase.Formal
