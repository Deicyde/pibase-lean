module

public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.Constructions.SumProd

public import PiBaseLean.Spaces.Bundled.Defs

@[expose] public section

open Topology

namespace PiBase.Spaces
namespace S143

/- Space 143: Butterfly space.
See https://topology.pi-base.org/spaces/S000143.
Carrier `X = ℝ × [0, ∞)`, the closed upper half plane. Points above the x-axis keep
their usual Euclidean neighborhoods; a boundary point `p = (p_x, 0)` gets the
"butterfly neighborhoods" `N_ε(p) = {p} ∪ {q ∈ X : ‖q - p‖ < ε and q_y < ε|q_x - p_x|}`
as a local base, for `ε > 0` (the points strictly under the two rays of slope `±ε`
emanating from `p`, within distance `ε` of `p`). -/

/-- The closed upper half plane `X = {(x, y) ∈ ℝ² : y ≥ 0}`, carrier of the
Butterfly space (pi-Base S143). -/
def S143 : Type := {p : ℝ × ℝ // 0 ≤ p.2}

/-- The generating subbasis for the Butterfly topology: Euclidean-open subsets of the
open upper half plane (giving interior points their usual Euclidean neighborhoods),
together with, for each boundary point `p = (p_x, 0)` and each `ε > 0`, the butterfly
neighborhood `N_ε(p) = {p} ∪ {q : (q_x - p_x)^2 + q_y^2 < ε^2 ∧ q_y < ε|q_x - p_x|}`. -/
def S143.subbasis : Set (Set S143) :=
  {s | ∃ U : Set (ℝ × ℝ), IsOpen U ∧ s = {p : S143 | p.1 ∈ U ∧ 0 < p.1.2}} ∪
  {s | ∃ (px ε : ℝ), 0 < ε ∧
    s = insert (⟨(px, 0), le_refl 0⟩ : S143)
      {q : S143 | (q.1.1 - px) ^ 2 + q.1.2 ^ 2 < ε ^ 2 ∧ q.1.2 < ε * |q.1.1 - px|}}

instance : TopologicalSpace S143 := TopologicalSpace.generateFrom S143.subbasis

end S143
end PiBase.Spaces

namespace PiBase.Formal

/-- π-Base S143 as a bundled `Space` (carrier + topology). -/
noncomputable def S143 : Space := ⟨PiBase.Spaces.S143.S143, inferInstance⟩

end PiBase.Formal
