module

public import Mathlib.Topology.Instances.Real.Lemmas

public import PiBaseLean.Spaces.Bundled.Defs

@[expose] public section

open Topology

namespace PiBase.Spaces
namespace S118

/- Space 118: Integer broom.
See https://topology.pi-base.org/spaces/S000118.
Carrier `X = ω × ({0} ∪ {1/n : n ≥ 1})` (points with "polar coordinates" `(n, θ)`).
The topology has as a basis all sets `U ×ˢ V` where `U` is open in the right order
(right-ray) topology on `ω` and `V` is open in `{0} ∪ {1/n : n ≥ 1} ⊂ ℝ` (subspace
topology). We generate the topology from exactly these box sets: `U` ranges over right
rays `{k : ω | a ≤ k}` (together with `∅` and `ω`), and `V` ranges over traces `W ∩ Y`
of opens `W` of `ℝ` on the second-coordinate set `Y = {0} ∪ {1/n : n ≥ 1}`. -/

/-- The second-coordinate set `Y = {0} ∪ {1/n : n ≥ 1} ⊂ ℝ` of the integer broom. -/
def S118.Y : Set ℝ := {0} ∪ {x : ℝ | ∃ n : ℕ, 0 < n ∧ x = 1 / (n : ℝ)}

/-- The carrier of the integer broom (pi-Base S118): pairs `(n, θ)` with `n : ω` and
`θ ∈ Y = {0} ∪ {1/n : n ≥ 1}`. -/
def S118 : Type := ℕ × S118.Y

/-- The generating box sets `U ×ˢ V`: `U` a right ray of `ω` (or `∅` / all of `ω`) and
`V` the trace on `Y` of an open set `W` of `ℝ`. -/
def S118.generators : Set (Set S118) :=
  { s | ∃ a : ℕ, ∃ W : Set ℝ, IsOpen W ∧
      s = {p : S118 | a ≤ p.1 ∧ (p.2 : ℝ) ∈ W} }

instance : TopologicalSpace S118 := TopologicalSpace.generateFrom S118.generators

end S118
end PiBase.Spaces

namespace PiBase.Formal

/-- π-Base S118 as a bundled `Space` (carrier + topology). -/
noncomputable def S118 : Space := ⟨PiBase.Spaces.S118.S118, inferInstance⟩

end PiBase.Formal
