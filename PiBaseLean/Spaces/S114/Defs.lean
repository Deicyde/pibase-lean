module

public import Mathlib.Topology.Constructions
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

@[expose] public section

open Topology

namespace PiBase.Spaces
namespace S114

/- Space 114: Closed Topologist's Sine Curve.
See https://topology.pi-base.org/spaces/S000114.
The subset $X=\{(x, \sin(1/x)) : x \in (0,1]\} \cup \{(0,y) : y \in [-1,1]\}$ of
$\mathbb R \times \mathbb R$ (π-Base S176, with the product topology), with the
subspace topology. -/

/-- The closed topologist's sine curve (pi-Base S114): the graph of
`x ↦ sin (1 / x)` for `x ∈ (0, 1]`, together with the segment `{0} × [-1, 1]`,
as a subspace of `ℝ × ℝ`. -/
def S114 : Type :=
  {p : ℝ × ℝ // (0 < p.1 ∧ p.1 ≤ 1 ∧ p.2 = Real.sin (1 / p.1)) ∨ (p.1 = 0 ∧ p.2 ∈ Set.Icc (-1 : ℝ) 1)}

instance : TopologicalSpace S114 := instTopologicalSpaceSubtype

end S114
end PiBase.Spaces
