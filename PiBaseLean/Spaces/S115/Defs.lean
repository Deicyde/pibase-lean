module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

@[expose] public section

open Topology

namespace PiBase.Spaces
namespace S115

/- Space 115: Extended topologist's sine curve.
See https://topology.pi-base.org/spaces/S000115.
The subspace of ℝ² given by {(x, sin(1/x)) : x ∈ (0,1]} ∪ {(0,y) : y ∈ [-1,1]} ∪
{(x,1) : x ∈ [0,1]}, with the subspace topology inherited from ℝ². -/

/-- The carrier set of the extended topologist's sine curve, as a subset of `ℝ × ℝ`. -/
def S115Set : Set (ℝ × ℝ) :=
  {p : ℝ × ℝ | 0 < p.1 ∧ p.1 ≤ 1 ∧ p.2 = Real.sin (1 / p.1)} ∪
  {p : ℝ × ℝ | p.1 = 0 ∧ -1 ≤ p.2 ∧ p.2 ≤ 1} ∪
  {p : ℝ × ℝ | 0 ≤ p.1 ∧ p.1 ≤ 1 ∧ p.2 = 1}

/-- Extended topologist's sine curve (pi-Base S115). -/
def S115 : Type := S115Set

instance : TopologicalSpace S115 := inferInstanceAs (TopologicalSpace S115Set)

end S115
end PiBase.Spaces
