module

public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Instances.Real.Lemmas

@[expose] public section

open Topology

namespace PiBase.Spaces
namespace S201

/- Space 201: Infinite earring.
See https://topology.pi-base.org/spaces/S000201.
The subspace of `ℝ × ℝ` (π-Base S176, Euclidean plane) consisting of the union, over
positive integers `n`, of the circle of radius `1/n` centered at `(1/n, 0)`. -/

/-- The carrier set: the union of circles of radius `1/n` centered at `(1/n, 0)`,
for `n` a positive integer. -/
def S201.carrier : Set (ℝ × ℝ) :=
  {p : ℝ × ℝ | ∃ n : ℕ, 0 < n ∧ (p.1 - 1 / n) ^ 2 + p.2 ^ 2 = (1 / (n : ℝ)) ^ 2}

/-- Infinite earring (pi-Base S201), a.k.a. the Hawaiian earring: the subspace of the
Euclidean plane `ℝ × ℝ` consisting of the union of circles of radius `1/n` centered
at `(1/n, 0)`, for positive integers `n`. -/
def S201 : Type := S201.carrier

instance : TopologicalSpace S201 := instTopologicalSpaceSubtype

end S201
end PiBase.Spaces
