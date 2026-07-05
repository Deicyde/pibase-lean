module

public import Mathlib.Topology.Instances.Real.Lemmas

@[expose] public section

open Topology

namespace PiBase.Spaces
namespace S27

/- Space 27: Rational numbers ℚ.
See https://topology.pi-base.org/spaces/S000027.
Carrier `X = ℚ`, with the subspace topology induced from the Euclidean reals ℝ
(pi-Base S25) via the inclusion `(↑) : ℚ → ℝ`. -/

/-- Rational numbers ℚ (pi-Base S27), with the subspace topology from ℝ. -/
def S27 : Type := ℚ

instance : TopologicalSpace S27 :=
  TopologicalSpace.induced ((↑) : ℚ → ℝ) inferInstance

end S27
end PiBase.Spaces
