module

public import Mathlib.Analysis.Convex.Segment
public import Mathlib.NumberTheory.Real.Irrational
public import Mathlib.Topology.Instances.CantorSet
public import Mathlib.Topology.Instances.Real.Lemmas

@[expose] public section

open Topology

namespace PiBase.Spaces
namespace S125

/- Space 125: Knaster-Kuratowski fan.
See https://topology.pi-base.org/spaces/S000125.
For `a ∈ [0,1]`, let `L(a)` be the segment from `(a, 0)` to the apex
`p = (1/2, 1/2)`. Let `C` be the middle-thirds Cantor set, `E` the (countable) set
of endpoints of its removed intervals -- i.e. the ternary-rational points of `C` --
and `F = C \ E`. The carrier is `A ∪ B ⊆ ℝ × ℝ`, where `A` consists of the points of
`L(c)` with rational second coordinate for `c ∈ E`, and `B` consists of the points of
`L(c)` with irrational second coordinate for `c ∈ F`; topologized as a subspace of
the plane `ℝ × ℝ` with its product topology. -/

/-- The endpoints of the removed intervals of the middle-thirds Cantor set: the
ternary-rational points of `cantorSet`. -/
def S125.cantorEndpoints : Set ℝ := {c ∈ cantorSet | ∃ (n : ℕ) (k : ℤ), c = k / 3 ^ n}

/-- The remaining points of the Cantor set (those with no finite ternary expansion). -/
def S125.cantorNonEndpoints : Set ℝ := cantorSet \ S125.cantorEndpoints

/-- The line segment `L(a)` from `(a, 0)` to the apex `(1/2, 1/2)`. -/
def S125.L (a : ℝ) : Set (ℝ × ℝ) := segment ℝ (a, (0 : ℝ)) ((1 : ℝ) / 2, (1 : ℝ) / 2)

/-- The rational-height part of the fan, built over the endpoints of the removed
Cantor intervals. -/
def S125.A : Set (ℝ × ℝ) :=
  {q : ℝ × ℝ | ∃ c ∈ S125.cantorEndpoints, q ∈ S125.L c ∧ ¬ Irrational q.2}

/-- The irrational-height part of the fan, built over the non-endpoint Cantor points. -/
def S125.B : Set (ℝ × ℝ) :=
  {q : ℝ × ℝ | ∃ c ∈ S125.cantorNonEndpoints, q ∈ S125.L c ∧ Irrational q.2}

/-- The carrier of the Knaster-Kuratowski fan. -/
def S125.carrier : Set (ℝ × ℝ) := S125.A ∪ S125.B

/-- The Knaster-Kuratowski fan, a.k.a. Cantor's leaky tent (pi-Base S125). -/
def S125 : Type := S125.carrier

instance : TopologicalSpace S125 := instTopologicalSpaceSubtype

end S125
end PiBase.Spaces
