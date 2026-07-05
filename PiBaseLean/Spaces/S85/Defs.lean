module

public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.Order

@[expose] public section

open Topology

namespace PiBase.Spaces
namespace S85

/- Space 85: Line with uncountably many origins.
See https://topology.pi-base.org/spaces/S000085.
Quotient of `ℝ × S` (with `S` of cardinality `2^𝔠`, here `Set ℝ`) identifying `(x, α)` and
`(x, β)` whenever `x ≠ 0`; equivalently, `ℝ` with the origin replaced by one origin `0_α`
for each `α ∈ S`, each retaining the Euclidean neighborhood filter of `0` at `x ≠ 0`. -/

/-- The index set for the origins, of cardinality `2^𝔠`. -/
def S85Origins : Type := Set ℝ

/-- `S`, the index set of origins, carries the discrete topology (pi-Base's stated
construction: "a set `S` of cardinality `2^𝔠` with the discrete topology"). -/
instance : TopologicalSpace S85Origins := ⊥

/-- Identify `(x, α)` and `(x, β)` in `ℝ × S85Origins` whenever `x ≠ 0`
(and, trivially, identify a point with itself). -/
def S85Rel (p q : ℝ × S85Origins) : Prop := p.1 = q.1 ∧ (p.1 ≠ 0 ∨ p.2 = q.2)

/-- Line with uncountably many origins (pi-Base S85). -/
def S85 : Type := Quot S85Rel

instance : TopologicalSpace S85 :=
  TopologicalSpace.coinduced (Quot.mk S85Rel) instTopologicalSpaceProd

end S85
end PiBase.Spaces
