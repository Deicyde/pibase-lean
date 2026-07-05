module

public import Mathlib.SetTheory.Cardinal.Aleph
public import Mathlib.Topology.Order

@[expose] public section

open Topology Ordinal

namespace PiBase.Spaces
namespace S177

/- Space 177: Misra's space E₀.
See https://topology.pi-base.org/spaces/S000177.
From A. Misra, "A topological view of P-spaces", Example 3.1 (doi:10.1016/0016-660X(72)90026-8):
a P-space of cardinality ℵ₁ on the point set {a, b} ∪ {c_γ : γ < ω₁} ∪ {a_αβ, b_αβ},
where every a_αβ, b_αβ is isolated and {a, b} ∪ {c_γ : γ < ω₁} is a discrete subspace;
it is T₂ and semiregular but not Urysohn (T2.5). -/

/-- The ω₁-indexed family of "background" points `c_γ` used in Misra's space `E₀`
(pi-Base S177), realized as the ordinals below the least uncountable ordinal `ω₁`. -/
def S177.COmega : Type 1 := {o : Ordinal.{0} // o < ω₁}

/-- The doubly-`ω₁`-indexed family of points `a_αβ` (and, reused, `b_αβ`) in Misra's
space `E₀` (pi-Base S177). -/
def S177.DoubleIndex : Type 1 := S177.COmega × S177.COmega

/-- The carrier of Misra's space `E₀` (pi-Base S177): the disjoint union of the two
distinguished points `a, b`, the family `{c_γ : γ < ω₁}`, and the two doubly-indexed
families `{a_αβ}` and `{b_αβ}`. -/
def S177 : Type 1 :=
  (PUnit.{2} ⊕ PUnit.{2}) ⊕ (S177.COmega ⊕ (S177.DoubleIndex ⊕ S177.DoubleIndex))

/-- **Faithfulness gap.** π-Base records (Example 3.1 of Misra's paper) that every
`a_αβ`/`b_αβ` is isolated and that `{a, b} ∪ {c_γ : γ < ω₁}` is a *discrete subspace*
of `E₀` -- but the actual neighbourhood filters that Misra assigns to `a`, `b`, and each
`c_γ` *within the ambient space* (the data that makes `E₀` a non-discrete P-space that is
semiregular but not Urysohn) are not reproduced in the available π-Base source data, only
cited to the (inaccessible) journal article. Asserting a specific such filter here would
risk fabricating Misra's construction, so this topology only encodes the one concretely
sourced fact -- that the doubly-indexed points are isolated -- via the generating set of
their singletons. This under-approximates the true topology of `E₀` (it does not yet make
`a`, `b`, or the `c_γ` isolated, nor build in the P-space/semiregular/non-Urysohn
structure); a complete, faithful topology needs the primary source. -/
instance : TopologicalSpace S177 :=
  TopologicalSpace.generateFrom
    {s : Set S177 | ∃ p : S177.DoubleIndex ⊕ S177.DoubleIndex, s = {Sum.inr (Sum.inr p)}}

end S177
end PiBase.Spaces
