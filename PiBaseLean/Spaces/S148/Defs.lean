module

public import Mathlib.Topology.GDelta.Basic
public import Mathlib.Topology.Instances.Real.Lemmas

@[expose] public section

open Topology

namespace PiBase.Spaces
namespace S148

/- Space 148: (CH) A Luzin subset of the reals (the generic Lusin set H).
See https://topology.pi-base.org/spaces/S000148.
A Luzin set is an uncountable `X ⊆ ℝ` whose intersection with every nowhere dense
subset of ℝ is countable; π-Base uses the CH construction of Theorem 2.13 of
Just–Miller–Scheepers–Szeptycki to guarantee this, since the mere existence of an
uncountable Luzin set is independent of ZFC (it follows from CH, but is consistently
false, e.g. under MA + ¬CH). We therefore cannot exhibit a *specific* Luzin set inside
plain Mathlib (no `ContinuumHypothesis` axiom is available to invoke, nor would we want
to bake CH into this file as a global hypothesis); instead, faithfully to π-Base's
"generic Lusin set", we parametrize the carrier by an arbitrary `X : Set ℝ` together
with hypotheses that `X` is uncountable and meets every nowhere dense subset of ℝ in a
countable set, and topologize it as the subspace of ℝ. Any actual instantiation of `X`
still requires CH (or another hypothesis implying a Luzin set exists) to supply the
witness and the two hypotheses below.
TODO: the specific point set from Theorem 2.13 of Just–Miller–Scheepers–Szeptycki (built
by a CH-length transfinite recursion enumerating the nowhere dense subsets of ℝ and
diagonalizing against them) is not constructed here; only the shape of the defining
property is captured, via the hypotheses `huncountable` and `hcountable_inter`. -/

variable (X : Set ℝ) (huncountable : ¬ X.Countable)
  (hcountable_inter : ∀ Y : Set ℝ, IsNowhereDense Y → (X ∩ Y).Countable)

/-- The carrier of a Luzin subset of the reals (pi-Base S148): an arbitrary set
`X : Set ℝ` satisfying the defining Luzin hypotheses `huncountable` and
`hcountable_inter` (see the TODO above — the specific CH-constructed set of
Just–Miller–Scheepers–Szeptycki, Theorem 2.13, is not built here). The hypotheses are
not used in the body (only `X` is needed to form the carrier type and its subspace
topology below); they are recorded as parameters purely to pin down which sets `X`
this definition is meant to be instantiated at. -/
def S148 (X : Set ℝ) (huncountable : ¬ X.Countable)
    (hcountable_inter : ∀ Y : Set ℝ, IsNowhereDense Y → (X ∩ Y).Countable) : Type := X

instance : TopologicalSpace (S148 X huncountable hcountable_inter) :=
  inferInstanceAs (TopologicalSpace X)

end S148
end PiBase.Spaces
