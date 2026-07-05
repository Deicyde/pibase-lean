module

public import Mathlib.Topology.GDelta.Basic
public import Mathlib.Topology.Instances.Real.Lemmas

@[expose] public section

open Topology

namespace PiBase.Spaces
namespace S147

/- Space 147: (CH) A Luzin subset of the reals (the special Lusin set L).
See https://topology.pi-base.org/spaces/S000147.
A Luzin set is an uncountable `X ⊆ ℝ` whose intersection with every nowhere dense
subset of ℝ (equivalently, every meager subset of ℝ) is countable; the mere existence
of an uncountable Luzin set is independent of ZFC (it follows from CH, but is
consistently false, e.g. under MA + ¬CH), so we cannot exhibit a *specific* Luzin set
inside plain Mathlib (no `ContinuumHypothesis` axiom is available to invoke, nor would
we want to bake CH into this file as a global hypothesis). π-Base uses the CH
construction of Lemma 2.6 of Just–Miller–Scheepers–Szeptycki for this particular set L,
chosen so as to additionally guarantee the failure of the Rothberger property (S147
fails π-Base P150), unlike the generic Lusin set of S148. Faithfully to that
construction, we parametrize the carrier by an arbitrary `X : Set ℝ` together with
hypotheses that `X` is uncountable and meets every nowhere dense subset of ℝ in a
countable set, and topologize it as the subspace of ℝ. Any actual instantiation of `X`
still requires CH (or another hypothesis implying a Luzin set exists) to supply the
witness and the two hypotheses below; the extra Rothberger-failure trait distinguishing
L from the generic Lusin set is not itself encoded in the carrier (it would be a further
property of the specific witness `X`).
TODO: the specific point set from Lemma 2.6 of Just–Miller–Scheepers–Szeptycki (built by
a CH-length transfinite recursion enumerating the nowhere dense subsets of ℝ and
diagonalizing against them, with the extra bookkeeping needed to defeat Rothberger) is
not constructed here; only the shape of the defining Luzin property is captured, via the
hypotheses `huncountable` and `hcountable_inter`. -/

variable (X : Set ℝ) (huncountable : ¬ X.Countable)
  (hcountable_inter : ∀ Y : Set ℝ, IsNowhereDense Y → (X ∩ Y).Countable)

/-- The carrier of the special Lusin set L (pi-Base S147): an arbitrary set
`X : Set ℝ` satisfying the defining Luzin hypotheses `huncountable` and
`hcountable_inter` (see the TODO above — the specific CH-constructed set of
Just–Miller–Scheepers–Szeptycki, Lemma 2.6, is not built here). The hypotheses are
not used in the body (only `X` is needed to form the carrier type and its subspace
topology below); they are recorded as parameters purely to pin down which sets `X`
this definition is meant to be instantiated at. -/
def S147 (X : Set ℝ) (huncountable : ¬ X.Countable)
    (hcountable_inter : ∀ Y : Set ℝ, IsNowhereDense Y → (X ∩ Y).Countable) : Type := X

instance : TopologicalSpace (S147 X huncountable hcountable_inter) :=
  inferInstanceAs (TopologicalSpace X)

end S147
end PiBase.Spaces
