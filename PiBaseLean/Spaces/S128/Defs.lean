module

public import Mathlib.Topology.Instances.CantorSet
public import Mathlib.Topology.Instances.Real.Lemmas

public import PiBaseLean.Spaces.Bundled.Defs

@[expose] public section

open Topology Set

namespace PiBase.Spaces
namespace S128

/- Space 128: Miller's biconnected set.
See https://topology.pi-base.org/spaces/S000128.
Pi-Base's own definition (marked `ambiguous_construction: true` in the source data): let
`C ⊂ [0,1]` be the Cantor set, `W = C × [0,1] ⊂ ℝ²`, and let `K` be an indecomposable
continuum with `K ∩ [0,1]² = W`. Inside `K` one then runs a transfinite recursion of
length `|ℝ|`, choosing a countable dense `Δ ⊂ K` and a set `M` built from a well-ordering
of the composants of `K`, the continua separating `K`, and the dense-in-a-square subsets
of `Δ`, so that `X = Δ ∪ M ⊂ ℝ²` carries the subspace topology.
"Indecomposable continuum" and "composant" have no Mathlib formalization, and the
recursive choice of `M` is exactly the part the source flags as ambiguous, so we cannot
encode `X` itself. We instead encode the one faithfully-statable, non-ambiguous fact
used to build it: `K` is a nonempty compact subset of ℝ² whose trace on the unit square
is `C × [0,1]`, fixed once by choice, and give it the subspace topology of ℝ² (S176),
matching pi-Base's "⊂ ℝ² ... with the subspace topology".
TODO: `K` is not shown connected or indecomposable (Mathlib has no continuum/composant
theory to state that with), and the composant/`Δ`/`M` recursion that actually carves
`X` out of `K` is not encoded — only a compact set with the right square-trace is. -/

/-- The trace pi-Base's continuum `K` must have on the unit square: the Cantor set
times the unit interval. -/
def biconnectedTrace : Set (ℝ × ℝ) := cantorSet ×ˢ Set.Icc (0 : ℝ) 1

/-- A nonempty compact subset of `ℝ²` whose intersection with `[0,1]²` is
`biconnectedTrace`, in the shape of pi-Base's continuum `K` (its connectedness and
indecomposability are not tracked here — see the module docstring). -/
structure ContinuumWitness where
  /-- The witnessed continuum, as a subset of `ℝ²`. -/
  carrier : Set (ℝ × ℝ)
  nonempty : carrier.Nonempty
  isCompact : IsCompact carrier
  trace_eq : carrier ∩ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1 = biconnectedTrace

/-- `biconnectedTrace` itself already satisfies the required shape (it is nonempty,
compact, and its own trace on `[0,1]²`), so a witness continuum always exists; we fix
one by choice, following the same pattern used for the pseudo-arc (S127). -/
noncomputable def someContinuumWitness : ContinuumWitness where
  carrier := biconnectedTrace
  nonempty := ⟨(0, 0), by simp [biconnectedTrace, zero_mem_cantorSet]⟩
  isCompact := isCompact_cantorSet.prod isCompact_Icc
  trace_eq := by
    apply Set.eq_of_subset_of_subset
    · exact fun p hp => hp.1
    · intro p hp
      refine ⟨hp, ?_, ?_⟩
      · exact cantorSet_subset_unitInterval hp.1
      · exact hp.2

/-- Miller's biconnected set (pi-Base S128), encoded as the ambient continuum witness
`K` fixed above (the `Δ ∪ M` carving described by pi-Base is not encoded — see the
module docstring), topologized as a subspace of `ℝ²`. -/
def S128 : Type := someContinuumWitness.carrier

instance S128_top : TopologicalSpace S128 := instTopologicalSpaceSubtype

end S128
end PiBase.Spaces

namespace PiBase.Formal

/-- π-Base S128 as a bundled `Space` (carrier + topology). -/
noncomputable def S128 : Space := ⟨PiBase.Spaces.S128.S128, PiBase.Spaces.S128.S128_top⟩

end PiBase.Formal
