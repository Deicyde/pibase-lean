module

public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.Compactness.Compact

public import PiBaseLean.Spaces.Bundled.Defs

@[expose] public section

open Topology Set

namespace PiBase.Spaces
namespace S127

/- Space 127: Pseudo-arc.
See https://topology.pi-base.org/spaces/S000127.
Pi-Base's own construction (see property P16 on this space): the pseudo-arc is the
intersection of a decreasing (nested) sequence of closed "chains" in ℝ², each of which
is closed and bounded and hence compact; it is topologized as a subspace of ℝ² (S176).
We encode "a nested sequence of nonempty compact chains in ℝ²" faithfully via the
hypotheses of Mathlib's Cantor-intersection theorem for sequences
(`IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed`), and fix one such
sequence by choice so that the resulting intersection is a genuine, nonempty, compact
subspace of ℝ².
TODO (INFEASIBLE GAP — read before using `S127` below): the genuine pseudo-arc requires a
specific sequence of "crooked" chains (each chain threading back and forth inside the
previous one) whose crookedness is exactly what forces the intersection to be
non-degenerate and hereditarily indecomposable. Constructing that crooked bonding data
faithfully is a substantial piece of continuum theory in its own right and is NOT
attempted here. `someChainSequence` below is only a type-correct placeholder witness (a
constant sequence of a single point) satisfying the *shape* of the definition (nested,
compact, closed, nonempty chains in ℝ²) — its intersection is a single point, i.e. it is
*not* the pseudo-arc (a point is degenerate and decomposable). `S127` is therefore a
faithful skeleton of pi-Base's construction, not a faithful copy of the pseudo-arc
itself. -/

/-- A nested sequence of nonempty, closed, compact "chains" in ℝ², in the shape used by
pi-Base's own construction of the pseudo-arc (P16: "the intersection of closed chains
in ℝ², each closed and bounded and thus compact"). -/
structure ChainSequence where
  /-- The `n`-th chain (a closed, bounded region of ℝ²). -/
  chain : ℕ → Set (ℝ × ℝ)
  nested : ∀ n, chain (n + 1) ⊆ chain n
  nonempty : ∀ n, (chain n).Nonempty
  isCompact_zero : IsCompact (chain 0)
  isClosed : ∀ n, IsClosed (chain n)

/-- A placeholder witnessing sequence of chains satisfying only the *shape* of pi-Base's
construction (nested, compact, closed, nonempty chains in ℝ²) — see the INFEASIBLE-GAP
TODO above. Its intersection is a single point, so it is NOT the pseudo-arc. -/
noncomputable def someChainSequence : ChainSequence :=
  ⟨fun _ => {(0, 0)}, fun _ => subset_rfl, fun _ => singleton_nonempty _,
    isCompact_singleton, fun _ => isClosed_singleton⟩

/-- Pseudo-arc (pi-Base S127). Skeleton only: the carrier is the intersection of a
nested sequence of closed, compact "chains" in ℝ² (a subspace of ℝ²), matching the
*shape* of pi-Base's construction — but the concrete chain sequence used
(`someChainSequence`) is a placeholder, not the genuine crooked pseudo-arc chains; see
the INFEASIBLE-GAP TODO above. -/
def S127 : Type := ⋂ n, someChainSequence.chain n

instance : TopologicalSpace S127 := instTopologicalSpaceSubtype

end S127
end PiBase.Spaces

namespace PiBase.Formal

/-- π-Base S127 as a bundled `Space` (carrier + topology). -/
noncomputable def S127 : Space := ⟨PiBase.Spaces.S127.S127, inferInstance⟩

end PiBase.Formal
