module

public import Mathlib.Topology.Order

public import PiBaseLean.Spaces.Bundled.Defs

@[expose] public section

open Topology

namespace PiBase.Spaces
namespace S161

/- Space 161: Van Douwen's anti-Hausdorff Fréchet space.
See https://topology.pi-base.org/spaces/S000161.
The carrier is `ω` (the natural numbers). π-Base cites only "the topology on `ω`
constructed by Eric K. van Douwen in Section 5 of [his 1993 paper 'An anti-Hausdorff
Fréchet space in which convergent sequences have unique limits', Topology and its
Applications, doi:10.1016/0166-8641(93)90147-6]" -- it does not itself spell out the
open sets, and that paper's text is not available in this project's source data (only
the π-Base stub above and the asserted-property list: it is anti-Hausdorff/not T₂ (P16),
not T₁ (P39), Fréchet in the paper's terminology (P80), sequential (P99), and countable
(P181, by definition of `ω`)). Van Douwen's Section 5 construction is a specific,
nontrivial combinatorial topology (built by a recursion selecting, for each `n : ω`, a
carefully chosen filter/neighbourhood scheme on `ω` so that sequences converge but limits
can fail to be unique) that cannot be reconstructed faithfully from this stub alone.
TODO: the actual open sets from Section 5 of van Douwen's paper are not reproduced here;
only the carrier `ω` is captured faithfully, together with the coarsest honest topology
we can justify without the source (the indiscrete topology `⊤`, under which every point
is topologically indistinguishable from every other -- consistent with, but not a proof
of, the paper's anti-Hausdorff/non-T₁ conclusion; it is NOT claimed to be Fréchet (P80),
which is a genuine content fact about van Douwen's specific construction that this stub
does not attempt to reprove). Replace this with the real generateFrom subbasis if/when
the paper's construction is transcribed into the source data. -/

/-- Van Douwen's anti-Hausdorff Fréchet space (pi-Base S161), carrier only:
the underlying set is `ω` (the natural numbers). -/
def S161 : Type := ℕ

/-- TODO: placeholder topology only -- see the module docstring. The real topology is
van Douwen's specific Section 5 construction on `ω`, not reproduced here. -/
instance S161_top : TopologicalSpace S161 := ⊤

end S161
end PiBase.Spaces

namespace PiBase.Formal

/-- π-Base S161 as a bundled `Space` (carrier + topology). -/
noncomputable def S161 : Space := ⟨PiBase.Spaces.S161.S161, PiBase.Spaces.S161.S161_top⟩

end PiBase.Formal
