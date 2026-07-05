module

public import Mathlib.Topology.Compactification.StoneCech

@[expose] public section

open Topology

namespace PiBase.Spaces
namespace S109

/- Space 109: Novak space.
See https://topology.pi-base.org/spaces/S000109.
The subspace $A_1 = \mathbb N \cup \{x_\xi\}$ of $\beta\mathbb N$ (π-Base S108, formalized
here as Mathlib's `StoneCech ℕ`) built by Novak's transfinite recursion: enumerate the
$2^{\mathfrak c}$ countably infinite subsets $S_\xi$ of $\beta\omega$, and recursively pick
distinct $x_\xi, y_\xi \in \overline{S_\xi}\setminus S_\xi$ so that the $x_\xi$'s and $y_\xi$'s
together partition $\beta\omega\setminus\omega$; then $X = \omega \cup \{x_\xi : \xi < \lambda\}$.

TODO: the carrier below is honestly incomplete. Constructing the actual point set requires
running Novak's transfinite recursion over the $2^{\mathfrak c}$ countable subsets of
`StoneCech ℕ` (well-ordering them, and at each step choosing fresh boundary points subject to a
global pairwise-disjointness/partition constraint) — a substantial standalone piece of set
theory that Mathlib does not package and that is not carried out in this file. What we *can*
state faithfully is the ambient space and the fact that the carrier is some subset `X` of
`StoneCech ℕ` containing (the image of) `ℕ`; we parametrize by an arbitrary such subset rather
than fabricating the specific Novak set, since presenting an unverified concrete choice as *the*
Novak carrier would misrepresent the construction. -/

variable (X : Set (StoneCech ℕ))

/-- The carrier of a subspace of `βℕ = StoneCech ℕ` cut out by a set `X`
(π-Base S109 is the specific such `X` produced by Novak's transfinite recursion;
see the TODO above — that specific set is not constructed here). -/
def S109 (X : Set (StoneCech ℕ)) : Type := X

instance : TopologicalSpace (S109 X) := inferInstanceAs (TopologicalSpace X)

end S109
end PiBase.Spaces
