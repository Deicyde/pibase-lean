module

public import Mathlib.Topology.Order

@[expose] public section

open Topology

namespace PiBase.Spaces
namespace S71

/- Space 71: Irregular lattice topology.
See https://topology.pi-base.org/spaces/S000071.
Carrier `X = A ∪ B ⊆ ℕ × ℕ`, where `A = {(i, k) : i > 0}` and `B = {(i, 0) : i ∈ ℕ}`
(so `X` omits only the points `(0, k)` with `k > 0`). Every point of `A` is declared
open; the point `(i, 0)` for `i > 0` has local basis `Uₙ(i) = {(i, k) : k = 0 ∨ k ≥ n}`;
the point `(0, 0)` has local basis `Vₙ = {(i, k) : (i, k) = (0, 0) ∨ (i ≥ n ∧ k ≥ n)}`. -/

/-- The carrier of the irregular lattice topology (pi-Base S71): the set
`A ∪ B ⊆ ℕ × ℕ` where `A = {(i, k) : i > 0}` and `B = {(i, 0) : i ∈ ℕ}`. -/
def S71 : Type :=
  ↥{p : ℕ × ℕ | 0 < p.1 ∨ p.2 = 0}

/-- The generating subbasis: singletons at points of `A` (`i > 0`), the local
basis `Uₙ(i) = {(i, k) : k = 0 ∨ k ≥ n}` at each point `(i, 0)` with `i > 0`, and
the local basis `Vₙ = {(i, k) : (i, k) = (0, 0) ∨ (i ≥ n ∧ k ≥ n)}` at `(0, 0)`. -/
instance : TopologicalSpace S71 :=
  TopologicalSpace.generateFrom
    ({s : Set S71 | ∃ a : S71, s = {a}} ∪
      {s : Set S71 | ∃ i : ℕ, 0 < i ∧ ∃ n : ℕ,
        s = {p : S71 | p.val.1 = i ∧ (p.val.2 = 0 ∨ n ≤ p.val.2)}} ∪
      {s : Set S71 | ∃ n : ℕ,
        s = {p : S71 | p.val = (0, 0) ∨ (n ≤ p.val.1 ∧ n ≤ p.val.2)}})

end S71
end PiBase.Spaces
