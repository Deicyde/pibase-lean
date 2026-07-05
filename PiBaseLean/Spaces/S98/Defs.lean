module

public import Mathlib.Topology.Order

public import PiBaseLean.Spaces.Bundled.Defs

@[expose] public section

open Topology

namespace PiBase.Spaces
namespace S98

/- Space 98: Minimal Hausdorff topology.
See https://topology.pi-base.org/spaces/S000098.
Let `A` be the linearly ordered set `{1,2,3,…,ω,…,-3,-2,-1}` with the interval topology
(order type `ω + 1 + ω*`): a `false`-branch `1,2,3,…` increasing to `ω`, and a `true`-branch
`…,-3,-2,-1` decreasing away from `ω`, encoded here as `Bool × ℕ` (branch, distance from `ω`)
together with the point `ω` itself. Let `X = A × ℕ ∪ {a, -a}`, with two extra ideal points:
`a` has neighbourhoods `{a} ∪ {(i,j) : i < ω, j > n}` and `-a` has neighbourhoods
`{-a} ∪ {(i,j) : i > ω, j > n}`, for every `n`. We generate the topology on `X` directly from:
the singleton of every point of `A × ℕ` whose `A`-coordinate is not `ω` (each such point of `A`
is isolated in the order topology); the basic "cofinite on both tails" neighbourhoods of
`(ω, j)` for each `j`; and the basic neighbourhoods of `a` and of `-a` described above. -/

/-- The linearly ordered carrier `A = {1,2,3,…,ω,…,-3,-2,-1}` of Counterexample 100
(order type `ω + 1 + ω*`): `inl (s, n)` is the point at distance `n` from `ω` on branch `s`
(`false` = the increasing `1,2,3,…` branch, `true` = the `…,-3,-2,-1` branch), and `inr ()`
is the limit point `ω` itself. -/
def S98.A : Type := (Bool × ℕ) ⊕ Unit

/-- The point `ω` of `A`, the common limit of both branches. -/
def S98.A.omega : S98.A := Sum.inr ()

/-- Minimal Hausdorff topology (pi-Base S98). Carrier `X = A × ℕ ⊕ {a, -a}`,
with `Sum.inr false` playing the role of the ideal point `a` and `Sum.inr true` the ideal
point `-a`. -/
def S98 : Type := (S98.A × ℕ) ⊕ Bool

/-- The generating open sets of the minimal Hausdorff topology on `X`:
* the singleton of every ordinary point `((branch, n), j)` of `A × ℕ` with `A`-coordinate
  on a branch (i.e. not `ω`) — every such point of `A` is isolated in the order topology;
* for each `j n : ℕ`, the basic neighbourhood of `(ω, j)` consisting of `(ω, j)` together
  with all points `((s, k), j)` on either branch with `k > n` (cofinite on both tails,
  matching the order-interval neighbourhoods of `ω` in `A`);
* for each `n : ℕ`, the basic neighbourhood `M_n^+(a) = {a} ∪ {(i, j) : i < ω, j > n}` of the
  ideal point `a`, i.e. `{a}` together with every `((false, k), j)` with `j > n`;
* for each `n : ℕ`, the basic neighbourhood `M_n^-(-a) = {-a} ∪ {(i, j) : i > ω, j > n}` of the
  ideal point `-a`, i.e. `{-a}` together with every `((true, k), j)` with `j > n`. -/
def S98.generators : Set (Set S98) :=
  { s | ∃ (b : Bool) (n j : ℕ), s = {Sum.inl (Sum.inl (b, n), j)} } ∪
  { s | ∃ n j : ℕ, s = {Sum.inl (S98.A.omega, j)} ∪
      {p : S98 | ∃ (b : Bool) (k : ℕ), p = Sum.inl (Sum.inl (b, k), j) ∧ n < k} } ∪
  { s | ∃ n : ℕ, s = {Sum.inr false} ∪
      {p : S98 | ∃ (k j : ℕ), p = Sum.inl (Sum.inl (false, k), j) ∧ n < j} } ∪
  { s | ∃ n : ℕ, s = {Sum.inr true} ∪
      {p : S98 | ∃ (k j : ℕ), p = Sum.inl (Sum.inl (true, k), j) ∧ n < j} }

instance : TopologicalSpace S98 := TopologicalSpace.generateFrom S98.generators

end S98
end PiBase.Spaces

namespace PiBase.Formal

/-- π-Base S98 as a bundled `Space` (carrier + topology). -/
noncomputable def S98 : Space := ⟨PiBase.Spaces.S98.S98, inferInstance⟩

end PiBase.Formal
