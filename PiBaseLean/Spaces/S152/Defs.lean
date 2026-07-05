module

public import Mathlib.Topology.Order

public import PiBaseLean.Spaces.Bundled.Defs

@[expose] public section

open Topology

namespace PiBase.Spaces
namespace S152

/- Space 152: Poset {-1, 0_a, 0_b} ∪ {1/n}_{n=1}^∞ with Alexandrov topology.
See https://topology.pi-base.org/spaces/S000152.
Carrier `X = {-1, 0_a, 0_b} ∪ {1/n}_{n=1}^∞`, encoded as an inductive type with
constructors `neg1`, `zeroA`, `zeroB`, and `frac n` (standing for the point `1/(n+1)`,
so `frac 0 = 1/1`, `frac 1 = 1/2`, ...). The order: `-1` is below everything, `0_a`
and `0_b` are incomparable to each other but each below every `1/n`, and the `1/n`
carry their usual real order (`1/(n+1) ≥ 1/(m+1) ↔ n ≤ m`). The Alexandrov topology
associated to this order has as open sets exactly the upper sets for `≤`; we generate
it from the principal up-sets of each point: `↑(-1) = X`, `↑0_a = {0_a} ∪ {1/n}`,
`↑0_b = {0_b} ∪ {1/n}`, and `↑(1/(n+1)) = {1/(m+1) : m ≤ n}` for each `n`. Arbitrary
unions of principal up-sets are exactly the up-sets, so this generates the Alexandrov
topology. -/

/-- The carrier of the poset `{-1, 0_a, 0_b} ∪ {1/n}_{n=1}^∞` (pi-Base S152):
`neg1` is `-1`, `zeroA`/`zeroB` are the two incomparable zeros `0_a`/`0_b`, and
`frac n` is the point `1/(n+1)`. -/
def S152 : Type := Bool ⊕ Bool ⊕ ℕ

namespace S152

/-- The point `-1`, the global minimum of the poset. -/
def neg1 : S152 := Sum.inl false

/-- The point `0_a`. -/
def zeroA : S152 := Sum.inl true

/-- The point `0_b`, incomparable to `0_a`. -/
def zeroB : S152 := Sum.inr (Sum.inl false)

/-- The point `1/(n+1)`. -/
def frac (n : ℕ) : S152 := Sum.inr (Sum.inr n)

/-- The principal up-set of `-1`: all of `X`, since `-1` is the minimum. -/
def upNeg1 : Set S152 := Set.univ

/-- The principal up-set of `0_a`: itself together with every `1/n`. -/
def upZeroA : Set S152 := {zeroA} ∪ Set.range frac

/-- The principal up-set of `0_b`: itself together with every `1/n`. -/
def upZeroB : Set S152 := {zeroB} ∪ Set.range frac

/-- The principal up-set of `1/(n+1)`: the finitely many `1/(m+1)` with `m ≤ n`
(i.e. with `1/(m+1) ≥ 1/(n+1)`), matching the usual order on `{1/n}`. -/
def upFrac (n : ℕ) : Set S152 := frac '' {m | m ≤ n}

/-- The generating family of open sets for the Alexandrov topology: the principal
up-set of every point of `X`. -/
def generators : Set (Set S152) :=
  {upNeg1, upZeroA, upZeroB} ∪ Set.range upFrac

end S152

instance : TopologicalSpace S152 := TopologicalSpace.generateFrom S152.generators

end S152
end PiBase.Spaces

namespace PiBase.Formal

/-- π-Base S152 as a bundled `Space` (carrier + topology). -/
noncomputable def S152 : Space := ⟨PiBase.Spaces.S152.S152, inferInstance⟩

end PiBase.Formal
