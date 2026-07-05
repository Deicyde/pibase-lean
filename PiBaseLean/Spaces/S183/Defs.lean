module

public import Mathlib.Topology.Compactification.OnePoint.Basic
public import Mathlib.Data.Set.Countable
public import Mathlib.Data.Real.Basic

public import PiBaseLean.Spaces.Bundled.Defs

@[expose] public section

open Topology

namespace PiBase.Spaces
namespace S183

/- Space 183: KP Hart's non-sequentially discrete modified cocountable topology.
See https://topology.pi-base.org/spaces/S000183.
Carrier `X = Y ⊕ Z` with `Y = ℝ` (the pi-Base S17 carrier, cocountable topology) and
`Z = OnePoint ℕ` (the pi-Base S20 Fort-space carrier); the topology is the coarsest
one making `Z` a closed subspace of `X` (carrying its own `S20`/Fort topology) and
every countable subset of `Y` closed in `X`. -/

/-- KP Hart's non-sequentially discrete modified cocountable topology (pi-Base S183). -/
def S183 : Type := ℝ ⊕ OnePoint ℕ

/-- Subbasis: opens of `Z` (pulled back along `Sum.inr`, giving `Z` its own Fort
topology as a subspace), the set `Y` itself (so that `Z = Yᶜ` is closed), and
complements of `Sum.inl`-images of countable subsets of `Y` (so that every
countable subset of `Y` is closed in `X`). -/
instance S183_top : TopologicalSpace S183 :=
  TopologicalSpace.generateFrom
    ({ s : Set S183 | ∃ V : Set (OnePoint ℕ), IsOpen V ∧ s = Sum.inr '' V } ∪
      {Set.range (Sum.inl : ℝ → S183)} ∪
      { s : Set S183 | ∃ C : Set ℝ, C.Countable ∧ s = (Sum.inl '' C)ᶜ })

end S183
end PiBase.Spaces

namespace PiBase.Formal

/-- π-Base S183 as a bundled `Space` (carrier + topology). -/
noncomputable def S183 : Space := ⟨PiBase.Spaces.S183.S183, PiBase.Spaces.S183.S183_top⟩

end PiBase.Formal
