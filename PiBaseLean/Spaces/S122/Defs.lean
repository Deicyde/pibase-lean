module

public import Mathlib.Topology.Order
public import Mathlib.Data.PNat.Basic
public import Mathlib.Data.Nat.Pairing
public import Mathlib.Logic.Equiv.List

public import PiBaseLean.Spaces.Bundled.Defs

@[expose] public section

open Topology

namespace PiBase.Spaces
namespace S122

/- Space 122: Gustin's sequence space.
See https://topology.pi-base.org/spaces/S000122.
Let `Y` be the finite sequences of positive integers of even length, and
`W` the 2-element subsets of `Y`. The carrier is `X = Y ⊕ (ℕ+ × W)`. For an
arbitrary-length finite sequence `α` and `β : Y`, write `β ⊇ᵢ α` when `β`
extends `α` by appending a (possibly empty) sequence all of whose entries
are `≥ i`; then `Uᵢ(α) = {β ∈ Y | β ⊇ᵢ α}` is the basic neighbourhood of a
sequence `α` in `Y`. Fixing any injective `q : ℕ+ × W → ℕ+` increasing in
its first coordinate, the basic neighbourhood of a point `(n, w) : ℕ+ × W`
is `Vᵢ(n, w) = {(n, w)} ∪ ⋃_{α ∈ w} Uᵢ(α ++ [q(n, w)])` (the union ranging
over the two elements `α` of the pair `w`). The topology is generated from
all these `Uᵢ(α)` and `Vᵢ(n, w)`. -/

/-- `Y`: the finite sequences of positive integers of even length. -/
def S122.Y : Type := {l : List ℕ+ // Even l.length}

/-- `W`: the 2-element subsets of `Y`. -/
def S122.W : Type := {s : Finset S122.Y // s.card = 2}

instance : Countable S122.Y := by
  unfold S122.Y; infer_instance

instance : Countable S122.W := by
  unfold S122.W; infer_instance

/-- Gustin's sequence space (pi-Base S122). Carrier `X = Y ⊕ (ℕ+ × W)`. -/
def S122 : Type := S122.Y ⊕ (ℕ+ × S122.W)

namespace S122

/-- `β ⊇ᵢ α`: `β` extends the (arbitrary-length) finite sequence `α` by
appending a sequence all of whose entries are `≥ i`. -/
def extendsFrom (i : ℕ+) (α : List ℕ+) (β : Y) : Prop :=
  ∃ γ : List ℕ+, (∀ x ∈ γ, i ≤ x) ∧ β.val = α ++ γ

/-- `Uᵢ(α)`: the basic neighbourhood, in `Y`, of the (arbitrary-length)
finite sequence `α`. -/
def U (i : ℕ+) (α : List ℕ+) : Set Y := {β : Y | extendsFrom i α β}

/-- Some fixed injection of `W` into `ℕ`, used to build the auxiliary
function `q` of the pi-Base definition. -/
noncomputable def code : W → ℕ := (Countable.exists_injective_nat W).choose

theorem code_injective : Function.Injective code :=
  (Countable.exists_injective_nat W).choose_spec

/-- A fixed injective function `q : ℕ+ × W → ℕ+`, increasing on its first
coordinate, as postulated by the pi-Base definition (built from `Nat.pair`
composed with the injection `code` of `W` into `ℕ`). -/
noncomputable def q (n : ℕ+) (w : W) : ℕ+ :=
  ⟨Nat.pair (n : ℕ) (code w) + 1, Nat.succ_pos _⟩

theorem q_injective : Function.Injective (fun p : ℕ+ × W => q p.1 p.2) := by
  rintro ⟨n₁, w₁⟩ ⟨n₂, w₂⟩ h
  have h' : Nat.pair (n₁ : ℕ) (code w₁) + 1 = Nat.pair (n₂ : ℕ) (code w₂) + 1 :=
    congrArg Subtype.val h
  obtain ⟨hn, hw⟩ := Nat.pair_eq_pair.mp (Nat.add_right_cancel h')
  have hw' : w₁ = w₂ := code_injective hw
  have hn' : n₁ = n₂ := PNat.coe_injective hn
  rw [hn', hw']

theorem q_strictMono_left (w : W) : StrictMono (fun n : ℕ+ => q n w) := by
  intro n₁ n₂ hlt
  simp only [q]
  exact Subtype.mk_lt_mk.mpr (Nat.add_lt_add_right (Nat.pair_lt_pair_left _ hlt) 1)

/-- `Vᵢ(n, w)`: the basic neighbourhood, in `X`, of the point `(n, w)`,
where `w = {α, β}` (a 2-element subset of `Y`); the union below ranges over
the (exactly two) elements `α` of `w`, matching `Uᵢ(αq(n,w)) ∪ Uᵢ(βq(n,w))`
from the pi-Base definition. -/
def V (i : ℕ+) (n : ℕ+) (w : W) : Set S122 :=
  {Sum.inr (n, w)} ∪ ⋃ α ∈ w.val, Sum.inl '' U i (α.val ++ [q n w])

instance : TopologicalSpace S122 :=
  TopologicalSpace.generateFrom
    ({s : Set S122 | ∃ i : ℕ+, ∃ α : List ℕ+, s = Sum.inl '' U i α} ∪
      {s : Set S122 | ∃ i : ℕ+, ∃ n : ℕ+, ∃ w : W, s = V i n w})

end S122

end S122
end PiBase.Spaces

namespace PiBase.Formal

/-- π-Base S122 as a bundled `Space` (carrier + topology). -/
noncomputable def S122 : Space := ⟨PiBase.Spaces.S122.S122, inferInstance⟩

end PiBase.Formal
