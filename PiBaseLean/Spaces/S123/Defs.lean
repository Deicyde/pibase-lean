module

public import Mathlib.Topology.Order
public import Mathlib.Data.Rat.Cast.Defs
public import Mathlib.Data.Nat.Nth
public import Mathlib.Data.Nat.Prime.Defs

@[expose] public section

open Topology

namespace PiBase.Spaces
namespace S123

/- Space 123: Roy's lattice space.
See https://topology.pi-base.org/spaces/S000123.
Let `p i = Nat.nth Nat.Prime i` enumerate the primes, and let `C i` be the rationals of
the form `a / (p i) ^ n` with `a : ℤ` not divisible by `p i` (the `C i` are disjoint dense
subsets of `ℚ`). Carrier `X = {(r, i) : ℚ × ℕ | r ∈ C i} ∪ {ω}`, represented as
`Option ↥{p : ℚ × ℕ | p.1 ∈ S123.C p.2}` (`ω := none`). Basic neighborhoods: at a point
`(r, 2n)` on an even level, the interval `U_ε(r,2n) = {(t,2n) | |r-t| < ε}` (staying on
that single level); at a point `(r, 2n-1)` on an odd level, the "lattice" set
`V_ε(r,2n-1) = {(t,m) | |r-t| < ε, |m-n| ≤ 1}` (spreading to the two adjacent levels);
at `ω`, the tail sets `W_n(ω) = {(s,i) | i ≥ 2n} ∪ {ω}`. -/

/-- The `i`-th prime, `p i` (pi-Base S123). -/
noncomputable def S123.p (i : ℕ) : ℕ := Nat.nth Nat.Prime i

/-- The disjoint dense subset `C i ⊆ ℚ` of rationals `a / (p i) ^ n` with `a : ℤ` not
divisible by the `i`-th prime `p i` (pi-Base S123). -/
def S123.C (i : ℕ) : Set ℚ :=
  {r : ℚ | ∃ (a : ℤ) (n : ℕ), ¬ ((S123.p i : ℤ) ∣ a) ∧ r = (a : ℚ) / (S123.p i : ℚ) ^ n}

/-- The "grid" part of the carrier: pairs `(r, i)` with `r ∈ C i` (pi-Base S123). -/
def S123.Grid : Type := ↥{q : ℚ × ℕ | q.1 ∈ S123.C q.2}

/-- The carrier of Roy's lattice space (pi-Base S123): the grid `{(r, i) | r ∈ C i}`
together with one extra point `ω` (represented as `none`). -/
def S123 : Type := Option S123.Grid

/-- The generating neighborhood sets: on even levels `2n`, the `ε`-intervals
`U_ε(r,2n) = {(t,2n) | |r-t| < ε}`; on odd levels `2n-1` (i.e. `i = 2 * n - 1`), the
lattice sets `V_ε(r,2n-1) = {(t,m) | |r-t| < ε, |m-n| ≤ 1}`; and at `ω = none`, the tail
sets `W_n(ω) = {(s,i) | i ≥ 2n} ∪ {ω}`. -/
def S123.generators : Set (Set S123) :=
  -- `U_ε(r, 2n)`, for even levels.
  { s | ∃ (r : ℚ) (n : ℕ) (ε : ℚ), 0 < ε ∧
      s = {x : S123 | ∃ q : S123.Grid, x = some q ∧ (q.val : ℚ × ℕ).2 = 2 * n ∧
        |r - (q.val : ℚ × ℕ).1| < ε } } ∪
  -- `V_ε(r, 2n-1)`, for odd levels.
  { s | ∃ (r : ℚ) (n : ℕ) (ε : ℚ), 0 < ε ∧
      s = {x : S123 | ∃ q : S123.Grid, x = some q ∧ (q.val : ℚ × ℕ).2 + 1 = 2 * n ∧
        |r - (q.val : ℚ × ℕ).1| < ε ∧
        ((q.val : ℚ × ℕ).2 : ℤ) - (n : ℤ) ∈ Set.Icc (-1 : ℤ) 1 } } ∪
  -- `W_n(ω)`, the tail neighborhoods of the extra point `ω`.
  { s | ∃ n : ℕ,
      s = {x : S123 | x = none ∨ ∃ q : S123.Grid, x = some q ∧ 2 * n ≤ (q.val : ℚ × ℕ).2} }

instance : TopologicalSpace S123 := TopologicalSpace.generateFrom S123.generators

end S123
end PiBase.Spaces
