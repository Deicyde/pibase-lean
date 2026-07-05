module

public import Mathlib.Topology.Order
public import Mathlib.Data.Set.Finite.Basic

@[expose] public section

open Topology

namespace PiBase.Spaces
namespace S185

/- Space 185: One-point compactification of the metric fan.
See https://topology.pi-base.org/spaces/S000185.
Carrier `X = (ω × ω) ∪ {∞_x, ∞_y}`, represented as `(ℕ × ℕ) ⊕ Bool`
(`Sum.inr false := ∞_x`, `Sum.inr true := ∞_y`). Every grid point `(m, n) : ω × ω` is
isolated; a set containing `∞_x` is a neighborhood of it iff it contains all but
finitely many columns of `ω × ω`; a set containing `∞_y` is a neighborhood of it iff it
contains all but finitely many rows of `ω × ω`. -/

/-- The carrier of the one-point compactification of the metric fan (pi-Base S185): the
grid `ω × ω` together with two extra points `∞_x, ∞_y` (represented via `Sum.inr false`
and `Sum.inr true` respectively). -/
def S185 : Type := (ℕ × ℕ) ⊕ Bool

/-- The generating open sets: every singleton grid point `{(m, n)}` (making each grid
point isolated); for each finite set `F` of columns, the set `{∞_x} ∪ {(m,n) | m ∉ F}`
(a neighborhood of `∞_x` missing only the finitely many columns in `F`); and for each
finite set `F` of rows, the set `{∞_y} ∪ {(m,n) | n ∉ F}` (a neighborhood of `∞_y`
missing only the finitely many rows in `F`). -/
def S185.generators : Set (Set S185) :=
  -- Singletons of grid points, so every `(m, n)` is isolated.
  { s | ∃ p : ℕ × ℕ, s = {(Sum.inl p : S185)} } ∪
  -- Cofinite-in-columns neighborhoods of `∞_x`.
  { s | ∃ F : Set ℕ, F.Finite ∧
      s = insert (Sum.inr false) {x : S185 | ∃ p : ℕ × ℕ, x = Sum.inl p ∧ p.1 ∉ F} } ∪
  -- Cofinite-in-rows neighborhoods of `∞_y`.
  { s | ∃ F : Set ℕ, F.Finite ∧
      s = insert (Sum.inr true) {x : S185 | ∃ p : ℕ × ℕ, x = Sum.inl p ∧ p.2 ∉ F} }

instance : TopologicalSpace S185 := TopologicalSpace.generateFrom S185.generators

end S185
end PiBase.Spaces
