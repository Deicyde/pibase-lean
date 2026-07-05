module

public import Mathlib.SetTheory.Cardinal.Aleph
public import Mathlib.SetTheory.Ordinal.Basic
public import Mathlib.Data.Prod.Lex
public import Mathlib.Data.Real.Basic
public import Mathlib.Topology.Order

public import PiBaseLean.Spaces.Bundled.Defs

@[expose] public section

open Topology
open scoped Ordinal

namespace PiBase.Spaces

/- Space 39: Closed long ray.
See https://topology.pi-base.org/spaces/S000039.
The set ω₁ × [0,1) ∪ {⟨ω₁,0⟩} — i.e. all pairs `(a, x)` with `a ≤ ω₁` and `x ∈ [0,1)`,
except that the top ordinal `ω₁` may only pair with `x = 0` — carrying the lexicographic
order topology; equivalently the one-point compactification of the long ray (S38). -/

/-- The underlying linear order: countable ordinals together with `ω₁` itself,
i.e. all ordinals `≤ ω₁`. -/
abbrev S39.Ord : Type := (Order.succ ω₁).ToType

/-- The half-open unit interval `[0,1)`, carrying its usual (subtype) linear order. -/
abbrev S39.Unit : Type := Set.Ico (0 : ℝ) 1

/-- `⟨ω₁, 0⟩`, the extra point added to compactify the long ray. -/
noncomputable def S39.topPoint : S39.Ord ×ₗ S39.Unit :=
  toLex (⊤, (⟨0, by norm_num⟩ : S39.Unit))

/-- Closed long ray (pi-Base S39): the long ray `ω₁ × [0,1)` together with one point
`⟨ω₁, 0⟩` at its far end, i.e. everything lexicographically `≤ ⟨ω₁, 0⟩`. -/
noncomputable def S39 : Type := {p : S39.Ord ×ₗ S39.Unit // p ≤ S39.topPoint}

noncomputable instance : LinearOrder S39 :=
  inferInstanceAs (LinearOrder {p : S39.Ord ×ₗ S39.Unit // p ≤ S39.topPoint})

noncomputable instance : TopologicalSpace S39 :=
  TopologicalSpace.generateFrom {s | ∃ a, s = Set.Ioi a ∨ s = Set.Iio a}

end PiBase.Spaces

namespace PiBase.Formal

/-- π-Base S39 as a bundled `Space` (carrier + topology). -/
noncomputable def S39 : Space := ⟨PiBase.Spaces.S39, inferInstance⟩

end PiBase.Formal
