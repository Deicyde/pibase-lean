module

public import Mathlib.Topology.MetricSpace.Perfect
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.SetTheory.Cardinal.Continuum

@[expose] public section

open Topology Set Cardinal Ordinal

namespace PiBase.Spaces
namespace S121

/- Space 121: Bernstein's connected set.
See https://topology.pi-base.org/spaces/S000121.
Well-order the closed, connected, ≥2-point subsets of the plane ℝ² (S176) as
`{C_α : α < 𝔠}`. Recursively choose two fresh points `a_α, b_α ∈ C_α`, distinct
from each other and from every point chosen at an earlier stage `β < α` (possible
since each `C_α` has cardinality `𝔠`, while only `< 𝔠`-many points have been used
so far). Bernstein's connected set is `A = ⋃_{α<𝔠} {a_α}`, with the subspace
topology induced from ℝ². -/

namespace S121

/-- The ambient plane ℝ² (matches pi-Base S176, `ℝ × ℝ` with the product topology). -/
abbrev Plane := ℝ × ℝ

/-- The family of closed, connected, nontrivial (≥ 2 point) subsets of the plane:
this is the family pi-Base well-orders (with order type `𝔠`) to build Bernstein's
connected set. -/
def CC : Type := {C : Set Plane // IsClosed C ∧ IsPreconnected C ∧ C.Nontrivial}

/-- Every closed connected nontrivial subset of the plane is perfect (has no isolated
points): being connected with ≥ 2 points it is dense-in-itself, and being closed it
equals its own closure. -/
theorem CC.perfect (C : CC) : Perfect C.1 := by
  obtain ⟨C, hC, hconn, hnt⟩ := C
  have hpp : Preperfect C := hconn.preperfect_of_nontrivial hnt
  rw [preperfect_iff_perfect_closure] at hpp
  rwa [hC.closure_eq] at hpp

/-- A continuous injection of the Cantor space `ℕ → Bool` into `C`, witnessing that a
closed connected nontrivial `C` has cardinality (at least) the continuum. This is how
each stage of the recursion sources fresh points of `C`. -/
noncomputable def CC.cantor (C : CC) : (ℕ → Bool) → Plane :=
  (C.perfect.exists_nat_bool_injection C.2.2.2.nonempty).choose

theorem CC.cantor_range (C : CC) : range C.cantor ⊆ C.1 :=
  (C.perfect.exists_nat_bool_injection C.2.2.2.nonempty).choose_spec.1

theorem CC.cantor_injective (C : CC) : Function.Injective C.cantor :=
  (C.perfect.exists_nat_bool_injection C.2.2.2.nonempty).choose_spec.2.2

/-- There are at most continuum-many closed connected nontrivial subsets of the plane:
the plane is second countable, so every open set is the union of the subfamily of a
fixed countable basis that it contains, giving an injection of the open sets into
`Set (countable index set)`, of cardinality `2 ^ ℵ₀ = 𝔠`; closed sets are complements
of open sets, and `CC` is a subtype of the closed sets. -/
theorem mk_CC_le_continuum : #CC ≤ 𝔠 := by
  obtain ⟨B, hBc, -, hB⟩ := TopologicalSpace.exists_countable_basis Plane
  set S : {u : Set Plane // IsOpen u} → Set B :=
    fun u => {s : B | (s : Set Plane) ⊆ u.1} with hS
  have key : ∀ u : {u : Set Plane // IsOpen u}, u.1 = ⋃₀ (Subtype.val '' S u) := by
    intro u
    rw [hB.open_eq_sUnion' u.2]
    congr 1
    ext s
    simp only [mem_image, mem_setOf_eq, S]
    constructor
    · rintro ⟨hsB, hsu⟩; exact ⟨⟨s, hsB⟩, hsu, rfl⟩
    · rintro ⟨⟨s', hs'B⟩, hs'u, rfl⟩; exact ⟨hs'B, hs'u⟩
  have hinj_open : Function.Injective S := by
    intro u v huv
    apply Subtype.ext
    rw [key u, key v, huv]
  have hopen : #{u : Set Plane // IsOpen u} ≤ 𝔠 :=
    calc #{u : Set Plane // IsOpen u} ≤ #(Set B) := Cardinal.mk_le_of_injective hinj_open
      _ = 2 ^ #B := by rw [Cardinal.mk_set]
      _ ≤ 2 ^ ℵ₀ := Cardinal.power_le_power_left two_ne_zero hBc.le_aleph0
      _ = 𝔠 := rfl
  have hinj_closed : Function.Injective (fun C : {C : Set Plane // IsClosed C} =>
      (⟨Cᶜ, C.2.isOpen_compl⟩ : {u : Set Plane // IsOpen u})) := by
    intro C D hCD
    apply Subtype.ext
    have := congrArg Subtype.val hCD
    simp only at this
    rwa [compl_inj_iff] at this
  have hclosed : #{C : Set Plane // IsClosed C} ≤ 𝔠 :=
    (Cardinal.mk_le_of_injective hinj_closed).trans hopen
  have hinj_CC : Function.Injective
      (fun C : CC => (⟨C.1, C.2.1⟩ : {C : Set Plane // IsClosed C})) := by
    intro C D hCD
    apply Subtype.ext
    simpa using hCD
  exact (Cardinal.mk_le_of_injective hinj_CC).trans hclosed

/-- The order type of the well-order of `CC` used to enumerate it (`= #CC ≤ 𝔠`). -/
noncomputable def ccOrd : Ordinal := (Cardinal.mk CC).ord

/-- A bijection realizing `ccOrd` as the order type of (a well-order of) `CC`. -/
noncomputable def ccEquiv : CC ≃ ccOrd.ToType := by
  have : #CC = #ccOrd.ToType := by
    rw [Cardinal.mk_toType, ccOrd, Cardinal.card_ord]
  exact Classical.choice (Cardinal.eq.mp this)

/-- For `o < ccOrd`, the `o`-th closed connected nontrivial subset of the plane in the
well-order of `CC`, i.e. pi-Base's `C_o`. -/
noncomputable def enumCC (o : Ordinal) (h : o < ccOrd) : CC :=
  ccEquiv.symm (Ordinal.ToType.mk ⟨o, h⟩)

/-- Below `ccOrd`, the ordinals used so far number `< 𝔠`: `Iio o` for `o < ccOrd` has
cardinality `o.card < #CC ≤ 𝔠`. -/
theorem card_Iio_lt_continuum {o : Ordinal} (h : o < ccOrd) : #(Iio o) < 𝔠 := by
  have h1 : o.card < Cardinal.mk CC := Cardinal.lt_ord.mp h
  rw [Ordinal.mk_Iio_ordinal o]
  have h3 : Cardinal.lift.{1} o.card < Cardinal.lift.{1} (Cardinal.mk CC) :=
    Cardinal.lift_lt.mpr h1
  have h4 : Cardinal.lift.{1} (Cardinal.mk CC) ≤ Cardinal.lift.{1} 𝔠 :=
    Cardinal.lift_le.mpr mk_CC_le_continuum
  have h5 : Cardinal.lift.{1} (𝔠 : Cardinal.{0}) = 𝔠 := Cardinal.lift_continuum
  rw [h5] at h4
  exact h3.trans_le h4

open Classical in
/-- The pair of points `(a_o, b_o)` chosen at stage `o` of the transfinite recursion:
two points of the `o`-th closed connected nontrivial set `C_o`, distinct from each
other and from every point chosen at an earlier stage `p < o` (always possible: `C_o`
is sourced through a Cantor-space injection, of cardinality `𝔠`, while only `< 𝔠`-many
points have been used by stage `o`, by `card_Iio_lt_continuum`). Junk `(0, 0)` once
`o ≥ ccOrd` (no closed connected set left to enumerate). -/
noncomputable def pair : Ordinal → Plane × Plane
  | o =>
    if h : o < ccOrd then
      let C := enumCC o h
      let used : Set (ℕ → Bool) :=
        C.cantor ⁻¹' (⋃ p : Iio o, ({(pair p.1).1, (pair p.1).2} : Set Plane))
      let x : ℕ → Bool :=
        if hx : (Set.univ \ used).Nonempty then hx.choose else Classical.arbitrary _
      let y : ℕ → Bool :=
        if hy : (Set.univ \ (used ∪ {x})).Nonempty then hy.choose else Classical.arbitrary _
      (C.cantor x, C.cantor y)
    else (0, 0)
termination_by o => o
decreasing_by
  all_goals exact p.2

/-- Bernstein's connected set (pi-Base S121): the union, over all closed connected
nontrivial subsets `C_o` of the plane in the fixed well-order, of the point `a_o`
freshly chosen from `C_o` at stage `o` of the construction. -/
def A : Set Plane := ⋃ o : Iio ccOrd, {(pair o.1).1}

end S121

/-- Bernstein's connected set (pi-Base S121), as the subset `A` of the plane ℝ². -/
def S121 : Type := ↥S121.A

instance : TopologicalSpace S121 := instTopologicalSpaceSubtype

end S121
end PiBase.Spaces
