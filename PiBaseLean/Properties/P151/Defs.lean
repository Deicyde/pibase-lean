module

public import Mathlib.Topology.Homeomorph.Lemmas
public import PiBaseLean.AdditionalDefs.Games
public import PiBaseLean.Properties.Bundled.Defs
public import PiBaseLean.Properties.P69.Defs

@[expose] public section

universe u

namespace PiBase

/- 151. Strategically Rothberger -/
class StrategicallyRothbergerSpace (X : Type u) [TopologicalSpace X] : Prop where
  strategically_rothberger : Nonempty X → HasWinningStrategyB (rothbergerGame X)

end PiBase

namespace PiBase

open Set

/-! ### Transporting selection games along a relabelling of the players' moves

`PiBaseLean.Properties.P69.Defs` provides the transport of `Game.ofAllowed` along a
relabelling of the moves. The selection games `g1Game` and `gFinGame` are played with
*families* of subsets as moves, so a relabelling of the moves is obtained from a bijection
`e : V ≃ W` between the subsets by taking images. This section records the facts about
`Equiv.Set.congr e` needed to transport the allowed moves and payoff conditions of `g1Game`
and `gFinGame`, and then specialises them to the games built from open covers and from
k-covers.

The results here are reused by the properties 152, 157, 158, 160 and 161. -/

section FamilyTransport

variable {V W : Type u} (e : V ≃ W)

theorem familyEquiv_apply (S : Set V) : Equiv.Set.congr e S = e '' S := rfl

theorem familyEquiv_symm_apply (T : Set W) : (Equiv.Set.congr e).symm T = e.symm '' T := rfl

@[simp]
theorem familyEquiv_empty : Equiv.Set.congr e ∅ = (∅ : Set W) := image_empty _

theorem familyEquiv_mem_iff {S : Set V} {a : V} : e a ∈ Equiv.Set.congr e S ↔ a ∈ S := by
  rw [familyEquiv_apply]
  exact e.injective.mem_set_image

theorem familyEquiv_singleton (a : V) : Equiv.Set.congr e {a} = {e a} := image_singleton

theorem familyEquiv_iUnion (s : ℕ → Set V) :
    Equiv.Set.congr e (⋃ n, s n) = ⋃ n, Equiv.Set.congr e (s n) := by
  simp only [familyEquiv_apply, image_iUnion]

@[simp]
theorem familyEquiv_finite (S : Set V) : (Equiv.Set.congr e S).Finite ↔ S.Finite := by
  rw [familyEquiv_apply]
  refine ⟨fun h ↦ ?_, fun h ↦ h.image _⟩
  have := h.image e.symm
  rwa [e.symm_image_image] at this

@[simp]
theorem familyEquiv_subset (S T : Set V) :
    Equiv.Set.congr e S ⊆ Equiv.Set.congr e T ↔ S ⊆ T := by
  rw [familyEquiv_apply, familyEquiv_apply]
  exact image_subset_image_iff e.injective

/-- The "pick one element of the previous move" condition of `g1Game` is invariant under a
relabelling of the subsets. -/
theorem familyEquiv_exists_singleton (S T : Set V) :
    (∃ a, Equiv.Set.congr e S = {a} ∧ a ∈ Equiv.Set.congr e T) ↔
      (∃ a, S = {a} ∧ a ∈ T) := by
  constructor
  · rintro ⟨a, hS, ha⟩
    refine ⟨e.symm a, ?_, ?_⟩
    · have : (Equiv.Set.congr e).symm (Equiv.Set.congr e S) = (Equiv.Set.congr e).symm {a} :=
        congrArg _ hS
      rwa [Equiv.symm_apply_apply, familyEquiv_symm_apply, image_singleton] at this
    · rw [← familyEquiv_mem_iff e, Equiv.apply_symm_apply]
      exact ha
  · rintro ⟨a, rfl, ha⟩
    exact ⟨e a, familyEquiv_singleton e a, familyEquiv_mem_iff e |>.mpr ha⟩

/-- The allowed moves of a `g1Game`: player A plays a member of `A`, player B answers with a
singleton chosen inside player A's last move. -/
def g1Allowed {V : Type u} (A : Set (Set V)) : AllowedMoves (Set V) :=
  fun l ↦ l ≠ [] → ((Odd l.length → l.getLastD ∅ ∈ A) ∧
    (Even l.length → ∃ a, l.getLastD ∅ = {a} ∧ a ∈ l.dropLast.getLastD ∅))

/-- The allowed moves of a `gFinGame`: player A plays a member of `A`, player B answers with a
finite subfamily of player A's last move. -/
def gFinAllowed {V : Type u} (A : Set (Set V)) : AllowedMoves (Set V) :=
  fun l ↦ l ≠ [] → ((Odd l.length → l.getLastD ∅ ∈ A) ∧
    (Even l.length → (l.getLastD ∅).Finite ∧ l.getLastD ∅ ⊆ l.dropLast.getLastD ∅))

variable {A : Set (Set V)} {A' : Set (Set W)}

/-- The last entry of a list of families, and the last entry of its truncation, commute with a
relabelling of the subsets. -/
private theorem familyEquiv_getLastD (l : List (Set V)) :
    (l.map (Equiv.Set.congr e)).getLastD ∅ = Equiv.Set.congr e (l.getLastD ∅) := by
  rw [← familyEquiv_empty e, List.getLastD_map]

private theorem familyEquiv_getLastD_dropLast (l : List (Set V)) :
    (l.map (Equiv.Set.congr e)).dropLast.getLastD ∅
      = Equiv.Set.congr e (l.dropLast.getLastD ∅) := by
  rw [← List.map_dropLast, familyEquiv_getLastD]

theorem g1Allowed_iff (hA : ∀ S : Set V, Equiv.Set.congr e S ∈ A' ↔ S ∈ A) (l : List (Set V)) :
    g1Allowed A l ↔ g1Allowed A' (l.map (Equiv.Set.congr e)) := by
  simp only [g1Allowed, familyEquiv_getLastD e, familyEquiv_getLastD_dropLast e, List.length_map,
    ne_eq, List.map_eq_nil_iff, hA, familyEquiv_exists_singleton e]

theorem gFinAllowed_iff (hA : ∀ S : Set V, Equiv.Set.congr e S ∈ A' ↔ S ∈ A)
    (l : List (Set V)) :
    gFinAllowed A l ↔ gFinAllowed A' (l.map (Equiv.Set.congr e)) := by
  simp only [gFinAllowed, familyEquiv_getLastD e, familyEquiv_getLastD_dropLast e,
    List.length_map, ne_eq, List.map_eq_nil_iff, hA, familyEquiv_finite, familyEquiv_subset]

variable {B : Set (Set V)} {B' : Set (Set W)}

/-- The payoff condition of a selection game is invariant under a relabelling of the subsets. -/
theorem selectionPayoff_iff (hB : ∀ S : Set V, Equiv.Set.congr e S ∈ B' ↔ S ∈ B)
    (b : ℕ → Set V) :
    ((⋃ n, b (2 * n + 1)) ∉ B) ↔
      ((⋃ n, Equiv.Set.congr e (b (2 * n + 1))) ∉ B') := by
  rw [← familyEquiv_iUnion, hB]

theorem g1Game_isPayoff_iff (hA : ∀ S : Set V, Equiv.Set.congr e S ∈ A' ↔ S ∈ A)
    (hB : ∀ S : Set V, Equiv.Set.congr e S ∈ B' ↔ S ∈ B) (b : ℕ → Set V) :
    (g1Game A B).IsPayoff b ↔
      (g1Game A' B').IsPayoff fun n ↦ Equiv.Set.congr e (b n) :=
  isPayoff_ofAllowed_iff (Equiv.Set.congr e) (g1Allowed_iff e hA) b (selectionPayoff_iff e hB b)

theorem gFinGame_isPayoff_iff (hA : ∀ S : Set V, Equiv.Set.congr e S ∈ A' ↔ S ∈ A)
    (hB : ∀ S : Set V, Equiv.Set.congr e S ∈ B' ↔ S ∈ B) (b : ℕ → Set V) :
    (gFinGame A B).IsPayoff b ↔
      (gFinGame A' B').IsPayoff fun n ↦ Equiv.Set.congr e (b n) :=
  isPayoff_ofAllowed_iff (Equiv.Set.congr e) (gFinAllowed_iff e hA) b (selectionPayoff_iff e hB b)

end FamilyTransport

/-! ### The families of moves of the topological selection games -/

section Covers

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

/-- `preimageFamilyEquiv` is the relabelling of the moves induced by taking preimages. -/
theorem preimageFamilyEquiv_eq (φ : X ≃ₜ Y) :
    preimageFamilyEquiv φ = Equiv.Set.congr (preimageSetEquiv φ) := rfl

/-- The families of open covers of `X` and of `Y` correspond to each other. -/
theorem preimageFamilyEquiv_mem_openCovers' (φ : X ≃ₜ Y) (S : Set (Set Y)) :
    preimageFamilyEquiv φ S ∈ {A : Set (Set X) | ⋃₀ A = univ ∧ ∀ s ∈ A, IsOpen s} ↔
      S ∈ {A : Set (Set Y) | ⋃₀ A = univ ∧ ∀ s ∈ A, IsOpen s} :=
  preimageFamilyEquiv_mem_openCovers φ S

theorem preimageFamilyEquiv_univ_mem_iff (φ : X ≃ₜ Y) (S : Set (Set Y)) :
    (univ : Set X) ∈ preimageFamilyEquiv φ S ↔ (univ : Set Y) ∈ S := by
  rw [preimageFamilyEquiv_apply]
  constructor
  · rintro ⟨t, ht, hteq⟩
    rw [preimageSetEquiv_apply] at hteq
    rwa [← (preimage_eq_univ_iff_of_homeomorph φ t).mp hteq]
  · intro hS
    exact ⟨univ, hS, by simp [preimageSetEquiv_apply]⟩

/-- Being a k-cover is invariant under a homeomorphism. -/
theorem preimageFamilyEquiv_isKCover' (φ : X ≃ₜ Y) (S : Set (Set Y)) :
    IsKCover' (preimageFamilyEquiv φ S) ↔ IsKCover' S := by
  have hcover := preimageFamilyEquiv_mem_openCovers φ S
  have hKrange : ∀ K : Set Y, K ⊆ range φ := fun K ↦ by
    rw [φ.surjective.range_eq]; exact subset_univ K
  constructor
  · rintro ⟨hopen, hunion, hne, hK⟩
    obtain ⟨hunion', hopen'⟩ := hcover.mp ⟨hunion, hopen⟩
    refine ⟨hopen', hunion', fun h ↦ hne ((preimageFamilyEquiv_univ_mem_iff φ S).mpr h), ?_⟩
    intro K hKc
    obtain ⟨i, hi, hKi⟩ := hK (φ.isCompact_preimage.mpr hKc)
    rw [preimageFamilyEquiv_apply] at hi
    obtain ⟨t, ht, rfl⟩ := hi
    rw [preimageSetEquiv_apply] at hKi
    exact ⟨t, ht, (preimage_subset_preimage_iff (hKrange K)).mp hKi⟩
  · rintro ⟨hopen, hunion, hne, hK⟩
    obtain ⟨hunion', hopen'⟩ := hcover.mpr ⟨hunion, hopen⟩
    refine ⟨hopen', hunion', fun h ↦ hne ((preimageFamilyEquiv_univ_mem_iff φ S).mp h), ?_⟩
    intro K hKc
    obtain ⟨t, ht, hKt⟩ := hK (hKc.image φ.continuous)
    refine ⟨preimageSetEquiv φ t, ⟨t, ht, rfl⟩, ?_⟩
    rw [preimageSetEquiv_apply]
    exact fun x hx ↦ hKt ⟨x, hx, rfl⟩

end Covers

/-! ### Transporting the Rothberger game along a homeomorphism -/

section Rothberger

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

theorem rothbergerGame_isPayoff_iff (φ : X ≃ₜ Y) (b : ℕ → Set (Set Y)) :
    (rothbergerGame Y).IsPayoff b ↔
      (rothbergerGame X).IsPayoff fun n ↦ preimageFamilyEquiv φ (b n) :=
  g1Game_isPayoff_iff (preimageSetEquiv φ) (preimageFamilyEquiv_mem_openCovers' φ)
    (preimageFamilyEquiv_mem_openCovers' φ) b

theorem HasWinningStrategyB.rothbergerGame_of_homeomorph (φ : X ≃ₜ Y)
    (h : HasWinningStrategyB (rothbergerGame X)) : HasWinningStrategyB (rothbergerGame Y) :=
  h.of_equiv (preimageFamilyEquiv φ) fun b hb ↦ (rothbergerGame_isPayoff_iff φ b).mp hb

theorem HasMarkovKWinningStrategyB.rothbergerGame_of_homeomorph {k : ℕ} (φ : X ≃ₜ Y)
    (h : HasMarkovKWinningStrategyB (rothbergerGame X) k) :
    HasMarkovKWinningStrategyB (rothbergerGame Y) k :=
  h.of_equiv (preimageFamilyEquiv φ) fun b hb ↦ (rothbergerGame_isPayoff_iff φ b).mp hb

end Rothberger

end PiBase

namespace PiBase.Formal

open PiBase

def P151 : Property where
  toPred := StrategicallyRothbergerSpace
  well_defined {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] (φ : X ≃ₜ Y) h :=
    ⟨fun hY ↦ (h.strategically_rothberger ⟨φ.symm hY.some⟩).rothbergerGame_of_homeomorph φ⟩

end PiBase.Formal
