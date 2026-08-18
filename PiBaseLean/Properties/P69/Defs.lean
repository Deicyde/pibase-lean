module

public import PiBaseLean.AdditionalDefs.Games
public import PiBaseLean.Properties.Bundled.Defs

@[expose] public section

universe u

namespace PiBase

/- 69. Strategic Menger -/
class StrategicMengerSpace (X : Type u) [TopologicalSpace X] : Prop where
  strategic_menger : HasWinningStrategyB (mengerGame X)

end PiBase

namespace PiBase

open Set

/-! ### Transporting games along a relabelling of the moves

The following section provides a reusable way of moving winning strategies between two games
whose move sets are in bijection. It is used to show that game-theoretic properties such as
`StrategicMengerSpace` (69), `MarkovMengerSpace` (70), `TwoMarkovMengerSpace` (72) and
`ProximalSpace` (76) are preserved by homeomorphisms. -/

section Transport

variable {A B : Type u}

theorem map_ofFun (e : B → A) (b : ℕ → B) (k : ℕ) :
    (List.ofFun b k).map e = List.ofFun (fun n ↦ e (b n)) k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [List.ofFun, ih]

theorem map_ltakeHalf (e : B → A) (l : List B) (n : ℕ) :
    (l.ltakeHalf n).map e = (l.map e).ltakeHalf n := by
  induction n generalizing l with
  | zero =>
    match l with
    | [] => rfl
    | [_] => rfl
    | _ :: _ :: _ => rfl
  | succ n ih =>
    match l with
    | [] => rfl
    | [_] => rfl
    | _ :: _ :: l => exact congrArg _ (ih l)

theorem map_rtakeHalf (e : B → A) (l : List B) (n : ℕ) :
    (l.rtakeHalf n).map e = (l.map e).rtakeHalf n := by
  change (l.reverse.ltakeHalf n).map e = (l.map e).reverse.ltakeHalf n
  rw [map_ltakeHalf, List.map_reverse]

/-- Transport of a payoff condition through a relabelling `e` of the moves, for games built
with `Game.ofAllowed`. -/
theorem isPayoff_ofAllowed_iff {G : Game A} {H : Game B} {SA : AllowedMoves A}
    {SB : AllowedMoves B} (e : B → A) (hS : ∀ l : List B, SB l ↔ SA (l.map e)) (b : ℕ → B)
    (hP : H.IsPayoff b ↔ G.IsPayoff fun n ↦ e (b n)) :
    (H.ofAllowed SB).IsPayoff b ↔ (G.ofAllowed SA).IsPayoff fun n ↦ e (b n) := by
  have hSk : ∀ k : ℕ, SB (List.ofFun b k) ↔ SA (List.ofFun (fun n ↦ e (b n)) k) := by
    intro k
    rw [hS, map_ofFun]
  simp only [Game.ofAllowed, hSk, hP]

/-- If the moves of `H` inject into the moves of `G` compatibly with the payoff conditions,
then a winning strategy for player `A` in `G` yields one in `H`. -/
theorem HasWinningStrategyA.of_equiv {G : Game A} {H : Game B} (e : B ≃ A)
    (hP : ∀ b : ℕ → B, (G.IsPayoff fun n ↦ e (b n)) → H.IsPayoff b)
    (hG : HasWinningStrategyA G) : HasWinningStrategyA H := by
  obtain ⟨f, hf⟩ := hG
  refine ⟨fun l ↦ e.symm (f (l.map e)), ?_⟩
  intro b hb
  refine hP b (hf (fun n ↦ e (b n)) ?_)
  intro n
  show e (b (2 * n)) = f (List.ofFun (fun n ↦ e (b n)) (2 * n))
  rw [← map_ofFun]
  simpa using congrArg e (hb n)

/-- If the moves of `H` inject into the moves of `G` compatibly with the payoff conditions,
then a winning strategy for player `B` in `G` yields one in `H`. -/
theorem HasWinningStrategyB.of_equiv {G : Game A} {H : Game B} (e : B ≃ A)
    (hP : ∀ b : ℕ → B, H.IsPayoff b → G.IsPayoff fun n ↦ e (b n))
    (hG : HasWinningStrategyB G) : HasWinningStrategyB H := by
  obtain ⟨f, hf⟩ := hG
  refine ⟨fun l ↦ e.symm (f (l.map e)), ?_⟩
  intro b hb hpb
  refine hf (fun n ↦ e (b n)) ?_ (hP b hpb)
  intro n
  show e (b (2 * n + 1)) = f (List.ofFun (fun n ↦ e (b n)) (2 * n + 1))
  rw [← map_ofFun]
  simpa using congrArg e (hb n)

/-- The `k`-Markov analogue of `HasWinningStrategyB.of_equiv`. -/
theorem HasMarkovKWinningStrategyB.of_equiv {G : Game A} {H : Game B} {k : ℕ} (e : B ≃ A)
    (hP : ∀ b : ℕ → B, H.IsPayoff b → G.IsPayoff fun n ↦ e (b n))
    (hG : HasMarkovKWinningStrategyB G k) : HasMarkovKWinningStrategyB H k := by
  obtain ⟨f, hf⟩ := hG
  refine ⟨fun n l ↦ e.symm (f n (l.map e)), ?_⟩
  intro b hb hpb
  refine hf (fun n ↦ e (b n)) ?_ (hP b hpb)
  intro n
  show e (b (2 * n + 1)) = f n ((List.ofFun (fun n ↦ e (b n)) (2 * n + 1)).rtakeHalf k)
  rw [← map_ofFun, ← map_rtakeHalf]
  simpa using congrArg e (hb n)

end Transport

/-! ### Transporting the Menger game along a homeomorphism -/

section Menger

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

/-- Taking preimages under a homeomorphism is a bijection between the subsets of the two
spaces. -/
def preimageSetEquiv (φ : X ≃ₜ Y) : Set Y ≃ Set X where
  toFun t := φ ⁻¹' t
  invFun s := φ.symm ⁻¹' s
  left_inv t := by ext y; simp
  right_inv s := by ext x; simp

@[simp]
theorem preimageSetEquiv_apply (φ : X ≃ₜ Y) (t : Set Y) : preimageSetEquiv φ t = φ ⁻¹' t := rfl

/-- Taking preimages under a homeomorphism is a bijection between the families of subsets of
the two spaces. -/
def preimageFamilyEquiv (φ : X ≃ₜ Y) : Set (Set Y) ≃ Set (Set X) :=
  Equiv.Set.congr (preimageSetEquiv φ)

theorem preimageFamilyEquiv_apply (φ : X ≃ₜ Y) (S : Set (Set Y)) :
    preimageFamilyEquiv φ S = (preimageSetEquiv φ) '' S := rfl

@[simp]
theorem preimageFamilyEquiv_empty (φ : X ≃ₜ Y) :
    preimageFamilyEquiv φ ∅ = (∅ : Set (Set X)) := by
  rw [preimageFamilyEquiv_apply, image_empty]

theorem sUnion_preimageFamilyEquiv (φ : X ≃ₜ Y) (S : Set (Set Y)) :
    ⋃₀ (preimageFamilyEquiv φ S) = φ ⁻¹' (⋃₀ S) := by
  rw [preimageFamilyEquiv_apply, sUnion_image, preimage_sUnion]
  simp

theorem preimageFamilyEquiv_iUnion (φ : X ≃ₜ Y) (s : ℕ → Set (Set Y)) :
    preimageFamilyEquiv φ (⋃ n, s n) = ⋃ n, preimageFamilyEquiv φ (s n) := by
  simp only [preimageFamilyEquiv_apply, image_iUnion]

@[simp]
theorem preimageFamilyEquiv_finite (φ : X ≃ₜ Y) (S : Set (Set Y)) :
    (preimageFamilyEquiv φ S).Finite ↔ S.Finite := by
  rw [preimageFamilyEquiv_apply]
  refine ⟨fun h ↦ ?_, fun h ↦ h.image _⟩
  have := h.image (preimageSetEquiv φ).symm
  rwa [(preimageSetEquiv φ).symm_image_image] at this

@[simp]
theorem preimageFamilyEquiv_subset (φ : X ≃ₜ Y) (S T : Set (Set Y)) :
    preimageFamilyEquiv φ S ⊆ preimageFamilyEquiv φ T ↔ S ⊆ T := by
  rw [preimageFamilyEquiv_apply, preimageFamilyEquiv_apply]
  exact image_subset_image_iff (preimageSetEquiv φ).injective

theorem preimage_eq_univ_iff_of_homeomorph (φ : X ≃ₜ Y) (U : Set Y) :
    φ ⁻¹' U = univ ↔ U = univ := by
  rw [preimage_eq_univ_iff, φ.surjective.range_eq, univ_subset_iff]

/-- The families of open covers of `X` and of `Y` correspond to each other under
`preimageFamilyEquiv`. -/
@[simp]
theorem preimageFamilyEquiv_mem_openCovers (φ : X ≃ₜ Y) (S : Set (Set Y)) :
    (⋃₀ (preimageFamilyEquiv φ S) = univ ∧ ∀ s ∈ preimageFamilyEquiv φ S, IsOpen s) ↔
      (⋃₀ S = univ ∧ ∀ t ∈ S, IsOpen t) := by
  rw [sUnion_preimageFamilyEquiv, preimage_eq_univ_iff_of_homeomorph]
  refine and_congr_right fun _ ↦ ⟨fun h t ht ↦ ?_, fun h s hs ↦ ?_⟩
  · exact φ.isOpen_preimage.mp (h (φ ⁻¹' t) ⟨t, ht, rfl⟩)
  · obtain ⟨t, ht, rfl⟩ := hs
    exact φ.isOpen_preimage.mpr (h t ht)

/-- The set of allowed moves of `mengerGame`. -/
private def openCoverAllowed (Z : Type u) [TopologicalSpace Z] : AllowedMoves (Set (Set Z)) :=
  fun l ↦ l ≠ [] → ((Odd l.length →
      l.getLastD ∅ ∈ {A : Set (Set Z) | ⋃₀ A = univ ∧ ∀ s ∈ A, IsOpen s}) ∧
    (Even l.length → (l.getLastD ∅).Finite ∧ l.getLastD ∅ ⊆ l.dropLast.getLastD ∅))

private theorem openCoverAllowed_iff (φ : X ≃ₜ Y) (l : List (Set (Set Y))) :
    openCoverAllowed Y l ↔ openCoverAllowed X (l.map (preimageFamilyEquiv φ)) := by
  have hLast : (l.map (preimageFamilyEquiv φ)).getLastD ∅
      = preimageFamilyEquiv φ (l.getLastD ∅) := by
    rw [← preimageFamilyEquiv_empty φ, List.getLastD_map]
  have hLast' : (l.map (preimageFamilyEquiv φ)).dropLast.getLastD ∅
      = preimageFamilyEquiv φ (l.dropLast.getLastD ∅) := by
    rw [← List.map_dropLast, ← preimageFamilyEquiv_empty φ, List.getLastD_map]
  simp only [openCoverAllowed, hLast, hLast', List.length_map, ne_eq, List.map_eq_nil_iff,
    mem_ofPred_eq, preimageFamilyEquiv_mem_openCovers, preimageFamilyEquiv_finite,
    preimageFamilyEquiv_subset]

/-- The payoff conditions of the Menger games on `X` and on `Y` correspond to each other
under a homeomorphism. -/
theorem mengerGame_isPayoff_iff (φ : X ≃ₜ Y) (b : ℕ → Set (Set Y)) :
    (mengerGame Y).IsPayoff b ↔
      (mengerGame X).IsPayoff fun n ↦ preimageFamilyEquiv φ (b n) := by
  refine isPayoff_ofAllowed_iff (preimageFamilyEquiv φ) (openCoverAllowed_iff φ) b ?_
  change (⋃ n, b (2 * n + 1)) ∉ {A : Set (Set Y) | ⋃₀ A = univ ∧ ∀ s ∈ A, IsOpen s} ↔
    (⋃ n, preimageFamilyEquiv φ (b (2 * n + 1))) ∉
      {A : Set (Set X) | ⋃₀ A = univ ∧ ∀ s ∈ A, IsOpen s}
  rw [← preimageFamilyEquiv_iUnion]
  simp

theorem HasWinningStrategyB.mengerGame_of_homeomorph (φ : X ≃ₜ Y)
    (h : HasWinningStrategyB (mengerGame X)) : HasWinningStrategyB (mengerGame Y) :=
  h.of_equiv (preimageFamilyEquiv φ) fun b hb ↦ (mengerGame_isPayoff_iff φ b).mp hb

theorem HasMarkovKWinningStrategyB.mengerGame_of_homeomorph {k : ℕ} (φ : X ≃ₜ Y)
    (h : HasMarkovKWinningStrategyB (mengerGame X) k) :
    HasMarkovKWinningStrategyB (mengerGame Y) k :=
  h.of_equiv (preimageFamilyEquiv φ) fun b hb ↦ (mengerGame_isPayoff_iff φ b).mp hb

end Menger

end PiBase

namespace PiBase.Formal

def P69 : Property where
  toPred := StrategicMengerSpace
  well_defined {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] (φ : X ≃ₜ Y) h :=
    ⟨h.strategic_menger.mengerGame_of_homeomorph φ⟩

end PiBase.Formal
