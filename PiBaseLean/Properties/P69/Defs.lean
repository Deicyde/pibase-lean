module

public import PiBaseLean.AdditionalDefs.Games
public import PiBaseLean.Properties.Bundled.Defs

@[expose] public section

universe u v

namespace PiBase

/- 69. Strategic Menger -/
class StrategicMengerSpace (X : Type u) [TopologicalSpace X] : Prop where
  strategic_menger : HasWinningStrategyB (mengerGame X)

open Set

section Menger

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

/-- The set of allowed moves of `mengerGame`. -/
private def openCoverAllowed (Z : Type*) [TopologicalSpace Z] : AllowedMoves (Set (Set Z)) :=
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

/-- The payoff conditions of the Menger games correspond under a homeomorphism. -/
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
  well_defined φ h :=
    ⟨h.strategic_menger.mengerGame_of_homeomorph φ⟩

end PiBase.Formal
