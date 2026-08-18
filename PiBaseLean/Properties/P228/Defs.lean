module

public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Topology.Defs.Basic
public import PiBaseLean.Properties.Bundled.Defs

@[expose] public section

namespace PiBase

/- 228. Weakly first countable -/
class WeaklyFirstCountableSpace (X : Type*) [TopologicalSpace X] : Prop where
  nhds_countable_weak_basis :
    ∃ V : X → ℕ → Set X, (∀ (x : X), Antitone (V x) ∧ ∀ (n : ℕ), x ∈ V x n)
      ∧ ∀ O : Set X, IsOpen O ↔ ∀ x ∈ O, ∃ k : ℕ, V x k ⊆ O

end PiBase

namespace PiBase.Formal

def P228 : Property where
  toPred := WeaklyFirstCountableSpace
  well_defined φ h := by
    obtain ⟨V, hVanti, hVopen⟩ := h.nhds_countable_weak_basis
    refine ⟨fun y n => φ '' V (φ.symm y) n, ?_⟩
    constructor
    · intro y
      constructor
      · intro n m hnm
        exact Set.image_mono ((hVanti (φ.symm y)).1 hnm)
      · intro n
        exact ⟨φ.symm y, (hVanti (φ.symm y)).2 n, φ.apply_symm_apply y⟩
    · intro O
      constructor
      · intro hO y hy
        have hO_pre : IsOpen (φ ⁻¹' O) := φ.isOpen_preimage.mpr hO
        have hy' : φ.symm y ∈ φ ⁻¹' O := by
          change φ (φ.symm y) ∈ O
          rwa [φ.apply_symm_apply]
        have := (hVopen (φ ⁻¹' O)).mp hO_pre (φ.symm y) hy'
        obtain ⟨k, hk⟩ := this
        refine ⟨k, ?_⟩
        calc φ '' V (φ.symm y) k ⊆ φ '' (φ ⁻¹' O) := Set.image_mono hk
          _ = O := φ.image_preimage O
      · intro hRHS
        have hRHS_pre : ∀ x ∈ φ ⁻¹' O, ∃ k : ℕ, V x k ⊆ φ ⁻¹' O := by
          intro x hx
          have hxO : φ x ∈ O := hx
          obtain ⟨k, hk⟩ := hRHS (φ x) hxO
          refine ⟨k, ?_⟩
          intro z hz
          have : φ z ∈ φ '' V x k := ⟨z, hz, rfl⟩
          -- Actually V x = V (φ.symm (φ x))? Need to align
          have hx_eq : φ.symm (φ x) = x := φ.symm_apply_apply x
          have hVk : V x k = V (φ.symm (φ x)) k := by rw [hx_eq]
          -- hk : φ '' V (φ.symm (φ x)) k ⊆ O
          have h' : V x k ⊆ φ ⁻¹' O := by
            intro w hw
            have : φ w ∈ φ '' V (φ.symm (φ x)) k := by
              have : V x k = V (φ.symm (φ x)) k := by rw [hx_eq]
              rw [this] at hw
              exact ⟨w, hw, rfl⟩
            exact hk this
          exact h' hz
        have hOpen_pre : IsOpen (φ ⁻¹' O) := (hVopen _).mpr hRHS_pre
        exact φ.isOpen_preimage.mp hOpen_pre

end PiBase.Formal
