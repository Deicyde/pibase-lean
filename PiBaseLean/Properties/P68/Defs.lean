module

public import Mathlib.Topology.Defs.Basic
public import PiBaseLean.Properties.Bundled.Defs

@[expose] public section

open Topology Set Function TopologicalSpace

universe u

namespace PiBase

/- 68. Rothberger -/
class RothbergerSpace (X : Type u) [TopologicalSpace X] : Prop where
  rothberger : ∀ {ι : Type u} (U : ℕ → ι → Set X), Nonempty ι →
    (∀ (n : ℕ) (i : ι), IsOpen (U n i)) → (∀ (n : ℕ), univ = ⋃ (i : ι), (U n i)) →
      ∃ j : ℕ → ι, univ = ⋃ (n : ℕ), U n (j n)

end PiBase

namespace PiBase.Formal

def P68 : Property where
  toPred := RothbergerSpace
  well_defined φ h := by
    constructor
    intro ι U hι hU_open hU_cover
    let U' : ℕ → ι → Set _ := fun n i => φ ⁻¹' (U n i)
    have hU'_open : ∀ n i, IsOpen (U' n i) := fun n i => φ.isOpen_preimage.mpr (hU_open n i)
    have hU'_cover : ∀ n, (⋃ i, U' n i) = univ := fun n => by
      have : (⋃ i, U' n i) = φ ⁻¹' (⋃ i, U n i) := by
        simp only [U', preimage_iUnion]
      rw [this, ← hU_cover n, preimage_univ]
    obtain ⟨j, hj⟩ := h.rothberger U' hι hU'_open (fun n => (hU'_cover n).symm)
    refine ⟨j, ?_⟩
    calc univ = φ '' univ := (image_univ_of_surjective φ.surjective).symm
      _ = φ '' (⋃ n, U' n (j n)) := by rw [← hj]
      _ = ⋃ n, φ '' (U' n (j n)) := by rw [image_iUnion]
      _ = ⋃ n, U n (j n) := by
          have h_eq : ∀ n, φ '' (U' n (j n)) = U n (j n) := fun n => φ.image_preimage (U n (j n))
          simp_rw [h_eq]

end PiBase.Formal
