module

public import PiBaseLean.AdditionalDefs.Meta
public import PiBaseLean.Properties.P68.Defs

@[expose] public section

open Topology Set Filter TopologicalSpace

universe u

namespace PiBase

/- 150. ω-Rothberger -/
class OmegaRothberger (X : Type u) [TopologicalSpace X] : Prop where
  omega_rothberger : Omega RothbergerSpace X

end PiBase

namespace PiBase.Formal

def P150 : Property where
  toPred := OmegaRothberger
  well_defined φ h := by
    have roth_pres : ∀ {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y],
        (X ≃ₜ Y) → RothbergerSpace X → RothbergerSpace Y := by
      intro X Y _ _ f hf
      constructor
      intro ι U hι hU_open hU_cover
      let U' : ℕ → ι → Set X := fun n i => f ⁻¹' (U n i)
      have hU'_open : ∀ n i, IsOpen (U' n i) := fun n i => f.isOpen_preimage.mpr (hU_open n i)
      have hU'_cover : ∀ n, (⋃ i, U' n i) = univ := fun n => by
        have : (⋃ i, U' n i) = f ⁻¹' (⋃ i, U n i) := by
          simp [U', Set.preimage_iUnion]
        rw [this, ← hU_cover n, Set.preimage_univ]
      obtain ⟨j, hj⟩ := hf.rothberger U' hι hU'_open (fun n => (hU'_cover n).symm)
      refine ⟨j, ?_⟩
      have h_eq : ∀ n, U n (j n) = f '' (U' n (j n)) := fun n => (f.image_preimage (U n (j n))).symm
      calc univ = f '' univ := (Set.image_univ_of_surjective f.surjective).symm
        _ = f '' (⋃ n, U' n (j n)) := by rw [← hj]
        _ = (⋃ n, f '' (U' n (j n))) := by rw [Set.image_iUnion]
        _ = (⋃ n, U n (j n)) := by simp_rw [h_eq]
    constructor
    intro n
    have h_n : RothbergerSpace (Fin n → _) := h.omega_rothberger n
    let e : (Fin n → _) ≃ₜ (Fin n → _) := Homeomorph.piCongrRight (fun _ => φ)
    exact roth_pres e h_n

end PiBase.Formal
