module

public import Mathlib.Topology.NoetherianSpace
public import PiBaseLean.Properties.Bundled.Defs

@[expose] public section

open TopologicalSpace

namespace PiBase

/- 226. Artinian -/
abbrev ArtinianSpace (X : Type*) [TopologicalSpace X] := WellFoundedGT (Closeds X)

end PiBase

namespace PiBase.Formal

universe u

def P226 : Property where
  toPred := ArtinianSpace
  well_defined {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
      (φ : X ≃ₜ Y) (h : ArtinianSpace X) : ArtinianSpace Y := by
    unfold ArtinianSpace at *
    let f : Closeds Y → Closeds X := fun s =>
      ⟨φ ⁻¹' (s : Set Y), φ.isClosed_preimage.mpr s.isClosed⟩
    have hf_surj : Function.Surjective f := by
      intro t
      refine ⟨⟨φ '' (t : Set X), φ.isClosed_image.mpr t.isClosed⟩, Closeds.ext ?_⟩
      change φ ⁻¹' (φ '' (t : Set X)) = (t : Set X)
      exact Set.preimage_image_eq _ φ.injective
    have hf_le_iff : ∀ (a b : Closeds Y), a ≤ b ↔ f a ≤ f b :=
      fun a b => φ.surjective.preimage_subset_preimage_iff.symm
    have hf_gt_iff : ∀ (a b : Closeds Y), (a > b) ↔ (f a > f b) := by
      intro a b
      simp only [gt_iff_lt, lt_iff_le_not_ge, hf_le_iff]
    have hwf_iff : WellFounded (fun (a b : Closeds Y) => a > b) ↔
        WellFounded (fun (a b : Closeds X) => a > b) :=
      Function.Surjective.wellFounded_iff hf_surj (fun {a b} => hf_gt_iff a b)
    exact ⟨hwf_iff.mpr h.wf⟩

end PiBase.Formal
