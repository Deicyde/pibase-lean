module

public import PiBaseLean.AdditionalDefs.Meta
public import PiBaseLean.Properties.P95.Defs

@[expose] public section

namespace PiBase

open Topology Filter Set Function TopologicalSpace

section Meta

universe u v

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

theorem Homeomorph.arcConnectedSpace [h : ArcConnectedSpace X] (f : X ≃ₜ Y) :
    ArcConnectedSpace Y := by
  constructor
  intro x y hxy
  have hxy' : f.symm x ≠ f.symm y := by
    intro heq
    apply hxy
    calc
      x = f (f.symm x) := (f.apply_symm_apply x).symm
      _ = f (f.symm y) := by rw [heq]
      _ = y := f.apply_symm_apply y
  obtain ⟨p, hp⟩ := h.joined hxy'
  have h_map : IsEmbedding (p.map f.continuous) := by
    have h_map_eq : (⇑(p.map f.continuous) : unitInterval → _) = f ∘ ⇑p := by
      ext t
      rfl
    rw [h_map_eq]
    exact f.isEmbedding.comp hp
  let q := (p.map f.continuous).cast (f.apply_symm_apply x).symm
    (f.apply_symm_apply y).symm
  refine ⟨q, ?_⟩
  simpa only [q, Path.cast_coe] using h_map

theorem WellDefined.arcConnectedSpace : WellDefined ArcConnectedSpace :=
  fun {_ _} _ _ h hX => Formal.P95.well_defined h.some hX

end Meta

end PiBase
