module

public import Mathlib.Topology.Metrizable.Basic
public import PiBaseLean.Properties.Bundled.Defs

@[expose] public section

open Topology Set Filter Function

namespace PiBase

/- 211. α₁.₅ space -/
class α15Space (X : Type*) [TopologicalSpace X] : Prop where
  subset_converge {x : X} {S : ℕ → ℕ → X} (S_inj : ∀ n, Injective (S n))
    (S_disj : Pairwise (fun n m ↦ range (S n) ∩ range (S m) = ∅))
    (hS : ∀ n : ℕ, Tendsto (S n) atTop (𝓝 x)) : ∃ T : ℕ → X, Injective T ∧
      Tendsto T atTop (𝓝 x) ∧ range T ⊆ ⋃ n, range (S n) ∧
        {n | (range (S n) \ range T).Finite}.Infinite

end PiBase

namespace PiBase.Formal

section AlphaTransport

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

private theorem mem_range_symm_comp (φ : X ≃ₜ Y) (f : ℕ → Y) (w : X) :
    w ∈ range (φ.symm ∘ f) ↔ φ w ∈ range f := by
  constructor
  · rintro ⟨m, hm⟩
    refine ⟨m, ?_⟩
    rw [← hm]
    exact (φ.apply_symm_apply (f m)).symm
  · rintro ⟨m, hm⟩
    refine ⟨m, ?_⟩
    change φ.symm (f m) = w
    rw [hm, φ.symm_apply_apply]

private theorem mem_range_comp (φ : X ≃ₜ Y) (g : ℕ → X) (z : Y) :
    z ∈ range (φ ∘ g) ↔ φ.symm z ∈ range g := by
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    rw [← hk]
    exact (φ.symm_apply_apply (g k)).symm
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    change φ (g k) = z
    rw [hk, φ.apply_symm_apply]

private theorem tendsto_symm_comp (φ : X ≃ₜ Y) {f : ℕ → Y} {y : Y}
    (hf : Tendsto f atTop (𝓝 y)) : Tendsto (φ.symm ∘ f) atTop (𝓝 (φ.symm y)) :=
  (φ.symm.continuous.tendsto y).comp hf

private theorem tendsto_comp_of_symm (φ : X ≃ₜ Y) {g : ℕ → X} {y : Y}
    (hg : Tendsto g atTop (𝓝 (φ.symm y))) : Tendsto (φ ∘ g) atTop (𝓝 y) := by
  have h := (φ.continuous.tendsto (φ.symm y)).comp hg
  rwa [φ.apply_symm_apply y] at h

private theorem range_comp_subset (φ : X ≃ₜ Y) (f : ℕ → ℕ → Y) (g : ℕ → X)
    (h : range g ⊆ ⋃ n, range (φ.symm ∘ f n)) : range (φ ∘ g) ⊆ ⋃ n, range (f n) := by
  intro z hz
  rw [mem_range_comp φ g z] at hz
  obtain ⟨n, hn⟩ := mem_iUnion.1 (h hz)
  refine mem_iUnion.2 ⟨n, ?_⟩
  have hmem := (mem_range_symm_comp φ (f n) (φ.symm z)).1 hn
  rwa [φ.apply_symm_apply] at hmem

private theorem symm_range_inter_symm (φ : X ≃ₜ Y) (f₁ f₂ : ℕ → Y) :
    range (φ.symm ∘ f₁) ∩ range (φ.symm ∘ f₂) = φ.symm '' (range f₁ ∩ range f₂) := by
  ext w
  constructor
  · rintro ⟨hw₁, hw₂⟩
    exact ⟨φ w, ⟨(mem_range_symm_comp φ f₁ w).1 hw₁, (mem_range_symm_comp φ f₂ w).1 hw₂⟩,
      φ.symm_apply_apply w⟩
  · rintro ⟨z, ⟨hz₁, hz₂⟩, rfl⟩
    refine ⟨(mem_range_symm_comp φ f₁ (φ.symm z)).2 ?_,
      (mem_range_symm_comp φ f₂ (φ.symm z)).2 ?_⟩
    · rwa [φ.apply_symm_apply]
    · rwa [φ.apply_symm_apply]

private theorem symm_pairwise_disjoint (φ : X ≃ₜ Y) (S : ℕ → ℕ → Y)
    (h : Pairwise fun n m ↦ range (S n) ∩ range (S m) = ∅) :
    Pairwise fun n m ↦ range (φ.symm ∘ S n) ∩ range (φ.symm ∘ S m) = ∅ := by
  intro n m hnm
  rw [symm_range_inter_symm φ (S n) (S m), h hnm, Set.image_empty]

private theorem symm_image_range_diff (φ : X ≃ₜ Y) (f : ℕ → Y) (g : ℕ → X) :
    range (φ.symm ∘ f) \ range g = φ.symm '' (range f \ range (φ ∘ g)) := by
  ext w
  constructor
  · rintro ⟨hw₁, hw₂⟩
    refine ⟨φ w, ⟨(mem_range_symm_comp φ f w).1 hw₁, ?_⟩, φ.symm_apply_apply w⟩
    rw [mem_range_comp φ g (φ w), φ.symm_apply_apply]
    exact hw₂
  · rintro ⟨z, ⟨hz₁, hz₂⟩, rfl⟩
    rw [mem_range_comp φ g z] at hz₂
    refine ⟨(mem_range_symm_comp φ f (φ.symm z)).2 ?_, hz₂⟩
    rwa [φ.apply_symm_apply]

private theorem finite_diff_iff (φ : X ≃ₜ Y) (f : ℕ → Y) (g : ℕ → X) :
    (range f \ range (φ ∘ g)).Finite ↔ (range (φ.symm ∘ f) \ range g).Finite := by
  rw [symm_image_range_diff φ f g, Set.finite_image_iff φ.symm.injective.injOn]

private theorem infinite_setOf_finite_diff (φ : X ≃ₜ Y) (S : ℕ → ℕ → Y) (T : ℕ → X)
    (h : {n | (range (φ.symm ∘ S n) \ range T).Finite}.Infinite) :
    {n | (range (S n) \ range (φ ∘ T)).Finite}.Infinite := by
  have hEq : {n | (range (φ.symm ∘ S n) \ range T).Finite}
      = {n | (range (S n) \ range (φ ∘ T)).Finite} := by
    ext n
    exact (finite_diff_iff φ (S n) T).symm
  rwa [hEq] at h

end AlphaTransport

def P211 : Property where
  toPred := α15Space
  well_defined {X Y} _ _ φ h := by
    constructor
    intro y S S_inj S_disj hS
    obtain ⟨T, hT_inj, hT_tend, hT_sub, hT_inf⟩ :=
      h.subset_converge (x := φ.symm y) (S := fun n => φ.symm ∘ S n)
        (fun n => φ.symm.injective.comp (S_inj n)) (symm_pairwise_disjoint φ S S_disj)
        (fun n => tendsto_symm_comp φ (hS n))
    exact ⟨φ ∘ T, φ.injective.comp hT_inj, tendsto_comp_of_symm φ hT_tend,
      range_comp_subset φ S T hT_sub, infinite_setOf_finite_diff φ S T hT_inf⟩

end PiBase.Formal
