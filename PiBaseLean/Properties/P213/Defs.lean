module

public import Mathlib.Topology.Metrizable.Basic
public import PiBaseLean.Properties.Bundled.Defs

@[expose] public section

open Topology Set Filter Function

namespace PiBase

/- 213. α₃ space -/
class α3Space (X : Type*) [τ : TopologicalSpace X] : Prop where
  subset_converge {x : X} {S : ℕ → ℕ → X} (S_inj : ∀ n, Injective (S n))
    (hS : ∀ n : ℕ, Tendsto (S n) atTop (𝓝 x)) : ∃ T : ℕ → X, Injective T ∧
      Tendsto T atTop (𝓝 x) ∧ range T ⊆ ⋃ n, range (S n) ∧
        {n | (range (S n) ∩ range T).Infinite}.Infinite

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

private theorem symm_image_range_inter (φ : X ≃ₜ Y) (f : ℕ → Y) (g : ℕ → X) :
    range (φ.symm ∘ f) ∩ range g = φ.symm '' (range f ∩ range (φ ∘ g)) := by
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

private theorem infinite_inter_iff (φ : X ≃ₜ Y) (f : ℕ → Y) (g : ℕ → X) :
    (range f ∩ range (φ ∘ g)).Infinite ↔ (range (φ.symm ∘ f) ∩ range g).Infinite := by
  rw [symm_image_range_inter φ f g, Set.infinite_image_iff φ.symm.injective.injOn]

private theorem infinite_setOf_infinite_inter (φ : X ≃ₜ Y) (S : ℕ → ℕ → Y) (T : ℕ → X)
    (h : {n | (range (φ.symm ∘ S n) ∩ range T).Infinite}.Infinite) :
    {n | (range (S n) ∩ range (φ ∘ T)).Infinite}.Infinite := by
  have hEq : {n | (range (φ.symm ∘ S n) ∩ range T).Infinite}
      = {n | (range (S n) ∩ range (φ ∘ T)).Infinite} := by
    ext n
    exact (infinite_inter_iff φ (S n) T).symm
  rwa [hEq] at h

end AlphaTransport

def P213 : Property where
  toPred := α3Space
  well_defined {X Y} _ _ φ h := by
    constructor
    intro y S S_inj hS
    obtain ⟨T, hT_inj, hT_tend, hT_sub, hT_infSet⟩ :=
      h.subset_converge (x := φ.symm y) (S := fun n => φ.symm ∘ S n)
        (fun n => φ.symm.injective.comp (S_inj n)) (fun n => tendsto_symm_comp φ (hS n))
    exact ⟨φ ∘ T, φ.injective.comp hT_inj, tendsto_comp_of_symm φ hT_tend,
      range_comp_subset φ S T hT_sub, infinite_setOf_infinite_inter φ S T hT_infSet⟩

end PiBase.Formal
