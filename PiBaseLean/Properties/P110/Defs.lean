module

public import Mathlib.Data.Countable.Defs
public import Mathlib.Topology.Defs.Filter
public import PiBaseLean.AdditionalDefs.Cover
public import PiBaseLean.Properties.Bundled.Defs

@[expose] public section

open Topology Set Filter

universe u

namespace PiBase

structure Development (X : Type u) [TopologicalSpace X] where
  idx : ℕ → Type u
  toCover : {n : ℕ} → (idx n) → Set X
  isOpen : ∀ᵉ (n : ℕ) (t : idx n), IsOpen (toCover t)
  isCover : ∀ (n : ℕ), ⋃ t : idx n, toCover t = univ
  isLocalBase (x : X) : HasBasis (𝓝 x) (fun _ ↦ True)  (fun n ↦ CoverStar (toCover (n := n)) x)

/- 110. Developable -/
class DevelopableSpace (X : Type u) [TopologicalSpace X] : Prop where
  developable : Nonempty (Development X)

end PiBase

namespace PiBase.Formal

def P110 : Property where
  toPred := DevelopableSpace
  well_defined φ h := by
    obtain ⟨⟨idx, toCover, isOpen, isCover, isLocalBase⟩⟩ := h.developable
    refine ⟨⟨⟨idx, fun {n} t => φ '' toCover t, fun n t => φ.isOpenMap _ (isOpen n t), ?_, ?_⟩⟩⟩
    · intro n
      calc (⋃ t : idx n, φ '' toCover t) = φ '' (⋃ t, toCover t) := by
            rw [image_iUnion]
        _ = φ '' univ := by rw [isCover n]
        _ = univ := by rw [image_univ, EquivLike.range_eq_univ]
    · intro y
      have hx :
          (𝓝 (φ.symm y)).HasBasis
            (fun _ => True) (fun n => CoverStar (toCover (n := n)) (φ.symm y)) :=
        isLocalBase (φ.symm y)
      have hEq : Filter.map φ (𝓝 (φ.symm y)) = 𝓝 y := by
        calc Filter.map φ (𝓝 (φ.symm y)) = 𝓝 (φ (φ.symm y)) := φ.map_nhds_eq (φ.symm y)
          _ = 𝓝 y := by rw [φ.apply_symm_apply]
      have hBasisY :
          (𝓝 y).HasBasis
            (fun _ => True) (fun n => φ '' CoverStar (toCover (n := n)) (φ.symm y)) := by
        rw [← hEq]
        exact hx.map φ
      have hStarEq : ∀ n, φ '' CoverStar (toCover (n := n)) (φ.symm y) =
          CoverStar (fun t : idx n => φ '' toCover t) y := by
        intro n
        ext y'
        simp only [CoverStar, mem_iUnion, mem_image]
        constructor
        · rintro ⟨x, ⟨i, hi_mem, hx_mem⟩, rfl⟩
          refine ⟨i, ⟨⟨φ.symm y, hi_mem, φ.apply_symm_apply y⟩, ?_⟩⟩
          exact ⟨x, hx_mem, rfl⟩
        · rintro ⟨i, ⟨⟨z, hz_mem, rfl⟩, hy_mem⟩⟩
          obtain ⟨x, hx_mem, rfl⟩ := hy_mem
          exact ⟨x, ⟨i, by simpa using hz_mem, hx_mem⟩, rfl⟩
      simp_rw [hStarEq] at hBasisY
      exact hBasisY

end PiBase.Formal
