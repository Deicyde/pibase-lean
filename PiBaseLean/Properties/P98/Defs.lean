module

public import Mathlib.Order.BourbakiWitt
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Homeomorph.Lemmas
public import PiBaseLean.Properties.Bundled.Defs

@[expose] public section

open Topology Set Function Filter TopologicalSpace Set.Notation

namespace PiBase

/- 98. k ω 1 space -/
class kω1Space (X : Type*) [TopologicalSpace X] : Prop where
  k_omega : ∃ K : ℕ → Set X, Monotone K ∧ univ = ⋃ n : ℕ, K n ∧
    (∀ n : ℕ, IsCompact (K n)) ∧
      ∀ s : Set X, IsOpen s ↔ ∀ n : ℕ, IsOpen ((K n) ↓∩ s)

end PiBase

namespace PiBase.Formal

def P98 : Property where
  toPred := kω1Space
  well_defined φ h := by
    obtain ⟨K, hMono, hUniv, hComp, hOpen⟩ := h.k_omega
    refine ⟨⟨fun n => φ '' K n, ?_, ?_, fun n => (hComp n).image φ.continuous, ?_⟩⟩
    · intro a b hab
      exact Set.image_mono (hMono hab)
    · calc
        univ = φ '' univ := by rw [image_univ, EquivLike.range_eq_univ]
        _ = φ '' (⋃ n, K n) := by rw [← hUniv]
        _ = ⋃ n, φ '' K n := by rw [image_iUnion]
    · intro s
      constructor
      · intro hs n
        have hXn : IsOpen (K n ↓∩ φ ⁻¹' s) :=
          (hOpen _).mp (hs.preimage φ.continuous) n
        let e : (K n) ≃ₜ (φ '' K n) := φ.image (K n)
        have hEq : e ⁻¹' ((φ '' K n) ↓∩ s) = K n ↓∩ φ ⁻¹' s := by
          ext x
          rfl
        apply e.isOpen_preimage.mp
        rwa [hEq]
      · intro hAll
        have hPre : ∀ n, IsOpen (K n ↓∩ φ ⁻¹' s) := by
          intro n
          let e : (K n) ≃ₜ (φ '' K n) := φ.image (K n)
          have hYn : IsOpen ((φ '' K n) ↓∩ s) := hAll n
          have hEq : e ⁻¹' ((φ '' K n) ↓∩ s) = K n ↓∩ φ ⁻¹' s := by
            ext x
            rfl
          have hPreimage : IsOpen (e ⁻¹' ((φ '' K n) ↓∩ s)) :=
            e.isOpen_preimage.mpr hYn
          rwa [hEq] at hPreimage
        exact φ.isOpen_preimage.mp ((hOpen _).mpr hPre)

end PiBase.Formal
