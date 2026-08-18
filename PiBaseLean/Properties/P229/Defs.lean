module

public import PiBaseLean.AdditionalDefs.Constructions
public import PiBaseLean.Properties.Bundled.Defs
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic

@[expose] public section

open Topology Set Filter

namespace PiBase

/- 229. Semilocally simply connected -/
class SemilocallySimplyConnectedSpace (X : Type*) [TopologicalSpace X] : Prop where
  homo_trivial (x : X) : ∃ U : Set X, ∃ hU : U ∈ 𝓝 x,
    HasTrivialFundGroupImageAt ⟨Subtype.val, continuous_subtype_val⟩ ⟨x, mem_of_mem_nhds hU⟩

section FundGroupImage

variable {A B Z W : Type*} [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace Z]
  [TopologicalSpace W]

/-- `HasTrivialFundGroupImageAt` stated on elements of the fundamental group. -/
private theorem hasTrivialFundGroupImageAt_iff {f : C(A, B)} {a : A} :
    HasTrivialFundGroupImageAt f a ↔ ∀ p, FundamentalGroup.map f a p = 1 := by
  simp [HasTrivialFundGroupImageAt, MonoidHom.range_eq_bot_iff, DFunLike.ext_iff]

/-- Functoriality of `FundamentalGroup.map`, stated on elements. -/
private theorem fundGroup_map_comp (f : C(A, B)) (g : C(B, Z)) (a : A) (p : FundamentalGroup A a) :
    FundamentalGroup.map (g.comp f) a p =
      FundamentalGroup.map g (f a) (FundamentalGroup.map f a p) :=
  Path.Homotopic.Quotient.map_comp

/-- A map factoring through `f` has trivial fundamental group image whenever `f` does. -/
private theorem hasTrivialFundGroupImageAt_comp (e : C(A, B)) (f : C(B, Z)) (g : C(Z, W)) (a : A)
    (h : HasTrivialFundGroupImageAt f (e a)) :
    HasTrivialFundGroupImageAt (g.comp (f.comp e)) a := by
  rw [hasTrivialFundGroupImageAt_iff] at h ⊢
  intro p
  rw [fundGroup_map_comp (f.comp e) g a p, fundGroup_map_comp e f a p, h, map_one]

end FundGroupImage

/-- Semilocal simple connectedness is transported along a homeomorphism.

Given `U ∈ 𝓝 (e.symm y)` witnessing the property at `e.symm y`, the neighbourhood
`e.symm ⁻¹' U ∈ 𝓝 y` works at `y`: its inclusion into `Y` factors as
`e ∘ (U ↪ X) ∘ (e.symm ⁻¹' U ≃ₜ U)`, so functoriality of `FundamentalGroup.map` kills it. -/
theorem semilocallySimplyConnectedSpace_of_homeomorph {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] (e : X ≃ₜ Y) (h : SemilocallySimplyConnectedSpace X) :
    SemilocallySimplyConnectedSpace Y where
  homo_trivial y := by
    obtain ⟨U, hU, hUtriv⟩ := h.homo_trivial (e.symm y)
    have hV : e.symm ⁻¹' U ∈ 𝓝 y := e.continuous_symm.continuousAt.preimage_mem_nhds hU
    refine ⟨e.symm ⁻¹' U, hV, ?_⟩
    let eU : ↥(e.symm ⁻¹' U) ≃ₜ ↥U := e.symm.sets (t := U) rfl
    let r : C(↥(e.symm ⁻¹' U), ↥U) := ⟨eU, eU.continuous⟩
    let iU : C(↥U, X) := ⟨Subtype.val, continuous_subtype_val⟩
    let eC : C(X, Y) := ⟨e, e.continuous⟩
    have hcomp : eC.comp (iU.comp r) =
        (⟨Subtype.val, continuous_subtype_val⟩ : C(↥(e.symm ⁻¹' U), Y)) :=
      ContinuousMap.ext fun v => e.apply_symm_apply v.val
    rw [← hcomp]
    exact hasTrivialFundGroupImageAt_comp r iU eC _ hUtriv

end PiBase

namespace PiBase.Formal

open PiBase

def P229 : Property where
  toPred := SemilocallySimplyConnectedSpace
  well_defined φ hX := semilocallySimplyConnectedSpace_of_homeomorph φ hX

end PiBase.Formal
