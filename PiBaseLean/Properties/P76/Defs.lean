module

public import PiBaseLean.AdditionalDefs.Games
public import PiBaseLean.Properties.Bundled.Defs
public import PiBaseLean.Properties.P69.Defs
public import Mathlib.Topology.UniformSpace.Basic
public import Mathlib.Topology.UniformSpace.UniformEmbedding

@[expose] public section

universe u

namespace PiBase

/- 76. Proximal -/
class ProximalSpace (X : Type u) [τ : TopologicalSpace X] : Prop where
  proximal (h : Inhabited X) :
    ∃ t : UniformSpace X, t.toTopologicalSpace = τ ∧ HasWinningStrategyA (@proximalGame X t h)

end PiBase

namespace PiBase

open Set Filter Topology

/-! ### Transporting the proximal game along a homeomorphism -/

section Proximal

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

@[simp]
theorem prodMap_symm_prodMap (φ : X ≃ₜ Y) (p : X × X) :
    Prod.map (φ.symm : Y → X) φ.symm (Prod.map (φ : X → Y) φ p) = p := by
  obtain ⟨x₁, x₂⟩ := p; simp

@[simp]
theorem prodMap_prodMap_symm (φ : X ≃ₜ Y) (p : Y × Y) :
    Prod.map (φ : X → Y) φ (Prod.map (φ.symm : Y → X) φ.symm p) = p := by
  obtain ⟨y₁, y₂⟩ := p; simp

/-- Taking preimages under `φ × φ` is a bijection between the relations on `Y` and the
relations on `X`. -/
def preimageRelEquiv (φ : X ≃ₜ Y) : Set (Y × Y) ≃ Set (X × X) where
  toFun V := Prod.map φ φ ⁻¹' V
  invFun U := Prod.map φ.symm φ.symm ⁻¹' U
  left_inv V := by ext p; simp
  right_inv U := by ext p; simp

@[simp]
theorem preimageRelEquiv_apply (φ : X ≃ₜ Y) (V : Set (Y × Y)) :
    preimageRelEquiv φ V = Prod.map φ φ ⁻¹' V := rfl

/-- The bijection between the moves of the proximal game on `Y` and the moves of the proximal
game on `X`. -/
def proximalMoveEquiv (φ : X ≃ₜ Y) : Y × Set (Y × Y) ≃ X × Set (X × X) :=
  (φ.symm.toEquiv).prodCongr (preimageRelEquiv φ)

@[simp]
theorem proximalMoveEquiv_fst (φ : X ≃ₜ Y) (p : Y × Set (Y × Y)) :
    (proximalMoveEquiv φ p).1 = φ.symm p.1 := rfl

@[simp]
theorem proximalMoveEquiv_snd (φ : X ≃ₜ Y) (p : Y × Set (Y × Y)) :
    (proximalMoveEquiv φ p).2 = Prod.map φ φ ⁻¹' p.2 := rfl

theorem prodMap_surjective (φ : X ≃ₜ Y) : Function.Surjective (Prod.map (φ : X → Y) φ) :=
  fun p ↦ ⟨Prod.map φ.symm φ.symm p, prodMap_prodMap_symm φ p⟩

@[simp]
theorem preimage_prodMap_subset_iff (φ : X ≃ₜ Y) (V W : Set (Y × Y)) :
    Prod.map φ φ ⁻¹' V ⊆ Prod.map φ φ ⁻¹' W ↔ V ⊆ W :=
  preimage_subset_preimage_iff (by rw [(prodMap_surjective φ).range_eq]; exact subset_univ V)

@[simp]
theorem preimage_prodMap_eq_iff (φ : X ≃ₜ Y) (V W : Set (Y × Y)) :
    Prod.map φ φ ⁻¹' V = Prod.map φ φ ⁻¹' W ↔ V = W :=
  preimage_eq_preimage (prodMap_surjective φ)

theorem preimage_eq_empty_iff_of_homeomorph (φ : X ≃ₜ Y) (S : Set Y) :
    φ ⁻¹' S = ∅ ↔ S = ∅ := by
  refine ⟨fun h ↦ ?_, fun h ↦ by rw [h, preimage_empty]⟩
  rw [← image_preimage_eq S φ.surjective, h, image_empty]

/-- The slice of a transported entourage is the preimage of the slice of the original one. -/
theorem slice_preimage_prodMap (φ : X ≃ₜ Y) (y : Y) (V : Set (Y × Y)) :
    Prod.mk (φ.symm y) ⁻¹' (Prod.map φ φ ⁻¹' V) = φ ⁻¹' (Prod.mk y ⁻¹' V) := by
  ext x; simp

/-- Convergence of a sequence can be transported along a homeomorphism. -/
theorem exists_tendsto_comp_iff (φ : X ≃ₜ Y) (f : ℕ → Y) :
    (∃ z : X, Tendsto (fun n ↦ φ.symm (f n)) atTop (𝓝 z)) ↔
      ∃ z : Y, Tendsto f atTop (𝓝 z) := by
  refine ⟨fun ⟨z, hz⟩ ↦ ⟨φ z, ?_⟩,
    fun ⟨z, hz⟩ ↦ ⟨φ.symm z, (φ.symm.continuous.tendsto z).comp hz⟩⟩
  simpa [Function.comp_def] using (φ.continuous.tendsto z).comp hz

end Proximal

end PiBase

namespace PiBase.Formal

open Set Filter Topology

def P76 : Property where
  toPred := ProximalSpace
  well_defined {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] (φ : X ≃ₜ Y) h := by
    constructor
    intro hY
    -- The default point of `X` has to stay reducible, so it is introduced with `let`.
    let hX : Inhabited X := ⟨φ.symm hY.default⟩
    obtain ⟨tX, htX, hwin⟩ := h.proximal hX
    subst htX
    -- Pull the uniformity back along `φ.symm`, keeping the topology on `Y` untouched.
    refine ⟨(UniformSpace.comap φ.symm tX).replaceTopology φ.symm.isInducing.eq_induced, rfl, ?_⟩
    set tY : UniformSpace Y :=
      (UniformSpace.comap φ.symm tX).replaceTopology φ.symm.isInducing.eq_induced with htY
    -- Entourages of `Y` correspond exactly to entourages of `X`.
    have hEnt : ∀ V : Set (Y × Y),
        V ∈ @uniformity Y tY ↔ Prod.map φ φ ⁻¹' V ∈ @uniformity X tX := by
      intro V
      have huniv : @uniformity Y tY
          = Filter.comap (Prod.map (φ.symm : Y → X) φ.symm) (@uniformity X tX) := rfl
      rw [huniv, Filter.mem_comap]
      refine ⟨fun hV ↦ ?_, fun hV ↦ ⟨Prod.map φ φ ⁻¹' V, hV, fun p hp ↦ ?_⟩⟩
      · obtain ⟨U, hU, hsub⟩ := hV
        refine Filter.mem_of_superset hU fun p hp ↦ hsub ?_
        simpa using hp
      · simpa using hp
    refine HasWinningStrategyA.of_equiv (proximalMoveEquiv φ) (fun b hb ↦ ?_) hwin
    have hd : proximalMoveEquiv φ (hY.default, univ) = (hX.default, univ) := by
      change (hX.default, Prod.map (φ : X → Y) φ ⁻¹' (univ : Set (Y × Y))) = (hX.default, univ)
      rw [preimage_univ]
    refine (isPayoff_ofAllowed_iff (proximalMoveEquiv φ) (fun l ↦ ?_) b ?_).mpr hb
    · -- The allowed moves correspond to each other.
      have hlast : (l.map (proximalMoveEquiv φ)).getLastD (hX.default, univ)
          = proximalMoveEquiv φ (l.getLastD (hY.default, univ)) := by
        rw [← hd, List.getLastD_map]
      have hlast1 : (l.map (proximalMoveEquiv φ)).dropLast.getLastD (hX.default, univ)
          = proximalMoveEquiv φ (l.dropLast.getLastD (hY.default, univ)) := by
        rw [← List.map_dropLast, ← hd, List.getLastD_map]
      have hlast2 : (l.map (proximalMoveEquiv φ)).dropLast.dropLast.getLastD (hX.default, univ)
          = proximalMoveEquiv φ (l.dropLast.dropLast.getLastD (hY.default, univ)) := by
        rw [← List.map_dropLast, ← List.map_dropLast, ← hd, List.getLastD_map]
      simp only [hlast, hlast1, hlast2, List.length_map, ne_eq, List.map_eq_nil_iff,
        proximalMoveEquiv_fst, proximalMoveEquiv_snd, hEnt, preimage_prodMap_subset_iff,
        preimage_prodMap_eq_iff, EmbeddingLike.apply_eq_iff_eq, slice_preimage_prodMap,
        mem_preimage, Homeomorph.apply_symm_apply]
    · -- The payoff conditions correspond to each other.
      change ((∃ z : Y, Tendsto (fun n ↦ (b n).1) atTop (𝓝 z)) ∨
          (⋂ n, Prod.mk (b (2 * n + 1)).1 ⁻¹' (b (2 * n + 1)).2) = ∅) ↔
        ((∃ z : X, Tendsto (fun n ↦ (proximalMoveEquiv φ (b n)).1) atTop (𝓝 z)) ∨
          (⋂ n, Prod.mk (proximalMoveEquiv φ (b (2 * n + 1))).1 ⁻¹'
            (proximalMoveEquiv φ (b (2 * n + 1))).2) = ∅)
      simp only [proximalMoveEquiv_fst, proximalMoveEquiv_snd, slice_preimage_prodMap,
        ← preimage_iInter, preimage_eq_empty_iff_of_homeomorph, exists_tendsto_comp_iff]

end PiBase.Formal
