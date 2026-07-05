module

public import PiBaseLean.Spaces.S79.Defs
public import Mathlib.SetTheory.Cardinal.Arithmetic

public import PiBaseLean.Spaces.Bundled.Defs

@[expose] public section

open Topology Ordinal OnePoint Cardinal Set

namespace PiBase.Spaces
namespace S90

-- Stage 1: build T = S88 (Tychonoff corkscrew) inline, as a quotient.

/-- `Y`, the deleted Tychonoff plank (pi-Base S79), the base space for the
Jones-machine (double-sided) construction. -/
abbrev S90.Y : Type 1 := S79

/-- `H = ω₁ × {ω}`, the "row ω" boundary of `Y`: points whose second (Tychonoff-plank)
coordinate is the point at infinity. -/
def S90.H : Set S90.Y := {y : S90.Y | y.1.2 = (∞ : S78.Snd)}

/-- `K = {ω₁} × ω`, the "column ω₁" boundary of `Y`: points whose first
(Tychonoff-plank) coordinate is `ω₁`. -/
def S90.K : Set S90.Y := {y : S90.Y | y.1.1 = (⟨ω₁, le_refl ω₁⟩ : S78.Fst)}

/-- `H` and `K` are disjoint in `Y` (they would only meet at the corner point
`(ω₁, ω)`, which is exactly the point deleted from `S78` to form `Y = S79`). -/
theorem S90.H_disjoint_K : Disjoint S90.H S90.K := by
  rw [Set.disjoint_iff]
  rintro y ⟨hH, hK⟩
  exact y.2 (Prod.ext hK hH)

/-- The raw (pre-quotient) carrier: two copies-indexed-by-`ℤ` of `Y`, plus two
extra points `p⁻, p⁺` (encoded as `Bool`, `false ↦ p⁻`, `true ↦ p⁺`). -/
def S90.Z' : Type 1 := (S90.Y × ℤ) ⊕ Bool

instance : TopologicalSpace S90.Z' :=
  inferInstanceAs (TopologicalSpace ((S90.Y × ℤ) ⊕ Bool))

/-- The canonical-representative retraction on `Y × ℤ` realizing the gluing
`(x, 2n) ∼ (x, 2n+1)` for `x ∈ H` and `(x, 2n-1) ∼ (x, 2n)` for `x ∈ K`: for
`x ∈ H` we round the ℤ-coordinate down to the nearest even integer, for `x ∈ K`
we round it down to the nearest odd integer, and elsewhere we leave it alone.
Since `H` and `K` are disjoint this is a well-defined function. -/
noncomputable def S90.retr (p : S90.Y × ℤ) : S90.Y × ℤ :=
  open Classical in
  if p.1 ∈ S90.H then (p.1, if p.2 % 2 = 0 then p.2 else p.2 - 1)
  else if p.1 ∈ S90.K then (p.1, if p.2 % 2 ≠ 0 then p.2 else p.2 - 1)
  else p

/-- The retraction on the full raw carrier `Z'`: acts via `retr` on the
`Y × ℤ` summand, and is the identity on the two extra points `p⁻, p⁺`. -/
noncomputable def S90.Z'.retr : S90.Z' → S90.Z' :=
  Sum.map S90.retr id

/-- The gluing equivalence relation on `Z'`, realized as the kernel of the
canonical-representative retraction. -/
noncomputable def S90.T.setoid : Setoid S90.Z' := Setoid.ker S90.Z'.retr

/-- Tychonoff corkscrew `T = DJ(Y, H, K)` (pi-Base S88), realized as the
quotient of `Z' = (Y × ℤ) ⊕ Bool` by the gluing relation identifying
`(x, 2n) ∼ (x, 2n+1)` for `x ∈ H` and `(x, 2n-1) ∼ (x, 2n)` for `x ∈ K`. -/
def S90.T : Type 1 := Quotient S90.T.setoid

noncomputable instance : TopologicalSpace S90.T :=
  inferInstanceAs (TopologicalSpace (Quotient S90.T.setoid))

/-- The distinguished point `p⁻` of `T` (the class of the `false` summand of `Z'`). -/
noncomputable def S90.aneg : S90.T := Quotient.mk _ (Sum.inr false)

/-- The distinguished point `p⁺` of `T` (the class of the `true` summand of `Z'`). -/
noncomputable def S90.apos : S90.T := Quotient.mk _ (Sum.inr true)

-- Stage 2: cardinality bookkeeping needed to build the fixed bijection `Γ`.

/-- `#{o : Ordinal // o < ω₁} = ℵ₁`. -/
theorem S90.mk_Iio_omega1 : #(Iio (ω₁ : Ordinal.{0})) = (ℵ₁ : Cardinal.{1}) := by
  rw [mk_Iio_ordinal, ← ord_aleph 1, card_ord]
  simp

/-- `#{o : Ordinal // o ≤ ω₁} ≤ ℵ₁` (an upper bound; equality also holds but is not needed). -/
theorem S90.mk_Iic_omega1_le : #{o : Ordinal.{0} // o ≤ ω₁} ≤ (ℵ₁ : Cardinal.{1}) := by
  have key : #{o : Ordinal.{0} // o ≤ ω₁} ≤ #((Iio (ω₁ : Ordinal.{0})) ⊕ PUnit.{1}) := by
    apply mk_le_of_injective
      (f := fun p => if h : p.1 < ω₁ then Sum.inl ⟨p.1, h⟩ else Sum.inr PUnit.unit)
    intro p q hpq
    by_cases hp : p.1 < ω₁ <;> by_cases hq : q.1 < ω₁ <;>
      simp only [hp, hq, dif_pos, dif_neg, not_false_iff, Sum.inl.injEq, reduceCtorEq] at hpq
    · exact Subtype.ext (by injection hpq)
    · exact Subtype.ext
        ((le_antisymm p.2 (not_lt.mp hp)).trans (le_antisymm q.2 (not_lt.mp hq)).symm)
  have h2 : #((Iio (ω₁ : Ordinal.{0})) ⊕ PUnit.{1}) = (ℵ₁ : Cardinal.{1}) + 1 := by
    rw [Cardinal.mk_sum, S90.mk_Iio_omega1]; simp
  have hle : (ℵ₀ : Cardinal.{1}) ≤ (ℵ₁ : Cardinal.{1}) := aleph0_le_aleph 1
  have h3 : (ℵ_ 1 : Cardinal.{1}) + 1 = ℵ_ 1 := add_one_eq hle
  exact key.trans (h2.le.trans h3.le)

/-- `#S78 ≤ ℵ₁` (an upper bound; equality also holds but is not needed). -/
theorem S90.mk_S78_le : #S78 ≤ (ℵ₁ : Cardinal.{1}) := by
  show #(S78.Fst × S78.Snd) ≤ _
  rw [Cardinal.mk_prod]
  have h20 : #S78.Snd = ℵ₀ := by
    have : Countable S78.Snd := inferInstanceAs (Countable (Option ℕ))
    have : Infinite S78.Snd := OnePoint.infinite
    exact Cardinal.mk_eq_aleph0 _
  have h0 : (ℵ₀ : Cardinal.{1}) ≤ ℵ₁ := aleph0_le_aleph 1
  simp only [h20, Cardinal.lift_aleph0, Cardinal.lift_id']
  calc #S78.Fst * ℵ₀ ≤ (ℵ₁ : Cardinal.{1}) * ℵ₀ := mul_le_mul_right' S90.mk_Iic_omega1_le ℵ₀
    _ = ℵ₁ := Cardinal.mul_eq_left h0 h0 Cardinal.aleph0_ne_zero

/-- `#Y ≤ ℵ₁` (an upper bound; equality also holds but is not needed). -/
theorem S90.mk_Y_le : #S90.Y ≤ (ℵ₁ : Cardinal.{1}) :=
  le_trans (mk_le_of_injective (f := fun p => p.1) (fun _ _ hab => Subtype.ext hab)) S90.mk_S78_le

/-- `#Z' ≤ ℵ₁` (an upper bound; equality also holds but is not needed). -/
theorem S90.mk_Z'_le : #S90.Z' ≤ (ℵ₁ : Cardinal.{1}) := by
  have h0 : (ℵ₀ : Cardinal.{1}) ≤ ℵ₁ := aleph0_le_aleph 1
  have hprod : #(S90.Y × ℤ) ≤ (ℵ₁ : Cardinal.{1}) := by
    rw [Cardinal.mk_prod]
    have hZ' : #ℤ = ℵ₀ := by
      have : Countable ℤ := inferInstance
      have : Infinite ℤ := inferInstance
      exact Cardinal.mk_eq_aleph0 _
    simp only [hZ', Cardinal.lift_aleph0, Cardinal.lift_id']
    calc #S90.Y * ℵ₀ ≤ (ℵ₁ : Cardinal.{1}) * ℵ₀ := mul_le_mul_right' S90.mk_Y_le ℵ₀
      _ = ℵ₁ := Cardinal.mul_eq_left h0 h0 Cardinal.aleph0_ne_zero
  have hbool : Cardinal.lift.{1, 0} #Bool ≤ (ℵ₁ : Cardinal.{1}) := by
    have hlt : #Bool < (ℵ₀ : Cardinal.{0}) := Cardinal.mk_lt_aleph0
    have hlift : Cardinal.lift.{1, 0} #Bool < Cardinal.lift.{1, 0} (ℵ₀ : Cardinal.{0}) :=
      Cardinal.lift_lt.mpr hlt
    rw [Cardinal.lift_aleph0] at hlift
    exact hlift.le.trans h0
  calc #S90.Z' = Cardinal.lift.{0, 1} #(S90.Y × ℤ) + Cardinal.lift.{1, 0} #Bool :=
        Cardinal.mk_sum _ _
    _ = #(S90.Y × ℤ) + Cardinal.lift.{1, 0} #Bool := by rw [Cardinal.lift_id']
    _ ≤ ℵ₁ + ℵ₁ := add_le_add hprod hbool
    _ = ℵ₁ := Cardinal.add_eq_self h0

/-- `#T ≤ ℵ₁` (an upper bound; equality also holds but is not needed). -/
theorem S90.mk_T_le : #S90.T ≤ (ℵ₁ : Cardinal.{1}) :=
  le_trans Cardinal.mk_quotient_le S90.mk_Z'_le

/-- `T' = T \ {a⁻, a⁺}`, the carrier used for `X` below. -/
def S90.T' : Type 1 := {t : S90.T // t ≠ S90.aneg ∧ t ≠ S90.apos}

/-- `#T' ≤ ℵ₁` (an upper bound; equality also holds but is not needed). -/
theorem S90.mk_T'_le : #S90.T' ≤ (ℵ₁ : Cardinal.{1}) :=
  le_trans (mk_le_of_injective (f := fun p => p.1) (fun _ _ hab => Subtype.ext hab)) S90.mk_T_le

/-- An explicit point of `Y`, witnessing `Y` (and hence `T'`) is nonempty:
`(0, 0) : [0,ω₁] × [0,ω]`, which is not the deleted corner `(ω₁, ω)` since its
second coordinate `0 ≠ ∞`. -/
def S90.y0 : S90.Y :=
  Subtype.mk ((⟨0, bot_le⟩, ((0 : ℕ) : OnePoint ℕ)) : S78) (by
    intro h
    have := congrArg Prod.snd h
    simp only [S79.corner] at this
    exact OnePoint.coe_ne_infty 0 this)

/-- The quotient class of `(y0, 0)` differs from both `a⁻` and `a⁺` (their classes
come from the `Bool` summand of `Z'`, disjoint by construction from the `Y × ℤ`
summand `(y0, 0)` sits in), witnessing `T'` is nonempty. -/
theorem S90.t0_ne_aneg_apos :
    (Quotient.mk S90.T.setoid (Sum.inl (S90.y0, (0:ℤ))) : S90.T) ≠ S90.aneg ∧
    (Quotient.mk S90.T.setoid (Sum.inl (S90.y0, (0:ℤ))) : S90.T) ≠ S90.apos := by
  refine ⟨?_, ?_⟩ <;>
  · show (Quotient.mk S90.T.setoid _ : S90.T) ≠ Quotient.mk S90.T.setoid _
    rw [Ne, Quotient.eq]
    show ¬ Setoid.ker S90.Z'.retr _ _
    rw [Setoid.ker_def]
    simp [S90.Z'.retr]

/-- An explicit point of `T'`, witnessing `T'` is nonempty. -/
noncomputable def S90.t0 : S90.T' :=
  Subtype.mk (Quotient.mk S90.T.setoid (Sum.inl (S90.y0, (0:ℤ)))) S90.t0_ne_aneg_apos

instance : Nonempty S90.T' := ⟨S90.t0⟩

/-- `Λ = {λ : Ordinal // λ < ω₁}`, the index set `ω₁` ranges over: `#Λ = ℵ₁`. -/
def S90.Lam : Type 1 := {o : Ordinal.{0} // o < ω₁}

theorem S90.mk_Lam : #S90.Lam = (ℵ₁ : Cardinal.{1}) := S90.mk_Iio_omega1

/-- `X = T' × Λ`, the carrier of Hewitt's condensed corkscrew (pi-Base S90). -/
def S90.X : Type 1 := S90.T' × S90.Lam

/-- `#X = ℵ₁`. -/
theorem S90.mk_X : #S90.X = (ℵ₁ : Cardinal.{1}) := by
  apply le_antisymm
  · have hmp : #S90.X = #S90.T' * #S90.Lam := by
      show #(S90.T' × S90.Lam) = _
      rw [Cardinal.mk_prod (α := S90.T') (β := S90.Lam)]
      simp
    rw [hmp]
    calc #S90.T' * #S90.Lam ≤ (ℵ₁ : Cardinal.{1}) * ℵ₁ :=
          mul_le_mul' S90.mk_T'_le S90.mk_Lam.le
      _ = ℵ₁ := Cardinal.mul_eq_self (aleph0_le_aleph 1)
  · rw [← S90.mk_Lam]
    exact mk_le_of_injective (f := fun l => (S90.t0, l))
      (fun a b hab => (Prod.ext_iff.mp hab).2)

/-- `#(X × X) = ℵ₁ = #Λ`, so a bijection `Γ : X × X ≃ Λ` exists. -/
theorem S90.mk_XX_eq_Lam : #(S90.X × S90.X) = #S90.Lam := by
  rw [S90.mk_Lam]
  have hmp : #(S90.X × S90.X) = #S90.X * #S90.X := by
    rw [Cardinal.mk_prod (α := S90.X) (β := S90.X)]
    simp
  rw [hmp, S90.mk_X]
  exact Cardinal.mul_eq_self (aleph0_le_aleph 1)

/-- `Γ : X × X ≃ Λ`, a fixed bijection (obtained noncomputably from the
cardinality equality `#(X × X) = #Λ`). -/
noncomputable def S90.Gamma : S90.X × S90.X ≃ S90.Lam :=
  Classical.choice (Cardinal.eq.mp S90.mk_XX_eq_Lam)

end S90
end PiBase.Spaces

namespace PiBase.Formal

/-- π-Base S90 as a bundled `Space` (carrier + topology). -/
noncomputable def S90 : Space := ⟨PiBase.Spaces.S90.S90.T, inferInstance⟩

end PiBase.Formal
