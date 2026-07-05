module

public import Mathlib.SetTheory.Cardinal.Aleph
public import Mathlib.Topology.Order.Basic

@[expose] public section

open Topology Ordinal

namespace PiBase.Spaces
namespace S207

/- Space 207: Cohen's modification of ω₁×(ω₁+1).
See https://topology.pi-base.org/spaces/S000207.
Carrier: the plain set-theoretic product of ω₁ (S35) with ω₁+1 (S36). Topology: NOT the
product topology — it is modified by declaring every point of ω₁×ω₁ isolated; each point
⟨α,ω₁⟩ with α>0 keeps the local base {(β,α]×(γ,ω₁] : β<α, γ<ω₁}, and ⟨0,ω₁⟩ keeps the
local base {{0}×(γ,ω₁] : γ<ω₁}. -/

/-- The first factor: ordinals below the least uncountable ordinal ω₁ (pi-Base S35's
carrier). -/
def S207.Fst : Type 1 := {o : Ordinal.{0} // o < ω₁}

/-- The second factor: ordinals up to and including ω₁ (pi-Base S36's carrier). -/
def S207.Snd : Type 1 := {o : Ordinal.{0} // o ≤ ω₁}

/-- Cohen's modification of ω₁×(ω₁+1) (pi-Base S207): the carrier is the plain
set-theoretic product ω₁×(ω₁+1). -/
def S207 : Type 1 := S207.Fst × S207.Snd

noncomputable instance : LinearOrder S207.Fst :=
  inferInstanceAs (LinearOrder {o : Ordinal.{0} // o < ω₁})

noncomputable instance : LinearOrder S207.Snd :=
  inferInstanceAs (LinearOrder {o : Ordinal.{0} // o ≤ ω₁})

/-- The zero point of the first factor. -/
noncomputable def S207.zeroFst : S207.Fst := ⟨0, omega_pos 1⟩

/-- The inclusion of the first factor into the second (every ordinal `< ω₁` is `≤ ω₁`). -/
def S207.fstToSnd (a : S207.Fst) : S207.Snd := ⟨a.1, a.2.le⟩

/-- The distinguished "top" point ω₁ of the second factor. -/
noncomputable def S207.top : S207.Snd := ⟨ω₁, le_refl ω₁⟩

/-- The generating open sets of the modified topology on `S207 = ω₁ × (ω₁+1)`:
* every singleton `{⟨a, b⟩}` with `b < ω₁` (making these points isolated);
* for `a > 0`, the sets `(b, a] × (γ, ω₁]` with `b < a`, `γ < ω₁`
  (a local base at `⟨a, ω₁⟩`); and
* the sets `{0} × (γ, ω₁]` with `γ < ω₁` (a local base at `⟨0, ω₁⟩`). -/
noncomputable def S207.generators : Set (Set S207) :=
  {s | ∃ (a : S207.Fst) (b : S207.Fst), s = {((a, S207.fstToSnd b) : S207)}} ∪
  {s | ∃ (a b : S207.Fst), 0 < a.1 ∧ b < a ∧ ∃ (γ : S207.Fst),
        s = (Set.Ioc b a) ×ˢ (Set.Ioc (S207.fstToSnd γ) S207.top)} ∪
  {s | ∃ (γ : S207.Fst),
        s = ({S207.zeroFst} : Set S207.Fst) ×ˢ (Set.Ioc (S207.fstToSnd γ) S207.top)}

instance : TopologicalSpace S207 := TopologicalSpace.generateFrom S207.generators

end S207
end PiBase.Spaces
