module

public import PiBaseLean.Bundled.Independent

/-! This file develops the machinery to stating the ultimate goal of this project. -/

universe u

@[expose] public section

namespace PiBase.Formal

def implicationSet : List Property.{u} → Set (Property.{u} × Property.{u})
  | [] => ∅
  | a :: l => (implicationSet l) ∪ {(a, i) | i ∈ l} ∪ {(a, iᶜ) | i ∈ l}

def propertyPairToLe (e : Property.{u} × Property.{u}) : Prop :=
  e.1 ≤ e.2

def DecidesPropertySet (s a b c : Set Prop) : Prop :=
  a ∪ b ∪ c = s ∧ (∀ i ∈ a, i) ∧ (∀ i ∈ b, ¬ i) ∧ (∀ i ∈ c, Independent.{u} i)

end PiBase.Formal
