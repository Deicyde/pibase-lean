module

public import Mathlib.Topology.Order

@[expose] public section

/-!
# π-Base S4 — "Indiscrete topology on {0,1}"

*Prototype of the pi-base/data-mirroring layout (Felix's request on #1304).*

The space file carries only the **carrier + topology**. Its traits live one-per-file
under `Traits/`, and only the **asserted** traits — the facts π-Base cannot deduce
from other traits together with the theorems — get a file. Everything derivable
(compact, ¬T₀, Lindelöf, σ-compact, …) is left to the deduction engine; we do not
restate it here.

π-Base asserts exactly three traits for `S000004`:

| trait | property | value |
|---|---|---|
| `P125` | Has multiple points | `true` |
| `P129` | Indiscrete | `true` |
| `P175` | Cardinality ≥ 3 | `false` |

See <https://topology.pi-base.org/spaces/S000004>.
-/

namespace PiBase.Spaces

/-- π-Base **S4**: the indiscrete topology on the two-point set `Fin 2`. -/
def S4 : Type := Fin 2

/-- Its topology: the indiscrete (`⊤`) topology — every subset is open. -/
instance S4_top : TopologicalSpace S4 := ⊤

end PiBase.Spaces
