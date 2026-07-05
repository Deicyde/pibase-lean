module

public import Mathlib.Topology.Instances.Real.Lemmas

public import PiBaseLean.Spaces.Bundled.Defs

@[expose] public section

open Topology

namespace PiBase.Spaces
namespace S180

/- Space 180: Solomon's scattered space.
See https://topology.pi-base.org/spaces/S000180.
Constructed by R. C. Solomon (1976, doi:10.1112/blms/8.3.239) to give a T3.5 (P6),
scattered (P51) space that is not zero-dimensional (P50): a base set of cardinality 𝔠
with extra points `x_{r,s}` adjoined for every `r ∈ (0,1)` and `s` in a particular set
`F_r` of real sequences (each of cardinality at most `𝔠^ℵ₀ = 𝔠`); the discrete subspace
witnessing P65/¬P197 has cardinality 𝔠.
-- TODO: pi-Base's own record for S180 only sketches this shape (see the properties
-- README under P000065) and does not itself spell out the family `F_r` or the open
-- sets of Solomon's actual topology -- that detail lives only in the (paywalled)
-- 1976 paper. We therefore cannot faithfully reproduce the true topology from the
-- data available here. As a faithful placeholder we take the carrier to be `ℝ`
-- (cardinality 𝔠, matching P65) with the usual order/metric topology; this is
-- NOT claimed to be scattered, T3.5-but-not-zero-dimensional, or otherwise to
-- satisfy S180's asserted trait profile -- it only records the one concrete fact
-- pi-Base gives us (the base set has cardinality continuum). -/

/-- Solomon's scattered space (pi-Base S180). Carrier only faithfully recorded as a
set of cardinality 𝔠; the real construction (extra points `x_{r,s}`) is not
reproducible from the available pi-Base data -- see the `TODO` above. -/
def S180 : Type := ℝ

instance S180_top : TopologicalSpace S180 := inferInstanceAs (TopologicalSpace ℝ)

end S180
end PiBase.Spaces

namespace PiBase.Formal

/-- π-Base S180 as a bundled `Space` (carrier + topology). -/
noncomputable def S180 : Space := ⟨PiBase.Spaces.S180.S180, PiBase.Spaces.S180.S180_top⟩

end PiBase.Formal
