module

public import PiBaseLean.Audit.Spaces.Registry
public import PiBaseLean.Spaces.S1.Lemmas

open Lean

open PiBase.Audit.Spaces

register_space S000001
  carrier PiBase.S1
  canonical PiBase.S1_canonicalHomeomorph
  assumptions []

register_certificate S000001 P000052 true
  proof PiBase.Formal.S1_P52
  provenance direct
  assumptions []

run_cmd do
  let env ← getEnv
  let space ← match getSpaceById env "S000001" with
    | .ok entry => pure entry
    | .error message => throwError message
  unless space.carrier == ``PiBase.S1 &&
      space.canonicalHomeomorph == ``PiBase.S1_canonicalHomeomorph &&
      space.assumptionIds.isEmpty do
    throwError "unexpected S000001 space registration: {repr space}"
  let certificate ← match getCertificate env "S000001" "P000052" with
    | .ok entry => pure entry
    | .error message => throwError message
  unless certificate.property == ``PiBase.Formal.P52 &&
      certificate.proof == ``PiBase.Formal.S1_P52 &&
      certificate.polarity &&
      certificate.provenance == .direct &&
      certificate.assumptionIds.isEmpty do
    throwError "unexpected S000001/P000052 certificate registration: {repr certificate}"
