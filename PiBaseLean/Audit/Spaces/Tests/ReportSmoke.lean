module

public meta import PiBaseLean.Audit.Spaces.Audit
public import PiBaseLean.Spaces.S1.Lemmas
public import PiBaseLean.Spaces.S4.Lemmas
public import PiBaseLean.Spaces.S10.Lemmas
public import PiBaseLean.Spaces.S189.Lemmas

open Lean
open PiBase.Audit.Spaces

run_cmd do
  let report ← Lean.Elab.Command.liftTermElabM buildAuditReport
  unless report.isSuccess do
    throwError "space audit unexpectedly failed:\n{report.toJson.pretty}"
  unless report.summary.spaces == 4 && report.summary.implemented == 4 do
    throwError "unexpected implemented-space summary: {repr report.summary}"
  unless report.summary.traits == 86 do
    throwError "unexpected total trait count: {report.summary.traits}"
  let expectedDirectCounts := #[
    ("S000001", 3),
    ("S000004", 3),
    ("S000010", 5),
    ("S000189", 3)
  ]
  for (spaceId, expectedCount) in expectedDirectCounts do
    let actualCount := match expectedCatalogMatches spaceId with
      | #[space] => space.directTraits.size
      | _ => 0
    unless actualCount == expectedCount do
      throwError "unexpected direct trait count for {spaceId}: {actualCount}"
  if let .error message := Json.parse report.toJsonString then
    throwError "audit JSON did not parse: {message}"

#assert_pibase_spaces
