#!/usr/bin/env python3
"""Fail when generated dashboard artifacts disagree with their manifest."""

from __future__ import annotations

import json
from collections import Counter
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
PUBLIC = ROOT / "dashboard" / "public"
DATA = PUBLIC / "data"


def load(path: Path):
    with path.open(encoding="utf-8") as handle:
        return json.load(handle)


def require(condition: bool, message: str) -> None:
    if not condition:
        raise SystemExit(f"dashboard integrity error: {message}")


def check_review(kind: str, expected: int) -> None:
    index = load(DATA / f"review-{kind}.json")
    entries = index["entries"]
    require(len(entries) == expected, f"{kind} review index has {len(entries)} entries, expected {expected}")
    require(len({entry["id"] for entry in entries}) == expected, f"{kind} review index has duplicate IDs")
    chunk_ids: set[str] = set()
    for chunk_number, relative in enumerate(index["chunks"]):
        path = PUBLIC / relative
        require(path.exists(), f"missing review chunk {relative}")
        payload = load(path)
        require(payload["chunk"] == chunk_number, f"review chunk number mismatch in {relative}")
        chunk_ids.update(entry["id"] for entry in payload["entries"])
    require(chunk_ids == {entry["id"] for entry in entries}, f"{kind} review chunks do not match their index")
    require(all(0 <= entry["chunk"] < len(index["chunks"]) for entry in entries), f"{kind} review entry has an invalid chunk")


def main() -> None:
    manifest = load(DATA / "dashboard.json")
    size = manifest["graph"]["size"]
    outcomes = (DATA / "outcomes.bin").read_bytes()
    witness_bytes = (DATA / "witnesses.bin").read_bytes()
    require(len(manifest["properties"]) == size, "property list does not match graph size")
    require(len(outcomes) == size * size, "outcome matrix dimensions are invalid")
    require(len(witness_bytes) == size * size * 2, "witness matrix dimensions are invalid")

    histogram = Counter(outcomes)
    expected = manifest["graph"]["counts"]
    require(histogram[0] == size, "diagonal cell count is invalid")
    for code, key in ((1, "explicitTrue"), (2, "derivedTrue"), (3, "false"), (4, "independent"), (5, "open")):
        require(histogram[code] == expected.get(key, 0), f"{key} count disagrees with outcome matrix")
    require(sum(histogram.values()) == size * size, "outcome matrix contains invalid status bytes")

    witnesses = [
        int.from_bytes(witness_bytes[index:index + 2], "little")
        for index in range(0, len(witness_bytes), 2)
    ]
    require(max(witnesses, default=0) <= len(manifest["spaces"]), "witness index is out of range")
    require(
        all((value > 0) == (state == 3) for value, state in zip(witnesses, outcomes, strict=True)),
        "witness matrix does not align with false outcomes",
    )

    frontier = manifest["frontier"]
    require(len(frontier) == expected.get("open", 0), "frontier size disagrees with open count")
    node_index = {item["id"]: index for index, item in enumerate(manifest["properties"])}
    require(
        all(outcomes[node_index[item["source"]] * size + node_index[item["target"]]] == 5 for item in frontier),
        "frontier contains a non-open pair",
    )

    summary = manifest["summary"]
    require(sum(manifest["trust"]["properties"].values()) == summary["propertyEntries"], "property trust totals disagree")
    require(sum(manifest["trust"]["theorems"].values()) == summary["theoremEntries"], "theorem trust totals disagree")
    require(sum(manifest["trust"]["spaces"].values()) == summary["spaceEntries"], "space trust totals disagree")
    require(
        summary["theoremDeclarations"]
        == summary["theoremEntries"] - manifest["trust"]["theorems"].get("missing-declaration", 0),
        "canonical theorem declaration count disagrees with trust ledger",
    )

    check_review("spaces", summary["spaceEntries"])
    check_review("properties", summary["propertyEntries"])
    check_review("theorems", summary["theoremEntries"])

    for artifact in manifest["downloads"]:
        require((PUBLIC / artifact["path"]).exists(), f"download is missing: {artifact['path']}")
    for page in ("blueprint.html", "review.html", "data.html"):
        require((PUBLIC / page).exists(), f"public page is missing: {page}")

    print(
        "dashboard integrity: "
        f"{size} nodes, {sum(histogram.values()):,} cells, "
        f"{len(frontier):,} frontier pairs, review chunks valid"
    )


if __name__ == "__main__":
    main()
