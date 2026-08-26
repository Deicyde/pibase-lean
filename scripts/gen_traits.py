#!/usr/bin/env python3
"""Generate sound, reproducible Lean trait derivations from the pi-base catalog.

The catalog's asserted traits are direct proof obligations.  This script never
manufactures those proofs: it lists their expected declarations and generates
only consequences of formalized positive implications.  Supported deductions
are forward implication and constructive contraposition.

Examples:
  python3 scripts/gen_traits.py
  python3 scripts/gen_traits.py --emit S3
  python3 scripts/gen_traits.py --write S3 S4
  python3 scripts/gen_traits.py --check S3 S4
  python3 scripts/gen_traits.py --data data/traits.json
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from collections import defaultdict
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Iterable, Mapping, Sequence

REPO_ROOT = Path(__file__).resolve().parents[1]
DEFAULT_CATALOG = REPO_ROOT / "data" / "pibase.json"
DEFAULT_INDEPENDENCE = REPO_ROOT / "data" / "independence.json"
DEFAULT_LEAN_ROOT = REPO_ROOT
DEFAULT_LEMMAS_ROOT = REPO_ROOT / "PiBaseLean" / "Spaces"

GENERATED_IMPORTS_BEGIN = "-- BEGIN PIBASE TRAIT IMPORTS"
GENERATED_IMPORTS_END = "-- END PIBASE TRAIT IMPORTS"
GENERATED_BEGIN = "/- BEGIN PIBASE TRAIT DERIVATIONS -/"
GENERATED_END = "/- END PIBASE TRAIT DERIVATIONS -/"
_UID_RE = re.compile(r"([PST])(\d+)$", re.IGNORECASE)
_LEAN_NAME_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_'.]*$")
_CONDITIONAL_ASSUMPTIONS = {
    "CH": ("PiBase.ContinuumHypothesis", "continuumHypothesis"),
    "not CH": ("PiBase.NotContinuumHypothesis", "notContinuumHypothesis"),
    "MA": ("PiBase.MartinsAxiom", "martinsAxiom"),
    "GCH": (
        "PiBase.GeneralizedContinuumHypothesis",
        "generalizedContinuumHypothesis",
    ),
}

Literal = tuple[str, bool]
Derivation = tuple[str, str | None, tuple[Literal, ...]]


@dataclass(frozen=True)
class ConditionalBinder:
    type: str
    assumption_id: str


@dataclass(frozen=True)
class GenerationContext:
    catalog: Mapping[str, Any]
    lean_root: Path
    independence: Mapping[str, Any]

    @property
    def property_names(self) -> dict[str, str]:
        return {item["uid"]: item["name"] for item in self.catalog["properties"]}

    @property
    def space_names(self) -> dict[str, str]:
        return {item["uid"]: item["name"] for item in self.catalog["spaces"]}

    @property
    def seeds(self) -> dict[str, dict[str, bool]]:
        result: defaultdict[str, dict[str, bool]] = defaultdict(dict)
        for trait in self.catalog["traits"]:
            result[trait["space"]][trait["property"]] = trait["value"]
        return dict(result)

    @property
    def available_properties(self) -> set[str]:
        return available("P", self.lean_root)

    @property
    def available_theorems(self) -> list[Mapping[str, Any]]:
        return [
            item
            for item in self.catalog["theorems"]
            if theorem_matches_lean(item, self.lean_root)
        ]


def load_json(path: Path) -> Any:
    with path.open(encoding="utf-8") as handle:
        return json.load(handle)


def normalize_uid(value: str, kind: str) -> str:
    match = _UID_RE.fullmatch(value)
    if not match or match.group(1).upper() != kind:
        raise ValueError(f"expected {kind}<number>, got {value!r}")
    return f"{kind}{int(match.group(2)):06d}"


def short_uid(uid: str) -> str:
    match = _UID_RE.fullmatch(uid)
    if not match:
        raise ValueError(f"invalid pi-base uid: {uid!r}")
    return f"{match.group(1).upper()}{int(match.group(2))}"


def atoms(formula: Mapping[str, Any]) -> Iterable[Literal]:
    kind = formula["kind"]
    if kind == "atom":
        yield formula["property"], formula["value"]
        return
    if kind != "and":
        raise ValueError(f"unsupported formula kind: {kind!r}")
    for subformula in formula["subs"]:
        yield from atoms(subformula)


def positive_implication(theorem: Mapping[str, Any]) -> tuple[tuple[Literal, ...], Literal] | None:
    """Return the executable literals for an entirely positive implication."""
    try:
        antecedents = tuple(atoms(theorem["when"]))
        conclusions = tuple(atoms(theorem["then"]))
    except (KeyError, TypeError, ValueError):
        return None
    if len(conclusions) != 1:
        return None
    conclusion = conclusions[0]
    if not antecedents or not conclusion[1] or any(not value for _, value in antecedents):
        return None
    return antecedents, conclusion


def close(
    seed: Mapping[str, bool],
    theorems: Sequence[Mapping[str, Any]],
    available_properties: set[str],
) -> tuple[dict[str, bool], dict[str, Derivation], list[str]]:
    """Close direct traits under positive implication and constructive contraposition."""
    known = {prop: value for prop, value in seed.items() if prop in available_properties}
    derivations: dict[str, Derivation] = {
        prop: ("direct", None, ()) for prop in known
    }
    order = list(known)
    executable = [
        (theorem, implication)
        for theorem in theorems
        if (implication := positive_implication(theorem)) is not None
    ]

    changed = True
    while changed:
        changed = False
        for theorem, (antecedents, conclusion) in executable:
            conclusion_prop, _ = conclusion

            if all(known.get(prop) is value for prop, value in antecedents):
                if conclusion_prop not in known:
                    known[conclusion_prop] = True
                    derivations[conclusion_prop] = (
                        "implication",
                        theorem["uid"],
                        antecedents,
                    )
                    order.append(conclusion_prop)
                    changed = True

            if known.get(conclusion_prop) is not False:
                continue
            unknown = [literal for literal in antecedents if literal[0] not in known]
            if len(unknown) != 1:
                continue
            target_prop, target_value = unknown[0]
            if not target_value or target_prop not in available_properties:
                continue
            others = tuple(literal for literal in antecedents if literal[0] != target_prop)
            if all(known.get(prop) is value for prop, value in others):
                known[target_prop] = False
                derivations[target_prop] = (
                    "contrapositive",
                    theorem["uid"],
                    (conclusion, *others),
                )
                order.append(target_prop)
                changed = True

    return known, derivations, order


def theorem_matches_lean(theorem: Mapping[str, Any], lean_root: Path | str) -> bool:
    """Check that a catalog implication agrees with the actual Lean `T<N>` statement."""
    implication = positive_implication(theorem)
    if implication is None:
        return False
    antecedents, conclusion = implication
    short = short_uid(theorem["uid"])
    source_path = Path(lean_root) / "PiBaseLean" / "Theorems" / short / "Theorem.lean"
    if not source_path.is_file():
        return False
    source = source_path.read_text(encoding="utf-8")
    match = re.search(
        rf"\btheorem\s+{re.escape(short)}\s*:\s*(.*?)\s*≤\s*(P\d+)\s*:=",
        source,
        re.DOTALL,
    )
    if match is None:
        return False
    lean_antecedents = tuple(
        f"P{int(number):06d}" for number in re.findall(r"\bP(\d+)\b", match.group(1))
    )
    lean_conclusion = f"P{int(match.group(2)[1:]):06d}"
    return (
        lean_antecedents == tuple(prop for prop, _ in antecedents)
        and lean_conclusion == conclusion[0]
    )


def available(kind: str, lean_root: Path | str) -> set[str]:
    """Return entities with their expected numbered Lean declaration."""
    directory = Path(lean_root) / "PiBaseLean" / {
        "P": "Properties",
        "T": "Theorems",
        "S": "Spaces",
    }[kind]
    source_name = {"P": "Defs.lean", "T": "Theorem.lean", "S": "Defs.lean"}[kind]
    declaration_kind = "(?:theorem|lemma)" if kind == "T" else "def"
    if not directory.is_dir():
        return set()
    result = set()
    for child in directory.iterdir():
        match = re.fullmatch(rf"{kind}(\d+)", child.name)
        source = child / source_name
        if not match or not source.is_file():
            continue
        number = int(match.group(1))
        declaration = re.compile(rf"\b{declaration_kind}\s+{kind}{number}\b")
        if declaration.search(source.read_text(encoding="utf-8")):
            result.add(f"{kind}{number:06d}")
    return result


def conditional_binders(
    space_uid: str, independence: Mapping[str, Any]
) -> tuple[ConditionalBinder, ...]:
    assumptions: list[str] = []
    for item in independence.get("conditionalSpaces", []):
        if item.get("space") == space_uid:
            assumptions.extend(item.get("assumptions", []))
    result = []
    seen = set()
    for assumption in assumptions:
        if assumption in seen:
            continue
        mapping = _CONDITIONAL_ASSUMPTIONS.get(assumption)
        if mapping is None:
            raise ValueError(
                f"conditional assumption {assumption!r} for {short_uid(space_uid)} "
                "has no registry mapping"
            )
        binder_type, assumption_id = mapping
        if not _LEAN_NAME_RE.fullmatch(binder_type):
            raise ValueError(
                f"conditional assumption {assumption!r} for {short_uid(space_uid)} "
                "has no valid Lean typeclass mapping"
            )
        seen.add(assumption)
        result.append(ConditionalBinder(binder_type, assumption_id))
    return tuple(result)


def theorem_name(space_uid: str, property_uid: str, value: bool) -> str:
    suffix = "" if value else "_not"
    return f"{short_uid(space_uid)}_{short_uid(property_uid)}{suffix}"


def carrier_name(space_uid: str) -> str:
    return f"PiBase.{short_uid(space_uid)}"


def goal(property_uid: str, value: bool, carrier: str) -> str:
    expression = f"{short_uid(property_uid)} {carrier}"
    return expression if value else f"¬ {expression}"


def binder_text(binders: Sequence[ConditionalBinder]) -> str:
    return "".join(f" [{binder.type}]" for binder in binders)


def assumption_text(binders: Sequence[ConditionalBinder]) -> str:
    return ", ".join(binder.assumption_id for binder in binders)


def render_certificate(
    space_uid: str,
    property_uid: str,
    value: bool,
    provenance: str,
    binders: Sequence[ConditionalBinder],
) -> str:
    proof = theorem_name(space_uid, property_uid, value)
    polarity = str(value).lower()
    return (
        f"register_certificate {space_uid} {property_uid} {polarity}\n"
        f"  proof PiBase.Formal.{proof}\n"
        f"  provenance {provenance}\n"
        f"  assumptions [{assumption_text(binders)}]"
    )


def reference(
    space_uid: str,
    property_uid: str,
    value: bool,
    binders: Sequence[ConditionalBinder],
) -> str:
    return theorem_name(space_uid, property_uid, value)


def antecedent_payload(
    space_uid: str,
    antecedents: Sequence[Literal],
    binders: Sequence[ConditionalBinder],
    replacement: tuple[str, str] | None = None,
) -> str:
    refs = []
    for prop, value in antecedents:
        if replacement is not None and prop == replacement[0]:
            refs.append(replacement[1])
        else:
            refs.append(reference(space_uid, prop, value, binders))
    if len(refs) == 1:
        return refs[0]
    return "⟨" + ", ".join(refs) + "⟩"


def render_derived_declaration(
    space_uid: str,
    property_uid: str,
    value: bool,
    derivation: Derivation,
    theorems_by_uid: Mapping[str, Mapping[str, Any]],
    binders: Sequence[ConditionalBinder],
) -> str:
    kind, theorem_uid, prerequisites = derivation
    if kind == "direct" or theorem_uid is None:
        raise ValueError("direct obligations are not generated declarations")
    theorem = theorems_by_uid[theorem_uid]
    implication = positive_implication(theorem)
    if implication is None:
        raise ValueError(f"{short_uid(theorem_uid)} is not a positive implication")
    antecedents, conclusion = implication
    carrier = carrier_name(space_uid)
    declaration = (
        f"theorem {theorem_name(space_uid, property_uid, value)}"
        f"{binder_text(binders)} : {goal(property_uid, value, carrier)} :="
    )
    theorem_ref = f"{short_uid(theorem_uid)} {carrier} inferInstance"

    if kind == "implication":
        payload = antecedent_payload(space_uid, antecedents, binders)
        return f"{declaration}\n  {theorem_ref} {payload}"

    if kind != "contrapositive" or value:
        raise ValueError(f"unsupported derivation kind: {kind!r}")
    conclusion_prop, conclusion_value = conclusion
    if not conclusion_value:
        raise ValueError("contraposition requires a positive conclusion")
    others = tuple(
        literal for literal in antecedents if literal[0] != property_uid
    )
    payload = antecedent_payload(
        space_uid,
        antecedents,
        binders,
        replacement=(property_uid, "h"),
    )
    contradiction = reference(
        space_uid, conclusion_prop, False, binders
    )
    return (
        f"{declaration} by\n"
        "  intro h\n"
        f"  exact {contradiction} ({theorem_ref} {payload})"
    )


def generated_dependencies(
    seed: Mapping[str, bool],
    theorems: Sequence[Mapping[str, Any]],
    available_properties: set[str],
) -> tuple[list[str], list[str]]:
    """Return the exact property and theorem modules needed by generated declarations."""
    known, derivations, _ = close(seed, theorems, available_properties)
    properties = sorted(
        (short_uid(prop) for prop in known if derivations[prop][0] != "direct"),
        key=lambda uid: int(uid[1:]),
    )
    theorem_ids = sorted(
        {
            short_uid(derivation[1])
            for derivation in derivations.values()
            if derivation[0] != "direct" and derivation[1] is not None
        },
        key=lambda uid: int(uid[1:]),
    )
    return properties, theorem_ids


def render_generated_imports(
    seed: Mapping[str, bool],
    theorems: Sequence[Mapping[str, Any]],
    available_properties: set[str],
) -> str:
    properties, theorem_ids = generated_dependencies(seed, theorems, available_properties)
    lines = [
        GENERATED_IMPORTS_BEGIN,
        "public meta import PiBaseLean.Audit.Spaces.Registry",
    ]
    lines.extend(f"public import PiBaseLean.Properties.{uid}.Defs" for uid in properties)
    lines.extend(f"public import PiBaseLean.Theorems.{uid}.Theorem" for uid in theorem_ids)
    lines.append(GENERATED_IMPORTS_END)
    return "\n".join(lines)


def render_generated_region(
    space_uid: str,
    seed: Mapping[str, bool],
    theorems: Sequence[Mapping[str, Any]],
    available_properties: set[str],
    property_names: Mapping[str, str],
    space_names: Mapping[str, str],
    independence: Mapping[str, Any],
) -> str:
    known, derivations, order = close(seed, theorems, available_properties)
    binders = conditional_binders(space_uid, independence)
    carrier = carrier_name(space_uid)
    direct = [prop for prop in order if derivations[prop][0] == "direct"]
    derived = [prop for prop in order if derivations[prop][0] != "direct"]
    theorem_map = {item["uid"]: item for item in theorems}

    lines = [
        GENERATED_BEGIN,
        f"/- Traits for {short_uid(space_uid)} ({space_names.get(space_uid, '')}).",
        "Direct obligations are handwritten outside this generated region:",
    ]
    if direct:
        for prop in direct:
            value = known[prop]
            lines.append(
                f"  {theorem_name(space_uid, prop, value)}"
                f"{binder_text(binders)} : {goal(prop, value, carrier)}"
                f"  ({property_names.get(prop, prop)})"
            )
    else:
        lines.append("  (none)")
    lines.extend(["", "Generated derived declarations:", "-/", "", "namespace PiBase.Formal"])

    if derived:
        for prop in derived:
            lines.extend(
                [
                    "",
                    render_derived_declaration(
                        space_uid,
                        prop,
                        known[prop],
                        derivations[prop],
                        theorem_map,
                        binders,
                    ),
                    "",
                    render_certificate(
                        space_uid,
                        prop,
                        known[prop],
                        "derived",
                        binders,
                    ),
                ]
            )
    else:
        lines.extend(["", "/- No derived declarations. -/"])
    lines.extend(["", "end PiBase.Formal", GENERATED_END])
    return "\n".join(lines)


def replace_generated_imports(source: str, imports: str) -> str:
    begin_count = source.count(GENERATED_IMPORTS_BEGIN)
    end_count = source.count(GENERATED_IMPORTS_END)
    if begin_count != end_count or begin_count > 1:
        raise ValueError("expected at most one complete generated import region")
    if begin_count == 1:
        start = source.index(GENERATED_IMPORTS_BEGIN)
        end = source.index(GENERATED_IMPORTS_END, start) + len(GENERATED_IMPORTS_END)
        return source[:start] + imports + source[end:]
    expose = source.find("@[expose]")
    if expose < 0:
        raise ValueError("numbered Lemmas file is missing @[expose] public section")
    prefix = source[:expose].rstrip()
    suffix = source[expose:].lstrip()
    return f"{prefix}\n\n{imports}\n\n{suffix}"


def replace_generated_region(source: str, region: str) -> str:
    begin_count = source.count(GENERATED_BEGIN)
    end_count = source.count(GENERATED_END)
    if begin_count != end_count or begin_count > 1:
        raise ValueError("expected at most one complete generated trait region")
    if begin_count == 1:
        start = source.index(GENERATED_BEGIN)
        end = source.index(GENERATED_END, start) + len(GENERATED_END)
        return source[:start] + region + source[end:]
    if not source:
        return region + "\n"
    separator = "\n" if source.endswith("\n\n") else "\n\n"
    return source.rstrip("\n") + separator + region + "\n"


def lemmas_path(lemmas_root: Path, space_uid: str) -> Path:
    return lemmas_root / short_uid(space_uid) / "Lemmas.lean"


def update_lemmas(path: Path, imports: str, region: str, check: bool) -> bool:
    if not path.is_file():
        raise FileNotFoundError(f"numbered Lemmas file does not exist: {path}")
    current = path.read_text(encoding="utf-8")
    updated = replace_generated_imports(current, imports)
    updated = replace_generated_region(updated, region)
    changed = updated != current
    if changed and not check:
        path.write_text(updated, encoding="utf-8")
    return changed


def build_traits_data(data: Mapping[str, Any], lean_root: Path | str) -> dict[str, Any]:
    """Build the trait table consumed by the review UI."""
    property_names = {item["uid"]: item["name"] for item in data["properties"]}
    space_names = {item["uid"]: item["name"] for item in data["spaces"]}
    seeds: defaultdict[str, dict[str, bool]] = defaultdict(dict)
    for trait in data["traits"]:
        seeds[trait["space"]][trait["property"]] = trait["value"]
    available_properties = available("P", lean_root)
    theorems = [
        item for item in data["theorems"] if theorem_matches_lean(item, lean_root)
    ]

    result = {}
    for space_uid in sorted(seeds):
        known, derivations, order = close(
            seeds[space_uid], theorems, available_properties
        )
        rows = []
        for prop in order:
            kind, theorem_uid, _ = derivations[prop]
            rows.append(
                {
                    "property": prop,
                    "name": property_names.get(prop, prop),
                    "value": known[prop],
                    "status": "asserted" if kind == "direct" else "proven",
                    "via": short_uid(theorem_uid) if theorem_uid else None,
                }
            )
        result[space_uid] = {
            "name": space_names.get(space_uid, ""),
            "traits": rows,
        }
    return result


def print_stats(context: GenerationContext) -> None:
    seeds = context.seeds
    available_properties = context.available_properties
    available_theorems = context.available_theorems
    direct_count = derived_count = cell_count = 0
    per_space = []
    for space_uid in sorted(seeds):
        known, derivations, _ = close(
            seeds[space_uid], available_theorems, available_properties
        )
        direct = sum(derivations[prop][0] == "direct" for prop in known)
        derived = len(known) - direct
        direct_count += direct
        derived_count += derived
        cell_count += len(known)
        per_space.append((space_uid, len(known), direct, derived))

    print(f"pi-base data: {len(seeds)} spaces, {len(context.catalog['traits'])} asserted traits")
    print(
        f"formalized: {len(available_properties)} properties, "
        f"{len(available('T', context.lean_root))} theorems, "
        f"{len(available('S', context.lean_root))} space directories"
    )
    print(f"trait cells determined: {cell_count}")
    print(f"  direct obligations: {direct_count}")
    print(f"  generated derivations: {derived_count}")
    print("per-space sample (cells = direct + derived):")
    for space_uid, count, direct, derived in per_space[:12]:
        name = context.space_names.get(space_uid, "")[:34]
        print(
            f"  {space_uid} «{name:34}» {count:3} = "
            f"{direct} direct + {derived} derived"
        )


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("spaces", nargs="*", help="space ids such as S3 or S000003")
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--emit", action="store_true", help="print generated regions")
    mode.add_argument("--write", action="store_true", help="update existing numbered Lemmas files")
    mode.add_argument("--check", action="store_true", help="fail if numbered Lemmas files are stale")
    mode.add_argument(
        "--data",
        nargs="?",
        const=str(REPO_ROOT / "data" / "traits.json"),
        metavar="PATH",
        help="write review trait data (default: data/traits.json)",
    )
    parser.add_argument("--catalog", type=Path, default=DEFAULT_CATALOG)
    parser.add_argument("--independence", type=Path, default=DEFAULT_INDEPENDENCE)
    parser.add_argument("--lean-root", type=Path, default=DEFAULT_LEAN_ROOT)
    parser.add_argument("--lemmas-root", type=Path, default=DEFAULT_LEMMAS_ROOT)
    return parser


def main(argv: Sequence[str] | None = None) -> int:
    parser = build_parser()
    args = parser.parse_args(argv)
    if args.spaces and not (args.emit or args.write or args.check):
        parser.error("space ids require --emit, --write, or --check")
    if (args.emit or args.write or args.check) and not args.spaces:
        parser.error("this mode requires at least one space id")

    context = GenerationContext(
        catalog=load_json(args.catalog.resolve()),
        lean_root=args.lean_root.resolve(),
        independence=load_json(args.independence.resolve()),
    )

    if args.data is not None:
        destination = Path(args.data).resolve()
        destination.parent.mkdir(parents=True, exist_ok=True)
        data = build_traits_data(context.catalog, context.lean_root)
        destination.write_text(
            json.dumps(data, ensure_ascii=False, indent=2) + "\n",
            encoding="utf-8",
        )
        cells = sum(len(item["traits"]) for item in data.values())
        print(f"wrote {destination}: {len(data)} spaces, {cells} trait cells")
        return 0

    if args.emit or args.write or args.check:
        seeds = context.seeds
        exit_code = 0
        for raw_space in args.spaces:
            try:
                space_uid = normalize_uid(raw_space, "S")
            except ValueError as error:
                parser.error(str(error))
            if space_uid not in seeds:
                parser.error(f"space is absent from the trait catalog: {raw_space}")
            region = render_generated_region(
                space_uid,
                seeds[space_uid],
                context.available_theorems,
                context.available_properties,
                context.property_names,
                context.space_names,
                context.independence,
            )
            imports = render_generated_imports(
                seeds[space_uid],
                context.available_theorems,
                context.available_properties,
            )
            if args.emit:
                if len(args.spaces) > 1:
                    print(f"-- {short_uid(space_uid)} --")
                print(region)
                continue
            path = lemmas_path(args.lemmas_root.resolve(), space_uid)
            try:
                changed = update_lemmas(path, imports, region, check=args.check)
            except (FileNotFoundError, ValueError) as error:
                print(error, file=sys.stderr)
                exit_code = 1
                continue
            if args.check:
                print(f"{'stale' if changed else 'current'}: {path}")
                exit_code |= int(changed)
            else:
                print(f"{'updated' if changed else 'unchanged'}: {path}")
        return exit_code

    print_stats(context)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
