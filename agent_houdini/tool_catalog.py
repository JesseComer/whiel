# Author: Fangzhu Shen
"""MCP tool metadata over separately authorized canonical queries."""

from copy import deepcopy
from dataclasses import dataclass
import re

from .skills import SkillCatalog


KNOWN_QUERIES = (
    "countermodel", "strongest_refutations", "history", "ledger",
    "validate_clauses", "evaluate_clauses",
)


def _object(properties, required):
    return {"type": "object", "properties": properties, "required": list(required),
            "additionalProperties": False}


def _tool(name, description, schema):
    return {"name": name, "description": description, "inputSchema": schema}


def _evaluation_schema():
    relation = _object({
        "name": {"type": "string"},
        "rows": {"type": "array", "items": {"type": "array", "items": {"type": "string"}}},
    }, ("name", "rows"))
    instance = _object({
        "carrier_keys": {"type": "array", "items": {"type": "string"}},
        "relations": {"type": "array", "items": relation},
    }, ("carrier_keys", "relations"))
    retained = _object({"kind": {"const": "retained"}, "attempt": {"type": "integer", "minimum": 0}},
                       ("kind", "attempt"))
    supplied = _object({"kind": {"const": "supplied"}, "instance": instance}, ("kind", "instance"))
    return _object({
        "clauses": {"type": "array", "items": {"type": "string"}},
        "instances": {"oneOf": [{"const": "all_retained"},
                                {"type": "array", "items": {"oneOf": [retained, supplied]}}]},
    }, ("clauses", "instances"))


def tools_for_policy(query_names=KNOWN_QUERIES) -> list[dict]:
    if isinstance(query_names, str):
        raise ValueError("expected canonical query names")
    selected = []
    for name in query_names:
        if not isinstance(name, str):
            raise ValueError("expected canonical query names")
        if name in KNOWN_QUERIES and name not in selected:
            selected.append(name)
    # The three digests name the clause; the admitted text the push shows
    # beside them may be copied back with it and is optional, so a whole
    # identity lifted out of the observation is a valid argument.
    clause = _object({
        "clause_id": {"type": "integer", "minimum": 0},
        "record_digest": {"type": "string"}, "formula_digest": {"type": "string"},
        "canonical_source": {"type": ["string", "null"]},
        "display": {"type": ["string", "null"]},
    }, ("clause_id", "record_digest", "formula_digest"))
    definitions = {
        "countermodel": (
            "Fetch the Lean-validated finite database behind one refuted check: every relation's "
            "rows, on which the check's premises hold and its goal fails. Use it only after a "
            "`refuted` verdict, and pass that verdict's own attempt: the push's "
            "`postcondition_open.attempt`, or the `attempt_id` inside a history row's `result` -- "
            "never a row's `row_ordinal`, which is a different number. An inconclusive or "
            "timed-out check has no countermodel and the call is refused. Example: "
            "{\"attempt\": 17}.",
            _object({"attempt": {"type": "integer", "minimum": 0}}, ("attempt",))),
        "strongest_refutations": (
            "For one clause identity, the refutations whose premise sets are inclusion-maximal, per "
            "role: provenance for a clause that keeps failing, after `history` has been read. Copy "
            "the identity from the prompt's IDENTITIES section. Example: {\"clause\": "
            "{\"clause_id\": 3, \"record_digest\": \"...\", \"formula_digest\": \"...\"}}.",
            _object({"clause": deepcopy(clause)}, ("clause",))),
        "history": (
            "One clause's whole record: status, minimum and current level, and every check row "
            "(level, role, outcome, the attempt that refuted it), oldest first. Use it when the "
            "push does not say why a pending clause is still pending. Copy the identity from the "
            "prompt's IDENTITIES section. Example: {\"clause\": {\"clause_id\": 3, "
            "\"record_digest\": \"...\", \"formula_digest\": \"...\"}}.",
            _object({"clause": deepcopy(clause)}, ("clause",))),
        "ledger": (
            "The run's whole check chronology, newest page first; pass the returned continuation "
            "cursor for the next page. For one clause use `history` instead; this is the run-wide "
            "view. Example: {} and then {\"cursor\": \"<the returned cursor>\"}.",
            _object({"cursor": {"type": ["string", "null"]}}, ())),
        "validate_clauses": (
            "Ask Lean whether draft clause strings parse and fit the schema; returns each admitted "
            "clause's canonical source or a diagnostic. Costs no round and changes nothing, so call "
            "it before submitting any syntax you are not sure of. Example: {\"clauses\": "
            "[\"(op_zR = ∅[2])\"]}.",
            _object({"clauses": {"type": "array", "items": {"type": "string"}}}, ("clauses",))),
        "evaluate_clauses": (
            "Evaluate draft clauses, exactly as written, on explicit finite instances. `holds[i]` "
            "is the clause's truth value on instance `i`, so a draft excludes that instance "
            "exactly when `holds` reads false; it proves nothing about inductiveness and changes "
            "no state. `instances` is either the bare string \"all_retained\" -- which evaluates "
            "on nothing when nothing is retained -- or an ARRAY whose entries are {\"kind\": "
            "\"retained\", \"attempt\": n} or {\"kind\": \"supplied\", \"instance\": "
            "{\"carrier_keys\": [...], \"relations\": [{\"name\", \"rows\"}]}}, where "
            "`carrier_keys` is required, non-empty, and written in the same domain-value form as "
            "the cells (`num:1`, `str:a`, `bool:0`). Example: {\"clauses\": [\"(op_zR = ∅[2])\"], "
            "\"instances\": [{\"kind\": \"retained\", \"attempt\": 17}]}.",
            _evaluation_schema()),
    }
    tools = [_tool(name, *definitions[name]) for name in selected]
    tools.append(_tool(
        "submit",
        "Deliver this consultation's one response: payload is the complete response JSON as a "
        "string, its binding copied from the RESPONSE EXAMPLE. Exactly once per consultation; a "
        "receipt means the bytes arrived, not that anything was admitted or proved. Closing chat "
        "text is not a submission. Some faults are caught here before the payload is sent: the "
        "reply is then an error naming the fault, nothing was delivered, no round was spent, and "
        "you may correct it and call submit again in this same turn.",
        _object({"payload": {"type": "string"}}, ("payload",)),
    ))
    return tools


def valid_name(name) -> bool:
    return isinstance(name, str) and re.fullmatch(r"[A-Za-z][A-Za-z0-9_]{0,63}", name) is not None


def validate_inventory(names) -> list[str]:
    names = list(names)
    if (not names or len(names) > 128 or not all(valid_name(name) for name in names)
            or len(set(names)) != len(names) or names.count("submit") != 1):
        raise ValueError("invalid C-advertised native tool inventory")
    return names


@dataclass(frozen=True, slots=True, init=False)
class ToolCatalog:
    skills: SkillCatalog

    def __init__(self, skills=None):
        if skills is not None and not isinstance(skills, SkillCatalog):
            raise ValueError("expected a C skill snapshot")
        object.__setattr__(self, "skills", SkillCatalog() if skills is None else skills)

    def with_skills(self, skills: SkillCatalog) -> "ToolCatalog":
        return ToolCatalog(skills)

    def query(self, name: str) -> str | None:
        return name if name in KNOWN_QUERIES else None

    def advertise(self, canonical: list[dict]) -> list[dict]:
        tools = deepcopy(canonical)
        if self.skills.enabled():
            tools.append(_tool(
                "get_skill",
                "Read one local skill: a written procedure for a kind of loop or a kind of "
                "failure, listed under the prompt's Skills section. Read the skills whose "
                "description matches your task before your first proposal. Guidance only, never "
                "verifier evidence. Example: {\"id\": \"<an id from the Skills section>\"}.",
                _object({"id": {"type": "string", "enum": self.skills.ids()}}, ("id",)),
            ))
        return tools

    def tools_for_policy(self, query_names=KNOWN_QUERIES) -> list[dict]:
        return self.advertise(tools_for_policy(query_names))

    def names_for_policy(self, query_names=KNOWN_QUERIES) -> list[str]:
        return [tool["name"] for tool in self.tools_for_policy(query_names)]

    def inventory(self, query_names=KNOWN_QUERIES) -> list[str]:
        """Validate C's advertised inventory once, where the catalog is built."""
        return validate_inventory(self.names_for_policy(query_names))


def default_catalog() -> ToolCatalog:
    return ToolCatalog()
