# Author: Fangzhu Shen
"""C-local precheck of a submission against the push the coordinator holds.

A refusal the verifier raises costs a whole round: the payload is accepted as
bytes, the round is spent, and the fault comes back in the next consultation's
correction two minutes later. Every fault in this module is one C can decide
from the push it already holds, so it is returned inside the same turn, as a
tool error the model can read and answer immediately, and the turn may submit
again.

The checks are the faults C can be certain of: a payload that is not one
complete JSON value; a `binding` that is not the one this consultation's
response example carries; a drop the push did not authorize; a clause the push
reports permanently dead; and a clause Lean's own admission refuses. Where a
fault is not certain -- an unparseable member C cannot classify, a query the
run did not negotiate, an answer in an unexpected shape -- the payload is
forwarded and the verifier decides, because refusing something the verifier
would have accepted costs the run an answer it had.

Nothing here edits, completes or reconstructs a payload: a refused payload is
not sent, an accepted payload is sent byte for byte, and the verifier checks
every submission it receives exactly as before.
"""

from dataclasses import dataclass, field
import json

from .json_wire import JsonWireError, decode


BINDING_BYTES = 64 * 1024
PAYLOAD_BYTES = 4 * 1024 * 1024
MAXIMUM_NAMED_KEYS = 16
IDENTITY_FIELDS = ("clause_id", "record_digest", "formula_digest")
NOT_SENT = ("Nothing was sent and no round was spent; correct this and call"
            " submit again.")


def expected_binding(response_example):
    """The binding object of B's response example, or None if it has none."""
    if type(response_example) is not bytes:
        return None
    try:
        value = decode(response_example, maximum=BINDING_BYTES)
    except JsonWireError:
        return None
    binding = value.get("binding") if isinstance(value, dict) else None
    return dict(binding) if isinstance(binding, dict) else None


def _drop_key(reference):
    """The identity the verifier matches a drop on, or None if incomplete.

    `resolve_drops` accepts a drop only when its consultation digest, its
    authorization digest and the three fields of its clause identity all equal
    an issued reference's. The clause text an identity may carry beside them
    is checked against the verifier's own record, which is not C's to judge,
    so it is left out of the comparison.
    """
    if not isinstance(reference, dict):
        return None
    clause = reference.get("clause")
    if not isinstance(clause, dict):
        return None
    key = [reference.get("consultation_digest"), reference.get("authorization_digest")]
    key.extend(clause.get(name) for name in IDENTITY_FIELDS)
    if not isinstance(key[0], str) or not isinstance(key[1], str):
        return None
    if not isinstance(key[2], int) or not all(isinstance(part, str) for part in key[3:]):
        return None
    return tuple(key)


@dataclass(frozen=True)
class PushChecks:
    """What this consultation's push lets C decide about a payload."""

    binding: dict | None = None
    drops: frozenset = field(default_factory=frozenset)
    dead: frozenset = field(default_factory=frozenset)

    def holds_push(self) -> bool:
        """Whether there is a push to check a payload against.

        Every check in this module is a comparison with the consultation's
        own push, and its response example is the part the coordinator always
        receives with one. Without it C is not looking at a submission it can
        judge, so it judges nothing and the verifier decides as it always did.
        """
        return self.binding is not None


def push_checks(response_example, observation=None) -> PushChecks:
    """Read the coordinator's push once, for every check this turn will make."""
    feedback = observation.get("feedback") if isinstance(observation, dict) else None
    feedback = feedback if isinstance(feedback, dict) else {}
    drops, dead = set(), set()
    for entry in feedback.get("pending") or []:
        key = _drop_key(entry.get("drop_reference") if isinstance(entry, dict) else None)
        if key is not None:
            drops.add(key)
    # Only a clause dead by refutation is permanently dead; one dead by a drop
    # of your own is revived by exactly this resubmission.
    for entry in feedback.get("last_round") or []:
        outcome = entry.get("outcome") if isinstance(entry, dict) else None
        if not isinstance(outcome, dict) or outcome.get("cause") != "refuted":
            continue
        clause = entry.get("clause")
        source = clause.get("canonical_source") if isinstance(clause, dict) else None
        if isinstance(source, str) and source:
            dead.add(source)
    return PushChecks(expected_binding(response_example), frozenset(drops), frozenset(dead))


def binding_difference(binding, expected):
    """Missing, unexpected and changed keys, each list sorted and bounded."""
    if not isinstance(binding, dict):
        return {"missing": sorted(expected)[:MAXIMUM_NAMED_KEYS], "unexpected": [], "changed": []}
    return {"missing": sorted(set(expected) - set(binding))[:MAXIMUM_NAMED_KEYS],
            "unexpected": sorted(set(binding) - set(expected))[:MAXIMUM_NAMED_KEYS],
            "changed": sorted(key for key in set(binding) & set(expected)
                              if binding[key] != expected[key])[:MAXIMUM_NAMED_KEYS]}


def binding_refusal(binding, expected):
    """Why this binding would be refused, or None when it is the exact one.

    The binding is a verbatim copy target: the verifier compares it key for
    key and value for value with the object it issued, so a differing value is
    as certain a refusal as a missing key, and naming the key here saves the
    round that naming it in the next push would cost.
    """
    if expected is None or binding == expected:
        return None
    difference = binding_difference(binding, expected)
    parts = []
    if not isinstance(binding, dict):
        parts.append("`binding` is missing or is not an object")
    for label, keys in (("missing keys", difference["missing"]),
                        ("keys that do not belong", difference["unexpected"]),
                        ("keys with a different value", difference["changed"])):
        if keys:
            parts.append(label + ": " + ", ".join(keys))
    if not parts:
        return None
    return ("Not submitted: the `binding` object must be copied verbatim from the "
            "RESPONSE EXAMPLE in the push (" + "; ".join(parts) + "). " + NOT_SENT +
            " Copy the RESPONSE EXAMPLE's exact `binding` object, changing only "
            "`clauses` and `dropped` (or `input`).")


def _decoder_fault(error):
    """The decoder's own complaint and position, never the rejected text."""
    cause = error.__cause__
    if isinstance(cause, json.JSONDecodeError):
        return f"{cause.msg}, at character {cause.pos}"
    return None


def payload_refusal(payload, checks):
    """Why this payload would be refused, or None to send it to the verifier.

    Decided in the order the verifier itself decides: the document must parse,
    its envelope must carry this consultation's binding, and only then are its
    drops and clauses read.
    """
    if not checks.holds_push() or type(payload) is not bytes or len(payload) > PAYLOAD_BYTES:
        return None
    try:
        value = decode(payload, maximum=PAYLOAD_BYTES)
    except JsonWireError as error:
        # Only a decoder position is certain. A duplicate key, a nesting bound
        # or an oversized document may yet be read differently by the
        # verifier's own decoder, so those go to it unchanged.
        fault = _decoder_fault(error)
        if fault is None:
            return None
        return (f"Not submitted: `payload` is not one complete JSON value ({fault}). "
                + NOT_SENT + " Send the whole response document again, checking that"
                " it opens with `{`, closes with the matching `}`, and carries"
                " nothing before or after it.")
    if not isinstance(value, dict):
        return None
    refusal = binding_refusal(value.get("binding"), checks.binding)
    if refusal is not None:
        return refusal
    dropped = value.get("dropped")
    if isinstance(dropped, list) and checks.drops:
        for index, reference in enumerate(dropped):
            key = _drop_key(reference)
            if key is not None and key not in checks.drops:
                return (f"Not submitted: `dropped[{index}]` is not one of the drop "
                        "references this consultation issued. " + NOT_SENT +
                        " Copy the reference whole out of IDENTITIES AND DROP"
                        " REFERENCES in the prompt; one kept from an earlier"
                        " consultation is never eligible.")
    for index, clause in enumerate(clause_drafts(value)):
        if clause in checks.dead:
            return (f"Not submitted: `clauses[{index}]` is a formula the push reports "
                    "dead by refutation, which the verifier refuses before the round "
                    "runs. " + NOT_SENT + " Propose different content, not a different"
                    " spelling of the same formula.")
    return None


def clause_drafts(value):
    """The clause strings of a decoded payload, or an empty list."""
    clauses = value.get("clauses") if isinstance(value, dict) else None
    if not isinstance(clauses, list):
        return []
    return [clause for clause in clauses if isinstance(clause, str)]


def decoded_payload(payload):
    """The payload as an object, or None when C cannot read it as one."""
    if type(payload) is not bytes or len(payload) > PAYLOAD_BYTES:
        return None
    try:
        value = decode(payload, maximum=PAYLOAD_BYTES)
    except JsonWireError:
        return None
    return value if isinstance(value, dict) else None


def admission_refusal(reply, clauses):
    """Why Lean's own admission would refuse a clause, or None to send it.

    `reply` is the whole `validate_clauses` answer for the payload's clause
    list, whose `result.results` runs in the order the clauses were asked
    about. Anything C cannot read as that answer -- an error payload, a
    truncated list, an unfamiliar shape -- leaves the payload alone.
    """
    result = reply.get("result") if isinstance(reply, dict) else None
    results = result.get("results") if isinstance(result, dict) else None
    if not isinstance(results, list) or len(results) != len(clauses):
        return None
    for index, result in enumerate(results):
        if not isinstance(result, dict) or result.get("admitted") is not False:
            continue
        diagnostic = result.get("correctable")
        diagnostic = diagnostic if isinstance(diagnostic, dict) else {}
        named = [str(diagnostic.get("code") or "not admitted")]
        message = diagnostic.get("message")
        if isinstance(message, str) and message:
            named.append(message)
        for name in ("item_index", "offset", "path"):
            if diagnostic.get(name) is not None:
                named.append(f"{name} {diagnostic[name]}")
        return (f"Not submitted: Lean does not admit `clauses[{index}]` ("
                + "; ".join(named) + "). " + NOT_SENT +
                " Fix the clause, or try a draft with validate_clauses, which"
                " costs no round either.")
    return None
