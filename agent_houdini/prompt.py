# Author: Fangzhu Shen
"""The prompt C renders for one consultation: assets, then the selected push.

C owns every word the agent reads. The explanation comes from `prompt_assets/`
in numeric order and is a manual of the verifier, not a coach: the role and
the submission rules, the prophecy schema and the clause grammar, how the
leveled checks work and how to read the push, and what each verdict costs and
calls for. The first three are rendered whatever the push costs; the fourth is
dropped only when the push itself would carry the prompt past its byte aim.
Method-level advice -- how to build a Core in layers, worked examples, clause
patterns for particular loop shapes -- is not in the prompt: it lives in the
skill library C serves through `get_skill`, whose index the prompt lists when
a library is configured, so that the library can be switched off and its
contribution measured. After the explanation C presents the push it selected
and formatted: the task, the relation table, the Core, pending clauses, last
round, the latest result, any correction, the remaining budget in plain
seconds, the tools and the skill index. B's exact response example closes the
prompt unchanged, followed by the clause identities and drop references copied
out of the observation verbatim: the only values of the push an agent has to
hand back exactly. C derives no canonical fact, rewrites no value and never
reconstructs a binding, an identity or a digest.

Every clause the verifier names carries the text the verifier admitted for it
(`clause.canonical_source`, with `clause.display` beside it), so the clauses
shown here are the verifier's own and C keeps no record of its own submissions.
What identities do not carry is the check history -- which level and role each
attempt ran at, how it came out and which attempt refuted it. C does not fetch
that to render it: the assets point the agent at `history` and `ledger`, which
it can page itself, and C spends no query of its own on a consultation.
"""

from pathlib import Path
import re

from .json_wire import encode


ASSET_DIRECTORY = Path(__file__).with_name("prompt_assets")
ASSET_ORDER = ("00-framework.md",)
FIRST_CONSULTATION_ONLY = frozenset()
# Every asset is unconditional: the single reference file is never budgeted.
UNCONDITIONAL_ASSETS = ("00-framework.md",)
# B's response example and the identity tail are never dropped. The constants
# are set against the largest real pushes on record -- a populated later
# consultation renders its task text twice in C's presentation, and the tail
# adds a line per clause -- and leave every recorded first consultation holding
# all five assets. Raising either constant simply includes more.
FIRST_BUDGET_BYTES = 48 * 1024
LATER_BUDGET_BYTES = 56 * 1024

RULE = "=" * 78
# Every canonical relation key: lift prefix, family tag, the `s`-repeated index
# and the payload (`Whiel/Concrete/WhielNames/Notation.lean`, `encode`). The
# clause spelling drops the colons and closes the index with `z`
# (`Whiel/Concrete/WhielNames/SurfaceSyntax.lean`, `source`).
KEY_PATTERN = re.compile(r"^([oy]):([paf]):(s*):(.+)$")
BASE_PATTERN = re.compile(r"[A-Za-z]+")
FLAG_PATTERN = re.compile(r"0|[1-9][0-9]*")
COMMENT_PATTERN = re.compile(r"\A\s*<!--.*?-->\s*", re.DOTALL)


def asset_text(name: str) -> str:
    """One prompt asset without its provenance comment; assets are C-owned."""
    text = (ASSET_DIRECTORY / name).read_text(encoding="utf-8")
    return COMMENT_PATTERN.sub("", text).strip()


def _object(value, key):
    found = value.get(key) if isinstance(value, dict) else None
    return found if isinstance(found, dict) else {}


def _list(value, key):
    found = value.get(key) if isinstance(value, dict) else None
    return found if isinstance(found, list) else []


def _text(value):
    return value if isinstance(value, str) else ""


def is_first_consultation(observation) -> bool:
    """An input's opening consultation: round one with nothing to correct."""
    feedback = _object(observation, "feedback")
    return observation.get("correction") is None and feedback.get("iteration") == 1


def _parts(key: str):
    """Lift, family, index and payload of a canonical relation key, or None."""
    match = KEY_PATTERN.match(key)
    if match is None:
        return None
    lift, family, index, payload = match.groups()
    pattern = FLAG_PATTERN if family == "f" else BASE_PATTERN
    if not pattern.fullmatch(payload):
        return None
    return lift, family, index, payload


def clause_spelling(key: str):
    """The surface name of a relation key, for every canonical key form.

    The clause spelling drops the key's colons and closes the index segment
    with `z`: `o:p::E` is written `op_zE`, `y:p::T` is written `yp_zT`,
    `o:a::T` is written `oa_zT`, `y:a::T` is written `ya_zT`, the indexed key
    `o:p:s:R` is written `op_szR` and the flag key `o:f::1` is written `of_z1`.
    A key this shorthand cannot parse is reported as unknown rather than
    guessed; `validate_clauses` remains the authority on any spelling.
    """
    parsed = _parts(key)
    if parsed is None:
        return None
    lift, family, index, payload = parsed
    return lift + family + "_" + index + "z" + payload


def _display_name(key: str):
    """The concrete notation's spelling, as the task text writes the relation.

    `Whiel/Concrete/WhielNames.lean`, `spell`: an auxiliary name carries `_aux`
    before any index, a positive index is written `_n`, and a flag is written
    `flag_<id>_<index>`. C adds the trailing ∞ that marks a prophecy copy.
    """
    parsed = _parts(key)
    if parsed is None:
        return key
    lift, family, index, payload = parsed
    number = len(index)
    if family == "f":
        name = f"flag_{payload}_{number}"
    else:
        name = payload + ("_aux" if family == "a" else "")
        if number:
            name += f"_{number}"
    return name + ("∞" if lift == "y" else "")


def _indent(text, prefix="        "):
    return "\n".join(prefix + line for line in _text(text).split("\n"))


def _wrap(text, width=66):
    """Greedy word wrap, so a fixed note reads the same width as the prose."""
    lines, current = [], ""
    for word in text.split():
        candidate = f"{current} {word}" if current else word
        if current and len(candidate) > width:
            lines.append(current)
            current = word
        else:
            current = candidate
    return lines + ([current] if current else [])


def _seconds(nanoseconds):
    try:
        return int(str(nanoseconds)) / 1_000_000_000
    except (TypeError, ValueError):
        return None


def _triple(triple):
    lines = []
    for name in ("precondition", "command", "postcondition"):
        lines.append(f"    {name}:")
        lines.append(_indent(triple.get(name)))
    lines.append("")
    return lines


def _task_section(presentation, feedback):
    task = _object(presentation, "task")
    iteration = feedback.get("iteration")
    header = "# Task " + (_text(task.get("canonical_id")) or "(unnamed input)")
    if isinstance(iteration, int):
        header += f" — consultation {iteration}"
    lines = [header, ""]
    if not task:
        return lines + ["The push carried no task document.", ""]
    lines.append("The verification claim you are investigating, in the loop form the")
    lines.append("verification conditions are built from:")
    lines.append("")
    lines.extend(_triple(_object(task, "preprocessed")))
    original = _object(task, "original")
    if original and original != _object(task, "preprocessed"):
        lines.append("The original program, before the straight-line prefix was absorbed")
        lines.append("into the precondition. Context only; your clauses are about the loop:")
        lines.append("")
        lines.extend(_triple(original))
    return lines


def instance_name(key: str):
    """How a counterexample instance names this relation, or None.

    An instance is over the task's raw input schema, which the push does not
    publish separately: it is the ambient schema's ordinary copies at base
    index zero, flags excluded (`Whiel/Concrete/WhielNames.lean`,
    `IsRawInput`). A prophecy copy, an indexed preprocessing copy and a
    control flag are all outside it. The accepted spelling drops the `o:`
    lift prefix, which is the form the verifier's own records use.
    """
    parsed = _parts(key)
    if parsed is None:
        return None
    lift, family, index, _ = parsed
    if lift != "o" or family == "f" or index:
        return None
    return key[2:]


def _relation_section(presentation):
    schema = _object(presentation, "ambient_schema")
    relations = [item for item in _list(schema, "relations") if isinstance(item, dict)]
    if not relations:
        return []
    prophecy_of = {}
    for pair in _list(schema, "prophecy_map"):
        if isinstance(pair, dict):
            prophecy_of[_text(pair.get("prophecy_relation"))] = _text(pair.get("program_relation"))
    prophecy_from = {value: key for key, value in prophecy_of.items() if value}
    lines = ["# Relations", "",
             "One relation, four spellings. A push key carries the lift prefix `o:`",
             "(ordinary) or `y:` (prophecy); the task text above uses the displayed",
             "spelling, with a trailing ∞ on a prophecy copy; inside a clause you write",
             "the surface form in the third column, and nothing else is accepted there.",
             "The fourth column is how a counterexample instance names the relation,",
             "and a `—` there means the relation is not in the input schema an",
             "instance is over: an instance lists every relation that has a name in",
             "that column, empty ones as `rows: []`, and no other.",
             "`validate_clauses` returns the canonical source of whatever it admits.", "",
             "    push key      displayed     in a clause    in an instance  arity   prophecy pairing"]
    for relation in relations:
        key = _text(relation.get("key"))
        arity = relation.get("arity")
        if key in prophecy_of:
            pairing = "the exit value of " + prophecy_of[key]
        elif key in prophecy_from:
            pairing = "prophecy copy " + prophecy_from[key]
        else:
            pairing = "no prophecy copy: the body never assigns it"
        lines.append("    {:<13} {:<13} {:<14} {:<15} {:<7} {}".format(
            key, _display_name(key), clause_spelling(key) or "(ask validate_clauses)",
            instance_name(key) or "—", "?" if arity is None else arity, pairing))
    return lines + [""]


def _identity(entry):
    identifier = _object(entry, "clause").get("clause_id")
    return identifier if isinstance(identifier, int) else "(no identity)"


def _clause_lines(entry, prefix="        "):
    """The verifier's own text for one clause it named.

    `canonical_source` is the source the verifier admitted, in the grammar a
    submission is written in; `display` is the same clause's display spelling
    and is shown only when it differs. Either is null only where the text is
    unsafe to present, which is the one case with nothing to show.
    """
    clause = _object(entry, "clause")
    source = _text(clause.get("canonical_source"))
    display = _text(clause.get("display"))
    if not source:
        source, display = display, ""
    if not source:
        return [prefix + "(the push carried no readable text for this clause)"]
    lines = [prefix + line for line in source.split("\n")]
    if display and display != source:
        lines += [prefix + "displayed: " + line for line in display.split("\n")]
    return lines


def _count(number, noun):
    return f"{number} {noun}" + ("" if number == 1 else "s")


def _core_section(feedback):
    entries = [item for item in _list(feedback, "core") if isinstance(item, dict)]
    lines = [f"# Current Core ({_count(len(entries), 'clause')})", ""]
    if not entries:
        return lines + ["Empty. Nothing is committed yet, so every check runs from the",
                        "precondition alone.", ""]
    lines.append("Committed and proved inductive at their level. Validity is accepted when the")
    lines.append("Core alone entails the postcondition. Each clause is shown as the")
    lines.append("verifier admitted it; `origin` is the audited source that placed it.")
    lines.append("")
    for entry in entries:
        identifier = _identity(entry)
        lines.append("    clause {}  level {}  origin {}".format(
            identifier, entry.get("level"), _text(entry.get("source")) or "unknown"))
        lines.extend(_clause_lines(entry))
    return lines + [""]


def _pending_section(feedback):
    entries = [item for item in _list(feedback, "pending") if isinstance(item, dict)]
    lines = [f"# Pending clauses ({len(entries)})", ""]
    if not entries:
        return lines + ["None. Nothing is being retried.", ""]
    lines.append("Retried from their minimum level every round until dropped. A current")
    lines.append("level is the level a clause failed through last scan, which is history,")
    lines.append("not a verdict. `drop_reference: yes` means the push authorizes a drop;")
    lines.append("the reference itself is printed under IDENTITIES AND DROP REFERENCES at")
    lines.append("the end of this prompt and goes into `dropped` whole.")
    lines.append("")
    lines.append("A pending clause is retried on its own, so a clause you want kept needs")
    lines.append("no action: drop only what you want gone. A response may never drop and")
    lines.append("submit the same admitted formula — that whole response is refused with")
    lines.append("`drop_submission_conflict` and no round runs, so dropping a clause is")
    lines.append("not a way to resubmit or reset it.")
    lines.append("")
    for entry in entries:
        identifier = _identity(entry)
        lines.append("    clause {}  minimum level {}  current level {}  origin {}  drop_reference: {}".format(
            identifier, entry.get("minimum_level"), entry.get("current_level"),
            _text(entry.get("source")) or "unknown",
            "yes" if entry.get("drop_reference") else "no"))
        lines.extend(_clause_lines(entry))
    return lines + [""]


def _last_round_section(feedback):
    entries = [item for item in _list(feedback, "last_round") if isinstance(item, dict)]
    # A clause round is the only thing that produces these outcomes. A
    # counterexample round runs no clause epoch and leaves them exactly as the
    # previous epoch did, and a rolled-back epoch records none at all, so the
    # heading alone would claim more than the section holds.
    latest = _text(_object(feedback, "latest").get("kind"))
    lines = [f"# Last round ({_count(len(entries), 'clause')})", ""]
    if not entries:
        if latest in ("", "initial"):
            return lines + ["No previous round.", ""]
        return lines + ["The last round recorded no clause outcomes. The latest result",
                        "below says what became of it.", ""]
    lines.append("What became of each clause the last clause round proposed, each shown")
    lines.append("as the verifier admitted it. The verifier lists these in ascending")
    lines.append("clause order, which is not the order you submitted them in.")
    if latest == "counterexample_rejected":
        lines.append("")
        lines.append("Your last response was a counterexample, which runs no clause round,")
        lines.append("so these are an earlier round's outcomes and say nothing about it.")
    lines.append("")
    for entry in entries:
        identifier = _identity(entry)
        outcome = _object(entry, "outcome")
        words = _text(outcome.get("kind")) or "unknown"
        if outcome.get("level") is not None:
            words += f" at level {outcome['level']}"
        if outcome.get("cause") is not None:
            words += f", cause {outcome['cause']}"
        # The refuting check's own ledger row, which `ledger` pages by and
        # which the push carries nowhere else.
        reason = _object(outcome, "reason")
        if reason.get("attempt") is not None:
            words += f", ledger row {reason['attempt']}"
        lines.append("    clause {}  {}  origin {}".format(
            identifier, words, _text(entry.get("source")) or "unknown"))
        lines.extend(_clause_lines(entry))
    return lines + [""]


LATEST_EXPLANATION = {
    "initial": "no round has run yet",
    "postcondition_open": "the Core is sound but does not yet entail the postcondition",
    "counterexample_rejected": "an instance you proposed was rejected",
    "failure": "infrastructure failure, never a judgement on a clause",
}

# One line per counterexample rejection code, where what the verdict means for
# the next instance does not follow from the reason the verifier sent.
REJECTION_NOTES = {
    "malformed": "The document is wrong, not the instance. The reason gives the"
                 " offending position: every relation of the input schema must be"
                 " listed, no row may repeat, and every cell is a `num:`/`str:`/"
                 "`bool:` string.",
    "unknown_relation": "A name in `relations` is not an input-schema relation of"
                        " this task. A prophecy key and an auxiliary of the"
                        " preprocessed loop are both outside that schema.",
    "precondition_fails": "The instance does not satisfy the precondition, so the"
                          " program is never run on it and it refutes nothing.",
    "postcondition_holds": "The loop halted on this instance in a state the"
                           " postcondition accepts, so it is not a counterexample.",
    "not_quantifier_free": "This task's precondition or postcondition carries a"
                           " quantifier, so no instance is ever accepted for it."
                           " Spend no further round on one.",
    "timeout": "The replay has a 30-second limit and reached it. That is usually a"
               " verdict on the instance: either the loop does not halt on it, or"
               " it is too large to replay.",
    "internal_error": "The validation path failed closed. It says nothing about"
                      " your instance.",
}


def _latest_section(feedback):
    latest = _object(feedback, "latest")
    kind = _text(latest.get("kind")) or "unavailable"
    explanation = LATEST_EXPLANATION.get(kind, "")
    lines = ["# Latest result", "",
             "    " + kind + (" — " + explanation if explanation else "")]
    for name, value in latest.items():
        if name != "kind" and not isinstance(value, (dict, list)):
            lines.append(f"    {name}: {value}")
    # The verifier names one sub-object after the event's own kind, and that
    # object is the whole of what the event says: a rejection's code and
    # reason, a failure's classification, the postcondition check's outcome.
    detail = _object(latest, kind)
    for name, value in detail.items():
        if not isinstance(value, (dict, list)):
            lines.append(f"    {kind}.{name}: {'none' if value is None else value}")
    if (kind == "postcondition_open" and detail.get("outcome") == "refuted"
            and detail.get("attempt") is None):
        lines += ["    " + line for line in _wrap(
            "No countermodel is retained for this refutation, so `countermodel`"
            " refuses it. Work from the Core and the postcondition instead.")]
    note = REJECTION_NOTES.get(_text(detail.get("code"))) if kind == "counterexample_rejected" else None
    if note:
        lines += ["    " + line for line in _wrap(note)]
    return lines + [""]


# The codes decided on the response document itself, before any clause of it
# is read.
ENVELOPE_CODES = ("wrong_response_binding", "malformed_response", "malformed_json",
                  "duplicate_object_key")
# The only two paths a binding fault is named at. `schema_version` is a
# top-level key rather than a member of `binding`, but both are copied from the
# same response example, so both are repaired the same way.
BINDING_PATHS = ("$.binding", "$.schema_version")
# One line per code where the refusal's cost or remedy is not obvious from the
# message the verifier sent. Codes not named here need no gloss.
CORRECTION_NOTES = {
    "drop_submission_conflict":
        "Keep a clause by leaving it pending — it is retried every round on its"
        " own — and drop only what you want gone. Resubmitting a dropped clause"
        " is a later round's move, never the same response's.",
    "dead_clause_rejected":
        "That formula is permanently dead and is refused before the round runs."
        " The consultation is re-asked, so what this costs is consultation time;"
        " propose different content.",
    "clause_lexical_error":
        "The clause carries a character the grammar does not have — most often"
        " `⊇` (write `(B ⊆ A)`) or `→` (write `((¬(p)) ∨ q)`); there is no `∩`"
        " and no quantifier. Write the operator characters themselves inside"
        " `payload`, since a `\\u`-escaped operator arrives as those literal"
        " characters.",
    "clause_syntax_error":
        "The characters are all in the grammar but the formula is not: usually a"
        " missing parenthesis around a prefix operator's operand."
        " `validate_clauses` returns the offset of the failure and costs no"
        " round.",
    "clause_schema_error":
        "The clause parses, but a relation name is not in the ambient schema or"
        " is used at the wrong arity. The relation table above gives every name"
        " of this task in its clause spelling, with its arity.",
    "unauthorized_drop":
        "A `dropped` entry is not one of the drop references this consultation"
        " issued. Copy the reference whole out of IDENTITIES AND DROP REFERENCES"
        " below; one kept from an earlier consultation is never eligible.",
    "malformed_json":
        "The payload was not one complete JSON value — commonly a trailing"
        " brace, a truncated document, or text wrapped around the JSON. None of"
        " it was read, so send the whole document again.",
    "duplicate_object_key":
        "One object in the document sets the same key twice, and the verifier"
        " will not guess which was meant. Rebuild the document from the RESPONSE"
        " EXAMPLE rather than editing what you sent.",
}


def _correction_section(observation):
    correction = observation.get("correction")
    if not isinstance(correction, dict):
        return []
    diagnostics = [item for item in _list(correction, "diagnostics") if isinstance(item, dict)]
    lines = ["# Correction on your previous response", "",
             "Your previous response was refused and no round ran. Fix what is named",
             "here before anything else.", ""]
    for diagnostic in diagnostics:
        lines.append("    {}: {}".format(_text(diagnostic.get("code")) or "unknown",
                                         _text(diagnostic.get("message"))))
        # `item_index` names which clause of the submission, `offset` where
        # inside it: without the second the agent has a clause number for a
        # list it keeps no copy of and nowhere to look in the text.
        for name in ("item_index", "offset", "path"):
            if diagnostic.get(name) is not None:
                lines.append(f"        {name}: {diagnostic[name]}")
        # The verifier names the exact keys it refused; show them rather than
        # leaving the agent to guess which field of the binding moved.
        details = _object(diagnostic, "details")
        for name in ("missing", "unexpected", "changed"):
            keys = _list(details, name)
            if keys:
                lines.append("        {}: {}".format(name, ", ".join(str(key) for key in keys)))
        note = CORRECTION_NOTES.get(_text(diagnostic.get("code")))
        if note:
            lines.extend("        " + line for line in _wrap(note))
    # The remedy is whatever the diagnostic above names. Only a fault at the
    # binding's own path is repaired by copying the binding: leading every
    # envelope refusal with that advice sends a proposer whose fault was a
    # stray member or a truncated document to recopy a binding already right.
    if any(_text(item.get("code")) in ENVELOPE_CODES for item in diagnostics):
        lines += ["",
                  "This is an envelope refusal: the response document is checked before",
                  "a single clause of it is read, so nothing you proposed was judged.",
                  "Fix exactly the code, path and keys named above and resend."]
    if any(_text(item.get("path")) in BINDING_PATHS for item in diagnostics):
        lines += ["",
                  "The fault is the envelope's own binding: copy the `binding` object",
                  "of the RESPONSE EXAMPLE below again, exactly, together with the",
                  "`schema_version` beside it, and change nothing else."]
    return lines + [""]


def _budget_section(feedback):
    seconds = _seconds(feedback.get("remaining_search_budget_ns"))
    lines = ["# Remaining budget", ""]
    if seconds is None:
        return lines + ["The push named no remaining search budget.", ""]
    return lines + [
        f"    about {seconds:.0f} seconds of search budget remain for this input", "",
        "That is the verifier's clock for the whole run -- proving, refuting and",
        "your turns together -- and this turn ends no later than it does; unless",
        "the run sets a separate consultation limit, it ends exactly there. If it",
        "expires while you are still working, the turn is killed with nothing",
        "submitted and the round is empty. Submit what you have before then, and",
        "spend the time on a well-motivated proposal rather than exhaustive reading.", ""]


def _tool_section(tools):
    lines = ["# Tools", ""]
    if not tools:
        return lines + ["No tools beyond the submission channel.", ""]
    for tool in tools:
        if isinstance(tool, dict):
            lines.append("    " + _text(tool.get("name")))
            lines.append("        " + " ".join(_text(tool.get("description")).split()))
    return lines + [""]


def default_tools(query_names):
    """The tools C advertises for this policy, for display only."""
    from .tool_catalog import tools_for_policy

    return tools_for_policy([name for name in query_names if isinstance(name, str)])


def _skills_section(skills):
    """The local skill library's index, when one is configured.

    The index is what the agent chooses from; the skills themselves are read
    through `get_skill`. Nothing here is rendered when no library is set, so a
    run without skills reads a prompt with no trace of them.
    """
    index = skills.index() if skills is not None and skills.enabled() else []
    if not index:
        return []
    lines = ["# Skills", "",
             "A local library of written procedures, one per kind of loop or kind of",
             "failure, read with `get_skill` by id. Before your first proposal read every",
             "skill whose description matches your task and skip the rest; on a later",
             "round, read the one that matches the failure you are answering. A skill is",
             "guidance: nothing in it is a verifier fact, and a clause it suggests is",
             "checked like any other.", ""]
    for entry in index:
        line = "    " + entry["id"]
        if entry["description"]:
            line += "  —  " + " ".join(entry["description"].split())
        if entry["applies"]:
            line += "  [applies: " + " ".join(entry["applies"].split()) + "]"
        lines.append(line)
    return lines + [""]


def render_push(observation, *, tools=None, skills=None) -> str:
    """The structured presentation of one push: C's selection and formatting."""
    feedback = _object(observation, "feedback")
    presentation = _object(feedback, "presentation")
    if tools is None:
        tools = default_tools(_list(feedback, "tools"))
    lines = [RULE, "THIS CONSULTATION", RULE, ""]
    lines += _correction_section(observation)
    lines += _task_section(presentation, feedback)
    lines += _relation_section(presentation)
    lines += _core_section(feedback)
    lines += _pending_section(feedback)
    lines += _last_round_section(feedback)
    lines += _latest_section(feedback)
    lines += _budget_section(feedback)
    lines += _tool_section(tools)
    lines += _skills_section(skills)
    return "\n".join(lines)


IDENTITY_FIELDS = ("clause_id", "record_digest", "formula_digest")


def _identity_lines(feedback):
    """One line per clause the push names: its identity, verbatim.

    The three fields are the `clause` argument of `history`,
    `strongest_refutations` and `evaluate_clauses`. They are the verifier's own
    values, selected from its clause object and re-encoded without change; C
    computes nothing here.
    """
    seen, lines = set(), []
    for key in ("core", "pending", "last_round"):
        for entry in _list(feedback, key):
            clause = _object(entry, "clause")
            identifier = clause.get("clause_id")
            if not isinstance(identifier, int) or identifier in seen:
                continue
            seen.add(identifier)
            identity = {name: clause[name] for name in IDENTITY_FIELDS if name in clause}
            lines.append(f"    clause {identifier}: " + encode(identity).decode("utf-8"))
    return lines


def _drop_lines(feedback):
    """One line per pending clause the push authorizes a drop for, verbatim."""
    lines = []
    for entry in _list(feedback, "pending"):
        reference = entry.get("drop_reference") if isinstance(entry, dict) else None
        if isinstance(reference, dict):
            lines.append(f"    clause {_identity(entry)}: " + encode(reference).decode("utf-8"))
    return lines


def _host_limit_lines(feedback):
    presentation = _object(feedback, "presentation")
    lines = []
    for limit in _list(presentation, "host_limits"):
        if isinstance(limit, dict) and isinstance(limit.get("limit"), str):
            lines.append(f"    {limit['limit']}: {limit.get('value')}")
    return lines


def render_identities(observation) -> str:
    """The values an agent hands back exactly, copied out of the push verbatim."""
    feedback = _object(observation, "feedback")
    identities = _identity_lines(feedback) or ["    none: the push names no clause yet"]
    drops = _drop_lines(feedback) or ["    none: no pending clause is authorized for a drop"]
    limits = _host_limit_lines(feedback) or ["    none"]
    return "\n".join([
        RULE, "IDENTITIES AND DROP REFERENCES", RULE, "",
        "Copied from the verifier's push exactly as it sent them; copy them exactly",
        "in turn, and never edit, shorten or recompute a digest. A clause identity",
        "is the `clause` argument of `history`, `strongest_refutations` and",
        "`evaluate_clauses`. A drop reference goes into `dropped` whole.",
        "",
        "Clause identities:",
        "",
        *identities,
        "",
        "Drop references, one per pending clause the push lets you drop:",
        "",
        *drops,
        "",
        "Host limits in force:",
        "",
        *limits,
        "",
    ])


def render_documents(observation, response_example: bytes) -> str:
    """B's response example, delimited, then the identities copied from the push."""
    return "\n".join([
        RULE, "RESPONSE ENVELOPE", RULE, "",
        "Call `submit` exactly once, with `payload` set to the complete JSON of a",
        "document of exactly this shape, encoded as a string.",
        "",
        "Copy the `binding` object from the RESPONSE EXAMPLE below exactly: every",
        "key, every value, nothing added and nothing left out. It is the only",
        "binding you are shown and the only one the verifier accepts for this",
        "consultation; it is the verifier's, never yours to invent, edit or",
        "recompute, and a binding kept from an earlier consultation is refused.",
        "",
        "Put your clause strings in `clauses` and only push-authorized drop",
        "references in `dropped`. Never drop and submit the same formula in one",
        "response: that is refused as `drop_submission_conflict`.",
        "",
        "The `candidate_counterexample` kind keeps the same `schema_version` and",
        "`binding`, omits `clauses` and `dropped` altogether, and carries `input`,",
        "one concrete instance over the input schema:",
        "",
        "    {\"schema_version\": 4, \"kind\": \"candidate_counterexample\",",
        "     \"binding\": <the RESPONSE EXAMPLE's binding object, copied whole>,",
        "     \"input\": {\"relations\": [{\"name\": \"p::E\", \"rows\": [[\"num:0\", \"num:1\"]]},",
        "                             {\"name\": \"p::T\", \"rows\": []}]}}",
        "",
        "Every relation the Relations table gives an instance name for is listed,",
        "the empty ones as `rows: []`; every cell is a domain-value string",
        "(`num:1`, `str:root`, `bool:0`). Left in empty, `clauses` and `dropped`",
        "are ignored; carrying anything they are refused.",
        "",
        "Write the operator characters themselves inside `payload` — `⊆`, `∪`, `σ`,",
        "`π`, `∅`.",
        "",
        "RESPONSE EXAMPLE:",
        response_example.decode("utf-8").strip(),
        "",
        render_identities(observation),
    ])


def render_prompt(observation, response_example: bytes, *, tools=None, skills=None,
                  first_consultation=None, budget_bytes=None) -> bytes:
    """Assets, C's presentation of the push, B's response example, the identities."""
    if not isinstance(response_example, bytes) or not response_example:
        raise ValueError("push lacks response binding")
    if not isinstance(observation, dict):
        raise ValueError("render observation: expected an observation object")
    if first_consultation is None:
        first_consultation = is_first_consultation(observation)
    if budget_bytes is None:
        budget_bytes = FIRST_BUDGET_BYTES if first_consultation else LATER_BUDGET_BYTES
    tail = "\n".join([
        render_push(observation, tools=tools, skills=skills),
        render_documents(observation, response_example),
    ])
    sections, used = [], len(tail.encode("utf-8"))
    for name in ASSET_ORDER:
        if not first_consultation and name in FIRST_CONSULTATION_ONLY:
            continue
        text = asset_text(name)
        length = len(text.encode("utf-8")) + 2
        # The unconditional assets are never weighed: whatever the push costs,
        # the agent still reads the grammar and the checking procedure.
        if (name not in UNCONDITIONAL_ASSETS and budget_bytes is not None
                and used + length > budget_bytes):
            break
        sections.append(text)
        used += length
    return "\n\n".join([*sections, tail]).encode("utf-8")
