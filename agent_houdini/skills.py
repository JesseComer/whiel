# Author: Fangzhu Shen
"""C-owned, per-consultation guidance snapshots; never engine evidence or policy.

Two storage shapes serve `get_skill`. A JSON file maps skill ids to guidance,
the original catalog, bounded at 16 KiB. A directory holds `index.json`,
`{"skills": [{"id", "description", "applies", "file"}, ...]}`, and one Markdown
file per skill: the index is what the prompt lists so the agent can choose,
the file is what `get_skill` returns. Either way the catalog is read once per
consultation into an immutable snapshot, through nonblocking opens of regular
files with a fixed byte bound per file, and edits become visible on the next
consultation. Skills are procedural guidance only: they grant no permission,
carry no verifier fact and are never evidence.
"""

from dataclasses import dataclass, field
import os
from pathlib import Path
import re
import stat

from .json_wire import decode, encode


SKILLS_FILE_ENV = "WHIEL_AGENT_SKILLS_FILE"
SKILLS_JSON_ENV = "WHIEL_AGENT_SKILLS_JSON"
MAX_SKILL_CATALOG_BYTES = 16 * 1024
MAX_SKILL_BYTES = 32 * 1024
MAX_SKILL_COUNT = 64
MAX_DESCRIPTION_CHARS = 400
MAX_SNAPSHOT_BYTES = MAX_SKILL_COUNT * MAX_SKILL_BYTES + MAX_SKILL_CATALOG_BYTES
INDEX_FILE = "index.json"
ID_PATTERN = re.compile(r"[A-Za-z0-9][A-Za-z0-9_.-]{0,63}")
FILE_PATTERN = re.compile(r"[A-Za-z0-9][A-Za-z0-9_.-]{0,127}\.md")


def _read_regular(path, maximum, what):
    """At most `maximum` + 1 bytes of one regular file, opened without blocking."""
    descriptor = os.open(path, os.O_RDONLY | getattr(os, "O_NONBLOCK", 0)
                         | getattr(os, "O_CLOEXEC", 0))
    try:
        if not stat.S_ISREG(os.fstat(descriptor).st_mode):
            raise ValueError(f"{what} must be a regular file")
        data = bytearray()
        limit = maximum + 1
        while len(data) < limit:
            part = os.read(descriptor, min(4096, limit - len(data)))
            if not part:
                break
            data.extend(part)
        return bytes(data)
    finally:
        os.close(descriptor)


@dataclass(frozen=True, slots=True)
class SkillCatalog:
    # Encoded immutable storage prevents callers from mutating nested content.
    _content: bytes | None = field(default=None, repr=False)

    @classmethod
    def _from_entries(cls, entries, maximum) -> "SkillCatalog":
        if not isinstance(entries, dict):
            raise ValueError("C skill catalog must map nonempty IDs to JSON content")
        if any(not key for key in entries):
            raise ValueError("C skill IDs must be nonempty")
        try:
            content = encode(entries, sort_keys=True, maximum=maximum)
        except (ValueError, TypeError, UnicodeError) as error:
            raise ValueError("C skill catalog exceeds its byte bound") from error
        return cls(content)

    @classmethod
    def from_json(cls, data: bytes) -> "SkillCatalog":
        try:
            entries = decode(data, maximum=MAX_SKILL_CATALOG_BYTES)
        except (ValueError, TypeError, UnicodeError) as error:
            raise ValueError("invalid or oversized C skill catalog JSON") from error
        if not isinstance(entries, dict):
            raise ValueError("C skill catalog must map nonempty IDs to JSON content")
        if any(not key for key in entries):
            raise ValueError("C skill IDs must be nonempty")
        try:
            content = encode(entries, sort_keys=True, maximum=MAX_SKILL_CATALOG_BYTES)
        except (ValueError, TypeError, UnicodeError) as error:
            raise ValueError("C skill catalog exceeds 16 KiB") from error
        return cls(content)

    @classmethod
    def from_file(cls, path) -> "SkillCatalog":
        return cls.from_json(_read_regular(path, MAX_SKILL_CATALOG_BYTES, "C skill catalog"))

    @classmethod
    def from_directory(cls, path) -> "SkillCatalog":
        """A skill library: `index.json` plus one Markdown file per skill.

        Each index entry names a skill by `id`, states in `description` what
        it is for (the line the prompt shows), optionally names in `applies`
        the loop shapes it is for, and points with `file` at a Markdown file
        beside the index. Files are read here, once, so a consultation sees
        one consistent library; nothing outside the directory is followed.
        """
        directory = Path(path)
        try:
            index = decode(_read_regular(directory / INDEX_FILE, MAX_SKILL_CATALOG_BYTES,
                                         "C skill index"), maximum=MAX_SKILL_CATALOG_BYTES)
        except (ValueError, TypeError, UnicodeError) as error:
            raise ValueError("invalid or oversized C skill index") from error
        listed = index.get("skills") if isinstance(index, dict) else None
        if not isinstance(listed, list) or len(listed) > MAX_SKILL_COUNT:
            raise ValueError(f"C skill index must list at most {MAX_SKILL_COUNT} skills")
        entries = {}
        for item in listed:
            if not isinstance(item, dict):
                raise ValueError("C skill index entries must be objects")
            identifier, name = item.get("id"), item.get("file")
            description = item.get("description", "")
            applies = item.get("applies", "")
            if not isinstance(identifier, str) or not ID_PATTERN.fullmatch(identifier):
                raise ValueError("C skill IDs must be short names without separators")
            if identifier in entries:
                raise ValueError(f"C skill index repeats {identifier}")
            if not isinstance(name, str) or not FILE_PATTERN.fullmatch(name):
                raise ValueError(f"C skill {identifier} must name a Markdown file beside the index")
            if not isinstance(description, str) or len(description) > MAX_DESCRIPTION_CHARS:
                raise ValueError(f"C skill {identifier} needs a description under {MAX_DESCRIPTION_CHARS} characters")
            if not isinstance(applies, str) or len(applies) > MAX_DESCRIPTION_CHARS:
                raise ValueError(f"C skill {identifier} has an unusable applies field")
            data = _read_regular(directory / name, MAX_SKILL_BYTES, f"C skill {identifier}")
            if len(data) > MAX_SKILL_BYTES:
                raise ValueError(f"C skill {identifier} exceeds {MAX_SKILL_BYTES} bytes")
            try:
                text = data.decode("utf-8")
            except UnicodeError as error:
                raise ValueError(f"C skill {identifier} is not UTF-8") from error
            entries[identifier] = {"description": description, "applies": applies, "text": text}
        return cls._from_entries(entries, MAX_SNAPSHOT_BYTES)

    @classmethod
    def from_path(cls, path) -> "SkillCatalog":
        """A directory library or a JSON file, whichever the path names."""
        return cls.from_directory(path) if os.path.isdir(path) else cls.from_file(path)

    @classmethod
    def from_file_environment(cls) -> "SkillCatalog":
        path = os.environ.get(SKILLS_FILE_ENV)
        return cls() if path is None else cls.from_path(path)

    @classmethod
    def from_handoff_json(cls, encoded: str) -> "SkillCatalog":
        return cls() if encoded == "null" else cls._from_entries(
            decode(encoded.encode("utf-8"), maximum=MAX_SNAPSHOT_BYTES), MAX_SNAPSHOT_BYTES)

    def enabled(self) -> bool:
        return self._content is not None

    def ids(self) -> list[str]:
        return [] if self._content is None else sorted(decode(self._content, maximum=MAX_SNAPSHOT_BYTES))

    def index(self) -> list[dict]:
        """`{id, description, applies}` per skill, in id order, for the prompt."""
        if self._content is None:
            return []
        entries = decode(self._content, maximum=MAX_SNAPSHOT_BYTES)
        listed = []
        for identifier in sorted(entries):
            value = entries[identifier]
            description = value.get("description") if isinstance(value, dict) else None
            applies = value.get("applies") if isinstance(value, dict) else None
            listed.append({"id": identifier,
                           "description": description if isinstance(description, str) else "",
                           "applies": applies if isinstance(applies, str) else ""})
        return listed

    def handoff_json(self) -> str:
        return "null" if self._content is None else self._content.decode("utf-8")

    def get(self, arguments) -> tuple[dict, bool]:
        def fail(code, message):
            return {"error": {"code": code, "message": message}}, True

        if self._content is None:
            return fail("skill_disabled", "Local skills are disabled.")
        if (not isinstance(arguments, dict) or set(arguments) != {"id"}
                or not isinstance(arguments["id"], str)):
            return fail("invalid_arguments", "Expected exactly one string id.")
        entries = decode(self._content, maximum=MAX_SNAPSHOT_BYTES)
        identifier = arguments["id"]
        if identifier not in entries:
            return fail("unknown_skill", "No local skill has that ID.")
        return {"id": identifier, "content": entries[identifier]}, False
