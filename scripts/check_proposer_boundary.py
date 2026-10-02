#!/usr/bin/env python3
"""Check mechanical Python C / Rust B source ownership conventions.

C owns agent execution and may use subprocesses, sockets, native executables,
its own files, helper modules and third-party packages. Every C runtime Python
module is discovered; no provider, dependency or helper filename is privileged.
Generated virtual environments rooted at an ordinary pyvenv.cfg are excluded
from the source inventory. Their installed dependencies are not audited, and C
cannot import those excluded trees as local source packages. The marker is a
layout convention, not proof that an environment or dependency is safe.
Private engine imports, Python source/import-loader bypasses, identifiable private
engine file access and direct worker/solver launches are unsupported. Constructing
paths (including denied-access preflight targets) is not an engine read.

This is a review/CI convention, NOT an OS sandbox, dependency audit, Python/Rust
resolver or proof against hostile code. It recognizes ordinary imports, simple
aliases/paths and known file/process calls; arbitrary reflection, generated code,
interprocedural flows, subprocess implementations and installed dependencies need
review. C tests may inspect B fixtures but cannot be imported by runtime code.
B cannot compile C sources or assets into its crate. Provider-neutrality of B's
behavior is a separate migration/review gate, not established by this check.
"""

import argparse
import ast
from dataclasses import dataclass
import hashlib
import json
from pathlib import Path
import re
import shlex
import sys

DEFAULT_ROOT = Path(__file__).resolve().parents[1]


class BoundaryError(ValueError):
    pass


@dataclass(frozen=True)
class Token:
    text: str
    line: int
    literal: str | None = None


def lex(source: str) -> list[Token]:
    """A small token lexer; literal contents never become source tokens."""
    result = []
    i, line = 0, 1
    while i < len(source):
        start, start_line = i, line
        if source[i].isspace():
            i += 1
        elif source.startswith("//", i):
            end = source.find("\n", i)
            i = len(source) if end < 0 else end
        elif source.startswith("/*", i):
            depth, i = 1, i + 2
            while depth and i < len(source):
                if source.startswith("/*", i):
                    depth, i = depth + 1, i + 2
                elif source.startswith("*/", i):
                    depth, i = depth - 1, i + 2
                else:
                    i += 1
            if depth:
                raise BoundaryError(f"line {start_line}: unterminated block comment")
        else:
            raw = re.match(r'(?:br|cr|r)(#*)"', source[i:])
            string = re.match(r'(?:b|c)?"', source[i:])
            char = re.match(r"b?'(?:\\(?:u\{[0-9a-fA-F_]+\}|x[0-9a-fA-F]{2}|.)|[^'\\\n])'", source[i:])
            identifier = re.match(r'(?:r#)?[A-Za-z_][A-Za-z_0-9]*', source[i:])
            if raw:
                body = i + raw.end()
                closing = '"' + raw[1]
                end = source.find(closing, body)
                if end < 0:
                    raise BoundaryError(f"line {start_line}: unterminated raw string")
                i = end + len(closing)
                value = source[body:end] if source[start] == 'r' else None
                result.append(Token("literal", line, value))
            elif string:
                body = i + string.end()
                i = body
                escaped = False
                while i < len(source) and source[i] != '"':
                    if source[i] == "\\":
                        escaped = True
                        i += 2
                    else:
                        i += 1
                if i >= len(source):
                    raise BoundaryError(f"line {start_line}: unterminated string")
                value = source[body:i] if not escaped and source[start] == '"' else None
                i += 1
                result.append(Token("literal", line, value))
            elif char:
                i += char.end()
                result.append(Token("character", line))
            elif identifier:
                i += identifier.end()
                result.append(Token(identifier[0].removeprefix("r#"), line))
            else:
                punctuation = "::" if source.startswith("::", i) else source[i]
                i += len(punctuation)
                result.append(Token(punctuation, line))
        line += source[start:i].count("\n")
    return result


def plain_identifier(text: str) -> bool:
    return re.fullmatch(r"[A-Za-z_][A-Za-z_0-9]*", text) is not None


def use_paths(tokens: list[Token]) -> list[list[str]]:
    """Expand a supported use tree, including nested groups and aliases."""
    texts = [token.text for token in tokens]
    paths = []
    i = 0

    def tree(prefix: list[str]) -> None:
        nonlocal i
        parts = list(prefix)
        if i < len(texts) and texts[i] == "::":
            i += 1
        while i < len(texts):
            if texts[i] == "{":
                i += 1
                while i < len(texts) and texts[i] != "}":
                    tree(parts)
                    if i < len(texts) and texts[i] == ",":
                        i += 1
                    elif i >= len(texts) or texts[i] != "}":
                        raise BoundaryError("unsupported grouped import")
                if i >= len(texts):
                    raise BoundaryError("unterminated grouped import")
                i += 1
                return
            if texts[i] != "*" and not plain_identifier(texts[i]):
                raise BoundaryError("unsupported import syntax")
            parts.append(texts[i])
            i += 1
            if i < len(texts) and texts[i] == "::":
                i += 1
                continue
            if i < len(texts) and texts[i] == "as":
                i += 1
                if i >= len(texts) or not plain_identifier(texts[i]):
                    raise BoundaryError("unsupported import alias")
                i += 1
            paths.append(parts)
            return
        raise BoundaryError("incomplete import path")

    tree([])
    if i != len(texts):
        raise BoundaryError("unsupported import suffix")
    return paths


def checked_file(path: Path, boundary: Path) -> Path:
    """Check every lexical component before resolving so symlinks cannot hide."""
    if path.is_absolute() and not path.is_relative_to(boundary):
        raise BoundaryError(f"path escapes {boundary}: {path}")
    current = path
    while current != boundary:
        if current.is_symlink():
            raise BoundaryError(f"symlink source/asset is unsupported: {current}")
        if current.parent == current:
            raise BoundaryError(f"path escapes {boundary}: {path}")
        current = current.parent
    if boundary.is_symlink():
        raise BoundaryError(f"symlink source root: {boundary}")
    resolved = path.resolve()
    if not resolved.is_relative_to(boundary.resolve()) or not resolved.is_file():
        raise BoundaryError(f"missing or escaping source/asset: {path}")
    return resolved


# These describe the private engine/source boundary, never C's implementation
# inventory or its choice of dependencies. Rust/Lean implementations belong A/B;
# installed native tools and third-party binary assets are legitimate C inputs.
ENGINE_ROOTS = frozenset({"whiel_runner", "whiel_synth", "Whiel", "Databases", "VampLean"})
PRIVATE_MODULES = ENGINE_ROOTS | {"framework2"}
PRIVATE_PATH_PARTS = ENGINE_ROOTS | {"Benchmark", ".lake"}
FORBIDDEN_SOURCE_SUFFIXES = frozenset({".rs", ".lean"})
DYNAMIC_NAMES = frozenset({"__import__", "eval", "exec", "compile"})
DYNAMIC_MODULES = frozenset({"runpy", "marshal", "_imp"})
DYNAMIC_PREFIXES = (
    "importlib.util", "importlib.machinery", "importlib.import_module",
    "importlib.__import__", "importlib.reload", "pkgutil.get_loader",
    "pkgutil.find_loader", "pkgutil.resolve_name",
)
# This is B's public executable surface, not an allowlist of C/native programs.
PUBLIC_ENGINE_COMMANDS = frozenset({"whiel-symbolic"})
PRIVATE_COMMANDS = frozenset({
    "lean", "lake", "vampire", "leancheck", "whiel-agent-tools",
    "fixed_ambient_encoding_worker", "example0012_encoding_worker",
    "benchmark_encoding_worker",
})
FILE_FUNCTIONS = frozenset({
    "open", "builtins.open", "io.open", "os.open", "os.remove", "os.unlink",
    "os.rename", "os.replace", "shutil.copy", "shutil.copy2", "shutil.copyfile",
    "shutil.copytree", "shutil.move", "shutil.rmtree",
    "ctypes.CDLL", "ctypes.PyDLL", "ctypes.WinDLL", "ctypes.OleDLL",
    "ctypes.cdll.LoadLibrary", "ctypes.pydll.LoadLibrary",
})
PATH_IO_METHODS = frozenset({
    "open", "read_text", "read_bytes", "write_text", "write_bytes", "unlink",
    "rename", "replace", "touch", "rmdir", "mkdir",
})
RESOURCE_FUNCTIONS = frozenset({
    "importlib.resources.files", "importlib.resources.path",
    "importlib.resources.open_text", "importlib.resources.open_binary",
    "importlib.resources.read_text", "importlib.resources.read_binary",
    "pkgutil.get_data",
})
PROCESS_FUNCTIONS = frozenset({
    "subprocess.run", "subprocess.Popen", "subprocess.call",
    "subprocess.check_call", "subprocess.check_output",
    "subprocess.getoutput", "subprocess.getstatusoutput", "os.system", "os.popen",
    "asyncio.create_subprocess_exec", "asyncio.create_subprocess_shell",
})


def dotted(node, aliases):
    if isinstance(node, ast.Name):
        return aliases.get(node.id, node.id)
    if isinstance(node, ast.Attribute):
        parent = dotted(node.value, aliases)
        return parent + "." + node.attr if parent else None
    return None


def source_path(node, path, aliases, paths):
    """Recognize literals and simple paths/aliases, not arbitrary Python values.

    Relative literal paths are interpreted next to the source for this source
    convention. Runtime working directories and function argument flows are not
    inferred. Merely recognizing a path does not refuse it; inspect its use.
    """
    if isinstance(node, ast.Constant) and isinstance(node.value, str):
        value = Path(node.value)
        return value if value.is_absolute() else path.parent / value
    if isinstance(node, ast.Name):
        return path if node.id == "__file__" else paths.get(node.id)
    if isinstance(node, ast.Call):
        name = dotted(node.func, aliases)
        if name in ("pathlib.Path", "Path", "str", "os.fspath") and len(node.args) == 1 and not node.keywords:
            return source_path(node.args[0], path, aliases, paths)
        if name == "os.path.join" and node.args:
            base = source_path(node.args[0], path, aliases, paths)
            if base is not None and all(isinstance(arg, ast.Constant) and isinstance(arg.value, str)
                                        for arg in node.args[1:]):
                return base.joinpath(*(arg.value for arg in node.args[1:]))
        if name in ("os.path.dirname", "os.path.abspath", "os.path.realpath") and len(node.args) == 1:
            base = source_path(node.args[0], path, aliases, paths)
            if base is not None:
                return base.parent if name == "os.path.dirname" else base.resolve()
        if isinstance(node.func, ast.Attribute):
            base = source_path(node.func.value, path, aliases, paths)
            if base is not None:
                if node.func.attr in ("resolve", "absolute") and not node.args:
                    return base.resolve()
                if node.func.attr == "joinpath" and all(
                    isinstance(arg, ast.Constant) and isinstance(arg.value, str) for arg in node.args
                ):
                    return base.joinpath(*(arg.value for arg in node.args))
                if (node.func.attr in ("with_suffix", "with_name") and len(node.args) == 1
                        and isinstance(node.args[0], ast.Constant) and isinstance(node.args[0].value, str)):
                    return getattr(base, node.func.attr)(node.args[0].value)
    if isinstance(node, ast.Attribute) and node.attr == "parent":
        base = source_path(node.value, path, aliases, paths)
        return base.parent if base is not None else None
    if (isinstance(node, ast.Subscript) and isinstance(node.value, ast.Attribute)
            and node.value.attr == "parents" and isinstance(node.slice, ast.Constant)
            and type(node.slice.value) is int and node.slice.value >= 0):
        base = source_path(node.value.value, path, aliases, paths)
        if base is not None:
            try:
                return base.parents[node.slice.value]
            except IndexError as error:
                raise BoundaryError("source parent path exceeds filesystem root") from error
    if (isinstance(node, ast.BinOp) and isinstance(node.op, ast.Div)
            and isinstance(node.right, ast.Constant) and isinstance(node.right.value, str)):
        base = source_path(node.left, path, aliases, paths)
        return base / node.right.value if base is not None else None
    return None


def generated_environment(directory, boundary):
    """Recognize the standard venv boundary, not a particular directory name.

    Do not exempt C itself or linked markers. This marks installed dependency
    trees outside the source audit; it does not attest their origin or safety.
    """
    marker = directory / "pyvenv.cfg"
    return (directory != boundary and directory.is_relative_to(boundary)
            and marker.is_file() and not marker.is_symlink())


def c_source_entries(boundary):
    """Discover C sources/assets without traversing generated environments."""
    directories = [boundary]
    while directories:
        for path in sorted(directories.pop().iterdir()):
            if path.name in ("__pycache__", ".git"):
                continue
            # Source symlinks remain errors; only links *inside* an excluded
            # environment (e.g. bin/python) fall outside this source audit.
            if not path.is_symlink() and path.is_dir():
                if generated_environment(path, boundary):
                    continue
                directories.append(path)
            yield path


def local_module(name, package, boundary):
    parts = name.split(".") if name else []
    candidate = package.joinpath(*parts)
    options = [candidate.with_suffix(".py"), candidate / "__init__.py"]
    present = [item for item in options if item.exists() or item.is_symlink()]
    # Namespace packages are supported without requiring an __init__.py file.
    if not present and candidate.is_dir():
        if candidate.is_symlink() or not candidate.resolve().is_relative_to(boundary):
            raise BoundaryError("local namespace package escapes C")
        selected = candidate
    elif len(present) == 1:
        selected = checked_file(present[0], boundary)
    else:
        raise BoundaryError(f"local import must resolve to one ordinary C module: {name}")
    if any(generated_environment(parent, boundary) for parent in (selected, *selected.parents)
           if parent.is_relative_to(boundary)):
        raise BoundaryError("runtime may not import an excluded virtual environment as C source")
    if {"tests", "__pycache__", ".git"}.intersection(selected.relative_to(boundary).parts):
        raise BoundaryError("runtime may not import C test/cache infrastructure")
    return selected


def private_path(candidate, boundary):
    if candidate is None:
        return False
    resolved = candidate.resolve()
    if resolved.is_relative_to(boundary):
        return False
    return bool(PRIVATE_PATH_PARTS.intersection(resolved.parts))


def package_bootstrap(node, path, boundary, aliases, paths):
    """Allow the same package-root bootstrap in any C script, including aliases."""
    if (dotted(node.func, aliases) != "sys.path.insert" or len(node.args) != 2
            or node.keywords or not isinstance(node.args[0], ast.Constant)
            or type(node.args[0].value) is not int or node.args[0].value != 0):
        return False
    # Require a __file__-derived path, not a coincidentally matching literal.
    if not any(isinstance(child, ast.Name) and child.id == "__file__"
               for child in ast.walk(node.args[1])):
        return False
    selected = source_path(node.args[1], path, aliases, paths)
    return selected is not None and selected.resolve() == boundary.parent


def check_python(path, boundary):
    try:
        tree = ast.parse(path.read_text(encoding="utf-8"), filename=str(path))
    except SyntaxError as error:
        raise BoundaryError(f"{path}:{error.lineno}: invalid Python source") from error
    aliases, paths, values = {}, {}, {}
    for node in ast.walk(tree):
        if isinstance(node, ast.Import):
            for item in node.names:
                aliases[item.asname or item.name.split(".")[0]] = item.name if item.asname else item.name.split(".")[0]
        elif isinstance(node, ast.ImportFrom):
            for item in node.names:
                aliases[item.asname or item.name] = ".".join(filter(None, (node.module, item.name)))
    # Limited simple-alias propagation, deliberately not general data-flow or
    # scope analysis. Dynamic loading remains unsupported even through aliases.
    for _ in range(4):
        for node in ast.walk(tree):
            if isinstance(node, (ast.Assign, ast.AnnAssign)):
                targets = node.targets if isinstance(node, ast.Assign) else [node.target]
                for target in targets:
                    if isinstance(target, ast.Name) and node.value is not None:
                        values[target.id] = node.value
                        origin = dotted(node.value, aliases)
                        if origin:
                            aliases[target.id] = origin
                        resolved = source_path(node.value, path, aliases, paths)
                        if resolved is not None:
                            paths[target.id] = resolved

    def imported(name, level=0):
        base = name.split(".")[0] if name else ""
        if base in PRIVATE_MODULES:
            raise BoundaryError("private engine import is unsupported in C; use the public process API")
        if base in DYNAMIC_MODULES or any(name == prefix or name.startswith(prefix + ".")
                                        for prefix in DYNAMIC_PREFIXES):
            raise BoundaryError("dynamic source/import loader is unsupported in C")
        if level:
            package = path.parent
            for _ in range(level - 1):
                package = package.parent
            if not package.is_relative_to(boundary):
                raise BoundaryError("relative import climbs above C")
            return package, name
        if base == "agent_houdini":
            return boundary, name.partition(".")[2]
        # Resolve direct-script imports if their root exists in C. Otherwise the
        # ordinary Python import is a stdlib/third-party dependency. Do not ask B
        # to enumerate, install, import or approve C's dependency graph.
        for package in dict.fromkeys((path.parent, boundary)):
            if (package / base).exists() or (package / (base + ".py")).exists():
                return package, name
        return None

    def inspect_file(node):
        selected = source_path(node, path, aliases, paths)
        if private_path(selected, boundary):
            raise BoundaryError("private engine/proof file access bypasses the public API")

    def inspect_process(node):
        # Ordinary argv lists and simple aliases are covered. Arbitrary helper
        # argument semantics and generated shell programs are outside this gate.
        seen = set()
        while isinstance(node, ast.Name) and node.id in values and node.id not in seen:
            seen.add(node.id)
            node = values[node.id]
        if isinstance(node, (ast.List, ast.Tuple)):
            node = node.elts[0] if node.elts else None
        if node is None:
            return
        selected = source_path(node, path, aliases, paths)
        if selected is None:
            return
        if isinstance(node, ast.Constant) and isinstance(node.value, str):
            # Cover the executable in a literal shell command without treating
            # every argument (e.g. denied preflight targets) as a file read.
            command = shlex.split(node.value)
            if not command:
                return
            selected = Path(command[0])
        if selected.name in PRIVATE_COMMANDS:
            raise BoundaryError("private worker/solver launch bypasses the public API")
        if private_path(selected, boundary) and selected.name not in PUBLIC_ENGINE_COMMANDS:
            raise BoundaryError("private engine executable bypasses the public API")

    for node in ast.walk(tree):
        try:
            if isinstance(node, ast.Import):
                for item in node.names:
                    selected = imported(item.name)
                    if selected is not None:
                        local_module(selected[1], selected[0], boundary)
            elif isinstance(node, ast.ImportFrom):
                selected = imported(node.module or "", node.level)
                if any(item.name == "*" for item in node.names):
                    raise BoundaryError("wildcard Python imports are unsupported")
                if selected is not None:
                    package, module = selected
                    if module:
                        imported_path = local_module(module, package, boundary)
                        if imported_path.is_dir() or imported_path.name == "__init__.py":
                            directory = imported_path if imported_path.is_dir() else imported_path.parent
                            for item in node.names:
                                if ((directory / item.name).exists()
                                        or (directory / (item.name + ".py")).exists()):
                                    local_module(item.name, directory, boundary)
                    else:
                        for item in node.names:
                            local_module(item.name, package, boundary)
                for item in node.names:
                    imported(".".join(filter(None, (node.module, item.name))))
            name = dotted(node, aliases)
            if name:
                if name in DYNAMIC_NAMES or name in {"builtins." + item for item in DYNAMIC_NAMES}:
                    raise BoundaryError("dynamic execution/import is unsupported in C")
                if any(name == prefix or name.startswith(prefix + ".") for prefix in DYNAMIC_PREFIXES):
                    raise BoundaryError("dynamic source/import loader is unsupported in C")
                if name == "__path__" or name.startswith(("sys.meta_path", "sys.path_hooks", "sys.path_importer_cache", "sys.modules")):
                    raise BoundaryError("Python import-loader mutation is unsupported")
                if name == "sys.path" and isinstance(node.ctx, (ast.Store, ast.Del)):
                    raise BoundaryError("sys.path mutation requires a C package-root bootstrap")
            if isinstance(node, ast.Subscript) and dotted(node.value, aliases) in (
                "ctypes.cdll", "ctypes.pydll", "ctypes.windll", "ctypes.oledll",
            ):
                inspect_file(node.slice)
            if isinstance(node, ast.Call):
                target = dotted(node.func, aliases) or ""
                if target.startswith("sys.path.") and not package_bootstrap(node, path, boundary, aliases, paths):
                    raise BoundaryError("sys.path mutation requires a C package-root bootstrap")
                if target in RESOURCE_FUNCTIONS:
                    anchors = list(node.args[:1]) + [keyword.value for keyword in node.keywords
                                                   if keyword.arg in ("anchor", "package")]
                    for anchor in anchors:
                        if (isinstance(anchor, ast.Constant) and isinstance(anchor.value, str)
                                and anchor.value.split(".")[0] in PRIVATE_MODULES):
                            raise BoundaryError("private engine resource access bypasses the public API")
                if target in FILE_FUNCTIONS:
                    for arg in node.args:
                        inspect_file(arg)
                    for keyword in node.keywords:
                        if keyword.arg in ("file", "path", "src", "dst", "name"):
                            inspect_file(keyword.value)
                if isinstance(node.func, ast.Attribute) and node.func.attr in ("dlopen", "LoadLibrary"):
                    for arg in node.args:
                        inspect_file(arg)
                if isinstance(node.func, ast.Attribute) and node.func.attr in PATH_IO_METHODS:
                    inspect_file(node.func.value)
                    if node.func.attr in ("rename", "replace") and node.args:
                        inspect_file(node.args[0])
                if (target in PROCESS_FUNCTIONS or target.startswith(("os.exec", "os.spawn"))):
                    position = 1 if target.startswith("os.spawn") else 0
                    if len(node.args) > position:
                        inspect_process(node.args[position])
                    for keyword in node.keywords:
                        if keyword.arg in ("args", "executable", "program", "cmd"):
                            inspect_process(keyword.value)
        except (BoundaryError, OSError, ValueError) as error:
            raise BoundaryError(f"{path}:{getattr(node, 'lineno', 1)}: {error}") from error


def check_rust_host(path, root):
    """Reject C implementation imports/mounts; ordinary strings are not imports."""
    tokens = lex(path.read_text(encoding="utf-8"))
    for index, token in enumerate(tokens):
        try:
            if token.text == "agent_houdini":
                previous = tokens[index - 1].text if index else ""
                following = tokens[index + 1].text if index + 1 < len(tokens) else ""
                if previous in ("mod", "::", "use", "crate", "{", ",") or following == "::":
                    raise BoundaryError("B may not import or mount the C implementation")
            if token.text == "use":
                end = index + 1
                while end < len(tokens) and tokens[end].text != ";":
                    end += 1
                for parts in use_paths(tokens[index + 1:end]):
                    if "agent_houdini" in parts:
                        raise BoundaryError("B may not import the C implementation")
                    if parts[-1] in ("include", "include_str", "include_bytes"):
                        raise BoundaryError("aliasing Rust source/asset inclusion is unsupported")
            if token.text == "#":
                begin = index + 1
                if begin < len(tokens) and tokens[begin].text == "!":
                    begin += 1
                if begin < len(tokens) and tokens[begin].text == "[":
                    depth, end = 1, begin + 1
                    while end < len(tokens) and depth:
                        if tokens[end].text == "[":
                            depth += 1
                        elif tokens[end].text == "]":
                            depth -= 1
                        if tokens[end].text == "path" and end + 1 < len(tokens) and tokens[end + 1].text == "=":
                            literal = tokens[end + 2].literal if end + 2 < len(tokens) else None
                            if literal is None:
                                raise BoundaryError("computed/escaped Rust source paths are unsupported")
                            selected = path.parent / literal
                            if not selected.resolve().is_relative_to(root / "whiel_runner"):
                                raise BoundaryError("Rust source inclusion escapes B")
                        end += 1
                    if depth:
                        raise BoundaryError("unterminated Rust source attribute")
            if token.text in ("include", "include_str", "include_bytes") and index + 1 < len(tokens) and tokens[index + 1].text == "!":
                args = tokens[index + 2:index + 5]
                if len(args) != 3 or args[0].text != "(" or args[1].literal is None or args[2].text != ")":
                    raise BoundaryError("computed Rust source/asset inclusion is unsupported")
                selected = (path.parent / args[1].literal).resolve()
                if token.text == "include" and not selected.is_relative_to(root / "whiel_runner"):
                    raise BoundaryError("Rust source inclusion escapes B")
                if selected.is_relative_to(root / "agent_houdini"):
                    raise BoundaryError("B may not compile C source/assets into its binary")
        except BoundaryError as error:
            raise BoundaryError(f"{path}:{token.line}: {error}") from error


def check(root: Path) -> list[Path]:
    root = root.resolve()
    boundary = root / "agent_houdini"
    if not boundary.is_dir() or boundary.is_symlink():
        raise BoundaryError(f"missing or symlink C package root: {boundary}")
    inventory = set()
    for path in c_source_entries(boundary):
        relative = path.relative_to(boundary)
        if path.is_symlink():
            raise BoundaryError(f"symlink C source/asset is unsupported: {path}")
        if path.suffix.lower() in FORBIDDEN_SOURCE_SUFFIXES:
            raise BoundaryError(f"C runtime implementations must be Python, not Rust/Lean sources: {path}")
        if path.is_file():
            inventory.add(checked_file(path, boundary))
            if path.suffix == ".py" and "tests" not in relative.parts:
                check_python(path, boundary)
    engine = root / "whiel_runner/src"
    lib = checked_file(engine / "lib.rs", engine)
    inventory.add(lib)
    for entry in engine.rglob("*"):
        if entry.is_symlink():
            raise BoundaryError(f"symlink B source entry is unsupported: {entry}")
    for path in sorted(engine.rglob("*.rs")):
        checked_file(path, engine)
        check_rust_host(path, root)
        inventory.add(path.resolve())
    return sorted(inventory)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=DEFAULT_ROOT)
    parser.add_argument("--inventory", action="store_true", help="emit checked source/asset SHA256 JSON")
    args = parser.parse_args()
    root = args.root.resolve()
    try:
        paths = check(root)
    except (BoundaryError, OSError, UnicodeError) as error:
        print(f"proposer source convention: {error}", file=sys.stderr)
        return 1
    if args.inventory:
        print(json.dumps({str(path.relative_to(root.resolve())): hashlib.sha256(path.read_bytes()).hexdigest() for path in paths}, indent=2))
    else:
        print(f"proposer source convention passed ({len(paths)} source/asset files; not a security boundary)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
