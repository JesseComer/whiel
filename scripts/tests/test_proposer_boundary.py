"""Positive/negative fixtures for the Python C / Rust B source convention."""

import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

SCRIPT = Path(__file__).resolve().parents[1] / "check_proposer_boundary.py"
SPEC = importlib.util.spec_from_file_location("proposer_boundary", SCRIPT)
GATE = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = GATE
SPEC.loader.exec_module(GATE)


class ProposerBoundaryTest(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix="whiel-proposer-boundary-")
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name).resolve()
        self.c = self.root / "agent_houdini"
        self.c.mkdir()
        for name in ("frontend.py", "__init__.py", "protocol.py", "json_wire.py", "skills.py", "prompt.py"):
            (self.c / name).write_text("")
        self.frontend = self.c / "frontend.py"
        self.lib = self.root / "whiel_runner/src/lib.rs"
        self.lib.parent.mkdir(parents=True)
        self.lib.write_text("pub mod framework2;\npub mod encoding;\npub mod proposer_api;\n")

    def check(self, source, *, file=None):
        (file or self.frontend).write_text(source)
        return GATE.check(self.root)

    def rejects(self, source, *, file=None):
        with self.assertRaises(GATE.BoundaryError):
            self.check(source, file=file)

    def test_standard_library_and_explicit_local_imports(self):
        self.check("""
import json, socket as transport
import agent_houdini.protocol as wire
from pathlib import Path as P
from collections.abc import Mapping
from agent_houdini.protocol import Endpoint as Client
from agent_houdini import skills
from .json_wire import encode
from . import prompt
from json_wire import decode
""")

    def test_private_engine_and_dynamic_imports_are_refused(self):
        for source in [
            "import whiel_runner.framework2 as hidden", "from Whiel import Verify",
            "import Databases", "from VampLean import Replay", "import whiel_synth",
            "from framework2 import State", "from importlib.util import spec_from_file_location",
            "import runpy", "import marshal", "from agent_houdini.protocol import *",
        ]:
            with self.subTest(source=source):
                self.rejects(source)

    def test_relative_imports_cannot_climb_above_c(self):
        self.check("from .protocol import Endpoint")
        self.rejects("from ..whiel_runner import framework2")
        nested = self.c / "nested"
        nested.mkdir()
        (nested / "__init__.py").write_text("")
        module = nested / "client.py"
        self.frontend.write_text("from .nested.client import entry")
        self.check("from ..protocol import Endpoint", file=module)
        self.rejects("from ...whiel_runner import framework2", file=module)

    def test_comments_docstrings_and_tool_names_are_not_imports(self):
        self.check('''
# import whiel_runner
"""ctypes.CDLL('../engine.so'); from ..Whiel import Checker"""
TOOLS = ["history", "ledger", "countermodel", "evaluate_clauses"]
MODEL = "gpt-5.5"
EXAMPLE = "from whiel_runner import state"
''')
        self.lib.write_text(r'''
// use crate::agent_houdini::prompt;
/* outer /* #[path="../../agent_houdini/rust/mod.rs"] */ */
const S: &str = "crate::agent_houdini::run();";
const R: &str = r###" #[path="../../agent_houdini/rust/mod.rs"] "###;
const B: &[u8] = br##"use crate::{agent_houdini::prompt};"##;
const Q: char = '\'';
fn f<'a>(s: &'a str) -> &'a str { s }
''')
        GATE.check(self.root)

    def test_dynamic_execution_and_import_loader_aliases_are_refused(self):
        for source in [
            "__import__('whiel_runner')", "loader = __import__\nloader('ctypes')",
            "exec('import whiel_runner')", "eval('1')", "compile('x', 'x', 'exec')",
            "from builtins import eval as e\ne('1')", "import builtins as b\nb.exec('x')",
            "import importlib as il\nil.import_module('whiel_runner')",
            "from importlib import import_module as load\nload('whiel_runner')",
            "from importlib import util as hidden", "import pkgutil\npkgutil.resolve_name('whiel_runner')",
        ]:
            with self.subTest(source=source):
                self.rejects(source)

    def test_package_bootstrap_is_allowed_in_any_c_script(self):
        source = """
import sys as system
from pathlib import Path as P
if __package__ in (None, ""):
    system.path.insert(0, str(P(__file__).resolve().parent.parent))
from agent_houdini.protocol import Endpoint
"""
        self.check(source)
        self.check(source, file=self.c / "arbitrary_launcher.py")
        self.check(source, file=self.c / "prompt.py")
        nested = self.c / "nested"
        nested.mkdir()
        self.check(source.replace(".parent.parent", ".parent.parent.parent"),
                   file=nested / "launch.py")

    def test_path_mutations_aliases_hooks_and_bootstrap_variations_fail(self):
        for source in [
            "import sys\nsys.path.append('../whiel_runner')",
            "import sys as s\ns = s.path\ns.insert(0, '/tmp')",
            "from sys import path as p\np.extend(['../Whiel'])",
            "import sys\nsys.path = ['x']", "import sys\nsys.path += ['x']",
            "import sys\nsys.modules['engine'] = object()",
            "import sys\nsys.meta_path.append(object())", "__path__ = ['../Whiel']",
            "import sys\nfrom pathlib import Path\nsys.path.insert(0, str(Path(__file__).resolve().parent.parent.parent))",
        ]:
            with self.subTest(source=source):
                self.rejects(source)

    def test_private_file_access_is_refused_without_forbidding_path_construction(self):
        for source in [
            "open('../whiel_runner/src/lib.rs').read()",
            "from pathlib import Path\nPath('../../Databases/Basic.lean').read_text()",
            "from pathlib import Path as P\nroot = P(__file__).parents[1]\n(root / 'Whiel' / 'Main.lean').read_bytes()",
            "from pathlib import Path\np = Path(__file__).parent / '..' / 'Whiel' / 'Main.lean'\np.write_text('changed')",
            "from io import open as read\nread('../VampLean/Main.lean')",
            "import os\nos.open('../whiel_synth/state.py', os.O_RDONLY)",
            "from pathlib import Path\np = Path('../Benchmark/A/Certificate/Valid.lean')\nf = open\nf(p)",
            "import shutil\nshutil.copyfile('../whiel_runner/src/lib.rs', '/tmp/copied')",
            "from pathlib import Path\nPath('/tmp/proposal.json').replace('../Whiel/Main.lean')",
            "open(file='../whiel_runner/src/lib.rs')",
            "import os\nopen(os.path.join(os.path.dirname(__file__), '..', 'whiel_runner', 'src', 'lib.rs'))",
            "from importlib import resources\nresources.files('whiel_runner').joinpath('src/lib.rs').read_text()",
            "from importlib.resources import read_text\nread_text(package='Whiel', resource='Main.lean')",
            "import pkgutil\npkgutil.get_data('whiel_runner', 'src/lib.rs')",
        ]:
            with self.subTest(source=source):
                self.rejects(source)
        self.check("""
from pathlib import Path
root = Path(__file__).resolve().parent.parent
private_targets = sorted((root / 'Benchmark').glob('*/Certificate/Valid.lean'))
source_target = root / 'whiel_runner/src/lib.rs'
asset = Path(__file__).parent / 'guide.json'
asset.read_text()
auth = Path('/tmp/agent-auth')
auth.write_text('synthetic')
Path('/etc/ssl/certs/ca-certificates.crt').read_bytes()
(root / 'toolchain/provider-sandbox/cli-lock.json').read_text()
""")

    def test_c_helpers_dependencies_subprocesses_and_system_ffi_need_no_b_edits(self):
        (self.c / "custom_helper.py").write_text("import subprocess\n")
        (self.c / "setup_cli.py").write_text("import os\nos.fork()\n")
        self.check("""
import openai, anthropic, arbitrary_future_sdk
import ctypes, ctypes.util, cffi
import importlib.metadata, importlib.resources
import socket, subprocess, os, asyncio
from subprocess import run as launch
from agent_houdini import custom_helper
from .setup_cli import prepare
libproc = ctypes.CDLL('/usr/lib/libproc.dylib')
libcustom = ctypes.CDLL('/tmp/c-owned-native/helper.so')
ffi = cffi.FFI()
ffi.dlopen('/tmp/c-owned-native/helper.so')
launch(['/tmp/custom-helper', '--mode', 'proposal'])
os.execv('/tmp/provider-cli', [])
subprocess.run(['python3', 'own_helper.py'])
asyncio.create_subprocess_exec('/tmp/provider-cli')
""")
        (self.c / "requirements.txt").write_text("arbitrary_future_sdk==1.2.3\n")
        (self.c / "provider.toml").write_text('provider = "custom"\n')
        inventory = GATE.check(self.root)
        self.assertIn(self.c / "custom_helper.py", inventory)
        self.assertIn(self.c / "requirements.txt", inventory)

    def test_private_worker_and_engine_launches_are_refused(self):
        for source in [
            "import subprocess\nsubprocess.run(['lean', 'x.lean'])",
            "from subprocess import Popen as launch\nlaunch(['/tmp/vampire'])",
            "import os\nos.system('lake env lean input.lean')",
            "import os\nos.execv('/tmp/fixed_ambient_encoding_worker', [])",
            "import os\nos.spawnv(os.P_WAIT, '/tmp/whiel-agent-tools', [])",
            "import asyncio\nasyncio.create_subprocess_exec('lean')",
            "import subprocess\nargs = ['../whiel_runner/target/debug/private-driver']\nsubprocess.run(args)",
            "import subprocess\nsubprocess.Popen(args=['lean'])",
            "import subprocess\nsubprocess.Popen(['helper'], executable='/usr/bin/lean')",
        ]:
            with self.subTest(source=source):
                self.rejects(source)
        self.check("""
import subprocess
from pathlib import Path
root = Path(__file__).resolve().parents[1]
subprocess.run([str(root / 'whiel_runner/target/debug/whiel-symbolic'), 'campaign', 'run'])
subprocess.run(['whiel-symbolic', '--help'])
# Diagnostic targets are not read merely by passing their names to C's probe.
subprocess.run(['own-sandbox-probe', str(root / 'Benchmark/A/Certificate/Valid.lean')])
""")

    def test_private_library_loading_is_refused_but_ffi_itself_is_allowed(self):
        for source in [
            "import ctypes\nctypes.CDLL('../whiel_runner/target/debug/libprivate.dylib')",
            "from ctypes import CDLL as load\nload('../whiel_runner/libprivate.so')",
            "import ctypes\nctypes.cdll.LoadLibrary('../whiel_synth/private.so')",
            "import ctypes\nctypes.cdll['../whiel_runner/private.so']",
            "import cffi\nffi = cffi.FFI()\nffi.dlopen('../whiel_runner/private.so')",
        ]:
            with self.subTest(source=source):
                self.rejects(source)

    def test_rust_and_lean_c_implementations_are_refused_but_native_assets_are_allowed(self):
        for name in ("rust/mod.rs", "checker.lean"):
            path = self.c / name
            path.parent.mkdir(exist_ok=True)
            path.write_text("")
            with self.subTest(name=name), self.assertRaises(GATE.BoundaryError):
                GATE.check(self.root)
            path.unlink()
        for name in ("native-cli", "wrapper.so", "wrapper.dylib", "wrapper.pyd"):
            (self.c / name).write_bytes(b"\x7fELF\x00\xff")
        inventory = GATE.check(self.root)
        self.assertIn(self.c / "native-cli", inventory)

    def test_b_rust_imports_grouped_aliases_and_raw_names_are_refused(self):
        for source in [
            "use crate::agent_houdini::prompt;", "use crate::agent_houdini as hidden;",
            "use crate::{proposer_api::AgentPush, agent_houdini::{prompt as hidden}};",
            "fn f() { crate::agent_houdini::prompt::render(); }",
            "use ::whiel_runner::agent_houdini::skills;",
            "fn f() { r#crate::r#agent_houdini::prompt(); }",
            "extern crate agent_houdini as hidden;", "pub mod agent_houdini;",
        ]:
            with self.subTest(source=source):
                self.rejects(source, file=self.lib)

    def test_rust_source_includes_cannot_mount_c_or_hide_computed_paths(self):
        for source in [
            '#[path="../../agent_houdini/rust/mod.rs"] mod alternate;',
            '#[cfg_attr(any(unix, windows), path=r"../../agent_houdini/rust/mod.rs")] mod alternate;',
            'include!("../../agent_houdini/rust/mod.rs");',
            'include!(concat!(env!("C_SOURCE"), "/mod.rs"));',
            'use std::include as hidden;',
            'use std::include_str as hidden;',
            'include_str!("../../agent_houdini/frontend.py");',
            'include_bytes!("../../agent_houdini/guide.json");',
            'include_str!(concat!(env!("C_SOURCE"), "/guide.json"));',
            '#[path="\\x2e\\x2e/agent_houdini/rust/mod.rs"] mod hidden;',
        ]:
            with self.subTest(source=source):
                self.rejects(source, file=self.lib)
        self.lib.write_text('#[path="internal.rs"] mod internal;\nconst B: &str = include_str!("internal.rs");')
        (self.lib.parent / "internal.rs").write_text("fn inside_b() {}")
        GATE.check(self.root)

    def test_discovered_modules_and_missing_or_ambiguous_local_imports(self):
        self.rejects("from .missing import x")
        (self.c / "protocol").mkdir()
        (self.c / "protocol/__init__.py").write_text("")
        self.rejects("from .protocol import Endpoint")
        (self.c / "protocol/__init__.py").unlink()
        (self.c / "protocol").rmdir()
        self.frontend.write_text("")
        (self.c / "skills.py").unlink()
        GATE.check(self.root)  # Removing an unused module needs no B list update.
        new = self.c / "arbitrary_new_module.py"
        new.write_text("import whiel_runner")
        with self.assertRaises(GATE.BoundaryError):
            GATE.check(self.root)
        new.unlink()
        hidden = self.c / ".custom"
        hidden.mkdir()
        (hidden / "runtime.py").write_text("import whiel_runner")
        with self.assertRaises(GATE.BoundaryError):
            GATE.check(self.root)

    def make_generated_environment(self, name):
        environment = self.c / name
        environment.mkdir(parents=True)
        (environment / "pyvenv.cfg").write_text(
            "home = /usr/bin\ninclude-system-site-packages = false\nversion = 3.13.0\n")
        packages = environment / "lib/python3.13/site-packages/sdk"
        packages.mkdir(parents=True)
        (packages / "__init__.py").write_text("import importlib.util\n")
        (environment / "bin").mkdir()
        (environment / "bin/python").symlink_to(sys.executable)
        # Virtualenv and dependency implementation files are not C's sources.
        (environment / "dependency.py").write_text("import importlib.machinery\n")
        (environment / "native_dependency.rs").write_text("fn implementation() {}")
        return environment

    def test_generated_virtual_environments_are_not_dependency_audits(self):
        for name in (".venv", "arbitrary_environment", ".cache/provider-environment"):
            with self.subTest(name=name):
                environment = self.make_generated_environment(name)
                inventory = self.check("import sdk, arbitrary_future_sdk\n")
                self.assertFalse(any(path.is_relative_to(environment) for path in inventory))
        hidden = self.c / ".custom"
        hidden.mkdir()
        source = hidden / "runtime.py"
        source.write_text("import arbitrary_future_sdk\n")
        self.assertIn(source, GATE.check(self.root))
        source.write_text("import whiel_runner\n")
        self.rejects("import sdk\n")

    def test_runtime_cannot_import_excluded_environment_source(self):
        self.make_generated_environment("environment")
        for source in [
            "import agent_houdini.environment.dependency",
            "from agent_houdini import environment",
            "from agent_houdini.environment import dependency",
            "from .environment import dependency",
            "from . import environment",
            "import environment.dependency",
            "import sys\nfrom pathlib import Path\nsys.path.insert(0, str(Path(__file__).parent / 'environment'))",
        ]:
            with self.subTest(source=source):
                self.rejects(source)
        self.check("import sdk\n")  # The selected interpreter resolves its own dependencies.

    def test_environment_marker_does_not_exempt_c_root_or_source_symlinks(self):
        marker = self.c / "pyvenv.cfg"
        marker.write_text("home = /usr/bin\n")
        self.rejects("import whiel_runner")
        marker.unlink()
        self.frontend.write_text("")
        environment = self.make_generated_environment(".venv")
        # A directory name alone is insufficient to suppress normal source checks.
        (environment / "pyvenv.cfg").unlink()
        with self.assertRaises(GATE.BoundaryError):
            GATE.check(self.root)
        marker.write_text("home = /usr/bin\n")
        (environment / "pyvenv.cfg").symlink_to(marker)
        with self.assertRaises(GATE.BoundaryError):
            GATE.check(self.root)

    def test_new_namespace_packages_and_local_shadow_modules_are_checked(self):
        nested = self.c / "extensions"
        nested.mkdir()
        (nested / "provider.py").write_text("import arbitrary_provider_sdk")
        self.check("from .extensions.provider import run")
        self.check("from agent_houdini.extensions import provider")
        (self.c / "json.py").write_text("import whiel_runner")
        self.rejects("import json")

    def test_symlink_private_file_access_is_refused(self):
        engine = self.root / "whiel_runner/src/state.txt"
        engine.write_text("private")
        outside_link = self.root / "alias"
        outside_link.symlink_to(engine)
        self.rejects("from pathlib import Path\nPath('../alias').read_text()")

    def test_symlink_source_directories_assets_and_c_root_are_refused(self):
        outside = self.root / "outside.py"
        outside.write_text("")
        for name, target, directory in (("linked.py", outside, False),
                                        ("linked", self.root, True),
                                        ("guide.json", outside, False)):
            link = self.c / name
            link.symlink_to(target, target_is_directory=directory)
            with self.subTest(name=name), self.assertRaises(GATE.BoundaryError):
                GATE.check(self.root)
            link.unlink()
        moved = self.root / "moved"
        self.c.rename(moved)
        self.c.symlink_to(moved, target_is_directory=True)
        with self.assertRaises(GATE.BoundaryError):
            GATE.check(self.root)

    def test_test_infrastructure_is_inventoried_but_cannot_be_imported_at_runtime(self):
        tests = self.c / "tests"
        tests.mkdir()
        (tests / "__init__.py").write_text("")
        test = tests / "test_fixture.py"
        test.write_text("import importlib.util\n")
        inventory = GATE.check(self.root)
        self.assertIn(test, inventory)
        self.rejects("from agent_houdini.tests.test_fixture import x")
        self.rejects("from agent_houdini import tests")
        self.rejects("from . import tests")
        nested = self.c / "nested"
        nested.mkdir()
        (nested / "tests").mkdir()
        self.rejects("from agent_houdini.nested import tests")
        self.rejects("from .nested import tests")
        cache = self.c / "__pycache__"
        cache.mkdir()
        (cache / "unchecked.py").write_text("import whiel_runner")
        self.rejects("from agent_houdini.__pycache__ import unchecked")

    def test_b_symlink_sources_and_directories_cannot_hide_c_mounts(self):
        outside = self.root / "outside.rs"
        outside.write_text("use crate::agent_houdini::prompt;")
        for name, target, directory in (("hidden.rs", outside, False),
                                        ("hidden", self.c, True)):
            link = self.lib.parent / name
            link.symlink_to(target, target_is_directory=directory)
            with self.subTest(name=name), self.assertRaises(GATE.BoundaryError):
                GATE.check(self.root)
            link.unlink()

    def test_cli_inventory_includes_runtime_assets_and_b_sources(self):
        asset = self.c / "guide.json"
        asset.write_text('{"content":"local"}')
        result = subprocess.run([sys.executable, str(SCRIPT), "--root", str(self.root), "--inventory"], capture_output=True, text=True)
        self.assertEqual(result.returncode, 0, result.stderr)
        inventory = json.loads(result.stdout)
        self.assertIn("agent_houdini/frontend.py", inventory)
        self.assertIn("agent_houdini/guide.json", inventory)
        self.assertIn("whiel_runner/src/lib.rs", inventory)
        self.frontend.write_text("import whiel_runner\n")
        result = subprocess.run([sys.executable, str(SCRIPT), "--root", str(self.root)], capture_output=True, text=True)
        self.assertEqual(result.returncode, 1)
        self.assertIn("frontend.py:1", result.stderr)

    def test_malformed_python_and_rust_literals_fail_closed(self):
        for source in ("if :", "from .protocol import (", "'unclosed"):
            with self.subTest(source=source):
                self.rejects(source)
        self.frontend.write_text("")
        for source in ('/* unclosed', 'r###"unclosed"##', '"unclosed', '#[path='):
            with self.subTest(source=source):
                self.rejects(source, file=self.lib)


if __name__ == "__main__":
    unittest.main()
