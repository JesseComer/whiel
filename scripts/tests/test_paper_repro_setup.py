"""PAPER REPRODUCTION CODE: synthetic setup/login checks; no network or builds."""
import hashlib
import io
import json
from pathlib import Path
import tarfile
import tempfile
import unittest
from unittest.mock import patch

from scripts import paper_repro_setup as setup
from scripts.paper_repro_common import Context, ReproError


def elf():
    return b'\x7fELF\x02\x01\x01' + b'\0' * 9 + b'\x02\0\x3e\0' + b'fixture'


class SetupTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.repo = Path(self.temporary.name).resolve()
        self.ctx = Context(self.repo, self.repo / 'artifacts/paper-reproduction')
        self.calls = []

    def fake_command(self, ctx, arguments, log=None, **kwargs):
        self.calls.append((arguments, kwargs))
        if log:
            log.parent.mkdir(parents=True, exist_ok=True)
            version = '0.154.0' if any('0.154.0' in str(v) for v in arguments) else '0.148.0'
            log.write_bytes(f'codex-cli {version}\n'.encode())
        if '--device-auth' in arguments:
            (Path(kwargs['env']['CODEX_HOME']) / 'auth.json').write_text('synthetic')
        return 0

    def native(self, version):
        binary = setup.cli_path(self.ctx, version)
        binary.parent.mkdir(parents=True)
        binary.write_bytes(elf())
        binary.chmod(0o555)
        return binary

    def metadata(self, data):
        return {'tag_name': 'rust-v0.154.0', 'draft': False, 'assets': [{
            'name': setup.MEMBER + '.tar.gz', 'id': 123, 'size': len(data),
            'browser_download_url': setup.ASTRA_URL,
            'digest': 'sha256:' + hashlib.sha256(data).hexdigest()}]}

    def archive(self, name=None, link=False, extra=False):
        output = io.BytesIO()
        with tarfile.open(fileobj=output, mode='w:gz') as tar:
            member = tarfile.TarInfo(name or setup.MEMBER)
            member.size = len(elf())
            if link:
                member.type = tarfile.SYMTYPE
                member.linkname = 'elsewhere'
            tar.addfile(member, None if link else io.BytesIO(elf()))
            if extra:
                tar.addfile(tarfile.TarInfo('extra'))
        return output.getvalue()

    def test_strict_version_and_pin(self):
        binary = self.native('0.148.0')
        lock = self.repo / 'agent_houdini/toolchain/cli-lock.json'
        lock.parent.mkdir(parents=True)
        lock.write_text(json.dumps({'packages': {setup.TARGET: {
            'binary_size': len(elf()), 'binary_sha256': hashlib.sha256(elf()).hexdigest()}}}))
        with patch.object(setup, 'command', side_effect=self.fake_command):
            self.assertEqual(setup.verify_cli(self.ctx, '0.148.0'), binary)
        binary.chmod(0o755)
        binary.write_bytes(elf() + b'changed')
        with self.assertRaises(ReproError), patch.object(setup, 'command') as command:
            setup.verify_cli(self.ctx, '0.148.0')
        command.assert_not_called()

    def test_wrong_version_fails(self):
        def command(ctx, argv, log, **kwargs):
            log.parent.mkdir(parents=True, exist_ok=True)
            log.write_text('codex-cli 0.148.0\n')
        with patch.object(setup, 'command', side_effect=command), self.assertRaises(ReproError):
            setup._version(self.ctx, Path('fake'), '0.154.0')

    def test_metadata_requires_official_digest_url_unique_asset(self):
        for mutate in (lambda m: m['assets'][0].pop('digest'),
                       lambda m: m['assets'][0].update(browser_download_url='https://example.invalid/file'),
                       lambda m: m['assets'].append(m['assets'][0]),
                       lambda m: m.update(tag_name='rust-v0.999.0')):
            value = self.metadata(b'archive')
            mutate(value)
            with self.assertRaises(ReproError):
                setup._metadata(value)

    def test_archive_rejects_links_traversal_and_extra_files(self):
        for options in ({'link': True}, {'name': '../codex'}, {'extra': True}):
            with tempfile.TemporaryDirectory(dir=self.repo) as temporary:
                root = Path(temporary)
                archive = root / 'archive.tar.gz'
                archive.write_bytes(self.archive(**options))
                with self.assertRaises(ReproError):
                    setup._extract(archive, root / 'binary')

    def test_install_and_verify_astra_without_network(self):
        archive = self.archive()
        metadata = self.metadata(archive)
        def download(url, destination, maximum, expected_hash=None):
            data = json.dumps(metadata).encode() if url == setup.ASTRA_API else archive
            if expected_hash:
                self.assertEqual(maximum, len(data))
                self.assertEqual(expected_hash, hashlib.sha256(data).hexdigest())
            destination.write_bytes(data)
        def command(ctx, arguments, log=None, **kwargs):
            self.calls.append((arguments, kwargs))
            log.parent.mkdir(parents=True, exist_ok=True)
            log.write_text('codex-cli 0.154.0\n')
        with patch.object(setup, '_download', side_effect=download) as fetch, \
                patch.object(setup, 'command', side_effect=command):
            binary = setup._install_astra(self.ctx)
            self.assertEqual(binary.read_bytes(), elf())
            self.assertEqual(fetch.call_count, 2)
            setup._install_astra(self.ctx)
            self.assertEqual(fetch.call_count, 2)
        receipt = json.loads((binary.parent / 'installation.json').read_text())
        self.assertIn('not a shipped paper binary pin', receipt['provenance'])
        self.assertTrue(all(kwargs['cleanup_group'] for _, kwargs in self.calls))

    def test_download_rejects_changed_bytes(self):
        class Response(io.BytesIO):
            pass
        opener = unittest.mock.Mock()
        opener.open.return_value = Response(b'wrong')
        with patch.object(setup.urllib.request, 'build_opener', return_value=opener), \
                self.assertRaises(ReproError):
            setup._download(setup.ASTRA_URL, self.repo / 'download', 5, '0' * 64)

    def setup_pins(self):
        (self.repo / 'lean-toolchain').write_text('leanprover/lean4:v4.30.0-rc1\n')
        (self.repo / 'lake-manifest.json').write_text('{"packages": [{"name": "fixture"}]}')
        for name in ('lakefile.toml', 'toolchain.lock.json', 'agent_houdini/toolchain/cli-lock.json'):
            path = self.repo / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text('fixture')

    def test_setup_composes_only_strict_existing_commands(self):
        self.setup_pins()
        with patch.object(setup, '_requirements'), \
                patch.object(setup, 'command', side_effect=self.fake_command), \
                patch.object(setup, 'verify_cli'), patch.object(setup, '_install_astra'):
            setup.setup(self.ctx)
        commands = [args for args, _ in self.calls]
        self.assertEqual(len(commands), 11)
        self.assertTrue(all(kwargs['cleanup_group'] for _, kwargs in self.calls))
        self.assertFalse(any('--bootstrap' in args or '--force' in args or '--launch' in args
                             for args in commands))
        self.assertTrue(any('scripts/check_toolchain.py' in args for args in commands))
        self.assertFalse(any('update' in args for args in commands))
        self.assertTrue(any(args[-4:] == ['lake', 'exe', 'cache', 'get'] for args in commands))
        self.assertTrue(all(kwargs['env']['LEAN_NUM_THREADS'] == '1' for _, kwargs in self.calls))

    def test_setup_requires_existing_manifest_without_launch(self):
        with patch.object(setup, '_requirements'), patch.object(setup, 'command') as command, \
                self.assertRaises(ReproError):
            setup.setup(self.ctx)
        command.assert_not_called()

    def test_setup_detects_changed_manifest_even_when_command_fails(self):
        self.setup_pins()
        def mutate(ctx, args, log, **kwargs):
            (self.repo / 'lake-manifest.json').write_text('{"packages": ["changed"]}')
            raise OSError('synthetic command failure')
        with patch.object(setup, '_requirements'), patch.object(setup, 'command', side_effect=mutate), \
                self.assertRaisesRegex(ReproError, 'protected source settings: lake-manifest.json'):
            setup.setup(self.ctx)
        self.assertFalse((self.ctx.output_root / 'setup.json').exists())

    def test_requirements_delegates_existing_bwrap_policy(self):
        from agent_houdini.bwrap import SandboxError
        with patch.object(setup.platform, 'system', return_value='Linux'), \
                patch.object(setup.platform, 'machine', return_value='x86_64'), \
                patch('agent_houdini.bwrap.python_relay_resources', side_effect=SandboxError('fixture policy')) as relay, \
                self.assertRaisesRegex(ReproError, 'fixture policy'):
            setup._requirements(self.ctx)
        relay.assert_called_once_with(Path(setup.sys.executable),
                                      (self.repo / 'agent_houdini/mcp_stdio.py').resolve())

    def test_login_uses_four_distinct_native_stores_and_reuses(self):
        binary = self.native('0.148.0')
        with patch.object(setup, '_requirements'), patch.object(setup, 'verify_cli', return_value=binary), \
                patch.object(setup, 'command', side_effect=self.fake_command):
            setup.login(self.ctx)
            setup.login(self.ctx)
        self.assertEqual(len(self.calls), 4)
        homes = [kwargs['env']['CODEX_HOME'] for _, kwargs in self.calls]
        self.assertEqual(len(set(homes)), 4)
        for args, kwargs in self.calls:
            self.assertIn('--device-auth', args)
            self.assertTrue(kwargs['interactive'])
            self.assertEqual((Path(kwargs['env']['CODEX_HOME']) / 'auth.json').stat().st_mode & 0o777, 0o600)

    def test_login_refuses_symlink_store_without_reading_secret(self):
        self.ctx.auth_root.mkdir(parents=True)
        elsewhere = self.repo / 'elsewhere'
        elsewhere.mkdir()
        (self.ctx.auth_root / 'worker-1').symlink_to(elsewhere)
        with patch.object(setup, '_requirements'), patch.object(setup, 'verify_cli', return_value=Path('codex')), \
                patch.object(setup, 'command') as command, self.assertRaises(ReproError):
            setup.login(self.ctx)
        command.assert_not_called()


if __name__ == '__main__':
    unittest.main()
