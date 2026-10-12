"""Retain the actual serialized proof consumed by Nanoda in this one audit project."""
from pathlib import Path
import hashlib
import json
import os
import shutil
import stat
import sys
import time

root = Path(__file__).resolve().parent
project = root / 'project'
deadline = time.monotonic() + 21600
while time.monotonic() < deadline:
    for proc in Path('/proc').iterdir():
        if not proc.name.isdigit():
            continue
        try:
            if (proc / 'cwd').resolve() != project:
                continue
            args = (proc / 'cmdline').read_bytes().split(b'\0')
            if len(args) < 2 or Path(os.fsdecode(args[0])).name != 'nanoda_bin':
                continue
            config_path = Path(os.fsdecode(args[1]))
            if config_path.parent != Path('/tmp') or config_path.is_symlink():
                continue
            config = json.loads(config_path.read_text())
            source = Path(config['export_file_path'])
            if source.parent != Path('/tmp') or source.is_symlink():
                continue
            info = source.stat()
            if info.st_uid != os.getuid() or not stat.S_ISREG(info.st_mode):
                continue
            if not (0 < info.st_size < 5_000_000_000):
                continue
            destination = root / 'evidence/solution-export.ndjson'
            shutil.copyfile(source, destination)
            digest = hashlib.file_digest(destination.open('rb'), 'sha256').hexdigest()
            evidence = {'nanoda_pid':int(proc.name), 'bytes':destination.stat().st_size,
                        'sha256':digest, 'checker_config':config,
                        'claim':'Copied the actual regular export file while the configured Nanoda process was checking it.'}
            (root / 'evidence/retained-export.json').write_text(json.dumps(evidence,indent=2)+'\n')
            print('Retained actual Nanoda input:', digest, flush=True)
            sys.exit(0)
        except (FileNotFoundError, PermissionError, ProcessLookupError, KeyError, json.JSONDecodeError):
            pass
    time.sleep(1)
raise SystemExit('No matching main-project Nanoda process observed before timeout.')
