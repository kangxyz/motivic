#!/usr/bin/env python3
# Authors: kangxyz
"""Run the pinned Batteries driver on exact defining-module origins only.

The temporary runtime adapter adds one filter to Batteries scripts/runLinter.lean
at f2effa3d803fda822b1f97b806c47cf2adfbcbc2 (Apache-2.0). All native enabled
linters, options, nolints handling and failure behavior remain unchanged.
"""
import argparse
import hashlib
import os
from pathlib import Path
import subprocess
import sys
import tempfile

from library_sources import source_modules

ROOT = Path(__file__).resolve().parents[1]
DRIVER_SHA256 = '24ee54cb7f38734970b970406ad75baf7aae7a8889b939d13f7b5a8c5f20556a'
ENUMERATION = '    let decls ← getDeclsInPackage module.getRoot\n'
ORIGIN_FILTER = '''    let env ← getEnv
    let decls := decls.filter fun name =>
      match env.getModuleIdxFor? name with
      | some index => env.header.moduleNames[index]! == module
      | none => false
'''


def adapt(source: bytes) -> str:
    if hashlib.sha256(source).hexdigest() != DRIVER_SHA256:
        raise ValueError('Batteries linter driver differs from the reviewed pinned source; review its origin interface')
    text = source.decode('utf-8')
    if text.count(ENUMERATION) != 1:
        raise ValueError('Expected exactly one pinned declaration enumeration')
    return text.replace(ENUMERATION, ENUMERATION + ORIGIN_FILTER)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, default=ROOT)
    parser.add_argument('--no-build', action='store_true', required=True)
    parser.add_argument('targets', nargs='+')
    args = parser.parse_args()
    root = args.root.resolve()
    try:
        sources = source_modules(root)
        if any(name not in sources for name in args.targets):
            raise ValueError('Declaration lint requires explicit existing local module origins')
        driver = root / '.lake/packages/batteries/scripts/runLinter.lean'
        adapted = adapt(driver.read_bytes())
        with tempfile.TemporaryDirectory(prefix='motivic-declaration-runtime-') as directory:
            runtime = Path(directory) / 'RunSelectedLinter.lean'
            runtime.write_text(adapted)
            # Lake may prepend its real bin directory; name the selected guard explicitly.
            lean = os.environ.get('LEAN') or 'lean'
            # Release interpreter state between origins; the driver imports each independently.
            for origin in dict.fromkeys(args.targets):
                result = subprocess.run(['lake', 'env', lean, '--run', str(runtime),
                                         '--no-build', origin], cwd=root)
                if result.returncode:
                    return result.returncode
            return 0
    except (OSError, UnicodeError, ValueError) as error:
        print(f'Focused declaration lint failed: {error}', file=sys.stderr)
        return 1


if __name__ == '__main__':
    raise SystemExit(main())
