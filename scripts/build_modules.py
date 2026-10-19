#!/usr/bin/env python3
# Authors: kangxyz
"""Keep the pinned guarded build driver on explicit Lake module selectors."""
import hashlib
import importlib.util
from pathlib import Path
import sys

DRIVER_SHA256 = 'd8a17817fb612923fc8edae53956715cf517286bf2e5c4fa9ef4e4613c8c98a3'


def main(argv: list[str] | None = None) -> int:
    argv = sys.argv[1:] if argv is None else argv
    try:
        if not argv:
            raise ValueError('Expected the pinned build helper path and its arguments')
        path = Path(argv[0]).resolve(strict=True)
        source = path.read_bytes()
        if hashlib.sha256(source).hexdigest() != DRIVER_SHA256:
            raise ValueError('Guarded build helper differs from the reviewed source; review its target interface')
        # A separate child loads the helper's own parser and resource guard modules.
        sys.path.insert(0, str(path.parent))
        spec = importlib.util.spec_from_file_location('_motivic_module_build', path)
        helper = importlib.util.module_from_spec(spec)
        # Execute exactly the checked bytes, rather than rereading a mutable helper.
        exec(compile(source, str(path), 'exec'), helper.__dict__)
        original = helper.source_order

        def source_order(root, targets):
            if not targets or any(not name.startswith('+') or name.startswith('++') for name in targets):
                raise ValueError('Guarded module build requires explicit +MODULE selectors')
            return original(root, [name[1:] for name in targets])

        helper.source_order = source_order
        sys.argv = [str(path), *argv[1:]]
        return helper.main()
    except (OSError, ValueError) as error:
        print(f'Focused module build failed: {error}', file=sys.stderr)
        return 1


if __name__ == '__main__':
    raise SystemExit(main())
