# Authors: kangxyz
"""Comment-aware Lean source inventory (Python 3.11+).

Lexical import parser adapted from kangxyz/aglib scripts/library_sources.py,
revision c9863095f90b8bd312af807dbf0e378df82403b5, Apache-2.0.
Copyright (c) 2026 Algebraic geometry contributors; Authors: kangxyz.
The project inventory below is specific to Motivic.
"""
from pathlib import Path
import re

# Lean identifiers used as module components, including quoted identifiers.
IDENT = r'(?:[^\W\d][\w\u0080-\uffff\'!?]*|«[^»\n]+»)'
MODULE = re.compile(IDENT + r'(?:\.' + IDENT + r')*')
IMPORT_START = re.compile(r'^[ \t]*(?:(?:public|private|meta)[ \t]+)*import\b', re.M)
KEYWORDS = {'import', 'all', 'public', 'private', 'meta', 'prelude', 'module', 'namespace',
            'section', 'end', 'open', 'set_option', 'noncomputable', 'universe',
            'variable', 'def', 'theorem', 'lemma', 'example', 'instance', 'abbrev',
            'axiom', 'constant', 'class', 'structure', 'inductive', 'attribute',
            'export', 'initialize', 'mutual', 'syntax', 'macro', 'elab'}


def strip_comments_and_strings(source: str) -> str:
    """Mask nested Lean comments and escaped strings, retaining token boundaries.

    A masked string is a non-whitespace sentinel, so an import cannot continue
    through a string into apparent module names later in the source.
    """
    result = list(source)
    i, depth = 0, 0
    while i < len(source):
        if depth:
            if source.startswith('/-', i):
                result[i:i + 2] = '  '; depth += 1; i += 2
            elif source.startswith('-/', i):
                result[i:i + 2] = '  '; depth -= 1; i += 2
            else:
                if source[i] != '\n':
                    result[i] = ' '
                i += 1
        elif source.startswith('/-', i):
            result[i:i + 2] = '  '; depth = 1; i += 2
        elif source.startswith('--', i):
            while i < len(source) and source[i] != '\n':
                result[i] = ' '; i += 1
        elif source[i] == '"':
            result[i] = '#'; i += 1
            while i < len(source):
                char = source[i]
                if char != '\n':
                    result[i] = ' '
                i += 1
                if char == '\\' and i < len(source):
                    if source[i] != '\n':
                        result[i] = ' '
                    i += 1
                elif char == '"':
                    break
        elif source[i] == '«':
            # Comment/string delimiters inside a quoted identifier are literal.
            end = source.find('»', i + 1)
            i = len(source) if end < 0 else end + 1
        else:
            i += 1
    return ''.join(result)


def lean_imports(source: str) -> list[str]:
    """Read single/multiple/multiline imports with optional Lean modifiers."""
    clean = strip_comments_and_strings(source)
    imports = []
    for start in IMPORT_START.finditer(clean):
        position = start.end()
        # `all` modifies the import; it is not a module named `all`.
        modifier = re.match(r'\s+all\b', clean[position:])
        if modifier:
            position += modifier.end()
        while position < len(clean):
            while position < len(clean) and clean[position].isspace():
                position += 1
            match = MODULE.match(clean, position)
            if not match or match.group() in KEYWORDS:
                break
            # Normalize quoted ordinary identifiers to prevent namespace bypasses.
            token = re.sub(r'«([^»]+)»', lambda m: m[1] if
                           re.fullmatch(r'[^\W\d]\w*', m[1]) else m[0], match.group())
            imports.append(token)
            position = match.end()
    return imports


def uses_module_system(source: str) -> bool:
    """Recognize a real module header after comments, rather than quoted prose."""
    return re.match(r'\s*module\b', strip_comments_and_strings(source)) is not None


def is_import_surface(source: str) -> bool:
    """Recognize import-only APIs without treating foundational definitions as facades.

    Adapted from the same pinned Aglib source identified above. Empty public
    sections and generated import-file size metadata do not add declarations.
    """
    remaining = strip_comments_and_strings(source).lstrip()
    remaining = re.sub(r'^module\b\s*', '', remaining)
    remaining = re.sub(r'^prelude\b\s*', '', remaining)
    while match := IMPORT_START.match(remaining):
        position = match.end()
        modifier = re.match(r'\s+all\b', remaining[position:])
        if modifier:
            position += modifier.end()
        while position < len(remaining):
            while position < len(remaining) and remaining[position].isspace():
                position += 1
            token = MODULE.match(remaining, position)
            if not token or token.group() in KEYWORDS:
                break
            position = token.end()
        remaining = remaining[position:].lstrip()
    remaining = re.sub(r'^set_option\s+linter\.style\.longFile\s+\d+\s*', '', remaining)
    return re.fullmatch(r'(?:@\[\s*expose\s*\]\s*)?(?:public\s+)?(?:meta\s+)?section\s*',
                        remaining) is not None or not remaining


def module_path(module: str) -> Path:
    parts = [part[1:-1] if part.startswith('«') else part
             for part in re.findall(IDENT, module)]
    return Path(*parts[:-1], parts[-1] + '.lean')


def module_name(path: Path | str) -> str:
    return Path(path).with_suffix('').as_posix().replace('/', '.')



ROOTS = ('Motivic', 'MotivicTest')


def source_modules(root: Path) -> dict[str, Path]:
    """Include occupied roots and leaves; never invent a missing facade."""
    result = {}
    for name in ROOTS:
        facade = root / (name + '.lean')
        if facade.is_file():
            result[name] = facade
        for path in (root / name).rglob('*.lean'):
            result[module_name(path.relative_to(root))] = path
    return result


def client_sources(root: Path) -> dict[str, Path]:
    """Inventory the independent client in its own module-resolution namespace."""
    client = root / 'examples/downstream'
    return {module_name(path.relative_to(client)): path
            for path in client.rglob('*.lean')
            if '.lake' not in path.relative_to(client).parts}
