#!/usr/bin/env python3
# Authors: kangxyz
"""Compatibility launcher for the installed Lean toolkit."""
import sys
from shared_workflow import forward


def main(argv=None):
    argv = sys.argv[1:] if argv is None else argv
    return forward('build', argv)


if __name__ == '__main__':
    sys.dont_write_bytecode = True
    raise SystemExit(main())
