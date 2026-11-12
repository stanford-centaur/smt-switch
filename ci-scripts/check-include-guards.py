#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 the smt-switch authors
# SPDX-FileContributor: Áron Ricardo Perez-Lopez
# SPDX-License-Identifier: BSD-3-Clause

"""Check that each header given has an include guard named after it.

External users include a header as smt-switch/<name>.h, so the guard of
name.h is SMT_SWITCH_NAME_H. Its #ifndef and #define follow the header
comment directly, and the file ends with `#endif  // SMT_SWITCH_NAME_H`.
A source file must not have an include guard, whatever its name, and no
file may use #pragma once. A configured name.h.in is checked as the
name.h it becomes.
"""

import re
import sys
from pathlib import Path

HEADER_SUFFIXES = {".h", ".hh", ".hpp", ".hxx"}
LEADING_COMMENTS = re.compile(r"(?:\s|//[^\n]*|/\*.*?\*/)*", re.DOTALL)
PRAGMA_ONCE = re.compile(r"^\s*#\s*pragma\s+once\b", re.MULTILINE)
ANY_GUARD_OPENING = re.compile(r"\s*#\s*ifndef\s+(\w+)\s*\n\s*#\s*define\s+\1\s*\n")
FINAL_ENDIF = re.compile(r"\n\s*#\s*endif\b[^\n]*\s*\Z")


def header_problems(path, text, comments):
    name = path.name.removesuffix(".in")
    guard = "SMT_SWITCH_" + re.sub(r"[^0-9A-Za-z]", "_", name).upper()
    found = []
    prefix = comments + "\n" if comments else ""
    if not text.startswith(f"{prefix}#ifndef {guard}\n#define {guard}\n"):
        found.append(
            f"does not open with #ifndef {guard} and #define {guard} "
            "on the lines right after the header comment"
        )
    if not text.endswith(f"\n#endif  // {guard}\n"):
        found.append(f"does not end with #endif  // {guard}")
    return found


def source_problems(text, comments):
    if ANY_GUARD_OPENING.match(text, len(comments)) and FINAL_ENDIF.search(text):
        return ["has an include guard, which only a header needs"]
    return []


def problems(path):
    text = path.read_text(encoding="utf-8")
    comments = text[: LEADING_COMMENTS.match(text).end()].rstrip()
    found = []
    if PRAGMA_ONCE.search(text):
        found.append("uses #pragma once")
    if Path(path.name.removesuffix(".in")).suffix in HEADER_SUFFIXES:
        found += header_problems(path, text, comments)
    else:
        found += source_problems(text, comments)
    return found


def main():
    status = 0
    for arg in sys.argv[1:]:
        for problem in problems(Path(arg)):
            sys.stdout.write(f"{arg}: {problem}\n")
            status = 1
    return status


if __name__ == "__main__":
    sys.exit(main())
