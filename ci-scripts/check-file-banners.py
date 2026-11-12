#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 the smt-switch authors
# SPDX-FileContributor: Áron Ricardo Perez-Lopez
# SPDX-License-Identifier: BSD-3-Clause

"""Check that each file given opens with the one banner format.

The banner is a Doxygen comment on the first line: \\file naming the file
(a configured name.h.in as the name.h it becomes), a \\brief of at most
two lines, the second lined up under its first word, written as one simple
phrase with no full stop anywhere, one \\author
line per author, the \\date of the year the file was created and the
\\copyright line, then optionally a blank comment line and a longer
explanation in full sentences, each of its paragraphs ending with a full
stop. The code follows on the next line, with no blank line between.
"""

import re
import sys
from pathlib import Path

COPYRIGHT = "See the LICENSE file in the top-level source directory."
# A line of a brief, which is one simple phrase: a dot only inside a word,
# as in a file name, so that no full stop ends it or splits it into
# sentences, and no semicolon, colon or dash joining two parts
PHRASE = r"(?![^\n]*(?: -- |: ))\S(?:[^.;\n]|\.(?=\S))*"


def banner_pattern(name):
    return re.compile(
        r"/\*!\n"
        rf" \* \\file {re.escape(name)}\n"
        rf" \* \\brief {PHRASE}\n(?: \*        {PHRASE}\n)?"
        r"(?: \* \\author \S[^\n]*\n)+"
        r" \* \\date \d{4}\n"
        rf" \* \\copyright {re.escape(COPYRIGHT)}\n"
        r"(?: \*\n(?P<description>(?: \*(?: [^\n]*)?\n)*?))?"
        r" \*/\n"
        r"(?=[^\n])"
    )


def main():
    status = 0
    for arg in sys.argv[1:]:
        path = Path(arg)
        name = path.name.removesuffix(".in")
        text = path.read_text(encoding="utf-8")
        match = banner_pattern(name).match(text)
        if not match:
            sys.stdout.write(
                f"{arg}: does not open with the file banner, or a blank line "
                "follows it; see ci-scripts/check-file-banners.py\n"
            )
            status = 1
            continue
        paragraphs = re.split(
            r"^ \*\n", match.group("description") or "", flags=re.MULTILINE
        )
        if any(p and not p.rstrip().endswith(".") for p in paragraphs):
            sys.stdout.write(
                f"{arg}: a paragraph of the file description does not end with "
                "a full stop\n"
            )
            status = 1
    return status


if __name__ == "__main__":
    sys.exit(main())
