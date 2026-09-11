#!/usr/bin/env bash
set -euo pipefail
python -m venv .uploadenv
# shellcheck source=/dev/null  # activate script created by the command above
source .uploadenv/bin/activate
pip install twine
twine upload --skip-existing wheelhouse/*.whl
