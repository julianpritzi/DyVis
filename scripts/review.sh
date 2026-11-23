#!/usr/bin/env bash
# Serve the viewer for reviewing diagrams one by one: accepting them from the
# picture, and opening the code an event is emitted by.
#   scripts/review.sh [port]
# Runs over DYVIS_DATA (default: this package's `diagrams/`); see
# viewer/tests/data.mjs.
set -euo pipefail

root=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
source "$root/scripts/node.sh"

exec "$DYVIS_NODE" "$root/viewer/tests/server.mjs" "$@"
