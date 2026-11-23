#!/usr/bin/env bash
# Approval tests for the theorem diagrams. See viewer/tests/snapshot.mjs.
#
#   scripts/snapshot.sh                 compare, report what changed
#   scripts/snapshot.sh --check         fail only if an APPROVED diagram
#                                       changed; ignores unreviewed ones
#   scripts/snapshot.sh --accept        accept everything that differs
#   scripts/snapshot.sh --accept a b    accept only these diagrams
#
# Runs over DYVIS_DATA (default: this package's `diagrams/`); see
# viewer/tests/data.mjs. To review the pictures rather than the text, use
# scripts/review.sh.
set -euo pipefail

root=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
source "$root/scripts/node.sh"

exec "$DYVIS_NODE" "$root/viewer/tests/snapshot.mjs" "$@"
