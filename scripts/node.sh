# Locate a JavaScript runtime. VS Code ships one, which is usually the only
# one on these machines. Sets DYVIS_NODE.
DYVIS_NODE=$(command -v node || command -v deno || command -v bun || true)
if [[ -z $DYVIS_NODE ]]; then
  DYVIS_NODE=$(ls -d "$HOME"/.vscode-server/bin/*/node 2>/dev/null | head -1 || true)
fi
if [[ -z $DYVIS_NODE ]]; then
  echo "no JavaScript runtime found (looked for node, deno, bun, and the one VS Code ships)" >&2
  exit 2
fi
