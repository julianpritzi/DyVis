// Serves the viewer and the claims under DYVIS_DATA (see `data.mjs`), lets the
// viewer accept what it is showing, and opens the code behind an event.
//
// Reviewing means looking at a PICTURE, so the accept button belongs next to the
// picture rather than in a terminal beside it. Snapshots are recomputed per
// request, so editing `lower.js` or `graph.js` and reloading is enough -- no
// restart, and the button always accepts what is currently on screen.
//
// Serving with anything else still works; the viewer hides the button when
// `/review/status` is not there, and falls back to a `vscode://` link when
// `/review/open` is not.

import fs from "node:fs";
import path from "node:path";
import http from "node:http";
import { execFile } from "node:child_process";
import { viewerDir, claimsDir, rootDir } from "./data.mjs";

// Re-imported per request rather than held: an ES module is cached after its
// first import, so a running server would keep answering with the code it
// started with. It did once, and disagreed with the terminal about which
// diagrams had changed -- the one thing this must never do.
const lib = () => import(`./snapshot.mjs?t=${Date.now()}`);

const port = Number(process.argv[2] || 8730);

const TYPES = { ".html": "text/html", ".js": "text/javascript",
                ".json": "application/json", ".txt": "text/plain" };

const json = (res, code, body) => {
  res.writeHead(code, { "content-type": "application/json" });
  res.end(JSON.stringify(body));
};

// A Lean file under DYVIS_ROOT and the line a declaration is on, or null.
// Confined to DYVIS_ROOT and to `.lean`: the name comes off a claims file, and
// this end runs a program with it.
const locate = (rel, decl) => {
  const file = path.resolve(rootDir, rel);
  if (!file.startsWith(rootDir + path.sep) || !file.endsWith(".lean")
      || !fs.existsSync(file)) return null;
  const lines = fs.readFileSync(file, "utf8").split("\n");
  const parts = decl.split(".");
  const kw = "(?:def|theorem|abbrev|instance|structure|inductive|class)";
  // Longest suffix first: `Zone.signRrset` before `signRrset`, so a short name
  // that also occurs inside another namespace cannot win.
  let line = 0;
  for (let i = 0; i < parts.length && !line; i++) {
    const name = parts.slice(i).join(".").replace(/[.*+?^${}()|[\]\\]/g, "\\$&");
    const re = new RegExp(`^\\s*(?:@\\[[^\\]]*\\]\\s*)?(?:public\\s+|private\\s+|protected\\s+)*${kw}\\s+${name}\\b`);
    const at = lines.findIndex(l => re.test(l));
    if (at >= 0) line = at + 1;
  }
  return { file, line };
};

http.createServer(async (req, res) => {
  const url = new URL(req.url, `http://${req.headers.host}`);

  if (url.pathname === "/review/status") {
    try {
      const { computeSnapshots, review, writeCurrent } = await lib();
      const current = computeSnapshots();
      writeCurrent(current);
      const { state, gone } = review(current);
      return json(res, 200, { state, gone });
    } catch (e) { return json(res, 500, { error: e.message }); }
  }

  if (url.pathname === "/review/claims") {
    const files = (fs.existsSync(claimsDir) ? fs.readdirSync(claimsDir) : [])
      .filter(f => f.endsWith(".json")).sort();
    return json(res, 200, { files: files.map(f => `claims/${f}`) });
  }

  if (url.pathname === "/review/accept" && req.method === "POST") {
    const name = url.searchParams.get("name");
    try {
      const { computeSnapshots, review, accept } = await lib();
      const current = computeSnapshots();
      accept(name, current);
      const { state, gone } = review(current);
      return json(res, 200, { state, gone });
    } catch (e) { return json(res, 400, { error: e.message }); }
  }

  // Where a declaration is RIGHT NOW. The claim names the declaration, not a
  // line, so a claims file written before an edit still lands on the thing it
  // meant rather than confidently on whatever moved into its old line.
  if (url.pathname === "/review/locate" || url.pathname === "/review/open") {
    const found = locate(url.searchParams.get("file") || "", url.searchParams.get("decl") || "");
    if (!found) return json(res, 404, { error: "no such Lean file" });
    const { file, line } = found;
    // The URI is built HERE because only this end knows where the file really
    // is. Under WSL the editor runs on Windows against a remote host, so a
    // `vscode://file/home/...` path is a Windows path that does not exist; the
    // remote has to be named. Anything else that reaches its files through a
    // remote -- ssh, a container -- names itself in DYVIS_EDITOR_URI rather
    // than being guessed at, since a wrong guess fails silently.
    const at = `${file}${line ? `:${line}` : ""}`;
    const distro = process.env.WSL_DISTRO_NAME;
    const uri = process.env.DYVIS_EDITOR_URI
      ? process.env.DYVIS_EDITOR_URI.replace("{path}", file).replace("{line}", line || 1)
      : distro ? `vscode://vscode-remote/wsl+${distro}${at}`
               : `vscode://file${at}`;
    if (url.pathname === "/review/locate")
      return json(res, 200, { path: file, line, found: line > 0, uri });

    // Opening from HERE rather than handing a `vscode://` URI to the browser:
    // the browser may be on the other side of the remote boundary from the
    // editor and have no handler for the scheme at all, in which case it drops
    // the navigation silently. This end is where the files are, so the editor
    // is reachable from it by definition. Argument array, never a shell.
    return execFile("code", ["--goto", `${file}:${line || 1}:1`], err =>
      err ? json(res, 200, { ok: false, uri, why: err.code || String(err) })
          : json(res, 200, { ok: true }));
  }

  // Static: the viewer's own files, and `claims/` from the data directory.
  const rel = decodeURIComponent(url.pathname).replace(/^\/+/, "") || "viewer.html";
  const [base, sub] = rel.startsWith("claims/") ? [claimsDir, rel.slice(7)] : [viewerDir, rel];
  const file = path.resolve(base, sub);
  if (!file.startsWith(base + path.sep) ||!fs.existsSync(file) || fs.statSync(file).isDirectory()) {
    res.writeHead(404); return res.end("not found");
  }
  res.writeHead(200, { "content-type": TYPES[path.extname(file)] || "application/octet-stream",
                       "cache-control": "no-store" });
  res.end(fs.readFileSync(file));
}).listen(port, "127.0.0.1", () => {
  console.log(`review at http://127.0.0.1:${port}/viewer.html`);
});
