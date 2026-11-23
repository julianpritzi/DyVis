// Where the viewer's code is, and where the diagrams it is run over live.
//
// DYVIS_DATA names a directory holding `claims/` (written by
// `#traceClaimsToFile`), `accepted/` (approved snapshots) and `current/` (the
// latest snapshots, not to be committed). It defaults to this package's own
// `diagrams/`, the reference theorems of `DYVis/Theorem/Example.lean`.
//
// DYVIS_ROOT is the directory `lake build` runs in: the paths inside a claims
// file are relative to it. It defaults to the parent of the data directory.

import path from "node:path";
import { fileURLToPath } from "node:url";

export const viewerDir = path.resolve(path.dirname(fileURLToPath(import.meta.url)), "..");
export const dataDir = path.resolve(process.env.DYVIS_DATA || path.join(viewerDir, "..", "diagrams"));
export const claimsDir = path.join(dataDir, "claims");
export const acceptedDir = path.join(dataDir, "accepted");
export const currentDir = path.join(dataDir, "current");
export const rootDir = path.resolve(process.env.DYVIS_ROOT || path.dirname(dataDir));

/** A diagram's name: the theorem's, without the reference theorems' namespace. */
export const shortName = name => name.replace(/^DYVis\.Theorem\./, "");
