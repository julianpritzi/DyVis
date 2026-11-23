-- A minimal execution config, built from DY alone.
--
-- DYVis must not depend on any protocol, and DY ships no ready-made config --- they
-- are all per-campaign. So the checks bring their own: three byte sub-functors and
-- three trace entry types, which is the least that exercises the library.
--
-- This file is NOT imported by `DYVis.lean`, and must not be. `#combine +toplevel`
-- registers global instances (`BytesFunctor`, `HasExecTrace`, …); a campaign that
-- picked this up alongside its own config would have two of each.
module

public import DY.Trace
public import DY.Bytes
public import DY.Actions.Network
public import DY.Actions.Random
public import DY.Actions.ProtocolEvent
public import DY.EquationalTheory.Literal
public import DY.EquationalTheory.Concat
import DY.Meta

open DY

namespace DYVis.Trace.Check

public section CheckBytes

#combine +toplevel into BytesFunctor, BytesLength, attackerKnowledge from
  Random,
  Literal,
  Concat,

end CheckBytes

/-- Two constructors, so `eventDecoder%` has something to tell apart. Declared
    after the byte algebra exists, since its fields are `Bytes`. -/
public inductive DemoEvent where
  /-- One party recorded that it sent something. -/
  | sentSomething (what : Bytes)
  /-- The other recorded that it accepted it. -/
  | acceptedSomething (what : Bytes)

public section CheckTrace

#combine +toplevel into
  ExecEntryT,
  baseAttackerKnowledge,
from
  Network,
  Random,
  ProtocolEvent DemoEvent,

end CheckTrace

end DYVis.Trace.Check
