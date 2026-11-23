# DYVis — named send, drawn read

## Overview

```mermaid
sequenceDiagram
  participant alice
  participant wire@{ "type" : "queue" }
  participant bob
  activate alice
    Note over alice: ▸ Random.genRand
    Note over alice: «1 entry»
  deactivate alice

  wire->>wire: ⟦1⟧ the value, on the wire
  activate bob
    wire->>bob: ⟦1⟧ the value, on the wire
    Note over bob: ▸ Network.receiveMessage
  deactivate bob

```

## Terms

The same run with the bytes shown.

```mermaid
sequenceDiagram
  participant alice
  participant wire@{ "type" : "queue" }
  participant bob
  activate alice
    Note over alice: ▸ Random.genRand
    Note over alice: «1 entry»
  deactivate alice

  wire->>wire: /- the value, on the wire -/<br/>⟦1⟧ rand:1
  activate bob
    wire->>bob: /- the value, on the wire -/<br/>⟦1⟧ rand:1
    Note over bob: ▸ Network.receiveMessage
  deactivate bob

```

## Legend

| | |
|---|---|
| `▸ Name` | a step; `Name` is the definition it calls |
| `/- … -/` | comment, maybe helpful for understanding the step |
| `· name` | an event the step logged, named by its constructor |
| `‹name›` | what the author called that value — declared, not derived |
| `⟦n⟧` | the trace handle of the message |
| `f:n(x)` | a constructor of the byte algebra `f`, and the term's instance number `n` |
| `concat:n[a, b]` | a concatenation, flattened |
| `concat:n[a, concat:k]` | `k` kept whole: it is also a message on the wire |
| `f:n`, `concat:n` | that same term again; its structure is printed once, earlier |
| `x ×n` | n adjacent copies of that same term |
| `?:n` | a term without formatting information |
| `…` | the depth limit cut here |
| `«n entries»` | omitted trace entries |
| `— REJECTED` | the driver returned `none`; the run stopped there |

