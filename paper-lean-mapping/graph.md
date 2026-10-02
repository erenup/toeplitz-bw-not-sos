# Dependency graph

Arrows record the paper argument, not Lean proof dependencies. Dashed edges into green nodes use a separate formal route, explained in the section table. Dashed edges into unproved remarks indicate motivation. Green status applies to the formal scope stated in the table. The uniform theorem covers every k >= 16; Lean closes the needed scale k = 4980737 directly. The positive range is a separate branch.

```mermaid
%%{init: {"flowchart": {"nodeSpacing": 16, "rankSpacing": 22, "padding": 8}, "themeVariables": {"fontSize": "14px"}}}%%
flowchart LR
  subgraph Results[Numbered results]
    direction TB
  n0["Non-SOS at large orders<br/>thm:negative"]:::s0
  n1 --> n0
  n1["Explicit threshold<br/>cor:threshold"]:::s0
  n9 -.-> n1
  n2["Quadratic frame<br/>lem:frame"]:::s2
  n3["Stabilized corner<br/>lem:corner"]:::s2
  n2 --> n3
  n4["Complete low means<br/>lem:means"]:::s2
  n3 --> n4
  n5["Global kernel bound<br/>lem:global"]:::s2
  n3 --> n5
  n6["Uniform finite tails<br/>lem:tails"]:::s0
  n4 -.-> n6
  n5 -.-> n6
  n7["Continuation estimate<br/>lem:continuation"]:::s2
  n6 --> n7
  n5 --> n7
  n8["Exact tangent witness<br/>lem:witness"]:::s0
  n9["Finite-scale obstruction<br/>thm:finite-scale"]:::s2
  n3 --> n9
  n6 --> n9
  n7 --> n9
  n8 --> n9
  n10["SOS through order 50<br/>prop:positive"]:::s1
  n11["Exchange criterion<br/>thm:exchange"]:::s2
  n2 --> n11
  n12["Budget criticality<br/>thm:criticality"]:::s2
  n11 --> n12
  n13["Boundary obstruction<br/>cor:boundary"]:::s2
  n1 --> n13
  n14["Moderate-order expectation<br/>rem:persistence"]:::s3
  n10 -.-> n14
  end
  subgraph Legend
    direction TB
    legend0["Lean-proved"]:::s0
    legend1["Exact-verified"]:::s1
    legend2["Proved in the paper only"]:::s2
    legend3["Unproved remark"]:::s3
    key0["Arrows: paper argument; not Lean proof dependencies"]
    key1["Dashed to green: separate Lean route (see table)"]
    key2["Green: Lean proves the formal scope in the table"]
    key3["All k >= 16: paper; k = 4980737: Lean application"]
    key4["Dashed to unproved remark: motivating evidence"]
    legend0 ~~~ legend1 ~~~ legend2 ~~~ legend3
  end
  Results ~~~ Legend
  style Results fill:#ffffff,stroke:#cbd5e1
  style Legend fill:#ffffff,stroke:#cbd5e1
  classDef s0 fill:#d1fae5,stroke:#475569,color:#0f172a
  classDef s1 fill:#dbeafe,stroke:#475569,color:#0f172a
  classDef s2 fill:#fef3c7,stroke:#475569,color:#0f172a
  classDef s3 fill:#ede9fe,stroke:#475569,color:#0f172a
```

“Proved in the paper only” records an analytic proof. A cited Lean proposition definition does not change that status.
