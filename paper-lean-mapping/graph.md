# Dependency graph

Arrows record the arXiv v1 paper argument, not Lean proof dependencies. Dashed edges into green nodes use a separate formal route, explained in the section table. Dashed edges into unproved remarks indicate motivation. Green status applies to the formal scope stated in the table. The uniform theorem covers every k >= 16; Lean closes the needed scale k = 4980737 directly. The positive range is a separate branch.

```mermaid
%%{init: {"flowchart": {"nodeSpacing": 16, "rankSpacing": 22, "padding": 8}, "themeVariables": {"fontSize": "14px"}}}%%
flowchart LR
  subgraph Results[Numbered results]
    direction TB
  n0["Theorem 2.1<br/>Non-SOS at large orders"]:::s0
  n9 -.-> n0
  n28 -.-> n0
  n1["Lemma 2.1<br/>Complete wedge Gram characterization"]:::s2
  n2["Lemma 2.2<br/>Literal corner stabilization"]:::s2
  n1 --> n2
  n3["Example 2.1<br/>Depth-two Gram example"]:::s2
  n4["Lemma 2.3<br/>Baseline corner Gram"]:::s2
  n2 --> n4
  n5["Lemma 2.4<br/>Complete normal form"]:::s2
  n1 --> n5
  n4 --> n5
  n6["Lemma 2.5<br/>Finite complex Gram test"]:::s2
  n5 --> n6
  n7["Remark 2.1<br/>Complex tests of a real SOS problem"]:::s2
  n6 --> n7
  n8["Lemma 2.6<br/>Gram-invariant decomposition"]:::s2
  n5 --> n8
  n6 --> n8
  n9["Proposition 2.1<br/>Negative limiting test"]:::s2
  n8 --> n9
  n17 --> n9
  n24 --> n9
  n21 --> n9
  n10["Lemma 3.1<br/>Symmetry splitting"]:::s2
  n11["Lemma 3.2<br/>Symmetric/skew pair identity"]:::s2
  n12["Proposition 3.1<br/>Same-symmetry Toeplitz pairs"]:::s2
  n29 --> n12
  n13["Theorem 3.1<br/>One symmetric or skew factor"]:::s2
  n10 --> n13
  n11 --> n13
  n12 --> n13
  n14["Remark 3.1<br/>Both factors with mixed symmetry"]:::s2
  n13 --> n14
  n15["Lemma 4.1<br/>Exact positive increments"]:::s1
  n16["Theorem 4.1<br/>SOS through order 50"]:::s1
  n15 --> n16
  n17["Lemma B.1<br/>Qualitative finite-depth tail"]:::s2
  n4 --> n17
  n18["Lemma B.2<br/>Forced low mixed modes"]:::s2
  n5 --> n18
  n19["Lemma B.3<br/>Conjugate-point improvement"]:::s2
  n18 --> n19
  n17 --> n19
  n20["Lemma B.4<br/>Qualitative continuation"]:::s2
  n21["Proposition B.1<br/>Uniform Gram-dependent vanishing"]:::s2
  n19 --> n21
  n20 --> n21
  n22["Lemma B.5<br/>Uniform finite tails"]:::s0
  n18 -.-> n22
  n23["Lemma B.6<br/>Quantitative continuation"]:::s2
  n22 --> n23
  n24["Lemma C.1<br/>Exact limiting witness"]:::s1
  n25["Remark C.1<br/>Numerical eigenvalue observation"]:::s3
  n26["Remark C.2<br/>Alternative numerical test families"]:::s3
  n27["Theorem D.1<br/>Uniform finite-scale obstruction"]:::s2
  n8 --> n27
  n22 --> n27
  n23 --> n27
  n24 --> n27
  n28["Proposition D.1<br/>Explicit sufficient order"]:::s0
  n27 -.-> n28
  n2 -.-> n28
  n29["Proposition E.1<br/>Positive window decomposition"]:::s2
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

“Proved in the paper only” includes full statements with formal ingredients of narrower scope. Purple remarks are numerical observations. A definition is not a proof.
