# Dependency graph

Arrows record the arXiv v1 paper argument, not Lean proof dependencies. Dashed edges into green nodes use a separate formal route, explained in the section table. Dashed edges into unproved remarks indicate motivation. Green status applies to the formal scope stated in the table. The uniform theorem covers every k >= 16; Lean closes the needed scale k = 4980737 directly. The positive range is a separate branch.

```mermaid
%%{init: {"flowchart": {"nodeSpacing": 16, "rankSpacing": 22, "padding": 8}, "themeVariables": {"fontSize": "14px"}}}%%
flowchart LR
  subgraph Results[Numbered results]
    direction TB
  n0["Non-SOS at large orders<br/>thm:negative"]:::s0
  n9 -.-> n0
  n28 -.-> n0
  n1["Complete wedge Gram characterization<br/>lem:frame"]:::s2
  n2["Literal corner stabilization<br/>lem:corner"]:::s2
  n1 --> n2
  n3["Depth-two Gram example<br/>ex:gram-m2"]:::s2
  n4["Baseline corner Gram<br/>lem:corner-gram"]:::s2
  n2 --> n4
  n5["Complete normal form<br/>lem:normal-form"]:::s2
  n1 --> n5
  n4 --> n5
  n6["Finite complex Gram test<br/>lem:finite-test"]:::s2
  n5 --> n6
  n7["Complex tests of a real SOS problem<br/>rem:complex-test"]:::s2
  n6 --> n7
  n8["Gram-invariant decomposition<br/>lem:finite-decomposition"]:::s2
  n5 --> n8
  n6 --> n8
  n9["Negative limiting test<br/>lem:negative-limit"]:::s2
  n8 --> n9
  n17 --> n9
  n24 --> n9
  n21 --> n9
  n10["Symmetry splitting<br/>lem:positive-split"]:::s2
  n11["Symmetric/skew pair identity<br/>lem:positive-mixed"]:::s2
  n12["Same-symmetry Toeplitz pairs<br/>prop:same-symmetry"]:::s2
  n29 --> n12
  n13["One symmetric or skew factor<br/>thm:one-sided"]:::s2
  n10 --> n13
  n11 --> n13
  n12 --> n13
  n14["Both factors with mixed symmetry<br/>unlabelled:sections/03_positive_subclasses.tex:remark:1"]:::s2
  n13 --> n14
  n15["Exact positive increments<br/>lem:finite-increments"]:::s1
  n16["SOS through order 50<br/>thm:finite-positive"]:::s1
  n15 --> n16
  n17["Qualitative finite-depth tail<br/>B:lem:tail"]:::s2
  n4 --> n17
  n18["Forced low mixed modes<br/>B:lem:means"]:::s2
  n5 --> n18
  n19["Conjugate-point improvement<br/>B:lem:conjugate"]:::s2
  n18 --> n19
  n17 --> n19
  n20["Qualitative continuation<br/>B:lem:continuation"]:::s2
  n21["Uniform Gram-dependent vanishing<br/>B:prop:R"]:::s2
  n19 --> n21
  n20 --> n21
  n22["Uniform finite tails<br/>B:lem:quant-tails"]:::s0
  n18 -.-> n22
  n23["Quantitative continuation<br/>B:lem:quant-continuation"]:::s2
  n22 --> n23
  n24["Exact limiting witness<br/>C:lem:witness"]:::s1
  n25["Numerical eigenvalue observation<br/>unlabelled:appendices/C_negative_witness.tex:remark:1"]:::s3
  n26["Alternative numerical test families<br/>C:rem:alternative-test-families"]:::s3
  n27["Uniform finite-scale obstruction<br/>thm:finite-scale"]:::s2
  n8 --> n27
  n22 --> n27
  n23 --> n27
  n24 --> n27
  n28["Explicit sufficient order<br/>prop:explicit-threshold"]:::s0
  n27 -.-> n28
  n2 -.-> n28
  n29["Positive window decomposition<br/>prop:positive-window-certificate"]:::s2
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
