# The manuscript

The paper is a **working version dated 2 October 2026** and is being finalized
by the authors. The final version will be posted on arXiv and will replace
`paper/`. The theorem and equation numbers in `paper-lean-mapping/` refer
to this working version.

Read [main.pdf](main.pdf) or follow the [result map](../paper-lean-mapping/README.md).
The sources include the complete finite analytic proof, positive certificate
argument, exchange criterion, boundary consequence, and open questions.

Build from the repository root:

```sh
bash paper/build.sh
```

Expected last line: `PASS: paper built (.build/main.pdf)`.
The script writes the PDF and intermediate files into the ignored `.build/`
directory. It leaves the tracked `main.pdf` unchanged. To replace that artifact,
run `bash paper/build.sh --update-pdf` explicitly; its last line is
`PASS: paper built and tracked PDF updated (main.pdf)`.
It requires TeX Live with AMS, the Palatino fonts (`mathpazo`), microtype,
mathtools, booktabs, geometry, hyperref and xurl, plus `latexmk`, BibTeX, and
POSIX `grep`. No plots, network access, or font downloads are needed. A fixed source
timestamp makes the PDF reproducible with the same TeX distribution.
Both commands take about 2–3 seconds for a clean build and use under 100 MiB
of resident memory; a cached run is faster. Installing TeX depends on the
operating system and package-cache availability.

Every numbered result and every equation or section label is covered by
[`mapping.json`](../paper-lean-mapping/mapping.json). Its tables distinguish
full Lean statements, proved ingredients with a different formal scope,
exact computations, written proofs, and unproved remarks. The printed verification
table lists only the exact programs included in this repository.

The [witness checker](../verification/witness.py) reads the threshold macro
from `main.tex`, reconstructs the full rational pairing, checks its independent
convolution, and rejects five corruptions in both Python modes. Full
reproduction commands are in the [root README](../README.md).

## Copyright

The paper sources and PDF are not licensed. All rights reserved.
