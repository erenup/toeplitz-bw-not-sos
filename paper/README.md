# The arXiv v1 paper

This directory contains [arXiv:2610.08980v1](https://arxiv.org/abs/2610.08980v1),
submitted 6 October 2026, DOI [10.48550/arXiv.2610.08980](https://doi.org/10.48550/arXiv.2610.08980).
[main.pdf](main.pdf) is the published arXiv PDF, downloaded 8 October 2026.
The printed title-page date is 8 October 2026. Each source below is byte-identical
to its entry in the arXiv e-print; [00README.json](00README.json) is retained.
The [2 October working version](https://github.com/erenup/toeplitz-bw-not-sos/blob/v1.0/paper/main.pdf)
remains at tag v1.0.

## Provenance

E-print: `https://arxiv.org/src/2610.08980v1`.
SHA-256: `eed5b9c04bfa1c0e832288bee7550032d196b4ada5bc360e65fec00c72b41b01`.
PDF: `https://arxiv.org/pdf/2610.08980v1`.
Per-file SHA-256 digests:

| File | SHA-256 |
|---|---|
| `00README.json` | `d1f6b1a71c9accb812ec5121d1fff7910c025ca7bb201948bacdb40941bc14e5` |
| `appendices/A_wedge_gram.tex` | `336a4631224166de936f5648909a066f9a5e8467186c794d2cf36a226ab05941` |
| `appendices/B_quantitative.tex` | `8325dde7d424bac63f9f8e71455306f51f6acc823cbf8cf06a0e8e9957b57588` |
| `appendices/C_negative_witness.tex` | `f0494d087549ed533d1cdb27facaff17d8358191eadffd8850db2c398f58c1e2` |
| `appendices/D_explicit_bound.tex` | `d82a51f26fa0b839d96a10afdabf03589a6670c91f9104f55ea101b342c24ac5` |
| `appendices/E_positive_certificates.tex` | `b75ec0cc847e1e17baa7ae90506b0a235e04eb3f9569aad115d66c1edc4f7065` |
| `appendices/F_finite_certificates.tex` | `46743e25ddac68a8989e114806437edbcb235d6ac6235087890fd67810eabf83` |
| `main.pdf` | `aa474f031feb4e2e002611db9c4f18625e13b471cf059090970a7785492bdff4` |
| `main.tex` | `2938813d3720bf0bc46db6f69260fad555be66a0522819fabd361689d7d3882e` |
| `references.bib` | `0b108ad0d519b0b5de8d6b0b156a6ac54e063a3e37729063e9d6648df8fb76a3` |
| `sections/01_introduction.tex` | `4663c363202cd06023f3401085e8f21289c91008c081afe8e2faf5d7fd362e03` |
| `sections/02_non_sos.tex` | `6cfffb7ec555dd50a1d9bb8fdcb00a01b3fee703c6503160bfba5c34151a16b8` |
| `sections/03_positive_subclasses.tex` | `a30c6bbc009ef5258e6f064df228055b1b060c4196b605c6b1ee4c8027d1fbba` |
| `sections/04_exact_certificates.tex` | `878c90de1ea4f242963a50ac765030b925465cc4d4c22d5bd2e2c65764b02f7c` |
| `sections/05_conclusion.tex` | `b87fabcffc6e847ec38b9223290334df530f74d082f9a8927c5bb128e1f92bd8` |

## Build

From the repository root, run `bash paper/build.sh`.
Expected last line: `PASS: paper built (.build/main.pdf)`.
It builds with `pdflatex` (the compiler in `00README.json`) and BibTeX through
`latexmk`, into the ignored `paper/.build/` directory. It preserves the
published `main.pdf`. No network access or external figures are needed.
The arXiv compilation used TeX Live 2025; local TeX distributions can produce
different fonts, layout or PDF metadata. The 29-page local build was checked
against all 29 numbered theorems, propositions, lemmas and remarks, as well
as Example 2.1, in the published 29-page PDF.

The source uses `\date{\today}`. The build script fixes the source clock to
8 October 2026 so repeated local builds print the same date; an ordinary
unconfigured compilation prints its compilation date. Local compilation omits
the arXiv stamp and arXiv's PDF processing and metadata, so a locally built PDF
is not expected to match the published PDF's bytes. Never replace the published
PDF with the local build. The numbering checker labels the two unlabelled
remarks only in a temporary source copy, then checks their compiled numbers.

Required TeX packages (including the source's conditional packages):
`geometry`, `inputenc`, `amsmath`, `amsthm`, `amssymb`, `mathrsfs`, `natbib`,
`graphicx`, `listings`, `caption`, `tikz`, `array`, `makecell`, `sidecap`,
`subcaption`, `xcolor`, `color`, `enumitem`, `comment`, `algorithm2e`,
`algpseudocode`, `bbm`, `tcolorbox`, `tabularray`, `diagbox`, `csquotes`,
`xurl`, `hyperref`, and `cleveref`, with the standard `article` class and
`plainnat` bibliography style. The source loads `algorithm2e`, `algpseudocode`,
and `bbm` only when they are available. Also install `latexmk`, BibTeX and
POSIX `grep`. A clean build takes about 3 seconds and under 100 MiB of memory;
installation time depends on the operating system.

The [result map](../paper-lean-mapping/README.md) uses the arXiv v1 numbers and
states where the frozen formal proof uses a different argument or has narrower
scope. The exact [witness checker](../verification/witness.py) reads the threshold
macro from the unchanged `main.tex`.

## License

All contents of `paper/` are licensed under
[CC BY-SA 4.0](https://creativecommons.org/licenses/by-sa/4.0/), matching the
arXiv v1 license. This replaces the v1.0 all-rights-reserved statement.
See [LICENSE](LICENSE). Everything outside `paper/` remains under MIT.
