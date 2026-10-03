# Fjordmind Labs — mathematics

Research artifacts from [Fjordmind Labs](https://github.com/fjordmindlabs) on
AI-assisted mathematics: kernel-checked Lean 4 certificates, the generators
and verifiers that produce them, and the accompanying writeups. Everything
here is machine-checked where it can be, and says plainly where it cannot.

| Project | What it is | Status |
|---|---|---|
| [`erdos647-sparse/`](erdos647-sparse/) | Erdős Problem 647 has no solution in (24, 10¹³], kernel-checked in Lean 4.30.0 / Mathlib with axioms exactly `{propext, Classical.choice, Quot.sound}`. 10,000× the previous kernel-checked range (decanus, 10⁹) in a smaller certificate, via modular rungs proved inside the kernel and a sparse witness walk. | Verified on one machine, 2026-10-03; axiom gate passes. |

The Lean proofs and generator pipelines in this repository were produced by an
AI agent working under human direction; the mathematical claims are exactly
what the Lean kernel checks and nothing more.

License: Apache-2.0 (see [LICENSE](LICENSE)). Contact: Eero Tölö, Fjordmind Labs — labs@fjordmind.no.
