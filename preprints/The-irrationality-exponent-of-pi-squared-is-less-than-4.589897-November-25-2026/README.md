# The irrationality exponent of π² is less than 4.589897

[Read the paper](paper.pdf) · [LaTeX source](build/main.tex) · [Lean proof](lean/README.md) · [Download the proof](lean-proof.zip)

The paper proves that the irrationality exponent of π² is at most 821200073639400000000 / 178914706731744129841, strictly less than 4.589897. The bound applies to all rational approximations. The proof finds a further common divisor of the integer linear forms of Leibtag and coauthors by translating six prime intervals through a fixed million periods.

The [theorem map](theorem-map.json) identifies the Lean statements. See [verification and build instructions](VERIFY.md) for the proof replay, numerical check and PDF build, and [licenses and attribution](LICENSES.md) for the sources.

On November 25, GitHub Actions rebuilt the proof and verified all five Lean statements against an independent specification. [Hosted run](https://github.com/Mattie/math/actions/runs/45713249120/job/139552735865) · [Retained receipt and logs](verification/hosted-evidence.zip)
