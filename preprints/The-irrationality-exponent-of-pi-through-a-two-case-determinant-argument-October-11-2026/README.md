# The irrationality exponent of pi through a two-case determinant argument

Ryan Matthew Casper · October 11, 2026 · package revision November 27, 2026

[Paper](paper.pdf) · [LaTeX source](build/main.tex) · [Lean companion](../../formalizations/PiTwoCaseBridge/README.md) · [Verification](VERIFY.md) · [Source correspondence](SOURCE-MAP.md) · [Attached Lean source ZIP](build/PiTwoCaseBridge-2026-11-26.zip)

This paper presents OpenAI's proof that $\mu(\pi)=2$ with an alternative interpolation argument. Sections 2–3 use one determinant to compare the arithmetic lower bound with the two analytic estimates. Sections 4–5 retain the original curve inequality and ordinary blow-up. Theorem 5.1 obtains jet interpolation from global generation, weighted arcs, and finite polynomial reduction. [OpenAI manuscript](https://github.com/openai/math/tree/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-irrationality-exponent-of-pi-is-2-September-24-2026)

The Lean companion proves Theorem 5.1 and uses it in the proof of $\mu(\pi)=2$. The verification record identifies the shared proof export accepted by stock Lean and Nanoda, and the source map connects the paper's argument to the companion declarations. [Verification](VERIFY.md) · [Source map](SOURCE-MAP.md)

The last page of the PDF also carries the Lean source ZIP. See the [replay instructions](../../verification/isolated-pi-two-case/REPLAY.md) for the toolchain and checker commands.

From this preprint directory, rebuild the PDF with Tectonic 0.17.0.

~~~powershell
./scripts/build-paper.ps1 -Tectonic /path/to/tectonic.exe
~~~

Tectonic can download TeX resources on a first build. The PDF timestamp can vary between builds. [Build output](paper.pdf)

Original prose is licensed under [CC BY 4.0](licenses/CC-BY-4.0.txt). [License scope and attribution](LICENSES.md)
