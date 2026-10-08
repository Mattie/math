# License scope

Ryan Matthew Casper's five new `lean/Degree/` modules and original scripts
are covered by [MIT](LICENSE). The manuscript and
original explanatory prose are covered by [CC BY 4.0](licenses/CC-BY-4.0.txt).

Dependencies and retained third-party source keep their upstream terms:

- The fetched OpenAI π library, and its proof terms in the export, are covered
  by [Apache 2.0](licenses/OpenAI-Apache-2.0.txt).
- The fetched rational-logarithm extension is MIT licensed. Its public package
  supplies the applicable notices; the exact revision is recorded in the dependency pin.
- Lean and Mathlib retain their Apache 2.0 licenses. The
  [Lean license](licenses/Lean-Apache-2.0.txt) is retained with the replay materials.
- The retained `lean/reference-reader/Main.lean` is unchanged from Lean Kernel
  Arena at commit `b83254de5146ef34147ab82a48edbe1856b0edcc`, under
  [Apache 2.0](licenses/Lean-Kernel-Arena-Apache-2.0.txt).
- The retained `lean/reference-reader/parser/` files are from lean4export
  commit `076e8e57707e813375e8f9da8bf989799ace9680`, under
  [Apache 2.0](licenses/lean4export-Apache-2.0.txt). The reader's manifest pins
  that same parser.
- Nanoda is fetched separately, with its own upstream license; no Nanoda source
  or binary is redistributed in this package.

Compiled dependency caches and checker binaries are not included. The compressed
proof export includes the dependency closure, so these notices also accompany
that artifact. The MIT license grants rights only in our original contributions.
