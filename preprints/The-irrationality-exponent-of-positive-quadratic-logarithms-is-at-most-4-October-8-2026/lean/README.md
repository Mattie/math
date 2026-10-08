# Quadratic logarithm formalization

`AlgebraicLog/Main.lean` proves the bound for arbitrary positive real quadratic algebraic inputs other than one. `Examples.lean` proves both sample instances. `AxiomAudit.lean` prints the final statements and axiom closures.

With Lean 4.34.1, Lake, Git, and Python 3.11 or later available, run `bash verify.sh`. This fetches and builds the pinned dependency project when `LEAN_DEPENDENCY_ROOT` is unset. Set that variable to an already built matching project to reuse its dependencies. Outputs go to the package's ignored `.verification/` directory.

See [verification](../VERIFY.md) and [dependency pin](../evidence/dependency-pin.json).
