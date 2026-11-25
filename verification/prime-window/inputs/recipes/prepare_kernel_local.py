"""Prepare two shell-independent versions of the pinned kernel assembly proofs.

Usage: python prepare_kernel_local.py UPSTREAM_CHECKOUT PRIVATE_BUILD_DIRECTORY
The original declarations remain in the upstream checkout. Only the hypotheses
and the single call to its chamber table change in these proofs.
"""
from argparse import ArgumentParser
from pathlib import Path
from subprocess import check_output


PIN = "a0e8ac417cddc6ffa88e43cfd68d2b58ea339517"
DIRECTORY = "Zeta2FourTrajectoryMatrices/ArithmeticNormalization"
SHELL = "(hs : p < 8 * N ∧ p.Prime ∧ 50 * N < p ^ 2 ∧ InShell N r p)"
NUMERIC = "(hp8 : p < 8 * N) (hp2 : 50 * N < p ^ 2)"
ORIGINAL_TABLE = "Zeta2ANChamber.chamber_table_core N r p hN hr hs k k0 hk hk0 ht hχ0"


def replace_once(text, old, new):
    if text.count(old) != 1:
        raise ValueError(f"Expected one occurrence of {old!r}")
    return text.replace(old, new)


def adapt(repo, suffix, original_name, new_name):
    path = f"{DIRECTORY}/arithmetic_normalization_kernel{suffix}.lean"
    source = check_output(["git", "-C", str(repo), "show", f"{PIN}:{path}"]).decode("utf-8")
    start = source.index(f"theorem {original_name} ")
    end = source.index("\nend Zeta2ANKernel", start)
    decl = source[start:end].strip()
    decl = replace_once(decl, f"{original_name} (N r p : ℕ)", f"{new_name} (N p : ℕ)")
    decl = replace_once(decl, "(hN : 1 ≤ N) (hr : r < 3)\n    " + SHELL,
                        NUMERIC + "\n    (uniform : PrimeNumerator.KernelChamber.Uniform N p)")
    decl = replace_once(decl, ORIGINAL_TABLE, "uniform k k0 hk hk0 ht hχ0")
    if original_name == "kernel_residue_core":
        decl = replace_once(decl, "CJloc N p hs.1 hs.2.2.1", "CJloc N p hp8 hp2")
    return decl


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("upstream", type=Path)
    parser.add_argument("build_dir", type=Path)
    args = parser.parse_args()
    residue = adapt(args.upstream, 2, "kernel_residue_core", "residue_of_uniform")
    evaluation = adapt(args.upstream, 3, "R_pt_core", "evaluation_of_uniform")
    header = """-- Generated from the pinned Leibtag et al. proofs by prepare_kernel_local.py.
import Zeta2FourTrajectoryMatrices.ArithmeticNormalization.arithmetic_normalization_kernel3
import KernelChamber

open Polynomial Finset Zeta2Blueprint Zeta2NextTwo Zeta2ANKernel

noncomputable section
namespace PrimeNumerator.KernelLocal
"""
    footer = """
#print axioms residue_of_uniform
#print axioms evaluation_of_uniform
end PrimeNumerator.KernelLocal
"""
    out = args.build_dir / "KernelLocal.lean"
    out.write_text("\n\n".join((header.rstrip(), residue, evaluation, footer.strip())) + "\n",
                   encoding="utf-8", newline="\n")


if __name__ == "__main__":
    main()
