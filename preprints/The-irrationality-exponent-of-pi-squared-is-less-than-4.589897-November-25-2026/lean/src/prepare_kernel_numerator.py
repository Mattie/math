"""Reconstruct KernelNumerator.lean from the pinned proofs of Leibtag et al.

Usage: python prepare_kernel_numerator.py UPSTREAM_CHECKOUT BUILD_DIRECTORY
Requires Python 3.8+ and Git. Line numbers below refer to immutable Git blobs.
"""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess


def source_span(lines, first, last):
    """Return an inclusive range of one-based source lines, without its final LF."""
    return "\n".join(lines[first - 1:last])


def assemble(sprime, jval, an):
    def s(first, last):
        return source_span(sprime, first, last)

    def j(first, last):
        return source_span(jval, first, last)

    def a(first, last):
        return source_span(an, first, last)

    header = """import Zeta2FourTrajectoryMatrices.ArithmeticNormalization.arithmetic_normalization_sprime2
import Zeta2FourTrajectoryMatrices.ArithmeticNormalization.arithmetic_normalization_jval
import Zeta2FourTrajectoryMatrices.ArithmeticNormalization.arithmetic_normalization
import Bounds

open Polynomial Finset Zeta2Blueprint Zeta2FirstThree Zeta2NextTwo Zeta2ANSprime Zeta2ANJval Zeta2ArithmeticNormalization
noncomputable section
namespace PrimeNumerator.KernelNumerator"""
    kernel = "\n".join([
        s(194, 194).replace("kernel_divided_core", "kernel_divided_translated"),
        "    (hpn : p < N) (hp2 : 50 * N < p ^ 2) (Q : (ZMod p)[X])",
        s(196, 214),
        """  let K := (p - 1) / 3
  have hKi : 2 ≤ K ∧ 13 * N + r < p * K ∧ 3 * K + 1 ≤ p :=
    PrimeNumerator.Bounds.interpolation hpn hp2 hr
  obtain ⟨hK2, hK1, hK3⟩ := hKi""",
        s(217, 281),
    ])
    newton = "\n".join([
        j(164, 164).replace("J_val_core", "J_val_translated"),
        "    (hp2 : 50 * N < p ^ 2) (h A : ℕ)",
        j(166, 212).replace("rw [zsum_zero", "rw [Zeta2ANJval.zsum_zero"),
    ])
    low_sums = """    (hfull : ∑ k ∈ range p, (k : ZMod p) ^ r * Q.eval (k : ZMod p) = 0)
    (hpartial : ∑ k ∈ range (11 * N % p + 1), (k : ZMod p) ^ r * Q.eval (k : ZMod p) = 0)"""
    shift = "(A0 * p)"
    harmonic_sum = "\n".join([
        "theorem harmonic_sum_translated (N r p : ℕ) [Fact p.Prime] (Q : (ZMod p)[X])",
        low_sums,
        a(410, 412).replace("(Qpoly N p).eval", "Q.eval"),
        "    (A0 : ℕ) :",
        a(414, 429).replace("etaP N p", shift).replace("(Qpoly N p).eval", "Q.eval")
                   .replace(", hA0,\n      Nat.add_mul", ", Nat.add_mul"),
        a(430, 430).replace("(Qsum_range N r p hN hr hs) (Q_partial N r p hN hr hs)",
                            "hfull hpartial"),
    ])
    harmonic_val = "\n".join([
        """theorem harmonic_val_translated (N r p : ℕ) [Fact p.Prime] (hp2 : 50 * N < p ^ 2)
    (A0 : ℕ) (hlimit : 11 * N + A0 * p < p ^ 2) (Q : (ZMod p)[X])""",
        low_sums,
        s(196, 196),
        a(411, 412).replace("(Qpoly N p).eval", "Q.eval") + " :",
        a(440, 442).replace("etaP N p", shift),
        "  obtain ⟨κ, Acoef, hA⟩ := hC",
        a(451, 464).replace("etaP N p", shift),
        "  rw [harmonic_sum_translated N r p Q hfull hpartial κ Acoef hA A0] at hred",
        a(466, 469),
    ])
    split = "\n".join([
        """theorem lcm_GN_split_translated (N p : ℕ) [Fact p.Prime] (hpn : p < N)
    (hp2 : 50 * N < p ^ 2) :""",
        a(106, 107).replace("13 * N + r", "13 * N + 0"),
        a(442, 442),
        a(109, 114).replace("13 * N + r", "13 * N + 0"),
    ])
    # Extract the inner single-prime argument from arithmetic_normalization.
    def inner(first, last):
        return "\n".join(line[2:] for line in an[first - 1:last])

    divides = "\n".join([
        """theorem column_zero_divides_translated (N p A0 : ℕ) [Fact p.Prime] (_hN : 1 ≤ N)
    (hpn : p < N) (hp2 : 50 * N < p ^ 2)
    (hη₁ : 2 * N ≤ A0 * p) (hη₂ : A0 * p ≤ 9 * N)
    (hH : pInt p (hexp N p + 1) ((p : ℚ) ^ 2 *
      ∑ j ∈ range (11 * N + 1), (j : ℚ) ^ (0 : ℕ) * cj N j * harm2 (j + A0 * p)))
    (hJ : pInt p (hexp N p + 1) ((p : ℚ) ^ 2 * Jfun (A0 * p) (Spoly N 0)))
    (z : Fin 2 → ℤ) (hz : ∀ i, ((CN N * lcmUpTo (12 * N) * lcmUpTo (13 * N + (0 : Fin 3)) : ℕ) / (GN N : ℕ) : ℚ) * readout N i 0 = z i)
    (i : Fin 2) : (p : ℤ) ∣ z i := by""",
        a(442, 442),
        inner(512, 512).replace("N r (etaP N p)", "N (0 : Fin 3) (A0 * p)"),
        a(501, 502).replace("fun p hp", "fun q hq").replace("mem_Sset hp", "mem_Sset hq"),
        inner(514, 518).replace("readout N i r", "readout N i 0"),
        "      exact pInt_add pp (hH) (hJ)",
        inner(520, 534).replace("(r : ℕ)", "((0 : ℕ))"),
        inner(535, 535).replace("G, hU,", "G, _,")
                       .replace("lcm_GN_split N r p hN r.2 hs", "lcm_GN_split_translated N p hpn hp2"),
        inner(536, 538).replace("readout N i r", "readout N i 0").replace("13 * N + r", "13 * N + 0"),
        "    simp only [Fin.val_zero, Nat.add_zero] at hz ⊢",
        inner(539, 560),
    ])
    footer = """#print axioms lcm_GN_split_translated
#print axioms column_zero_divides_translated
#print axioms harmonic_sum_translated
#print axioms harmonic_val_translated
#print axioms kernel_divided_translated
#print axioms J_val_translated
end PrimeNumerator.KernelNumerator

"""
    return (header + "\n\n" + "\n\n\n".join([kernel, newton, harmonic_sum, harmonic_val, split])
            + "\n\n" + divides + "\n\n" + footer).encode("utf-8")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("upstream", type=Path)
    parser.add_argument("build_dir", type=Path)
    args = parser.parse_args()
    manifest = json.loads(Path(__file__).with_name("kernel_provenance.json").read_text(encoding="utf-8"))
    pin = manifest["commit"]
    sources = {}
    for key, item in manifest["numerator_inputs"].items():
        data = subprocess.check_output(["git", "-C", str(args.upstream), "show", f"{pin}:{item['path']}"])
        if hashlib.sha256(data).hexdigest() != item["sha256"]:
            raise SystemExit(f"Unexpected upstream bytes for {item['path']}")
        sources[key] = data.decode("utf-8").splitlines()
    result = assemble(**sources)
    if hashlib.sha256(result).hexdigest() != manifest["outputs"]["KernelNumerator.lean"]["lf_sha256"]:
        raise SystemExit("Reconstructed KernelNumerator.lean failed its SHA-256 check")
    args.build_dir.mkdir(parents=True, exist_ok=True)
    target = args.build_dir / "KernelNumerator.lean"
    if target.exists() and target.read_bytes().replace(b"\r\n", b"\n") != result:
        raise SystemExit(f"Refusing to replace a different file at {target}")
    target.write_bytes(result)


if __name__ == "__main__":
    main()
