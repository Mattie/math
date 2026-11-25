"""Generate a Lean v4.35.0-rc4 proof slice from the Apache-2.0 PNT+ sources."""

import argparse
from hashlib import sha256
from pathlib import Path
import re
from urllib.request import urlopen


PIN = "127b50e33f6033e2147921167a117af96d9ba4ea"
ROOT = "PrimeNumberTheoremAnd/"
DIGESTS = {
    "LICENSE": "c71d239df91726fc519c6eb72d318ec65820627232b2f796219e87dcf35d0ab4",
    ROOT + "Fourier.lean": "44d2c28b251be0296f897e43a75a055f346a6199849b54ab204240fe4099e6c2",
    ROOT + "SmoothExistence.lean": "e689045a2d7f92c71c68fda6aa69a89d4a8692187475ba432ed010f453110ea0",
    ROOT + "Sobolev.lean": "fe06e13fad5b47dbd324307ba246110515c4cb50f4c41d6cb15764fd53b1b8ef",
    ROOT + "Wiener.lean": "7bd40c9cffedc1d9a0f675ea971c6719e490b1b106807459d549145f30d70f05",
    ROOT + "Mathlib/Algebra/Notation/Support.lean": "e688bf925c2130b291c536d3b93b72c20e41ae95d530c90915921d75a6f52504",
    ROOT + "Mathlib/Analysis/Asymptotics/Asymptotics.lean": "c1cdb6bb509c6178bf17868c57e5b53721b87fb2774ef8562bc5945ffe5b11ae",
    ROOT + "Consequences.lean": "7b9146a398d01aac583ce4ebfa6d62036f1a3de2d53b9dad827d34f1414d9611",
}


def source_bytes(name, cache):
    path = cache / name
    if path.is_file():
        data = path.read_bytes()
    else:
        url = f"https://raw.githubusercontent.com/AlexKontorovich/PrimeNumberTheoremAnd/{PIN}/{name}"
        with urlopen(url, timeout=60) as response:
            data = response.read()
    if sha256(data).hexdigest() != DIGESTS[name]:
        raise ValueError(f"PNT+ source hash mismatch for {name}")
    if not path.is_file():
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(data)
    return data


def before_after(text, start, end):
    first = text.index(start)
    return text[:first] + text[text.index(end, first):]


def slice_between(text, start, end):
    first = text.index(start)
    return text[first:text.index(end, first + len(start))]


def theta_module(text):
    # These are the Consequences lemmas on the dependency path to theta.
    s = "import PrimeNumberTheoremAnd.Wiener\n\n"
    s += slice_between(text, "open ArithmeticFunction hiding log", "lemma Set.Ico")
    s += "open scoped Topology\n\n"
    s += slice_between(text, "theorem Asymptotics.IsEquivalent.add_isLittleO''",
                       "/-- `(⌊x⌋₊ + 1)")
    s += slice_between(text, "theorem chebyshev_asymptotic :", "theorem chebyshev_asymptotic_finsum")
    s = s.replace(slice_between(s, "  have := Real.tendsto_pow_log_div_pow_atTop", "/--"),
                  "  exact Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp "
                  "tendsto_natCast_atTop_atTop\n\n")
    return s + """namespace PrimeNumeratorPNT

theorem prime_number_theorem : Tendsto (fun x : ℝ => Chebyshev.theta x / x) atTop (𝓝 1) :=
  (isEquivalent_iff_tendsto_one (by exact eventually_ne_atTop (0 : ℝ))).mp chebyshev_asymptotic

end PrimeNumeratorPNT
"""


def generate(output, cache):
    for name in DIGESTS:
        data = source_bytes(name, cache)
        if name == "LICENSE":
            (output / "PNT-PLUS-LICENSE").write_bytes(data)
            continue
        text = data.decode("utf-8")
        filename = name
        if name.endswith("/Consequences.lean"):
            text = theta_module(text)
            filename = "PrimeNumeratorPNT.lean"
        if name.endswith("/Wiener.lean"):
            text = text[:text.index("section auto_cheby")]
            # Omit two unused, admitted bounded-variation lemmas and their sole consumer.
            text = before_after(text, '@[blueprint "prelim-decay-2"', "lemma decay_bounds_key")
        # Architect only supplies the blueprint prose commands in this slice.
        text = text.replace("import Architect\n", "")
        text = re.sub(r"blueprint_comment /--.*?-/", "", text, flags=re.S)
        text = re.sub(r"^@\[blueprint\b.*?\)\]\s*\n", "", text, flags=re.S | re.M)
        if re.search(r"\b(sorry|admit|axiom|blueprint)\b", text):
            raise ValueError(f"Unexpected admission or blueprint in {name}")
        notice = (f"-- Source: PNT+, {PIN}, {name}. Apache-2.0.\n"
                  "-- Prepared for the pinned prime-numerator replay; see prepare_pnt.py for changes.\n")
        path = output / filename
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes((notice + text).encode("utf-8"))


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("output", type=Path)
    parser.add_argument("--cache", type=Path, help="Pinned original source files for offline reuse")
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=True)
    generate(args.output, args.cache or args.output / "pnt-plus-originals")
