"""Integer-only cross-check of the finite prime-window rate in the paper."""
from fractions import Fraction


def main():
    periods = 1_000_000
    scale = 10**18
    # Each tuple gives the endpoints u/v and w/z of an open base interval.
    windows = [(1, 8, 2, 13), (2, 9, 3, 13), (3, 10, 4, 13),
               (3, 8, 5, 13), (4, 9, 6, 13), (8, 9, 12, 13)]
    total = 0
    for u, v, w, z in windows:
        numerator = scale * (v*w - z*u)
        # Floor each positive term. Each remainder is less than one unit.
        total += sum(numerator // ((t*v + u) * (t*z + w))
                     for t in range(1, periods + 1))
    lower = Fraction(total, scale)
    upper = Fraction(total + periods*len(windows), scale)
    saving = Fraction(10_868_226, 100_000_000)
    arithmetic = Fraction(143_297_092_558_247_390_159, 13_110_552_000_000_000_000)
    height = Fraction(38_168_733, 1_000_000) + arithmetic
    gap = Fraction(62_636_575, 1_000_000)
    bound = gap / (gap - height + saving)
    assert lower > saving
    assert bound == Fraction(821_200_073_639_400_000_000, 178_914_706_731_744_129_841)
    assert bound < Fraction(4_589_897, 1_000_000)
    print(f"Finite sum of window widths lies in [{lower}, {upper}).")
    print(f"Certified saving exceeds {saving}.")
    print(f"Exponent at that saving: {bound} < 4589897/1000000.")


if __name__ == "__main__":
    main()
