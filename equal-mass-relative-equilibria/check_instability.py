"""Verify strict trace bounds on the 28 published central-configuration boxes."""

from collections import Counter
from fractions import Fraction
from hashlib import sha256
from itertools import combinations
from math import ceil, floor, isqrt
import re
import sys
import tarfile


SCALE = 10**15
PADDING = SCALE // 10**6
REPORT_DIGEST = "f7d05ecd636c220dad2616b3041742a8dbd3f3c40a32f5111e84d2a3fece85a0"
BOX_COUNTS = {5: 5, 6: 9, 7: 14}
COORDINATE = re.compile(
    r"^i: (\d+) X: \[([^,]+), ([^\]]+)\] Y: \[([^,]+), ([^\]]+)\]", re.M
)


class Interval:
    """Closed interval with endpoints lo/SCALE and hi/SCALE."""

    __slots__ = ("lo", "hi")

    def __init__(self, lo, hi):
        if lo > hi:
            raise ValueError("Reversed interval endpoints")
        self.lo = lo
        self.hi = hi

    def __add__(self, other):
        return Interval(self.lo + other.lo, self.hi + other.hi)

    def __neg__(self):
        return Interval(-self.hi, -self.lo)

    def __sub__(self, other):
        return self + (-other)

    def __mul__(self, other):
        products = (
            self.lo * other.lo, self.lo * other.hi,
            self.hi * other.lo, self.hi * other.hi,
        )
        return Interval(min(products) // SCALE, -(-max(products) // SCALE))

    def sqrt(self):
        if self.lo < 0:
            raise ValueError("Square root requires a nonnegative interval")
        lo = isqrt(self.lo * SCALE)
        hi_squared = self.hi * SCALE
        hi = isqrt(hi_squared)
        return Interval(lo, hi + int(hi * hi < hi_squared))

    def inverse(self):
        if self.lo <= 0:
            raise ValueError("Reciprocal requires a positive interval")
        numerator = SCALE**2
        return Interval(numerator // self.hi, -(-numerator // self.lo))


def integer(value):
    return Interval(value * SCALE, value * SCALE)


ZERO = integer(0)
ONE = integer(1)
THREE = integer(3)


def coordinate_interval(lower, upper):
    lo, hi = Fraction(lower), Fraction(upper)
    if lo > hi:
        raise ValueError("Reversed source coordinate endpoints")
    return Interval(floor(lo * SCALE) - PADDING, ceil(hi * SCALE) + PADDING)


def read_boxes(archive):
    with tarfile.open(archive) as source:
        report = source.extractfile("reports.tex").read()
    if sha256(report).hexdigest() != REPORT_DIGEST:
        raise ValueError("reports.tex must match the pinned arXiv:1812.07279v3 input")
    reports = report.decode("utf-8")

    for n, expected_count in BOX_COUNTS.items():
        section = reports.split(f"Number of bodies = {n}\n", 1)[1]
        body = re.split(r"\\end\{[vV]erbatim\}", section, 1)[0]
        parts = re.split(r"^position (\d+)[ \t]*\n", body, flags=re.M)
        labels = parts[1::2]
        if len(labels) != expected_count or len(set(labels)) != expected_count:
            raise ValueError(f"Unexpected configuration labels for n={n}")
        boxes = []
        for label, part in zip(labels, parts[2::2]):
            rows = COORDINATE.findall(part)
            if [int(row[0]) for row in rows] != list(range(n)):
                raise ValueError(f"Unexpected coordinate rows for n={n}, position {label}")
            box = [
                (coordinate_interval(x0, x1), coordinate_interval(y0, y1))
                for _, x0, x1, y0, y1 in rows
            ]
            boxes.append((label, box))
        yield n, boxes


def product(left, right):
    dimension = len(left)
    result = [[ZERO] * dimension for _ in range(dimension)]
    for i, row in enumerate(left):
        for k, a in enumerate(row):
            if not (a.lo or a.hi):
                continue
            for j, b in enumerate(right[k]):
                if b.lo or b.hi:
                    result[i][j] = result[i][j] + a * b
    return result


def trace(matrix):
    return sum((row[i] for i, row in enumerate(matrix)), ZERO)


def jacobian(positions):
    n = len(positions)
    d = 2 * n
    matrix = [[ZERO] * (2 * d) for _ in range(2 * d)]
    for i in range(d):
        matrix[i][d + i] = ONE
        matrix[d + i][i] = ONE
    for i in range(0, d, 2):
        matrix[d + i][d + i + 1] = integer(2)
        matrix[d + i + 1][d + i] = integer(-2)

    for i, j in combinations(range(n), 2):
        delta = [positions[i][axis] - positions[j][axis] for axis in range(2)]
        radius_squared = delta[0] * delta[0] + delta[1] * delta[1]
        inverse_radius_squared = radius_squared.inverse()
        weight = (integer(n) * radius_squared * radius_squared.sqrt()).inverse()
        for a in range(2):
            for b in range(2):
                term = weight * (
                    THREE * delta[a] * delta[b] * inverse_radius_squared - integer(int(a == b))
                )
                for left, right, entry in ((i, i, term), (j, j, term), (i, j, -term), (j, i, -term)):
                    row, col = d + 2 * left + a, 2 * right + b
                    matrix[row][col] = matrix[row][col] + entry
    return matrix


def trace_test(matrix):
    squared = product(matrix, matrix)
    first = -trace(squared)
    if first.hi < 0:
        return 1, first.hi
    fourth = product(squared, squared)
    second = trace(fourth)
    if second.hi < 0:
        return 2, second.hi
    third = -sum(
        (entry * fourth[j][i] for i, row in enumerate(squared) for j, entry in enumerate(row)),
        ZERO,
    )
    return 3, third.hi


def main(archive):
    for n, boxes in read_boxes(archive):
        results = []
        for label, box in boxes:
            power, upper = trace_test(jacobian(box))
            if upper >= 0:
                raise SystemExit(f"No strict trace bound for n={n}, position {label}")
            print(f"n={n} position={label:>2} k={power} trace_upper={upper}/{SCALE}")
            results.append((power, upper))
        counts = Counter(power for power, _ in results)
        worst = max(upper for _, upper in results)
        print(f"n={n} verified={len(results)} counts_by_k={dict(sorted(counts.items()))} "
              f"largest_upper={worst}/{SCALE}")


if __name__ == "__main__":
    if len(sys.argv) != 2:
        raise SystemExit("Pass the arXiv:1812.07279v3 source archive as the sole argument.")
    main(sys.argv[1])
