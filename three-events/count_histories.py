"""Search Dickey–Rosenberg, Conjecture 20(ii), using exact integer counts."""

import argparse
from heapq import heapify, heappop, heappush
from itertools import accumulate
from math import prod


def huffman_split(arity, internals):
    # Weight = descendant leaves = 1 + (arity - 1) * internal-node count.
    weights = [0] * (1 + (arity - 1) * internals)
    heapify(weights)
    for _ in range(internals - 1):
        merged = 1 + sum(heappop(weights) for _ in range(arity))
        heappush(weights, merged)
    return tuple(sorted(weights, reverse=True))


def splits(total, slots, ceiling):
    if slots == 1:
        if total <= ceiling:
            yield (total,)
        return
    for first in range(min(total, ceiling), (total + slots - 1) // slots - 1, -1):
        for tail in splits(total - first, slots - 1, first):
            yield (first, *tail)


def count_from_children(children, slots):
    # F[t] counts strict assignments from the first t ordered time slots.
    levels = (prod(child[t] for child in children) for t in range(slots))
    return (0, *accumulate(levels))


def all_levels(counts):
    # Forward differences at zero give the number of surjective assignments.
    column = counts
    while column:
        yield column[0]
        column = [b - a for a, b in zip(column, column[1:])]


def maximum_for_three_events(arity, internals):
    excess = internals - arity - 1
    if excess <= 0:
        return max(0, 2 ** max(0, internals - 1) - 2)
    if excess > arity**2:
        return 0
    deep_branches = (excess + arity - 1) // arity
    return 2 ** (arity - deep_branches)


def scan(arity, limit):
    full = [(1,) * (limit + 1)]  # an empty internal tree has one assignment
    compared = 0
    for m in range(1, limit + 1):
        target = huffman_split(arity, m)
        target_counts = count_from_children([full[n] for n in target], limit)
        target_exact = tuple(all_levels(target_counts[: m + 1]))
        if m >= 3 and target_exact[3] != maximum_for_three_events(arity, m):
            raise AssertionError(f"Three-event formula disagrees at r={arity}, m={m}")
        for split in splits(m - 1, arity, m - 1):
            if split == target:
                continue
            compared += 1
            counts = count_from_children([full[n] for n in split], m)
            exact = tuple(all_levels(counts))
            for z, (a, b) in enumerate(zip(target_exact, exact)):
                if b > a:
                    print("counterexample", dict(
                        arity=arity, internals=m, leaves=(arity - 1) * m + 1,
                        events=z, huffman=target, competitor=split, counts=(a, b),
                        huffman_all=target_exact, competitor_all=exact,
                    ), flush=True)
                    return True
        full.append(target_counts)
    print(f"r={arity}, m<={limit}: {compared} root splits checked, no counterexample", flush=True)
    return False


if __name__ == "__main__":
    cli = argparse.ArgumentParser()
    cli.add_argument("--arity", type=int, nargs="+", default=list(range(2, 11)))
    cli.add_argument("--limit", type=int, default=42)
    args = cli.parse_args()
    if min(args.arity) < 2 or args.limit < 1:
        cli.error("arity must be at least 2 and limit must be positive")
    for arity in args.arity:
        if scan(arity, args.limit):
            break
