"""Exhaustive check for the seven-point triangle-profile argument."""

from collections import Counter
from itertools import combinations, permutations


ORDER = 7
MAX_TRIANGLE_TYPES = 4
MAX_DISTANCE_LABELS = 6


def compatible_prefix(edges, size):
    """Apply geometric conditions on the vertices with all edges assigned."""
    vertices = range(size)
    for a, b in combinations(vertices, 2):
        # Two circles with distinct centers have at most two common points.
        counts = Counter(
            (edges[a][c], edges[b][c]) for c in vertices if c not in (a, b)
        )
        if any(count > 2 for count in counts.values()):
            return False
    for points in combinations(vertices, 4):
        if len({edges[a][b] for a, b in combinations(points, 2)}) == 1:
            return False
    return True


def colorings():
    """Enumerate distance labels in order of their first occurrence."""
    edges = [[-1] * ORDER for _ in range(ORDER)]

    def assign(vertex, neighbor, used, profiles):
        if neighbor == vertex:
            if not compatible_prefix(edges, vertex + 1):
                return
            if vertex + 1 == ORDER:
                incidences = Counter(c for p in profiles for c in set(p))
                if used >= 3 and all(incidences[c] >= 2 for c in range(used)):
                    yield used, tuple(tuple(row) for row in edges)
            else:
                yield from assign(vertex + 1, 0, used, profiles)
            return

        for color in range(min(used + 1, MAX_DISTANCE_LABELS)):
            # A triangle is complete when its last edge, (vertex, neighbor),
            # has been assigned. Its third vertex is smaller than neighbor.
            added = {
                tuple(sorted((color, edges[vertex][third], edges[neighbor][third])))
                for third in range(neighbor)
            }
            next_profiles = profiles | added
            if len(next_profiles) > MAX_TRIANGLE_TYPES:
                continue
            edges[vertex][neighbor] = edges[neighbor][vertex] = color
            yield from assign(vertex, neighbor + 1, max(used, color + 1), next_profiles)

    yield from assign(1, 0, 0, set())


def has_bisector_obstruction(edges):
    # All vertices in on_bisector lie on one line in a planar realization.
    for a, b in combinations(range(ORDER), 2):
        on_bisector = [
            c for c in range(ORDER) if c not in (a, b) and edges[c][a] == edges[c][b]
        ]
        for c, d in combinations(on_bisector, 2):
            equidistant = [
                x for x in on_bisector if x not in (c, d) and edges[x][c] == edges[x][d]
            ]
            if len(equidistant) >= 2:
                return True
    return False


def has_cyclic_order(edges):
    for tail in permutations(range(1, ORDER)):
        order = (0,) + tail
        if all(
            all(
                edges[order[i]][order[(i + step) % ORDER]] == edges[0][order[step]]
                for i in range(1, ORDER)
            )
            for step in range(1, 4)
        ):
            return True
    return False


def main():
    counts = Counter()
    for used, edges in colorings():
        counts[used] += 1
        if used >= 5:
            raise AssertionError(("Five- or six-label exception", edges))
        if used == 4 and not has_bisector_obstruction(edges):
            raise AssertionError(("Four-label exception", edges))
        if used == 3 and not has_cyclic_order(edges):
            raise AssertionError(("Three-label exception", edges))

    if counts != {3: 120, 4: 105}:
        raise AssertionError(("Unexpected enumeration totals", counts))
    print("Three labels: all 120 matrices have a cyclic distance order.")
    print("Four labels: all 105 matrices have the bisector obstruction.")
    print("Five or six labels: no matrix passed the necessary conditions.")


if __name__ == "__main__":
    main()

