"""Check the 15-vertex witness directly, using only the Python standard library."""

from itertools import combinations, permutations


def double_leaf_star(groups):
    graph = [set() for _ in range(3 * groups)]

    def join(a, b):
        graph[a].add(b)
        graph[b].add(a)

    for i in range(groups):
        if i:
            join(0, i)
        join(i, groups + i)
        join(i, 2 * groups + i)
    return graph


def burns(graph, schedule):
    lit = set()
    for source in schedule:
        if source in lit:
            return False
        lit |= {source} | {v for u in lit for v in graph[u]}
    return len(lit) == len(graph)


def power_dominates(graph, seeds):
    seen = set(seeds) | {v for u in seeds for v in graph[u]}
    while len(seen) < len(graph):
        added = set()
        for u in seen:
            unseen_neighbors = graph[u] - seen
            if len(unseen_neighbors) == 1:
                added.update(unseen_neighbors)
        if not added:
            return False
        seen.update(added)
    return True


def first_successes(graph, choices, check):
    vertices = range(len(graph))
    for size in range(len(graph) + 1):
        count = sum(check(graph, trial) for trial in choices(vertices, size))
        if count:
            return size, count
    raise AssertionError("All vertices must suffice")


if __name__ == "__main__":
    graph = double_leaf_star(5)
    b, schedules = first_successes(graph, permutations, burns)
    p, seeds = first_successes(graph, combinations, power_dominates)
    print(f"vertices={len(graph)}, edges={sum(map(len, graph)) // 2}")
    print(f"burning number={b}, optimal ordered schedules={schedules}")
    print(f"power domination number={p}, optimal seed sets={seeds}")
    print(f"rank 54: {p} <= {3*b - 5} is {p <= 3*b - 5}")
    assert (b, p, seeds) == (3, 5, 3**5)
