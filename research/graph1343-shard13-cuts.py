"""Small finite certificates for the clean-prefix cut in FIRSTJ=13.

This program concerns only a necessary cut condition. It does not search
for an unrestricted 21-gate circuit or certify an entire official shard.
"""
from itertools import combinations
import argparse
from functools import lru_cache

EDGES = ((0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6),
         (3, 7), (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10),
         (7, 9), (8, 9))
VERTICES = range(11)


def mask(vertices):
    return sum(1 << v for v in vertices)


EDGE_MASKS = [mask(e) for e in EDGES]
NEIGHBORS = [mask(v for e in EDGES if u in e for v in e if u != v)
             for u in VERTICES]


def positive(bits):
    return any(bits & e == e for e in EDGE_MASKS)


MAX_INDEPENDENT = [bits for bits in range(1 << 11) if not positive(bits)
                   and all(bits >> u & 1 or positive(bits | 1 << u)
                           for u in VERTICES)]
OBLIGATIONS = [(u, r) for u in VERTICES for r in MAX_INDEPENDENT
               if not r >> u & 1 and r & NEIGHBORS[u]]


def conflict(a, b):
    u, r = a
    v, s = b
    return bool((s >> u & 1) or (r >> v & 1))


# Eight pairwise conflicting obligations. In any proper coloring with at
# least eight colors one may permute the names of the colors to fix these.
ANCHORS = [(0, (2, 4, 6, 9)), (1, (0, 3, 4, 5)), (2, (1, 3, 9, 10)),
           (6, (1, 2, 3, 9)), (4, (1, 2, 6, 9)), (5, (0, 2, 4, 6)),
           (3, (0, 4, 5, 6)), (9, (0, 1, 3, 5))]
ANCHORS = [(u, mask(r)) for u, r in ANCHORS]


def colorable(colors, obligations, node_limit=None):
    nodes = 0
    all_vertices = (1 << len(obligations)) - 1
    neighbors = [sum(1 << j for j, w in enumerate(obligations)
                     if conflict(v, w)) for v in obligations]
    blocked = [0] * colors
    remaining = all_vertices
    active_anchors = [v for v in ANCHORS if v in obligations]
    if len(active_anchors) > colors:
        return False, 0
    for c, v in enumerate(active_anchors):
        i = obligations.index(v)
        blocked[c] = neighbors[i]
        remaining &= ~(1 << i)

    def visit(left):
        nonlocal nodes
        nodes += 1
        if node_limit is not None and nodes > node_limit:
            raise TimeoutError
        if not left:
            return True
        # after processing c colors, at_most[k] is the bitset of remaining
        # vertices enjoying at most k permitted colors amongst those c.
        at_most = [left]
        for forbidden in blocked:
            allowed = left & ~forbidden
            at_most = ([at_most[0] & ~allowed]
                       + [(at_most[k] & ~allowed) | (at_most[k-1] & allowed)
                          for k in range(1, len(at_most))] + [left])
        if at_most[0]:
            return False
        group = next(group for group in at_most if group)
        bit = group & -group
        i = bit.bit_length() - 1
        for c, previous in enumerate(blocked):
            if previous & bit:
                continue
            blocked[c] = previous | neighbors[i]
            if visit(left ^ bit):
                return True
            blocked[c] = previous
        return False

    try:
        return visit(remaining), nodes
    except TimeoutError:
        return None, nodes


FIVE_EDGE_TEST = [
    (3, 6, (1, 2, 6, 9)), (0, 10, (1, 3, 5, 10)),
    (4, 1, (0, 1, 3, 5)), (6, 3, (0, 3, 4, 5)),
    (2, 5, (0, 4, 5, 6)), (9, 0, (0, 2, 4, 6)),
    (1, 4, (2, 4, 6, 9)), (5, 2, (1, 2, 3, 9)),
]
TEN_SUPPORTS = [(0, 5, 7, 8), (1,), (0, 2, 4, 6), (6, 10), (4, 10),
                (5, 9), (3,), (2, 8, 9), (8, 10), (7,)]


def joint_prefix_price(stars, boundary, other_ands=0):
    """Lower bound for specified first-mixing (center, opposite mask) gates."""
    by_center = {}
    supports_at = {}
    for c, support in stars:
        if not support or support & ~NEIGHBORS[c]:
            raise ValueError('an opposite support must be nonempty and lie in the neighborhood')
        by_center[c] = by_center.get(c, 0) | support
        supports_at.setdefault(c, set()).add(support)
    available = set(1 << u for u in VERTICES) | {s for c, s in stars}
    size = lambda s: bin(s).count('1')

    def free(s):
        return any(not (s & ~a) for a in available)

    @lru_cache(None)
    def cover(s):
        if not s:
            return 0
        pivot = s & -s
        return 1 + min(cover(s & ~a) for a in available if a & pivot)

    targets = sorted(set(s for s in boundary if not free(s)))
    if len(targets) > 9:
        raise ValueError('a FIRSTJ=13 suffix has at most nine distinct outside reads')
    bonuses = [max(0, cover(s) - 1 - sum(not (t & ~s) for t in targets))
               for s in targets]
    supplemental = 0
    for chosen_bits in range(1 << len(targets)):
        chosen = [i for i in range(len(targets)) if chosen_bits >> i & 1]
        if all(free(targets[i] & targets[j]) for i,j in combinations(chosen, 2)):
            supplemental = max(supplemental, sum(bonuses[i] for i in chosen))
    star_or_price = sum(max(size(s) - len(supports_at[c]),
                            sum(size(q) > 1 for q in supports_at[c]))
                        for c, s in by_center.items())
    return (len(stars) + star_or_price + other_ands
            + len(targets) + supplemental)


@lru_cache(None)
def formula_counts(leaves):
    if leaves == 1:
        return {(1, 1)}
    counts = set()
    for left in range(1, leaves):
        for a, b in formula_counts(left):
            for c, d in formula_counts(leaves-left):
                counts.add((a+c, b*d))
                counts.add((a*c, b+d))
    return counts


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--omit-edge', action='append', default=[], metavar='U,V')
    parser.add_argument('--omit-star', type=int, action='append', default=[])
    parser.add_argument('--colors', type=int, default=None)
    parser.add_argument('--node-limit', type=int, default=100000)
    args = parser.parse_args()
    assert len(MAX_INDEPENDENT) == 24 and len(OBLIGATIONS) == 170
    assert set(ANCHORS) <= set(OBLIGATIONS)
    assert all(conflict(a, b) for a, b in combinations(ANCHORS, 2))
    five = [(u, mask(r)) for u, v, r in FIVE_EDGE_TEST]
    for u, v, r in FIVE_EDGE_TEST:
        assert v in r and u not in r and tuple(sorted((u, v))) in EDGES
        assert mask(r) in MAX_INDEPENDENT
    assert len({tuple(sorted((u, v))) for u, v, r in FIVE_EDGE_TEST}) == 5
    assert all(conflict(a, b) for a, b in combinations(five, 2))
    supports = [mask(s) for s in TEN_SUPPORTS]
    assert all(any((s >> u & 1) and not (s & r) for s in supports)
               for u, r in OBLIGATIONS)
    def reduced(omitted):
        active = [e for e in EDGES if e not in omitted]
        neighbors = [mask(v for e in active if u in e for v in e if v != u)
                     for u in VERTICES]
        cells = [(u, r) for u, r in OBLIGATIONS if neighbors[u] & r]
        degree = {v: sum(conflict(v, w) for w in cells) for v in cells}
        return sorted(cells, key=lambda v: -degree[v])

    if args.colors is not None or args.omit_edge or args.omit_star:
        if args.colors is None or not 1 <= args.colors <= 11:
            parser.error('choose --colors between 1 and 11')
        if args.node_limit < 1 or not set(args.omit_star) <= set(VERTICES):
            parser.error('invalid node limit or star center')
        omitted = set()
        for edge_text in args.omit_edge:
            try:
                edge = tuple(sorted(map(int, edge_text.split(','))))
            except ValueError:
                parser.error('edges must be given as U,V')
            if edge not in EDGES:
                parser.error(f'{edge_text} is not a listed edge')
            omitted.add(edge)
        omitted.update(e for e in EDGES if any(u in e for u in args.omit_star))
        cells = reduced(omitted)
        result, nodes = colorable(args.colors, cells, args.node_limit)
        state = {True: 'colorable', False: 'infeasible', None: 'unknown (node cap)'}
        print(f'{len(cells)} obligations, {args.colors} colors: {state[result]}, {nodes} calls')
        return
    print('maximal independent sets:', len(MAX_INDEPENDENT))
    print('separation obligations:', len(OBLIGATIONS))
    for k in (8, 9):
        result, nodes = colorable(k, OBLIGATIONS)
        assert not result
        print(f'{k} colors: infeasible after {nodes} exhaustive recursive calls')
    print('10 supports: verified against all obligations')
    print('five-edge eight-obligation witness: verified')
    special = {(4,10), (6,10), (7,9), (4,8)}
    result, nodes = colorable(9, reduced(special))
    assert result is False
    print(f'four omitted edges, 9 colors: infeasible, {nodes} calls')
    star_nodes = []
    for center in VERTICES:
        result, nodes = colorable(8, reduced({e for e in EDGES if center in e}))
        assert result is False
        star_nodes.append(nodes)
    print('one omitted star, 8 colors: all infeasible, calls by center', star_nodes)
    stars = [(c, NEIGHBORS[c]) for c in (4, 8, 7)]
    boundary = [mask((0, 2, 3, 4)), mask((0, 1, 5, 6, 10))]
    bound = joint_prefix_price(stars, boundary)
    assert bound == 16
    print('joint star and two-read example: requires at least 16 prefix gates')
    negative_counts = [
        sum(not bits >> c & 1 and not positive(bits)
            and all(u == c or bits >> u & 1 or positive(bits | 1 << u)
                    for u in VERTICES) for bits in range(1 << 11))
        for c in VERTICES]
    assert negative_counts == [18,16,17,15,16,17,17,17,19,19,19]
    assert max(p for p,q in formula_counts(9) if q >= 17) == 4
    assert max(p for p,q in formula_counts(9) if q >= 15) == 5
    max_clauses = lambda n: max(q for p,q in formula_counts(n))
    assert max(max_clauses(n) + max_clauses(9-n) for n in range(2,8)) == 14
    print('nine-leaf clause bound: verified for all single-center restrictions')


if __name__ == '__main__':
    main()
