from argparse import ArgumentParser
from fractions import Fraction
from math import isqrt

import numpy as np


def prime_array(limit):
    flags = np.ones(limit + 1, dtype=bool)
    flags[:2] = False
    for d in range(2, isqrt(limit) + 1):
        if flags[d]:
            flags[d * d::d] = False
    return np.flatnonzero(flags).astype(np.int64)


def is_prime(m, trial_primes):
    if m < 2:
        return False
    for d in trial_primes:
        if d * d > m:
            break
        if m % d == 0:
            return False
    return True


def h_function(n, primes):
    return int(primes[primes < n].sum()) + n * int(np.searchsorted(primes, isqrt(n), side="right"))


def exact_optimum(n):
    from scipy.optimize import Bounds, LinearConstraint, linprog, milp
    from scipy.sparse import csc_matrix

    primes = prime_array(n).tolist()
    support = [[] for _ in range(n + 1)]
    for p in primes:
        for multiple in range(p, n + 1, p):
            support[multiple].append(p)
    largest = {}
    for m in range(2, n + 1):
        largest[tuple(support[m])] = m
    row = {p: i for i, p in enumerate(primes)}
    rows, columns = [], []
    for j, factors in enumerate(largest):
        for p in factors:
            rows.append(row[p])
            columns.append(j)
    matrix = csc_matrix((np.ones(len(rows)), (rows, columns)), shape=(len(primes), len(largest)))
    weights = np.asarray(list(largest.values()), dtype=float)
    packing = milp(-weights, integrality=np.ones(len(largest)), bounds=Bounds(0, 1),
                   constraints=LinearConstraint(matrix, 0, 1), options={"mip_rel_gap": 0})
    if not packing.success:
        raise RuntimeError(packing.message)
    chosen = [int(m) for m, x in zip(weights, packing.x) if x > 0.5]
    occupied = set()
    for m in chosen:
        assert occupied.isdisjoint(support[m])
        occupied.update(support[m])
    value = sum(chosen)
    relaxation = linprog(-weights, A_ub=matrix, b_ub=np.ones(len(primes)))
    if not relaxation.success:
        raise RuntimeError(relaxation.message)
    prices = {p: Fraction(float(-y)).limit_denominator(10**6)
              for p, y in zip(primes, relaxation.ineqlin.marginals)}
    certified = (all(price >= 0 for price in prices.values())
                 and all(sum(prices[p] for p in factors) >= m for factors, m in largest.items())
                 and sum(prices.values()) == value)
    return value + 1, certified


def greedy_deficit(n):
    root = isqrt(n)
    small = prime_array(root).tolist()
    ceiling = n
    loss = partner_sum = squares = 0
    for p in small:
        candidate = min(n // p, ceiling - 1)
        if candidate % 2 == 0 and candidate != 2:
            candidate -= 1
        while candidate > root and not is_prime(candidate, small):
            candidate -= 2
        if candidate > root:
            loss += n - p * candidate
            partner_sum += candidate
            ceiling = candidate
        else:
            loss += n - p * p
            squares += 1
            ceiling = root + 1
    deficit = loss + sum(small) + partner_sum - 1 - n * is_prime(n, small)
    return deficit, loss, squares


def direct_deficit(n):
    primes = prime_array(n).tolist()
    small = [p for p in primes if p * p <= n]
    unused = set(primes) - set(small)
    chosen = [1]
    for p in small:
        partner = max((q for q in unused if p * q <= n), default=None)
        if partner is None:
            chosen.append(p * p)
        else:
            chosen.append(p * partner)
            unused.remove(partner)
    chosen.extend(unused)
    return h_function(n, np.asarray(primes, dtype=np.int64)) - sum(chosen)


def sweep(n, primes, top):
    root = isqrt(n)
    x = float(n) ** 0.5
    first_large = int(np.searchsorted(primes, root, side="right"))
    small = primes[int(np.searchsorted(primes, n // (top + 1), side="right")):first_large]
    slots = primes[first_large:int(np.searchsorted(primes, top, side="right"))]
    slots_above = len(slots) - np.searchsorted(slots, n // small, side="right")
    arrival_index = slots_above + np.arange(len(small))
    total = len(small) + len(slots)
    is_arrival = np.zeros(total, dtype=bool)
    is_arrival[arrival_index] = True
    position = np.empty(total)
    position[is_arrival] = n / small.astype(float)
    position[~is_arrival] = slots[::-1]
    label = np.empty(total, dtype=np.int64)
    label[is_arrival] = small
    label[~is_arrival] = slots[::-1]
    partial = np.cumsum(np.where(is_arrival, 1, -1))
    waiting = partial - np.minimum.accumulate(np.minimum(partial, 0))
    below = np.append(position[1:], x)
    before = np.concatenate(([0], waiting[:-1]))
    served_by = label[~is_arrival & (before > 0)]
    return {"x": x, "position": position, "below": below, "waiting": waiting,
            "arrivals": small, "served_by": served_by}


def queue_integral(state, low, high):
    upper = np.minimum(state["position"], high)
    lower = np.maximum(state["below"], low)
    active = upper > lower
    waiting = state["waiting"][active]
    if len(waiting) == 0:
        return 0.0, 0
    return float(np.sum(waiting * np.log(upper[active] / lower[active]))), int(waiting.max())


def near_diagonal(n, primes):
    state = sweep(n, primes, isqrt(64 * n))
    return queue_integral(state, state["x"], 2 * state["x"])


def check_small_cases():
    for n in range(2, 301):
        assert greedy_deficit(n)[0] == direct_deficit(n)
    for n in list(range(4, 3000, 7)) + [10**4, 10**5, 10**6, 1018081]:
        primes = prime_array(max(n // 2, isqrt(64 * n)))
        state = sweep(n, primes, n // 2)
        arrivals, served_by = state["arrivals"], state["served_by"]
        products = arrivals[:len(served_by)] * served_by
        assert np.all(products <= n)
        loss = int(np.sum(n - products)) + int(np.sum(n - arrivals[len(served_by):] ** 2))
        assert loss == greedy_deficit(n)[1]
        total = queue_integral(state, state["x"], n / 2)[0]
        assert loss <= 2 * n * total + 1e-6 * n
        if n >= 64:
            assert abs(near_diagonal(n, primes)[0]
                       - queue_integral(state, state["x"], 2 * state["x"])[0]) < 1e-9


def main():
    parser = ArgumentParser()
    parser.add_argument("check", nargs="?", default="all", choices=("all", "exact", "greedy", "sweep", "sample"))
    args = parser.parse_args()
    if args.check in ("all", "exact"):
        print("n  G(n)  H(n)-G(n)  H(n)-C(n)  dual certificate")
        for n, expected in ((10**3, 85685), (10**4, 5972790), (10**5, 460762887), (10**6, 37717171223)):
            optimum, certified = exact_optimum(n)
            assert optimum == expected
            h = h_function(n, prime_array(n))
            print(n, optimum, h - optimum, greedy_deficit(n)[0], certified)
    if args.check in ("all", "greedy"):
        check_small_cases()
        print("n  H(n)-C(n)  (H(n)-C(n))/n  squares")
        for k in range(3, 11):
            n = 10**k
            deficit, _, squares = greedy_deficit(n)
            print(n, deficit, f"{deficit / n:.4f}", squares)
    if args.check in ("all", "sweep"):
        print("n  I(n)  max W on (X,2X]  outer integral")
        primes = prime_array(8 * 10**7)
        for k in range(4, 15):
            n = 10**k
            inner, peak = near_diagonal(n, primes)
            outer = ""
            if k <= 8:
                state = sweep(n, primes, n // 2)
                outer = f"{queue_integral(state, 2 * state['x'], n / 2)[0]:.4f}"
            print(n, f"{inner:.4f}", peak, outer)
    if args.check in ("all", "sample"):
        print("N  mean I(n)  max I(n)  max W   over 1000 equally spaced n in (N,2N]")
        for k in (8, 10, 12, 14):
            base = 10**k
            primes = prime_array(isqrt(128 * base) + 1)
            values = [near_diagonal(base + j * (base // 1000), primes) for j in range(1, 1001)]
            integrals = [v[0] for v in values]
            print(base, f"{sum(integrals) / len(integrals):.4f}", f"{max(integrals):.4f}",
                  max(v[1] for v in values))


if __name__ == "__main__":
    main()
