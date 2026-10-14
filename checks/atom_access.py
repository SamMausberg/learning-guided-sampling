#!/usr/bin/env python3
"""Exact-rational reference algorithms for guide-derived atom access.

Only the ``guide`` callback exposes the unknown target. Background probabilities,
candidate strings, the mixture weight, and reliability constants are known data.
``branch`` fixes the random cyclic shift and thinning-coin outcome; it returns
None precisely when a *fresh, independent* background sample must be drawn.
All actual guide invocations are charged, including unsuccessful membership tests.
This is a query-complexity reference, not an efficient data representation.
"""
from __future__ import annotations
from dataclasses import dataclass
from fractions import Fraction as F
from typing import Callable, Optional, Sequence

Mass = Callable[[str], F]

@dataclass(frozen=True)
class Group:
    prefix: str
    candidates: tuple[str, ...]
    exact_leaf: bool

@dataclass(frozen=True)
class Plan:
    groups: tuple[Group, ...]
    tests: int
    thin: F
    cap: int
    alpha: F
    beta: F
    R: F
    C: F
    n: int
    strategy: str
    pointwise: bool = False

@dataclass(frozen=True)
class Outcome:
    atom: Optional[str]
    queries: int
    tested: tuple[str, ...]


def ceiling(x: F) -> int:
    return -((-x.numerator) // x.denominator)


def recovery_bound(m: int) -> int:
    k, p, q = 0, m, 1
    while p > q:
        p *= 2
        q *= 3
        k += 1
    return k


def make_plan(candidates: Sequence[str], background: Mass, alpha: F,
              R: F = F(9, 4), C: F = F(9, 4), beta: Optional[F] = None,
              strategy: str = 'auto') -> Plan:
    ss = tuple(sorted(set(candidates)))
    if len(ss) < 2 or len(ss) != len(candidates):
        raise ValueError('At least two distinct candidate atoms are required.')
    n = len(ss[0])
    if n < 1 or any(len(x) != n or set(x) - {'0', '1'} for x in ss):
        raise ValueError('Candidates must be binary strings of one positive length.')
    if not 0 < alpha <= F(1, 4) or R < 1 or C < 1:
        raise ValueError('Invalid mixture weight or reliability constants.')
    beta = alpha if beta is None else beta
    if not 0 < beta <= alpha:
        raise ValueError('This implementation requires 0 < beta <= alpha.')
    if strategy not in {'auto', 'partition', 'leaves'}:
        raise ValueError('Unknown strategy.')
    tau = alpha * alpha / (2 * R * C * (1 - alpha))
    groups: list[Group] = []
    def descend(u: str, xs: tuple[str, ...]) -> None:
        if not xs:
            return
        if len(u) == n:
            groups.append(Group(u, xs, True))
        elif background(u) <= tau:
            groups.append(Group(u, xs, False))
        else:
            for bit in '01':
                v = u + bit
                descend(v, tuple(x for x in xs if x.startswith(v)))
    if strategy != 'leaves':
        descend('', ss)
    leaf_q = ceiling(beta * len(ss))
    group_q = ceiling(beta * len(groups)) if groups else leaf_q
    group_cap = group_q + max((recovery_bound(len(g.candidates)) for g in groups), default=0)
    if strategy == 'leaves' or (strategy == 'auto' and leaf_q <= group_cap):
        groups = [Group(x, (x,), True) for x in ss]
        q, cap, selected = leaf_q, leaf_q, 'leaves'
    else:
        q, cap, selected = group_q, group_cap, 'partition'
    return Plan(tuple(groups), q, beta * len(groups) / q, cap,
                alpha, beta, R, C, n, selected)


def balanced_prefix(root: str, xs: tuple[str, ...]) -> str:
    """A prefix containing between one third and two thirds of the candidates."""
    N = len(xs)
    if N < 2:
        raise ValueError('No split is needed for a singleton.')
    u = root
    current = xs
    while True:
        z = tuple(x for x in current if x.startswith(u + '0'))
        o = tuple(x for x in current if x.startswith(u + '1'))
        bit, child = ('0', z) if len(z) >= len(o) else ('1', o)
        u += bit
        current = child
        if 3 * len(current) <= 2 * N:
            assert 3 * len(current) > N
            return u


def branch(plan: Plan, background: Mass, guide: Mass, shift: int,
           coin: F) -> Outcome:
    """One execution with a fixed cyclic shift and U[0,1) thinning coordinate."""
    if not 0 <= shift < len(plan.groups) or not 0 <= coin < 1:
        raise ValueError('Random coordinates out of range.')
    transcript: list[str] = []
    def query(u: str) -> F:
        transcript.append(u)
        return guide(u)
    threshold = plan.alpha / plan.R if plan.pointwise else plan.alpha * plan.alpha / plan.C
    for j in range(plan.tests):
        g = plan.groups[(shift + j) % len(plan.groups)]
        value = query(g.prefix)
        hit = (value > (1 - plan.alpha) * background(g.prefix)
               if g.exact_leaf else value >= threshold)
        if not hit:
            continue
        if coin >= plan.thin:
            return Outcome(None, len(transcript), tuple(transcript))
        xs = g.candidates
        while len(xs) > 1:
            u = balanced_prefix(g.prefix, xs)
            occupied = query(u) >= threshold
            xs = tuple(x for x in xs if x.startswith(u) == occupied)
            if not xs:
                raise ValueError('The guide violated the membership promise.')
        out = Outcome(xs[0], len(transcript), tuple(transcript))
        assert out.queries <= plan.cap
        return out
    return Outcome(None, len(transcript), tuple(transcript))


def fixed_error_branch(L: int, guide: Mass, shift: int) -> Outcome:
    """The 16-subtree pointwise sampler: alpha=1/4 and four group tests."""
    if L < 1 or not 0 <= shift < 16:
        raise ValueError('Invalid parameter or random coordinate.')
    tested: list[str] = []
    def query(u: str) -> F:
        tested.append(u)
        return guide(u)
    for j in range(4):
        y = format((shift + j) % 16, '04b')
        if query(y) < F(1, 8):
            continue
        lo, hi = 1, L
        while lo < hi:
            t = (lo + hi) // 2
            if query(y + '0' * t) >= F(1, 8):
                lo = t + 1
            else:
                hi = t
        return Outcome(y + '0' * (lo - 1) + '1' + '0' * (L - lo),
                       len(tested), tuple(tested))
    return Outcome(None, len(tested), tuple(tested))


def make_pointwise_plan(candidates: Sequence[str], background: Mass, alpha: F,
                        R: F = F(9, 4), beta: Optional[F] = None,
                        strategy: str = 'auto') -> Plan:
    """Known-background pointwise partition also balances candidate counts."""
    # Reuse the input validation without querying the guide.
    leaf_plan = make_plan(candidates, background, alpha, R=R, beta=beta,
                          strategy='leaves')
    if strategy not in {'auto', 'partition', 'leaves'}:
        raise ValueError('Unknown strategy.')
    if strategy == 'leaves':
        return leaf_plan
    ss=tuple(sorted(candidates));n=len(ss[0]);beta=leaf_plan.beta
    tau=alpha/(4*R*R*(1-alpha));groups=[]
    stack=[('',ss)]
    while stack:
        u,xs=stack.pop()
        if not xs:continue
        if len(u)==n:
            groups.append(Group(u,xs,True))
        elif (background(u)+F(len(xs),len(ss)))/2 <= tau:
            groups.append(Group(u,xs,False))
        else:
            for bit in '10':
                v=u+bit
                stack.append((v,tuple(x for x in xs if x.startswith(v))))
    q=ceiling(beta*len(groups))
    cap=q+max(recovery_bound(len(g.candidates)) for g in groups)
    if strategy=='auto' and leaf_plan.cap<=cap:return leaf_plan
    return Plan(tuple(groups),q,beta*len(groups)/q,cap,alpha,beta,R,R,n,
                'pointwise-partition',True)
