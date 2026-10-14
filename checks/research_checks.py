#!/usr/bin/env python3
"""Deterministic exact-arithmetic checks of the new statements and algorithms.

The checks are finite tests, not proofs of the quantified theorems. They compute
mixed-depth capacities by dynamic programming rather than the manuscript's
single-path formula, and enumerate the algorithms' full random branch laws.
"""
from __future__ import annotations
from fractions import Fraction as F
from itertools import product
from collections import defaultdict
from functools import lru_cache
from math import log, log1p, ceil, log2
from pathlib import Path
import json, random, time
from atom_access import make_plan, make_pointwise_plan, branch, fixed_error_branch

R = C = F(9, 4)
counts = defaultdict(int)

def words(n):
    return tuple(''.join(x) for x in product('01', repeat=n))

def prefix_mass(n, weights):
    p = {u: F(0) for t in range(n+1) for u in words(t)}
    for x, w in weights.items():
        for t in range(n+1):
            p[x[:t]] += w
    assert p[''] == 1
    return p

def target(n, nu, alpha, x):
    return {u:(1-alpha)*v + alpha*int(x.startswith(u)) for u,v in nu.items()}

def capacity(n, mu, h):
    @lru_cache(None)
    def dp(u):
        v = mu[u]*mu[u]/h[u] if h[u] else F(0)
        assert h[u] or not mu[u]
        return v if len(u)==n else max(v,dp(u+'0')+dp(u+'1'))
    return dp('')

def comb(n, d):
    nu = {u:F(1,16*2**len(u)) for t in range(n+1) for u in words(t)}
    for u in nu:
        if len(u) <= d:
            nu[u] += F(15,16*2**len(u))
        elif set(u[d:]) <= {'0'}:
            nu[u] += F(15,16*2**d)
    atoms = tuple(y+'0'*(j-1)+'1'+'0'*(n-d-j)
                  for y in words(d) for j in range(1,n-d+1))
    return nu, atoms

def public_guide(n,d,nu,mu):
    return {u:nu[u] if (len(u)<n and (len(u)<=d or set(u[d:]) <= {'0'}))
            else mu[u] for u in nu}

def law_check(n,nu,atoms,alpha,beta,h,x,strategy):
    plan = (make_pointwise_plan(atoms,nu.__getitem__,alpha,beta=beta,strategy='partition')
            if strategy=='pointwise-partition' else
            make_plan(atoms,nu.__getitem__,alpha,beta=beta,strategy=strategy))
    out = defaultdict(F); fallback = F(0); worst = 0
    for shift in range(len(plan.groups)):
        for coin,w in ((F(0),plan.thin),(plan.thin,1-plan.thin)):
            if not w: continue
            calls=[]
            def oracle(u):
                calls.append(u)
                return h[u]
            result = branch(plan,nu.__getitem__,oracle,shift,coin)
            assert result.queries == len(calls) <= plan.cap
            worst=max(worst,result.queries)
            weight=w/len(plan.groups)
            if result.atom is None: fallback += weight
            else: out[result.atom] += weight
            counts['enumerated_algorithm_executions'] += 1
    assert fallback == 1-beta
    assert dict(out) == {x:beta}
    # The complete unconditional law, including every fallback leaf.
    for y in words(n):
        assert fallback*nu[y]+out[y] == (1-beta)*nu[y]+beta*int(y==x)
    counts['complete_output_laws'] += 1
    counts['checked_output_coordinates'] += 2**n
    return worst,plan.cap

def check_public_capacity():
    for n in range(1,9):
        for alpha in (F(1,4),F(1,8),F(1,16),F(3,20)):
            d=min(n-1,(alpha.denominator**2//alpha.numerator**2).bit_length()-1)
            nu,atoms=comb(n,d)
            for x in atoms[::max(1,len(atoms)//8)]:
                mu=target(n,nu,alpha,x); h=public_guide(n,d,nu,mu)
                cap=capacity(n,mu,h)
                formula=max([F(1)]+[1+alpha-2*alpha**2-(1-alpha)*alpha*nu[u]+alpha**2/nu[u]
                          for u in h if h[u]==nu[u] and len(u)<n and x.startswith(u)])
                assert cap==formula <= F(263,120) < C
                assert all(h[u] <= F(4,3)*mu[u] for u in h)
                assert all(h[y] == mu[y] for y in words(n))
                counts['mixed_depth_capacity_identities'] += 1
            # Arbitrary prefix answers differ from the public baseline for at
            # most one candidate, which checks the equality-oracle simulation.
            for u in nu:
                answers=[]
                for x in atoms:
                    mu_u=(1-alpha)*nu[u]+alpha*int(x.startswith(u))
                    is_public=len(u)<n and (len(u)<=d or set(u[d:]) <= {'0'})
                    ans=nu[u] if is_public else mu_u
                    baseline=nu[u] if is_public else (1-alpha)*nu[u]
                    if ans != baseline: answers.append(x)
                assert len(answers)<=1
                counts['arbitrary_prefix_equality_checks'] += 1

def check_fixed_error():
    for L in range(1,7):
        n=L+4; nu,atoms=comb(n,4)
        for x in atoms:
            mu=target(n,nu,F(1,4),x)
            for mode in ('exact','lower','upper','adversarial'):
                h={u:(mu[u] if len(u) in (0,n) or mode=='exact' else
                       mu[u]/R if mode=='lower' else
                       R*mu[u] if mode=='upper' else
                       mu[u]/R if x.startswith(u) else R*mu[u]) for u in nu}
                outputs=defaultdict(F); fallback=F(0)
                for shift in range(16):
                    calls=[]
                    def oracle(u): calls.append(u); return h[u]
                    r=fixed_error_branch(L,oracle,shift)
                    assert len(calls)==r.queries<=4+ceil(log2(L))
                    if r.atom is None: fallback+=F(1,16)
                    else: outputs[r.atom]+=F(1,16)
                    counts['fixed_error_pointwise_executions']+=1
                assert dict(outputs)=={x:F(1,4)} and fallback==F(3,4)
                for y in words(n): assert outputs[y]+fallback*nu[y]==mu[y]
                counts['fixed_error_full_laws']+=1
            # Exact lower-bound integrality and the leaf-search matching law.
            eps=F(3,64*2**n)
            assert ceil(16*L*(F(1,4)-F(1,16)+eps)-1)==3*L
            assert ceil(16*L*(F(1,4)+eps)-1)==4*L
            for q,delta in ((3*L,F(1,16)),(4*L,F(0))):
                tv=sum(abs((1-F(q,16*L))*nu[y]+F(q,16*L)*int(y==x)-mu[y])
                       for y in words(n))/2
                assert tv <= delta
                counts['fixed_error_safe_caps']+=1

def check_general_samplers():
    rng=random.Random(90416)
    for n in range(2,8):
        ww=words(n)
        raw=[rng.randrange(1,12) for _ in ww]
        total=sum(raw)
        random_nu=prefix_mass(n,dict(zip(ww,(F(v,total) for v in raw))))
        zero_nu=prefix_mass(n,{ww[0]:F(1)})
        uniform={u:F(1,2**len(u)) for t in range(n+1) for u in words(t)}
        nu_comb,_=comb(n,max(0,n//2))
        for nu in (uniform,random_nu,zero_nu,nu_comb):
            atoms=tuple(ww[i] for i in sorted(rng.sample(range(len(ww)),min(9,len(ww)))))
            for alpha in (F(1,4),F(3,20),F(1,16)):
                for x in atoms[::max(1,len(atoms)//3)]:
                    mu=target(n,nu,alpha,x)
                    # An additive capacity envelope constructs a safe guide
                    # that need not be pointwise accurate.
                    xi={u:F(int(ww[-1].startswith(u))) for u in nu}
                    h={u:mu[u] if len(u) in (0,n) else
                       mu[u]**2/(mu[u]+(C-1)*xi[u]) if mu[u] else F(0) for u in nu}
                    assert capacity(n,mu,h)<=C
                    for beta in (alpha,3*alpha/4):
                        for strategy in ('leaves','partition','auto'):
                            law_check(n,nu,atoms,alpha,beta,h,x,strategy)
    # Full-cube groups genuinely need recovery and non-integral thinning.
    n=10; ww=words(n)
    nu={u:F(1,2**len(u)) for t in range(n+1) for u in words(t)}
    for alpha in (F(1,4),F(3,20)):
        for x in ww[::127]:
            mu=target(n,nu,alpha,x)
            h={u:mu[u] if len(u) in (0,n) else mu[u]**2/(mu[u]+(C-1)*int(x.startswith(u)))
               for u in nu}
            for beta in (alpha,3*alpha/4):
                law_check(n,nu,ww,alpha,beta,h,x,'partition')

def check_branching_moments():
    rng=random.Random(34471)
    for n in range(1,8):
        ww=words(n)
        for trial in range(12):
            vals=[rng.randrange(0,10) for _ in ww]
            if not sum(vals): vals[0]=1
            mu=prefix_mass(n,{x:F(v,sum(vals)) for x,v in zip(ww,vals)})
            h={u:mu[u] if len(u) in (0,n) else mu[u]*F(rng.randrange(1,17),8) for u in mu}
            @lru_cache(None)
            def recurrence(u):
                if not h[u]: return F(0),F(0),F(0)
                if len(u)==n: return F(1),F(0),F(0)
                mean=var=F(0); cost=F(2)
                for b in '01':
                    m,v,c=recurrence(u+b); lam=h[u+b]/h[u]
                    mean+=lam*m; var+=lam*(v+m*m); cost+=lam*c
                return mean,var,cost
            mean,var,cost=recurrence('')
            S=sum(mu[u]**2/h[u] for u in mu if u and h[u])
            H=sum(h[u] for u in h if len(u)<n)
            assert mean==1 and var==S and cost==2*H
            counts['independent_branching_moment_recursions']+=1



def check_pointwise_backgrounds():
    rng=random.Random(192763)
    for n in range(2,9):
        ww=words(n)
        vv=[rng.randrange(0,9) for _ in ww]
        if not sum(vv):vv[0]=1
        random_nu=prefix_mass(n,{x:F(v,sum(vv)) for x,v in zip(ww,vv)})
        uniform=prefix_mass(n,{x:F(1,2**n) for x in ww})
        for nu in (uniform,random_nu,comb(n,max(0,n//3))[0]):
            atoms=ww if n<=6 else tuple(ww[i] for i in range(0,len(ww),3))
            for alpha in (F(1,4),F(3,20),F(1,16)):
                for x in atoms[::max(1,len(atoms)//3)]:
                    mu=target(n,nu,alpha,x)
                    h={u:mu[u] if len(u) in (0,n) else
                       mu[u]/R if x.startswith(u) else R*mu[u] for u in nu}
                    law_check(n,nu,atoms,alpha,alpha,h,x,'pointwise-partition')
                    counts['pointwise_background_full_laws']+=1
                    p=make_pointwise_plan(atoms,nu.__getitem__,alpha,strategy='partition')
                    for g in p.groups:
                        if not g.exact_leaf:
                            assert len(g.candidates)<=alpha*len(atoms)
                            counts['candidate_balanced_light_groups']+=1
    ratios=[]
    for n in range(1,129):
        for j in range(2,101):
            alpha=2.0**(-j);z=2.0**(n-j)
            d=min(n-1,j-2);K=2**d*(n-d)
            ratios.append(alpha*K/log1p(z))
    assert min(ratios)>.35 and max(ratios)<1.01
    counts['pointwise_geometry_checks']+=len(ratios)
    for n in range(1,9):
        for alpha in (F(1,4),F(1,8),F(1,16),F(3,20)):
            d=min(n-1,(alpha.denominator//(4*alpha.numerator)).bit_length()-1)
            nu,atoms=comb(n,d)
            for x in atoms[::max(1,len(atoms)//5)]:
                mu=target(n,nu,alpha,x);h=public_guide(n,d,nu,mu)
                assert all(mu[u]/F(4,3)<=h[u]<=F(4,3)*mu[u] for u in mu)
                counts['pointwise_comb_guide_checks']+=1
    return [min(ratios),max(ratios)]

def check_capacity_concatenation():
    """Compute the full product cut DP separately from the excess-cut DP."""
    rng=random.Random(449632)
    for d in range(1,5):
        for n in range(1,5):
            for trial in range(16):
                def instance(k):
                    ww=words(k)
                    vv=[rng.randrange(0,8) for _ in ww]
                    if not sum(vv): vv[0]=1
                    mu=prefix_mass(k,{x:F(v,sum(vv)) for x,v in zip(ww,vv)})
                    h={u:mu[u] if len(u) in (0,k) else
                       mu[u]*F(rng.randrange(1,13),4) for u in mu}
                    return mu,h
                nu,g=instance(d);sig,h=instance(n)
                co=capacity(d,nu,g);ci=capacity(n,sig,h)
                product_mu={u:(nu[u] if len(u)<=d else nu[u[:d]]*sig[u[d:]])
                            for t in range(d+n+1) for u in words(t)}
                product_h={u:(g[u] if len(u)<=d else nu[u[:d]]*h[u[d:]])
                           for u in product_mu}
                whole=capacity(d+n,product_mu,product_h)
                @lru_cache(None)
                def excess(u):
                    if len(u)==d: return F(0)
                    reward=(nu[u]**2/g[u] if g[u] else F(0))-ci*nu[u]
                    return max(F(0),reward,excess(u+'0')+excess(u+'1'))
                assert whole==ci+excess('') <= co+ci-1
                rout=max(nu[u]/g[u] for u in nu if g[u])
                assert whole<=max(rout,ci)
                counts['full_product_capacity_identities']+=1

def check_coherent_repair():
    rng=random.Random(591110)
    for n in range(1,7):
        for trial in range(12):
            ww=words(n)
            vv=[rng.randrange(0,8) for _ in ww]
            if not sum(vv): vv[0]=1
            mu=prefix_mass(n,{x:F(v,sum(vv)) for x,v in zip(ww,vv)})
            h={u:mu[u] if len(u) in (0,n) else
               mu[u]*F(rng.randrange(0,17),4) for u in mu}
            demand={u:max(F(0),h[u]-R*mu[u],mu[u]-R*h[u]) for u in mu}
            # A simple (not optimal) additive envelope is the sum of a
            # demand-sized point mass at one descendant of each prefix.
            lam_leaf={x:F(0) for x in ww}
            for u,v in demand.items(): lam_leaf[u+'0'*(n-len(u))]+=v
            lam={u:sum(v for x,v in lam_leaf.items() if x.startswith(u)) for u in mu}
            B=lam[''];den=1+B/(R-1)
            mh={u:(mu[u]+lam[u]/(R-1))/den for u in mu}
            hh={u:(h[u]+lam[u]/(R-1))/den for u in mu}
            assert all(lam[u]>=demand[u] and mh[u]/R<=hh[u]<=R*mh[u] for u in mu)
            assert all(mh[x]==hh[x] for x in ww) and mh['']==hh['']==1
            tv=sum(abs(mh[x]-mu[x]) for x in ww)/2
            assert tv<=B/(R-1+B)
            counts['coherent_repair_instances']+=1

def check_geometry():
    ratios=[]
    for n in range(1,257):
        for j in range(2,161):
            # Power-of-two weights exercise both sides of every cutoff.
            alpha=2.0**(-j); B=1/alpha; z=2.0**(n-2*j)
            d=min(n-1,2*j); K=2**d*(n-d)
            ratios.append(alpha*K/(B*log1p(z)))
            counts['geometry_parameter_checks']+=1
    assert min(ratios)>.49 and max(ratios)<1.5
    return [min(ratios),max(ratios)]

def check_seed_reuse_mutant():
    L=2;n=6;nu,atoms=comb(n,4);x=atoms[0];mu=target(n,nu,F(1,4),x)
    bad=defaultdict(F)
    for y in words(n):
        r=fixed_error_branch(L,mu.__getitem__,int(y[:4],2))
        bad[y if r.atom is None else r.atom]+=nu[y]
    tv=sum(abs(bad[y]-mu[y]) for y in words(n))/2
    assert tv==F(3,16)>F(1,16)
    counts['detected_seed_reuse_mutants']+=1
    return str(tv)

def main():
    start=time.time()
    check_public_capacity();check_fixed_error();check_general_samplers()
    check_branching_moments();check_capacity_concatenation();check_coherent_repair()
    ratios=check_geometry();point_ratios=check_pointwise_backgrounds();mutant=check_seed_reuse_mutant()
    data={'status':'passed','arithmetic':'fractions.Fraction except asymptotic geometry grid',
          'counts':dict(counts),'geometry_ratio_range':ratios,'pointwise_geometry_ratio_range':point_ratios,
          'biased_seed_reuse_total_variation':mutant,'elapsed_seconds':round(time.time()-start,3),
          'scope':'Finite executable checks only; no formal proof or independent human review.'}
    import sys
    out=Path(sys.argv[1]) if len(sys.argv)>1 else Path(__file__).with_name('research-results.json')
    out.write_text(json.dumps(data,indent=2)+'\n')
    print(json.dumps(data,indent=2))
if __name__=='__main__':main()
