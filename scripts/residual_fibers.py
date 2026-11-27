"""All binary two-dimensional residual fibers."""
import math
from collections import Counter
from itertools import product


def span(rows):
    vals={0}
    for r in rows:
        vals |= {r^x for x in vals}
    return frozenset(vals)


def state(m,x):
    out=0
    for i,col in enumerate(m):
        if (x>>i)&1:
            out ^= col
    return out


def residual():
    vectors=range(4)
    matrices=list(product(vectors,repeat=2))
    bases=[(),(1,),(2,),(3,),(1,2)]
    num=0
    by_bits=Counter()
    for F,P,C in product(matrices,bases,bases):
        fibers={}
        for S in matrices:
            old=tuple(state(S,x) for x in P)
            new=tuple(state(F,state(S,x)) for x in C)
            fibers.setdefault(old,set()).add(new)
        r=int(math.log2(len(span(F))))
        d=int(math.log2(len(span(P+C))//len(span(P))))
        assert {len(v) for v in fibers.values()}=={2**(r*d)}
        by_bits[r*d]+=1
        num+=1
    return {"configurations":num,"by_exact_residual_bits":dict(by_bits)}


if __name__ == "__main__":
    print(residual())
