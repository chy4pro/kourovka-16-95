#!/usr/bin/env python3
"""K6-GC4EQ: collect and classify low-rank g=6 equality cases."""
from __future__ import annotations

import argparse
import importlib.util
import itertools
import json
import time
from collections import Counter
from pathlib import Path

HERE = Path(__file__).resolve().parent
SOURCE = HERE.parent / "k1695_r6_gc4r2" / "scan.py"
spec = importlib.util.spec_from_file_location("gc4r2_scan", SOURCE)
assert spec is not None and spec.loader is not None
scan = importlib.util.module_from_spec(spec)
spec.loader.exec_module(scan)

np = scan.np
N = 4
PERMS = scan.PERMS
IDENT = tuple(1 if i == j else 0 for i in range(N) for j in range(N))


def rows(m):
    return [list(m[4*i:4*i+4]) for i in range(4)]


def flat(a):
    return tuple(int(x) for row in a for x in row)


def rank_matrix(m, field):
    return scan.rank_rows(rows(m), 4, field.scalar)


def sub_scalar_perm(m, a, p, field):
    out=[]
    for i in range(4):
        for j in range(4):
            base=a if i == p[j] else 0
            out.append(field.scalar.ADD[m[4*i+j]][field.scalar.NEG[base]])
    return tuple(out)


def factor_rank_one(r, field):
    pivot=next((k for k,x in enumerate(r) if x),None)
    if pivot is None:return None
    i0,j0=divmod(pivot,4);pv=r[pivot]
    u=[r[4*i+j0] for i in range(4)]
    w=[field.scalar.MUL[r[4*i0+j]][field.scalar.INV[pv]] for j in range(4)]
    assert all(r[4*i+j] == field.scalar.MUL[u[i]][w[j]] for i in range(4) for j in range(4))
    return u,w


def canonical_full(m, field):
    best=None
    rr=rows(m)
    for transpose in (False,True):
        base=rr if not transpose else [[rr[j][i] for j in range(4)] for i in range(4)]
        for a in range(1,field.q):
            for rp in PERMS:
                for cp in PERMS:
                    key=tuple(field.scalar.MUL[a][base[rp[i]][cp[j]]] for i in range(4) for j in range(4))
                    if best is None or key<best:best=key
    assert best is not None
    return best


def structure(m, field):
    candidates=[]
    for a in range(1,field.q):
        for p in PERMS:
            r=sub_scalar_perm(m,a,p,field);rk=rank_matrix(r,field)
            if rk <= 1:
                factor=factor_rank_one(r,field) if rk==1 else None
                sparsity=(sum(x!=0 for x in factor[0])+sum(x!=0 for x in factor[1])) if factor else 0
                candidates.append((rk,sparsity,a,p,r,factor))
    if not candidates:return {"kind":"not_scalar_permutation_plus_rank_one"}
    rk,_,a,p,r,factor=min(candidates,key=lambda z:(z[0],z[1],z[2],z[3]))
    if rk==0:return {"kind":"scalar_permutation","scalar":a,"permutation":list(p)}
    u,w=factor
    return {"kind":"scalar_permutation_plus_rank_one","scalar":a,"permutation":list(p),
            "u":u,"w":w,"u_support":sum(x!=0 for x in u),"w_support":sum(x!=0 for x in w)}


def good_record(m, field):
    good=scan.scalar_good_list(m,field)
    assert len(good)==6
    return [{"permutation":list(p),"cycle_type":list(scan.cycle_type(p))} for p in good]


def payload(q,mode,matrices,metadata):
    field=scan.BatchField(q)
    unique=sorted(set(matrices))
    classes={}
    records=[]
    for m in unique:
        key=canonical_full(m,field)
        classes.setdefault(key,[]).append(m)
        records.append({"matrix":rows(m),"rank_A_minus_I":scan.matrix_rank_minus_identity(m,field),
                        "good":good_record(m,field)})
    class_rows=[]
    for key,members in sorted(classes.items()):
        ctypes=Counter(tuple(x["cycle_type"]) for x in good_record(key,field))
        class_rows.append({"canonical_matrix":rows(key),"members":len(members),
                           "structure":structure(key,field),
                           "good_cycle_type_histogram":{"-".join(map(str,k)):v for k,v in sorted(ctypes.items())}})
    return {"field":f"GF({q})","mode":mode,"metadata":metadata,"minimizer_count":len(unique),
            "full_symmetry_class_count":len(class_rows),"full_symmetry_classes":class_rows,
            "minimizers":records}


def save(name,data):
    path=HERE/f"result_{name}.json"
    path.write_text(json.dumps(data,indent=2,sort_keys=True)+"\n")
    print(f"RESULT name={name} minimizers={data['minimizer_count']} classes={data['full_symmetry_class_count']}")
    print(f"DONE output={path}")


def exhaustive_f2():
    field=scan.BatchField(2);started=time.monotonic();hist=Counter();mins=[];scanned=0
    for lo in range(0,2**16,8192):
        codes=np.arange(lo,min(lo+8192,2**16),dtype=np.int64)
        mats=scan.decode_codes(codes,16,2).reshape(-1,4,4)
        mats=mats[field.rank_batch(mats)==4]
        g=scan.g_batch(mats,field);scanned+=len(mats);hist.update(map(int,g.tolist()))
        mins.extend(tuple(map(int,m.reshape(16))) for m in mats[g==6])
    return payload(2,"exhaustive_GL4",mins,{"invertible_scanned":scanned,"g_histogram":dict(sorted(hist.items())),
                                           "elapsed_seconds":time.monotonic()-started})


def exhaustive_f3():
    result,mins=scan.scan_exhaustive_f3()
    return payload(3,"exhaustive_rank_le_2",mins,result)


def random_rank2(q,target,seed):
    result,mins=scan.random_rank2_scan(q,target,seed)
    eq=mins if result["minimum_g"]==6 else []
    return payload(q,"random_distinct_invertible_rank_2",eq,result)


def rank1_scan(q,target=None,seed=0):
    field=scan.BatchField(q);ident=np.eye(4,dtype=np.uint8);lines=scan.rref_subspaces(q,1)
    total=len(lines)*(q**4-1);hist=Counter();mins=[];scanned=0;started=time.monotonic()
    if target is None:
        keys=np.arange(total,dtype=np.int64)
    else:
        rng=np.random.default_rng(seed);chosen=set()
        while len(chosen)<min(total,target*2):
            chosen.update(map(int,rng.integers(0,total,size=min(100000,total),dtype=np.int64)))
            if len(chosen)>=target*2:break
        keys=np.asarray(sorted(chosen),dtype=np.int64)
    for lo in range(0,len(keys),25000):
        kk=keys[lo:lo+25000];uidx=kk%len(lines);codes=kk//len(lines)+1
        w=scan.decode_codes(codes,4,q).reshape(-1,1,4)
        mats=field.add[ident,field.mm(lines[uidx],w)]
        mats=mats[field.rank_batch(mats)==4]
        if target is not None and scanned+len(mats)>target:mats=mats[:target-scanned]
        if not len(mats):continue
        g=scan.g_batch(mats,field);scanned+=len(mats);hist.update(map(int,g.tolist()))
        mins.extend(tuple(map(int,m.reshape(16))) for m in mats[g==6])
        if target is not None and scanned>=target:break
    return payload(q,"exhaustive_rank_0_1" if target is None else "random_distinct_invertible_rank_1",
                   [IDENT,*mins],{"invertible_rank1_scanned":scanned,"factor_key_population":total,
                                  "target":target,"seed":seed,"g_histogram":dict(sorted(hist.items())),
                                  "elapsed_seconds":time.monotonic()-started})


def controls_payload():
    c=scan.controls()
    # An equality-family representative present in every field.
    for q in (2,3,4,5,7,9):
        f=scan.BatchField(q);z=[0,0,1,f.scalar.NEG[1]];p=(3,2,1,0)
        m=tuple(f.scalar.ADD[int(i==p[j])][f.scalar.MUL[z[i]][z[j]]] for i in range(4) for j in range(4))
        c[f"two_support_GF{q}"]={"matrix":rows(m),"g":len(scan.scalar_good_list(m,f))}
    return c


def refresh_existing():
    """Recompute canonical-class annotations without repeating any scan."""
    refreshed=[]
    for name in ("f2","f3","f4","f5"):
        path=HERE/f"result_{name}.json"
        old=json.loads(path.read_text())
        mats=[flat(record["matrix"]) for record in old["minimizers"]]
        data=payload(int(old["field"][3:-1]),old["mode"],mats,old["metadata"])
        path.write_text(json.dumps(data,indent=2,sort_keys=True)+"\n")
        refreshed.append({"name":name,"minimizers":data["minimizer_count"],
                          "classes":data["full_symmetry_class_count"]})
    print(json.dumps(refreshed,sort_keys=True))
    print("DONE refreshed=f2,f3,f4,f5")


def main():
    ap=argparse.ArgumentParser();ap.add_argument("mode",choices=("f2","f3","f4","f5","f7rank1","f7rank2","f9rank1","controls","refresh"));a=ap.parse_args()
    if a.mode=="f2":save("f2",exhaustive_f2())
    elif a.mode=="f3":save("f3",exhaustive_f3())
    elif a.mode=="f4":save("f4",random_rank2(4,1_000_000,1695404))
    elif a.mode=="f5":save("f5",random_rank2(5,1_000_000,1695405))
    elif a.mode=="f7rank1":save("f7rank1",rank1_scan(7))
    elif a.mode=="f7rank2":save("f7rank2",random_rank2(7,2_177_199,1695717))
    elif a.mode=="f9rank1":save("f9rank1",rank1_scan(9,1_000_000,1695909))
    elif a.mode=="controls":
        data=controls_payload();path=HERE/"result_controls.json";path.write_text(json.dumps(data,indent=2,sort_keys=True)+"\n")
        print(json.dumps(data,sort_keys=True));print(f"DONE output={path}")
    else:refresh_existing()


if __name__=="__main__":main()
