#!/usr/bin/env python3
"""Artifact replay and report generator for K6-N5J."""
from __future__ import annotations
import hashlib, json, re
from pathlib import Path

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[2]

def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def unit(p):
    body=''.join(x for x in p.read_text(errors='replace').splitlines() if not x.startswith('#'))
    return re.sub(r'\s+','',body).startswith('[1]')
def primes(limit):
    out=[]
    for n in range(2,limit):
        if all(n%p for p in out if p*p<=n): out.append(n)
    return out

def check_result(r, expected_unit=True):
    src,basis=(ROOT/Path(r['source']),ROOT/Path(r['basis']))
    assert all(p.exists() for p in (src,basis))
    lines=src.read_text().splitlines(); assert int(lines[1])==r['characteristic']
    assert len(lines[0].split(','))==len(r['variables'])
    if expected_unit: assert r['generator_count']==74
    assert r['child_returncode']==r['wrapper_returncode']==0 and not r['capped']
    assert r['swap_used_mib_at_start']<10240 and r['msolve_version']=='0.10.1'
    assert unit(basis)==r['unit']==expected_unit

def main():
    bundle=json.loads((HERE/'j5_polynomials.json').read_text())
    assert (bundle['total_determinants'],bundle['identically_zero'],bundle['nonzero'],
            bundle['max_total_degree'],bundle['distinct_nonzero_polynomials'])==(120,46,74,8,74)
    state=json.loads((HERE/'prime_results.json').read_text())
    expected=[3,2,5,7,0]+[p for p in primes(2000) if p not in (2,3,5,7)]
    assert state['order']==expected and [r['characteristic'] for r in state['results']]==expected
    assert len(expected)==304 and state['exhaustive'] and state['all_unit'] and not state['blocked_reason']
    for r in state['results']: check_result(r)
    controls=json.loads((HERE/'controls.json').read_text()); assert controls['passed']
    for name in ('pivot_control','toy_control'):
        r=controls[name]['result']; check_result(r,False); assert r['status']=='NONUNIT'
    witness=controls['realised_pattern_control']['witness_result']; check_result(witness,False)
    raw=controls['realised_pattern_control']['raw_result']
    assert raw['status'] in ('UNRESOLVED-due-to-load','UNRESOLVED-due-to-load') and raw['capped']
    audit=json.loads((HERE/'finite_audit.json').read_text())
    assert audit['verified'] and [(a['characteristic'],a['rank_one_invertible_matrices'],a['failed'])
                                 for a in audit['audits']]==[(2,465,0),(3,19481,0)]
    rows=state['results']; report={
      'polynomials':{'sha256':sha(HERE/'j5_polynomials.json'),'total':120,'zero':46,'nonzero':74,'max_degree':8},
      'prime_scan':{'sha256':sha(HERE/'prime_results.json'),'runs':304,'unit':304,
        'sum_seconds':round(sum(r['seconds'] for r in rows),3),
        'max_seconds':max(r['seconds'] for r in rows),'max_peak_rss_kib':max(r['peak_rss_kib'] for r in rows),
        'swap_range_mib':[min(r['swap_used_mib_at_start'] for r in rows),max(r['swap_used_mib_at_start'] for r in rows)]},
      'controls':{'sha256':sha(HERE/'controls.json'),'verified':True},
      'finite_audit':{'sha256':sha(HERE/'finite_audit.json'),'verified':True},'verified':True}
    (HERE/'verification.json').write_text(json.dumps(report,indent=2)+'\n')
    table=['| field | status | seconds | peak RSS KiB | launch swap MiB |','|---:|---|---:|---:|---:|']
    for r in rows:
        field='Q' if r['characteristic']==0 else f"GF({r['characteristic']})"
        table.append(f"| {field} | {r['status']} | {r['seconds']:.3f} | {r['peak_rss_kib']:,} | {r['swap_used_mib_at_start']:.2f} |")
    md=f'''# K6-N5J — Krylov-determinant ideal J5

## Status ledger

- **COMPUTED:** the independently constructed family has 120 determinants: 46 identically zero and 74 distinct nonzero, of maximum total degree 8.
- **COMPUTED:** msolve 0.10.1 returned `[1]` over Q and every one of the 303 prime fields below 2000 (304 fields total).
- **VERIFIED:** the pivot-only and toy controls are NONUNIT. The raw realised-pattern ideal hit the 2.5-GB cap; exact evaluation gives its concrete zero, and the larger ideal obtained by adjoining that point's eight linear equations is NONUNIT, which rigorously certifies the raw subideal NONUNIT.
- **VERIFIED:** exhaustive direct audits cover all 465 normalized exact-rank-one invertible matrices over GF(2) and all 19,481 over GF(3); every matrix has a cyclic permutation product.

Nothing was published outward and nothing is labelled SOLVED. No lake build, CP-SAT, or Singular was used. Every msolve launch was sequential, preceded by the `< 10240 MiB` swap gate, and used the stricter user-specified 600-second cap.

## Commands and aggregate resources

```text
python3 encoders/line/run_capped.py --wall 600 --mem 2500000 --log FIELD.log -- msolve -g 2 -v 1 -t 1 -f FIELD.ms -o FIELD.gb
```

msolve version: `0.10.1`; options: `-g 2 -v 1 -t 1`. Main-scan wrapper time totals {report['prime_scan']['sum_seconds']:.3f} s. Maximum node time is {report['prime_scan']['max_seconds']:.3f} s; maximum recorded RSS is {report['prime_scan']['max_peak_rss_kib']:,} KiB; launch swap ranges from {report['prime_scan']['swap_range_mib'][0]:.2f} to {report['prime_scan']['swap_range_mib'][1]:.2f} MiB. No main scan capped.

## Per-field results

{chr(10).join(table)}

## Controls and finite audit

The `j=i` control has 6 nonzero generators and is NONUNIT. The realised GF(3) point has `x=(1,1,1,2)`, `y=(0,0,0,0)`, 60 nonzero determinants and 14 nonzero vanishing generators. Its raw msolve attempt hit the resident-memory cap at 2,602,864 KiB; the exact point evaluation plus NONUNIT witness-containing ideal proves the required result without relaxing the cap. The toy `<xy,1-tx>` is NONUNIT.

The independent audit normalizes the first nonzero coordinate of `v` to 1, enumerates every admissible nonzero `u`, checks `1+v^T u != 0`, and tests cyclicity by the rank of `I,B,...,B^4` for all permutation products until a witness is found. It reports zero failures in GF(2) and GF(3).

Principal artifacts: `n5j_encoder.py`, `n5j_runner.py`, `n5j_controls.py`, `n5j_finite_audit.py`, `n5j_verify.py`, `j5_polynomials.json`, `prime_results.json`, `controls.json`, `finite_audit.json`, `verification.json`, and `certificates/`.

DONE-n5j
'''
    (HERE/'REPORT.md').write_text(md)
    print(json.dumps(report,indent=2))

if __name__=='__main__': main()
