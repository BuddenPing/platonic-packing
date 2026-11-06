"""Put arrow results (scripts/patterns/arrows_*.py, record units) into the search archive state/best, crediting
PingYou Ltd, who introduced the arrows and first reported these values (6 Nov 2026). Only strict improvements over
the archived best are imported; the publisher (scripts/publish_families.py) then builds the records, with clearance
and exact certificates, as for every other record.

Usage: python3 scripts/patterns/import_arrows.py FAMILY DIR [--apply]
"""
import json, os, sys, glob, time
import numpy as np
ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
sys.path.insert(0, os.path.join(ROOT, 'src')); sys.path.insert(0, os.path.join(ROOT, 'scripts'))
import exact, fastslp
from engine import _read, _write, _path

fam, d = sys.argv[1], sys.argv[2]; apply = '--apply' in sys.argv
for f in sorted(glob.glob(os.path.join(d, f'{fam}_n*.json'))):
    w = json.load(open(f)); n = w['n']
    pb = exact.Problem(w['piece'], w['container'])
    C = np.array(w['C'], float) * pb.edge
    R = [exact.quat_to_R(np.array(q) / np.linalg.norm(q)) for q in w['Q']]
    L, _, C2 = fastslp.certify_fast(pb, C, R)            # re-legalize in internal units
    s = pb.s_of_L(L)
    case = _read(_path('best', fam, n))
    cur = case['best']['s'] if case and case.get('best') else None
    win = cur is None or s < cur - 1e-9
    print(f'{fam} n={n}: arrow {s:.12f}  archive {cur}  {"IMPORT" if win else "skip"}  ({w.get("arrow")})')
    if win and apply:
        case['best'] = {'s': s, 'C': np.asarray(C2).tolist(), 'Q': [exact.R_to_quat(r).tolist() for r in R],
                        'src': {'move': 'arrow', 'lineage': 'PingYou Ltd', 'arrow': w.get('arrow'),
                                'reported': '2026-11-06', 'reproduced_from_catalogue': True,
                                'script': 'scripts/patterns/arrows_search.py, arrows_kick.py', 'raw': s},
                        't': time.time(), 'tightened': True}
        case['stats']['improvements'] = case['stats'].get('improvements', 0) + 1
        _write(_path('best', fam, n), case)
