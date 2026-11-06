"""Catalogue-wide pattern statistics for the patterns paper (docs/patterns/stats.json).

Reads every record (records/*/*_nNN.json), the 3D structural features (docs/patterns/features3d.json) and subset
inheritance (docs/patterns/inherit3d.json) and tabulates: construction lineage (search.move), plateaus
(maximal runs of equal s_full in n), frozen-subset inheritance, composite records s(nm) = s(n) s(m), lattice
windows at rational scales, orientation classes, configuration symmetry, layering and closed-form fields.
"""
import json, os, glob, re, collections
from fractions import Fraction
ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))


def records():
    out = {}
    for f in glob.glob(os.path.join(ROOT, 'records', '*', '*_n*.json')):
        try: d = json.load(open(f))
        except Exception: continue
        if not isinstance(d, dict) or 'pieces' not in d or 's_full' not in d: continue
        out[d.get('record_id') or os.path.basename(f)[:-5]] = d
    return out


def field(c):
    if not c: return None
    has = lambda t: t in c
    if '√' not in c and 'φ' not in c: return 'Q'
    nested = bool(re.search(r'√\(', c))
    keys = [k for k, t in (('√2', '√2'), ('√3', '√3'), ('√5', '√5')) if has(t)] + (['φ'] if has('φ') else [])
    other = bool(re.search(r'√(\d+)', c) and any(m not in ('2', '3', '5') for m in re.findall(r'√(\d+)', c)))
    tag = 'Q(' + ','.join(keys) + ')' if keys else 'Q(other)'
    if nested: tag += ' nested'
    elif other: tag += ' +other'
    return tag


def main():
    R = records()
    fam = collections.defaultdict(dict)
    for rid, d in R.items(): fam[rid.rsplit('_n', 1)[0]][d['n']] = d
    st = {'records': len(R), 'families': len(fam),
          'dims': dict(collections.Counter(d.get('dim', 3) for d in R.values()))}
    st['lineage'] = dict(collections.Counter((d.get('search') or {}).get('move') or 'none' for d in R.values()).most_common())
    st['found_by'] = dict(collections.Counter(re.split(r' \(', d.get('found_by', ''))[0] for d in R.values()).most_common(12))
    # plateaus
    plat = []; in_plat = 0
    for f, by in fam.items():
        ns = sorted(by); i = 0
        while i < len(ns):
            j = i
            while j + 1 < len(ns) and ns[j + 1] == ns[j] + 1 and abs(by[ns[j + 1]]['s_full'] - by[ns[i]]['s_full']) < 1e-9 * by[ns[i]]['s_full']:
                j += 1
            if j > i:
                plat.append((f, ns[i], ns[j], by[ns[i]]['s_full'])); in_plat += j - i + 1
            i = j + 1
    plat.sort(key=lambda x: -(x[2] - x[1]))
    st['plateaus'] = {'count': len(plat), 'records_in_plateaus': in_plat, 'longest': plat[:15]}
    # composites
    comp = []
    for f, by in fam.items():
        a = f.split('in')
        if len(a) != 2 or a[0] != a[1]: continue
        for n in by:
            for m in by:
                if 2 <= n <= m and n * m in by:
                    t = lambda d: d.get('s_tight') or d['s_full']
                    if abs(t(by[n * m]) - t(by[n]) * t(by[m])) < 1e-6 * t(by[n * m]):
                        comp.append((f, n, m, n * m, round(t(by[n * m]), 9)))
    st['composites'] = comp
    st['nested_constructions'] = sorted(rid for rid, d in R.items() if 'nested construction' in d.get('found_by', '')
                                        or (d.get('search') or {}).get('move') == 'compose')
    # closed forms
    cf = collections.Counter(field(d.get('closed_form_conjecture')) for d in R.values() if d.get('closed_form_conjecture'))
    st['closed_forms'] = {'count': sum(cf.values()), 'fields': dict(cf.most_common())}
    # features
    fpath = os.path.join(ROOT, 'docs', 'patterns', 'features3d.json')
    if os.path.exists(fpath):
        F = json.load(open(fpath))
        st['features3d'] = {'records': len(F)}
        st['features3d']['symmetry_order'] = dict(sorted(collections.Counter(x['sym']['order'] for x in F).items()))
        st['features3d']['orientation_classes'] = dict(sorted(collections.Counter(min(len(x['orient']), 12) for x in F).items()))
        lat = [x for x in F if x['lattice'] and all((l or {}).get('lattice') for l in x['lattice'])
               and sum(len([1]) for _ in x['orient']) <= 4 and x['n'] >= 4 and len(x['orient']) <= 4]
        st['features3d']['lattice_windows'] = len(lat)
        st['features3d']['lattice_single_orientation'] = sum(1 for x in lat if len(x['orient']) == 1)
        rat = [x for x in lat if abs(float(Fraction(x['s']).limit_denominator(12)) - x['s']) < 2e-6]
        st['features3d']['lattice_rational_scale'] = len(rat)
        st['features3d']['lattice_by_family'] = dict(collections.Counter(x['record_id'].rsplit('_n', 1)[0] for x in lat).most_common())
        lay = collections.Counter()
        for x in F:
            if x['layers'] and x['n'] >= 8:
                L = len(x['layers']['sizes']); lay['<= n^(1/3)' if L <= round(x['n'] ** (1 / 3)) else '<= n^(1/2)' if L <= x['n'] ** 0.5 else 'more'] += 1
        st['features3d']['layering'] = dict(lay)
        two = [x for x in F if len(x['orient']) == 2 and x['n'] >= 8]
        st['features3d']['two_orientation_examples'] = [(x['record_id'], x['orient'], round(x['s'], 7)) for x in two[:20]]
        st['features3d']['symmetric_examples'] = [(x['record_id'], x['sym']['order'], round(x['s'], 7))
                                                  for x in sorted(F, key=lambda x: -x['sym']['order'])[:25]]
    ipath = os.path.join(ROOT, 'docs', 'patterns', 'inherit3d.json')
    if os.path.exists(ipath):
        I = json.load(open(ipath))
        cons = [(f, k) for f, r in I.items() for k, v in r.items() if int(k.split('-')[1]) - int(k.split('-')[0]) == 1]
        full = [(f, k) for f, r in I.items() for k, v in r.items() if v >= 1.0]
        st['inheritance'] = {
            'families': len(I), 'pairs': sum(len(r) for r in I.values()),
            'consecutive_pairs': len(cons),
            'consecutive_frozen': sum(1 for f, k in cons if I[f][k] >= 1.0),
            'frozen_any_gap': len(full),
            'partial_ge_0.8': sum(1 for f, r in I.items() for k, v in r.items() if 0.8 <= v < 1.0),
            'by_gap': {g: (sum(1 for f, r in I.items() for k, v in r.items() if int(k.split('-')[1]) - int(k.split('-')[0]) == g and v >= 1.0),
                           sum(1 for f, r in I.items() for k in r if int(k.split('-')[1]) - int(k.split('-')[0]) == g))
                       for g in range(1, 7)},
            'frozen_by_family': dict(collections.Counter(f for f, k in full).most_common(20))}
    json.dump(st, open(os.path.join(ROOT, 'docs', 'patterns', 'stats.json'), 'w'), indent=1, ensure_ascii=False)
    print(json.dumps({k: v for k, v in st.items() if k not in ('composites',)}, ensure_ascii=False)[:3000])


if __name__ == '__main__':
    main()
