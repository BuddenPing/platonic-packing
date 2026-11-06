import json, sympy as sp
d = json.load(open('oct_bands.json'))
def q(x): 
    x = sp.Rational(x)
    return f'({x.p} / {x.q} : ℝ)' if x.q != 1 else f'({x.p} : ℝ)'
def term(name, v):
    # nonneg proof terms; base facts: hrl : rl ≤ r, hrh : r ≤ rh, hG : 0 ≤ G, h1 : lo ≤ r^2, h2 : r^2 ≤ hi
    base = {'L': 'sub_nonneg.mpr hrl', 'U': 'sub_nonneg.mpr hrh', 'G': 'hG', 'H': 'sub_nonneg.mpr h2', 'Lo': 'sub_nonneg.mpr h1',
            'D': 'sq_nonneg (r - 1)'}
    if name == '1': return None
    if name.startswith('sq:'): return f'sq_nonneg (r - {q(name[3:])})'
    m = None
    for pre in ['LUsq:', 'Dsq:']:
        if name.startswith(pre):
            c = q(name[len(pre):])
            if pre == 'LUsq:': return f'mul_nonneg (mul_nonneg ({base["L"]}) ({base["U"]})) (sq_nonneg (r - {c}))'
            return f'mul_nonneg (sq_nonneg (r - 1)) (sq_nonneg (r - {c}))'
    if 'sq:' in name:
        a, c = name.split('sq:'); return f'mul_nonneg ({base[a]}) (sq_nonneg (r - {q(c)}))'
    # products of base names (greedy tokenization)
    toks = []; s = name
    while s:
        for t in ['Lo', 'L', 'U', 'G', 'H', 'D']:
            if s.startswith(t): toks.append(t); s = s[len(t):]; break
        else: raise ValueError(name)
    e = f'({base[toks[0]]})'
    for t in toks[1:]: e = f'(mul_nonneg {e} ({base[t]}))'
    return e
out = []
for idx, (k, v) in enumerate(d.items()):
    name = 'tangent' if k == 'tangent' else f'band{idx}'
    a, b, lo, hi, rl, rh = (q(v[x]) for x in ('a', 'b', 'lo', 'hi', 'rl', 'rh'))
    Lx = f'(r - {a} - {b} * r ^ 2)'
    hints = [h for h in (term(t, v) for t in v['terms']) if h]
    rl_proof = 'hr' if sp.Rational(v['rl']) == 0 else f'by nlinarith'
    out.append(f'''theorem oct_{name} (r m : ℝ) (hr : 0 ≤ r) (hm : r / 3 ≤ m) (hQ : 1 ≤ 6 * m ^ 2 - 4 * m * r + r ^ 2)
    (h1 : {lo} ≤ r ^ 2) (h2 : r ^ 2 ≤ {hi}) : r * (1 - m) ≤ {a} + {b} * r ^ 2 := by
  by_contra hneg
  push Not at hneg
  have hrl : {rl} ≤ r := {'by linarith' if sp.Rational(v['rl']) == 0 else 'by nlinarith'}
  have hrh : r ≤ {rh} := by nlinarith
  have hz3 : r ^ 2 / 3 ≤ r * m := by nlinarith
  have hq : 0 ≤ 6 * (r * m) ^ 2 - 4 * r ^ 2 * (r * m) + r ^ 4 - r ^ 2 := by
    have := mul_nonneg (sq_nonneg r) (sub_nonneg.mpr hQ); nlinarith
  have hG : 0 ≤ {Lx} - r ^ 2 / 3 := by nlinarith
  have hP : 6 * {Lx} ^ 2 - 4 * r ^ 2 * {Lx} + r ^ 4 - r ^ 2 ≤ 0 := by
    nlinarith [{", ".join(hints)}]
  have key : 0 < ({Lx} - r * m) * (6 * ({Lx} + r * m) - 4 * r ^ 2) := mul_pos (by linarith) (by nlinarith)
  nlinarith [key, hq, hP]
''')
open('oct_bands.lean', 'w').write('\n'.join(out))
print('\n'.join(out)[:3000])
