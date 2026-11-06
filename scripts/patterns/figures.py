"""Figures for the patterns paper (docs/patterns-paper/fig_*.pdf). Static print figures; palette from the dataviz
reference (categorical blue #2a78d6, orange #eb6834, aqua #1baf7a; sequential blue ramp; recessive grey axes)."""
import json, os, sys, glob, collections
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from mpl_toolkits.mplot3d.art3d import Poly3DCollection, Line3DCollection
from matplotlib.colors import LinearSegmentedColormap
ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
sys.path.insert(0, os.path.join(ROOT, 'scripts', 'patterns'))
from features import SOL, quat_to_R
OUT = os.path.join(ROOT, 'docs', 'patterns-paper')
BLUE, ORANGE, AQUA = '#2a78d6', '#eb6834', '#1baf7a'
INK, INK2, GRID, SURF = '#0b0b0b', '#52514e', '#d9d8d4', '#fcfcfb'
SEQ = LinearSegmentedColormap.from_list('seq', ['#cde2fb', '#86b6ef', '#3987e5', '#1c5cab', '#0d366b'])
plt.rcParams.update({'font.size': 9, 'axes.edgecolor': INK2, 'axes.labelcolor': INK, 'xtick.color': INK2,
                     'ytick.color': INK2, 'axes.spines.top': False, 'axes.spines.right': False,
                     'axes.linewidth': 0.6, 'figure.facecolor': 'white', 'savefig.facecolor': 'white',
                     'font.family': 'DejaVu Sans'})
ST = json.load(open(os.path.join(ROOT, 'docs', 'patterns', 'stats.json')))


def save(fig, name):
    fig.savefig(os.path.join(OUT, name + '.pdf'), bbox_inches='tight')
    fig.savefig(os.path.join(OUT, name + '.png'), dpi=200, bbox_inches='tight')
    plt.close(fig)


def fig_lineage():
    L = ST['lineage']
    groups = [('Deletion (n+1 minus a piece)', ['monotone', 'descend']),
              ('Insertion (n-1 plus a piece)', ['ascend', 'reinsert']),
              ('Soft-to-rigid hops and kicks', ['hop', 'perturb', 'tighten', 'largen-study']),
              ('Fresh and symmetric starts', ['fresh', 'symfresh', 'bench-symfresh', 'bench-fresh', 'bench-hop',
                                              'bench-symfresh25', 'bench-symchain']),
              ('Lattice cuts', ['latcut']), ('Composition (nested)', ['compose']),
              ('Contributed or published', ['community', 'literature', 'import', 'construction']),
              ('No lineage recorded', ['none'])]
    vals = [(g, sum(L.get(m, 0) for m in ms)) for g, ms in groups]
    vals = [v for v in vals if v[1] > 0][::-1]
    fig, ax = plt.subplots(figsize=(6.2, 2.9))
    y = np.arange(len(vals))
    ax.barh(y, [v[1] for v in vals], height=0.62, color=BLUE)
    for yi, (g, v) in zip(y, vals): ax.text(v + 60, yi, f'{v:,}', va='center', color=INK, fontsize=8)
    ax.set_yticks(y); ax.set_yticklabels([v[0] for v in vals], color=INK)
    ax.set_xlabel('records'); ax.xaxis.grid(True, color=GRID, lw=0.5); ax.set_axisbelow(True)
    ax.set_xlim(0, max(v[1] for v in vals) * 1.15)
    ax.set_title(f'How the {ST["records"]:,} records were produced (last move of their lineage)', fontsize=9, color=INK, loc='left')
    save(fig, 'fig_lineage')


def fig_sym_orient():
    F = ST['features3d']
    fig, axs = plt.subplots(1, 2, figsize=(6.6, 2.5))
    so = {int(k): v for k, v in F['symmetry_order'].items()}
    ks = sorted(so); ax = axs[0]
    ax.bar(range(len(ks)), [so[k] for k in ks], color=BLUE, width=0.62)
    ax.set_yscale('log'); ax.set_xticks(range(len(ks))); ax.set_xticklabels([str(k) for k in ks], fontsize=7)
    ax.set_xlabel('order of the configuration symmetry group'); ax.set_ylabel('3D records')
    ax.yaxis.grid(True, color=GRID, lw=0.5); ax.set_axisbelow(True)
    ax.set_title('(a) Symmetry', fontsize=9, loc='left', color=INK)
    oc = {int(k): v for k, v in F['orientation_classes'].items()}
    ks = sorted(oc); ax = axs[1]
    ax.bar(range(len(ks)), [oc[k] for k in ks], color=BLUE, width=0.62)
    ax.set_xticks(range(len(ks))); ax.set_xticklabels([str(k) if k < 12 else '12+' for k in ks], fontsize=7)
    ax.set_xlabel('orientation classes'); ax.yaxis.grid(True, color=GRID, lw=0.5); ax.set_axisbelow(True)
    ax.set_title('(b) Orientation classes', fontsize=9, loc='left', color=INK)
    fig.tight_layout(); save(fig, 'fig_sym_orient')


def staircase(fam):
    pts = []
    for f in glob.glob(os.path.join(ROOT, 'records', fam, f'{fam}_n*.json')):
        d = json.load(open(f)); pts.append((d['n'], d['s_full']))
    return sorted(pts)


def fig_windows():
    fig, axs = plt.subplots(1, 2, figsize=(6.6, 2.6), sharey=False)
    for ax, fam, title, wins in ((axs[0], 'rdoinrdo', '(a) Rhombic dodecahedra (FCC windows)', {3: 19, 4: 44, 5: 93}),
                                 (axs[1], 'tcuintcu', '(b) Truncated cubes (cubic windows)', {4: 56})):
        P = staircase(fam)
        ax.plot([p[0] for p in P], [p[1] for p in P], color=BLUE, lw=1.6, drawstyle='steps-post')
        for s, n in wins.items():
            ax.plot([n], [s], 'o', ms=5, color=ORANGE, mec='white', mew=1.2, zorder=5)
            ax.annotate(f'{n} at {s}', (n, s), xytext=(4, -11), textcoords='offset points', fontsize=7.5, color=INK)
        ax.set_xlabel('n'); ax.yaxis.grid(True, color=GRID, lw=0.5); ax.set_axisbelow(True)
        ax.set_title(title, fontsize=9, loc='left', color=INK)
    axs[0].set_ylabel('record scale s(n)')
    fig.tight_layout(); save(fig, 'fig_windows')


def fig_inherit(fam='cubincub', kmax=40, gap=6):
    I = json.load(open(os.path.join(ROOT, 'docs', 'patterns', 'inherit3d.json'))).get(fam, {})
    M = np.full((gap, kmax - 1), np.nan)
    for key, v in I.items():
        k, N = map(int, key.split('-'))
        if k <= kmax and 1 <= N - k <= gap: M[N - k - 1, k - 2] = v
    fig, ax = plt.subplots(figsize=(6.6, 1.9))
    im = ax.imshow(M, aspect='auto', cmap=SEQ, vmin=0, vmax=1, origin='lower', extent=(1.5, kmax + 0.5, 0.5, gap + 0.5))
    ax.set_xlabel('k'); ax.set_ylabel('N - k'); ax.set_yticks(range(1, gap + 1))
    cb = fig.colorbar(im, ax=ax, fraction=0.03, pad=0.01); cb.set_label('inherited fraction', fontsize=8)
    cb.outline.set_linewidth(0.4)
    ax.set_title(f'Subset inheritance f(k, N) in {fam}: the share of record k found rigidly inside record N',
                 fontsize=9, loc='left', color=INK)
    save(fig, f'fig_inherit_{fam}')


def faces_world(piece, c, R):
    V = np.array(SOL[piece]['V'], float); W = c + V @ R.T
    return [W[f] for f in SOL[piece]['faces']]


def render(ax, rid, highlight=None, colors=None, title=None, elev=22, azim=35):
    fam = rid.rsplit('_n', 1)[0]
    d = json.load(open(os.path.join(ROOT, 'records', fam, rid + '.json')))
    P = np.array(d['pieces'], float); piece, cont = d['piece'], d['container']
    light = np.array([0.4, -0.5, 0.75]); light /= np.linalg.norm(light)
    allpts = []
    for i, p in enumerate(P):
        R = quat_to_R(p[3:7]); fs = faces_world(piece, p[:3], R)
        base = np.array(matplotlib.colors.to_rgb(colors[i] if colors else (ORANGE if highlight and i in highlight else BLUE)))
        cols = []
        for f in fs:
            nrm = np.cross(f[1] - f[0], f[2] - f[0]); nrm /= np.linalg.norm(nrm) + 1e-12
            if np.dot(nrm, f.mean(0) - p[:3]) < 0: nrm = -nrm
            sh = 0.55 + 0.45 * max(0.0, float(nrm @ light))
            cols.append(np.clip(base * sh + (1 - sh) * 0.15, 0, 1))
        alpha = 0.95 if (highlight is None or i in highlight) else 0.18
        pc = Poly3DCollection(fs, facecolors=cols, edgecolors=(0.15, 0.15, 0.15, 0.6 * alpha), linewidths=0.25, alpha=alpha)
        ax.add_collection3d(pc); allpts.append(np.concatenate(fs))
    CV = np.array(SOL[cont]['V'], float) * d['s_full']
    segs = [[CV[i], CV[j]] for i, j in SOL[cont]['edges']]
    ax.add_collection3d(Line3DCollection(segs, colors=INK2, linewidths=0.5))
    X = np.concatenate(allpts + [CV]); m = X.mean(0); r = np.abs(X - m).max()
    ax.set_xlim(m[0] - r, m[0] + r); ax.set_ylim(m[1] - r, m[1] + r); ax.set_zlim(m[2] - r, m[2] + r)
    ax.set_box_aspect((1, 1, 1)); ax.view_init(elev=elev, azim=azim); ax.set_axis_off()
    if title: ax.set_title(title, fontsize=8, color=INK, pad=-4)


def fig_gallery():
    fig = plt.figure(figsize=(7.0, 4.9))
    items = [('rdoinrdo_n19', 'FCC shell: 19 = 1 + 12 + 6\nrhombic dodecahedra, s = 3'),
             ('tcuintcu_n56', 'Cartesian shell: 56 = 4³ − 2³\ntruncated cubes, s = 4'),
             ('kttinktt_n16', 'Recursion: 16 = 4²\ntriakis tetrahedra, s = (5/3)²'),
             ('tteintte_n71', 'Two-orientation window: 71 = 40 + 31\ntruncated tetrahedra, s = 13/3'),
             ('cubincub_n27', 'Lattice tiling: 27 = 3³\ncubes, s = 3 (optimal)'),
             ('octincub_n02', 'Proven optimal (n = 2): octahedra\nin a cube, s = √2')]
    for k, (rid, t) in enumerate(items):
        ax = fig.add_subplot(2, 3, k + 1, projection='3d')
        cols = None
        if rid == 'tteintte_n71':
            F = {x['record_id']: x for x in json.load(open(os.path.join(ROOT, 'docs', 'patterns', 'features3d.json')))}
            d = json.load(open(os.path.join(ROOT, 'records', 'tteintte', rid + '.json')))
            P = np.array(d['pieces']); R = [quat_to_R(q) for q in P[:, 3:7]]
            sys.path.insert(0, os.path.join(ROOT, 'scripts')); import symmetry
            from features import orient_classes
            G = [g for g in symmetry.sym_group('truncated_tetrahedron') if np.linalg.det(g) > 0]
            oc = orient_classes(R, G, 1e-3); cols = [None] * len(P)
            for ci, grp in enumerate(oc):
                for i in grp: cols[i] = BLUE if ci == 0 else ORANGE
        render(ax, rid, colors=cols, title=t)
    fig.subplots_adjust(wspace=0.0, hspace=0.12)
    save(fig, 'fig_gallery')


def fig_arrow(src='ap4inap4_n15', sub=(4, 6, 12), res=None):
    fig = plt.figure(figsize=(6.6, 2.8))
    ax = fig.add_subplot(1, 2, 1, projection='3d')
    render(ax, src, highlight=set(sub), title=f'Source: record n = 15 (s = 3.0118); keep pieces {list(sub)}')
    ax = fig.add_subplot(1, 2, 2, projection='3d')
    if res:
        w = json.load(open(res))
        tmp = {'pieces': [[*c, *exact_q] for c, exact_q in zip(w['C'], w['Q'])], 's_full': w['s'],
               'piece': w['piece'], 'container': w['container']}
        path = os.path.join(OUT, '_arrow_tmp.json'); os.makedirs(os.path.join(ROOT, 'records', '_tmp'), exist_ok=True)
        json.dump(tmp, open(os.path.join(ROOT, 'records', '_tmp', '_tmp_n03.json'), 'w'))
        render(ax, '_tmp_n03', colors=[ORANGE] * 3, title=f'After F then P: s = {w["s"]:.9f}')
        os.remove(os.path.join(ROOT, 'records', '_tmp', '_tmp_n03.json')); os.rmdir(os.path.join(ROOT, 'records', '_tmp'))
    save(fig, 'fig_arrow')


if __name__ == '__main__':
    os.makedirs(OUT, exist_ok=True)
    which = sys.argv[1:] or ['lineage', 'sym', 'windows', 'inherit', 'gallery']
    if 'lineage' in which: fig_lineage()
    if 'sym' in which: fig_sym_orient()
    if 'windows' in which: fig_windows()
    if 'inherit' in which: fig_inherit('cubincub'); fig_inherit('rdoinrdo')
    if 'gallery' in which: fig_gallery()
    if 'arrow' in which: fig_arrow(res=sys.argv[-1] if sys.argv[-1].endswith('.json') else None)
    print('ok')
