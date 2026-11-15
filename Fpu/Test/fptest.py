#!/usr/bin/env python3
"""Differential test of FpCore against an exact-rational reference.

Usage: fptest.py <e> <f> <ncases> <seed> [xlen]          -- fpuCompute, all single-format ops
       fptest.py cvt <e1> <f1> <e2> <f2> <ncases> <seed>  -- cvtFF from (e1,f1) to (e2,f2)
       fptest.py fli <e> <f>                             -- the Zfa FLI constant table
Generates cases, writes a Coq file that evaluates them with vm_compute, runs it, and compares.
"""
import math, os, random, re, subprocess, sys, tempfile
from fractions import Fraction

# Paths relative to this script: <Fpu>/Test/fptest.py, Guru at <Fpu>/../../Guru (as in _CoqProject).
FPU = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
# Exponent mode of FpCore: true = biased (hardware model), false = unbiased reference model.
BM = os.environ.get('FPTEST_BM', 'true')
GURU = os.path.normpath(os.path.join(FPU, '..', '..', 'Guru'))

OPS = dict(ADD=0, SUB=1, MUL=2, DIV=3, SQRT=4, MADD=5, MSUB=6, NMSUB=7, NMADD=8,
           MIN=9, MAX=10, SGNJ=11, SGNJN=12, SGNJX=13,
           CVTWF=14, CVTWUF=15, CVTLF=16, CVTLUF=17, CVTFW=18, CVTFWU=19, CVTFL=20, CVTFLU=21,
           FEQ=22, FLT=23, FLE=24, FCLASS=25,
           # Zfa
           MINM=26, MAXM=27, FLTQ=28, FLEQ=29, FROUND=30, FROUNDNX=31)

# The decoded operation (FpCore.FpOpDK) of each op: family index (position of the family flag)
# and option bits (bit0 negB, bit1 negProd, bit2 negAdd, bit3 isMax, bit4 nanProp, bits5-6 mode,
# bit7 quiet, bit8 unsigned, bit9 wide, bit10 nx).
FAM = dict(add=0, mul=1, fma=2, div=3, sqrt=4, minmax=5, sgnj=6, cmp=7, fclass=8, cvtFI=9, cvtIF=10,
           round=11)
DEC = {0: ('add', 0), 1: ('add', 1), 2: ('mul', 0), 3: ('div', 0), 4: ('sqrt', 0),
       5: ('fma', 0), 6: ('fma', 4), 7: ('fma', 2), 8: ('fma', 6),
       9: ('minmax', 0), 10: ('minmax', 8), 11: ('sgnj', 0), 12: ('sgnj', 32), 13: ('sgnj', 64),
       14: ('cvtFI', 0), 15: ('cvtFI', 256), 16: ('cvtFI', 512), 17: ('cvtFI', 768),
       18: ('cvtIF', 0), 19: ('cvtIF', 256), 20: ('cvtIF', 512), 21: ('cvtIF', 768),
       22: ('cmp', 0), 23: ('cmp', 32), 24: ('cmp', 64), 25: ('fclass', 0),
       26: ('minmax', 16), 27: ('minmax', 24), 28: ('cmp', 32 + 128), 29: ('cmp', 64 + 128),
       30: ('round', 0), 31: ('round', 1024)}
NV, DZ, OF, UF, NX = 16, 8, 4, 2, 1


class Fmt:
    def __init__(s, e, f):
        s.e, s.f = e, f
        s.bias = 2 ** (e - 1) - 1
        s.emin, s.emax = 1 - s.bias, s.bias
        s.w = e + f + 1
        s.sbit = 1 << (e + f)
        s.qnan = (((1 << e) - 1) << f) | (1 << (f - 1))
        s.S = 4 * (s.bias + f) + 16


def cls(F, x):
    s = x >> (F.e + F.f)
    ef = (x >> F.f) & ((1 << F.e) - 1)
    fr = x & ((1 << F.f) - 1)
    if ef == (1 << F.e) - 1:
        if fr == 0:
            return 'inf', s, None
        return ('qnan' if (fr >> (F.f - 1)) & 1 else 'snan'), s, None
    if ef == 0:
        if fr == 0:
            return 'zero', s, Fraction(0)
        return 'fin', s, Fraction(fr) * Fraction(2) ** (F.emin - F.f)
    return 'fin', s, Fraction((1 << F.f) | fr) * Fraction(2) ** (ef - F.bias - F.f)


def isnan(c): return c in ('qnan', 'snan')


def rnd(F, s, N, S, sticky, rm):
    """Round magnitude N/2^S (+ sticky) with sign s. N > 0."""
    E = N.bit_length() - 1 - S

    def round_at(Q):
        sh = S + Q
        assert sh >= 2, (sh, S, Q)
        kept = N >> sh
        low = N & ((1 << sh) - 1)
        half = 1 << (sh - 1)
        g = low >= half
        r = (low & (half - 1)) != 0 or sticky
        lsb = kept & 1
        if rm == 1:
            inc = False
        elif rm == 2:
            inc = (g or r) and s
        elif rm == 3:
            inc = (g or r) and not s
        elif rm == 4:
            inc = g
        else:
            inc = g and (r or lsb)
        return kept + int(inc), (g or r)

    Ep = max(E, F.emin)
    kept, inexact = round_at(Ep - F.f)
    if kept == 1 << (F.f + 1):
        kept >>= 1
        Ep += 1
    kU, _ = round_at(E - F.f)
    tiny = Fraction(kU) * Fraction(2) ** (E - F.f) < Fraction(2) ** F.emin
    if Ep > F.emax:
        toinf = rm in (0, 4, 5, 6, 7) or (rm == 2 and s) or (rm == 3 and not s)
        mag = ((1 << F.e) - 1) << F.f
        if not toinf:
            mag -= 1
        return (s * F.sbit) | mag, OF | NX
    if kept >= 1 << F.f:
        mag = ((Ep + F.bias) << F.f) | (kept - (1 << F.f))
    else:
        mag = kept
    fl = (NX if inexact else 0) | (UF if (tiny and inexact) else 0)
    return (s * F.sbit) | mag, fl


def round_value(F, v, rm, zero_sign):
    """Round a signed Fraction v; exact zero gets sign zero_sign."""
    if v == 0:
        return zero_sign * F.sbit, 0
    s = 1 if v < 0 else 0
    m = abs(v)
    e0 = m.numerator.bit_length() - m.denominator.bit_length()
    S = max(F.S, -e0 + F.f + 8)
    sc = m * (1 << S)
    N = sc.numerator // sc.denominator
    return rnd(F, s, N, S, sc != N, rm)


def round_sqrt(F, v, rm):
    sc = v * (1 << (2 * F.S))
    assert sc.denominator == 1
    n = sc.numerator
    N = math.isqrt(n)
    return rnd(F, 0, N, F.S, N * N != n, rm)


def sval(s, m): return -m if s else m


def ref(F, op, rm, a, b, c):
    QN = F.qnan
    if op in (OPS['ADD'], OPS['SUB']):
        if op == OPS['SUB']:
            b ^= F.sbit
        ca, sa, va = cls(F, a)
        cb, sb, vb = cls(F, b)
        if isnan(ca) or isnan(cb):
            return QN, NV if 'snan' in (ca, cb) else 0
        if ca == 'inf' and cb == 'inf' and sa != sb:
            return QN, NV
        if ca == 'inf':
            return a, 0
        if cb == 'inf':
            return b, 0
        if ca == 'zero' and cb == 'zero':
            zs = sa if sa == sb else int(rm == 2)
            return zs * F.sbit, 0
        return round_value(F, sval(sa, va) + sval(sb, vb), rm, int(rm == 2))
    if op == OPS['MUL']:
        ca, sa, va = cls(F, a)
        cb, sb, vb = cls(F, b)
        s = sa ^ sb
        inv = (ca == 'inf' and cb == 'zero') or (ca == 'zero' and cb == 'inf')
        if isnan(ca) or isnan(cb) or inv:
            return QN, NV if ('snan' in (ca, cb) or inv) else 0
        if 'inf' in (ca, cb):
            return s * F.sbit | (((1 << F.e) - 1) << F.f), 0
        if 'zero' in (ca, cb):
            return s * F.sbit, 0
        return round_value(F, sval(s, va * vb), rm, 0)
    if op in (OPS['MADD'], OPS['MSUB'], OPS['NMSUB'], OPS['NMADD']):
        negp = op in (OPS['NMSUB'], OPS['NMADD'])
        negc = op in (OPS['MSUB'], OPS['NMADD'])
        if negc:
            c ^= F.sbit
        ca, sa, va = cls(F, a)
        cb, sb, vb = cls(F, b)
        cc, sc, vc = cls(F, c)
        sp = sa ^ sb ^ int(negp)
        inv = (ca == 'inf' and cb == 'zero') or (ca == 'zero' and cb == 'inf')
        if isnan(ca) or isnan(cb) or isnan(cc) or inv:
            return QN, NV if ('snan' in (ca, cb, cc) or inv) else 0
        pinf = 'inf' in (ca, cb)
        if pinf:
            if cc == 'inf' and sc != sp:
                return QN, NV
            return sp * F.sbit | (((1 << F.e) - 1) << F.f), 0
        if cc == 'inf':
            return c, 0
        pzero = 'zero' in (ca, cb)
        if pzero and cc == 'zero':
            zs = sp if sp == sc else int(rm == 2)
            return zs * F.sbit, 0
        vp = Fraction(0) if pzero else sval(sp, va * vb)
        return round_value(F, vp + sval(sc, vc), rm, int(rm == 2))
    if op == OPS['DIV']:
        ca, sa, va = cls(F, a)
        cb, sb, vb = cls(F, b)
        s = sa ^ sb
        inv = (ca == 'inf' and cb == 'inf') or (ca == 'zero' and cb == 'zero')
        if isnan(ca) or isnan(cb) or inv:
            return QN, NV if ('snan' in (ca, cb) or inv) else 0
        inf = s * F.sbit | (((1 << F.e) - 1) << F.f)
        if ca == 'inf':
            return inf, 0
        if cb == 'inf' or ca == 'zero':
            return s * F.sbit, 0
        if cb == 'zero':
            return inf, DZ
        return round_value(F, sval(s, va / vb), rm, 0)
    if op == OPS['SQRT']:
        ca, sa, va = cls(F, a)
        if isnan(ca):
            return QN, NV if ca == 'snan' else 0
        if ca == 'zero':
            return a, 0
        if sa:
            return QN, NV
        if ca == 'inf':
            return a, 0
        return round_sqrt(F, va, rm)
    if op in (OPS['FROUND'], OPS['FROUNDNX']):
        ca, sa, va = cls(F, a)
        if isnan(ca):
            return QN, NV if ca == 'snan' else 0
        if ca in ('inf', 'zero'):
            return a, 0
        v = sval(sa, va)
        r = round_int(v, rm)
        fl = NX if (r != v and op == OPS['FROUNDNX']) else 0
        if r == v:
            return a, fl
        if r == 0:
            return sa * F.sbit, fl
        bits, f0 = round_value(F, Fraction(r), rm, sa)
        assert f0 == 0
        return bits, fl
    if op in (OPS['MIN'], OPS['MAX'], OPS['MINM'], OPS['MAXM']):
        ca, sa, va = cls(F, a)
        cb, sb, vb = cls(F, b)
        fl = NV if 'snan' in (ca, cb) else 0
        if isnan(ca) and isnan(cb):
            return QN, fl
        if op in (OPS['MINM'], OPS['MAXM']) and (isnan(ca) or isnan(cb)):
            return QN, fl
        if isnan(ca):
            return b, fl
        if isnan(cb):
            return a, fl

        def key(cl, s, v):
            if cl == 'inf':
                return (sval(s, Fraction(2) ** (F.emax + 10)), 0)
            return (sval(s, v), -1 if s else 1)  # -0 < +0
        ka, kb = key(ca, sa, va), key(cb, sb, vb)
        lt = ka < kb
        if op in (OPS['MIN'], OPS['MINM']):
            return (a if lt else b), fl
        return (b if lt else a), fl
    if op in (OPS['SGNJ'], OPS['SGNJN'], OPS['SGNJX']):
        sa = a >> (F.e + F.f)
        sb = b >> (F.e + F.f)
        s = sb if op == OPS['SGNJ'] else (1 - sb if op == OPS['SGNJN'] else sa ^ sb)
        return (s * F.sbit) | (a & (F.sbit - 1)), 0
    raise ValueError(op)


def round_int(v, rm):
    fl = v.numerator // v.denominator
    fr = v - fl
    if fr == 0:
        return fl
    if rm == 1:
        return fl if v >= 0 else fl + 1
    if rm == 2:
        return fl
    if rm == 3:
        return fl + 1
    half = Fraction(1, 2)
    if fr > half:
        return fl + 1
    if fr < half:
        return fl
    if rm == 4:
        return fl + 1 if v > 0 else fl
    return fl if fl % 2 == 0 else fl + 1


def ref_int(F, xlen, op, rm, a, b, x):
    """Returns (res, xres, flags) for the integer-touching ops."""
    M = (1 << xlen) - 1
    if op in (14, 15, 16, 17):
        W = 64 if op in (16, 17) else 32
        signed = op in (14, 16)
        hi = (1 << (W - 1)) - 1 if signed else (1 << W) - 1
        lo = -(1 << (W - 1)) if signed else 0
        ca, sa, va = cls(F, a)

        def fin(r):
            r &= (1 << W) - 1
            if W == 32 and (r >> 31) & 1:
                r |= M ^ 0xFFFFFFFF
            return r & M
        if isnan(ca):
            return 0, fin(hi), NV
        if ca == 'inf':
            return 0, fin(lo if sa else hi), NV
        if ca == 'zero':
            return 0, 0, 0
        v = sval(sa, va)
        r = round_int(v, rm)
        if lo <= r <= hi:
            return 0, fin(r), (NX if r != v else 0)
        return 0, fin(lo if v < 0 else hi), NV
    if op in (18, 19, 20, 21):
        W = 64 if op in (20, 21) else 32
        signed = op in (18, 20)
        v = x & ((1 << W) - 1)
        if signed and (v >> (W - 1)) & 1:
            v -= 1 << W
        r, fl = round_value(F, Fraction(v), rm, 0)
        return r, 0, fl
    if op in (22, 23, 24, 28, 29):
        quiet = op in (28, 29)
        op = {28: 23, 29: 24}.get(op, op)
        ca, sa, va = cls(F, a)
        cb, sb, vb = cls(F, b)
        nan = isnan(ca) or isnan(cb)
        if op == 22 or quiet:
            fl = NV if 'snan' in (ca, cb) else 0
        else:
            fl = NV if nan else 0
        if nan:
            return 0, 0, fl

        def val(cl, s, v):
            if cl == 'inf':
                return sval(s, Fraction(2) ** (F.emax + 10))
            return sval(s, v)
        A, B = val(ca, sa, va), val(cb, sb, vb)
        res = (A == B) if op == 22 else ((A < B) if op == 23 else (A <= B))
        return 0, int(res), fl
    if op == 25:
        ca, sa, va = cls(F, a)
        ef = (a >> F.f) & ((1 << F.e) - 1)
        if ca == 'inf':
            bit = 0 if sa else 7
        elif ca == 'zero':
            bit = 3 if sa else 4
        elif ca == 'snan':
            bit = 8
        elif ca == 'qnan':
            bit = 9
        elif ef == 0:
            bit = 2 if sa else 5
        else:
            bit = 1 if sa else 6
        return 0, 1 << bit, 0
    raise ValueError(op)


def gen_x(r, xlen):
    k = r.random()
    if k < 0.2:
        return r.randrange(0, 4)
    if k < 0.4:
        return (-r.randrange(1, 1000)) & ((1 << xlen) - 1)
    if k < 0.6:
        return r.getrandbits(xlen) >> r.randrange(xlen)
    if k < 0.7:
        return (1 << r.randrange(xlen)) + r.randrange(-2, 3) & ((1 << xlen) - 1)
    return r.getrandbits(xlen)


def gen_val(F, rnd_):
    k = rnd_.random()
    mx = (1 << F.w) - 1
    s = rnd_.getrandbits(1) * F.sbit
    ones = ((1 << F.e) - 1) << F.f
    if k < 0.05:
        return s
    if k < 0.10:
        return s | ones
    if k < 0.13:
        return s | ones | (1 << (F.f - 1)) | rnd_.getrandbits(F.f - 1)
    if k < 0.16:
        return s | ones | max(1, rnd_.getrandbits(F.f - 1))
    if k < 0.30:
        return s | max(1, rnd_.getrandbits(F.f) >> rnd_.randrange(F.f))
    if k < 0.36:
        return s | (1 << F.f) | rnd_.getrandbits(F.f)  # min normal binade
    if k < 0.42:
        return s | (ones - (1 << F.f)) | rnd_.getrandbits(F.f)  # max binade
    if k < 0.50:
        # near 1.0
        return s | ((F.bias + rnd_.randrange(-3, 4)) << F.f) | rnd_.getrandbits(F.f)
    return rnd_.getrandbits(F.w) & mx if rnd_.random() < 0.5 else (
        s | ((rnd_.randrange(1, (1 << F.e) - 1)) << F.f) | rnd_.getrandbits(F.f))


def gen_cases(F, n, seed, xlen=64):
    r = random.Random(seed)
    cases = []
    oplist = [v for v in OPS.values() if xlen == 64 or v not in (16, 17, 20, 21)]
    for i in range(n):
        op = oplist[i % len(oplist)]
        rm = r.randrange(5)
        a, b, c = gen_val(F, r), gen_val(F, r), gen_val(F, r)
        if r.random() < 0.15:  # cancellation: b close to -a or a
            b = (a ^ (F.sbit if op in (0, 5) else 0)) ^ r.getrandbits(3)
        if op in range(5, 9) and r.random() < 0.2:
            # c close to -(a*b) when finite
            ca, sa, va = cls(F, a)
            cb, sb, vb = cls(F, b)
            if ca == 'fin' and cb == 'fin':
                p = sval(sa ^ sb ^ int(op in (7, 8)), va * vb)
                t, _ = round_value(F, -p if op in (5, 7) else p, r.randrange(5), 0)
                c = t
        if op in (2, 3, 5, 6, 7, 8) and r.random() < 0.3:
            # result exponent near the subnormal / tininess / overflow boundaries
            ca, sa, va = cls(F, a)
            if ca == 'fin':
                T = r.choice([F.emin - F.f - 2, F.emin - F.f, F.emin - 2, F.emin - 1, F.emin,
                              F.emax - 1, F.emax, F.emax + 1])
                tgt = Fraction(2) ** T * Fraction(r.randrange(1 << 12, 1 << 13), 1 << 12)
                q = tgt / va if op != 3 else va / tgt
                b, _ = round_value(F, q if r.random() < 0.5 else -q, r.randrange(5), 0)
        if op in (30, 31) and r.random() < 0.5:
            # near integers and half-integers, small and near 2^f
            base = r.choice([0, 1, 2, 3, 7, (1 << F.f) - 2, 1 << (F.f - 1)])
            t = Fraction(base) + Fraction(r.choice([0, 1, 2, 3, 4, 5, 6, 7]), 8)
            t = t + Fraction(r.choice([-1, 0, 1]), 1 << (F.f - 2))
            a, _ = round_value(F, -t if r.random() < 0.4 else t, 0, 0)
        if op in (14, 15, 16, 17) and r.random() < 0.5:
            # values near the integer range edges
            W = 64 if op in (16, 17) else 32
            t = Fraction(r.choice([1 << (W - 1), 1 << W, 1, 0])) + Fraction(r.randrange(-6, 7), r.choice([1, 2, 4]))
            t = -t if r.random() < 0.4 else t
            a, _ = round_value(F, t, 0, 0)
        cases.append((op, rm, a, b, c, gen_x(r, xlen)))
    return cases


def run_coq_file(body, tag):
    d = os.environ.get('FPTEST_DIR', os.path.join(tempfile.gettempdir(), 'fptest'))
    os.makedirs(d, exist_ok=True)
    vf = os.path.join(d, f'T_{tag}.v')
    open(vf, 'w').write(body)
    out = subprocess.run(['rocq', 'compile', '-Q', FPU, 'Fpu', '-Q', GURU, 'Guru', vf],
                         capture_output=True, text=True)
    if out.returncode != 0:
        print(out.stdout[-3000:], out.stderr[-3000:])
        sys.exit(1)
    return out.stdout


# RISC-V W / WU integer width (the core's `wlen` parameter); `ref_int` models RISC-V.
WLEN = 32

def run_coq3(e, f, xlen, cases, tag):
    lst = ';\n  '.join(f'({FAM[DEC[op][0]]}, {DEC[op][1]}, {rm}, {a}, {b}, {c}, {x})'
                        for (op, rm, a, b, c, x) in cases)
    out = run_coq_file(f'''
From Stdlib Require Import String List ZArith Zmod.
From Guru Require Import Primitives Library Syntax Combinators Notations Semantics.
From Fpu Require Import FpUtil FpCore.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.

Definition mkOp (fam o : Z) : type FpOpDK :=
  let bt k := Z.testbit o k in
  (Z.eqb fam 0 ,, (Z.eqb fam 1 ,, (Z.eqb fam 2 ,, (Z.eqb fam 3 ,, (Z.eqb fam 4 ,, (Z.eqb fam 5 ,, (Z.eqb fam 6 ,,
  (Z.eqb fam 7 ,, (Z.eqb fam 8 ,, (Z.eqb fam 9 ,, (Z.eqb fam 10 ,, (Z.eqb fam 11 ,,
  (bt 0 ,, (bt 1 ,, (bt 2 ,, (bt 3 ,, (bt 4 ,, (Zmod.of_Z _ ((o / 32) mod 4) ,,
  (bt 7 ,, (bt 8 ,, (bt 9 ,, (bt 10 ,, tt)))))))))))))))))))))).

Definition runOne (t : Z * Z * Z * Z * Z * Z * Z) : Z * Z * Z :=
  let '(fam, o, rm, a, b, c, x) := t in
  let req : type (FpReqK {e} {f} {xlen}) :=
    (mkOp fam o ,, (Zmod.of_Z _ rm ,, (Zmod.of_Z _ a ,, (Zmod.of_Z _ b ,, (Zmod.of_Z _ c ,, (Zmod.of_Z _ x ,, tt)))))) in
  let out := evalLetExpr (fpuCompute {BM} {e} {f} {xlen} {WLEN} type req) in
  (Zmod.unsigned (out @% "res"), Zmod.unsigned (out @% "xres"), Zmod.unsigned (out @% "flags")).

Definition cases : list (Z * Z * Z * Z * Z * Z * Z) := [
  {lst} ].

Eval vm_compute in (map runOne cases).
''', tag)
    trip = re.findall(r'\(\s*(\d+),\s*(\d+),\s*(\d+)\)', out)
    return [(int(x), int(y), int(z)) for x, y, z in trip]


def run_cvt(e1, f1, e2, f2, cases, tag):
    lst = ';\n  '.join(f'({rm}, {a})' for (rm, a) in cases)
    out = run_coq_file(f'''
From Stdlib Require Import String List ZArith Zmod.
From Guru Require Import Primitives Library Syntax Combinators Notations Semantics.
From Fpu Require Import FpUtil FpCore.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.

Definition runOne (t : Z * Z) : Z * Z :=
  let '(rm, a) := t in
  let out := evalLetExpr (cvtFF {BM} {e1} {f1} {e2} {f2} type (Zmod.of_Z _ rm) (Zmod.of_Z _ a)) in
  (Zmod.unsigned (out @% "res"), Zmod.unsigned (out @% "flags")).

Definition cases : list (Z * Z) := [
  {lst} ].

Eval vm_compute in (map runOne cases).
''', tag)
    pairs = re.findall(r'\(\s*(\d+),\s*(\d+)\)', out)
    return [(int(x), int(y)) for x, y in pairs]


def run_coq(e, f, cases, tag):
    d = os.environ.get('FPTEST_DIR', os.path.join(tempfile.gettempdir(), 'fptest'))
    os.makedirs(d, exist_ok=True)
    vf = os.path.join(d, f'T_{tag}.v')
    lst = ';\n  '.join(f'({op}, {rm}, {a}, {b}, {c})' for (op, rm, a, b, c) in cases)
    open(vf, 'w').write(f'''
From Stdlib Require Import String List ZArith Zmod.
From Guru Require Import Primitives Library Syntax Combinators Notations Semantics.
From Fpu Require Import FpUtil FpCore.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.

Definition runOne (t : Z * Z * Z * Z * Z) : Z * Z :=
  let '(op, rm, a, b, c) := t in
  let req : type (FpReqK {e} {f}) :=
    (Zmod.of_Z _ op ,, (Zmod.of_Z _ rm ,, (Zmod.of_Z _ a ,, (Zmod.of_Z _ b ,, (Zmod.of_Z _ c ,, tt))))) in
  let out := evalLetExpr (fpuCompute {e} {f} type req) in
  (Zmod.unsigned (out @% "res"), Zmod.unsigned (out @% "flags")).

Definition cases : list (Z * Z * Z * Z * Z) := [
  {lst} ].

Eval vm_compute in (map runOne cases).
''')
    out = subprocess.run(['rocq', 'compile', '-Q', FPU, 'Fpu', '-Q', GURU, 'Guru', vf],
                         capture_output=True, text=True)
    if out.returncode != 0:
        print(out.stdout[-3000:], out.stderr[-3000:])
        sys.exit(1)
    pairs = re.findall(r'\(\s*(\d+),\s*(\d+)\)', out.stdout)
    return [(int(x), int(y)) for x, y in pairs]


def ref_cvt(F1, F2, rm, a):
    ca, sa, va = cls(F1, a)
    if isnan(ca):
        return F2.qnan, NV if ca == 'snan' else 0
    if ca == 'inf':
        return sa * F2.sbit | (((1 << F2.e) - 1) << F2.f), 0
    if ca == 'zero':
        return sa * F2.sbit, 0
    return round_value(F2, sval(sa, va), rm, 0)


def main_cvt(e1, f1, e2, f2, n, seed):
    F1, F2 = Fmt(e1, f1), Fmt(e2, f2)
    r = random.Random(seed)
    cases = []
    for i in range(n):
        a = gen_val(F1, r)
        if r.random() < 0.3 and e1 > e2:  # near the target's range edges
            t = Fraction(2) ** r.choice([F2.emax, F2.emax + 1, F2.emin, F2.emin - F2.f, F2.emin - F2.f - 1])
            t = t * Fraction(r.randrange(1 << 10, 1 << 11), 1 << 10)
            a, _ = round_value(F1, -t if r.random() < 0.5 else t, 0, 0)
        cases.append((r.randrange(5), a))
    got = run_cvt(e1, f1, e2, f2, cases, f'cvt_{e1}_{f1}_{e2}_{f2}_{seed}')
    assert len(got) == len(cases), (len(got), len(cases))
    bad = 0
    for (rm, a), g in zip(cases, got):
        exp = ref_cvt(F1, F2, rm, a)
        if exp != g:
            bad += 1
            if bad <= 25:
                print(f'MISMATCH cvt rm={rm} a={a:#x}: spec=({g[0]:#x},{g[1]:#04x}) ref=({exp[0]:#x},{exp[1]:#04x})')
    print(f'cvt ({e1},{f1}) -> ({e2},{f2}): {len(cases)} cases, {bad} mismatches')


FLI = [(1, 1, 0), 'minnorm', (0, 1, -16), (0, 1, -15), (0, 1, -8), (0, 1, -7), (0, 1, -4), (0, 1, -3),
       (0, 1, -2), (0, 5, -4), (0, 3, -3), (0, 7, -4), (0, 1, -1), (0, 5, -3), (0, 3, -2), (0, 7, -3),
       (0, 1, 0), (0, 5, -2), (0, 3, -1), (0, 7, -2), (0, 1, 1), (0, 5, -1), (0, 3, 0), (0, 1, 2),
       (0, 1, 3), (0, 1, 4), (0, 1, 7), (0, 1, 8), (0, 1, 15), (0, 1, 16), 'inf', 'nan']


def ref_fli(F, i):
    t = FLI[i]
    if t == 'minnorm':
        return 1 << F.f
    if t == 'inf':
        return ((1 << F.e) - 1) << F.f
    if t == 'nan':
        return F.qnan
    sg, m, k = t
    v = Fraction(m) * Fraction(2) ** k
    maxf = (Fraction(2) - Fraction(1, 1 << F.f)) * Fraction(2) ** F.emax
    if v > maxf:
        return sg * F.sbit | (((1 << F.e) - 1) << F.f)
    bits, fl = round_value(F, -v if sg else v, 0, 0)
    assert fl == 0, (i, F.e, F.f)
    return bits


def main_fli(e, f):
    F = Fmt(e, f)
    out = run_coq_file(f'''
From Stdlib Require Import String List ZArith Zmod.
From Guru Require Import Primitives Library Syntax Combinators Notations Semantics.
From Fpu Require Import FpUtil FpCore.
Import ListNotations.
Local Open Scope Z_scope.
Eval vm_compute in (map (fun i => Zmod.unsigned (evalExpr (fliConstE {e} {f} type (Const type (Bit 5) (Zmod.of_Z _ i)))))
                        (map Z.of_nat (seq 0 32))).
''', f'fli_{e}_{f}')
    got = [int(v) for v in re.findall(r'\d+', out.split('=', 1)[1])][:32]
    bad = [(i, hex(g), hex(ref_fli(F, i))) for i, g in enumerate(got) if g != ref_fli(F, i)]
    for b in bad:
        print('MISMATCH fli', b)
    print(f'fli ({e},{f}): 32 entries, {len(bad)} mismatches')


def main():
    if sys.argv[1] == 'cvt':
        return main_cvt(*map(int, sys.argv[2:8]))
    if sys.argv[1] == 'fli':
        return main_fli(*map(int, sys.argv[2:4]))
    e, f, n, seed = map(int, sys.argv[1:5])
    xlen = int(sys.argv[5]) if len(sys.argv) > 5 else 64
    F = Fmt(e, f)
    cases = gen_cases(F, n, seed, xlen)
    got = run_coq3(e, f, xlen, cases, f'{e}_{f}_{seed}_{xlen}')
    assert len(got) == len(cases), (len(got), len(cases))
    inv = {v: k for k, v in OPS.items()}
    bad = 0
    for cs, g in zip(cases, got):
        op, rm, a, b, c, x = cs
        if 14 <= op <= 25 or op in (28, 29):
            exp = ref_int(F, xlen, op, rm, a, b, x)
        else:
            r0, f0 = ref(F, op, rm, a, b, c)
            exp = (r0, 0, f0)
        if exp != g:
            bad += 1
            if bad <= 25:
                print(f'MISMATCH {inv[op]} rm={rm} a={a:#x} b={b:#x} c={c:#x} x={x:#x}: '
                      f'spec=({g[0]:#x},{g[1]:#x},{g[2]:#04x}) ref=({exp[0]:#x},{exp[1]:#x},{exp[2]:#04x})')
    print(f'format ({e},{f}) xlen {xlen}: {len(cases)} cases, {bad} mismatches')


if __name__ == '__main__':
    main()
