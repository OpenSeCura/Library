(*
 * Copyright 2026 Google LLC
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     https://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 *)

(*
 * Single-format floating-point arithmetic spec (`FpCore.v`).
 *
 * Everything is generic over a binary interchange format with `e` exponent bits and `f`
 * fraction bits (precision `p = f + 1`, packed width `f + e + 1`):
 *   H = (5, 10), S = (8, 23), D = (11, 52), Q = (15, 112).
 *
 * The functions here ARE the definition of the arithmetic (RISC-V rules: canonical NaN,
 * tininess after rounding, no flush-to-zero, `inf * 0 + qNaN` raises NV, minimumNumber /
 * maximumNumber for FMIN / FMAX).
 *
 * Internal representation of a finite non-zero operand (`fpUnpack`): sign, signed internal
 * exponent `exp` (`e + 3` bits, two's complement) and normalized significand `sig` (`p` bits,
 * top bit set; subnormals are normalized with a leading-zero count), so that
 *   value = (-1)^sign * sig * 2^(exp - expOff - f).
 * The exponent mode `bm` selects the offset: `bm = true` (the hardware model used by the spec and
 * the units) keeps exponents BIASED (`expOff = bias`): unpacking needs no bias subtraction and
 * packing no bias addition; only MUL / FMA (`- bias`), DIV and SQRT (`+ bias`) and the format
 * conversion (`+ bias2 - bias1`) adjust once.  `bm = false` is the unbiased reference model
 * (`expOff = 0`, see `FpCoreRef.v`); both models share every definition.
 * (`sig` has its top bit set for every input, including zeros, infinities and NaNs.)
 *
 * Rounding (`roundPack`) takes `sigR : Bit (f + 3)` with its top bit (bit `f + 2`) of weight
 * `2^x`, plus a sticky bit for everything below bit 0, and returns the packed result and the
 * `fflags` bits (NV DZ OF UF NX = bits 4..0).  `normRound` first normalizes any wider
 * significand.
 *
 * Units (see `ImplFpuUnits.v` for the staged implementations of the same algorithms):
 * - pipe unit: every family except DIV and SQRT (and the narrow conversions, see `SpecFpu.v`):
 *   ADD/SUB, MUL, FMA (4 variants), MIN/MAX (+ Zfa FMINM/FMAXM), SGNJ*, FCVT to / from integers,
 *   FEQ/FLT/FLE (+ Zfa FLTQ/FLEQ), FCLASS, Zfa FROUND/FROUNDNX.  The operation is the decoded
 *   record `FpOpDK`.  Zfa FLI is a constant (`fliConstE`), not an operation.
 *   `pipeSpec` = `pipeInfoOf`, then the exact significand product (`Mul`), then `pipeFinishCore`.
 * - divide unit: `divSpec` = `divInfoOf`, then quotient / sticky from `Div` / `Rem`, then
 *   `divFinishCore`.
 * - square-root unit: `sqrtSpec` = `sqrtInit`, `f + 3` steps of the restoring square-root
 *   recurrence `sqrtStep`, then `sqrtFinish`.
 *)

From Stdlib Require Import String List ZArith Zmod Lia.
From Guru Require Import Primitives Library Syntax Combinators Notations.
From Fpu Require Import FpUtil.

Unset Implicit Arguments.

Import ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope guru_scope.

(* ===========================================================================
 * 1. OPERATIONS, ROUNDING MODES, KINDS
 * =========================================================================== *)

(* The decoded operation.  The FPU's packets carry a tagged union of operation families with
 * their options (`SpecFpu.FpuOpK`); `SpecFpu.decodeOp` turns it into this flat record once, at
 * the core's entry: one flag per family plus the options, which are false / zero unless their
 * family is set.  The core never sees the narrow-format conversions (`SpecFpu.v`). *)
Definition FpOpDK : Kind :=
  STRUCT_TYPE {
    "add"      :: Bool ;   (* FADD / FSUB (negB) *)
    "mul"      :: Bool ;   (* FMUL *)
    "fma"      :: Bool ;   (* FMADD / FMSUB / FNMSUB / FNMADD (negProd, negAdd) *)
    "div"      :: Bool ;   (* FDIV *)
    "sqrt"     :: Bool ;   (* FSQRT *)
    "minmax"   :: Bool ;   (* FMIN / FMAX (isMax); Zfa FMINM / FMAXM (nanProp) *)
    "sgnj"     :: Bool ;   (* FSGNJ / FSGNJN / FSGNJX (mode 0 / 1 / 2) *)
    "cmp"      :: Bool ;   (* FEQ / FLT / FLE (mode 0 / 1 / 2); Zfa FLTQ / FLEQ (quiet) *)
    "fclass"   :: Bool ;   (* FCLASS *)
    "cvtFI"    :: Bool ;   (* FCVT.{W,WU,L,LU}.fmt (unsigned, wide) *)
    "cvtIF"    :: Bool ;   (* FCVT.fmt.{W,WU,L,LU} (unsigned, wide) *)
    "round"    :: Bool ;   (* Zfa FROUND / FROUNDNX (nx) *)
    "negB"     :: Bool ;   (* subtract *)
    "negProd"  :: Bool ;   (* negate the product *)
    "negAdd"   :: Bool ;   (* negate the addend *)
    "isMax"    :: Bool ;   (* maximum (else minimum) *)
    "nanProp"  :: Bool ;   (* a NaN input gives the canonical NaN *)
    "mode"     :: Bit 2 ;  (* sign-injection kind / comparison kind *)
    "quiet"    :: Bool ;   (* FLT / FLE signal NV only for signaling NaNs *)
    "unsigned" :: Bool ;   (* unsigned integer *)
    "wide"     :: Bool ;   (* 64-bit integer (XLEN = 64 only) *)
    "nx"       :: Bool     (* FROUNDNX: raise NX when inexact *)
  }.

(* Rounding modes (3 bits).  `RmDyn` only appears in packets; the core sees a resolved mode.
 * Reserved values 5..7 are treated as RNE by the core. *)
Definition RmRne : Z := 0.
Definition RmRtz : Z := 1.
Definition RmRdn : Z := 2.
Definition RmRup : Z := 3.
Definition RmRmm : Z := 4.
Definition RmDyn : Z := 7.

Definition FpBits (e f : Z) : Kind := Bit (f + e + 1).

Definition FpUnpK (e f : Z) : Kind :=
  STRUCT_TYPE {
    "sign" :: Bool ;
    "zero" :: Bool ;
    "inf"  :: Bool ;
    "nan"  :: Bool ;
    "snan" :: Bool ;
    "exp"  :: Bit (e + 3) ;
    "sig"  :: Bit (f + 1)
  }.

Definition FpOutK (e f : Z) : Kind :=
  STRUCT_TYPE {
    "res"   :: Bit (f + e + 1) ;
    "flags" :: Bit 5
  }.

Definition FpReqK (e f xlen : Z) : Kind :=
  STRUCT_TYPE {
    "op" :: FpOpDK ;
    "rm" :: Bit 3 ;
    "a"  :: Bit (f + e + 1) ;
    "b"  :: Bit (f + e + 1) ;
    "c"  :: Bit (f + e + 1) ;
    "x"  :: Bit xlen            (* integer operand (int -> fp conversions) *)
  }.

(* Integer result and flags. *)
Definition IntOutK (xlen : Z) : Kind :=
  STRUCT_TYPE {
    "xres"  :: Bit xlen ;
    "flags" :: Bit 5
  }.

(* Result of one operation: floating-point result, integer result, flags. *)
Definition FpResK (e f xlen : Z) : Kind :=
  STRUCT_TYPE {
    "res"   :: Bit (f + e + 1) ;
    "xres"  :: Bit xlen ;
    "flags" :: Bit 5
  }.

(* Everything the pipe unit's finish step needs, except the significand product. *)
Definition PipeInfoK (e f xlen : Z) : Kind :=
  STRUCT_TYPE {
    "op"      :: FpOpDK ;
    "x"       :: Bit xlen ;
    "rm"      :: Bit 3 ;
    "a"       :: Bit (f + e + 1) ;
    "b2"      :: Bit (f + e + 1) ;  (* b, negated for FSUB *)
    "c2"      :: Bit (f + e + 1) ;  (* c, negated for FMSUB / FNMADD *)
    "ua"      :: FpUnpK e f ;
    "ub"      :: FpUnpK e f ;       (* unpacked b2 *)
    "uc"      :: FpUnpK e f ;       (* unpacked c2 *)
    "negProd" :: Bool               (* NMSUB / NMADD *)
  }.

(* The exponent-dependent quantities of rounding (`rpExp`); they are the same in both exponent
 * modes. *)
Definition RpExpK (e : Z) : Kind :=
  STRUCT_TYPE {
    "tinyPre" :: Bool ;          (* x < emin: subnormal before rounding *)
    "sh"      :: Bit (e + 3) ;   (* subnormal right shift *)
    "bm1"     :: Bit (e + 3) ;   (* packed exponent field minus 1 *)
    "ovfX"    :: Bool ;          (* x > emax *)
    "atEm1"   :: Bool            (* x = emin - 1 *)
  }.

Definition AlignK (W : Z) : Kind :=
  STRUCT_TYPE { "r" :: Bit W ; "st" :: Bool ; "effSub" :: Bool }.

Definition DivInfoK (e f : Z) : Kind :=
  STRUCT_TYPE {
    "rm" :: Bit 3 ;
    "ua" :: FpUnpK e f ;
    "ub" :: FpUnpK e f
  }.

Definition SqrtInfoK (e f : Z) : Kind :=
  STRUCT_TYPE {
    "rm" :: Bit 3 ;
    "a"  :: Bit (f + e + 1) ;
    "ua" :: FpUnpK e f
  }.

(* Restoring square root of a `2 (f + 3)`-bit radicand, one root bit per step. *)
Definition SqrtStateK (e f : Z) : Kind :=
  STRUCT_TYPE {
    "info" :: SqrtInfoK e f ;
    "rad"  :: Bit (2 * f + 6) ;  (* radicand, consumed two bits per step from the top *)
    "rem"  :: Bit (f + 5) ;      (* partial remainder *)
    "root" :: Bit (f + 3)        (* partial root *)
  }.

Section FpCore.
  (* Exponent mode (the first argument of every definition that depends on it): `bm = true` keeps
   * exponents biased internally (the hardware model, used by the units); `bm = false` is the
   * readable unbiased reference model (`FpCoreRef.v`).  Both models share every definition; only
   * `expOff` / `expUnpack` depend on `bm`. *)
  Variable bm : bool.
  Variable e f xlen : Z.
  Variable ty : Kind -> Type.

  Local Abbreviation FB := (FpBits e f).
  Local Abbreviation UK := (FpUnpK e f).
  Local Abbreviation OK := (FpOutK e f).
  Local Abbreviation XK := (Bit (e + 3)).

  (* ---------------------------------------------------------------------------
   * 2. FORMAT CONSTANTS AND SMALL BUILDERS
   * --------------------------------------------------------------------------- *)

  Definition fpBias   : Z := 2 ^ (e - 1) - 1.
  Definition fpEmin   : Z := 1 - fpBias.
  Definition fpEmax   : Z := fpBias.

  (* Internal exponent = unbiased exponent + `expOff`. *)
  Definition expOff   : Z := if bm then fpBias else 0.
  Definition infMagZ  : Z := (2 ^ e - 1) * 2 ^ f.
  Definition qnanMagZ : Z := infMagZ + 2 ^ (f - 1).

  Definition packSigned (s : Expr ty Bool) (mag : Expr ty (Bit (f + e))) : Expr ty FB :=
    Concat (boolBit s) mag.

  Definition qnanE : Expr ty FB := cst (f + e + 1) qnanMagZ.

  Definition infE (s : Expr ty Bool) : Expr ty FB := packSigned s (cst (f + e) infMagZ).

  Definition zeroE (s : Expr ty Bool) : Expr ty FB := packSigned s (cst (f + e) 0).

  Definition mkFlags (nv dz ov uf nx : Expr ty Bool) : Expr ty (Bit 5) :=
    Or [ ITE nv (cst 5 16) (cst 5 0) ;
         ITE dz (cst 5 8)  (cst 5 0) ;
         ITE ov (cst 5 4)  (cst 5 0) ;
         ITE uf (cst 5 2)  (cst 5 0) ;
         ITE nx (cst 5 1)  (cst 5 0) ].

  Definition noFlags : Expr ty (Bit 5) := cst 5 0.

  Definition mkOut (res : Expr ty FB) (flags : Expr ty (Bit 5)) : Expr ty OK :=
    STRUCT { "res" ::= res ; "flags" ::= flags }.

  Definition isRne (rm : ty (Bit 3)) : Expr ty Bool :=
    Or [ Eq (#rm) (cst 3 RmRne) ; Not (Ult (#rm) (cst 3 5)) ].

  Definition magOf (x : ty FB) : Expr ty (Bit (f + e)) := TruncLsb 1 (f + e) (#x).

  Definition flipSign (neg : Expr ty Bool) (x : ty FB) : Expr ty FB :=
    Xor [ #x ; ITE neg (cst (f + e + 1) (2 ^ (f + e))) (cst (f + e + 1) 0) ].

  (* ---------------------------------------------------------------------------
   * 3. UNPACK
   * --------------------------------------------------------------------------- *)

  (* Internal exponent of an operand from its exponent field (`1` for subnormals) and the
   * normalization shift: biased mode needs no bias subtraction. *)
  Definition expUnpack (ebase lz : ty XK) : Expr ty XK :=
    if bm then Sub (#ebase) (#lz) else Sub (Sub (#ebase) (cst (e + 3) fpBias)) (#lz).

  Definition fpUnpack (x : ty FB) : LetExpr ty UK :=
    LetE sgn   : Bit 1       <- TruncMsb 1 (f + e) (#x) ;
    LetE mag   : Bit (f + e) <- TruncLsb 1 (f + e) (#x) ;
    LetE ef    : Bit e       <- TruncMsb e f (#mag) ;
    LetE fr    : Bit f       <- TruncLsb e f (#mag) ;
    LetE eZero : Bool        <- isZero (#ef) ;
    LetE eOnes : Bool        <- isAllOnes (#ef) ;
    LetE fZero : Bool        <- isZero (#fr) ;
    LetE qbit  : Bool        <- bitSet fr (f - 1) ;
    LetE raw   : Bit (f + 1) <- Concat (boolBit (Not (#eZero))) (#fr) ;
    LetE lz    : XK          <- clz (f + 1) (e + 3) raw ;
    (* For a zero, `raw = 0` and the `Or` makes `sig = 2^f`; for anything else the `Or` is a
     * no-op.  So `sig` always has its top bit set. *)
    LetE sig   : Bit (f + 1) <- Or [ Sll (#raw) (#lz) ; cst (f + 1) (2 ^ f) ] ;
    LetE efx   : XK          <- ZeroExtend 3 (#ef) ;
    LetE ebase : XK          <- ITE (#eZero) (cst (e + 3) 1) (#efx) ;
    LetE ex    : XK          <- expUnpack ebase lz ;
    @RetE ty UK (STRUCT {
      "sign" ::= isNotZero (#sgn) ;
      "zero" ::= And [ #eZero ; #fZero ] ;
      "inf"  ::= And [ #eOnes ; #fZero ] ;
      "nan"  ::= And [ #eOnes ; Not (#fZero) ] ;
      "snan" ::= And [ #eOnes ; Not (#fZero) ; Not (#qbit) ] ;
      "exp"  ::= #ex ;
      "sig"  ::= #sig
    }).

  (* ---------------------------------------------------------------------------
   * 4. ROUNDING
   * --------------------------------------------------------------------------- *)

  (* Round-up decision from the sign, the kept LSB, the guard bit and the sticky bit. *)
  Definition roundInc (rm : ty (Bit 3)) (s lsb g r : ty Bool) : Expr ty Bool :=
    Or [ And [ isRne rm ; #g ; Or [ #r ; #lsb ] ] ;
         And [ Eq (#rm) (cst 3 RmRdn) ; Or [ #g ; #r ] ; #s ] ;
         And [ Eq (#rm) (cst 3 RmRup) ; Or [ #g ; #r ] ; Not (#s) ] ;
         And [ Eq (#rm) (cst 3 RmRmm) ; #g ] ].

  (* Overflow goes to infinity (else to the largest finite value). *)
  Definition overflowToInf (rm : ty (Bit 3)) (s : ty Bool) : Expr ty Bool :=
    Or [ isRne rm ;
         Eq (#rm) (cst 3 RmRmm) ;
         And [ Eq (#rm) (cst 3 RmRdn) ; #s ] ;
         And [ Eq (#rm) (cst 3 RmRup) ; Not (#s) ] ].

  (* `sigR` has its top bit (bit `f + 2`) set and of weight `2^x`; `st` = anything below
   * bit 0 is non-zero.  Subnormal results are produced by shifting right (with sticky) to
   * exponent `emin`; the packed magnitude is `((xEff + bias - 1) << f) + rounded`, so a
   * rounding carry moves into the exponent field (subnormal -> normal, normal -> overflow). *)
  (* The exponent part of rounding: everything `roundPack` needs from the internal exponent `x`. *)
  Definition rpExp (x : ty XK) : LetExpr ty (RpExpK e) :=
    LetE emin     : XK          <- cst (e + 3) (fpEmin + expOff) ;
    LetE tinyPre  : Bool        <- Slt (#x) (#emin) ;
    LetE dRaw     : XK          <- Sub (#emin) (#x) ;
    LetE dCl      : XK          <- ITE (Ult (#dRaw) (cst (e + 3) (f + 3))) (#dRaw) (cst (e + 3) (f + 3)) ;
    LetE sh       : XK          <- ITE (#tinyPre) (#dCl) (cst (e + 3) 0) ;
    LetE xEff     : XK          <- ITE (#tinyPre) (#emin) (#x) ;
    LetE bm1      : XK          <- Add [ #xEff ; cst (e + 3) (fpBias - 1 - expOff) ] ;
    @RetE ty (RpExpK e) (STRUCT {
      "tinyPre" ::= #tinyPre ;
      "sh"      ::= #sh ;
      "bm1"     ::= #bm1 ;
      "ovfX"    ::= Slt (cst (e + 3) (fpEmax + expOff)) (#x) ;
      "atEm1"   ::= Eq (#x) (cst (e + 3) (fpEmin - 1 + expOff))
    }).

  Definition roundPack (s : ty Bool) (x : ty XK) (sigR : ty (Bit (f + 3))) (st : ty Bool)
    (rm : ty (Bit 3)) : LetExpr ty OK :=
    LETE xe       : RpExpK e    <- rpExp x ;
    LetE tinyPre  : Bool        <- ##xe`"tinyPre" ;
    LetE sh       : XK          <- ##xe`"sh" ;
    LetE sigS     : Bit (f + 3) <- Srl (#sigR) (#sh) ;
    LetE lostMask : Bit (f + 3) <- Not (Sll (cst (f + 3) (-1)) (#sh)) ;
    LetE stS      : Bool        <- Or [ #st ; isNotZero (And [ #sigR ; #lostMask ]) ] ;
    LetE lsb      : Bool        <- bitSet sigS 2 ;
    LetE g        : Bool        <- bitSet sigS 1 ;
    LetE r        : Bool        <- Or [ bitSet sigS 0 ; #stS ] ;
    LetE inc      : Bool        <- roundInc rm s lsb g r ;
    LetE inexact  : Bool        <- Or [ #g ; #r ] ;
    LetE kept     : Bit (f + 3) <- Srl (#sigS) (cst (f + 3) 2) ;
    LetE rounded  : Bit (f + 3) <- Add [ #kept ; ITE (#inc) (cst (f + 3) 1) (cst (f + 3) 0) ] ;
    LetE bm1      : XK          <- ##xe`"bm1" ;
    LetE magW     : Bit (f + (e + 3)) <-
      Add [ Sll (zext (e + 3) (f + (e + 3)) (#bm1)) (cst (e + 3) f) ;
            zext (f + 3) (f + (e + 3)) (#rounded) ] ;
    LetE ovf      : Bool        <- Or [ ##xe`"ovfX" ;
                                        Not (Ult (#magW) (cst (f + (e + 3)) infMagZ)) ] ;
    LetE toInf    : Bool        <- overflowToInf rm s ;
    LetE magOv    : Bit (f + e) <- ITE (#toInf) (cst (f + e) infMagZ) (cst (f + e) (infMagZ - 1)) ;
    LetE magFin   : Bit (f + e) <- ITE (#ovf) (#magOv) (trunc (f + (e + 3)) (f + e) (#magW)) ;
    (* Tininess after rounding: tiny unless rounding with unbounded exponent at
     * `x = emin - 1` carries up to `2^emin`. *)
    LetE lsb0     : Bool        <- bitSet sigR 2 ;
    LetE g0       : Bool        <- bitSet sigR 1 ;
    LetE r0       : Bool        <- Or [ bitSet sigR 0 ; #st ] ;
    LetE inc0     : Bool        <- roundInc rm s lsb0 g0 r0 ;
    LetE kept0    : Bit (f + 3) <- Srl (#sigR) (cst (f + 3) 2) ;
    LetE carry0   : Bool        <- And [ #inc0 ; Eq (#kept0) (cst (f + 3) (2 ^ (f + 1) - 1)) ] ;
    LetE tiny     : Bool        <- And [ #tinyPre ; Not (And [ ##xe`"atEm1" ; #carry0 ]) ] ;
    LetE uf       : Bool        <- And [ #tiny ; #inexact ; Not (#ovf) ] ;
    LetE nx       : Bool        <- Or [ #inexact ; #ovf ] ;
    @RetE ty OK (mkOut (packSigned (#s) (#magFin))
                       (mkFlags (ConstBool false) (ConstBool false) (#ovf) (#uf) (#nx))).

  (* `wsig : Bit W` has its bit `W - 1` of weight `2^x` (it may have leading zeros); `W >= f + 3`.
   * An exact zero (`wsig = 0`, `st = false`) gives a zero with sign `s`. *)
  Definition normRound (W : Z) (s : ty Bool) (x : ty XK) (wsig : ty (Bit W)) (st : ty Bool)
    (rm : ty (Bit 3)) : LetExpr ty OK :=
    LetE lz   : XK          <- clz W (e + 3) wsig ;
    LetE sigN : Bit W       <- Sll (#wsig) (#lz) ;
    LetE xN   : XK          <- Sub (#x) (#lz) ;
    LetE top  : Bit (f + 3) <- trunc W (f + 3) (Srl (#sigN) (cst W (W - (f + 3)))) ;
    LetE st2  : Bool        <- Or [ #st ; isNotZero (And [ #sigN ; cst W (2 ^ (W - (f + 3)) - 1) ]) ] ;
    LetE isZ  : Bool        <- And [ isZero (#wsig) ; Not (#st) ] ;
    LETE rp   : OK          <- roundPack s xN top st2 rm ;
    RetE (ITE (#isZ) (mkOut (zeroE (#s)) noFlags) (#rp)).

  (* ---------------------------------------------------------------------------
   * 5. ADD / SUB  (b already negated for SUB)
   * --------------------------------------------------------------------------- *)

  (* Align the smaller operand (`W`-bit window, both inputs with the leading one at the same
   * position) and add / subtract.  The result is `floor` of the exact value in window units,
   * plus a sticky bit: for an effective subtraction the shifted-out part is borrowed. *)
  Definition alignAdd (W : Z) (sBig sSm : ty Bool) (xBig xSm : ty XK) (big sm : ty (Bit W))
    : LetExpr ty (AlignK W) :=
    LetE d      : XK    <- Sub (#xBig) (#xSm) ;
    LetE sh     : XK    <- ITE (Ult (#d) (cst (e + 3) W)) (#d) (cst (e + 3) W) ;
    LetE smSh   : Bit W <- Srl (#sm) (#sh) ;
    LetE st     : Bool  <- isNotZero (And [ #sm ; Not (Sll (cst W (-1)) (#sh)) ]) ;
    LetE effSub : Bool  <- Not (Eq (#sBig) (#sSm)) ;
    LetE r      : Bit W <- ITE (#effSub)
                               (Sub (Sub (#big) (#smSh)) (ITE (#st) (cst W 1) (cst W 0)))
                               (Add [ #big ; #smSh ]) ;
    @RetE ty (AlignK W) (STRUCT { "r" ::= #r ; "st" ::= #st ; "effSub" ::= #effSub }).

  Definition addCore (rm : ty (Bit 3)) (a b : ty FB) (ua ub : ty UK) : LetExpr ty OK :=
    LetE sa     : Bool        <- ##ua`"sign" ;
    LetE sb     : Bool        <- ##ub`"sign" ;
    LetE xa     : XK          <- ##ua`"exp" ;
    LetE xb     : XK          <- ##ub`"exp" ;
    LetE siga   : Bit (f + 1) <- ##ua`"sig" ;
    LetE sigb   : Bit (f + 1) <- ##ub`"sig" ;
    LetE xGt    : Bool        <- Slt (#xb) (#xa) ;
    LetE xEq    : Bool        <- Eq (#xa) (#xb) ;
    LetE aBig   : Bool        <- Or [ #xGt ; And [ #xEq ; Not (Ult (#siga) (#sigb)) ] ] ;
    LetE sBig   : Bool        <- ITE (#aBig) (#sa) (#sb) ;
    LetE sSm    : Bool        <- ITE (#aBig) (#sb) (#sa) ;
    LetE xBig   : XK          <- ITE (#aBig) (#xa) (#xb) ;
    LetE xSm    : XK          <- ITE (#aBig) (#xb) (#xa) ;
    LetE big    : Bit (f + 5) <- Sll (zext (f + 1) (f + 5) (ITE (#aBig) (#siga) (#sigb))) (cst (f + 5) 3) ;
    LetE sm     : Bit (f + 5) <- Sll (zext (f + 1) (f + 5) (ITE (#aBig) (#sigb) (#siga))) (cst (f + 5) 3) ;
    LETE al     : AlignK (f + 5) <-
                  alignAdd (f + 5) sBig sSm xBig xSm big sm ;
    LetE r      : Bit (f + 5) <- ##al`"r" ;
    LetE st     : Bool        <- ##al`"st" ;
    LetE xR     : XK          <- Add [ #xBig ; cst (e + 3) 1 ] ;
    LetE sR     : Bool        <- ITE (And [ isZero (#r) ; Not (#st) ]) (Eq (#rm) (cst 3 RmRdn)) (#sBig) ;
    LETE nrm    : OK          <- normRound (f + 5) sR xR r st rm ;
    (* Special operands. *)
    LetE anyNaN : Bool        <- Or [ ##ua`"nan" ; ##ub`"nan" ] ;
    LetE anySN  : Bool        <- Or [ ##ua`"snan" ; ##ub`"snan" ] ;
    LetE infInf : Bool        <- And [ ##ua`"inf" ; ##ub`"inf" ; Not (Eq (#sa) (#sb)) ] ;
    LetE zz     : Bool        <- And [ ##ua`"zero" ; ##ub`"zero" ] ;
    LetE zzSign : Bool        <- ITE (Eq (#sa) (#sb)) (#sa) (Eq (#rm) (cst 3 RmRdn)) ;
    RetE (ITE (#anyNaN) (mkOut qnanE (mkFlags (#anySN) (ConstBool false) (ConstBool false) (ConstBool false) (ConstBool false)))
         (ITE (#infInf) (mkOut qnanE (mkFlags (ConstBool true) (ConstBool false) (ConstBool false) (ConstBool false) (ConstBool false)))
         (ITE (##ua`"inf") (mkOut (#a) noFlags)
         (ITE (##ub`"inf") (mkOut (#b) noFlags)
         (ITE (#zz) (mkOut (zeroE (#zzSign)) noFlags)
         (ITE (##ua`"zero") (mkOut (#b) noFlags)
         (ITE (##ub`"zero") (mkOut (#a) noFlags)
         (#nrm)))))))).

  (* ---------------------------------------------------------------------------
   * 6. MUL  (given the exact `2p`-bit significand product)
   * --------------------------------------------------------------------------- *)

  Definition mulFinish (rm : ty (Bit 3)) (ua ub : ty UK) (prod : ty (Bit (2 * f + 2))) : LetExpr ty OK :=
    LetE s      : Bool <- Xor [ ##ua`"sign" ; ##ub`"sign" ] ;
    LetE xP     : XK   <- Add [ ##ua`"exp" ; ##ub`"exp" ; cst (e + 3) (1 - expOff) ] ;
    LetE noSt   : Bool <- ConstBool false ;
    LETE nrm    : OK   <- normRound (2 * f + 2) s xP prod noSt rm ;
    LetE anyNaN : Bool <- Or [ ##ua`"nan" ; ##ub`"nan" ] ;
    LetE invP   : Bool <- Or [ And [ ##ua`"inf" ; ##ub`"zero" ] ; And [ ##ua`"zero" ; ##ub`"inf" ] ] ;
    LetE nv     : Bool <- Or [ ##ua`"snan" ; ##ub`"snan" ; #invP ] ;
    RetE (ITE (Or [ #anyNaN ; #invP ])
              (mkOut qnanE (mkFlags (#nv) (ConstBool false) (ConstBool false) (ConstBool false) (ConstBool false)))
         (ITE (Or [ ##ua`"inf" ; ##ub`"inf" ]) (mkOut (infE (#s)) noFlags)
         (ITE (Or [ ##ua`"zero" ; ##ub`"zero" ]) (mkOut (zeroE (#s)) noFlags)
         (#nrm)))).

  (* ---------------------------------------------------------------------------
   * 7. FUSED MULTIPLY-ADD  (c already negated for MSUB / NMADD; `negProd` for NMSUB / NMADD)
   * --------------------------------------------------------------------------- *)

  Definition fmaFinish (rm : ty (Bit 3)) (c : ty FB) (ua ub uc : ty UK) (negProd : ty Bool)
    (prod : ty (Bit (2 * f + 2))) : LetExpr ty OK :=
    LetE sp     : Bool            <- Xor [ ##ua`"sign" ; ##ub`"sign" ; #negProd ] ;
    LetE sc     : Bool            <- ##uc`"sign" ;
    LetE xc     : XK              <- ##uc`"exp" ;
    LetE top    : Bool            <- bitSet prod (2 * f + 1) ;
    LetE pn     : Bit (2 * f + 2) <- ITE (#top) (#prod) (Sll (#prod) (cst (2 * f + 2) 1)) ;
    LetE xp     : XK              <- Add [ ##ua`"exp" ; ##ub`"exp" ;
                                           ITE (#top) (cst (e + 3) (1 - expOff)) (cst (e + 3) (0 - expOff)) ] ;
    LetE pext   : Bit (2 * f + 6) <- Sll (zext (2 * f + 2) (2 * f + 6) (#pn)) (cst (2 * f + 6) 3) ;
    LetE sigc   : Bit (f + 1)     <- ##uc`"sig" ;
    LetE cext   : Bit (2 * f + 6) <- Sll (zext (f + 1) (2 * f + 6) (#sigc)) (cst (2 * f + 6) (f + 4)) ;
    LetE xGt    : Bool            <- Slt (#xc) (#xp) ;
    LetE xEq    : Bool            <- Eq (#xp) (#xc) ;
    LetE pBig   : Bool            <- Or [ ##uc`"zero" ; #xGt ; And [ #xEq ; Not (Ult (#pext) (#cext)) ] ] ;
    LetE cz     : Bit (2 * f + 6) <- ITE (##uc`"zero") (cst (2 * f + 6) 0) (#cext) ;
    LetE sBig   : Bool            <- ITE (#pBig) (#sp) (#sc) ;
    LetE sSm    : Bool            <- ITE (#pBig) (#sc) (#sp) ;
    LetE xBig   : XK              <- ITE (#pBig) (#xp) (#xc) ;
    LetE xSm    : XK              <- ITE (#pBig) (#xc) (#xp) ;
    LetE big    : Bit (2 * f + 6) <- ITE (#pBig) (#pext) (#cz) ;
    LetE sm     : Bit (2 * f + 6) <- ITE (#pBig) (#cz) (#pext) ;
    LETE al     : AlignK (2 * f + 6) <-
                  alignAdd (2 * f + 6) sBig sSm xBig xSm big sm ;
    LetE r      : Bit (2 * f + 6) <- ##al`"r" ;
    LetE st     : Bool            <- ##al`"st" ;
    LetE xR     : XK              <- Add [ #xBig ; cst (e + 3) 1 ] ;
    LetE sR     : Bool            <- ITE (And [ isZero (#r) ; Not (#st) ]) (Eq (#rm) (cst 3 RmRdn)) (#sBig) ;
    LETE nrm    : OK              <- normRound (2 * f + 6) sR xR r st rm ;
    (* Special operands. *)
    LetE anyNaN : Bool <- Or [ ##ua`"nan" ; ##ub`"nan" ; ##uc`"nan" ] ;
    LetE invP   : Bool <- Or [ And [ ##ua`"inf" ; ##ub`"zero" ] ; And [ ##ua`"zero" ; ##ub`"inf" ] ] ;
    LetE pInf   : Bool <- Or [ ##ua`"inf" ; ##ub`"inf" ] ;
    LetE pZero  : Bool <- Or [ ##ua`"zero" ; ##ub`"zero" ] ;
    LetE infCan : Bool <- And [ #pInf ; ##uc`"inf" ; Not (Eq (#sp) (#sc)) ] ;
    LetE nvN    : Bool <- Or [ ##ua`"snan" ; ##ub`"snan" ; ##uc`"snan" ; #invP ] ;
    LetE zSign  : Bool <- ITE (Eq (#sp) (#sc)) (#sp) (Eq (#rm) (cst 3 RmRdn)) ;
    RetE (ITE (Or [ #anyNaN ; #invP ])
              (mkOut qnanE (mkFlags (#nvN) (ConstBool false) (ConstBool false) (ConstBool false) (ConstBool false)))
         (ITE (#infCan) (mkOut qnanE (mkFlags (ConstBool true) (ConstBool false) (ConstBool false) (ConstBool false) (ConstBool false)))
         (ITE (#pInf) (mkOut (infE (#sp)) noFlags)
         (ITE (##uc`"inf") (mkOut (#c) noFlags)
         (ITE (And [ #pZero ; ##uc`"zero" ]) (mkOut (zeroE (#zSign)) noFlags)
         (ITE (#pZero) (mkOut (#c) noFlags)
         (#nrm))))))).

  (* ---------------------------------------------------------------------------
   * 8. MIN / MAX / SIGN INJECTION
   * --------------------------------------------------------------------------- *)

  (* minimumNumber / maximumNumber, with -0 < +0.  `nanProp` (Zfa FMINM / FMAXM, IEEE 754-2019
   * minimum / maximum): a NaN input gives the canonical NaN. *)
  Definition minMax (isMax nanProp : ty Bool) (a b : ty FB) (ua ub : ty UK) : LetExpr ty OK :=
    LetE sa   : Bool        <- ##ua`"sign" ;
    LetE sb   : Bool        <- ##ub`"sign" ;
    LetE ma   : Bit (f + e) <- magOf a ;
    LetE mb   : Bit (f + e) <- magOf b ;
    LetE lt   : Bool        <- Or [ And [ #sa ; Not (#sb) ] ;
                                    And [ Not (#sa) ; Not (#sb) ; Ult (#ma) (#mb) ] ;
                                    And [ #sa ; #sb ; Ult (#mb) (#ma) ] ] ;
    LetE pick : FB          <- ITE (Xor [ #lt ; #isMax ]) (#a) (#b) ;
    LetE nv   : Bool        <- Or [ ##ua`"snan" ; ##ub`"snan" ] ;
    LetE fl   : Bit 5       <- mkFlags (#nv) (ConstBool false) (ConstBool false) (ConstBool false) (ConstBool false) ;
    RetE (mkOut (ITE (Or [ And [ ##ua`"nan" ; ##ub`"nan" ] ;
                           And [ #nanProp ; Or [ ##ua`"nan" ; ##ub`"nan" ] ] ]) qnanE
                (ITE (##ua`"nan") (#b)
                (ITE (##ub`"nan") (#a)
                (#pick)))) (#fl)).

  (* `kind`: 0 = SGNJ, 1 = SGNJN, 2 = SGNJX.  No flags, no NaN canonicalization. *)
  Definition sgnInj (kind : ty (Bit 2)) (a b : ty FB) : LetExpr ty OK :=
    LetE sa : Bool <- isNotZero (TruncMsb 1 (f + e) (#a)) ;
    LetE sb : Bool <- isNotZero (TruncMsb 1 (f + e) (#b)) ;
    LetE s  : Bool <- ITE (Eq (#kind) (cst 2 0)) (#sb)
                     (ITE (Eq (#kind) (cst 2 1)) (Not (#sb)) (Xor [ #sa ; #sb ])) ;
    RetE (mkOut (packSigned (#s) (magOf a)) noFlags).

  (* ---------------------------------------------------------------------------
   * 9. INTEGER CONVERSIONS, COMPARISONS, CLASSIFICATION
   * --------------------------------------------------------------------------- *)

  Definition mkIntOut (xres : Expr ty (Bit xlen)) (flags : Expr ty (Bit 5)) : Expr ty (IntOutK xlen) :=
    STRUCT { "xres" ::= xres ; "flags" ::= flags }.

  Definition nvFlag (nv : Expr ty Bool) : Expr ty (Bit 5) :=
    mkFlags nv (ConstBool false) (ConstBool false) (ConstBool false) (ConstBool false).

  (* Low 32 bits, sign-extended to XLEN. *)
  Definition sext32 (v : ty (Bit xlen)) : Expr ty (Bit xlen) :=
    Or [ And [ #v ; cst xlen (2 ^ 32 - 1) ] ;
         ITE (bitSet v 31) (cst xlen (2 ^ xlen - 2 ^ 32)) (cst xlen 0) ].

  (* FCVT.{W,WU,L,LU}: round to an integer with the rounding mode, then saturate.
   * Valid range (after rounding): signed [-2^(W-1), 2^(W-1) - 1], unsigned [0, 2^W - 1].
   * NaN and too-large positive values give the maximum, too-large negative values the minimum;
   * those set NV (and not NX).  32-bit results are sign-extended to XLEN. *)
  Definition fpToInt (rm : ty (Bit 3)) (isSigned is64 : ty Bool) (ua : ty UK) : LetExpr ty (IntOutK xlen) :=
    LetE s       : Bool                 <- ##ua`"sign" ;
    LetE xv      : XK                   <- ##ua`"exp" ;
    LetE big     : Bool                 <- Slt (cst (e + 3) (xlen + 1 + expOff)) (#xv) ;
    LetE sh      : XK                   <- Sub (#xv) (cst (e + 3) (f + expOff)) ;
    LetE shNeg   : Bool                 <- Slt (#sh) (cst (e + 3) 0) ;
    LetE amtR0   : XK                   <- Neg (#sh) ;
    LetE amtR    : XK                   <- ITE (Ult (#amtR0) (cst (e + 3) (xlen + f + 4))) (#amtR0) (cst (e + 3) (xlen + f + 4)) ;
    LetE sig     : Bit (f + 1)          <- ##ua`"sig" ;
    LetE base    : Bit (xlen + f + 4)   <- Sll (zext (f + 1) (xlen + f + 4) (#sig)) (cst (xlen + f + 4) 2) ;
    LetE nn      : Bit (xlen + f + 4)   <- ITE (#shNeg) (Srl (#base) (#amtR))
                                            (ITE (#big) (cst (xlen + f + 4) 0) (Sll (#base) (#sh))) ;
    LetE stk     : Bool                 <- And [ #shNeg ; isNotZero (And [ #base ; Not (Sll (cst (xlen + f + 4) (-1)) (#amtR)) ]) ] ;
    LetE lsb     : Bool                 <- bitSet nn 2 ;
    LetE g       : Bool                 <- bitSet nn 1 ;
    LetE r       : Bool                 <- Or [ bitSet nn 0 ; #stk ] ;
    LetE inc     : Bool                 <- roundInc rm s lsb g r ;
    LetE inexact : Bool                 <- Or [ #g ; #r ] ;
    LetE mm      : Bit (xlen + f + 4)   <- Add [ Srl (#nn) (cst (xlen + f + 4) 2) ; ITE (#inc) (cst (xlen + f + 4) 1) (cst (xlen + f + 4) 0) ] ;
    LetE posLim  : Bit (xlen + f + 4)   <- ITE (#is64)
                                            (ITE (#isSigned) (cst (xlen + f + 4) (2 ^ 63 - 1)) (cst (xlen + f + 4) (2 ^ 64 - 1)))
                                            (ITE (#isSigned) (cst (xlen + f + 4) (2 ^ 31 - 1)) (cst (xlen + f + 4) (2 ^ 32 - 1))) ;
    LetE negLim  : Bit (xlen + f + 4)   <- ITE (#isSigned)
                                            (ITE (#is64) (cst (xlen + f + 4) (2 ^ 63)) (cst (xlen + f + 4) (2 ^ 31)))
                                            (cst (xlen + f + 4) 0) ;
    LetE inRange : Bool                 <- And [ Not (#big) ; Not (##ua`"inf") ; Not (##ua`"nan") ;
                                                 Not (Ult (ITE (#s) (#negLim) (#posLim)) (#mm)) ] ;
    LetE val     : Bit xlen             <- trunc (xlen + f + 4) xlen (ITE (#s) (Neg (#mm)) (#mm)) ;
    LetE satPos  : Bit xlen             <- trunc (xlen + f + 4) xlen (#posLim) ;
    LetE satNeg  : Bit xlen             <- trunc (xlen + f + 4) xlen (Neg (#negLim)) ;
    LetE sat     : Bit xlen             <- ITE (And [ #s ; Not (##ua`"nan") ]) (#satNeg) (#satPos) ;
    LetE raw     : Bit xlen             <- ITE (##ua`"zero") (cst xlen 0) (ITE (#inRange) (#val) (#sat)) ;
    LetE res     : Bit xlen             <- ITE (#is64) (#raw) (sext32 raw) ;
    LetE nv      : Bool                 <- And [ Not (##ua`"zero") ; Not (#inRange) ] ;
    LetE nx      : Bool                 <- And [ Not (##ua`"zero") ; #inRange ; #inexact ] ;
    RetE (mkIntOut (#res) (mkFlags (#nv) (ConstBool false) (ConstBool false) (ConstBool false) (#nx))).

  (* FCVT.fmt.{W,WU,L,LU}: the low 32 bits (or all 64) of `x`, signed or unsigned, rounded. *)
  Definition intToFp (rm : ty (Bit 3)) (isSigned is64 : ty Bool) (x : ty (Bit xlen)) : LetExpr ty OK :=
    LetE mask : Bit xlen           <- ITE (#is64) (cst xlen (-1)) (cst xlen (2 ^ 32 - 1)) ;
    LetE sb   : Bool               <- ITE (#is64) (bitSet x (xlen - 1)) (bitSet x 31) ;
    LetE neg  : Bool               <- And [ #isSigned ; #sb ] ;
    LetE mag  : Bit xlen           <- And [ ITE (#neg) (Neg (#x)) (#x) ; #mask ] ;
    LetE wsig : Bit (xlen + f + 3) <- Sll (zext xlen (xlen + f + 3) (#mag)) (cst (xlen + f + 3) (f + 3)) ;
    LetE xtop : XK                 <- cst (e + 3) (xlen - 1 + expOff) ;
    LetE noSt : Bool               <- ConstBool false ;
    normRound (xlen + f + 3) neg xtop wsig noSt rm.

  (* FEQ (quiet), FLT / FLE (signaling; with `quiet`, Zfa FLTQ / FLEQ: NV only for signaling
   * NaNs).  `kind`: 0 = EQ, 1 = LT, 2 = LE. *)
  Definition fpCompare (kind : ty (Bit 2)) (quiet : ty Bool) (a b : ty FB) (ua ub : ty UK)
    : LetExpr ty (IntOutK xlen) :=
    LetE sa     : Bool        <- ##ua`"sign" ;
    LetE sb     : Bool        <- ##ub`"sign" ;
    LetE ma     : Bit (f + e) <- magOf a ;
    LetE mb     : Bit (f + e) <- magOf b ;
    LetE anyNaN : Bool        <- Or [ ##ua`"nan" ; ##ub`"nan" ] ;
    LetE zz     : Bool        <- And [ ##ua`"zero" ; ##ub`"zero" ] ;
    LetE eq     : Bool        <- And [ Not (#anyNaN) ; Or [ Eq (#a) (#b) ; #zz ] ] ;
    LetE lt     : Bool        <- And [ Not (#anyNaN) ; Not (#zz) ;
                                       Or [ And [ #sa ; Not (#sb) ] ;
                                            And [ Not (#sa) ; Not (#sb) ; Ult (#ma) (#mb) ] ;
                                            And [ #sa ; #sb ; Ult (#mb) (#ma) ] ] ] ;
    LetE isEq   : Bool        <- Eq (#kind) (cst 2 0) ;
    LetE isLt   : Bool        <- Eq (#kind) (cst 2 1) ;
    LetE res    : Bool        <- ITE (#isEq) (#eq) (ITE (#isLt) (#lt) (Or [ #lt ; #eq ])) ;
    LetE nv     : Bool        <- ITE (Or [ #isEq ; #quiet ]) (Or [ ##ua`"snan" ; ##ub`"snan" ]) (#anyNaN) ;
    RetE (mkIntOut (ITE (#res) (cst xlen 1) (cst xlen 0)) (nvFlag (#nv))).

  (* FCLASS: one-hot 10-bit mask. *)
  Definition fpClass (a : ty FB) (ua : ty UK) : LetExpr ty (IntOutK xlen) :=
    LetE s    : Bool  <- ##ua`"sign" ;
    LetE ef   : Bit e <- TruncMsb e f (magOf a) ;
    LetE sub  : Bool  <- And [ isZero (#ef) ; Not (##ua`"zero") ] ;
    LetE norm : Bool  <- And [ Not (isZero (#ef)) ; Not (##ua`"inf") ; Not (##ua`"nan") ] ;
    LetE snan : Bool  <- ##ua`"snan" ;
    LetE qnan : Bool  <- And [ ##ua`"nan" ; Not (#snan) ] ;
    RetE (mkIntOut
      (Or [ ITE (And [ #s ; ##ua`"inf" ])        (cst xlen 1)   (cst xlen 0) ;
            ITE (And [ #s ; #norm ])             (cst xlen 2)   (cst xlen 0) ;
            ITE (And [ #s ; #sub ])              (cst xlen 4)   (cst xlen 0) ;
            ITE (And [ #s ; ##ua`"zero" ])       (cst xlen 8)   (cst xlen 0) ;
            ITE (And [ Not (#s) ; ##ua`"zero" ]) (cst xlen 16)  (cst xlen 0) ;
            ITE (And [ Not (#s) ; #sub ])        (cst xlen 32)  (cst xlen 0) ;
            ITE (And [ Not (#s) ; #norm ])       (cst xlen 64)  (cst xlen 0) ;
            ITE (And [ Not (#s) ; ##ua`"inf" ])  (cst xlen 128) (cst xlen 0) ;
            ITE (#snan)                          (cst xlen 256) (cst xlen 0) ;
            ITE (#qnan)                          (cst xlen 512) (cst xlen 0) ])
      noFlags).

  (* Zfa FROUND / FROUNDNX: round to an integral value in the same format with the rounding mode
   * (`nx`: raise NX when inexact, FROUNDNX).  NaN -> canonical NaN (NV for a signaling NaN);
   * infinities, zeros and values with unbiased exponent `>= f` (already integral) are returned
   * unchanged.  Otherwise the integer magnitude `m <= 2^f` is computed like `fpToInt` and packed
   * back exactly (`normRound` with no rounding; `m = 0` gives a zero with the input's sign). *)
  Definition fpRound (rm : ty (Bit 3)) (nx : ty Bool) (a : ty FB) (ua : ty UK) : LetExpr ty OK :=
    LetE s       : Bool        <- ##ua`"sign" ;
    LetE xv      : XK          <- ##ua`"exp" ;
    LetE intg    : Bool        <- Slt (cst (e + 3) (f - 1 + expOff)) (#xv) ;
    LetE shR0    : XK          <- Sub (cst (e + 3) (f + expOff)) (#xv) ;
    LetE shR     : XK          <- ITE (Ult (#shR0) (cst (e + 3) (f + 4))) (#shR0) (cst (e + 3) (f + 4)) ;
    LetE sig     : Bit (f + 1) <- ##ua`"sig" ;
    LetE base    : Bit (f + 4) <- Sll (zext (f + 1) (f + 4) (#sig)) (cst (f + 4) 2) ;
    LetE nn      : Bit (f + 4) <- Srl (#base) (#shR) ;
    LetE stk     : Bool        <- isNotZero (And [ #base ; Not (Sll (cst (f + 4) (-1)) (#shR)) ]) ;
    LetE lsb     : Bool        <- bitSet nn 2 ;
    LetE g       : Bool        <- bitSet nn 1 ;
    LetE r       : Bool        <- Or [ bitSet nn 0 ; #stk ] ;
    LetE inc     : Bool        <- roundInc rm s lsb g r ;
    LetE inexact : Bool        <- Or [ #g ; #r ] ;
    LetE m       : Bit (f + 4) <- Add [ Srl (#nn) (cst (f + 4) 2) ; ITE (#inc) (cst (f + 4) 1) (cst (f + 4) 0) ] ;
    LetE xtop    : XK          <- cst (e + 3) (f + 3 + expOff) ;
    LetE noSt    : Bool        <- ConstBool false ;
    LETE nrm     : OK          <- normRound (f + 4) s xtop m noSt rm ;
    RetE (ITE (##ua`"nan") (mkOut qnanE (mkFlags (##ua`"snan") (ConstBool false) (ConstBool false) (ConstBool false) (ConstBool false)))
         (ITE (Or [ ##ua`"inf" ; ##ua`"zero" ; #intg ]) (mkOut (#a) noFlags)
         (mkOut (##nrm`"res") (mkFlags (ConstBool false) (ConstBool false) (ConstBool false) (ConstBool false)
                                       (And [ #nx ; #inexact ]))))).

  (* Zfa FLI: the 32-entry constant table in this format, selected by a 5-bit index.  Entries are
   * `(-1)^s * m * 2^k`, except entry 1 (the minimum positive normal), 30 (+inf) and 31 (the
   * canonical NaN); a value above the format's range gives +inf.  Not an FPU operation: the
   * parent writes the constant with `SpecFpu.fpuWrite` (see `SpecFpu.fliConst`). *)
  Definition fliEncode (t : Z * Z * Z) : Z :=
    let '(sg, m, k) := t in
    let p := Z.log2 m in
    let x := k + p in
    let mag := if fpEmax <? x then infMagZ
               else if fpEmin <=? x then (x + fpBias) * 2 ^ f + (m - 2 ^ p) * 2 ^ (f - p)
               else m * 2 ^ (k - fpEmin + f) in
    sg * 2 ^ (f + e) + mag.

  Definition fliTable : list Z :=
    map fliEncode [ (1, 1, 0) ] ++ [ 2 ^ f ] ++
    map fliEncode [ (0, 1, -16) ; (0, 1, -15) ; (0, 1, -8) ; (0, 1, -7) ; (0, 1, -4) ; (0, 1, -3) ;
                    (0, 1, -2) ; (0, 5, -4) ; (0, 3, -3) ; (0, 7, -4) ; (0, 1, -1) ; (0, 5, -3) ;
                    (0, 3, -2) ; (0, 7, -3) ; (0, 1, 0) ; (0, 5, -2) ; (0, 3, -1) ; (0, 7, -2) ;
                    (0, 1, 1) ; (0, 5, -1) ; (0, 3, 0) ; (0, 1, 2) ; (0, 1, 3) ; (0, 1, 4) ;
                    (0, 1, 7) ; (0, 1, 8) ; (0, 1, 15) ; (0, 1, 16) ] ++
    [ infMagZ ; qnanMagZ ].

  Fixpoint fliSel (idx : Expr ty (Bit 5)) (k : Z) (vs : list Z) : Expr ty FB :=
    match vs with
    | nil => qnanE
    | v :: rest => ITE (Eq idx (cst 5 k)) (cst (f + e + 1) v) (fliSel idx (k + 1) rest)
    end.

  Definition fliConstE (idx : Expr ty (Bit 5)) : Expr ty FB := fliSel idx 0 fliTable.

  (* ---------------------------------------------------------------------------
   * 10. PIPE UNIT (everything except DIV and SQRT)
   * --------------------------------------------------------------------------- *)

  Definition fpRes (o : ty OK) : Expr ty (FpResK e f xlen) :=
    STRUCT { "res" ::= ##o`"res" ; "xres" ::= @cst ty xlen 0 ; "flags" ::= ##o`"flags" }.

  Definition intRes (o : ty (IntOutK xlen)) : Expr ty (FpResK e f xlen) :=
    STRUCT { "res" ::= @cst ty (f + e + 1) 0 ; "xres" ::= ##o`"xres" ; "flags" ::= ##o`"flags" }.

  Definition pipeInfoOf (req : ty (FpReqK e f xlen)) : LetExpr ty (PipeInfoK e f xlen) :=
    LetE op      : FpOpDK     <- ##req`"op" ;
    LetE a       : FB         <- ##req`"a" ;
    LetE b       : FB         <- ##req`"b" ;
    LetE c       : FB         <- ##req`"c" ;
    LetE b2      : FB         <- flipSign (And [ ##op`"add" ; ##op`"negB" ]) b ;
    LetE c2      : FB         <- flipSign (And [ ##op`"fma" ; ##op`"negAdd" ]) c ;
    LETE ua      : UK         <- fpUnpack a ;
    LETE ub      : UK         <- fpUnpack b2 ;
    LETE uc      : UK         <- fpUnpack c2 ;
    @RetE ty (PipeInfoK e f xlen) (STRUCT {
      "op"      ::= #op ;
      "x"       ::= ##req`"x" ;
      "rm"      ::= ##req`"rm" ;
      "a"       ::= #a ;
      "b2"      ::= #b2 ;
      "c2"      ::= #c2 ;
      "ua"      ::= #ua ;
      "ub"      ::= #ub ;
      "uc"      ::= #uc ;
      "negProd" ::= And [ ##op`"fma" ; ##op`"negProd" ]
    }).

  Definition pipeFinishCore (info : ty (PipeInfoK e f xlen)) (prod : ty (Bit (2 * f + 2)))
    : LetExpr ty (FpResK e f xlen) :=
    LetE op    : FpOpDK     <- ##info`"op" ;
    LetE x     : Bit xlen   <- ##info`"x" ;
    LetE rm    : Bit 3      <- ##info`"rm" ;
    LetE a     : FB         <- ##info`"a" ;
    LetE b2    : FB         <- ##info`"b2" ;
    LetE c2    : FB         <- ##info`"c2" ;
    LetE ua    : UK         <- ##info`"ua" ;
    LetE ub    : UK         <- ##info`"ub" ;
    LetE uc    : UK         <- ##info`"uc" ;
    LetE negP  : Bool       <- ##info`"negProd" ;
    LetE isMax : Bool       <- ##op`"isMax" ;
    LetE nanP  : Bool       <- ##op`"nanProp" ;
    LetE md    : Bit 2      <- ##op`"mode" ;
    LetE qt    : Bool       <- ##op`"quiet" ;
    LetE cvSg  : Bool       <- Not (##op`"unsigned") ;
    LetE cv64  : Bool       <- ##op`"wide" ;
    LetE rnx   : Bool       <- ##op`"nx" ;
    LETE oAdd  : OK         <- addCore rm a b2 ua ub ;
    LETE oMul  : OK         <- mulFinish rm ua ub prod ;
    LETE oFma  : OK         <- fmaFinish rm c2 ua ub uc negP prod ;
    LETE oMm   : OK         <- minMax isMax nanP a b2 ua ub ;
    LETE oSj   : OK         <- sgnInj md a b2 ;
    LETE oFI   : IntOutK xlen <- fpToInt rm cvSg cv64 ua ;
    LETE oIF   : OK         <- intToFp rm cvSg cv64 x ;
    LETE oCmp  : IntOutK xlen <- fpCompare md qt a b2 ua ub ;
    LETE oCls  : IntOutK xlen <- fpClass a ua ;
    LETE oRnd  : OK         <- fpRound rm rnx a ua ;
    RetE (ITE (##op`"add") (fpRes oAdd)
         (ITE (##op`"mul") (fpRes oMul)
         (ITE (##op`"minmax") (fpRes oMm)
         (ITE (##op`"sgnj") (fpRes oSj)
         (ITE (##op`"cvtFI") (intRes oFI)
         (ITE (##op`"cvtIF") (fpRes oIF)
         (ITE (##op`"cmp") (intRes oCmp)
         (ITE (##op`"fclass") (intRes oCls)
         (ITE (##op`"round") (fpRes oRnd)
         (fpRes oFma)))))))))).

  (* The `p x p -> 2p` significand product. *)
  Definition sigProduct (siga sigb : ty (Bit (f + 1))) : Expr ty (Bit (2 * f + 2)) :=
    Mul [ zext (f + 1) (2 * f + 2) (#siga) ; zext (f + 1) (2 * f + 2) (#sigb) ].

  Definition pipeSpec (req : ty (FpReqK e f xlen)) : LetExpr ty (FpResK e f xlen) :=
    LETE info : PipeInfoK e f xlen <- pipeInfoOf req ;
    LetE ua   : UK              <- ##info`"ua" ;
    LetE ub   : UK              <- ##info`"ub" ;
    LetE siga : Bit (f + 1)     <- ##ua`"sig" ;
    LetE sigb : Bit (f + 1)     <- ##ub`"sig" ;
    LetE prod : Bit (2 * f + 2) <- sigProduct siga sigb ;
    pipeFinishCore info prod.

  (* ---------------------------------------------------------------------------
   * 11. DIVIDE UNIT
   * --------------------------------------------------------------------------- *)

  Definition divInfoOf (req : ty (FpReqK e f xlen)) : LetExpr ty (DivInfoK e f) :=
    LetE a  : FB <- ##req`"a" ;
    LetE b  : FB <- ##req`"b" ;
    LETE ua : UK <- fpUnpack a ;
    LETE ub : UK <- fpUnpack b ;
    @RetE ty (DivInfoK e f) (STRUCT { "rm" ::= ##req`"rm" ; "ua" ::= #ua ; "ub" ::= #ub }).

  (* `q = floor(siga * 2^(f + 2) / sigb)` (`p + 1` or `p + 2` bits), `st` = remainder is non-zero.
   * Bit `f + 2` of `q` has weight `2^(xa - xb)`. *)
  Definition divFinishCore (info : ty (DivInfoK e f)) (q : ty (Bit (f + 3))) (st : ty Bool) : LetExpr ty OK :=
    LetE rm     : Bit 3 <- ##info`"rm" ;
    LetE ua     : UK    <- ##info`"ua" ;
    LetE ub     : UK    <- ##info`"ub" ;
    LetE s      : Bool  <- Xor [ ##ua`"sign" ; ##ub`"sign" ] ;
    LetE xq     : XK    <- Add [ Sub (##ua`"exp") (##ub`"exp") ; cst (e + 3) expOff ] ;
    LETE nrm    : OK    <- normRound (f + 3) s xq q st rm ;
    LetE anyNaN : Bool  <- Or [ ##ua`"nan" ; ##ub`"nan" ] ;
    LetE inv    : Bool  <- Or [ And [ ##ua`"inf" ; ##ub`"inf" ] ; And [ ##ua`"zero" ; ##ub`"zero" ] ] ;
    LetE nv     : Bool  <- Or [ ##ua`"snan" ; ##ub`"snan" ; #inv ] ;
    RetE (ITE (Or [ #anyNaN ; #inv ])
              (mkOut qnanE (mkFlags (#nv) (ConstBool false) (ConstBool false) (ConstBool false) (ConstBool false)))
         (ITE (##ua`"inf") (mkOut (infE (#s)) noFlags)
         (ITE (##ub`"inf") (mkOut (zeroE (#s)) noFlags)
         (ITE (##ua`"zero") (mkOut (zeroE (#s)) noFlags)
         (ITE (##ub`"zero") (mkOut (infE (#s)) (mkFlags (ConstBool false) (ConstBool true) (ConstBool false) (ConstBool false) (ConstBool false)))
         (#nrm)))))).

  Definition divNumer (siga : ty (Bit (f + 1))) : Expr ty (Bit (2 * f + 3)) :=
    Sll (zext (f + 1) (2 * f + 3) (#siga)) (cst (2 * f + 3) (f + 2)).

  Definition divDenom (sigb : ty (Bit (f + 1))) : Expr ty (Bit (2 * f + 3)) :=
    zext (f + 1) (2 * f + 3) (#sigb).

  Definition divSpec (req : ty (FpReqK e f xlen)) : LetExpr ty OK :=
    LETE info : DivInfoK e f    <- divInfoOf req ;
    LetE ua   : UK              <- ##info`"ua" ;
    LetE ub   : UK              <- ##info`"ub" ;
    LetE siga : Bit (f + 1)     <- ##ua`"sig" ;
    LetE sigb : Bit (f + 1)     <- ##ub`"sig" ;
    LetE nn   : Bit (2 * f + 3) <- divNumer siga ;
    LetE dd   : Bit (2 * f + 3) <- divDenom sigb ;
    LetE q    : Bit (f + 3)     <- trunc (2 * f + 3) (f + 3) (Div (#nn) (#dd)) ;
    LetE st   : Bool            <- isNotZero (Rem (#nn) (#dd)) ;
    divFinishCore info q st.

  (* ---------------------------------------------------------------------------
   * 12. SQUARE-ROOT UNIT
   * --------------------------------------------------------------------------- *)

  (* Radicand `sig << (f + 4 + odd(exp))`, in `[2^(2f+4), 2^(2f+6))`: its integer square root
   * has `f + 3` bits with the top one set, of weight `2^(exp >> 1)`. *)
  Definition sqrtInit (req : ty (FpReqK e f xlen)) : LetExpr ty (SqrtStateK e f) :=
    LetE a   : FB <- ##req`"a" ;
    LETE ua  : UK <- fpUnpack a ;
    LetE sig : Bit (f + 1) <- ##ua`"sig" ;
    (* Unbiased exponent parity: `exp - expOff` and `exp + expOff` have the same parity. *)
    LetE ex  : XK <- Add [ ##ua`"exp" ; cst (e + 3) expOff ] ;
    LetE odd : Bool <- bitSet ex 0 ;
    LetE rad : Bit (2 * f + 6) <-
      Sll (zext (f + 1) (2 * f + 6) (#sig)) (ITE (#odd) (cst (2 * f + 6) (f + 5)) (cst (2 * f + 6) (f + 4))) ;
    LetE info : SqrtInfoK e f <- STRUCT { "rm" ::= ##req`"rm" ; "a" ::= #a ; "ua" ::= #ua } ;
    LetE rem0 : Bit (f + 5) <- cst (f + 5) 0 ;
    LetE root0 : Bit (f + 3) <- cst (f + 3) 0 ;
    @RetE ty (SqrtStateK e f) (STRUCT {
      "info" ::= #info ;
      "rad"  ::= #rad ;
      "rem"  ::= #rem0 ;
      "root" ::= #root0
    }).

  Definition sqrtStep (st : ty (SqrtStateK e f)) : LetExpr ty (SqrtStateK e f) :=
    LetE rad   : Bit (2 * f + 6) <- ##st`"rad" ;
    LetE rem   : Bit (f + 5)     <- ##st`"rem" ;
    LetE root  : Bit (f + 3)     <- ##st`"root" ;
    LetE top2  : Bit (f + 5)     <- trunc (2 * f + 6) (f + 5) (Srl (#rad) (cst (2 * f + 6) (2 * f + 4))) ;
    LetE remS  : Bit (f + 5)     <- Or [ Sll (#rem) (cst (f + 5) 2) ; #top2 ] ;
    LetE trial : Bit (f + 5)     <- Or [ Sll (zext (f + 3) (f + 5) (#root)) (cst (f + 5) 2) ; cst (f + 5) 1 ] ;
    LetE ge    : Bool            <- Not (Ult (#remS) (#trial)) ;
    @RetE ty (SqrtStateK e f)
      (((##st `{ "rad" <- Sll (#rad) (cst (2 * f + 6) 2) })
              `{ "rem" <- ITE (#ge) (Sub (#remS) (#trial)) (#remS) })
              `{ "root" <- Or [ Sll (#root) (cst (f + 3) 1) ; ITE (#ge) (cst (f + 3) 1) (cst (f + 3) 0) ] }).

  Fixpoint sqrtIter (n : nat) (st : ty (SqrtStateK e f)) : LetExpr ty (SqrtStateK e f) :=
    match n with
    | 0%nat => RetE (#st)
    | S m   => LETE nx : SqrtStateK e f <- sqrtStep st ; sqrtIter m nx
    end.

  Definition sqrtFinish (st : ty (SqrtStateK e f)) : LetExpr ty OK :=
    LetE info : SqrtInfoK e f <- ##st`"info" ;
    LetE rm   : Bit 3       <- ##info`"rm" ;
    LetE a    : FB          <- ##info`"a" ;
    LetE ua   : UK          <- ##info`"ua" ;
    LetE root : Bit (f + 3) <- ##st`"root" ;
    LetE sti  : Bool        <- isNotZero (##st`"rem") ;
    (* `floor((exp - expOff) / 2) + expOff = floor((exp + expOff) / 2)`. *)
    LetE xr   : XK          <- Sra (Add [ ##ua`"exp" ; cst (e + 3) expOff ]) (cst 1 1) ;
    LetE pos  : Bool        <- ConstBool false ;
    LETE nrm  : OK          <- normRound (f + 3) pos xr root sti rm ;
    RetE (ITE (##ua`"nan") (mkOut qnanE (mkFlags (##ua`"snan") (ConstBool false) (ConstBool false) (ConstBool false) (ConstBool false)))
         (ITE (##ua`"zero") (mkOut (#a) noFlags)
         (ITE (##ua`"sign") (mkOut qnanE (mkFlags (ConstBool true) (ConstBool false) (ConstBool false) (ConstBool false) (ConstBool false)))
         (ITE (##ua`"inf") (mkOut (#a) noFlags)
         (#nrm))))).

  Definition sqrtSteps : nat := Z.to_nat (f + 3).

  Definition sqrtSpec (req : ty (FpReqK e f xlen)) : LetExpr ty OK :=
    LETE s0 : SqrtStateK e f <- sqrtInit req ;
    LETE sn : SqrtStateK e f <- sqrtIter sqrtSteps s0 ;
    sqrtFinish sn.

  (* ---------------------------------------------------------------------------
   * 13. WHOLE SINGLE-FORMAT COMPUTE FUNCTION
   * --------------------------------------------------------------------------- *)

  Definition fpuCompute (req : ty (FpReqK e f xlen)) : LetExpr ty (FpResK e f xlen) :=
    LetE op  : FpOpDK              <- ##req`"op" ;
    LETE oP  : FpResK e f xlen     <- pipeSpec req ;
    LETE oD  : OK                  <- divSpec req ;
    LETE oS  : OK                  <- sqrtSpec req ;
    RetE (ITE (##op`"div") (fpRes oD) (ITE (##op`"sqrt") (fpRes oS) (#oP))).

End FpCore.

(* ===========================================================================
 * 14. CONVERSION BETWEEN FORMATS  (FCVT.fmt2.fmt1)
 * =========================================================================== *)

Section FpCvt.
  Variable bm : bool.
  Variable e1 f1 e2 f2 : Z.
  Variable ty : Kind -> Type.

  (* Exponent arithmetic in the wider of the two exponent widths. *)
  Local Abbreviation ew := (Z.max e1 e2 + 3).
  (* Significand window: the source significand, padded to at least `f2 + 3` bits. *)
  Local Abbreviation ww := (Z.max (f1 + 1) (f2 + 3)).

  (* The (unbiased) exponent is clamped to `[emin2 - (f2 + 4), emax2 + 1]` before narrowing it to `e2 + 3`
   * bits: below, every bit is shifted out by the subnormal shift anyway; above, it overflows. *)
  Definition cvtFF (rm : ty (Bit 3)) (a : ty (FpBits e1 f1)) : LetExpr ty (FpOutK e2 f2) :=
    LETE ua   : FpUnpK e1 f1 <- fpUnpack bm e1 f1 ty a ;
    LetE s    : Bool         <- ##ua`"sign" ;
    (* Rebias from the source to the target internal exponent. *)
    LetE ex1  : Bit (e1 + 3) <- ##ua`"exp" ;
    (* Sign-extend `ex1` to `ew` bits by flipping its top bit, zero-extending, and subtracting the
     * flipped weight (folded into the rebias constant). *)
    LetE x1   : Bit ew       <- Add [ zext (e1 + 3) ew (Xor [ #ex1 ; cst (e1 + 3) (2 ^ (e1 + 2)) ]) ;
                                      cst ew (expOff bm e2 - expOff bm e1 - 2 ^ (e1 + 2)) ] ;
    LetE lo   : Bit ew       <- cst ew (fpEmin e2 - (f2 + 4) + expOff bm e2) ;
    LetE hi   : Bit ew       <- cst ew (fpEmax e2 + 1 + expOff bm e2) ;
    LetE below : Bool        <- Slt (#x1) (#lo) ;
    LetE above : Bool        <- Slt (#hi) (#x1) ;
    LetE xc   : Bit ew       <- ITE (#below) (#lo) (ITE (#above) (#hi) (#x1)) ;
    LetE x2   : Bit (e2 + 3) <- trunc ew (e2 + 3) (#xc) ;
    LetE sig1 : Bit (f1 + 1) <- ##ua`"sig" ;
    LetE wsig : Bit ww       <- Sll (zext (f1 + 1) ww (#sig1)) (cst ww (ww - (f1 + 1))) ;
    LetE noSt : Bool         <- ConstBool false ;
    LETE nrm  : FpOutK e2 f2 <- normRound bm e2 f2 ty ww s x2 wsig noSt rm ;
    RetE (ITE (##ua`"nan")
              (mkOut e2 f2 ty (qnanE e2 f2 ty)
                     (mkFlags ty (##ua`"snan") (ConstBool false) (ConstBool false) (ConstBool false) (ConstBool false)))
         (ITE (##ua`"inf") (mkOut e2 f2 ty (infE e2 f2 ty (#s)) (noFlags ty))
         (ITE (##ua`"zero") (mkOut e2 f2 ty (zeroE e2 f2 ty (#s)) (noFlags ty))
         (#nrm)))).
End FpCvt.
