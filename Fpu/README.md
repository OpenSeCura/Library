# Fpu: a generic RISC-V FPU in Guru

A single-format, format-ignorant FPU with parameters:

- `F`: the own format `(e, f)` (exponent bits, fraction bits); `FmtS` / `FmtD` / `FmtH` / `FmtQ` /
  `FmtB` = binary32 / 64 / 16 / 128, bfloat16.  FP registers are `fmtW F = e + f + 1` bits wide
  (own-format values are stored unboxed).
- `xlen`: the integer register width.
- `wlen`: the width of the narrow integer conversions (`1 <= wlen <= xlen`; RISC-V W / WU use 32).
  The core contains no fixed integer width.
- `narrow`: a static list of NaN-boxed narrow formats (example: `F = FmtS, narrow = [FmtH; FmtB]`).

Packets carry no format.  The operation is a tagged union of families with their options
(`SpecFpu.FpuOpK`), decoded once (`SpecFpu.decodeOp`) into the core's flat record `FpCore.FpOpDK`:

| Family | Options | RISC-V |
|---|---|---|
| `add` | `negB` | FADD / FSUB |
| `mul` | | FMUL |
| `fma` | `negProd`, `negAdd` | FMADD / FMSUB / FNMSUB / FNMADD |
| `div`, `sqrt` | | FDIV, FSQRT |
| `minmax` | `isMax`, `nanProp` | FMIN / FMAX; Zfa FMINM / FMAXM |
| `sgnj` | `mode` (0/1/2) | FSGNJ / FSGNJN / FSGNJX |
| `cmp` | `mode` (eq/lt/le), `quiet` | FEQ / FLT / FLE; Zfa FLTQ / FLEQ |
| `fclass` | | FCLASS |
| `cvtFI`, `cvtIF` | `unsigned`, `wide` (`xlen`-bit integer, else `wlen`-bit) | FCVT.{W,WU,L,LU}.fmt, FCVT.fmt.{W,WU,L,LU} |
| `round` | `nx` | Zfa FROUND / FROUNDNX |
| `cvtN` | `toNarrow`, `nidx` | FCVT with a boxed narrow format (`nidx` indexes `narrow`) |

The D-only Zfa ops (FCVTMOD.W.D, FMVH.X.D, FMVP.D.X) are out of scope.

## Spec and impl

Both are sets of Guru actions over a state tree, not packaged `Mod`s: the parent calls the actions
from its own rules.  They share the architectural state of `FpuArch.v`.

### Spec (`SpecFpu.v`)

State (`fpuArchTree flen`):

- `fpr_0 .. fpr_1f`: 32 registers of `flen` bits.
- `frm` (3 bits), `fflags` (5 bits), `fs` (2 bits, the `mstatus.FS` field).

Methods (always succeed, atomic):

- `fpuExec pkt x`: reads rs1 / rs2 / rs3 and `frm`, computes the result, writes `rd` if it is an f
  result, ORs the flags into `fflags`, sets `fs` to Dirty, and returns the integer result.
- `fpuRead idx` / `fpuWrite idx v`: raw register access; the write sets `fs` to Dirty.
- `frmRead` / `frmWrite`, `fflagsRead` / `fflagsWrite`, `fcsrRead` / `fcsrWrite`: the writes set
  `fs` to Dirty.
- `fsRead` / `fsWrite`.

Rules: none.

### Impl (`ImplFpu.v`)

State (`implTree ls`):

- The same architectural state as the spec.
- `ctl.pend` (32 bits): one bit per f register that is the destination of an operation in flight.
- `ctl.lpend` (32 bits): one bit per f register reserved by a load.
- `ctl.intBusy` (Bool): an integer-result operation is in flight.
- The state of each functional unit in `ls`.  The standard list `fpuFUs mul_stages mul_bps` is a
  pipe unit (everything except divide, square root and the narrow conversions), a divide unit, a
  square-root unit, and a narrow-conversion unit if `narrow` is non-empty.
  - The pipe unit has `mul_stages` stages; each does `mul_bps` bits of the shift-and-add
    multiplication of the significands, so `mul_stages * mul_bps` must be at least `f + 1`.
  - The divide and square-root units take `f + 3` iterations.

An f register is busy if its `pend` or `lpend` bit is set.

Methods (each has a ready flag; a call that is not ready changes nothing):

| Method | Ready when | Effect |
|---|---|---|
| `fpuIssue pkt x` : Bool | rs1 / rs2 / rs3 not busy; `rd` not busy (f result) or not `intBusy` (integer result); the accepting unit has room | Reads the operands, enqueues into the unit, sets the `pend` bit of `rd` or `intBusy`, sets `fs` to Dirty |
| `fpuIntResp` : Option (Bit xlen) | a unit's head is a finished integer-result operation | Dequeues it, ORs its flags into `fflags`, clears `intBusy` |
| `fpuReserve rd` : Bool | `rd` not busy | Sets the `lpend` bit of `rd`, sets `fs` to Dirty |
| `fpuFill rd v` : Bool | the `lpend` bit of `rd` is set | Writes `rd`, clears that bit |
| `fpuReadT idx` : Option (Bit flen), `fpuWriteT idx v` : Bool | `idx` not busy | The spec's `fpuRead` / `fpuWrite` |
| `fpuFflagsReadT`, `fpuFcsrReadT`, `fpuFflagsWriteT`, `fpuFcsrWriteT` | `pend = 0` and not `intBusy` | The spec's action |
| `fpuFrmRead`, `fpuFrmWrite`, `fpuFsRead`, `fpuFsWrite` | always | The spec's action |

Rules (`fpuImplRules`, which the parent adds to its rule list):

- One write-back rule per unit (`wbRule`): if the unit's head is a finished f result, write `rd`,
  OR the flags into `fflags`, clear the `pend` bit of `rd`, and dequeue.  Results are written back
  out of order across units.
- Each unit's own internal rules: the pipe unit's stage-advance rules and one step rule each for
  divide and square root.  The narrow-conversion unit has none.

## What is proved

Format condition `FmtOk G`: `2 <= f` and `f + 1 < 2^(e-1)` (`FmtOk_std`: S, D, H, Q, BF16 satisfy
it).  Integer condition: `0 <= xlen` and `xlen + 4 <= 7 * 2^(e-1)`.

- **Units** (`Proof/FpuUnitsProof.v`): the staged pipe, divide and square-root units compute exactly
  the core's `pipeSpec` / `divSpec` / `sqrtSpec` (`Pipe_/Div_/Sqrt_StageValAt_spec`), with
  controller theorems for each unit.
- **Exponent modes** (`Proof/FpCoreRefProof.v`): the biased hardware core and the unbiased reference
  core compute identical results (`fpuComputeRef_equiv`, `cvtFFRef_equiv`), under `FmtOk` and the
  integer condition.
- **Interface contract** (`Proof/FpuContract.v`, stated with Guru's `Interface.v`): the pipelined
  FPU, used only through its methods, behaves as the atomic spec.  `FpuView S a` relates an impl
  state to an abstract state `a`: the spec state with every accepted operation applied
  (`fa_arch`), the integer result not yet collected (`fa_int`) and the registers reserved by loads
  (`fa_resv`).  Each method moves `a` by its `*Step` relation (an accepted `fpuIssue pkt x` is the
  spec's `execSem`), a refused call changes nothing, and the internal rules do not change `a`.
  `fpu_contract` holds for any spec mode agreeing with the biased core; `fpu_contract_ref` is the
  instance for the standard fus and the reference core, under `FmtOk` and the integer condition.
  The contract says nothing about when a call is accepted (no liveness).
- **IEEE 754** (`FlocqProof/`): every operation of the reference core (`FpCoreRef.fpuComputeRef`,
  `FpCoreRef.cvtFFRef`) computes exactly the corresponding IEEE 754 operation of Flocq
  (`BinarySingleNaN`), together with the IEEE exception flags (see the table below).

The spec with `bm = false` (the reference core) is the spec of record: clients state their FPU
correctness against it, for formats satisfying `FmtOk`.

All theorems are admit-free; `Print Assumptions` lists only Guru's disabled kernel checks (guard check bypassed for `evalExpr`, positivity check unset for `Expr` / `FullFormat`).  The theorems in
`FlocqProof/` additionally list the standard axioms behind Rocq's real numbers (used by Flocq):
`ClassicalDedekindReals.sig_not_dec`, `sig_forall_dec`, `functional_extensionality_dep`,
`Classical_Prop.classic`.

### The core against Flocq

Every theorem is generic in the format `(e, f)` with `2 <= f` and `f + 1 < 2^(e-1)`, and states,
for all inputs and rounding modes, both the result bits and the 5 `fflags` bits.  Results are
compared through Flocq's own bit encoding (`Glue.toB` / `Glue.ofB`; a NaN result encodes to the
RISC-V canonical NaN).

| Op | Theorem (file in `FlocqProof/`) | Compared with |
|---|---|---|
| FADD / FSUB | `fadd_flocq_holds`, `fsub_flocq_holds` (`Add.v`) | `Bplus`, `Bminus` |
| FMUL | `fmul_flocq_holds` (`Mul.v`) | `Bmult` |
| FDIV | `fdiv_flocq_holds` (`Div.v`) | `Bdiv` |
| FSQRT | `fsqrt_flocq_ok` (`Sqrt.v`) | `Bsqrt` |
| FMADD / FMSUB / FNMSUB / FNMADD | `ffma_flocq_thm` (`Fma.v`) | `Bfma` with `Bopp` on `a` / `c` |
| FCVT.fmt.{W,WU,L,LU} | `cvtIF_flocq_holds` (`CvtIF.v`) | `binary_normalize` of the integer |
| FROUND / FROUNDNX | `fround_flocq_holds` (`CvtRound.v`) | `Bnearbyint` |
| FCVT.fmt.fmt | `cvtFF_flocq_holds` (`CvtFF.v`) | `binary_normalize` of the source float's mantissa and exponent |
| FCVT.{W,WU,L,LU}.fmt | `cvtFI_flocq_holds` (`CvtFI.v`) | the saturating `xlen` / `wlen`-bit integer of Flocq's integer rounding of `B2R` |
| FEQ / FLT / FLE / FLTQ / FLEQ | `fcmp_flocq` (`Misc.v`) | `Bcompare`, with the RISC-V NV rules |
| FMIN / FMAX / FMINM / FMAXM | `fminmax_flocq` (`Misc.v`) | `Bcompare` (-0 < +0), with the RISC-V NaN rules |
| FSGNJ / FSGNJN / FSGNJX | `fsgnj_bits`, `fsgnj_flocq` (`Misc.v`) | sign bits; `Bsign` / `Bopp` |
| FCLASS | `fclass_flocq` (`Misc.v`) | the class mask of `toB` |
| FLI (table) | `fli_flocq` (`Misc.v`) | the Zfa constants as Flocq values |

Flags: NV and DZ as RISC-V specifies per op; OF, UF (tininess after rounding) and NX from
`Flags.roundFlags` of the exact real result.

Hypotheses beyond the format condition:

- `CvtIF`, `CvtFI`: `1 <= wlen <= xlen` and `xlen + 4 <= 7 * 2^(e-1)` (`wlen` is the narrow
  integer width, RISC-V W = 32).
- `CvtFF`: the format condition for both formats.
- All others: none.

## Design notes

### Exponent modes and the reference model

Exponents are kept BIASED inside the core (`FpCore` with mode `true`, the hardware model used by
the units): no bias subtraction at unpack and no bias addition at pack; MUL / FMA subtract, DIV /
SQRT add, and the narrow conversions rebias once.  Mode `false` is the readable unbiased reference
model (`FpCoreRef.v`: `fpuComputeRef := fpuCompute false`, `cvtFFRef := cvtFF false`).  Both modes
share every definition, so the significand datapath is the same code.  The mode is the first
argument of every core and spec definition that depends on it.

### Zfa FLI (load FP immediate)

FLI is not an FPU operation: it reads no FP register, raises no flag and needs no rounding, so it is
not in the operation union and never goes through `fpuIssue` or a unit.  It is a register write of
a constant, like a move.  The library provides the constant table; the parent core does the write.

- `FpCore.fliConstE e f ty idx` : `Expr ty (Bit (f + e + 1))` -- entry `idx` (5 bits) of the Zfa
  table, encoded in format `(e, f)`: -1.0, the minimum positive normal, 2^-16, 2^-15, 2^-8, 2^-7,
  0.0625 ... 256, 2^15, 2^16, +inf, the canonical NaN.  A value above the format's range gives +inf
  (only binary16 entry 29, 2^16).
- `SpecFpu.fliConst idx` : `Expr ty (Bit flen)` -- the same in the own format `F`.

How the parent executes FLI.fmt rd, idx:

1. Own format (`fmt = F`): compute `v := fliConst idx` and write it to `rd`.
   - Against the spec: `fpuWrite (#rd) v` (sets `fs` to Dirty).
   - Against the pipelined FPU: `fpuWriteT rd v`, which returns `false` (and changes
     nothing) while `rd` is still the destination of an operation in flight; retry until it
     returns `true`, exactly as for FMV.W.X / FP loads.
2. A narrow format `G` in `narrow`: NaN-box the narrow constant,
   `v := boxTo G (fliConstE (fmtE G) (fmtF G) _ idx)`, then write it as above.

Example (own format binary32, `narrow = [FmtH]`): FLI.S rd, 16 writes `0x3f800000` (1.0);
FLI.H rd, 16 writes `boxTo FmtH 0x3c00`.

The table carries no proof obligation in the contract because the FPU never computes it:
the parent's write is an ordinary `fpuWrite` / `fpuWriteT`.  Its values are proved against Flocq
(`fli_flocq` in `FlocqProof/Misc.v`) and tested against an exact Python encoder
(`python3 Test/fptest.py fli <e> <f>`).

## Files

| File | Contents |
|---|---|
| `FpUtil.v` | Width-generic helpers (`zext`, `sext`, `trunc`, `cst`, `clz`, `Slt`). |
| `FpCore.v` | Single-format arithmetic over the decoded operation `FpOpDK`, with exponent mode `bm`: unpack, rounding (`roundPack`, `normRound`), ADD/SUB, MUL, FMA, DIV, SQRT, MIN/MAX (+ Zfa), SGNJ*, FCVT to/from integers, FEQ/FLT/FLE (+ Zfa), FCLASS, Zfa FROUND/FROUNDNX (`fpuCompute`); FCVT between formats (`cvtFF`); Zfa FLI table (`fliConstE`). |
| `FpCoreRef.v` | The unbiased reference core: `fpuComputeRef := fpuCompute false`, `cvtFFRef := cvtFF false`. |
| `SpecFpu.v` | Register-level spec: FP register list `fpr_0..fpr_1f`, `frm`, `fflags`, `fs`; actions `fpuExec`, `fpuRead`/`fpuWrite`, `fcsrRead`/`fcsrWrite`, `frm*`, `fflags*`, `fs*`; operation union `FpuOpK` and its decoder `decodeOp`; own-format ops plus narrow conversions (`narrowSel`), NaN-boxing (`boxTo`), Zfa FLI constants (`fliConst`); Gallina semantics of the actions (`execSem`, ...). |
| `IntMul.v` | Unsigned shift-and-add multiplier core. |
| `ShiftFifo.v`, `ImplStaged.v` | Generic pipelined / iterative staged controllers. |
| `ImplFpuUnits.v` | Staged units: pipe unit (`stagedPipe`), divide and square-root units (`stagedIter`). |
| `FpuArch.v` | Architectural FP state shared by spec and impl (`fpuArchTree`), with Gallina views. |
| `FpuFU.v` | FU interface (`FU`) and fus: `pipeFU`/`divFU`/`sqrtFU` (units + metadata), `cvtFU` (narrow conversions, only if `narrow` is non-empty); `fpuFUs`. |
| `ImplFpu.v` | Pipelined FPU: scoreboard (`pend`, `lpend`, `intBusy`; RAW/WAW only), fus, out-of-order write-back; interface with ready flags (`fpuIssue`, `fpuIntResp`, `fpuReserve`/`fpuFill`, `fpuReadT`/`fpuWriteT`, CSR/FS accessors); internal rules `fpuImplRules`. |
| `Proof/IntMulProof.v`, `Proof/ImplStagedProof.v`, `Proof/ShiftFifoLemmas.v` | The multiplier and the staged controllers. |
| `Proof/FpUtilLemmas.v`, `Proof/ExpShift.v` | Evaluation of the helpers; bit-vector facts for exponent offsets (`Sub` / `Slt` / `bitSet` / `clz`, `shiftV`, `InRange`). |
| `Proof/FpuUnitsProof.v` | The units compute the core; controller theorems. |
| `Proof/FpCoreRefProof.v` | Exponent-mode equivalence (`fpuCompute_bm_equiv`, `cvtFF_bm_equiv`, `fpuComputeRef_equiv`, `cvtFFRef_equiv`). |
| `Proof/FpuArchLemmas.v`, `Proof/SpecFpuLemmas.v` | Arch and spec actions in terms of Gallina semantics; decoding a built operation union. |
| `Proof/StagedQueue.v` | Queue view of the staged controllers (`PipeHolds`, `IterHolds`). |
| `Proof/FpuFUProof.v` | `FUOk`: each fu is a FIFO whose head computes `SpecFpu.execResOf`; instances for all fus. |
| `Proof/BitVecLemmas.v`, `Proof/ImplFpuLemmas.v` | Scoreboard bit vectors; forward lemmas for every impl action and rule. |
| `Proof/RelFpu.v` | Relation `RelC` between an impl state and a base spec state plus a ghost `g` of the operations accepted since, in program order; `foldSem g sigma` is the spec state with all of them applied; preservation lemmas `relC_*`. |
| `Proof/SpecFpuRef.v` | `FmtOk`, `FmtOk_std`, `execResOf_ref` (reference and biased spec results agree). |
| `Proof/FpuContract.v` | The interface contract: `FpuAbs`, `FpuView`, the `*Step` relations, `fpu_contract`, `fpu_contract_ref`; `fpuFUsP_wf`. |
| `FlocqProof/Glue.v` | Bits <-> Flocq `BinarySingleNaN` floats via Flocq's encoding (`toB`, `ofB`), rounding modes (`modeOf`), Flocq side conditions. |
| `FlocqProof/Flags.v` | IEEE flag spec from Flocq's real values (`roundFlags`, `finiteFlags`) and the RISC-V `fflags` encoding (`mkFl`). |
| `FlocqProof/Decode.v` | `B2SF (toB x)` from the sign / exponent / fraction fields; `ofB (toB x) = x` for non-NaN `x`. |
| `FlocqProof/RoundBits.v` | `roundPack` (reference mode) as an integer model (`roundPack_Z`). |
| `FlocqProof/RoundLoc.v` | Guard / round-sticky locations and Flocq rounding in every mode (`round_at`). |
| `FlocqProof/RoundCore.v` | The integer model is Flocq's rounding: value, overflow, flags, result bits (`rp_result`, `rp_flags`). |
| `FlocqProof/NormRound.v` | `clz`, `normRound` = `roundPack` on the normalized window, location transfer. |
| `FlocqProof/Unpack.v` | `fpUnpack` against the fields: class flags, normalized significand and exponent. |
| `FlocqProof/` `Mul.v`, `Add.v`, `Div.v`, `Sqrt.v`, `Fma.v`, `FmaAlign.v`, `CvtIF.v`, `CvtRound.v`, `CvtFF.v`, `CvtFI.v`, `Misc.v` | The per-op theorems against Flocq (table above) and their helpers. |
| `Test/fptest.py` | Differential test of `FpCore` (all families incl. Zfa, `cvtFF`, the FLI table) against an exact-rational Python reference, evaluated with `vm_compute` (RISC-V: `wlen = 32`); `FPTEST_BM=false` tests the reference model. |

## Build and test

Needs Rocq, its Stdlib and Flocq; the build uses the `rocq` found on `PATH` (or in `COQBIN`).
`make coq` builds Guru, the FPU, its proofs and `FlocqProof/`.

```
make coq
python3 Test/fptest.py 8 23 3000 1 64          # single format (e, f), n cases, seed, xlen
python3 Test/fptest.py cvt 11 52 8 23 2000 2    # cvtFF from (e1, f1) to (e2, f2)
python3 Test/fptest.py fli 8 23                  # the Zfa FLI table
FPTEST_BM=false python3 Test/fptest.py 5 10 2000 3   # the same tests on the reference model
```

## Use of AI

AI was used to generate all the proofs.  `ShiftFifo.v`, `ImplStaged.v`, `IntMul.v` and their
proofs (`Proof/ShiftFifoLemmas.v`, `Proof/ImplStagedProof.v`, `Proof/IntMulProof.v`) were adapted
from https://github.com/OpenSeCura/cheriot, where the designs were handwritten and the proofs
were generated by AI.

`FpCore.v`, which specifies the operations and is parameterized on whether exponents are kept
biased, and `SpecFpu.v`, which specifies the FPU's architectural state and how the operations
update it, were both generated by AI and reviewed by humans.

The Flocq-side specifications were written or reviewed by humans.  Most of them are existing
functions of the Flocq library (`Bplus`, `Bmult`, ...); those that Flocq does not provide (for
example the exception flags, the saturating conversion to integers and the RISC-V NaN rules) were
written on top of Flocq's definitions.  Each operation of `FpCore.v` in its reference (unbiased)
mode is proved by AI against the corresponding specification.

In short, the combinational operations of the AI-generated `FpCore.v` are proved against
Flocq-based specifications written or reviewed by humans.  The atomic architectural updates of the
AI-generated `SpecFpu.v` were reviewed by humans, and the AI-generated multicycle / pipelined FPU
implementation is proved by AI against them.
