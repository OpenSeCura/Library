# Fpu: a generic RISC-V FPU in Guru

A single-format, format-ignorant FPU: parameters `F` (the own format `(e, f)` = exponent bits,
fraction bits; `FmtS`/`FmtD`/`FmtH`/`FmtQ`/`FmtB` = binary32/64/16/128, bfloat16), `xlen`, and a
static list `narrow` of NaN-boxed narrow formats.  The FP registers are `fmtW F = e + f + 1` bits
wide (own-format values are stored unboxed).  Packets carry no format.  Example instance:
`F = FmtS, narrow = [FmtH; FmtB]`.

The operation is a tagged union of families with their options (`SpecFpu.FpuOpK`), decoded once
(`SpecFpu.decodeOp`) into the core's flat record `FpCore.FpOpDK`:

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
| `cvtFI`, `cvtIF` | `unsigned`, `wide` | FCVT.{W,WU,L,LU}.fmt, FCVT.fmt.{W,WU,L,LU} |
| `round` | `nx` | Zfa FROUND / FROUNDNX |
| `cvtN` | `toNarrow`, `nidx` | FCVT with a boxed narrow format (`nidx` indexes `narrow`) |

The D-only Zfa ops (FCVTMOD.W.D, FMVH.X.D, FMVP.D.X) are out of scope.

### Zfa FLI (load FP immediate)

FLI is not an FPU operation: it reads no FP register, raises no flag and needs no rounding, so it is
not in the operation union and never goes through `fpuIssue` or a unit.  It is a register write
of a constant, like a move.  The library provides the constant table; the parent core does the
write.

- `FpCore.fliConstE e f ty idx` : `Expr ty (Bit (f + e + 1))` -- entry `idx` (5 bits) of the Zfa
  table, encoded in format `(e, f)`: -1.0, the minimum positive normal, 2^-16, 2^-15, 2^-8, 2^-7,
  0.0625 ... 256, 2^15, 2^16, +inf, the canonical NaN.  A value above the format's range gives +inf
  (only binary16 entry 29, 2^16).
- `SpecFpu.fliConst idx` : `Expr ty (Bit flen)` -- the same in the own format `F`.

How the parent executes FLI.fmt rd, idx:

1. Own format (`fmt = F`): compute `v := fliConst idx` and write it to `rd`.
   - Against the spec (`fpuRefMod`, or `fpuSpecMod true`): `fpuWrite (#rd) v` (sets `fs` to Dirty).
   - Against the pipelined FPU (`fpuImplMod`): `fpuWriteT rd v`, which returns `false` (and changes
     nothing) while `rd` is still the destination of an operation in flight; retry until it
     returns `true`, exactly as for FMV.W.X / FP loads.
2. A narrow format `G` in `narrow`: NaN-box the narrow constant,
   `v := boxTo G (fliConstE (fmtE G) (fmtF G) _ idx)`, then write it as above.

Example (own format binary32, `narrow = [FmtH]`): FLI.S rd, 16 writes `0x3f800000` (1.0);
FLI.H rd, 16 writes `boxTo FmtH 0x3c00`.

The table itself is checked against an exact Python encoder for every standard format
(`python3 Test/fptest.py fli <e> <f>`); for binary32 it matches the hex table of the Zfa
specification.  It carries no proof obligation in the refinement theorems because the FPU never
computes it: the parent's write is an ordinary `fpuWrite` / `fpuWriteT`.

### Exponent modes and the reference model

Exponents are kept BIASED inside the core (`FpCore` with mode `true`, the hardware model used by
the units): no bias subtraction at unpack and no bias addition at pack; MUL / FMA subtract, DIV /
SQRT add, and the narrow conversions rebias once.  Mode `false` is the readable unbiased reference
model (`FpCoreRef.v`: `fpuComputeRef := fpuCompute false`, `cvtFFRef := cvtFF false`).  Both modes
share every definition, so the significand datapath is the same code.  The mode is the first
argument of every core and spec definition that depends on it.

`Proof/FpCoreRefProof.v` proves the two modes compute identical results for every format with
`2 <= f` and `f + 1 < 2^(e-1)` (`FmtOk`; and `0 <= xlen`, `xlen + 4 <= 7 * 2^(e-1)`), which
covers S, D, H, Q and BF16 with xlen 32 or 64.  The spec takes the mode too, and the pipelined FPU
refines both versions: `fpu_refines_std` for `fpuSpecMod true`, `fpu_refines_ref` for
`fpuRefMod := fpuSpecMod false`.

`fpuRefMod` is the spec of record: clients should state their FPU correctness against it, for
formats satisfying `FmtOk` (`FmtOk_std` proves it for all standard formats).

## Files

| File | Contents |
|---|---|
| `FpUtil.v` | Width-generic helpers (`zext`, `sext`, `trunc`, `cst`, `clz`, `Slt`). |
| `FpCore.v` | Single-format arithmetic spec over the decoded operation `FpOpDK`, with exponent mode `bm`: unpack, rounding (`roundPack`, `normRound`), ADD/SUB, MUL, FMA, DIV, SQRT, MIN/MAX (+ Zfa), SGNJ*, FCVT to/from integers, FEQ/FLT/FLE (+ Zfa), FCLASS, Zfa FROUND/FROUNDNX (`fpuCompute`); FCVT between formats (`cvtFF`); Zfa FLI table (`fliConstE`). |
| `FpCoreRef.v` | The unbiased reference core: `fpuComputeRef := fpuCompute false`, `cvtFFRef := cvtFF false`. |
| `SpecFpu.v` | Register-level spec: FP register list `fpr_0..fpr_1f`, `frm`, `fflags`, `fs`; actions `fpuExec`, `fpuRead`/`fpuWrite`, `fcsrRead`/`fcsrWrite`, `frm*`, `fflags*`, `fs*`; operation union `FpuOpK` and its decoder `decodeOp`; own-format ops plus narrow conversions (`narrowSel`), NaN-boxing (`boxTo` for narrow loads/moves), Zfa FLI constants (`fliConst`). |
| `IntMul.v` | Unsigned shift-and-add multiplier core (copied from `cheriot/Impl/ImplMulDiv.v`). |
| `ShiftFifo.v`, `ImplStaged.v` | Generic pipelined / iterative staged controllers (copied from `cheriot`). |
| `ImplFpuUnits.v` | Staged units: pipe unit (`stagedPipe`), divide and square-root units (`stagedIter`). |
| `Proof/FpuUnitsProof.v` | Each unit computes exactly the spec (`Pipe_/Div_/Sqrt_StageValAt_spec`), plus the controller theorems for each unit. |
| `Proof/ExpShift.v` | Bit-vector facts for exponent offsets: `Sub` / `Slt` / `bitSet` / `clz` evaluation, shifted values (`shiftV`, `InRange`, `slt_shift`, ...). |
| `Proof/FpCoreRefProof.v` | Exponent-mode equivalence: unpack shifts the exponent (`fpUnpack_shift`), rounding is shift-invariant (`rpExp_eq`, `roundPack_eq`, `normRound_eq`), per-op lemmas with range lemmas, assembly (`fpuCompute_bm_equiv`, `cvtFF_bm_equiv`, `fpuComputeRef_equiv`, `cvtFFRef_equiv`). |
| `Proof/IntMulProof.v`, `Proof/ImplStagedProof.v`, `Proof/ShiftFifoLemmas.v` | Copied proofs. |
| `FpuArch.v` | Architectural FP state shared by spec and impl (`fpuArchTree`), with Gallina views. |
| `FpuFU.v` | FU interface (`FU`) and fus: `pipeFU`/`divFU`/`sqrtFU` (units + metadata), `cvtFU` (narrow conversions, only if `narrow` is non-empty); `fpuFUs`. |
| `ImplFpu.v` | Pipelined FPU: scoreboard (`pend`, `lpend`, `intBusy`; RAW/WAW only), fus, out-of-order write-back; interface with ready flags (`fpuIssue`, `fpuIntResp`, `fpuReserve`/`fpuFill`, `fpuReadT`/`fpuWriteT`, CSR/FS accessors); `fpuImplMod`. |
| `Proof/FpuArchLemmas.v`, `Proof/SpecFpuLemmas.v` | Arch and spec actions in terms of Gallina semantics; decoding a built operation union (`decode_*`, `cvtN_payload`, via Guru's union round-trip lemma). |
| `Proof/StagedQueue.v` | Queue view of the staged controllers (`PipeHolds`, `IterHolds`) with forward lemmas. |
| `Proof/FpuFUProof.v` | `FUOk`: each fu is a FIFO whose head computes `SpecFpu.execResOf`; instances for all fus. |
| `Proof/BitVecLemmas.v`, `Proof/ImplFpuLemmas.v` | Scoreboard bit vectors; forward lemmas for every impl action and rule. |
| `Proof/RelFpu.v` | Refinement relation `RelFpuG g S sigma` (ghost of uncommitted ops in program order, spec lags impl); step lemmas `rel_*` (spec never steps), read lemmas, `rel_commit`. |
| `Proof/FpuRefinement.v` | `fpu_refines bm`: `ModSimulationInit fpuImplMod (fpuSpecMod bm)` for any mode whose results agree with the biased ones, committing the done prefix after each impl step; `fpu_refines_std` (mode `true`). |
| `Proof/FpuRefinementRef.v` | `fpu_refines_ref`: the pipelined FPU refines the spec built on the reference core (`FmtOk`, `FmtOk_std`). |
| `Test/fptest.py` | Differential test of `FpCore` (all families incl. Zfa, `cvtFF`, the FLI table) against an exact-rational Python reference (evaluated with `vm_compute`); `FPTEST_BM=false` tests the reference model. |

## Build and test

```
make coq
python3 Test/fptest.py 8 23 3000 1 64          # single format (e, f), n cases, seed, xlen
python3 Test/fptest.py cvt 11 52 8 23 2000 2    # cvtFF from (e1, f1) to (e2, f2)
python3 Test/fptest.py fli 8 23                  # the Zfa FLI table
FPTEST_BM=false python3 Test/fptest.py 5 10 2000 3   # the same tests on the reference model
```
