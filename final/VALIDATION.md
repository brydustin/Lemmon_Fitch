# Validation of the original-paper audit repairs

Date: 2026-09-11. See `ORIGINAL_PAPER_COMPARISON.md` for mathematical coverage.
A passing build validates the stated theorems. As of this date the critical
path is complete: `hlPaperCorrect_toFitch` proves the checked translation
succeeds on every nonempty paper-correct source, so the emission-totality
obligation this file used to record as outstanding is discharged.

## Source checks

- Complete **48-theory cap and Haskell/SML regeneration: passed**,
  source-loaded from HOL (5m58s overall, exit 0). All three generated files
  were regenerated **byte-for-byte unchanged** from the previous checkpoint.
- The isolated sessions used during development — `HL_T2` for the erasure and
  rule-transfer layer and `HL_T3B` for the construction layer — pass from HOL
  with `quick_and_dirty=false`, in 2m31s and 1m54s respectively.

The maintained sources at this 48-theory checkpoint contain 1,199
lemma/theorem/corollary command sites and 124 `by eval` command sites. These
are textual counts, not coverage metrics. A source scan found **no proof
admissions, `oops`, axiomatizations, oracles, or `quick_and_dirty` settings**,
and all 48 maintained theories are explicitly imported by the cap. The original
Desktop PDF remains unchanged and matches the preserved reference copy,
SHA-256:

```
055ad67d33563ed786fe78b1d7d4df1715d5af60f78adde5429bdf72832884cc
```

## Executable checks

All checks below were rebuilt against the audit Haskell and returned exit
status 0. Every source check since, up to and including the 48-theory one
above, has regenerated all three exports byte-for-byte unchanged, so these
executable results continue to apply:

- Differential checker verdicts: **9,874 comparisons, 0 disagreements**;
  2,706 rejected lines exercise the rejection path (`differential/RESULT.txt`).
- Rejection messages: **860/860 exact**, no verdict disagreement
  (`differential/RESULT.messages`).
- Supplied checker regression suite: **all 80 cases passed** with its
  `LemmonChecker` replaced by the generated-kernel shim
  (`differential/RESULT.shim`). Its further 29 translation cases exercise the
  supplied `FitchConvert`, not our generated translator.
- External public API regression: **26 assertions passed**
  (`differential/ApiRegression.hs`). Covers Nat conversion, actual box scope,
  singleton subproof discharge, exact LEM dependencies, unused premises and
  both universal/existential outer-premise repairs.

These finite checks preserve agreement with the supplied Lemmon checker and
verify the concrete repairs. They do not close general exact translation
correctness or all-source success.

## Reproduction

From the project root with Isabelle 2025-2:

```bash
./generate_code.sh
```

This source-processes all maintained theories from HOL and exports Haskell and
SML; it does not select a prebuilt project heap. See `differential/README.md`
for the verdict/message corpus and `differential/ApiRegression.hs` for the
new API assertions.
