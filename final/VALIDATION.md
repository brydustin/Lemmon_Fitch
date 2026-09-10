# Validation of the original-paper audit repairs

Date: 2026-09-09. See `ORIGINAL_PAPER_COMPARISON.md` for mathematical coverage.
A passing build validates the stated theorems; it does not supply the remaining
exact-layer L2–L4/emission-totality theorems.

## Source checks

- Exact runtime audit, source-loaded from HOL with `quick_and_dirty=false`:
  passed (1m43s session time). Includes the new genuine nesting checker,
  root-premise semantic soundness, canonical dependency reconstruction,
  outer-premise universal/existential repairs, and all-21-rule tree examples.
- Exact translation proof theory: passed its isolated check after its parent
  theories were checked from HOL. Proves successful source-to-tree unfolding,
  conclusion preservation and conditional checked-output guarantees.
- Complete 34-theory cap and Haskell/SML regeneration: **passed**, source-loaded
  from HOL by `./generate_code.sh` (5m12s session time, exit 0). All three
  generated files were refreshed. The revised paper also rebuilt successfully
  (21 pages, no undefined references or box-layout warnings).

The maintained sources contain 793 lemma/theorem/corollary command sites and
121 `by eval` command sites. These are textual counts, not coverage metrics.
The source scan found no proof admissions, axiomatizations, oracles, or
`quick_and_dirty` settings. All maintained theories are explicitly imported by
the cap. The original Desktop PDF remains unchanged and matches the preserved
reference copy, SHA-256:

```
055ad67d33563ed786fe78b1d7d4df1715d5af60f78adde5429bdf72832884cc
```

## Executable checks

All checks below were rebuilt against the newly regenerated Haskell and
returned exit status 0:

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
