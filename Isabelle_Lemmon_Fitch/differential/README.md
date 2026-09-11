# Differential test: generated kernel vs. handwritten checker

Answers one question: **does the Isabelle-generated checker return the same
verdict as Halvorson's handwritten checker, on the same input?**

This is the check that distinguishes a faithful reconstruction from a careful
lookalike. It is *testing*, not proof — Haskell has no formal semantics here,
so the two can never be proved equivalent.

## Running it

    ghc --make -O1 -igenerated/haskell \
        -ireference/lemmon-checker-main/src -idifferential \
        -outputdir differential/build -o differential/diff \
        differential/Differential.hs
    ./differential/diff

Needs `ghc libghc-aeson-dev libghc-split-dev` (Debian/Ubuntu). His source
compiles **unmodified**; the reference checker is unchanged.

## What is compared

Per line, through his public API (`checkProof` / `LineReport`), never through
internals. His `checkLine` = `checkStructure` then `checkJustification`; ours
is `hlLineOK` = `hlStructureOK` and `hlRuleOK`. Whole-proof verdicts
(`proofValid` vs `hlCorrect`) are compared as well.

Comparing only whole-proof verdicts would let two disagreements on different
lines cancel out, which is why the comparison is per line.

## Coverage, and why each phase is there

**Phase 1, his corpus.** 14 proofs parsed from `eval/**.pipe`. Nearly all
lines are accepted, so this phase alone is weak: a checker that always
returned `True` would pass it.

**Hand-written extras.** His corpus uses only 13 of the 21 rules. `Extra.hs`
adds proofs for the eight it never uses — `OrElim`, `EqIntro`, `EqElim`,
`LEM`, `PropTaut`, `IffIntro`, `IffElim`, `QN` — which are also the rules the
audit flagged. They need not be valid: agreement is what is measured, so a
proof both checkers reject is as informative as one both accept.

**Phase 2, mutation.** Every line of every proof is corrupted several ways
(dependency sets grown, shrunk and emptied; line numbers changed; each
justification replaced by neighbouring ones; formulas replaced). This is what
exercises the rejection path, and where a real disagreement would surface.

## Result

**Verdicts** (`RESULT.txt`): 9,874 line comparisons, 2,706 of them rejections,
**0 disagreements**. His own regression suite (`test/Tests.hs`) also passes
unmodified against the shim in `shim/`, which replaces his `LemmonChecker`
module with one backed by the generated kernel.

**Messages** (`RESULT.messages`): of 860 rejections, **all 860 reproduce his
message byte for byte**.

The messages come from `hlLineError`, which Isabelle proves reports no error
exactly when `hlLineOK` holds (`hlLineError_None`, `hlProofReport_valid` in
`LF_HLW_Report.thy`). Isabelle decides *which* error and *with what
data*; `Render.hs` supplies only the wording, because Isabelle's string
literals are ASCII (`Str_Literal.hs` raises above code point 127) and his
messages use U+274C and the connectives.

Crucially `hlRuleOK` still makes every accept/reject decision:
`hlRejectionReason` runs only after a failure has been established, so
`hlRuleError_None` is a one-line proof and *adding messages cannot change
which proofs are accepted*. That is why the verdict count stayed at zero
disagreements through six rounds of message work.

`Render.hs` mirrors two things from his source that had to be reproduced
faithfully rather than corrected:

* `renderFormula`, including two defects — `isBinary` counts `Predicate "="`
  at any arity but omits `Iff`, and `Iff` prints an ASCII arrow while every
  other connective is Unicode (audit finding 9);
* Haskell's derived `Show` for the formula datatype, which one message uses
  instead of the pretty-printer, implemented in full rather than stubbed for
  the shape the corpus happens to reach.

## What this does not establish

* Not equivalence. It is a test over finitely many inputs.
* The corpus is small — 14 proofs, 86 lines of genuine material.
* Integer overflow is untested. His line numbers are machine `Int` and wrap;
  ours are `Integer` and do not. Isabelle will not emit a wrapping integer
  because it would falsify the proofs, so on absurd line numbers the two
  checkers *should* diverge. No test here reaches that range.

## Original-paper audit API regressions (2026-09-09)

`ApiRegression.hs` is an external client of the generated public module. It
checks natural-number conversions, closed-box rejection, immediate discharge,
canonical dependency bookkeeping, unused-premise removal, and both
outer-premise eigenconstant repairs. Rebuild the generated code first:

```bash
ghc --make -O1 -igenerated/haskell -outputdir /tmp/lf_api_regression \
  -o /tmp/lf_api_regression/api-regression differential/ApiRegression.hs
/tmp/lf_api_regression/api-regression
```

This adds boundary and repair coverage; it does not prove the exact translator
succeeds on every valid input. See `../VALIDATION.md` for this revision's
combined results.
