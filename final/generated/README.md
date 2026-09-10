# Generated code

This directory is deliberately separate from the flat Isabelle source tree.
Its Haskell and SML files are derived distribution snapshots, not Isabelle
theories, and no `.thy` file imports them.

The authoritative generator is the `export_code` section of `../Lemmon_Fitch.thy`.
After that cap has finished source-processing from the standard `HOL` image,
the current outputs are available under `isabelle-export:/Lemmon_Fitch/code/` in
jEdit. Keeping this directory is useful when distributing executable code to
someone who does not have Isabelle; it is otherwise safe to delete and
regenerate.

The snapshots regenerated during the 2026-09-09 original-paper audit include the exact Haskell-shaped
`HL_` formula, Lemmon, and Fitch datatypes, all twenty-one authoritative rule
checks, `hlCorrect`, `hlVerifiedCorrect`, and the total Fitch-to-Lemmon map
`hlFitchToLemmon` (`δ⇩H`). They also include the finite, error-aware model
evaluator, corrected NNF/DNF conversion, repaired exact direct map
`hlLemmonToFitchDirect`, and the exact derivation-tree fallback exposed through
`hlLemmonToFitchChecked`, alongside the compact translation development. The
fallback includes ancestor-sensitive premise classification, which corrects
the handwritten source's global `boxed` bug.
Run `../generate_code.sh` to refresh them source-only; the script does not
build or select a `Lemmon_Fitch` heap.

The public API now includes `nat_of_integer`/`integer_of_nat`,
`hlPaperCorrect` and canonical dependency reconstruction, `hlFitchCorrect`
with genuine nested scope, and `hlFitchPremises`/`hlFitchConclusion`.
`hlLemmonToFitchChecked` validates the target's rules, scope, conclusion and
premise inclusion. Raw construction functions are not acceptance interfaces.
General all-source success of the exact translator remains unproved; see
`../ORIGINAL_PAPER_COMPARISON.md`.
