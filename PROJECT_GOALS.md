# Remaining project goals

Active worklist, revised 2026-09-09. The specification is the original paper in
`reference/original-paper/`, with its corrections and interpretation limits
recorded in `ORIGINAL_PAPER_COMPARISON.md`. A goal closes only when its actual
statement has been checked by Isabelle; testing an output validator is not a
substitute for a quantified construction theorem.

## The end state

One theorem, at the exact `HL_` types, unconditional:

> for every nonempty `hlPaperCorrect P` there is an `F` with
> `hlLemmonToFitchChecked P = Inr F`, `hlFitchCorrect F`,
> `hlFitchConclusion F = hlConclusion P`, and
> `set (hlFitchPremises F) ⊆ set (hlOpenPremises P)`.

That is **T3/G6**. Everything on the critical path exists to feed it; everything
off it is paper reconciliation or shipping. A conditional guarantee about
outputs that happen to pass the validator must never be reported as this
theorem.

## Closed

| ID | Target | Evidence |
|---|---|---|
| G1 | Every nonempty paper-correct source unfolds to a correct `hl_derivation` tree, retaining its conclusion and requiring no additional premises. | `hlVerifiedCorrect_toDerivation`, `hlPaperCorrect_toDerivation` (`LF_HLW_Faithful.thy`); all 21 rule cases, ancestor classification, conclusion and premise bound. |
| G2 | Fresh constant renaming preserves every exact rule, derivation correctness and unaffected open assumptions. | `hlDerivationOK_rename`, `hlRenameDerivation_open_unchanged` (`LF_HLW_Derivation_Renaming.thy`); both quantifier patterns with eigenconditions, witness uniqueness, empty-name sentinel explicit. |
| G3 | Emitter fuel adequacy, increasing fresh line allocation, conclusion preservation. | `LF_HLW_Layout.thy` (allocation), `LF_HLW_Fuel.thy` (`hlEmitDerivationFuel_sufficient`, fuel independence), `hlClassifiedDerivationToFitch_conclusion` (`LF_HLW_Conclusion.thy`), covering the premise-only case. |

Also established earlier: exact Lemmon semantic soundness, strengthened Fitch
semantic soundness, canonical dependency reconstruction (Proposition 7),
source-to-tree unfolding (L1), and safety/sequent preservation of accepted
checked translations.

---

## Critical path

### T1 — Emitter structural well-formedness (closes G4)

`hlFitchVerified` has five conjuncts. Three already hold of
`hlDerivationToFitch` (`LF_HLW_Premise_Layout.thy`): `hlConcludesAtTop`, and
within `hlFitchNestedWellFormed` the `hlFitchPremisesFirst`, positivity and
`sorted_wrt (<)` parts, together with the root premise set
(`hlDerivationToFitch_premises`) and the absence of emitted premise lines
(`hlEmitDerivation_no_premises`).

Two structural conjuncts remain untouched:

- **Ordinary citation visibility.** `hlFitchWellFormed F`, i.e.
  `hlFitchScopeFrom 0 {} F ≠ None`: every ordinary citation names a line
  already visible at its depth, and no `HL_FPremise` appears at depth > 0.
- **Discharge-pair visibility.** `hlFitchNestingFrom 0 {} {} F`: every cited
  subproof reference `(assumption, last)` is in scope
  (`hlFitchCitedSubs ⊆ boxes`), and no `HL_FAssume` stands as a line item.

Both are inductions on `hlEmitDerivationFuel` in the shape of those already in
`LF_HLW_Layout.thy`; the visible-set invariant should ride on the existing
`hlAllocated` interval characterisation. **Completion evidence:** two theorems
`hlDerivationToFitch_wellFormed` and `hlDerivationToFitch_nesting`, plus
`hlDerivationToFitch_nestedWellFormed` assembling the five-conjunct
`hlFitchNestedWellFormed`, checked in an isolated session.

This is the piece the whole chain is blocked on. It is not the hard one.

### T2 — Rule transfer through emission (closes G5)

`LF_HLW_Rule_Transfer.thy` proves the 21 dependency-arithmetic cases
(`hlRuleOK_expectedReferences`) and eigenconstant antitonicity
(`hlRuleOKG_eigen_antitone`, `hlRuleOKG_assumption_antitone`,
`hlRuleOKG_non_eigen_independent`) **about a fixed proof**. What is missing is
that they survive erasure:

1. A characterisation of `δ⇩H (hlDerivationToFitch d)` — its formulas and
   justifications are the emitted ones with renumbered citations.
2. `hlDependencyClosed` and `hlCanonicalOrder` for that erasure, hence
   `hlVerifiedCorrect (δ⇩H F)`.
3. The two eigenconstant repairs actually discharge `hlEigenScopeViolations`
   on the emitted proof — antitonicity alone does not say this.

**This is the long pole**, and it is where defects should be expected to
surface, as four did in `lemmonToFitchDirect`. Any defect found here is
repaired with concrete regression evidence, or recorded as a precise
counterexample to the proposed theorem.

### T3 — Premise closure, then the construction theorem (closes G6)

`hlFitchPremiseClosed` is stated over `δ⇩H F`, so it is not provable before T2
even though `hlDerivationToFitch_premises` already pins the root premise set.
Once T1 and T2 land, `hlFitchVerified` assembles, and G6 is composition with
G1, G2 and G3.

**Dependency chain: G1 + G2 + G3 → T1 → T2 → T3.**

### T4 — Exact-layer impossibility results (closes G7)

Theorem 10 and Conjectures 27 and 28 are proved **only at the compact types**.
`hl_theorem_10` currently states only that the source is correct and that one
particular direct algorithm fails, which is not the paper's claim.

Two routes, and the fork is worth deciding before starting:

- Re-prove nonexistence three times at `HL_` types. Exact counterparts of
  `subs_span`, `subs_unique_proof` and `image_subproof_ordered` are needed.
- Prove one structural bridge between compact `proof`/`fitch` and
  `hl_proof`/`hl_fitch_proof`, preserving correctness and positional images,
  and transport all three. This also pays for Lemma 23 and Corollary 24.

The bridge is more work up front and carries the largest uncertainty in the
project: the two layers' rule rosters differ, and a total bridge may not exist
in one direction. **Scope T4 to whichever direction is actually total. If
neither is, state Theorem 10 directly at `HL_` types and leave Conjectures
27/28 at compact types with an explicit recorded note.**

---

## Off the critical path

### T5 — Manuscript reconciliation (closes G8)

Walk `lemmon-fitch.tex` against the final theorem statements: hypotheses,
types, and the retained corrections to Theorem 4, Conjecture 26, graph
orientation, and the image/laminarity claims. The existing 49-identifier check
is name resolution, not mathematical coverage, and is not the acceptance test.

### T6 — Revalidation and distribution (closes G9)

Full `./generate_code.sh` from HOL, differential harness rerun, paper rebuild,
`MANIFEST.txt` and `VALIDATION.md` refresh. Note that **`final/` is stale**: it
predates eleven maintained theories, including all of `LF_HLW_Faithful`,
`LF_HLW_Renaming`, `LF_HLW_Quantifier_Renaming`, `LF_HLW_Derivation_Renaming`,
`LF_HLW_Rule_Transfer`, `LF_HLW_Layout`, `LF_HLW_Fuel`, `LF_HLW_Conclusion`,
`LF_HLW_Premise_Layout`, `LF_HLW_Derivation` and `LF_HLW_Witnesses`. Refreshing
it is part of this target, not a separate one.

### Recorded as not pursued

These are decisions, not oversights, and are written off rather than proved:

- **Is `hlCorrect` alone semantically sound?** `hlVerifiedCorrect_sound` is
  proved of the stronger `hlVerifiedCorrect`. Settle it by constructing a
  witness, never by reasoning from the definitions — the fourth `boxHeadError`
  obstruction is the standing reason why.
- **Are the seven direct-translation checks necessary as well as sufficient?**
  Sufficiency is `lemmonToFitchDirect_fitchWF`. All six witnesses are proved
  imageless (`checks_reject_only_imageless_sources`), but six sources are not
  all sources.
- **Parser / Aeson / web application adapter.** Interface engineering rather
  than formalisation. Do not delete `reference/lemmon-checker-main` before its
  interface code is copied somewhere maintained.
- **Further defect hunting in the supplied Haskell.** Sixteen findings are in
  `HASKELL_AUDIT.md`. The logical kernel was searched thoroughly and the search
  was stopped there deliberately.

---

## Checked milestones

- 2026-09-09: G1 closed by `hlVerifiedCorrect_toDerivation` (a stronger source
  class than requested) and its `hlPaperCorrect_toDerivation` corollary.
  Isolated session `HL_Faithful_Check` passed in 28 seconds.
- 2026-09-09: `HL_Rename_Only` passed the renaming foundations. Candidate
  membership alone was insufficient for G2.
- 2026-09-09: G3 closed. `HL_Fuel` and `HL_Conclusion` passed; conclusion
  preservation holds for every ancestor-classified tree, with no correctness
  assumption.
- 2026-09-09: G2 closed by `HL_Derivation_Renaming` (28 seconds). Both
  quantifier patterns with eigenconditions and the equality/tautology rules are
  included; no ordering assumption is made about witness search.
- 2026-09-09: `HL_Premise_Layout` passed (31 seconds), closing the
  premise-placement and source-premise-set parts of G4.
