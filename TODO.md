# Audit record and authoritative-Haskell migration

Recorded 2026-08-27 and completed 2026-08-28. Every item below is proved,
implemented, or refuted by a named counterexample; the table is retained as an
audit trail rather than a list of open work.

The supplied Haskell checker was subsequently designated authoritative. The
following migration status is therefore separate from the completed compact
formalisation below:

| Item | Status |
|---|---|
| Exact Haskell `Term`/`PredFormula`, including Boolean constants and equality-as-predicate | **done** — `LF_Halvorson_Formula.thy` |
| Total versions of partial Boolean and biconditional formula operations | **done**, with executable guard lemmas |
| Exact twenty-one-constructor Lemmon checker and Haskell line-number behavior | **done** — `LF_Halvorson.thy`, `hlCorrect` |
| Strengthened order/dependency invariants for theorem use | **done** — `hlVerifiedCorrect` |
| Exact Fitch syntax and total Fitch-to-Lemmon `δ⇩H` | **done** — `LF_Halvorson_Fitch.thy` |
| Source-generated Haskell and SML containing the exact layer | **done** — refreshed 2026-08-28 |
| Standard semantics for the exact `HL_` formulas | **done** — `LF_Halvorson_Semantics.thy`; includes substitution and `PropTaut` soundness plus the equality-model counterexample |
| Corrected executable DNF pipeline | **done** — `LF_Halvorson_DNF.thy` covers the missing biconditional cases and rejects non-propositional input explicitly |
| End-to-end soundness theorem for all exact `hlVerifiedCorrect` rules | **done** — `hlRuleOK_sound` covers all twenty-one authoritative rule branches; `hlVerifiedCorrect_line_sound` composes them by well-founded dependency induction; `hlVerifiedCorrect_sound` proves the conclusion true whenever the open premises are true in a standard interpretation |
| Direct Lemmon-to-Fitch algorithm on exact `HL_` types | **done** — `LF_Halvorson_Translate.thy`; includes positional preservation and a verified round-trip guard |
| Tree Lemmon-to-Fitch fallback migrated from compact `fm`/`just` to exact `HL_` types | **done** — `LF_Halvorson_Unfold.thy`; includes all 21 derivation rules, both eigenconstant repairs, ancestor-sensitive premise classification, a verified shared-discharge fallback guard, and the complete checked route |
| Parser/Aeson/web adapter and Haskell regression corpus run against generated `HL_` kernel | **open**; no GHC/Cabal/Stack toolchain is installed on this machine |

| # | Item | Status |
|---|------|--------|
| 1 | `README.md` is factually wrong: claims one `sorry`, `quick_and_dirty`, and Conjecture 26 open | **done** — sessions, theory table and "what is not proved" rewritten |
| 2 | `lemmonToFitchDirect` is unsound — returns `Inr F` with `¬ fitchWF F` | **done** — four gaps found and plugged: `subScopeError` (cited subproof out of scope; `c27` → `OutOfScope 5 3 2`), `premiseOrderError` (undischarged assumption written too late; `premLate` → `PremiseLate 3 2`), `boxOrderError` (discharge running backwards; `backCP` → `BoxReversed 2 1`), and `boxHeadError` (one assumption discharged from two lines; `reused` → `AssumptionReused 2 3 4`). `LF_Positional.thy` now proves all six conjuncts: `lemmonToFitchDirect_citations` closes the last citation conjunct and `lemmonToFitchDirect_fitchWF` proves `lemmonToFitchDirect P = Inr F ⟹ fitchWF F`. The proof includes `buildItems_scope_eq` and `buildItems_subrefs`; both remove duplicate box heads because a valid `OrElim` may cite one discharge pair twice (`duplicateDischarge`) while the image contains one subproof. |
| 3 | `theorem_10` states "our checker rejects ex11/ex12", not the paper's "no positional Fitch image exists" | **done** — `LF_Theorem10.thy`: `theorem_10`, proved for both examples via `subs_span` |
| 4 | No semantics anywhere — nothing validates that the 21 rules are sound | **done for derivations and Lemmon; Fitch target refuted structurally** — `LF_Semantics.thy` defines standard satisfaction and model-relative entailment, proves substitution, relevance, freshness, and equality-substitution lemmas, then proves `derivOK_sound` for every reconstructed rule and `lemmon_semantic_soundness` through verified unfolding. The rule roster is semantically sound. The separate Fitch turnstile theorem is false: `openAssumptionFitch` is accepted as a proof of `P` from no premises although `falseInterp` refutes it, because `fitchWF` does not require the conclusion to stand at the outermost level. No rule or checker condition was changed. |
| 5 | Contiguity/laminarity of subproofs in `flatten`, and a biconditional characterisation of positional translatability | **structural results and checker soundness done; proposed biconditional refuted for the current predicate** — `LF_Span.thy`: `subs_block_proof`, `subs_unique`, `subs_span_structural`, `subs_span`; `LF_Positional.thy`: `buildItems_scope_eq`, `buildItems_subrefs`, `lemmonToFitchDirect_fitchWF`. `LF_Conjecture27.thy`: `seven_checks_not_necessary` shows that `premLate` has a well-formed positional image using an unused one-line `FAssume` subproof even though `premiseOrderError` rejects the canonical direct image. A true biconditional would need a deliberately strengthened image predicate excluding unused subproofs; do not silently change `positionalImage`. |
| 6 | Conjecture 28 with auxiliary lines permitted — left open in `LF_Conjecture27.thy` | **done** — `sourceCovered` drops the target-to-source half of `fitchImage`, thereby allowing completely arbitrary auxiliary Fitch lines; `sharedDischarge_no_auxiliary_image`, `c27_no_auxiliary_image`, and `conjecture_28_with_auxiliaries_false` show that the shared-discharge witness still has no image |
| 7 | Conjecture 28's positive half: laminar dependency family ⟹ duplication-free image exists | **done (refuted)** — `dependencyLaminar` formalizes the proposed condition; `ex12_dependency_laminar` proves Example 12 has disjoint dependency regions, while `dependency_laminar_not_sufficient` combines that fact with Theorem 10's no-image result |
| 8 | `lemmon_21` is defined and exported but never used as a hypothesis; `Reit` is admitted unconditionally | **done** — `reit_same_formula`, `reit_same_deps` in `LF_Lemmon`: a reiteration line duplicates the cited line exactly, which is why `lemmon_21` need never be a hypothesis |
| 9 | Notation: make `[b/a]` valid syntax for renaming | **done** — abbreviations for `trm`, `fm`, `fm list` (`LF_Formula`) and `deriv` (`LF_Derivation`) |
| 10 | Notation: make `d ⊩ G ⊢⇩L ψ` parse as `d ⊩` applied to `G ⊢⇩L ψ` | **done** — `⊢⇩L`/`⊢⇩F` are plain infix predicates declared once in `LF_Delta`; `⊩` is `syntax _derivOf (‹_ ⊩ _› [51,50] 45)` with `translations "d ⊩ Γ ⊢⇩L ψ" ⇌ "CONST derivOf d Γ ψ"`. No datatype, no coercion |

## Fixed along the way

* The proposed invariant `flScope fl = boxPath P (flNum fl)` is false when a
  valid `OrElim` names the same discharge pair twice: `boxPath` retains both
  copies, while Fitch has one subproof. `duplicateDischarge` is an accepted,
  well-formed witness. The proved scope and subref characterisations use
  `remdups_adj`; the reconstructed rule roster was not changed.

* The proposed “positional image exists iff the seven checks pass” converse is
  false for the standing `positionalImage` predicate. `premLate_fitch_alt`
  represents the late undischarged assumption as an unused one-line `FAssume`
  subproof, producing a well-formed positional image although the direct checker
  rejects `premLate`. `seven_checks_not_necessary` records the counterexample.

* The first semantic audit found that `fitchWF` permits the whole proof to end
  in an undischarged top-level subproof. Thus `openAssumptionFitch` is
  `fitchCorrect` and proves `P` from `[]`; `falseInterp_not_entails` supplies a
  countermodel. `fitch_semantic_soundness_fails` records the unsoundness. This
  happens outside the reconstructed rules: `derivOK_sound` checks all of them,
  and `lemmon_semantic_soundness` proves every Lemmon sequent model-valid.

* The handwritten tree fallback's global `boxed` set misclassifies an open
  premise when that assumption is discharged only on a dead sibling branch.
  On the shared-discharge proof it drops `P` and emits a citation to line `0`.
  `hlClassifyAssumptions` repairs the classification from the actual ancestor
  dischargers; `hl_exact_complete_uses_tree` is the executable regression.

* The fourth gap (`boxHeadError`) had to be found by *construction*, not by
  argument. The claim that `scopeError` would always catch one assumption
  discharged from two lines is false: it catches `twiceDischarged` only because
  that proof happens to cite across a box boundary, and `reused` does not. Both
  witnesses are kept in `LF_Positional.thy`, the second labelled as the
  near-miss it is.

* `positionalImage` in `LF_Conjecture27.thy` required every assumption line
  of the image to carry `FPremise`, because `toFitchRule Assumption = FPremise`.
  A discharged assumption opens a subproof and so carries `FAssume`, which meant
  no proof containing a discharge could have a positional image and the
  Conjecture 27 and 28 refutations held vacuously. Fixed with `ruleMatches`,
  which admits both for an assumption. `sec2_positional_image` is now a standing
  non-vacuity check: the Section 2 example *does* have a positional Fitch image.
* `[b/a]` was ambiguous with applying a term to the singleton list `[b / a]`,
  since `/` is `inverse_divide` infix; both readings type-check unless the types
  are already pinned. Fixed at the source with `no_notation inverse_divide` in
  `LF_Formula`, not by ascribing types at the site that happened to break.
  Six guard lemmas (`bracket_trm/fm/fms/deriv`, `turnstiles_distinct`,
  `turnstile_composes`) hold by `refl` and fail to *parse* if it regresses.
  Verify such things with `isabelle eval_at -d . -U File.thy LINE`, not by
  observing that the build is green.

## Notation pitfalls, learned the hard way

* `⊢⇩L`/`⊢⇩F` sit at priority 50, the same as `=`. So `Γ ⊢⇩L ψ = X` does **not**
  parse — `=` wants its left argument at 51 and gets 50; `⊢⇩L` wants its right
  argument at 51 and gets 50. Use `⟷` (priority 25), which takes them bare.
  Asserting a turnstile on its own needs no brackets.
* A first attempt made `⊢⇩L`/`⊢⇩F` constructors of a `sequent` datatype with
  `[[coercion holds]]` so a sequent could stand as a proposition. It worked but
  was fragile; the translation above is simpler and needs no coercion.
* Declaring the same notation twice makes every use ambiguous. A stale editor
  process can retain a declaration after it is removed from source. The
  project therefore opens `LF_All.thy` from `HOL`, never from a project heap;
  after a notation change, restart that source-only jEdit process and let the
  imports reprocess.
* Check a notation with `isabelle eval_at -d . -U File.thy LINE`, which prints
  the elaborated command. A green build of a *cached* session is not evidence.
