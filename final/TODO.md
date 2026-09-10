# Completion audit — original paper comparison

Updated 2026-09-09. **The original-paper project is not fully complete.**
The previous closed-out audit compared the development with our revised
paper. The controlling comparison is now
[ORIGINAL_PAPER_COMPARISON.md](ORIGINAL_PAPER_COMPARISON.md), against the
unchanged Desktop PDF preserved in `reference/original-paper/`.

## Required remaining proof work

1. Prove validity of exact `HL_` derivations obtained from every nonempty
   paper-correct Lemmon proof, including all twenty-one rule branches.
2. Prove exact-layer renaming and emission invariants: citation order, real
   box scope, both eigenconstant repairs, conclusion and premise preservation.
   These are the missing general L2–L4/composition results. The compact
   theorems do not discharge them for the different `HL_` datatypes.
3. Deduce that the checked exact translator always succeeds on those sources.
   A theorem about outputs that pass its validator is only conditional safety.
4. Keep the original Conjecture 26 (universal-introduction repair only)
   distinct from our corrected construction (also existential elimination).
   Keep the Conjectures 27/28 citation-preserving interpretation explicit.

The source-to-tree termination result and canonical dependency reconstruction
are now separate exact-layer results. Genuine Fitch nesting, root-premise
semantic soundness, and concrete translation failures have been repaired and
covered by regression checks. See the comparison for precise theorem names
and validation status.

## Historical audit, with corrected scope

Recorded 2026-08-27 through 2026-09-08. The entries below concern completed
compact-layer work or individual implementation tasks; they do not close the
original-paper obligations above.

The supplied Haskell checker was subsequently designated authoritative. The
following migration status is therefore separate from the completed compact
formalisation below:

| Item | Status |
|---|---|
| Exact Haskell `Term`/`PredFormula`, including Boolean constants and equality-as-predicate | **done** — `LF_HLW_Formula.thy` |
| Total versions of partial Boolean and biconditional formula operations | **done**, with executable guard lemmas |
| Exact twenty-one-constructor Lemmon checker and Haskell line-number behavior | **done** — `LF_HLW.thy`, `hlCorrect` |
| Strengthened order/dependency invariants for theorem use | **done** — `hlVerifiedCorrect` |
| Exact Fitch syntax and total Fitch-to-Lemmon `δ⇩H` | **done** — `LF_HLW_Fitch.thy` |
| Source-generated Haskell and SML containing the exact layer | **done** — refreshed 2026-08-28 |
| Standard semantics for the exact `HL_` formulas | **done** — `LF_HLW_Semantics.thy`; includes substitution and `PropTaut` soundness plus the equality-model counterexample |
| Corrected executable DNF pipeline | **done** — `LF_HLW_DNF.thy` covers the missing biconditional cases and rejects non-propositional input explicitly |
| End-to-end soundness theorem for all exact `hlVerifiedCorrect` rules | **done** — `hlRuleOK_sound` covers all twenty-one authoritative rule branches; `hlVerifiedCorrect_line_sound` composes them by well-founded dependency induction; `hlVerifiedCorrect_sound` proves the conclusion true whenever the open premises are true in a standard interpretation |
| Direct Lemmon-to-Fitch algorithm on exact `HL_` types | **done** — `LF_HLW_Translate.thy`; includes positional preservation and a verified round-trip guard |
| Tree Lemmon-to-Fitch fallback migrated from compact `fm`/`just` to exact `HL_` types | **done** — `LF_HLW_Unfold.thy`; includes all 21 derivation rules, both eigenconstant repairs, ancestor-sensitive premise classification, a verified shared-discharge fallback guard, and a checked route with explicit target validation (general all-source success remains open) |
| Haskell regression corpus run against generated `HL_` kernel | **done** — GHC 9.4.7 installed; his kernel compiles unmodified; `differential/` compares both checkers per line: 9,874 comparisons, 0 verdict disagreements, all 860 rejection messages byte-identical, and his own `test/Tests.hs` passes against a shim backed by the generated kernel |
| Parser/Aeson/web application adapter | **not pursued** — see *Open questions*; interface engineering rather than formalisation |

| # | Item | Status |
|---|------|--------|
| 1 | `README.md` is factually wrong: claims one `sorry`, `quick_and_dirty`, and Conjecture 26 open | **done** — sessions, theory table and "what is not proved" rewritten |
| 2 | `lemmonToFitchDirect` is unsound — returns `Inr F` with `¬ fitchWF F` | **done** — four gaps found and plugged: `subScopeError` (cited subproof out of scope; `c27` → `OutOfScope 5 3 2`), `premiseOrderError` (undischarged assumption written too late; `premLate` → `PremiseLate 3 2`), `boxOrderError` (discharge running backwards; `backCP` → `BoxReversed 2 1`), and `boxHeadError` (one assumption discharged from two lines; `reused` → `AssumptionReused 2 3 4`). `LF_Positional.thy` now proves all six conjuncts: `lemmonToFitchDirect_citations` closes the last citation conjunct and `lemmonToFitchDirect_fitchWF` proves `lemmonToFitchDirect P = Inr F ⟹ fitchWF F`. The proof includes `buildItems_scope_eq` and `buildItems_subrefs`; both remove duplicate box heads because a valid `OrElim` may cite one discharge pair twice (`duplicateDischarge`) while the image contains one subproof. |
| 3 | `theorem_10` states "our checker rejects ex11/ex12", not the paper's "no positional Fitch image exists" | **done** — `LF_Theorem10.thy`: `theorem_10`, proved for both examples via `subs_span` |
| 4 | No semantics anywhere — nothing validates that the 21 rules are sound | **done, both turnstiles** — `LF_Semantics.thy` defines standard satisfaction and model-relative entailment, proves substitution, relevance, freshness and equality-substitution lemmas, then `derivOK_sound` for every reconstructed rule and `lemmon_semantic_soundness` for the Lemmon turnstile. The Fitch turnstile was *unsound* on the first audit and is now sound: the root-scope hole is closed by the `concludesAtTop` conjunct of `fitchWF`, and `fitch_semantic_soundness` follows via `theorem_4_forward` + `proposition_5` + `lemmon_semantic_soundness` with no new model theory. No rule or rule-checking condition was changed. |
| 5 | Contiguity/laminarity of subproofs in `flatten`, and a biconditional characterisation of positional translatability | **structural results and checker soundness done; the biconditional is open again** — `LF_Span.thy`: `subs_block_proof`, `subs_unique`, `subs_span_structural`, `subs_span`; `LF_Positional.thy`: `buildItems_scope_eq`, `buildItems_subrefs`, `lemmonToFitchDirect_fitchWF`. The old counterexample to the converse, `seven_checks_not_necessary`, depended on an image that ended inside an unused `FAssume` subproof, which `concludesAtTop` now rejects; `premLate_no_positional_image` shows that source has **no** well-formed positional image at all, so for it the checker and the existence question agree. No counterexample is currently known, and `checks_reject_only_imageless_sources` (`LF_Theorem10.thy`) now proves all six witnesses imageless — `backCP` via `image_subproof_ordered` (a cited subproof runs forwards) and `reused` via `subs_unique_proof` (a subproof is determined by its assumption line). Evidence for the converse, not a proof. |
| 6 | Conjecture 28 with auxiliary lines permitted — left open in `LF_Conjecture27.thy` | **done** — `sourceCovered` drops the target-to-source half of `fitchImage`, thereby allowing completely arbitrary auxiliary Fitch lines; `sharedDischarge_no_auxiliary_image`, `c27_no_auxiliary_image`, and `conjecture_28_with_auxiliaries_false` show that the shared-discharge witness still has no image |
| 7 | Fixed-order laminarity condition: laminar dependency family ⟹ positional image exists | **done (refuted)** — `dependencyLaminar` formalizes the proposed condition; `ex12_dependency_laminar` proves Example 12 has disjoint dependency regions, while `dependency_laminar_not_sufficient` combines that fact with Theorem 10's no-image result |
| 8 | `lemmon_21` is defined and exported but never used as a hypothesis; `Reit` is admitted unconditionally | **done** — `reit_same_formula`, `reit_same_deps` in `LF_Lemmon`: a reiteration line duplicates the cited line exactly, which is why `lemmon_21` need never be a hypothesis |
| 9 | Notation: make `[b/a]` valid syntax for renaming | **done** — abbreviations for `trm`, `fm`, `fm list` (`LF_Formula`) and `deriv` (`LF_Derivation`) |
| 10 | Notation: make `d ⊩ G ⊢⇩L ψ` parse as `d ⊩` applied to `G ⊢⇩L ψ` | **done** — `⊢⇩L`/`⊢⇩F` are plain infix predicates declared once in `LF_Delta`; `⊩` is `syntax _derivOf (‹_ ⊩ _› [51,50] 45)` with `translations "d ⊩ Γ ⊢⇩L ψ" ⇌ "CONST derivOf d Γ ψ"`. No datatype, no coercion |

## Fixed along the way

* The proposed invariant `flScope fl = boxPath P (flNum fl)` is false when a
  valid `OrElim` names the same discharge pair twice: `boxPath` retains both
  copies, while Fitch has one subproof. `duplicateDischarge` is an accepted,
  well-formed witness. The proved scope and subref characterisations use
  `remdups_adj`; the reconstructed rule roster was not changed.

* The semantic audit found that `fitchWF` permitted the whole proof to end in an
  undischarged top-level subproof: `openAssumptionFitch = [FSub (Subproof 1 P [])]`
  was `fitchCorrect`, had no premises, and had `P` as its conclusion, so
  `[] ⊢⇩F P` held for arbitrary `P`. The defect was in the well-formedness
  definition, not in any rule. It is now closed by the `concludesAtTop` conjunct,
  and `openAssumptionFitch_fails_only_root_scope` records by evaluation that the
  witness satisfies every *other* conjunct — so the new one is not redundant.
  Dependents rechecked: `L2_L3` (via `concludesAtTop_premLines_append`),
  `lemmonToFitchDirect_fitchWF` (via `lemmonToFitchDirect_concludesAtTop`, which
  holds because a box is closed by a strictly later line and so the source's last
  line opens none), and `corollary_6`, whose `cor6_wide` witness had to gain a
  top-level closing line.

* Closing that hole also destroyed the counterexample to the converse of
  `lemmonToFitchDirect_fitchWF`. The old `premLate_fitch_alt` hid a late
  undischarged assumption in an unused one-line `FAssume` subproof — and *ended*
  there. `premLate_no_positional_image` now shows the dodge cannot be repaired:
  the image must end in a line matching the late assumption, at the outermost
  level, where `FAssume` cannot stand, so it is an `FPremise` following a
  non-premise and `premisesFirst` fails. Whether the seven checks are necessary
  in general is open again.

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
  project therefore opens `Lemmon_Fitch.thy` from `HOL`, never from a project heap;
  after a notation change, restart that source-only jEdit process and let the
  imports reprocess.
* Check a notation with `isabelle eval_at -d . -U File.thy LINE`, which prints
  the elaborated command. A green build of a *cached* session is not evidence.

## Definition of done

The deliverable is `lemmon-fitch.tex`, the revised paper. The formalisation
exists to back its claims, so completion is checkable rather than a matter of
taste. The earlier criteria below were insufficient for the original-paper request.
Identifier resolution is not evidence that a theorem states the original claim.
Completion now also requires the proof obligations at the top of this file:

1. **Every substantive claim must match a proved statement.** The historical check found all 49 Isabelle
   identifiers cited by the paper resolve to definitions or theorems in the
   development. (`SubRef`, `boxed`, `fitchWellFormed` and `eval` are references
   to the Haskell, not to Isabelle, and are correct as such.) The cross-check
   is mechanical and can be re-run; it is a name-resolution check, not the acceptance test for mathematical coverage.
2. **The development builds clean and the exports regenerate.** `isabelle build
   -d . -e Lemmon_Fitch` is the batch check. The current 34-theory source
   check and regenerated-code results are recorded in `VALIDATION.md`.
3. **Remaining requirements are recorded as open work.** Above; ancillary questions follow.

## Open questions, not pursued

These are recorded so that they are not mistaken for oversights. These ancillary questions are separate from the required exact-layer proof
work at the top of this file.

* **Is `hlCorrect` alone semantically sound?** `hlVerifiedCorrect_sound` is
  proved of `hlVerifiedCorrect`, which adds `hlDependencyClosed` and
  `hlCanonicalOrder` to the supplied checker's own condition. Both additions
  are genuinely extra, with isolating witnesses (`hl_cp_misordered`,
  `hl_lem_free_dependency`), and neither witness is unsound. Why the obvious
  attacks fail is recorded in `LF_HLW_Examples.thy`; that is an argument,
  not a proof. Settle it by building a witness, not by reasoning from the
  definitions — the fourth obstruction is the standing reason why.

* **Are the seven direct-translation checks necessary as well as sufficient?**
  Sufficiency is `lemmonToFitchDirect_fitchWF`. For the converse, all six
  witnesses the checks were built from are proved imageless
  (`checks_reject_only_imageless_sources`), but six sources are not all
  sources. The counterexample that previously refuted the converse depended on
  the root-scope hole and did not survive closing it.

* **The parser/Aeson/web application adapter.** The differential test and the
  regression-corpus run are done (see `differential/`), and a shim in
  `differential/shim/` already replaces his `LemmonChecker` module with one
  backed by the generated kernel. What is *not* done is wiring that into the
  web application, which additionally needs the Aeson instances, the parser,
  and a decision about `FitchConvert` — our translator has additional diagnostics
  (`PremiseLate`, `BoxReversed`, `AssumptionReused`, `SourceNotVerified`,
  and the exact checked route's `HL_TargetNotVerified`), so swapping it in
  changes observable behavior. The checked route also enforces actual Fitch
  scope and source-sequent preservation. Do not delete
  `reference/lemmon-checker-main` before its interface code is copied
  somewhere maintained; Isabelle does not generate the parser, JSON codecs,
  OCR pipeline, LaTeX rendering or web routes.

* **Further defect hunting in the supplied Haskell.** Sixteen findings are
  recorded in `HASKELL_AUDIT.md`, including two that are soundness bugs rather
  than omissions. The search was thorough over the logical kernel and was
  stopped there deliberately; the interface modules were read but not audited
  to the same standard.
