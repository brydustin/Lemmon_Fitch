# Development notes — Lemmon/Fitch formalisation

Updated 2026-09-09 after comparison with the original Desktop paper.
`ORIGINAL_PAPER_COMPARISON.md` and the open work at the top of `TODO.md`
control completion claims; the compact totality theorem is not exact-layer
translation totality. This file records the working
rules, theory graph, verified results, known limitation, and code-generation
procedure for the current project.

## 1. Toolchain and source-only workflow

Use this Isabelle installation:

```text
/home/dusty/Desktop/Isabelle/Isabelle2025-2/bin/isabelle
```

Do not use the `Isabelle2025-CyPhyAssure` installation.

All Isabelle theories live directly in the project root. `reference/lemmon-checker-main/` contains supplied code;
`reference/original-paper/` preserves the original paper unchanged. `generated/` contains derived Haskell
and SML snapshots and is not part of the Isabelle import graph.

Open the complete development as editable source from the standard `HOL` image:

```bash
cd /home/dusty/Desktop/Lemmon_Fitch
/home/dusty/Desktop/Isabelle/Isabelle2025-2/bin/isabelle \
  jedit -d . -n -l HOL Lemmon_Fitch.thy
```

The `-l HOL` and `-n` options are required. Do not open the cap with
`-l Lemmon_Fitch` or `-R`: a project session image would hide imported project
theories from the editable source view.

Before editing, check for live unsaved jEdit buffers:

```bash
find . -maxdepth 1 \( -name '#*.thy#' -o -name '.#*.thy' \) -print
```

Never overwrite the corresponding `.thy` while such a buffer exists.

For an authoritative source check of a command, use `eval_at` from `HOL`, for
example:

```bash
/home/dusty/Desktop/Isabelle/Isabelle2025-2/bin/isabelle \
  eval_at -v -d . -l HOL -U LF_Delta.thy 36 'term "\<delta> F"'
```

This guards against stale constants from cached images. A timeout or an
unfinished command is not a successful check.

## 2. The slow command

`LF_Lemmon.thy:218–229` is the eleven-equation definition

```isabelle
fun eqsub :: "nm ⇒ nm ⇒ fm ⇒ fm ⇒ bool"
```

It is intentionally referenced in `Lemmon_Fitch.thy`. On the current six-thread
machine it takes roughly 2–3 minutes to compile from `HOL`. The complete cap,
including Haskell and SML exports, takes roughly 4–6 minutes. Let the command
finish unless Isabelle reports an error.

## 3. Theory graph

`Lemmon_Fitch.thy` explicitly imports every maintained theory. The principal chains
are:

```text
LF_Formula
  → LF_Lemmon
    → LF_Fitch
      → LF_Delta
        → LF_Direct
          → LF_Derivation
            → LF_Unfold
              → LF_Render
                → LF_Examples

LF_Unfold → LF_WellFormed ─┐
LF_Unfold → LF_Faithful ───┴→ LF_Check → LF_Conjecture

LF_Examples → LF_Span → LF_Positional → LF_Conjecture27 → LF_Theorem10

LF_Faithful + LF_Examples → LF_Semantics

LF_Formula → LF_HLW_Formula → LF_HLW → LF_HLW_Fitch
  → LF_HLW_Scope → LF_HLW_Semantics → LF_HLW_DNF → LF_HLW_Translate
    → LF_HLW_Unfold → LF_HLW_Examples → LF_HLW_Delta

(Canonical dependency reconstruction branches from LF_HLW;
Fitch semantic soundness branches from LF_HLW_Semantics; translation proofs
branch from LF_HLW_Unfold. The principal chain is otherwise linear: everything from LF_HLW_Fitch
onwards is in scope in LF_HLW_Delta.  The compact layer is NOT --- the
two stacks share only LF_Formula, so a doc antiquotation naming e.g. fitchWF
from a Halvorson theory is an "Undefined constant" error.)
```

Responsibilities:

| theory | role |
|---|---|
| `LF_Formula` | terms, formulas, free variables, instantiation, renaming, readable object-language notation |
| `LF_Lemmon` | Lemmon lines, reconstructed rules, dependencies, rule checker |
| `LF_Fitch` | Fitch lines/subproofs, flattening, scope, citations, well-formedness |
| `LF_Delta` | the map `δ : fitch_proof ⇒ lemmon_proof` and the two turnstiles |
| `LF_Direct` | partial positional Lemmon-to-Fitch construction and seven diagnostics |
| `LF_Derivation` | tree derivations, Lemma 23, Corollary 24 |
| `LF_Unfold` | total unfolding route and renaming repair |
| `LF_WellFormed` | well-formedness of the tree-generated Fitch proof |
| `LF_Faithful` | sound conversion from correct Lemmon proofs to derivations |
| `LF_Check` | preservation of Fitch rule checking through the traversal |
| `LF_Conjecture` | Conjecture 26 and translation totality |
| `LF_Span` | subproof contiguity and numerical spans |
| `LF_Positional` | exact direct-image scope/subproof characterisations and checker soundness |
| `LF_Conjecture27` | Definition 9 as `positionalImage`; refutations of Conjectures 27 and 28 |
| `LF_Theorem10` | no positional image for Examples 11 and 12 |
| `LF_Semantics` | standard satisfaction and semantic soundness audit |
| `LF_HLW_Formula` | authoritative `ProofTypes.hs` formula representation and total formula operations |
| `LF_HLW` | authoritative twenty-one-rule `LemmonChecker.hs` mirror and verified invariants |
| `LF_HLW_Fitch` | authoritative `FitchTypes.hs` representation, `δ⇩H`, and the root-scope condition the Haskell omits |
| `LF_HLW_Semantics` | exact-layer semantics, all-rule and whole-proof soundness, substitution and propositional-consequence soundness, equality-model audit |
| `LF_HLW_DNF` | total propositional NNF/DNF pipeline corresponding to `PropDNF.hs` |
| `LF_HLW_Translate` | repaired direct `FitchConvert.hs` Lemmon-to-Fitch route on exact `HL_` types |
| `LF_HLW_Unfold` | exact derivation-tree fallback, ancestor-sensitive premise classification, and conditionally safe checked route |
| `Lemmon_Fitch` | cap and executable-code export |

## 4. Translation vocabulary

Given a Fitch proof `F`, `δ F` is its Lemmon image. `fitchToLemmon` is the
descriptive generated-code name for the same function.

Given a Lemmon proof `P`:

- `lemmonToFitchDirect P` attempts Definition 9’s positional route and returns
  either a diagnostic or a Fitch proof.
- `toDerivation P` followed by `derivationToFitch` unfolds the dependency graph
  to a tree. It may duplicate or renumber lines.
- `lemmonToFitch P` tries the direct route and falls back to the tree route.
- `lemmonToFitchChecked P` checks a direct candidate before accepting it.

Definition 9 is represented relationally:

```isabelle
positionalImage F P ⟷ list_all2 lineMatches (flatten F) P
```

This preserves the sequence, line numbers, formulas, and corresponding rules.
A Lemmon `Assumption` may match either Fitch `FPremise` or `FAssume`. The phrase
“has a positional Fitch image” must be written

```isabelle
∃F. fitchWF F ∧ positionalImage F P
```

because `positionalImage` alone is a correspondence predicate, not the demand
that its first argument be a well-formed proof. Keep
`sec2_positional_image` as the non-vacuity guard.

## 5. Verified headline results

There is no `sorry`, `oops`, `axiomatization`, or `quick_and_dirty` setting.

| result | theory |
|---|---|
| `proposition_5`, `theorem_4_forward`, `proposition_7` | `LF_Delta` |
| `renaming`, `renaming_sequent`, `renaming_open` | `LF_Derivation` |
| `proposition_18`, `unfolding_terminates` | `LF_Unfold` |
| `L2_L3` | `LF_WellFormed` |
| `toDerivation_sound` | `LF_Faithful` |
| `L4_derivation` | `LF_Check` |
| `conjecture_26`, `conjecture_26_sequent`, `translation_total` | `LF_Conjecture` |
| `lemmonToFitchDirect_fitchWF` | `LF_Positional` |
| `theorem_10` | `LF_Theorem10` |
| `conjecture_27_false`, `conjecture_28_false`, `conjecture_28_with_auxiliaries_false` | `LF_Conjecture27` |
| `dependency_laminar_not_sufficient` | `LF_Theorem10` |
| `derivOK_sound`, `lemmon_semantic_soundness` | `LF_Semantics` |
| `hlRuleOK_sound`, `hlVerifiedCorrect_line_sound`, `hlVerifiedCorrect_sound` | `LF_HLW_Semantics` |

Conjecture 28 remains false even with arbitrary auxiliary target lines:
`sourceCovered` allows auxiliary target lines but preserves the source rules
and citation relationships. This does not refute arbitrary formula-only
translations with rewritten justifications.

The fixed-number positional laminarity condition is refuted by Example 12
(the original Remark 13 permits a repairing permutation):
`ex12_dependency_laminar` holds, while `theorem_10_ex12` rules out an image.
The proof `dependency_laminar_not_sufficient` uses `correct_sources(3)`.

## 6. Semantic soundness

Both Lemmon layers are semantically sound.  In the compact layer,
`derivOK_sound` covers every reconstructed rule and
`lemmon_semantic_soundness` validates the Lemmon turnstile.  In the
authoritative Haskell-shaped layer, `hlRuleOK_sound` covers all twenty-one
checker branches, `hlVerifiedCorrect_line_sound` composes citations by
well-founded dependency induction, and `hlVerifiedCorrect_sound` takes true
open premises to a true conclusion in every standard interpretation.

The Fitch turnstile is now sound too. It was not: `fitchWF` permitted the whole
proof to end inside an undischarged top-level subproof, so
`[FSub (Subproof 1 P [])]` was accepted as a proof of `P` from no premises. The
repair is the `concludesAtTop` conjunct of `fitchWF`, which requires the last
item of the proof to be a top-level line; `fitchWF_conclusion_top` then gives
the conclusion line an empty scope, and `fitch_semantic_soundness` follows from
`theorem_4_forward`, `proposition_5` and `lemmon_semantic_soundness` with no new
model theory. `openAssumptionFitch_fails_only_root_scope` records by evaluation
that the witness satisfies every other conjunct, so the new one is not
redundant.

The authoritative layer now has genuine nesting checks in
`hlFitchNestedWellFormed`, a root conclusion requirement, and the explicit
`hlFitchPremiseClosed` guard connecting dependency premises with displayed
outer premises. `hlFitchVerified` checks these and the erased Lemmon proof.
`hlFitchCorrect` additionally checks eigenconditions against all outer premises
and enclosing assumptions (`LF_HLW_Scope.thy`). Both are semantically sound
from displayed premises (`LF_HLW_Fitch_Semantics.thy`). The paper's Theorem 22
still distinguishes dependency validity from the stronger Fitch scope rules.

Both routes of `hlLemmonToFitchChecked` now demand full `hlFitchCorrect`,
unchanged conclusion, and no premises beyond the source conclusion's open
premises. The tree emitter starts with its outer premises in eigenconstant
scope. Raw `hlLemmonToFitchDirect`/`hlLemmonToFitch` remain diagnostic,
unchecked construction interfaces; use the checked API for accepted proofs.
General all-source success of that API remains to be proved.

**When adding a Fitch-side condition, put it on the verified predicate, never
on `hlFitchWellFormed`.** Two correspondence lemmas depend on the latter
accepting exactly what the Haskell accepts.

**The sharpest open question about the authoritative checker.**
`hlVerifiedCorrect_sound` is stated of `hlVerifiedCorrect` = `hlCorrect` +
`hlDependencyClosed` + `hlCanonicalOrder`. Only `hlCorrect` is Halvorson's;
`hlCanonicalOrder` is an invariant `checkStructure` fails to enforce (audit
finding 4). So the theorem does not by itself say the supplied checker is sound.
Both added invariants are genuinely extra, each with an isolating witness in
`LF_HLW_Examples.thy`: `hl_cp_misordered` fails only `hlCanonicalOrder`,
`hl_lem_free_dependency` fails only `hlDependencyClosed`. Neither is unsound —
both conclude tautologies. The structural reason the attacks fail is recorded
there: `HL_LEM` is the only branch of `hlRuleOK` that leaves the dependency set
free, its formula is valid so a free set can only enlarge the reported premises
(weakening the sequent), and every subtraction discharges a line the checker
requires to be an assumption. Note `hlStructureOK` already forces distinct line
numbers, so duplicate-number attacks are closed off. Whether `hlCorrect` alone
admits a semantically invalid proof is still unsettled — build a witness, do not
argue it from the definitions.

## 7. Code generation

`Lemmon_Fitch.thy` owns the Haskell and SML `export_code` commands. To refresh the
checked-in snapshots:

```bash
./generate_code.sh
```

The script source-processes every theory from `HOL` in a private temporary
session and copies these files into `generated/`:

```text
generated/haskell/LemmonFitch.hs
generated/haskell/Str_Literal.hs
generated/sml.ML
```

The generated public API includes both the compact translation layer and the
authoritative `HL_` layer. The latter has Haskell-shaped Boolean formulas,
all twenty-one supplied justifications, `hlCorrect`, `hlVerifiedCorrect`, the
complete Fitch syntax, and `hlFitchToLemmon` (`δ⇩H`).
It also includes `hlLemmonToFitchDirect`, `hlToDerivation`,
`hlDerivationToFitch`, and `hlLemmonToFitchChecked` on those exact types.

Do not describe this generated module as a drop-in replacement for the whole
application under `reference/lemmon-checker-main`: its parser, Aeson instances,
OCR, LaTeX, web, and corpus modules still require an adapter. The rule-roster
decision itself is settled—the supplied Haskell checker is authoritative.
`HASKELL_AUDIT.md` records source defects, Isabelle totalisations, and the
remaining interface-adapter work. Preserve the interface
modules if `Halvorson/` is removed; Isabelle does not generate them.

The semantic relation `modelEntails` is intentionally not executable code: it
quantifies over arbitrary HOL interpretations and valuations. A generated
finite-model evaluator would require a separate finite-domain representation.
Parsers, JSON, OCR, LaTeX, and web/UI integration in `Halvorson/` are interface
code rather than the verified logical kernel and are not generated here.

## 8. Readability conventions

Use the descriptive aliases in expository statements and the compact names in
recursive proofs where they keep the proof legible:

| compact internal name | reader-facing name |
|---|---|
| `trm`, `fm`, `nm`, `vr` | `object_term`, `formula`, `individual_name`, `object_variable` |
| `fvs`, `rn`, `inst` | `freeVariablesInFormula`, `renameInFormula`, `instantiateFormula` |
| `pline`, `just` | `lemmon_line`, `proof_justification` |
| `depsAt`, `depFms`, `ruleOK` | `dependenciesAt`, `dependencyFormulas`, `ruleIsCorrect` |
| `fline`, `flScope` | `flattened_fitch_line`, `enclosingAssumptions` |

Displayed object formulas should prefer `⊥ₒ`, `¬ₒ`, `∧ₒ`, `∨ₒ`, `⟶ₒ`,
`⟷ₒ`, `=ₒ`, `∀ₒ`, and `∃ₒ`. Displayed proofs should prefer
`⟨Γ,n,φ,j⟩L`, `⟨n,φ,r⟩F`, and `⟦a:φ; body⟧F` over raw constructors.

The two provability predicates are `Γ ⊢⇩L φ` and `Γ ⊢⇩F φ`. The derivation
judgement is `d ⊩ Γ ⊢⇩L φ`.

Renaming syntax `[b/a]` relies on `no_notation inverse_divide` in
`LF_Formula.thy`. Keep the six parse guards `bracket_trm`, `bracket_fm`,
`bracket_fms`, `bracket_deriv`, `turnstiles_distinct`, and
`turnstile_composes`.

## 9. Rule-roster discipline

The Haskell checker in `reference/lemmon-checker-main/src` is authoritative.
Its exact roster is localized to `hlCitedLines` and `hlRuleOK` in
`LF_HLW.thy`, with Fitch counterparts in `LF_HLW_Fitch.thy`.
`hlCorrect` deliberately preserves observable Haskell behavior;
`hlVerifiedCorrect` adds explicit order/dependency-closure invariants.
`hlPaperCorrect` additionally enforces the original Definition 3 dependency
arithmetic, including empty dependencies for excluded middle; this is required
for the exact Proposition 7 reconstruction theorem.
The older compact roster in `LF_Lemmon.thy` is internal proof infrastructure,
not a competing specification.

If a rule-related theorem fails, identify the rule and report it. Do not change
the authoritative roster merely to make a proof succeed. Repairing a partial
Haskell pattern means adding the missing total case in Isabelle and recording
the discrepancy; a rule change requires rechecking examples, translations,
semantic soundness, and regenerated code.

`Reit` is not one of the twenty-one rules. It is admitted so that `δ` is total
on Fitch proofs using reiteration and so the unfolding can emit required
reiterations. `reit_same_formula` and `reit_same_deps` explain why no theorem
needs `lemmon_21` as a hypothesis.
