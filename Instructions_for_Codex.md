# Instructions for Codex — Lemmon/Fitch formalisation

Updated 2026-08-28 for the flat source layout. This file records the working
rules, theory graph, verified results, known limitation, and code-generation
procedure for the current project.

## 1. Toolchain and source-only workflow

Use this Isabelle installation:

```text
/home/dusty/Desktop/Isabelle/Isabelle2025-2/bin/isabelle
```

Do not use the `Isabelle2025-CyPhyAssure` installation.

All Isabelle theories live directly in the project root. `Halvorson/` is source
material supplied by the collaborators. `generated/` contains derived Haskell
and SML snapshots and is not part of the Isabelle import graph.

Open the complete development as editable source from the standard `HOL` image:

```bash
cd /home/dusty/Desktop/Lemmon_Fitch
/home/dusty/Desktop/Isabelle/Isabelle2025-2/bin/isabelle \
  jedit -d . -n -l HOL LF_All.thy
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

It is intentionally referenced in `LF_All.thy`. On the current six-thread
machine it takes roughly 2–3 minutes to compile from `HOL`. The complete cap,
including Haskell and SML exports, takes roughly 4–6 minutes. Let the command
finish unless Isabelle reports an error.

## 3. Theory graph

`LF_All.thy` explicitly imports every maintained theory. The principal chains
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

LF_Formula → LF_Halvorson_Formula → LF_Halvorson → LF_Halvorson_Fitch
                                                    → LF_Halvorson_Semantics
                                                    → LF_Halvorson_DNF
                                                    → LF_Halvorson_Translate
                                                      → LF_Halvorson_Unfold
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
| `LF_Halvorson_Formula` | authoritative `ProofTypes.hs` formula representation and total formula operations |
| `LF_Halvorson` | authoritative twenty-one-rule `LemmonChecker.hs` mirror and verified invariants |
| `LF_Halvorson_Fitch` | authoritative `FitchTypes.hs` representation and `δ⇩H` |
| `LF_Halvorson_Semantics` | exact-layer semantics, all-rule and whole-proof soundness, substitution and propositional-consequence soundness, equality-model audit |
| `LF_Halvorson_DNF` | total propositional NNF/DNF pipeline corresponding to `PropDNF.hs` |
| `LF_Halvorson_Translate` | repaired direct `FitchConvert.hs` Lemmon-to-Fitch route on exact `HL_` types |
| `LF_Halvorson_Unfold` | exact derivation-tree fallback, ancestor-sensitive premise classification, and complete checked route |
| `LF_All` | cap and executable-code export |

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
| `hlRuleOK_sound`, `hlVerifiedCorrect_line_sound`, `hlVerifiedCorrect_sound` | `LF_Halvorson_Semantics` |

Conjecture 28 remains false even with arbitrary auxiliary target lines:
`sourceCovered` requires only that each source line occur in the target.

The proposed positive laminarity condition is refuted by Example 12:
`ex12_dependency_laminar` holds, while `theorem_10_ex12` rules out an image.
The proof `dependency_laminar_not_sufficient` uses `correct_sources(3)`.

## 6. Known semantic limitation

Both Lemmon layers are semantically sound.  In the compact layer,
`derivOK_sound` covers every reconstructed rule and
`lemmon_semantic_soundness` validates the Lemmon turnstile.  In the
authoritative Haskell-shaped layer, `hlRuleOK_sound` covers all twenty-one
checker branches, `hlVerifiedCorrect_line_sound` composes citations by
well-founded dependency induction, and `hlVerifiedCorrect_sound` takes true
open premises to a true conclusion in every standard interpretation.

The current Fitch turnstile is not semantically sound because `fitchWF` permits
the whole proof to end inside an undischarged top-level subproof.
`fitch_semantic_soundness_fails` gives the checked counterexample. This is a
structural root-scope issue, not an unsound reconstructed inference rule. Do not
claim Fitch semantic soundness until the well-formedness definition and every
dependent proof have been updated.

## 7. Code generation

`LF_All.thy` owns the Haskell and SML `export_code` commands. To refresh the
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
application under `Halvorson/lemmon-checker-main`: its parser, Aeson instances,
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

The Haskell checker in `Halvorson/lemmon-checker-main/src` is authoritative.
Its exact roster is localized to `hlCitedLines` and `hlRuleOK` in
`LF_Halvorson.thy`, with Fitch counterparts in `LF_Halvorson_Fitch.thy`.
`hlCorrect` deliberately preserves observable Haskell behavior;
`hlVerifiedCorrect` adds the explicit invariants required by formal theorems.
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
