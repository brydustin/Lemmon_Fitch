# Dependency and Scope, in Isabelle/HOL

An Isabelle/HOL formalisation of Hans Halvorson, *Dependency and Scope: On the
Translation Between Lemmon and Fitch Proofs*, together with a verified Haskell
kernel generated from it.

The original 14-page draft is preserved unchanged in
[`reference/original-paper/`](reference/original-paper/README.md). The root paper
and the paper under `reference/lemmon-checker-main/paper/` are later revisions.
[`ORIGINAL_PAPER_COMPARISON.md`](ORIGINAL_PAPER_COMPARISON.md) maps the original
claims to their formal statements and corrections.

**What is proved.** The construction theorem holds, unconditionally, at the
exact `HL_` types:

> for every nonempty paper-correct Lemmon proof `P`, the checked translation
> `hlLemmonToFitchChecked P` returns a Fitch proof `F` that passes every check
> (`hlFitchCorrect F`), keeps the conclusion, and needs no premise the source
> did not already have.

That is `hlPaperCorrect_toFitch` in `LF_HLW_Construct.thy`. It is not a
conditional guarantee about outputs that happen to pass the validator: the
translation is proved to succeed. The route is left existential because the
checked translation tries the direct algorithm first and falls back to the
derivation-tree construction, and Conjecture 27 is false — see
[`LF_Conjecture27.thy`](LF_Conjecture27.thy) — so no single direct algorithm
can be claimed.

**What is not.** The impossibility results now hold at the exact types too:
`hl_theorem_10`, `hl_conjecture_27_false` and `hl_conjecture_28_false` in
[`LF_HLW_Theorem10.thy`](LF_HLW_Theorem10.thy). They rest on three structural
facts about the boxes of an exact Fitch proof — spans never cross, nothing
outside a box cites into it, and two distinct boxes never share a last line.
What remains is engineering rather than mathematics: the web application has
not been adapted to the generated Aeson/parser interface. See
[`PROJECT_GOALS.md`](PROJECT_GOALS.md) for the decisions recorded as
deliberately not pursued.

Section 7 of the paper reports that the translations "were implemented in
Haskell against the proof checker for *How Logic Works*". That checker is the
authoritative specification for the executable rule language. Isabelle now
reproduces its formula, Lemmon, and Fitch datatypes and its twenty-one rule
checks under `HL_`/`hl` names, and generates them from `Lemmon_Fitch.thy`. The web
application has not yet been adapted to the generated Aeson/parser interface;
see `HASKELL_AUDIT.md` before treating the generated module as a drop-in
application replacement.

## Opening and checking the source

Open the cap directly from Isabelle's standard `HOL` image:

```
/home/dusty/Desktop/Isabelle/Isabelle2025-2/bin/isabelle \
  jedit -d . -n -l HOL Lemmon_Fitch.thy
```

The `-l HOL` and `-n` options are intentional. They make Isabelle process every
project theory as editable source; no `Lemmon_Fitch` heap is selected or built.
All `.thy` files are at the project root, and `Lemmon_Fitch.thy` explicitly imports
every one of them. The `ROOT` session exists only for optional batch checking;
it is not needed for normal editing.

No session sets `quick_and_dirty`, and the development contains no `sorry`.

`Lemmon_Fitch.thy` is the single code-generation entry point. When the cap has
finished processing in jEdit, its Haskell and SML outputs appear below
`isabelle-export:/Lemmon_Fitch/code/`; this does not require a project heap.

## The theories

| file | what it is |
|---|---|
| `LF_Formula.thy` | the object language: terms, formulas, names, free variables, instantiation, renaming, freshness |
| `LF_Lemmon.thy` | Definition 1: Lemmon lines, the compact reconstructed rules, the dependency arithmetic of Definition 3, and the checker |
| `LF_Fitch.thy` | Definition 2: Fitch items and subproofs, flattening, Definition 19's scope, well-formedness |
| `LF_Delta.thy` | Section 3: δ, Proposition 5, Theorem 4 (one direction), Proposition 7 |
| `LF_Direct.thy` | Section 4: the positional translation and its seven obstructions |
| `LF_Derivation.thy` | Section 5: derivations as trees, Lemma 23 (Renaming), Corollary 24 |
| `LF_Unfold.thy` | Definition 21: the unfolding translation with the renaming repair; Proposition 18; (L1) |
| `LF_Render.thy` | a pretty-printer, so that `value` shows proofs rather than terms |
| `LF_Examples.thy` | the paper's proofs, checked by evaluation |
| `LF_Span.thy` | a subproof occupies a contiguous block of the flattened proof (`subs_span`) |
| `LF_Positional.thy` | exact positional geometry and soundness of the seven-check direct construction |
| `LF_Semantics.thy` | model satisfaction; derivation and Lemmon soundness; the Fitch root-scope counterexample |
| `LF_HLW_Formula.thy` | exact `ProofTypes.hs` term/formula representation and total formula operations |
| `LF_HLW.thy` | exact twenty-one-rule `LemmonChecker.hs` mirror, plus strengthened verified invariants |
| `LF_HLW_Canonical.thy` | original exact dependency arithmetic, `hlPaperCorrect`, and Proposition 7 reconstruction/uniqueness |
| `LF_HLW_Fitch.thy` | exact `FitchTypes.hs` syntax and the authoritative Fitch-to-Lemmon map `δ⇩H` |
| `LF_HLW_Scope.thy` | scope-based checking using outer premises and enclosing assumptions |
| `LF_HLW_Semantics.thy` | standard semantics for the exact formula layer; soundness of all twenty-one rules and complete verified proofs; equality-model counterexample |
| `LF_HLW_Fitch_Semantics.thy` | semantic soundness from the premises displayed at the outer Fitch level |
| `LF_HLW_DNF.thy` | corrected executable version of `PropDNF.hs`, including biconditionals |
| `LF_HLW_Translate.thy` | repaired direct Lemmon-to-Fitch translation on the exact Haskell-shaped datatypes |
| `LF_HLW_Unfold.thy` | exact derivation-tree fallback, both eigenconstant repairs, and checked route |
| `LF_HLW_Translation_Proofs.thy` | exact unfolding termination/success and conditional guarantees for accepted translations |
| `LF_HLW_Derivation.thy`, `LF_HLW_Faithful.thy` | exact tree correctness; every verified nonempty source unfolds correctly, with its conclusion and no additional premises |
| `LF_HLW_Renaming.thy`, `LF_HLW_Rule_Transfer.thy` | renaming foundations, exact rule dependency arithmetic and eigenconstant antitonicity |
| `LF_HLW_Regression.thy` | outer-premise eigenconstant regressions and a tree example for every exact rule |
| `LF_WellFormed.thy` | (L2) and (L3) of Section 6.1, and the conclusion and premises of the image |
| `LF_Faithful.thy` | Section 5.1: `toDerivation_sound` |
| `LF_Check.thy` | (L4) of Section 6.1, and the side conditions the repair preserves |
| `LF_Conjecture.thy` | corrected compact Conjecture 26 with both eigenconstant repairs |
| `LF_Conjecture27.thy` | compact citation-preserving Conjectures 27 and 28, refuted; Definition 9 as the predicate `positionalImage` |
| `LF_Theorem10.thy` | Theorem 10 as the paper states it: Examples 11 and 12 have no positional Fitch image |
| `LF_HLW_Report.thy` | executable per-line reports and agreement with the exact checker |
| `Lemmon_Fitch.thy` | cap theory importing the complete development and generating Haskell and SML |

## Proofs are objects

A Lemmon proof is a list of `ProofLine` values; a Fitch proof is a list of
`FLine` and `FSub` values. δ and both translations are ordinary executable
functions on them, so they run:

```isabelle
value "showLemmon (δ sec2_fitch)"
value "showTranslation (lemmonToFitch ex11)"
```

and the corresponding equations are theorems settled by the code generator:

```isabelle
lemma sec2_delta: "δ sec2_fitch = sec2_lemmon" by eval
lemma sec2_roundtrip: "lemmonToFitchDirect sec2_lemmon = Inr sec2_fitch" by eval
```

### The running example of Section 2

`value "showFitch sec2_fitch"` and `value "showLemmon (δ sec2_fitch)"`:

```
1    P                                   Premise            1         (1)   P                          A
2    | Q                                 Assume             2         (2)   Q                          A
3    | (P & Q)                           &I 1,2             1,2       (3)   (P & Q)                    1,2 &I
4    (Q -> (P & Q))                      CP 2-3             1         (4)   (Q -> (P & Q))             2,3 CP
```

### Section 6.3: the two proofs with no positional image

Examples 11 and 12 have no scope tree under which every citation is permitted
(Theorem 10), so `lemmonToFitch` falls back to the unfolding.
`value "showTranslation (lemmonToFitch ex11)"` and the same for `ex12`:

```
-- via a derivation tree                 -- via a derivation tree
1    | Q                     Assume      1    P                              Premise
2    | | P                   Assume      2    (P v R)                        vI 1
3    | | (P & Q)             &I 2,1      3    | Q                            Assume
4    | (P -> (P & Q))        CP 2-3      4    | (Q & Q)                      &I 3,3
5    (Q -> (P -> (P & Q)))   CP 1-4      5    (Q -> (Q & Q))                 CP 3-4
                                         6    ((P v R) & (Q -> (Q & Q)))     &I 2,5
```

Five lines and six — the lengths of the originals, with no line duplicated,
which is what Section 6.3 reports.

### Theorem 22 and the renaming repair

`value "showTranslation (lemmonToFitch thm22_lemmon)"` — the paper's function,
which accepts the positional image without checking it — against
`value "showTranslation (lemmonToFitchChecked thm22_lemmon)"`:

```
-- positional                                -- via a derivation tree
1    Ax.G(x)                    Premise      1    Ax.G(x)                    Premise
2    | F(a)                     Assume       2    | F(a)                     Assume
3    | G(a)                     AE 1         3    | G(cc)                    AE 1
4    | Ay.G(y)                  AI 3         4    | Ay.G(y)                  AI 3
5    | (F(a) & Ay.G(y))         &I 2,4       5    | (F(a) & Ay.G(y))         &I 2,4
6    (F(a) -> (F(a) & Ay.G(y))) CP 2-5       6    (F(a) -> (F(a) & Ay.G(y))) CP 2-5
```

The left one is not a correct Fitch proof; line 4 generalises on `a` while
`F(a)` stands as an undischarged assumption in its scope. On the right a single
line changes, exactly as Section 5.4 says: line 3 instantiates to a name
occurring nowhere else — `cc` where the paper writes `b` — and nothing moves.

## The generated code

Processing `Lemmon_Fitch.thy` generates `haskell/LemmonFitch.hs`,
`haskell/Str_Literal.hs`, and `sml.ML` in the cap theory's logical export
filesystem (`isabelle-export:/Lemmon_Fitch/code/`). To refresh the checked-in
distribution snapshots directly from source, run:

```bash
./generate_code.sh
```

The script uses `process_theories` with `HOL` and a private temporary source
session; it does not select or create a persistent `Lemmon_Fitch` heap. The
declarations the paper
displays come out of the generator as the paper writes them:

```haskell
data Deriv = Deriv Fm Drule;

data Drule = DAssume Nat | DPremise Nat | DMP Deriv Deriv | DCP Nat Fm Deriv
  | DRAA Nat Fm Deriv | DDN Deriv | DBotI Deriv Deriv | DAndIntro Deriv Deriv
  | DOrElim Deriv Nat Fm Deriv Nat Fm Deriv | ... ;

data Route = Direct | ViaTree;

lemmonToFitch :: [Pline] -> Sum Translation_error (Route, [Fitch_item]);
lemmonToFitch p = (case lemmonToFitchDirect p of {
                    Inl _ -> viaTree p;
                    Inr f -> Inr (Direct, f);
                  });
```

`Sum` is the generator's name for `Either` and `Nat` its arbitrary-precision
naturals; `String.literal` comes out as `String`. The cap explicitly exports
the public checker and translation API; Isabelle adds all implementation
dependencies automatically. GHC is installed, and the generated module is
compiled by the differential harness. Natural-number and integer conversions
are public so that external callers can construct both proof representations.

## The design decision that carries the development

`ruleOK` takes the list of assumption formulas its side conditions range over as
a parameter:

```isabelle
fun ruleOK :: "lemmon_proof ⇒ fm ⇒ fm list ⇒ just ⇒ bool"
type_synonym asm_src = "lemmon_proof ⇒ nat ⇒ nat set ⇒ fm list"
definition lineOK_gen :: "asm_src ⇒ lemmon_proof ⇒ pline ⇒ bool"
```

Lemmon supplies the assumptions a line *rests on* (`depSrc`); Fitch, having no
record of those, supplies the assumptions *in scope* (`scopeSrc`). That single
substitution is the whole difference between the two systems' rule checks, and
it is Section 6.2 of the paper made into a definition: the Fitch checker is
literally the Lemmon checker with scope in place of dependency. Everything
downstream — Theorem 4, Theorem 22, the renaming repair — is a consequence of
the two sources' being ordered by `⊆` (Proposition 5) and the side conditions'
being antitone in them (`ruleOK_antitone`).

## Four things the formalisation found

**1. Theorem 4's "if and only if" holds in one direction only.**

The paper states that a Fitch proof `F` is correct iff `δ F` is. The ⟸
direction fails, and Theorem 22 is itself the counterexample:

```isabelle
theorem theorem_4_backward_fails:
  "¬ fitchCorrect thm22_fitch_bad ∧ lemmonCorrect (δ thm22_fitch_bad)" by eval

lemma theorem_22_delta: "δ thm22_fitch_bad = thm22_lemmon" by eval
```

so the failure is visible on the very pair of proofs the paper prints. This is
not an artefact: it is the phenomenon of Section 6.2. At universal introduction
the Fitch side condition speaks of scope where the Lemmon one speaks of
dependency; scope may properly include the dependency set; so Fitch licenses
strictly less, and a translation that forgets scope cannot reflect its
correctness. The surviving direction, `theorem_4_forward`, is proved in
`LF_Delta.thy`.

**2. Existential elimination has the same defect as universal introduction.**

Section 6.2 says that "universal introduction alone imposes a condition on the
assumptions". On the standard statement of existential elimination — the witness
must occur neither in the existential, nor in the conclusion, nor in any
assumption on which the conclusion depends other than the witness assumption —
that rule imposes one too, and the same failure follows for the same reason.
`LF_Examples.thy` gives a correct Lemmon proof, structurally parallel to the one
in Theorem 22, whose positional Fitch image is incorrect at an existential
elimination. The total repair must therefore cover existential elimination as
well as universal introduction. The construction in `LF_Unfold.thy` does so;
the extra case is
`exRepair`, and it is justified in the same way, by Lemma 23 and Corollary 24.

**3. Fitch well-formedness never says where the proof ends.**

Neither the paper's conditions nor `FitchTypes.fitchWellFormed` requires the
conclusion to stand at the outermost level, and nothing else implies it: an
empty subproof body satisfies the "a subproof ends in a line" condition
vacuously. So

```isabelle
openAssumptionFitch = [FSub (Subproof 1 P [])]
```

passed every check, had no premises, and had `P` as its conclusion --- making
the Fitch turnstile unsound, since any interpretation making `P` false refutes
`[] ⊢⇩F P`. The repair is one more conjunct, `concludesAtTop`;
`openAssumptionFitch_fails_only_root_scope` records by evaluation that the
witness satisfies every other condition, so the conjunct is not redundant.
With it in force `fitch_semantic_soundness` goes through, and it needs no new
model theory: `theorem_4_forward` carries the proof to Lemmon, `proposition_5`
bounds the conclusion's dependencies by the assumptions in scope at it, and
`concludesAtTop` makes that scope the premises alone.

**4. The paper's `lemmonToFitch` accepts a positional image without checking it.**

```haskell
lemmonToFitch prf = case lemmonToFitchDirect prf of
  Right fp -> Right (Direct, fp)
  ...
```

`lemmonToFitchDirect` returns `Right` when the obstructions are absent --- the
three of Section 4 and the four found here; their absence does not make the image correct. On the Lemmon proof
of Theorem 22 the obstructions are absent and the image is the incorrect Fitch
proof the paper displays. `lemmonToFitchChecked` asks the checker before taking
the shortcut.

## The two formal layers

The supplied Haskell roster is authoritative. `LF_HLW_Formula.thy`,
`LF_HLW.thy`, `LF_HLW_Fitch.thy`,
`LF_HLW_Semantics.thy`, `LF_HLW_DNF.thy`,
`LF_HLW_Translate.thy`, and `LF_HLW_Unfold.thy` reproduce its
logical kernel directly,
including Boolean constants, equality-as-predicate, `MT`, `LEM`, `PropTaut`,
`QN`, bidirectional double negation, conjunction-form reductio, detachment for
biconditional elimination, formula-first equality elimination, and
multi-quantifier rules. `hlCorrect` matches the program's observable checker;
`hlVerifiedCorrect` adds positive increasing source order and dependency
closure for theorem statements.

The exact layer is now connected end to end to the semantics.
`hlRuleOK_sound` proves that each of the twenty-one authoritative rule branches
preserves truth, including the reinterpretation arguments required by the two
eigenconstant rules. `hlVerifiedCorrect_line_sound` composes those local
results by well-founded induction over cited line numbers, and
`hlVerifiedCorrect_sound` proves that a verified proof's conclusion is true
whenever its open premises are true in a standard interpretation.

The shorter `fm`/`just` layer in `LF_Formula.thy` and `LF_Lemmon.thy` remains
as internal proof infrastructure for the already established translation and
semantic theorems. It is not presented as a rival specification. Both the
repaired direct Lemmon-to-Fitch map and the complete derivation-tree fallback
now operate on `HL_` values. `hlLemmonToFitchChecked` accepts the direct route
only when it verifies and otherwise unfolds. The exact fallback also corrects
the handwritten implementation's global `boxed` classification: an assumption
is a discharged leaf only when its discharger is an ancestor in the selected
derivation, so a dead sibling branch cannot erase an open premise.

`Reit` is not one of the twenty-one. Lemmon has no reiteration rule and needs
none (Proposition 18); it appears here so that δ is total on Fitch proofs that
use reiteration, and so that the unfolding can emit the reiteration Fitch
requires when a subproof's conclusion comes from outside it.

## Answers to the three questions

**The corrected compact unfolding is total.** `conjecture_26` in
`LF_Conjecture.thy` retains the draft's numbering but is an Isabelle theorem:
the compact construction, with repairs for both universal introduction and
existential elimination, yields, for every correct compact Lemmon
proof, a well-formed and correct Fitch proof with the same conclusion. The
revised paper states this as a theorem. Of the four supporting results, (L1) is
`unfolding_terminates` in `LF_Unfold.thy`, (L2) and (L3) are `L2_L3` in
`LF_WellFormed.thy`, and (L4) is `L4_derivation` in `LF_Check.thy`;
`toDerivation_sound` is in `LF_Faithful.thy`. `conjecture_26_sequent` states the
containment of one turnstile in the other, `Γ ⊢⇩L ψ ⟹ Γ ⊢⇩F ψ`. The corollary
`translation_total`, that `lemmonToFitchChecked` succeeds on every correct
Lemmon proof, follows.

**Permutation and duplication-free translation do not always suffice.** The
claims numbered 27 and 28 in the earlier draft are refuted in
`LF_Conjecture27.thy` by one five-line proof, which discharges two different
assumptions at the same line:

```
1     (1) P            A
2     (2) Q            A
1,2   (3) P ∧ Q        1,2 ∧I
2     (4) P → (P∧Q)    1,3 CP
1     (5) Q → (P∧Q)    2,3 CP
```

Fitch would need two subproofs both closing at line 3, so the outer one would
end in a subproof rather than a line (`subrefs_same_last`). This is a *third*
obstruction, beyond the two of Theorem 10, and unlike those it is invariant
under permutation. It also refutes a duplication-free image, even if arbitrary
auxiliary target lines are allowed (`conjecture_28_with_auxiliaries_false`).

**Laminar dependency regions do not suffice for a fixed positional image.** Example 12 has disjoint,
hence laminar, dependency regions (`ex12_dependency_laminar`) but has no Fitch
image (`theorem_10_ex12`). The combined negative theorem is
`dependency_laminar_not_sufficient` in `LF_Theorem10.thy`. This statement keeps
the source numbering fixed. It does not rule out repairing Example 12 by
permuting and renumbering its lines, as the original paper's Remark 13 does.

## What is not proved

* **Exact-layer emission correctness and total translator success remain to be proved.**
  In particular, the compact `L2_L3`, `L4`, and `translation_total` theorems
  do not apply to `hlDerivationToFitch`. Runtime validation ensures that the
  checked route returns only an accepted target; a theorem that every valid
  source obtains such a target requires the exact emitter and renaming proofs.
* The original Conjecture 26 specifies only universal-introduction repair.
  The proved compact theorem uses an extended construction which also repairs
  existential elimination. It is a corrected result, not the original wording
  proved verbatim.

Neither turnstile is among the remaining gaps. `lemmon_semantic_soundness` and
`fitch_semantic_soundness` (both in `LF_Semantics.thy`) prove every Lemmon and
every Fitch sequent model-valid, and `hlVerifiedCorrect_sound` is the
authoritative checker's end-to-end semantic soundness theorem.

* Whether the seven checks are *necessary* for `positionalImage`, as well as
  sufficient, is open — but every witness they were built from is now proved to
  have no image at all (`checks_reject_only_imageless_sources` in
  `LF_Theorem10.thy`, covering `ex11`, `ex12`, `c27`, `premLate`, `backCP` and
  `reused`). That is evidence, not a proof: six sources are not all sources. `LF_Positional.thy` establishes exact, duplicate-aware
  scope and subproof characterisations and `lemmonToFitchDirect_fitchWF`, so
  every accepted source yields a well-formed positional Fitch proof. The
  converse was refuted for the older `fitchWF`, by giving `premLate` an image
  that hid its late undischarged assumption in an unused one-line `FAssume`
  subproof --- but that image *ended inside* the unused subproof, and
  `concludesAtTop` now rejects it. `premLate_no_positional_image` shows the
  dodge cannot be repaired for that source, so no counterexample is currently
  known and the question is reopened.
* **Whether `hlCorrect` alone is sound is open.** `hlVerifiedCorrect_sound` is
  proved of `hlVerifiedCorrect` = `hlCorrect` + `hlDependencyClosed` +
  `hlCanonicalOrder`, and only `hlCorrect` is Halvorson's. Both added invariants
  are genuinely extra, each with an isolating witness in
  `LF_HLW_Examples.thy`: `hl_cp_misordered` fails only `hlCanonicalOrder`
  (audit finding 4 — `checkStructure` compares line *numbers*, not physical
  order); `hl_lem_free_dependency` fails only `hlDependencyClosed` (finding 5 —
  `HL_LEM` is the one branch of `hlRuleOK` that constrains nothing about the
  dependency set). Neither witness is unsound: both conclusions are tautologies.
  Reading the branches says why the obvious attacks fail — every branch but
  `HL_LEM` fixes `G` from the cited lines, `HL_LEM`'s formula is valid so a free
  `G` can only *enlarge* the reported premises and thereby weaken the sequent,
  and every subtraction discharges a line the checker separately requires to be
  an assumption. That is an argument, not a proof, and this project's record
  says arguments of that shape should be checked by construction.
* Conjecture 28 is also refuted when auxiliary Fitch lines are allowed.
  `sourceCovered` requires only that every source line be represented and places
  no restriction on additional target lines; `conjecture_28_with_auxiliaries_false`
  shows that the shared-discharge obstruction survives this weakening.

The exact-layer construction proof is required before claiming that the
original paper's full twenty-one-rule translation has been verified. Resolving
the theorem names in the revised paper and building without `sorry` are
necessary checks, but do not establish that correspondence by themselves.
