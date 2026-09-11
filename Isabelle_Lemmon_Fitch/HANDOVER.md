# Handover note

**Historical note superseded on 2026-09-09.** The current source-to-original
comparison is [ORIGINAL_PAPER_COMPARISON.md](ORIGINAL_PAPER_COMPARISON.md).
The actual original is [the Desktop PDF](/home/dusty/Desktop/lemmon-fitch.pdf);
the `reference/` paper already contains revisions and is not the original
baseline. Completion claims below must be read against the new matrix:
the compact corrected construction theorem does not establish the general
translation theorem for the exact HL rules. This turn also adds canonical
HL dependency reconstruction and repairs the strengthened Fitch checks.

Prepared 2026-09-08, for the author of `lemmon-fitch.tex`.

Two things need your attention: edits made to your draft, and an
overstatement in how the relationship between the Isabelle development and
your Haskell checker has been described.

---

## 1. Edits to your draft

`lemmon-fitch.tex` in the repository root has been edited; the copy under
`reference/lemmon-checker-main/paper/` was left as the supplied baseline, so
the two now differ. Six passages changed, in two groups.

### Corrections forced by a change to the formalisation

The draft cited `fitch_semantic_soundness_fails` and read the root-scope
boundary case as an open observation:

> "The result should be read constructively: the Fitch checker needs a
> closed-root condition if its turnstile is to take the premises of the outer
> level as the assumptions of the whole proof. Formalisation is valuable here
> precisely because it does not silently supply the intended convention."

That condition has since been supplied. `fitchWF` gained a conjunct,
`concludesAtTop`, requiring the last item of a proof to be a line at the
outermost level, and the Fitch turnstile is now proved semantically sound
(`fitch_semantic_soundness`). The cited theorem no longer exists, because the
definition beneath it changed and its statement became false.

**This is worth your judgement, not just your assent.** Your sentence made a
methodological point: that formalisation earns its keep by exposing a missing
convention rather than quietly supplying it. Supplying it is exactly what was
then done. The affected passages have been rewritten to say what was found,
what was added, that the addition is not redundant
(`openAssumptionFitch_fails_only_root_scope` shows the witness satisfies each
of the other six conditions and fails only the new one), and what follows. If
you would rather keep the unrepaired definition and the finding it supports,
the change is reversible: keep `fitchWF` as it was, and attach
`concludesAtTop` to a separate predicate, which is how the same omission is
handled in the authoritative layer (`hlFitchWellFormed` is left faithful to
your Haskell; `hlConcludesAtTop` is separate).

Passages changed for this reason: the introduction; the round-trip remark in
§3; the semantic-audit paragraph; the closing paragraph on the retract
formulation.

### Additions

Two results proved since the draft, added where the draft already discussed
the topic:

* All six witnesses behind the direct translation's checks are proved to have
  no well-formed positional Fitch image at all
  (`checks_reject_only_imageless_sources`). Stated as evidence for the
  converse of the sufficiency theorem, explicitly **not** a proof of it.
* Both invariants that `hlVerifiedCorrect` adds to your `hlCorrect` are
  genuinely extra, each with a witness accepted by yours and rejected by the
  strengthened one (`hl_cp_misordered`, `hl_lem_free_dependency`). Neither is
  unsound. Whether `hlCorrect` alone admits a semantically invalid proof is
  left open.

All 55 Isabelle identifiers the draft cites now resolve; the check is
mechanical and is recorded in `TODO.md` as the acceptance test.

---

## 2. What "reproduces your checker" does and does not mean

The draft is careful here — it says Isabelle is the environment for their
"formal reproduction" and that an application adapter is still needed. This
note is to make sure the surrounding conversation does not drift into a
stronger claim, because the stronger claim is false.

**What has been established.** The `HL_` datatypes are isomorphic to yours,
constructor for constructor: 21 justifications, 23 Fitch rules, 9 formula
constructors, matching names, arities and order. The rule decisions were
transliterated by reading `LemmonChecker.hs`. Sixteen defects in the source are
recorded in `HASKELL_AUDIT.md`, two of them soundness bugs rather than
omissions.

**Your kernel now builds here, unmodified.** GHC 9.4.7 was installed (your
`dist-newstyle` targeted 9.4.8, the same series). `ProofTypes`, `PrettyPrint`,
`ModelSemantics`, `LatexPretty`, `TruthTable` and `LemmonChecker` all compile
with no edits to anything under `Halvorson/`. The audit's earlier claim that
the package could not be rebuilt is superseded.

**The two checkers have been compared directly.** `differential/` runs both on
the same inputs and compares verdicts *per line*, through your public
`checkProof`/`LineReport` interface rather than through internals:

| | |
|---|---|
| line comparisons | 9,874 |
| of which rejections | 2,706 |
| verdict disagreements | **0** |
| rejection messages byte-identical | **860 / 860** |
| your `test/Tests.hs` against the generated kernel | passes (24 exact, 5 via tree route, 0 broken) |

Three phases: your 14 `eval` proofs that parse; twelve hand-written proofs
covering the eight rules your corpus never uses (`OrElim`, `EqIntro`, `EqElim`,
`LEM`, `PropTaut`, `IffIntro`, `IffElim`, `QN` — also the rules the audit
flagged); and 1,728 systematic mutants corrupting dependency sets, line
numbers, justifications and formulas. The mutants are the point: your corpus is
nearly all valid proofs, so a checker that answered "correct" to everything
would have passed a corpus-only test 86/86.

**Messages.** Isabelle decides *which* error and *with what data*
(`hlLineError` in `LF_HLW_Report.thy`); a renderer supplies the wording,
because Isabelle's string literals are ASCII — `Str_Literal.hs` raises above
code point 127 — and your messages use U+274C and the connectives. The
decision stays where the theorems are:

```isabelle
lemma hlRuleError_None: "hlRuleError P l = None ⟷ hlRuleOK P l"
theorem hlProofReport_valid:
  "list_all (λe. snd e = None) (hlProofReport P) ⟷ hlCorrect P"
```

`hlRuleOK` still makes every accept/reject decision; the diagnostic only
describes a failure it has already established. So the messages could not have
changed which proofs are accepted, by construction rather than by
re-verification — which is why the verdict count stayed at zero through six
rounds of message work.

Two of your defects are reproduced **deliberately**, because the text cannot
match otherwise: `renderFormula`'s `isBinary` counts `Predicate "="` at any
arity but omits `Iff`, and `Iff` prints an ASCII arrow among Unicode
connectives (finding 9).

**Two defects in the export, found only by compiling against it.** Neither is
visible by reading the generated file:

* It exported `Int`, `Nat`, `Set` and `Sum` **abstractly** — no constructors,
  no conversions — so no Haskell caller could construct an argument to any
  exported checker, nor inspect any translator result. The exported kernel was
  uncallable. This recurred four times as new types were added; every datatype
  must have its constructors named in `export_code`, and nothing warns you.
* `int` was emitted as binary numeral trees (`data Int = Zero_int | Pos Num |
  Neg Num`) rather than as an integer, because `Code_Target_Int` had not been
  imported alongside `Code_Target_Nat`.

Both are fixed at the Isabelle source, so they persist through regeneration.
Reading generated code and *using* it are not the same check.

**What remains impossible.** The Isabelle development cannot be *proved*
equivalent to your program: Haskell has no formal semantics here. The
strongest defensible claim is "transliterated from your source by hand, and
differentially tested to agree on 9,874 line comparisons and 860 messages,
spanning all twenty-one rules". It would be a mistake to describe it as more.
Nor can Isabelle emit your *file*: it has no mechanism for comments, `deriving`
clauses or your layout, and forcing the text to match would sever the output
from the proofs that make it worth generating.

One divergence is permanent and belongs in the paper rather than hidden. Your
line numbers are machine `Int` and wrap on overflow; the generated ones are
`Integer` and do not. Isabelle will not emit a wrapping integer, because that
would falsify the proofs about it. So near the machine word size the two
checkers *should* disagree, and the differential test does not reach that
range.

---

## 3. State of the development

Green build; no `sorry`, `oops`, `axiomatization` or `quick_and_dirty`. 29
theories, 745 lemmas/theorems/corollaries, 102 executable `by eval` checks.
Conjecture 26 proved, Theorem 10 in your own formulation, Conjectures 27 and 28
refuted including with auxiliary lines, Theorem 4's converse refuted, and both
turnstiles semantically sound.

`TODO.md` is a closed record, not a worklist: it states the completion criteria
and the questions deliberately left open, with reasons.

## 4. Decisions that are yours, not mine

1. **The closed-root repair.** §1 above. Your draft used the Fitch turnstile's
   unsoundness as a finding and said formalisation earns its keep by *not*
   silently supplying the missing convention. It has now been supplied. If you
   would rather keep the finding, the change is reversible — keep `fitchWF` as
   it was and attach `concludesAtTop` to a separate predicate, exactly as the
   authoritative layer does with `hlFitchWellFormed` and `hlConcludesAtTop`.

2. **Which checker the application should run.** `hlCorrect` is bug-compatible
   with yours: it reproduces the LEM dependency hole and the number-comparison
   in `checkStructure`, which is precisely why the 9,874 comparisons agree.
   `hlVerifiedCorrect` adds the two invariants your checker omits. It is not
   simply better — it is *stricter*, and one of its two conditions
   (`hlCanonicalOrder`) would reject a valid proof written in an unusual order.
   Dropping it in changes what your students' proofs do.

3. **`FitchConvert`.** Not swapped, and it cannot be a silent swap: our
   translator has four checks yours lacks (`PremiseLate`, `BoxReversed`,
   `AssumptionReused`, `SourceNotVerified`) — the gaps this project found — so
   it rejects sources yours accepts, with error codes your
   `renderTranslationError` has no case for. Extending your `TranslationError`
   with those four is a change to your public API.

4. **Whether `hlCorrect` alone is sound.** Open, and recorded as such in
   `TODO.md`. Both invariants `hlVerifiedCorrect` adds are genuinely extra,
   with isolating witnesses, and neither witness is unsound; the structural
   argument for why the obvious attacks fail is in
   `LF_HLW_Examples.thy`, stated as an argument rather than a proof.

## 5. Reproducing any of this

```bash
# Isabelle: build and regenerate the exported Haskell/SML
/home/dusty/Desktop/Isabelle/Isabelle2025-2/bin/isabelle build -d . -e Lemmon_Fitch

# the differential tests (needs: ghc libghc-aeson-dev libghc-split-dev)
ghc --make -O1 -igenerated/haskell -ireference/lemmon-checker-main/src \
    -idifferential -outputdir differential/build \
    -o differential/diff differential/Differential.hs && ./differential/diff

# your regression suite, against the generated kernel
ghc --make -O1 -idifferential/shim -igenerated/haskell \
    -ireference/lemmon-checker-main/src -idifferential \
    -outputdir differential/buildshim -o differential/shimtest \
    reference/lemmon-checker-main/test/Tests.hs && ./differential/shimtest
```

`differential/RESULT.txt` and `differential/RESULT.messages` hold the last
recorded runs. `differential/README.md` states what the tests do *not*
establish.
