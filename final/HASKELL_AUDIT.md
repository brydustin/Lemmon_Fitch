# Audit of `reference/lemmon-checker-main`

This audit records the supplied-code findings of 2026-08-28, with
Isabelle integration corrections dated 2026-09-09. See
`ORIGINAL_PAPER_COMPARISON.md` for the original-paper completion audit. The handwritten logical
kernel is authoritative for the intended *How Logic Works* checker. Isabelle
now reproduces its formula, Lemmon, and Fitch datatypes and its rule behavior
under `HL_`/`hl` names, while retaining a separately named compact layer used
by the established translation proofs.

## Scope inspected

The complete `src/` tree (eighteen modules), every `app/` executable, the test
suite, Cabal and Stack metadata, Dockerfile, paper/problem notes, prompts, and
the roles of the static and OCR/training assets were inspected. The logical
kernel now builds here: `ghc`, `libghc-aeson-dev` and `libghc-split-dev` were
installed (GHC 9.4.7; his `dist-newstyle` targeted 9.4.8, the same series), and
`ProofTypes`, `PrettyPrint`, `ModelSemantics`, `LatexPretty`, `TruthTable` and
`LemmonChecker` compile **unmodified**. The `dist-newstyle` cache still refers
to Hans Halvorson's former macOS path and holds no reusable binaries. The web
executable and its dependencies were not built.

## Isabelle reproduction

`LF_HLW_Formula.thy` now has the exact Haskell-shaped `hl_term` and
`hl_formula` datatypes: genuine Boolean constants and equality represented by
the predicate name `"="`. `LF_HLW.thy` has the exact twenty-one
justification constructors and reproduces rule patterns, citation order,
multi-quantifier behavior, dependency equations, full-proof lookup, and the
Haskell `Int` line-number domain. `LF_HLW_Fitch.thy` mirrors every Fitch
constructor, including `FReit`, and defines the authoritative total map
`δ⇩H = hlFitchToLemmon`; reiteration maps to `HL_PropTaut [m]`. It keeps
`hlFitchWellFormed` bug-for-bug faithful to the Haskell and adds the missing
root-scope condition separately, as `hlConcludesAtTop`, so that the
correspondence tests and the verified predicates stay distinguishable.

`LF_HLW_Semantics.thy` supplies the corrected total evaluator, including
biconditionals and the equality-as-identity condition required by the equality
rules. It also proves `hlRuleOK_sound` for all twenty-one authoritative rule
branches, composes citations by well-founded induction in
`hlVerifiedCorrect_line_sound`, and proves the end-to-end theorem
`hlVerifiedCorrect_sound`: true open premises imply a true conclusion in every
standard interpretation. `LF_HLW_DNF.thy` supplies the propositional
NNF/DNF pipeline with the omitted biconditional cases repaired. Both are
public roots of the cap's generated module.

`LF_HLW_Translate.thy` implements the direct Lemmon-to-Fitch route on the
same exact datatypes. It adds the reversed-box, reused-assumption, late-premise,
subproof-scope, and eigenvariable-scope checks required by the formal audit,
proves that every successful result is positional, and has an executable
verified round-trip guard.

`LF_HLW_Unfold.thy` implements the source-shaped derivation datatype,
unfolding, renaming, premise layout, subproof emission, and a checked route on
the same exact types. It repairs universal-introduction and
existential-elimination eigenconstants and classifies assumption leaves by
their actual ancestor dischargers. The shared-discharge regression forces the
fallback route and checks its Fitch proof and conclusion under `delta_H`.
A candidate that fails target validation returns `HL_TargetNotVerified`;
clients matching every translation-error constructor must handle it.
General exact-layer emission correctness and all-source success are not yet
proved. The original-paper audit added genuine nested scope checks,
root-premise semantic soundness, and target validation with premise inclusion
and conclusion preservation. It also corrected outer-premise eigenconstant
scope and existential-elimination diagnostics. These strengthen verified
interfaces; `hlCorrect` and the legacy Haskell visibility checker stay faithful.

The generated module is not a drop-in replacement for the application: it
lacks the Aeson instances and the parser, and its entry point differs in type
(his `checkProof :: Proof -> ProofReport` reports per line; the generated
`hlCorrect :: [Hl_line] -> Bool` does not).

Two defects in the **export itself** were found by trying to compile against
it, and are fixed at the Isabelle source:

15. The generated module exported `Int`, `Nat` and `Set` abstractly, with no
    constructors and no conversion functions, so no Haskell caller could build
    an argument to any exported checker: the exported kernel was uncallable.
    `int_of_integer`, `integer_of_int` and `set` were exported first.
    The 2026-09-09 review found `Nat` still unusable for indices and fuel;
    `nat_of_integer` and `integer_of_nat` are now exported too.
16. `int` was emitted as `data Int = Zero_int | Pos Num | Neg Num` over binary
    numeral trees rather than as an integer, because `Code_Target_Int` was not
    imported while `Code_Target_Nat` was. It is now `newtype Int =
    Int_of_integer Integer`.

**Differential test.** `differential/` compares the generated checker with his,
per line, through his public API. On 9,874 comparisons --- his 14-proof corpus,
twelve hand-written proofs covering the eight rules his corpus never uses, and
1,728 systematic mutants, with 2,706 of the comparisons being rejections ---
there were **no verdict disagreements**, and **all 860 rejection messages
reproduce his text byte for byte**. His own `test/Tests.hs` also passes against
a shim that replaces `LemmonChecker` with the generated kernel.

The messages come from `hlLineError` (`LF_HLW_Report.thy`), which
Isabelle proves reports no error exactly when `hlLineOK` holds; `hlRuleOK`
still makes every accept/reject decision, so the diagnostics cannot alter which
proofs are accepted. The renderer reproduces finding 9's two `renderFormula`
defects deliberately, since the text cannot match otherwise.

That is testing, not proof; see `differential/README.md` for what it does not
establish.

## High-priority source findings

1. `ProofTypes.hs` omits `Boolean` cases from `varsInFormula`,
   `constsInFormula`, `freeFor`, `abstractConstFree`, `substFree`, `freeVars`,
   and Boolean equality in `equalUpToConstReplacement`. These are partial
   functions and can fail at runtime.
2. `ModelSemantics.eval` omits `Iff`. Model checking and the public truth-table
   endpoint can therefore fail on biconditionals.
3. `PropDNF` omits `Iff` from its propositional check and does not eliminate it
   before NNF/clause extraction.
4. `LemmonChecker.checkStructure` compares cited line numbers with the current
   number instead of checking physical proof order. A first line numbered 10
   can cite a later line numbered 5 and evade the intended acyclicity check.
5. `LemmonChecker` does not require an `LEM` line to have the empty dependency
   set.
6. `FitchConvert.lemmonToFitch` accepts a direct candidate without checking its
   Fitch rules. Direct eigenvariable checking covers universal introduction
   but not existential elimination; the tree repair has the same asymmetry.
7. `FitchTypes.fitchWellFormed` checks scope/citations but not rule correctness,
   eigenvariables, actual subproof-reference existence, or a root-level final
   conclusion. The last of these is a soundness bug, not just an omission: a
   proof consisting of one bare subproof has no premises and reports the
   subproof's assumption as its conclusion, so it "proves" an arbitrary formula
   from nothing. The witness is `hlOpenAssumptionFitch` in
   `LF_HLW_Fitch.thy`; `hlOpenAssumptionFitch_fails_only_root_scope`
   shows by evaluation that it passes every other condition, including the
   scope-based rule check. `hlFitchWellFormed` reproduces the defect faithfully
   and is left alone; the condition was added to `hlConcludesAtTop`, which
   `hlFitchVerified` and `hlFitchCorrect` now require. The same repair was made
   in the compact layer as the `concludesAtTop` conjunct of `fitchWF`, where it
   turned a refuted soundness claim into the proved
   `fitch_semantic_soundness`.
8. `PipeParse.parseRefs` silently discards malformed dependency tokens rather
   than reporting them. The formula normalizer also replaces every lowercase
   `v` with disjunction, including a legitimate term/name `v`.
9. `FormulaParser` cannot parse the truth constants that `PrettyPrint` and
   `PropDNF` emit. `PrettyPrint.isBinary` omits `Iff`, and it prints the
   biconditional as ASCII while the other connectives use Unicode.
10. `OcrLatexToPipe.dropSimpleCmd` does not construct the intended command
    pattern and runs after braces have already been stripped. Nonempty bracketed
    dependency cells are returned uncleaned.
11. `ProofToLaTeX` defines but never inserts its requested header row and emits
    the malformed disjunction-elimination string `"$\\∨ee$E"`.
12. `app/JsonToPipe.hs` does not handle `EqIntro`, `EqElim`, `PropTaut`,
    `IffIntro`, `IffElim`, or `QN` and is partial at runtime.
13. The paid Mathpix `/ocr` route has neither the size/rate limits nor the
    exception/redaction handling used by the paid Anthropic `/transcribe`
    route. The comment claiming only `/transcribe` spends money is false.
14. `FitchConvert.toDerivation` computes one global `boxed` set. If an
    assumption is discharged on a source line that is dead with respect to the
    selected conclusion, the tree still labels that assumption `DAssume`
    instead of `DPremise`. The shared-discharge proof then loses an open
    premise and `derivationToFitch` cites line `0`. Isabelle corrects this with
    `hlClassifyAssumptions`, whose bound set follows actual derivation ancestors.

`-Wall` is enabled for the library but warnings are not errors. Several
executables, including the web executable, do not enable `-Wall`; this allows
the partial matches and unused imports to survive a normal build.

## Preservation and integration decision

Do not delete `reference/lemmon-checker-main` until its interface code has been
copied into a maintained location. Isabelle will not generate the parser, JSON
codecs, OCR/transcription pipeline, LaTeX rendering, web routes, static pages,
or regression corpus.

The compatibility decision is settled: the supplied Haskell checker is the
intended specification. The remaining integration work is to adapt those
interfaces to the generated `HL_` types and rerun the Haskell corpus
against the generated checker. Until that adapter exists, a successful build
of the web application and a successful Isabelle export are separate facts.
