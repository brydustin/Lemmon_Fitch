# Audit of `Halvorson/lemmon-checker-main`

This audit records the state found on 2026-08-28. The handwritten logical
kernel is authoritative for the intended *How Logic Works* checker. Isabelle
now reproduces its formula, Lemmon, and Fitch datatypes and its rule behavior
under `HL_`/`hl` names, while retaining a separately named compact layer used
by the established translation proofs.

## Scope inspected

The complete `src/` tree (eighteen modules), every `app/` executable, the test
suite, Cabal and Stack metadata, Dockerfile, paper/problem notes, prompts, and
the roles of the static and OCR/training assets were inspected. The Haskell
package could not be rebuilt on this machine because no `ghc`, `cabal`, or
`stack` executable is installed. Its `dist-newstyle` cache refers to Hans
Halvorson's former macOS GHC 9.4.8 path and contains no reusable binaries.

## Isabelle reproduction

`LF_Halvorson_Formula.thy` now has the exact Haskell-shaped `hl_term` and
`hl_formula` datatypes: genuine Boolean constants and equality represented by
the predicate name `"="`. `LF_Halvorson.thy` has the exact twenty-one
justification constructors and reproduces rule patterns, citation order,
multi-quantifier behavior, dependency equations, full-proof lookup, and the
Haskell `Int` line-number domain. `LF_Halvorson_Fitch.thy` mirrors every Fitch
constructor, including `FReit`, and defines the authoritative total map
`δ⇩H = hlFitchToLemmon`; reiteration maps to `HL_PropTaut [m]`.

`LF_Halvorson_Semantics.thy` supplies the corrected total evaluator, including
biconditionals and the equality-as-identity condition required by the equality
rules. It also proves `hlRuleOK_sound` for all twenty-one authoritative rule
branches, composes citations by well-founded induction in
`hlVerifiedCorrect_line_sound`, and proves the end-to-end theorem
`hlVerifiedCorrect_sound`: true open premises imply a true conclusion in every
standard interpretation. `LF_Halvorson_DNF.thy` supplies the propositional
NNF/DNF pipeline with the omitted biconditional cases repaired. Both are
public roots of the cap's generated module.

`LF_Halvorson_Translate.thy` implements the direct Lemmon-to-Fitch route on the
same exact datatypes. It adds the reversed-box, reused-assumption, late-premise,
subproof-scope, and eigenvariable-scope checks required by the formal audit,
proves that every successful result is positional, and has an executable
verified round-trip guard.

`LF_Halvorson_Unfold.thy` implements the source-shaped derivation datatype,
unfolding, renaming, premise layout, subproof emission, and complete route on
the same exact types. It repairs universal-introduction and
existential-elimination eigenconstants and classifies assumption leaves by
their actual ancestor dischargers. The shared-discharge regression forces the
fallback route and checks its Fitch proof and conclusion under `delta_H`.

The generated module is not yet a drop-in web-application replacement because
the application still imports its handwritten types and expects Aeson/parser
instances. That is now an interface-adapter problem, not an unresolved choice
of formal rule roster.

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
   conclusion.
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

Do not delete `Halvorson/lemmon-checker-main` until its interface code has been
copied into a maintained location. Isabelle will not generate the parser, JSON
codecs, OCR/transcription pipeline, LaTeX rendering, web routes, static pages,
or regression corpus.

The compatibility decision is settled: the supplied Haskell checker is the
intended specification. The remaining integration work is to adapt those
interfaces to the generated `HL_` types and rerun the Haskell corpus
against the generated checker. Until that adapter exists, a successful build
of the web application and a successful Isabelle export are separate facts.
