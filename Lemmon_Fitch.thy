(*  Title:      Lemmon_Fitch.thy

    Cap theory for the complete Lemmon/Fitch development.  Keep the imports
    explicit so that this file is also an inventory of the maintained theories.
*)

theory Lemmon_Fitch
  imports
    LF_Formula
    LF_Lemmon
    LF_Fitch
    LF_Delta
    LF_Direct
    LF_Derivation
    LF_Unfold
    LF_Render
    LF_Examples
    LF_WellFormed
    LF_Faithful
    LF_Check
    LF_Conjecture
    LF_Span
    LF_Positional
    LF_Semantics
    LF_HLW_Formula
    LF_HLW
    LF_HLW_Canonical
    LF_HLW_Fitch
    LF_HLW_Scope
    LF_HLW_Semantics
    LF_HLW_Fitch_Semantics
    LF_HLW_DNF
    LF_HLW_Translate
    LF_HLW_Unfold
    LF_HLW_Translation_Proofs
    LF_HLW_Derivation
    LF_HLW_Faithful
    LF_HLW_Renaming
    LF_HLW_Witnesses
    LF_HLW_Quantifier_Renaming
    LF_HLW_Derivation_Renaming
    LF_HLW_Rule_Transfer
    LF_HLW_Layout
    LF_HLW_Fuel
    LF_HLW_Conclusion
    LF_HLW_Premise_Layout
    LF_HLW_Nesting
    LF_HLW_Fresh
    LF_HLW_Erasure
    LF_HLW_Examples
    LF_HLW_Delta
    LF_HLW_Regression
    LF_HLW_Report
    LF_Conjecture27
    LF_Theorem10
begin

text \<open>This theory intentionally contains no new definitions or theorems.
  Successfully importing it certifies that the complete development can be
  loaded into one Isabelle theory context.\<close>

text \<open>Source-processing note: \<^file>\<open>LF_Lemmon.thy\<close>, lines
  218--229, defines @{const eqsub} with eleven recursive pattern equations.
  That particular \<open>fun eqsub\<close> command can take a while to compile when
  this cap is opened from the base HOL image.  A visible pause at
  \<open>LF_Lemmon.thy:218--229\<close> is expected; let Isabelle finish processing the
  command.

  On the current six-thread development machine, that command takes roughly
  2--3 minutes, and source-processing this entire cap (including the Haskell and
  SML exports below) takes roughly 5--7 minutes.  These are orientation figures,
  not time limits: processor load and Isabelle settings can make either stage
  slower.\<close>

section \<open>Executable export\<close>

text \<open>This cap is also the single code-generation entry point.  Opening
  this theory from the base @{session HOL} image source-processes every imported
  theory; the exports below are then available in Isabelle/jEdit under
  \<open>isabelle-export:\<close>.  Code-generation dependencies are included by Isabelle
  automatically, but the public roots are listed explicitly to make the intended
  generated API auditable.\<close>

text \<open>The public API includes the term/formula utilities, the rule-level
  checker, both rule maps, citation inspection, every one of the seven
  direct-translation diagnostics, the direct layout, the explicit tree
  fallback, the source-shaped exact checked route, and the predicates used to
  state positional and duplication-free images.\<close>

text \<open>The authoritative checker is also connected to its standard
  semantics.  @{thm hlRuleOK_sound} covers all twenty-one rule branches,
  @{thm hlVerifiedCorrect_line_sound} composes cited lines by well-founded
  induction, and @{thm hlVerifiedCorrect_sound} takes true open premises to a
  true conclusion.  These are logical theorems rather than executable
  constants, so they certify the generated checker without appearing as
  runtime functions in the export below.\<close>

export_code
  \<comment> \<open>Interoperation: the generated module exports \<open>int\<close> and \<open>set\<close>
    abstractly, so without these a caller cannot build an argument to any of
    the checkers below.  They are what lets a Haskell client construct the
    exact \<open>HL_\<close> datatypes.\<close>
  int_of_integer integer_of_int nat_of_integer integer_of_nat set Inl Inr
  hlLineError hlProofReport hlStructureError
  HL_DuplicateLine HL_LateCitation HL_RuleFailed
  HL_InvalidAssumption HL_MissingCited HL_RuleRejected hlRejectionReason
  HL_MPFirstNotConditional HL_MPSecondNotAntecedent HL_AndElimNotConjunction
  HL_OrIntroNotDisjunct HL_DNShape HL_MTFailed hlIsMT
  HL_EqElimNotEquality HL_AndIntroMismatch HL_MPNotConsequent
  HL_ForallIntroNotInstance HL_ForallIntroAbstraction HL_ForallElimNoConstants
  HL_ExistsIntroNotWitness HL_ExistsElimNotAssumption HL_ExistsElimNotRepeated
  HL_RAAFailed HL_OrElimFailed
  hlAnyCitationMissing hlRuleError

  \<comment> \<open>the object language and its executable operations\<close>
  Nm Vr Atom Eqf Bot Neg Conj Disj Impl Iff Uni Exi
  names_t names fvs_t fvs sentence inst_t inst rn_t rn eqsub_t eqsub
  instWitnesses instOK genOK witOK fresh_for fresh_for_fms

  \<comment> \<open>Definition 1: Lemmon lines, rules, dependency arithmetic and checker\<close>
  ProofLine
  Assumption MP CP RAA DN BotI AndIntro AndElimL AndElimR OrIntroL OrIntroR
  OrElim IffIntro IffElimL IffElimR ForallElim ForallIntro ExistsIntro
  ExistsElim EqIntro EqElim Reit
  citedLines dischargePairs lookupLine fmAt depsAt justAt depsOf depFms
  ruleOK lineOK_gen checkFrom_gen lemmon_21 lemmonCorrect conclusion openPremises

  \<comment> \<open>Definition 2: Fitch syntax, citations, scope and checker\<close>
  FLine FSub Subproof FL
  FPremise FAssume FMP FCP FRAA FDN FBotI FAndIntro FAndElimL FAndElimR
  FOrIntroL FOrIntroR FOrElim FIffIntro FIffElimL FIffElimR FForallElim
  FForallIntro FExistsIntro FExistsElim FEqIntro FEqElim FReit
  fCitedLines fCitedSubs toLemmonRule flatten scopeOf scopePath subrefs
  premiseLines fitchPremises fitchConclusion premisesFirst citationOK
  fitchWF fitchWellFormed

  \<comment> \<open>Section 3: \<delta> and Proposition 7\<close>
  \<delta> fitchToLemmon fitchCorrect stripDeps recompute

  \<comment> \<open>Section 4: direct translation and all seven diagnostics\<close>
  NotNested OutOfScope PremiseInBox PremiseLate BoxReversed AssumptionReused
  NotCorrect
  toFitchRule boxesOf boxPath boxOrderError boxHeadError nestingError
  premiseError scopeError subScopeError premiseOrderError buildItems
  lemmonToFitchDirect

  \<comment> \<open>Section 5: derivations, unfolding, repair and route selection\<close>
  Deriv DAssume DPremise DMP DCP DRAA DDN DBotI DAndIntro DAndElimL DAndElimR
  DOrIntroL DOrIntroR DOrElim DIffIntro DIffElimL DIffElimR DForallElim
  DForallIntro DExistsIntro DExistsElim DEqIntro DEqElim DReit
  Direct ViaTree openAsms derivOK rnD toDerivation derivationToFitch
  viaTree lemmonToFitch lemmonToFitchChecked

  \<comment> \<open>Definition 9 and the image predicates used for Conjectures 27 and 28\<close>
  ruleMatches lineMatches positionalImage fitchImage noDuplication sourceCovered
  renumberJust relabel permuteProof dependents

  \<comment> \<open>printing\<close>
  showFm showJust showLemmon showFitch showError showTranslation showNat

  \<comment> \<open>The authoritative How Logic Works checker interface from the supplied Haskell source\<close>
  HL_Var HL_Const HL_Predicate HL_Boolean HL_Not HL_And HL_Or HL_Implies
  HL_Iff HL_ForAll HL_Exists
  hlVariablesInTerm hlConstantsInTerm hlVariablesInFormula hlConstantsInFormula
  hlFreeVariables hlSubstituteTerm hlSubstituteFree hlFreeFor
  hlAbstractConstantFree hlAbstractMany hlEqualityFormula
  hlTermEqualUpToConstantReplacement hlEqualUpToConstantReplacement
  hlCollectForalls hlCollectExists hlPrefixForalls hlPrefixExists
  hlEliminationCount hlWitnessLists hlInferWitnessConstsK
  hlQuantifierNegationForms hlQuantifierNegationReachable
  hlQuantifierNegationEquivalent
  HL_ProofLine
  HL_Assumption HL_MP HL_MT HL_DN HL_CP HL_AndIntro HL_AndElim HL_OrIntro
  HL_OrElim HL_RAA HL_ForallElim HL_ExistsIntro HL_ForallIntro HL_ExistsElim
  HL_EqIntro HL_EqElim HL_LEM HL_PropTaut HL_IffIntro HL_IffElim HL_QN
  hlCitedLines hlDischargePairs hlLookupLine hlFormulaAt hlReferencesAt
  hlJustificationAt hlIsAssumptionLine hlReferenceUnion hlAssumptionConstants
  hlReferencedConstants hlPropositionalAtoms hlPropositionalValue
  hlPropositionalConsequence hlContradiction hlExcludedMiddle
  hlRuleOK hlStructureOK hlLineOK hlCorrect hlConclusion hlOpenPremises
  hlDependencyClosed hlCanonicalOrder hlVerifiedCorrect
  hlPaperCorrect hlCanonicalDependencies hlStripDependencies hlRecomputeDependencies

  \<comment> \<open>The authoritative Fitch syntax and the total map \<delta>\<close>
  HL_FPremise HL_FAssume HL_FMP HL_FMT HL_FDN HL_FCP HL_FAndI HL_FAndE
  HL_FOrI HL_FOrE HL_FRAA HL_FForallE HL_FForallI HL_FExistsI HL_FExistsE
  HL_FEqI HL_FEqE HL_FLEM HL_FPropTaut HL_FIffI HL_FIffE HL_FQN HL_FReit
  HL_FLine HL_FSub HL_Subproof
  hlSubAssumptionLine hlSubAssumptionFormula hlSubBody hlSubLastLine
  hlItemLastLine hlFitchLineNumbers hlFitchCitedLines hlToLemmonRule
  hlFlattenFitch hlDependencyLookup hlFitchDependenciesOf
  hlFitchToLemmonFrom hlFitchToLemmon hlFitchScopeFrom
  hlFitchWellFormed hlConcludesAtTop hlFitchNestedWellFormed
  hlFitchPremises hlFitchConclusion hlFitchPremiseClosed hlFitchVerified hlFitchCorrect

  \<comment> \<open>The finite ModelSemantics evaluator, truth-table core, and DNF utility\<close>
  HL_FiniteModel hlFiniteDomain hlFiniteConstants hlFinitePredicates
  hlSequenceOptions hlFiniteEvalTerm hlOptionAll hlOptionAny hlFiniteEval
  hlFiniteEvalClosed hlFiniteStandardEquality hlValuations
  hlIsPropositional hlEliminateImplications hlPushNegations hlToNNF
  hlDNFClauses hlLiteralFormula hlConjoin hlDisjoin hlClausesFormula hlToDNF

  \<comment> \<open>The repaired direct Lemmon-to-Fitch map on the exact HL_ datatypes\<close>
  HL_NotNested HL_OutOfScope HL_UnknownAssumption HL_MissingLine
  HL_EigenInScope HL_PremiseInBox HL_PremiseLate HL_BoxReversed
  HL_AssumptionReused HL_SourceNotVerified HL_TargetNotVerified
  hlToFitchRule hlBoxesOf hlDischargedAssumptions hlDischargerOf hlBoxPath
  hlBoxOrderError hlBoxHeadError hlOverlapping hlNestingError
  hlIsPremiseLine hlPremiseError hlPremiseOrderError hlIsPrefix
  hlFirstDifference hlBadCitations hlScopeError hlSubproofLevel
  hlBadSubproofCitations hlSubproofScopeError hlGeneralizedConstants
  hlEigenScopeAssumptions hlEigenScopeViolations hlEigenScopeError hlBuildFitchItems
  hlLemmonToFitchDirect

  \<comment> \<open>The exact derivation-tree fallback and complete checked route\<close>
  HL_Derivation
  HL_DAssume HL_DPremise HL_DMP HL_DMT HL_DDN HL_DCP HL_DAndI HL_DAndE
  HL_DOrI HL_DOrE HL_DRAA HL_DForallE HL_DForallI HL_DExistsI HL_DExistsE
  HL_DEqI HL_DEqE HL_DLEM HL_DPropTaut HL_DIffI HL_DIffE HL_DQN
  hlUnfoldDerivation hlClassifyAssumptions hlToDerivation hlRenameTerm hlRenameFormula
  hlRenameDerivation hlDerivationFormulas hlDerivationConstants hlFreshIndex
  hlRenamePairsFormula hlRepairDerivation hlForallRepairConstants
  hlExistsRepairConstants hlPremisesOf hlPremiseEnvironment
  hlEmitDerivation hlEmitDerivations hlDerivationToFitch
  HL_DirectRoute HL_ViaTreeRoute
  hlViaTree hlLemmonToFitch hlLemmonToFitchChecked

  in Haskell module_name LemmonFitch file_prefix haskell

text \<open>The same verified equations are exported to SML, which is the target
  used by @{method eval} for executable examples.\<close>

export_code
  lemmonCorrect ruleOK fitchCorrect fitchWF fitchWellFormed \<delta> fitchToLemmon
  boxOrderError boxHeadError nestingError premiseError scopeError subScopeError
  premiseOrderError lemmonToFitchDirect toDerivation derivationToFitch viaTree
  lemmonToFitch lemmonToFitchChecked recompute stripDeps
  ruleMatches lineMatches positionalImage fitchImage noDuplication sourceCovered
  renumberJust relabel permuteProof dependents
  showLemmon showFitch showError showTranslation
  hlRuleOK hlLineOK hlCorrect hlConclusion hlOpenPremises hlVerifiedCorrect
  hlPaperCorrect hlCanonicalDependencies hlStripDependencies hlRecomputeDependencies
  hlFitchToLemmon hlFitchWellFormed hlConcludesAtTop hlFitchNestedWellFormed
  hlFitchPremises hlFitchConclusion hlFitchPremiseClosed hlFitchVerified hlFitchCorrect
  hlFiniteEval hlFiniteEvalClosed hlFiniteStandardEquality
  hlIsPropositional hlToNNF hlToDNF
  hlLemmonToFitchDirect hlToDerivation hlDerivationToFitch
  hlViaTree hlLemmonToFitch hlLemmonToFitchChecked
  in SML module_name LemmonFitch file_prefix sml

end
