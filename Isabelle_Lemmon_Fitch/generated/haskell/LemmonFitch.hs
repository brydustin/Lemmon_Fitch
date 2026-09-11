{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  LemmonFitch(Int(..), integer_of_int, Nat, integer_of_nat, Trm(..), Fm(..),
               Justa(..), Num, Hl_term(..), Hl_justification(..),
               Hl_formula(..), Set(..), Char, Sum(..), Fitch_rule(..),
               Fline(..), Hl_line(..), Pline(..), Route(..), Subproof(..),
               Fitch_item(..), Deriv(..), Drule(..), Hl_route(..),
               Hl_fitch_rule(..), Hl_subproof(..), Hl_fitch_item(..),
               Translation_error(..), Hl_derivation(..), Hl_derivation_rule(..),
               Hl_check_error(..), Hl_finite_model(..),
               Hl_translation_error(..), rn_t, rn, names_t, names, openAsms,
               inst_t, inst, fvs_t, fvs, instWitnesses, rnD, lookupLine, fmAt,
               hlCitedLines, hlStructureOK, hlQuantifierNegationForms,
               hlQuantifierNegationReachable, hlQuantifierNegationEquivalent,
               hlTermEqualUpToConstantReplacement,
               hlEqualUpToConstantReplacement, hlConstantsInTerm,
               hlConstantsInFormula, hlSubstituteTerm, hlSubstituteFree,
               hlVariablesInTerm, hlFreeVariables, hlWitnessLists,
               hlInferWitnessConstsK, hlEliminationCount, hlPropositionalValue,
               hlPropositionalAtoms, hlValuations, hlPropositionalConsequence,
               hlEqualityFormula, hlCollectForalls, hlCollectExists,
               hlPrefixExists, hlAbstractConstantFree, hlAbstractMany,
               hlReferencedConstants, hlAssumptionConstants, hlLookupLine,
               hlReferencesAt, hlReferenceUnion, hlExcludedMiddle,
               hlContradiction, hlFormulaAt, hlRuleOK, hlLineOK, eqsub_t, eqsub,
               genOK, witOK, flatten, premisesFirst, fCitedLines, fCitedSubs,
               subrefs, citationOK, fitchWF, premiseLines, scopePath, scopeOf,
               hlCorrect, depFms, depsAt, citedLines, depsOf, instOK, justAt,
               ruleOK, showFm, toLemmonRule, delta, dischargePairs, boxesOf,
               boxPath, nat_of_integer, showNat, derivationToFitch, lineOK_gen,
               checkFrom_gen, lemmonCorrect, toDerivation, viaTree, recompute,
               stripDeps, hlIsPropositional, hlLiteralFormula, hlDisjoin,
               hlConjoin, hlClausesFormula, hlDNFClauses,
               hlEliminateImplications, hlPushNegations, hlToNNF, hlToDNF,
               showJust, sentence, hlConclusion, lemmon_21, showError,
               showFitch, toFitchRule, buildItems, scopeError, fresh_for,
               hlIsMT, conclusion, showLemmon, fitchCorrect, derivOK,
               hlOpenPremises, fitchToLemmon, boxHeadError, nestingError,
               premiseError, fitchPremises, hlSubBody, openPremises,
               renumberJust, relabel, boxOrderError, subScopeError,
               hlCanonicalOrder, hlDischargePairs, hlPremisesOf,
               hlPremiseEnvironment, hlDerivationFormulas,
               hlForallRepairConstants, hlExistsRepairConstants, hlRenameTerm,
               hlRenameFormula, hlRenamePairsFormula, hlRenameDerivation,
               hlFreshIndex, hlRepairDerivation, hlEmitDerivation,
               hlDerivationToFitch, hlClassifyAssumptions, hlBoxesOf,
               hlDischargedAssumptions, hlSequenceOptions, hlUnfoldDerivation,
               hlDependencyClosed, hlVerifiedCorrect, hlToDerivation,
               hlFitchCitedLines, hlFitchDependenciesOf, hlDependencyLookup,
               hlToLemmonRule, hlFitchToLemmonFrom, hlFlattenFitch,
               hlFitchToLemmon, hlFitchPremises, hlConcludesAtTop,
               hlFitchLineNumbers, hlSubLastLine, hlFitchNestedWellFormed,
               hlFitchPremiseClosed, hlFitchScopeFrom, hlFitchWellFormed,
               hlFitchVerified, hlFitchCorrect, hlViaTree, premiseOrderError,
               lemmonToFitchDirect, lemmonToFitch, fitchConclusion,
               fitchWellFormed, fresh_for_fms, hlJustificationAt, hlFreeFor,
               hlIsAssumptionLine, hlStructureError, hlAnyCitationMissing,
               hlRejectionReason, hlRuleError, hlLineError, showTranslation,
               dependents, ruleMatches, lineMatches, fitchImage, hlBoxPath,
               hlItemLastLine, hlProofReport, hlIsPrefix, permuteProof,
               hlOptionAll, hlOptionAny, noDuplication, sourceCovered,
               hlFinitePredicates, hlFiniteDomain, hlFiniteConstants,
               hlFiniteEvalTerm, hlFiniteEval, hlFirstDifference, hlToFitchRule,
               hlBadCitations, hlScopeError, hlSubproofLevel,
               hlBadSubproofCitations, hlSubproofScopeError, hlIsPremiseLine,
               hlPremiseOrderError, hlEigenScopeAssumptions,
               hlGeneralizedConstants, hlEigenScopeViolations,
               hlEigenScopeError, hlBuildFitchItems, hlBoxOrderError,
               hlPremiseError, hlDischargerOf, hlOverlapping, hlNestingError,
               hlBoxHeadError, hlLemmonToFitchDirect, hlLemmonToFitch,
               hlFitchConclusion, hlPrefixForalls, lemmonToFitchChecked,
               positionalImage, hlCanonicalDependencies, hlPaperCorrect,
               hlEmitDerivations, hlSubAssumptionLine, hlSubAssumptionFormula,
               hlVariablesInFormula, hlFiniteEvalClosed, hlDerivationConstants,
               hlStripDependencies, hlLemmonToFitchChecked,
               hlRecomputeDependencies, hlFiniteStandardEquality)
  where {

import Prelude ((==), (/=), (<), (<=), (>=), (>), (+), (-), (*), (/), (**),
  (>>=), (>>), (=<<), (&&), (||), (^), (^^), (.), ($), ($!), (++), (!!), Eq,
  error, id, return, not, fst, snd, map, filter, concat, concatMap, reverse,
  zip, null, takeWhile, dropWhile, all, any, Integer, negate, abs, divMod,
  String, Bool(True, False), Maybe(Nothing, Just));
import Data.Bits ((.&.), (.|.), (.^.));
import qualified Prelude;
import qualified Data.Bits;
import qualified Str_Literal;

newtype Int = Int_of_integer Integer;

integer_of_int :: Int -> Integer;
integer_of_int (Int_of_integer k) = k;

equal_int :: Int -> Int -> Bool;
equal_int k l = integer_of_int k == integer_of_int l;

instance Eq Int where {
  a == b = equal_int a b;
};

less_eq_int :: Int -> Int -> Bool;
less_eq_int k l = integer_of_int k <= integer_of_int l;

class Ord a where {
  less_eq :: a -> a -> Bool;
  less :: a -> a -> Bool;
};

less_int :: Int -> Int -> Bool;
less_int k l = integer_of_int k < integer_of_int l;

instance Ord Int where {
  less_eq = less_eq_int;
  less = less_int;
};

class (Ord a) => Preorder a where {
};

class (Preorder a) => Order a where {
};

instance Preorder Int where {
};

instance Order Int where {
};

class (Order a) => Linorder a where {
};

instance Linorder Int where {
};

newtype Nat = Nat Integer;

integer_of_nat :: Nat -> Integer;
integer_of_nat (Nat x) = x;

equal_nat :: Nat -> Nat -> Bool;
equal_nat m n = integer_of_nat m == integer_of_nat n;

instance Eq Nat where {
  a == b = equal_nat a b;
};

less_eq_nat :: Nat -> Nat -> Bool;
less_eq_nat m n = integer_of_nat m <= integer_of_nat n;

less_nat :: Nat -> Nat -> Bool;
less_nat m n = integer_of_nat m < integer_of_nat n;

instance Ord Nat where {
  less_eq = less_eq_nat;
  less = less_nat;
};

instance Preorder Nat where {
};

instance Order Nat where {
};

instance Linorder Nat where {
};

data Trm = Nm String | Vr String;

equal_trm :: Trm -> Trm -> Bool;
equal_trm (Nm x1) (Vr x2) = False;
equal_trm (Vr x2) (Nm x1) = False;
equal_trm (Vr x2) (Vr y2) = x2 == y2;
equal_trm (Nm x1) (Nm y1) = x1 == y1;

data Fm = Atom String [Trm] | Eqf Trm Trm | Bot | Neg Fm | Conj Fm Fm
  | Disj Fm Fm | Impl Fm Fm | Iff Fm Fm | Uni String Fm | Exi String Fm;

instance Eq Trm where {
  a == b = equal_trm a b;
};

equal_fm :: Fm -> Fm -> Bool;
equal_fm (Uni x91 x92) (Exi x101 x102) = False;
equal_fm (Exi x101 x102) (Uni x91 x92) = False;
equal_fm (Iff x81 x82) (Exi x101 x102) = False;
equal_fm (Exi x101 x102) (Iff x81 x82) = False;
equal_fm (Iff x81 x82) (Uni x91 x92) = False;
equal_fm (Uni x91 x92) (Iff x81 x82) = False;
equal_fm (Impl x71 x72) (Exi x101 x102) = False;
equal_fm (Exi x101 x102) (Impl x71 x72) = False;
equal_fm (Impl x71 x72) (Uni x91 x92) = False;
equal_fm (Uni x91 x92) (Impl x71 x72) = False;
equal_fm (Impl x71 x72) (Iff x81 x82) = False;
equal_fm (Iff x81 x82) (Impl x71 x72) = False;
equal_fm (Disj x61 x62) (Exi x101 x102) = False;
equal_fm (Exi x101 x102) (Disj x61 x62) = False;
equal_fm (Disj x61 x62) (Uni x91 x92) = False;
equal_fm (Uni x91 x92) (Disj x61 x62) = False;
equal_fm (Disj x61 x62) (Iff x81 x82) = False;
equal_fm (Iff x81 x82) (Disj x61 x62) = False;
equal_fm (Disj x61 x62) (Impl x71 x72) = False;
equal_fm (Impl x71 x72) (Disj x61 x62) = False;
equal_fm (Conj x51 x52) (Exi x101 x102) = False;
equal_fm (Exi x101 x102) (Conj x51 x52) = False;
equal_fm (Conj x51 x52) (Uni x91 x92) = False;
equal_fm (Uni x91 x92) (Conj x51 x52) = False;
equal_fm (Conj x51 x52) (Iff x81 x82) = False;
equal_fm (Iff x81 x82) (Conj x51 x52) = False;
equal_fm (Conj x51 x52) (Impl x71 x72) = False;
equal_fm (Impl x71 x72) (Conj x51 x52) = False;
equal_fm (Conj x51 x52) (Disj x61 x62) = False;
equal_fm (Disj x61 x62) (Conj x51 x52) = False;
equal_fm (Neg x4) (Exi x101 x102) = False;
equal_fm (Exi x101 x102) (Neg x4) = False;
equal_fm (Neg x4) (Uni x91 x92) = False;
equal_fm (Uni x91 x92) (Neg x4) = False;
equal_fm (Neg x4) (Iff x81 x82) = False;
equal_fm (Iff x81 x82) (Neg x4) = False;
equal_fm (Neg x4) (Impl x71 x72) = False;
equal_fm (Impl x71 x72) (Neg x4) = False;
equal_fm (Neg x4) (Disj x61 x62) = False;
equal_fm (Disj x61 x62) (Neg x4) = False;
equal_fm (Neg x4) (Conj x51 x52) = False;
equal_fm (Conj x51 x52) (Neg x4) = False;
equal_fm Bot (Exi x101 x102) = False;
equal_fm (Exi x101 x102) Bot = False;
equal_fm Bot (Uni x91 x92) = False;
equal_fm (Uni x91 x92) Bot = False;
equal_fm Bot (Iff x81 x82) = False;
equal_fm (Iff x81 x82) Bot = False;
equal_fm Bot (Impl x71 x72) = False;
equal_fm (Impl x71 x72) Bot = False;
equal_fm Bot (Disj x61 x62) = False;
equal_fm (Disj x61 x62) Bot = False;
equal_fm Bot (Conj x51 x52) = False;
equal_fm (Conj x51 x52) Bot = False;
equal_fm Bot (Neg x4) = False;
equal_fm (Neg x4) Bot = False;
equal_fm (Eqf x21 x22) (Exi x101 x102) = False;
equal_fm (Exi x101 x102) (Eqf x21 x22) = False;
equal_fm (Eqf x21 x22) (Uni x91 x92) = False;
equal_fm (Uni x91 x92) (Eqf x21 x22) = False;
equal_fm (Eqf x21 x22) (Iff x81 x82) = False;
equal_fm (Iff x81 x82) (Eqf x21 x22) = False;
equal_fm (Eqf x21 x22) (Impl x71 x72) = False;
equal_fm (Impl x71 x72) (Eqf x21 x22) = False;
equal_fm (Eqf x21 x22) (Disj x61 x62) = False;
equal_fm (Disj x61 x62) (Eqf x21 x22) = False;
equal_fm (Eqf x21 x22) (Conj x51 x52) = False;
equal_fm (Conj x51 x52) (Eqf x21 x22) = False;
equal_fm (Eqf x21 x22) (Neg x4) = False;
equal_fm (Neg x4) (Eqf x21 x22) = False;
equal_fm (Eqf x21 x22) Bot = False;
equal_fm Bot (Eqf x21 x22) = False;
equal_fm (Atom x11 x12) (Exi x101 x102) = False;
equal_fm (Exi x101 x102) (Atom x11 x12) = False;
equal_fm (Atom x11 x12) (Uni x91 x92) = False;
equal_fm (Uni x91 x92) (Atom x11 x12) = False;
equal_fm (Atom x11 x12) (Iff x81 x82) = False;
equal_fm (Iff x81 x82) (Atom x11 x12) = False;
equal_fm (Atom x11 x12) (Impl x71 x72) = False;
equal_fm (Impl x71 x72) (Atom x11 x12) = False;
equal_fm (Atom x11 x12) (Disj x61 x62) = False;
equal_fm (Disj x61 x62) (Atom x11 x12) = False;
equal_fm (Atom x11 x12) (Conj x51 x52) = False;
equal_fm (Conj x51 x52) (Atom x11 x12) = False;
equal_fm (Atom x11 x12) (Neg x4) = False;
equal_fm (Neg x4) (Atom x11 x12) = False;
equal_fm (Atom x11 x12) Bot = False;
equal_fm Bot (Atom x11 x12) = False;
equal_fm (Atom x11 x12) (Eqf x21 x22) = False;
equal_fm (Eqf x21 x22) (Atom x11 x12) = False;
equal_fm (Exi x101 x102) (Exi y101 y102) = x101 == y101 && equal_fm x102 y102;
equal_fm (Uni x91 x92) (Uni y91 y92) = x91 == y91 && equal_fm x92 y92;
equal_fm (Iff x81 x82) (Iff y81 y82) = equal_fm x81 y81 && equal_fm x82 y82;
equal_fm (Impl x71 x72) (Impl y71 y72) = equal_fm x71 y71 && equal_fm x72 y72;
equal_fm (Disj x61 x62) (Disj y61 y62) = equal_fm x61 y61 && equal_fm x62 y62;
equal_fm (Conj x51 x52) (Conj y51 y52) = equal_fm x51 y51 && equal_fm x52 y52;
equal_fm (Neg x4) (Neg y4) = equal_fm x4 y4;
equal_fm (Eqf x21 x22) (Eqf y21 y22) = equal_trm x21 y21 && equal_trm x22 y22;
equal_fm (Atom x11 x12) (Atom y11 y12) = x11 == y11 && x12 == y12;
equal_fm Bot Bot = True;

instance Eq Fm where {
  a == b = equal_fm a b;
};

data Justa = Assumption | MP Nat Nat | CP Nat Nat | RAA Nat Nat | DN Nat
  | BotI Nat Nat | AndIntro Nat Nat | AndElimL Nat | AndElimR Nat | OrIntroL Nat
  | OrIntroR Nat | OrElim Nat Nat Nat Nat Nat | IffIntro Nat Nat | IffElimL Nat
  | IffElimR Nat | ForallElim Nat | ForallIntro Nat | ExistsIntro Nat
  | ExistsElim Nat Nat Nat | EqIntro | EqElim Nat Nat | Reit Nat;

equal_just :: Justa -> Justa -> Bool;
equal_just (EqElim x211 x212) (Reit x22a) = False;
equal_just (Reit x22a) (EqElim x211 x212) = False;
equal_just EqIntro (Reit x22a) = False;
equal_just (Reit x22a) EqIntro = False;
equal_just EqIntro (EqElim x211 x212) = False;
equal_just (EqElim x211 x212) EqIntro = False;
equal_just (ExistsElim x191 x192 x193) (Reit x22a) = False;
equal_just (Reit x22a) (ExistsElim x191 x192 x193) = False;
equal_just (ExistsElim x191 x192 x193) (EqElim x211 x212) = False;
equal_just (EqElim x211 x212) (ExistsElim x191 x192 x193) = False;
equal_just (ExistsElim x191 x192 x193) EqIntro = False;
equal_just EqIntro (ExistsElim x191 x192 x193) = False;
equal_just (ExistsIntro x18) (Reit x22a) = False;
equal_just (Reit x22a) (ExistsIntro x18) = False;
equal_just (ExistsIntro x18) (EqElim x211 x212) = False;
equal_just (EqElim x211 x212) (ExistsIntro x18) = False;
equal_just (ExistsIntro x18) EqIntro = False;
equal_just EqIntro (ExistsIntro x18) = False;
equal_just (ExistsIntro x18) (ExistsElim x191 x192 x193) = False;
equal_just (ExistsElim x191 x192 x193) (ExistsIntro x18) = False;
equal_just (ForallIntro x17) (Reit x22a) = False;
equal_just (Reit x22a) (ForallIntro x17) = False;
equal_just (ForallIntro x17) (EqElim x211 x212) = False;
equal_just (EqElim x211 x212) (ForallIntro x17) = False;
equal_just (ForallIntro x17) EqIntro = False;
equal_just EqIntro (ForallIntro x17) = False;
equal_just (ForallIntro x17) (ExistsElim x191 x192 x193) = False;
equal_just (ExistsElim x191 x192 x193) (ForallIntro x17) = False;
equal_just (ForallIntro x17) (ExistsIntro x18) = False;
equal_just (ExistsIntro x18) (ForallIntro x17) = False;
equal_just (ForallElim x16) (Reit x22a) = False;
equal_just (Reit x22a) (ForallElim x16) = False;
equal_just (ForallElim x16) (EqElim x211 x212) = False;
equal_just (EqElim x211 x212) (ForallElim x16) = False;
equal_just (ForallElim x16) EqIntro = False;
equal_just EqIntro (ForallElim x16) = False;
equal_just (ForallElim x16) (ExistsElim x191 x192 x193) = False;
equal_just (ExistsElim x191 x192 x193) (ForallElim x16) = False;
equal_just (ForallElim x16) (ExistsIntro x18) = False;
equal_just (ExistsIntro x18) (ForallElim x16) = False;
equal_just (ForallElim x16) (ForallIntro x17) = False;
equal_just (ForallIntro x17) (ForallElim x16) = False;
equal_just (IffElimR x15) (Reit x22a) = False;
equal_just (Reit x22a) (IffElimR x15) = False;
equal_just (IffElimR x15) (EqElim x211 x212) = False;
equal_just (EqElim x211 x212) (IffElimR x15) = False;
equal_just (IffElimR x15) EqIntro = False;
equal_just EqIntro (IffElimR x15) = False;
equal_just (IffElimR x15) (ExistsElim x191 x192 x193) = False;
equal_just (ExistsElim x191 x192 x193) (IffElimR x15) = False;
equal_just (IffElimR x15) (ExistsIntro x18) = False;
equal_just (ExistsIntro x18) (IffElimR x15) = False;
equal_just (IffElimR x15) (ForallIntro x17) = False;
equal_just (ForallIntro x17) (IffElimR x15) = False;
equal_just (IffElimR x15) (ForallElim x16) = False;
equal_just (ForallElim x16) (IffElimR x15) = False;
equal_just (IffElimL x14) (Reit x22a) = False;
equal_just (Reit x22a) (IffElimL x14) = False;
equal_just (IffElimL x14) (EqElim x211 x212) = False;
equal_just (EqElim x211 x212) (IffElimL x14) = False;
equal_just (IffElimL x14) EqIntro = False;
equal_just EqIntro (IffElimL x14) = False;
equal_just (IffElimL x14) (ExistsElim x191 x192 x193) = False;
equal_just (ExistsElim x191 x192 x193) (IffElimL x14) = False;
equal_just (IffElimL x14) (ExistsIntro x18) = False;
equal_just (ExistsIntro x18) (IffElimL x14) = False;
equal_just (IffElimL x14) (ForallIntro x17) = False;
equal_just (ForallIntro x17) (IffElimL x14) = False;
equal_just (IffElimL x14) (ForallElim x16) = False;
equal_just (ForallElim x16) (IffElimL x14) = False;
equal_just (IffElimL x14) (IffElimR x15) = False;
equal_just (IffElimR x15) (IffElimL x14) = False;
equal_just (IffIntro x131 x132) (Reit x22a) = False;
equal_just (Reit x22a) (IffIntro x131 x132) = False;
equal_just (IffIntro x131 x132) (EqElim x211 x212) = False;
equal_just (EqElim x211 x212) (IffIntro x131 x132) = False;
equal_just (IffIntro x131 x132) EqIntro = False;
equal_just EqIntro (IffIntro x131 x132) = False;
equal_just (IffIntro x131 x132) (ExistsElim x191 x192 x193) = False;
equal_just (ExistsElim x191 x192 x193) (IffIntro x131 x132) = False;
equal_just (IffIntro x131 x132) (ExistsIntro x18) = False;
equal_just (ExistsIntro x18) (IffIntro x131 x132) = False;
equal_just (IffIntro x131 x132) (ForallIntro x17) = False;
equal_just (ForallIntro x17) (IffIntro x131 x132) = False;
equal_just (IffIntro x131 x132) (ForallElim x16) = False;
equal_just (ForallElim x16) (IffIntro x131 x132) = False;
equal_just (IffIntro x131 x132) (IffElimR x15) = False;
equal_just (IffElimR x15) (IffIntro x131 x132) = False;
equal_just (IffIntro x131 x132) (IffElimL x14) = False;
equal_just (IffElimL x14) (IffIntro x131 x132) = False;
equal_just (OrElim x121 x122 x123 x124 x125) (Reit x22a) = False;
equal_just (Reit x22a) (OrElim x121 x122 x123 x124 x125) = False;
equal_just (OrElim x121 x122 x123 x124 x125) (EqElim x211 x212) = False;
equal_just (EqElim x211 x212) (OrElim x121 x122 x123 x124 x125) = False;
equal_just (OrElim x121 x122 x123 x124 x125) EqIntro = False;
equal_just EqIntro (OrElim x121 x122 x123 x124 x125) = False;
equal_just (OrElim x121 x122 x123 x124 x125) (ExistsElim x191 x192 x193) =
  False;
equal_just (ExistsElim x191 x192 x193) (OrElim x121 x122 x123 x124 x125) =
  False;
equal_just (OrElim x121 x122 x123 x124 x125) (ExistsIntro x18) = False;
equal_just (ExistsIntro x18) (OrElim x121 x122 x123 x124 x125) = False;
equal_just (OrElim x121 x122 x123 x124 x125) (ForallIntro x17) = False;
equal_just (ForallIntro x17) (OrElim x121 x122 x123 x124 x125) = False;
equal_just (OrElim x121 x122 x123 x124 x125) (ForallElim x16) = False;
equal_just (ForallElim x16) (OrElim x121 x122 x123 x124 x125) = False;
equal_just (OrElim x121 x122 x123 x124 x125) (IffElimR x15) = False;
equal_just (IffElimR x15) (OrElim x121 x122 x123 x124 x125) = False;
equal_just (OrElim x121 x122 x123 x124 x125) (IffElimL x14) = False;
equal_just (IffElimL x14) (OrElim x121 x122 x123 x124 x125) = False;
equal_just (OrElim x121 x122 x123 x124 x125) (IffIntro x131 x132) = False;
equal_just (IffIntro x131 x132) (OrElim x121 x122 x123 x124 x125) = False;
equal_just (OrIntroR x11) (Reit x22a) = False;
equal_just (Reit x22a) (OrIntroR x11) = False;
equal_just (OrIntroR x11) (EqElim x211 x212) = False;
equal_just (EqElim x211 x212) (OrIntroR x11) = False;
equal_just (OrIntroR x11) EqIntro = False;
equal_just EqIntro (OrIntroR x11) = False;
equal_just (OrIntroR x11) (ExistsElim x191 x192 x193) = False;
equal_just (ExistsElim x191 x192 x193) (OrIntroR x11) = False;
equal_just (OrIntroR x11) (ExistsIntro x18) = False;
equal_just (ExistsIntro x18) (OrIntroR x11) = False;
equal_just (OrIntroR x11) (ForallIntro x17) = False;
equal_just (ForallIntro x17) (OrIntroR x11) = False;
equal_just (OrIntroR x11) (ForallElim x16) = False;
equal_just (ForallElim x16) (OrIntroR x11) = False;
equal_just (OrIntroR x11) (IffElimR x15) = False;
equal_just (IffElimR x15) (OrIntroR x11) = False;
equal_just (OrIntroR x11) (IffElimL x14) = False;
equal_just (IffElimL x14) (OrIntroR x11) = False;
equal_just (OrIntroR x11) (IffIntro x131 x132) = False;
equal_just (IffIntro x131 x132) (OrIntroR x11) = False;
equal_just (OrIntroR x11) (OrElim x121 x122 x123 x124 x125) = False;
equal_just (OrElim x121 x122 x123 x124 x125) (OrIntroR x11) = False;
equal_just (OrIntroL x10) (Reit x22a) = False;
equal_just (Reit x22a) (OrIntroL x10) = False;
equal_just (OrIntroL x10) (EqElim x211 x212) = False;
equal_just (EqElim x211 x212) (OrIntroL x10) = False;
equal_just (OrIntroL x10) EqIntro = False;
equal_just EqIntro (OrIntroL x10) = False;
equal_just (OrIntroL x10) (ExistsElim x191 x192 x193) = False;
equal_just (ExistsElim x191 x192 x193) (OrIntroL x10) = False;
equal_just (OrIntroL x10) (ExistsIntro x18) = False;
equal_just (ExistsIntro x18) (OrIntroL x10) = False;
equal_just (OrIntroL x10) (ForallIntro x17) = False;
equal_just (ForallIntro x17) (OrIntroL x10) = False;
equal_just (OrIntroL x10) (ForallElim x16) = False;
equal_just (ForallElim x16) (OrIntroL x10) = False;
equal_just (OrIntroL x10) (IffElimR x15) = False;
equal_just (IffElimR x15) (OrIntroL x10) = False;
equal_just (OrIntroL x10) (IffElimL x14) = False;
equal_just (IffElimL x14) (OrIntroL x10) = False;
equal_just (OrIntroL x10) (IffIntro x131 x132) = False;
equal_just (IffIntro x131 x132) (OrIntroL x10) = False;
equal_just (OrIntroL x10) (OrElim x121 x122 x123 x124 x125) = False;
equal_just (OrElim x121 x122 x123 x124 x125) (OrIntroL x10) = False;
equal_just (OrIntroL x10) (OrIntroR x11) = False;
equal_just (OrIntroR x11) (OrIntroL x10) = False;
equal_just (AndElimR x9) (Reit x22a) = False;
equal_just (Reit x22a) (AndElimR x9) = False;
equal_just (AndElimR x9) (EqElim x211 x212) = False;
equal_just (EqElim x211 x212) (AndElimR x9) = False;
equal_just (AndElimR x9) EqIntro = False;
equal_just EqIntro (AndElimR x9) = False;
equal_just (AndElimR x9) (ExistsElim x191 x192 x193) = False;
equal_just (ExistsElim x191 x192 x193) (AndElimR x9) = False;
equal_just (AndElimR x9) (ExistsIntro x18) = False;
equal_just (ExistsIntro x18) (AndElimR x9) = False;
equal_just (AndElimR x9) (ForallIntro x17) = False;
equal_just (ForallIntro x17) (AndElimR x9) = False;
equal_just (AndElimR x9) (ForallElim x16) = False;
equal_just (ForallElim x16) (AndElimR x9) = False;
equal_just (AndElimR x9) (IffElimR x15) = False;
equal_just (IffElimR x15) (AndElimR x9) = False;
equal_just (AndElimR x9) (IffElimL x14) = False;
equal_just (IffElimL x14) (AndElimR x9) = False;
equal_just (AndElimR x9) (IffIntro x131 x132) = False;
equal_just (IffIntro x131 x132) (AndElimR x9) = False;
equal_just (AndElimR x9) (OrElim x121 x122 x123 x124 x125) = False;
equal_just (OrElim x121 x122 x123 x124 x125) (AndElimR x9) = False;
equal_just (AndElimR x9) (OrIntroR x11) = False;
equal_just (OrIntroR x11) (AndElimR x9) = False;
equal_just (AndElimR x9) (OrIntroL x10) = False;
equal_just (OrIntroL x10) (AndElimR x9) = False;
equal_just (AndElimL x8) (Reit x22a) = False;
equal_just (Reit x22a) (AndElimL x8) = False;
equal_just (AndElimL x8) (EqElim x211 x212) = False;
equal_just (EqElim x211 x212) (AndElimL x8) = False;
equal_just (AndElimL x8) EqIntro = False;
equal_just EqIntro (AndElimL x8) = False;
equal_just (AndElimL x8) (ExistsElim x191 x192 x193) = False;
equal_just (ExistsElim x191 x192 x193) (AndElimL x8) = False;
equal_just (AndElimL x8) (ExistsIntro x18) = False;
equal_just (ExistsIntro x18) (AndElimL x8) = False;
equal_just (AndElimL x8) (ForallIntro x17) = False;
equal_just (ForallIntro x17) (AndElimL x8) = False;
equal_just (AndElimL x8) (ForallElim x16) = False;
equal_just (ForallElim x16) (AndElimL x8) = False;
equal_just (AndElimL x8) (IffElimR x15) = False;
equal_just (IffElimR x15) (AndElimL x8) = False;
equal_just (AndElimL x8) (IffElimL x14) = False;
equal_just (IffElimL x14) (AndElimL x8) = False;
equal_just (AndElimL x8) (IffIntro x131 x132) = False;
equal_just (IffIntro x131 x132) (AndElimL x8) = False;
equal_just (AndElimL x8) (OrElim x121 x122 x123 x124 x125) = False;
equal_just (OrElim x121 x122 x123 x124 x125) (AndElimL x8) = False;
equal_just (AndElimL x8) (OrIntroR x11) = False;
equal_just (OrIntroR x11) (AndElimL x8) = False;
equal_just (AndElimL x8) (OrIntroL x10) = False;
equal_just (OrIntroL x10) (AndElimL x8) = False;
equal_just (AndElimL x8) (AndElimR x9) = False;
equal_just (AndElimR x9) (AndElimL x8) = False;
equal_just (AndIntro x71 x72) (Reit x22a) = False;
equal_just (Reit x22a) (AndIntro x71 x72) = False;
equal_just (AndIntro x71 x72) (EqElim x211 x212) = False;
equal_just (EqElim x211 x212) (AndIntro x71 x72) = False;
equal_just (AndIntro x71 x72) EqIntro = False;
equal_just EqIntro (AndIntro x71 x72) = False;
equal_just (AndIntro x71 x72) (ExistsElim x191 x192 x193) = False;
equal_just (ExistsElim x191 x192 x193) (AndIntro x71 x72) = False;
equal_just (AndIntro x71 x72) (ExistsIntro x18) = False;
equal_just (ExistsIntro x18) (AndIntro x71 x72) = False;
equal_just (AndIntro x71 x72) (ForallIntro x17) = False;
equal_just (ForallIntro x17) (AndIntro x71 x72) = False;
equal_just (AndIntro x71 x72) (ForallElim x16) = False;
equal_just (ForallElim x16) (AndIntro x71 x72) = False;
equal_just (AndIntro x71 x72) (IffElimR x15) = False;
equal_just (IffElimR x15) (AndIntro x71 x72) = False;
equal_just (AndIntro x71 x72) (IffElimL x14) = False;
equal_just (IffElimL x14) (AndIntro x71 x72) = False;
equal_just (AndIntro x71 x72) (IffIntro x131 x132) = False;
equal_just (IffIntro x131 x132) (AndIntro x71 x72) = False;
equal_just (AndIntro x71 x72) (OrElim x121 x122 x123 x124 x125) = False;
equal_just (OrElim x121 x122 x123 x124 x125) (AndIntro x71 x72) = False;
equal_just (AndIntro x71 x72) (OrIntroR x11) = False;
equal_just (OrIntroR x11) (AndIntro x71 x72) = False;
equal_just (AndIntro x71 x72) (OrIntroL x10) = False;
equal_just (OrIntroL x10) (AndIntro x71 x72) = False;
equal_just (AndIntro x71 x72) (AndElimR x9) = False;
equal_just (AndElimR x9) (AndIntro x71 x72) = False;
equal_just (AndIntro x71 x72) (AndElimL x8) = False;
equal_just (AndElimL x8) (AndIntro x71 x72) = False;
equal_just (BotI x61 x62) (Reit x22a) = False;
equal_just (Reit x22a) (BotI x61 x62) = False;
equal_just (BotI x61 x62) (EqElim x211 x212) = False;
equal_just (EqElim x211 x212) (BotI x61 x62) = False;
equal_just (BotI x61 x62) EqIntro = False;
equal_just EqIntro (BotI x61 x62) = False;
equal_just (BotI x61 x62) (ExistsElim x191 x192 x193) = False;
equal_just (ExistsElim x191 x192 x193) (BotI x61 x62) = False;
equal_just (BotI x61 x62) (ExistsIntro x18) = False;
equal_just (ExistsIntro x18) (BotI x61 x62) = False;
equal_just (BotI x61 x62) (ForallIntro x17) = False;
equal_just (ForallIntro x17) (BotI x61 x62) = False;
equal_just (BotI x61 x62) (ForallElim x16) = False;
equal_just (ForallElim x16) (BotI x61 x62) = False;
equal_just (BotI x61 x62) (IffElimR x15) = False;
equal_just (IffElimR x15) (BotI x61 x62) = False;
equal_just (BotI x61 x62) (IffElimL x14) = False;
equal_just (IffElimL x14) (BotI x61 x62) = False;
equal_just (BotI x61 x62) (IffIntro x131 x132) = False;
equal_just (IffIntro x131 x132) (BotI x61 x62) = False;
equal_just (BotI x61 x62) (OrElim x121 x122 x123 x124 x125) = False;
equal_just (OrElim x121 x122 x123 x124 x125) (BotI x61 x62) = False;
equal_just (BotI x61 x62) (OrIntroR x11) = False;
equal_just (OrIntroR x11) (BotI x61 x62) = False;
equal_just (BotI x61 x62) (OrIntroL x10) = False;
equal_just (OrIntroL x10) (BotI x61 x62) = False;
equal_just (BotI x61 x62) (AndElimR x9) = False;
equal_just (AndElimR x9) (BotI x61 x62) = False;
equal_just (BotI x61 x62) (AndElimL x8) = False;
equal_just (AndElimL x8) (BotI x61 x62) = False;
equal_just (BotI x61 x62) (AndIntro x71 x72) = False;
equal_just (AndIntro x71 x72) (BotI x61 x62) = False;
equal_just (DN x5) (Reit x22a) = False;
equal_just (Reit x22a) (DN x5) = False;
equal_just (DN x5) (EqElim x211 x212) = False;
equal_just (EqElim x211 x212) (DN x5) = False;
equal_just (DN x5) EqIntro = False;
equal_just EqIntro (DN x5) = False;
equal_just (DN x5) (ExistsElim x191 x192 x193) = False;
equal_just (ExistsElim x191 x192 x193) (DN x5) = False;
equal_just (DN x5) (ExistsIntro x18) = False;
equal_just (ExistsIntro x18) (DN x5) = False;
equal_just (DN x5) (ForallIntro x17) = False;
equal_just (ForallIntro x17) (DN x5) = False;
equal_just (DN x5) (ForallElim x16) = False;
equal_just (ForallElim x16) (DN x5) = False;
equal_just (DN x5) (IffElimR x15) = False;
equal_just (IffElimR x15) (DN x5) = False;
equal_just (DN x5) (IffElimL x14) = False;
equal_just (IffElimL x14) (DN x5) = False;
equal_just (DN x5) (IffIntro x131 x132) = False;
equal_just (IffIntro x131 x132) (DN x5) = False;
equal_just (DN x5) (OrElim x121 x122 x123 x124 x125) = False;
equal_just (OrElim x121 x122 x123 x124 x125) (DN x5) = False;
equal_just (DN x5) (OrIntroR x11) = False;
equal_just (OrIntroR x11) (DN x5) = False;
equal_just (DN x5) (OrIntroL x10) = False;
equal_just (OrIntroL x10) (DN x5) = False;
equal_just (DN x5) (AndElimR x9) = False;
equal_just (AndElimR x9) (DN x5) = False;
equal_just (DN x5) (AndElimL x8) = False;
equal_just (AndElimL x8) (DN x5) = False;
equal_just (DN x5) (AndIntro x71 x72) = False;
equal_just (AndIntro x71 x72) (DN x5) = False;
equal_just (DN x5) (BotI x61 x62) = False;
equal_just (BotI x61 x62) (DN x5) = False;
equal_just (RAA x41 x42) (Reit x22a) = False;
equal_just (Reit x22a) (RAA x41 x42) = False;
equal_just (RAA x41 x42) (EqElim x211 x212) = False;
equal_just (EqElim x211 x212) (RAA x41 x42) = False;
equal_just (RAA x41 x42) EqIntro = False;
equal_just EqIntro (RAA x41 x42) = False;
equal_just (RAA x41 x42) (ExistsElim x191 x192 x193) = False;
equal_just (ExistsElim x191 x192 x193) (RAA x41 x42) = False;
equal_just (RAA x41 x42) (ExistsIntro x18) = False;
equal_just (ExistsIntro x18) (RAA x41 x42) = False;
equal_just (RAA x41 x42) (ForallIntro x17) = False;
equal_just (ForallIntro x17) (RAA x41 x42) = False;
equal_just (RAA x41 x42) (ForallElim x16) = False;
equal_just (ForallElim x16) (RAA x41 x42) = False;
equal_just (RAA x41 x42) (IffElimR x15) = False;
equal_just (IffElimR x15) (RAA x41 x42) = False;
equal_just (RAA x41 x42) (IffElimL x14) = False;
equal_just (IffElimL x14) (RAA x41 x42) = False;
equal_just (RAA x41 x42) (IffIntro x131 x132) = False;
equal_just (IffIntro x131 x132) (RAA x41 x42) = False;
equal_just (RAA x41 x42) (OrElim x121 x122 x123 x124 x125) = False;
equal_just (OrElim x121 x122 x123 x124 x125) (RAA x41 x42) = False;
equal_just (RAA x41 x42) (OrIntroR x11) = False;
equal_just (OrIntroR x11) (RAA x41 x42) = False;
equal_just (RAA x41 x42) (OrIntroL x10) = False;
equal_just (OrIntroL x10) (RAA x41 x42) = False;
equal_just (RAA x41 x42) (AndElimR x9) = False;
equal_just (AndElimR x9) (RAA x41 x42) = False;
equal_just (RAA x41 x42) (AndElimL x8) = False;
equal_just (AndElimL x8) (RAA x41 x42) = False;
equal_just (RAA x41 x42) (AndIntro x71 x72) = False;
equal_just (AndIntro x71 x72) (RAA x41 x42) = False;
equal_just (RAA x41 x42) (BotI x61 x62) = False;
equal_just (BotI x61 x62) (RAA x41 x42) = False;
equal_just (RAA x41 x42) (DN x5) = False;
equal_just (DN x5) (RAA x41 x42) = False;
equal_just (CP x31 x32) (Reit x22a) = False;
equal_just (Reit x22a) (CP x31 x32) = False;
equal_just (CP x31 x32) (EqElim x211 x212) = False;
equal_just (EqElim x211 x212) (CP x31 x32) = False;
equal_just (CP x31 x32) EqIntro = False;
equal_just EqIntro (CP x31 x32) = False;
equal_just (CP x31 x32) (ExistsElim x191 x192 x193) = False;
equal_just (ExistsElim x191 x192 x193) (CP x31 x32) = False;
equal_just (CP x31 x32) (ExistsIntro x18) = False;
equal_just (ExistsIntro x18) (CP x31 x32) = False;
equal_just (CP x31 x32) (ForallIntro x17) = False;
equal_just (ForallIntro x17) (CP x31 x32) = False;
equal_just (CP x31 x32) (ForallElim x16) = False;
equal_just (ForallElim x16) (CP x31 x32) = False;
equal_just (CP x31 x32) (IffElimR x15) = False;
equal_just (IffElimR x15) (CP x31 x32) = False;
equal_just (CP x31 x32) (IffElimL x14) = False;
equal_just (IffElimL x14) (CP x31 x32) = False;
equal_just (CP x31 x32) (IffIntro x131 x132) = False;
equal_just (IffIntro x131 x132) (CP x31 x32) = False;
equal_just (CP x31 x32) (OrElim x121 x122 x123 x124 x125) = False;
equal_just (OrElim x121 x122 x123 x124 x125) (CP x31 x32) = False;
equal_just (CP x31 x32) (OrIntroR x11) = False;
equal_just (OrIntroR x11) (CP x31 x32) = False;
equal_just (CP x31 x32) (OrIntroL x10) = False;
equal_just (OrIntroL x10) (CP x31 x32) = False;
equal_just (CP x31 x32) (AndElimR x9) = False;
equal_just (AndElimR x9) (CP x31 x32) = False;
equal_just (CP x31 x32) (AndElimL x8) = False;
equal_just (AndElimL x8) (CP x31 x32) = False;
equal_just (CP x31 x32) (AndIntro x71 x72) = False;
equal_just (AndIntro x71 x72) (CP x31 x32) = False;
equal_just (CP x31 x32) (BotI x61 x62) = False;
equal_just (BotI x61 x62) (CP x31 x32) = False;
equal_just (CP x31 x32) (DN x5) = False;
equal_just (DN x5) (CP x31 x32) = False;
equal_just (CP x31 x32) (RAA x41 x42) = False;
equal_just (RAA x41 x42) (CP x31 x32) = False;
equal_just (MP x21 x22) (Reit x22a) = False;
equal_just (Reit x22a) (MP x21 x22) = False;
equal_just (MP x21 x22) (EqElim x211 x212) = False;
equal_just (EqElim x211 x212) (MP x21 x22) = False;
equal_just (MP x21 x22) EqIntro = False;
equal_just EqIntro (MP x21 x22) = False;
equal_just (MP x21 x22) (ExistsElim x191 x192 x193) = False;
equal_just (ExistsElim x191 x192 x193) (MP x21 x22) = False;
equal_just (MP x21 x22) (ExistsIntro x18) = False;
equal_just (ExistsIntro x18) (MP x21 x22) = False;
equal_just (MP x21 x22) (ForallIntro x17) = False;
equal_just (ForallIntro x17) (MP x21 x22) = False;
equal_just (MP x21 x22) (ForallElim x16) = False;
equal_just (ForallElim x16) (MP x21 x22) = False;
equal_just (MP x21 x22) (IffElimR x15) = False;
equal_just (IffElimR x15) (MP x21 x22) = False;
equal_just (MP x21 x22) (IffElimL x14) = False;
equal_just (IffElimL x14) (MP x21 x22) = False;
equal_just (MP x21 x22) (IffIntro x131 x132) = False;
equal_just (IffIntro x131 x132) (MP x21 x22) = False;
equal_just (MP x21 x22) (OrElim x121 x122 x123 x124 x125) = False;
equal_just (OrElim x121 x122 x123 x124 x125) (MP x21 x22) = False;
equal_just (MP x21 x22) (OrIntroR x11) = False;
equal_just (OrIntroR x11) (MP x21 x22) = False;
equal_just (MP x21 x22) (OrIntroL x10) = False;
equal_just (OrIntroL x10) (MP x21 x22) = False;
equal_just (MP x21 x22) (AndElimR x9) = False;
equal_just (AndElimR x9) (MP x21 x22) = False;
equal_just (MP x21 x22) (AndElimL x8) = False;
equal_just (AndElimL x8) (MP x21 x22) = False;
equal_just (MP x21 x22) (AndIntro x71 x72) = False;
equal_just (AndIntro x71 x72) (MP x21 x22) = False;
equal_just (MP x21 x22) (BotI x61 x62) = False;
equal_just (BotI x61 x62) (MP x21 x22) = False;
equal_just (MP x21 x22) (DN x5) = False;
equal_just (DN x5) (MP x21 x22) = False;
equal_just (MP x21 x22) (RAA x41 x42) = False;
equal_just (RAA x41 x42) (MP x21 x22) = False;
equal_just (MP x21 x22) (CP x31 x32) = False;
equal_just (CP x31 x32) (MP x21 x22) = False;
equal_just Assumption (Reit x22a) = False;
equal_just (Reit x22a) Assumption = False;
equal_just Assumption (EqElim x211 x212) = False;
equal_just (EqElim x211 x212) Assumption = False;
equal_just Assumption EqIntro = False;
equal_just EqIntro Assumption = False;
equal_just Assumption (ExistsElim x191 x192 x193) = False;
equal_just (ExistsElim x191 x192 x193) Assumption = False;
equal_just Assumption (ExistsIntro x18) = False;
equal_just (ExistsIntro x18) Assumption = False;
equal_just Assumption (ForallIntro x17) = False;
equal_just (ForallIntro x17) Assumption = False;
equal_just Assumption (ForallElim x16) = False;
equal_just (ForallElim x16) Assumption = False;
equal_just Assumption (IffElimR x15) = False;
equal_just (IffElimR x15) Assumption = False;
equal_just Assumption (IffElimL x14) = False;
equal_just (IffElimL x14) Assumption = False;
equal_just Assumption (IffIntro x131 x132) = False;
equal_just (IffIntro x131 x132) Assumption = False;
equal_just Assumption (OrElim x121 x122 x123 x124 x125) = False;
equal_just (OrElim x121 x122 x123 x124 x125) Assumption = False;
equal_just Assumption (OrIntroR x11) = False;
equal_just (OrIntroR x11) Assumption = False;
equal_just Assumption (OrIntroL x10) = False;
equal_just (OrIntroL x10) Assumption = False;
equal_just Assumption (AndElimR x9) = False;
equal_just (AndElimR x9) Assumption = False;
equal_just Assumption (AndElimL x8) = False;
equal_just (AndElimL x8) Assumption = False;
equal_just Assumption (AndIntro x71 x72) = False;
equal_just (AndIntro x71 x72) Assumption = False;
equal_just Assumption (BotI x61 x62) = False;
equal_just (BotI x61 x62) Assumption = False;
equal_just Assumption (DN x5) = False;
equal_just (DN x5) Assumption = False;
equal_just Assumption (RAA x41 x42) = False;
equal_just (RAA x41 x42) Assumption = False;
equal_just Assumption (CP x31 x32) = False;
equal_just (CP x31 x32) Assumption = False;
equal_just Assumption (MP x21 x22) = False;
equal_just (MP x21 x22) Assumption = False;
equal_just (Reit x22a) (Reit y22a) = equal_nat x22a y22a;
equal_just (EqElim x211 x212) (EqElim y211 y212) =
  equal_nat x211 y211 && equal_nat x212 y212;
equal_just (ExistsElim x191 x192 x193) (ExistsElim y191 y192 y193) =
  equal_nat x191 y191 && equal_nat x192 y192 && equal_nat x193 y193;
equal_just (ExistsIntro x18) (ExistsIntro y18) = equal_nat x18 y18;
equal_just (ForallIntro x17) (ForallIntro y17) = equal_nat x17 y17;
equal_just (ForallElim x16) (ForallElim y16) = equal_nat x16 y16;
equal_just (IffElimR x15) (IffElimR y15) = equal_nat x15 y15;
equal_just (IffElimL x14) (IffElimL y14) = equal_nat x14 y14;
equal_just (IffIntro x131 x132) (IffIntro y131 y132) =
  equal_nat x131 y131 && equal_nat x132 y132;
equal_just (OrElim x121 x122 x123 x124 x125) (OrElim y121 y122 y123 y124 y125) =
  equal_nat x121 y121 &&
    equal_nat x122 y122 &&
      equal_nat x123 y123 && equal_nat x124 y124 && equal_nat x125 y125;
equal_just (OrIntroR x11) (OrIntroR y11) = equal_nat x11 y11;
equal_just (OrIntroL x10) (OrIntroL y10) = equal_nat x10 y10;
equal_just (AndElimR x9) (AndElimR y9) = equal_nat x9 y9;
equal_just (AndElimL x8) (AndElimL y8) = equal_nat x8 y8;
equal_just (AndIntro x71 x72) (AndIntro y71 y72) =
  equal_nat x71 y71 && equal_nat x72 y72;
equal_just (BotI x61 x62) (BotI y61 y62) =
  equal_nat x61 y61 && equal_nat x62 y62;
equal_just (DN x5) (DN y5) = equal_nat x5 y5;
equal_just (RAA x41 x42) (RAA y41 y42) = equal_nat x41 y41 && equal_nat x42 y42;
equal_just (CP x31 x32) (CP y31 y32) = equal_nat x31 y31 && equal_nat x32 y32;
equal_just (MP x21 x22) (MP y21 y22) = equal_nat x21 y21 && equal_nat x22 y22;
equal_just EqIntro EqIntro = True;
equal_just Assumption Assumption = True;

instance Eq Justa where {
  a == b = equal_just a b;
};

instance Ord String where {
  less_eq = (\ a b -> a <= b);
  less = (\ a b -> a < b);
};

instance Preorder String where {
};

instance Order String where {
};

instance Linorder String where {
};

data Num = One | Bit0 Num | Bit1 Num;

one_integer :: Integer;
one_integer = (1 :: Integer);

class One a where {
  one :: a;
};

instance One Integer where {
  one = one_integer;
};

class Zero a where {
  zero :: a;
};

instance Zero Integer where {
  zero = (0 :: Integer);
};

instance Ord Integer where {
  less_eq = (\ a b -> a <= b);
  less = (\ a b -> a < b);
};

class (One a, Zero a) => Zero_neq_one a where {
};

instance Zero_neq_one Integer where {
};

data Hl_term = HL_Var String | HL_Const String;

equal_hl_term :: Hl_term -> Hl_term -> Bool;
equal_hl_term (HL_Var x1) (HL_Const x2) = False;
equal_hl_term (HL_Const x2) (HL_Var x1) = False;
equal_hl_term (HL_Const x2) (HL_Const y2) = x2 == y2;
equal_hl_term (HL_Var x1) (HL_Var y1) = x1 == y1;

instance Eq Hl_term where {
  a == b = equal_hl_term a b;
};

data Hl_justification = HL_Assumption | HL_MP Int Int | HL_MT Int Int
  | HL_DN Int | HL_CP Int Int | HL_AndIntro Int Int | HL_AndElim Int
  | HL_OrIntro Int | HL_OrElim Int Int Int Int Int | HL_RAA Int Int
  | HL_ForallElim Int | HL_ExistsIntro Int | HL_ForallIntro Int
  | HL_ExistsElim Int Int Int | HL_EqIntro | HL_EqElim Int Int | HL_LEM
  | HL_PropTaut [Int] | HL_IffIntro Int Int | HL_IffElim Int Int | HL_QN Int;

equal_hl_justification :: Hl_justification -> Hl_justification -> Bool;
equal_hl_justification (HL_IffElim x201 x202) (HL_QN x21a) = False;
equal_hl_justification (HL_QN x21a) (HL_IffElim x201 x202) = False;
equal_hl_justification (HL_IffIntro x191 x192) (HL_QN x21a) = False;
equal_hl_justification (HL_QN x21a) (HL_IffIntro x191 x192) = False;
equal_hl_justification (HL_IffIntro x191 x192) (HL_IffElim x201 x202) = False;
equal_hl_justification (HL_IffElim x201 x202) (HL_IffIntro x191 x192) = False;
equal_hl_justification (HL_PropTaut x18) (HL_QN x21a) = False;
equal_hl_justification (HL_QN x21a) (HL_PropTaut x18) = False;
equal_hl_justification (HL_PropTaut x18) (HL_IffElim x201 x202) = False;
equal_hl_justification (HL_IffElim x201 x202) (HL_PropTaut x18) = False;
equal_hl_justification (HL_PropTaut x18) (HL_IffIntro x191 x192) = False;
equal_hl_justification (HL_IffIntro x191 x192) (HL_PropTaut x18) = False;
equal_hl_justification HL_LEM (HL_QN x21a) = False;
equal_hl_justification (HL_QN x21a) HL_LEM = False;
equal_hl_justification HL_LEM (HL_IffElim x201 x202) = False;
equal_hl_justification (HL_IffElim x201 x202) HL_LEM = False;
equal_hl_justification HL_LEM (HL_IffIntro x191 x192) = False;
equal_hl_justification (HL_IffIntro x191 x192) HL_LEM = False;
equal_hl_justification HL_LEM (HL_PropTaut x18) = False;
equal_hl_justification (HL_PropTaut x18) HL_LEM = False;
equal_hl_justification (HL_EqElim x161 x162) (HL_QN x21a) = False;
equal_hl_justification (HL_QN x21a) (HL_EqElim x161 x162) = False;
equal_hl_justification (HL_EqElim x161 x162) (HL_IffElim x201 x202) = False;
equal_hl_justification (HL_IffElim x201 x202) (HL_EqElim x161 x162) = False;
equal_hl_justification (HL_EqElim x161 x162) (HL_IffIntro x191 x192) = False;
equal_hl_justification (HL_IffIntro x191 x192) (HL_EqElim x161 x162) = False;
equal_hl_justification (HL_EqElim x161 x162) (HL_PropTaut x18) = False;
equal_hl_justification (HL_PropTaut x18) (HL_EqElim x161 x162) = False;
equal_hl_justification (HL_EqElim x161 x162) HL_LEM = False;
equal_hl_justification HL_LEM (HL_EqElim x161 x162) = False;
equal_hl_justification HL_EqIntro (HL_QN x21a) = False;
equal_hl_justification (HL_QN x21a) HL_EqIntro = False;
equal_hl_justification HL_EqIntro (HL_IffElim x201 x202) = False;
equal_hl_justification (HL_IffElim x201 x202) HL_EqIntro = False;
equal_hl_justification HL_EqIntro (HL_IffIntro x191 x192) = False;
equal_hl_justification (HL_IffIntro x191 x192) HL_EqIntro = False;
equal_hl_justification HL_EqIntro (HL_PropTaut x18) = False;
equal_hl_justification (HL_PropTaut x18) HL_EqIntro = False;
equal_hl_justification HL_EqIntro HL_LEM = False;
equal_hl_justification HL_LEM HL_EqIntro = False;
equal_hl_justification HL_EqIntro (HL_EqElim x161 x162) = False;
equal_hl_justification (HL_EqElim x161 x162) HL_EqIntro = False;
equal_hl_justification (HL_ExistsElim x141 x142 x143) (HL_QN x21a) = False;
equal_hl_justification (HL_QN x21a) (HL_ExistsElim x141 x142 x143) = False;
equal_hl_justification (HL_ExistsElim x141 x142 x143) (HL_IffElim x201 x202) =
  False;
equal_hl_justification (HL_IffElim x201 x202) (HL_ExistsElim x141 x142 x143) =
  False;
equal_hl_justification (HL_ExistsElim x141 x142 x143) (HL_IffIntro x191 x192) =
  False;
equal_hl_justification (HL_IffIntro x191 x192) (HL_ExistsElim x141 x142 x143) =
  False;
equal_hl_justification (HL_ExistsElim x141 x142 x143) (HL_PropTaut x18) = False;
equal_hl_justification (HL_PropTaut x18) (HL_ExistsElim x141 x142 x143) = False;
equal_hl_justification (HL_ExistsElim x141 x142 x143) HL_LEM = False;
equal_hl_justification HL_LEM (HL_ExistsElim x141 x142 x143) = False;
equal_hl_justification (HL_ExistsElim x141 x142 x143) (HL_EqElim x161 x162) =
  False;
equal_hl_justification (HL_EqElim x161 x162) (HL_ExistsElim x141 x142 x143) =
  False;
equal_hl_justification (HL_ExistsElim x141 x142 x143) HL_EqIntro = False;
equal_hl_justification HL_EqIntro (HL_ExistsElim x141 x142 x143) = False;
equal_hl_justification (HL_ForallIntro x13) (HL_QN x21a) = False;
equal_hl_justification (HL_QN x21a) (HL_ForallIntro x13) = False;
equal_hl_justification (HL_ForallIntro x13) (HL_IffElim x201 x202) = False;
equal_hl_justification (HL_IffElim x201 x202) (HL_ForallIntro x13) = False;
equal_hl_justification (HL_ForallIntro x13) (HL_IffIntro x191 x192) = False;
equal_hl_justification (HL_IffIntro x191 x192) (HL_ForallIntro x13) = False;
equal_hl_justification (HL_ForallIntro x13) (HL_PropTaut x18) = False;
equal_hl_justification (HL_PropTaut x18) (HL_ForallIntro x13) = False;
equal_hl_justification (HL_ForallIntro x13) HL_LEM = False;
equal_hl_justification HL_LEM (HL_ForallIntro x13) = False;
equal_hl_justification (HL_ForallIntro x13) (HL_EqElim x161 x162) = False;
equal_hl_justification (HL_EqElim x161 x162) (HL_ForallIntro x13) = False;
equal_hl_justification (HL_ForallIntro x13) HL_EqIntro = False;
equal_hl_justification HL_EqIntro (HL_ForallIntro x13) = False;
equal_hl_justification (HL_ForallIntro x13) (HL_ExistsElim x141 x142 x143) =
  False;
equal_hl_justification (HL_ExistsElim x141 x142 x143) (HL_ForallIntro x13) =
  False;
equal_hl_justification (HL_ExistsIntro x12) (HL_QN x21a) = False;
equal_hl_justification (HL_QN x21a) (HL_ExistsIntro x12) = False;
equal_hl_justification (HL_ExistsIntro x12) (HL_IffElim x201 x202) = False;
equal_hl_justification (HL_IffElim x201 x202) (HL_ExistsIntro x12) = False;
equal_hl_justification (HL_ExistsIntro x12) (HL_IffIntro x191 x192) = False;
equal_hl_justification (HL_IffIntro x191 x192) (HL_ExistsIntro x12) = False;
equal_hl_justification (HL_ExistsIntro x12) (HL_PropTaut x18) = False;
equal_hl_justification (HL_PropTaut x18) (HL_ExistsIntro x12) = False;
equal_hl_justification (HL_ExistsIntro x12) HL_LEM = False;
equal_hl_justification HL_LEM (HL_ExistsIntro x12) = False;
equal_hl_justification (HL_ExistsIntro x12) (HL_EqElim x161 x162) = False;
equal_hl_justification (HL_EqElim x161 x162) (HL_ExistsIntro x12) = False;
equal_hl_justification (HL_ExistsIntro x12) HL_EqIntro = False;
equal_hl_justification HL_EqIntro (HL_ExistsIntro x12) = False;
equal_hl_justification (HL_ExistsIntro x12) (HL_ExistsElim x141 x142 x143) =
  False;
equal_hl_justification (HL_ExistsElim x141 x142 x143) (HL_ExistsIntro x12) =
  False;
equal_hl_justification (HL_ExistsIntro x12) (HL_ForallIntro x13) = False;
equal_hl_justification (HL_ForallIntro x13) (HL_ExistsIntro x12) = False;
equal_hl_justification (HL_ForallElim x11) (HL_QN x21a) = False;
equal_hl_justification (HL_QN x21a) (HL_ForallElim x11) = False;
equal_hl_justification (HL_ForallElim x11) (HL_IffElim x201 x202) = False;
equal_hl_justification (HL_IffElim x201 x202) (HL_ForallElim x11) = False;
equal_hl_justification (HL_ForallElim x11) (HL_IffIntro x191 x192) = False;
equal_hl_justification (HL_IffIntro x191 x192) (HL_ForallElim x11) = False;
equal_hl_justification (HL_ForallElim x11) (HL_PropTaut x18) = False;
equal_hl_justification (HL_PropTaut x18) (HL_ForallElim x11) = False;
equal_hl_justification (HL_ForallElim x11) HL_LEM = False;
equal_hl_justification HL_LEM (HL_ForallElim x11) = False;
equal_hl_justification (HL_ForallElim x11) (HL_EqElim x161 x162) = False;
equal_hl_justification (HL_EqElim x161 x162) (HL_ForallElim x11) = False;
equal_hl_justification (HL_ForallElim x11) HL_EqIntro = False;
equal_hl_justification HL_EqIntro (HL_ForallElim x11) = False;
equal_hl_justification (HL_ForallElim x11) (HL_ExistsElim x141 x142 x143) =
  False;
equal_hl_justification (HL_ExistsElim x141 x142 x143) (HL_ForallElim x11) =
  False;
equal_hl_justification (HL_ForallElim x11) (HL_ForallIntro x13) = False;
equal_hl_justification (HL_ForallIntro x13) (HL_ForallElim x11) = False;
equal_hl_justification (HL_ForallElim x11) (HL_ExistsIntro x12) = False;
equal_hl_justification (HL_ExistsIntro x12) (HL_ForallElim x11) = False;
equal_hl_justification (HL_RAA x101 x102) (HL_QN x21a) = False;
equal_hl_justification (HL_QN x21a) (HL_RAA x101 x102) = False;
equal_hl_justification (HL_RAA x101 x102) (HL_IffElim x201 x202) = False;
equal_hl_justification (HL_IffElim x201 x202) (HL_RAA x101 x102) = False;
equal_hl_justification (HL_RAA x101 x102) (HL_IffIntro x191 x192) = False;
equal_hl_justification (HL_IffIntro x191 x192) (HL_RAA x101 x102) = False;
equal_hl_justification (HL_RAA x101 x102) (HL_PropTaut x18) = False;
equal_hl_justification (HL_PropTaut x18) (HL_RAA x101 x102) = False;
equal_hl_justification (HL_RAA x101 x102) HL_LEM = False;
equal_hl_justification HL_LEM (HL_RAA x101 x102) = False;
equal_hl_justification (HL_RAA x101 x102) (HL_EqElim x161 x162) = False;
equal_hl_justification (HL_EqElim x161 x162) (HL_RAA x101 x102) = False;
equal_hl_justification (HL_RAA x101 x102) HL_EqIntro = False;
equal_hl_justification HL_EqIntro (HL_RAA x101 x102) = False;
equal_hl_justification (HL_RAA x101 x102) (HL_ExistsElim x141 x142 x143) =
  False;
equal_hl_justification (HL_ExistsElim x141 x142 x143) (HL_RAA x101 x102) =
  False;
equal_hl_justification (HL_RAA x101 x102) (HL_ForallIntro x13) = False;
equal_hl_justification (HL_ForallIntro x13) (HL_RAA x101 x102) = False;
equal_hl_justification (HL_RAA x101 x102) (HL_ExistsIntro x12) = False;
equal_hl_justification (HL_ExistsIntro x12) (HL_RAA x101 x102) = False;
equal_hl_justification (HL_RAA x101 x102) (HL_ForallElim x11) = False;
equal_hl_justification (HL_ForallElim x11) (HL_RAA x101 x102) = False;
equal_hl_justification (HL_OrElim x91 x92 x93 x94 x95) (HL_QN x21a) = False;
equal_hl_justification (HL_QN x21a) (HL_OrElim x91 x92 x93 x94 x95) = False;
equal_hl_justification (HL_OrElim x91 x92 x93 x94 x95) (HL_IffElim x201 x202) =
  False;
equal_hl_justification (HL_IffElim x201 x202) (HL_OrElim x91 x92 x93 x94 x95) =
  False;
equal_hl_justification (HL_OrElim x91 x92 x93 x94 x95) (HL_IffIntro x191 x192) =
  False;
equal_hl_justification (HL_IffIntro x191 x192) (HL_OrElim x91 x92 x93 x94 x95) =
  False;
equal_hl_justification (HL_OrElim x91 x92 x93 x94 x95) (HL_PropTaut x18) =
  False;
equal_hl_justification (HL_PropTaut x18) (HL_OrElim x91 x92 x93 x94 x95) =
  False;
equal_hl_justification (HL_OrElim x91 x92 x93 x94 x95) HL_LEM = False;
equal_hl_justification HL_LEM (HL_OrElim x91 x92 x93 x94 x95) = False;
equal_hl_justification (HL_OrElim x91 x92 x93 x94 x95) (HL_EqElim x161 x162) =
  False;
equal_hl_justification (HL_EqElim x161 x162) (HL_OrElim x91 x92 x93 x94 x95) =
  False;
equal_hl_justification (HL_OrElim x91 x92 x93 x94 x95) HL_EqIntro = False;
equal_hl_justification HL_EqIntro (HL_OrElim x91 x92 x93 x94 x95) = False;
equal_hl_justification (HL_OrElim x91 x92 x93 x94 x95)
  (HL_ExistsElim x141 x142 x143) = False;
equal_hl_justification (HL_ExistsElim x141 x142 x143)
  (HL_OrElim x91 x92 x93 x94 x95) = False;
equal_hl_justification (HL_OrElim x91 x92 x93 x94 x95) (HL_ForallIntro x13) =
  False;
equal_hl_justification (HL_ForallIntro x13) (HL_OrElim x91 x92 x93 x94 x95) =
  False;
equal_hl_justification (HL_OrElim x91 x92 x93 x94 x95) (HL_ExistsIntro x12) =
  False;
equal_hl_justification (HL_ExistsIntro x12) (HL_OrElim x91 x92 x93 x94 x95) =
  False;
equal_hl_justification (HL_OrElim x91 x92 x93 x94 x95) (HL_ForallElim x11) =
  False;
equal_hl_justification (HL_ForallElim x11) (HL_OrElim x91 x92 x93 x94 x95) =
  False;
equal_hl_justification (HL_OrElim x91 x92 x93 x94 x95) (HL_RAA x101 x102) =
  False;
equal_hl_justification (HL_RAA x101 x102) (HL_OrElim x91 x92 x93 x94 x95) =
  False;
equal_hl_justification (HL_OrIntro x8) (HL_QN x21a) = False;
equal_hl_justification (HL_QN x21a) (HL_OrIntro x8) = False;
equal_hl_justification (HL_OrIntro x8) (HL_IffElim x201 x202) = False;
equal_hl_justification (HL_IffElim x201 x202) (HL_OrIntro x8) = False;
equal_hl_justification (HL_OrIntro x8) (HL_IffIntro x191 x192) = False;
equal_hl_justification (HL_IffIntro x191 x192) (HL_OrIntro x8) = False;
equal_hl_justification (HL_OrIntro x8) (HL_PropTaut x18) = False;
equal_hl_justification (HL_PropTaut x18) (HL_OrIntro x8) = False;
equal_hl_justification (HL_OrIntro x8) HL_LEM = False;
equal_hl_justification HL_LEM (HL_OrIntro x8) = False;
equal_hl_justification (HL_OrIntro x8) (HL_EqElim x161 x162) = False;
equal_hl_justification (HL_EqElim x161 x162) (HL_OrIntro x8) = False;
equal_hl_justification (HL_OrIntro x8) HL_EqIntro = False;
equal_hl_justification HL_EqIntro (HL_OrIntro x8) = False;
equal_hl_justification (HL_OrIntro x8) (HL_ExistsElim x141 x142 x143) = False;
equal_hl_justification (HL_ExistsElim x141 x142 x143) (HL_OrIntro x8) = False;
equal_hl_justification (HL_OrIntro x8) (HL_ForallIntro x13) = False;
equal_hl_justification (HL_ForallIntro x13) (HL_OrIntro x8) = False;
equal_hl_justification (HL_OrIntro x8) (HL_ExistsIntro x12) = False;
equal_hl_justification (HL_ExistsIntro x12) (HL_OrIntro x8) = False;
equal_hl_justification (HL_OrIntro x8) (HL_ForallElim x11) = False;
equal_hl_justification (HL_ForallElim x11) (HL_OrIntro x8) = False;
equal_hl_justification (HL_OrIntro x8) (HL_RAA x101 x102) = False;
equal_hl_justification (HL_RAA x101 x102) (HL_OrIntro x8) = False;
equal_hl_justification (HL_OrIntro x8) (HL_OrElim x91 x92 x93 x94 x95) = False;
equal_hl_justification (HL_OrElim x91 x92 x93 x94 x95) (HL_OrIntro x8) = False;
equal_hl_justification (HL_AndElim x7) (HL_QN x21a) = False;
equal_hl_justification (HL_QN x21a) (HL_AndElim x7) = False;
equal_hl_justification (HL_AndElim x7) (HL_IffElim x201 x202) = False;
equal_hl_justification (HL_IffElim x201 x202) (HL_AndElim x7) = False;
equal_hl_justification (HL_AndElim x7) (HL_IffIntro x191 x192) = False;
equal_hl_justification (HL_IffIntro x191 x192) (HL_AndElim x7) = False;
equal_hl_justification (HL_AndElim x7) (HL_PropTaut x18) = False;
equal_hl_justification (HL_PropTaut x18) (HL_AndElim x7) = False;
equal_hl_justification (HL_AndElim x7) HL_LEM = False;
equal_hl_justification HL_LEM (HL_AndElim x7) = False;
equal_hl_justification (HL_AndElim x7) (HL_EqElim x161 x162) = False;
equal_hl_justification (HL_EqElim x161 x162) (HL_AndElim x7) = False;
equal_hl_justification (HL_AndElim x7) HL_EqIntro = False;
equal_hl_justification HL_EqIntro (HL_AndElim x7) = False;
equal_hl_justification (HL_AndElim x7) (HL_ExistsElim x141 x142 x143) = False;
equal_hl_justification (HL_ExistsElim x141 x142 x143) (HL_AndElim x7) = False;
equal_hl_justification (HL_AndElim x7) (HL_ForallIntro x13) = False;
equal_hl_justification (HL_ForallIntro x13) (HL_AndElim x7) = False;
equal_hl_justification (HL_AndElim x7) (HL_ExistsIntro x12) = False;
equal_hl_justification (HL_ExistsIntro x12) (HL_AndElim x7) = False;
equal_hl_justification (HL_AndElim x7) (HL_ForallElim x11) = False;
equal_hl_justification (HL_ForallElim x11) (HL_AndElim x7) = False;
equal_hl_justification (HL_AndElim x7) (HL_RAA x101 x102) = False;
equal_hl_justification (HL_RAA x101 x102) (HL_AndElim x7) = False;
equal_hl_justification (HL_AndElim x7) (HL_OrElim x91 x92 x93 x94 x95) = False;
equal_hl_justification (HL_OrElim x91 x92 x93 x94 x95) (HL_AndElim x7) = False;
equal_hl_justification (HL_AndElim x7) (HL_OrIntro x8) = False;
equal_hl_justification (HL_OrIntro x8) (HL_AndElim x7) = False;
equal_hl_justification (HL_AndIntro x61 x62) (HL_QN x21a) = False;
equal_hl_justification (HL_QN x21a) (HL_AndIntro x61 x62) = False;
equal_hl_justification (HL_AndIntro x61 x62) (HL_IffElim x201 x202) = False;
equal_hl_justification (HL_IffElim x201 x202) (HL_AndIntro x61 x62) = False;
equal_hl_justification (HL_AndIntro x61 x62) (HL_IffIntro x191 x192) = False;
equal_hl_justification (HL_IffIntro x191 x192) (HL_AndIntro x61 x62) = False;
equal_hl_justification (HL_AndIntro x61 x62) (HL_PropTaut x18) = False;
equal_hl_justification (HL_PropTaut x18) (HL_AndIntro x61 x62) = False;
equal_hl_justification (HL_AndIntro x61 x62) HL_LEM = False;
equal_hl_justification HL_LEM (HL_AndIntro x61 x62) = False;
equal_hl_justification (HL_AndIntro x61 x62) (HL_EqElim x161 x162) = False;
equal_hl_justification (HL_EqElim x161 x162) (HL_AndIntro x61 x62) = False;
equal_hl_justification (HL_AndIntro x61 x62) HL_EqIntro = False;
equal_hl_justification HL_EqIntro (HL_AndIntro x61 x62) = False;
equal_hl_justification (HL_AndIntro x61 x62) (HL_ExistsElim x141 x142 x143) =
  False;
equal_hl_justification (HL_ExistsElim x141 x142 x143) (HL_AndIntro x61 x62) =
  False;
equal_hl_justification (HL_AndIntro x61 x62) (HL_ForallIntro x13) = False;
equal_hl_justification (HL_ForallIntro x13) (HL_AndIntro x61 x62) = False;
equal_hl_justification (HL_AndIntro x61 x62) (HL_ExistsIntro x12) = False;
equal_hl_justification (HL_ExistsIntro x12) (HL_AndIntro x61 x62) = False;
equal_hl_justification (HL_AndIntro x61 x62) (HL_ForallElim x11) = False;
equal_hl_justification (HL_ForallElim x11) (HL_AndIntro x61 x62) = False;
equal_hl_justification (HL_AndIntro x61 x62) (HL_RAA x101 x102) = False;
equal_hl_justification (HL_RAA x101 x102) (HL_AndIntro x61 x62) = False;
equal_hl_justification (HL_AndIntro x61 x62) (HL_OrElim x91 x92 x93 x94 x95) =
  False;
equal_hl_justification (HL_OrElim x91 x92 x93 x94 x95) (HL_AndIntro x61 x62) =
  False;
equal_hl_justification (HL_AndIntro x61 x62) (HL_OrIntro x8) = False;
equal_hl_justification (HL_OrIntro x8) (HL_AndIntro x61 x62) = False;
equal_hl_justification (HL_AndIntro x61 x62) (HL_AndElim x7) = False;
equal_hl_justification (HL_AndElim x7) (HL_AndIntro x61 x62) = False;
equal_hl_justification (HL_CP x51 x52) (HL_QN x21a) = False;
equal_hl_justification (HL_QN x21a) (HL_CP x51 x52) = False;
equal_hl_justification (HL_CP x51 x52) (HL_IffElim x201 x202) = False;
equal_hl_justification (HL_IffElim x201 x202) (HL_CP x51 x52) = False;
equal_hl_justification (HL_CP x51 x52) (HL_IffIntro x191 x192) = False;
equal_hl_justification (HL_IffIntro x191 x192) (HL_CP x51 x52) = False;
equal_hl_justification (HL_CP x51 x52) (HL_PropTaut x18) = False;
equal_hl_justification (HL_PropTaut x18) (HL_CP x51 x52) = False;
equal_hl_justification (HL_CP x51 x52) HL_LEM = False;
equal_hl_justification HL_LEM (HL_CP x51 x52) = False;
equal_hl_justification (HL_CP x51 x52) (HL_EqElim x161 x162) = False;
equal_hl_justification (HL_EqElim x161 x162) (HL_CP x51 x52) = False;
equal_hl_justification (HL_CP x51 x52) HL_EqIntro = False;
equal_hl_justification HL_EqIntro (HL_CP x51 x52) = False;
equal_hl_justification (HL_CP x51 x52) (HL_ExistsElim x141 x142 x143) = False;
equal_hl_justification (HL_ExistsElim x141 x142 x143) (HL_CP x51 x52) = False;
equal_hl_justification (HL_CP x51 x52) (HL_ForallIntro x13) = False;
equal_hl_justification (HL_ForallIntro x13) (HL_CP x51 x52) = False;
equal_hl_justification (HL_CP x51 x52) (HL_ExistsIntro x12) = False;
equal_hl_justification (HL_ExistsIntro x12) (HL_CP x51 x52) = False;
equal_hl_justification (HL_CP x51 x52) (HL_ForallElim x11) = False;
equal_hl_justification (HL_ForallElim x11) (HL_CP x51 x52) = False;
equal_hl_justification (HL_CP x51 x52) (HL_RAA x101 x102) = False;
equal_hl_justification (HL_RAA x101 x102) (HL_CP x51 x52) = False;
equal_hl_justification (HL_CP x51 x52) (HL_OrElim x91 x92 x93 x94 x95) = False;
equal_hl_justification (HL_OrElim x91 x92 x93 x94 x95) (HL_CP x51 x52) = False;
equal_hl_justification (HL_CP x51 x52) (HL_OrIntro x8) = False;
equal_hl_justification (HL_OrIntro x8) (HL_CP x51 x52) = False;
equal_hl_justification (HL_CP x51 x52) (HL_AndElim x7) = False;
equal_hl_justification (HL_AndElim x7) (HL_CP x51 x52) = False;
equal_hl_justification (HL_CP x51 x52) (HL_AndIntro x61 x62) = False;
equal_hl_justification (HL_AndIntro x61 x62) (HL_CP x51 x52) = False;
equal_hl_justification (HL_DN x4) (HL_QN x21a) = False;
equal_hl_justification (HL_QN x21a) (HL_DN x4) = False;
equal_hl_justification (HL_DN x4) (HL_IffElim x201 x202) = False;
equal_hl_justification (HL_IffElim x201 x202) (HL_DN x4) = False;
equal_hl_justification (HL_DN x4) (HL_IffIntro x191 x192) = False;
equal_hl_justification (HL_IffIntro x191 x192) (HL_DN x4) = False;
equal_hl_justification (HL_DN x4) (HL_PropTaut x18) = False;
equal_hl_justification (HL_PropTaut x18) (HL_DN x4) = False;
equal_hl_justification (HL_DN x4) HL_LEM = False;
equal_hl_justification HL_LEM (HL_DN x4) = False;
equal_hl_justification (HL_DN x4) (HL_EqElim x161 x162) = False;
equal_hl_justification (HL_EqElim x161 x162) (HL_DN x4) = False;
equal_hl_justification (HL_DN x4) HL_EqIntro = False;
equal_hl_justification HL_EqIntro (HL_DN x4) = False;
equal_hl_justification (HL_DN x4) (HL_ExistsElim x141 x142 x143) = False;
equal_hl_justification (HL_ExistsElim x141 x142 x143) (HL_DN x4) = False;
equal_hl_justification (HL_DN x4) (HL_ForallIntro x13) = False;
equal_hl_justification (HL_ForallIntro x13) (HL_DN x4) = False;
equal_hl_justification (HL_DN x4) (HL_ExistsIntro x12) = False;
equal_hl_justification (HL_ExistsIntro x12) (HL_DN x4) = False;
equal_hl_justification (HL_DN x4) (HL_ForallElim x11) = False;
equal_hl_justification (HL_ForallElim x11) (HL_DN x4) = False;
equal_hl_justification (HL_DN x4) (HL_RAA x101 x102) = False;
equal_hl_justification (HL_RAA x101 x102) (HL_DN x4) = False;
equal_hl_justification (HL_DN x4) (HL_OrElim x91 x92 x93 x94 x95) = False;
equal_hl_justification (HL_OrElim x91 x92 x93 x94 x95) (HL_DN x4) = False;
equal_hl_justification (HL_DN x4) (HL_OrIntro x8) = False;
equal_hl_justification (HL_OrIntro x8) (HL_DN x4) = False;
equal_hl_justification (HL_DN x4) (HL_AndElim x7) = False;
equal_hl_justification (HL_AndElim x7) (HL_DN x4) = False;
equal_hl_justification (HL_DN x4) (HL_AndIntro x61 x62) = False;
equal_hl_justification (HL_AndIntro x61 x62) (HL_DN x4) = False;
equal_hl_justification (HL_DN x4) (HL_CP x51 x52) = False;
equal_hl_justification (HL_CP x51 x52) (HL_DN x4) = False;
equal_hl_justification (HL_MT x31 x32) (HL_QN x21a) = False;
equal_hl_justification (HL_QN x21a) (HL_MT x31 x32) = False;
equal_hl_justification (HL_MT x31 x32) (HL_IffElim x201 x202) = False;
equal_hl_justification (HL_IffElim x201 x202) (HL_MT x31 x32) = False;
equal_hl_justification (HL_MT x31 x32) (HL_IffIntro x191 x192) = False;
equal_hl_justification (HL_IffIntro x191 x192) (HL_MT x31 x32) = False;
equal_hl_justification (HL_MT x31 x32) (HL_PropTaut x18) = False;
equal_hl_justification (HL_PropTaut x18) (HL_MT x31 x32) = False;
equal_hl_justification (HL_MT x31 x32) HL_LEM = False;
equal_hl_justification HL_LEM (HL_MT x31 x32) = False;
equal_hl_justification (HL_MT x31 x32) (HL_EqElim x161 x162) = False;
equal_hl_justification (HL_EqElim x161 x162) (HL_MT x31 x32) = False;
equal_hl_justification (HL_MT x31 x32) HL_EqIntro = False;
equal_hl_justification HL_EqIntro (HL_MT x31 x32) = False;
equal_hl_justification (HL_MT x31 x32) (HL_ExistsElim x141 x142 x143) = False;
equal_hl_justification (HL_ExistsElim x141 x142 x143) (HL_MT x31 x32) = False;
equal_hl_justification (HL_MT x31 x32) (HL_ForallIntro x13) = False;
equal_hl_justification (HL_ForallIntro x13) (HL_MT x31 x32) = False;
equal_hl_justification (HL_MT x31 x32) (HL_ExistsIntro x12) = False;
equal_hl_justification (HL_ExistsIntro x12) (HL_MT x31 x32) = False;
equal_hl_justification (HL_MT x31 x32) (HL_ForallElim x11) = False;
equal_hl_justification (HL_ForallElim x11) (HL_MT x31 x32) = False;
equal_hl_justification (HL_MT x31 x32) (HL_RAA x101 x102) = False;
equal_hl_justification (HL_RAA x101 x102) (HL_MT x31 x32) = False;
equal_hl_justification (HL_MT x31 x32) (HL_OrElim x91 x92 x93 x94 x95) = False;
equal_hl_justification (HL_OrElim x91 x92 x93 x94 x95) (HL_MT x31 x32) = False;
equal_hl_justification (HL_MT x31 x32) (HL_OrIntro x8) = False;
equal_hl_justification (HL_OrIntro x8) (HL_MT x31 x32) = False;
equal_hl_justification (HL_MT x31 x32) (HL_AndElim x7) = False;
equal_hl_justification (HL_AndElim x7) (HL_MT x31 x32) = False;
equal_hl_justification (HL_MT x31 x32) (HL_AndIntro x61 x62) = False;
equal_hl_justification (HL_AndIntro x61 x62) (HL_MT x31 x32) = False;
equal_hl_justification (HL_MT x31 x32) (HL_CP x51 x52) = False;
equal_hl_justification (HL_CP x51 x52) (HL_MT x31 x32) = False;
equal_hl_justification (HL_MT x31 x32) (HL_DN x4) = False;
equal_hl_justification (HL_DN x4) (HL_MT x31 x32) = False;
equal_hl_justification (HL_MP x21 x22) (HL_QN x21a) = False;
equal_hl_justification (HL_QN x21a) (HL_MP x21 x22) = False;
equal_hl_justification (HL_MP x21 x22) (HL_IffElim x201 x202) = False;
equal_hl_justification (HL_IffElim x201 x202) (HL_MP x21 x22) = False;
equal_hl_justification (HL_MP x21 x22) (HL_IffIntro x191 x192) = False;
equal_hl_justification (HL_IffIntro x191 x192) (HL_MP x21 x22) = False;
equal_hl_justification (HL_MP x21 x22) (HL_PropTaut x18) = False;
equal_hl_justification (HL_PropTaut x18) (HL_MP x21 x22) = False;
equal_hl_justification (HL_MP x21 x22) HL_LEM = False;
equal_hl_justification HL_LEM (HL_MP x21 x22) = False;
equal_hl_justification (HL_MP x21 x22) (HL_EqElim x161 x162) = False;
equal_hl_justification (HL_EqElim x161 x162) (HL_MP x21 x22) = False;
equal_hl_justification (HL_MP x21 x22) HL_EqIntro = False;
equal_hl_justification HL_EqIntro (HL_MP x21 x22) = False;
equal_hl_justification (HL_MP x21 x22) (HL_ExistsElim x141 x142 x143) = False;
equal_hl_justification (HL_ExistsElim x141 x142 x143) (HL_MP x21 x22) = False;
equal_hl_justification (HL_MP x21 x22) (HL_ForallIntro x13) = False;
equal_hl_justification (HL_ForallIntro x13) (HL_MP x21 x22) = False;
equal_hl_justification (HL_MP x21 x22) (HL_ExistsIntro x12) = False;
equal_hl_justification (HL_ExistsIntro x12) (HL_MP x21 x22) = False;
equal_hl_justification (HL_MP x21 x22) (HL_ForallElim x11) = False;
equal_hl_justification (HL_ForallElim x11) (HL_MP x21 x22) = False;
equal_hl_justification (HL_MP x21 x22) (HL_RAA x101 x102) = False;
equal_hl_justification (HL_RAA x101 x102) (HL_MP x21 x22) = False;
equal_hl_justification (HL_MP x21 x22) (HL_OrElim x91 x92 x93 x94 x95) = False;
equal_hl_justification (HL_OrElim x91 x92 x93 x94 x95) (HL_MP x21 x22) = False;
equal_hl_justification (HL_MP x21 x22) (HL_OrIntro x8) = False;
equal_hl_justification (HL_OrIntro x8) (HL_MP x21 x22) = False;
equal_hl_justification (HL_MP x21 x22) (HL_AndElim x7) = False;
equal_hl_justification (HL_AndElim x7) (HL_MP x21 x22) = False;
equal_hl_justification (HL_MP x21 x22) (HL_AndIntro x61 x62) = False;
equal_hl_justification (HL_AndIntro x61 x62) (HL_MP x21 x22) = False;
equal_hl_justification (HL_MP x21 x22) (HL_CP x51 x52) = False;
equal_hl_justification (HL_CP x51 x52) (HL_MP x21 x22) = False;
equal_hl_justification (HL_MP x21 x22) (HL_DN x4) = False;
equal_hl_justification (HL_DN x4) (HL_MP x21 x22) = False;
equal_hl_justification (HL_MP x21 x22) (HL_MT x31 x32) = False;
equal_hl_justification (HL_MT x31 x32) (HL_MP x21 x22) = False;
equal_hl_justification HL_Assumption (HL_QN x21a) = False;
equal_hl_justification (HL_QN x21a) HL_Assumption = False;
equal_hl_justification HL_Assumption (HL_IffElim x201 x202) = False;
equal_hl_justification (HL_IffElim x201 x202) HL_Assumption = False;
equal_hl_justification HL_Assumption (HL_IffIntro x191 x192) = False;
equal_hl_justification (HL_IffIntro x191 x192) HL_Assumption = False;
equal_hl_justification HL_Assumption (HL_PropTaut x18) = False;
equal_hl_justification (HL_PropTaut x18) HL_Assumption = False;
equal_hl_justification HL_Assumption HL_LEM = False;
equal_hl_justification HL_LEM HL_Assumption = False;
equal_hl_justification HL_Assumption (HL_EqElim x161 x162) = False;
equal_hl_justification (HL_EqElim x161 x162) HL_Assumption = False;
equal_hl_justification HL_Assumption HL_EqIntro = False;
equal_hl_justification HL_EqIntro HL_Assumption = False;
equal_hl_justification HL_Assumption (HL_ExistsElim x141 x142 x143) = False;
equal_hl_justification (HL_ExistsElim x141 x142 x143) HL_Assumption = False;
equal_hl_justification HL_Assumption (HL_ForallIntro x13) = False;
equal_hl_justification (HL_ForallIntro x13) HL_Assumption = False;
equal_hl_justification HL_Assumption (HL_ExistsIntro x12) = False;
equal_hl_justification (HL_ExistsIntro x12) HL_Assumption = False;
equal_hl_justification HL_Assumption (HL_ForallElim x11) = False;
equal_hl_justification (HL_ForallElim x11) HL_Assumption = False;
equal_hl_justification HL_Assumption (HL_RAA x101 x102) = False;
equal_hl_justification (HL_RAA x101 x102) HL_Assumption = False;
equal_hl_justification HL_Assumption (HL_OrElim x91 x92 x93 x94 x95) = False;
equal_hl_justification (HL_OrElim x91 x92 x93 x94 x95) HL_Assumption = False;
equal_hl_justification HL_Assumption (HL_OrIntro x8) = False;
equal_hl_justification (HL_OrIntro x8) HL_Assumption = False;
equal_hl_justification HL_Assumption (HL_AndElim x7) = False;
equal_hl_justification (HL_AndElim x7) HL_Assumption = False;
equal_hl_justification HL_Assumption (HL_AndIntro x61 x62) = False;
equal_hl_justification (HL_AndIntro x61 x62) HL_Assumption = False;
equal_hl_justification HL_Assumption (HL_CP x51 x52) = False;
equal_hl_justification (HL_CP x51 x52) HL_Assumption = False;
equal_hl_justification HL_Assumption (HL_DN x4) = False;
equal_hl_justification (HL_DN x4) HL_Assumption = False;
equal_hl_justification HL_Assumption (HL_MT x31 x32) = False;
equal_hl_justification (HL_MT x31 x32) HL_Assumption = False;
equal_hl_justification HL_Assumption (HL_MP x21 x22) = False;
equal_hl_justification (HL_MP x21 x22) HL_Assumption = False;
equal_hl_justification (HL_QN x21a) (HL_QN y21a) = equal_int x21a y21a;
equal_hl_justification (HL_IffElim x201 x202) (HL_IffElim y201 y202) =
  equal_int x201 y201 && equal_int x202 y202;
equal_hl_justification (HL_IffIntro x191 x192) (HL_IffIntro y191 y192) =
  equal_int x191 y191 && equal_int x192 y192;
equal_hl_justification (HL_PropTaut x18) (HL_PropTaut y18) = x18 == y18;
equal_hl_justification (HL_EqElim x161 x162) (HL_EqElim y161 y162) =
  equal_int x161 y161 && equal_int x162 y162;
equal_hl_justification (HL_ExistsElim x141 x142 x143)
  (HL_ExistsElim y141 y142 y143) =
  equal_int x141 y141 && equal_int x142 y142 && equal_int x143 y143;
equal_hl_justification (HL_ForallIntro x13) (HL_ForallIntro y13) =
  equal_int x13 y13;
equal_hl_justification (HL_ExistsIntro x12) (HL_ExistsIntro y12) =
  equal_int x12 y12;
equal_hl_justification (HL_ForallElim x11) (HL_ForallElim y11) =
  equal_int x11 y11;
equal_hl_justification (HL_RAA x101 x102) (HL_RAA y101 y102) =
  equal_int x101 y101 && equal_int x102 y102;
equal_hl_justification (HL_OrElim x91 x92 x93 x94 x95)
  (HL_OrElim y91 y92 y93 y94 y95) =
  equal_int x91 y91 &&
    equal_int x92 y92 &&
      equal_int x93 y93 && equal_int x94 y94 && equal_int x95 y95;
equal_hl_justification (HL_OrIntro x8) (HL_OrIntro y8) = equal_int x8 y8;
equal_hl_justification (HL_AndElim x7) (HL_AndElim y7) = equal_int x7 y7;
equal_hl_justification (HL_AndIntro x61 x62) (HL_AndIntro y61 y62) =
  equal_int x61 y61 && equal_int x62 y62;
equal_hl_justification (HL_CP x51 x52) (HL_CP y51 y52) =
  equal_int x51 y51 && equal_int x52 y52;
equal_hl_justification (HL_DN x4) (HL_DN y4) = equal_int x4 y4;
equal_hl_justification (HL_MT x31 x32) (HL_MT y31 y32) =
  equal_int x31 y31 && equal_int x32 y32;
equal_hl_justification (HL_MP x21 x22) (HL_MP y21 y22) =
  equal_int x21 y21 && equal_int x22 y22;
equal_hl_justification HL_LEM HL_LEM = True;
equal_hl_justification HL_EqIntro HL_EqIntro = True;
equal_hl_justification HL_Assumption HL_Assumption = True;

instance Eq Hl_justification where {
  a == b = equal_hl_justification a b;
};

data Hl_formula = HL_Predicate String [Hl_term] | HL_Boolean Bool
  | HL_Not Hl_formula | HL_And Hl_formula Hl_formula
  | HL_Or Hl_formula Hl_formula | HL_Implies Hl_formula Hl_formula
  | HL_Iff Hl_formula Hl_formula | HL_ForAll String Hl_formula
  | HL_Exists String Hl_formula;

equal_hl_formula :: Hl_formula -> Hl_formula -> Bool;
equal_hl_formula (HL_ForAll x81 x82) (HL_Exists x91 x92) = False;
equal_hl_formula (HL_Exists x91 x92) (HL_ForAll x81 x82) = False;
equal_hl_formula (HL_Iff x71 x72) (HL_Exists x91 x92) = False;
equal_hl_formula (HL_Exists x91 x92) (HL_Iff x71 x72) = False;
equal_hl_formula (HL_Iff x71 x72) (HL_ForAll x81 x82) = False;
equal_hl_formula (HL_ForAll x81 x82) (HL_Iff x71 x72) = False;
equal_hl_formula (HL_Implies x61 x62) (HL_Exists x91 x92) = False;
equal_hl_formula (HL_Exists x91 x92) (HL_Implies x61 x62) = False;
equal_hl_formula (HL_Implies x61 x62) (HL_ForAll x81 x82) = False;
equal_hl_formula (HL_ForAll x81 x82) (HL_Implies x61 x62) = False;
equal_hl_formula (HL_Implies x61 x62) (HL_Iff x71 x72) = False;
equal_hl_formula (HL_Iff x71 x72) (HL_Implies x61 x62) = False;
equal_hl_formula (HL_Or x51 x52) (HL_Exists x91 x92) = False;
equal_hl_formula (HL_Exists x91 x92) (HL_Or x51 x52) = False;
equal_hl_formula (HL_Or x51 x52) (HL_ForAll x81 x82) = False;
equal_hl_formula (HL_ForAll x81 x82) (HL_Or x51 x52) = False;
equal_hl_formula (HL_Or x51 x52) (HL_Iff x71 x72) = False;
equal_hl_formula (HL_Iff x71 x72) (HL_Or x51 x52) = False;
equal_hl_formula (HL_Or x51 x52) (HL_Implies x61 x62) = False;
equal_hl_formula (HL_Implies x61 x62) (HL_Or x51 x52) = False;
equal_hl_formula (HL_And x41 x42) (HL_Exists x91 x92) = False;
equal_hl_formula (HL_Exists x91 x92) (HL_And x41 x42) = False;
equal_hl_formula (HL_And x41 x42) (HL_ForAll x81 x82) = False;
equal_hl_formula (HL_ForAll x81 x82) (HL_And x41 x42) = False;
equal_hl_formula (HL_And x41 x42) (HL_Iff x71 x72) = False;
equal_hl_formula (HL_Iff x71 x72) (HL_And x41 x42) = False;
equal_hl_formula (HL_And x41 x42) (HL_Implies x61 x62) = False;
equal_hl_formula (HL_Implies x61 x62) (HL_And x41 x42) = False;
equal_hl_formula (HL_And x41 x42) (HL_Or x51 x52) = False;
equal_hl_formula (HL_Or x51 x52) (HL_And x41 x42) = False;
equal_hl_formula (HL_Not x3) (HL_Exists x91 x92) = False;
equal_hl_formula (HL_Exists x91 x92) (HL_Not x3) = False;
equal_hl_formula (HL_Not x3) (HL_ForAll x81 x82) = False;
equal_hl_formula (HL_ForAll x81 x82) (HL_Not x3) = False;
equal_hl_formula (HL_Not x3) (HL_Iff x71 x72) = False;
equal_hl_formula (HL_Iff x71 x72) (HL_Not x3) = False;
equal_hl_formula (HL_Not x3) (HL_Implies x61 x62) = False;
equal_hl_formula (HL_Implies x61 x62) (HL_Not x3) = False;
equal_hl_formula (HL_Not x3) (HL_Or x51 x52) = False;
equal_hl_formula (HL_Or x51 x52) (HL_Not x3) = False;
equal_hl_formula (HL_Not x3) (HL_And x41 x42) = False;
equal_hl_formula (HL_And x41 x42) (HL_Not x3) = False;
equal_hl_formula (HL_Boolean x2) (HL_Exists x91 x92) = False;
equal_hl_formula (HL_Exists x91 x92) (HL_Boolean x2) = False;
equal_hl_formula (HL_Boolean x2) (HL_ForAll x81 x82) = False;
equal_hl_formula (HL_ForAll x81 x82) (HL_Boolean x2) = False;
equal_hl_formula (HL_Boolean x2) (HL_Iff x71 x72) = False;
equal_hl_formula (HL_Iff x71 x72) (HL_Boolean x2) = False;
equal_hl_formula (HL_Boolean x2) (HL_Implies x61 x62) = False;
equal_hl_formula (HL_Implies x61 x62) (HL_Boolean x2) = False;
equal_hl_formula (HL_Boolean x2) (HL_Or x51 x52) = False;
equal_hl_formula (HL_Or x51 x52) (HL_Boolean x2) = False;
equal_hl_formula (HL_Boolean x2) (HL_And x41 x42) = False;
equal_hl_formula (HL_And x41 x42) (HL_Boolean x2) = False;
equal_hl_formula (HL_Boolean x2) (HL_Not x3) = False;
equal_hl_formula (HL_Not x3) (HL_Boolean x2) = False;
equal_hl_formula (HL_Predicate x11 x12) (HL_Exists x91 x92) = False;
equal_hl_formula (HL_Exists x91 x92) (HL_Predicate x11 x12) = False;
equal_hl_formula (HL_Predicate x11 x12) (HL_ForAll x81 x82) = False;
equal_hl_formula (HL_ForAll x81 x82) (HL_Predicate x11 x12) = False;
equal_hl_formula (HL_Predicate x11 x12) (HL_Iff x71 x72) = False;
equal_hl_formula (HL_Iff x71 x72) (HL_Predicate x11 x12) = False;
equal_hl_formula (HL_Predicate x11 x12) (HL_Implies x61 x62) = False;
equal_hl_formula (HL_Implies x61 x62) (HL_Predicate x11 x12) = False;
equal_hl_formula (HL_Predicate x11 x12) (HL_Or x51 x52) = False;
equal_hl_formula (HL_Or x51 x52) (HL_Predicate x11 x12) = False;
equal_hl_formula (HL_Predicate x11 x12) (HL_And x41 x42) = False;
equal_hl_formula (HL_And x41 x42) (HL_Predicate x11 x12) = False;
equal_hl_formula (HL_Predicate x11 x12) (HL_Not x3) = False;
equal_hl_formula (HL_Not x3) (HL_Predicate x11 x12) = False;
equal_hl_formula (HL_Predicate x11 x12) (HL_Boolean x2) = False;
equal_hl_formula (HL_Boolean x2) (HL_Predicate x11 x12) = False;
equal_hl_formula (HL_Exists x91 x92) (HL_Exists y91 y92) =
  x91 == y91 && equal_hl_formula x92 y92;
equal_hl_formula (HL_ForAll x81 x82) (HL_ForAll y81 y82) =
  x81 == y81 && equal_hl_formula x82 y82;
equal_hl_formula (HL_Iff x71 x72) (HL_Iff y71 y72) =
  equal_hl_formula x71 y71 && equal_hl_formula x72 y72;
equal_hl_formula (HL_Implies x61 x62) (HL_Implies y61 y62) =
  equal_hl_formula x61 y61 && equal_hl_formula x62 y62;
equal_hl_formula (HL_Or x51 x52) (HL_Or y51 y52) =
  equal_hl_formula x51 y51 && equal_hl_formula x52 y52;
equal_hl_formula (HL_And x41 x42) (HL_And y41 y42) =
  equal_hl_formula x41 y41 && equal_hl_formula x42 y42;
equal_hl_formula (HL_Not x3) (HL_Not y3) = equal_hl_formula x3 y3;
equal_hl_formula (HL_Boolean x2) (HL_Boolean y2) = x2 == y2;
equal_hl_formula (HL_Predicate x11 x12) (HL_Predicate y11 y12) =
  x11 == y11 && x12 == y12;

instance Eq Hl_formula where {
  a == b = equal_hl_formula a b;
};

data Set a = Set [a] | Coset [a];

data Char = Char Bool Bool Bool Bool Bool Bool Bool Bool;

data Sum a b = Inl a | Inr b;

data Fitch_rule = FPremise | FAssume | FMP Nat Nat | FCP (Nat, Nat)
  | FRAA (Nat, Nat) | FDN Nat | FBotI Nat Nat | FAndIntro Nat Nat
  | FAndElimL Nat | FAndElimR Nat | FOrIntroL Nat | FOrIntroR Nat
  | FOrElim Nat (Nat, Nat) (Nat, Nat) | FIffIntro Nat Nat | FIffElimL Nat
  | FIffElimR Nat | FForallElim Nat | FForallIntro Nat | FExistsIntro Nat
  | FExistsElim Nat (Nat, Nat) | FEqIntro | FEqElim Nat Nat | FReit Nat;

data Fline = FL Nat Fm Fitch_rule [Nat];

data Hl_line = HL_ProofLine Int Hl_formula Hl_justification (Set Int);

data Pline = ProofLine Nat Fm Justa (Set Nat);

data Route = Direct | ViaTree;

data Subproof = Subproof Nat Fm [Fitch_item];

data Fitch_item = FLine Nat Fm Fitch_rule | FSub Subproof;

data Deriv = Deriv Fm Drule;

data Drule = DAssume Nat | DPremise Nat | DMP Deriv Deriv | DCP Nat Fm Deriv
  | DRAA Nat Fm Deriv | DDN Deriv | DBotI Deriv Deriv | DAndIntro Deriv Deriv
  | DAndElimL Deriv | DAndElimR Deriv | DOrIntroL Deriv | DOrIntroR Deriv
  | DOrElim Deriv Nat Fm Deriv Nat Fm Deriv | DIffIntro Deriv Deriv
  | DIffElimL Deriv | DIffElimR Deriv | DForallElim Deriv | DForallIntro Deriv
  | DExistsIntro Deriv | DExistsElim Deriv Nat Fm Deriv | DEqIntro
  | DEqElim Deriv Deriv | DReit Deriv;

data Hl_route = HL_DirectRoute | HL_ViaTreeRoute;

data Hl_fitch_rule = HL_FPremise | HL_FAssume | HL_FMP Int Int | HL_FMT Int Int
  | HL_FDN Int | HL_FCP (Int, Int) | HL_FAndI Int Int | HL_FAndE Int
  | HL_FOrI Int | HL_FOrE Int (Int, Int) (Int, Int) | HL_FRAA (Int, Int)
  | HL_FForallE Int | HL_FForallI Int | HL_FExistsI Int
  | HL_FExistsE Int (Int, Int) | HL_FEqI | HL_FEqE Int Int | HL_FLEM
  | HL_FPropTaut [Int] | HL_FIffI Int Int | HL_FIffE Int Int | HL_FQN Int
  | HL_FReit Int;

data Hl_subproof = HL_Subproof Int Hl_formula [Hl_fitch_item];

data Hl_fitch_item = HL_FLine Int Hl_formula Hl_fitch_rule
  | HL_FSub Hl_subproof;

data Translation_error = NotNested Nat Nat [Nat] | OutOfScope Nat Nat Nat
  | PremiseInBox Nat Nat | PremiseLate Nat Nat | BoxReversed Nat Nat
  | AssumptionReused Nat Nat Nat | NotCorrect Nat;

data Hl_derivation = HL_Derivation Hl_formula Hl_derivation_rule;

data Hl_derivation_rule = HL_DAssume Int | HL_DPremise Int
  | HL_DMP Hl_derivation Hl_derivation | HL_DMT Hl_derivation Hl_derivation
  | HL_DDN Hl_derivation | HL_DCP Int Hl_formula Hl_derivation
  | HL_DAndI Hl_derivation Hl_derivation | HL_DAndE Hl_derivation
  | HL_DOrI Hl_derivation
  | HL_DOrE Hl_derivation Int Hl_formula Hl_derivation Int Hl_formula
      Hl_derivation
  | HL_DRAA Int Hl_formula Hl_derivation | HL_DForallE Hl_derivation
  | HL_DForallI Hl_derivation | HL_DExistsI Hl_derivation
  | HL_DExistsE Hl_derivation Int Hl_formula Hl_derivation | HL_DEqI
  | HL_DEqE Hl_derivation Hl_derivation | HL_DLEM | HL_DPropTaut [Hl_derivation]
  | HL_DIffI Hl_derivation Hl_derivation | HL_DIffE Hl_derivation Hl_derivation
  | HL_DQN Hl_derivation;

data Hl_check_error = HL_DuplicateLine Int Int | HL_LateCitation Int [Int]
  | HL_InvalidAssumption Int | HL_MissingCited Hl_justification Int
  | HL_MPFirstNotConditional Int | HL_MPSecondNotAntecedent Int
  | HL_AndElimNotConjunction Int | HL_OrIntroNotDisjunct | HL_DNShape Int
  | HL_MTFailed Int Int Int Bool Bool Bool | HL_EqElimNotEquality
  | HL_AndIntroMismatch Int Hl_formula Hl_formula Hl_formula
  | HL_MPNotConsequent Hl_formula | HL_ForallIntroNotInstance Int
  | HL_ForallIntroAbstraction | HL_ForallElimNoConstants
  | HL_ExistsIntroNotWitness | HL_ExistsElimNotAssumption Int
  | HL_ExistsElimNotRepeated Int Int
  | HL_RAAFailed Int Int Int Bool Bool Bool [Int] [Int]
  | HL_OrElimFailed Int Int Int Int Bool Bool
  | HL_RuleRejected Hl_justification Int | HL_RuleFailed Int;

data Hl_finite_model a =
  HL_FiniteModel [a] [(String, a)] [((String, Nat), [[a]])];

data Hl_translation_error = HL_NotNested Int Int [Int]
  | HL_OutOfScope Int Int Int | HL_UnknownAssumption Int Int
  | HL_MissingLine Int | HL_EigenInScope Int String Int
  | HL_PremiseInBox Int Int | HL_PremiseLate Int Int | HL_BoxReversed Int Int
  | HL_AssumptionReused Int Int Int | HL_SourceNotVerified Int
  | HL_TargetNotVerified;

plus_nat :: Nat -> Nat -> Nat;
plus_nat m n = Nat (integer_of_nat m + integer_of_nat n);

one_nat :: Nat;
one_nat = Nat (1 :: Integer);

suc :: Nat -> Nat;
suc n = plus_nat n one_nat;

upt :: Nat -> Nat -> [Nat];
upt i j = (if less_nat i j then i : upt (suc i) j else []);

ball :: forall a. Set a -> (a -> Bool) -> Bool;
ball (Set xs) p = all p xs;

max :: forall a. (Ord a) => a -> a -> a;
max a b = (if less_eq a b then b else a);

minus_nat :: Nat -> Nat -> Nat;
minus_nat m n = Nat (max (0 :: Integer) (integer_of_nat m - integer_of_nat n));

zero_nat :: Nat;
zero_nat = Nat (0 :: Integer);

drop :: forall a. Nat -> [a] -> [a];
drop n [] = [];
drop n (x : xs) =
  (if equal_nat n zero_nat then x : xs else drop (minus_nat n one_nat) xs);

find :: forall a. (a -> Bool) -> [a] -> Maybe a;
find uu [] = Nothing;
find p (x : xs) = (if p x then Just x else find p xs);

fold :: forall a b. (a -> b -> b) -> [a] -> b -> b;
fold f [] s = s;
fold f (x : xs) s = fold f xs (f x s);

last :: forall a. [a] -> a;
last (x : xs) = (if null xs then x else last xs);

take :: forall a. Nat -> [a] -> [a];
take n [] = [];
take n (x : xs) =
  (if equal_nat n zero_nat then [] else x : take (minus_nat n one_nat) xs);

image :: forall a b. (a -> b) -> Set a -> Set b;
image f (Set xs) = Set (map f xs);

foldl :: forall a b. (a -> b -> a) -> a -> [b] -> a;
foldl f a [] = a;
foldl f a (x : xs) = foldl f (f a x) xs;

foldr :: forall a b. (a -> b -> b) -> [a] -> b -> b;
foldr f [] = id;
foldr f (x : xs) = f x . foldr f xs;

map_of :: forall a b. (Eq a) => [(a, b)] -> a -> Maybe b;
map_of [] k = Nothing;
map_of ((l, v) : ps) k = (if l == k then Just v else map_of ps k);

filtera :: forall a. (a -> Bool) -> Set a -> Set a;
filtera p (Set xs) = Set (filter p xs);

removeAll :: forall a. (Eq a) => a -> [a] -> [a];
removeAll x [] = [];
removeAll x (y : xs) = (if x == y then removeAll x xs else y : removeAll x xs);

membera :: forall a. (Eq a) => [a] -> a -> Bool;
membera [] y = False;
membera (x : xs) y = x == y || membera xs y;

inserta :: forall a. (Eq a) => a -> [a] -> [a];
inserta x xs = (if membera xs x then xs else x : xs);

insert :: forall a. (Eq a) => a -> Set a -> Set a;
insert x (Set xs) = Set (inserta x xs);
insert x (Coset xs) = Coset (removeAll x xs);

member :: forall a. (Eq a) => a -> Set a -> Bool;
member x (Set xs) = membera xs x;
member x (Coset xs) = not (membera xs x);

remove :: forall a. (Eq a) => a -> Set a -> Set a;
remove x (Set xs) = Set (removeAll x xs);
remove x (Coset xs) = Coset (inserta x xs);

fun_upd :: forall a b. (Eq a) => (a -> b) -> a -> b -> a -> b;
fun_upd f a b = (\ x -> (if x == a then b else f x));

tl :: forall a. [a] -> [a];
tl [] = [];
tl (x21 : x22) = x22;

product :: forall a b. [a] -> [b] -> [(a, b)];
product [] uu = [];
product (x : xs) ys = map (\ a -> (x, a)) ys ++ product xs ys;

remdups :: forall a. (Eq a) => [a] -> [a];
remdups [] = [];
remdups (x : xs) = (if membera xs x then remdups xs else x : remdups xs);

rn_t :: String -> String -> Trm -> Trm;
rn_t a b (Nm c) = Nm (if c == a then b else c);
rn_t a b (Vr y) = Vr y;

rn :: String -> String -> Fm -> Fm;
rn a b (Atom p ts) = Atom p (map (rn_t a b) ts);
rn a b (Eqf t u) = Eqf (rn_t a b t) (rn_t a b u);
rn a b Bot = Bot;
rn a b (Neg p) = Neg (rn a b p);
rn a b (Conj p q) = Conj (rn a b p) (rn a b q);
rn a b (Disj p q) = Disj (rn a b p) (rn a b q);
rn a b (Impl p q) = Impl (rn a b p) (rn a b q);
rn a b (Iff p q) = Iff (rn a b p) (rn a b q);
rn a b (Uni y p) = Uni y (rn a b p);
rn a b (Exi y p) = Exi y (rn a b p);

cat :: [String] -> String;
cat ss = foldr (\ a b -> a ++ b) ss "";

of_bool :: forall a. (Zero_neq_one a) => Bool -> a;
of_bool False = zero;
of_bool True = one;

integer_of_char :: Char -> Integer;
integer_of_char (Char b0 b1 b2 b3 b4 b5 b6 b7) =
  ((((((of_bool b7 * (2 :: Integer) + of_bool b6) * (2 :: Integer) +
        of_bool b5) *
        (2 :: Integer) +
       of_bool b4) *
       (2 :: Integer) +
      of_bool b3) *
      (2 :: Integer) +
     of_bool b2) *
     (2 :: Integer) +
    of_bool b1) *
    (2 :: Integer) +
    of_bool b0;

implode :: [Char] -> String;
implode cs = Str_Literal.literalOfAsciis (map integer_of_char cs);

replicate :: forall a. Nat -> a -> [a];
replicate n x =
  (if equal_nat n zero_nat then [] else x : replicate (minus_nat n one_nat) x);

freshIdx :: Nat -> Nat -> String;
freshIdx base k =
  implode
    (replicate (plus_nat base k)
      (Char True True False False False True True False));

names_t :: Trm -> [String];
names_t (Nm a) = [a];
names_t (Vr uu) = [];

names :: Fm -> [String];
names (Atom uu ts) = concatMap names_t ts;
names (Eqf t u) = names_t t ++ names_t u;
names Bot = [];
names (Neg p) = names p;
names (Conj p q) = names p ++ names q;
names (Disj p q) = names p ++ names q;
names (Impl p q) = names p ++ names q;
names (Iff p q) = names p ++ names q;
names (Uni uv p) = names p;
names (Exi uw p) = names p;

arbitrary_in :: String -> [Fm] -> Bool;
arbitrary_in a ps = all (\ p -> not (membera (names p) a)) ps;

subDerivs :: Drule -> [Deriv];
subDerivs (DAssume k1) = [];
subDerivs (DPremise k1) = [];
subDerivs (DMP d1 d2) = [d1, d2];
subDerivs (DCP k1 g1 d1) = [d1];
subDerivs (DRAA k1 g1 d1) = [d1];
subDerivs (DDN d1) = [d1];
subDerivs (DBotI d1 d2) = [d1, d2];
subDerivs (DAndIntro d1 d2) = [d1, d2];
subDerivs (DAndElimL d1) = [d1];
subDerivs (DAndElimR d1) = [d1];
subDerivs (DOrIntroL d1) = [d1];
subDerivs (DOrIntroR d1) = [d1];
subDerivs (DOrElim d1 k1 g1 d2 k2 g2 d3) = [d1, d2, d3];
subDerivs (DIffIntro d1 d2) = [d1, d2];
subDerivs (DIffElimL d1) = [d1];
subDerivs (DIffElimR d1) = [d1];
subDerivs (DForallElim d1) = [d1];
subDerivs (DForallIntro d1) = [d1];
subDerivs (DExistsIntro d1) = [d1];
subDerivs (DExistsElim d1 k1 g1 d2) = [d1, d2];
subDerivs DEqIntro = [];
subDerivs (DEqElim d1 d2) = [d1, d2];
subDerivs (DReit d1) = [d1];

openAsms :: Deriv -> [(Nat, Fm)];
openAsms (Deriv phi (DAssume n)) = [(n, phi)];
openAsms (Deriv phi (DPremise n)) = [(n, phi)];
openAsms (Deriv phi (DCP a fa d)) =
  filter (\ nf -> not (equal_nat (fst nf) a)) (openAsms d);
openAsms (Deriv phi (DRAA a fa d)) =
  filter (\ nf -> not (equal_nat (fst nf) a)) (openAsms d);
openAsms (Deriv phi (DOrElim d0 a1 f1 d1 a2 f2 d2)) =
  openAsms d0 ++
    filter (\ nf -> not (equal_nat (fst nf) a1)) (openAsms d1) ++
      filter (\ nf -> not (equal_nat (fst nf) a2)) (openAsms d2);
openAsms (Deriv phi (DExistsElim d0 a f d1)) =
  openAsms d0 ++ filter (\ nf -> not (equal_nat (fst nf) a)) (openAsms d1);
openAsms (Deriv phi (DMP v va)) = concatMap openAsms (subDerivs (DMP v va));
openAsms (Deriv phi (DDN v)) = concatMap openAsms (subDerivs (DDN v));
openAsms (Deriv phi (DBotI v va)) = concatMap openAsms (subDerivs (DBotI v va));
openAsms (Deriv phi (DAndIntro v va)) =
  concatMap openAsms (subDerivs (DAndIntro v va));
openAsms (Deriv phi (DAndElimL v)) =
  concatMap openAsms (subDerivs (DAndElimL v));
openAsms (Deriv phi (DAndElimR v)) =
  concatMap openAsms (subDerivs (DAndElimR v));
openAsms (Deriv phi (DOrIntroL v)) =
  concatMap openAsms (subDerivs (DOrIntroL v));
openAsms (Deriv phi (DOrIntroR v)) =
  concatMap openAsms (subDerivs (DOrIntroR v));
openAsms (Deriv phi (DIffIntro v va)) =
  concatMap openAsms (subDerivs (DIffIntro v va));
openAsms (Deriv phi (DIffElimL v)) =
  concatMap openAsms (subDerivs (DIffElimL v));
openAsms (Deriv phi (DIffElimR v)) =
  concatMap openAsms (subDerivs (DIffElimR v));
openAsms (Deriv phi (DForallElim v)) =
  concatMap openAsms (subDerivs (DForallElim v));
openAsms (Deriv phi (DForallIntro v)) =
  concatMap openAsms (subDerivs (DForallIntro v));
openAsms (Deriv phi (DExistsIntro v)) =
  concatMap openAsms (subDerivs (DExistsIntro v));
openAsms (Deriv phi DEqIntro) = concatMap openAsms (subDerivs DEqIntro);
openAsms (Deriv phi (DEqElim v va)) =
  concatMap openAsms (subDerivs (DEqElim v va));
openAsms (Deriv phi (DReit v)) = concatMap openAsms (subDerivs (DReit v));

inst_t :: String -> String -> Trm -> Trm;
inst_t x a (Nm b) = Nm b;
inst_t x a (Vr y) = (if x == y then Nm a else Vr y);

inst :: String -> String -> Fm -> Fm;
inst x a (Atom p ts) = Atom p (map (inst_t x a) ts);
inst x a (Eqf t u) = Eqf (inst_t x a t) (inst_t x a u);
inst x a Bot = Bot;
inst x a (Neg p) = Neg (inst x a p);
inst x a (Conj p q) = Conj (inst x a p) (inst x a q);
inst x a (Disj p q) = Disj (inst x a p) (inst x a q);
inst x a (Impl p q) = Impl (inst x a p) (inst x a q);
inst x a (Iff p q) = Iff (inst x a p) (inst x a q);
inst x a (Uni y p) = Uni y (if x == y then p else inst x a p);
inst x a (Exi y p) = Exi y (if x == y then p else inst x a p);

fvs_t :: Trm -> [String];
fvs_t (Nm uu) = [];
fvs_t (Vr x) = [x];

fvs :: Fm -> [String];
fvs (Atom uu ts) = concatMap fvs_t ts;
fvs (Eqf t u) = fvs_t t ++ fvs_t u;
fvs Bot = [];
fvs (Neg p) = fvs p;
fvs (Conj p q) = fvs p ++ fvs q;
fvs (Disj p q) = fvs p ++ fvs q;
fvs (Impl p q) = fvs p ++ fvs q;
fvs (Iff p q) = fvs p ++ fvs q;
fvs (Uni x p) = removeAll x (fvs p);
fvs (Exi x p) = removeAll x (fvs p);

instWitnesses :: String -> Fm -> Fm -> [String];
instWitnesses x p q =
  (if membera (fvs p) x then filter (\ a -> equal_fm (inst x a p) q) (names q)
    else []);

witnessOf :: Fm -> Fm -> Fm -> [Fm] -> Maybe String;
witnessOf ex f psi asa =
  (case ex of {
    Atom _ _ -> Nothing;
    Eqf _ _ -> Nothing;
    Bot -> Nothing;
    Neg _ -> Nothing;
    Conj _ _ -> Nothing;
    Disj _ _ -> Nothing;
    Impl _ _ -> Nothing;
    Iff _ _ -> Nothing;
    Uni _ _ -> Nothing;
    Exi x p ->
      (case filter
              (\ b ->
                not (membera (names p) b) &&
                  not (membera (names psi) b) && arbitrary_in b asa)
              (instWitnesses x p f)
        of {
        [] -> Nothing;
        b : _ -> Just b;
      });
  });

envFms :: [(Nat, (Nat, Fm))] -> [Fm];
envFms g = map (snd . snd) g;

map_filter :: forall a b. (a -> Maybe b) -> [a] -> [b];
map_filter f [] = [];
map_filter f (x : xs) = (case f x of {
                          Nothing -> map_filter f xs;
                          Just y -> y : map_filter f xs;
                        });

exRepair ::
  [(Nat, (Nat, Fm))] -> Fm -> Fm -> Fm -> Nat -> Deriv -> Deriv -> Maybe String;
exRepair g ex f psi a d0 d1 =
  (case witnessOf ex f psi
          (map snd (openAsms d0) ++
            map_filter
              (\ x ->
                (if not (equal_nat (fst x) a) then Just (snd x) else Nothing))
              (openAsms d1))
    of {
    Nothing -> Nothing;
    Just b -> (if arbitrary_in b (envFms g) then Nothing else Just b);
  });

rnD :: String -> String -> Deriv -> Deriv;
rnD a b (Deriv phi (DAssume k1)) = Deriv (rn a b phi) (DAssume k1);
rnD a b (Deriv phi (DPremise k1)) = Deriv (rn a b phi) (DPremise k1);
rnD a b (Deriv phi (DMP d1 d2)) =
  Deriv (rn a b phi) (DMP (rnD a b d1) (rnD a b d2));
rnD a b (Deriv phi (DCP k1 g1 d1)) =
  Deriv (rn a b phi) (DCP k1 (rn a b g1) (rnD a b d1));
rnD a b (Deriv phi (DRAA k1 g1 d1)) =
  Deriv (rn a b phi) (DRAA k1 (rn a b g1) (rnD a b d1));
rnD a b (Deriv phi (DDN d1)) = Deriv (rn a b phi) (DDN (rnD a b d1));
rnD a b (Deriv phi (DBotI d1 d2)) =
  Deriv (rn a b phi) (DBotI (rnD a b d1) (rnD a b d2));
rnD a b (Deriv phi (DAndIntro d1 d2)) =
  Deriv (rn a b phi) (DAndIntro (rnD a b d1) (rnD a b d2));
rnD a b (Deriv phi (DAndElimL d1)) =
  Deriv (rn a b phi) (DAndElimL (rnD a b d1));
rnD a b (Deriv phi (DAndElimR d1)) =
  Deriv (rn a b phi) (DAndElimR (rnD a b d1));
rnD a b (Deriv phi (DOrIntroL d1)) =
  Deriv (rn a b phi) (DOrIntroL (rnD a b d1));
rnD a b (Deriv phi (DOrIntroR d1)) =
  Deriv (rn a b phi) (DOrIntroR (rnD a b d1));
rnD a b (Deriv phi (DOrElim d1 k1 g1 d2 k2 g2 d3)) =
  Deriv (rn a b phi)
    (DOrElim (rnD a b d1) k1 (rn a b g1) (rnD a b d2) k2 (rn a b g2)
      (rnD a b d3));
rnD a b (Deriv phi (DIffIntro d1 d2)) =
  Deriv (rn a b phi) (DIffIntro (rnD a b d1) (rnD a b d2));
rnD a b (Deriv phi (DIffElimL d1)) =
  Deriv (rn a b phi) (DIffElimL (rnD a b d1));
rnD a b (Deriv phi (DIffElimR d1)) =
  Deriv (rn a b phi) (DIffElimR (rnD a b d1));
rnD a b (Deriv phi (DForallElim d1)) =
  Deriv (rn a b phi) (DForallElim (rnD a b d1));
rnD a b (Deriv phi (DForallIntro d1)) =
  Deriv (rn a b phi) (DForallIntro (rnD a b d1));
rnD a b (Deriv phi (DExistsIntro d1)) =
  Deriv (rn a b phi) (DExistsIntro (rnD a b d1));
rnD a b (Deriv phi (DExistsElim d1 k1 g1 d2)) =
  Deriv (rn a b phi) (DExistsElim (rnD a b d1) k1 (rn a b g1) (rnD a b d2));
rnD a b (Deriv phi DEqIntro) = Deriv (rn a b phi) DEqIntro;
rnD a b (Deriv phi (DEqElim d1 d2)) =
  Deriv (rn a b phi) (DEqElim (rnD a b d1) (rnD a b d2));
rnD a b (Deriv phi (DReit d1)) = Deriv (rn a b phi) (DReit (rnD a b d1));

exD ::
  Nat ->
    Nat ->
      [(Nat, (Nat, Fm))] -> Fm -> Fm -> Fm -> Nat -> Deriv -> Deriv -> Deriv;
exD base cnt g ex f psi a d0 d1 = (case exRepair g ex f psi a d0 d1 of {
                                    Nothing -> d1;
                                    Just b -> rnD b (freshIdx base cnt) d1;
                                  });

exF ::
  Nat ->
    Nat -> [(Nat, (Nat, Fm))] -> Fm -> Fm -> Fm -> Nat -> Deriv -> Deriv -> Fm;
exF base cnt g ex f psi a d0 d1 = (case exRepair g ex f psi a d0 d1 of {
                                    Nothing -> f;
                                    Just b -> rn b (freshIdx base cnt) f;
                                  });

superset :: forall a. (Eq a) => [a] -> [a] -> Bool;
superset xs = all (membera xs);

map_option :: forall a b. (a -> b) -> Maybe a -> Maybe b;
map_option f Nothing = Nothing;
map_option f (Just x2) = Just (f x2);

formula :: Pline -> Fm;
formula (ProofLine x1 x2 x3 x4) = x2;

lineNumber :: Pline -> Nat;
lineNumber (ProofLine x1 x2 x3 x4) = x1;

lookupLine :: [Pline] -> Nat -> Maybe Pline;
lookupLine [] n = Nothing;
lookupLine (l : ls) n =
  (if equal_nat (lineNumber l) n then Just l else lookupLine ls n);

fmAt :: [Pline] -> Nat -> Maybe Fm;
fmAt p n = map_option formula (lookupLine p n);

dForm :: Deriv -> Fm;
dForm (Deriv x1 x2) = x1;

endsAt :: [Fitch_item] -> Nat -> Nat -> Bool;
endsAt body asmLine c =
  (if null body then equal_nat asmLine c else (case last body of {
        FLine n _ _ -> equal_nat n c;
        FSub _ -> False;
      }));

closeSub ::
  Nat -> Fm -> [Fitch_item] -> Nat -> Nat -> ([Fitch_item], (Nat, Nat));
closeSub asmLine psi body c nxt =
  (if endsAt body asmLine c then (body, (c, nxt))
    else (body ++ [FLine nxt psi (FReit c)], (nxt, suc nxt)));

envLine :: [(Nat, (Nat, Fm))] -> Nat -> Nat;
envLine g a = (case find (\ e -> equal_nat (fst e) a) g of {
                Nothing -> zero_nat;
                Just e -> fst (snd e);
              });

eigenOf :: String -> Fm -> Deriv -> Maybe String;
eigenOf x p d =
  (case filter
          (\ a ->
            not (membera (names p) a) && arbitrary_in a (map snd (openAsms d)))
          (instWitnesses x p (dForm d))
    of {
    [] -> Nothing;
    a : _ -> Just a;
  });

uniRepair :: [(Nat, (Nat, Fm))] -> Fm -> Deriv -> Maybe String;
uniRepair g phi d =
  (case phi of {
    Atom _ _ -> Nothing;
    Eqf _ _ -> Nothing;
    Bot -> Nothing;
    Neg _ -> Nothing;
    Conj _ _ -> Nothing;
    Disj _ _ -> Nothing;
    Impl _ _ -> Nothing;
    Iff _ _ -> Nothing;
    Uni x p ->
      (case eigenOf x p d of {
        Nothing -> Nothing;
        Just a -> (if arbitrary_in a (envFms g) then Nothing else Just a);
      });
    Exi _ _ -> Nothing;
  });

uniCnt :: Nat -> [(Nat, (Nat, Fm))] -> Fm -> Deriv -> Nat;
uniCnt cnt g phi d = (case uniRepair g phi d of {
                       Nothing -> cnt;
                       Just _ -> suc cnt;
                     });

exCnt ::
  Nat -> [(Nat, (Nat, Fm))] -> Fm -> Fm -> Fm -> Nat -> Deriv -> Deriv -> Nat;
exCnt cnt g ex f psi a d0 d1 = (case exRepair g ex f psi a d0 d1 of {
                                 Nothing -> cnt;
                                 Just _ -> suc cnt;
                               });

uniD :: Nat -> Nat -> [(Nat, (Nat, Fm))] -> Fm -> Deriv -> Deriv;
uniD base cnt g phi d = (case uniRepair g phi d of {
                          Nothing -> d;
                          Just a -> rnD a (freshIdx base cnt) d;
                        });

emit ::
  Nat ->
    [(Nat, (Nat, Fm))] ->
      Nat -> Nat -> Deriv -> ([Fitch_item], (Nat, (Nat, Nat)));
emit base g nx cnt (Deriv phi (DAssume a)) = ([], (envLine g a, (nx, cnt)));
emit base g nx cnt (Deriv phi (DPremise a)) = ([], (envLine g a, (nx, cnt)));
emit base g nx cnt (Deriv phi (DMP d1 d2)) =
  (case emit base g nx cnt d1 of {
    (i1, (c1, (nx1, cnt1))) ->
      (case emit base g nx1 cnt1 d2 of {
        (i2, (c2, (nx2, cnt2))) ->
          (i1 ++ i2 ++ [FLine nx2 phi (FMP c1 c2)], (nx2, (suc nx2, cnt2)));
      });
  });
emit base g nx cnt (Deriv phi (DCP a fa d1)) =
  (case emit base ((a, (nx, fa)) : g) (suc nx) cnt d1 of {
    (b1, (cc1, (nx1, cnt1))) ->
      (case closeSub nx (dForm d1) b1 cc1 nx1 of {
        (b1a, (l1, nx2)) ->
          ([FSub (Subproof nx fa b1a), FLine nx2 phi (FCP (nx, l1))],
            (nx2, (suc nx2, cnt1)));
      });
  });
emit base g nx cnt (Deriv phi (DRAA a fa d1)) =
  (case emit base ((a, (nx, fa)) : g) (suc nx) cnt d1 of {
    (b1, (cc1, (nx1, cnt1))) ->
      (case closeSub nx (dForm d1) b1 cc1 nx1 of {
        (b1a, (l1, nx2)) ->
          ([FSub (Subproof nx fa b1a), FLine nx2 phi (FRAA (nx, l1))],
            (nx2, (suc nx2, cnt1)));
      });
  });
emit base g nx cnt (Deriv phi (DDN d1)) =
  (case emit base g nx cnt d1 of {
    (i1, (c1, (nx1, cnt1))) ->
      (i1 ++ [FLine nx1 phi (FDN c1)], (nx1, (suc nx1, cnt1)));
  });
emit base g nx cnt (Deriv phi (DBotI d1 d2)) =
  (case emit base g nx cnt d1 of {
    (i1, (c1, (nx1, cnt1))) ->
      (case emit base g nx1 cnt1 d2 of {
        (i2, (c2, (nx2, cnt2))) ->
          (i1 ++ i2 ++ [FLine nx2 phi (FBotI c1 c2)], (nx2, (suc nx2, cnt2)));
      });
  });
emit base g nx cnt (Deriv phi (DAndIntro d1 d2)) =
  (case emit base g nx cnt d1 of {
    (i1, (c1, (nx1, cnt1))) ->
      (case emit base g nx1 cnt1 d2 of {
        (i2, (c2, (nx2, cnt2))) ->
          (i1 ++ i2 ++ [FLine nx2 phi (FAndIntro c1 c2)],
            (nx2, (suc nx2, cnt2)));
      });
  });
emit base g nx cnt (Deriv phi (DAndElimL d1)) =
  (case emit base g nx cnt d1 of {
    (i1, (c1, (nx1, cnt1))) ->
      (i1 ++ [FLine nx1 phi (FAndElimL c1)], (nx1, (suc nx1, cnt1)));
  });
emit base g nx cnt (Deriv phi (DAndElimR d1)) =
  (case emit base g nx cnt d1 of {
    (i1, (c1, (nx1, cnt1))) ->
      (i1 ++ [FLine nx1 phi (FAndElimR c1)], (nx1, (suc nx1, cnt1)));
  });
emit base g nx cnt (Deriv phi (DOrIntroL d1)) =
  (case emit base g nx cnt d1 of {
    (i1, (c1, (nx1, cnt1))) ->
      (i1 ++ [FLine nx1 phi (FOrIntroL c1)], (nx1, (suc nx1, cnt1)));
  });
emit base g nx cnt (Deriv phi (DOrIntroR d1)) =
  (case emit base g nx cnt d1 of {
    (i1, (c1, (nx1, cnt1))) ->
      (i1 ++ [FLine nx1 phi (FOrIntroR c1)], (nx1, (suc nx1, cnt1)));
  });
emit base g nx cnt (Deriv phi (DOrElim d0 a1 f1 d1 a2 f2 d2)) =
  (case emit base g nx cnt d0 of {
    (i0, (c0, (nx0, cnt0))) ->
      (case emit base ((a1, (nx0, f1)) : g) (suc nx0) cnt0 d1 of {
        (b1, (cc1, (nx1, cnt1))) ->
          (case closeSub nx0 (dForm d1) b1 cc1 nx1 of {
            (b1a, (l1, nx1a)) ->
              (case emit base ((a2, (nx1a, f2)) : g) (suc nx1a) cnt1 d2 of {
                (b2, (cc2, (nx2, cnt2))) ->
                  (case closeSub nx1a (dForm d2) b2 cc2 nx2 of {
                    (b2a, (l2, nx2a)) ->
                      (i0 ++ [FSub (Subproof nx0 f1 b1a),
                               FSub (Subproof nx1a f2 b2a),
                               FLine nx2a phi
                                 (FOrElim c0 (nx0, l1) (nx1a, l2))],
                        (nx2a, (suc nx2a, cnt2)));
                  });
              });
          });
      });
  });
emit base g nx cnt (Deriv phi (DIffIntro d1 d2)) =
  (case emit base g nx cnt d1 of {
    (i1, (c1, (nx1, cnt1))) ->
      (case emit base g nx1 cnt1 d2 of {
        (i2, (c2, (nx2, cnt2))) ->
          (i1 ++ i2 ++ [FLine nx2 phi (FIffIntro c1 c2)],
            (nx2, (suc nx2, cnt2)));
      });
  });
emit base g nx cnt (Deriv phi (DIffElimL d1)) =
  (case emit base g nx cnt d1 of {
    (i1, (c1, (nx1, cnt1))) ->
      (i1 ++ [FLine nx1 phi (FIffElimL c1)], (nx1, (suc nx1, cnt1)));
  });
emit base g nx cnt (Deriv phi (DIffElimR d1)) =
  (case emit base g nx cnt d1 of {
    (i1, (c1, (nx1, cnt1))) ->
      (i1 ++ [FLine nx1 phi (FIffElimR c1)], (nx1, (suc nx1, cnt1)));
  });
emit base g nx cnt (Deriv phi (DForallElim d1)) =
  (case emit base g nx cnt d1 of {
    (i1, (c1, (nx1, cnt1))) ->
      (i1 ++ [FLine nx1 phi (FForallElim c1)], (nx1, (suc nx1, cnt1)));
  });
emit base g nx cnt (Deriv phi (DForallIntro d1)) =
  (case emit base g nx (uniCnt cnt g phi d1) (uniD base cnt g phi d1) of {
    (i1, (c1, (nx1, cnt1))) ->
      (i1 ++ [FLine nx1 phi (FForallIntro c1)], (nx1, (suc nx1, cnt1)));
  });
emit base g nx cnt (Deriv phi (DExistsIntro d1)) =
  (case emit base g nx cnt d1 of {
    (i1, (c1, (nx1, cnt1))) ->
      (i1 ++ [FLine nx1 phi (FExistsIntro c1)], (nx1, (suc nx1, cnt1)));
  });
emit base g nx cnt (Deriv phi (DExistsElim d0 a f d1)) =
  (case emit base g nx cnt d0 of {
    (i0, (c0, (nx0, cnt0))) ->
      let {
        fa = exF base cnt0 g (dForm d0) f phi a d0 d1;
      } in (case emit base ((a, (nx0, fa)) : g) (suc nx0)
                   (exCnt cnt0 g (dForm d0) f phi a d0 d1)
                   (exD base cnt0 g (dForm d0) f phi a d0 d1)
             of {
             (b1, (cc1, (nx1, cnt1))) ->
               (case closeSub nx0 phi b1 cc1 nx1 of {
                 (b1a, (l1, nx2)) ->
                   (i0 ++ [FSub (Subproof nx0 fa b1a),
                            FLine nx2 phi (FExistsElim c0 (nx0, l1))],
                     (nx2, (suc nx2, cnt1)));
               });
           });
  });
emit base g nx cnt (Deriv phi DEqIntro) =
  ([FLine nx phi FEqIntro], (nx, (suc nx, cnt)));
emit base g nx cnt (Deriv phi (DEqElim d1 d2)) =
  (case emit base g nx cnt d1 of {
    (i1, (c1, (nx1, cnt1))) ->
      (case emit base g nx1 cnt1 d2 of {
        (i2, (c2, (nx2, cnt2))) ->
          (i1 ++ i2 ++ [FLine nx2 phi (FEqElim c1 c2)], (nx2, (suc nx2, cnt2)));
      });
  });
emit base g nx cnt (Deriv phi (DReit d1)) =
  (case emit base g nx cnt d1 of {
    (i1, (c1, (nx1, cnt1))) ->
      (i1 ++ [FLine nx1 phi (FReit c1)], (nx1, (suc nx1, cnt1)));
  });

enumerate :: forall a. Nat -> [a] -> [(Nat, a)];
enumerate n [] = [];
enumerate n (x : xs) = (n, x) : enumerate (suc n) xs;

is_none :: forall a. Maybe a -> Bool;
is_none Nothing = True;
is_none (Just x) = False;

flNum :: Fline -> Nat;
flNum (FL x1 x2 x3 x4) = x1;

findFL :: [Fline] -> Nat -> Maybe Fline;
findFL [] n = Nothing;
findFL (fl : fls) n =
  (if equal_nat (flNum fl) n then Just fl else findFL fls n);

length_tailrec :: forall a. [a] -> Nat -> Nat;
length_tailrec [] n = n;
length_tailrec (x : xs) n = length_tailrec xs (suc n);

size_lista :: forall a. [a] -> Nat;
size_lista xs = length_tailrec xs zero_nat;

bit_cut_integer :: Integer -> (Integer, Bool);
bit_cut_integer k =
  (if k == (0 :: Integer) then ((0 :: Integer), False)
    else (case divMod (abs k) (abs (2 :: Integer)) of {
           (r, s) ->
             ((if (0 :: Integer) < k then r else negate r - s),
               s == (1 :: Integer));
         }));

char_of_integer :: Integer -> Char;
char_of_integer k =
  (case bit_cut_integer k of {
    (q0, b0) ->
      (case bit_cut_integer q0 of {
        (q1, b1) ->
          (case bit_cut_integer q1 of {
            (q2, b2) ->
              (case bit_cut_integer q2 of {
                (q3, b3) ->
                  (case bit_cut_integer q3 of {
                    (q4, b4) ->
                      (case bit_cut_integer q4 of {
                        (q5, b5) ->
                          (case bit_cut_integer q5 of {
                            (q6, b6) ->
                              (case bit_cut_integer q6 of {
                                (_, a) -> Char b0 b1 b2 b3 b4 b5 b6 a;
                              });
                          });
                      });
                  });
              });
          });
      });
  });

explode :: String -> [Char];
explode s = map char_of_integer (Str_Literal.asciisOfLiteral s);

nlen :: String -> Nat;
nlen a = size_lista (explode a);

hlJustification :: Hl_line -> Hl_justification;
hlJustification (HL_ProofLine x1 x2 x3 x4) = x3;

hlLineNumber :: Hl_line -> Int;
hlLineNumber (HL_ProofLine x1 x2 x3 x4) = x1;

hlCitedLines :: Hl_justification -> [Int];
hlCitedLines HL_Assumption = [];
hlCitedLines (HL_MP m n) = [m, n];
hlCitedLines (HL_MT m n) = [m, n];
hlCitedLines (HL_DN m) = [m];
hlCitedLines (HL_CP m n) = [m, n];
hlCitedLines (HL_AndIntro m n) = [m, n];
hlCitedLines (HL_AndElim m) = [m];
hlCitedLines (HL_OrIntro m) = [m];
hlCitedLines (HL_OrElim d a1 c1 a2 c2) = [d, a1, c1, a2, c2];
hlCitedLines (HL_RAA a c) = [a, c];
hlCitedLines (HL_ForallElim m) = [m];
hlCitedLines (HL_ExistsIntro m) = [m];
hlCitedLines (HL_ForallIntro m) = [m];
hlCitedLines (HL_ExistsElim m a c) = [m, a, c];
hlCitedLines HL_EqIntro = [];
hlCitedLines (HL_EqElim m n) = [m, n];
hlCitedLines HL_LEM = [];
hlCitedLines (HL_PropTaut ms) = ms;
hlCitedLines (HL_IffIntro m n) = [m, n];
hlCitedLines (HL_IffElim m n) = [m, n];
hlCitedLines (HL_QN m) = [m];

hlStructureOK :: [Hl_line] -> Hl_line -> Bool;
hlStructureOK p l =
  equal_nat
    (size_lista (filter (\ k -> equal_int (hlLineNumber k) (hlLineNumber l)) p))
    one_nat &&
    all (\ m -> less_int m (hlLineNumber l)) (hlCitedLines (hlJustification l));

hlQuantifierNegationForms :: Hl_formula -> [Hl_formula];
hlQuantifierNegationForms (HL_Not (HL_ForAll x p)) =
  HL_Not (HL_ForAll x p) :
    map (HL_Exists x) (hlQuantifierNegationForms (HL_Not p));
hlQuantifierNegationForms (HL_Not (HL_Exists x p)) =
  HL_Not (HL_Exists x p) :
    map (HL_ForAll x) (hlQuantifierNegationForms (HL_Not p));
hlQuantifierNegationForms (HL_ForAll x p) =
  map (HL_ForAll x) (hlQuantifierNegationForms p);
hlQuantifierNegationForms (HL_Exists x p) =
  map (HL_Exists x) (hlQuantifierNegationForms p);
hlQuantifierNegationForms (HL_Predicate v va) = [HL_Predicate v va];
hlQuantifierNegationForms (HL_Boolean v) = [HL_Boolean v];
hlQuantifierNegationForms (HL_Not (HL_Predicate va vb)) =
  [HL_Not (HL_Predicate va vb)];
hlQuantifierNegationForms (HL_Not (HL_Boolean va)) = [HL_Not (HL_Boolean va)];
hlQuantifierNegationForms (HL_Not (HL_Not va)) = [HL_Not (HL_Not va)];
hlQuantifierNegationForms (HL_Not (HL_And va vb)) = [HL_Not (HL_And va vb)];
hlQuantifierNegationForms (HL_Not (HL_Or va vb)) = [HL_Not (HL_Or va vb)];
hlQuantifierNegationForms (HL_Not (HL_Implies va vb)) =
  [HL_Not (HL_Implies va vb)];
hlQuantifierNegationForms (HL_Not (HL_Iff va vb)) = [HL_Not (HL_Iff va vb)];
hlQuantifierNegationForms (HL_And v va) = [HL_And v va];
hlQuantifierNegationForms (HL_Or v va) = [HL_Or v va];
hlQuantifierNegationForms (HL_Implies v va) = [HL_Implies v va];
hlQuantifierNegationForms (HL_Iff v va) = [HL_Iff v va];

hlQuantifierNegationReachable :: Hl_formula -> Hl_formula -> Bool;
hlQuantifierNegationReachable p q =
  (case p of {
    HL_Predicate _ _ -> False;
    HL_Boolean _ -> False;
    HL_Not _ -> membera (hlQuantifierNegationForms p) q;
    HL_And _ _ -> False;
    HL_Or _ _ -> False;
    HL_Implies _ _ -> False;
    HL_Iff _ _ -> False;
    HL_ForAll _ _ -> False;
    HL_Exists _ _ -> False;
  });

hlQuantifierNegationEquivalent :: Hl_formula -> Hl_formula -> Bool;
hlQuantifierNegationEquivalent p q =
  hlQuantifierNegationReachable p q || hlQuantifierNegationReachable q p;

hlTermEqualUpToConstantReplacement ::
  String -> String -> Hl_term -> Hl_term -> Bool;
hlTermEqualUpToConstantReplacement a b (HL_Var x) (HL_Var y) = x == y;
hlTermEqualUpToConstantReplacement a b (HL_Const c) (HL_Const d) =
  c == a && d == b || c == d;
hlTermEqualUpToConstantReplacement a b (HL_Const v) (HL_Var va) = False;
hlTermEqualUpToConstantReplacement a b (HL_Var va) (HL_Const v) = False;

list_all2 :: forall a b. (a -> b -> Bool) -> [a] -> [b] -> Bool;
list_all2 p [] ys = null ys;
list_all2 p xs [] = null xs;
list_all2 p (x : xs) (y : ys) = p x y && list_all2 p xs ys;

hlEqualUpToConstantReplacement ::
  String -> String -> Hl_formula -> Hl_formula -> Bool;
hlEqualUpToConstantReplacement a b p q =
  (case p of {
    HL_Predicate pa ts ->
      (case q of {
        HL_Predicate qa us ->
          pa == qa && list_all2 (hlTermEqualUpToConstantReplacement a b) ts us;
        HL_Boolean _ -> False;
        HL_Not _ -> False;
        HL_And _ _ -> False;
        HL_Or _ _ -> False;
        HL_Implies _ _ -> False;
        HL_Iff _ _ -> False;
        HL_ForAll _ _ -> False;
        HL_Exists _ _ -> False;
      });
    HL_Boolean c -> (case q of {
                      HL_Predicate _ _ -> False;
                      HL_Boolean aa -> c == aa;
                      HL_Not _ -> False;
                      HL_And _ _ -> False;
                      HL_Or _ _ -> False;
                      HL_Implies _ _ -> False;
                      HL_Iff _ _ -> False;
                      HL_ForAll _ _ -> False;
                      HL_Exists _ _ -> False;
                    });
    HL_Not r -> (case q of {
                  HL_Predicate _ _ -> False;
                  HL_Boolean _ -> False;
                  HL_Not c -> hlEqualUpToConstantReplacement a b r c;
                  HL_And _ _ -> False;
                  HL_Or _ _ -> False;
                  HL_Implies _ _ -> False;
                  HL_Iff _ _ -> False;
                  HL_ForAll _ _ -> False;
                  HL_Exists _ _ -> False;
                });
    HL_And r s ->
      (case q of {
        HL_Predicate _ _ -> False;
        HL_Boolean _ -> False;
        HL_Not _ -> False;
        HL_And u v ->
          hlEqualUpToConstantReplacement a b r u &&
            hlEqualUpToConstantReplacement a b s v;
        HL_Or _ _ -> False;
        HL_Implies _ _ -> False;
        HL_Iff _ _ -> False;
        HL_ForAll _ _ -> False;
        HL_Exists _ _ -> False;
      });
    HL_Or r s ->
      (case q of {
        HL_Predicate _ _ -> False;
        HL_Boolean _ -> False;
        HL_Not _ -> False;
        HL_And _ _ -> False;
        HL_Or u v ->
          hlEqualUpToConstantReplacement a b r u &&
            hlEqualUpToConstantReplacement a b s v;
        HL_Implies _ _ -> False;
        HL_Iff _ _ -> False;
        HL_ForAll _ _ -> False;
        HL_Exists _ _ -> False;
      });
    HL_Implies r s ->
      (case q of {
        HL_Predicate _ _ -> False;
        HL_Boolean _ -> False;
        HL_Not _ -> False;
        HL_And _ _ -> False;
        HL_Or _ _ -> False;
        HL_Implies u v ->
          hlEqualUpToConstantReplacement a b r u &&
            hlEqualUpToConstantReplacement a b s v;
        HL_Iff _ _ -> False;
        HL_ForAll _ _ -> False;
        HL_Exists _ _ -> False;
      });
    HL_Iff r s ->
      (case q of {
        HL_Predicate _ _ -> False;
        HL_Boolean _ -> False;
        HL_Not _ -> False;
        HL_And _ _ -> False;
        HL_Or _ _ -> False;
        HL_Implies _ _ -> False;
        HL_Iff u v ->
          hlEqualUpToConstantReplacement a b r u &&
            hlEqualUpToConstantReplacement a b s v;
        HL_ForAll _ _ -> False;
        HL_Exists _ _ -> False;
      });
    HL_ForAll x r ->
      (case q of {
        HL_Predicate _ _ -> False;
        HL_Boolean _ -> False;
        HL_Not _ -> False;
        HL_And _ _ -> False;
        HL_Or _ _ -> False;
        HL_Implies _ _ -> False;
        HL_Iff _ _ -> False;
        HL_ForAll y s -> x == y && hlEqualUpToConstantReplacement a b r s;
        HL_Exists _ _ -> False;
      });
    HL_Exists x r ->
      (case q of {
        HL_Predicate _ _ -> False;
        HL_Boolean _ -> False;
        HL_Not _ -> False;
        HL_And _ _ -> False;
        HL_Or _ _ -> False;
        HL_Implies _ _ -> False;
        HL_Iff _ _ -> False;
        HL_ForAll _ _ -> False;
        HL_Exists y s -> x == y && hlEqualUpToConstantReplacement a b r s;
      });
  });

insort_key :: forall a b. (Linorder b) => (a -> b) -> a -> [a] -> [a];
insort_key f x [] = [x];
insort_key f x (y : ys) =
  (if less_eq (f x) (f y) then x : y : ys else y : insort_key f x ys);

sort_key :: forall a b. (Linorder b) => (a -> b) -> [a] -> [a];
sort_key f xs = foldr (insort_key f) xs [];

sorted_list_of_set :: forall a. (Eq a, Linorder a) => Set a -> [a];
sorted_list_of_set (Set xs) = sort_key (\ x -> x) (remdups xs);

sup_set :: forall a. (Eq a) => Set a -> Set a -> Set a;
sup_set (Set xs) a = fold insert xs a;
sup_set (Coset xs) a = Coset (filter (\ x -> not (member x a)) xs);

bot_set :: forall a. Set a;
bot_set = Set [];

sup_seta :: forall a. (Eq a) => Set (Set a) -> Set a;
sup_seta (Set xs) = fold sup_set xs bot_set;

hlConstantsInTerm :: Hl_term -> Set String;
hlConstantsInTerm (HL_Var uu) = bot_set;
hlConstantsInTerm (HL_Const a) = insert a bot_set;

hlConstantsInFormula :: Hl_formula -> Set String;
hlConstantsInFormula (HL_Predicate uu ts) =
  sup_seta (image hlConstantsInTerm (Set ts));
hlConstantsInFormula (HL_Boolean uv) = bot_set;
hlConstantsInFormula (HL_Not p) = hlConstantsInFormula p;
hlConstantsInFormula (HL_And p q) =
  sup_set (hlConstantsInFormula p) (hlConstantsInFormula q);
hlConstantsInFormula (HL_Or p q) =
  sup_set (hlConstantsInFormula p) (hlConstantsInFormula q);
hlConstantsInFormula (HL_Implies p q) =
  sup_set (hlConstantsInFormula p) (hlConstantsInFormula q);
hlConstantsInFormula (HL_Iff p q) =
  sup_set (hlConstantsInFormula p) (hlConstantsInFormula q);
hlConstantsInFormula (HL_ForAll uw p) = hlConstantsInFormula p;
hlConstantsInFormula (HL_Exists ux p) = hlConstantsInFormula p;

hlSubstituteTerm :: String -> Hl_term -> Hl_term -> Hl_term;
hlSubstituteTerm x t (HL_Var y) = (if x == y then t else HL_Var y);
hlSubstituteTerm x t (HL_Const a) = HL_Const a;

hlSubstituteFree :: String -> Hl_term -> Hl_formula -> Hl_formula;
hlSubstituteFree x t (HL_Predicate p ts) =
  HL_Predicate p (map (hlSubstituteTerm x t) ts);
hlSubstituteFree x t (HL_Boolean b) = HL_Boolean b;
hlSubstituteFree x t (HL_Not p) = HL_Not (hlSubstituteFree x t p);
hlSubstituteFree x t (HL_And p q) =
  HL_And (hlSubstituteFree x t p) (hlSubstituteFree x t q);
hlSubstituteFree x t (HL_Or p q) =
  HL_Or (hlSubstituteFree x t p) (hlSubstituteFree x t q);
hlSubstituteFree x t (HL_Implies p q) =
  HL_Implies (hlSubstituteFree x t p) (hlSubstituteFree x t q);
hlSubstituteFree x t (HL_Iff p q) =
  HL_Iff (hlSubstituteFree x t p) (hlSubstituteFree x t q);
hlSubstituteFree x t (HL_ForAll y p) =
  HL_ForAll y (if x == y then p else hlSubstituteFree x t p);
hlSubstituteFree x t (HL_Exists y p) =
  HL_Exists y (if x == y then p else hlSubstituteFree x t p);

hlVariablesInTerm :: Hl_term -> Set String;
hlVariablesInTerm (HL_Var x) = insert x bot_set;
hlVariablesInTerm (HL_Const uu) = bot_set;

hlFreeVariables :: Hl_formula -> Set String;
hlFreeVariables (HL_Predicate uu ts) =
  sup_seta (image hlVariablesInTerm (Set ts));
hlFreeVariables (HL_Boolean uv) = bot_set;
hlFreeVariables (HL_Not p) = hlFreeVariables p;
hlFreeVariables (HL_And p q) = sup_set (hlFreeVariables p) (hlFreeVariables q);
hlFreeVariables (HL_Or p q) = sup_set (hlFreeVariables p) (hlFreeVariables q);
hlFreeVariables (HL_Implies p q) =
  sup_set (hlFreeVariables p) (hlFreeVariables q);
hlFreeVariables (HL_Iff p q) = sup_set (hlFreeVariables p) (hlFreeVariables q);
hlFreeVariables (HL_ForAll x p) = remove x (hlFreeVariables p);
hlFreeVariables (HL_Exists x p) = remove x (hlFreeVariables p);

hlWitnessLists :: [String] -> Hl_formula -> Hl_formula -> [[String]];
hlWitnessLists [] p q = (if equal_hl_formula p q then [[]] else []);
hlWitnessLists (x : xs) p q =
  (if not (member x (hlFreeVariables p))
    then map (\ a -> "" : a) (hlWitnessLists xs p q)
    else concatMap
           (\ a ->
             map (\ b -> a : b)
               (hlWitnessLists xs (hlSubstituteFree x (HL_Const a) p) q))
           (sorted_list_of_set (hlConstantsInFormula q)));

hlInferWitnessConstsK ::
  [String] -> Hl_formula -> Nat -> Hl_formula -> Maybe [String];
hlInferWitnessConstsK xs p k q =
  let {
    candidates = hlWitnessLists (take k xs) p q;
  } in (if null candidates then Nothing else Just (last candidates));

hlEliminationCount :: [String] -> [String] -> Maybe Nat;
hlEliminationCount source destination =
  let {
    k = minus_nat (size_lista source) (size_lista destination);
  } in (if less_eq_nat (size_lista destination) (size_lista source) &&
             drop k source == destination
         then Just k else Nothing);

hlPropositionalValue :: (Hl_formula -> Bool) -> Hl_formula -> Bool;
hlPropositionalValue v (HL_Boolean b) = b;
hlPropositionalValue v (HL_Not p) = not (hlPropositionalValue v p);
hlPropositionalValue v (HL_And p q) =
  hlPropositionalValue v p && hlPropositionalValue v q;
hlPropositionalValue v (HL_Or p q) =
  hlPropositionalValue v p || hlPropositionalValue v q;
hlPropositionalValue v (HL_Implies p q) =
  (if hlPropositionalValue v p then hlPropositionalValue v q else True);
hlPropositionalValue v (HL_Iff p q) =
  hlPropositionalValue v p == hlPropositionalValue v q;
hlPropositionalValue v (HL_Predicate va vb) = v (HL_Predicate va vb);
hlPropositionalValue v (HL_ForAll va vb) = v (HL_ForAll va vb);
hlPropositionalValue v (HL_Exists va vb) = v (HL_Exists va vb);

hlPropositionalAtoms :: Hl_formula -> [Hl_formula];
hlPropositionalAtoms (HL_Predicate p ts) = [HL_Predicate p ts];
hlPropositionalAtoms (HL_Boolean uu) = [];
hlPropositionalAtoms (HL_Not p) = hlPropositionalAtoms p;
hlPropositionalAtoms (HL_And p q) =
  hlPropositionalAtoms p ++ hlPropositionalAtoms q;
hlPropositionalAtoms (HL_Or p q) =
  hlPropositionalAtoms p ++ hlPropositionalAtoms q;
hlPropositionalAtoms (HL_Implies p q) =
  hlPropositionalAtoms p ++ hlPropositionalAtoms q;
hlPropositionalAtoms (HL_Iff p q) =
  hlPropositionalAtoms p ++ hlPropositionalAtoms q;
hlPropositionalAtoms (HL_ForAll v va) = [HL_ForAll v va];
hlPropositionalAtoms (HL_Exists v va) = [HL_Exists v va];

hlValuations :: [Hl_formula] -> [Hl_formula -> Bool];
hlValuations [] = [(\ _ -> False)];
hlValuations (p : ps) =
  map (\ v -> fun_upd v p False) (hlValuations ps) ++
    map (\ v -> fun_upd v p True) (hlValuations ps);

hlPropositionalConsequence :: [Hl_formula] -> Hl_formula -> Bool;
hlPropositionalConsequence premises conclusion =
  let {
    atoms = remdups (concatMap hlPropositionalAtoms (conclusion : premises));
  } in all (\ v ->
             (if all (hlPropositionalValue v) premises
               then hlPropositionalValue v conclusion else True))
         (hlValuations atoms);

hlEqualityFormula :: Hl_formula -> Maybe (Hl_term, Hl_term);
hlEqualityFormula (HL_Predicate p [t, u]) =
  (if p == "=" then Just (t, u) else Nothing);
hlEqualityFormula (HL_Predicate v []) = Nothing;
hlEqualityFormula (HL_Predicate v [vb]) = Nothing;
hlEqualityFormula (HL_Predicate v (vb : vd : vf : vg)) = Nothing;
hlEqualityFormula (HL_Boolean v) = Nothing;
hlEqualityFormula (HL_Not v) = Nothing;
hlEqualityFormula (HL_And v va) = Nothing;
hlEqualityFormula (HL_Or v va) = Nothing;
hlEqualityFormula (HL_Implies v va) = Nothing;
hlEqualityFormula (HL_Iff v va) = Nothing;
hlEqualityFormula (HL_ForAll v va) = Nothing;
hlEqualityFormula (HL_Exists v va) = Nothing;

hlCollectForalls :: Hl_formula -> ([String], Hl_formula);
hlCollectForalls (HL_ForAll x p) = (case hlCollectForalls p of {
                                     (xs, a) -> (x : xs, a);
                                   });
hlCollectForalls (HL_Predicate v va) = ([], HL_Predicate v va);
hlCollectForalls (HL_Boolean v) = ([], HL_Boolean v);
hlCollectForalls (HL_Not v) = ([], HL_Not v);
hlCollectForalls (HL_And v va) = ([], HL_And v va);
hlCollectForalls (HL_Or v va) = ([], HL_Or v va);
hlCollectForalls (HL_Implies v va) = ([], HL_Implies v va);
hlCollectForalls (HL_Iff v va) = ([], HL_Iff v va);
hlCollectForalls (HL_Exists v va) = ([], HL_Exists v va);

hlCollectExists :: Hl_formula -> ([String], Hl_formula);
hlCollectExists (HL_Exists x p) = (case hlCollectExists p of {
                                    (xs, a) -> (x : xs, a);
                                  });
hlCollectExists (HL_Predicate v va) = ([], HL_Predicate v va);
hlCollectExists (HL_Boolean v) = ([], HL_Boolean v);
hlCollectExists (HL_Not v) = ([], HL_Not v);
hlCollectExists (HL_And v va) = ([], HL_And v va);
hlCollectExists (HL_Or v va) = ([], HL_Or v va);
hlCollectExists (HL_Implies v va) = ([], HL_Implies v va);
hlCollectExists (HL_Iff v va) = ([], HL_Iff v va);
hlCollectExists (HL_ForAll v va) = ([], HL_ForAll v va);

hlPrefixExists :: [String] -> Hl_formula -> Hl_formula;
hlPrefixExists xs p = foldr HL_Exists xs p;

hlReplaceConstantInTerm :: String -> String -> Hl_term -> Hl_term;
hlReplaceConstantInTerm a x (HL_Const b) =
  (if a == b then HL_Var x else HL_Const b);
hlReplaceConstantInTerm a x (HL_Var y) = HL_Var y;

hlAbstractConstantFree :: String -> String -> Hl_formula -> Maybe Hl_formula;
hlAbstractConstantFree a x (HL_Predicate p ts) =
  Just (HL_Predicate p (map (hlReplaceConstantInTerm a x) ts));
hlAbstractConstantFree a x (HL_Boolean b) = Just (HL_Boolean b);
hlAbstractConstantFree a x (HL_Not p) =
  map_option HL_Not (hlAbstractConstantFree a x p);
hlAbstractConstantFree a x (HL_And p q) =
  (case (hlAbstractConstantFree a x p, hlAbstractConstantFree a x q) of {
    (Nothing, _) -> Nothing;
    (Just _, Nothing) -> Nothing;
    (Just r, Just s) -> Just (HL_And r s);
  });
hlAbstractConstantFree a x (HL_Or p q) =
  (case (hlAbstractConstantFree a x p, hlAbstractConstantFree a x q) of {
    (Nothing, _) -> Nothing;
    (Just _, Nothing) -> Nothing;
    (Just r, Just s) -> Just (HL_Or r s);
  });
hlAbstractConstantFree a x (HL_Implies p q) =
  (case (hlAbstractConstantFree a x p, hlAbstractConstantFree a x q) of {
    (Nothing, _) -> Nothing;
    (Just _, Nothing) -> Nothing;
    (Just r, Just s) -> Just (HL_Implies r s);
  });
hlAbstractConstantFree a x (HL_Iff p q) =
  (case (hlAbstractConstantFree a x p, hlAbstractConstantFree a x q) of {
    (Nothing, _) -> Nothing;
    (Just _, Nothing) -> Nothing;
    (Just r, Just s) -> Just (HL_Iff r s);
  });
hlAbstractConstantFree a x (HL_ForAll y p) =
  (if y == x then Nothing
    else map_option (HL_ForAll y) (hlAbstractConstantFree a x p));
hlAbstractConstantFree a x (HL_Exists y p) =
  (if y == x then Nothing
    else map_option (HL_Exists y) (hlAbstractConstantFree a x p));

hlAbstractMany :: [(String, String)] -> Hl_formula -> Maybe Hl_formula;
hlAbstractMany [] p = Just p;
hlAbstractMany ((x, a) : ps) p = (case hlAbstractConstantFree a x p of {
                                   Nothing -> Nothing;
                                   Just aa -> hlAbstractMany ps aa;
                                 });

less_eq_set :: forall a. (Eq a) => Set a -> Set a -> Bool;
less_eq_set (Set xs) b = all (\ x -> member x b) xs;
less_eq_set a (Coset ys) = all (\ y -> not (member y a)) ys;
less_eq_set (Coset []) (Set []) = False;

equal_set :: forall a. (Eq a) => Set a -> Set a -> Bool;
equal_set a b = less_eq_set a b && less_eq_set b a;

hlFormula :: Hl_line -> Hl_formula;
hlFormula (HL_ProofLine x1 x2 x3 x4) = x2;

hlReferencedConstants :: [Hl_line] -> Set Int -> Set String;
hlReferencedConstants p g =
  sup_seta
    (image hlConstantsInFormula
      (image hlFormula (Set (filter (\ l -> member (hlLineNumber l) g) p))));

hlAssumptionConstants :: [Hl_line] -> Set Int -> Set String;
hlAssumptionConstants p g =
  sup_seta
    (image hlConstantsInFormula
      (image hlFormula
        (Set (filter
               (\ l ->
                 member (hlLineNumber l) g &&
                   equal_hl_justification (hlJustification l) HL_Assumption)
               p))));

hlReferences :: Hl_line -> Set Int;
hlReferences (HL_ProofLine x1 x2 x3 x4) = x4;

hlLookupLine :: [Hl_line] -> Int -> Maybe Hl_line;
hlLookupLine [] n = Nothing;
hlLookupLine (l : ls) n =
  (if equal_int (hlLineNumber l) n then Just l else hlLookupLine ls n);

hlReferencesAt :: [Hl_line] -> Int -> Maybe (Set Int);
hlReferencesAt p n = map_option hlReferences (hlLookupLine p n);

hlMapFilter :: forall a b. (a -> Maybe b) -> [a] -> [b];
hlMapFilter f [] = [];
hlMapFilter f (x : xs) = (case f x of {
                           Nothing -> hlMapFilter f xs;
                           Just y -> y : hlMapFilter f xs;
                         });

hlReferenceUnion :: [Hl_line] -> [Int] -> Set Int;
hlReferenceUnion p ns = sup_seta (Set (hlMapFilter (hlReferencesAt p) ns));

hlExcludedMiddle :: Hl_formula -> Bool;
hlExcludedMiddle p =
  (case p of {
    HL_Predicate _ _ -> False;
    HL_Boolean _ -> False;
    HL_Not _ -> False;
    HL_And _ _ -> False;
    HL_Or (HL_Predicate _ _) (HL_Predicate _ _) -> False;
    HL_Or (HL_Predicate _ _) (HL_Boolean _) -> False;
    HL_Or (HL_Predicate literal list) (HL_Not a) ->
      equal_hl_formula (HL_Predicate literal list) a;
    HL_Or (HL_Predicate _ _) (HL_And _ _) -> False;
    HL_Or (HL_Predicate _ _) (HL_Or _ _) -> False;
    HL_Or (HL_Predicate _ _) (HL_Implies _ _) -> False;
    HL_Or (HL_Predicate _ _) (HL_Iff _ _) -> False;
    HL_Or (HL_Predicate _ _) (HL_ForAll _ _) -> False;
    HL_Or (HL_Predicate _ _) (HL_Exists _ _) -> False;
    HL_Or (HL_Boolean _) (HL_Predicate _ _) -> False;
    HL_Or (HL_Boolean _) (HL_Boolean _) -> False;
    HL_Or (HL_Boolean bool) (HL_Not a) -> equal_hl_formula (HL_Boolean bool) a;
    HL_Or (HL_Boolean _) (HL_And _ _) -> False;
    HL_Or (HL_Boolean _) (HL_Or _ _) -> False;
    HL_Or (HL_Boolean _) (HL_Implies _ _) -> False;
    HL_Or (HL_Boolean _) (HL_Iff _ _) -> False;
    HL_Or (HL_Boolean _) (HL_ForAll _ _) -> False;
    HL_Or (HL_Boolean _) (HL_Exists _ _) -> False;
    HL_Or (HL_Not hl_formula) (HL_Predicate literal list) ->
      equal_hl_formula hl_formula (HL_Predicate literal list);
    HL_Or (HL_Not hl_formula) (HL_Boolean bool) ->
      equal_hl_formula hl_formula (HL_Boolean bool);
    HL_Or (HL_Not hl_formula) (HL_Not a) ->
      equal_hl_formula (HL_Not hl_formula) a;
    HL_Or (HL_Not hl_formula) (HL_And hl_formula1 hl_formula2) ->
      equal_hl_formula hl_formula (HL_And hl_formula1 hl_formula2);
    HL_Or (HL_Not hl_formula) (HL_Or hl_formula1 hl_formula2) ->
      equal_hl_formula hl_formula (HL_Or hl_formula1 hl_formula2);
    HL_Or (HL_Not hl_formula) (HL_Implies hl_formula1 hl_formula2) ->
      equal_hl_formula hl_formula (HL_Implies hl_formula1 hl_formula2);
    HL_Or (HL_Not hl_formula) (HL_Iff hl_formula1 hl_formula2) ->
      equal_hl_formula hl_formula (HL_Iff hl_formula1 hl_formula2);
    HL_Or (HL_Not hl_formula) (HL_ForAll literal hl_formulaa) ->
      equal_hl_formula hl_formula (HL_ForAll literal hl_formulaa);
    HL_Or (HL_Not hl_formula) (HL_Exists literal hl_formulaa) ->
      equal_hl_formula hl_formula (HL_Exists literal hl_formulaa);
    HL_Or (HL_And _ _) (HL_Predicate _ _) -> False;
    HL_Or (HL_And _ _) (HL_Boolean _) -> False;
    HL_Or (HL_And hl_formula1 hl_formula2) (HL_Not a) ->
      equal_hl_formula (HL_And hl_formula1 hl_formula2) a;
    HL_Or (HL_And _ _) (HL_And _ _) -> False;
    HL_Or (HL_And _ _) (HL_Or _ _) -> False;
    HL_Or (HL_And _ _) (HL_Implies _ _) -> False;
    HL_Or (HL_And _ _) (HL_Iff _ _) -> False;
    HL_Or (HL_And _ _) (HL_ForAll _ _) -> False;
    HL_Or (HL_And _ _) (HL_Exists _ _) -> False;
    HL_Or (HL_Or _ _) (HL_Predicate _ _) -> False;
    HL_Or (HL_Or _ _) (HL_Boolean _) -> False;
    HL_Or (HL_Or hl_formula1 hl_formula2) (HL_Not a) ->
      equal_hl_formula (HL_Or hl_formula1 hl_formula2) a;
    HL_Or (HL_Or _ _) (HL_And _ _) -> False;
    HL_Or (HL_Or _ _) (HL_Or _ _) -> False;
    HL_Or (HL_Or _ _) (HL_Implies _ _) -> False;
    HL_Or (HL_Or _ _) (HL_Iff _ _) -> False;
    HL_Or (HL_Or _ _) (HL_ForAll _ _) -> False;
    HL_Or (HL_Or _ _) (HL_Exists _ _) -> False;
    HL_Or (HL_Implies _ _) (HL_Predicate _ _) -> False;
    HL_Or (HL_Implies _ _) (HL_Boolean _) -> False;
    HL_Or (HL_Implies hl_formula1 hl_formula2) (HL_Not a) ->
      equal_hl_formula (HL_Implies hl_formula1 hl_formula2) a;
    HL_Or (HL_Implies _ _) (HL_And _ _) -> False;
    HL_Or (HL_Implies _ _) (HL_Or _ _) -> False;
    HL_Or (HL_Implies _ _) (HL_Implies _ _) -> False;
    HL_Or (HL_Implies _ _) (HL_Iff _ _) -> False;
    HL_Or (HL_Implies _ _) (HL_ForAll _ _) -> False;
    HL_Or (HL_Implies _ _) (HL_Exists _ _) -> False;
    HL_Or (HL_Iff _ _) (HL_Predicate _ _) -> False;
    HL_Or (HL_Iff _ _) (HL_Boolean _) -> False;
    HL_Or (HL_Iff hl_formula1 hl_formula2) (HL_Not a) ->
      equal_hl_formula (HL_Iff hl_formula1 hl_formula2) a;
    HL_Or (HL_Iff _ _) (HL_And _ _) -> False;
    HL_Or (HL_Iff _ _) (HL_Or _ _) -> False;
    HL_Or (HL_Iff _ _) (HL_Implies _ _) -> False;
    HL_Or (HL_Iff _ _) (HL_Iff _ _) -> False;
    HL_Or (HL_Iff _ _) (HL_ForAll _ _) -> False;
    HL_Or (HL_Iff _ _) (HL_Exists _ _) -> False;
    HL_Or (HL_ForAll _ _) (HL_Predicate _ _) -> False;
    HL_Or (HL_ForAll _ _) (HL_Boolean _) -> False;
    HL_Or (HL_ForAll literal hl_formula) (HL_Not a) ->
      equal_hl_formula (HL_ForAll literal hl_formula) a;
    HL_Or (HL_ForAll _ _) (HL_And _ _) -> False;
    HL_Or (HL_ForAll _ _) (HL_Or _ _) -> False;
    HL_Or (HL_ForAll _ _) (HL_Implies _ _) -> False;
    HL_Or (HL_ForAll _ _) (HL_Iff _ _) -> False;
    HL_Or (HL_ForAll _ _) (HL_ForAll _ _) -> False;
    HL_Or (HL_ForAll _ _) (HL_Exists _ _) -> False;
    HL_Or (HL_Exists _ _) (HL_Predicate _ _) -> False;
    HL_Or (HL_Exists _ _) (HL_Boolean _) -> False;
    HL_Or (HL_Exists literal hl_formula) (HL_Not a) ->
      equal_hl_formula (HL_Exists literal hl_formula) a;
    HL_Or (HL_Exists _ _) (HL_And _ _) -> False;
    HL_Or (HL_Exists _ _) (HL_Or _ _) -> False;
    HL_Or (HL_Exists _ _) (HL_Implies _ _) -> False;
    HL_Or (HL_Exists _ _) (HL_Iff _ _) -> False;
    HL_Or (HL_Exists _ _) (HL_ForAll _ _) -> False;
    HL_Or (HL_Exists _ _) (HL_Exists _ _) -> False;
    HL_Implies _ _ -> False;
    HL_Iff _ _ -> False;
    HL_ForAll _ _ -> False;
    HL_Exists _ _ -> False;
  });

hlContradiction :: Hl_formula -> Bool;
hlContradiction p =
  (case p of {
    HL_Predicate _ _ -> False;
    HL_Boolean _ -> False;
    HL_Not _ -> False;
    HL_And (HL_Predicate _ _) (HL_Predicate _ _) -> False;
    HL_And (HL_Predicate _ _) (HL_Boolean _) -> False;
    HL_And (HL_Predicate literal list) (HL_Not a) ->
      equal_hl_formula (HL_Predicate literal list) a;
    HL_And (HL_Predicate _ _) (HL_And _ _) -> False;
    HL_And (HL_Predicate _ _) (HL_Or _ _) -> False;
    HL_And (HL_Predicate _ _) (HL_Implies _ _) -> False;
    HL_And (HL_Predicate _ _) (HL_Iff _ _) -> False;
    HL_And (HL_Predicate _ _) (HL_ForAll _ _) -> False;
    HL_And (HL_Predicate _ _) (HL_Exists _ _) -> False;
    HL_And (HL_Boolean _) (HL_Predicate _ _) -> False;
    HL_And (HL_Boolean _) (HL_Boolean _) -> False;
    HL_And (HL_Boolean bool) (HL_Not a) -> equal_hl_formula (HL_Boolean bool) a;
    HL_And (HL_Boolean _) (HL_And _ _) -> False;
    HL_And (HL_Boolean _) (HL_Or _ _) -> False;
    HL_And (HL_Boolean _) (HL_Implies _ _) -> False;
    HL_And (HL_Boolean _) (HL_Iff _ _) -> False;
    HL_And (HL_Boolean _) (HL_ForAll _ _) -> False;
    HL_And (HL_Boolean _) (HL_Exists _ _) -> False;
    HL_And (HL_Not hl_formula) (HL_Predicate literal list) ->
      equal_hl_formula hl_formula (HL_Predicate literal list);
    HL_And (HL_Not hl_formula) (HL_Boolean bool) ->
      equal_hl_formula hl_formula (HL_Boolean bool);
    HL_And (HL_Not hl_formula) (HL_Not a) ->
      equal_hl_formula (HL_Not hl_formula) a;
    HL_And (HL_Not hl_formula) (HL_And hl_formula1 hl_formula2) ->
      equal_hl_formula hl_formula (HL_And hl_formula1 hl_formula2);
    HL_And (HL_Not hl_formula) (HL_Or hl_formula1 hl_formula2) ->
      equal_hl_formula hl_formula (HL_Or hl_formula1 hl_formula2);
    HL_And (HL_Not hl_formula) (HL_Implies hl_formula1 hl_formula2) ->
      equal_hl_formula hl_formula (HL_Implies hl_formula1 hl_formula2);
    HL_And (HL_Not hl_formula) (HL_Iff hl_formula1 hl_formula2) ->
      equal_hl_formula hl_formula (HL_Iff hl_formula1 hl_formula2);
    HL_And (HL_Not hl_formula) (HL_ForAll literal hl_formulaa) ->
      equal_hl_formula hl_formula (HL_ForAll literal hl_formulaa);
    HL_And (HL_Not hl_formula) (HL_Exists literal hl_formulaa) ->
      equal_hl_formula hl_formula (HL_Exists literal hl_formulaa);
    HL_And (HL_And _ _) (HL_Predicate _ _) -> False;
    HL_And (HL_And _ _) (HL_Boolean _) -> False;
    HL_And (HL_And hl_formula1 hl_formula2) (HL_Not a) ->
      equal_hl_formula (HL_And hl_formula1 hl_formula2) a;
    HL_And (HL_And _ _) (HL_And _ _) -> False;
    HL_And (HL_And _ _) (HL_Or _ _) -> False;
    HL_And (HL_And _ _) (HL_Implies _ _) -> False;
    HL_And (HL_And _ _) (HL_Iff _ _) -> False;
    HL_And (HL_And _ _) (HL_ForAll _ _) -> False;
    HL_And (HL_And _ _) (HL_Exists _ _) -> False;
    HL_And (HL_Or _ _) (HL_Predicate _ _) -> False;
    HL_And (HL_Or _ _) (HL_Boolean _) -> False;
    HL_And (HL_Or hl_formula1 hl_formula2) (HL_Not a) ->
      equal_hl_formula (HL_Or hl_formula1 hl_formula2) a;
    HL_And (HL_Or _ _) (HL_And _ _) -> False;
    HL_And (HL_Or _ _) (HL_Or _ _) -> False;
    HL_And (HL_Or _ _) (HL_Implies _ _) -> False;
    HL_And (HL_Or _ _) (HL_Iff _ _) -> False;
    HL_And (HL_Or _ _) (HL_ForAll _ _) -> False;
    HL_And (HL_Or _ _) (HL_Exists _ _) -> False;
    HL_And (HL_Implies _ _) (HL_Predicate _ _) -> False;
    HL_And (HL_Implies _ _) (HL_Boolean _) -> False;
    HL_And (HL_Implies hl_formula1 hl_formula2) (HL_Not a) ->
      equal_hl_formula (HL_Implies hl_formula1 hl_formula2) a;
    HL_And (HL_Implies _ _) (HL_And _ _) -> False;
    HL_And (HL_Implies _ _) (HL_Or _ _) -> False;
    HL_And (HL_Implies _ _) (HL_Implies _ _) -> False;
    HL_And (HL_Implies _ _) (HL_Iff _ _) -> False;
    HL_And (HL_Implies _ _) (HL_ForAll _ _) -> False;
    HL_And (HL_Implies _ _) (HL_Exists _ _) -> False;
    HL_And (HL_Iff _ _) (HL_Predicate _ _) -> False;
    HL_And (HL_Iff _ _) (HL_Boolean _) -> False;
    HL_And (HL_Iff hl_formula1 hl_formula2) (HL_Not a) ->
      equal_hl_formula (HL_Iff hl_formula1 hl_formula2) a;
    HL_And (HL_Iff _ _) (HL_And _ _) -> False;
    HL_And (HL_Iff _ _) (HL_Or _ _) -> False;
    HL_And (HL_Iff _ _) (HL_Implies _ _) -> False;
    HL_And (HL_Iff _ _) (HL_Iff _ _) -> False;
    HL_And (HL_Iff _ _) (HL_ForAll _ _) -> False;
    HL_And (HL_Iff _ _) (HL_Exists _ _) -> False;
    HL_And (HL_ForAll _ _) (HL_Predicate _ _) -> False;
    HL_And (HL_ForAll _ _) (HL_Boolean _) -> False;
    HL_And (HL_ForAll literal hl_formula) (HL_Not a) ->
      equal_hl_formula (HL_ForAll literal hl_formula) a;
    HL_And (HL_ForAll _ _) (HL_And _ _) -> False;
    HL_And (HL_ForAll _ _) (HL_Or _ _) -> False;
    HL_And (HL_ForAll _ _) (HL_Implies _ _) -> False;
    HL_And (HL_ForAll _ _) (HL_Iff _ _) -> False;
    HL_And (HL_ForAll _ _) (HL_ForAll _ _) -> False;
    HL_And (HL_ForAll _ _) (HL_Exists _ _) -> False;
    HL_And (HL_Exists _ _) (HL_Predicate _ _) -> False;
    HL_And (HL_Exists _ _) (HL_Boolean _) -> False;
    HL_And (HL_Exists literal hl_formula) (HL_Not a) ->
      equal_hl_formula (HL_Exists literal hl_formula) a;
    HL_And (HL_Exists _ _) (HL_And _ _) -> False;
    HL_And (HL_Exists _ _) (HL_Or _ _) -> False;
    HL_And (HL_Exists _ _) (HL_Implies _ _) -> False;
    HL_And (HL_Exists _ _) (HL_Iff _ _) -> False;
    HL_And (HL_Exists _ _) (HL_ForAll _ _) -> False;
    HL_And (HL_Exists _ _) (HL_Exists _ _) -> False;
    HL_Or _ _ -> False;
    HL_Implies _ _ -> False;
    HL_Iff _ _ -> False;
    HL_ForAll _ _ -> False;
    HL_Exists _ _ -> False;
  });

hlFormulaAt :: [Hl_line] -> Int -> Maybe Hl_formula;
hlFormulaAt p n = map_option hlFormula (hlLookupLine p n);

hlRuleOK :: [Hl_line] -> Hl_line -> Bool;
hlRuleOK p l =
  let {
    phi = hlFormula l;
    g = hlReferences l;
  } in (case hlJustification l of {
         HL_Assumption -> equal_set g (insert (hlLineNumber l) bot_set);
         HL_MP m n ->
           (case (hlLookupLine p m, hlLookupLine p n) of {
             (Nothing, _) -> False;
             (Just _, Nothing) -> False;
             (Just lm, Just ln) ->
               (case hlFormula lm of {
                 HL_Predicate _ _ -> False;
                 HL_Boolean _ -> False;
                 HL_Not _ -> False;
                 HL_And _ _ -> False;
                 HL_Or _ _ -> False;
                 HL_Implies pa q ->
                   equal_hl_formula (hlFormula ln) pa &&
                     equal_hl_formula phi q &&
                       equal_set g
                         (sup_set (hlReferences lm) (hlReferences ln));
                 HL_Iff _ _ -> False;
                 HL_ForAll _ _ -> False;
                 HL_Exists _ _ -> False;
               });
           });
         HL_MT m n ->
           (case (hlLookupLine p m, (hlLookupLine p n, phi)) of {
             (Nothing, _) -> False;
             (Just _, (Nothing, _)) -> False;
             (Just _, (Just _, HL_Predicate _ _)) -> False;
             (Just _, (Just _, HL_Boolean _)) -> False;
             (Just lm, (Just ln, HL_Not pa)) ->
               (case (hlFormula lm, hlFormula ln) of {
                 (HL_Predicate _ _, _) -> False;
                 (HL_Boolean _, _) -> False;
                 (HL_Not _, _) -> False;
                 (HL_And _ _, _) -> False;
                 (HL_Or _ _, _) -> False;
                 (HL_Implies _ _, HL_Predicate _ _) -> False;
                 (HL_Implies _ _, HL_Boolean _) -> False;
                 (HL_Implies q r, HL_Not s) ->
                   equal_hl_formula pa q &&
                     equal_hl_formula r s &&
                       equal_set g
                         (sup_set (hlReferences lm) (hlReferences ln));
                 (HL_Implies _ _, HL_And _ _) -> False;
                 (HL_Implies _ _, HL_Or _ _) -> False;
                 (HL_Implies _ _, HL_Implies _ _) -> False;
                 (HL_Implies _ _, HL_Iff _ _) -> False;
                 (HL_Implies _ _, HL_ForAll _ _) -> False;
                 (HL_Implies _ _, HL_Exists _ _) -> False;
                 (HL_Iff _ _, _) -> False;
                 (HL_ForAll _ _, _) -> False;
                 (HL_Exists _ _, _) -> False;
               });
             (Just _, (Just _, HL_And _ _)) -> False;
             (Just _, (Just _, HL_Or _ _)) -> False;
             (Just _, (Just _, HL_Implies _ _)) -> False;
             (Just _, (Just _, HL_Iff _ _)) -> False;
             (Just _, (Just _, HL_ForAll _ _)) -> False;
             (Just _, (Just _, HL_Exists _ _)) -> False;
           });
         HL_DN m ->
           (case hlLookupLine p m of {
             Nothing -> False;
             Just lm ->
               (equal_hl_formula (hlFormula lm) (HL_Not (HL_Not phi)) ||
                 equal_hl_formula phi (HL_Not (HL_Not (hlFormula lm)))) &&
                 equal_set g (hlReferences lm);
           });
         HL_CP a c ->
           (case (hlLookupLine p a, hlLookupLine p c) of {
             (Nothing, _) -> False;
             (Just _, Nothing) -> False;
             (Just la, Just lc) ->
               equal_hl_justification (hlJustification la) HL_Assumption &&
                 equal_hl_formula phi
                   (HL_Implies (hlFormula la) (hlFormula lc)) &&
                   equal_set g (remove (hlLineNumber la) (hlReferences lc));
           });
         HL_AndIntro m n ->
           (case (hlLookupLine p m, hlLookupLine p n) of {
             (Nothing, _) -> False;
             (Just _, Nothing) -> False;
             (Just lm, Just ln) ->
               (equal_hl_formula phi (HL_And (hlFormula lm) (hlFormula ln)) ||
                 equal_hl_formula phi (HL_And (hlFormula ln) (hlFormula lm))) &&
                 equal_set g (sup_set (hlReferences lm) (hlReferences ln));
           });
         HL_AndElim m ->
           (case hlLookupLine p m of {
             Nothing -> False;
             Just lm ->
               (case hlFormula lm of {
                 HL_Predicate _ _ -> False;
                 HL_Boolean _ -> False;
                 HL_Not _ -> False;
                 HL_And pa q ->
                   (equal_hl_formula phi pa || equal_hl_formula phi q) &&
                     equal_set g (hlReferences lm);
                 HL_Or _ _ -> False;
                 HL_Implies _ _ -> False;
                 HL_Iff _ _ -> False;
                 HL_ForAll _ _ -> False;
                 HL_Exists _ _ -> False;
               });
           });
         HL_OrIntro m ->
           (case (hlLookupLine p m, phi) of {
             (Nothing, _) -> False;
             (Just _, HL_Predicate _ _) -> False;
             (Just _, HL_Boolean _) -> False;
             (Just _, HL_Not _) -> False;
             (Just _, HL_And _ _) -> False;
             (Just lm, HL_Or pa q) ->
               (equal_hl_formula (hlFormula lm) pa ||
                 equal_hl_formula (hlFormula lm) q) &&
                 equal_set g (hlReferences lm);
             (Just _, HL_Implies _ _) -> False;
             (Just _, HL_Iff _ _) -> False;
             (Just _, HL_ForAll _ _) -> False;
             (Just _, HL_Exists _ _) -> False;
           });
         HL_OrElim d a1 c1 a2 c2 ->
           (case (hlLookupLine p d,
                   (hlLookupLine p a1,
                     (hlLookupLine p c1,
                       (hlLookupLine p a2, hlLookupLine p c2))))
             of {
             (Nothing, _) -> False;
             (Just _, (Nothing, _)) -> False;
             (Just _, (Just _, (Nothing, _))) -> False;
             (Just _, (Just _, (Just _, (Nothing, _)))) -> False;
             (Just _, (Just _, (Just _, (Just _, Nothing)))) -> False;
             (Just ld, (Just la1, (Just lc1, (Just la2, Just lc2)))) ->
               equal_hl_justification (hlJustification la1) HL_Assumption &&
                 equal_hl_justification (hlJustification la2) HL_Assumption &&
                   equal_hl_formula (hlFormula lc1) phi &&
                     equal_hl_formula (hlFormula lc2) phi &&
                       (case hlFormula ld of {
                         HL_Predicate _ _ -> False;
                         HL_Boolean _ -> False;
                         HL_Not _ -> False;
                         HL_And _ _ -> False;
                         HL_Or pa q ->
                           equal_hl_formula (hlFormula la1) pa &&
                             equal_hl_formula (hlFormula la2) q ||
                             equal_hl_formula (hlFormula la1) q &&
                               equal_hl_formula (hlFormula la2) pa;
                         HL_Implies _ _ -> False;
                         HL_Iff _ _ -> False;
                         HL_ForAll _ _ -> False;
                         HL_Exists _ _ -> False;
                       }) &&
                         equal_set g
                           (sup_set
                             (sup_set (hlReferences ld)
                               (remove (hlLineNumber la1) (hlReferences lc1)))
                             (remove (hlLineNumber la2) (hlReferences lc2)));
           });
         HL_RAA a c ->
           (case (hlLookupLine p a, hlLookupLine p c) of {
             (Nothing, _) -> False;
             (Just _, Nothing) -> False;
             (Just la, Just lc) ->
               equal_hl_justification (hlJustification la) HL_Assumption &&
                 equal_hl_formula phi (HL_Not (hlFormula la)) &&
                   hlContradiction (hlFormula lc) &&
                     equal_set g (remove (hlLineNumber la) (hlReferences lc));
           });
         HL_ForallElim m ->
           (case hlLookupLine p m of {
             Nothing -> False;
             Just lm ->
               (case hlCollectForalls (hlFormula lm) of {
                 (sourceVars, sourceCore) ->
                   (case hlCollectForalls phi of {
                     (targetVars, targetCore) ->
                       (case hlEliminationCount sourceVars targetVars of {
                         Nothing -> False;
                         Just k ->
                           not (is_none
                                 (hlInferWitnessConstsK sourceVars sourceCore k
                                   targetCore)) &&
                             equal_set g (hlReferences lm);
                       });
                   });
               });
           });
         HL_ExistsIntro m ->
           (case hlLookupLine p m of {
             Nothing -> False;
             Just lm ->
               (case hlCollectExists phi of {
                 (xs, core) ->
                   not (null xs) &&
                     any (\ k ->
                           not (is_none
                                 (hlInferWitnessConstsK xs
                                   (hlPrefixExists (drop k xs) core) k
                                   (hlFormula lm))))
                       (upt zero_nat (suc (size_lista xs))) &&
                       equal_set g (hlReferences lm);
               });
           });
         HL_ForallIntro m ->
           (case hlLookupLine p m of {
             Nothing -> False;
             Just lm ->
               (case hlCollectForalls phi of {
                 (xs, core) ->
                   not (null xs) &&
                     (case hlInferWitnessConstsK xs core (size_lista xs)
                             (hlFormula lm)
                       of {
                       Nothing -> False;
                       Just cs ->
                         let {
                           pairs =
                             filter (\ xc -> not (snd xc == "")) (zip xs cs);
                         } in hlAbstractMany pairs (hlFormula lm) ==
                                Just core &&
                                ball (image snd (Set pairs))
                                  (\ c ->
                                    not (member c
  (hlAssumptionConstants p (hlReferences lm)))) &&
                                  equal_set g (hlReferences lm);
                     });
               });
           });
         HL_ExistsElim m a c ->
           (case (hlLookupLine p m, (hlLookupLine p a, hlLookupLine p c)) of {
             (Nothing, _) -> False;
             (Just _, (Nothing, _)) -> False;
             (Just _, (Just _, Nothing)) -> False;
             (Just lm, (Just la, Just lc)) ->
               (case hlCollectExists (hlFormula lm) of {
                 (sourceVars, sourceCore) ->
                   (case hlCollectExists (hlFormula la) of {
                     (targetVars, _) ->
                       let {
                         delta = remove (hlLineNumber la) (hlReferences lc);
                       } in not (null sourceVars) &&
                              equal_hl_justification (hlJustification la)
                                HL_Assumption &&
                                (case hlEliminationCount sourceVars targetVars
                                  of {
                                  Nothing -> False;
                                  Just k ->
                                    let {
                                      template =
hlPrefixExists targetVars sourceCore;
                                    } in (case
   hlInferWitnessConstsK sourceVars template k (hlFormula la) of {
   Nothing -> False;
   Just cs ->
     let {
       pairs = filter (\ xc -> not (snd xc == "")) (zip (take k sourceVars) cs);
     } in hlAbstractMany pairs (hlFormula la) == Just template &&
            ball (image snd (Set pairs))
              (\ w ->
                not (member w (hlConstantsInFormula (hlFormula lc))) &&
                  not (member w (hlReferencedConstants p delta))) &&
              equal_hl_formula phi (hlFormula lc) &&
                equal_set g (sup_set (hlReferences lm) delta);
 });
                                });
                   });
               });
           });
         HL_EqIntro ->
           (case phi of {
             HL_Predicate _ [] -> False;
             HL_Predicate _ (HL_Var _ : _) -> False;
             HL_Predicate _ [HL_Const _] -> False;
             HL_Predicate _ (HL_Const _ : HL_Var _ : _) -> False;
             HL_Predicate e [HL_Const a, HL_Const b] ->
               e == "=" && a == b && equal_set g bot_set;
             HL_Predicate _ (HL_Const _ : HL_Const _ : _ : _) -> False;
             HL_Boolean _ -> False;
             HL_Not _ -> False;
             HL_And _ _ -> False;
             HL_Or _ _ -> False;
             HL_Implies _ _ -> False;
             HL_Iff _ _ -> False;
             HL_ForAll _ _ -> False;
             HL_Exists _ _ -> False;
           });
         HL_EqElim m n ->
           (case (hlLookupLine p m, hlLookupLine p n) of {
             (Nothing, _) -> False;
             (Just _, Nothing) -> False;
             (Just lm, Just ln) ->
               (case hlEqualityFormula (hlFormula ln) of {
                 Nothing -> False;
                 Just (HL_Var _, _) -> False;
                 Just (HL_Const _, HL_Var _) -> False;
                 Just (HL_Const a, HL_Const b) ->
                   hlEqualUpToConstantReplacement a b (hlFormula lm) phi &&
                     equal_set g (sup_set (hlReferences lm) (hlReferences ln));
               });
           });
         HL_LEM -> hlExcludedMiddle phi;
         HL_PropTaut ms ->
           all (\ m -> not (is_none (hlLookupLine p m))) ms &&
             hlPropositionalConsequence (hlMapFilter (hlFormulaAt p) ms) phi &&
               equal_set g (hlReferenceUnion p ms);
         HL_IffIntro m n ->
           (case (hlLookupLine p m, (hlLookupLine p n, phi)) of {
             (Nothing, _) -> False;
             (Just _, (Nothing, _)) -> False;
             (Just _, (Just _, HL_Predicate _ _)) -> False;
             (Just _, (Just _, HL_Boolean _)) -> False;
             (Just _, (Just _, HL_Not _)) -> False;
             (Just _, (Just _, HL_And _ _)) -> False;
             (Just _, (Just _, HL_Or _ _)) -> False;
             (Just _, (Just _, HL_Implies _ _)) -> False;
             (Just lm, (Just ln, HL_Iff u v)) ->
               (case (hlFormula lm, hlFormula ln) of {
                 (HL_Predicate _ _, _) -> False;
                 (HL_Boolean _, _) -> False;
                 (HL_Not _, _) -> False;
                 (HL_And _ _, _) -> False;
                 (HL_Or _ _, _) -> False;
                 (HL_Implies _ _, HL_Predicate _ _) -> False;
                 (HL_Implies _ _, HL_Boolean _) -> False;
                 (HL_Implies _ _, HL_Not _) -> False;
                 (HL_Implies _ _, HL_And _ _) -> False;
                 (HL_Implies _ _, HL_Or _ _) -> False;
                 (HL_Implies pa q, HL_Implies r s) ->
                   equal_hl_formula pa s &&
                     equal_hl_formula q r &&
                       (equal_hl_formula u pa && equal_hl_formula v q ||
                         equal_hl_formula u q && equal_hl_formula v pa) &&
                         equal_set g
                           (sup_set (hlReferences lm) (hlReferences ln));
                 (HL_Implies _ _, HL_Iff _ _) -> False;
                 (HL_Implies _ _, HL_ForAll _ _) -> False;
                 (HL_Implies _ _, HL_Exists _ _) -> False;
                 (HL_Iff _ _, _) -> False;
                 (HL_ForAll _ _, _) -> False;
                 (HL_Exists _ _, _) -> False;
               });
             (Just _, (Just _, HL_ForAll _ _)) -> False;
             (Just _, (Just _, HL_Exists _ _)) -> False;
           });
         HL_IffElim m n ->
           (case (hlLookupLine p m, hlLookupLine p n) of {
             (Nothing, _) -> False;
             (Just _, Nothing) -> False;
             (Just lm, Just ln) ->
               (case hlFormula lm of {
                 HL_Predicate _ _ -> False;
                 HL_Boolean _ -> False;
                 HL_Not _ -> False;
                 HL_And _ _ -> False;
                 HL_Or _ _ -> False;
                 HL_Implies _ _ -> False;
                 HL_Iff pa q ->
                   (equal_hl_formula (hlFormula ln) pa &&
                      equal_hl_formula phi q ||
                     equal_hl_formula (hlFormula ln) q &&
                       equal_hl_formula phi pa) &&
                     equal_set g (sup_set (hlReferences lm) (hlReferences ln));
                 HL_ForAll _ _ -> False;
                 HL_Exists _ _ -> False;
               });
           });
         HL_QN m ->
           (case hlLookupLine p m of {
             Nothing -> False;
             Just lm ->
               hlQuantifierNegationEquivalent (hlFormula lm) phi &&
                 equal_set g (hlReferences lm);
           });
       });

hlLineOK :: [Hl_line] -> Hl_line -> Bool;
hlLineOK p l = hlStructureOK p l && hlRuleOK p l;

eqsub_t :: String -> String -> Trm -> Trm -> Bool;
eqsub_t a b (Nm c) (Nm d) = c == d || c == a && d == b;
eqsub_t a b (Vr x) (Vr y) = x == y;
eqsub_t a b (Vr v) (Nm va) = False;
eqsub_t a b (Nm va) (Vr v) = False;

eqsub :: String -> String -> Fm -> Fm -> Bool;
eqsub a b (Atom p ts) (Atom q us) = p == q && list_all2 (eqsub_t a b) ts us;
eqsub a b (Eqf ta ua) (Eqf t u) = eqsub_t a b ta t && eqsub_t a b ua u;
eqsub a b Bot Bot = True;
eqsub a b (Neg pa) (Neg p) = eqsub a b pa p;
eqsub a b (Conj pa qa) (Conj p q) = eqsub a b pa p && eqsub a b qa q;
eqsub a b (Disj pa qa) (Disj p q) = eqsub a b pa p && eqsub a b qa q;
eqsub a b (Impl pa qa) (Impl p q) = eqsub a b pa p && eqsub a b qa q;
eqsub a b (Iff pa qa) (Iff p q) = eqsub a b pa p && eqsub a b qa q;
eqsub a b (Uni x pa) (Uni y p) = x == y && eqsub a b pa p;
eqsub a b (Exi x pa) (Exi y p) = x == y && eqsub a b pa p;
eqsub a b (Eqf v va) (Atom vb vc) = False;
eqsub a b (Eqf v va) Bot = False;
eqsub a b (Eqf v va) (Neg vb) = False;
eqsub a b (Eqf v va) (Conj vb vc) = False;
eqsub a b (Eqf v va) (Disj vb vc) = False;
eqsub a b (Eqf v va) (Impl vb vc) = False;
eqsub a b (Eqf v va) (Iff vb vc) = False;
eqsub a b (Eqf v va) (Uni vb vc) = False;
eqsub a b (Eqf v va) (Exi vb vc) = False;
eqsub a b Bot (Atom v va) = False;
eqsub a b Bot (Eqf v va) = False;
eqsub a b Bot (Neg v) = False;
eqsub a b Bot (Conj v va) = False;
eqsub a b Bot (Disj v va) = False;
eqsub a b Bot (Impl v va) = False;
eqsub a b Bot (Iff v va) = False;
eqsub a b Bot (Uni v va) = False;
eqsub a b Bot (Exi v va) = False;
eqsub a b (Neg v) (Atom va vb) = False;
eqsub a b (Neg v) (Eqf va vb) = False;
eqsub a b (Neg v) Bot = False;
eqsub a b (Neg v) (Conj va vb) = False;
eqsub a b (Neg v) (Disj va vb) = False;
eqsub a b (Neg v) (Impl va vb) = False;
eqsub a b (Neg v) (Iff va vb) = False;
eqsub a b (Neg v) (Uni va vb) = False;
eqsub a b (Neg v) (Exi va vb) = False;
eqsub a b (Conj v va) (Atom vb vc) = False;
eqsub a b (Conj v va) (Eqf vb vc) = False;
eqsub a b (Conj v va) Bot = False;
eqsub a b (Conj v va) (Neg vb) = False;
eqsub a b (Conj v va) (Disj vb vc) = False;
eqsub a b (Conj v va) (Impl vb vc) = False;
eqsub a b (Conj v va) (Iff vb vc) = False;
eqsub a b (Conj v va) (Uni vb vc) = False;
eqsub a b (Conj v va) (Exi vb vc) = False;
eqsub a b (Disj v va) (Atom vb vc) = False;
eqsub a b (Disj v va) (Eqf vb vc) = False;
eqsub a b (Disj v va) Bot = False;
eqsub a b (Disj v va) (Neg vb) = False;
eqsub a b (Disj v va) (Conj vb vc) = False;
eqsub a b (Disj v va) (Impl vb vc) = False;
eqsub a b (Disj v va) (Iff vb vc) = False;
eqsub a b (Disj v va) (Uni vb vc) = False;
eqsub a b (Disj v va) (Exi vb vc) = False;
eqsub a b (Impl v va) (Atom vb vc) = False;
eqsub a b (Impl v va) (Eqf vb vc) = False;
eqsub a b (Impl v va) Bot = False;
eqsub a b (Impl v va) (Neg vb) = False;
eqsub a b (Impl v va) (Conj vb vc) = False;
eqsub a b (Impl v va) (Disj vb vc) = False;
eqsub a b (Impl v va) (Iff vb vc) = False;
eqsub a b (Impl v va) (Uni vb vc) = False;
eqsub a b (Impl v va) (Exi vb vc) = False;
eqsub a b (Iff v va) (Atom vb vc) = False;
eqsub a b (Iff v va) (Eqf vb vc) = False;
eqsub a b (Iff v va) Bot = False;
eqsub a b (Iff v va) (Neg vb) = False;
eqsub a b (Iff v va) (Conj vb vc) = False;
eqsub a b (Iff v va) (Disj vb vc) = False;
eqsub a b (Iff v va) (Impl vb vc) = False;
eqsub a b (Iff v va) (Uni vb vc) = False;
eqsub a b (Iff v va) (Exi vb vc) = False;
eqsub a b (Uni v va) (Atom vb vc) = False;
eqsub a b (Uni v va) (Eqf vb vc) = False;
eqsub a b (Uni v va) Bot = False;
eqsub a b (Uni v va) (Neg vb) = False;
eqsub a b (Uni v va) (Conj vb vc) = False;
eqsub a b (Uni v va) (Disj vb vc) = False;
eqsub a b (Uni v va) (Impl vb vc) = False;
eqsub a b (Uni v va) (Iff vb vc) = False;
eqsub a b (Uni v va) (Exi vb vc) = False;
eqsub a b (Exi v va) (Atom vb vc) = False;
eqsub a b (Exi v va) (Eqf vb vc) = False;
eqsub a b (Exi v va) Bot = False;
eqsub a b (Exi v va) (Neg vb) = False;
eqsub a b (Exi v va) (Conj vb vc) = False;
eqsub a b (Exi v va) (Disj vb vc) = False;
eqsub a b (Exi v va) (Impl vb vc) = False;
eqsub a b (Exi v va) (Iff vb vc) = False;
eqsub a b (Exi v va) (Uni vb vc) = False;
eqsub a b (Atom vb vc) (Eqf v va) = False;
eqsub a b (Atom v va) Bot = False;
eqsub a b (Atom va vb) (Neg v) = False;
eqsub a b (Atom vb vc) (Conj v va) = False;
eqsub a b (Atom vb vc) (Disj v va) = False;
eqsub a b (Atom vb vc) (Impl v va) = False;
eqsub a b (Atom vb vc) (Iff v va) = False;
eqsub a b (Atom vb vc) (Uni v va) = False;
eqsub a b (Atom vb vc) (Exi v va) = False;

genOK :: String -> Fm -> Fm -> [Fm] -> Bool;
genOK x p psi asa =
  (if membera (fvs p) x
    then any (\ a -> not (membera (names p) a) && arbitrary_in a asa)
           (instWitnesses x p psi)
    else equal_fm psi p);

witOK :: String -> Fm -> Fm -> Fm -> [Fm] -> Bool;
witOK x p psi phi asa =
  (if membera (fvs p) x
    then any (\ b ->
               not (membera (names p) b) &&
                 not (membera (names phi) b) && arbitrary_in b asa)
           (instWitnesses x p psi)
    else equal_fm psi p);

equal_char :: Char -> Char -> Bool;
equal_char (Char x1 x2 x3 x4 x5 x6 x7 x8) (Char y1 y2 y3 y4 y5 y6 y7 y8) =
  x1 == y1 &&
    x2 == y2 &&
      x3 == y3 && x4 == y4 && x5 == y5 && x6 == y6 && x7 == y7 && x8 == y8;

dispLen :: [Char] -> Nat;
dispLen [] = zero_nat;
dispLen (c : cs) =
  (if equal_char c (Char False False True True True False True False)
    then suc (dispLen
               (tl (dropWhile
                     (\ x ->
                       not (equal_char x
                             (Char False True True True True True False False)))
                     cs)))
    else suc (dispLen cs));

dispWidth :: String -> Nat;
dispWidth s = dispLen (explode s);

padTo :: Nat -> String -> String;
padTo n s =
  s ++ implode
         (replicate (minus_nat n (dispWidth s))
           (Char False False False False False True False False));

sepBy :: String -> [String] -> String;
sepBy s ss = (case ss of {
               [] -> "";
               t : ts -> t ++ cat (map (\ a -> s ++ a) ts);
             });

isaSym :: String -> String;
isaSym s =
  (implode
     [Char False False True True True False True False,
       Char False False True True True True False False] ++
    s) ++
    ">";

symEx :: String;
symEx = isaSym "exists";

symOr :: String;
symOr = isaSym "or";

sorted_wrt :: forall a. (a -> a -> Bool) -> [a] -> Bool;
sorted_wrt p [] = True;
sorted_wrt p (x : ys) = all (p x) ys && sorted_wrt p ys;

equal_fitch_rule :: Fitch_rule -> Fitch_rule -> Bool;
equal_fitch_rule (FEqElim x221 x222) (FReit x23) = False;
equal_fitch_rule (FReit x23) (FEqElim x221 x222) = False;
equal_fitch_rule FEqIntro (FReit x23) = False;
equal_fitch_rule (FReit x23) FEqIntro = False;
equal_fitch_rule FEqIntro (FEqElim x221 x222) = False;
equal_fitch_rule (FEqElim x221 x222) FEqIntro = False;
equal_fitch_rule (FExistsElim x201 x202) (FReit x23) = False;
equal_fitch_rule (FReit x23) (FExistsElim x201 x202) = False;
equal_fitch_rule (FExistsElim x201 x202) (FEqElim x221 x222) = False;
equal_fitch_rule (FEqElim x221 x222) (FExistsElim x201 x202) = False;
equal_fitch_rule (FExistsElim x201 x202) FEqIntro = False;
equal_fitch_rule FEqIntro (FExistsElim x201 x202) = False;
equal_fitch_rule (FExistsIntro x19) (FReit x23) = False;
equal_fitch_rule (FReit x23) (FExistsIntro x19) = False;
equal_fitch_rule (FExistsIntro x19) (FEqElim x221 x222) = False;
equal_fitch_rule (FEqElim x221 x222) (FExistsIntro x19) = False;
equal_fitch_rule (FExistsIntro x19) FEqIntro = False;
equal_fitch_rule FEqIntro (FExistsIntro x19) = False;
equal_fitch_rule (FExistsIntro x19) (FExistsElim x201 x202) = False;
equal_fitch_rule (FExistsElim x201 x202) (FExistsIntro x19) = False;
equal_fitch_rule (FForallIntro x18) (FReit x23) = False;
equal_fitch_rule (FReit x23) (FForallIntro x18) = False;
equal_fitch_rule (FForallIntro x18) (FEqElim x221 x222) = False;
equal_fitch_rule (FEqElim x221 x222) (FForallIntro x18) = False;
equal_fitch_rule (FForallIntro x18) FEqIntro = False;
equal_fitch_rule FEqIntro (FForallIntro x18) = False;
equal_fitch_rule (FForallIntro x18) (FExistsElim x201 x202) = False;
equal_fitch_rule (FExistsElim x201 x202) (FForallIntro x18) = False;
equal_fitch_rule (FForallIntro x18) (FExistsIntro x19) = False;
equal_fitch_rule (FExistsIntro x19) (FForallIntro x18) = False;
equal_fitch_rule (FForallElim x17) (FReit x23) = False;
equal_fitch_rule (FReit x23) (FForallElim x17) = False;
equal_fitch_rule (FForallElim x17) (FEqElim x221 x222) = False;
equal_fitch_rule (FEqElim x221 x222) (FForallElim x17) = False;
equal_fitch_rule (FForallElim x17) FEqIntro = False;
equal_fitch_rule FEqIntro (FForallElim x17) = False;
equal_fitch_rule (FForallElim x17) (FExistsElim x201 x202) = False;
equal_fitch_rule (FExistsElim x201 x202) (FForallElim x17) = False;
equal_fitch_rule (FForallElim x17) (FExistsIntro x19) = False;
equal_fitch_rule (FExistsIntro x19) (FForallElim x17) = False;
equal_fitch_rule (FForallElim x17) (FForallIntro x18) = False;
equal_fitch_rule (FForallIntro x18) (FForallElim x17) = False;
equal_fitch_rule (FIffElimR x16) (FReit x23) = False;
equal_fitch_rule (FReit x23) (FIffElimR x16) = False;
equal_fitch_rule (FIffElimR x16) (FEqElim x221 x222) = False;
equal_fitch_rule (FEqElim x221 x222) (FIffElimR x16) = False;
equal_fitch_rule (FIffElimR x16) FEqIntro = False;
equal_fitch_rule FEqIntro (FIffElimR x16) = False;
equal_fitch_rule (FIffElimR x16) (FExistsElim x201 x202) = False;
equal_fitch_rule (FExistsElim x201 x202) (FIffElimR x16) = False;
equal_fitch_rule (FIffElimR x16) (FExistsIntro x19) = False;
equal_fitch_rule (FExistsIntro x19) (FIffElimR x16) = False;
equal_fitch_rule (FIffElimR x16) (FForallIntro x18) = False;
equal_fitch_rule (FForallIntro x18) (FIffElimR x16) = False;
equal_fitch_rule (FIffElimR x16) (FForallElim x17) = False;
equal_fitch_rule (FForallElim x17) (FIffElimR x16) = False;
equal_fitch_rule (FIffElimL x15) (FReit x23) = False;
equal_fitch_rule (FReit x23) (FIffElimL x15) = False;
equal_fitch_rule (FIffElimL x15) (FEqElim x221 x222) = False;
equal_fitch_rule (FEqElim x221 x222) (FIffElimL x15) = False;
equal_fitch_rule (FIffElimL x15) FEqIntro = False;
equal_fitch_rule FEqIntro (FIffElimL x15) = False;
equal_fitch_rule (FIffElimL x15) (FExistsElim x201 x202) = False;
equal_fitch_rule (FExistsElim x201 x202) (FIffElimL x15) = False;
equal_fitch_rule (FIffElimL x15) (FExistsIntro x19) = False;
equal_fitch_rule (FExistsIntro x19) (FIffElimL x15) = False;
equal_fitch_rule (FIffElimL x15) (FForallIntro x18) = False;
equal_fitch_rule (FForallIntro x18) (FIffElimL x15) = False;
equal_fitch_rule (FIffElimL x15) (FForallElim x17) = False;
equal_fitch_rule (FForallElim x17) (FIffElimL x15) = False;
equal_fitch_rule (FIffElimL x15) (FIffElimR x16) = False;
equal_fitch_rule (FIffElimR x16) (FIffElimL x15) = False;
equal_fitch_rule (FIffIntro x141 x142) (FReit x23) = False;
equal_fitch_rule (FReit x23) (FIffIntro x141 x142) = False;
equal_fitch_rule (FIffIntro x141 x142) (FEqElim x221 x222) = False;
equal_fitch_rule (FEqElim x221 x222) (FIffIntro x141 x142) = False;
equal_fitch_rule (FIffIntro x141 x142) FEqIntro = False;
equal_fitch_rule FEqIntro (FIffIntro x141 x142) = False;
equal_fitch_rule (FIffIntro x141 x142) (FExistsElim x201 x202) = False;
equal_fitch_rule (FExistsElim x201 x202) (FIffIntro x141 x142) = False;
equal_fitch_rule (FIffIntro x141 x142) (FExistsIntro x19) = False;
equal_fitch_rule (FExistsIntro x19) (FIffIntro x141 x142) = False;
equal_fitch_rule (FIffIntro x141 x142) (FForallIntro x18) = False;
equal_fitch_rule (FForallIntro x18) (FIffIntro x141 x142) = False;
equal_fitch_rule (FIffIntro x141 x142) (FForallElim x17) = False;
equal_fitch_rule (FForallElim x17) (FIffIntro x141 x142) = False;
equal_fitch_rule (FIffIntro x141 x142) (FIffElimR x16) = False;
equal_fitch_rule (FIffElimR x16) (FIffIntro x141 x142) = False;
equal_fitch_rule (FIffIntro x141 x142) (FIffElimL x15) = False;
equal_fitch_rule (FIffElimL x15) (FIffIntro x141 x142) = False;
equal_fitch_rule (FOrElim x131 x132 x133) (FReit x23) = False;
equal_fitch_rule (FReit x23) (FOrElim x131 x132 x133) = False;
equal_fitch_rule (FOrElim x131 x132 x133) (FEqElim x221 x222) = False;
equal_fitch_rule (FEqElim x221 x222) (FOrElim x131 x132 x133) = False;
equal_fitch_rule (FOrElim x131 x132 x133) FEqIntro = False;
equal_fitch_rule FEqIntro (FOrElim x131 x132 x133) = False;
equal_fitch_rule (FOrElim x131 x132 x133) (FExistsElim x201 x202) = False;
equal_fitch_rule (FExistsElim x201 x202) (FOrElim x131 x132 x133) = False;
equal_fitch_rule (FOrElim x131 x132 x133) (FExistsIntro x19) = False;
equal_fitch_rule (FExistsIntro x19) (FOrElim x131 x132 x133) = False;
equal_fitch_rule (FOrElim x131 x132 x133) (FForallIntro x18) = False;
equal_fitch_rule (FForallIntro x18) (FOrElim x131 x132 x133) = False;
equal_fitch_rule (FOrElim x131 x132 x133) (FForallElim x17) = False;
equal_fitch_rule (FForallElim x17) (FOrElim x131 x132 x133) = False;
equal_fitch_rule (FOrElim x131 x132 x133) (FIffElimR x16) = False;
equal_fitch_rule (FIffElimR x16) (FOrElim x131 x132 x133) = False;
equal_fitch_rule (FOrElim x131 x132 x133) (FIffElimL x15) = False;
equal_fitch_rule (FIffElimL x15) (FOrElim x131 x132 x133) = False;
equal_fitch_rule (FOrElim x131 x132 x133) (FIffIntro x141 x142) = False;
equal_fitch_rule (FIffIntro x141 x142) (FOrElim x131 x132 x133) = False;
equal_fitch_rule (FOrIntroR x12) (FReit x23) = False;
equal_fitch_rule (FReit x23) (FOrIntroR x12) = False;
equal_fitch_rule (FOrIntroR x12) (FEqElim x221 x222) = False;
equal_fitch_rule (FEqElim x221 x222) (FOrIntroR x12) = False;
equal_fitch_rule (FOrIntroR x12) FEqIntro = False;
equal_fitch_rule FEqIntro (FOrIntroR x12) = False;
equal_fitch_rule (FOrIntroR x12) (FExistsElim x201 x202) = False;
equal_fitch_rule (FExistsElim x201 x202) (FOrIntroR x12) = False;
equal_fitch_rule (FOrIntroR x12) (FExistsIntro x19) = False;
equal_fitch_rule (FExistsIntro x19) (FOrIntroR x12) = False;
equal_fitch_rule (FOrIntroR x12) (FForallIntro x18) = False;
equal_fitch_rule (FForallIntro x18) (FOrIntroR x12) = False;
equal_fitch_rule (FOrIntroR x12) (FForallElim x17) = False;
equal_fitch_rule (FForallElim x17) (FOrIntroR x12) = False;
equal_fitch_rule (FOrIntroR x12) (FIffElimR x16) = False;
equal_fitch_rule (FIffElimR x16) (FOrIntroR x12) = False;
equal_fitch_rule (FOrIntroR x12) (FIffElimL x15) = False;
equal_fitch_rule (FIffElimL x15) (FOrIntroR x12) = False;
equal_fitch_rule (FOrIntroR x12) (FIffIntro x141 x142) = False;
equal_fitch_rule (FIffIntro x141 x142) (FOrIntroR x12) = False;
equal_fitch_rule (FOrIntroR x12) (FOrElim x131 x132 x133) = False;
equal_fitch_rule (FOrElim x131 x132 x133) (FOrIntroR x12) = False;
equal_fitch_rule (FOrIntroL x11) (FReit x23) = False;
equal_fitch_rule (FReit x23) (FOrIntroL x11) = False;
equal_fitch_rule (FOrIntroL x11) (FEqElim x221 x222) = False;
equal_fitch_rule (FEqElim x221 x222) (FOrIntroL x11) = False;
equal_fitch_rule (FOrIntroL x11) FEqIntro = False;
equal_fitch_rule FEqIntro (FOrIntroL x11) = False;
equal_fitch_rule (FOrIntroL x11) (FExistsElim x201 x202) = False;
equal_fitch_rule (FExistsElim x201 x202) (FOrIntroL x11) = False;
equal_fitch_rule (FOrIntroL x11) (FExistsIntro x19) = False;
equal_fitch_rule (FExistsIntro x19) (FOrIntroL x11) = False;
equal_fitch_rule (FOrIntroL x11) (FForallIntro x18) = False;
equal_fitch_rule (FForallIntro x18) (FOrIntroL x11) = False;
equal_fitch_rule (FOrIntroL x11) (FForallElim x17) = False;
equal_fitch_rule (FForallElim x17) (FOrIntroL x11) = False;
equal_fitch_rule (FOrIntroL x11) (FIffElimR x16) = False;
equal_fitch_rule (FIffElimR x16) (FOrIntroL x11) = False;
equal_fitch_rule (FOrIntroL x11) (FIffElimL x15) = False;
equal_fitch_rule (FIffElimL x15) (FOrIntroL x11) = False;
equal_fitch_rule (FOrIntroL x11) (FIffIntro x141 x142) = False;
equal_fitch_rule (FIffIntro x141 x142) (FOrIntroL x11) = False;
equal_fitch_rule (FOrIntroL x11) (FOrElim x131 x132 x133) = False;
equal_fitch_rule (FOrElim x131 x132 x133) (FOrIntroL x11) = False;
equal_fitch_rule (FOrIntroL x11) (FOrIntroR x12) = False;
equal_fitch_rule (FOrIntroR x12) (FOrIntroL x11) = False;
equal_fitch_rule (FAndElimR x10) (FReit x23) = False;
equal_fitch_rule (FReit x23) (FAndElimR x10) = False;
equal_fitch_rule (FAndElimR x10) (FEqElim x221 x222) = False;
equal_fitch_rule (FEqElim x221 x222) (FAndElimR x10) = False;
equal_fitch_rule (FAndElimR x10) FEqIntro = False;
equal_fitch_rule FEqIntro (FAndElimR x10) = False;
equal_fitch_rule (FAndElimR x10) (FExistsElim x201 x202) = False;
equal_fitch_rule (FExistsElim x201 x202) (FAndElimR x10) = False;
equal_fitch_rule (FAndElimR x10) (FExistsIntro x19) = False;
equal_fitch_rule (FExistsIntro x19) (FAndElimR x10) = False;
equal_fitch_rule (FAndElimR x10) (FForallIntro x18) = False;
equal_fitch_rule (FForallIntro x18) (FAndElimR x10) = False;
equal_fitch_rule (FAndElimR x10) (FForallElim x17) = False;
equal_fitch_rule (FForallElim x17) (FAndElimR x10) = False;
equal_fitch_rule (FAndElimR x10) (FIffElimR x16) = False;
equal_fitch_rule (FIffElimR x16) (FAndElimR x10) = False;
equal_fitch_rule (FAndElimR x10) (FIffElimL x15) = False;
equal_fitch_rule (FIffElimL x15) (FAndElimR x10) = False;
equal_fitch_rule (FAndElimR x10) (FIffIntro x141 x142) = False;
equal_fitch_rule (FIffIntro x141 x142) (FAndElimR x10) = False;
equal_fitch_rule (FAndElimR x10) (FOrElim x131 x132 x133) = False;
equal_fitch_rule (FOrElim x131 x132 x133) (FAndElimR x10) = False;
equal_fitch_rule (FAndElimR x10) (FOrIntroR x12) = False;
equal_fitch_rule (FOrIntroR x12) (FAndElimR x10) = False;
equal_fitch_rule (FAndElimR x10) (FOrIntroL x11) = False;
equal_fitch_rule (FOrIntroL x11) (FAndElimR x10) = False;
equal_fitch_rule (FAndElimL x9) (FReit x23) = False;
equal_fitch_rule (FReit x23) (FAndElimL x9) = False;
equal_fitch_rule (FAndElimL x9) (FEqElim x221 x222) = False;
equal_fitch_rule (FEqElim x221 x222) (FAndElimL x9) = False;
equal_fitch_rule (FAndElimL x9) FEqIntro = False;
equal_fitch_rule FEqIntro (FAndElimL x9) = False;
equal_fitch_rule (FAndElimL x9) (FExistsElim x201 x202) = False;
equal_fitch_rule (FExistsElim x201 x202) (FAndElimL x9) = False;
equal_fitch_rule (FAndElimL x9) (FExistsIntro x19) = False;
equal_fitch_rule (FExistsIntro x19) (FAndElimL x9) = False;
equal_fitch_rule (FAndElimL x9) (FForallIntro x18) = False;
equal_fitch_rule (FForallIntro x18) (FAndElimL x9) = False;
equal_fitch_rule (FAndElimL x9) (FForallElim x17) = False;
equal_fitch_rule (FForallElim x17) (FAndElimL x9) = False;
equal_fitch_rule (FAndElimL x9) (FIffElimR x16) = False;
equal_fitch_rule (FIffElimR x16) (FAndElimL x9) = False;
equal_fitch_rule (FAndElimL x9) (FIffElimL x15) = False;
equal_fitch_rule (FIffElimL x15) (FAndElimL x9) = False;
equal_fitch_rule (FAndElimL x9) (FIffIntro x141 x142) = False;
equal_fitch_rule (FIffIntro x141 x142) (FAndElimL x9) = False;
equal_fitch_rule (FAndElimL x9) (FOrElim x131 x132 x133) = False;
equal_fitch_rule (FOrElim x131 x132 x133) (FAndElimL x9) = False;
equal_fitch_rule (FAndElimL x9) (FOrIntroR x12) = False;
equal_fitch_rule (FOrIntroR x12) (FAndElimL x9) = False;
equal_fitch_rule (FAndElimL x9) (FOrIntroL x11) = False;
equal_fitch_rule (FOrIntroL x11) (FAndElimL x9) = False;
equal_fitch_rule (FAndElimL x9) (FAndElimR x10) = False;
equal_fitch_rule (FAndElimR x10) (FAndElimL x9) = False;
equal_fitch_rule (FAndIntro x81 x82) (FReit x23) = False;
equal_fitch_rule (FReit x23) (FAndIntro x81 x82) = False;
equal_fitch_rule (FAndIntro x81 x82) (FEqElim x221 x222) = False;
equal_fitch_rule (FEqElim x221 x222) (FAndIntro x81 x82) = False;
equal_fitch_rule (FAndIntro x81 x82) FEqIntro = False;
equal_fitch_rule FEqIntro (FAndIntro x81 x82) = False;
equal_fitch_rule (FAndIntro x81 x82) (FExistsElim x201 x202) = False;
equal_fitch_rule (FExistsElim x201 x202) (FAndIntro x81 x82) = False;
equal_fitch_rule (FAndIntro x81 x82) (FExistsIntro x19) = False;
equal_fitch_rule (FExistsIntro x19) (FAndIntro x81 x82) = False;
equal_fitch_rule (FAndIntro x81 x82) (FForallIntro x18) = False;
equal_fitch_rule (FForallIntro x18) (FAndIntro x81 x82) = False;
equal_fitch_rule (FAndIntro x81 x82) (FForallElim x17) = False;
equal_fitch_rule (FForallElim x17) (FAndIntro x81 x82) = False;
equal_fitch_rule (FAndIntro x81 x82) (FIffElimR x16) = False;
equal_fitch_rule (FIffElimR x16) (FAndIntro x81 x82) = False;
equal_fitch_rule (FAndIntro x81 x82) (FIffElimL x15) = False;
equal_fitch_rule (FIffElimL x15) (FAndIntro x81 x82) = False;
equal_fitch_rule (FAndIntro x81 x82) (FIffIntro x141 x142) = False;
equal_fitch_rule (FIffIntro x141 x142) (FAndIntro x81 x82) = False;
equal_fitch_rule (FAndIntro x81 x82) (FOrElim x131 x132 x133) = False;
equal_fitch_rule (FOrElim x131 x132 x133) (FAndIntro x81 x82) = False;
equal_fitch_rule (FAndIntro x81 x82) (FOrIntroR x12) = False;
equal_fitch_rule (FOrIntroR x12) (FAndIntro x81 x82) = False;
equal_fitch_rule (FAndIntro x81 x82) (FOrIntroL x11) = False;
equal_fitch_rule (FOrIntroL x11) (FAndIntro x81 x82) = False;
equal_fitch_rule (FAndIntro x81 x82) (FAndElimR x10) = False;
equal_fitch_rule (FAndElimR x10) (FAndIntro x81 x82) = False;
equal_fitch_rule (FAndIntro x81 x82) (FAndElimL x9) = False;
equal_fitch_rule (FAndElimL x9) (FAndIntro x81 x82) = False;
equal_fitch_rule (FBotI x71 x72) (FReit x23) = False;
equal_fitch_rule (FReit x23) (FBotI x71 x72) = False;
equal_fitch_rule (FBotI x71 x72) (FEqElim x221 x222) = False;
equal_fitch_rule (FEqElim x221 x222) (FBotI x71 x72) = False;
equal_fitch_rule (FBotI x71 x72) FEqIntro = False;
equal_fitch_rule FEqIntro (FBotI x71 x72) = False;
equal_fitch_rule (FBotI x71 x72) (FExistsElim x201 x202) = False;
equal_fitch_rule (FExistsElim x201 x202) (FBotI x71 x72) = False;
equal_fitch_rule (FBotI x71 x72) (FExistsIntro x19) = False;
equal_fitch_rule (FExistsIntro x19) (FBotI x71 x72) = False;
equal_fitch_rule (FBotI x71 x72) (FForallIntro x18) = False;
equal_fitch_rule (FForallIntro x18) (FBotI x71 x72) = False;
equal_fitch_rule (FBotI x71 x72) (FForallElim x17) = False;
equal_fitch_rule (FForallElim x17) (FBotI x71 x72) = False;
equal_fitch_rule (FBotI x71 x72) (FIffElimR x16) = False;
equal_fitch_rule (FIffElimR x16) (FBotI x71 x72) = False;
equal_fitch_rule (FBotI x71 x72) (FIffElimL x15) = False;
equal_fitch_rule (FIffElimL x15) (FBotI x71 x72) = False;
equal_fitch_rule (FBotI x71 x72) (FIffIntro x141 x142) = False;
equal_fitch_rule (FIffIntro x141 x142) (FBotI x71 x72) = False;
equal_fitch_rule (FBotI x71 x72) (FOrElim x131 x132 x133) = False;
equal_fitch_rule (FOrElim x131 x132 x133) (FBotI x71 x72) = False;
equal_fitch_rule (FBotI x71 x72) (FOrIntroR x12) = False;
equal_fitch_rule (FOrIntroR x12) (FBotI x71 x72) = False;
equal_fitch_rule (FBotI x71 x72) (FOrIntroL x11) = False;
equal_fitch_rule (FOrIntroL x11) (FBotI x71 x72) = False;
equal_fitch_rule (FBotI x71 x72) (FAndElimR x10) = False;
equal_fitch_rule (FAndElimR x10) (FBotI x71 x72) = False;
equal_fitch_rule (FBotI x71 x72) (FAndElimL x9) = False;
equal_fitch_rule (FAndElimL x9) (FBotI x71 x72) = False;
equal_fitch_rule (FBotI x71 x72) (FAndIntro x81 x82) = False;
equal_fitch_rule (FAndIntro x81 x82) (FBotI x71 x72) = False;
equal_fitch_rule (FDN x6) (FReit x23) = False;
equal_fitch_rule (FReit x23) (FDN x6) = False;
equal_fitch_rule (FDN x6) (FEqElim x221 x222) = False;
equal_fitch_rule (FEqElim x221 x222) (FDN x6) = False;
equal_fitch_rule (FDN x6) FEqIntro = False;
equal_fitch_rule FEqIntro (FDN x6) = False;
equal_fitch_rule (FDN x6) (FExistsElim x201 x202) = False;
equal_fitch_rule (FExistsElim x201 x202) (FDN x6) = False;
equal_fitch_rule (FDN x6) (FExistsIntro x19) = False;
equal_fitch_rule (FExistsIntro x19) (FDN x6) = False;
equal_fitch_rule (FDN x6) (FForallIntro x18) = False;
equal_fitch_rule (FForallIntro x18) (FDN x6) = False;
equal_fitch_rule (FDN x6) (FForallElim x17) = False;
equal_fitch_rule (FForallElim x17) (FDN x6) = False;
equal_fitch_rule (FDN x6) (FIffElimR x16) = False;
equal_fitch_rule (FIffElimR x16) (FDN x6) = False;
equal_fitch_rule (FDN x6) (FIffElimL x15) = False;
equal_fitch_rule (FIffElimL x15) (FDN x6) = False;
equal_fitch_rule (FDN x6) (FIffIntro x141 x142) = False;
equal_fitch_rule (FIffIntro x141 x142) (FDN x6) = False;
equal_fitch_rule (FDN x6) (FOrElim x131 x132 x133) = False;
equal_fitch_rule (FOrElim x131 x132 x133) (FDN x6) = False;
equal_fitch_rule (FDN x6) (FOrIntroR x12) = False;
equal_fitch_rule (FOrIntroR x12) (FDN x6) = False;
equal_fitch_rule (FDN x6) (FOrIntroL x11) = False;
equal_fitch_rule (FOrIntroL x11) (FDN x6) = False;
equal_fitch_rule (FDN x6) (FAndElimR x10) = False;
equal_fitch_rule (FAndElimR x10) (FDN x6) = False;
equal_fitch_rule (FDN x6) (FAndElimL x9) = False;
equal_fitch_rule (FAndElimL x9) (FDN x6) = False;
equal_fitch_rule (FDN x6) (FAndIntro x81 x82) = False;
equal_fitch_rule (FAndIntro x81 x82) (FDN x6) = False;
equal_fitch_rule (FDN x6) (FBotI x71 x72) = False;
equal_fitch_rule (FBotI x71 x72) (FDN x6) = False;
equal_fitch_rule (FRAA x5) (FReit x23) = False;
equal_fitch_rule (FReit x23) (FRAA x5) = False;
equal_fitch_rule (FRAA x5) (FEqElim x221 x222) = False;
equal_fitch_rule (FEqElim x221 x222) (FRAA x5) = False;
equal_fitch_rule (FRAA x5) FEqIntro = False;
equal_fitch_rule FEqIntro (FRAA x5) = False;
equal_fitch_rule (FRAA x5) (FExistsElim x201 x202) = False;
equal_fitch_rule (FExistsElim x201 x202) (FRAA x5) = False;
equal_fitch_rule (FRAA x5) (FExistsIntro x19) = False;
equal_fitch_rule (FExistsIntro x19) (FRAA x5) = False;
equal_fitch_rule (FRAA x5) (FForallIntro x18) = False;
equal_fitch_rule (FForallIntro x18) (FRAA x5) = False;
equal_fitch_rule (FRAA x5) (FForallElim x17) = False;
equal_fitch_rule (FForallElim x17) (FRAA x5) = False;
equal_fitch_rule (FRAA x5) (FIffElimR x16) = False;
equal_fitch_rule (FIffElimR x16) (FRAA x5) = False;
equal_fitch_rule (FRAA x5) (FIffElimL x15) = False;
equal_fitch_rule (FIffElimL x15) (FRAA x5) = False;
equal_fitch_rule (FRAA x5) (FIffIntro x141 x142) = False;
equal_fitch_rule (FIffIntro x141 x142) (FRAA x5) = False;
equal_fitch_rule (FRAA x5) (FOrElim x131 x132 x133) = False;
equal_fitch_rule (FOrElim x131 x132 x133) (FRAA x5) = False;
equal_fitch_rule (FRAA x5) (FOrIntroR x12) = False;
equal_fitch_rule (FOrIntroR x12) (FRAA x5) = False;
equal_fitch_rule (FRAA x5) (FOrIntroL x11) = False;
equal_fitch_rule (FOrIntroL x11) (FRAA x5) = False;
equal_fitch_rule (FRAA x5) (FAndElimR x10) = False;
equal_fitch_rule (FAndElimR x10) (FRAA x5) = False;
equal_fitch_rule (FRAA x5) (FAndElimL x9) = False;
equal_fitch_rule (FAndElimL x9) (FRAA x5) = False;
equal_fitch_rule (FRAA x5) (FAndIntro x81 x82) = False;
equal_fitch_rule (FAndIntro x81 x82) (FRAA x5) = False;
equal_fitch_rule (FRAA x5) (FBotI x71 x72) = False;
equal_fitch_rule (FBotI x71 x72) (FRAA x5) = False;
equal_fitch_rule (FRAA x5) (FDN x6) = False;
equal_fitch_rule (FDN x6) (FRAA x5) = False;
equal_fitch_rule (FCP x4) (FReit x23) = False;
equal_fitch_rule (FReit x23) (FCP x4) = False;
equal_fitch_rule (FCP x4) (FEqElim x221 x222) = False;
equal_fitch_rule (FEqElim x221 x222) (FCP x4) = False;
equal_fitch_rule (FCP x4) FEqIntro = False;
equal_fitch_rule FEqIntro (FCP x4) = False;
equal_fitch_rule (FCP x4) (FExistsElim x201 x202) = False;
equal_fitch_rule (FExistsElim x201 x202) (FCP x4) = False;
equal_fitch_rule (FCP x4) (FExistsIntro x19) = False;
equal_fitch_rule (FExistsIntro x19) (FCP x4) = False;
equal_fitch_rule (FCP x4) (FForallIntro x18) = False;
equal_fitch_rule (FForallIntro x18) (FCP x4) = False;
equal_fitch_rule (FCP x4) (FForallElim x17) = False;
equal_fitch_rule (FForallElim x17) (FCP x4) = False;
equal_fitch_rule (FCP x4) (FIffElimR x16) = False;
equal_fitch_rule (FIffElimR x16) (FCP x4) = False;
equal_fitch_rule (FCP x4) (FIffElimL x15) = False;
equal_fitch_rule (FIffElimL x15) (FCP x4) = False;
equal_fitch_rule (FCP x4) (FIffIntro x141 x142) = False;
equal_fitch_rule (FIffIntro x141 x142) (FCP x4) = False;
equal_fitch_rule (FCP x4) (FOrElim x131 x132 x133) = False;
equal_fitch_rule (FOrElim x131 x132 x133) (FCP x4) = False;
equal_fitch_rule (FCP x4) (FOrIntroR x12) = False;
equal_fitch_rule (FOrIntroR x12) (FCP x4) = False;
equal_fitch_rule (FCP x4) (FOrIntroL x11) = False;
equal_fitch_rule (FOrIntroL x11) (FCP x4) = False;
equal_fitch_rule (FCP x4) (FAndElimR x10) = False;
equal_fitch_rule (FAndElimR x10) (FCP x4) = False;
equal_fitch_rule (FCP x4) (FAndElimL x9) = False;
equal_fitch_rule (FAndElimL x9) (FCP x4) = False;
equal_fitch_rule (FCP x4) (FAndIntro x81 x82) = False;
equal_fitch_rule (FAndIntro x81 x82) (FCP x4) = False;
equal_fitch_rule (FCP x4) (FBotI x71 x72) = False;
equal_fitch_rule (FBotI x71 x72) (FCP x4) = False;
equal_fitch_rule (FCP x4) (FDN x6) = False;
equal_fitch_rule (FDN x6) (FCP x4) = False;
equal_fitch_rule (FCP x4) (FRAA x5) = False;
equal_fitch_rule (FRAA x5) (FCP x4) = False;
equal_fitch_rule (FMP x31 x32) (FReit x23) = False;
equal_fitch_rule (FReit x23) (FMP x31 x32) = False;
equal_fitch_rule (FMP x31 x32) (FEqElim x221 x222) = False;
equal_fitch_rule (FEqElim x221 x222) (FMP x31 x32) = False;
equal_fitch_rule (FMP x31 x32) FEqIntro = False;
equal_fitch_rule FEqIntro (FMP x31 x32) = False;
equal_fitch_rule (FMP x31 x32) (FExistsElim x201 x202) = False;
equal_fitch_rule (FExistsElim x201 x202) (FMP x31 x32) = False;
equal_fitch_rule (FMP x31 x32) (FExistsIntro x19) = False;
equal_fitch_rule (FExistsIntro x19) (FMP x31 x32) = False;
equal_fitch_rule (FMP x31 x32) (FForallIntro x18) = False;
equal_fitch_rule (FForallIntro x18) (FMP x31 x32) = False;
equal_fitch_rule (FMP x31 x32) (FForallElim x17) = False;
equal_fitch_rule (FForallElim x17) (FMP x31 x32) = False;
equal_fitch_rule (FMP x31 x32) (FIffElimR x16) = False;
equal_fitch_rule (FIffElimR x16) (FMP x31 x32) = False;
equal_fitch_rule (FMP x31 x32) (FIffElimL x15) = False;
equal_fitch_rule (FIffElimL x15) (FMP x31 x32) = False;
equal_fitch_rule (FMP x31 x32) (FIffIntro x141 x142) = False;
equal_fitch_rule (FIffIntro x141 x142) (FMP x31 x32) = False;
equal_fitch_rule (FMP x31 x32) (FOrElim x131 x132 x133) = False;
equal_fitch_rule (FOrElim x131 x132 x133) (FMP x31 x32) = False;
equal_fitch_rule (FMP x31 x32) (FOrIntroR x12) = False;
equal_fitch_rule (FOrIntroR x12) (FMP x31 x32) = False;
equal_fitch_rule (FMP x31 x32) (FOrIntroL x11) = False;
equal_fitch_rule (FOrIntroL x11) (FMP x31 x32) = False;
equal_fitch_rule (FMP x31 x32) (FAndElimR x10) = False;
equal_fitch_rule (FAndElimR x10) (FMP x31 x32) = False;
equal_fitch_rule (FMP x31 x32) (FAndElimL x9) = False;
equal_fitch_rule (FAndElimL x9) (FMP x31 x32) = False;
equal_fitch_rule (FMP x31 x32) (FAndIntro x81 x82) = False;
equal_fitch_rule (FAndIntro x81 x82) (FMP x31 x32) = False;
equal_fitch_rule (FMP x31 x32) (FBotI x71 x72) = False;
equal_fitch_rule (FBotI x71 x72) (FMP x31 x32) = False;
equal_fitch_rule (FMP x31 x32) (FDN x6) = False;
equal_fitch_rule (FDN x6) (FMP x31 x32) = False;
equal_fitch_rule (FMP x31 x32) (FRAA x5) = False;
equal_fitch_rule (FRAA x5) (FMP x31 x32) = False;
equal_fitch_rule (FMP x31 x32) (FCP x4) = False;
equal_fitch_rule (FCP x4) (FMP x31 x32) = False;
equal_fitch_rule FAssume (FReit x23) = False;
equal_fitch_rule (FReit x23) FAssume = False;
equal_fitch_rule FAssume (FEqElim x221 x222) = False;
equal_fitch_rule (FEqElim x221 x222) FAssume = False;
equal_fitch_rule FAssume FEqIntro = False;
equal_fitch_rule FEqIntro FAssume = False;
equal_fitch_rule FAssume (FExistsElim x201 x202) = False;
equal_fitch_rule (FExistsElim x201 x202) FAssume = False;
equal_fitch_rule FAssume (FExistsIntro x19) = False;
equal_fitch_rule (FExistsIntro x19) FAssume = False;
equal_fitch_rule FAssume (FForallIntro x18) = False;
equal_fitch_rule (FForallIntro x18) FAssume = False;
equal_fitch_rule FAssume (FForallElim x17) = False;
equal_fitch_rule (FForallElim x17) FAssume = False;
equal_fitch_rule FAssume (FIffElimR x16) = False;
equal_fitch_rule (FIffElimR x16) FAssume = False;
equal_fitch_rule FAssume (FIffElimL x15) = False;
equal_fitch_rule (FIffElimL x15) FAssume = False;
equal_fitch_rule FAssume (FIffIntro x141 x142) = False;
equal_fitch_rule (FIffIntro x141 x142) FAssume = False;
equal_fitch_rule FAssume (FOrElim x131 x132 x133) = False;
equal_fitch_rule (FOrElim x131 x132 x133) FAssume = False;
equal_fitch_rule FAssume (FOrIntroR x12) = False;
equal_fitch_rule (FOrIntroR x12) FAssume = False;
equal_fitch_rule FAssume (FOrIntroL x11) = False;
equal_fitch_rule (FOrIntroL x11) FAssume = False;
equal_fitch_rule FAssume (FAndElimR x10) = False;
equal_fitch_rule (FAndElimR x10) FAssume = False;
equal_fitch_rule FAssume (FAndElimL x9) = False;
equal_fitch_rule (FAndElimL x9) FAssume = False;
equal_fitch_rule FAssume (FAndIntro x81 x82) = False;
equal_fitch_rule (FAndIntro x81 x82) FAssume = False;
equal_fitch_rule FAssume (FBotI x71 x72) = False;
equal_fitch_rule (FBotI x71 x72) FAssume = False;
equal_fitch_rule FAssume (FDN x6) = False;
equal_fitch_rule (FDN x6) FAssume = False;
equal_fitch_rule FAssume (FRAA x5) = False;
equal_fitch_rule (FRAA x5) FAssume = False;
equal_fitch_rule FAssume (FCP x4) = False;
equal_fitch_rule (FCP x4) FAssume = False;
equal_fitch_rule FAssume (FMP x31 x32) = False;
equal_fitch_rule (FMP x31 x32) FAssume = False;
equal_fitch_rule FPremise (FReit x23) = False;
equal_fitch_rule (FReit x23) FPremise = False;
equal_fitch_rule FPremise (FEqElim x221 x222) = False;
equal_fitch_rule (FEqElim x221 x222) FPremise = False;
equal_fitch_rule FPremise FEqIntro = False;
equal_fitch_rule FEqIntro FPremise = False;
equal_fitch_rule FPremise (FExistsElim x201 x202) = False;
equal_fitch_rule (FExistsElim x201 x202) FPremise = False;
equal_fitch_rule FPremise (FExistsIntro x19) = False;
equal_fitch_rule (FExistsIntro x19) FPremise = False;
equal_fitch_rule FPremise (FForallIntro x18) = False;
equal_fitch_rule (FForallIntro x18) FPremise = False;
equal_fitch_rule FPremise (FForallElim x17) = False;
equal_fitch_rule (FForallElim x17) FPremise = False;
equal_fitch_rule FPremise (FIffElimR x16) = False;
equal_fitch_rule (FIffElimR x16) FPremise = False;
equal_fitch_rule FPremise (FIffElimL x15) = False;
equal_fitch_rule (FIffElimL x15) FPremise = False;
equal_fitch_rule FPremise (FIffIntro x141 x142) = False;
equal_fitch_rule (FIffIntro x141 x142) FPremise = False;
equal_fitch_rule FPremise (FOrElim x131 x132 x133) = False;
equal_fitch_rule (FOrElim x131 x132 x133) FPremise = False;
equal_fitch_rule FPremise (FOrIntroR x12) = False;
equal_fitch_rule (FOrIntroR x12) FPremise = False;
equal_fitch_rule FPremise (FOrIntroL x11) = False;
equal_fitch_rule (FOrIntroL x11) FPremise = False;
equal_fitch_rule FPremise (FAndElimR x10) = False;
equal_fitch_rule (FAndElimR x10) FPremise = False;
equal_fitch_rule FPremise (FAndElimL x9) = False;
equal_fitch_rule (FAndElimL x9) FPremise = False;
equal_fitch_rule FPremise (FAndIntro x81 x82) = False;
equal_fitch_rule (FAndIntro x81 x82) FPremise = False;
equal_fitch_rule FPremise (FBotI x71 x72) = False;
equal_fitch_rule (FBotI x71 x72) FPremise = False;
equal_fitch_rule FPremise (FDN x6) = False;
equal_fitch_rule (FDN x6) FPremise = False;
equal_fitch_rule FPremise (FRAA x5) = False;
equal_fitch_rule (FRAA x5) FPremise = False;
equal_fitch_rule FPremise (FCP x4) = False;
equal_fitch_rule (FCP x4) FPremise = False;
equal_fitch_rule FPremise (FMP x31 x32) = False;
equal_fitch_rule (FMP x31 x32) FPremise = False;
equal_fitch_rule FPremise FAssume = False;
equal_fitch_rule FAssume FPremise = False;
equal_fitch_rule (FReit x23) (FReit y23) = equal_nat x23 y23;
equal_fitch_rule (FEqElim x221 x222) (FEqElim y221 y222) =
  equal_nat x221 y221 && equal_nat x222 y222;
equal_fitch_rule (FExistsElim x201 x202) (FExistsElim y201 y202) =
  equal_nat x201 y201 && x202 == y202;
equal_fitch_rule (FExistsIntro x19) (FExistsIntro y19) = equal_nat x19 y19;
equal_fitch_rule (FForallIntro x18) (FForallIntro y18) = equal_nat x18 y18;
equal_fitch_rule (FForallElim x17) (FForallElim y17) = equal_nat x17 y17;
equal_fitch_rule (FIffElimR x16) (FIffElimR y16) = equal_nat x16 y16;
equal_fitch_rule (FIffElimL x15) (FIffElimL y15) = equal_nat x15 y15;
equal_fitch_rule (FIffIntro x141 x142) (FIffIntro y141 y142) =
  equal_nat x141 y141 && equal_nat x142 y142;
equal_fitch_rule (FOrElim x131 x132 x133) (FOrElim y131 y132 y133) =
  equal_nat x131 y131 && x132 == y132 && x133 == y133;
equal_fitch_rule (FOrIntroR x12) (FOrIntroR y12) = equal_nat x12 y12;
equal_fitch_rule (FOrIntroL x11) (FOrIntroL y11) = equal_nat x11 y11;
equal_fitch_rule (FAndElimR x10) (FAndElimR y10) = equal_nat x10 y10;
equal_fitch_rule (FAndElimL x9) (FAndElimL y9) = equal_nat x9 y9;
equal_fitch_rule (FAndIntro x81 x82) (FAndIntro y81 y82) =
  equal_nat x81 y81 && equal_nat x82 y82;
equal_fitch_rule (FBotI x71 x72) (FBotI y71 y72) =
  equal_nat x71 y71 && equal_nat x72 y72;
equal_fitch_rule (FDN x6) (FDN y6) = equal_nat x6 y6;
equal_fitch_rule (FRAA x5) (FRAA y5) = x5 == y5;
equal_fitch_rule (FCP x4) (FCP y4) = x4 == y4;
equal_fitch_rule (FMP x31 x32) (FMP y31 y32) =
  equal_nat x31 y31 && equal_nat x32 y32;
equal_fitch_rule FEqIntro FEqIntro = True;
equal_fitch_rule FAssume FAssume = True;
equal_fitch_rule FPremise FPremise = True;

noAssumeLinesItem :: Fitch_item -> Bool;
noAssumeLinesItem (FLine uu uv r) = not (equal_fitch_rule r FAssume);
noAssumeLinesItem (FSub s) = noAssumeLinesSub s;

noAssumeLinesSub :: Subproof -> Bool;
noAssumeLinesSub (Subproof uw ux body) = all noAssumeLinesItem body;

lastIsLineItem :: Fitch_item -> Bool;
lastIsLineItem (FLine uu uv uw) = True;
lastIsLineItem (FSub s) = lastIsLineSub s;

lastIsLineSub :: Subproof -> Bool;
lastIsLineSub (Subproof ux uy body) =
  all lastIsLineItem body && (null body || (case last body of {
     FLine _ _ _ -> True;
     FSub _ -> False;
   }));

concludesAtTop :: [Fitch_item] -> Bool;
concludesAtTop f = null f || (case last f of {
                               FLine _ _ _ -> True;
                               FSub _ -> False;
                             });

flRule :: Fline -> Fitch_rule;
flRule (FL x1 x2 x3 x4) = x3;

flatItem :: Fitch_item -> [Nat] -> [Fline];
flatItem (FLine n f r) path = [FL n f r path];
flatItem (FSub s) path = flatSub s path;

flatSub :: Subproof -> [Nat] -> [Fline];
flatSub (Subproof a fa body) path =
  FL a fa FAssume (path ++ [a]) :
    concatMap (\ it -> flatItem it (path ++ [a])) body;

flatten :: [Fitch_item] -> [Fline];
flatten f = concatMap (\ it -> flatItem it []) f;

premisesFirst :: [Fitch_item] -> Bool;
premisesFirst f =
  all (\ fl -> not (equal_fitch_rule (flRule fl) FPremise))
    (dropWhile (\ fl -> equal_fitch_rule (flRule fl) FPremise) (flatten f));

flScope :: Fline -> [Nat];
flScope (FL x1 x2 x3 x4) = x4;

fCitedLines :: Fitch_rule -> [Nat];
fCitedLines FPremise = [];
fCitedLines FAssume = [];
fCitedLines (FMP i j) = [i, j];
fCitedLines (FCP uu) = [];
fCitedLines (FRAA uv) = [];
fCitedLines (FDN i) = [i];
fCitedLines (FBotI i j) = [i, j];
fCitedLines (FAndIntro i j) = [i, j];
fCitedLines (FAndElimL i) = [i];
fCitedLines (FAndElimR i) = [i];
fCitedLines (FOrIntroL i) = [i];
fCitedLines (FOrIntroR i) = [i];
fCitedLines (FOrElim d uw ux) = [d];
fCitedLines (FIffIntro i j) = [i, j];
fCitedLines (FIffElimL i) = [i];
fCitedLines (FIffElimR i) = [i];
fCitedLines (FForallElim i) = [i];
fCitedLines (FForallIntro i) = [i];
fCitedLines (FExistsIntro i) = [i];
fCitedLines (FExistsElim m uy) = [m];
fCitedLines FEqIntro = [];
fCitedLines (FEqElim i j) = [i, j];
fCitedLines (FReit i) = [i];

fCitedSubs :: Fitch_rule -> [(Nat, Nat)];
fCitedSubs (FCP s) = [s];
fCitedSubs (FRAA s) = [s];
fCitedSubs (FOrElim uu s1 s2) = [s1, s2];
fCitedSubs (FExistsElim uv s) = [s];
fCitedSubs FPremise = [];
fCitedSubs FAssume = [];
fCitedSubs (FMP v va) = [];
fCitedSubs (FDN v) = [];
fCitedSubs (FBotI v va) = [];
fCitedSubs (FAndIntro v va) = [];
fCitedSubs (FAndElimL v) = [];
fCitedSubs (FAndElimR v) = [];
fCitedSubs (FOrIntroL v) = [];
fCitedSubs (FOrIntroR v) = [];
fCitedSubs (FIffIntro v va) = [];
fCitedSubs (FIffElimL v) = [];
fCitedSubs (FIffElimR v) = [];
fCitedSubs (FForallElim v) = [];
fCitedSubs (FForallIntro v) = [];
fCitedSubs (FExistsIntro v) = [];
fCitedSubs FEqIntro = [];
fCitedSubs (FEqElim v va) = [];
fCitedSubs (FReit v) = [];

is_prefix :: forall a. (Eq a) => [a] -> [a] -> Bool;
is_prefix [] ys = True;
is_prefix (x : xs) [] = False;
is_prefix (x : xs) (y : ys) = x == y && is_prefix xs ys;

subLastLine :: Subproof -> Nat;
subLastLine s = flNum (last (flatSub s []));

subrefsItem :: Fitch_item -> [Nat] -> [((Nat, Nat), [Nat])];
subrefsItem (FLine uu uv uw) path = [];
subrefsItem (FSub s) path = subrefsSub s path;

subrefsSub :: Subproof -> [Nat] -> [((Nat, Nat), [Nat])];
subrefsSub (Subproof a fa body) path =
  ((a, subLastLine (Subproof a fa body)), path) :
    concatMap (\ it -> subrefsItem it (path ++ [a])) body;

subrefs :: [Fitch_item] -> [((Nat, Nat), [Nat])];
subrefs f = concatMap (\ it -> subrefsItem it []) f;

citationOK :: [Fitch_item] -> Fline -> Bool;
citationOK f fl =
  all (\ m ->
        less_nat m (flNum fl) &&
          (case findFL (flatten f) m of {
            Nothing -> False;
            Just fla -> is_prefix (flScope fla) (flScope fl);
          }))
    (fCitedLines (flRule fl)) &&
    all (\ (a, c) ->
          less_nat c (flNum fl) && membera (subrefs f) ((a, c), flScope fl))
      (fCitedSubs (flRule fl));

fitchWF :: [Fitch_item] -> Bool;
fitchWF f =
  sorted_wrt less_nat (map flNum (flatten f)) &&
    all noAssumeLinesItem f &&
      all (\ fl ->
            (if equal_fitch_rule (flRule fl) FPremise then null (flScope fl)
              else True))
        (flatten f) &&
        premisesFirst f &&
          all lastIsLineItem f &&
            concludesAtTop f && all (citationOK f) (flatten f);

premiseLines :: [Fitch_item] -> [Nat];
premiseLines f =
  map_filter
    (\ x ->
      (if equal_fitch_rule (flRule x) FPremise then Just (flNum x)
        else Nothing))
    (flatten f);

scopePath :: [Fitch_item] -> Nat -> [Nat];
scopePath f n = (case findFL (flatten f) n of {
                  Nothing -> [];
                  Just a -> flScope a;
                });

scopeOf :: [Fitch_item] -> Nat -> Set Nat;
scopeOf f n = sup_set (Set (premiseLines f)) (Set (scopePath f n));

hlCorrect :: [Hl_line] -> Bool;
hlCorrect p = all (hlLineOK p) p;

depFms :: [Pline] -> Set Nat -> [Fm];
depFms e g =
  map_filter
    (\ x -> (if member (lineNumber x) g then Just (formula x) else Nothing)) e;

depSrc :: [Pline] -> Nat -> Set Nat -> [Fm];
depSrc e n g = depFms e g;

references :: Pline -> Set Nat;
references (ProofLine x1 x2 x3 x4) = x4;

depsAt :: [Pline] -> Nat -> Set Nat;
depsAt p n = (case lookupLine p n of {
               Nothing -> bot_set;
               Just a -> references a;
             });

citedLines :: Justa -> [Nat];
citedLines Assumption = [];
citedLines (MP i j) = [i, j];
citedLines (CP a c) = [a, c];
citedLines (RAA a c) = [a, c];
citedLines (DN i) = [i];
citedLines (BotI i j) = [i, j];
citedLines (AndIntro i j) = [i, j];
citedLines (AndElimL i) = [i];
citedLines (AndElimR i) = [i];
citedLines (OrIntroL i) = [i];
citedLines (OrIntroR i) = [i];
citedLines (OrElim d a1 c1 a2 c2) = [d, a1, c1, a2, c2];
citedLines (IffIntro i j) = [i, j];
citedLines (IffElimL i) = [i];
citedLines (IffElimR i) = [i];
citedLines (ForallElim i) = [i];
citedLines (ForallIntro i) = [i];
citedLines (ExistsIntro i) = [i];
citedLines (ExistsElim m a c) = [m, a, c];
citedLines EqIntro = [];
citedLines (EqElim i j) = [i, j];
citedLines (Reit i) = [i];

depsOf :: (Nat -> Set Nat) -> Justa -> Nat -> Set Nat;
depsOf look j self =
  (case j of {
    Assumption -> insert self bot_set;
    MP _ _ -> sup_seta (Set (map look (citedLines j)));
    CP a c -> remove a (look c);
    RAA a c -> remove a (look c);
    DN _ -> sup_seta (Set (map look (citedLines j)));
    BotI _ _ -> sup_seta (Set (map look (citedLines j)));
    AndIntro _ _ -> sup_seta (Set (map look (citedLines j)));
    AndElimL _ -> sup_seta (Set (map look (citedLines j)));
    AndElimR _ -> sup_seta (Set (map look (citedLines j)));
    OrIntroL _ -> sup_seta (Set (map look (citedLines j)));
    OrIntroR _ -> sup_seta (Set (map look (citedLines j)));
    OrElim d a1 c1 a2 c2 ->
      sup_set (sup_set (look d) (remove a1 (look c1))) (remove a2 (look c2));
    IffIntro _ _ -> sup_seta (Set (map look (citedLines j)));
    IffElimL _ -> sup_seta (Set (map look (citedLines j)));
    IffElimR _ -> sup_seta (Set (map look (citedLines j)));
    ForallElim _ -> sup_seta (Set (map look (citedLines j)));
    ForallIntro _ -> sup_seta (Set (map look (citedLines j)));
    ExistsIntro _ -> sup_seta (Set (map look (citedLines j)));
    ExistsElim m a c -> sup_set (look m) (remove a (look c));
    EqIntro -> bot_set;
    EqElim _ _ -> sup_seta (Set (map look (citedLines j)));
    Reit _ -> sup_seta (Set (map look (citedLines j)));
  });

instOK :: String -> Fm -> Fm -> Bool;
instOK x p q =
  (if membera (fvs p) x then not (null (instWitnesses x p q))
    else equal_fm q p);

justification :: Pline -> Justa;
justification (ProofLine x1 x2 x3 x4) = x3;

justAt :: [Pline] -> Nat -> Maybe Justa;
justAt p n = map_option justification (lookupLine p n);

isAssumptionLine :: [Pline] -> Nat -> Bool;
isAssumptionLine e a = justAt e a == Just Assumption;

ruleOK :: [Pline] -> Fm -> [Fm] -> Justa -> Bool;
ruleOK e phi asa Assumption = True;
ruleOK e phi asa (MP i j) =
  (case fmAt e i of {
    Nothing -> False;
    Just (Atom _ _) -> False;
    Just (Eqf _ _) -> False;
    Just Bot -> False;
    Just (Neg _) -> False;
    Just (Conj _ _) -> False;
    Just (Disj _ _) -> False;
    Just (Impl p q) -> fmAt e j == Just p && equal_fm phi q;
    Just (Iff _ _) -> False;
    Just (Uni _ _) -> False;
    Just (Exi _ _) -> False;
  });
ruleOK e phi asa (CP a c) =
  isAssumptionLine e a && (case (fmAt e a, fmAt e c) of {
                            (Nothing, _) -> False;
                            (Just _, Nothing) -> False;
                            (Just p, Just q) -> equal_fm phi (Impl p q);
                          });
ruleOK e phi asa (RAA a c) =
  isAssumptionLine e a &&
    fmAt e c == Just Bot && (case fmAt e a of {
                              Nothing -> False;
                              Just p -> equal_fm phi (Neg p);
                            });
ruleOK e phi asa (DN i) = fmAt e i == Just (Neg (Neg phi));
ruleOK e phi asa (BotI i j) =
  equal_fm phi Bot && (case fmAt e i of {
                        Nothing -> False;
                        Just p -> fmAt e j == Just (Neg p);
                      });
ruleOK e phi asa (AndIntro i j) =
  (case phi of {
    Atom _ _ -> False;
    Eqf _ _ -> False;
    Bot -> False;
    Neg _ -> False;
    Conj p q -> fmAt e i == Just p && fmAt e j == Just q;
    Disj _ _ -> False;
    Impl _ _ -> False;
    Iff _ _ -> False;
    Uni _ _ -> False;
    Exi _ _ -> False;
  });
ruleOK e phi asa (AndElimL i) = (case fmAt e i of {
                                  Nothing -> False;
                                  Just (Atom _ _) -> False;
                                  Just (Eqf _ _) -> False;
                                  Just Bot -> False;
                                  Just (Neg _) -> False;
                                  Just (Conj p _) -> equal_fm phi p;
                                  Just (Disj _ _) -> False;
                                  Just (Impl _ _) -> False;
                                  Just (Iff _ _) -> False;
                                  Just (Uni _ _) -> False;
                                  Just (Exi _ _) -> False;
                                });
ruleOK e phi asa (AndElimR i) = (case fmAt e i of {
                                  Nothing -> False;
                                  Just (Atom _ _) -> False;
                                  Just (Eqf _ _) -> False;
                                  Just Bot -> False;
                                  Just (Neg _) -> False;
                                  Just (Conj _ a) -> equal_fm phi a;
                                  Just (Disj _ _) -> False;
                                  Just (Impl _ _) -> False;
                                  Just (Iff _ _) -> False;
                                  Just (Uni _ _) -> False;
                                  Just (Exi _ _) -> False;
                                });
ruleOK e phi asa (OrIntroL i) = (case phi of {
                                  Atom _ _ -> False;
                                  Eqf _ _ -> False;
                                  Bot -> False;
                                  Neg _ -> False;
                                  Conj _ _ -> False;
                                  Disj p _ -> fmAt e i == Just p;
                                  Impl _ _ -> False;
                                  Iff _ _ -> False;
                                  Uni _ _ -> False;
                                  Exi _ _ -> False;
                                });
ruleOK e phi asa (OrIntroR i) = (case phi of {
                                  Atom _ _ -> False;
                                  Eqf _ _ -> False;
                                  Bot -> False;
                                  Neg _ -> False;
                                  Conj _ _ -> False;
                                  Disj _ q -> fmAt e i == Just q;
                                  Impl _ _ -> False;
                                  Iff _ _ -> False;
                                  Uni _ _ -> False;
                                  Exi _ _ -> False;
                                });
ruleOK e phi asa (OrElim d a1 c1 a2 c2) =
  isAssumptionLine e a1 &&
    isAssumptionLine e a2 &&
      fmAt e c1 == Just phi &&
        fmAt e c2 == Just phi &&
          (case fmAt e d of {
            Nothing -> False;
            Just (Atom _ _) -> False;
            Just (Eqf _ _) -> False;
            Just Bot -> False;
            Just (Neg _) -> False;
            Just (Conj _ _) -> False;
            Just (Disj p q) -> fmAt e a1 == Just p && fmAt e a2 == Just q;
            Just (Impl _ _) -> False;
            Just (Iff _ _) -> False;
            Just (Uni _ _) -> False;
            Just (Exi _ _) -> False;
          });
ruleOK e phi asa (IffIntro i j) =
  (case phi of {
    Atom _ _ -> False;
    Eqf _ _ -> False;
    Bot -> False;
    Neg _ -> False;
    Conj _ _ -> False;
    Disj _ _ -> False;
    Impl _ _ -> False;
    Iff p q -> fmAt e i == Just (Impl p q) && fmAt e j == Just (Impl q p);
    Uni _ _ -> False;
    Exi _ _ -> False;
  });
ruleOK e phi asa (IffElimL i) = (case phi of {
                                  Atom _ _ -> False;
                                  Eqf _ _ -> False;
                                  Bot -> False;
                                  Neg _ -> False;
                                  Conj _ _ -> False;
                                  Disj _ _ -> False;
                                  Impl p q -> fmAt e i == Just (Iff p q);
                                  Iff _ _ -> False;
                                  Uni _ _ -> False;
                                  Exi _ _ -> False;
                                });
ruleOK e phi asa (IffElimR i) = (case phi of {
                                  Atom _ _ -> False;
                                  Eqf _ _ -> False;
                                  Bot -> False;
                                  Neg _ -> False;
                                  Conj _ _ -> False;
                                  Disj _ _ -> False;
                                  Impl q p -> fmAt e i == Just (Iff p q);
                                  Iff _ _ -> False;
                                  Uni _ _ -> False;
                                  Exi _ _ -> False;
                                });
ruleOK e phi asa (ForallElim i) = (case fmAt e i of {
                                    Nothing -> False;
                                    Just (Atom _ _) -> False;
                                    Just (Eqf _ _) -> False;
                                    Just Bot -> False;
                                    Just (Neg _) -> False;
                                    Just (Conj _ _) -> False;
                                    Just (Disj _ _) -> False;
                                    Just (Impl _ _) -> False;
                                    Just (Iff _ _) -> False;
                                    Just (Uni x p) -> instOK x p phi;
                                    Just (Exi _ _) -> False;
                                  });
ruleOK e phi asa (ForallIntro i) = (case (phi, fmAt e i) of {
                                     (Atom _ _, _) -> False;
                                     (Eqf _ _, _) -> False;
                                     (Bot, _) -> False;
                                     (Neg _, _) -> False;
                                     (Conj _ _, _) -> False;
                                     (Disj _ _, _) -> False;
                                     (Impl _ _, _) -> False;
                                     (Iff _ _, _) -> False;
                                     (Uni _ _, Nothing) -> False;
                                     (Uni x p, Just psi) -> genOK x p psi asa;
                                     (Exi _ _, _) -> False;
                                   });
ruleOK e phi asa (ExistsIntro i) = (case (phi, fmAt e i) of {
                                     (Atom _ _, _) -> False;
                                     (Eqf _ _, _) -> False;
                                     (Bot, _) -> False;
                                     (Neg _, _) -> False;
                                     (Conj _ _, _) -> False;
                                     (Disj _ _, _) -> False;
                                     (Impl _ _, _) -> False;
                                     (Iff _ _, _) -> False;
                                     (Uni _ _, _) -> False;
                                     (Exi _ _, Nothing) -> False;
                                     (Exi x p, Just a) -> instOK x p a;
                                   });
ruleOK e phi asa (ExistsElim m a c) =
  isAssumptionLine e a &&
    fmAt e c == Just phi &&
      (case (fmAt e m, fmAt e a) of {
        (Nothing, _) -> False;
        (Just (Atom _ _), _) -> False;
        (Just (Eqf _ _), _) -> False;
        (Just Bot, _) -> False;
        (Just (Neg _), _) -> False;
        (Just (Conj _ _), _) -> False;
        (Just (Disj _ _), _) -> False;
        (Just (Impl _ _), _) -> False;
        (Just (Iff _ _), _) -> False;
        (Just (Uni _ _), _) -> False;
        (Just (Exi _ _), Nothing) -> False;
        (Just (Exi x p), Just psi) -> witOK x p psi phi asa;
      });
ruleOK e phi asa EqIntro = (case phi of {
                             Atom _ _ -> False;
                             Eqf (Nm a) (Nm b) -> a == b;
                             Eqf (Nm _) (Vr _) -> False;
                             Eqf (Vr _) _ -> False;
                             Bot -> False;
                             Neg _ -> False;
                             Conj _ _ -> False;
                             Disj _ _ -> False;
                             Impl _ _ -> False;
                             Iff _ _ -> False;
                             Uni _ _ -> False;
                             Exi _ _ -> False;
                           });
ruleOK e phi asa (EqElim i j) =
  (case fmAt e i of {
    Nothing -> False;
    Just (Atom _ _) -> False;
    Just (Eqf (Nm a) (Nm b)) -> (case fmAt e j of {
                                  Nothing -> False;
                                  Just psi -> eqsub a b psi phi;
                                });
    Just (Eqf (Nm _) (Vr _)) -> False;
    Just (Eqf (Vr _) _) -> False;
    Just Bot -> False;
    Just (Neg _) -> False;
    Just (Conj _ _) -> False;
    Just (Disj _ _) -> False;
    Just (Impl _ _) -> False;
    Just (Iff _ _) -> False;
    Just (Uni _ _) -> False;
    Just (Exi _ _) -> False;
  });
ruleOK e phi asa (Reit i) = fmAt e i == Just phi;

showTrm :: Trm -> String;
showTrm (Nm a) = a;
showTrm (Vr x) = x;

symNot :: String;
symNot = isaSym "not";

symImp :: String;
symImp = isaSym "longrightarrow";

symIff :: String;
symIff = isaSym "longleftrightarrow";

symBot :: String;
symBot = isaSym "bottom";

symAnd :: String;
symAnd = isaSym "and";

symAll :: String;
symAll = isaSym "forall";

showFm :: Fm -> String;
showFm (Atom p []) = p;
showFm (Atom p (v : va)) =
  ((p ++ "(") ++ sepBy "," (map showTrm (v : va))) ++ ")";
showFm (Eqf s t) = (showTrm s ++ " = ") ++ showTrm t;
showFm Bot = symBot;
showFm (Neg Bot) = isaSym "top";
showFm (Neg (Atom v va)) = symNot ++ showFm (Atom v va);
showFm (Neg (Eqf v va)) = symNot ++ showFm (Eqf v va);
showFm (Neg (Neg v)) = symNot ++ showFm (Neg v);
showFm (Neg (Conj v va)) = symNot ++ showFm (Conj v va);
showFm (Neg (Disj v va)) = symNot ++ showFm (Disj v va);
showFm (Neg (Impl v va)) = symNot ++ showFm (Impl v va);
showFm (Neg (Iff v va)) = symNot ++ showFm (Iff v va);
showFm (Neg (Uni v va)) = symNot ++ showFm (Uni v va);
showFm (Neg (Exi v va)) = symNot ++ showFm (Exi v va);
showFm (Conj p q) =
  ((((("(" ++ showFm p) ++ " ") ++ symAnd) ++ " ") ++ showFm q) ++ ")";
showFm (Disj p q) =
  ((((("(" ++ showFm p) ++ " ") ++ symOr) ++ " ") ++ showFm q) ++ ")";
showFm (Impl p q) =
  ((((("(" ++ showFm p) ++ " ") ++ symImp) ++ " ") ++ showFm q) ++ ")";
showFm (Iff p q) =
  ((((("(" ++ showFm p) ++ " ") ++ symIff) ++ " ") ++ showFm q) ++ ")";
showFm (Uni x p) = ((symAll ++ x) ++ ". ") ++ showFm p;
showFm (Exi x p) = ((symEx ++ x) ++ ". ") ++ showFm p;

toLemmonRule :: Fitch_rule -> Justa;
toLemmonRule FPremise = Assumption;
toLemmonRule FAssume = Assumption;
toLemmonRule (FMP i j) = MP i j;
toLemmonRule (FCP (a, c)) = CP a c;
toLemmonRule (FRAA (a, c)) = RAA a c;
toLemmonRule (FDN i) = DN i;
toLemmonRule (FBotI i j) = BotI i j;
toLemmonRule (FAndIntro i j) = AndIntro i j;
toLemmonRule (FAndElimL i) = AndElimL i;
toLemmonRule (FAndElimR i) = AndElimR i;
toLemmonRule (FOrIntroL i) = OrIntroL i;
toLemmonRule (FOrIntroR i) = OrIntroR i;
toLemmonRule (FOrElim d (a1, c1) (a2, c2)) = OrElim d a1 c1 a2 c2;
toLemmonRule (FIffIntro i j) = IffIntro i j;
toLemmonRule (FIffElimL i) = IffElimL i;
toLemmonRule (FIffElimR i) = IffElimR i;
toLemmonRule (FForallElim i) = ForallElim i;
toLemmonRule (FForallIntro i) = ForallIntro i;
toLemmonRule (FExistsIntro i) = ExistsIntro i;
toLemmonRule (FExistsElim m (a, c)) = ExistsElim m a c;
toLemmonRule FEqIntro = EqIntro;
toLemmonRule (FEqElim i j) = EqElim i j;
toLemmonRule (FReit i) = Reit i;

flFm :: Fline -> Fm;
flFm (FL x1 x2 x3 x4) = x2;

deltaAux :: [Pline] -> [Fline] -> [Pline];
deltaAux acc [] = acc;
deltaAux acc (fl : fls) =
  deltaAux
    (acc ++
      [ProofLine (flNum fl) (flFm fl) (toLemmonRule (flRule fl))
         (depsOf (depsAt acc) (toLemmonRule (flRule fl)) (flNum fl))])
    fls;

delta :: [Fitch_item] -> [Pline];
delta f = deltaAux [] (flatten f);

scopeSrc :: [Fitch_item] -> [Pline] -> Nat -> Set Nat -> [Fm];
scopeSrc f e n g = depFms e (scopeOf f n);

dischargePairs :: Justa -> [(Nat, Nat)];
dischargePairs (CP a c) = [(a, c)];
dischargePairs (RAA a c) = [(a, c)];
dischargePairs (OrElim d a1 c1 a2 c2) = [(a1, c1), (a2, c2)];
dischargePairs (ExistsElim m a c) = [(a, c)];
dischargePairs Assumption = [];
dischargePairs (MP v va) = [];
dischargePairs (DN v) = [];
dischargePairs (BotI v va) = [];
dischargePairs (AndIntro v va) = [];
dischargePairs (AndElimL v) = [];
dischargePairs (AndElimR v) = [];
dischargePairs (OrIntroL v) = [];
dischargePairs (OrIntroR v) = [];
dischargePairs (IffIntro v va) = [];
dischargePairs (IffElimL v) = [];
dischargePairs (IffElimR v) = [];
dischargePairs (ForallElim v) = [];
dischargePairs (ForallIntro v) = [];
dischargePairs (ExistsIntro v) = [];
dischargePairs EqIntro = [];
dischargePairs (EqElim v va) = [];
dischargePairs (Reit v) = [];

boxesOf :: [Pline] -> [(Nat, Nat)];
boxesOf p = concatMap (\ l -> dischargePairs (justification l)) p;

boxPath :: [Pline] -> Nat -> [Nat];
boxPath p m =
  sort_key (\ x -> x)
    (map_filter
      (\ x ->
        (if less_eq_nat (fst x) m && less_eq_nat m (snd x) then Just (fst x)
          else Nothing))
      (boxesOf p));

maxlen :: [String] -> Nat;
maxlen used = foldr (\ a n -> max n (nlen a)) used zero_nat;

is_reit :: Justa -> Bool;
is_reit j = (case j of {
              Assumption -> False;
              MP _ _ -> False;
              CP _ _ -> False;
              RAA _ _ -> False;
              DN _ -> False;
              BotI _ _ -> False;
              AndIntro _ _ -> False;
              AndElimL _ -> False;
              AndElimR _ -> False;
              OrIntroL _ -> False;
              OrIntroR _ -> False;
              OrElim _ _ _ _ _ -> False;
              IffIntro _ _ -> False;
              IffElimL _ -> False;
              IffElimR _ -> False;
              ForallElim _ -> False;
              ForallIntro _ -> False;
              ExistsIntro _ -> False;
              ExistsElim _ _ _ -> False;
              EqIntro -> False;
              EqElim _ _ -> False;
              Reit _ -> True;
            });

apsnd :: forall a b c. (a -> b) -> (c, a) -> (c, b);
apsnd f (x, y) = (x, f y);

divmod_integer :: Integer -> Integer -> (Integer, Integer);
divmod_integer k l =
  (if k == (0 :: Integer) then ((0 :: Integer), (0 :: Integer))
    else (if (0 :: Integer) < l
           then (if (0 :: Integer) < k then divMod (abs k) (abs l)
                  else (case divMod (abs k) (abs l) of {
                         (r, s) ->
                           (if s == (0 :: Integer)
                             then (negate r, (0 :: Integer))
                             else (negate r - (1 :: Integer), l - s));
                       }))
           else (if l == (0 :: Integer) then ((0 :: Integer), k)
                  else apsnd negate
                         (if k < (0 :: Integer) then divMod (abs k) (abs l)
                           else (case divMod (abs k) (abs l) of {
                                  (r, s) ->
                                    (if s == (0 :: Integer)
                                      then (negate r, (0 :: Integer))
                                      else (negate r - (1 :: Integer),
     negate l - s));
                                })))));

modulo_integer :: Integer -> Integer -> Integer;
modulo_integer k l = snd (divmod_integer k l);

modulo_nat :: Nat -> Nat -> Nat;
modulo_nat m n = Nat (modulo_integer (integer_of_nat m) (integer_of_nat n));

divide_integer :: Integer -> Integer -> Integer;
divide_integer k l = fst (divmod_integer k l);

divide_nat :: Nat -> Nat -> Nat;
divide_nat m n = Nat (divide_integer (integer_of_nat m) (integer_of_nat n));

char_of_nat :: Nat -> Char;
char_of_nat = char_of_integer . integer_of_nat;

nat_of_integer :: Integer -> Nat;
nat_of_integer k = Nat (max (0 :: Integer) k);

digitsAux :: Nat -> [Char];
digitsAux v =
  (if equal_nat v zero_nat then []
    else digitsAux
           (divide_nat (suc (minus_nat v one_nat))
             (nat_of_integer (10 :: Integer))) ++
           [char_of_nat
              (plus_nat (nat_of_integer (48 :: Integer))
                (modulo_nat (suc (minus_nat v one_nat))
                  (nat_of_integer (10 :: Integer))))]);

showNat :: Nat -> String;
showNat n = (if equal_nat n zero_nat then "0" else implode (digitsAux n));

premEnv :: Deriv -> [(Nat, (Nat, Fm))];
premEnv d =
  map (\ ke -> (fst (snd ke), (suc (fst ke), snd (snd ke))))
    (enumerate zero_nat (sort_key fst (remdups (openAsms d))));

dischargedAssumps :: [Pline] -> [Nat];
dischargedAssumps p = map fst (boxesOf p);

unfoldD :: Nat -> [Pline] -> Nat -> Maybe Deriv;
unfoldD k p n =
  (if equal_nat k zero_nat then Nothing
    else (case lookupLine p n of {
           Nothing -> Nothing;
           Just l ->
             (case justification l of {
               Assumption ->
                 Just (Deriv (formula l)
                        (if membera (dischargedAssumps p) n then DAssume n
                          else DPremise n));
               MP i j ->
                 (case (unfoldD (minus_nat k one_nat) p i,
                         unfoldD (minus_nat k one_nat) p j)
                   of {
                   (Nothing, _) -> Nothing;
                   (Just _, Nothing) -> Nothing;
                   (Just e0, Just e1) -> Just (Deriv (formula l) (DMP e0 e1));
                 });
               CP a c ->
                 (case (fmAt p a, unfoldD (minus_nat k one_nat) p c) of {
                   (Nothing, _) -> Nothing;
                   (Just _, Nothing) -> Nothing;
                   (Just g0, Just e1) -> Just (Deriv (formula l) (DCP a g0 e1));
                 });
               RAA a c ->
                 (case (fmAt p a, unfoldD (minus_nat k one_nat) p c) of {
                   (Nothing, _) -> Nothing;
                   (Just _, Nothing) -> Nothing;
                   (Just g0, Just e1) ->
                     Just (Deriv (formula l) (DRAA a g0 e1));
                 });
               DN i -> (case unfoldD (minus_nat k one_nat) p i of {
                         Nothing -> Nothing;
                         Just e0 -> Just (Deriv (formula l) (DDN e0));
                       });
               BotI i j ->
                 (case (unfoldD (minus_nat k one_nat) p i,
                         unfoldD (minus_nat k one_nat) p j)
                   of {
                   (Nothing, _) -> Nothing;
                   (Just _, Nothing) -> Nothing;
                   (Just e0, Just e1) -> Just (Deriv (formula l) (DBotI e0 e1));
                 });
               AndIntro i j ->
                 (case (unfoldD (minus_nat k one_nat) p i,
                         unfoldD (minus_nat k one_nat) p j)
                   of {
                   (Nothing, _) -> Nothing;
                   (Just _, Nothing) -> Nothing;
                   (Just e0, Just e1) ->
                     Just (Deriv (formula l) (DAndIntro e0 e1));
                 });
               AndElimL i ->
                 (case unfoldD (minus_nat k one_nat) p i of {
                   Nothing -> Nothing;
                   Just e0 -> Just (Deriv (formula l) (DAndElimL e0));
                 });
               AndElimR i ->
                 (case unfoldD (minus_nat k one_nat) p i of {
                   Nothing -> Nothing;
                   Just e0 -> Just (Deriv (formula l) (DAndElimR e0));
                 });
               OrIntroL i ->
                 (case unfoldD (minus_nat k one_nat) p i of {
                   Nothing -> Nothing;
                   Just e0 -> Just (Deriv (formula l) (DOrIntroL e0));
                 });
               OrIntroR i ->
                 (case unfoldD (minus_nat k one_nat) p i of {
                   Nothing -> Nothing;
                   Just e0 -> Just (Deriv (formula l) (DOrIntroR e0));
                 });
               OrElim d a1 c1 a2 c2 ->
                 (case (unfoldD (minus_nat k one_nat) p d,
                         (fmAt p a1,
                           (unfoldD (minus_nat k one_nat) p c1,
                             (fmAt p a2, unfoldD (minus_nat k one_nat) p c2))))
                   of {
                   (Nothing, _) -> Nothing;
                   (Just _, (Nothing, _)) -> Nothing;
                   (Just _, (Just _, (Nothing, _))) -> Nothing;
                   (Just _, (Just _, (Just _, (Nothing, _)))) -> Nothing;
                   (Just _, (Just _, (Just _, (Just _, Nothing)))) -> Nothing;
                   (Just e0, (Just g1, (Just e2, (Just g3, Just e4)))) ->
                     Just (Deriv (formula l) (DOrElim e0 a1 g1 e2 a2 g3 e4));
                 });
               IffIntro i j ->
                 (case (unfoldD (minus_nat k one_nat) p i,
                         unfoldD (minus_nat k one_nat) p j)
                   of {
                   (Nothing, _) -> Nothing;
                   (Just _, Nothing) -> Nothing;
                   (Just e0, Just e1) ->
                     Just (Deriv (formula l) (DIffIntro e0 e1));
                 });
               IffElimL i ->
                 (case unfoldD (minus_nat k one_nat) p i of {
                   Nothing -> Nothing;
                   Just e0 -> Just (Deriv (formula l) (DIffElimL e0));
                 });
               IffElimR i ->
                 (case unfoldD (minus_nat k one_nat) p i of {
                   Nothing -> Nothing;
                   Just e0 -> Just (Deriv (formula l) (DIffElimR e0));
                 });
               ForallElim i ->
                 (case unfoldD (minus_nat k one_nat) p i of {
                   Nothing -> Nothing;
                   Just e0 -> Just (Deriv (formula l) (DForallElim e0));
                 });
               ForallIntro i ->
                 (case unfoldD (minus_nat k one_nat) p i of {
                   Nothing -> Nothing;
                   Just e0 -> Just (Deriv (formula l) (DForallIntro e0));
                 });
               ExistsIntro i ->
                 (case unfoldD (minus_nat k one_nat) p i of {
                   Nothing -> Nothing;
                   Just e0 -> Just (Deriv (formula l) (DExistsIntro e0));
                 });
               ExistsElim m a c ->
                 (case (unfoldD (minus_nat k one_nat) p m,
                         (fmAt p a, unfoldD (minus_nat k one_nat) p c))
                   of {
                   (Nothing, _) -> Nothing;
                   (Just _, (Nothing, _)) -> Nothing;
                   (Just _, (Just _, Nothing)) -> Nothing;
                   (Just e0, (Just g1, Just e2)) ->
                     Just (Deriv (formula l) (DExistsElim e0 a g1 e2));
                 });
               EqIntro -> Just (Deriv (formula l) DEqIntro);
               EqElim i j ->
                 (case (unfoldD (minus_nat k one_nat) p i,
                         unfoldD (minus_nat k one_nat) p j)
                   of {
                   (Nothing, _) -> Nothing;
                   (Just _, Nothing) -> Nothing;
                   (Just e0, Just e1) ->
                     Just (Deriv (formula l) (DEqElim e0 e1));
                 });
               Reit i -> (case unfoldD (minus_nat k one_nat) p i of {
                           Nothing -> Nothing;
                           Just e0 -> Just (Deriv (formula l) (DReit e0));
                         });
             });
         }));

ruleFms :: Drule -> [Fm];
ruleFms (DAssume k1) = [];
ruleFms (DPremise k1) = [];
ruleFms (DMP d1 d2) = [];
ruleFms (DCP k1 g1 d1) = [g1];
ruleFms (DRAA k1 g1 d1) = [g1];
ruleFms (DDN d1) = [];
ruleFms (DBotI d1 d2) = [];
ruleFms (DAndIntro d1 d2) = [];
ruleFms (DAndElimL d1) = [];
ruleFms (DAndElimR d1) = [];
ruleFms (DOrIntroL d1) = [];
ruleFms (DOrIntroR d1) = [];
ruleFms (DOrElim d1 k1 g1 d2 k2 g2 d3) = [g1, g2];
ruleFms (DIffIntro d1 d2) = [];
ruleFms (DIffElimL d1) = [];
ruleFms (DIffElimR d1) = [];
ruleFms (DForallElim d1) = [];
ruleFms (DForallIntro d1) = [];
ruleFms (DExistsIntro d1) = [];
ruleFms (DExistsElim d1 k1 g1 d2) = [g1];
ruleFms DEqIntro = [];
ruleFms (DEqElim d1 d2) = [];
ruleFms (DReit d1) = [];

namesD :: Deriv -> [String];
namesD (Deriv phi r) =
  names phi ++ concatMap names (ruleFms r) ++ concatMap namesD (subDerivs r);

premLines :: [(Nat, (Nat, Fm))] -> [Fitch_item];
premLines g = map (\ e -> FLine (fst (snd e)) (snd (snd e)) FPremise) g;

derivationToFitch :: Deriv -> [Fitch_item];
derivationToFitch d =
  let {
    g = premEnv d;
    base = suc (maxlen (namesD d));
  } in (case emit base g (suc (size_lista g)) zero_nat d of {
         (items, (_, (_, _))) -> premLines g ++ items;
       });

lineOK_gen :: ([Pline] -> Nat -> Set Nat -> [Fm]) -> [Pline] -> Pline -> Bool;
lineOK_gen a e l =
  let {
    g = depsOf (depsAt e) (justification l) (lineNumber l);
  } in equal_set (references l) g &&
         all (\ m -> not (is_none (lookupLine e m)))
           (citedLines (justification l)) &&
           ruleOK e (formula l) (a e (lineNumber l) g) (justification l);

checkFrom_gen ::
  ([Pline] -> Nat -> Set Nat -> [Fm]) -> [Pline] -> [Pline] -> Bool;
checkFrom_gen a e [] = True;
checkFrom_gen a e (l : ls) = lineOK_gen a e l && checkFrom_gen a (e ++ [l]) ls;

lemmonCorrect :: [Pline] -> Bool;
lemmonCorrect p =
  sorted_wrt less_nat (map lineNumber p) && checkFrom_gen depSrc [] p;

rootLine :: [Pline] -> Nat;
rootLine p = (if null p then zero_nat else lineNumber (last p));

toDerivation :: [Pline] -> Sum Translation_error Deriv;
toDerivation p =
  (if null p || not (lemmonCorrect p) then Inl (NotCorrect zero_nat)
    else (case unfoldD (suc (rootLine p)) p (rootLine p) of {
           Nothing -> Inl (NotCorrect (rootLine p));
           Just a -> Inr a;
         }));

viaTree :: [Pline] -> Sum Translation_error (Route, [Fitch_item]);
viaTree p = (case toDerivation p of {
              Inl a -> Inl a;
              Inr d -> Inr (ViaTree, derivationToFitch d);
            });

recomputeAux :: [Pline] -> [(Nat, (Fm, Justa))] -> [Pline];
recomputeAux acc [] = acc;
recomputeAux acc ((n, (f, j)) : ls) =
  recomputeAux (acc ++ [ProofLine n f j (depsOf (depsAt acc) j n)]) ls;

recompute :: [(Nat, (Fm, Justa))] -> [Pline];
recompute = recomputeAux [];

stripDeps :: [Pline] -> [(Nat, (Fm, Justa))];
stripDeps p = map (\ l -> (lineNumber l, (formula l, justification l))) p;

subLevel :: [Pline] -> (Nat, Nat) -> [Nat];
subLevel p ac = removeAll (fst ac) (boxPath p (fst ac));

hlIsPropositional :: Hl_formula -> Bool;
hlIsPropositional (HL_Predicate p ts) = null ts;
hlIsPropositional (HL_Boolean b) = True;
hlIsPropositional (HL_Not p) = hlIsPropositional p;
hlIsPropositional (HL_And p q) = hlIsPropositional p && hlIsPropositional q;
hlIsPropositional (HL_Or p q) = hlIsPropositional p && hlIsPropositional q;
hlIsPropositional (HL_Implies p q) = hlIsPropositional p && hlIsPropositional q;
hlIsPropositional (HL_Iff p q) = hlIsPropositional p && hlIsPropositional q;
hlIsPropositional (HL_ForAll x p) = False;
hlIsPropositional (HL_Exists x p) = False;

hlLiteralFormula :: (String, Bool) -> Hl_formula;
hlLiteralFormula (p, True) = HL_Predicate p [];
hlLiteralFormula (p, False) = HL_Not (HL_Predicate p []);

hlDisjoin :: [Hl_formula] -> Hl_formula;
hlDisjoin ps = (case ps of {
                 [] -> HL_Boolean False;
                 a : b -> foldl HL_Or a b;
               });

hlConjoin :: [Hl_formula] -> Hl_formula;
hlConjoin ps = (case ps of {
                 [] -> HL_Boolean True;
                 a : b -> foldl HL_And a b;
               });

hlClausesFormula :: [[(String, Bool)]] -> Hl_formula;
hlClausesFormula clauses =
  hlDisjoin (map (hlConjoin . map hlLiteralFormula) clauses);

hlDNFClauses :: Hl_formula -> Maybe [[(String, Bool)]];
hlDNFClauses (HL_Boolean True) = Just [[]];
hlDNFClauses (HL_Boolean False) = Just [];
hlDNFClauses (HL_Or p q) = (case (hlDNFClauses p, hlDNFClauses q) of {
                             (Nothing, _) -> Nothing;
                             (Just _, Nothing) -> Nothing;
                             (Just ps, Just qs) -> Just (ps ++ qs);
                           });
hlDNFClauses (HL_And p q) =
  (case (hlDNFClauses p, hlDNFClauses q) of {
    (Nothing, _) -> Nothing;
    (Just _, Nothing) -> Nothing;
    (Just ps, Just qs) -> Just (concatMap (\ r -> map (\ a -> r ++ a) qs) ps);
  });
hlDNFClauses (HL_Predicate p []) = Just [[(p, True)]];
hlDNFClauses (HL_Not (HL_Predicate p [])) = Just [[(p, False)]];
hlDNFClauses (HL_Predicate v (vb : vc)) = Nothing;
hlDNFClauses (HL_Not (HL_Predicate va (vc : vd))) = Nothing;
hlDNFClauses (HL_Not (HL_Boolean va)) = Nothing;
hlDNFClauses (HL_Not (HL_Not va)) = Nothing;
hlDNFClauses (HL_Not (HL_And va vb)) = Nothing;
hlDNFClauses (HL_Not (HL_Or va vb)) = Nothing;
hlDNFClauses (HL_Not (HL_Implies va vb)) = Nothing;
hlDNFClauses (HL_Not (HL_Iff va vb)) = Nothing;
hlDNFClauses (HL_Not (HL_ForAll va vb)) = Nothing;
hlDNFClauses (HL_Not (HL_Exists va vb)) = Nothing;
hlDNFClauses (HL_Implies v va) = Nothing;
hlDNFClauses (HL_Iff v va) = Nothing;
hlDNFClauses (HL_ForAll v va) = Nothing;
hlDNFClauses (HL_Exists v va) = Nothing;

hlEliminateImplications :: Hl_formula -> Hl_formula;
hlEliminateImplications (HL_Predicate p ts) = HL_Predicate p ts;
hlEliminateImplications (HL_Boolean b) = HL_Boolean b;
hlEliminateImplications (HL_Not p) = HL_Not (hlEliminateImplications p);
hlEliminateImplications (HL_And p q) =
  HL_And (hlEliminateImplications p) (hlEliminateImplications q);
hlEliminateImplications (HL_Or p q) =
  HL_Or (hlEliminateImplications p) (hlEliminateImplications q);
hlEliminateImplications (HL_Implies p q) =
  HL_Or (HL_Not (hlEliminateImplications p)) (hlEliminateImplications q);
hlEliminateImplications (HL_Iff p q) =
  let {
    pa = hlEliminateImplications p;
    qa = hlEliminateImplications q;
  } in HL_And (HL_Or (HL_Not pa) qa) (HL_Or (HL_Not qa) pa);
hlEliminateImplications (HL_ForAll x p) =
  HL_ForAll x (hlEliminateImplications p);
hlEliminateImplications (HL_Exists x p) =
  HL_Exists x (hlEliminateImplications p);

hlPushNegations :: Hl_formula -> Hl_formula;
hlPushNegations (HL_Not (HL_Not p)) = hlPushNegations p;
hlPushNegations (HL_Not (HL_And p q)) =
  HL_Or (hlPushNegations (HL_Not p)) (hlPushNegations (HL_Not q));
hlPushNegations (HL_Not (HL_Or p q)) =
  HL_And (hlPushNegations (HL_Not p)) (hlPushNegations (HL_Not q));
hlPushNegations (HL_Not (HL_Boolean b)) = HL_Boolean (not b);
hlPushNegations (HL_Not (HL_ForAll x p)) =
  HL_Exists x (hlPushNegations (HL_Not p));
hlPushNegations (HL_Not (HL_Exists x p)) =
  HL_ForAll x (hlPushNegations (HL_Not p));
hlPushNegations (HL_Not (HL_Predicate v va)) = HL_Not (HL_Predicate v va);
hlPushNegations (HL_Not (HL_Implies v va)) = HL_Not (HL_Implies v va);
hlPushNegations (HL_Not (HL_Iff v va)) = HL_Not (HL_Iff v va);
hlPushNegations (HL_And p q) = HL_And (hlPushNegations p) (hlPushNegations q);
hlPushNegations (HL_Or p q) = HL_Or (hlPushNegations p) (hlPushNegations q);
hlPushNegations (HL_ForAll x p) = HL_ForAll x (hlPushNegations p);
hlPushNegations (HL_Exists x p) = HL_Exists x (hlPushNegations p);
hlPushNegations (HL_Predicate v va) = HL_Predicate v va;
hlPushNegations (HL_Boolean v) = HL_Boolean v;
hlPushNegations (HL_Implies v va) = HL_Implies v va;
hlPushNegations (HL_Iff v va) = HL_Iff v va;

hlToNNF :: Hl_formula -> Hl_formula;
hlToNNF p = hlPushNegations (hlEliminateImplications p);

hlToDNF :: Hl_formula -> Maybe Hl_formula;
hlToDNF p =
  (if hlIsPropositional p
    then map_option hlClausesFormula (hlDNFClauses (hlToNNF p)) else Nothing);

showNats :: [Nat] -> String;
showNats ns = sepBy "," (map showNat ns);

showDeps :: Set Nat -> String;
showDeps g = showNats (sorted_list_of_set g);

showJust :: Justa -> String;
showJust Assumption = "A";
showJust (MP i j) = showNats [i, j] ++ " MP";
showJust (CP a c) = showNats [a, c] ++ " CP";
showJust (RAA a c) = showNats [a, c] ++ " RAA";
showJust (DN i) = showNat i ++ " DN";
showJust (BotI i j) = ((showNats [i, j] ++ " ") ++ symBot) ++ "I";
showJust (AndIntro i j) = ((showNats [i, j] ++ " ") ++ symAnd) ++ "I";
showJust (AndElimL i) = ((showNat i ++ " ") ++ symAnd) ++ "E";
showJust (AndElimR i) = ((showNat i ++ " ") ++ symAnd) ++ "E";
showJust (OrIntroL i) = ((showNat i ++ " ") ++ symOr) ++ "I";
showJust (OrIntroR i) = ((showNat i ++ " ") ++ symOr) ++ "I";
showJust (OrElim d a1 c1 a2 c2) =
  ((showNats [d, a1, c1, a2, c2] ++ " ") ++ symOr) ++ "E";
showJust (IffIntro i j) = ((showNats [i, j] ++ " ") ++ symIff) ++ "I";
showJust (IffElimL i) = ((showNat i ++ " ") ++ symIff) ++ "E";
showJust (IffElimR i) = ((showNat i ++ " ") ++ symIff) ++ "E";
showJust (ForallElim i) = ((showNat i ++ " ") ++ symAll) ++ "E";
showJust (ForallIntro i) = ((showNat i ++ " ") ++ symAll) ++ "I";
showJust (ExistsIntro i) = ((showNat i ++ " ") ++ symEx) ++ "I";
showJust (ExistsElim m a c) = ((showNats [m, a, c] ++ " ") ++ symEx) ++ "E";
showJust EqIntro = "=I";
showJust (EqElim i j) = showNats [i, j] ++ " =E";
showJust (Reit i) = showNat i ++ " R";

firstDiff :: [Nat] -> [Nat] -> Nat;
firstDiff [] ys = zero_nat;
firstDiff (x : xs) [] = x;
firstDiff (x : xs) (y : ys) = (if equal_nat x y then firstDiff xs ys else x);

sentence :: Fm -> Bool;
sentence p = null (fvs p);

hlConclusion :: [Hl_line] -> Maybe Hl_formula;
hlConclusion p = (if null p then Nothing else Just (hlFormula (last p)));

lemmon_21 :: [Pline] -> Bool;
lemmon_21 p = all (\ l -> not (is_reit (justification l))) p;

showError :: Translation_error -> String;
showError (NotNested n a bs) =
  ((((("line " ++ showNat n) ++ " discharges ") ++ showNat a) ++
     " while the box(es) opened at ") ++
    showNats bs) ++
    " are still open";
showError (OutOfScope n m b) =
  ((((("line " ++ showNat n) ++ " cites ") ++ showNat m) ++
     ", which the box opened at ") ++
    showNat b) ++
    " has closed over";
showError (PremiseInBox n b) =
  (("premise " ++ showNat n) ++ " is written inside the box opened at ") ++
    showNat b;
showError (PremiseLate n m) =
  ((("premise " ++ showNat n) ++ " is written after line ") ++ showNat m) ++
    ", which is not a premise";
showError (BoxReversed a c) =
  ((("the assumption at line " ++ showNat a) ++ " is discharged from line ") ++
    showNat c) ++
    ", which precedes it";
showError (AssumptionReused a ca c) =
  ((((("the assumption at line " ++ showNat a) ++
       " is discharged both at line ") ++
      showNat ca) ++
     " and at line ") ++
    showNat c) ++
    ", so two subproofs would have to open together";
showError (NotCorrect n) =
  ("the source is not a correct Lemmon proof (line " ++ showNat n) ++ ")";

showFRule :: Fitch_rule -> String;
showFRule FPremise = "Premise";
showFRule FAssume = "Assume";
showFRule (FMP i j) = "MP " ++ showNats [i, j];
showFRule (FCP (a, c)) = (("CP " ++ showNat a) ++ "-") ++ showNat c;
showFRule (FRAA (a, c)) = (("RAA " ++ showNat a) ++ "-") ++ showNat c;
showFRule (FDN i) = "DN " ++ showNat i;
showFRule (FBotI i j) = (symBot ++ "I ") ++ showNats [i, j];
showFRule (FAndIntro i j) = (symAnd ++ "I ") ++ showNats [i, j];
showFRule (FAndElimL i) = (symAnd ++ "E ") ++ showNat i;
showFRule (FAndElimR i) = (symAnd ++ "E ") ++ showNat i;
showFRule (FOrIntroL i) = (symOr ++ "I ") ++ showNat i;
showFRule (FOrIntroR i) = (symOr ++ "I ") ++ showNat i;
showFRule (FOrElim d (a1, c1) (a2, c2)) =
  (((((((((symOr ++ "E ") ++ showNat d) ++ ", ") ++ showNat a1) ++ "-") ++
       showNat c1) ++
      ", ") ++
     showNat a2) ++
    "-") ++
    showNat c2;
showFRule (FIffIntro i j) = (symIff ++ "I ") ++ showNats [i, j];
showFRule (FIffElimL i) = (symIff ++ "E ") ++ showNat i;
showFRule (FIffElimR i) = (symIff ++ "E ") ++ showNat i;
showFRule (FForallElim i) = (symAll ++ "E ") ++ showNat i;
showFRule (FForallIntro i) = (symAll ++ "I ") ++ showNat i;
showFRule (FExistsIntro i) = (symEx ++ "I ") ++ showNat i;
showFRule (FExistsElim m (a, c)) =
  (((((symEx ++ "E ") ++ showNat m) ++ ", ") ++ showNat a) ++ "-") ++ showNat c;
showFRule FEqIntro = "=I";
showFRule (FEqElim i j) = "=E " ++ showNats [i, j];
showFRule (FReit i) = "R " ++ showNat i;

showFitchLine :: Fline -> String;
showFitchLine fl =
  (padTo (nat_of_integer (5 :: Integer)) (showNat (flNum fl)) ++
    padTo (nat_of_integer (36 :: Integer))
      (cat (replicate (size_lista (flScope fl)) "| ") ++ showFm (flFm fl))) ++
    showFRule (flRule fl);

showFitch :: [Fitch_item] -> [String];
showFitch f = map showFitchLine (flatten f);

showRoute :: Route -> String;
showRoute Direct = "-- positional";
showRoute ViaTree = "-- via a derivation tree";

size_list :: forall a. (a -> Nat) -> [a] -> Nat;
size_list x [] = zero_nat;
size_list x (x21 : x22) =
  plus_nat (plus_nat (x x21) (size_list x x22)) (suc zero_nat);

toFitchRule :: Justa -> Fitch_rule;
toFitchRule Assumption = FPremise;
toFitchRule (MP i j) = FMP i j;
toFitchRule (CP a c) = FCP (a, c);
toFitchRule (RAA a c) = FRAA (a, c);
toFitchRule (DN i) = FDN i;
toFitchRule (BotI i j) = FBotI i j;
toFitchRule (AndIntro i j) = FAndIntro i j;
toFitchRule (AndElimL i) = FAndElimL i;
toFitchRule (AndElimR i) = FAndElimR i;
toFitchRule (OrIntroL i) = FOrIntroL i;
toFitchRule (OrIntroR i) = FOrIntroR i;
toFitchRule (OrElim d a1 c1 a2 c2) = FOrElim d (a1, c1) (a2, c2);
toFitchRule (IffIntro i j) = FIffIntro i j;
toFitchRule (IffElimL i) = FIffElimL i;
toFitchRule (IffElimR i) = FIffElimR i;
toFitchRule (ForallElim i) = FForallElim i;
toFitchRule (ForallIntro i) = FForallIntro i;
toFitchRule (ExistsIntro i) = FExistsIntro i;
toFitchRule (ExistsElim m a c) = FExistsElim m (a, c);
toFitchRule EqIntro = FEqIntro;
toFitchRule (EqElim i j) = FEqElim i j;
toFitchRule (Reit i) = FReit i;

buildItems :: [(Nat, Nat)] -> [Pline] -> [Fitch_item];
buildItems boxes [] = [];
buildItems boxes (l : ls) =
  (case find (\ ac -> equal_nat (fst ac) (lineNumber l)) boxes of {
    Nothing ->
      FLine (lineNumber l) (formula l) (toFitchRule (justification l)) :
        buildItems boxes ls;
    Just ac ->
      FSub (Subproof (lineNumber l) (formula l)
             (buildItems boxes
               (takeWhile (\ la -> less_eq_nat (lineNumber la) (snd ac)) ls))) :
        buildItems boxes
          (dropWhile (\ la -> less_eq_nat (lineNumber la) (snd ac)) ls);
  });

badCitations :: [Pline] -> [(Nat, Nat)];
badCitations p =
  concatMap
    (\ l ->
      map_filter
        (\ x ->
          (if not (is_prefix (boxPath p x) (boxPath p (lineNumber l)))
            then Just (lineNumber l, x) else Nothing))
        (fCitedLines (toFitchRule (justification l))))
    p;

scopeError :: [Pline] -> Maybe Translation_error;
scopeError p =
  (case badCitations p of {
    [] -> Nothing;
    (n, m) : _ -> Just (OutOfScope n m (firstDiff (boxPath p m) (boxPath p n)));
  });

fresh_for :: [String] -> String;
fresh_for used =
  implode
    (replicate (suc (maxlen used))
      (Char True True False False False True True False));

hlIsMT :: Hl_formula -> Hl_formula -> Hl_formula -> Bool;
hlIsMT a b goal =
  (case (a, (b, goal)) of {
    (HL_Predicate _ _, _) -> False;
    (HL_Boolean _, _) -> False;
    (HL_Not _, _) -> False;
    (HL_And _ _, _) -> False;
    (HL_Or _ _, _) -> False;
    (HL_Implies _ _, (HL_Predicate _ _, _)) -> False;
    (HL_Implies _ _, (HL_Boolean _, _)) -> False;
    (HL_Implies _ _, (HL_Not _, HL_Predicate _ _)) -> False;
    (HL_Implies _ _, (HL_Not _, HL_Boolean _)) -> False;
    (HL_Implies phi psi, (HL_Not psia, HL_Not phia)) ->
      equal_hl_formula psi psia && equal_hl_formula phi phia;
    (HL_Implies _ _, (HL_Not _, HL_And _ _)) -> False;
    (HL_Implies _ _, (HL_Not _, HL_Or _ _)) -> False;
    (HL_Implies _ _, (HL_Not _, HL_Implies _ _)) -> False;
    (HL_Implies _ _, (HL_Not _, HL_Iff _ _)) -> False;
    (HL_Implies _ _, (HL_Not _, HL_ForAll _ _)) -> False;
    (HL_Implies _ _, (HL_Not _, HL_Exists _ _)) -> False;
    (HL_Implies _ _, (HL_And _ _, _)) -> False;
    (HL_Implies _ _, (HL_Or _ _, _)) -> False;
    (HL_Implies _ _, (HL_Implies _ _, _)) -> False;
    (HL_Implies _ _, (HL_Iff _ _, _)) -> False;
    (HL_Implies _ _, (HL_ForAll _ _, _)) -> False;
    (HL_Implies _ _, (HL_Exists _ _, _)) -> False;
    (HL_Iff _ _, _) -> False;
    (HL_ForAll _ _, _) -> False;
    (HL_Exists _ _, _) -> False;
  });

conclusion :: [Pline] -> Maybe Fm;
conclusion p = (if null p then Nothing else Just (formula (last p)));

showLemmonLine :: Pline -> String;
showLemmonLine l =
  ((padTo (nat_of_integer (10 :: Integer)) (showDeps (references l)) ++
     padTo (nat_of_integer (6 :: Integer))
       (("(" ++ showNat (lineNumber l)) ++ ")")) ++
    padTo (nat_of_integer (32 :: Integer)) (showFm (formula l))) ++
    showJust (justification l);

showLemmon :: [Pline] -> [String];
showLemmon p = map showLemmonLine p;

fitchCorrect :: [Fitch_item] -> Bool;
fitchCorrect f = fitchWF f && checkFrom_gen (scopeSrc f) [] (delta f);

dischargeOK :: Nat -> Fm -> Deriv -> Bool;
dischargeOK a fa d =
  all (\ nf -> (if equal_nat (fst nf) a then equal_fm (snd nf) fa else True))
    (openAsms d);

derivOK :: Deriv -> Bool;
derivOK (Deriv phi (DAssume n)) = True;
derivOK (Deriv phi (DPremise n)) = True;
derivOK (Deriv phi (DMP d1 d2)) =
  derivOK d1 && derivOK d2 && equal_fm (dForm d1) (Impl (dForm d2) phi);
derivOK (Deriv phi (DCP a fa d)) =
  derivOK d && equal_fm phi (Impl fa (dForm d)) && dischargeOK a fa d;
derivOK (Deriv phi (DRAA a fa d)) =
  derivOK d &&
    equal_fm phi (Neg fa) && equal_fm (dForm d) Bot && dischargeOK a fa d;
derivOK (Deriv phi (DDN d)) = derivOK d && equal_fm (dForm d) (Neg (Neg phi));
derivOK (Deriv phi (DBotI d1 d2)) =
  derivOK d1 &&
    derivOK d2 && equal_fm phi Bot && equal_fm (dForm d2) (Neg (dForm d1));
derivOK (Deriv phi (DAndIntro d1 d2)) =
  derivOK d1 && derivOK d2 && equal_fm phi (Conj (dForm d1) (dForm d2));
derivOK (Deriv phi (DAndElimL d)) = derivOK d && (case dForm d of {
           Atom _ _ -> False;
           Eqf _ _ -> False;
           Bot -> False;
           Neg _ -> False;
           Conj p _ -> equal_fm phi p;
           Disj _ _ -> False;
           Impl _ _ -> False;
           Iff _ _ -> False;
           Uni _ _ -> False;
           Exi _ _ -> False;
         });
derivOK (Deriv phi (DAndElimR d)) = derivOK d && (case dForm d of {
           Atom _ _ -> False;
           Eqf _ _ -> False;
           Bot -> False;
           Neg _ -> False;
           Conj _ a -> equal_fm phi a;
           Disj _ _ -> False;
           Impl _ _ -> False;
           Iff _ _ -> False;
           Uni _ _ -> False;
           Exi _ _ -> False;
         });
derivOK (Deriv phi (DOrIntroL d)) =
  derivOK d && (case phi of {
                 Atom _ _ -> False;
                 Eqf _ _ -> False;
                 Bot -> False;
                 Neg _ -> False;
                 Conj _ _ -> False;
                 Disj p _ -> equal_fm (dForm d) p;
                 Impl _ _ -> False;
                 Iff _ _ -> False;
                 Uni _ _ -> False;
                 Exi _ _ -> False;
               });
derivOK (Deriv phi (DOrIntroR d)) =
  derivOK d && (case phi of {
                 Atom _ _ -> False;
                 Eqf _ _ -> False;
                 Bot -> False;
                 Neg _ -> False;
                 Conj _ _ -> False;
                 Disj _ a -> equal_fm (dForm d) a;
                 Impl _ _ -> False;
                 Iff _ _ -> False;
                 Uni _ _ -> False;
                 Exi _ _ -> False;
               });
derivOK (Deriv phi (DOrElim d0 a1 f1 d1 a2 f2 d2)) =
  derivOK d0 &&
    derivOK d1 &&
      derivOK d2 &&
        equal_fm (dForm d0) (Disj f1 f2) &&
          equal_fm (dForm d1) phi &&
            equal_fm (dForm d2) phi &&
              dischargeOK a1 f1 d1 && dischargeOK a2 f2 d2;
derivOK (Deriv phi (DIffIntro d1 d2)) =
  derivOK d1 &&
    derivOK d2 &&
      (case phi of {
        Atom _ _ -> False;
        Eqf _ _ -> False;
        Bot -> False;
        Neg _ -> False;
        Conj _ _ -> False;
        Disj _ _ -> False;
        Impl _ _ -> False;
        Iff p q ->
          equal_fm (dForm d1) (Impl p q) && equal_fm (dForm d2) (Impl q p);
        Uni _ _ -> False;
        Exi _ _ -> False;
      });
derivOK (Deriv phi (DIffElimL d)) =
  derivOK d && (case phi of {
                 Atom _ _ -> False;
                 Eqf _ _ -> False;
                 Bot -> False;
                 Neg _ -> False;
                 Conj _ _ -> False;
                 Disj _ _ -> False;
                 Impl p q -> equal_fm (dForm d) (Iff p q);
                 Iff _ _ -> False;
                 Uni _ _ -> False;
                 Exi _ _ -> False;
               });
derivOK (Deriv phi (DIffElimR d)) =
  derivOK d && (case phi of {
                 Atom _ _ -> False;
                 Eqf _ _ -> False;
                 Bot -> False;
                 Neg _ -> False;
                 Conj _ _ -> False;
                 Disj _ _ -> False;
                 Impl q p -> equal_fm (dForm d) (Iff p q);
                 Iff _ _ -> False;
                 Uni _ _ -> False;
                 Exi _ _ -> False;
               });
derivOK (Deriv phi (DForallElim d)) = derivOK d && (case dForm d of {
             Atom _ _ -> False;
             Eqf _ _ -> False;
             Bot -> False;
             Neg _ -> False;
             Conj _ _ -> False;
             Disj _ _ -> False;
             Impl _ _ -> False;
             Iff _ _ -> False;
             Uni x p -> instOK x p phi;
             Exi _ _ -> False;
           });
derivOK (Deriv phi (DForallIntro d)) =
  derivOK d && (case phi of {
                 Atom _ _ -> False;
                 Eqf _ _ -> False;
                 Bot -> False;
                 Neg _ -> False;
                 Conj _ _ -> False;
                 Disj _ _ -> False;
                 Impl _ _ -> False;
                 Iff _ _ -> False;
                 Uni x p -> genOK x p (dForm d) (map snd (openAsms d));
                 Exi _ _ -> False;
               });
derivOK (Deriv phi (DExistsIntro d)) =
  derivOK d && (case phi of {
                 Atom _ _ -> False;
                 Eqf _ _ -> False;
                 Bot -> False;
                 Neg _ -> False;
                 Conj _ _ -> False;
                 Disj _ _ -> False;
                 Impl _ _ -> False;
                 Iff _ _ -> False;
                 Uni _ _ -> False;
                 Exi x p -> instOK x p (dForm d);
               });
derivOK (Deriv phi (DExistsElim d0 a f d1)) =
  derivOK d0 &&
    derivOK d1 &&
      equal_fm (dForm d1) phi &&
        dischargeOK a f d1 &&
          (case dForm d0 of {
            Atom _ _ -> False;
            Eqf _ _ -> False;
            Bot -> False;
            Neg _ -> False;
            Conj _ _ -> False;
            Disj _ _ -> False;
            Impl _ _ -> False;
            Iff _ _ -> False;
            Uni _ _ -> False;
            Exi x p ->
              witOK x p f phi
                (map snd (openAsms d0) ++
                  map_filter
                    (\ xa ->
                      (if not (equal_nat (fst xa) a) then Just (snd xa)
                        else Nothing))
                    (openAsms d1));
          });
derivOK (Deriv phi DEqIntro) = (case phi of {
                                 Atom _ _ -> False;
                                 Eqf (Nm a) (Nm b) -> a == b;
                                 Eqf (Nm _) (Vr _) -> False;
                                 Eqf (Vr _) _ -> False;
                                 Bot -> False;
                                 Neg _ -> False;
                                 Conj _ _ -> False;
                                 Disj _ _ -> False;
                                 Impl _ _ -> False;
                                 Iff _ _ -> False;
                                 Uni _ _ -> False;
                                 Exi _ _ -> False;
                               });
derivOK (Deriv phi (DEqElim d1 d2)) =
  derivOK d1 && derivOK d2 && (case dForm d1 of {
                                Atom _ _ -> False;
                                Eqf (Nm a) (Nm b) -> eqsub a b (dForm d2) phi;
                                Eqf (Nm _) (Vr _) -> False;
                                Eqf (Vr _) _ -> False;
                                Bot -> False;
                                Neg _ -> False;
                                Conj _ _ -> False;
                                Disj _ _ -> False;
                                Impl _ _ -> False;
                                Iff _ _ -> False;
                                Uni _ _ -> False;
                                Exi _ _ -> False;
                              });
derivOK (Deriv phi (DReit d)) = derivOK d && equal_fm phi (dForm d);

overlapping :: (Nat, Nat) -> (Nat, Nat) -> Bool;
overlapping ac b =
  less_nat (fst ac) (fst b) &&
    less_eq_nat (fst b) (snd ac) && less_nat (snd ac) (snd b);

hlOpenPremises :: [Hl_line] -> [Hl_formula];
hlOpenPremises p =
  (if null p then []
    else map_filter
           (\ x ->
             (if member (hlLineNumber x) (hlReferences (last p)) &&
                   equal_hl_justification (hlJustification x) HL_Assumption
               then Just (hlFormula x) else Nothing))
           p);

fitchToLemmon :: [Fitch_item] -> [Pline];
fitchToLemmon f = delta f;

boxHeadError :: [Pline] -> Maybe Translation_error;
boxHeadError p =
  (case filter
          (\ x ->
            equal_nat (fst (fst x)) (fst (snd x)) &&
              not (equal_nat (snd (fst x)) (snd (snd x))))
          (product (boxesOf p) (boxesOf p))
    of {
    [] -> Nothing;
    x : _ -> Just (AssumptionReused (fst (fst x)) (snd (fst x)) (snd (snd x)));
  });

dischargerOf :: [Pline] -> (Nat, Nat) -> Nat;
dischargerOf p ac =
  (case find (\ l -> membera (dischargePairs (justification l)) ac) p of {
    Nothing -> zero_nat;
    Just a -> lineNumber a;
  });

nestingError :: [Pline] -> Maybe Translation_error;
nestingError p =
  (case filter (\ ac -> any (overlapping ac) (boxesOf p)) (boxesOf p) of {
    [] -> Nothing;
    ac : _ ->
      Just (NotNested (dischargerOf p ac) (fst ac)
             (map_filter
               (\ x -> (if overlapping ac x then Just (fst x) else Nothing))
               (boxesOf p)));
  });

premiseError :: [Pline] -> Maybe Translation_error;
premiseError p =
  (case filter
          (\ l ->
            equal_just (justification l) Assumption &&
              not (membera (dischargedAssumps p) (lineNumber l)) &&
                not (null (boxPath p (lineNumber l))))
          p
    of {
    [] -> Nothing;
    l : _ ->
      Just (PremiseInBox (lineNumber l) (last (boxPath p (lineNumber l))));
  });

fitchPremises :: [Fitch_item] -> [Fm];
fitchPremises f =
  map_filter
    (\ x ->
      (if equal_fitch_rule (flRule x) FPremise then Just (flFm x) else Nothing))
    (flatten f);

hlSubBody :: Hl_subproof -> [Hl_fitch_item];
hlSubBody (HL_Subproof a p body) = body;

hlRuleOKG ::
  ([Hl_line] -> Int -> Set Int -> Set Int) -> [Hl_line] -> Hl_line -> Bool;
hlRuleOKG src p l =
  let {
    phi = hlFormula l;
    g = hlReferences l;
  } in (case hlJustification l of {
         HL_Assumption -> equal_set g (insert (hlLineNumber l) bot_set);
         HL_MP m n ->
           (case (hlLookupLine p m, hlLookupLine p n) of {
             (Nothing, _) -> False;
             (Just _, Nothing) -> False;
             (Just lm, Just ln) ->
               (case hlFormula lm of {
                 HL_Predicate _ _ -> False;
                 HL_Boolean _ -> False;
                 HL_Not _ -> False;
                 HL_And _ _ -> False;
                 HL_Or _ _ -> False;
                 HL_Implies pa q ->
                   equal_hl_formula (hlFormula ln) pa &&
                     equal_hl_formula phi q &&
                       equal_set g
                         (sup_set (hlReferences lm) (hlReferences ln));
                 HL_Iff _ _ -> False;
                 HL_ForAll _ _ -> False;
                 HL_Exists _ _ -> False;
               });
           });
         HL_MT m n ->
           (case (hlLookupLine p m, (hlLookupLine p n, phi)) of {
             (Nothing, _) -> False;
             (Just _, (Nothing, _)) -> False;
             (Just _, (Just _, HL_Predicate _ _)) -> False;
             (Just _, (Just _, HL_Boolean _)) -> False;
             (Just lm, (Just ln, HL_Not pa)) ->
               (case (hlFormula lm, hlFormula ln) of {
                 (HL_Predicate _ _, _) -> False;
                 (HL_Boolean _, _) -> False;
                 (HL_Not _, _) -> False;
                 (HL_And _ _, _) -> False;
                 (HL_Or _ _, _) -> False;
                 (HL_Implies _ _, HL_Predicate _ _) -> False;
                 (HL_Implies _ _, HL_Boolean _) -> False;
                 (HL_Implies q r, HL_Not s) ->
                   equal_hl_formula pa q &&
                     equal_hl_formula r s &&
                       equal_set g
                         (sup_set (hlReferences lm) (hlReferences ln));
                 (HL_Implies _ _, HL_And _ _) -> False;
                 (HL_Implies _ _, HL_Or _ _) -> False;
                 (HL_Implies _ _, HL_Implies _ _) -> False;
                 (HL_Implies _ _, HL_Iff _ _) -> False;
                 (HL_Implies _ _, HL_ForAll _ _) -> False;
                 (HL_Implies _ _, HL_Exists _ _) -> False;
                 (HL_Iff _ _, _) -> False;
                 (HL_ForAll _ _, _) -> False;
                 (HL_Exists _ _, _) -> False;
               });
             (Just _, (Just _, HL_And _ _)) -> False;
             (Just _, (Just _, HL_Or _ _)) -> False;
             (Just _, (Just _, HL_Implies _ _)) -> False;
             (Just _, (Just _, HL_Iff _ _)) -> False;
             (Just _, (Just _, HL_ForAll _ _)) -> False;
             (Just _, (Just _, HL_Exists _ _)) -> False;
           });
         HL_DN m ->
           (case hlLookupLine p m of {
             Nothing -> False;
             Just lm ->
               (equal_hl_formula (hlFormula lm) (HL_Not (HL_Not phi)) ||
                 equal_hl_formula phi (HL_Not (HL_Not (hlFormula lm)))) &&
                 equal_set g (hlReferences lm);
           });
         HL_CP a c ->
           (case (hlLookupLine p a, hlLookupLine p c) of {
             (Nothing, _) -> False;
             (Just _, Nothing) -> False;
             (Just la, Just lc) ->
               equal_hl_justification (hlJustification la) HL_Assumption &&
                 equal_hl_formula phi
                   (HL_Implies (hlFormula la) (hlFormula lc)) &&
                   equal_set g (remove (hlLineNumber la) (hlReferences lc));
           });
         HL_AndIntro m n ->
           (case (hlLookupLine p m, hlLookupLine p n) of {
             (Nothing, _) -> False;
             (Just _, Nothing) -> False;
             (Just lm, Just ln) ->
               (equal_hl_formula phi (HL_And (hlFormula lm) (hlFormula ln)) ||
                 equal_hl_formula phi (HL_And (hlFormula ln) (hlFormula lm))) &&
                 equal_set g (sup_set (hlReferences lm) (hlReferences ln));
           });
         HL_AndElim m ->
           (case hlLookupLine p m of {
             Nothing -> False;
             Just lm ->
               (case hlFormula lm of {
                 HL_Predicate _ _ -> False;
                 HL_Boolean _ -> False;
                 HL_Not _ -> False;
                 HL_And pa q ->
                   (equal_hl_formula phi pa || equal_hl_formula phi q) &&
                     equal_set g (hlReferences lm);
                 HL_Or _ _ -> False;
                 HL_Implies _ _ -> False;
                 HL_Iff _ _ -> False;
                 HL_ForAll _ _ -> False;
                 HL_Exists _ _ -> False;
               });
           });
         HL_OrIntro m ->
           (case (hlLookupLine p m, phi) of {
             (Nothing, _) -> False;
             (Just _, HL_Predicate _ _) -> False;
             (Just _, HL_Boolean _) -> False;
             (Just _, HL_Not _) -> False;
             (Just _, HL_And _ _) -> False;
             (Just lm, HL_Or pa q) ->
               (equal_hl_formula (hlFormula lm) pa ||
                 equal_hl_formula (hlFormula lm) q) &&
                 equal_set g (hlReferences lm);
             (Just _, HL_Implies _ _) -> False;
             (Just _, HL_Iff _ _) -> False;
             (Just _, HL_ForAll _ _) -> False;
             (Just _, HL_Exists _ _) -> False;
           });
         HL_OrElim d a1 c1 a2 c2 ->
           (case (hlLookupLine p d,
                   (hlLookupLine p a1,
                     (hlLookupLine p c1,
                       (hlLookupLine p a2, hlLookupLine p c2))))
             of {
             (Nothing, _) -> False;
             (Just _, (Nothing, _)) -> False;
             (Just _, (Just _, (Nothing, _))) -> False;
             (Just _, (Just _, (Just _, (Nothing, _)))) -> False;
             (Just _, (Just _, (Just _, (Just _, Nothing)))) -> False;
             (Just ld, (Just la1, (Just lc1, (Just la2, Just lc2)))) ->
               equal_hl_justification (hlJustification la1) HL_Assumption &&
                 equal_hl_justification (hlJustification la2) HL_Assumption &&
                   equal_hl_formula (hlFormula lc1) phi &&
                     equal_hl_formula (hlFormula lc2) phi &&
                       (case hlFormula ld of {
                         HL_Predicate _ _ -> False;
                         HL_Boolean _ -> False;
                         HL_Not _ -> False;
                         HL_And _ _ -> False;
                         HL_Or pa q ->
                           equal_hl_formula (hlFormula la1) pa &&
                             equal_hl_formula (hlFormula la2) q ||
                             equal_hl_formula (hlFormula la1) q &&
                               equal_hl_formula (hlFormula la2) pa;
                         HL_Implies _ _ -> False;
                         HL_Iff _ _ -> False;
                         HL_ForAll _ _ -> False;
                         HL_Exists _ _ -> False;
                       }) &&
                         equal_set g
                           (sup_set
                             (sup_set (hlReferences ld)
                               (remove (hlLineNumber la1) (hlReferences lc1)))
                             (remove (hlLineNumber la2) (hlReferences lc2)));
           });
         HL_RAA a c ->
           (case (hlLookupLine p a, hlLookupLine p c) of {
             (Nothing, _) -> False;
             (Just _, Nothing) -> False;
             (Just la, Just lc) ->
               equal_hl_justification (hlJustification la) HL_Assumption &&
                 equal_hl_formula phi (HL_Not (hlFormula la)) &&
                   hlContradiction (hlFormula lc) &&
                     equal_set g (remove (hlLineNumber la) (hlReferences lc));
           });
         HL_ForallElim m ->
           (case hlLookupLine p m of {
             Nothing -> False;
             Just lm ->
               (case hlCollectForalls (hlFormula lm) of {
                 (sourceVars, sourceCore) ->
                   (case hlCollectForalls phi of {
                     (targetVars, targetCore) ->
                       (case hlEliminationCount sourceVars targetVars of {
                         Nothing -> False;
                         Just k ->
                           not (is_none
                                 (hlInferWitnessConstsK sourceVars sourceCore k
                                   targetCore)) &&
                             equal_set g (hlReferences lm);
                       });
                   });
               });
           });
         HL_ExistsIntro m ->
           (case hlLookupLine p m of {
             Nothing -> False;
             Just lm ->
               (case hlCollectExists phi of {
                 (xs, core) ->
                   not (null xs) &&
                     any (\ k ->
                           not (is_none
                                 (hlInferWitnessConstsK xs
                                   (hlPrefixExists (drop k xs) core) k
                                   (hlFormula lm))))
                       (upt zero_nat (suc (size_lista xs))) &&
                       equal_set g (hlReferences lm);
               });
           });
         HL_ForallIntro m ->
           (case hlLookupLine p m of {
             Nothing -> False;
             Just lm ->
               (case hlCollectForalls phi of {
                 (xs, core) ->
                   not (null xs) &&
                     (case hlInferWitnessConstsK xs core (size_lista xs)
                             (hlFormula lm)
                       of {
                       Nothing -> False;
                       Just cs ->
                         let {
                           pairs =
                             filter (\ xc -> not (snd xc == "")) (zip xs cs);
                         } in hlAbstractMany pairs (hlFormula lm) ==
                                Just core &&
                                ball (image snd (Set pairs))
                                  (\ c ->
                                    not (member c
  (hlAssumptionConstants p (src p (hlLineNumber l) g)))) &&
                                  equal_set g (hlReferences lm);
                     });
               });
           });
         HL_ExistsElim m a c ->
           (case (hlLookupLine p m, (hlLookupLine p a, hlLookupLine p c)) of {
             (Nothing, _) -> False;
             (Just _, (Nothing, _)) -> False;
             (Just _, (Just _, Nothing)) -> False;
             (Just lm, (Just la, Just lc)) ->
               (case hlCollectExists (hlFormula lm) of {
                 (sourceVars, sourceCore) ->
                   (case hlCollectExists (hlFormula la) of {
                     (targetVars, _) ->
                       let {
                         delta = remove (hlLineNumber la) (hlReferences lc);
                         deltaSrc =
                           remove (hlLineNumber la)
                             (src p (hlLineNumber lc) (hlReferences lc));
                       } in not (null sourceVars) &&
                              equal_hl_justification (hlJustification la)
                                HL_Assumption &&
                                (case hlEliminationCount sourceVars targetVars
                                  of {
                                  Nothing -> False;
                                  Just k ->
                                    let {
                                      template =
hlPrefixExists targetVars sourceCore;
                                    } in (case
   hlInferWitnessConstsK sourceVars template k (hlFormula la) of {
   Nothing -> False;
   Just cs ->
     let {
       pairs = filter (\ xc -> not (snd xc == "")) (zip (take k sourceVars) cs);
     } in hlAbstractMany pairs (hlFormula la) == Just template &&
            ball (image snd (Set pairs))
              (\ w ->
                not (member w (hlConstantsInFormula (hlFormula lc))) &&
                  not (member w (hlReferencedConstants p deltaSrc))) &&
              equal_hl_formula phi (hlFormula lc) &&
                equal_set g (sup_set (hlReferences lm) delta);
 });
                                });
                   });
               });
           });
         HL_EqIntro ->
           (case phi of {
             HL_Predicate _ [] -> False;
             HL_Predicate _ (HL_Var _ : _) -> False;
             HL_Predicate _ [HL_Const _] -> False;
             HL_Predicate _ (HL_Const _ : HL_Var _ : _) -> False;
             HL_Predicate e [HL_Const a, HL_Const b] ->
               e == "=" && a == b && equal_set g bot_set;
             HL_Predicate _ (HL_Const _ : HL_Const _ : _ : _) -> False;
             HL_Boolean _ -> False;
             HL_Not _ -> False;
             HL_And _ _ -> False;
             HL_Or _ _ -> False;
             HL_Implies _ _ -> False;
             HL_Iff _ _ -> False;
             HL_ForAll _ _ -> False;
             HL_Exists _ _ -> False;
           });
         HL_EqElim m n ->
           (case (hlLookupLine p m, hlLookupLine p n) of {
             (Nothing, _) -> False;
             (Just _, Nothing) -> False;
             (Just lm, Just ln) ->
               (case hlEqualityFormula (hlFormula ln) of {
                 Nothing -> False;
                 Just (HL_Var _, _) -> False;
                 Just (HL_Const _, HL_Var _) -> False;
                 Just (HL_Const a, HL_Const b) ->
                   hlEqualUpToConstantReplacement a b (hlFormula lm) phi &&
                     equal_set g (sup_set (hlReferences lm) (hlReferences ln));
               });
           });
         HL_LEM -> hlExcludedMiddle phi;
         HL_PropTaut ms ->
           all (\ m -> not (is_none (hlLookupLine p m))) ms &&
             hlPropositionalConsequence (hlMapFilter (hlFormulaAt p) ms) phi &&
               equal_set g (hlReferenceUnion p ms);
         HL_IffIntro m n ->
           (case (hlLookupLine p m, (hlLookupLine p n, phi)) of {
             (Nothing, _) -> False;
             (Just _, (Nothing, _)) -> False;
             (Just _, (Just _, HL_Predicate _ _)) -> False;
             (Just _, (Just _, HL_Boolean _)) -> False;
             (Just _, (Just _, HL_Not _)) -> False;
             (Just _, (Just _, HL_And _ _)) -> False;
             (Just _, (Just _, HL_Or _ _)) -> False;
             (Just _, (Just _, HL_Implies _ _)) -> False;
             (Just lm, (Just ln, HL_Iff u v)) ->
               (case (hlFormula lm, hlFormula ln) of {
                 (HL_Predicate _ _, _) -> False;
                 (HL_Boolean _, _) -> False;
                 (HL_Not _, _) -> False;
                 (HL_And _ _, _) -> False;
                 (HL_Or _ _, _) -> False;
                 (HL_Implies _ _, HL_Predicate _ _) -> False;
                 (HL_Implies _ _, HL_Boolean _) -> False;
                 (HL_Implies _ _, HL_Not _) -> False;
                 (HL_Implies _ _, HL_And _ _) -> False;
                 (HL_Implies _ _, HL_Or _ _) -> False;
                 (HL_Implies pa q, HL_Implies r s) ->
                   equal_hl_formula pa s &&
                     equal_hl_formula q r &&
                       (equal_hl_formula u pa && equal_hl_formula v q ||
                         equal_hl_formula u q && equal_hl_formula v pa) &&
                         equal_set g
                           (sup_set (hlReferences lm) (hlReferences ln));
                 (HL_Implies _ _, HL_Iff _ _) -> False;
                 (HL_Implies _ _, HL_ForAll _ _) -> False;
                 (HL_Implies _ _, HL_Exists _ _) -> False;
                 (HL_Iff _ _, _) -> False;
                 (HL_ForAll _ _, _) -> False;
                 (HL_Exists _ _, _) -> False;
               });
             (Just _, (Just _, HL_ForAll _ _)) -> False;
             (Just _, (Just _, HL_Exists _ _)) -> False;
           });
         HL_IffElim m n ->
           (case (hlLookupLine p m, hlLookupLine p n) of {
             (Nothing, _) -> False;
             (Just _, Nothing) -> False;
             (Just lm, Just ln) ->
               (case hlFormula lm of {
                 HL_Predicate _ _ -> False;
                 HL_Boolean _ -> False;
                 HL_Not _ -> False;
                 HL_And _ _ -> False;
                 HL_Or _ _ -> False;
                 HL_Implies _ _ -> False;
                 HL_Iff pa q ->
                   (equal_hl_formula (hlFormula ln) pa &&
                      equal_hl_formula phi q ||
                     equal_hl_formula (hlFormula ln) q &&
                       equal_hl_formula phi pa) &&
                     equal_set g (sup_set (hlReferences lm) (hlReferences ln));
                 HL_ForAll _ _ -> False;
                 HL_Exists _ _ -> False;
               });
           });
         HL_QN m ->
           (case hlLookupLine p m of {
             Nothing -> False;
             Just lm ->
               hlQuantifierNegationEquivalent (hlFormula lm) phi &&
                 equal_set g (hlReferences lm);
           });
       });

hlLineOKG ::
  ([Hl_line] -> Int -> Set Int -> Set Int) -> [Hl_line] -> Hl_line -> Bool;
hlLineOKG src p l = hlStructureOK p l && hlRuleOKG src p l;

openPremises :: [Pline] -> [Fm];
openPremises p = (if null p then [] else depFms p (references (last p)));

renumberJust :: (Nat -> Nat) -> Justa -> Justa;
renumberJust r Assumption = Assumption;
renumberJust r (MP i0 i1) = MP (r i0) (r i1);
renumberJust r (CP i0 i1) = CP (r i0) (r i1);
renumberJust r (RAA i0 i1) = RAA (r i0) (r i1);
renumberJust r (DN i0) = DN (r i0);
renumberJust r (BotI i0 i1) = BotI (r i0) (r i1);
renumberJust r (AndIntro i0 i1) = AndIntro (r i0) (r i1);
renumberJust r (AndElimL i0) = AndElimL (r i0);
renumberJust r (AndElimR i0) = AndElimR (r i0);
renumberJust r (OrIntroL i0) = OrIntroL (r i0);
renumberJust r (OrIntroR i0) = OrIntroR (r i0);
renumberJust r (OrElim i0 i1 i2 i3 i4) =
  OrElim (r i0) (r i1) (r i2) (r i3) (r i4);
renumberJust r (IffIntro i0 i1) = IffIntro (r i0) (r i1);
renumberJust r (IffElimL i0) = IffElimL (r i0);
renumberJust r (IffElimR i0) = IffElimR (r i0);
renumberJust r (ForallElim i0) = ForallElim (r i0);
renumberJust r (ForallIntro i0) = ForallIntro (r i0);
renumberJust r (ExistsIntro i0) = ExistsIntro (r i0);
renumberJust r (ExistsElim i0 i1 i2) = ExistsElim (r i0) (r i1) (r i2);
renumberJust r EqIntro = EqIntro;
renumberJust r (EqElim i0 i1) = EqElim (r i0) (r i1);
renumberJust r (Reit i0) = Reit (r i0);

relabel :: (Nat -> Nat) -> Pline -> Pline;
relabel r l =
  ProofLine (r (lineNumber l)) (formula l) (renumberJust r (justification l))
    (image r (references l));

boxOrderError :: [Pline] -> Maybe Translation_error;
boxOrderError p =
  (case filter (\ ac -> less_nat (snd ac) (fst ac)) (boxesOf p) of {
    [] -> Nothing;
    ac : _ -> Just (BoxReversed (fst ac) (snd ac));
  });

isPremiseLine :: [Pline] -> Pline -> Bool;
isPremiseLine p l =
  equal_just (justification l) Assumption &&
    not (membera (dischargedAssumps p) (lineNumber l));

badSubCitations :: [Pline] -> [(Nat, (Nat, Nat))];
badSubCitations p =
  concatMap
    (\ l ->
      map_filter
        (\ x ->
          (if not (boxPath p (lineNumber l) == subLevel p x)
            then Just (lineNumber l, (snd x, fst x)) else Nothing))
        (dischargePairs (justification l)))
    p;

subScopeError :: [Pline] -> Maybe Translation_error;
subScopeError p = (case badSubCitations p of {
                    [] -> Nothing;
                    (n, (c, a)) : _ -> Just (OutOfScope n c a);
                  });

zero_int :: Int;
zero_int = Int_of_integer (0 :: Integer);

hlCanonicalOrder :: [Hl_line] -> Bool;
hlCanonicalOrder p =
  all (less_int zero_int) (map hlLineNumber p) &&
    sorted_wrt less_int (map hlLineNumber p);

hlDischargePairs :: Hl_justification -> [(Int, Int)];
hlDischargePairs (HL_CP a c) = [(a, c)];
hlDischargePairs (HL_RAA a c) = [(a, c)];
hlDischargePairs (HL_OrElim d a1 c1 a2 c2) = [(a1, c1), (a2, c2)];
hlDischargePairs (HL_ExistsElim m a c) = [(a, c)];
hlDischargePairs HL_Assumption = [];
hlDischargePairs (HL_MP v va) = [];
hlDischargePairs (HL_MT v va) = [];
hlDischargePairs (HL_DN v) = [];
hlDischargePairs (HL_AndIntro v va) = [];
hlDischargePairs (HL_AndElim v) = [];
hlDischargePairs (HL_OrIntro v) = [];
hlDischargePairs (HL_ForallElim v) = [];
hlDischargePairs (HL_ExistsIntro v) = [];
hlDischargePairs (HL_ForallIntro v) = [];
hlDischargePairs HL_EqIntro = [];
hlDischargePairs (HL_EqElim v va) = [];
hlDischargePairs HL_LEM = [];
hlDischargePairs (HL_PropTaut v) = [];
hlDischargePairs (HL_IffIntro v va) = [];
hlDischargePairs (HL_IffElim v va) = [];
hlDischargePairs (HL_QN v) = [];

hlCorrectG :: ([Hl_line] -> Int -> Set Int -> Set Int) -> [Hl_line] -> Bool;
hlCorrectG src p = all (hlLineOKG src p) p;

equal_hl_fitch_rule :: Hl_fitch_rule -> Hl_fitch_rule -> Bool;
equal_hl_fitch_rule (HL_FQN x22) (HL_FReit x23) = False;
equal_hl_fitch_rule (HL_FReit x23) (HL_FQN x22) = False;
equal_hl_fitch_rule (HL_FIffE x211 x212) (HL_FReit x23) = False;
equal_hl_fitch_rule (HL_FReit x23) (HL_FIffE x211 x212) = False;
equal_hl_fitch_rule (HL_FIffE x211 x212) (HL_FQN x22) = False;
equal_hl_fitch_rule (HL_FQN x22) (HL_FIffE x211 x212) = False;
equal_hl_fitch_rule (HL_FIffI x201 x202) (HL_FReit x23) = False;
equal_hl_fitch_rule (HL_FReit x23) (HL_FIffI x201 x202) = False;
equal_hl_fitch_rule (HL_FIffI x201 x202) (HL_FQN x22) = False;
equal_hl_fitch_rule (HL_FQN x22) (HL_FIffI x201 x202) = False;
equal_hl_fitch_rule (HL_FIffI x201 x202) (HL_FIffE x211 x212) = False;
equal_hl_fitch_rule (HL_FIffE x211 x212) (HL_FIffI x201 x202) = False;
equal_hl_fitch_rule (HL_FPropTaut x19) (HL_FReit x23) = False;
equal_hl_fitch_rule (HL_FReit x23) (HL_FPropTaut x19) = False;
equal_hl_fitch_rule (HL_FPropTaut x19) (HL_FQN x22) = False;
equal_hl_fitch_rule (HL_FQN x22) (HL_FPropTaut x19) = False;
equal_hl_fitch_rule (HL_FPropTaut x19) (HL_FIffE x211 x212) = False;
equal_hl_fitch_rule (HL_FIffE x211 x212) (HL_FPropTaut x19) = False;
equal_hl_fitch_rule (HL_FPropTaut x19) (HL_FIffI x201 x202) = False;
equal_hl_fitch_rule (HL_FIffI x201 x202) (HL_FPropTaut x19) = False;
equal_hl_fitch_rule HL_FLEM (HL_FReit x23) = False;
equal_hl_fitch_rule (HL_FReit x23) HL_FLEM = False;
equal_hl_fitch_rule HL_FLEM (HL_FQN x22) = False;
equal_hl_fitch_rule (HL_FQN x22) HL_FLEM = False;
equal_hl_fitch_rule HL_FLEM (HL_FIffE x211 x212) = False;
equal_hl_fitch_rule (HL_FIffE x211 x212) HL_FLEM = False;
equal_hl_fitch_rule HL_FLEM (HL_FIffI x201 x202) = False;
equal_hl_fitch_rule (HL_FIffI x201 x202) HL_FLEM = False;
equal_hl_fitch_rule HL_FLEM (HL_FPropTaut x19) = False;
equal_hl_fitch_rule (HL_FPropTaut x19) HL_FLEM = False;
equal_hl_fitch_rule (HL_FEqE x171 x172) (HL_FReit x23) = False;
equal_hl_fitch_rule (HL_FReit x23) (HL_FEqE x171 x172) = False;
equal_hl_fitch_rule (HL_FEqE x171 x172) (HL_FQN x22) = False;
equal_hl_fitch_rule (HL_FQN x22) (HL_FEqE x171 x172) = False;
equal_hl_fitch_rule (HL_FEqE x171 x172) (HL_FIffE x211 x212) = False;
equal_hl_fitch_rule (HL_FIffE x211 x212) (HL_FEqE x171 x172) = False;
equal_hl_fitch_rule (HL_FEqE x171 x172) (HL_FIffI x201 x202) = False;
equal_hl_fitch_rule (HL_FIffI x201 x202) (HL_FEqE x171 x172) = False;
equal_hl_fitch_rule (HL_FEqE x171 x172) (HL_FPropTaut x19) = False;
equal_hl_fitch_rule (HL_FPropTaut x19) (HL_FEqE x171 x172) = False;
equal_hl_fitch_rule (HL_FEqE x171 x172) HL_FLEM = False;
equal_hl_fitch_rule HL_FLEM (HL_FEqE x171 x172) = False;
equal_hl_fitch_rule HL_FEqI (HL_FReit x23) = False;
equal_hl_fitch_rule (HL_FReit x23) HL_FEqI = False;
equal_hl_fitch_rule HL_FEqI (HL_FQN x22) = False;
equal_hl_fitch_rule (HL_FQN x22) HL_FEqI = False;
equal_hl_fitch_rule HL_FEqI (HL_FIffE x211 x212) = False;
equal_hl_fitch_rule (HL_FIffE x211 x212) HL_FEqI = False;
equal_hl_fitch_rule HL_FEqI (HL_FIffI x201 x202) = False;
equal_hl_fitch_rule (HL_FIffI x201 x202) HL_FEqI = False;
equal_hl_fitch_rule HL_FEqI (HL_FPropTaut x19) = False;
equal_hl_fitch_rule (HL_FPropTaut x19) HL_FEqI = False;
equal_hl_fitch_rule HL_FEqI HL_FLEM = False;
equal_hl_fitch_rule HL_FLEM HL_FEqI = False;
equal_hl_fitch_rule HL_FEqI (HL_FEqE x171 x172) = False;
equal_hl_fitch_rule (HL_FEqE x171 x172) HL_FEqI = False;
equal_hl_fitch_rule (HL_FExistsE x151 x152) (HL_FReit x23) = False;
equal_hl_fitch_rule (HL_FReit x23) (HL_FExistsE x151 x152) = False;
equal_hl_fitch_rule (HL_FExistsE x151 x152) (HL_FQN x22) = False;
equal_hl_fitch_rule (HL_FQN x22) (HL_FExistsE x151 x152) = False;
equal_hl_fitch_rule (HL_FExistsE x151 x152) (HL_FIffE x211 x212) = False;
equal_hl_fitch_rule (HL_FIffE x211 x212) (HL_FExistsE x151 x152) = False;
equal_hl_fitch_rule (HL_FExistsE x151 x152) (HL_FIffI x201 x202) = False;
equal_hl_fitch_rule (HL_FIffI x201 x202) (HL_FExistsE x151 x152) = False;
equal_hl_fitch_rule (HL_FExistsE x151 x152) (HL_FPropTaut x19) = False;
equal_hl_fitch_rule (HL_FPropTaut x19) (HL_FExistsE x151 x152) = False;
equal_hl_fitch_rule (HL_FExistsE x151 x152) HL_FLEM = False;
equal_hl_fitch_rule HL_FLEM (HL_FExistsE x151 x152) = False;
equal_hl_fitch_rule (HL_FExistsE x151 x152) (HL_FEqE x171 x172) = False;
equal_hl_fitch_rule (HL_FEqE x171 x172) (HL_FExistsE x151 x152) = False;
equal_hl_fitch_rule (HL_FExistsE x151 x152) HL_FEqI = False;
equal_hl_fitch_rule HL_FEqI (HL_FExistsE x151 x152) = False;
equal_hl_fitch_rule (HL_FExistsI x14) (HL_FReit x23) = False;
equal_hl_fitch_rule (HL_FReit x23) (HL_FExistsI x14) = False;
equal_hl_fitch_rule (HL_FExistsI x14) (HL_FQN x22) = False;
equal_hl_fitch_rule (HL_FQN x22) (HL_FExistsI x14) = False;
equal_hl_fitch_rule (HL_FExistsI x14) (HL_FIffE x211 x212) = False;
equal_hl_fitch_rule (HL_FIffE x211 x212) (HL_FExistsI x14) = False;
equal_hl_fitch_rule (HL_FExistsI x14) (HL_FIffI x201 x202) = False;
equal_hl_fitch_rule (HL_FIffI x201 x202) (HL_FExistsI x14) = False;
equal_hl_fitch_rule (HL_FExistsI x14) (HL_FPropTaut x19) = False;
equal_hl_fitch_rule (HL_FPropTaut x19) (HL_FExistsI x14) = False;
equal_hl_fitch_rule (HL_FExistsI x14) HL_FLEM = False;
equal_hl_fitch_rule HL_FLEM (HL_FExistsI x14) = False;
equal_hl_fitch_rule (HL_FExistsI x14) (HL_FEqE x171 x172) = False;
equal_hl_fitch_rule (HL_FEqE x171 x172) (HL_FExistsI x14) = False;
equal_hl_fitch_rule (HL_FExistsI x14) HL_FEqI = False;
equal_hl_fitch_rule HL_FEqI (HL_FExistsI x14) = False;
equal_hl_fitch_rule (HL_FExistsI x14) (HL_FExistsE x151 x152) = False;
equal_hl_fitch_rule (HL_FExistsE x151 x152) (HL_FExistsI x14) = False;
equal_hl_fitch_rule (HL_FForallI x13) (HL_FReit x23) = False;
equal_hl_fitch_rule (HL_FReit x23) (HL_FForallI x13) = False;
equal_hl_fitch_rule (HL_FForallI x13) (HL_FQN x22) = False;
equal_hl_fitch_rule (HL_FQN x22) (HL_FForallI x13) = False;
equal_hl_fitch_rule (HL_FForallI x13) (HL_FIffE x211 x212) = False;
equal_hl_fitch_rule (HL_FIffE x211 x212) (HL_FForallI x13) = False;
equal_hl_fitch_rule (HL_FForallI x13) (HL_FIffI x201 x202) = False;
equal_hl_fitch_rule (HL_FIffI x201 x202) (HL_FForallI x13) = False;
equal_hl_fitch_rule (HL_FForallI x13) (HL_FPropTaut x19) = False;
equal_hl_fitch_rule (HL_FPropTaut x19) (HL_FForallI x13) = False;
equal_hl_fitch_rule (HL_FForallI x13) HL_FLEM = False;
equal_hl_fitch_rule HL_FLEM (HL_FForallI x13) = False;
equal_hl_fitch_rule (HL_FForallI x13) (HL_FEqE x171 x172) = False;
equal_hl_fitch_rule (HL_FEqE x171 x172) (HL_FForallI x13) = False;
equal_hl_fitch_rule (HL_FForallI x13) HL_FEqI = False;
equal_hl_fitch_rule HL_FEqI (HL_FForallI x13) = False;
equal_hl_fitch_rule (HL_FForallI x13) (HL_FExistsE x151 x152) = False;
equal_hl_fitch_rule (HL_FExistsE x151 x152) (HL_FForallI x13) = False;
equal_hl_fitch_rule (HL_FForallI x13) (HL_FExistsI x14) = False;
equal_hl_fitch_rule (HL_FExistsI x14) (HL_FForallI x13) = False;
equal_hl_fitch_rule (HL_FForallE x12) (HL_FReit x23) = False;
equal_hl_fitch_rule (HL_FReit x23) (HL_FForallE x12) = False;
equal_hl_fitch_rule (HL_FForallE x12) (HL_FQN x22) = False;
equal_hl_fitch_rule (HL_FQN x22) (HL_FForallE x12) = False;
equal_hl_fitch_rule (HL_FForallE x12) (HL_FIffE x211 x212) = False;
equal_hl_fitch_rule (HL_FIffE x211 x212) (HL_FForallE x12) = False;
equal_hl_fitch_rule (HL_FForallE x12) (HL_FIffI x201 x202) = False;
equal_hl_fitch_rule (HL_FIffI x201 x202) (HL_FForallE x12) = False;
equal_hl_fitch_rule (HL_FForallE x12) (HL_FPropTaut x19) = False;
equal_hl_fitch_rule (HL_FPropTaut x19) (HL_FForallE x12) = False;
equal_hl_fitch_rule (HL_FForallE x12) HL_FLEM = False;
equal_hl_fitch_rule HL_FLEM (HL_FForallE x12) = False;
equal_hl_fitch_rule (HL_FForallE x12) (HL_FEqE x171 x172) = False;
equal_hl_fitch_rule (HL_FEqE x171 x172) (HL_FForallE x12) = False;
equal_hl_fitch_rule (HL_FForallE x12) HL_FEqI = False;
equal_hl_fitch_rule HL_FEqI (HL_FForallE x12) = False;
equal_hl_fitch_rule (HL_FForallE x12) (HL_FExistsE x151 x152) = False;
equal_hl_fitch_rule (HL_FExistsE x151 x152) (HL_FForallE x12) = False;
equal_hl_fitch_rule (HL_FForallE x12) (HL_FExistsI x14) = False;
equal_hl_fitch_rule (HL_FExistsI x14) (HL_FForallE x12) = False;
equal_hl_fitch_rule (HL_FForallE x12) (HL_FForallI x13) = False;
equal_hl_fitch_rule (HL_FForallI x13) (HL_FForallE x12) = False;
equal_hl_fitch_rule (HL_FRAA x11) (HL_FReit x23) = False;
equal_hl_fitch_rule (HL_FReit x23) (HL_FRAA x11) = False;
equal_hl_fitch_rule (HL_FRAA x11) (HL_FQN x22) = False;
equal_hl_fitch_rule (HL_FQN x22) (HL_FRAA x11) = False;
equal_hl_fitch_rule (HL_FRAA x11) (HL_FIffE x211 x212) = False;
equal_hl_fitch_rule (HL_FIffE x211 x212) (HL_FRAA x11) = False;
equal_hl_fitch_rule (HL_FRAA x11) (HL_FIffI x201 x202) = False;
equal_hl_fitch_rule (HL_FIffI x201 x202) (HL_FRAA x11) = False;
equal_hl_fitch_rule (HL_FRAA x11) (HL_FPropTaut x19) = False;
equal_hl_fitch_rule (HL_FPropTaut x19) (HL_FRAA x11) = False;
equal_hl_fitch_rule (HL_FRAA x11) HL_FLEM = False;
equal_hl_fitch_rule HL_FLEM (HL_FRAA x11) = False;
equal_hl_fitch_rule (HL_FRAA x11) (HL_FEqE x171 x172) = False;
equal_hl_fitch_rule (HL_FEqE x171 x172) (HL_FRAA x11) = False;
equal_hl_fitch_rule (HL_FRAA x11) HL_FEqI = False;
equal_hl_fitch_rule HL_FEqI (HL_FRAA x11) = False;
equal_hl_fitch_rule (HL_FRAA x11) (HL_FExistsE x151 x152) = False;
equal_hl_fitch_rule (HL_FExistsE x151 x152) (HL_FRAA x11) = False;
equal_hl_fitch_rule (HL_FRAA x11) (HL_FExistsI x14) = False;
equal_hl_fitch_rule (HL_FExistsI x14) (HL_FRAA x11) = False;
equal_hl_fitch_rule (HL_FRAA x11) (HL_FForallI x13) = False;
equal_hl_fitch_rule (HL_FForallI x13) (HL_FRAA x11) = False;
equal_hl_fitch_rule (HL_FRAA x11) (HL_FForallE x12) = False;
equal_hl_fitch_rule (HL_FForallE x12) (HL_FRAA x11) = False;
equal_hl_fitch_rule (HL_FOrE x101 x102 x103) (HL_FReit x23) = False;
equal_hl_fitch_rule (HL_FReit x23) (HL_FOrE x101 x102 x103) = False;
equal_hl_fitch_rule (HL_FOrE x101 x102 x103) (HL_FQN x22) = False;
equal_hl_fitch_rule (HL_FQN x22) (HL_FOrE x101 x102 x103) = False;
equal_hl_fitch_rule (HL_FOrE x101 x102 x103) (HL_FIffE x211 x212) = False;
equal_hl_fitch_rule (HL_FIffE x211 x212) (HL_FOrE x101 x102 x103) = False;
equal_hl_fitch_rule (HL_FOrE x101 x102 x103) (HL_FIffI x201 x202) = False;
equal_hl_fitch_rule (HL_FIffI x201 x202) (HL_FOrE x101 x102 x103) = False;
equal_hl_fitch_rule (HL_FOrE x101 x102 x103) (HL_FPropTaut x19) = False;
equal_hl_fitch_rule (HL_FPropTaut x19) (HL_FOrE x101 x102 x103) = False;
equal_hl_fitch_rule (HL_FOrE x101 x102 x103) HL_FLEM = False;
equal_hl_fitch_rule HL_FLEM (HL_FOrE x101 x102 x103) = False;
equal_hl_fitch_rule (HL_FOrE x101 x102 x103) (HL_FEqE x171 x172) = False;
equal_hl_fitch_rule (HL_FEqE x171 x172) (HL_FOrE x101 x102 x103) = False;
equal_hl_fitch_rule (HL_FOrE x101 x102 x103) HL_FEqI = False;
equal_hl_fitch_rule HL_FEqI (HL_FOrE x101 x102 x103) = False;
equal_hl_fitch_rule (HL_FOrE x101 x102 x103) (HL_FExistsE x151 x152) = False;
equal_hl_fitch_rule (HL_FExistsE x151 x152) (HL_FOrE x101 x102 x103) = False;
equal_hl_fitch_rule (HL_FOrE x101 x102 x103) (HL_FExistsI x14) = False;
equal_hl_fitch_rule (HL_FExistsI x14) (HL_FOrE x101 x102 x103) = False;
equal_hl_fitch_rule (HL_FOrE x101 x102 x103) (HL_FForallI x13) = False;
equal_hl_fitch_rule (HL_FForallI x13) (HL_FOrE x101 x102 x103) = False;
equal_hl_fitch_rule (HL_FOrE x101 x102 x103) (HL_FForallE x12) = False;
equal_hl_fitch_rule (HL_FForallE x12) (HL_FOrE x101 x102 x103) = False;
equal_hl_fitch_rule (HL_FOrE x101 x102 x103) (HL_FRAA x11) = False;
equal_hl_fitch_rule (HL_FRAA x11) (HL_FOrE x101 x102 x103) = False;
equal_hl_fitch_rule (HL_FOrI x9) (HL_FReit x23) = False;
equal_hl_fitch_rule (HL_FReit x23) (HL_FOrI x9) = False;
equal_hl_fitch_rule (HL_FOrI x9) (HL_FQN x22) = False;
equal_hl_fitch_rule (HL_FQN x22) (HL_FOrI x9) = False;
equal_hl_fitch_rule (HL_FOrI x9) (HL_FIffE x211 x212) = False;
equal_hl_fitch_rule (HL_FIffE x211 x212) (HL_FOrI x9) = False;
equal_hl_fitch_rule (HL_FOrI x9) (HL_FIffI x201 x202) = False;
equal_hl_fitch_rule (HL_FIffI x201 x202) (HL_FOrI x9) = False;
equal_hl_fitch_rule (HL_FOrI x9) (HL_FPropTaut x19) = False;
equal_hl_fitch_rule (HL_FPropTaut x19) (HL_FOrI x9) = False;
equal_hl_fitch_rule (HL_FOrI x9) HL_FLEM = False;
equal_hl_fitch_rule HL_FLEM (HL_FOrI x9) = False;
equal_hl_fitch_rule (HL_FOrI x9) (HL_FEqE x171 x172) = False;
equal_hl_fitch_rule (HL_FEqE x171 x172) (HL_FOrI x9) = False;
equal_hl_fitch_rule (HL_FOrI x9) HL_FEqI = False;
equal_hl_fitch_rule HL_FEqI (HL_FOrI x9) = False;
equal_hl_fitch_rule (HL_FOrI x9) (HL_FExistsE x151 x152) = False;
equal_hl_fitch_rule (HL_FExistsE x151 x152) (HL_FOrI x9) = False;
equal_hl_fitch_rule (HL_FOrI x9) (HL_FExistsI x14) = False;
equal_hl_fitch_rule (HL_FExistsI x14) (HL_FOrI x9) = False;
equal_hl_fitch_rule (HL_FOrI x9) (HL_FForallI x13) = False;
equal_hl_fitch_rule (HL_FForallI x13) (HL_FOrI x9) = False;
equal_hl_fitch_rule (HL_FOrI x9) (HL_FForallE x12) = False;
equal_hl_fitch_rule (HL_FForallE x12) (HL_FOrI x9) = False;
equal_hl_fitch_rule (HL_FOrI x9) (HL_FRAA x11) = False;
equal_hl_fitch_rule (HL_FRAA x11) (HL_FOrI x9) = False;
equal_hl_fitch_rule (HL_FOrI x9) (HL_FOrE x101 x102 x103) = False;
equal_hl_fitch_rule (HL_FOrE x101 x102 x103) (HL_FOrI x9) = False;
equal_hl_fitch_rule (HL_FAndE x8) (HL_FReit x23) = False;
equal_hl_fitch_rule (HL_FReit x23) (HL_FAndE x8) = False;
equal_hl_fitch_rule (HL_FAndE x8) (HL_FQN x22) = False;
equal_hl_fitch_rule (HL_FQN x22) (HL_FAndE x8) = False;
equal_hl_fitch_rule (HL_FAndE x8) (HL_FIffE x211 x212) = False;
equal_hl_fitch_rule (HL_FIffE x211 x212) (HL_FAndE x8) = False;
equal_hl_fitch_rule (HL_FAndE x8) (HL_FIffI x201 x202) = False;
equal_hl_fitch_rule (HL_FIffI x201 x202) (HL_FAndE x8) = False;
equal_hl_fitch_rule (HL_FAndE x8) (HL_FPropTaut x19) = False;
equal_hl_fitch_rule (HL_FPropTaut x19) (HL_FAndE x8) = False;
equal_hl_fitch_rule (HL_FAndE x8) HL_FLEM = False;
equal_hl_fitch_rule HL_FLEM (HL_FAndE x8) = False;
equal_hl_fitch_rule (HL_FAndE x8) (HL_FEqE x171 x172) = False;
equal_hl_fitch_rule (HL_FEqE x171 x172) (HL_FAndE x8) = False;
equal_hl_fitch_rule (HL_FAndE x8) HL_FEqI = False;
equal_hl_fitch_rule HL_FEqI (HL_FAndE x8) = False;
equal_hl_fitch_rule (HL_FAndE x8) (HL_FExistsE x151 x152) = False;
equal_hl_fitch_rule (HL_FExistsE x151 x152) (HL_FAndE x8) = False;
equal_hl_fitch_rule (HL_FAndE x8) (HL_FExistsI x14) = False;
equal_hl_fitch_rule (HL_FExistsI x14) (HL_FAndE x8) = False;
equal_hl_fitch_rule (HL_FAndE x8) (HL_FForallI x13) = False;
equal_hl_fitch_rule (HL_FForallI x13) (HL_FAndE x8) = False;
equal_hl_fitch_rule (HL_FAndE x8) (HL_FForallE x12) = False;
equal_hl_fitch_rule (HL_FForallE x12) (HL_FAndE x8) = False;
equal_hl_fitch_rule (HL_FAndE x8) (HL_FRAA x11) = False;
equal_hl_fitch_rule (HL_FRAA x11) (HL_FAndE x8) = False;
equal_hl_fitch_rule (HL_FAndE x8) (HL_FOrE x101 x102 x103) = False;
equal_hl_fitch_rule (HL_FOrE x101 x102 x103) (HL_FAndE x8) = False;
equal_hl_fitch_rule (HL_FAndE x8) (HL_FOrI x9) = False;
equal_hl_fitch_rule (HL_FOrI x9) (HL_FAndE x8) = False;
equal_hl_fitch_rule (HL_FAndI x71 x72) (HL_FReit x23) = False;
equal_hl_fitch_rule (HL_FReit x23) (HL_FAndI x71 x72) = False;
equal_hl_fitch_rule (HL_FAndI x71 x72) (HL_FQN x22) = False;
equal_hl_fitch_rule (HL_FQN x22) (HL_FAndI x71 x72) = False;
equal_hl_fitch_rule (HL_FAndI x71 x72) (HL_FIffE x211 x212) = False;
equal_hl_fitch_rule (HL_FIffE x211 x212) (HL_FAndI x71 x72) = False;
equal_hl_fitch_rule (HL_FAndI x71 x72) (HL_FIffI x201 x202) = False;
equal_hl_fitch_rule (HL_FIffI x201 x202) (HL_FAndI x71 x72) = False;
equal_hl_fitch_rule (HL_FAndI x71 x72) (HL_FPropTaut x19) = False;
equal_hl_fitch_rule (HL_FPropTaut x19) (HL_FAndI x71 x72) = False;
equal_hl_fitch_rule (HL_FAndI x71 x72) HL_FLEM = False;
equal_hl_fitch_rule HL_FLEM (HL_FAndI x71 x72) = False;
equal_hl_fitch_rule (HL_FAndI x71 x72) (HL_FEqE x171 x172) = False;
equal_hl_fitch_rule (HL_FEqE x171 x172) (HL_FAndI x71 x72) = False;
equal_hl_fitch_rule (HL_FAndI x71 x72) HL_FEqI = False;
equal_hl_fitch_rule HL_FEqI (HL_FAndI x71 x72) = False;
equal_hl_fitch_rule (HL_FAndI x71 x72) (HL_FExistsE x151 x152) = False;
equal_hl_fitch_rule (HL_FExistsE x151 x152) (HL_FAndI x71 x72) = False;
equal_hl_fitch_rule (HL_FAndI x71 x72) (HL_FExistsI x14) = False;
equal_hl_fitch_rule (HL_FExistsI x14) (HL_FAndI x71 x72) = False;
equal_hl_fitch_rule (HL_FAndI x71 x72) (HL_FForallI x13) = False;
equal_hl_fitch_rule (HL_FForallI x13) (HL_FAndI x71 x72) = False;
equal_hl_fitch_rule (HL_FAndI x71 x72) (HL_FForallE x12) = False;
equal_hl_fitch_rule (HL_FForallE x12) (HL_FAndI x71 x72) = False;
equal_hl_fitch_rule (HL_FAndI x71 x72) (HL_FRAA x11) = False;
equal_hl_fitch_rule (HL_FRAA x11) (HL_FAndI x71 x72) = False;
equal_hl_fitch_rule (HL_FAndI x71 x72) (HL_FOrE x101 x102 x103) = False;
equal_hl_fitch_rule (HL_FOrE x101 x102 x103) (HL_FAndI x71 x72) = False;
equal_hl_fitch_rule (HL_FAndI x71 x72) (HL_FOrI x9) = False;
equal_hl_fitch_rule (HL_FOrI x9) (HL_FAndI x71 x72) = False;
equal_hl_fitch_rule (HL_FAndI x71 x72) (HL_FAndE x8) = False;
equal_hl_fitch_rule (HL_FAndE x8) (HL_FAndI x71 x72) = False;
equal_hl_fitch_rule (HL_FCP x6) (HL_FReit x23) = False;
equal_hl_fitch_rule (HL_FReit x23) (HL_FCP x6) = False;
equal_hl_fitch_rule (HL_FCP x6) (HL_FQN x22) = False;
equal_hl_fitch_rule (HL_FQN x22) (HL_FCP x6) = False;
equal_hl_fitch_rule (HL_FCP x6) (HL_FIffE x211 x212) = False;
equal_hl_fitch_rule (HL_FIffE x211 x212) (HL_FCP x6) = False;
equal_hl_fitch_rule (HL_FCP x6) (HL_FIffI x201 x202) = False;
equal_hl_fitch_rule (HL_FIffI x201 x202) (HL_FCP x6) = False;
equal_hl_fitch_rule (HL_FCP x6) (HL_FPropTaut x19) = False;
equal_hl_fitch_rule (HL_FPropTaut x19) (HL_FCP x6) = False;
equal_hl_fitch_rule (HL_FCP x6) HL_FLEM = False;
equal_hl_fitch_rule HL_FLEM (HL_FCP x6) = False;
equal_hl_fitch_rule (HL_FCP x6) (HL_FEqE x171 x172) = False;
equal_hl_fitch_rule (HL_FEqE x171 x172) (HL_FCP x6) = False;
equal_hl_fitch_rule (HL_FCP x6) HL_FEqI = False;
equal_hl_fitch_rule HL_FEqI (HL_FCP x6) = False;
equal_hl_fitch_rule (HL_FCP x6) (HL_FExistsE x151 x152) = False;
equal_hl_fitch_rule (HL_FExistsE x151 x152) (HL_FCP x6) = False;
equal_hl_fitch_rule (HL_FCP x6) (HL_FExistsI x14) = False;
equal_hl_fitch_rule (HL_FExistsI x14) (HL_FCP x6) = False;
equal_hl_fitch_rule (HL_FCP x6) (HL_FForallI x13) = False;
equal_hl_fitch_rule (HL_FForallI x13) (HL_FCP x6) = False;
equal_hl_fitch_rule (HL_FCP x6) (HL_FForallE x12) = False;
equal_hl_fitch_rule (HL_FForallE x12) (HL_FCP x6) = False;
equal_hl_fitch_rule (HL_FCP x6) (HL_FRAA x11) = False;
equal_hl_fitch_rule (HL_FRAA x11) (HL_FCP x6) = False;
equal_hl_fitch_rule (HL_FCP x6) (HL_FOrE x101 x102 x103) = False;
equal_hl_fitch_rule (HL_FOrE x101 x102 x103) (HL_FCP x6) = False;
equal_hl_fitch_rule (HL_FCP x6) (HL_FOrI x9) = False;
equal_hl_fitch_rule (HL_FOrI x9) (HL_FCP x6) = False;
equal_hl_fitch_rule (HL_FCP x6) (HL_FAndE x8) = False;
equal_hl_fitch_rule (HL_FAndE x8) (HL_FCP x6) = False;
equal_hl_fitch_rule (HL_FCP x6) (HL_FAndI x71 x72) = False;
equal_hl_fitch_rule (HL_FAndI x71 x72) (HL_FCP x6) = False;
equal_hl_fitch_rule (HL_FDN x5) (HL_FReit x23) = False;
equal_hl_fitch_rule (HL_FReit x23) (HL_FDN x5) = False;
equal_hl_fitch_rule (HL_FDN x5) (HL_FQN x22) = False;
equal_hl_fitch_rule (HL_FQN x22) (HL_FDN x5) = False;
equal_hl_fitch_rule (HL_FDN x5) (HL_FIffE x211 x212) = False;
equal_hl_fitch_rule (HL_FIffE x211 x212) (HL_FDN x5) = False;
equal_hl_fitch_rule (HL_FDN x5) (HL_FIffI x201 x202) = False;
equal_hl_fitch_rule (HL_FIffI x201 x202) (HL_FDN x5) = False;
equal_hl_fitch_rule (HL_FDN x5) (HL_FPropTaut x19) = False;
equal_hl_fitch_rule (HL_FPropTaut x19) (HL_FDN x5) = False;
equal_hl_fitch_rule (HL_FDN x5) HL_FLEM = False;
equal_hl_fitch_rule HL_FLEM (HL_FDN x5) = False;
equal_hl_fitch_rule (HL_FDN x5) (HL_FEqE x171 x172) = False;
equal_hl_fitch_rule (HL_FEqE x171 x172) (HL_FDN x5) = False;
equal_hl_fitch_rule (HL_FDN x5) HL_FEqI = False;
equal_hl_fitch_rule HL_FEqI (HL_FDN x5) = False;
equal_hl_fitch_rule (HL_FDN x5) (HL_FExistsE x151 x152) = False;
equal_hl_fitch_rule (HL_FExistsE x151 x152) (HL_FDN x5) = False;
equal_hl_fitch_rule (HL_FDN x5) (HL_FExistsI x14) = False;
equal_hl_fitch_rule (HL_FExistsI x14) (HL_FDN x5) = False;
equal_hl_fitch_rule (HL_FDN x5) (HL_FForallI x13) = False;
equal_hl_fitch_rule (HL_FForallI x13) (HL_FDN x5) = False;
equal_hl_fitch_rule (HL_FDN x5) (HL_FForallE x12) = False;
equal_hl_fitch_rule (HL_FForallE x12) (HL_FDN x5) = False;
equal_hl_fitch_rule (HL_FDN x5) (HL_FRAA x11) = False;
equal_hl_fitch_rule (HL_FRAA x11) (HL_FDN x5) = False;
equal_hl_fitch_rule (HL_FDN x5) (HL_FOrE x101 x102 x103) = False;
equal_hl_fitch_rule (HL_FOrE x101 x102 x103) (HL_FDN x5) = False;
equal_hl_fitch_rule (HL_FDN x5) (HL_FOrI x9) = False;
equal_hl_fitch_rule (HL_FOrI x9) (HL_FDN x5) = False;
equal_hl_fitch_rule (HL_FDN x5) (HL_FAndE x8) = False;
equal_hl_fitch_rule (HL_FAndE x8) (HL_FDN x5) = False;
equal_hl_fitch_rule (HL_FDN x5) (HL_FAndI x71 x72) = False;
equal_hl_fitch_rule (HL_FAndI x71 x72) (HL_FDN x5) = False;
equal_hl_fitch_rule (HL_FDN x5) (HL_FCP x6) = False;
equal_hl_fitch_rule (HL_FCP x6) (HL_FDN x5) = False;
equal_hl_fitch_rule (HL_FMT x41 x42) (HL_FReit x23) = False;
equal_hl_fitch_rule (HL_FReit x23) (HL_FMT x41 x42) = False;
equal_hl_fitch_rule (HL_FMT x41 x42) (HL_FQN x22) = False;
equal_hl_fitch_rule (HL_FQN x22) (HL_FMT x41 x42) = False;
equal_hl_fitch_rule (HL_FMT x41 x42) (HL_FIffE x211 x212) = False;
equal_hl_fitch_rule (HL_FIffE x211 x212) (HL_FMT x41 x42) = False;
equal_hl_fitch_rule (HL_FMT x41 x42) (HL_FIffI x201 x202) = False;
equal_hl_fitch_rule (HL_FIffI x201 x202) (HL_FMT x41 x42) = False;
equal_hl_fitch_rule (HL_FMT x41 x42) (HL_FPropTaut x19) = False;
equal_hl_fitch_rule (HL_FPropTaut x19) (HL_FMT x41 x42) = False;
equal_hl_fitch_rule (HL_FMT x41 x42) HL_FLEM = False;
equal_hl_fitch_rule HL_FLEM (HL_FMT x41 x42) = False;
equal_hl_fitch_rule (HL_FMT x41 x42) (HL_FEqE x171 x172) = False;
equal_hl_fitch_rule (HL_FEqE x171 x172) (HL_FMT x41 x42) = False;
equal_hl_fitch_rule (HL_FMT x41 x42) HL_FEqI = False;
equal_hl_fitch_rule HL_FEqI (HL_FMT x41 x42) = False;
equal_hl_fitch_rule (HL_FMT x41 x42) (HL_FExistsE x151 x152) = False;
equal_hl_fitch_rule (HL_FExistsE x151 x152) (HL_FMT x41 x42) = False;
equal_hl_fitch_rule (HL_FMT x41 x42) (HL_FExistsI x14) = False;
equal_hl_fitch_rule (HL_FExistsI x14) (HL_FMT x41 x42) = False;
equal_hl_fitch_rule (HL_FMT x41 x42) (HL_FForallI x13) = False;
equal_hl_fitch_rule (HL_FForallI x13) (HL_FMT x41 x42) = False;
equal_hl_fitch_rule (HL_FMT x41 x42) (HL_FForallE x12) = False;
equal_hl_fitch_rule (HL_FForallE x12) (HL_FMT x41 x42) = False;
equal_hl_fitch_rule (HL_FMT x41 x42) (HL_FRAA x11) = False;
equal_hl_fitch_rule (HL_FRAA x11) (HL_FMT x41 x42) = False;
equal_hl_fitch_rule (HL_FMT x41 x42) (HL_FOrE x101 x102 x103) = False;
equal_hl_fitch_rule (HL_FOrE x101 x102 x103) (HL_FMT x41 x42) = False;
equal_hl_fitch_rule (HL_FMT x41 x42) (HL_FOrI x9) = False;
equal_hl_fitch_rule (HL_FOrI x9) (HL_FMT x41 x42) = False;
equal_hl_fitch_rule (HL_FMT x41 x42) (HL_FAndE x8) = False;
equal_hl_fitch_rule (HL_FAndE x8) (HL_FMT x41 x42) = False;
equal_hl_fitch_rule (HL_FMT x41 x42) (HL_FAndI x71 x72) = False;
equal_hl_fitch_rule (HL_FAndI x71 x72) (HL_FMT x41 x42) = False;
equal_hl_fitch_rule (HL_FMT x41 x42) (HL_FCP x6) = False;
equal_hl_fitch_rule (HL_FCP x6) (HL_FMT x41 x42) = False;
equal_hl_fitch_rule (HL_FMT x41 x42) (HL_FDN x5) = False;
equal_hl_fitch_rule (HL_FDN x5) (HL_FMT x41 x42) = False;
equal_hl_fitch_rule (HL_FMP x31 x32) (HL_FReit x23) = False;
equal_hl_fitch_rule (HL_FReit x23) (HL_FMP x31 x32) = False;
equal_hl_fitch_rule (HL_FMP x31 x32) (HL_FQN x22) = False;
equal_hl_fitch_rule (HL_FQN x22) (HL_FMP x31 x32) = False;
equal_hl_fitch_rule (HL_FMP x31 x32) (HL_FIffE x211 x212) = False;
equal_hl_fitch_rule (HL_FIffE x211 x212) (HL_FMP x31 x32) = False;
equal_hl_fitch_rule (HL_FMP x31 x32) (HL_FIffI x201 x202) = False;
equal_hl_fitch_rule (HL_FIffI x201 x202) (HL_FMP x31 x32) = False;
equal_hl_fitch_rule (HL_FMP x31 x32) (HL_FPropTaut x19) = False;
equal_hl_fitch_rule (HL_FPropTaut x19) (HL_FMP x31 x32) = False;
equal_hl_fitch_rule (HL_FMP x31 x32) HL_FLEM = False;
equal_hl_fitch_rule HL_FLEM (HL_FMP x31 x32) = False;
equal_hl_fitch_rule (HL_FMP x31 x32) (HL_FEqE x171 x172) = False;
equal_hl_fitch_rule (HL_FEqE x171 x172) (HL_FMP x31 x32) = False;
equal_hl_fitch_rule (HL_FMP x31 x32) HL_FEqI = False;
equal_hl_fitch_rule HL_FEqI (HL_FMP x31 x32) = False;
equal_hl_fitch_rule (HL_FMP x31 x32) (HL_FExistsE x151 x152) = False;
equal_hl_fitch_rule (HL_FExistsE x151 x152) (HL_FMP x31 x32) = False;
equal_hl_fitch_rule (HL_FMP x31 x32) (HL_FExistsI x14) = False;
equal_hl_fitch_rule (HL_FExistsI x14) (HL_FMP x31 x32) = False;
equal_hl_fitch_rule (HL_FMP x31 x32) (HL_FForallI x13) = False;
equal_hl_fitch_rule (HL_FForallI x13) (HL_FMP x31 x32) = False;
equal_hl_fitch_rule (HL_FMP x31 x32) (HL_FForallE x12) = False;
equal_hl_fitch_rule (HL_FForallE x12) (HL_FMP x31 x32) = False;
equal_hl_fitch_rule (HL_FMP x31 x32) (HL_FRAA x11) = False;
equal_hl_fitch_rule (HL_FRAA x11) (HL_FMP x31 x32) = False;
equal_hl_fitch_rule (HL_FMP x31 x32) (HL_FOrE x101 x102 x103) = False;
equal_hl_fitch_rule (HL_FOrE x101 x102 x103) (HL_FMP x31 x32) = False;
equal_hl_fitch_rule (HL_FMP x31 x32) (HL_FOrI x9) = False;
equal_hl_fitch_rule (HL_FOrI x9) (HL_FMP x31 x32) = False;
equal_hl_fitch_rule (HL_FMP x31 x32) (HL_FAndE x8) = False;
equal_hl_fitch_rule (HL_FAndE x8) (HL_FMP x31 x32) = False;
equal_hl_fitch_rule (HL_FMP x31 x32) (HL_FAndI x71 x72) = False;
equal_hl_fitch_rule (HL_FAndI x71 x72) (HL_FMP x31 x32) = False;
equal_hl_fitch_rule (HL_FMP x31 x32) (HL_FCP x6) = False;
equal_hl_fitch_rule (HL_FCP x6) (HL_FMP x31 x32) = False;
equal_hl_fitch_rule (HL_FMP x31 x32) (HL_FDN x5) = False;
equal_hl_fitch_rule (HL_FDN x5) (HL_FMP x31 x32) = False;
equal_hl_fitch_rule (HL_FMP x31 x32) (HL_FMT x41 x42) = False;
equal_hl_fitch_rule (HL_FMT x41 x42) (HL_FMP x31 x32) = False;
equal_hl_fitch_rule HL_FAssume (HL_FReit x23) = False;
equal_hl_fitch_rule (HL_FReit x23) HL_FAssume = False;
equal_hl_fitch_rule HL_FAssume (HL_FQN x22) = False;
equal_hl_fitch_rule (HL_FQN x22) HL_FAssume = False;
equal_hl_fitch_rule HL_FAssume (HL_FIffE x211 x212) = False;
equal_hl_fitch_rule (HL_FIffE x211 x212) HL_FAssume = False;
equal_hl_fitch_rule HL_FAssume (HL_FIffI x201 x202) = False;
equal_hl_fitch_rule (HL_FIffI x201 x202) HL_FAssume = False;
equal_hl_fitch_rule HL_FAssume (HL_FPropTaut x19) = False;
equal_hl_fitch_rule (HL_FPropTaut x19) HL_FAssume = False;
equal_hl_fitch_rule HL_FAssume HL_FLEM = False;
equal_hl_fitch_rule HL_FLEM HL_FAssume = False;
equal_hl_fitch_rule HL_FAssume (HL_FEqE x171 x172) = False;
equal_hl_fitch_rule (HL_FEqE x171 x172) HL_FAssume = False;
equal_hl_fitch_rule HL_FAssume HL_FEqI = False;
equal_hl_fitch_rule HL_FEqI HL_FAssume = False;
equal_hl_fitch_rule HL_FAssume (HL_FExistsE x151 x152) = False;
equal_hl_fitch_rule (HL_FExistsE x151 x152) HL_FAssume = False;
equal_hl_fitch_rule HL_FAssume (HL_FExistsI x14) = False;
equal_hl_fitch_rule (HL_FExistsI x14) HL_FAssume = False;
equal_hl_fitch_rule HL_FAssume (HL_FForallI x13) = False;
equal_hl_fitch_rule (HL_FForallI x13) HL_FAssume = False;
equal_hl_fitch_rule HL_FAssume (HL_FForallE x12) = False;
equal_hl_fitch_rule (HL_FForallE x12) HL_FAssume = False;
equal_hl_fitch_rule HL_FAssume (HL_FRAA x11) = False;
equal_hl_fitch_rule (HL_FRAA x11) HL_FAssume = False;
equal_hl_fitch_rule HL_FAssume (HL_FOrE x101 x102 x103) = False;
equal_hl_fitch_rule (HL_FOrE x101 x102 x103) HL_FAssume = False;
equal_hl_fitch_rule HL_FAssume (HL_FOrI x9) = False;
equal_hl_fitch_rule (HL_FOrI x9) HL_FAssume = False;
equal_hl_fitch_rule HL_FAssume (HL_FAndE x8) = False;
equal_hl_fitch_rule (HL_FAndE x8) HL_FAssume = False;
equal_hl_fitch_rule HL_FAssume (HL_FAndI x71 x72) = False;
equal_hl_fitch_rule (HL_FAndI x71 x72) HL_FAssume = False;
equal_hl_fitch_rule HL_FAssume (HL_FCP x6) = False;
equal_hl_fitch_rule (HL_FCP x6) HL_FAssume = False;
equal_hl_fitch_rule HL_FAssume (HL_FDN x5) = False;
equal_hl_fitch_rule (HL_FDN x5) HL_FAssume = False;
equal_hl_fitch_rule HL_FAssume (HL_FMT x41 x42) = False;
equal_hl_fitch_rule (HL_FMT x41 x42) HL_FAssume = False;
equal_hl_fitch_rule HL_FAssume (HL_FMP x31 x32) = False;
equal_hl_fitch_rule (HL_FMP x31 x32) HL_FAssume = False;
equal_hl_fitch_rule HL_FPremise (HL_FReit x23) = False;
equal_hl_fitch_rule (HL_FReit x23) HL_FPremise = False;
equal_hl_fitch_rule HL_FPremise (HL_FQN x22) = False;
equal_hl_fitch_rule (HL_FQN x22) HL_FPremise = False;
equal_hl_fitch_rule HL_FPremise (HL_FIffE x211 x212) = False;
equal_hl_fitch_rule (HL_FIffE x211 x212) HL_FPremise = False;
equal_hl_fitch_rule HL_FPremise (HL_FIffI x201 x202) = False;
equal_hl_fitch_rule (HL_FIffI x201 x202) HL_FPremise = False;
equal_hl_fitch_rule HL_FPremise (HL_FPropTaut x19) = False;
equal_hl_fitch_rule (HL_FPropTaut x19) HL_FPremise = False;
equal_hl_fitch_rule HL_FPremise HL_FLEM = False;
equal_hl_fitch_rule HL_FLEM HL_FPremise = False;
equal_hl_fitch_rule HL_FPremise (HL_FEqE x171 x172) = False;
equal_hl_fitch_rule (HL_FEqE x171 x172) HL_FPremise = False;
equal_hl_fitch_rule HL_FPremise HL_FEqI = False;
equal_hl_fitch_rule HL_FEqI HL_FPremise = False;
equal_hl_fitch_rule HL_FPremise (HL_FExistsE x151 x152) = False;
equal_hl_fitch_rule (HL_FExistsE x151 x152) HL_FPremise = False;
equal_hl_fitch_rule HL_FPremise (HL_FExistsI x14) = False;
equal_hl_fitch_rule (HL_FExistsI x14) HL_FPremise = False;
equal_hl_fitch_rule HL_FPremise (HL_FForallI x13) = False;
equal_hl_fitch_rule (HL_FForallI x13) HL_FPremise = False;
equal_hl_fitch_rule HL_FPremise (HL_FForallE x12) = False;
equal_hl_fitch_rule (HL_FForallE x12) HL_FPremise = False;
equal_hl_fitch_rule HL_FPremise (HL_FRAA x11) = False;
equal_hl_fitch_rule (HL_FRAA x11) HL_FPremise = False;
equal_hl_fitch_rule HL_FPremise (HL_FOrE x101 x102 x103) = False;
equal_hl_fitch_rule (HL_FOrE x101 x102 x103) HL_FPremise = False;
equal_hl_fitch_rule HL_FPremise (HL_FOrI x9) = False;
equal_hl_fitch_rule (HL_FOrI x9) HL_FPremise = False;
equal_hl_fitch_rule HL_FPremise (HL_FAndE x8) = False;
equal_hl_fitch_rule (HL_FAndE x8) HL_FPremise = False;
equal_hl_fitch_rule HL_FPremise (HL_FAndI x71 x72) = False;
equal_hl_fitch_rule (HL_FAndI x71 x72) HL_FPremise = False;
equal_hl_fitch_rule HL_FPremise (HL_FCP x6) = False;
equal_hl_fitch_rule (HL_FCP x6) HL_FPremise = False;
equal_hl_fitch_rule HL_FPremise (HL_FDN x5) = False;
equal_hl_fitch_rule (HL_FDN x5) HL_FPremise = False;
equal_hl_fitch_rule HL_FPremise (HL_FMT x41 x42) = False;
equal_hl_fitch_rule (HL_FMT x41 x42) HL_FPremise = False;
equal_hl_fitch_rule HL_FPremise (HL_FMP x31 x32) = False;
equal_hl_fitch_rule (HL_FMP x31 x32) HL_FPremise = False;
equal_hl_fitch_rule HL_FPremise HL_FAssume = False;
equal_hl_fitch_rule HL_FAssume HL_FPremise = False;
equal_hl_fitch_rule (HL_FReit x23) (HL_FReit y23) = equal_int x23 y23;
equal_hl_fitch_rule (HL_FQN x22) (HL_FQN y22) = equal_int x22 y22;
equal_hl_fitch_rule (HL_FIffE x211 x212) (HL_FIffE y211 y212) =
  equal_int x211 y211 && equal_int x212 y212;
equal_hl_fitch_rule (HL_FIffI x201 x202) (HL_FIffI y201 y202) =
  equal_int x201 y201 && equal_int x202 y202;
equal_hl_fitch_rule (HL_FPropTaut x19) (HL_FPropTaut y19) = x19 == y19;
equal_hl_fitch_rule (HL_FEqE x171 x172) (HL_FEqE y171 y172) =
  equal_int x171 y171 && equal_int x172 y172;
equal_hl_fitch_rule (HL_FExistsE x151 x152) (HL_FExistsE y151 y152) =
  equal_int x151 y151 && x152 == y152;
equal_hl_fitch_rule (HL_FExistsI x14) (HL_FExistsI y14) = equal_int x14 y14;
equal_hl_fitch_rule (HL_FForallI x13) (HL_FForallI y13) = equal_int x13 y13;
equal_hl_fitch_rule (HL_FForallE x12) (HL_FForallE y12) = equal_int x12 y12;
equal_hl_fitch_rule (HL_FRAA x11) (HL_FRAA y11) = x11 == y11;
equal_hl_fitch_rule (HL_FOrE x101 x102 x103) (HL_FOrE y101 y102 y103) =
  equal_int x101 y101 && x102 == y102 && x103 == y103;
equal_hl_fitch_rule (HL_FOrI x9) (HL_FOrI y9) = equal_int x9 y9;
equal_hl_fitch_rule (HL_FAndE x8) (HL_FAndE y8) = equal_int x8 y8;
equal_hl_fitch_rule (HL_FAndI x71 x72) (HL_FAndI y71 y72) =
  equal_int x71 y71 && equal_int x72 y72;
equal_hl_fitch_rule (HL_FCP x6) (HL_FCP y6) = x6 == y6;
equal_hl_fitch_rule (HL_FDN x5) (HL_FDN y5) = equal_int x5 y5;
equal_hl_fitch_rule (HL_FMT x41 x42) (HL_FMT y41 y42) =
  equal_int x41 y41 && equal_int x42 y42;
equal_hl_fitch_rule (HL_FMP x31 x32) (HL_FMP y31 y32) =
  equal_int x31 y31 && equal_int x32 y32;
equal_hl_fitch_rule HL_FLEM HL_FLEM = True;
equal_hl_fitch_rule HL_FEqI HL_FEqI = True;
equal_hl_fitch_rule HL_FAssume HL_FAssume = True;
equal_hl_fitch_rule HL_FPremise HL_FPremise = True;

hlFitchPremiseNumbers :: [Hl_fitch_item] -> [Int];
hlFitchPremiseNumbers [] = [];
hlFitchPremiseNumbers (HL_FLine n p r : rest) =
  (if equal_hl_fitch_rule r HL_FPremise then n : hlFitchPremiseNumbers rest
    else hlFitchPremiseNumbers rest);
hlFitchPremiseNumbers (HL_FSub s : rest) = hlFitchPremiseNumbers rest;

hlFitchScopeRecord :: Set Int -> [Hl_fitch_item] -> [(Int, Set Int)];
hlFitchScopeRecord scope [] = [];
hlFitchScopeRecord scope (HL_FLine n p r : rest) =
  (n, scope) : hlFitchScopeRecord scope rest;
hlFitchScopeRecord scope (HL_FSub (HL_Subproof a p body) : rest) =
  (a, insert a scope) :
    hlFitchScopeRecord (insert a scope) body ++ hlFitchScopeRecord scope rest;

hlFitchScopeOf :: [Hl_fitch_item] -> Int -> Set Int;
hlFitchScopeOf f n =
  (case map_of (hlFitchScopeRecord (Set (hlFitchPremiseNumbers f)) f) n of {
    Nothing -> bot_set;
    Just scope -> scope;
  });

hlScopeSrc :: [Hl_fitch_item] -> [Hl_line] -> Int -> Set Int -> Set Int;
hlScopeSrc f p n g = hlFitchScopeOf f n;

plus_int :: Int -> Int -> Int;
plus_int k l = Int_of_integer (integer_of_int k + integer_of_int l);

one_int :: Int;
one_int = Int_of_integer (1 :: Integer);

hlNumberPremises :: Int -> [(Int, Hl_formula)] -> [(Int, (Int, Hl_formula))];
hlNumberPremises next [] = [];
hlNumberPremises next ((source, phi) : premises) =
  (source, (next, phi)) : hlNumberPremises (plus_int next one_int) premises;

hlPremisesOf :: Hl_derivation -> [(Int, Hl_formula)];
hlPremisesOf (HL_Derivation phi r) =
  (case r of {
    HL_DAssume _ -> [];
    HL_DPremise i -> [(i, phi)];
    HL_DMP d1 d2 -> hlPremisesOf d1 ++ hlPremisesOf d2;
    HL_DMT d1 d2 -> hlPremisesOf d1 ++ hlPremisesOf d2;
    HL_DDN a -> hlPremisesOf a;
    HL_DCP _ _ a -> hlPremisesOf a;
    HL_DAndI d1 d2 -> hlPremisesOf d1 ++ hlPremisesOf d2;
    HL_DAndE a -> hlPremisesOf a;
    HL_DOrI a -> hlPremisesOf a;
    HL_DOrE d0 _ _ d1 _ _ d2 ->
      hlPremisesOf d0 ++ hlPremisesOf d1 ++ hlPremisesOf d2;
    HL_DRAA _ _ a -> hlPremisesOf a;
    HL_DForallE a -> hlPremisesOf a;
    HL_DForallI a -> hlPremisesOf a;
    HL_DExistsI a -> hlPremisesOf a;
    HL_DExistsE d0 _ _ d -> hlPremisesOf d0 ++ hlPremisesOf d;
    HL_DEqI -> [];
    HL_DEqE d1 d2 -> hlPremisesOf d1 ++ hlPremisesOf d2;
    HL_DLEM -> [];
    HL_DPropTaut a -> concatMap hlPremisesOf a;
    HL_DIffI d1 d2 -> hlPremisesOf d1 ++ hlPremisesOf d2;
    HL_DIffE d1 d2 -> hlPremisesOf d1 ++ hlPremisesOf d2;
    HL_DQN a -> hlPremisesOf a;
  });

hlPremiseEnvironment :: Hl_derivation -> [(Int, (Int, Hl_formula))];
hlPremiseEnvironment d =
  hlNumberPremises one_int (sort_key fst (remdups (hlPremisesOf d)));

hlDerivationFormulas :: Hl_derivation -> [Hl_formula];
hlDerivationFormulas (HL_Derivation phi r) =
  phi : (case r of {
          HL_DAssume _ -> [];
          HL_DPremise _ -> [];
          HL_DMP d1 d2 -> hlDerivationFormulas d1 ++ hlDerivationFormulas d2;
          HL_DMT d1 d2 -> hlDerivationFormulas d1 ++ hlDerivationFormulas d2;
          HL_DDN a -> hlDerivationFormulas a;
          HL_DCP _ p d -> p : hlDerivationFormulas d;
          HL_DAndI d1 d2 -> hlDerivationFormulas d1 ++ hlDerivationFormulas d2;
          HL_DAndE a -> hlDerivationFormulas a;
          HL_DOrI a -> hlDerivationFormulas a;
          HL_DOrE d0 _ p1 d1 _ p2 d2 ->
            p1 : p2 : hlDerivationFormulas d0 ++
                        hlDerivationFormulas d1 ++ hlDerivationFormulas d2;
          HL_DRAA _ p d -> p : hlDerivationFormulas d;
          HL_DForallE a -> hlDerivationFormulas a;
          HL_DForallI a -> hlDerivationFormulas a;
          HL_DExistsI a -> hlDerivationFormulas a;
          HL_DExistsE d0 _ p d ->
            p : hlDerivationFormulas d0 ++ hlDerivationFormulas d;
          HL_DEqI -> [];
          HL_DEqE d1 d2 -> hlDerivationFormulas d1 ++ hlDerivationFormulas d2;
          HL_DLEM -> [];
          HL_DPropTaut a -> concatMap hlDerivationFormulas a;
          HL_DIffI d1 d2 -> hlDerivationFormulas d1 ++ hlDerivationFormulas d2;
          HL_DIffE d1 d2 -> hlDerivationFormulas d1 ++ hlDerivationFormulas d2;
          HL_DQN a -> hlDerivationFormulas a;
        });

hlPremiseFitchLines :: [(Int, (Int, Hl_formula))] -> [Hl_fitch_item];
hlPremiseFitchLines env =
  map (\ (_, (n, phi)) -> HL_FLine n phi HL_FPremise) env;

size_hl_derivation :: Hl_derivation -> Nat;
size_hl_derivation (HL_Derivation x11 x12) =
  plus_nat (size_hl_derivation_rule x12) (suc zero_nat);

size_hl_derivation_rule :: Hl_derivation_rule -> Nat;
size_hl_derivation_rule (HL_DAssume x21) = zero_nat;
size_hl_derivation_rule (HL_DPremise x22) = zero_nat;
size_hl_derivation_rule (HL_DMP x231 x232) =
  plus_nat (plus_nat (size_hl_derivation x231) (size_hl_derivation x232))
    (suc zero_nat);
size_hl_derivation_rule (HL_DMT x241 x242) =
  plus_nat (plus_nat (size_hl_derivation x241) (size_hl_derivation x242))
    (suc zero_nat);
size_hl_derivation_rule (HL_DDN x25) =
  plus_nat (size_hl_derivation x25) (suc zero_nat);
size_hl_derivation_rule (HL_DCP x261 x262 x263) =
  plus_nat (size_hl_derivation x263) (suc zero_nat);
size_hl_derivation_rule (HL_DAndI x271 x272) =
  plus_nat (plus_nat (size_hl_derivation x271) (size_hl_derivation x272))
    (suc zero_nat);
size_hl_derivation_rule (HL_DAndE x28) =
  plus_nat (size_hl_derivation x28) (suc zero_nat);
size_hl_derivation_rule (HL_DOrI x29) =
  plus_nat (size_hl_derivation x29) (suc zero_nat);
size_hl_derivation_rule (HL_DOrE x2101 x2102 x2103 x2104 x2105 x2106 x2107) =
  plus_nat
    (plus_nat (plus_nat (size_hl_derivation x2101) (size_hl_derivation x2104))
      (size_hl_derivation x2107))
    (suc zero_nat);
size_hl_derivation_rule (HL_DRAA x2111 x2112 x2113) =
  plus_nat (size_hl_derivation x2113) (suc zero_nat);
size_hl_derivation_rule (HL_DForallE x212) =
  plus_nat (size_hl_derivation x212) (suc zero_nat);
size_hl_derivation_rule (HL_DForallI x213) =
  plus_nat (size_hl_derivation x213) (suc zero_nat);
size_hl_derivation_rule (HL_DExistsI x214) =
  plus_nat (size_hl_derivation x214) (suc zero_nat);
size_hl_derivation_rule (HL_DExistsE x2151 x2152 x2153 x2154) =
  plus_nat (plus_nat (size_hl_derivation x2151) (size_hl_derivation x2154))
    (suc zero_nat);
size_hl_derivation_rule HL_DEqI = zero_nat;
size_hl_derivation_rule (HL_DEqE x2171 x2172) =
  plus_nat (plus_nat (size_hl_derivation x2171) (size_hl_derivation x2172))
    (suc zero_nat);
size_hl_derivation_rule HL_DLEM = zero_nat;
size_hl_derivation_rule (HL_DPropTaut x219) =
  plus_nat (size_list size_hl_derivation x219) (suc zero_nat);
size_hl_derivation_rule (HL_DIffI x2201 x2202) =
  plus_nat (plus_nat (size_hl_derivation x2201) (size_hl_derivation x2202))
    (suc zero_nat);
size_hl_derivation_rule (HL_DIffE x2211 x2212) =
  plus_nat (plus_nat (size_hl_derivation x2211) (size_hl_derivation x2212))
    (suc zero_nat);
size_hl_derivation_rule (HL_DQN x222) =
  plus_nat (size_hl_derivation x222) (suc zero_nat);

hlDerivationFormula :: Hl_derivation -> Hl_formula;
hlDerivationFormula (HL_Derivation x1 x2) = x1;

hlConstantsInScope :: [Hl_formula] -> Set String;
hlConstantsInScope scope = sup_seta (image hlConstantsInFormula (Set scope));

minus_set :: forall a. (Eq a) => Set a -> Set a -> Set a;
minus_set a (Set xs) = fold remove xs a;
minus_set a (Coset xs) = Set (filter (\ x -> member x a) xs);

inf_set :: forall a. (Eq a) => Set a -> Set a -> Set a;
inf_set a (Set xs) = Set (filter (\ x -> member x a) xs);
inf_set a (Coset xs) = fold remove xs a;

hlForallRepairConstants ::
  [Hl_formula] -> Hl_formula -> Hl_derivation -> [String];
hlForallRepairConstants scope goal d =
  sorted_list_of_set
    (inf_set
      (minus_set (hlConstantsInFormula (hlDerivationFormula d))
        (hlConstantsInFormula goal))
      (hlConstantsInScope scope));

hlExistsRepairConstants ::
  [Hl_formula] -> Hl_formula -> Hl_derivation -> Hl_formula -> [String];
hlExistsRepairConstants scope assumption source goal =
  sorted_list_of_set
    (inf_set
      (minus_set (hlConstantsInFormula assumption)
        (sup_set (hlConstantsInFormula (hlDerivationFormula source))
          (hlConstantsInFormula goal)))
      (hlConstantsInScope scope));

hlEmitDerivationsUsing ::
  (Int -> Nat -> Hl_derivation -> ([Hl_fitch_item], (Int, (Int, Nat)))) ->
    Int -> Nat -> [Hl_derivation] -> ([Hl_fitch_item], ([Int], (Int, Nat)));
hlEmitDerivationsUsing emit next count [] = ([], ([], (next, count)));
hlEmitDerivationsUsing emit next count (d : ds) =
  (case emit next count d of {
    (items, (n, (next1, count1))) ->
      (case hlEmitDerivationsUsing emit next1 count1 ds of {
        (more, (numbers, (next2, count2))) ->
          (items ++ more, (n : numbers, (next2, count2)));
      });
  });

hlRenameTerm :: String -> String -> Hl_term -> Hl_term;
hlRenameTerm old new (HL_Var x) = HL_Var x;
hlRenameTerm old new (HL_Const a) = HL_Const (if a == old then new else a);

hlRenameFormula :: String -> String -> Hl_formula -> Hl_formula;
hlRenameFormula old new (HL_Predicate p ts) =
  HL_Predicate p (map (hlRenameTerm old new) ts);
hlRenameFormula old new (HL_Boolean b) = HL_Boolean b;
hlRenameFormula old new (HL_Not p) = HL_Not (hlRenameFormula old new p);
hlRenameFormula old new (HL_And p q) =
  HL_And (hlRenameFormula old new p) (hlRenameFormula old new q);
hlRenameFormula old new (HL_Or p q) =
  HL_Or (hlRenameFormula old new p) (hlRenameFormula old new q);
hlRenameFormula old new (HL_Implies p q) =
  HL_Implies (hlRenameFormula old new p) (hlRenameFormula old new q);
hlRenameFormula old new (HL_Iff p q) =
  HL_Iff (hlRenameFormula old new p) (hlRenameFormula old new q);
hlRenameFormula old new (HL_ForAll x p) =
  HL_ForAll x (hlRenameFormula old new p);
hlRenameFormula old new (HL_Exists x p) =
  HL_Exists x (hlRenameFormula old new p);

hlRenamePairsFormula :: [(String, String)] -> Hl_formula -> Hl_formula;
hlRenamePairsFormula [] p = p;
hlRenamePairsFormula ((old, new) : pairs) p =
  hlRenamePairsFormula pairs (hlRenameFormula old new p);

hlRenameDerivation :: String -> String -> Hl_derivation -> Hl_derivation;
hlRenameDerivation old new (HL_Derivation phi r) =
  HL_Derivation (hlRenameFormula old new phi)
    (case r of {
      HL_DAssume a -> HL_DAssume a;
      HL_DPremise a -> HL_DPremise a;
      HL_DMP d1 d2 ->
        HL_DMP (hlRenameDerivation old new d1) (hlRenameDerivation old new d2);
      HL_DMT d1 d2 ->
        HL_DMT (hlRenameDerivation old new d1) (hlRenameDerivation old new d2);
      HL_DDN d -> HL_DDN (hlRenameDerivation old new d);
      HL_DCP i p d ->
        HL_DCP i (hlRenameFormula old new p) (hlRenameDerivation old new d);
      HL_DAndI d1 d2 ->
        HL_DAndI (hlRenameDerivation old new d1)
          (hlRenameDerivation old new d2);
      HL_DAndE d -> HL_DAndE (hlRenameDerivation old new d);
      HL_DOrI d -> HL_DOrI (hlRenameDerivation old new d);
      HL_DOrE d0 a1 p1 d1 a2 p2 d2 ->
        HL_DOrE (hlRenameDerivation old new d0) a1 (hlRenameFormula old new p1)
          (hlRenameDerivation old new d1) a2 (hlRenameFormula old new p2)
          (hlRenameDerivation old new d2);
      HL_DRAA i p d ->
        HL_DRAA i (hlRenameFormula old new p) (hlRenameDerivation old new d);
      HL_DForallE d -> HL_DForallE (hlRenameDerivation old new d);
      HL_DForallI d -> HL_DForallI (hlRenameDerivation old new d);
      HL_DExistsI d -> HL_DExistsI (hlRenameDerivation old new d);
      HL_DExistsE d0 i p d ->
        HL_DExistsE (hlRenameDerivation old new d0) i
          (hlRenameFormula old new p) (hlRenameDerivation old new d);
      HL_DEqI -> HL_DEqI;
      HL_DEqE d1 d2 ->
        HL_DEqE (hlRenameDerivation old new d1) (hlRenameDerivation old new d2);
      HL_DLEM -> HL_DLEM;
      HL_DPropTaut ds -> HL_DPropTaut (map (hlRenameDerivation old new) ds);
      HL_DIffI d1 d2 ->
        HL_DIffI (hlRenameDerivation old new d1)
          (hlRenameDerivation old new d2);
      HL_DIffE d1 d2 ->
        HL_DIffE (hlRenameDerivation old new d1)
          (hlRenameDerivation old new d2);
      HL_DQN d -> HL_DQN (hlRenameDerivation old new d);
    });

hlFreshIndex :: Nat -> Nat -> String;
hlFreshIndex base k =
  implode
    (replicate (plus_nat base k)
      (Char True True False False False True True False));

hlRepairDerivation ::
  Nat ->
    Nat ->
      [String] -> Hl_derivation -> (Nat, ([(String, String)], Hl_derivation));
hlRepairDerivation base count [] d = (count, ([], d));
hlRepairDerivation base count (old : olds) d =
  let {
    new = hlFreshIndex base count;
    da = hlRenameDerivation old new d;
  } in (case hlRepairDerivation base (suc count) olds da of {
         (counta, (pairs, result)) -> (counta, ((old, new) : pairs, result));
       });

hlEnvironmentLine :: [(Int, (Int, Hl_formula))] -> Int -> Int;
hlEnvironmentLine [] source = zero_int;
hlEnvironmentLine ((i, (n, p)) : env) source =
  (if equal_int i source then n else hlEnvironmentLine env source);

hlEmitDerivationFuel ::
  [()] ->
    Nat ->
      [(Int, (Int, Hl_formula))] ->
        [Hl_formula] ->
          Int -> Nat -> Hl_derivation -> ([Hl_fitch_item], (Int, (Int, Nat)));
hlEmitDerivationFuel [] base env scope next count d =
  ([], (zero_int, (next, count)));
hlEmitDerivationFuel (uu : fuel) base env scope next count
  (HL_Derivation phi rule) =
  (case rule of {
    HL_DAssume i -> ([], (hlEnvironmentLine env i, (next, count)));
    HL_DPremise i -> ([], (hlEnvironmentLine env i, (next, count)));
    HL_DMP d1 d2 ->
      (case hlEmitDerivationFuel fuel base env scope next count d1 of {
        (items1, (n1, (next1, count1))) ->
          (case hlEmitDerivationFuel fuel base env scope next1 count1 d2 of {
            (items2, (n2, (next2, count2))) ->
              (items1 ++ items2 ++ [HL_FLine next2 phi (HL_FMP n1 n2)],
                (next2, (plus_int next2 one_int, count2)));
          });
      });
    HL_DMT d1 d2 ->
      (case hlEmitDerivationFuel fuel base env scope next count d1 of {
        (items1, (n1, (next1, count1))) ->
          (case hlEmitDerivationFuel fuel base env scope next1 count1 d2 of {
            (items2, (n2, (next2, count2))) ->
              (items1 ++ items2 ++ [HL_FLine next2 phi (HL_FMT n1 n2)],
                (next2, (plus_int next2 one_int, count2)));
          });
      });
    HL_DDN d ->
      (case hlEmitDerivationFuel fuel base env scope next count d of {
        (items, (n, (nexta, counta))) ->
          (items ++ [HL_FLine nexta phi (HL_FDN n)],
            (nexta, (plus_int nexta one_int, counta)));
      });
    HL_DCP a af body ->
      let {
        assumptionLine = next;
      } in (case hlEmitDerivationFuel fuel base
                   ((a, (assumptionLine, af)) : env) (af : scope)
                   (plus_int next one_int) count body
             of {
             (bodyItems, (bodyLine, (next1, count1))) ->
               let {
                 needsReiteration =
                   null bodyItems && not (equal_int bodyLine assumptionLine);
                 closedBody =
                   (if needsReiteration
                     then [HL_FLine next1 (hlDerivationFormula body)
                             (HL_FReit bodyLine)]
                     else bodyItems);
                 lastLine = (if needsReiteration then next1 else bodyLine);
                 afterBox =
                   (if needsReiteration then plus_int next1 one_int else next1);
               } in ([HL_FSub (HL_Subproof assumptionLine af closedBody),
                       HL_FLine afterBox phi
                         (HL_FCP (assumptionLine, lastLine))],
                      (afterBox, (plus_int afterBox one_int, count1)));
           });
    HL_DAndI d1 d2 ->
      (case hlEmitDerivationFuel fuel base env scope next count d1 of {
        (items1, (n1, (next1, count1))) ->
          (case hlEmitDerivationFuel fuel base env scope next1 count1 d2 of {
            (items2, (n2, (next2, count2))) ->
              (items1 ++ items2 ++ [HL_FLine next2 phi (HL_FAndI n1 n2)],
                (next2, (plus_int next2 one_int, count2)));
          });
      });
    HL_DAndE d ->
      (case hlEmitDerivationFuel fuel base env scope next count d of {
        (items, (n, (nexta, counta))) ->
          (items ++ [HL_FLine nexta phi (HL_FAndE n)],
            (nexta, (plus_int nexta one_int, counta)));
      });
    HL_DOrI d ->
      (case hlEmitDerivationFuel fuel base env scope next count d of {
        (items, (n, (nexta, counta))) ->
          (items ++ [HL_FLine nexta phi (HL_FOrI n)],
            (nexta, (plus_int nexta one_int, counta)));
      });
    HL_DOrE d0 a1 f1 b1 a2 f2 b2 ->
      (case hlEmitDerivationFuel fuel base env scope next count d0 of {
        (items0, (n0, (next0, count0))) ->
          let {
            assumption1 = next0;
          } in (case hlEmitDerivationFuel fuel base
                       ((a1, (assumption1, f1)) : env) (f1 : scope)
                       (plus_int next0 one_int) count0 b1
                 of {
                 (body1, (line1, (next1, count1))) ->
                   let {
                     reiterate1 =
                       null body1 && not (equal_int line1 assumption1);
                     closed1 =
                       (if reiterate1
                         then [HL_FLine next1 (hlDerivationFormula b1)
                                 (HL_FReit line1)]
                         else body1);
                     last1 = (if reiterate1 then next1 else line1);
                     after1 =
                       (if reiterate1 then plus_int next1 one_int else next1);
                     assumption2 = after1;
                   } in (case hlEmitDerivationFuel fuel base
                                ((a2, (assumption2, f2)) : env) (f2 : scope)
                                (plus_int after1 one_int) count1 b2
                          of {
                          (body2, (line2, (next2, count2))) ->
                            let {
                              reiterate2 =
                                null body2 && not (equal_int line2 assumption2);
                              closed2 =
                                (if reiterate2
                                  then [HL_FLine next2 (hlDerivationFormula b2)
  (HL_FReit line2)]
                                  else body2);
                              last2 = (if reiterate2 then next2 else line2);
                              after2 =
                                (if reiterate2 then plus_int next2 one_int
                                  else next2);
                            } in (items0 ++
                                    [HL_FSub
                                       (HL_Subproof assumption1 f1 closed1),
                                      HL_FSub
(HL_Subproof assumption2 f2 closed2),
                                      HL_FLine after2 phi
(HL_FOrE n0 (assumption1, last1) (assumption2, last2))],
                                   (after2, (plus_int after2 one_int, count2)));
                        });
               });
      });
    HL_DRAA a af body ->
      let {
        assumptionLine = next;
      } in (case hlEmitDerivationFuel fuel base
                   ((a, (assumptionLine, af)) : env) (af : scope)
                   (plus_int next one_int) count body
             of {
             (bodyItems, (bodyLine, (next1, count1))) ->
               let {
                 needsReiteration =
                   null bodyItems && not (equal_int bodyLine assumptionLine);
                 closedBody =
                   (if needsReiteration
                     then [HL_FLine next1 (hlDerivationFormula body)
                             (HL_FReit bodyLine)]
                     else bodyItems);
                 lastLine = (if needsReiteration then next1 else bodyLine);
                 afterBox =
                   (if needsReiteration then plus_int next1 one_int else next1);
               } in ([HL_FSub (HL_Subproof assumptionLine af closedBody),
                       HL_FLine afterBox phi
                         (HL_FRAA (assumptionLine, lastLine))],
                      (afterBox, (plus_int afterBox one_int, count1)));
           });
    HL_DForallE d ->
      (case hlEmitDerivationFuel fuel base env scope next count d of {
        (items, (n, (nexta, counta))) ->
          (items ++ [HL_FLine nexta phi (HL_FForallE n)],
            (nexta, (plus_int nexta one_int, counta)));
      });
    HL_DForallI d ->
      let {
        bad = hlForallRepairConstants scope phi d;
      } in (case hlRepairDerivation base count bad d of {
             (count0, (_, repaired)) ->
               (case hlEmitDerivationFuel fuel base env scope next count0
                       repaired
                 of {
                 (items, (n, (nexta, counta))) ->
                   (items ++ [HL_FLine nexta phi (HL_FForallI n)],
                     (nexta, (plus_int nexta one_int, counta)));
               });
           });
    HL_DExistsI d ->
      (case hlEmitDerivationFuel fuel base env scope next count d of {
        (items, (n, (nexta, counta))) ->
          (items ++ [HL_FLine nexta phi (HL_FExistsI n)],
            (nexta, (plus_int nexta one_int, counta)));
      });
    HL_DExistsE source a af body ->
      (case hlEmitDerivationFuel fuel base env scope next count source of {
        (sourceItems, (sourceLine, (next0, count0))) ->
          let {
            bad = hlExistsRepairConstants scope af source phi;
          } in (case hlRepairDerivation base count0 bad body of {
                 (countR, (pairs, repairedBody)) ->
                   let {
                     repairedAssumption = hlRenamePairsFormula pairs af;
                     assumptionLine = next0;
                   } in (case hlEmitDerivationFuel fuel base
                                ((a, (assumptionLine, repairedAssumption)) :
                                  env)
                                (repairedAssumption : scope)
                                (plus_int next0 one_int) countR repairedBody
                          of {
                          (bodyItems, (bodyLine, (next1, count1))) ->
                            let {
                              needsReiteration =
                                null bodyItems &&
                                  not (equal_int bodyLine assumptionLine);
                              closedBody =
                                (if needsReiteration
                                  then [HL_FLine next1
  (hlDerivationFormula repairedBody) (HL_FReit bodyLine)]
                                  else bodyItems);
                              lastLine =
                                (if needsReiteration then next1 else bodyLine);
                              afterBox =
                                (if needsReiteration then plus_int next1 one_int
                                  else next1);
                            } in (sourceItems ++
                                    [HL_FSub
                                       (HL_Subproof assumptionLine
 repairedAssumption closedBody),
                                      HL_FLine afterBox phi
(HL_FExistsE sourceLine (assumptionLine, lastLine))],
                                   (afterBox,
                                     (plus_int afterBox one_int, count1)));
                        });
               });
      });
    HL_DEqI ->
      ([HL_FLine next phi HL_FEqI], (next, (plus_int next one_int, count)));
    HL_DEqE d1 d2 ->
      (case hlEmitDerivationFuel fuel base env scope next count d1 of {
        (items1, (n1, (next1, count1))) ->
          (case hlEmitDerivationFuel fuel base env scope next1 count1 d2 of {
            (items2, (n2, (next2, count2))) ->
              (items1 ++ items2 ++ [HL_FLine next2 phi (HL_FEqE n1 n2)],
                (next2, (plus_int next2 one_int, count2)));
          });
      });
    HL_DLEM ->
      ([HL_FLine next phi HL_FLEM], (next, (plus_int next one_int, count)));
    HL_DPropTaut ds ->
      (case hlEmitDerivationsUsing (hlEmitDerivationFuel fuel base env scope)
              next count ds
        of {
        (items, (numbers, (nexta, counta))) ->
          (items ++ [HL_FLine nexta phi (HL_FPropTaut numbers)],
            (nexta, (plus_int nexta one_int, counta)));
      });
    HL_DIffI d1 d2 ->
      (case hlEmitDerivationFuel fuel base env scope next count d1 of {
        (items1, (n1, (next1, count1))) ->
          (case hlEmitDerivationFuel fuel base env scope next1 count1 d2 of {
            (items2, (n2, (next2, count2))) ->
              (items1 ++ items2 ++ [HL_FLine next2 phi (HL_FIffI n1 n2)],
                (next2, (plus_int next2 one_int, count2)));
          });
      });
    HL_DIffE d1 d2 ->
      (case hlEmitDerivationFuel fuel base env scope next count d1 of {
        (items1, (n1, (next1, count1))) ->
          (case hlEmitDerivationFuel fuel base env scope next1 count1 d2 of {
            (items2, (n2, (next2, count2))) ->
              (items1 ++ items2 ++ [HL_FLine next2 phi (HL_FIffE n1 n2)],
                (next2, (plus_int next2 one_int, count2)));
          });
      });
    HL_DQN d ->
      (case hlEmitDerivationFuel fuel base env scope next count d of {
        (items, (n, (nexta, counta))) ->
          (items ++ [HL_FLine nexta phi (HL_FQN n)],
            (nexta, (plus_int nexta one_int, counta)));
      });
  });

hlEmitDerivation ::
  Nat ->
    [(Int, (Int, Hl_formula))] ->
      [Hl_formula] ->
        Int -> Nat -> Hl_derivation -> ([Hl_fitch_item], (Int, (Int, Nat)));
hlEmitDerivation base env scope next count d =
  hlEmitDerivationFuel (replicate (suc (size_hl_derivation d)) ()) base env
    scope next count d;

int_of_nat :: Nat -> Int;
int_of_nat n = Int_of_integer (integer_of_nat n);

hlDerivationToFitch :: Hl_derivation -> [Hl_fitch_item];
hlDerivationToFitch d =
  let {
    env = hlPremiseEnvironment d;
    premiseLines = hlPremiseFitchLines env;
    base =
      suc (maxlen
            (sorted_list_of_set
              (sup_seta
                (image hlConstantsInFormula (Set (hlDerivationFormulas d))))));
  } in (case hlEmitDerivation base env (map (\ (_, (_, phi)) -> phi) env)
               (plus_int one_int (int_of_nat (size_lista env))) zero_nat d
         of {
         (body, (_, (_, _))) -> premiseLines ++ body;
       });

hlClassifyAssumptions :: Set Int -> Hl_derivation -> Hl_derivation;
hlClassifyAssumptions bound (HL_Derivation phi rule) =
  HL_Derivation phi
    (case rule of {
      HL_DAssume i -> (if member i bound then HL_DAssume i else HL_DPremise i);
      HL_DPremise i -> (if member i bound then HL_DAssume i else HL_DPremise i);
      HL_DMP d1 d2 ->
        HL_DMP (hlClassifyAssumptions bound d1)
          (hlClassifyAssumptions bound d2);
      HL_DMT d1 d2 ->
        HL_DMT (hlClassifyAssumptions bound d1)
          (hlClassifyAssumptions bound d2);
      HL_DDN d -> HL_DDN (hlClassifyAssumptions bound d);
      HL_DCP i p d -> HL_DCP i p (hlClassifyAssumptions (insert i bound) d);
      HL_DAndI d1 d2 ->
        HL_DAndI (hlClassifyAssumptions bound d1)
          (hlClassifyAssumptions bound d2);
      HL_DAndE d -> HL_DAndE (hlClassifyAssumptions bound d);
      HL_DOrI d -> HL_DOrI (hlClassifyAssumptions bound d);
      HL_DOrE d0 a1 p1 d1 a2 p2 d2 ->
        HL_DOrE (hlClassifyAssumptions bound d0) a1 p1
          (hlClassifyAssumptions (insert a1 bound) d1) a2 p2
          (hlClassifyAssumptions (insert a2 bound) d2);
      HL_DRAA i p d -> HL_DRAA i p (hlClassifyAssumptions (insert i bound) d);
      HL_DForallE d -> HL_DForallE (hlClassifyAssumptions bound d);
      HL_DForallI d -> HL_DForallI (hlClassifyAssumptions bound d);
      HL_DExistsI d -> HL_DExistsI (hlClassifyAssumptions bound d);
      HL_DExistsE d0 i p d ->
        HL_DExistsE (hlClassifyAssumptions bound d0) i p
          (hlClassifyAssumptions (insert i bound) d);
      HL_DEqI -> HL_DEqI;
      HL_DEqE d1 d2 ->
        HL_DEqE (hlClassifyAssumptions bound d1)
          (hlClassifyAssumptions bound d2);
      HL_DLEM -> HL_DLEM;
      HL_DPropTaut ds -> HL_DPropTaut (map (hlClassifyAssumptions bound) ds);
      HL_DIffI d1 d2 ->
        HL_DIffI (hlClassifyAssumptions bound d1)
          (hlClassifyAssumptions bound d2);
      HL_DIffE d1 d2 ->
        HL_DIffE (hlClassifyAssumptions bound d1)
          (hlClassifyAssumptions bound d2);
      HL_DQN d -> HL_DQN (hlClassifyAssumptions bound d);
    });

hlBoxesOf :: [Hl_line] -> [(Int, Int)];
hlBoxesOf p = concatMap (hlDischargePairs . hlJustification) p;

hlDischargedAssumptions :: [Hl_line] -> [Int];
hlDischargedAssumptions p = map fst (hlBoxesOf p);

hlSequenceOptions :: forall a. [Maybe a] -> Maybe [a];
hlSequenceOptions [] = Just [];
hlSequenceOptions (Nothing : xs) = Nothing;
hlSequenceOptions (Just x : xs) =
  map_option (\ a -> x : a) (hlSequenceOptions xs);

hlUnfoldDerivation :: Nat -> [Hl_line] -> Int -> Maybe Hl_derivation;
hlUnfoldDerivation fuel p n =
  (if equal_nat fuel zero_nat then Nothing
    else (case hlLookupLine p n of {
           Nothing -> Nothing;
           Just l ->
             let {
               phi = hlFormula l;
               node = HL_Derivation phi;
             } in (case hlJustification l of {
                    HL_Assumption ->
                      Just (node (if membera (hlDischargedAssumptions p) n
                                   then HL_DAssume n else HL_DPremise n));
                    HL_MP m k ->
                      (case (hlUnfoldDerivation (minus_nat fuel one_nat) p m,
                              hlUnfoldDerivation (minus_nat fuel one_nat) p k)
                        of {
                        (Nothing, _) -> Nothing;
                        (Just _, Nothing) -> Nothing;
                        (Just d1, Just d2) -> Just (node (HL_DMP d1 d2));
                      });
                    HL_MT m k ->
                      (case (hlUnfoldDerivation (minus_nat fuel one_nat) p m,
                              hlUnfoldDerivation (minus_nat fuel one_nat) p k)
                        of {
                        (Nothing, _) -> Nothing;
                        (Just _, Nothing) -> Nothing;
                        (Just d1, Just d2) -> Just (node (HL_DMT d1 d2));
                      });
                    HL_DN m ->
                      map_option (node . HL_DDN)
                        (hlUnfoldDerivation (minus_nat fuel one_nat) p m);
                    HL_CP a c ->
                      (case (hlFormulaAt p a,
                              hlUnfoldDerivation (minus_nat fuel one_nat) p c)
                        of {
                        (Nothing, _) -> Nothing;
                        (Just _, Nothing) -> Nothing;
                        (Just assumption, Just body) ->
                          Just (node (HL_DCP a assumption body));
                      });
                    HL_AndIntro m k ->
                      (case (hlUnfoldDerivation (minus_nat fuel one_nat) p m,
                              hlUnfoldDerivation (minus_nat fuel one_nat) p k)
                        of {
                        (Nothing, _) -> Nothing;
                        (Just _, Nothing) -> Nothing;
                        (Just d1, Just d2) -> Just (node (HL_DAndI d1 d2));
                      });
                    HL_AndElim m ->
                      map_option (node . HL_DAndE)
                        (hlUnfoldDerivation (minus_nat fuel one_nat) p m);
                    HL_OrIntro m ->
                      map_option (node . HL_DOrI)
                        (hlUnfoldDerivation (minus_nat fuel one_nat) p m);
                    HL_OrElim d a1 c1 a2 c2 ->
                      (case (hlUnfoldDerivation (minus_nat fuel one_nat) p d,
                              (hlFormulaAt p a1,
                                (hlUnfoldDerivation (minus_nat fuel one_nat) p
                                   c1,
                                  (hlFormulaAt p a2,
                                    hlUnfoldDerivation (minus_nat fuel one_nat)
                                      p c2))))
                        of {
                        (Nothing, _) -> Nothing;
                        (Just _, (Nothing, _)) -> Nothing;
                        (Just _, (Just _, (Nothing, _))) -> Nothing;
                        (Just _, (Just _, (Just _, (Nothing, _)))) -> Nothing;
                        (Just _, (Just _, (Just _, (Just _, Nothing)))) ->
                          Nothing;
                        (Just dd, (Just f1, (Just b1, (Just f2, Just b2)))) ->
                          Just (node (HL_DOrE dd a1 f1 b1 a2 f2 b2));
                      });
                    HL_RAA a c ->
                      (case (hlFormulaAt p a,
                              hlUnfoldDerivation (minus_nat fuel one_nat) p c)
                        of {
                        (Nothing, _) -> Nothing;
                        (Just _, Nothing) -> Nothing;
                        (Just assumption, Just body) ->
                          Just (node (HL_DRAA a assumption body));
                      });
                    HL_ForallElim m ->
                      map_option (node . HL_DForallE)
                        (hlUnfoldDerivation (minus_nat fuel one_nat) p m);
                    HL_ExistsIntro m ->
                      map_option (node . HL_DExistsI)
                        (hlUnfoldDerivation (minus_nat fuel one_nat) p m);
                    HL_ForallIntro m ->
                      map_option (node . HL_DForallI)
                        (hlUnfoldDerivation (minus_nat fuel one_nat) p m);
                    HL_ExistsElim m a c ->
                      (case (hlUnfoldDerivation (minus_nat fuel one_nat) p m,
                              (hlFormulaAt p a,
                                hlUnfoldDerivation (minus_nat fuel one_nat) p
                                  c))
                        of {
                        (Nothing, _) -> Nothing;
                        (Just _, (Nothing, _)) -> Nothing;
                        (Just _, (Just _, Nothing)) -> Nothing;
                        (Just source, (Just assumption, Just body)) ->
                          Just (node (HL_DExistsE source a assumption body));
                      });
                    HL_EqIntro -> Just (node HL_DEqI);
                    HL_EqElim m k ->
                      (case (hlUnfoldDerivation (minus_nat fuel one_nat) p m,
                              hlUnfoldDerivation (minus_nat fuel one_nat) p k)
                        of {
                        (Nothing, _) -> Nothing;
                        (Just _, Nothing) -> Nothing;
                        (Just d1, Just d2) -> Just (node (HL_DEqE d1 d2));
                      });
                    HL_LEM -> Just (node HL_DLEM);
                    HL_PropTaut ms ->
                      map_option (node . HL_DPropTaut)
                        (hlSequenceOptions
                          (map (hlUnfoldDerivation (minus_nat fuel one_nat) p)
                            ms));
                    HL_IffIntro m k ->
                      (case (hlUnfoldDerivation (minus_nat fuel one_nat) p m,
                              hlUnfoldDerivation (minus_nat fuel one_nat) p k)
                        of {
                        (Nothing, _) -> Nothing;
                        (Just _, Nothing) -> Nothing;
                        (Just d1, Just d2) -> Just (node (HL_DIffI d1 d2));
                      });
                    HL_IffElim m k ->
                      (case (hlUnfoldDerivation (minus_nat fuel one_nat) p m,
                              hlUnfoldDerivation (minus_nat fuel one_nat) p k)
                        of {
                        (Nothing, _) -> Nothing;
                        (Just _, Nothing) -> Nothing;
                        (Just d1, Just d2) -> Just (node (HL_DIffE d1 d2));
                      });
                    HL_QN m ->
                      map_option (node . HL_DQN)
                        (hlUnfoldDerivation (minus_nat fuel one_nat) p m);
                  });
         }));

hlDependencyClosed :: [Hl_line] -> Bool;
hlDependencyClosed p =
  all (\ l ->
        less_eq_set (hlReferences l)
          (image hlLineNumber
            (filtera
              (\ a -> equal_hl_justification (hlJustification a) HL_Assumption)
              (Set p))))
    p;

hlVerifiedCorrect :: [Hl_line] -> Bool;
hlVerifiedCorrect p = hlCorrect p && hlDependencyClosed p && hlCanonicalOrder p;

hlToDerivation :: [Hl_line] -> Maybe Hl_derivation;
hlToDerivation p =
  (if null p || not (hlVerifiedCorrect p) then Nothing
    else map_option (hlClassifyAssumptions bot_set)
           (hlUnfoldDerivation (suc (size_lista p)) p (hlLineNumber (last p))));

hlFitchCitedLines :: Hl_fitch_rule -> [Int];
hlFitchCitedLines HL_FPremise = [];
hlFitchCitedLines HL_FAssume = [];
hlFitchCitedLines (HL_FMP m n) = [m, n];
hlFitchCitedLines (HL_FMT m n) = [m, n];
hlFitchCitedLines (HL_FDN m) = [m];
hlFitchCitedLines (HL_FCP s) = [];
hlFitchCitedLines (HL_FAndI m n) = [m, n];
hlFitchCitedLines (HL_FAndE m) = [m];
hlFitchCitedLines (HL_FOrI m) = [m];
hlFitchCitedLines (HL_FOrE d s1 s2) = [d];
hlFitchCitedLines (HL_FRAA s) = [];
hlFitchCitedLines (HL_FForallE m) = [m];
hlFitchCitedLines (HL_FForallI m) = [m];
hlFitchCitedLines (HL_FExistsI m) = [m];
hlFitchCitedLines (HL_FExistsE m s) = [m];
hlFitchCitedLines HL_FEqI = [];
hlFitchCitedLines (HL_FEqE m n) = [m, n];
hlFitchCitedLines HL_FLEM = [];
hlFitchCitedLines (HL_FPropTaut ms) = ms;
hlFitchCitedLines (HL_FIffI m n) = [m, n];
hlFitchCitedLines (HL_FIffE m n) = [m, n];
hlFitchCitedLines (HL_FQN m) = [m];
hlFitchCitedLines (HL_FReit m) = [m];

hlFitchDependenciesOf :: (Int -> Set Int) -> Hl_fitch_rule -> Int -> Set Int;
hlFitchDependenciesOf look r self =
  (case r of {
    HL_FPremise -> insert self bot_set;
    HL_FAssume -> insert self bot_set;
    HL_FMP _ _ -> sup_seta (Set (map look (hlFitchCitedLines r)));
    HL_FMT _ _ -> sup_seta (Set (map look (hlFitchCitedLines r)));
    HL_FDN _ -> sup_seta (Set (map look (hlFitchCitedLines r)));
    HL_FCP (a, c) -> remove a (look c);
    HL_FAndI _ _ -> sup_seta (Set (map look (hlFitchCitedLines r)));
    HL_FAndE _ -> sup_seta (Set (map look (hlFitchCitedLines r)));
    HL_FOrI _ -> sup_seta (Set (map look (hlFitchCitedLines r)));
    HL_FOrE d (a1, c1) (a2, c2) ->
      sup_set (sup_set (look d) (remove a1 (look c1))) (remove a2 (look c2));
    HL_FRAA (a, c) -> remove a (look c);
    HL_FForallE _ -> sup_seta (Set (map look (hlFitchCitedLines r)));
    HL_FForallI _ -> sup_seta (Set (map look (hlFitchCitedLines r)));
    HL_FExistsI _ -> sup_seta (Set (map look (hlFitchCitedLines r)));
    HL_FExistsE m (a, c) -> sup_set (look m) (remove a (look c));
    HL_FEqI -> sup_seta (Set (map look (hlFitchCitedLines r)));
    HL_FEqE _ _ -> sup_seta (Set (map look (hlFitchCitedLines r)));
    HL_FLEM -> sup_seta (Set (map look (hlFitchCitedLines r)));
    HL_FPropTaut _ -> sup_seta (Set (map look (hlFitchCitedLines r)));
    HL_FIffI _ _ -> sup_seta (Set (map look (hlFitchCitedLines r)));
    HL_FIffE _ _ -> sup_seta (Set (map look (hlFitchCitedLines r)));
    HL_FQN _ -> sup_seta (Set (map look (hlFitchCitedLines r)));
    HL_FReit _ -> sup_seta (Set (map look (hlFitchCitedLines r)));
  });

hlDependencyLookup :: [(Int, Set Int)] -> Int -> Set Int;
hlDependencyLookup [] n = bot_set;
hlDependencyLookup ((m, g) : env) n =
  (if equal_int m n then g else hlDependencyLookup env n);

hlToLemmonRule :: Hl_fitch_rule -> Hl_justification;
hlToLemmonRule HL_FPremise = HL_Assumption;
hlToLemmonRule HL_FAssume = HL_Assumption;
hlToLemmonRule (HL_FMP m n) = HL_MP m n;
hlToLemmonRule (HL_FMT m n) = HL_MT m n;
hlToLemmonRule (HL_FDN m) = HL_DN m;
hlToLemmonRule (HL_FCP (a, c)) = HL_CP a c;
hlToLemmonRule (HL_FAndI m n) = HL_AndIntro m n;
hlToLemmonRule (HL_FAndE m) = HL_AndElim m;
hlToLemmonRule (HL_FOrI m) = HL_OrIntro m;
hlToLemmonRule (HL_FOrE d (a1, c1) (a2, c2)) = HL_OrElim d a1 c1 a2 c2;
hlToLemmonRule (HL_FRAA (a, c)) = HL_RAA a c;
hlToLemmonRule (HL_FForallE m) = HL_ForallElim m;
hlToLemmonRule (HL_FForallI m) = HL_ForallIntro m;
hlToLemmonRule (HL_FExistsI m) = HL_ExistsIntro m;
hlToLemmonRule (HL_FExistsE m (a, c)) = HL_ExistsElim m a c;
hlToLemmonRule HL_FEqI = HL_EqIntro;
hlToLemmonRule (HL_FEqE m n) = HL_EqElim m n;
hlToLemmonRule HL_FLEM = HL_LEM;
hlToLemmonRule (HL_FPropTaut ms) = HL_PropTaut ms;
hlToLemmonRule (HL_FIffI m n) = HL_IffIntro m n;
hlToLemmonRule (HL_FIffE m n) = HL_IffElim m n;
hlToLemmonRule (HL_FQN m) = HL_QN m;
hlToLemmonRule (HL_FReit m) = HL_PropTaut [m];

hlFitchToLemmonFrom ::
  [(Int, Set Int)] ->
    [(Int, (Hl_formula, Hl_fitch_rule))] -> ([(Int, Set Int)], [Hl_line]);
hlFitchToLemmonFrom env [] = (env, []);
hlFitchToLemmonFrom env ((n, (p, r)) : ls) =
  let {
    g = hlFitchDependenciesOf (hlDependencyLookup env) r n;
    line = HL_ProofLine n p (hlToLemmonRule r) g;
  } in (case hlFitchToLemmonFrom ((n, g) : env) ls of {
         (enva, tail) -> (enva, line : tail);
       });

hlFlattenFitch :: [Hl_fitch_item] -> [(Int, (Hl_formula, Hl_fitch_rule))];
hlFlattenFitch [] = [];
hlFlattenFitch (i : is) = hlFlattenFitchItem i ++ hlFlattenFitch is;

hlFlattenFitchItem :: Hl_fitch_item -> [(Int, (Hl_formula, Hl_fitch_rule))];
hlFlattenFitchItem (HL_FLine n p r) = [(n, (p, r))];
hlFlattenFitchItem (HL_FSub (HL_Subproof a p body)) =
  (a, (p, HL_FAssume)) : hlFlattenFitch body;

hlFitchToLemmon :: [Hl_fitch_item] -> [Hl_line];
hlFitchToLemmon f = snd (hlFitchToLemmonFrom [] (hlFlattenFitch f));

hlFitchPremises :: [Hl_fitch_item] -> [Hl_formula];
hlFitchPremises [] = [];
hlFitchPremises (HL_FLine n p r : rest) =
  (if equal_hl_fitch_rule r HL_FPremise then p : hlFitchPremises rest
    else hlFitchPremises rest);
hlFitchPremises (HL_FSub s : rest) = hlFitchPremises rest;

hlFitchPremisesFirst :: [Hl_fitch_item] -> Bool;
hlFitchPremisesFirst f =
  all (\ (_, (_, r)) -> not (equal_hl_fitch_rule r HL_FPremise))
    (dropWhile (\ (_, (_, r)) -> equal_hl_fitch_rule r HL_FPremise)
      (hlFlattenFitch f));

hlFitchCitedSubs :: Hl_fitch_rule -> [(Int, Int)];
hlFitchCitedSubs (HL_FCP s) = [s];
hlFitchCitedSubs (HL_FRAA s) = [s];
hlFitchCitedSubs (HL_FOrE uu s1 s2) = [s1, s2];
hlFitchCitedSubs (HL_FExistsE uv s) = [s];
hlFitchCitedSubs HL_FPremise = [];
hlFitchCitedSubs HL_FAssume = [];
hlFitchCitedSubs (HL_FMP v va) = [];
hlFitchCitedSubs (HL_FMT v va) = [];
hlFitchCitedSubs (HL_FDN v) = [];
hlFitchCitedSubs (HL_FAndI v va) = [];
hlFitchCitedSubs (HL_FAndE v) = [];
hlFitchCitedSubs (HL_FOrI v) = [];
hlFitchCitedSubs (HL_FForallE v) = [];
hlFitchCitedSubs (HL_FForallI v) = [];
hlFitchCitedSubs (HL_FExistsI v) = [];
hlFitchCitedSubs HL_FEqI = [];
hlFitchCitedSubs (HL_FEqE v va) = [];
hlFitchCitedSubs HL_FLEM = [];
hlFitchCitedSubs (HL_FPropTaut v) = [];
hlFitchCitedSubs (HL_FIffI v va) = [];
hlFitchCitedSubs (HL_FIffE v va) = [];
hlFitchCitedSubs (HL_FQN v) = [];
hlFitchCitedSubs (HL_FReit v) = [];

hlConcludesAtTop :: [Hl_fitch_item] -> Bool;
hlConcludesAtTop f = null f || (case last f of {
                                 HL_FLine _ _ _ -> True;
                                 HL_FSub _ -> False;
                               });

hlFitchLineNumbers :: [Hl_fitch_item] -> [Int];
hlFitchLineNumbers [] = [];
hlFitchLineNumbers (i : is) = hlFitchItemLineNumbers i ++ hlFitchLineNumbers is;

hlFitchItemLineNumbers :: Hl_fitch_item -> [Int];
hlFitchItemLineNumbers (HL_FLine n p r) = [n];
hlFitchItemLineNumbers (HL_FSub (HL_Subproof a p body)) =
  a : hlFitchLineNumbers body;

hlSubLastLine :: Hl_subproof -> Int;
hlSubLastLine (HL_Subproof a p body) =
  (if null (hlFitchLineNumbers body) then a
    else last (hlFitchLineNumbers body));

hlFitchNestingFrom ::
  Nat -> Set Int -> Set (Int, Int) -> [Hl_fitch_item] -> Bool;
hlFitchNestingFrom depth visible boxes [] = True;
hlFitchNestingFrom depth visible boxes (HL_FLine n p r : rest) =
  not (equal_hl_fitch_rule r HL_FAssume) &&
    (if equal_hl_fitch_rule r HL_FPremise then equal_nat depth zero_nat
      else True) &&
      less_eq_set (Set (hlFitchCitedLines r)) visible &&
        less_eq_set (Set (hlFitchCitedSubs r)) boxes &&
          hlFitchNestingFrom depth (insert n visible) boxes rest;
hlFitchNestingFrom depth visible boxes (HL_FSub (HL_Subproof a p body) : rest) =
  hlConcludesAtTop body &&
    hlFitchNestingFrom (suc depth) (insert a visible) bot_set body &&
      hlFitchNestingFrom depth visible
        (insert (a, hlSubLastLine (HL_Subproof a p body)) boxes) rest;

hlFitchNestedWellFormed :: [Hl_fitch_item] -> Bool;
hlFitchNestedWellFormed f =
  hlFitchNestingFrom zero_nat bot_set bot_set f &&
    hlFitchPremisesFirst f &&
      all (less_int zero_int) (hlFitchLineNumbers f) &&
        sorted_wrt less_int (hlFitchLineNumbers f) && hlConcludesAtTop f;

hlFitchPremiseClosed :: [Hl_fitch_item] -> Bool;
hlFitchPremiseClosed f =
  superset (hlFitchPremises f) (hlOpenPremises (hlFitchToLemmon f));

hlFitchScopeFrom :: Nat -> Set Int -> [Hl_fitch_item] -> Maybe (Set Int);
hlFitchScopeFrom depth visible [] = Just visible;
hlFitchScopeFrom depth visible (HL_FLine n p r : rest) =
  (if (case r of {
        HL_FPremise -> equal_nat depth zero_nat;
        HL_FAssume -> True;
        HL_FMP _ _ -> True;
        HL_FMT _ _ -> True;
        HL_FDN _ -> True;
        HL_FCP _ -> True;
        HL_FAndI _ _ -> True;
        HL_FAndE _ -> True;
        HL_FOrI _ -> True;
        HL_FOrE _ _ _ -> True;
        HL_FRAA _ -> True;
        HL_FForallE _ -> True;
        HL_FForallI _ -> True;
        HL_FExistsI _ -> True;
        HL_FExistsE _ _ -> True;
        HL_FEqI -> True;
        HL_FEqE _ _ -> True;
        HL_FLEM -> True;
        HL_FPropTaut _ -> True;
        HL_FIffI _ _ -> True;
        HL_FIffE _ _ -> True;
        HL_FQN _ -> True;
        HL_FReit _ -> True;
      }) &&
        less_eq_set (Set (hlFitchCitedLines r)) visible
    then hlFitchScopeFrom depth (insert n visible) rest else Nothing);
hlFitchScopeFrom depth visible (HL_FSub (HL_Subproof a p body) : rest) =
  (case hlFitchScopeFrom (suc depth) (insert a visible) body of {
    Nothing -> Nothing;
    Just _ ->
      hlFitchScopeFrom depth
        (insert a (insert (hlSubLastLine (HL_Subproof a p body)) visible)) rest;
  });

hlFitchWellFormed :: [Hl_fitch_item] -> Bool;
hlFitchWellFormed f = not (is_none (hlFitchScopeFrom zero_nat bot_set f));

hlFitchVerified :: [Hl_fitch_item] -> Bool;
hlFitchVerified f =
  hlFitchWellFormed f &&
    hlConcludesAtTop f &&
      hlFitchNestedWellFormed f &&
        hlFitchPremiseClosed f && hlVerifiedCorrect (hlFitchToLemmon f);

hlFitchCorrect :: [Hl_fitch_item] -> Bool;
hlFitchCorrect f =
  hlFitchVerified f && hlCorrectG (hlScopeSrc f) (hlFitchToLemmon f);

hlViaTree :: [Hl_line] -> Sum Hl_translation_error (Hl_route, [Hl_fitch_item]);
hlViaTree p =
  (case hlToDerivation p of {
    Nothing -> Inl (HL_SourceNotVerified zero_int);
    Just d ->
      let {
        f = hlDerivationToFitch d;
      } in (if hlFitchCorrect f &&
                 superset (hlOpenPremises p) (hlFitchPremises f) &&
                   hlConclusion (hlFitchToLemmon f) == hlConclusion p
             then Inr (HL_ViaTreeRoute, f) else Inl HL_TargetNotVerified);
  });

premiseOrderError :: [Pline] -> Maybe Translation_error;
premiseOrderError p =
  let {
    rest = dropWhile (isPremiseLine p) p;
  } in (case filter (isPremiseLine p) rest of {
         [] -> Nothing;
         l : _ -> (case rest of {
                    [] -> Nothing;
                    e : _ -> Just (PremiseLate (lineNumber l) (lineNumber e));
                  });
       });

lemmonToFitchDirect :: [Pline] -> Sum Translation_error [Fitch_item];
lemmonToFitchDirect p =
  (if not (lemmonCorrect p) then Inl (NotCorrect zero_nat)
    else (case boxOrderError p of {
           Nothing ->
             (case boxHeadError p of {
               Nothing ->
                 (case nestingError p of {
                   Nothing ->
                     (case premiseError p of {
                       Nothing ->
                         (case scopeError p of {
                           Nothing ->
                             (case subScopeError p of {
                               Nothing ->
                                 (case premiseOrderError p of {
                                   Nothing -> Inr (buildItems (boxesOf p) p);
                                   Just a -> Inl a;
                                 });
                               Just a -> Inl a;
                             });
                           Just a -> Inl a;
                         });
                       Just a -> Inl a;
                     });
                   Just a -> Inl a;
                 });
               Just a -> Inl a;
             });
           Just a -> Inl a;
         }));

lemmonToFitch :: [Pline] -> Sum Translation_error (Route, [Fitch_item]);
lemmonToFitch p = (case lemmonToFitchDirect p of {
                    Inl _ -> viaTree p;
                    Inr f -> Inr (Direct, f);
                  });

fitchConclusion :: [Fitch_item] -> Maybe Fm;
fitchConclusion f =
  (if null (flatten f) then Nothing else Just (flFm (last (flatten f))));

fitchWellFormed :: [Fitch_item] -> Maybe String;
fitchWellFormed f =
  (if not (sorted_wrt less_nat (map flNum (flatten f)))
    then Just "line numbers are not strictly increasing"
    else (if not (all noAssumeLinesItem f)
           then Just "an assumption occurs otherwise than as the head of a subproof"
           else (if not (all (\ fl ->
                               (if equal_fitch_rule (flRule fl) FPremise
                                 then null (flScope fl) else True))
                          (flatten f))
                  then Just "a premise occurs inside a subproof"
                  else (if not (premisesFirst f)
                         then Just "a premise occurs after a line that is not a premise"
                         else (if not (all lastIsLineItem f)
                                then Just "a subproof does not end in a line"
                                else (if not (concludesAtTop f)
                                       then Just
      "the proof does not end at the outermost level"
                                       else (if not
          (all (citationOK f) (flatten f))
      then Just "a line cites something not in its scope" else Nothing)))))));

fresh_for_fms :: [Fm] -> String;
fresh_for_fms ps = fresh_for (concatMap names ps);

hlJustificationAt :: [Hl_line] -> Int -> Maybe Hl_justification;
hlJustificationAt p n = map_option hlJustification (hlLookupLine p n);

hlFreeForUnder :: Set String -> String -> Hl_term -> Hl_formula -> Bool;
hlFreeForUnder b x t (HL_Predicate p ts) =
  all (\ a ->
        (case a of {
          HL_Var y ->
            not (y == x) || equal_set (inf_set (hlVariablesInTerm t) b) bot_set;
          HL_Const _ -> True;
        }))
    ts;
hlFreeForUnder b x t (HL_Boolean uu) = True;
hlFreeForUnder b x t (HL_Not p) = hlFreeForUnder b x t p;
hlFreeForUnder b x t (HL_And p q) =
  hlFreeForUnder b x t p && hlFreeForUnder b x t q;
hlFreeForUnder b x t (HL_Or p q) =
  hlFreeForUnder b x t p && hlFreeForUnder b x t q;
hlFreeForUnder b x t (HL_Implies p q) =
  hlFreeForUnder b x t p && hlFreeForUnder b x t q;
hlFreeForUnder b x t (HL_Iff p q) =
  hlFreeForUnder b x t p && hlFreeForUnder b x t q;
hlFreeForUnder b x t (HL_ForAll y p) = hlFreeForUnder (insert y b) x t p;
hlFreeForUnder b x t (HL_Exists y p) = hlFreeForUnder (insert y b) x t p;

hlFreeFor :: String -> Hl_term -> Hl_formula -> Bool;
hlFreeFor x t p = hlFreeForUnder bot_set x t p;

hlIsAssumptionLine :: [Hl_line] -> Int -> Bool;
hlIsAssumptionLine p n = hlJustificationAt p n == Just HL_Assumption;

hlStructureError :: [Hl_line] -> Hl_line -> Maybe Hl_check_error;
hlStructureError p l =
  let {
    n = hlLineNumber l;
    dupes = size_lista (filter (\ k -> equal_int (hlLineNumber k) n) p);
    late =
      filter (\ m -> not (less_int m n)) (hlCitedLines (hlJustification l));
  } in (if less_nat one_nat dupes
         then Just (HL_DuplicateLine n (int_of_nat dupes))
         else (if not (null late) then Just (HL_LateCitation n late)
                else Nothing));

hlAnyCitationMissing :: [Hl_line] -> Hl_justification -> Bool;
hlAnyCitationMissing p j =
  any (\ m -> is_none (hlLookupLine p m)) (hlCitedLines j);

hlRejectionReason ::
  [Hl_line] -> Hl_line -> Hl_justification -> Int -> Hl_check_error;
hlRejectionReason p l (HL_MP m k) n =
  (case hlLookupLine p m of {
    Nothing -> HL_RuleRejected (HL_MP m k) n;
    Just lm ->
      (case hlFormula lm of {
        HL_Predicate _ _ -> HL_MPFirstNotConditional n;
        HL_Boolean _ -> HL_MPFirstNotConditional n;
        HL_Not _ -> HL_MPFirstNotConditional n;
        HL_And _ _ -> HL_MPFirstNotConditional n;
        HL_Or _ _ -> HL_MPFirstNotConditional n;
        HL_Implies pa q ->
          (case hlLookupLine p k of {
            Nothing -> HL_RuleRejected (HL_MP m k) n;
            Just lk ->
              (if not (equal_hl_formula (hlFormula lk) pa)
                then HL_MPSecondNotAntecedent n
                else (if not (equal_hl_formula (hlFormula l) q)
                       then HL_MPNotConsequent q
                       else HL_RuleRejected (HL_MP m k) n));
          });
        HL_Iff _ _ -> HL_MPFirstNotConditional n;
        HL_ForAll _ _ -> HL_MPFirstNotConditional n;
        HL_Exists _ _ -> HL_MPFirstNotConditional n;
      });
  });
hlRejectionReason p l (HL_AndElim m) n =
  (case hlLookupLine p m of {
    Nothing -> HL_RuleRejected (HL_AndElim m) n;
    Just lm -> (case hlFormula lm of {
                 HL_Predicate _ _ -> HL_AndElimNotConjunction m;
                 HL_Boolean _ -> HL_AndElimNotConjunction m;
                 HL_Not _ -> HL_AndElimNotConjunction m;
                 HL_And _ _ -> HL_RuleRejected (HL_AndElim m) n;
                 HL_Or _ _ -> HL_AndElimNotConjunction m;
                 HL_Implies _ _ -> HL_AndElimNotConjunction m;
                 HL_Iff _ _ -> HL_AndElimNotConjunction m;
                 HL_ForAll _ _ -> HL_AndElimNotConjunction m;
                 HL_Exists _ _ -> HL_AndElimNotConjunction m;
               });
  });
hlRejectionReason p l (HL_OrIntro m) n =
  (case hlFormula l of {
    HL_Predicate _ _ -> HL_RuleRejected (HL_OrIntro m) n;
    HL_Boolean _ -> HL_RuleRejected (HL_OrIntro m) n;
    HL_Not _ -> HL_RuleRejected (HL_OrIntro m) n;
    HL_And _ _ -> HL_RuleRejected (HL_OrIntro m) n;
    HL_Or _ _ -> HL_OrIntroNotDisjunct;
    HL_Implies _ _ -> HL_RuleRejected (HL_OrIntro m) n;
    HL_Iff _ _ -> HL_RuleRejected (HL_OrIntro m) n;
    HL_ForAll _ _ -> HL_RuleRejected (HL_OrIntro m) n;
    HL_Exists _ _ -> HL_RuleRejected (HL_OrIntro m) n;
  });
hlRejectionReason p l (HL_DN m) n = HL_DNShape n;
hlRejectionReason p l (HL_ForallIntro m) n =
  (case hlLookupLine p m of {
    Nothing -> HL_RuleRejected (HL_ForallIntro m) n;
    Just lm ->
      (case hlCollectForalls (hlFormula l) of {
        (xs, core) ->
          (if null xs then HL_RuleRejected (HL_ForallIntro m) n
            else (case hlInferWitnessConstsK xs core (size_lista xs)
                         (hlFormula lm)
                   of {
                   Nothing -> HL_ForallIntroNotInstance m;
                   Just cs ->
                     let {
                       pairs = filter (\ xc -> not (snd xc == "")) (zip xs cs);
                     } in (if not (hlAbstractMany pairs (hlFormula lm) ==
                                    Just core)
                            then HL_ForallIntroAbstraction
                            else HL_RuleRejected (HL_ForallIntro m) n);
                 }));
      });
  });
hlRejectionReason p l (HL_ForallElim m) n =
  (case hlLookupLine p m of {
    Nothing -> HL_RuleRejected (HL_ForallElim m) n;
    Just lm ->
      (case hlCollectForalls (hlFormula lm) of {
        (sv, sc) ->
          (case hlCollectForalls (hlFormula l) of {
            (dv, dc) ->
              (case hlEliminationCount sv dv of {
                Nothing -> HL_RuleRejected (HL_ForallElim m) n;
                Just k -> (case hlInferWitnessConstsK sv sc k dc of {
                            Nothing -> HL_ForallElimNoConstants;
                            Just _ -> HL_RuleRejected (HL_ForallElim m) n;
                          });
              });
          });
      });
  });
hlRejectionReason p l (HL_ExistsIntro m) n =
  (case hlLookupLine p m of {
    Nothing -> HL_RuleRejected (HL_ExistsIntro m) n;
    Just _ ->
      (case hlCollectExists (hlFormula l) of {
        (xs, _) ->
          (if null xs then HL_RuleRejected (HL_ExistsIntro m) n
            else HL_ExistsIntroNotWitness);
      });
  });
hlRejectionReason p l (HL_ExistsElim m a c) n =
  (case (hlLookupLine p m, (hlLookupLine p a, hlLookupLine p c)) of {
    (Nothing, _) -> HL_RuleRejected (HL_ExistsElim m a c) n;
    (Just _, (Nothing, _)) -> HL_RuleRejected (HL_ExistsElim m a c) n;
    (Just _, (Just _, Nothing)) -> HL_RuleRejected (HL_ExistsElim m a c) n;
    (Just lm, (Just la, Just lc)) ->
      (case hlCollectExists (hlFormula lm) of {
        (sv, _) ->
          (if null sv then HL_RuleRejected (HL_ExistsElim m a c) n
            else (if not (equal_hl_justification (hlJustification la)
                           HL_Assumption)
                   then HL_ExistsElimNotAssumption a
                   else (if not (equal_hl_formula (hlFormula l) (hlFormula lc))
                          then HL_ExistsElimNotRepeated n c
                          else HL_RuleRejected (HL_ExistsElim m a c) n)));
      });
  });
hlRejectionReason p l (HL_RAA m k) n =
  (case (hlLookupLine p m, hlLookupLine p k) of {
    (Nothing, _) -> HL_RuleRejected (HL_RAA m k) n;
    (Just _, Nothing) -> HL_RuleRejected (HL_RAA m k) n;
    (Just lm, Just lk) ->
      let {
        expected = remove (hlLineNumber lm) (hlReferences lk);
      } in HL_RAAFailed n m k
             (equal_hl_justification (hlJustification lm) HL_Assumption)
             (case hlFormula lk of {
               HL_Predicate _ _ -> False;
               HL_Boolean _ -> False;
               HL_Not _ -> False;
               HL_And (HL_Predicate _ _) (HL_Predicate _ _) -> False;
               HL_And (HL_Predicate _ _) (HL_Boolean _) -> False;
               HL_And (HL_Predicate literal list) (HL_Not a) ->
                 equal_hl_formula (HL_Predicate literal list) a;
               HL_And (HL_Predicate _ _) (HL_And _ _) -> False;
               HL_And (HL_Predicate _ _) (HL_Or _ _) -> False;
               HL_And (HL_Predicate _ _) (HL_Implies _ _) -> False;
               HL_And (HL_Predicate _ _) (HL_Iff _ _) -> False;
               HL_And (HL_Predicate _ _) (HL_ForAll _ _) -> False;
               HL_And (HL_Predicate _ _) (HL_Exists _ _) -> False;
               HL_And (HL_Boolean _) (HL_Predicate _ _) -> False;
               HL_And (HL_Boolean _) (HL_Boolean _) -> False;
               HL_And (HL_Boolean bool) (HL_Not a) ->
                 equal_hl_formula (HL_Boolean bool) a;
               HL_And (HL_Boolean _) (HL_And _ _) -> False;
               HL_And (HL_Boolean _) (HL_Or _ _) -> False;
               HL_And (HL_Boolean _) (HL_Implies _ _) -> False;
               HL_And (HL_Boolean _) (HL_Iff _ _) -> False;
               HL_And (HL_Boolean _) (HL_ForAll _ _) -> False;
               HL_And (HL_Boolean _) (HL_Exists _ _) -> False;
               HL_And (HL_Not hl_formula) (HL_Predicate literal list) ->
                 equal_hl_formula hl_formula (HL_Predicate literal list);
               HL_And (HL_Not hl_formula) (HL_Boolean bool) ->
                 equal_hl_formula hl_formula (HL_Boolean bool);
               HL_And (HL_Not hl_formula) (HL_Not a) ->
                 equal_hl_formula (HL_Not hl_formula) a;
               HL_And (HL_Not hl_formula) (HL_And hl_formula1 hl_formula2) ->
                 equal_hl_formula hl_formula (HL_And hl_formula1 hl_formula2);
               HL_And (HL_Not hl_formula) (HL_Or hl_formula1 hl_formula2) ->
                 equal_hl_formula hl_formula (HL_Or hl_formula1 hl_formula2);
               HL_And (HL_Not hl_formula) (HL_Implies hl_formula1 hl_formula2)
                 -> equal_hl_formula hl_formula
                      (HL_Implies hl_formula1 hl_formula2);
               HL_And (HL_Not hl_formula) (HL_Iff hl_formula1 hl_formula2) ->
                 equal_hl_formula hl_formula (HL_Iff hl_formula1 hl_formula2);
               HL_And (HL_Not hl_formula) (HL_ForAll literal hl_formulaa) ->
                 equal_hl_formula hl_formula (HL_ForAll literal hl_formulaa);
               HL_And (HL_Not hl_formula) (HL_Exists literal hl_formulaa) ->
                 equal_hl_formula hl_formula (HL_Exists literal hl_formulaa);
               HL_And (HL_And _ _) (HL_Predicate _ _) -> False;
               HL_And (HL_And _ _) (HL_Boolean _) -> False;
               HL_And (HL_And hl_formula1 hl_formula2) (HL_Not a) ->
                 equal_hl_formula (HL_And hl_formula1 hl_formula2) a;
               HL_And (HL_And _ _) (HL_And _ _) -> False;
               HL_And (HL_And _ _) (HL_Or _ _) -> False;
               HL_And (HL_And _ _) (HL_Implies _ _) -> False;
               HL_And (HL_And _ _) (HL_Iff _ _) -> False;
               HL_And (HL_And _ _) (HL_ForAll _ _) -> False;
               HL_And (HL_And _ _) (HL_Exists _ _) -> False;
               HL_And (HL_Or _ _) (HL_Predicate _ _) -> False;
               HL_And (HL_Or _ _) (HL_Boolean _) -> False;
               HL_And (HL_Or hl_formula1 hl_formula2) (HL_Not a) ->
                 equal_hl_formula (HL_Or hl_formula1 hl_formula2) a;
               HL_And (HL_Or _ _) (HL_And _ _) -> False;
               HL_And (HL_Or _ _) (HL_Or _ _) -> False;
               HL_And (HL_Or _ _) (HL_Implies _ _) -> False;
               HL_And (HL_Or _ _) (HL_Iff _ _) -> False;
               HL_And (HL_Or _ _) (HL_ForAll _ _) -> False;
               HL_And (HL_Or _ _) (HL_Exists _ _) -> False;
               HL_And (HL_Implies _ _) (HL_Predicate _ _) -> False;
               HL_And (HL_Implies _ _) (HL_Boolean _) -> False;
               HL_And (HL_Implies hl_formula1 hl_formula2) (HL_Not a) ->
                 equal_hl_formula (HL_Implies hl_formula1 hl_formula2) a;
               HL_And (HL_Implies _ _) (HL_And _ _) -> False;
               HL_And (HL_Implies _ _) (HL_Or _ _) -> False;
               HL_And (HL_Implies _ _) (HL_Implies _ _) -> False;
               HL_And (HL_Implies _ _) (HL_Iff _ _) -> False;
               HL_And (HL_Implies _ _) (HL_ForAll _ _) -> False;
               HL_And (HL_Implies _ _) (HL_Exists _ _) -> False;
               HL_And (HL_Iff _ _) (HL_Predicate _ _) -> False;
               HL_And (HL_Iff _ _) (HL_Boolean _) -> False;
               HL_And (HL_Iff hl_formula1 hl_formula2) (HL_Not a) ->
                 equal_hl_formula (HL_Iff hl_formula1 hl_formula2) a;
               HL_And (HL_Iff _ _) (HL_And _ _) -> False;
               HL_And (HL_Iff _ _) (HL_Or _ _) -> False;
               HL_And (HL_Iff _ _) (HL_Implies _ _) -> False;
               HL_And (HL_Iff _ _) (HL_Iff _ _) -> False;
               HL_And (HL_Iff _ _) (HL_ForAll _ _) -> False;
               HL_And (HL_Iff _ _) (HL_Exists _ _) -> False;
               HL_And (HL_ForAll _ _) (HL_Predicate _ _) -> False;
               HL_And (HL_ForAll _ _) (HL_Boolean _) -> False;
               HL_And (HL_ForAll literal hl_formula) (HL_Not a) ->
                 equal_hl_formula (HL_ForAll literal hl_formula) a;
               HL_And (HL_ForAll _ _) (HL_And _ _) -> False;
               HL_And (HL_ForAll _ _) (HL_Or _ _) -> False;
               HL_And (HL_ForAll _ _) (HL_Implies _ _) -> False;
               HL_And (HL_ForAll _ _) (HL_Iff _ _) -> False;
               HL_And (HL_ForAll _ _) (HL_ForAll _ _) -> False;
               HL_And (HL_ForAll _ _) (HL_Exists _ _) -> False;
               HL_And (HL_Exists _ _) (HL_Predicate _ _) -> False;
               HL_And (HL_Exists _ _) (HL_Boolean _) -> False;
               HL_And (HL_Exists literal hl_formula) (HL_Not a) ->
                 equal_hl_formula (HL_Exists literal hl_formula) a;
               HL_And (HL_Exists _ _) (HL_And _ _) -> False;
               HL_And (HL_Exists _ _) (HL_Or _ _) -> False;
               HL_And (HL_Exists _ _) (HL_Implies _ _) -> False;
               HL_And (HL_Exists _ _) (HL_Iff _ _) -> False;
               HL_And (HL_Exists _ _) (HL_ForAll _ _) -> False;
               HL_And (HL_Exists _ _) (HL_Exists _ _) -> False;
               HL_Or _ _ -> False;
               HL_Implies _ _ -> False;
               HL_Iff _ _ -> False;
               HL_ForAll _ _ -> False;
               HL_Exists _ _ -> False;
             })
             (equal_hl_formula (hlFormula l) (HL_Not (hlFormula lm)))
             (sorted_list_of_set expected)
             (sorted_list_of_set (hlReferences l));
  });
hlRejectionReason p l (HL_OrElim d a1 c1 a2 c2) n =
  (case (hlLookupLine p a1, hlLookupLine p a2) of {
    (Nothing, _) -> HL_RuleRejected (HL_OrElim d a1 c1 a2 c2) n;
    (Just _, Nothing) -> HL_RuleRejected (HL_OrElim d a1 c1 a2 c2) n;
    (Just la1, Just la2) ->
      HL_OrElimFailed n d a1 a2
        (equal_hl_justification (hlJustification la1) HL_Assumption)
        (equal_hl_justification (hlJustification la2) HL_Assumption);
  });
hlRejectionReason p l (HL_AndIntro m k) n =
  (case (hlLookupLine p m, hlLookupLine p k) of {
    (Nothing, _) -> HL_RuleRejected (HL_AndIntro m k) n;
    (Just _, Nothing) -> HL_RuleRejected (HL_AndIntro m k) n;
    (Just lm, Just lk) ->
      (if not (equal_hl_formula (hlFormula l)
                (HL_And (hlFormula lm) (hlFormula lk))) &&
            not (equal_hl_formula (hlFormula l)
                  (HL_And (hlFormula lk) (hlFormula lm)))
        then HL_AndIntroMismatch n (hlFormula lm) (hlFormula lk) (hlFormula l)
        else HL_RuleRejected (HL_AndIntro m k) n);
  });
hlRejectionReason p l (HL_EqElim m k) n =
  (case hlLookupLine p k of {
    Nothing -> HL_RuleRejected (HL_EqElim m k) n;
    Just lk ->
      (case hlFormula lk of {
        HL_Predicate _ [] -> HL_EqElimNotEquality;
        HL_Predicate _ (HL_Var _ : _) -> HL_EqElimNotEquality;
        HL_Predicate _ [HL_Const _] -> HL_EqElimNotEquality;
        HL_Predicate _ (HL_Const _ : HL_Var _ : _) -> HL_EqElimNotEquality;
        HL_Predicate e [HL_Const _, HL_Const _] ->
          (if e == "=" then HL_RuleRejected (HL_EqElim m k) n
            else HL_EqElimNotEquality);
        HL_Predicate _ (HL_Const _ : HL_Const _ : _ : _) ->
          HL_EqElimNotEquality;
        HL_Boolean _ -> HL_EqElimNotEquality;
        HL_Not _ -> HL_EqElimNotEquality;
        HL_And _ _ -> HL_EqElimNotEquality;
        HL_Or _ _ -> HL_EqElimNotEquality;
        HL_Implies _ _ -> HL_EqElimNotEquality;
        HL_Iff _ _ -> HL_EqElimNotEquality;
        HL_ForAll _ _ -> HL_EqElimNotEquality;
        HL_Exists _ _ -> HL_EqElimNotEquality;
      });
  });
hlRejectionReason p l (HL_MT m k) n =
  (case (hlLookupLine p m, hlLookupLine p k) of {
    (Nothing, _) -> HL_RuleRejected (HL_MT m k) n;
    (Just _, Nothing) -> HL_RuleRejected (HL_MT m k) n;
    (Just lm, Just lk) ->
      HL_MTFailed n m k (hlIsMT (hlFormula lm) (hlFormula lk) (hlFormula l))
        (hlIsMT (hlFormula lk) (hlFormula lm) (hlFormula l))
        (equal_set (hlReferences l)
          (sup_set (hlReferences lm) (hlReferences lk)));
  });
hlRejectionReason p l HL_Assumption n = HL_RuleRejected HL_Assumption n;
hlRejectionReason p l (HL_CP v va) n = HL_RuleRejected (HL_CP v va) n;
hlRejectionReason p l HL_EqIntro n = HL_RuleRejected HL_EqIntro n;
hlRejectionReason p l HL_LEM n = HL_RuleRejected HL_LEM n;
hlRejectionReason p l (HL_PropTaut v) n = HL_RuleRejected (HL_PropTaut v) n;
hlRejectionReason p l (HL_IffIntro v va) n =
  HL_RuleRejected (HL_IffIntro v va) n;
hlRejectionReason p l (HL_IffElim v va) n = HL_RuleRejected (HL_IffElim v va) n;
hlRejectionReason p l (HL_QN v) n = HL_RuleRejected (HL_QN v) n;

hlRuleError :: [Hl_line] -> Hl_line -> Maybe Hl_check_error;
hlRuleError p l =
  (if hlRuleOK p l then Nothing
    else Just (let {
                 n = hlLineNumber l;
                 j = hlJustification l;
               } in (if equal_hl_justification j HL_Assumption
                      then HL_InvalidAssumption n
                      else (if hlAnyCitationMissing p j then HL_MissingCited j n
                             else hlRejectionReason p l j n))));

hlLineError :: [Hl_line] -> Hl_line -> Maybe Hl_check_error;
hlLineError p l = (case hlStructureError p l of {
                    Nothing -> hlRuleError p l;
                    Just a -> Just a;
                  });

showTranslation :: Sum Translation_error (Route, [Fitch_item]) -> [String];
showTranslation r = (case r of {
                      Inl e -> ["no translation: " ++ showError e];
                      Inr (rt, f) -> showRoute rt : showFitch f;
                    });

dependents :: [Pline] -> Nat -> [Nat];
dependents p a =
  map_filter
    (\ x -> (if member a (references x) then Just (lineNumber x) else Nothing))
    p;

ruleMatches :: Justa -> Fitch_rule -> Bool;
ruleMatches j r =
  (if equal_just j Assumption
    then equal_fitch_rule r FPremise || equal_fitch_rule r FAssume
    else equal_fitch_rule r (toFitchRule j));

lineMatches :: Fline -> Pline -> Bool;
lineMatches fl l =
  equal_nat (flNum fl) (lineNumber l) &&
    equal_fm (flFm fl) (formula l) && ruleMatches (justification l) (flRule fl);

fitchImage :: [Fitch_item] -> [Pline] -> Bool;
fitchImage f p =
  all (\ l -> any (\ fl -> lineMatches fl l) (flatten f)) p &&
    all (\ fl -> any (lineMatches fl) p) (flatten f);

hlBoxPath :: [Hl_line] -> Int -> [Int];
hlBoxPath p m =
  sort_key (\ x -> x)
    (map_filter
      (\ x ->
        (if less_eq_int (fst x) m && less_eq_int m (snd x) then Just (fst x)
          else Nothing))
      (hlBoxesOf p));

hlItemLastLine :: Hl_fitch_item -> Int;
hlItemLastLine (HL_FLine n p r) = n;
hlItemLastLine (HL_FSub s) = hlSubLastLine s;

hlProofReport :: [Hl_line] -> [(Int, Maybe Hl_check_error)];
hlProofReport p = map (\ l -> (hlLineNumber l, hlLineError p l)) p;

hlIsPrefix :: forall a. (Eq a) => [a] -> [a] -> Bool;
hlIsPrefix [] ys = True;
hlIsPrefix (x : xs) [] = False;
hlIsPrefix (x : xs) (y : ys) = x == y && hlIsPrefix xs ys;

permuteProof :: (Nat -> Nat) -> [Pline] -> [Pline];
permuteProof r p = sort_key lineNumber (map (relabel r) p);

hlOptionAll :: forall a. (a -> Maybe Bool) -> [a] -> Maybe Bool;
hlOptionAll f [] = Just True;
hlOptionAll f (x : xs) = (case f x of {
                           Nothing -> Nothing;
                           Just True -> hlOptionAll f xs;
                           Just False -> Just False;
                         });

hlOptionAny :: forall a. (a -> Maybe Bool) -> [a] -> Maybe Bool;
hlOptionAny f [] = Just False;
hlOptionAny f (x : xs) = (case f x of {
                           Nothing -> Nothing;
                           Just True -> Just True;
                           Just False -> hlOptionAny f xs;
                         });

noDuplication :: [Fitch_item] -> [Pline] -> Bool;
noDuplication f p =
  fitchImage f p && equal_nat (size_lista (flatten f)) (size_lista p);

sourceCovered :: [Fitch_item] -> [Pline] -> Bool;
sourceCovered f p = all (\ l -> any (\ fl -> lineMatches fl l) (flatten f)) p;

hlFinitePredicates :: forall a. Hl_finite_model a -> [((String, Nat), [[a]])];
hlFinitePredicates (HL_FiniteModel x1 x2 x3) = x3;

hlFiniteDomain :: forall a. Hl_finite_model a -> [a];
hlFiniteDomain (HL_FiniteModel x1 x2 x3) = x1;

hlFiniteConstants :: forall a. Hl_finite_model a -> [(String, a)];
hlFiniteConstants (HL_FiniteModel x1 x2 x3) = x2;

hlFiniteEvalTerm ::
  forall a. Hl_finite_model a -> [(String, a)] -> Hl_term -> Maybe a;
hlFiniteEvalTerm m assignment (HL_Var x) = map_of assignment x;
hlFiniteEvalTerm m assignment (HL_Const a) = map_of (hlFiniteConstants m) a;

hlFiniteEval ::
  forall a.
    (Eq a) => Hl_finite_model a -> [(String, a)] -> Hl_formula -> Maybe Bool;
hlFiniteEval m assignment (HL_Boolean b) = Just b;
hlFiniteEval m assignment (HL_Predicate p ts) =
  (case hlSequenceOptions (map (hlFiniteEvalTerm m assignment) ts) of {
    Nothing -> Nothing;
    Just values -> (case map_of (hlFinitePredicates m) (p, size_lista ts) of {
                     Nothing -> Nothing;
                     Just relation -> Just (membera relation values);
                   });
  });
hlFiniteEval m assignment (HL_Not p) =
  map_option not (hlFiniteEval m assignment p);
hlFiniteEval m assignment (HL_And p q) =
  (case (hlFiniteEval m assignment p, hlFiniteEval m assignment q) of {
    (Nothing, _) -> Nothing;
    (Just _, Nothing) -> Nothing;
    (Just a, Just b) -> Just (a && b);
  });
hlFiniteEval m assignment (HL_Or p q) =
  (case (hlFiniteEval m assignment p, hlFiniteEval m assignment q) of {
    (Nothing, _) -> Nothing;
    (Just _, Nothing) -> Nothing;
    (Just a, Just b) -> Just (a || b);
  });
hlFiniteEval m assignment (HL_Implies p q) =
  (case (hlFiniteEval m assignment p, hlFiniteEval m assignment q) of {
    (Nothing, _) -> Nothing;
    (Just _, Nothing) -> Nothing;
    (Just a, Just b) -> Just (if a then b else True);
  });
hlFiniteEval m assignment (HL_Iff p q) =
  (case (hlFiniteEval m assignment p, hlFiniteEval m assignment q) of {
    (Nothing, _) -> Nothing;
    (Just _, Nothing) -> Nothing;
    (Just a, Just b) -> Just (a == b);
  });
hlFiniteEval m assignment (HL_ForAll x p) =
  (if null (hlFiniteDomain m) then Nothing
    else hlOptionAll (\ d -> hlFiniteEval m ((x, d) : assignment) p)
           (hlFiniteDomain m));
hlFiniteEval m assignment (HL_Exists x p) =
  (if null (hlFiniteDomain m) then Nothing
    else hlOptionAny (\ d -> hlFiniteEval m ((x, d) : assignment) p)
           (hlFiniteDomain m));

hlFirstDifference :: [Int] -> [Int] -> Int;
hlFirstDifference [] ys = zero_int;
hlFirstDifference (x : xs) [] = x;
hlFirstDifference (x : xs) (y : ys) =
  (if equal_int x y then hlFirstDifference xs ys else x);

hlToFitchRule :: Hl_justification -> Hl_fitch_rule;
hlToFitchRule HL_Assumption = HL_FPremise;
hlToFitchRule (HL_MP m n) = HL_FMP m n;
hlToFitchRule (HL_MT m n) = HL_FMT m n;
hlToFitchRule (HL_DN m) = HL_FDN m;
hlToFitchRule (HL_CP a c) = HL_FCP (a, c);
hlToFitchRule (HL_AndIntro m n) = HL_FAndI m n;
hlToFitchRule (HL_AndElim m) = HL_FAndE m;
hlToFitchRule (HL_OrIntro m) = HL_FOrI m;
hlToFitchRule (HL_OrElim d a1 c1 a2 c2) = HL_FOrE d (a1, c1) (a2, c2);
hlToFitchRule (HL_RAA a c) = HL_FRAA (a, c);
hlToFitchRule (HL_ForallElim m) = HL_FForallE m;
hlToFitchRule (HL_ExistsIntro m) = HL_FExistsI m;
hlToFitchRule (HL_ForallIntro m) = HL_FForallI m;
hlToFitchRule (HL_ExistsElim m a c) = HL_FExistsE m (a, c);
hlToFitchRule HL_EqIntro = HL_FEqI;
hlToFitchRule (HL_EqElim m n) = HL_FEqE m n;
hlToFitchRule HL_LEM = HL_FLEM;
hlToFitchRule (HL_PropTaut ms) = HL_FPropTaut ms;
hlToFitchRule (HL_IffIntro m n) = HL_FIffI m n;
hlToFitchRule (HL_IffElim m n) = HL_FIffE m n;
hlToFitchRule (HL_QN m) = HL_FQN m;

hlBadCitations :: [Hl_line] -> [(Int, Int)];
hlBadCitations p =
  concatMap
    (\ l ->
      map_filter
        (\ x ->
          (if not (hlIsPrefix (hlBoxPath p x) (hlBoxPath p (hlLineNumber l)))
            then Just (hlLineNumber l, x) else Nothing))
        (hlFitchCitedLines (hlToFitchRule (hlJustification l))))
    p;

hlScopeError :: [Hl_line] -> Maybe Hl_translation_error;
hlScopeError p =
  (case hlBadCitations p of {
    [] -> Nothing;
    (n, m) : _ ->
      Just (HL_OutOfScope n m
             (hlFirstDifference (hlBoxPath p m) (hlBoxPath p n)));
  });

hlSubproofLevel :: [Hl_line] -> (Int, Int) -> [Int];
hlSubproofLevel p ac = removeAll (fst ac) (hlBoxPath p (fst ac));

hlBadSubproofCitations :: [Hl_line] -> [(Int, (Int, Int))];
hlBadSubproofCitations p =
  concatMap
    (\ l ->
      map_filter
        (\ x ->
          (if not (hlBoxPath p (hlLineNumber l) == hlSubproofLevel p x)
            then Just (hlLineNumber l, (snd x, fst x)) else Nothing))
        (hlDischargePairs (hlJustification l)))
    p;

hlSubproofScopeError :: [Hl_line] -> Maybe Hl_translation_error;
hlSubproofScopeError p = (case hlBadSubproofCitations p of {
                           [] -> Nothing;
                           (n, (c, a)) : _ -> Just (HL_OutOfScope n c a);
                         });

hlIsPremiseLine :: [Hl_line] -> Hl_line -> Bool;
hlIsPremiseLine p l =
  equal_hl_justification (hlJustification l) HL_Assumption &&
    not (membera (hlDischargedAssumptions p) (hlLineNumber l));

hlPremiseOrderError :: [Hl_line] -> Maybe Hl_translation_error;
hlPremiseOrderError p =
  let {
    rest = dropWhile (hlIsPremiseLine p) p;
  } in (case filter (hlIsPremiseLine p) rest of {
         [] -> Nothing;
         l : _ ->
           (case rest of {
             [] -> Nothing;
             e : _ -> Just (HL_PremiseLate (hlLineNumber l) (hlLineNumber e));
           });
       });

hlEigenScopeAssumptions :: [Hl_line] -> Hl_line -> [Int];
hlEigenScopeAssumptions p l =
  let {
    n = hlLineNumber l;
    premises =
      map_filter
        (\ x ->
          (if hlIsPremiseLine p x && less_int (hlLineNumber x) n
            then Just (hlLineNumber x) else Nothing))
        p;
  } in premises ++ (case hlJustification l of {
                     HL_Assumption -> hlBoxPath p n;
                     HL_MP _ _ -> hlBoxPath p n;
                     HL_MT _ _ -> hlBoxPath p n;
                     HL_DN _ -> hlBoxPath p n;
                     HL_CP _ _ -> hlBoxPath p n;
                     HL_AndIntro _ _ -> hlBoxPath p n;
                     HL_AndElim _ -> hlBoxPath p n;
                     HL_OrIntro _ -> hlBoxPath p n;
                     HL_OrElim _ _ _ _ _ -> hlBoxPath p n;
                     HL_RAA _ _ -> hlBoxPath p n;
                     HL_ForallElim _ -> hlBoxPath p n;
                     HL_ExistsIntro _ -> hlBoxPath p n;
                     HL_ForallIntro _ -> hlBoxPath p n;
                     HL_ExistsElim _ a c -> removeAll a (hlBoxPath p c);
                     HL_EqIntro -> hlBoxPath p n;
                     HL_EqElim _ _ -> hlBoxPath p n;
                     HL_LEM -> hlBoxPath p n;
                     HL_PropTaut _ -> hlBoxPath p n;
                     HL_IffIntro _ _ -> hlBoxPath p n;
                     HL_IffElim _ _ -> hlBoxPath p n;
                     HL_QN _ -> hlBoxPath p n;
                   });

hlGeneralizedConstants :: [Hl_line] -> Hl_line -> [String];
hlGeneralizedConstants p (HL_ProofLine n goal (HL_ForallIntro m) g) =
  (case hlLookupLine p m of {
    Nothing -> [];
    Just source ->
      sorted_list_of_set
        (minus_set (hlConstantsInFormula (hlFormula source))
          (hlConstantsInFormula goal));
  });
hlGeneralizedConstants p (HL_ProofLine n goal (HL_ExistsElim m a c) g) =
  (case (hlFormulaAt p m, hlFormulaAt p a) of {
    (Nothing, _) -> [];
    (Just _, Nothing) -> [];
    (Just source, Just assumption) ->
      sorted_list_of_set
        (minus_set (hlConstantsInFormula assumption)
          (sup_set (hlConstantsInFormula source) (hlConstantsInFormula goal)));
  });
hlGeneralizedConstants p (HL_ProofLine v va HL_Assumption vc) = [];
hlGeneralizedConstants p (HL_ProofLine v va (HL_MP vd ve) vc) = [];
hlGeneralizedConstants p (HL_ProofLine v va (HL_MT vd ve) vc) = [];
hlGeneralizedConstants p (HL_ProofLine v va (HL_DN vd) vc) = [];
hlGeneralizedConstants p (HL_ProofLine v va (HL_CP vd ve) vc) = [];
hlGeneralizedConstants p (HL_ProofLine v va (HL_AndIntro vd ve) vc) = [];
hlGeneralizedConstants p (HL_ProofLine v va (HL_AndElim vd) vc) = [];
hlGeneralizedConstants p (HL_ProofLine v va (HL_OrIntro vd) vc) = [];
hlGeneralizedConstants p (HL_ProofLine v va (HL_OrElim vd ve vf vg vh) vc) = [];
hlGeneralizedConstants p (HL_ProofLine v va (HL_RAA vd ve) vc) = [];
hlGeneralizedConstants p (HL_ProofLine v va (HL_ForallElim vd) vc) = [];
hlGeneralizedConstants p (HL_ProofLine v va (HL_ExistsIntro vd) vc) = [];
hlGeneralizedConstants p (HL_ProofLine v va HL_EqIntro vc) = [];
hlGeneralizedConstants p (HL_ProofLine v va (HL_EqElim vd ve) vc) = [];
hlGeneralizedConstants p (HL_ProofLine v va HL_LEM vc) = [];
hlGeneralizedConstants p (HL_ProofLine v va (HL_PropTaut vd) vc) = [];
hlGeneralizedConstants p (HL_ProofLine v va (HL_IffIntro vd ve) vc) = [];
hlGeneralizedConstants p (HL_ProofLine v va (HL_IffElim vd ve) vc) = [];
hlGeneralizedConstants p (HL_ProofLine v va (HL_QN vd) vc) = [];

hlEigenScopeViolations :: [Hl_line] -> [(Int, (String, Int))];
hlEigenScopeViolations p =
  concatMap
    (\ l ->
      concatMap
        (\ a ->
          map_filter
            (\ x ->
              (if (case hlFormulaAt p a of {
                    Nothing -> False;
                    Just assumption ->
                      member x (hlConstantsInFormula assumption);
                  })
                then Just (hlLineNumber l, (x, a)) else Nothing))
            (hlGeneralizedConstants p l))
        (hlEigenScopeAssumptions p l))
    p;

hlEigenScopeError :: [Hl_line] -> Maybe Hl_translation_error;
hlEigenScopeError p = (case hlEigenScopeViolations p of {
                        [] -> Nothing;
                        (n, (c, a)) : _ -> Just (HL_EigenInScope n c a);
                      });

hlBuildFitchItems :: [(Int, Int)] -> [Hl_line] -> [Hl_fitch_item];
hlBuildFitchItems boxes [] = [];
hlBuildFitchItems boxes (l : ls) =
  (case find (\ ac -> equal_int (fst ac) (hlLineNumber l)) boxes of {
    Nothing ->
      HL_FLine (hlLineNumber l) (hlFormula l)
        (hlToFitchRule (hlJustification l)) :
        hlBuildFitchItems boxes ls;
    Just ac ->
      HL_FSub
        (HL_Subproof (hlLineNumber l) (hlFormula l)
          (hlBuildFitchItems boxes
            (takeWhile (\ la -> less_eq_int (hlLineNumber la) (snd ac)) ls))) :
        hlBuildFitchItems boxes
          (dropWhile (\ la -> less_eq_int (hlLineNumber la) (snd ac)) ls);
  });

hlBoxOrderError :: [Hl_line] -> Maybe Hl_translation_error;
hlBoxOrderError p =
  (case filter (\ ac -> less_int (snd ac) (fst ac)) (hlBoxesOf p) of {
    [] -> Nothing;
    ac : _ -> Just (HL_BoxReversed (fst ac) (snd ac));
  });

hlPremiseError :: [Hl_line] -> Maybe Hl_translation_error;
hlPremiseError p =
  (case filter
          (\ l ->
            hlIsPremiseLine p l && not (null (hlBoxPath p (hlLineNumber l))))
          p
    of {
    [] -> Nothing;
    l : _ ->
      Just (HL_PremiseInBox (hlLineNumber l)
             (last (hlBoxPath p (hlLineNumber l))));
  });

hlDischargerOf :: [Hl_line] -> (Int, Int) -> Int;
hlDischargerOf p ac =
  (case find (\ l -> membera (hlDischargePairs (hlJustification l)) ac) p of {
    Nothing -> zero_int;
    Just a -> hlLineNumber a;
  });

hlOverlapping :: (Int, Int) -> (Int, Int) -> Bool;
hlOverlapping ac bd =
  less_int (fst ac) (fst bd) &&
    less_eq_int (fst bd) (snd ac) && less_int (snd ac) (snd bd);

hlNestingError :: [Hl_line] -> Maybe Hl_translation_error;
hlNestingError p =
  (case filter (\ ac -> any (hlOverlapping ac) (hlBoxesOf p)) (hlBoxesOf p) of {
    [] -> Nothing;
    ac : _ ->
      Just (HL_NotNested (hlDischargerOf p ac) (fst ac)
             (map_filter
               (\ x -> (if hlOverlapping ac x then Just (fst x) else Nothing))
               (hlBoxesOf p)));
  });

hlBoxHeadError :: [Hl_line] -> Maybe Hl_translation_error;
hlBoxHeadError p =
  (case filter
          (\ x ->
            equal_int (fst (fst x)) (fst (snd x)) &&
              not (equal_int (snd (fst x)) (snd (snd x))))
          (product (hlBoxesOf p) (hlBoxesOf p))
    of {
    [] -> Nothing;
    x : _ ->
      Just (HL_AssumptionReused (fst (fst x)) (snd (fst x)) (snd (snd x)));
  });

hlLemmonToFitchDirect :: [Hl_line] -> Sum Hl_translation_error [Hl_fitch_item];
hlLemmonToFitchDirect p =
  (if not (hlVerifiedCorrect p) then Inl (HL_SourceNotVerified zero_int)
    else (case hlBoxOrderError p of {
           Nothing ->
             (case hlBoxHeadError p of {
               Nothing ->
                 (case hlNestingError p of {
                   Nothing ->
                     (case hlPremiseError p of {
                       Nothing ->
                         (case hlScopeError p of {
                           Nothing ->
                             (case hlSubproofScopeError p of {
                               Nothing ->
                                 (case hlPremiseOrderError p of {
                                   Nothing ->
                                     (case hlEigenScopeError p of {
                                       Nothing ->
 Inr (hlBuildFitchItems (hlBoxesOf p) p);
                                       Just a -> Inl a;
                                     });
                                   Just a -> Inl a;
                                 });
                               Just a -> Inl a;
                             });
                           Just a -> Inl a;
                         });
                       Just a -> Inl a;
                     });
                   Just a -> Inl a;
                 });
               Just a -> Inl a;
             });
           Just a -> Inl a;
         }));

hlLemmonToFitch ::
  [Hl_line] -> Sum Hl_translation_error (Hl_route, [Hl_fitch_item]);
hlLemmonToFitch p = (case hlLemmonToFitchDirect p of {
                      Inl _ -> hlViaTree p;
                      Inr f -> Inr (HL_DirectRoute, f);
                    });

hlFitchConclusion :: [Hl_fitch_item] -> Maybe Hl_formula;
hlFitchConclusion f =
  (if null (hlFlattenFitch f) then Nothing
    else Just (fst (snd (last (hlFlattenFitch f)))));

hlPrefixForalls :: [String] -> Hl_formula -> Hl_formula;
hlPrefixForalls xs p = foldr HL_ForAll xs p;

lemmonToFitchChecked :: [Pline] -> Sum Translation_error (Route, [Fitch_item]);
lemmonToFitchChecked p =
  (case lemmonToFitchDirect p of {
    Inl _ -> viaTree p;
    Inr f -> (if fitchCorrect f then Inr (Direct, f) else viaTree p);
  });

positionalImage :: [Fitch_item] -> [Pline] -> Bool;
positionalImage f p = list_all2 lineMatches (flatten f) p;

hlPaperDependenciesOf :: (Int -> Set Int) -> Hl_justification -> Int -> Set Int;
hlPaperDependenciesOf look HL_Assumption self = insert self bot_set;
hlPaperDependenciesOf look (HL_CP a c) self = remove a (look c);
hlPaperDependenciesOf look (HL_RAA a c) self = remove a (look c);
hlPaperDependenciesOf look (HL_OrElim d a1 c1 a2 c2) self =
  sup_set (sup_set (look d) (remove a1 (look c1))) (remove a2 (look c2));
hlPaperDependenciesOf look (HL_ExistsElim m a c) self =
  sup_set (look m) (remove a (look c));
hlPaperDependenciesOf look (HL_MP v va) self =
  sup_seta (Set (map look (hlCitedLines (HL_MP v va))));
hlPaperDependenciesOf look (HL_MT v va) self =
  sup_seta (Set (map look (hlCitedLines (HL_MT v va))));
hlPaperDependenciesOf look (HL_DN v) self =
  sup_seta (Set (map look (hlCitedLines (HL_DN v))));
hlPaperDependenciesOf look (HL_AndIntro v va) self =
  sup_seta (Set (map look (hlCitedLines (HL_AndIntro v va))));
hlPaperDependenciesOf look (HL_AndElim v) self =
  sup_seta (Set (map look (hlCitedLines (HL_AndElim v))));
hlPaperDependenciesOf look (HL_OrIntro v) self =
  sup_seta (Set (map look (hlCitedLines (HL_OrIntro v))));
hlPaperDependenciesOf look (HL_ForallElim v) self =
  sup_seta (Set (map look (hlCitedLines (HL_ForallElim v))));
hlPaperDependenciesOf look (HL_ExistsIntro v) self =
  sup_seta (Set (map look (hlCitedLines (HL_ExistsIntro v))));
hlPaperDependenciesOf look (HL_ForallIntro v) self =
  sup_seta (Set (map look (hlCitedLines (HL_ForallIntro v))));
hlPaperDependenciesOf look HL_EqIntro self =
  sup_seta (Set (map look (hlCitedLines HL_EqIntro)));
hlPaperDependenciesOf look (HL_EqElim v va) self =
  sup_seta (Set (map look (hlCitedLines (HL_EqElim v va))));
hlPaperDependenciesOf look HL_LEM self =
  sup_seta (Set (map look (hlCitedLines HL_LEM)));
hlPaperDependenciesOf look (HL_PropTaut v) self =
  sup_seta (Set (map look (hlCitedLines (HL_PropTaut v))));
hlPaperDependenciesOf look (HL_IffIntro v va) self =
  sup_seta (Set (map look (hlCitedLines (HL_IffIntro v va))));
hlPaperDependenciesOf look (HL_IffElim v va) self =
  sup_seta (Set (map look (hlCitedLines (HL_IffElim v va))));
hlPaperDependenciesOf look (HL_QN v) self =
  sup_seta (Set (map look (hlCitedLines (HL_QN v))));

hlPaperDependencyAt :: [Hl_line] -> Int -> Set Int;
hlPaperDependencyAt e n = (case hlReferencesAt e n of {
                            Nothing -> bot_set;
                            Just g -> g;
                          });

hlCanonicalFrom :: [Hl_line] -> [Hl_line] -> Bool;
hlCanonicalFrom e [] = True;
hlCanonicalFrom e (l : ls) =
  equal_set (hlReferences l)
    (hlPaperDependenciesOf (hlPaperDependencyAt e) (hlJustification l)
      (hlLineNumber l)) &&
    hlCanonicalFrom (e ++ [l]) ls;

hlCanonicalDependencies :: [Hl_line] -> Bool;
hlCanonicalDependencies p = hlCanonicalFrom [] p;

hlPaperCorrect :: [Hl_line] -> Bool;
hlPaperCorrect p = hlVerifiedCorrect p && hlCanonicalDependencies p;

hlEmitDerivations ::
  Nat ->
    [(Int, (Int, Hl_formula))] ->
      [Hl_formula] ->
        Int -> Nat -> [Hl_derivation] -> ([Hl_fitch_item], ([Int], (Int, Nat)));
hlEmitDerivations base env scope next count ds =
  hlEmitDerivationsUsing (hlEmitDerivation base env scope) next count ds;

hlSubAssumptionLine :: Hl_subproof -> Int;
hlSubAssumptionLine (HL_Subproof a p body) = a;

hlSubAssumptionFormula :: Hl_subproof -> Hl_formula;
hlSubAssumptionFormula (HL_Subproof a p body) = p;

hlVariablesInFormula :: Hl_formula -> Set String;
hlVariablesInFormula (HL_Predicate uu ts) =
  sup_seta (image hlVariablesInTerm (Set ts));
hlVariablesInFormula (HL_Boolean uv) = bot_set;
hlVariablesInFormula (HL_Not p) = hlVariablesInFormula p;
hlVariablesInFormula (HL_And p q) =
  sup_set (hlVariablesInFormula p) (hlVariablesInFormula q);
hlVariablesInFormula (HL_Or p q) =
  sup_set (hlVariablesInFormula p) (hlVariablesInFormula q);
hlVariablesInFormula (HL_Implies p q) =
  sup_set (hlVariablesInFormula p) (hlVariablesInFormula q);
hlVariablesInFormula (HL_Iff p q) =
  sup_set (hlVariablesInFormula p) (hlVariablesInFormula q);
hlVariablesInFormula (HL_ForAll uw p) = hlVariablesInFormula p;
hlVariablesInFormula (HL_Exists ux p) = hlVariablesInFormula p;

hlFiniteEvalClosed ::
  forall a. (Eq a) => Hl_finite_model a -> Hl_formula -> Maybe Bool;
hlFiniteEvalClosed m p =
  (if equal_set (hlFreeVariables p) bot_set then hlFiniteEval m [] p
    else Nothing);

hlDerivationConstants :: Hl_derivation -> Set String;
hlDerivationConstants d =
  sup_seta (image hlConstantsInFormula (Set (hlDerivationFormulas d)));

hlStripDependencies :: [Hl_line] -> [(Int, (Hl_formula, Hl_justification))];
hlStripDependencies p =
  map (\ l -> (hlLineNumber l, (hlFormula l, hlJustification l))) p;

hlLemmonToFitchChecked ::
  [Hl_line] -> Sum Hl_translation_error (Hl_route, [Hl_fitch_item]);
hlLemmonToFitchChecked p =
  (case hlLemmonToFitchDirect p of {
    Inl _ -> hlViaTree p;
    Inr f ->
      (if hlFitchCorrect f &&
            superset (hlOpenPremises p) (hlFitchPremises f) &&
              hlConclusion (hlFitchToLemmon f) == hlConclusion p
        then Inr (HL_DirectRoute, f) else hlViaTree p);
  });

hlRecomputeDependenciesFrom ::
  [Hl_line] -> [(Int, (Hl_formula, Hl_justification))] -> [Hl_line];
hlRecomputeDependenciesFrom e [] = e;
hlRecomputeDependenciesFrom e ((n, (p, j)) : ls) =
  hlRecomputeDependenciesFrom
    (e ++ [HL_ProofLine n p j
             (hlPaperDependenciesOf (hlPaperDependencyAt e) j n)])
    ls;

hlRecomputeDependencies :: [(Int, (Hl_formula, Hl_justification))] -> [Hl_line];
hlRecomputeDependencies = hlRecomputeDependenciesFrom [];

hlFiniteStandardEquality :: forall a. (Eq a) => Hl_finite_model a -> Bool;
hlFiniteStandardEquality m =
  (case map_of (hlFinitePredicates m) ("=", nat_of_integer (2 :: Integer)) of {
    Nothing -> False;
    Just relation ->
      let {
        diagonal = map (\ x -> [x, x]) (hlFiniteDomain m);
      } in all (membera diagonal) relation && all (membera relation) diagonal;
  });

}
