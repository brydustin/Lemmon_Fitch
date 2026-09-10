(*  Title:      LF_HLW.thy

    The executable Lemmon checker in
    Halvorson/lemmon-checker-main/src/{ProofTypes,LemmonChecker,TruthTable}.hs,
    represented directly in Isabelle.  Constructor shapes, citation order,
    dependency arithmetic, multi-quantifier rules, and the Haskell program's
    line-number discipline are deliberately preserved.
*)

theory LF_HLW
  imports LF_HLW_Formula
begin

section \<open>The twenty-one How Logic Works justifications\<close>

datatype hl_justification =
    HL_Assumption
  | HL_MP int int
  | HL_MT int int
  | HL_DN int
  | HL_CP int int
  | HL_AndIntro int int
  | HL_AndElim int
  | HL_OrIntro int
  | HL_OrElim int int int int int
  | HL_RAA int int
  | HL_ForallElim int
  | HL_ExistsIntro int
  | HL_ForallIntro int
  | HL_ExistsElim int int int
  | HL_EqIntro
  | HL_EqElim int int
  | HL_LEM
  | HL_PropTaut "int list"
  | HL_IffIntro int int
  | HL_IffElim int int
  | HL_QN int

datatype hl_line =
  HL_ProofLine
    (hlLineNumber: int)
    (hlFormula: hl_formula)
    (hlJustification: hl_justification)
    (hlReferences: "int set")

type_synonym hl_proof = "hl_line list"
type_synonym halvorson_proof = hl_proof

fun hlCitedLines :: "hl_justification \<Rightarrow> int list" where
  "hlCitedLines HL_Assumption = []"
| "hlCitedLines (HL_MP m n) = [m,n]"
| "hlCitedLines (HL_MT m n) = [m,n]"
| "hlCitedLines (HL_DN m) = [m]"
| "hlCitedLines (HL_CP m n) = [m,n]"
| "hlCitedLines (HL_AndIntro m n) = [m,n]"
| "hlCitedLines (HL_AndElim m) = [m]"
| "hlCitedLines (HL_OrIntro m) = [m]"
| "hlCitedLines (HL_OrElim d a1 c1 a2 c2) = [d,a1,c1,a2,c2]"
| "hlCitedLines (HL_RAA a c) = [a,c]"
| "hlCitedLines (HL_ForallElim m) = [m]"
| "hlCitedLines (HL_ExistsIntro m) = [m]"
| "hlCitedLines (HL_ForallIntro m) = [m]"
| "hlCitedLines (HL_ExistsElim m a c) = [m,a,c]"
| "hlCitedLines HL_EqIntro = []"
| "hlCitedLines (HL_EqElim m n) = [m,n]"
| "hlCitedLines HL_LEM = []"
| "hlCitedLines (HL_PropTaut ms) = ms"
| "hlCitedLines (HL_IffIntro m n) = [m,n]"
| "hlCitedLines (HL_IffElim m n) = [m,n]"
| "hlCitedLines (HL_QN m) = [m]"

fun hlDischargePairs :: "hl_justification \<Rightarrow> (int \<times> int) list" where
  "hlDischargePairs (HL_CP a c) = [(a,c)]"
| "hlDischargePairs (HL_RAA a c) = [(a,c)]"
| "hlDischargePairs (HL_OrElim d a1 c1 a2 c2) = [(a1,c1),(a2,c2)]"
| "hlDischargePairs (HL_ExistsElim m a c) = [(a,c)]"
| "hlDischargePairs _ = []"

fun hlLookupLine :: "hl_proof \<Rightarrow> int \<Rightarrow> hl_line option" where
  "hlLookupLine [] n = None"
| "hlLookupLine (l # ls) n =
     (if hlLineNumber l = n then Some l else hlLookupLine ls n)"

definition hlFormulaAt :: "hl_proof \<Rightarrow> int \<Rightarrow> hl_formula option" where
  "hlFormulaAt P n = map_option hlFormula (hlLookupLine P n)"

definition hlReferencesAt :: "hl_proof \<Rightarrow> int \<Rightarrow> int set option" where
  "hlReferencesAt P n = map_option hlReferences (hlLookupLine P n)"

definition hlJustificationAt ::
    "hl_proof \<Rightarrow> int \<Rightarrow> hl_justification option" where
  "hlJustificationAt P n = map_option hlJustification (hlLookupLine P n)"

definition hlIsAssumptionLine :: "hl_proof \<Rightarrow> int \<Rightarrow> bool" where
  "hlIsAssumptionLine P n \<longleftrightarrow>
     hlJustificationAt P n = Some HL_Assumption"

fun hlMapFilter :: "('a \<Rightarrow> 'b option) \<Rightarrow> 'a list \<Rightarrow> 'b list" where
  "hlMapFilter f [] = []"
| "hlMapFilter f (x # xs) =
     (case f x of None \<Rightarrow> hlMapFilter f xs | Some y \<Rightarrow> y # hlMapFilter f xs)"

definition hlReferenceUnion :: "hl_proof \<Rightarrow> int list \<Rightarrow> int set" where
  "hlReferenceUnion P ns = \<Union> (set (hlMapFilter (hlReferencesAt P) ns))"

definition hlAssumptionConstants :: "hl_proof \<Rightarrow> int set \<Rightarrow> hl_name set" where
  "hlAssumptionConstants P G =
     \<Union> (hlConstantsInFormula `
       hlFormula ` set (filter
         (\<lambda>l. hlLineNumber l \<in> G \<and> hlJustification l = HL_Assumption) P))"

definition hlReferencedConstants :: "hl_proof \<Rightarrow> int set \<Rightarrow> hl_name set" where
  "hlReferencedConstants P G =
     \<Union> (hlConstantsInFormula `
       hlFormula ` set (filter (\<lambda>l. hlLineNumber l \<in> G) P))"

section \<open>Propositional consequence\<close>

fun hlPropositionalAtoms :: "hl_formula \<Rightarrow> hl_formula list" where
  "hlPropositionalAtoms (HL_Predicate P ts) = [HL_Predicate P ts]"
| "hlPropositionalAtoms (HL_Boolean _) = []"
| "hlPropositionalAtoms (HL_Not p) = hlPropositionalAtoms p"
| "hlPropositionalAtoms (HL_And p q) =
     hlPropositionalAtoms p @ hlPropositionalAtoms q"
| "hlPropositionalAtoms (HL_Or p q) =
     hlPropositionalAtoms p @ hlPropositionalAtoms q"
| "hlPropositionalAtoms (HL_Implies p q) =
     hlPropositionalAtoms p @ hlPropositionalAtoms q"
| "hlPropositionalAtoms (HL_Iff p q) =
     hlPropositionalAtoms p @ hlPropositionalAtoms q"
| "hlPropositionalAtoms p = [p]"

fun hlValuations :: "hl_formula list \<Rightarrow> (hl_formula \<Rightarrow> bool) list" where
  "hlValuations [] = [(\<lambda>_. False)]"
| "hlValuations (p # ps) =
     map (\<lambda>v. v(p := False)) (hlValuations ps) @
     map (\<lambda>v. v(p := True)) (hlValuations ps)"

fun hlPropositionalValue :: "(hl_formula \<Rightarrow> bool) \<Rightarrow> hl_formula \<Rightarrow> bool" where
  "hlPropositionalValue v (HL_Boolean b) \<longleftrightarrow> b"
| "hlPropositionalValue v (HL_Not p) \<longleftrightarrow> \<not> hlPropositionalValue v p"
| "hlPropositionalValue v (HL_And p q) \<longleftrightarrow>
     hlPropositionalValue v p \<and> hlPropositionalValue v q"
| "hlPropositionalValue v (HL_Or p q) \<longleftrightarrow>
     hlPropositionalValue v p \<or> hlPropositionalValue v q"
| "hlPropositionalValue v (HL_Implies p q) \<longleftrightarrow>
     (hlPropositionalValue v p \<longrightarrow> hlPropositionalValue v q)"
| "hlPropositionalValue v (HL_Iff p q) \<longleftrightarrow>
     (hlPropositionalValue v p \<longleftrightarrow> hlPropositionalValue v q)"
| "hlPropositionalValue v p \<longleftrightarrow> v p"

definition hlPropositionalConsequence ::
    "hl_formula list \<Rightarrow> hl_formula \<Rightarrow> bool" where
  "hlPropositionalConsequence premises conclusion \<longleftrightarrow>
     (let atoms = remdups
          (concat (map hlPropositionalAtoms (conclusion # premises)))
      in list_all (\<lambda>v.
           list_all (hlPropositionalValue v) premises \<longrightarrow>
           hlPropositionalValue v conclusion)
         (hlValuations atoms))"

definition hlContradiction :: "hl_formula \<Rightarrow> bool" where
  "hlContradiction p \<longleftrightarrow>
     (case p of
        HL_And q (HL_Not r) \<Rightarrow> q = r
      | HL_And (HL_Not q) r \<Rightarrow> q = r
      | _ \<Rightarrow> False)"

definition hlExcludedMiddle :: "hl_formula \<Rightarrow> bool" where
  "hlExcludedMiddle p \<longleftrightarrow>
     (case p of
        HL_Or q (HL_Not r) \<Rightarrow> q = r
      | HL_Or (HL_Not q) r \<Rightarrow> q = r
      | _ \<Rightarrow> False)"

section \<open>The line checker\<close>

definition hlRuleOK :: "hl_proof \<Rightarrow> hl_line \<Rightarrow> bool" where
  "hlRuleOK P l \<longleftrightarrow>
     (let phi = hlFormula l; G = hlReferences l; j = hlJustification l
      in case j of
        HL_Assumption \<Rightarrow> G = {hlLineNumber l}
      | HL_MP m n \<Rightarrow>
          (case (hlLookupLine P m,hlLookupLine P n) of
             (Some lm,Some ln) \<Rightarrow>
               (case hlFormula lm of
                  HL_Implies p q \<Rightarrow>
                    hlFormula ln = p \<and> phi = q \<and>
                    G = hlReferences lm \<union> hlReferences ln
                | _ \<Rightarrow> False)
           | _ \<Rightarrow> False)
      | HL_MT m n \<Rightarrow>
          (case (hlLookupLine P m,hlLookupLine P n,phi) of
             (Some lm,Some ln,HL_Not p) \<Rightarrow>
               (case (hlFormula lm,hlFormula ln) of
                  (HL_Implies q r,HL_Not s) \<Rightarrow>
                    p = q \<and> r = s \<and>
                    G = hlReferences lm \<union> hlReferences ln
                | _ \<Rightarrow> False)
           | _ \<Rightarrow> False)
      | HL_DN m \<Rightarrow>
          (case hlLookupLine P m of
             Some lm \<Rightarrow>
               (hlFormula lm = HL_Not (HL_Not phi) \<or>
                phi = HL_Not (HL_Not (hlFormula lm))) \<and> G = hlReferences lm
           | None \<Rightarrow> False)
      | HL_CP a c \<Rightarrow>
          (case (hlLookupLine P a,hlLookupLine P c) of
             (Some la,Some lc) \<Rightarrow>
               hlJustification la = HL_Assumption \<and>
               phi = HL_Implies (hlFormula la) (hlFormula lc) \<and>
               G = hlReferences lc - {hlLineNumber la}
           | _ \<Rightarrow> False)
      | HL_AndIntro m n \<Rightarrow>
          (case (hlLookupLine P m,hlLookupLine P n) of
             (Some lm,Some ln) \<Rightarrow>
               (phi = HL_And (hlFormula lm) (hlFormula ln) \<or>
                phi = HL_And (hlFormula ln) (hlFormula lm)) \<and>
               G = hlReferences lm \<union> hlReferences ln
           | _ \<Rightarrow> False)
      | HL_AndElim m \<Rightarrow>
          (case hlLookupLine P m of
             Some lm \<Rightarrow>
               (case hlFormula lm of
                  HL_And p q \<Rightarrow> (phi = p \<or> phi = q) \<and> G = hlReferences lm
                | _ \<Rightarrow> False)
           | None \<Rightarrow> False)
      | HL_OrIntro m \<Rightarrow>
          (case (hlLookupLine P m,phi) of
             (Some lm,HL_Or p q) \<Rightarrow>
               (hlFormula lm = p \<or> hlFormula lm = q) \<and> G = hlReferences lm
           | _ \<Rightarrow> False)
      | HL_OrElim d a1 c1 a2 c2 \<Rightarrow>
          (case (hlLookupLine P d,hlLookupLine P a1,hlLookupLine P c1,
                 hlLookupLine P a2,hlLookupLine P c2) of
             (Some ld,Some la1,Some lc1,Some la2,Some lc2) \<Rightarrow>
               hlJustification la1 = HL_Assumption \<and>
               hlJustification la2 = HL_Assumption \<and>
               hlFormula lc1 = phi \<and> hlFormula lc2 = phi \<and>
               (case hlFormula ld of
                  HL_Or p q \<Rightarrow>
                    ((hlFormula la1 = p \<and> hlFormula la2 = q) \<or>
                     (hlFormula la1 = q \<and> hlFormula la2 = p))
                | _ \<Rightarrow> False) \<and>
               G = hlReferences ld \<union>
                   (hlReferences lc1 - {hlLineNumber la1}) \<union>
                   (hlReferences lc2 - {hlLineNumber la2})
           | _ \<Rightarrow> False)
      | HL_RAA a c \<Rightarrow>
          (case (hlLookupLine P a,hlLookupLine P c) of
             (Some la,Some lc) \<Rightarrow>
               hlJustification la = HL_Assumption \<and>
               phi = HL_Not (hlFormula la) \<and>
               hlContradiction (hlFormula lc) \<and>
               G = hlReferences lc - {hlLineNumber la}
           | _ \<Rightarrow> False)
      | HL_ForallElim m \<Rightarrow>
          (case hlLookupLine P m of
             Some lm \<Rightarrow>
               (let (sourceVars,sourceCore) = hlCollectForalls (hlFormula lm);
                    (targetVars,targetCore) = hlCollectForalls phi
                in (case hlEliminationCount sourceVars targetVars of
                      Some k \<Rightarrow>
                        hlInferWitnessConstsK sourceVars sourceCore k targetCore \<noteq> None \<and>
                        G = hlReferences lm
                    | None \<Rightarrow> False))
           | None \<Rightarrow> False)
      | HL_ExistsIntro m \<Rightarrow>
          (case hlLookupLine P m of
             Some lm \<Rightarrow>
               (let (xs,core) = hlCollectExists phi
                in xs \<noteq> [] \<and>
                   list_ex (\<lambda>k.
                     hlInferWitnessConstsK xs
                       (hlPrefixExists (drop k xs) core) k (hlFormula lm) \<noteq> None)
                     [0..<Suc (length xs)] \<and> G = hlReferences lm)
           | None \<Rightarrow> False)
      | HL_ForallIntro m \<Rightarrow>
          (case hlLookupLine P m of
             Some lm \<Rightarrow>
               (let (xs,core) = hlCollectForalls phi
                in xs \<noteq> [] \<and>
                   (case hlInferWitnessConstsK xs core (length xs) (hlFormula lm) of
                      Some cs \<Rightarrow>
                        (let pairs = filter (\<lambda>xc. snd xc \<noteq> STR '''') (zip xs cs)
                         in hlAbstractMany pairs (hlFormula lm) = Some core \<and>
                            (\<forall>c \<in> snd ` set pairs.
                               c \<notin> hlAssumptionConstants P (hlReferences lm)) \<and>
                            G = hlReferences lm)
                    | None \<Rightarrow> False))
           | None \<Rightarrow> False)
      | HL_ExistsElim m a c \<Rightarrow>
          (case (hlLookupLine P m,hlLookupLine P a,hlLookupLine P c) of
             (Some lm,Some la,Some lc) \<Rightarrow>
               (let (sourceVars,sourceCore) = hlCollectExists (hlFormula lm);
                    (targetVars,targetCore) = hlCollectExists (hlFormula la);
                    delta = hlReferences lc - {hlLineNumber la}
                in sourceVars \<noteq> [] \<and> hlJustification la = HL_Assumption \<and>
                   (case hlEliminationCount sourceVars targetVars of
                      Some k \<Rightarrow>
                        (let template = hlPrefixExists targetVars sourceCore
                         in (case hlInferWitnessConstsK sourceVars template k (hlFormula la) of
                               Some cs \<Rightarrow>
                                 (let pairs = filter (\<lambda>xc. snd xc \<noteq> STR '''')
                                                (zip (take k sourceVars) cs)
                                  in hlAbstractMany pairs (hlFormula la) = Some template \<and>
                                     (\<forall>w \<in> snd ` set pairs.
                                        w \<notin> hlConstantsInFormula (hlFormula lc) \<and>
                                        w \<notin> hlReferencedConstants P delta) \<and>
                                     phi = hlFormula lc \<and>
                                     G = hlReferences lm \<union> delta)
                             | None \<Rightarrow> False))
                    | None \<Rightarrow> False))
           | _ \<Rightarrow> False)
      | HL_EqIntro \<Rightarrow>
          (case phi of
             HL_Predicate E [HL_Const a,HL_Const b] \<Rightarrow>
               E = STR ''='' \<and> a = b \<and> G = {}
           | _ \<Rightarrow> False)
      | HL_EqElim m n \<Rightarrow>
          (case (hlLookupLine P m,hlLookupLine P n) of
             (Some lm,Some ln) \<Rightarrow>
               (case hlEqualityFormula (hlFormula ln) of
                  Some (HL_Const a,HL_Const b) \<Rightarrow>
                    hlEqualUpToConstantReplacement a b (hlFormula lm) phi \<and>
                    G = hlReferences lm \<union> hlReferences ln
                | _ \<Rightarrow> False)
           | _ \<Rightarrow> False)
      | HL_LEM \<Rightarrow> hlExcludedMiddle phi
      | HL_PropTaut ms \<Rightarrow>
          list_all (\<lambda>m. hlLookupLine P m \<noteq> None) ms \<and>
          hlPropositionalConsequence (hlMapFilter (hlFormulaAt P) ms) phi \<and>
          G = hlReferenceUnion P ms
      | HL_IffIntro m n \<Rightarrow>
          (case (hlLookupLine P m,hlLookupLine P n,phi) of
             (Some lm,Some ln,HL_Iff u v) \<Rightarrow>
               (case (hlFormula lm,hlFormula ln) of
                  (HL_Implies p q,HL_Implies r s) \<Rightarrow>
                    p = s \<and> q = r \<and>
                    ((u = p \<and> v = q) \<or> (u = q \<and> v = p)) \<and>
                    G = hlReferences lm \<union> hlReferences ln
                | _ \<Rightarrow> False)
           | _ \<Rightarrow> False)
      | HL_IffElim m n \<Rightarrow>
          (case (hlLookupLine P m,hlLookupLine P n) of
             (Some lm,Some ln) \<Rightarrow>
               (case hlFormula lm of
                  HL_Iff p q \<Rightarrow>
                    ((hlFormula ln = p \<and> phi = q) \<or>
                     (hlFormula ln = q \<and> phi = p)) \<and>
                    G = hlReferences lm \<union> hlReferences ln
                | _ \<Rightarrow> False)
           | _ \<Rightarrow> False)
      | HL_QN m \<Rightarrow>
          (case hlLookupLine P m of
             Some lm \<Rightarrow>
               hlQuantifierNegationEquivalent (hlFormula lm) phi \<and>
               G = hlReferences lm
           | None \<Rightarrow> False))"

definition hlStructureOK :: "hl_proof \<Rightarrow> hl_line \<Rightarrow> bool" where
  "hlStructureOK P l \<longleftrightarrow>
     length (filter (\<lambda>k. hlLineNumber k = hlLineNumber l) P) = 1 \<and>
     (\<forall>m \<in> set (hlCitedLines (hlJustification l)). m < hlLineNumber l)"

definition hlLineOK :: "hl_proof \<Rightarrow> hl_line \<Rightarrow> bool" where
  "hlLineOK P l \<longleftrightarrow> hlStructureOK P l \<and> hlRuleOK P l"

definition hlCorrect :: "hl_proof \<Rightarrow> bool" where
  "hlCorrect P \<longleftrightarrow> list_all (hlLineOK P) P"

definition hlConclusion :: "hl_proof \<Rightarrow> hl_formula option" where
  "hlConclusion P = (if P = [] then None else Some (hlFormula (last P)))"

definition hlOpenPremises :: "hl_proof \<Rightarrow> hl_formula list" where
  "hlOpenPremises P =
     (if P = [] then []
      else map hlFormula
        (filter (\<lambda>l. hlLineNumber l \<in> hlReferences (last P) \<and>
                    hlJustification l = HL_Assumption) P))"

text \<open>
  The Haskell LEM branch checks only the displayed formula.  Consequently a
  LEM line may carry arbitrary dependency numbers.  The exact checker above
  preserves that observable behavior; the strengthened predicate below is the
  kernel used for verified translation and code generation.
\<close>

definition hlDependencyClosed :: "hl_proof \<Rightarrow> bool" where
  "hlDependencyClosed P \<longleftrightarrow>
     (\<forall>l \<in> set P. hlReferences l \<subseteq>
        hlLineNumber ` {a \<in> set P. hlJustification a = HL_Assumption})"

definition hlCanonicalOrder :: "hl_proof \<Rightarrow> bool" where
  "hlCanonicalOrder P \<longleftrightarrow>
     list_all (\<lambda>n. 0 < n) (map hlLineNumber P) \<and>
     sorted_wrt (<) (map hlLineNumber P)"

definition hlVerifiedCorrect :: "hl_proof \<Rightarrow> bool" where
  "hlVerifiedCorrect P \<longleftrightarrow>
     hlCorrect P \<and> hlDependencyClosed P \<and> hlCanonicalOrder P"

lemma hl_LEM_preserves_legacy_dependency_behavior:
  "hlRuleOK P (HL_ProofLine n (p \<or>\<^sub>H \<not>\<^sub>H p) HL_LEM G)"
  by (cases p; simp add: hlRuleOK_def hlExcludedMiddle_def)

section \<open>Executable correspondence examples\<close>

abbreviation hlP :: hl_formula where "hlP \<equiv> HL_Predicate (STR ''P'') []"
abbreviation hlQ :: hl_formula where "hlQ \<equiv> HL_Predicate (STR ''Q'') []"
abbreviation hlPredF :: "hl_term \<Rightarrow> hl_formula" where
  "hlPredF t \<equiv> HL_Predicate (STR ''F'') [t]"
abbreviation hlx :: hl_name where "hlx \<equiv> STR ''x''"
abbreviation hla :: hl_name where "hla \<equiv> STR ''a''"
abbreviation hlb :: hl_name where "hlb \<equiv> STR ''b''"

definition hl_assumption_example :: hl_proof where
  "hl_assumption_example = [HL_ProofLine 1 hlP HL_Assumption {1}]"

definition hl_mp_example :: hl_proof where
  "hl_mp_example =
     [ HL_ProofLine 1 (hlP \<longrightarrow>\<^sub>H hlQ) HL_Assumption {1},
       HL_ProofLine 2 hlP HL_Assumption {2},
       HL_ProofLine 3 hlQ (HL_MP 1 2) {1,2} ]"

definition hl_mt_example :: hl_proof where
  "hl_mt_example =
     [ HL_ProofLine 1 (hlP \<longrightarrow>\<^sub>H hlQ) HL_Assumption {1},
       HL_ProofLine 2 (\<not>\<^sub>H hlQ) HL_Assumption {2},
       HL_ProofLine 3 (\<not>\<^sub>H hlP) (HL_MT 1 2) {1,2} ]"

definition hl_dn_example :: hl_proof where
  "hl_dn_example =
     [ HL_ProofLine 1 hlP HL_Assumption {1},
       HL_ProofLine 2 (\<not>\<^sub>H \<not>\<^sub>H hlP) (HL_DN 1) {1} ]"

definition hl_cp_example :: hl_proof where
  "hl_cp_example =
     [ HL_ProofLine 1 hlP HL_Assumption {1},
       HL_ProofLine 2 hlQ HL_Assumption {2},
       HL_ProofLine 3 (hlP \<and>\<^sub>H hlQ) (HL_AndIntro 1 2) {1,2},
       HL_ProofLine 4 (hlQ \<longrightarrow>\<^sub>H (hlP \<and>\<^sub>H hlQ)) (HL_CP 2 3) {1} ]"

definition hl_and_elim_example :: hl_proof where
  "hl_and_elim_example =
     [ HL_ProofLine 1 (hlP \<and>\<^sub>H hlQ) HL_Assumption {1},
       HL_ProofLine 2 hlQ (HL_AndElim 1) {1} ]"

definition hl_or_intro_example :: hl_proof where
  "hl_or_intro_example =
     [ HL_ProofLine 1 hlP HL_Assumption {1},
       HL_ProofLine 2 (hlQ \<or>\<^sub>H hlP) (HL_OrIntro 1) {1} ]"

definition hl_or_elim_example :: hl_proof where
  "hl_or_elim_example =
     [ HL_ProofLine 1 (hlP \<or>\<^sub>H hlQ) HL_Assumption {1},
       HL_ProofLine 2 hlP HL_Assumption {2},
       HL_ProofLine 3 (hlQ \<or>\<^sub>H hlP) (HL_OrIntro 2) {2},
       HL_ProofLine 4 hlQ HL_Assumption {4},
       HL_ProofLine 5 (hlQ \<or>\<^sub>H hlP) (HL_OrIntro 4) {4},
       HL_ProofLine 6 (hlQ \<or>\<^sub>H hlP) (HL_OrElim 1 2 3 4 5) {1} ]"

definition hl_raa_example :: hl_proof where
  "hl_raa_example =
     [ HL_ProofLine 1 hlP HL_Assumption {1},
       HL_ProofLine 2 (\<not>\<^sub>H hlP) HL_Assumption {2},
       HL_ProofLine 3 (hlP \<and>\<^sub>H \<not>\<^sub>H hlP) (HL_AndIntro 1 2) {1,2},
       HL_ProofLine 4 (\<not>\<^sub>H hlP) (HL_RAA 1 3) {2} ]"

definition hl_forall_elim_example :: hl_proof where
  "hl_forall_elim_example =
     [ HL_ProofLine 1 (\<forall>\<^sub>H hlx. hlPredF (HL_Var hlx)) HL_Assumption {1},
       HL_ProofLine 2 (hlPredF (HL_Const hla)) (HL_ForallElim 1) {1} ]"

definition hl_exists_intro_example :: hl_proof where
  "hl_exists_intro_example =
     [ HL_ProofLine 1 (hlPredF (HL_Const hla)) HL_Assumption {1},
       HL_ProofLine 2 (\<exists>\<^sub>H hlx. hlPredF (HL_Var hlx)) (HL_ExistsIntro 1) {1} ]"

definition hl_forall_intro_example :: hl_proof where
  "hl_forall_intro_example =
     [ HL_ProofLine 1 (\<forall>\<^sub>H hlx. hlPredF (HL_Var hlx)) HL_Assumption {1},
       HL_ProofLine 2 (hlPredF (HL_Const hla)) (HL_ForallElim 1) {1},
       HL_ProofLine 3 (\<forall>\<^sub>H hlx. hlPredF (HL_Var hlx)) (HL_ForallIntro 2) {1} ]"

definition hl_exists_elim_example :: hl_proof where
  "hl_exists_elim_example =
     [ HL_ProofLine 1 (\<exists>\<^sub>H hlx. hlPredF (HL_Var hlx)) HL_Assumption {1},
       HL_ProofLine 2 (hlPredF (HL_Const hla)) HL_Assumption {2},
       HL_ProofLine 3 hlP HL_Assumption {3},
       HL_ProofLine 4 hlP (HL_ExistsElim 1 2 3) {1,3} ]"

definition hl_eq_intro_example :: hl_proof where
  "hl_eq_intro_example = [HL_ProofLine 1 (HL_Const hla =\<^sub>H HL_Const hla) HL_EqIntro {}]"

definition hl_eq_elim_example :: hl_proof where
  "hl_eq_elim_example =
     [ HL_ProofLine 1 (hlPredF (HL_Const hla)) HL_Assumption {1},
       HL_ProofLine 2 (HL_Const hla =\<^sub>H HL_Const hlb) HL_Assumption {2},
       HL_ProofLine 3 (hlPredF (HL_Const hlb)) (HL_EqElim 1 2) {1,2} ]"

definition hl_lem_example :: hl_proof where
  "hl_lem_example = [HL_ProofLine 1 (hlP \<or>\<^sub>H \<not>\<^sub>H hlP) HL_LEM {}]"

definition hl_prop_taut_example :: hl_proof where
  "hl_prop_taut_example = [HL_ProofLine 1 (hlP \<longrightarrow>\<^sub>H hlP) (HL_PropTaut []) {}]"

definition hl_iff_intro_example :: hl_proof where
  "hl_iff_intro_example =
     [ HL_ProofLine 1 (hlP \<longrightarrow>\<^sub>H hlQ) HL_Assumption {1},
       HL_ProofLine 2 (hlQ \<longrightarrow>\<^sub>H hlP) HL_Assumption {2},
       HL_ProofLine 3 (hlP \<longleftrightarrow>\<^sub>H hlQ) (HL_IffIntro 1 2) {1,2} ]"

definition hl_iff_elim_example :: hl_proof where
  "hl_iff_elim_example =
     [ HL_ProofLine 1 (hlP \<longleftrightarrow>\<^sub>H hlQ) HL_Assumption {1},
       HL_ProofLine 2 hlP HL_Assumption {2},
       HL_ProofLine 3 hlQ (HL_IffElim 1 2) {1,2} ]"

definition hl_qn_example :: hl_proof where
  "hl_qn_example =
     [ HL_ProofLine 1 (\<not>\<^sub>H (\<forall>\<^sub>H hlx. hlPredF (HL_Var hlx))) HL_Assumption {1},
       HL_ProofLine 2 (\<exists>\<^sub>H hlx. \<not>\<^sub>H hlPredF (HL_Var hlx)) (HL_QN 1) {1} ]"

definition hl_all_rule_examples :: "hl_proof list" where
  "hl_all_rule_examples =
     [ hl_assumption_example, hl_mp_example, hl_mt_example, hl_dn_example,
       hl_cp_example, take 3 hl_cp_example, hl_and_elim_example,
       hl_or_intro_example, hl_or_elim_example, hl_raa_example,
       hl_forall_elim_example, hl_exists_intro_example,
       hl_forall_intro_example, hl_exists_elim_example,
       hl_eq_intro_example, hl_eq_elim_example, hl_lem_example,
       hl_prop_taut_example, hl_iff_intro_example, hl_iff_elim_example,
       hl_qn_example ]"

lemma hl_all_authoritative_examples:
  "list_all hlCorrect hl_all_rule_examples"
  by eval

lemma hl_truth_constants_regression:
  "hlPropositionalConsequence [] \<top>\<^sub>H \<and>
   \<not> hlPropositionalConsequence [] \<bottom>\<^sub>H"
  by eval

end
