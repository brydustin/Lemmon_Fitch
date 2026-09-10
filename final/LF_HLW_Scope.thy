(* Scope-based rule checking for the exact Haskell-shaped calculus. *)

theory LF_HLW_Scope
  imports LF_HLW_Fitch
begin

section \<open>A parametrized rule checker\<close>

type_synonym hl_asm_src = "hl_proof \<Rightarrow> int \<Rightarrow> int set \<Rightarrow> int set"

definition hlDepSrc :: hl_asm_src where
  "hlDepSrc P n G = G"

text \<open>Identical to @{const hlRuleOK} except at @{const HL_ForallIntro} and
  @{const HL_ExistsElim}, the only two branches whose side condition
  consults assumption formulas rather than purely citing lines (matching
  @{text ruleOK_indep} in the compact layer). There, the fixed dependency
  argument is replaced by @{term "src P n G"}, evaluated at whichever line's
  position the unparametrized @{const hlRuleOK} already keys its freshness
  check on: for @{const HL_ForallIntro} that is the generalising line \<open>l\<close>
  itself (whose own dependency @{term G} equals the cited premise's, so this
  matches the compact layer's @{text "A E (lineNumber l) G"} exactly); for
  @{const HL_ExistsElim} it is the witness subproof's own conclusion line
  \<open>lc\<close>, which is what @{const hlRuleOK}'s existing @{term delta} already keys
  on (its structural @{term G} additionally unions in the cited premise's
  dependency, which @{const hlRuleOK} does not fold into the freshness check
  either --- preserved here rather than silently changed).\<close>

definition hlRuleOKG :: "hl_asm_src \<Rightarrow> hl_proof \<Rightarrow> hl_line \<Rightarrow> bool" where
  "hlRuleOKG src P l \<longleftrightarrow>
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
                               c \<notin> hlAssumptionConstants P (src P (hlLineNumber l) G)) \<and>
                            G = hlReferences lm)
                    | None \<Rightarrow> False))
           | None \<Rightarrow> False)
      | HL_ExistsElim m a c \<Rightarrow>
          (case (hlLookupLine P m,hlLookupLine P a,hlLookupLine P c) of
             (Some lm,Some la,Some lc) \<Rightarrow>
               (let (sourceVars,sourceCore) = hlCollectExists (hlFormula lm);
                    (targetVars,targetCore) = hlCollectExists (hlFormula la);
                    delta = hlReferences lc - {hlLineNumber la};
                    deltaSrc = src P (hlLineNumber lc) (hlReferences lc) - {hlLineNumber la}
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
                                        w \<notin> hlReferencedConstants P deltaSrc) \<and>
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

lemma hlRuleOKG_hlDepSrc: "hlRuleOKG hlDepSrc P l = hlRuleOK P l"
  by (cases "hlJustification l")
     (auto simp: hlRuleOKG_def hlRuleOK_def hlDepSrc_def Let_def
       split: option.splits hl_formula.splits hl_term.splits prod.splits)

section \<open>The generic checker\<close>

definition hlLineOKG :: "hl_asm_src \<Rightarrow> hl_proof \<Rightarrow> hl_line \<Rightarrow> bool" where
  "hlLineOKG src P l \<longleftrightarrow> hlStructureOK P l \<and> hlRuleOKG src P l"

definition hlCorrectG :: "hl_asm_src \<Rightarrow> hl_proof \<Rightarrow> bool" where
  "hlCorrectG src P \<longleftrightarrow> list_all (hlLineOKG src P) P"

lemma hlLineOKG_hlDepSrc: "hlLineOKG hlDepSrc P l = hlLineOK P l"
  by (simp add: hlLineOKG_def hlLineOK_def hlRuleOKG_hlDepSrc)

lemma hlCorrectG_hlDepSrc: "hlCorrectG hlDepSrc P = hlCorrect P"
  by (simp add: hlCorrectG_def hlCorrect_def list_all_iff hlLineOKG_hlDepSrc)

section \<open>Assumptions in genuine Fitch scope\<close>

fun hlFitchPremiseNumbers :: "hl_fitch_proof \<Rightarrow> int list" where
  "hlFitchPremiseNumbers [] = []"
| "hlFitchPremiseNumbers (HL_FLine n p r # rest) =
     (if r = HL_FPremise then n # hlFitchPremiseNumbers rest
      else hlFitchPremiseNumbers rest)"
| "hlFitchPremiseNumbers (HL_FSub s # rest) = hlFitchPremiseNumbers rest"

fun hlFitchScopeRecord ::
    "int set \<Rightarrow> hl_fitch_proof \<Rightarrow> (int \<times> int set) list" where
  "hlFitchScopeRecord scope [] = []"
| "hlFitchScopeRecord scope (HL_FLine n p r # rest) =
     (n,scope) # hlFitchScopeRecord scope rest"
| "hlFitchScopeRecord scope (HL_FSub (HL_Subproof a p body) # rest) =
     (a,insert a scope) # hlFitchScopeRecord (insert a scope) body @
       hlFitchScopeRecord scope rest"

text \<open>Definition 19 makes the root assumptions available throughout the
  proof, together with the heads of the enclosing boxes. Earlier derived
  lines and closed sibling boxes contribute no assumptions to this scope.\<close>

definition hlFitchScopeOf :: "hl_fitch_proof \<Rightarrow> int \<Rightarrow> int set" where
  "hlFitchScopeOf F n =
     (case map_of (hlFitchScopeRecord (set (hlFitchPremiseNumbers F)) F) n of
        None \<Rightarrow> {} | Some scope \<Rightarrow> scope)"

definition hlScopeSrc :: "hl_fitch_proof \<Rightarrow> hl_asm_src" where
  "hlScopeSrc F P n G = hlFitchScopeOf F n"

section \<open>Fitch correctness\<close>

text \<open>The dependency-based erasure check and the scope-based
  eigenconstant check have different jobs. Both are required, alongside
  verified nesting and the sequent boundary check. The Haskell correspondence
  predicate @{const hlFitchWellFormed} is left unchanged.\<close>

definition hlFitchCorrect :: "hl_fitch_proof \<Rightarrow> bool" where
  "hlFitchCorrect F \<longleftrightarrow>
     hlFitchVerified F \<and> hlCorrectG (hlScopeSrc F) (\<delta>\<^sub>H F)"

lemma hlFitchCorrect_verified:
  "hlFitchCorrect F \<Longrightarrow> hlFitchVerified F"
  by (simp add: hlFitchCorrect_def)

lemma hlFitchCorrect_delta_verified:
  "hlFitchCorrect F \<Longrightarrow> hlVerifiedCorrect (\<delta>\<^sub>H F)"
  by (simp add: hlFitchCorrect_def hlFitchVerified_def)

lemma hlOpenAssumptionFitch_not_hlFitchCorrect:
  "\<not> hlFitchCorrect hlOpenAssumptionFitch"
  by eval

lemma hlOpenAssumptionFitch_fails_only_root_scope:
  "hlFitchWellFormed hlOpenAssumptionFitch"
  "hlCorrectG (hlScopeSrc hlOpenAssumptionFitch) (\<delta>\<^sub>H hlOpenAssumptionFitch)"
  "\<not> hlConcludesAtTop hlOpenAssumptionFitch"
  by eval+

end
