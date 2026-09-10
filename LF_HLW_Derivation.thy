theory LF_HLW_Derivation
  imports LF_HLW_Unfold
begin

section \<open>Children and open assumptions of exact derivation trees\<close>

fun hlSubDerivations :: "hl_derivation_rule \<Rightarrow> hl_derivation list" where
  "hlSubDerivations (HL_DAssume i) = []"
| "hlSubDerivations (HL_DPremise i) = []"
| "hlSubDerivations (HL_DMP d e) = [d,e]"
| "hlSubDerivations (HL_DMT d e) = [d,e]"
| "hlSubDerivations (HL_DDN d) = [d]"
| "hlSubDerivations (HL_DCP a f d) = [d]"
| "hlSubDerivations (HL_DAndI d e) = [d,e]"
| "hlSubDerivations (HL_DAndE d) = [d]"
| "hlSubDerivations (HL_DOrI d) = [d]"
| "hlSubDerivations (HL_DOrE d a f e b g h) = [d,e,h]"
| "hlSubDerivations (HL_DRAA a f d) = [d]"
| "hlSubDerivations (HL_DForallE d) = [d]"
| "hlSubDerivations (HL_DForallI d) = [d]"
| "hlSubDerivations (HL_DExistsI d) = [d]"
| "hlSubDerivations (HL_DExistsE d a f e) = [d,e]"
| "hlSubDerivations HL_DEqI = []"
| "hlSubDerivations (HL_DEqE d e) = [d,e]"
| "hlSubDerivations HL_DLEM = []"
| "hlSubDerivations (HL_DPropTaut ds) = ds"
| "hlSubDerivations (HL_DIffI d e) = [d,e]"
| "hlSubDerivations (HL_DIffE d e) = [d,e]"
| "hlSubDerivations (HL_DQN d) = [d]"

lemma hlSubDerivations_size [termination_simp]:
  "d \<in> set (hlSubDerivations r) \<Longrightarrow> size d < size r"
  by (cases r) (auto intro: le_imp_less_Suc size_list_estimation')

abbreviation hlDropAssumption ::
  "int \<Rightarrow> (int \<times> hl_formula) list \<Rightarrow> (int \<times> hl_formula) list" where
  "hlDropAssumption a G \<equiv> filter (\<lambda>nf. fst nf \<noteq> a) G"

fun hlOpenAssumptions :: "hl_derivation \<Rightarrow> (int \<times> hl_formula) list" where
  "hlOpenAssumptions (HL_Derivation f (HL_DAssume n)) = [(n,f)]"
| "hlOpenAssumptions (HL_Derivation f (HL_DPremise n)) = [(n,f)]"
| "hlOpenAssumptions (HL_Derivation f (HL_DCP a p d)) =
     hlDropAssumption a (hlOpenAssumptions d)"
| "hlOpenAssumptions (HL_Derivation f (HL_DRAA a p d)) =
     hlDropAssumption a (hlOpenAssumptions d)"
| "hlOpenAssumptions (HL_Derivation f (HL_DOrE d a p e b q h)) =
     hlOpenAssumptions d @ hlDropAssumption a (hlOpenAssumptions e) @
       hlDropAssumption b (hlOpenAssumptions h)"
| "hlOpenAssumptions (HL_Derivation f (HL_DExistsE d a p e)) =
     hlOpenAssumptions d @ hlDropAssumption a (hlOpenAssumptions e)"
| "hlOpenAssumptions (HL_Derivation f r) =
     concat (map hlOpenAssumptions (hlSubDerivations r))"

abbreviation hlOpenFormulas :: "hl_derivation \<Rightarrow> hl_formula list" where
  "hlOpenFormulas d \<equiv> map snd (hlOpenAssumptions d)"

definition hlDischargeOK :: "int \<Rightarrow> hl_formula \<Rightarrow> hl_derivation \<Rightarrow> bool" where
  "hlDischargeOK a f d \<longleftrightarrow>
     (\<forall>nf \<in> set (hlOpenAssumptions d). fst nf = a \<longrightarrow> snd nf = f)"

section \<open>The exact quantifier side conditions on formulas\<close>

definition hlForallElimStep :: "hl_formula \<Rightarrow> hl_formula \<Rightarrow> bool" where
  "hlForallElimStep source goal \<longleftrightarrow>
     (let (xs,p) = hlCollectForalls source;
          (ys,q) = hlCollectForalls goal
      in case hlEliminationCount xs ys of
           Some k \<Rightarrow> hlInferWitnessConstsK xs p k q \<noteq> None
         | None \<Rightarrow> False)"

definition hlExistsIntroStep :: "hl_formula \<Rightarrow> hl_formula \<Rightarrow> bool" where
  "hlExistsIntroStep source goal \<longleftrightarrow>
     (let (xs,p) = hlCollectExists goal
      in xs \<noteq> [] \<and>
         list_ex (\<lambda>k.
           hlInferWitnessConstsK xs (hlPrefixExists (drop k xs) p) k source \<noteq> None)
           [0..<Suc (length xs)])"

definition hlForallIntroStep ::
  "hl_formula \<Rightarrow> hl_formula \<Rightarrow> hl_formula list \<Rightarrow> bool" where
  "hlForallIntroStep source goal G \<longleftrightarrow>
     (let (xs,p) = hlCollectForalls goal
      in xs \<noteq> [] \<and>
         (case hlInferWitnessConstsK xs p (length xs) source of
            Some cs \<Rightarrow>
              (let pairs = filter (\<lambda>xc. snd xc \<noteq> STR '''') (zip xs cs)
               in hlAbstractMany pairs source = Some p \<and>
                  (\<forall>c \<in> snd ` set pairs. c \<notin> hlConstantsInScope G))
          | None \<Rightarrow> False))"

definition hlExistsElimStep ::
  "hl_formula \<Rightarrow> hl_formula \<Rightarrow> hl_formula \<Rightarrow>
    hl_formula list \<Rightarrow> bool" where
  "hlExistsElimStep source assumption goal G \<longleftrightarrow>
     (let (xs,p) = hlCollectExists source;
          (ys,q) = hlCollectExists assumption
      in xs \<noteq> [] \<and>
         (case hlEliminationCount xs ys of
            Some k \<Rightarrow>
              (let template = hlPrefixExists ys p
               in case hlInferWitnessConstsK xs template k assumption of
                    Some cs \<Rightarrow>
                      (let pairs = filter (\<lambda>xc. snd xc \<noteq> STR '''')
                                     (zip (take k xs) cs)
                       in hlAbstractMany pairs assumption = Some template \<and>
                          (\<forall>w \<in> snd ` set pairs.
                             w \<notin> hlConstantsInFormula goal \<and>
                             w \<notin> hlConstantsInScope G))
                  | None \<Rightarrow> False)
          | None \<Rightarrow> False))"

lemma hlConstantsInScope_mono:
  "set G \<subseteq> set H \<Longrightarrow> hlConstantsInScope G \<subseteq> hlConstantsInScope H"
  by (auto simp: hlConstantsInScope_def)

lemma hlForallIntroStep_antitone:
  "hlForallIntroStep p q H \<Longrightarrow> set G \<subseteq> set H \<Longrightarrow>
   hlForallIntroStep p q G"
  unfolding hlForallIntroStep_def
  using hlConstantsInScope_mono[of G H]
  by (auto simp: Let_def split: prod.splits option.splits)

lemma hlExistsElimStep_antitone:
  "hlExistsElimStep p a q H \<Longrightarrow> set G \<subseteq> set H \<Longrightarrow>
   hlExistsElimStep p a q G"
  unfolding hlExistsElimStep_def
  using hlConstantsInScope_mono[of G H]
  by (auto simp: Let_def split: prod.splits option.splits)

section \<open>Correctness of exact derivation trees\<close>

text \<open>These are the supplied twenty-one rule patterns on child formulas.
  Both leaf tags have the same local meaning; ancestor classification decides
  which leaves become root premises. Discharge checks also enforce agreement
  between each discharged label and every leaf carrying it. The existential
  freshness condition follows the supplied checker and ranges over the body's
  remaining assumptions, rather than adding source dependencies silently.\<close>

fun hlDerivationOK :: "hl_derivation \<Rightarrow> bool" where
  "hlDerivationOK (HL_Derivation f (HL_DAssume n)) = True"
| "hlDerivationOK (HL_Derivation f (HL_DPremise n)) = True"
| "hlDerivationOK (HL_Derivation f (HL_DMP d e)) =
     (hlDerivationOK d \<and> hlDerivationOK e \<and>
      hlDerivationFormula d = HL_Implies (hlDerivationFormula e) f)"
| "hlDerivationOK (HL_Derivation f (HL_DMT d e)) =
     (hlDerivationOK d \<and> hlDerivationOK e \<and>
      (case (hlDerivationFormula d,hlDerivationFormula e,f) of
         (HL_Implies p q,HL_Not r,HL_Not s) \<Rightarrow> p = s \<and> q = r
       | _ \<Rightarrow> False))"
| "hlDerivationOK (HL_Derivation f (HL_DDN d)) =
     (hlDerivationOK d \<and>
      (hlDerivationFormula d = HL_Not (HL_Not f) \<or>
       f = HL_Not (HL_Not (hlDerivationFormula d))))"
| "hlDerivationOK (HL_Derivation f (HL_DCP a p d)) =
     (hlDerivationOK d \<and> hlDischargeOK a p d \<and>
      f = HL_Implies p (hlDerivationFormula d))"
| "hlDerivationOK (HL_Derivation f (HL_DAndI d e)) =
     (hlDerivationOK d \<and> hlDerivationOK e \<and>
      (f = HL_And (hlDerivationFormula d) (hlDerivationFormula e) \<or>
       f = HL_And (hlDerivationFormula e) (hlDerivationFormula d)))"
| "hlDerivationOK (HL_Derivation f (HL_DAndE d)) =
     (hlDerivationOK d \<and>
      (case hlDerivationFormula d of HL_And p q \<Rightarrow> f = p \<or> f = q
       | _ \<Rightarrow> False))"
| "hlDerivationOK (HL_Derivation f (HL_DOrI d)) =
     (hlDerivationOK d \<and>
      (case f of HL_Or p q \<Rightarrow> hlDerivationFormula d = p \<or> hlDerivationFormula d = q
       | _ \<Rightarrow> False))"
| "hlDerivationOK (HL_Derivation f (HL_DOrE d a p e b q h)) =
     (hlDerivationOK d \<and> hlDerivationOK e \<and> hlDerivationOK h \<and>
      hlDischargeOK a p e \<and> hlDischargeOK b q h \<and>
      hlDerivationFormula e = f \<and> hlDerivationFormula h = f \<and>
      (hlDerivationFormula d = HL_Or p q \<or> hlDerivationFormula d = HL_Or q p))"
| "hlDerivationOK (HL_Derivation f (HL_DRAA a p d)) =
     (hlDerivationOK d \<and> hlDischargeOK a p d \<and>
      f = HL_Not p \<and> hlContradiction (hlDerivationFormula d))"
| "hlDerivationOK (HL_Derivation f (HL_DForallE d)) =
     (hlDerivationOK d \<and> hlForallElimStep (hlDerivationFormula d) f)"
| "hlDerivationOK (HL_Derivation f (HL_DForallI d)) =
     (hlDerivationOK d \<and> hlForallIntroStep (hlDerivationFormula d) f (hlOpenFormulas d))"
| "hlDerivationOK (HL_Derivation f (HL_DExistsI d)) =
     (hlDerivationOK d \<and> hlExistsIntroStep (hlDerivationFormula d) f)"
| "hlDerivationOK (HL_Derivation f (HL_DExistsE d a p e)) =
     (hlDerivationOK d \<and> hlDerivationOK e \<and> hlDischargeOK a p e \<and>
      hlDerivationFormula e = f \<and>
      hlExistsElimStep (hlDerivationFormula d) p f
        (map snd (hlDropAssumption a (hlOpenAssumptions e))))"
| "hlDerivationOK (HL_Derivation f HL_DEqI) =
     (case f of HL_Predicate E [HL_Const a,HL_Const b] \<Rightarrow> E = STR ''='' \<and> a = b
      | _ \<Rightarrow> False)"
| "hlDerivationOK (HL_Derivation f (HL_DEqE d e)) =
     (hlDerivationOK d \<and> hlDerivationOK e \<and>
      (case hlEqualityFormula (hlDerivationFormula e) of
         Some (HL_Const a,HL_Const b) \<Rightarrow>
           hlEqualUpToConstantReplacement a b (hlDerivationFormula d) f
       | _ \<Rightarrow> False))"
| "hlDerivationOK (HL_Derivation f HL_DLEM) = hlExcludedMiddle f"
| "hlDerivationOK (HL_Derivation f (HL_DPropTaut ds)) =
     (list_all hlDerivationOK ds \<and>
      hlPropositionalConsequence (map hlDerivationFormula ds) f)"
| "hlDerivationOK (HL_Derivation f (HL_DIffI d e)) =
     (hlDerivationOK d \<and> hlDerivationOK e \<and>
      (case (hlDerivationFormula d,hlDerivationFormula e,f) of
         (HL_Implies p q,HL_Implies r s,HL_Iff u v) \<Rightarrow>
           p = s \<and> q = r \<and> ((u = p \<and> v = q) \<or> (u = q \<and> v = p))
       | _ \<Rightarrow> False))"
| "hlDerivationOK (HL_Derivation f (HL_DIffE d e)) =
     (hlDerivationOK d \<and> hlDerivationOK e \<and>
      (case hlDerivationFormula d of
         HL_Iff p q \<Rightarrow>
           (hlDerivationFormula e = p \<and> f = q) \<or>
           (hlDerivationFormula e = q \<and> f = p)
       | _ \<Rightarrow> False))"
| "hlDerivationOK (HL_Derivation f (HL_DQN d)) =
     (hlDerivationOK d \<and> hlQuantifierNegationEquivalent (hlDerivationFormula d) f)"

section \<open>Ancestor classification preserves the derivation\<close>

lemma hlClassifyAssumptions_root [simp]:
  "hlDerivationFormula (hlClassifyAssumptions bound d) = hlDerivationFormula d"
  by (cases d) simp

lemma hlClassifyAssumptions_open [simp]:
  "hlOpenAssumptions (hlClassifyAssumptions bound d) = hlOpenAssumptions d"
  by (induction d arbitrary: bound rule: hlOpenAssumptions.induct)
     (auto simp: map_map comp_def split: if_splits
       intro!: arg_cong[where f=concat] map_cong)

lemma hlClassifyAssumptions_discharge [simp]:
  "hlDischargeOK a f (hlClassifyAssumptions bound d) = hlDischargeOK a f d"
  by (simp add: hlDischargeOK_def)

lemma hlClassifyAssumptions_OK [simp]:
  "hlDerivationOK (hlClassifyAssumptions bound d) = hlDerivationOK d"
  apply (induction d arbitrary: bound rule: hlDerivationOK.induct)
  apply (auto simp: list_all_iff map_map comp_def split: if_splits)
  apply (simp_all only: hlClassifyAssumptions_root
    cong: hl_formula.case_cong hl_term.case_cong option.case_cong)
  done

lemma hlClassifyAssumptions_premises:
  "set (hlPremisesOf (hlClassifyAssumptions bound d)) =
   {nf \<in> set (hlOpenAssumptions d). fst nf \<notin> bound}"
  by (induction d arbitrary: bound rule: hlOpenAssumptions.induct)
     (auto simp: map_map comp_def split: if_splits)

corollary hlClassifyAssumptions_root_premises:
  "set (hlPremisesOf (hlClassifyAssumptions {} d)) = set (hlOpenAssumptions d)"
  by (simp add: hlClassifyAssumptions_premises)

end
