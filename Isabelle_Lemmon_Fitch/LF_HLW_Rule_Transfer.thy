(* Local transfer principles for all twenty-one authoritative HL rules. *)

theory LF_HLW_Rule_Transfer
  imports LF_HLW_Scope
begin

declare hlEqualUpToConstantReplacement.simps [simp del]

section \<open>The dependency component of rule checking\<close>

definition hlRuleReferencesAt :: "hl_proof \<Rightarrow> int \<Rightarrow> int set" where
  "hlRuleReferencesAt P n = (case hlReferencesAt P n of None \<Rightarrow> {} | Some G \<Rightarrow> G)"

fun hlExpectedReferences :: "hl_proof \<Rightarrow> int \<Rightarrow> hl_justification \<Rightarrow> int set" where
  "hlExpectedReferences P n HL_Assumption = {n}"
| "hlExpectedReferences P n (HL_CP a c) = hlRuleReferencesAt P c - {a}"
| "hlExpectedReferences P n (HL_RAA a c) = hlRuleReferencesAt P c - {a}"
| "hlExpectedReferences P n (HL_OrElim d a1 c1 a2 c2) =
     hlRuleReferencesAt P d \<union> (hlRuleReferencesAt P c1 - {a1}) \<union>
       (hlRuleReferencesAt P c2 - {a2})"
| "hlExpectedReferences P n (HL_ExistsElim m a c) =
     hlRuleReferencesAt P m \<union> (hlRuleReferencesAt P c - {a})"
| "hlExpectedReferences P n j = hlReferenceUnion P (hlCitedLines j)"

definition hlRuleDependenciesCorrect :: "hl_proof \<Rightarrow> hl_line \<Rightarrow> bool" where
  "hlRuleDependenciesCorrect P l \<longleftrightarrow>
     hlJustification l = HL_LEM \<or>
     hlReferences l = hlExpectedReferences P (hlLineNumber l) (hlJustification l)"

lemma hlRuleLookup_number:
  "hlLookupLine P n = Some l \<Longrightarrow> hlLineNumber l = n"
  by (induction P) (auto split: if_splits)

lemma hlRuleOKG_cited_exists:
  assumes "hlRuleOKG src P l" "m \<in> set (hlCitedLines (hlJustification l))"
  shows "hlLookupLine P m \<noteq> None"
proof (rule ccontr)
  assume "\<not> ?thesis"
  then have missing: "hlLookupLine P m = None" by simp
  from assms missing show False
    by (cases "hlJustification l";
        force simp: hlRuleOKG_def Let_def list_all_iff split: option.splits)
qed

lemma hlRuleReferenceUnion_Nil [simp]: "hlReferenceUnion P [] = {}"
  by (simp add: hlReferenceUnion_def)

lemma hlRuleReferenceUnion_Cons [simp]:
  "hlReferenceUnion P (n # ns) = hlRuleReferencesAt P n \<union> hlReferenceUnion P ns"
  by (simp add: hlReferenceUnion_def hlRuleReferencesAt_def split: option.splits)

lemma hlRuleReferencesAt_lookup [simp]:
  "hlLookupLine P n = Some l \<Longrightarrow> hlRuleReferencesAt P n = hlReferences l"
  by (simp add: hlRuleReferencesAt_def hlReferencesAt_def)

lemma hlRuleOKG_dependencies:
  assumes accepted: "hlRuleOKG src P l"
  shows "hlRuleDependenciesCorrect P l"
proof (cases "hlJustification l")
  case HL_Assumption
  from accepted  show ?thesis
    by (auto simp: hlRuleOKG_def HL_Assumption 
        hlRuleDependenciesCorrect_def Let_def
        split: hl_formula.splits hl_term.splits option.splits prod.splits)
next
  case (HL_MP m k)
  obtain lm where lm: "hlLookupLine P m = Some lm"
    using hlRuleOKG_cited_exists[OF accepted, of m] HL_MP by auto
  obtain lk where lk: "hlLookupLine P k = Some lk"
    using hlRuleOKG_cited_exists[OF accepted, of k] HL_MP by auto
  from accepted hlRuleLookup_number[OF lm] hlRuleLookup_number[OF lk] show ?thesis
    by (auto simp: hlRuleOKG_def HL_MP lm lk
        hlRuleDependenciesCorrect_def Let_def
        split: hl_formula.splits hl_term.splits option.splits prod.splits)
next
  case (HL_MT m k)
  obtain lm where lm: "hlLookupLine P m = Some lm"
    using hlRuleOKG_cited_exists[OF accepted, of m] HL_MT by auto
  obtain lk where lk: "hlLookupLine P k = Some lk"
    using hlRuleOKG_cited_exists[OF accepted, of k] HL_MT by auto
  from accepted hlRuleLookup_number[OF lm] hlRuleLookup_number[OF lk] show ?thesis
    by (auto simp: hlRuleOKG_def HL_MT lm lk
        hlRuleDependenciesCorrect_def Let_def
        split: hl_formula.splits hl_term.splits option.splits prod.splits)
next
  case (HL_DN m)
  obtain lm where lm: "hlLookupLine P m = Some lm"
    using hlRuleOKG_cited_exists[OF accepted, of m] HL_DN by auto
  from accepted hlRuleLookup_number[OF lm] show ?thesis
    by (auto simp: hlRuleOKG_def HL_DN lm
        hlRuleDependenciesCorrect_def Let_def
        split: hl_formula.splits hl_term.splits option.splits prod.splits)
next
  case (HL_CP a c)
  obtain la where la: "hlLookupLine P a = Some la"
    using hlRuleOKG_cited_exists[OF accepted, of a] HL_CP by auto
  obtain lc where lc: "hlLookupLine P c = Some lc"
    using hlRuleOKG_cited_exists[OF accepted, of c] HL_CP by auto
  from accepted hlRuleLookup_number[OF la] hlRuleLookup_number[OF lc] show ?thesis
    by (auto simp: hlRuleOKG_def HL_CP la lc
        hlRuleDependenciesCorrect_def Let_def
        split: hl_formula.splits hl_term.splits option.splits prod.splits)
next
  case (HL_AndIntro m k)
  obtain lm where lm: "hlLookupLine P m = Some lm"
    using hlRuleOKG_cited_exists[OF accepted, of m] HL_AndIntro by auto
  obtain lk where lk: "hlLookupLine P k = Some lk"
    using hlRuleOKG_cited_exists[OF accepted, of k] HL_AndIntro by auto
  from accepted hlRuleLookup_number[OF lm] hlRuleLookup_number[OF lk] show ?thesis
    by (auto simp: hlRuleOKG_def HL_AndIntro lm lk
        hlRuleDependenciesCorrect_def Let_def
        split: hl_formula.splits hl_term.splits option.splits prod.splits)
next
  case (HL_AndElim m)
  obtain lm where lm: "hlLookupLine P m = Some lm"
    using hlRuleOKG_cited_exists[OF accepted, of m] HL_AndElim by auto
  from accepted hlRuleLookup_number[OF lm] show ?thesis
    by (auto simp: hlRuleOKG_def HL_AndElim lm
        hlRuleDependenciesCorrect_def Let_def
        split: hl_formula.splits hl_term.splits option.splits prod.splits)
next
  case (HL_OrIntro m)
  obtain lm where lm: "hlLookupLine P m = Some lm"
    using hlRuleOKG_cited_exists[OF accepted, of m] HL_OrIntro by auto
  from accepted hlRuleLookup_number[OF lm] show ?thesis
    by (auto simp: hlRuleOKG_def HL_OrIntro lm
        hlRuleDependenciesCorrect_def Let_def
        split: hl_formula.splits hl_term.splits option.splits prod.splits)
next
  case (HL_OrElim m a c b e)
  obtain lm where lm: "hlLookupLine P m = Some lm"
    using hlRuleOKG_cited_exists[OF accepted, of m] HL_OrElim by auto
  obtain la where la: "hlLookupLine P a = Some la"
    using hlRuleOKG_cited_exists[OF accepted, of a] HL_OrElim by auto
  obtain lc where lc: "hlLookupLine P c = Some lc"
    using hlRuleOKG_cited_exists[OF accepted, of c] HL_OrElim by auto
  obtain lb where lb: "hlLookupLine P b = Some lb"
    using hlRuleOKG_cited_exists[OF accepted, of b] HL_OrElim by auto
  obtain le where le: "hlLookupLine P e = Some le"
    using hlRuleOKG_cited_exists[OF accepted, of e] HL_OrElim by auto
  from accepted hlRuleLookup_number[OF lm] hlRuleLookup_number[OF la] hlRuleLookup_number[OF lc] hlRuleLookup_number[OF lb] hlRuleLookup_number[OF le] show ?thesis
    by (auto simp: hlRuleOKG_def HL_OrElim lm la lc lb le
        hlRuleDependenciesCorrect_def Let_def
        split: hl_formula.splits hl_term.splits option.splits prod.splits)
next
  case (HL_RAA a c)
  obtain la where la: "hlLookupLine P a = Some la"
    using hlRuleOKG_cited_exists[OF accepted, of a] HL_RAA by auto
  obtain lc where lc: "hlLookupLine P c = Some lc"
    using hlRuleOKG_cited_exists[OF accepted, of c] HL_RAA by auto
  from accepted hlRuleLookup_number[OF la] hlRuleLookup_number[OF lc] show ?thesis
    by (auto simp: hlRuleOKG_def HL_RAA la lc
        hlRuleDependenciesCorrect_def Let_def
        split: hl_formula.splits hl_term.splits option.splits prod.splits)
next
  case (HL_ForallElim m)
  obtain lm where lm: "hlLookupLine P m = Some lm"
    using hlRuleOKG_cited_exists[OF accepted, of m] HL_ForallElim by auto
  from accepted hlRuleLookup_number[OF lm] show ?thesis
    by (auto simp: hlRuleOKG_def HL_ForallElim lm
        hlRuleDependenciesCorrect_def Let_def
        split: hl_formula.splits hl_term.splits option.splits prod.splits)
next
  case (HL_ExistsIntro m)
  obtain lm where lm: "hlLookupLine P m = Some lm"
    using hlRuleOKG_cited_exists[OF accepted, of m] HL_ExistsIntro by auto
  from accepted hlRuleLookup_number[OF lm] show ?thesis
    by (auto simp: hlRuleOKG_def HL_ExistsIntro lm
        hlRuleDependenciesCorrect_def Let_def
        split: hl_formula.splits hl_term.splits option.splits prod.splits)
next
  case (HL_ForallIntro m)
  obtain lm where lm: "hlLookupLine P m = Some lm"
    using hlRuleOKG_cited_exists[OF accepted, of m] HL_ForallIntro by auto
  from accepted hlRuleLookup_number[OF lm] show ?thesis
    by (auto simp: hlRuleOKG_def HL_ForallIntro lm
        hlRuleDependenciesCorrect_def Let_def
        split: hl_formula.splits hl_term.splits option.splits prod.splits)
next
  case (HL_ExistsElim m a c)
  obtain lm where lm: "hlLookupLine P m = Some lm"
    using hlRuleOKG_cited_exists[OF accepted, of m] HL_ExistsElim by auto
  obtain la where la: "hlLookupLine P a = Some la"
    using hlRuleOKG_cited_exists[OF accepted, of a] HL_ExistsElim by auto
  obtain lc where lc: "hlLookupLine P c = Some lc"
    using hlRuleOKG_cited_exists[OF accepted, of c] HL_ExistsElim by auto
  from accepted hlRuleLookup_number[OF lm] hlRuleLookup_number[OF la] hlRuleLookup_number[OF lc] show ?thesis
    by (auto simp: hlRuleOKG_def HL_ExistsElim lm la lc
        hlRuleDependenciesCorrect_def Let_def
        split: hl_formula.splits hl_term.splits option.splits prod.splits)
next
  case HL_EqIntro
  from accepted obtain c where
    "hlFormula l = HL_Predicate (STR ''='') [HL_Const c,HL_Const c]"
    "hlReferences l = {}"
    apply (auto simp: hlRuleOKG_def HL_EqIntro Let_def
        split: hl_formula.splits hl_term.splits list.splits)
    apply (metis hl_term.exhaust list.exhaust)
    done
  then show ?thesis by (simp add: hlRuleDependenciesCorrect_def HL_EqIntro)
next
  case (HL_EqElim m k)
  obtain lm where lm: "hlLookupLine P m = Some lm"
    using hlRuleOKG_cited_exists[OF accepted, of m] HL_EqElim by auto
  obtain lk where lk: "hlLookupLine P k = Some lk"
    using hlRuleOKG_cited_exists[OF accepted, of k] HL_EqElim by auto
  from accepted obtain a b where equality:
    "hlEqualityFormula (hlFormula lk) = Some (HL_Const a,HL_Const b)"
    and refs: "hlReferences l = hlReferences lm \<union> hlReferences lk"
    apply (auto simp: hlRuleOKG_def HL_EqElim lm lk Let_def
        split: option.splits hl_term.splits prod.splits)
    apply (metis hl_term.exhaust)
    done
  from refs show ?thesis
    by (simp add: hlRuleDependenciesCorrect_def HL_EqElim lm lk)
next
  case HL_LEM
  from accepted  show ?thesis
    by (auto simp: hlRuleOKG_def HL_LEM 
        hlRuleDependenciesCorrect_def Let_def
        split: hl_formula.splits hl_term.splits option.splits prod.splits)
next
  case (HL_PropTaut ms)
  from accepted show ?thesis by (simp add: hlRuleOKG_def HL_PropTaut
      hlRuleDependenciesCorrect_def Let_def)
next
  case (HL_IffIntro m k)
  obtain lm where lm: "hlLookupLine P m = Some lm"
    using hlRuleOKG_cited_exists[OF accepted, of m] HL_IffIntro by auto
  obtain lk where lk: "hlLookupLine P k = Some lk"
    using hlRuleOKG_cited_exists[OF accepted, of k] HL_IffIntro by auto
  from accepted hlRuleLookup_number[OF lm] hlRuleLookup_number[OF lk] show ?thesis
    by (auto simp: hlRuleOKG_def HL_IffIntro lm lk
        hlRuleDependenciesCorrect_def Let_def
        split: hl_formula.splits hl_term.splits option.splits prod.splits)
next
  case (HL_IffElim m k)
  obtain lm where lm: "hlLookupLine P m = Some lm"
    using hlRuleOKG_cited_exists[OF accepted, of m] HL_IffElim by auto
  obtain lk where lk: "hlLookupLine P k = Some lk"
    using hlRuleOKG_cited_exists[OF accepted, of k] HL_IffElim by auto
  from accepted hlRuleLookup_number[OF lm] hlRuleLookup_number[OF lk] show ?thesis
    by (auto simp: hlRuleOKG_def HL_IffElim lm lk
        hlRuleDependenciesCorrect_def Let_def
        split: hl_formula.splits hl_term.splits option.splits prod.splits)
next
  case (HL_QN m)
  obtain lm where lm: "hlLookupLine P m = Some lm"
    using hlRuleOKG_cited_exists[OF accepted, of m] HL_QN by auto
  from accepted hlRuleLookup_number[OF lm] show ?thesis
    by (auto simp: hlRuleOKG_def HL_QN lm
        hlRuleDependenciesCorrect_def Let_def
        split: hl_formula.splits hl_term.splits option.splits prod.splits)
qed

theorem hlRuleOK_expectedReferences:
  assumes "hlRuleOK P l" "hlJustification l \<noteq> HL_LEM"
  shows "hlReferences l = hlExpectedReferences P (hlLineNumber l) (hlJustification l)"
  using hlRuleOKG_dependencies[of hlDepSrc P l] assms
  by (simp add: hlRuleOKG_hlDepSrc hlRuleDependenciesCorrect_def)

section \<open>The exact sets inspected by the eigenconstant rules\<close>

definition hlRuleEigenConstants ::
    "hl_asm_src \<Rightarrow> hl_proof \<Rightarrow> hl_line \<Rightarrow> hl_name set" where
  "hlRuleEigenConstants src P l =
    (case hlJustification l of
       HL_ForallIntro m \<Rightarrow>
         hlAssumptionConstants P (src P (hlLineNumber l) (hlReferences l))
     | HL_ExistsElim m a c \<Rightarrow>
         (case (hlLookupLine P a,hlLookupLine P c) of
            (Some la,Some lc) \<Rightarrow>
              hlReferencedConstants P
                (src P (hlLineNumber lc) (hlReferences lc) - {hlLineNumber la})
          | _ \<Rightarrow> {})
     | _ \<Rightarrow> {})"

lemma hlAssumptionConstants_mono:
  "A \<subseteq> B \<Longrightarrow> hlAssumptionConstants P A \<subseteq> hlAssumptionConstants P B"
  by (auto simp: hlAssumptionConstants_def)

lemma hlReferencedConstants_mono:
  "A \<subseteq> B \<Longrightarrow> hlReferencedConstants P A \<subseteq> hlReferencedConstants P B"
  by (auto simp: hlReferencedConstants_def)

theorem hlRuleOKG_eigen_antitone:
  assumes accepted: "hlRuleOKG src P l"
      and smaller: "hlRuleEigenConstants dst P l \<subseteq> hlRuleEigenConstants src P l"
  shows "hlRuleOKG dst P l"
  using assms
  apply (cases "hlJustification l")
  apply (auto simp: hlRuleOKG_def hlRuleEigenConstants_def Let_def
       split: option.splits prod.splits)
  apply blast+
  done

theorem hlRuleOKG_assumption_antitone:
  assumes accepted: "hlRuleOKG src P l"
      and smaller: "\<And>n G. dst P n G \<subseteq> src P n G"
  shows "hlRuleOKG dst P l"
proof (rule hlRuleOKG_eigen_antitone[OF accepted])
  show "hlRuleEigenConstants dst P l \<subseteq> hlRuleEigenConstants src P l"
    using smaller
    by (cases "hlJustification l")
       (auto simp: hlRuleEigenConstants_def
         intro!: hlAssumptionConstants_mono hlReferencedConstants_mono
         split: option.splits)
qed

theorem hlRuleOKG_non_eigen_independent:
  assumes "\<And>m. hlJustification l \<noteq> HL_ForallIntro m"
      and "\<And>m a c. hlJustification l \<noteq> HL_ExistsElim m a c"
  shows "hlRuleOKG src P l = hlRuleOKG dst P l"
  using assms
  apply (cases "hlJustification l")
  apply (simp_all add: hlRuleOKG_def Let_def)
  apply blast+
  done

end
