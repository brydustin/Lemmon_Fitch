(* T2: what the erasure delta_H makes of an emitted Fitch proof. *)

theory LF_HLW_Erasure
  imports LF_HLW_Nesting
begin

section \<open>The erasure preserves the flattened shape\<close>

lemma hlFlattenFitch_numbers:
  "map fst (hlFlattenFitch F) = hlFitchLineNumbers F"
  "map fst (hlFlattenFitchItem i) = hlFitchItemLineNumbers i"
  by (induction F and i rule: hlFlattenFitch_hlFlattenFitchItem.induct) auto

lemma hlFitchToLemmonFrom_numbers:
  "map hlLineNumber (snd (hlFitchToLemmonFrom env ls)) = map fst ls"
  by (induction ls arbitrary: env)
     (auto simp: Let_def case_prod_beta split: prod.splits)

lemma hlFitchToLemmonFrom_justifications:
  "map hlJustification (snd (hlFitchToLemmonFrom env ls)) =
   map (\<lambda>t. hlToLemmonRule (snd (snd t))) ls"
  by (induction ls arbitrary: env)
     (auto simp: Let_def case_prod_beta split: prod.splits)

lemma hlFitchToLemmon_numbers:
  "map hlLineNumber (hlFitchToLemmon F) = hlFitchLineNumbers F"
  by (simp add: hlFitchToLemmon_def hlFitchToLemmonFrom_numbers hlFlattenFitch_numbers)

lemma hlFitchToLemmon_justifications:
  "map hlJustification (hlFitchToLemmon F) =
   map (\<lambda>t. hlToLemmonRule (snd (snd t))) (hlFlattenFitch F)"
  by (simp add: hlFitchToLemmon_def hlFitchToLemmonFrom_justifications)

section \<open>Canonical order\<close>

text \<open>The erasure renumbers nothing, so the emitter's allocation invariant is
  already the Lemmon-side order condition.\<close>

lemma hlFitchToLemmon_canonicalOrder:
  assumes "list_all (\<lambda>n. 0 < n) (hlFitchLineNumbers F)"
      and "sorted_wrt (<) (hlFitchLineNumbers F)"
  shows "hlCanonicalOrder (hlFitchToLemmon F)"
  using assms by (simp add: hlCanonicalOrder_def hlFitchToLemmon_numbers)

theorem hlClassifiedDerivationToFitch_canonicalOrder:
  "hlCanonicalOrder (\<delta>\<^sub>H (hlDerivationToFitch (hlClassifyAssumptions {} d)))"
  using hlDerivationToFitch_positive_sorted[of "hlClassifyAssumptions {} d"]
  by (simp add: hlFitchToLemmon_canonicalOrder)

section \<open>Dependency closure\<close>

text \<open>Every dependency set the erasure computes is built from lookups that
  bottom out at the \<open>{self}\<close> of a premise or assumption line, so it can only
  ever contain numbers of lines the Lemmon side calls \<^const>\<open>HL_Assumption\<close>.\<close>

lemma hlDependencyLookup_subset:
  "\<forall>q \<in> set env. snd q \<subseteq> A \<Longrightarrow> hlDependencyLookup env n \<subseteq> A"
  by (induction env) (auto split: if_splits)

lemma hlFitchDependenciesOf_subset:
  assumes look: "\<And>n. look n \<subseteq> A"
      and self: "r = HL_FPremise \<or> r = HL_FAssume \<Longrightarrow> s \<in> A"
  shows "hlFitchDependenciesOf look r s \<subseteq> A"
  using assms
  by (cases r) (auto simp: hlFitchDependenciesOf_def)

lemma hlFitchToLemmonFrom_dependencies:
  assumes "\<forall>q \<in> set env. snd q \<subseteq> A"
      and "\<forall>t \<in> set ls.
             (snd (snd t) = HL_FPremise \<or> snd (snd t) = HL_FAssume) \<longrightarrow> fst t \<in> A"
  shows "(\<forall>l \<in> set (snd (hlFitchToLemmonFrom env ls)). hlReferences l \<subseteq> A) \<and>
         (\<forall>q \<in> set (fst (hlFitchToLemmonFrom env ls)). snd q \<subseteq> A)"
  using assms
proof (induction ls arbitrary: env)
  case Nil
  then show ?case by simp
next
  case (Cons t ls)
  obtain n p r where t: "t = (n,p,r)" by (cases t) auto
  let ?G = "hlFitchDependenciesOf (hlDependencyLookup env) r n"
  have G: "?G \<subseteq> A"
    by (rule hlFitchDependenciesOf_subset)
       (use Cons.prems t hlDependencyLookup_subset[of env A] in auto)
  have env': "\<forall>q \<in> set ((n,?G) # env). snd q \<subseteq> A" using G Cons.prems(1) by auto
  have rest: "\<forall>u \<in> set ls.
      (snd (snd u) = HL_FPremise \<or> snd (snd u) = HL_FAssume) \<longrightarrow> fst u \<in> A"
    using Cons.prems(2) by auto
  from Cons.IH[OF env' rest] show ?case
    using G t by (auto simp: Let_def case_prod_beta split: prod.splits)
qed

text \<open>The Lemmon-side assumption lines of an erased proof are exactly the
  flattened premise and box-assumption lines: no other Fitch rule is sent to
  \<^const>\<open>HL_Assumption\<close> by \<^const>\<open>hlToLemmonRule\<close>.\<close>

definition hlFitchAssumptionNumbers :: "hl_fitch_proof \<Rightarrow> int set" where
  "hlFitchAssumptionNumbers F =
     fst ` {t \<in> set (hlFlattenFitch F).
              snd (snd t) = HL_FPremise \<or> snd (snd t) = HL_FAssume}"

lemma hlToLemmonRule_Assumption_iff:
  "hlToLemmonRule r = HL_Assumption \<longleftrightarrow> r = HL_FPremise \<or> r = HL_FAssume"
  by (cases r) auto

lemma hlFitchToLemmonFrom_lines:
  "map (\<lambda>l. (hlLineNumber l, hlJustification l)) (snd (hlFitchToLemmonFrom env ls))
   = map (\<lambda>t. (fst t, hlToLemmonRule (snd (snd t)))) ls"
  by (induction ls arbitrary: env)
     (auto simp: Let_def case_prod_beta split: prod.splits)

lemma hlFitchToLemmon_assumptions:
  "hlLineNumber ` {a \<in> set (\<delta>\<^sub>H F). hlJustification a = HL_Assumption} =
   hlFitchAssumptionNumbers F"
proof -
  have eq: "map (\<lambda>l. (hlLineNumber l, hlJustification l)) (\<delta>\<^sub>H F)
          = map (\<lambda>t. (fst t, hlToLemmonRule (snd (snd t)))) (hlFlattenFitch F)"
    unfolding hlFitchToLemmon_def by (rule hlFitchToLemmonFrom_lines)
  have "hlLineNumber ` {a \<in> set (\<delta>\<^sub>H F). hlJustification a = HL_Assumption}
      = fst ` {q \<in> set (map (\<lambda>l. (hlLineNumber l, hlJustification l)) (\<delta>\<^sub>H F)).
               snd q = HL_Assumption}"
    by force
  also have "\<dots> = fst ` {q \<in> set (map (\<lambda>t. (fst t, hlToLemmonRule (snd (snd t))))
                                   (hlFlattenFitch F)). snd q = HL_Assumption}"
    by (simp only: eq)
  also have "\<dots> = hlFitchAssumptionNumbers F"
    unfolding hlFitchAssumptionNumbers_def
    by (force simp: hlToLemmonRule_Assumption_iff)
  finally show ?thesis .
qed

theorem hlFitchToLemmon_dependencyClosed:
  "hlDependencyClosed (\<delta>\<^sub>H F)"
  unfolding hlDependencyClosed_def hlFitchToLemmon_assumptions
  using hlFitchToLemmonFrom_dependencies
          [of "[]" "hlFitchAssumptionNumbers F" "hlFlattenFitch F"]
  by (auto simp: hlFitchToLemmon_def hlFitchAssumptionNumbers_def)

end
