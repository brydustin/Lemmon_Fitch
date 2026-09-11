(*  Title:      LF_HLW_Translation_Proofs.thy

    General guarantees for the authoritative HL citation-DAG unfolding.
    These are succeeds-on-valid-inputs results, not just termination of a
    fuelled function.  Fitch layout and eigenconstant preservation are
    separate obligations, and are not asserted by these theorems.
*)

theory LF_HLW_Translation_Proofs
  imports LF_HLW_Unfold
begin

section \<open>Every checked citation exists\<close>

lemma hlRuleOK_cited_exists:
  assumes "hlRuleOK P l" "m \<in> set (hlCitedLines (hlJustification l))"
  shows "hlLookupLine P m \<noteq> None"
  using assms
  by (cases "hlJustification l")
     (auto simp: hlRuleOK_def Let_def list_all_iff split: option.splits)

lemma hlSequenceOptions_success:
  "hlSequenceOptions xs \<noteq> None \<longleftrightarrow> None \<notin> set xs"
  by (induction xs rule: hlSequenceOptions.induct)
     (auto split: option.splits)

lemma hlUnfoldDerivation_step:
  assumes lookup: "hlLookupLine P n = Some l"
      and rule: "hlRuleOK P l"
      and children: "\<And>m. m \<in> set (hlCitedLines (hlJustification l)) \<Longrightarrow>
        hlUnfoldDerivation fuel P m \<noteq> None"
  shows "hlUnfoldDerivation (Suc fuel) P n \<noteq> None"
proof (cases "hlJustification l")
  case HL_Assumption
  show ?thesis by (simp add: lookup HL_Assumption  Let_def)
next
  case (HL_MP m k)
  obtain d_m where d_m: "hlUnfoldDerivation fuel P m = Some d_m"
    using children HL_MP by auto
  obtain d_k where d_k: "hlUnfoldDerivation fuel P k = Some d_k"
    using children HL_MP by auto
  show ?thesis by (simp add: lookup HL_MP d_m d_k Let_def)
next
  case (HL_MT m k)
  obtain d_m where d_m: "hlUnfoldDerivation fuel P m = Some d_m"
    using children HL_MT by auto
  obtain d_k where d_k: "hlUnfoldDerivation fuel P k = Some d_k"
    using children HL_MT by auto
  show ?thesis by (simp add: lookup HL_MT d_m d_k Let_def)
next
  case (HL_DN m)
  obtain d_m where d_m: "hlUnfoldDerivation fuel P m = Some d_m"
    using children HL_DN by auto
  show ?thesis by (simp add: lookup HL_DN d_m Let_def)
next
  case (HL_CP a c)
  obtain d_c where d_c: "hlUnfoldDerivation fuel P c = Some d_c"
    using children HL_CP by auto
  have "hlLookupLine P a \<noteq> None"
    by (rule hlRuleOK_cited_exists[OF rule]) (simp add: HL_CP)
  then obtain f_a where f_a: "hlFormulaAt P a = Some f_a"
    by (auto simp: hlFormulaAt_def split: option.splits)
  show ?thesis by (simp add: lookup HL_CP d_c f_a Let_def)
next
  case (HL_AndIntro m k)
  obtain d_m where d_m: "hlUnfoldDerivation fuel P m = Some d_m"
    using children HL_AndIntro by auto
  obtain d_k where d_k: "hlUnfoldDerivation fuel P k = Some d_k"
    using children HL_AndIntro by auto
  show ?thesis by (simp add: lookup HL_AndIntro d_m d_k Let_def)
next
  case (HL_AndElim m)
  obtain d_m where d_m: "hlUnfoldDerivation fuel P m = Some d_m"
    using children HL_AndElim by auto
  show ?thesis by (simp add: lookup HL_AndElim d_m Let_def)
next
  case (HL_OrIntro m)
  obtain d_m where d_m: "hlUnfoldDerivation fuel P m = Some d_m"
    using children HL_OrIntro by auto
  show ?thesis by (simp add: lookup HL_OrIntro d_m Let_def)
next
  case (HL_OrElim d a1 c1 a2 c2)
  obtain d_d where d_d: "hlUnfoldDerivation fuel P d = Some d_d"
    using children HL_OrElim by auto
  obtain d_c1 where d_c1: "hlUnfoldDerivation fuel P c1 = Some d_c1"
    using children HL_OrElim by auto
  obtain d_c2 where d_c2: "hlUnfoldDerivation fuel P c2 = Some d_c2"
    using children HL_OrElim by auto
  have "hlLookupLine P a1 \<noteq> None"
    by (rule hlRuleOK_cited_exists[OF rule]) (simp add: HL_OrElim)
  then obtain f_a1 where f_a1: "hlFormulaAt P a1 = Some f_a1"
    by (auto simp: hlFormulaAt_def split: option.splits)
  have "hlLookupLine P a2 \<noteq> None"
    by (rule hlRuleOK_cited_exists[OF rule]) (simp add: HL_OrElim)
  then obtain f_a2 where f_a2: "hlFormulaAt P a2 = Some f_a2"
    by (auto simp: hlFormulaAt_def split: option.splits)
  show ?thesis by (simp add: lookup HL_OrElim d_d d_c1 d_c2 f_a1 f_a2 Let_def)
next
  case (HL_RAA a c)
  obtain d_c where d_c: "hlUnfoldDerivation fuel P c = Some d_c"
    using children HL_RAA by auto
  have "hlLookupLine P a \<noteq> None"
    by (rule hlRuleOK_cited_exists[OF rule]) (simp add: HL_RAA)
  then obtain f_a where f_a: "hlFormulaAt P a = Some f_a"
    by (auto simp: hlFormulaAt_def split: option.splits)
  show ?thesis by (simp add: lookup HL_RAA d_c f_a Let_def)
next
  case (HL_ForallElim m)
  obtain d_m where d_m: "hlUnfoldDerivation fuel P m = Some d_m"
    using children HL_ForallElim by auto
  show ?thesis by (simp add: lookup HL_ForallElim d_m Let_def)
next
  case (HL_ExistsIntro m)
  obtain d_m where d_m: "hlUnfoldDerivation fuel P m = Some d_m"
    using children HL_ExistsIntro by auto
  show ?thesis by (simp add: lookup HL_ExistsIntro d_m Let_def)
next
  case (HL_ForallIntro m)
  obtain d_m where d_m: "hlUnfoldDerivation fuel P m = Some d_m"
    using children HL_ForallIntro by auto
  show ?thesis by (simp add: lookup HL_ForallIntro d_m Let_def)
next
  case (HL_ExistsElim m a c)
  obtain d_m where d_m: "hlUnfoldDerivation fuel P m = Some d_m"
    using children HL_ExistsElim by auto
  obtain d_c where d_c: "hlUnfoldDerivation fuel P c = Some d_c"
    using children HL_ExistsElim by auto
  have "hlLookupLine P a \<noteq> None"
    by (rule hlRuleOK_cited_exists[OF rule]) (simp add: HL_ExistsElim)
  then obtain f_a where f_a: "hlFormulaAt P a = Some f_a"
    by (auto simp: hlFormulaAt_def split: option.splits)
  show ?thesis by (simp add: lookup HL_ExistsElim d_m d_c f_a Let_def)
next
  case HL_EqIntro
  show ?thesis by (simp add: lookup HL_EqIntro  Let_def)
next
  case (HL_EqElim m k)
  obtain d_m where d_m: "hlUnfoldDerivation fuel P m = Some d_m"
    using children HL_EqElim by auto
  obtain d_k where d_k: "hlUnfoldDerivation fuel P k = Some d_k"
    using children HL_EqElim by auto
  show ?thesis by (simp add: lookup HL_EqElim d_m d_k Let_def)
next
  case HL_LEM
  show ?thesis by (simp add: lookup HL_LEM  Let_def)
next
  case (HL_PropTaut ms)
  have "hlSequenceOptions (map (hlUnfoldDerivation fuel P) ms) \<noteq> None"
    apply (subst hlSequenceOptions_success)
    using children HL_PropTaut by fastforce
  then obtain ds where ds:
    "hlSequenceOptions (map (hlUnfoldDerivation fuel P) ms) = Some ds" by auto
  show ?thesis by (simp add: lookup HL_PropTaut ds Let_def)
next
  case (HL_IffIntro m k)
  obtain d_m where d_m: "hlUnfoldDerivation fuel P m = Some d_m"
    using children HL_IffIntro by auto
  obtain d_k where d_k: "hlUnfoldDerivation fuel P k = Some d_k"
    using children HL_IffIntro by auto
  show ?thesis by (simp add: lookup HL_IffIntro d_m d_k Let_def)
next
  case (HL_IffElim m k)
  obtain d_m where d_m: "hlUnfoldDerivation fuel P m = Some d_m"
    using children HL_IffElim by auto
  obtain d_k where d_k: "hlUnfoldDerivation fuel P k = Some d_k"
    using children HL_IffElim by auto
  show ?thesis by (simp add: lookup HL_IffElim d_m d_k Let_def)
next
  case (HL_QN m)
  obtain d_m where d_m: "hlUnfoldDerivation fuel P m = Some d_m"
    using children HL_QN by auto
  show ?thesis by (simp add: lookup HL_QN d_m Let_def)
qed

section \<open>A finite rank for the citation graph\<close>

definition hlCitationRank :: "hl_proof \<Rightarrow> int \<Rightarrow> nat" where
  "hlCitationRank P n = length (filter (\<lambda>l. hlLineNumber l < n) P)"

lemma hlCitationRank_le_length:
  "hlCitationRank P n \<le> length P"
  by (simp add: hlCitationRank_def)

lemma hlCitationRank_strict:
  assumes lookup: "hlLookupLine P m = Some lm" and smaller: "m < n"
  shows "hlCitationRank P m < hlCitationRank P n"
proof -
  have member: "lm \<in> set P" using hlLookupLine_in_set[OF lookup] .
  have number: "hlLineNumber lm = m" using hlLookupLine_number[OF lookup] .
  have member_filtered: "lm \<in> set (filter (\<lambda>l. hlLineNumber l < n) P)"
    using member number smaller by simp
  have not_lower: "\<not> hlLineNumber lm < m" using number by simp
  have filter_eq:
    "filter (\<lambda>l. hlLineNumber l < m)
      (filter (\<lambda>l. hlLineNumber l < n) P) =
     filter (\<lambda>l. hlLineNumber l < m) P"
    using smaller by (auto intro!: filter_cong)
  show ?thesis
    using length_filter_less[where P = "\<lambda>l. hlLineNumber l < m",
      OF member_filtered not_lower]
    by (simp only: hlCitationRank_def filter_eq)
qed

theorem hlUnfoldDerivation_succeeds:
  assumes correct: "hlCorrect P"
      and lookup: "hlLookupLine P n = Some l"
      and fuel: "hlCitationRank P n < fuel"
  shows "\<exists>d. hlUnfoldDerivation fuel P n = Some d"
  using lookup fuel
proof (induction fuel arbitrary: n l)
  case 0
  then show ?case by simp
next
  case (Suc fuel)
  have member: "l \<in> set P" using hlLookupLine_in_set[OF Suc.prems(1)] .
  have line_ok: "hlLineOK P l"
    using correct member by (auto simp: hlCorrect_def list_all_iff)
  have rule: "hlRuleOK P l" and line_structure: "hlStructureOK P l"
    using line_ok by (auto simp: hlLineOK_def)
  have number: "hlLineNumber l = n" using hlLookupLine_number[OF Suc.prems(1)] .
  have children: "\<And>m. m \<in> set (hlCitedLines (hlJustification l)) \<Longrightarrow>
      hlUnfoldDerivation fuel P m \<noteq> None"
  proof -
    fix m
    assume cited: "m \<in> set (hlCitedLines (hlJustification l))"
    obtain lm where child_lookup: "hlLookupLine P m = Some lm"
      using hlRuleOK_cited_exists[OF rule cited] by auto
    have smaller: "m < n"
      using line_structure cited number by (auto simp: hlStructureOK_def)
    have rank: "hlCitationRank P m < fuel"
      using hlCitationRank_strict[OF child_lookup smaller] Suc.prems(2) by arith
    show "hlUnfoldDerivation fuel P m \<noteq> None"
      using Suc.IH[OF child_lookup rank] by auto
  qed
  show ?case
    using hlUnfoldDerivation_step[OF Suc.prems(1) rule children] by auto
qed

section \<open>The exact source-to-tree interface succeeds\<close>

theorem hlToDerivation_total:
  assumes verified: "hlVerifiedCorrect P" and nonempty: "P \<noteq> []"
  shows "\<exists>d. hlToDerivation P = Some d"
proof -
  have correct: "hlCorrect P" using verified by (simp add: hlVerifiedCorrect_def)
  have member: "last P \<in> set P" using nonempty by simp
  have lookup: "hlLookupLine P (hlLineNumber (last P)) = Some (last P)"
    by (rule hlCorrect_lookup_self[OF correct member])
  have fuel: "hlCitationRank P (hlLineNumber (last P)) < Suc (length P)"
    using hlCitationRank_le_length[of P "hlLineNumber (last P)"] by simp
  obtain d where "hlUnfoldDerivation (Suc (length P)) P
      (hlLineNumber (last P)) = Some d"
    using hlUnfoldDerivation_succeeds[OF correct lookup fuel] by blast
  then show ?thesis
    using verified nonempty by (simp add: hlToDerivation_def)
qed

lemma hlUnfoldDerivation_formula:
  assumes "hlUnfoldDerivation fuel P n = Some d"
  shows "hlFormulaAt P n = Some (hlDerivationFormula d)"
  using assms
  by (cases fuel; auto simp: hlFormulaAt_def Let_def
      split: option.splits hl_justification.splits prod.splits)

lemma hlClassifyAssumptions_formula [simp]:
  "hlDerivationFormula (hlClassifyAssumptions bound d) = hlDerivationFormula d"
  by (cases d) simp

theorem hlToDerivation_conclusion:
  assumes "hlToDerivation P = Some d"
  shows "hlConclusion P = Some (hlDerivationFormula d)"
proof -
  from assms obtain d0 where nonempty: "P \<noteq> []"
    and correct: "hlCorrect P"
    and unfolded: "hlUnfoldDerivation (Suc (length P)) P
      (hlLineNumber (last P)) = Some d0"
    and classified: "d = hlClassifyAssumptions {} d0"
    by (auto simp: hlToDerivation_def hlVerifiedCorrect_def split: if_splits option.splits)
  have lookup: "hlLookupLine P (hlLineNumber (last P)) = Some (last P)"
    by (rule hlCorrect_lookup_self[OF correct]) (simp add: nonempty)
  have "hlFormula (last P) = hlDerivationFormula d0"
    using hlUnfoldDerivation_formula[OF unfolded] by (simp add: hlFormulaAt_def lookup)
  then show ?thesis by (simp add: hlConclusion_def nonempty classified)
qed

section \<open>Formula preservation through the Fitch representation\<close>

lemma hlFitchToLemmon_formulas:
  "map hlFormula (\<delta>\<^sub>H F) = map (\<lambda>(n,p,r). p) (hlFlattenFitch F)"
  by (simp add: hlFitchToLemmon_def hlFitchToLemmonFrom_formulas comp_def case_prod_beta)

lemma hlConclusion_formulas:
  "hlConclusion P =
   (if map hlFormula P = [] then None else Some (last (map hlFormula P)))"
  by (simp add: hlConclusion_def last_map)

theorem hlLemmonToFitchDirect_conclusion:
  assumes direct: "hlLemmonToFitchDirect P = Inr F"
  shows "hlConclusion (\<delta>\<^sub>H F) = hlConclusion P"
proof -
  have formulas: "map hlFormula (\<delta>\<^sub>H F) = map hlFormula P"
    using arg_cong[OF hlLemmonToFitchDirect_positional[OF direct], of "map snd"]
    by (simp add: hlFitchToLemmon_formulas comp_def case_prod_unfold)
  show ?thesis by (simp only: hlConclusion_formulas formulas)
qed

text \<open>The following theorem is an accepted-output guarantee for the
  checked interface.  Its Fitch-validity component comes from the executable
  validator.  It does not state that the validator accepts every unfolded
  verified source; proving that assertion still requires the general layout
  and eigenconstant-preservation arguments.\<close>

theorem hlViaTree_accepted:
  assumes "hlViaTree P = Inr (route,F)"
  shows "hlFitchCorrect F \<and> hlConclusion (\<delta>\<^sub>H F) = hlConclusion P \<and>
    set (hlFitchPremises F) \<subseteq> set (hlOpenPremises P)"
  using assms
  by (auto simp: hlViaTree_def Let_def split: option.splits if_splits)

theorem hlLemmonToFitchChecked_accepted:
  assumes "hlLemmonToFitchChecked P = Inr (route,F)"
  shows "hlFitchCorrect F \<and> hlConclusion (\<delta>\<^sub>H F) = hlConclusion P \<and>
    set (hlFitchPremises F) \<subseteq> set (hlOpenPremises P)"
  using assms hlViaTree_accepted hlLemmonToFitchDirect_conclusion
  by (auto simp: hlLemmonToFitchChecked_def split: sum.splits if_splits)

section \<open>Unused source assumptions must not enlarge the target sequent\<close>

definition hl_unused_premise_example :: hl_proof where
  "hl_unused_premise_example =
    [HL_ProofLine 1 hlP HL_Assumption {1},
     HL_ProofLine 2 (hlQ \<or>\<^sub>H \<not>\<^sub>H hlQ) HL_LEM {}]"

lemma hl_unused_premise_source:
  "hlVerifiedCorrect hl_unused_premise_example"
  "hlOpenPremises hl_unused_premise_example = []"
  by eval+

lemma hl_unused_premise_direct_enlarges_context:
  "case hlLemmonToFitchDirect hl_unused_premise_example of
     Inl e \<Rightarrow> False
   | Inr F \<Rightarrow> hlFitchCorrect F \<and> hlFitchPremises F = [hlP]"
  by eval

lemma hl_unused_premise_checked_preserves_context:
  "case hlLemmonToFitchChecked hl_unused_premise_example of
     Inl e \<Rightarrow> False
   | Inr (route,F) \<Rightarrow>
       route = HL_ViaTreeRoute \<and> hlFitchCorrect F \<and>
       hlFitchPremises F = [] \<and>
       hlConclusion (\<delta>\<^sub>H F) = hlConclusion hl_unused_premise_example"
  by eval

end
