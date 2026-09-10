theory LF_HLW_Conclusion
  imports LF_HLW_Fuel
begin

lemma hlEmitDerivationFuel_empty:
  assumes "fuel \<noteq> []"
    "hlEmitDerivationFuel fuel base env scope first count d = ([],n,after,count')"
  shows "\<exists>i. (d = HL_Derivation (hlDerivationFormula d) (HL_DAssume i) \<or>
    d = HL_Derivation (hlDerivationFormula d) (HL_DPremise i)) \<and>
    n = hlEnvironmentLine env i \<and> after = first \<and> count' = count"
  using assms
  by (cases fuel; cases d)
     (auto simp: Let_def split: hl_derivation_rule.splits prod.splits if_splits)

lemma hlEmitDerivation_empty:
  "hlEmitDerivation base env scope first count d = ([],n,after,count') \<Longrightarrow>
   \<exists>i. (d = HL_Derivation (hlDerivationFormula d) (HL_DAssume i) \<or>
    d = HL_Derivation (hlDerivationFormula d) (HL_DPremise i)) \<and>
    n = hlEnvironmentLine env i \<and> after = first \<and> count' = count"
  unfolding hlEmitDerivation_def by (rule hlEmitDerivationFuel_empty) auto

lemma hlFlattenFitch_append:
  "hlFlattenFitch (F @ G) = hlFlattenFitch F @ hlFlattenFitch G"
  by (induction F) simp_all

lemma hlFitchConclusion_last_line:
  "F \<noteq> [] \<Longrightarrow> last F = HL_FLine n p r \<Longrightarrow>
   hlFitchConclusion (G @ F) = Some p"
  by (induction F arbitrary: G rule: rev_induct)
     (auto simp: hlFitchConclusion_def hlFlattenFitch_append)

lemma hlClassifyAssumptions_root_not_assume:
  "hlClassifyAssumptions {} d \<noteq> HL_Derivation p (HL_DAssume i)"
  by (cases d) (auto split: hl_derivation_rule.splits)

lemma hlDerivationToFitch_premise:
  "hlDerivationToFitch (HL_Derivation p (HL_DPremise i)) = [HL_FLine 1 p HL_FPremise]"
  by (simp add: hlDerivationToFitch_def hlPremiseEnvironment_def
      hlPremiseFitchLines_def hlEmitDerivation_def Let_def)

lemma hlDerivationToFitch_conclusion:
  assumes root: "\<And>i. d \<noteq> HL_Derivation (hlDerivationFormula d) (HL_DAssume i)"
  shows "hlFitchConclusion (hlDerivationToFitch d) = Some (hlDerivationFormula d)"
proof -
  let ?env = "hlPremiseEnvironment d"
  let ?base = "Suc (maxlen (sorted_list_of_set
    (\<Union> (hlConstantsInFormula ` set (hlDerivationFormulas d)))))"
  obtain body n after count where emitted:
    "hlEmitDerivation ?base ?env (map (\<lambda>(source,n,phi). phi) ?env)
      (1 + int (length ?env)) 0 d = (body,n,after,count)"
    by (cases "hlEmitDerivation ?base ?env (map (\<lambda>(source,n,phi). phi) ?env)
      (1 + int (length ?env)) 0 d") auto
  show ?thesis
  proof (cases "body = []")
    case True
    from hlEmitDerivation_empty[OF emitted[unfolded True]] root
    obtain i where d: "d = HL_Derivation (hlDerivationFormula d) (HL_DPremise i)" by blast
    then show ?thesis by (metis hlDerivationToFitch_premise hlFitchConclusion_last_line
      append_Nil list.distinct(1) last.simps)
  next
    case False
    from hlEmitDerivation_last[OF emitted False] obtain r where
      finish: "last body = HL_FLine n (hlDerivationFormula d) r" by blast
    from hlFitchConclusion_last_line[OF False finish, of "hlPremiseFitchLines ?env"]
    show ?thesis by (simp add: hlDerivationToFitch_def Let_def emitted)
  qed
qed

corollary hlClassifiedDerivationToFitch_conclusion:
  "hlFitchConclusion (hlDerivationToFitch (hlClassifyAssumptions {} d)) =
   Some (hlDerivationFormula d)"
  using hlDerivationToFitch_conclusion[OF hlClassifyAssumptions_root_not_assume, of d]
  by simp

end
