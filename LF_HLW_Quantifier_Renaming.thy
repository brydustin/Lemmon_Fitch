theory LF_HLW_Quantifier_Renaming
  imports LF_HLW_Derivation LF_HLW_Witnesses
begin

lemma hlCollectForalls_constants:
  "hlConstantsInFormula (snd (hlCollectForalls p)) = hlConstantsInFormula p"
  by (induction p) (auto simp: case_prod_beta)

lemma hlCollectExists_constants:
  "hlConstantsInFormula (snd (hlCollectExists p)) = hlConstantsInFormula p"
  by (induction p) (auto simp: case_prod_beta)

lemma hlPrefixExists_constants [simp]:
  "hlConstantsInFormula (hlPrefixExists xs p) = hlConstantsInFormula p"
  unfolding hlPrefixExists_def by (induction xs) simp_all

lemma hlConstantsInScope_rename:
  "hlConstantsInScope (map (hlRenameFormula old new) G) =
    hlRenameName old new ` hlConstantsInScope G"
  by (auto simp: hlConstantsInScope_def hlRenameFormula_constants)

lemma hlRenameName_fresh:
  "c \<notin> S \<Longrightarrow> c \<noteq> new \<Longrightarrow> new \<notin> S \<Longrightarrow>
   hlRenameName old new c \<notin> hlRenameName old new ` S"
  by (auto simp: hlRenameName_def)

lemma hlRenameName_marker:
  "old \<noteq> STR '''' \<Longrightarrow> new \<noteq> STR '''' \<Longrightarrow>
   (hlRenameName old new c = STR '''') = (c = STR '''')"
  by (auto simp: hlRenameName_def)

lemma hlRenameWitnessPairs:
  assumes "old \<noteq> STR ''''" "new \<noteq> STR ''''"
  shows "filter (\<lambda>xc. snd xc \<noteq> STR '''') (zip xs (map (hlRenameName old new) cs)) =
    map (map_prod id (hlRenameName old new))
      (filter (\<lambda>xc. snd xc \<noteq> STR '''') (zip xs cs))"
  using assms
  by (induction xs arbitrary: cs) (case_tac cs; auto simp: hlRenameName_marker)+

lemma hlWitnessPairs_fresh:
  assumes "hlInferWitnessConstsK xs p k q = Some cs"
      "new \<notin> hlConstantsInFormula q" "new \<noteq> STR ''''"
  shows "new \<notin> snd ` set (filter (\<lambda>xc. snd xc \<noteq> STR '''') (zip ys cs))"
  using hlWitnessLists_constants[OF hlInferWitnessConstsK_witness[OF assms(1)]] assms(2,3)
  by (auto dest: set_zip_rightD)

lemma hlForallElimStep_rename:
  assumes step: "hlForallElimStep p q" and marker: "old \<noteq> STR ''''"
      and fresh: "new \<notin> hlConstantsInFormula p" "new \<notin> hlConstantsInFormula q"
  shows "hlForallElimStep (hlRenameFormula old new p) (hlRenameFormula old new q)"
proof -
  obtain xs core where source: "hlCollectForalls p = (xs,core)" by (cases "hlCollectForalls p") auto
  obtain ys target where goal: "hlCollectForalls q = (ys,target)" by (cases "hlCollectForalls q") auto
  from step obtain k cs where checks: "hlEliminationCount xs ys = Some k"
    "hlInferWitnessConstsK xs core k target = Some cs"
    by (auto simp: hlForallElimStep_def source goal Let_def split: option.splits)
  have core_fresh: "new \<notin> hlConstantsInFormula core" "new \<notin> hlConstantsInFormula target"
    using fresh hlCollectForalls_constants[of p] hlCollectForalls_constants[of q]
    by (simp_all add: source goal)
  from hlInferWitnessConstsK_rename[OF checks(2) marker core_fresh] checks(1)
  show ?thesis by (simp add: hlForallElimStep_def hlRenameFormula_collect_foralls source goal Let_def)
qed

lemma hlExistsIntroStep_rename:
  assumes step: "hlExistsIntroStep p q" and marker: "old \<noteq> STR ''''"
      and fresh: "new \<notin> hlConstantsInFormula p" "new \<notin> hlConstantsInFormula q"
  shows "hlExistsIntroStep (hlRenameFormula old new p) (hlRenameFormula old new q)"
proof -
  obtain xs core where goal: "hlCollectExists q = (xs,core)" by (cases "hlCollectExists q") auto
  from step have nonempty: "xs \<noteq> []" and candidate:
    "\<exists>k \<in> set [0..<Suc (length xs)].
      hlInferWitnessConstsK xs (hlPrefixExists (drop k xs) core) k p \<noteq> None"
    by (simp_all add: hlExistsIntroStep_def goal Let_def list_ex_iff)
  from candidate obtain k where member: "k \<in> set [0..<Suc (length xs)]"
    and inferred: "hlInferWitnessConstsK xs (hlPrefixExists (drop k xs) core) k p \<noteq> None"
    by blast
  from inferred obtain cs where selected:
    "hlInferWitnessConstsK xs (hlPrefixExists (drop k xs) core) k p = Some cs" by auto
  note checks = nonempty member selected
  have core_fresh: "new \<notin> hlConstantsInFormula (hlPrefixExists (drop k xs) core)"
    using fresh(2) hlCollectExists_constants[of q] by (simp add: goal)
  from hlInferWitnessConstsK_rename[OF checks(3) marker core_fresh fresh(1)] checks(1,2)
  show ?thesis
    by (auto simp: hlExistsIntroStep_def hlRenameFormula_collect_exists goal Let_def
        hlRenameFormula_prefix_exists list_ex_iff)
qed

lemma hlForallIntroStep_rename:
  assumes step: "hlForallIntroStep p q G"
      and marker: "old \<noteq> STR ''''" "new \<noteq> STR ''''"
      and fresh: "new \<notin> hlConstantsInFormula p" "new \<notin> hlConstantsInFormula q"
        "new \<notin> hlConstantsInScope G"
  shows "hlForallIntroStep (hlRenameFormula old new p) (hlRenameFormula old new q)
    (map (hlRenameFormula old new) G)"
proof -
  obtain xs core where goal: "hlCollectForalls q = (xs,core)" by (cases "hlCollectForalls q") auto
  from step obtain cs where checks: "xs \<noteq> []"
    "hlInferWitnessConstsK xs core (length xs) p = Some cs"
    "hlAbstractMany (filter (\<lambda>xc. snd xc \<noteq> STR '''') (zip xs cs)) p = Some core"
    "\<forall>c \<in> snd ` set (filter (\<lambda>xc. snd xc \<noteq> STR '''') (zip xs cs)).
      c \<notin> hlConstantsInScope G"
    by (auto simp: hlForallIntroStep_def goal Let_def split: option.splits)
  have core_fresh: "new \<notin> hlConstantsInFormula core"
    using fresh(2) hlCollectForalls_constants[of q] by (simp add: goal)
  have pairs_fresh: "new \<notin> snd ` set (filter (\<lambda>xc. snd xc \<noteq> STR '''') (zip xs cs))"
    by (rule hlWitnessPairs_fresh[OF checks(2) fresh(1) marker(2)])
  note inferred = hlInferWitnessConstsK_rename[OF checks(2) marker(1) core_fresh fresh(1)]
  note abstracted = hlRenameFormula_abstract_many[OF fresh(1) pairs_fresh, of old]
  from checks inferred abstracted pairs_fresh fresh(3) show ?thesis
    apply (auto simp: hlForallIntroStep_def hlRenameFormula_collect_foralls goal Let_def
        hlRenameWitnessPairs[OF marker] hlConstantsInScope_rename)
    apply (auto simp: hlRenameName_def split: if_splits)
    apply (force simp: image_iff)+
    done
qed
lemma hlExistsElimStep_rename:
  assumes step: "hlExistsElimStep p a q G"
      and marker: "old \<noteq> STR ''''" "new \<noteq> STR ''''"
      and fresh: "new \<notin> hlConstantsInFormula p" "new \<notin> hlConstantsInFormula a"
        "new \<notin> hlConstantsInFormula q" "new \<notin> hlConstantsInScope G"
  shows "hlExistsElimStep (hlRenameFormula old new p) (hlRenameFormula old new a)
    (hlRenameFormula old new q) (map (hlRenameFormula old new) G)"
proof -
  obtain xs core where source: "hlCollectExists p = (xs,core)" by (cases "hlCollectExists p") auto
  obtain ys body where assumption: "hlCollectExists a = (ys,body)" by (cases "hlCollectExists a") auto
  from step obtain k cs where checks: "xs \<noteq> []" "hlEliminationCount xs ys = Some k"
    "hlInferWitnessConstsK xs (hlPrefixExists ys core) k a = Some cs"
    "hlAbstractMany (filter (\<lambda>xc. snd xc \<noteq> STR '''') (zip (take k xs) cs)) a =
      Some (hlPrefixExists ys core)"
    "\<forall>c \<in> snd ` set (filter (\<lambda>xc. snd xc \<noteq> STR '''') (zip (take k xs) cs)).
      c \<notin> hlConstantsInFormula q \<and> c \<notin> hlConstantsInScope G"
    by (auto simp: hlExistsElimStep_def source assumption Let_def split: option.splits)
  have core_fresh: "new \<notin> hlConstantsInFormula (hlPrefixExists ys core)"
    using fresh(1) hlCollectExists_constants[of p] by (simp add: source)
  have pairs_fresh: "new \<notin> snd ` set (filter (\<lambda>xc. snd xc \<noteq> STR '''') (zip (take k xs) cs))"
    by (rule hlWitnessPairs_fresh[OF checks(3) fresh(2) marker(2)])
  note inferred = hlInferWitnessConstsK_rename[OF checks(3) marker(1) core_fresh fresh(2)]
  note abstracted = hlRenameFormula_abstract_many[OF fresh(2) pairs_fresh, of old]
  from checks inferred abstracted pairs_fresh fresh(3,4) show ?thesis
    apply (auto simp: hlExistsElimStep_def hlRenameFormula_collect_exists source assumption Let_def
        hlRenameFormula_prefix_exists hlRenameWitnessPairs[OF marker]
        hlConstantsInScope_rename hlRenameFormula_constants)
    apply (auto simp: hlRenameName_def split: if_splits)
    apply (force simp: image_iff)+
    done
qed


end
