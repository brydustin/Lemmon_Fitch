theory LF_HLW_Derivation_Renaming
  imports LF_HLW_Quantifier_Renaming
begin

declare hlEqualUpToConstantReplacement.simps [simp del]

section \<open>Propositional rules under renaming\<close>

lemma hlPropositionalValue_cong:
  "(\<And>a. a \<in> set (hlPropositionalAtoms p) \<Longrightarrow> v a = w a) \<Longrightarrow>
   hlPropositionalValue v p = hlPropositionalValue w p"
  by (induction p) auto

lemma hlPropositionalConsequence_valuations:
  "hlPropositionalConsequence G p \<longleftrightarrow>
   (\<forall>v. list_all (hlPropositionalValue v) G \<longrightarrow> hlPropositionalValue v p)"
proof
  assume consequence: "hlPropositionalConsequence G p"
  show "\<forall>v. list_all (hlPropositionalValue v) G \<longrightarrow> hlPropositionalValue v p"
  proof (intro allI impI)
    fix v
    assume given: "list_all (hlPropositionalValue v) G"
    let ?atoms = "remdups (concat (map hlPropositionalAtoms (p # G)))"
    obtain w where w: "w \<in> set (hlValuations ?atoms)" "\<forall>a \<in> set ?atoms. w a = v a"
      using hlValuations_complete[of ?atoms v] by blast
    have agree: "\<And>q. q \<in> set (p # G) \<Longrightarrow>
        hlPropositionalValue w q = hlPropositionalValue v q"
      by (rule hlPropositionalValue_cong) (use w(2) in auto)
    from consequence w(1) given agree show "hlPropositionalValue v p"
      by (auto simp: hlPropositionalConsequence_def Let_def list_all_iff)
  qed
next
  assume "\<forall>v. list_all (hlPropositionalValue v) G \<longrightarrow> hlPropositionalValue v p"
  then show "hlPropositionalConsequence G p"
    by (auto simp: hlPropositionalConsequence_def Let_def list_all_iff)
qed

lemma hlPropositionalValue_rename:
  "hlPropositionalValue v (hlRenameFormula old new p) =
   hlPropositionalValue (\<lambda>a. v (hlRenameFormula old new a)) p"
  by (induction p) simp_all

lemma hlPropositionalConsequence_rename:
  "hlPropositionalConsequence G p \<Longrightarrow>
   hlPropositionalConsequence (map (hlRenameFormula old new) G) (hlRenameFormula old new p)"
  by (auto simp: hlPropositionalConsequence_valuations list_all_iff hlPropositionalValue_rename)

lemma hlContradiction_rename:
  "hlContradiction p \<Longrightarrow> hlContradiction (hlRenameFormula old new p)"
  by (auto simp: hlContradiction_def split: hl_formula.splits)

lemma hlExcludedMiddle_rename:
  "hlExcludedMiddle p \<Longrightarrow> hlExcludedMiddle (hlRenameFormula old new p)"
  by (auto simp: hlExcludedMiddle_def split: hl_formula.splits)

lemma hlEqualityFormula_rename:
  "hlEqualityFormula p = Some (t,u) \<Longrightarrow>
   hlEqualityFormula (hlRenameFormula old new p) =
     Some (hlRenameTerm old new t,hlRenameTerm old new u)"
  by (induction p rule: hlEqualityFormula.induct) (auto split: if_splits)

section \<open>Open assumptions and local freshness\<close>

lemma hlOpenAssumptions_rename:
  "hlOpenAssumptions (hlRenameDerivation old new d) =
   map (map_prod id (hlRenameFormula old new)) (hlOpenAssumptions d)"
  by (induction d rule: hlOpenAssumptions.induct)
     (auto simp: map_map map_concat comp_def filter_map
       intro!: arg_cong[where f=concat] map_cong)

lemma hlOpenFormulas_rename:
  "hlOpenFormulas (hlRenameDerivation old new d) =
   map (hlRenameFormula old new) (hlOpenFormulas d)"
  by (simp add: hlOpenAssumptions_rename map_map comp_def)

lemma hlDischargeOK_rename:
  "hlDischargeOK a p d \<Longrightarrow>
   hlDischargeOK a (hlRenameFormula old new p) (hlRenameDerivation old new d)"
  by (auto simp: hlDischargeOK_def hlOpenAssumptions_rename)

lemma hlOpenAssumptions_in_formulas:
  "nf \<in> set (hlOpenAssumptions d) \<Longrightarrow> snd nf \<in> set (hlDerivationFormulas d)"
  by (induction d arbitrary: nf rule: hlOpenAssumptions.induct) auto

lemma hlOpenFormulas_fresh:
  "new \<notin> hlDerivationConstants d \<Longrightarrow>
   new \<notin> hlConstantsInScope (hlOpenFormulas d)"
  by (auto simp: hlDerivationConstants_def hlConstantsInScope_def
      dest: hlOpenAssumptions_in_formulas)

lemma hlOpenFormulas_drop_fresh:
  "new \<notin> hlDerivationConstants d \<Longrightarrow>
   new \<notin> hlConstantsInScope (map snd (hlDropAssumption a (hlOpenAssumptions d)))"
  using hlOpenFormulas_fresh[of new d] by (auto simp: hlConstantsInScope_def)

lemma hlRenameDerivation_open_unchanged:
  "old \<notin> hlConstantsInScope (hlOpenFormulas d) \<Longrightarrow>
   hlOpenAssumptions (hlRenameDerivation old new d) = hlOpenAssumptions d"
  apply (auto simp: hlOpenAssumptions_rename hlConstantsInScope_def intro!: map_idI)
  apply (rule hlRenameFormula_absent; force)
  done


lemma hlDerivationFormula_in_formulas:
  "hlDerivationFormula d \<in> set (hlDerivationFormulas d)"
  by (cases d) simp

lemma hlDerivationFormula_fresh:
  "new \<notin> hlDerivationConstants d \<Longrightarrow>
   new \<notin> hlConstantsInFormula (hlDerivationFormula d)"
  using hlDerivationFormula_in_formulas[of d]
  by (auto simp: hlDerivationConstants_def)

lemma hlOpenFormulas_drop_rename:
  "map snd (hlDropAssumption a (hlOpenAssumptions (hlRenameDerivation old new d))) =
   map (hlRenameFormula old new) (map snd (hlDropAssumption a (hlOpenAssumptions d)))"
  by (simp add: hlOpenAssumptions_rename filter_map map_map comp_def)

section \<open>Fresh renaming preserves every exact derivation rule\<close>

lemma hlDerivationOK_rename:
  assumes "hlDerivationOK d" "new \<notin> hlDerivationConstants d"
    "old \<noteq> STR ''''" "new \<noteq> STR ''''"
  shows "hlDerivationOK (hlRenameDerivation old new d)"
  using assms
  apply (induction d rule: hlDerivationOK.induct)
  apply (auto simp: hlDerivationConstants_def list_all_iff map_map comp_def
      hlOpenFormulas_rename hlOpenFormulas_drop_rename
    intro: hlDischargeOK_rename hlContradiction_rename hlExcludedMiddle_rename
      hlForallElimStep_rename hlForallIntroStep_rename hlExistsIntroStep_rename
      hlExistsElimStep_rename hlPropositionalConsequence_rename
      hlRenameFormula_qn
    split: hl_formula.splits)
  subgoal for f d
    by (rule hlForallElimStep_rename)
       (auto simp: hlDerivationFormula_in_formulas)
  subgoal for f d
    apply (rule hlForallIntroStep_rename[where G="hlOpenFormulas d", simplified map_map comp_def])
    apply (auto simp: hlDerivationFormula_in_formulas)
    apply (insert hlOpenFormulas_fresh[of new d])
    apply (auto simp: hlDerivationConstants_def)
    done
  subgoal for f d
    by (rule hlExistsIntroStep_rename)
       (auto simp: hlDerivationFormula_in_formulas)
  subgoal for d a p e
    apply (rule hlExistsElimStep_rename[where G="map snd (hlDropAssumption a (hlOpenAssumptions e))",
      simplified map_map comp_def])
    apply (auto simp: hlDerivationFormula_in_formulas)
    apply (insert hlOpenFormulas_drop_fresh[of new e a])
    apply (auto simp: hlDerivationConstants_def)
    done
  subgoal premises prems for E ts
    using prems
    by (cases ts; cases "tl ts"; cases "tl (tl ts)";
        cases "hd ts"; cases "hd (tl ts)") auto
  subgoal premises prems for f d e
  proof -
    from prems obtain a b where eq:
      "hlEqualityFormula (hlDerivationFormula e) = Some (HL_Const a,HL_Const b)"
      and repl: "hlEqualUpToConstantReplacement a b (hlDerivationFormula d) f"
      by (auto split: option.split_asm prod.split_asm hl_term.split_asm)
    from hlEqualityFormula_rename[OF eq, of old new]
      hlRenameFormula_equality_replacement[OF repl, of old new]
    show ?thesis by (simp add: hlRenameName_def)
  qed
  subgoal for f ds
    using hlPropositionalConsequence_rename[where G="map hlDerivationFormula ds",
      simplified map_map comp_def] by blast
  done

end
