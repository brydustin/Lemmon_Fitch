theory LF_HLW_Faithful
  imports LF_HLW_Derivation LF_HLW_Canonical LF_HLW_Translation_Proofs
begin

declare hlEqualUpToConstantReplacement.simps [simp del]

section \<open>Labelled assumptions read from the source proof\<close>

definition hlSourceAssumptions ::
  "hl_proof \<Rightarrow> int set \<Rightarrow> (int \<times> hl_formula) set" where
  "hlSourceAssumptions P G =
     {nf. fst nf \<in> G \<and>
       (\<exists>l. hlLookupLine P (fst nf) = Some l \<and>
         hlJustification l = HL_Assumption \<and> hlFormula l = snd nf)}"

lemma hlSourceAssumptions_empty [simp]: "hlSourceAssumptions P {} = {}"
  by (auto simp: hlSourceAssumptions_def)

lemma hlSourceAssumptions_union [simp]:
  "hlSourceAssumptions P (G \<union> H) =
   hlSourceAssumptions P G \<union> hlSourceAssumptions P H"
  by (auto simp: hlSourceAssumptions_def)

lemma hlSourceAssumptions_difference [simp]:
  "hlSourceAssumptions P (G - {a}) =
   {nf \<in> hlSourceAssumptions P G. fst nf \<noteq> a}"
  by (auto simp: hlSourceAssumptions_def)

lemma hlSourceAssumptions_mono:
  "G \<subseteq> H \<Longrightarrow> hlSourceAssumptions P G \<subseteq> hlSourceAssumptions P H"
  by (auto simp: hlSourceAssumptions_def)

lemma hlSourceAssumptions_discharge:
  assumes "set (hlOpenAssumptions d) \<subseteq> hlSourceAssumptions P G"
      and "hlFormulaAt P a = Some f"
  shows "hlDischargeOK a f d"
  using assms
  by (auto simp: hlDischargeOK_def hlSourceAssumptions_def hlFormulaAt_def
      split: option.splits)

lemma hlSourceAssumptions_formulas:
  "snd ` hlSourceAssumptions P G \<subseteq> set (hlAssumptionFormulas P G)"
proof
  fix f
  assume "f \<in> snd ` hlSourceAssumptions P G"
  then obtain a l where lookup: "hlLookupLine P a = Some l"
    and facts: "a \<in> G" "hlJustification l = HL_Assumption" "f = hlFormula l"
    by (auto simp: hlSourceAssumptions_def)
  have "l \<in> set P" by (rule hlLookupLine_in_set[OF lookup])
  moreover have "hlLineNumber l = a" by (rule hlLookupLine_number[OF lookup])
  ultimately show "f \<in> set (hlAssumptionFormulas P G)"
    using facts by (auto simp: hlAssumptionFormulas_def)
qed

lemma hlSourceAssumptions_constants:
  assumes "set (hlOpenAssumptions d) \<subseteq> hlSourceAssumptions P G"
  shows "hlConstantsInScope (hlOpenFormulas d) \<subseteq> hlAssumptionConstants P G"
  using assms hlSourceAssumptions_formulas[of P G]
  by (auto simp: hlConstantsInScope_def hlAssumptionFormulas_constants[symmetric])

lemma hlSourceAssumptions_referenced_constants:
  assumes "set (hlOpenAssumptions d) \<subseteq> hlSourceAssumptions P G"
  shows "hlConstantsInScope (map snd (hlDropAssumption a (hlOpenAssumptions d)))
      \<subseteq> hlReferencedConstants P (G - {a})"
proof
  fix x
  assume "x \<in> hlConstantsInScope (map snd (hlDropAssumption a (hlOpenAssumptions d)))"
  then obtain b f where bf: "(b,f) \<in> set (hlOpenAssumptions d)"
    "b \<noteq> a" "x \<in> hlConstantsInFormula f"
    by (auto simp: hlConstantsInScope_def)
  from assms bf obtain l where lookup: "hlLookupLine P b = Some l"
    and facts: "b \<in> G" "hlFormula l = f"
    by (auto simp: hlSourceAssumptions_def)
  have "l \<in> set P" by (rule hlLookupLine_in_set[OF lookup])
  moreover have "hlLineNumber l = b" by (rule hlLookupLine_number[OF lookup])
  ultimately show "x \<in> hlReferencedConstants P (G - {a})"
    using facts bf by (auto simp: hlReferencedConstants_def)
qed

definition hlTreeRepresents :: "hl_proof \<Rightarrow> int \<Rightarrow> hl_derivation \<Rightarrow> bool" where
  "hlTreeRepresents P n d \<longleftrightarrow>
     hlDerivationOK d \<and>
     hlFormulaAt P n = Some (hlDerivationFormula d) \<and>
     set (hlOpenAssumptions d) \<subseteq> hlSourceAssumptions P (hlPaperDependencyAt P n)"


section \<open>Every successful checked unfolding is a correct derivation\<close>

lemma hlPaperDependencyAt_lookup:
  "hlLookupLine P n = Some l \<Longrightarrow> hlPaperDependencyAt P n = hlReferences l"
  by (simp add: hlPaperDependencyAt_def hlReferencesAt_def)

lemma hlSequenceOptions_map_relation:
  assumes "hlSequenceOptions (map f xs) = Some ys"
  shows "list_all2 (\<lambda>x y. f x = Some y) xs ys"
  using assms
proof (induction xs arbitrary: ys)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then show ?case by (cases "f a") (auto split: option.splits)
qed

lemma hlTreeRepresents_list:
  assumes "list_all2 (hlTreeRepresents P) ns ds"
  shows "list_all hlDerivationOK ds \<and>
     map hlDerivationFormula ds = hlMapFilter (hlFormulaAt P) ns \<and>
     set (concat (map hlOpenAssumptions ds)) \<subseteq>
       hlSourceAssumptions P (hlReferenceUnion P ns)"
  using assms
proof (induction rule: list_all2_induct)
  case Nil
  then show ?case by (simp add: hlReferenceUnion_def)
next
  case (Cons n ns d ds)
  from Cons.hyps(1) obtain l where lookup: "hlLookupLine P n = Some l"
    by (auto simp: hlTreeRepresents_def hlFormulaAt_def)
  from Cons.hyps(1) Cons.IH show ?case
    by (auto simp: hlTreeRepresents_def hlFormulaAt_def lookup
        hlPaperDependencyAt_lookup[OF lookup] hlReferenceUnion_def hlReferencesAt_def)
qed

lemma hlUnfoldDerivation_represents:
  assumes correct: "hlCorrect P" and unfolded: "hlUnfoldDerivation fuel P n = Some d"
  shows "hlTreeRepresents P n d"
  using unfolded
proof (induction fuel arbitrary: n d)
  case 0
  then show ?case by simp
next
  case (Suc fuel)
  from Suc.prems obtain l where lookup: "hlLookupLine P n = Some l"
    by (auto simp: Let_def split: option.splits)
  have rule: "hlRuleOK P l"
    using correct hlLookupLine_in_set[OF lookup]
    by (auto simp: hlCorrect_def list_all_iff hlLineOK_def)
  have child: "\<And>m e lm. hlUnfoldDerivation fuel P m = Some e \<Longrightarrow>
      hlLookupLine P m = Some lm \<Longrightarrow>
      hlDerivationOK e \<and> hlDerivationFormula e = hlFormula lm \<and>
      set (hlOpenAssumptions e) \<subseteq> hlSourceAssumptions P (hlReferences lm)"
  proof -
    fix m e lm
    assume unfolded: "hlUnfoldDerivation fuel P m = Some e"
      and looked: "hlLookupLine P m = Some lm"
    from Suc.IH[OF unfolded] show "hlDerivationOK e \<and>
        hlDerivationFormula e = hlFormula lm \<and>
        set (hlOpenAssumptions e) \<subseteq> hlSourceAssumptions P (hlReferences lm)"
      by (simp add: hlTreeRepresents_def hlFormulaAt_def looked
          hlPaperDependencyAt_lookup[OF looked])
  qed
  show ?case
  proof (cases "hlJustification l")
    case HL_Assumption
    have number: "hlLineNumber l = n" by (rule hlLookupLine_number[OF lookup])
    have refs: "hlReferences l = {n}"
      using rule by (simp add: hlRuleOK_def HL_Assumption Let_def number)
    have premise: "(n,hlFormula l) \<in> hlSourceAssumptions P (hlReferences l)"
      using lookup HL_Assumption by (auto simp: hlSourceAssumptions_def refs)
    from Suc.prems have tree: "d = HL_Derivation (hlFormula l)
      (if n \<in> set (hlDischargedAssumptions P) then HL_DAssume n else HL_DPremise n)"
      by (simp add: lookup HL_Assumption Let_def)
    from premise show ?thesis
      by (simp add: hlTreeRepresents_def tree hlFormulaAt_def lookup
          hlPaperDependencyAt_lookup[OF lookup] split: if_splits)
  next
    case (HL_MP m k)
    obtain lm where lm: "hlLookupLine P m = Some lm"
      using hlRuleOK_cited_exists[OF rule, of m] HL_MP by auto
    obtain lk where lk: "hlLookupLine P k = Some lk"
      using hlRuleOK_cited_exists[OF rule, of k] HL_MP by auto
    from Suc.prems obtain dm dk where
      um: "hlUnfoldDerivation fuel P m = Some dm"
      and uk: "hlUnfoldDerivation fuel P k = Some dk"
      and tree: "d = HL_Derivation (hlFormula l) (HL_DMP dm dk)"
      by (auto simp: lookup HL_MP lm lk hlFormulaAt_def Let_def split: option.splits)
    note cm = child[OF um lm]
    note ck = child[OF uk lk]
    from rule cm ck   show ?thesis
      by (auto simp: hlTreeRepresents_def tree hlFormulaAt_def lookup
          hlPaperDependencyAt_lookup[OF lookup] hlRuleOK_def HL_MP lm lk Let_def
          split: hl_formula.splits hl_term.splits option.splits prod.splits)
  next
    case (HL_MT m k)
    obtain lm where lm: "hlLookupLine P m = Some lm"
      using hlRuleOK_cited_exists[OF rule, of m] HL_MT by auto
    obtain lk where lk: "hlLookupLine P k = Some lk"
      using hlRuleOK_cited_exists[OF rule, of k] HL_MT by auto
    from Suc.prems obtain dm dk where
      um: "hlUnfoldDerivation fuel P m = Some dm"
      and uk: "hlUnfoldDerivation fuel P k = Some dk"
      and tree: "d = HL_Derivation (hlFormula l) (HL_DMT dm dk)"
      by (auto simp: lookup HL_MT lm lk hlFormulaAt_def Let_def split: option.splits)
    note cm = child[OF um lm]
    note ck = child[OF uk lk]
    from rule cm ck   show ?thesis
      by (auto simp: hlTreeRepresents_def tree hlFormulaAt_def lookup
          hlPaperDependencyAt_lookup[OF lookup] hlRuleOK_def HL_MT lm lk Let_def
          split: hl_formula.splits hl_term.splits option.splits prod.splits)
  next
    case (HL_DN m)
    obtain lm where lm: "hlLookupLine P m = Some lm"
      using hlRuleOK_cited_exists[OF rule, of m] HL_DN by auto
    from Suc.prems obtain dm where
      um: "hlUnfoldDerivation fuel P m = Some dm"
      and tree: "d = HL_Derivation (hlFormula l) (HL_DDN dm)"
      by (auto simp: lookup HL_DN lm hlFormulaAt_def Let_def split: option.splits)
    note cm = child[OF um lm]
    from rule cm   show ?thesis
      by (auto simp: hlTreeRepresents_def tree hlFormulaAt_def lookup
          hlPaperDependencyAt_lookup[OF lookup] hlRuleOK_def HL_DN lm Let_def
          split: hl_formula.splits hl_term.splits option.splits prod.splits)
  next
    case (HL_CP a c)
    obtain la where la: "hlLookupLine P a = Some la"
      using hlRuleOK_cited_exists[OF rule, of a] HL_CP by auto
    obtain lc where lc: "hlLookupLine P c = Some lc"
      using hlRuleOK_cited_exists[OF rule, of c] HL_CP by auto
    from Suc.prems obtain dc where
      uc: "hlUnfoldDerivation fuel P c = Some dc"
      and tree: "d = HL_Derivation (hlFormula l) (HL_DCP a (hlFormula la) dc)"
      by (auto simp: lookup HL_CP la lc hlFormulaAt_def Let_def split: option.splits)
    note cc = child[OF uc lc]
    have disa: "hlDischargeOK a (hlFormula la) dc"
      by (rule hlSourceAssumptions_discharge[OF cc[THEN conjunct2, THEN conjunct2]])
         (simp add: hlFormulaAt_def la)
    from rule cc disa hlLookupLine_number[OF la] show ?thesis
      by (auto simp: hlTreeRepresents_def tree hlFormulaAt_def lookup
          hlPaperDependencyAt_lookup[OF lookup] hlRuleOK_def HL_CP la lc Let_def
          split: hl_formula.splits hl_term.splits option.splits prod.splits)
  next
    case (HL_AndIntro m k)
    obtain lm where lm: "hlLookupLine P m = Some lm"
      using hlRuleOK_cited_exists[OF rule, of m] HL_AndIntro by auto
    obtain lk where lk: "hlLookupLine P k = Some lk"
      using hlRuleOK_cited_exists[OF rule, of k] HL_AndIntro by auto
    from Suc.prems obtain dm dk where
      um: "hlUnfoldDerivation fuel P m = Some dm"
      and uk: "hlUnfoldDerivation fuel P k = Some dk"
      and tree: "d = HL_Derivation (hlFormula l) (HL_DAndI dm dk)"
      by (auto simp: lookup HL_AndIntro lm lk hlFormulaAt_def Let_def split: option.splits)
    note cm = child[OF um lm]
    note ck = child[OF uk lk]
    from rule cm ck   show ?thesis
      by (auto simp: hlTreeRepresents_def tree hlFormulaAt_def lookup
          hlPaperDependencyAt_lookup[OF lookup] hlRuleOK_def HL_AndIntro lm lk Let_def
          split: hl_formula.splits hl_term.splits option.splits prod.splits)
  next
    case (HL_AndElim m)
    obtain lm where lm: "hlLookupLine P m = Some lm"
      using hlRuleOK_cited_exists[OF rule, of m] HL_AndElim by auto
    from Suc.prems obtain dm where
      um: "hlUnfoldDerivation fuel P m = Some dm"
      and tree: "d = HL_Derivation (hlFormula l) (HL_DAndE dm)"
      by (auto simp: lookup HL_AndElim lm hlFormulaAt_def Let_def split: option.splits)
    note cm = child[OF um lm]
    from rule cm   show ?thesis
      by (auto simp: hlTreeRepresents_def tree hlFormulaAt_def lookup
          hlPaperDependencyAt_lookup[OF lookup] hlRuleOK_def HL_AndElim lm Let_def
          split: hl_formula.splits hl_term.splits option.splits prod.splits)
  next
    case (HL_OrIntro m)
    obtain lm where lm: "hlLookupLine P m = Some lm"
      using hlRuleOK_cited_exists[OF rule, of m] HL_OrIntro by auto
    from Suc.prems obtain dm where
      um: "hlUnfoldDerivation fuel P m = Some dm"
      and tree: "d = HL_Derivation (hlFormula l) (HL_DOrI dm)"
      by (auto simp: lookup HL_OrIntro lm hlFormulaAt_def Let_def split: option.splits)
    note cm = child[OF um lm]
    from rule cm   show ?thesis
      by (auto simp: hlTreeRepresents_def tree hlFormulaAt_def lookup
          hlPaperDependencyAt_lookup[OF lookup] hlRuleOK_def HL_OrIntro lm Let_def
          split: hl_formula.splits hl_term.splits option.splits prod.splits)
  next
    case (HL_OrElim m a c b e)
    obtain lm where lm: "hlLookupLine P m = Some lm"
      using hlRuleOK_cited_exists[OF rule, of m] HL_OrElim by auto
    obtain la where la: "hlLookupLine P a = Some la"
      using hlRuleOK_cited_exists[OF rule, of a] HL_OrElim by auto
    obtain lc where lc: "hlLookupLine P c = Some lc"
      using hlRuleOK_cited_exists[OF rule, of c] HL_OrElim by auto
    obtain lb where lb: "hlLookupLine P b = Some lb"
      using hlRuleOK_cited_exists[OF rule, of b] HL_OrElim by auto
    obtain le where le: "hlLookupLine P e = Some le"
      using hlRuleOK_cited_exists[OF rule, of e] HL_OrElim by auto
    from Suc.prems obtain dm dc de where
      um: "hlUnfoldDerivation fuel P m = Some dm"
      and uc: "hlUnfoldDerivation fuel P c = Some dc"
      and ue: "hlUnfoldDerivation fuel P e = Some de"
      and tree: "d = HL_Derivation (hlFormula l) (HL_DOrE dm a (hlFormula la) dc b (hlFormula lb) de)"
      by (auto simp: lookup HL_OrElim lm la lc lb le hlFormulaAt_def Let_def split: option.splits)
    note cm = child[OF um lm]
    note cc = child[OF uc lc]
    note ce = child[OF ue le]
    have disa: "hlDischargeOK a (hlFormula la) dc"
      by (rule hlSourceAssumptions_discharge[OF cc[THEN conjunct2, THEN conjunct2]])
         (simp add: hlFormulaAt_def la)
    have disb: "hlDischargeOK b (hlFormula lb) de"
      by (rule hlSourceAssumptions_discharge[OF ce[THEN conjunct2, THEN conjunct2]])
         (simp add: hlFormulaAt_def lb)
    from rule cm cc ce disa disb hlLookupLine_number[OF la] hlLookupLine_number[OF lb] show ?thesis
      by (auto simp: hlTreeRepresents_def tree hlFormulaAt_def lookup
          hlPaperDependencyAt_lookup[OF lookup] hlRuleOK_def HL_OrElim lm la lc lb le Let_def
          split: hl_formula.splits hl_term.splits option.splits prod.splits)
  next
    case (HL_RAA a c)
    obtain la where la: "hlLookupLine P a = Some la"
      using hlRuleOK_cited_exists[OF rule, of a] HL_RAA by auto
    obtain lc where lc: "hlLookupLine P c = Some lc"
      using hlRuleOK_cited_exists[OF rule, of c] HL_RAA by auto
    from Suc.prems obtain dc where
      uc: "hlUnfoldDerivation fuel P c = Some dc"
      and tree: "d = HL_Derivation (hlFormula l) (HL_DRAA a (hlFormula la) dc)"
      by (auto simp: lookup HL_RAA la lc hlFormulaAt_def Let_def split: option.splits)
    note cc = child[OF uc lc]
    have disa: "hlDischargeOK a (hlFormula la) dc"
      by (rule hlSourceAssumptions_discharge[OF cc[THEN conjunct2, THEN conjunct2]])
         (simp add: hlFormulaAt_def la)
    from rule cc disa hlLookupLine_number[OF la] show ?thesis
      by (auto simp: hlTreeRepresents_def tree hlFormulaAt_def lookup
          hlPaperDependencyAt_lookup[OF lookup] hlRuleOK_def HL_RAA la lc Let_def
          split: hl_formula.splits hl_term.splits option.splits prod.splits)
  next
    case (HL_ForallElim m)
    obtain lm where lm: "hlLookupLine P m = Some lm"
      using hlRuleOK_cited_exists[OF rule, of m] HL_ForallElim by auto
    from Suc.prems obtain dm where
      um: "hlUnfoldDerivation fuel P m = Some dm"
      and tree: "d = HL_Derivation (hlFormula l) (HL_DForallE dm)"
      by (auto simp: lookup HL_ForallElim lm hlFormulaAt_def Let_def split: option.splits)
    note cm = child[OF um lm]
    from rule cm   show ?thesis
      by (auto simp: hlTreeRepresents_def tree hlFormulaAt_def lookup
          hlPaperDependencyAt_lookup[OF lookup] hlRuleOK_def HL_ForallElim lm Let_def
          hlForallElimStep_def
          split: hl_formula.splits hl_term.splits option.splits prod.splits)
  next
    case (HL_ExistsIntro m)
    obtain lm where lm: "hlLookupLine P m = Some lm"
      using hlRuleOK_cited_exists[OF rule, of m] HL_ExistsIntro by auto
    from Suc.prems obtain dm where
      um: "hlUnfoldDerivation fuel P m = Some dm"
      and tree: "d = HL_Derivation (hlFormula l) (HL_DExistsI dm)"
      by (auto simp: lookup HL_ExistsIntro lm hlFormulaAt_def Let_def split: option.splits)
    note cm = child[OF um lm]
    from rule cm   show ?thesis
      by (auto simp: hlTreeRepresents_def tree hlFormulaAt_def lookup
          hlPaperDependencyAt_lookup[OF lookup] hlRuleOK_def HL_ExistsIntro lm Let_def
          hlExistsIntroStep_def
          split: hl_formula.splits hl_term.splits option.splits prod.splits)
  next
    case (HL_ForallIntro m)
    obtain lm where lm: "hlLookupLine P m = Some lm"
      using hlRuleOK_cited_exists[OF rule, of m] HL_ForallIntro by auto
    from Suc.prems obtain dm where
      um: "hlUnfoldDerivation fuel P m = Some dm"
      and tree: "d = HL_Derivation (hlFormula l) (HL_DForallI dm)"
      by (auto simp: lookup HL_ForallIntro lm hlFormulaAt_def Let_def split: option.splits)
    note cm = child[OF um lm]
    note constants = hlSourceAssumptions_constants[OF cm[THEN conjunct2, THEN conjunct2]]
    from rule cm   constants show ?thesis
      apply (auto simp: hlTreeRepresents_def tree hlFormulaAt_def lookup
          hlPaperDependencyAt_lookup[OF lookup] hlRuleOK_def HL_ForallIntro lm Let_def
          hlForallIntroStep_def
          split: hl_formula.splits hl_term.splits option.splits prod.splits)
      apply blast+
      done
  next
    case (HL_ExistsElim m a c)
    obtain lm where lm: "hlLookupLine P m = Some lm"
      using hlRuleOK_cited_exists[OF rule, of m] HL_ExistsElim by auto
    obtain la where la: "hlLookupLine P a = Some la"
      using hlRuleOK_cited_exists[OF rule, of a] HL_ExistsElim by auto
    obtain lc where lc: "hlLookupLine P c = Some lc"
      using hlRuleOK_cited_exists[OF rule, of c] HL_ExistsElim by auto
    from Suc.prems obtain dm dc where
      um: "hlUnfoldDerivation fuel P m = Some dm"
      and uc: "hlUnfoldDerivation fuel P c = Some dc"
      and tree: "d = HL_Derivation (hlFormula l) (HL_DExistsE dm a (hlFormula la) dc)"
      by (auto simp: lookup HL_ExistsElim lm la lc hlFormulaAt_def Let_def split: option.splits)
    note cm = child[OF um lm]
    note cc = child[OF uc lc]
    have disa: "hlDischargeOK a (hlFormula la) dc"
      by (rule hlSourceAssumptions_discharge[OF cc[THEN conjunct2, THEN conjunct2]])
         (simp add: hlFormulaAt_def la)
    note constants = hlSourceAssumptions_referenced_constants[OF cc[THEN conjunct2, THEN conjunct2], of a]
    obtain xs p where source: "hlCollectExists (hlFormula lm) = (xs,p)"
      by (cases "hlCollectExists (hlFormula lm)") auto
    obtain ys q where assumption: "hlCollectExists (hlFormula la) = (ys,q)"
      by (cases "hlCollectExists (hlFormula la)") auto
    from rule obtain k cs where checks:
      "xs \<noteq> []" "hlEliminationCount xs ys = Some k"
      "hlInferWitnessConstsK xs (hlPrefixExists ys p) k (hlFormula la) = Some cs"
      "hlAbstractMany (filter (\<lambda>xc. snd xc \<noteq> STR '''') (zip (take k xs) cs))
        (hlFormula la) = Some (hlPrefixExists ys p)"
      "\<forall>w \<in> snd ` set (filter (\<lambda>xc. snd xc \<noteq> STR '''') (zip (take k xs) cs)).
        w \<notin> hlConstantsInFormula (hlFormula lc) \<and>
        w \<notin> hlReferencedConstants P (hlReferences lc - {hlLineNumber la})"
      "hlFormula l = hlFormula lc"
      "hlReferences l = hlReferences lm \<union> (hlReferences lc - {hlLineNumber la})"
      by (auto simp: hlRuleOK_def HL_ExistsElim lm la lc source assumption Let_def
          split: option.splits)
    have step: "hlExistsElimStep (hlFormula lm) (hlFormula la) (hlFormula l)
        (map snd (hlDropAssumption a (hlOpenAssumptions dc)))"
      using checks constants hlLookupLine_number[OF la]
      by (auto simp: hlExistsElimStep_def source assumption Let_def)
    from cm cc disa step checks(6,7) hlLookupLine_number[OF la] show ?thesis
      by (auto simp: hlTreeRepresents_def tree hlFormulaAt_def lookup
          hlPaperDependencyAt_lookup[OF lookup])
  next
    case HL_EqIntro
    from Suc.prems have tree: "d = HL_Derivation (hlFormula l) HL_DEqI"
      by (auto simp: lookup HL_EqIntro  hlFormulaAt_def Let_def split: option.splits)
    from rule    show ?thesis
      by (auto simp: hlTreeRepresents_def tree hlFormulaAt_def lookup
          hlPaperDependencyAt_lookup[OF lookup] hlRuleOK_def HL_EqIntro  Let_def
          split: hl_formula.splits hl_term.splits option.splits prod.splits list.splits)
  next
    case (HL_EqElim m k)
    obtain lm where lm: "hlLookupLine P m = Some lm"
      using hlRuleOK_cited_exists[OF rule, of m] HL_EqElim by auto
    obtain lk where lk: "hlLookupLine P k = Some lk"
      using hlRuleOK_cited_exists[OF rule, of k] HL_EqElim by auto
    from Suc.prems obtain dm dk where
      um: "hlUnfoldDerivation fuel P m = Some dm"
      and uk: "hlUnfoldDerivation fuel P k = Some dk"
      and tree: "d = HL_Derivation (hlFormula l) (HL_DEqE dm dk)"
      by (auto simp: lookup HL_EqElim lm lk hlFormulaAt_def Let_def split: option.splits)
    note cm = child[OF um lm]
    note ck = child[OF uk lk]
    from rule obtain a b where equality:
      "hlEqualityFormula (hlFormula lk) = Some (HL_Const a,HL_Const b)"
      and replacement: "hlEqualUpToConstantReplacement a b (hlFormula lm) (hlFormula l)"
      and refs: "hlReferences l = hlReferences lm \<union> hlReferences lk"
      apply (auto simp: hlRuleOK_def HL_EqElim lm lk Let_def
          simp del: hlEqualUpToConstantReplacement.simps
          split: option.splits hl_term.splits prod.splits)
      apply (metis hl_term.exhaust)
      done
    from cm ck equality replacement refs show ?thesis
      by (auto simp: hlTreeRepresents_def tree hlFormulaAt_def lookup
          hlPaperDependencyAt_lookup[OF lookup]
          simp del: hlEqualUpToConstantReplacement.simps)
  next
    case HL_LEM
    from Suc.prems have tree: "d = HL_Derivation (hlFormula l) HL_DLEM"
      by (auto simp: lookup HL_LEM  hlFormulaAt_def Let_def split: option.splits)
    from rule    show ?thesis
      by (auto simp: hlTreeRepresents_def tree hlFormulaAt_def lookup
          hlPaperDependencyAt_lookup[OF lookup] hlRuleOK_def HL_LEM  Let_def
          split: hl_formula.splits hl_term.splits option.splits prod.splits)
  next
    case (HL_PropTaut ms)
    from Suc.prems obtain ds where sequence:
      "hlSequenceOptions (map (hlUnfoldDerivation fuel P) ms) = Some ds"
      and tree: "d = HL_Derivation (hlFormula l) (HL_DPropTaut ds)"
      by (auto simp: lookup HL_PropTaut Let_def split: option.splits)
    have represents: "list_all2 (hlTreeRepresents P) ms ds"
      using hlSequenceOptions_map_relation[OF sequence]
      by (rule list_all2_mono) (rule Suc.IH)
    from hlTreeRepresents_list[OF represents] rule show ?thesis
      by (auto simp: hlTreeRepresents_def tree hlFormulaAt_def lookup
          hlPaperDependencyAt_lookup[OF lookup] hlRuleOK_def HL_PropTaut Let_def)
  next
    case (HL_IffIntro m k)
    obtain lm where lm: "hlLookupLine P m = Some lm"
      using hlRuleOK_cited_exists[OF rule, of m] HL_IffIntro by auto
    obtain lk where lk: "hlLookupLine P k = Some lk"
      using hlRuleOK_cited_exists[OF rule, of k] HL_IffIntro by auto
    from Suc.prems obtain dm dk where
      um: "hlUnfoldDerivation fuel P m = Some dm"
      and uk: "hlUnfoldDerivation fuel P k = Some dk"
      and tree: "d = HL_Derivation (hlFormula l) (HL_DIffI dm dk)"
      by (auto simp: lookup HL_IffIntro lm lk hlFormulaAt_def Let_def split: option.splits)
    note cm = child[OF um lm]
    note ck = child[OF uk lk]
    from rule cm ck   show ?thesis
      by (auto simp: hlTreeRepresents_def tree hlFormulaAt_def lookup
          hlPaperDependencyAt_lookup[OF lookup] hlRuleOK_def HL_IffIntro lm lk Let_def
          split: hl_formula.splits hl_term.splits option.splits prod.splits)
  next
    case (HL_IffElim m k)
    obtain lm where lm: "hlLookupLine P m = Some lm"
      using hlRuleOK_cited_exists[OF rule, of m] HL_IffElim by auto
    obtain lk where lk: "hlLookupLine P k = Some lk"
      using hlRuleOK_cited_exists[OF rule, of k] HL_IffElim by auto
    from Suc.prems obtain dm dk where
      um: "hlUnfoldDerivation fuel P m = Some dm"
      and uk: "hlUnfoldDerivation fuel P k = Some dk"
      and tree: "d = HL_Derivation (hlFormula l) (HL_DIffE dm dk)"
      by (auto simp: lookup HL_IffElim lm lk hlFormulaAt_def Let_def split: option.splits)
    note cm = child[OF um lm]
    note ck = child[OF uk lk]
    from rule cm ck   show ?thesis
      by (auto simp: hlTreeRepresents_def tree hlFormulaAt_def lookup
          hlPaperDependencyAt_lookup[OF lookup] hlRuleOK_def HL_IffElim lm lk Let_def
          split: hl_formula.splits hl_term.splits option.splits prod.splits)
  next
    case (HL_QN m)
    obtain lm where lm: "hlLookupLine P m = Some lm"
      using hlRuleOK_cited_exists[OF rule, of m] HL_QN by auto
    from Suc.prems obtain dm where
      um: "hlUnfoldDerivation fuel P m = Some dm"
      and tree: "d = HL_Derivation (hlFormula l) (HL_DQN dm)"
      by (auto simp: lookup HL_QN lm hlFormulaAt_def Let_def split: option.splits)
    note cm = child[OF um lm]
    from rule cm   show ?thesis
      by (auto simp: hlTreeRepresents_def tree hlFormulaAt_def lookup
          hlPaperDependencyAt_lookup[OF lookup] hlRuleOK_def HL_QN lm Let_def
          split: hl_formula.splits hl_term.splits option.splits prod.splits)
  qed
qed


section \<open>The complete source-to-tree guarantee\<close>

theorem hlToDerivation_correct:
  assumes translated: "hlToDerivation P = Some d"
  shows "hlDerivationOK d \<and>
    hlConclusion P = Some (hlDerivationFormula d) \<and>
    set (map snd (hlPremisesOf d)) \<subseteq> set (hlOpenPremises P)"
proof -
  from translated obtain raw where nonempty: "P \<noteq> []"
    and correct: "hlCorrect P"
    and unfolded: "hlUnfoldDerivation (Suc (length P)) P
      (hlLineNumber (last P)) = Some raw"
    and classified: "d = hlClassifyAssumptions {} raw"
    by (auto simp: hlToDerivation_def hlVerifiedCorrect_def
        split: if_splits option.splits)
  have lookup: "hlLookupLine P (hlLineNumber (last P)) = Some (last P)"
    by (rule hlCorrect_lookup_self[OF correct]) (simp add: nonempty)
  have represents: "hlTreeRepresents P (hlLineNumber (last P)) raw"
    by (rule hlUnfoldDerivation_represents[OF correct unfolded])
  have opened: "set (hlOpenAssumptions raw) \<subseteq>
      hlSourceAssumptions P (hlReferences (last P))"
    using represents by (simp add: hlTreeRepresents_def hlPaperDependencyAt_lookup[OF lookup])
  have premise_bound: "set (map snd (hlPremisesOf d)) \<subseteq> set (hlOpenPremises P)"
    using opened hlSourceAssumptions_formulas[of P "hlReferences (last P)"]
    by (auto simp: classified hlClassifyAssumptions_root_premises
        hlOpenPremises_as_assumption_formulas[OF nonempty])
  from represents premise_bound hlToDerivation_conclusion[OF translated] show ?thesis
    by (simp add: hlTreeRepresents_def classified)
qed

theorem hlVerifiedCorrect_toDerivation:
  assumes "hlVerifiedCorrect P" "P \<noteq> []"
  shows "\<exists>d. hlToDerivation P = Some d \<and> hlDerivationOK d \<and>
    hlConclusion P = Some (hlDerivationFormula d) \<and>
    set (map snd (hlPremisesOf d)) \<subseteq> set (hlOpenPremises P)"
  using hlToDerivation_total[OF assms] hlToDerivation_correct by blast

corollary hlPaperCorrect_toDerivation:
  assumes "hlPaperCorrect P" "P \<noteq> []"
  shows "\<exists>d. hlToDerivation P = Some d \<and> hlDerivationOK d \<and>
    hlConclusion P = Some (hlDerivationFormula d) \<and>
    set (map snd (hlPremisesOf d)) \<subseteq> set (hlOpenPremises P)"
  by (rule hlVerifiedCorrect_toDerivation[OF hlPaperCorrect_verified[OF assms(1)] assms(2)])

end
