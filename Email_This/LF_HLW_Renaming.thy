(* Fresh-name renaming foundations for the exact HL calculus. *)

theory LF_HLW_Renaming
  imports LF_HLW_Unfold
begin

section \<open>Names, terms, and formulas\<close>

definition hlRenameName :: "hl_name \<Rightarrow> hl_name \<Rightarrow> hl_name \<Rightarrow> hl_name" where
  "hlRenameName old new c = (if c = old then new else c)"

lemma hlRenameName_injective_away:
  assumes "new \<notin> S"
  shows "inj_on (hlRenameName old new) S"
  using assms by (auto simp: inj_on_def hlRenameName_def split: if_splits)

lemma hlRenameName_inverse:
  "c \<noteq> new \<Longrightarrow>
   hlRenameName new old (hlRenameName old new c) = c"
  by (auto simp: hlRenameName_def)

lemma hlRenameTerm_const [simp]:
  "hlRenameTerm old new (HL_Const c) = HL_Const (hlRenameName old new c)"
  by (simp add: hlRenameName_def)

lemma hlRenameTerm_variables [simp]:
  "hlVariablesInTerm (hlRenameTerm old new t) = hlVariablesInTerm t"
  by (cases t) simp_all

lemma hlRenameTerm_constants:
  "hlConstantsInTerm (hlRenameTerm old new t) =
   hlRenameName old new ` hlConstantsInTerm t"
  by (cases t) (simp_all add: hlRenameName_def)

lemma hlRenameTerm_is_var [simp]:
  "hlRenameTerm old new t = HL_Var x \<longleftrightarrow> t = HL_Var x"
  by (cases t) simp_all

lemma hlRenameFormula_variables [simp]:
  "hlVariablesInFormula (hlRenameFormula old new p) = hlVariablesInFormula p"
  by (induction p) auto

lemma hlRenameFormula_free_variables [simp]:
  "hlFreeVariables (hlRenameFormula old new p) = hlFreeVariables p"
  by (induction p) auto

lemma hlRenameFormula_constants:
  "hlConstantsInFormula (hlRenameFormula old new p) =
   hlRenameName old new ` hlConstantsInFormula p"
  by (induction p) (auto simp: hlRenameTerm_constants)

lemma hlRenameTerm_fresh_inverse:
  "new \<notin> hlConstantsInTerm t \<Longrightarrow>
   hlRenameTerm new old (hlRenameTerm old new t) = t"
  by (cases t) (auto simp: hlRenameName_inverse)

lemma hlRenameFormula_fresh_inverse:
  "new \<notin> hlConstantsInFormula p \<Longrightarrow>
   hlRenameFormula new old (hlRenameFormula old new p) = p"
  by (induction p)
     (auto simp: map_map hlRenameTerm_fresh_inverse intro!: map_idI)

lemma hlRenameFormula_fresh_injective:
  assumes "new \<notin> hlConstantsInFormula p" "new \<notin> hlConstantsInFormula q"
  shows "hlRenameFormula old new p = hlRenameFormula old new q \<longleftrightarrow> p = q"
  using hlRenameFormula_fresh_inverse[OF assms(1), of old]
    hlRenameFormula_fresh_inverse[OF assms(2), of old] by metis

lemma hlRenameTerm_absent:
  "old \<notin> hlConstantsInTerm t \<Longrightarrow> hlRenameTerm old new t = t"
  by (cases t) (auto simp: hlRenameName_def)

lemma hlRenameFormula_absent:
  "old \<notin> hlConstantsInFormula p \<Longrightarrow> hlRenameFormula old new p = p"
  by (induction p) (auto intro!: map_idI intro: hlRenameTerm_absent)

lemma hlConstantsInTerm_finite [simp]: "finite (hlConstantsInTerm t)"
  by (cases t) simp_all

lemma hlConstantsInFormula_finite [simp]: "finite (hlConstantsInFormula p)"
  by (induction p) simp_all

lemma hlRenameFormula_old_absent:
  "new \<notin> hlConstantsInFormula p \<Longrightarrow>
   old \<notin> hlConstantsInFormula (hlRenameFormula old new p)"
  by (auto simp: hlRenameFormula_constants hlRenameName_def)

section \<open>Free substitution and quantifier prefixes\<close>

lemma hlRenameTerm_substitute:
  "hlRenameTerm old new (hlSubstituteTerm x t u) =
   hlSubstituteTerm x (hlRenameTerm old new t) (hlRenameTerm old new u)"
  by (cases u) auto

lemma hlRenameFormula_substitute:
  "hlRenameFormula old new (hlSubstituteFree x t p) =
   hlSubstituteFree x (hlRenameTerm old new t) (hlRenameFormula old new p)"
  by (induction p)
     (auto simp: map_map hlRenameTerm_substitute intro!: map_cong)

lemma hlSubstituteTerm_constants_subset:
  "hlConstantsInTerm (hlSubstituteTerm x t u) \<subseteq>
   hlConstantsInTerm u \<union> hlConstantsInTerm t"
  by (cases u) auto

lemma hlSubstituteFree_constants_subset:
  "hlConstantsInFormula (hlSubstituteFree x t p) \<subseteq>
   hlConstantsInFormula p \<union> hlConstantsInTerm t"
  by (induction p)
     (auto dest: subsetD[OF hlSubstituteTerm_constants_subset])

lemma hlRenameFormula_free_for_under:
  "hlFreeForUnder B x (hlRenameTerm old new t) (hlRenameFormula old new p) =
   hlFreeForUnder B x t p"
  by (induction p arbitrary: B)
     (auto split: hl_term.splits)

lemma hlRenameFormula_free_for [simp]:
  "hlFreeFor x (hlRenameTerm old new t) (hlRenameFormula old new p) =
   hlFreeFor x t p"
  by (simp add: hlFreeFor_def hlRenameFormula_free_for_under)

lemma hlRenameFormula_collect_foralls:
  "hlCollectForalls (hlRenameFormula old new p) =
   map_prod id (hlRenameFormula old new) (hlCollectForalls p)"
  by (induction p) (auto simp: case_prod_beta)

lemma hlRenameFormula_collect_exists:
  "hlCollectExists (hlRenameFormula old new p) =
   map_prod id (hlRenameFormula old new) (hlCollectExists p)"
  by (induction p) (auto simp: case_prod_beta)

lemma hlRenameFormula_prefix_foralls:
  "hlRenameFormula old new (hlPrefixForalls xs p) =
   hlPrefixForalls xs (hlRenameFormula old new p)"
  unfolding hlPrefixForalls_def by (induction xs) simp_all

lemma hlRenameFormula_prefix_exists:
  "hlRenameFormula old new (hlPrefixExists xs p) =
   hlPrefixExists xs (hlRenameFormula old new p)"
  unfolding hlPrefixExists_def by (induction xs) simp_all

lemma hlRenameFormula_qn_forms:
  "hlQuantifierNegationForms (hlRenameFormula old new p) =
   map (hlRenameFormula old new) (hlQuantifierNegationForms p)"
  by (induction p rule: hlQuantifierNegationForms.induct)
     (simp_all add: map_map)

lemma hlRenameFormula_qn_member:
  "q \<in> set (hlQuantifierNegationForms p) \<Longrightarrow>
   hlRenameFormula old new q \<in>
     set (hlQuantifierNegationForms (hlRenameFormula old new p))"
  by (simp only: hlRenameFormula_qn_forms set_map) blast

lemma hlRenameFormula_qn_reachable:
  assumes "hlQuantifierNegationReachable p q"
  shows "hlQuantifierNegationReachable
     (hlRenameFormula old new p) (hlRenameFormula old new q)"
proof -
  from assms obtain r where p: "p = HL_Not r"
    and mem: "q \<in> set (hlQuantifierNegationForms p)"
    by (cases p) (auto simp: hlQuantifierNegationReachable_def)
  from hlRenameFormula_qn_member[OF mem, of old new] show ?thesis
    by (simp add: hlQuantifierNegationReachable_def p)
qed

lemma hlRenameFormula_qn:
  "hlQuantifierNegationEquivalent p q \<Longrightarrow>
   hlQuantifierNegationEquivalent
     (hlRenameFormula old new p) (hlRenameFormula old new q)"
  unfolding hlQuantifierNegationEquivalent_def
  using hlRenameFormula_qn_reachable by blast

section \<open>Abstraction and equality replacement\<close>

lemma hlRenameTerm_abstract:
  assumes "new \<notin> hlConstantsInTerm t" "c \<noteq> new"
  shows "hlReplaceConstantInTerm (hlRenameName old new c) x
       (hlRenameTerm old new t) =
     hlRenameTerm old new (hlReplaceConstantInTerm c x t)"
  using assms by (cases t) (auto simp: hlRenameName_def)

lemma hlRenameFormula_abstract:
  assumes "new \<notin> hlConstantsInFormula p" "c \<noteq> new"
  shows "hlAbstractConstantFree (hlRenameName old new c) x
       (hlRenameFormula old new p) =
     map_option (hlRenameFormula old new) (hlAbstractConstantFree c x p)"
  using assms
  by (induction p)
     (auto simp: map_map map_option_case hlRenameTerm_abstract split: option.splits
       intro!: map_cong)

lemma hlReplaceConstantInTerm_constants:
  "hlConstantsInTerm (hlReplaceConstantInTerm c x t) =
   hlConstantsInTerm t - {c}"
  by (cases t) auto

lemma hlAbstractConstantFree_constants:
  "hlAbstractConstantFree c x p = Some q \<Longrightarrow>
   hlConstantsInFormula q = hlConstantsInFormula p - {c}"
proof (induction p arbitrary: q)
  case (HL_Predicate P ts)
  then show ?case by (auto simp: hlReplaceConstantInTerm_constants)
next
  case (HL_Boolean b)
  then have "q = HL_Boolean b" by simp
  then show ?case by simp
next
  case (HL_Not p)
  from HL_Not.prems obtain u where u: "hlAbstractConstantFree c x p = Some u"
    and q: "q = HL_Not u"
    by (auto simp: map_option_case split: option.splits if_splits)
  from HL_Not.IH[OF u] show ?case by (simp add: q)
next
  case (HL_And p r)
  from HL_And.prems obtain u v where u: "hlAbstractConstantFree c x p = Some u"
    and v: "hlAbstractConstantFree c x r = Some v" and q: "q = HL_And u v"
    by (auto split: option.splits)
  from HL_And.IH(1)[OF u] HL_And.IH(2)[OF v] show ?case by (auto simp: q)
next
  case (HL_Or p r)
  from HL_Or.prems obtain u v where u: "hlAbstractConstantFree c x p = Some u"
    and v: "hlAbstractConstantFree c x r = Some v" and q: "q = HL_Or u v"
    by (auto split: option.splits)
  from HL_Or.IH(1)[OF u] HL_Or.IH(2)[OF v] show ?case by (auto simp: q)
next
  case (HL_Implies p r)
  from HL_Implies.prems obtain u v where u: "hlAbstractConstantFree c x p = Some u"
    and v: "hlAbstractConstantFree c x r = Some v" and q: "q = HL_Implies u v"
    by (auto split: option.splits)
  from HL_Implies.IH(1)[OF u] HL_Implies.IH(2)[OF v] show ?case by (auto simp: q)
next
  case (HL_Iff p r)
  from HL_Iff.prems obtain u v where u: "hlAbstractConstantFree c x p = Some u"
    and v: "hlAbstractConstantFree c x r = Some v" and q: "q = HL_Iff u v"
    by (auto split: option.splits)
  from HL_Iff.IH(1)[OF u] HL_Iff.IH(2)[OF v] show ?case by (auto simp: q)
next
  case (HL_ForAll y p)
  from HL_ForAll.prems obtain u where u: "hlAbstractConstantFree c x p = Some u"
    and q: "q = HL_ForAll y u"
    by (auto simp: map_option_case split: option.splits if_splits)
  from HL_ForAll.IH[OF u] show ?case by (simp add: q)
next
  case (HL_Exists y p)
  from HL_Exists.prems obtain u where u: "hlAbstractConstantFree c x p = Some u"
    and q: "q = HL_Exists y u"
    by (auto simp: map_option_case split: option.splits if_splits)
  from HL_Exists.IH[OF u] show ?case by (simp add: q)
qed

lemma hlRenameFormula_abstract_many:
  assumes "new \<notin> hlConstantsInFormula p"
      "new \<notin> snd ` set pairs"
  shows "hlAbstractMany (map (map_prod id (hlRenameName old new)) pairs)
       (hlRenameFormula old new p) =
     map_option (hlRenameFormula old new) (hlAbstractMany pairs p)"
  using assms
proof (induction pairs arbitrary: p)
  case Nil
  then show ?case by simp
next
  case (Cons pair pairs)
  obtain x c where pair: "pair = (x,c)" by (cases pair) auto
  have cn: "c \<noteq> new" using Cons.prems(2) pair by auto
  note rename = hlRenameFormula_abstract[OF Cons.prems(1) cn, of old x]
  show ?case
  proof (cases "hlAbstractConstantFree c x p")
    case None
    with Cons.prems pair show ?thesis
      by (simp add: rename)
  next
    case (Some q)
    have fresh: "new \<notin> hlConstantsInFormula q"
      using hlAbstractConstantFree_constants[OF Some] Cons.prems(1) by auto
    from Cons.IH[OF fresh] Cons.prems Some pair show ?thesis
      by (simp add: rename)
  qed
qed

lemma hlRenameTerm_equality_replacement:
  "hlTermEqualUpToConstantReplacement a b t u \<Longrightarrow>
   hlTermEqualUpToConstantReplacement
     (hlRenameName old new a) (hlRenameName old new b)
     (hlRenameTerm old new t) (hlRenameTerm old new u)"
  by (cases t; cases u) (auto simp: hlRenameName_def)

lemma hlRenameTerms_equality_replacement:
  "list_all2 (hlTermEqualUpToConstantReplacement a b) ts us \<Longrightarrow>
   list_all2 (hlTermEqualUpToConstantReplacement
       (hlRenameName old new a) (hlRenameName old new b))
     (map (hlRenameTerm old new) ts) (map (hlRenameTerm old new) us)"
  by (induction rule: list_all2_induct)
     (auto intro: hlRenameTerm_equality_replacement)

lemma hlRenameFormula_equality_replacement:
  "hlEqualUpToConstantReplacement a b p q \<Longrightarrow>
   hlEqualUpToConstantReplacement
     (hlRenameName old new a) (hlRenameName old new b)
     (hlRenameFormula old new p) (hlRenameFormula old new q)"
  by (induction p arbitrary: q)
     (case_tac q; auto intro: hlRenameTerms_equality_replacement)+

section \<open>Witness search without an order assumption\<close>

lemma hlWitnessLists_constants:
  "cs \<in> set (hlWitnessLists xs p q) \<Longrightarrow>
   set cs \<subseteq> insert (STR '''') (hlConstantsInFormula q)"
  apply (induction xs arbitrary: p cs)
  apply (auto split: if_splits)
  apply blast+
  done

lemma hlWitnessLists_rename:
  assumes marker: "old \<noteq> STR ''''"
      and fresh: "new \<notin> hlConstantsInFormula p" "new \<notin> hlConstantsInFormula q"
      and member: "cs \<in> set (hlWitnessLists xs p q)"
  shows "map (hlRenameName old new) cs \<in>
    set (hlWitnessLists xs (hlRenameFormula old new p) (hlRenameFormula old new q))"
  using fresh member
proof (induction xs arbitrary: p q cs)
  case Nil
  then show ?case by auto
next
  case (Cons x xs)
  show ?case
  proof (cases "x \<in> hlFreeVariables p")
    case False
    from Cons.prems(3) False obtain ds where cs: "cs = STR '''' # ds"
      and member: "ds \<in> set (hlWitnessLists xs p q)" by auto
    from Cons.IH[OF Cons.prems(1,2) member] False cs marker show ?thesis
      by (simp add: hlRenameName_def)
  next
    case True
    from Cons.prems(3) True obtain a ds where a: "a \<in> hlConstantsInFormula q"
      and cs: "cs = a # ds"
      and member: "ds \<in> set (hlWitnessLists xs (hlSubstituteFree x (HL_Const a) p) q)"
      by auto
    have fresh_sub: "new \<notin> hlConstantsInFormula (hlSubstituteFree x (HL_Const a) p)"
      using hlSubstituteFree_constants_subset[of x "HL_Const a" p]
        Cons.prems(1,2) a by auto
    have renamed_a: "hlRenameName old new a \<in>
      hlConstantsInFormula (hlRenameFormula old new q)"
      using a by (simp add: hlRenameFormula_constants)
    from Cons.IH[OF fresh_sub Cons.prems(2) member] renamed_a True cs
    show ?thesis
      apply (auto simp: hlRenameFormula_substitute hlRenameName_def)
      apply blast+
      done
  qed
qed

section \<open>Tree shape is unchanged\<close>

lemma hlSizeList_cong:
  "(\<And>x. x \<in> set xs \<Longrightarrow> f x = g x) \<Longrightarrow>
   size_list f xs = size_list g xs"
  by (induction xs) auto

lemma hlRenameDerivation_formula [simp]:
  "hlDerivationFormula (hlRenameDerivation old new d) =
   hlRenameFormula old new (hlDerivationFormula d)"
  by (cases d) simp

lemma hlRenameDerivation_size [simp]:
  "size (hlRenameDerivation old new d) = size d"
  by (induction d rule: hlRenameDerivation.induct)
     (auto simp: map_map comp_def split: hl_derivation_rule.splits
       intro!: hlSizeList_cong)

lemma hlRenameDerivation_formulas:
  "hlDerivationFormulas (hlRenameDerivation old new d) =
   map (hlRenameFormula old new) (hlDerivationFormulas d)"
  by (induction d rule: hlRenameDerivation.induct)
     (auto simp: map_map map_concat comp_def split: hl_derivation_rule.splits
       intro!: arg_cong[where f=concat] map_cong)

lemma hlRepairDerivation_size:
  "hlRepairDerivation base count bad d = (count',pairs,d') \<Longrightarrow>
   size d' = size d"
  by (induction bad arbitrary: count d count' pairs d')
     (auto simp: Let_def split: prod.splits)

lemma hlRenameDerivation_constants:
  "hlDerivationConstants (hlRenameDerivation old new d) =
   hlRenameName old new ` hlDerivationConstants d"
  by (auto simp: hlDerivationConstants_def hlRenameDerivation_formulas
      hlRenameFormula_constants)

end
