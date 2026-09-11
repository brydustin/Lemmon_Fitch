theory LF_HLW_Witnesses
  imports LF_HLW_Renaming
begin

section \<open>Simultaneous constant instantiation\<close>

fun hlInstantiateNameTerm :: "(hl_name \<Rightarrow> hl_name option) \<Rightarrow> hl_term \<Rightarrow> hl_term" where
  "hlInstantiateNameTerm rho (HL_Var x) =
    (case rho x of None \<Rightarrow> HL_Var x | Some c \<Rightarrow> HL_Const c)"
| "hlInstantiateNameTerm rho (HL_Const c) = HL_Const c"

fun hlInstantiateNames :: "(hl_name \<Rightarrow> hl_name option) \<Rightarrow> hl_formula \<Rightarrow> hl_formula" where
  "hlInstantiateNames rho (HL_Predicate P ts) = HL_Predicate P (map (hlInstantiateNameTerm rho) ts)"
| "hlInstantiateNames rho (HL_Boolean b) = HL_Boolean b"
| "hlInstantiateNames rho (HL_Not p) = HL_Not (hlInstantiateNames rho p)"
| "hlInstantiateNames rho (HL_And p q) = HL_And (hlInstantiateNames rho p) (hlInstantiateNames rho q)"
| "hlInstantiateNames rho (HL_Or p q) = HL_Or (hlInstantiateNames rho p) (hlInstantiateNames rho q)"
| "hlInstantiateNames rho (HL_Implies p q) = HL_Implies (hlInstantiateNames rho p) (hlInstantiateNames rho q)"
| "hlInstantiateNames rho (HL_Iff p q) = HL_Iff (hlInstantiateNames rho p) (hlInstantiateNames rho q)"
| "hlInstantiateNames rho (HL_ForAll x p) = HL_ForAll x (hlInstantiateNames (rho(x := None)) p)"
| "hlInstantiateNames rho (HL_Exists x p) = HL_Exists x (hlInstantiateNames (rho(x := None)) p)"

lemma hlInstantiateNameTerm_cong:
  "(\<And>x. x \<in> hlVariablesInTerm t \<Longrightarrow> rho x = sigma x) \<Longrightarrow>
   hlInstantiateNameTerm rho t = hlInstantiateNameTerm sigma t"
  by (cases t) auto

lemma hlInstantiateNames_cong:
  "(\<And>x. x \<in> hlFreeVariables p \<Longrightarrow> rho x = sigma x) \<Longrightarrow>
   hlInstantiateNames rho p = hlInstantiateNames sigma p"
proof (induction p arbitrary: rho sigma)
  case (HL_Predicate P ts)
  have terms: "map (hlInstantiateNameTerm rho) ts = map (hlInstantiateNameTerm sigma) ts"
  proof (rule map_cong[OF refl])
    fix t
    assume member: "t \<in> set ts"
    show "hlInstantiateNameTerm rho t = hlInstantiateNameTerm sigma t"
      by (rule hlInstantiateNameTerm_cong) (use member HL_Predicate.prems in auto)
  qed
  then show ?case by simp
next
  case (HL_Boolean b)
  then show ?case by simp
next
  case (HL_Not p)
  have "hlInstantiateNames rho p = hlInstantiateNames sigma p"
    by (rule HL_Not.IH) (use HL_Not.prems in auto)
  then show ?case by simp
next
  case (HL_And p q)
  have left: "hlInstantiateNames rho p = hlInstantiateNames sigma p"
    by (rule HL_And.IH(1)) (use HL_And.prems in auto)
  have right: "hlInstantiateNames rho q = hlInstantiateNames sigma q"
    by (rule HL_And.IH(2)) (use HL_And.prems in auto)
  show ?case by (simp add: left right)
next
  case (HL_Or p q)
  have left: "hlInstantiateNames rho p = hlInstantiateNames sigma p"
    by (rule HL_Or.IH(1)) (use HL_Or.prems in auto)
  have right: "hlInstantiateNames rho q = hlInstantiateNames sigma q"
    by (rule HL_Or.IH(2)) (use HL_Or.prems in auto)
  show ?case by (simp add: left right)
next
  case (HL_Implies p q)
  have left: "hlInstantiateNames rho p = hlInstantiateNames sigma p"
    by (rule HL_Implies.IH(1)) (use HL_Implies.prems in auto)
  have right: "hlInstantiateNames rho q = hlInstantiateNames sigma q"
    by (rule HL_Implies.IH(2)) (use HL_Implies.prems in auto)
  show ?case by (simp add: left right)
next
  case (HL_Iff p q)
  have left: "hlInstantiateNames rho p = hlInstantiateNames sigma p"
    by (rule HL_Iff.IH(1)) (use HL_Iff.prems in auto)
  have right: "hlInstantiateNames rho q = hlInstantiateNames sigma q"
    by (rule HL_Iff.IH(2)) (use HL_Iff.prems in auto)
  show ?case by (simp add: left right)
next
  case (HL_ForAll y p)
  have "hlInstantiateNames (rho(y := None)) p = hlInstantiateNames (sigma(y := None)) p"
    by (rule HL_ForAll.IH) (use HL_ForAll.prems in auto)
  then show ?case by simp
next
  case (HL_Exists y p)
  have "hlInstantiateNames (rho(y := None)) p = hlInstantiateNames (sigma(y := None)) p"
    by (rule HL_Exists.IH) (use HL_Exists.prems in auto)
  then show ?case by simp
qed

lemma hlInstantiateNameTerm_empty [simp]: "hlInstantiateNameTerm (\<lambda>_. None) t = t"
  by (cases t) simp_all

lemma hlInstantiateNames_empty [simp]: "hlInstantiateNames (\<lambda>_. None) p = p"
  by (induction p) (simp_all add: fun_upd_idem map_idI)

lemma hlInstantiateNames_unused:
  "x \<notin> hlFreeVariables p \<Longrightarrow>
   hlInstantiateNames (rho(x := v)) p = hlInstantiateNames rho p"
  by (rule hlInstantiateNames_cong) auto

lemma hlInstantiateNameTerm_after_substitute:
  "hlInstantiateNameTerm rho (hlSubstituteTerm x (HL_Const c) t) =
   hlInstantiateNameTerm (rho(x := Some c)) t"
  by (cases t) auto

lemma hlInstantiateNames_after_substitute:
  "hlInstantiateNames rho (hlSubstituteFree x (HL_Const c) p) =
   hlInstantiateNames (rho(x := Some c)) p"
  by (induction p arbitrary: rho)
     (auto simp: map_map hlInstantiateNameTerm_after_substitute fun_upd_twist
       intro!: map_cong split: if_splits)

lemma hlInstantiateNameTerm_injective:
  "hlInstantiateNameTerm rho t = hlInstantiateNameTerm sigma t \<Longrightarrow>
   x \<in> hlVariablesInTerm t \<Longrightarrow> rho x = sigma x"
  by (cases t) (auto split: option.splits)

lemma hlInstantiateNames_injective:
  "hlInstantiateNames rho p = hlInstantiateNames sigma p \<Longrightarrow>
   x \<in> hlFreeVariables p \<Longrightarrow> rho x = sigma x"
  apply (induction p arbitrary: rho sigma)
  apply (auto simp: map_eq_conv dest: hlInstantiateNameTerm_injective)
  apply (metis fun_upd_other)+
  done

section \<open>Successful witness lists are unique\<close>

lemma hlWitnessLists_instance:
  "cs \<in> set (hlWitnessLists xs p q) \<Longrightarrow>
   hlInstantiateNames (map_of (zip xs cs)) p = q"
proof (induction xs arbitrary: p cs)
  case Nil
  then show ?case by auto
next
  case (Cons x xs)
  show ?case
  proof (cases "x \<in> hlFreeVariables p")
    case False
    from Cons.prems False obtain ds where cs: "cs = STR '''' # ds"
      and ds: "ds \<in> set (hlWitnessLists xs p q)" by auto
    from Cons.IH[OF ds] False cs show ?thesis
      by (simp add: hlInstantiateNames_unused flip: fun_upd_def)
  next
    case True
    from Cons.prems True obtain c ds where cs: "cs = c # ds"
      and ds: "ds \<in> set (hlWitnessLists xs (hlSubstituteFree x (HL_Const c) p) q)"
      by auto
    from Cons.IH[OF ds] cs show ?thesis
      by (simp add: hlInstantiateNames_after_substitute flip: fun_upd_def)
  qed
qed

lemma hlWitnessLists_unique:
  assumes "cs \<in> set (hlWitnessLists xs p q)" "ds \<in> set (hlWitnessLists xs p q)"
  shows "cs = ds"
  using assms
proof (induction xs arbitrary: p cs ds)
  case Nil
  then show ?case by auto
next
  case (Cons x xs)
  show ?case
  proof (cases "x \<in> hlFreeVariables p")
    case False
    from Cons.prems False show ?thesis by (auto intro: Cons.IH)
  next
    case True
    from Cons.prems(1) True obtain a as where cs: "cs = a # as"
      and as: "as \<in> set (hlWitnessLists xs (hlSubstituteFree x (HL_Const a) p) q)" by auto
    from Cons.prems(2) True obtain b bs where ds: "ds = b # bs"
      and bs: "bs \<in> set (hlWitnessLists xs (hlSubstituteFree x (HL_Const b) p) q)" by auto
    have inst_eq: "hlInstantiateNames (map_of (zip (x # xs) cs)) p =
        hlInstantiateNames (map_of (zip (x # xs) ds)) p"
      using hlWitnessLists_instance[OF Cons.prems(1)] hlWitnessLists_instance[OF Cons.prems(2)] by simp
    from hlInstantiateNames_injective[OF inst_eq True] have ab: "a = b" by (simp add: cs ds)
    from Cons.IH[OF as] bs ab show ?thesis by (simp add: cs ds)
  qed
qed

lemma hlInferWitnessConstsK_member:
  "cs \<in> set (hlWitnessLists (take k xs) p q) \<Longrightarrow>
   hlInferWitnessConstsK xs p k q = Some cs"
proof -
  assume member: "cs \<in> set (hlWitnessLists (take k xs) p q)"
  then have nonempty: "hlWitnessLists (take k xs) p q \<noteq> []" by auto
  have "last (hlWitnessLists (take k xs) p q) = cs"
    by (rule hlWitnessLists_unique[OF last_in_set[OF nonempty] member])
  then show ?thesis by (simp add: hlInferWitnessConstsK_def nonempty Let_def)
qed

lemma hlInferWitnessConstsK_rename:
  assumes inferred: "hlInferWitnessConstsK xs p k q = Some cs"
      and marker: "old \<noteq> STR ''''"
      and fresh: "new \<notin> hlConstantsInFormula p" "new \<notin> hlConstantsInFormula q"
  shows "hlInferWitnessConstsK xs (hlRenameFormula old new p) k
      (hlRenameFormula old new q) = Some (map (hlRenameName old new) cs)"
  by (rule hlInferWitnessConstsK_member)
     (rule hlWitnessLists_rename[OF marker fresh hlInferWitnessConstsK_witness[OF inferred]])

end
