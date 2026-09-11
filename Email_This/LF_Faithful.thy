(*  Title:      LF_Faithful.thy

    Towards Conjecture 26.  Definition 21 has two halves: from the Lemmon proof
    to the derivation (Section 5.1), and from the derivation to the Fitch proof
    (Section 5.2).  This theory is the first half: unfolding a correct Lemmon
    proof yields a correct derivation, whose conclusion is the proof's and whose
    open assumptions are, label for label, the dependency set of the last line.

    That last clause is the one that does the work later on: it is what turns
    Lemmon's bookkeeping into the derivation's, and so it is what the side
    conditions of the two systems are compared through.
*)

theory LF_Faithful
  imports LF_Unfold
begin

section \<open>What a correct Lemmon proof says about each of its lines\<close>

text \<open>The checker of Definition 1 reads left to right, so what it establishes at
  a line is stated in terms of the prefix already read.  Everything below wants
  it stated in terms of the whole proof.  Lookup is unchanged by appending,
  provided what is looked up is already there, and every predicate the checker
  uses is built from lookup; so the move costs only the lemmas of this section.\<close>

lemma fmAt_prefix: "lookupLine E m \<noteq> None \<Longrightarrow> fmAt (E @ F) m = fmAt E m"
  by (cases "lookupLine E m") (auto simp: fmAt_def lookupLine_prefix)

lemma justAt_prefix: "lookupLine E m \<noteq> None \<Longrightarrow> justAt (E @ F) m = justAt E m"
  by (cases "lookupLine E m") (auto simp: justAt_def lookupLine_prefix)

lemma depsAt_prefix: "lookupLine E m \<noteq> None \<Longrightarrow> depsAt (E @ F) m = depsAt E m"
  by (cases "lookupLine E m") (auto simp: depsAt_def lookupLine_prefix)

lemma isAssumptionLine_prefix:
  "lookupLine E m \<noteq> None \<Longrightarrow> isAssumptionLine (E @ F) m = isAssumptionLine E m"
  by (simp add: isAssumptionLine_def justAt_prefix)

lemma depsOf_cong:
  assumes "\<And>m. m \<in> set (citedLines j) \<Longrightarrow> look m = look' m"
  shows "depsOf look j self = depsOf look' j self"
  using assms by (cases j) (auto simp: depsOf_def)

text \<open>A rule check inspects the proof only at the lines the justification cites
  --- including, for a discharging rule, the assumption line it names, which the
  justification does cite.  So it too is unchanged by appending.\<close>

lemma ruleOK_prefix:
  assumes "\<forall>m \<in> set (citedLines j). lookupLine E m \<noteq> None"
  shows "ruleOK (E @ F) phi As j = ruleOK E phi As j"
proof -
  have f: "fmAt (E @ F) m = fmAt E m" if "m \<in> set (citedLines j)" for m
    using assms that by (simp add: fmAt_prefix)
  have a: "isAssumptionLine (E @ F) m = isAssumptionLine E m"
    if "m \<in> set (citedLines j)" for m
    using assms that by (simp add: isAssumptionLine_prefix)
  show ?thesis using f a
    by (cases j) (simp_all split: option.splits fm.splits trm.splits)
qed

subsection \<open>Dependency sets name earlier lines\<close>

lemma depsAt_sub:
  assumes "\<forall>l \<in> set E. references l \<subseteq> set (map lineNumber E)"
  shows "depsAt E m \<subseteq> set (map lineNumber E)"
  using assms by (auto simp: depsAt_def split: option.splits dest: lookupLine_Some)

lemma depsOf_sub:
  assumes "\<And>m. look m \<subseteq> S" and "self \<in> S"
  shows "depsOf look j self \<subseteq> S"
  using assms by (cases j) (auto simp: depsOf_def)

text \<open>Only two of the twenty-one rules read the assumption list at all, and
  neither of them is @{const Assumption}: so for those two the dependency set
  names lines strictly earlier, and the list of assumption formulas is the same
  whether it is read off the prefix or off the whole proof.\<close>

definition usesAsms :: "just \<Rightarrow> bool" where
  "usesAsms j \<longleftrightarrow> (\<exists>i. j = ForallIntro i) \<or> (\<exists>m a c. j = ExistsElim m a c)"

lemma depsOf_usesAsms_sub:
  assumes "\<And>m. look m \<subseteq> S" and "usesAsms j"
  shows "depsOf look j self \<subseteq> S"
  using assms by (auto simp: usesAsms_def depsOf_def subset_iff)

text \<open>Stated as an implication rather than an equation: as an equation it is a
  rewrite whose right-hand side matches its own left-hand side, and the
  simplifier loops on it.\<close>

lemma ruleOK_notUsesAsms:
  assumes "\<not> usesAsms j" and "ruleOK E phi As j"
  shows "ruleOK E phi Bs j"
proof -
  from assms(1) have "\<not> (\<exists>i. j = ForallIntro i)"
    and "\<not> (\<exists>m a c. j = ExistsElim m a c)"
    by (auto simp: usesAsms_def)
  then have eq: "ruleOK E phi As j = ruleOK E phi Bs j" by (rule ruleOK_indep)
  show ?thesis using assms(2) eq by simp
qed

section \<open>The facts a correct proof establishes, stated globally\<close>

definition lineFacts :: "lemmon_proof \<Rightarrow> pline \<Rightarrow> bool" where
  "lineFacts Q l \<longleftrightarrow>
     (\<forall>m \<in> set (citedLines (justification l)).
        m < lineNumber l \<and> lookupLine Q m \<noteq> None) \<and>
     references l = depsOf (depsAt Q) (justification l) (lineNumber l) \<and>
     references l \<subseteq> set (map lineNumber Q) \<and>
     ruleOK Q (formula l) (depFms Q (references l)) (justification l)"

lemma depFms_append_notin:
  assumes "\<forall>l \<in> set F. lineNumber l \<notin> G"
  shows "depFms (E @ F) G = depFms E G"
  using assms by (auto simp: depFms_def filter_empty_conv)

lemma checkFrom_lineFacts:
  assumes "sorted_wrt (<) (map lineNumber (E @ P))"
      and "checkFrom_gen depSrc E P"
      and "\<forall>l \<in> set E. references l \<subseteq> set (map lineNumber E)"
  shows "\<forall>l \<in> set P. lineFacts (E @ P) l"
  using assms
proof (induction P arbitrary: E)
  case (Cons l ls)
  let ?j = "justification l"
  let ?n = "lineNumber l"
  let ?Q = "E @ l # ls"

  from Cons.prems(2) have lo: "lineOK_gen depSrc E l"
    and rest: "checkFrom_gen depSrc (E @ [l]) ls" by auto
  from lo have refs: "references l = depsOf (depsAt E) ?j ?n"
    and rok: "ruleOK E (formula l) (depFms E (references l)) ?j"
    by (auto simp: lineOK_gen_def Let_def depSrc_def)
  from lo have cited: "\<forall>m \<in> set (citedLines ?j). lookupLine E m \<noteq> None"
    by (auto simp: lineOK_gen_def Let_def list_all_iff)

  have below: "\<forall>x \<in> set E. lineNumber x < ?n"
    using Cons.prems(1) by (auto simp: sorted_wrt_append)

  text \<open>The citations reach back into the prefix, hence into the whole proof.\<close>
  have C: "\<forall>m \<in> set (citedLines ?j). m < ?n \<and> lookupLine ?Q m \<noteq> None"
  proof
    fix m assume m: "m \<in> set (citedLines ?j)"
    with cited obtain l' where l': "lookupLine E m = Some l'" by auto
    then have "l' \<in> set E" and "lineNumber l' = m" by (auto dest: lookupLine_Some)
    with below have "m < ?n" by auto
    moreover from l' have "lookupLine ?Q m \<noteq> None"
      using lookupLine_prefix [of E m l' "l # ls"] by simp
    ultimately show "m < ?n \<and> lookupLine ?Q m \<noteq> None" ..
  qed

  text \<open>So the dependency arithmetic reads the same off the whole proof.\<close>
  have R: "references l = depsOf (depsAt ?Q) ?j ?n"
  proof -
    have "depsOf (depsAt ?Q) ?j ?n = depsOf (depsAt E) ?j ?n"
    proof (rule depsOf_cong)
      fix m assume "m \<in> set (citedLines ?j)"
      with cited show "depsAt ?Q m = depsAt E m"
        using depsAt_prefix [of E m "l # ls"] by simp
    qed
    with refs show ?thesis by simp
  qed

  have subE: "depsAt E m \<subseteq> set (map lineNumber E)" for m
    by (rule depsAt_sub [OF Cons.prems(3)])
  have S: "references l \<subseteq> set (map lineNumber (E @ [l]))"
    unfolding refs by (rule depsOf_sub) (use subE in auto)

  text \<open>And the rule check does too.  Where the check reads the assumptions, the
    dependency set names lines already in the prefix, so the two readings of the
    assumption list agree; where it does not, there is nothing to agree about.\<close>
  have K: "ruleOK ?Q (formula l) (depFms ?Q (references l)) ?j"
  proof (cases "usesAsms ?j")
    case True
    then have "references l \<subseteq> set (map lineNumber E)"
      unfolding refs by (rule depsOf_usesAsms_sub [OF subE, rotated])
    then have "\<forall>x \<in> set (l # ls). lineNumber x \<notin> references l"
      using Cons.prems(1) by (fastforce simp: sorted_wrt_append)
    then have "depFms ?Q (references l) = depFms E (references l)"
      by (rule depFms_append_notin)
    with rok cited show ?thesis by (simp add: ruleOK_prefix)
  next
    case False
    from rok cited have "ruleOK ?Q (formula l) (depFms E (references l)) ?j"
      by (simp add: ruleOK_prefix)
    with False show ?thesis by (rule ruleOK_notUsesAsms)
  qed

  from C R S K have "lineFacts ?Q l" by (auto simp: lineFacts_def)
  moreover have "\<forall>l' \<in> set ls. lineFacts ?Q l'"
  proof -
    have s: "sorted_wrt (<) (map lineNumber ((E @ [l]) @ ls))" using Cons.prems(1) by simp
    have e: "\<forall>x \<in> set (E @ [l]). references x \<subseteq> set (map lineNumber (E @ [l]))"
      using Cons.prems(3) S by auto
    from Cons.IH [OF s rest e] show ?thesis by simp
  qed
  ultimately show ?case by simp
qed simp

theorem lemmonCorrect_lineFacts:
  assumes "lemmonCorrect P" and "l \<in> set P"
  shows "lineFacts P l"
proof -
  have "\<forall>x \<in> set P. lineFacts ([] @ P) x"
    by (rule checkFrom_lineFacts) (use assms(1) in \<open>simp_all add: lemmonCorrect_def\<close>)
  with assms(2) show ?thesis by simp
qed

section \<open>Unfolding is faithful\<close>

text \<open>The invariant.  Reading the four conjuncts in order: the derivation proves
  the formula the line carries; it is a correct derivation; its open assumptions
  carry exactly the labels of the line's dependency set --- this is the clause
  that turns Lemmon's bookkeeping into the derivation's --- and each label
  carries the formula the source wrote at that line.

  The third and fourth together are what let a side condition proved against
  @{const depFms} be re-proved against @{const openFms}: they say the two lists
  of assumption formulas are the same list, read two ways.\<close>

definition unfoldInv :: "lemmon_proof \<Rightarrow> nat \<Rightarrow> deriv \<Rightarrow> bool" where
  "unfoldInv P n d \<longleftrightarrow>
     fmAt P n = Some (dForm d) \<and>
     derivOK d \<and>
     fst ` set (openAsms d) = depsAt P n \<and>
     (\<forall>nf \<in> set (openAsms d). fmAt P (fst nf) = Some (snd nf))"

lemma unfoldInv_dest:
  assumes "unfoldInv P n d"
  shows "fmAt P n = Some (dForm d)" and "derivOK d"
    and "fst ` set (openAsms d) = depsAt P n"
    and "\<forall>nf \<in> set (openAsms d). fmAt P (fst nf) = Some (snd nf)"
  using assms by (simp_all add: unfoldInv_def)

subsection \<open>Assumption formulas, read two ways\<close>

lemma depFms_mem:
  assumes "fmAt P m = Some f" and "m \<in> G"
  shows "f \<in> set (depFms P G)"
proof -
  from assms(1) obtain l where l: "lookupLine P m = Some l" and f: "formula l = f"
    by (auto simp: fmAt_def)
  from l have "l \<in> set P" and "lineNumber l = m" by (auto dest: lookupLine_Some)
  with assms(2) f show ?thesis by (force simp: depFms_def)
qed

lemma asms_sub_depFms:
  assumes "\<forall>nf \<in> set A. fmAt P (fst nf) = Some (snd nf)"
      and "fst ` set A \<subseteq> G"
  shows "set (map snd A) \<subseteq> set (depFms P G)"
  using assms by (auto intro: depFms_mem)

text \<open>A discharging rule names a label, and every leaf carrying that label
  carries the formula the source wrote there --- which is the assumption the
  rule discharges.  So @{const dischargeOK} comes for free from the fourth
  conjunct.\<close>

lemma dischargeOK_fmAt:
  assumes "\<forall>nf \<in> set (openAsms e). fmAt P (fst nf) = Some (snd nf)"
      and "fmAt P a = Some fa"
  shows "dischargeOK a fa e"
  unfolding dischargeOK_def
proof
  fix nf assume nf: "nf \<in> set (openAsms e)"
  show "fst nf = a \<longrightarrow> snd nf = fa"
  proof
    assume "fst nf = a"
    with assms nf have "fmAt P a = Some (snd nf)" by auto
    with assms(2) show "snd nf = fa" by simp
  qed
qed

subsection \<open>The induction\<close>

text \<open>Twenty-two cases, one for each justification.  Each has the same shape:
  unpack what @{const unfoldD} returned, apply the induction hypothesis to the
  subderivations, read the Lemmon rule check off @{thm [source] lineFacts_def}
  and turn it into the derivation's, and combine the dependency sets.  The two
  quantifier rules are the only ones where the last step is not an equality of
  finite unions but an appeal to antitonicity.\<close>

lemma unfoldD_sound:
  assumes P: "lemmonCorrect P"
  shows "\<forall>n d. unfoldD k P n = Some d \<longrightarrow> unfoldInv P n d"
proof (induction k)
  case 0
  show ?case by simp
next
  case (Suc k)
  show ?case
  proof (intro allI impI)
    fix n d assume u: "unfoldD (Suc k) P n = Some d"
    then obtain l where l: "lookupLine P n = Some l"
      by (cases "lookupLine P n") auto
    then have lp: "l \<in> set P" and ln: "lineNumber l = n" by (auto dest: lookupLine_Some)
    from l have fmn: "fmAt P n = Some (formula l)" by (simp add: fmAt_def)
    from l have dn: "depsAt P n = references l" by (simp add: depsAt_def)
    from lemmonCorrect_lineFacts [OF P lp] ln
    have Fref: "references l = depsOf (depsAt P) (justification l) n"
      and Frok: "ruleOK P (formula l) (depFms P (references l)) (justification l)"
      by (auto simp: lineFacts_def)
    from Fref dn have D: "depsAt P n = depsOf (depsAt P) (justification l) n" by simp

    show "unfoldInv P n d"
    proof (cases "justification l")
      case Assumption
      with D have dpn: "depsAt P n = {n}" by (simp add: depsOf_def)
      show ?thesis
      proof (cases "n \<in> set (dischargedAssumps P)")
        case True
        with l u Assumption have "d = Deriv (formula l) (DAssume n)" by simp
        then show ?thesis using fmn dpn by (simp add: unfoldInv_def)
      next
        case False
        with l u Assumption have "d = Deriv (formula l) (DPremise n)" by simp
        then show ?thesis using fmn dpn by (simp add: unfoldInv_def)
      qed
    next
      case (MP i j)
      with l u obtain e1 e2 where s1: "unfoldD k P i = Some e1"
        and s2: "unfoldD k P j = Some e2"
        and dd: "d = Deriv (formula l) (DMP e1 e2)"
        by (auto split: option.splits)
      from Suc.IH s1 have H1: "unfoldInv P i e1" by blast
      from Suc.IH s2 have H2: "unfoldInv P j e2" by blast
      note I1 = unfoldInv_dest [OF H1] and I2 = unfoldInv_dest [OF H2]
      from D \<open>justification l = MP i j\<close> I1(3) I2(3)
      have as: "fst ` set (openAsms e1) \<union> fst ` set (openAsms e2) = depsAt P n"
        by (simp add: depsOf_def)
      from Frok \<open>justification l = MP i j\<close> I1(1) I2(1)
      have rl: "dForm e1 = Impl (dForm e2) (formula l)" by (auto split: fm.splits)
      show ?thesis using dd fmn I1(2) I2(2) I1(4) I2(4) as rl
        by (simp add: unfoldInv_def image_Un ball_Un)
    next
      case (CP a c)
      with l u obtain g1 e1 where fa: "fmAt P a = Some g1"
        and s1: "unfoldD k P c = Some e1"
        and dd: "d = Deriv (formula l) (DCP a g1 e1)"
        by (auto split: option.splits)
      from Suc.IH s1 have H1: "unfoldInv P c e1" by blast
      note I1 = unfoldInv_dest [OF H1]
      from Frok \<open>justification l = CP a c\<close> fa I1(1)
      have rl: "formula l = Impl g1 (dForm e1)" by simp
      from I1(4) fa have disch: "dischargeOK a g1 e1" by (rule dischargeOK_fmAt)
      from D \<open>justification l = CP a c\<close> I1(3)
      have as: "fst ` set (openAsms e1) - {a} = depsAt P n" by (simp add: depsOf_def)
      show ?thesis using dd fmn I1(2) I1(4) as rl disch
        by (auto simp: unfoldInv_def)
    next
      case (RAA a c)
      with l u obtain g1 e1 where fa: "fmAt P a = Some g1"
        and s1: "unfoldD k P c = Some e1"
        and dd: "d = Deriv (formula l) (DRAA a g1 e1)"
        by (auto split: option.splits)
      from Suc.IH s1 have H1: "unfoldInv P c e1" by blast
      note I1 = unfoldInv_dest [OF H1]
      from Frok \<open>justification l = RAA a c\<close> fa I1(1)
      have rl: "formula l = Neg g1" and bot: "dForm e1 = Bot" by simp_all
      from I1(4) fa have disch: "dischargeOK a g1 e1" by (rule dischargeOK_fmAt)
      from D \<open>justification l = RAA a c\<close> I1(3)
      have as: "fst ` set (openAsms e1) - {a} = depsAt P n" by (simp add: depsOf_def)
      show ?thesis using dd fmn I1(2) I1(4) as rl bot disch
        by (auto simp: unfoldInv_def)
    next
      case (DN i)
      with l u obtain e1 where s1: "unfoldD k P i = Some e1"
        and dd: "d = Deriv (formula l) (DDN e1)"
        by (auto split: option.splits)
      from Suc.IH s1 have H1: "unfoldInv P i e1" by blast
      note I1 = unfoldInv_dest [OF H1]
      from D \<open>justification l = DN i\<close> I1(3)
      have as: "fst ` set (openAsms e1) = depsAt P n" by (simp add: depsOf_def)
      from Frok \<open>justification l = DN i\<close> I1(1)
      have rl: "dForm e1 = Neg (Neg (formula l))" by simp
      show ?thesis using dd fmn I1(2) I1(4) as rl
        by (simp add: unfoldInv_def)
    next
      case (BotI i j)
      with l u obtain e1 e2 where s1: "unfoldD k P i = Some e1"
        and s2: "unfoldD k P j = Some e2"
        and dd: "d = Deriv (formula l) (DBotI e1 e2)"
        by (auto split: option.splits)
      from Suc.IH s1 have H1: "unfoldInv P i e1" by blast
      from Suc.IH s2 have H2: "unfoldInv P j e2" by blast
      note I1 = unfoldInv_dest [OF H1] and I2 = unfoldInv_dest [OF H2]
      from D \<open>justification l = BotI i j\<close> I1(3) I2(3)
      have as: "fst ` set (openAsms e1) \<union> fst ` set (openAsms e2) = depsAt P n"
        by (simp add: depsOf_def)
      from Frok \<open>justification l = BotI i j\<close> I1(1) I2(1)
      have rl: "formula l = Bot" and rl2: "dForm e2 = Neg (dForm e1)" by simp_all
      show ?thesis using dd fmn I1(2) I2(2) I1(4) I2(4) as rl rl2
        by (simp add: unfoldInv_def image_Un ball_Un)
    next
      case (AndIntro i j)
      with l u obtain e1 e2 where s1: "unfoldD k P i = Some e1"
        and s2: "unfoldD k P j = Some e2"
        and dd: "d = Deriv (formula l) (DAndIntro e1 e2)"
        by (auto split: option.splits)
      from Suc.IH s1 have H1: "unfoldInv P i e1" by blast
      from Suc.IH s2 have H2: "unfoldInv P j e2" by blast
      note I1 = unfoldInv_dest [OF H1] and I2 = unfoldInv_dest [OF H2]
      from D \<open>justification l = AndIntro i j\<close> I1(3) I2(3)
      have as: "fst ` set (openAsms e1) \<union> fst ` set (openAsms e2) = depsAt P n"
        by (simp add: depsOf_def)
      from Frok \<open>justification l = AndIntro i j\<close> I1(1) I2(1)
      have rl: "formula l = Conj (dForm e1) (dForm e2)" by (auto split: fm.splits)
      show ?thesis using dd fmn I1(2) I2(2) I1(4) I2(4) as rl
        by (simp add: unfoldInv_def image_Un ball_Un)
    next
      case (AndElimL i)
      with l u obtain e1 where s1: "unfoldD k P i = Some e1"
        and dd: "d = Deriv (formula l) (DAndElimL e1)"
        by (auto split: option.splits)
      from Suc.IH s1 have H1: "unfoldInv P i e1" by blast
      note I1 = unfoldInv_dest [OF H1]
      from D \<open>justification l = AndElimL i\<close> I1(3)
      have as: "fst ` set (openAsms e1) = depsAt P n" by (simp add: depsOf_def)
      obtain p q where rl: "dForm e1 = Conj p q" and rl2: "formula l = p"
        using Frok \<open>justification l = AndElimL i\<close> I1(1) by (cases "dForm e1") auto
      show ?thesis using dd fmn I1(2) I1(4) as rl rl2
        by (simp add: unfoldInv_def)
    next
      case (AndElimR i)
      with l u obtain e1 where s1: "unfoldD k P i = Some e1"
        and dd: "d = Deriv (formula l) (DAndElimR e1)"
        by (auto split: option.splits)
      from Suc.IH s1 have H1: "unfoldInv P i e1" by blast
      note I1 = unfoldInv_dest [OF H1]
      from D \<open>justification l = AndElimR i\<close> I1(3)
      have as: "fst ` set (openAsms e1) = depsAt P n" by (simp add: depsOf_def)
      obtain p q where rl: "dForm e1 = Conj p q" and rl2: "formula l = q"
        using Frok \<open>justification l = AndElimR i\<close> I1(1) by (cases "dForm e1") auto
      show ?thesis using dd fmn I1(2) I1(4) as rl rl2
        by (simp add: unfoldInv_def)
    next
      case (OrIntroL i)
      with l u obtain e1 where s1: "unfoldD k P i = Some e1"
        and dd: "d = Deriv (formula l) (DOrIntroL e1)"
        by (auto split: option.splits)
      from Suc.IH s1 have H1: "unfoldInv P i e1" by blast
      note I1 = unfoldInv_dest [OF H1]
      from D \<open>justification l = OrIntroL i\<close> I1(3)
      have as: "fst ` set (openAsms e1) = depsAt P n" by (simp add: depsOf_def)
      obtain p q where rl: "formula l = Disj p q" and rl2: "dForm e1 = p"
        using Frok \<open>justification l = OrIntroL i\<close> I1(1) by (cases "formula l") auto
      show ?thesis using dd fmn I1(2) I1(4) as rl rl2
        by (simp add: unfoldInv_def)
    next
      case (OrIntroR i)
      with l u obtain e1 where s1: "unfoldD k P i = Some e1"
        and dd: "d = Deriv (formula l) (DOrIntroR e1)"
        by (auto split: option.splits)
      from Suc.IH s1 have H1: "unfoldInv P i e1" by blast
      note I1 = unfoldInv_dest [OF H1]
      from D \<open>justification l = OrIntroR i\<close> I1(3)
      have as: "fst ` set (openAsms e1) = depsAt P n" by (simp add: depsOf_def)
      obtain p q where rl: "formula l = Disj p q" and rl2: "dForm e1 = q"
        using Frok \<open>justification l = OrIntroR i\<close> I1(1) by (cases "formula l") auto
      show ?thesis using dd fmn I1(2) I1(4) as rl rl2
        by (simp add: unfoldInv_def)
    next
      case (OrElim d0 a1 c1 a2 c2)
      with l u obtain e0 g1 e2 g2 e3 where
        s0: "unfoldD k P d0 = Some e0" and fa1: "fmAt P a1 = Some g1"
        and s2: "unfoldD k P c1 = Some e2" and fa2: "fmAt P a2 = Some g2"
        and s3: "unfoldD k P c2 = Some e3"
        and dd: "d = Deriv (formula l) (DOrElim e0 a1 g1 e2 a2 g2 e3)"
        by (auto split: option.splits)
      from Suc.IH s0 have H0: "unfoldInv P d0 e0" by blast
      from Suc.IH s2 have H2: "unfoldInv P c1 e2" by blast
      from Suc.IH s3 have H3: "unfoldInv P c2 e3" by blast
      note I0 = unfoldInv_dest [OF H0] and I2 = unfoldInv_dest [OF H2]
        and I3 = unfoldInv_dest [OF H3]
      from Frok \<open>justification l = OrElim d0 a1 c1 a2 c2\<close> I0(1) I2(1) I3(1) fa1 fa2
      have rl: "dForm e0 = Disj g1 g2" and rl2: "dForm e2 = formula l"
        and rl3: "dForm e3 = formula l" by (auto split: fm.splits)
      from I2(4) fa1 have disch1: "dischargeOK a1 g1 e2" by (rule dischargeOK_fmAt)
      from I3(4) fa2 have disch2: "dischargeOK a2 g2 e3" by (rule dischargeOK_fmAt)
      from D \<open>justification l = OrElim d0 a1 c1 a2 c2\<close> I0(3) I2(3) I3(3)
      have as: "fst ` set (openAsms e0) \<union> (fst ` set (openAsms e2) - {a1})
                  \<union> (fst ` set (openAsms e3) - {a2}) = depsAt P n"
        by (simp add: depsOf_def)
      show ?thesis using dd fmn I0(2) I2(2) I3(2) I0(4) I2(4) I3(4) as
                         rl rl2 rl3 disch1 disch2
        by (auto simp: unfoldInv_def image_Un)
    next
      case (IffIntro i j)
      with l u obtain e1 e2 where s1: "unfoldD k P i = Some e1"
        and s2: "unfoldD k P j = Some e2"
        and dd: "d = Deriv (formula l) (DIffIntro e1 e2)"
        by (auto split: option.splits)
      from Suc.IH s1 have H1: "unfoldInv P i e1" by blast
      from Suc.IH s2 have H2: "unfoldInv P j e2" by blast
      note I1 = unfoldInv_dest [OF H1] and I2 = unfoldInv_dest [OF H2]
      from D \<open>justification l = IffIntro i j\<close> I1(3) I2(3)
      have as: "fst ` set (openAsms e1) \<union> fst ` set (openAsms e2) = depsAt P n"
        by (simp add: depsOf_def)
      obtain p q where fl: "formula l = Iff p q"
        using Frok \<open>justification l = IffIntro i j\<close> by (cases "formula l") auto
      with Frok \<open>justification l = IffIntro i j\<close> I1(1) I2(1)
      have rl: "dForm e1 = Impl p q" and rl2: "dForm e2 = Impl q p" by simp_all
      show ?thesis using dd fmn I1(2) I2(2) I1(4) I2(4) as fl rl rl2
        by (simp add: unfoldInv_def image_Un ball_Un)
    next
      case (IffElimL i)
      with l u obtain e1 where s1: "unfoldD k P i = Some e1"
        and dd: "d = Deriv (formula l) (DIffElimL e1)"
        by (auto split: option.splits)
      from Suc.IH s1 have H1: "unfoldInv P i e1" by blast
      note I1 = unfoldInv_dest [OF H1]
      from D \<open>justification l = IffElimL i\<close> I1(3)
      have as: "fst ` set (openAsms e1) = depsAt P n" by (simp add: depsOf_def)
      obtain p q where fl: "formula l = Impl p q" and rl: "dForm e1 = Iff p q"
        using Frok \<open>justification l = IffElimL i\<close> I1(1) by (cases "formula l") auto
      show ?thesis using dd fmn I1(2) I1(4) as fl rl
        by (simp add: unfoldInv_def)
    next
      case (IffElimR i)
      with l u obtain e1 where s1: "unfoldD k P i = Some e1"
        and dd: "d = Deriv (formula l) (DIffElimR e1)"
        by (auto split: option.splits)
      from Suc.IH s1 have H1: "unfoldInv P i e1" by blast
      note I1 = unfoldInv_dest [OF H1]
      from D \<open>justification l = IffElimR i\<close> I1(3)
      have as: "fst ` set (openAsms e1) = depsAt P n" by (simp add: depsOf_def)
      obtain p q where fl: "formula l = Impl q p" and rl: "dForm e1 = Iff p q"
        using Frok \<open>justification l = IffElimR i\<close> I1(1) by (cases "formula l") auto
      show ?thesis using dd fmn I1(2) I1(4) as fl rl
        by (simp add: unfoldInv_def)
    next
      case (ForallElim i)
      with l u obtain e1 where s1: "unfoldD k P i = Some e1"
        and dd: "d = Deriv (formula l) (DForallElim e1)"
        by (auto split: option.splits)
      from Suc.IH s1 have H1: "unfoldInv P i e1" by blast
      note I1 = unfoldInv_dest [OF H1]
      from D \<open>justification l = ForallElim i\<close> I1(3)
      have as: "fst ` set (openAsms e1) = depsAt P n" by (simp add: depsOf_def)
      obtain x p where rl: "dForm e1 = Uni x p" and rl2: "instOK x p (formula l)"
        using Frok \<open>justification l = ForallElim i\<close> I1(1) by (cases "dForm e1") auto
      show ?thesis using dd fmn I1(2) I1(4) as rl rl2
        by (simp add: unfoldInv_def)
    next
      case (ForallIntro i)
      with l u obtain e1 where s1: "unfoldD k P i = Some e1"
        and dd: "d = Deriv (formula l) (DForallIntro e1)"
        by (auto split: option.splits)
      from Suc.IH s1 have H1: "unfoldInv P i e1" by blast
      note I1 = unfoldInv_dest [OF H1]
      from D \<open>justification l = ForallIntro i\<close> I1(3)
      have as: "fst ` set (openAsms e1) = depsAt P n" by (simp add: depsOf_def)
      from Fref \<open>justification l = ForallIntro i\<close> I1(3)
      have refs: "fst ` set (openAsms e1) \<subseteq> references l" by (simp add: depsOf_def)
      have sub: "set (openFms e1) \<subseteq> set (depFms P (references l))"
        by (rule asms_sub_depFms [OF I1(4) refs])
      obtain x p where fl: "formula l = Uni x p"
        using Frok \<open>justification l = ForallIntro i\<close> by (cases "formula l") auto
      with Frok \<open>justification l = ForallIntro i\<close> I1(1)
      have g: "genOK x p (dForm e1) (depFms P (references l))" by simp
      from genOK_antitone [OF sub g] have rl: "genOK x p (dForm e1) (openFms e1)" .
      show ?thesis using dd fmn I1(2) I1(4) as fl rl
        by (simp add: unfoldInv_def)
    next
      case (ExistsIntro i)
      with l u obtain e1 where s1: "unfoldD k P i = Some e1"
        and dd: "d = Deriv (formula l) (DExistsIntro e1)"
        by (auto split: option.splits)
      from Suc.IH s1 have H1: "unfoldInv P i e1" by blast
      note I1 = unfoldInv_dest [OF H1]
      from D \<open>justification l = ExistsIntro i\<close> I1(3)
      have as: "fst ` set (openAsms e1) = depsAt P n" by (simp add: depsOf_def)
      obtain x p where fl: "formula l = Exi x p" and rl: "instOK x p (dForm e1)"
        using Frok \<open>justification l = ExistsIntro i\<close> I1(1) by (cases "formula l") auto
      show ?thesis using dd fmn I1(2) I1(4) as fl rl
        by (simp add: unfoldInv_def)
    next
      case (ExistsElim m a c)
      with l u obtain e0 g1 e2 where
        s0: "unfoldD k P m = Some e0" and fa: "fmAt P a = Some g1"
        and s2: "unfoldD k P c = Some e2"
        and dd: "d = Deriv (formula l) (DExistsElim e0 a g1 e2)"
        by (auto split: option.splits)
      from Suc.IH s0 have H0: "unfoldInv P m e0" by blast
      from Suc.IH s2 have H2: "unfoldInv P c e2" by blast
      note I0 = unfoldInv_dest [OF H0] and I2 = unfoldInv_dest [OF H2]
      from I2(4) fa have disch: "dischargeOK a g1 e2" by (rule dischargeOK_fmAt)
      from Frok \<open>justification l = ExistsElim m a c\<close> I2(1)
      have rl2: "dForm e2 = formula l" by simp

      text \<open>The two dependency sets the rule pools, and the assumption list they
        make up.\<close>
      from Fref \<open>justification l = ExistsElim m a c\<close> I0(3)
      have refs0: "fst ` set (openAsms e0) \<subseteq> references l" by (simp add: depsOf_def)
      from Fref \<open>justification l = ExistsElim m a c\<close> I2(3)
      have refs2: "fst ` set (drop_label a (openAsms e2)) \<subseteq> references l"
        by (auto simp: depsOf_def)
      have sub: "set (openFms e0 @ map snd (drop_label a (openAsms e2)))
                   \<subseteq> set (depFms P (references l))"
      proof -
        have "set (openFms e0) \<subseteq> set (depFms P (references l))"
          by (rule asms_sub_depFms [OF I0(4) refs0])
        moreover have "set (map snd (drop_label a (openAsms e2)))
                         \<subseteq> set (depFms P (references l))"
          by (rule asms_sub_depFms [OF _ refs2]) (use I2(4) in auto)
        ultimately show ?thesis by simp
      qed

      obtain x p where e0f: "dForm e0 = Exi x p"
        using Frok \<open>justification l = ExistsElim m a c\<close> I0(1) by (cases "dForm e0") auto
      with Frok \<open>justification l = ExistsElim m a c\<close> I0(1) fa
      have w: "witOK x p g1 (formula l) (depFms P (references l))" by simp
      from witOK_antitone [OF sub w]
      have rl: "witOK x p g1 (formula l)
                  (openFms e0 @ map snd (drop_label a (openAsms e2)))" .

      from D \<open>justification l = ExistsElim m a c\<close> I0(3) I2(3)
      have as: "fst ` set (openAsms e0) \<union> (fst ` set (openAsms e2) - {a}) = depsAt P n"
        by (simp add: depsOf_def)
      show ?thesis using dd fmn I0(2) I2(2) I0(4) I2(4) as rl rl2 disch e0f
        by (auto simp: unfoldInv_def image_Un)
    next
      case EqIntro
      with l u have dd: "d = Deriv (formula l) DEqIntro" by simp
      from Frok EqIntro have rl: "ruleOK P (formula l) (depFms P (references l)) EqIntro"
        by simp
      from D EqIntro have as: "depsAt P n = {}" by (simp add: depsOf_def)
      show ?thesis using dd fmn as rl
        by (cases "formula l"; simp add: unfoldInv_def)
    next
      case (EqElim i j)
      with l u obtain e1 e2 where s1: "unfoldD k P i = Some e1"
        and s2: "unfoldD k P j = Some e2"
        and dd: "d = Deriv (formula l) (DEqElim e1 e2)"
        by (auto split: option.splits)
      from Suc.IH s1 have H1: "unfoldInv P i e1" by blast
      from Suc.IH s2 have H2: "unfoldInv P j e2" by blast
      note I1 = unfoldInv_dest [OF H1] and I2 = unfoldInv_dest [OF H2]
      from D \<open>justification l = EqElim i j\<close> I1(3) I2(3)
      have as: "fst ` set (openAsms e1) \<union> fst ` set (openAsms e2) = depsAt P n"
        by (simp add: depsOf_def)
      obtain a b where rl: "dForm e1 = Eqf (Nm a) (Nm b)"
        and rl2: "eqsub a b (dForm e2) (formula l)"
        using Frok \<open>justification l = EqElim i j\<close> I1(1) I2(1)
        by (cases "dForm e1") (auto split: trm.splits)
      show ?thesis using dd fmn I1(2) I2(2) I1(4) I2(4) as rl rl2
        by (simp add: unfoldInv_def image_Un ball_Un)
    next
      case (Reit i)
      with l u obtain e1 where s1: "unfoldD k P i = Some e1"
        and dd: "d = Deriv (formula l) (DReit e1)"
        by (auto split: option.splits)
      from Suc.IH s1 have H1: "unfoldInv P i e1" by blast
      note I1 = unfoldInv_dest [OF H1]
      from D \<open>justification l = Reit i\<close> I1(3)
      have as: "fst ` set (openAsms e1) = depsAt P n" by (simp add: depsOf_def)
      from Frok \<open>justification l = Reit i\<close> I1(1) have rl: "dForm e1 = formula l" by simp
      show ?thesis using dd fmn I1(2) I1(4) as rl
        by (simp add: unfoldInv_def)
    qed
  qed
qed


section \<open>The first half of Definition 21\<close>

text \<open>Unfolding a correct Lemmon proof of \<open>\<Gamma> \<turnstile>\<^sub>L \<psi>\<close> yields a correct derivation
  of \<open>\<Gamma> \<turnstile>\<^sub>L \<psi>\<close>: its open assumptions are labelled by the dependency set of the
  last line and carry the formulas the source wrote at those lines, and its root
  is the proof's conclusion.  (The sequent form, \<open>unfolding_sequent\<close>, is stated
  in \<open>LF_Conjecture\<close>, where the turnstile on the Fitch side is available too.)

  Together with @{thm [source] unfolding_terminates}, which says the unfolding
  is defined, this is everything Section 5.1 claims.  What remains of
  Conjecture 26 is Section 5.2: that the traversal of such a derivation is a
  correct Fitch proof.\<close>

theorem toDerivation_sound:
  assumes P: "lemmonCorrect P" and ne: "P \<noteq> []" and d: "toDerivation P = Inr d"
  shows "derivOK d"
    and "conclusion P = Some (dForm d)"
    and "fst ` set (openAsms d) = references (last P)"
    and "\<forall>nf \<in> set (openAsms d). fmAt P (fst nf) = Some (snd nf)"
proof -
  from d have uf: "unfoldD (Suc (rootLine P)) P (rootLine P) = Some d"
    by (auto simp: toDerivation_def split: option.splits if_splits)
  from unfoldD_sound [OF P] uf have inv: "unfoldInv P (rootLine P) d" by blast
  note I = unfoldInv_dest [OF inv]

  from P have "distinct (map lineNumber P)"
    by (simp add: lemmonCorrect_def sorted_wrt_less_distinct)
  moreover from ne have "last P \<in> set P" by simp
  ultimately have lk: "lookupLine P (rootLine P) = Some (last P)"
    using ne by (simp add: rootLine_def lookupLine_mem)

  from lk have "fmAt P (rootLine P) = Some (formula (last P))" by (simp add: fmAt_def)
  with I(1) have cc: "formula (last P) = dForm d" by simp

  show "derivOK d" by (rule I(2))
  show "conclusion P = Some (dForm d)" using ne cc by (simp add: conclusion_def)
  from lk have "depsAt P (rootLine P) = references (last P)" by (simp add: depsAt_def)
  with I(3) show "fst ` set (openAsms d) = references (last P)" by simp
  show "\<forall>nf \<in> set (openAsms d). fmAt P (fst nf) = Some (snd nf)" by (rule I(4))
qed

corollary unfolding_yields_correct_derivation:
  assumes "lemmonCorrect P" and "P \<noteq> []"
  shows "\<exists>d. toDerivation P = Inr d \<and> derivOK d \<and> conclusion P = Some (dForm d)"
proof -
  from unfolding_terminates [OF assms] obtain d where d: "toDerivation P = Inr d" by blast
  with toDerivation_sound [OF assms d] show ?thesis by blast
qed

end
