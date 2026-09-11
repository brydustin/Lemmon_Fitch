(*  Title:      LF_Unfold.thy

    Definition 21 of the paper, with the renaming repair of Section 5.4.

    When no scope tree permits every citation the source makes -- which is
    Theorem 10 -- one may unfold.  Unfolding removes sharing, and a DAG without
    sharing is a tree; a tree imposes no constraint that could be violated,
    since nothing is shared to be shared wrongly.

    Two functions and a choice between them: the positional translation of
    LF_Direct is attempted first, because it preserves numbering and structure,
    and the unfolding is the fallback.
*)

theory LF_Unfold
  imports LF_Derivation
begin

section \<open>Unfolding the citation graph\<close>

text \<open>Where the Lemmon justification names line numbers, the derivation names
  subderivations, and a line cited twice becomes two subtrees.  The recursion is
  on the line number, which strictly decreases along every citation; the fuel
  parameter makes that visible to the definition, and lemma \<open>L1\<close> below discharges
  it.\<close>

definition rootLine :: "lemmon_proof \<Rightarrow> nat" where
  "rootLine P = (if P = [] then 0 else lineNumber (last P))"

fun unfoldD :: "nat \<Rightarrow> lemmon_proof \<Rightarrow> nat \<Rightarrow> deriv option" where
  "unfoldD 0 P n = None"
| "unfoldD (Suc k) P n =
     (case lookupLine P n of
        None \<Rightarrow> None
      | Some l \<Rightarrow>
        (case justification l of
           Assumption \<Rightarrow> Some (Deriv (formula l)
                          (if n \<in> set (dischargedAssumps P) then DAssume n else DPremise n))
         | MP i j \<Rightarrow> (case (unfoldD k P i, unfoldD k P j) of
                       (Some e0, Some e1) \<Rightarrow> Some (Deriv (formula l) (DMP e0 e1)) | _ \<Rightarrow> None)
         | CP a c \<Rightarrow> (case (fmAt P a, unfoldD k P c) of
                       (Some g0, Some e1) \<Rightarrow> Some (Deriv (formula l) (DCP a g0 e1)) | _ \<Rightarrow> None)
         | RAA a c \<Rightarrow> (case (fmAt P a, unfoldD k P c) of
                       (Some g0, Some e1) \<Rightarrow> Some (Deriv (formula l) (DRAA a g0 e1)) | _ \<Rightarrow> None)
         | DN i \<Rightarrow> (case unfoldD k P i of
                       Some e0 \<Rightarrow> Some (Deriv (formula l) (DDN e0)) | _ \<Rightarrow> None)
         | BotI i j \<Rightarrow> (case (unfoldD k P i, unfoldD k P j) of
                       (Some e0, Some e1) \<Rightarrow> Some (Deriv (formula l) (DBotI e0 e1)) | _ \<Rightarrow> None)
         | AndIntro i j \<Rightarrow> (case (unfoldD k P i, unfoldD k P j) of
                       (Some e0, Some e1) \<Rightarrow> Some (Deriv (formula l) (DAndIntro e0 e1)) | _ \<Rightarrow> None)
         | AndElimL i \<Rightarrow> (case unfoldD k P i of
                       Some e0 \<Rightarrow> Some (Deriv (formula l) (DAndElimL e0)) | _ \<Rightarrow> None)
         | AndElimR i \<Rightarrow> (case unfoldD k P i of
                       Some e0 \<Rightarrow> Some (Deriv (formula l) (DAndElimR e0)) | _ \<Rightarrow> None)
         | OrIntroL i \<Rightarrow> (case unfoldD k P i of
                       Some e0 \<Rightarrow> Some (Deriv (formula l) (DOrIntroL e0)) | _ \<Rightarrow> None)
         | OrIntroR i \<Rightarrow> (case unfoldD k P i of
                       Some e0 \<Rightarrow> Some (Deriv (formula l) (DOrIntroR e0)) | _ \<Rightarrow> None)
         | OrElim d a1 c1 a2 c2 \<Rightarrow> (case (unfoldD k P d, fmAt P a1, unfoldD k P c1, fmAt P a2, unfoldD k P c2) of
                       (Some e0, Some g1, Some e2, Some g3, Some e4) \<Rightarrow> Some (Deriv (formula l) (DOrElim e0 a1 g1 e2 a2 g3 e4)) | _ \<Rightarrow> None)
         | IffIntro i j \<Rightarrow> (case (unfoldD k P i, unfoldD k P j) of
                       (Some e0, Some e1) \<Rightarrow> Some (Deriv (formula l) (DIffIntro e0 e1)) | _ \<Rightarrow> None)
         | IffElimL i \<Rightarrow> (case unfoldD k P i of
                       Some e0 \<Rightarrow> Some (Deriv (formula l) (DIffElimL e0)) | _ \<Rightarrow> None)
         | IffElimR i \<Rightarrow> (case unfoldD k P i of
                       Some e0 \<Rightarrow> Some (Deriv (formula l) (DIffElimR e0)) | _ \<Rightarrow> None)
         | ForallElim i \<Rightarrow> (case unfoldD k P i of
                       Some e0 \<Rightarrow> Some (Deriv (formula l) (DForallElim e0)) | _ \<Rightarrow> None)
         | ForallIntro i \<Rightarrow> (case unfoldD k P i of
                       Some e0 \<Rightarrow> Some (Deriv (formula l) (DForallIntro e0)) | _ \<Rightarrow> None)
         | ExistsIntro i \<Rightarrow> (case unfoldD k P i of
                       Some e0 \<Rightarrow> Some (Deriv (formula l) (DExistsIntro e0)) | _ \<Rightarrow> None)
         | ExistsElim m a c \<Rightarrow> (case (unfoldD k P m, fmAt P a, unfoldD k P c) of
                       (Some e0, Some g1, Some e2) \<Rightarrow> Some (Deriv (formula l) (DExistsElim e0 a g1 e2)) | _ \<Rightarrow> None)
         | EqIntro \<Rightarrow> Some (Deriv (formula l) DEqIntro)
         | EqElim i j \<Rightarrow> (case (unfoldD k P i, unfoldD k P j) of
                       (Some e0, Some e1) \<Rightarrow> Some (Deriv (formula l) (DEqElim e0 e1)) | _ \<Rightarrow> None)
         | Reit i \<Rightarrow> (case unfoldD k P i of
                       Some e0 \<Rightarrow> Some (Deriv (formula l) (DReit e0)) | _ \<Rightarrow> None)
         ))"

definition toDerivation :: "lemmon_proof \<Rightarrow> translation_error + deriv" where
  "toDerivation P =
     (if P = [] \<or> \<not> lemmonCorrect P then Inl (NotCorrect 0)
      else case unfoldD (Suc (rootLine P)) P (rootLine P) of
             None \<Rightarrow> Inl (NotCorrect (rootLine P))
           | Some d \<Rightarrow> Inr d)"

subsection \<open>(L1) Unfolding terminates\<close>

text \<open>``A line may cite only lines with smaller numbers, so the recursion is
  well-founded on the line number, and the derivation is finite.''  In the
  present formulation finiteness is free --- a @{typ deriv} is a finite tree by
  construction --- and what wants proving is that the fuel never runs out.\<close>

definition citesDown :: "lemmon_proof \<Rightarrow> bool" where
  "citesDown P \<longleftrightarrow>
     (\<forall>l \<in> set P. \<forall>m \<in> set (citedLines (justification l)).
        m < lineNumber l \<and> lookupLine P m \<noteq> None)"

lemma lookupLine_prefix:
  "lookupLine E m = Some l \<Longrightarrow> lookupLine (E @ F) m = Some l"
  by (induction E) auto

lemma checkFrom_citesDown:
  assumes "sorted_wrt (<) (map lineNumber (E @ P))"
      and "checkFrom_gen A E P"
    shows "\<forall>l \<in> set P. \<forall>m \<in> set (citedLines (justification l)).
             m < lineNumber l \<and> lookupLine (E @ P) m \<noteq> None"
  using assms
proof (induction P arbitrary: E)
  case (Cons l ls)
  have s: "sorted_wrt (<) (map lineNumber ((E @ [l]) @ ls))" using Cons.prems(1) by simp
  from Cons.prems(2) have lo: "lineOK_gen A E l" and rest: "checkFrom_gen A (E @ [l]) ls" by auto
  have "\<forall>m \<in> set (citedLines (justification l)). m < lineNumber l \<and> lookupLine (E @ l # ls) m \<noteq> None"
  proof
    fix m assume m: "m \<in> set (citedLines (justification l))"
    from lo m obtain l' where l': "lookupLine E m = Some l'"
      unfolding lineOK_gen_def Let_def by (auto simp: list_all_iff)
    then have "l' \<in> set E" "lineNumber l' = m" by (auto dest: lookupLine_Some)
    moreover from Cons.prems(1) have "\<forall>x \<in> set E. lineNumber x < lineNumber l"
      by (auto simp: sorted_wrt_append)
    ultimately have "m < lineNumber l" by auto
    moreover from l' have "lookupLine (E @ l # ls) m \<noteq> None"
      using lookupLine_prefix [where F = "l # ls"] by simp
    ultimately show "m < lineNumber l \<and> lookupLine (E @ l # ls) m \<noteq> None" ..
  qed
  moreover have "\<forall>l'' \<in> set ls. \<forall>m \<in> set (citedLines (justification l'')).
                    m < lineNumber l'' \<and> lookupLine (E @ l # ls) m \<noteq> None"
    using Cons.IH [OF s rest] by simp
  ultimately show ?case by simp
qed simp

lemma lemmonCorrect_citesDown: "lemmonCorrect P \<Longrightarrow> citesDown P"
  using checkFrom_citesDown [where E = "[]" and P = P and A = depSrc]
  by (simp add: lemmonCorrect_def citesDown_def)

lemma L1:
  assumes "citesDown P"
  shows "lookupLine P n \<noteq> None \<Longrightarrow> n < k \<Longrightarrow> unfoldD k P n \<noteq> None"
proof (induction k arbitrary: n)
  case (Suc k)
  then obtain l where l: "lookupLine P n = Some l" by auto
  then have "l \<in> set P" and "lineNumber l = n" by (auto dest: lookupLine_Some)
  with assms have cd: "\<And>m. m \<in> set (citedLines (justification l))
                            \<Longrightarrow> m < n \<and> lookupLine P m \<noteq> None"
    by (auto simp: citesDown_def)
  then have "\<forall>m \<in> set (citedLines (justification l)).
                unfoldD k P m \<noteq> None \<and> fmAt P m \<noteq> None"
    using Suc.IH Suc.prems(2) by (fastforce simp: fmAt_def)
  then show ?case
    using l by (cases "justification l") (auto split: option.splits)
qed simp

lemma sorted_wrt_less_distinct: "sorted_wrt (<) (xs :: nat list) \<Longrightarrow> distinct xs"
  by (induction xs) auto

text \<open>Proposition 18: the citation graph is a DAG, and every earlier line is
  available to be cited.  Acyclicity is @{thm [source] lemmonCorrect_citesDown};
  availability is the second conjunct of @{const citesDown}, which says that the
  notation contains no device by which a line could cease to be.\<close>

theorem proposition_18:
  assumes "lemmonCorrect P" and "l \<in> set P"
      and "m \<in> set (citedLines (justification l))"
  shows "m < lineNumber l" and "lookupLine P m \<noteq> None"
  using lemmonCorrect_citesDown [OF assms(1)] assms by (auto simp: citesDown_def)

theorem unfolding_terminates:
  assumes "lemmonCorrect P" and "P \<noteq> []"
  shows "\<exists>d. toDerivation P = Inr d"
proof -
  from assms(1) have "distinct (map lineNumber P)"
    by (simp add: lemmonCorrect_def sorted_wrt_less_distinct)
  moreover from assms(2) have "last P \<in> set P" by simp
  ultimately have lk: "lookupLine P (rootLine P) \<noteq> None"
    using assms(2) by (simp add: rootLine_def lookupLine_mem)
  have "unfoldD (Suc (rootLine P)) P (rootLine P) \<noteq> None"
    by (rule L1 [OF lemmonCorrect_citesDown [OF assms(1)] lk]) simp
  then show ?thesis using assms
    by (cases "unfoldD (Suc (rootLine P)) P (rootLine P)")
       (simp_all add: toDerivation_def del: unfoldD.simps)
qed

section \<open>The traversal\<close>

text \<open>``Traverse the derivation, emitting first the premises, at the outermost
  level and once each however often they are used, and thereafter, for each
  node, the subderivations its rule requires followed by the line applying it,
  opening a subproof at each discharge.''

  The traversal carries an environment binding each assumption label that is in
  scope to the Fitch line that carries it, together with its formula.  The
  labels are the line numbers of the source; the Fitch line numbers are fresh,
  because unfolding duplicates.\<close>

type_synonym env = "(nat \<times> nat \<times> fm) list"

definition envLine :: "env \<Rightarrow> nat \<Rightarrow> nat" where
  "envLine G a = (case find (\<lambda>e. fst e = a) G of Some e \<Rightarrow> fst (snd e) | None \<Rightarrow> 0)"

definition envFms :: "env \<Rightarrow> fm list" where
  "envFms G = map (snd \<circ> snd) G"

text \<open>``If a subproof's conclusion is a line from outside it --- as in deriving
  \<open>Q \<longrightarrow> P\<close> from the premise \<open>P\<close> --- then the subproof would contain nothing at
  all, and Fitch requires a reiteration step to bring the line in.''\<close>

definition endsAt :: "fitch_item list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "endsAt body asmLine c \<longleftrightarrow>
     (if body = [] then asmLine = c
      else (case last body of FLine n _ _ \<Rightarrow> n = c | FSub _ \<Rightarrow> False))"

definition closeSub :: "nat \<Rightarrow> fm \<Rightarrow> fitch_item list \<Rightarrow> nat \<Rightarrow> nat
                          \<Rightarrow> fitch_item list \<times> nat \<times> nat" where
  "closeSub asmLine psi body c nxt =
     (if endsAt body asmLine c then (body, c, nxt)
      else (body @ [FLine nxt psi (FReit c)], nxt, Suc nxt))"

lemma subLastLine_body:
  assumes "endsAt body a c"
  shows "subLastLine (Subproof a fa body) = c"
proof (cases "body = []")
  case True
  with assms show ?thesis by (simp add: subLastLine_def endsAt_def)
next
  case False
  with assms obtain f r where lb: "last body = FLine c f r"
    by (cases "last body") (auto simp: endsAt_def split: fitch_item.splits)
  from False have "last (flatSub (Subproof a fa body) []) = FL c f r [a]"
    by (simp add: last_concat_map lb)
  then show ?thesis by (simp add: subLastLine_def)
qed

text \<open>So a discharging rule may cite the subproof the traversal has just built
  by the pair of numbers it has just used.\<close>

lemma subLastLine_closeSub:
  "subLastLine (Subproof a fa (fst (closeSub a psi body c nxt)))
     = fst (snd (closeSub a psi body c nxt))"
proof (cases "endsAt body a c")
  case True
  then show ?thesis by (simp add: closeSub_def subLastLine_body)
next
  case False
  have "endsAt (body @ [FLine nxt psi (FReit c)]) a nxt" by (simp add: endsAt_def)
  with False show ?thesis by (simp add: closeSub_def subLastLine_body)
qed

subsection \<open>The renaming repair\<close>

text \<open>Section 5.4.  ``Wherever the construction is about to emit a universal
  introduction whose eigenvariable occurs in an assumption in scope, rename the
  subderivation feeding it to a name occurring nowhere in the proof --- nowhere,
  and not merely nowhere in the subderivation, for the reason given in
  Remark 25.''

  Names of increasing length are fresh for the whole derivation once @{term base}
  exceeds the length of every name occurring in it; the counter makes successive
  repairs use different names, which matters when one universal introduction
  stands directly above another.\<close>

definition freshIdx :: "nat \<Rightarrow> nat \<Rightarrow> nm" where
  "freshIdx base k = String.implode (replicate (base + k) CHR ''c'')"

lemma nlen_freshIdx [simp]: "nlen (freshIdx base k) = base + k"
  by (simp add: nlen_def freshIdx_def)

lemma freshIdx_fresh: "maxlen used < base + k \<Longrightarrow> freshIdx base k \<notin> set used"
  using maxlen_ge [of "freshIdx base k" used] by auto

lemma freshIdx_inject: "freshIdx base k = freshIdx base k' \<Longrightarrow> k = k'"
  by (metis nlen_freshIdx add_left_imp_eq)

text \<open>The eigenvariable of a universal introduction: a name the Lemmon side
  condition licenses.  By @{thm [source] instWitnesses_complete} the search is
  complete, so this is @{const genOK} made to say which name it found.\<close>

definition eigenOf :: "vr \<Rightarrow> fm \<Rightarrow> deriv \<Rightarrow> nm option" where
  "eigenOf x p d =
     (case filter (\<lambda>a. \<not> occurs a p \<and> arbitrary_in a (openFms d))
                  (instWitnesses x p (dForm d)) of
        [] \<Rightarrow> None | a # _ \<Rightarrow> Some a)"

lemma eigenOf_Some:
  assumes "eigenOf x p d = Some a"
  shows "inst x a p = dForm d \<and> \<not> occurs a p \<and> arbitrary_in a (openFms d)"
proof -
  let ?ws = "filter (\<lambda>a. \<not> occurs a p \<and> arbitrary_in a (openFms d))
                    (instWitnesses x p (dForm d))"
  from assms obtain as where "?ws = a # as"
    by (auto simp: eigenOf_def split: list.splits)
  then have "a \<in> set ?ws" by simp
  then show ?thesis by (auto dest: instWitnesses_sound)
qed

lemma eigenOf_None_iff:
  "eigenOf x p d = None
     \<longleftrightarrow> \<not> (\<exists>a \<in> set (instWitnesses x p (dForm d)).
                \<not> occurs a p \<and> arbitrary_in a (openFms d))"
proof -
  have "eigenOf x p d = None
          \<longleftrightarrow> filter (\<lambda>a. \<not> occurs a p \<and> arbitrary_in a (openFms d))
                       (instWitnesses x p (dForm d)) = []"
    by (simp add: eigenOf_def split: list.splits)
  also have "\<dots> \<longleftrightarrow> \<not> (\<exists>a \<in> set (instWitnesses x p (dForm d)).
                            \<not> occurs a p \<and> arbitrary_in a (openFms d))"
    by (simp add: filter_empty_conv)
  finally show ?thesis .
qed

text \<open>@{const eigenOf} is @{const genOK} made to say which name it found: the
  search over @{const instWitnesses} is complete by @{thm [source]
  instWitnesses_complete}.\<close>

lemma genOK_eigenOf:
  assumes "x \<in> set (fvs p)"
  shows "genOK x p (dForm d) (openFms d) \<longleftrightarrow> eigenOf x p d \<noteq> None"
  using assms by (simp add: genOK_def eigenOf_None_iff)

text \<open>The witness of an existential elimination.  The paper's Section 6.2 says
  that universal introduction alone imposes a condition on the assumptions; on
  the rule set of \<open>LF_Lemmon.thy\<close> existential elimination
  does so too, and the same repair is required at it.  See the discussion at the
  end of this theory.\<close>

definition witnessOf :: "fm \<Rightarrow> fm \<Rightarrow> fm \<Rightarrow> fm list \<Rightarrow> nm option" where
  "witnessOf ex f psi As =
     (case ex of
        Exi x p \<Rightarrow>
          (case filter (\<lambda>b. \<not> occurs b p \<and> \<not> occurs b psi \<and> arbitrary_in b As)
                       (instWitnesses x p f) of
             [] \<Rightarrow> None | b # _ \<Rightarrow> Some b)
      | _ \<Rightarrow> None)"

text \<open>A repair is called for exactly when the name the Lemmon side condition
  licensed occurs in an assumption that Fitch has in scope but the line does not
  depend on.\<close>

definition uniRepair :: "env \<Rightarrow> fm \<Rightarrow> deriv \<Rightarrow> nm option" where
  "uniRepair G phi d =
     (case phi of
        Uni x p \<Rightarrow>
          (case eigenOf x p d of
             None \<Rightarrow> None
           | Some a \<Rightarrow> if arbitrary_in a (envFms G) then None else Some a)
      | _ \<Rightarrow> None)"

definition uniD :: "nat \<Rightarrow> nat \<Rightarrow> env \<Rightarrow> fm \<Rightarrow> deriv \<Rightarrow> deriv" where
  "uniD base cnt G phi d =
     (case uniRepair G phi d of None \<Rightarrow> d | Some a \<Rightarrow> rnD a (freshIdx base cnt) d)"

definition uniCnt :: "nat \<Rightarrow> env \<Rightarrow> fm \<Rightarrow> deriv \<Rightarrow> nat" where
  "uniCnt cnt G phi d = (case uniRepair G phi d of None \<Rightarrow> cnt | Some a \<Rightarrow> Suc cnt)"

definition exRepair :: "env \<Rightarrow> fm \<Rightarrow> fm \<Rightarrow> fm \<Rightarrow> nat \<Rightarrow> deriv \<Rightarrow> deriv \<Rightarrow> nm option" where
  "exRepair G ex f psi a d0 d1 =
     (case witnessOf ex f psi (openFms d0 @ map snd (drop_label a (openAsms d1))) of
        None \<Rightarrow> None
      | Some b \<Rightarrow> if arbitrary_in b (envFms G) then None else Some b)"

definition exD :: "nat \<Rightarrow> nat \<Rightarrow> env \<Rightarrow> fm \<Rightarrow> fm \<Rightarrow> fm \<Rightarrow> nat \<Rightarrow> deriv \<Rightarrow> deriv \<Rightarrow> deriv" where
  "exD base cnt G ex f psi a d0 d1 =
     (case exRepair G ex f psi a d0 d1 of
        None \<Rightarrow> d1 | Some b \<Rightarrow> rnD b (freshIdx base cnt) d1)"

definition exF :: "nat \<Rightarrow> nat \<Rightarrow> env \<Rightarrow> fm \<Rightarrow> fm \<Rightarrow> fm \<Rightarrow> nat \<Rightarrow> deriv \<Rightarrow> deriv \<Rightarrow> fm" where
  "exF base cnt G ex f psi a d0 d1 =
     (case exRepair G ex f psi a d0 d1 of
        None \<Rightarrow> f | Some b \<Rightarrow> rn b (freshIdx base cnt) f)"

definition exCnt :: "nat \<Rightarrow> env \<Rightarrow> fm \<Rightarrow> fm \<Rightarrow> fm \<Rightarrow> nat \<Rightarrow> deriv \<Rightarrow> deriv \<Rightarrow> nat" where
  "exCnt cnt G ex f psi a d0 d1 =
     (case exRepair G ex f psi a d0 d1 of None \<Rightarrow> cnt | Some b \<Rightarrow> Suc cnt)"

text \<open>Renaming does not change the shape of a derivation, which is what the
  traversal recurses on.\<close>

lemma size_rnD [termination_simp]: "size (rnD a b d) = size d"
  by (induction a b d rule: rnD.induct) auto

lemma size_uniD [termination_simp]: "size (uniD base cnt G phi d) = size d"
  by (simp add: uniD_def size_rnD split: option.splits)

lemma size_exD [termination_simp]: "size (exD base cnt G ex f psi a d0 d1) = size d1"
  by (simp add: exD_def size_rnD split: option.splits)

subsection \<open>Emitting the lines\<close>

text \<open>@{term "emit base G nx cnt d"} returns the items @{term d} contributes at
  the level it sits at, the number of the line carrying its conclusion, the next
  free line number, and the next free repair index.\<close>

fun emit :: "nat \<Rightarrow> env \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> deriv
               \<Rightarrow> fitch_item list \<times> nat \<times> nat \<times> nat" where
  "emit base G nx cnt (Deriv phi (DAssume a)) = ([], envLine G a, nx, cnt)"
| "emit base G nx cnt (Deriv phi (DPremise a)) = ([], envLine G a, nx, cnt)"
| "emit base G nx cnt (Deriv phi (DMP d1 d2)) =
     (let (i1, c1, nx1, cnt1) = emit base G nx cnt d1;
          (i2, c2, nx2, cnt2) = emit base G nx1 cnt1 d2
      in (i1 @ i2 @ [FLine nx2 phi (FMP c1 c2)], nx2, Suc nx2, cnt2))"
| "emit base G nx cnt (Deriv phi (DCP a fa d1)) =
     (let (b1, cc1, nx1, cnt1) = emit base ((a, nx, fa) # G) (Suc nx) cnt d1;
          (b1', l1, nx2) = closeSub nx (dForm d1) b1 cc1 nx1
      in ([FSub (Subproof nx fa b1'), FLine nx2 phi (FCP (nx, l1))],
          nx2, Suc nx2, cnt1))"
| "emit base G nx cnt (Deriv phi (DRAA a fa d1)) =
     (let (b1, cc1, nx1, cnt1) = emit base ((a, nx, fa) # G) (Suc nx) cnt d1;
          (b1', l1, nx2) = closeSub nx (dForm d1) b1 cc1 nx1
      in ([FSub (Subproof nx fa b1'), FLine nx2 phi (FRAA (nx, l1))],
          nx2, Suc nx2, cnt1))"
| "emit base G nx cnt (Deriv phi (DDN d1)) =
     (let (i1, c1, nx1, cnt1) = emit base G nx cnt d1
      in (i1 @ [FLine nx1 phi (FDN c1)], nx1, Suc nx1, cnt1))"
| "emit base G nx cnt (Deriv phi (DBotI d1 d2)) =
     (let (i1, c1, nx1, cnt1) = emit base G nx cnt d1;
          (i2, c2, nx2, cnt2) = emit base G nx1 cnt1 d2
      in (i1 @ i2 @ [FLine nx2 phi (FBotI c1 c2)], nx2, Suc nx2, cnt2))"
| "emit base G nx cnt (Deriv phi (DAndIntro d1 d2)) =
     (let (i1, c1, nx1, cnt1) = emit base G nx cnt d1;
          (i2, c2, nx2, cnt2) = emit base G nx1 cnt1 d2
      in (i1 @ i2 @ [FLine nx2 phi (FAndIntro c1 c2)], nx2, Suc nx2, cnt2))"
| "emit base G nx cnt (Deriv phi (DAndElimL d1)) =
     (let (i1, c1, nx1, cnt1) = emit base G nx cnt d1
      in (i1 @ [FLine nx1 phi (FAndElimL c1)], nx1, Suc nx1, cnt1))"
| "emit base G nx cnt (Deriv phi (DAndElimR d1)) =
     (let (i1, c1, nx1, cnt1) = emit base G nx cnt d1
      in (i1 @ [FLine nx1 phi (FAndElimR c1)], nx1, Suc nx1, cnt1))"
| "emit base G nx cnt (Deriv phi (DOrIntroL d1)) =
     (let (i1, c1, nx1, cnt1) = emit base G nx cnt d1
      in (i1 @ [FLine nx1 phi (FOrIntroL c1)], nx1, Suc nx1, cnt1))"
| "emit base G nx cnt (Deriv phi (DOrIntroR d1)) =
     (let (i1, c1, nx1, cnt1) = emit base G nx cnt d1
      in (i1 @ [FLine nx1 phi (FOrIntroR c1)], nx1, Suc nx1, cnt1))"
| "emit base G nx cnt (Deriv phi (DOrElim d0 a1 f1 d1 a2 f2 d2)) =
     (let (i0, c0, nx0, cnt0) = emit base G nx cnt d0;
          (b1, cc1, nx1, cnt1) = emit base ((a1, nx0, f1) # G) (Suc nx0) cnt0 d1;
          (b1', l1, nx1') = closeSub nx0 (dForm d1) b1 cc1 nx1;
          (b2, cc2, nx2, cnt2) = emit base ((a2, nx1', f2) # G) (Suc nx1') cnt1 d2;
          (b2', l2, nx2') = closeSub nx1' (dForm d2) b2 cc2 nx2
      in (i0 @ [FSub (Subproof nx0 f1 b1'), FSub (Subproof nx1' f2 b2'),
                FLine nx2' phi (FOrElim c0 (nx0, l1) (nx1', l2))],
          nx2', Suc nx2', cnt2))"
| "emit base G nx cnt (Deriv phi (DIffIntro d1 d2)) =
     (let (i1, c1, nx1, cnt1) = emit base G nx cnt d1;
          (i2, c2, nx2, cnt2) = emit base G nx1 cnt1 d2
      in (i1 @ i2 @ [FLine nx2 phi (FIffIntro c1 c2)], nx2, Suc nx2, cnt2))"
| "emit base G nx cnt (Deriv phi (DIffElimL d1)) =
     (let (i1, c1, nx1, cnt1) = emit base G nx cnt d1
      in (i1 @ [FLine nx1 phi (FIffElimL c1)], nx1, Suc nx1, cnt1))"
| "emit base G nx cnt (Deriv phi (DIffElimR d1)) =
     (let (i1, c1, nx1, cnt1) = emit base G nx cnt d1
      in (i1 @ [FLine nx1 phi (FIffElimR c1)], nx1, Suc nx1, cnt1))"
| "emit base G nx cnt (Deriv phi (DForallElim d1)) =
     (let (i1, c1, nx1, cnt1) = emit base G nx cnt d1
      in (i1 @ [FLine nx1 phi (FForallElim c1)], nx1, Suc nx1, cnt1))"
| "emit base G nx cnt (Deriv phi (DForallIntro d1)) =
     (let (i1, c1, nx1, cnt1) =
            emit base G nx (uniCnt cnt G phi d1) (uniD base cnt G phi d1)
      in (i1 @ [FLine nx1 phi (FForallIntro c1)], nx1, Suc nx1, cnt1))"
| "emit base G nx cnt (Deriv phi (DExistsIntro d1)) =
     (let (i1, c1, nx1, cnt1) = emit base G nx cnt d1
      in (i1 @ [FLine nx1 phi (FExistsIntro c1)], nx1, Suc nx1, cnt1))"
| "emit base G nx cnt (Deriv phi (DExistsElim d0 a f d1)) =
     (let (i0, c0, nx0, cnt0) = emit base G nx cnt d0;
          f' = exF base cnt0 G (dForm d0) f phi a d0 d1;
          (b1, cc1, nx1, cnt1) =
            emit base ((a, nx0, f') # G) (Suc nx0) (exCnt cnt0 G (dForm d0) f phi a d0 d1)
                 (exD base cnt0 G (dForm d0) f phi a d0 d1);
          (b1', l1, nx2) = closeSub nx0 phi b1 cc1 nx1
      in (i0 @ [FSub (Subproof nx0 f' b1'), FLine nx2 phi (FExistsElim c0 (nx0, l1))],
          nx2, Suc nx2, cnt1))"
| "emit base G nx cnt (Deriv phi DEqIntro) =
     ([FLine nx phi FEqIntro], nx, Suc nx, cnt)"
| "emit base G nx cnt (Deriv phi (DEqElim d1 d2)) =
     (let (i1, c1, nx1, cnt1) = emit base G nx cnt d1;
          (i2, c2, nx2, cnt2) = emit base G nx1 cnt1 d2
      in (i1 @ i2 @ [FLine nx2 phi (FEqElim c1 c2)], nx2, Suc nx2, cnt2))"
| "emit base G nx cnt (Deriv phi (DReit d1)) =
     (let (i1, c1, nx1, cnt1) = emit base G nx cnt d1
      in (i1 @ [FLine nx1 phi (FReit c1)], nx1, Suc nx1, cnt1))"

subsection \<open>Premises first, at the outermost level\<close>

text \<open>Lemma (L3) of Section 6.1 is the one the paper reports the implementation
  as having failed first: ``it emitted premises wherever the source had written
  them, which put some inside subproofs''.  Here the premises are read off the
  root's open assumptions --- exactly the leaves no ancestor discharges --- and
  emitted once each before anything else, in the order of the source's line
  numbers.\<close>

definition premEnv :: "deriv \<Rightarrow> env" where
  "premEnv d =
     map (\<lambda>ke. (fst (snd ke), Suc (fst ke), snd (snd ke)))
         (List.enumerate 0 (sort_key fst (remdups (openAsms d))))"

definition premLines :: "env \<Rightarrow> fitch_proof" where
  "premLines G = map (\<lambda>e. FLine (fst (snd e)) (snd (snd e)) FPremise) G"

definition derivationToFitch :: "deriv \<Rightarrow> fitch_proof" where
  "derivationToFitch d =
     (let G = premEnv d;
          base = Suc (maxlen (namesD d));
          (items, c, nx, cnt) = emit base G (Suc (length G)) 0 d
      in premLines G @ items)"

section \<open>The translation\<close>

text \<open>``Translation is then two functions and a choice between them.  The
  positional translation is attempted first, because it preserves numbering and
  structure; unfolding is the fallback, and the result records which was
  used.''\<close>

datatype route = Direct | ViaTree

definition viaTree :: "lemmon_proof \<Rightarrow> translation_error + (route \<times> fitch_proof)" where
  "viaTree P =
     (case toDerivation P of
        Inl e \<Rightarrow> Inl e
      | Inr d \<Rightarrow> Inr (ViaTree, derivationToFitch d))"

definition lemmonToFitch :: "lemmon_proof \<Rightarrow> translation_error + (route \<times> fitch_proof)" where
  "lemmonToFitch P =
     (case lemmonToFitchDirect P of
        Inr F \<Rightarrow> Inr (Direct, F)
      | Inl _ \<Rightarrow> viaTree P)"

text \<open>@{const lemmonToFitchDirect} returns an image whenever the three
  obstructions of Section 4 are absent.  Their absence does not make the image
  correct: the Lemmon proof of Theorem 22 has none of them, and its positional
  image is the incorrect Fitch proof the paper displays beneath it.  So the
  function above, which is the paper's, returns an incorrect proof by the
  @{const Direct} route on exactly the example that Section 5.4 is about.  The
  variant below asks the checker before taking the shortcut.\<close>

definition lemmonToFitchChecked ::
    "lemmon_proof \<Rightarrow> translation_error + (route \<times> fitch_proof)" where
  "lemmonToFitchChecked P =
     (case lemmonToFitchDirect P of
        Inr F \<Rightarrow> if fitchCorrect F then Inr (Direct, F) else viaTree P
      | Inl _ \<Rightarrow> viaTree P)"

text \<open>A positional image preserves the sequence of lines, so it has the
  conclusion of the source.\<close>

lemma lemmonToFitchDirect_conclusion:
  assumes "lemmonToFitchDirect P = Inr F" and "P \<noteq> []"
  shows "fitchConclusion F = conclusion P"
proof -
  from lemmonToFitchDirect_positional [OF assms(1)]
  have m: "map (\<lambda>fl. (flNum fl, flFm fl)) (flatten F)
             = map (\<lambda>l. (lineNumber l, formula l)) P" .
  with assms(2) have ne: "flatten F \<noteq> []" by auto
  from m have "last (map (\<lambda>fl. (flNum fl, flFm fl)) (flatten F))
                 = last (map (\<lambda>l. (lineNumber l, formula l)) P)" by simp
  with ne assms(2) have "flFm (last (flatten F)) = formula (last P)"
    by (simp add: last_map)
  with ne assms(2) show ?thesis by (simp add: fitchConclusion_def conclusion_def)
qed

end
