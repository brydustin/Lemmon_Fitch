(*  Title:      LF_Delta.thy

    Section 3 of the paper: from Fitch to Lemmon.  Definition 3 (\<delta>),
    Proposition 5 (the dependency set is contained in the scope),
    Theorem 4 (\<delta> is total and transfers correctness), and
    Proposition 7 (the dependency column is recoverable).
*)

theory LF_Delta
  imports LF_Fitch
begin

section \<open>The translation \<open>\<delta>\<close>\<close>

subsection \<open>Definition 3\<close>

text \<open>Flatten the Fitch proof into a sequence of lines in order and assign to
  each the set given by @{text depsOf}: the whole of \<open>\<delta>\<close>'s arithmetic.  Note
  that the source's own annotation is not consulted --- there is none to
  consult --- which is what Proposition 7 turns on.\<close>

fun deltaAux :: "lemmon_proof \<Rightarrow> fline list \<Rightarrow> lemmon_proof" where
  "deltaAux acc [] = acc"
| "deltaAux acc (fl # fls) =
     deltaAux (acc @ [ProofLine (flNum fl) (flFm fl) (toLemmonRule (flRule fl))
                        (depsOf (depsAt acc) (toLemmonRule (flRule fl)) (flNum fl))]) fls"

definition \<delta> :: "fitch_proof \<Rightarrow> lemmon_proof" where
  "\<delta> F = deltaAux [] (flatten F)"

definition fitchToLemmon :: "fitch_proof \<Rightarrow> lemmon_proof" where
  "fitchToLemmon F = \<delta> F"

lemma fitchToLemmon_eq [simp]: "fitchToLemmon F = \<delta> F"
  by (simp add: fitchToLemmon_def)

text \<open>Fitch checks its rules against the assumptions in scope, Lemmon against
  the assumptions the line rests on.  Otherwise the two checks are the same
  check: this is @{text scopeSrc} against @{text depSrc}.\<close>

definition scopeSrc :: "fitch_proof \<Rightarrow> asm_src" where
  "scopeSrc F E n G = depFms E (scopeOf F n)"

definition fitchCorrect :: "fitch_proof \<Rightarrow> bool" where
  "fitchCorrect F \<longleftrightarrow> fitchWF F \<and> checkFrom_gen (scopeSrc F) [] (\<delta> F)"

abbreviation isCorrectFitchProof :: "fitch_proof \<Rightarrow> bool" where
  "isCorrectFitchProof F \<equiv> fitchCorrect F"

section \<open>The two turnstiles\<close>

text \<open>The paper writes a single \<open>\<turnstile>\<close> for both systems, which it may, having
  settled Theorem 4.  Here they are two, because which of them a proof
  establishes is exactly what is at issue.

  A sequent is what a turnstile builds, and \<open>holds\<close> says whether the
  system in question proves it.  Making the turnstiles constructors rather than
  predicates has a point: \<open>\<Gamma> \<turnstile>\<^sub>L \<psi>\<close> is then a term in its own right, so further
  notation can be applied to it --- which is what \<open>\<tturnstile>\<close> in \<open>LF_Derivation\<close> does,
  writing \<open>d \<tturnstile> \<Gamma> \<turnstile>\<^sub>L \<psi>\<close> for ``@{term d} is a derivation of \<open>\<Gamma> \<turnstile>\<^sub>L \<psi>\<close>''.  The
  coercion lets a sequent stand wherever a proposition is expected, so
  \<open>\<Gamma> \<turnstile>\<^sub>L \<psi>\<close> may still simply be asserted.

  The two sides differ only in where the assumptions on the left are read off ---
  a dependency set there, the premise lines here --- and in which check the proof
  has to pass.  Conjecture 26 is the statement that \<open>\<turnstile>\<^sub>L\<close> is contained in
  \<open>\<turnstile>\<^sub>F\<close>.\<close>

text \<open>Each turnstile is declared exactly once, here, as an ordinary infix
  predicate at priority 50.  \<open>\<tturnstile>\<close> in \<open>LF_Derivation\<close> then binds looser and takes
  a \<open>\<turnstile>\<^sub>L\<close> statement as its right-hand argument, so \<open>d \<tturnstile> \<Gamma> \<turnstile>\<^sub>L \<psi>\<close> is \<open>\<tturnstile>\<close>
  applied to \<open>\<Gamma> \<turnstile>\<^sub>L \<psi>\<close> --- and \<open>\<Gamma> \<turnstile>\<^sub>L \<psi>\<close> on its own is a proposition, needing
  no wrapper and no coercion.\<close>

definition Lprov :: "fm list \<Rightarrow> fm \<Rightarrow> bool"  (infix \<open>\<turnstile>\<^sub>L\<close> 50) where
  "\<Gamma> \<turnstile>\<^sub>L \<psi> \<longleftrightarrow>
     (\<exists>P. lemmonCorrect P \<and> P \<noteq> [] \<and>
          set (openPremises P) = set \<Gamma> \<and> conclusion P = Some \<psi>)"

definition Fprov :: "fm list \<Rightarrow> fm \<Rightarrow> bool"  (infix \<open>\<turnstile>\<^sub>F\<close> 50) where
  "\<Gamma> \<turnstile>\<^sub>F \<psi> \<longleftrightarrow>
     (\<exists>F. fitchCorrect F \<and>
          set (fitchPremises F) = set \<Gamma> \<and> fitchConclusion F = Some \<psi>)"

text \<open>Guards.  Each holds by @{method rule} @{thm refl} and so fails to parse if
  the notation is ever ambiguous or shadowed.  The bare forms are the point: no
  enclosing parentheses.  Note \<open>\<longleftrightarrow>\<close> rather than \<open>=\<close>: both turnstiles sit at
  priority 50, as \<open>=\<close> does, so \<open>\<Gamma> \<turnstile>\<^sub>L \<psi> = X\<close> would not parse without brackets,
  whereas \<open>\<longleftrightarrow>\<close> at 25 takes them bare.  Assert a turnstile on its own --- in
  \<open>assumes\<close>, \<open>shows\<close>, or before \<open>\<Longrightarrow>\<close> --- and no brackets are needed at all.\<close>

lemma turnstile_L: "\<Gamma> \<turnstile>\<^sub>L \<psi> \<longleftrightarrow> Lprov \<Gamma> \<psi>" by (rule refl)
lemma turnstile_F: "\<Gamma> \<turnstile>\<^sub>F \<psi> \<longleftrightarrow> Fprov \<Gamma> \<psi>" by (rule refl)

lemma LseqI:
  assumes "lemmonCorrect P" and "P \<noteq> []"
      and "set (openPremises P) = set \<Gamma>" and "conclusion P = Some \<psi>"
    shows "\<Gamma> \<turnstile>\<^sub>L \<psi>"
  using assms unfolding Lprov_def by blast

lemma LseqE:
  assumes "\<Gamma> \<turnstile>\<^sub>L \<psi>"
  obtains P where "lemmonCorrect P" and "P \<noteq> []"
    and "set (openPremises P) = set \<Gamma>" and "conclusion P = Some \<psi>"
  using assms unfolding Lprov_def by blast

lemma FseqI:
  assumes "fitchCorrect F" and "set (fitchPremises F) = set \<Gamma>"
      and "fitchConclusion F = Some \<psi>"
    shows "\<Gamma> \<turnstile>\<^sub>F \<psi>"
  using assms unfolding Fprov_def by blast

lemma FseqE:
  assumes "\<Gamma> \<turnstile>\<^sub>F \<psi>"
  obtains F where "fitchCorrect F" and "set (fitchPremises F) = set \<Gamma>"
    and "fitchConclusion F = Some \<psi>"
  using assms unfolding Fprov_def by blast


subsection \<open>Elementary facts about lookup and the fold\<close>

lemma lookupLine_Some: "lookupLine E m = Some l \<Longrightarrow> lineNumber l = m \<and> l \<in> set E"
  by (induction E, auto split: if_splits)

lemma lookupLine_mem:
  "distinct (map lineNumber E) \<Longrightarrow> l \<in> set E \<Longrightarrow> lookupLine E (lineNumber l) = Some l"
  by (induction E, auto)

lemma findFL_Some: "findFL xs m = Some fl \<Longrightarrow> flNum fl = m \<and> fl \<in> set xs"
  by (induction xs, auto split: if_splits)

lemma findFL_mem:
  "distinct (map flNum xs) \<Longrightarrow> fl \<in> set xs \<Longrightarrow> findFL xs (flNum fl) = Some fl"
  by (induction xs, auto)

lemma deltaAux_nums: "map lineNumber (deltaAux acc fls) = map lineNumber acc @ map flNum fls"
  by (induction fls arbitrary: acc, auto)

lemma deltaAux_fms: "map formula (deltaAux acc fls) = map formula acc @ map flFm fls"
  by (induction fls arbitrary: acc, auto) 

lemma deltaAux_append: "deltaAux acc (xs @ ys) = deltaAux (deltaAux acc xs) ys"
  by (induction xs arbitrary: acc, auto)

lemma delta_nums: "map lineNumber (\<delta> F) = map flNum (flatten F)"
  by (simp add: \<delta>_def deltaAux_nums)

lemma delta_fms: "map formula (\<delta> F) = map flFm (flatten F)"
  by (simp add: \<delta>_def deltaAux_fms)

subsection \<open>Structural facts about flattening\<close>

lemma concat_map_nonempty:
  "xs \<noteq> [] \<Longrightarrow> \<forall>x \<in> set xs. g x \<noteq> [] \<Longrightarrow> concat (map g xs) \<noteq> []"
  by (cases xs, auto) 

lemma last_concat_map:
  "xs \<noteq> [] \<Longrightarrow> \<forall>x \<in> set xs. g x \<noteq> [] \<Longrightarrow> last (concat (map g xs)) = last (g (last xs))"
proof (induction xs)
  case (Cons x xs)
  show ?case
  proof (cases "xs = []")
    case True then show ?thesis by simp
  next
    case False
    with Cons.prems have "concat (map g xs) \<noteq> []" by (simp add: concat_map_nonempty)
    with False Cons show ?thesis by simp
  qed
qed simp

text \<open>Where a subproof's last line sits, and what its number is.  The number does
  not depend on the path, which is why @{text subLastLine} may compute it at the
  empty path.\<close>

lemma subLastLine_last:
  assumes "lastIsLineSub (Subproof a fa body)"
  shows "\<exists>f r. last (flatSub (Subproof a fa body) path)
                 = FL (subLastLine (Subproof a fa body)) f r (path @ [a])"
proof (cases "body = []")
  case True
  then show ?thesis by (simp add: subLastLine_def)
next
  case False
  with assms obtain c f r where lb: "last body = FLine c f r"
    by (cases "last body") (auto split: fitch_item.splits)
  have A: "last (flatSub (Subproof a fa body) q) = FL c f r (q @ [a])" for q :: "nat list"
    using False by (simp add: last_concat_map lb)
  from A [of "[]"] have "subLastLine (Subproof a fa body) = c" by (simp add: subLastLine_def)
  with A [of path] show ?thesis by simp
qed

text \<open>An assumption line lies inside its own subproof.\<close>

lemma flat_assume_scope:
  "FL n f FAssume sc \<in> set (flatItem it path) \<Longrightarrow> noAssumeLinesItem it \<Longrightarrow> n \<in> set sc"
  "FL n f FAssume sc \<in> set (flatSub s path) \<Longrightarrow> noAssumeLinesSub s \<Longrightarrow> n \<in> set sc"
proof (induction it and s arbitrary: path and path)
  case (Subproof a fa body)
  then show ?case by (auto simp: list_all_iff)
qed auto

text \<open>A subproof reference names an assumption line and a last line, both
  belonging to the subproof, whose path extends the citing level's by the
  assumption.\<close>

lemma subref_lines:
  "((a, c), P) \<in> set (subrefsItem it path) \<Longrightarrow> lastIsLineItem it \<Longrightarrow>
     (\<exists>f. FL a f FAssume (P @ [a]) \<in> set (flatItem it path)) \<and>
     (\<exists>f r. FL c f r (P @ [a]) \<in> set (flatItem it path))"
  "((a, c), P) \<in> set (subrefsSub s path) \<Longrightarrow> lastIsLineSub s \<Longrightarrow>
     (\<exists>f. FL a f FAssume (P @ [a]) \<in> set (flatSub s path)) \<and>
     (\<exists>f r. FL c f r (P @ [a]) \<in> set (flatSub s path))"
proof (induction it and s arbitrary: path and path)
  case (Subproof a' fa body)
  from Subproof.prems(2) have lil: "lastIsLineSub (Subproof a' fa body)" by simp
  show ?case
  proof (cases "((a, c), P) = ((a', subLastLine (Subproof a' fa body)), path)")
    case True
    then have ax: "a = a'" and Px: "P = path"
          and cx: "c = subLastLine (Subproof a' fa body)" by auto
    obtain f r where L: "last (flatSub (Subproof a' fa body) path)
                           = FL (subLastLine (Subproof a' fa body)) f r (path @ [a'])"
      using subLastLine_last [OF lil, of path] by blast
    have "FL c f r (P @ [a]) \<in> set (flatSub (Subproof a' fa body) path)"
      using L ax Px cx by (metis flatSub_nonempty last_in_set)
    moreover have "FL a fa FAssume (P @ [a]) \<in> set (flatSub (Subproof a' fa body) path)"
      using ax Px by simp
    ultimately show ?thesis by blast
  next
    case False
    with Subproof.prems(1) obtain it'
      where it': "it' \<in> set body" "((a, c), P) \<in> set (subrefsItem it' (path @ [a']))"
      by auto
    from lil it'(1) have "lastIsLineItem it'" by (auto simp: list_all_iff)
    from Subproof.IH [OF it'(1) it'(2) this] it'(1) show ?thesis by auto
  qed
qed auto

lemma subrefs_lines:
  assumes "fitchWF F" and "((a, c), P) \<in> set (subrefs F)"
  shows "(\<exists>f. FL a f FAssume (P @ [a]) \<in> set (flatten F)) \<and>
         (\<exists>f r. FL c f r (P @ [a]) \<in> set (flatten F))"
proof -
  from assms(2) obtain it where "it \<in> set F" "((a, c), P) \<in> set (subrefsItem it [])"
    by (auto simp: subrefs_def)
  moreover with assms(1) have "lastIsLineItem it" by (auto simp: fitchWF_def list_all_iff)
  ultimately show ?thesis using subref_lines(1) by (fastforce simp: flatten_def)
qed

subsection \<open>Proposition 5\<close>

lemma fitchWF_distinct: "fitchWF F \<Longrightarrow> distinct (map flNum (flatten F))"
  by (auto simp: fitchWF_def dest: strict_sorted_iff [THEN iffD1])

lemma scopePath_eq:
  assumes "fitchWF F" and "fl \<in> set (flatten F)"
  shows "scopePath F (flNum fl) = flScope fl"
  using assms findFL_mem [OF fitchWF_distinct [OF assms(1)] assms(2)]
  by (simp add: scopePath_def)

lemma scopeOf_mono:
  assumes "fitchWF F" "fl \<in> set (flatten F)" "fl' \<in> set (flatten F)"
      and "is_prefix (flScope fl') (flScope fl)"
  shows "scopeOf F (flNum fl') \<subseteq> scopeOf F (flNum fl)"
  using assms scopePath_eq [OF assms(1) assms(2)] scopePath_eq [OF assms(1) assms(3)]
  by (auto simp: scopeOf_def dest: is_prefix_set [THEN subsetD])

lemma premise_in_scope:
  assumes "fl \<in> set (flatten F)" "flRule fl = FPremise"
  shows "flNum fl \<in> scopeOf F (flNum fl)"
  using assms by (force simp: scopeOf_def premiseLines_def)

lemma assume_in_scope:
  assumes "fitchWF F" "fl \<in> set (flatten F)" "flRule fl = FAssume"
  shows "flNum fl \<in> scopeOf F (flNum fl)"
proof -
  from assms obtain it where it: "it \<in> set F" "fl \<in> set (flatItem it [])"
    by (auto simp: flatten_def)
  with assms(1) have "noAssumeLinesItem it" by (auto simp: fitchWF_def list_all_iff)
  with it assms(3) have "flNum fl \<in> set (flScope fl)"
    using flat_assume_scope(1) [of "flNum fl" "flFm fl" "flScope fl" it "[]"] by (cases fl) auto
  with assms(1) assms(2) show ?thesis by (simp add: scopeOf_def scopePath_eq)
qed

text \<open>The generic step: a rule's dependency set stays inside a set that contains
  the assumption line itself, the dependency sets of the lines it cites, and the
  dependency sets of the last lines of the subproofs it cites bar their
  assumptions.\<close>

lemma depsOf_subset:
  assumes "\<And>m. m \<in> set (fCitedLines r) \<Longrightarrow> look m \<subseteq> S"
      and "\<And>a c. (a, c) \<in> set (fCitedSubs r) \<Longrightarrow> look c \<subseteq> insert a S"
      and "r = FPremise \<or> r = FAssume \<Longrightarrow> n \<in> S"
  shows "depsOf look (toLemmonRule r) n \<subseteq> S"
  using assms by (cases r rule: toLemmonRule.cases) (auto simp: depsOf_def)

lemma depsAt_scope:
  assumes "\<forall>l \<in> set acc. references l \<subseteq> scopeOf F (lineNumber l)"
  shows "depsAt acc m \<subseteq> scopeOf F m"
  using assms by (auto simp: depsAt_def dest: lookupLine_Some split: option.splits)

lemma depsOf_scopeOf:
  assumes wf: "fitchWF F"
      and fl: "fl \<in> set (flatten F)"
      and inv: "\<forall>l \<in> set acc. references l \<subseteq> scopeOf F (lineNumber l)"
  shows "depsOf (depsAt acc) (toLemmonRule (flRule fl)) (flNum fl) \<subseteq> scopeOf F (flNum fl)"
proof (rule depsOf_subset)
  fix m assume m: "m \<in> set (fCitedLines (flRule fl))"
  from wf fl have "citationOK F fl" by (auto simp: fitchWF_def list_all_iff)
  with m obtain fl' where fl': "findFL (flatten F) m = Some fl'"
                                "is_prefix (flScope fl') (flScope fl)"
    by (auto simp: citationOK_def list_all_iff split: option.splits)
  then have "fl' \<in> set (flatten F)" "flNum fl' = m" by (auto dest: findFL_Some)
  with fl' wf fl have "scopeOf F m \<subseteq> scopeOf F (flNum fl)" using scopeOf_mono by blast
  with depsAt_scope [OF inv, of m] show "depsAt acc m \<subseteq> scopeOf F (flNum fl)" by blast
next
  fix a c assume ac: "(a, c) \<in> set (fCitedSubs (flRule fl))"
  from wf fl have "citationOK F fl" by (auto simp: fitchWF_def list_all_iff)
  with ac have "((a, c), flScope fl) \<in> set (subrefs F)"
    by (auto simp: citationOK_def list_all_iff)
  with wf obtain f r where c: "FL c f r (flScope fl @ [a]) \<in> set (flatten F)"
    using subrefs_lines by blast
  then have "scopePath F c = flScope fl @ [a]"
    using wf scopePath_eq [OF wf c] by simp
  then have "scopeOf F c \<subseteq> insert a (scopeOf F (flNum fl))"
    using wf fl by (auto simp: scopeOf_def scopePath_eq)
  with depsAt_scope [OF inv, of c] show "depsAt acc c \<subseteq> insert a (scopeOf F (flNum fl))"
    by blast
next
  assume "flRule fl = FPremise \<or> flRule fl = FAssume"
  with wf fl show "flNum fl \<in> scopeOf F (flNum fl)"
    using premise_in_scope assume_in_scope by blast
qed

lemma deltaAux_scope:
  assumes wf: "fitchWF F"
  shows "\<lbrakk> set fls \<subseteq> set (flatten F);
           \<forall>l \<in> set acc. references l \<subseteq> scopeOf F (lineNumber l) \<rbrakk>
         \<Longrightarrow> \<forall>l \<in> set (deltaAux acc fls). references l \<subseteq> scopeOf F (lineNumber l)"
proof (induction fls arbitrary: acc)
  case (Cons fl fls)
  let ?l = "ProofLine (flNum fl) (flFm fl) (toLemmonRule (flRule fl))
                (depsOf (depsAt acc) (toLemmonRule (flRule fl)) (flNum fl))"
  from Cons.prems have "fl \<in> set (flatten F)" by simp
  with depsOf_scopeOf [OF wf _ Cons.prems(2)]
  have "references ?l \<subseteq> scopeOf F (lineNumber ?l)" by simp
  with Cons.prems have "\<forall>l \<in> set (acc @ [?l]). references l \<subseteq> scopeOf F (lineNumber l)" by auto
  from Cons.IH [OF _ this] Cons.prems show ?case by simp
qed simp

theorem proposition_5:
  assumes "fitchWF F"
  shows "\<forall>l \<in> set (\<delta> F). references l \<subseteq> scopeOf F (lineNumber l)"
  using deltaAux_scope [OF assms, of "flatten F" "[]"] by (simp add: \<delta>_def)

subsection \<open>Theorem 4, the direction that holds\<close>

text \<open>Weakening the assumptions a side condition must avoid can only license
  more, so a proof that passes the Fitch check passes the Lemmon check.\<close>

lemma depFms_mono: "S \<subseteq> T \<Longrightarrow> set (depFms E S) \<subseteq> set (depFms E T)"
  by (auto simp: depFms_def)

lemma checkFrom_gen_weaken:
  "\<lbrakk> checkFrom_gen B E P;
     \<And>E' l. l \<in> set P \<Longrightarrow>
        set (A E' (lineNumber l) (references l)) \<subseteq> set (B E' (lineNumber l) (references l)) \<rbrakk>
   \<Longrightarrow> checkFrom_gen A E P"
proof (induction P arbitrary: E)
  case (Cons l ls)
  from Cons.prems(1) have ok: "lineOK_gen B E l" and rest: "checkFrom_gen B (E @ [l]) ls" by auto
  from ok have refs: "references l = depsOf (depsAt E) (justification l) (lineNumber l)"
    by (simp only: lineOK_gen_def Let_def)
  from ok refs have rok: "ruleOK E (formula l) (B E (lineNumber l) (references l)) (justification l)"
    by (simp only: lineOK_gen_def Let_def)
  have sub: "set (A E (lineNumber l) (references l))
               \<subseteq> set (B E (lineNumber l) (references l))"
    by (rule Cons.prems(2)) simp
  from ruleOK_antitone [OF sub rok] ok refs have "lineOK_gen A E l"
    by (simp only: lineOK_gen_def Let_def)
  moreover have "checkFrom_gen A (E @ [l]) ls"
  proof (rule Cons.IH [OF rest])
    fix E' l' assume "l' \<in> set ls"
    then have "l' \<in> set (l # ls)" by simp
    then show "set (A E' (lineNumber l') (references l'))
                 \<subseteq> set (B E' (lineNumber l') (references l'))"
      by (rule Cons.prems(2))
  qed
  ultimately show ?case by simp
qed simp

theorem theorem_4_forward:
  assumes "fitchCorrect F"
  shows "lemmonCorrect (\<delta> F)"
proof -
  from assms have wf: "fitchWF F" and chk: "checkFrom_gen (scopeSrc F) [] (\<delta> F)"
    by (auto simp: fitchCorrect_def)
  have "sorted_wrt (<) (map lineNumber (\<delta> F))"
    using wf by (simp only: delta_nums fitchWF_def)
  moreover have "checkFrom_gen depSrc [] (\<delta> F)"
  proof (rule checkFrom_gen_weaken [OF chk])
    fix E' :: lemmon_proof and l assume "l \<in> set (\<delta> F)"
    with proposition_5 [OF wf] have "references l \<subseteq> scopeOf F (lineNumber l)" by blast
    then show "set (depSrc E' (lineNumber l) (references l))
                 \<subseteq> set (scopeSrc F E' (lineNumber l) (references l))"
      unfolding depSrc_def scopeSrc_def by (rule depFms_mono)
  qed
  ultimately show ?thesis by (simp only: lemmonCorrect_def)
qed

subsection \<open>Proposition 7: the dependency column is redundant\<close>

text \<open>@{text stripDeps} deletes the dependency column; @{text recompute} runs
  the recursion of Definition 3 on what is left.  It uses only the
  justifications, so it returns the column it was not given.\<close>

type_synonym stripped_line = "nat \<times> fm \<times> just"

definition stripDeps :: "lemmon_proof \<Rightarrow> stripped_line list" where
  "stripDeps P = map (\<lambda>l. (lineNumber l, formula l, justification l)) P"

fun recomputeAux :: "lemmon_proof \<Rightarrow> stripped_line list \<Rightarrow> lemmon_proof" where
  "recomputeAux acc [] = acc"
| "recomputeAux acc ((n, f, j) # ls) =
     recomputeAux (acc @ [ProofLine n f j (depsOf (depsAt acc) j n)]) ls"

definition recompute :: "stripped_line list \<Rightarrow> lemmon_proof" where
  "recompute = recomputeAux []"

lemma recomputeAux_id:
  "checkFrom_gen A acc P \<Longrightarrow> recomputeAux acc (stripDeps P) = acc @ P"
proof (induction P arbitrary: acc)
  case (Cons l ls)
  from Cons.prems have "references l = depsOf (depsAt acc) (justification l) (lineNumber l)"
    by (simp add: lineOK_gen_def Let_def)
  then have "ProofLine (lineNumber l) (formula l) (justification l)
               (depsOf (depsAt acc) (justification l) (lineNumber l)) = l"
    by (cases l) simp
  with Cons show ?case by (simp add: stripDeps_def)
next
  show "\<And>acc. checkFrom_gen A acc [] \<Longrightarrow> recomputeAux acc (stripDeps []) = acc @ []"
    by (simp add: stripDeps_def)
qed 

theorem proposition_7:
  assumes "lemmonCorrect P"
  shows "recompute (stripDeps P) = P"
  using assms recomputeAux_id [of depSrc "[]" P]
  by (simp add: lemmonCorrect_def recompute_def)

text \<open>The same recursion, applied to a Fitch proof, is \<open>\<delta>\<close>: Proposition 7's
  proof is the observation that Definition 3 never reads the column.\<close>

lemma delta_is_recompute:
  "\<delta> F = recompute (map (\<lambda>fl. (flNum fl, flFm fl, toLemmonRule (flRule fl))) (flatten F))"
proof -
  have "deltaAux acc fls
          = recomputeAux acc (map (\<lambda>fl. (flNum fl, flFm fl, toLemmonRule (flRule fl))) fls)"
    for acc fls by (induction fls arbitrary: acc, auto)
  then show ?thesis by (simp only: \<delta>_def recompute_def)
qed

end
