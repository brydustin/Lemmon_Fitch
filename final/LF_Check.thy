(*  Title:      LF_Check.thy

    The reduction of (L4).

    fitchCorrect runs the Lemmon checker over the whole of \<delta> F, left to
    right, each line against the prefix already read.  What the traversal of
    Definition 21 knows is local: it knows, line by line, what it emitted.  This
    theory closes the gap between the two, so that (L4) becomes a statement
    about one line at a time.
*)

theory LF_Check
  imports LF_WellFormed LF_Faithful
begin

section \<open>\<open>\<delta>\<close> as a running check\<close>

text \<open>@{const deltaAux} carries an accumulator, and the accumulator is exactly
  the prefix the checker will have read when it reaches the line being built:
  Definition 3 and the checker of Definition 1 walk the proof in step.  Making
  that visible is a matter of splitting off the part @{const deltaAux} appends.

  \<open>deltaLine\<close> below is a definition rather than a function so that the
  simplifier leaves it alone; the four selector equations are all that is ever
  wanted of it, and unfolding it in a goal only makes the goal larger.\<close>

definition deltaLine :: "lemmon_proof \<Rightarrow> fline \<Rightarrow> pline" where
  "deltaLine acc fl =
     ProofLine (flNum fl) (flFm fl) (toLemmonRule (flRule fl))
       (depsOf (depsAt acc) (toLemmonRule (flRule fl)) (flNum fl))"

lemma deltaLine_sel [simp]:
  "lineNumber (deltaLine acc fl) = flNum fl"
  "formula (deltaLine acc fl) = flFm fl"
  "justification (deltaLine acc fl) = toLemmonRule (flRule fl)"
  "references (deltaLine acc fl)
     = depsOf (depsAt acc) (toLemmonRule (flRule fl)) (flNum fl)"
  by (simp_all add: deltaLine_def)

fun deltaFrom :: "lemmon_proof \<Rightarrow> fline list \<Rightarrow> lemmon_proof" where
  "deltaFrom acc [] = []"
| "deltaFrom acc (fl # fls) = deltaLine acc fl # deltaFrom (acc @ [deltaLine acc fl]) fls"

lemma deltaAux_eq: "deltaAux acc fls = acc @ deltaFrom acc fls"
  by (induction fls arbitrary: acc) (simp_all add: deltaLine_def)

lemma delta_deltaFrom: "\<delta> F = deltaFrom [] (flatten F)"
  by (simp add: \<delta>_def deltaAux_eq)

lemma deltaAux_step:
  "deltaAux acc (fls @ [fl]) = deltaAux acc fls @ [deltaLine (deltaAux acc fls) fl]"
  by (simp add: deltaAux_append deltaLine_def)

subsection \<open>Two small facts about lists of lines\<close>

lemma lookupLine_nums: "m \<in> set (map lineNumber E) \<Longrightarrow> lookupLine E m \<noteq> None"
  by (induction E) auto

lemma depFms_append: "depFms (E @ E') G = depFms E G @ depFms E' G"
  by (simp add: depFms_def)

section \<open>The reduction\<close>

text \<open>Three hypotheses.  The first is the sortedness half of @{const fitchWF}.
  The second says that a Lemmon citation of the image reaches backwards to a
  line that is there --- Proposition 18 for the image rather than for the
  source.  The third is the local statement: each flattened line's rule checks,
  against the whole of @{term "\<delta> F"} and against the assumptions in scope.

  The third is stated against the whole image, not against the prefix, because
  that is the convenient thing to prove; the two moves that make it usable are
  that a rule check reads the proof only where the justification cites (@{thm
  [source] ruleOK_prefix}), and that a rule check is antitone in the assumption
  list (@{thm [source] ruleOK_antitone}), so a check that survives the longer
  list survives the shorter.\<close>

theorem delta_check:
  assumes srt: "sorted_wrt (<) (map flNum (flatten F))"
      and cited: "\<And>fl m. fl \<in> set (flatten F) \<Longrightarrow>
                    m \<in> set (citedLines (toLemmonRule (flRule fl))) \<Longrightarrow>
                    m < flNum fl \<and> m \<in> set (map flNum (flatten F))"
      and rules: "\<And>fl. fl \<in> set (flatten F) \<Longrightarrow>
                    ruleOK (\<delta> F) (flFm fl)
                           (depFms (\<delta> F) (scopeOf F (flNum fl)))
                           (toLemmonRule (flRule fl))"
  shows "checkFrom_gen (scopeSrc F) [] (\<delta> F)"
proof -
  have key: "\<forall>pre. flatten F = pre @ post \<longrightarrow>
               checkFrom_gen (scopeSrc F) (deltaAux [] pre) (deltaFrom (deltaAux [] pre) post)"
    for post
  proof (induction post)
    case Nil
    show ?case by simp
  next
    case (Cons fl post')
    show ?case
    proof (intro allI impI)
      fix pre assume split: "flatten F = pre @ fl # post'"
      let ?acc = "deltaAux [] pre"
      let ?l = "deltaLine ?acc fl"
      let ?j = "toLemmonRule (flRule fl)"
      let ?S = "scopeOf F (flNum fl)"

      have flmem: "fl \<in> set (flatten F)" using split by simp
      have accn: "map lineNumber ?acc = map flNum pre" by (simp add: deltaAux_nums)

      text \<open>Nothing from this line on is numbered below this line.\<close>
      have ahead: "\<forall>x \<in> set (map flNum (fl # post')). flNum fl \<le> x"
      proof -
        from srt split have "sorted_wrt (<) (map flNum pre @ map flNum (fl # post'))"
          by simp
        then have "sorted_wrt (<) (map flNum (fl # post'))"
          by (simp add: sorted_wrt_append)
        then show ?thesis by auto
      qed

      text \<open>So every line the rule cites has been read already.\<close>
      have cit: "lookupLine ?acc m \<noteq> None" if m: "m \<in> set (citedLines ?j)" for m
      proof -
        from cited [OF flmem m] have lt: "m < flNum fl"
          and mem: "m \<in> set (map flNum (flatten F))" by auto
        from mem split have "m \<in> set (map flNum pre) \<union> set (map flNum (fl # post'))"
          by simp
        with ahead lt have "m \<in> set (map flNum pre)" by auto
        with accn show ?thesis by (simp add: lookupLine_nums)
      qed
      have citB: "\<forall>m \<in> set (citedLines ?j). lookupLine ?acc m \<noteq> None" using cit by blast

      text \<open>The accumulator is a prefix of the image.\<close>
      have dF: "\<delta> F = ?acc @ deltaFrom ?acc (fl # post')"
      proof -
        have "\<delta> F = deltaAux [] (pre @ fl # post')" unfolding \<delta>_def split ..
        also have "\<dots> = deltaAux ?acc (fl # post')" by (rule deltaAux_append)
        also have "\<dots> = ?acc @ deltaFrom ?acc (fl # post')" by (rule deltaAux_eq)
        finally show ?thesis .
      qed

      have lok: "lineOK_gen (scopeSrc F) ?acc ?l"
      proof -
        have B: "list_all (\<lambda>m. lookupLine ?acc m \<noteq> None) (citedLines ?j)"
          unfolding list_all_iff using citB by simp
        have C: "ruleOK ?acc (flFm fl) (depFms ?acc ?S) ?j"
        proof -
          have sub: "set (depFms ?acc ?S) \<subseteq> set (depFms (\<delta> F) ?S)"
            by (simp add: dF depFms_append)
          from ruleOK_antitone [OF sub rules [OF flmem]]
          have "ruleOK (\<delta> F) (flFm fl) (depFms ?acc ?S) ?j" .
          then show ?thesis by (simp add: dF ruleOK_prefix [OF citB])
        qed
        show ?thesis
          unfolding lineOK_gen_def Let_def
          using B C by (simp add: scopeSrc_def)
      qed

      have accl: "deltaAux [] (pre @ [fl]) = ?acc @ [?l]" by (rule deltaAux_step)
      have "flatten F = (pre @ [fl]) @ post'" using split by simp
      with Cons.IH have "checkFrom_gen (scopeSrc F) (deltaAux [] (pre @ [fl]))
                           (deltaFrom (deltaAux [] (pre @ [fl])) post')" by blast
      then have IH': "checkFrom_gen (scopeSrc F) (?acc @ [?l]) (deltaFrom (?acc @ [?l]) post')"
        unfolding accl .
      from lok IH' show "checkFrom_gen (scopeSrc F) ?acc (deltaFrom ?acc (fl # post'))"
        by simp
    qed
  qed
  have "flatten F = [] @ flatten F" by simp
  with key [of "flatten F"]
  have "checkFrom_gen (scopeSrc F) (deltaAux [] []) (deltaFrom (deltaAux [] []) (flatten F))"
    by blast
  then show ?thesis by (simp add: delta_deltaFrom)
qed


section \<open>Citations of the image reach backwards\<close>

text \<open>The second hypothesis of @{thm [source] delta_check} is Proposition 18 for
  the image: a Lemmon justification of @{term "\<delta> F"} cites only lines of
  @{term "\<delta> F"} with smaller numbers.  For the lines a Fitch rule cites this
  is immediate from @{const citationOK}.  For the \emph{subproofs} it cites it is
  not, because a subproof reference names two lines and @{const citationOK}
  bounds only the second: the missing step is that a subproof's assumption line
  does not come after its conclusion.  It does not, because the assumption line
  heads the subproof and the numbers increase.\<close>

lemma sorted_wrt_itemsNums_mem:
  "sorted_wrt (<) (itemsNums its) \<Longrightarrow> it \<in> set its \<Longrightarrow> sorted_wrt (<) (itemNums it)"
  by (induction its) (auto simp: sorted_wrt_append)

lemma subLastLine_in_subNums:
  assumes "lastIsLineSub s"
  shows "subLastLine s \<in> set (subNums s)"
proof (cases s)
  case (Subproof a fa body)
  with assms have lil: "lastIsLineSub (Subproof a fa body)" by simp
  from subLastLine_last [OF lil] obtain f r
    where L: "last (flatSub (Subproof a fa body) []) =
                FL (subLastLine (Subproof a fa body)) f r ([] @ [a])" by blast
  have "flatSub (Subproof a fa body) [] \<noteq> []" by simp
  with L have mem: "FL (subLastLine (Subproof a fa body)) f r ([] @ [a])
                      \<in> set (flatSub (Subproof a fa body) [])"
    using last_in_set by metis
  have "subLastLine (Subproof a fa body)
          \<in> set (map flNum (flatSub (Subproof a fa body) []))"
    unfolding set_map by (rule image_eqI [OF _ mem]) simp
  then show ?thesis using Subproof by (simp only: flNum_flatSub)
qed

lemma subref_le:
  "\<forall>path. sorted_wrt (<) (itemNums it) \<longrightarrow> lastIsLineItem it \<longrightarrow>
     (\<forall>x \<in> set (subrefsItem it path). fst (fst x) \<le> snd (fst x))"
  "\<forall>path. sorted_wrt (<) (subNums s) \<longrightarrow> lastIsLineSub s \<longrightarrow>
     (\<forall>x \<in> set (subrefsSub s path). fst (fst x) \<le> snd (fst x))"
proof (induction it and s)
  case (Subproof a fa body)
  show ?case
  proof (intro allI impI ballI)
    fix path x
    assume srt: "sorted_wrt (<) (subNums (Subproof a fa body))"
       and lil: "lastIsLineSub (Subproof a fa body)"
       and x: "x \<in> set (subrefsSub (Subproof a fa body) path)"
    show "fst (fst x) \<le> snd (fst x)"
    proof (cases "x = ((a, subLastLine (Subproof a fa body)), path)")
      case True
      from subLastLine_in_subNums [OF lil] srt
      have "a \<le> subLastLine (Subproof a fa body)" by fastforce
      with True show ?thesis by simp
    next
      case False
      with x obtain it' where it': "it' \<in> set body"
        and xit: "x \<in> set (subrefsItem it' (path @ [a]))" by auto
      from srt have "sorted_wrt (<) (itemsNums body)" by (simp add: itemsNums_def)
      from sorted_wrt_itemsNums_mem [OF this it'] have s': "sorted_wrt (<) (itemNums it')" .
      from lil it' have l': "lastIsLineItem it'" by (auto simp: list_all_iff)
      from Subproof.IH [OF it'] s' l' xit show ?thesis by blast
    qed
  qed
qed simp_all

lemma subrefs_le:
  assumes wf: "fitchWF F" and sr: "((a, c), P) \<in> set (subrefs F)"
  shows "a \<le> c"
proof -
  from sr obtain it where it: "it \<in> set F" and x: "((a, c), P) \<in> set (subrefsItem it [])"
    by (auto simp: subrefs_def)
  from wf have "sorted_wrt (<) (itemsNums F)" by (simp add: fitchWF_def flatten_eq)
  from sorted_wrt_itemsNums_mem [OF this it] have s: "sorted_wrt (<) (itemNums it)" .
  from wf it have l: "lastIsLineItem it" by (auto simp: fitchWF_def list_all_iff)
  have "\<forall>y \<in> set (subrefsItem it []). fst (fst y) \<le> snd (fst y)"
    using subref_le(1) [of it] s l by blast
  with x show ?thesis by auto
qed

lemma fitchWF_cited:
  assumes wf: "fitchWF F" and fl: "fl \<in> set (flatten F)"
      and m: "m \<in> set (citedLines (toLemmonRule (flRule fl)))"
  shows "m < flNum fl \<and> m \<in> set (map flNum (flatten F))"
proof -
  from wf fl have cok: "citationOK F fl" by (auto simp: fitchWF_def list_all_iff)
  from m consider (line) "m \<in> set (fCitedLines (flRule fl))"
    | (sub) a c where "(a, c) \<in> set (fCitedSubs (flRule fl))" and "m = a \<or> m = c"
    using citedLines_toLemmonRule [of "flRule fl"] by auto
  then show ?thesis
  proof cases
    case line
    with cok have lt: "m < flNum fl"
      and f: "case findFL (flatten F) m of None \<Rightarrow> False
                | Some fl' \<Rightarrow> is_prefix (flScope fl') (flScope fl)"
      by (auto simp: citationOK_def list_all_iff)
    from f obtain fl' where "findFL (flatten F) m = Some fl'"
      by (cases "findFL (flatten F) m") auto
    then have "flNum fl' = m" and "fl' \<in> set (flatten F)" by (auto dest: findFL_Some)
    with lt show ?thesis by force
  next
    case (sub a c)
    with cok have lt: "c < flNum fl" and sr: "((a, c), flScope fl) \<in> set (subrefs F)"
      by (auto simp: citationOK_def list_all_iff)
    from subrefs_le [OF wf sr] have le: "a \<le> c" .
    from subrefs_lines [OF wf sr] obtain f f' r'
      where A: "FL a f FAssume (flScope fl @ [a]) \<in> set (flatten F)"
        and C: "FL c f' r' (flScope fl @ [a]) \<in> set (flatten F)" by blast
    from A have "a \<in> set (map flNum (flatten F))" by force
    moreover from C have "c \<in> set (map flNum (flatten F))" by force
    ultimately show ?thesis using sub(2) lt le by auto
  qed
qed

text \<open>So (L4) for a well-formed Fitch proof is exactly a statement about one
  line at a time: a well-formed Fitch proof each of whose lines applies its rule
  correctly --- read against the assumptions in scope, which is Fitch's
  bookkeeping and not Lemmon's --- is a correct Fitch proof.\<close>

theorem fitchCorrect_lines:
  assumes wf: "fitchWF F"
      and rules: "\<And>fl. fl \<in> set (flatten F) \<Longrightarrow>
                    ruleOK (\<delta> F) (flFm fl)
                           (depFms (\<delta> F) (scopeOf F (flNum fl)))
                           (toLemmonRule (flRule fl))"
  shows "fitchCorrect F"
  unfolding fitchCorrect_def
proof
  show "fitchWF F" by (rule wf)
  show "checkFrom_gen (scopeSrc F) [] (\<delta> F)"
  proof (rule delta_check)
    show "sorted_wrt (<) (map flNum (flatten F))" using wf by (simp add: fitchWF_def)
  qed (use wf rules fitchWF_cited in blast)+
qed


section \<open>Reading the image at a line\<close>

text \<open>The rule check of @{thm [source] fitchCorrect_lines} runs against
  @{term "\<delta> F"}, and what it reads there is the formula and the
  justification at a cited number.  Both are read off the flattened Fitch proof
  directly: @{text \<delta>} copies the number, the formula and the rule of each line
  and computes only the dependency column, which the check never consults.\<close>

lemma deltaAux_triples:
  "map (\<lambda>l. (lineNumber l, formula l, justification l)) (deltaAux acc fls)
     = map (\<lambda>l. (lineNumber l, formula l, justification l)) acc
       @ map (\<lambda>fl. (flNum fl, flFm fl, toLemmonRule (flRule fl))) fls"
  by (induction fls arbitrary: acc) auto

lemma delta_triples:
  "map (\<lambda>l. (lineNumber l, formula l, justification l)) (\<delta> F)
     = map (\<lambda>fl. (flNum fl, flFm fl, toLemmonRule (flRule fl))) (flatten F)"
  by (simp add: \<delta>_def deltaAux_triples)

lemma delta_lookup:
  assumes wf: "fitchWF F" and fl: "fl \<in> set (flatten F)"
  shows "fmAt (\<delta> F) (flNum fl) = Some (flFm fl)"
    and "justAt (\<delta> F) (flNum fl) = Some (toLemmonRule (flRule fl))"
proof -
  have "(flNum fl, flFm fl, toLemmonRule (flRule fl))
          \<in> set (map (\<lambda>l. (lineNumber l, formula l, justification l)) (\<delta> F))"
    unfolding delta_triples using fl by force
  then obtain l where l: "l \<in> set (\<delta> F)" and n: "lineNumber l = flNum fl"
    and f: "formula l = flFm fl" and j: "justification l = toLemmonRule (flRule fl)"
    by auto
  from wf have "distinct (map lineNumber (\<delta> F))"
    by (simp add: delta_nums fitchWF_distinct)
  from lookupLine_mem [OF this l] n have "lookupLine (\<delta> F) (flNum fl) = Some l" by simp
  with f show "fmAt (\<delta> F) (flNum fl) = Some (flFm fl)" by (simp add: fmAt_def)
  from \<open>lookupLine (\<delta> F) (flNum fl) = Some l\<close> j
  show "justAt (\<delta> F) (flNum fl) = Some (toLemmonRule (flRule fl))"
    by (simp add: justAt_def)
qed

lemma delta_isAssumptionLine:
  assumes "fitchWF F" and "fl \<in> set (flatten F)"
      and "flRule fl = FAssume \<or> flRule fl = FPremise"
  shows "isAssumptionLine (\<delta> F) (flNum fl)"
  using delta_lookup(2) [OF assms(1,2)] assms(3)
  by (auto simp: isAssumptionLine_def)

text \<open>And what the check offers a side condition is the assumptions in scope:
  the premises, together with the assumption of every subproof the line sits
  inside --- which is the line's scope path.\<close>

lemma scopeOf_flScope:
  assumes "fitchWF F" and "fl \<in> set (flatten F)"
  shows "scopeOf F (flNum fl) = set (premiseLines F) \<union> set (flScope fl)"
  using scopePath_eq [OF assms] by (simp add: scopeOf_def)

section \<open>The lines that need no checking\<close>

text \<open>A premise and the assumption heading a subproof become @{const Assumption}
  under @{const toLemmonRule}, and @{const ruleOK} asks nothing of an
  assumption: Definition 1 lets a line be assumed outright, and the whole of the
  bookkeeping is in the dependency set, which @{text \<delta>} computes rather than
  checks.  So (L4) is a statement about the lines that apply a rule.\<close>

lemma ruleOK_assume:
  assumes "flRule fl = FAssume \<or> flRule fl = FPremise"
  shows "ruleOK E (flFm fl) As (toLemmonRule (flRule fl))"
  using assms by auto

theorem fitchCorrect_ruleLines:
  assumes wf: "fitchWF F"
      and rules: "\<And>fl. fl \<in> set (flatten F) \<Longrightarrow> flRule fl \<noteq> FAssume \<Longrightarrow>
                    flRule fl \<noteq> FPremise \<Longrightarrow>
                    ruleOK (\<delta> F) (flFm fl)
                           (depFms (\<delta> F) (scopeOf F (flNum fl)))
                           (toLemmonRule (flRule fl))"
  shows "fitchCorrect F"
proof (rule fitchCorrect_lines [OF wf])
  fix fl assume fl: "fl \<in> set (flatten F)"
  show "ruleOK (\<delta> F) (flFm fl) (depFms (\<delta> F) (scopeOf F (flNum fl)))
               (toLemmonRule (flRule fl))"
  proof (cases "flRule fl = FAssume \<or> flRule fl = FPremise")
    case True
    then show ?thesis by (rule ruleOK_assume)
  next
    case False
    with fl show ?thesis by (auto intro: rules)
  qed
qed


section \<open>What the traversal knows about the formulas it emits\<close>

text \<open>The numbers and formulas of the lines an item contributes do not depend on
  where the item sits: only the scope path does.  So they may be read off the
  item itself, which is what the traversal has in hand.\<close>

primrec itemNumFms :: "fitch_item \<Rightarrow> (nat \<times> fm) list"
    and subNumFms :: "subproof \<Rightarrow> (nat \<times> fm) list" where
  "itemNumFms (FLine n f r) = [(n, f)]"
| "itemNumFms (FSub s) = subNumFms s"
| "subNumFms (Subproof a fa body) = (a, fa) # concat (map itemNumFms body)"

definition itemsNumFms :: "fitch_item list \<Rightarrow> (nat \<times> fm) list" where
  "itemsNumFms its = concat (map itemNumFms its)"

lemma itemsNumFms_simps [simp]:
  "itemsNumFms [] = []"
  "itemsNumFms (it # its) = itemNumFms it @ itemsNumFms its"
  "itemsNumFms (xs @ ys) = itemsNumFms xs @ itemsNumFms ys"
  by (auto simp: itemsNumFms_def)

lemma numFm_flat_all:
  "\<forall>p. map (\<lambda>fl. (flNum fl, flFm fl)) (flatItem it p) = itemNumFms it"
  "\<forall>q. map (\<lambda>fl. (flNum fl, flFm fl)) (flatSub s q) = subNumFms s"
  by (induction it and s) (auto simp: map_concat cong: map_cong)

lemma subNumFms_nonempty [simp]: "subNumFms s \<noteq> []"
  by (cases s) simp

lemma itemNumFms_nonempty [simp]: "itemNumFms it \<noteq> []"
  by (cases it) simp_all

lemma numFm_flatItems:
  "map (\<lambda>fl. (flNum fl, flFm fl)) (flatItems its path) = itemsNumFms its"
  by (induction its) (auto simp: numFm_flat_all(1) [rule_format])

subsection \<open>The environment carries the right formulas\<close>

text \<open>@{const boundIn} says every label the derivation still rests on is bound in
  the environment.  This says what it is bound to: the formula the leaves
  carrying that label carry.  For a discharge it is @{const dischargeOK}; at the
  root it is what @{const premEnv} was built from.\<close>

definition envNumFms :: "env \<Rightarrow> (nat \<times> fm) list" where
  "envNumFms G = map (\<lambda>e. (fst (snd e), snd (snd e))) G"

text \<open>What the environment must say about a label: not that every entry
  carrying it agrees --- an outer entry may be shadowed --- but that the entry
  @{const envLine} will actually find carries the formula the leaves carry.\<close>

definition envMatches :: "env \<Rightarrow> deriv \<Rightarrow> bool" where
  "envMatches G d \<longleftrightarrow>
     (\<forall>nf \<in> set (openAsms d).
        \<exists>e. find (\<lambda>g. fst g = fst nf) G = Some e \<and> snd (snd e) = snd nf)"

lemma find_Some_mem: "find P xs = Some x \<Longrightarrow> x \<in> set xs \<and> P x"
  by (induction xs) (auto split: if_splits)

subsection \<open>The conclusion line carries the node's formula\<close>

text \<open>Either the traversal emitted a line for this node --- and then the last
  item it emitted is that line, whatever the rule --- or the node is a leaf and
  it emitted nothing, pointing instead at the environment.\<close>

definition emitConcl :: "env \<Rightarrow> fitch_item list \<Rightarrow> nat \<Rightarrow> fm \<Rightarrow> bool" where
  "emitConcl G its c phi \<longleftrightarrow> (c, phi) \<in> set (envNumFms G) \<union> set (itemsNumFms its)"

lemma emit_concl_fm:
  assumes em: "envMatches G d"
      and e: "emit base G nx cnt d = (its, c, nx', cnt')"
  shows "emitConcl G its c (dForm d)"
proof (cases "its = []")
  case False
  from emit_conclusion_line [OF e False] obtain rl where lst: "last its = FLine c (dForm d) rl"
    by blast
  from False have mem: "last its \<in> set its" by (rule last_in_set)
  have "(c, dForm d) \<in> set (itemNumFms (last its))" by (simp add: lst)
  with mem have "(c, dForm d) \<in> set (itemsNumFms its)" by (auto simp: itemsNumFms_def)
  then show ?thesis by (simp add: emitConcl_def)
next
  case True
  with e obtain a where r: "dRule d = DAssume a \<or> dRule d = DPremise a"
    using emit_nil_leaf by blast
  then have oa: "openAsms d = [(a, dForm d)]" by (cases d) auto
  from r e True have c: "c = envLine G a" by (cases d) auto
  from em oa obtain g where g: "find (\<lambda>h. fst h = a) G = Some g"
    and gf: "snd (snd g) = dForm d" by (fastforce simp: envMatches_def)
  from find_Some_mem [OF g] have gmem: "g \<in> set G" by simp
  from g c have cg: "c = fst (snd g)" by (simp add: envLine_def)
  have "(c, dForm d) = snd g" using cg gf [symmetric] by simp
  moreover from gmem have "snd g \<in> set (envNumFms G)" by (force simp: envNumFms_def)
  ultimately show ?thesis by (simp add: emitConcl_def)
qed


section \<open>A rule check reads the proof only where the justification cites\<close>

text \<open>@{thm [source] ruleOK_prefix} is the instance of this for an extension by
  appending.  The general form is what carries a check proved against the
  formulas the traversal has in hand over to a check against @{term "\<delta> F"}:
  the two agree wherever the justification looks, and a rule check looks
  nowhere else.  Note that a discharging rule cites the assumption line it
  names, so @{const isAssumptionLine} is covered by the same quantifier.\<close>

lemma ruleOK_lookup_cong:
  assumes "\<And>m. m \<in> set (citedLines j) \<Longrightarrow> fmAt E m = fmAt E' m"
      and "\<And>m. m \<in> set (citedLines j) \<Longrightarrow> isAssumptionLine E m = isAssumptionLine E' m"
  shows "ruleOK E phi As j = ruleOK E' phi As j"
  using assms by (cases j) (simp_all split: option.splits fm.splits trm.splits)

text \<open>Specialised to the image: a check that holds when the cited formulas and
  justifications are read off the flattened Fitch proof holds against
  @{term "\<delta> F"}.\<close>

lemma ruleOK_delta:
  assumes wf: "fitchWF F"
      and look: "\<And>m. m \<in> set (citedLines j) \<Longrightarrow>
                   \<exists>fl \<in> set (flatten F). flNum fl = m
                     \<and> fmAt E m = Some (flFm fl)
                     \<and> justAt E m = Some (toLemmonRule (flRule fl))"
      and ok: "ruleOK E phi As j"
  shows "ruleOK (\<delta> F) phi As j"
proof -
  have "ruleOK (\<delta> F) phi As j = ruleOK E phi As j"
  proof (rule ruleOK_lookup_cong)
    fix m assume m: "m \<in> set (citedLines j)"
    from look [OF m] obtain fl where fl: "fl \<in> set (flatten F)" and n: "flNum fl = m"
      and f: "fmAt E m = Some (flFm fl)"
      and jt: "justAt E m = Some (toLemmonRule (flRule fl))" by blast
    from delta_lookup [OF wf fl] n f
    show "fmAt (\<delta> F) m = fmAt E m" by simp
    from delta_lookup(2) [OF wf fl] n jt
    show "isAssumptionLine (\<delta> F) m = isAssumptionLine E m"
      by (simp add: isAssumptionLine_def)
  qed
  with ok show ?thesis by simp
qed


section \<open>The renaming repair preserves what the traversal relies on\<close>

text \<open>Section 5.4 renames the subderivation feeding a universal introduction
  when its eigenvariable occurs in an assumption Fitch has in scope.  Three
  things have to survive that: the subderivation stays correct, its open
  assumptions are untouched, and the next repair still has a fresh name to use.
  The first two are Corollary 24; the third is what the counter is for.\<close>

subsection \<open>Lengths\<close>

lemma maxlen_le: "\<forall>a \<in> set used. nlen a \<le> k \<Longrightarrow> maxlen used \<le> k"
  by (induction used) (auto simp: maxlen_def)

text \<open>@{term "base + cnt"} is the length of the name the next repair will use, and
  the invariant is that every name in the derivation is shorter than that.  A
  repair adds one name, of exactly that length, and increments the counter; so
  the invariant survives, which is the whole reason @{const uniCnt} counts.\<close>

definition namesBelow :: "nat \<Rightarrow> nat \<Rightarrow> deriv \<Rightarrow> bool" where
  "namesBelow base cnt d \<longleftrightarrow> maxlen (namesD d) < base + cnt"

lemma namesBelow_mono: "namesBelow base cnt d \<Longrightarrow> cnt \<le> cnt' \<Longrightarrow> namesBelow base cnt' d"
  by (simp add: namesBelow_def)

lemma namesBelow_sub:
  assumes "namesBelow base cnt d" and "set (namesD e) \<subseteq> set (namesD d)"
  shows "namesBelow base cnt e"
proof -
  have "\<forall>a \<in> set (namesD e). nlen a \<le> maxlen (namesD d)"
    using assms(2) maxlen_ge by blast
  from maxlen_le [OF this] assms(1) show ?thesis by (simp add: namesBelow_def)
qed

lemma namesBelow_fresh:
  "namesBelow base cnt d \<Longrightarrow> freshIdx base cnt \<notin> set (namesD d)"
  by (simp add: namesBelow_def freshIdx_fresh)

subsection \<open>Universal introduction\<close>

lemma uniRepair_Some:
  assumes "uniRepair G phi d = Some a"
  shows "\<exists>x p. phi = Uni x p \<and> eigenOf x p d = Some a"
  using assms by (cases phi) (auto simp: uniRepair_def split: option.splits if_splits)

lemma uniRepair_arbitrary:
  assumes "uniRepair G phi d = Some a"
  shows "arbitrary_in a (openFms d)"
proof -
  from uniRepair_Some [OF assms] obtain x p where "eigenOf x p d = Some a" by blast
  from eigenOf_Some [OF this] show ?thesis by simp
qed

lemma openAsms_uniD [simp]: "openAsms (uniD base cnt G phi d) = openAsms d"
proof (cases "uniRepair G phi d")
  case None
  then show ?thesis by (simp add: uniD_def)
next
  case (Some a)
  from uniRepair_arbitrary [OF Some] have arb: "arbitrary_in a (openFms d)" .
  have "map (\<lambda>nf. (fst nf, rn a (freshIdx base cnt) (snd nf))) (openAsms d) = openAsms d"
  proof (rule map_idI)
    fix nf assume "nf \<in> set (openAsms d)"
    with arb have "\<not> occurs a (snd nf)" by (auto simp: arbitrary_in_def)
    then show "(fst nf, rn a (freshIdx base cnt) (snd nf)) = nf" by (cases nf) simp
  qed
  with Some show ?thesis by (simp add: uniD_def openAsms_rnD)
qed

lemma derivOK_uniD:
  assumes ok: "derivOK d" and nb: "namesBelow base cnt d"
  shows "derivOK (uniD base cnt G phi d)"
proof (cases "uniRepair G phi d")
  case None
  then show ?thesis using ok by (simp add: uniD_def)
next
  case (Some a)
  from renaming [OF ok namesBelow_fresh [OF nb]]
  have "derivOK (rnD a (freshIdx base cnt) d)" .
  with Some show ?thesis by (simp add: uniD_def)
qed

lemma namesD_uniD:
  "set (namesD (uniD base cnt G phi d)) \<subseteq> set (namesD d) \<union> {freshIdx base cnt}"
  by (auto simp: uniD_def namesD_rnD split: option.splits)

lemma namesBelow_uniD:
  assumes "namesBelow base cnt d"
  shows "namesBelow base (uniCnt cnt G phi d) (uniD base cnt G phi d)"
proof (cases "uniRepair G phi d")
  case None
  then show ?thesis using assms by (simp add: uniD_def uniCnt_def)
next
  case (Some a)
  have "\<forall>c \<in> set (namesD (uniD base cnt G phi d)). nlen c \<le> base + cnt"
  proof
    fix c assume "c \<in> set (namesD (uniD base cnt G phi d))"
    with namesD_uniD have "c \<in> set (namesD d) \<or> c = freshIdx base cnt" by blast
    then show "nlen c \<le> base + cnt"
    proof
      assume "c \<in> set (namesD d)"
      then have "nlen c \<le> maxlen (namesD d)" by (rule maxlen_ge)
      with assms show ?thesis by (simp add: namesBelow_def)
    next
      assume "c = freshIdx base cnt" then show ?thesis by simp
    qed
  qed
  from maxlen_le [OF this] Some show ?thesis by (simp add: namesBelow_def uniCnt_def)
qed

subsection \<open>Existential elimination\<close>

lemma witnessOf_Some:
  assumes "witnessOf ex f psi As = Some b"
  shows "\<exists>x p. ex = Exi x p \<and> inst x b p = f \<and> \<not> occurs b p \<and> \<not> occurs b psi
                \<and> arbitrary_in b As"
proof (cases ex)
  case (Exi x p)
  let ?ws = "filter (\<lambda>b. \<not> occurs b p \<and> \<not> occurs b psi \<and> arbitrary_in b As)
                    (instWitnesses x p f)"
  from assms Exi obtain bs where "?ws = b # bs"
    by (auto simp: witnessOf_def split: list.splits)
  then have "b \<in> set ?ws" by simp
  with Exi show ?thesis by (auto dest: instWitnesses_sound)
qed (use assms in \<open>auto simp: witnessOf_def\<close>)

lemma exRepair_Some:
  assumes "exRepair G ex f psi a d0 d1 = Some b"
  shows "arbitrary_in b (openFms d0 @ map snd (drop_label a (openAsms d1)))"
proof -
  from assms
  have w: "witnessOf ex f psi (openFms d0 @ map snd (drop_label a (openAsms d1))) = Some b"
    by (auto simp: exRepair_def split: option.splits if_splits)
  from witnessOf_Some [OF w] show ?thesis by blast
qed

text \<open>The witness avoids every assumption the subderivation still rests on
  \emph{except} the one being discharged --- which is why @{const exF} renames
  that one too, and puts the renamed formula in the environment.\<close>

lemma openAsms_exD_other:
  assumes "exRepair G ex f psi a d0 d1 = Some b"
  shows "drop_label a (openAsms (exD base cnt G ex f psi a d0 d1))
           = drop_label a (openAsms d1)"
proof -
  from exRepair_Some [OF assms]
  have arb: "\<forall>g \<in> set (map snd (drop_label a (openAsms d1))). \<not> occurs b g"
    by (simp add: arbitrary_in_def)
  have "map (\<lambda>nf. (fst nf, rn b (freshIdx base cnt) (snd nf))) (drop_label a (openAsms d1))
          = drop_label a (openAsms d1)"
  proof (rule map_idI)
    fix nf assume nf: "nf \<in> set (drop_label a (openAsms d1))"
    then have "snd nf \<in> set (map snd (drop_label a (openAsms d1)))" by simp
    with arb have "\<not> occurs b (snd nf)" by blast
    then show "(fst nf, rn b (freshIdx base cnt) (snd nf)) = nf" by (cases nf) simp
  qed
  with assms show ?thesis
    by (simp add: exD_def openAsms_rnD filter_map o_def)
qed

lemma dischargeOK_exD:
  assumes "dischargeOK a f d1"
  shows "dischargeOK a (exF base cnt G ex f psi a d0 d1)
                       (exD base cnt G ex f psi a d0 d1)"
proof (cases "exRepair G ex f psi a d0 d1")
  case None
  then show ?thesis using assms by (simp add: exD_def exF_def)
next
  case (Some b)
  from assms have "dischargeOK a (rn b (freshIdx base cnt) f) (rnD b (freshIdx base cnt) d1)"
    by (rule dischargeOK_rnD)
  with Some show ?thesis by (simp add: exD_def exF_def)
qed

lemma derivOK_exD:
  assumes ok: "derivOK d1" and nb: "namesBelow base cnt d1"
  shows "derivOK (exD base cnt G ex f psi a d0 d1)"
proof (cases "exRepair G ex f psi a d0 d1")
  case None
  then show ?thesis using ok by (simp add: exD_def)
next
  case (Some b)
  from renaming [OF ok namesBelow_fresh [OF nb]]
  have "derivOK (rnD b (freshIdx base cnt) d1)" .
  with Some show ?thesis by (simp add: exD_def)
qed

lemma namesD_exD:
  "set (namesD (exD base cnt G ex f psi a d0 d1))
     \<subseteq> set (namesD d1) \<union> {freshIdx base cnt}"
  by (auto simp: exD_def namesD_rnD split: option.splits)

lemma namesBelow_exD:
  assumes "namesBelow base cnt d1"
  shows "namesBelow base (exCnt cnt G ex f psi a d0 d1) (exD base cnt G ex f psi a d0 d1)"
proof (cases "exRepair G ex f psi a d0 d1")
  case None
  then show ?thesis using assms by (simp add: exD_def exCnt_def)
next
  case (Some b)
  have "\<forall>c \<in> set (namesD (exD base cnt G ex f psi a d0 d1)). nlen c \<le> base + cnt"
  proof
    fix c assume "c \<in> set (namesD (exD base cnt G ex f psi a d0 d1))"
    with namesD_exD have "c \<in> set (namesD d1) \<or> c = freshIdx base cnt" by blast
    then show "nlen c \<le> base + cnt"
    proof
      assume "c \<in> set (namesD d1)"
      then have "nlen c \<le> maxlen (namesD d1)" by (rule maxlen_ge)
      with assms show ?thesis by (simp add: namesBelow_def)
    next
      assume "c = freshIdx base cnt" then show ?thesis by simp
    qed
  qed
  from maxlen_le [OF this] Some show ?thesis by (simp add: namesBelow_def exCnt_def)
qed

section \<open>The repair counter only goes up\<close>

text \<open>Each repair uses a longer name than the last, so a subderivation reached
  later in the traversal is still short enough for its own repairs.  That is the
  content of the counter, and it is what lets @{const namesBelow} be carried
  down the tree.\<close>

lemma emit_cnt_k:
  "\<forall>base G nx cnt d. size d \<le> k \<longrightarrow> cnt \<le> eCnt base G nx cnt d"
proof (induction k)
  case 0
  show ?case
  proof (intro allI impI)
    fix base G nx cnt and d :: deriv
    assume "size d \<le> 0"
    then show "cnt \<le> eCnt base G nx cnt d" by (cases d) simp
  qed
next
  case (Suc k)
  have IH: "\<And>base G nx cnt d. size d \<le> k \<Longrightarrow> cnt \<le> eCnt base G nx cnt d"
    using Suc.IH by blast
  show ?case
  proof (intro allI impI)
    fix base G nx cnt and d :: deriv
    assume sz: "size d \<le> Suc k"
    show "cnt \<le> eCnt base G nx cnt d"
    proof (cases d)
      case (Deriv phi r)
      show ?thesis
      proof (cases r)
        case (DAssume a)
        with Deriv show ?thesis by simp
      next
        case (DPremise a)
        with Deriv show ?thesis by simp
      next
        case (DMP d1 d2)
        obtain i1 c1 n1 t1 where e1: "emit base G nx cnt d1 = (i1, c1, n1, t1)"
          by (rule prod_cases4)
        obtain i2 c2 n2 t2 where e2: "emit base G n1 t1 d2 = (i2, c2, n2, t2)"
          by (rule prod_cases4)
        from sz Deriv \<open>r = DMP d1 d2\<close> have z1: "size d1 \<le> k"
          and z2: "size d2 \<le> k" by simp_all
        have "cnt \<le> eCnt base G nx cnt d1" by (rule IH [OF z1])
        with e1 have A: "cnt \<le> t1" by simp
        have "t1 \<le> eCnt base G n1 t1 d2" by (rule IH [OF z2])
        with e2 A have "cnt \<le> t2" by simp
        with Deriv \<open>r = DMP d1 d2\<close> e1 e2 show ?thesis by simp
      next
        case (DCP a fa d1)
        obtain b1 cc1 n1 t1
          where e1: "emit base ((a, nx, fa) # G) (Suc nx) cnt d1 = (b1, cc1, n1, t1)"
          by (rule prod_cases4)
        obtain b1' l1 n2 where cs: "closeSub nx (dForm d1) b1 cc1 n1 = (b1', l1, n2)"
          by (rule prod_cases3)
        from sz Deriv \<open>r = DCP a fa d1\<close> have s1: "size d1 \<le> k" by simp
        have "cnt \<le> eCnt base ((a, nx, fa) # G) (Suc nx) cnt d1" by (rule IH [OF s1])
        with e1 have "cnt \<le> t1" by simp
        with Deriv \<open>r = DCP a fa d1\<close> e1 cs show ?thesis by simp
      next
        case (DRAA a fa d1)
        obtain b1 cc1 n1 t1
          where e1: "emit base ((a, nx, fa) # G) (Suc nx) cnt d1 = (b1, cc1, n1, t1)"
          by (rule prod_cases4)
        obtain b1' l1 n2 where cs: "closeSub nx (dForm d1) b1 cc1 n1 = (b1', l1, n2)"
          by (rule prod_cases3)
        from sz Deriv \<open>r = DRAA a fa d1\<close> have s1: "size d1 \<le> k" by simp
        have "cnt \<le> eCnt base ((a, nx, fa) # G) (Suc nx) cnt d1" by (rule IH [OF s1])
        with e1 have "cnt \<le> t1" by simp
        with Deriv \<open>r = DRAA a fa d1\<close> e1 cs show ?thesis by simp
      next
        case (DBotI d1 d2)
        obtain i1 c1 n1 t1 where e1: "emit base G nx cnt d1 = (i1, c1, n1, t1)"
          by (rule prod_cases4)
        obtain i2 c2 n2 t2 where e2: "emit base G n1 t1 d2 = (i2, c2, n2, t2)"
          by (rule prod_cases4)
        from sz Deriv \<open>r = DBotI d1 d2\<close> have z1: "size d1 \<le> k"
          and z2: "size d2 \<le> k" by simp_all
        have "cnt \<le> eCnt base G nx cnt d1" by (rule IH [OF z1])
        with e1 have A: "cnt \<le> t1" by simp
        have "t1 \<le> eCnt base G n1 t1 d2" by (rule IH [OF z2])
        with e2 A have "cnt \<le> t2" by simp
        with Deriv \<open>r = DBotI d1 d2\<close> e1 e2 show ?thesis by simp
      next
        case (DAndIntro d1 d2)
        obtain i1 c1 n1 t1 where e1: "emit base G nx cnt d1 = (i1, c1, n1, t1)"
          by (rule prod_cases4)
        obtain i2 c2 n2 t2 where e2: "emit base G n1 t1 d2 = (i2, c2, n2, t2)"
          by (rule prod_cases4)
        from sz Deriv \<open>r = DAndIntro d1 d2\<close> have z1: "size d1 \<le> k"
          and z2: "size d2 \<le> k" by simp_all
        have "cnt \<le> eCnt base G nx cnt d1" by (rule IH [OF z1])
        with e1 have A: "cnt \<le> t1" by simp
        have "t1 \<le> eCnt base G n1 t1 d2" by (rule IH [OF z2])
        with e2 A have "cnt \<le> t2" by simp
        with Deriv \<open>r = DAndIntro d1 d2\<close> e1 e2 show ?thesis by simp
      next
        case (DDN d1)
        obtain i1 c1 n1 t1 where e1: "emit base G nx cnt d1 = (i1, c1, n1, t1)"
          by (rule prod_cases4)
        from sz Deriv \<open>r = DDN d1\<close> have s1: "size d1 \<le> k" by simp
        have "cnt \<le> eCnt base G nx cnt d1" by (rule IH [OF s1])
        with e1 have "cnt \<le> t1" by simp
        with Deriv \<open>r = DDN d1\<close> e1 show ?thesis
          by (simp split: prod.splits)
      next
        case (DAndElimL d1)
        obtain i1 c1 n1 t1 where e1: "emit base G nx cnt d1 = (i1, c1, n1, t1)"
          by (rule prod_cases4)
        from sz Deriv \<open>r = DAndElimL d1\<close> have s1: "size d1 \<le> k" by simp
        have "cnt \<le> eCnt base G nx cnt d1" by (rule IH [OF s1])
        with e1 have "cnt \<le> t1" by simp
        with Deriv \<open>r = DAndElimL d1\<close> e1 show ?thesis
          by (simp split: prod.splits)
      next
        case (DAndElimR d1)
        obtain i1 c1 n1 t1 where e1: "emit base G nx cnt d1 = (i1, c1, n1, t1)"
          by (rule prod_cases4)
        from sz Deriv \<open>r = DAndElimR d1\<close> have s1: "size d1 \<le> k" by simp
        have "cnt \<le> eCnt base G nx cnt d1" by (rule IH [OF s1])
        with e1 have "cnt \<le> t1" by simp
        with Deriv \<open>r = DAndElimR d1\<close> e1 show ?thesis
          by (simp split: prod.splits)
      next
        case (DOrIntroL d1)
        obtain i1 c1 n1 t1 where e1: "emit base G nx cnt d1 = (i1, c1, n1, t1)"
          by (rule prod_cases4)
        from sz Deriv \<open>r = DOrIntroL d1\<close> have s1: "size d1 \<le> k" by simp
        have "cnt \<le> eCnt base G nx cnt d1" by (rule IH [OF s1])
        with e1 have "cnt \<le> t1" by simp
        with Deriv \<open>r = DOrIntroL d1\<close> e1 show ?thesis
          by (simp split: prod.splits)
      next
        case (DOrIntroR d1)
        obtain i1 c1 n1 t1 where e1: "emit base G nx cnt d1 = (i1, c1, n1, t1)"
          by (rule prod_cases4)
        from sz Deriv \<open>r = DOrIntroR d1\<close> have s1: "size d1 \<le> k" by simp
        have "cnt \<le> eCnt base G nx cnt d1" by (rule IH [OF s1])
        with e1 have "cnt \<le> t1" by simp
        with Deriv \<open>r = DOrIntroR d1\<close> e1 show ?thesis
          by (simp split: prod.splits)
      next
        case (DOrElim d0 a1 f1 d1 a2 f2 d2)
        obtain i0 c0 n0 t0 where e0: "emit base G nx cnt d0 = (i0, c0, n0, t0)"
          by (rule prod_cases4)
        obtain b1 cc1 n1 t1
          where e1: "emit base ((a1, n0, f1) # G) (Suc n0) t0 d1 = (b1, cc1, n1, t1)"
          by (rule prod_cases4)
        obtain b1' l1 n1' where cs1: "closeSub n0 (dForm d1) b1 cc1 n1 = (b1', l1, n1')"
          by (rule prod_cases3)
        obtain b2 cc2 n2 t2
          where e2: "emit base ((a2, n1', f2) # G) (Suc n1') t1 d2 = (b2, cc2, n2, t2)"
          by (rule prod_cases4)
        obtain b2' l2 n2' where cs2: "closeSub n1' (dForm d2) b2 cc2 n2 = (b2', l2, n2')"
          by (rule prod_cases3)
        from sz Deriv \<open>r = DOrElim d0 a1 f1 d1 a2 f2 d2\<close>
        have z0: "size d0 \<le> k" and z1: "size d1 \<le> k" and z2: "size d2 \<le> k" by simp_all
        have "cnt \<le> eCnt base G nx cnt d0" by (rule IH [OF z0])
        with e0 have A: "cnt \<le> t0" by simp
        have "t0 \<le> eCnt base ((a1, n0, f1) # G) (Suc n0) t0 d1" by (rule IH [OF z1])
        with e1 A have B: "cnt \<le> t1" by simp
        have "t1 \<le> eCnt base ((a2, n1', f2) # G) (Suc n1') t1 d2" by (rule IH [OF z2])
        with e2 B have "cnt \<le> t2" by simp
        with Deriv \<open>r = DOrElim d0 a1 f1 d1 a2 f2 d2\<close> e0 e1 cs1 e2 cs2 show ?thesis by simp
      next
        case (DIffIntro d1 d2)
        obtain i1 c1 n1 t1 where e1: "emit base G nx cnt d1 = (i1, c1, n1, t1)"
          by (rule prod_cases4)
        obtain i2 c2 n2 t2 where e2: "emit base G n1 t1 d2 = (i2, c2, n2, t2)"
          by (rule prod_cases4)
        from sz Deriv \<open>r = DIffIntro d1 d2\<close> have z1: "size d1 \<le> k"
          and z2: "size d2 \<le> k" by simp_all
        have "cnt \<le> eCnt base G nx cnt d1" by (rule IH [OF z1])
        with e1 have A: "cnt \<le> t1" by simp
        have "t1 \<le> eCnt base G n1 t1 d2" by (rule IH [OF z2])
        with e2 A have "cnt \<le> t2" by simp
        with Deriv \<open>r = DIffIntro d1 d2\<close> e1 e2 show ?thesis by simp
      next
        case (DIffElimL d1)
        obtain i1 c1 n1 t1 where e1: "emit base G nx cnt d1 = (i1, c1, n1, t1)"
          by (rule prod_cases4)
        from sz Deriv \<open>r = DIffElimL d1\<close> have s1: "size d1 \<le> k" by simp
        have "cnt \<le> eCnt base G nx cnt d1" by (rule IH [OF s1])
        with e1 have "cnt \<le> t1" by simp
        with Deriv \<open>r = DIffElimL d1\<close> e1 show ?thesis
          by (simp split: prod.splits)
      next
        case (DIffElimR d1)
        obtain i1 c1 n1 t1 where e1: "emit base G nx cnt d1 = (i1, c1, n1, t1)"
          by (rule prod_cases4)
        from sz Deriv \<open>r = DIffElimR d1\<close> have s1: "size d1 \<le> k" by simp
        have "cnt \<le> eCnt base G nx cnt d1" by (rule IH [OF s1])
        with e1 have "cnt \<le> t1" by simp
        with Deriv \<open>r = DIffElimR d1\<close> e1 show ?thesis
          by (simp split: prod.splits)
      next
        case (DForallElim d1)
        obtain i1 c1 n1 t1 where e1: "emit base G nx cnt d1 = (i1, c1, n1, t1)"
          by (rule prod_cases4)
        from sz Deriv \<open>r = DForallElim d1\<close> have s1: "size d1 \<le> k" by simp
        have "cnt \<le> eCnt base G nx cnt d1" by (rule IH [OF s1])
        with e1 have "cnt \<le> t1" by simp
        with Deriv \<open>r = DForallElim d1\<close> e1 show ?thesis
          by (simp split: prod.splits)
      next
        case (DForallIntro d1)
        obtain i1 c1 n1 t1
          where e1: "emit base G nx (uniCnt cnt G phi d1) (uniD base cnt G phi d1)
                       = (i1, c1, n1, t1)"
          by (rule prod_cases4)
        from sz Deriv \<open>r = DForallIntro d1\<close>
        have s1: "size (uniD base cnt G phi d1) \<le> k" by (simp add: size_uniD)
        have "uniCnt cnt G phi d1
                \<le> eCnt base G nx (uniCnt cnt G phi d1) (uniD base cnt G phi d1)"
          by (rule IH [OF s1])
        with e1 have "uniCnt cnt G phi d1 \<le> t1" by simp
        moreover have "cnt \<le> uniCnt cnt G phi d1"
          by (simp add: uniCnt_def split: option.splits)
        ultimately have "cnt \<le> t1" by simp
        with Deriv \<open>r = DForallIntro d1\<close> e1 show ?thesis by simp
      next
        case (DExistsIntro d1)
        obtain i1 c1 n1 t1 where e1: "emit base G nx cnt d1 = (i1, c1, n1, t1)"
          by (rule prod_cases4)
        from sz Deriv \<open>r = DExistsIntro d1\<close> have s1: "size d1 \<le> k" by simp
        have "cnt \<le> eCnt base G nx cnt d1" by (rule IH [OF s1])
        with e1 have "cnt \<le> t1" by simp
        with Deriv \<open>r = DExistsIntro d1\<close> e1 show ?thesis
          by (simp split: prod.splits)
      next
        case (DExistsElim d0 a f d1)
        obtain i0 c0 n0 t0 where e0: "emit base G nx cnt d0 = (i0, c0, n0, t0)"
          by (rule prod_cases4)
        obtain b1 cc1 n1 t1
          where e1: "emit base ((a, n0, exF base t0 G (dForm d0) f phi a d0 d1) # G) (Suc n0)
                       (exCnt t0 G (dForm d0) f phi a d0 d1)
                       (exD base t0 G (dForm d0) f phi a d0 d1) = (b1, cc1, n1, t1)"
          by (rule prod_cases4)
        obtain b1' l1 n2 where cs: "closeSub n0 phi b1 cc1 n1 = (b1', l1, n2)"
          by (rule prod_cases3)
        from sz Deriv \<open>r = DExistsElim d0 a f d1\<close>
        have z0: "size d0 \<le> k"
          and z1: "size (exD base t0 G (dForm d0) f phi a d0 d1) \<le> k" by (simp_all add: size_exD)
        have "cnt \<le> eCnt base G nx cnt d0" by (rule IH [OF z0])
        with e0 have A: "cnt \<le> t0" by simp
        have "exCnt t0 G (dForm d0) f phi a d0 d1
                \<le> eCnt base ((a, n0, exF base t0 G (dForm d0) f phi a d0 d1) # G) (Suc n0)
                      (exCnt t0 G (dForm d0) f phi a d0 d1)
                      (exD base t0 G (dForm d0) f phi a d0 d1)"
          by (rule IH [OF z1])
        with e1 have "exCnt t0 G (dForm d0) f phi a d0 d1 \<le> t1" by simp
        moreover have "t0 \<le> exCnt t0 G (dForm d0) f phi a d0 d1"
          by (simp add: exCnt_def split: option.splits)
        ultimately have "cnt \<le> t1" using A by simp
        with Deriv \<open>r = DExistsElim d0 a f d1\<close> e0 e1 cs show ?thesis by (simp add: Let_def)
      next
        case DEqIntro
        with Deriv show ?thesis by simp
      next
        case (DEqElim d1 d2)
        obtain i1 c1 n1 t1 where e1: "emit base G nx cnt d1 = (i1, c1, n1, t1)"
          by (rule prod_cases4)
        obtain i2 c2 n2 t2 where e2: "emit base G n1 t1 d2 = (i2, c2, n2, t2)"
          by (rule prod_cases4)
        from sz Deriv \<open>r = DEqElim d1 d2\<close> have z1: "size d1 \<le> k"
          and z2: "size d2 \<le> k" by simp_all
        have "cnt \<le> eCnt base G nx cnt d1" by (rule IH [OF z1])
        with e1 have A: "cnt \<le> t1" by simp
        have "t1 \<le> eCnt base G n1 t1 d2" by (rule IH [OF z2])
        with e2 A have "cnt \<le> t2" by simp
        with Deriv \<open>r = DEqElim d1 d2\<close> e1 e2 show ?thesis by simp
      next
        case (DReit d1)
        obtain i1 c1 n1 t1 where e1: "emit base G nx cnt d1 = (i1, c1, n1, t1)"
          by (rule prod_cases4)
        from sz Deriv \<open>r = DReit d1\<close> have s1: "size d1 \<le> k" by simp
        have "cnt \<le> eCnt base G nx cnt d1" by (rule IH [OF s1])
        with e1 have "cnt \<le> t1" by simp
        with Deriv \<open>r = DReit d1\<close> e1 show ?thesis by simp
      qed
    qed
  qed
qed

lemma emit_cnt: "cnt \<le> eCnt base G nx cnt d"
  using emit_cnt_k [of "size d"] by blast


section \<open>The side conditions transfer\<close>

text \<open>Section 6.2: of the twenty-one rules, exactly the two that read the
  assumption list can fail to transfer, because Fitch offers the assumptions in
  scope where Lemmon offered the assumptions depended on, and scope is the
  larger.  This section is the claim that the repair of Section 5.4 closes that
  gap --- for both rules, since on this rule set existential elimination reads
  the assumptions too.

  The environment holds exactly the formulas Fitch has in scope, so what has to
  be shown is that the eigenvariable --- after repair, if a repair was called
  for --- occurs in none of them.  When no repair was called for that is what
  @{const uniRepair} decided; when one was, the name used is longer than every
  name in the environment, which is what @{term "base + cnt"} is for.\<close>

definition envNames :: "env \<Rightarrow> nm list" where
  "envNames G = concat (map names (envFms G))"

definition envNamesBelow :: "nat \<Rightarrow> nat \<Rightarrow> env \<Rightarrow> bool" where
  "envNamesBelow base cnt G \<longleftrightarrow> maxlen (envNames G) < base + cnt"

lemma envNamesBelow_fresh:
  assumes "envNamesBelow base cnt G"
  shows "arbitrary_in (freshIdx base cnt) (envFms G)"
  unfolding arbitrary_in_def
proof
  fix g assume g: "g \<in> set (envFms G)"
  show "\<not> occurs (freshIdx base cnt) g"
  proof
    assume "occurs (freshIdx base cnt) g"
    with g have "freshIdx base cnt \<in> set (envNames G)" by (auto simp: envNames_def)
    then have "nlen (freshIdx base cnt) \<le> maxlen (envNames G)" by (rule maxlen_ge)
    with assms show False by (simp add: envNamesBelow_def)
  qed
qed

subsection \<open>Universal introduction\<close>

theorem uniD_genOK:
  assumes ok: "derivOK (Deriv (Uni x p) (DForallIntro d1))"
      and nb: "namesBelow base cnt (Deriv (Uni x p) (DForallIntro d1))"
      and en: "envNamesBelow base cnt G"
  shows "genOK x p (dForm (uniD base cnt G (Uni x p) d1)) (envFms G)"
proof (cases "x \<in> set (fvs p)")
  case False
  then have "eigenOf x p d1 = None" by (simp add: eigenOf_def instWitnesses_def)
  then have "uniD base cnt G (Uni x p) d1 = d1" by (simp add: uniD_def uniRepair_def)
  moreover from ok have "genOK x p (dForm d1) (openFms d1)" by simp
  ultimately show ?thesis using False by (simp add: genOK_def)
next
  case True
  show ?thesis
  proof (cases "uniRepair G (Uni x p) d1")
    case None
    text \<open>No repair: either the Lemmon side condition never licensed a name at
      all --- impossible, since the derivation is correct --- or the name it
      licensed already avoids the environment.\<close>
    from ok True have "eigenOf x p d1 \<noteq> None" by (simp add: genOK_eigenOf)
    then obtain a where eig: "eigenOf x p d1 = Some a" by auto
    with None have arbG: "arbitrary_in a (envFms G)"
      by (auto simp: uniRepair_def split: if_splits)
    from eigenOf_Some [OF eig] have inst: "inst x a p = dForm d1" and nap: "\<not> occurs a p"
      by auto
    from instWitnesses_complete [OF True inst]
    have "a \<in> set (instWitnesses x p (dForm d1))" .
    with nap arbG True None show ?thesis by (auto simp: genOK_def uniD_def)
  next
    case (Some a)
    text \<open>A repair: the name is replaced by one longer than every name in the
      derivation and every name in the environment.\<close>
    let ?b = "freshIdx base cnt"
    from uniRepair_Some [OF Some] have eig: "eigenOf x p d1 = Some a" by auto
    from eigenOf_Some [OF eig] have inst: "inst x a p = dForm d1" and nap: "\<not> occurs a p"
      by auto
    from namesBelow_fresh [OF nb] have "?b \<notin> set (namesD (Deriv (Uni x p) (DForallIntro d1)))" .
    then have nbp: "\<not> occurs ?b p" by simp
    have rp: "rn a ?b p = p" using nap by simp
    have "rn a ?b (inst x a p) = inst x ?b (rn a ?b p)" by (simp add: rn_inst)
    with inst rp have iw: "inst x ?b p = rn a ?b (dForm d1)" by simp
    from instWitnesses_complete [OF True iw]
    have w: "?b \<in> set (instWitnesses x p (rn a ?b (dForm d1)))" .
    have dd: "dForm (uniD base cnt G (Uni x p) d1) = rn a ?b (dForm d1)"
      using Some by (simp add: uniD_def)
    from envNamesBelow_fresh [OF en] have "arbitrary_in ?b (envFms G)" .
    with w nbp True dd show ?thesis by (auto simp: genOK_def)
  qed
qed

subsection \<open>Existential elimination\<close>

lemma witnessOf_complete:
  assumes "witOK x p psi phi As" and "ex = Exi x p" and "x \<in> set (fvs p)"
  shows "witnessOf ex psi phi As \<noteq> None"
proof -
  from assms(1,3) obtain b where "b \<in> set (instWitnesses x p psi)"
    and "\<not> occurs b p" and "\<not> occurs b phi" and "arbitrary_in b As"
    by (auto simp: witOK_def)
  then have "filter (\<lambda>b. \<not> occurs b p \<and> \<not> occurs b phi \<and> arbitrary_in b As)
                    (instWitnesses x p psi) \<noteq> []"
    by (auto simp: filter_empty_conv)
  with assms(2) show ?thesis by (auto simp: witnessOf_def split: list.splits)
qed

theorem exD_witOK:
  assumes ok: "derivOK (Deriv phi (DExistsElim d0 a f d1))"
      and dd: "dForm d0 = Exi x p"
      and nb: "namesBelow base cnt (Deriv phi (DExistsElim d0 a f d1))"
      and en: "envNamesBelow base cnt G"
  shows "witOK x p (exF base cnt G (dForm d0) f phi a d0 d1) phi (envFms G)"
proof -
  let ?As0 = "openFms d0 @ map snd (drop_label a (openAsms d1))"
  from ok dd have w0: "witOK x p f phi ?As0" by simp
  show ?thesis
  proof (cases "x \<in> set (fvs p)")
    case False
    then have "instWitnesses x p f = []" by (simp add: instWitnesses_def)
    with dd have "witnessOf (dForm d0) f phi ?As0 = None" by (simp add: witnessOf_def)
    then have "exF base cnt G (dForm d0) f phi a d0 d1 = f"
      by (simp add: exF_def exRepair_def)
    with w0 False show ?thesis by (simp add: witOK_def)
  next
    case True
    show ?thesis
    proof (cases "exRepair G (dForm d0) f phi a d0 d1")
      case None
      from witnessOf_complete [OF w0 dd True]
      obtain b where wit: "witnessOf (dForm d0) f phi ?As0 = Some b" by auto
      with None have arbG: "arbitrary_in b (envFms G)"
        by (auto simp: exRepair_def split: if_splits)
      from witnessOf_Some [OF wit] dd
      have inst: "inst x b p = f" and nbp: "\<not> occurs b p" and nbphi: "\<not> occurs b phi"
        by auto
      from instWitnesses_complete [OF True inst] have "b \<in> set (instWitnesses x p f)" .
      with nbp nbphi arbG True None show ?thesis by (auto simp: witOK_def exF_def)
    next
      case (Some b)
      let ?b = "freshIdx base cnt"
      from Some have wit: "witnessOf (dForm d0) f phi ?As0 = Some b"
        by (auto simp: exRepair_def split: option.splits if_splits)
      from witnessOf_Some [OF wit] dd
      have inst: "inst x b p = f" and nbp: "\<not> occurs b p" by auto
      from namesBelow_fresh [OF nb]
      have fr: "?b \<notin> set (namesD (Deriv phi (DExistsElim d0 a f d1)))" .
      then have nfphi: "\<not> occurs ?b phi" by simp
      from fr have "?b \<notin> set (namesD d0)" by simp
      with namesD_dForm [of d0] dd have nfp: "\<not> occurs ?b p" by auto
      have rp: "rn b ?b p = p" using nbp by simp
      have "rn b ?b (inst x b p) = inst x ?b (rn b ?b p)" by (simp add: rn_inst)
      with inst rp have iw: "inst x ?b p = rn b ?b f" by simp
      from instWitnesses_complete [OF True iw]
      have w: "?b \<in> set (instWitnesses x p (rn b ?b f))" .
      have ef: "exF base cnt G (dForm d0) f phi a d0 d1 = rn b ?b f"
        using Some by (simp add: exF_def)
      from envNamesBelow_fresh [OF en] have "arbitrary_in ?b (envFms G)" .
      with w nfp nfphi True ef show ?thesis by (auto simp: witOK_def)
    qed
  qed
qed


section \<open>The environment is the scope\<close>

text \<open>The traversal's environment binds the premises and the assumption of every
  subproof it is currently inside.  Those are exactly the lines Definition 19
  puts in scope at the level it is emitting at.  So the assumption list Fitch
  offers a side condition and the list @{const uniRepair} and @{const exRepair}
  consult are the same list --- which is what makes the previous section apply.\<close>

definition envIsScope :: "fitch_proof \<Rightarrow> env \<Rightarrow> nat list \<Rightarrow> bool" where
  "envIsScope F G path \<longleftrightarrow>
     envNums G = set (premiseLines F) \<union> set path \<and>
     (\<forall>e \<in> set G. fmAt (\<delta> F) (fst (snd e)) = Some (snd (snd e)))"

lemma envIsScope_scope:
  assumes wf: "fitchWF F" and eis: "envIsScope F G path"
      and fl: "fl \<in> set (flatten F)" and sc: "flScope fl = path"
  shows "set (depFms (\<delta> F) (scopeOf F (flNum fl))) = set (envFms G)"
proof -
  from scopeOf_flScope [OF wf fl] sc eis
  have S: "scopeOf F (flNum fl) = envNums G" by (simp add: envIsScope_def)

  have "set (envFms G) \<subseteq> set (depFms (\<delta> F) (envNums G))"
  proof
    fix g assume "g \<in> set (envFms G)"
    then obtain e where e: "e \<in> set G" and g: "g = snd (snd e)"
      by (auto simp: envFms_def)
    from e eis have "fmAt (\<delta> F) (fst (snd e)) = Some (snd (snd e))"
      by (simp add: envIsScope_def)
    moreover from e have "fst (snd e) \<in> envNums G" by (force simp: envNums_def)
    ultimately show "g \<in> set (depFms (\<delta> F) (envNums G))"
      using g by (auto intro: depFms_mem)
  qed
  moreover have "set (depFms (\<delta> F) (envNums G)) \<subseteq> set (envFms G)"
  proof
    fix g assume "g \<in> set (depFms (\<delta> F) (envNums G))"
    then obtain l where l: "l \<in> set (\<delta> F)" and n: "lineNumber l \<in> envNums G"
      and g: "g = formula l" by (auto simp: depFms_def)
    from wf have dst: "distinct (map lineNumber (\<delta> F))"
      by (simp add: delta_nums fitchWF_distinct)
    from lookupLine_mem [OF dst l] g have fm: "fmAt (\<delta> F) (lineNumber l) = Some g"
      by (simp add: fmAt_def)
    from n obtain e where e: "e \<in> set G" and en: "fst (snd e) = lineNumber l"
      by (force simp: envNums_def)
    from e eis have "fmAt (\<delta> F) (fst (snd e)) = Some (snd (snd e))"
      by (simp add: envIsScope_def)
    with en fm have "g = snd (snd e)" by simp
    with e show "g \<in> set (envFms G)" by (force simp: envFms_def)
  qed
  ultimately show ?thesis using S by simp
qed

text \<open>Entering a subproof extends both by the same line.\<close>

lemma envIsScope_Cons:
  assumes "envIsScope F G path" and "fmAt (\<delta> F) n = Some fa"
  shows "envIsScope F ((a, n, fa) # G) (path @ [n])"
  using assms by (auto simp: envIsScope_def envNums_def)


section \<open>The obligation at a single emitted line\<close>

definition lineOK :: "fitch_proof \<Rightarrow> fline \<Rightarrow> bool" where
  "lineOK F fl \<longleftrightarrow>
     (flRule fl \<noteq> FAssume \<longrightarrow> flRule fl \<noteq> FPremise \<longrightarrow>
        ruleOK (\<delta> F) (flFm fl) (depFms (\<delta> F) (scopeOf F (flNum fl)))
               (toLemmonRule (flRule fl)))"

lemma lineOK_assume [simp]: "lineOK F (FL n f FAssume p)" "lineOK F (FL n f FPremise p)"
  by (simp_all add: lineOK_def)

text \<open>The interface to the traversal: to discharge a line it emitted, it is
  enough to check the rule against the environment, which is what the traversal
  has.  The environment is the scope, so the check against the scope follows.\<close>

lemma lineOK_I:
  assumes wf: "fitchWF F" and eis: "envIsScope F G path"
      and mem: "FL n phi r path \<in> set (flatten F)"
      and ok: "ruleOK (\<delta> F) phi (envFms G) (toLemmonRule r)"
  shows "lineOK F (FL n phi r path)"
proof -
  from envIsScope_scope [OF wf eis mem] have
    "set (depFms (\<delta> F) (scopeOf F n)) = set (envFms G)" by simp
  then have "set (depFms (\<delta> F) (scopeOf F n)) \<subseteq> set (envFms G)" by simp
  from ruleOK_antitone [OF this ok] show ?thesis by (simp add: lineOK_def)
qed

subsection \<open>Reading a conclusion line off the image\<close>

lemma concl_fmAt:
  assumes wf: "fitchWF F" and eis: "envIsScope F G path"
      and sub: "set (flatItems its path) \<subseteq> set (flatten F)"
      and ec: "emitConcl G its c phi"
  shows "fmAt (\<delta> F) c = Some phi"
proof -
  from ec consider (env) "(c, phi) \<in> set (envNumFms G)"
    | (item) "(c, phi) \<in> set (itemsNumFms its)" by (auto simp: emitConcl_def)
  then show ?thesis
  proof cases
    case env
    then obtain e where e: "e \<in> set G" and "fst (snd e) = c" and "snd (snd e) = phi"
      by (auto simp: envNumFms_def)
    with eis show ?thesis by (auto simp: envIsScope_def)
  next
    case item
    then have "(c, phi) \<in> set (map (\<lambda>fl. (flNum fl, flFm fl)) (flatItems its path))"
      by (simp add: numFm_flatItems)
    then obtain fl where fl: "fl \<in> set (flatItems its path)"
      and n: "flNum fl = c" and f: "flFm fl = phi" by auto
    from fl sub have "fl \<in> set (flatten F)" by blast
    from delta_lookup(1) [OF wf this] n f show ?thesis by simp
  qed
qed

lemma emit_fmAt:
  assumes wf: "fitchWF F" and eis: "envIsScope F G path"
      and em: "envMatches G d"
      and e: "emit base G nx cnt d = (its, c, nx', cnt')"
      and sub: "set (flatItems its path) \<subseteq> set (flatten F)"
  shows "fmAt (\<delta> F) c = Some (dForm d)"
  by (rule concl_fmAt [OF wf eis sub emit_concl_fm [OF em e]])

subsection \<open>Closing a subproof\<close>

lemma flatItems_closeSub:
  "flatItems (fst (closeSub asmLine psi body c nxt)) p
     = flatItems body p @ (if endsAt body asmLine c then [] else [FL nxt psi (FReit c) p])"
  by (simp add: closeSub_def)

lemma closeSub_num:
  "fst (snd (closeSub asmLine psi body c nxt)) = (if endsAt body asmLine c then c else nxt)"
  by (simp add: closeSub_def)

lemma lineOK_reit:
  assumes wf: "fitchWF F" and eis: "envIsScope F G p"
      and mem: "FL nxt psi (FReit c) p \<in> set (flatten F)"
      and fm: "fmAt (\<delta> F) c = Some psi"
  shows "lineOK F (FL nxt psi (FReit c) p)"
  by (rule lineOK_I [OF wf eis mem]) (simp add: fm)

text \<open>Whatever @{const closeSub} returns as the subproof's last line, that line
  carries the subderivation's conclusion: either it is the line the traversal
  already produced, or it is the reiteration of that line.\<close>

lemma closeSub_fmAt:
  assumes fm: "fmAt (\<delta> F) c = Some psi"
      and wf: "fitchWF F"
      and reit: "\<not> endsAt body asmLine c \<Longrightarrow> FL nxt psi (FReit c) p \<in> set (flatten F)"
  shows "fmAt (\<delta> F) (fst (snd (closeSub asmLine psi body c nxt))) = Some psi"
proof (cases "endsAt body asmLine c")
  case True
  with fm show ?thesis by (simp add: closeSub_num)
next
  case False
  from delta_lookup(1) [OF wf reit [OF False]] False show ?thesis by (simp add: closeSub_num)
qed

subsection \<open>Carrying the invariants into a subproof\<close>

lemma boundIn_discharge:
  assumes "fst ` set (drop_label a (openAsms e)) \<subseteq> labels G"
  shows "boundIn ((a, n, fa) # G) e"
  using assms by (auto simp: boundIn_def labels_def)

lemma envMatches_discharge:
  assumes em: "envMatches G d"
      and drop: "set (drop_label a (openAsms e)) \<subseteq> set (openAsms d)"
      and dis: "dischargeOK a fa e"
  shows "envMatches ((a, n, fa) # G) e"
  unfolding envMatches_def
proof
  fix nf assume nf: "nf \<in> set (openAsms e)"
  show "\<exists>g. find (\<lambda>g. fst g = fst nf) ((a, n, fa) # G) = Some g \<and> snd (snd g) = snd nf"
  proof (cases "fst nf = a")
    case True
    with nf dis have "snd nf = fa" by (auto simp: dischargeOK_def)
    with True show ?thesis by auto
  next
    case False
    with nf have "nf \<in> set (drop_label a (openAsms e))" by simp
    with drop have "nf \<in> set (openAsms d)" by blast
    with em obtain g where "find (\<lambda>g. fst g = fst nf) G = Some g" and "snd (snd g) = snd nf"
      by (fastforce simp: envMatches_def)
    with False show ?thesis by auto
  qed
qed

lemma maxlen_less: "\<forall>a \<in> set used. nlen a < k \<Longrightarrow> 0 < k \<Longrightarrow> maxlen used < k"
  by (induction used) (auto simp: maxlen_def)

lemma envNamesBelow_Cons:
  assumes G: "envNamesBelow base cnt G" and fa: "maxlen (names fa) < base + cnt"
  shows "envNamesBelow base cnt ((a, n, fa) # G)"
proof -
  from G have pos: "0 < base + cnt" unfolding envNamesBelow_def by linarith
  have "\<forall>c \<in> set (envNames ((a, n, fa) # G)). nlen c < base + cnt"
  proof
    fix c assume "c \<in> set (envNames ((a, n, fa) # G))"
    then have "c \<in> set (names fa) \<or> c \<in> set (envNames G)"
      by (auto simp: envNames_def envFms_def)
    then show "nlen c < base + cnt"
    proof
      assume "c \<in> set (names fa)"
      then have "nlen c \<le> maxlen (names fa)" by (rule maxlen_ge)
      with fa show ?thesis by simp
    next
      assume "c \<in> set (envNames G)"
      then have "nlen c \<le> maxlen (envNames G)" by (rule maxlen_ge)
      with G show ?thesis by (simp add: envNamesBelow_def)
    qed
  qed
  from maxlen_less [OF this pos] show ?thesis by (simp add: envNamesBelow_def)
qed


section \<open>Packaging a subproof\<close>

lemma maxlen_mono: "set xs \<subseteq> set ys \<Longrightarrow> maxlen xs \<le> maxlen ys"
  by (rule maxlen_le, auto dest: maxlen_ge)

lemma envMatches_mono:
  "envMatches G d \<Longrightarrow> set (openAsms e) \<subseteq> set (openAsms d) \<Longrightarrow> envMatches G e"
  by (auto simp: envMatches_def)

lemma names_rn_sub: "set (names (rn a b p)) \<subseteq> set (names p) \<union> {b}"
  by (auto simp: names_rn)

text \<open>The witness of an existential elimination is required to avoid the
  conclusion, so renaming it leaves the conclusion alone: the subproof still
  ends where the rule says it does.\<close>

lemma dForm_exD:
  assumes "dForm d1 = phi"
  shows "dForm (exD base cnt G ex f phi a d0 d1) = phi"
proof (cases "exRepair G ex f phi a d0 d1")
  case None
  then show ?thesis using assms by (simp add: exD_def)
next
  case (Some b)
  then have "witnessOf ex f phi (openFms d0 @ map snd (drop_label a (openAsms d1))) = Some b"
    by (auto simp: exRepair_def split: option.splits if_splits)
  from witnessOf_Some [OF this] have "\<not> occurs b phi" by blast
  with Some assms show ?thesis by (simp add: exD_def)
qed

text \<open>Everything the traversal emits for one discharge: the assumption heading
  the subproof, the body, and --- when the body does not already end where the
  rule needs it to --- the reiteration @{const closeSub} adds.  The second
  conclusion is the one the discharging line needs: whatever number
  @{const closeSub} reports as the subproof's last line, that line carries the
  subderivation's conclusion.\<close>

lemma lineOK_subproof:
  assumes wf: "fitchWF F"
      and eis: "envIsScope F G' (path @ [n])"
      and body: "\<forall>fl \<in> set (flatItems b1 (path @ [n])). lineOK F fl"
      and psi: "fmAt (\<delta> F) cc = Some psi"
      and subF: "set (flatItems (fst (closeSub n psi b1 cc nxt)) (path @ [n]))
                   \<subseteq> set (flatten F)"
  shows "\<forall>fl \<in> set (flatItems (fst (closeSub n psi b1 cc nxt)) (path @ [n])). lineOK F fl"
    and "fmAt (\<delta> F) (fst (snd (closeSub n psi b1 cc nxt))) = Some psi"
proof -
  have reit: "FL nxt psi (FReit cc) (path @ [n]) \<in> set (flatten F)"
    if ne: "\<not> endsAt b1 n cc"
  proof -
    from ne have "FL nxt psi (FReit cc) (path @ [n])
                    \<in> set (flatItems (fst (closeSub n psi b1 cc nxt)) (path @ [n]))"
      by (simp add: flatItems_closeSub)
    with subF show ?thesis by blast
  qed
  show "\<forall>fl \<in> set (flatItems (fst (closeSub n psi b1 cc nxt)) (path @ [n])). lineOK F fl"
  proof (cases "endsAt b1 n cc")
    case True
    with body show ?thesis by (simp add: flatItems_closeSub)
  next
    case False
    from lineOK_reit [OF wf eis reit [OF False] psi] body False show ?thesis
      by (simp add: flatItems_closeSub)
  qed
  show "fmAt (\<delta> F) (fst (snd (closeSub n psi b1 cc nxt))) = Some psi"
    by (rule closeSub_fmAt [OF psi wf reit])
qed

lemma flatSub_split:
  "flatSub (Subproof n fa body) path = FL n fa FAssume (path @ [n]) # flatItems body (path @ [n])"
  by (simp add: flatItems_def)

section \<open>(L4) for the traversal\<close>

lemma envNamesBelow_mono:
  "envNamesBelow base cnt G \<Longrightarrow> cnt \<le> cnt' \<Longrightarrow> envNamesBelow base cnt' G"
  by (simp add: envNamesBelow_def)

text \<open>The traversal emits, for each node, the lines its subderivations need and
  then one line applying the node's rule.  That line's rule check is read off
  @{const derivOK}: the formulas the rule cites are the conclusions of the
  subderivations, and @{thm [source] emit_fmAt} says the cited lines carry them.
  The two quantifier rules are the two where that is not the end of it, and
  there @{thm [source] uniD_genOK} and @{thm [source] exD_witOK} finish the
  argument.\<close>

lemma emit_rules_k:
  assumes wf: "fitchWF F"
  shows "\<forall>base G nx cnt d path its c nx' cnt'.
     size d \<le> k \<longrightarrow> derivOK d \<longrightarrow> envMatches G d \<longrightarrow>
     namesBelow base cnt d \<longrightarrow> envNamesBelow base cnt G \<longrightarrow> envIsScope F G path \<longrightarrow>
     emit base G nx cnt d = (its, c, nx', cnt') \<longrightarrow>
     set (flatItems its path) \<subseteq> set (flatten F) \<longrightarrow>
     (\<forall>fl \<in> set (flatItems its path). lineOK F fl)"
proof (induction k)
  case 0
  show ?case
  proof (intro allI impI)
    fix base G nx cnt and d :: deriv and path its c nx' cnt'
    assume "size d \<le> 0"
    then show "\<forall>fl \<in> set (flatItems its path). lineOK F fl" by (cases d) simp
  qed
next
  case (Suc k)
  have IH: "\<And>base G nx cnt d path its c nx' cnt'.
      size d \<le> k \<Longrightarrow> derivOK d \<Longrightarrow> envMatches G d \<Longrightarrow>
      namesBelow base cnt d \<Longrightarrow> envNamesBelow base cnt G \<Longrightarrow> envIsScope F G path \<Longrightarrow>
      emit base G nx cnt d = (its, c, nx', cnt') \<Longrightarrow>
      set (flatItems its path) \<subseteq> set (flatten F) \<Longrightarrow>
      \<forall>fl \<in> set (flatItems its path). lineOK F fl"
    using Suc.IH by blast
  show ?case
  proof (intro allI impI)
    fix base G nx cnt and d :: deriv and path its c nx' cnt'
    assume sz: "size d \<le> Suc k" and ok: "derivOK d" and em: "envMatches G d"
       and nb: "namesBelow base cnt d" and en: "envNamesBelow base cnt G"
       and eis: "envIsScope F G path" and e: "emit base G nx cnt d = (its, c, nx', cnt')"
       and subF: "set (flatItems its path) \<subseteq> set (flatten F)"
    show "\<forall>fl \<in> set (flatItems its path). lineOK F fl"
    proof (cases d)
      case (Deriv phi r)
      show ?thesis
      proof (cases r)
        case (DAssume a)
        with Deriv e have "its = []" by simp
        then show ?thesis by (simp add: ball_Un)
      next
        case (DPremise a)
        with Deriv e have "its = []" by simp
        then show ?thesis by (simp add: ball_Un)
      next
        case (DMP d1 d2)
        obtain i1 c1 n1 t1 where e1: "emit base G nx cnt d1 = (i1, c1, n1, t1)"
          by (rule prod_cases4)
        obtain i2 c2 n2 t2 where e2: "emit base G n1 t1 d2 = (i2, c2, n2, t2)"
          by (rule prod_cases4)
        from Deriv \<open>r = DMP d1 d2\<close> e e1 e2
        have its: "its = i1 @ i2 @ [FLine c phi (FMP c1 c2)]"
 by auto
        from sz Deriv \<open>r = DMP d1 d2\<close> have s1: "size d1 \<le> k" and s2: "size d2 \<le> k"
          by simp_all
        from ok Deriv \<open>r = DMP d1 d2\<close> have ok1: "derivOK d1" and ok2: "derivOK d2"
          by simp_all
        from em Deriv \<open>r = DMP d1 d2\<close> have em1: "envMatches G d1" and em2: "envMatches G d2"
          by (simp_all add: envMatches_def)
        have sn1: "set (namesD d1) \<subseteq> set (namesD d)"
          and sn2: "set (namesD d2) \<subseteq> set (namesD d)"
          using Deriv \<open>r = DMP d1 d2\<close> by auto
        from namesBelow_sub [OF nb sn1] have nb1: "namesBelow base cnt d1" .
        from namesBelow_sub [OF nb sn2] have nb2a: "namesBelow base cnt d2" .
        have cle: "cnt \<le> t1" using emit_cnt [of cnt base G nx d1] e1 by simp
        from namesBelow_mono [OF nb2a cle] have nb2: "namesBelow base t1 d2" .
        from envNamesBelow_mono [OF en cle] have en2: "envNamesBelow base t1 G" .
        from subF its have sub1: "set (flatItems i1 path) \<subseteq> set (flatten F)"
          and sub2: "set (flatItems i2 path) \<subseteq> set (flatten F)" by simp_all
        from IH [OF s1 ok1 em1 nb1 en eis e1 sub1]
        have body1: "\<forall>fl \<in> set (flatItems i1 path). lineOK F fl" .
        from IH [OF s2 ok2 em2 nb2 en2 eis e2 sub2]
        have body2: "\<forall>fl \<in> set (flatItems i2 path). lineOK F fl" .
        from emit_fmAt [OF wf eis em1 e1 sub1] have fm1: "fmAt (\<delta> F) c1 = Some (dForm d1)" .
        from emit_fmAt [OF wf eis em2 e2 sub2] have fm2: "fmAt (\<delta> F) c2 = Some (dForm d2)" .
        from subF its have mem: "FL c phi (FMP c1 c2) path \<in> set (flatten F)" by simp
        from ok Deriv \<open>r = DMP d1 d2\<close> fm1 fm2
        have "ruleOK (\<delta> F) phi (envFms G) (toLemmonRule (FMP c1 c2))"
          by (simp split: fm.splits option.splits)
        from lineOK_I [OF wf eis mem this] body1 body2 its show ?thesis by (simp add: ball_Un)
      next
        case (DCP a fa d1)
        obtain b1 cc1 n1 t1
          where e1: "emit base ((a, nx, fa) # G) (Suc nx) cnt d1 = (b1, cc1, n1, t1)"
          by (rule prod_cases4)
        let ?cl = "closeSub nx (dForm d1) b1 cc1 n1"
        from Deriv \<open>r = DCP a fa d1\<close> e e1
        have its: "its = [FSub (Subproof nx fa (fst ?cl)),
                          FLine c phi (FCP (nx, fst (snd ?cl)))]"
          by (auto simp: case_prod_unfold Let_def)
        have flat: "flatItems its path
                      = (FL nx fa FAssume (path @ [nx]) # flatItems (fst ?cl) (path @ [nx]))
                        @ [FL c phi (FCP (nx, fst (snd ?cl))) path]"
          by (simp add: its flatItems_def)
        from subF flat have memA: "FL nx fa FAssume (path @ [nx]) \<in> set (flatten F)" by simp
        from subF flat have memC: "FL c phi (FCP (nx, fst (snd ?cl))) path
                                     \<in> set (flatten F)" by simp
        from subF flat have subCL: "set (flatItems (fst ?cl) (path @ [nx])) \<subseteq> set (flatten F)"
          by simp
        from subCL have subB: "set (flatItems b1 (path @ [nx])) \<subseteq> set (flatten F)"
          by (auto simp: flatItems_closeSub split: if_splits)
        from delta_lookup(1) [OF wf memA] have fmA: "fmAt (\<delta> F) nx = Some fa" by simp
        from delta_isAssumptionLine [OF wf memA] have asl: "isAssumptionLine (\<delta> F) nx" by simp
        from envIsScope_Cons [OF eis fmA] have eis1: "envIsScope F ((a, nx, fa) # G) (path @ [nx])" .
        from sz Deriv \<open>r = DCP a fa d1\<close> have s1: "size d1 \<le> k" by simp
        from ok Deriv \<open>r = DCP a fa d1\<close> have ok1: "derivOK d1" and dis: "dischargeOK a fa d1"
          by simp_all
        have oaS: "set (drop_label a (openAsms d1)) \<subseteq> set (openAsms d)"
          using Deriv \<open>r = DCP a fa d1\<close> by auto
        from envMatches_discharge [OF em oaS dis] have em1: "envMatches ((a, nx, fa) # G) d1" .
        have sn1: "set (namesD d1) \<subseteq> set (namesD d)"
          using Deriv \<open>r = DCP a fa d1\<close> by auto
        from namesBelow_sub [OF nb sn1] have nb1: "namesBelow base cnt d1" .
        have fan: "set (names fa) \<subseteq> set (namesD d)" using Deriv \<open>r = DCP a fa d1\<close> by auto
        from maxlen_mono [OF fan] nb have fam: "maxlen (names fa) < base + cnt"
          by (simp add: namesBelow_def)
        from envNamesBelow_Cons [OF en fam] have en1: "envNamesBelow base cnt ((a, nx, fa) # G)" .
        from IH [OF s1 ok1 em1 nb1 en1 eis1 e1 subB]
        have body: "\<forall>fl \<in> set (flatItems b1 (path @ [nx])). lineOK F fl" .
        from emit_fmAt [OF wf eis1 em1 e1 subB] have fmcc: "fmAt (\<delta> F) cc1 = Some (dForm d1)" .
        from lineOK_subproof(2) [OF wf eis1 body fmcc subCL]
        have fml: "fmAt (\<delta> F) (fst (snd ?cl)) = Some (dForm d1)" .
        from ok Deriv \<open>r = DCP a fa d1\<close> have rl: "phi = Impl fa (dForm d1)" by simp
        from asl fmA fml rl
        have "ruleOK (\<delta> F) phi (envFms G) (toLemmonRule (FCP (nx, fst (snd ?cl))))" by simp
        from lineOK_I [OF wf eis memC this]
             lineOK_subproof(1) [OF wf eis1 body fmcc subCL]
        show ?thesis by (simp add: flat ball_Un)
      next
        case (DRAA a fa d1)
        obtain b1 cc1 n1 t1
          where e1: "emit base ((a, nx, fa) # G) (Suc nx) cnt d1 = (b1, cc1, n1, t1)"
          by (rule prod_cases4)
        let ?cl = "closeSub nx (dForm d1) b1 cc1 n1"
        from Deriv \<open>r = DRAA a fa d1\<close> e e1
        have its: "its = [FSub (Subproof nx fa (fst ?cl)),
                          FLine c phi (FRAA (nx, fst (snd ?cl)))]"
          by (auto simp: case_prod_unfold Let_def)
        have flat: "flatItems its path
                      = (FL nx fa FAssume (path @ [nx]) # flatItems (fst ?cl) (path @ [nx]))
                        @ [FL c phi (FRAA (nx, fst (snd ?cl))) path]"
          by (simp add: its flatItems_def)
        from subF flat have memA: "FL nx fa FAssume (path @ [nx]) \<in> set (flatten F)" by simp
        from subF flat have memC: "FL c phi (FRAA (nx, fst (snd ?cl))) path
                                     \<in> set (flatten F)" by simp
        from subF flat have subCL: "set (flatItems (fst ?cl) (path @ [nx])) \<subseteq> set (flatten F)"
          by simp
        from subCL have subB: "set (flatItems b1 (path @ [nx])) \<subseteq> set (flatten F)"
          by (auto simp: flatItems_closeSub split: if_splits)
        from delta_lookup(1) [OF wf memA] have fmA: "fmAt (\<delta> F) nx = Some fa" by simp
        from delta_isAssumptionLine [OF wf memA] have asl: "isAssumptionLine (\<delta> F) nx" by simp
        from envIsScope_Cons [OF eis fmA] have eis1: "envIsScope F ((a, nx, fa) # G) (path @ [nx])" .
        from sz Deriv \<open>r = DRAA a fa d1\<close> have s1: "size d1 \<le> k" by simp
        from ok Deriv \<open>r = DRAA a fa d1\<close> have ok1: "derivOK d1" and dis: "dischargeOK a fa d1"
          by simp_all
        have oaS: "set (drop_label a (openAsms d1)) \<subseteq> set (openAsms d)"
          using Deriv \<open>r = DRAA a fa d1\<close> by auto
        from envMatches_discharge [OF em oaS dis] have em1: "envMatches ((a, nx, fa) # G) d1" .
        have sn1: "set (namesD d1) \<subseteq> set (namesD d)"
          using Deriv \<open>r = DRAA a fa d1\<close> by auto
        from namesBelow_sub [OF nb sn1] have nb1: "namesBelow base cnt d1" .
        have fan: "set (names fa) \<subseteq> set (namesD d)" using Deriv \<open>r = DRAA a fa d1\<close> by auto
        from maxlen_mono [OF fan] nb have fam: "maxlen (names fa) < base + cnt"
          by (simp add: namesBelow_def)
        from envNamesBelow_Cons [OF en fam] have en1: "envNamesBelow base cnt ((a, nx, fa) # G)" .
        from IH [OF s1 ok1 em1 nb1 en1 eis1 e1 subB]
        have body: "\<forall>fl \<in> set (flatItems b1 (path @ [nx])). lineOK F fl" .
        from emit_fmAt [OF wf eis1 em1 e1 subB] have fmcc: "fmAt (\<delta> F) cc1 = Some (dForm d1)" .
        from lineOK_subproof(2) [OF wf eis1 body fmcc subCL]
        have fml: "fmAt (\<delta> F) (fst (snd ?cl)) = Some (dForm d1)" .
        from ok Deriv \<open>r = DRAA a fa d1\<close> have rl: "phi = Neg fa" and bot: "dForm d1 = Bot"
          by simp_all
        from asl fmA fml rl bot
        have "ruleOK (\<delta> F) phi (envFms G) (toLemmonRule (FRAA (nx, fst (snd ?cl))))" by simp
        from lineOK_I [OF wf eis memC this]
             lineOK_subproof(1) [OF wf eis1 body fmcc subCL]
        show ?thesis by (simp add: flat ball_Un)
      next
        case (DDN d1)
        obtain i1 c1 n1 t1 where e1: "emit base G nx cnt d1 = (i1, c1, n1, t1)"
          by (rule prod_cases4)
        from Deriv \<open>r = DDN d1\<close> e e1
        have its: "its = i1 @ [FLine c phi (FDN c1)]" by auto
        from sz Deriv \<open>r = DDN d1\<close> have s1: "size d1 \<le> k" by simp
        from ok Deriv \<open>r = DDN d1\<close> have ok1: "derivOK d1" by simp
        from em Deriv \<open>r = DDN d1\<close> have em1: "envMatches G d1"
          by (simp add: envMatches_def)
        have sn1: "set (namesD d1) \<subseteq> set (namesD d)"
          using Deriv \<open>r = DDN d1\<close> by auto
        from namesBelow_sub [OF nb sn1] have nb1: "namesBelow base cnt d1" .
        from subF its have sub1: "set (flatItems i1 path) \<subseteq> set (flatten F)" by simp
        from IH [OF s1 ok1 em1 nb1 en eis e1 sub1]
        have body: "\<forall>fl \<in> set (flatItems i1 path). lineOK F fl" .
        from emit_fmAt [OF wf eis em1 e1 sub1] have fm1: "fmAt (\<delta> F) c1 = Some (dForm d1)" .
        from subF its have mem: "FL c phi (FDN c1) path \<in> set (flatten F)" by simp
        from ok Deriv \<open>r = DDN d1\<close> fm1
        have "ruleOK (\<delta> F) phi (envFms G) (toLemmonRule (FDN c1))"
          by (simp split: fm.splits option.splits)
        from lineOK_I [OF wf eis mem this] body its show ?thesis by (simp add: ball_Un)
      next
        case (DBotI d1 d2)
        obtain i1 c1 n1 t1 where e1: "emit base G nx cnt d1 = (i1, c1, n1, t1)"
          by (rule prod_cases4)
        obtain i2 c2 n2 t2 where e2: "emit base G n1 t1 d2 = (i2, c2, n2, t2)"
          by (rule prod_cases4)
        from Deriv \<open>r = DBotI d1 d2\<close> e e1 e2
        have its: "its = i1 @ i2 @ [FLine c phi (FBotI c1 c2)]"
 by auto
        from sz Deriv \<open>r = DBotI d1 d2\<close> have s1: "size d1 \<le> k" and s2: "size d2 \<le> k"
          by simp_all
        from ok Deriv \<open>r = DBotI d1 d2\<close> have ok1: "derivOK d1" and ok2: "derivOK d2"
          by simp_all
        from em Deriv \<open>r = DBotI d1 d2\<close> have em1: "envMatches G d1" and em2: "envMatches G d2"
          by (simp_all add: envMatches_def)
        have sn1: "set (namesD d1) \<subseteq> set (namesD d)"
          and sn2: "set (namesD d2) \<subseteq> set (namesD d)"
          using Deriv \<open>r = DBotI d1 d2\<close> by auto
        from namesBelow_sub [OF nb sn1] have nb1: "namesBelow base cnt d1" .
        from namesBelow_sub [OF nb sn2] have nb2a: "namesBelow base cnt d2" .
        have cle: "cnt \<le> t1" using emit_cnt [of cnt base G nx d1] e1 by simp
        from namesBelow_mono [OF nb2a cle] have nb2: "namesBelow base t1 d2" .
        from envNamesBelow_mono [OF en cle] have en2: "envNamesBelow base t1 G" .
        from subF its have sub1: "set (flatItems i1 path) \<subseteq> set (flatten F)"
          and sub2: "set (flatItems i2 path) \<subseteq> set (flatten F)" by simp_all
        from IH [OF s1 ok1 em1 nb1 en eis e1 sub1]
        have body1: "\<forall>fl \<in> set (flatItems i1 path). lineOK F fl" .
        from IH [OF s2 ok2 em2 nb2 en2 eis e2 sub2]
        have body2: "\<forall>fl \<in> set (flatItems i2 path). lineOK F fl" .
        from emit_fmAt [OF wf eis em1 e1 sub1] have fm1: "fmAt (\<delta> F) c1 = Some (dForm d1)" .
        from emit_fmAt [OF wf eis em2 e2 sub2] have fm2: "fmAt (\<delta> F) c2 = Some (dForm d2)" .
        from subF its have mem: "FL c phi (FBotI c1 c2) path \<in> set (flatten F)" by simp
        from ok Deriv \<open>r = DBotI d1 d2\<close> fm1 fm2
        have "ruleOK (\<delta> F) phi (envFms G) (toLemmonRule (FBotI c1 c2))"
          by (simp split: fm.splits option.splits)
        from lineOK_I [OF wf eis mem this] body1 body2 its show ?thesis by (simp add: ball_Un)
      next
        case (DAndIntro d1 d2)
        obtain i1 c1 n1 t1 where e1: "emit base G nx cnt d1 = (i1, c1, n1, t1)"
          by (rule prod_cases4)
        obtain i2 c2 n2 t2 where e2: "emit base G n1 t1 d2 = (i2, c2, n2, t2)"
          by (rule prod_cases4)
        from Deriv \<open>r = DAndIntro d1 d2\<close> e e1 e2
        have its: "its = i1 @ i2 @ [FLine c phi (FAndIntro c1 c2)]"
 by auto
        from sz Deriv \<open>r = DAndIntro d1 d2\<close> have s1: "size d1 \<le> k" and s2: "size d2 \<le> k"
          by simp_all
        from ok Deriv \<open>r = DAndIntro d1 d2\<close> have ok1: "derivOK d1" and ok2: "derivOK d2"
          by simp_all
        from em Deriv \<open>r = DAndIntro d1 d2\<close> have em1: "envMatches G d1" and em2: "envMatches G d2"
          by (simp_all add: envMatches_def)
        have sn1: "set (namesD d1) \<subseteq> set (namesD d)"
          and sn2: "set (namesD d2) \<subseteq> set (namesD d)"
          using Deriv \<open>r = DAndIntro d1 d2\<close> by auto
        from namesBelow_sub [OF nb sn1] have nb1: "namesBelow base cnt d1" .
        from namesBelow_sub [OF nb sn2] have nb2a: "namesBelow base cnt d2" .
        have cle: "cnt \<le> t1" using emit_cnt [of cnt base G nx d1] e1 by simp
        from namesBelow_mono [OF nb2a cle] have nb2: "namesBelow base t1 d2" .
        from envNamesBelow_mono [OF en cle] have en2: "envNamesBelow base t1 G" .
        from subF its have sub1: "set (flatItems i1 path) \<subseteq> set (flatten F)"
          and sub2: "set (flatItems i2 path) \<subseteq> set (flatten F)" by simp_all
        from IH [OF s1 ok1 em1 nb1 en eis e1 sub1]
        have body1: "\<forall>fl \<in> set (flatItems i1 path). lineOK F fl" .
        from IH [OF s2 ok2 em2 nb2 en2 eis e2 sub2]
        have body2: "\<forall>fl \<in> set (flatItems i2 path). lineOK F fl" .
        from emit_fmAt [OF wf eis em1 e1 sub1] have fm1: "fmAt (\<delta> F) c1 = Some (dForm d1)" .
        from emit_fmAt [OF wf eis em2 e2 sub2] have fm2: "fmAt (\<delta> F) c2 = Some (dForm d2)" .
        from subF its have mem: "FL c phi (FAndIntro c1 c2) path \<in> set (flatten F)" by simp
        from ok Deriv \<open>r = DAndIntro d1 d2\<close> fm1 fm2
        have "ruleOK (\<delta> F) phi (envFms G) (toLemmonRule (FAndIntro c1 c2))"
          by (simp split: fm.splits option.splits)
        from lineOK_I [OF wf eis mem this] body1 body2 its show ?thesis by (simp add: ball_Un)
      next
        case (DAndElimL d1)
        obtain i1 c1 n1 t1 where e1: "emit base G nx cnt d1 = (i1, c1, n1, t1)"
          by (rule prod_cases4)
        from Deriv \<open>r = DAndElimL d1\<close> e e1
        have its: "its = i1 @ [FLine c phi (FAndElimL c1)]"
 by auto
        from sz Deriv \<open>r = DAndElimL d1\<close> have s1: "size d1 \<le> k" by simp
        from ok Deriv \<open>r = DAndElimL d1\<close> have ok1: "derivOK d1" by simp
        from em Deriv \<open>r = DAndElimL d1\<close> have em1: "envMatches G d1"
          by (simp add: envMatches_def)
        have sn1: "set (namesD d1) \<subseteq> set (namesD d)"
          using Deriv \<open>r = DAndElimL d1\<close> by auto
        from namesBelow_sub [OF nb sn1] have nb1: "namesBelow base cnt d1" .
        from subF its have sub1: "set (flatItems i1 path) \<subseteq> set (flatten F)" by simp
        from IH [OF s1 ok1 em1 nb1 en eis e1 sub1]
        have body: "\<forall>fl \<in> set (flatItems i1 path). lineOK F fl" .
        from emit_fmAt [OF wf eis em1 e1 sub1] have fm1: "fmAt (\<delta> F) c1 = Some (dForm d1)" .
        from subF its have mem: "FL c phi (FAndElimL c1) path \<in> set (flatten F)" by simp
        from ok Deriv \<open>r = DAndElimL d1\<close> fm1
        have "ruleOK (\<delta> F) phi (envFms G) (toLemmonRule (FAndElimL c1))"
          by (simp split: fm.splits option.splits)
        from lineOK_I [OF wf eis mem this] body its show ?thesis by (simp add: ball_Un)
      next
        case (DAndElimR d1)
        obtain i1 c1 n1 t1 where e1: "emit base G nx cnt d1 = (i1, c1, n1, t1)"
          by (rule prod_cases4)
        from Deriv \<open>r = DAndElimR d1\<close> e e1
        have its: "its = i1 @ [FLine c phi (FAndElimR c1)]"
 by auto
        from sz Deriv \<open>r = DAndElimR d1\<close> have s1: "size d1 \<le> k" by simp
        from ok Deriv \<open>r = DAndElimR d1\<close> have ok1: "derivOK d1" by simp
        from em Deriv \<open>r = DAndElimR d1\<close> have em1: "envMatches G d1"
          by (simp add: envMatches_def)
        have sn1: "set (namesD d1) \<subseteq> set (namesD d)"
          using Deriv \<open>r = DAndElimR d1\<close> by auto
        from namesBelow_sub [OF nb sn1] have nb1: "namesBelow base cnt d1" .
        from subF its have sub1: "set (flatItems i1 path) \<subseteq> set (flatten F)" by simp
        from IH [OF s1 ok1 em1 nb1 en eis e1 sub1]
        have body: "\<forall>fl \<in> set (flatItems i1 path). lineOK F fl" .
        from emit_fmAt [OF wf eis em1 e1 sub1] have fm1: "fmAt (\<delta> F) c1 = Some (dForm d1)" .
        from subF its have mem: "FL c phi (FAndElimR c1) path \<in> set (flatten F)" by simp
        from ok Deriv \<open>r = DAndElimR d1\<close> fm1
        have "ruleOK (\<delta> F) phi (envFms G) (toLemmonRule (FAndElimR c1))"
          by (simp split: fm.splits option.splits)
        from lineOK_I [OF wf eis mem this] body its show ?thesis by (simp add: ball_Un)
      next
        case (DOrIntroL d1)
        obtain i1 c1 n1 t1 where e1: "emit base G nx cnt d1 = (i1, c1, n1, t1)"
          by (rule prod_cases4)
        from Deriv \<open>r = DOrIntroL d1\<close> e e1
        have its: "its = i1 @ [FLine c phi (FOrIntroL c1)]"
 by auto
        from sz Deriv \<open>r = DOrIntroL d1\<close> have s1: "size d1 \<le> k" by simp
        from ok Deriv \<open>r = DOrIntroL d1\<close> have ok1: "derivOK d1" by simp
        from em Deriv \<open>r = DOrIntroL d1\<close> have em1: "envMatches G d1"
          by (simp add: envMatches_def)
        have sn1: "set (namesD d1) \<subseteq> set (namesD d)"
          using Deriv \<open>r = DOrIntroL d1\<close> by auto
        from namesBelow_sub [OF nb sn1] have nb1: "namesBelow base cnt d1" .
        from subF its have sub1: "set (flatItems i1 path) \<subseteq> set (flatten F)" by simp
        from IH [OF s1 ok1 em1 nb1 en eis e1 sub1]
        have body: "\<forall>fl \<in> set (flatItems i1 path). lineOK F fl" .
        from emit_fmAt [OF wf eis em1 e1 sub1] have fm1: "fmAt (\<delta> F) c1 = Some (dForm d1)" .
        from subF its have mem: "FL c phi (FOrIntroL c1) path \<in> set (flatten F)" by simp
        from ok Deriv \<open>r = DOrIntroL d1\<close> fm1
        have "ruleOK (\<delta> F) phi (envFms G) (toLemmonRule (FOrIntroL c1))"
          by (simp split: fm.splits option.splits)
        from lineOK_I [OF wf eis mem this] body its show ?thesis by (simp add: ball_Un)
      next
        case (DOrIntroR d1)
        obtain i1 c1 n1 t1 where e1: "emit base G nx cnt d1 = (i1, c1, n1, t1)"
          by (rule prod_cases4)
        from Deriv \<open>r = DOrIntroR d1\<close> e e1
        have its: "its = i1 @ [FLine c phi (FOrIntroR c1)]"
 by auto
        from sz Deriv \<open>r = DOrIntroR d1\<close> have s1: "size d1 \<le> k" by simp
        from ok Deriv \<open>r = DOrIntroR d1\<close> have ok1: "derivOK d1" by simp
        from em Deriv \<open>r = DOrIntroR d1\<close> have em1: "envMatches G d1"
          by (simp add: envMatches_def)
        have sn1: "set (namesD d1) \<subseteq> set (namesD d)"
          using Deriv \<open>r = DOrIntroR d1\<close> by auto
        from namesBelow_sub [OF nb sn1] have nb1: "namesBelow base cnt d1" .
        from subF its have sub1: "set (flatItems i1 path) \<subseteq> set (flatten F)" by simp
        from IH [OF s1 ok1 em1 nb1 en eis e1 sub1]
        have body: "\<forall>fl \<in> set (flatItems i1 path). lineOK F fl" .
        from emit_fmAt [OF wf eis em1 e1 sub1] have fm1: "fmAt (\<delta> F) c1 = Some (dForm d1)" .
        from subF its have mem: "FL c phi (FOrIntroR c1) path \<in> set (flatten F)" by simp
        from ok Deriv \<open>r = DOrIntroR d1\<close> fm1
        have "ruleOK (\<delta> F) phi (envFms G) (toLemmonRule (FOrIntroR c1))"
          by (simp split: fm.splits option.splits)
        from lineOK_I [OF wf eis mem this] body its show ?thesis by (simp add: ball_Un)
      next
        case (DOrElim d0 a1 f1 d1 a2 f2 d2)
        obtain i0 c0 n0 t0 where e0: "emit base G nx cnt d0 = (i0, c0, n0, t0)"
          by (rule prod_cases4)
        obtain b1 cc1 n1 t1
          where e1: "emit base ((a1, n0, f1) # G) (Suc n0) t0 d1 = (b1, cc1, n1, t1)"
          by (rule prod_cases4)
        let ?cl1 = "closeSub n0 (dForm d1) b1 cc1 n1"
        obtain b2 cc2 n2 t2
          where e2: "emit base ((a2, snd (snd ?cl1), f2) # G) (Suc (snd (snd ?cl1))) t1 d2
                       = (b2, cc2, n2, t2)"
          by (rule prod_cases4)
        let ?cl2 = "closeSub (snd (snd ?cl1)) (dForm d2) b2 cc2 n2"
        from Deriv \<open>r = DOrElim d0 a1 f1 d1 a2 f2 d2\<close> e e0 e1 e2
        have its: "its = i0 @ [FSub (Subproof n0 f1 (fst ?cl1)),
                               FSub (Subproof (snd (snd ?cl1)) f2 (fst ?cl2)),
                               FLine c phi
                                 (FOrElim c0 (n0, fst (snd ?cl1))
                                    (snd (snd ?cl1), fst (snd ?cl2)))]"
          by (auto simp: case_prod_unfold Let_def)
        have flat: "flatItems its path
                      = flatItems i0 path
                        @ (FL n0 f1 FAssume (path @ [n0]) # flatItems (fst ?cl1) (path @ [n0]))
                        @ (FL (snd (snd ?cl1)) f2 FAssume (path @ [snd (snd ?cl1)])
                             # flatItems (fst ?cl2) (path @ [snd (snd ?cl1)]))
                        @ [FL c phi
                             (FOrElim c0 (n0, fst (snd ?cl1))
                                (snd (snd ?cl1), fst (snd ?cl2))) path]"
          by (simp add: its flatItems_def)
        from subF flat have sub0: "set (flatItems i0 path) \<subseteq> set (flatten F)"
          and memA1: "FL n0 f1 FAssume (path @ [n0]) \<in> set (flatten F)"
          and subCL1: "set (flatItems (fst ?cl1) (path @ [n0])) \<subseteq> set (flatten F)"
          and memA2: "FL (snd (snd ?cl1)) f2 FAssume (path @ [snd (snd ?cl1)])
                        \<in> set (flatten F)"
          and subCL2: "set (flatItems (fst ?cl2) (path @ [snd (snd ?cl1)])) \<subseteq> set (flatten F)"
          and memC: "FL c phi
                       (FOrElim c0 (n0, fst (snd ?cl1)) (snd (snd ?cl1), fst (snd ?cl2))) path
                       \<in> set (flatten F)" by simp_all
        from subCL1 have subB1: "set (flatItems b1 (path @ [n0])) \<subseteq> set (flatten F)"
          by (auto simp: flatItems_closeSub split: if_splits)
        from subCL2 have subB2: "set (flatItems b2 (path @ [snd (snd ?cl1)])) \<subseteq> set (flatten F)"
          by (auto simp: flatItems_closeSub split: if_splits)
        from delta_lookup(1) [OF wf memA1] have fmA1: "fmAt (\<delta> F) n0 = Some f1" by simp
        from delta_lookup(1) [OF wf memA2]
        have fmA2: "fmAt (\<delta> F) (snd (snd ?cl1)) = Some f2" by simp
        from delta_isAssumptionLine [OF wf memA1] have asl1: "isAssumptionLine (\<delta> F) n0" by simp
        from delta_isAssumptionLine [OF wf memA2]
        have asl2: "isAssumptionLine (\<delta> F) (snd (snd ?cl1))" by simp
        from envIsScope_Cons [OF eis fmA1] have eis1: "envIsScope F ((a1, n0, f1) # G) (path @ [n0])" .
        from envIsScope_Cons [OF eis fmA2]
        have eis2: "envIsScope F ((a2, snd (snd ?cl1), f2) # G) (path @ [snd (snd ?cl1)])" .
        from sz Deriv \<open>r = DOrElim d0 a1 f1 d1 a2 f2 d2\<close>
        have s0: "size d0 \<le> k" and s1: "size d1 \<le> k" and s2: "size d2 \<le> k" by simp_all
        from ok Deriv \<open>r = DOrElim d0 a1 f1 d1 a2 f2 d2\<close>
        have ok0: "derivOK d0" and ok1: "derivOK d1" and ok2: "derivOK d2"
          and rd0: "dForm d0 = Disj f1 f2" and rd1: "dForm d1 = phi" and rd2: "dForm d2 = phi"
          and dis1: "dischargeOK a1 f1 d1" and dis2: "dischargeOK a2 f2 d2" by simp_all
        from em Deriv \<open>r = DOrElim d0 a1 f1 d1 a2 f2 d2\<close>
        have em0: "envMatches G d0" by (simp add: envMatches_def)
        have oa1: "set (drop_label a1 (openAsms d1)) \<subseteq> set (openAsms d)"
          using Deriv \<open>r = DOrElim d0 a1 f1 d1 a2 f2 d2\<close> by auto
        have oa2: "set (drop_label a2 (openAsms d2)) \<subseteq> set (openAsms d)"
          using Deriv \<open>r = DOrElim d0 a1 f1 d1 a2 f2 d2\<close> by auto
        from envMatches_discharge [OF em oa1 dis1] have em1: "envMatches ((a1, n0, f1) # G) d1" .
        from envMatches_discharge [OF em oa2 dis2]
        have em2: "envMatches ((a2, snd (snd ?cl1), f2) # G) d2" .
        have sn0: "set (namesD d0) \<subseteq> set (namesD d)"
          and sn1: "set (namesD d1) \<subseteq> set (namesD d)"
          and sn2: "set (namesD d2) \<subseteq> set (namesD d)"
          and fn1: "set (names f1) \<subseteq> set (namesD d)"
          and fn2: "set (names f2) \<subseteq> set (namesD d)"
          using Deriv \<open>r = DOrElim d0 a1 f1 d1 a2 f2 d2\<close> by auto
        from namesBelow_sub [OF nb sn0] have nb0: "namesBelow base cnt d0" .
        have c0le: "cnt \<le> t0" using emit_cnt [of cnt base G nx d0] e0 by simp
        have c1le: "t0 \<le> t1"
          using emit_cnt [of t0 base "(a1, n0, f1) # G" "Suc n0" d1] e1 by simp
        from namesBelow_mono [OF namesBelow_sub [OF nb sn1] c0le]
        have nb1: "namesBelow base t0 d1" .
        from namesBelow_mono [OF namesBelow_sub [OF nb sn2] order_trans [OF c0le c1le]]
        have nb2: "namesBelow base t1 d2" .
        from maxlen_mono [OF fn1] nb have fam1: "maxlen (names f1) < base + t0"
          using c0le by (simp add: namesBelow_def)
        from maxlen_mono [OF fn2] nb have fam2: "maxlen (names f2) < base + t1"
          using c0le c1le by (simp add: namesBelow_def)
        from envNamesBelow_Cons [OF envNamesBelow_mono [OF en c0le] fam1]
        have en1: "envNamesBelow base t0 ((a1, n0, f1) # G)" .
        from envNamesBelow_Cons [OF envNamesBelow_mono [OF en order_trans [OF c0le c1le]] fam2]
        have en2: "envNamesBelow base t1 ((a2, snd (snd ?cl1), f2) # G)" .
        from IH [OF s0 ok0 em0 nb0 en eis e0 sub0]
        have body0: "\<forall>fl \<in> set (flatItems i0 path). lineOK F fl" .
        from IH [OF s1 ok1 em1 nb1 en1 eis1 e1 subB1]
        have body1: "\<forall>fl \<in> set (flatItems b1 (path @ [n0])). lineOK F fl" .
        from IH [OF s2 ok2 em2 nb2 en2 eis2 e2 subB2]
        have body2: "\<forall>fl \<in> set (flatItems b2 (path @ [snd (snd ?cl1)])). lineOK F fl" .
        from emit_fmAt [OF wf eis em0 e0 sub0] rd0
        have fm0: "fmAt (\<delta> F) c0 = Some (Disj f1 f2)" by simp
        from emit_fmAt [OF wf eis1 em1 e1 subB1] have fmcc1: "fmAt (\<delta> F) cc1 = Some (dForm d1)" .
        from emit_fmAt [OF wf eis2 em2 e2 subB2] have fmcc2: "fmAt (\<delta> F) cc2 = Some (dForm d2)" .
        from lineOK_subproof(2) [OF wf eis1 body1 fmcc1 subCL1] rd1
        have fml1: "fmAt (\<delta> F) (fst (snd ?cl1)) = Some phi" by simp
        from lineOK_subproof(2) [OF wf eis2 body2 fmcc2 subCL2] rd2
        have fml2: "fmAt (\<delta> F) (fst (snd ?cl2)) = Some phi" by simp
        from asl1 asl2 fmA1 fmA2 fm0 fml1 fml2
        have "ruleOK (\<delta> F) phi (envFms G)
                (toLemmonRule (FOrElim c0 (n0, fst (snd ?cl1))
                                 (snd (snd ?cl1), fst (snd ?cl2))))" by simp
        from lineOK_I [OF wf eis memC this] body0
             lineOK_subproof(1) [OF wf eis1 body1 fmcc1 subCL1]
             lineOK_subproof(1) [OF wf eis2 body2 fmcc2 subCL2]
        show ?thesis by (simp add: flat ball_Un)
      next
        case (DIffIntro d1 d2)
        obtain i1 c1 n1 t1 where e1: "emit base G nx cnt d1 = (i1, c1, n1, t1)"
          by (rule prod_cases4)
        obtain i2 c2 n2 t2 where e2: "emit base G n1 t1 d2 = (i2, c2, n2, t2)"
          by (rule prod_cases4)
        from Deriv \<open>r = DIffIntro d1 d2\<close> e e1 e2
        have its: "its = i1 @ i2 @ [FLine c phi (FIffIntro c1 c2)]"
 by auto
        from sz Deriv \<open>r = DIffIntro d1 d2\<close> have s1: "size d1 \<le> k" and s2: "size d2 \<le> k"
          by simp_all
        from ok Deriv \<open>r = DIffIntro d1 d2\<close> have ok1: "derivOK d1" and ok2: "derivOK d2"
          by simp_all
        from em Deriv \<open>r = DIffIntro d1 d2\<close> have em1: "envMatches G d1" and em2: "envMatches G d2"
          by (simp_all add: envMatches_def)
        have sn1: "set (namesD d1) \<subseteq> set (namesD d)"
          and sn2: "set (namesD d2) \<subseteq> set (namesD d)"
          using Deriv \<open>r = DIffIntro d1 d2\<close> by auto
        from namesBelow_sub [OF nb sn1] have nb1: "namesBelow base cnt d1" .
        from namesBelow_sub [OF nb sn2] have nb2a: "namesBelow base cnt d2" .
        have cle: "cnt \<le> t1" using emit_cnt [of cnt base G nx d1] e1 by simp
        from namesBelow_mono [OF nb2a cle] have nb2: "namesBelow base t1 d2" .
        from envNamesBelow_mono [OF en cle] have en2: "envNamesBelow base t1 G" .
        from subF its have sub1: "set (flatItems i1 path) \<subseteq> set (flatten F)"
          and sub2: "set (flatItems i2 path) \<subseteq> set (flatten F)" by simp_all
        from IH [OF s1 ok1 em1 nb1 en eis e1 sub1]
        have body1: "\<forall>fl \<in> set (flatItems i1 path). lineOK F fl" .
        from IH [OF s2 ok2 em2 nb2 en2 eis e2 sub2]
        have body2: "\<forall>fl \<in> set (flatItems i2 path). lineOK F fl" .
        from emit_fmAt [OF wf eis em1 e1 sub1] have fm1: "fmAt (\<delta> F) c1 = Some (dForm d1)" .
        from emit_fmAt [OF wf eis em2 e2 sub2] have fm2: "fmAt (\<delta> F) c2 = Some (dForm d2)" .
        from subF its have mem: "FL c phi (FIffIntro c1 c2) path \<in> set (flatten F)" by simp
        from ok Deriv \<open>r = DIffIntro d1 d2\<close> fm1 fm2
        have "ruleOK (\<delta> F) phi (envFms G) (toLemmonRule (FIffIntro c1 c2))"
          by (simp split: fm.splits option.splits)
        from lineOK_I [OF wf eis mem this] body1 body2 its show ?thesis by (simp add: ball_Un)
      next
        case (DIffElimL d1)
        obtain i1 c1 n1 t1 where e1: "emit base G nx cnt d1 = (i1, c1, n1, t1)"
          by (rule prod_cases4)
        from Deriv \<open>r = DIffElimL d1\<close> e e1
        have its: "its = i1 @ [FLine c phi (FIffElimL c1)]"
 by auto
        from sz Deriv \<open>r = DIffElimL d1\<close> have s1: "size d1 \<le> k" by simp
        from ok Deriv \<open>r = DIffElimL d1\<close> have ok1: "derivOK d1" by simp
        from em Deriv \<open>r = DIffElimL d1\<close> have em1: "envMatches G d1"
          by (simp add: envMatches_def)
        have sn1: "set (namesD d1) \<subseteq> set (namesD d)"
          using Deriv \<open>r = DIffElimL d1\<close> by auto
        from namesBelow_sub [OF nb sn1] have nb1: "namesBelow base cnt d1" .
        from subF its have sub1: "set (flatItems i1 path) \<subseteq> set (flatten F)" by simp
        from IH [OF s1 ok1 em1 nb1 en eis e1 sub1]
        have body: "\<forall>fl \<in> set (flatItems i1 path). lineOK F fl" .
        from emit_fmAt [OF wf eis em1 e1 sub1] have fm1: "fmAt (\<delta> F) c1 = Some (dForm d1)" .
        from subF its have mem: "FL c phi (FIffElimL c1) path \<in> set (flatten F)" by simp
        from ok Deriv \<open>r = DIffElimL d1\<close> fm1
        have "ruleOK (\<delta> F) phi (envFms G) (toLemmonRule (FIffElimL c1))"
          by (simp split: fm.splits option.splits)
        from lineOK_I [OF wf eis mem this] body its show ?thesis by (simp add: ball_Un)
      next
        case (DIffElimR d1)
        obtain i1 c1 n1 t1 where e1: "emit base G nx cnt d1 = (i1, c1, n1, t1)"
          by (rule prod_cases4)
        from Deriv \<open>r = DIffElimR d1\<close> e e1
        have its: "its = i1 @ [FLine c phi (FIffElimR c1)]"
 by auto
        from sz Deriv \<open>r = DIffElimR d1\<close> have s1: "size d1 \<le> k" by simp
        from ok Deriv \<open>r = DIffElimR d1\<close> have ok1: "derivOK d1" by simp
        from em Deriv \<open>r = DIffElimR d1\<close> have em1: "envMatches G d1"
          by (simp add: envMatches_def)
        have sn1: "set (namesD d1) \<subseteq> set (namesD d)"
          using Deriv \<open>r = DIffElimR d1\<close> by auto
        from namesBelow_sub [OF nb sn1] have nb1: "namesBelow base cnt d1" .
        from subF its have sub1: "set (flatItems i1 path) \<subseteq> set (flatten F)" by simp
        from IH [OF s1 ok1 em1 nb1 en eis e1 sub1]
        have body: "\<forall>fl \<in> set (flatItems i1 path). lineOK F fl" .
        from emit_fmAt [OF wf eis em1 e1 sub1] have fm1: "fmAt (\<delta> F) c1 = Some (dForm d1)" .
        from subF its have mem: "FL c phi (FIffElimR c1) path \<in> set (flatten F)" by simp
        from ok Deriv \<open>r = DIffElimR d1\<close> fm1
        have "ruleOK (\<delta> F) phi (envFms G) (toLemmonRule (FIffElimR c1))"
          by (simp split: fm.splits option.splits)
        from lineOK_I [OF wf eis mem this] body its show ?thesis by (simp add: ball_Un)
      next
        case (DForallElim d1)
        obtain i1 c1 n1 t1 where e1: "emit base G nx cnt d1 = (i1, c1, n1, t1)"
          by (rule prod_cases4)
        from Deriv \<open>r = DForallElim d1\<close> e e1
        have its: "its = i1 @ [FLine c phi (FForallElim c1)]"
 by auto
        from sz Deriv \<open>r = DForallElim d1\<close> have s1: "size d1 \<le> k" by simp
        from ok Deriv \<open>r = DForallElim d1\<close> have ok1: "derivOK d1" by simp
        from em Deriv \<open>r = DForallElim d1\<close> have em1: "envMatches G d1"
          by (simp add: envMatches_def)
        have sn1: "set (namesD d1) \<subseteq> set (namesD d)"
          using Deriv \<open>r = DForallElim d1\<close> by auto
        from namesBelow_sub [OF nb sn1] have nb1: "namesBelow base cnt d1" .
        from subF its have sub1: "set (flatItems i1 path) \<subseteq> set (flatten F)" by simp
        from IH [OF s1 ok1 em1 nb1 en eis e1 sub1]
        have body: "\<forall>fl \<in> set (flatItems i1 path). lineOK F fl" .
        from emit_fmAt [OF wf eis em1 e1 sub1] have fm1: "fmAt (\<delta> F) c1 = Some (dForm d1)" .
        from subF its have mem: "FL c phi (FForallElim c1) path \<in> set (flatten F)" by simp
        from ok Deriv \<open>r = DForallElim d1\<close> fm1
        have "ruleOK (\<delta> F) phi (envFms G) (toLemmonRule (FForallElim c1))"
          by (simp split: fm.splits option.splits)
        from lineOK_I [OF wf eis mem this] body its show ?thesis by (simp add: ball_Un)
      next
        case (DForallIntro d1)
        let ?d1 = "uniD base cnt G phi d1"
        let ?c1 = "uniCnt cnt G phi d1"
        obtain i1 c1 n1 t1 where e1: "emit base G nx ?c1 ?d1 = (i1, c1, n1, t1)"
          by (rule prod_cases4)
        from Deriv \<open>r = DForallIntro d1\<close> e e1
        have its: "its = i1 @ [FLine c phi (FForallIntro c1)]"
 by auto
        from sz Deriv \<open>r = DForallIntro d1\<close> have s1: "size ?d1 \<le> k" by (simp add: size_uniD)
        from ok Deriv \<open>r = DForallIntro d1\<close> have ok1: "derivOK d1" by simp
        have sn1: "set (namesD d1) \<subseteq> set (namesD d)"
          using Deriv \<open>r = DForallIntro d1\<close> by auto
        from namesBelow_sub [OF nb sn1] have nb1: "namesBelow base cnt d1" .
        from derivOK_uniD [OF ok1 nb1] have okr: "derivOK ?d1" .
        from em Deriv \<open>r = DForallIntro d1\<close> have "envMatches G d1" by (simp add: envMatches_def)
        then have em1: "envMatches G ?d1" by (simp add: envMatches_def)
        from namesBelow_uniD [OF nb1] have nbr: "namesBelow base ?c1 ?d1" .
        have cle: "cnt \<le> ?c1" by (simp add: uniCnt_def split: option.splits)
        from envNamesBelow_mono [OF en cle] have enr: "envNamesBelow base ?c1 G" .
        from subF its have sub1: "set (flatItems i1 path) \<subseteq> set (flatten F)" by simp
        from IH [OF s1 okr em1 nbr enr eis e1 sub1]
        have body: "\<forall>fl \<in> set (flatItems i1 path). lineOK F fl" .
        from emit_fmAt [OF wf eis em1 e1 sub1] have fm1: "fmAt (\<delta> F) c1 = Some (dForm ?d1)" .
        from subF its have mem: "FL c phi (FForallIntro c1) path \<in> set (flatten F)" by simp
        from ok Deriv \<open>r = DForallIntro d1\<close> obtain x p where fp: "phi = Uni x p"
          by (cases phi) auto
        from ok Deriv \<open>r = DForallIntro d1\<close> fp nb en
        have "genOK x p (dForm (uniD base cnt G (Uni x p) d1)) (envFms G)"
          by (intro uniD_genOK) simp_all
        with fp fm1 have "ruleOK (\<delta> F) phi (envFms G) (toLemmonRule (FForallIntro c1))"
          by simp
        from lineOK_I [OF wf eis mem this] body its show ?thesis by (simp add: ball_Un)
      next
        case (DExistsIntro d1)
        obtain i1 c1 n1 t1 where e1: "emit base G nx cnt d1 = (i1, c1, n1, t1)"
          by (rule prod_cases4)
        from Deriv \<open>r = DExistsIntro d1\<close> e e1
        have its: "its = i1 @ [FLine c phi (FExistsIntro c1)]"
 by auto
        from sz Deriv \<open>r = DExistsIntro d1\<close> have s1: "size d1 \<le> k" by simp
        from ok Deriv \<open>r = DExistsIntro d1\<close> have ok1: "derivOK d1" by simp
        from em Deriv \<open>r = DExistsIntro d1\<close> have em1: "envMatches G d1"
          by (simp add: envMatches_def)
        have sn1: "set (namesD d1) \<subseteq> set (namesD d)"
          using Deriv \<open>r = DExistsIntro d1\<close> by auto
        from namesBelow_sub [OF nb sn1] have nb1: "namesBelow base cnt d1" .
        from subF its have sub1: "set (flatItems i1 path) \<subseteq> set (flatten F)" by simp
        from IH [OF s1 ok1 em1 nb1 en eis e1 sub1]
        have body: "\<forall>fl \<in> set (flatItems i1 path). lineOK F fl" .
        from emit_fmAt [OF wf eis em1 e1 sub1] have fm1: "fmAt (\<delta> F) c1 = Some (dForm d1)" .
        from subF its have mem: "FL c phi (FExistsIntro c1) path \<in> set (flatten F)" by simp
        from ok Deriv \<open>r = DExistsIntro d1\<close> fm1
        have "ruleOK (\<delta> F) phi (envFms G) (toLemmonRule (FExistsIntro c1))"
          by (simp split: fm.splits option.splits)
        from lineOK_I [OF wf eis mem this] body its show ?thesis by (simp add: ball_Un)
      next
        case (DExistsElim d0 a f d1)
        obtain i0 c0 n0 t0 where e0: "emit base G nx cnt d0 = (i0, c0, n0, t0)"
          by (rule prod_cases4)
        let ?f = "exF base t0 G (dForm d0) f phi a d0 d1"
        let ?d1 = "exD base t0 G (dForm d0) f phi a d0 d1"
        let ?c1 = "exCnt t0 G (dForm d0) f phi a d0 d1"
        obtain b1 cc1 n1 t1
          where e1: "emit base ((a, n0, ?f) # G) (Suc n0) ?c1 ?d1 = (b1, cc1, n1, t1)"
          by (rule prod_cases4)
        let ?cl = "closeSub n0 phi b1 cc1 n1"
        from Deriv \<open>r = DExistsElim d0 a f d1\<close> e e0 e1
        have its: "its = i0 @ [FSub (Subproof n0 ?f (fst ?cl)),
                               FLine c phi (FExistsElim c0 (n0, fst (snd ?cl)))]"
          by (auto simp: case_prod_unfold Let_def)
        have flat: "flatItems its path
                      = flatItems i0 path
                        @ (FL n0 ?f FAssume (path @ [n0]) # flatItems (fst ?cl) (path @ [n0]))
                        @ [FL c phi (FExistsElim c0 (n0, fst (snd ?cl))) path]"
          by (simp add: its flatItems_def)
        from subF flat have sub0: "set (flatItems i0 path) \<subseteq> set (flatten F)"
          and memA: "FL n0 ?f FAssume (path @ [n0]) \<in> set (flatten F)"
          and subCL: "set (flatItems (fst ?cl) (path @ [n0])) \<subseteq> set (flatten F)"
          and memC: "FL c phi (FExistsElim c0 (n0, fst (snd ?cl))) path
                       \<in> set (flatten F)" by simp_all
        from subCL have subB: "set (flatItems b1 (path @ [n0])) \<subseteq> set (flatten F)"
          by (auto simp: flatItems_closeSub split: if_splits)
        from delta_lookup(1) [OF wf memA] have fmA: "fmAt (\<delta> F) n0 = Some ?f" by simp
        from delta_isAssumptionLine [OF wf memA] have asl: "isAssumptionLine (\<delta> F) n0" by simp
        from envIsScope_Cons [OF eis fmA] have eis1: "envIsScope F ((a, n0, ?f) # G) (path @ [n0])" .
        from sz Deriv \<open>r = DExistsElim d0 a f d1\<close>
        have s0: "size d0 \<le> k" and s1: "size ?d1 \<le> k" by (simp_all add: size_exD)
        from ok Deriv \<open>r = DExistsElim d0 a f d1\<close>
        have ok0: "derivOK d0" and ok1: "derivOK d1" and rd1: "dForm d1 = phi"
          and dis: "dischargeOK a f d1" by simp_all
        from em Deriv \<open>r = DExistsElim d0 a f d1\<close>
        have em0: "envMatches G d0" by (simp add: envMatches_def)
        have sn0: "set (namesD d0) \<subseteq> set (namesD d)"
          and sn1: "set (namesD d1) \<subseteq> set (namesD d)"
          and fn: "set (names f) \<subseteq> set (namesD d)"
          using Deriv \<open>r = DExistsElim d0 a f d1\<close> by auto
        from namesBelow_sub [OF nb sn0] have nb0: "namesBelow base cnt d0" .
        have c0le: "cnt \<le> t0" using emit_cnt [of cnt base G nx d0] e0 by simp
        from namesBelow_mono [OF namesBelow_sub [OF nb sn1] c0le]
        have nb1: "namesBelow base t0 d1" .
        from derivOK_exD [OF ok1 nb1] have okr: "derivOK ?d1" .
        from namesBelow_exD [OF nb1] have nbr: "namesBelow base ?c1 ?d1" .
        have c1le: "t0 \<le> ?c1" by (simp add: exCnt_def split: option.splits)
        from dischargeOK_exD [OF dis] have disr: "dischargeOK a ?f ?d1" .
        have oaS: "set (drop_label a (openAsms ?d1)) \<subseteq> set (openAsms d)"
        proof (cases "exRepair G (dForm d0) f phi a d0 d1")
          case None
          then show ?thesis using Deriv \<open>r = DExistsElim d0 a f d1\<close> by (auto simp: exD_def)
        next
          case (Some b)
          from openAsms_exD_other [OF Some] show ?thesis
            using Deriv \<open>r = DExistsElim d0 a f d1\<close> by auto
        qed
        from envMatches_discharge [OF em oaS disr] have em1: "envMatches ((a, n0, ?f) # G) ?d1" .
        have fam: "maxlen (names ?f) < base + ?c1"
        proof (cases "exRepair G (dForm d0) f phi a d0 d1")
          case None
          then have "?f = f" and "?c1 = t0" by (simp_all add: exF_def exCnt_def)
          with maxlen_mono [OF fn] nb c0le show ?thesis by (simp add: namesBelow_def)
        next
          case (Some b)
          then have ff: "?f = rn b (freshIdx base t0) f" and cc: "?c1 = Suc t0"
            by (simp_all add: exF_def exCnt_def)
          have "\<forall>cnm \<in> set (names ?f). nlen cnm \<le> base + t0"
          proof
            fix cnm assume "cnm \<in> set (names ?f)"
            with ff names_rn_sub have "cnm \<in> set (names f) \<or> cnm = freshIdx base t0" by auto
            then show "nlen cnm \<le> base + t0"
            proof
              assume "cnm \<in> set (names f)"
              then have "nlen cnm \<le> maxlen (names f)" by (rule maxlen_ge)
              also from maxlen_mono [OF fn] have "\<dots> \<le> maxlen (namesD d)" .
              finally show ?thesis using nb c0le by (simp add: namesBelow_def)
            next
              assume "cnm = freshIdx base t0" then show ?thesis by (simp add: ball_Un)
            qed
          qed
          from maxlen_le [OF this] cc show ?thesis by (simp add: ball_Un)
        qed
        from envNamesBelow_Cons [OF envNamesBelow_mono [OF en order_trans [OF c0le c1le]] fam]
        have en1: "envNamesBelow base ?c1 ((a, n0, ?f) # G)" .
        from IH [OF s0 ok0 em0 nb0 en eis e0 sub0]
        have body0: "\<forall>fl \<in> set (flatItems i0 path). lineOK F fl" .
        from IH [OF s1 okr em1 nbr en1 eis1 e1 subB]
        have body1: "\<forall>fl \<in> set (flatItems b1 (path @ [n0])). lineOK F fl" .
        from emit_fmAt [OF wf eis em0 e0 sub0] have fm0: "fmAt (\<delta> F) c0 = Some (dForm d0)" .
        from emit_fmAt [OF wf eis1 em1 e1 subB] dForm_exD [OF rd1]
        have fmcc: "fmAt (\<delta> F) cc1 = Some phi" by simp
        from lineOK_subproof(2) [OF wf eis1 body1 fmcc subCL]
        have fml: "fmAt (\<delta> F) (fst (snd ?cl)) = Some phi" .
        from ok Deriv \<open>r = DExistsElim d0 a f d1\<close> obtain x p where dd: "dForm d0 = Exi x p"
          by (cases "dForm d0") auto
        from ok Deriv \<open>r = DExistsElim d0 a f d1\<close> dd nb
             envNamesBelow_mono [OF en c0le] namesBelow_mono [OF nb c0le]
        have wo: "witOK x p ?f phi (envFms G)"
          by (intro exD_witOK) simp_all
        from asl fmA fm0 fml dd wo
        have "ruleOK (\<delta> F) phi (envFms G)
                (toLemmonRule (FExistsElim c0 (n0, fst (snd ?cl))))" by simp
        from lineOK_I [OF wf eis memC this] body0
             lineOK_subproof(1) [OF wf eis1 body1 fmcc subCL]
        show ?thesis by (simp add: flat ball_Un)
      next
        case DEqIntro
        from Deriv \<open>r = DEqIntro\<close> e have its: "its = [FLine c phi FEqIntro]"
 by auto
        with subF have mem: "FL c phi FEqIntro path \<in> set (flatten F)" by simp
        from ok Deriv \<open>r = DEqIntro\<close>
        have "ruleOK (\<delta> F) phi (envFms G) (toLemmonRule FEqIntro)" by simp
        from lineOK_I [OF wf eis mem this] its show ?thesis by (simp add: ball_Un)
      next
        case (DEqElim d1 d2)
        obtain i1 c1 n1 t1 where e1: "emit base G nx cnt d1 = (i1, c1, n1, t1)"
          by (rule prod_cases4)
        obtain i2 c2 n2 t2 where e2: "emit base G n1 t1 d2 = (i2, c2, n2, t2)"
          by (rule prod_cases4)
        from Deriv \<open>r = DEqElim d1 d2\<close> e e1 e2
        have its: "its = i1 @ i2 @ [FLine c phi (FEqElim c1 c2)]"
 by auto
        from sz Deriv \<open>r = DEqElim d1 d2\<close> have s1: "size d1 \<le> k" and s2: "size d2 \<le> k"
          by simp_all
        from ok Deriv \<open>r = DEqElim d1 d2\<close> have ok1: "derivOK d1" and ok2: "derivOK d2"
          by simp_all
        from em Deriv \<open>r = DEqElim d1 d2\<close> have em1: "envMatches G d1" and em2: "envMatches G d2"
          by (simp_all add: envMatches_def)
        have sn1: "set (namesD d1) \<subseteq> set (namesD d)"
          and sn2: "set (namesD d2) \<subseteq> set (namesD d)"
          using Deriv \<open>r = DEqElim d1 d2\<close> by auto
        from namesBelow_sub [OF nb sn1] have nb1: "namesBelow base cnt d1" .
        from namesBelow_sub [OF nb sn2] have nb2a: "namesBelow base cnt d2" .
        have cle: "cnt \<le> t1" using emit_cnt [of cnt base G nx d1] e1 by simp
        from namesBelow_mono [OF nb2a cle] have nb2: "namesBelow base t1 d2" .
        from envNamesBelow_mono [OF en cle] have en2: "envNamesBelow base t1 G" .
        from subF its have sub1: "set (flatItems i1 path) \<subseteq> set (flatten F)"
          and sub2: "set (flatItems i2 path) \<subseteq> set (flatten F)" by simp_all
        from IH [OF s1 ok1 em1 nb1 en eis e1 sub1]
        have body1: "\<forall>fl \<in> set (flatItems i1 path). lineOK F fl" .
        from IH [OF s2 ok2 em2 nb2 en2 eis e2 sub2]
        have body2: "\<forall>fl \<in> set (flatItems i2 path). lineOK F fl" .
        from emit_fmAt [OF wf eis em1 e1 sub1] have fm1: "fmAt (\<delta> F) c1 = Some (dForm d1)" .
        from emit_fmAt [OF wf eis em2 e2 sub2] have fm2: "fmAt (\<delta> F) c2 = Some (dForm d2)" .
        from subF its have mem: "FL c phi (FEqElim c1 c2) path \<in> set (flatten F)" by simp
        from ok Deriv \<open>r = DEqElim d1 d2\<close> fm1 fm2
        have "ruleOK (\<delta> F) phi (envFms G) (toLemmonRule (FEqElim c1 c2))"
          by (simp split: fm.splits option.splits trm.splits)
        from lineOK_I [OF wf eis mem this] body1 body2 its show ?thesis by (simp add: ball_Un)
      next
        case (DReit d1)
        obtain i1 c1 n1 t1 where e1: "emit base G nx cnt d1 = (i1, c1, n1, t1)"
          by (rule prod_cases4)
        from Deriv \<open>r = DReit d1\<close> e e1 have its: "its = i1 @ [FLine c phi (FReit c1)]"
 by auto
        from sz Deriv \<open>r = DReit d1\<close> have s1: "size d1 \<le> k" by simp
        from ok Deriv \<open>r = DReit d1\<close> have ok1: "derivOK d1" by simp
        from em Deriv \<open>r = DReit d1\<close> have em1: "envMatches G d1" by (simp add: envMatches_def)
        have sn1: "set (namesD d1) \<subseteq> set (namesD d)" using Deriv \<open>r = DReit d1\<close> by auto
        from namesBelow_sub [OF nb sn1] have nb1: "namesBelow base cnt d1" .
        from subF its have sub1: "set (flatItems i1 path) \<subseteq> set (flatten F)" by simp
        from IH [OF s1 ok1 em1 nb1 en eis e1 sub1]
        have body: "\<forall>fl \<in> set (flatItems i1 path). lineOK F fl" .
        from emit_fmAt [OF wf eis em1 e1 sub1] have fm1: "fmAt (\<delta> F) c1 = Some (dForm d1)" .
        from subF its have mem: "FL c phi (FReit c1) path \<in> set (flatten F)" by simp
        from ok Deriv \<open>r = DReit d1\<close> fm1
        have "ruleOK (\<delta> F) phi (envFms G) (toLemmonRule (FReit c1))" by simp
        from lineOK_I [OF wf eis mem this] body its show ?thesis by (simp add: ball_Un)
      qed
    qed
  qed
qed

lemma emit_rules:
  assumes "fitchWF F" and "derivOK d" and "envMatches G d"
      and "namesBelow base cnt d" and "envNamesBelow base cnt G" and "envIsScope F G path"
      and "emit base G nx cnt d = (its, c, nx', cnt')"
      and "set (flatItems its path) \<subseteq> set (flatten F)"
  shows "\<forall>fl \<in> set (flatItems its path). lineOK F fl"
  using emit_rules_k [OF assms(1), of "size d"] assms by blast


section \<open>(L4)\<close>

text \<open>@{const derivOK} constrains a discharged label through @{const
  dischargeOK}: every leaf an ancestor discharges carries the formula that
  ancestor names.  Nothing constrains an \emph{un}discharged one, and nothing
  needs to until the traversal reads the premise block off @{const openAsms}:
  there two leaves with one label and two formulas would be given one Fitch line
  between them.  Unfolding never produces such a derivation --- the formula at a
  label is the formula the source wrote at that line.\<close>

definition labelsConsistent :: "deriv \<Rightarrow> bool" where
  "labelsConsistent d \<longleftrightarrow>
     (\<forall>nf \<in> set (openAsms d). \<forall>mg \<in> set (openAsms d).
        fst nf = fst mg \<longrightarrow> snd nf = snd mg)"

lemma map_snd_enumerate: "map snd (List.enumerate n xs) = xs"
  by (induction xs arbitrary: n) auto

lemma premEnv_pairs_list:
  "map (\<lambda>e. (fst e, snd (snd e))) (premEnv d) = sort_key fst (remdups (openAsms d))"
  by (simp add: premEnv_def comp_def)

lemma premEnv_image: "(\<lambda>e. (fst e, snd (snd e))) ` set (premEnv d) = set (openAsms d)"
proof -
  have "(\<lambda>e. (fst e, snd (snd e))) ` set (premEnv d)
          = set (map (\<lambda>e. (fst e, snd (snd e))) (premEnv d))" by simp
  also have "\<dots> = set (sort_key fst (remdups (openAsms d)))"
    by (simp only: premEnv_pairs_list)
  also have "\<dots> = set (openAsms d)" by simp
  finally show ?thesis .
qed

lemma envMatches_premEnv:
  assumes lc: "labelsConsistent d"
  shows "envMatches (premEnv d) d"
  unfolding envMatches_def
proof
  fix nf assume nf: "nf \<in> set (openAsms d)"
  then have "nf \<in> (\<lambda>e. (fst e, snd (snd e))) ` set (premEnv d)"
    by (simp add: premEnv_image)
  then have "\<exists>e \<in> set (premEnv d). fst e = fst nf" by force
  then obtain g where g: "find (\<lambda>g. fst g = fst nf) (premEnv d) = Some g"
    by (cases "find (\<lambda>g. fst g = fst nf) (premEnv d)") (auto simp: find_None_iff)
  from find_Some_mem [OF g] have gmem: "g \<in> set (premEnv d)" and ga: "fst g = fst nf" by auto
  from gmem have "(fst g, snd (snd g)) \<in> (\<lambda>e. (fst e, snd (snd e))) ` set (premEnv d)"
    by force
  then have inO: "(fst g, snd (snd g)) \<in> set (openAsms d)" by (simp add: premEnv_image)
  have "snd (snd g) = snd nf"
  proof -
    from lc inO nf
    have "fst (fst g, snd (snd g)) = fst nf \<longrightarrow> snd (fst g, snd (snd g)) = snd nf"
      unfolding labelsConsistent_def by blast
    with ga show ?thesis by simp
  qed
  with g show "\<exists>e. find (\<lambda>g. fst g = fst nf) (premEnv d) = Some e \<and> snd (snd e) = snd nf"
    by blast
qed

text \<open>Everything the traversal needs, at the root.  The environment is the
  premise block; the scope at the outermost level is the premises; the base is
  one longer than every name in the derivation, so the counter starts with a
  fresh name available.\<close>

theorem L4_derivation:
  assumes ok: "derivOK d" and lc: "labelsConsistent d"
  shows "\<forall>fl \<in> set (flatten (derivationToFitch d)). lineOK (derivationToFitch d) fl"
proof -
  let ?G = "premEnv d"
  let ?base = "Suc (maxlen (namesD d))"
  obtain its c nx cnt where e: "emit ?base ?G (Suc (length ?G)) 0 d = (its, c, nx, cnt)"
    by (rule prod_cases4)
  let ?F = "premLines ?G @ its"
  have F: "derivationToFitch d = ?F" by (simp add: derivationToFitch_def e)
  have wf: "fitchWF ?F" using L2_L3 [of d] F by simp
  have flat: "flatten ?F = flatItems (premLines ?G) [] @ flatItems its []"
    by (simp add: flatten_eq)

  from emit_inv [OF boundIn_premEnv [of d], where base = ?base
                 and nx = "Suc (length ?G)" and cnt = 0] e
  have E: "emitInv ?G (Suc (length ?G)) its c nx" by simp
  then have B: "blockInv (Suc (length ?G)) its nx" by (simp add: emitInv_def)
  then have npi: "list_all noPremItem its" by (simp add: blockInv_def)
  have noprem: "\<And>fl. fl \<in> set (flatItems its []) \<Longrightarrow> flRule fl \<noteq> FPremise"
    by (rule noPrem_flatItems [OF npi])

  have prem: "premiseLines ?F = map (\<lambda>e. fst (snd e)) ?G"
  proof -
    have "filter (\<lambda>fl. flRule fl = FPremise) (flatItems its []) = []"
      using noprem by (simp add: filter_empty_conv)
    then show ?thesis unfolding premiseLines_def flat by (simp add: comp_def)
  qed

  have eis: "envIsScope ?F ?G []"
    unfolding envIsScope_def
  proof
    show "envNums ?G = set (premiseLines ?F) \<union> set []"
      by (simp add: prem envNums_def comp_def)
  next
    show "\<forall>ee \<in> set ?G. fmAt (\<delta> ?F) (fst (snd ee)) = Some (snd (snd ee))"
    proof
      fix ee assume "ee \<in> set ?G"
      then have "FL (fst (snd ee)) (snd (snd ee)) FPremise []
                   \<in> set (flatItems (premLines ?G) [])" by force
      with flat have "FL (fst (snd ee)) (snd (snd ee)) FPremise [] \<in> set (flatten ?F)" by simp
      from delta_lookup(1) [OF wf this]
      show "fmAt (\<delta> ?F) (fst (snd ee)) = Some (snd (snd ee))" by simp
    qed
  qed

  have em: "envMatches ?G d" by (rule envMatches_premEnv [OF lc])
  have nbT: "namesBelow ?base 0 d" by (simp add: namesBelow_def)
  have enT: "envNamesBelow ?base 0 ?G"
  proof -
    have "\<forall>cnm \<in> set (envNames ?G). nlen cnm \<le> maxlen (namesD d)"
    proof
      fix cnm assume "cnm \<in> set (envNames ?G)"
      then obtain g where g: "g \<in> set ?G" and cn: "cnm \<in> set (names (snd (snd g)))"
        by (force simp: envNames_def envFms_def)
      from g have "(fst g, snd (snd g))
                     \<in> (\<lambda>e. (fst e, snd (snd e))) ` set (premEnv d)" by force
      then have "(fst g, snd (snd g)) \<in> set (openAsms d)" by (simp add: premEnv_image)
      from openAsms_names [OF this] cn have "cnm \<in> set (namesD d)" by blast
      then show "nlen cnm \<le> maxlen (namesD d)" by (rule maxlen_ge)
    qed
    from maxlen_le [OF this] show ?thesis by (simp add: envNamesBelow_def)
  qed
  have subT: "set (flatItems its []) \<subseteq> set (flatten ?F)" by (simp add: flat)

  from emit_rules [OF wf ok em nbT enT eis e subT]
  have body: "\<forall>fl \<in> set (flatItems its []). lineOK ?F fl" .
  show ?thesis
    unfolding F flat
  proof
    fix fl assume "fl \<in> set (flatItems (premLines ?G) [] @ flatItems its [])"
    then consider (p) "fl \<in> set (flatItems (premLines ?G) [])"
      | (i) "fl \<in> set (flatItems its [])" by auto
    then show "lineOK ?F fl"
    proof cases
      case p
      then show ?thesis by auto
    next
      case i
      with body show ?thesis by blast
    qed
  qed
qed

end
