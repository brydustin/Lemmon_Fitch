(*  Title:      LF_Positional.thy

    Towards the soundness of the positional translation: that when
    lemmonToFitchDirect returns an image, the image is a well-formed Fitch proof.

    That was not true until the fourth obstruction was added (see
    LF_Conjecture27).  This theory builds the corrected result from the
    structural facts about buildItems, one conjunct of fitchWF at a time.
*)

theory LF_Positional
  imports LF_Span
begin

section \<open>Flattening a list of items\<close>

definition bflat :: "fitch_item list \<Rightarrow> nat list \<Rightarrow> fline list" where
  "bflat its path = concat (map (\<lambda>it. flatItem it path) its)"

lemma bflat_Nil [simp]: "bflat [] path = []"
  by (simp add: bflat_def)

lemma bflat_Cons [simp]: "bflat (it # its) path = flatItem it path @ bflat its path"
  by (simp add: bflat_def)

lemma bflat_append: "bflat (xs @ ys) path = bflat xs path @ bflat ys path"
  by (simp add: bflat_def)

lemma flatten_bflat: "flatten F = bflat F []"
  by (simp add: flatten_def bflat_def)

section \<open>The image has no stray assumption lines\<close>

text \<open>@{const toFitchRule} never produces @{const FAssume}: an assumption of the
  source becomes @{const FPremise}, and the @{const FAssume} lines of the image
  come from the @{const Subproof} constructor instead.  So no \emph{line} of the
  image carries @{const FAssume}, which is the second conjunct of
  @{const fitchWF}.\<close>

lemma toFitchRule_not_FAssume: "toFitchRule j \<noteq> FAssume"
  by (cases j, auto)

lemma buildItems_noAssume: "list_all noAssumeLinesItem (buildItems boxes ls)"
proof (induction boxes ls rule: buildItems.induct)
  case (2 boxes l ls)
  show ?case
  proof (cases "find (\<lambda>ac. fst ac = lineNumber l) boxes")
    case None
    with 2(1) show ?thesis by (simp add: toFitchRule_not_FAssume)
  next
    case (Some ac)
    with 2(2) [OF Some] 2(3) [OF Some] show ?thesis by (simp add: list_all_iff)
  qed
qed simp

section \<open>The image keeps the source's line numbers, in order\<close>

lemma buildItems_nums:
  "map flNum (bflat (buildItems boxes ls) path) = map lineNumber ls"
proof -
  have "map (\<lambda>fl. (flNum fl, flFm fl)) (bflat (buildItems boxes ls) path)
          = map (\<lambda>l. (lineNumber l, formula l)) ls"
    unfolding bflat_def by (rule buildItems_positional)
  from arg_cong [where f = "map fst", OF this] show ?thesis by (simp add: comp_def)
qed

lemma buildItems_fms:
  "map flFm (bflat (buildItems boxes ls) path) = map formula ls"
proof -
  have "map (\<lambda>fl. (flNum fl, flFm fl)) (bflat (buildItems boxes ls) path)
          = map (\<lambda>l. (lineNumber l, formula l)) ls"
    unfolding bflat_def by (rule buildItems_positional)
  from arg_cong [where f = "map snd", OF this] show ?thesis by (simp add: comp_def)
qed

text \<open>So the first conjunct of @{const fitchWF} --- that the image's line numbers
  strictly increase --- is exactly the corresponding fact about the source, which
  @{const lemmonCorrect} supplies.\<close>

theorem buildItems_sorted:
  assumes "sorted_wrt (<) (map lineNumber P)"
  shows "sorted_wrt (<) (map flNum (flatten (buildItems boxes P)))"
  using assms by (simp only: flatten_bflat buildItems_nums)

theorem lemmonToFitchDirect_sorted:
  assumes "lemmonToFitchDirect P = Inr F"
  shows "sorted_wrt (<) (map flNum (flatten F))"
proof -
  from assms have "lemmonCorrect P" and F: "F = buildItems (boxesOf P) P"
    by (auto simp: lemmonToFitchDirect_def split: option.splits if_splits)
  then have "sorted_wrt (<) (map lineNumber P)" by (simp only: lemmonCorrect_def)
  with F show ?thesis by (simp only: buildItems_sorted)
qed

theorem lemmonToFitchDirect_noAssume:
  assumes "lemmonToFitchDirect P = Inr F"
  shows "list_all noAssumeLinesItem F"
proof -
  from assms have "F = buildItems (boxesOf P) P"
    by (auto simp: lemmonToFitchDirect_def split: option.splits if_splits)
  then show ?thesis by (simp only: buildItems_noAssume)
qed

section \<open>The scope invariant\<close>

text \<open>The traversal carries a path, and every line it emits is at that path or
  deeper.  This is the frame of the whole scope argument.\<close>

lemma buildItems_path_prefix:
  "fl \<in> set (bflat (buildItems boxes ls) path) \<Longrightarrow> is_prefix path (flScope fl)"
proof (induction boxes ls arbitrary: path rule: buildItems.induct)
  case (2 boxes l ls)
  show ?case
  proof (cases "find (\<lambda>ac. fst ac = lineNumber l) boxes")
    case None
    with 2(4) consider (here) "fl = FL (lineNumber l) (formula l)
                                       (toFitchRule (justification l)) path"
      | (rest) "fl \<in> set (bflat (buildItems boxes ls) path)" by auto
    then show ?thesis
    proof cases
      case here then show ?thesis by simp
    next
      case rest from 2(1) [OF None rest] show ?thesis .
    qed
  next
    case (Some ac)
    let ?a = "lineNumber l"
    let ?body = "buildItems boxes (takeWhile (\<lambda>l'. lineNumber l' \<le> snd ac) ls)"
    from Some 2(4)
    consider (asm) "fl = FL ?a (formula l) FAssume (path @ [?a])"
      | (body) "fl \<in> set (bflat ?body (path @ [?a]))"
      | (rest) "fl \<in> set (bflat (buildItems boxes
                          (dropWhile (\<lambda>l'. lineNumber l' \<le> snd ac) ls)) path)"
      by (auto simp: bflat_def)
    then show ?thesis
    proof cases
      case asm then show ?thesis by simp
    next
      case body
      have "is_prefix path (path @ [?a])" by simp
      moreover from 2(2) [OF Some body] have "is_prefix (path @ [?a]) (flScope fl)" .
      ultimately show ?thesis by (rule is_prefix_trans)
    next
      case rest from 2(3) [OF Some rest] show ?thesis .
    qed
  qed
qed simp

subsection \<open>Small facts the induction needs\<close>

lemma find_Some_mem: "find P xs = Some x \<Longrightarrow> x \<in> set xs \<and> P x"
  by (induction xs) (auto split: if_splits)

lemma buildItems_num_mem:
  assumes "fl \<in> set (bflat (buildItems boxes ls) path)"
  shows "flNum fl \<in> set (map lineNumber ls)"
proof -
  from assms have "flNum fl \<in> set (map flNum (bflat (buildItems boxes ls) path))" by simp
  then show ?thesis by (simp only: buildItems_nums)
qed

lemma sorted_wrt_map_takeWhile:
  "sorted_wrt R (map f xs) \<Longrightarrow> sorted_wrt R (map f (takeWhile P xs))"
proof -
  assume "sorted_wrt R (map f xs)"
  moreover have "map f xs = map f (takeWhile P xs) @ map f (dropWhile P xs)"
    by (metis map_append takeWhile_dropWhile_id)
  ultimately show ?thesis by (simp only: sorted_wrt_append)
qed

lemma sorted_wrt_map_dropWhile:
  "sorted_wrt R (map f xs) \<Longrightarrow> sorted_wrt R (map f (dropWhile P xs))"
proof -
  assume "sorted_wrt R (map f xs)"
  moreover have "map f xs = map f (takeWhile P xs) @ map f (dropWhile P xs)"
    by (metis map_append takeWhile_dropWhile_id)
  ultimately show ?thesis by (simp only: sorted_wrt_append)
qed

subsection \<open>Every scope entry is a box containing the line\<close>

text \<open>The other half of the invariant: a line's scope contains nothing but the
  path it was reached at and the assumption lines of boxes whose interval covers
  its number.  Sortedness of the source is what places the body of a box inside
  that interval --- the lines after the assumption are numbered above it, and
  @{term takeWhile} stops at the closing line.\<close>

lemma buildItems_scope_sub:
  "sorted_wrt (<) (map lineNumber ls) \<Longrightarrow>
   (\<And>ac. ac \<in> set boxes \<Longrightarrow> fst ac \<le> snd ac) \<Longrightarrow>
   fl \<in> set (bflat (buildItems boxes ls) path) \<Longrightarrow>
     set (flScope fl)
       \<subseteq> set path \<union> {a. \<exists>c. (a, c) \<in> set boxes \<and> a \<le> flNum fl \<and> flNum fl \<le> c}"
proof (induction boxes ls arbitrary: path rule: buildItems.induct)
  case (2 boxes l ls)
  have srt: "sorted_wrt (<) (map lineNumber ls)" using 2(4) by simp
  show ?case
  proof (cases "find (\<lambda>ac. fst ac = lineNumber l) boxes")
    case None
    with 2(6) consider (here) "fl = FL (lineNumber l) (formula l)
                                       (toFitchRule (justification l)) path"
      | (rest) "fl \<in> set (bflat (buildItems boxes ls) path)" by auto
    then show ?thesis
    proof cases
      case here then show ?thesis by simp
    next
      case rest from 2(1) [OF None srt 2(5) rest] show ?thesis by blast
    qed
  next
    case (Some ac)
    let ?a = "lineNumber l" and ?c = "snd ac"
    from find_Some_mem [OF Some] have acm: "ac \<in> set boxes" and acf: "fst ac = ?a" by auto
    from 2(5) [OF acm] acf have ale: "?a \<le> ?c" by simp
    have acpair: "(?a, ?c) \<in> set boxes" using acm acf by (metis prod.collapse)
    let ?tw = "takeWhile (\<lambda>l'. lineNumber l' \<le> ?c) ls"
    let ?dw = "dropWhile (\<lambda>l'. lineNumber l' \<le> ?c) ls"
    from Some 2(6)
    consider (asm) "fl = FL ?a (formula l) FAssume (path @ [?a])"
      | (body) "fl \<in> set (bflat (buildItems boxes ?tw) (path @ [?a]))"
      | (rest) "fl \<in> set (bflat (buildItems boxes ?dw) path)"
      by (auto simp: bflat_def)
    then show ?thesis
    proof cases
      case asm
      with acpair ale show ?thesis by auto
    next
      case body
      \<comment> \<open>the emitted line lies inside the box, by sortedness and by @{term takeWhile}\<close>
      from buildItems_num_mem [OF body] have nm: "flNum fl \<in> set (map lineNumber ?tw)" .
      then obtain l' where l': "l' \<in> set ?tw" "lineNumber l' = flNum fl" by auto
      from l'(1) have "l' \<in> set ls" and "lineNumber l' \<le> ?c"
        by (auto dest: set_takeWhileD)
      with l'(2) have upper: "flNum fl \<le> ?c" by simp
      from \<open>l' \<in> set ls\<close> 2(4) l'(2) have lower: "?a \<le> flNum fl" by fastforce
      from 2(2) [OF Some sorted_wrt_map_takeWhile [OF srt] 2(5) body]
      have "set (flScope fl)
              \<subseteq> set (path @ [?a])
                  \<union> {a. \<exists>c. (a, c) \<in> set boxes \<and> a \<le> flNum fl \<and> flNum fl \<le> c}" .
      moreover from acpair lower upper
      have "?a \<in> {a. \<exists>c. (a, c) \<in> set boxes \<and> a \<le> flNum fl \<and> flNum fl \<le> c}" by blast
      ultimately show ?thesis by auto
    next
      case rest
      from 2(3) [OF Some sorted_wrt_map_dropWhile [OF srt] 2(5) rest] show ?thesis by blast
    qed
  qed
qed simp

subsection \<open>Where a premise line of the image comes from\<close>

lemma find_None_mem: "find P xs = None \<Longrightarrow> x \<in> set xs \<Longrightarrow> \<not> P x"
  by (induction xs, auto split: if_splits)

lemma toFitchRule_FPremise: "toFitchRule j = FPremise \<Longrightarrow> j = Assumption"
  by (cases j, auto)

text \<open>A line of the image carrying @{const FPremise} is an assumption of the
  source that no rule discharges: the discharged ones are turned into subproofs,
  and their assumption lines carry @{const FAssume}.\<close>

lemma buildItems_FPremise:
  "fl \<in> set (bflat (buildItems boxes ls) path) \<Longrightarrow> flRule fl = FPremise \<Longrightarrow>
     \<exists>l \<in> set ls. lineNumber l = flNum fl \<and> justification l = Assumption
                  \<and> (\<forall>ac \<in> set boxes. fst ac \<noteq> lineNumber l)"
proof (induction boxes ls arbitrary: path rule: buildItems.induct)
  case (2 boxes l ls)
  show ?case
  proof (cases "find (\<lambda>ac. fst ac = lineNumber l) boxes")
    case None
    with 2(4) consider (here) "fl = FL (lineNumber l) (formula l)
                                       (toFitchRule (justification l)) path"
      | (rest) "fl \<in> set (bflat (buildItems boxes ls) path)" by auto
    then show ?thesis
    proof cases
      case here
      with 2(5) have "toFitchRule (justification l) = FPremise" by simp
      then have "justification l = Assumption" by (rule toFitchRule_FPremise)
      moreover from here have "lineNumber l = flNum fl" by simp
      moreover from None have "\<forall>ac \<in> set boxes. fst ac \<noteq> lineNumber l"
        by (auto dest: find_None_mem)
      ultimately show ?thesis by auto
    next
      case rest from 2(1) [OF None rest 2(5)] show ?thesis by auto
    qed
  next
    case (Some ac)
    let ?a = "lineNumber l" and ?c = "snd ac"
    from Some 2(4)
    consider (asm) "fl = FL ?a (formula l) FAssume (path @ [?a])"
      | (body) "fl \<in> set (bflat (buildItems boxes
                    (takeWhile (\<lambda>l'. lineNumber l' \<le> ?c) ls)) (path @ [?a]))"
      | (rest) "fl \<in> set (bflat (buildItems boxes
                    (dropWhile (\<lambda>l'. lineNumber l' \<le> ?c) ls)) path)"
      by (auto simp: bflat_def)
    then show ?thesis
    proof cases
      case asm with 2(5) show ?thesis by simp
    next
      case body
      from 2(2) [OF Some body 2(5)] show ?thesis by (auto dest: set_takeWhileD)
    next
      case rest
      from 2(3) [OF Some rest 2(5)] obtain l'
        where l': "l' \<in> set (dropWhile (\<lambda>l'. lineNumber l' \<le> ?c) ls)"
                  "lineNumber l' = flNum fl" "justification l' = Assumption"
                  "\<forall>ac \<in> set boxes. fst ac \<noteq> lineNumber l'" by blast
      from l'(1) have "l' \<in> set ls" by (rule set_dropWhileD)
      with l'(2,3,4) show ?thesis by auto
    qed
  qed
qed simp

subsection \<open>Which rule each emitted line carries\<close>

text \<open>Positionally, line for line: a source line that opens a box becomes the
  assumption line of a subproof and carries @{const FAssume}; every other line
  carries the rule @{const toFitchRule} gives it.  This is the rule-level
  companion of @{thm [source] buildItems_positional}.\<close>

definition opensBox :: "(nat \<times> nat) list \<Rightarrow> pline \<Rightarrow> bool" where
  "opensBox boxes l \<longleftrightarrow> (\<exists>ac \<in> set boxes. fst ac = lineNumber l)"

lemma buildItems_rules:
  "map flRule (bflat (buildItems boxes ls) path)
     = map (\<lambda>l. if opensBox boxes l then FAssume else toFitchRule (justification l)) ls"
proof (induction boxes ls arbitrary: path rule: buildItems.induct)
  case (2 boxes l ls)
  let ?f = "\<lambda>l. if opensBox boxes l then FAssume else toFitchRule (justification l)"
  show ?case
  proof (cases "find (\<lambda>ac. fst ac = lineNumber l) boxes")
    case None
    then have nb: "\<not> opensBox boxes l"
      by (auto simp: opensBox_def dest: find_None_mem)
    have "map flRule (bflat (buildItems boxes (l # ls)) path)
            = toFitchRule (justification l) # map flRule (bflat (buildItems boxes ls) path)"
      using None by simp
    also have "\<dots> = toFitchRule (justification l) # map ?f ls"
      using 2(1) [OF None] by simp
    finally show ?thesis using nb by simp
  next
    case (Some ac)
    let ?a = "lineNumber l" and ?c = "snd ac"
    let ?tw = "takeWhile (\<lambda>l'. lineNumber l' \<le> ?c) ls"
    let ?dw = "dropWhile (\<lambda>l'. lineNumber l' \<le> ?c) ls"
    from find_Some_mem [OF Some] have ob: "opensBox boxes l" by (auto simp: opensBox_def)
    have "map flRule (bflat (buildItems boxes (l # ls)) path)
            = FAssume # map flRule (bflat (buildItems boxes ?tw) (path @ [?a]))
                      @ map flRule (bflat (buildItems boxes ?dw) path)"
      using Some by (simp add: bflat_def)
    also have "\<dots> = FAssume # map ?f ?tw @ map ?f ?dw"
      using 2(2) [OF Some] 2(3) [OF Some] by simp
    also have "map ?f ?tw @ map ?f ?dw = map ?f ls"
      by (metis map_append takeWhile_dropWhile_id)
    finally show ?thesis using ob by simp
  qed
qed simp

subsection \<open>Premises of the image come first\<close>

lemma opensBox_dischargedAssumps:
  "opensBox (boxesOf P) l \<longleftrightarrow> lineNumber l \<in> set (dischargedAssumps P)"
  by (force simp: opensBox_def dischargedAssumps_def)

lemma rule_FPremise_iff:
  "((if opensBox (boxesOf P) l then FAssume else toFitchRule (justification l)) = FPremise)
     \<longleftrightarrow> isPremiseLine P l"
  by (auto simp: isPremiseLine_def opensBox_dischargedAssumps toFitchRule_FPremise)

lemma list_all_dropWhile_map:
  "list_all (\<lambda>x. Q (g x)) (dropWhile (\<lambda>x. R (g x)) xs)
     = list_all Q (dropWhile R (map g xs))"
  by (simp add: dropWhile_map list.pred_map comp_def)

lemma premiseOrderError_None:
  assumes "premiseOrderError P = None"
  shows "filter (isPremiseLine P) (dropWhile (isPremiseLine P) P) = []"
  using assms unfolding premiseOrderError_def Let_def by (auto split: list.splits)

theorem lemmonToFitchDirect_premisesFirst:
  assumes A: "lemmonToFitchDirect P = Inr F"
  shows "premisesFirst F"
proof -
  from A have F: "F = buildItems (boxesOf P) P" and po: "premiseOrderError P = None"
    by (auto simp: lemmonToFitchDirect_def split: option.splits if_splits)
  let ?f = "\<lambda>l. if opensBox (boxesOf P) l then FAssume else toFitchRule (justification l)"
  have R: "map flRule (flatten F) = map ?f P"
    using F by (simp add: flatten_bflat buildItems_rules)
  have "premisesFirst F
          = list_all (\<lambda>r. r \<noteq> FPremise)
                     (dropWhile (\<lambda>r. r = FPremise) (map flRule (flatten F)))"
    unfolding premisesFirst_def by (rule list_all_dropWhile_map)
  also have "\<dots> = list_all (\<lambda>r. r \<noteq> FPremise) (dropWhile (\<lambda>r. r = FPremise) (map ?f P))"
    by (simp add: R)
  also have "\<dots> = list_all (\<lambda>l. ?f l \<noteq> FPremise) (dropWhile (\<lambda>l. ?f l = FPremise) P)"
    by (rule list_all_dropWhile_map [symmetric])
  also have "\<dots> = list_all (\<lambda>l. \<not> isPremiseLine P l) (dropWhile (isPremiseLine P) P)"
    by (simp add: rule_FPremise_iff cong: dropWhile_cong)
  finally show ?thesis
    using premiseOrderError_None [OF po] by (simp add: list_all_iff filter_empty_conv)
qed

subsection \<open>Premises of the image stand at the outermost level\<close>

lemma boxPath_empty:
  assumes "boxPath P n = []" and "ac \<in> set (boxesOf P)"
  shows "\<not> (fst ac \<le> n \<and> n \<le> snd ac)"
proof -
  from assms(1) have "length (map fst (filter (\<lambda>ac. fst ac \<le> n \<and> n \<le> snd ac) (boxesOf P))) = 0"
    unfolding boxPath_def by (metis (no_types, lifting) length_0_conv length_sort)
  then have "filter (\<lambda>ac. fst ac \<le> n \<and> n \<le> snd ac) (boxesOf P) = []" by simp
  with assms(2) show ?thesis by (simp add: filter_empty_conv)
qed

lemma premiseError_None:
  assumes "premiseError P = None" and "l \<in> set P"
      and "justification l = Assumption"
      and "lineNumber l \<notin> set (dischargedAssumps P)"
  shows "boxPath P (lineNumber l) = []"
proof -
  from assms(1)
  have "filter (\<lambda>l. justification l = Assumption
                     \<and> lineNumber l \<notin> set (dischargedAssumps P)
                     \<and> boxPath P (lineNumber l) \<noteq> []) P = []"
    unfolding premiseError_def by (auto split: list.splits)
  with assms(2,3,4) show ?thesis by (auto simp: filter_empty_conv)
qed

theorem lemmonToFitchDirect_premise_scope:
  assumes A: "lemmonToFitchDirect P = Inr F"
  shows "list_all (\<lambda>fl. flRule fl = FPremise \<longrightarrow> flScope fl = []) (flatten F)"
proof -
  from A have corr: "lemmonCorrect P" and F: "F = buildItems (boxesOf P) P"
        and pe: "premiseError P = None" and bo: "boxOrderError P = None"
    by (auto simp: lemmonToFitchDirect_def split: option.splits if_splits)
  from corr have srt: "sorted_wrt (<) (map lineNumber P)" by (simp add: lemmonCorrect_def)
  show ?thesis
    unfolding list_all_iff
  proof (intro ballI impI)
    fix fl assume m: "fl \<in> set (flatten F)" and r: "flRule fl = FPremise"
    from m F have m': "fl \<in> set (bflat (buildItems (boxesOf P) P) [])"
      by (simp add: flatten_bflat)
    from buildItems_FPremise [OF m' r] obtain l
      where l: "l \<in> set P" "lineNumber l = flNum fl" "justification l = Assumption"
        and nb: "\<forall>ac \<in> set (boxesOf P). fst ac \<noteq> lineNumber l" by blast
    from nb have "lineNumber l \<notin> set (dischargedAssumps P)"
      by (auto simp: dischargedAssumps_def)
    from premiseError_None [OF pe l(1) l(3) this] have bp: "boxPath P (lineNumber l) = []" .
    have "set (flScope fl) \<subseteq> set []
            \<union> {a. \<exists>c. (a, c) \<in> set (boxesOf P) \<and> a \<le> flNum fl \<and> flNum fl \<le> c}"
      by (rule buildItems_scope_sub [OF srt _ m'])
         (use boxOrderError_None [OF bo] in blast)
    moreover
    have "{a. \<exists>c. (a, c) \<in> set (boxesOf P) \<and> a \<le> flNum fl \<and> flNum fl \<le> c} = {}"
      using boxPath_empty [OF bp] l(2) by fastforce
    ultimately show "flScope fl = []" by simp
  qed
qed

subsection \<open>What the subproof-scope check buys\<close>

text \<open>@{const subScopeError} says that a discharging line stands at exactly the
  level its subproof sits at.  Read as a fact about the source, it is this: for
  every discharge pair a line names, the boxes open at that line are the boxes
  strictly containing the pair.  It is what rules out two boxes closing together
  --- the obstruction of \<open>LF_Conjecture27\<close> --- and it is what
  @{const lastIsLineItem} will need, since a subproof whose last line opened a
  further box would end in a subproof rather than a line.\<close>

lemma subScopeError_None:
  assumes "subScopeError P = None" and "l \<in> set P"
      and "ac \<in> set (dischargePairs (justification l))"
  shows "boxPath P (lineNumber l) = subLevel P ac"
proof -
  from assms(1) have "badSubCitations P = []"
    unfolding subScopeError_def by (auto split: list.splits)
  then have "\<forall>l \<in> set P.
               filter (\<lambda>ac. boxPath P (lineNumber l) \<noteq> subLevel P ac)
                      (dischargePairs (justification l)) = []"
    unfolding badSubCitations_def by simp
  with assms(2,3) show ?thesis by (auto simp: filter_empty_conv)
qed

subsection \<open>What the nesting check buys\<close>

text \<open>@{const nestingError} says no two boxes overlap improperly.  The consequence
  @{const lastIsLineItem} needs is that a box opened inside another closes inside
  it too: a subproof whose body ran off the end of its enclosing box would leave
  that box ending in a subproof rather than in a line.\<close>

lemma nestingError_None:
  assumes "nestingError P = None" and "ac \<in> set (boxesOf P)" and "b \<in> set (boxesOf P)"
  shows "\<not> overlapping ac b"
proof -
  from assms(1)
  have "filter (\<lambda>ac. \<exists>b \<in> set (boxesOf P). overlapping ac b) (boxesOf P) = []"
    unfolding nestingError_def by (auto split: list.splits)
  with assms(2,3) show ?thesis by (auto simp: filter_empty_conv)
qed

lemma box_inside_closes_inside:
  assumes "nestingError P = None"
      and "(a, c) \<in> set (boxesOf P)" and "(a', c') \<in> set (boxesOf P)"
      and "a < a'" and "a' \<le> c"
  shows "c' \<le> c"
  using nestingError_None [OF assms(1) assms(2) assms(3)] assms(4,5)
  unfolding overlapping_def by auto

text \<open>And, read the other way, two boxes are nested or disjoint: if one starts
  inside the other it is contained in it.\<close>

lemma boxes_laminar:
  assumes "nestingError P = None"
      and "(a, c) \<in> set (boxesOf P)" and "(a', c') \<in> set (boxesOf P)"
      and "a \<le> a'" and "a' \<le> c"
  shows "c' \<le> c \<or> a = a'"
proof (cases "a = a'")
  case True then show ?thesis by simp
next
  case False
  with assms(4) have "a < a'" by simp
  from box_inside_closes_inside [OF assms(1,2,3) this assms(5)] show ?thesis by simp
qed

subsection \<open>The last item a block emits\<close>

lemma buildItems_nonempty: "ls \<noteq> [] \<Longrightarrow> buildItems boxes ls \<noteq> []"
  by (cases ls) (auto split: option.splits)

lemma dropWhile_last:
  assumes "dropWhile P xs \<noteq> []"
  shows "last (dropWhile P xs) = last xs"
proof -
  have "xs = takeWhile P xs @ dropWhile P xs" by simp
  with assms show ?thesis by (metis last_appendR)
qed

lemma dropWhile_nonempty:
  assumes "x \<in> set xs" and "\<not> P x"
  shows "dropWhile P xs \<noteq> []"
  using assms by (induction xs) auto

text \<open>If every box opened within a block closes strictly before the block's last
  line, then the block ends in a line, not in a subproof --- the last line is
  reached at the top level of the block and emitted as an @{const FLine}.\<close>

definition boxesClosedIn :: "(nat \<times> nat) list \<Rightarrow> pline list \<Rightarrow> bool" where
  "boxesClosedIn boxes ls \<longleftrightarrow>
     (\<forall>l \<in> set ls. \<forall>ac \<in> set boxes.
        fst ac = lineNumber l \<longrightarrow> snd ac < lineNumber (last ls))"

lemma buildItems_last:
  "ls \<noteq> [] \<Longrightarrow> (\<forall>ac \<in> set boxes. fst ac \<le> snd ac) \<Longrightarrow>
   boxesClosedIn boxes ls \<Longrightarrow>
     \<exists>n f r. last (buildItems boxes ls) = FLine n f r"
proof (induction boxes ls rule: buildItems.induct)
  case (2 boxes l ls)
  show ?case
  proof (cases "find (\<lambda>ac. fst ac = lineNumber l) boxes")
    case None
    show ?thesis
    proof (cases "ls = []")
      case True with None show ?thesis by simp
    next
      case False
      have cl: "boxesClosedIn boxes ls"
        unfolding boxesClosedIn_def
      proof (intro ballI impI)
        fix l' ac assume "l' \<in> set ls" and "ac \<in> set boxes" and "fst ac = lineNumber l'"
        with 2(6) have "snd ac < lineNumber (last (l # ls))"
          unfolding boxesClosedIn_def by auto
        with False show "snd ac < lineNumber (last ls)" by simp
      qed
      from 2(1) [OF None False 2(5) cl] obtain n f r
        where "last (buildItems boxes ls) = FLine n f r" by blast
      moreover from False have "buildItems boxes ls \<noteq> []" by (rule buildItems_nonempty)
      ultimately show ?thesis using None by simp
    qed
  next
    case (Some ac)
    let ?c = "snd ac"
    let ?dw = "dropWhile (\<lambda>l'. lineNumber l' \<le> ?c) ls"
    from find_Some_mem [OF Some] have acm: "ac \<in> set boxes" and acf: "fst ac = lineNumber l"
      by auto
    from 2(5) acm acf have ord: "lineNumber l \<le> ?c" by auto
    from 2(6) acm acf have lt: "?c < lineNumber (last (l # ls))"
      unfolding boxesClosedIn_def by auto
    have nonnil: "ls \<noteq> []"
    proof
      assume "ls = []" then have "last (l # ls) = l" by simp
      with lt ord show False by simp
    qed
    then have lastls: "last (l # ls) = last ls" by simp
    have dwne: "?dw \<noteq> []"
      using dropWhile_nonempty [of "last ls" ls] lt lastls nonnil by simp
    have cl: "boxesClosedIn boxes ?dw"
      unfolding boxesClosedIn_def
    proof (intro ballI impI)
      fix l' b assume m: "l' \<in> set ?dw" and acb: "b \<in> set boxes"
        and f: "fst b = lineNumber l'"
      from m have "l' \<in> set ls" by (rule set_dropWhileD)
      with acb f 2(6) have "snd b < lineNumber (last (l # ls))"
        unfolding boxesClosedIn_def by auto
      then show "snd b < lineNumber (last ?dw)"
        using dropWhile_last [OF dwne] lastls by simp
    qed
    from 2(3) [OF Some dwne 2(5) cl] obtain n f r
      where "last (buildItems boxes ?dw) = FLine n f r" by blast
    moreover from dwne have "buildItems boxes ?dw \<noteq> []" by (rule buildItems_nonempty)
    ultimately show ?thesis using Some by simp
  qed
qed simp

section \<open>Conjunct five: every subproof ends in a line\<close>

text \<open>A Fitch subproof must end in a line rather than in a further subproof:
  the discharging rule cites the subproof's last formula, and a citation reaches
  lines, not boxes.  The image can fail this in only one way --- a box closing
  exactly where the box enclosing it closes, so that the inner subproof is the
  last item of the outer one.

  That cannot happen, and the reason is @{const subScopeError} together with
  @{const boxHeadError}.  Suppose boxes \<open>(a, c)\<close> and \<open>(a', c)\<close> with
  \<open>a < a' \<le> c\<close>.  The line \<open>n\<close> that discharges \<open>a'\<close> comes after \<open>c\<close>, and
  @{const subScopeError} puts \<open>n\<close> at the level of \<open>a'\<close> with \<open>a'\<close> itself removed
  --- a level that still contains \<open>a\<close>.  So some box headed \<open>a\<close> contains \<open>n\<close>; by
  @{const boxHeadError} that box is \<open>(a, c)\<close> itself, whence \<open>n \<le> c\<close>,
  contradicting \<open>c < n\<close>.  This is what the fourth obstruction was for.\<close>

subsection \<open>Reading off a box path\<close>

lemma set_boxPath:
  "set (boxPath P n) = fst ` {ac \<in> set (boxesOf P). fst ac \<le> n \<and> n \<le> snd ac}"
  unfolding boxPath_def by auto

lemma boxPath_memI:
  assumes "(a, c) \<in> set (boxesOf P)" and "a \<le> n" and "n \<le> c"
  shows "a \<in> set (boxPath P n)"
  using assms unfolding set_boxPath by force

lemma boxPath_memD:
  assumes "x \<in> set (boxPath P n)"
  shows "\<exists>c. (x, c) \<in> set (boxesOf P) \<and> x \<le> n \<and> n \<le> c"
proof -
  from assms obtain ac
    where ac: "ac \<in> set (boxesOf P)" "fst ac \<le> n" "n \<le> snd ac" "fst ac = x"
    unfolding set_boxPath by auto
  from ac(1) have "(x, snd ac) \<in> set (boxesOf P)" using ac(4) by (metis prod.collapse)
  with ac(2,3,4) show ?thesis by auto
qed

subsection \<open>Where a box comes from, and when it closes\<close>

lemma boxesOf_source:
  assumes "ac \<in> set (boxesOf P)"
  shows "\<exists>l \<in> set P. ac \<in> set (dischargePairs (justification l))"
  using assms unfolding boxesOf_def by auto

lemma dischargePairs_citedL: "ac \<in> set (dischargePairs j) \<Longrightarrow> fst ac \<in> set (citedLines j)"
  by (cases j) auto

lemma dischargePairs_citedR: "ac \<in> set (dischargePairs j) \<Longrightarrow> snd ac \<in> set (citedLines j)"
  by (cases j) auto

lemma dischargePairs_earlier:
  assumes "lemmonCorrect P" and "l \<in> set P"
      and "ac \<in> set (dischargePairs (justification l))"
  shows "fst ac < lineNumber l" and "snd ac < lineNumber l"
proof -
  from lemmonCorrect_citesDown [OF assms(1)] assms(2)
  have cd: "\<forall>m \<in> set (citedLines (justification l)). m < lineNumber l"
    unfolding citesDown_def by blast
  from cd dischargePairs_citedL [OF assms(3)] show "fst ac < lineNumber l" by blast
  from cd dischargePairs_citedR [OF assms(3)] show "snd ac < lineNumber l" by blast
qed

lemma boxesOf_closes_at_a_line:
  assumes "lemmonCorrect P" and "ac \<in> set (boxesOf P)"
  shows "\<exists>l \<in> set P. lineNumber l = snd ac"
proof -
  from boxesOf_source [OF assms(2)] obtain l0
    where l0: "l0 \<in> set P" "ac \<in> set (dischargePairs (justification l0))" by blast
  from lemmonCorrect_citesDown [OF assms(1)] l0(1) dischargePairs_citedR [OF l0(2)]
  have "lookupLine P (snd ac) \<noteq> None" unfolding citesDown_def by blast
  then obtain l where "lookupLine P (snd ac) = Some l" by auto
  then have "l \<in> set P" and "lineNumber l = snd ac" by (auto dest: lookupLine_Some)
  then show ?thesis by blast
qed

lemma boxesOf_opens_at_a_line:
  assumes "lemmonCorrect P" and "ac \<in> set (boxesOf P)"
  shows "\<exists>l \<in> set P. lineNumber l = fst ac"
proof -
  from boxesOf_source [OF assms(2)] obtain l0
    where l0: "l0 \<in> set P" "ac \<in> set (dischargePairs (justification l0))" by blast
  from lemmonCorrect_citesDown [OF assms(1)] l0(1) dischargePairs_citedL [OF l0(2)]
  have "lookupLine P (fst ac) \<noteq> None" unfolding citesDown_def by blast
  then obtain l where "lookupLine P (fst ac) = Some l" by auto
  then have "l \<in> set P" and "lineNumber l = fst ac" by (auto dest: lookupLine_Some)
  then show ?thesis by blast
qed

subsection \<open>No two boxes close together\<close>

lemma boxes_close_apart:
  assumes corr: "lemmonCorrect P" and bh: "boxHeadError P = None"
      and se: "subScopeError P = None"
      and b1: "(a, c) \<in> set (boxesOf P)" and b2: "(a', c') \<in> set (boxesOf P)"
      and lt: "a < a'" and le: "a' \<le> c" and eq: "c' = c"
  shows False
proof -
  from b2 eq have b2': "(a', c) \<in> set (boxesOf P)" by simp
  from boxesOf_source [OF b2'] obtain l
    where l: "l \<in> set P" "(a', c) \<in> set (dischargePairs (justification l))" by blast
  from dischargePairs_earlier(2) [OF corr l(1) l(2)] have cn: "c < lineNumber l" by simp
  from subScopeError_None [OF se l(1) l(2)]
  have lev: "boxPath P (lineNumber l) = subLevel P (a', c)" .
  from lt have "a \<le> a'" by simp
  from boxPath_memI [OF b1 this le] have "a \<in> set (boxPath P a')" .
  with lt have "a \<in> set (removeAll a' (boxPath P a'))" by simp
  with lev have "a \<in> set (boxPath P (lineNumber l))" by (simp add: subLevel_def)
  from boxPath_memD [OF this] obtain c''
    where c'': "(a, c'') \<in> set (boxesOf P)" "a \<le> lineNumber l" "lineNumber l \<le> c''" by blast
  have "fst (a, c) = fst (a, c'')" by simp
  from boxHeadError_None [OF bh b1 c''(1) this] have "c'' = c" by simp
  with c''(3) cn show False by simp
qed

text \<open>So the boxes of an accepted source are strictly laminar: one that starts
  inside another closes strictly before it.\<close>

definition boxesStrict :: "(nat \<times> nat) list \<Rightarrow> bool" where
  "boxesStrict boxes \<longleftrightarrow>
     (\<forall>b \<in> set boxes. fst b \<le> snd b) \<and>
     (\<forall>b \<in> set boxes. \<forall>b' \<in> set boxes.
        fst b < fst b' \<longrightarrow> fst b' \<le> snd b \<longrightarrow> snd b' < snd b)"

lemma boxesStrict_boxesOf:
  assumes corr: "lemmonCorrect P" and bo: "boxOrderError P = None"
      and bh: "boxHeadError P = None" and ne: "nestingError P = None"
      and se: "subScopeError P = None"
  shows "boxesStrict (boxesOf P)"
  unfolding boxesStrict_def
proof (intro conjI ballI impI)
  fix b assume "b \<in> set (boxesOf P)"
  from boxOrderError_None [OF bo this] show "fst b \<le> snd b" .
next
  fix b b' assume bm: "b \<in> set (boxesOf P)" and bm': "b' \<in> set (boxesOf P)"
    and lt: "fst b < fst b'" and le: "fst b' \<le> snd b"
  have p: "(fst b, snd b) \<in> set (boxesOf P)" using bm by simp
  have p': "(fst b', snd b') \<in> set (boxesOf P)" using bm' by simp
  from box_inside_closes_inside [OF ne p p' lt le] have "snd b' \<le> snd b" .
  moreover have "snd b' \<noteq> snd b"
    using boxes_close_apart [OF corr bh se p p' lt le] by blast
  ultimately show "snd b' < snd b" by simp
qed

subsection \<open>Every box of a block closes inside the block\<close>

text \<open>The second thing the induction needs is that a box opened in a block also
  closes there --- that its closing line is one of the block's lines, not one
  beyond them.\<close>

definition boxesLandIn :: "(nat \<times> nat) list \<Rightarrow> pline list \<Rightarrow> bool" where
  "boxesLandIn boxes ls \<longleftrightarrow>
     (\<forall>l \<in> set ls. \<forall>b \<in> set boxes.
        fst b = lineNumber l \<longrightarrow> (\<exists>l' \<in> set ls. lineNumber l' = snd b))"

lemma boxesLandIn_boxesOf:
  assumes "lemmonCorrect P"
  shows "boxesLandIn (boxesOf P) P"
  unfolding boxesLandIn_def
proof (intro ballI impI)
  fix l b assume "l \<in> set P" and bm: "b \<in> set (boxesOf P)" and "fst b = lineNumber l"
  from boxesOf_closes_at_a_line [OF assms bm] show "\<exists>l' \<in> set P. lineNumber l' = snd b" .
qed

lemma mem_takeWhile_le:
  assumes "sorted_wrt (<) (map lineNumber ls)" and "x \<in> set ls" and "lineNumber x \<le> c"
  shows "x \<in> set (takeWhile (\<lambda>l'. lineNumber l' \<le> c) ls)"
  using assms
proof (induction ls)
  case (Cons y ys)
  show ?case
  proof (cases "lineNumber y \<le> c")
    case True
    show ?thesis
    proof (cases "x = y")
      case True with \<open>lineNumber y \<le> c\<close> show ?thesis by simp
    next
      case False
      with Cons.prems(2) have "x \<in> set ys" by simp
      with Cons.IH Cons.prems(1,3) have "x \<in> set (takeWhile (\<lambda>l'. lineNumber l' \<le> c) ys)"
        by simp
      with True show ?thesis by simp
    qed
  next
    case False
    with Cons.prems show ?thesis by auto
  qed
qed simp

lemma mem_dropWhile_gt:
  assumes "x \<in> set ls" and "\<not> lineNumber x \<le> c"
  shows "x \<in> set (dropWhile (\<lambda>l'. lineNumber l' \<le> c) ls)"
  using assms by (induction ls) auto

lemma dropWhile_le_gt:
  assumes "sorted_wrt (<) (map lineNumber ls)"
      and "x \<in> set (dropWhile (\<lambda>l'. lineNumber l' \<le> c) ls)"
  shows "c < lineNumber x"
  using assms
proof (induction ls)
  case (Cons y ys)
  show ?case
  proof (cases "lineNumber y \<le> c")
    case True with Cons show ?thesis by simp
  next
    case False
    with Cons.prems(2) have "x \<in> set (y # ys)" by simp
    with Cons.prems(1) False show ?thesis by auto
  qed
qed simp

subsection \<open>The exact scope of an emitted line\<close>

text \<open>Every box whose head occurs in the current source block and whose
  interval contains an emitted line contributes its head to that line's scope.
  The equal-head premise is essential: without it @{const buildItems} could
  choose a shorter one of two boxes with the same head and skip the longer one.
  The accepted positional translation gets the premise from
  @{const boxHeadError}.\<close>

lemma buildItems_scope_sup:
  assumes "sorted_wrt (<) (map lineNumber ls)" and "boxesStrict boxes"
      and heads: "\<And>b b'. b \<in> set boxes \<Longrightarrow> b' \<in> set boxes
                        \<Longrightarrow> fst b = fst b' \<Longrightarrow> snd b = snd b'"
      and "fl \<in> set (bflat (buildItems boxes ls) path)"
  shows "{a. \<exists>c l. (a, c) \<in> set boxes \<and> l \<in> set ls
                       \<and> lineNumber l = a
                       \<and> a \<le> flNum fl \<and> flNum fl \<le> c}
           \<subseteq> set (flScope fl)"
using assms
proof (induction boxes ls arbitrary: path rule: buildItems.induct)
  case (2 boxes l ls)
  have srt: "sorted_wrt (<) (map lineNumber ls)" using 2(4) by simp
  have gt: "\<forall>z \<in> set ls. lineNumber l < lineNumber z" using 2(4) by simp
  show ?case
  proof (cases "find (\<lambda>ac. fst ac = lineNumber l) boxes")
    case None
    then have no: "\<forall>b \<in> set boxes. fst b \<noteq> lineNumber l"
      by (auto dest: find_None_mem)
    from None 2(7) consider (here) "fl = FL (lineNumber l) (formula l)
                                      (toFitchRule (justification l)) path"
      | (rest) "fl \<in> set (bflat (buildItems boxes ls) path)" by auto
    then show ?thesis
    proof cases
      case here
      show ?thesis
      proof
        fix a assume "a \<in> {a. \<exists>c l'. (a, c) \<in> set boxes \<and> l' \<in> set (l # ls)
                         \<and> lineNumber l' = a
                         \<and> a \<le> flNum fl \<and> flNum fl \<le> c}"
        then obtain c l' where b: "(a, c) \<in> set boxes" and lm: "l' \<in> set (l # ls)"
          and ln: "lineNumber l' = a" and le: "a \<le> flNum fl" by blast
        from here le ln have "lineNumber l' \<le> lineNumber l" by simp
        with gt lm have "lineNumber l' = lineNumber l" by auto
        with b ln no show "a \<in> set (flScope fl)" by auto
      qed
    next
      case rest
      have sub: "{a. \<exists>c l'. (a, c) \<in> set boxes \<and> l' \<in> set (l # ls)
                         \<and> lineNumber l' = a
                         \<and> a \<le> flNum fl \<and> flNum fl \<le> c}
                   \<subseteq> {a. \<exists>c l'. (a, c) \<in> set boxes \<and> l' \<in> set ls
                         \<and> lineNumber l' = a
                         \<and> a \<le> flNum fl \<and> flNum fl \<le> c}"
        using no by auto
      from 2(1) [OF None srt 2(5) 2(6) rest] sub show ?thesis by blast
    qed
  next
    case (Some ac)
    let ?a = "lineNumber l" and ?c = "snd ac"
    let ?tw = "takeWhile (\<lambda>l'. lineNumber l' \<le> ?c) ls"
    let ?dw = "dropWhile (\<lambda>l'. lineNumber l' \<le> ?c) ls"
    from find_Some_mem [OF Some] have acm: "ac \<in> set boxes" and acf: "fst ac = ?a" by auto
    have acpair: "(?a, ?c) \<in> set boxes" using acm acf by (metis prod.collapse)
    from Some 2(7)
    consider (asm) "fl = FL ?a (formula l) FAssume (path @ [?a])"
      | (body) "fl \<in> set (bflat (buildItems boxes ?tw) (path @ [?a]))"
      | (rest) "fl \<in> set (bflat (buildItems boxes ?dw) path)"
      by (auto simp: bflat_def)
    then show ?thesis
    proof cases
      case asm
      show ?thesis
      proof
        fix x assume "x \<in> {a. \<exists>c l'. (a, c) \<in> set boxes \<and> l' \<in> set (l # ls)
                         \<and> lineNumber l' = a
                         \<and> a \<le> flNum fl \<and> flNum fl \<le> c}"
        then obtain c l' where lm: "l' \<in> set (l # ls)" and ln: "lineNumber l' = x"
          and le: "x \<le> flNum fl" by blast
        from asm le ln have "lineNumber l' \<le> lineNumber l" by simp
        with gt lm have "x = ?a" using ln by auto
        with asm show "x \<in> set (flScope fl)" by simp
      qed
    next
      case body
      from buildItems_num_mem [OF body] obtain z
        where zm: "z \<in> set ?tw" and zn: "lineNumber z = flNum fl" by auto
      from zm have upper: "flNum fl \<le> ?c" using zn by (auto dest: set_takeWhileD)
      have ap: "?a \<in> set (flScope fl)"
        using is_prefix_set [OF buildItems_path_prefix [OF body]] by auto
      show ?thesis
      proof
        fix x assume "x \<in> {a. \<exists>c l'. (a, c) \<in> set boxes \<and> l' \<in> set (l # ls)
                         \<and> lineNumber l' = a
                         \<and> a \<le> flNum fl \<and> flNum fl \<le> c}"
        then obtain c l' where b: "(x, c) \<in> set boxes" and lm: "l' \<in> set (l # ls)"
          and ln: "lineNumber l' = x" and lower: "x \<le> flNum fl"
          and fc: "flNum fl \<le> c" by blast
        show "x \<in> set (flScope fl)"
        proof (cases "l' = l")
          case True with ln ap show ?thesis by simp
        next
          case False
          with lm have lls: "l' \<in> set ls" by simp
          from lower upper ln have "lineNumber l' \<le> ?c" by simp
          from mem_takeWhile_le [OF srt lls this] have ltw: "l' \<in> set ?tw" .
          have xin: "x \<in> {a. \<exists>c l'. (a, c) \<in> set boxes \<and> l' \<in> set ?tw
                         \<and> lineNumber l' = a
                         \<and> a \<le> flNum fl \<and> flNum fl \<le> c}"
            using b ltw ln lower fc by blast
          from 2(2) [OF Some sorted_wrt_map_takeWhile [OF srt] 2(5) 2(6) body]
          show ?thesis using xin by blast
        qed
      qed
    next
      case rest
      from buildItems_num_mem [OF rest] obtain z
        where zm: "z \<in> set ?dw" and zn: "lineNumber z = flNum fl" by auto
      from dropWhile_le_gt [OF srt zm] have after: "?c < flNum fl" using zn by simp
      show ?thesis
      proof
        fix x assume "x \<in> {a. \<exists>c l'. (a, c) \<in> set boxes \<and> l' \<in> set (l # ls)
                         \<and> lineNumber l' = a
                         \<and> a \<le> flNum fl \<and> flNum fl \<le> c}"
        then obtain c l' where b: "(x, c) \<in> set boxes" and lm: "l' \<in> set (l # ls)"
          and ln: "lineNumber l' = x" and lower: "x \<le> flNum fl"
          and fc: "flNum fl \<le> c" by blast
        have nl: "l' \<noteq> l"
        proof
          assume "l' = l"
          with ln have eqh: "fst ac = fst (x, c)" using acf by simp
          from 2(6) [OF acm b eqh] have "?c = c" by simp
          with after fc show False by simp
        qed
        with lm have lls: "l' \<in> set ls" by simp
        have notle: "\<not> lineNumber l' \<le> ?c"
        proof
          assume le: "lineNumber l' \<le> ?c"
          from bspec [OF gt lls] have "?a < lineNumber l'" .
          then have lt: "fst ac < fst (x, c)" using acf ln by simp
          from le ln have xle: "fst (x, c) \<le> snd ac" by simp
          from 2(5) have strict:
            "\<forall>b \<in> set boxes. \<forall>b' \<in> set boxes.
               fst b < fst b' \<longrightarrow> fst b' \<le> snd b \<longrightarrow> snd b' < snd b"
            unfolding boxesStrict_def by simp
          from bspec [OF strict acm] have strict_ac:
            "\<forall>b' \<in> set boxes.
               fst ac < fst b' \<longrightarrow> fst b' \<le> snd ac \<longrightarrow> snd b' < snd ac" .
          from bspec [OF strict_ac b] lt xle have "c < ?c" by simp
          with after fc show False by simp
        qed
        from mem_dropWhile_gt [OF lls notle] have ldw: "l' \<in> set ?dw" .
        have xin: "x \<in> {a. \<exists>c l'. (a, c) \<in> set boxes \<and> l' \<in> set ?dw
                         \<and> lineNumber l' = a
                         \<and> a \<le> flNum fl \<and> flNum fl \<le> c}"
          using b ldw ln lower fc by blast
        from 2(3) [OF Some sorted_wrt_map_dropWhile [OF srt] 2(5) 2(6) rest]
        show "x \<in> set (flScope fl)" using xin by blast
      qed
    qed
  qed
qed simp

lemma buildItems_scope_sorted:
  assumes "sorted_wrt (<) (map lineNumber ls)" and "sorted_wrt (<) path"
      and before: "\<And>x l. x \<in> set path \<Longrightarrow> l \<in> set ls
                          \<Longrightarrow> x < lineNumber l"
      and "fl \<in> set (bflat (buildItems boxes ls) path)"
  shows "sorted_wrt (<) (flScope fl)"
using assms
proof (induction boxes ls arbitrary: path rule: buildItems.induct)
  case (2 boxes l ls)
  have srt: "sorted_wrt (<) (map lineNumber ls)" using 2(4) by simp
  have gt: "\<forall>z \<in> set ls. lineNumber l < lineNumber z" using 2(4) by simp
  show ?case
  proof (cases "find (\<lambda>ac. fst ac = lineNumber l) boxes")
    case None
    with 2(7) consider (here) "fl = FL (lineNumber l) (formula l)
                                      (toFitchRule (justification l)) path"
      | (rest) "fl \<in> set (bflat (buildItems boxes ls) path)" by auto
    then show ?thesis
    proof cases
      case here with 2(5) show ?thesis by simp
    next
      case rest
      from 2(1) [OF None srt 2(5) _ rest] show ?thesis
        using 2(6) by auto
    qed
  next
    case (Some ac)
    let ?a = "lineNumber l" and ?c = "snd ac"
    let ?tw = "takeWhile (\<lambda>l'. lineNumber l' \<le> ?c) ls"
    let ?dw = "dropWhile (\<lambda>l'. lineNumber l' \<le> ?c) ls"
    have ps: "sorted_wrt (<) (path @ [?a])"
      using 2(5,6) by (auto simp: sorted_wrt_append)
    from Some 2(7)
    consider (asm) "fl = FL ?a (formula l) FAssume (path @ [?a])"
      | (body) "fl \<in> set (bflat (buildItems boxes ?tw) (path @ [?a]))"
      | (rest) "fl \<in> set (bflat (buildItems boxes ?dw) path)"
      by (auto simp: bflat_def)
    then show ?thesis
    proof cases
      case asm with ps show ?thesis by simp
    next
      case body
      have bef: "\<And>x z. x \<in> set (path @ [?a]) \<Longrightarrow> z \<in> set ?tw
                              \<Longrightarrow> x < lineNumber z"
      proof -
        fix x z assume xp: "x \<in> set (path @ [?a])" and zm: "z \<in> set ?tw"
        from zm have zls: "z \<in> set ls" by (auto dest: set_takeWhileD)
        from xp consider (old) "x \<in> set path" | (new) "x = ?a" by auto
        then show "x < lineNumber z"
        proof cases
          case old
          from zls have "z \<in> set (l # ls)" by simp
          from 2(6) [OF old this] show ?thesis .
        next
          case new with gt zls show ?thesis by simp
        qed
      qed
      from 2(2) [OF Some sorted_wrt_map_takeWhile [OF srt] ps bef body]
      show ?thesis .
    next
      case rest
      have bef: "\<And>x z. x \<in> set path \<Longrightarrow> z \<in> set ?dw
                              \<Longrightarrow> x < lineNumber z"
        using 2(6) by (auto dest: set_dropWhileD)
      from 2(3) [OF Some sorted_wrt_map_dropWhile [OF srt] 2(5) bef rest]
      show ?thesis .
    qed
  qed
qed simp

lemma sorted_le_hd:
  "sorted xs \<Longrightarrow> y \<in> set xs \<Longrightarrow> hd xs \<le> y"
  by (cases xs) auto

lemma sorted_distinct_adj_imp_distinct:
  assumes "sorted xs" and "distinct_adj xs"
  shows "distinct xs"
using assms
proof (induction xs)
  case (Cons x xs)
  have sx: "sorted xs" using Cons.prems by simp
  have da: "distinct_adj xs" by (rule distinct_adj_ConsD [OF Cons.prems(2)])
  from Cons.IH [OF sx da] have dx: "distinct xs" .
  have xn: "x \<notin> set xs"
  proof
    assume xm: "x \<in> set xs"
    then have ne: "xs \<noteq> []" by auto
    from sorted_le_hd [OF sx xm] have hx: "hd xs \<le> x" .
    from Cons.prems(1) ne have xh: "x \<le> hd xs" by (cases xs) auto
    from Cons.prems(2) ne have "x \<noteq> hd xs" by (simp add: distinct_adj_Cons)
    with hx xh show False by simp
  qed
  with dx show ?case by simp
qed simp

theorem buildItems_scope_eq:
  assumes A: "lemmonToFitchDirect P = Inr F" and m: "fl \<in> set (flatten F)"
  shows "flScope fl = remdups_adj (boxPath P (flNum fl))"
proof -
  from A have corr: "lemmonCorrect P" and F: "F = buildItems (boxesOf P) P"
        and bo: "boxOrderError P = None" and bh: "boxHeadError P = None"
        and ne: "nestingError P = None" and se: "subScopeError P = None"
    by (auto simp: lemmonToFitchDirect_def split: option.splits if_splits)
  from corr have srt: "sorted_wrt (<) (map lineNumber P)" by (simp add: lemmonCorrect_def)
  from m F have m': "fl \<in> set (bflat (buildItems (boxesOf P) P) [])"
    by (simp add: flatten_bflat)
  have ord: "\<And>ac. ac \<in> set (boxesOf P) \<Longrightarrow> fst ac \<le> snd ac"
    using boxOrderError_None [OF bo] by blast
  from buildItems_scope_sub [OF srt ord m']
  have upper0: "set (flScope fl)
          \<subseteq> {a. \<exists>c. (a, c) \<in> set (boxesOf P)
                          \<and> a \<le> flNum fl \<and> flNum fl \<le> c}"
    by simp
  have upper: "set (flScope fl) \<subseteq> set (boxPath P (flNum fl))"
    using upper0 unfolding set_boxPath by force
  have heads: "\<And>b b'. b \<in> set (boxesOf P) \<Longrightarrow> b' \<in> set (boxesOf P)
                         \<Longrightarrow> fst b = fst b' \<Longrightarrow> snd b = snd b'"
    using boxHeadError_None [OF bh] by blast
  have source: "\<And>a c. (a, c) \<in> set (boxesOf P)
                         \<Longrightarrow> \<exists>l \<in> set P. lineNumber l = a"
    using boxesOf_opens_at_a_line [OF corr] by force
  have lower0:
    "{a. \<exists>c l. (a, c) \<in> set (boxesOf P) \<and> l \<in> set P
                    \<and> lineNumber l = a
                    \<and> a \<le> flNum fl \<and> flNum fl \<le> c}
       \<subseteq> set (flScope fl)"
    by (rule buildItems_scope_sup [OF srt boxesStrict_boxesOf [OF corr bo bh ne se]
                                      heads m'])
  have lower: "set (boxPath P (flNum fl)) \<subseteq> set (flScope fl)"
  proof
    fix a assume "a \<in> set (boxPath P (flNum fl))"
    from boxPath_memD [OF this] obtain c
      where b: "(a, c) \<in> set (boxesOf P)" and le: "a \<le> flNum fl" "flNum fl \<le> c"
      by blast
    from source [OF b] obtain l where "l \<in> set P" "lineNumber l = a" by blast
    with b le lower0 show "a \<in> set (flScope fl)" by blast
  qed
  have sets: "set (flScope fl) = set (remdups_adj (boxPath P (flNum fl)))"
    using upper lower by auto
  have ss: "sorted (flScope fl)" and ds: "distinct (flScope fl)"
    using buildItems_scope_sorted [OF srt _ _ m'] by (auto simp: strict_sorted_iff)
  have sb: "sorted (remdups_adj (boxPath P (flNum fl)))"
    by (simp add: boxPath_def)
  have db: "distinct (remdups_adj (boxPath P (flNum fl)))"
    by (rule sorted_distinct_adj_imp_distinct [OF sb]) simp
  from sorted_distinct_set_unique [OF ss ds sb db sets]
  show ?thesis .
qed

lemma is_prefix_dropWhile:
  assumes "is_prefix xs ys"
  shows "is_prefix (dropWhile P xs) (dropWhile P ys)"
proof -
  from is_prefix_ex [OF assms] obtain zs where ys: "ys = xs @ zs" by blast
  have "is_prefix (dropWhile P xs) (dropWhile P (xs @ zs))"
    by (induction xs) auto
  then show ?thesis by (simp add: ys)
qed

lemma is_prefix_remdups_adj:
  assumes "is_prefix xs ys"
  shows "is_prefix (remdups_adj xs) (remdups_adj ys)"
using assms
proof (induction "length xs" arbitrary: xs ys rule: less_induct)
  case (less xs)
  show ?case
  proof (cases xs)
    case [simp]: (Cons x xs')
    then obtain y ys' where [simp]: "ys = y # ys'"
      using \<open>is_prefix xs ys\<close> by (cases ys) auto
    from less show ?thesis
      by (auto simp: remdups_adj_Cons' less_Suc_eq_le length_dropWhile_le
               intro!: less is_prefix_dropWhile)
  qed auto
qed

lemma scopeError_None:
  assumes "scopeError P = None" and "l \<in> set P"
      and "m \<in> set (fCitedLines (toFitchRule (justification l)))"
  shows "is_prefix (boxPath P m) (boxPath P (lineNumber l))"
proof -
  from assms(1) have "badCitations P = []"
    unfolding scopeError_def by (auto split: list.splits prod.splits)
  then have "\<forall>l \<in> set P.
               filter (\<lambda>m. \<not> is_prefix (boxPath P m) (boxPath P (lineNumber l)))
                      (fCitedLines (toFitchRule (justification l))) = []"
    unfolding badCitations_def by simp
  with assms(2,3) show ?thesis by (auto simp: filter_empty_conv)
qed

lemma fCitedLines_toFitchRule:
  "set (fCitedLines (toFitchRule j)) \<subseteq> set (citedLines j)"
  by (cases j) auto

lemma buildItems_line:
  assumes "fl \<in> set (bflat (buildItems boxes ls) path)"
  shows "\<exists>l \<in> set ls. flNum fl = lineNumber l
          \<and> flRule fl =
              (if opensBox boxes l then FAssume else toFitchRule (justification l))"
proof -
  let ?fs = "bflat (buildItems boxes ls) path"
  from assms obtain i where i: "i < length ?fs" "?fs ! i = fl"
    by (meson in_set_conv_nth)
  from arg_cong [where f = length, OF buildItems_nums [of boxes ls path]]
  have len: "length ?fs = length ls" by simp
  with i(1) have il: "i < length ls" by simp
  let ?l = "ls ! i"
  have lm: "?l \<in> set ls" using il by simp
  from arg_cong [where f = "\<lambda>xs. xs ! i", OF buildItems_nums [of boxes ls path]]
  have num: "flNum fl = lineNumber ?l" using i il by simp
  from arg_cong [where f = "\<lambda>xs. xs ! i", OF buildItems_rules [of boxes ls path]]
  have rule: "flRule fl =
       (if opensBox boxes ?l then FAssume else toFitchRule (justification ?l))"
    using i il len by simp
  from lm num rule show ?thesis by blast
qed

theorem lemmonToFitchDirect_line_citations:
  assumes A: "lemmonToFitchDirect P = Inr F"
  shows "list_all
    (\<lambda>fl. list_all
      (\<lambda>m. m < flNum fl \<and>
        (case findFL (flatten F) m of
           None \<Rightarrow> False
         | Some fl' \<Rightarrow> is_prefix (flScope fl') (flScope fl)))
      (fCitedLines (flRule fl)))
    (flatten F)"
proof -
  from A have corr: "lemmonCorrect P" and F: "F = buildItems (boxesOf P) P"
        and sc: "scopeError P = None"
    by (auto simp: lemmonToFitchDirect_def split: option.splits if_splits)
  from lemmonToFitchDirect_sorted [OF A]
  have dist: "distinct (map flNum (flatten F))"
    by (rule sorted_wrt_less_distinct)
  show ?thesis
    unfolding list_all_iff
  proof (intro ballI)
    fix fl assume fm: "fl \<in> set (flatten F)"
    from fm F have fm': "fl \<in> set (bflat (buildItems (boxesOf P) P) [])"
      by (simp add: flatten_bflat)
    from buildItems_line [OF fm'] obtain l where l: "l \<in> set P"
      and num: "flNum fl = lineNumber l"
      and rule: "flRule fl =
          (if opensBox (boxesOf P) l then FAssume else toFitchRule (justification l))"
      by blast
    fix m assume mc: "m \<in> set (fCitedLines (flRule fl))"
      have nobox: "\<not> opensBox (boxesOf P) l"
      proof
        assume "opensBox (boxesOf P) l"
        with rule mc show False by simp
      qed
      with rule have fr: "flRule fl = toFitchRule (justification l)" by simp
      from mc fr have mc':
        "m \<in> set (fCitedLines (toFitchRule (justification l)))" by simp
      from subsetD [OF fCitedLines_toFitchRule [of "justification l"] mc']
      have cj: "m \<in> set (citedLines (justification l))" .
      from lemmonCorrect_citesDown [OF corr] l cj
      have down: "m < lineNumber l" and lookup: "lookupLine P m \<noteq> None"
        unfolding citesDown_def by blast+
      from lookup obtain lm where lk: "lookupLine P m = Some lm" by auto
      from lookupLine_Some [OF lk] have lmm: "lm \<in> set P" and lmn: "lineNumber lm = m"
        by auto
      from lmm lmn have min: "m \<in> set (map lineNumber P)" by auto
      have nums: "map flNum (flatten F) = map lineNumber P"
        using F by (simp add: flatten_bflat buildItems_nums)
      from min nums have "m \<in> set (map flNum (flatten F))" by simp
      then obtain fl' where flm: "fl' \<in> set (flatten F)" and fln: "flNum fl' = m"
        by auto
      from findFL_mem [OF dist flm] fln
      have find: "findFL (flatten F) m = Some fl'" by simp
      from scopeError_None [OF sc l mc']
      have bp: "is_prefix (boxPath P m) (boxPath P (lineNumber l))" .
      from is_prefix_remdups_adj [OF bp]
      have pref: "is_prefix (flScope fl') (flScope fl)"
        using buildItems_scope_eq [OF A flm] buildItems_scope_eq [OF A fm]
              fln num by simp
      from down num find pref show
        "m < flNum fl \<and>
          (case findFL (flatten F) m of None \<Rightarrow> False
            | Some fl' \<Rightarrow> is_prefix (flScope fl') (flScope fl))"
        by simp
  qed
qed

lemma lemmonToFitchDirect_source_line:
  assumes A: "lemmonToFitchDirect P = Inr F" and l: "l \<in> set P"
  shows "\<exists>fl \<in> set (flatten F). flNum fl = lineNumber l"
proof -
  from A have F: "F = buildItems (boxesOf P) P"
    by (auto simp: lemmonToFitchDirect_def split: option.splits if_splits)
  have nums: "map flNum (flatten F) = map lineNumber P"
    using F by (simp add: flatten_bflat buildItems_nums)
  from l have "lineNumber l \<in> set (map lineNumber P)" by simp
  with nums have "lineNumber l \<in> set (map flNum (flatten F))" by simp
  then show ?thesis by auto
qed

lemma sorted_dropWhile_gt:
  assumes "sorted (xs :: nat list)" and "x \<in> set (dropWhile (\<lambda>y. y \<le> c) xs)"
  shows "c < x"
using assms
proof (induction xs)
  case (Cons y ys)
  show ?case
  proof (cases "y \<le> c")
    case True with Cons show ?thesis by simp
  next
    case False
    with Cons.prems(2) have "x \<in> set (y # ys)" by simp
    with Cons.prems(1) False show ?thesis by auto
  qed
qed simp

text \<open>Inside a source box, the de-duplicated box path at its assumption
  line is a prefix of every later path in the box.  De-duplication is necessary
  because the reconstructed @{const OrElim} rule can name the same branch pair
  twice; the Fitch image still contains only one subproof.\<close>

lemma boxPath_interval_prefix:
  assumes strict: "boxesStrict (boxesOf P)"
      and heads: "\<And>b b'. b \<in> set (boxesOf P) \<Longrightarrow> b' \<in> set (boxesOf P)
                         \<Longrightarrow> fst b = fst b' \<Longrightarrow> snd b = snd b'"
      and box: "(a, c) \<in> set (boxesOf P)" and an: "a \<le> n" and nc: "n \<le> c"
  shows "is_prefix (remdups_adj (boxPath P a)) (remdups_adj (boxPath P n))"
proof -
  let ?xs = "remdups_adj (boxPath P a)"
  let ?ys = "remdups_adj (boxPath P n)"
  have sxs: "sorted ?xs" and sys: "sorted ?ys"
    by (simp_all add: boxPath_def)
  have dxs: "distinct ?xs"
    by (rule sorted_distinct_adj_imp_distinct [OF sxs]) simp
  have dys: "distinct ?ys"
    by (rule sorted_distinct_adj_imp_distinct [OF sys]) simp
  have sets: "set ?xs = set (filter (\<lambda>x. x \<le> a) ?ys)"
  proof
    show "set ?xs \<subseteq> set (filter (\<lambda>x. x \<le> a) ?ys)"
    proof
      fix x assume xm: "x \<in> set ?xs"
      then have xpa: "x \<in> set (boxPath P a)" by simp
      from boxPath_memD [OF xpa] obtain d
        where b: "(x, d) \<in> set (boxesOf P)" and xa: "x \<le> a" and ad: "a \<le> d"
        by blast
      have xn: "x \<in> set (boxPath P n)"
      proof (cases "x = a")
        case True
        from heads [OF b box] True have "d = c" by simp
        with b True an nc show ?thesis by (auto intro: boxPath_memI)
      next
        case False
        with xa have lt: "x < a" by simp
        from strict have nested:
          "\<forall>b \<in> set (boxesOf P). \<forall>b' \<in> set (boxesOf P).
             fst b < fst b' \<longrightarrow> fst b' \<le> snd b \<longrightarrow> snd b' < snd b"
          unfolding boxesStrict_def by simp
        from bspec [OF nested b] have nested_b:
          "\<forall>b' \<in> set (boxesOf P).
             fst (x, d) < fst b' \<longrightarrow> fst b' \<le> snd (x, d) \<longrightarrow> snd b' < snd (x, d)" .
        from bspec [OF nested_b box] lt ad have "c < d" by simp
        with b xa an nc show ?thesis by (auto intro: boxPath_memI)
      qed
      with xa show "x \<in> set (filter (\<lambda>x. x \<le> a) ?ys)" by simp
    qed
  next
    show "set (filter (\<lambda>x. x \<le> a) ?ys) \<subseteq> set ?xs"
    proof
      fix x assume "x \<in> set (filter (\<lambda>x. x \<le> a) ?ys)"
      then have xpn: "x \<in> set (boxPath P n)" and xa: "x \<le> a" by auto
      from boxPath_memD [OF xpn] obtain d
        where b: "(x, d) \<in> set (boxesOf P)" and nd: "n \<le> d" by blast
      from b xa an nd have "x \<in> set (boxPath P a)" by (auto intro: boxPath_memI)
      then show "x \<in> set ?xs" by simp
    qed
  qed
  have sf: "sorted (filter (\<lambda>x. x \<le> a) ?ys)"
    using sorted_filter [where f = id and xs = ?ys and P = "\<lambda>x. x \<le> a"] sys
    by simp
  have df: "distinct (filter (\<lambda>x. x \<le> a) ?ys)" using dys by simp
  from sorted_distinct_set_unique [OF sxs dxs sf df sets]
  have xf: "?xs = filter (\<lambda>x. x \<le> a) ?ys" .
  have tf: "takeWhile (\<lambda>x. x \<le> a) ?ys = filter (\<lambda>x. x \<le> a) ?ys"
  proof (rule takeWhile_eq_filter)
    fix x assume "x \<in> set (dropWhile (\<lambda>x. x \<le> a) ?ys)"
    from sorted_dropWhile_gt [OF sys this] show "\<not> x \<le> a" by simp
  qed
  have "is_prefix (takeWhile (\<lambda>x. x \<le> a) ?ys) ?ys"
    using takeWhile_dropWhile_id [of "\<lambda>x. x \<le> a" ?ys]
    by (metis is_prefix_self_append)
  with xf tf show ?thesis by simp
qed

lemma accepted_subproof_box:
  assumes A: "lemmonToFitchDirect P = Inr F" and sp: "(s, p) \<in> set (subs F)"
      and srtF: "sorted_wrt (<) (map flNum (flatten F))"
      and lastF: "list_all lastIsLineItem F"
  shows "(subAssumeLine s, subLastLine s) \<in> set (boxesOf P)
       \<and> p = remdups_adj (subLevel P (subAssumeLine s, subLastLine s))"
proof -
  let ?a = "subAssumeLine s" and ?c = "subLastLine s"
  let ?h = "FL ?a (subAssumeForm s) FAssume (p @ [?a])"
  from A have corr: "lemmonCorrect P" and bo: "boxOrderError P = None"
        and bh: "boxHeadError P = None" and ne: "nestingError P = None"
        and se: "subScopeError P = None"
    by (auto simp: lemmonToFitchDirect_def split: option.splits if_splits)
  have strict: "boxesStrict (boxesOf P)" by (rule boxesStrict_boxesOf [OF corr bo bh ne se])
  have heads: "\<And>b b'. b \<in> set (boxesOf P) \<Longrightarrow> b' \<in> set (boxesOf P)
                         \<Longrightarrow> fst b = fst b' \<Longrightarrow> snd b = snd b'"
    using boxHeadError_None [OF bh] by blast
  from subs_block_proof [OF sp] obtain before after
    where split: "flatten F = before @ flatSub s p @ after" by blast
  have hin: "?h \<in> set (flatSub s p)" by (subst flatSub_hd) simp
  with split have hflat: "?h \<in> set (flatten F)" by auto
  have hscope: "p @ [?a] = remdups_adj (boxPath P ?a)"
    using buildItems_scope_eq [OF A hflat] by simp
  from arg_cong [where f = set, OF hscope]
  have "set (p @ [?a]) = set (boxPath P ?a)" by simp
  then have "?a \<in> set (boxPath P ?a)" by auto
  from boxPath_memD [OF this] obtain c0
    where b0: "(?a, c0) \<in> set (boxesOf P)" and ac0: "?a \<le> c0" by blast

  have plevel: "p = remdups_adj (subLevel P (?a, ?c))"
  proof -
    have spath: "sorted (p @ [?a])" and dpath: "distinct (p @ [?a])"
      using hscope by (auto simp: boxPath_def intro: sorted_distinct_adj_imp_distinct)
    from spath have ps: "sorted p" by (simp add: sorted_wrt_append)
    from dpath have pd: "distinct p" and anot: "?a \<notin> set p" by auto
    have bp_sorted: "sorted (boxPath P ?a)" by (simp add: boxPath_def)
    have raw: "sorted (subLevel P (?a, ?c))"
      using sorted_filter [where f = id and xs = "boxPath P ?a" and P = "\<lambda>y. ?a \<noteq> y"]
            bp_sorted
      by (simp add: subLevel_def removeAll_filter_not_eq)
    have sr: "sorted (remdups_adj (subLevel P (?a, ?c)))" using raw by simp
    have dr: "distinct (remdups_adj (subLevel P (?a, ?c)))"
      by (rule sorted_distinct_adj_imp_distinct [OF sr]) simp
    from arg_cong [where f = set, OF hscope]
    have pathset: "set (p @ [?a]) = set (boxPath P ?a)" by simp
    have seteq: "set p = set (remdups_adj (subLevel P (?a, ?c)))"
      using pathset anot by (auto simp: subLevel_def)
    from sorted_distinct_set_unique [OF ps pd sr dr seteq] show ?thesis .
  qed

  from boxesOf_closes_at_a_line [OF corr b0] obtain l0
    where l0: "l0 \<in> set P" "lineNumber l0 = c0" by auto
  from lemmonToFitchDirect_source_line [OF A l0(1)] obtain fl0
    where fl00: "fl0 \<in> set (flatten F)" "flNum fl0 = lineNumber l0" by auto
  with l0(2) have fl0: "fl0 \<in> set (flatten F)" "flNum fl0 = c0" by simp_all
  from boxPath_interval_prefix [OF strict heads b0 ac0 order_refl]
  have bp0: "is_prefix (remdups_adj (boxPath P ?a))
                       (remdups_adj (boxPath P c0))" .
  have pref0: "is_prefix (p @ [?a]) (flScope fl0)"
    using bp0 hscope buildItems_scope_eq [OF A fl0(1)] fl0(2) by simp
  from srtF lastF subs_span_structural [of F s p fl0]
  have c0le: "c0 \<le> ?c" using sp fl0 pref0 by blast

  have lil: "lastIsLineSub s"
    using sp lastF
    by (auto simp: subs_def list_all_iff dest: subs_lastIsLine(1))
  obtain sa sfa sbody where sdef: "s = Subproof sa sfa sbody" by (cases s)
  with lil have lil': "lastIsLineSub (Subproof sa sfa sbody)" by simp
  from subLastLine_last [OF lil', of p] obtain f r
    where last: "last (flatSub s p) = FL ?c f r (p @ [?a])"
    using sdef by auto
  have lastin: "FL ?c f r (p @ [?a]) \<in> set (flatSub s p)"
    using last flatSub_nonempty last_in_set by metis
  with split have lastflat: "FL ?c f r (p @ [?a]) \<in> set (flatten F)" by auto
  from buildItems_scope_eq [OF A lastflat]
  have lastscope: "p @ [?a] = remdups_adj (boxPath P ?c)" by simp
  from arg_cong [where f = set, OF lastscope]
  have "set (p @ [?a]) = set (boxPath P ?c)" by simp
  then have "?a \<in> set (boxPath P ?c)" by auto
  from boxPath_memD [OF this] obtain c1
    where b1: "(?a, c1) \<in> set (boxesOf P)" and cc1: "?c \<le> c1" by blast
  from heads [OF b1 b0] have "c1 = c0" by simp
  with c0le cc1 have ceq: "?c = c0" by simp
  with b0 plevel show ?thesis by simp
qed

theorem buildItems_subrefs_structural:
  assumes A: "lemmonToFitchDirect P = Inr F"
      and srtF: "sorted_wrt (<) (map flNum (flatten F))"
      and lastF: "list_all lastIsLineItem F"
  shows "((a, c), path) \<in> set (subrefs F)
       \<longleftrightarrow> (a, c) \<in> set (boxesOf P)
             \<and> path = remdups_adj (subLevel P (a, c))"
proof
  assume ref: "((a, c), path) \<in> set (subrefs F)"
  from subrefs_subs_proof [OF ref] obtain s
    where sp: "(s, path) \<in> set (subs F)"
      and sa: "subAssumeLine s = a" and sc: "subLastLine s = c" by blast
  from accepted_subproof_box [OF A sp srtF lastF] sa sc
  show "(a, c) \<in> set (boxesOf P) \<and> path = remdups_adj (subLevel P (a, c))"
    by simp
next
  assume rhs: "(a, c) \<in> set (boxesOf P)
             \<and> path = remdups_adj (subLevel P (a, c))"
  then have box: "(a, c) \<in> set (boxesOf P)" and path: "path = remdups_adj (subLevel P (a, c))"
    by auto
  from A have corr: "lemmonCorrect P" and bo: "boxOrderError P = None"
        and bh: "boxHeadError P = None"
    by (auto simp: lemmonToFitchDirect_def split: option.splits if_splits)
  from boxesOf_opens_at_a_line [OF corr box] obtain l
    where l: "l \<in> set P" "lineNumber l = a" by auto
  from lemmonToFitchDirect_source_line [OF A l(1)] obtain fl
    where fl0: "fl \<in> set (flatten F)" "flNum fl = lineNumber l" by auto
  with l(2) have fl: "fl \<in> set (flatten F)" "flNum fl = a" by simp_all
  from boxOrderError_None [OF bo box] have ac: "a \<le> c" by simp
  from boxPath_memI [OF box order_refl ac] have "a \<in> set (boxPath P a)" .
  from buildItems_scope_eq [OF A fl(1)] fl(2)
  have scope: "flScope fl = remdups_adj (boxPath P a)" by simp
  with \<open>a \<in> set (boxPath P a)\<close> have "a \<in> set (flScope fl)" by auto
  from scope_mem_sub_proof [OF fl(1) this] obtain s q
    where sp: "(s, q) \<in> set (subs F)" and sa: "subAssumeLine s = a" by blast
  from accepted_subproof_box [OF A sp srtF lastF] sa
  have b': "(a, subLastLine s) \<in> set (boxesOf P)"
    and q: "q = remdups_adj (subLevel P (a, subLastLine s))" by auto
  from boxHeadError_None [OF bh b' box] have ceq: "subLastLine s = c" by simp
  from subs_subrefs_proof [OF sp] have "((a, c), q) \<in> set (subrefs F)"
    using sa ceq by simp
  with q ceq path show "((a, c), path) \<in> set (subrefs F)" by simp
qed

subsection \<open>The conjunct\<close>

lemma buildItems_lastIsLine:
  "sorted_wrt (<) (map lineNumber ls) \<Longrightarrow> boxesStrict boxes \<Longrightarrow> boxesLandIn boxes ls \<Longrightarrow>
     list_all lastIsLineItem (buildItems boxes ls)"
proof (induction boxes ls rule: buildItems.induct)
  case (2 boxes l ls)
  have srt: "sorted_wrt (<) (map lineNumber ls)" using 2(4) by simp
  have gt: "\<forall>z \<in> set ls. lineNumber l < lineNumber z" using 2(4) by simp
  have ordb: "\<forall>b \<in> set boxes. fst b \<le> snd b" using 2(5) by (simp add: boxesStrict_def)
  show ?case
  proof (cases "find (\<lambda>ac. fst ac = lineNumber l) boxes")
    case None
    have land: "boxesLandIn boxes ls"
      unfolding boxesLandIn_def
    proof (intro ballI impI)
      fix l' b assume m: "l' \<in> set ls" and bm: "b \<in> set boxes" and bf: "fst b = lineNumber l'"
      from m have mcons: "l' \<in> set (l # ls)" by simp
      from 2(6) [unfolded boxesLandIn_def] mcons bm bf obtain l''
        where l'': "l'' \<in> set (l # ls)" "lineNumber l'' = snd b" by blast
      from bspec [OF ordb bm] have fs: "fst b \<le> snd b" .
      from gt m have "lineNumber l < lineNumber l'" by simp
      with fs bf l''(2) have "lineNumber l < lineNumber l''" by linarith
      then have "l'' \<noteq> l" by auto
      with l''(1) l''(2) show "\<exists>x \<in> set ls. lineNumber x = snd b" by auto
    qed
    from 2(1) [OF None srt 2(5) land] show ?thesis using None by simp
  next
    case (Some ac)
    let ?c = "snd ac"
    let ?tw = "takeWhile (\<lambda>l'. lineNumber l' \<le> ?c) ls"
    let ?dw = "dropWhile (\<lambda>l'. lineNumber l' \<le> ?c) ls"
    from find_Some_mem [OF Some] have acm: "ac \<in> set boxes" and acf: "fst ac = lineNumber l"
      by auto
    from bspec [OF ordb acm] acf have ord: "lineNumber l \<le> ?c" by simp

    have inner: "\<And>l' b. l' \<in> set ?tw \<Longrightarrow> b \<in> set boxes \<Longrightarrow> fst b = lineNumber l'
                          \<Longrightarrow> snd b < ?c"
    proof -
      fix l' b assume m: "l' \<in> set ?tw" and bm: "b \<in> set boxes" and bf: "fst b = lineNumber l'"
      from m have mls: "l' \<in> set ls" and upper: "lineNumber l' \<le> ?c"
        by (auto dest: set_takeWhileD)
      from gt mls have "lineNumber l < lineNumber l'" by simp
      with acf bf have "fst ac < fst b" by simp
      moreover from bf upper have "fst b \<le> ?c" by simp
      ultimately show "snd b < ?c"
        using 2(5) acm bm unfolding boxesStrict_def by blast
    qed

    have landtw: "boxesLandIn boxes ?tw"
      unfolding boxesLandIn_def
    proof (intro ballI impI)
      fix l' b assume m: "l' \<in> set ?tw" and bm: "b \<in> set boxes" and bf: "fst b = lineNumber l'"
      from m have mls: "l' \<in> set ls" by (auto dest: set_takeWhileD)
      then have mcons: "l' \<in> set (l # ls)" by simp
      from 2(6) [unfolded boxesLandIn_def] mcons bm bf obtain l''
        where l'': "l'' \<in> set (l # ls)" "lineNumber l'' = snd b" by blast
      from bspec [OF ordb bm] have fs: "fst b \<le> snd b" .
      from gt mls have "lineNumber l < lineNumber l'" by simp
      with fs bf l''(2) have "lineNumber l < lineNumber l''" by linarith
      then have "l'' \<noteq> l" by auto
      with l''(1) have mem: "l'' \<in> set ls" by simp
      from inner [OF m bm bf] l''(2) have "lineNumber l'' \<le> ?c" by simp
      from mem_takeWhile_le [OF srt mem this] l''(2)
      show "\<exists>x \<in> set ?tw. lineNumber x = snd b" by blast
    qed

    have landdw: "boxesLandIn boxes ?dw"
      unfolding boxesLandIn_def
    proof (intro ballI impI)
      fix l' b assume m: "l' \<in> set ?dw" and bm: "b \<in> set boxes" and bf: "fst b = lineNumber l'"
      from m have mls: "l' \<in> set ls" by (rule set_dropWhileD)
      from dropWhile_le_gt [OF srt m] have gtc: "?c < lineNumber l'" .
      from mls have mcons: "l' \<in> set (l # ls)" by simp
      from 2(6) [unfolded boxesLandIn_def] mcons bm bf obtain l''
        where l'': "l'' \<in> set (l # ls)" "lineNumber l'' = snd b" by blast
      from bspec [OF ordb bm] have fs: "fst b \<le> snd b" .
      from fs bf gtc l''(2) have big: "?c < lineNumber l''" by linarith
      with ord have "l'' \<noteq> l" by auto
      with l''(1) have mem: "l'' \<in> set ls" by simp
      from big have "\<not> lineNumber l'' \<le> ?c" by simp
      from mem_dropWhile_gt [OF mem this] l''(2)
      show "\<exists>x \<in> set ?dw. lineNumber x = snd b" by blast
    qed

    from 2(2) [OF Some sorted_wrt_map_takeWhile [OF srt] 2(5) landtw]
    have b1: "list_all lastIsLineItem (buildItems boxes ?tw)" .
    from 2(3) [OF Some sorted_wrt_map_dropWhile [OF srt] 2(5) landdw]
    have b2: "list_all lastIsLineItem (buildItems boxes ?dw)" .

    have sub: "lastIsLineItem
                 (FSub (Subproof (lineNumber l) (formula l) (buildItems boxes ?tw)))"
    proof (cases "?tw = []")
      case True with b1 show ?thesis by simp
    next
      case False
      \<comment> \<open>the block reaches the line the box closes at, so that line is its last\<close>
      have lcons: "l \<in> set (l # ls)" by simp
      from 2(6) [unfolded boxesLandIn_def] lcons acm acf
      obtain l0 where l0: "l0 \<in> set (l # ls)" "lineNumber l0 = ?c" by blast
      have "l0 \<noteq> l"
      proof
        assume "l0 = l"
        with l0(2) have eqc: "?c = lineNumber l" by simp
        have "?tw = []"
        proof (cases ls)
          case Nil then show ?thesis by simp
        next
          case (Cons z zs)
          with gt have "lineNumber l < lineNumber z" by simp
          with eqc Cons show ?thesis by simp
        qed
        with False show False ..
      qed
      with l0(1) have "l0 \<in> set ls" by simp
      from mem_takeWhile_le [OF srt this] l0(2) have "l0 \<in> set ?tw" by simp
      then have "lineNumber l0 \<in> set (map lineNumber ?tw)" by simp
      from sorted_wrt_less_last [OF sorted_wrt_map_takeWhile [OF srt] this] False
      have cle: "?c \<le> lineNumber (last ?tw)" using l0(2) by (simp add: last_map)
      have closed: "boxesClosedIn boxes ?tw"
        unfolding boxesClosedIn_def
      proof (intro ballI impI)
        fix l' b assume m: "l' \<in> set ?tw" and bm: "b \<in> set boxes"
          and bf: "fst b = lineNumber l'"
        from inner [OF m bm bf] cle show "snd b < lineNumber (last ?tw)" by simp
      qed
      from buildItems_last [OF False ordb closed] obtain n f r
        where "last (buildItems boxes ?tw) = FLine n f r" by blast
      moreover from False have "buildItems boxes ?tw \<noteq> []" by (rule buildItems_nonempty)
      ultimately show ?thesis using b1 by simp
    qed
    from sub b2 show ?thesis using Some by simp
  qed
qed simp

theorem lemmonToFitchDirect_lastIsLine:
  assumes A: "lemmonToFitchDirect P = Inr F"
  shows "list_all lastIsLineItem F"
proof -
  from A have corr: "lemmonCorrect P" and F: "F = buildItems (boxesOf P) P"
        and bo: "boxOrderError P = None" and bh: "boxHeadError P = None"
        and ne: "nestingError P = None" and se: "subScopeError P = None"
    by (auto simp: lemmonToFitchDirect_def split: option.splits if_splits)
  from corr have srt: "sorted_wrt (<) (map lineNumber P)" by (simp add: lemmonCorrect_def)
  from buildItems_lastIsLine [OF srt boxesStrict_boxesOf [OF corr bo bh ne se]
                                 boxesLandIn_boxesOf [OF corr]]
  show ?thesis using F by simp
qed

theorem buildItems_subrefs:
  assumes A: "lemmonToFitchDirect P = Inr F"
  shows "((a, c), path) \<in> set (subrefs F)
       \<longleftrightarrow> (a, c) \<in> set (boxesOf P)
             \<and> path = remdups_adj (subLevel P (a, c))"
  by (rule buildItems_subrefs_structural [OF A lemmonToFitchDirect_sorted [OF A]
                                              lemmonToFitchDirect_lastIsLine [OF A]])

lemma fCitedSubs_toFitchRule:
  "fCitedSubs (toFitchRule j) = dischargePairs j"
  by (cases j) auto

theorem lemmonToFitchDirect_sub_citations:
  assumes A: "lemmonToFitchDirect P = Inr F"
  shows "list_all
    (\<lambda>fl. list_all
      (\<lambda>(a, c). c < flNum fl \<and> ((a, c), flScope fl) \<in> set (subrefs F))
      (fCitedSubs (flRule fl)))
    (flatten F)"
proof -
  from A have corr: "lemmonCorrect P" and F: "F = buildItems (boxesOf P) P"
        and suberr: "subScopeError P = None"
    by (auto simp: lemmonToFitchDirect_def split: option.splits if_splits)
  show ?thesis
    unfolding list_all_iff
  proof (intro ballI)
    fix fl assume fm: "fl \<in> set (flatten F)"
    from fm F have fm': "fl \<in> set (bflat (buildItems (boxesOf P) P) [])"
      by (simp add: flatten_bflat)
    from buildItems_line [OF fm'] obtain l where l: "l \<in> set P"
      and num: "flNum fl = lineNumber l"
      and rule: "flRule fl =
          (if opensBox (boxesOf P) l then FAssume else toFitchRule (justification l))"
      by blast
    fix ac assume acm: "ac \<in> set (fCitedSubs (flRule fl))"
    have nobox: "\<not> opensBox (boxesOf P) l"
    proof
      assume "opensBox (boxesOf P) l"
      with rule acm show False by simp
    qed
    with rule have fr: "flRule fl = toFitchRule (justification l)" by simp
    from acm fr have dp: "ac \<in> set (dischargePairs (justification l))"
      by (simp add: fCitedSubs_toFitchRule)
    have box: "ac \<in> set (boxesOf P)" using l dp unfolding boxesOf_def by auto
    from dischargePairs_earlier(2) [OF corr l dp]
    have close: "snd ac < flNum fl" using num by simp
    from subScopeError_None [OF suberr l dp]
    have level: "boxPath P (flNum fl) = subLevel P ac" using num by simp
    have scope: "flScope fl = remdups_adj (subLevel P ac)"
      using buildItems_scope_eq [OF A fm] level by simp
    obtain a c where acdef: "ac = (a, c)" by (cases ac)
    from buildItems_subrefs [OF A, of a c "flScope fl"] box scope acdef
    have "((fst ac, snd ac), flScope fl) \<in> set (subrefs F)" by simp
    with close show
      "case ac of (a, c) \<Rightarrow> c < flNum fl \<and> ((a, c), flScope fl) \<in> set (subrefs F)"
      by (cases ac) simp
  qed
qed

theorem lemmonToFitchDirect_citations:
  assumes A: "lemmonToFitchDirect P = Inr F"
  shows "list_all (citationOK F) (flatten F)"
  using lemmonToFitchDirect_line_citations [OF A]
        lemmonToFitchDirect_sub_citations [OF A]
  unfolding citationOK_def list_all_iff
  by blast

subsection \<open>All six\<close>

text \<open>The five structural conjuncts of @{const fitchWF} and the citation
  conjunct are now proved.  The intermediate equivalence records the useful
  reduction to citations; the following theorem closes the soundness proof.\<close>

theorem lemmonToFitchDirect_fitchWF_iff_citations:
  assumes A: "lemmonToFitchDirect P = Inr F"
  shows "fitchWF F \<longleftrightarrow> list_all (citationOK F) (flatten F)"
  unfolding fitchWF_def
  using lemmonToFitchDirect_sorted [OF A] lemmonToFitchDirect_noAssume [OF A]
        lemmonToFitchDirect_premise_scope [OF A]
        lemmonToFitchDirect_premisesFirst [OF A]
        lemmonToFitchDirect_lastIsLine [OF A]
  by blast

theorem lemmonToFitchDirect_fitchWF:
  assumes A: "lemmonToFitchDirect P = Inr F"
  shows "fitchWF F"
  using lemmonToFitchDirect_fitchWF_iff_citations [OF A]
        lemmonToFitchDirect_citations [OF A]
  by simp

section \<open>A second gap: premises need not come first\<close>

text \<open>@{const fitchWF} also demands @{const premisesFirst}: every premise line
  stands before every line that is not one.  Fitch requires it --- a premise is
  an assumption of the whole proof, and the notation writes them at the top ---
  and Lemmon has no such convention.  An undischarged assumption may be made at
  any point, and none of the four obstructions looks at where.

  Three lines are enough.  Line 3 is an assumption that is never discharged, so
  it becomes a premise of the image, and it stands after line 2, which is not a
  premise.\<close>

definition premLate :: lemmon_proof where
  "premLate =
     [ ProofLine 1 Pf Assumption {1}
     , ProofLine 2 (Disj Pf Rf) (OrIntroL 1) {1}
     , ProofLine 3 Qf Assumption {3} ]"

lemma premLate_correct: "lemmonCorrect premLate"
  by eval

lemma premLate_passes_obstructions:
  "nestingError premLate = None" "premiseError premLate = None"
  "scopeError premLate = None"  "subScopeError premLate = None"
  by eval+

text \<open>With those four alone the translation succeeded and returned this, which is
  not a Fitch proof.  The object is still there to be inspected.\<close>

lemma premLate_image_malformed:
  "\<not> fitchWF (buildItems (boxesOf premLate) premLate)"
  "fitchWellFormed (buildItems (boxesOf premLate) premLate)
     = Some (STR ''a premise occurs after a line that is not a premise'')"
  by eval+

text \<open>@{const premiseOrderError} is the missing check, and with it the source is
  rejected, naming the premise and the earlier line that is not one.\<close>

lemma premLate_rejected:
  "lemmonToFitchDirect premLate = Inl (PremiseLate 3 2)"
  by eval

section \<open>A third gap: a discharge may run backwards\<close>

text \<open>Lemmon's \<open>CP a c\<close> discharges the assumption at line \<open>a\<close> from line \<open>c\<close>, and
  nothing makes \<open>a\<close> precede \<open>c\<close>.  A \emph{vacuous} discharge --- where \<open>c\<close> does
  not depend on \<open>a\<close> at all --- may perfectly well cite an assumption made later,
  and the result is a correct Lemmon proof whose box is the empty interval
  @{term "(2::nat, 1::nat)"}.

  Line 1 does not depend on line 2, so discharging 2 from 1 is legitimate and
  yields @{term "Impl Qf Pf"} resting on \<open>{1}\<close>.\<close>

definition backCP :: lemmon_proof where
  "backCP =
     [ ProofLine 1 Pf Assumption {1}
     , ProofLine 2 Qf Assumption {2}
     , ProofLine 3 (Impl Qf Pf) (CP 2 1) {1} ]"

lemma backCP_correct: "lemmonCorrect backCP"
  by eval

lemma backCP_box_reversed: "boxesOf backCP = [(2, 1)]"
  by eval

text \<open>The other five obstructions see nothing wrong, and the image
  @{const buildItems} builds has an empty subproof whose reported last line, 1,
  lies outside it --- so line 3 cites a subproof that is not there.\<close>

lemma backCP_passes_the_others:
  "nestingError backCP = None" "premiseError backCP = None"
  "scopeError backCP = None"   "subScopeError backCP = None"
  "premiseOrderError backCP = None"
  by eval+

lemma backCP_image_malformed:
  "\<not> fitchWF (buildItems (boxesOf backCP) backCP)"
  "fitchWellFormed (buildItems (boxesOf backCP) backCP)
     = Some (STR ''a line cites something not in its scope'')"
  by eval+

text \<open>@{const boxOrderError} is the missing check, and it runs first because every
  other check reads a box as an interval.\<close>

lemma backCP_rejected: "lemmonToFitchDirect backCP = Inl (BoxReversed 2 1)"
  by eval

text \<open>With it, the hypothesis @{thm [source] buildItems_scope_sub} needs --- that a
  box runs forwards --- is discharged for any source the translation accepts.\<close>

lemma lemmonToFitchDirect_boxes_ordered:
  assumes "lemmonToFitchDirect P = Inr F" and "ac \<in> set (boxesOf P)"
  shows "fst ac \<le> snd ac"
proof -
  from assms(1) have "boxOrderError P = None"
    by (auto simp: lemmonToFitchDirect_def split: option.splits if_splits)
  from boxOrderError_None [OF this assms(2)] show ?thesis .
qed

section \<open>A fourth gap: one assumption, two discharges\<close>

text \<open>Lemmon may discharge one assumption from two \emph{different} lines.  The
  two boxes then share their opening line, and a positional image would need two
  subproofs starting there.  @{const buildItems} builds the first and the second
  discharge is left citing a subproof that does not exist.

  Nothing outside a box cites anything inside one here, which is why
  @{const scopeError} sees nothing --- the case below, \<open>twiceDischarged\<close>,
  is caught by it only because it happens to have such a citation.  That
  difference is why this had to be found by construction rather than by
  argument.\<close>

definition reused :: lemmon_proof where
  "reused =
     [ ProofLine 1 Pf Assumption {1}
     , ProofLine 2 Qf Assumption {2}
     , ProofLine 3 (Conj Pf Qf) (AndIntro 1 2) {1, 2}
     , ProofLine 4 (Disj Pf Rf) (OrIntroL 1) {1}
     , ProofLine 5 (Impl Qf (Conj Pf Qf)) (CP 2 3) {1}
     , ProofLine 6 (Impl Qf (Disj Pf Rf)) (CP 2 4) {1} ]"

lemma reused_correct: "lemmonCorrect reused"
  by eval

lemma reused_boxes_share_head: "boxesOf reused = [(2, 3), (2, 4)]"
  by eval

lemma reused_passes_the_other_six:
  "boxOrderError reused = None" "nestingError reused = None"
  "premiseError reused = None"  "scopeError reused = None"
  "subScopeError reused = None" "premiseOrderError reused = None"
  by eval+

lemma reused_image_malformed:
  "\<not> fitchWF (buildItems (boxesOf reused) reused)"
  "fitchWellFormed (buildItems (boxesOf reused) reused)
     = Some (STR ''a line cites something not in its scope'')"
  by eval+

lemma reused_rejected: "lemmonToFitchDirect reused = Inl (AssumptionReused 2 3 4)"
  by eval

section \<open>Not a gap: the same assumption discharged twice from the same line\<close>

text \<open>An exact duplicate discharge pair is different again.  The reconstructed
  @{const OrElim} rule permits its two branches to name the same assumption and
  conclusion when the disjuncts coincide.  Then @{const boxPath} contains the
  same box head twice, while @{const buildItems} quite properly emits just one
  subproof.  The translation is nevertheless well formed: its discharging rule
  simply cites that one subproof twice.  This is why the scope invariant below
  is stated after removing duplicates from @{const boxPath}, rather than as the
  tempting but false equality with @{const boxPath} itself.\<close>

definition duplicateDischarge :: lemmon_proof where
  "duplicateDischarge =
     [ ProofLine 1 (Disj Pf Pf) Assumption {1}
     , ProofLine 2 Pf Assumption {2}
     , ProofLine 3 Pf (OrElim 1 2 2 2 2) {1} ]"

lemma duplicateDischarge_correct: "lemmonCorrect duplicateDischarge"
  by eval

lemma duplicateDischarge_boxes: "boxesOf duplicateDischarge = [(2, 2), (2, 2)]"
  by eval

definition duplicateDischarge_fitch :: fitch_proof where
  "duplicateDischarge_fitch =
     [ FLine 1 (Disj Pf Pf) FPremise
     , FSub (Subproof 2 Pf [])
     , FLine 3 Pf (FOrElim 1 (2, 2) (2, 2)) ]"

lemma duplicateDischarge_accepted:
  "lemmonToFitchDirect duplicateDischarge = Inr duplicateDischarge_fitch
     \<and> fitchWF duplicateDischarge_fitch"
  by eval

lemma duplicateDischarge_scope_not_boxPath:
  "findFL (flatten duplicateDischarge_fitch) 2 = Some (FL 2 Pf FAssume [2])
     \<and> boxPath duplicateDischarge 2 = [2, 2]"
  by eval

text \<open>Lemmon may discharge one assumption more than once --- here assumption 2 is
  discharged at line 4, from line 3, and again at line 5, from itself.  The boxes
  then share a first endpoint, @{term "[(2::nat, 3::nat), (2, 2)]"}, and
  @{const buildItems} would build only the first of them, leaving line 5 citing a
  subproof that is not there.

  This one the checks that were already there do catch, and it is worth
  recording which: @{const scopeError}, because line 2 then lies in two boxes at
  once, so @{term "boxPath P 2"} repeats and is no longer a prefix of
  @{term "boxPath P 3"}.  So it was not this case that forced
  @{const boxHeadError} --- though, now that the check exists, it is the one that
  reaches this proof first.\<close>

definition twiceDischarged :: lemmon_proof where
  "twiceDischarged =
     [ ProofLine 1 Pf Assumption {1}
     , ProofLine 2 Qf Assumption {2}
     , ProofLine 3 (Conj Pf Qf) (AndIntro 1 2) {1, 2}
     , ProofLine 4 (Impl Qf (Conj Pf Qf)) (CP 2 3) {1}
     , ProofLine 5 (Impl Qf Qf) (CP 2 2) {} ]"

lemma twiceDischarged_correct: "lemmonCorrect twiceDischarged"
  by eval

lemma twiceDischarged_boxes_share_head: "boxesOf twiceDischarged = [(2, 3), (2, 2)]"
  by eval

lemma twiceDischarged_image_malformed:
  "\<not> fitchWF (buildItems (boxesOf twiceDischarged) twiceDischarged)"
  by eval

lemma twiceDischarged_caught_by_scope:
  "scopeError twiceDischarged = Some (OutOfScope 3 2 2)"
  by eval

lemma twiceDischarged_rejected:
  "lemmonToFitchDirect twiceDischarged = Inl (AssumptionReused 2 3 2)"
  by eval

end
