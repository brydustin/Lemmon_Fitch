(*  Title:      LF_Span.thy

    The structural fact the development was missing: a subproof occupies a
    contiguous block of the flattened proof, running from its assumption line to
    its last line.  Everything about scope follows --- in particular that a line
    lies inside a subproof exactly when its number lies between the subproof's
    endpoints, which is what makes Theorem 10 provable as the paper states it
    rather than as a report about the checker.
*)

theory LF_Span
  imports LF_Examples
begin

section \<open>Prefixes\<close>

lemma is_prefix_self_append [simp]: "is_prefix xs (xs @ ys)"
  by (induction xs) auto

lemma is_prefix_ex: "is_prefix xs ys \<Longrightarrow> \<exists>zs. ys = xs @ zs"
  by (induction xs ys rule: is_prefix.induct) auto

lemma is_prefix_trans:
  assumes "is_prefix xs ys" and "is_prefix ys zs"
  shows "is_prefix xs zs"
proof -
  from is_prefix_ex [OF assms(1)] obtain us where "ys = xs @ us" by blast
  moreover from is_prefix_ex [OF assms(2)] obtain vs where "zs = ys @ vs" by blast
  ultimately have "zs = xs @ (us @ vs)" by simp
  then show ?thesis by simp
qed

lemma is_prefix_antisym:
  assumes "is_prefix xs ys" and "is_prefix ys xs"
  shows "xs = ys"
proof -
  from is_prefix_ex [OF assms(1)] obtain us where u: "ys = xs @ us" by blast
  from is_prefix_ex [OF assms(2)] obtain vs where v: "xs = ys @ vs" by blast
  from u v have "length xs = length xs + length us + length vs" by simp
  then have "us = []" by simp
  with u show ?thesis by simp
qed

section \<open>The subproofs of a proof, with the level each sits at\<close>

text \<open>@{const subrefsItem} records a subproof as the pair of its endpoints.  For
  the structural argument we want the subproof itself, so that its flattening can
  be spoken of; otherwise the recursion is the same one.\<close>

primrec subsItem :: "fitch_item \<Rightarrow> nat list \<Rightarrow> (subproof \<times> nat list) list"
    and subsSub :: "subproof \<Rightarrow> nat list \<Rightarrow> (subproof \<times> nat list) list" where
  "subsItem (FLine _ _ _) path = []"
| "subsItem (FSub s) path = subsSub s path"
| "subsSub (Subproof a fa body) path =
     (Subproof a fa body, path)
       # concat (map (\<lambda>it. subsItem it (path @ [a])) body)"

definition subs :: "fitch_proof \<Rightarrow> (subproof \<times> nat list) list" where
  "subs F = concat (map (\<lambda>it. subsItem it []) F)"

lemma subs_subrefs:
  "(s, p) \<in> set (subsItem it path)
     \<Longrightarrow> ((subAssumeLine s, subLastLine s), p) \<in> set (subrefsItem it path)"
  "(s, p) \<in> set (subsSub t path)
     \<Longrightarrow> ((subAssumeLine s, subLastLine s), p) \<in> set (subrefsSub t path)"
  by (induction it and t arbitrary: path and path) auto

lemma subrefs_subs:
  "((a, c), p) \<in> set (subrefsItem it path)
     \<Longrightarrow> \<exists>s. (s, p) \<in> set (subsItem it path)
             \<and> subAssumeLine s = a \<and> subLastLine s = c"
  "((a, c), p) \<in> set (subrefsSub t path)
     \<Longrightarrow> \<exists>s. (s, p) \<in> set (subsSub t path)
             \<and> subAssumeLine s = a \<and> subLastLine s = c"
proof (induction it and t arbitrary: path and path)
  case (Subproof a' fa body)
  show ?case
  proof (cases "((a, c), p) = ((a', subLastLine (Subproof a' fa body)), path)")
    case True
    then show ?thesis by (intro exI [of _ "Subproof a' fa body"]) simp
  next
    case False
    with Subproof.prems obtain it'
      where it': "it' \<in> set body"
                 "((a, c), p) \<in> set (subrefsItem it' (path @ [a']))" by auto
    from Subproof.IH [OF it'(1) it'(2)] obtain s
      where "(s, p) \<in> set (subsItem it' (path @ [a']))"
        and "subAssumeLine s = a" and "subLastLine s = c" by blast
    with it'(1) show ?thesis by auto
  qed
qed auto

lemma subs_subrefs_proof:
  assumes "(s, p) \<in> set (subs F)"
  shows "((subAssumeLine s, subLastLine s), p) \<in> set (subrefs F)"
proof -
  from assms obtain it where it: "it \<in> set F" "(s, p) \<in> set (subsItem it [])"
    by (auto simp: subs_def)
  from subs_subrefs(1) [OF it(2)] it(1) show ?thesis by (auto simp: subrefs_def)
qed

lemma subrefs_subs_proof:
  assumes "((a, c), p) \<in> set (subrefs F)"
  shows "\<exists>s. (s, p) \<in> set (subs F) \<and> subAssumeLine s = a \<and> subLastLine s = c"
proof -
  from assms obtain it where it: "it \<in> set F" "((a, c), p) \<in> set (subrefsItem it [])"
    by (auto simp: subrefs_def)
  from subrefs_subs(1) [OF it(2)] obtain s
    where "(s, p) \<in> set (subsItem it [])"
      and "subAssumeLine s = a" and "subLastLine s = c" by blast
  with it(1) show ?thesis by (auto simp: subs_def)
qed

section \<open>Scopes only grow inward\<close>

lemma flat_scope_prefix:
  "fl \<in> set (flatItem it path) \<Longrightarrow> is_prefix path (flScope fl)"
  "fl \<in> set (flatSub t path) \<Longrightarrow> is_prefix path (flScope fl)"
proof (induction it and t arbitrary: path and path)
  case (Subproof a fa body)
  from Subproof.prems consider (asm) "fl = FL a fa FAssume (path @ [a])"
    | (body) it' where "it' \<in> set body" "fl \<in> set (flatItem it' (path @ [a]))"
    by auto
  then show ?case
  proof cases
    case asm then show ?thesis by simp
  next
    case body
    have "is_prefix path (path @ [a])" by simp
    moreover from Subproof.IH [OF body(1) body(2)]
    have "is_prefix (path @ [a]) (flScope fl)" .
    ultimately show ?thesis by (rule is_prefix_trans)
  qed
qed auto

section \<open>A subproof occupies a contiguous block\<close>

lemma concat_map_split:
  assumes "x \<in> set xs"
  shows "\<exists>as bs. concat (map g xs) = as @ g x @ bs"
proof -
  from assms obtain us vs where "xs = us @ x # vs" by (meson split_list)
  then show ?thesis by auto
qed

lemma subs_block:
  "(s, p) \<in> set (subsItem it path)
     \<Longrightarrow> \<exists>as bs. flatItem it path = as @ flatSub s p @ bs"
  "(s, p) \<in> set (subsSub t path)
     \<Longrightarrow> \<exists>as bs. flatSub t path = as @ flatSub s p @ bs"
proof (induction it and t arbitrary: path and path)
  case (Subproof a fa body)
  show ?case
  proof (cases "(s, p) = (Subproof a fa body, path)")
    case True
    then have "flatSub (Subproof a fa body) path = [] @ flatSub s p @ []" by simp
    then show ?thesis by blast
  next
    case False
    with Subproof.prems obtain it'
      where it': "it' \<in> set body" "(s, p) \<in> set (subsItem it' (path @ [a]))" by auto
    from Subproof.IH [OF it'(1) it'(2)] obtain as bs
      where inner: "flatItem it' (path @ [a]) = as @ flatSub s p @ bs" by blast
    from concat_map_split [OF it'(1), of "\<lambda>it. flatItem it (path @ [a])"] obtain A B
      where outer: "concat (map (\<lambda>it. flatItem it (path @ [a])) body)
                      = A @ flatItem it' (path @ [a]) @ B" by blast
    have "flatSub (Subproof a fa body) path
            = (FL a fa FAssume (path @ [a]) # A @ as) @ flatSub s p @ (bs @ B)"
      by (simp add: outer inner)
    then show ?thesis by blast
  qed
qed auto

lemma subs_block_proof:
  assumes "(s, p) \<in> set (subs F)"
  shows "\<exists>as bs. flatten F = as @ flatSub s p @ bs"
proof -
  from assms obtain it where it: "it \<in> set F" "(s, p) \<in> set (subsItem it [])"
    by (auto simp: subs_def)
  from subs_block(1) [OF it(2)] obtain as bs
    where inner: "flatItem it [] = as @ flatSub s p @ bs" by blast
  from concat_map_split [OF it(1), of "\<lambda>it. flatItem it []"] obtain A B
    where outer: "concat (map (\<lambda>it. flatItem it []) F) = A @ flatItem it [] @ B" by blast
  have "flatten F = (A @ as) @ flatSub s p @ (bs @ B)"
    by (simp add: flatten_def outer inner)
  then show ?thesis by blast
qed

section \<open>What the block tells us\<close>

text \<open>A subproof sits at a path extending the level it was found at.\<close>

lemma subs_path_extends:
  "(s, q) \<in> set (subsItem it path) \<Longrightarrow> is_prefix path q"
  "(s, q) \<in> set (subsSub t path) \<Longrightarrow> is_prefix path q"
proof (induction it and t arbitrary: path and path)
  case (Subproof a fa body)
  show ?case
  proof (cases "(s, q) = (Subproof a fa body, path)")
    case True then show ?thesis by simp
  next
    case False
    with Subproof.prems obtain it'
      where it': "it' \<in> set body" "(s, q) \<in> set (subsItem it' (path @ [a]))" by auto
    have "is_prefix path (path @ [a])" by simp
    moreover from Subproof.IH [OF it'(1) it'(2)] have "is_prefix (path @ [a]) q" .
    ultimately show ?thesis by (rule is_prefix_trans)
  qed
qed auto

text \<open>Every line of a subproof's block has the subproof's own path as a prefix of
  its scope --- one level deeper than @{thm [source] flat_scope_prefix} gives.\<close>

lemma flatSub_scope:
  assumes "fl \<in> set (flatSub s p)"
  shows "is_prefix (p @ [subAssumeLine s]) (flScope fl)"
proof (cases s)
  case (Subproof a fa body)
  with assms consider (asm) "fl = FL a fa FAssume (p @ [a])"
    | (body) it' where "it' \<in> set body" "fl \<in> set (flatItem it' (p @ [a]))" by auto
  then show ?thesis
  proof cases
    case asm with Subproof show ?thesis by simp
  next
    case body
    from flat_scope_prefix(1) [OF body(2)] Subproof show ?thesis by simp
  qed
qed

text \<open>The block begins with the assumption line.\<close>

lemma flatSub_hd:
  "flatSub s p = FL (subAssumeLine s) (subAssumeForm s) FAssume (p @ [subAssumeLine s])
                   # concat (map (\<lambda>it. flatItem it (p @ [subAssumeLine s])) (subBody s))"
  by (cases s) simp

lemma subs_assume_mem:
  assumes "(s, q) \<in> set (subsItem it path)"
  shows "subAssumeLine s \<in> set (map flNum (flatItem it path))"
proof -
  from subs_block(1) [OF assms] obtain as bs
    where "flatItem it path = as @ flatSub s q @ bs" by blast
  moreover have "FL (subAssumeLine s) (subAssumeForm s) FAssume (q @ [subAssumeLine s])
                   \<in> set (flatSub s q)"
    by (subst flatSub_hd) simp
  ultimately show ?thesis by force
qed

text \<open>Conversely, if a number occurs in a line's scope beyond the level we are
  looking from, then the line lies in the block of a subproof with that
  assumption line.  This needs no well-formedness: it is how @{const flatSub}
  builds the scope.\<close>

lemma scope_mem_sub:
  "fl \<in> set (flatItem it path) \<Longrightarrow> n \<in> set (flScope fl) \<Longrightarrow> n \<notin> set path \<Longrightarrow>
     \<exists>s q. (s, q) \<in> set (subsItem it path) \<and> subAssumeLine s = n
           \<and> fl \<in> set (flatSub s q)"
  "fl \<in> set (flatSub t path) \<Longrightarrow> n \<in> set (flScope fl) \<Longrightarrow> n \<notin> set path \<Longrightarrow>
     \<exists>s q. (s, q) \<in> set (subsSub t path) \<and> subAssumeLine s = n
           \<and> fl \<in> set (flatSub s q)"
proof (induction it and t arbitrary: path and path)
  case (Subproof a fa body)
  from Subproof.prems(1) consider (asm) "fl = FL a fa FAssume (path @ [a])"
    | (body) it' where "it' \<in> set body" "fl \<in> set (flatItem it' (path @ [a]))" by auto
  then show ?case
  proof cases
    case asm
    with Subproof.prems(2,3) have "n = a" by simp
    with asm show ?thesis by (intro exI [of _ "Subproof a fa body"] exI [of _ path]) simp
  next
    case body
    show ?thesis
    proof (cases "n = a")
      case True
      from body have "fl \<in> set (flatSub (Subproof a fa body) path)" by auto
      with True show ?thesis
        by (intro exI [of _ "Subproof a fa body"] exI [of _ path]) simp
    next
      case False
      with Subproof.prems(3) have "n \<notin> set (path @ [a])" by simp
      from Subproof.IH [OF body(1) body(2) Subproof.prems(2) this] body(1)
      show ?thesis by auto
    qed
  qed
qed auto

lemma scope_mem_sub_proof:
  assumes "fl \<in> set (flatten F)" and "n \<in> set (flScope fl)"
  shows "\<exists>s q. (s, q) \<in> set (subs F) \<and> subAssumeLine s = n
           \<and> fl \<in> set (flatSub s q)"
proof -
  from assms(1) obtain it where it: "it \<in> set F" "fl \<in> set (flatItem it [])"
    by (auto simp: flatten_def)
  from scope_mem_sub(1) [OF it(2) assms(2)] obtain s q
    where "(s, q) \<in> set (subsItem it [])" "subAssumeLine s = n"
      "fl \<in> set (flatSub s q)" by auto
  with it(1) show ?thesis by (auto simp: subs_def)
qed

section \<open>A subproof is determined by its assumption line\<close>

lemma distinct_concat_part:
  assumes "distinct (concat (map h xs))" and "x \<in> set xs"
  shows "distinct (h x)"
proof -
  from assms(2) obtain A B where "xs = A @ x # B" by (meson split_list)
  with assms(1) show ?thesis by auto
qed

lemma distinct_concat_parts:
  assumes d: "distinct (concat (map h xs))"
      and x: "x \<in> set xs" and y: "y \<in> set xs" and xy: "x \<noteq> y"
  shows "set (h x) \<inter> set (h y) = {}"
proof -
  from x obtain A B where xs: "xs = A @ x # B" by (meson split_list)
  from y xy xs have "y \<in> set A \<union> set B" by auto
  moreover from d xs
  have "set (h x) \<inter> set (concat (map h A)) = {}"
   and "set (h x) \<inter> set (concat (map h B)) = {}" by auto
  ultimately show ?thesis by auto
qed

text \<open>Two subproofs of the same proof with the same assumption line are the same
  subproof, sitting at the same level.  The reason is that a subproof's block
  begins with its assumption line, so two of them would put one line number in
  two places, and a well-formed Fitch proof numbers its lines distinctly.\<close>

lemma subs_unique:
  "(s, q) \<in> set (subsItem it path) \<Longrightarrow> (s', q') \<in> set (subsItem it path) \<Longrightarrow>
     distinct (map flNum (flatItem it path)) \<Longrightarrow>
     subAssumeLine s = subAssumeLine s' \<Longrightarrow> s = s' \<and> q = q'"
  "(s, q) \<in> set (subsSub t path) \<Longrightarrow> (s', q') \<in> set (subsSub t path) \<Longrightarrow>
     distinct (map flNum (flatSub t path)) \<Longrightarrow>
     subAssumeLine s = subAssumeLine s' \<Longrightarrow> s = s' \<and> q = q'"
proof (induction it and t arbitrary: path and path)
  case (Subproof a fa body)
  let ?h = "\<lambda>it. map flNum (flatItem it (path @ [a]))"
  from Subproof.prems(3)
  have D: "distinct (a # concat (map ?h body))"
    by (simp add: map_concat comp_def)
  then have aC: "a \<notin> set (concat (map ?h body))"
       and dC: "distinct (concat (map ?h body))" by simp_all
  have inner: "subAssumeLine u \<in> set (?h it')"
    if "it' \<in> set body" "(u, r) \<in> set (subsItem it' (path @ [a]))" for u r it'
    using subs_assume_mem [OF that(2)] by simp
  have notHead: False
    if "subAssumeLine u = a" "it' \<in> set body" "(u, r) \<in> set (subsItem it' (path @ [a]))"
    for u r it'
  proof -
    from inner [OF that(2,3)] that(1) have "a \<in> set (?h it')" by simp
    with that(2) have "a \<in> set (concat (map ?h body))" by auto
    with aC show False by simp
  qed
  consider (hh) "(s, q) = (Subproof a fa body, path)" "(s', q') = (Subproof a fa body, path)"
    | (hi) it' r where "(s, q) = (Subproof a fa body, path)"
                      "it' \<in> set body" "(s', q') \<in> set (subsItem it' (path @ [a]))" "r = it'"
    | (ih) it' r where "(s', q') = (Subproof a fa body, path)"
                      "it' \<in> set body" "(s, q) \<in> set (subsItem it' (path @ [a]))" "r = it'"
    | (ii) it1 it2 where "it1 \<in> set body" "(s, q) \<in> set (subsItem it1 (path @ [a]))"
                        "it2 \<in> set body" "(s', q') \<in> set (subsItem it2 (path @ [a]))"
    using Subproof.prems(1,2) by auto
  then show ?case
  proof cases
    case hh then show ?thesis by simp
  next
    case hi
    from hi(1) Subproof.prems(4) have "subAssumeLine s' = a" by simp
    from notHead [OF this hi(2) hi(3)] show ?thesis by simp
  next
    case ih
    from ih(1) Subproof.prems(4) have "subAssumeLine s = a" by simp
    from notHead [OF this ih(2) ih(3)] show ?thesis by simp
  next
    case ii
    show ?thesis
    proof (cases "it1 = it2")
      case True
      have "distinct (?h it1)" using distinct_concat_part [OF dC ii(1)] .
      then have "distinct (map flNum (flatItem it1 (path @ [a])))" by simp
      from Subproof.IH [OF ii(1) ii(2) _ this Subproof.prems(4)] ii(4) True
      show ?thesis by simp
    next
      case False
      from distinct_concat_parts [OF dC ii(1) ii(3) False]
      have disj: "set (?h it1) \<inter> set (?h it2) = {}" .
      from inner [OF ii(1) ii(2)] have "subAssumeLine s \<in> set (?h it1)" .
      moreover from inner [OF ii(3) ii(4)] have "subAssumeLine s' \<in> set (?h it2)" .
      ultimately show ?thesis using disj Subproof.prems(4) by auto
    qed
  qed
qed auto

lemma subs_unique_proof:
  assumes wf: "distinct (map flNum (flatten F))"
      and A: "(s, q) \<in> set (subs F)" and B: "(s', q') \<in> set (subs F)"
      and eq: "subAssumeLine s = subAssumeLine s'"
  shows "s = s' \<and> q = q'"
proof -
  let ?h = "\<lambda>it. map flNum (flatItem it [])"
  from wf have dC: "distinct (concat (map ?h F))"
    by (simp add: flatten_def map_concat comp_def)
  from A obtain it1 where it1: "it1 \<in> set F" "(s, q) \<in> set (subsItem it1 [])"
    by (auto simp: subs_def)
  from B obtain it2 where it2: "it2 \<in> set F" "(s', q') \<in> set (subsItem it2 [])"
    by (auto simp: subs_def)
  show ?thesis
  proof (cases "it1 = it2")
    case True
    from distinct_concat_part [OF dC it1(1)] have "distinct (map flNum (flatItem it1 []))"
      by simp
    from subs_unique(1) [OF it1(2) _ this eq] it2(2) True show ?thesis by simp
  next
    case False
    from distinct_concat_parts [OF dC it1(1) it2(1) False]
    have disj: "set (?h it1) \<inter> set (?h it2) = {}" .
    from subs_assume_mem [OF it1(2)] have "subAssumeLine s \<in> set (?h it1)" by simp
    moreover from subs_assume_mem [OF it2(2)] have "subAssumeLine s' \<in> set (?h it2)" by simp
    ultimately show ?thesis using disj eq by auto
  qed
qed

lemma subs_lastIsLine:
  "(s, q) \<in> set (subsItem it path) \<Longrightarrow> lastIsLineItem it \<Longrightarrow> lastIsLineSub s"
  "(s, q) \<in> set (subsSub t path) \<Longrightarrow> lastIsLineSub t \<Longrightarrow> lastIsLineSub s"
  by (induction it and t arbitrary: path and path) (auto simp: list_all_iff)

lemma subs_lastIsLine_proof:
  "(s, q) \<in> set (subs F) \<Longrightarrow> fitchWF F \<Longrightarrow> lastIsLineSub s"
  by (auto simp: subs_def fitchWF_def list_all_iff dest: subs_lastIsLine(1))

section \<open>The span of a subproof\<close>

lemma sorted_wrt_less_hd: "sorted_wrt (<) xs \<Longrightarrow> y \<in> set xs \<Longrightarrow> hd xs \<le> (y :: nat)"
  by (cases xs) auto

lemma sorted_wrt_less_last: "sorted_wrt (<) xs \<Longrightarrow> y \<in> set xs \<Longrightarrow> y \<le> (last xs :: nat)"
proof (induction xs)
  case Nil then show ?case by simp
next
  case (Cons x xs)
  show ?case
  proof (cases "xs = []")
    case True with Cons.prems show ?thesis by simp
  next
    case False
    then have L: "last (x # xs) = last xs" by simp
    from False have M: "last xs \<in> set xs" by simp
    show ?thesis
    proof (cases "y = x")
      case True
      from Cons.prems(1) M have "x < last xs" by auto
      with True L show ?thesis by simp
    next
      case False
      with Cons.prems(2) have ym: "y \<in> set xs" by simp
      from Cons.prems(1) have "sorted_wrt (<) xs" by simp
      from Cons.IH [OF this ym] L show ?thesis by simp
    qed
  qed
qed

text \<open>The theorem the development was missing.  A line of a well-formed Fitch
  proof lies inside a given subproof exactly when its number lies between the
  subproof's assumption line and its last line.  Half of it is that the block is
  contiguous and the numbers increase; the other half is that a number in a
  line's scope names the subproof it is in, and that subproof is unique.\<close>

theorem subs_span_structural:
  assumes srt: "sorted_wrt (<) (map flNum (flatten F))"
      and last: "list_all lastIsLineItem F"
      and sp: "(s, p) \<in> set (subs F)" and fl: "fl \<in> set (flatten F)"
  shows "is_prefix (p @ [subAssumeLine s]) (flScope fl)
           \<longleftrightarrow> subAssumeLine s \<le> flNum fl \<and> flNum fl \<le> subLastLine s"
proof -
  let ?a = "subAssumeLine s" and ?c = "subLastLine s"
  from sp last have lil: "lastIsLineSub s"
    by (auto simp: subs_def list_all_iff dest: subs_lastIsLine(1))
  from srt have dist: "distinct (map flNum (flatten F))"
    by (rule sorted_wrt_less_distinct)
  from subs_block_proof [OF sp] obtain as bs
    where split: "flatten F = as @ flatSub s p @ bs" by blast
  have hdblk: "hd (map flNum (flatSub s p)) = ?a" by (subst flatSub_hd) simp
  obtain sa sfa sbody where sdef: "s = Subproof sa sfa sbody" by (cases s)
  with lil have lil': "lastIsLineSub (Subproof sa sfa sbody)" by simp
  from subLastLine_last [OF lil', of p] obtain f r
    where lastblk: "last (flatSub s p) = FL ?c f r (p @ [?a])"
    using sdef by auto
  have blkne: "flatSub s p \<noteq> []" by simp
  have mlast: "last (map flNum (flatSub s p)) = ?c"
    using blkne lastblk by (simp add: last_map)
  from srt split have S: "sorted_wrt (<) (map flNum as @ map flNum (flatSub s p) @ map flNum bs)"
    by simp
  from S have S1: "\<forall>x \<in> set (map flNum as).
                     \<forall>y \<in> set (map flNum (flatSub s p) @ map flNum bs). x < y"
    by (simp add: sorted_wrt_append)
  from S have S2: "sorted_wrt (<) (map flNum (flatSub s p) @ map flNum bs)"
    by (simp add: sorted_wrt_append)
  from S2 have S3: "\<forall>x \<in> set (map flNum (flatSub s p)). \<forall>y \<in> set (map flNum bs). x < y"
    by (simp add: sorted_wrt_append)
  from S2 have sb: "sorted_wrt (<) (map flNum (flatSub s p))"
    by (simp add: sorted_wrt_append)
  have mne: "map flNum (flatSub s p) \<noteq> []" using blkne by simp
  have ain: "?a \<in> set (map flNum (flatSub s p))"
  proof -
    from mne have "hd (map flNum (flatSub s p)) \<in> set (map flNum (flatSub s p))"
      by (rule hd_in_set)
    with hdblk show ?thesis by simp
  qed
  have cin: "?c \<in> set (map flNum (flatSub s p))"
  proof -
    from mne have "last (map flNum (flatSub s p)) \<in> set (map flNum (flatSub s p))"
      by (rule last_in_set)
    with mlast show ?thesis by simp
  qed
  \<comment> \<open>inside the block the numbers run from the assumption line to the last line\<close>
  have inblk: "?a \<le> flNum g \<and> flNum g \<le> ?c" if "g \<in> set (flatSub s p)" for g
  proof -
    from that have m: "flNum g \<in> set (map flNum (flatSub s p))" by simp
    from sorted_wrt_less_hd [OF sb m] hdblk have "?a \<le> flNum g" by simp
    moreover from sorted_wrt_less_last [OF sb m] mlast have "flNum g \<le> ?c" by simp
    ultimately show ?thesis by simp
  qed
  \<comment> \<open>and everything outside it lies strictly outside that range\<close>
  have outas: "flNum g < ?a" if "g \<in> set as" for g
  proof -
    from that have "flNum g \<in> set (map flNum as)" by simp
    moreover from ain have "?a \<in> set (map flNum (flatSub s p) @ map flNum bs)" by simp
    ultimately show ?thesis using S1 by blast
  qed
  have outbs: "?c < flNum g" if "g \<in> set bs" for g
  proof -
    from that have "flNum g \<in> set (map flNum bs)" by simp
    with cin S3 show ?thesis by blast
  qed
  have memblk: "fl \<in> set (flatSub s p) \<longleftrightarrow> ?a \<le> flNum fl \<and> flNum fl \<le> ?c"
  proof
    assume "fl \<in> set (flatSub s p)" then show "?a \<le> flNum fl \<and> flNum fl \<le> ?c"
      by (rule inblk)
  next
    assume R: "?a \<le> flNum fl \<and> flNum fl \<le> ?c"
    from fl split have "fl \<in> set as \<union> set (flatSub s p) \<union> set bs" by auto
    moreover from R outas have "fl \<notin> set as" by force
    moreover from R outbs have "fl \<notin> set bs" by force
    ultimately show "fl \<in> set (flatSub s p)" by blast
  qed
  show ?thesis
  proof
    assume pref: "is_prefix (p @ [?a]) (flScope fl)"
    from is_prefix_set [OF pref] have "set (p @ [?a]) \<subseteq> set (flScope fl)" .
    then have "?a \<in> set (flScope fl)" by auto
    from fl obtain it where it: "it \<in> set F" "fl \<in> set (flatItem it [])"
      by (auto simp: flatten_def)
    from scope_mem_sub(1) [OF it(2) \<open>?a \<in> set (flScope fl)\<close>] obtain s' q'
      where s': "(s', q') \<in> set (subsItem it [])" "subAssumeLine s' = ?a"
                "fl \<in> set (flatSub s' q')" by auto
    from it(1) s'(1) have "(s', q') \<in> set (subs F)" by (auto simp: subs_def)
    from subs_unique_proof [OF dist this sp] s'(2) have "s' = s \<and> q' = p" by simp
    with s'(3) have "fl \<in> set (flatSub s p)" by simp
    with memblk show "?a \<le> flNum fl \<and> flNum fl \<le> ?c" by simp
  next
    assume "?a \<le> flNum fl \<and> flNum fl \<le> ?c"
    with memblk have "fl \<in> set (flatSub s p)" by simp
    then show "is_prefix (p @ [?a]) (flScope fl)" by (rule flatSub_scope)
  qed
qed

theorem subs_span:
  assumes wf: "fitchWF F" and sp: "(s, p) \<in> set (subs F)" and fl: "fl \<in> set (flatten F)"
  shows "is_prefix (p @ [subAssumeLine s]) (flScope fl)
           \<longleftrightarrow> subAssumeLine s \<le> flNum fl \<and> flNum fl \<le> subLastLine s"
proof -
  from wf have srt: "sorted_wrt (<) (map flNum (flatten F))"
    and last: "list_all lastIsLineItem F" by (simp_all add: fitchWF_def)
  from subs_span_structural [OF srt last sp fl] show ?thesis .
qed

end
