(* T4: Theorem 10 at the exact HL types. *)

theory LF_HLW_Theorem10
  imports LF_HLW_Examples LF_HLW_Conclusion
begin

section \<open>The spans of the boxes of a Fitch proof\<close>

text \<open>A discharging rule cites a pair of line numbers. \<^const>\<open>hlFitchNestingFrom\<close>
  admits such a citation only when the pair is a box that has already closed at
  the citing line's own level, so the pair is a genuine box of the proof.\<close>

fun hlBoxSpans :: "hl_fitch_proof \<Rightarrow> hl_subproof_reference set" where
  "hlBoxSpans [] = {}"
| "hlBoxSpans (HL_FLine n p r # rest) = hlBoxSpans rest"
| "hlBoxSpans (HL_FSub (HL_Subproof a p body) # rest) =
     insert (a,hlSubLastLine (HL_Subproof a p body))
       (hlBoxSpans body \<union> hlBoxSpans rest)"

lemma hlFitchNestingFrom_citedSubs:
  "hlFitchNestingFrom depth visible boxes F \<Longrightarrow>
   t \<in> set (hlFlattenFitch F) \<Longrightarrow>
   set (hlFitchCitedSubs (snd (snd t))) \<subseteq> boxes \<union> hlBoxSpans F"
proof (induction F arbitrary: depth visible boxes rule: hlBoxSpans.induct)
  case 1
  then show ?case by simp
next
  case (2 n p r rest)
  then show ?case by fastforce
next
  case (3 a p body rest)
  from 3(3) have body_ok: "hlFitchNestingFrom (Suc depth) (insert a visible) {} body"
    and rest_ok: "hlFitchNestingFrom depth visible
      (insert (a,hlSubLastLine (HL_Subproof a p body)) boxes) rest" by simp_all
  from 3(4) consider "t = (a,p,HL_FAssume)" | "t \<in> set (hlFlattenFitch body)"
    | "t \<in> set (hlFlattenFitch rest)" by (auto simp: hlFlattenFitch_append)
  then show ?case
  proof cases
    case 1
    then show ?thesis by simp
  next
    case 2
    from 3(1)[OF body_ok 2] show ?thesis by auto
  next
    case 3
    from "3.IH"(2)[OF rest_ok 3] show ?thesis by auto
  qed
qed

section \<open>A box occupies a contiguous block of the line numbers\<close>

lemma hlFitchLineNumbers_append [simp]:
  "hlFitchLineNumbers (F @ G) = hlFitchLineNumbers F @ hlFitchLineNumbers G"
  by (induction F) simp_all

lemma hlBoxSpans_segment:
  "(a,c) \<in> hlBoxSpans F \<Longrightarrow>
   \<exists>pre B post. hlFitchLineNumbers F = pre @ (a # B) @ post \<and> c = last (a # B)"
proof (induction F rule: hlBoxSpans.induct)
  case 1
  then show ?case by simp
next
  case (2 n p r rest)
  from "2.prems" have "(a,c) \<in> hlBoxSpans rest" by simp
  from "2.IH"[OF this] obtain pre B post where
    p: "hlFitchLineNumbers rest = pre @ (a # B) @ post" and c: "c = last (a # B)" by blast
  have "hlFitchLineNumbers (HL_FLine n p r # rest) = (n # pre) @ (a # B) @ post"
    using p by simp
  then show ?case using c by blast
next
  case (3 b q body rest)
  from "3.prems" consider
      "(a,c) = (b,hlSubLastLine (HL_Subproof b q body))"
    | "(a,c) \<in> hlBoxSpans body" | "(a,c) \<in> hlBoxSpans rest" by auto
  then show ?case
  proof cases
    case 1
    then have a: "a = b" and c: "c = hlSubLastLine (HL_Subproof b q body)" by simp_all
    have seg: "hlFitchLineNumbers (HL_FSub (HL_Subproof b q body) # rest)
               = [] @ (b # hlFitchLineNumbers body) @ hlFitchLineNumbers rest" by simp
    have "c = last (b # hlFitchLineNumbers body)"
      using c by (cases "hlFitchLineNumbers body = []") simp_all
    then show ?thesis using seg a by blast
  next
    case 2
    from "3.IH"(1)[OF 2] obtain pre B post where
      p: "hlFitchLineNumbers body = pre @ (a # B) @ post" and c: "c = last (a # B)" by blast
    have "hlFitchLineNumbers (HL_FSub (HL_Subproof b q body) # rest)
          = (b # pre) @ (a # B) @ (post @ hlFitchLineNumbers rest)" using p by simp
    then show ?thesis using c by blast
  next
    case 3
    from "3.IH"(2)[OF 3] obtain pre B post where
      p: "hlFitchLineNumbers rest = pre @ (a # B) @ post" and c: "c = last (a # B)" by blast
    have "hlFitchLineNumbers (HL_FSub (HL_Subproof b q body) # rest)
          = ((b # hlFitchLineNumbers body) @ pre) @ (a # B) @ post" using p by simp
    then show ?thesis using c by blast
  qed
qed

section \<open>Boxes nest, so their spans never cross\<close>

lemma hlBoxSpans_mem:
  "(a,c) \<in> hlBoxSpans F \<Longrightarrow>
   a \<in> set (hlFitchLineNumbers F) \<and> c \<in> set (hlFitchLineNumbers F)"
proof (induction F rule: hlBoxSpans.induct)
  case 1
  then show ?case by simp
next
  case (2 n p r rest)
  then show ?case by auto
next
  case (3 b q body rest)
  from "3.prems" consider
      "(a,c) = (b,hlSubLastLine (HL_Subproof b q body))"
    | "(a,c) \<in> hlBoxSpans body" | "(a,c) \<in> hlBoxSpans rest" by auto
  then show ?case
  proof cases
    case 1
    then show ?thesis
      by (cases "hlFitchLineNumbers body = []") auto
  next
    case 2
    from "3.IH"(1)[OF 2] show ?thesis by auto
  next
    case 3
    from "3.IH"(2)[OF 3] show ?thesis by auto
  qed
qed

lemma sorted_wrt_less_le_last:
  "sorted_wrt (<) xs \<Longrightarrow> x \<in> set xs \<Longrightarrow> x \<le> last (xs :: 'a :: linorder list)"
proof (induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  show ?case
  proof (cases "xs = []")
    case True
    then show ?thesis using Cons.prems by simp
  next
    case ne: False
    show ?thesis
    proof (cases "x = a")
      case True
      have "a < last xs" using Cons.prems(1) ne last_in_set by auto
      then show ?thesis using True ne by simp
    next
      case False
      then have "x \<in> set xs" using Cons.prems(2) by simp
      then show ?thesis using Cons.IH Cons.prems(1) ne by simp
    qed
  qed
qed

lemma hlBoxSpans_nested:
  "sorted_wrt (<) (hlFitchLineNumbers F) \<Longrightarrow>
   (a,c) \<in> hlBoxSpans F \<Longrightarrow> (a',c') \<in> hlBoxSpans F \<Longrightarrow>
   a < a' \<Longrightarrow> a' \<le> c \<Longrightarrow> c' \<le> c"
proof (induction F arbitrary: a c a' c' rule: hlBoxSpans.induct)
  case 1
  then show ?case by simp
next
  case (2 n p r rest)
  then show ?case by auto
next
  case (3 b q body rest)
  let ?sub = "HL_Subproof b q body"
  have nums: "hlFitchLineNumbers (HL_FSub ?sub # rest)
              = (b # hlFitchLineNumbers body) @ hlFitchLineNumbers rest" by simp
  from "3.prems"(1) nums have
    sortB: "sorted_wrt (<) (hlFitchLineNumbers body)"
    and sortR: "sorted_wrt (<) (hlFitchLineNumbers rest)"
    and bodyR: "\<forall>x \<in> set (b # hlFitchLineNumbers body).
                  \<forall>y \<in> set (hlFitchLineNumbers rest). x < y"
    and bbody: "\<forall>x \<in> set (hlFitchLineNumbers body). b < x"
    by (auto simp: sorted_wrt_append)
  have lastb: "hlSubLastLine ?sub \<in> set (b # hlFitchLineNumbers body)"
    by (cases "hlFitchLineNumbers body = []") auto
  from "3.prems"(2) consider
      "(a,c) = (b,hlSubLastLine ?sub)"
    | "(a,c) \<in> hlBoxSpans body" | "(a,c) \<in> hlBoxSpans rest" by auto
  then show ?case
  proof cases
    case A: 1
    from "3.prems"(3) consider
        "(a',c') = (b,hlSubLastLine ?sub)"
      | "(a',c') \<in> hlBoxSpans body" | "(a',c') \<in> hlBoxSpans rest" by auto
    then show ?thesis
    proof cases
      case 1
      then show ?thesis using A "3.prems"(4) by simp
    next
      case 2
      from hlBoxSpans_mem[OF 2] have "c' \<in> set (hlFitchLineNumbers body)" by simp
      moreover have "hlSubLastLine ?sub = last (hlFitchLineNumbers body)"
        using 2 hlBoxSpans_mem[OF 2] by (cases "hlFitchLineNumbers body = []") auto
      ultimately show ?thesis
        using A sorted_wrt_less_le_last[OF sortB] by simp
    next
      case 3
      from hlBoxSpans_mem[OF 3] have "a' \<in> set (hlFitchLineNumbers rest)" by simp
      with bodyR lastb A "3.prems"(5) show ?thesis by fastforce
    qed
  next
    case B: 2
    from "3.prems"(3) consider
        "(a',c') = (b,hlSubLastLine ?sub)"
      | "(a',c') \<in> hlBoxSpans body" | "(a',c') \<in> hlBoxSpans rest" by auto
    then show ?thesis
    proof cases
      case 1
      from hlBoxSpans_mem[OF B] bbody have "b < a" by simp
      then show ?thesis using 1 "3.prems"(4) by simp
    next
      case 2
      show ?thesis
        by (rule "3.IH"(1)[OF sortB B 2 "3.prems"(4) "3.prems"(5)])
    next
      case 3
      from hlBoxSpans_mem[OF B] have "c \<in> set (hlFitchLineNumbers body)" by simp
      moreover from hlBoxSpans_mem[OF 3] have "a' \<in> set (hlFitchLineNumbers rest)" by simp
      ultimately show ?thesis using bodyR "3.prems"(5) by fastforce
    qed
  next
    case C: 3
    from "3.prems"(3) consider
        "(a',c') = (b,hlSubLastLine ?sub)"
      | "(a',c') \<in> hlBoxSpans body" | "(a',c') \<in> hlBoxSpans rest" by auto
    then show ?thesis
    proof cases
      case 1
      from hlBoxSpans_mem[OF C] have "a \<in> set (hlFitchLineNumbers rest)" by simp
      with bodyR have "b < a" by simp
      then show ?thesis using 1 "3.prems"(4) by simp
    next
      case 2
      from hlBoxSpans_mem[OF C] have "a \<in> set (hlFitchLineNumbers rest)" by simp
      moreover from hlBoxSpans_mem[OF 2] have "a' \<in> set (hlFitchLineNumbers body)" by simp
      ultimately show ?thesis using bodyR "3.prems"(4) by fastforce
    next
      case 3
      show ?thesis
        by (rule "3.IH"(2)[OF sortR C 3 "3.prems"(4) "3.prems"(5)])
    qed
  qed
qed

section \<open>Fitch images at the exact types\<close>

text \<open>A Fitch line images a Lemmon line when it carries the same number, the
  same formula, and the rule that erases to that line's justification.  This is
  the exact counterpart of the compact \<open>lineMatches\<close>: there the correspondence
  is written Lemmon-to-Fitch, here Fitch-to-Lemmon, and \<^const>\<open>hlToLemmonRule\<close>
  is the map the erasure already uses.\<close>

definition hlLineMatches ::
    "int \<times> hl_formula \<times> hl_fitch_rule \<Rightarrow> hl_line \<Rightarrow> bool" where
  "hlLineMatches t l \<longleftrightarrow>
     fst t = hlLineNumber l \<and> fst (snd t) = hlFormula l \<and>
     hlToLemmonRule (snd (snd t)) = hlJustification l"

definition hlFitchImage :: "hl_fitch_proof \<Rightarrow> hl_proof \<Rightarrow> bool" where
  "hlFitchImage F P \<longleftrightarrow>
     (\<forall>l \<in> set P. \<exists>t \<in> set (hlFlattenFitch F). hlLineMatches t l) \<and>
     (\<forall>t \<in> set (hlFlattenFitch F). \<exists>l \<in> set P. hlLineMatches t l)"

lemma hlToLemmonRule_CP_inv:
  "hlToLemmonRule r = HL_CP a c \<Longrightarrow> r = HL_FCP (a,c)"
  by (cases r) auto

text \<open>A conditional proof in an imaged source forces a genuine box: the image
  line carries \<^term>\<open>HL_FCP (a,c)\<close>, and nesting admits that citation only when
  the pair is a box that has closed at the citing line's own level.\<close>

lemma hlFitchImage_CP_box:
  assumes nest: "hlFitchNestingFrom 0 {} {} F"
      and img: "hlFitchImage F P"
      and l: "l \<in> set P"
      and j: "hlJustification l = HL_CP a c"
  shows "(a,c) \<in> hlBoxSpans F"
proof -
  from img l obtain t where t: "t \<in> set (hlFlattenFitch F)"
    and m: "hlLineMatches t l" by (auto simp: hlFitchImage_def)
  from m j have "hlToLemmonRule (snd (snd t)) = HL_CP a c"
    by (simp add: hlLineMatches_def)
  from hlToLemmonRule_CP_inv[OF this] have r: "snd (snd t) = HL_FCP (a,c)" .
  have "set (hlFitchCitedSubs (snd (snd t))) \<subseteq> {} \<union> hlBoxSpans F"
    by (rule hlFitchNestingFrom_citedSubs[OF nest t])
  then show ?thesis using r by simp
qed

section \<open>Theorem 10 at the exact types\<close>

text \<open>Example 11 makes assumption 1 first and discharges it first.  An image
  would need a box spanning lines 1 to 3 and another spanning 2 to 4.  The
  second starts inside the first and ends outside it, and boxes nest.\<close>

theorem hl_theorem_10_ex11:
  "\<not> (\<exists>F. hlFitchNestedWellFormed F \<and> hlFitchImage F hl_ex11)"
proof (rule notI, elim exE conjE)
  fix F assume wf: "hlFitchNestedWellFormed F" and img: "hlFitchImage F hl_ex11"
  have nest: "hlFitchNestingFrom 0 {} {} F"
    and sorted: "sorted_wrt (<) (hlFitchLineNumbers F)"
    using wf by (simp_all add: hlFitchNestedWellFormed_def)
  have l4: "HL_ProofLine 4 (hlP \<longrightarrow>\<^sub>H (hlP \<and>\<^sub>H hlQ)) (HL_CP 1 3) {2} \<in> set hl_ex11"
    by (simp add: hl_ex11_def)
  have l5: "HL_ProofLine 5 (hlQ \<longrightarrow>\<^sub>H (hlP \<longrightarrow>\<^sub>H (hlP \<and>\<^sub>H hlQ))) (HL_CP 2 4) {} \<in> set hl_ex11"
    by (simp add: hl_ex11_def)
  from hlFitchImage_CP_box[OF nest img l4] have b1: "(1,3) \<in> hlBoxSpans F" by simp
  from hlFitchImage_CP_box[OF nest img l5] have b2: "(2,4) \<in> hlBoxSpans F" by simp
  from hlBoxSpans_nested[OF sorted b1 b2] show False by simp
qed

end
