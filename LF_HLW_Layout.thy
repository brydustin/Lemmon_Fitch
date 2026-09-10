(* Structural invariants of the exact derivation-to-Fitch emitter. *)

theory LF_HLW_Layout
  imports LF_HLW_Renaming
begin

section \<open>Fresh consecutive allocation\<close>

lemma hlFitchLineNumbers_append [simp]:
  "hlFitchLineNumbers (F @ G) = hlFitchLineNumbers F @ hlFitchLineNumbers G"
  by (induction F) simp_all

lemma hlFitchPremises_append [simp]:
  "hlFitchPremises (F @ G) = hlFitchPremises F @ hlFitchPremises G"
  by (induction F) (auto, rename_tac a F, case_tac a, auto)

text \<open>An emitted fragment allocates exactly the interval from its initial
  counter up to, but excluding, its final counter. This numerical invariant
  makes no claim about the logical correctness of its formulas.\<close>

definition hlAllocated :: "int \<Rightarrow> hl_fitch_proof \<Rightarrow> int \<Rightarrow> bool" where
  "hlAllocated first F after \<longleftrightarrow>
     first \<le> after \<and> hlFitchLineNumbers F = [first..after - 1]"

lemma hlAllocated_empty [simp]: "hlAllocated first [] first"
  by (simp add: hlAllocated_def)

lemma hlAllocated_Nil_iff [simp]: "hlAllocated first [] after \<longleftrightarrow> after = first"
  by (auto simp: hlAllocated_def)

lemma hlAllocated_line [simp]:
  "hlAllocated first [HL_FLine first p r] (first + 1)"
  by (simp add: hlAllocated_def)

lemma hlAllocated_append:
  assumes "hlAllocated first F middle" "hlAllocated middle G after"
  shows "hlAllocated first (F @ G) after"
proof -
  have bounds: "first \<le> middle" "middle \<le> after"
    using assms by (auto simp: hlAllocated_def)
  have interval: "[first..middle - 1] @ [middle..after - 1] = [first..after - 1]"
  proof (cases "middle = after")
    case True
    then show ?thesis by simp
  next
    case False
    have "middle \<le> after - 1" using False bounds(2) by linarith
    from upto_split1[OF bounds(1) this] show ?thesis by simp
  qed
  from assms bounds interval show ?thesis
    by (auto simp: hlAllocated_def intro: order_trans)
qed

lemma hlAllocated_subproof:
  assumes "hlAllocated (first + 1) body after"
  shows "hlAllocated first [HL_FSub (HL_Subproof first p body)] after"
  using assms by (auto simp: hlAllocated_def upto_rec1)

lemma hlAllocated_sorted:
  "hlAllocated first F after \<Longrightarrow> sorted_wrt (<) (hlFitchLineNumbers F)"
  by (simp add: hlAllocated_def)

lemma hlAllocated_range:
  "hlAllocated first F after \<Longrightarrow>
   n \<in> set (hlFitchLineNumbers F) \<Longrightarrow> first \<le> n \<and> n < after"
  by (auto simp: hlAllocated_def)

lemma hlAllocated_empty_iff:
  "hlAllocated first F after \<Longrightarrow>
   (hlFitchLineNumbers F = []) = (after = first)"
  by (auto simp: hlAllocated_def)

lemma hlAllocated_snoc:
  "hlAllocated first F after \<Longrightarrow>
   hlAllocated first (F @ [HL_FLine after p r]) (after + 1)"
  by (erule hlAllocated_append) (rule hlAllocated_line)

lemma hlAllocated_cons_subproof:
  assumes "hlAllocated (first + 1) body middle" "hlAllocated middle rest after"
  shows "hlAllocated first (HL_FSub (HL_Subproof first p body) # rest) after"
  using hlAllocated_append[OF hlAllocated_subproof[OF assms(1)] assms(2)] by simp

lemma hlAllocated_box_and_line:
  "hlAllocated (first + 1) body after \<Longrightarrow>
   hlAllocated first [HL_FSub (HL_Subproof first p body),HL_FLine after q r] (after + 1)"
  using hlAllocated_snoc[OF hlAllocated_subproof] by simp

lemma hlAllocated_line_end:
  "after = first + 1 \<Longrightarrow> hlAllocated first [HL_FLine first p r] after"
  by (simp add: hlAllocated_def)

lemma hlAllocated_snoc_end:
  "hlAllocated first F middle \<Longrightarrow> after = middle + 1 \<Longrightarrow>
   hlAllocated first (F @ [HL_FLine middle p r]) after"
  using hlAllocated_snoc by blast

lemma hlAllocated_box_and_line_end:
  "hlAllocated (first + 1) body middle \<Longrightarrow> after = middle + 1 \<Longrightarrow>
   hlAllocated first [HL_FSub (HL_Subproof first p body),HL_FLine middle q r] after"
  using hlAllocated_box_and_line by blast

lemma hlAllocated_two_boxes_and_line_end:
  assumes "hlAllocated (first + 1) body1 middle"
    "hlAllocated (middle + 1) body2 finish" "after = finish + 1"
  shows "hlAllocated first
    [HL_FSub (HL_Subproof first p body1),HL_FSub (HL_Subproof middle q body2),
     HL_FLine finish r j] after"
  by (rule hlAllocated_cons_subproof[OF assms(1)])
     (rule hlAllocated_box_and_line_end[OF assms(2,3)])

lemma hlAllocated_reiteration [simp]:
  "hlAllocated (first + 1) [HL_FLine (first + 1) p r] (2 + first)"
  by (simp add: hlAllocated_def add.commute)

lemma hlAllocated_reiterated_box [simp]:
  "hlAllocated first
    [HL_FSub (HL_Subproof first p [HL_FLine (first + 1) q r]),
     HL_FLine (2 + first) s t] (3 + first)"
  by (simp add: hlAllocated_def upto_rec1 add.commute)

lemma hlAllocated_emit_list:
  assumes emitted: "hlEmitDerivationsUsing emit first count ds = (items,ns,after,count')"
      and each: "\<And>d first count items n after count'. d \<in> set ds \<Longrightarrow>
        emit first count d = (items,n,after,count') \<Longrightarrow> hlAllocated first items after"
  shows "hlAllocated first items after"
  using emitted each
proof (induction ds arbitrary: first count items ns after count')
  case Nil
  then show ?case by simp
next
  case (Cons d ds)
  from Cons.prems(1) obtain front n middle count1 rest ks where
    front: "emit first count d = (front,n,middle,count1)"
    and rest: "hlEmitDerivationsUsing emit middle count1 ds = (rest,ks,after,count')"
    and items: "items = front @ rest"
    by (auto simp: Let_def split: prod.splits)
  have front_allocated: "hlAllocated first front middle"
    by (rule Cons.prems(2)[OF _ front]) simp
  have rest_allocated: "hlAllocated middle rest after"
    by (rule Cons.IH[OF rest]) (auto intro: Cons.prems(2))
  from hlAllocated_append[OF front_allocated rest_allocated] show ?case
    by (simp add: items)
qed

lemma hlEmitDerivationFuel_allocated:
  assumes "hlEmitDerivationFuel fuel base env scope first count d = (items,n,after,count')"
  shows "hlAllocated first items after"
  using assms
proof (induction fuel arbitrary: env scope first count d items n after count')
  case Nil
  then show ?case by simp
next
  case (Cons u fuel)
  have list_allocated: "\<And>ds first count items ns after count'.
    hlEmitDerivationsUsing (\<lambda>first count d. hlEmitDerivationFuel fuel base env scope first count d)
      first count ds = (items,ns,after,count') \<Longrightarrow> hlAllocated first items after"
    by (rule hlAllocated_emit_list) (auto intro: Cons.IH)
  obtain phi rule where d: "d = HL_Derivation phi rule" by (cases d) auto
  from Cons.prems show ?case
    apply (cases rule)
    apply (auto simp: d Let_def split: prod.splits if_splits
         dest!: Cons.IH list_allocated
         intro: hlAllocated_snoc_end hlAllocated_box_and_line_end hlAllocated_append
           hlAllocated_line_end hlAllocated_two_boxes_and_line_end
           hlAllocated_subproof hlAllocated_cons_subproof)
    apply (erule hlAllocated_append; rule hlAllocated_two_boxes_and_line_end;
        auto simp: hlAllocated_def add.commute)+
    done
qed

lemma hlEmitDerivation_allocated:
  "hlEmitDerivation base env scope first count d = (items,n,after,count') \<Longrightarrow>
   hlAllocated first items after"
  unfolding hlEmitDerivation_def by (rule hlEmitDerivationFuel_allocated)

lemma hlEmitDerivation_fresh_numbers:
  assumes "hlEmitDerivation base env scope first count d = (items,n,after,count')"
  shows "sorted_wrt (<) (hlFitchLineNumbers items) \<and>
    distinct (hlFitchLineNumbers items) \<and>
    (\<forall>k \<in> set (hlFitchLineNumbers items). first \<le> k \<and> k < after)"
  using hlEmitDerivation_allocated[OF assms]
  by (auto simp: hlAllocated_def)

section \<open>The final emitted line\<close>

lemma hlEmitDerivationFuel_last:
  assumes "hlEmitDerivationFuel fuel base env scope first count d = (items,n,after,count')"
      and "items \<noteq> []"
  shows "\<exists>r. last items = HL_FLine n (hlDerivationFormula d) r \<and> after = n + 1"
  using assms
  by (cases fuel; cases d)
     (auto simp: Let_def split: hl_derivation_rule.splits prod.splits if_splits)

lemma hlEmitDerivation_last:
  assumes "hlEmitDerivation base env scope first count d = (items,n,after,count')"
      and "items \<noteq> []"
  shows "\<exists>r. last items = HL_FLine n (hlDerivationFormula d) r \<and> after = n + 1"
  using assms hlEmitDerivationFuel_last unfolding hlEmitDerivation_def by blast

lemma hlEmitDerivationFuel_concludesAtTop:
  "hlConcludesAtTop (fst (hlEmitDerivationFuel fuel base env scope first count d))"
proof -
  obtain items n after count' where result:
    "hlEmitDerivationFuel fuel base env scope first count d = (items,n,after,count')"
    by (cases "hlEmitDerivationFuel fuel base env scope first count d") auto
  show ?thesis
  proof (cases "items = []")
    case True
    then show ?thesis by (simp add: result hlConcludesAtTop_def)
  next
    case False
    from hlEmitDerivationFuel_last[OF result False] obtain r where
      last_item: "last items = HL_FLine n (hlDerivationFormula d) r" by blast
    show ?thesis by (simp add: result hlConcludesAtTop_def last_item)
  qed
qed

lemma hlEmitDerivation_concludesAtTop:
  "hlConcludesAtTop (fst (hlEmitDerivation base env scope first count d))"
  by (simp add: hlEmitDerivation_def hlEmitDerivationFuel_concludesAtTop)

end
