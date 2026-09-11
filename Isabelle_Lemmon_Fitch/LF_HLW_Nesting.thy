theory LF_HLW_Nesting
  imports LF_HLW_Premise_Layout LF_HLW_Derivation_Renaming
begin

fun hlTopLines :: "hl_fitch_proof \<Rightarrow> int set" where
  "hlTopLines [] = {}"
| "hlTopLines (HL_FLine n p r # F) = insert n (hlTopLines F)"
| "hlTopLines (HL_FSub s # F) = hlTopLines F"

fun hlTopBoxes :: "hl_fitch_proof \<Rightarrow> hl_subproof_reference set" where
  "hlTopBoxes [] = {}"
| "hlTopBoxes (HL_FLine n p r # F) = hlTopBoxes F"
| "hlTopBoxes (HL_FSub (HL_Subproof a p body) # F) =
    insert (a,hlSubLastLine (HL_Subproof a p body)) (hlTopBoxes F)"

lemma hlTopLines_append [simp]: "hlTopLines (F @ G) = hlTopLines F \<union> hlTopLines G"
proof (induction F)
  case Nil
  then show ?case by simp
next
  case (Cons item F)
  then show ?case by (cases item) auto
qed

lemma hlTopBoxes_append [simp]: "hlTopBoxes (F @ G) = hlTopBoxes F \<union> hlTopBoxes G"
proof (induction F)
  case Nil
  then show ?case by simp
next
  case (Cons item F)
  then show ?case
    by (cases item) (simp, rename_tac sub, case_tac sub, simp)
qed

lemma hlFitchNestingFrom_append:
  "hlFitchNestingFrom depth visible boxes (F @ G) =
   (hlFitchNestingFrom depth visible boxes F \<and>
    hlFitchNestingFrom depth (visible \<union> hlTopLines F) (boxes \<union> hlTopBoxes F) G)"
proof (induction F arbitrary: visible boxes)
  case Nil
  then show ?case by simp
next
  case (Cons item F)
  show ?case
  proof (cases item)
    case (HL_FLine n p r)
    then show ?thesis using Cons.IH
      by (auto simp: Un_insert_right insert_commute)
  next
    case (HL_FSub sub)
    then show ?thesis using Cons.IH
      by (cases sub) (auto simp: Un_insert_right insert_commute)
  qed
qed

lemma hlFitchNestingFrom_mono:
  "hlFitchNestingFrom depth visible boxes F \<Longrightarrow>
   visible \<subseteq> visible' \<Longrightarrow> boxes \<subseteq> boxes' \<Longrightarrow>
   hlFitchNestingFrom depth visible' boxes' F"
proof (induction depth visible boxes F arbitrary: visible' boxes' rule: hlFitchNestingFrom.induct)
  case (1 depth visible boxes)
  then show ?case by simp
next
  case (2 depth visible boxes n p r rest)
  from "2.prems"(1) have tail:
    "hlFitchNestingFrom depth (insert n visible) boxes rest" by simp
  have tail': "hlFitchNestingFrom depth (insert n visible') boxes' rest"
    by (rule "2.IH"[OF tail _ "2.prems"(3)]) (use "2.prems"(2) in auto)
  from "2.prems" tail' show ?case by auto
next
  case (3 depth visible boxes a p body rest)
  have body: "hlFitchNestingFrom (Suc depth) (insert a visible) {} body"
    using "3.prems"(1) by (simp only: hlFitchNestingFrom.simps; blast)
  have rest: "hlFitchNestingFrom depth visible
      (insert (a,hlSubLastLine (HL_Subproof a p body)) boxes) rest"
    using "3.prems"(1) by (simp only: hlFitchNestingFrom.simps; blast)
  have body': "hlFitchNestingFrom (Suc depth) (insert a visible') {} body"
    by (rule "3.IH"(1)[OF body]) (use "3.prems"(2) in auto)
  have rest': "hlFitchNestingFrom depth visible'
      (insert (a,hlSubLastLine (HL_Subproof a p body)) boxes') rest"
    by (rule "3.IH"(2)[OF rest "3.prems"(2)]) (use "3.prems"(3) in auto)
  from "3.prems"(1) body' rest' show ?case
    by (simp only: hlFitchNestingFrom.simps; blast)
qed

lemma hlTopLines_subset:
  "hlTopLines F \<subseteq> set (hlFitchLineNumbers F)"
proof (induction F)
  case Nil
  then show ?case by simp
next
  case (Cons item F)
  then show ?case by (cases item) auto
qed

lemma hlTopLines_last:
  "F \<noteq> [] \<Longrightarrow> last F = HL_FLine n p r \<Longrightarrow> n \<in> hlTopLines F"
  by (induction F rule: rev_induct) auto

lemma hlFitchLineNumbers_last:
  "F \<noteq> [] \<Longrightarrow> last F = HL_FLine n p r \<Longrightarrow>
   hlFitchLineNumbers F \<noteq> [] \<and> last (hlFitchLineNumbers F) = n"
  by (induction F rule: rev_induct) auto

text \<open>Only the labels of open leaves matter to citation visibility.
  Formula agreement is a separate rule-preservation obligation.\<close>

definition hlEnvironmentVisible ::
    "hl_layout_environment \<Rightarrow> int set \<Rightarrow> hl_derivation \<Rightarrow> bool" where
  "hlEnvironmentVisible env visible d \<longleftrightarrow>
   (\<forall>nf \<in> set (hlOpenAssumptions d). hlEnvironmentLine env (fst nf) \<in> visible)"

lemma hlEnvironmentVisible_mono:
  "hlEnvironmentVisible env visible d \<Longrightarrow> visible \<subseteq> visible' \<Longrightarrow>
   hlEnvironmentVisible env visible' d"
  by (auto simp: hlEnvironmentVisible_def)

lemma hlEnvironmentVisible_rename [simp]:
  "hlEnvironmentVisible env visible (hlRenameDerivation old new d) =
   hlEnvironmentVisible env visible d"
  by (auto simp: hlEnvironmentVisible_def hlOpenAssumptions_rename)

lemma hlEnvironmentVisible_repair:
  "hlRepairDerivation base count bad d = (count',pairs,d') \<Longrightarrow>
   hlEnvironmentVisible env visible d' = hlEnvironmentVisible env visible d"
  by (induction bad arbitrary: count d count' pairs d')
     (auto simp: Let_def split: prod.splits)

lemma hlEnvironmentVisible_extend:
  assumes "\<forall>nf \<in> set (hlOpenAssumptions d).
     fst nf \<noteq> a \<longrightarrow> hlEnvironmentLine env (fst nf) \<in> visible"
  shows "hlEnvironmentVisible ((a,n,p) # env) (insert n visible) d"
  using assms by (auto simp: hlEnvironmentVisible_def)

lemma hlFitchNestingFrom_snoc:
  assumes "hlFitchNestingFrom depth visible boxes F"
      and "r \<noteq> HL_FAssume" "r \<noteq> HL_FPremise"
      and "set (hlFitchCitedLines r) \<subseteq> visible \<union> hlTopLines F"
      and "set (hlFitchCitedSubs r) \<subseteq> boxes \<union> hlTopBoxes F"
  shows "hlFitchNestingFrom depth visible boxes (F @ [HL_FLine n p r])"
  using assms by (simp add: hlFitchNestingFrom_append)

lemma hlFitchNestingFrom_subproof:
  assumes "hlConcludesAtTop body"
      and "hlFitchNestingFrom (Suc depth) (insert a visible) {} body"
  shows "hlFitchNestingFrom depth visible boxes [HL_FSub (HL_Subproof a p body)]"
  using assms by simp

lemma hlClosedBody_concludesAtTop:
  assumes "hlConcludesAtTop body"
  shows "hlConcludesAtTop
    (if body = [] \<and> line \<noteq> a then [HL_FLine next p (HL_FReit line)] else body)"
  using assms by (auto simp: hlConcludesAtTop_def)

lemma hlClosedBody_nesting:
  assumes nested: "hlFitchNestingFrom depth (insert a visible) {} body"
      and cited: "line \<in> insert a visible \<union> hlTopLines body"
  shows "hlFitchNestingFrom depth (insert a visible) {}
    (if body = [] \<and> line \<noteq> a then [HL_FLine next p (HL_FReit line)] else body)"
  using nested cited by auto

lemma hlClosedBody_last:
  assumes "body \<noteq> [] \<Longrightarrow> \<exists>r. last body = HL_FLine line p r"
  shows "hlSubLastLine (HL_Subproof a af
    (if body = [] \<and> line \<noteq> a then [HL_FLine next p (HL_FReit line)] else body)) =
    (if body = [] \<and> line \<noteq> a then next else line)"
  using assms hlFitchLineNumbers_last[of body line p]
  by (cases "body = []") auto

lemma hlEmitDerivationFuel_return_visible:
  assumes emitted: "hlEmitDerivationFuel fuel base env scope first count d = (items,n,after,count')"
      and enough: "size d < length fuel"
      and covered: "hlEnvironmentVisible env visible d"
  shows "n \<in> visible \<union> hlTopLines items"
proof (cases "items = []")
  case False
  from hlEmitDerivationFuel_last[OF emitted False] obtain r where
    "last items = HL_FLine n (hlDerivationFormula d) r" by blast
  from hlTopLines_last[OF False this] show ?thesis by simp
next
  case True
  from enough have fuel: "fuel \<noteq> []" by auto
  have empty: "hlEmitDerivationFuel fuel base env scope first count d = ([],n,after,count')"
    using emitted True by simp
  from hlEmitDerivationFuel_empty[OF fuel empty] covered
  show ?thesis by (cases d) (auto simp: hlEnvironmentVisible_def)
qed

lemma hlFitchNestingFrom_append_both:
  assumes "hlFitchNestingFrom depth visible boxes F"
      and "hlFitchNestingFrom depth visible boxes G"
  shows "hlFitchNestingFrom depth visible boxes (F @ G)"
  using assms hlFitchNestingFrom_mono
  by (auto simp: hlFitchNestingFrom_append)

lemma hlNesting_emit_list:
  assumes emitted: "hlEmitDerivationsUsing emit first count ds = (items,ns,after,count')"
      and each: "\<And>d first count items n after count'. d \<in> set ds \<Longrightarrow>
        emit first count d = (items,n,after,count') \<Longrightarrow>
        hlFitchNestingFrom depth visible boxes items \<and>
        n \<in> visible \<union> hlTopLines items"
  shows "hlFitchNestingFrom depth visible boxes items \<and>
    set ns \<subseteq> visible \<union> hlTopLines items"
  using emitted each
proof (induction ds arbitrary: first count items ns after count')
  case Nil
  then show ?case by simp
next
  case (Cons d ds)
  from Cons.prems(1) obtain front n middle count1 rest ks where
    front: "emit first count d = (front,n,middle,count1)"
    and rest: "hlEmitDerivationsUsing emit middle count1 ds = (rest,ks,after,count')"
    and items: "items = front @ rest" and ns: "ns = n # ks"
    by (auto simp: Let_def split: prod.splits)
  have front_ok: "hlFitchNestingFrom depth visible boxes front \<and>
    n \<in> visible \<union> hlTopLines front"
    by (rule Cons.prems(2)[OF _ front]) simp
  have rest_ok: "hlFitchNestingFrom depth visible boxes rest \<and>
    set ks \<subseteq> visible \<union> hlTopLines rest"
  proof (rule Cons.IH[OF rest])
    fix e first count out n after count'
    assume member: "e \<in> set ds"
      and emitted: "emit first count e = (out,n,after,count')"
    have "e \<in> set (d # ds)" using member by simp
    from Cons.prems(2)[OF this emitted]
    show "hlFitchNestingFrom depth visible boxes out \<and>
      n \<in> visible \<union> hlTopLines out" .
  qed
  from front_ok rest_ok show ?case
    by (auto simp: items ns intro: hlFitchNestingFrom_append_both)
qed

lemma hlClosedBox_nesting:
  assumes nested: "hlFitchNestingFrom (Suc depth) (insert a visible) {} body"
      and cited: "line \<in> insert a visible \<union> hlTopLines body"
      and top: "hlConcludesAtTop body"
  shows "hlFitchNestingFrom depth visible boxes
    [HL_FSub (HL_Subproof a af
      (if body = [] \<and> line \<noteq> a then [HL_FLine next p (HL_FReit line)] else body))]"
  using hlClosedBody_concludesAtTop[OF top]
    hlClosedBody_nesting[OF nested cited]
  by simp

lemma hlClosedBox_reference:
  assumes "body \<noteq> [] \<Longrightarrow> \<exists>r. last body = HL_FLine line p r"
  shows "(a,if body = [] \<and> line \<noteq> a then next else line) \<in>
    hlTopBoxes [HL_FSub (HL_Subproof a af
      (if body = [] \<and> line \<noteq> a then [HL_FLine next p (HL_FReit line)] else body))]"
  using hlClosedBody_last[OF assms] by simp

section \<open>The environment covers every sub-derivation\<close>

lemma hlEnvironmentVisible_subset:
  "hlEnvironmentVisible env visible d \<Longrightarrow>
   set (hlOpenAssumptions e) \<subseteq> set (hlOpenAssumptions d) \<Longrightarrow>
   hlEnvironmentVisible env visible e"
  by (auto simp: hlEnvironmentVisible_def)

section \<open>Emitted fragments in citation position\<close>

lemma hlNesting_unary_shape:
  assumes emitted: "hlEmitDerivationFuel fs bs env scope first count e = (front,k,after,c1)"
      and enough: "size e < length fs"
      and covered: "hlEnvironmentVisible env visible e"
      and nested: "hlFitchNestingFrom depth visible boxes front"
      and lines: "set (hlFitchCitedLines r) \<subseteq> {k}"
      and subs: "hlFitchCitedSubs r = []"
      and shape: "r \<noteq> HL_FAssume" "r \<noteq> HL_FPremise"
  shows "hlFitchNestingFrom depth visible boxes (front @ [HL_FLine m p r])"
proof (rule hlFitchNestingFrom_snoc[OF nested shape])
  show "set (hlFitchCitedLines r) \<subseteq> visible \<union> hlTopLines front"
    using lines hlEmitDerivationFuel_return_visible[OF emitted enough covered] by auto
next
  show "set (hlFitchCitedSubs r) \<subseteq> boxes \<union> hlTopBoxes front" using subs by simp
qed

lemma hlNesting_binary_shape:
  assumes e1: "hlEmitDerivationFuel fs bs env scope first count e = (front,k,mid,c1)"
      and e2: "hlEmitDerivationFuel fs bs env scope mid c1 e2 = (back,k2,after,c2)"
      and enough: "size e < length fs" "size e2 < length fs"
      and covered: "hlEnvironmentVisible env visible e" "hlEnvironmentVisible env visible e2"
      and nested: "hlFitchNestingFrom depth visible boxes front"
        "hlFitchNestingFrom depth visible boxes back"
      and lines: "set (hlFitchCitedLines r) \<subseteq> {k,k2}"
      and subs: "hlFitchCitedSubs r = []"
      and shape: "r \<noteq> HL_FAssume" "r \<noteq> HL_FPremise"
  shows "hlFitchNestingFrom depth visible boxes (front @ back @ [HL_FLine m p r])"
proof -
  have joined: "hlFitchNestingFrom depth visible boxes (front @ back)"
    by (rule hlFitchNestingFrom_append_both[OF nested])
  have "set (hlFitchCitedLines r) \<subseteq> visible \<union> hlTopLines (front @ back)"
    using lines
      hlEmitDerivationFuel_return_visible[OF e1 enough(1) covered(1)]
      hlEmitDerivationFuel_return_visible[OF e2 enough(2) covered(2)]
    by auto
  from hlFitchNestingFrom_snoc[OF joined shape this] subs
  show ?thesis by simp
qed

text \<open>A closed box followed by the line that discharges it.  The box is the
  only new discharge pair the fragment introduces, and the box contributes no
  top-level line, so an ordinary citation of the trailing line must already be
  visible before the box.\<close>

lemma hlNesting_box_line:
  assumes box: "hlFitchNestingFrom depth visible boxes [HL_FSub (HL_Subproof a af cb)]"
      and ref: "s \<in> hlTopBoxes [HL_FSub (HL_Subproof a af cb)]"
      and lines: "hlFitchCitedLines r = []"
      and subs: "set (hlFitchCitedSubs r) \<subseteq> {s}"
      and shape: "r \<noteq> HL_FAssume" "r \<noteq> HL_FPremise"
  shows "hlFitchNestingFrom depth visible boxes
           [HL_FSub (HL_Subproof a af cb), HL_FLine m p r]"
  using assms by auto

lemma hlNesting_prefix_box_line:
  assumes pre: "hlFitchNestingFrom depth visible boxes front"
      and box: "hlFitchNestingFrom depth (visible \<union> hlTopLines front)
                  (boxes \<union> hlTopBoxes front) [HL_FSub (HL_Subproof a af cb)]"
      and ref: "s \<in> hlTopBoxes [HL_FSub (HL_Subproof a af cb)]"
      and lines: "set (hlFitchCitedLines r) \<subseteq> visible \<union> hlTopLines front"
      and subs: "set (hlFitchCitedSubs r) \<subseteq> {s}"
      and shape: "r \<noteq> HL_FAssume" "r \<noteq> HL_FPremise"
  shows "hlFitchNestingFrom depth visible boxes
           (front @ [HL_FSub (HL_Subproof a af cb), HL_FLine m p r])"
  using assms by (auto simp: hlFitchNestingFrom_append)

lemma hlNesting_prefix_two_boxes_line:
  assumes pre: "hlFitchNestingFrom depth visible boxes front"
      and box1: "hlFitchNestingFrom depth (visible \<union> hlTopLines front)
                   (boxes \<union> hlTopBoxes front) [HL_FSub (HL_Subproof a1 f1 c1)]"
      and box2: "hlFitchNestingFrom depth (visible \<union> hlTopLines front)
                   (boxes \<union> hlTopBoxes front \<union> hlTopBoxes [HL_FSub (HL_Subproof a1 f1 c1)])
                   [HL_FSub (HL_Subproof a2 f2 c2)]"
      and ref1: "s1 \<in> hlTopBoxes [HL_FSub (HL_Subproof a1 f1 c1)]"
      and ref2: "s2 \<in> hlTopBoxes [HL_FSub (HL_Subproof a2 f2 c2)]"
      and lines: "set (hlFitchCitedLines r) \<subseteq> visible \<union> hlTopLines front"
      and subs: "set (hlFitchCitedSubs r) \<subseteq> {s1,s2}"
      and shape: "r \<noteq> HL_FAssume" "r \<noteq> HL_FPremise"
  shows "hlFitchNestingFrom depth visible boxes
           (front @ [HL_FSub (HL_Subproof a1 f1 c1), HL_FSub (HL_Subproof a2 f2 c2),
                     HL_FLine m p r])"
  using assms by (auto simp: hlFitchNestingFrom_append)

section \<open>Discharge-pair visibility of the emitted proof\<close>

text \<open>Every citation the emitter writes names a line already visible at its
  depth, and every discharge pair it writes names a box in scope.  The
  environment hypothesis is what makes the leaf cases work: an emitted
  \<open>HL_DAssume\<close> or \<open>HL_DPremise\<close> contributes no line of its own and returns a
  line number looked up in \<open>env\<close>.\<close>

lemma hlEmitDerivationFuel_nesting:
  assumes "size d < length fuel"
      and "hlEmitDerivationFuel fuel base env scope first count d = (items,n,after,cnt)"
      and "hlEnvironmentVisible env visible d"
  shows "hlFitchNestingFrom depth visible boxes items"
  using assms
proof (induction d arbitrary: fuel env scope first count items n after cnt
       visible boxes depth rule: measure_induct_rule[where f=size])
  case (less d)
  from less.prems(1) obtain u fs where fuel: "fuel = u # fs" by (cases fuel) auto
  obtain phi rule where d: "d = HL_Derivation phi rule" by (cases d) auto
  have small: "size e < length fs" if "size e < size d" for e
    using less.prems(1) that fuel by simp

  have IH: "hlFitchNestingFrom dp vs bx front"
    if "size e < size d"
      and "hlEmitDerivationFuel fs base ev sc fi ct e = (front,k,af,c2)"
      and "hlEnvironmentVisible ev vs e"
    for e ev sc fi ct front k af c2 vs bx dp
    using less.IH[OF that(1) small[OF that(1)] that(2,3)] .

  show ?case
  proof (cases rule)
    case (HL_DAssume i)
    with less.prems(2) fuel d show ?thesis by simp
  next
    case (HL_DPremise i)
    with less.prems(2) fuel d show ?thesis by simp
  next
    case HL_DEqI
    with less.prems(2) fuel d show ?thesis by auto
  next
    case HL_DLEM
    with less.prems(2) fuel d show ?thesis by auto
  next
    case (HL_DDN e)
    obtain front k mid c1 where
      em: "hlEmitDerivationFuel fs base env scope first count e = (front,k,mid,c1)"
      by (cases "hlEmitDerivationFuel fs base env scope first count e") auto
    have sz: "size e < size d" using d HL_DDN by simp
    have cov: "hlEnvironmentVisible env visible e"
      using less.prems(3) d HL_DDN by (auto simp: hlEnvironmentVisible_def)
    have it: "items = front @ [HL_FLine mid phi (HL_FDN k)]"
      using less.prems(2) fuel d HL_DDN em by (auto simp: Let_def)
    show ?thesis unfolding it
      by (rule hlNesting_unary_shape[OF em small[OF sz] cov IH[OF sz em cov]]) auto
  next
    case (HL_DAndE e)
    obtain front k mid c1 where
      em: "hlEmitDerivationFuel fs base env scope first count e = (front,k,mid,c1)"
      by (cases "hlEmitDerivationFuel fs base env scope first count e") auto
    have sz: "size e < size d" using d HL_DAndE by simp
    have cov: "hlEnvironmentVisible env visible e"
      using less.prems(3) d HL_DAndE by (auto simp: hlEnvironmentVisible_def)
    have it: "items = front @ [HL_FLine mid phi (HL_FAndE k)]"
      using less.prems(2) fuel d HL_DAndE em by (auto simp: Let_def)
    show ?thesis unfolding it
      by (rule hlNesting_unary_shape[OF em small[OF sz] cov IH[OF sz em cov]]) auto
  next
    case (HL_DOrI e)
    obtain front k mid c1 where
      em: "hlEmitDerivationFuel fs base env scope first count e = (front,k,mid,c1)"
      by (cases "hlEmitDerivationFuel fs base env scope first count e") auto
    have sz: "size e < size d" using d HL_DOrI by simp
    have cov: "hlEnvironmentVisible env visible e"
      using less.prems(3) d HL_DOrI by (auto simp: hlEnvironmentVisible_def)
    have it: "items = front @ [HL_FLine mid phi (HL_FOrI k)]"
      using less.prems(2) fuel d HL_DOrI em by (auto simp: Let_def)
    show ?thesis unfolding it
      by (rule hlNesting_unary_shape[OF em small[OF sz] cov IH[OF sz em cov]]) auto
  next
    case (HL_DForallE e)
    obtain front k mid c1 where
      em: "hlEmitDerivationFuel fs base env scope first count e = (front,k,mid,c1)"
      by (cases "hlEmitDerivationFuel fs base env scope first count e") auto
    have sz: "size e < size d" using d HL_DForallE by simp
    have cov: "hlEnvironmentVisible env visible e"
      using less.prems(3) d HL_DForallE by (auto simp: hlEnvironmentVisible_def)
    have it: "items = front @ [HL_FLine mid phi (HL_FForallE k)]"
      using less.prems(2) fuel d HL_DForallE em by (auto simp: Let_def)
    show ?thesis unfolding it
      by (rule hlNesting_unary_shape[OF em small[OF sz] cov IH[OF sz em cov]]) auto
  next
    case (HL_DExistsI e)
    obtain front k mid c1 where
      em: "hlEmitDerivationFuel fs base env scope first count e = (front,k,mid,c1)"
      by (cases "hlEmitDerivationFuel fs base env scope first count e") auto
    have sz: "size e < size d" using d HL_DExistsI by simp
    have cov: "hlEnvironmentVisible env visible e"
      using less.prems(3) d HL_DExistsI by (auto simp: hlEnvironmentVisible_def)
    have it: "items = front @ [HL_FLine mid phi (HL_FExistsI k)]"
      using less.prems(2) fuel d HL_DExistsI em by (auto simp: Let_def)
    show ?thesis unfolding it
      by (rule hlNesting_unary_shape[OF em small[OF sz] cov IH[OF sz em cov]]) auto
  next
    case (HL_DQN e)
    obtain front k mid c1 where
      em: "hlEmitDerivationFuel fs base env scope first count e = (front,k,mid,c1)"
      by (cases "hlEmitDerivationFuel fs base env scope first count e") auto
    have sz: "size e < size d" using d HL_DQN by simp
    have cov: "hlEnvironmentVisible env visible e"
      using less.prems(3) d HL_DQN by (auto simp: hlEnvironmentVisible_def)
    have it: "items = front @ [HL_FLine mid phi (HL_FQN k)]"
      using less.prems(2) fuel d HL_DQN em by (auto simp: Let_def)
    show ?thesis unfolding it
      by (rule hlNesting_unary_shape[OF em small[OF sz] cov IH[OF sz em cov]]) auto
  next
    case (HL_DMP e1 e2)
    obtain front k mid c1 where
      em1: "hlEmitDerivationFuel fs base env scope first count e1 = (front,k,mid,c1)"
      by (cases "hlEmitDerivationFuel fs base env scope first count e1") auto
    obtain rear k2 fin c2 where
      em2: "hlEmitDerivationFuel fs base env scope mid c1 e2 = (rear,k2,fin,c2)"
      by (cases "hlEmitDerivationFuel fs base env scope mid c1 e2") auto
    have sz1: "size e1 < size d" and sz2: "size e2 < size d" using d HL_DMP by simp_all
    have cov1: "hlEnvironmentVisible env visible e1"
      and cov2: "hlEnvironmentVisible env visible e2"
      using less.prems(3) d HL_DMP by (auto simp: hlEnvironmentVisible_def)
    have it: "items = front @ rear @ [HL_FLine fin phi (HL_FMP k k2)]"
      using less.prems(2) fuel d HL_DMP em1 em2 by (auto simp: Let_def)
    show ?thesis unfolding it
      by (rule hlNesting_binary_shape[OF em1 em2 small[OF sz1] small[OF sz2] cov1 cov2
            IH[OF sz1 em1 cov1] IH[OF sz2 em2 cov2]]) auto
  next
    case (HL_DMT e1 e2)
    obtain front k mid c1 where
      em1: "hlEmitDerivationFuel fs base env scope first count e1 = (front,k,mid,c1)"
      by (cases "hlEmitDerivationFuel fs base env scope first count e1") auto
    obtain rear k2 fin c2 where
      em2: "hlEmitDerivationFuel fs base env scope mid c1 e2 = (rear,k2,fin,c2)"
      by (cases "hlEmitDerivationFuel fs base env scope mid c1 e2") auto
    have sz1: "size e1 < size d" and sz2: "size e2 < size d" using d HL_DMT by simp_all
    have cov1: "hlEnvironmentVisible env visible e1"
      and cov2: "hlEnvironmentVisible env visible e2"
      using less.prems(3) d HL_DMT by (auto simp: hlEnvironmentVisible_def)
    have it: "items = front @ rear @ [HL_FLine fin phi (HL_FMT k k2)]"
      using less.prems(2) fuel d HL_DMT em1 em2 by (auto simp: Let_def)
    show ?thesis unfolding it
      by (rule hlNesting_binary_shape[OF em1 em2 small[OF sz1] small[OF sz2] cov1 cov2
            IH[OF sz1 em1 cov1] IH[OF sz2 em2 cov2]]) auto
  next
    case (HL_DAndI e1 e2)
    obtain front k mid c1 where
      em1: "hlEmitDerivationFuel fs base env scope first count e1 = (front,k,mid,c1)"
      by (cases "hlEmitDerivationFuel fs base env scope first count e1") auto
    obtain rear k2 fin c2 where
      em2: "hlEmitDerivationFuel fs base env scope mid c1 e2 = (rear,k2,fin,c2)"
      by (cases "hlEmitDerivationFuel fs base env scope mid c1 e2") auto
    have sz1: "size e1 < size d" and sz2: "size e2 < size d" using d HL_DAndI by simp_all
    have cov1: "hlEnvironmentVisible env visible e1"
      and cov2: "hlEnvironmentVisible env visible e2"
      using less.prems(3) d HL_DAndI by (auto simp: hlEnvironmentVisible_def)
    have it: "items = front @ rear @ [HL_FLine fin phi (HL_FAndI k k2)]"
      using less.prems(2) fuel d HL_DAndI em1 em2 by (auto simp: Let_def)
    show ?thesis unfolding it
      by (rule hlNesting_binary_shape[OF em1 em2 small[OF sz1] small[OF sz2] cov1 cov2
            IH[OF sz1 em1 cov1] IH[OF sz2 em2 cov2]]) auto
  next
    case (HL_DEqE e1 e2)
    obtain front k mid c1 where
      em1: "hlEmitDerivationFuel fs base env scope first count e1 = (front,k,mid,c1)"
      by (cases "hlEmitDerivationFuel fs base env scope first count e1") auto
    obtain rear k2 fin c2 where
      em2: "hlEmitDerivationFuel fs base env scope mid c1 e2 = (rear,k2,fin,c2)"
      by (cases "hlEmitDerivationFuel fs base env scope mid c1 e2") auto
    have sz1: "size e1 < size d" and sz2: "size e2 < size d" using d HL_DEqE by simp_all
    have cov1: "hlEnvironmentVisible env visible e1"
      and cov2: "hlEnvironmentVisible env visible e2"
      using less.prems(3) d HL_DEqE by (auto simp: hlEnvironmentVisible_def)
    have it: "items = front @ rear @ [HL_FLine fin phi (HL_FEqE k k2)]"
      using less.prems(2) fuel d HL_DEqE em1 em2 by (auto simp: Let_def)
    show ?thesis unfolding it
      by (rule hlNesting_binary_shape[OF em1 em2 small[OF sz1] small[OF sz2] cov1 cov2
            IH[OF sz1 em1 cov1] IH[OF sz2 em2 cov2]]) auto
  next
    case (HL_DIffI e1 e2)
    obtain front k mid c1 where
      em1: "hlEmitDerivationFuel fs base env scope first count e1 = (front,k,mid,c1)"
      by (cases "hlEmitDerivationFuel fs base env scope first count e1") auto
    obtain rear k2 fin c2 where
      em2: "hlEmitDerivationFuel fs base env scope mid c1 e2 = (rear,k2,fin,c2)"
      by (cases "hlEmitDerivationFuel fs base env scope mid c1 e2") auto
    have sz1: "size e1 < size d" and sz2: "size e2 < size d" using d HL_DIffI by simp_all
    have cov1: "hlEnvironmentVisible env visible e1"
      and cov2: "hlEnvironmentVisible env visible e2"
      using less.prems(3) d HL_DIffI by (auto simp: hlEnvironmentVisible_def)
    have it: "items = front @ rear @ [HL_FLine fin phi (HL_FIffI k k2)]"
      using less.prems(2) fuel d HL_DIffI em1 em2 by (auto simp: Let_def)
    show ?thesis unfolding it
      by (rule hlNesting_binary_shape[OF em1 em2 small[OF sz1] small[OF sz2] cov1 cov2
            IH[OF sz1 em1 cov1] IH[OF sz2 em2 cov2]]) auto
  next
    case (HL_DIffE e1 e2)
    obtain front k mid c1 where
      em1: "hlEmitDerivationFuel fs base env scope first count e1 = (front,k,mid,c1)"
      by (cases "hlEmitDerivationFuel fs base env scope first count e1") auto
    obtain rear k2 fin c2 where
      em2: "hlEmitDerivationFuel fs base env scope mid c1 e2 = (rear,k2,fin,c2)"
      by (cases "hlEmitDerivationFuel fs base env scope mid c1 e2") auto
    have sz1: "size e1 < size d" and sz2: "size e2 < size d" using d HL_DIffE by simp_all
    have cov1: "hlEnvironmentVisible env visible e1"
      and cov2: "hlEnvironmentVisible env visible e2"
      using less.prems(3) d HL_DIffE by (auto simp: hlEnvironmentVisible_def)
    have it: "items = front @ rear @ [HL_FLine fin phi (HL_FIffE k k2)]"
      using less.prems(2) fuel d HL_DIffE em1 em2 by (auto simp: Let_def)
    show ?thesis unfolding it
      by (rule hlNesting_binary_shape[OF em1 em2 small[OF sz1] small[OF sz2] cov1 cov2
            IH[OF sz1 em1 cov1] IH[OF sz2 em2 cov2]]) auto
  next
    case (HL_DCP a af body)
    let ?ev = "(a,first,af) # env"
    obtain bi bl n1 c1 where
      em: "hlEmitDerivationFuel fs base ?ev (af # scope) (first + 1) count body
             = (bi,bl,n1,c1)"
      by (cases "hlEmitDerivationFuel fs base ?ev (af # scope) (first + 1) count body") auto
    have sz: "size body < size d" using d HL_DCP by simp
    have cov: "hlEnvironmentVisible ?ev (insert first visible) body"
      by (rule hlEnvironmentVisible_extend)
         (use less.prems(3) d HL_DCP in \<open>auto simp: hlEnvironmentVisible_def\<close>)
    have nested: "hlFitchNestingFrom (Suc depth) (insert first visible) {} bi"
      by (rule IH[OF sz em cov])
    have top: "hlConcludesAtTop bi"
      using hlEmitDerivationFuel_concludesAtTop[of fs base ?ev "af # scope" "first + 1" count body]
      by (simp add: em)
    have cited: "bl \<in> insert first visible \<union> hlTopLines bi"
      using hlEmitDerivationFuel_return_visible[OF em small[OF sz] cov] by simp
    have lst: "bi \<noteq> [] \<Longrightarrow> \<exists>r. last bi = HL_FLine bl (hlDerivationFormula body) r"
      using hlEmitDerivationFuel_last[OF em] by blast
    have it: "items =
      [HL_FSub (HL_Subproof first af
         (if bi = [] \<and> bl \<noteq> first
          then [HL_FLine n1 (hlDerivationFormula body) (HL_FReit bl)] else bi)),
       HL_FLine (if bi = [] \<and> bl \<noteq> first then n1 + 1 else n1) phi
         (HL_FCP (first, if bi = [] \<and> bl \<noteq> first then n1 else bl))]"
      using less.prems(2) fuel d HL_DCP em by (auto simp: Let_def)
    show ?thesis unfolding it
      by (rule hlNesting_box_line
            [OF hlClosedBox_nesting[OF nested cited top] hlClosedBox_reference[OF lst]]) auto
  next
    case (HL_DRAA a af body)
    let ?ev = "(a,first,af) # env"
    obtain bi bl n1 c1 where
      em: "hlEmitDerivationFuel fs base ?ev (af # scope) (first + 1) count body
             = (bi,bl,n1,c1)"
      by (cases "hlEmitDerivationFuel fs base ?ev (af # scope) (first + 1) count body") auto
    have sz: "size body < size d" using d HL_DRAA by simp
    have cov: "hlEnvironmentVisible ?ev (insert first visible) body"
      by (rule hlEnvironmentVisible_extend)
         (use less.prems(3) d HL_DRAA in \<open>auto simp: hlEnvironmentVisible_def\<close>)
    have nested: "hlFitchNestingFrom (Suc depth) (insert first visible) {} bi"
      by (rule IH[OF sz em cov])
    have top: "hlConcludesAtTop bi"
      using hlEmitDerivationFuel_concludesAtTop[of fs base ?ev "af # scope" "first + 1" count body]
      by (simp add: em)
    have cited: "bl \<in> insert first visible \<union> hlTopLines bi"
      using hlEmitDerivationFuel_return_visible[OF em small[OF sz] cov] by simp
    have lst: "bi \<noteq> [] \<Longrightarrow> \<exists>r. last bi = HL_FLine bl (hlDerivationFormula body) r"
      using hlEmitDerivationFuel_last[OF em] by blast
    have it: "items =
      [HL_FSub (HL_Subproof first af
         (if bi = [] \<and> bl \<noteq> first
          then [HL_FLine n1 (hlDerivationFormula body) (HL_FReit bl)] else bi)),
       HL_FLine (if bi = [] \<and> bl \<noteq> first then n1 + 1 else n1) phi
         (HL_FRAA (first, if bi = [] \<and> bl \<noteq> first then n1 else bl))]"
      using less.prems(2) fuel d HL_DRAA em by (auto simp: Let_def)
    show ?thesis unfolding it
      by (rule hlNesting_box_line
            [OF hlClosedBox_nesting[OF nested cited top] hlClosedBox_reference[OF lst]]) auto
  next
    case (HL_DForallI e)
    obtain c0 prs rep where
      rp: "hlRepairDerivation base count (hlForallRepairConstants scope phi e) e = (c0,prs,rep)"
      by (cases "hlRepairDerivation base count (hlForallRepairConstants scope phi e) e") auto
    obtain front k mid c1 where
      em: "hlEmitDerivationFuel fs base env scope first c0 rep = (front,k,mid,c1)"
      by (cases "hlEmitDerivationFuel fs base env scope first c0 rep") auto
    have sz: "size rep < size d"
      using d HL_DForallI hlRepairDerivation_size[OF rp] by simp
    have cov: "hlEnvironmentVisible env visible rep"
      using hlEnvironmentVisible_repair[OF rp] less.prems(3) d HL_DForallI
      by (auto simp: hlEnvironmentVisible_def)
    have it: "items = front @ [HL_FLine mid phi (HL_FForallI k)]"
      using less.prems(2) fuel d HL_DForallI rp em by (auto simp: Let_def)
    show ?thesis unfolding it
      by (rule hlNesting_unary_shape[OF em small[OF sz] cov IH[OF sz em cov]]) auto
  next
    case (HL_DPropTaut ds)
    obtain front ns mid c1 where
      em: "hlEmitDerivationsUsing (hlEmitDerivationFuel fs base env scope) first count ds
             = (front,ns,mid,c1)"
      by (cases "hlEmitDerivationsUsing (hlEmitDerivationFuel fs base env scope) first count ds")
         auto
    have each: "hlFitchNestingFrom depth visible boxes out \<and> k \<in> visible \<union> hlTopLines out"
      if mem: "e \<in> set ds"
        and got: "hlEmitDerivationFuel fs base env scope fi ct e = (out,k,af2,c2)"
      for e fi ct out k af2 c2
    proof -
      have sz: "size e < size d"
      proof -
        have "size e \<le> size_list size ds"
          by (rule size_list_estimation'[OF mem]) simp
        then show ?thesis using d HL_DPropTaut by simp
      qed
      have cov: "hlEnvironmentVisible env visible e"
        using less.prems(3) d HL_DPropTaut mem by (auto simp: hlEnvironmentVisible_def)
      show ?thesis
        using IH[OF sz got cov] hlEmitDerivationFuel_return_visible[OF got small[OF sz] cov]
        by blast
    qed
    have parts: "hlFitchNestingFrom depth visible boxes front \<and>
                 set ns \<subseteq> visible \<union> hlTopLines front"
      by (rule hlNesting_emit_list[OF em]) (use each in blast)
    have it: "items = front @ [HL_FLine mid phi (HL_FPropTaut ns)]"
      using less.prems(2) fuel d HL_DPropTaut em by (auto simp: Let_def)
    show ?thesis unfolding it
      using parts by (auto intro!: hlFitchNestingFrom_snoc)
  next
    case (HL_DExistsE src a af body)
    obtain si sl n0 c0 where
      ems: "hlEmitDerivationFuel fs base env scope first count src = (si,sl,n0,c0)"
      by (cases "hlEmitDerivationFuel fs base env scope first count src") auto
    obtain cR prs rb where
      rp: "hlRepairDerivation base c0 (hlExistsRepairConstants scope af src phi) body
             = (cR,prs,rb)"
      by (cases "hlRepairDerivation base c0 (hlExistsRepairConstants scope af src phi) body") auto
    let ?ra = "hlRenamePairsFormula prs af"
    let ?ev = "(a,n0,?ra) # env"
    let ?vis = "visible \<union> hlTopLines si"
    obtain bi bl n1 c1 where
      em: "hlEmitDerivationFuel fs base ?ev (?ra # scope) (n0 + 1) cR rb = (bi,bl,n1,c1)"
      by (cases "hlEmitDerivationFuel fs base ?ev (?ra # scope) (n0 + 1) cR rb") auto
    have szs: "size src < size d" and szb: "size rb < size d"
      using d HL_DExistsE hlRepairDerivation_size[OF rp] by simp_all
    have covs: "hlEnvironmentVisible env visible src"
      using less.prems(3) d HL_DExistsE by (auto simp: hlEnvironmentVisible_def)
    have covb: "hlEnvironmentVisible ?ev (insert n0 ?vis) rb"
      unfolding hlEnvironmentVisible_repair[OF rp]
      by (rule hlEnvironmentVisible_extend)
         (use less.prems(3) d HL_DExistsE in \<open>auto simp: hlEnvironmentVisible_def\<close>)
    have pre: "hlFitchNestingFrom depth visible boxes si" by (rule IH[OF szs ems covs])
    have nested: "hlFitchNestingFrom (Suc depth) (insert n0 ?vis) {} bi"
      by (rule IH[OF szb em covb])
    have top: "hlConcludesAtTop bi"
      using hlEmitDerivationFuel_concludesAtTop[of fs base ?ev "?ra # scope" "n0 + 1" cR rb]
      by (simp add: em)
    have cited: "bl \<in> insert n0 ?vis \<union> hlTopLines bi"
      using hlEmitDerivationFuel_return_visible[OF em small[OF szb] covb] by simp
    have lst: "bi \<noteq> [] \<Longrightarrow> \<exists>r. last bi = HL_FLine bl (hlDerivationFormula rb) r"
      using hlEmitDerivationFuel_last[OF em] by blast
    have srcvis: "sl \<in> visible \<union> hlTopLines si"
      using hlEmitDerivationFuel_return_visible[OF ems small[OF szs] covs] by simp
    have it: "items = si @
      [HL_FSub (HL_Subproof n0 ?ra
         (if bi = [] \<and> bl \<noteq> n0
          then [HL_FLine n1 (hlDerivationFormula rb) (HL_FReit bl)] else bi)),
       HL_FLine (if bi = [] \<and> bl \<noteq> n0 then n1 + 1 else n1) phi
         (HL_FExistsE sl (n0, if bi = [] \<and> bl \<noteq> n0 then n1 else bl))]"
      using less.prems(2) fuel d HL_DExistsE ems rp em by (auto simp: Let_def)
    show ?thesis unfolding it
      by (rule hlNesting_prefix_box_line
            [OF pre hlClosedBox_nesting[OF nested cited top] hlClosedBox_reference[OF lst]])
         (use srcvis in auto)
  next
    case (HL_DOrE d0 a1 f1 bd1 a2 f2 bd2)
    obtain i0 k0 n0 c0 where
      em0: "hlEmitDerivationFuel fs base env scope first count d0 = (i0,k0,n0,c0)"
      by (cases "hlEmitDerivationFuel fs base env scope first count d0") auto
    let ?vis = "visible \<union> hlTopLines i0"
    let ?ev1 = "(a1,n0,f1) # env"
    obtain u1 l1 n1 c1 where
      em1: "hlEmitDerivationFuel fs base ?ev1 (f1 # scope) (n0 + 1) c0 bd1 = (u1,l1,n1,c1)"
      by (cases "hlEmitDerivationFuel fs base ?ev1 (f1 # scope) (n0 + 1) c0 bd1") auto
    let ?after1 = "if u1 = [] \<and> l1 \<noteq> n0 then n1 + 1 else n1"
    let ?ev2 = "(a2,?after1,f2) # env"
    obtain u2 l2 n2 c2 where
      em2: "hlEmitDerivationFuel fs base ?ev2 (f2 # scope) (?after1 + 1) c1 bd2 = (u2,l2,n2,c2)"
      by (cases "hlEmitDerivationFuel fs base ?ev2 (f2 # scope) (?after1 + 1) c1 bd2") auto
    have sz0: "size d0 < size d" and sz1: "size bd1 < size d" and sz2: "size bd2 < size d"
      using d HL_DOrE by simp_all
    have cov0: "hlEnvironmentVisible env visible d0"
      using less.prems(3) d HL_DOrE by (auto simp: hlEnvironmentVisible_def)
    have cov1: "hlEnvironmentVisible ?ev1 (insert n0 ?vis) bd1"
      by (rule hlEnvironmentVisible_extend)
         (use less.prems(3) d HL_DOrE in \<open>auto simp: hlEnvironmentVisible_def\<close>)
    have cov2: "hlEnvironmentVisible ?ev2 (insert ?after1 ?vis) bd2"
      by (rule hlEnvironmentVisible_extend)
         (use less.prems(3) d HL_DOrE in \<open>auto simp: hlEnvironmentVisible_def\<close>)
    have pre: "hlFitchNestingFrom depth visible boxes i0" by (rule IH[OF sz0 em0 cov0])
    have nest1: "hlFitchNestingFrom (Suc depth) (insert n0 ?vis) {} u1"
      by (rule IH[OF sz1 em1 cov1])
    have nest2: "hlFitchNestingFrom (Suc depth) (insert ?after1 ?vis) {} u2"
      by (rule IH[OF sz2 em2 cov2])
    have top1: "hlConcludesAtTop u1"
      using hlEmitDerivationFuel_concludesAtTop[of fs base ?ev1 "f1 # scope" "n0 + 1" c0 bd1]
      by (simp add: em1)
    have top2: "hlConcludesAtTop u2"
      using hlEmitDerivationFuel_concludesAtTop[of fs base ?ev2 "f2 # scope" "?after1 + 1" c1 bd2]
      by (simp add: em2)
    have cit1: "l1 \<in> insert n0 ?vis \<union> hlTopLines u1"
      using hlEmitDerivationFuel_return_visible[OF em1 small[OF sz1] cov1] by simp
    have cit2: "l2 \<in> insert ?after1 ?vis \<union> hlTopLines u2"
      using hlEmitDerivationFuel_return_visible[OF em2 small[OF sz2] cov2] by simp
    have lst1: "u1 \<noteq> [] \<Longrightarrow> \<exists>r. last u1 = HL_FLine l1 (hlDerivationFormula bd1) r"
      using hlEmitDerivationFuel_last[OF em1] by blast
    have lst2: "u2 \<noteq> [] \<Longrightarrow> \<exists>r. last u2 = HL_FLine l2 (hlDerivationFormula bd2) r"
      using hlEmitDerivationFuel_last[OF em2] by blast
    have srcvis: "k0 \<in> visible \<union> hlTopLines i0"
      using hlEmitDerivationFuel_return_visible[OF em0 small[OF sz0] cov0] by simp
    have it: "items = i0 @
      [HL_FSub (HL_Subproof n0 f1
         (if u1 = [] \<and> l1 \<noteq> n0
          then [HL_FLine n1 (hlDerivationFormula bd1) (HL_FReit l1)] else u1)),
       HL_FSub (HL_Subproof ?after1 f2
         (if u2 = [] \<and> l2 \<noteq> ?after1
          then [HL_FLine n2 (hlDerivationFormula bd2) (HL_FReit l2)] else u2)),
       HL_FLine (if u2 = [] \<and> l2 \<noteq> ?after1 then n2 + 1 else n2) phi
         (HL_FOrE k0 (n0, if u1 = [] \<and> l1 \<noteq> n0 then n1 else l1)
                     (?after1, if u2 = [] \<and> l2 \<noteq> ?after1 then n2 else l2))]"
      using less.prems(2) fuel d HL_DOrE em0 em1 em2 by (auto simp: Let_def)
    show ?thesis unfolding it
      by (rule hlNesting_prefix_two_boxes_line
            [OF pre hlClosedBox_nesting[OF nest1 cit1 top1]
                hlClosedBox_nesting[OF nest2 cit2 top2]
                hlClosedBox_reference[OF lst1] hlClosedBox_reference[OF lst2]])
         (use srcvis in auto)
  qed
qed

section \<open>Ordinary citation visibility follows from discharge-pair visibility\<close>

text \<open>\<^const>\<open>hlFitchScopeFrom\<close> is the weaker of the two checks: after a box it
  makes the box's assumption line and last line visible, which
  \<^const>\<open>hlFitchNestingFrom\<close> does not, and it inspects no discharge pairs at
  all.  So the nesting theorem carries the scope check with it, and
  \<^const>\<open>hlFitchWellFormed\<close> needs no separate induction over the emitter.\<close>

lemma hlFitchNestingFrom_scope:
  "hlFitchNestingFrom depth visible boxes F \<Longrightarrow> visible \<subseteq> W \<Longrightarrow>
   hlFitchScopeFrom depth W F \<noteq> None"
proof (induction depth visible boxes F arbitrary: W rule: hlFitchNestingFrom.induct)
  case (1 depth visible boxes)
  then show ?case by simp
next
  case (2 depth visible boxes n p r rest)
  from "2.prems"(1) have
    prem: "r = HL_FPremise \<longrightarrow> depth = 0"
    and cits: "set (hlFitchCitedLines r) \<subseteq> visible"
    and tail: "hlFitchNestingFrom depth (insert n visible) boxes rest"
    by simp_all
  have "hlFitchScopeFrom depth (insert n W) rest \<noteq> None"
    by (rule "2.IH"[OF tail]) (use "2.prems"(2) in auto)
  then show ?case
    using cits prem "2.prems"(2) by (auto split: hl_fitch_rule.split)
next
  case (3 depth visible boxes a p body rest)
  from "3.prems"(1) have
    body: "hlFitchNestingFrom (Suc depth) (insert a visible) {} body"
    and rest: "hlFitchNestingFrom depth visible
                 (insert (a,hlSubLastLine (HL_Subproof a p body)) boxes) rest"
    by simp_all
  have "hlFitchScopeFrom (Suc depth) (insert a W) body \<noteq> None"
    by (rule "3.IH"(1)[OF body]) (use "3.prems"(2) in auto)
  then obtain V where bV: "hlFitchScopeFrom (Suc depth) (insert a W) body = Some V" by auto
  have "hlFitchScopeFrom depth
      (insert a (insert (hlSubLastLine (HL_Subproof a p body)) W)) rest \<noteq> None"
    by (rule "3.IH"(2)[OF rest]) (use "3.prems"(2) in auto)
  then show ?case using bV by simp
qed

section \<open>The emitted proof, and the whole translation\<close>

lemma hlEmitDerivation_nesting:
  assumes "hlEmitDerivation base env scope first count d = (items,n,after,cnt)"
      and "hlEnvironmentVisible env visible d"
  shows "hlFitchNestingFrom depth visible boxes items"
  using assms unfolding hlEmitDerivation_def
  by (rule hlEmitDerivationFuel_nesting[rotated]) simp_all

lemma hlEnvironmentLine_in_lines:
  "i \<in> fst ` set env \<Longrightarrow> hlEnvironmentLine env i \<in> (\<lambda>(s,n,p). n) ` set env"
proof (induction env)
  case Nil
  then show ?case by simp
next
  case (Cons e env)
  obtain s m q where e: "e = (s,m,q)" by (cases e) auto
  show ?case
  proof (cases "s = i")
    case True
    then show ?thesis using e by simp
  next
    case False
    then have "i \<in> fst ` set env" using Cons.prems e by auto
    then show ?thesis using Cons.IH e False by auto
  qed
qed

lemma hlTopLines_premiseFitchLines:
  "hlTopLines (hlPremiseFitchLines env) = (\<lambda>(s,n,p). n) ` set env"
  by (induction env) (auto simp: hlPremiseFitchLines_def split: prod.splits)

lemma hlTopBoxes_premiseFitchLines:
  "hlTopBoxes (hlPremiseFitchLines env) = {}"
  by (induction env) (auto simp: hlPremiseFitchLines_def split: prod.splits)

lemma hlNesting_premiseFitchLines:
  "hlFitchNestingFrom 0 visible boxes (hlPremiseFitchLines env)"
  by (induction env arbitrary: visible) (auto simp: hlPremiseFitchLines_def split: prod.splits)

lemma hlNumberPremises_sources:
  "fst ` set (hlNumberPremises k G) = fst ` set G"
proof (induction G arbitrary: k)
  case Nil
  then show ?case by simp
next
  case (Cons g G)
  obtain s q where g: "g = (s,q)" by (cases g) auto
  show ?case using Cons.IH[of "k+1"] by (simp add: g)
qed

text \<open>The root environment lists every open assumption of a classified tree, so
  every leaf citation resolves to one of the emitted premise lines.\<close>

lemma hlPremiseEnvironment_covers:
  assumes "set (hlPremisesOf d) = set (hlOpenAssumptions d)"
  shows "hlEnvironmentVisible (hlPremiseEnvironment d)
           (hlTopLines (hlPremiseFitchLines (hlPremiseEnvironment d))) d"
  unfolding hlEnvironmentVisible_def hlTopLines_premiseFitchLines
proof
  fix nf assume nf: "nf \<in> set (hlOpenAssumptions d)"
  have "fst nf \<in> fst ` set (hlPremiseEnvironment d)"
    using nf assms
    by (auto simp: hlPremiseEnvironment_def hlNumberPremises_sources)
  from hlEnvironmentLine_in_lines[OF this]
  show "hlEnvironmentLine (hlPremiseEnvironment d) (fst nf)
          \<in> (\<lambda>(s,n,p). n) ` set (hlPremiseEnvironment d)" .
qed

theorem hlDerivationToFitch_nesting:
  assumes "set (hlPremisesOf d) = set (hlOpenAssumptions d)"
  shows "hlFitchNestingFrom 0 {} {} (hlDerivationToFitch d)"
proof -
  let ?env = "hlPremiseEnvironment d"
  let ?pre = "hlPremiseFitchLines ?env"
  obtain body k after cnt where
    em: "hlEmitDerivation
           (Suc (maxlen (sorted_list_of_set
             (\<Union> (hlConstantsInFormula ` set (hlDerivationFormulas d))))))
           ?env (map (\<lambda>(source,n,phi). phi) ?env) (1 + int (length ?env)) 0 d
         = (body,k,after,cnt)"
    by (cases "hlEmitDerivation
           (Suc (maxlen (sorted_list_of_set
             (\<Union> (hlConstantsInFormula ` set (hlDerivationFormulas d))))))
           ?env (map (\<lambda>(source,n,phi). phi) ?env) (1 + int (length ?env)) 0 d") auto
  have F: "hlDerivationToFitch d = ?pre @ body"
    using em unfolding hlDerivationToFitch_def by (simp add: Let_def)
  have "hlFitchNestingFrom 0 (hlTopLines ?pre) {} body"
    by (rule hlEmitDerivation_nesting[OF em hlPremiseEnvironment_covers[OF assms]])
  then show ?thesis
    unfolding F
    by (simp add: hlFitchNestingFrom_append hlNesting_premiseFitchLines
        hlTopBoxes_premiseFitchLines)
qed

corollary hlDerivationToFitch_wellFormed:
  assumes "set (hlPremisesOf d) = set (hlOpenAssumptions d)"
  shows "hlFitchWellFormed (hlDerivationToFitch d)"
  using hlFitchNestingFrom_scope[OF hlDerivationToFitch_nesting[OF assms] subset_refl]
  by (simp add: hlFitchWellFormed_def)

text \<open>Assembled with the four conjuncts already proved in
  \<open>LF_HLW_Premise_Layout.thy\<close>, this closes structural well-formedness of the
  emitter for every ancestor-classified tree.\<close>

lemma hlClassified_premises_open:
  "set (hlPremisesOf (hlClassifyAssumptions {} d)) =
   set (hlOpenAssumptions (hlClassifyAssumptions {} d))"
  by (simp add: hlClassifyAssumptions_root_premises)

theorem hlClassifiedDerivationToFitch_nestedWellFormed:
  "hlFitchNestedWellFormed (hlDerivationToFitch (hlClassifyAssumptions {} d))"
  unfolding hlFitchNestedWellFormed_def
  using hlDerivationToFitch_nesting[OF hlClassified_premises_open]
    hlDerivationToFitch_premises_first[of "hlClassifyAssumptions {} d"]
    hlDerivationToFitch_positive_sorted[of "hlClassifyAssumptions {} d"]
    hlDerivationToFitch_concludesAtTop[of "hlClassifyAssumptions {} d"]
  by simp

theorem hlClassifiedDerivationToFitch_wellFormed:
  "hlFitchWellFormed (hlDerivationToFitch (hlClassifyAssumptions {} d))"
  by (rule hlDerivationToFitch_wellFormed[OF hlClassified_premises_open])

end
