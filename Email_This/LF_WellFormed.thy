(*  Title:      LF_WellFormed.thy

    Lemmas (L2) and (L3) of Section 6.1 of the paper.

    (L2) Citations precede uses.  "By induction on the derivation: the traversal
         emits every subderivation a node requires before the line applying it,
         so every line number a rule cites is smaller than the number of the
         line citing it."

    (L3) Every citation is in scope.  "By induction, using two facts about the
         traversal: premises are emitted at the outermost level before anything
         else, and an assumption is emitted as the first line of its own
         subproof, so that uses of it within that subproof are visible to it."

    Together they say that the construction of Definition 21 always yields a
    well-formed Fitch proof -- for every derivation, correct or not, since
    neither lemma is about the rules.  What remains of Conjecture 26 after this
    theory is (L4), that each rule transfers.
*)

theory LF_WellFormed
  imports LF_Unfold
begin

section \<open>Flattening an item list at a path\<close>

definition flatItems :: "fitch_item list \<Rightarrow> nat list \<Rightarrow> fline list" where
  "flatItems its path = concat (map (\<lambda>it. flatItem it path) its)"

definition subrefsItems :: "fitch_item list \<Rightarrow> nat list \<Rightarrow> (subref \<times> nat list) list" where
  "subrefsItems its path = concat (map (\<lambda>it. subrefsItem it path) its)"

lemma flatItems_simps [simp]:
  "flatItems [] path = []"
  "flatItems (it # its) path = flatItem it path @ flatItems its path"
  "flatItems (xs @ ys) path = flatItems xs path @ flatItems ys path"
  by (auto simp: flatItems_def)

lemma subrefsItems_simps [simp]:
  "subrefsItems [] path = []"
  "subrefsItems (it # its) path = subrefsItem it path @ subrefsItems its path"
  "subrefsItems (xs @ ys) path = subrefsItems xs path @ subrefsItems ys path"
  by (auto simp: subrefsItems_def)

lemma flatten_eq: "flatten F = flatItems F []"
  by (simp add: flatten_def flatItems_def)

lemma subrefs_eq: "subrefs F = subrefsItems F []"
  by (simp add: subrefs_def subrefsItems_def)

subsection \<open>Line numbers do not depend on the path\<close>

primrec itemNums :: "fitch_item \<Rightarrow> nat list"
    and subNums :: "subproof \<Rightarrow> nat list" where
  "itemNums (FLine n f r) = [n]"
| "itemNums (FSub s) = subNums s"
| "subNums (Subproof a fa body) = a # concat (map itemNums body)"

definition itemsNums :: "fitch_item list \<Rightarrow> nat list" where
  "itemsNums its = concat (map itemNums its)"

lemma itemsNums_simps [simp]:
  "itemsNums [] = []"
  "itemsNums (it # its) = itemNums it @ itemsNums its"
  "itemsNums (xs @ ys) = itemsNums xs @ itemsNums ys"
  by (auto simp: itemsNums_def)

lemma subNums_Subproof [simp]: "subNums (Subproof a fa body) = a # itemsNums body"
  by (simp add: itemsNums_def)

lemma flNum_flat_all:
  "\<forall>p. map flNum (flatItem it p) = itemNums it"
  "\<forall>q. map flNum (flatSub s q) = subNums s"
  by (induction it and s) (auto simp: map_concat cong: map_cong)

lemma flNum_flatItem [simp]: "map flNum (flatItem it p) = itemNums it"
  using flNum_flat_all(1) by blast

lemma flNum_flatSub [simp]: "map flNum (flatSub s q) = subNums s"
  using flNum_flat_all(2) by blast

lemma flNum_flatItems [simp]: "map flNum (flatItems its path) = itemsNums its"
  by (induction its) auto

section \<open>Prefixes\<close>

lemma is_prefix_iff: "is_prefix xs ys \<longleftrightarrow> (\<exists>zs. ys = xs @ zs)"
  by (induction xs ys rule: is_prefix.induct) auto

lemma is_prefix_appendI [simp]: "is_prefix xs (xs @ ys)"
  by (simp add: is_prefix_iff)

lemma is_prefix_trans: "is_prefix xs ys \<Longrightarrow> is_prefix ys zs \<Longrightarrow> is_prefix xs zs"
  by (auto simp: is_prefix_iff)

text \<open>Every line an item contributes lies at or below the path the item sits at.\<close>

lemma flat_scope_all:
  "\<forall>p. \<forall>fl \<in> set (flatItem it p). is_prefix p (flScope fl)"
  "\<forall>q. \<forall>fl \<in> set (flatSub s q). is_prefix q (flScope fl)"
  by (induction it and s) (fastforce simp: is_prefix_iff)+

lemma flatItem_scope: "fl \<in> set (flatItem it p) \<Longrightarrow> is_prefix p (flScope fl)"
  using flat_scope_all(1) by blast

lemma flatItems_scope: "fl \<in> set (flatItems its path) \<Longrightarrow> is_prefix path (flScope fl)"
  by (induction its) (auto dest: flatItem_scope)

section \<open>The environment\<close>

definition envNums :: "env \<Rightarrow> nat set" where
  "envNums G = set (map (fst \<circ> snd) G)"

definition labels :: "env \<Rightarrow> nat set" where
  "labels G = set (map fst G)"

lemma find_mem: "find P xs = Some x \<Longrightarrow> x \<in> set xs"
  by (induction xs) (auto split: if_splits)

lemma envLine_mem:
  assumes "a \<in> labels G" shows "envLine G a \<in> envNums G"
proof -
  from assms have "\<exists>e \<in> set G. fst e = a" by (auto simp: labels_def)
  then obtain e where "find (\<lambda>e. fst e = a) G = Some e"
    by (cases "find (\<lambda>e. fst e = a) G") (auto simp: find_None_iff)
  then show ?thesis
    using find_mem [of "\<lambda>e. fst e = a" G e] by (force simp: envLine_def envNums_def)
qed

text \<open>Every label a derivation still rests on is bound in the environment.  This
  is what makes the traversal's citations resolve, and the environment is set up
  at the outermost level so that it holds there.\<close>

definition boundIn :: "env \<Rightarrow> deriv \<Rightarrow> bool" where
  "boundIn G d \<longleftrightarrow> fst ` set (openAsms d) \<subseteq> labels G"

lemma boundIn_Cons: "boundIn G d \<Longrightarrow> boundIn (e # G) d"
  by (auto simp: boundIn_def labels_def)

section \<open>A block of items\<close>

text \<open>The traversal never writes a premise, and never writes an assumption other
  than as the head of a subproof.\<close>

primrec noPremItem :: "fitch_item \<Rightarrow> bool"
    and noPremSub :: "subproof \<Rightarrow> bool" where
  "noPremItem (FLine n f r) \<longleftrightarrow> r \<noteq> FPremise"
| "noPremItem (FSub s) \<longleftrightarrow> noPremSub s"
| "noPremSub (Subproof a fa body) \<longleftrightarrow> list_all noPremItem body"

text \<open>@{term "blockInv nx its nx'"}: the items @{term its} were emitted starting
  at line @{term nx} and stopping before @{term nx'}.\<close>

definition blockInv :: "nat \<Rightarrow> fitch_item list \<Rightarrow> nat \<Rightarrow> bool" where
  "blockInv nx its nx' \<longleftrightarrow>
     nx \<le> nx' \<and>
     (\<forall>n \<in> set (itemsNums its). nx \<le> n \<and> n < nx') \<and>
     sorted_wrt (<) (itemsNums its) \<and>
     list_all noAssumeLinesItem its \<and>
     list_all noPremItem its \<and>
     list_all lastIsLineItem its"

lemma blockInv_Nil [simp]: "blockInv nx [] nx"
  by (simp add: blockInv_def)

lemma blockInv_mono: "blockInv nx its m \<Longrightarrow> m \<le> nx' \<Longrightarrow> blockInv nx its nx'"
  by (fastforce simp: blockInv_def)

lemma blockInv_append:
  assumes "blockInv nx xs m" and "blockInv m ys nx'"
  shows "blockInv nx (xs @ ys) nx'"
  using assms by (fastforce simp: blockInv_def sorted_wrt_append)

lemma blockInv_line:
  assumes "blockInv nx its m" and "R \<noteq> FAssume" and "R \<noteq> FPremise"
  shows "blockInv nx (its @ [FLine m phi R]) (Suc m)"
  using assms by (fastforce simp: blockInv_def sorted_wrt_append)

lemma blockInv_sub:
  assumes "blockInv (Suc a) body m"
      and "body = [] \<or> (case last body of FLine _ _ _ \<Rightarrow> True | FSub _ \<Rightarrow> False)"
  shows "blockInv a [FSub (Subproof a fa body)] m"
proof -
  from assms(1) have le: "Suc a \<le> m"
    and rng: "\<forall>n \<in> set (itemsNums body). Suc a \<le> n \<and> n < m"
    and srt: "sorted_wrt (<) (itemsNums body)"
    and na: "list_all noAssumeLinesItem body"
    and np: "list_all noPremItem body"
    and ll: "list_all lastIsLineItem body"
    by (simp_all add: blockInv_def)
  from rng have above: "\<forall>n \<in> set (itemsNums body). a < n" by auto
  have nums: "itemsNums [FSub (Subproof a fa body)] = a # itemsNums body"
    by (simp add: itemsNums_def)
  show ?thesis
    unfolding blockInv_def nums
    using le rng srt na np ll above assms(2) by auto
qed

section \<open>The traversal's invariant\<close>

abbreviation eItems :: "nat \<Rightarrow> env \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> deriv \<Rightarrow> fitch_item list" where
  "eItems base G nx cnt d \<equiv> fst (emit base G nx cnt d)"

abbreviation eConcl :: "nat \<Rightarrow> env \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> deriv \<Rightarrow> nat" where
  "eConcl base G nx cnt d \<equiv> fst (snd (emit base G nx cnt d))"

abbreviation eNext :: "nat \<Rightarrow> env \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> deriv \<Rightarrow> nat" where
  "eNext base G nx cnt d \<equiv> fst (snd (snd (emit base G nx cnt d)))"

abbreviation eCnt :: "nat \<Rightarrow> env \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> deriv \<Rightarrow> nat" where
  "eCnt base G nx cnt d \<equiv> snd (snd (snd (emit base G nx cnt d)))"

definition emitInv :: "env \<Rightarrow> nat \<Rightarrow> fitch_item list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "emitInv G nx its c nx' \<longleftrightarrow>
     blockInv nx its nx' \<and>
     (if its = [] then nx' = nx \<and> c \<in> envNums G
      else Suc c = nx' \<and> (\<exists>f r. last its = FLine c f r))"

lemma emitInv_lastIsLine:
  "emitInv G nx its c nx' \<Longrightarrow> its = [] \<or> (case last its of FLine _ _ _ \<Rightarrow> True | FSub _ \<Rightarrow> False)"
  by (auto simp: emitInv_def split: if_splits)

text \<open>And the same fact for the whole proof: the premise lines are all
  @{const FLine}s, so a block that ends in a line leaves the assembled proof
  ending in one too.  This is @{const concludesAtTop}.\<close>

lemma concludesAtTop_premLines_append:
  assumes "emitInv G nx its c nx'"
  shows "concludesAtTop (premLines G @ its)"
proof (cases "its = []")
  case False
  then have "last (premLines G @ its) = last its" by simp
  with emitInv_lastIsLine [OF assms] False show ?thesis
    by (simp add: concludesAtTop_def)
next
  case True
  show ?thesis
  proof (cases "G = []")
    case True
    with \<open>its = []\<close> show ?thesis by (simp add: concludesAtTop_def premLines_def)
  next
    case False
    then have ne: "premLines G \<noteq> []" by (simp add: premLines_def)
    then have "last (premLines G) \<in> set (premLines G)" by simp
    then obtain e where "last (premLines G)
                           = FLine (fst (snd e)) (snd (snd e)) FPremise"
      by (auto simp: premLines_def)
    with \<open>its = []\<close> ne show ?thesis by (simp add: concludesAtTop_def)
  qed
qed

lemma emitInv_le: "emitInv G nx its c nx' \<Longrightarrow> nx \<le> nx'"
  by (simp add: emitInv_def blockInv_def)

section \<open>Combinators for the invariant\<close>

lemma emitInv_line0:
  assumes "R \<noteq> FAssume" and "R \<noteq> FPremise"
  shows "emitInv G nx [FLine nx phi R] nx (Suc nx)"
  using assms blockInv_line [OF blockInv_Nil, of R nx phi] by (simp add: emitInv_def)

lemma emitInv_line1:
  assumes "emitInv G nx i1 c1 nx1" and "R \<noteq> FAssume" and "R \<noteq> FPremise"
  shows "emitInv G nx (i1 @ [FLine nx1 phi R]) nx1 (Suc nx1)"
proof -
  from assms(1) have "blockInv nx i1 nx1" by (simp add: emitInv_def)
  from blockInv_line [OF this assms(2,3)] show ?thesis by (simp add: emitInv_def)
qed

lemma emitInv_line2:
  assumes "emitInv G nx i1 c1 nx1" and "emitInv G nx1 i2 c2 nx2"
      and "R \<noteq> FAssume" and "R \<noteq> FPremise"
  shows "emitInv G nx (i1 @ i2 @ [FLine nx2 phi R]) nx2 (Suc nx2)"
proof -
  from assms(1,2) have "blockInv nx (i1 @ i2) nx2"
    by (auto simp: emitInv_def intro: blockInv_append)
  from blockInv_line [OF this assms(3,4)] show ?thesis by (simp add: emitInv_def)
qed

text \<open>Closing a subproof: if its body did not end at the line the discharging
  rule names --- which happens exactly when the subderivation was a leaf, so that
  the conclusion is a line from outside --- a reiteration is added.\<close>

lemma closeSub_block:
  assumes "emitInv G' (Suc a) body c m" and "closeSub a psi body c m = (body', l, m')"
  shows "blockInv (Suc a) body' m'"
    and "body' = [] \<or> (case last body' of FLine _ _ _ \<Rightarrow> True | FSub _ \<Rightarrow> False)"
proof -
  from assms(1) have B: "blockInv (Suc a) body m" by (simp add: emitInv_def)
  from assms(1) have L: "body = [] \<or> (case last body of FLine _ _ _ \<Rightarrow> True | FSub _ \<Rightarrow> False)"
    by (rule emitInv_lastIsLine)
  from assms(2) have b': "body' = fst (closeSub a psi body c m)"
    and m': "m' = snd (snd (closeSub a psi body c m))" by simp_all
  show "blockInv (Suc a) body' m'"
    unfolding b' m'
    using B blockInv_line [OF B, of "FReit c" psi] by (simp add: closeSub_def)
  show "body' = [] \<or> (case last body' of FLine _ _ _ \<Rightarrow> True | FSub _ \<Rightarrow> False)"
    unfolding b' using L by (simp add: closeSub_def)
qed

lemma emitInv_discharge:
  assumes "emitInv G' (Suc a) body c m" and "closeSub a psi body c m = (body', l, m')"
      and "R \<noteq> FAssume" and "R \<noteq> FPremise"
  shows "emitInv G a [FSub (Subproof a fa body'), FLine m' phi R] m' (Suc m')"
proof -
  from blockInv_sub [OF closeSub_block(1) [OF assms(1,2)] closeSub_block(2) [OF assms(1,2)]]
  have "blockInv a [FSub (Subproof a fa body')] m'" .
  from blockInv_line [OF this assms(3,4)] show ?thesis by (simp add: emitInv_def)
qed

lemma emitInv_discharge1:
  assumes "emitInv G nx i0 c0 nx0"
      and "emitInv G' (Suc nx0) body c m" and "closeSub nx0 psi body c m = (body', l, m')"
      and "R \<noteq> FAssume" and "R \<noteq> FPremise"
  shows "emitInv G nx (i0 @ [FSub (Subproof nx0 fa body'), FLine m' phi R]) m' (Suc m')"
proof -
  from assms(1) have B0: "blockInv nx i0 nx0" by (simp add: emitInv_def)
  from blockInv_sub [OF closeSub_block(1) [OF assms(2,3)] closeSub_block(2) [OF assms(2,3)]]
  have "blockInv nx0 [FSub (Subproof nx0 fa body')] m'" .
  from blockInv_append [OF B0 this]
  have "blockInv nx (i0 @ [FSub (Subproof nx0 fa body')]) m'" .
  from blockInv_line [OF this assms(4,5)] show ?thesis by (simp add: emitInv_def)
qed

lemma emitInv_discharge2:
  assumes "emitInv G nx i0 c0 nx0"
      and "emitInv G1 (Suc nx0) b1 cc1 m1" and "closeSub nx0 psi1 b1 cc1 m1 = (b1', l1, n1)"
      and "emitInv G2 (Suc n1) b2 cc2 m2" and "closeSub n1 psi2 b2 cc2 m2 = (b2', l2, n2)"
      and "R \<noteq> FAssume" and "R \<noteq> FPremise"
  shows "emitInv G nx (i0 @ [FSub (Subproof nx0 f1 b1'), FSub (Subproof n1 f2 b2'),
                            FLine n2 phi R]) n2 (Suc n2)"
proof -
  from assms(1) have B0: "blockInv nx i0 nx0" by (simp add: emitInv_def)
  from blockInv_sub [OF closeSub_block(1) [OF assms(2,3)] closeSub_block(2) [OF assms(2,3)]]
  have S1: "blockInv nx0 [FSub (Subproof nx0 f1 b1')] n1" .
  from blockInv_sub [OF closeSub_block(1) [OF assms(4,5)] closeSub_block(2) [OF assms(4,5)]]
  have S2: "blockInv n1 [FSub (Subproof n1 f2 b2')] n2" .
  from blockInv_append [OF blockInv_append [OF B0 S1] S2]
  have "blockInv nx (i0 @ [FSub (Subproof nx0 f1 b1')] @ [FSub (Subproof n1 f2 b2')]) n2"
    by simp
  from blockInv_line [OF this assms(6,7)] show ?thesis by (simp add: emitInv_def)
qed

section \<open>Renaming does not disturb the labels\<close>

lemma boundIn_rnD: "boundIn G d \<Longrightarrow> boundIn G (rnD a b d)"
  by (simp add: boundIn_def openAsms_rnD image_image)

lemma boundIn_uniD: "boundIn G d \<Longrightarrow> boundIn G (uniD base cnt G' phi d)"
  by (auto simp: uniD_def boundIn_rnD split: option.splits)

lemma boundIn_exD: "boundIn G d1 \<Longrightarrow> boundIn G (exD base cnt G' ex f psi a d0 d1)"
  by (auto simp: exD_def boundIn_rnD split: option.splits)

section \<open>(L2) The traversal numbers its lines in order\<close>

lemma emit_inv_k:
  "\<forall>base G nx cnt d. size d \<le> k \<longrightarrow> boundIn G d \<longrightarrow>
      emitInv G nx (eItems base G nx cnt d) (eConcl base G nx cnt d) (eNext base G nx cnt d)"
proof (induction k)
  case 0
  show ?case
  proof (intro allI impI)
    fix base G nx cnt and d :: deriv
    assume "size d \<le> 0"
    then show "emitInv G nx (eItems base G nx cnt d) (eConcl base G nx cnt d)
                 (eNext base G nx cnt d)" by (cases d) simp
  qed
next
  case (Suc k)
  have IH: "\<And>base G nx cnt d. size d \<le> k \<Longrightarrow> boundIn G d \<Longrightarrow>
              emitInv G nx (eItems base G nx cnt d) (eConcl base G nx cnt d)
                (eNext base G nx cnt d)"
    using Suc.IH by blast
  show ?case
  proof (intro allI impI)
    fix base G nx cnt and d :: deriv
    assume sz: "size d \<le> Suc k" and bd: "boundIn G d"
    show "emitInv G nx (eItems base G nx cnt d) (eConcl base G nx cnt d)
            (eNext base G nx cnt d)"
    proof (cases d)
      case (Deriv phi r)
      show ?thesis
      proof (cases r)
        case (DAssume a)
        with Deriv bd have "a \<in> labels G" by (simp add: boundIn_def)
        then have "envLine G a \<in> envNums G" by (rule envLine_mem)
        with Deriv \<open>r = DAssume a\<close> show ?thesis by (simp add: emitInv_def)
      next
        case (DPremise a)
        with Deriv bd have "a \<in> labels G" by (simp add: boundIn_def)
        then have "envLine G a \<in> envNums G" by (rule envLine_mem)
        with Deriv \<open>r = DPremise a\<close> show ?thesis by (simp add: emitInv_def)
      next
        case (DMP d1 d2)
        obtain i1 c1 nx1 cnt1 where e1: "emit base G nx cnt d1 = (i1, c1, nx1, cnt1)"
          by (rule prod_cases4)
        obtain i2 c2 nx2 cnt2 where e2: "emit base G nx1 cnt1 d2 = (i2, c2, nx2, cnt2)"
          by (rule prod_cases4)
        from sz Deriv \<open>r = DMP d1 d2\<close> have s1: "size d1 \<le> k" and s2: "size d2 \<le> k" by simp_all
        from bd Deriv \<open>r = DMP d1 d2\<close> have b1: "boundIn G d1" and b2: "boundIn G d2"
          by (auto simp: boundIn_def)
        from IH [OF s1 b1, where base = base and nx = nx and cnt = cnt] e1
        have E1: "emitInv G nx i1 c1 nx1" by simp
        from IH [OF s2 b2, where base = base and nx = nx1 and cnt = cnt1] e2
        have E2: "emitInv G nx1 i2 c2 nx2" by simp
        have ed: "emit base G nx cnt d
                    = (i1 @ i2 @ [FLine nx2 phi (FMP c1 c2)], nx2, Suc nx2, cnt2)"
          using Deriv \<open>r = DMP d1 d2\<close> e1 e2 by simp
        have "emitInv G nx (i1 @ i2 @ [FLine nx2 phi (FMP c1 c2)]) nx2 (Suc nx2)"
          by (rule emitInv_line2 [OF E1 E2]) simp_all
        with ed show ?thesis by simp
      next
        case (DCP a fa d1)
        obtain b1 cc1 nx1 cnt1
          where e1: "emit base ((a, nx, fa) # G) (Suc nx) cnt d1 = (b1, cc1, nx1, cnt1)"
          by (rule prod_cases4)
        obtain b1' l1 nx2 where cs: "closeSub nx (dForm d1) b1 cc1 nx1 = (b1', l1, nx2)"
          by (rule prod_cases3)
        from sz Deriv \<open>r = DCP a fa d1\<close> have s1: "size d1 \<le> k" by simp
        from bd Deriv \<open>r = DCP a fa d1\<close> have b1: "boundIn ((a, nx, fa) # G) d1"
          by (auto simp: boundIn_def labels_def)
        from IH [OF s1 b1, where base = base and nx = "Suc nx" and cnt = cnt] e1
        have E1: "emitInv ((a, nx, fa) # G) (Suc nx) b1 cc1 nx1" by simp
        have ed: "emit base G nx cnt d
                    = ([FSub (Subproof nx fa b1'), FLine nx2 phi (FCP (nx, l1))],
                       nx2, Suc nx2, cnt1)"
          using Deriv \<open>r = DCP a fa d1\<close> e1 cs by simp
        have "emitInv G nx [FSub (Subproof nx fa b1'), FLine nx2 phi (FCP (nx, l1))] nx2 (Suc nx2)"
          by (rule emitInv_discharge [OF E1 cs]) simp_all
        with ed show ?thesis by simp
      next
        case (DRAA a fa d1)
        obtain b1 cc1 nx1 cnt1
          where e1: "emit base ((a, nx, fa) # G) (Suc nx) cnt d1 = (b1, cc1, nx1, cnt1)"
          by (rule prod_cases4)
        obtain b1' l1 nx2 where cs: "closeSub nx (dForm d1) b1 cc1 nx1 = (b1', l1, nx2)"
          by (rule prod_cases3)
        from sz Deriv \<open>r = DRAA a fa d1\<close> have s1: "size d1 \<le> k" by simp
        from bd Deriv \<open>r = DRAA a fa d1\<close> have b1: "boundIn ((a, nx, fa) # G) d1"
          by (auto simp: boundIn_def labels_def)
        from IH [OF s1 b1, where base = base and nx = "Suc nx" and cnt = cnt] e1
        have E1: "emitInv ((a, nx, fa) # G) (Suc nx) b1 cc1 nx1" by simp
        have ed: "emit base G nx cnt d
                    = ([FSub (Subproof nx fa b1'), FLine nx2 phi (FRAA (nx, l1))],
                       nx2, Suc nx2, cnt1)"
          using Deriv \<open>r = DRAA a fa d1\<close> e1 cs by simp
        have "emitInv G nx [FSub (Subproof nx fa b1'), FLine nx2 phi (FRAA (nx, l1))] nx2 (Suc nx2)"
          by (rule emitInv_discharge [OF E1 cs]) simp_all
        with ed show ?thesis by simp
      next
        case (DDN d1)
        obtain i1 c1 nx1 cnt1 where e1: "emit base G nx cnt d1 = (i1, c1, nx1, cnt1)"
          by (rule prod_cases4)
        from sz Deriv \<open>r = DDN d1\<close> have s1: "size d1 \<le> k" by simp
        from bd Deriv \<open>r = DDN d1\<close> have b1: "boundIn G d1" by (simp add: boundIn_def)
        from IH [OF s1 b1, where base = base and nx = nx and cnt = cnt] e1
        have E1: "emitInv G nx i1 c1 nx1" by simp
        have ed: "emit base G nx cnt d = (i1 @ [FLine nx1 phi (FDN c1)], nx1, Suc nx1, cnt1)"
          using Deriv \<open>r = DDN d1\<close> e1 by simp
        have "emitInv G nx (i1 @ [FLine nx1 phi (FDN c1)]) nx1 (Suc nx1)"
          by (rule emitInv_line1 [OF E1]) simp_all
        with ed show ?thesis by simp
      next
        case (DBotI d1 d2)
        obtain i1 c1 nx1 cnt1 where e1: "emit base G nx cnt d1 = (i1, c1, nx1, cnt1)"
          by (rule prod_cases4)
        obtain i2 c2 nx2 cnt2 where e2: "emit base G nx1 cnt1 d2 = (i2, c2, nx2, cnt2)"
          by (rule prod_cases4)
        from sz Deriv \<open>r = DBotI d1 d2\<close> have s1: "size d1 \<le> k" and s2: "size d2 \<le> k" by simp_all
        from bd Deriv \<open>r = DBotI d1 d2\<close> have b1: "boundIn G d1" and b2: "boundIn G d2"
          by (auto simp: boundIn_def)
        from IH [OF s1 b1, where base = base and nx = nx and cnt = cnt] e1
        have E1: "emitInv G nx i1 c1 nx1" by simp
        from IH [OF s2 b2, where base = base and nx = nx1 and cnt = cnt1] e2
        have E2: "emitInv G nx1 i2 c2 nx2" by simp
        have ed: "emit base G nx cnt d
                    = (i1 @ i2 @ [FLine nx2 phi (FBotI c1 c2)], nx2, Suc nx2, cnt2)"
          using Deriv \<open>r = DBotI d1 d2\<close> e1 e2 by simp
        have "emitInv G nx (i1 @ i2 @ [FLine nx2 phi (FBotI c1 c2)]) nx2 (Suc nx2)"
          by (rule emitInv_line2 [OF E1 E2]) simp_all
        with ed show ?thesis by simp
      next
        case (DAndIntro d1 d2)
        obtain i1 c1 nx1 cnt1 where e1: "emit base G nx cnt d1 = (i1, c1, nx1, cnt1)"
          by (rule prod_cases4)
        obtain i2 c2 nx2 cnt2 where e2: "emit base G nx1 cnt1 d2 = (i2, c2, nx2, cnt2)"
          by (rule prod_cases4)
        from sz Deriv \<open>r = DAndIntro d1 d2\<close> have s1: "size d1 \<le> k" and s2: "size d2 \<le> k" by simp_all
        from bd Deriv \<open>r = DAndIntro d1 d2\<close> have b1: "boundIn G d1" and b2: "boundIn G d2"
          by (auto simp: boundIn_def)
        from IH [OF s1 b1, where base = base and nx = nx and cnt = cnt] e1
        have E1: "emitInv G nx i1 c1 nx1" by simp
        from IH [OF s2 b2, where base = base and nx = nx1 and cnt = cnt1] e2
        have E2: "emitInv G nx1 i2 c2 nx2" by simp
        have ed: "emit base G nx cnt d
                    = (i1 @ i2 @ [FLine nx2 phi (FAndIntro c1 c2)], nx2, Suc nx2, cnt2)"
          using Deriv \<open>r = DAndIntro d1 d2\<close> e1 e2 by simp
        have "emitInv G nx (i1 @ i2 @ [FLine nx2 phi (FAndIntro c1 c2)]) nx2 (Suc nx2)"
          by (rule emitInv_line2 [OF E1 E2]) simp_all
        with ed show ?thesis by simp
      next
        case (DAndElimL d1)
        obtain i1 c1 nx1 cnt1 where e1: "emit base G nx cnt d1 = (i1, c1, nx1, cnt1)"
          by (rule prod_cases4)
        from sz Deriv \<open>r = DAndElimL d1\<close> have s1: "size d1 \<le> k" by simp
        from bd Deriv \<open>r = DAndElimL d1\<close> have b1: "boundIn G d1" by (simp add: boundIn_def)
        from IH [OF s1 b1, where base = base and nx = nx and cnt = cnt] e1
        have E1: "emitInv G nx i1 c1 nx1" by simp
        have ed: "emit base G nx cnt d = (i1 @ [FLine nx1 phi (FAndElimL c1)], nx1, Suc nx1, cnt1)"
          using Deriv \<open>r = DAndElimL d1\<close> e1 by simp
        have "emitInv G nx (i1 @ [FLine nx1 phi (FAndElimL c1)]) nx1 (Suc nx1)"
          by (rule emitInv_line1 [OF E1]) simp_all
        with ed show ?thesis by simp
      next
        case (DAndElimR d1)
        obtain i1 c1 nx1 cnt1 where e1: "emit base G nx cnt d1 = (i1, c1, nx1, cnt1)"
          by (rule prod_cases4)
        from sz Deriv \<open>r = DAndElimR d1\<close> have s1: "size d1 \<le> k" by simp
        from bd Deriv \<open>r = DAndElimR d1\<close> have b1: "boundIn G d1" by (simp add: boundIn_def)
        from IH [OF s1 b1, where base = base and nx = nx and cnt = cnt] e1
        have E1: "emitInv G nx i1 c1 nx1" by simp
        have ed: "emit base G nx cnt d = (i1 @ [FLine nx1 phi (FAndElimR c1)], nx1, Suc nx1, cnt1)"
          using Deriv \<open>r = DAndElimR d1\<close> e1 by simp
        have "emitInv G nx (i1 @ [FLine nx1 phi (FAndElimR c1)]) nx1 (Suc nx1)"
          by (rule emitInv_line1 [OF E1]) simp_all
        with ed show ?thesis by simp
      next
        case (DOrIntroL d1)
        obtain i1 c1 nx1 cnt1 where e1: "emit base G nx cnt d1 = (i1, c1, nx1, cnt1)"
          by (rule prod_cases4)
        from sz Deriv \<open>r = DOrIntroL d1\<close> have s1: "size d1 \<le> k" by simp
        from bd Deriv \<open>r = DOrIntroL d1\<close> have b1: "boundIn G d1" by (simp add: boundIn_def)
        from IH [OF s1 b1, where base = base and nx = nx and cnt = cnt] e1
        have E1: "emitInv G nx i1 c1 nx1" by simp
        have ed: "emit base G nx cnt d = (i1 @ [FLine nx1 phi (FOrIntroL c1)], nx1, Suc nx1, cnt1)"
          using Deriv \<open>r = DOrIntroL d1\<close> e1 by simp
        have "emitInv G nx (i1 @ [FLine nx1 phi (FOrIntroL c1)]) nx1 (Suc nx1)"
          by (rule emitInv_line1 [OF E1]) simp_all
        with ed show ?thesis by simp
      next
        case (DOrIntroR d1)
        obtain i1 c1 nx1 cnt1 where e1: "emit base G nx cnt d1 = (i1, c1, nx1, cnt1)"
          by (rule prod_cases4)
        from sz Deriv \<open>r = DOrIntroR d1\<close> have s1: "size d1 \<le> k" by simp
        from bd Deriv \<open>r = DOrIntroR d1\<close> have b1: "boundIn G d1" by (simp add: boundIn_def)
        from IH [OF s1 b1, where base = base and nx = nx and cnt = cnt] e1
        have E1: "emitInv G nx i1 c1 nx1" by simp
        have ed: "emit base G nx cnt d = (i1 @ [FLine nx1 phi (FOrIntroR c1)], nx1, Suc nx1, cnt1)"
          using Deriv \<open>r = DOrIntroR d1\<close> e1 by simp
        have "emitInv G nx (i1 @ [FLine nx1 phi (FOrIntroR c1)]) nx1 (Suc nx1)"
          by (rule emitInv_line1 [OF E1]) simp_all
        with ed show ?thesis by simp
      next
        case (DOrElim d0 a1 f1 d1 a2 f2 d2)
        obtain i0 c0 nx0 cnt0 where e0: "emit base G nx cnt d0 = (i0, c0, nx0, cnt0)"
          by (rule prod_cases4)
        obtain b1 cc1 m1 cnt1
          where e1: "emit base ((a1, nx0, f1) # G) (Suc nx0) cnt0 d1 = (b1, cc1, m1, cnt1)"
          by (rule prod_cases4)
        obtain b1' l1 n1 where cs1: "closeSub nx0 (dForm d1) b1 cc1 m1 = (b1', l1, n1)"
          by (rule prod_cases3)
        obtain b2 cc2 m2 cnt2
          where e2: "emit base ((a2, n1, f2) # G) (Suc n1) cnt1 d2 = (b2, cc2, m2, cnt2)"
          by (rule prod_cases4)
        obtain b2' l2 n2 where cs2: "closeSub n1 (dForm d2) b2 cc2 m2 = (b2', l2, n2)"
          by (rule prod_cases3)
        from sz Deriv \<open>r = DOrElim d0 a1 f1 d1 a2 f2 d2\<close>
        have s0: "size d0 \<le> k" and s1: "size d1 \<le> k" and s2: "size d2 \<le> k" by simp_all
        from bd Deriv \<open>r = DOrElim d0 a1 f1 d1 a2 f2 d2\<close>
        have b0: "boundIn G d0" and b1: "boundIn ((a1, nx0, f1) # G) d1"
         and b2: "boundIn ((a2, n1, f2) # G) d2"
          by (auto simp: boundIn_def labels_def)
        from IH [OF s0 b0, where base = base and nx = nx and cnt = cnt] e0
        have E0: "emitInv G nx i0 c0 nx0" by simp
        from IH [OF s1 b1, where base = base and nx = "Suc nx0" and cnt = cnt0] e1
        have E1: "emitInv ((a1, nx0, f1) # G) (Suc nx0) b1 cc1 m1" by simp
        from IH [OF s2 b2, where base = base and nx = "Suc n1" and cnt = cnt1] e2
        have E2: "emitInv ((a2, n1, f2) # G) (Suc n1) b2 cc2 m2" by simp
        have ed: "emit base G nx cnt d
                    = (i0 @ [FSub (Subproof nx0 f1 b1'), FSub (Subproof n1 f2 b2'),
                             FLine n2 phi (FOrElim c0 (nx0, l1) (n1, l2))], n2, Suc n2, cnt2)"
          using Deriv \<open>r = DOrElim d0 a1 f1 d1 a2 f2 d2\<close> e0 e1 cs1 e2 cs2 by simp
        have "emitInv G nx (i0 @ [FSub (Subproof nx0 f1 b1'), FSub (Subproof n1 f2 b2'),
                                  FLine n2 phi (FOrElim c0 (nx0, l1) (n1, l2))]) n2 (Suc n2)"
          by (rule emitInv_discharge2 [OF E0 E1 cs1 E2 cs2]) simp_all
        with ed show ?thesis by simp
      next
        case (DIffIntro d1 d2)
        obtain i1 c1 nx1 cnt1 where e1: "emit base G nx cnt d1 = (i1, c1, nx1, cnt1)"
          by (rule prod_cases4)
        obtain i2 c2 nx2 cnt2 where e2: "emit base G nx1 cnt1 d2 = (i2, c2, nx2, cnt2)"
          by (rule prod_cases4)
        from sz Deriv \<open>r = DIffIntro d1 d2\<close> have s1: "size d1 \<le> k" and s2: "size d2 \<le> k" by simp_all
        from bd Deriv \<open>r = DIffIntro d1 d2\<close> have b1: "boundIn G d1" and b2: "boundIn G d2"
          by (auto simp: boundIn_def)
        from IH [OF s1 b1, where base = base and nx = nx and cnt = cnt] e1
        have E1: "emitInv G nx i1 c1 nx1" by simp
        from IH [OF s2 b2, where base = base and nx = nx1 and cnt = cnt1] e2
        have E2: "emitInv G nx1 i2 c2 nx2" by simp
        have ed: "emit base G nx cnt d
                    = (i1 @ i2 @ [FLine nx2 phi (FIffIntro c1 c2)], nx2, Suc nx2, cnt2)"
          using Deriv \<open>r = DIffIntro d1 d2\<close> e1 e2 by simp
        have "emitInv G nx (i1 @ i2 @ [FLine nx2 phi (FIffIntro c1 c2)]) nx2 (Suc nx2)"
          by (rule emitInv_line2 [OF E1 E2]) simp_all
        with ed show ?thesis by simp
      next
        case (DIffElimL d1)
        obtain i1 c1 nx1 cnt1 where e1: "emit base G nx cnt d1 = (i1, c1, nx1, cnt1)"
          by (rule prod_cases4)
        from sz Deriv \<open>r = DIffElimL d1\<close> have s1: "size d1 \<le> k" by simp
        from bd Deriv \<open>r = DIffElimL d1\<close> have b1: "boundIn G d1" by (simp add: boundIn_def)
        from IH [OF s1 b1, where base = base and nx = nx and cnt = cnt] e1
        have E1: "emitInv G nx i1 c1 nx1" by simp
        have ed: "emit base G nx cnt d = (i1 @ [FLine nx1 phi (FIffElimL c1)], nx1, Suc nx1, cnt1)"
          using Deriv \<open>r = DIffElimL d1\<close> e1 by simp
        have "emitInv G nx (i1 @ [FLine nx1 phi (FIffElimL c1)]) nx1 (Suc nx1)"
          by (rule emitInv_line1 [OF E1]) simp_all
        with ed show ?thesis by simp
      next
        case (DIffElimR d1)
        obtain i1 c1 nx1 cnt1 where e1: "emit base G nx cnt d1 = (i1, c1, nx1, cnt1)"
          by (rule prod_cases4)
        from sz Deriv \<open>r = DIffElimR d1\<close> have s1: "size d1 \<le> k" by simp
        from bd Deriv \<open>r = DIffElimR d1\<close> have b1: "boundIn G d1" by (simp add: boundIn_def)
        from IH [OF s1 b1, where base = base and nx = nx and cnt = cnt] e1
        have E1: "emitInv G nx i1 c1 nx1" by simp
        have ed: "emit base G nx cnt d = (i1 @ [FLine nx1 phi (FIffElimR c1)], nx1, Suc nx1, cnt1)"
          using Deriv \<open>r = DIffElimR d1\<close> e1 by simp
        have "emitInv G nx (i1 @ [FLine nx1 phi (FIffElimR c1)]) nx1 (Suc nx1)"
          by (rule emitInv_line1 [OF E1]) simp_all
        with ed show ?thesis by simp
      next
        case (DForallElim d1)
        obtain i1 c1 nx1 cnt1 where e1: "emit base G nx cnt d1 = (i1, c1, nx1, cnt1)"
          by (rule prod_cases4)
        from sz Deriv \<open>r = DForallElim d1\<close> have s1: "size d1 \<le> k" by simp
        from bd Deriv \<open>r = DForallElim d1\<close> have b1: "boundIn G d1" by (simp add: boundIn_def)
        from IH [OF s1 b1, where base = base and nx = nx and cnt = cnt] e1
        have E1: "emitInv G nx i1 c1 nx1" by simp
        have ed: "emit base G nx cnt d = (i1 @ [FLine nx1 phi (FForallElim c1)], nx1, Suc nx1, cnt1)"
          using Deriv \<open>r = DForallElim d1\<close> e1 by simp
        have "emitInv G nx (i1 @ [FLine nx1 phi (FForallElim c1)]) nx1 (Suc nx1)"
          by (rule emitInv_line1 [OF E1]) simp_all
        with ed show ?thesis by simp
      next
        case (DForallIntro d1)
        obtain i1 c1 nx1 cnt1
          where e1: "emit base G nx (uniCnt cnt G phi d1) (uniD base cnt G phi d1)
                       = (i1, c1, nx1, cnt1)"
          by (rule prod_cases4)
        from sz Deriv \<open>r = DForallIntro d1\<close> have s1: "size (uniD base cnt G phi d1) \<le> k"
          by (simp add: size_uniD)
        from bd Deriv \<open>r = DForallIntro d1\<close> have "boundIn G d1"
          by (simp add: boundIn_def)
        then have b1: "boundIn G (uniD base cnt G phi d1)" by (rule boundIn_uniD)
        from IH [OF s1 b1, where base = base and nx = nx and cnt = "uniCnt cnt G phi d1"] e1
        have E1: "emitInv G nx i1 c1 nx1" by simp
        have ed: "emit base G nx cnt d
                    = (i1 @ [FLine nx1 phi (FForallIntro c1)], nx1, Suc nx1, cnt1)"
          using Deriv \<open>r = DForallIntro d1\<close> e1 by simp
        have "emitInv G nx (i1 @ [FLine nx1 phi (FForallIntro c1)]) nx1 (Suc nx1)"
          by (rule emitInv_line1 [OF E1]) simp_all
        with ed show ?thesis by simp
      next
        case (DExistsIntro d1)
        obtain i1 c1 nx1 cnt1 where e1: "emit base G nx cnt d1 = (i1, c1, nx1, cnt1)"
          by (rule prod_cases4)
        from sz Deriv \<open>r = DExistsIntro d1\<close> have s1: "size d1 \<le> k" by simp
        from bd Deriv \<open>r = DExistsIntro d1\<close> have b1: "boundIn G d1" by (simp add: boundIn_def)
        from IH [OF s1 b1, where base = base and nx = nx and cnt = cnt] e1
        have E1: "emitInv G nx i1 c1 nx1" by simp
        have ed: "emit base G nx cnt d = (i1 @ [FLine nx1 phi (FExistsIntro c1)], nx1, Suc nx1, cnt1)"
          using Deriv \<open>r = DExistsIntro d1\<close> e1 by simp
        have "emitInv G nx (i1 @ [FLine nx1 phi (FExistsIntro c1)]) nx1 (Suc nx1)"
          by (rule emitInv_line1 [OF E1]) simp_all
        with ed show ?thesis by simp
      next
        case (DExistsElim d0 a f d1)
        obtain i0 c0 nx0 cnt0 where e0: "emit base G nx cnt d0 = (i0, c0, nx0, cnt0)"
          by (rule prod_cases4)
        let ?f' = "exF base cnt0 G (dForm d0) f phi a d0 d1"
        let ?d1 = "exD base cnt0 G (dForm d0) f phi a d0 d1"
        obtain b1 cc1 m1 cnt1
          where e1: "emit base ((a, nx0, ?f') # G) (Suc nx0)
                       (exCnt cnt0 G (dForm d0) f phi a d0 d1) ?d1 = (b1, cc1, m1, cnt1)"
          by (rule prod_cases4)
        obtain b1' l1 n1 where cs: "closeSub nx0 phi b1 cc1 m1 = (b1', l1, n1)"
          by (rule prod_cases3)
        from sz Deriv \<open>r = DExistsElim d0 a f d1\<close>
        have s0: "size d0 \<le> k" and s1: "size ?d1 \<le> k" by (simp_all add: size_exD)
        from bd Deriv \<open>r = DExistsElim d0 a f d1\<close>
        have b0: "boundIn G d0" and bb: "boundIn ((a, nx0, ?f') # G) d1"
          by (auto simp: boundIn_def labels_def)
        from bb have b1: "boundIn ((a, nx0, ?f') # G) ?d1" by (rule boundIn_exD)
        from IH [OF s0 b0, where base = base and nx = nx and cnt = cnt] e0
        have E0: "emitInv G nx i0 c0 nx0" by simp
        from IH [OF s1 b1, where base = base and nx = "Suc nx0"
                 and cnt = "exCnt cnt0 G (dForm d0) f phi a d0 d1"] e1
        have E1: "emitInv ((a, nx0, ?f') # G) (Suc nx0) b1 cc1 m1" by simp
        have ed: "emit base G nx cnt d
                    = (i0 @ [FSub (Subproof nx0 ?f' b1'),
                             FLine n1 phi (FExistsElim c0 (nx0, l1))], n1, Suc n1, cnt1)"
          using Deriv \<open>r = DExistsElim d0 a f d1\<close> e0 e1 cs by simp
        have "emitInv G nx (i0 @ [FSub (Subproof nx0 ?f' b1'),
                                  FLine n1 phi (FExistsElim c0 (nx0, l1))]) n1 (Suc n1)"
          by (rule emitInv_discharge1 [OF E0 E1 cs]) simp_all
        with ed show ?thesis by simp
      next
        case DEqIntro
        have ed: "emit base G nx cnt d = ([FLine nx phi FEqIntro], nx, Suc nx, cnt)"
          using Deriv \<open>r = DEqIntro\<close> by simp
        have "emitInv G nx [FLine nx phi FEqIntro] nx (Suc nx)"
          by (rule emitInv_line0) simp_all
        with ed show ?thesis by simp
      next
        case (DEqElim d1 d2)
        obtain i1 c1 nx1 cnt1 where e1: "emit base G nx cnt d1 = (i1, c1, nx1, cnt1)"
          by (rule prod_cases4)
        obtain i2 c2 nx2 cnt2 where e2: "emit base G nx1 cnt1 d2 = (i2, c2, nx2, cnt2)"
          by (rule prod_cases4)
        from sz Deriv \<open>r = DEqElim d1 d2\<close> have s1: "size d1 \<le> k" and s2: "size d2 \<le> k" by simp_all
        from bd Deriv \<open>r = DEqElim d1 d2\<close> have b1: "boundIn G d1" and b2: "boundIn G d2"
          by (auto simp: boundIn_def)
        from IH [OF s1 b1, where base = base and nx = nx and cnt = cnt] e1
        have E1: "emitInv G nx i1 c1 nx1" by simp
        from IH [OF s2 b2, where base = base and nx = nx1 and cnt = cnt1] e2
        have E2: "emitInv G nx1 i2 c2 nx2" by simp
        have ed: "emit base G nx cnt d
                    = (i1 @ i2 @ [FLine nx2 phi (FEqElim c1 c2)], nx2, Suc nx2, cnt2)"
          using Deriv \<open>r = DEqElim d1 d2\<close> e1 e2 by simp
        have "emitInv G nx (i1 @ i2 @ [FLine nx2 phi (FEqElim c1 c2)]) nx2 (Suc nx2)"
          by (rule emitInv_line2 [OF E1 E2]) simp_all
        with ed show ?thesis by simp
      next
        case (DReit d1)
        obtain i1 c1 nx1 cnt1 where e1: "emit base G nx cnt d1 = (i1, c1, nx1, cnt1)"
          by (rule prod_cases4)
        from sz Deriv \<open>r = DReit d1\<close> have s1: "size d1 \<le> k" by simp
        from bd Deriv \<open>r = DReit d1\<close> have b1: "boundIn G d1" by (simp add: boundIn_def)
        from IH [OF s1 b1, where base = base and nx = nx and cnt = cnt] e1
        have E1: "emitInv G nx i1 c1 nx1" by simp
        have ed: "emit base G nx cnt d = (i1 @ [FLine nx1 phi (FReit c1)], nx1, Suc nx1, cnt1)"
          using Deriv \<open>r = DReit d1\<close> e1 by simp
        have "emitInv G nx (i1 @ [FLine nx1 phi (FReit c1)]) nx1 (Suc nx1)"
          by (rule emitInv_line1 [OF E1]) simp_all
        with ed show ?thesis by simp
      qed
    qed
  qed
qed

lemma emit_inv:
  "boundIn G d \<Longrightarrow>
     emitInv G nx (eItems base G nx cnt d) (eConcl base G nx cnt d) (eNext base G nx cnt d)"
  using emit_inv_k [of "size d"] by blast

section \<open>(L3) Every citation is in scope\<close>

text \<open>The traversal makes exactly two kinds of citation: to a line it has itself
  emitted at the same level, and to a line the environment binds --- a premise,
  or the assumption of an enclosing subproof.  \<open>citeInv\<close> below says that every
  citation is one of the two, that the first kind is visible (its scope path is a
  prefix), and that every line cited is earlier.  Nothing else can be cited,
  because the only way a subderivation reaches outside itself is through a
  @{const DAssume} or @{const DPremise} leaf, and those read the environment.\<close>

definition envBelow :: "env \<Rightarrow> nat \<Rightarrow> bool" where
  "envBelow G nx \<longleftrightarrow> (\<forall>n \<in> envNums G. n < nx)"

lemma envBelow_mono: "envBelow G nx \<Longrightarrow> nx \<le> m \<Longrightarrow> envBelow G m"
  by (fastforce simp: envBelow_def)

lemma envBelow_Cons: "envBelow G a \<Longrightarrow> envBelow ((lab, a, fa) # G) (Suc a)"
  by (auto simp: envBelow_def envNums_def)

lemma envNums_Cons [simp]: "envNums ((lab, a, fa) # G) = insert a (envNums G)"
  by (simp add: envNums_def)

definition citeInv :: "env \<Rightarrow> nat list \<Rightarrow> fitch_item list \<Rightarrow> bool" where
  "citeInv G path its \<longleftrightarrow>
     (\<forall>fl \<in> set (flatItems its path).
        (\<forall>m \<in> set (fCitedLines (flRule fl)).
            m < flNum fl \<and>
            ((\<exists>fl' \<in> set (flatItems its path).
                 flNum fl' = m \<and> is_prefix (flScope fl') (flScope fl))
             \<or> m \<in> envNums G)) \<and>
        (\<forall>ac \<in> set (fCitedSubs (flRule fl)).
            snd ac < flNum fl \<and> (ac, flScope fl) \<in> set (subrefsItems its path)))"

subsection \<open>Reading the pieces\<close>

lemma flatItems_FSub [simp]:
  "flatItems [FSub (Subproof a fa body)] path
     = FL a fa FAssume (path @ [a]) # flatItems body (path @ [a])"
  by (simp add: flatItems_def)

lemma subrefsItems_FSub [simp]:
  "subrefsItems [FSub (Subproof a fa body)] path
     = ((a, subLastLine (Subproof a fa body)), path) # subrefsItems body (path @ [a])"
  by (simp add: subrefsItems_def)

lemma flatItems_mem:
  "it \<in> set its \<Longrightarrow> fl \<in> set (flatItem it path) \<Longrightarrow> fl \<in> set (flatItems its path)"
  by (induction its) auto

subsection \<open>What a subderivation's conclusion line is good for\<close>

lemma cite_witness:
  assumes "emitInv G nx its c nx'" and "envBelow G nx" and "nx' \<le> n"
  shows "c < n"
    and "(\<exists>fl' \<in> set (flatItems its path). flNum fl' = c \<and> is_prefix (flScope fl') path)
         \<or> c \<in> envNums G"
proof -
  show "c < n"
  proof (cases "its = []")
    case True
    with assms(1) have "nx' = nx" and "c \<in> envNums G" by (simp_all add: emitInv_def)
    with assms(2,3) show ?thesis by (auto simp: envBelow_def)
  next
    case False
    with assms(1) have "Suc c = nx'" by (simp add: emitInv_def)
    with assms(3) show ?thesis by simp
  qed
  show "(\<exists>fl' \<in> set (flatItems its path). flNum fl' = c \<and> is_prefix (flScope fl') path)
         \<or> c \<in> envNums G"
  proof (cases "its = []")
    case True
    with assms(1) show ?thesis by (simp add: emitInv_def)
  next
    case False
    with assms(1) obtain f r where l: "last its = FLine c f r" by (auto simp: emitInv_def)
    from False have "last its \<in> set its" by simp
    with l have "FL c f r path \<in> set (flatItems its path)"
      by (auto intro: flatItems_mem [where it = "FLine c f r"])
    then have "\<exists>fl' \<in> set (flatItems its path).
                  flNum fl' = c \<and> is_prefix (flScope fl') path"
      by (intro bexI [where x = "FL c f r path"]) simp_all
    then show ?thesis ..
  qed
qed

subsection \<open>Combinators\<close>

lemma citeInv_Nil [simp]: "citeInv G path []"
  by (simp add: citeInv_def)

lemma citeInv_append:
  assumes "citeInv G path xs" and "citeInv G path ys"
  shows "citeInv G path (xs @ ys)"
  using assms unfolding citeInv_def by fastforce

lemma citeInv_app_line:
  assumes "citeInv G path its"
      and "\<forall>m \<in> set (fCitedLines R). m < n \<and>
             ((\<exists>fl' \<in> set (flatItems its path). flNum fl' = m \<and> is_prefix (flScope fl') path)
              \<or> m \<in> envNums G)"
      and "\<forall>ac \<in> set (fCitedSubs R). snd ac < n \<and> (ac, path) \<in> set (subrefsItems its path)"
  shows "citeInv G path (its @ [FLine n phi R])"
  using assms unfolding citeInv_def by fastforce

text \<open>Lifting a subproof.  Inside it, the assumption is read from the
  environment; outside, it is a line of the level the subproof sits at, and it is
  visible to everything in the subproof because its scope path is a prefix of
  theirs.  This is the half of (L3) about assumptions.\<close>

lemma citeInv_sub:
  assumes "citeInv G' (path @ [a]) body" and "envNums G' \<subseteq> insert a (envNums G)"
  shows "citeInv G path [FSub (Subproof a fa body)]"
proof -
  have "\<forall>fl \<in> set (flatItems body (path @ [a])). is_prefix (path @ [a]) (flScope fl)"
    by (auto dest: flatItems_scope)
  with assms show ?thesis
    unfolding citeInv_def flatItems_FSub subrefsItems_FSub by fastforce
qed

text \<open>Closing a subproof may add a reiteration, which cites the line the body
  ended at.\<close>

lemma citeInv_closeSub:
  assumes "citeInv G' q body" and "emitInv G' (Suc a) body c m"
      and "envBelow G' (Suc a)" and "closeSub a psi body c m = (body', l, m')"
  shows "citeInv G' q body'"
proof (cases "endsAt body a c")
  case True
  with assms(1,4) show ?thesis by (simp add: closeSub_def)
next
  case False
  with assms(4) have b: "body' = fst (closeSub a psi body c m)" by simp
  have "citeInv G' q (body @ [FLine m psi (FReit c)])"
    by (rule citeInv_app_line [OF assms(1)])
       (auto simp: cite_witness(1) [OF assms(2,3) order_refl]
                   cite_witness(2) [OF assms(2,3) order_refl])
  with False b show ?thesis by (simp add: closeSub_def)
qed

subsection \<open>The shapes the traversal builds\<close>

lemma subLastLine_cs:
  assumes "closeSub a psi body c m = (body', l, m')"
  shows "subLastLine (Subproof a fa body') = l"
  using subLastLine_closeSub [where a = a and fa = fa and psi = psi and body = body
                                and c = c and nxt = m] assms
  by simp

lemma closeSub_lt:
  assumes "emitInv G' (Suc a) body c m" and "envBelow G' (Suc a)"
      and "closeSub a psi body c m = (body', l, m')"
  shows "l < m'"
proof (cases "endsAt body a c")
  case True
  from assms(3) have "l = fst (snd (closeSub a psi body c m))"
    and "m' = snd (snd (closeSub a psi body c m))" by simp_all
  with True cite_witness(1) [OF assms(1,2) order_refl] show ?thesis
    by (simp add: closeSub_def)
next
  case False
  from assms(3) have "l = fst (snd (closeSub a psi body c m))"
    and "m' = snd (snd (closeSub a psi body c m))" by simp_all
  with False show ?thesis by (simp add: closeSub_def)
qed

lemma citeInv_step0:
  assumes "fCitedLines R = []" and "fCitedSubs R = []"
  shows "citeInv G path [FLine n phi R]"
proof -
  have "citeInv G path ([] @ [FLine n phi R])"
    by (rule citeInv_app_line [OF citeInv_Nil]) (simp_all add: assms)
  then show ?thesis by simp
qed

lemma citeInv_step1:
  assumes C1: "citeInv G path i1" and E1: "emitInv G nx i1 c1 nx1" and eb: "envBelow G nx"
      and R1: "set (fCitedLines R) \<subseteq> {c1}" and R2: "fCitedSubs R = []"
  shows "citeInv G path (i1 @ [FLine nx1 phi R])"
proof (rule citeInv_app_line [OF C1])
  show "\<forall>m \<in> set (fCitedLines R). m < nx1 \<and>
          ((\<exists>fl' \<in> set (flatItems i1 path). flNum fl' = m \<and> is_prefix (flScope fl') path)
           \<or> m \<in> envNums G)"
    using R1 cite_witness(1) [OF E1 eb order_refl]
          cite_witness(2) [OF E1 eb order_refl, where path = path] by auto
next
  show "\<forall>ac \<in> set (fCitedSubs R). snd ac < nx1 \<and> (ac, path) \<in> set (subrefsItems i1 path)"
    by (simp add: R2)
qed

lemma citeInv_step2:
  assumes C1: "citeInv G path i1" and C2: "citeInv G path i2"
      and E1: "emitInv G nx i1 c1 nx1" and E2: "emitInv G nx1 i2 c2 nx2" and eb: "envBelow G nx"
      and R1: "set (fCitedLines R) \<subseteq> {c1, c2}" and R2: "fCitedSubs R = []"
  shows "citeInv G path (i1 @ i2 @ [FLine nx2 phi R])"
proof -
  from eb emitInv_le [OF E1] have eb1: "envBelow G nx1" by (rule envBelow_mono)
  have le2: "nx1 \<le> nx2" by (rule emitInv_le [OF E2])
  have "citeInv G path ((i1 @ i2) @ [FLine nx2 phi R])"
  proof (rule citeInv_app_line [OF citeInv_append [OF C1 C2]])
    show "\<forall>m \<in> set (fCitedLines R). m < nx2 \<and>
            ((\<exists>fl' \<in> set (flatItems (i1 @ i2) path).
                 flNum fl' = m \<and> is_prefix (flScope fl') path) \<or> m \<in> envNums G)"
      using R1 cite_witness(1) [OF E1 eb le2]
            cite_witness(2) [OF E1 eb le2, where path = path]
            cite_witness(1) [OF E2 eb1 order_refl]
            cite_witness(2) [OF E2 eb1 order_refl, where path = path] by auto
  next
    show "\<forall>ac \<in> set (fCitedSubs R). snd ac < nx2
            \<and> (ac, path) \<in> set (subrefsItems (i1 @ i2) path)"
      by (simp add: R2)
  qed
  then show ?thesis by simp
qed

lemma citeInv_CP:
  assumes B: "citeInv G' (path @ [a]) body'" and env: "envNums G' \<subseteq> insert a (envNums G)"
      and sl: "subLastLine (Subproof a fa body') = l" and lt: "l < n"
      and R1: "fCitedLines R = []" and R2: "set (fCitedSubs R) \<subseteq> {(a, l)}"
  shows "citeInv G path [FSub (Subproof a fa body'), FLine n phi R]"
proof -
  from citeInv_sub [OF B env, where fa = fa]
  have S: "citeInv G path [FSub (Subproof a fa body')]" .
  have "citeInv G path ([FSub (Subproof a fa body')] @ [FLine n phi R])"
  proof (rule citeInv_app_line [OF S])
    show "\<forall>m \<in> set (fCitedLines R). m < n \<and>
            ((\<exists>fl' \<in> set (flatItems [FSub (Subproof a fa body')] path).
                 flNum fl' = m \<and> is_prefix (flScope fl') path) \<or> m \<in> envNums G)"
      by (simp add: R1)
  next
    show "\<forall>ac \<in> set (fCitedSubs R). snd ac < n
            \<and> (ac, path) \<in> set (subrefsItems [FSub (Subproof a fa body')] path)"
      using R2 sl lt by auto
  qed
  then show ?thesis by simp
qed

lemma citeInv_EE:
  assumes C0: "citeInv G path i0" and E0: "emitInv G nx i0 c0 nx0" and eb: "envBelow G nx"
      and B: "citeInv G' (path @ [nx0]) body'" and env: "envNums G' \<subseteq> insert nx0 (envNums G)"
      and sl: "subLastLine (Subproof nx0 fa body') = l" and lt: "l < n" and le: "nx0 \<le> n"
      and R1: "set (fCitedLines R) \<subseteq> {c0}" and R2: "set (fCitedSubs R) \<subseteq> {(nx0, l)}"
  shows "citeInv G path (i0 @ [FSub (Subproof nx0 fa body'), FLine n phi R])"
proof -
  from citeInv_sub [OF B env, where fa = fa]
  have S: "citeInv G path [FSub (Subproof nx0 fa body')]" .
  have "citeInv G path ((i0 @ [FSub (Subproof nx0 fa body')]) @ [FLine n phi R])"
  proof (rule citeInv_app_line [OF citeInv_append [OF C0 S]])
    show "\<forall>m \<in> set (fCitedLines R). m < n \<and>
            ((\<exists>fl' \<in> set (flatItems (i0 @ [FSub (Subproof nx0 fa body')]) path).
                 flNum fl' = m \<and> is_prefix (flScope fl') path) \<or> m \<in> envNums G)"
      using R1 cite_witness(1) [OF E0 eb le]
            cite_witness(2) [OF E0 eb le, where path = path] by auto
  next
    show "\<forall>ac \<in> set (fCitedSubs R). snd ac < n
            \<and> (ac, path) \<in> set (subrefsItems (i0 @ [FSub (Subproof nx0 fa body')]) path)"
      using R2 sl lt by auto
  qed
  then show ?thesis by simp
qed

lemma citeInv_OE:
  assumes C0: "citeInv G path i0" and E0: "emitInv G nx i0 c0 nx0" and eb: "envBelow G nx"
      and B1: "citeInv G1 (path @ [nx0]) b1'" and env1: "envNums G1 \<subseteq> insert nx0 (envNums G)"
      and sl1: "subLastLine (Subproof nx0 f1 b1') = l1" and lt1: "l1 < n"
      and B2: "citeInv G2 (path @ [n1]) b2'" and env2: "envNums G2 \<subseteq> insert n1 (envNums G)"
      and sl2: "subLastLine (Subproof n1 f2 b2') = l2" and lt2: "l2 < n"
      and le: "nx0 \<le> n"
      and R1: "set (fCitedLines R) \<subseteq> {c0}"
      and R2: "set (fCitedSubs R) \<subseteq> {(nx0, l1), (n1, l2)}"
  shows "citeInv G path
           (i0 @ [FSub (Subproof nx0 f1 b1'), FSub (Subproof n1 f2 b2'), FLine n phi R])"
proof -
  from citeInv_sub [OF B1 env1, where fa = f1]
  have S1: "citeInv G path [FSub (Subproof nx0 f1 b1')]" .
  from citeInv_sub [OF B2 env2, where fa = f2]
  have S2: "citeInv G path [FSub (Subproof n1 f2 b2')]" .
  let ?its = "(i0 @ [FSub (Subproof nx0 f1 b1')]) @ [FSub (Subproof n1 f2 b2')]"
  have "citeInv G path (?its @ [FLine n phi R])"
  proof (rule citeInv_app_line [OF citeInv_append [OF citeInv_append [OF C0 S1] S2]])
    show "\<forall>m \<in> set (fCitedLines R). m < n \<and>
            ((\<exists>fl' \<in> set (flatItems ?its path).
                 flNum fl' = m \<and> is_prefix (flScope fl') path) \<or> m \<in> envNums G)"
      using R1 cite_witness(1) [OF E0 eb le]
            cite_witness(2) [OF E0 eb le, where path = path] by auto
  next
    show "\<forall>ac \<in> set (fCitedSubs R). snd ac < n
            \<and> (ac, path) \<in> set (subrefsItems ?its path)"
      using R2 sl1 lt1 sl2 lt2 by auto
  qed
  then show ?thesis by simp
qed

lemma closeSub_le: "closeSub a psi body c m = (body', l, m') \<Longrightarrow> m \<le> m'"
proof -
  assume cs: "closeSub a psi body c m = (body', l, m')"
  then have "m' = snd (snd (closeSub a psi body c m))" by simp
  then show ?thesis by (simp add: closeSub_def)
qed

subsection \<open>The induction\<close>

lemma emit_cite_k:
  "\<forall>base G nx cnt d path. size d \<le> k \<longrightarrow> boundIn G d \<longrightarrow> envBelow G nx \<longrightarrow>
      citeInv G path (eItems base G nx cnt d)"
proof (induction k)
  case 0
  show ?case
  proof (intro allI impI)
    fix base G nx cnt path and d :: deriv
    assume "size d \<le> 0"
    then show "citeInv G path (eItems base G nx cnt d)" by (cases d) simp
  qed
next
  case (Suc k)
  have IH: "\<And>base G nx cnt d path. size d \<le> k \<Longrightarrow> boundIn G d \<Longrightarrow> envBelow G nx \<Longrightarrow>
              citeInv G path (eItems base G nx cnt d)"
    using Suc.IH by blast
  show ?case
  proof (intro allI impI)
    fix base G nx cnt path and d :: deriv
    assume sz: "size d \<le> Suc k" and bd: "boundIn G d" and eb: "envBelow G nx"
    show "citeInv G path (eItems base G nx cnt d)"
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
        obtain i1 c1 nx1 cnt1 where e1: "emit base G nx cnt d1 = (i1, c1, nx1, cnt1)"
          by (rule prod_cases4)
        obtain i2 c2 nx2 cnt2 where e2: "emit base G nx1 cnt1 d2 = (i2, c2, nx2, cnt2)"
          by (rule prod_cases4)
        from sz Deriv \<open>r = DMP d1 d2\<close> have s1: "size d1 \<le> k" and s2: "size d2 \<le> k" by simp_all
        from bd Deriv \<open>r = DMP d1 d2\<close> have b1: "boundIn G d1" and b2: "boundIn G d2"
          by (auto simp: boundIn_def)
        from emit_inv [OF b1, where base = base and nx = nx and cnt = cnt] e1
        have E1: "emitInv G nx i1 c1 nx1" by simp
        from eb emitInv_le [OF E1] have eb1: "envBelow G nx1" by (rule envBelow_mono)
        from emit_inv [OF b2, where base = base and nx = nx1 and cnt = cnt1] e2
        have E2: "emitInv G nx1 i2 c2 nx2" by simp
        from IH [OF s1 b1 eb, where base = base and cnt = cnt and path = path] e1
        have C1: "citeInv G path i1" by simp
        from IH [OF s2 b2 eb1, where base = base and cnt = cnt1 and path = path] e2
        have C2: "citeInv G path i2" by simp
        have ed: "emit base G nx cnt d
                    = (i1 @ i2 @ [FLine nx2 phi (FMP c1 c2)], nx2, Suc nx2, cnt2)"
          using Deriv \<open>r = DMP d1 d2\<close> e1 e2 by simp
        have "citeInv G path (i1 @ i2 @ [FLine nx2 phi (FMP c1 c2)])"
          by (rule citeInv_step2 [OF C1 C2 E1 E2 eb]) simp_all
        with ed show ?thesis by simp
      next
        case (DCP a fa d1)
        obtain b1 cc1 nx1 cnt1
          where e1: "emit base ((a, nx, fa) # G) (Suc nx) cnt d1 = (b1, cc1, nx1, cnt1)"
          by (rule prod_cases4)
        obtain b1' l1 nx2 where cs: "closeSub nx (dForm d1) b1 cc1 nx1 = (b1', l1, nx2)"
          by (rule prod_cases3)
        from sz Deriv \<open>r = DCP a fa d1\<close> have s1: "size d1 \<le> k" by simp
        from bd Deriv \<open>r = DCP a fa d1\<close> have b1: "boundIn ((a, nx, fa) # G) d1"
          by (auto simp: boundIn_def labels_def)
        from eb have eb1: "envBelow ((a, nx, fa) # G) (Suc nx)" by (rule envBelow_Cons)
        from emit_inv [OF b1, where base = base and nx = "Suc nx" and cnt = cnt] e1
        have E1: "emitInv ((a, nx, fa) # G) (Suc nx) b1 cc1 nx1" by simp
        from IH [OF s1 b1 eb1, where base = base and cnt = cnt
                 and path = "path @ [nx]"] e1
        have C1: "citeInv ((a, nx, fa) # G) (path @ [nx]) b1" by simp
        from citeInv_closeSub [OF C1 E1 eb1 cs]
        have C1': "citeInv ((a, nx, fa) # G) (path @ [nx]) b1'" .
        have env1: "envNums ((a, nx, fa) # G) \<subseteq> insert nx (envNums G)" by simp
        have lt1: "l1 < nx2" by (rule closeSub_lt [OF E1 eb1 cs])
        have ed: "emit base G nx cnt d
                    = ([FSub (Subproof nx fa b1'), FLine nx2 phi (FCP (nx, l1))],
                       nx2, Suc nx2, cnt1)"
          using Deriv \<open>r = DCP a fa d1\<close> e1 cs by simp
        have "citeInv G path [FSub (Subproof nx fa b1'), FLine nx2 phi (FCP (nx, l1))]"
          by (rule citeInv_CP [OF C1' env1 subLastLine_cs [OF cs] lt1]) simp_all
        with ed show ?thesis by simp
      next
        case (DRAA a fa d1)
        obtain b1 cc1 nx1 cnt1
          where e1: "emit base ((a, nx, fa) # G) (Suc nx) cnt d1 = (b1, cc1, nx1, cnt1)"
          by (rule prod_cases4)
        obtain b1' l1 nx2 where cs: "closeSub nx (dForm d1) b1 cc1 nx1 = (b1', l1, nx2)"
          by (rule prod_cases3)
        from sz Deriv \<open>r = DRAA a fa d1\<close> have s1: "size d1 \<le> k" by simp
        from bd Deriv \<open>r = DRAA a fa d1\<close> have b1: "boundIn ((a, nx, fa) # G) d1"
          by (auto simp: boundIn_def labels_def)
        from eb have eb1: "envBelow ((a, nx, fa) # G) (Suc nx)" by (rule envBelow_Cons)
        from emit_inv [OF b1, where base = base and nx = "Suc nx" and cnt = cnt] e1
        have E1: "emitInv ((a, nx, fa) # G) (Suc nx) b1 cc1 nx1" by simp
        from IH [OF s1 b1 eb1, where base = base and cnt = cnt
                 and path = "path @ [nx]"] e1
        have C1: "citeInv ((a, nx, fa) # G) (path @ [nx]) b1" by simp
        from citeInv_closeSub [OF C1 E1 eb1 cs]
        have C1': "citeInv ((a, nx, fa) # G) (path @ [nx]) b1'" .
        have env1: "envNums ((a, nx, fa) # G) \<subseteq> insert nx (envNums G)" by simp
        have lt1: "l1 < nx2" by (rule closeSub_lt [OF E1 eb1 cs])
        have ed: "emit base G nx cnt d
                    = ([FSub (Subproof nx fa b1'), FLine nx2 phi (FRAA (nx, l1))],
                       nx2, Suc nx2, cnt1)"
          using Deriv \<open>r = DRAA a fa d1\<close> e1 cs by simp
        have "citeInv G path [FSub (Subproof nx fa b1'), FLine nx2 phi (FRAA (nx, l1))]"
          by (rule citeInv_CP [OF C1' env1 subLastLine_cs [OF cs] lt1]) simp_all
        with ed show ?thesis by simp
      next
        case (DDN d1)
        obtain i1 c1 nx1 cnt1 where e1: "emit base G nx cnt d1 = (i1, c1, nx1, cnt1)"
          by (rule prod_cases4)
        from sz Deriv \<open>r = DDN d1\<close> have s1: "size d1 \<le> k" by simp
        from bd Deriv \<open>r = DDN d1\<close> have b1: "boundIn G d1" by (simp add: boundIn_def)
        from emit_inv [OF b1, where base = base and nx = nx and cnt = cnt] e1
        have E1: "emitInv G nx i1 c1 nx1" by simp
        from IH [OF s1 b1 eb, where base = base and cnt = cnt and path = path] e1
        have C1: "citeInv G path i1" by simp
        have ed: "emit base G nx cnt d = (i1 @ [FLine nx1 phi (FDN c1)], nx1, Suc nx1, cnt1)"
          using Deriv \<open>r = DDN d1\<close> e1 by simp
        have "citeInv G path (i1 @ [FLine nx1 phi (FDN c1)])"
          by (rule citeInv_step1 [OF C1 E1 eb]) simp_all
        with ed show ?thesis by simp
      next
        case (DBotI d1 d2)
        obtain i1 c1 nx1 cnt1 where e1: "emit base G nx cnt d1 = (i1, c1, nx1, cnt1)"
          by (rule prod_cases4)
        obtain i2 c2 nx2 cnt2 where e2: "emit base G nx1 cnt1 d2 = (i2, c2, nx2, cnt2)"
          by (rule prod_cases4)
        from sz Deriv \<open>r = DBotI d1 d2\<close> have s1: "size d1 \<le> k" and s2: "size d2 \<le> k" by simp_all
        from bd Deriv \<open>r = DBotI d1 d2\<close> have b1: "boundIn G d1" and b2: "boundIn G d2"
          by (auto simp: boundIn_def)
        from emit_inv [OF b1, where base = base and nx = nx and cnt = cnt] e1
        have E1: "emitInv G nx i1 c1 nx1" by simp
        from eb emitInv_le [OF E1] have eb1: "envBelow G nx1" by (rule envBelow_mono)
        from emit_inv [OF b2, where base = base and nx = nx1 and cnt = cnt1] e2
        have E2: "emitInv G nx1 i2 c2 nx2" by simp
        from IH [OF s1 b1 eb, where base = base and cnt = cnt and path = path] e1
        have C1: "citeInv G path i1" by simp
        from IH [OF s2 b2 eb1, where base = base and cnt = cnt1 and path = path] e2
        have C2: "citeInv G path i2" by simp
        have ed: "emit base G nx cnt d
                    = (i1 @ i2 @ [FLine nx2 phi (FBotI c1 c2)], nx2, Suc nx2, cnt2)"
          using Deriv \<open>r = DBotI d1 d2\<close> e1 e2 by simp
        have "citeInv G path (i1 @ i2 @ [FLine nx2 phi (FBotI c1 c2)])"
          by (rule citeInv_step2 [OF C1 C2 E1 E2 eb]) simp_all
        with ed show ?thesis by simp
      next
        case (DAndIntro d1 d2)
        obtain i1 c1 nx1 cnt1 where e1: "emit base G nx cnt d1 = (i1, c1, nx1, cnt1)"
          by (rule prod_cases4)
        obtain i2 c2 nx2 cnt2 where e2: "emit base G nx1 cnt1 d2 = (i2, c2, nx2, cnt2)"
          by (rule prod_cases4)
        from sz Deriv \<open>r = DAndIntro d1 d2\<close> have s1: "size d1 \<le> k" and s2: "size d2 \<le> k" by simp_all
        from bd Deriv \<open>r = DAndIntro d1 d2\<close> have b1: "boundIn G d1" and b2: "boundIn G d2"
          by (auto simp: boundIn_def)
        from emit_inv [OF b1, where base = base and nx = nx and cnt = cnt] e1
        have E1: "emitInv G nx i1 c1 nx1" by simp
        from eb emitInv_le [OF E1] have eb1: "envBelow G nx1" by (rule envBelow_mono)
        from emit_inv [OF b2, where base = base and nx = nx1 and cnt = cnt1] e2
        have E2: "emitInv G nx1 i2 c2 nx2" by simp
        from IH [OF s1 b1 eb, where base = base and cnt = cnt and path = path] e1
        have C1: "citeInv G path i1" by simp
        from IH [OF s2 b2 eb1, where base = base and cnt = cnt1 and path = path] e2
        have C2: "citeInv G path i2" by simp
        have ed: "emit base G nx cnt d
                    = (i1 @ i2 @ [FLine nx2 phi (FAndIntro c1 c2)], nx2, Suc nx2, cnt2)"
          using Deriv \<open>r = DAndIntro d1 d2\<close> e1 e2 by simp
        have "citeInv G path (i1 @ i2 @ [FLine nx2 phi (FAndIntro c1 c2)])"
          by (rule citeInv_step2 [OF C1 C2 E1 E2 eb]) simp_all
        with ed show ?thesis by simp
      next
        case (DAndElimL d1)
        obtain i1 c1 nx1 cnt1 where e1: "emit base G nx cnt d1 = (i1, c1, nx1, cnt1)"
          by (rule prod_cases4)
        from sz Deriv \<open>r = DAndElimL d1\<close> have s1: "size d1 \<le> k" by simp
        from bd Deriv \<open>r = DAndElimL d1\<close> have b1: "boundIn G d1" by (simp add: boundIn_def)
        from emit_inv [OF b1, where base = base and nx = nx and cnt = cnt] e1
        have E1: "emitInv G nx i1 c1 nx1" by simp
        from IH [OF s1 b1 eb, where base = base and cnt = cnt and path = path] e1
        have C1: "citeInv G path i1" by simp
        have ed: "emit base G nx cnt d = (i1 @ [FLine nx1 phi (FAndElimL c1)], nx1, Suc nx1, cnt1)"
          using Deriv \<open>r = DAndElimL d1\<close> e1 by simp
        have "citeInv G path (i1 @ [FLine nx1 phi (FAndElimL c1)])"
          by (rule citeInv_step1 [OF C1 E1 eb]) simp_all
        with ed show ?thesis by simp
      next
        case (DAndElimR d1)
        obtain i1 c1 nx1 cnt1 where e1: "emit base G nx cnt d1 = (i1, c1, nx1, cnt1)"
          by (rule prod_cases4)
        from sz Deriv \<open>r = DAndElimR d1\<close> have s1: "size d1 \<le> k" by simp
        from bd Deriv \<open>r = DAndElimR d1\<close> have b1: "boundIn G d1" by (simp add: boundIn_def)
        from emit_inv [OF b1, where base = base and nx = nx and cnt = cnt] e1
        have E1: "emitInv G nx i1 c1 nx1" by simp
        from IH [OF s1 b1 eb, where base = base and cnt = cnt and path = path] e1
        have C1: "citeInv G path i1" by simp
        have ed: "emit base G nx cnt d = (i1 @ [FLine nx1 phi (FAndElimR c1)], nx1, Suc nx1, cnt1)"
          using Deriv \<open>r = DAndElimR d1\<close> e1 by simp
        have "citeInv G path (i1 @ [FLine nx1 phi (FAndElimR c1)])"
          by (rule citeInv_step1 [OF C1 E1 eb]) simp_all
        with ed show ?thesis by simp
      next
        case (DOrIntroL d1)
        obtain i1 c1 nx1 cnt1 where e1: "emit base G nx cnt d1 = (i1, c1, nx1, cnt1)"
          by (rule prod_cases4)
        from sz Deriv \<open>r = DOrIntroL d1\<close> have s1: "size d1 \<le> k" by simp
        from bd Deriv \<open>r = DOrIntroL d1\<close> have b1: "boundIn G d1" by (simp add: boundIn_def)
        from emit_inv [OF b1, where base = base and nx = nx and cnt = cnt] e1
        have E1: "emitInv G nx i1 c1 nx1" by simp
        from IH [OF s1 b1 eb, where base = base and cnt = cnt and path = path] e1
        have C1: "citeInv G path i1" by simp
        have ed: "emit base G nx cnt d = (i1 @ [FLine nx1 phi (FOrIntroL c1)], nx1, Suc nx1, cnt1)"
          using Deriv \<open>r = DOrIntroL d1\<close> e1 by simp
        have "citeInv G path (i1 @ [FLine nx1 phi (FOrIntroL c1)])"
          by (rule citeInv_step1 [OF C1 E1 eb]) simp_all
        with ed show ?thesis by simp
      next
        case (DOrIntroR d1)
        obtain i1 c1 nx1 cnt1 where e1: "emit base G nx cnt d1 = (i1, c1, nx1, cnt1)"
          by (rule prod_cases4)
        from sz Deriv \<open>r = DOrIntroR d1\<close> have s1: "size d1 \<le> k" by simp
        from bd Deriv \<open>r = DOrIntroR d1\<close> have b1: "boundIn G d1" by (simp add: boundIn_def)
        from emit_inv [OF b1, where base = base and nx = nx and cnt = cnt] e1
        have E1: "emitInv G nx i1 c1 nx1" by simp
        from IH [OF s1 b1 eb, where base = base and cnt = cnt and path = path] e1
        have C1: "citeInv G path i1" by simp
        have ed: "emit base G nx cnt d = (i1 @ [FLine nx1 phi (FOrIntroR c1)], nx1, Suc nx1, cnt1)"
          using Deriv \<open>r = DOrIntroR d1\<close> e1 by simp
        have "citeInv G path (i1 @ [FLine nx1 phi (FOrIntroR c1)])"
          by (rule citeInv_step1 [OF C1 E1 eb]) simp_all
        with ed show ?thesis by simp
      next
        case (DOrElim d0 a1 f1 d1 a2 f2 d2)
        obtain i0 c0 nx0 cnt0 where e0: "emit base G nx cnt d0 = (i0, c0, nx0, cnt0)"
          by (rule prod_cases4)
        obtain b1 cc1 m1 cnt1
          where e1: "emit base ((a1, nx0, f1) # G) (Suc nx0) cnt0 d1 = (b1, cc1, m1, cnt1)"
          by (rule prod_cases4)
        obtain b1' l1 n1 where cs1: "closeSub nx0 (dForm d1) b1 cc1 m1 = (b1', l1, n1)"
          by (rule prod_cases3)
        obtain b2 cc2 m2 cnt2
          where e2: "emit base ((a2, n1, f2) # G) (Suc n1) cnt1 d2 = (b2, cc2, m2, cnt2)"
          by (rule prod_cases4)
        obtain b2' l2 n2 where cs2: "closeSub n1 (dForm d2) b2 cc2 m2 = (b2', l2, n2)"
          by (rule prod_cases3)
        from sz Deriv \<open>r = DOrElim d0 a1 f1 d1 a2 f2 d2\<close>
        have s0: "size d0 \<le> k" and s1: "size d1 \<le> k" and s2: "size d2 \<le> k" by simp_all
        from bd Deriv \<open>r = DOrElim d0 a1 f1 d1 a2 f2 d2\<close>
        have b0: "boundIn G d0" and bb1: "boundIn ((a1, nx0, f1) # G) d1"
         and bb2: "boundIn ((a2, n1, f2) # G) d2"
          by (auto simp: boundIn_def labels_def)
        from emit_inv [OF b0, where base = base and nx = nx and cnt = cnt] e0
        have E0: "emitInv G nx i0 c0 nx0" by simp
        from eb emitInv_le [OF E0] have eb0: "envBelow G nx0" by (rule envBelow_mono)
        from eb0 have eb1: "envBelow ((a1, nx0, f1) # G) (Suc nx0)" by (rule envBelow_Cons)
        from emit_inv [OF bb1, where base = base and nx = "Suc nx0" and cnt = cnt0] e1
        have E1: "emitInv ((a1, nx0, f1) # G) (Suc nx0) b1 cc1 m1" by simp
        have le1: "nx0 \<le> n1" using emitInv_le [OF E1] closeSub_le [OF cs1] by simp
        from eb0 le1 have eb0': "envBelow G n1" by (rule envBelow_mono)
        from eb0' have eb2: "envBelow ((a2, n1, f2) # G) (Suc n1)" by (rule envBelow_Cons)
        from emit_inv [OF bb2, where base = base and nx = "Suc n1" and cnt = cnt1] e2
        have E2: "emitInv ((a2, n1, f2) # G) (Suc n1) b2 cc2 m2" by simp
        have le2: "n1 \<le> n2" using emitInv_le [OF E2] closeSub_le [OF cs2] by simp
        from IH [OF s0 b0 eb, where base = base and cnt = cnt and path = path] e0
        have C0: "citeInv G path i0" by simp
        from IH [OF s1 bb1 eb1, where base = base and cnt = cnt0
                 and path = "path @ [nx0]"] e1
        have C1: "citeInv ((a1, nx0, f1) # G) (path @ [nx0]) b1" by simp
        from citeInv_closeSub [OF C1 E1 eb1 cs1]
        have C1': "citeInv ((a1, nx0, f1) # G) (path @ [nx0]) b1'" .
        from IH [OF s2 bb2 eb2, where base = base and cnt = cnt1
                 and path = "path @ [n1]"] e2
        have C2: "citeInv ((a2, n1, f2) # G) (path @ [n1]) b2" by simp
        from citeInv_closeSub [OF C2 E2 eb2 cs2]
        have C2': "citeInv ((a2, n1, f2) # G) (path @ [n1]) b2'" .
        have env1: "envNums ((a1, nx0, f1) # G) \<subseteq> insert nx0 (envNums G)" by simp
        have env2: "envNums ((a2, n1, f2) # G) \<subseteq> insert n1 (envNums G)" by simp
        have lt1: "l1 < n2" using closeSub_lt [OF E1 eb1 cs1] le2 by simp
        have lt2: "l2 < n2" by (rule closeSub_lt [OF E2 eb2 cs2])
        have le: "nx0 \<le> n2" using le1 le2 by simp
        have ed: "emit base G nx cnt d
                    = (i0 @ [FSub (Subproof nx0 f1 b1'), FSub (Subproof n1 f2 b2'),
                             FLine n2 phi (FOrElim c0 (nx0, l1) (n1, l2))], n2, Suc n2, cnt2)"
          using Deriv \<open>r = DOrElim d0 a1 f1 d1 a2 f2 d2\<close> e0 e1 cs1 e2 cs2 by simp
        have "citeInv G path (i0 @ [FSub (Subproof nx0 f1 b1'), FSub (Subproof n1 f2 b2'),
                                    FLine n2 phi (FOrElim c0 (nx0, l1) (n1, l2))])"
          by (rule citeInv_OE [OF C0 E0 eb C1' env1 subLastLine_cs [OF cs1] lt1
                                  C2' env2 subLastLine_cs [OF cs2] lt2 le]) simp_all
        with ed show ?thesis by simp
      next
        case (DIffIntro d1 d2)
        obtain i1 c1 nx1 cnt1 where e1: "emit base G nx cnt d1 = (i1, c1, nx1, cnt1)"
          by (rule prod_cases4)
        obtain i2 c2 nx2 cnt2 where e2: "emit base G nx1 cnt1 d2 = (i2, c2, nx2, cnt2)"
          by (rule prod_cases4)
        from sz Deriv \<open>r = DIffIntro d1 d2\<close> have s1: "size d1 \<le> k" and s2: "size d2 \<le> k" by simp_all
        from bd Deriv \<open>r = DIffIntro d1 d2\<close> have b1: "boundIn G d1" and b2: "boundIn G d2"
          by (auto simp: boundIn_def)
        from emit_inv [OF b1, where base = base and nx = nx and cnt = cnt] e1
        have E1: "emitInv G nx i1 c1 nx1" by simp
        from eb emitInv_le [OF E1] have eb1: "envBelow G nx1" by (rule envBelow_mono)
        from emit_inv [OF b2, where base = base and nx = nx1 and cnt = cnt1] e2
        have E2: "emitInv G nx1 i2 c2 nx2" by simp
        from IH [OF s1 b1 eb, where base = base and cnt = cnt and path = path] e1
        have C1: "citeInv G path i1" by simp
        from IH [OF s2 b2 eb1, where base = base and cnt = cnt1 and path = path] e2
        have C2: "citeInv G path i2" by simp
        have ed: "emit base G nx cnt d
                    = (i1 @ i2 @ [FLine nx2 phi (FIffIntro c1 c2)], nx2, Suc nx2, cnt2)"
          using Deriv \<open>r = DIffIntro d1 d2\<close> e1 e2 by simp
        have "citeInv G path (i1 @ i2 @ [FLine nx2 phi (FIffIntro c1 c2)])"
          by (rule citeInv_step2 [OF C1 C2 E1 E2 eb]) simp_all
        with ed show ?thesis by simp
      next
        case (DIffElimL d1)
        obtain i1 c1 nx1 cnt1 where e1: "emit base G nx cnt d1 = (i1, c1, nx1, cnt1)"
          by (rule prod_cases4)
        from sz Deriv \<open>r = DIffElimL d1\<close> have s1: "size d1 \<le> k" by simp
        from bd Deriv \<open>r = DIffElimL d1\<close> have b1: "boundIn G d1" by (simp add: boundIn_def)
        from emit_inv [OF b1, where base = base and nx = nx and cnt = cnt] e1
        have E1: "emitInv G nx i1 c1 nx1" by simp
        from IH [OF s1 b1 eb, where base = base and cnt = cnt and path = path] e1
        have C1: "citeInv G path i1" by simp
        have ed: "emit base G nx cnt d = (i1 @ [FLine nx1 phi (FIffElimL c1)], nx1, Suc nx1, cnt1)"
          using Deriv \<open>r = DIffElimL d1\<close> e1 by simp
        have "citeInv G path (i1 @ [FLine nx1 phi (FIffElimL c1)])"
          by (rule citeInv_step1 [OF C1 E1 eb]) simp_all
        with ed show ?thesis by simp
      next
        case (DIffElimR d1)
        obtain i1 c1 nx1 cnt1 where e1: "emit base G nx cnt d1 = (i1, c1, nx1, cnt1)"
          by (rule prod_cases4)
        from sz Deriv \<open>r = DIffElimR d1\<close> have s1: "size d1 \<le> k" by simp
        from bd Deriv \<open>r = DIffElimR d1\<close> have b1: "boundIn G d1" by (simp add: boundIn_def)
        from emit_inv [OF b1, where base = base and nx = nx and cnt = cnt] e1
        have E1: "emitInv G nx i1 c1 nx1" by simp
        from IH [OF s1 b1 eb, where base = base and cnt = cnt and path = path] e1
        have C1: "citeInv G path i1" by simp
        have ed: "emit base G nx cnt d = (i1 @ [FLine nx1 phi (FIffElimR c1)], nx1, Suc nx1, cnt1)"
          using Deriv \<open>r = DIffElimR d1\<close> e1 by simp
        have "citeInv G path (i1 @ [FLine nx1 phi (FIffElimR c1)])"
          by (rule citeInv_step1 [OF C1 E1 eb]) simp_all
        with ed show ?thesis by simp
      next
        case (DForallElim d1)
        obtain i1 c1 nx1 cnt1 where e1: "emit base G nx cnt d1 = (i1, c1, nx1, cnt1)"
          by (rule prod_cases4)
        from sz Deriv \<open>r = DForallElim d1\<close> have s1: "size d1 \<le> k" by simp
        from bd Deriv \<open>r = DForallElim d1\<close> have b1: "boundIn G d1" by (simp add: boundIn_def)
        from emit_inv [OF b1, where base = base and nx = nx and cnt = cnt] e1
        have E1: "emitInv G nx i1 c1 nx1" by simp
        from IH [OF s1 b1 eb, where base = base and cnt = cnt and path = path] e1
        have C1: "citeInv G path i1" by simp
        have ed: "emit base G nx cnt d = (i1 @ [FLine nx1 phi (FForallElim c1)], nx1, Suc nx1, cnt1)"
          using Deriv \<open>r = DForallElim d1\<close> e1 by simp
        have "citeInv G path (i1 @ [FLine nx1 phi (FForallElim c1)])"
          by (rule citeInv_step1 [OF C1 E1 eb]) simp_all
        with ed show ?thesis by simp
      next
        case (DForallIntro d1)
        obtain i1 c1 nx1 cnt1
          where e1: "emit base G nx (uniCnt cnt G phi d1) (uniD base cnt G phi d1)
                       = (i1, c1, nx1, cnt1)"
          by (rule prod_cases4)
        from sz Deriv \<open>r = DForallIntro d1\<close> have s1: "size (uniD base cnt G phi d1) \<le> k"
          by (simp add: size_uniD)
        from bd Deriv \<open>r = DForallIntro d1\<close> have "boundIn G d1" by (simp add: boundIn_def)
        then have b1: "boundIn G (uniD base cnt G phi d1)" by (rule boundIn_uniD)
        from emit_inv [OF b1, where base = base and nx = nx and cnt = "uniCnt cnt G phi d1"] e1
        have E1: "emitInv G nx i1 c1 nx1" by simp
        from IH [OF s1 b1 eb, where base = base and cnt = "uniCnt cnt G phi d1" and path = path] e1
        have C1: "citeInv G path i1" by simp
        have ed: "emit base G nx cnt d
                    = (i1 @ [FLine nx1 phi (FForallIntro c1)], nx1, Suc nx1, cnt1)"
          using Deriv \<open>r = DForallIntro d1\<close> e1 by simp
        have "citeInv G path (i1 @ [FLine nx1 phi (FForallIntro c1)])"
          by (rule citeInv_step1 [OF C1 E1 eb]) simp_all
        with ed show ?thesis by simp
      next
        case (DExistsIntro d1)
        obtain i1 c1 nx1 cnt1 where e1: "emit base G nx cnt d1 = (i1, c1, nx1, cnt1)"
          by (rule prod_cases4)
        from sz Deriv \<open>r = DExistsIntro d1\<close> have s1: "size d1 \<le> k" by simp
        from bd Deriv \<open>r = DExistsIntro d1\<close> have b1: "boundIn G d1" by (simp add: boundIn_def)
        from emit_inv [OF b1, where base = base and nx = nx and cnt = cnt] e1
        have E1: "emitInv G nx i1 c1 nx1" by simp
        from IH [OF s1 b1 eb, where base = base and cnt = cnt and path = path] e1
        have C1: "citeInv G path i1" by simp
        have ed: "emit base G nx cnt d = (i1 @ [FLine nx1 phi (FExistsIntro c1)], nx1, Suc nx1, cnt1)"
          using Deriv \<open>r = DExistsIntro d1\<close> e1 by simp
        have "citeInv G path (i1 @ [FLine nx1 phi (FExistsIntro c1)])"
          by (rule citeInv_step1 [OF C1 E1 eb]) simp_all
        with ed show ?thesis by simp
      next
        case (DExistsElim d0 a f d1)
        obtain i0 c0 nx0 cnt0 where e0: "emit base G nx cnt d0 = (i0, c0, nx0, cnt0)"
          by (rule prod_cases4)
        let ?f' = "exF base cnt0 G (dForm d0) f phi a d0 d1"
        let ?d1 = "exD base cnt0 G (dForm d0) f phi a d0 d1"
        obtain b1 cc1 m1 cnt1
          where e1: "emit base ((a, nx0, ?f') # G) (Suc nx0)
                       (exCnt cnt0 G (dForm d0) f phi a d0 d1) ?d1 = (b1, cc1, m1, cnt1)"
          by (rule prod_cases4)
        obtain b1' l1 n1 where cs: "closeSub nx0 phi b1 cc1 m1 = (b1', l1, n1)"
          by (rule prod_cases3)
        from sz Deriv \<open>r = DExistsElim d0 a f d1\<close>
        have s0: "size d0 \<le> k" and s1: "size ?d1 \<le> k" by (simp_all add: size_exD)
        from bd Deriv \<open>r = DExistsElim d0 a f d1\<close>
        have b0: "boundIn G d0" and bb: "boundIn ((a, nx0, ?f') # G) d1"
          by (auto simp: boundIn_def labels_def)
        from bb have b1: "boundIn ((a, nx0, ?f') # G) ?d1" by (rule boundIn_exD)
        from emit_inv [OF b0, where base = base and nx = nx and cnt = cnt] e0
        have E0: "emitInv G nx i0 c0 nx0" by simp
        from eb emitInv_le [OF E0] have eb0: "envBelow G nx0" by (rule envBelow_mono)
        from eb0 have eb1: "envBelow ((a, nx0, ?f') # G) (Suc nx0)" by (rule envBelow_Cons)
        from emit_inv [OF b1, where base = base and nx = "Suc nx0"
                       and cnt = "exCnt cnt0 G (dForm d0) f phi a d0 d1"] e1
        have E1: "emitInv ((a, nx0, ?f') # G) (Suc nx0) b1 cc1 m1" by simp
        from IH [OF s0 b0 eb, where base = base and cnt = cnt and path = path] e0
        have C0: "citeInv G path i0" by simp
        from IH [OF s1 b1 eb1, where base = base and cnt = "exCnt cnt0 G (dForm d0) f phi a d0 d1" and path = "path @ [nx0]"] e1
        have C1: "citeInv ((a, nx0, ?f') # G) (path @ [nx0]) b1" by simp
        from citeInv_closeSub [OF C1 E1 eb1 cs]
        have C1': "citeInv ((a, nx0, ?f') # G) (path @ [nx0]) b1'" .
        have env1: "envNums ((a, nx0, ?f') # G) \<subseteq> insert nx0 (envNums G)" by simp
        have lt1: "l1 < n1" by (rule closeSub_lt [OF E1 eb1 cs])
        have le: "nx0 \<le> n1" using emitInv_le [OF E1] closeSub_le [OF cs] by simp
        have ed: "emit base G nx cnt d
                    = (i0 @ [FSub (Subproof nx0 ?f' b1'),
                             FLine n1 phi (FExistsElim c0 (nx0, l1))], n1, Suc n1, cnt1)"
          using Deriv \<open>r = DExistsElim d0 a f d1\<close> e0 e1 cs by simp
        have "citeInv G path (i0 @ [FSub (Subproof nx0 ?f' b1'),
                                    FLine n1 phi (FExistsElim c0 (nx0, l1))])"
          by (rule citeInv_EE [OF C0 E0 eb C1' env1 subLastLine_cs [OF cs] lt1 le]) simp_all
        with ed show ?thesis by simp
      next
        case DEqIntro
        have ed: "emit base G nx cnt d = ([FLine nx phi FEqIntro], nx, Suc nx, cnt)"
          using Deriv \<open>r = DEqIntro\<close> by simp
        have "citeInv G path [FLine nx phi FEqIntro]" by (rule citeInv_step0) simp_all
        with ed show ?thesis by simp
      next
        case (DEqElim d1 d2)
        obtain i1 c1 nx1 cnt1 where e1: "emit base G nx cnt d1 = (i1, c1, nx1, cnt1)"
          by (rule prod_cases4)
        obtain i2 c2 nx2 cnt2 where e2: "emit base G nx1 cnt1 d2 = (i2, c2, nx2, cnt2)"
          by (rule prod_cases4)
        from sz Deriv \<open>r = DEqElim d1 d2\<close> have s1: "size d1 \<le> k" and s2: "size d2 \<le> k" by simp_all
        from bd Deriv \<open>r = DEqElim d1 d2\<close> have b1: "boundIn G d1" and b2: "boundIn G d2"
          by (auto simp: boundIn_def)
        from emit_inv [OF b1, where base = base and nx = nx and cnt = cnt] e1
        have E1: "emitInv G nx i1 c1 nx1" by simp
        from eb emitInv_le [OF E1] have eb1: "envBelow G nx1" by (rule envBelow_mono)
        from emit_inv [OF b2, where base = base and nx = nx1 and cnt = cnt1] e2
        have E2: "emitInv G nx1 i2 c2 nx2" by simp
        from IH [OF s1 b1 eb, where base = base and cnt = cnt and path = path] e1
        have C1: "citeInv G path i1" by simp
        from IH [OF s2 b2 eb1, where base = base and cnt = cnt1 and path = path] e2
        have C2: "citeInv G path i2" by simp
        have ed: "emit base G nx cnt d
                    = (i1 @ i2 @ [FLine nx2 phi (FEqElim c1 c2)], nx2, Suc nx2, cnt2)"
          using Deriv \<open>r = DEqElim d1 d2\<close> e1 e2 by simp
        have "citeInv G path (i1 @ i2 @ [FLine nx2 phi (FEqElim c1 c2)])"
          by (rule citeInv_step2 [OF C1 C2 E1 E2 eb]) simp_all
        with ed show ?thesis by simp
      next
        case (DReit d1)
        obtain i1 c1 nx1 cnt1 where e1: "emit base G nx cnt d1 = (i1, c1, nx1, cnt1)"
          by (rule prod_cases4)
        from sz Deriv \<open>r = DReit d1\<close> have s1: "size d1 \<le> k" by simp
        from bd Deriv \<open>r = DReit d1\<close> have b1: "boundIn G d1" by (simp add: boundIn_def)
        from emit_inv [OF b1, where base = base and nx = nx and cnt = cnt] e1
        have E1: "emitInv G nx i1 c1 nx1" by simp
        from IH [OF s1 b1 eb, where base = base and cnt = cnt and path = path] e1
        have C1: "citeInv G path i1" by simp
        have ed: "emit base G nx cnt d = (i1 @ [FLine nx1 phi (FReit c1)], nx1, Suc nx1, cnt1)"
          using Deriv \<open>r = DReit d1\<close> e1 by simp
        have "citeInv G path (i1 @ [FLine nx1 phi (FReit c1)])"
          by (rule citeInv_step1 [OF C1 E1 eb]) simp_all
        with ed show ?thesis by simp
      qed
    qed
  qed
qed

lemma emit_cite:
  "boundIn G d \<Longrightarrow> envBelow G nx \<Longrightarrow> citeInv G path (eItems base G nx cnt d)"
  using emit_cite_k [of "size d"] by blast

section \<open>The premises, at the outermost level\<close>

lemma flatItems_premLines [simp]:
  "flatItems (premLines G) path = map (\<lambda>e. FL (fst (snd e)) (snd (snd e)) FPremise path) G"
  by (induction G) (auto simp: premLines_def)

lemma itemsNums_premLines [simp]: "itemsNums (premLines G) = map (fst \<circ> snd) G"
  by (induction G) (auto simp: premLines_def)

lemma subrefsItems_premLines [simp]: "subrefsItems (premLines G) path = []"
  by (induction G) (auto simp: premLines_def)

lemma noAssume_premLines [simp]: "list_all noAssumeLinesItem (premLines G)"
  by (induction G) (auto simp: premLines_def)

lemma lastIsLine_premLines [simp]: "list_all lastIsLineItem (premLines G)"
  by (induction G) (auto simp: premLines_def)

lemma premLines_witness:
  assumes "m \<in> envNums G"
  shows "\<exists>fl \<in> set (flatItems (premLines G) path). flNum fl = m \<and> flScope fl = path"
  using assms by (auto simp: envNums_def)

text \<open>The traversal only ever asks for the premises at the top level, so the
  instance with the empty path is the one used below.  It is stated separately
  rather than instantiated at the point of use: the schematic names of a lemma
  are not part of its statement, and depending on them is brittle.\<close>

lemma premLines_witness_root:
  assumes "m \<in> envNums G"
  shows "\<exists>fl \<in> set (flatItems (premLines G) []). flNum fl = m \<and> flScope fl = []"
  using assms by (auto simp: envNums_def)

subsection \<open>The environment the traversal starts from\<close>

lemma premEnv_aux [rule_format]:
  "\<forall>n. map fst (map (\<lambda>ke. (fst (snd ke), Suc (fst ke), snd (snd ke)))
                     (List.enumerate n L)) = map fst L"
  "\<forall>n. map (\<lambda>e. fst (snd e))
              (map (\<lambda>ke. (fst (snd ke), Suc (fst ke), snd (snd ke)))
                   (List.enumerate n L)) = [Suc n..<Suc (n + length L)]"
  by (induction L) (auto simp: upt_conv_Cons)

lemma map_fst_premEnv: "map fst (premEnv d) = map fst (sort_key fst (remdups (openAsms d)))"
  using premEnv_aux(1) by (simp add: premEnv_def)

lemma labels_premEnv: "labels (premEnv d) = fst ` set (openAsms d)"
  by (simp add: labels_def map_fst_premEnv)

lemma boundIn_premEnv: "boundIn (premEnv d) d"
  by (simp add: boundIn_def labels_premEnv)

lemma length_premEnv:
  "length (premEnv d) = length (sort_key fst (remdups (openAsms d)))"
  by (simp add: premEnv_def)

lemma premEnv_nums:
  "map (\<lambda>e. fst (snd e)) (premEnv d) = [1..<Suc (length (premEnv d))]"
proof -
  have "map (\<lambda>e. fst (snd e)) (premEnv d)
          = [Suc 0..<Suc (0 + length (sort_key fst (remdups (openAsms d))))]"
    unfolding premEnv_def by (rule premEnv_aux(2))
  then show ?thesis by (simp add: length_premEnv)
qed

lemma envBelow_premEnv: "envBelow (premEnv d) (Suc (length (premEnv d)))"
  using premEnv_nums [of d] by (auto simp: envBelow_def envNums_def comp_def)

section \<open>Well-formedness\<close>

lemma noPrem_flat_all:
  "\<forall>p. noPremItem it \<longrightarrow> (\<forall>fl \<in> set (flatItem it p). flRule fl \<noteq> FPremise)"
  "\<forall>q. noPremSub s \<longrightarrow> (\<forall>fl \<in> set (flatSub s q). flRule fl \<noteq> FPremise)"
  by (induction it and s) (fastforce simp: list_all_iff)+

lemma noPrem_flatItems:
  "list_all noPremItem its \<Longrightarrow> fl \<in> set (flatItems its path) \<Longrightarrow> flRule fl \<noteq> FPremise"
  by (induction its) (auto simp: noPrem_flat_all(1) [rule_format])

lemma set_dropWhile: "set (dropWhile P xs) \<subseteq> set xs"
  by (induction xs) auto

lemma citationOK_I:
  assumes "distinct (map flNum (flatten F))"
      and "\<forall>m \<in> set (fCitedLines (flRule fl)). m < flNum fl \<and>
             (\<exists>fl' \<in> set (flatten F). flNum fl' = m \<and> is_prefix (flScope fl') (flScope fl))"
      and "\<forall>ac \<in> set (fCitedSubs (flRule fl)). snd ac < flNum fl
             \<and> (ac, flScope fl) \<in> set (subrefs F)"
  shows "citationOK F fl"
  unfolding citationOK_def
proof (intro conjI)
  show "list_all (\<lambda>m. m < flNum fl \<and>
          (case findFL (flatten F) m of None \<Rightarrow> False
           | Some fl' \<Rightarrow> is_prefix (flScope fl') (flScope fl))) (fCitedLines (flRule fl))"
    unfolding list_all_iff
  proof
    fix m assume "m \<in> set (fCitedLines (flRule fl))"
    with assms(2) obtain fl' where m: "m < flNum fl" and fl': "fl' \<in> set (flatten F)"
      and n: "flNum fl' = m" and pre: "is_prefix (flScope fl') (flScope fl)" by blast
    from findFL_mem [OF assms(1) fl'] n have "findFL (flatten F) m = Some fl'" by simp
    with m pre show "m < flNum fl \<and>
          (case findFL (flatten F) m of None \<Rightarrow> False
           | Some fl' \<Rightarrow> is_prefix (flScope fl') (flScope fl))" by simp
  qed
next
  show "list_all (\<lambda>(a, c). c < flNum fl \<and> ((a, c), flScope fl) \<in> set (subrefs F))
          (fCitedSubs (flRule fl))"
    using assms(3) by (fastforce simp: list_all_iff)
qed

text \<open>Putting (L2) and (L3) together.  Note that no hypothesis is needed: the two
  lemmas are about the traversal, not about the rules, so the construction of
  Definition 21 yields a well-formed Fitch proof from \emph{any} derivation.
  What correctness of the source is needed for is (L4).\<close>

theorem L2_L3: "fitchWF (derivationToFitch d)"
proof -
  let ?G = "premEnv d"
  let ?base = "Suc (maxlen (namesD d))"
  obtain its c nx cnt where e: "emit ?base ?G (Suc (length ?G)) 0 d = (its, c, nx, cnt)"
    by (rule prod_cases4)
  let ?F = "premLines ?G @ its"
  have F: "derivationToFitch d = ?F" by (simp add: derivationToFitch_def e)
  from emit_inv [OF boundIn_premEnv [of d], where base = ?base
                 and nx = "Suc (length ?G)" and cnt = 0] e
  have E: "emitInv ?G (Suc (length ?G)) its c nx" by simp
  from emit_cite [OF boundIn_premEnv [of d] envBelow_premEnv [of d],
                  where base = ?base and cnt = 0 and path = "[]"] e
  have C: "citeInv ?G [] its" by simp
  from E have B: "blockInv (Suc (length ?G)) its nx" by (simp add: emitInv_def)

  have flat: "flatten ?F = flatItems (premLines ?G) [] @ flatItems its []"
    by (simp add: flatten_eq)
  have nums: "map flNum (flatten ?F) = [1..<Suc (length ?G)] @ itemsNums its"
  proof -
    have "map flNum (flatten ?F) = map (\<lambda>e. fst (snd e)) ?G @ itemsNums its"
      by (simp add: flat comp_def)
    also have "\<dots> = [1..<Suc (length ?G)] @ itemsNums its"
      by (simp only: premEnv_nums)
    finally show ?thesis .
  qed

  have srt: "sorted_wrt (<) (map flNum (flatten ?F))"
    using B unfolding nums blockInv_def by (auto simp: sorted_wrt_append)
  then have dist: "distinct (map flNum (flatten ?F))"
    by (rule sorted_wrt_less_distinct)

  from B have npi: "list_all noPremItem its" by (simp add: blockInv_def)
  have noprem: "\<And>fl. fl \<in> set (flatItems its []) \<Longrightarrow> flRule fl \<noteq> FPremise"
    by (rule noPrem_flatItems [OF npi])

  have "list_all (citationOK ?F) (flatten ?F)"
    unfolding list_all_iff
  proof
    fix fl assume "fl \<in> set (flatten ?F)"
    then consider (prem) "fl \<in> set (flatItems (premLines ?G) [])"
      | (item) "fl \<in> set (flatItems its [])" using flat by auto
    then show "citationOK ?F fl"
    proof cases
      case prem
      then have "flRule fl = FPremise" by auto
      then show ?thesis by (simp add: citationOK_def)
    next
      case item
      show ?thesis
      proof (rule citationOK_I [OF dist])
        show "\<forall>m \<in> set (fCitedLines (flRule fl)). m < flNum fl \<and>
                (\<exists>fl' \<in> set (flatten ?F). flNum fl' = m
                   \<and> is_prefix (flScope fl') (flScope fl))"
        proof
          fix m assume m: "m \<in> set (fCitedLines (flRule fl))"
          with C item have lt: "m < flNum fl"
            and alt: "(\<exists>fl' \<in> set (flatItems its []). flNum fl' = m
                         \<and> is_prefix (flScope fl') (flScope fl)) \<or> m \<in> envNums ?G"
            by (auto simp: citeInv_def)
          from alt have "\<exists>fl' \<in> set (flatten ?F). flNum fl' = m
                           \<and> is_prefix (flScope fl') (flScope fl)"
          proof
            assume "\<exists>fl' \<in> set (flatItems its []). flNum fl' = m
                      \<and> is_prefix (flScope fl') (flScope fl)"
            with flat show ?thesis by auto
          next
            assume mm: "m \<in> envNums ?G"
            obtain fl' where fl'1: "fl' \<in> set (flatItems (premLines ?G) [])"
              and fl'2: "flNum fl' = m" and fl'3: "flScope fl' = []"
              using premLines_witness_root [OF mm] by blast
            from fl'1 flat have inF: "fl' \<in> set (flatten ?F)" by simp
            have pre: "is_prefix (flScope fl') (flScope fl)"
              unfolding fl'3 by simp
            from inF fl'2 pre show ?thesis by blast
          qed
          with lt show "m < flNum fl \<and> (\<exists>fl' \<in> set (flatten ?F). flNum fl' = m
                          \<and> is_prefix (flScope fl') (flScope fl))" ..
        qed
      next
        show "\<forall>ac \<in> set (fCitedSubs (flRule fl)). snd ac < flNum fl
                \<and> (ac, flScope fl) \<in> set (subrefs ?F)"
          using C item by (auto simp: citeInv_def subrefs_eq)
      qed
    qed
  qed
  moreover have "list_all noAssumeLinesItem ?F"
    using B by (simp add: blockInv_def)
  moreover have "list_all (\<lambda>fl. flRule fl = FPremise \<longrightarrow> flScope fl = []) (flatten ?F)"
    using noprem by (auto simp: flat list_all_iff)
  moreover have "premisesFirst ?F"
  proof -
    text \<open>The premise lines are exactly the block @{term dropWhile} skips, so what
      follows them is what the traversal emitted --- and the traversal emits no
      premise.  Both steps are stated as rewrites of the @{const dropWhile} term
      itself: the simplifier must not be allowed to unfold @{const flatten} here,
      or it will try to decide the side condition of @{thm [source]
      dropWhile_append2} against the whole of @{const premEnv}.\<close>
    have D: "dropWhile (\<lambda>fl. flRule fl = FPremise) (flatten ?F)
               = dropWhile (\<lambda>fl. flRule fl = FPremise) (flatItems its [])"
    proof -
      have "\<And>fl. fl \<in> set (flatItems (premLines ?G) []) \<Longrightarrow> flRule fl = FPremise"
        by auto
      then show ?thesis unfolding flat by (rule dropWhile_append2)
    qed
    have "list_all (\<lambda>fl. flRule fl \<noteq> FPremise)
            (dropWhile (\<lambda>fl. flRule fl = FPremise) (flatItems its []))"
      unfolding list_all_iff
    proof
      fix fl' assume "fl' \<in> set (dropWhile (\<lambda>fl. flRule fl = FPremise) (flatItems its []))"
      then have "fl' \<in> set (flatItems its [])" by (rule set_dropWhileD)
      then show "flRule fl' \<noteq> FPremise" by (rule noprem)
    qed
    then show ?thesis unfolding premisesFirst_def D .
  qed
  moreover have "list_all lastIsLineItem ?F"
    using B by (simp add: blockInv_def)
  moreover have "concludesAtTop ?F"
    using E by (rule concludesAtTop_premLines_append)
  ultimately show ?thesis using srt unfolding F fitchWF_def by blast
qed

corollary L2_L3_wellFormed: "fitchWellFormed (derivationToFitch d) = None"
  by (simp add: fitchWellFormed_iff L2_L3)


section \<open>The conclusion of the traversal\<close>

text \<open>Definition 21 is supposed to preserve the conclusion.  It does, and for a
  reason that needs no induction: whatever a node's rule is, the last item the
  traversal emits for it is the line applying that rule, which carries the
  node's own formula.  The one exception is a leaf, which emits nothing at all
  and points instead at a line of the environment --- and at the root that
  environment is the premise block, whose single entry is the leaf's formula.\<close>

lemma last_flatItems:
  assumes "its \<noteq> []"
  shows "last (flatItems its path) = last (flatItem (last its) path)"
  unfolding flatItems_def by (rule last_concat_map [OF assms]) simp

lemma flatItems_nonempty: "its \<noteq> [] \<Longrightarrow> flatItems its path \<noteq> []"
  unfolding flatItems_def by (rule concat_map_nonempty) simp_all

lemma emit_conclusion_line:
  assumes "emit base G nx cnt d = (its, c, nx', cnt')" and "its \<noteq> []"
  shows "\<exists>rl. last its = FLine c (dForm d) rl"
  using assms by (cases d; cases "dRule d") (auto simp: Let_def split: prod.splits)

lemma emit_nil_leaf:
  assumes "emit base G nx cnt d = ([], c, nx', cnt')"
  shows "\<exists>a. dRule d = DAssume a \<or> dRule d = DPremise a"
  using assms by (cases d; cases "dRule d") (auto simp: Let_def split: prod.splits)

theorem derivationToFitch_conclusion:
  "fitchConclusion (derivationToFitch d) = Some (dForm d)"
proof -
  let ?G = "premEnv d"
  obtain its c nx cnt
    where e: "emit (Suc (maxlen (namesD d))) ?G (Suc (length ?G)) 0 d = (its, c, nx, cnt)"
    by (rule prod_cases4)
  have F: "derivationToFitch d = premLines ?G @ its"
    by (simp add: derivationToFitch_def e)
  show ?thesis
  proof (cases "its = []")
    case False
    then obtain rl where lst: "last its = FLine c (dForm d) rl"
      using emit_conclusion_line [OF e] by blast
    have flat: "flatten (derivationToFitch d) = flatItems (premLines ?G) [] @ flatItems its []"
      unfolding F by (simp add: flatten_eq)
    from False have ne: "flatItems its [] \<noteq> []" by (rule flatItems_nonempty)
    have "last (flatten (derivationToFitch d)) = last (flatItems its [])"
      unfolding flat using ne by simp
    also from False have "\<dots> = last (flatItem (last its) [])" by (rule last_flatItems)
    also have "\<dots> = FL c (dForm d) rl []" by (simp add: lst)
    finally have "flFm (last (flatten (derivationToFitch d))) = dForm d" by simp
    moreover from ne have "flatten (derivationToFitch d) \<noteq> []" unfolding flat by simp
    ultimately show ?thesis by (simp add: fitchConclusion_def)
  next
    case True
    with e obtain a where "dRule d = DAssume a \<or> dRule d = DPremise a"
      using emit_nil_leaf by blast
    then have "openAsms d = [(a, dForm d)]" by (cases d) auto
    then have "?G = [(a, 1, dForm d)]" by (simp add: premEnv_def)
    with True F show ?thesis
      by (simp add: premLines_def flatten_eq fitchConclusion_def)
  qed
qed

section \<open>The premises of the image\<close>

text \<open>@{const derivationToFitch} emits one premise line for each undischarged
  leaf of the derivation, and nothing else it emits is a premise line.  So the
  assumptions the image asserts are exactly the ones the derivation rests on.
  With @{thm [source] derivationToFitch_conclusion} this fixes both sides of
  the sequent the image carries.\<close>

lemma premEnv_fms_aux:
  "map (\<lambda>e. snd (snd e))
       (map (\<lambda>ke. (fst (snd ke), Suc (fst ke), snd (snd ke))) (List.enumerate n xs))
     = map snd xs"
  by (induction xs arbitrary: n) auto

lemma premEnv_fms:
  "map (\<lambda>e. snd (snd e)) (premEnv d) = map snd (sort_key fst (remdups (openAsms d)))"
  unfolding premEnv_def by (rule premEnv_fms_aux)

lemma set_premEnv_fms: "set (map (\<lambda>e. snd (snd e)) (premEnv d)) = set (openFms d)"
proof -
  have "set (map (\<lambda>e. snd (snd e)) (premEnv d))
          = snd ` set (sort_key fst (remdups (openAsms d)))"
    by (simp add: premEnv_fms)
  also have "set (sort_key fst (remdups (openAsms d))) = set (openAsms d)"
    by simp
  finally show ?thesis by simp
qed

theorem derivationToFitch_premises:
  "set (fitchPremises (derivationToFitch d)) = set (openFms d)"
proof -
  let ?G = "premEnv d"
  let ?base = "Suc (maxlen (namesD d))"
  obtain its c nx cnt where e: "emit ?base ?G (Suc (length ?G)) 0 d = (its, c, nx, cnt)"
    by (rule prod_cases4)
  let ?F = "premLines ?G @ its"
  have F: "derivationToFitch d = ?F" by (simp add: derivationToFitch_def e)
  from emit_inv [OF boundIn_premEnv [of d], where base = ?base
                 and nx = "Suc (length ?G)" and cnt = 0] e
  have E: "emitInv ?G (Suc (length ?G)) its c nx" by simp
  then have B: "blockInv (Suc (length ?G)) its nx" by (simp add: emitInv_def)
  then have npi: "list_all noPremItem its" by (simp add: blockInv_def)
  have flat: "flatten ?F = flatItems (premLines ?G) [] @ flatItems its []"
    by (simp add: flatten_eq)
  have p1: "filter (\<lambda>fl. flRule fl = FPremise) (flatItems (premLines ?G) [])
              = flatItems (premLines ?G) []"
    by (simp add: filter_id_conv)
  have p2: "filter (\<lambda>fl. flRule fl = FPremise) (flatItems its []) = []"
    using noPrem_flatItems [OF npi] by (simp add: filter_empty_conv)
  have "fitchPremises ?F = map flFm (flatItems (premLines ?G) [])"
    unfolding fitchPremises_def flat by (simp add: p1 p2)
  also have "\<dots> = map (\<lambda>e. snd (snd e)) ?G" by (simp add: comp_def)
  finally show ?thesis using F set_premEnv_fms [of d] by simp
qed

end
