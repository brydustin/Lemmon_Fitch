(* T2: what the erasure delta_H makes of an emitted Fitch proof. *)

theory LF_HLW_Erasure
  imports LF_HLW_Nesting
begin

section \<open>The erasure preserves the flattened shape\<close>

lemma hlFlattenFitch_numbers:
  "map fst (hlFlattenFitch F) = hlFitchLineNumbers F"
  "map fst (hlFlattenFitchItem i) = hlFitchItemLineNumbers i"
  by (induction F and i rule: hlFlattenFitch_hlFlattenFitchItem.induct) auto

lemma hlFitchToLemmonFrom_numbers:
  "map hlLineNumber (snd (hlFitchToLemmonFrom env ls)) = map fst ls"
  by (induction ls arbitrary: env)
     (auto simp: Let_def case_prod_beta split: prod.splits)

lemma hlFitchToLemmonFrom_justifications:
  "map hlJustification (snd (hlFitchToLemmonFrom env ls)) =
   map (\<lambda>t. hlToLemmonRule (snd (snd t))) ls"
  by (induction ls arbitrary: env)
     (auto simp: Let_def case_prod_beta split: prod.splits)

lemma hlFitchToLemmon_numbers:
  "map hlLineNumber (hlFitchToLemmon F) = hlFitchLineNumbers F"
  by (simp add: hlFitchToLemmon_def hlFitchToLemmonFrom_numbers hlFlattenFitch_numbers)

lemma hlFitchToLemmon_justifications:
  "map hlJustification (hlFitchToLemmon F) =
   map (\<lambda>t. hlToLemmonRule (snd (snd t))) (hlFlattenFitch F)"
  by (simp add: hlFitchToLemmon_def hlFitchToLemmonFrom_justifications)

section \<open>Canonical order\<close>

text \<open>The erasure renumbers nothing, so the emitter's allocation invariant is
  already the Lemmon-side order condition.\<close>

lemma hlFitchToLemmon_canonicalOrder:
  assumes "list_all (\<lambda>n. 0 < n) (hlFitchLineNumbers F)"
      and "sorted_wrt (<) (hlFitchLineNumbers F)"
  shows "hlCanonicalOrder (hlFitchToLemmon F)"
  using assms by (simp add: hlCanonicalOrder_def hlFitchToLemmon_numbers)

theorem hlClassifiedDerivationToFitch_canonicalOrder:
  "hlCanonicalOrder (\<delta>\<^sub>H (hlDerivationToFitch (hlClassifyAssumptions {} d)))"
  using hlDerivationToFitch_positive_sorted[of "hlClassifyAssumptions {} d"]
  by (simp add: hlFitchToLemmon_canonicalOrder)

section \<open>Dependency closure\<close>

text \<open>Every dependency set the erasure computes is built from lookups that
  bottom out at the \<open>{self}\<close> of a premise or assumption line, so it can only
  ever contain numbers of lines the Lemmon side calls \<^const>\<open>HL_Assumption\<close>.\<close>

lemma hlDependencyLookup_subset:
  "\<forall>q \<in> set env. snd q \<subseteq> A \<Longrightarrow> hlDependencyLookup env n \<subseteq> A"
  by (induction env) (auto split: if_splits)

lemma hlFitchDependenciesOf_subset:
  assumes look: "\<And>n. look n \<subseteq> A"
      and self: "r = HL_FPremise \<or> r = HL_FAssume \<Longrightarrow> s \<in> A"
  shows "hlFitchDependenciesOf look r s \<subseteq> A"
  using assms
  by (cases r) (auto simp: hlFitchDependenciesOf_def)

lemma hlFitchToLemmonFrom_dependencies:
  assumes "\<forall>q \<in> set env. snd q \<subseteq> A"
      and "\<forall>t \<in> set ls.
             (snd (snd t) = HL_FPremise \<or> snd (snd t) = HL_FAssume) \<longrightarrow> fst t \<in> A"
  shows "(\<forall>l \<in> set (snd (hlFitchToLemmonFrom env ls)). hlReferences l \<subseteq> A) \<and>
         (\<forall>q \<in> set (fst (hlFitchToLemmonFrom env ls)). snd q \<subseteq> A)"
  using assms
proof (induction ls arbitrary: env)
  case Nil
  then show ?case by simp
next
  case (Cons t ls)
  obtain n p r where t: "t = (n,p,r)" by (cases t) auto
  let ?G = "hlFitchDependenciesOf (hlDependencyLookup env) r n"
  have G: "?G \<subseteq> A"
    by (rule hlFitchDependenciesOf_subset)
       (use Cons.prems t hlDependencyLookup_subset[of env A] in auto)
  have env': "\<forall>q \<in> set ((n,?G) # env). snd q \<subseteq> A" using G Cons.prems(1) by auto
  have rest: "\<forall>u \<in> set ls.
      (snd (snd u) = HL_FPremise \<or> snd (snd u) = HL_FAssume) \<longrightarrow> fst u \<in> A"
    using Cons.prems(2) by auto
  from Cons.IH[OF env' rest] show ?case
    using G t by (auto simp: Let_def case_prod_beta split: prod.splits)
qed

text \<open>The Lemmon-side assumption lines of an erased proof are exactly the
  flattened premise and box-assumption lines: no other Fitch rule is sent to
  \<^const>\<open>HL_Assumption\<close> by \<^const>\<open>hlToLemmonRule\<close>.\<close>

definition hlFitchAssumptionNumbers :: "hl_fitch_proof \<Rightarrow> int set" where
  "hlFitchAssumptionNumbers F =
     fst ` {t \<in> set (hlFlattenFitch F).
              snd (snd t) = HL_FPremise \<or> snd (snd t) = HL_FAssume}"

lemma hlToLemmonRule_Assumption_iff:
  "hlToLemmonRule r = HL_Assumption \<longleftrightarrow> r = HL_FPremise \<or> r = HL_FAssume"
  by (cases r) auto

lemma hlFitchToLemmonFrom_lines:
  "map (\<lambda>l. (hlLineNumber l, hlJustification l)) (snd (hlFitchToLemmonFrom env ls))
   = map (\<lambda>t. (fst t, hlToLemmonRule (snd (snd t)))) ls"
  by (induction ls arbitrary: env)
     (auto simp: Let_def case_prod_beta split: prod.splits)

lemma hlFitchToLemmon_assumptions:
  "hlLineNumber ` {a \<in> set (\<delta>\<^sub>H F). hlJustification a = HL_Assumption} =
   hlFitchAssumptionNumbers F"
proof -
  have eq: "map (\<lambda>l. (hlLineNumber l, hlJustification l)) (\<delta>\<^sub>H F)
          = map (\<lambda>t. (fst t, hlToLemmonRule (snd (snd t)))) (hlFlattenFitch F)"
    unfolding hlFitchToLemmon_def by (rule hlFitchToLemmonFrom_lines)
  have "hlLineNumber ` {a \<in> set (\<delta>\<^sub>H F). hlJustification a = HL_Assumption}
      = fst ` {q \<in> set (map (\<lambda>l. (hlLineNumber l, hlJustification l)) (\<delta>\<^sub>H F)).
               snd q = HL_Assumption}"
    by force
  also have "\<dots> = fst ` {q \<in> set (map (\<lambda>t. (fst t, hlToLemmonRule (snd (snd t))))
                                   (hlFlattenFitch F)). snd q = HL_Assumption}"
    by (simp only: eq)
  also have "\<dots> = hlFitchAssumptionNumbers F"
    unfolding hlFitchAssumptionNumbers_def
    by (force simp: hlToLemmonRule_Assumption_iff)
  finally show ?thesis .
qed

theorem hlFitchToLemmon_dependencyClosed:
  "hlDependencyClosed (\<delta>\<^sub>H F)"
  unfolding hlDependencyClosed_def hlFitchToLemmon_assumptions
  using hlFitchToLemmonFrom_dependencies
          [of "[]" "hlFitchAssumptionNumbers F" "hlFlattenFitch F"]
  by (auto simp: hlFitchToLemmon_def hlFitchAssumptionNumbers_def)

section \<open>Citations point backwards\<close>

text \<open>The Lemmon justification of an erased line cites the ordinary lines the
  Fitch rule cited, together with both endpoints of each discharge pair.\<close>

abbreviation hlRuleSources :: "hl_fitch_rule \<Rightarrow> int set" where
  "hlRuleSources r \<equiv>
     set (hlFitchCitedLines r) \<union> (\<Union>q \<in> set (hlFitchCitedSubs r). {fst q, snd q})"

lemma hlCitedLines_toLemmonRule:
  "set (hlCitedLines (hlToLemmonRule r)) = hlRuleSources r"
  by (cases r) auto

lemma hlSubLastLine_mem:
  "hlSubLastLine (HL_Subproof a p body) \<in> set (a # hlFitchLineNumbers body)"
  by (cases "hlFitchLineNumbers body = []") auto

lemma hlTopLines_subset_numbers:
  "hlTopLines F \<subseteq> set (hlFitchLineNumbers F)"
  by (rule hlTopLines_subset)

lemma hlTopBoxes_endpoints:
  "q \<in> hlTopBoxes F \<Longrightarrow> fst q \<in> set (hlFitchLineNumbers F) \<and>
                        snd q \<in> set (hlFitchLineNumbers F)"
proof (induction F)
  case Nil
  then show ?case by simp
next
  case (Cons item F)
  show ?case
  proof (cases item)
    case (HL_FLine n p r)
    then show ?thesis using Cons by auto
  next
    case (HL_FSub sub)
    obtain a p body where sub: "sub = HL_Subproof a p body" by (cases sub) auto
    show ?thesis
      using Cons.prems Cons.IH hlSubLastLine_mem[of a p body]
      by (auto simp: HL_FSub sub)
  qed
qed

text \<open>Only strict sortedness of the emitted line numbers is needed, not the
  full allocation interval: everything a line may cite comes either from the
  ambient visible set or from an item that precedes it, and both lie below it.\<close>

lemma hlFitchNestingFrom_backwards:
  "hlFitchNestingFrom depth visible boxes F \<Longrightarrow>
   sorted_wrt (<) (hlFitchLineNumbers F) \<Longrightarrow>
   \<forall>m \<in> visible. \<forall>k \<in> set (hlFitchLineNumbers F). m < k \<Longrightarrow>
   \<forall>q \<in> boxes. \<forall>k \<in> set (hlFitchLineNumbers F). fst q < k \<and> snd q < k \<Longrightarrow>
   \<forall>t \<in> set (hlFlattenFitch F).
     \<forall>m \<in> set (hlCitedLines (hlToLemmonRule (snd (snd t)))). m < fst t"
proof (induction depth visible boxes F rule: hlFitchNestingFrom.induct)
  case (1 depth visible boxes)
  then show ?case by simp
next
  case (2 depth visible boxes n p r rest)
  from "2.prems"(1) have
    cits: "set (hlFitchCitedLines r) \<subseteq> visible"
    and subs: "set (hlFitchCitedSubs r) \<subseteq> boxes"
    and tail: "hlFitchNestingFrom depth (insert n visible) boxes rest"
    by simp_all
  have head: "\<forall>m \<in> set (hlCitedLines (hlToLemmonRule r)). m < n"
    using hlCitedLines_toLemmonRule[of r] cits subs "2.prems"(3,4) by fastforce
  have sorted: "sorted_wrt (<) (hlFitchLineNumbers rest)"
    using "2.prems"(2) by simp
  have below: "\<forall>k \<in> set (hlFitchLineNumbers rest). n < k"
    using "2.prems"(2) by simp
  have vis: "\<forall>m \<in> insert n visible. \<forall>k \<in> set (hlFitchLineNumbers rest). m < k"
    using below "2.prems"(3) by auto
  have bx: "\<forall>q \<in> boxes. \<forall>k \<in> set (hlFitchLineNumbers rest). fst q < k \<and> snd q < k"
    using "2.prems"(4) by auto
  from "2.IH"[OF tail sorted vis bx] head show ?case by simp
next
  case (3 depth visible boxes a p body rest)
  from "3.prems"(1) have
    body: "hlFitchNestingFrom (Suc depth) (insert a visible) {} body"
    and rest: "hlFitchNestingFrom depth visible
                 (insert (a,hlSubLastLine (HL_Subproof a p body)) boxes) rest"
    by simp_all
  have nums: "hlFitchLineNumbers (HL_FSub (HL_Subproof a p body) # rest) =
              a # hlFitchLineNumbers body @ hlFitchLineNumbers rest" by simp
  have sortedB: "sorted_wrt (<) (hlFitchLineNumbers body)"
    and sortedR: "sorted_wrt (<) (hlFitchLineNumbers rest)"
    using "3.prems"(2) by (simp_all add: sorted_wrt_append)
  have aB: "\<forall>k \<in> set (hlFitchLineNumbers body). a < k"
    and aR: "\<forall>k \<in> set (hlFitchLineNumbers rest). a < k"
    using "3.prems"(2) by (simp_all add: sorted_wrt_append)
  have BR: "\<forall>j \<in> set (hlFitchLineNumbers body). \<forall>k \<in> set (hlFitchLineNumbers rest). j < k"
    using "3.prems"(2) by (simp add: sorted_wrt_append)
  have visB: "\<forall>m \<in> insert a visible. \<forall>k \<in> set (hlFitchLineNumbers body). m < k"
    using aB "3.prems"(3) by auto
  have IHb: "\<forall>t \<in> set (hlFlattenFitch body).
     \<forall>m \<in> set (hlCitedLines (hlToLemmonRule (snd (snd t)))). m < fst t"
    by (rule "3.IH"(1)[OF body sortedB visB]) simp
  have lastR: "\<forall>k \<in> set (hlFitchLineNumbers rest).
                 hlSubLastLine (HL_Subproof a p body) < k"
    using hlSubLastLine_mem[of a p body] aR BR by auto
  have bxR: "\<forall>q \<in> insert (a,hlSubLastLine (HL_Subproof a p body)) boxes.
     \<forall>k \<in> set (hlFitchLineNumbers rest). fst q < k \<and> snd q < k"
    using aR lastR "3.prems"(4) by auto
  have visR: "\<forall>m \<in> visible. \<forall>k \<in> set (hlFitchLineNumbers rest). m < k"
    using "3.prems"(3) by auto
  have IHr: "\<forall>t \<in> set (hlFlattenFitch rest).
     \<forall>m \<in> set (hlCitedLines (hlToLemmonRule (snd (snd t)))). m < fst t"
    by (rule "3.IH"(2)[OF rest sortedR visR bxR])
  show ?case using IHb IHr by auto
qed

section \<open>Structural correctness of the erased proof\<close>

lemma hlFitchToLemmon_pairs_image:
  "(\<lambda>l. (hlLineNumber l, hlJustification l)) ` set (\<delta>\<^sub>H F) =
   (\<lambda>t. (fst t, hlToLemmonRule (snd (snd t)))) ` set (hlFlattenFitch F)"
proof -
  have "map (\<lambda>l. (hlLineNumber l, hlJustification l)) (\<delta>\<^sub>H F)
      = map (\<lambda>t. (fst t, hlToLemmonRule (snd (snd t)))) (hlFlattenFitch F)"
    unfolding hlFitchToLemmon_def by (rule hlFitchToLemmonFrom_lines)
  from arg_cong[where f=set, OF this] show ?thesis by simp
qed

lemma hlFitchToLemmon_backwards:
  assumes nest: "hlFitchNestingFrom 0 {} {} F"
      and sorted: "sorted_wrt (<) (hlFitchLineNumbers F)"
  shows "\<forall>l \<in> set (\<delta>\<^sub>H F).
           \<forall>m \<in> set (hlCitedLines (hlJustification l)). m < hlLineNumber l"
proof
  fix l assume l: "l \<in> set (\<delta>\<^sub>H F)"
  have "(hlLineNumber l, hlJustification l) \<in>
        (\<lambda>t. (fst t, hlToLemmonRule (snd (snd t)))) ` set (hlFlattenFitch F)"
    using l hlFitchToLemmon_pairs_image[of F] by blast
  then obtain t where t: "t \<in> set (hlFlattenFitch F)"
    and eq: "hlLineNumber l = fst t" "hlJustification l = hlToLemmonRule (snd (snd t))"
    by auto
  from hlFitchNestingFrom_backwards[OF nest sorted] t eq
  show "\<forall>m \<in> set (hlCitedLines (hlJustification l)). m < hlLineNumber l" by simp
qed

lemma sorted_wrt_less_distinct:
  "sorted_wrt (<) (xs :: int list) \<Longrightarrow> distinct xs"
  by (induction xs) auto

lemma distinct_map_filter_length:
  assumes "distinct (map f xs)" "x \<in> set xs"
  shows "length (filter (\<lambda>y. f y = f x) xs) = 1"
  using assms
proof (induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons y xs)
  show ?case
  proof (cases "y = x")
    case True
    have "filter (\<lambda>z. f z = f x) xs = []"
    proof (rule filter_False)
      show "\<forall>z \<in> set xs. \<not> f z = f x"
      proof
        fix z assume "z \<in> set xs"
        then have "f z \<in> f ` set xs" by simp
        moreover have "f x \<notin> f ` set xs" using Cons.prems(1) True by simp
        ultimately show "\<not> f z = f x" by auto
      qed
    qed
    then show ?thesis using True by simp
  next
    case False
    then have mem: "x \<in> set xs" using Cons.prems(2) by simp
    then have "f y \<noteq> f x" using Cons.prems(1) by auto
    then show ?thesis using Cons.IH[OF _ mem] Cons.prems(1) by simp
  qed
qed

theorem hlFitchToLemmon_structureOK:
  assumes nest: "hlFitchNestingFrom 0 {} {} F"
      and sorted: "sorted_wrt (<) (hlFitchLineNumbers F)"
  shows "\<forall>l \<in> set (\<delta>\<^sub>H F). hlStructureOK (\<delta>\<^sub>H F) l"
proof
  fix l assume l: "l \<in> set (\<delta>\<^sub>H F)"
  have "distinct (map hlLineNumber (\<delta>\<^sub>H F))"
    using sorted_wrt_less_distinct[OF sorted]
    by (simp add: hlFitchToLemmon_numbers)
  from distinct_map_filter_length[OF this l]
  have "length (filter (\<lambda>k. hlLineNumber k = hlLineNumber l) (\<delta>\<^sub>H F)) = 1" .
  then show "hlStructureOK (\<delta>\<^sub>H F) l"
    unfolding hlStructureOK_def
    using hlFitchToLemmon_backwards[OF nest sorted] l by simp
qed

section \<open>The erasure's environment agrees with the proof it builds\<close>

text \<open>\<^const>\<open>hlFitchDependenciesOf\<close> consults its lookup only at the lines the
  rule actually cites.\<close>

lemma hlFitchDependenciesOf_cong:
  "(\<forall>m \<in> hlRuleSources r. look m = look' m) \<Longrightarrow>
   hlFitchDependenciesOf look r s = hlFitchDependenciesOf look' r s"
  by (cases r) (auto simp: hlFitchDependenciesOf_def)

lemma hlDependencyLookup_append_miss:
  "\<forall>q \<in> set xs. fst q \<noteq> m \<Longrightarrow>
   hlDependencyLookup (xs @ ys) m = hlDependencyLookup ys m"
  by (induction xs) auto

text \<open>Reading the whole finished proof back as an environment gives the same
  answer, at every line a rule may cite, as the partial environment the
  erasure actually held when it computed that line.  Later lines cannot
  interfere because their numbers are larger and citations point backwards.\<close>

lemma hlFitchToLemmonFrom_zip:
  "hlFitchToLemmonFrom env ls = (env',P) \<Longrightarrow> length P = length ls"
  by (induction ls arbitrary: env env' P) (auto simp: Let_def split: prod.splits)

lemma hlFitchToLemmonFrom_refs_zip:
  "hlFitchToLemmonFrom env ls = (env',P) \<Longrightarrow>
   sorted_wrt (<) (map fst ls) \<Longrightarrow>
   (\<forall>t \<in> set ls. \<forall>m \<in> hlRuleSources (snd (snd t)). m < fst t) \<Longrightarrow>
   \<forall>(l,t) \<in> set (zip P ls).
     hlReferences l =
       hlFitchDependenciesOf
         (hlDependencyLookup
            (rev (map (\<lambda>k. (hlLineNumber k, hlReferences k)) P) @ env))
         (snd (snd t)) (fst t)"
proof (induction ls arbitrary: env env' P)
  case Nil
  then show ?case by simp
next
  case (Cons t ls)
  obtain n p r where t: "t = (n,p,r)" by (cases t) auto
  let ?G = "hlFitchDependenciesOf (hlDependencyLookup env) r n"
  obtain P' env2 where
    step: "hlFitchToLemmonFrom ((n,?G) # env) ls = (env2,P')"
    by (cases "hlFitchToLemmonFrom ((n,?G) # env) ls") auto
  have P: "P = HL_ProofLine n p (hlToLemmonRule r) ?G # P'"
    and env2: "env2 = env'"
    using Cons.prems(1) step t by (auto simp: Let_def split: prod.splits)
  let ?g = "\<lambda>k. (hlLineNumber k, hlReferences k)"
  have full: "rev (map ?g P) @ env = rev (map ?g P') @ (n,?G) # env"
    by (simp add: P)
  have sorted': "sorted_wrt (<) (map fst ls)" using Cons.prems(2) by simp
  have bwd': "\<forall>u \<in> set ls. \<forall>m \<in> hlRuleSources (snd (snd u)). m < fst u"
    using Cons.prems(3) by simp
  have IH: "\<forall>(l,u) \<in> set (zip P' ls).
      hlReferences l =
        hlFitchDependenciesOf
          (hlDependencyLookup (rev (map ?g P') @ (n,?G) # env)) (snd (snd u)) (fst u)"
    using Cons.IH[OF step sorted' bwd'] by simp
  have numbers: "map hlLineNumber P' = map fst ls"
    using hlFitchToLemmonFrom_numbers[of "(n,?G) # env" ls] step by simp
  have head: "hlReferences (HL_ProofLine n p (hlToLemmonRule r) ?G) =
      hlFitchDependenciesOf (hlDependencyLookup (rev (map ?g P) @ env)) r n"
  proof -
    have above: "\<forall>k \<in> set P'. n < hlLineNumber k"
    proof
      fix k assume k: "k \<in> set P'"
      have "hlLineNumber k \<in> set (map hlLineNumber P')" using k by simp
      then have "hlLineNumber k \<in> set (map fst ls)" using numbers by simp
      then show "n < hlLineNumber k" using Cons.prems(2) by (force simp: t)
    qed
    have miss: "\<forall>q \<in> set (rev (map ?g P')). fst q \<noteq> m" if "m < n" for m
    proof
      fix q assume "q \<in> set (rev (map ?g P'))"
      then obtain k where k: "k \<in> set P'" and q: "q = ?g k" by auto
      show "fst q \<noteq> m" using above k q that by auto
    qed
    have "\<forall>m \<in> hlRuleSources r.
        hlDependencyLookup (rev (map ?g P) @ env) m = hlDependencyLookup env m"
    proof
      fix m assume m: "m \<in> hlRuleSources r"
      then have lt: "m < n" using Cons.prems(3) t by auto
      then have ne: "n \<noteq> m" by simp
      show "hlDependencyLookup (rev (map ?g P) @ env) m = hlDependencyLookup env m"
        using hlDependencyLookup_append_miss[OF miss[OF lt], of "(n,?G) # env" ]
        by (simp add: full ne)
    qed
    from hlFitchDependenciesOf_cong[OF this] show ?thesis by simp
  qed
  show ?case using IH head by (simp add: P full t)
qed

section \<open>The dependency equation every rule demands\<close>

lemma hlDependencyLookup_mem:
  "distinct (map fst xs) \<Longrightarrow> (m,G) \<in> set xs \<Longrightarrow> hlDependencyLookup xs m = G"
  by (induction xs) (force simp: image_iff)+

lemma hlDependencyLookup_not_mem:
  "m \<notin> fst ` set xs \<Longrightarrow> hlDependencyLookup xs m = {}"
  by (induction xs) auto

lemma hlLookupLine_SomeD:
  "hlLookupLine P m = Some l \<Longrightarrow> l \<in> set P \<and> hlLineNumber l = m"
  by (induction P) (auto split: if_splits)

lemma hlLookupLine_NoneD:
  "hlLookupLine P m = None \<Longrightarrow> m \<notin> hlLineNumber ` set P"
  by (induction P) (auto split: if_splits)

lemma hlDependencyLookup_proof:
  assumes "distinct (map hlLineNumber P)"
  shows "hlDependencyLookup (rev (map (\<lambda>k. (hlLineNumber k, hlReferences k)) P)) =
         (\<lambda>m. case hlLookupLine P m of Some l \<Rightarrow> hlReferences l | None \<Rightarrow> {})"
proof (rule ext)
  fix m
  show "hlDependencyLookup (rev (map (\<lambda>k. (hlLineNumber k, hlReferences k)) P)) m =
        (case hlLookupLine P m of Some l \<Rightarrow> hlReferences l | None \<Rightarrow> {})"
  proof (cases "hlLookupLine P m")
    case None
    then have "m \<notin> fst ` set (rev (map (\<lambda>k. (hlLineNumber k, hlReferences k)) P))"
      using hlLookupLine_NoneD[OF None] by (force simp: image_iff)
    then show ?thesis using None by (simp add: hlDependencyLookup_not_mem)
  next
    case (Some l)
    from hlLookupLine_SomeD[OF Some] have l: "l \<in> set P" "hlLineNumber l = m" by auto
    have dist: "distinct (map fst (rev (map (\<lambda>k. (hlLineNumber k, hlReferences k)) P)))"
      using assms by (simp add: o_def rev_map[symmetric] comp_def)
    have "(m, hlReferences l) \<in> set (rev (map (\<lambda>k. (hlLineNumber k, hlReferences k)) P))"
      using l by force
    from hlDependencyLookup_mem[OF dist this] Some show ?thesis by simp
  qed
qed

text \<open>Every erased line's dependency set is exactly the union its Lemmon rule
  prescribes, read off the finished proof.  This is the whole dependency half
  of \<^const>\<open>hlRuleOK\<close>, and it holds for all twenty-one rules at once rather
  than case by case, because \<^const>\<open>hlFitchDependenciesOf\<close> was defined to
  compute that union.\<close>

theorem hlFitchToLemmon_references:
  assumes nest: "hlFitchNestingFrom 0 {} {} F"
      and sorted: "sorted_wrt (<) (hlFitchLineNumbers F)"
  shows "\<forall>(l,t) \<in> set (zip (\<delta>\<^sub>H F) (hlFlattenFitch F)).
           hlReferences l =
             hlFitchDependenciesOf
               (\<lambda>m. case hlLookupLine (\<delta>\<^sub>H F) m of
                       Some k \<Rightarrow> hlReferences k | None \<Rightarrow> {})
               (snd (snd t)) (fst t)"
proof -
  have bwd: "\<forall>t \<in> set (hlFlattenFitch F). \<forall>m \<in> hlRuleSources (snd (snd t)). m < fst t"
  proof (intro ballI)
    fix t m assume t: "t \<in> set (hlFlattenFitch F)" and m: "m \<in> hlRuleSources (snd (snd t))"
    show "m < fst t"
      using hlFitchNestingFrom_backwards[OF nest sorted] t m
      by (simp add: hlCitedLines_toLemmonRule)
  qed
  have sortedF: "sorted_wrt (<) (map fst (hlFlattenFitch F))"
    using sorted by (simp add: hlFlattenFitch_numbers)
  have dist: "distinct (map hlLineNumber (\<delta>\<^sub>H F))"
    using sorted_wrt_less_distinct[OF sorted] by (simp add: hlFitchToLemmon_numbers)
  obtain env' where run: "hlFitchToLemmonFrom [] (hlFlattenFitch F) = (env', \<delta>\<^sub>H F)"
    by (cases "hlFitchToLemmonFrom [] (hlFlattenFitch F)")
       (simp add: hlFitchToLemmon_def)
  from hlFitchToLemmonFrom_refs_zip[OF run sortedF bwd]
  show ?thesis by (simp add: hlDependencyLookup_proof[OF dist])
qed

section \<open>Reading a line of the erased proof off the Fitch side\<close>

lemma hlFitchToLemmonFrom_triples:
  "map (\<lambda>l. (hlLineNumber l, hlFormula l, hlJustification l))
       (snd (hlFitchToLemmonFrom env ls))
   = map (\<lambda>t. (fst t, fst (snd t), hlToLemmonRule (snd (snd t)))) ls"
  by (induction ls arbitrary: env)
     (auto simp: Let_def case_prod_beta split: prod.splits)

lemma hlFitchToLemmon_triples:
  "map (\<lambda>l. (hlLineNumber l, hlFormula l, hlJustification l)) (\<delta>\<^sub>H F)
   = map (\<lambda>t. (fst t, fst (snd t), hlToLemmonRule (snd (snd t)))) (hlFlattenFitch F)"
  unfolding hlFitchToLemmon_def by (rule hlFitchToLemmonFrom_triples)

lemma hlLookupLine_self:
  "distinct (map hlLineNumber P) \<Longrightarrow> l \<in> set P \<Longrightarrow>
   hlLookupLine P (hlLineNumber l) = Some l"
  by (induction P) (auto split: if_splits)

text \<open>Every flattened Fitch line has a counterpart in the erased proof with the
  same number, the same formula and the translated rule.\<close>

lemma hlFitchToLemmon_lookup:
  assumes dist: "distinct (hlFitchLineNumbers F)"
      and t: "t \<in> set (hlFlattenFitch F)"
  shows "\<exists>l. hlLookupLine (\<delta>\<^sub>H F) (fst t) = Some l \<and>
             hlFormula l = fst (snd t) \<and>
             hlJustification l = hlToLemmonRule (snd (snd t))"
proof -
  have distP: "distinct (map hlLineNumber (\<delta>\<^sub>H F))"
    using dist by (simp add: hlFitchToLemmon_numbers)
  have "(fst t, fst (snd t), hlToLemmonRule (snd (snd t)))
        \<in> set (map (\<lambda>u. (fst u, fst (snd u), hlToLemmonRule (snd (snd u))))
                      (hlFlattenFitch F))"
    using t by simp
  then have "(fst t, fst (snd t), hlToLemmonRule (snd (snd t)))
        \<in> set (map (\<lambda>l. (hlLineNumber l, hlFormula l, hlJustification l)) (\<delta>\<^sub>H F))"
    by (simp only: hlFitchToLemmon_triples)
  then obtain l where l: "l \<in> set (\<delta>\<^sub>H F)"
    and eq: "hlLineNumber l = fst t" "hlFormula l = fst (snd t)"
            "hlJustification l = hlToLemmonRule (snd (snd t))"
    by auto
  from hlLookupLine_self[OF distP l] eq show ?thesis by auto
qed

section \<open>The number an emitted fragment returns names its own formula\<close>

text \<open>A non-empty fragment ends on the line carrying its conclusion; an empty
  one is a leaf that returns a line already in the environment.  No induction
  is needed --- the two existing emitter facts cover both cases.\<close>

lemma hlFlattenFitch_mem_line:
  "HL_FLine n p r \<in> set F \<Longrightarrow> (n,p,r) \<in> set (hlFlattenFitch F)"
  by (induction F) auto

lemma hlEmitDerivationFuel_returns_formula:
  assumes emit: "hlEmitDerivationFuel fuel base env scope first count d = (items,n,after,cnt)"
      and enough: "size d < length fuel"
      and envF: "\<forall>nf \<in> set (hlOpenAssumptions d).
                   look (hlEnvironmentLine env (fst nf)) = Some (snd nf)"
      and itemsF: "\<forall>t \<in> set (hlFlattenFitch items). look (fst t) = Some (fst (snd t))"
  shows "look n = Some (hlDerivationFormula d)"
proof (cases "items = []")
  case False
  from hlEmitDerivationFuel_last[OF emit False] obtain r where
    lst: "last items = HL_FLine n (hlDerivationFormula d) r" by blast
  have "HL_FLine n (hlDerivationFormula d) r \<in> set items"
    using False lst last_in_set by fastforce
  from hlFlattenFitch_mem_line[OF this] itemsF show ?thesis by fastforce
next
  case True
  from enough have fuel: "fuel \<noteq> []" by auto
  have empty: "hlEmitDerivationFuel fuel base env scope first count d = ([],n,after,cnt)"
    using emit True by simp
  from hlEmitDerivationFuel_empty[OF fuel empty] obtain i where
    leaf: "d = HL_Derivation (hlDerivationFormula d) (HL_DAssume i) \<or>
           d = HL_Derivation (hlDerivationFormula d) (HL_DPremise i)"
    and num: "n = hlEnvironmentLine env i" by blast
  obtain f rl where d: "d = HL_Derivation f rl" by (cases d) auto
  have "rl = HL_DAssume i \<or> rl = HL_DPremise i" using leaf d by auto
  then have "hlOpenAssumptions d = [(i,f)]" using d by auto
  then show ?thesis using envF num d by fastforce
qed

section \<open>Per-rule interfaces to \<^const>\<open>hlRuleOK\<close>\<close>

text \<open>Each of these turns the shape facts the emitter can supply -- what the
  cited lines are, what formulas they carry, and the dependency union already
  proved in \<open>hlFitchToLemmon_references\<close> -- into the corresponding branch of
  \<^const>\<open>hlRuleOK\<close>.  They are the interface the emitter induction has to meet,
  one per authoritative rule.\<close>

lemma hlRuleOK_Assumption:
  "hlJustification l = HL_Assumption \<Longrightarrow> hlReferences l = {hlLineNumber l} \<Longrightarrow>
   hlRuleOK P l"
  by (simp add: hlRuleOK_def)

lemma hlRuleOK_MP:
  assumes "hlJustification l = HL_MP m n"
      and "hlLookupLine P m = Some lm" "hlLookupLine P n = Some ln"
      and "hlFormula lm = HL_Implies (hlFormula ln) (hlFormula l)"
      and "hlReferences l = hlReferences lm \<union> hlReferences ln"
  shows "hlRuleOK P l"
  using assms by (simp add: hlRuleOK_def)

lemma hlRuleOK_DN:
  assumes "hlJustification l = HL_DN m"
      and "hlLookupLine P m = Some lm"
      and "hlFormula lm = HL_Not (HL_Not (hlFormula l)) \<or>
           hlFormula l = HL_Not (HL_Not (hlFormula lm))"
      and "hlReferences l = hlReferences lm"
  shows "hlRuleOK P l"
  using assms by (auto simp: hlRuleOK_def)

lemma hlRuleOK_AndIntro:
  assumes "hlJustification l = HL_AndIntro m n"
      and "hlLookupLine P m = Some lm" "hlLookupLine P n = Some ln"
      and "hlFormula l = HL_And (hlFormula lm) (hlFormula ln) \<or>
           hlFormula l = HL_And (hlFormula ln) (hlFormula lm)"
      and "hlReferences l = hlReferences lm \<union> hlReferences ln"
  shows "hlRuleOK P l"
  using assms by (auto simp: hlRuleOK_def)

lemma hlRuleOK_AndElim:
  assumes "hlJustification l = HL_AndElim m"
      and "hlLookupLine P m = Some lm"
      and "\<exists>p q. hlFormula lm = HL_And p q \<and> (hlFormula l = p \<or> hlFormula l = q)"
      and "hlReferences l = hlReferences lm"
  shows "hlRuleOK P l"
  using assms by (auto simp: hlRuleOK_def)

lemma hlRuleOK_OrIntro:
  assumes "hlJustification l = HL_OrIntro m"
      and "hlLookupLine P m = Some lm"
      and "\<exists>p q. hlFormula l = HL_Or p q \<and> (hlFormula lm = p \<or> hlFormula lm = q)"
      and "hlReferences l = hlReferences lm"
  shows "hlRuleOK P l"
  using assms by (auto simp: hlRuleOK_def)

lemma hlRuleOK_CP:
  assumes "hlJustification l = HL_CP a c"
      and "hlLookupLine P a = Some la" "hlLookupLine P c = Some lc"
      and "hlJustification la = HL_Assumption"
      and "hlFormula l = HL_Implies (hlFormula la) (hlFormula lc)"
      and "hlReferences l = hlReferences lc - {hlLineNumber la}"
  shows "hlRuleOK P l"
  using assms by (simp add: hlRuleOK_def)

lemma hlRuleOK_RAA:
  assumes "hlJustification l = HL_RAA a c"
      and "hlLookupLine P a = Some la" "hlLookupLine P c = Some lc"
      and "hlJustification la = HL_Assumption"
      and "hlFormula l = HL_Not (hlFormula la)"
      and "hlContradiction (hlFormula lc)"
      and "hlReferences l = hlReferences lc - {hlLineNumber la}"
  shows "hlRuleOK P l"
  using assms by (simp add: hlRuleOK_def)

lemma hlRuleOK_OrElim:
  assumes "hlJustification l = HL_OrElim d a1 c1 a2 c2"
      and "hlLookupLine P d = Some ld"
      and "hlLookupLine P a1 = Some la1" "hlLookupLine P c1 = Some lc1"
      and "hlLookupLine P a2 = Some la2" "hlLookupLine P c2 = Some lc2"
      and "hlJustification la1 = HL_Assumption" "hlJustification la2 = HL_Assumption"
      and "hlFormula lc1 = hlFormula l" "hlFormula lc2 = hlFormula l"
      and "hlFormula ld = HL_Or (hlFormula la1) (hlFormula la2) \<or>
           hlFormula ld = HL_Or (hlFormula la2) (hlFormula la1)"
      and "hlReferences l = hlReferences ld \<union>
             (hlReferences lc1 - {hlLineNumber la1}) \<union>
             (hlReferences lc2 - {hlLineNumber la2})"
  shows "hlRuleOK P l"
  using assms by (auto simp: hlRuleOK_def)

lemma hlRuleOK_LEM:
  "hlJustification l = HL_LEM \<Longrightarrow> hlExcludedMiddle (hlFormula l) \<Longrightarrow> hlRuleOK P l"
  by (simp add: hlRuleOK_def)

section \<open>Dependencies track the open assumptions of the emitted tree\<close>

text \<open>This is what the two eigenconstant rules need.  \<^const>\<open>hlForallIntroStep\<close>
  states its freshness side condition against the \<^emph>\<open>derivation's\<close> open
  assumption formulas, while \<^const>\<open>hlRuleOK\<close> states it against the
  \<^emph>\<open>proof's\<close> assumption lines named in the dependency set.  The two agree
  exactly when an emitted line's dependency set is the set of environment lines
  of the subderivation's open assumptions, which is what is proved here.\<close>

abbreviation hlRefsF :: "hl_proof \<Rightarrow> int \<Rightarrow> int set" where
  "hlRefsF Q m \<equiv> (case hlLookupLine Q m of Some k \<Rightarrow> hlReferences k | None \<Rightarrow> {})"

abbreviation hlLookF :: "hl_proof \<Rightarrow> int \<Rightarrow> hl_formula option" where
  "hlLookF Q m \<equiv> map_option hlFormula (hlLookupLine Q m)"

definition hlEnvImage :: "hl_layout_environment \<Rightarrow> hl_derivation \<Rightarrow> int set" where
  "hlEnvImage env d =
     (\<lambda>nf. hlEnvironmentLine env (fst nf)) ` set (hlOpenAssumptions d)"

definition hlEnvBelow :: "hl_layout_environment \<Rightarrow> int \<Rightarrow> bool" where
  "hlEnvBelow env k \<longleftrightarrow> (\<forall>q \<in> set env. fst (snd q) < k)"

lemma hlEnvBelow_mono:
  "hlEnvBelow env k \<Longrightarrow> k \<le> j \<Longrightarrow> hlEnvBelow env j"
  by (auto simp: hlEnvBelow_def)

lemma hlEnvBelow_Cons:
  "hlEnvBelow env k \<Longrightarrow> m < j \<Longrightarrow> k \<le> j \<Longrightarrow> hlEnvBelow ((i,m,p) # env) j"
  by (auto simp: hlEnvBelow_def)

lemma hlEnvironmentLine_below:
  "hlEnvBelow env k \<Longrightarrow> i \<in> fst ` set env \<Longrightarrow> hlEnvironmentLine env i < k"
proof (induction env)
  case Nil
  then show ?case by simp
next
  case (Cons e env)
  obtain a m q where e: "e = (a,m,q)" by (cases e) auto
  show ?case
  proof (cases "a = i")
    case True
    then show ?thesis using Cons.prems e by (simp add: hlEnvBelow_def)
  next
    case False
    then have "i \<in> fst ` set env" using Cons.prems(2) e by auto
    then show ?thesis using Cons.IH Cons.prems(1) e False
      by (simp add: hlEnvBelow_def)
  qed
qed

lemma hlEnvImage_Cons_other:
  "hlEnvironmentLine ((a,m,p) # env) i =
     (if a = i then m else hlEnvironmentLine env i)"
  by simp

text \<open>Extending the environment with a freshly allocated assumption line only
  adds that line to the image, and never collides with an older one.\<close>

lemma hlEnvImage_drop:
  assumes below: "hlEnvBelow env m"
      and covered: "\<forall>nf \<in> set (hlOpenAssumptions e). fst nf \<noteq> a \<longrightarrow> fst nf \<in> fst ` set env"
  shows "hlEnvImage ((a,m,p) # env) e - {m} =
         hlEnvImage env (HL_Derivation f (HL_DCP a p e))"
proof -
  have "hlEnvImage ((a,m,p) # env) e - {m}
      = (\<lambda>nf. hlEnvironmentLine env (fst nf)) `
          {nf \<in> set (hlOpenAssumptions e). fst nf \<noteq> a}"
  proof (rule set_eqI, rule iffI)
    fix x assume "x \<in> hlEnvImage ((a,m,p) # env) e - {m}"
    then obtain nf where nf: "nf \<in> set (hlOpenAssumptions e)"
      and x: "x = hlEnvironmentLine ((a,m,p) # env) (fst nf)" and ne: "x \<noteq> m"
      by (auto simp: hlEnvImage_def)
    have "fst nf \<noteq> a" using x ne by (auto split: if_splits)
    then show "x \<in> (\<lambda>nf. hlEnvironmentLine env (fst nf)) `
                    {nf \<in> set (hlOpenAssumptions e). fst nf \<noteq> a}"
      using nf x by auto
  next
    fix x assume "x \<in> (\<lambda>nf. hlEnvironmentLine env (fst nf)) `
                       {nf \<in> set (hlOpenAssumptions e). fst nf \<noteq> a}"
    then obtain nf where nf: "nf \<in> set (hlOpenAssumptions e)" "fst nf \<noteq> a"
      and x: "x = hlEnvironmentLine env (fst nf)" by auto
    have "hlEnvironmentLine env (fst nf) < m"
      using hlEnvironmentLine_below[OF below] covered nf by auto
    then show "x \<in> hlEnvImage ((a,m,p) # env) e - {m}"
      using nf x by (auto simp: hlEnvImage_def)
  qed
  then show ?thesis by (simp add: hlEnvImage_def)
qed

lemma hlEnvImage_rename [simp]:
  "hlEnvImage env (hlRenameDerivation old new d) = hlEnvImage env d"
  by (simp add: hlEnvImage_def hlOpenAssumptions_rename image_image)

lemma hlEnvImage_repair:
  "hlRepairDerivation base count bad d = (count',pairs,d') \<Longrightarrow>
   hlEnvImage env d' = hlEnvImage env d"
  by (induction bad arbitrary: count d count' pairs d')
     (auto simp: Let_def split: prod.splits)

lemma hlEnvImage_simps [simp]:
  "hlEnvImage env (HL_Derivation f (HL_DMP d e)) =
     hlEnvImage env d \<union> hlEnvImage env e"
  "hlEnvImage env (HL_Derivation f (HL_DMT d e)) =
     hlEnvImage env d \<union> hlEnvImage env e"
  "hlEnvImage env (HL_Derivation f (HL_DAndI d e)) =
     hlEnvImage env d \<union> hlEnvImage env e"
  "hlEnvImage env (HL_Derivation f (HL_DEqE d e)) =
     hlEnvImage env d \<union> hlEnvImage env e"
  "hlEnvImage env (HL_Derivation f (HL_DIffI d e)) =
     hlEnvImage env d \<union> hlEnvImage env e"
  "hlEnvImage env (HL_Derivation f (HL_DIffE d e)) =
     hlEnvImage env d \<union> hlEnvImage env e"
  "hlEnvImage env (HL_Derivation f (HL_DDN d)) = hlEnvImage env d"
  "hlEnvImage env (HL_Derivation f (HL_DAndE d)) = hlEnvImage env d"
  "hlEnvImage env (HL_Derivation f (HL_DOrI d)) = hlEnvImage env d"
  "hlEnvImage env (HL_Derivation f (HL_DForallE d)) = hlEnvImage env d"
  "hlEnvImage env (HL_Derivation f (HL_DForallI d)) = hlEnvImage env d"
  "hlEnvImage env (HL_Derivation f (HL_DExistsI d)) = hlEnvImage env d"
  "hlEnvImage env (HL_Derivation f (HL_DQN d)) = hlEnvImage env d"
  "hlEnvImage env (HL_Derivation f HL_DEqI) = {}"
  "hlEnvImage env (HL_Derivation f HL_DLEM) = {}"
  "hlEnvImage env (HL_Derivation f (HL_DPropTaut ds)) =
     (\<Union>e \<in> set ds. hlEnvImage env e)"
  by (auto simp: hlEnvImage_def)

lemma hlEnvImage_leaf [simp]:
  "hlEnvImage env (HL_Derivation f (HL_DAssume i)) = {hlEnvironmentLine env i}"
  "hlEnvImage env (HL_Derivation f (HL_DPremise i)) = {hlEnvironmentLine env i}"
  by (auto simp: hlEnvImage_def)

text \<open>The bundled hypothesis carried through the emitter induction.\<close>

definition hlDepsCtx ::
    "hl_proof \<Rightarrow> hl_layout_environment \<Rightarrow> int \<Rightarrow> hl_derivation \<Rightarrow> bool" where
  "hlDepsCtx Q env k d \<longleftrightarrow>
     hlEnvBelow env k \<and>
     (\<forall>nf \<in> set (hlOpenAssumptions d). fst nf \<in> fst ` set env) \<and>
     (\<forall>nf \<in> set (hlOpenAssumptions d).
        hlRefsF Q (hlEnvironmentLine env (fst nf)) =
          {hlEnvironmentLine env (fst nf)})"

lemma hlDepsCtx_sub:
  "hlDepsCtx Q env k d \<Longrightarrow>
   set (hlOpenAssumptions e) \<subseteq> set (hlOpenAssumptions d) \<Longrightarrow>
   k \<le> j \<Longrightarrow> hlDepsCtx Q env j e"
  by (auto simp: hlDepsCtx_def hlEnvBelow_def)

abbreviation hlItemsDeps :: "hl_proof \<Rightarrow> hl_fitch_proof \<Rightarrow> bool" where
  "hlItemsDeps Q items \<equiv>
     (\<forall>t \<in> set (hlFlattenFitch items).
        hlRefsF Q (fst t) =
          hlFitchDependenciesOf (hlRefsF Q) (snd (snd t)) (fst t))"

end
