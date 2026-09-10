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

end
