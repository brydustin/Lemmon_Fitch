(* T3: the emitted Fitch proof is correct, and the construction theorem. *)

theory LF_HLW_Construct
  imports LF_HLW_Erasure
begin

section \<open>The premise environment is functional\<close>

text \<open>\<^const>\<open>hlEnvironmentLine\<close> returns the first entry with a given source, so
  the root environment only describes the open assumptions if no source carries
  two different formulas.  That is automatic for a tree unfolded from a proof:
  a source is a line number, and a line carries one formula.\<close>

definition hlAssumptionsFunctional :: "hl_derivation \<Rightarrow> bool" where
  "hlAssumptionsFunctional d \<longleftrightarrow>
     (\<forall>nf \<in> set (hlOpenAssumptions d). \<forall>mg \<in> set (hlOpenAssumptions d).
        fst nf = fst mg \<longrightarrow> snd nf = snd mg)"

lemma hlNumberPremises_mem:
  "(s,n,p) \<in> set (hlNumberPremises k G) \<Longrightarrow> (s,p) \<in> set G"
proof (induction G arbitrary: k)
  case Nil
  then show ?case by simp
next
  case (Cons g G)
  obtain a b where g: "g = (a,b)" by (cases g) auto
  from Cons.prems g
  have "(s,n,p) = (a,k,b) \<or> (s,n,p) \<in> set (hlNumberPremises (k + 1) G)" by simp
  then show ?case using Cons.IH g by auto
qed

lemma hlNumberPremises_mem_rev:
  "(s,p) \<in> set G \<Longrightarrow> \<exists>n. (s,n,p) \<in> set (hlNumberPremises k G)"
proof (induction G arbitrary: k)
  case Nil
  then show ?case by simp
next
  case (Cons g G)
  obtain a b where g: "g = (a,b)" by (cases g) auto
  show ?case
  proof (cases "(s,p) = (a,b)")
    case True
    then show ?thesis using g by auto
  next
    case False
    then have "(s,p) \<in> set G" using Cons.prems g by auto
    then show ?thesis using Cons.IH[of "k + 1"] g by auto
  qed
qed

lemma hlNumberPremises_fst:
  "map fst (hlNumberPremises k G) = map fst G"
proof (induction G arbitrary: k)
  case Nil
  then show ?case by simp
next
  case (Cons g G)
  obtain a b where g: "g = (a,b)" by (cases g) auto
  show ?case using Cons.IH[of "k + 1"] g by simp
qed

lemma hlNumberPremises_below:
  "(s,n,p) \<in> set (hlNumberPremises k G) \<Longrightarrow> k \<le> n \<and> n < k + int (length G)"
proof (induction G arbitrary: k)
  case Nil
  then show ?case by simp
next
  case (Cons g G)
  obtain a b where g: "g = (a,b)" by (cases g) auto
  from Cons.prems g
  have "(s,n,p) = (a,k,b) \<or> (s,n,p) \<in> set (hlNumberPremises (k + 1) G)" by simp
  then show ?case using Cons.IH[of "k + 1"] g by fastforce
qed

lemma fst_distinct_unique:
  "distinct (map fst L) \<Longrightarrow> q \<in> set L \<Longrightarrow> r \<in> set L \<Longrightarrow> fst q = fst r \<Longrightarrow> q = r"
  by (auto simp: distinct_map inj_on_def)

lemma hlEnvironmentLine_unique:
  assumes mem: "(s,n,p) \<in> set env"
      and fn: "distinct (map fst env)"
  shows "hlEnvironmentLine env s = n"
  using assms
proof (induction env)
  case Nil
  then show ?case by simp
next
  case (Cons e env)
  obtain a m q where e: "e = (a,m,q)" by (cases e) auto
  show ?case
  proof (cases "a = s")
    case True
    have "(s,n,p) \<notin> set env" using Cons.prems(2) e True by force
    then have "(s,n,p) = (a,m,q)" using Cons.prems(1) e by auto
    then show ?thesis using e True by simp
  next
    case False
    then have "(s,n,p) \<in> set env" using Cons.prems(1) e by auto
    then show ?thesis using Cons.IH Cons.prems(2) e False by simp
  qed
qed

lemma hlPremiseEnvironment_distinct_fst:
  assumes fn: "hlAssumptionsFunctional d"
      and root: "set (hlPremisesOf d) = set (hlOpenAssumptions d)"
  shows "distinct (map fst (hlPremiseEnvironment d))"
proof -
  let ?L = "remdups (hlPremisesOf d)"
  let ?G = "sort_key fst ?L"
  have setG: "set ?G = set (hlOpenAssumptions d)" using root by simp
  have distG: "distinct ?G" by simp
  have "inj_on fst (set ?G)"
  proof (rule inj_onI)
    fix q r assume qr: "q \<in> set ?G" "r \<in> set ?G" "fst q = fst r"
    have qm: "q \<in> set (hlOpenAssumptions d)" and rm: "r \<in> set (hlOpenAssumptions d)"
      using qr(1,2) setG by auto
    have "snd q = snd r"
      using fn qm rm qr(3) unfolding hlAssumptionsFunctional_def by blast
    then show "q = r" using qr(3) by (cases q; cases r) simp
  qed
  with distG have "distinct (map fst ?G)" by (simp add: distinct_map)
  then show ?thesis by (simp add: hlPremiseEnvironment_def hlNumberPremises_fst)
qed

lemma hlPremiseEnvironment_line:
  assumes fn: "hlAssumptionsFunctional d"
      and root: "set (hlPremisesOf d) = set (hlOpenAssumptions d)"
      and nf: "nf \<in> set (hlOpenAssumptions d)"
  shows "\<exists>n. (fst nf,n,snd nf) \<in> set (hlPremiseEnvironment d) \<and>
             hlEnvironmentLine (hlPremiseEnvironment d) (fst nf) = n \<and>
             1 \<le> n \<and> n < 1 + int (length (hlPremiseEnvironment d))"
proof -
  have "(fst nf,snd nf) \<in> set (sort_key fst (remdups (hlPremisesOf d)))"
    using nf root by simp
  then obtain n where n: "(fst nf,n,snd nf) \<in> set (hlPremiseEnvironment d)"
    unfolding hlPremiseEnvironment_def using hlNumberPremises_mem_rev by blast
  have "hlEnvironmentLine (hlPremiseEnvironment d) (fst nf) = n"
    by (rule hlEnvironmentLine_unique[OF n hlPremiseEnvironment_distinct_fst[OF fn root]])
  moreover have "1 \<le> n \<and> n < 1 + int (length (hlPremiseEnvironment d))"
    using n hlNumberPremises_below
    by (fastforce simp: hlPremiseEnvironment_def)
  ultimately show ?thesis using n by blast
qed

lemma hlPremiseEnvironment_below:
  "hlEnvBelow (hlPremiseEnvironment d) (1 + int (length (hlPremiseEnvironment d)))"
  unfolding hlEnvBelow_def
proof
  fix q assume q: "q \<in> set (hlPremiseEnvironment d)"
  obtain s n p where qp: "q = (s,n,p)" by (cases q) auto
  then have "(s,n,p) \<in> set (hlNumberPremises 1 (sort_key fst (remdups (hlPremisesOf d))))"
    using q by (simp add: hlPremiseEnvironment_def)
  from hlNumberPremises_below[OF this]
  show "fst (snd q) < 1 + int (length (hlPremiseEnvironment d))"
    using qp by (simp add: hlPremiseEnvironment_def)
qed

section \<open>Reading the erased proof back at a flattened line\<close>

text \<open>The zip in \<open>hlFitchToLemmon_references\<close> is positional; since the two lists
  carry the same numbers in the same order, and those numbers are distinct, it
  is the same as a statement about \<^const>\<open>hlLookupLine\<close>.\<close>

lemma hlFitchToLemmon_itemsDeps:
  assumes nest: "hlFitchNestingFrom 0 {} {} F"
      and sorted: "sorted_wrt (<) (hlFitchLineNumbers F)"
      and t: "t \<in> set (hlFlattenFitch F)"
  shows "hlRefsF (\<delta>\<^sub>H F) (fst t) =
         hlFitchDependenciesOf (hlRefsF (\<delta>\<^sub>H F)) (snd (snd t)) (fst t)"
proof -
  have nums: "map hlLineNumber (\<delta>\<^sub>H F) = map fst (hlFlattenFitch F)"
    by (simp add: hlFitchToLemmon_numbers hlFlattenFitch_numbers)
  then have len: "length (\<delta>\<^sub>H F) = length (hlFlattenFitch F)"
    by (metis length_map)
  from t obtain i where i: "i < length (hlFlattenFitch F)" "hlFlattenFitch F ! i = t"
    by (meson in_set_conv_nth)
  have pair: "(\<delta>\<^sub>H F ! i, t) \<in> set (zip (\<delta>\<^sub>H F) (hlFlattenFitch F))"
    using i len by (auto simp: set_zip)
  have num: "hlLineNumber (\<delta>\<^sub>H F ! i) = fst t"
    using nums i len by (metis nth_map)
  have dist: "distinct (map hlLineNumber (\<delta>\<^sub>H F))"
    using sorted_wrt_less_distinct[OF sorted] by (simp add: hlFitchToLemmon_numbers)
  have look: "hlLookupLine (\<delta>\<^sub>H F) (fst t) = Some (\<delta>\<^sub>H F ! i)"
    using hlLookupLine_self[OF dist nth_mem[of i "\<delta>\<^sub>H F"]] num i len by simp
  have "hlReferences (\<delta>\<^sub>H F ! i) =
        hlFitchDependenciesOf (hlRefsF (\<delta>\<^sub>H F)) (snd (snd t)) (fst t)"
    using hlFitchToLemmon_references[OF nest sorted] pair by auto
  then show ?thesis using look by simp
qed

lemma hlFitchToLemmon_itemsCtx:
  assumes nest: "hlFitchNestingFrom 0 {} {} F"
      and sorted: "sorted_wrt (<) (hlFitchLineNumbers F)"
      and sub: "set (hlFlattenFitch G) \<subseteq> set (hlFlattenFitch F)"
  shows "hlItemsCtx (\<delta>\<^sub>H F) G"
proof (intro conjI ballI allI impI)
  have dist: "distinct (hlFitchLineNumbers F)" by (rule sorted_wrt_less_distinct[OF sorted])
  fix t assume t: "t \<in> set (hlFlattenFitch G)"
  then have tF: "t \<in> set (hlFlattenFitch F)" using sub by blast
  from hlFitchToLemmon_lookup[OF dist tF] show "hlLookF (\<delta>\<^sub>H F) (fst t) = Some (fst (snd t))"
    by auto
next
  have dist: "distinct (hlFitchLineNumbers F)" by (rule sorted_wrt_less_distinct[OF sorted])
  fix t l assume t: "t \<in> set (hlFlattenFitch G)"
    and l: "hlLookupLine (\<delta>\<^sub>H F) (fst t) = Some l"
  then have tF: "t \<in> set (hlFlattenFitch F)" using sub by blast
  from hlFitchToLemmon_lookup[OF dist tF] l
  show "hlJustification l = hlToLemmonRule (snd (snd t))" by auto
next
  fix t assume t: "t \<in> set (hlFlattenFitch G)"
  then have tF: "t \<in> set (hlFlattenFitch F)" using sub by blast
  show "hlRefsF (\<delta>\<^sub>H F) (fst t) =
        hlFitchDependenciesOf (hlRefsF (\<delta>\<^sub>H F)) (snd (snd t)) (fst t)"
    by (rule hlFitchToLemmon_itemsDeps[OF nest sorted tF])
qed

lemma hlPremiseFitchLines_flatten:
  "hlFlattenFitch (hlPremiseFitchLines env) =
   map (\<lambda>(source,n,phi). (n,phi,HL_FPremise)) env"
  by (induction env) (auto simp: hlPremiseFitchLines_def split: prod.splits)

lemma hlPremiseLine_erased:
  assumes nest: "hlFitchNestingFrom 0 {} {} F"
      and sorted: "sorted_wrt (<) (hlFitchLineNumbers F)"
      and t: "(n,p,HL_FPremise) \<in> set (hlFlattenFitch F)"
  shows "\<exists>l. hlLookupLine (\<delta>\<^sub>H F) n = Some l \<and> hlFormula l = p \<and>
             hlJustification l = HL_Assumption \<and> hlReferences l = {n}"
proof -
  have dist: "distinct (hlFitchLineNumbers F)" by (rule sorted_wrt_less_distinct[OF sorted])
  from hlFitchToLemmon_lookup[OF dist t] obtain l where
    l: "hlLookupLine (\<delta>\<^sub>H F) n = Some l" and lf: "hlFormula l = p"
    and lj: "hlJustification l = HL_Assumption" by auto
  have "hlRefsF (\<delta>\<^sub>H F) n = hlFitchDependenciesOf (hlRefsF (\<delta>\<^sub>H F)) HL_FPremise n"
    using hlFitchToLemmon_itemsDeps[OF nest sorted t] by simp
  then have "hlReferences l = {n}" using l by (simp add: hlFitchDependenciesOf_def)
  with l lf lj show ?thesis by blast
qed

section \<open>The root name bound\<close>

text \<open>\<^const>\<open>hlDerivationToFitch\<close> starts the repair counter at zero and picks
  a base one longer than every constant in the tree, which is exactly the
  invariant the emitter induction carries.\<close>

lemma hlNamesBelow_root:
  "hlNamesBelow (Suc (maxlen (sorted_list_of_set (hlDerivationConstants d)))) 0 d"
proof -
  have fin: "finite (hlDerivationConstants d)"
    by (simp add: hlDerivationConstants_def)
  have "nlen c < Suc (maxlen (sorted_list_of_set (hlDerivationConstants d)))"
    if "c \<in> hlDerivationConstants d" for c
  proof -
    have "c \<in> set (sorted_list_of_set (hlDerivationConstants d))"
      using that fin by simp
    from maxlen_ge[OF this] show ?thesis by simp
  qed
  then show ?thesis by (simp add: hlNamesBelow_def)
qed

section \<open>The emitted Fitch proof erases to a correct Lemmon proof\<close>

theorem hlDerivationToFitch_correct:
  assumes fn: "hlAssumptionsFunctional d"
      and root: "set (hlPremisesOf d) = set (hlOpenAssumptions d)"
      and ok: "hlDerivationOK d"
  shows "hlCorrect (\<delta>\<^sub>H (hlDerivationToFitch d)) \<and>
         hlFitchPremiseClosed (hlDerivationToFitch d)"
proof -
  let ?env = "hlPremiseEnvironment d"
  let ?pre = "hlPremiseFitchLines ?env"
  let ?base = "Suc (maxlen (sorted_list_of_set (hlDerivationConstants d)))"
  let ?first = "1 + int (length ?env)"
  obtain body k after cnt where
    em: "hlEmitDerivation ?base ?env (map (\<lambda>(source,n,phi). phi) ?env) ?first 0 d
         = (body,k,after,cnt)"
    by (cases "hlEmitDerivation ?base ?env (map (\<lambda>(source,n,phi). phi) ?env) ?first 0 d")
       auto
  have F: "hlDerivationToFitch d = ?pre @ body"
    using em unfolding hlDerivationToFitch_def hlDerivationConstants_def
    by (simp add: Let_def)
  let ?F = "hlDerivationToFitch d"
  let ?Q = "\<delta>\<^sub>H ?F"
  have nest: "hlFitchNestingFrom 0 {} {} ?F" by (rule hlDerivationToFitch_nesting[OF root])
  have sorted: "sorted_wrt (<) (hlFitchLineNumbers ?F)"
    using hlDerivationToFitch_positive_sorted[of d] by simp
  have distQ: "distinct (map hlLineNumber ?Q)"
    using sorted_wrt_less_distinct[OF sorted] by (simp add: hlFitchToLemmon_numbers)
  have nums: "map hlLineNumber ?Q = map fst (hlFlattenFitch ?F)"
    by (simp add: hlFitchToLemmon_numbers hlFlattenFitch_numbers)
  have flatF: "set (hlFlattenFitch ?F) =
               set (hlFlattenFitch ?pre) \<union> set (hlFlattenFitch body)"
    using F by (simp add: hlFlattenFitch_append)

  text \<open>Every premise line erases to an assumption depending on itself alone.\<close>
  have premise: "\<exists>l. hlLookupLine ?Q n = Some l \<and> hlFormula l = p \<and>
                     hlJustification l = HL_Assumption \<and> hlReferences l = {n}"
    if "(n,p,HL_FPremise) \<in> set (hlFlattenFitch ?pre)" for n p
    by (rule hlPremiseLine_erased[OF nest sorted]) (use that flatF in blast)

  have envline: "\<exists>n. hlEnvironmentLine ?env (fst nf) = n \<and>
                     (n,snd nf,HL_FPremise) \<in> set (hlFlattenFitch ?pre) \<and>
                     fst nf \<in> fst ` set ?env"
    if nf: "nf \<in> set (hlOpenAssumptions d)" for nf
  proof -
    from hlPremiseEnvironment_line[OF fn root nf] obtain n where
      n: "(fst nf,n,snd nf) \<in> set ?env" and line: "hlEnvironmentLine ?env (fst nf) = n"
      by blast
    have "(n,snd nf,HL_FPremise) \<in> set (hlFlattenFitch ?pre)"
      using n by (force simp: hlPremiseFitchLines_flatten)
    moreover have "fst nf \<in> fst ` set ?env" using n by force
    ultimately show ?thesis using line by blast
  qed

  have ctx: "hlEmitCtx ?Q ?env ?first d"
    unfolding hlEmitCtx_def hlDepsCtx_def hlFormCtx_def
  proof (intro conjI ballI)
    show "hlEnvBelow ?env ?first" by (rule hlPremiseEnvironment_below)
  next
    fix nf assume nf: "nf \<in> set (hlOpenAssumptions d)"
    show "fst nf \<in> fst ` set ?env" using envline[OF nf] by blast
  next
    fix nf assume nf: "nf \<in> set (hlOpenAssumptions d)"
    from envline[OF nf] obtain n where line: "hlEnvironmentLine ?env (fst nf) = n"
      and mem: "(n,snd nf,HL_FPremise) \<in> set (hlFlattenFitch ?pre)" by blast
    from premise[OF mem] obtain l where
      l: "hlLookupLine ?Q n = Some l" and lr: "hlReferences l = {n}" by blast
    have "hlRefsF ?Q n = {n}" using l lr by simp
    then show
      "hlRefsF ?Q (hlEnvironmentLine ?env (fst nf)) =
       {hlEnvironmentLine ?env (fst nf)}" using line by simp
  next
    fix nf assume nf: "nf \<in> set (hlOpenAssumptions d)"
    from envline[OF nf] obtain n where line: "hlEnvironmentLine ?env (fst nf) = n"
      and mem: "(n,snd nf,HL_FPremise) \<in> set (hlFlattenFitch ?pre)" by blast
    from premise[OF mem] obtain l where
      l: "hlLookupLine ?Q n = Some l" and lf: "hlFormula l = snd nf" by blast
    have "hlLookF ?Q n = Some (snd nf)" using l lf by simp
    then show
      "hlLookF ?Q (hlEnvironmentLine ?env (fst nf)) = Some (snd nf)" using line by simp
  qed

  have ictxF: "hlItemsCtx ?Q ?F"
    by (rule hlFitchToLemmon_itemsCtx[OF nest sorted subset_refl])
  have ictxB: "hlItemsCtx ?Q body"
    by (rule hlFitchToLemmon_itemsCtx[OF nest sorted]) (use flatF in blast)

  have bodyOK: "\<forall>t \<in> set (hlFlattenFitch body).
                  \<forall>l. hlLookupLine ?Q (fst t) = Some l \<longrightarrow> hlRuleOK ?Q l"
  proof (rule hlEmitDerivationFuel_ruleOK)
    show "size d < length (replicate (Suc (size d)) ())" by simp
  next
    show "hlEmitDerivationFuel (replicate (Suc (size d)) ()) ?base ?env
            (map (\<lambda>(source,n,phi). phi) ?env) ?first 0 d = (body,k,after,cnt)"
      using em by (simp add: hlEmitDerivation_def)
  next
    show "hlDerivationOK d" by (rule ok)
  next
    show "distinct (map hlLineNumber ?Q)" by (rule distQ)
  next
    show "hlEmitCtx ?Q ?env ?first d" by (rule ctx)
  next
    show "hlItemsCtx ?Q body" by (rule ictxB)
  next
    show "0 < ?base" by simp
  next
    show "hlNamesBelow ?base 0 d" by (rule hlNamesBelow_root)
  qed

  have ruleOK: "\<forall>l \<in> set ?Q. hlRuleOK ?Q l"
  proof
    fix l assume l: "l \<in> set ?Q"
    have look: "hlLookupLine ?Q (hlLineNumber l) = Some l"
      by (rule hlLookupLine_self[OF distQ l])
    have "hlLineNumber l \<in> set (map fst (hlFlattenFitch ?F))" using l nums by (metis image_eqI list.set_map)
    then obtain t where t: "t \<in> set (hlFlattenFitch ?F)" and tn: "fst t = hlLineNumber l"
      by auto
    from t flatF have "t \<in> set (hlFlattenFitch ?pre) \<or> t \<in> set (hlFlattenFitch body)"
      by blast
    then show "hlRuleOK ?Q l"
    proof
      assume tp: "t \<in> set (hlFlattenFitch ?pre)"
      obtain n p where t': "t = (n,p,HL_FPremise)"
        using tp by (force simp: hlPremiseFitchLines_flatten)
      from premise[OF tp[unfolded t']] obtain l' where
        l': "hlLookupLine ?Q n = Some l'"
        and l'j: "hlJustification l' = HL_Assumption"
        and l'r: "hlReferences l' = {n}" by blast
      have num: "hlLineNumber l = n" using tn t' by simp
      have same: "l' = l" using l' look num by simp
      show ?thesis
      proof (rule hlRuleOK_Assumption)
        show "hlJustification l = HL_Assumption" using l'j same by simp
      next
        show "hlReferences l = {hlLineNumber l}" using l'r same num by simp
      qed
    next
      assume "t \<in> set (hlFlattenFitch body)"
      then show ?thesis using bodyOK look tn by auto
    qed
  qed

  have structOK: "\<forall>l \<in> set ?Q. hlStructureOK ?Q l"
    by (rule hlFitchToLemmon_structureOK[OF nest sorted])
  have correct: "hlCorrect ?Q"
    unfolding hlCorrect_def list_all_iff hlLineOK_def using ruleOK structOK by blast

  text \<open>The conclusion depends only on premise lines, so every open premise of
    the erasure is one of the Fitch proof's own premises.\<close>

  have prem: "hlFitchPremises ?F = map (\<lambda>(s,n,p). p) ?env"
    using F hlPremiseFitchLines_premises[of ?env]
          hlNoPremiseLines_root_premises[OF hlEmitDerivation_no_premises[OF em]]
    by simp
  have envnum: "n \<in> (\<lambda>q. fst (snd q)) ` set ?env \<Longrightarrow>
                \<exists>p. (n,p,HL_FPremise) \<in> set (hlFlattenFitch ?pre) \<and>
                    p \<in> set (hlFitchPremises ?F)" for n
    by (force simp: hlPremiseFitchLines_flatten prem)
  have pclosed: "hlFitchPremiseClosed ?F"
  proof (cases "?Q = []")
    case True
    then show ?thesis by (simp add: hlFitchPremiseClosed_def hlOpenPremises_def)
  next
    case nonempty: False
    have lastin: "last ?Q \<in> set ?Q" using nonempty by simp
    have refs: "hlReferences (last ?Q) \<subseteq> (\<lambda>q. fst (snd q)) ` set ?env"
    proof (cases "body = []")
      case True
      have "hlLineNumber (last ?Q) \<in> set (map fst (hlFlattenFitch ?F))"
        using lastin nums by (metis image_eqI list.set_map)
      then have "hlLineNumber (last ?Q) \<in> (\<lambda>q. fst (snd q)) ` set ?env"
        using F True by (force simp: hlPremiseFitchLines_flatten)
      then obtain p where mem: "(hlLineNumber (last ?Q),p,HL_FPremise)
              \<in> set (hlFlattenFitch ?pre)" using envnum by blast
      have look: "hlLookupLine ?Q (hlLineNumber (last ?Q)) = Some (last ?Q)"
        by (rule hlLookupLine_self[OF distQ lastin])
      from premise[OF mem] look
      have "hlReferences (last ?Q) = {hlLineNumber (last ?Q)}" by auto
      then show ?thesis
        using \<open>hlLineNumber (last ?Q) \<in> (\<lambda>q. fst (snd q)) ` set ?env\<close> by auto
    next
      case False
      from hlEmitDerivation_last[OF em False] obtain r where
        lastb: "last body = HL_FLine k (hlDerivationFormula d) r" by blast
      have bodyflat: "hlFlattenFitch body =
          hlFlattenFitch (butlast body) @ [(k,hlDerivationFormula d,r)]"
      proof -
        have split: "body = butlast body @ [last body]" using False by simp
        have "hlFlattenFitch body =
              hlFlattenFitch (butlast body) @ hlFlattenFitch [last body]"
          by (subst split) (rule hlFlattenFitch_append)
        then show ?thesis using lastb by simp
      qed
      have flatne: "hlFlattenFitch ?F \<noteq> []"
        using F bodyflat by (simp add: hlFlattenFitch_append)
      have lastflat: "last (hlFlattenFitch ?F) = (k,hlDerivationFormula d,r)"
        using F bodyflat by (simp add: hlFlattenFitch_append)
      have num: "hlLineNumber (last ?Q) = k"
      proof -
        have "hlLineNumber (last ?Q) = last (map hlLineNumber ?Q)"
          using nonempty by (simp add: last_map)
        also have "\<dots> = last (map fst (hlFlattenFitch ?F))" using nums by simp
        also have "\<dots> = fst (last (hlFlattenFitch ?F))"
          using flatne by (simp add: last_map)
        finally show ?thesis using lastflat by simp
      qed
      have look: "hlLookupLine ?Q k = Some (last ?Q)"
        using hlLookupLine_self[OF distQ lastin] num by simp
      have "hlRefsF ?Q k = hlEnvImage ?env d"
      proof (rule hlEmitDerivationFuel_deps)
        show "size d < length (replicate (Suc (size d)) ())" by simp
      next
        show "hlEmitDerivationFuel (replicate (Suc (size d)) ()) ?base ?env
                (map (\<lambda>(source,n,phi). phi) ?env) ?first 0 d = (body,k,after,cnt)"
          using em by (simp add: hlEmitDerivation_def)
      next
        show "hlDepsCtx ?Q ?env ?first d" using ctx by (simp add: hlEmitCtx_def)
      next
        show "hlItemsDeps ?Q body" using ictxB by simp
      qed
      then have "hlReferences (last ?Q) = hlEnvImage ?env d" using look by simp
      moreover have "hlEnvImage ?env d \<subseteq> (\<lambda>q. fst (snd q)) ` set ?env"
      proof
        fix x assume "x \<in> hlEnvImage ?env d"
        then obtain nf where nf: "nf \<in> set (hlOpenAssumptions d)"
          and x: "x = hlEnvironmentLine ?env (fst nf)" by (auto simp: hlEnvImage_def)
        from hlPremiseEnvironment_line[OF fn root nf] obtain m where
          m: "(fst nf,m,snd nf) \<in> set ?env" "hlEnvironmentLine ?env (fst nf) = m" by blast
        then show "x \<in> (\<lambda>q. fst (snd q)) ` set ?env" using x by force
      qed
      ultimately show ?thesis by simp
    qed
    have "hlFormula l \<in> set (hlFitchPremises ?F)"
      if l: "l \<in> set ?Q" and lr: "hlLineNumber l \<in> hlReferences (last ?Q)" for l
    proof -
      from lr refs have "hlLineNumber l \<in> (\<lambda>q. fst (snd q)) ` set ?env" by blast
      then obtain p where mem: "(hlLineNumber l,p,HL_FPremise) \<in> set (hlFlattenFitch ?pre)"
        and pp: "p \<in> set (hlFitchPremises ?F)" using envnum by blast
      have look: "hlLookupLine ?Q (hlLineNumber l) = Some l"
        by (rule hlLookupLine_self[OF distQ l])
      from premise[OF mem] look have "hlFormula l = p" by auto
      then show ?thesis using pp by simp
    qed
    then show ?thesis
      unfolding hlFitchPremiseClosed_def hlOpenPremises_def using nonempty by auto
  qed
  show ?thesis using correct pclosed by simp
qed

section \<open>Everything \<^const>\<open>hlFitchVerified\<close> asks of the emitted proof\<close>

lemma hlAssumptionsFunctional_classify [simp]:
  "hlAssumptionsFunctional (hlClassifyAssumptions bound d) = hlAssumptionsFunctional d"
  by (simp add: hlAssumptionsFunctional_def)

theorem hlClassifiedDerivationToFitch_verified:
  assumes fn: "hlAssumptionsFunctional d"
      and ok: "hlDerivationOK d"
  shows "hlFitchVerified (hlDerivationToFitch (hlClassifyAssumptions {} d))"
proof -
  let ?d = "hlClassifyAssumptions {} d"
  have fn': "hlAssumptionsFunctional ?d" using fn by simp
  have ok': "hlDerivationOK ?d" using ok by simp
  have root: "set (hlPremisesOf ?d) = set (hlOpenAssumptions ?d)"
    by (rule hlClassified_premises_open)
  from hlDerivationToFitch_correct[OF fn' root ok']
  have correct: "hlCorrect (\<delta>\<^sub>H (hlDerivationToFitch ?d))"
    and pclosed: "hlFitchPremiseClosed (hlDerivationToFitch ?d)" by simp_all
  have "hlVerifiedCorrect (\<delta>\<^sub>H (hlDerivationToFitch ?d))"
    unfolding hlVerifiedCorrect_def
    using correct hlFitchToLemmon_dependencyClosed
      hlClassifiedDerivationToFitch_canonicalOrder[of d] by simp
  then show ?thesis
    unfolding hlFitchVerified_def
    using hlClassifiedDerivationToFitch_wellFormed[of d]
      hlDerivationToFitch_concludesAtTop[of ?d]
      hlClassifiedDerivationToFitch_nestedWellFormed[of d] pclosed
    by simp
qed

section \<open>The scope record of an emitted proof\<close>

text \<open>\<^const>\<open>hlFitchScopeOf\<close> names the root premises and the heads of the
  enclosing boxes.  Those are exactly the lines whose formulas the emitter
  carries in its \<open>scope\<close> argument, which is what \<^const>\<open>hlForallRepairConstants\<close>
  and \<^const>\<open>hlExistsRepairConstants\<close> consult.  The bridge between the two is
  this record.\<close>

lemma hlFitchScopeRecord_append:
  "hlFitchScopeRecord S (F @ G) =
   hlFitchScopeRecord S F @ hlFitchScopeRecord S G"
  by (induction S F rule: hlFitchScopeRecord.induct) auto

lemma hlFitchScopeRecord_numbers:
  "map fst (hlFitchScopeRecord S F) = hlFitchLineNumbers F"
  by (induction S F rule: hlFitchScopeRecord.induct) auto

text \<open>On a proof with distinct line numbers the record is a function, so its
  \<^const>\<open>map_of\<close> can be read off any decomposition.\<close>

lemma hlFitchScopeOf_record:
  assumes dist: "distinct (hlFitchLineNumbers F)"
      and mem: "(m,T) \<in> set (hlFitchScopeRecord (set (hlFitchPremiseNumbers F)) F)"
  shows "hlFitchScopeOf F m = T"
proof -
  have "distinct (map fst (hlFitchScopeRecord (set (hlFitchPremiseNumbers F)) F))"
    using dist by (simp add: hlFitchScopeRecord_numbers)
  from map_of_is_SomeI[OF this mem] show ?thesis
    by (simp add: hlFitchScopeOf_def)
qed

end
