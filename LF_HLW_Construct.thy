(* T3: the emitted Fitch proof is correct, and the construction theorem. *)

theory LF_HLW_Construct
  imports LF_HLW_Erasure LF_HLW_Rule_Transfer LF_HLW_Faithful
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


lemma hlFitchPremiseNumbers_append:
  "hlFitchPremiseNumbers (F @ G) =
   hlFitchPremiseNumbers F @ hlFitchPremiseNumbers G"
  by (induction F rule: hlFitchPremiseNumbers.induct) auto

lemma hlFitchPremiseNumbers_premiseFitchLines:
  "hlFitchPremiseNumbers (hlPremiseFitchLines env) = map (\<lambda>(s,n,p). n) env"
  by (induction env) (auto simp: hlPremiseFitchLines_def split: prod.splits)

lemma hlNoPremiseLines_numbers:
  "hlNoPremiseLines F \<Longrightarrow> hlFitchPremiseNumbers F = []"
  by (induction F rule: hlFitchPremiseNumbers.induct)
     (auto simp: hlNoPremiseLines_def hlFlattenFitch_append)

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

section \<open>Eigenconstants against a scope rather than a dependency set\<close>

text \<open>\<^const>\<open>hlFitchScopeOf\<close> is generally larger than a line's dependencies ---
  it holds every root premise and every enclosing box head --- so the scope
  check is strictly stronger than \<^const>\<open>hlRuleOK\<close> and does not follow from it
  by antitonicity.  What makes it available is that the inferred witnesses are
  drawn from the constants of the premise itself: \<^const>\<open>hlWitnessLists\<close> takes
  its candidates from \<open>hlConstantsInFormula q\<close>.  So a witness always lies in
  the premise's constants and, having been abstracted away, never in the
  conclusion's --- which is exactly the set the emitter's repair empties of
  scope constants.\<close>

lemma hlAbstractMany_removes:
  "hlAbstractMany ps p = Some q \<Longrightarrow>
   hlConstantsInFormula q = hlConstantsInFormula p - snd ` set ps"
proof (induction ps arbitrary: p)
  case Nil
  then show ?case by simp
next
  case (Cons xa ps)
  obtain x a where xa: "xa = (x,a)" by (cases xa) auto
  from Cons.prems xa obtain r where r: "hlAbstractConstantFree a x p = Some r"
    and rest: "hlAbstractMany ps r = Some q"
    by (auto split: option.splits)
  have "hlConstantsInFormula r = hlConstantsInFormula p - {a}"
    by (rule hlAbstractConstantFree_constants[OF r])
  then show ?case using Cons.IH[OF rest] xa by auto
qed

lemma hlInferWitnessConstsK_constants:
  "hlInferWitnessConstsK xs p k q = Some cs \<Longrightarrow>
   set cs \<subseteq> insert (STR '''') (hlConstantsInFormula q)"
  by (rule hlWitnessLists_constants[OF hlInferWitnessConstsK_witness])

lemma hlForallIntroStep_scope:
  assumes step: "hlForallIntroStep src goal G"
      and disj: "(hlConstantsInFormula src - hlConstantsInFormula goal) \<inter>
                 hlConstantsInScope H = {}"
  shows "hlForallIntroStep src goal H"
proof -
  obtain xs core where xc: "hlCollectForalls goal = (xs,core)"
    by (cases "hlCollectForalls goal") auto
  from step xc obtain cs where
    ne: "xs \<noteq> []"
    and inf: "hlInferWitnessConstsK xs core (length xs) src = Some cs"
    and abst: "hlAbstractMany (filter (\<lambda>xc. snd xc \<noteq> STR '''') (zip xs cs)) src
                 = Some core"
    by (auto simp: hlForallIntroStep_def Let_def split: option.splits)
  have core: "hlConstantsInFormula core = hlConstantsInFormula goal"
    using hlCollectForalls_constants[of goal] xc by simp
  have fresh: "w \<notin> hlConstantsInScope H"
    if w: "w \<in> snd ` set (filter (\<lambda>xc. snd xc \<noteq> STR '''') (zip xs cs))" for w
  proof -
    have "w \<in> set cs" using w by (auto dest: set_zip_rightD)
    moreover have "w \<noteq> STR ''''" using w by auto
    ultimately have inc: "w \<in> hlConstantsInFormula src"
      using hlInferWitnessConstsK_constants[OF inf] by blast
    have "w \<notin> hlConstantsInFormula core"
      using hlAbstractMany_removes[OF abst] w by blast
    then show ?thesis using inc core disj by blast
  qed
  show ?thesis
    unfolding hlForallIntroStep_def
    using xc ne inf abst fresh by (simp add: Let_def)
qed

lemma hlExistsElimStep_scope:
  assumes step: "hlExistsElimStep src asm goal G"
      and disj: "(hlConstantsInFormula asm -
                  (hlConstantsInFormula src \<union> hlConstantsInFormula goal)) \<inter>
                 hlConstantsInScope H = {}"
  shows "hlExistsElimStep src asm goal H"
proof -
  obtain xs p where xp: "hlCollectExists src = (xs,p)"
    by (cases "hlCollectExists src") auto
  obtain ys q where yq: "hlCollectExists asm = (ys,q)"
    by (cases "hlCollectExists asm") auto
  from step xp yq obtain k cs where
    ne: "xs \<noteq> []"
    and ec: "hlEliminationCount xs ys = Some k"
    and inf: "hlInferWitnessConstsK xs (hlPrefixExists ys p) k asm = Some cs"
    and abst: "hlAbstractMany (filter (\<lambda>xc. snd xc \<noteq> STR '''') (zip (take k xs) cs)) asm
                 = Some (hlPrefixExists ys p)"
    and goalfresh: "\<forall>w \<in> snd ` set (filter (\<lambda>xc. snd xc \<noteq> STR '''')
                                      (zip (take k xs) cs)).
                      w \<notin> hlConstantsInFormula goal"
    by (auto simp: hlExistsElimStep_def Let_def split: option.splits)
  have core: "hlConstantsInFormula (hlPrefixExists ys p) = hlConstantsInFormula src"
    using hlCollectExists_constants[of src] xp by simp
  have fresh: "w \<notin> hlConstantsInScope H"
    if w: "w \<in> snd ` set (filter (\<lambda>xc. snd xc \<noteq> STR '''') (zip (take k xs) cs))" for w
  proof -
    have "w \<in> set cs" using w by (auto dest: set_zip_rightD)
    moreover have "w \<noteq> STR ''''" using w by auto
    ultimately have inc: "w \<in> hlConstantsInFormula asm"
      using hlInferWitnessConstsK_constants[OF inf] by blast
    have "w \<notin> hlConstantsInFormula (hlPrefixExists ys p)"
      using hlAbstractMany_removes[OF abst] w by blast
    then have "w \<notin> hlConstantsInFormula src" using core by simp
    moreover have "w \<notin> hlConstantsInFormula goal" using goalfresh w by blast
    ultimately show ?thesis using inc disj by blast
  qed
  show ?thesis
    unfolding hlExistsElimStep_def
    using xp yq ne ec inf abst fresh goalfresh by (simp add: Let_def)
qed

text \<open>The two interfaces to \<^const>\<open>hlRuleOKG\<close>.  They differ from their
  \<^const>\<open>hlRuleOK\<close> counterparts only in where the forbidden constants come
  from.\<close>

lemma hlRuleOKG_ForallIntro:
  assumes j: "hlJustification l = HL_ForallIntro m"
      and lu: "hlLookupLine P m = Some lm"
      and step: "hlForallIntroStep (hlFormula lm) (hlFormula l) G"
      and sub: "hlAssumptionConstants P (src P (hlLineNumber l) (hlReferences lm))
                  \<subseteq> hlConstantsInScope G"
      and refs: "hlReferences l = hlReferences lm"
  shows "hlRuleOKG src P l"
proof -
  obtain xs core where xc: "hlCollectForalls (hlFormula l) = (xs,core)"
    by (cases "hlCollectForalls (hlFormula l)") auto
  from step xc obtain cs where
    ne: "xs \<noteq> []"
    and inf: "hlInferWitnessConstsK xs core (length xs) (hlFormula lm) = Some cs"
    and abst: "hlAbstractMany (filter (\<lambda>xc. snd xc \<noteq> STR '''') (zip xs cs))
                 (hlFormula lm) = Some core"
    and fresh: "\<forall>c \<in> snd ` set (filter (\<lambda>xc. snd xc \<noteq> STR '''') (zip xs cs)).
                  c \<notin> hlConstantsInScope G"
    by (auto simp: hlForallIntroStep_def Let_def split: option.splits)
  have fresh': "\<forall>c \<in> snd ` set (filter (\<lambda>xc. snd xc \<noteq> STR '''') (zip xs cs)).
                  c \<notin> hlAssumptionConstants P (src P (hlLineNumber l) (hlReferences lm))"
    using fresh sub by blast
  show ?thesis
    unfolding hlRuleOKG_def
    using j lu xc ne inf abst fresh' refs by (simp add: Let_def)
qed

lemma hlRuleOKG_ExistsElim:
  assumes j: "hlJustification l = HL_ExistsElim m x c"
      and lm: "hlLookupLine P m = Some lm"
      and lx: "hlLookupLine P x = Some la"
      and lc: "hlLookupLine P c = Some lc"
      and asm: "hlJustification la = HL_Assumption"
      and step: "hlExistsElimStep (hlFormula lm) (hlFormula la) (hlFormula lc) G"
      and sub: "hlReferencedConstants P
                  (src P (hlLineNumber lc) (hlReferences lc) - {hlLineNumber la})
                  \<subseteq> hlConstantsInScope G"
      and fm: "hlFormula l = hlFormula lc"
      and refs: "hlReferences l =
                   hlReferences lm \<union> (hlReferences lc - {hlLineNumber la})"
  shows "hlRuleOKG src P l"
proof -
  obtain xs p where xp: "hlCollectExists (hlFormula lm) = (xs,p)"
    by (cases "hlCollectExists (hlFormula lm)") auto
  obtain ys q where yq: "hlCollectExists (hlFormula la) = (ys,q)"
    by (cases "hlCollectExists (hlFormula la)") auto
  from step xp yq obtain k cs where
    ne: "xs \<noteq> []"
    and ec: "hlEliminationCount xs ys = Some k"
    and inf: "hlInferWitnessConstsK xs (hlPrefixExists ys p) k (hlFormula la) = Some cs"
    and abst: "hlAbstractMany (filter (\<lambda>xc. snd xc \<noteq> STR '''') (zip (take k xs) cs))
                 (hlFormula la) = Some (hlPrefixExists ys p)"
    and fresh: "\<forall>w \<in> snd ` set (filter (\<lambda>xc. snd xc \<noteq> STR '''') (zip (take k xs) cs)).
                  w \<notin> hlConstantsInFormula (hlFormula lc) \<and> w \<notin> hlConstantsInScope G"
    by (auto simp: hlExistsElimStep_def Let_def split: option.splits)
  have fresh': "\<forall>w \<in> snd ` set (filter (\<lambda>xc. snd xc \<noteq> STR '''') (zip (take k xs) cs)).
                  w \<notin> hlConstantsInFormula (hlFormula lc) \<and>
                  w \<notin> hlReferencedConstants P
                         (src P (hlLineNumber lc) (hlReferences lc) - {hlLineNumber la})"
    using fresh sub by blast
  show ?thesis
    unfolding hlRuleOKG_def
    using j lm lx lc asm xp yq ne ec inf abst fresh' fm refs by (simp add: Let_def)
qed

text \<open>Every other rule is already settled: only the two eigenconstant rules
  read the \<open>src\<close> argument at all.\<close>

lemma hlRuleOKG_of_hlRuleOK:
  assumes ok: "hlRuleOK P l"
      and nf: "\<And>m. hlJustification l \<noteq> HL_ForallIntro m"
      and ne: "\<And>m a c. hlJustification l \<noteq> HL_ExistsElim m a c"
  shows "hlRuleOKG src P l"
  using hlRuleOKG_non_eigen_independent[OF nf ne, where src = src and dst = hlDepSrc] ok
  by (simp add: hlRuleOKG_hlDepSrc)

lemma hlToLemmonRule_ForallIntro:
  "hlToLemmonRule r = HL_ForallIntro m \<Longrightarrow> r = HL_FForallI m"
  by (cases r) auto

lemma hlToLemmonRule_ExistsElim:
  "hlToLemmonRule r = HL_ExistsElim m a c \<Longrightarrow> r = HL_FExistsE m (a,c)"
  by (cases r) auto

section \<open>The repair empties the conclusion's new constants of scope constants\<close>

definition hlScopeBelow :: "nat \<Rightarrow> nat \<Rightarrow> hl_formula list \<Rightarrow> bool" where
  "hlScopeBelow base cnt scope \<longleftrightarrow>
     (\<forall>c \<in> hlConstantsInScope scope. nlen c < base + cnt)"

lemma hlScopeBelow_mono:
  "hlScopeBelow base cnt scope \<Longrightarrow> cnt \<le> cnt' \<Longrightarrow> hlScopeBelow base cnt' scope"
  by (fastforce simp: hlScopeBelow_def)

lemma hlScopeBelow_Cons:
  "hlScopeBelow base cnt scope \<Longrightarrow>
   (\<forall>c \<in> hlConstantsInFormula p. nlen c < base + cnt) \<Longrightarrow>
   hlScopeBelow base cnt (p # scope)"
  by (auto simp: hlScopeBelow_def hlConstantsInScope_def)

lemma hlRenamePairsFormula_constants_sub:
  "hlConstantsInFormula (hlRenamePairsFormula pairs f) \<subseteq>
   hlConstantsInFormula f \<union> snd ` set pairs"
proof (induction pairs arbitrary: f)
  case Nil
  then show ?case by simp
next
  case (Cons op pairs)
  obtain old new where op: "op = (old,new)" by (cases op) auto
  have "hlConstantsInFormula (hlRenameFormula old new f) \<subseteq>
        hlConstantsInFormula f \<union> {new}"
    by (auto simp: hlRenameFormula_constants hlRenameName_def)
  then show ?case using Cons.IH[of "hlRenameFormula old new f"] op by auto
qed

lemma hlRenamePairsFormula_removes:
  assumes "\<forall>op \<in> set pairs. \<forall>oq \<in> set pairs. snd op \<noteq> fst oq"
  shows "fst ` set pairs \<inter>
         hlConstantsInFormula (hlRenamePairsFormula pairs f) = {}"
  using assms
proof (induction pairs arbitrary: f)
  case Nil
  then show ?case by simp
next
  case (Cons op pairs)
  obtain old new where op: "op = (old,new)" by (cases op) auto
  have ne: "new \<noteq> old" using Cons.prems op by fastforce
  have gone: "old \<notin> hlConstantsInFormula (hlRenameFormula old new f)"
    using ne by (auto simp: hlRenameFormula_constants hlRenameName_def)
  have notlater: "old \<notin> snd ` set pairs" using Cons.prems op by fastforce
  have "old \<notin> hlConstantsInFormula
          (hlRenamePairsFormula pairs (hlRenameFormula old new f))"
    using gone notlater hlRenamePairsFormula_constants_sub by blast
  moreover have "fst ` set pairs \<inter>
      hlConstantsInFormula (hlRenamePairsFormula pairs (hlRenameFormula old new f)) = {}"
    by (rule Cons.IH) (use Cons.prems in simp)
  ultimately show ?case using op by auto
qed

lemma hlRepairDerivation_pairs_fresh:
  "hlRepairDerivation base count bad e = (count',pairs,e') \<Longrightarrow>
   \<forall>op \<in> set pairs. \<exists>k. count \<le> k \<and> snd op = hlFreshIndex base k"
proof (induction bad arbitrary: count e count' pairs e')
  case Nil
  then show ?case by simp
next
  case (Cons old olds)
  from Cons.prems obtain c2 ps r where
    rec: "hlRepairDerivation base (Suc count) olds
            (hlRenameDerivation old (hlFreshIndex base count) e) = (c2,ps,r)"
    and eq: "pairs = (old,hlFreshIndex base count) # ps"
    by (auto simp: Let_def split: prod.splits)
  show ?case
  proof
    fix op assume "op \<in> set pairs"
    then consider "op = (old,hlFreshIndex base count)" | "op \<in> set ps" using eq by auto
    then show "\<exists>k. count \<le> k \<and> snd op = hlFreshIndex base k"
    proof cases
      case 1
      then show ?thesis by auto
    next
      case 2
      then obtain k where k: "Suc count \<le> k" "snd op = hlFreshIndex base k"
        using Cons.IH[OF rec] by blast
      have "count \<le> k" using k(1) by simp
      then show ?thesis using k(2) by blast
    qed
  qed
qed

lemma hlRepairDerivation_pairs_nlen:
  "hlRepairDerivation base count bad e = (count',pairs,e') \<Longrightarrow>
   \<forall>op \<in> set pairs. base + count \<le> nlen (snd op)"
  using hlRepairDerivation_pairs_fresh by fastforce

text \<open>A repaired formula's constants split into originals the repair did not
  touch and freshly minted names, and both are outside the scope: the first by
  construction of the bad set, the second because it is longer than anything
  the scope holds.\<close>

lemma hlRepair_disjoint:
  assumes rp: "hlRepairDerivation base count bad e = (count',pairs,e')"
      and sb: "hlScopeBelow base count scope"
      and origin: "\<And>c. c \<in> hlConstantsInFormula g \<Longrightarrow> c \<notin> K \<Longrightarrow>
                        c \<in> hlConstantsInScope scope \<Longrightarrow> c \<in> set bad"
      and small: "\<forall>c \<in> set bad. nlen c < base + count"
  shows "(hlConstantsInFormula (hlRenamePairsFormula pairs g) - K) \<inter>
         hlConstantsInScope scope = {}"
proof -
  have fpairs: "fst ` set pairs = set bad"
    using hlRepairDerivation_pairs_fst[OF rp] by (metis list.set_map)
  have fresh: "\<forall>op \<in> set pairs. base + count \<le> nlen (snd op)"
    by (rule hlRepairDerivation_pairs_nlen[OF rp])
  have noclash: "\<forall>op \<in> set pairs. \<forall>oq \<in> set pairs. snd op \<noteq> fst oq"
  proof (intro ballI)
    fix op oq assume o: "op \<in> set pairs" and q: "oq \<in> set pairs"
    have "fst oq \<in> set bad" using q fpairs by blast
    then have "nlen (fst oq) < base + count" using small by blast
    moreover have "base + count \<le> nlen (snd op)" using fresh o by blast
    ultimately show "snd op \<noteq> fst oq" by auto
  qed
  have "c \<notin> hlConstantsInScope scope"
    if c: "c \<in> hlConstantsInFormula (hlRenamePairsFormula pairs g)"
      and nc: "c \<notin> K" for c
  proof
    assume sc: "c \<in> hlConstantsInScope scope"
    then have low: "nlen c < base + count" using sb by (simp add: hlScopeBelow_def)
    have "c \<notin> snd ` set pairs" using fresh low by fastforce
    then have "c \<in> hlConstantsInFormula g"
      using c hlRenamePairsFormula_constants_sub by blast
    then have "c \<in> set bad" using origin nc sc by blast
    then have "c \<in> fst ` set pairs" using fpairs by blast
    with hlRenamePairsFormula_removes[OF noclash, of g] c show False by blast
  qed
  then show ?thesis by blast
qed

text \<open>Hence the two rule steps hold against the emitter's own scope, which is
  what the scope-based check reads.\<close>

lemma hlForallRepair_scope:
  assumes rp: "hlRepairDerivation base count (hlForallRepairConstants scope phi e)
                 e = (c0,prs,rep)"
      and sb: "hlScopeBelow base count scope"
      and nbe: "hlNamesBelow base count e"
      and step: "hlForallIntroStep (hlDerivationFormula rep) phi G"
  shows "hlForallIntroStep (hlDerivationFormula rep) phi scope"
proof (rule hlForallIntroStep_scope[OF step])
  have form: "hlDerivationFormula rep = hlRenamePairsFormula prs (hlDerivationFormula e)"
    by (rule hlDerivationFormula_repair[OF rp])
  show "(hlConstantsInFormula (hlDerivationFormula rep) -
         hlConstantsInFormula phi) \<inter> hlConstantsInScope scope = {}"
    unfolding form
  proof (rule hlRepair_disjoint[OF rp sb])
    fix c assume "c \<in> hlConstantsInFormula (hlDerivationFormula e)"
      and "c \<notin> hlConstantsInFormula phi" and "c \<in> hlConstantsInScope scope"
    then show "c \<in> set (hlForallRepairConstants scope phi e)"
      by (simp add: set_hlForallRepairConstants)
  next
    show "\<forall>c \<in> set (hlForallRepairConstants scope phi e). nlen c < base + count"
      using nbe hlDerivationFormula_in_formulas[of e]
      by (auto simp: set_hlForallRepairConstants hlNamesBelow_def
          hlDerivationConstants_def)
  qed
qed

lemma hlExistsRepair_scope:
  assumes rp: "hlRepairDerivation base count (hlExistsRepairConstants scope af src phi)
                 body = (cR,prs,rbody)"
      and sb: "hlScopeBelow base count scope"
      and nbaf: "\<forall>c \<in> hlConstantsInFormula af. nlen c < base + count"
      and step: "hlExistsElimStep (hlDerivationFormula src)
                   (hlRenamePairsFormula prs af) phi G"
  shows "hlExistsElimStep (hlDerivationFormula src)
           (hlRenamePairsFormula prs af) phi scope"
proof (rule hlExistsElimStep_scope[OF step])
  show "(hlConstantsInFormula (hlRenamePairsFormula prs af) -
         (hlConstantsInFormula (hlDerivationFormula src) \<union>
          hlConstantsInFormula phi)) \<inter> hlConstantsInScope scope = {}"
  proof (rule hlRepair_disjoint[OF rp sb])
    fix c assume "c \<in> hlConstantsInFormula af"
      and "c \<notin> hlConstantsInFormula (hlDerivationFormula src) \<union>
                hlConstantsInFormula phi"
      and "c \<in> hlConstantsInScope scope"
    then show "c \<in> set (hlExistsRepairConstants scope af src phi)"
      by (simp add: set_hlExistsRepairConstants)
  next
    show "\<forall>c \<in> set (hlExistsRepairConstants scope af src phi). nlen c < base + count"
      using nbaf by (auto simp: set_hlExistsRepairConstants)
  qed
qed

text \<open>Entering a box adds its head to the scope; the head's formula is the one
  the emitter pushes onto its \<open>scope\<close> list, so the invariant survives.\<close>

lemma hlAssumptionConstants_insert:
  assumes dist: "distinct (map hlLineNumber Q)"
      and look: "hlLookupLine Q m = Some l"
  shows "hlAssumptionConstants Q (insert m S) \<subseteq>
         hlAssumptionConstants Q S \<union> hlConstantsInFormula (hlFormula l)"
proof
  fix c assume "c \<in> hlAssumptionConstants Q (insert m S)"
  then obtain k where k: "k \<in> set Q" "hlLineNumber k \<in> insert m S"
      "hlJustification k = HL_Assumption"
    and cc: "c \<in> hlConstantsInFormula (hlFormula k)"
    by (auto simp: hlAssumptionConstants_def)
  show "c \<in> hlAssumptionConstants Q S \<union> hlConstantsInFormula (hlFormula l)"
  proof (cases "hlLineNumber k = m")
    case True
    have "hlLookupLine Q (hlLineNumber k) = Some k" by (rule hlLookupLine_self[OF dist k(1)])
    then have "k = l" using True look by simp
    then show ?thesis using cc by simp
  next
    case False
    then have "hlLineNumber k \<in> S" using k(2) by simp
    then show ?thesis using k cc by (auto simp: hlAssumptionConstants_def)
  qed
qed

lemma hlReferencedConstants_insert:
  assumes dist: "distinct (map hlLineNumber Q)"
      and look: "hlLookupLine Q m = Some l"
  shows "hlReferencedConstants Q (insert m S) \<subseteq>
         hlReferencedConstants Q S \<union> hlConstantsInFormula (hlFormula l)"
proof
  fix c assume "c \<in> hlReferencedConstants Q (insert m S)"
  then obtain k where k: "k \<in> set Q" "hlLineNumber k \<in> insert m S"
    and cc: "c \<in> hlConstantsInFormula (hlFormula k)"
    by (auto simp: hlReferencedConstants_def)
  show "c \<in> hlReferencedConstants Q S \<union> hlConstantsInFormula (hlFormula l)"
  proof (cases "hlLineNumber k = m")
    case True
    have "hlLookupLine Q (hlLineNumber k) = Some k" by (rule hlLookupLine_self[OF dist k(1)])
    then have "k = l" using True look by simp
    then show ?thesis using cc by simp
  next
    case False
    then have "hlLineNumber k \<in> S" using k(2) by simp
    then show ?thesis using k cc by (auto simp: hlReferencedConstants_def)
  qed
qed

text \<open>The list traversal behind \<open>HL_DPropTaut\<close>, for the scope check.\<close>

lemma hlScopeOK_emit_list:
  assumes emitted: "hlEmitDerivationsUsing emit first count ds = (items,ns,after,cnt)"
      and wictx: "hlItemsCtx Q items"
      and wrules: "\<forall>t \<in> set (hlFlattenFitch items).
                     \<forall>l. hlLookupLine Q (fst t) = Some l \<longrightarrow> hlRuleOK Q l"
      and wrec: "\<forall>q \<in> set (hlFitchScopeRecord S items). hlFitchScopeOf F (fst q) = snd q"
      and mono: "\<And>e fi ct out k af c2. emit fi ct e = (out,k,af,c2) \<Longrightarrow> fi \<le> af"
      and cmono: "\<And>e fi ct out k af c2. emit fi ct e = (out,k,af,c2) \<Longrightarrow> ct \<le> c2"
      and start: "f0 \<le> first" and cstart: "c0 \<le> count"
      and each: "\<And>e fi ct out k af c2. e \<in> set ds \<Longrightarrow>
        emit fi ct e = (out,k,af,c2) \<Longrightarrow>
        hlItemsCtx Q out \<Longrightarrow>
        (\<forall>t \<in> set (hlFlattenFitch out).
           \<forall>l. hlLookupLine Q (fst t) = Some l \<longrightarrow> hlRuleOK Q l) \<Longrightarrow>
        (\<forall>q \<in> set (hlFitchScopeRecord S out). hlFitchScopeOf F (fst q) = snd q) \<Longrightarrow>
        f0 \<le> fi \<Longrightarrow> c0 \<le> ct \<Longrightarrow>
        (\<forall>t \<in> set (hlFlattenFitch out).
           \<forall>l. hlLookupLine Q (fst t) = Some l \<longrightarrow> hlRuleOKG (hlScopeSrc F) Q l)"
  shows "\<forall>t \<in> set (hlFlattenFitch items).
           \<forall>l. hlLookupLine Q (fst t) = Some l \<longrightarrow> hlRuleOKG (hlScopeSrc F) Q l"
  using emitted wictx wrules wrec start cstart each
proof (induction ds arbitrary: first count items ns after cnt)
  case Nil
  then show ?case by simp
next
  case (Cons e ds)
  from Cons.prems(1) obtain out k mid c1 rest ks where
    hd: "emit first count e = (out,k,mid,c1)"
    and tl: "hlEmitDerivationsUsing emit mid c1 ds = (rest,ks,after,cnt)"
    and items: "items = out @ rest"
    by (auto simp: Let_def split: prod.splits)
  have iout: "hlItemsCtx Q out" and irest: "hlItemsCtx Q rest"
    using Cons.prems(2) items by (simp_all add: hlFlattenFitch_append)
  have rout: "\<forall>t \<in> set (hlFlattenFitch out).
                \<forall>l. hlLookupLine Q (fst t) = Some l \<longrightarrow> hlRuleOK Q l"
    and rrest: "\<forall>t \<in> set (hlFlattenFitch rest).
                  \<forall>l. hlLookupLine Q (fst t) = Some l \<longrightarrow> hlRuleOK Q l"
    using Cons.prems(3) items by (auto simp: hlFlattenFitch_append)
  have aout: "\<forall>q \<in> set (hlFitchScopeRecord S out). hlFitchScopeOf F (fst q) = snd q"
    and arest: "\<forall>q \<in> set (hlFitchScopeRecord S rest). hlFitchScopeOf F (fst q) = snd q"
    using Cons.prems(4) items by (auto simp: hlFitchScopeRecord_append)
  have startMid: "f0 \<le> mid" using Cons.prems(5) mono[OF hd] by simp
  have cstartMid: "c0 \<le> c1" using Cons.prems(6) cmono[OF hd] by simp
  have here: "\<forall>t \<in> set (hlFlattenFitch out).
                \<forall>l. hlLookupLine Q (fst t) = Some l \<longrightarrow> hlRuleOKG (hlScopeSrc F) Q l"
    by (rule Cons.prems(7)[OF _ hd iout rout aout Cons.prems(5) Cons.prems(6)]) simp
  have rest_ok: "\<forall>t \<in> set (hlFlattenFitch rest).
                   \<forall>l. hlLookupLine Q (fst t) = Some l \<longrightarrow> hlRuleOKG (hlScopeSrc F) Q l"
  proof (rule Cons.IH[OF tl irest rrest arest startMid cstartMid])
    fix u fi ct out2 k2 af2 c3
    assume mem: "u \<in> set ds" and got: "emit fi ct u = (out2,k2,af2,c3)"
      and dd: "hlItemsCtx Q out2"
      and rr: "\<forall>t \<in> set (hlFlattenFitch out2).
                 \<forall>l. hlLookupLine Q (fst t) = Some l \<longrightarrow> hlRuleOK Q l"
      and aa: "\<forall>q \<in> set (hlFitchScopeRecord S out2). hlFitchScopeOf F (fst q) = snd q"
      and ff: "f0 \<le> fi" and cc: "c0 \<le> ct"
    have "u \<in> set (e # ds)" using mem by simp
    from Cons.prems(7)[OF this got dd rr aa ff cc] show
      "\<forall>t \<in> set (hlFlattenFitch out2).
         \<forall>l. hlLookupLine Q (fst t) = Some l \<longrightarrow> hlRuleOKG (hlScopeSrc F) Q l" .
  qed
  show ?case using here rest_ok items by (auto simp: hlFlattenFitch_append)
qed

lemma hlForallRepair_disjoint:
  assumes rp: "hlRepairDerivation base count (hlForallRepairConstants scope phi e)
                 e = (c0,prs,rep)"
      and sb: "hlScopeBelow base count scope"
      and nbe: "hlNamesBelow base count e"
  shows "(hlConstantsInFormula (hlDerivationFormula rep) -
          hlConstantsInFormula phi) \<inter> hlConstantsInScope scope = {}"
proof -
  have form: "hlDerivationFormula rep = hlRenamePairsFormula prs (hlDerivationFormula e)"
    by (rule hlDerivationFormula_repair[OF rp])
  show ?thesis
    unfolding form
  proof (rule hlRepair_disjoint[OF rp sb])
    fix c assume "c \<in> hlConstantsInFormula (hlDerivationFormula e)"
      and "c \<notin> hlConstantsInFormula phi" and "c \<in> hlConstantsInScope scope"
    then show "c \<in> set (hlForallRepairConstants scope phi e)"
      by (simp add: set_hlForallRepairConstants)
  next
    show "\<forall>c \<in> set (hlForallRepairConstants scope phi e). nlen c < base + count"
      using nbe hlDerivationFormula_in_formulas[of e]
      by (auto simp: set_hlForallRepairConstants hlNamesBelow_def
          hlDerivationConstants_def)
  qed
qed

lemma hlExistsRepair_disjoint:
  assumes rp: "hlRepairDerivation base count (hlExistsRepairConstants scope af src phi)
                 body = (cR,prs,rbody)"
      and sb: "hlScopeBelow base count scope"
      and nbaf: "\<forall>c \<in> hlConstantsInFormula af. nlen c < base + count"
  shows "(hlConstantsInFormula (hlRenamePairsFormula prs af) -
          (hlConstantsInFormula (hlDerivationFormula src) \<union>
           hlConstantsInFormula phi)) \<inter> hlConstantsInScope scope = {}"
proof (rule hlRepair_disjoint[OF rp sb])
  fix c assume "c \<in> hlConstantsInFormula af"
    and "c \<notin> hlConstantsInFormula (hlDerivationFormula src) \<union> hlConstantsInFormula phi"
    and "c \<in> hlConstantsInScope scope"
  then show "c \<in> set (hlExistsRepairConstants scope af src phi)"
    by (simp add: set_hlExistsRepairConstants)
next
  show "\<forall>c \<in> set (hlExistsRepairConstants scope af src phi). nlen c < base + count"
    using nbaf by (auto simp: set_hlExistsRepairConstants)
qed

text \<open>The steps can also be rebuilt from the dependency-based check the erasure
  already passes, which is how the emitter induction supplies them.\<close>

lemma hlRuleOK_ForallIntro_scope:
  assumes ok: "hlRuleOK P l"
      and j: "hlJustification l = HL_ForallIntro m"
      and lu: "hlLookupLine P m = Some lm"
      and disj: "(hlConstantsInFormula (hlFormula lm) -
                  hlConstantsInFormula (hlFormula l)) \<inter> hlConstantsInScope H = {}"
  shows "hlForallIntroStep (hlFormula lm) (hlFormula l) H"
proof -
  obtain xs core where xc: "hlCollectForalls (hlFormula l) = (xs,core)"
    by (cases "hlCollectForalls (hlFormula l)") auto
  from ok j lu xc obtain cs where
    ne: "xs \<noteq> []"
    and inf: "hlInferWitnessConstsK xs core (length xs) (hlFormula lm) = Some cs"
    and abst: "hlAbstractMany (filter (\<lambda>xc. snd xc \<noteq> STR '''') (zip xs cs))
                 (hlFormula lm) = Some core"
    by (auto simp: hlRuleOK_def Let_def split: option.splits)
  have core: "hlConstantsInFormula core = hlConstantsInFormula (hlFormula l)"
    using hlCollectForalls_constants[of "hlFormula l"] xc by simp
  have fresh: "w \<notin> hlConstantsInScope H"
    if w: "w \<in> snd ` set (filter (\<lambda>xc. snd xc \<noteq> STR '''') (zip xs cs))" for w
  proof -
    have "w \<in> set cs" using w by (auto dest: set_zip_rightD)
    moreover have "w \<noteq> STR ''''" using w by auto
    ultimately have inc: "w \<in> hlConstantsInFormula (hlFormula lm)"
      using hlInferWitnessConstsK_constants[OF inf] by blast
    have "w \<notin> hlConstantsInFormula core"
      using hlAbstractMany_removes[OF abst] w by blast
    then show ?thesis using inc core disj by blast
  qed
  show ?thesis
    unfolding hlForallIntroStep_def
    using xc ne inf abst fresh by (simp add: Let_def)
qed

lemma hlRuleOK_ExistsElim_scope:
  assumes ok: "hlRuleOK P l"
      and j: "hlJustification l = HL_ExistsElim m x c"
      and lm: "hlLookupLine P m = Some lm"
      and lx: "hlLookupLine P x = Some la"
      and lc: "hlLookupLine P c = Some lc"
      and disj: "(hlConstantsInFormula (hlFormula la) -
                  (hlConstantsInFormula (hlFormula lm) \<union>
                   hlConstantsInFormula (hlFormula lc))) \<inter> hlConstantsInScope H = {}"
  shows "hlExistsElimStep (hlFormula lm) (hlFormula la) (hlFormula lc) H"
proof -
  obtain xs p where xp: "hlCollectExists (hlFormula lm) = (xs,p)"
    by (cases "hlCollectExists (hlFormula lm)") auto
  obtain ys q where yq: "hlCollectExists (hlFormula la) = (ys,q)"
    by (cases "hlCollectExists (hlFormula la)") auto
  from ok j lm lx lc xp yq obtain k cs where
    ne: "xs \<noteq> []"
    and ec: "hlEliminationCount xs ys = Some k"
    and inf: "hlInferWitnessConstsK xs (hlPrefixExists ys p) k (hlFormula la) = Some cs"
    and abst: "hlAbstractMany (filter (\<lambda>xc. snd xc \<noteq> STR '''') (zip (take k xs) cs))
                 (hlFormula la) = Some (hlPrefixExists ys p)"
    and goalfresh: "\<forall>w \<in> snd ` set (filter (\<lambda>xc. snd xc \<noteq> STR '''')
                                      (zip (take k xs) cs)).
                      w \<notin> hlConstantsInFormula (hlFormula lc)"
    by (auto simp: hlRuleOK_def Let_def split: option.splits)
  have core: "hlConstantsInFormula (hlPrefixExists ys p) =
              hlConstantsInFormula (hlFormula lm)"
    using hlCollectExists_constants[of "hlFormula lm"] xp by simp
  have fresh: "w \<notin> hlConstantsInScope H"
    if w: "w \<in> snd ` set (filter (\<lambda>xc. snd xc \<noteq> STR '''') (zip (take k xs) cs))" for w
  proof -
    have "w \<in> set cs" using w by (auto dest: set_zip_rightD)
    moreover have "w \<noteq> STR ''''" using w by auto
    ultimately have inc: "w \<in> hlConstantsInFormula (hlFormula la)"
      using hlInferWitnessConstsK_constants[OF inf] by blast
    have "w \<notin> hlConstantsInFormula (hlPrefixExists ys p)"
      using hlAbstractMany_removes[OF abst] w by blast
    then have "w \<notin> hlConstantsInFormula (hlFormula lm)" using core by simp
    moreover have "w \<notin> hlConstantsInFormula (hlFormula lc)" using goalfresh w by blast
    ultimately show ?thesis using inc disj by blast
  qed
  show ?thesis
    unfolding hlExistsElimStep_def
    using xp yq ne ec inf abst fresh goalfresh by (simp add: Let_def)
qed

lemma hlRepairDerivation_pairs_range:
  "hlRepairDerivation base count bad e = (count',pairs,e') \<Longrightarrow>
   \<forall>op \<in> set pairs. \<exists>k. count \<le> k \<and> k < count' \<and> snd op = hlFreshIndex base k"
proof (induction bad arbitrary: count e count' pairs e')
  case Nil
  then show ?case by simp
next
  case (Cons old olds)
  from Cons.prems obtain c2 ps r where
    rec: "hlRepairDerivation base (Suc count) olds
            (hlRenameDerivation old (hlFreshIndex base count) e) = (c2,ps,r)"
    and eq: "pairs = (old,hlFreshIndex base count) # ps" "count' = c2"
    by (auto simp: Let_def split: prod.splits)
  have ge: "Suc count \<le> c2" by (rule hlRepairDerivation_count_le[OF rec])
  show ?case
  proof
    fix op assume "op \<in> set pairs"
    then consider "op = (old,hlFreshIndex base count)" | "op \<in> set ps" using eq by auto
    then show "\<exists>k. count \<le> k \<and> k < count' \<and> snd op = hlFreshIndex base k"
    proof cases
      case 1
      then show ?thesis using ge eq by auto
    next
      case 2
      then obtain k where k: "Suc count \<le> k" "k < c2" "snd op = hlFreshIndex base k"
        using Cons.IH[OF rec] by blast
      have "count \<le> k" using k(1) by simp
      then show ?thesis using k(2,3) eq by blast
    qed
  qed
qed

lemma hlRenamePairsFormula_below:
  assumes rp: "hlRepairDerivation base count bad e = (count',pairs,e')"
      and af: "\<forall>c \<in> hlConstantsInFormula g. nlen c < base + count"
  shows "\<forall>c \<in> hlConstantsInFormula (hlRenamePairsFormula pairs g). nlen c < base + count'"
proof
  fix c assume "c \<in> hlConstantsInFormula (hlRenamePairsFormula pairs g)"
  then have "c \<in> hlConstantsInFormula g \<or> c \<in> snd ` set pairs"
    using hlRenamePairsFormula_constants_sub by blast
  then show "nlen c < base + count'"
  proof
    assume "c \<in> hlConstantsInFormula g"
    then have "nlen c < base + count" using af by blast
    moreover have "count \<le> count'" by (rule hlRepairDerivation_count_le[OF rp])
    ultimately show ?thesis by simp
  next
    assume "c \<in> snd ` set pairs"
    then obtain op where op: "op \<in> set pairs" "c = snd op" by blast
    then obtain k where k: "count \<le> k" "k < count'" "snd op = hlFreshIndex base k"
      using hlRepairDerivation_pairs_range[OF rp] by blast
    then show ?thesis using op(2) by simp
  qed
qed

section \<open>The scope-based check on the emitted proof\<close>

lemma hlEmitDerivationFuel_scopeOK:
  assumes "size d < length fuel"
      and emit: "hlEmitDerivationFuel fuel base env scope first count d = (items,n,after,cnt)"
      and ok: "hlDerivationOK d"
      and ictx: "hlItemsCtx Q items"
      and nb: "hlNamesBelow base count d"
      and sb: "hlScopeBelow base count scope"
      and ctx: "hlEmitCtx Q env first d"
      and rules: "\<forall>t \<in> set (hlFlattenFitch items).
                    \<forall>l. hlLookupLine Q (fst t) = Some l \<longrightarrow> hlRuleOK Q l"
      and agree: "\<forall>q \<in> set (hlFitchScopeRecord S items). hlFitchScopeOf F (fst q) = snd q"
      and inv: "hlAssumptionConstants Q S \<subseteq> hlConstantsInScope scope"
      and refinv: "hlReferencedConstants Q S \<subseteq> hlConstantsInScope scope"
      and sbelow: "\<forall>m \<in> S. m < first"
      and dist: "distinct (map hlLineNumber Q)"
      and pos: "0 < base"
  shows "\<forall>t \<in> set (hlFlattenFitch items).
           \<forall>l. hlLookupLine Q (fst t) = Some l \<longrightarrow> hlRuleOKG (hlScopeSrc F) Q l"
  using assms
proof (induction d arbitrary: fuel env scope first count items n after cnt S
       rule: measure_induct_rule[where f=size])
  case (less d)
  from less.prems(1) obtain u fs where fuel: "fuel = u # fs" by (cases fuel) auto
  obtain phi rule where d: "d = HL_Derivation phi rule" by (cases d) auto
  have small: "size e < length fs" if "size e < size d" for e
    using less.prems(1) that fuel by simp

  have IH: "\<forall>t \<in> set (hlFlattenFitch out).
              \<forall>l. hlLookupLine Q (fst t) = Some l \<longrightarrow> hlRuleOKG (hlScopeSrc F) Q l"
    if "size e < size d"
      and "hlEmitDerivationFuel fs base ev sc fi ct e = (out,k,af,c2)"
      and "hlDerivationOK e"
      and "hlItemsCtx Q out"
      and "hlNamesBelow base ct e"
      and "hlScopeBelow base ct sc"
      and "hlEmitCtx Q ev fi e"
      and "\<forall>t \<in> set (hlFlattenFitch out).
             \<forall>l. hlLookupLine Q (fst t) = Some l \<longrightarrow> hlRuleOK Q l"
      and "\<forall>q \<in> set (hlFitchScopeRecord T out). hlFitchScopeOf F (fst q) = snd q"
      and "hlAssumptionConstants Q T \<subseteq> hlConstantsInScope sc"
      and "hlReferencedConstants Q T \<subseteq> hlConstantsInScope sc"
      and "\<forall>m \<in> T. m < fi"
    for e ev sc fi ct out k af c2 T
    using less.IH[OF that(1) small[OF that(1)] that(2,3,4,5,6,7,8,9,10,11,12)
                  less.prems(13) less.prems(14)] .

  have NB: "hlNamesBelow base ct e"
    if sub: "e \<in> set (hlSubDerivations rule)" and le: "count \<le> ct" for e ct
  proof -
    have "hlDerivationConstants e \<subseteq> hlDerivationConstants d"
      using hlDerivationConstants_sub[OF sub, of phi] d by simp
    from hlNamesBelow_sub[OF less.prems(5) this] show ?thesis
      using le by (rule hlNamesBelow_mono)
  qed

  show ?case
  proof (cases rule)
    case (HL_DAssume i)
    with less.prems(2) fuel d show ?thesis by simp
  next
    case (HL_DPremise i)
    with less.prems(2) fuel d show ?thesis by simp
  next
    case HL_DEqI
    have eq: "items = [HL_FLine first phi HL_FEqI]"
      using less.prems(2) fuel d HL_DEqI by (auto simp: Let_def)
    have "hlRuleOKG (hlScopeSrc F) Q l" if ll: "hlLookupLine Q first = Some l" for l
    proof (rule hlRuleOKG_of_hlRuleOK)
      show "hlRuleOK Q l" using less.prems(8) eq ll by simp
    next
      show "hlJustification l \<noteq> HL_ForallIntro m" for m
        using less.prems(4) eq ll by fastforce
    next
      show "hlJustification l \<noteq> HL_ExistsElim m a c" for m a c
        using less.prems(4) eq ll by fastforce
    qed
    then show ?thesis using eq by simp
  next
    case HL_DLEM
    have eq: "items = [HL_FLine first phi HL_FLEM]"
      using less.prems(2) fuel d HL_DLEM by (auto simp: Let_def)
    have "hlRuleOKG (hlScopeSrc F) Q l" if ll: "hlLookupLine Q first = Some l" for l
    proof (rule hlRuleOKG_of_hlRuleOK)
      show "hlRuleOK Q l" using less.prems(8) eq ll by simp
    next
      show "hlJustification l \<noteq> HL_ForallIntro m" for m
        using less.prems(4) eq ll by fastforce
    next
      show "hlJustification l \<noteq> HL_ExistsElim m a c" for m a c
        using less.prems(4) eq ll by fastforce
    qed
    then show ?thesis using eq by simp
  next
    case (HL_DMP e1 e2)
    obtain front k1 mid c1 where
      em1: "hlEmitDerivationFuel fs base env scope first count e1 = (front,k1,mid,c1)"
      by (cases "hlEmitDerivationFuel fs base env scope first count e1") auto
    obtain rear k2 fin c2 where
      em2: "hlEmitDerivationFuel fs base env scope mid c1 e2 = (rear,k2,fin,c2)"
      by (cases "hlEmitDerivationFuel fs base env scope mid c1 e2") auto
    have sz1: "size e1 < size d" and sz2: "size e2 < size d" using d HL_DMP by simp_all
    have le: "first \<le> mid" by (rule hlEmitDerivationFuel_start_le[OF em1])
    have lec: "count \<le> c1" by (rule hlEmitDerivationFuel_count_le[OF em1])
    have eq: "items = front @ rear @ [HL_FLine fin phi (HL_FMP k1 k2)] \<and> n = fin"
      using less.prems(2) fuel d HL_DMP em1 em2 by (auto simp: Let_def)
    have flat: "hlFlattenFitch items =
        hlFlattenFitch front @ hlFlattenFitch rear @ [(fin,phi,HL_FMP k1 k2)]"
      using eq by (simp add: hlFlattenFitch_append)
    have rec: "hlFitchScopeRecord S items =
        hlFitchScopeRecord S front @ hlFitchScopeRecord S rear @ [(fin,S)]"
      using eq by (simp add: hlFitchScopeRecord_append)
    have ctx1: "hlEmitCtx Q env first e1" and ctx2: "hlEmitCtx Q env mid e2"
      using less.prems(7) d HL_DMP le
      by (auto simp: hlEmitCtx_def hlDepsCtx_def hlFormCtx_def hlEnvBelow_def)
    have IH1: "\<forall>t \<in> set (hlFlattenFitch front).
                 \<forall>l. hlLookupLine Q (fst t) = Some l \<longrightarrow> hlRuleOKG (hlScopeSrc F) Q l"
    proof (rule IH[OF sz1 em1])
      show "hlDerivationOK e1" using less.prems(3) d HL_DMP by simp
      show "hlItemsCtx Q front" using less.prems(4) flat by (simp add: hlFlattenFitch_append)
      show "hlNamesBelow base count e1" by (rule NB) (simp_all add: HL_DMP)
      show "hlScopeBelow base count scope" by (rule less.prems(6))
      show "hlEmitCtx Q env first e1" by (rule ctx1)
      show "\<forall>t \<in> set (hlFlattenFitch front).
              \<forall>l. hlLookupLine Q (fst t) = Some l \<longrightarrow> hlRuleOK Q l"
        using less.prems(8) flat by auto
      show "\<forall>q \<in> set (hlFitchScopeRecord S front). hlFitchScopeOf F (fst q) = snd q"
        using less.prems(9) rec by auto
      show "hlAssumptionConstants Q S \<subseteq> hlConstantsInScope scope" by (rule less.prems(10))
      show "hlReferencedConstants Q S \<subseteq> hlConstantsInScope scope" by (rule less.prems(11))
      show "\<forall>m \<in> S. m < first" by (rule less.prems(12))
    qed
    have IH2: "\<forall>t \<in> set (hlFlattenFitch rear).
                 \<forall>l. hlLookupLine Q (fst t) = Some l \<longrightarrow> hlRuleOKG (hlScopeSrc F) Q l"
    proof (rule IH[OF sz2 em2])
      show "hlDerivationOK e2" using less.prems(3) d HL_DMP by simp
      show "hlItemsCtx Q rear" using less.prems(4) flat by (simp add: hlFlattenFitch_append)
      show "hlNamesBelow base c1 e2" by (rule NB) (use HL_DMP lec in simp_all)
      show "hlScopeBelow base c1 scope" by (rule hlScopeBelow_mono[OF less.prems(6) lec])
      show "hlEmitCtx Q env mid e2" by (rule ctx2)
      show "\<forall>t \<in> set (hlFlattenFitch rear).
              \<forall>l. hlLookupLine Q (fst t) = Some l \<longrightarrow> hlRuleOK Q l"
        using less.prems(8) flat by auto
      show "\<forall>q \<in> set (hlFitchScopeRecord S rear). hlFitchScopeOf F (fst q) = snd q"
        using less.prems(9) rec by auto
      show "hlAssumptionConstants Q S \<subseteq> hlConstantsInScope scope" by (rule less.prems(10))
      show "hlReferencedConstants Q S \<subseteq> hlConstantsInScope scope" by (rule less.prems(11))
      show "\<forall>m \<in> S. m < mid" using less.prems(12) le by auto
    qed
    have newline: "hlRuleOKG (hlScopeSrc F) Q l" if ll: "hlLookupLine Q fin = Some l" for l
    proof (rule hlRuleOKG_of_hlRuleOK)
      show "hlRuleOK Q l" using less.prems(8) flat ll by auto
    next
      show "hlJustification l \<noteq> HL_ForallIntro m" for m
        using less.prems(4) flat ll by fastforce
    next
      show "hlJustification l \<noteq> HL_ExistsElim m a c" for m a c
        using less.prems(4) flat ll by fastforce
    qed
    show ?thesis using IH1 IH2 newline flat by auto
  next
    case (HL_DMT e1 e2)
    obtain front k1 mid c1 where
      em1: "hlEmitDerivationFuel fs base env scope first count e1 = (front,k1,mid,c1)"
      by (cases "hlEmitDerivationFuel fs base env scope first count e1") auto
    obtain rear k2 fin c2 where
      em2: "hlEmitDerivationFuel fs base env scope mid c1 e2 = (rear,k2,fin,c2)"
      by (cases "hlEmitDerivationFuel fs base env scope mid c1 e2") auto
    have sz1: "size e1 < size d" and sz2: "size e2 < size d" using d HL_DMT by simp_all
    have le: "first \<le> mid" by (rule hlEmitDerivationFuel_start_le[OF em1])
    have lec: "count \<le> c1" by (rule hlEmitDerivationFuel_count_le[OF em1])
    have eq: "items = front @ rear @ [HL_FLine fin phi (HL_FMT k1 k2)] \<and> n = fin"
      using less.prems(2) fuel d HL_DMT em1 em2 by (auto simp: Let_def)
    have flat: "hlFlattenFitch items =
        hlFlattenFitch front @ hlFlattenFitch rear @ [(fin,phi,HL_FMT k1 k2)]"
      using eq by (simp add: hlFlattenFitch_append)
    have rec: "hlFitchScopeRecord S items =
        hlFitchScopeRecord S front @ hlFitchScopeRecord S rear @ [(fin,S)]"
      using eq by (simp add: hlFitchScopeRecord_append)
    have ctx1: "hlEmitCtx Q env first e1" and ctx2: "hlEmitCtx Q env mid e2"
      using less.prems(7) d HL_DMT le
      by (auto simp: hlEmitCtx_def hlDepsCtx_def hlFormCtx_def hlEnvBelow_def)
    have IH1: "\<forall>t \<in> set (hlFlattenFitch front).
                 \<forall>l. hlLookupLine Q (fst t) = Some l \<longrightarrow> hlRuleOKG (hlScopeSrc F) Q l"
    proof (rule IH[OF sz1 em1])
      show "hlDerivationOK e1" using less.prems(3) d HL_DMT by simp
      show "hlItemsCtx Q front" using less.prems(4) flat by (simp add: hlFlattenFitch_append)
      show "hlNamesBelow base count e1" by (rule NB) (simp_all add: HL_DMT)
      show "hlScopeBelow base count scope" by (rule less.prems(6))
      show "hlEmitCtx Q env first e1" by (rule ctx1)
      show "\<forall>t \<in> set (hlFlattenFitch front).
              \<forall>l. hlLookupLine Q (fst t) = Some l \<longrightarrow> hlRuleOK Q l"
        using less.prems(8) flat by auto
      show "\<forall>q \<in> set (hlFitchScopeRecord S front). hlFitchScopeOf F (fst q) = snd q"
        using less.prems(9) rec by auto
      show "hlAssumptionConstants Q S \<subseteq> hlConstantsInScope scope" by (rule less.prems(10))
      show "hlReferencedConstants Q S \<subseteq> hlConstantsInScope scope" by (rule less.prems(11))
      show "\<forall>m \<in> S. m < first" by (rule less.prems(12))
    qed
    have IH2: "\<forall>t \<in> set (hlFlattenFitch rear).
                 \<forall>l. hlLookupLine Q (fst t) = Some l \<longrightarrow> hlRuleOKG (hlScopeSrc F) Q l"
    proof (rule IH[OF sz2 em2])
      show "hlDerivationOK e2" using less.prems(3) d HL_DMT by simp
      show "hlItemsCtx Q rear" using less.prems(4) flat by (simp add: hlFlattenFitch_append)
      show "hlNamesBelow base c1 e2" by (rule NB) (use HL_DMT lec in simp_all)
      show "hlScopeBelow base c1 scope" by (rule hlScopeBelow_mono[OF less.prems(6) lec])
      show "hlEmitCtx Q env mid e2" by (rule ctx2)
      show "\<forall>t \<in> set (hlFlattenFitch rear).
              \<forall>l. hlLookupLine Q (fst t) = Some l \<longrightarrow> hlRuleOK Q l"
        using less.prems(8) flat by auto
      show "\<forall>q \<in> set (hlFitchScopeRecord S rear). hlFitchScopeOf F (fst q) = snd q"
        using less.prems(9) rec by auto
      show "hlAssumptionConstants Q S \<subseteq> hlConstantsInScope scope" by (rule less.prems(10))
      show "hlReferencedConstants Q S \<subseteq> hlConstantsInScope scope" by (rule less.prems(11))
      show "\<forall>m \<in> S. m < mid" using less.prems(12) le by auto
    qed
    have newline: "hlRuleOKG (hlScopeSrc F) Q l" if ll: "hlLookupLine Q fin = Some l" for l
    proof (rule hlRuleOKG_of_hlRuleOK)
      show "hlRuleOK Q l" using less.prems(8) flat ll by auto
    next
      show "hlJustification l \<noteq> HL_ForallIntro m" for m
        using less.prems(4) flat ll by fastforce
    next
      show "hlJustification l \<noteq> HL_ExistsElim m a c" for m a c
        using less.prems(4) flat ll by fastforce
    qed
    show ?thesis using IH1 IH2 newline flat by auto
  next
    case (HL_DDN e)
    obtain front k mid c1 where
      em: "hlEmitDerivationFuel fs base env scope first count e = (front,k,mid,c1)"
      by (cases "hlEmitDerivationFuel fs base env scope first count e") auto
    have sz: "size e < size d" using d HL_DDN by simp
    have eq: "items = front @ [HL_FLine mid phi (HL_FDN k)] \<and> n = mid"
      using less.prems(2) fuel d HL_DDN em by (auto simp: Let_def)
    have flat: "hlFlattenFitch items = hlFlattenFitch front @ [(mid,phi,HL_FDN k)]"
      using eq by (simp add: hlFlattenFitch_append)
    have rec: "hlFitchScopeRecord S items = hlFitchScopeRecord S front @ [(mid,S)]"
      using eq by (simp add: hlFitchScopeRecord_append)
    have IHf: "\<forall>t \<in> set (hlFlattenFitch front).
                 \<forall>l. hlLookupLine Q (fst t) = Some l \<longrightarrow> hlRuleOKG (hlScopeSrc F) Q l"
    proof (rule IH[OF sz em])
      show "hlDerivationOK e" using less.prems(3) d HL_DDN by simp
      show "hlItemsCtx Q front" using less.prems(4) flat by (simp add: hlFlattenFitch_append)
      show "hlNamesBelow base count e" by (rule NB) (simp_all add: HL_DDN)
      show "hlScopeBelow base count scope" by (rule less.prems(6))
      show "hlEmitCtx Q env first e"
        using less.prems(7) d HL_DDN
        by (simp add: hlEmitCtx_def hlDepsCtx_def hlFormCtx_def)
      show "\<forall>t \<in> set (hlFlattenFitch front).
              \<forall>l. hlLookupLine Q (fst t) = Some l \<longrightarrow> hlRuleOK Q l"
        using less.prems(8) flat by auto
      show "\<forall>q \<in> set (hlFitchScopeRecord S front). hlFitchScopeOf F (fst q) = snd q"
        using less.prems(9) rec by auto
      show "hlAssumptionConstants Q S \<subseteq> hlConstantsInScope scope" by (rule less.prems(10))
      show "hlReferencedConstants Q S \<subseteq> hlConstantsInScope scope" by (rule less.prems(11))
      show "\<forall>m \<in> S. m < first" by (rule less.prems(12))
    qed
    have newline: "hlRuleOKG (hlScopeSrc F) Q l" if ll: "hlLookupLine Q mid = Some l" for l
    proof (rule hlRuleOKG_of_hlRuleOK)
      show "hlRuleOK Q l" using less.prems(8) flat ll by auto
    next
      show "hlJustification l \<noteq> HL_ForallIntro m" for m
        using less.prems(4) flat ll by fastforce
    next
      show "hlJustification l \<noteq> HL_ExistsElim m a c" for m a c
        using less.prems(4) flat ll by fastforce
    qed
    show ?thesis using IHf newline flat by auto
  next
    case (HL_DCP a p body)
    obtain bi bl n1 c1 where
      em: "hlEmitDerivationFuel fs base ((a,first,p) # env) (p # scope) (first + 1) count body
             = (bi,bl,n1,c1)"
      by (cases "hlEmitDerivationFuel fs base ((a,first,p) # env) (p # scope)
                   (first + 1) count body") auto
    define cb where "cb = (if bi = [] \<and> bl \<noteq> first
                           then [HL_FLine n1 (hlDerivationFormula body) (HL_FReit bl)]
                           else bi)"
    define lst where "lst = (if bi = [] \<and> bl \<noteq> first then n1 else bl)"
    define aft where "aft = (if bi = [] \<and> bl \<noteq> first then n1 + 1 else n1)"
    have sz: "size body < size d" using d HL_DCP by simp
    have okb: "hlDerivationOK body" using less.prems(3) d HL_DCP by simp
    have dis: "hlDischargeOK a p body" using less.prems(3) d HL_DCP by simp
    have eq: "items = [HL_FSub (HL_Subproof first p cb),
                       HL_FLine aft phi (HL_FCP (first,lst))] \<and> n = aft"
      using less.prems(2) fuel d HL_DCP em
      by (auto simp: Let_def cb_def lst_def aft_def)
    have flat: "hlFlattenFitch items =
      (first,p,HL_FAssume) # hlFlattenFitch cb @ [(aft,phi,HL_FCP (first,lst))]"
      using eq by simp
    have rec: "hlFitchScopeRecord S items =
      (first, insert first S) # hlFitchScopeRecord (insert first S) cb @ [(aft,S)]"
      using eq by (simp add: hlFitchScopeRecord_append)
    have headin: "(first,p,HL_FAssume) \<in> set (hlFlattenFitch items)" using flat by simp
    have headF: "hlLookF Q first = Some p" using less.prems(4) headin by fastforce
    obtain la where la: "hlLookupLine Q first = Some la" and laf: "hlFormula la = p"
      using headF by (cases "hlLookupLine Q first") auto
    have laref: "hlReferences la = {first}"
      using less.prems(4) headin la by (fastforce simp: hlFitchDependenciesOf_def)
    have below: "hlEnvBelow env first"
      using less.prems(7) by (simp add: hlEmitCtx_def hlDepsCtx_def)
    have covered: "\<forall>nf \<in> set (hlOpenAssumptions body).
        fst nf \<noteq> a \<longrightarrow> nf \<in> set (hlOpenAssumptions d)"
      using d HL_DCP by simp
    have ctxb: "hlEmitCtx Q ((a,first,p) # env) (first + 1) body"
      unfolding hlEmitCtx_def hlDepsCtx_def hlFormCtx_def
    proof (intro conjI ballI)
      show "hlEnvBelow ((a,first,p) # env) (first + 1)"
        by (rule hlEnvBelow_Cons[OF below]) auto
    next
      fix nf assume nf: "nf \<in> set (hlOpenAssumptions body)"
      show "fst nf \<in> fst ` set ((a,first,p) # env)"
        using nf covered less.prems(7)
        by (cases "fst nf = a") (auto simp: hlEmitCtx_def hlDepsCtx_def)
    next
      fix nf assume nf: "nf \<in> set (hlOpenAssumptions body)"
      show "hlRefsF Q (hlEnvironmentLine ((a,first,p) # env) (fst nf)) =
            {hlEnvironmentLine ((a,first,p) # env) (fst nf)}"
      proof (cases "fst nf = a")
        case True
        then show ?thesis using la laref by simp
      next
        case False
        then have "nf \<in> set (hlOpenAssumptions d)" using nf covered by blast
        then show ?thesis using less.prems(7) False
          unfolding hlEmitCtx_def hlDepsCtx_def by fastforce
      qed
    next
      fix nf assume nf: "nf \<in> set (hlOpenAssumptions body)"
      show "hlLookF Q (hlEnvironmentLine ((a,first,p) # env) (fst nf)) = Some (snd nf)"
      proof (cases "fst nf = a")
        case True
        then have "snd nf = p" using dis nf by (simp add: hlDischargeOK_def)
        then show ?thesis using True headF by simp
      next
        case False
        then have "nf \<in> set (hlOpenAssumptions d)" using nf covered by blast
        then show ?thesis using less.prems(7) False
          unfolding hlEmitCtx_def hlFormCtx_def by fastforce
      qed
    qed
    have icb: "hlItemsCtx Q cb"
      using less.prems(4) flat by (simp add: hlFlattenFitch_append)
    have pform: "\<forall>c \<in> hlConstantsInFormula p. nlen c < base + count"
      using less.prems(5) d HL_DCP
      by (auto simp: hlNamesBelow_def hlDerivationConstants_def)
    have ibi: "hlItemsCtx Q bi" by (rule hlItemsCtx_closedBody[OF cb_def icb])
    have subrec: "set (hlFitchScopeRecord (insert first S) bi) \<subseteq>
                  set (hlFitchScopeRecord (insert first S) cb)"
      by (cases "bi = [] \<and> bl \<noteq> first") (simp_all add: cb_def)
    have subflat: "set (hlFlattenFitch bi) \<subseteq> set (hlFlattenFitch cb)"
      by (cases "bi = [] \<and> bl \<noteq> first") (simp_all add: cb_def)
    have IHb: "\<forall>t \<in> set (hlFlattenFitch bi).
                 \<forall>l. hlLookupLine Q (fst t) = Some l \<longrightarrow> hlRuleOKG (hlScopeSrc F) Q l"
    proof (rule IH[OF sz em])
      show "hlDerivationOK body" by (rule okb)
      show "hlItemsCtx Q bi" by (rule ibi)
      show "hlNamesBelow base count body" by (rule NB) (simp_all add: HL_DCP)
      show "hlScopeBelow base count (p # scope)"
        by (rule hlScopeBelow_Cons[OF less.prems(6) pform])
      show "hlEmitCtx Q ((a,first,p) # env) (first + 1) body" by (rule ctxb)
      show "\<forall>t \<in> set (hlFlattenFitch bi).
              \<forall>l. hlLookupLine Q (fst t) = Some l \<longrightarrow> hlRuleOK Q l"
        using less.prems(8) flat subflat by (auto simp: hlFlattenFitch_append)
      show "\<forall>q \<in> set (hlFitchScopeRecord (insert first S) bi).
              hlFitchScopeOf F (fst q) = snd q"
        using less.prems(9) rec subrec by auto
      show "hlAssumptionConstants Q (insert first S) \<subseteq> hlConstantsInScope (p # scope)"
        using hlAssumptionConstants_insert[OF less.prems(13) la] less.prems(10) laf
        by (auto simp: hlConstantsInScope_def)
      show "hlReferencedConstants Q (insert first S) \<subseteq> hlConstantsInScope (p # scope)"
        using hlReferencedConstants_insert[OF less.prems(13) la] less.prems(11) laf
        by (auto simp: hlConstantsInScope_def)
      show "\<forall>m \<in> insert first S. m < first + 1" using less.prems(12) by auto
    qed
    have cbOK: "\<forall>t \<in> set (hlFlattenFitch cb).
                  \<forall>l. hlLookupLine Q (fst t) = Some l \<longrightarrow> hlRuleOKG (hlScopeSrc F) Q l"
    proof (cases "bi = [] \<and> bl \<noteq> first")
      case False
      then have "cb = bi" using cb_def by simp
      then show ?thesis using IHb by simp
    next
      case True
      then have cbv: "cb = [HL_FLine n1 (hlDerivationFormula body) (HL_FReit bl)]"
        using cb_def by simp
      have "hlRuleOKG (hlScopeSrc F) Q l" if ll: "hlLookupLine Q n1 = Some l" for l
      proof (rule hlRuleOKG_of_hlRuleOK)
        show "hlRuleOK Q l" using less.prems(8) flat cbv ll by auto
      next
        show "hlJustification l \<noteq> HL_ForallIntro m" for m
          using less.prems(4) flat cbv ll by fastforce
      next
        show "hlJustification l \<noteq> HL_ExistsElim m a' c" for m a' c
          using less.prems(4) flat cbv ll by fastforce
      qed
      then show ?thesis using cbv by simp
    qed
    have headOK: "hlRuleOKG (hlScopeSrc F) Q l" if ll: "hlLookupLine Q first = Some l" for l
    proof (rule hlRuleOKG_of_hlRuleOK)
      show "hlRuleOK Q l" using less.prems(8) headin ll by auto
    next
      show "hlJustification l \<noteq> HL_ForallIntro m" for m
        using less.prems(4) headin ll by fastforce
    next
      show "hlJustification l \<noteq> HL_ExistsElim m a' c" for m a' c
        using less.prems(4) headin ll by fastforce
    qed
    have newline: "hlRuleOKG (hlScopeSrc F) Q l" if ll: "hlLookupLine Q aft = Some l" for l
    proof (rule hlRuleOKG_of_hlRuleOK)
      show "hlRuleOK Q l" using less.prems(8) flat ll by auto
    next
      show "hlJustification l \<noteq> HL_ForallIntro m" for m
        using less.prems(4) flat ll by fastforce
    next
      show "hlJustification l \<noteq> HL_ExistsElim m a' c" for m a' c
        using less.prems(4) flat ll by fastforce
    qed
    show ?thesis using cbOK headOK newline la flat by auto
  next
    case (HL_DAndI e1 e2)
    obtain front k1 mid c1 where
      em1: "hlEmitDerivationFuel fs base env scope first count e1 = (front,k1,mid,c1)"
      by (cases "hlEmitDerivationFuel fs base env scope first count e1") auto
    obtain rear k2 fin c2 where
      em2: "hlEmitDerivationFuel fs base env scope mid c1 e2 = (rear,k2,fin,c2)"
      by (cases "hlEmitDerivationFuel fs base env scope mid c1 e2") auto
    have sz1: "size e1 < size d" and sz2: "size e2 < size d" using d HL_DAndI by simp_all
    have le: "first \<le> mid" by (rule hlEmitDerivationFuel_start_le[OF em1])
    have lec: "count \<le> c1" by (rule hlEmitDerivationFuel_count_le[OF em1])
    have eq: "items = front @ rear @ [HL_FLine fin phi (HL_FAndI k1 k2)] \<and> n = fin"
      using less.prems(2) fuel d HL_DAndI em1 em2 by (auto simp: Let_def)
    have flat: "hlFlattenFitch items =
        hlFlattenFitch front @ hlFlattenFitch rear @ [(fin,phi,HL_FAndI k1 k2)]"
      using eq by (simp add: hlFlattenFitch_append)
    have rec: "hlFitchScopeRecord S items =
        hlFitchScopeRecord S front @ hlFitchScopeRecord S rear @ [(fin,S)]"
      using eq by (simp add: hlFitchScopeRecord_append)
    have ctx1: "hlEmitCtx Q env first e1" and ctx2: "hlEmitCtx Q env mid e2"
      using less.prems(7) d HL_DAndI le
      by (auto simp: hlEmitCtx_def hlDepsCtx_def hlFormCtx_def hlEnvBelow_def)
    have IH1: "\<forall>t \<in> set (hlFlattenFitch front).
                 \<forall>l. hlLookupLine Q (fst t) = Some l \<longrightarrow> hlRuleOKG (hlScopeSrc F) Q l"
    proof (rule IH[OF sz1 em1])
      show "hlDerivationOK e1" using less.prems(3) d HL_DAndI by simp
      show "hlItemsCtx Q front" using less.prems(4) flat by (simp add: hlFlattenFitch_append)
      show "hlNamesBelow base count e1" by (rule NB) (simp_all add: HL_DAndI)
      show "hlScopeBelow base count scope" by (rule less.prems(6))
      show "hlEmitCtx Q env first e1" by (rule ctx1)
      show "\<forall>t \<in> set (hlFlattenFitch front).
              \<forall>l. hlLookupLine Q (fst t) = Some l \<longrightarrow> hlRuleOK Q l"
        using less.prems(8) flat by auto
      show "\<forall>q \<in> set (hlFitchScopeRecord S front). hlFitchScopeOf F (fst q) = snd q"
        using less.prems(9) rec by auto
      show "hlAssumptionConstants Q S \<subseteq> hlConstantsInScope scope" by (rule less.prems(10))
      show "hlReferencedConstants Q S \<subseteq> hlConstantsInScope scope" by (rule less.prems(11))
      show "\<forall>m \<in> S. m < first" by (rule less.prems(12))
    qed
    have IH2: "\<forall>t \<in> set (hlFlattenFitch rear).
                 \<forall>l. hlLookupLine Q (fst t) = Some l \<longrightarrow> hlRuleOKG (hlScopeSrc F) Q l"
    proof (rule IH[OF sz2 em2])
      show "hlDerivationOK e2" using less.prems(3) d HL_DAndI by simp
      show "hlItemsCtx Q rear" using less.prems(4) flat by (simp add: hlFlattenFitch_append)
      show "hlNamesBelow base c1 e2" by (rule NB) (use HL_DAndI lec in simp_all)
      show "hlScopeBelow base c1 scope" by (rule hlScopeBelow_mono[OF less.prems(6) lec])
      show "hlEmitCtx Q env mid e2" by (rule ctx2)
      show "\<forall>t \<in> set (hlFlattenFitch rear).
              \<forall>l. hlLookupLine Q (fst t) = Some l \<longrightarrow> hlRuleOK Q l"
        using less.prems(8) flat by auto
      show "\<forall>q \<in> set (hlFitchScopeRecord S rear). hlFitchScopeOf F (fst q) = snd q"
        using less.prems(9) rec by auto
      show "hlAssumptionConstants Q S \<subseteq> hlConstantsInScope scope" by (rule less.prems(10))
      show "hlReferencedConstants Q S \<subseteq> hlConstantsInScope scope" by (rule less.prems(11))
      show "\<forall>m \<in> S. m < mid" using less.prems(12) le by auto
    qed
    have newline: "hlRuleOKG (hlScopeSrc F) Q l" if ll: "hlLookupLine Q fin = Some l" for l
    proof (rule hlRuleOKG_of_hlRuleOK)
      show "hlRuleOK Q l" using less.prems(8) flat ll by auto
    next
      show "hlJustification l \<noteq> HL_ForallIntro m" for m
        using less.prems(4) flat ll by fastforce
    next
      show "hlJustification l \<noteq> HL_ExistsElim m a c" for m a c
        using less.prems(4) flat ll by fastforce
    qed
    show ?thesis using IH1 IH2 newline flat by auto
  next
    case (HL_DAndE e)
    obtain front k mid c1 where
      em: "hlEmitDerivationFuel fs base env scope first count e = (front,k,mid,c1)"
      by (cases "hlEmitDerivationFuel fs base env scope first count e") auto
    have sz: "size e < size d" using d HL_DAndE by simp
    have eq: "items = front @ [HL_FLine mid phi (HL_FAndE k)] \<and> n = mid"
      using less.prems(2) fuel d HL_DAndE em by (auto simp: Let_def)
    have flat: "hlFlattenFitch items = hlFlattenFitch front @ [(mid,phi,HL_FAndE k)]"
      using eq by (simp add: hlFlattenFitch_append)
    have rec: "hlFitchScopeRecord S items = hlFitchScopeRecord S front @ [(mid,S)]"
      using eq by (simp add: hlFitchScopeRecord_append)
    have IHf: "\<forall>t \<in> set (hlFlattenFitch front).
                 \<forall>l. hlLookupLine Q (fst t) = Some l \<longrightarrow> hlRuleOKG (hlScopeSrc F) Q l"
    proof (rule IH[OF sz em])
      show "hlDerivationOK e" using less.prems(3) d HL_DAndE by simp
      show "hlItemsCtx Q front" using less.prems(4) flat by (simp add: hlFlattenFitch_append)
      show "hlNamesBelow base count e" by (rule NB) (simp_all add: HL_DAndE)
      show "hlScopeBelow base count scope" by (rule less.prems(6))
      show "hlEmitCtx Q env first e"
        using less.prems(7) d HL_DAndE
        by (simp add: hlEmitCtx_def hlDepsCtx_def hlFormCtx_def)
      show "\<forall>t \<in> set (hlFlattenFitch front).
              \<forall>l. hlLookupLine Q (fst t) = Some l \<longrightarrow> hlRuleOK Q l"
        using less.prems(8) flat by auto
      show "\<forall>q \<in> set (hlFitchScopeRecord S front). hlFitchScopeOf F (fst q) = snd q"
        using less.prems(9) rec by auto
      show "hlAssumptionConstants Q S \<subseteq> hlConstantsInScope scope" by (rule less.prems(10))
      show "hlReferencedConstants Q S \<subseteq> hlConstantsInScope scope" by (rule less.prems(11))
      show "\<forall>m \<in> S. m < first" by (rule less.prems(12))
    qed
    have newline: "hlRuleOKG (hlScopeSrc F) Q l" if ll: "hlLookupLine Q mid = Some l" for l
    proof (rule hlRuleOKG_of_hlRuleOK)
      show "hlRuleOK Q l" using less.prems(8) flat ll by auto
    next
      show "hlJustification l \<noteq> HL_ForallIntro m" for m
        using less.prems(4) flat ll by fastforce
    next
      show "hlJustification l \<noteq> HL_ExistsElim m a c" for m a c
        using less.prems(4) flat ll by fastforce
    qed
    show ?thesis using IHf newline flat by auto
  next
    case (HL_DOrI e)
    obtain front k mid c1 where
      em: "hlEmitDerivationFuel fs base env scope first count e = (front,k,mid,c1)"
      by (cases "hlEmitDerivationFuel fs base env scope first count e") auto
    have sz: "size e < size d" using d HL_DOrI by simp
    have eq: "items = front @ [HL_FLine mid phi (HL_FOrI k)] \<and> n = mid"
      using less.prems(2) fuel d HL_DOrI em by (auto simp: Let_def)
    have flat: "hlFlattenFitch items = hlFlattenFitch front @ [(mid,phi,HL_FOrI k)]"
      using eq by (simp add: hlFlattenFitch_append)
    have rec: "hlFitchScopeRecord S items = hlFitchScopeRecord S front @ [(mid,S)]"
      using eq by (simp add: hlFitchScopeRecord_append)
    have IHf: "\<forall>t \<in> set (hlFlattenFitch front).
                 \<forall>l. hlLookupLine Q (fst t) = Some l \<longrightarrow> hlRuleOKG (hlScopeSrc F) Q l"
    proof (rule IH[OF sz em])
      show "hlDerivationOK e" using less.prems(3) d HL_DOrI by simp
      show "hlItemsCtx Q front" using less.prems(4) flat by (simp add: hlFlattenFitch_append)
      show "hlNamesBelow base count e" by (rule NB) (simp_all add: HL_DOrI)
      show "hlScopeBelow base count scope" by (rule less.prems(6))
      show "hlEmitCtx Q env first e"
        using less.prems(7) d HL_DOrI
        by (simp add: hlEmitCtx_def hlDepsCtx_def hlFormCtx_def)
      show "\<forall>t \<in> set (hlFlattenFitch front).
              \<forall>l. hlLookupLine Q (fst t) = Some l \<longrightarrow> hlRuleOK Q l"
        using less.prems(8) flat by auto
      show "\<forall>q \<in> set (hlFitchScopeRecord S front). hlFitchScopeOf F (fst q) = snd q"
        using less.prems(9) rec by auto
      show "hlAssumptionConstants Q S \<subseteq> hlConstantsInScope scope" by (rule less.prems(10))
      show "hlReferencedConstants Q S \<subseteq> hlConstantsInScope scope" by (rule less.prems(11))
      show "\<forall>m \<in> S. m < first" by (rule less.prems(12))
    qed
    have newline: "hlRuleOKG (hlScopeSrc F) Q l" if ll: "hlLookupLine Q mid = Some l" for l
    proof (rule hlRuleOKG_of_hlRuleOK)
      show "hlRuleOK Q l" using less.prems(8) flat ll by auto
    next
      show "hlJustification l \<noteq> HL_ForallIntro m" for m
        using less.prems(4) flat ll by fastforce
    next
      show "hlJustification l \<noteq> HL_ExistsElim m a c" for m a c
        using less.prems(4) flat ll by fastforce
    qed
    show ?thesis using IHf newline flat by auto
  next
    case (HL_DOrE d0 a1 f1 bd1 a2 f2 bd2)
    obtain i0 k0 n0 c0 where
      em0: "hlEmitDerivationFuel fs base env scope first count d0 = (i0,k0,n0,c0)"
      by (cases "hlEmitDerivationFuel fs base env scope first count d0") auto
    obtain u1 l1 m1 c1 where
      em1: "hlEmitDerivationFuel fs base ((a1,n0,f1) # env) (f1 # scope) (n0 + 1) c0 bd1
              = (u1,l1,m1,c1)"
      by (cases "hlEmitDerivationFuel fs base ((a1,n0,f1) # env) (f1 # scope)
                   (n0 + 1) c0 bd1") auto
    define cb1 where "cb1 = (if u1 = [] \<and> l1 \<noteq> n0
                             then [HL_FLine m1 (hlDerivationFormula bd1) (HL_FReit l1)]
                             else u1)"
    define lst1 where "lst1 = (if u1 = [] \<and> l1 \<noteq> n0 then m1 else l1)"
    define af1 where "af1 = (if u1 = [] \<and> l1 \<noteq> n0 then m1 + 1 else m1)"
    obtain u2 l2 m2 c2 where
      em2: "hlEmitDerivationFuel fs base ((a2,af1,f2) # env) (f2 # scope) (af1 + 1) c1 bd2
              = (u2,l2,m2,c2)"
      by (cases "hlEmitDerivationFuel fs base ((a2,af1,f2) # env) (f2 # scope)
                   (af1 + 1) c1 bd2") auto
    define cb2 where "cb2 = (if u2 = [] \<and> l2 \<noteq> af1
                             then [HL_FLine m2 (hlDerivationFormula bd2) (HL_FReit l2)]
                             else u2)"
    define lst2 where "lst2 = (if u2 = [] \<and> l2 \<noteq> af1 then m2 else l2)"
    define aft where "aft = (if u2 = [] \<and> l2 \<noteq> af1 then m2 + 1 else m2)"
    have sz0: "size d0 < size d" and sz1: "size bd1 < size d" and sz2: "size bd2 < size d"
      using d HL_DOrE by simp_all
    have ok0: "hlDerivationOK d0" and ok1: "hlDerivationOK bd1" and ok2: "hlDerivationOK bd2"
      and dis1: "hlDischargeOK a1 f1 bd1" and dis2: "hlDischargeOK a2 f2 bd2"
      using less.prems(3) d HL_DOrE by simp_all
    have eq: "items = i0 @ [HL_FSub (HL_Subproof n0 f1 cb1),
                            HL_FSub (HL_Subproof af1 f2 cb2),
                            HL_FLine aft phi (HL_FOrE k0 (n0,lst1) (af1,lst2))] \<and> n = aft"
      using less.prems(2) fuel d HL_DOrE em0 em1 em2
      by (auto simp: Let_def cb1_def cb2_def lst1_def lst2_def af1_def aft_def)
    have flat: "hlFlattenFitch items = hlFlattenFitch i0 @
      ((n0,f1,HL_FAssume) # hlFlattenFitch cb1) @
      ((af1,f2,HL_FAssume) # hlFlattenFitch cb2) @
      [(aft,phi,HL_FOrE k0 (n0,lst1) (af1,lst2))]"
      using eq by (simp add: hlFlattenFitch_append)
    have rec: "hlFitchScopeRecord S items = hlFitchScopeRecord S i0 @
      ((n0, insert n0 S) # hlFitchScopeRecord (insert n0 S) cb1) @
      ((af1, insert af1 S) # hlFitchScopeRecord (insert af1 S) cb2) @ [(aft,S)]"
      using eq by (simp add: hlFitchScopeRecord_append)
    have ii0: "hlItemsCtx Q i0" and icb1: "hlItemsCtx Q cb1" and icb2: "hlItemsCtx Q cb2"
      using less.prems(4) flat by (simp_all add: hlFlattenFitch_append)
    have iu1: "hlItemsCtx Q u1" by (rule hlItemsCtx_closedBody[OF cb1_def icb1])
    have iu2: "hlItemsCtx Q u2" by (rule hlItemsCtx_closedBody[OF cb2_def icb2])
    have h1in: "(n0,f1,HL_FAssume) \<in> set (hlFlattenFitch items)" using flat by simp
    have h2in: "(af1,f2,HL_FAssume) \<in> set (hlFlattenFitch items)" using flat by simp
    have h1F: "hlLookF Q n0 = Some f1" using less.prems(4) h1in by fastforce
    have h2F: "hlLookF Q af1 = Some f2" using less.prems(4) h2in by fastforce
    obtain la1 where la1: "hlLookupLine Q n0 = Some la1" and la1f: "hlFormula la1 = f1"
      using h1F by (cases "hlLookupLine Q n0") auto
    obtain la2 where la2: "hlLookupLine Q af1 = Some la2" and la2f: "hlFormula la2 = f2"
      using h2F by (cases "hlLookupLine Q af1") auto
    have la1r: "hlReferences la1 = {n0}"
      using less.prems(4) h1in la1 by (fastforce simp: hlFitchDependenciesOf_def)
    have la2r: "hlReferences la2 = {af1}"
      using less.prems(4) h2in la2 by (fastforce simp: hlFitchDependenciesOf_def)
    have below: "hlEnvBelow env first"
      using less.prems(7) by (simp add: hlEmitCtx_def hlDepsCtx_def)
    have le0: "first \<le> n0" by (rule hlEmitDerivationFuel_start_le[OF em0])
    have below0: "hlEnvBelow env n0" by (rule hlEnvBelow_mono[OF below le0])
    have le1: "n0 + 1 \<le> m1" by (rule hlEmitDerivationFuel_start_le[OF em1])
    have below1: "hlEnvBelow env af1"
      by (rule hlEnvBelow_mono[OF below0]) (use le1 in \<open>simp add: af1_def\<close>)
    have ltaf1: "n0 < af1" using le1 by (simp add: af1_def)
    have lec0: "count \<le> c0" by (rule hlEmitDerivationFuel_count_le[OF em0])
    have lec1: "count \<le> c1"
      using lec0 hlEmitDerivationFuel_count_le[OF em1] by simp
    have ctx0: "hlEmitCtx Q env first d0"
      using less.prems(7) d HL_DOrE
      unfolding hlEmitCtx_def hlDepsCtx_def hlFormCtx_def by fastforce
    have cov1: "\<forall>nf \<in> set (hlOpenAssumptions bd1).
        fst nf \<noteq> a1 \<longrightarrow> nf \<in> set (hlOpenAssumptions d)"
      and cov2: "\<forall>nf \<in> set (hlOpenAssumptions bd2).
        fst nf \<noteq> a2 \<longrightarrow> nf \<in> set (hlOpenAssumptions d)"
      using d HL_DOrE by simp_all
    have ctxb1: "hlEmitCtx Q ((a1,n0,f1) # env) (n0 + 1) bd1"
      unfolding hlEmitCtx_def hlDepsCtx_def hlFormCtx_def
    proof (intro conjI ballI)
      show "hlEnvBelow ((a1,n0,f1) # env) (n0 + 1)"
        by (rule hlEnvBelow_Cons[OF below0]) auto
    next
      fix nf assume nf: "nf \<in> set (hlOpenAssumptions bd1)"
      show "fst nf \<in> fst ` set ((a1,n0,f1) # env)"
        using nf cov1 less.prems(7)
        by (cases "fst nf = a1") (auto simp: hlEmitCtx_def hlDepsCtx_def)
    next
      fix nf assume nf: "nf \<in> set (hlOpenAssumptions bd1)"
      show "hlRefsF Q (hlEnvironmentLine ((a1,n0,f1) # env) (fst nf)) =
            {hlEnvironmentLine ((a1,n0,f1) # env) (fst nf)}"
      proof (cases "fst nf = a1")
        case True
        then show ?thesis using la1 la1r by simp
      next
        case False
        then have "nf \<in> set (hlOpenAssumptions d)" using nf cov1 by blast
        then show ?thesis using less.prems(7) False
          unfolding hlEmitCtx_def hlDepsCtx_def by fastforce
      qed
    next
      fix nf assume nf: "nf \<in> set (hlOpenAssumptions bd1)"
      show "hlLookF Q (hlEnvironmentLine ((a1,n0,f1) # env) (fst nf)) = Some (snd nf)"
      proof (cases "fst nf = a1")
        case True
        then have "snd nf = f1" using dis1 nf by (simp add: hlDischargeOK_def)
        then show ?thesis using True h1F by simp
      next
        case False
        then have "nf \<in> set (hlOpenAssumptions d)" using nf cov1 by blast
        then show ?thesis using less.prems(7) False
          unfolding hlEmitCtx_def hlFormCtx_def by fastforce
      qed
    qed
    have ctxb2: "hlEmitCtx Q ((a2,af1,f2) # env) (af1 + 1) bd2"
      unfolding hlEmitCtx_def hlDepsCtx_def hlFormCtx_def
    proof (intro conjI ballI)
      show "hlEnvBelow ((a2,af1,f2) # env) (af1 + 1)"
        by (rule hlEnvBelow_Cons[OF below1]) auto
    next
      fix nf assume nf: "nf \<in> set (hlOpenAssumptions bd2)"
      show "fst nf \<in> fst ` set ((a2,af1,f2) # env)"
        using nf cov2 less.prems(7)
        by (cases "fst nf = a2") (auto simp: hlEmitCtx_def hlDepsCtx_def)
    next
      fix nf assume nf: "nf \<in> set (hlOpenAssumptions bd2)"
      show "hlRefsF Q (hlEnvironmentLine ((a2,af1,f2) # env) (fst nf)) =
            {hlEnvironmentLine ((a2,af1,f2) # env) (fst nf)}"
      proof (cases "fst nf = a2")
        case True
        then show ?thesis using la2 la2r by simp
      next
        case False
        then have "nf \<in> set (hlOpenAssumptions d)" using nf cov2 by blast
        then show ?thesis using less.prems(7) False
          unfolding hlEmitCtx_def hlDepsCtx_def by fastforce
      qed
    next
      fix nf assume nf: "nf \<in> set (hlOpenAssumptions bd2)"
      show "hlLookF Q (hlEnvironmentLine ((a2,af1,f2) # env) (fst nf)) = Some (snd nf)"
      proof (cases "fst nf = a2")
        case True
        then have "snd nf = f2" using dis2 nf by (simp add: hlDischargeOK_def)
        then show ?thesis using True h2F by simp
      next
        case False
        then have "nf \<in> set (hlOpenAssumptions d)" using nf cov2 by blast
        then show ?thesis using less.prems(7) False
          unfolding hlEmitCtx_def hlFormCtx_def by fastforce
      qed
    qed
    have f1form: "\<forall>c \<in> hlConstantsInFormula f1. nlen c < base + count"
      and f2form: "\<forall>c \<in> hlConstantsInFormula f2. nlen c < base + count"
      using less.prems(5) d HL_DOrE
      by (auto simp: hlNamesBelow_def hlDerivationConstants_def)
    have IH0: "\<forall>t \<in> set (hlFlattenFitch i0).
                 \<forall>l. hlLookupLine Q (fst t) = Some l \<longrightarrow> hlRuleOKG (hlScopeSrc F) Q l"
    proof (rule IH[OF sz0 em0])
      show "hlDerivationOK d0" by (rule ok0)
      show "hlItemsCtx Q i0" by (rule ii0)
      show "hlNamesBelow base count d0" by (rule NB) (simp_all add: HL_DOrE)
      show "hlScopeBelow base count scope" by (rule less.prems(6))
      show "hlEmitCtx Q env first d0" by (rule ctx0)
      show "\<forall>t \<in> set (hlFlattenFitch i0).
              \<forall>l. hlLookupLine Q (fst t) = Some l \<longrightarrow> hlRuleOK Q l"
        using less.prems(8) flat by (auto simp: hlFlattenFitch_append)
      show "\<forall>q \<in> set (hlFitchScopeRecord S i0). hlFitchScopeOf F (fst q) = snd q"
        using less.prems(9) rec by auto
      show "hlAssumptionConstants Q S \<subseteq> hlConstantsInScope scope" by (rule less.prems(10))
      show "hlReferencedConstants Q S \<subseteq> hlConstantsInScope scope" by (rule less.prems(11))
      show "\<forall>m \<in> S. m < first" by (rule less.prems(12))
    qed
    have subrec1: "set (hlFitchScopeRecord (insert n0 S) u1) \<subseteq>
                   set (hlFitchScopeRecord (insert n0 S) cb1)"
      and subflat1: "set (hlFlattenFitch u1) \<subseteq> set (hlFlattenFitch cb1)"
      by (cases "u1 = [] \<and> l1 \<noteq> n0"; simp add: cb1_def)+
    have subrec2: "set (hlFitchScopeRecord (insert af1 S) u2) \<subseteq>
                   set (hlFitchScopeRecord (insert af1 S) cb2)"
      and subflat2: "set (hlFlattenFitch u2) \<subseteq> set (hlFlattenFitch cb2)"
      by (cases "u2 = [] \<and> l2 \<noteq> af1"; simp add: cb2_def)+
    have IH1: "\<forall>t \<in> set (hlFlattenFitch u1).
                 \<forall>l. hlLookupLine Q (fst t) = Some l \<longrightarrow> hlRuleOKG (hlScopeSrc F) Q l"
    proof (rule IH[OF sz1 em1])
      show "hlDerivationOK bd1" by (rule ok1)
      show "hlItemsCtx Q u1" by (rule iu1)
      show "hlNamesBelow base c0 bd1" by (rule NB) (use HL_DOrE lec0 in simp_all)
      show "hlScopeBelow base c0 (f1 # scope)"
        by (rule hlScopeBelow_Cons[OF hlScopeBelow_mono[OF less.prems(6) lec0]])
           (use f1form lec0 in fastforce)
      show "hlEmitCtx Q ((a1,n0,f1) # env) (n0 + 1) bd1" by (rule ctxb1)
      show "\<forall>t \<in> set (hlFlattenFitch u1).
              \<forall>l. hlLookupLine Q (fst t) = Some l \<longrightarrow> hlRuleOK Q l"
        using less.prems(8) flat subflat1 by (auto simp: hlFlattenFitch_append)
      show "\<forall>q \<in> set (hlFitchScopeRecord (insert n0 S) u1).
              hlFitchScopeOf F (fst q) = snd q"
        using less.prems(9) rec subrec1 by auto
      show "hlAssumptionConstants Q (insert n0 S) \<subseteq> hlConstantsInScope (f1 # scope)"
        using hlAssumptionConstants_insert[OF less.prems(13) la1] less.prems(10) la1f
        by (auto simp: hlConstantsInScope_def)
      show "hlReferencedConstants Q (insert n0 S) \<subseteq> hlConstantsInScope (f1 # scope)"
        using hlReferencedConstants_insert[OF less.prems(13) la1] less.prems(11) la1f
        by (auto simp: hlConstantsInScope_def)
      show "\<forall>m \<in> insert n0 S. m < n0 + 1" using less.prems(12) le0 by auto
    qed
    have IH2: "\<forall>t \<in> set (hlFlattenFitch u2).
                 \<forall>l. hlLookupLine Q (fst t) = Some l \<longrightarrow> hlRuleOKG (hlScopeSrc F) Q l"
    proof (rule IH[OF sz2 em2])
      show "hlDerivationOK bd2" by (rule ok2)
      show "hlItemsCtx Q u2" by (rule iu2)
      show "hlNamesBelow base c1 bd2" by (rule NB) (use HL_DOrE lec1 in simp_all)
      show "hlScopeBelow base c1 (f2 # scope)"
        by (rule hlScopeBelow_Cons[OF hlScopeBelow_mono[OF less.prems(6) lec1]])
           (use f2form lec1 in fastforce)
      show "hlEmitCtx Q ((a2,af1,f2) # env) (af1 + 1) bd2" by (rule ctxb2)
      show "\<forall>t \<in> set (hlFlattenFitch u2).
              \<forall>l. hlLookupLine Q (fst t) = Some l \<longrightarrow> hlRuleOK Q l"
        using less.prems(8) flat subflat2 by (auto simp: hlFlattenFitch_append)
      show "\<forall>q \<in> set (hlFitchScopeRecord (insert af1 S) u2).
              hlFitchScopeOf F (fst q) = snd q"
        using less.prems(9) rec subrec2 by auto
      show "hlAssumptionConstants Q (insert af1 S) \<subseteq> hlConstantsInScope (f2 # scope)"
        using hlAssumptionConstants_insert[OF less.prems(13) la2] less.prems(10) la2f
        by (auto simp: hlConstantsInScope_def)
      show "hlReferencedConstants Q (insert af1 S) \<subseteq> hlConstantsInScope (f2 # scope)"
        using hlReferencedConstants_insert[OF less.prems(13) la2] less.prems(11) la2f
        by (auto simp: hlConstantsInScope_def)
      show "\<forall>m \<in> insert af1 S. m < af1 + 1"
        using less.prems(12) le0 ltaf1 by auto
    qed
    have cb1OK: "\<forall>t \<in> set (hlFlattenFitch cb1).
                   \<forall>l. hlLookupLine Q (fst t) = Some l \<longrightarrow> hlRuleOKG (hlScopeSrc F) Q l"
    proof (cases "u1 = [] \<and> l1 \<noteq> n0")
      case False
      then have "cb1 = u1" using cb1_def by simp
      then show ?thesis using IH1 by simp
    next
      case True
      then have cbv: "cb1 = [HL_FLine m1 (hlDerivationFormula bd1) (HL_FReit l1)]"
        using cb1_def by simp
      have "hlRuleOKG (hlScopeSrc F) Q l" if ll: "hlLookupLine Q m1 = Some l" for l
      proof (rule hlRuleOKG_of_hlRuleOK)
        show "hlRuleOK Q l" using less.prems(8) flat cbv ll by auto
      next
        show "hlJustification l \<noteq> HL_ForallIntro m" for m
          using less.prems(4) flat cbv ll by fastforce
      next
        show "hlJustification l \<noteq> HL_ExistsElim m a' c" for m a' c
          using less.prems(4) flat cbv ll by fastforce
      qed
      then show ?thesis using cbv by simp
    qed
    have cb2OK: "\<forall>t \<in> set (hlFlattenFitch cb2).
                   \<forall>l. hlLookupLine Q (fst t) = Some l \<longrightarrow> hlRuleOKG (hlScopeSrc F) Q l"
    proof (cases "u2 = [] \<and> l2 \<noteq> af1")
      case False
      then have "cb2 = u2" using cb2_def by simp
      then show ?thesis using IH2 by simp
    next
      case True
      then have cbv: "cb2 = [HL_FLine m2 (hlDerivationFormula bd2) (HL_FReit l2)]"
        using cb2_def by simp
      have "hlRuleOKG (hlScopeSrc F) Q l" if ll: "hlLookupLine Q m2 = Some l" for l
      proof (rule hlRuleOKG_of_hlRuleOK)
        show "hlRuleOK Q l" using less.prems(8) flat cbv ll by auto
      next
        show "hlJustification l \<noteq> HL_ForallIntro m" for m
          using less.prems(4) flat cbv ll by fastforce
      next
        show "hlJustification l \<noteq> HL_ExistsElim m a' c" for m a' c
          using less.prems(4) flat cbv ll by fastforce
      qed
      then show ?thesis using cbv by simp
    qed
    have h1OK: "hlRuleOKG (hlScopeSrc F) Q l" if ll: "hlLookupLine Q n0 = Some l" for l
    proof (rule hlRuleOKG_of_hlRuleOK)
      show "hlRuleOK Q l" using less.prems(8) h1in ll by auto
    next
      show "hlJustification l \<noteq> HL_ForallIntro m" for m
        using less.prems(4) h1in ll by fastforce
    next
      show "hlJustification l \<noteq> HL_ExistsElim m a' c" for m a' c
        using less.prems(4) h1in ll by fastforce
    qed
    have h2OK: "hlRuleOKG (hlScopeSrc F) Q l" if ll: "hlLookupLine Q af1 = Some l" for l
    proof (rule hlRuleOKG_of_hlRuleOK)
      show "hlRuleOK Q l" using less.prems(8) h2in ll by auto
    next
      show "hlJustification l \<noteq> HL_ForallIntro m" for m
        using less.prems(4) h2in ll by fastforce
    next
      show "hlJustification l \<noteq> HL_ExistsElim m a' c" for m a' c
        using less.prems(4) h2in ll by fastforce
    qed
    have newline: "hlRuleOKG (hlScopeSrc F) Q l" if ll: "hlLookupLine Q aft = Some l" for l
    proof (rule hlRuleOKG_of_hlRuleOK)
      show "hlRuleOK Q l" using less.prems(8) flat ll by auto
    next
      show "hlJustification l \<noteq> HL_ForallIntro m" for m
        using less.prems(4) flat ll by fastforce
    next
      show "hlJustification l \<noteq> HL_ExistsElim m a' c" for m a' c
        using less.prems(4) flat ll by fastforce
    qed
    show ?thesis
      using IH0 h1OK cb1OK h2OK cb2OK newline la1 la2 flat by auto
  next
    case (HL_DRAA a p body)
    obtain bi bl n1 c1 where
      em: "hlEmitDerivationFuel fs base ((a,first,p) # env) (p # scope) (first + 1) count body
             = (bi,bl,n1,c1)"
      by (cases "hlEmitDerivationFuel fs base ((a,first,p) # env) (p # scope)
                   (first + 1) count body") auto
    define cb where "cb = (if bi = [] \<and> bl \<noteq> first
                           then [HL_FLine n1 (hlDerivationFormula body) (HL_FReit bl)]
                           else bi)"
    define lst where "lst = (if bi = [] \<and> bl \<noteq> first then n1 else bl)"
    define aft where "aft = (if bi = [] \<and> bl \<noteq> first then n1 + 1 else n1)"
    have sz: "size body < size d" using d HL_DRAA by simp
    have okb: "hlDerivationOK body" using less.prems(3) d HL_DRAA by simp
    have dis: "hlDischargeOK a p body" using less.prems(3) d HL_DRAA by simp
    have eq: "items = [HL_FSub (HL_Subproof first p cb),
                       HL_FLine aft phi (HL_FRAA (first,lst))] \<and> n = aft"
      using less.prems(2) fuel d HL_DRAA em
      by (auto simp: Let_def cb_def lst_def aft_def)
    have flat: "hlFlattenFitch items =
      (first,p,HL_FAssume) # hlFlattenFitch cb @ [(aft,phi,HL_FRAA (first,lst))]"
      using eq by simp
    have rec: "hlFitchScopeRecord S items =
      (first, insert first S) # hlFitchScopeRecord (insert first S) cb @ [(aft,S)]"
      using eq by (simp add: hlFitchScopeRecord_append)
    have headin: "(first,p,HL_FAssume) \<in> set (hlFlattenFitch items)" using flat by simp
    have headF: "hlLookF Q first = Some p" using less.prems(4) headin by fastforce
    obtain la where la: "hlLookupLine Q first = Some la" and laf: "hlFormula la = p"
      using headF by (cases "hlLookupLine Q first") auto
    have laref: "hlReferences la = {first}"
      using less.prems(4) headin la by (fastforce simp: hlFitchDependenciesOf_def)
    have below: "hlEnvBelow env first"
      using less.prems(7) by (simp add: hlEmitCtx_def hlDepsCtx_def)
    have covered: "\<forall>nf \<in> set (hlOpenAssumptions body).
        fst nf \<noteq> a \<longrightarrow> nf \<in> set (hlOpenAssumptions d)"
      using d HL_DRAA by simp
    have ctxb: "hlEmitCtx Q ((a,first,p) # env) (first + 1) body"
      unfolding hlEmitCtx_def hlDepsCtx_def hlFormCtx_def
    proof (intro conjI ballI)
      show "hlEnvBelow ((a,first,p) # env) (first + 1)"
        by (rule hlEnvBelow_Cons[OF below]) auto
    next
      fix nf assume nf: "nf \<in> set (hlOpenAssumptions body)"
      show "fst nf \<in> fst ` set ((a,first,p) # env)"
        using nf covered less.prems(7)
        by (cases "fst nf = a") (auto simp: hlEmitCtx_def hlDepsCtx_def)
    next
      fix nf assume nf: "nf \<in> set (hlOpenAssumptions body)"
      show "hlRefsF Q (hlEnvironmentLine ((a,first,p) # env) (fst nf)) =
            {hlEnvironmentLine ((a,first,p) # env) (fst nf)}"
      proof (cases "fst nf = a")
        case True
        then show ?thesis using la laref by simp
      next
        case False
        then have "nf \<in> set (hlOpenAssumptions d)" using nf covered by blast
        then show ?thesis using less.prems(7) False
          unfolding hlEmitCtx_def hlDepsCtx_def by fastforce
      qed
    next
      fix nf assume nf: "nf \<in> set (hlOpenAssumptions body)"
      show "hlLookF Q (hlEnvironmentLine ((a,first,p) # env) (fst nf)) = Some (snd nf)"
      proof (cases "fst nf = a")
        case True
        then have "snd nf = p" using dis nf by (simp add: hlDischargeOK_def)
        then show ?thesis using True headF by simp
      next
        case False
        then have "nf \<in> set (hlOpenAssumptions d)" using nf covered by blast
        then show ?thesis using less.prems(7) False
          unfolding hlEmitCtx_def hlFormCtx_def by fastforce
      qed
    qed
    have icb: "hlItemsCtx Q cb"
      using less.prems(4) flat by (simp add: hlFlattenFitch_append)
    have pform: "\<forall>c \<in> hlConstantsInFormula p. nlen c < base + count"
      using less.prems(5) d HL_DRAA
      by (auto simp: hlNamesBelow_def hlDerivationConstants_def)
    have ibi: "hlItemsCtx Q bi" by (rule hlItemsCtx_closedBody[OF cb_def icb])
    have subrec: "set (hlFitchScopeRecord (insert first S) bi) \<subseteq>
                  set (hlFitchScopeRecord (insert first S) cb)"
      by (cases "bi = [] \<and> bl \<noteq> first") (simp_all add: cb_def)
    have subflat: "set (hlFlattenFitch bi) \<subseteq> set (hlFlattenFitch cb)"
      by (cases "bi = [] \<and> bl \<noteq> first") (simp_all add: cb_def)
    have IHb: "\<forall>t \<in> set (hlFlattenFitch bi).
                 \<forall>l. hlLookupLine Q (fst t) = Some l \<longrightarrow> hlRuleOKG (hlScopeSrc F) Q l"
    proof (rule IH[OF sz em])
      show "hlDerivationOK body" by (rule okb)
      show "hlItemsCtx Q bi" by (rule ibi)
      show "hlNamesBelow base count body" by (rule NB) (simp_all add: HL_DRAA)
      show "hlScopeBelow base count (p # scope)"
        by (rule hlScopeBelow_Cons[OF less.prems(6) pform])
      show "hlEmitCtx Q ((a,first,p) # env) (first + 1) body" by (rule ctxb)
      show "\<forall>t \<in> set (hlFlattenFitch bi).
              \<forall>l. hlLookupLine Q (fst t) = Some l \<longrightarrow> hlRuleOK Q l"
        using less.prems(8) flat subflat by (auto simp: hlFlattenFitch_append)
      show "\<forall>q \<in> set (hlFitchScopeRecord (insert first S) bi).
              hlFitchScopeOf F (fst q) = snd q"
        using less.prems(9) rec subrec by auto
      show "hlAssumptionConstants Q (insert first S) \<subseteq> hlConstantsInScope (p # scope)"
        using hlAssumptionConstants_insert[OF less.prems(13) la] less.prems(10) laf
        by (auto simp: hlConstantsInScope_def)
      show "hlReferencedConstants Q (insert first S) \<subseteq> hlConstantsInScope (p # scope)"
        using hlReferencedConstants_insert[OF less.prems(13) la] less.prems(11) laf
        by (auto simp: hlConstantsInScope_def)
      show "\<forall>m \<in> insert first S. m < first + 1" using less.prems(12) by auto
    qed
    have cbOK: "\<forall>t \<in> set (hlFlattenFitch cb).
                  \<forall>l. hlLookupLine Q (fst t) = Some l \<longrightarrow> hlRuleOKG (hlScopeSrc F) Q l"
    proof (cases "bi = [] \<and> bl \<noteq> first")
      case False
      then have "cb = bi" using cb_def by simp
      then show ?thesis using IHb by simp
    next
      case True
      then have cbv: "cb = [HL_FLine n1 (hlDerivationFormula body) (HL_FReit bl)]"
        using cb_def by simp
      have "hlRuleOKG (hlScopeSrc F) Q l" if ll: "hlLookupLine Q n1 = Some l" for l
      proof (rule hlRuleOKG_of_hlRuleOK)
        show "hlRuleOK Q l" using less.prems(8) flat cbv ll by auto
      next
        show "hlJustification l \<noteq> HL_ForallIntro m" for m
          using less.prems(4) flat cbv ll by fastforce
      next
        show "hlJustification l \<noteq> HL_ExistsElim m a' c" for m a' c
          using less.prems(4) flat cbv ll by fastforce
      qed
      then show ?thesis using cbv by simp
    qed
    have headOK: "hlRuleOKG (hlScopeSrc F) Q l" if ll: "hlLookupLine Q first = Some l" for l
    proof (rule hlRuleOKG_of_hlRuleOK)
      show "hlRuleOK Q l" using less.prems(8) headin ll by auto
    next
      show "hlJustification l \<noteq> HL_ForallIntro m" for m
        using less.prems(4) headin ll by fastforce
    next
      show "hlJustification l \<noteq> HL_ExistsElim m a' c" for m a' c
        using less.prems(4) headin ll by fastforce
    qed
    have newline: "hlRuleOKG (hlScopeSrc F) Q l" if ll: "hlLookupLine Q aft = Some l" for l
    proof (rule hlRuleOKG_of_hlRuleOK)
      show "hlRuleOK Q l" using less.prems(8) flat ll by auto
    next
      show "hlJustification l \<noteq> HL_ForallIntro m" for m
        using less.prems(4) flat ll by fastforce
    next
      show "hlJustification l \<noteq> HL_ExistsElim m a' c" for m a' c
        using less.prems(4) flat ll by fastforce
    qed
    show ?thesis using cbOK headOK newline la flat by auto
  next
    case (HL_DForallE e)
    obtain front k mid c1 where
      em: "hlEmitDerivationFuel fs base env scope first count e = (front,k,mid,c1)"
      by (cases "hlEmitDerivationFuel fs base env scope first count e") auto
    have sz: "size e < size d" using d HL_DForallE by simp
    have eq: "items = front @ [HL_FLine mid phi (HL_FForallE k)] \<and> n = mid"
      using less.prems(2) fuel d HL_DForallE em by (auto simp: Let_def)
    have flat: "hlFlattenFitch items = hlFlattenFitch front @ [(mid,phi,HL_FForallE k)]"
      using eq by (simp add: hlFlattenFitch_append)
    have rec: "hlFitchScopeRecord S items = hlFitchScopeRecord S front @ [(mid,S)]"
      using eq by (simp add: hlFitchScopeRecord_append)
    have IHf: "\<forall>t \<in> set (hlFlattenFitch front).
                 \<forall>l. hlLookupLine Q (fst t) = Some l \<longrightarrow> hlRuleOKG (hlScopeSrc F) Q l"
    proof (rule IH[OF sz em])
      show "hlDerivationOK e" using less.prems(3) d HL_DForallE by simp
      show "hlItemsCtx Q front" using less.prems(4) flat by (simp add: hlFlattenFitch_append)
      show "hlNamesBelow base count e" by (rule NB) (simp_all add: HL_DForallE)
      show "hlScopeBelow base count scope" by (rule less.prems(6))
      show "hlEmitCtx Q env first e"
        using less.prems(7) d HL_DForallE
        by (simp add: hlEmitCtx_def hlDepsCtx_def hlFormCtx_def)
      show "\<forall>t \<in> set (hlFlattenFitch front).
              \<forall>l. hlLookupLine Q (fst t) = Some l \<longrightarrow> hlRuleOK Q l"
        using less.prems(8) flat by auto
      show "\<forall>q \<in> set (hlFitchScopeRecord S front). hlFitchScopeOf F (fst q) = snd q"
        using less.prems(9) rec by auto
      show "hlAssumptionConstants Q S \<subseteq> hlConstantsInScope scope" by (rule less.prems(10))
      show "hlReferencedConstants Q S \<subseteq> hlConstantsInScope scope" by (rule less.prems(11))
      show "\<forall>m \<in> S. m < first" by (rule less.prems(12))
    qed
    have newline: "hlRuleOKG (hlScopeSrc F) Q l" if ll: "hlLookupLine Q mid = Some l" for l
    proof (rule hlRuleOKG_of_hlRuleOK)
      show "hlRuleOK Q l" using less.prems(8) flat ll by auto
    next
      show "hlJustification l \<noteq> HL_ForallIntro m" for m
        using less.prems(4) flat ll by fastforce
    next
      show "hlJustification l \<noteq> HL_ExistsElim m a c" for m a c
        using less.prems(4) flat ll by fastforce
    qed
    show ?thesis using IHf newline flat by auto
  next
    case (HL_DForallI e)
    obtain c0 prs rep where
      rp: "hlRepairDerivation base count (hlForallRepairConstants scope phi e) e
             = (c0,prs,rep)"
      by (cases "hlRepairDerivation base count (hlForallRepairConstants scope phi e) e")
         auto
    obtain front k mid c1 where
      em: "hlEmitDerivationFuel fs base env scope first c0 rep = (front,k,mid,c1)"
      by (cases "hlEmitDerivationFuel fs base env scope first c0 rep") auto
    have sz: "size rep < size d"
      using d HL_DForallI hlRepairDerivation_size[OF rp] by simp
    have okd: "hlDerivationOK (HL_Derivation phi (HL_DForallI e))"
      using less.prems(3) d HL_DForallI by simp
    have nbd: "hlNamesBelow base count (HL_Derivation phi (HL_DForallI e))"
      using less.prems(5) d HL_DForallI by simp
    have nbe: "hlNamesBelow base count e" by (rule NB) (simp_all add: HL_DForallI)
    have fresh: "\<forall>old \<in> set (hlForallRepairConstants scope phi e).
        old \<notin> hlConstantsInScope (hlOpenFormulas e) \<and> old \<noteq> STR ''''"
      by (rule hlForallRepair_fresh[OF okd])
    have nophi: "\<forall>old \<in> set (hlForallRepairConstants scope phi e).
        old \<notin> hlConstantsInFormula phi"
      by (simp add: set_hlForallRepairConstants)
    have rpD: "hlRepairDerivation base count (hlForallRepairConstants scope phi e)
                 (HL_Derivation phi (HL_DForallI e))
               = (c0,prs,HL_Derivation phi (HL_DForallI rep))"
      by (rule hlRepairDerivation_ForallI[OF nophi rp])
    have okD: "hlDerivationOK (HL_Derivation phi (HL_DForallI rep))"
      by (rule hlDerivationOK_repair[OF rpD okd nbd less.prems(14)]) (use fresh in blast)
    have okrep: "hlDerivationOK rep" using okD by simp
    have same: "hlOpenAssumptions rep = hlOpenAssumptions e"
      by (rule hlOpenAssumptions_repair_unchanged[OF rp]) (use fresh in blast)
    have lec: "count \<le> c0" by (rule hlRepairDerivation_count_le[OF rp])
    have nbrep: "hlNamesBelow base c0 rep" by (rule hlNamesBelow_repair[OF rp nbe])
    have eq: "items = front @ [HL_FLine mid phi (HL_FForallI k)] \<and> n = mid"
      using less.prems(2) fuel d HL_DForallI rp em by (auto simp: Let_def)
    have flat: "hlFlattenFitch items = hlFlattenFitch front @ [(mid,phi,HL_FForallI k)]"
      using eq by (simp add: hlFlattenFitch_append)
    have rec: "hlFitchScopeRecord S items = hlFitchScopeRecord S front @ [(mid,S)]"
      using eq by (simp add: hlFitchScopeRecord_append)
    have ifront: "hlItemsCtx Q front"
      using less.prems(4) flat by (simp add: hlFlattenFitch_append)
    have ctxe: "hlEmitCtx Q env first rep"
      using less.prems(7) d HL_DForallI same
      by (simp add: hlEmitCtx_def hlDepsCtx_def hlFormCtx_def)
    have IHf: "\<forall>t \<in> set (hlFlattenFitch front).
                 \<forall>l. hlLookupLine Q (fst t) = Some l \<longrightarrow> hlRuleOKG (hlScopeSrc F) Q l"
    proof (rule IH[OF sz em])
      show "hlDerivationOK rep" by (rule okrep)
      show "hlItemsCtx Q front" by (rule ifront)
      show "hlNamesBelow base c0 rep" by (rule nbrep)
      show "hlScopeBelow base c0 scope" by (rule hlScopeBelow_mono[OF less.prems(6) lec])
      show "hlEmitCtx Q env first rep" by (rule ctxe)
      show "\<forall>t \<in> set (hlFlattenFitch front).
              \<forall>l. hlLookupLine Q (fst t) = Some l \<longrightarrow> hlRuleOK Q l"
        using less.prems(8) flat by auto
      show "\<forall>q \<in> set (hlFitchScopeRecord S front). hlFitchScopeOf F (fst q) = snd q"
        using less.prems(9) rec by auto
      show "hlAssumptionConstants Q S \<subseteq> hlConstantsInScope scope" by (rule less.prems(10))
      show "hlReferencedConstants Q S \<subseteq> hlConstantsInScope scope" by (rule less.prems(11))
      show "\<forall>m \<in> S. m < first" by (rule less.prems(12))
    qed
    have kf: "hlLookF Q k = Some (hlDerivationFormula rep)"
    proof (rule hlEmitDerivationFuel_returns_formula[OF em small[OF sz]])
      show "\<forall>nf \<in> set (hlOpenAssumptions rep).
              hlLookF Q (hlEnvironmentLine env (fst nf)) = Some (snd nf)"
        using ctxe by (simp add: hlEmitCtx_def hlFormCtx_def)
    next
      show "\<forall>t \<in> set (hlFlattenFitch front). hlLookF Q (fst t) = Some (fst (snd t))"
        using ifront by simp
    qed
    obtain lm where lm: "hlLookupLine Q k = Some lm"
      and lmf: "hlFormula lm = hlDerivationFormula rep"
      using kf by (cases "hlLookupLine Q k") auto
    have newline: "hlRuleOKG (hlScopeSrc F) Q l" if ll: "hlLookupLine Q mid = Some l" for l
    proof -
      have tin: "(mid,phi,HL_FForallI k) \<in> set (hlFlattenFitch items)" using flat by simp
      have fl: "hlFormula l = phi" using less.prems(4) tin ll by fastforce
      have jl: "hlJustification l = HL_ForallIntro k"
        using less.prems(4) tin ll by fastforce
      have rl: "hlReferences l = hlReferences lm"
        using less.prems(4) tin ll lm by (fastforce simp: hlFitchDependenciesOf_def)
      have okl: "hlRuleOK Q l" using less.prems(8) flat ll by auto
      have disj: "(hlConstantsInFormula (hlFormula lm) -
                   hlConstantsInFormula (hlFormula l)) \<inter> hlConstantsInScope scope = {}"
        using hlForallRepair_disjoint[OF rp less.prems(6) nbe] lmf fl by simp
      have step: "hlForallIntroStep (hlFormula lm) (hlFormula l) scope"
        by (rule hlRuleOK_ForallIntro_scope[OF okl jl lm disj])
      have num: "hlLineNumber l = mid" by (rule hlLookupLine_number[OF ll])
      have scopeat: "hlFitchScopeOf F mid = S" using less.prems(9) rec by auto
      show ?thesis
      proof (rule hlRuleOKG_ForallIntro[OF jl lm step _ rl])
        show "hlAssumptionConstants Q
                (hlScopeSrc F Q (hlLineNumber l) (hlReferences lm)) \<subseteq>
              hlConstantsInScope scope"
          using scopeat num less.prems(10) by (simp add: hlScopeSrc_def)
      qed
    qed
    show ?thesis using IHf newline flat by auto
  next
    case (HL_DExistsI e)
    obtain front k mid c1 where
      em: "hlEmitDerivationFuel fs base env scope first count e = (front,k,mid,c1)"
      by (cases "hlEmitDerivationFuel fs base env scope first count e") auto
    have sz: "size e < size d" using d HL_DExistsI by simp
    have eq: "items = front @ [HL_FLine mid phi (HL_FExistsI k)] \<and> n = mid"
      using less.prems(2) fuel d HL_DExistsI em by (auto simp: Let_def)
    have flat: "hlFlattenFitch items = hlFlattenFitch front @ [(mid,phi,HL_FExistsI k)]"
      using eq by (simp add: hlFlattenFitch_append)
    have rec: "hlFitchScopeRecord S items = hlFitchScopeRecord S front @ [(mid,S)]"
      using eq by (simp add: hlFitchScopeRecord_append)
    have IHf: "\<forall>t \<in> set (hlFlattenFitch front).
                 \<forall>l. hlLookupLine Q (fst t) = Some l \<longrightarrow> hlRuleOKG (hlScopeSrc F) Q l"
    proof (rule IH[OF sz em])
      show "hlDerivationOK e" using less.prems(3) d HL_DExistsI by simp
      show "hlItemsCtx Q front" using less.prems(4) flat by (simp add: hlFlattenFitch_append)
      show "hlNamesBelow base count e" by (rule NB) (simp_all add: HL_DExistsI)
      show "hlScopeBelow base count scope" by (rule less.prems(6))
      show "hlEmitCtx Q env first e"
        using less.prems(7) d HL_DExistsI
        by (simp add: hlEmitCtx_def hlDepsCtx_def hlFormCtx_def)
      show "\<forall>t \<in> set (hlFlattenFitch front).
              \<forall>l. hlLookupLine Q (fst t) = Some l \<longrightarrow> hlRuleOK Q l"
        using less.prems(8) flat by auto
      show "\<forall>q \<in> set (hlFitchScopeRecord S front). hlFitchScopeOf F (fst q) = snd q"
        using less.prems(9) rec by auto
      show "hlAssumptionConstants Q S \<subseteq> hlConstantsInScope scope" by (rule less.prems(10))
      show "hlReferencedConstants Q S \<subseteq> hlConstantsInScope scope" by (rule less.prems(11))
      show "\<forall>m \<in> S. m < first" by (rule less.prems(12))
    qed
    have newline: "hlRuleOKG (hlScopeSrc F) Q l" if ll: "hlLookupLine Q mid = Some l" for l
    proof (rule hlRuleOKG_of_hlRuleOK)
      show "hlRuleOK Q l" using less.prems(8) flat ll by auto
    next
      show "hlJustification l \<noteq> HL_ForallIntro m" for m
        using less.prems(4) flat ll by fastforce
    next
      show "hlJustification l \<noteq> HL_ExistsElim m a c" for m a c
        using less.prems(4) flat ll by fastforce
    qed
    show ?thesis using IHf newline flat by auto
  next
    case (HL_DExistsE src a af body)
    obtain si sl n0 c0 where
      em0: "hlEmitDerivationFuel fs base env scope first count src = (si,sl,n0,c0)"
      by (cases "hlEmitDerivationFuel fs base env scope first count src") auto
    obtain cR prs rbody where
      rb: "hlRepairDerivation base c0 (hlExistsRepairConstants scope af src phi) body
             = (cR,prs,rbody)"
      by (cases "hlRepairDerivation base c0 (hlExistsRepairConstants scope af src phi) body")
         auto
    obtain cS ps rsrc where
      rs: "hlRepairDerivation base c0 (hlExistsRepairConstants scope af src phi) src
             = (cS,ps,rsrc)"
      by (cases "hlRepairDerivation base c0 (hlExistsRepairConstants scope af src phi) src")
         auto
    define raf where "raf = hlRenamePairsFormula prs af"
    obtain bi bl n1 c1 where
      em1: "hlEmitDerivationFuel fs base ((a,n0,raf) # env) (raf # scope) (n0 + 1) cR rbody
              = (bi,bl,n1,c1)"
      by (cases "hlEmitDerivationFuel fs base ((a,n0,raf) # env) (raf # scope)
                   (n0 + 1) cR rbody") auto
    define cb where "cb = (if bi = [] \<and> bl \<noteq> n0
                           then [HL_FLine n1 (hlDerivationFormula rbody) (HL_FReit bl)]
                           else bi)"
    define lst where "lst = (if bi = [] \<and> bl \<noteq> n0 then n1 else bl)"
    define aft where "aft = (if bi = [] \<and> bl \<noteq> n0 then n1 + 1 else n1)"
    have sz0: "size src < size d" using d HL_DExistsE by simp
    have szb: "size rbody < size d"
      using d HL_DExistsE hlRepairDerivation_size[OF rb] by simp
    have okd: "hlDerivationOK (HL_Derivation phi (HL_DExistsE src a af body))"
      using less.prems(3) d HL_DExistsE by simp
    have oksrc: "hlDerivationOK src" using okd by simp
    have lec0: "count \<le> c0" by (rule hlEmitDerivationFuel_count_le[OF em0])
    have le0: "first \<le> n0" by (rule hlEmitDerivationFuel_start_le[OF em0])
    have nbd0: "hlNamesBelow base c0 (HL_Derivation phi (HL_DExistsE src a af body))"
      using less.prems(5) d HL_DExistsE hlNamesBelow_mono[OF less.prems(5) lec0] by simp
    have freshB: "\<forall>old \<in> set (hlExistsRepairConstants scope af src phi).
        old \<notin> hlConstantsInScope
                 (map snd (hlDropAssumption a (hlOpenAssumptions body))) \<and>
        old \<noteq> STR ''''"
      by (rule hlExistsRepair_fresh[OF okd])
    have nophi: "\<forall>old \<in> set (hlExistsRepairConstants scope af src phi).
        old \<notin> hlConstantsInFormula phi"
      by (simp add: set_hlExistsRepairConstants)
    have rpD: "hlRepairDerivation base c0 (hlExistsRepairConstants scope af src phi)
                 (HL_Derivation phi (HL_DExistsE src a af body))
               = (cR,prs,HL_Derivation phi (HL_DExistsE rsrc a raf rbody))"
      unfolding raf_def by (rule hlRepairDerivation_ExistsE[OF nophi rs rb])
    have okD: "hlDerivationOK (HL_Derivation phi (HL_DExistsE rsrc a raf rbody))"
      by (rule hlDerivationOK_repair[OF rpD okd nbd0 less.prems(14)]) (use freshB in blast)
    have okrb: "hlDerivationOK rbody" using okD by simp
    have disR: "hlDischargeOK a raf rbody" using okD by simp
    have cfR: "hlDerivationFormula rbody = phi" using okD by simp
    have sameB: "hlDropAssumption a (hlOpenAssumptions rbody) =
                 hlDropAssumption a (hlOpenAssumptions body)"
      by (rule hlDropAssumption_repair[OF rb]) (use freshB in blast)
    have nbbody: "hlNamesBelow base c0 body" by (rule NB) (use HL_DExistsE lec0 in simp_all)
    have nbrb: "hlNamesBelow base cR rbody" by (rule hlNamesBelow_repair[OF rb nbbody])
    have lecR: "c0 \<le> cR" by (rule hlRepairDerivation_count_le[OF rb])
    have afbound: "\<forall>c \<in> hlConstantsInFormula af. nlen c < base + c0"
    proof
      fix c assume "c \<in> hlConstantsInFormula af"
      then have "nlen c < base + count"
        using less.prems(5) d HL_DExistsE
        by (auto simp: hlNamesBelow_def hlDerivationConstants_def)
      then show "nlen c < base + c0" using lec0 by simp
    qed
    have rafbound: "\<forall>c \<in> hlConstantsInFormula raf. nlen c < base + cR"
      unfolding raf_def by (rule hlRenamePairsFormula_below[OF rb afbound])
    have eq: "items = si @ [HL_FSub (HL_Subproof n0 raf cb),
                            HL_FLine aft phi (HL_FExistsE sl (n0,lst))] \<and> n = aft"
      using less.prems(2) fuel d HL_DExistsE em0 rb em1
      by (auto simp: Let_def raf_def cb_def lst_def aft_def)
    have flat: "hlFlattenFitch items = hlFlattenFitch si @
      ((n0,raf,HL_FAssume) # hlFlattenFitch cb) @ [(aft,phi,HL_FExistsE sl (n0,lst))]"
      using eq by (simp add: hlFlattenFitch_append)
    have rec: "hlFitchScopeRecord S items = hlFitchScopeRecord S si @
      ((n0, insert n0 S) # hlFitchScopeRecord (insert n0 S) cb) @ [(aft,S)]"
      using eq by (simp add: hlFitchScopeRecord_append)
    have isi: "hlItemsCtx Q si" and icb: "hlItemsCtx Q cb"
      using less.prems(4) flat by (simp_all add: hlFlattenFitch_append)
    have ibi: "hlItemsCtx Q bi" by (rule hlItemsCtx_closedBody[OF cb_def icb])
    have hin: "(n0,raf,HL_FAssume) \<in> set (hlFlattenFitch items)" using flat by simp
    have hF: "hlLookF Q n0 = Some raf" using less.prems(4) hin by fastforce
    obtain la where la: "hlLookupLine Q n0 = Some la" and laf: "hlFormula la = raf"
      using hF by (cases "hlLookupLine Q n0") auto
    have laj: "hlJustification la = HL_Assumption"
      using less.prems(4) hin la by fastforce
    have lan: "hlLineNumber la = n0" by (rule hlLookupLine_number[OF la])
    have lar: "hlReferences la = {n0}"
      using less.prems(4) hin la by (fastforce simp: hlFitchDependenciesOf_def)
    have below: "hlEnvBelow env first"
      using less.prems(7) by (simp add: hlEmitCtx_def hlDepsCtx_def)
    have below0: "hlEnvBelow env n0" by (rule hlEnvBelow_mono[OF below le0])
    have ctx0: "hlEmitCtx Q env first src"
      using less.prems(7) d HL_DExistsE
      unfolding hlEmitCtx_def hlDepsCtx_def hlFormCtx_def by fastforce
    have cov: "\<forall>nf \<in> set (hlOpenAssumptions rbody).
        fst nf \<noteq> a \<longrightarrow> nf \<in> set (hlOpenAssumptions d)"
    proof (intro ballI impI)
      fix nf assume nf: "nf \<in> set (hlOpenAssumptions rbody)" and ne: "fst nf \<noteq> a"
      then have "nf \<in> set (hlDropAssumption a (hlOpenAssumptions rbody))" by simp
      then have "nf \<in> set (hlDropAssumption a (hlOpenAssumptions body))" using sameB by simp
      then show "nf \<in> set (hlOpenAssumptions d)" using d HL_DExistsE by simp
    qed
    have ctxb: "hlEmitCtx Q ((a,n0,raf) # env) (n0 + 1) rbody"
      unfolding hlEmitCtx_def hlDepsCtx_def hlFormCtx_def
    proof (intro conjI ballI)
      show "hlEnvBelow ((a,n0,raf) # env) (n0 + 1)"
        by (rule hlEnvBelow_Cons[OF below0]) auto
    next
      fix nf assume nf: "nf \<in> set (hlOpenAssumptions rbody)"
      show "fst nf \<in> fst ` set ((a,n0,raf) # env)"
        using nf cov less.prems(7)
        by (cases "fst nf = a") (auto simp: hlEmitCtx_def hlDepsCtx_def)
    next
      fix nf assume nf: "nf \<in> set (hlOpenAssumptions rbody)"
      show "hlRefsF Q (hlEnvironmentLine ((a,n0,raf) # env) (fst nf)) =
            {hlEnvironmentLine ((a,n0,raf) # env) (fst nf)}"
      proof (cases "fst nf = a")
        case True
        then show ?thesis using la lar by simp
      next
        case False
        then have "nf \<in> set (hlOpenAssumptions d)" using nf cov by blast
        then show ?thesis using less.prems(7) False
          unfolding hlEmitCtx_def hlDepsCtx_def by fastforce
      qed
    next
      fix nf assume nf: "nf \<in> set (hlOpenAssumptions rbody)"
      show "hlLookF Q (hlEnvironmentLine ((a,n0,raf) # env) (fst nf)) = Some (snd nf)"
      proof (cases "fst nf = a")
        case True
        then have "snd nf = raf" using disR nf by (simp add: hlDischargeOK_def)
        then show ?thesis using True hF by simp
      next
        case False
        then have "nf \<in> set (hlOpenAssumptions d)" using nf cov by blast
        then show ?thesis using less.prems(7) False
          unfolding hlEmitCtx_def hlFormCtx_def by fastforce
      qed
    qed
    have IH0: "\<forall>t \<in> set (hlFlattenFitch si).
                 \<forall>l. hlLookupLine Q (fst t) = Some l \<longrightarrow> hlRuleOKG (hlScopeSrc F) Q l"
    proof (rule IH[OF sz0 em0])
      show "hlDerivationOK src" by (rule oksrc)
      show "hlItemsCtx Q si" by (rule isi)
      show "hlNamesBelow base count src" by (rule NB) (simp_all add: HL_DExistsE)
      show "hlScopeBelow base count scope" by (rule less.prems(6))
      show "hlEmitCtx Q env first src" by (rule ctx0)
      show "\<forall>t \<in> set (hlFlattenFitch si).
              \<forall>l. hlLookupLine Q (fst t) = Some l \<longrightarrow> hlRuleOK Q l"
        using less.prems(8) flat by (auto simp: hlFlattenFitch_append)
      show "\<forall>q \<in> set (hlFitchScopeRecord S si). hlFitchScopeOf F (fst q) = snd q"
        using less.prems(9) rec by auto
      show "hlAssumptionConstants Q S \<subseteq> hlConstantsInScope scope" by (rule less.prems(10))
      show "hlReferencedConstants Q S \<subseteq> hlConstantsInScope scope" by (rule less.prems(11))
      show "\<forall>m \<in> S. m < first" by (rule less.prems(12))
    qed
    have subrec: "set (hlFitchScopeRecord (insert n0 S) bi) \<subseteq>
                  set (hlFitchScopeRecord (insert n0 S) cb)"
      and subflat: "set (hlFlattenFitch bi) \<subseteq> set (hlFlattenFitch cb)"
      by (cases "bi = [] \<and> bl \<noteq> n0"; simp add: cb_def)+
    have IHb: "\<forall>t \<in> set (hlFlattenFitch bi).
                 \<forall>l. hlLookupLine Q (fst t) = Some l \<longrightarrow> hlRuleOKG (hlScopeSrc F) Q l"
    proof (rule IH[OF szb em1])
      show "hlDerivationOK rbody" by (rule okrb)
      show "hlItemsCtx Q bi" by (rule ibi)
      show "hlNamesBelow base cR rbody" by (rule nbrb)
      show "hlScopeBelow base cR (raf # scope)"
        by (rule hlScopeBelow_Cons[OF hlScopeBelow_mono[OF less.prems(6)] rafbound])
           (use lec0 lecR in simp)
      show "hlEmitCtx Q ((a,n0,raf) # env) (n0 + 1) rbody" by (rule ctxb)
      show "\<forall>t \<in> set (hlFlattenFitch bi).
              \<forall>l. hlLookupLine Q (fst t) = Some l \<longrightarrow> hlRuleOK Q l"
        using less.prems(8) flat subflat by (auto simp: hlFlattenFitch_append)
      show "\<forall>q \<in> set (hlFitchScopeRecord (insert n0 S) bi).
              hlFitchScopeOf F (fst q) = snd q"
        using less.prems(9) rec subrec by auto
      show "hlAssumptionConstants Q (insert n0 S) \<subseteq> hlConstantsInScope (raf # scope)"
        using hlAssumptionConstants_insert[OF less.prems(13) la] less.prems(10) laf
        by (auto simp: hlConstantsInScope_def)
      show "hlReferencedConstants Q (insert n0 S) \<subseteq> hlConstantsInScope (raf # scope)"
        using hlReferencedConstants_insert[OF less.prems(13) la] less.prems(11) laf
        by (auto simp: hlConstantsInScope_def)
      show "\<forall>m \<in> insert n0 S. m < n0 + 1" using less.prems(12) le0 by auto
    qed
    have cbOK: "\<forall>t \<in> set (hlFlattenFitch cb).
                  \<forall>l. hlLookupLine Q (fst t) = Some l \<longrightarrow> hlRuleOKG (hlScopeSrc F) Q l"
    proof (cases "bi = [] \<and> bl \<noteq> n0")
      case False
      then have "cb = bi" using cb_def by simp
      then show ?thesis using IHb by simp
    next
      case True
      then have cbv: "cb = [HL_FLine n1 (hlDerivationFormula rbody) (HL_FReit bl)]"
        using cb_def by simp
      have "hlRuleOKG (hlScopeSrc F) Q l" if ll: "hlLookupLine Q n1 = Some l" for l
      proof (rule hlRuleOKG_of_hlRuleOK)
        show "hlRuleOK Q l" using less.prems(8) flat cbv ll by auto
      next
        show "hlJustification l \<noteq> HL_ForallIntro m" for m
          using less.prems(4) flat cbv ll by fastforce
      next
        show "hlJustification l \<noteq> HL_ExistsElim m a' c" for m a' c
          using less.prems(4) flat cbv ll by fastforce
      qed
      then show ?thesis using cbv by simp
    qed
    have headOK: "hlRuleOKG (hlScopeSrc F) Q l" if ll: "hlLookupLine Q n0 = Some l" for l
    proof (rule hlRuleOKG_of_hlRuleOK)
      show "hlRuleOK Q l" using less.prems(8) hin ll by auto
    next
      show "hlJustification l \<noteq> HL_ForallIntro m" for m
        using less.prems(4) hin ll by fastforce
    next
      show "hlJustification l \<noteq> HL_ExistsElim m a' c" for m a' c
        using less.prems(4) hin ll by fastforce
    qed
    have lstrec: "(lst, insert n0 S) \<in> set (hlFitchScopeRecord S items)"
    proof (cases "bi = [] \<and> bl \<noteq> n0")
      case True
      then have "cb = [HL_FLine n1 (hlDerivationFormula rbody) (HL_FReit bl)]"
        and "lst = n1" using cb_def lst_def by simp_all
      then show ?thesis using rec by simp
    next
      case notreit: False
      show ?thesis
      proof (cases "bi = []")
        case True
        have blv: "bl = n0" using True notreit by simp
        have "lst = n0" using lst_def blv by simp
        then show ?thesis using rec by simp
      next
        case False
        from hlEmitDerivationFuel_last[OF em1 False] obtain r where
          lastb: "last bi = HL_FLine bl (hlDerivationFormula rbody) r" by blast
        have "bi = butlast bi @ [HL_FLine bl (hlDerivationFormula rbody) r]"
          using lastb False by (metis append_butlast_last_id)
        then have "hlFitchScopeRecord (insert n0 S) bi =
                   hlFitchScopeRecord (insert n0 S) (butlast bi) @ [(bl, insert n0 S)]"
          by (metis hlFitchScopeRecord_append hlFitchScopeRecord.simps(1,2))
        then have "(bl, insert n0 S) \<in> set (hlFitchScopeRecord (insert n0 S) bi)" by simp
        moreover have "cb = bi" and "lst = bl"
          using notreit False cb_def lst_def by simp_all
        ultimately show ?thesis using rec by auto
      qed
    qed
    have lstf: "hlLookF Q lst = Some (hlDerivationFormula rbody)"
    proof -
      have blf: "hlLookF Q bl = Some (hlDerivationFormula rbody)"
      proof (rule hlEmitDerivationFuel_returns_formula[OF em1 small[OF szb]])
        show "\<forall>nf \<in> set (hlOpenAssumptions rbody).
                hlLookF Q (hlEnvironmentLine ((a,n0,raf) # env) (fst nf)) = Some (snd nf)"
          using ctxb by (simp add: hlEmitCtx_def hlFormCtx_def)
      next
        show "\<forall>t \<in> set (hlFlattenFitch bi). hlLookF Q (fst t) = Some (fst (snd t))"
          using ibi by simp
      qed
      show ?thesis by (rule hlClosedBody_form[OF cb_def lst_def _ blf]) (use icb in simp)
    qed
    obtain lc where lc: "hlLookupLine Q lst = Some lc"
      and lcf: "hlFormula lc = hlDerivationFormula rbody"
      using lstf by (cases "hlLookupLine Q lst") auto
    have slf: "hlLookF Q sl = Some (hlDerivationFormula src)"
    proof (rule hlEmitDerivationFuel_returns_formula[OF em0 small[OF sz0]])
      show "\<forall>nf \<in> set (hlOpenAssumptions src).
              hlLookF Q (hlEnvironmentLine env (fst nf)) = Some (snd nf)"
        using ctx0 by (simp add: hlEmitCtx_def hlFormCtx_def)
    next
      show "\<forall>t \<in> set (hlFlattenFitch si). hlLookF Q (fst t) = Some (fst (snd t))"
        using isi by simp
    qed
    obtain lm where lm: "hlLookupLine Q sl = Some lm"
      and lmf: "hlFormula lm = hlDerivationFormula src"
      using slf by (cases "hlLookupLine Q sl") auto
    have newline: "hlRuleOKG (hlScopeSrc F) Q l" if ll: "hlLookupLine Q aft = Some l" for l
    proof -
      have tin: "(aft,phi,HL_FExistsE sl (n0,lst)) \<in> set (hlFlattenFitch items)"
        using flat by simp
      have fl: "hlFormula l = phi" using less.prems(4) tin ll by fastforce
      have jl: "hlJustification l = HL_ExistsElim sl n0 lst"
        using less.prems(4) tin ll by fastforce
      have rl: "hlReferences l = hlReferences lm \<union> (hlReferences lc - {n0})"
        using less.prems(4) tin ll lm lc by (fastforce simp: hlFitchDependenciesOf_def)
      have okl: "hlRuleOK Q l" using less.prems(8) flat ll by auto
      have disj: "(hlConstantsInFormula (hlFormula la) -
                   (hlConstantsInFormula (hlFormula lm) \<union>
                    hlConstantsInFormula (hlFormula lc))) \<inter> hlConstantsInScope scope = {}"
        using hlExistsRepair_disjoint[OF rb hlScopeBelow_mono[OF less.prems(6) lec0]
                afbound] laf lmf lcf cfR by (simp add: raf_def)
      have step: "hlExistsElimStep (hlFormula lm) (hlFormula la) (hlFormula lc) scope"
        by (rule hlRuleOK_ExistsElim_scope[OF okl jl lm la lc disj])
      have lcn: "hlLineNumber lc = lst" by (rule hlLookupLine_number[OF lc])
      have scopeat: "hlFitchScopeOf F lst = insert n0 S"
        using less.prems(9) lstrec by auto
      have notin: "n0 \<notin> S" using less.prems(12) le0 by auto
      show ?thesis
      proof (rule hlRuleOKG_ExistsElim[OF jl lm la lc laj step _ _ _])
        show "hlReferencedConstants Q
                (hlScopeSrc F Q (hlLineNumber lc) (hlReferences lc) -
                 {hlLineNumber la}) \<subseteq> hlConstantsInScope scope"
          using scopeat lcn lan notin less.prems(11) by (simp add: hlScopeSrc_def)
      next
        show "hlFormula l = hlFormula lc" using fl lcf cfR by simp
      next
        show "hlReferences l =
                hlReferences lm \<union> (hlReferences lc - {hlLineNumber la})"
          using rl lan by simp
      qed
    qed
    show ?thesis using IH0 headOK cbOK newline la flat by auto
  next
    case (HL_DEqE e1 e2)
    obtain front k1 mid c1 where
      em1: "hlEmitDerivationFuel fs base env scope first count e1 = (front,k1,mid,c1)"
      by (cases "hlEmitDerivationFuel fs base env scope first count e1") auto
    obtain rear k2 fin c2 where
      em2: "hlEmitDerivationFuel fs base env scope mid c1 e2 = (rear,k2,fin,c2)"
      by (cases "hlEmitDerivationFuel fs base env scope mid c1 e2") auto
    have sz1: "size e1 < size d" and sz2: "size e2 < size d" using d HL_DEqE by simp_all
    have le: "first \<le> mid" by (rule hlEmitDerivationFuel_start_le[OF em1])
    have lec: "count \<le> c1" by (rule hlEmitDerivationFuel_count_le[OF em1])
    have eq: "items = front @ rear @ [HL_FLine fin phi (HL_FEqE k1 k2)] \<and> n = fin"
      using less.prems(2) fuel d HL_DEqE em1 em2 by (auto simp: Let_def)
    have flat: "hlFlattenFitch items =
        hlFlattenFitch front @ hlFlattenFitch rear @ [(fin,phi,HL_FEqE k1 k2)]"
      using eq by (simp add: hlFlattenFitch_append)
    have rec: "hlFitchScopeRecord S items =
        hlFitchScopeRecord S front @ hlFitchScopeRecord S rear @ [(fin,S)]"
      using eq by (simp add: hlFitchScopeRecord_append)
    have ctx1: "hlEmitCtx Q env first e1" and ctx2: "hlEmitCtx Q env mid e2"
      using less.prems(7) d HL_DEqE le
      by (auto simp: hlEmitCtx_def hlDepsCtx_def hlFormCtx_def hlEnvBelow_def)
    have IH1: "\<forall>t \<in> set (hlFlattenFitch front).
                 \<forall>l. hlLookupLine Q (fst t) = Some l \<longrightarrow> hlRuleOKG (hlScopeSrc F) Q l"
    proof (rule IH[OF sz1 em1])
      show "hlDerivationOK e1" using less.prems(3) d HL_DEqE by simp
      show "hlItemsCtx Q front" using less.prems(4) flat by (simp add: hlFlattenFitch_append)
      show "hlNamesBelow base count e1" by (rule NB) (simp_all add: HL_DEqE)
      show "hlScopeBelow base count scope" by (rule less.prems(6))
      show "hlEmitCtx Q env first e1" by (rule ctx1)
      show "\<forall>t \<in> set (hlFlattenFitch front).
              \<forall>l. hlLookupLine Q (fst t) = Some l \<longrightarrow> hlRuleOK Q l"
        using less.prems(8) flat by auto
      show "\<forall>q \<in> set (hlFitchScopeRecord S front). hlFitchScopeOf F (fst q) = snd q"
        using less.prems(9) rec by auto
      show "hlAssumptionConstants Q S \<subseteq> hlConstantsInScope scope" by (rule less.prems(10))
      show "hlReferencedConstants Q S \<subseteq> hlConstantsInScope scope" by (rule less.prems(11))
      show "\<forall>m \<in> S. m < first" by (rule less.prems(12))
    qed
    have IH2: "\<forall>t \<in> set (hlFlattenFitch rear).
                 \<forall>l. hlLookupLine Q (fst t) = Some l \<longrightarrow> hlRuleOKG (hlScopeSrc F) Q l"
    proof (rule IH[OF sz2 em2])
      show "hlDerivationOK e2" using less.prems(3) d HL_DEqE by simp
      show "hlItemsCtx Q rear" using less.prems(4) flat by (simp add: hlFlattenFitch_append)
      show "hlNamesBelow base c1 e2" by (rule NB) (use HL_DEqE lec in simp_all)
      show "hlScopeBelow base c1 scope" by (rule hlScopeBelow_mono[OF less.prems(6) lec])
      show "hlEmitCtx Q env mid e2" by (rule ctx2)
      show "\<forall>t \<in> set (hlFlattenFitch rear).
              \<forall>l. hlLookupLine Q (fst t) = Some l \<longrightarrow> hlRuleOK Q l"
        using less.prems(8) flat by auto
      show "\<forall>q \<in> set (hlFitchScopeRecord S rear). hlFitchScopeOf F (fst q) = snd q"
        using less.prems(9) rec by auto
      show "hlAssumptionConstants Q S \<subseteq> hlConstantsInScope scope" by (rule less.prems(10))
      show "hlReferencedConstants Q S \<subseteq> hlConstantsInScope scope" by (rule less.prems(11))
      show "\<forall>m \<in> S. m < mid" using less.prems(12) le by auto
    qed
    have newline: "hlRuleOKG (hlScopeSrc F) Q l" if ll: "hlLookupLine Q fin = Some l" for l
    proof (rule hlRuleOKG_of_hlRuleOK)
      show "hlRuleOK Q l" using less.prems(8) flat ll by auto
    next
      show "hlJustification l \<noteq> HL_ForallIntro m" for m
        using less.prems(4) flat ll by fastforce
    next
      show "hlJustification l \<noteq> HL_ExistsElim m a c" for m a c
        using less.prems(4) flat ll by fastforce
    qed
    show ?thesis using IH1 IH2 newline flat by auto
  next
    case (HL_DPropTaut ds)
    obtain front ns mid c1 where
      em: "hlEmitDerivationsUsing (hlEmitDerivationFuel fs base env scope) first count ds
             = (front,ns,mid,c1)"
      by (cases "hlEmitDerivationsUsing (hlEmitDerivationFuel fs base env scope)
                   first count ds") auto
    have eq: "items = front @ [HL_FLine mid phi (HL_FPropTaut ns)] \<and> n = mid"
      using less.prems(2) fuel d HL_DPropTaut em by (auto simp: Let_def)
    have flat: "hlFlattenFitch items = hlFlattenFitch front @ [(mid,phi,HL_FPropTaut ns)]"
      using eq by (simp add: hlFlattenFitch_append)
    have rec: "hlFitchScopeRecord S items = hlFitchScopeRecord S front @ [(mid,S)]"
      using eq by (simp add: hlFitchScopeRecord_append)
    have ifront: "hlItemsCtx Q front"
      using less.prems(4) flat by (simp add: hlFlattenFitch_append)
    have rfront: "\<forall>t \<in> set (hlFlattenFitch front).
                    \<forall>l. hlLookupLine Q (fst t) = Some l \<longrightarrow> hlRuleOK Q l"
      using less.prems(8) flat by auto
    have afront: "\<forall>q \<in> set (hlFitchScopeRecord S front).
                    hlFitchScopeOf F (fst q) = snd q"
      using less.prems(9) rec by auto
    have IHf: "\<forall>t \<in> set (hlFlattenFitch front).
                 \<forall>l. hlLookupLine Q (fst t) = Some l \<longrightarrow> hlRuleOKG (hlScopeSrc F) Q l"
    proof (rule hlScopeOK_emit_list[OF em ifront rfront afront])
      fix e fi ct out k af c2
      show "fi \<le> af"
        if "hlEmitDerivationFuel fs base env scope fi ct e = (out,k,af,c2)"
        using hlEmitDerivationFuel_start_le[OF that] .
    next
      fix e fi ct out k af c2
      show "ct \<le> c2"
        if "hlEmitDerivationFuel fs base env scope fi ct e = (out,k,af,c2)"
        using hlEmitDerivationFuel_count_le[OF that] .
    next
      show "first \<le> first" by simp
    next
      show "count \<le> count" by simp
    next
      fix e fi ct out k af c2
      assume mem: "e \<in> set ds"
        and got: "hlEmitDerivationFuel fs base env scope fi ct e = (out,k,af,c2)"
        and dd: "hlItemsCtx Q out"
        and rr: "\<forall>t \<in> set (hlFlattenFitch out).
                   \<forall>l. hlLookupLine Q (fst t) = Some l \<longrightarrow> hlRuleOK Q l"
        and aa: "\<forall>q \<in> set (hlFitchScopeRecord S out). hlFitchScopeOf F (fst q) = snd q"
        and ff: "first \<le> fi" and cc: "count \<le> ct"
      have sz: "size e < size d"
      proof -
        have "size e \<le> size_list size ds"
          by (rule size_list_estimation'[OF mem]) simp
        then show ?thesis using d HL_DPropTaut by simp
      qed
      show "\<forall>t \<in> set (hlFlattenFitch out).
              \<forall>l. hlLookupLine Q (fst t) = Some l \<longrightarrow> hlRuleOKG (hlScopeSrc F) Q l"
      proof (rule IH[OF sz got])
        show "hlDerivationOK e"
          using less.prems(3) d HL_DPropTaut mem by (simp add: list_all_iff)
        show "hlItemsCtx Q out" by (rule dd)
        show "hlNamesBelow base ct e" by (rule NB) (use mem HL_DPropTaut cc in simp_all)
        show "hlScopeBelow base ct scope"
          by (rule hlScopeBelow_mono[OF less.prems(6) cc])
        show "hlEmitCtx Q env fi e"
          using less.prems(7) mem d HL_DPropTaut ff
          by (fastforce simp: hlEmitCtx_def hlDepsCtx_def hlFormCtx_def hlEnvBelow_def)
        show "\<forall>t \<in> set (hlFlattenFitch out).
                \<forall>l. hlLookupLine Q (fst t) = Some l \<longrightarrow> hlRuleOK Q l" by (rule rr)
        show "\<forall>q \<in> set (hlFitchScopeRecord S out). hlFitchScopeOf F (fst q) = snd q"
          by (rule aa)
        show "hlAssumptionConstants Q S \<subseteq> hlConstantsInScope scope" by (rule less.prems(10))
        show "hlReferencedConstants Q S \<subseteq> hlConstantsInScope scope" by (rule less.prems(11))
        show "\<forall>m \<in> S. m < fi" using less.prems(12) ff by auto
      qed
    qed
    have newline: "hlRuleOKG (hlScopeSrc F) Q l" if ll: "hlLookupLine Q mid = Some l" for l
    proof (rule hlRuleOKG_of_hlRuleOK)
      show "hlRuleOK Q l" using less.prems(8) flat ll by auto
    next
      show "hlJustification l \<noteq> HL_ForallIntro m" for m
        using less.prems(4) flat ll by fastforce
    next
      show "hlJustification l \<noteq> HL_ExistsElim m a' c" for m a' c
        using less.prems(4) flat ll by fastforce
    qed
    show ?thesis using IHf newline flat by auto
  next
    case (HL_DIffI e1 e2)
    obtain front k1 mid c1 where
      em1: "hlEmitDerivationFuel fs base env scope first count e1 = (front,k1,mid,c1)"
      by (cases "hlEmitDerivationFuel fs base env scope first count e1") auto
    obtain rear k2 fin c2 where
      em2: "hlEmitDerivationFuel fs base env scope mid c1 e2 = (rear,k2,fin,c2)"
      by (cases "hlEmitDerivationFuel fs base env scope mid c1 e2") auto
    have sz1: "size e1 < size d" and sz2: "size e2 < size d" using d HL_DIffI by simp_all
    have le: "first \<le> mid" by (rule hlEmitDerivationFuel_start_le[OF em1])
    have lec: "count \<le> c1" by (rule hlEmitDerivationFuel_count_le[OF em1])
    have eq: "items = front @ rear @ [HL_FLine fin phi (HL_FIffI k1 k2)] \<and> n = fin"
      using less.prems(2) fuel d HL_DIffI em1 em2 by (auto simp: Let_def)
    have flat: "hlFlattenFitch items =
        hlFlattenFitch front @ hlFlattenFitch rear @ [(fin,phi,HL_FIffI k1 k2)]"
      using eq by (simp add: hlFlattenFitch_append)
    have rec: "hlFitchScopeRecord S items =
        hlFitchScopeRecord S front @ hlFitchScopeRecord S rear @ [(fin,S)]"
      using eq by (simp add: hlFitchScopeRecord_append)
    have ctx1: "hlEmitCtx Q env first e1" and ctx2: "hlEmitCtx Q env mid e2"
      using less.prems(7) d HL_DIffI le
      by (auto simp: hlEmitCtx_def hlDepsCtx_def hlFormCtx_def hlEnvBelow_def)
    have IH1: "\<forall>t \<in> set (hlFlattenFitch front).
                 \<forall>l. hlLookupLine Q (fst t) = Some l \<longrightarrow> hlRuleOKG (hlScopeSrc F) Q l"
    proof (rule IH[OF sz1 em1])
      show "hlDerivationOK e1" using less.prems(3) d HL_DIffI by simp
      show "hlItemsCtx Q front" using less.prems(4) flat by (simp add: hlFlattenFitch_append)
      show "hlNamesBelow base count e1" by (rule NB) (simp_all add: HL_DIffI)
      show "hlScopeBelow base count scope" by (rule less.prems(6))
      show "hlEmitCtx Q env first e1" by (rule ctx1)
      show "\<forall>t \<in> set (hlFlattenFitch front).
              \<forall>l. hlLookupLine Q (fst t) = Some l \<longrightarrow> hlRuleOK Q l"
        using less.prems(8) flat by auto
      show "\<forall>q \<in> set (hlFitchScopeRecord S front). hlFitchScopeOf F (fst q) = snd q"
        using less.prems(9) rec by auto
      show "hlAssumptionConstants Q S \<subseteq> hlConstantsInScope scope" by (rule less.prems(10))
      show "hlReferencedConstants Q S \<subseteq> hlConstantsInScope scope" by (rule less.prems(11))
      show "\<forall>m \<in> S. m < first" by (rule less.prems(12))
    qed
    have IH2: "\<forall>t \<in> set (hlFlattenFitch rear).
                 \<forall>l. hlLookupLine Q (fst t) = Some l \<longrightarrow> hlRuleOKG (hlScopeSrc F) Q l"
    proof (rule IH[OF sz2 em2])
      show "hlDerivationOK e2" using less.prems(3) d HL_DIffI by simp
      show "hlItemsCtx Q rear" using less.prems(4) flat by (simp add: hlFlattenFitch_append)
      show "hlNamesBelow base c1 e2" by (rule NB) (use HL_DIffI lec in simp_all)
      show "hlScopeBelow base c1 scope" by (rule hlScopeBelow_mono[OF less.prems(6) lec])
      show "hlEmitCtx Q env mid e2" by (rule ctx2)
      show "\<forall>t \<in> set (hlFlattenFitch rear).
              \<forall>l. hlLookupLine Q (fst t) = Some l \<longrightarrow> hlRuleOK Q l"
        using less.prems(8) flat by auto
      show "\<forall>q \<in> set (hlFitchScopeRecord S rear). hlFitchScopeOf F (fst q) = snd q"
        using less.prems(9) rec by auto
      show "hlAssumptionConstants Q S \<subseteq> hlConstantsInScope scope" by (rule less.prems(10))
      show "hlReferencedConstants Q S \<subseteq> hlConstantsInScope scope" by (rule less.prems(11))
      show "\<forall>m \<in> S. m < mid" using less.prems(12) le by auto
    qed
    have newline: "hlRuleOKG (hlScopeSrc F) Q l" if ll: "hlLookupLine Q fin = Some l" for l
    proof (rule hlRuleOKG_of_hlRuleOK)
      show "hlRuleOK Q l" using less.prems(8) flat ll by auto
    next
      show "hlJustification l \<noteq> HL_ForallIntro m" for m
        using less.prems(4) flat ll by fastforce
    next
      show "hlJustification l \<noteq> HL_ExistsElim m a c" for m a c
        using less.prems(4) flat ll by fastforce
    qed
    show ?thesis using IH1 IH2 newline flat by auto
  next
    case (HL_DIffE e1 e2)
    obtain front k1 mid c1 where
      em1: "hlEmitDerivationFuel fs base env scope first count e1 = (front,k1,mid,c1)"
      by (cases "hlEmitDerivationFuel fs base env scope first count e1") auto
    obtain rear k2 fin c2 where
      em2: "hlEmitDerivationFuel fs base env scope mid c1 e2 = (rear,k2,fin,c2)"
      by (cases "hlEmitDerivationFuel fs base env scope mid c1 e2") auto
    have sz1: "size e1 < size d" and sz2: "size e2 < size d" using d HL_DIffE by simp_all
    have le: "first \<le> mid" by (rule hlEmitDerivationFuel_start_le[OF em1])
    have lec: "count \<le> c1" by (rule hlEmitDerivationFuel_count_le[OF em1])
    have eq: "items = front @ rear @ [HL_FLine fin phi (HL_FIffE k1 k2)] \<and> n = fin"
      using less.prems(2) fuel d HL_DIffE em1 em2 by (auto simp: Let_def)
    have flat: "hlFlattenFitch items =
        hlFlattenFitch front @ hlFlattenFitch rear @ [(fin,phi,HL_FIffE k1 k2)]"
      using eq by (simp add: hlFlattenFitch_append)
    have rec: "hlFitchScopeRecord S items =
        hlFitchScopeRecord S front @ hlFitchScopeRecord S rear @ [(fin,S)]"
      using eq by (simp add: hlFitchScopeRecord_append)
    have ctx1: "hlEmitCtx Q env first e1" and ctx2: "hlEmitCtx Q env mid e2"
      using less.prems(7) d HL_DIffE le
      by (auto simp: hlEmitCtx_def hlDepsCtx_def hlFormCtx_def hlEnvBelow_def)
    have IH1: "\<forall>t \<in> set (hlFlattenFitch front).
                 \<forall>l. hlLookupLine Q (fst t) = Some l \<longrightarrow> hlRuleOKG (hlScopeSrc F) Q l"
    proof (rule IH[OF sz1 em1])
      show "hlDerivationOK e1" using less.prems(3) d HL_DIffE by simp
      show "hlItemsCtx Q front" using less.prems(4) flat by (simp add: hlFlattenFitch_append)
      show "hlNamesBelow base count e1" by (rule NB) (simp_all add: HL_DIffE)
      show "hlScopeBelow base count scope" by (rule less.prems(6))
      show "hlEmitCtx Q env first e1" by (rule ctx1)
      show "\<forall>t \<in> set (hlFlattenFitch front).
              \<forall>l. hlLookupLine Q (fst t) = Some l \<longrightarrow> hlRuleOK Q l"
        using less.prems(8) flat by auto
      show "\<forall>q \<in> set (hlFitchScopeRecord S front). hlFitchScopeOf F (fst q) = snd q"
        using less.prems(9) rec by auto
      show "hlAssumptionConstants Q S \<subseteq> hlConstantsInScope scope" by (rule less.prems(10))
      show "hlReferencedConstants Q S \<subseteq> hlConstantsInScope scope" by (rule less.prems(11))
      show "\<forall>m \<in> S. m < first" by (rule less.prems(12))
    qed
    have IH2: "\<forall>t \<in> set (hlFlattenFitch rear).
                 \<forall>l. hlLookupLine Q (fst t) = Some l \<longrightarrow> hlRuleOKG (hlScopeSrc F) Q l"
    proof (rule IH[OF sz2 em2])
      show "hlDerivationOK e2" using less.prems(3) d HL_DIffE by simp
      show "hlItemsCtx Q rear" using less.prems(4) flat by (simp add: hlFlattenFitch_append)
      show "hlNamesBelow base c1 e2" by (rule NB) (use HL_DIffE lec in simp_all)
      show "hlScopeBelow base c1 scope" by (rule hlScopeBelow_mono[OF less.prems(6) lec])
      show "hlEmitCtx Q env mid e2" by (rule ctx2)
      show "\<forall>t \<in> set (hlFlattenFitch rear).
              \<forall>l. hlLookupLine Q (fst t) = Some l \<longrightarrow> hlRuleOK Q l"
        using less.prems(8) flat by auto
      show "\<forall>q \<in> set (hlFitchScopeRecord S rear). hlFitchScopeOf F (fst q) = snd q"
        using less.prems(9) rec by auto
      show "hlAssumptionConstants Q S \<subseteq> hlConstantsInScope scope" by (rule less.prems(10))
      show "hlReferencedConstants Q S \<subseteq> hlConstantsInScope scope" by (rule less.prems(11))
      show "\<forall>m \<in> S. m < mid" using less.prems(12) le by auto
    qed
    have newline: "hlRuleOKG (hlScopeSrc F) Q l" if ll: "hlLookupLine Q fin = Some l" for l
    proof (rule hlRuleOKG_of_hlRuleOK)
      show "hlRuleOK Q l" using less.prems(8) flat ll by auto
    next
      show "hlJustification l \<noteq> HL_ForallIntro m" for m
        using less.prems(4) flat ll by fastforce
    next
      show "hlJustification l \<noteq> HL_ExistsElim m a c" for m a c
        using less.prems(4) flat ll by fastforce
    qed
    show ?thesis using IH1 IH2 newline flat by auto
  next
    case (HL_DQN e)
    obtain front k mid c1 where
      em: "hlEmitDerivationFuel fs base env scope first count e = (front,k,mid,c1)"
      by (cases "hlEmitDerivationFuel fs base env scope first count e") auto
    have sz: "size e < size d" using d HL_DQN by simp
    have eq: "items = front @ [HL_FLine mid phi (HL_FQN k)] \<and> n = mid"
      using less.prems(2) fuel d HL_DQN em by (auto simp: Let_def)
    have flat: "hlFlattenFitch items = hlFlattenFitch front @ [(mid,phi,HL_FQN k)]"
      using eq by (simp add: hlFlattenFitch_append)
    have rec: "hlFitchScopeRecord S items = hlFitchScopeRecord S front @ [(mid,S)]"
      using eq by (simp add: hlFitchScopeRecord_append)
    have IHf: "\<forall>t \<in> set (hlFlattenFitch front).
                 \<forall>l. hlLookupLine Q (fst t) = Some l \<longrightarrow> hlRuleOKG (hlScopeSrc F) Q l"
    proof (rule IH[OF sz em])
      show "hlDerivationOK e" using less.prems(3) d HL_DQN by simp
      show "hlItemsCtx Q front" using less.prems(4) flat by (simp add: hlFlattenFitch_append)
      show "hlNamesBelow base count e" by (rule NB) (simp_all add: HL_DQN)
      show "hlScopeBelow base count scope" by (rule less.prems(6))
      show "hlEmitCtx Q env first e"
        using less.prems(7) d HL_DQN
        by (simp add: hlEmitCtx_def hlDepsCtx_def hlFormCtx_def)
      show "\<forall>t \<in> set (hlFlattenFitch front).
              \<forall>l. hlLookupLine Q (fst t) = Some l \<longrightarrow> hlRuleOK Q l"
        using less.prems(8) flat by auto
      show "\<forall>q \<in> set (hlFitchScopeRecord S front). hlFitchScopeOf F (fst q) = snd q"
        using less.prems(9) rec by auto
      show "hlAssumptionConstants Q S \<subseteq> hlConstantsInScope scope" by (rule less.prems(10))
      show "hlReferencedConstants Q S \<subseteq> hlConstantsInScope scope" by (rule less.prems(11))
      show "\<forall>m \<in> S. m < first" by (rule less.prems(12))
    qed
    have newline: "hlRuleOKG (hlScopeSrc F) Q l" if ll: "hlLookupLine Q mid = Some l" for l
    proof (rule hlRuleOKG_of_hlRuleOK)
      show "hlRuleOK Q l" using less.prems(8) flat ll by auto
    next
      show "hlJustification l \<noteq> HL_ForallIntro m" for m
        using less.prems(4) flat ll by fastforce
    next
      show "hlJustification l \<noteq> HL_ExistsElim m a c" for m a c
        using less.prems(4) flat ll by fastforce
    qed
    show ?thesis using IHf newline flat by auto
  qed
qed

section \<open>The emitted Fitch proof erases to a correct Lemmon proof\<close>

theorem hlDerivationToFitch_correct:
  assumes fn: "hlAssumptionsFunctional d"
      and root: "set (hlPremisesOf d) = set (hlOpenAssumptions d)"
      and ok: "hlDerivationOK d"
  shows "hlCorrect (\<delta>\<^sub>H (hlDerivationToFitch d)) \<and>
         hlFitchPremiseClosed (hlDerivationToFitch d) \<and>
         hlCorrectG (hlScopeSrc (hlDerivationToFitch d))
           (\<delta>\<^sub>H (hlDerivationToFitch d))"
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

  text \<open>The scope-based check.  At the root the scope is exactly the premise
    lines, whose formulas are exactly the emitter's own scope list.\<close>

  have distF: "distinct (hlFitchLineNumbers ?F)" by (rule sorted_wrt_less_distinct[OF sorted])
  have Snums: "set (hlFitchPremiseNumbers ?F) = (\<lambda>q. fst (snd q)) ` set ?env"
  proof -
    have "hlFitchPremiseNumbers ?F =
          hlFitchPremiseNumbers ?pre @ hlFitchPremiseNumbers body"
      using F by (simp add: hlFitchPremiseNumbers_append)
    also have "\<dots> = map (\<lambda>(s,n,p). n) ?env"
      using hlFitchPremiseNumbers_premiseFitchLines[of ?env]
            hlNoPremiseLines_numbers[OF hlEmitDerivation_no_premises[OF em]] by simp
    finally show ?thesis by (force simp: case_prod_beta)
  qed
  have Sline: "\<exists>p. (m,p,HL_FPremise) \<in> set (hlFlattenFitch ?pre) \<and>
                   p \<in> set (map (\<lambda>(source,n,phi). phi) ?env)"
    if mem: "m \<in> set (hlFitchPremiseNumbers ?F)" for m
  proof -
    from mem Snums obtain q where q: "q \<in> set ?env" "m = fst (snd q)" by blast
    obtain s nn pp where qv: "q = (s,nn,pp)" by (cases q) auto
    have a1: "(nn,pp,HL_FPremise) \<in> set (hlFlattenFitch ?pre)"
      using q(1) qv by (force simp: hlPremiseFitchLines_flatten)
    have a2: "pp \<in> set (map (\<lambda>(source,n,phi). phi) ?env)" using q(1) qv by force
    have "m = nn" using q(2) qv by simp
    then show ?thesis using a1 a2 by blast
  qed
  have Sinv: "hlAssumptionConstants ?Q (set (hlFitchPremiseNumbers ?F)) \<subseteq>
              hlConstantsInScope (map (\<lambda>(source,n,phi). phi) ?env)"
  proof
    fix c assume "c \<in> hlAssumptionConstants ?Q (set (hlFitchPremiseNumbers ?F))"
    then obtain l where l: "l \<in> set ?Q" "hlLineNumber l \<in> set (hlFitchPremiseNumbers ?F)"
      and cc: "c \<in> hlConstantsInFormula (hlFormula l)"
      by (auto simp: hlAssumptionConstants_def)
    from Sline[OF l(2)] obtain p where
      mem: "(hlLineNumber l,p,HL_FPremise) \<in> set (hlFlattenFitch ?pre)"
      and pin: "p \<in> set (map (\<lambda>(source,n,phi). phi) ?env)" by blast
    have look: "hlLookupLine ?Q (hlLineNumber l) = Some l"
      by (rule hlLookupLine_self[OF distQ l(1)])
    from premise[OF mem] look have fp: "hlFormula l = p" by auto
    have "c \<in> hlConstantsInFormula p" using cc fp by simp
    then show "c \<in> hlConstantsInScope (map (\<lambda>(source,n,phi). phi) ?env)"
      using pin unfolding hlConstantsInScope_def by blast
  qed
  have Sref: "hlReferencedConstants ?Q (set (hlFitchPremiseNumbers ?F)) \<subseteq>
              hlConstantsInScope (map (\<lambda>(source,n,phi). phi) ?env)"
  proof
    fix c assume "c \<in> hlReferencedConstants ?Q (set (hlFitchPremiseNumbers ?F))"
    then obtain l where l: "l \<in> set ?Q" "hlLineNumber l \<in> set (hlFitchPremiseNumbers ?F)"
      and cc: "c \<in> hlConstantsInFormula (hlFormula l)"
      by (auto simp: hlReferencedConstants_def)
    from Sline[OF l(2)] obtain p where
      mem: "(hlLineNumber l,p,HL_FPremise) \<in> set (hlFlattenFitch ?pre)"
      and pin: "p \<in> set (map (\<lambda>(source,n,phi). phi) ?env)" by blast
    have look: "hlLookupLine ?Q (hlLineNumber l) = Some l"
      by (rule hlLookupLine_self[OF distQ l(1)])
    from premise[OF mem] look have fp: "hlFormula l = p" by auto
    have "c \<in> hlConstantsInFormula p" using cc fp by simp
    then show "c \<in> hlConstantsInScope (map (\<lambda>(source,n,phi). phi) ?env)"
      using pin unfolding hlConstantsInScope_def by blast
  qed
  have Sbelow: "\<forall>m \<in> set (hlFitchPremiseNumbers ?F). m < ?first"
  proof
    fix m assume "m \<in> set (hlFitchPremiseNumbers ?F)"
    then obtain q where q: "q \<in> set ?env" "m = fst (snd q)" using Snums by blast
    obtain s nn pp where qv: "q = (s,nn,pp)" by (cases q) auto
    have "(s,nn,pp) \<in> set (hlNumberPremises 1 (sort_key fst (remdups (hlPremisesOf d))))"
      using q(1) qv by (simp add: hlPremiseEnvironment_def)
    from hlNumberPremises_below[OF this] show "m < ?first"
      using q(2) qv by (simp add: hlPremiseEnvironment_def)
  qed
  have scopeb: "hlScopeBelow ?base 0 (map (\<lambda>(source,n,phi). phi) ?env)"
    unfolding hlScopeBelow_def
  proof
    fix c assume "c \<in> hlConstantsInScope (map (\<lambda>(source,n,phi). phi) ?env)"
    then obtain p where p: "p \<in> set (map (\<lambda>(source,n,phi). phi) ?env)"
      and cc: "c \<in> hlConstantsInFormula p"
      unfolding hlConstantsInScope_def by blast
    have "p \<in> snd ` set (hlPremisesOf d)"
      using p hlPremiseEnvironment_formulas[of d] by simp
    then obtain nf where nf: "nf \<in> set (hlPremisesOf d)" "p = snd nf" by blast
    then have "nf \<in> set (hlOpenAssumptions d)" using root by simp
    then have "p \<in> set (hlDerivationFormulas d)"
      using nf(2) hlOpenAssumptions_in_formulas by blast
    then have "c \<in> hlDerivationConstants d" using cc by (auto simp: hlDerivationConstants_def)
    then show "nlen c < ?base + 0"
      using hlNamesBelow_root[of d] by (simp add: hlNamesBelow_def)
  qed
  have Sagree: "\<forall>q \<in> set (hlFitchScopeRecord (set (hlFitchPremiseNumbers ?F)) body).
                  hlFitchScopeOf ?F (fst q) = snd q"
  proof
    fix q assume "q \<in> set (hlFitchScopeRecord (set (hlFitchPremiseNumbers ?F)) body)"
    then have "(fst q, snd q) \<in>
               set (hlFitchScopeRecord (set (hlFitchPremiseNumbers ?F)) ?F)"
      using F by (simp add: hlFitchScopeRecord_append)
    from hlFitchScopeOf_record[OF distF this] show "hlFitchScopeOf ?F (fst q) = snd q" .
  qed
  have bodyG: "\<forall>t \<in> set (hlFlattenFitch body).
                 \<forall>l. hlLookupLine ?Q (fst t) = Some l \<longrightarrow>
                     hlRuleOKG (hlScopeSrc ?F) ?Q l"
  proof (rule hlEmitDerivationFuel_scopeOK)
    show "size d < length (replicate (Suc (size d)) ())" by simp
  next
    show "hlEmitDerivationFuel (replicate (Suc (size d)) ()) ?base ?env
            (map (\<lambda>(source,n,phi). phi) ?env) ?first 0 d = (body,k,after,cnt)"
      using em by (simp add: hlEmitDerivation_def)
  next
    show "hlDerivationOK d" by (rule ok)
  next
    show "hlItemsCtx ?Q body" by (rule ictxB)
  next
    show "hlNamesBelow ?base 0 d" by (rule hlNamesBelow_root)
  next
    show "hlScopeBelow ?base 0 (map (\<lambda>(source,n,phi). phi) ?env)" by (rule scopeb)
  next
    show "hlEmitCtx ?Q ?env ?first d" by (rule ctx)
  next
    show "\<forall>t \<in> set (hlFlattenFitch body).
            \<forall>l. hlLookupLine ?Q (fst t) = Some l \<longrightarrow> hlRuleOK ?Q l" by (rule bodyOK)
  next
    show "\<forall>q \<in> set (hlFitchScopeRecord (set (hlFitchPremiseNumbers ?F)) body).
            hlFitchScopeOf ?F (fst q) = snd q" by (rule Sagree)
  next
    show "hlAssumptionConstants ?Q (set (hlFitchPremiseNumbers ?F)) \<subseteq>
          hlConstantsInScope (map (\<lambda>(source,n,phi). phi) ?env)" by (rule Sinv)
  next
    show "hlReferencedConstants ?Q (set (hlFitchPremiseNumbers ?F)) \<subseteq>
          hlConstantsInScope (map (\<lambda>(source,n,phi). phi) ?env)" by (rule Sref)
  next
    show "\<forall>m \<in> set (hlFitchPremiseNumbers ?F). m < ?first" by (rule Sbelow)
  next
    show "distinct (map hlLineNumber ?Q)" by (rule distQ)
  next
    show "0 < ?base" by simp
  qed
  have ruleOKG: "\<forall>l \<in> set ?Q. hlRuleOKG (hlScopeSrc ?F) ?Q l"
  proof
    fix l assume l: "l \<in> set ?Q"
    have look: "hlLookupLine ?Q (hlLineNumber l) = Some l"
      by (rule hlLookupLine_self[OF distQ l])
    have "hlLineNumber l \<in> set (map fst (hlFlattenFitch ?F))"
      using l nums by (metis image_eqI list.set_map)
    then obtain t where t: "t \<in> set (hlFlattenFitch ?F)" and tn: "fst t = hlLineNumber l"
      by auto
    from t flatF have "t \<in> set (hlFlattenFitch ?pre) \<or> t \<in> set (hlFlattenFitch body)"
      by blast
    then show "hlRuleOKG (hlScopeSrc ?F) ?Q l"
    proof
      assume tp: "t \<in> set (hlFlattenFitch ?pre)"
      obtain nn pp where t': "t = (nn,pp,HL_FPremise)"
        using tp by (force simp: hlPremiseFitchLines_flatten)
      from premise[OF tp[unfolded t']] obtain l' where
        l': "hlLookupLine ?Q nn = Some l'"
        and l'j: "hlJustification l' = HL_Assumption" by blast
      have num: "hlLineNumber l = nn" using tn t' by simp
      have same: "l' = l" using l' look num by simp
      show ?thesis
      proof (rule hlRuleOKG_of_hlRuleOK)
        show "hlRuleOK ?Q l" using ruleOK l by simp
      next
        show "hlJustification l \<noteq> HL_ForallIntro m" for m using l'j same by simp
      next
        show "hlJustification l \<noteq> HL_ExistsElim m a c" for m a c using l'j same by simp
      qed
    next
      assume "t \<in> set (hlFlattenFitch body)"
      then show ?thesis using bodyG look tn by auto
    qed
  qed
  have correctG: "hlCorrectG (hlScopeSrc ?F) ?Q"
    unfolding hlCorrectG_def list_all_iff hlLineOKG_def using ruleOKG structOK by blast
  show ?thesis using correct pclosed correctG by simp
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

theorem hlClassifiedDerivationToFitch_correct:
  assumes fn: "hlAssumptionsFunctional d"
      and ok: "hlDerivationOK d"
  shows "hlFitchCorrect (hlDerivationToFitch (hlClassifyAssumptions {} d))"
proof -
  let ?d = "hlClassifyAssumptions {} d"
  have fn': "hlAssumptionsFunctional ?d" using fn by simp
  have ok': "hlDerivationOK ?d" using ok by simp
  have root: "set (hlPremisesOf ?d) = set (hlOpenAssumptions ?d)"
    by (rule hlClassified_premises_open)
  have "hlCorrectG (hlScopeSrc (hlDerivationToFitch ?d)) (\<delta>\<^sub>H (hlDerivationToFitch ?d))"
    using hlDerivationToFitch_correct[OF fn' root ok'] by simp
  then show ?thesis
    unfolding hlFitchCorrect_def
    using hlClassifiedDerivationToFitch_verified[OF fn ok] by simp
qed

section \<open>The construction theorem\<close>

text \<open>A source assumption set is functional because \<^const>\<open>hlLookupLine\<close> is:
  the label of an open assumption is a line number, and a line carries one
  formula.  That discharges the one hypothesis the emitter side needed.\<close>

lemma hlSourceAssumptions_functional:
  assumes sub: "set (hlOpenAssumptions e) \<subseteq> hlSourceAssumptions P G"
  shows "hlAssumptionsFunctional e"
  unfolding hlAssumptionsFunctional_def
proof (intro ballI impI)
  fix nf mg
  assume nf: "nf \<in> set (hlOpenAssumptions e)"
    and mg: "mg \<in> set (hlOpenAssumptions e)" and eq: "fst nf = fst mg"
  from nf sub obtain l where
    l: "hlLookupLine P (fst nf) = Some l" "hlFormula l = snd nf"
    by (auto simp: hlSourceAssumptions_def)
  from mg sub obtain l' where
    l': "hlLookupLine P (fst mg) = Some l'" "hlFormula l' = snd mg"
    by (auto simp: hlSourceAssumptions_def)
  show "snd nf = snd mg" using l l' eq by simp
qed

theorem hlToDerivation_functional:
  assumes translated: "hlToDerivation P = Some d"
  shows "hlAssumptionsFunctional d"
proof -
  from translated obtain raw where nonempty: "P \<noteq> []"
    and correct: "hlCorrect P"
    and unfolded: "hlUnfoldDerivation (Suc (length P)) P
      (hlLineNumber (last P)) = Some raw"
    and classified: "d = hlClassifyAssumptions {} raw"
    by (auto simp: hlToDerivation_def hlVerifiedCorrect_def
        split: if_splits option.splits)
  have lookup: "hlLookupLine P (hlLineNumber (last P)) = Some (last P)"
    by (rule hlCorrect_lookup_self[OF correct]) (simp add: nonempty)
  have represents: "hlTreeRepresents P (hlLineNumber (last P)) raw"
    by (rule hlUnfoldDerivation_represents[OF correct unfolded])
  have opened: "set (hlOpenAssumptions raw) \<subseteq>
      hlSourceAssumptions P (hlReferences (last P))"
    using represents
    by (simp add: hlTreeRepresents_def hlPaperDependencyAt_lookup[OF lookup])
  show ?thesis using hlSourceAssumptions_functional[OF opened] classified by simp
qed

text \<open>G6.  Every nonempty paper-correct Lemmon proof is translated, by the
  checked translation, to a Fitch proof that passes every check, retains the
  conclusion, and asks for no premise the source did not already have.\<close>

theorem hlPaperCorrect_toFitch:
  assumes correct: "hlPaperCorrect P" and nonempty: "P \<noteq> []"
  shows "\<exists>route F. hlLemmonToFitchChecked P = Inr (route,F) \<and>
                   hlFitchCorrect F \<and>
                   set (hlFitchPremises F) \<subseteq> set (hlOpenPremises P) \<and>
                   hlFitchConclusion F = hlConclusion P \<and>
                   hlConclusion (\<delta>\<^sub>H F) = hlConclusion P"
proof -
  from hlPaperCorrect_toDerivation[OF correct nonempty] obtain d where
    td: "hlToDerivation P = Some d" and okd: "hlDerivationOK d"
    and concl: "hlConclusion P = Some (hlDerivationFormula d)"
    and prem: "set (map snd (hlPremisesOf d)) \<subseteq> set (hlOpenPremises P)" by blast
  from td obtain raw where classified: "d = hlClassifyAssumptions {} raw"
    by (auto simp: hlToDerivation_def split: if_splits option.splits)
  have fnd: "hlAssumptionsFunctional d" by (rule hlToDerivation_functional[OF td])
  have fnraw: "hlAssumptionsFunctional raw" using fnd classified by simp
  have okraw: "hlDerivationOK raw" using okd classified by simp
  let ?F = "hlDerivationToFitch d"
  have fc: "hlFitchCorrect ?F"
    using hlClassifiedDerivationToFitch_correct[OF fnraw okraw] classified by simp
  have pr: "set (hlFitchPremises ?F) \<subseteq> set (hlOpenPremises P)"
    using hlDerivationToFitch_premises[of d] prem by auto
  have cc: "hlConclusion (\<delta>\<^sub>H ?F) = hlConclusion P"
    using hlClassifiedDerivationToFitch_conclusion[of raw] classified concl
    by (simp add: hlFitchConclusion_delta)
  have tree: "hlViaTree P = Inr (HL_ViaTreeRoute,?F)"
    using td fc pr cc by (simp add: hlViaTree_def)
  show ?thesis
  proof (cases "hlLemmonToFitchDirect P")
    case (Inl e)
    then show ?thesis using tree fc pr cc
      by (auto simp: hlLemmonToFitchChecked_def hlFitchConclusion_delta)
  next
    case (Inr G)
    show ?thesis
    proof (cases "hlFitchCorrect G \<and>
                  set (hlFitchPremises G) \<subseteq> set (hlOpenPremises P) \<and>
                  hlConclusion (\<delta>\<^sub>H G) = hlConclusion P")
      case True
      then show ?thesis using Inr
        by (auto simp: hlLemmonToFitchChecked_def hlFitchConclusion_delta)
    next
      case False
      then show ?thesis using Inr tree fc pr cc
        by (auto simp: hlLemmonToFitchChecked_def hlFitchConclusion_delta)
    qed
  qed
qed

end
