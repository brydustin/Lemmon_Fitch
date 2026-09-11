(* Fresh eigenconstants: what the emitter's repair does and does not change. *)

theory LF_HLW_Fresh
  imports LF_HLW_Nesting
begin

section \<open>Name lengths bound the repair counter\<close>

lemma nlen_hlFreshIndex [simp]: "nlen (hlFreshIndex base k) = base + k"
  by (simp add: nlen_def hlFreshIndex_def)

lemma nlen_empty [simp]: "nlen (STR '''') = 0"
  by (simp add: nlen_def zero_literal.rep_eq)

lemma hlFreshIndex_nonempty:
  assumes "0 < base"
  shows "hlFreshIndex base k \<noteq> STR ''''"
proof
  assume e: "hlFreshIndex base k = STR ''''"
  have "base + k = nlen (hlFreshIndex base k)" by simp
  also have "... = 0" using e by simp
  finally show False using assms by simp
qed

definition hlNamesBelow :: "nat \<Rightarrow> nat \<Rightarrow> hl_derivation \<Rightarrow> bool" where
  "hlNamesBelow base cnt d \<longleftrightarrow> (\<forall>c \<in> hlDerivationConstants d. nlen c < base + cnt)"

lemma hlNamesBelow_mono:
  "hlNamesBelow base cnt d \<Longrightarrow> cnt \<le> cnt' \<Longrightarrow> hlNamesBelow base cnt' d"
  by (fastforce simp: hlNamesBelow_def)

lemma hlNamesBelow_sub:
  "hlNamesBelow base cnt d \<Longrightarrow> hlDerivationConstants e \<subseteq> hlDerivationConstants d \<Longrightarrow>
   hlNamesBelow base cnt e"
  by (auto simp: hlNamesBelow_def)

lemma hlNamesBelow_fresh:
  "hlNamesBelow base cnt d \<Longrightarrow> hlFreshIndex base cnt \<notin> hlDerivationConstants d"
  by (auto simp: hlNamesBelow_def)

lemma hlDerivationFormulas_sub:
  "e \<in> set (hlSubDerivations r) \<Longrightarrow>
   set (hlDerivationFormulas e) \<subseteq> set (hlDerivationFormulas (HL_Derivation f r))"
  by (cases r) auto

lemma hlDerivationConstants_sub:
  "e \<in> set (hlSubDerivations r) \<Longrightarrow>
   hlDerivationConstants e \<subseteq> hlDerivationConstants (HL_Derivation f r)"
  using hlDerivationFormulas_sub by (fastforce simp: hlDerivationConstants_def)

section \<open>The counter never runs backwards\<close>

lemma hlRepairDerivation_count_le:
  "hlRepairDerivation base count bad d = (count',pairs,d') \<Longrightarrow> count \<le> count'"
proof (induction bad arbitrary: count d count' pairs d')
  case Nil
  then show ?case by simp
next
  case (Cons old olds)
  from Cons.prems obtain c2 ps r where
    rec: "hlRepairDerivation base (Suc count) olds
            (hlRenameDerivation old (hlFreshIndex base count) d) = (c2,ps,r)"
    and eq: "count' = c2"
    by (auto simp: Let_def split: prod.splits)
  from Cons.IH[OF rec] eq show ?case by simp
qed

lemma hlCount_emit_list:
  assumes "hlEmitDerivationsUsing emit first count ds = (items,ns,after,cnt)"
      and step: "\<And>e fi ct out k af c2. emit fi ct e = (out,k,af,c2) \<Longrightarrow> ct \<le> c2"
  shows "count \<le> cnt"
  using assms(1)
proof (induction ds arbitrary: first count items ns after cnt)
  case Nil
  then show ?case by simp
next
  case (Cons e ds)
  from Cons.prems obtain out k mid c1 rest ks where
    hd: "emit first count e = (out,k,mid,c1)"
    and tl: "hlEmitDerivationsUsing emit mid c1 ds = (rest,ks,after,cnt)"
    by (auto simp: Let_def split: prod.splits)
  have "count \<le> c1" by (rule step[OF hd])
  moreover have "c1 \<le> cnt" by (rule Cons.IH[OF tl])
  ultimately show ?case by simp
qed

lemma hlEmitDerivationFuel_count_le:
  "hlEmitDerivationFuel fuel base env scope first count d = (items,n,after,cnt) \<Longrightarrow>
   count \<le> cnt"
proof (induction fuel arbitrary: env scope first count d items n after cnt)
  case Nil
  then show ?case by simp
next
  case (Cons u fuel)
  have list_count: "\<And>ds first count items ns after cnt.
    hlEmitDerivationsUsing
      (\<lambda>first count d. hlEmitDerivationFuel fuel base env scope first count d)
      first count ds = (items,ns,after,cnt) \<Longrightarrow> count \<le> cnt"
    by (rule hlCount_emit_list) (auto intro: Cons.IH)
  obtain phi rule where d: "d = HL_Derivation phi rule" by (cases d) auto
  from Cons.prems show ?case
    by (cases rule)
       (auto simp: d Let_def split: prod.splits if_splits
          dest!: Cons.IH list_count hlRepairDerivation_count_le
          intro: order_trans)
qed

section \<open>What the repair does to open assumptions and constants\<close>

lemma hlRenamePairsFormula_absent:
  "\<forall>op \<in> set pairs. fst op \<notin> hlConstantsInFormula f \<Longrightarrow>
   hlRenamePairsFormula pairs f = f"
  by (induction pairs arbitrary: f) (auto simp: hlRenameFormula_absent)

lemma hlRepairDerivation_pairs_fst:
  "hlRepairDerivation base count bad d = (count',pairs,d') \<Longrightarrow> map fst pairs = bad"
proof (induction bad arbitrary: count d count' pairs d')
  case Nil
  then show ?case by simp
next
  case (Cons old olds)
  from Cons.prems obtain c2 ps r where
    rec: "hlRepairDerivation base (Suc count) olds
            (hlRenameDerivation old (hlFreshIndex base count) d) = (c2,ps,r)"
    and eq: "pairs = (old,hlFreshIndex base count) # ps"
    by (auto simp: Let_def split: prod.splits)
  from Cons.IH[OF rec] eq show ?case by simp
qed

lemma hlOpenAssumptions_repair:
  "hlRepairDerivation base count bad d = (count',pairs,d') \<Longrightarrow>
   hlOpenAssumptions d' =
     map (\<lambda>nf. (fst nf, hlRenamePairsFormula pairs (snd nf))) (hlOpenAssumptions d)"
proof (induction bad arbitrary: count d count' pairs d')
  case Nil
  then show ?case by simp
next
  case (Cons old olds)
  let ?new = "hlFreshIndex base count"
  from Cons.prems obtain c2 ps r where
    rec: "hlRepairDerivation base (Suc count) olds
            (hlRenameDerivation old ?new d) = (c2,ps,r)"
    and eq: "pairs = (old,?new) # ps" "d' = r"
    by (auto simp: Let_def split: prod.splits)
  have "hlOpenAssumptions r =
        map (\<lambda>nf. (fst nf, hlRenamePairsFormula ps (snd nf)))
          (hlOpenAssumptions (hlRenameDerivation old ?new d))"
    by (rule Cons.IH[OF rec])
  also have "\<dots> = map (\<lambda>nf. (fst nf, hlRenamePairsFormula ((old,?new) # ps) (snd nf)))
          (hlOpenAssumptions d)"
    by (simp add: hlOpenAssumptions_rename map_map comp_def map_prod_def
        case_prod_beta)
  finally show ?case using eq by simp
qed

lemma hlOpenAssumptions_repair_unchanged:
  assumes rp: "hlRepairDerivation base count bad d = (count',pairs,d')"
      and fresh: "\<forall>old \<in> set bad. old \<notin> hlConstantsInScope (hlOpenFormulas d)"
  shows "hlOpenAssumptions d' = hlOpenAssumptions d"
proof -
  have "map (\<lambda>nf. (fst nf, hlRenamePairsFormula pairs (snd nf))) (hlOpenAssumptions d) =
        hlOpenAssumptions d"
  proof (rule map_idI)
    fix nf assume nf: "nf \<in> set (hlOpenAssumptions d)"
    have "\<forall>op \<in> set pairs. fst op \<notin> hlConstantsInFormula (snd nf)"
    proof
      fix op assume "op \<in> set pairs"
      then have "fst op \<in> set bad"
        using hlRepairDerivation_pairs_fst[OF rp] by (metis image_eqI list.set_map)
      then show "fst op \<notin> hlConstantsInFormula (snd nf)"
        using fresh nf by (force simp: hlConstantsInScope_def)
    qed
    from hlRenamePairsFormula_absent[OF this]
    show "(fst nf, hlRenamePairsFormula pairs (snd nf)) = nf" by (cases nf) simp
  qed
  with hlOpenAssumptions_repair[OF rp] show ?thesis by simp
qed

lemma hlNamesBelow_rename:
  assumes "hlNamesBelow base count d"
  shows "hlNamesBelow base (Suc count) (hlRenameDerivation old (hlFreshIndex base count) d)"
proof -
  have "nlen c < base + Suc count"
    if "c \<in> hlRenameName old (hlFreshIndex base count) ` hlDerivationConstants d" for c
  proof -
    from that obtain u where u: "u \<in> hlDerivationConstants d"
      and c: "c = hlRenameName old (hlFreshIndex base count) u" by blast
    show ?thesis
    proof (cases "u = old")
      case True
      then have "c = hlFreshIndex base count" using c by (simp add: hlRenameName_def)
      then show ?thesis by simp
    next
      case False
      then have "c = u" using c by (simp add: hlRenameName_def)
      then show ?thesis using assms u by (fastforce simp: hlNamesBelow_def)
    qed
  qed
  then show ?thesis by (simp add: hlNamesBelow_def hlRenameDerivation_constants)
qed

lemma hlNamesBelow_repair:
  "hlRepairDerivation base count bad d = (count',pairs,d') \<Longrightarrow>
   hlNamesBelow base count d \<Longrightarrow> hlNamesBelow base count' d'"
proof (induction bad arbitrary: count d count' pairs d')
  case Nil
  then show ?case by simp
next
  case (Cons old olds)
  from Cons.prems(1) obtain c2 ps r where
    rec: "hlRepairDerivation base (Suc count) olds
            (hlRenameDerivation old (hlFreshIndex base count) d) = (c2,ps,r)"
    and eq: "count' = c2" "d' = r"
    by (auto simp: Let_def split: prod.splits)
  show ?case
    using Cons.IH[OF rec hlNamesBelow_rename[OF Cons.prems(2)]] eq by simp
qed

lemma hlDerivationOK_repair:
  "hlRepairDerivation base count bad d = (count',pairs,d') \<Longrightarrow>
   hlDerivationOK d \<Longrightarrow> hlNamesBelow base count d \<Longrightarrow> 0 < base \<Longrightarrow>
   (\<forall>old \<in> set bad. old \<noteq> STR '''') \<Longrightarrow> hlDerivationOK d'"
proof (induction bad arbitrary: count d count' pairs d')
  case Nil
  then show ?case by simp
next
  case (Cons old olds)
  let ?new = "hlFreshIndex base count"
  from Cons.prems(1) obtain c2 ps r where
    rec: "hlRepairDerivation base (Suc count) olds
            (hlRenameDerivation old ?new d) = (c2,ps,r)"
    and eq: "d' = r"
    by (auto simp: Let_def split: prod.splits)
  have ok: "hlDerivationOK (hlRenameDerivation old ?new d)"
  proof (rule hlDerivationOK_rename[OF Cons.prems(2)])
    show "?new \<notin> hlDerivationConstants d" by (rule hlNamesBelow_fresh[OF Cons.prems(3)])
  next
    show "old \<noteq> STR ''''" using Cons.prems(5) by simp
  next
    show "?new \<noteq> STR ''''" by (rule hlFreshIndex_nonempty[OF Cons.prems(4)])
  qed
  show ?case
    using Cons.IH[OF rec ok hlNamesBelow_rename[OF Cons.prems(3)] Cons.prems(4)]
          Cons.prems(5) eq by simp
qed

section \<open>Abstraction only forgets the constants it abstracts\<close>

lemma hlAbstractMany_constants:
  "hlAbstractMany ps p = Some q \<Longrightarrow>
   hlConstantsInFormula p \<subseteq> hlConstantsInFormula q \<union> snd ` set ps"
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

section \<open>The repair only renames eigenconstants\<close>

text \<open>The constants a repair renames are, by construction, exactly the ones
  the rule's own freshness condition already forbids in the surrounding
  assumptions.  So the repair leaves the open assumptions alone, and the
  emitter's environment keeps describing them.\<close>

lemma set_hlForallRepairConstants:
  "set (hlForallRepairConstants scope goal d) =
   (hlConstantsInFormula (hlDerivationFormula d) - hlConstantsInFormula goal) \<inter>
     hlConstantsInScope scope"
  by (simp add: hlForallRepairConstants_def)

lemma set_hlExistsRepairConstants:
  "set (hlExistsRepairConstants scope asm src goal) =
   (hlConstantsInFormula asm -
     (hlConstantsInFormula (hlDerivationFormula src) \<union> hlConstantsInFormula goal)) \<inter>
     hlConstantsInScope scope"
  by (simp add: hlExistsRepairConstants_def)

lemma hlForallIntroStep_witness:
  assumes step: "hlForallIntroStep src goal G"
      and c: "c \<in> hlConstantsInFormula src"
      and nc: "c \<notin> hlConstantsInFormula goal"
  shows "c \<notin> hlConstantsInScope G \<and> c \<noteq> STR ''''"
proof -
  obtain xs core where xc: "hlCollectForalls goal = (xs,core)"
    by (cases "hlCollectForalls goal") auto
  from step xc obtain cs where
    abst: "hlAbstractMany (filter (\<lambda>xc. snd xc \<noteq> STR '''') (zip xs cs)) src = Some core"
    and fresh: "\<forall>w \<in> snd ` set (filter (\<lambda>xc. snd xc \<noteq> STR '''') (zip xs cs)).
                  w \<notin> hlConstantsInScope G"
    by (auto simp: hlForallIntroStep_def Let_def split: option.splits)
  have core: "hlConstantsInFormula core = hlConstantsInFormula goal"
    using hlCollectForalls_constants[of goal] xc by simp
  have "c \<in> snd ` set (filter (\<lambda>xc. snd xc \<noteq> STR '''') (zip xs cs))"
    using hlAbstractMany_constants[OF abst] c nc core by auto
  then show ?thesis using fresh by auto
qed

lemma hlExistsElimStep_witness:
  assumes step: "hlExistsElimStep src asm goal G"
      and c: "c \<in> hlConstantsInFormula asm"
      and n1: "c \<notin> hlConstantsInFormula src"
      and n2: "c \<notin> hlConstantsInFormula goal"
  shows "c \<notin> hlConstantsInScope G \<and> c \<noteq> STR ''''"
proof -
  obtain xs p where xp: "hlCollectExists src = (xs,p)"
    by (cases "hlCollectExists src") auto
  obtain ys q where yq: "hlCollectExists asm = (ys,q)"
    by (cases "hlCollectExists asm") auto
  from step xp yq obtain k cs where
    abst: "hlAbstractMany (filter (\<lambda>xc. snd xc \<noteq> STR '''') (zip (take k xs) cs)) asm
             = Some (hlPrefixExists ys p)"
    and fresh: "\<forall>w \<in> snd ` set (filter (\<lambda>xc. snd xc \<noteq> STR '''') (zip (take k xs) cs)).
                  w \<notin> hlConstantsInFormula goal \<and> w \<notin> hlConstantsInScope G"
    by (auto simp: hlExistsElimStep_def Let_def split: option.splits)
  have core: "hlConstantsInFormula (hlPrefixExists ys p) = hlConstantsInFormula src"
    using hlCollectExists_constants[of src] xp by simp
  have "c \<in> snd ` set (filter (\<lambda>xc. snd xc \<noteq> STR '''') (zip (take k xs) cs))"
    using hlAbstractMany_constants[OF abst] c n1 core by auto
  then show ?thesis using fresh by auto
qed

lemma hlForallRepair_fresh:
  assumes ok: "hlDerivationOK (HL_Derivation phi (HL_DForallI e))"
  shows "\<forall>old \<in> set (hlForallRepairConstants scope phi e).
           old \<notin> hlConstantsInScope (hlOpenFormulas e) \<and> old \<noteq> STR ''''"
proof
  fix old assume mem: "old \<in> set (hlForallRepairConstants scope phi e)"
  have c: "old \<in> hlConstantsInFormula (hlDerivationFormula e)"
    and nc: "old \<notin> hlConstantsInFormula phi"
    using mem by (auto simp: set_hlForallRepairConstants)
  have step: "hlForallIntroStep (hlDerivationFormula e) phi (hlOpenFormulas e)"
    using ok by simp
  show "old \<notin> hlConstantsInScope (hlOpenFormulas e) \<and> old \<noteq> STR ''''"
    by (rule hlForallIntroStep_witness[OF step c nc])
qed

lemma hlExistsRepair_fresh:
  assumes ok: "hlDerivationOK (HL_Derivation phi (HL_DExistsE src a af body))"
  shows "\<forall>old \<in> set (hlExistsRepairConstants scope af src phi).
           old \<notin> hlConstantsInScope
                    (map snd (hlDropAssumption a (hlOpenAssumptions body))) \<and>
           old \<noteq> STR ''''"
proof
  fix old assume mem: "old \<in> set (hlExistsRepairConstants scope af src phi)"
  have c: "old \<in> hlConstantsInFormula af"
    and n1: "old \<notin> hlConstantsInFormula (hlDerivationFormula src)"
    and n2: "old \<notin> hlConstantsInFormula phi"
    using mem by (auto simp: set_hlExistsRepairConstants)
  have step: "hlExistsElimStep (hlDerivationFormula src) af phi
                (map snd (hlDropAssumption a (hlOpenAssumptions body)))"
    using ok by simp
  show "old \<notin> hlConstantsInScope
               (map snd (hlDropAssumption a (hlOpenAssumptions body))) \<and>
        old \<noteq> STR ''''"
    by (rule hlExistsElimStep_witness[OF step c n1 n2])
qed

section \<open>The repair commutes with the node it is performed under\<close>

text \<open>The emitter repairs only the subderivation, but the rule check it has to
  satisfy is the one at the node above.  Since the repaired constants never
  occur in that node's own formula, repairing the subderivation is the same as
  repairing the whole node, and the node's correctness comes along.\<close>

lemma hlRepairDerivation_ForallI:
  assumes nophi: "\<forall>old \<in> set bad. old \<notin> hlConstantsInFormula phi"
      and rp: "hlRepairDerivation base count bad e = (count',pairs,e')"
  shows "hlRepairDerivation base count bad (HL_Derivation phi (HL_DForallI e))
           = (count',pairs,HL_Derivation phi (HL_DForallI e'))"
  using assms
proof (induction bad arbitrary: count e count' pairs e')
  case Nil
  then show ?case by simp
next
  case (Cons old olds)
  let ?new = "hlFreshIndex base count"
  from Cons.prems(2) obtain c2 ps r where
    rec: "hlRepairDerivation base (Suc count) olds
            (hlRenameDerivation old ?new e) = (c2,ps,r)"
    and eq: "count' = c2" "pairs = (old,?new) # ps" "e' = r"
    by (auto simp: Let_def split: prod.splits)
  have phi: "hlRenameFormula old ?new phi = phi"
    using Cons.prems(1) by (simp add: hlRenameFormula_absent)
  have "hlRepairDerivation base (Suc count) olds
          (HL_Derivation phi (HL_DForallI (hlRenameDerivation old ?new e)))
        = (c2,ps,HL_Derivation phi (HL_DForallI r))"
    by (rule Cons.IH[OF _ rec]) (use Cons.prems(1) in simp)
  then show ?case using eq phi by (simp add: Let_def)
qed

lemma hlRepairDerivation_ExistsE:
  assumes nophi: "\<forall>old \<in> set bad. old \<notin> hlConstantsInFormula phi"
      and rs: "hlRepairDerivation base count bad src = (cs,ps,src')"
      and rb: "hlRepairDerivation base count bad body = (cb,pb,body')"
  shows "hlRepairDerivation base count bad
           (HL_Derivation phi (HL_DExistsE src a af body))
         = (cb,pb,HL_Derivation phi
              (HL_DExistsE src' a (hlRenamePairsFormula pb af) body'))"
  using assms
proof (induction bad arbitrary: count src body af src' body' cs ps cb pb)
  case Nil
  then show ?case by simp
next
  case (Cons old olds)
  let ?new = "hlFreshIndex base count"
  from Cons.prems(2) obtain c2 ps2 r2 where
    recs: "hlRepairDerivation base (Suc count) olds
             (hlRenameDerivation old ?new src) = (c2,ps2,r2)"
    and eqs: "cs = c2" "ps = (old,?new) # ps2" "src' = r2"
    by (auto simp: Let_def split: prod.splits)
  from Cons.prems(3) obtain c3 ps3 r3 where
    recb: "hlRepairDerivation base (Suc count) olds
             (hlRenameDerivation old ?new body) = (c3,ps3,r3)"
    and eqb: "cb = c3" "pb = (old,?new) # ps3" "body' = r3"
    by (auto simp: Let_def split: prod.splits)
  have phi: "hlRenameFormula old ?new phi = phi"
    using Cons.prems(1) by (simp add: hlRenameFormula_absent)
  have "hlRepairDerivation base (Suc count) olds
          (HL_Derivation phi (HL_DExistsE (hlRenameDerivation old ?new src) a
             (hlRenameFormula old ?new af) (hlRenameDerivation old ?new body)))
        = (c3,ps3,HL_Derivation phi
             (HL_DExistsE r2 a (hlRenamePairsFormula ps3
                (hlRenameFormula old ?new af)) r3))"
    by (rule Cons.IH[OF _ recs recb]) (use Cons.prems(1) in simp)
  then show ?case using eqs eqb phi by (simp add: Let_def)
qed

lemma hlDerivationFormula_repair:
  "hlRepairDerivation base count bad e = (count',pairs,e') \<Longrightarrow>
   hlDerivationFormula e' = hlRenamePairsFormula pairs (hlDerivationFormula e)"
proof (induction bad arbitrary: count e count' pairs e')
  case Nil
  then show ?case by simp
next
  case (Cons old olds)
  let ?new = "hlFreshIndex base count"
  from Cons.prems obtain c2 ps r where
    rec: "hlRepairDerivation base (Suc count) olds
            (hlRenameDerivation old ?new e) = (c2,ps,r)"
    and eq: "pairs = (old,?new) # ps" "e' = r"
    by (auto simp: Let_def split: prod.splits)
  from Cons.IH[OF rec] eq show ?case by simp
qed

lemma hlDerivationFormula_repair_absent:
  assumes rp: "hlRepairDerivation base count bad e = (count',pairs,e')"
      and fresh: "\<forall>old \<in> set bad.
                    old \<notin> hlConstantsInFormula (hlDerivationFormula e)"
  shows "hlDerivationFormula e' = hlDerivationFormula e"
proof -
  have "\<forall>op \<in> set pairs. fst op \<notin> hlConstantsInFormula (hlDerivationFormula e)"
  proof
    fix op assume "op \<in> set pairs"
    then have "fst op \<in> set bad"
      using hlRepairDerivation_pairs_fst[OF rp] by (metis image_eqI list.set_map)
    then show "fst op \<notin> hlConstantsInFormula (hlDerivationFormula e)" using fresh by blast
  qed
  from hlRenamePairsFormula_absent[OF this] hlDerivationFormula_repair[OF rp]
  show ?thesis by simp
qed

lemma hlDropAssumption_repair:
  assumes rp: "hlRepairDerivation base count bad e = (count',pairs,e')"
      and fresh: "\<forall>old \<in> set bad.
        old \<notin> hlConstantsInScope (map snd (hlDropAssumption a (hlOpenAssumptions e)))"
  shows "hlDropAssumption a (hlOpenAssumptions e') =
         hlDropAssumption a (hlOpenAssumptions e)"
proof -
  have img: "hlOpenAssumptions e' =
      map (\<lambda>nf. (fst nf, hlRenamePairsFormula pairs (snd nf))) (hlOpenAssumptions e)"
    by (rule hlOpenAssumptions_repair[OF rp])
  have "hlDropAssumption a (hlOpenAssumptions e') =
        map (\<lambda>nf. (fst nf, hlRenamePairsFormula pairs (snd nf)))
          (hlDropAssumption a (hlOpenAssumptions e))"
    by (simp add: img filter_map comp_def)
  also have "\<dots> = hlDropAssumption a (hlOpenAssumptions e)"
  proof (rule map_idI)
    fix nf assume nf: "nf \<in> set (hlDropAssumption a (hlOpenAssumptions e))"
    have "\<forall>op \<in> set pairs. fst op \<notin> hlConstantsInFormula (snd nf)"
    proof
      fix op assume "op \<in> set pairs"
      then have "fst op \<in> set bad"
        using hlRepairDerivation_pairs_fst[OF rp] by (metis image_eqI list.set_map)
      then show "fst op \<notin> hlConstantsInFormula (snd nf)"
        using fresh nf by (force simp: hlConstantsInScope_def)
    qed
    from hlRenamePairsFormula_absent[OF this]
    show "(fst nf, hlRenamePairsFormula pairs (snd nf)) = nf" by (cases nf) simp
  qed
  finally show ?thesis .
qed

end
