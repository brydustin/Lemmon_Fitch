(*  Title:      LF_Semantics.thy

    A standard model theory for the object language, soundness of derivation
    trees and the Lemmon system, and a semantic audit of the Fitch turnstile.
    The reconstructed rules are sound, but the intended Fitch soundness theorem
    is false because the whole proof may end in an undischarged top-level
    subproof.
*)

theory LF_Semantics
  imports LF_Faithful LF_Examples
begin

section \<open>Models\<close>

type_synonym 'a valu = "vr \<Rightarrow> 'a"

record 'a interp =
  iNm :: "nm \<Rightarrow> 'a"
  iPr :: "pr \<Rightarrow> 'a list \<Rightarrow> bool"

primrec evalT :: "'a interp \<Rightarrow> 'a valu \<Rightarrow> trm \<Rightarrow> 'a" where
  "evalT I \<rho> (Nm a) = iNm I a"
| "evalT I \<rho> (Vr x) = \<rho> x"

primrec sat :: "'a interp \<Rightarrow> 'a valu \<Rightarrow> fm \<Rightarrow> bool" where
  "sat I \<rho> (Atom P ts) \<longleftrightarrow> iPr I P (map (evalT I \<rho>) ts)"
| "sat I \<rho> (Eqf t u) \<longleftrightarrow> evalT I \<rho> t = evalT I \<rho> u"
| "sat I \<rho> Bot \<longleftrightarrow> False"
| "sat I \<rho> (Neg p) \<longleftrightarrow> \<not> sat I \<rho> p"
| "sat I \<rho> (Conj p q) \<longleftrightarrow> sat I \<rho> p \<and> sat I \<rho> q"
| "sat I \<rho> (Disj p q) \<longleftrightarrow> sat I \<rho> p \<or> sat I \<rho> q"
| "sat I \<rho> (Impl p q) \<longleftrightarrow> (sat I \<rho> p \<longrightarrow> sat I \<rho> q)"
| "sat I \<rho> (Iff p q) \<longleftrightarrow> (sat I \<rho> p \<longleftrightarrow> sat I \<rho> q)"
| "sat I \<rho> (Uni x p) \<longleftrightarrow> (\<forall>v. sat I (\<rho>(x := v)) p)"
| "sat I \<rho> (Exi x p) \<longleftrightarrow> (\<exists>v. sat I (\<rho>(x := v)) p)"

definition modelEntails :: "'a interp \<Rightarrow> fm list \<Rightarrow> fm \<Rightarrow> bool" where
  "modelEntails I \<Gamma> \<phi> \<longleftrightarrow>
     (\<forall>\<rho>. (\<forall>\<psi> \<in> set \<Gamma>. sat I \<rho> \<psi>) \<longrightarrow> sat I \<rho> \<phi>)"

section \<open>Semantic substitution and relevance\<close>

lemma evalT_inst:
  "evalT I \<rho> (inst_t x a t) = evalT I (\<rho>(x := iNm I a)) t"
  by (cases t) auto

lemma evalTs_inst:
  "map (evalT I \<rho>) (map (inst_t x a) ts) =
   map (evalT I (\<rho>(x := iNm I a))) ts"
  by (induction ts) (simp_all add: evalT_inst fun_upd_def)

lemma sat_inst:
  "sat I \<rho> (inst x a p) \<longleftrightarrow> sat I (\<rho>(x := iNm I a)) p"
proof (induction p arbitrary: \<rho>)
  case (Atom P ts)
  then show ?case by (simp only: inst.simps sat.simps evalTs_inst)
next
  case (Eqf t u)
  then show ?case by (metis evalT_inst inst.simps(2) sat.simps(2))
next
  case Bot
  then show ?case by simp
next
  case (Neg p)
  then show ?case by simp
next
  case (Conj p q)
  then show ?case by simp
next
  case (Disj p q)
  then show ?case by simp
next
  case (Impl p q)
  then show ?case by simp
next
  case (Iff p q)
  then show ?case by simp
next
  case (Uni z p)
  show ?case
  proof (cases "x = z")
    case True
    then show ?thesis by (subst True) simp
  next
    case False
    have point: "\<And>v. sat I (\<rho>(z := v)) (inst x a p) \<longleftrightarrow>
        sat I ((\<rho>(x := iNm I a))(z := v)) p"
    proof -
      fix v
      have "sat I (\<rho>(z := v)) (inst x a p) \<longleftrightarrow>
          sat I ((\<rho>(z := v))(x := iNm I a)) p"
        by (rule Uni.IH)
      also have "... \<longleftrightarrow> sat I ((\<rho>(x := iNm I a))(z := v)) p"
        using False by (simp add: fun_upd_twist)
      finally show "sat I (\<rho>(z := v)) (inst x a p) \<longleftrightarrow>
          sat I ((\<rho>(x := iNm I a))(z := v)) p" .
    qed
    with False show ?thesis
      by (simp only: inst.simps sat.simps if_False point)
  qed
next
  case (Exi z p)
  show ?case
  proof (cases "x = z")
    case True
    then show ?thesis by (subst True) simp
  next
    case False
    have point: "\<And>v. sat I (\<rho>(z := v)) (inst x a p) \<longleftrightarrow>
        sat I ((\<rho>(x := iNm I a))(z := v)) p"
    proof -
      fix v
      have "sat I (\<rho>(z := v)) (inst x a p) \<longleftrightarrow>
          sat I ((\<rho>(z := v))(x := iNm I a)) p"
        by (rule Exi.IH)
      also have "... \<longleftrightarrow> sat I ((\<rho>(x := iNm I a))(z := v)) p"
        using False by (simp add: fun_upd_twist)
      finally show "sat I (\<rho>(z := v)) (inst x a p) \<longleftrightarrow>
          sat I ((\<rho>(x := iNm I a))(z := v)) p" .
    qed
    with False show ?thesis
      by (simp only: inst.simps sat.simps if_False point)
  qed
qed

lemma evalT_fvs:
  assumes "x \<notin> set (fvs_t t)"
  shows "evalT I (\<rho>(x := v)) t = evalT I \<rho> t"
  using assms by (cases t) auto

lemma evalT_cong:
  assumes "\<And>y. y \<in> set (fvs_t t) \<Longrightarrow> \<rho> y = \<sigma> y"
  shows "evalT I \<rho> t = evalT I \<sigma> t"
  using assms by (cases t) auto

lemma evalTs_cong:
  assumes "\<forall>t \<in> set ts. \<forall>y \<in> set (fvs_t t). \<rho> y = \<sigma> y"
  shows "map (evalT I \<rho>) ts = map (evalT I \<sigma>) ts"
  using assms by (induction ts) (auto intro: evalT_cong)

lemma sat_cong:
  assumes "\<And>y. y \<in> set (fvs p) \<Longrightarrow> \<rho> y = \<sigma> y"
  shows "sat I \<rho> p \<longleftrightarrow> sat I \<sigma> p"
  using assms
proof (induction p arbitrary: \<rho> \<sigma>)
  case (Atom P ts)
  have "map (evalT I \<rho>) ts = map (evalT I \<sigma>) ts"
    by (rule evalTs_cong) (use Atom.prems in auto)
  then show ?case by (metis sat.simps(1))
next
  case (Eqf t u)
  have t: "evalT I \<rho> t = evalT I \<sigma> t"
    by (rule evalT_cong) (use Eqf.prems in auto)
  have u: "evalT I \<rho> u = evalT I \<sigma> u"
    by (rule evalT_cong) (use Eqf.prems in auto)
  show ?case using t u by simp
next
  case Bot
  then show ?case by simp
next
  case (Neg p)
  have p: "sat I \<rho> p \<longleftrightarrow> sat I \<sigma> p"
    by (rule Neg.IH) (use Neg.prems in simp)
  show ?case using p by simp
next
  case (Conj p q)
  have p: "sat I \<rho> p \<longleftrightarrow> sat I \<sigma> p"
    by (rule Conj.IH(1)) (use Conj.prems in auto)
  have q: "sat I \<rho> q \<longleftrightarrow> sat I \<sigma> q"
    by (rule Conj.IH(2)) (use Conj.prems in auto)
  show ?case using p q by simp
next
  case (Disj p q)
  have p: "sat I \<rho> p \<longleftrightarrow> sat I \<sigma> p"
    by (rule Disj.IH(1)) (use Disj.prems in auto)
  have q: "sat I \<rho> q \<longleftrightarrow> sat I \<sigma> q"
    by (rule Disj.IH(2)) (use Disj.prems in auto)
  show ?case using p q by simp
next
  case (Impl p q)
  have p: "sat I \<rho> p \<longleftrightarrow> sat I \<sigma> p"
    by (rule Impl.IH(1)) (use Impl.prems in auto)
  have q: "sat I \<rho> q \<longleftrightarrow> sat I \<sigma> q"
    by (rule Impl.IH(2)) (use Impl.prems in auto)
  show ?case using p q by simp
next
  case (Iff p q)
  have p: "sat I \<rho> p \<longleftrightarrow> sat I \<sigma> p"
    by (rule Iff.IH(1)) (use Iff.prems in auto)
  have q: "sat I \<rho> q \<longleftrightarrow> sat I \<sigma> q"
    by (rule Iff.IH(2)) (use Iff.prems in auto)
  show ?case using p q by simp
next
  case (Uni z p)
  have agree: "\<And>v y. y \<in> set (fvs p) \<Longrightarrow>
      (\<rho>(z := v)) y = (\<sigma>(z := v)) y"
  proof -
    fix v y assume yf: "y \<in> set (fvs p)"
    show "(\<rho>(z := v)) y = (\<sigma>(z := v)) y"
    proof (cases "y = z")
      case False
      from Uni.prems [of y] yf False show ?thesis by simp
    qed simp
  qed
  have body: "\<And>v. sat I (\<rho>(z := v)) p \<longleftrightarrow> sat I (\<sigma>(z := v)) p"
    by (rule Uni.IH) (rule agree)
  show ?case by (simp only: sat.simps body)
next
  case (Exi z p)
  have agree: "\<And>v y. y \<in> set (fvs p) \<Longrightarrow>
      (\<rho>(z := v)) y = (\<sigma>(z := v)) y"
  proof -
    fix v y assume yf: "y \<in> set (fvs p)"
    show "(\<rho>(z := v)) y = (\<sigma>(z := v)) y"
    proof (cases "y = z")
      case False
      from Exi.prems [of y] yf False show ?thesis by simp
    qed simp
  qed
  have body: "\<And>v. sat I (\<rho>(z := v)) p \<longleftrightarrow> sat I (\<sigma>(z := v)) p"
    by (rule Exi.IH) (rule agree)
  show ?case by (simp only: sat.simps body)
qed

lemma sat_fvs:
  assumes "x \<notin> set (fvs p)"
  shows "sat I (\<rho>(x := v)) p \<longleftrightarrow> sat I \<rho> p"
  by (rule sat_cong) (use assms in auto)

lemma evalT_names:
  assumes "a \<notin> set (names_t t)"
  shows "evalT (I\<lparr>iNm := (iNm I)(a := v)\<rparr>) \<rho> t = evalT I \<rho> t"
  using assms by (cases t) auto

lemma evalTs_names:
  assumes "\<forall>t \<in> set ts. a \<notin> set (names_t t)"
  shows "map (evalT (I\<lparr>iNm := (iNm I)(a := v)\<rparr>) \<rho>) ts =
         map (evalT I \<rho>) ts"
  using assms by (induction ts) (simp_all add: evalT_names)

lemma sat_names:
  assumes "\<not> occurs a p"
  shows "sat (I\<lparr>iNm := (iNm I)(a := v)\<rparr>) \<rho> p \<longleftrightarrow> sat I \<rho> p"
  using assms
  by (induction p arbitrary: \<rho>) (simp_all add: evalT_names evalTs_names)

lemma eqsub_t_sound:
  assumes "eqsub_t a b t u" and "iNm I a = iNm I b"
  shows "evalT I \<rho> t = evalT I \<rho> u"
  using assms by (cases t; cases u) auto

lemma eqsub_ts_sound:
  assumes "list_all2 (eqsub_t a b) ts us" and "iNm I a = iNm I b"
  shows "map (evalT I \<rho>) ts = map (evalT I \<rho>) us"
  using assms by (induction rule: list_all2_induct) (auto intro: eqsub_t_sound)

lemma eqsub_sound:
  assumes "eqsub a b p q" and "iNm I a = iNm I b"
  shows "sat I \<rho> p \<longleftrightarrow> sat I \<rho> q"
  using assms
proof (induction p arbitrary: q \<rho>)
  case (Atom P ts)
  then obtain Q us where q: "q = Atom Q us" by (cases q) auto
  from Atom.prems q have pq: "P = Q" and rel: "list_all2 (eqsub_t a b) ts us" by auto
  have "map (evalT I \<rho>) ts = map (evalT I \<rho>) us"
    by (rule eqsub_ts_sound [OF rel Atom.prems(2)])
  with pq q show ?case by simp
next
  case (Eqf t u)
  then obtain t' u' where q: "q = Eqf t' u'" by (cases q) auto
  from Eqf.prems q have t: "eqsub_t a b t t'" and u: "eqsub_t a b u u'" by auto
  have et: "evalT I \<rho> t = evalT I \<rho> t'"
    by (rule eqsub_t_sound [OF t Eqf.prems(2)])
  have eu: "evalT I \<rho> u = evalT I \<rho> u'"
    by (rule eqsub_t_sound [OF u Eqf.prems(2)])
  with et q show ?case by simp
next
  case Bot
  then show ?case by (cases q) auto
next
  case (Neg p)
  then obtain p' where q: "q = Neg p'" by (cases q) auto
  from Neg.prems q have rel: "eqsub a b p p'" by auto
  have "sat I \<rho> p \<longleftrightarrow> sat I \<rho> p'"
    by (rule Neg.IH [OF rel Neg.prems(2)])
  with q show ?case by simp
next
  case (Conj p r)
  then obtain p' r' where q: "q = Conj p' r'" by (cases q) auto
  from Conj.prems q have p: "eqsub a b p p'" and r: "eqsub a b r r'" by auto
  have ep: "sat I \<rho> p \<longleftrightarrow> sat I \<rho> p'"
    by (rule Conj.IH(1) [OF p Conj.prems(2)])
  have er: "sat I \<rho> r \<longleftrightarrow> sat I \<rho> r'"
    by (rule Conj.IH(2) [OF r Conj.prems(2)])
  with ep q show ?case by simp
next
  case (Disj p r)
  then obtain p' r' where q: "q = Disj p' r'" by (cases q) auto
  from Disj.prems q have p: "eqsub a b p p'" and r: "eqsub a b r r'" by auto
  have ep: "sat I \<rho> p \<longleftrightarrow> sat I \<rho> p'"
    by (rule Disj.IH(1) [OF p Disj.prems(2)])
  have er: "sat I \<rho> r \<longleftrightarrow> sat I \<rho> r'"
    by (rule Disj.IH(2) [OF r Disj.prems(2)])
  with ep q show ?case by simp
next
  case (Impl p r)
  then obtain p' r' where q: "q = Impl p' r'" by (cases q) auto
  from Impl.prems q have p: "eqsub a b p p'" and r: "eqsub a b r r'" by auto
  have ep: "sat I \<rho> p \<longleftrightarrow> sat I \<rho> p'"
    by (rule Impl.IH(1) [OF p Impl.prems(2)])
  have er: "sat I \<rho> r \<longleftrightarrow> sat I \<rho> r'"
    by (rule Impl.IH(2) [OF r Impl.prems(2)])
  with ep q show ?case by simp
next
  case (Iff p r)
  then obtain p' r' where q: "q = Iff p' r'" by (cases q) auto
  from Iff.prems q have p: "eqsub a b p p'" and r: "eqsub a b r r'" by auto
  have ep: "sat I \<rho> p \<longleftrightarrow> sat I \<rho> p'"
    by (rule Iff.IH(1) [OF p Iff.prems(2)])
  have er: "sat I \<rho> r \<longleftrightarrow> sat I \<rho> r'"
    by (rule Iff.IH(2) [OF r Iff.prems(2)])
  with ep q show ?case by simp
next
  case (Uni x p)
  then obtain y p' where q: "q = Uni y p'" by (cases q) auto
  from Uni.prems q have xy: "x = y" and rel: "eqsub a b p p'" by auto
  have body: "\<And>v. sat I (\<rho>(x := v)) p \<longleftrightarrow> sat I (\<rho>(x := v)) p'"
    by (rule Uni.IH [OF rel Uni.prems(2)])
  with xy q show ?case by simp
next
  case (Exi x p)
  then obtain y p' where q: "q = Exi y p'" by (cases q) auto
  from Exi.prems q have xy: "x = y" and rel: "eqsub a b p p'" by auto
  have body: "\<And>v. sat I (\<rho>(x := v)) p \<longleftrightarrow> sat I (\<rho>(x := v)) p'"
    by (rule Exi.IH [OF rel Exi.prems(2)])
  with xy q show ?case by simp
qed

section \<open>Semantic assumptions and quantifier side conditions\<close>

definition holds :: "'a interp \<Rightarrow> 'a valu \<Rightarrow> fm list \<Rightarrow> bool" where
  "holds I \<rho> \<Gamma> \<longleftrightarrow> (\<forall>p \<in> set \<Gamma>. sat I \<rho> p)"

lemma holds_Nil [simp]: "holds I \<rho> []"
  by (simp add: holds_def)

lemma holds_singleton [simp]: "holds I \<rho> [p] \<longleftrightarrow> sat I \<rho> p"
  by (simp add: holds_def)

lemma holds_append [simp]:
  "holds I \<rho> (\<Gamma> @ \<Delta>) \<longleftrightarrow> holds I \<rho> \<Gamma> \<and> holds I \<rho> \<Delta>"
  by (auto simp: holds_def)

lemma holds_names_update:
  assumes "arbitrary_in a \<Gamma>" and "holds I \<rho> \<Gamma>"
  shows "holds (I\<lparr>iNm := (iNm I)(a := v)\<rparr>) \<rho> \<Gamma>"
proof (unfold holds_def, intro ballI)
  fix p assume p: "p \<in> set \<Gamma>"
  from assms(1) p have fresh: "\<not> occurs a p" unfolding arbitrary_in_def by auto
  from assms(2) p have old: "sat I \<rho> p" unfolding holds_def by auto
  from sat_names [OF fresh, of I v \<rho>] old
  show "sat (I\<lparr>iNm := (iNm I)(a := v)\<rparr>) \<rho> p" by simp
qed

lemma holds_discharge:
  assumes drop: "holds I \<rho> (map snd (drop_label a (openAsms d)))"
      and fa: "sat I \<rho> f"
      and ok: "dischargeOK a f d"
  shows "holds I \<rho> (openFms d)"
proof (unfold holds_def, intro ballI)
  fix p assume "p \<in> set (openFms d)"
  then obtain n where np: "(n, p) \<in> set (openAsms d)" by auto
  show "sat I \<rho> p"
  proof (cases "n = a")
    case True
    with ok np have "p = f" unfolding dischargeOK_def by fastforce
    with fa show ?thesis by simp
  next
    case False
    with drop np show ?thesis unfolding holds_def by auto
  qed
qed

lemma instOK_forall_sound:
  assumes ok: "instOK x p q" and all: "sat I \<rho> (Uni x p)"
  shows "sat I \<rho> q"
proof (cases "x \<in> set (fvs p)")
  case True
  from True ok have ne: "instWitnesses x p q \<noteq> []" unfolding instOK_def by simp
  let ?a = "hd (instWitnesses x p q)"
  have a: "?a \<in> set (instWitnesses x p q)" using ne by simp
  have inst: "inst x ?a p = q" by (rule instWitnesses_sound [OF a])
  from all have "sat I (\<rho>(x := iNm I ?a)) p" by simp
  with sat_inst [of I \<rho> x ?a p] inst show ?thesis by simp
next
  case False
  with ok have q: "q = p" unfolding instOK_def by simp
  from all have body: "\<forall>v. sat I (\<rho>(x := v)) p" by simp
  have "sat I (\<rho>(x := \<rho> x)) p" by (rule body [rule_format])
  with q show ?thesis by simp
qed

lemma instOK_exists_sound:
  assumes ok: "instOK x p q" and one: "sat I \<rho> q"
  shows "sat I \<rho> (Exi x p)"
proof (cases "x \<in> set (fvs p)")
  case True
  from True ok have ne: "instWitnesses x p q \<noteq> []" unfolding instOK_def by simp
  let ?a = "hd (instWitnesses x p q)"
  have a: "?a \<in> set (instWitnesses x p q)" using ne by simp
  have inst: "inst x ?a p = q" by (rule instWitnesses_sound [OF a])
  from one inst sat_inst [of I \<rho> x ?a p]
  have body: "sat I (\<rho>(x := iNm I ?a)) p" by simp
  show ?thesis
    by (simp only: sat.simps; rule exI [of _ "iNm I ?a"]; rule body)
next
  case False
  with ok have q: "q = p" unfolding instOK_def by simp
  from one q have body: "sat I (\<rho>(x := \<rho> x)) p" by simp
  show ?thesis
    by (simp only: sat.simps; rule exI [of _ "\<rho> x"]; rule body)
qed

lemma genOK_sound:
  fixes I :: "'a interp"
  assumes ok: "genOK x p q \<Gamma>"
      and valid: "\<And>(J :: 'a interp) \<sigma>. holds J \<sigma> \<Gamma> \<Longrightarrow> sat J \<sigma> q"
      and hs: "holds I \<rho> \<Gamma>"
  shows "sat I \<rho> (Uni x p)"
proof (cases "x \<in> set (fvs p)")
  case False
  with ok have q: "q = p" unfolding genOK_def by simp
  have p: "sat I \<rho> p" using valid [OF hs] q by simp
  show ?thesis
  proof (simp only: sat.simps, rule allI)
    fix v
    from sat_fvs [OF False, of I \<rho> v] p show "sat I (\<rho>(x := v)) p" by simp
  qed
next
  case True
  with ok obtain a where aw: "a \<in> set (instWitnesses x p q)"
      and fresh: "\<not> occurs a p" and arb: "arbitrary_in a \<Gamma>"
    unfolding genOK_def by auto
  have inst: "inst x a p = q" by (rule instWitnesses_sound [OF aw])
  show ?thesis
  proof (simp only: sat.simps, rule allI)
    fix v
    define J where "J = I\<lparr>iNm := (iNm I)(a := v)\<rparr>"
    have hJ: "holds J \<rho> \<Gamma>"
      unfolding J_def by (rule holds_names_update [OF arb hs])
    have qJ: "sat J \<rho> q" by (rule valid [OF hJ])
    from qJ inst sat_inst [of J \<rho> x a p]
    have pJ: "sat J (\<rho>(x := iNm J a)) p" by simp
    have name: "iNm J a = v" by (simp add: J_def)
    from pJ name have "sat J (\<rho>(x := v)) p" by simp
    moreover from sat_names [OF fresh, of I v "\<rho>(x := v)"]
    have "sat J (\<rho>(x := v)) p \<longleftrightarrow> sat I (\<rho>(x := v)) p"
      by (simp add: J_def)
    ultimately show "sat I (\<rho>(x := v)) p" by simp
  qed
qed

lemma witOK_sound:
  fixes I :: "'a interp"
  assumes ok: "witOK x p f \<phi> (\<Delta> @ \<Gamma>)"
      and major: "sat I \<rho> (Exi x p)"
      and branch: "\<And>(J :: 'a interp) \<sigma>.
          holds J \<sigma> \<Gamma> \<Longrightarrow> sat J \<sigma> f \<Longrightarrow> sat J \<sigma> \<phi>"
      and hs: "holds I \<rho> (\<Delta> @ \<Gamma>)"
  shows "sat I \<rho> \<phi>"
proof (cases "x \<in> set (fvs p)")
  case False
  with ok have f: "f = p" unfolding witOK_def by simp
  from major have "\<exists>v. sat I (\<rho>(x := v)) p" by simp
  then obtain v where pv: "sat I (\<rho>(x := v)) p" by blast
  from sat_fvs [OF False, of I \<rho> v] pv have p: "sat I \<rho> p" by simp
  from hs have "holds I \<rho> \<Gamma>" by simp
  from branch [OF this] p f show ?thesis by simp
next
  case True
  with ok obtain b where bw: "b \<in> set (instWitnesses x p f)"
      and freshp: "\<not> occurs b p" and freshphi: "\<not> occurs b \<phi>"
      and arb: "arbitrary_in b (\<Delta> @ \<Gamma>)"
    unfolding witOK_def by auto
  have inst: "inst x b p = f" by (rule instWitnesses_sound [OF bw])
  from major have "\<exists>v. sat I (\<rho>(x := v)) p" by simp
  then obtain v where pv: "sat I (\<rho>(x := v)) p" by blast
  define J where "J = I\<lparr>iNm := (iNm I)(b := v)\<rparr>"
  have hJ: "holds J \<rho> (\<Delta> @ \<Gamma>)"
    unfolding J_def by (rule holds_names_update [OF arb hs])
  then have hGamma: "holds J \<rho> \<Gamma>" by simp
  from sat_names [OF freshp, of I v "\<rho>(x := v)"] pv
  have pJ: "sat J (\<rho>(x := v)) p" by (simp add: J_def)
  have name: "iNm J b = v" by (simp add: J_def)
  from pJ name have "sat J (\<rho>(x := iNm J b)) p" by simp
  with sat_inst [of J \<rho> x b p] inst have fJ: "sat J \<rho> f" by simp
  have phiJ: "sat J \<rho> \<phi>" by (rule branch [OF hGamma fJ])
  from sat_names [OF freshphi, of I v \<rho>] phiJ
  show ?thesis by (simp add: J_def)
qed

lemma genOK_instance_sound:
  fixes I :: "'a interp"
  assumes "genOK x p q \<Gamma>"
      and "\<And>(J :: 'a interp) \<sigma>. holds J \<sigma> \<Gamma> \<Longrightarrow> sat J \<sigma> q"
      and "holds I \<rho> \<Gamma>"
  shows "sat I (\<rho>(x := v)) p"
proof -
  from genOK_sound [OF assms] have "sat I \<rho> (Uni x p)" .
  then have "\<forall>w. sat I (\<rho>(x := w)) p" by simp
  then show ?thesis by (rule allE)
qed

lemma instOK_exists_witness:
  assumes "instOK x p q" and "sat I \<rho> q"
  shows "\<exists>v. sat I (\<rho>(x := v)) p"
  using instOK_exists_sound [OF assms] by simp

lemma eqsub_sat:
  assumes "eqsub a b p q" and "iNm I a = iNm I b" and "sat I \<rho> p"
  shows "sat I \<rho> q"
  using eqsub_sound [OF assms(1,2), of \<rho>] assms(3) by simp

lemma orElim_discharge_sound:
  assumes major: "sat I \<rho> f1 \<or> sat I \<rho> f2"
      and left: "holds I \<rho> (openFms d1) \<Longrightarrow> sat I \<rho> \<phi>"
      and right: "holds I \<rho> (openFms d2) \<Longrightarrow> sat I \<rho> \<phi>"
      and drop1: "holds I \<rho> (map snd (drop_label a1 (openAsms d1)))"
      and drop2: "holds I \<rho> (map snd (drop_label a2 (openAsms d2)))"
      and ok1: "dischargeOK a1 f1 d1" and ok2: "dischargeOK a2 f2 d2"
  shows "sat I \<rho> \<phi>"
proof -
  from major consider (left) "sat I \<rho> f1" | (right) "sat I \<rho> f2" by auto
  then show ?thesis
  proof cases
    case left
    from holds_discharge [OF drop1 left ok1] show ?thesis by (rule assms(2))
  next
    case right
    from holds_discharge [OF drop2 right ok2] show ?thesis by (rule assms(3))
  qed
qed

lemma existsElim_discharge_sound:
  fixes I :: "'a interp"
  assumes major: "\<exists>v. sat I (\<rho>(x := v)) p"
      and branch: "\<And>(J :: 'a interp) \<sigma>.
          holds J \<sigma> (openFms d) \<Longrightarrow> sat J \<sigma> \<phi>"
      and hs0: "holds I \<rho> \<Delta>"
      and drop: "holds I \<rho> (map snd (drop_label a (openAsms d)))"
      and discharge: "dischargeOK a f d"
      and witness: "witOK x p f \<phi>
          (\<Delta> @ map snd (drop_label a (openAsms d)))"
  shows "sat I \<rho> \<phi>"
proof -
  from major have major': "sat I \<rho> (Exi x p)" by simp
  show ?thesis
  proof (rule witOK_sound [OF witness major'])
  fix J :: "'a interp" and \<sigma>
  assume hdrop: "holds J \<sigma> (map snd (drop_label a (openAsms d)))"
      and f: "sat J \<sigma> f"
  from holds_discharge [OF hdrop f discharge] show "sat J \<sigma> \<phi>"
    by (rule branch)
  next
    show "holds I \<rho> (\<Delta> @ map snd (drop_label a (openAsms d)))"
      using hs0 drop by simp
  qed
qed

section \<open>Soundness of derivation trees\<close>

theorem derivOK_sound:
  assumes "derivOK d" and "holds I \<rho> (openFms d)"
  shows "sat I \<rho> (dForm d)"
  using assms
  apply (induction d arbitrary: I \<rho> rule: derivOK.induct)
  apply (auto split: fm.splits trm.splits
      intro: holds_discharge instOK_forall_sound instOK_exists_sound
        genOK_sound witOK_sound eqsub_sound genOK_instance_sound
        instOK_exists_witness eqsub_sat orElim_discharge_sound
        existsElim_discharge_sound)
  apply (metis orElim_discharge_sound)
  apply (metis existsElim_discharge_sound)
  done

section \<open>Soundness of the Lemmon system\<close>

lemma fmAt_witness_sem:
  assumes "fmAt P n = Some f"
  shows "\<exists>l \<in> set P. lineNumber l = n \<and> formula l = f"
  using assms by (auto simp: fmAt_def dest: lookupLine_Some split: option.splits)

lemma openFms_openPremises_sem:
  assumes P: "lemmonCorrect P" and ne: "P \<noteq> []"
      and refs: "fst ` set (openAsms d) = references (last P)"
      and fms: "\<forall>nf \<in> set (openAsms d). fmAt P (fst nf) = Some (snd nf)"
  shows "set (openFms d) = set (openPremises P)"
proof -
  from P have dist: "distinct (map lineNumber P)"
    by (simp add: lemmonCorrect_def sorted_wrt_less_distinct)
  have prem: "set (openPremises P)
                = {formula l | l. l \<in> set P \<and> lineNumber l \<in> references (last P)}"
    using ne by (auto simp: openPremises_def depFms_def)
  show ?thesis
  proof (rule set_eqI, rule iffI)
    fix f assume "f \<in> set (openFms d)"
    then obtain n where nf: "(n, f) \<in> set (openAsms d)" by auto
    from fms nf have "fmAt P n = Some f" by fastforce
    then obtain l where l: "l \<in> set P" and ln: "lineNumber l = n"
      and lf: "formula l = f" using fmAt_witness_sem by blast
    from nf refs have "n \<in> references (last P)" by force
    with l ln lf prem show "f \<in> set (openPremises P)" by auto
  next
    fix f assume "f \<in> set (openPremises P)"
    with prem obtain l where l: "l \<in> set P"
      and ln: "lineNumber l \<in> references (last P)" and lf: "formula l = f" by auto
    from ln refs obtain g where g: "(lineNumber l, g) \<in> set (openAsms d)" by force
    from fms g have "fmAt P (lineNumber l) = Some g" by fastforce
    moreover from lookupLine_mem [OF dist l]
    have "fmAt P (lineNumber l) = Some (formula l)" by (simp add: fmAt_def)
    ultimately have "g = f" using lf by simp
    with g show "f \<in> set (openFms d)" by force
  qed
qed

theorem lemmon_semantic_soundness:
  fixes I :: "'a interp"
  assumes seq: "\<Gamma> \<turnstile>\<^sub>L \<phi>"
  shows "modelEntails I \<Gamma> \<phi>"
proof -
  from seq obtain P where P: "lemmonCorrect P" and ne: "P \<noteq> []"
      and pre: "set (openPremises P) = set \<Gamma>"
      and concl: "conclusion P = Some \<phi>"
    by (rule LseqE)
  from unfolding_terminates [OF P ne]
  obtain d where d: "toDerivation P = Inr d" by blast
  note S = toDerivation_sound [OF P ne d]
  from S(2) concl have root: "dForm d = \<phi>" by simp
  from openFms_openPremises_sem [OF P ne S(3) S(4)]
  have opens: "set (openFms d) = set (openPremises P)" .
  show ?thesis
    unfolding modelEntails_def
  proof (intro allI impI)
    fix \<rho>
    assume hs: "\<forall>\<psi>\<in>set \<Gamma>. sat I \<rho> \<psi>"
    have "holds I \<rho> (openFms d)"
      using hs opens pre unfolding holds_def by auto
    from derivOK_sound [OF S(1) this] root
    show "sat I \<rho> \<phi>" by simp
  qed
qed

section \<open>A root-scope counterexample\<close>

text \<open>The subproof assumption is not a premise, yet @{const fitchConclusion}
  reads its line as the conclusion of the whole proof.  All current
  well-formedness and rule checks accept it.\<close>

definition openAssumptionFitch :: fitch_proof where
  "openAssumptionFitch = [FSub (Subproof 1 Pf [])]"

lemma openAssumptionFitch_correct: "fitchCorrect openAssumptionFitch"
  by eval

lemma openAssumptionFitch_proves: "[] \<turnstile>\<^sub>F Pf"
proof (rule FseqI [OF openAssumptionFitch_correct])
  show "set (fitchPremises openAssumptionFitch) = set []" by eval
  show "fitchConclusion openAssumptionFitch = Some Pf" by eval
qed

definition falseInterp :: "unit interp" where
  "falseInterp = \<lparr>iNm = (\<lambda>_. ()), iPr = (\<lambda>_ _. False)\<rparr>"

lemma falseInterp_not_entails: "\<not> modelEntails falseInterp [] Pf"
  by (simp add: modelEntails_def falseInterp_def Pf_def)

theorem fitch_semantic_soundness_fails:
  "\<exists>(I :: unit interp) \<Gamma> \<phi>. \<Gamma> \<turnstile>\<^sub>F \<phi> \<and> \<not> modelEntails I \<Gamma> \<phi>"
  using openAssumptionFitch_proves falseInterp_not_entails by blast

end
