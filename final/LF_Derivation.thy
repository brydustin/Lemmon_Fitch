(*  Title:      LF_Derivation.thy

    Section 5 of the paper.  The object both notations record is a derivation:
    a tree whose root is the conclusion, whose internal nodes are applications
    of rules, and whose children are the premises those rules require.  Where a
    Lemmon justification names line numbers, the derivation names
    subderivations, and a line cited twice becomes two subtrees.

    This theory fixes the tree form of the twenty-one rules, its correctness
    predicate, and Lemma 23 (Renaming) with Corollary 24.
*)

theory LF_Derivation
  imports LF_Direct
begin

section \<open>Derivations\<close>

datatype deriv = Deriv (dForm: fm) (dRule: drule)
and drule =
    DAssume nat                               \<comment> \<open>discharged by an ancestor\<close>
  | DPremise nat                              \<comment> \<open>never discharged\<close>
  | DMP deriv deriv
  | DCP nat fm deriv                          \<comment> \<open>discharges the named assumption\<close>
  | DRAA nat fm deriv
  | DDN deriv
  | DBotI deriv deriv
  | DAndIntro deriv deriv
  | DAndElimL deriv
  | DAndElimR deriv
  | DOrIntroL deriv
  | DOrIntroR deriv
  | DOrElim deriv nat fm deriv nat fm deriv   \<comment> \<open>the disjunction, then two labelled subderivations\<close>
  | DIffIntro deriv deriv
  | DIffElimL deriv
  | DIffElimR deriv
  | DForallElim deriv
  | DForallIntro deriv
  | DExistsIntro deriv
  | DExistsElim deriv nat fm deriv
  | DEqIntro
  | DEqElim deriv deriv
  | DReit deriv                               \<comment> \<open>not one of the twenty-one; see LF_Lemmon\<close>

subsection \<open>Taking a derivation apart\<close>

fun subDerivs :: "drule \<Rightarrow> deriv list" where
  "subDerivs (DAssume k1) = []"
| "subDerivs (DPremise k1) = []"
| "subDerivs (DMP d1 d2) = [d1, d2]"
| "subDerivs (DCP k1 g1 d1) = [d1]"
| "subDerivs (DRAA k1 g1 d1) = [d1]"
| "subDerivs (DDN d1) = [d1]"
| "subDerivs (DBotI d1 d2) = [d1, d2]"
| "subDerivs (DAndIntro d1 d2) = [d1, d2]"
| "subDerivs (DAndElimL d1) = [d1]"
| "subDerivs (DAndElimR d1) = [d1]"
| "subDerivs (DOrIntroL d1) = [d1]"
| "subDerivs (DOrIntroR d1) = [d1]"
| "subDerivs (DOrElim d1 k1 g1 d2 k2 g2 d3) = [d1, d2, d3]"
| "subDerivs (DIffIntro d1 d2) = [d1, d2]"
| "subDerivs (DIffElimL d1) = [d1]"
| "subDerivs (DIffElimR d1) = [d1]"
| "subDerivs (DForallElim d1) = [d1]"
| "subDerivs (DForallIntro d1) = [d1]"
| "subDerivs (DExistsIntro d1) = [d1]"
| "subDerivs (DExistsElim d1 k1 g1 d2) = [d1, d2]"
| "subDerivs DEqIntro = []"
| "subDerivs (DEqElim d1 d2) = [d1, d2]"
| "subDerivs (DReit d1) = [d1]"

text \<open>The formulas a rule records in its own right: the assumption a discharging
  rule names.\<close>

fun ruleFms :: "drule \<Rightarrow> fm list" where
  "ruleFms (DAssume k1) = []"
| "ruleFms (DPremise k1) = []"
| "ruleFms (DMP d1 d2) = []"
| "ruleFms (DCP k1 g1 d1) = [g1]"
| "ruleFms (DRAA k1 g1 d1) = [g1]"
| "ruleFms (DDN d1) = []"
| "ruleFms (DBotI d1 d2) = []"
| "ruleFms (DAndIntro d1 d2) = []"
| "ruleFms (DAndElimL d1) = []"
| "ruleFms (DAndElimR d1) = []"
| "ruleFms (DOrIntroL d1) = []"
| "ruleFms (DOrIntroR d1) = []"
| "ruleFms (DOrElim d1 k1 g1 d2 k2 g2 d3) = [g1, g2]"
| "ruleFms (DIffIntro d1 d2) = []"
| "ruleFms (DIffElimL d1) = []"
| "ruleFms (DIffElimR d1) = []"
| "ruleFms (DForallElim d1) = []"
| "ruleFms (DForallIntro d1) = []"
| "ruleFms (DExistsIntro d1) = []"
| "ruleFms (DExistsElim d1 k1 g1 d2) = [g1]"
| "ruleFms DEqIntro = []"
| "ruleFms (DEqElim d1 d2) = []"
| "ruleFms (DReit d1) = []"

lemma subDerivs_size [termination_simp]: "d \<in> set (subDerivs r) \<Longrightarrow> size d < size r"
  by (cases r, auto)

fun namesD :: "deriv \<Rightarrow> nm list" where
  "namesD (Deriv \<phi> r) =
     names \<phi> @ concat (map names (ruleFms r)) @ concat (map namesD (subDerivs r))"

lemma namesD_sub:
  "d \<in> set (subDerivs r) \<Longrightarrow> set (namesD d) \<subseteq> set (namesD (Deriv \<phi> r))"
  by auto

subsection \<open>The assumptions a derivation still rests on\<close>

text \<open>Assumptions are labelled, a label being the number of the Lemmon line the
  assumption came from.  A discharging rule removes every leaf carrying the
  label it names --- a line cited twice has become two leaves, and both go.\<close>

abbreviation drop_label :: "nat \<Rightarrow> (nat \<times> fm) list \<Rightarrow> (nat \<times> fm) list" where
  "drop_label a \<Gamma> \<equiv> filter (\<lambda>nf. fst nf \<noteq> a) \<Gamma>"

fun openAsms :: "deriv \<Rightarrow> (nat \<times> fm) list" where
  "openAsms (Deriv \<phi> (DAssume n)) = [(n, \<phi>)]"
| "openAsms (Deriv \<phi> (DPremise n)) = [(n, \<phi>)]"
| "openAsms (Deriv \<phi> (DCP a fa d)) = drop_label a (openAsms d)"
| "openAsms (Deriv \<phi> (DRAA a fa d)) = drop_label a (openAsms d)"
| "openAsms (Deriv \<phi> (DOrElim d0 a1 f1 d1 a2 f2 d2)) =
     openAsms d0 @ drop_label a1 (openAsms d1) @ drop_label a2 (openAsms d2)"
| "openAsms (Deriv \<phi> (DExistsElim d0 a f d1)) =
     openAsms d0 @ drop_label a (openAsms d1)"
| "openAsms (Deriv \<phi> r) = concat (map openAsms (subDerivs r))"

abbreviation openFms :: "deriv \<Rightarrow> fm list" where
  "openFms d \<equiv> map snd (openAsms d)"

lemma openAsms_names:
  "(n, f) \<in> set (openAsms d) \<Longrightarrow> set (names f) \<subseteq> set (namesD d)"
  by (induction d rule: openAsms.induct, fastforce+) 

subsection \<open>Correctness of a derivation\<close>

definition dischargeOK :: "nat \<Rightarrow> fm \<Rightarrow> deriv \<Rightarrow> bool" where
  "dischargeOK a fa d \<longleftrightarrow> (\<forall>nf \<in> set (openAsms d). fst nf = a \<longrightarrow> snd nf = fa)"

fun derivOK :: "deriv \<Rightarrow> bool" where
  "derivOK (Deriv \<phi> (DAssume n)) \<longleftrightarrow> True"
| "derivOK (Deriv \<phi> (DPremise n)) \<longleftrightarrow> True"
| "derivOK (Deriv \<phi> (DMP d1 d2)) \<longleftrightarrow>
     derivOK d1 \<and> derivOK d2 \<and> dForm d1 = Impl (dForm d2) \<phi>"
| "derivOK (Deriv \<phi> (DCP a fa d)) \<longleftrightarrow>
     derivOK d \<and> \<phi> = Impl fa (dForm d) \<and> dischargeOK a fa d"
| "derivOK (Deriv \<phi> (DRAA a fa d)) \<longleftrightarrow>
     derivOK d \<and> \<phi> = Neg fa \<and> dForm d = Bot \<and> dischargeOK a fa d"
| "derivOK (Deriv \<phi> (DDN d)) \<longleftrightarrow> derivOK d \<and> dForm d = Neg (Neg \<phi>)"
| "derivOK (Deriv \<phi> (DBotI d1 d2)) \<longleftrightarrow>
     derivOK d1 \<and> derivOK d2 \<and> \<phi> = Bot \<and> dForm d2 = Neg (dForm d1)"
| "derivOK (Deriv \<phi> (DAndIntro d1 d2)) \<longleftrightarrow>
     derivOK d1 \<and> derivOK d2 \<and> \<phi> = Conj (dForm d1) (dForm d2)"
| "derivOK (Deriv \<phi> (DAndElimL d)) \<longleftrightarrow>
     derivOK d \<and> (case dForm d of Conj p q \<Rightarrow> \<phi> = p | _ \<Rightarrow> False)"
| "derivOK (Deriv \<phi> (DAndElimR d)) \<longleftrightarrow>
     derivOK d \<and> (case dForm d of Conj p q \<Rightarrow> \<phi> = q | _ \<Rightarrow> False)"
| "derivOK (Deriv \<phi> (DOrIntroL d)) \<longleftrightarrow>
     derivOK d \<and> (case \<phi> of Disj p q \<Rightarrow> dForm d = p | _ \<Rightarrow> False)"
| "derivOK (Deriv \<phi> (DOrIntroR d)) \<longleftrightarrow>
     derivOK d \<and> (case \<phi> of Disj p q \<Rightarrow> dForm d = q | _ \<Rightarrow> False)"
| "derivOK (Deriv \<phi> (DOrElim d0 a1 f1 d1 a2 f2 d2)) \<longleftrightarrow>
     derivOK d0 \<and> derivOK d1 \<and> derivOK d2 \<and>
     dForm d0 = Disj f1 f2 \<and> dForm d1 = \<phi> \<and> dForm d2 = \<phi> \<and>
     dischargeOK a1 f1 d1 \<and> dischargeOK a2 f2 d2"
| "derivOK (Deriv \<phi> (DIffIntro d1 d2)) \<longleftrightarrow>
     derivOK d1 \<and> derivOK d2 \<and>
     (case \<phi> of Iff p q \<Rightarrow> dForm d1 = Impl p q \<and> dForm d2 = Impl q p | _ \<Rightarrow> False)"
| "derivOK (Deriv \<phi> (DIffElimL d)) \<longleftrightarrow>
     derivOK d \<and> (case \<phi> of Impl p q \<Rightarrow> dForm d = Iff p q | _ \<Rightarrow> False)"
| "derivOK (Deriv \<phi> (DIffElimR d)) \<longleftrightarrow>
     derivOK d \<and> (case \<phi> of Impl q p \<Rightarrow> dForm d = Iff p q | _ \<Rightarrow> False)"
| "derivOK (Deriv \<phi> (DForallElim d)) \<longleftrightarrow>
     derivOK d \<and> (case dForm d of Uni x p \<Rightarrow> instOK x p \<phi> | _ \<Rightarrow> False)"
| "derivOK (Deriv \<phi> (DForallIntro d)) \<longleftrightarrow>
     derivOK d \<and> (case \<phi> of Uni x p \<Rightarrow> genOK x p (dForm d) (openFms d) | _ \<Rightarrow> False)"
| "derivOK (Deriv \<phi> (DExistsIntro d)) \<longleftrightarrow>
     derivOK d \<and> (case \<phi> of Exi x p \<Rightarrow> instOK x p (dForm d) | _ \<Rightarrow> False)"
| "derivOK (Deriv \<phi> (DExistsElim d0 a f d1)) \<longleftrightarrow>
     derivOK d0 \<and> derivOK d1 \<and> dForm d1 = \<phi> \<and> dischargeOK a f d1 \<and>
     (case dForm d0 of
        Exi x p \<Rightarrow> witOK x p f \<phi> (openFms d0 @ map snd (drop_label a (openAsms d1)))
      | _ \<Rightarrow> False)"
| "derivOK (Deriv \<phi> DEqIntro) \<longleftrightarrow>
     (case \<phi> of Eqf (Nm a) (Nm b) \<Rightarrow> a = b | _ \<Rightarrow> False)"
| "derivOK (Deriv \<phi> (DEqElim d1 d2)) \<longleftrightarrow>
     derivOK d1 \<and> derivOK d2 \<and>
     (case dForm d1 of Eqf (Nm a) (Nm b) \<Rightarrow> eqsub a b (dForm d2) \<phi> | _ \<Rightarrow> False)"
| "derivOK (Deriv \<phi> (DReit d)) \<longleftrightarrow> derivOK d \<and> \<phi> = dForm d"

subsection \<open>The derivation turnstile\<close>

text \<open>A derivation carries its own sequent: the formulas of its undischarged
  leaves on the left, its root formula on the right.  We write \<open>d \<tturnstile> s\<close> for
  ``@{term d} is a derivation of the sequent @{term s}'', so that with the
  turnstiles of \<open>LF_Delta\<close> the statements below read \<open>d \<tturnstile> \<Gamma> \<turnstile>\<^sub>L \<psi>\<close>, as the paper
  writes them --- \<open>\<tturnstile>\<close> is an ordinary infix, and what it applies to on the right
  is the sequent itself.  Only a Lemmon sequent can be derived this way: a
  derivation is a tree of the Lemmon rules, and Definition 21 unfolds a Lemmon
  proof into one.  As there, \<open>\<Gamma>\<close> is compared as a set --- an assumption may be
  used at several leaves.\<close>

definition derivOf :: "deriv \<Rightarrow> fm list \<Rightarrow> fm \<Rightarrow> bool" where
  "derivOf d \<Gamma> \<psi> \<longleftrightarrow> derivOK d \<and> set (openFms d) = set \<Gamma> \<and> dForm d = \<psi>"

text \<open>\<open>\<tturnstile>\<close> is not a three-place template that re-declares \<open>\<turnstile>\<^sub>L\<close>.  It is a binary
  operator whose right-hand argument is a \<open>\<turnstile>\<^sub>L\<close> statement, bound looser than it
  (45 against 50) so that \<open>d \<tturnstile> \<Gamma> \<turnstile>\<^sub>L \<psi>\<close> needs no parentheses, and translated away
  to @{const derivOf}.  Nothing else can stand to the right of \<open>\<tturnstile>\<close>, which is as
  it should be: only a Lemmon sequent is derived by a derivation.\<close>

syntax "_derivOf" :: "deriv \<Rightarrow> bool \<Rightarrow> bool"  (\<open>_ \<tturnstile> _\<close> [51, 50] 45)
translations "d \<tturnstile> \<Gamma> \<turnstile>\<^sub>L \<psi>" \<rightleftharpoons> "CONST derivOf d \<Gamma> \<psi>"

lemma derivOf_iff [simp]:
  "d \<tturnstile> \<Gamma> \<turnstile>\<^sub>L \<psi> \<longleftrightarrow> derivOK d \<and> set (openFms d) = set \<Gamma> \<and> dForm d = \<psi>"
  by (simp add: derivOf_def)

lemma derivOf_self: "derivOK d \<Longrightarrow> d \<tturnstile> openFms d \<turnstile>\<^sub>L dForm d"
  by simp

lemma derivOf_derivOK: "d \<tturnstile> \<Gamma> \<turnstile>\<^sub>L \<psi> \<Longrightarrow> derivOK d"
  by simp

text \<open>Guard: \<open>\<tturnstile>\<close> really is applied to the \<open>\<turnstile>\<^sub>L\<close> statement, with no parentheses
  around either.  This fails to parse if the priorities are ever disturbed.\<close>

lemma turnstile_composes: "d \<tturnstile> \<Gamma> \<turnstile>\<^sub>L \<psi> \<longleftrightarrow> derivOf d \<Gamma> \<psi>" by (rule refl)

subsection \<open>Renaming\<close>

fun rnD :: "nm \<Rightarrow> nm \<Rightarrow> deriv \<Rightarrow> deriv" where
"rnD a b (Deriv \<phi> (DAssume k1)) = Deriv (rn a b \<phi>) (DAssume k1)"
| "rnD a b (Deriv \<phi> (DPremise k1)) = Deriv (rn a b \<phi>) (DPremise k1)"
| "rnD a b (Deriv \<phi> (DMP d1 d2)) = Deriv (rn a b \<phi>) (DMP (rnD a b d1) (rnD a b d2))"
| "rnD a b (Deriv \<phi> (DCP k1 g1 d1)) = Deriv (rn a b \<phi>) (DCP k1 (rn a b g1) (rnD a b d1))"
| "rnD a b (Deriv \<phi> (DRAA k1 g1 d1)) = Deriv (rn a b \<phi>) (DRAA k1 (rn a b g1) (rnD a b d1))"
| "rnD a b (Deriv \<phi> (DDN d1)) = Deriv (rn a b \<phi>) (DDN (rnD a b d1))"
| "rnD a b (Deriv \<phi> (DBotI d1 d2)) = Deriv (rn a b \<phi>) (DBotI (rnD a b d1) (rnD a b d2))"
| "rnD a b (Deriv \<phi> (DAndIntro d1 d2)) = Deriv (rn a b \<phi>) (DAndIntro (rnD a b d1) (rnD a b d2))"
| "rnD a b (Deriv \<phi> (DAndElimL d1)) = Deriv (rn a b \<phi>) (DAndElimL (rnD a b d1))"
| "rnD a b (Deriv \<phi> (DAndElimR d1)) = Deriv (rn a b \<phi>) (DAndElimR (rnD a b d1))"
| "rnD a b (Deriv \<phi> (DOrIntroL d1)) = Deriv (rn a b \<phi>) (DOrIntroL (rnD a b d1))"
| "rnD a b (Deriv \<phi> (DOrIntroR d1)) = Deriv (rn a b \<phi>) (DOrIntroR (rnD a b d1))"
| "rnD a b (Deriv \<phi> (DOrElim d1 k1 g1 d2 k2 g2 d3)) = Deriv (rn a b \<phi>) (DOrElim (rnD a b d1) k1 (rn a b g1) (rnD a b d2) k2 (rn a b g2) (rnD a b d3))"
| "rnD a b (Deriv \<phi> (DIffIntro d1 d2)) = Deriv (rn a b \<phi>) (DIffIntro (rnD a b d1) (rnD a b d2))"
| "rnD a b (Deriv \<phi> (DIffElimL d1)) = Deriv (rn a b \<phi>) (DIffElimL (rnD a b d1))"
| "rnD a b (Deriv \<phi> (DIffElimR d1)) = Deriv (rn a b \<phi>) (DIffElimR (rnD a b d1))"
| "rnD a b (Deriv \<phi> (DForallElim d1)) = Deriv (rn a b \<phi>) (DForallElim (rnD a b d1))"
| "rnD a b (Deriv \<phi> (DForallIntro d1)) = Deriv (rn a b \<phi>) (DForallIntro (rnD a b d1))"
| "rnD a b (Deriv \<phi> (DExistsIntro d1)) = Deriv (rn a b \<phi>) (DExistsIntro (rnD a b d1))"
| "rnD a b (Deriv \<phi> (DExistsElim d1 k1 g1 d2)) = Deriv (rn a b \<phi>) (DExistsElim (rnD a b d1) k1 (rn a b g1) (rnD a b d2))"
| "rnD a b (Deriv \<phi> DEqIntro) = Deriv (rn a b \<phi>) (DEqIntro)"
| "rnD a b (Deriv \<phi> (DEqElim d1 d2)) = Deriv (rn a b \<phi>) (DEqElim (rnD a b d1) (rnD a b d2))"
| "rnD a b (Deriv \<phi> (DReit d1)) = Deriv (rn a b \<phi>) (DReit (rnD a b d1))"

abbreviation rnn :: "nm \<Rightarrow> nm \<Rightarrow> nm \<Rightarrow> nm" where
  "rnn a b c \<equiv> (if c = a then b else c)"

lemma dForm_rnD [simp]: "dForm (rnD a b d) = rn a b (dForm d)"
  by (cases d; cases "dRule d", auto) 

lemma derivOK_rnD_sub: "d \<in> set (subDerivs r) \<Longrightarrow> size d < size r"
  by (rule subDerivs_size)

text \<open>And the paper's bracket, for a derivation.\<close>

abbreviation rnD_syn :: "deriv \<Rightarrow> nm \<Rightarrow> nm \<Rightarrow> deriv"  (\<open>_[_'/_]\<close> [1000, 0, 0] 1000)
  where "d[b/a] \<equiv> rnD a b d"

lemma bracket_deriv: "(d :: deriv)[b/a] = rnD a b d" by (rule refl)

lemma openAsms_rnD: "openAsms (rnD a b d) = map (\<lambda>nf. (fst nf, rn a b (snd nf))) (openAsms d)"
  by (induction d rule: openAsms.induct, auto simp: filter_map o_def)

lemma openFms_rnD: "openFms (rnD a b d) = map (rn a b) (openFms d)"
  by (simp add: openAsms_rnD o_def)

text \<open>The next three lemmas are what keeps @{text namesD_rnD} from being a
  twenty-three-way case analysis with set reasoning inside every branch.  They
  separate the two concerns: @{text namesD_unfold} and the two renaming
  equations say what the constructors do, each branch being a single equation
  between constructor applications; the proof proper then rewrites once, with no
  case analysis at all.\<close>

lemma namesD_unfold:
  "namesD d = names (dForm d) @ concat (map names (ruleFms (dRule d)))
                @ concat (map namesD (subDerivs (dRule d)))"
  by (cases d, simp)

lemma ruleFms_rnD:
  "ruleFms (dRule (rnD a b (Deriv \<phi> r))) = map (rn a b) (ruleFms r)"
  by (cases r, simp_all)

lemma subDerivs_rnD:
  "subDerivs (dRule (rnD a b (Deriv \<phi> r))) = map (rnD a b) (subDerivs r)"
  by (cases r, simp_all)

text \<open>Renaming commutes with taking the names of a list of formulas, and --- given
  the induction hypothesis --- of a list of subderivations.\<close>

lemma set_concat_names_rn:
  "set (concat (map names (map (rn a b) gs))) = rnn a b ` set (concat (map names gs))"
  by (induction gs, auto simp: names_rn image_Un)

lemma set_concat_namesD_rnD:
  assumes "\<forall>e \<in> set ds. set (namesD (rnD a b e)) = rnn a b ` set (namesD e)"
  shows "set (concat (map namesD (map (rnD a b) ds)))
           = rnn a b ` set (concat (map namesD ds))"
  using assms by (induction ds, auto simp: image_Un)

lemma namesD_rnD: "set (namesD (rnD a b d)) = rnn a b ` set (namesD d)"
proof (induction d rule: namesD.induct)
  case (1 \<phi> r)
  have sub: "\<forall>e \<in> set (subDerivs r).
                set (namesD (rnD a b e)) = rnn a b ` set (namesD e)"
    using 1 by blast
  have "set (namesD (rnD a b (Deriv \<phi> r)))
          = set (names (rn a b \<phi>))
            \<union> set (concat (map names (map (rn a b) (ruleFms r))))
            \<union> set (concat (map namesD (map (rnD a b) (subDerivs r))))"
    by (subst namesD_unfold) (simp add: ruleFms_rnD subDerivs_rnD Un_assoc)
  also have "\<dots> = rnn a b ` set (names \<phi>)
                  \<union> rnn a b ` set (concat (map names (ruleFms r)))
                  \<union> rnn a b ` set (concat (map namesD (subDerivs r)))"
    using names_rn set_concat_namesD_rnD set_concat_names_rn sub by presburger
  also have "\<dots> = rnn a b ` set (namesD (Deriv \<phi> r))"
    by (metis append_assoc image_Un namesD.simps set_append)
  finally show ?case .
qed

lemma namesD_dForm: "set (names (dForm d)) \<subseteq> set (namesD d)"
  by (cases d, auto)

lemma dischargeOK_rnD:
  "dischargeOK n fa d \<Longrightarrow> dischargeOK n (rn a b fa) (rnD a b d)"
  by (auto simp: dischargeOK_def openAsms_rnD)

subsection \<open>Renaming preserves the side conditions\<close>

text \<open>Substituting one name for another can introduce into the assumptions the
  very name a universal introduction is required to avoid.  That @{term b} be
  fresh is what closes the gap, and it is needed at exactly the three places
  below --- everywhere else renaming commutes with the rule.\<close>

lemma rn_image_notin:
  assumes "c \<notin> S" "b \<notin> S" "c \<noteq> b"
  shows "rnn a b c \<notin> rnn a b ` S"
  using assms by auto

lemma occurs_rn_notin:
  assumes "\<not> occurs c q" and "b \<notin> set (names q)" and "c \<noteq> b"
  shows "\<not> occurs (rnn a b c) (rn a b q)"
  using rn_image_notin [OF assms(1) assms(2) assms(3)] by (simp add: names_rn)

text \<open>A non-abbreviation for the renaming map, so that the simplifier does not
  split it apart before the rules below can be applied.\<close>

definition rnm :: "nm \<Rightarrow> nm \<Rightarrow> nm \<Rightarrow> nm" where
  "rnm a b c = (if c = a then b else c)"

lemma eqsub_t_rnm:
  "eqsub_t c e t u \<Longrightarrow> eqsub_t (rnm a b c) (rnm a b e) (rn_t a b t) (rn_t a b u)"
  by (cases t; cases u, auto simp: rnm_def)

lemma list_all2_eqsub_t_rnm:
  "list_all2 (eqsub_t c e) ts us \<Longrightarrow>
     list_all2 (\<lambda>t u. eqsub_t (rnm a b c) (rnm a b e) (rn_t a b t) (rn_t a b u)) ts us"
  by (induction ts us rule: list_all2_induct, auto intro: eqsub_t_rnm)

lemma eqsub_rnm:
  "eqsub c e p q \<Longrightarrow> eqsub (rnm a b c) (rnm a b e) (rn a b p) (rn a b q)"
proof (induction c e p q rule: eqsub.induct)
  case (1 c e P ts Q us)
  then show ?case by (simp add: list.rel_map list_all2_eqsub_t_rnm)
qed (auto intro: eqsub_t_rnm)

lemma eqsub_rn:
  "eqsub c e p q \<Longrightarrow> eqsub (rnn a b c) (rnn a b e) (rn a b p) (rn a b q)"
  using eqsub_rnm [of c e p q a b] by (simp only: rnm_def)

text \<open>The four instances the simplifier leaves after it has split the renaming
  map apart.\<close>

lemma eqsub_rn_cases:
  "eqsub a a p q \<Longrightarrow> eqsub b b (rn a b p) (rn a b q)"
  "eqsub a e p q \<Longrightarrow> e \<noteq> a \<Longrightarrow> eqsub b e (rn a b p) (rn a b q)"
  "eqsub c a p q \<Longrightarrow> c \<noteq> a \<Longrightarrow> eqsub c b (rn a b p) (rn a b q)"
  "eqsub c e p q \<Longrightarrow> c \<noteq> a \<Longrightarrow> e \<noteq> a \<Longrightarrow> eqsub c e (rn a b p) (rn a b q)"
  using eqsub_rnm [of a a p q a b] eqsub_rnm [of a e p q a b]
        eqsub_rnm [of c a p q a b] eqsub_rnm [of c e p q a b]
  by (simp_all add: rnm_def)

lemma instOK_rn:
  assumes "instOK x p q"
  shows "instOK x (rn a b p) (rn a b q)"
proof (cases "x \<in> set (fvs p)")
  case True
  with assms have "instWitnesses x p q \<noteq> []" by (simp add: instOK_def)
  then obtain c where c: "c \<in> set (instWitnesses x p q)"
    by (cases "instWitnesses x p q", auto)
  then have "inst x c p = q" by (rule instWitnesses_sound)
  then have "inst x (rnn a b c) (rn a b p) = rn a b q" by (metis rn_inst)
  moreover from True have "x \<in> set (fvs (rn a b p))" by simp
  ultimately have "rnn a b c \<in> set (instWitnesses x (rn a b p) (rn a b q))"
    by (rule_tac instWitnesses_complete, auto)
  with True show ?thesis by (auto simp: instOK_def)
qed (use assms in \<open>auto simp: instOK_def\<close>)

lemma genOK_rn:
  assumes ok: "genOK x p \<psi> As"
      and b: "b \<notin> set (names p) \<union> set (names \<psi>) \<union> (\<Union>f \<in> set As. set (names f))"
  shows "genOK x (rn a b p) (rn a b \<psi>) (map (rn a b) As)"
proof (cases "x \<in> set (fvs p)")
  case True
  with ok obtain c where c: "c \<in> set (instWitnesses x p \<psi>)"
                     and cp: "\<not> occurs c p" and cA: "arbitrary_in c As"
    by (auto simp: genOK_def)
  from c True have cq: "c \<in> set (names \<psi>)" by (auto simp: instWitnesses_def)
  with b have cb: "c \<noteq> b" by blast
  from c have "inst x c p = \<psi>" by (rule instWitnesses_sound)
  then have "inst x (rnn a b c) (rn a b p) = rn a b \<psi>" by (metis rn_inst)
  moreover from True have "x \<in> set (fvs (rn a b p))" by simp
  ultimately have w: "rnn a b c \<in> set (instWitnesses x (rn a b p) (rn a b \<psi>))"
    by (rule_tac instWitnesses_complete, auto)
  have "\<not> occurs (rnn a b c) (rn a b p)"
    using cp cb b by (intro occurs_rn_notin, auto)
  moreover have "arbitrary_in (rnn a b c) (map (rn a b) As)"
  proof (unfold arbitrary_in_def, intro ballI)
    fix g assume "g \<in> set (map (rn a b) As)"
    then obtain f where f: "f \<in> set As" "g = rn a b f" by auto
    with cA have "\<not> occurs c f" by (auto simp: arbitrary_in_def)
    moreover from f b have "b \<notin> set (names f)" by blast
    ultimately show "\<not> occurs (rnn a b c) g"
      using cb f by (simp only:, intro occurs_rn_notin, blast+)
  qed
  ultimately show ?thesis using w True by (auto simp: genOK_def)
qed (use ok in \<open>auto simp: genOK_def\<close>)

lemma witOK_rn:
  assumes ok: "witOK x p \<psi> \<phi> As"
      and b: "b \<notin> set (names p) \<union> set (names \<psi>) \<union> set (names \<phi>)
                    \<union> (\<Union>f \<in> set As. set (names f))"
  shows "witOK x (rn a b p) (rn a b \<psi>) (rn a b \<phi>) (map (rn a b) As)"
proof (cases "x \<in> set (fvs p)")
  case True
  with ok obtain c where c: "c \<in> set (instWitnesses x p \<psi>)"
                     and cp: "\<not> occurs c p" and c\<phi>: "\<not> occurs c \<phi>"
                     and cA: "arbitrary_in c As"
    by (auto simp: witOK_def)
  from c True have cq: "c \<in> set (names \<psi>)" by (auto simp: instWitnesses_def)
  with b have cb: "c \<noteq> b" by blast
  from c have "inst x c p = \<psi>" by (rule instWitnesses_sound)
  then have "inst x (rnn a b c) (rn a b p) = rn a b \<psi>" by (metis rn_inst)
  moreover from True have "x \<in> set (fvs (rn a b p))" by simp
  ultimately have w: "rnn a b c \<in> set (instWitnesses x (rn a b p) (rn a b \<psi>))"
    by (rule_tac instWitnesses_complete, auto)
  have "\<not> occurs (rnn a b c) (rn a b p)"
    using cp cb b by (intro occurs_rn_notin, blast+)
  moreover have "\<not> occurs (rnn a b c) (rn a b \<phi>)"
    using c\<phi> cb b by (intro occurs_rn_notin, blast+)
  moreover have "arbitrary_in (rnn a b c) (map (rn a b) As)"
  proof (unfold arbitrary_in_def, intro ballI)
    fix g assume "g \<in> set (map (rn a b) As)"
    then obtain f where f: "f \<in> set As" "g = rn a b f" by auto
    with cA have "\<not> occurs c f" by (auto simp: arbitrary_in_def)
    moreover from f b have "b \<notin> set (names f)" by blast
    ultimately show "\<not> occurs (rnn a b c) g"
      using cb f by (simp only:) (intro occurs_rn_notin, blast+)
  qed
  ultimately show ?thesis using w True by (auto simp: witOK_def)
qed (use ok in \<open>auto simp: witOK_def\<close>)

subsection \<open>Lemma 23: the Renaming Lemma\<close>

lemma b_notin_openAsms:
  "b \<notin> set (namesD d) \<Longrightarrow> (n, f) \<in> set (openAsms d) \<Longrightarrow> \<not> occurs b f"
  using openAsms_names by fastforce

lemma drop_label_rnD:
  "map snd (drop_label n (openAsms (rnD a b d)))
     = map (rn a b) (map snd (drop_label n (openAsms d)))"
  by (simp add: openAsms_rnD filter_map o_def)

lemma genOK_rnD:
  assumes ok: "genOK x p (dForm d) (openFms d)"
      and bp: "b \<notin> set (names p)" and bd: "b \<notin> set (namesD d)"
  shows "genOK x (rn a b p) (rn a b (dForm d)) (map (rn a b \<circ> snd) (openAsms d))"
proof -
  have "genOK x (rn a b p) (rn a b (dForm d)) (map (rn a b) (openFms d))"
  proof (rule genOK_rn [OF ok])
    from bd namesD_dForm have "b \<notin> set (names (dForm d))" by blast
    moreover have "\<forall>f \<in> set (openFms d). b \<notin> set (names f)"
      by (auto dest: b_notin_openAsms [OF bd])
    ultimately show "b \<notin> set (names p) \<union> set (names (dForm d))
                            \<union> (\<Union>f \<in> set (openFms d). set (names f))"
      using bp by blast
  qed
  then show ?thesis by simp
qed

lemma witOK_rnD:
  assumes ok: "witOK x p f \<phi> (openFms d0 @ map snd (drop_label n (openAsms d1)))"
      and dd: "dForm d0 = Exi x p"
      and b\<phi>: "b \<notin> set (names \<phi>)" and bf: "b \<notin> set (names f)"
      and b0: "b \<notin> set (namesD d0)" and b1: "b \<notin> set (namesD d1)"
  shows "witOK x (rn a b p) (rn a b f) (rn a b \<phi>)
           (map (rn a b \<circ> snd) (openAsms d0)
              @ map (rn a b \<circ> snd) (drop_label n (openAsms d1)))"
proof -
  have "witOK x (rn a b p) (rn a b f) (rn a b \<phi>)
          (map (rn a b) (openFms d0 @ map snd (drop_label n (openAsms d1))))"
  proof (rule witOK_rn [OF ok])
    from b0 dd namesD_dForm [of d0] have "b \<notin> set (names p)" by auto
    moreover have "\<forall>g \<in> set (openFms d0). b \<notin> set (names g)"
      by (auto dest: b_notin_openAsms [OF b0])
    moreover have "\<forall>g \<in> set (map snd (drop_label n (openAsms d1))). b \<notin> set (names g)"
      by (auto dest: b_notin_openAsms [OF b1])
    ultimately show "b \<notin> set (names p) \<union> set (names f) \<union> set (names \<phi>)
                       \<union> (\<Union>g \<in> set (openFms d0 @ map snd (drop_label n (openAsms d1))).
                            set (names g))"
      using bf b\<phi> by auto
  qed
  then show ?thesis by simp
qed

text \<open>Let @{term d} be a derivation of \<open>\<Gamma> \<turnstile>\<^sub>L \<psi>\<close>, and let @{term b} be a name
  occurring nowhere in @{term d}.  Then \<open>d[b/a]\<close> is a derivation of
  \<open>\<Gamma>[b/a] \<turnstile>\<^sub>L \<psi>[b/a]\<close>.  Eighteen of the rules impose no condition on names and
  go through by the shape of the rule alone; the quantifier rules are where the
  freshness of @{term b} is doing work, for the reason given in Remark 25.

  The workhorse form is the first theorem below: renaming preserves
  @{const derivOK}.  The sequent form follows it, and is the paper's own
  statement.\<close>

theorem renaming:
  assumes "derivOK d" and "b \<notin> set (namesD d)"
  shows "derivOK (rnD a b d)"
  using assms
proof (induction d rule: derivOK.induct)
qed (auto simp: dischargeOK_rnD openFms_rnD drop_label_rnD
                instOK_rn genOK_rnD witOK_rnD
          split: fm.splits trm.splits
          intro: eqsub_rn_cases)

corollary renaming_sequent:
  assumes "d \<tturnstile> \<Gamma> \<turnstile>\<^sub>L \<psi>" and "b \<notin> set (namesD d)"
  shows "d[b/a] \<tturnstile> \<Gamma>[b/a] \<turnstile>\<^sub>L \<psi>[b/a]"
proof -
  from assms(1) have ok: "derivOK d" and G: "set (openFms d) = set \<Gamma>"
    and psi: "dForm d = \<psi>" by simp_all
  from renaming [OF ok assms(2)] have "derivOK (rnD a b d)" .
  moreover have "set (openFms (rnD a b d)) = set (map (rn a b) \<Gamma>)"
    by (metis G image_set openFms_rnD)
  moreover have "dForm (rnD a b d) = rn a b \<psi>" using psi by simp
  ultimately show ?thesis by simp
qed

text \<open>Corollary 24: if in addition @{term a} does not occur in \<open>\<Gamma>\<close>, then
  \<open>\<Gamma>[b/a] = \<Gamma>\<close>, and so the open assumptions are untouched while the conclusion
  is renamed.  This is what licenses the repair of Section 5: the Lemmon side
  condition says exactly that @{term a} does not occur in the assumptions, so
  the subderivation feeding a universal introduction may be renamed without
  disturbing anything it rests on.\<close>

corollary renaming_open:
  assumes "derivOK d" and "b \<notin> set (namesD d)"
      and "\<forall>f \<in> set (openFms d). \<not> occurs a f"
  shows "derivOK (rnD a b d)"
    and "openFms (rnD a b d) = openFms d"
    and "dForm (rnD a b d) = rn a b (dForm d)"
proof -
  show "derivOK (rnD a b d)" using renaming [OF assms(1) assms(2)] .
  show "openFms (rnD a b d) = openFms d"
    using assms(3) by (simp add: openFms_rnD map_idI)
  show "dForm (rnD a b d) = rn a b (dForm d)" by simp
qed

end
