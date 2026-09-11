(*  Title:      LF_Lemmon.thy

    Definition 1 of the paper: a Lemmon proof is a finite sequence of lines,
    a line being a quadruple <Gamma, n, phi, j>.  Here we fix the rule set,
    the dependency arithmetic that the rules determine, and the checker.
*)

theory LF_Lemmon
  imports LF_Formula
begin

section \<open>The Lemmon system\<close>

text \<open>
  The paper works with the twenty-one rules of Halvorson, \emph{How Logic
  Works}.  The book does not travel with this file, so the particular
  twenty-one below are a reconstruction; what the paper actually uses of them
  is fixed and is reproduced exactly:

    \<^item> most rules pool the dependency sets of the lines they cite;
    \<^item> four rules discharge --- @{text CP} and @{text RAA} each name an
      assumption line together with a line derived from it, @{text OrElim}
      and @{text ExistsElim} name one or two such pairs;
    \<^item> @{text ForallIntro} and @{text ExistsElim} impose eigenconstant
      conditions on assumption formulas as well as on the cited formulas.

  The downstream proofs are over this particular reconstructed datatype.
  A change of roster requires corresponding derivation, renaming and
  translation proofs; these results do not automatically transfer to the
  separate exact @{text "HL_"} datatype.

  @{text Reit} is not one of the twenty-one.  Lemmon has no reiteration rule
  and needs none (Proposition 18); it is admitted here only so that
  @{text \<delta>} is defined on Fitch proofs that use reiteration, which the
  Lemmon-to-Fitch construction must sometimes emit (Section 5.3).  The
  predicate @{text lemmon_21} says that a proof stays inside the real system.
\<close>

subsection \<open>Justifications\<close>

datatype just =
    Assumption                                \<comment> \<open>A\<close>
  | MP nat nat                                \<comment> \<open>modus ponens, two lines\<close>
  | CP nat nat                                \<comment> \<open>assumption line, conclusion line\<close>
  | RAA nat nat                               \<comment> \<open>assumption line, conclusion line\<close>
  | DN nat                                    \<comment> \<open>double negation\<close>
  | BotI nat nat                              \<comment> \<open>\<open>\<phi>, \<not>\<phi> \<turnstile>\<^sub>L \<bottom>\<close>\<close>
  | AndIntro nat nat
  | AndElimL nat
  | AndElimR nat
  | OrIntroL nat
  | OrIntroR nat
  | OrElim nat nat nat nat nat                \<comment> \<open>disjunction, then two such pairs\<close>
  | IffIntro nat nat
  | IffElimL nat
  | IffElimR nat
  | ForallElim nat
  | ForallIntro nat
  | ExistsIntro nat
  | ExistsElim nat nat nat                    \<comment> \<open>existential, assumption line, conclusion line\<close>
  | EqIntro
  | EqElim nat nat
  | Reit nat                                  \<comment> \<open>not one of the twenty-one; see above\<close>

definition is_reit :: "just \<Rightarrow> bool" where
  "is_reit j \<longleftrightarrow> (case j of Reit _ \<Rightarrow> True | _ \<Rightarrow> False)"

text \<open>The lines a justification cites.\<close>

fun citedLines :: "just \<Rightarrow> nat list" where
  "citedLines Assumption = []"
| "citedLines (MP i j) = [i, j]"
| "citedLines (CP a c) = [a, c]"
| "citedLines (RAA a c) = [a, c]"
| "citedLines (DN i) = [i]"
| "citedLines (BotI i j) = [i, j]"
| "citedLines (AndIntro i j) = [i, j]"
| "citedLines (AndElimL i) = [i]"
| "citedLines (AndElimR i) = [i]"
| "citedLines (OrIntroL i) = [i]"
| "citedLines (OrIntroR i) = [i]"
| "citedLines (OrElim d a1 c1 a2 c2) = [d, a1, c1, a2, c2]"
| "citedLines (IffIntro i j) = [i, j]"
| "citedLines (IffElimL i) = [i]"
| "citedLines (IffElimR i) = [i]"
| "citedLines (ForallElim i) = [i]"
| "citedLines (ForallIntro i) = [i]"
| "citedLines (ExistsIntro i) = [i]"
| "citedLines (ExistsElim m a c) = [m, a, c]"
| "citedLines EqIntro = []"
| "citedLines (EqElim i j) = [i, j]"
| "citedLines (Reit i) = [i]"

text \<open>The assumption/conclusion pairs a justification discharges.  These are
  exactly the pairs a Fitch proof writes as a subproof reference.\<close>

fun dischargePairs :: "just \<Rightarrow> (nat \<times> nat) list" where
  "dischargePairs (CP a c) = [(a, c)]"
| "dischargePairs (RAA a c) = [(a, c)]"
| "dischargePairs (OrElim d a1 c1 a2 c2) = [(a1, c1), (a2, c2)]"
| "dischargePairs (ExistsElim m a c) = [(a, c)]"
| "dischargePairs _ = []"

definition discharges :: "just \<Rightarrow> bool" where
  "discharges j \<longleftrightarrow> dischargePairs j \<noteq> []"

subsection \<open>Lines and proofs\<close>

datatype pline =
  ProofLine (lineNumber: nat) (formula: fm) (justification: just) (references: "nat set")

type_synonym lemmon_proof = "pline list"

definition lemmon_21 :: "lemmon_proof \<Rightarrow> bool" where
  "lemmon_21 P \<longleftrightarrow> (\<forall>l \<in> set P. \<not> is_reit (justification l))"

fun lookupLine :: "lemmon_proof \<Rightarrow> nat \<Rightarrow> pline option" where
  "lookupLine [] n = None"
| "lookupLine (l # ls) n = (if lineNumber l = n then Some l else lookupLine ls n)"

definition fmAt :: "lemmon_proof \<Rightarrow> nat \<Rightarrow> fm option" where
  "fmAt P n = map_option formula (lookupLine P n)"

definition depsAt :: "lemmon_proof \<Rightarrow> nat \<Rightarrow> nat set" where
  "depsAt P n = (case lookupLine P n of None \<Rightarrow> {} | Some l \<Rightarrow> references l)"

definition justAt :: "lemmon_proof \<Rightarrow> nat \<Rightarrow> just option" where
  "justAt P n = map_option justification (lookupLine P n)"

subsection \<open>The dependency arithmetic\<close>

text \<open>Definition 3's arithmetic, in the form the paper gives it: the
  discharging cases subtract, every other rule takes the union of what it
  cites.  @{term look} supplies the dependency sets of the earlier lines and
  @{term self} is the number of the line being computed.\<close>

definition depsOf :: "(nat \<Rightarrow> nat set) \<Rightarrow> just \<Rightarrow> nat \<Rightarrow> nat set" where
  "depsOf look j self =
     (case j of
        Assumption \<Rightarrow> {self}
      | EqIntro \<Rightarrow> {}
      | CP a c \<Rightarrow> look c - {a}
      | RAA a c \<Rightarrow> look c - {a}
      | OrElim d a1 c1 a2 c2 \<Rightarrow> look d \<union> (look c1 - {a1}) \<union> (look c2 - {a2})
      | ExistsElim m a c \<Rightarrow> look m \<union> (look c - {a})
      | _ \<Rightarrow> \<Union> (set (map look (citedLines j))))"

lemma depsOf_nondischarging:
  assumes "\<not> discharges j" "j \<noteq> Assumption" "j \<noteq> EqIntro"
  shows "depsOf look j self = \<Union> (set (map look (citedLines j)))"
  using assms by (cases j) (auto simp: depsOf_def discharges_def)

subsection \<open>Side conditions\<close>

definition arbitrary_in :: "nm \<Rightarrow> fm list \<Rightarrow> bool" where
  "arbitrary_in a ps \<longleftrightarrow> (\<forall>p \<in> set ps. \<not> occurs a p)"


text \<open>The names by which @{term q} could have been got from @{term p} by
  instantiating @{term x}.  When @{term x} is free in @{term p} the name is
  forced to occur in @{term q}, so the search is over the names of @{term q};
  when it is not, the instantiation is vacuous and no name is determined, which
  the callers below handle separately.\<close>

definition instWitnesses :: "vr \<Rightarrow> fm \<Rightarrow> fm \<Rightarrow> nm list" where
  "instWitnesses x p q =
     (if x \<in> set (fvs p) then filter (\<lambda>a. inst x a p = q) (names q) else [])"

lemma instWitnesses_sound: "a \<in> set (instWitnesses x p q) \<Longrightarrow> inst x a p = q"
  unfolding instWitnesses_def by (cases "x \<in> set (fvs p)") simp_all

lemma instWitnesses_complete:
  assumes "x \<in> set (fvs p)" and "inst x a p = q"
  shows "a \<in> set (instWitnesses x p q)"
proof -
  have "occurs a (inst x a p)" using assms(1) by (simp add: occurs_inst)
  with assms show ?thesis by (simp add: instWitnesses_def)
qed

text \<open>If @{term x} is not free in @{term p} the quantifier is vacuous: @{term
  "Uni x p"} follows from @{term p} by generalising on any name at all, and a
  name occurring nowhere is always available, so no side condition can bite.
  Otherwise the name generalised upon is determined by the two formulas, and the
  side conditions are checked against it.\<close>

definition instOK :: "vr \<Rightarrow> fm \<Rightarrow> fm \<Rightarrow> bool" where
  "instOK x p q \<longleftrightarrow>
     (if x \<in> set (fvs p) then instWitnesses x p q \<noteq> [] else q = p)"

definition genOK :: "vr \<Rightarrow> fm \<Rightarrow> fm \<Rightarrow> fm list \<Rightarrow> bool" where
  "genOK x p psi As \<longleftrightarrow>
     (if x \<in> set (fvs p)
        then (\<exists>a \<in> set (instWitnesses x p psi). \<not> occurs a p \<and> arbitrary_in a As)
        else psi = p)"

definition witOK :: "vr \<Rightarrow> fm \<Rightarrow> fm \<Rightarrow> fm \<Rightarrow> fm list \<Rightarrow> bool" where
  "witOK x p psi phi As \<longleftrightarrow>
     (if x \<in> set (fvs p)
        then (\<exists>b \<in> set (instWitnesses x p psi).
                \<not> occurs b p \<and> \<not> occurs b phi \<and> arbitrary_in b As)
        else psi = p)"

lemma genOK_antitone: "set As \<subseteq> set Bs \<Longrightarrow> genOK x p psi Bs \<Longrightarrow> genOK x p psi As"
  unfolding genOK_def by (cases "x \<in> set (fvs p)") (auto simp: arbitrary_in_def)

lemma witOK_antitone: "set As \<subseteq> set Bs \<Longrightarrow> witOK x p psi phi Bs \<Longrightarrow> witOK x p psi phi As"
  unfolding witOK_def by (cases "x \<in> set (fvs p)") (auto simp: arbitrary_in_def)

text \<open>@{term "eqsub a b p q"}: @{term q} comes from @{term p} by replacing
  some (possibly no, possibly all) occurrences of the name @{term a} by
  @{term b}.  This is the relation @{text "=E"} licenses.\<close>

fun eqsub_t :: "nm \<Rightarrow> nm \<Rightarrow> trm \<Rightarrow> trm \<Rightarrow> bool" where
  "eqsub_t a b (Nm c) (Nm d) \<longleftrightarrow> (c = d \<or> (c = a \<and> d = b))"
| "eqsub_t a b (Vr x) (Vr y) \<longleftrightarrow> x = y"
| "eqsub_t a b _ _ \<longleftrightarrow> False"

fun eqsub :: "nm \<Rightarrow> nm \<Rightarrow> fm \<Rightarrow> fm \<Rightarrow> bool" where
  "eqsub a b (Atom P ts) (Atom Q us) \<longleftrightarrow> P = Q \<and> list_all2 (eqsub_t a b) ts us"
| "eqsub a b (Eqf t u) (Eqf t' u') \<longleftrightarrow> eqsub_t a b t t' \<and> eqsub_t a b u u'"
| "eqsub a b Bot Bot \<longleftrightarrow> True"
| "eqsub a b (Neg p) (Neg p') \<longleftrightarrow> eqsub a b p p'"
| "eqsub a b (Conj p q) (Conj p' q') \<longleftrightarrow> eqsub a b p p' \<and> eqsub a b q q'"
| "eqsub a b (Disj p q) (Disj p' q') \<longleftrightarrow> eqsub a b p p' \<and> eqsub a b q q'"
| "eqsub a b (Impl p q) (Impl p' q') \<longleftrightarrow> eqsub a b p p' \<and> eqsub a b q q'"
| "eqsub a b (Iff p q) (Iff p' q') \<longleftrightarrow> eqsub a b p p' \<and> eqsub a b q q'"
| "eqsub a b (Uni x p) (Uni y p') \<longleftrightarrow> x = y \<and> eqsub a b p p'"
| "eqsub a b (Exi x p) (Exi y p') \<longleftrightarrow> x = y \<and> eqsub a b p p'"
| "eqsub a b _ _ \<longleftrightarrow> False"

subsection \<open>Assumptions of a line\<close>

definition depFms :: "lemmon_proof \<Rightarrow> nat set \<Rightarrow> fm list" where
  "depFms E G = map formula (filter (\<lambda>l. lineNumber l \<in> G) E)"

definition isAssumptionLine :: "lemmon_proof \<Rightarrow> nat \<Rightarrow> bool" where
  "isAssumptionLine E a \<longleftrightarrow> justAt E a = Some Assumption"

text \<open>@{text ruleOK} takes the list of assumption formulas its side conditions
  range over as a parameter.  Lemmon supplies the assumptions the line rests on
  (@{text depFms}); Fitch, having no record of those, supplies the assumptions
  in scope.  That single substitution is the whole difference between the two
  systems' rule checks, and Section 6.2 of the paper is the observation that it
  matters at exactly one rule.\<close>

fun ruleOK :: "lemmon_proof \<Rightarrow> fm \<Rightarrow> fm list \<Rightarrow> just \<Rightarrow> bool" where
  "ruleOK E phi As Assumption \<longleftrightarrow> True"
| "ruleOK E phi As (MP i j) \<longleftrightarrow>
     (case fmAt E i of Some (Impl p q) \<Rightarrow> fmAt E j = Some p \<and> phi = q | _ \<Rightarrow> False)"
| "ruleOK E phi As (CP a c) \<longleftrightarrow>
     isAssumptionLine E a \<and>
     (case (fmAt E a, fmAt E c) of (Some p, Some q) \<Rightarrow> phi = Impl p q | _ \<Rightarrow> False)"
| "ruleOK E phi As (RAA a c) \<longleftrightarrow>
     isAssumptionLine E a \<and> fmAt E c = Some Bot \<and>
     (case fmAt E a of Some p \<Rightarrow> phi = Neg p | _ \<Rightarrow> False)"
| "ruleOK E phi As (DN i) \<longleftrightarrow> fmAt E i = Some (Neg (Neg phi))"
| "ruleOK E phi As (BotI i j) \<longleftrightarrow>
     phi = Bot \<and> (case fmAt E i of Some p \<Rightarrow> fmAt E j = Some (Neg p) | _ \<Rightarrow> False)"
| "ruleOK E phi As (AndIntro i j) \<longleftrightarrow>
     (case phi of Conj p q \<Rightarrow> fmAt E i = Some p \<and> fmAt E j = Some q | _ \<Rightarrow> False)"
| "ruleOK E phi As (AndElimL i) \<longleftrightarrow>
     (case fmAt E i of Some (Conj p q) \<Rightarrow> phi = p | _ \<Rightarrow> False)"
| "ruleOK E phi As (AndElimR i) \<longleftrightarrow>
     (case fmAt E i of Some (Conj p q) \<Rightarrow> phi = q | _ \<Rightarrow> False)"
| "ruleOK E phi As (OrIntroL i) \<longleftrightarrow>
     (case phi of Disj p q \<Rightarrow> fmAt E i = Some p | _ \<Rightarrow> False)"
| "ruleOK E phi As (OrIntroR i) \<longleftrightarrow>
     (case phi of Disj p q \<Rightarrow> fmAt E i = Some q | _ \<Rightarrow> False)"
| "ruleOK E phi As (OrElim d a1 c1 a2 c2) \<longleftrightarrow>
     isAssumptionLine E a1 \<and> isAssumptionLine E a2 \<and>
     fmAt E c1 = Some phi \<and> fmAt E c2 = Some phi \<and>
     (case fmAt E d of Some (Disj p q) \<Rightarrow> fmAt E a1 = Some p \<and> fmAt E a2 = Some q
        | _ \<Rightarrow> False)"
| "ruleOK E phi As (IffIntro i j) \<longleftrightarrow>
     (case phi of Iff p q \<Rightarrow> fmAt E i = Some (Impl p q) \<and> fmAt E j = Some (Impl q p)
        | _ \<Rightarrow> False)"
| "ruleOK E phi As (IffElimL i) \<longleftrightarrow>
     (case phi of Impl p q \<Rightarrow> fmAt E i = Some (Iff p q) | _ \<Rightarrow> False)"
| "ruleOK E phi As (IffElimR i) \<longleftrightarrow>
     (case phi of Impl q p \<Rightarrow> fmAt E i = Some (Iff p q) | _ \<Rightarrow> False)"
| "ruleOK E phi As (ForallElim i) \<longleftrightarrow>
     (case fmAt E i of Some (Uni x p) \<Rightarrow> instOK x p phi | _ \<Rightarrow> False)"
| "ruleOK E phi As (ForallIntro i) \<longleftrightarrow>
     (case (phi, fmAt E i) of
        (Uni x p, Some psi) \<Rightarrow> genOK x p psi As | _ \<Rightarrow> False)"
| "ruleOK E phi As (ExistsIntro i) \<longleftrightarrow>
     (case (phi, fmAt E i) of
        (Exi x p, Some psi) \<Rightarrow> instOK x p psi | _ \<Rightarrow> False)"
| "ruleOK E phi As (ExistsElim m a c) \<longleftrightarrow>
     isAssumptionLine E a \<and> fmAt E c = Some phi \<and>
     (case (fmAt E m, fmAt E a) of
        (Some (Exi x p), Some psi) \<Rightarrow> witOK x p psi phi As
      | _ \<Rightarrow> False)"
| "ruleOK E phi As EqIntro \<longleftrightarrow>
     (case phi of Eqf (Nm a) (Nm b) \<Rightarrow> a = b | _ \<Rightarrow> False)"
| "ruleOK E phi As (EqElim i j) \<longleftrightarrow>
     (case fmAt E i of
        Some (Eqf (Nm a) (Nm b)) \<Rightarrow>
          (case fmAt E j of Some psi \<Rightarrow> eqsub a b psi phi | _ \<Rightarrow> False)
      | _ \<Rightarrow> False)"
| "ruleOK E phi As (Reit i) \<longleftrightarrow> fmAt E i = Some phi"

lemma ruleOK_EqIntro:
  "ruleOK E phi As EqIntro \<longleftrightarrow> (\<exists>a. phi = Eqf (Nm a) (Nm a))"
  by (cases phi; auto split: trm.splits)

text \<open>The side conditions are the only place the assumption list is used, and
  they are antitone in it: shrinking the list of assumptions a name must avoid
  can only license more.  This is the exact sense in which Fitch's coarser
  bookkeeping ``licenses strictly less'' (Section 6.2).\<close>

lemma arbitrary_in_antitone: "set As \<subseteq> set Bs \<Longrightarrow> arbitrary_in a Bs \<Longrightarrow> arbitrary_in a As"
  by (auto simp: arbitrary_in_def)

lemma ruleOK_antitone:
  assumes "set As \<subseteq> set Bs" and "ruleOK E phi Bs j"
  shows "ruleOK E phi As j"
  using assms
  by (cases j; auto simp: genOK_antitone witOK_antitone split: option.splits fm.splits)

lemma ruleOK_indep:
  assumes "\<not> (\<exists>i. j = ForallIntro i) " and "\<not> (\<exists>m a c. j = ExistsElim m a c)"
  shows "ruleOK E phi As j = ruleOK E phi Bs j"
  using assms by (cases j) auto

subsection \<open>The checker\<close>

text \<open>The checker is parametric in where the side conditions get their
  assumptions from: @{term A} is applied to the prefix already checked, the
  number of the line, and its dependency set.  Instantiating @{term A} one way
  gives the Lemmon system, the other way the Fitch system (Section 3).\<close>

subsection \<open>Reiteration is idle\<close>

text \<open>@{const Reit} is not one of the twenty-one, and nothing below assumes it
  away: @{const lemmon_21} is stated, and exported, but is nowhere a hypothesis.
  It need not be.  A correct reiteration line duplicates the line it cites
  exactly --- the same formula, by the rule, and the same dependency set, by the
  arithmetic --- so it can neither prove anything new nor change what any other
  line rests on.  Every use of a reiterated line could cite the original instead.
  @{const Reit} is admitted only so that @{text \<open>\<delta>\<close>} is defined on Fitch proofs
  that use reiteration, which the Lemmon-to-Fitch construction must sometimes
  emit (Section 5.3); @{const lemmon_21} records when a proof has stayed inside
  the real system.\<close>

lemma reit_same_formula: "ruleOK E \<phi> As (Reit i) \<Longrightarrow> fmAt E i = Some \<phi>"
  by simp

lemma reit_same_deps: "depsOf look (Reit i) self = look i"
  by (simp add: depsOf_def)

type_synonym asm_src = "lemmon_proof \<Rightarrow> nat \<Rightarrow> nat set \<Rightarrow> fm list"

definition lineOK_gen :: "asm_src \<Rightarrow> lemmon_proof \<Rightarrow> pline \<Rightarrow> bool" where
  "lineOK_gen A E l \<longleftrightarrow>
     (let G = depsOf (depsAt E) (justification l) (lineNumber l) in
        references l = G \<and>
        list_all (\<lambda>m. lookupLine E m \<noteq> None) (citedLines (justification l)) \<and>
        ruleOK E (formula l) (A E (lineNumber l) G) (justification l))"

fun checkFrom_gen :: "asm_src \<Rightarrow> lemmon_proof \<Rightarrow> lemmon_proof \<Rightarrow> bool" where
  "checkFrom_gen A E [] \<longleftrightarrow> True"
| "checkFrom_gen A E (l # ls) \<longleftrightarrow> lineOK_gen A E l \<and> checkFrom_gen A (E @ [l]) ls"

definition depSrc :: asm_src where
  "depSrc E n G = depFms E G"

abbreviation "lineOK \<equiv> lineOK_gen depSrc"
abbreviation "checkFrom \<equiv> checkFrom_gen depSrc"

definition lemmonCorrect :: "lemmon_proof \<Rightarrow> bool" where
  "lemmonCorrect P \<longleftrightarrow> sorted_wrt (<) (map lineNumber P) \<and> checkFrom [] P"

text \<open>Weakening the assumption source weakens the check.\<close>

lemma checkFrom_gen_antitone:
  assumes "\<And>E n G. set (A E n G) \<subseteq> set (B E n G)"
  shows "checkFrom_gen B E P \<Longrightarrow> checkFrom_gen A E P"
proof (induction P arbitrary: E)
  case (Cons l ls)
  from Cons.prems have "lineOK_gen B E l" and "checkFrom_gen B (E @ [l]) ls" by auto
  from \<open>lineOK_gen B E l\<close> have "lineOK_gen A E l"
    unfolding lineOK_gen_def Let_def
    using ruleOK_antitone [OF assms] by blast
  with Cons.IH [OF \<open>checkFrom_gen B (E @ [l]) ls\<close>] show ?case by simp
qed simp

subsection \<open>Conclusion and premises\<close>

definition conclusion :: "lemmon_proof \<Rightarrow> fm option" where
  "conclusion P = (if P = [] then None else Some (formula (last P)))"

definition openPremises :: "lemmon_proof \<Rightarrow> fm list" where
  "openPremises P = (if P = [] then [] else depFms P (references (last P)))"

subsection \<open>Readable proof notation\<close>

type_synonym dependency_set = "nat set"
type_synonym lemmon_line = pline
type_synonym proof_justification = just

text \<open>A Lemmon line is written in the order used in the paper:
  dependency set, line number, formula, justification.  The implementation
  constructor stores the dependency set last; this notation removes that
  presentational mismatch.\<close>

abbreviation lemmonLine ::
    "dependency_set \<Rightarrow> nat \<Rightarrow> fm \<Rightarrow> just \<Rightarrow> pline"
    (\<open>\<langle>_,/ _,/ _,/ _\<rangle>\<^sub>L\<close>) where
  "\<langle>G, n, p, j\<rangle>\<^sub>L \<equiv> ProofLine n p j G"

subsection \<open>Descriptive aliases\<close>

text \<open>These aliases are intended for expository statements.  The short names
  remain convenient inside recursive definitions and proofs.\<close>

abbreviation dependencies :: "pline \<Rightarrow> dependency_set" where
  "dependencies l \<equiv> references l"

abbreviation formulaAt :: "lemmon_proof \<Rightarrow> nat \<Rightarrow> fm option" where
  "formulaAt P n \<equiv> fmAt P n"

abbreviation dependenciesAt :: "lemmon_proof \<Rightarrow> nat \<Rightarrow> dependency_set" where
  "dependenciesAt P n \<equiv> depsAt P n"

abbreviation dependencyFormulas ::
    "lemmon_proof \<Rightarrow> dependency_set \<Rightarrow> fm list" where
  "dependencyFormulas P G \<equiv> depFms P G"

abbreviation dependenciesFor ::
    "(nat \<Rightarrow> dependency_set) \<Rightarrow> just \<Rightarrow> nat \<Rightarrow> dependency_set" where
  "dependenciesFor look j n \<equiv> depsOf look j n"

abbreviation ruleIsCorrect ::
    "lemmon_proof \<Rightarrow> fm \<Rightarrow> fm list \<Rightarrow> just \<Rightarrow> bool" where
  "ruleIsCorrect P p assumptions j \<equiv> ruleOK P p assumptions j"

abbreviation isCorrectLemmonProof :: "lemmon_proof \<Rightarrow> bool" where
  "isCorrectLemmonProof P \<equiv> lemmonCorrect P"

subsection \<open>The turnstile\<close>

text \<open>The judgement the paper writes \<open>\<Gamma> \<turnstile> \<psi>\<close> is declared in
  \<open>LF_Delta\<close>, after both proof systems are available.  There it becomes the two
  predicates \<open>\<Gamma> \<turnstile>\<^sub>L \<psi>\<close> and \<open>\<Gamma> \<turnstile>\<^sub>F \<psi>\<close>.  Everything the Lemmon
  predicate uses is here: @{const lemmonCorrect}, @{const openPremises}, and
  @{const conclusion}.\<close>

end
