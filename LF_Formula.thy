(*  Title:      LF_Formula.thy
    Author:     formalisation of Halvorson, "Dependency and Scope"

    The object language: terms, formulas, the names occurring in a formula,
    substitution of a name for a variable (instantiation) and of a name for a
    name (renaming).  Names are individual constants; they are closed, so every
    substitution here is capture-free and no alpha-conversion is needed.
*)

theory LF_Formula
  imports Main "HOL-Library.Code_Target_Nat"
begin

section \<open>Terms and formulas\<close>

type_synonym nm = String.literal  \<comment> \<open>individual constants, the ``names''\<close>
type_synonym vr = String.literal  \<comment> \<open>individual variables\<close>
type_synonym pr = String.literal  \<comment> \<open>predicate symbols\<close>

datatype trm = Nm nm | Vr vr

datatype fm =
    Atom pr "trm list"
  | Eqf trm trm
  | Bot
  | Neg fm
  | Conj fm fm
  | Disj fm fm
  | Impl fm fm
  | Iff fm fm
  | Uni vr fm
  | Exi vr fm

subsection \<open>Readable object-language notation\<close>

text \<open>The implementation names are deliberately short because they occur in
  nearly every definition.  The following aliases and symbols provide a
  paper-like input language for statements and examples.  The subscript
  \<open>o\<close> marks an object-language connective and keeps it visibly distinct from
  Isabelle/HOL's meta-language connectives.\<close>

type_synonym individual_name = nm
type_synonym object_variable = vr
type_synonym predicate_symbol = pr
type_synonym object_term = trm
type_synonym formula = fm

abbreviation namedTerm :: "nm \<Rightarrow> trm" where
  "namedTerm a \<equiv> Nm a"

abbreviation variableTerm :: "vr \<Rightarrow> trm" where
  "variableTerm x \<equiv> Vr x"

abbreviation falsum :: fm (\<open>\<bottom>\<^sub>o\<close>) where
  "\<bottom>\<^sub>o \<equiv> Bot"

abbreviation verum :: fm (\<open>\<top>\<^sub>o\<close>) where
  "\<top>\<^sub>o \<equiv> Neg Bot"

abbreviation objectNegation :: "fm \<Rightarrow> fm" (\<open>\<not>\<^sub>o _\<close> [40] 40) where
  "\<not>\<^sub>o p \<equiv> Neg p"

abbreviation objectConjunction :: "fm \<Rightarrow> fm \<Rightarrow> fm"
    (infixr \<open>\<and>\<^sub>o\<close> 35) where
  "p \<and>\<^sub>o q \<equiv> Conj p q"

abbreviation objectDisjunction :: "fm \<Rightarrow> fm \<Rightarrow> fm"
    (infixr \<open>\<or>\<^sub>o\<close> 30) where
  "p \<or>\<^sub>o q \<equiv> Disj p q"

abbreviation objectImplication :: "fm \<Rightarrow> fm \<Rightarrow> fm"
    (infixr \<open>\<longrightarrow>\<^sub>o\<close> 25) where
  "p \<longrightarrow>\<^sub>o q \<equiv> Impl p q"

abbreviation objectBiconditional :: "fm \<Rightarrow> fm \<Rightarrow> fm"
    (infixr \<open>\<longleftrightarrow>\<^sub>o\<close> 25) where
  "p \<longleftrightarrow>\<^sub>o q \<equiv> Iff p q"

abbreviation objectEquality :: "trm \<Rightarrow> trm \<Rightarrow> fm"
    (infix \<open>=\<^sub>o\<close> 50) where
  "t =\<^sub>o u \<equiv> Eqf t u"

abbreviation objectUniversal :: "vr \<Rightarrow> fm \<Rightarrow> fm"
    (\<open>\<forall>\<^sub>o _./ _\<close> [0, 10] 10) where
  "\<forall>\<^sub>o x. p \<equiv> Uni x p"

abbreviation objectExistential :: "vr \<Rightarrow> fm \<Rightarrow> fm"
    (\<open>\<exists>\<^sub>o _./ _\<close> [0, 10] 10) where
  "\<exists>\<^sub>o x. p \<equiv> Exi x p"

subsection \<open>Names\<close>

fun names_t :: "trm \<Rightarrow> nm list" where
  "names_t (Nm a) = [a]"
| "names_t (Vr _) = []"

fun names :: "fm \<Rightarrow> nm list" where
  "names (Atom _ ts) = concat (map names_t ts)"
| "names (Eqf t u) = names_t t @ names_t u"
| "names Bot = []"
| "names (Neg p) = names p"
| "names (Conj p q) = names p @ names q"
| "names (Disj p q) = names p @ names q"
| "names (Impl p q) = names p @ names q"
| "names (Iff p q) = names p @ names q"
| "names (Uni _ p) = names p"
| "names (Exi _ p) = names p"

abbreviation occurs :: "nm \<Rightarrow> fm \<Rightarrow> bool" where
  "occurs a p \<equiv> a \<in> set (names p)"

subsection \<open>Free variables\<close>

fun fvs_t :: "trm \<Rightarrow> vr list" where
  "fvs_t (Nm _) = []"
| "fvs_t (Vr x) = [x]"

fun fvs :: "fm \<Rightarrow> vr list" where
  "fvs (Atom _ ts) = concat (map fvs_t ts)"
| "fvs (Eqf t u) = fvs_t t @ fvs_t u"
| "fvs Bot = []"
| "fvs (Neg p) = fvs p"
| "fvs (Conj p q) = fvs p @ fvs q"
| "fvs (Disj p q) = fvs p @ fvs q"
| "fvs (Impl p q) = fvs p @ fvs q"
| "fvs (Iff p q) = fvs p @ fvs q"
| "fvs (Uni x p) = removeAll x (fvs p)"
| "fvs (Exi x p) = removeAll x (fvs p)"

definition sentence :: "fm \<Rightarrow> bool" where
  "sentence p \<longleftrightarrow> fvs p = []"

subsection \<open>Instantiation: replace a free variable by a name\<close>

fun inst_t :: "vr \<Rightarrow> nm \<Rightarrow> trm \<Rightarrow> trm" where
  "inst_t x a (Nm b) = Nm b"
| "inst_t x a (Vr y) = (if x = y then Nm a else Vr y)"

fun inst :: "vr \<Rightarrow> nm \<Rightarrow> fm \<Rightarrow> fm" where
  "inst x a (Atom P ts) = Atom P (map (inst_t x a) ts)"
| "inst x a (Eqf t u) = Eqf (inst_t x a t) (inst_t x a u)"
| "inst x a Bot = Bot"
| "inst x a (Neg p) = Neg (inst x a p)"
| "inst x a (Conj p q) = Conj (inst x a p) (inst x a q)"
| "inst x a (Disj p q) = Disj (inst x a p) (inst x a q)"
| "inst x a (Impl p q) = Impl (inst x a p) (inst x a q)"
| "inst x a (Iff p q) = Iff (inst x a p) (inst x a q)"
| "inst x a (Uni y p) = Uni y (if x = y then p else inst x a p)"
| "inst x a (Exi y p) = Exi y (if x = y then p else inst x a p)"

subsection \<open>Renaming: replace a name by a name\<close>

fun rn_t :: "nm \<Rightarrow> nm \<Rightarrow> trm \<Rightarrow> trm" where
  "rn_t a b (Nm c) = Nm (if c = a then b else c)"
| "rn_t a b (Vr y) = Vr y"

fun rn :: "nm \<Rightarrow> nm \<Rightarrow> fm \<Rightarrow> fm" where
  "rn a b (Atom P ts) = Atom P (map (rn_t a b) ts)"
| "rn a b (Eqf t u) = Eqf (rn_t a b t) (rn_t a b u)"
| "rn a b Bot = Bot"
| "rn a b (Neg p) = Neg (rn a b p)"
| "rn a b (Conj p q) = Conj (rn a b p) (rn a b q)"
| "rn a b (Disj p q) = Disj (rn a b p) (rn a b q)"
| "rn a b (Impl p q) = Impl (rn a b p) (rn a b q)"
| "rn a b (Iff p q) = Iff (rn a b p) (rn a b q)"
| "rn a b (Uni y p) = Uni y (rn a b p)"
| "rn a b (Exi y p) = Exi y (rn a b p)"

subsection \<open>Descriptive aliases\<close>

abbreviation namesInTerm :: "trm \<Rightarrow> nm list" where
  "namesInTerm t \<equiv> names_t t"

abbreviation namesInFormula :: "fm \<Rightarrow> nm list" where
  "namesInFormula p \<equiv> names p"

abbreviation freeVariablesInTerm :: "trm \<Rightarrow> vr list" where
  "freeVariablesInTerm t \<equiv> fvs_t t"

abbreviation freeVariablesInFormula :: "fm \<Rightarrow> vr list" where
  "freeVariablesInFormula p \<equiv> fvs p"

abbreviation isSentence :: "fm \<Rightarrow> bool" where
  "isSentence p \<equiv> sentence p"

abbreviation instantiateTerm :: "vr \<Rightarrow> nm \<Rightarrow> trm \<Rightarrow> trm" where
  "instantiateTerm x a t \<equiv> inst_t x a t"

abbreviation instantiateFormula :: "vr \<Rightarrow> nm \<Rightarrow> fm \<Rightarrow> fm" where
  "instantiateFormula x a p \<equiv> inst x a p"

abbreviation renameInTerm :: "nm \<Rightarrow> nm \<Rightarrow> trm \<Rightarrow> trm" where
  "renameInTerm a b t \<equiv> rn_t a b t"

abbreviation renameInFormula :: "nm \<Rightarrow> nm \<Rightarrow> fm \<Rightarrow> fm" where
  "renameInFormula a b p \<equiv> rn a b p"

text \<open>The paper writes \<open>\<psi>[b/a]\<close> for the result of putting @{term b} for @{term a}
  throughout @{term \<psi>}, and we write it too.  These are abbreviations, so the term
  is still @{term "rn a b \<psi>"} and nothing proved about @{const rn} needs restating;
  the brackets are only how it is displayed and how it may be written.  The same
  notation serves for a term, a formula and a list of formulas, and (in
  \<open>LF_Derivation\<close>) for a derivation --- which of them is meant is settled by the
  type.\<close>

text \<open>One precaution first.  \<open>t[b/a]\<close> would otherwise be ambiguous: it also reads
  as @{term t} applied to the singleton list \<open>[b / a]\<close>, since \<open>/\<close> is an infix for
  division, and both readings type-check whenever the types are not already
  pinned down.  Nothing in this development divides anything, so we take the
  infix away and the bracket becomes the only reading.  The guard lemmas below
  are trivially true and are there to fail loudly if that ever stops holding.\<close>

no_notation inverse_divide  (infixl \<open>'/\<close> 70)

abbreviation rn_t_syn :: "trm \<Rightarrow> nm \<Rightarrow> nm \<Rightarrow> trm"  (\<open>_[_'/_]\<close> [1000, 0, 0] 1000)
  where "t[b/a] \<equiv> rn_t a b t"

abbreviation rn_syn :: "fm \<Rightarrow> nm \<Rightarrow> nm \<Rightarrow> fm"  (\<open>_[_'/_]\<close> [1000, 0, 0] 1000)
  where "p[b/a] \<equiv> rn a b p"

abbreviation rn_fms_syn :: "fm list \<Rightarrow> nm \<Rightarrow> nm \<Rightarrow> fm list"  (\<open>_[_'/_]\<close> [1000, 0, 0] 1000)
  where "G[b/a] \<equiv> map (rn a b) G"

text \<open>Guards.  Each fails to parse if the bracket ever becomes ambiguous again.\<close>

lemma bracket_trm: "(t :: trm)[b/a] = rn_t a b t" by (rule refl)
lemma bracket_fm:  "(p :: fm)[b/a] = rn a b p" by (rule refl)
lemma bracket_fms: "(G :: fm list)[b/a] = map (rn a b) G" by (rule refl)


subsection \<open>Basic facts\<close>

lemma names_rn_t: "set (names_t (rn_t a b t)) = (\<lambda>c. if c = a then b else c) ` set (names_t t)"
  by (cases t) auto

lemma names_rn: "set (names (rn a b p)) = (\<lambda>c. if c = a then b else c) ` set (names p)"
  by (induction p) (auto simp: names_rn_t image_Un)

lemma rn_t_id [simp]: "a \<notin> set (names_t t) \<Longrightarrow> rn_t a b t = t"
  by (cases t) auto

lemma rn_id [simp]: "\<not> occurs a p \<Longrightarrow> rn a b p = p"
  by (induction p) (auto intro: map_idI)

lemma rn_t_self [simp]: "rn_t a a t = t"
  by (cases t) auto

lemma rn_self [simp]: "rn a a p = p"
  by (induction p) (auto intro: map_idI)

text \<open>Renaming commutes with instantiation; this is the step the quantifier
  cases of the Renaming Lemma turn on.\<close>

lemma rn_inst_t:
  "rn_t a b (inst_t x c t) = inst_t x (if c = a then b else c) (rn_t a b t)"
  by (cases t) auto

lemma rn_inst: "rn a b (inst x c p) = inst x (if c = a then b else c) (rn a b p)"
  by (induction p) (auto simp: rn_inst_t)

lemma occurs_inst_t:
  "d \<in> set (names_t (inst_t x c t)) \<longleftrightarrow> (d \<in> set (names_t t) \<or> (d = c \<and> x \<in> set (fvs_t t)))"
  by (cases t) auto

lemma occurs_inst: "occurs d (inst x c p) \<longleftrightarrow> (occurs d p \<or> (d = c \<and> x \<in> set (fvs p)))"
  by (induction p) (auto simp: occurs_inst_t)

lemma fvs_rn_t [simp]: "fvs_t (rn_t a b t) = fvs_t t"
  by (cases t) auto

lemma fvs_rn [simp]: "fvs (rn a b p) = fvs p"
  by (induction p) (auto simp: comp_def)

lemma inst_t_notfree [simp]: "x \<notin> set (fvs_t t) \<Longrightarrow> inst_t x c t = t"
  by (cases t) auto

lemma inst_notfree: "x \<notin> set (fvs p) \<Longrightarrow> inst x c p = p"
  by (induction p) (auto intro: map_idI)

lemma names_inst_t: "set (names_t (inst_t x c t)) \<subseteq> insert c (set (names_t t))"
  by (cases t) auto

lemma names_inst: "set (names (inst x c p)) \<subseteq> insert c (set (names p))"
  by (induction p) (auto dest!: names_inst_t [THEN subsetD])

subsection \<open>Fresh names\<close>

text \<open>A name longer than every name in the given list is fresh for that list.
  This is the only place we look inside a name.\<close>

definition nlen :: "nm \<Rightarrow> nat" where
  "nlen a = size (String.explode a)"

definition maxlen :: "nm list \<Rightarrow> nat" where
  "maxlen used = foldr (\<lambda>a n. max n (nlen a)) used 0"

definition fresh_for :: "nm list \<Rightarrow> nm" where
  "fresh_for used = String.implode (replicate (Suc (maxlen used)) CHR ''c'')"

lemma nlen_fresh_for [simp]: "nlen (fresh_for used) = Suc (maxlen used)"
  by (simp add: nlen_def fresh_for_def)

lemma maxlen_ge: "a \<in> set used \<Longrightarrow> nlen a \<le> maxlen used"
  by (induction used) (auto simp: maxlen_def)

lemma fresh_for_fresh: "fresh_for used \<notin> set used"
  using maxlen_ge [of "fresh_for used" used] by auto

text \<open>The generic freshness interface used by the translation: a name occurring
  in none of a list of formulas.\<close>

definition fresh_for_fms :: "fm list \<Rightarrow> nm" where
  "fresh_for_fms ps = fresh_for (concat (map names ps))"

lemma fresh_for_fms: "p \<in> set ps \<Longrightarrow> \<not> occurs (fresh_for_fms ps) p"
  using fresh_for_fresh [of "concat (map names ps)"]
  by (auto simp: fresh_for_fms_def)

end
