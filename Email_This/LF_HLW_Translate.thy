(*  Title:      LF_HLW_Translate.thy

    The direct Lemmon-to-Fitch half of the authoritative FitchConvert.hs
    interface, operating on the exact HL_ datatypes.  The handwritten program's
    structural diagnostics are retained and supplemented by the four checks
    found necessary in the Isabelle positional-translation audit.
*)

theory LF_HLW_Translate
  imports LF_HLW_DNF
begin

section \<open>Translation diagnostics\<close>

datatype hl_translation_error =
    HL_NotNested int int "int list"
  | HL_OutOfScope int int int
  | HL_UnknownAssumption int int
  | HL_MissingLine int
  | HL_EigenInScope int hl_name int
  | HL_PremiseInBox int int
  | HL_PremiseLate int int
  | HL_BoxReversed int int
  | HL_AssumptionReused int int int
  | HL_SourceNotVerified int
  | HL_TargetNotVerified

fun hlToFitchRule :: "hl_justification \<Rightarrow> hl_fitch_rule" where
  "hlToFitchRule HL_Assumption = HL_FPremise"
| "hlToFitchRule (HL_MP m n) = HL_FMP m n"
| "hlToFitchRule (HL_MT m n) = HL_FMT m n"
| "hlToFitchRule (HL_DN m) = HL_FDN m"
| "hlToFitchRule (HL_CP a c) = HL_FCP (a,c)"
| "hlToFitchRule (HL_AndIntro m n) = HL_FAndI m n"
| "hlToFitchRule (HL_AndElim m) = HL_FAndE m"
| "hlToFitchRule (HL_OrIntro m) = HL_FOrI m"
| "hlToFitchRule (HL_OrElim d a1 c1 a2 c2) =
     HL_FOrE d (a1,c1) (a2,c2)"
| "hlToFitchRule (HL_RAA a c) = HL_FRAA (a,c)"
| "hlToFitchRule (HL_ForallElim m) = HL_FForallE m"
| "hlToFitchRule (HL_ExistsIntro m) = HL_FExistsI m"
| "hlToFitchRule (HL_ForallIntro m) = HL_FForallI m"
| "hlToFitchRule (HL_ExistsElim m a c) = HL_FExistsE m (a,c)"
| "hlToFitchRule HL_EqIntro = HL_FEqI"
| "hlToFitchRule (HL_EqElim m n) = HL_FEqE m n"
| "hlToFitchRule HL_LEM = HL_FLEM"
| "hlToFitchRule (HL_PropTaut ms) = HL_FPropTaut ms"
| "hlToFitchRule (HL_IffIntro m n) = HL_FIffI m n"
| "hlToFitchRule (HL_IffElim m n) = HL_FIffE m n"
| "hlToFitchRule (HL_QN m) = HL_FQN m"

lemma hl_rule_maps_round_trip [simp]:
  "hlToLemmonRule (hlToFitchRule j) = j"
  by (cases j) auto

section \<open>Boxes and their placement\<close>

definition hlBoxesOf :: "hl_proof \<Rightarrow> (int \<times> int) list" where
  "hlBoxesOf P = concat (map (hlDischargePairs \<circ> hlJustification) P)"

definition hlDischargedAssumptions :: "hl_proof \<Rightarrow> int list" where
  "hlDischargedAssumptions P = map fst (hlBoxesOf P)"

definition hlDischargerOf :: "hl_proof \<Rightarrow> int \<times> int \<Rightarrow> int" where
  "hlDischargerOf P ac =
     (case find (\<lambda>l. ac \<in> set (hlDischargePairs (hlJustification l))) P of
        Some l \<Rightarrow> hlLineNumber l
      | None \<Rightarrow> 0)"

definition hlBoxPath :: "hl_proof \<Rightarrow> int \<Rightarrow> int list" where
  "hlBoxPath P m =
     sort (map fst (filter (\<lambda>ac. fst ac \<le> m \<and> m \<le> snd ac)
       (hlBoxesOf P)))"

definition hlBoxOrderError :: "hl_proof \<Rightarrow> hl_translation_error option" where
  "hlBoxOrderError P =
     (case filter (\<lambda>ac. snd ac < fst ac) (hlBoxesOf P) of
        [] \<Rightarrow> None
      | ac # _ \<Rightarrow> Some (HL_BoxReversed (fst ac) (snd ac)))"

definition hlBoxHeadError :: "hl_proof \<Rightarrow> hl_translation_error option" where
  "hlBoxHeadError P =
     (case filter
       (\<lambda>x. fst (fst x) = fst (snd x) \<and> snd (fst x) \<noteq> snd (snd x))
       (List.product (hlBoxesOf P) (hlBoxesOf P)) of
        [] \<Rightarrow> None
      | x # _ \<Rightarrow>
          Some (HL_AssumptionReused
            (fst (fst x)) (snd (fst x)) (snd (snd x))))"

definition hlOverlapping ::
    "int \<times> int \<Rightarrow> int \<times> int \<Rightarrow> bool" where
  "hlOverlapping ac bd \<longleftrightarrow>
     fst ac < fst bd \<and> fst bd \<le> snd ac \<and> snd ac < snd bd"

definition hlNestingError :: "hl_proof \<Rightarrow> hl_translation_error option" where
  "hlNestingError P =
     (case filter (\<lambda>ac. \<exists>bd \<in> set (hlBoxesOf P). hlOverlapping ac bd)
       (hlBoxesOf P) of
        [] \<Rightarrow> None
      | ac # _ \<Rightarrow>
          Some (HL_NotNested (hlDischargerOf P ac) (fst ac)
            (map fst (filter (hlOverlapping ac) (hlBoxesOf P)))))"

definition hlIsPremiseLine :: "hl_proof \<Rightarrow> hl_line \<Rightarrow> bool" where
  "hlIsPremiseLine P l \<longleftrightarrow>
     hlJustification l = HL_Assumption \<and>
     hlLineNumber l \<notin> set (hlDischargedAssumptions P)"

definition hlPremiseError :: "hl_proof \<Rightarrow> hl_translation_error option" where
  "hlPremiseError P =
     (case filter (\<lambda>l. hlIsPremiseLine P l \<and>
                       hlBoxPath P (hlLineNumber l) \<noteq> []) P of
        [] \<Rightarrow> None
      | l # _ \<Rightarrow>
          Some (HL_PremiseInBox (hlLineNumber l)
            (last (hlBoxPath P (hlLineNumber l)))))"

definition hlPremiseOrderError :: "hl_proof \<Rightarrow> hl_translation_error option" where
  "hlPremiseOrderError P =
     (let rest = dropWhile (hlIsPremiseLine P) P
      in case filter (hlIsPremiseLine P) rest of
           [] \<Rightarrow> None
         | l # _ \<Rightarrow>
             (case rest of
                [] \<Rightarrow> None
              | e # _ \<Rightarrow>
                  Some (HL_PremiseLate (hlLineNumber l) (hlLineNumber e))))"

section \<open>Scope diagnostics\<close>

fun hlIsPrefix :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool" where
  "hlIsPrefix [] ys \<longleftrightarrow> True"
| "hlIsPrefix (x # xs) [] \<longleftrightarrow> False"
| "hlIsPrefix (x # xs) (y # ys) \<longleftrightarrow>
     x = y \<and> hlIsPrefix xs ys"

fun hlFirstDifference :: "int list \<Rightarrow> int list \<Rightarrow> int" where
  "hlFirstDifference [] ys = 0"
| "hlFirstDifference (x # xs) [] = x"
| "hlFirstDifference (x # xs) (y # ys) =
     (if x = y then hlFirstDifference xs ys else x)"

definition hlBadCitations :: "hl_proof \<Rightarrow> (int \<times> int) list" where
  "hlBadCitations P =
     concat (map (\<lambda>l.
       map (Pair (hlLineNumber l))
         (filter (\<lambda>m.
            \<not> hlIsPrefix (hlBoxPath P m) (hlBoxPath P (hlLineNumber l)))
          (hlFitchCitedLines (hlToFitchRule (hlJustification l))))) P)"

definition hlScopeError :: "hl_proof \<Rightarrow> hl_translation_error option" where
  "hlScopeError P =
     (case hlBadCitations P of
        [] \<Rightarrow> None
      | (n,m) # _ \<Rightarrow>
          Some (HL_OutOfScope n m
            (hlFirstDifference (hlBoxPath P m) (hlBoxPath P n))))"

definition hlSubproofLevel ::
    "hl_proof \<Rightarrow> int \<times> int \<Rightarrow> int list" where
  "hlSubproofLevel P ac = removeAll (fst ac) (hlBoxPath P (fst ac))"

definition hlBadSubproofCitations ::
    "hl_proof \<Rightarrow> (int \<times> int \<times> int) list" where
  "hlBadSubproofCitations P =
     concat (map (\<lambda>l.
       map (\<lambda>ac. (hlLineNumber l,snd ac,fst ac))
         (filter (\<lambda>ac.
            hlBoxPath P (hlLineNumber l) \<noteq> hlSubproofLevel P ac)
          (hlDischargePairs (hlJustification l)))) P)"

definition hlSubproofScopeError ::
    "hl_proof \<Rightarrow> hl_translation_error option" where
  "hlSubproofScopeError P =
     (case hlBadSubproofCitations P of
        [] \<Rightarrow> None
      | (n,c,a) # _ \<Rightarrow> Some (HL_OutOfScope n c a))"

fun hlGeneralizedConstants :: "hl_proof \<Rightarrow> hl_line \<Rightarrow> hl_name list" where
  "hlGeneralizedConstants P (HL_ProofLine n goal (HL_ForallIntro m) G) =
     (case hlLookupLine P m of
        None \<Rightarrow> []
      | Some source \<Rightarrow>
          sorted_list_of_set
            (hlConstantsInFormula (hlFormula source) -
             hlConstantsInFormula goal))"
| "hlGeneralizedConstants P (HL_ProofLine n goal (HL_ExistsElim m a c) G) =
     (case (hlFormulaAt P m, hlFormulaAt P a) of
        (Some source, Some assumption) \<Rightarrow>
          sorted_list_of_set
            (hlConstantsInFormula assumption -
              (hlConstantsInFormula source \<union> hlConstantsInFormula goal))
      | _ \<Rightarrow> [])"
| "hlGeneralizedConstants P l = []"

definition hlEigenScopeAssumptions :: "hl_proof \<Rightarrow> hl_line \<Rightarrow> int list" where
  "hlEigenScopeAssumptions P l =
     (let n = hlLineNumber l;
          premises = map hlLineNumber
            (filter (\<lambda>p. hlIsPremiseLine P p \<and> hlLineNumber p < n) P)
      in premises @
         (case hlJustification l of
            HL_ExistsElim m a c \<Rightarrow> removeAll a (hlBoxPath P c)
          | _ \<Rightarrow> hlBoxPath P n))"

definition hlEigenScopeViolations ::
    "hl_proof \<Rightarrow> (int \<times> hl_name \<times> int) list" where
  "hlEigenScopeViolations P =
     concat (map (\<lambda>l.
       concat (map (\<lambda>a.
         map (\<lambda>c. (hlLineNumber l,c,a))
           (filter (\<lambda>c.
             case hlFormulaAt P a of
               None \<Rightarrow> False
             | Some assumption \<Rightarrow>
                 c \<in> hlConstantsInFormula assumption)
             (hlGeneralizedConstants P l)))
         (hlEigenScopeAssumptions P l))) P)"

definition hlEigenScopeError ::
    "hl_proof \<Rightarrow> hl_translation_error option" where
  "hlEigenScopeError P =
     (case hlEigenScopeViolations P of
        [] \<Rightarrow> None
      | (n,c,a) # _ \<Rightarrow> Some (HL_EigenInScope n c a))"

section \<open>The exact direct translation\<close>

function (sequential) hlBuildFitchItems ::
    "(int \<times> int) list \<Rightarrow> hl_proof \<Rightarrow> hl_fitch_proof" where
  "hlBuildFitchItems boxes [] = []"
| "hlBuildFitchItems boxes (l # ls) =
     (case find (\<lambda>ac. fst ac = hlLineNumber l) boxes of
        None \<Rightarrow>
          HL_FLine (hlLineNumber l) (hlFormula l)
            (hlToFitchRule (hlJustification l)) #
          hlBuildFitchItems boxes ls
      | Some ac \<Rightarrow>
          HL_FSub (HL_Subproof (hlLineNumber l) (hlFormula l)
            (hlBuildFitchItems boxes
              (takeWhile (\<lambda>l'. hlLineNumber l' \<le> snd ac) ls))) #
          hlBuildFitchItems boxes
            (dropWhile (\<lambda>l'. hlLineNumber l' \<le> snd ac) ls))"
  by pat_completeness auto

termination
  by (relation "measure (\<lambda>(boxes,ls). length ls)")
     (auto simp: le_imp_less_Suc length_takeWhile_le
       intro: le_less_trans[OF length_dropWhile_le])

definition hlLemmonToFitchDirect ::
    "hl_proof \<Rightarrow> hl_translation_error + hl_fitch_proof" where
  "hlLemmonToFitchDirect P =
     (if \<not> hlVerifiedCorrect P then Inl (HL_SourceNotVerified 0)
      else case hlBoxOrderError P of Some e \<Rightarrow> Inl e | None \<Rightarrow>
       (case hlBoxHeadError P of Some e \<Rightarrow> Inl e | None \<Rightarrow>
        (case hlNestingError P of Some e \<Rightarrow> Inl e | None \<Rightarrow>
         (case hlPremiseError P of Some e \<Rightarrow> Inl e | None \<Rightarrow>
          (case hlScopeError P of Some e \<Rightarrow> Inl e | None \<Rightarrow>
           (case hlSubproofScopeError P of Some e \<Rightarrow> Inl e | None \<Rightarrow>
            (case hlPremiseOrderError P of Some e \<Rightarrow> Inl e | None \<Rightarrow>
             (case hlEigenScopeError P of Some e \<Rightarrow> Inl e | None \<Rightarrow>
               Inr (hlBuildFitchItems (hlBoxesOf P) P)))))))))"

lemma hlBuildFitchItems_positional:
  "map (\<lambda>(n,p,r). (n,p)) (hlFlattenFitch (hlBuildFitchItems boxes P)) =
   map (\<lambda>l. (hlLineNumber l,hlFormula l)) P"
proof (induction boxes P rule: hlBuildFitchItems.induct)
  case (2 boxes l ls)
  show ?case
  proof (cases "find (\<lambda>ac. fst ac = hlLineNumber l) boxes")
    case None
    with 2 show ?thesis by simp
  next
    case (Some ac)
    let ?inside = "takeWhile (\<lambda>l'. hlLineNumber l' \<le> snd ac) ls"
    let ?after = "dropWhile (\<lambda>l'. hlLineNumber l' \<le> snd ac) ls"
    from 2(2)[OF Some] 2(3)[OF Some] Some
    show ?thesis
      by (simp, metis map_append takeWhile_dropWhile_id)
  qed
qed simp

theorem hlLemmonToFitchDirect_positional:
  assumes "hlLemmonToFitchDirect P = Inr F"
  shows "map (\<lambda>(n,p,r). (n,p)) (hlFlattenFitch F) =
         map (\<lambda>l. (hlLineNumber l,hlFormula l)) P"
  using assms hlBuildFitchItems_positional[of "hlBoxesOf P" P]
  unfolding hlLemmonToFitchDirect_def
  by (auto split: option.splits if_splits)

lemma hl_exact_direct_cp_example:
  "case hlLemmonToFitchDirect hl_cp_example of
     Inl e \<Rightarrow> False
   | Inr F \<Rightarrow> hlFitchVerified F \<and> \<delta>\<^sub>H F = hl_cp_example"
  by eval

end
