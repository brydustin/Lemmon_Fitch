(*  Title:      LF_Halvorson_Unfold.thy

    The derivation-tree fallback of Halvorson's FitchConvert.hs on the exact
    HL_ datatypes.  A verified Lemmon citation DAG is unfolded into a finite
    derivation, then laid out as a Fitch proof.  Local eigenconstant repair is
    performed for both universal introduction and existential elimination.
*)

theory LF_Halvorson_Unfold
  imports LF_Halvorson_Translate
begin

section \<open>Exact derivation trees\<close>

datatype hl_derivation =
  HL_Derivation
    (hlDerivationFormula: hl_formula)
    (hlDerivationRule: hl_derivation_rule)
and hl_derivation_rule =
    HL_DAssume int
  | HL_DPremise int
  | HL_DMP hl_derivation hl_derivation
  | HL_DMT hl_derivation hl_derivation
  | HL_DDN hl_derivation
  | HL_DCP int hl_formula hl_derivation
  | HL_DAndI hl_derivation hl_derivation
  | HL_DAndE hl_derivation
  | HL_DOrI hl_derivation
  | HL_DOrE hl_derivation int hl_formula hl_derivation
      int hl_formula hl_derivation
  | HL_DRAA int hl_formula hl_derivation
  | HL_DForallE hl_derivation
  | HL_DForallI hl_derivation
  | HL_DExistsI hl_derivation
  | HL_DExistsE hl_derivation int hl_formula hl_derivation
  | HL_DEqI
  | HL_DEqE hl_derivation hl_derivation
  | HL_DLEM
  | HL_DPropTaut "hl_derivation list"
  | HL_DIffI hl_derivation hl_derivation
  | HL_DIffE hl_derivation hl_derivation
  | HL_DQN hl_derivation

section \<open>Unfolding the verified citation DAG\<close>

fun hlUnfoldDerivation ::
    "nat \<Rightarrow> hl_proof \<Rightarrow> int \<Rightarrow> hl_derivation option" where
  "hlUnfoldDerivation 0 P n = None"
| "hlUnfoldDerivation (Suc fuel) P n =
     (case hlLookupLine P n of
        None \<Rightarrow> None
      | Some l \<Rightarrow>
          (let phi = hlFormula l;
               node = HL_Derivation phi
           in case hlJustification l of
             HL_Assumption \<Rightarrow>
               Some (node
                 (if n \<in> set (hlDischargedAssumptions P)
                  then HL_DAssume n else HL_DPremise n))
           | HL_MP m k \<Rightarrow>
               (case (hlUnfoldDerivation fuel P m,
                      hlUnfoldDerivation fuel P k) of
                  (Some d1,Some d2) \<Rightarrow> Some (node (HL_DMP d1 d2))
                | _ \<Rightarrow> None)
           | HL_MT m k \<Rightarrow>
               (case (hlUnfoldDerivation fuel P m,
                      hlUnfoldDerivation fuel P k) of
                  (Some d1,Some d2) \<Rightarrow> Some (node (HL_DMT d1 d2))
                | _ \<Rightarrow> None)
           | HL_DN m \<Rightarrow>
               map_option (node \<circ> HL_DDN) (hlUnfoldDerivation fuel P m)
           | HL_CP a c \<Rightarrow>
               (case (hlFormulaAt P a,hlUnfoldDerivation fuel P c) of
                  (Some assumption,Some body) \<Rightarrow>
                    Some (node (HL_DCP a assumption body))
                | _ \<Rightarrow> None)
           | HL_AndIntro m k \<Rightarrow>
               (case (hlUnfoldDerivation fuel P m,
                      hlUnfoldDerivation fuel P k) of
                  (Some d1,Some d2) \<Rightarrow> Some (node (HL_DAndI d1 d2))
                | _ \<Rightarrow> None)
           | HL_AndElim m \<Rightarrow>
               map_option (node \<circ> HL_DAndE) (hlUnfoldDerivation fuel P m)
           | HL_OrIntro m \<Rightarrow>
               map_option (node \<circ> HL_DOrI) (hlUnfoldDerivation fuel P m)
           | HL_OrElim d a1 c1 a2 c2 \<Rightarrow>
               (case (hlUnfoldDerivation fuel P d,hlFormulaAt P a1,
                      hlUnfoldDerivation fuel P c1,hlFormulaAt P a2,
                      hlUnfoldDerivation fuel P c2) of
                  (Some dd,Some f1,Some b1,Some f2,Some b2) \<Rightarrow>
                    Some (node (HL_DOrE dd a1 f1 b1 a2 f2 b2))
                | _ \<Rightarrow> None)
           | HL_RAA a c \<Rightarrow>
               (case (hlFormulaAt P a,hlUnfoldDerivation fuel P c) of
                  (Some assumption,Some body) \<Rightarrow>
                    Some (node (HL_DRAA a assumption body))
                | _ \<Rightarrow> None)
           | HL_ForallElim m \<Rightarrow>
               map_option (node \<circ> HL_DForallE)
                 (hlUnfoldDerivation fuel P m)
           | HL_ExistsIntro m \<Rightarrow>
               map_option (node \<circ> HL_DExistsI)
                 (hlUnfoldDerivation fuel P m)
           | HL_ForallIntro m \<Rightarrow>
               map_option (node \<circ> HL_DForallI)
                 (hlUnfoldDerivation fuel P m)
           | HL_ExistsElim m a c \<Rightarrow>
               (case (hlUnfoldDerivation fuel P m,hlFormulaAt P a,
                      hlUnfoldDerivation fuel P c) of
                  (Some source,Some assumption,Some body) \<Rightarrow>
                    Some (node (HL_DExistsE source a assumption body))
                | _ \<Rightarrow> None)
           | HL_EqIntro \<Rightarrow> Some (node HL_DEqI)
           | HL_EqElim m k \<Rightarrow>
               (case (hlUnfoldDerivation fuel P m,
                      hlUnfoldDerivation fuel P k) of
                  (Some d1,Some d2) \<Rightarrow> Some (node (HL_DEqE d1 d2))
                | _ \<Rightarrow> None)
           | HL_LEM \<Rightarrow> Some (node HL_DLEM)
           | HL_PropTaut ms \<Rightarrow>
               map_option (node \<circ> HL_DPropTaut)
                 (hlSequenceOptions
                   (map (hlUnfoldDerivation fuel P) ms))
           | HL_IffIntro m k \<Rightarrow>
               (case (hlUnfoldDerivation fuel P m,
                      hlUnfoldDerivation fuel P k) of
                  (Some d1,Some d2) \<Rightarrow> Some (node (HL_DIffI d1 d2))
                | _ \<Rightarrow> None)
           | HL_IffElim m k \<Rightarrow>
               (case (hlUnfoldDerivation fuel P m,
                      hlUnfoldDerivation fuel P k) of
                  (Some d1,Some d2) \<Rightarrow> Some (node (HL_DIffE d1 d2))
                | _ \<Rightarrow> None)
           | HL_QN m \<Rightarrow>
               map_option (node \<circ> HL_DQN)
                 (hlUnfoldDerivation fuel P m)))"

text \<open>The handwritten fallback classifies an assumption as discharged
  whenever some line of the whole source proof discharges it.  That is too
  coarse after dead lines are removed: an assumption discharged on another
  branch may still be an open premise of the chosen conclusion.  The following
  pass uses the actual ancestors of each leaf instead.\<close>

fun hlClassifyAssumptions ::
    "int set \<Rightarrow> hl_derivation \<Rightarrow> hl_derivation" where
  "hlClassifyAssumptions bound (HL_Derivation phi rule) =
     HL_Derivation phi
       (case rule of
          HL_DAssume i \<Rightarrow>
            if i \<in> bound then HL_DAssume i else HL_DPremise i
        | HL_DPremise i \<Rightarrow>
            if i \<in> bound then HL_DAssume i else HL_DPremise i
        | HL_DMP d1 d2 \<Rightarrow>
            HL_DMP (hlClassifyAssumptions bound d1)
              (hlClassifyAssumptions bound d2)
        | HL_DMT d1 d2 \<Rightarrow>
            HL_DMT (hlClassifyAssumptions bound d1)
              (hlClassifyAssumptions bound d2)
        | HL_DDN d \<Rightarrow> HL_DDN (hlClassifyAssumptions bound d)
        | HL_DCP i p d \<Rightarrow>
            HL_DCP i p (hlClassifyAssumptions (insert i bound) d)
        | HL_DAndI d1 d2 \<Rightarrow>
            HL_DAndI (hlClassifyAssumptions bound d1)
              (hlClassifyAssumptions bound d2)
        | HL_DAndE d \<Rightarrow> HL_DAndE (hlClassifyAssumptions bound d)
        | HL_DOrI d \<Rightarrow> HL_DOrI (hlClassifyAssumptions bound d)
        | HL_DOrE d0 a1 p1 d1 a2 p2 d2 \<Rightarrow>
            HL_DOrE (hlClassifyAssumptions bound d0)
              a1 p1 (hlClassifyAssumptions (insert a1 bound) d1)
              a2 p2 (hlClassifyAssumptions (insert a2 bound) d2)
        | HL_DRAA i p d \<Rightarrow>
            HL_DRAA i p (hlClassifyAssumptions (insert i bound) d)
        | HL_DForallE d \<Rightarrow>
            HL_DForallE (hlClassifyAssumptions bound d)
        | HL_DForallI d \<Rightarrow>
            HL_DForallI (hlClassifyAssumptions bound d)
        | HL_DExistsI d \<Rightarrow>
            HL_DExistsI (hlClassifyAssumptions bound d)
        | HL_DExistsE d0 i p d \<Rightarrow>
            HL_DExistsE (hlClassifyAssumptions bound d0) i p
              (hlClassifyAssumptions (insert i bound) d)
        | HL_DEqI \<Rightarrow> HL_DEqI
        | HL_DEqE d1 d2 \<Rightarrow>
            HL_DEqE (hlClassifyAssumptions bound d1)
              (hlClassifyAssumptions bound d2)
        | HL_DLEM \<Rightarrow> HL_DLEM
        | HL_DPropTaut ds \<Rightarrow>
            HL_DPropTaut (map (hlClassifyAssumptions bound) ds)
        | HL_DIffI d1 d2 \<Rightarrow>
            HL_DIffI (hlClassifyAssumptions bound d1)
              (hlClassifyAssumptions bound d2)
        | HL_DIffE d1 d2 \<Rightarrow>
            HL_DIffE (hlClassifyAssumptions bound d1)
              (hlClassifyAssumptions bound d2)
        | HL_DQN d \<Rightarrow> HL_DQN (hlClassifyAssumptions bound d))"

definition hlToDerivation :: "hl_proof \<Rightarrow> hl_derivation option" where
  "hlToDerivation P =
     (if P = [] \<or> \<not> hlVerifiedCorrect P then None
      else map_option (hlClassifyAssumptions {})
        (hlUnfoldDerivation (Suc (length P)) P (hlLineNumber (last P))))"

section \<open>Renaming and freshness\<close>

fun hlRenameTerm :: "hl_name \<Rightarrow> hl_name \<Rightarrow> hl_term \<Rightarrow> hl_term" where
  "hlRenameTerm old new (HL_Var x) = HL_Var x"
| "hlRenameTerm old new (HL_Const a) =
     HL_Const (if a = old then new else a)"

fun hlRenameFormula ::
    "hl_name \<Rightarrow> hl_name \<Rightarrow> hl_formula \<Rightarrow> hl_formula" where
  "hlRenameFormula old new (HL_Predicate P ts) =
     HL_Predicate P (map (hlRenameTerm old new) ts)"
| "hlRenameFormula old new (HL_Boolean b) = HL_Boolean b"
| "hlRenameFormula old new (HL_Not p) =
     HL_Not (hlRenameFormula old new p)"
| "hlRenameFormula old new (HL_And p q) =
     HL_And (hlRenameFormula old new p) (hlRenameFormula old new q)"
| "hlRenameFormula old new (HL_Or p q) =
     HL_Or (hlRenameFormula old new p) (hlRenameFormula old new q)"
| "hlRenameFormula old new (HL_Implies p q) =
     HL_Implies (hlRenameFormula old new p) (hlRenameFormula old new q)"
| "hlRenameFormula old new (HL_Iff p q) =
     HL_Iff (hlRenameFormula old new p) (hlRenameFormula old new q)"
| "hlRenameFormula old new (HL_ForAll x p) =
     HL_ForAll x (hlRenameFormula old new p)"
| "hlRenameFormula old new (HL_Exists x p) =
     HL_Exists x (hlRenameFormula old new p)"

fun hlRenameDerivation ::
    "hl_name \<Rightarrow> hl_name \<Rightarrow> hl_derivation \<Rightarrow> hl_derivation" where
  "hlRenameDerivation old new (HL_Derivation phi r) =
     HL_Derivation (hlRenameFormula old new phi)
       (case r of
          HL_DAssume i \<Rightarrow> HL_DAssume i
        | HL_DPremise i \<Rightarrow> HL_DPremise i
        | HL_DMP d1 d2 \<Rightarrow>
            HL_DMP (hlRenameDerivation old new d1)
              (hlRenameDerivation old new d2)
        | HL_DMT d1 d2 \<Rightarrow>
            HL_DMT (hlRenameDerivation old new d1)
              (hlRenameDerivation old new d2)
        | HL_DDN d \<Rightarrow> HL_DDN (hlRenameDerivation old new d)
        | HL_DCP i p d \<Rightarrow>
            HL_DCP i (hlRenameFormula old new p)
              (hlRenameDerivation old new d)
        | HL_DAndI d1 d2 \<Rightarrow>
            HL_DAndI (hlRenameDerivation old new d1)
              (hlRenameDerivation old new d2)
        | HL_DAndE d \<Rightarrow> HL_DAndE (hlRenameDerivation old new d)
        | HL_DOrI d \<Rightarrow> HL_DOrI (hlRenameDerivation old new d)
        | HL_DOrE d0 a1 p1 d1 a2 p2 d2 \<Rightarrow>
            HL_DOrE (hlRenameDerivation old new d0)
              a1 (hlRenameFormula old new p1) (hlRenameDerivation old new d1)
              a2 (hlRenameFormula old new p2) (hlRenameDerivation old new d2)
        | HL_DRAA i p d \<Rightarrow>
            HL_DRAA i (hlRenameFormula old new p)
              (hlRenameDerivation old new d)
        | HL_DForallE d \<Rightarrow>
            HL_DForallE (hlRenameDerivation old new d)
        | HL_DForallI d \<Rightarrow>
            HL_DForallI (hlRenameDerivation old new d)
        | HL_DExistsI d \<Rightarrow>
            HL_DExistsI (hlRenameDerivation old new d)
        | HL_DExistsE d0 i p d \<Rightarrow>
            HL_DExistsE (hlRenameDerivation old new d0) i
              (hlRenameFormula old new p) (hlRenameDerivation old new d)
        | HL_DEqI \<Rightarrow> HL_DEqI
        | HL_DEqE d1 d2 \<Rightarrow>
            HL_DEqE (hlRenameDerivation old new d1)
              (hlRenameDerivation old new d2)
        | HL_DLEM \<Rightarrow> HL_DLEM
        | HL_DPropTaut ds \<Rightarrow>
            HL_DPropTaut (map (hlRenameDerivation old new) ds)
        | HL_DIffI d1 d2 \<Rightarrow>
            HL_DIffI (hlRenameDerivation old new d1)
              (hlRenameDerivation old new d2)
        | HL_DIffE d1 d2 \<Rightarrow>
            HL_DIffE (hlRenameDerivation old new d1)
              (hlRenameDerivation old new d2)
        | HL_DQN d \<Rightarrow> HL_DQN (hlRenameDerivation old new d))"

fun hlDerivationFormulas :: "hl_derivation \<Rightarrow> hl_formula list" where
  "hlDerivationFormulas (HL_Derivation phi r) =
     phi # (case r of
       HL_DAssume i \<Rightarrow> []
     | HL_DPremise i \<Rightarrow> []
     | HL_DMP d1 d2 \<Rightarrow> hlDerivationFormulas d1 @ hlDerivationFormulas d2
     | HL_DMT d1 d2 \<Rightarrow> hlDerivationFormulas d1 @ hlDerivationFormulas d2
     | HL_DDN d \<Rightarrow> hlDerivationFormulas d
     | HL_DCP i p d \<Rightarrow> p # hlDerivationFormulas d
     | HL_DAndI d1 d2 \<Rightarrow> hlDerivationFormulas d1 @ hlDerivationFormulas d2
     | HL_DAndE d \<Rightarrow> hlDerivationFormulas d
     | HL_DOrI d \<Rightarrow> hlDerivationFormulas d
     | HL_DOrE d0 a1 p1 d1 a2 p2 d2 \<Rightarrow>
         p1 # p2 # hlDerivationFormulas d0 @
           hlDerivationFormulas d1 @ hlDerivationFormulas d2
     | HL_DRAA i p d \<Rightarrow> p # hlDerivationFormulas d
     | HL_DForallE d \<Rightarrow> hlDerivationFormulas d
     | HL_DForallI d \<Rightarrow> hlDerivationFormulas d
     | HL_DExistsI d \<Rightarrow> hlDerivationFormulas d
     | HL_DExistsE d0 i p d \<Rightarrow>
         p # hlDerivationFormulas d0 @ hlDerivationFormulas d
     | HL_DEqI \<Rightarrow> []
     | HL_DEqE d1 d2 \<Rightarrow> hlDerivationFormulas d1 @ hlDerivationFormulas d2
     | HL_DLEM \<Rightarrow> []
     | HL_DPropTaut ds \<Rightarrow> concat (map hlDerivationFormulas ds)
     | HL_DIffI d1 d2 \<Rightarrow> hlDerivationFormulas d1 @ hlDerivationFormulas d2
     | HL_DIffE d1 d2 \<Rightarrow> hlDerivationFormulas d1 @ hlDerivationFormulas d2
     | HL_DQN d \<Rightarrow> hlDerivationFormulas d)"

definition hlDerivationConstants :: "hl_derivation \<Rightarrow> hl_name set" where
  "hlDerivationConstants d =
     \<Union> (hlConstantsInFormula ` set (hlDerivationFormulas d))"

definition hlFreshIndex :: "nat \<Rightarrow> nat \<Rightarrow> hl_name" where
  "hlFreshIndex base k = String.implode (replicate (base + k) CHR ''c'')"

fun hlRenamePairsFormula ::
    "(hl_name \<times> hl_name) list \<Rightarrow> hl_formula \<Rightarrow> hl_formula" where
  "hlRenamePairsFormula [] p = p"
| "hlRenamePairsFormula ((old,new) # pairs) p =
     hlRenamePairsFormula pairs (hlRenameFormula old new p)"

fun hlRepairDerivation ::
    "nat \<Rightarrow> nat \<Rightarrow> hl_name list \<Rightarrow> hl_derivation \<Rightarrow>
      nat \<times> (hl_name \<times> hl_name) list \<times> hl_derivation" where
  "hlRepairDerivation base count [] d = (count,[],d)"
| "hlRepairDerivation base count (old # olds) d =
     (let new = hlFreshIndex base count;
          d' = hlRenameDerivation old new d;
          (count',pairs,result) =
            hlRepairDerivation base (Suc count) olds d'
      in (count',(old,new) # pairs,result))"

definition hlConstantsInScope :: "hl_formula list \<Rightarrow> hl_name set" where
  "hlConstantsInScope scope =
     \<Union> (hlConstantsInFormula ` set scope)"

definition hlForallRepairConstants ::
    "hl_formula list \<Rightarrow> hl_formula \<Rightarrow> hl_derivation \<Rightarrow>
      hl_name list" where
  "hlForallRepairConstants scope goal d =
     sorted_list_of_set
       ((hlConstantsInFormula (hlDerivationFormula d) -
         hlConstantsInFormula goal) \<inter> hlConstantsInScope scope)"

definition hlExistsRepairConstants ::
    "hl_formula list \<Rightarrow> hl_formula \<Rightarrow> hl_derivation \<Rightarrow>
      hl_formula \<Rightarrow> hl_name list" where
  "hlExistsRepairConstants scope assumption source goal =
     sorted_list_of_set
       ((hlConstantsInFormula assumption -
         (hlConstantsInFormula (hlDerivationFormula source) \<union>
          hlConstantsInFormula goal)) \<inter> hlConstantsInScope scope)"

section \<open>Premises and layout environment\<close>

fun hlPremisesOf :: "hl_derivation \<Rightarrow> (int \<times> hl_formula) list" where
  "hlPremisesOf (HL_Derivation phi r) =
     (case r of
        HL_DPremise i \<Rightarrow> [(i,phi)]
      | HL_DAssume i \<Rightarrow> []
      | HL_DMP d1 d2 \<Rightarrow> hlPremisesOf d1 @ hlPremisesOf d2
      | HL_DMT d1 d2 \<Rightarrow> hlPremisesOf d1 @ hlPremisesOf d2
      | HL_DDN d \<Rightarrow> hlPremisesOf d
      | HL_DCP i p d \<Rightarrow> hlPremisesOf d
      | HL_DAndI d1 d2 \<Rightarrow> hlPremisesOf d1 @ hlPremisesOf d2
      | HL_DAndE d \<Rightarrow> hlPremisesOf d
      | HL_DOrI d \<Rightarrow> hlPremisesOf d
      | HL_DOrE d0 a1 p1 d1 a2 p2 d2 \<Rightarrow>
          hlPremisesOf d0 @ hlPremisesOf d1 @ hlPremisesOf d2
      | HL_DRAA i p d \<Rightarrow> hlPremisesOf d
      | HL_DForallE d \<Rightarrow> hlPremisesOf d
      | HL_DForallI d \<Rightarrow> hlPremisesOf d
      | HL_DExistsI d \<Rightarrow> hlPremisesOf d
      | HL_DExistsE d0 i p d \<Rightarrow> hlPremisesOf d0 @ hlPremisesOf d
      | HL_DEqI \<Rightarrow> []
      | HL_DEqE d1 d2 \<Rightarrow> hlPremisesOf d1 @ hlPremisesOf d2
      | HL_DLEM \<Rightarrow> []
      | HL_DPropTaut ds \<Rightarrow> concat (map hlPremisesOf ds)
      | HL_DIffI d1 d2 \<Rightarrow> hlPremisesOf d1 @ hlPremisesOf d2
      | HL_DIffE d1 d2 \<Rightarrow> hlPremisesOf d1 @ hlPremisesOf d2
      | HL_DQN d \<Rightarrow> hlPremisesOf d)"

type_synonym hl_layout_environment = "(int \<times> int \<times> hl_formula) list"

fun hlNumberPremises ::
    "int \<Rightarrow> (int \<times> hl_formula) list \<Rightarrow> hl_layout_environment" where
  "hlNumberPremises next [] = []"
| "hlNumberPremises next ((source,phi) # premises) =
     (source,next,phi) # hlNumberPremises (next + 1) premises"

definition hlPremiseEnvironment ::
    "hl_derivation \<Rightarrow> hl_layout_environment" where
  "hlPremiseEnvironment d =
     hlNumberPremises 1 (sort_key fst (remdups (hlPremisesOf d)))"

fun hlEnvironmentLine :: "hl_layout_environment \<Rightarrow> int \<Rightarrow> int" where
  "hlEnvironmentLine [] source = 0"
| "hlEnvironmentLine ((i,n,p) # env) source =
     (if i = source then n else hlEnvironmentLine env source)"

definition hlPremiseFitchLines ::
    "hl_layout_environment \<Rightarrow> hl_fitch_proof" where
  "hlPremiseFitchLines env =
     map (\<lambda>(source,n,phi). HL_FLine n phi HL_FPremise) env"

section \<open>Emitting a Fitch proof\<close>

type_synonym hl_emit_result =
  "hl_fitch_proof \<times> int \<times> int \<times> nat"

fun hlEmitDerivationsUsing ::
    "(int \<Rightarrow> nat \<Rightarrow> hl_derivation \<Rightarrow> hl_emit_result) \<Rightarrow>
      int \<Rightarrow> nat \<Rightarrow> hl_derivation list \<Rightarrow>
      hl_fitch_proof \<times> int list \<times> int \<times> nat" where
  "hlEmitDerivationsUsing emit next count [] = ([],[],next,count)"
| "hlEmitDerivationsUsing emit next count (d # ds) =
     (let (items,n,next1,count1) = emit next count d;
          (more,numbers,next2,count2) =
            hlEmitDerivationsUsing emit next1 count1 ds
      in (items @ more,n # numbers,next2,count2))"

fun hlEmitDerivationFuel ::
    "unit list \<Rightarrow> nat \<Rightarrow> hl_layout_environment \<Rightarrow> hl_formula list \<Rightarrow>
      int \<Rightarrow> nat \<Rightarrow> hl_derivation \<Rightarrow>
      hl_emit_result" where
  "hlEmitDerivationFuel [] base env scope next count d = ([],0,next,count)"
| "hlEmitDerivationFuel (_ # fuel) base env scope next count (HL_Derivation phi rule) =
     (case rule of
       HL_DAssume i \<Rightarrow> ([],hlEnvironmentLine env i,next,count)
     | HL_DPremise i \<Rightarrow> ([],hlEnvironmentLine env i,next,count)
     | HL_DMP d1 d2 \<Rightarrow>
       (let (items1,n1,next1,count1) = hlEmitDerivationFuel fuel base env scope next count d1;
          (items2,n2,next2,count2) = hlEmitDerivationFuel fuel base env scope next1 count1 d2
        in (items1 @ items2 @ [HL_FLine next2 phi (HL_FMP n1 n2)],
            next2,next2 + 1,count2))
     | HL_DMT d1 d2 \<Rightarrow>
       (let (items1,n1,next1,count1) = hlEmitDerivationFuel fuel base env scope next count d1;
          (items2,n2,next2,count2) = hlEmitDerivationFuel fuel base env scope next1 count1 d2
        in (items1 @ items2 @ [HL_FLine next2 phi (HL_FMT n1 n2)],
            next2,next2 + 1,count2))
     | HL_DDN d \<Rightarrow>
       (let (items,n,next',count') = hlEmitDerivationFuel fuel base env scope next count d
        in (items @ [HL_FLine next' phi (HL_FDN n)],next',next' + 1,count'))
     | HL_DCP a af body \<Rightarrow>
       (let assumptionLine = next;
          (bodyItems,bodyLine,next1,count1) =
            hlEmitDerivationFuel fuel base ((a,assumptionLine,af) # env) (af # scope)
              (next + 1) count body;
          needsReiteration = bodyItems = [] \<and> bodyLine \<noteq> assumptionLine;
          closedBody = (if needsReiteration
            then [HL_FLine next1 (hlDerivationFormula body) (HL_FReit bodyLine)]
            else bodyItems);
          lastLine = (if needsReiteration then next1 else bodyLine);
          afterBox = (if needsReiteration then next1 + 1 else next1)
        in ([HL_FSub (HL_Subproof assumptionLine af closedBody),
             HL_FLine afterBox phi (HL_FCP (assumptionLine,lastLine))],
            afterBox,afterBox + 1,count1))
     | HL_DAndI d1 d2 \<Rightarrow>
       (let (items1,n1,next1,count1) = hlEmitDerivationFuel fuel base env scope next count d1;
          (items2,n2,next2,count2) = hlEmitDerivationFuel fuel base env scope next1 count1 d2
        in (items1 @ items2 @ [HL_FLine next2 phi (HL_FAndI n1 n2)],
            next2,next2 + 1,count2))
     | HL_DAndE d \<Rightarrow>
       (let (items,n,next',count') = hlEmitDerivationFuel fuel base env scope next count d
        in (items @ [HL_FLine next' phi (HL_FAndE n)],next',next' + 1,count'))
     | HL_DOrI d \<Rightarrow>
       (let (items,n,next',count') = hlEmitDerivationFuel fuel base env scope next count d
        in (items @ [HL_FLine next' phi (HL_FOrI n)],next',next' + 1,count'))
     | HL_DOrE d0 a1 f1 b1 a2 f2 b2 \<Rightarrow>
       (let (items0,n0,next0,count0) = hlEmitDerivationFuel fuel base env scope next count d0;
          assumption1 = next0;
          (body1,line1,next1,count1) =
            hlEmitDerivationFuel fuel base ((a1,assumption1,f1) # env) (f1 # scope)
              (next0 + 1) count0 b1;
          reiterate1 = body1 = [] \<and> line1 \<noteq> assumption1;
          closed1 = (if reiterate1
            then [HL_FLine next1 (hlDerivationFormula b1) (HL_FReit line1)] else body1);
          last1 = (if reiterate1 then next1 else line1);
          after1 = (if reiterate1 then next1 + 1 else next1);
          assumption2 = after1;
          (body2,line2,next2,count2) =
            hlEmitDerivationFuel fuel base ((a2,assumption2,f2) # env) (f2 # scope)
              (after1 + 1) count1 b2;
          reiterate2 = body2 = [] \<and> line2 \<noteq> assumption2;
          closed2 = (if reiterate2
            then [HL_FLine next2 (hlDerivationFormula b2) (HL_FReit line2)] else body2);
          last2 = (if reiterate2 then next2 else line2);
          after2 = (if reiterate2 then next2 + 1 else next2)
        in (items0 @ [HL_FSub (HL_Subproof assumption1 f1 closed1),
            HL_FSub (HL_Subproof assumption2 f2 closed2),
            HL_FLine after2 phi (HL_FOrE n0 (assumption1,last1) (assumption2,last2))],
            after2,after2 + 1,count2))
     | HL_DRAA a af body \<Rightarrow>
       (let assumptionLine = next;
          (bodyItems,bodyLine,next1,count1) =
            hlEmitDerivationFuel fuel base ((a,assumptionLine,af) # env) (af # scope)
              (next + 1) count body;
          needsReiteration = bodyItems = [] \<and> bodyLine \<noteq> assumptionLine;
          closedBody = (if needsReiteration
            then [HL_FLine next1 (hlDerivationFormula body) (HL_FReit bodyLine)]
            else bodyItems);
          lastLine = (if needsReiteration then next1 else bodyLine);
          afterBox = (if needsReiteration then next1 + 1 else next1)
        in ([HL_FSub (HL_Subproof assumptionLine af closedBody),
             HL_FLine afterBox phi (HL_FRAA (assumptionLine,lastLine))],
            afterBox,afterBox + 1,count1))
     | HL_DForallE d \<Rightarrow>
       (let (items,n,next',count') = hlEmitDerivationFuel fuel base env scope next count d
        in (items @ [HL_FLine next' phi (HL_FForallE n)],next',next' + 1,count'))
     | HL_DForallI d \<Rightarrow>
       (let bad = hlForallRepairConstants scope phi d;
          (count0,pairs,repaired) = hlRepairDerivation base count bad d;
          (items,n,next',count') =
            hlEmitDerivationFuel fuel base env scope next count0 repaired
        in (items @ [HL_FLine next' phi (HL_FForallI n)],next',next' + 1,count'))
     | HL_DExistsI d \<Rightarrow>
       (let (items,n,next',count') = hlEmitDerivationFuel fuel base env scope next count d
        in (items @ [HL_FLine next' phi (HL_FExistsI n)],next',next' + 1,count'))
     | HL_DExistsE source a af body \<Rightarrow>
       (let (sourceItems,sourceLine,next0,count0) =
            hlEmitDerivationFuel fuel base env scope next count source;
          bad = hlExistsRepairConstants scope af source phi;
          (countR,pairs,repairedBody) = hlRepairDerivation base count0 bad body;
          repairedAssumption = hlRenamePairsFormula pairs af;
          assumptionLine = next0;
          (bodyItems,bodyLine,next1,count1) =
            hlEmitDerivationFuel fuel base ((a,assumptionLine,repairedAssumption) # env)
              (repairedAssumption # scope) (next0 + 1) countR repairedBody;
          needsReiteration = bodyItems = [] \<and> bodyLine \<noteq> assumptionLine;
          closedBody = (if needsReiteration
            then [HL_FLine next1 (hlDerivationFormula repairedBody) (HL_FReit bodyLine)]
            else bodyItems);
          lastLine = (if needsReiteration then next1 else bodyLine);
          afterBox = (if needsReiteration then next1 + 1 else next1)
        in (sourceItems @ [HL_FSub (HL_Subproof assumptionLine repairedAssumption closedBody),
             HL_FLine afterBox phi (HL_FExistsE sourceLine (assumptionLine,lastLine))],
            afterBox,afterBox + 1,count1))
     | HL_DEqI \<Rightarrow> ([HL_FLine next phi HL_FEqI],next,next + 1,count)
     | HL_DEqE d1 d2 \<Rightarrow>
       (let (items1,n1,next1,count1) = hlEmitDerivationFuel fuel base env scope next count d1;
          (items2,n2,next2,count2) = hlEmitDerivationFuel fuel base env scope next1 count1 d2
        in (items1 @ items2 @ [HL_FLine next2 phi (HL_FEqE n1 n2)],
            next2,next2 + 1,count2))
     | HL_DLEM \<Rightarrow> ([HL_FLine next phi HL_FLEM],next,next + 1,count)
     | HL_DPropTaut ds \<Rightarrow>
       (let (items,numbers,next',count') =
            hlEmitDerivationsUsing
              (\<lambda>next count d.
                hlEmitDerivationFuel fuel base env scope next count d)
              next count ds
        in (items @ [HL_FLine next' phi (HL_FPropTaut numbers)],
            next',next' + 1,count'))
     | HL_DIffI d1 d2 \<Rightarrow>
       (let (items1,n1,next1,count1) = hlEmitDerivationFuel fuel base env scope next count d1;
          (items2,n2,next2,count2) = hlEmitDerivationFuel fuel base env scope next1 count1 d2
        in (items1 @ items2 @ [HL_FLine next2 phi (HL_FIffI n1 n2)],
            next2,next2 + 1,count2))
     | HL_DIffE d1 d2 \<Rightarrow>
       (let (items1,n1,next1,count1) = hlEmitDerivationFuel fuel base env scope next count d1;
          (items2,n2,next2,count2) = hlEmitDerivationFuel fuel base env scope next1 count1 d2
        in (items1 @ items2 @ [HL_FLine next2 phi (HL_FIffE n1 n2)],
            next2,next2 + 1,count2))
     | HL_DQN d \<Rightarrow>
       (let (items,n,next',count') = hlEmitDerivationFuel fuel base env scope next count d
        in (items @ [HL_FLine next' phi (HL_FQN n)],next',next' + 1,count')))"

definition hlEmitDerivation ::
    "nat \<Rightarrow> hl_layout_environment \<Rightarrow> hl_formula list \<Rightarrow>
      int \<Rightarrow> nat \<Rightarrow> hl_derivation \<Rightarrow>
      hl_fitch_proof \<times> int \<times> int \<times> nat" where
  "hlEmitDerivation base env scope next count d =
     hlEmitDerivationFuel (replicate (Suc (size d)) ())
       base env scope next count d"

definition hlEmitDerivations ::
    "nat \<Rightarrow> hl_layout_environment \<Rightarrow> hl_formula list \<Rightarrow>
      int \<Rightarrow> nat \<Rightarrow> hl_derivation list \<Rightarrow>
      hl_fitch_proof \<times> int list \<times> int \<times> nat" where
  "hlEmitDerivations base env scope next count ds =
     hlEmitDerivationsUsing
       (\<lambda>next count d. hlEmitDerivation base env scope next count d)
       next count ds"

definition hlDerivationToFitch :: "hl_derivation \<Rightarrow> hl_fitch_proof" where
  "hlDerivationToFitch d =
     (let env = hlPremiseEnvironment d;
          premiseLines = hlPremiseFitchLines env;
          base = Suc (maxlen (sorted_list_of_set
            (\<Union> (hlConstantsInFormula ` set (hlDerivationFormulas d)))));
          (body,conclusion,next,count) =
            hlEmitDerivation base env [] (1 + int (length env)) 0 d
      in premiseLines @ body)"

section \<open>The complete exact translation\<close>

datatype hl_route = HL_DirectRoute | HL_ViaTreeRoute

definition hlViaTree ::
    "hl_proof \<Rightarrow> hl_translation_error + (hl_route \<times> hl_fitch_proof)" where
  "hlViaTree P =
     (case hlToDerivation P of
        None \<Rightarrow> Inl (HL_SourceNotVerified 0)
      | Some d \<Rightarrow> Inr (HL_ViaTreeRoute,hlDerivationToFitch d))"

definition hlLemmonToFitch ::
    "hl_proof \<Rightarrow> hl_translation_error + (hl_route \<times> hl_fitch_proof)" where
  "hlLemmonToFitch P =
     (case hlLemmonToFitchDirect P of
        Inr F \<Rightarrow> Inr (HL_DirectRoute,F)
      | Inl e \<Rightarrow> hlViaTree P)"

definition hlLemmonToFitchChecked ::
    "hl_proof \<Rightarrow> hl_translation_error + (hl_route \<times> hl_fitch_proof)" where
  "hlLemmonToFitchChecked P =
     (case hlLemmonToFitchDirect P of
        Inr F \<Rightarrow>
          if hlFitchVerified F then Inr (HL_DirectRoute,F) else hlViaTree P
      | Inl e \<Rightarrow> hlViaTree P)"

lemma hl_exact_tree_cp_example:
  "case hlViaTree hl_cp_example of
     Inl e \<Rightarrow> False
   | Inr (route,F) \<Rightarrow>
       route = HL_ViaTreeRoute \<and> hlFitchVerified F \<and>
       hlConclusion (\<delta>\<^sub>H F) = hlConclusion hl_cp_example"
  by eval

lemma hl_exact_complete_cp_example:
  "case hlLemmonToFitchChecked hl_cp_example of
     Inl e \<Rightarrow> False
   | Inr (route,F) \<Rightarrow> hlFitchVerified F"
  by eval

definition hl_shared_discharge_example :: hl_proof where
  "hl_shared_discharge_example =
    [ HL_ProofLine 1 hlP HL_Assumption {1},
      HL_ProofLine 2 hlQ HL_Assumption {2},
      HL_ProofLine 3 (hlP \<and>\<^sub>H hlQ) (HL_AndIntro 1 2) {1,2},
      HL_ProofLine 4 (hlP \<longrightarrow>\<^sub>H (hlP \<and>\<^sub>H hlQ)) (HL_CP 1 3) {2},
      HL_ProofLine 5 (hlQ \<longrightarrow>\<^sub>H (hlP \<and>\<^sub>H hlQ)) (HL_CP 2 3) {1} ]"

lemma hl_exact_complete_uses_tree:
  "case hlLemmonToFitchChecked hl_shared_discharge_example of
     Inl e \<Rightarrow> False
   | Inr (route,F) \<Rightarrow>
       route = HL_ViaTreeRoute \<and> hlFitchVerified F \<and>
       hlConclusion (\<delta>\<^sub>H F) = hlConclusion hl_shared_discharge_example"
  by eval

end
