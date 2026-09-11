theory LF_HLW_Premise_Layout
  imports LF_HLW_Conclusion
begin

definition hlNoPremiseLines :: "hl_fitch_proof \<Rightarrow> bool" where
  "hlNoPremiseLines F \<longleftrightarrow>
   list_all (\<lambda>(n,p,r). r \<noteq> HL_FPremise) (hlFlattenFitch F)"

lemma hlNoPremiseLines_simps [simp]:
  "hlNoPremiseLines []"
  "hlNoPremiseLines (F @ G) = (hlNoPremiseLines F \<and> hlNoPremiseLines G)"
  "hlNoPremiseLines (HL_FLine n p r # F) = (r \<noteq> HL_FPremise \<and> hlNoPremiseLines F)"
  "hlNoPremiseLines (HL_FSub (HL_Subproof a p body) # F) =
    (hlNoPremiseLines body \<and> hlNoPremiseLines F)"
  by (simp_all add: hlNoPremiseLines_def hlFlattenFitch_append)

lemma hlNoPremiseLines_emit_list:
  assumes emitted: "hlEmitDerivationsUsing emit first count ds = (items,ns,after,count')"
    and each: "\<And>d first count items n after count'. d \<in> set ds \<Longrightarrow>
      emit first count d = (items,n,after,count') \<Longrightarrow> hlNoPremiseLines items"
  shows "hlNoPremiseLines items"
  using emitted each
proof (induction ds arbitrary: first count items ns after count')
  case Nil
  then show ?case by simp
next
  case (Cons d ds)
  from Cons.prems(1) obtain front n middle count1 rest ks where
    front: "emit first count d = (front,n,middle,count1)"
    and rest: "hlEmitDerivationsUsing emit middle count1 ds = (rest,ks,after,count')"
    and items: "items = front @ rest"
    by (auto simp: Let_def split: prod.splits)
  have front_ok: "hlNoPremiseLines front"
    by (rule Cons.prems(2)[OF _ front]) simp
  have rest_ok: "hlNoPremiseLines rest"
    by (rule Cons.IH[OF rest]) (auto intro: Cons.prems(2))
  from front_ok rest_ok show ?case by (simp add: items)
qed

lemma hlEmitDerivationFuel_no_premises:
  "hlEmitDerivationFuel fuel base env scope first count d = (items,n,after,count') \<Longrightarrow>
   hlNoPremiseLines items"
proof (induction fuel arbitrary: env scope first count d items n after count')
  case Nil
  then show ?case by simp
next
  case (Cons u fuel)
  have list_no_premises: "\<And>ds first count items ns after count'.
    hlEmitDerivationsUsing (\<lambda>first count d. hlEmitDerivationFuel fuel base env scope first count d)
      first count ds = (items,ns,after,count') \<Longrightarrow> hlNoPremiseLines items"
    by (rule hlNoPremiseLines_emit_list) (auto intro: Cons.IH)
  obtain phi rule where d: "d = HL_Derivation phi rule" by (cases d) auto
  from Cons.prems show ?case
    by (cases rule)
       (auto simp: d Let_def split: prod.splits if_splits
         dest!: Cons.IH list_no_premises)
qed

lemma hlEmitDerivation_no_premises:
  "hlEmitDerivation base env scope first count d = (items,n,after,count') \<Longrightarrow>
   hlNoPremiseLines items"
  unfolding hlEmitDerivation_def by (rule hlEmitDerivationFuel_no_premises)

lemma hlNoPremiseLines_root_premises:
  "hlNoPremiseLines F \<Longrightarrow> hlFitchPremises F = []"
  apply (induction F)
  apply (auto, rename_tac a F, case_tac a, auto)
  apply (metis hlNoPremiseLines_simps(4) hl_subproof.exhaust)
  done

lemma hlNumberPremises_length [simp]:
  "length (hlNumberPremises first G) = length G"
  by (induction G arbitrary: first) (auto split: prod.splits)

lemma hlNumberPremises_formulas:
  "map (\<lambda>(source,n,p). p) (hlNumberPremises first G) = map snd G"
  by (induction G arbitrary: first) (auto split: prod.splits)

lemma hlPremiseFitchLines_premises:
  "hlFitchPremises (hlPremiseFitchLines env) = map (\<lambda>(source,n,p). p) env"
  by (induction env) (auto simp: hlPremiseFitchLines_def split: prod.splits)

lemma hlPremiseEnvironment_formulas:
  "set (map (\<lambda>(source,n,p). p) (hlPremiseEnvironment d)) = snd ` set (hlPremisesOf d)"
  by (simp add: hlPremiseEnvironment_def hlNumberPremises_formulas)

lemma hlDerivationToFitch_premises:
  "set (hlFitchPremises (hlDerivationToFitch d)) = snd ` set (hlPremisesOf d)"
  using hlPremiseEnvironment_formulas[of d]
  unfolding hlDerivationToFitch_def
  by (auto simp: Let_def hlPremiseFitchLines_premises hlPremiseEnvironment_formulas
      split: prod.splits dest!: hlEmitDerivation_no_premises hlNoPremiseLines_root_premises)

lemma hlPremiseFitchLines_allocated:
  "hlAllocated first (hlPremiseFitchLines (hlNumberPremises first G))
    (first + int (length G))"
proof (induction G arbitrary: first)
  case Nil
  then show ?case by (simp add: hlPremiseFitchLines_def)
next
  case (Cons nf G)
  obtain n p where nf: "nf = (n,p)" by (cases nf) auto
  from hlAllocated_append[OF hlAllocated_line Cons.IH[of "first + 1"]]
  show ?case by (simp add: nf hlPremiseFitchLines_def add.assoc)
qed


lemma hlNoPremiseLines_premises_first:
  "hlNoPremiseLines F \<Longrightarrow> hlFitchPremisesFirst F"
  by (auto simp: hlNoPremiseLines_def hlFitchPremisesFirst_def list_all_iff
      dest: set_dropWhileD)

lemma hlPremiseFitchLines_premises_first:
  "hlNoPremiseLines F \<Longrightarrow> hlFitchPremisesFirst (hlPremiseFitchLines env @ F)"
  by (induction env)
     (auto simp: hlPremiseFitchLines_def hlFitchPremisesFirst_def
       hlNoPremiseLines_def list_all_iff split: prod.splits dest: set_dropWhileD)

lemma hlDerivationToFitch_premises_first:
  "hlFitchPremisesFirst (hlDerivationToFitch d)"
  unfolding hlDerivationToFitch_def
  by (auto simp: Let_def split: prod.splits
      dest!: hlEmitDerivation_no_premises intro: hlPremiseFitchLines_premises_first)

lemma hlPremiseEnvironment_allocated:
  "hlAllocated 1 (hlPremiseFitchLines (hlPremiseEnvironment d))
    (1 + int (length (hlPremiseEnvironment d)))"
  using hlPremiseFitchLines_allocated[of 1 "sort_key fst (remdups (hlPremisesOf d))"]
  by (simp add: hlPremiseEnvironment_def)

lemma hlDerivationToFitch_allocated:
  "\<exists>after. hlAllocated 1 (hlDerivationToFitch d) after"
  unfolding hlDerivationToFitch_def
  apply (auto simp: Let_def split: prod.splits)
  apply (meson hlAllocated_append hlPremiseEnvironment_allocated hlEmitDerivation_allocated)
  done

lemma hlDerivationToFitch_positive_sorted:
  "list_all (\<lambda>n. 0 < n) (hlFitchLineNumbers (hlDerivationToFitch d)) \<and>
   sorted_wrt (<) (hlFitchLineNumbers (hlDerivationToFitch d))"
  using hlDerivationToFitch_allocated[of d]
  by (auto simp: hlAllocated_def list_all_iff)

lemma hlPremiseFitchLines_concludesAtTop:
  "hlConcludesAtTop (hlPremiseFitchLines env)"
  by (induction env rule: rev_induct)
     (auto simp: hlConcludesAtTop_def hlPremiseFitchLines_def split: prod.splits)

lemma hlConcludesAtTop_append:
  "hlConcludesAtTop F \<Longrightarrow> hlConcludesAtTop G \<Longrightarrow> hlConcludesAtTop (F @ G)"
  by (auto simp: hlConcludesAtTop_def last_append)

lemma hlDerivationToFitch_concludesAtTop:
  "hlConcludesAtTop (hlDerivationToFitch d)"
  unfolding hlDerivationToFitch_def
  apply (auto simp: Let_def split: prod.splits)
  apply (rule hlConcludesAtTop_append[OF hlPremiseFitchLines_concludesAtTop])
  apply (metis fst_conv hlEmitDerivation_concludesAtTop)
  done

end
