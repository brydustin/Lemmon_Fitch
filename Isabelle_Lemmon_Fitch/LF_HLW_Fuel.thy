theory LF_HLW_Fuel
  imports LF_HLW_Layout LF_HLW_Derivation
begin

lemma hlEmitDerivationsUsing_cong:
  assumes "\<And>d first count. d \<in> set ds \<Longrightarrow> emit first count d = emit' first count d"
  shows "hlEmitDerivationsUsing emit first count ds = hlEmitDerivationsUsing emit' first count ds"
  using assms
  by (induction ds arbitrary: first count) (auto simp: Let_def)

lemma hlEmitDerivationFuel_stable:
  assumes "size d < length fuel" "size d < length fuel2"
  shows "hlEmitDerivationFuel fuel base env scope first count d =
    hlEmitDerivationFuel fuel2 base env scope first count d"
  using assms
proof (induction d arbitrary: fuel fuel2 env scope first count rule: measure_induct_rule[where f=size])
  case (less d)
  from less.prems obtain u fs where fuel: "fuel = u # fs" by (cases fuel) auto
  from less.prems obtain v gs where fuel2: "fuel2 = v # gs" by (cases fuel2) auto
  have child: "\<And>e env scope first count. size e < size d \<Longrightarrow>
    hlEmitDerivationFuel fs base env scope first count e =
    hlEmitDerivationFuel gs base env scope first count e"
  proof -
    fix e :: hl_derivation
    fix env scope first count
    assume smaller: "size e < size d"
    show "hlEmitDerivationFuel fs base env scope first count e =
      hlEmitDerivationFuel gs base env scope first count e"
      by (rule less.IH[OF smaller]) (use less.prems smaller fuel fuel2 in auto)
  qed
  obtain phi rule where d: "d = HL_Derivation phi rule" by (cases d) auto
  have lists: "\<And>ds first count. rule = HL_DPropTaut ds \<Longrightarrow>
    hlEmitDerivationsUsing (hlEmitDerivationFuel fs base env scope) first count ds =
    hlEmitDerivationsUsing (hlEmitDerivationFuel gs base env scope) first count ds"
  proof -
    fix ds first count
    assume r: "rule = HL_DPropTaut ds"
    show "hlEmitDerivationsUsing (hlEmitDerivationFuel fs base env scope) first count ds =
      hlEmitDerivationsUsing (hlEmitDerivationFuel gs base env scope) first count ds"
    proof (rule hlEmitDerivationsUsing_cong)
      fix e first count
      assume member: "e \<in> set ds"
      have smaller: "size e < size rule"
        by (rule hlSubDerivations_size) (simp add: r member)
      show "hlEmitDerivationFuel fs base env scope first count e =
        hlEmitDerivationFuel gs base env scope first count e"
        by (rule child) (use smaller d in simp)
    qed
  qed
  show ?case
    apply (cases rule)
    apply (auto simp: d fuel fuel2 Let_def child lists
        split: prod.splits if_splits
        dest: hlRepairDerivation_size
        intro!: hlEmitDerivationsUsing_cong)
    done
qed

theorem hlEmitDerivationFuel_sufficient:
  "size d < length fuel \<Longrightarrow>
   hlEmitDerivationFuel fuel base env scope first count d =
   hlEmitDerivation base env scope first count d"
  unfolding hlEmitDerivation_def
  by (rule hlEmitDerivationFuel_stable) simp_all

end
