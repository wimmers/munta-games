theory Safety_Certification_Pure
  imports
    Safety_Certification
    \<comment> \<open>We generalize the material from this theory to federation subsumption:\<close>
    Certification.Unreachability_Certification2 \<comment> \<open>XXX: These should be merged.\<close>
begin

locale Reachability_Impl_pure_base =
  Reachability_Impl_base where less_eq = less_eq
  for less_eq :: "'a \<Rightarrow> 'a set \<Rightarrow> bool" (infix "\<preceq>" 50) +
  fixes get_succs and K and A and L and Li and lei
    and Li_split :: "'ki list list"
  assumes K_right_unique: "single_valued K"
  assumes K_left_unique:  "single_valued (K\<inverse>)"
  assumes Li_L: "(Li, L) \<in> \<langle>K\<rangle>list_set_rel"
  assumes lei_less_eq: "(lei, less_eq) \<in> A \<rightarrow> \<langle>A\<rangle>list_set_rel \<rightarrow> bool_rel"
  assumes get_succs_succs[param]:
    "(get_succs, succs) \<in> K \<rightarrow> \<langle>A\<rangle>list_set_rel \<rightarrow> \<langle>K \<times>\<^sub>r \<langle>A\<rangle>list_set_rel\<rangle>list_rel"
  assumes full_split: "set Li = (\<Union>xs \<in> set Li_split. set xs)"
begin

lemma lei_refine[refine_mono]:
  \<open>RETURN (lei a b) \<le> RETURN (a' \<preceq> b')\<close> if \<open>(a, a') \<in> A\<close> \<open>(b, b') \<in> \<langle>A\<rangle>list_set_rel\<close>
  using that using lei_less_eq by simp (metis pair_in_Id_conv tagged_fun_relD_both)

definition list_all_split :: "_ \<Rightarrow> 'ki list \<Rightarrow> bool" where [simp]:
  "list_all_split = list_all"

definition monadic_list_all_split :: "_ \<Rightarrow> 'ki list \<Rightarrow> bool nres" where [simp]:
  "monadic_list_all_split = monadic_list_all"

lemmas pure_unfolds =
  monadic_list_all_RETURN[where 'a = 'ki, folded monadic_list_all_split_def list_all_split_def]
  monadic_list_ex_RETURN monadic_list_all_RETURN monadic_list_ex_RETURN
  nres_monad1 option.case_distrib[where h = RETURN, symmetric]
  if_distrib[where f = RETURN, symmetric] prod.case_distrib[where h = RETURN, symmetric]

lemma list_all_split:
  "list_all_split Q Li = list_all id (Parallel.map (list_all Q) Li_split)"
  unfolding list_all_split_def list_all_split[OF full_split, symmetric] Parallel.map_def ..

end


locale Reachability_Impl_pure_invariant =
  Certification_Impl_invariant where M = M +
  Reachability_Impl_pure_base where Li_split = Li_split
  for M :: "'k \<Rightarrow> 'a set" and Li_split :: "'ki list list"

locale Reachability_Impl_pure_base2 =
  Reachability_Impl_pure_base where less_eq = less_eq and Li_split = Li_split
  for less_eq :: "'a \<Rightarrow> 'a set \<Rightarrow> bool" (infix "\<preceq>" 50) and Li_split :: "'ki list list" +
  fixes Pi and Fi
  assumes Pi_P'[refine,param]: "(Pi, P') \<in> K \<times>\<^sub>r A \<rightarrow> bool_rel"
  assumes Fi_F[refine]: "(Fi, F) \<in> K \<times>\<^sub>r A \<rightarrow> bool_rel"

locale Reachability_Impl_pure =
  Certification_Impl_common where M = M +
  Reachability_Impl_pure_base2 +
  Reachability_Impl_correct where M = "\<lambda>x. case M x of None \<Rightarrow> {} | Some S \<Rightarrow> S"
  for M :: "'k \<Rightarrow> 'a set option" +
  fixes Mi l\<^sub>0i s\<^sub>0i
  assumes Mi_M[param]: "(Mi, M) \<in> K \<rightarrow> \<langle>\<langle>A\<rangle>list_set_rel\<rangle>option_rel"
  assumes l\<^sub>0i_l\<^sub>0[refine,param]: "(l\<^sub>0i, l\<^sub>0) \<in> K"
      and s\<^sub>0i_s\<^sub>0[refine,param,refine_mono]: "(s\<^sub>0i, s\<^sub>0) \<in> A"
  fixes nonempty :: "'a \<Rightarrow> bool"
  assumes empty_not_subsumed [simp]:
    "nonempty x \<Longrightarrow> x \<preceq> {} \<longleftrightarrow> False"
  assumes succs_nonempty:
    "(l', S') \<in> set (succs l S) \<Longrightarrow> x \<in> S' \<Longrightarrow> nonempty x"
  assumes P'_nonempty:
    "P' (l, s) \<Longrightarrow> nonempty s"
begin

paragraph \<open>Refinement\<close>

definition "check_invariant1 L' \<equiv>
do {
  monadic_list_all_split (\<lambda>l.
    case Mi l of
      None \<Rightarrow> RETURN True
    | Some as \<Rightarrow> do {
        let succs = get_succs l as;
        monadic_list_all (\<lambda>(l', xs).
        do {
          if xs = [] then RETURN True
          else do {
            case Mi l' of
              None \<Rightarrow> RETURN False
            | Some ys \<Rightarrow> monadic_list_all (\<lambda>x.
              RETURN (lei x ys)
            ) xs
          }
        }
        ) succs
      }
  ) L'
}
"

lemma Mi_M_None_iff[simp]:
  "M l = None \<longleftrightarrow> Mi li = None" if "(li, l) \<in> K"
proof -
  from that have "(Mi li, M l) \<in> \<langle>\<langle>A\<rangle>list_set_rel\<rangle>option_rel"
    by parametricity
  then show ?thesis
    by auto
qed

definition A' where "A' = {(c, a). (c, a) \<in> A \<and> nonempty a}"

lemma A'_le_A [relator_props]:
  "A' \<le> A"
  unfolding A'_def by auto

lemma get_succs_succs'[param]:
  "(get_succs, succs) \<in> K \<rightarrow> \<langle>A\<rangle>list_set_rel \<rightarrow> \<langle>K \<times>\<^sub>r \<langle>A'\<rangle>list_set_rel\<rangle>list_rel"
  using succs_nonempty get_succs_succs unfolding A'_def
  by (auto dest!: fun_relD)
     (auto elim!: list.rel_mono_strong intro!: relcomp.relcompI
       simp: refine_rel_defs list_set_rel_def)

lemma empty_not_subsumed' [simp]:
  "(cs, as) \<in> \<langle>A'\<rangle>list_rel \<Longrightarrow> x \<in> set as \<Longrightarrow> x \<preceq> {} \<longleftrightarrow> False"
  unfolding A'_def by (auto elim: list_rel_setE2)

lemma check_invariant1_refine[refine]:
  "check_invariant1 L1 \<le> check_invariant L'" if "(L1, L') \<in> \<langle>K\<rangle>list_rel" "L = dom M"
  unfolding check_invariant1_def check_invariant_def Let_def monadic_list_all_split_def
  apply (refine_rcg monadic_list_all_mono' refine_IdI that)
  apply (clarsimp split: option.splits simp: succs_empty; safe)
   apply (simp flip: Mi_M_None_iff; fail)
  apply (refine_rcg monadic_list_all_mono')
   apply parametricity
  subgoal
    using Mi_M by (auto dest!: fun_relD1)
  apply (clarsimp split: option.splits; safe)
  apply (
    elim list_set_relE specify_right;
    auto simp: monadic_list_all_False intro!: res_right simp flip: Mi_M_None_iff; fail)
  apply (
    elim list_set_relE specify_right;
    auto simp: monadic_list_all_RETURN list_all_iff intro!: res_right simp flip: Mi_M_None_iff;
    fail)+
  subgoal premises prems for _ _ _ _ li _ l _ S xsi
  proof -
    have rel_mono: "\<langle>A'\<rangle>list_rel \<le> \<langle>A\<rangle>list_rel"
      by (intro relator_props)
    have *: \<open>li \<in> set Li \<longleftrightarrow> l \<in> L\<close> if \<open>(li, l) \<in> K\<close>
      using that using Li_L K_left_unique K_right_unique
      by (auto dest: single_valuedD elim: list_rel_setE1 list_rel_setE2 elim!: list_set_relE)
    have [simp]: "l \<in> L"
      using prems(6) that(2) by blast
    from prems have "(Mi li, M l) \<in> \<langle>\<langle>A\<rangle>list_set_rel\<rangle>option_rel"
      by parametricity
    with prems have "(xsi, S) \<in> \<langle>A\<rangle>list_set_rel"
      by auto
    with prems show ?thesis
      apply (elim list_set_relE, elim specify_right)
      apply (clarsimp, safe)
       apply (auto; fail)
      supply [refine_mono] = monadic_list_all_mono' monadic_list_ex_mono'
      apply refine_mono
      using rel_mono by fast
  qed
  done

definition check_prop1 where
  "check_prop1 L' M' = do {
  l \<leftarrow> RETURN L';
  monadic_list_all (\<lambda>l. do {
    let S = op_map_lookup l M';
    case S of None \<Rightarrow> RETURN True | Some S \<Rightarrow> do {
      xs \<leftarrow> RETURN S;
      r \<leftarrow> monadic_list_all (\<lambda>s.
        RETURN (Pi (l, s))
      ) xs;
      RETURN r
    }
    }
  ) l
  }"

lemma check_prop1_refine:
  "(check_prop1, check_prop') \<in> \<langle>K\<rangle>list_set_rel \<rightarrow> (K \<rightarrow> \<langle>\<langle>A\<rangle>list_set_rel\<rangle>option_rel) \<rightarrow> \<langle>Id\<rangle>nres_rel"
  supply [refine] =
    list_of_set_impl[THEN fun_relD, THEN nres_relD] monadic_list_all_mono' case_option_mono'
  supply [refine_mono] =
    monadic_list_all_mono' list_of_set_impl[THEN fun_relD, THEN nres_relD]
  unfolding check_prop1_def check_prop'_def list_of_set_def[symmetric] Let_def op_map_lookup_def
  apply refine_rcg
   apply assumption
  apply (refine_rcg refine_IdI, assumption)
   apply parametricity
  apply (rule bind_mono)
   apply refine_mono+
  using Pi_P'
  apply (auto simp add: prod_rel_def dest!: fun_relD)
  done

lemma [refine]:
  "(Mi l\<^sub>0i \<noteq> None, l\<^sub>0 \<in> L) \<in> bool_rel" if "L = dom M"
  using that by (auto simp: Mi_M_None_iff[symmetric, OF l\<^sub>0i_l\<^sub>0])

lemma [refine]:
  "(Pi (l\<^sub>0i, s\<^sub>0i), P' (l\<^sub>0, s\<^sub>0)) \<in> bool_rel"
  by parametricity

definition
  "check_all_pre1 \<equiv> do {
  b1 \<leftarrow> RETURN (Mi l\<^sub>0i \<noteq> None);
  b2 \<leftarrow> RETURN (Pi (l\<^sub>0i, s\<^sub>0i));
  case Mi l\<^sub>0i of
    None \<Rightarrow> RETURN False
  | Some xs \<Rightarrow> do {
    b3 \<leftarrow> RETURN (lei s\<^sub>0i xs);
    b4 \<leftarrow> check_prop1 Li Mi;
    RETURN (b1 \<and> b2 \<and> b3 \<and> b4)
  }
  }"

lemma Pi_P'_A' [refine,param]:
  "(Pi, P') \<in> K \<times>\<^sub>r A' \<rightarrow> bool_rel"
  using P'_nonempty Pi_P'
  by (smt (z3) A'_def case_prodD fun_relI mem_Collect_eq prod_relE prod_rel_simp tagged_fun_relD_both)

definition check_all_pre0 where
  "check_all_pre0 = do {
  b1 \<leftarrow> RETURN (l\<^sub>0 \<in> L);
  b2 \<leftarrow> RETURN (P' (l\<^sub>0, s\<^sub>0));
  case M l\<^sub>0 of
    None \<Rightarrow> RETURN False
  | Some xs \<Rightarrow> do {
    b3 \<leftarrow> RETURN (less_eq s\<^sub>0 xs);
    b4 \<leftarrow> check_prop P';
    RETURN (b1 \<and> b2 \<and> b3 \<and> b4)
  }
  }"

lemma check_all_pre0_correct:
  "check_all_pre0 \<le> SPEC (\<lambda>r. r \<longrightarrow> check_all_pre_spec l\<^sub>0 s\<^sub>0)"
  unfolding check_all_pre0_def check_all_pre_spec_def
  by (refine_vcg check_prop_correct; auto simp: list_ex_iff)

lemma check_all_pre0_1_refine:
  "(check_all_pre1, check_all_pre0) \<in> \<langle>bool_rel\<rangle>nres_rel" if "L = dom M"
unfolding check_all_pre1_def check_all_pre0_def
    apply (refine_rcg that; simp)
    supply [refine_mono] =
      monadic_list_ex_mono' monadic_list_ex_RETURN_mono specify_right HOL.refl
      check_prop1_refine[THEN fun_relD, THEN fun_relD, THEN nres_relD, THEN refine_IdD,
        of Li L Mi M, unfolded check_prop_alt_def]
      Li_L Mi_M
    supply [param] = lei_less_eq
   apply parametricity
  apply parametricity
  apply (rule order.trans)
  apply (rule refine_mono)
   apply refine_mono
  apply refine_mono
apply refine_rcg+
  by simp

lemma check_all_pre1_correct:
  "check_all_pre1 \<le> SPEC (\<lambda>r. r \<longrightarrow> check_all_pre_spec l\<^sub>0 s\<^sub>0)" if "L = dom M"
proof -
  note check_all_pre0_1_refine[THEN nres_relD]
  also note check_all_pre0_correct
  finally show ?thesis using that .
qed

lemma (in -) nres_cases'[case_names FAIL RES]:
  obtains "M=FAIL" | X where "X = {}" "M=RES X" | X where "X \<noteq> {}" "M=RES X"
  by (cases M) auto

text \<open>This is just a refinement-oriented alternative to derive @{thm check_all_pre1_correct}.\<close>
lemma check_prop_nofail:
  "nofail (check_prop P')"
  unfolding check_prop_def
  by (auto 4 5 intro: monadic_list_all_nofailI no_fail_RES_bindI split: option.split_asm)

lemma check_all_pre0_refine:
  "(check_all_pre0, check_all_pre l\<^sub>0 s\<^sub>0) \<in> \<langle>bool_rel\<rangle>nres_rel" if "L = dom M"
  apply (cases "M l\<^sub>0")
   apply (cases "P' (l\<^sub>0, s\<^sub>0)")
  unfolding check_all_pre0_def check_all_pre_def
  subgoal
    apply (refine_rcg, simp)
    apply (subst empty_not_subsumed, erule P'_nonempty)
    apply (cases "check_prop P'" rule: nres_cases'; simp)
    using check_prop_gt_SUCCEED by order
  subgoal
    apply (cases "check_prop P'" rule: nres_cases'; simp)
    subgoal
      using check_prop_nofail by refine_rcg
    subgoal for X
      using check_prop_gt_SUCCEED by order
    by refine_rcg
  by refine_rcg auto

lemma check_all_pre1_refine:
  "(check_all_pre1, check_all_pre l\<^sub>0 s\<^sub>0) \<in> \<langle>bool_rel\<rangle>nres_rel" if "L = dom M"
proof -
  note check_all_pre0_1_refine [THEN nres_relD]
  also note check_all_pre0_refine [THEN nres_relD]
  finally show ?thesis
    using that by refine_vcg
qed

definition
  "check_all1 \<equiv> do {
  b \<leftarrow> check_all_pre1;
  if b
  then do {
    r \<leftarrow> check_invariant1 Li;
    PRINT_CHECK STR ''State set invariant check'' r;
    RETURN r
  }
  else RETURN False
  }
"

lemma check_all1_correct[refine]:
  "check_all1 \<le> SPEC (\<lambda>r. r \<longrightarrow> check_all_pre_spec l\<^sub>0 s\<^sub>0 \<and> check_invariant_spec L)" if "L = dom M"
proof -
  note [refine] = check_all_pre1_correct [OF that]
  obtain L' where "(Li, L') \<in> \<langle>K\<rangle>list_rel" "set L' = L"
    using Li_L by (elim list_set_relE)
  note check_invariant1_refine
  also note check_invariant_correct
  also have [refine]: "check_invariant1 Li \<le> SPEC (\<lambda>r. r \<longrightarrow> check_invariant_spec L)"
    if "check_all_pre_spec l\<^sub>0 s\<^sub>0"
    apply (subst (2) \<open>_ = L\<close>[symmetric])
    apply (rule calculation)
    using Li_L \<open>(Li, L') \<in> _\<close> that unfolding check_all_pre_spec_def
    by (auto simp: \<open>_ = L\<close> \<open>L = _\<close> dest: P'_P)
  show ?thesis
    unfolding check_all1_def PRINT_CHECK_def comp_def by (refine_vcg; simp)
qed

definition
  "check_final1 L' = do {
  monadic_list_all (\<lambda>l. do {
    case op_map_lookup l Mi of None \<Rightarrow> RETURN True | Some xs \<Rightarrow> do {
      monadic_list_all (\<lambda>s.
        RETURN (\<not> PR_CONST Fi (l, s))
      ) xs
    }
    }
  ) L'
  }"

lemma check_final1_refine:
  "check_final1 Li \<le> check_final' L M"
    using Li_L apply (elim list_set_relE)
  unfolding check_final1_def check_final'_def
  apply (erule specify_right)
  supply [refine_mono] = monadic_list_all_mono'
  apply refine_mono
  apply (clarsimp split: option.splits)
  apply (refine_rcg monadic_list_all_mono')
   apply (simp flip: Mi_M_None_iff; fail)
  subgoal premises prems for _ li l xsi S
  proof -
    from \<open>(li, l) \<in> K\<close> have "(Mi li, M l) \<in> \<langle>\<langle>A\<rangle>list_set_rel\<rangle>option_rel"
      by parametricity
    with prems have "(xsi, S) \<in> \<langle>A\<rangle>list_set_rel"
      by auto
    then obtain xs where "(xsi, xs) \<in> \<langle>A\<rangle>list_rel" "set xs = S"
      by (elim list_set_relE)
    then show ?thesis
      using Fi_F \<open>(li, l) \<in> K\<close>
      by (refine_rcg monadic_list_all_mono' specify_right) (auto dest!: fun_relD)
  qed
  done

definition
  "certify_unreachable1 = do {
    b1 \<leftarrow> check_all1;
    b2 \<leftarrow> check_final1 Li;
    RETURN (b1 \<and> b2)
  }"

lemma certify_unreachable1_correct:
  "certify_unreachable1 \<le> SPEC (\<lambda>r. r \<longrightarrow> check_all_spec \<and> check_final_spec)" if "L = dom M"
proof -
  note check_final1_refine[unfolded check_final_alt_def]
  also note check_final_correct
  finally have [refine]: "check_final1 Li \<le> SPEC (\<lambda>r. r = check_final_spec)" .
  show ?thesis
    unfolding certify_unreachable1_def check_all_spec_def by (refine_vcg that; fast)
qed

paragraph \<open>Synthesizing a pure program via rewriting\<close>

lemma check_final1_alt_def:
  "check_final1 L' = RETURN (list_all_split
    (\<lambda>l. case op_map_lookup l Mi of None \<Rightarrow> True | Some xs \<Rightarrow> list_all (\<lambda>s. \<not> Fi (l, s)) xs) L')"
  unfolding check_final1_def
  unfolding monadic_list_all_RETURN[symmetric] list_all_split_def
  by (fo_rule arg_cong2, intro ext)
     (auto split: option.splits simp: monadic_list_all_RETURN[symmetric])

concrete_definition check_final_impl
  uses check_final1_alt_def is "_ = RETURN ?f"

schematic_goal check_prop1_alt_def:
  "check_prop1 L' M' \<equiv> RETURN ?f"
  unfolding check_prop1_def pure_unfolds Let_def .

concrete_definition check_prop_impl uses check_prop1_alt_def is "_ \<equiv> RETURN ?f"

schematic_goal check_all_pre1_alt_def:
  "check_all_pre1 \<equiv> RETURN ?f"
  unfolding check_all_pre1_def check_prop_impl.refine pure_unfolds .

concrete_definition check_all_pre_impl uses check_all_pre1_alt_def is "_ \<equiv> RETURN ?f" 

schematic_goal check_invariant1_alt_def:
  "check_invariant1 Li \<equiv> RETURN ?f"
  unfolding check_invariant1_def Let_def pure_unfolds .

concrete_definition check_invariant_impl uses check_invariant1_alt_def is "_ \<equiv> RETURN ?f"

schematic_goal certify_unreachable1_alt_def:
  "certify_unreachable1 \<equiv> RETURN ?f"
  unfolding
    certify_unreachable1_def check_all1_def check_final_impl.refine check_all_pre_impl.refine
    check_invariant_impl.refine
    pure_unfolds PRINT_CHECK_def comp_def short_circuit_conv .

concrete_definition certify_unreachable_impl_pure1
  uses certify_unreachable1_alt_def is "_ \<equiv> RETURN ?f"

text \<open>This is where we add parallel execution:\<close>

schematic_goal certify_unreachable_impl_pure1_alt_def:
  "certify_unreachable_impl_pure1 \<equiv> ?f"
  unfolding certify_unreachable_impl_pure1_def
  apply (abstract_let check_invariant_impl check_invariant)
  apply (abstract_let "check_final_impl Li" check_final)
  apply (abstract_let check_all_pre_impl check_all_pre_impl)
  apply (time_it "STR ''Time for state set preconditions check''" check_all_pre_impl)
  apply (time_it "STR ''Time for state space invariant check''"   check_invariant_impl)
  apply (time_it "STR ''Time to check final state predicate''"    "check_final_impl Li")
  unfolding
    check_invariant_impl_def check_all_pre_impl_def
    check_prop_impl_def check_final_impl_def
    list_all_split
  apply (subst list_all_default_split[where xs = Li, folded Parallel.map_def])
  .

concrete_definition (in -) certify_unreachable_impl_pure
  uses Reachability_Impl_pure.certify_unreachable_impl_pure1_alt_def is "_ \<equiv> ?f"

sublocale correct: Reachability_Impl_correct where
  M = "\<lambda>x. case M x of None \<Rightarrow> {} | Some S \<Rightarrow> abs_s ` S"
  apply standard
  oops

end (* Reachability_Impl_pure *)

locale Reachability_Impl_pure_correct =
  Reachability_Impl_pure where M = M +
  Reachability_Impl_correct where M = "\<lambda>x. case M x of None \<Rightarrow> {} | Some S \<Rightarrow> S" for M
begin

theorem certify_unreachable_impl_pure_correct:
  "certify_unreachable_impl_pure get_succs Li lei Li_split Pi Fi Mi l\<^sub>0i s\<^sub>0i
  \<longrightarrow> (\<nexists>s'. E\<^sup>*\<^sup>* (l\<^sub>0, s\<^sub>0) s' \<and> F s')"
  if "L = dom M"
  using certify_unreachable1_correct that
  unfolding
    certify_unreachable_impl_pure1.refine
    certify_unreachable_impl_pure.refine[OF Reachability_Impl_pure_axioms]
  using certify_unreachableI by simp

end (* Reachability_Impl_pure correct *)

end