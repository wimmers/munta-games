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
  assumes M_l\<^sub>0_not_None: "s\<^sub>0 \<preceq> {} \<Longrightarrow> M l\<^sub>0 \<noteq> None"
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
    apply (cases "s\<^sub>0 \<preceq> {}"; simp add: M_l\<^sub>0_not_None)
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

locale Reachability_Impl_imp_base =
  Reachability_Impl_base +
  Certification_Impl_imp_base

locale Reachability_Impl_imp_to_pure_base = Reachability_Impl_imp_base
  where K = K and A = A
  for K :: "'k \<Rightarrow> ('ki :: {hashable,heap}) \<Rightarrow> assn" and A :: "'s \<Rightarrow> ('si :: heap) \<Rightarrow> assn"
  +
  fixes to_state :: "'s1 \<Rightarrow> 'si Heap" and from_state :: "'si \<Rightarrow> 's1 Heap"
    and to_loc :: "'k1 \<Rightarrow> 'ki" and from_loc :: "'ki \<Rightarrow> 'k1"
  fixes lei
  fixes K_rel and A_rel
  fixes L_list :: "'ki list" and Li :: "'k1 list" and L :: "'k set" and L' :: "'k list"
  fixes Li_split :: "'k1 list list"
  assumes Li: "(L_list, L') \<in> \<langle>the_pure K\<rangle>list_rel" "(Li, L') \<in> \<langle>K_rel\<rangle>list_rel" "set L' = L"
  assumes to_state_ht: "(s1, s) \<in> A_rel \<Longrightarrow> <emp> to_state s1 <\<lambda>si. A s si>"
  assumes from_state_ht: "<A s si> from_state si <\<lambda>s'. \<up>((s', s) \<in> A_rel)>\<^sub>t"
  assumes from_loc: "(li, l) \<in> the_pure K \<Longrightarrow> (from_loc li, l) \<in> K_rel"
  assumes to_loc: "(l1, l) \<in> K_rel \<Longrightarrow> (to_loc l1, l) \<in> the_pure K"
  assumes K_rel: "single_valued K_rel" "single_valued (K_rel\<inverse>)"
  \<^cancel>\<open>assumes lei_less_eq: "(lei, (\<preceq>)) \<in> A_rel \<rightarrow> A_rel \<rightarrow> bool_rel"\<close>
  assumes lei_less_eq: "(lei, (\<preceq>)) \<in> A_rel \<rightarrow> \<langle>A_rel\<rangle>list_set_rel \<rightarrow> bool_rel"
  assumes full_split: "set Li = (\<Union>xs \<in> set Li_split. set xs)"
begin

definition
  "get_succs l xs \<equiv>
    do {
      let li = to_loc l;
      xsi \<leftarrow> Heap_Monad.fold_map to_state xs;
      r \<leftarrow> succsi li xsi;
      Heap_Monad.fold_map
        (\<lambda>(li, xsi). do {xs \<leftarrow> Heap_Monad.fold_map from_state xsi; return (from_loc li, xs)}) r
    }"

lemma get_succs:
  "(run_heap oo get_succs, succs)
  \<in> K_rel \<rightarrow> \<langle>A_rel\<rangle>list_set_rel \<rightarrow> \<langle>K_rel \<times>\<^sub>r \<langle>A_rel\<rangle>list_set_rel\<rangle>list_rel"
proof (refine_rcg, clarsimp, rule hoare_triple_run_heapD)
  fix l :: \<open>'k\<close> and l1 :: \<open>'k1\<close> and xs :: \<open>'s1 list\<close> and S :: \<open>'s set\<close>
  assume \<open>(l1, l) \<in> K_rel\<close> \<open>(xs, S) \<in> \<langle>A_rel\<rangle>list_set_rel\<close>
  then obtain ys where ys: "(xs, ys) \<in> \<langle>A_rel\<rangle>list_rel" "set ys = S"
    by (elim list_set_relE)
  have 1: "K = pure (the_pure K)"
    using pure_K by auto
  let ?li = "to_loc l1"
  show "<emp> get_succs l1 xs <\<lambda>r. \<up>((r, succs l S) \<in> \<langle>K_rel \<times>\<^sub>r \<langle>A_rel\<rangle>list_set_rel\<rangle>list_rel)>\<^sub>t"
    unfolding get_succs_def
    apply sep_auto
      (* fold_map to_state *)
     apply (rule Hoare_Triple.cons_pre_rule[rotated])
      apply (rule fold_map_ht3[where A = true and R = "pure A_rel" and Q = A and xs = ys])
    apply (sep_auto heap: to_state_ht simp: pure_def; fail)
     apply (unfold list_assn_pure_conv, sep_auto simp: pure_def ys; fail)
    apply sep_auto
      (* succsi *)
     apply (rule Hoare_Triple.cons_pre_rule[rotated], rule frame_rule[where R = true])
      apply (rule succsi[to_hnr, unfolded hn_refine_def hn_ctxt_def, simplified, of S _ l ?li])
    subgoal
      using ys \<open>(l1, l) \<in> K_rel\<close> unfolding lso_assn_def hr_comp_def br_def \<open>set ys = _\<close>[symmetric]
      by (subst 1) (sep_auto simp: pure_def to_loc)
        (* nested fold_map *)
    apply (sep_auto simp: invalid_assn_def)
    apply (rule cons_rule[rotated 2])
      apply (rule frame_rule)
      apply (rule fold_map_ht1[where
          A = true and R = "(K \<times>\<^sub>a lso_assn A)" and xs = "succs l S" and
          Q = "\<lambda>x xi. (xi, x) \<in> K_rel \<times>\<^sub>r \<langle>A_rel\<rangle>list_set_rel"
          ])
    subgoal
      unfolding lso_assn_def
      apply (subst 1, subst pure_def)
      apply (sep_auto simp: prod_assn_def hr_comp_def br_def split: prod.splits)
        (* inner fold_map *)
       apply (rule Hoare_Triple.cons_pre_rule[rotated])
        apply (rule fold_map_ht1[where A = true and R = A and Q = "\<lambda>l l1. (l1, l) \<in> A_rel"])
        apply (rule cons_rule[rotated 2], rule frame_rule, rule from_state_ht)
         apply frame_inference
        apply (sep_auto; fail)
       apply solve_entails
        (* return *)
      using list_all2_swap by (sep_auto simp: list.rel_eq list_set_rel_def from_loc list_rel_def)
     apply solve_entails
    using list_all2_swap by (sep_auto simp: list_rel_def)
qed

definition
  "to_pair \<equiv> \<lambda>(l, s). do {s \<leftarrow> to_state s; return (to_loc l, s)}"

lemma to_pair_ht:
  "<emp> to_pair a1 <\<lambda>ai. (K \<times>\<^sub>a A) a ai>" if "(a1, a) \<in> K_rel \<times>\<^sub>r A_rel"
  using that unfolding to_pair_def
  by (cases a, cases a1, subst pure_the_pure[symmetric, OF pure_K])
     (sep_auto heap: to_state_ht simp: pure_def to_loc prod_assn_def split: prod.splits)

sublocale pure:
  Reachability_Impl_pure_base2
  where
    get_succs = "run_heap oo get_succs" and
    K = K_rel and
    A = A_rel and
    lei = lei and
    Pi = "\<lambda>a. run_heap (do {a \<leftarrow> to_pair a; Pi a})" and
    Fi = "\<lambda>a. run_heap (do {a \<leftarrow> to_pair a; Fi a})" \<^cancel>\<open>and
    l\<^sub>0i = "from_loc (run_heap l\<^sub>0i)" and
    s\<^sub>0i = "run_heap (do {s \<leftarrow> s\<^sub>0i; from_state s})"\<close>
  apply standard
  subgoal
    by (rule K_rel)
  subgoal
    by (rule K_rel)
  subgoal
    using Li unfolding list_set_rel_def by auto
  subgoal
    by (rule lei_less_eq)
  subgoal
    using get_succs .
  subgoal
    by (rule full_split)
  subgoal
    apply standard
    apply (rule hoare_triple_run_heapD)
    apply (sep_auto heap: to_pair_ht simp del: prod_rel_simp prod_assn_pair_conv)
    apply (rule Hoare_Triple.cons_rule[rotated 2])
      apply (rule Pi_P'[to_hnr, unfolded hn_refine_def hn_ctxt_def, simplified], rule ent_refl)
    apply (sep_auto simp: pure_def)
    done
  subgoal
    apply standard
    apply (rule hoare_triple_run_heapD)
    apply (sep_auto heap: to_pair_ht simp del: prod_rel_simp prod_assn_pair_conv)
    apply (rule Hoare_Triple.cons_rule[rotated 2])
      apply (rule Fi_F[to_hnr, unfolded hn_refine_def hn_ctxt_def, simplified], rule ent_refl)
    apply (sep_auto simp: pure_def)
    done
  done

end

locale Reachability_Impl_imp_to_pure = Reachability_Impl where
  l\<^sub>0 = l\<^sub>0 and s\<^sub>0 = s\<^sub>0 and M = M and K = K and A = A
  + Reachability_Impl_imp_to_pure_base
  where K_rel = K_rel and A_rel = A_rel and K = K and A = A
  for l\<^sub>0 :: 'k and s\<^sub>0 :: 'a
  and K :: "'k \<Rightarrow> ('ki :: {hashable,heap}) \<Rightarrow> assn" and A :: "'a \<Rightarrow> ('ai :: heap) \<Rightarrow> assn"
  and M and K_rel :: "('k1 \<times> 'k) set" and A_rel :: "('a1 \<times> 'a) set" +
  fixes Mi :: "'k1 \<Rightarrow> 'a1 list option"
  assumes Mi_M: "(Mi, M) \<in> K_rel \<rightarrow> \<langle>\<langle>A_rel\<rangle>list_set_rel\<rangle>option_rel"
  fixes nonempty :: "'a \<Rightarrow> bool"
  assumes empty_not_subsumed [simp]:
    "nonempty x \<Longrightarrow> x \<preceq> {} \<longleftrightarrow> False"
  assumes succs_nonempty:
    "(l', S') \<in> set (succs l S) \<Longrightarrow> x \<in> S' \<Longrightarrow> nonempty x"
  assumes M_l\<^sub>0_not_None: "s\<^sub>0 \<preceq> {} \<Longrightarrow> M l\<^sub>0 \<noteq> None"
begin

sublocale pure:
  Reachability_Impl_pure
  where           
    M = M and
    Mi = Mi and
    get_succs = "run_heap oo get_succs" and
    K = K_rel and
    A = A_rel and
    lei = lei and
    Pi = "\<lambda>a. run_heap (do {a \<leftarrow> to_pair a; Pi a})" and
    Fi = "\<lambda>a. run_heap (do {a \<leftarrow> to_pair a; Fi a})" and
    l\<^sub>0i = "from_loc (run_heap l\<^sub>0i)" and
    s\<^sub>0i = "run_heap (do {s \<leftarrow> s\<^sub>0i; from_state s})"
  apply standard
    apply (rule Mi_M)
  subgoal
    apply (rule from_loc)
    apply (rule hoare_triple_run_heapD)
    using l\<^sub>0i_l\<^sub>0[to_hnr, unfolded hn_refine_def hn_ctxt_def, simplified]
    apply (subst (asm) pure_the_pure[symmetric, OF pure_K])
    apply (sep_auto simp: pure_def elim!: cons_post_rule)
    done
  subgoal
    using s\<^sub>0i_s\<^sub>0[to_hnr, unfolded hn_refine_def hn_ctxt_def, simplified]
    by - (rule hoare_triple_run_heapD, sep_auto heap: from_state_ht)
  apply (rule empty_not_subsumed succs_nonempty M_l\<^sub>0_not_None; assumption; fail)+
  done

end

locale Reachability_Impl_imp_to_pure_correct =
  Reachability_Impl_imp_to_pure where M = M
  + Reachability_Impl_correct where M = "\<lambda>x. case M x of None \<Rightarrow> {} | Some S \<Rightarrow> S"
  for M
begin

sublocale pure:
  Reachability_Impl_pure_correct
  where           
    M = M and
    Mi = Mi and
    get_succs = "run_heap oo get_succs" and
    K = K_rel and
    A = A_rel and
    lei = lei and
    Pi = "\<lambda>a. run_heap (do {a \<leftarrow> to_pair a; Pi a})" and
    Fi = "\<lambda>a. run_heap (do {a \<leftarrow> to_pair a; Fi a})" and
    l\<^sub>0i = "from_loc (run_heap l\<^sub>0i)" and
    s\<^sub>0i = "run_heap (do {s \<leftarrow> s\<^sub>0i; from_state s})"
  by standard

end

end