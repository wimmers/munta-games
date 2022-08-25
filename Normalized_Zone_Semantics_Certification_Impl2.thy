theory Normalized_Zone_Semantics_Certification_Impl2
  \<comment> \<open>This name is already duplicated but has nothing to do with that other theory.\<close>  
  imports
    Safety_Certification_Pure
    Timed_Game_Certification_Impl
    Normalized_Zone_Semantics_Certification2
    Certification.Unreachability_TA_Misc
    TA_Library.Reordering_Quantifiers
    TA_Library.More_Methods
    \<^cancel>\<open>Certification.Normalized_Zone_Semantics_Certification_Impl\<close> \<comment> \<open>We will duplicate this stuff\<close>
    \<comment> \<open>Need to rename local copy of Normalized_Zone_Semantics_Certification\<close>
begin

hide_const (open) Refine_Foreach.list_set_rel
hide_const (open) Simulation_Graphs_Certification.C

subsection \<open>Misc refinement setup\<close>

instance move :: ("{countable}") countable
  by (rule countable_classI[of
        "\<lambda> Act a \<Rightarrow> to_nat (0::nat,a)
         | Wait \<Rightarrow> to_nat (1::nat,undefined::'a)"])
     (simp split: move.splits)

instance move :: ("{heap}") heap ..

fun move_assn where
  "move_assn A (Act a) (Act b) = A a b"
| "move_assn A Wait Wait = (\<up>(True))"
| "move_assn A _ _ = false"

lemma Act_refine [sepref_fr_rules]:
  "(return o Act, RETURN o Act) \<in> A\<^sup>d \<rightarrow>\<^sub>a move_assn A"
  by sepref_to_hoare sep_auto

lemma Wait_refine [sepref_fr_rules]:
  "(uncurry0 (return Wait), uncurry0 (RETURN Wait)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a move_assn A"
  by sepref_to_hoare sep_auto

lemma fold_set_member_bex:
  "a \<in> S \<longleftrightarrow> (\<exists>x \<in> S. x = a)"
  by auto


subsection \<open>Successor Implementation\<close>

context TGA_Start_Defs
begin

paragraph \<open>Refinement\<close>

definition succs_precise where
  "succs_precise \<equiv> \<lambda>l T.
    if T = {} then []
    else rev [
      (l', {D' | D' D D\<^sub>s C.
        D \<in> T \<and> (D\<^sub>s, C) \<in> set (S (l, D)) \<and> Act a \<in> C \<and> D' = act l r g l' D\<^sub>s \<and> \<not> check_diag n D'
       }).
        (g,a,r,l') \<leftarrow> trans_fun l, controllable a
    ]
    @ rev [
      (l', {D' | D' D. D \<in> T \<and> D' = act l r g l' D \<and> \<not> check_diag n D'}).
        (g,a,r,l') \<leftarrow> trans_fun l, \<not> controllable a
    ]
    @ [
      (l, {D' | D' D D\<^sub>s C.
        D \<in> T \<and> (D\<^sub>s, C) \<in> set (S (l, D)) \<and> Wait \<in> C \<and> D' = del l D\<^sub>s \<and> \<not> check_diag n D'
      })
    ]"

definition succs_ctl_inner where
 "succs_ctl_inner a l r g l' T \<equiv> do {
    xs \<leftarrow> SPEC (\<lambda>xs. set xs = T);
    p \<leftarrow> nfoldli xs (\<lambda>_. True) (\<lambda>D xs.
      do {
        let Strat = PR_CONST S (l, D);
        nfoldli Strat (\<lambda>_. True) (\<lambda>(D\<^sub>s, C) xs.
          if Act a \<in> C then
            do {
              let D' = PR_CONST act l r g l' D\<^sub>s;
              if check_diag n D' then RETURN xs else RETURN (D' # xs)
            }
          else
            RETURN xs
        ) xs
      }
    ) [];
    S' \<leftarrow> SPEC (\<lambda>S. set p = S);
    RETURN S'
  }"

definition succs_wait_inner where
 "succs_wait_inner l T \<equiv> do {
    xs \<leftarrow> SPEC (\<lambda>xs. set xs = T);
    p \<leftarrow> nfoldli xs (\<lambda>_. True) (\<lambda>D xs.
      do {
        let Strat = PR_CONST S (l, D);
        nfoldli Strat (\<lambda>_. True) (\<lambda>(D\<^sub>s, C) xs.
          if Wait \<in> C then
            do {
              let D' = PR_CONST del l D\<^sub>s;
              if check_diag n D' then RETURN xs else RETURN (D' # xs)
            }
          else
            RETURN xs
        ) xs
      }
    ) [];
    S' \<leftarrow> SPEC (\<lambda>S. set p = S);
    RETURN S'
  }"

definition succs_uctl_inner where
 "succs_uctl_inner l r g l' T \<equiv> do {
    xs \<leftarrow> SPEC (\<lambda>xs. set xs = T);
    p \<leftarrow> nfoldli xs (\<lambda>_. True) (\<lambda>D xs.
      do {let D' = PR_CONST act l r g l' D; if check_diag n D' then RETURN xs else RETURN (D' # xs)}
    ) [];
    S' \<leftarrow> SPEC (\<lambda>S. set p = S);
    RETURN S'
  }"

definition succs_precise' where
  "succs_precise' \<equiv> \<lambda>l T. if T = {} then RETURN [] else do {
    wait \<leftarrow> succs_wait_inner l (COPY T);
    let acc = [(l, wait)];
    acc \<leftarrow> nfoldli (trans_fun l) (\<lambda>_. True) (\<lambda> (g,a,r,l') xxs.
      if controllable a then
        RETURN xxs
      else
        do {
          S' \<leftarrow> PR_CONST succs_uctl_inner l r g l' (COPY T);
          RETURN ((l', S') # xxs)
        }
    ) acc;
    nfoldli (trans_fun l) (\<lambda>_. True) (\<lambda> (g,a,r,l') xxs.
      if controllable a then
        do {
          S' \<leftarrow> PR_CONST succs_ctl_inner a l r g l' (COPY T);
          RETURN ((l', S') # xxs)
        }
      else
        RETURN xxs
    ) acc
  }"

definition
  "succs_uctl_inner_spec l r g l' T = {D' | D' D. D \<in> T \<and> D' = act l r g l' D \<and> \<not> check_diag n D'}"

lemma succs_uctl_inner_rule[folded succs_uctl_inner_spec_def]:
  "succs_uctl_inner l r g l' T
  \<le> RETURN {D' | D' D. D \<in> T \<and> D' = act l r g l' D \<and> \<not> check_diag n D'}"
  unfolding succs_uctl_inner_def
  by (refine_vcg nfoldli_rule[where
        I = "\<lambda>l1 l2 \<sigma>. \<sigma> = rev (filter (\<lambda>D'. \<not> check_diag n D') (map (act l r g l') l1))"
     ]) auto

definition
  "succs_ctl_inner_spec a l r g l' T
  = {D' | D' D D\<^sub>s C.
        D \<in> T \<and> (D\<^sub>s, C) \<in> set (S (l, D)) \<and> Act a \<in> C \<and> D' = act l r g l' D\<^sub>s \<and> \<not> check_diag n D'
       }"

lemma succs_ctl_inner_rule[folded succs_ctl_inner_spec_def]:
  "succs_ctl_inner a l r g l' T
  \<le> RETURN {D' | D' D D\<^sub>s C.
        D \<in> T \<and> (D\<^sub>s, C) \<in> set (S (l, D)) \<and> Act a \<in> C \<and> D' = act l r g l' D\<^sub>s \<and> \<not> check_diag n D'
       }"
  unfolding succs_ctl_inner_def
  apply (refine_vcg nfoldli_rule[where
        I = "\<lambda>l1 l2 \<sigma>. \<sigma> = rev [act l r g l' D\<^sub>s.
        D \<leftarrow> l1, (D\<^sub>s, C) \<leftarrow> S (l, D), Act a \<in> C, \<not> check_diag n (act l r g l' D\<^sub>s)
       ]"
     ])
  apply (simp; fail)
  subgoal for xs D l1 l2 acc
    by (refine_vcg nfoldli_rule[where
        I = "\<lambda>l1 l2 \<sigma>. \<sigma> = rev [act l r g l' D\<^sub>s.
        (D\<^sub>s, C) \<leftarrow> l1, Act a \<in> C, \<not> check_diag n (act l r g l' D\<^sub>s)
       ] @ acc"
     ]) auto
  by auto

definition
  "succs_wait_inner_spec l T
  = {D' | D' D D\<^sub>s C.
        D \<in> T \<and> (D\<^sub>s, C) \<in> set (S (l, D)) \<and> Wait \<in> C \<and> D' = del l D\<^sub>s \<and> \<not> check_diag n D'
       }"

lemma succs_wait_inner_rule[folded succs_wait_inner_spec_def]:
  "succs_wait_inner l T
  \<le> RETURN {D' | D' D D\<^sub>s C.
        D \<in> T \<and> (D\<^sub>s, C) \<in> set (S (l, D)) \<and> Wait \<in> C \<and> D' = del l D\<^sub>s \<and> \<not> check_diag n D'
       }"
  unfolding succs_wait_inner_def
  apply (refine_vcg nfoldli_rule[where
        I = "\<lambda>l1 l2 \<sigma>. \<sigma> = rev [del l D\<^sub>s.
        D \<leftarrow> l1, (D\<^sub>s, C) \<leftarrow> S (l, D), Wait \<in> C, \<not> check_diag n (del l D\<^sub>s)
       ]"
     ])
  apply (simp; fail)
  subgoal for xs D l1 l2 acc
    by (refine_vcg nfoldli_rule[where
        I = "\<lambda>l1 l2 \<sigma>. \<sigma> = rev [del l D\<^sub>s.
        (D\<^sub>s, C) \<leftarrow> l1, Wait \<in> C, \<not> check_diag n (del l D\<^sub>s)
       ] @ acc"
     ]) auto
  by auto

lemma succs_precise'_refine:
  "succs_precise' l T \<le> RETURN (succs_precise l T)"
proof -
  define acc1 where "acc1 =
    [(l, succs_wait_inner_spec l T)]"
  define acc2 where "acc2 = (\<lambda>xs.
    rev [(l', succs_uctl_inner_spec l r g l' T). (g,a,r,l') \<leftarrow> xs, \<not> controllable a] @ acc1)"
  define acc3 where "acc3 = (\<lambda>xs.
    rev [(l', succs_ctl_inner_spec a l r g l' T). (g,a,r,l') \<leftarrow> xs, controllable a ]
    @ acc2 (trans_fun l))"
  note fold_rule1 =
    nfoldli_rule[where I = "\<lambda>l1 l2 \<sigma>. \<sigma> = acc2 l1" and P = "\<lambda>\<sigma>. \<sigma> = acc2 (trans_fun l)"]
    and fold_rule2 =
    nfoldli_rule[where I = "\<lambda>l1 l2 \<sigma>. \<sigma> = acc3 l1" and P = "\<lambda>\<sigma>. \<sigma> = acc3 (trans_fun l)"]
  show ?thesis
    unfolding succs_precise_def succs_precise'_def PR_CONST_def
      succs_wait_inner_spec_def[symmetric] succs_ctl_inner_spec_def[symmetric]
      succs_uctl_inner_spec_def[symmetric]
    apply simp
    apply refine_vcg
    apply (rule order.trans, rule succs_wait_inner_rule)
    apply refine_vcg
    apply (rule order.trans, rule fold_rule1)
        apply (simp add: acc2_def acc1_def; fail)
       apply refine_vcg
        apply (simp add: acc2_def; fail)
       apply (rule order.trans, rule succs_uctl_inner_rule)
       apply refine_vcg
       apply (simp add: acc2_def acc1_def; fail)
      apply (simp; fail)+
    apply refine_vcg
    apply (rule order.trans, rule fold_rule2)
        apply (simp add: acc3_def; fail)
       apply (refine_vcg succs_ctl_inner_rule)
        apply (rule order.trans, rule succs_ctl_inner_rule)
        apply (simp add: acc3_def; fail)+
    apply (simp add: acc3_def acc2_def acc1_def)
    done
qed

lemma succs_precise'_correct:
  "(uncurry succs_precise', uncurry (RETURN oo PR_CONST succs_precise)) \<in> Id \<times>\<^sub>r Id \<rightarrow> \<langle>Id\<rangle>nres_rel"
  using succs_precise'_refine by (clarsimp simp: pw_le_iff pw_nres_rel_iff)


paragraph \<open>Synthesis\<close>

sepref_register "PR_CONST act" ::
  "'s \<Rightarrow> nat list \<Rightarrow> (nat, int) acconstraint list \<Rightarrow> 's \<Rightarrow> int DBMEntry i_mtx \<Rightarrow> int DBMEntry i_mtx"

sepref_register "PR_CONST del" ::
  "'s \<Rightarrow> int DBMEntry i_mtx \<Rightarrow> int DBMEntry i_mtx"

sepref_register "PR_CONST S"
  :: "'s \<times> int DBMEntry i_mtx \<Rightarrow> (int DBMEntry i_mtx \<times> 'a move set) list"

lemma aux:
  "b ::\<^sub>i TYPE((nat \<times> nat \<Rightarrow> int DBMEntry) set) \<Longrightarrow>
       ID b b TYPE(int DBMEntry i_mtx set)"
  unfolding ID_def by simp

lemma aux':
  "(b ::\<^sub>i TYPE((nat \<times> nat \<Rightarrow> int DBMEntry) set)) = (b ::\<^sub>i TYPE(int DBMEntry i_mtx set))"
  by simp

lemma aux'':
  "(b ::\<^sub>i TYPE((nat \<times> nat \<Rightarrow> int DBMEntry) )) = (b ::\<^sub>i TYPE(int DBMEntry i_mtx))"
  by simp

lemma aux3:
  "ID D x'a TYPE(nat \<times> nat \<Rightarrow> int DBMEntry) = ID D x'a TYPE(int DBMEntry i_mtx)"
  by simp

lemmas [sepref_fr_rules] =
  set_of_list_hnr Leadsto_Impl.lso_id_hnr
  act_impl del_impl

end


locale TGA_Start_Impl =
  TGA_Start_Defs +
  fixes S_impl
  assumes S_impl: "(S_impl, RETURN o PR_CONST S)
    \<in> (location_assn \<times>\<^sub>a mtx_assn n)\<^sup>d \<rightarrow>\<^sub>a list_assn (mtx_assn n \<times>\<^sub>a lso_assn (move_assn id_assn))"
  \<^cancel>\<open>assumes S_impl: "(S_impl, RETURN o PR_CONST S)
    \<in> state_assn'\<^sup>d \<rightarrow>\<^sub>a list_assn (mtx_assn n \<times>\<^sub>a lso_assn id_assn)"\<close>
begin

lemmas [sepref_fr_rules] = S_impl

interpretation DBM_Impl n .

sepref_definition succs_uctl_inner_impl is
  "uncurry4 (PR_CONST succs_uctl_inner)"
  :: "location_assn\<^sup>k *\<^sub>a (list_assn clock_assn)\<^sup>k *\<^sub>a
      (list_assn (acconstraint_assn clock_assn int_assn))\<^sup>k *\<^sub>a
      location_assn\<^sup>k *\<^sub>a (lso_assn mtx_assn)\<^sup>d
  \<rightarrow>\<^sub>a lso_assn mtx_assn"
  unfolding PR_CONST_def
  unfolding succs_uctl_inner_def
    list_of_set_def[symmetric] set_of_list_def[symmetric]
  apply (rewrite HOL_list.fold_custom_empty)
  apply sepref_dbg_keep
     apply sepref_dbg_id_keep
  unfolding aux3
         apply sepref_dbg_id_step+
     apply sepref_dbg_monadify
     apply sepref_dbg_opt_init
      apply sepref_dbg_trans_keep
     apply sepref_dbg_opt
    apply sepref_dbg_cons_solve
   apply sepref_dbg_cons_solve
  apply sepref_dbg_constraints
  done

lemma move_assn_id_assn [simp]:
  "move_assn id_assn = id_assn"
  apply (intro ext)
  subgoal for x y
    by (cases x; cases y; simp add: pure_def)
  done

lemma eq_move_id_import [sepref_import_param]:
  "((=), (=)) \<in> (Id :: (_ move * _) set) \<rightarrow> Id \<rightarrow> Id"
  by simp

\<comment> \<open>This was an attempt to apply @{thm eq_move_id_import} directly but we would probably also need
  the converse.\<close>
lemma hn_ctxt_hn_val_move_assn_match[sepref_frame_match_rules]:
  "hn_ctxt (move_assn id_assn) xf xi \<Longrightarrow>\<^sub>t hn_val Id xf xi"
  by simp

lemma eq_move_id_import' [sepref_fr_rules]:
  fixes x
  shows
    "hn_refine
      (hn_ctxt (move_assn id_assn) x' x * hn_ctxt (move_assn id_assn) x'a xa)
      (return (x = xa))
      (hn_ctxt (move_assn id_assn) x' x * hn_ctxt (move_assn id_assn) x'a xa)
      bool_assn (RETURN $ ((=) $ x' $ x'a))"
  using eq_move_id_import by simp

sepref_definition succs_ctl_inner_impl is
  "uncurry5 (PR_CONST succs_ctl_inner)"
  :: "id_assn\<^sup>k *\<^sub>a location_assn\<^sup>k *\<^sub>a (list_assn clock_assn)\<^sup>k *\<^sub>a
      (list_assn (acconstraint_assn clock_assn int_assn))\<^sup>k *\<^sub>a
      location_assn\<^sup>k *\<^sub>a (lso_assn mtx_assn)\<^sup>d
  \<rightarrow>\<^sub>a lso_assn mtx_assn"
  unfolding PR_CONST_def
  unfolding succs_ctl_inner_def
    list_of_set_def[symmetric] set_of_list_def[symmetric]
  apply (rewrite in \<open>Act _ \<in> _\<close> fold_set_member_bex[unfolded IICF_List_SetO.fold_lso_bex])
  apply (rewrite HOL_list.fold_custom_empty)
  apply sepref_dbg_keep
     apply sepref_dbg_id_keep
  unfolding aux3
         apply sepref_dbg_id_step+
     apply sepref_dbg_monadify
     apply sepref_dbg_opt_init
      apply sepref_dbg_trans_keep
     apply sepref_dbg_opt
    apply sepref_dbg_cons_solve
   apply sepref_dbg_cons_solve
  apply sepref_dbg_constraints
  done

sepref_definition succs_wait_inner_impl is
  "uncurry (PR_CONST succs_wait_inner)"
  :: "location_assn\<^sup>k *\<^sub>a (lso_assn mtx_assn)\<^sup>d
  \<rightarrow>\<^sub>a lso_assn mtx_assn"
  unfolding PR_CONST_def
  unfolding succs_wait_inner_def
    list_of_set_def[symmetric] set_of_list_def[symmetric]
  apply (rewrite in \<open>Wait \<in> _\<close> fold_set_member_bex[unfolded IICF_List_SetO.fold_lso_bex])
  apply (rewrite HOL_list.fold_custom_empty)
  apply sepref_dbg_keep
     apply sepref_dbg_id_keep
  unfolding aux3
         apply sepref_dbg_id_step+
     apply sepref_dbg_monadify
     apply sepref_dbg_opt_init
      apply sepref_dbg_trans_keep
     apply sepref_dbg_opt
    apply sepref_dbg_cons_solve
   apply sepref_dbg_cons_solve
  apply sepref_dbg_constraints
  done

sepref_register succs_uctl_inner succs_ctl_inner succs_wait_inner

lemmas [sepref_fr_rules] =
  succs_uctl_inner_impl.refine
  succs_ctl_inner_impl.refine
  succs_wait_inner_impl.refine

lemmas [sepref_fr_rules] = copy_list_lso_assn_refine[OF amtx_copy_hnr]

sepref_register controllable

lemma controllable_import [sepref_import_param]:
  "(controllable, controllable) \<in> Id \<rightarrow> Id"
  by simp

text \<open>We want to reuse the refinement setup for \<^term>\<open>trans_fun\<close> and friends.
To do so soundly, we should find a sane interpretation for \<open>TA_Impl_Op\<close> or move most of the setup
out of \<open>TA_Impl_Op\<close>.
\<close>
interpretation legacy: TA_Impl_Op where f = undefined and op_impl = undefined
  apply standard
  sorry

\<comment> \<open>Note: the \<open>d\<close> in the specification can also be a \<open>k\<close>.\<close>
sepref_definition succs_precise'_impl is
  "uncurry succs_precise'"
  :: "location_assn\<^sup>k *\<^sub>a (lso_assn mtx_assn)\<^sup>d
      \<rightarrow>\<^sub>a list_assn (prod_assn location_assn (lso_assn mtx_assn))"
  unfolding PR_CONST_def
  unfolding
    comp_def succs_precise'_def
    FW''_def[symmetric] rev_map_fold inv_of_A_def[symmetric]
    list_of_set_def[symmetric] set_of_list_def[symmetric]
  unfolding HOL_list.fold_custom_empty by sepref

lemmas succs_precise_impl_refine = succs_precise'_impl.refine[FCOMP succs_precise'_correct]


lemma succs_precise_finite:
  "\<forall>l S. \<forall>(l', S')\<in>set (succs_precise l S). finite S \<longrightarrow> finite S'"
  unfolding succs_precise_def by auto

lemma E_from_op_states:
  "l' \<in> states'" if "op_precise.E_from_op (l, M) a (l', M')" "l \<in> states'"
  using that unfolding op_precise.E_from_op_def by (auto split: action.split_asm)

end


subsection \<open>A new implementation invariant for DBMs\<close>
\<comment> \<open>Completely duplicated.\<close>

context TA_Impl_Ext
begin

definition
  "wf_dbm' D \<equiv> (canonical' D \<or> check_diag n D) \<and>
     (list_all (\<lambda>i. D (i, i) \<le> 0) [0..<n+1]) \<and> list_all (\<lambda>i. D (0, i) \<le> 0) [0..<n+1]"

theorem wf_dbm'_wf_dbm:
  fixes D :: "nat \<times> nat \<Rightarrow> int DBMEntry"
  assumes "wf_dbm' D"
  shows "wf_dbm D"
  using assms
  unfolding wf_dbm'_def wf_dbm_def valid_dbm_def list_all_iff canonical'_conv_M_iff
  unfolding valid_dbm.simps
  apply (elim conjE)
  apply (rule conjI)
   apply blast
  apply (rule conjI)
  subgoal
    by (intro impI diag_conv_M) auto
  apply (inst_existentials "curry (conv_M D)")
    apply (rule HOL.refl)
   apply (rule V_I)
  subgoal
    apply (auto del: disjE)
    subgoal for i
      apply (subgoal_tac "D (0, i) \<le> Le 0")
       apply (auto dest: conv_dbm_entry_mono simp: neutral del: disjE)
      apply (cases "i = n")
       apply auto
      done
    done
  apply (rule dbm_int_conv)
  done

lemma canonical'_compute:
  "canonical' M =
  list_all (\<lambda>i.
    list_all (\<lambda>j.
      list_all (\<lambda>k.
        M (i, k) \<le> M (i, j) + M (j, k)
  )[0..<n+1]) [0..<n+1]) [0..<n+1]
  "
  unfolding list_all_iff by auto force

interpretation DBM_Impl n .

sepref_definition canonical'_impl is
  "RETURN o PR_CONST canonical'" :: "mtx_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn"
  unfolding canonical'_compute list_all_foldli PR_CONST_def by sepref

sepref_thm wf_dbm'_impl is
  "RETURN o PR_CONST wf_dbm'" :: "mtx_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn"
  unfolding wf_dbm'_def canonical'_compute list_all_foldli PR_CONST_def by sepref

definition
  "states_mem l \<equiv> l \<in> states'"

definition
  "P \<equiv> \<lambda> (l, M). PR_CONST states_mem l \<and> wf_dbm' M"

lemma P_correct:
  "l \<in> states' \<and> wf_dbm M" if "P (l, M)"
  using that unfolding P_def states_mem_def by (auto intro: wf_dbm'_wf_dbm)

(* lemma [sepref_import_param]:
  "(states_mem, states_mem) \<in> Id \<rightarrow> Id"
  by simp *)

lemmas [sepref_import_param] = states_mem_impl[folded states_mem_def]

sepref_register states_mem

(* sepref_thm is_in_states_impl is
  "RETURN o PR_CONST states_mem" :: "(pure loc_rel)\<^sup>k \<rightarrow>\<^sub>a bool_assn"
  unfolding PR_CONST_def by sepref *)

sepref_register wf_dbm' :: "'fresh DBMEntry i_mtx \<Rightarrow> bool"

lemmas [sepref_fr_rules] =
  (* is_in_states_impl.refine_raw *)
  wf_dbm'_impl.refine_raw

sepref_definition P_impl is
  "RETURN o PR_CONST P" :: "(prod_assn (pure loc_rel) mtx_assn)\<^sup>k \<rightarrow>\<^sub>a bool_assn"
  unfolding PR_CONST_def P_def by sepref

(* XXX Better proof technique? *)
lemma P_impl_refine:
  "(P_impl, (RETURN \<circ>\<circ> PR_CONST) P) \<in> (location_assn \<times>\<^sub>a mtx_assn)\<^sup>k \<rightarrow>\<^sub>a bool_assn"
  apply sepref_to_hoare
  apply sep_auto
  subgoal for l M l' M'
    using P_impl.refine[to_hnr, unfolded hn_refine_def hn_ctxt_def, rule_format, of "(l, M)"]
    by (sep_auto simp: pure_def)
  done

\<^cancel>\<open>lemmas [safe_constraint_rules] = location_assn_constraints\<close>

\<comment> \<open>See discussion of above.\<close>
interpretation legacy: TA_Impl_Op where f = undefined and op_impl = undefined
  apply standard
  sorry

lemmas location_assn_constraints [safe_constraint_rules] = legacy.location_assn_constraints

end (* TA Impl Precise *)

\<comment> \<open>Duplicated\<close>

subsection \<open>Refinement setup: \<open>list_to_dbm\<close>/\<open>set\<close>\<close>
context TA_Impl
begin

term placeholder

sepref_register "list_to_dbm n"

lemmas [sepref_fr_rules] = of_list_list_to_dbm[of n]

sepref_register set

lemmas [sepref_fr_rules] = set_of_list_hnr'


lemma IArray_list_to_dbm_rel[param]:
  "(IArray, list_to_dbm n)
  \<in> {(xs, ys). xs = ys \<and> length xs = Suc n * Suc n} \<rightarrow> {(a, b). iarray_mtx_rel (Suc n) (Suc n) b a}"
  unfolding list_to_dbm_def op_amtx_new_def iarray_mtx_rel_def Unreachability_TA_Misc.dbm_tab_def
  by (auto simp: algebra_simps)

lemma IArray_list_to_dbm_rel':
  "(map IArray xs, list_to_dbm n ` set xs)
  \<in> \<langle>{(a, b). iarray_mtx_rel (Suc n) (Suc n) b a}\<rangle>list_set_rel"
  if "list_all (\<lambda>xs. length xs = Suc n * Suc n) xs"
  using that by (rule map_set_rel) (rule IArray_list_to_dbm_rel)

end


subsection \<open>Table Implementations\<close>
\<comment> \<open>Slightly refactored\<close>

locale TA_Impl_Loc_List =
  TA_Impl_Ext where A = A and l\<^sub>0i = l\<^sub>0i
  for A :: "('a, nat, int, 's) ta" and l\<^sub>0i :: "'si:: {hashable,heap}" +
  fixes L_list :: "'si list" and P_loc
  assumes state_impl_abstract: "\<And>li. P_loc li \<Longrightarrow> \<exists>l. (li, l) \<in> loc_rel"
  assumes P_loc: "list_all (\<lambda>x. P_loc x \<and> states_mem_impl x) L_list"

context TA_Impl_Loc_List
begin

definition
  "L \<equiv> map (\<lambda>li. SOME l. (li, l) \<in> loc_rel) L_list"

lemma mem_states'I:
  "l \<in> states'" if "states_mem_impl li" "(li, l) \<in> loc_rel" for l li
  using states_mem_impl that by (auto dest: fun_relD)

lemma L_list_rel:
  "(L_list, L) \<in> \<langle>location_rel\<rangle>list_rel"
  unfolding list_rel_def L_def
  using P_loc
  apply (clarsimp simp: list.pred_rel list.rel_map)
  apply (elim list_all2_mono)
  apply (clarsimp simp: eq_onp_def)
  apply (meson someI_ex state_impl_abstract)
  apply (erule mem_states'I, meson someI_ex state_impl_abstract)
  done

lemma L_list_hnr:
  "(uncurry0 (return L_list), uncurry0 (RETURN (PR_CONST (set L))))
  \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a lso_assn location_assn"
proof -
  have "(\<lambda>a c. \<up> ((c, a) \<in> loc_rel \<and> a \<in> states')) = pure location_rel"
    unfolding pure_def by auto
  then have "list_assn (\<lambda>a c. \<up> ((c, a) \<in> loc_rel \<and> a \<in> states')) = pure (\<langle>location_rel\<rangle>list_rel)"
    by (simp add: fcomp_norm_unfold)
  then have "emp \<Longrightarrow>\<^sub>A list_assn (\<lambda>a c. \<up> ((c, a) \<in> loc_rel \<and> a \<in> states')) L L_list * true"
    by (sep_auto simp: pure_def intro: L_list_rel)
  then show ?thesis
    by sepref_to_hoare (sep_auto simp: lso_assn_def hr_comp_def br_def)
qed

end

context TA_Impl_Loc_List
begin

context
  fixes M_list :: "('si \<times> 'v list) list" and g :: "'v \<Rightarrow> 'v1" and h :: "'v \<Rightarrow> 'v2"
    and P :: "'v \<Rightarrow> bool" and R :: "('v2 \<times> 'v1) set"
begin

definition
  "M_list1 \<equiv> map (\<lambda>(li, xs). (SOME l. (li, l) \<in> loc_rel, xs)) M_list"

definition
  "M1 = fold (\<lambda>p M.
    let
      s = fst p; xs = snd p;
      xs = rev (map g xs);
      S = set xs in fun_upd M s (Some S)
  ) (PR_CONST M_list1) IICF_Map.op_map_empty"

definition
  "M1i = hashmap_of_list (map (\<lambda>(k, dbms). (k, map h dbms)) M_list)"

context
  assumes M_list_covered: "fst ` set M_list \<subseteq> set L_list"
      and M_P: "list_all (\<lambda>(l, xs). list_all P xs) M_list"
    assumes g_h_param: "(h, g) \<in> {(x, y). x = y \<and> P x} \<rightarrow> R"
begin

lemma M1_finite:
  "\<forall>S\<in>ran M1. finite S"
  unfolding M1_def
  apply (rule fold_generalize_start[where P = "\<lambda>M. \<forall>S\<in>ran M. finite S"])
  subgoal for a
    unfolding M_list1_def
    apply (induction M_list arbitrary: a)
     apply (simp; fail)
    apply (simp, rprem, auto dest: ran_upd_cases)
    done
  apply (simp; fail)
  done

lemma P_loc1:
  "list_all
    (\<lambda>(l, xs). P_loc l \<and> states_mem_impl l \<and> list_all P xs) M_list"
  using P_loc \<open>_ \<subseteq> set L_list\<close> M_P unfolding list_all_iff by auto

lemma M_list_rel1:
  "(M_list, M_list1) \<in> \<langle>location_rel \<times>\<^sub>r \<langle>br id P\<rangle>list_rel\<rangle>list_rel"
  unfolding list_rel_def M_list1_def
  using P_loc1
  apply (clarsimp simp: list.pred_rel list.rel_map br_def)
  apply (elim list_all2_mono)
  apply (clarsimp simp: eq_onp_def)
  apply (meson someI_ex state_impl_abstract)
   apply (erule mem_states'I, meson someI_ex state_impl_abstract)
  apply (elim list_all2_mono, clarsimp)
  done

lemma dom_M_eq1_aux:
  "dom (fold (\<lambda>p M.
    let s = fst p; xs = snd p;
    xs = rev (map g xs); S = set xs in fun_upd M s (Some S)
  ) xs m) = dom m \<union> fst ` set xs" for xs m
    by (induction xs arbitrary: m) auto

lemma dom_M_eq1:
  "dom M1 = fst ` set M_list1"
  unfolding dom_M_eq1_aux M1_def by simp

lemma L_dom_M_eqI1:
  assumes "fst ` set M_list = set L_list"
  shows "set L = dom M1"
proof -
  show ?thesis
    unfolding dom_M_eq1
  proof (safe; clarsimp?)
    fix l assume "l \<in> set L"
    with L_list_rel assms obtain l' where "l' \<in> fst ` set M_list" "(l', l) \<in> location_rel"
      by (fastforce simp: list_all2_append2 list_all2_Cons2 list_rel_def elim!: in_set_list_format)
    with M_list_rel1 obtain l1 where "l1 \<in> fst ` set M_list1" "(l', l1) \<in> location_rel"
      by (fastforce simp: list_all2_append1 list_all2_Cons1 list_rel_def elim!: in_set_list_format)
    with \<open>(l', l) \<in> location_rel\<close> show "l \<in> fst ` set M_list1"
      using loc_rel_right_unique by auto
  next
    fix l M assume "(l, M) \<in> set M_list1"
    with M_list_rel1 assms obtain l' where "l' \<in> set L_list" "(l', l) \<in> location_rel"
      by (fastforce simp: list_all2_append2 list_all2_Cons2 list_rel_def elim!: in_set_list_format)
    with L_list_rel obtain l1 where "l1 \<in> set L" "(l', l1) \<in> location_rel"
      by (fastforce simp: list_all2_append1 list_all2_Cons1 list_rel_def elim!: in_set_list_format)
    with \<open>(l', l) \<in> location_rel\<close> show "l \<in> set L"
      using loc_rel_right_unique by auto
  qed
qed

lemma map_of_M_list_M_rel1:
  "(map_of_list (map (\<lambda>(k, dbms). (k, map h dbms)) M_list), M1)
\<in> location_rel \<rightarrow> \<langle>\<langle>R\<rangle>list_set_rel\<rangle>option_rel"
  unfolding M1_def M_list1_def
  unfolding map_of_list_def
  unfolding PR_CONST_def
proof goal_cases
  case 1
  let "(fold ?f ?xs Map.empty, fold ?g ?ys _) \<in> ?R" = ?case
  have *: "l' = (SOME l'. (l, l') \<in> loc_rel)"
    if "(l, l') \<in> loc_rel" "states_mem_impl l" "l' \<in> states'" for l l'
  proof -
    from that have "(l, SOME l'. (l, l') \<in> loc_rel) \<in> loc_rel"
      by (intro someI)
    moreover then have "(SOME l'. (l, l') \<in> loc_rel) \<in> states'"
      using that(2) by (elim mem_states'I)
    ultimately show ?thesis
      using that location_assn_constraints(3) unfolding single_valued_def by auto
  qed
  have "(fold ?f ?xs m, fold ?g ?ys m') \<in> ?R"
    if "(m, m') \<in> ?R" for m m'
    using that P_loc1
  proof (induction M_list arbitrary: m m')
    case Nil
    then show ?case
      by simp
  next
    case (Cons x M_list)
    obtain l M where "x = (l, M)"
      by force
    from Cons.IH \<open>list_all _ (x # M_list)\<close> show ?case
      apply (simp split:)
      apply rprems
      unfolding \<open>x = _\<close>
      apply simp
      apply (rule fun_relI)
      apply (clarsimp; safe)
      subgoal
        using g_h_param by (auto dest!: fun_relD intro!: map_set_rel)
      subgoal
        by (frule *) auto
      subgoal
        using location_assn_constraints(2) unfolding IS_LEFT_UNIQUE_def single_valued_def
        by (auto dest: someI_ex[OF state_impl_abstract])
      subgoal
        using Cons.prems(1)
        apply -
        apply (drule fun_relD)
        by simp
      done
  qed
  then show ?case
    by rprems auto
qed

lemma Mi_M1:
  "(\<lambda>k. Impl_Array_Hash_Map.ahm_lookup (=) bounded_hashcode_nat k M1i, M1)
  \<in> location_rel \<rightarrow> \<langle>\<langle>R\<rangle>list_set_rel\<rangle>option_rel"
(is "(?f, M1) \<in> ?R")
proof -
  let ?g = "map_of_list (map (\<lambda>(k, dbms). (k, map h dbms)) M_list)"
  have "(?f, ?g) \<in> Id \<rightarrow> \<langle>Id\<rangle>option_rel"
    unfolding M1i_def by (rule hashmap_of_list_lookup)
  moreover have "(?g, M1) \<in> ?R"
    by (rule map_of_M_list_M_rel1)
  ultimately show ?thesis
    by auto
qed

end (* Assumptions *)

end (* Defs *)

end

locale TA_Impl_Tab =
  TA_Impl_Loc_List where A = A and l\<^sub>0i = l\<^sub>0i
  for A :: "('a, nat, int, 's) ta" and l\<^sub>0i :: "'si:: {hashable,heap}" +
  fixes M_list :: "('si \<times> int DBMEntry list list) list"
  assumes M_list_covered: "fst ` set M_list \<subseteq> set L_list"
      and M_dbm_len: "list_all (\<lambda>(l, xs). list_all (\<lambda>M. length M = Suc n * Suc n) xs) M_list"
begin

lemmas M_assms = M_list_covered M_dbm_len IArray_list_to_dbm_rel

definition
  "M_list' \<equiv> M_list1 M_list"

definition
  "M = fold (\<lambda>p M.
    let s = fst p; xs = snd p; xs = rev (map (list_to_dbm n) xs); S = set xs in fun_upd M s (Some S)
  ) (PR_CONST M_list') IICF_Map.op_map_empty"

lemma M_alt_def:
  "M = M1 TYPE(int DBMEntry list) M_list (list_to_dbm n)"
  unfolding M_def M1_def M_list'_def ..

lemma M_finite:
  "\<forall>S\<in>ran M. finite S"
  unfolding M_alt_def by (rule M1_finite[OF M_assms])

lemmas M_list_rel = M_list_rel1[OF M_assms, folded M_list'_def]

lemma M_list_hnr[sepref_fr_rules]:
  "(uncurry0 (return M_list), uncurry0 (RETURN (PR_CONST M_list')))
    \<in> id_assn\<^sup>k \<rightarrow>\<^sub>a list_assn (
        location_assn \<times>\<^sub>a list_assn (pure (b_rel Id (\<lambda>xs. length xs = Suc n * Suc n))))"
proof -
  let ?R1 = "\<langle>br id (\<lambda>xs. length xs = Suc n * Suc n)\<rangle>list_rel"
  let ?R2 = "\<lambda>a c. \<up> (a = c \<and> length c = Suc (n + (n + n * n)))"
  let ?R = "(\<lambda>a c. \<up> ((c, a) \<in> loc_rel \<and> a \<in> states')) \<times>\<^sub>a list_assn ?R2"
  have "b_rel Id = br id"
    unfolding br_def b_rel_def by auto
  have *: "list_assn (\<lambda>a c. \<up> (a = c \<and> length c = Suc (n + (n + n * n)))) = pure ?R1"
    unfolding fcomp_norm_unfold by (simp add: pure_def br_def)
  have "?R = pure (location_rel \<times>\<^sub>r ?R1)"
    unfolding * pure_def prod_assn_def by (intro ext) auto
  then have **: "list_assn ?R = pure (\<langle>location_rel \<times>\<^sub>r ?R1\<rangle>list_rel)"
    unfolding fcomp_norm_unfold by simp (fo_rule HOL.arg_cong)
  have "emp \<Longrightarrow>\<^sub>A list_assn ?R M_list' M_list * true"
    using M_list_rel unfolding ** by (sep_auto simp: pure_def)
  then show ?thesis
    by sepref_to_hoare (sep_auto simp: lso_assn_def hr_comp_def br_def \<open>b_rel Id = br id\<close>)
qed

sepref_register "PR_CONST M_list'"

interpretation DBM_Impl n .

sepref_definition M_table is
  "uncurry0 (RETURN M)" :: "unit_assn\<^sup>k \<rightarrow>\<^sub>a hm.hms_assn' location_assn (lso_assn mtx_assn)"
  unfolding M_def set_of_list_def[symmetric] rev_map_fold
    HOL_list.fold_custom_empty hm.op_hms_empty_def[symmetric]
  by sepref

lemmas dom_M_eq = dom_M_eq1[OF M_assms, folded M_alt_def M_list'_def]

definition
  "Mi = hashmap_of_list (map (\<lambda>(k, dbms). (k, map IArray dbms)) M_list)"

lemma Mi_alt_def:
  "Mi = M1i TYPE(int DBMEntry list) M_list IArray"
  unfolding Mi_def M1i_def ..

lemmas map_of_M_list_M_rel = map_of_M_list_M_rel1[OF M_assms, folded M_alt_def]

lemmas Mi_M = Mi_M1[OF M_assms, folded M_alt_def Mi_alt_def]

lemmas L_dom_M_eqI = L_dom_M_eqI1[OF M_assms, folded M_alt_def]

end


subsection \<open>Deriving the Reachability Checker\<close>

locale TGA_Certify_Safe =
  TGA_Start_Impl where A = A and l\<^sub>0i = l\<^sub>0i +
  TA_Impl_Tab where A = A and l\<^sub>0i = l\<^sub>0i
  for A :: "('a, nat, int, 's) ta" and l\<^sub>0i :: "'si:: {hashable,heap}" +
  fixes Ki :: "'s \<times> int DBM' \<Rightarrow> bool"
  fixes K_impl
  assumes Ki_K: "(l, u) \<in> K \<Longrightarrow> u \<in> [curry (conv_M D)]\<^bsub>v,n\<^esub> \<Longrightarrow> wf_dbm D \<Longrightarrow> Ki (l, D)"
  assumes Ki_mono:
    "Ki (l, D) \<Longrightarrow> wf_dbm D \<Longrightarrow> wf_dbm D' \<Longrightarrow> dbm_subset n D D' \<Longrightarrow> Ki (l, D')"
  assumes K_impl_refine:
    "(K_impl, (RETURN \<circ>\<circ> PR_CONST) Ki) \<in> (location_assn \<times>\<^sub>a mtx_assn n)\<^sup>d \<rightarrow>\<^sub>a bool_assn"
begin

interpretation DBM_Impl n .

interpretation legacy: TA_Impl_Op where f = undefined and op_impl = undefined
  apply standard
  sorry

definition "subsumption \<equiv> \<lambda>(x :: int DBM') S. \<exists>y \<in> S. dbm_subset n x y"

sepref_register dbm_subset :: "nat \<Rightarrow> 'free DBMEntry i_mtx \<Rightarrow> 'free DBMEntry i_mtx \<Rightarrow> bool"

lemma aux4:
  "ID D x'a TYPE((nat \<times> nat \<Rightarrow> int DBMEntry) set) = ID D x'a TYPE((int DBMEntry i_mtx) set)"
  by simp

sepref_definition subsumption_impl is
  "uncurry (RETURN oo subsumption)"
  :: "mtx_assn\<^sup>k *\<^sub>a (lso_assn mtx_assn)\<^sup>k
      \<rightarrow>\<^sub>a bool_assn"
  unfolding subsumption_def IICF_List_SetO.fold_lso_bex
  thm fold_set_member_bex
  apply sepref_dbg_keep
     apply sepref_dbg_id_keep
  unfolding aux4[symmetric]
      apply sepref_dbg_id_step+
     apply sepref_dbg_monadify
     apply sepref_dbg_opt_init
      apply sepref_dbg_trans_keep
     apply sepref_dbg_opt
    apply sepref_dbg_cons_solve
   apply sepref_dbg_cons_solve
  apply sepref_dbg_constraints
  done

lemma strategy_split_preserves_wf_dbm:
  fixes M
  assumes "(M\<^sub>s, C) \<in> set (S (l, M))" "wf_dbm M"
  shows "wf_dbm M\<^sub>s"
  using strategy_split_preserves_wf_state[OF assms(1)] assms(2) by (auto simp: wf_state_def)

lemma S_dbm_mono':
  fixes M
  assumes "(M\<^sub>s, C) \<in> set (S (l, M))"
    and "wf_dbm M"
    and "wf_dbm M'"
    and "dbm_subset n M M'"
  shows "\<exists>M\<^sub>s' C'. (M\<^sub>s', C') \<in> set (S (l, M')) \<and> dbm_subset n M\<^sub>s M\<^sub>s' \<and> C \<subseteq> C'"
  using S_dbm_mono strategy_split_preserves_wf_dbm dbm_subset_correct'' assms
  by (meson dbm_subset_conv dbm_subset_conv_rev)

lemma E_from_op_empty_mono':
  fixes M
  assumes "step_impl (l, D) (l', D')"
    and "wf_dbm D"
    and "wf_dbm M"
    and "dbm_subset n D M"
  shows "\<exists>M'. step_impl (l, M) (l', M') \<and> dbm_subset n D' M'"
  using assms(1)
proof cases
  case (action M\<^sub>s a C)
  from \<open>(M\<^sub>s, C) \<in> set (S (l, D))\<close> \<open>dbm_subset n D M\<close> obtain M\<^sub>s' C' where
    "(M\<^sub>s', C') \<in> set (S (l, M))" "dbm_subset n M\<^sub>s M\<^sub>s'" "C \<subseteq> C'"
    using S_dbm_mono' \<open>wf_dbm D\<close> \<open>wf_dbm M\<close> by fast
  with action \<open>wf_dbm D\<close> \<open>wf_dbm M\<close> show ?thesis
    by - (drule op_precise.E_from_op_empty_mono'[where M = M\<^sub>s'],
          auto intro!: step_impl.action intro: strategy_split_preserves_wf_dbm)
next
  case (wait M\<^sub>s C)
  from \<open>(M\<^sub>s, C) \<in> set (S (l, D))\<close> \<open>dbm_subset n D M\<close> obtain M\<^sub>s' C' where
    "(M\<^sub>s', C') \<in> set (S (l, M))" "dbm_subset n M\<^sub>s M\<^sub>s'" "C \<subseteq> C'"
    using S_dbm_mono' \<open>wf_dbm D\<close> \<open>wf_dbm M\<close> by fast
  with wait \<open>wf_dbm D\<close> \<open>wf_dbm M\<close> show ?thesis
    by - (drule op_precise.E_from_op_empty_mono'[where M = M\<^sub>s'],
          auto intro!: step_impl.wait intro: strategy_split_preserves_wf_dbm)
next
  case (uncontrolled a)
  then show ?thesis
    by (meson assms(2-4) step_impl.uncontrolled op_precise.E_from_op_empty_mono')
qed

lemma step_impl_mono:
  assumes 
    "subsumption s S'" and
    "step_impl (l, s) (l', t)" and
    "Ball S' wf_dbm" and
    \<^cancel>\<open>"l \<in> states'" and\<close>
    "wf_dbm s"
  shows "\<exists>T. subsumption t T \<and> (\<forall>t'\<in>T. \<exists>s'\<in>S'. step_impl (l, s') (l', t'))"
  using assms unfolding subsumption_def by (auto 4 3 dest: E_from_op_empty_mono')

interpretation reach:
  Reachability_Impl
  where A = mtx_assn
    and F = Ki
    and l\<^sub>0i = "return l\<^sub>0i"
    and s\<^sub>0 = init_dbm
    and s\<^sub>0i = legacy.init_dbm_impl
    and succs = succs_precise
    and succsi = succs_precise'_impl
    and less_eq = subsumption
    and Lei = subsumption_impl
    and E = step_impl
    and Fi = K_impl
    and K = location_assn
    and keyi = "return o fst"
    and copyi = amtx_copy
    and P = "\<lambda>(l, M). l \<in> states' \<and> wf_dbm M"
    and P' = P
    and Pi = P_impl
    and L = "set L"
    and M = M
  apply standard
  subgoal (* L finite *)
    ..
  subgoal (* M finite *)
    by (rule M_finite)
  subgoal (* succs finite *)
    by (rule succs_precise_finite)
  subgoal (* succs empty *)
    unfolding succs_precise_def by auto
  subgoal (* succs correct *)
    unfolding succs_precise_def
    supply E_def = op_precise.E_from_op_empty_def op_precise.E_from_op_def
    apply (clarsimp, safe)

    subgoal premises prems for x D D\<^sub>s C \<comment> \<open>\<longrightarrow> wait\<close>
      using prems by (auto 4 3 intro: step_impl.wait simp: E_def)

    subgoal premises prems for x aa ab ac ba D D\<^sub>s C \<comment> \<open>\<longrightarrow> action\<close>
      using prems by (fastforce intro: step_impl.action simp: E_def)
  
    subgoal premises prems for x aa ab ac ba D \<comment> \<open>\<longrightarrow> uncontrolled\<close>
      using prems by (fastforce intro: step_impl.uncontrolled simp: E_def)

    subgoal premises prems for x a b s \<comment> \<open>\<longleftarrow>\<close>
      using prems apply -
      apply (elim step_impl.cases)
        apply (auto dest!: legacy.trans_of_trans_impl simp: E_def)
      apply blast
      by (metis (mono_tags, lifting) mem_Collect_eq)
      done
  subgoal (* P correct *)
    by (auto dest: P_correct)
  subgoal (* key refine *)
    by sepref_to_hoare sep_auto
  apply (rule amtx_copy_hnr; fail) (* COPY implementation for dbms *)
  subgoal (* P refine *)
    by (rule P_impl_refine)
  subgoal (* F refine *)
    by (rule K_impl_refine)
  subgoal (* succs refine *)
    using succs_precise_impl_refine unfolding b_assn_pure_conv .
  apply (rule location_assn_constraints; fail)+ (* location assn is correct *)
  subgoal (* init loc refine *)
    using init_impl states'_states by sepref_to_hoare sep_auto
  (* init dbm refine *)
         apply (unfold PR_CONST_def, rule legacy.init_dbm_impl.refine; fail)
  (* dbm subset relation is an ordering *)
  \<^cancel>\<open>apply (rule HOL.refl; fail)
  apply (rule dbm_subset_refl; fail)
  apply (rule dbm_subset_trans; assumption)\<close>
  subgoal (* F mono *)
    \<comment> \<open>XXX Move lemmas about \<^term>\<open>project\<close>\<close>
    unfolding subsumption_def project_def by (auto dest: Ki_mono)
  subgoal for s S' l l' t (* E_precise mono *)
    using step_impl_mono by auto
  subgoal (* E_precise invariant *)
    by (elim step_impl.cases;
        clarsimp simp: op_precise.E_from_op_empty_def,
        frule op_precise.E_from_op_wf_state[rotated],
        auto dest: E_from_op_states simp: wf_state_def intro: strategy_split_preserves_wf_dbm)
  subgoal for a A A' (* federation subsumption property *)
    unfolding subsumption_def by (blast intro: dbm_subset_trans)
  subgoal (* subsumption implementation *)
    \<^cancel>\<open>apply (rule hfrefI)
    using lso_bex_impl.refine\<close>
    using subsumption_impl.refine unfolding PR_CONST_def .
  done

lemmas reachability_impl = reach.Reachability_Impl_axioms

context
  fixes Li_split :: "'si list list"
  assumes full_split: "set L_list = (\<Union>xs \<in> set Li_split. set xs)"
begin

\<comment> \<open>This would probably need to be an assumption for a relaxed subsumption operation.\<close>
lemma M_l\<^sub>0_not_None:
  "subsumption s\<^sub>0 {} \<Longrightarrow> M l\<^sub>0 \<noteq> None"
  unfolding subsumption_def by auto

\<comment> \<open>XXX Move\<close>
definition
  "dbm_subset_pure \<equiv> \<lambda>as bs.
      (\<exists>i\<le>n. IArray.sub as (i + i * n + i) < Le 0) \<or> array_all2 (Suc n * Suc n) (\<le>) as bs"

definition "subsumption_pure \<equiv> \<lambda>(x :: int DBMEntry iarray) S. \<exists>y \<in> set S. dbm_subset_pure x y"

\<comment> \<open>XXX Move\<close>
lemma dbm_subset_pure_refine:
  "(dbm_subset_pure, dbm_subset n)
    \<in> {(a, b). iarray_mtx_rel (Suc n) (Suc n) b a} \<rightarrow>
       {(a, b). iarray_mtx_rel (Suc n) (Suc n) b a} \<rightarrow> bool_rel"
  unfolding dbm_subset_pure_def dbm_subset_def check_diag_def
  by (auto simp: array_all2_iff_pointwise_cmp[symmetric] iarray_mtx_relD)

\<comment> \<open>XXX Move\<close>
lemma list_set_rel_set_rel:
  "(set xs, T) \<in> \<langle>R\<rangle>set_rel" if "(xs, T) \<in> \<langle>R\<rangle>list_set_rel"
  using that unfolding list_set_rel_def set_rel_def
  by clarsimp (meson list_rel_setE1 list_rel_setE2)

lemma subsumption_pure_refine:
  "(subsumption_pure, subsumption)
    \<in> {(a, b). iarray_mtx_rel (Suc n) (Suc n) b a} \<rightarrow>
       \<langle>{(a, b). iarray_mtx_rel (Suc n) (Suc n) b a}\<rangle>list_set_rel \<rightarrow> bool_rel"
  unfolding subsumption_pure_def subsumption_def
  supply [param] = dbm_subset_pure_refine
  by parametricity (rule list_set_rel_set_rel)

interpretation Reachability_Impl_imp_to_pure_correct
  where A = mtx_assn
    and F = Ki
    and l\<^sub>0i = "return l\<^sub>0i"
    and s\<^sub>0 = init_dbm
    and s\<^sub>0i = legacy.init_dbm_impl
    and succs = succs_precise
    and succsi = succs_precise'_impl
    and less_eq = subsumption
    and Lei = subsumption_impl
    \<^cancel>\<open>and lei = "\<lambda>as bs.
      (\<exists>i\<le>n. IArray.sub as (i + i * n + i) < Le 0) \<or> array_all2 (Suc n * Suc n) (\<le>) as bs"\<close>
    and lei = subsumption_pure
    and E = step_impl
    and Fi = K_impl
    and K = location_assn
    and keyi = "return o fst"
    and copyi = amtx_copy
    and P = "\<lambda>(l, M). l \<in> states' \<and> wf_dbm M"
    and P' = P
    and Pi = P_impl
    and L = "set L"
    and M = M
    and to_loc = id
    and from_loc = id
    and L_list = L_list
    and K_rel = location_rel
    and L' = L
    and Li = L_list
    and to_state = array_unfreeze
    and from_state = array_freeze
    and A_rel = "{(a, b). iarray_mtx_rel (Suc n) (Suc n) b a}"
    and Mi = "\<lambda>k. Impl_Array_Hash_Map.ahm_lookup (=) bounded_hashcode_nat k Mi"
    and nonempty = "\<lambda>D. \<not> check_diag n D" \<comment> \<open>This would also work: \<^term>\<open>\<lambda>_. True\<close>.\<close>
  apply standard
  subgoal
    using L_list_rel by simp
  subgoal
    by (rule L_list_rel)
  subgoal
    ..
  subgoal for s1 s
    by (rule array_unfreeze_ht) simp
  subgoal for si s
    by (sep_auto heap: array_freeze_ht)
  subgoal
    by simp
  subgoal
    by simp
  subgoal
    by (rule legacy.right_unique_location_rel) \<comment> \<open>Also in @{thm location_assn_constraints}.\<close>
  subgoal
    using legacy.left_unique_location_rel unfolding IS_LEFT_UNIQUE_def .
  subgoal
    by (rule subsumption_pure_refine)
  subgoal
    using full_split .
  subgoal
    using Mi_M .
  \<comment> \<open>Properties of \<open>nonempty\<close>\<close>
  subgoal premises prems for x
    using prems unfolding subsumption_def by auto
  subgoal premises prems for l' S' l Sa x
    using prems unfolding succs_precise_def by (auto split: if_split_asm)
  by (rule M_l\<^sub>0_not_None)

concrete_definition certify_unreachable_pure
  uses pure.certify_unreachable_impl_pure_correct[unfolded to_pair_def get_succs_def] is "?f \<longrightarrow> _"

lemma certify_unreachable_pure_refine:
  assumes "fst ` set M_list = set L_list" certify_unreachable_pure
  shows "\<forall>u\<^sub>0. (\<forall>c\<le>n. u\<^sub>0 c = 0) \<longrightarrow> sem.safe_from (l\<^sub>0, u\<^sub>0)"
  using certify_unreachable_pure.refine[OF L_dom_M_eqI] assms
  by (auto simp: init_dbm_semantics intro!: safe_fromI[where D\<^sub>0 = init_dbm])
  \<comment> \<open>XXX Move @{thm reach.in_from_R_conv}\<close>
     (drule Ki_K, auto simp: wf_state_def reach.in_from_R_conv
        dest: sem_impl_simulation.PB_invariant.invariant_reaches)

end (* Fixed splitter *)

end

end