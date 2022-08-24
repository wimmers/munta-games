theory Normalized_Zone_Semantics_Certification_Impl2
  \<comment> \<open>This name is already duplicated but has nothing to do with that other theory.\<close>  
  imports
    \<^cancel>\<open>TA_Impl.Normalized_Zone_Semantics_Impl_Refine
    Normalized_Zone_Semantics_Certification
    Collections.Refine_Dflt_ICF
    Certification.Unreachability_Certification2
    Certification.Unreachability_Certification
    "HOL-Library.IArray"
    Deadlock.Deadlock_Impl
    TA_Library.More_Methods
    "HOL-Library.Rewrite"\<close>
    Safety_Certification_Pure
    Timed_Game_Certification_Impl
    Normalized_Zone_Semantics_Certification2
    Certification.Normalized_Zone_Semantics_Certification_Impl_Misc
    TA_Library.Reordering_Quantifiers
    \<^cancel>\<open>Certification.Normalized_Zone_Semantics_Certification_Impl\<close> \<comment> \<open>We will duplicate this stuff\<close>
    \<comment> \<open>Need to rename local copy of Normalized_Zone_Semantics_Certification\<close>
begin

term x

paragraph \<open>Misc refinement setup\<close>

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

context TA_Start_Defs
begin

end

context TA_Impl_Ext
begin

term step_impl_precise

end

context TA_Impl_Precise
begin

end


subsection \<open>Duplication\<close>

hide_const (open) Simulation_Graphs_Certification.C

paragraph \<open>Successor Implementation\<close>
context TGA_Start_Defs
begin

\<^cancel>\<open>lemma E_precise_E_op:
  "E_precise = (\<lambda>(l, M) a (l', M'''). \<exists>g r. A \<turnstile> l \<longrightarrow>\<^bsup>g,a,r\<^esup> l' \<and> M''' = E_precise_op l r g l' M)"
  unfolding E_precise_op_def E_precise_def by (intro ext) (auto elim!: step_impl.cases)\<close>

term "op_precise.E_from_op = (\<lambda> (l, M) a (l', M'). case a of
  \<tau> \<Rightarrow> l' = l \<and> M' = del l M
  | \<upharpoonleft>a \<Rightarrow> \<exists> g r. A \<turnstile> l \<longrightarrow>\<^bsup>g,a,r\<^esup> l' \<and> M' = act l r g l' M)"

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
  \<^cancel>\<open>apply (refine_vcg nfoldli_rule[where
        I = "\<lambda>l1 l2 \<sigma>. \<sigma> = rev (concat [[act l r g l' D\<^sub>s.
        (D\<^sub>s, C) \<leftarrow> S (l, D), Act a \<in> C, \<not> check_diag n (act l r g l' D\<^sub>s)
       ]. D \<leftarrow> l1])"
     ])\<close>
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

lemma list_comprehension_filter:
  "[x. x \<leftarrow> xs, P x] = filter P xs"
  by (induction xs; simp)

lemma list_comprehension_map_filter:
  "[f x. x \<leftarrow> xs, P x] = map f (filter P xs)"
  by (induction xs; simp)

lemma case_prod_if:
  "(\<lambda>(a, b). if P a b then f a b else g a b) =
   (\<lambda>x.
      if (case x of (a, b) \<Rightarrow> P a b) then (case x of (a, b) \<Rightarrow> f a b) else (case x of (a, b) \<Rightarrow> g a b))"
  by auto

lemma case_prod_singleton:
  "(\<lambda>(a, b). [f a b]) = (\<lambda>x. [case x of (a, b) \<Rightarrow> f a b])"
  by auto

term apply_if

thm fold_filter

lemma fold_append_meld':
  "fold (\<lambda>x. apply_if (P x) ((#) (f x))) xs (acc1 @ acc2) = fold (\<lambda>x. apply_if (P x) ((#) (f x))) xs acc1 @ acc2"
  by (induction xs arbitrary: acc1; simp) (metis (no_types, lifting) append_Cons)
thm fold_append_meld'
lemmas fold_append_meld = fold_append_meld'[of _ _ _ "[]", simplified, symmetric]

lemma succs_precise_alt_def:
  "succs_precise \<equiv> \<lambda>l T.
    if T = {} then []
    else rev (map (\<lambda>(g,a,r,l').
      (l', {D' | D' D D\<^sub>s C.
        D \<in> T \<and> (D\<^sub>s, C) \<in> set (S (l, D)) \<and> Act a \<in> C \<and> D' = act l r g l' D\<^sub>s \<and> \<not> check_diag n D'
       }))
      (filter (\<lambda>(g,a,r,l'). controllable a) (trans_fun l))
    )
    @ rev (map (\<lambda>(g,a,r,l').
      (l', {D' | D' D. D \<in> T \<and> D' = act l r g l' D \<and> \<not> check_diag n D'})
    ) (filter (\<lambda>(g,a,r,l'). \<not> controllable a) (trans_fun l)))
    @ [
      (l, {D' | D' D D\<^sub>s C.
        D \<in> T \<and> (D\<^sub>s, C) \<in> set (S (l, D)) \<and> Wait \<in> C \<and> D' = del l D\<^sub>s \<and> \<not> check_diag n D'
      })
    ]"
  unfolding succs_precise_def list_comprehension_map_filter[symmetric] apply (rule eq_reflection)
  apply (intro ext)
  apply (simp cong: concat_cong map_cong)
  apply simp
  apply (rule impI)
  apply (rule arg_cong[where f = concat])
  apply (rule arg_cong2[where f = map])
  unfolding case_prod_if case_prod_singleton
  apply (simp cong: if_cong)
  apply (rule arg_cong[where f = concat])
  apply (rule arg_cong2[where f = map])
   apply auto
  done
  apply rule
   apply (rule ext)
   apply (rule if_cong)
     apply rule
    apply (rule )
  apply simp
  apply (simp cong: list.map_cong_simp)
  apply (subst case_prod_if)
  apply auto
  done

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

context
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

end (* Anonymous context *)

end (* TA Impl Precise *)


paragraph \<open>A new implementation invariant for DBMs\<close>
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

lemmas [safe_constraint_rules] = location_assn_constraints

end (* TA Impl Precise *)

paragraph \<open>Deriving the Main Simulation Theorems\<close>

\<comment> \<open>Insert stuff we already have.\<close>

end