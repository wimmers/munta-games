theory Normalized_Zone_Semantics_Certification2
  imports TA_Impl.Normalized_Zone_Semantics_Impl_Semantic_Refinement Labeled_Graphs
begin

text \<open>Notes:
\<^item> We already have two variants of this theory
  \<^theory>\<open>TA_Impl.Normalized_Zone_Semantics_Impl_Semantic_Refinement\<close>,
  and \<open>Certification.Normalized_Zone_Semantics_Impl_Semantic_Refinement\<close>
\<^item> They gradually refine the same techniques and theorems because we need to implement finer steps
\<^item> The latter could definitely be derived from this theory by proving theorems for coupled steps
\<^item> The first adds normalization in the last step. Could this be another coupling step?
\<^item> \<open>E_combined_op\<close> is what is \<open>E_precise_op\<close> in
  \<open>Certification.Normalized_Zone_Semantics_Impl_Semantic_Refinement\<close>
\<close>

no_notation TA_Start_Defs.step_impl' ("\<langle>_, _\<rangle> \<leadsto>\<^bsub>_\<^esub> \<langle>_, _\<rangle>" [61,61,61] 61)

context TA_Start_Defs
begin

definition
  "E_del_op l M \<equiv>
    FW' (abstr_upd (inv_of A l) (up_canonical_upd M n)) n"

definition
  "E_del_op' l M \<equiv>
    abstr_repair (inv_of A l) (up_canonical_upd M n)"

definition
  "E_act_op l r g l' M \<equiv>
    FW' (abstr_upd (inv_of A l') (reset'_upd (FW' (abstr_upd g M) n) n r 0)) n"

definition
  "E_act_op' l r g l' M \<equiv>
    let
      M1 = filter_diag (\<lambda> M. abstr_repair g M) M;
      M2 = filter_diag (\<lambda> M. abstr_repair (inv_of A l') (reset'_upd M n r 0)) M1
    in M2"

definition
  "E_combined_op l r g l' M \<equiv>
    let
      M' = FW' (abstr_upd (inv_of A l) (up_canonical_upd M n)) n;
      M'' = FW' (abstr_upd (inv_of A l') (reset'_upd (FW' (abstr_upd g M') n) n r 0)) n
    in M''"

lemma E_combined_op_decomp:
  "E_combined_op l r g l' M \<equiv>
    let
      M' = E_del_op l M;
      M'' = E_act_op l r g l' M'
    in M''"
  unfolding E_combined_op_def E_del_op_def E_act_op_def .

definition
  "E_combined_op' l r g l' M \<equiv>
    let
      M1 = abstr_repair (inv_of A l) (up_canonical_upd M n);
      M2 = filter_diag (\<lambda> M. abstr_repair g M) M1;
      M3 = filter_diag (\<lambda> M. abstr_repair (inv_of A l') (reset'_upd M n r 0)) M2
    in M3"

lemma E_combined_op'_alt_def:
  "E_combined_op' l r g l' M \<equiv>
    let
      M' = abstr_repair (inv_of A l) (up_canonical_upd M n);
      f1 = \<lambda> M. abstr_repair g M;
      f2 = \<lambda> M. abstr_repair (inv_of A l') (reset'_upd M n r 0)
    in filter_diag (filter_diag f2 o f1) M'"
  unfolding E_combined_op'_def filter_diag_def
  by (rule HOL.eq_reflection) (auto simp: Let_def check_diag_marker)

lemma E_combined_op'_decomp:
  "E_combined_op' l r g l' M \<equiv>
    let
      M' = E_del_op' l M;
      M'' = E_act_op' l r g l' M'
    in M''"
  unfolding E_combined_op'_def E_del_op'_def E_act_op'_def unfolding Let_def .

no_notation step_impl' ("\<langle>_, _\<rangle> \<leadsto>\<^bsub>_\<^esub> \<langle>_, _\<rangle>" [61,61,61] 61)

abbreviation step_impl_precise' ("\<langle>_, _\<rangle> \<leadsto>\<^bsub>_\<^esub> \<langle>_, _\<rangle>" [61,61,61] 61)
where
  "\<langle>l, Z\<rangle> \<leadsto>\<^bsub>a\<^esub> \<langle>l'', Z''\<rangle> \<equiv> \<exists> l' Z'.
    A \<turnstile>\<^sub>I \<langle>l, Z\<rangle> \<leadsto>\<^bsub>n,\<tau>\<^esub> \<langle>l', Z'\<rangle> \<and> A \<turnstile>\<^sub>I \<langle>l', Z'\<rangle> \<leadsto>\<^bsub>n,\<upharpoonleft>a\<^esub> \<langle>l'', Z''\<rangle>"

(* sublocale Graph_Defs "\<lambda> (l, u) (l', u'). conv_A A \<turnstile>' \<langle>l, u\<rangle> \<rightarrow> \<langle>l', u'\<rangle>" . *)

definition "E_combined \<equiv> (\<lambda>(l, Z) (l'', Z''). \<exists>a. \<langle>l, Z\<rangle> \<leadsto>\<^bsub>a\<^esub> \<langle>l'', Z''\<rangle>)"

definition "E_precise \<equiv> (\<lambda>(l, Z) a (l', Z'). A \<turnstile>\<^sub>I \<langle>l, Z\<rangle> \<leadsto>\<^bsub>n,a\<^esub> \<langle>l', Z'\<rangle>)"

end

lemma (in TA_Start) E_precise_equiv:
  "\<exists> b'. E_precise b action b' \<and> a' \<sim> b'"
  if "E_precise a action a'" "a \<sim> b" "wf_state a" "wf_state b"
  using that
  unfolding wf_state_def E_precise_def
  apply safe
  apply (frule step_impl_equiv, assumption, assumption, rule state_equiv_D, assumption)
  by (safe, drule step_impl_equiv, auto intro: step_impl_wf_dbm simp: state_equiv_def)


locale E_From_Op_Defs = TA_Start_Defs _ l\<^sub>0 for l\<^sub>0 :: "'s" +
  fixes del :: "'s \<Rightarrow> (nat \<times> nat \<Rightarrow> int DBMEntry) \<Rightarrow> nat \<times> nat \<Rightarrow> int DBMEntry"
  fixes act :: "'s
   \<Rightarrow> nat list
      \<Rightarrow> (nat, int) acconstraint list
         \<Rightarrow> 's
            \<Rightarrow> (nat \<times> nat \<Rightarrow> int DBMEntry)
               \<Rightarrow> nat \<times> nat \<Rightarrow> int DBMEntry"
begin

definition "E_from_op = (\<lambda> (l, M) a (l', M'). case a of
  \<tau> \<Rightarrow> l' = l \<and> M' = del l M
  | \<upharpoonleft>a \<Rightarrow> \<exists> g r. A \<turnstile> l \<longrightarrow>\<^bsup>g,a,r\<^esup> l' \<and> M' = act l r g l' M)"

end


locale E_From_Op = TA_Start + E_From_Op_Defs

locale E_Precise_Bisim = E_From_Op +
  assumes del_bisim:
    "wf_dbm M \<Longrightarrow> del l M \<simeq> E_del_op l M"
    and act_bisim:
    "A \<turnstile> l \<longrightarrow>\<^bsup>g,a,r\<^esup> l' \<Longrightarrow> wf_dbm M \<Longrightarrow> act l r g l' M \<simeq> E_act_op l r g l' M"
    and del_wf:
    "wf_dbm M \<Longrightarrow> wf_dbm (del l M)"
    and act_wf:
    "A \<turnstile> l \<longrightarrow>\<^bsup>g,a,r\<^esup> l' \<Longrightarrow> wf_dbm M \<Longrightarrow> wf_dbm (act l r g l' M)"
begin

lemma step_impl_E_del_op:
  "A \<turnstile>\<^sub>I \<langle>l, Z\<rangle> \<leadsto>\<^bsub>n,\<tau>\<^esub> \<langle>l', Z'\<rangle> \<longleftrightarrow> l' = l \<and> Z' = E_del_op l Z"
  unfolding E_del_op_def by (auto elim!: step_impl.cases)

lemma step_impl_E_act_op:
  "A \<turnstile>\<^sub>I \<langle>l, Z\<rangle> \<leadsto>\<^bsub>n,\<upharpoonleft>a\<^esub> \<langle>l', Z'\<rangle> \<longleftrightarrow> (\<exists>g r. A \<turnstile> l \<longrightarrow>\<^bsup>g,a,r\<^esup> l' \<and> Z' = E_act_op l r g l' Z)"
  unfolding E_act_op_def by (auto elim!: step_impl.cases)

term "valid_dbm (curry (conv_M D))" term "dbm_int M n"
term E_From_Op_Defs.E_from_op
thm E_From_Op_Defs.E_from_op_def
\<^cancel>\<open>definition
  "E_precise_op = E_From_Op_Defs.E_from_op A E_del_op E_act_op"\<close>

lemma E_precise_alt_def:
  "E_precise = E_From_Op_Defs.E_from_op A E_del_op E_act_op"
  unfolding E_precise_def E_From_Op_Defs.E_from_op_def
  by (intro ext)
     (auto split: prod.splits action.split simp: simp: step_impl_E_del_op step_impl_E_act_op)

\<^cancel>\<open>lemma E_precise_E_op:
  "E_precise = (\<lambda>(l, M) a (l', M'''). \<exists>g a r. A \<turnstile> l \<longrightarrow>\<^bsup>g,a,r\<^esup> l' \<and> M''' = E_from_op l r g l' M)"
  unfolding E_precise_op_def E_precise_def by (intro ext) (auto elim!: step_impl.cases)
\<close>
\<^cancel>\<open>lemma E_precise_E_op:
  "E_precise = (\<lambda>(l, M) (l', M'''). \<exists>g a r. A \<turnstile> l \<longrightarrow>\<^bsup>g,a,r\<^esup> l' \<and> M''' = E_precise_op l r g l' M)"
  unfolding E_precise_op_def E_precise_def by (intro ext) (auto elim!: step_impl.cases)\<close>

lemma E_E_from_op_step:
  "\<exists>c. E_from_op a action c \<and> b \<sim> c" if "E_precise a action b" "wf_state a"
  using that unfolding E_precise_alt_def E_From_Op_Defs.E_from_op_def wf_state_def state_equiv_def
  by (cases action) (auto 4 4 intro!: del_bisim[THEN dbm_equiv_sym] act_bisim[THEN dbm_equiv_sym])

lemma E_from_op_E_step:
  "\<exists>c. E_precise a action c \<and> b \<sim> c" if "E_from_op a action b" "wf_state a"
  using that unfolding E_precise_alt_def E_From_Op_Defs.E_from_op_def wf_state_def state_equiv_def
  by (cases action) (auto 4 4 intro!: del_bisim act_bisim)

lemma E_from_op_wf_state:
  "wf_state b" if "wf_state a" "E_from_op a action b"
  using that unfolding E_E_op E_from_op_def wf_state_def state_equiv_def
  by (cases action) (auto 4 4 intro: del_wf act_wf)

lemma E_precise_wf_dbm[intro]:
  "wf_dbm D'" if "E_precise (l, D) action (l', D')" "wf_dbm D"
  using that unfolding wf_state_def E_def E_precise_def by (auto intro: step_impl_wf_dbm)

lemma E_precise_wf_state:
  "wf_state a \<Longrightarrow> E_precise a action b \<Longrightarrow> wf_state b"
  unfolding wf_state_def by auto

lemma E_from_op_bisim:
  "Bisimulation_Invariant E_precise E_from_op (\<sim>) wf_state wf_state"
  apply standard
  subgoal for action a b a'
    by (drule E_precise_equiv, assumption+) (auto dest!: E_E_from_op_step)
  subgoal
    by (drule (1) E_from_op_E_step, safe, drule E_precise_equiv) (auto 4 4 intro: state_equiv_sym)
   apply (rule E_precise_wf_state; assumption)
  apply (rule E_from_op_wf_state; assumption)
  done

(* lemma E_E_from_op_steps_empty:
  "(\<exists>l' M'. E_precise\<^sup>*\<^sup>* a\<^sub>0 (l', M') \<and> [curry (conv_M M')]\<^bsub>v,n\<^esub> = {}) \<longleftrightarrow>
   (\<exists>l' M'. E_from_op\<^sup>*\<^sup>* a\<^sub>0 (l', M') \<and> [curry (conv_M M')]\<^bsub>v,n\<^esub> = {})"
  by (rule E_E\<^sub>1_steps_empty[OF E_E_from_op_step E_from_op_E_step E_from_op_wf_state]) *)

\<^cancel>\<open>theorem E_from_op_reachability_check:
  "(\<exists> l' D'. E_precise\<^sup>*\<^sup>* a\<^sub>0 (l', D') \<and> F_rel (l', D'))
  \<longleftrightarrow> (\<exists> l' D'. E_from_op\<^sup>*\<^sup>* a\<^sub>0 (l', D') \<and> F_rel (l', D'))"
  oops\<close>
(*   apply (rule E_E\<^sub>1_steps_equiv[OF E_E_from_op_step E_from_op_E_step E_from_op_wf_state])
  by
    (auto
      simp: F_rel_def state_equiv_def wf_state_def dbm_equiv_def
      dest!:
        check_diag_empty_spec[OF check_diag_conv_M]
        canonical_check_diag_empty_iff[OF wf_dbm_altD(1)]
    ) *)

\<^cancel>\<open>lemma E_from_op_mono:
  assumes "E_from_op (l,D) (l',D')"
    and   "wf_dbm D" "wf_dbm M"
    and "[curry (conv_M D)]\<^bsub>v,n\<^esub> \<subseteq> [curry (conv_M M)]\<^bsub>v,n\<^esub>"
  shows "\<exists> M'. E_from_op (l,M) (l',M') \<and> [curry (conv_M D')]\<^bsub>v,n\<^esub> \<subseteq> [curry (conv_M M')]\<^bsub>v,n\<^esub>"
  (* using assms by - (rule E\<^sub>1_mono[OF E_E_from_op_step E_from_op_E_step E_from_op_wf_state]; blast) *)
  oops

lemma E_from_op_mono':
  assumes "E_from_op (l,D) (l',D')"
    and   "wf_dbm D" "wf_dbm M"
    and "dbm_subset n D M"
  shows "\<exists> M'. E_from_op (l,M) (l',M') \<and> dbm_subset n D' M'"
  (* using assms by - (rule E\<^sub>1_mono'[OF E_E_from_op_step E_from_op_E_step E_from_op_wf_state]; blast) *)
  oops

  thm E_E_from_op_step E_from_op_E_step E_from_op_wf_state

lemma E_equiv:
  "\<exists> b'. E_precise b b' \<and> a' \<sim> b'" if "E_precise a a'" "a \<sim> b" "wf_state a" "wf_state b"
  using that
  unfolding wf_state_def E_precise_def
  apply safe
  apply (frule step_impl_equiv, assumption, assumption, rule state_equiv_D, assumption)
  by (safe, drule step_impl_equiv, auto intro: step_impl_wf_dbm simp: state_equiv_def)

lemma E_from_op_bisim:
  "Bisimulation_Invariant E_precise E_from_op (\<sim>) wf_state wf_state"
  apply standard
  subgoal
    by (drule E_equiv, assumption+) (auto dest!: E_E_from_op_step)
  subgoal
    by (drule (1) E_from_op_E_step, safe, drule E_equiv) (auto 4 4 intro: state_equiv_sym)
   apply (rule E_precise_wf_state; assumption)
  apply (rule E_from_op_wf_state; assumption)
  done\<close>

lemma E_from_op_bisim_empty:
  "Bisimulation_Invariant
    (\<lambda>(l, M) action (l', M'). E_precise (l, M) action (l', M') \<and> \<not> check_diag n M')
    (\<lambda>(l, M) action (l', M'). E_from_op (l, M) action (l', M') \<and> \<not> check_diag n M')
    (\<sim>) wf_state wf_state"
  using E_from_op_bisim
  apply (rule Bisimulation_Invariant_filter[
        where FA = "\<lambda>(l, M). \<not> check_diag n M" and FB = "\<lambda>(l, M). \<not> check_diag n M"
        ])
  subgoal
    unfolding wf_state_def state_equiv_def
    apply clarsimp
    apply (subst canonical_check_diag_empty_iff[symmetric], erule wf_dbm_altD(1))
    apply (subst canonical_check_diag_empty_iff[symmetric], erule wf_dbm_altD(1))
    apply (simp add: dbm_equiv_def)
    done
   apply (auto; fail)+
  done

end (* End of context for bisimilarity *)


context TA_Start
begin

lemma
  assumes "A \<turnstile> l \<longrightarrow>\<^bsup>g,a,r\<^esup> l'" "wf_dbm M"
  shows E_act_op'_bisim: "E_act_op' l r g l' M \<simeq> E_act_op l r g l' M" (is ?bisim)
  and E_act_op'_wf: "wf_dbm (E_act_op' l r g l' M)" (is ?wf)
proof -
  note intros =
    dbm_equiv_refl dbm_equiv_trans[OF filter_diag_equiv, rotated]
    wf_dbm_abstr_repair_equiv_FW[rotated] reset'_upd_equiv
  have
    "\<forall>c\<in>constraint_clk ` set (inv_of A l'). 0 < c \<and> c \<le> n"
    "\<forall>c\<in>constraint_clk ` set (inv_of A l'). 0 < c"
    using clock_range collect_clks_inv_clk_set[of A l'] unfolding collect_clks_def by blast+
  moreover have "\<forall>c\<in>constraint_clk ` set g. 0 < c \<and> c \<le> n" "\<forall>c\<in>constraint_clk ` set g. 0 < c"
    using clock_range collect_clocks_clk_set[OF assms(1)] unfolding collect_clks_def by blast+
  moreover have "\<forall>i\<in>set r. 0 < i \<and> i \<le> n" "\<forall>i\<in>set r. 0 < i"
    using clock_range reset_clk_set[OF assms(1)] unfolding collect_clks_def by blast+
  moreover note side_conds = calculation assms(2)
  note wf_intros =
    wf_dbm_abstr_repair wf_dbm_reset'_upd filter_diag_wf_dbm wf_dbm_FW'_abstr_upd
  note check_diag_intros =
    reset'_upd_check_diag_preservation abstr_repair_check_diag_preservation
  show ?bisim unfolding E_act_op'_def E_act_op_def
    by simp (intro intros check_diag_intros side_conds wf_intros order.refl)
  show ?wf
    unfolding E_act_op'_def by simp (intro wf_intros side_conds order.refl)
qed

lemma
  assumes "wf_dbm M"
  shows E_del_op'_bisim: "E_del_op' l M \<simeq> E_del_op l M" (is ?bisim)
    and E_del_op'_wf: "wf_dbm (E_del_op' l M)" (is ?wf)
proof -
  note intros =
    dbm_equiv_refl wf_dbm_abstr_repair_equiv_FW[rotated]
  note wf_intros =
    wf_dbm_abstr_repair wf_dbm_up_canonical_upd filter_diag_wf_dbm
  note check_diag_intros =
    abstr_repair_check_diag_preservation
  have side_conds: "\<forall>c\<in>constraint_clk ` set (inv_of A l). 0 < c \<and> c \<le> n"
    using clock_range collect_clks_inv_clk_set[of A l] unfolding collect_clks_def by blast
  show ?bisim and ?wf unfolding E_del_op'_def E_del_op_def
    by (intro intros check_diag_intros side_conds wf_intros order.refl assms)+
qed

lemma step_z_step_z_dbm_equiv:
  "Bisimulation_Invariant
     (\<lambda> (l, D) a (l', D'). step_z (conv_A A) l D a l' D')
     (\<lambda> (l, D) a (l', D'). step_z_dbm (conv_A A) l D v n a l' D')
     (\<lambda>(l, Z) (l', M). l = l' \<and> [M]\<^bsub>v,n\<^esub> = Z)
     (\<lambda>(l, Z). True)
     (\<lambda>(l, y). True)"
  by (standard; fastforce elim: step_z_dbm_DBM intro: step_z_dbm_sound)

lemma step_z_dbm_step_impl_precise_equiv:
  "Bisimulation_Invariant
     (\<lambda> (l, D) a (l', D'). step_z_dbm (conv_A A) l D v n a l' D')
     E_precise
     (\<lambda>(l, M) (l', D). l = l' \<and> [curry (conv_M D)]\<^bsub>v,n\<^esub> = [M]\<^bsub>v,n\<^esub>)
     (\<lambda>(l, y). valid_dbm y)
     wf_state"
  unfolding E_precise_def
proof (standard, goal_cases)
  case prems: (1 a b a')
  then show ?case
    using step_impl_complete''_improved by (auto dest: step_z_dbm_equiv' simp: wf_state_def)
next
  case prems: (2 a a' b')
  then show ?case
    by clarsimp
       (drule step_impl_sound', auto 4 3 dest: step_z_dbm_equiv' simp add: wf_state_def wf_dbm_def)
next
  case (3 a b)
  then show ?case
    using step_z_norm_valid_dbm'_spec step_z_valid_dbm' by auto
next
  case (4 a b)
  then show ?case
    by (clarsimp simp: norm_step_wf_dbm step_impl_wf_dbm wf_state_def)
qed

sublocale E_precise_op': E_Precise_Bisim _ _ _ _ E_del_op' E_act_op'
  by standard
     (rule E_del_op'_bisim E_act_op'_bisim E_del_op'_wf E_act_op'_wf; assumption)+

lemma step_z_dbm_final_bisim:
  "Bisimulation_Invariant
     (\<lambda> (l, D) a (l', D'). step_z_dbm (conv_A A) l D v n a l' D')
     E_precise_op'.E_from_op
     (\<lambda> (l, M) (l', D'). l' = l \<and> [curry (conv_M D')]\<^bsub>v,n\<^esub> = [M]\<^bsub>v,n\<^esub>)
     (\<lambda>(l, y). valid_dbm y) wf_state"
  by (rule Bisimulation_Invariant_sim_replace,
      rule Bisimulation_Invariant_composition[
        OF step_z_dbm_step_impl_precise_equiv[folded E_precise_def] E_precise_op'.E_from_op_bisim
      ]) (auto simp add: state_equiv_def dbm_equiv_def)

end (* TA Start *)

context E_Precise_Bisim
begin

interpretation
  Bisimulation_Invariant
  "(\<lambda> (l, D) a (l', D'). conv_A A \<turnstile> \<langle>l, D\<rangle> \<leadsto>\<^bsub>v,n,a\<^esub> \<langle>l', D'\<rangle>)"
  E_from_op
  "\<lambda> (l, M) (l', D'). l' = l \<and> [curry (conv_M D')]\<^bsub>v,n\<^esub> = [M]\<^bsub>v,n\<^esub>"
  "\<lambda>(l, y). valid_dbm y"
  wf_state
  by (rule Bisimulation_Invariant_sim_replace,
      rule Bisimulation_Invariant_composition[
        OF step_z_dbm_step_impl_precise_equiv[folded E_precise_def] E_from_op_bisim
      ]) (auto simp add: state_equiv_def dbm_equiv_def)

lemmas step_z_dbm'_E_from_op_bisim = Bisimulation_Invariant_axioms

definition
  "E_from_op_empty \<equiv> \<lambda>(l, D) a (l', D'). E_from_op (l, D) a (l', D') \<and> \<not> check_diag n D'"

interpretation bisim_empty:
  Bisimulation_Invariant
  "\<lambda>(l, M) a (l', M'). conv_A A \<turnstile> \<langle>l, M\<rangle> \<leadsto>\<^bsub>v,n,a\<^esub> \<langle>l', M'\<rangle> \<and> [M']\<^bsub>v,n\<^esub> \<noteq> {}"
  "\<lambda>(l, D) a (l', D'). E_from_op (l, D) a (l', D') \<and> \<not> check_diag n D'"
  "\<lambda>(l, M) (l', D'). l' = l \<and> [curry (conv_M D')]\<^bsub>v,n\<^esub> = [M]\<^bsub>v,n\<^esub>"
  "\<lambda>(l, y). valid_dbm y"
  wf_state
  using step_z_dbm'_E_from_op_bisim apply (rule Bisimulation_Invariant_filter[
        where FA = "\<lambda>(l', M'). [M']\<^bsub>v,n\<^esub> \<noteq> {}" and FB = "\<lambda>(l', D'). \<not> check_diag n D'"
        ])
  using canonical_check_diag_empty_iff canonical_empty_check_diag' by (auto simp: wf_state_def)

lemmas step_z_dbm_E_from_op_bisim_empty =
  bisim_empty.Bisimulation_Invariant_axioms[folded E_from_op_empty_def]

lemma E_from_op_mono:
  assumes "E_from_op (l,D) a (l',D')"
    and   "wf_dbm D" "wf_dbm M"
    and "[curry (conv_M D)]\<^bsub>v,n\<^esub> \<subseteq> [curry (conv_M M)]\<^bsub>v,n\<^esub>"
  shows "\<exists> M'. E_from_op (l,M) a (l',M') \<and> [curry (conv_M D')]\<^bsub>v,n\<^esub> \<subseteq> [curry (conv_M M')]\<^bsub>v,n\<^esub>"
proof -
  from B_A_step[OF assms(1), of "(l, curry (conv_M D))"] assms(2) obtain D1 where D1:
    "conv_A A \<turnstile> \<langle>l, curry (conv_M D)\<rangle> \<leadsto>\<^bsub>v,n,a\<^esub> \<langle>l', D1\<rangle>" "[D1]\<^bsub>v,n\<^esub> = [curry (conv_M D')]\<^bsub>v,n\<^esub>"
    unfolding wf_state_def by (auto dest!: wf_dbm_D)
  from step_z_dbm_mono[OF this(1) assms(4)] obtain M1 where M1:
    "conv_A A \<turnstile> \<langle>l, curry (conv_M M)\<rangle> \<leadsto>\<^bsub>v,n,a\<^esub> \<langle>l', M1\<rangle>"
    "[D1]\<^bsub>v,n\<^esub> \<subseteq> [M1]\<^bsub>v,n\<^esub>"
    by atomize_elim
  with A_B_step[of "(l, curry (conv_M M))" a "(l', M1)" "(l, M)"] assms(3) obtain M2 where
    "E_from_op (l, M) a (l', M2)" "[curry (conv_M M2)]\<^bsub>v,n\<^esub> = [M1]\<^bsub>v,n\<^esub>"
    unfolding wf_state_def by (force dest: wf_dbm_D)
  with assms(3) M1(2) D1(2) show ?thesis
    by auto
qed

(* XXX Duplication (E_mono') *)
lemma E_from_op_mono':
  assumes "E_from_op (l,D) a (l',D')"
    and   "wf_dbm D" "wf_dbm M"
    and "dbm_subset n D M"
  shows "\<exists> M'. E_from_op (l,M) a (l',M') \<and> dbm_subset n D' M'"
  using assms
  apply -
  apply (frule E_from_op_mono[where M = M], assumption+)
   apply (subst dbm_subset_correct'', assumption+)
   apply (rule dbm_subset_conv, assumption)
  apply safe
  apply (subst (asm) dbm_subset_correct'')
  subgoal
    using B_invariant[unfolded wf_state_def] by auto
  subgoal
    using B_invariant[unfolded wf_state_def] by auto
  apply (blast intro: dbm_subset_conv_rev)
  done

lemma E_from_op_empty_mono':
  assumes "E_from_op_empty (l,D) a (l',D')"
    and   "wf_dbm D" "wf_dbm M"
    and "dbm_subset n D M"
  shows "\<exists> M'. E_from_op_empty (l,M) a (l',M') \<and> dbm_subset n D' M'"
  using assms unfolding E_from_op_empty_def using check_diag_subset E_from_op_mono' by fast

interpretation B:
    Bisimulation
    "\<lambda> (l, Z) a (l', Z'). conv_A A \<turnstile> \<langle>l, Z\<rangle> \<leadsto>\<^bsub>a\<^esub> \<langle>l', Z'\<rangle> \<and> Z' \<noteq> {}"
    "\<lambda> (l, M) a (l', M'). conv_A A \<turnstile> \<langle>l, M\<rangle> \<leadsto>\<^bsub>v,n,a\<^esub> \<langle>l', M'\<rangle> \<and> [M']\<^bsub>v,n\<^esub> \<noteq> {}"
    "\<lambda> (l, Z) (l', M). l' = l \<and> Z = [M]\<^bsub>v,n\<^esub>"
    by (standard; force elim!: step_z_dbm_DBM step_z_dbm_sound)

interpretation B1:
    Bisimulation_Invariant
    "\<lambda> (l, Z) a (l', Z'). conv_A A \<turnstile> \<langle>l, Z\<rangle> \<leadsto>\<^bsub>a\<^esub> \<langle>l', Z'\<rangle> \<and> Z' \<noteq> {}"
    "\<lambda> (l, M) a (l', M'). conv_A A \<turnstile> \<langle>l, M\<rangle> \<leadsto>\<^bsub>v,n,a\<^esub> \<langle>l', M'\<rangle> \<and> [M']\<^bsub>v,n\<^esub> \<noteq> {}"
    "\<lambda> (l, Z) (l', M). l' = l \<and> Z = [M]\<^bsub>v,n\<^esub>"
    "\<lambda>_. True"
    "\<lambda>(l, M). valid_dbm M"
  by standard (auto 4 3 elim: step_z_dbm_DBM step_z_dbm_sound dest: step_z_valid_dbm')

interpretation bisim_empty_zone:
  Bisimulation_Invariant
  "\<lambda>(l, Z) a (l', Z'). conv_A A \<turnstile> \<langle>l, Z\<rangle> \<leadsto>\<^bsub>a\<^esub> \<langle>l', Z'\<rangle> \<and> Z' \<noteq> {}"
  E_from_op_empty
  "\<lambda>(l, Z) (l', D). l' = l \<and> [curry (conv_M D)]\<^bsub>v,n\<^esub> = Z"
  "\<lambda>_. True"
  wf_state
  apply (rule Bisimulation_Invariant_sim_replace)
   apply (rule Bisimulation_Invariant_composition[rotated])
    apply (rule step_z_dbm_E_from_op_bisim_empty)
   apply (rule B1.Bisimulation_Invariant_axioms)
  apply (auto simp: wf_state_def dest!: wf_dbm_D(3))
  done

lemmas step_z_E_from_op_bisim_empty =
  bisim_empty_zone.Bisimulation_Invariant_axioms[folded E_from_op_empty_def]

end (* E Precise Bisim *)

end