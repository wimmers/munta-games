section \<open>Implementation of Timed Game Automata\<close>
theory Timed_Game_Certification_Impl
  imports
    Timed_Game_Automata
    TA_Impl.Normalized_Zone_Semantics_Impl_Refine
    Normalized_Zone_Semantics_Certification2
begin

subsection \<open>Misc\<close>

(* XXX Why do these not work? *)
no_notation
  comp2  (infixl "\<circ>\<circ>" 55) and
  comp3  (infixl "\<circ>\<circ>\<circ>" 55)

hide_const D

(* XXX Move *)
\<comment> \<open>Time-abstracted step of a timed automaton.\<close>
definition step_ta where
  "step_ta A \<equiv> \<lambda>(l, u) a (l', u'). case a of
      \<upharpoonleft>a \<Rightarrow> A \<turnstile> \<langle>l, u\<rangle> \<rightarrow>\<^bsub>a\<^esub> \<langle>l',u'\<rangle>
    | \<tau> \<Rightarrow> \<exists>d. A \<turnstile> \<langle>l, u\<rangle> \<rightarrow>\<^bsup>d\<^esup> \<langle>l',u'\<rangle>"


subsection \<open>Implementation Locales\<close>

locale TA_Impl_Ext =
  TA_Impl where A = A and l\<^sub>0i = l\<^sub>0i
  for A :: "('a, nat, int, 's) ta" and l\<^sub>0i :: "'si:: {hashable,heap}" +
  fixes states_mem_impl
  assumes states_mem_impl: "(states_mem_impl, (\<lambda>l. l \<in> states')) \<in> loc_rel \<rightarrow> bool_rel"

locale TA_Impl_Precise =
  TA_Impl _ _ _ l\<^sub>0 _ _ _ _ _ l\<^sub>0i
  + op_precise: E_Precise_Bisim _ l\<^sub>0 for l\<^sub>0 :: 's and l\<^sub>0i :: "'si:: {hashable,heap}" +
  fixes act_impl and del_impl and states_mem_impl
  assumes act_impl:
      "(uncurry4 act_impl, uncurry4 (\<lambda> l r. RETURN ooo PR_CONST act l r)) \<in> op_impl_assn"
      and del_impl: "(uncurry del_impl, uncurry (RETURN oo PR_CONST del))
        \<in> location_assn\<^sup>k *\<^sub>a (mtx_assn n)\<^sup>d \<rightarrow>\<^sub>a mtx_assn n"
      and states_mem_impl: "(states_mem_impl, (\<lambda>l. l \<in> states')) \<in> loc_rel \<rightarrow> bool_rel"
begin

sublocale TA_Impl_Ext
  by (standard) (rule states_mem_impl)

end


subsection \<open>Main Construction\<close>

locale TGA_Start_Defs =
  \<^cancel>\<open>TA_Start_Defs where A = A for A :: "('a, nat, int, 's) ta" +\<close>
  TA_Impl_Precise where A = A for A :: "('a, nat, int, 's) ta" +
  fixes controllable :: "'a \<Rightarrow> bool"
  fixes strategy :: "('a, nat, real, 's) strategy"
  fixes S :: "'s \<times> int DBM' \<Rightarrow> (int DBM' \<times> 'a move set) list"
  fixes K :: "(nat, real, 's) ta_config set"
  assumes strategy_S:
    "a \<in> strategy (l, u) \<Longrightarrow> u \<in> [curry (conv_M M)]\<^bsub>v,n\<^esub> \<Longrightarrow> wf_state (l, M)
  \<Longrightarrow> \<exists>M\<^sub>s C. (M\<^sub>s, C) \<in> set (S (l, M)) \<and> a \<in> C \<and> u \<in> [curry (conv_M M\<^sub>s)]\<^bsub>v,n\<^esub>"
  assumes S_dbm_equiv:
    "(M\<^sub>s, C) \<in> set (S (l, M)) \<Longrightarrow> wf_dbm M \<Longrightarrow> wf_dbm M' \<Longrightarrow> M \<simeq> M'
    \<Longrightarrow> \<exists>M\<^sub>s'. (M\<^sub>s', C) \<in> set (S (l, M')) \<and> M\<^sub>s \<simeq> M\<^sub>s'"
  assumes S_dbm_mono:
    "(M\<^sub>s, C) \<in> set (S (l, M)) \<Longrightarrow> wf_dbm M \<Longrightarrow> wf_dbm M'
    \<Longrightarrow> [curry (conv_M M)]\<^bsub>v,n\<^esub> \<subseteq> [curry (conv_M M')]\<^bsub>v,n\<^esub>
    \<Longrightarrow> \<exists>M\<^sub>s' C'. (M\<^sub>s', C') \<in> set (S (l, M'))
      \<and> [curry (conv_M M\<^sub>s)]\<^bsub>v,n\<^esub> \<subseteq> [curry (conv_M M\<^sub>s')]\<^bsub>v,n\<^esub> \<and> C \<subseteq> C'"
  assumes strategy_split_preserves_wf_state:
    "(M\<^sub>s, C) \<in> set (S (l, M)) \<Longrightarrow> wf_state (l, M) \<Longrightarrow> wf_state (l, M\<^sub>s)"
begin

sublocale sem: Timed_Game_Automaton "conv_A A" controllable strategy .

inductive step_impl where
  action: "step_impl (l, M) (l', M')"
  if "op_precise.E_from_op_empty (l, M\<^sub>s) (\<upharpoonleft>a) (l', M')"
  "controllable a" "(M\<^sub>s, C) \<in> set (S (l, M))" "Act a \<in> C"
| wait: "step_impl (l, M) (l', M')"
  if "op_precise.E_from_op_empty (l, M\<^sub>s) \<tau> (l', M')" "(M\<^sub>s, C) \<in> set (S (l, M))" "Wait \<in> C"
| uncontrolled: "step_impl (l, M) (l', M')"
  if "op_precise.E_from_op_empty (l, M) (\<upharpoonleft>a) (l', M')" "\<not> controllable a"

sublocale sem: Timed_Safety_Game_Strat "conv_A A" controllable K strategy .

lemma S_dbm_equivE:
  assumes "(M\<^sub>s, C) \<in> set (S (l, M))" "wf_dbm M" "wf_dbm M'" "M \<simeq> M'"
  obtains M\<^sub>s' where "(M\<^sub>s', C) \<in> set (S (l, M'))" "M\<^sub>s \<simeq> M\<^sub>s'"
  using assms by atomize_elim (rule S_dbm_equiv)

interpretation bisim_empty_zone:
  Bisimulation_Invariant
  "\<lambda>(l, Z) a (l', Z'). conv_A A \<turnstile> \<langle>l, Z\<rangle> \<leadsto>\<^bsub>a\<^esub> \<langle>l', Z'\<rangle> \<and> Z' \<noteq> {}"
  op_precise.E_from_op_empty
  "\<lambda>(l, Z) (l', D). l' = l \<and> [curry (conv_M D)]\<^bsub>v,n\<^esub> = Z"
  "\<lambda>_. True"
  wf_state
  by (rule op_precise.step_z_E_from_op_bisim_empty)

interpretation zone_simulation:
  Simulation
  "step_ta (conv_A A)"
  "\<lambda>(l, Z) a (l', Z'). conv_A A \<turnstile> \<langle>l, Z\<rangle> \<leadsto>\<^bsub>a\<^esub> \<langle>l', Z'\<rangle> \<and> Z' \<noteq> {}"
  "\<lambda> (l, u) (l', Z). l' = l \<and> u \<in> Z"
  apply (standard, clarsimp)
  unfolding step_ta_def
  by (auto split: action.split_asm intro: step_z.intros dest!: step_a_z_complete step_t_z_complete)

interpretation step_ta_impl_simulation:
  Simulation_Invariant
  "step_ta (conv_A A)"
  op_precise.E_from_op_empty
  "\<lambda>(l, u) (l', D). l' = l \<and> u \<in> [curry (conv_M D)]\<^bsub>v,n\<^esub>"
  "\<lambda>_. True"
  wf_state
  apply (rule Labeled_Graphs.Simulation_Invariant_sim_replace)
   apply (rule Labeled_Graphs.Simulation_Invariant_composition)
    apply (rule zone_simulation.Simulation_Invariant)
   apply (rule bisim_empty_zone.A_B.Simulation_Invariant_axioms)
  apply auto
  done

sublocale sem_impl_simulation:
  Graphs.Simulation_Invariant
  sem.step
  step_impl
  "\<lambda>(l, u) (l', D). l' = l \<and> u \<in> [curry (conv_M D)]\<^bsub>v,n\<^esub>"
  "\<lambda>_. True"
  wf_state
proof (standard; (clarsimp simp del: One_nat_def)?)
  fix l l' :: 's and u u' :: "nat \<Rightarrow> real" and M :: "int DBM'"
  assume 
    sem_step: "sem.step (l, u) (l', u')" and
    "wf_state (l, M)" and
    "u \<in> [curry (conv_M M)]\<^bsub>v,n\<^esub>"
  note sim_step = step_ta_impl_simulation.A_B_step[
      of "(l, u)" a "(l', u')" "(l, M\<^sub>s)" for a M\<^sub>s, simplified]
  note strategyD = strategy_S[OF _ \<open>u \<in> _\<close> \<open>wf_state _\<close>]
  note [intro] = strategy_split_preserves_wf_state
  from sem_step show "\<exists>b. step_impl (l, M) (l', b) \<and> u' \<in> [curry (conv_M b)]\<^bsub>v,n\<^esub>"
  proof cases
    case (action a)
    from strategyD[OF action(3)] obtain M\<^sub>s C where
      "(M\<^sub>s, C) \<in> set (S (l, M))"
      "Act a \<in> C"
      "u \<in> [curry (conv_M M\<^sub>s)]\<^bsub>v,n\<^esub>"
      by safe
    with sim_step[of "\<upharpoonleft>a" M\<^sub>s] action(1) \<open>wf_state (l, M)\<close> obtain M' where
      "op_precise.E_from_op_empty (l, M\<^sub>s) \<upharpoonleft>a (l', M')" "u' \<in> [curry (conv_M M')]\<^bsub>v,n\<^esub>"
      unfolding step_ta_def by auto
    with \<open>controllable a\<close> \<open>_\<in> set (S (l, M))\<close> \<open>_ \<in> C\<close> show ?thesis
      by (inst_existentials M') (rule step_impl.intros)
  next
    case (wait d)
    from strategyD[OF wait(2)] obtain M\<^sub>s C where
      "(M\<^sub>s, C) \<in> set (S (l, M))"
      "Wait \<in> C"
      "u \<in> [curry (conv_M M\<^sub>s)]\<^bsub>v,n\<^esub>"
      by safe
    with sim_step[of \<tau> M\<^sub>s] wait(1) \<open>wf_state (l, M)\<close> obtain M' where
      "op_precise.E_from_op_empty (l, M\<^sub>s) \<tau> (l', M')" "u' \<in> [curry (conv_M M')]\<^bsub>v,n\<^esub>"
      unfolding step_ta_def by auto
    with \<open>_\<in> set (S (l, M))\<close> \<open>_ \<in> C\<close> show ?thesis
      by (inst_existentials M') (rule step_impl.intros)
  next
    case (uncontrolled a)
    from sim_step[of "\<upharpoonleft>a" M] uncontrolled(1) \<open>u \<in> _\<close> \<open>wf_state _\<close> obtain M' where
      "op_precise.E_from_op_empty (l, M) \<upharpoonleft>a (l', M')" "u' \<in> [curry (conv_M M')]\<^bsub>v,n\<^esub>"
      unfolding step_ta_def by auto
    with uncontrolled(2-) show ?thesis
      by (inst_existentials M') (rule step_impl.intros)
  qed
next
  fix l l' :: 's and M M' :: "int DBM'"
  assume 
    "step_impl (l, M) (l', M')" "wf_state (l, M)"
  then show "wf_state (l', M')"
    by (cases; elim bisim_empty_zone.B_invariant[rotated] strategy_split_preserves_wf_state)
qed


lemma invariant_safe_fromI:
  assumes "Graph_Invariant_Start step_impl (l\<^sub>0, Z\<^sub>0) I"
    "\<forall>l Z. I (l, Z) \<longrightarrow> from_R l ([curry (conv_M Z)]\<^bsub>v,n\<^esub>) \<inter> K = {}"
    "u\<^sub>0 \<in> [curry (conv_M Z\<^sub>0)]\<^bsub>v,n\<^esub>" "wf_state (l\<^sub>0, Z\<^sub>0)"
  shows "sem.safe_from (l\<^sub>0, u\<^sub>0)"
proof -
  interpret inv: Graph_Invariant_Start step_impl "(l\<^sub>0, Z\<^sub>0)" I
    by (rule assms)
  show ?thesis
    unfolding sem.safe_from_alt_def using assms
    by (auto dest!: inv.invariant_reaches
          sem_impl_simulation.simulation_reaches[where b = "(l\<^sub>0, Z\<^sub>0)"])
qed

lemma safe_fromI:
  "sem.safe_from (l\<^sub>0, u\<^sub>0)"
  if "(\<nexists>l' D'. step_impl\<^sup>*\<^sup>* (l\<^sub>0, D\<^sub>0) (l', D') \<and> from_R l' ([curry (conv_M D')]\<^bsub>v,n\<^esub>) \<inter> K \<noteq> {})"
    "u\<^sub>0 \<in> [curry (conv_M D\<^sub>0)]\<^bsub>v,n\<^esub>" "wf_dbm D\<^sub>0"
  unfolding sem.safe_from_alt_def using that
  by (auto simp: wf_state_def dest!: sem_impl_simulation.simulation_reaches[where b = "(l\<^sub>0, D\<^sub>0)"])

end

end