theory Timed_Game_Certification_Impl2
  imports Timed_Game_Certification_Impl
begin

text \<open>This theory tried to achieve the same goals as theory \<open>Timed_Game_Certification_Impl\<close> but
turned out too complicated for our purposes.
It is therefore incomplete and can be considered deprecated.
We leave it for now to document the thought process.\<close>

subsection \<open>More Simulation Theorems\<close>

text \<open>These theorems might be useful, maybe they should be moved somewhere else.\<close>

lemma (in Graphs.Simulation) Graph_InvariantI:
  assumes "Graphs.Graph_Invariant B I"
  shows "Graphs.Graph_Invariant A (\<lambda>a. \<exists>b. a \<sim> b \<and> I b)"
  by (smt (verit, ccfv_SIG) Graphs.Graph_Invariant_def A_B_step assms(1))

lemmas Graph_Invariant_simulationI = Simulation.Graph_InvariantI

lemma (in Graphs.Simulation) Graph_Invariant_StartI:
  assumes "Graphs.Graph_Invariant_Start B b\<^sub>0 I" "a\<^sub>0 \<sim> b\<^sub>0"
  shows "Graphs.Graph_Invariant_Start A a\<^sub>0 (\<lambda>a. \<exists>b. a \<sim> b \<and> I b)"
  using assms unfolding Graphs.Graph_Invariant_Start_def Graphs.Graph_Invariant_Start_axioms_def
  by (blast intro: Graph_InvariantI)

lemmas Graph_Invariant_Start_simulationI = Simulation.Graph_Invariant_StartI

lemma (in Graphs.Graph_Invariant) replaceI:
  assumes "P = Q"
  shows "Graphs.Graph_Invariant E Q"
  using Graph_Invariant_axioms assms by simp

lemma (in Graphs.Graph_Invariant_Start) replaceI:
  assumes "P = Q"
  shows "Graphs.Graph_Invariant_Start E s\<^sub>0 Q"
  using Graph_Invariant_Start_axioms assms by simp

lemma (in Graphs.Simulation_Invariant) Graph_InvariantI:
  assumes "Graphs.Graph_Invariant B I"
  shows "Graphs.Graph_Invariant A (\<lambda>a. \<exists>b. PA a \<and> a \<sim> b \<and> I b \<and> PB b)"
  using assms
  by (smt (verit, ccfv_threshold) A_B_step A_invariant B_invariant Graphs.Graph_Invariant_def)

lemma Simulation_Invariant_composition:
  assumes
    "Graphs.Simulation_Invariant A B sim1 PA PB"
    "Graphs.Simulation_Invariant B C sim2 PB PC"
  shows
    "Graphs.Simulation_Invariant A C (\<lambda> a c. \<exists> b. PB b \<and> sim1 a b \<and> sim2 b c) PA PC"
proof -
  interpret A: Graphs.Simulation_Invariant A B sim1 PA PB
    by (rule assms(1))
  interpret B: Graphs.Simulation_Invariant B C sim2 PB PC
    by (rule assms(2))
  show ?thesis
    by (standard; (blast dest: A.A_B_step B.A_B_step))
qed

lemma (in Graphs.Simulation) Simulation_Invariant:
  "Graphs.Simulation_Invariant A B sim (\<lambda>_. True) (\<lambda>_. True)"
  by unfold_locales (rule A_B_step)

lemma Simulation_Invariant_sim_replace:
  assumes "Graphs.Simulation_Invariant A B sim PA PB"
      and "\<And> a b. PA a \<Longrightarrow> PB b \<Longrightarrow> sim a b \<longleftrightarrow> sim' a b"
    shows "Graphs.Simulation_Invariant A B sim' PA PB"
proof -
  interpret Graphs.Simulation_Invariant A B sim PA PB
    by (rule assms(1))
  from assms(2) show ?thesis
    by (unfold_locales; blast dest: A_B_step)
qed

subsection \<open>The Original More Layered Approach\<close>

text \<open>To make it work properly,
  one would need to introduce an invariant already in the zone semantics.\<close>

paragraph \<open>Zone Semantics\<close>

locale Timed_Game_Automaton_Zones =
  Timed_Game_Automaton where A = A for A :: "('a, 'c, 't :: time, 's) ta" +
  fixes Strategy :: "'s \<times> ('c, 't) zone \<Rightarrow> (('c, 't) zone \<times> 'a move set) set"
  assumes strategy_Strategy:
    "a \<in> strategy (l, u) \<Longrightarrow> u \<in> Z \<Longrightarrow> \<exists>Z\<^sub>s M. (Z\<^sub>s, M) \<in> Strategy (l, Z) \<and> a \<in> M \<and> u \<in> Z\<^sub>s"
begin

text \<open>XXX: Choose maximal \<open>Z'\<close>\<close>
\<^cancel>\<open>definition "Strategy \<equiv> \<lambda>(l, Z). {(Z', C) | Z' C. Z' \<subseteq> Z \<and> (\<forall>u \<in> Z'. strategy (l, u) = C)}"\<close>

text \<open>Are strategies convex, i.e. is \<^term>\<open>Strategy(l, Z)\<close> always singleton?\<close>

inductive step_z where
  action: "step_z (l, Z) (l', Z')"
  if "A \<turnstile> \<langle>l, Z\<^sub>s\<rangle> \<leadsto>\<^bsub>\<upharpoonleft>a\<^esub> \<langle>l', Z'\<rangle>" "controllable a" "(Z\<^sub>s, C) \<in> Strategy (l, Z)" "Act a \<in> C"
| wait: "step_z (l, Z) (l', Z')"
  if "A \<turnstile> \<langle>l, Z\<^sub>s\<rangle> \<leadsto>\<^bsub>\<tau>\<^esub> \<langle>l',Z'\<rangle>" "(Z\<^sub>s, C) \<in> Strategy (l, Z)" "Wait \<in> C"
| uncontrolled: "step_z (l, Z) (l', Z')"
  if "A \<turnstile> \<langle>l, Z\<rangle> \<leadsto>\<^bsub>\<upharpoonleft>a\<^esub> \<langle>l', Z'\<rangle>" "\<not> controllable a"

lemma strategy_StrategyE:
  assumes "u \<in> Z" "a \<in> strategy (l, u)"
  obtains Z\<^sub>s M where "(Z\<^sub>s, M) \<in> Strategy (l, Z)" "a \<in> M" \<^cancel>\<open>"Z\<^sub>s \<subseteq> Z"\<close> "u \<in> Z\<^sub>s"
  using assms by atomize_elim (rule strategy_Strategy)

sublocale zone_simulation:
  Graphs.Simulation
  step
  "\<lambda> (l, Z) (l', Z'). step_z (l, Z) (l', Z') \<and> Z' \<noteq> {}"
  "\<lambda> (l, u) (l', Z). l' = l \<and> u \<in> Z"
  apply standard
  apply clarsimp
  apply (erule step.cases; clarsimp; (erule (1) strategy_StrategyE)?)
    apply (auto intro: step_z.intros dest!: step_a_z_complete step_t_z_complete)
  done

end




paragraph \<open>Concrete Semantics To Zone Semantics\<close>
context Timed_Safety_Game_Strat
begin

thm invariant_safe_fromI

\<comment> \<open>We directly establish the invariant in the end, see below.\<close>
lemma invariant_safe_fromI:
  assumes "Labeled_Graphs.Graph_Invariant_Start (\<lambda> (l, Z) a (l', Z'). step_z (l, Z) a (l', Z') \<and> Z' \<noteq> {}) (l\<^sub>0, Z\<^sub>0) I"
    "\<forall>l Z. I (l, Z) \<longrightarrow> from_R l Z \<inter> K = {}" "u\<^sub>0 \<in> Z\<^sub>0"
  shows "safe_from (l\<^sub>0, u\<^sub>0)"
  apply (rule invariant_safe_fromI[where I = "\<lambda>(l, u). \<exists>Z. I (l, Z) \<and> u \<in> Z"])
  apply (rule Graph_Invariant_Start.replaceI)
  apply (rule zone_simulation.Graph_Invariant_StartI)
  using assms by auto













end


paragraph \<open>Zone Semantics To Implementation Semantics\<close>

locale TGA_Start_Defs1 =
  \<^cancel>\<open>TA_Start_Defs where A = A for A :: "('a, nat, int, 's) ta" +\<close>
  TA_Impl_Precise where A = A for A :: "('a, nat, int, 's) ta" +
  fixes controllable :: "'a \<Rightarrow> bool"
  fixes strategy :: "('a, nat, real, 's) strategy"
  fixes S :: "'s \<times> int DBM' \<Rightarrow> (int DBM' \<times> 'a move set) set"
  fixes K :: "(nat, real, 's) ta_config set"
  assumes strategy_S:
    "a \<in> strategy (l, u) \<Longrightarrow> u \<in> [curry (conv_M M)]\<^bsub>v,n\<^esub> \<Longrightarrow> wf_state (l, M)
  \<Longrightarrow> \<exists>M\<^sub>s C. (M\<^sub>s, C) \<in> S (l, M) \<and> a \<in> C \<and> u \<in> [curry (conv_M M\<^sub>s)]\<^bsub>v,n\<^esub>"
begin

term "conv_A A \<turnstile> \<langle>l, Z\<rangle> \<leadsto> \<langle>l', Z'\<rangle>"

sublocale sem: Timed_Game_Automaton "conv_A A" controllable strategy .

definition
  "Strategy \<equiv> \<lambda>(l, Z).
    {([curry (conv_M M\<^sub>s)]\<^bsub>v,n\<^esub>, C) | M\<^sub>s C. \<exists>M. Z = [curry (conv_M M)]\<^bsub>v,n\<^esub> \<and> (M\<^sub>s, C) \<in> S (l, M)}"

inductive step_z where
  action: "step_z (l, Z) (l', Z')"
  if "conv_A A \<turnstile> \<langle>l, Z\<^sub>s\<rangle> \<leadsto>\<^bsub>\<upharpoonleft>a\<^esub> \<langle>l', Z'\<rangle>" "controllable a" "(Z\<^sub>s, C) \<in> Strategy (l, Z)" "Act a \<in> C"
| wait: "step_z (l, Z) (l', Z')"
  if "conv_A A \<turnstile> \<langle>l, Z\<^sub>s\<rangle> \<leadsto>\<^bsub>\<tau>\<^esub> \<langle>l',Z'\<rangle>" "(Z\<^sub>s, C) \<in> Strategy (l, Z)" "Wait \<in> C"
| uncontrolled: "step_z (l, Z) (l', Z')"
  if "conv_A A \<turnstile> \<langle>l, Z\<rangle> \<leadsto>\<^bsub>\<upharpoonleft>a\<^esub> \<langle>l', Z'\<rangle>" "\<not> controllable a"

lemma strategy_StrategyE:
  assumes "u \<in> Z" "a \<in> strategy (l, u)" "Z = [curry (conv_M M)]\<^bsub>v,n\<^esub>" "wf_state (l, M)"
  obtains Z\<^sub>s M where "(Z\<^sub>s, M) \<in> Strategy (l, Z)" "a \<in> M" \<^cancel>\<open>"Z\<^sub>s \<subseteq> Z"\<close> "u \<in> Z\<^sub>s"
  using assms
  unfolding Strategy_def
  by (blast dest!: strategy_S[where M = M])

sublocale sem: Timed_Game_Automaton_Zones controllable strategy "conv_A A" Strategy
  apply standard
  sorry

inductive step_impl where
  action: "step_impl (l, M) (l', M')"
  if "op_precise.E_from_op_empty (l, M\<^sub>s) (\<upharpoonleft>a) (l', M')"
  "controllable a" "(M\<^sub>s, C) \<in> S (l, M)" "Act a \<in> C"
| wait: "step_impl (l, M) (l', M')"
  if "op_precise.E_from_op_empty (l, M\<^sub>s) \<tau> (l', M')" "(M\<^sub>s, C) \<in> S (l, M)" "Wait \<in> C"
| uncontrolled: "step_impl (l, M) (l', M')"
  if "op_precise.E_from_op_empty (l, M) (\<upharpoonleft>a) (l', M')" "\<not> controllable a"

sublocale sem: Timed_Safety_Game_Strat "conv_A A" controllable K strategy .

lemma S_dbm_equivE:
  assumes "(M\<^sub>s, C) \<in> S (l, M)" "M \<simeq> M'"
  obtains M\<^sub>s' where "(M\<^sub>s', C) \<in> S (l, M')" "M\<^sub>s \<simeq> M\<^sub>s'"
  sorry

lemma strategy_SimulationE:
  assumes "(Z\<^sub>s, C) \<in> Strategy (l, [curry (conv_M M)]\<^bsub>v,n\<^esub>)" "wf_state (l, M)"
  obtains M\<^sub>s where "(M\<^sub>s, C) \<in> S (l, M)" "Z\<^sub>s = [curry (conv_M M\<^sub>s)]\<^bsub>v,n\<^esub>"
  apply atomize_elim
  using assms
  unfolding Strategy_def
  apply (auto 4 3 simp: dbm_equiv_def elim: S_dbm_equivE[where M' = M])
  done

lemma strategy_split_preserves_wf_state:
  assumes "(M\<^sub>s, C) \<in> S (l, M)" "wf_state (l, M)"
  shows "wf_state (l, M\<^sub>s)"
  sorry

interpretation bisim_empty_zone:
  Bisimulation_Invariant
  "\<lambda>(l, Z) a (l', Z'). conv_A A \<turnstile> \<langle>l, Z\<rangle> \<leadsto>\<^bsub>a\<^esub> \<langle>l', Z'\<rangle> \<and> Z' \<noteq> {}"
  op_precise.E_from_op_empty
  "\<lambda>(l, Z) (l', D). l' = l \<and> [curry (conv_M D)]\<^bsub>v,n\<^esub> = Z"
  "\<lambda>_. True"
  wf_state
  by (rule op_precise.step_z_E_from_op_bisim_empty)

sublocale zone_impl_simulation:
  Graphs.Simulation_Invariant
  "\<lambda> (l, Z) (l', Z'). sem.step_z (l, Z) (l', Z') \<and> Z' \<noteq> {}"
  step_impl
  "\<lambda>(l, Z) (l', D). l' = l \<and> [curry (conv_M D)]\<^bsub>v,n\<^esub> = Z"
  "\<lambda>_. True"
  wf_state
proof (standard; (clarsimp simp del: One_nat_def)?)
  fix l l' :: 's and Z' :: "(nat \<Rightarrow> real) set" and M :: "int DBM'"
  assume 
    "wf_state (l, M)" and
    sem_step: "sem.step_z (l, [curry (conv_M M)]\<^bsub>v,n\<^esub>) (l', Z')" and
    "Z' \<noteq> {}"
  from sem_step show "\<exists>b. local.step_impl (l, M) (l', b) \<and> [curry (conv_M b)]\<^bsub>v,n\<^esub> = Z'"
  proof cases
    case (action Z\<^sub>s a C)
    from strategy_SimulationE[OF action(3) \<open>wf_state _\<close>] obtain M\<^sub>s where
      "(M\<^sub>s, C) \<in> S (l, M)"
      "Z\<^sub>s = [curry (conv_M M\<^sub>s)]\<^bsub>v,n\<^esub>" .
    have "wf_state (l, M\<^sub>s)"
      using \<open>(M\<^sub>s, C) \<in> S (l, M)\<close> \<open>wf_state (l, M)\<close> by (rule strategy_split_preserves_wf_state)
    with bisim_empty_zone.A_B_step[of "(l, Z\<^sub>s)" "\<upharpoonleft>a" "(l', Z')" "(l, M\<^sub>s)", simplified]
      action(1) \<open>Z' \<noteq> {}\<close> \<open>Z\<^sub>s = _\<close>
    obtain M' where
      "op_precise.E_from_op_empty (l, M\<^sub>s) \<upharpoonleft>a (l', M')" "[curry (conv_M M')]\<^bsub>v,n\<^esub> = Z'"
      by metis
    with action(2,4) \<open>_\<in> S (l, M)\<close> show ?thesis
      by (inst_existentials M') (rule step_impl.intros; simp)
  next
    case (wait Z\<^sub>s C)
    from strategy_SimulationE[OF wait(2) \<open>wf_state _\<close>] obtain M\<^sub>s where
      "(M\<^sub>s, C) \<in> S (l, M)"
      "Z\<^sub>s = [curry (conv_M M\<^sub>s)]\<^bsub>v,n\<^esub>" .
    have "wf_state (l, M\<^sub>s)"
      using \<open>(M\<^sub>s, C) \<in> S (l, M)\<close> \<open>wf_state (l, M)\<close> by (rule strategy_split_preserves_wf_state)
    with bisim_empty_zone.A_B_step[of "(l, Z\<^sub>s)" \<tau> "(l', Z')" "(l, M\<^sub>s)", simplified]
      wait(1) \<open>Z' \<noteq> {}\<close> \<open>Z\<^sub>s = _\<close>
    obtain M' where
      "op_precise.E_from_op_empty (l, M\<^sub>s) \<tau> (l', M')" "[curry (conv_M M')]\<^bsub>v,n\<^esub> = Z'"
      by metis
    with wait(3) \<open>_\<in> S (l, M)\<close> show ?thesis
      by (inst_existentials M') (rule step_impl.intros; simp)
  next
    case (uncontrolled a)
    from bisim_empty_zone.A_B_step[of _ "\<upharpoonleft>a" "(l', Z')" "(l, M)", simplified]
      uncontrolled(1) \<open>Z' \<noteq> {}\<close> \<open>wf_state _\<close>
    obtain M' where
      "op_precise.E_from_op_empty (l, M) \<upharpoonleft>a (l', M')" "[curry (conv_M M')]\<^bsub>v,n\<^esub> = Z'"
      by auto
    with uncontrolled(2-) show ?thesis
      by (inst_existentials M') (rule step_impl.intros; simp)
  qed
next
  fix l l' :: 's and M M' :: "int DBM'"
  assume "wf_state (l, M)" "step_impl (l, M) (l', M')"
  from this(2,1) show "wf_state (l', M')"
    by (cases; elim bisim_empty_zone.B_invariant[rotated] strategy_split_preserves_wf_state)
qed

sublocale sem_impl_simulation:
  Graphs.Simulation_Invariant
  sem.step
  step_impl
  "\<lambda>(l, u) (l', D). l' = l \<and> u \<in> [curry (conv_M D)]\<^bsub>v,n\<^esub>"
  "\<lambda>_. True"
  wf_state
  apply (rule Simulation_Invariant_sim_replace)
   apply (rule Simulation_Invariant_composition)
    apply (rule sem.zone_simulation.Simulation_Invariant)
   apply (rule zone_impl_simulation.Simulation_Invariant_axioms)
  apply auto
  done

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