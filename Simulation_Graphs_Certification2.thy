theory Simulation_Graphs_Certification2
  imports
    Certification.Simulation_Graphs_Certification
    TA_Library.Graphs
begin

context
  fixes E :: "'a \<Rightarrow> 'a \<Rightarrow> bool" and P :: "'a \<Rightarrow> bool"
    and less_eq :: "'a \<Rightarrow> 'a set \<Rightarrow> bool" (infix "\<preceq>" 50)\<^cancel>\<open> and less (infix "\<prec>" 50)\<close>
  \<^cancel>\<open>assumes preorder: "class.preorder less_eq less"\<close>
  assumes mono: "a \<preceq> B \<Longrightarrow> E a a' \<Longrightarrow> P a \<Longrightarrow> (\<forall>b \<in> B. P b)
    \<Longrightarrow> \<exists>B'. (\<forall>b' \<in> B'. \<exists>b \<in> B. E b b') \<and> a' \<preceq> B'"
  assumes invariant: "P a \<Longrightarrow> E a a' \<Longrightarrow> P b"
begin

\<^cancel>\<open>interpretation preorder less_eq less
  by (rule preorder)\<close>

\<^cancel>\<open>interpretation Simulation_Invariant
  E "\<lambda> x y. \<exists> z. z \<preceq> y \<and> E x z \<and> P z" "(\<preceq>)" P P
  by standard (auto 0 4 intro: invariant dest: mono)\<close>

interpretation Graph_Defs E .

interpretation Graph_Invariant E P
  by standard (rule invariant)

interpretation B: Graph_Invariant "\<lambda>B B'. \<forall>b' \<in> B'. \<exists>b \<in> B. E b b'" "\<lambda>B. \<forall>b \<in> B. P b"
  by standard (auto 4 3 intro: invariant)

context
  fixes F :: "'a \<Rightarrow> bool" \<comment> \<open>Final states\<close>
  assumes F_mono[intro]: "F a \<Longrightarrow> a \<preceq> B \<Longrightarrow> \<exists>b \<in> B'. F b"
begin

lemma reaches_mono:
  assumes 
    "a \<preceq> B" and
    "a \<rightarrow>* a'" and
    "P a" and
    "\<forall>b\<in>B. P b"
  shows "\<exists>B'. (\<forall>b'\<in>B'. \<exists>b\<in>B. b \<rightarrow>* b') \<and> a' \<preceq> B'"
  using assms(2) assms(1,3-)
proof (induction arbitrary: )
  case base
  then show ?case
    by auto
next
  case (step y z)
  then obtain B' where
    "a \<rightarrow>* y"
    "y \<rightarrow> z"
    "P a"
    "\<forall>a\<in>B. P a"
    "\<forall>b'\<in>B'. \<exists>b\<in>B. b \<rightarrow>* b'"
    "y \<preceq> B'"
    by auto
  then have \<open>P y\<close> \<open>\<forall>x\<in>B'. P x\<close>
    by (auto 4 3 intro: invariant_reaches)
  with mono[OF \<open>y \<preceq> B'\<close> \<open>y \<rightarrow> z\<close>] this obtain B\<^sub>z where
    "\<forall>b'\<in>B\<^sub>z. \<exists>b\<in>B'. b \<rightarrow> b'"
    "z \<preceq> B\<^sub>z"
    by auto
  with \<open>\<forall>b'\<in>B'. \<exists>b\<in>B. b \<rightarrow>* b'\<close> show ?case
    including graph_automation_aggressive by (inst_existentials B\<^sub>z) blast
qed

corollary reachability_correct:
  "\<nexists> s'. reaches a s' \<and> F s'"
  if "\<nexists> B' b'. B.reaches B B' \<and> b' \<in> B' \<and> F b'" "a \<preceq> B" "P a" "\<forall>b \<in> B. P b"
  using that by (meson F_mono reaches_mono rtranclp.rtrancl_refl)

end (* Context for property *)

end (* Context for over-approximation *)


locale Unreachability_Invariant_pre_defs =
  fixes E :: "'a \<Rightarrow> 'a \<Rightarrow> bool" and P :: "'a \<Rightarrow> bool"
    and less_eq :: "'a \<Rightarrow> 'a set \<Rightarrow> bool" (infix "\<preceq>" 50)
begin

sublocale Graph_Defs E .

definition
  "Step S T \<equiv> \<forall>t \<in> T. \<exists>s \<in> S. E s t"

notation Step ("_ \<rightarrow>'' _" [100, 100] 40)

definition Subsumed where
  "Subsumed S T \<equiv> \<forall>s \<in> S. \<exists>T' \<subseteq> T. s \<preceq> T'"

notation Subsumed (infix "\<sqsubseteq>" 50)

end


locale Unreachability_Invariant_defs =
  fixes E :: "'a \<Rightarrow> 'a \<Rightarrow> bool" and P :: "'a \<Rightarrow> bool"
    and less_eq :: "'a \<Rightarrow> 'a set \<Rightarrow> bool" (infix "\<preceq>" 50)
    and I :: "'a \<Rightarrow> bool" and SE :: "'a \<Rightarrow> 'a set \<Rightarrow> bool"
begin

sublocale Unreachability_Invariant_pre_defs .

definition Subsumed' where
  "Subsumed' S T \<equiv> \<forall>s \<in> S. \<exists>T' \<subseteq> T. SE s T'"

notation Subsumed' (infix "\<sqsubseteq>''" 50)

definition Inv where
  "Inv T \<equiv> \<forall>t \<in> T. I t"

definition Step' where
  "Step' S T \<equiv> \<exists>S'. Step S S' \<and> S' \<sqsubseteq>' T \<and> Inv T"

end

locale Unreachability_Invariant =
  Unreachability_Invariant_defs +
  assumes mono: "a \<preceq> B \<Longrightarrow> E a a' \<Longrightarrow> P a \<Longrightarrow> (\<forall>b \<in> B. P b)
    \<Longrightarrow> \<exists>B'. (\<forall>b' \<in> B'. \<exists>b \<in> B. E b b') \<and> a' \<preceq> B'"
  assumes S_E_subsumed: "I s \<Longrightarrow> E s t \<Longrightarrow> \<exists> T. (\<forall>t' \<in> T. I t') \<and> SE t T"
  assumes subsumptions_subsume: "SE s T \<Longrightarrow> s \<preceq> T"
  assumes I_P[intro]: "I s \<Longrightarrow> P s"
  assumes P_invariant: "P a \<Longrightarrow> E a a' \<Longrightarrow> P a'"
  assumes subsumes_Subsumed: "a \<preceq> A \<Longrightarrow> A \<sqsubseteq> A' \<Longrightarrow> a \<preceq> A'"
begin

interpretation Graph_Invariant E P
  by standard (rule P_invariant)

interpretation BB: Graph_Invariant "\<lambda>B B'. \<forall>b' \<in> B'. \<exists>b \<in> B. E b b'" "\<lambda>B. \<forall>b \<in> B. P b"
  by standard (auto 4 3 intro: invariant)

lemma S_E_subsumed':
  assumes "Inv S" "S \<rightarrow>' T" shows "\<exists> T'. Inv T' \<and> T \<sqsubseteq>' T'"
proof -
  define T' where "T' \<equiv> \<lambda>t. SOME T'. SE t T' \<and> Inv T'"
  have "SE t (T' t) \<and> Inv (T' t)" if "t \<in> T" for t
    using S_E_subsumed that assms unfolding T'_def Step_def Inv_def by - (rule someI_ex, blast)
  then show ?thesis
    unfolding Step_def Inv_def Subsumed'_def by (inst_existentials "\<Union>t \<in> T. T' t"; blast)
qed

lemma Subsumed'_Subsumed:
  "A \<sqsubseteq> A'" if "A \<sqsubseteq>' A'"
  using that unfolding Subsumed_def Subsumed'_def by (blast intro: subsumptions_subsume)

lemma subsumes_Subsumed':
  assumes "a \<preceq> A" "A \<sqsubseteq>' A'" shows "a \<preceq> A'"
  using assms by (elim subsumes_Subsumed Subsumed'_Subsumed)

interpretation Simulation_Invariant E Step' "(\<preceq>)" P Inv
proof standard
  fix a b :: \<open>'a\<close> and A
  assume \<open>a \<rightarrow> b\<close> \<open>P a\<close> \<open>Inv A\<close> \<open>a \<preceq> A\<close>
  with mono[OF \<open>a \<preceq> A\<close> \<open>a \<rightarrow> b\<close>] obtain B where "b \<preceq> B" "\<forall>b'\<in>B. \<exists>a\<in>A. a \<rightarrow> b'"
    by (auto simp: Inv_def)
  then have "b \<preceq> B" "A \<rightarrow>' B"
    by (auto simp: Step_def)
  with S_E_subsumed'[OF \<open>Inv A\<close>] \<open>a \<preceq> A\<close> \<open>P a\<close> obtain C where "Inv C" "B \<sqsubseteq>' C"
    by auto
  with \<open>A \<rightarrow>' B\<close> have "Step' A C"
    unfolding Step'_def by auto
  with \<open>b \<preceq> B\<close> \<open>B \<sqsubseteq>' C\<close> subsumptions_subsume show \<open>\<exists>b'. Step' A b' \<and> b \<preceq> b'\<close>
    by (blast intro: subsumes_Subsumed')
qed (auto simp: Step'_def P_invariant)

\<comment> \<open>Not really necessary\<close>
sublocale Post: Simulation_Graph_Poststable
  where C = E
    and A = Step
  by standard (auto simp: Step_def)



context
  fixes s\<^sub>0 S\<^sub>0
  assumes "s\<^sub>0 \<preceq> S\<^sub>0" "P s\<^sub>0" "Inv S\<^sub>0"
begin

lemma run_subsumed:
  assumes "run (s\<^sub>0 ## xs)"
  obtains ys where "B.run (S\<^sub>0 ## ys)" "stream_all2 (\<preceq>) xs ys" "pred_stream Inv ys"
proof -
  from \<open>s\<^sub>0 \<preceq> _\<close> \<open>P s\<^sub>0\<close> \<open>Inv S\<^sub>0\<close> have "equiv' s\<^sub>0 S\<^sub>0"
    unfolding equiv'_def by auto
  with assms show ?thesis
    by - (drule simulation_run, auto
          dest: PB_invariant.invariant_run elim: stream_all2_weaken intro!: that simp: equiv'_def)
qed

context
  fixes F :: "'a \<Rightarrow> bool" \<comment> \<open>Final states\<close>
  assumes F_mono[intro]: "P a \<Longrightarrow> F a \<Longrightarrow> a \<preceq> B \<Longrightarrow> \<forall>b \<in> B. P b \<Longrightarrow> \<exists>b \<in> B. F b"
begin

corollary final_unreachable:
  "\<nexists> s'. reaches s\<^sub>0 s' \<and> F s'" if "\<forall>s'. I s' \<longrightarrow> \<not> F s'"
  using \<open>s\<^sub>0 \<preceq> _\<close> \<open>P s\<^sub>0\<close> \<open>Inv S\<^sub>0\<close> simulation_reaches that I_P F_mono unfolding Inv_def by metis

lemma buechi_run_lasso:
  assumes "finite {s. I s}" "run (s\<^sub>0 ## xs)" "alw (ev (holds F)) (s\<^sub>0 ## xs)"
  obtains s where "B.reaches S\<^sub>0 s" "B.reaches1 s s" "\<exists>s' \<in> s. F s'"
proof -
  interpret Finite: Finite_Graph Step' S\<^sub>0
    by (standard, rule finite_subset[OF _ assms(1)[THEN finite_Collect_subsets]])
       (auto dest: PB_invariant.invariant_reaches[OF _ \<open>Inv S\<^sub>0\<close>] simp: Inv_def)
  from run_subsumed[OF assms(2)] obtain ys where ys:
    "B.run (S\<^sub>0 ## ys)" "stream_all2 (\<preceq>) xs ys" "pred_stream Inv ys" .
  moreover from \<open>run _\<close> have "pred_stream P xs"
    using \<open>P s\<^sub>0\<close> invariant_run by auto
  ultimately have "stream_all2 (\<lambda>x y. x \<preceq> y \<and> P x \<and> Inv y) xs ys"
    by (smt stream.pred_set stream.rel_mono_strong)
  with assms(3) \<open>s\<^sub>0 \<preceq> _\<close> \<open>P s\<^sub>0\<close> \<open>Inv S\<^sub>0\<close> have "alw (ev (holds (\<lambda>S. \<exists>s \<in> S. F s))) (S\<^sub>0 ## ys)"
    by (elim alw_ev_lockstep) (erule stream.rel_intros[rotated], auto simp: I_P Inv_def)
  from Finite.buechi_run_lasso[OF ys(1) this] show ?thesis
    using that .
qed

end (* Context for property *)

end (* Start state *)

end (* Unreachability Invariant *)

context Simulation_Graphs_Certification.Unreachability_Invariant1
begin

interpretation Unreachability_Invariant
  where less_eq = "\<lambda>s S. \<exists>s'. S = {s'} \<and> s \<preceq> s'"
    and SE = "\<lambda>s S. \<exists>s'. S = {s'} \<and> SE s s'"
  apply standard
  subgoal premises prems for a B a'
    using prems apply -
    by (metis mono singletonD singletonI)

subgoal premises prems for s t
  using prems apply -
  sorry

subgoal premises prems for s T
  using prems apply -
  sorry

subgoal premises prems for s
  using prems apply -
  sorry

subgoal premises prems for a a'
  using prems apply -
  sorry

subgoal premises prems for a A A'
  using prems apply -
  unfolding Unreachability_Invariant_pre_defs.Subsumed_def
  apply auto
  oops

end

end