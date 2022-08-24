theory Labeled_Graphs
  imports TA_Library.Graphs \<^cancel>\<open>"Transition_Systems_and_Automata.Sequence_LTL"\<close>
begin

locale Graph_Defs =
  fixes E :: "'a \<Rightarrow> 'l \<Rightarrow> 'a \<Rightarrow> bool"
begin

abbreviation "E\<^sub>u \<equiv> \<lambda>a b. \<exists> l. E a l b"

sublocale UL: Graphs.Graph_Defs E\<^sub>u .

end

locale Simulation_Defs =
  fixes A :: "'a \<Rightarrow> 'l \<Rightarrow> 'a \<Rightarrow> bool" and B :: "'b \<Rightarrow> 'l \<Rightarrow> 'b \<Rightarrow> bool"
    and sim :: "'a \<Rightarrow> 'b \<Rightarrow> bool" (infixr "\<sim>" 60)
begin

sublocale A: Graph_Defs A .

sublocale B: Graph_Defs B .

sublocale UL: Graphs.Simulation_Defs A.E\<^sub>u B.E\<^sub>u sim .

end

locale Simulation = Simulation_Defs +
  assumes A_B_step: "\<And> l a b a'. A a l b \<Longrightarrow> a \<sim> a' \<Longrightarrow> (\<exists> b'. B a' l b' \<and> b \<sim> b')"
begin

\<^cancel>\<open>lemma simulation_reaches:
  "\<exists> b'. B\<^sup>*\<^sup>* b l b' \<and> a' \<sim> b'" if "A\<^sup>*\<^sup>* a l a'" "a \<sim> b"
  using that by (induction rule: rtranclp_induct) (auto intro: rtranclp.intros(2) dest: A_B_step)

lemma simulation_reaches1:
  "\<exists> b'. B\<^sup>+\<^sup>+ b b' \<and> a' \<sim> b'" if "A\<^sup>+\<^sup>+ a a'" "a \<sim> b"
  using that by (induction rule: tranclp_induct) (auto 4 3 intro: tranclp.intros(2) dest: A_B_step)

lemma simulation_steps:
  "\<exists> bs. B.steps (b # bs) \<and> list_all2 (\<lambda> a b. a \<sim> b) as bs" if "A.steps (a # as)" "a \<sim> b"
  using that
  apply (induction "a # as" arbitrary: a b as)
   apply force
  apply (frule A_B_step, auto)
  done

lemma simulation_run:
  "\<exists> ys. B.run (y ## ys) \<and> stream_all2 (\<sim>) xs ys" if "A.run (x ## xs)" "x \<sim> y"
proof -
  let ?ys = "sscan (\<lambda> a' b. SOME b'. B b b' \<and> a' \<sim> b') xs y"
  have "B.run (y ## ?ys)"
    using that by (coinduction arbitrary: x y xs) (force dest!: someI_ex A_B_step elim: A.run.cases)
  moreover have "stream_all2 (\<sim>) xs ?ys"
    using that by (coinduction arbitrary: x y xs) (force dest!: someI_ex A_B_step elim: A.run.cases)
  ultimately show ?thesis by blast
qed\<close>

sublocale UL: Graphs.Simulation A.E\<^sub>u B.E\<^sub>u sim
  by standard (blast dest: A_B_step)

end (* Simulation *)

locale Graph_Invariant = Graph_Defs +
  fixes P :: "'a \<Rightarrow> bool"
  assumes invariant: "P a \<Longrightarrow> E a l b \<Longrightarrow> P b"
begin

sublocale UL: Graphs.Graph_Invariant E\<^sub>u
  by standard (blast dest: invariant)

\<^cancel>\<open>lemma invariant_steps:
  "list_all P as" if "steps (a # as)" "P a"
  using that by (induction "a # as" arbitrary: as a) (auto intro: invariant)

lemma invariant_reaches:
  "P b" if "a \<rightarrow>* b" "P a"
  using that by (induction; blast intro: invariant)

lemma invariant_run:
  assumes run: "run (x ## xs)" and P: "P x"
  shows "pred_stream P (x ## xs)"
  using run P by (coinduction arbitrary: x xs) (auto 4 3 elim: invariant run.cases)

text \<open>Every graph invariant induces a subgraph.\<close>
sublocale Subgraph_Node_Defs where E = E and V = P .

lemma subgraph':
  assumes "x \<rightarrow> y" "P x"
  shows "E' x y"
  using assms by (intro subgraph') (auto intro: invariant)

lemma invariant_steps_iff:
  "G'.steps (v # vs) \<longleftrightarrow> steps (v # vs)" if "P v"
  apply (rule iffI)
  subgoal
    using G'.steps_alt_induct steps_appendI by blast
  subgoal premises prems
    using prems \<open>P v\<close> by (induction "v # vs" arbitrary: v vs) (auto intro: subgraph' invariant)
  done

lemma invariant_reaches_iff:
  "G'.reaches u v \<longleftrightarrow> reaches u v" if "P u"
  using that by (simp add: reaches_steps_iff2 G'.reaches_steps_iff2 invariant_steps_iff)

lemma invariant_reaches1_iff:
  "G'.reaches1 u v \<longleftrightarrow> reaches1 u v" if "P u"
  using that by (simp add: reaches1_steps_iff G'.reaches1_steps_iff invariant_steps_iff)\<close>

end (* Graph Invariant *)

locale Graph_Invariants = Graph_Defs +
  fixes P Q :: "'a \<Rightarrow> bool"
  assumes invariant: "P a \<Longrightarrow> E a l b \<Longrightarrow> Q b" and Q_P: "Q a \<Longrightarrow> P a"
begin

sublocale Pre: Graph_Invariant E P
  by standard (blast intro: invariant Q_P)

sublocale Post: Graph_Invariant E Q
  by standard (blast intro: invariant Q_P)

\<^cancel>\<open>
lemma invariant_steps:
  "list_all Q as" if "steps (a # as)" "P a"
  using that by (induction "a # as" arbitrary: as a) (auto intro: invariant Q_P)

lemma invariant_run:
  assumes run: "run (x ## xs)" and P: "P x"
  shows "pred_stream Q xs"
  using run P by (coinduction arbitrary: x xs) (auto 4 4 elim: invariant run.cases intro: Q_P)

lemma invariant_reaches1:
  "Q b" if "a \<rightarrow>\<^sup>+ b" "P a"
  using that by (induction; blast intro: invariant Q_P)\<close>

end (* Graph Invariants *)

locale Simulation_Invariant = Simulation_Defs A B sim
  for A :: "'a \<Rightarrow> 'l \<Rightarrow> 'a \<Rightarrow> bool"
  and B :: "'b \<Rightarrow> 'l \<Rightarrow> 'b \<Rightarrow> bool"
  and sim :: "'a \<Rightarrow> 'b \<Rightarrow> bool" (infixr "\<sim>" 60) +
  fixes PA :: "'a \<Rightarrow> bool" and PB :: "'b \<Rightarrow> bool"
  assumes A_B_step:
    "\<And> l a b a'. A a l b \<Longrightarrow> PA a \<Longrightarrow> PB a' \<Longrightarrow> a \<sim> a' \<Longrightarrow> (\<exists>b'. B a' l b' \<and> b \<sim> b')"
  assumes A_invariant[intro]: "\<And> l a b. PA a \<Longrightarrow> A a l b \<Longrightarrow> PA b"
  assumes B_invariant[intro]: "\<And> l a b. PB a \<Longrightarrow> B a l b \<Longrightarrow> PB b"
begin

definition "equiv' \<equiv> \<lambda> a b. a \<sim> b \<and> PA a \<and> PB b"

sublocale Simulation A B equiv' by standard (auto dest: A_B_step simp: equiv'_def)

sublocale PA_invariant: Graph_Invariant A PA by standard blast

sublocale PB_invariant: Graph_Invariant B PB by standard blast

\<^cancel>\<open>lemma simulation_reaches:
  "\<exists> b'. B\<^sup>*\<^sup>* b b' \<and> a' \<sim> b' \<and> PA a' \<and> PB b'" if "A\<^sup>*\<^sup>* a a'" "a \<sim> b" "PA a" "PB b"
  using simulation_reaches[of a a' b] that unfolding equiv'_def by simp

lemma simulation_steps:
  "\<exists> bs. B.steps (b # bs) \<and> list_all2 (\<lambda> a b. a \<sim> b \<and> PA a \<and> PB b) as bs"
  if "A.steps (a # as)" "a \<sim> b" "PA a" "PB b"
  using simulation_steps[of a as b] that unfolding equiv'_def by simp

lemma simulation_steps':
  "\<exists> bs. B.steps (b # bs) \<and> list_all2 (\<lambda> a b. a \<sim> b) as bs \<and> list_all PA as \<and> list_all PB bs"
  if "A.steps (a # as)" "a \<sim> b" "PA a" "PB b"
  using simulation_steps[OF that]
  by (force dest: list_all2_set1 list_all2_set2 simp: list_all_iff elim: list_all2_mono)

context
  fixes f
  assumes eq: "a \<sim> b \<Longrightarrow> b = f a"
begin

lemma simulation_steps'_map:
  "\<exists> bs.
    B.steps (b # bs) \<and> bs = map f as
    \<and> list_all2 (\<lambda> a b. a \<sim> b) as bs
    \<and> list_all PA as \<and> list_all PB bs"
  if "A.steps (a # as)" "a \<sim> b" "PA a" "PB b"
proof -
  from simulation_steps'[OF that] obtain bs where guessed:
    "B.steps (b # bs)"
    "list_all2 (\<sim>) as bs"
    "list_all PA as"
    "list_all PB bs"
    by safe
  from this(2) have "bs = map f as"
    by (induction; simp add: eq)
  with guessed show ?thesis
    by auto
qed\<close>

\<^cancel>\<open>end (* Context for Equality Relation *)\<close>

end (* Simulation Invariant *)

locale Simulation_Invariants = Simulation_Defs A B sim
  for A :: "'a \<Rightarrow> 'l \<Rightarrow> 'a \<Rightarrow> bool"
  and B :: "'b \<Rightarrow> 'l \<Rightarrow> 'b \<Rightarrow> bool"
  and sim :: "'a \<Rightarrow> 'b \<Rightarrow> bool" (infixr "\<sim>" 60) +
  fixes PA QA :: "'a \<Rightarrow> bool" and PB QB :: "'b \<Rightarrow> bool"
  assumes A_B_step:
    "\<And> a b l a'. A a l b \<Longrightarrow> PA a \<Longrightarrow> PB a' \<Longrightarrow> a \<sim> a' \<Longrightarrow> (\<exists> b'. B a' l b' \<and> b \<sim> b')"
  assumes A_invariant[intro]: "\<And> a b. PA a \<Longrightarrow> A a l b \<Longrightarrow> QA b"
  assumes B_invariant[intro]: "\<And> a b. PB a \<Longrightarrow> B a l b \<Longrightarrow> QB b"
  assumes PA_QA[intro]: "\<And> a. QA a \<Longrightarrow> PA a" and PB_QB[intro]: "\<And> a. QB a \<Longrightarrow> PB a"
begin
print_locale Simulation_Invariant
sublocale Pre: Simulation_Invariant A B "(\<sim>)" PA PB
  by standard (auto intro: A_B_step)

sublocale Post: Simulation_Invariant A B "(\<sim>)" QA QB
  by standard (auto intro: A_B_step)

sublocale A_invs: Graph_Invariants A PA QA
  by standard auto

sublocale B_invs: Graph_Invariants B PB QB
  by standard auto

\<^cancel>\<open>lemma simulation_reaches1:
  "\<exists> b2. B.reaches1 b1 b2 \<and> a2 \<sim> b2 \<and> QB b2" if "A.reaches1 a1 a2" "a1 \<sim> b1" "PA a1" "PB b1"
  using that
  by - (drule Pre.simulation_reaches1, auto intro: B_invs.invariant_reaches1 simp: Pre.equiv'_def)

lemma reaches1_unique:
  assumes unique: "\<And> b2. a \<sim> b2 \<Longrightarrow> QB b2 \<Longrightarrow> b2 = b"
    and that: "A.reaches1 a a" "a \<sim> b" "PA a" "PB b"
  shows "B.reaches1 b b"
  using that by (auto dest: unique simulation_reaches1)\<close>

end (* Simualation Invariants *)

locale Bisimulation = Simulation_Defs +
  assumes A_B_step: "\<And> l a b a'. A a l b \<Longrightarrow> a \<sim> a' \<Longrightarrow> (\<exists> b'. B a' l b' \<and> b \<sim> b')"
  assumes B_A_step: "\<And> l a a' b'. B a' l b' \<Longrightarrow> a \<sim> a' \<Longrightarrow> (\<exists> b. A a l b \<and> b \<sim> b')"
begin

sublocale A_B: Simulation A B "(\<sim>)" by standard (rule A_B_step)

sublocale B_A: Simulation B A "\<lambda> x y. y \<sim> x" by standard (rule B_A_step)

\<^cancel>\<open>lemma A_B_reaches:
  "\<exists> b'. B\<^sup>*\<^sup>* b b' \<and> a' \<sim> b'" if "A\<^sup>*\<^sup>* a a'" "a \<sim> b"
  using A_B.simulation_reaches[OF that] .

lemma B_A_reaches:
  "\<exists> b'. A\<^sup>*\<^sup>* b b' \<and> b' \<sim> a'" if "B\<^sup>*\<^sup>* a a'" "b \<sim> a"
  using B_A.simulation_reaches[OF that] .\<close>

end (* Bisim *)

locale Bisimulation_Invariant = Simulation_Defs A B sim
  for A :: "'a \<Rightarrow> 'l \<Rightarrow> 'a \<Rightarrow> bool"
  and B :: "'b \<Rightarrow> 'l \<Rightarrow> 'b \<Rightarrow> bool"
  and sim :: "'a \<Rightarrow> 'b \<Rightarrow> bool" (infixr "\<sim>" 60) +
  fixes PA :: "'a \<Rightarrow> bool" and PB :: "'b \<Rightarrow> bool"
  assumes A_B_step: "\<And> l a b a'. A a l b \<Longrightarrow> a \<sim> a' \<Longrightarrow> PA a \<Longrightarrow> PB a' \<Longrightarrow> (\<exists> b'. B a' l b' \<and> b \<sim> b')"
  assumes B_A_step: "\<And> l a a' b'. B a' l b' \<Longrightarrow> a \<sim> a' \<Longrightarrow> PA a \<Longrightarrow> PB a' \<Longrightarrow> (\<exists> b. A a l b \<and> b \<sim> b')"
  assumes A_invariant[intro]: "\<And> l a b. PA a \<Longrightarrow> A a l b \<Longrightarrow> PA b"
  assumes B_invariant[intro]: "\<And> l a b. PB a \<Longrightarrow> B a l b \<Longrightarrow> PB b"
begin

sublocale PA_invariant: Graph_Invariant A PA by standard blast

sublocale PB_invariant: Graph_Invariant B PB by standard blast

\<^cancel>\<open>lemmas B_steps_invariant[intro] = PB_invariant.invariant_reaches\<close>

definition "equiv' \<equiv> \<lambda> a b. a \<sim> b \<and> PA a \<and> PB b"

sublocale bisim: Bisimulation A B equiv'
  by standard (clarsimp simp add: equiv'_def, frule A_B_step B_A_step, assumption; auto)+

sublocale A_B: Simulation_Invariant A B "(\<sim>)" PA PB
  by (standard; blast intro: A_B_step B_A_step)

sublocale B_A: Simulation_Invariant B A "\<lambda> x y. y \<sim> x" PB PA
  by (standard; blast intro: A_B_step B_A_step)

\<^cancel>\<open>context
  fixes f
  assumes eq: "a \<sim> b \<longleftrightarrow> b = f a"
    and inj: "\<forall> a b. PB (f a) \<and> PA b \<and> f a = f b \<longrightarrow> a = b"
begin

lemma list_all2_inj_map_eq:
  "as = bs" if "list_all2 (\<lambda>a b. a = f b) (map f as) bs" "list_all PB (map f as)" "list_all PA bs"
  using that inj
  by (induction "map f as" bs arbitrary: as rule: list_all2_induct) (auto simp: inj_on_def)

lemma steps_map_equiv:
  "A.steps (a # as) \<longleftrightarrow> B.steps (b # map f as)" if "a \<sim> b" "PA a" "PB b"
  using A_B.simulation_steps'_map[of f a as b] B_A.simulation_steps'[of b "map f as" a] that eq
  by (auto dest: list_all2_inj_map_eq)

lemma steps_map:
  "\<exists> as. bs = map f as" if "B.steps (f a # bs)" "PA a" "PB (f a)"
proof -
  have "a \<sim> f a" unfolding eq ..
  from B_A.simulation_steps'[OF that(1) this \<open>PB _\<close> \<open>PA _\<close>] obtain as where
    "A.steps (a # as)"
    "list_all2 (\<lambda>a b. b \<sim> a) bs as"
    "list_all PB bs"
    "list_all PA as"
    by safe
  from this(2) show ?thesis
    unfolding eq by (inst_existentials as, induction rule: list_all2_induct, auto)
qed

lemma reaches_equiv:
  "A.reaches a a' \<longleftrightarrow> B.reaches (f a) (f a')" if "PA a" "PB (f a)"
  apply safe
   apply (drule A_B.simulation_reaches[of a a' "f a"]; simp add: eq that)
  apply (drule B_A.simulation_reaches)
     defer
     apply (rule that | clarsimp simp: eq | metis inj)+
  done

end (* Context for Equality Relation *)\<close>

lemma equiv'_D:
  "a \<sim> b" if "A_B.equiv' a b"
  using that unfolding A_B.equiv'_def by auto

lemma equiv'_rotate_1:
  "B_A.equiv' b a" if "A_B.equiv' a b"
  using that by (auto simp: B_A.equiv'_def A_B.equiv'_def)

lemma equiv'_rotate_2:
  "A_B.equiv' a b" if "B_A.equiv' b a"
  using that by (auto simp: B_A.equiv'_def A_B.equiv'_def)

lemma stream_all2_equiv'_D:
  "stream_all2 (\<sim>) xs ys" if "stream_all2 A_B.equiv' xs ys"
  using stream_all2_weaken[OF that equiv'_D] by fast

lemma stream_all2_equiv'_D2:
  "stream_all2 B_A.equiv' ys xs \<Longrightarrow> stream_all2 ((\<sim>)\<inverse>\<inverse>) ys xs"
  by (coinduction arbitrary: xs ys) (auto simp: B_A.equiv'_def)

lemma stream_all2_rotate_1:
  "stream_all2 B_A.equiv' ys xs \<Longrightarrow> stream_all2 A_B.equiv' xs ys"
  by (coinduction arbitrary: xs ys) (auto simp: B_A.equiv'_def A_B.equiv'_def)

lemma stream_all2_rotate_2:
  "stream_all2 A_B.equiv' xs ys \<Longrightarrow> stream_all2 B_A.equiv' ys xs"
  by (coinduction arbitrary: xs ys) (auto simp: B_A.equiv'_def A_B.equiv'_def)

end (* Bisim Invariant *)

lemma Bisimulation_Invariant_composition:
  assumes
    "Bisimulation_Invariant A B sim1 PA PB"
    "Bisimulation_Invariant B C sim2 PB PC"
  shows
    "Bisimulation_Invariant A C (\<lambda> a c. \<exists> b. PB b \<and> sim1 a b \<and> sim2 b c) PA PC"
proof -
  interpret A: Bisimulation_Invariant A B sim1 PA PB
    by (rule assms(1))
  interpret B: Bisimulation_Invariant B C sim2 PB PC
    by (rule assms(2))
  show ?thesis
    by (standard; (blast dest: A.A_B_step B.A_B_step | blast dest: A.B_A_step B.B_A_step))
qed

lemma Bisimulation_Invariant_filter:
  assumes
    "Bisimulation_Invariant A B sim PA PB"
    "\<And> l a b. sim a b \<Longrightarrow> PA a \<Longrightarrow> PB b \<Longrightarrow> FA a \<longleftrightarrow> FB b"
    "\<And> l a b. A a l b \<and> FA b \<longleftrightarrow> A' a l b"
    "\<And> l a b. B a l b \<and> FB b \<longleftrightarrow> B' a l b"
  shows
    "Bisimulation_Invariant A' B' sim PA PB"
proof -
  interpret Bisimulation_Invariant A B sim PA PB
    by (rule assms(1))
  have unfold:
    "A' = (\<lambda> a l b. A a l b \<and> FA b)" "B' = (\<lambda> a l b. B a l b \<and> FB b)"
    using assms(3,4) by auto
  show ?thesis
    unfolding unfold
    apply standard
    using assms(2) apply (blast dest: A_B_step)
    using assms(2) apply (blast dest: B_A_step)
    by blast+
qed


lemma Bisimulation_Invariant_strengthen_post:
  assumes
    "Bisimulation_Invariant A B sim PA PB"
    "\<And> l a b. PA' a \<Longrightarrow> PA b \<Longrightarrow> A a l b \<Longrightarrow> PA' b"
    "\<And> a. PA' a \<Longrightarrow> PA a"
  shows "Bisimulation_Invariant A B sim PA' PB"
proof -
  interpret Bisimulation_Invariant A B sim PA PB
    by (rule assms)
  show ?thesis
    by (standard; blast intro: A_B_step B_A_step assms)
qed

lemma Bisimulation_Invariant_strengthen_post':
  assumes
    "Bisimulation_Invariant A B sim PA PB"
    "\<And> l a b. PB' a \<Longrightarrow> PB b \<Longrightarrow> B a l b \<Longrightarrow> PB' b"
    "\<And> a. PB' a \<Longrightarrow> PB a"
  shows "Bisimulation_Invariant A B sim PA PB'"
proof -
  interpret Bisimulation_Invariant A B sim PA PB
    by (rule assms)
  show ?thesis
    by (standard; blast intro: A_B_step B_A_step assms)
qed

lemma Simulation_Invariant_strengthen_post:
  assumes
    "Simulation_Invariant A B sim PA PB"
    "\<And> l a b. PA a \<Longrightarrow> PA b \<Longrightarrow> A a l b \<Longrightarrow> PA' b"
    "\<And> a. PA' a \<Longrightarrow> PA a"
  shows "Simulation_Invariant A B sim PA' PB"
proof -
  interpret Simulation_Invariant A B sim PA PB
    by (rule assms)
  show ?thesis
    by (standard; blast intro: A_B_step assms)
qed

lemma Simulation_Invariant_strengthen_post':
  assumes
    "Simulation_Invariant A B sim PA PB"
    "\<And> l a b. PB a \<Longrightarrow> PB b \<Longrightarrow> B a l b \<Longrightarrow> PB' b"
    "\<And> a. PB' a \<Longrightarrow> PB a"
  shows "Simulation_Invariant A B sim PA PB'"
proof -
  interpret Simulation_Invariant A B sim PA PB
    by (rule assms)
  show ?thesis
    by (standard; blast intro: A_B_step assms)
qed

lemma Simulation_Invariants_strengthen_post:
  assumes
    "Simulation_Invariants A B sim PA QA PB QB"
    "\<And> l a b. PA a \<Longrightarrow> QA b \<Longrightarrow> A a l b \<Longrightarrow> QA' b"
    "\<And> a. QA' a \<Longrightarrow> QA a"
  shows "Simulation_Invariants A B sim PA QA' PB QB"
proof -
  interpret Simulation_Invariants A B sim PA QA PB QB
    by (rule assms)
  show ?thesis
    by (standard; blast intro: A_B_step assms)
qed

lemma Simulation_Invariants_strengthen_post':
  assumes
    "Simulation_Invariants A B sim PA QA PB QB"
    "\<And> l a b. PB a \<Longrightarrow> QB b \<Longrightarrow> B a l b \<Longrightarrow> QB' b"
    "\<And> a. QB' a \<Longrightarrow> QB a"
  shows "Simulation_Invariants A B sim PA QA PB QB'"
proof -
  interpret Simulation_Invariants A B sim PA QA PB QB
    by (rule assms)
  show ?thesis
    by (standard; blast intro: A_B_step assms)
qed

lemma Bisimulation_Invariant_sim_replace:
  assumes "Bisimulation_Invariant A B sim PA PB"
      and "\<And> a b. PA a \<Longrightarrow> PB b \<Longrightarrow> sim a b \<longleftrightarrow> sim' a b"
    shows "Bisimulation_Invariant A B sim' PA PB"
proof -
  interpret Bisimulation_Invariant A B sim PA PB
    by (rule assms(1))
  from assms(2) show ?thesis
    apply unfold_locales
    using assms(2) apply (blast dest: A_B_step)
    using assms(2) apply (blast dest: B_A_step)
    by blast+
qed

lemma (in Bisimulation) Bisimulation_Bisimulation_Invariant:
  shows "Bisimulation_Invariant A B sim (\<lambda>_. True) (\<lambda>_. True)"
  by standard (auto intro: A_B_step B_A_step)

lemma Simulation_Invariant_composition:
  assumes
    "Simulation_Invariant A B sim1 PA PB"
    "Simulation_Invariant B C sim2 PB PC"
  shows
    "Simulation_Invariant A C (\<lambda> a c. \<exists> b. PB b \<and> sim1 a b \<and> sim2 b c) PA PC"
proof -
  interpret A: Simulation_Invariant A B sim1 PA PB
    by (rule assms(1))
  interpret B: Simulation_Invariant B C sim2 PB PC
    by (rule assms(2))
  show ?thesis
    by (standard; (blast dest: A.A_B_step B.A_B_step))
qed

lemma (in Simulation) Simulation_Invariant:
  "Simulation_Invariant A B sim (\<lambda>_. True) (\<lambda>_. True)"
  by unfold_locales (rule A_B_step)

lemma Simulation_Invariant_sim_replace:
  assumes "Simulation_Invariant A B sim PA PB"
      and "\<And> a b. PA a \<Longrightarrow> PB b \<Longrightarrow> sim a b \<longleftrightarrow> sim' a b"
    shows "Simulation_Invariant A B sim' PA PB"
proof -
  interpret Simulation_Invariant A B sim PA PB
    by (rule assms(1))
  from assms(2) show ?thesis
    by (unfold_locales; blast dest: A_B_step)
qed

end