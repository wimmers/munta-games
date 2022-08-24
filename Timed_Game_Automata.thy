theory Timed_Game_Automata
  imports TA.Timed_Automata TA_Games_Misc "~/Code/explorer/Guess_Explore"
begin

paragraph \<open>Basic Definitions\<close>

datatype 'a move = Act 'a | Wait

type_synonym ('c, 't, 's) ta_config = "'s \<times> ('c, 't) cval"

\<comment> \<open>We only consider memoryless strategies:\<close>
type_synonym ('a, 'c, 't, 's) strategy =
  "('c, 't, 's) ta_config \<Rightarrow> 'a move set"

locale Timed_Game_Automaton =
  fixes A :: "('a, 'c, 't :: time, 's) ta"
    and controllable :: "'a \<Rightarrow> bool"
    and strategy :: "('a, 'c, 't, 's) strategy"
begin

inductive step where
  action: "step (l, u) (l', u')"
  if "A \<turnstile> \<langle>l, u\<rangle> \<rightarrow>\<^bsub>a\<^esub> \<langle>l', u'\<rangle>" "controllable a" "Act a \<in> strategy (l, u)"
| wait: "step (l, u) (l', u')"
  if "A \<turnstile> \<langle>l, u\<rangle> \<rightarrow>\<^bsup>d\<^esup> \<langle>l',u'\<rangle>" "Wait \<in> strategy (l, u)"
    "\<forall>d' < d. \<exists> l' u'. A \<turnstile> \<langle>l, u\<rangle> \<rightarrow>\<^bsup>d'\<^esup> \<langle>l', u'\<rangle> \<and> Wait \<in> strategy (l', u')"
| uncontrolled: "step (l, u) (l', u')"
  if "A \<turnstile> \<langle>l, u\<rangle> \<rightarrow>\<^bsub>a\<^esub> \<langle>l', u'\<rangle>" "\<not> controllable a"

sublocale Graph_Defs step .

\<comment> \<open>XXX: Q: why are these not automatically activated? Why are there no bundles?\<close>
notation step ("_ \<rightarrow> _" [100, 100] 40)

notation reaches ("_ \<rightarrow>* _" [100, 100] 40)

term "reaches x y"

end




locale Timed_Reachability_Game =
  fixes A :: "('a, 'c, 't :: time, 's) ta"
    and controllable :: "'a \<Rightarrow> bool"
  fixes K :: "('c, 't, 's) ta_config set"
begin

definition
  "lost \<equiv> \<lambda>(l, u). \<forall>a l' u'. A \<turnstile> \<langle>l, u\<rangle> \<rightarrow>\<^bsub>a\<^esub> \<langle>l', u'\<rangle> \<longrightarrow> \<not> controllable a"

definition
  "terminal x \<longleftrightarrow> lost x \<or> x \<in> K"

definition
  "maximal xs \<longleftrightarrow> xs \<noteq> [] \<and> terminal (last xs) \<and> (\<forall>x \<in> set (butlast xs). \<not> terminal x)"

lemma maximal_single_eq_terminal [simp]:
  "maximal [x] \<longleftrightarrow> terminal x"
  unfolding maximal_def by simp

lemma maximal_terminal_startD:
  "xs = []" if "maximal (x # xs)" "terminal x"
  using that unfolding maximal_def by (auto split: if_split_asm)

context
  fixes strategy :: "('a, 'c, 't, 's) strategy"
begin

interpretation Timed_Game_Automaton A controllable strategy .

definition
  "no_runs_from x \<longleftrightarrow> (\<forall>\<omega>. run (x ## \<omega>) \<longrightarrow> 
      (\<exists>xs \<omega>'. \<omega> = xs @- \<omega>' \<and> maximal (x # xs)))"

lemma maximal_Cons_iff:
  "maximal (x # xs) \<longleftrightarrow> terminal x \<and> xs = [] \<or> \<not> terminal x \<and> maximal xs"
  unfolding maximal_def by auto

\<comment> \<open>We show: \<open>no_runs_from x \<longleftrightarrow> x \<turnstile> F terminal\<close>.\<close>
lemma no_runs_from_def1:
  "no_runs_from x \<longleftrightarrow> (\<forall>\<omega>. run (x ## \<omega>) \<longrightarrow> ev (holds terminal) (x ## \<omega>))"
proof -
  have "\<exists>xs \<omega>'. \<omega> = xs @- \<omega>' \<and> maximal (x # xs)" if "ev (holds terminal) (x ## \<omega>)" for \<omega>
    using that
  proof (induction "x ## \<omega>" arbitrary: x \<omega> rule: ev_induct_strong)
    case base
    then show ?case
      unfolding holds.simps maximal_def by simp
  next
    case step
    from step(3)[of "shd \<omega>" "stl \<omega>"] obtain xs \<omega>' where
      "maximal (shd \<omega> # xs)" "stl \<omega> = xs @- \<omega>'"
      by auto
    then show ?case
      using stream.collapse[symmetric, of \<omega>] step(2)
      by (inst_existentials "shd \<omega> # xs" \<omega>'; simp add: holds_Stream maximal_Cons_iff)
  qed
  moreover have "ev (holds terminal) (x ## \<omega>)" if "\<omega> = xs @- \<omega>'" "maximal (x # xs)" for xs \<omega> \<omega>'
    using that
    unfolding ev_alt_def maximal_def
    apply (simp split: if_split_asm)
    subgoal
      by (metis holds_Stream shift.simps(1))
    subgoal
      by (metis append_butlast_last_id holds_Stream shift.simps(2) shift_append)
    done
  ultimately show ?thesis
    unfolding no_runs_from_def by auto
qed

lemma no_runs_from_if_start_winning:
  "no_runs_from c\<^sub>0" if "c\<^sub>0 \<in> K"
  using that unfolding no_runs_from_def maximal_def terminal_def by auto

definition
  "wstrat_from c\<^sub>0 \<longleftrightarrow>
    (\<forall>xs. steps (c\<^sub>0 # xs) \<and> maximal (c\<^sub>0 # xs) \<longrightarrow> last (c\<^sub>0 # xs) \<in> K)
  \<and> no_runs_from c\<^sub>0"

lemma wstrat_from_def1:
  "wstrat_from c\<^sub>0 \<longleftrightarrow> c\<^sub>0 \<in> K \<or> \<not> lost c\<^sub>0 \<and>
    (\<forall>xs w. steps (c\<^sub>0 # xs @ [w]) \<and> maximal (c\<^sub>0 # xs @ [w]) \<longrightarrow> w \<in> K)
  \<and> no_runs_from c\<^sub>0"
  unfolding wstrat_from_def
  by (fastforce dest: maximal_terminal_startD elim: snocE no_runs_from_if_start_winning
        simp: terminal_def)

lemma no_runs_from_unfold:
  "no_runs_from c\<^sub>0 \<longleftrightarrow> terminal c\<^sub>0 \<or> (\<forall>x. c\<^sub>0 \<rightarrow> x \<longrightarrow> no_runs_from x)"
  unfolding no_runs_from_def1 by (auto simp: ev_Stream holds.simps elim: run.cases)

lemma wstrat_from_rec:
  "wstrat_from c\<^sub>0 \<longleftrightarrow> c\<^sub>0 \<in> K \<or> \<not> terminal c\<^sub>0 \<and> (\<forall>x. c\<^sub>0 \<rightarrow> x \<longrightarrow> wstrat_from x)"
  unfolding wstrat_from_def
  apply safe
        apply (fastforce simp: terminal_def)
       apply (metis Single stepsI maximal_Cons_iff last.simps list.sel(1))
      apply (subst (asm) no_runs_from_unfold; auto; fail)
     apply (fastforce dest: maximal_terminal_startD simp: terminal_def)
    apply (fastforce elim: no_runs_from_if_start_winning)
   apply (smt (verit, ccfv_threshold) terminal_def last.simps list.sel(1)
            local.steps.simps maximal_Cons_iff maximal_def terminal_def)
  apply (subst no_runs_from_unfold; auto; fail)
  done

end

definition
  "winning c\<^sub>0 \<longleftrightarrow> (\<exists>strategy. wstrat_from strategy c\<^sub>0)"

end

locale Timed_Safety_Game =
  fixes A :: "('a, 'c, 't :: time, 's) ta"
    and controllable :: "'a \<Rightarrow> bool"
  fixes K :: "('c, 't, 's) ta_config set"
begin

\<comment> \<open>We want to show that the enemy cannot win the dual game.\<close>
sublocale dual: Timed_Reachability_Game where
  A = A and
  controllable = "\<lambda>a. \<not> controllable a" and
  K = "- K" .

end

locale Timed_Safety_Game_Strat =
  Timed_Safety_Game A controllable K
  for A :: "('a, 'c, 't :: time, 's) ta" and controllable K +
  fixes strategy :: "('a, 'c, 't, 's) strategy"
begin

sublocale Timed_Game_Automaton A controllable strategy .

definition
  "safe_steps xs \<longleftrightarrow> steps xs \<and> (\<forall>x \<in> set xs. x \<notin> K)"

definition
  "safe_from c\<^sub>0 \<longleftrightarrow> c\<^sub>0 \<notin> K \<and> (\<forall>xs. steps (c\<^sub>0 # xs) \<longrightarrow> (\<forall>x \<in> set xs. x \<notin> K))"

lemma safe_from_alt_def:
  "safe_from c\<^sub>0 \<longleftrightarrow> (\<forall>x. c\<^sub>0 \<rightarrow>* x \<longrightarrow> x \<notin> K)"
  unfolding safe_from_def
  unfolding reaches_steps_iff2
  apply (cases c\<^sub>0)
  apply auto
  subgoal for a\<^sub>0 b\<^sub>0 xs a b
    apply (drule split_list)
    apply clarsimp
    subgoal for ys zs
      \<comment> \<open>Can we automate such goals?\<close>
      \<^cancel>\<open>apply (subgoal_tac "steps ((a\<^sub>0, b\<^sub>0) # ys @ [(a, b)])")
       apply metis\<close>
      by (smt (verit, del_insts) Nil_is_append_conv Single append_self_conv2 hd_append2 list.discI
            list.sel(1) list.sel(3) local.steps.cases stepsI steps_append_single steps_decomp)
    done
  done

lemma safe_from_unfold:
  "safe_from c\<^sub>0 \<longleftrightarrow> c\<^sub>0 \<notin> K \<and> (\<forall>x. c\<^sub>0 \<rightarrow> x \<longrightarrow> safe_from x)"
  unfolding safe_from_alt_def
  including graph_automation_aggressive by (cases c\<^sub>0) (auto elim: converse_rtranclpE)

lemma invariant_safe_fromI:
  assumes "Graph_Invariant_Start step c\<^sub>0 I" "\<forall>s. I s \<longrightarrow> s \<notin> K"
  shows "safe_from c\<^sub>0"
  using assms by (metis Graph_Invariant_Start.invariant_reaches safe_from_alt_def)

end

context Timed_Safety_Game
begin

abbreviation
  "safe_from' \<equiv> Timed_Safety_Game_Strat.safe_from A controllable K"

definition
  "safe c\<^sub>0 \<longleftrightarrow> (\<exists>strategy. safe_from' strategy c\<^sub>0)"

text \<open>Some ways of expressing duality. I am not sure how these are proved.\<close>
lemma
  "safe c\<^sub>0 \<longleftrightarrow> \<not> dual.winning c\<^sub>0"
  oops

lemma
  "safe (l, u) \<longleftrightarrow> (l, u) \<notin> K \<and> (\<forall>l' u'. A \<turnstile> \<langle>l, u\<rangle> \<rightarrow>\<^bsub>a\<^esub> \<langle>l', u'\<rangle> \<and> \<not> controllable a \<longrightarrow> safe (l', u'))"
  apply (subst safe_def)
  apply safe
  subgoal
    unfolding Timed_Safety_Game_Strat.safe_from_def by simp
  subgoal for strategy l' u'
    unfolding safe_def
    apply (rule exI[where x = strategy])
    apply (subst (asm) Timed_Safety_Game_Strat.safe_from_unfold)
    apply (auto intro: Timed_Game_Automaton.step.intros)
    done
  subgoal \<comment> \<open>\<longleftarrow>\<close>
    apply (subst Timed_Safety_Game_Strat.safe_from_unfold)
    \<comment> \<open>Use intersection of strategies for choice in current state\<close>
  oops

end

end