theory TA_Games_Misc
  imports
    Main
    "HOL-Library.Sublist"
    "HOL-Library.Linear_Temporal_Logic_on_Streams" Transition_Systems_and_Automata.Sequence_LTL
    TA_Library.Instantiate_Existentials
    TA_Library.Graphs
begin

paragraph \<open>Unused\<close>

lemma strict_suffix_Cons_iff:
  "strict_suffix xs (x # ys) \<longleftrightarrow> xs = ys \<or> strict_suffix xs ys"
  by (metis suffix_Cons suffix_ConsD' suffix_order.less_le)

lemma ev_alt_def_strong:
  "ev \<phi> w \<longleftrightarrow> (\<exists>u v. w = u @- v \<and> \<phi> v \<and> (\<forall>x. suffix x u \<and> x \<noteq> [] \<longrightarrow> \<not> \<phi> (x @- v)))"
  apply safe
  subgoal premises prems
    using prems apply (induction rule: ev_induct_strong)
     apply (rule exI[where x = "[]"], simp; fail)
    apply (elim exE)
    subgoal for xs u v
      using stream.collapse[symmetric, of xs]
      by (inst_existentials "shd xs # u" v) (auto simp: suffix_Cons)
  done
  unfolding ev_alt_def by auto

paragraph \<open>Misc\<close>

lemma snocE:
  assumes "xs \<noteq> []"
  obtains x xs' where "xs = xs' @ [x]"
  using assms by (intro that[of "butlast xs" "last xs"]) (simp add: snoc_eq_iff_butlast)

end