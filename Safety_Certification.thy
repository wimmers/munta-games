theory Safety_Certification
  imports
    Simulation_Graphs_Certification2
    Certification.Unreachability_Common
    "~/Code/Explorer/Guess_Explore"
begin

locale Unreachability_Invariant_paired_pre_defs =
  fixes E :: "'l \<times> 's \<Rightarrow> 'l \<times> 's \<Rightarrow> bool" and P :: "'l \<times> 's \<Rightarrow> bool"
    and less_eq :: "'s \<Rightarrow> 's set \<Rightarrow> bool" (infix "\<preceq>" 50)
begin

sublocale Unreachability_Invariant_pre_defs where
  less_eq = "\<lambda>(l, s) S. (\<forall>(l', s') \<in> S. l' = l) \<and> s \<preceq> R_of S" .

end

\<comment> \<open>Contains all auxiliary assumptions that will not be checked computationally.\<close>
locale Unreachability_Invariant_paired_pre =
  Unreachability_Invariant_paired_pre_defs +
  \<^cancel>\<open>assumes mono: "a \<preceq> B \<Longrightarrow> E a a' \<Longrightarrow> P a \<Longrightarrow> (\<forall>b \<in> B. P b)
    \<Longrightarrow> \<exists>B'. (\<forall>b' \<in> B'. \<exists>b \<in> B. E b b') \<and> a' \<preceq> B'"\<close>
  assumes mono:
    "s \<preceq> S \<Longrightarrow> E (l, s) (l', t) \<Longrightarrow> P (l, s) \<Longrightarrow> \<forall>s \<in> S. P (l, s)
    \<Longrightarrow> \<exists> T. t \<preceq> T \<and> (\<forall>t' \<in> T. \<exists>s' \<in> S. E (l, s') (l', t'))"
  \<^cancel>\<open>assumes P_invariant: "P a \<Longrightarrow> E a a' \<Longrightarrow> P b"\<close>
  assumes P_invariant: "P (l, s) \<Longrightarrow> E (l, s) (l', s') \<Longrightarrow> P (l', s')"
  assumes subsumes_Subsumed: "a \<preceq> A \<Longrightarrow> \<forall>s \<in> A. \<exists>T' \<subseteq> A'. s \<preceq> T' \<Longrightarrow> a \<preceq> A'"
begin

sublocale Unreachability_Invariant where
  less_eq = "\<lambda>(l, s) S. (\<forall>(l', s') \<in> S. l' = l) \<and> s \<preceq> R_of S"
  apply standard
  oops

end

definition project (infix "\<restriction>" 55) where
  "project S l = {s | s. (l, s) \<in> S}"

locale Reachability_Impl_base =
  Certification_Impl_base where E = E +
  Unreachability_Invariant_paired_pre_defs where E = E
  for E :: "'l \<times> 's \<Rightarrow> _" +
  fixes P' and F
  assumes P'_P: "\<And> l s. P' (l, s) \<Longrightarrow> P (l, s)"
  assumes F_mono:
    "\<And>a A. P a \<Longrightarrow> F a \<Longrightarrow> (\<lambda>(l, s) S. s \<preceq> S \<restriction> l) a A
    \<Longrightarrow> (\<forall> a \<in> A. P a) \<Longrightarrow> (\<exists> a \<in> A. F a)"

locale Reachability_Impl_pre =
  Reachability_Impl_base where E = E +
  Unreachability_Invariant_paired_pre where E = E +
  Paired_Graph_Set where E = E for E :: "'l \<times> 's \<Rightarrow> _"
begin

\<comment> \<open>Note that these instantiations can be restricted more,
  e.g.\ to allow subsumption checking with certificates.\<close>
sublocale Certification_Impl
  where R = "\<lambda>l s xs. s \<preceq> xs"
    and R_impl = "\<lambda>l s xs. RETURN (s \<preceq> xs)"
  by standard rule

end

locale Reachability_Impl_pre_start =
  Reachability_Impl_pre where E = E for E :: "'l \<times> 's \<Rightarrow> _" +
  fixes l\<^sub>0 :: 'l and s\<^sub>0 :: 's
begin

sublocale Certification_Impl_Start
  where R = "\<lambda>l s xs. s \<preceq> xs"
    and R_impl = "\<lambda>l s xs. RETURN (s \<preceq> xs)"
  ..

end

locale Reachability_Impl_correct =
  Reachability_Impl_pre_start where E = E +
  Unreachability_Invariant_paired_pre where E = E for E :: "'l \<times> 's \<Rightarrow> _"
begin

definition I where
  "I \<equiv> \<lambda>(l, s). l \<in> L \<and> s \<in> M l"

definition less_eq' where
  "less_eq' \<equiv> \<lambda>(l, s) S. s \<preceq> S \<restriction> l"

lemma less_eq'_pair [simp]:
  "less_eq' (l, s) S \<longleftrightarrow> s \<preceq> S \<restriction> l"
  unfolding less_eq'_def project_def from_R_def by auto

lemma project_from_R [simp]:
  "from_R l S \<restriction> l = S"
  unfolding project_def from_R_def by simp

lemma subsumes_Subsumed_lifted:
  assumes "s \<preceq> R_of A" "A \<sqsubseteq> A'" shows "s \<preceq> R_of A'"
  using assms unfolding Subsumed_def
  by (elim subsumes_Subsumed) (fastforce simp: R_of_def subset_image_iff dest: bspec)

lemma mem_project_iff:
  "s \<in> A \<restriction> l \<longleftrightarrow> (l, s) \<in> A"
  unfolding project_def by auto

lemma project_subsI:
  "A \<restriction> l \<subseteq> B \<restriction> l" if "A \<subseteq> B"
  using that unfolding project_def by auto

\<comment> \<open>Note that the second occurrence of \<^term>\<open>less_eq'\<close> can be restricted
  to only use certain subsumptions (e.g.\ from certificates).\<close>
lemma Unreachability_Invariant_pairedI[rule_format]:
  "check_all_spec \<longrightarrow> Unreachability_Invariant E P less_eq' I less_eq'"
  unfolding check_all_spec_def check_all_pre_spec_def check_invariant_spec_def
proof safe
  assume invariant:
    "\<forall>l\<in>L. \<forall>s\<in>M l. \<forall>l' s'. (l, s) \<rightarrow> (l', s') \<longrightarrow> l' \<in> L \<and> s' \<preceq> M l'" and
    wf: "\<forall>l\<in>L. \<forall>s\<in>M l. P' (l, s)" and
    \<comment> \<open>Unused:\<close>
    "l\<^sub>0 \<in> L"
    "s\<^sub>0 \<preceq> M l\<^sub>0"
    "P' (l\<^sub>0, s\<^sub>0)"
  show "Unreachability_Invariant E P less_eq' I less_eq'"
  proof standard
    fix a :: "'l \<times> 's" and B :: "('l \<times> 's) set" and a' :: "'l \<times> 's"
    assume prems:
      "less_eq' a B"
      "a \<rightarrow> a'"
      "P a"
      "\<forall>b\<in>B. P b"
    obtain l s l' s' where [simp]: "a = (l, s)" "a' = (l', s')"
      by (cases a; cases a')
    have "\<forall>s\<in>B \<restriction> l. P (l, s)" for l
      using prems(4) unfolding project_def by auto
    with prems(1-3) obtain T where "s' \<preceq> T" "\<forall>t'\<in>T. \<exists>s'\<in>B \<restriction> l. (l, s') \<rightarrow> (l', t')"
      by atomize_elim (rule mono, auto)
    then show "\<exists>B'. (\<forall>b'\<in>B'. \<exists>b\<in>B. b \<rightarrow> b') \<and> less_eq' a' B'"
      by (inst_existentials "from_R l' T") (auto simp: from_R_def project_def)
  next
    fix s :: "'l \<times> 's" and t :: "'l \<times> 's"
    assume prems: "I s" "s \<rightarrow> t"
    obtain l' s' where "t = (l', s')"
      by (cases t)
    with prems invariant show "\<exists>T. Ball T I \<and> less_eq' t T"
      by (inst_existentials "from_R l' (M l')"; clarsimp) (auto simp: from_R_def I_def)
  next
    fix s :: "'l \<times> 's" and T :: "('l \<times> 's) set"
    assume "less_eq' s T"
    then show "less_eq' s T" .
  next
    fix s :: "'l \<times> 's"
    assume "I s"
    with wf show "P s"
      by (metis (no_types, lifting) I_def P'_P case_prodE)
  next
    fix a :: "'l \<times> 's" and a' :: "'l \<times> 's"
    assume  "P a" and "a \<rightarrow> a'"
    then show "P a'"
      by - (cases a; cases a'; simp only:; rule P_invariant)
  next
    fix a :: "'l \<times> 's" and A :: "('l \<times> 's) set" and A' :: "('l \<times> 's) set"
    assume prems:
      "less_eq' a A"
      "Unreachability_Invariant_pre_defs.Subsumed less_eq' A A'"
    obtain l s where [simp]: "a = (l, s)"
      by (cases a)
    have "\<exists>T'\<subseteq>A' \<restriction> l. s \<preceq> T'" if "s \<in> A \<restriction> l" for s
    proof -
      from that prems (2) obtain T' where
        "(l, s) \<in> A" "T' \<subseteq> A'" "s \<preceq> T' \<restriction> l"
        unfolding Unreachability_Invariant_pre_defs.Subsumed_def by (auto simp: mem_project_iff)
      then show ?thesis
        by (auto dest: project_subsI)
    qed
    with prems(1) show "less_eq' a A'"
      by (auto elim: subsumes_Subsumed)
  qed
qed

lemma check_all_correct':
  "check_all \<le> SPEC (\<lambda>r. r \<longrightarrow> Unreachability_Invariant E P less_eq' I less_eq')"
  by (refine_vcg Unreachability_Invariant_pairedI check_all_correct) fast

lemma in_from_R_conv:
  "(l, s) \<in> from_R l' S \<longleftrightarrow> l = l' \<and> s \<in> S"
  unfolding from_R_def by auto

lemma F_mono':
  "P (l, s) \<Longrightarrow> F (l, s) \<Longrightarrow> s \<preceq> B \<restriction> l \<Longrightarrow> \<forall>x \<in> B. P x \<Longrightarrow> \<exists>b \<in> B. F b"
  by (drule F_mono[rotated, where A = "B"]) (auto simp: mem_project_iff)

lemma certify_unreachableI:
  "check_all_spec \<and> check_final_spec \<longrightarrow> (\<nexists>s'. E\<^sup>*\<^sup>* (l\<^sub>0, s\<^sub>0) s' \<and> F s')"
  by (rule impI Unreachability_Invariant.final_unreachable[where S\<^sub>0 = "from_R l\<^sub>0 (M l\<^sub>0)"]
        Unreachability_Invariant_pairedI)+
     (auto intro: F_mono P'_P
       simp: check_final_spec_def check_all_spec_def check_all_pre_spec_def
        Unreachability_Invariant_defs.Inv_def I_def in_from_R_conv)

lemma certify_unreachable_correct':
  "certify_unreachable \<le> SPEC (\<lambda>r. r \<longrightarrow> (\<nexists>s'. E\<^sup>*\<^sup>* (l\<^sub>0, s\<^sub>0) s' \<and> F s'))"
  by (refine_vcg certify_unreachableI[rule_format] certify_unreachable_correct; fast)

end

locale Reachability_Impl =
  Certification_Impl_imp where M = M and K = K and A = A +
  Reachability_Impl_correct where M = "\<lambda>x. case M x of None \<Rightarrow> {} | Some S \<Rightarrow> S"
    for M :: "'k \<Rightarrow> 'a set option"
    and K :: "'k \<Rightarrow> 'ki :: {hashable,heap} \<Rightarrow> assn"
    and A :: "'a \<Rightarrow> 'ai :: heap \<Rightarrow> assn" +
  \<comment> \<open>Again, as explained above, this can be replaced with a more specific subsumption.\<close>
  fixes Lei
  assumes Lei[sepref_fr_rules]:
    "(uncurry Lei,uncurry (RETURN oo PR_CONST less_eq)) \<in> A\<^sup>k *\<^sub>a (lso_assn A)\<^sup>k \<rightarrow>\<^sub>a bool_assn"

end