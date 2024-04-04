theory hpaxos_aux
imports Main hpaxos hpaxos_safety
begin


lemma next_msgs_preserved:
  assumes "Next st st2"
      and "x \<in> set (msgs st)"
  shows "x \<in> set (msgs st2)"
proof -
  have css: "ProposerSendAction st st2 \<or>
        (\<exists>A :: Acceptor. is_safe A
                    \<and> queued_msg st A = None 
                    \<and> (\<exists>m \<in> set (msgs st). Process1a A m st st2)) \<or>
        (\<exists>A :: Acceptor. is_safe A
                      \<and> queued_msg st A \<noteq> None 
                      \<and> Process1b A (the (queued_msg st A)) st st2) \<or>
        (\<exists>A :: Acceptor. is_safe A
                      \<and> queued_msg st A = None 
                      \<and> (\<exists>m \<in> set (msgs st). Process1b A m st st2)) \<or>
        (\<exists>A :: Acceptor. is_safe A
                      \<and> two_a_lrn_loop st A 
                      \<and> (\<exists>l :: Learner. Process1bLearnerLoopStep A l st st2)) \<or>
        (\<exists>A :: Acceptor. is_safe A
                      \<and> two_a_lrn_loop st A 
                      \<and> Process1bLearnerLoopDone A st st2) \<or>
        LearnerProcessAction st st2 \<or>
        (\<exists>A :: Acceptor. \<not> (is_safe A)
                      \<and> FakeSend1b A st st2) \<or>
        (\<exists>A :: Acceptor. \<not> (is_safe A)
                      \<and> FakeSend2a A st st2)
        "
        using assms next_split by presburger
    then show ?thesis
    proof (elim disjE)
      assume "ProposerSendAction st st2"
      then show ?thesis
        using assms(2) by auto
    next
      assume "\<exists>A. is_safe A \<and>
                queued_msg st A = None \<and>
                (\<exists>m\<in>set (msgs st).
                    Process1a A m st st2)"
      show ?thesis
        by (metis Process1a.elims(2) Send.elims(2) \<open>\<exists>A. is_safe A \<and> queued_msg st A = None \<and> (\<exists>m\<in>set (msgs st). Process1a A m st st2)\<close> assms(2) in_set_member member_rec(1))
    next
      assume "\<exists>A :: Acceptor. is_safe A
                        \<and> queued_msg st A \<noteq> None 
                        \<and> Process1b A (the (queued_msg st A)) st st2"
      then show ?thesis
        by (metis Process1b.elims(2) assms(2))
    next
      assume "\<exists>A :: Acceptor. is_safe A
                  \<and> queued_msg st A = None 
                  \<and> (\<exists>m \<in> set (msgs st). Process1b A m st st2)"
      then show ?thesis
        by (metis Process1b.elims(2) assms(2))
    next
      assume "\<exists>A :: Acceptor. is_safe A
                        \<and> two_a_lrn_loop st A 
                        \<and> (\<exists>l :: Learner. Process1bLearnerLoopStep A l st st2)"
      then show ?thesis
        by (metis Process1bLearnerLoopStep.elims(2) Send.elims(2) assms(2) in_set_member member_rec(1))
    next
      assume "\<exists>A. is_safe A \<and>
        two_a_lrn_loop st A \<and>
        Process1bLearnerLoopDone A st st2"
      show ?thesis
        using \<open>\<exists>A. is_safe A \<and> two_a_lrn_loop st A \<and> Process1bLearnerLoopDone A st st2\<close> assms(2) by force
    next
      assume "LearnerProcessAction st st2"
      then show ?thesis
        by (metis (no_types, lifting) LearnerProcessAction.elims(2) LearnerAction.elims(2) LearnerDecide.elims(2) LearnerRecv.elims(2) assms(2) simps(1) surjective update_convs(3) update_convs(8))
    next
      assume "\<exists>A. \<not> is_safe A \<and> FakeSend1b A st st2"
      show ?thesis
        by (metis FakeSend1b.simps \<open>\<exists>A. \<not> is_safe A \<and> FakeSend1b A st st2\<close> assms(2) in_set_member member_rec(1) simps(1) surjective update_convs(1))
    next
      assume "\<exists>A. \<not> is_safe A \<and> FakeSend2a A st st2"
      then show ?thesis
        by (metis FakeSend2a.simps assms(2) ext_inject in_set_member member_rec(1) surjective update_convs(1))
    qed
qed

lemma spec_msgs_preserved:
  assumes "Spec f"
      and "x \<in> set (msgs (f i))"
  shows "x \<in> set (msgs (f (i + 1)))"
  by (metis Spec.elims(2) Suc_eq_plus1 assms(1) assms(2) next_msgs_preserved)

lemma msgs_preserved:
  assumes "Spec f"
  shows "j \<ge> i \<longrightarrow> x \<in> set (msgs (f i)) \<longrightarrow> x \<in> set (msgs (f j))"
proof (induction j)
  case 0
  then show ?case
    by simp
next
  case (Suc j)
  then show ?case
    by (metis One_nat_def add.right_neutral add_Suc_right assms le_SucE spec_msgs_preserved)
qed

lemma msgs_preserved_subset:
  assumes "Spec f"
      and "i \<le> j"
  shows "set (msgs (f i)) \<subseteq> set (msgs (f j))"
  using assms msgs_preserved by blast

lemma next_known_msgs_acc_preserved:
  assumes "Next st st2"
      and "x \<in> set (known_msgs_acc st a)"
    shows "x \<in> set (known_msgs_acc st2 a)"
proof -
  have css: "ProposerSendAction st st2 \<or>
        (\<exists>A :: Acceptor. is_safe A
                    \<and> queued_msg st A = None 
                    \<and> (\<exists>m \<in> set (msgs st). Process1a A m st st2)) \<or>
        (\<exists>A :: Acceptor. is_safe A
                      \<and> queued_msg st A \<noteq> None 
                      \<and> Process1b A (the (queued_msg st A)) st st2) \<or>
        (\<exists>A :: Acceptor. is_safe A
                      \<and> queued_msg st A = None 
                      \<and> (\<exists>m \<in> set (msgs st). Process1b A m st st2)) \<or>
        (\<exists>A :: Acceptor. is_safe A
                      \<and> two_a_lrn_loop st A 
                      \<and> (\<exists>l :: Learner. Process1bLearnerLoopStep A l st st2)) \<or>
        (\<exists>A :: Acceptor. is_safe A
                      \<and> two_a_lrn_loop st A 
                      \<and> Process1bLearnerLoopDone A st st2) \<or>
        LearnerProcessAction st st2 \<or>
        (\<exists>A :: Acceptor. \<not> (is_safe A)
                      \<and> FakeSend1b A st st2) \<or>
        (\<exists>A :: Acceptor. \<not> (is_safe A)
                      \<and> FakeSend2a A st st2)
        "
        using assms next_split by presburger
    then show ?thesis
    proof (elim disjE)
      assume "ProposerSendAction st st2"
      then show ?thesis
        using assms(2) by auto
    next
      assume "\<exists>A. is_safe A \<and>
                queued_msg st A = None \<and>
                (\<exists>m\<in>set (msgs st).
                    Process1a A m st st2)"
      show ?thesis
        by (metis Process1a.elims(2) Store_acc.elims(2) \<open>\<exists>A. is_safe A \<and> queued_msg st A = None \<and> (\<exists>m\<in>set (msgs st). Process1a A m st st2)\<close> assms(2) list.set_intros(2))
    next
      assume "\<exists>A :: Acceptor. is_safe A
                        \<and> queued_msg st A \<noteq> None 
                        \<and> Process1b A (the (queued_msg st A)) st st2"
      then show ?thesis
      proof (clarify)
        fix A y2
        assume "is_safe A"
           and "queued_msg st A = Some y2"
           and "Process1b A (the (queued_msg st A)) st st2"
        then have "known_msgs_acc st2 = (
                \<lambda>x. if A = x 
                    then y2 # known_msgs_acc st x
                    else known_msgs_acc st x
            )"
          by (metis Process1b.elims(2) Store_acc.elims(2) option.sel)
        then show ?thesis
          by (simp add: assms(2))
      qed
    next
      assume "\<exists>A :: Acceptor. is_safe A
                  \<and> queued_msg st A = None 
                  \<and> (\<exists>m \<in> set (msgs st). Process1b A m st st2)"
      then show ?thesis
      proof (clarify)
        fix A m
        assume "is_safe A"
           and "queued_msg st A = None"
           and "m \<in> set (msgs st)"
           and "Process1b A m st st2"
        then have "known_msgs_acc st2 = (
                \<lambda>x. if A = x 
                    then m # known_msgs_acc st x
                    else known_msgs_acc st x
            )"
          by (metis Process1b.elims(2) Store_acc.elims(2))
        then show ?thesis
          by (simp add: assms(2))
      qed
    next
      assume "\<exists>A :: Acceptor. is_safe A
                        \<and> two_a_lrn_loop st A 
                        \<and> (\<exists>l :: Learner. Process1bLearnerLoopStep A l st st2)"
      then show ?thesis
        by (metis Process1bLearnerLoopStep.elims(2) Store_acc.elims(2) assms(2) list.set_intros(2))
    next
      assume "\<exists>A. is_safe A \<and>
        two_a_lrn_loop st A \<and>
        Process1bLearnerLoopDone A st st2"
      show ?thesis
        using \<open>\<exists>A. is_safe A \<and> two_a_lrn_loop st A \<and> Process1bLearnerLoopDone A st st2\<close> assms(2) by force
    next
      assume "LearnerProcessAction st st2"
      then show ?thesis
        by (smt (verit) LearnerAction.elims(2) LearnerDecide.elims(2) LearnerProcessAction.elims(1) LearnerRecv.elims(2) assms(2) ext_inject surjective update_convs(3) update_convs(8))
    next
      assume "\<exists>A. \<not> is_safe A \<and> FakeSend1b A st st2"
      show ?thesis
        by (metis FakeSend1b.elims(1) \<open>\<exists>A. \<not> is_safe A \<and> FakeSend1b A st st2\<close> assms(2) ext_inject surjective update_convs(1))
    next
      assume "\<exists>A. \<not> is_safe A \<and> FakeSend2a A st st2"
      then show ?thesis
        by (metis FakeSend2a.simps assms(2) ext_inject surjective update_convs(1))
    qed
qed

lemma known_msgs_acc_preserved:
  assumes "Spec f"
  shows "j \<ge> i \<longrightarrow> x \<in> set (known_msgs_acc (f i) a) \<longrightarrow> x \<in> set (known_msgs_acc (f j) a)"
proof (induction j)
  case 0
  then show ?case
    by simp
next
  case (Suc j)
  then show ?case
    by (metis Spec.elims(2) assms le_SucE next_known_msgs_acc_preserved)
qed

lemma known_msgs_acc_preserved_subset:
  assumes "Spec f"
      and "i \<le> j"
  shows "set (known_msgs_acc (f i) a) \<subseteq> set (known_msgs_acc (f j) a)"
  using assms known_msgs_acc_preserved by blast






lemma next_known_msgs_lrn_preserved:
  assumes "Next st st2"
      and "x \<in> set (known_msgs_lrn st a)"
    shows "x \<in> set (known_msgs_lrn st2 a)"
proof -
  have css: "ProposerSendAction st st2 \<or>
        (\<exists>A :: Acceptor. is_safe A
                    \<and> queued_msg st A = None 
                    \<and> (\<exists>m \<in> set (msgs st). Process1a A m st st2)) \<or>
        (\<exists>A :: Acceptor. is_safe A
                      \<and> queued_msg st A \<noteq> None 
                      \<and> Process1b A (the (queued_msg st A)) st st2) \<or>
        (\<exists>A :: Acceptor. is_safe A
                      \<and> queued_msg st A = None 
                      \<and> (\<exists>m \<in> set (msgs st). Process1b A m st st2)) \<or>
        (\<exists>A :: Acceptor. is_safe A
                      \<and> two_a_lrn_loop st A 
                      \<and> (\<exists>l :: Learner. Process1bLearnerLoopStep A l st st2)) \<or>
        (\<exists>A :: Acceptor. is_safe A
                      \<and> two_a_lrn_loop st A 
                      \<and> Process1bLearnerLoopDone A st st2) \<or>
        LearnerProcessAction st st2 \<or>
        (\<exists>A :: Acceptor. \<not> (is_safe A)
                      \<and> FakeSend1b A st st2) \<or>
        (\<exists>A :: Acceptor. \<not> (is_safe A)
                      \<and> FakeSend2a A st st2)
        "
        using assms next_split by presburger
    then show ?thesis
    proof (elim disjE)
      assume "ProposerSendAction st st2"
      then show ?thesis
        using assms(2) by auto
    next
      assume "\<exists>A. is_safe A \<and>
                queued_msg st A = None \<and>
                (\<exists>m\<in>set (msgs st).
                    Process1a A m st st2)"
      show ?thesis
        by (metis Process1a.elims(2) Store_acc.elims(2) \<open>\<exists>A. is_safe A \<and> queued_msg st A = None \<and> (\<exists>m\<in>set (msgs st). Process1a A m st st2)\<close> assms(2))
    next
      assume "\<exists>A :: Acceptor. is_safe A
                        \<and> queued_msg st A \<noteq> None 
                        \<and> Process1b A (the (queued_msg st A)) st st2"
      then show ?thesis
      proof (clarify)
        fix A y2
        assume "is_safe A"
           and "queued_msg st A = Some y2"
           and "Process1b A (the (queued_msg st A)) st st2"
        then show ?thesis
          by (simp add: assms(2))
      qed
    next
      assume "\<exists>A :: Acceptor. is_safe A
                  \<and> queued_msg st A = None 
                  \<and> (\<exists>m \<in> set (msgs st). Process1b A m st st2)"
      then show ?thesis
      proof (clarify)
        fix A m
        assume "is_safe A"
           and "queued_msg st A = None"
           and "m \<in> set (msgs st)"
           and "Process1b A m st st2"
        then show ?thesis
          by (simp add: assms(2))
      qed
    next
      assume "\<exists>A :: Acceptor. is_safe A
                        \<and> two_a_lrn_loop st A 
                        \<and> (\<exists>l :: Learner. Process1bLearnerLoopStep A l st st2)"
      then show ?thesis
        by (metis Process1bLearnerLoopStep.elims(2) Store_acc.elims(2) assms(2))
    next
      assume "\<exists>A. is_safe A \<and>
        two_a_lrn_loop st A \<and>
        Process1bLearnerLoopDone A st st2"
      show ?thesis
        using \<open>\<exists>A. is_safe A \<and> two_a_lrn_loop st A \<and> Process1bLearnerLoopDone A st st2\<close> assms(2) by force
    next
      assume "LearnerProcessAction st st2"
      then show ?thesis
        by (smt (verit) LearnerAction.elims(2) LearnerDecide.elims(2) LearnerProcessAction.elims(1) LearnerRecv.elims(2) assms(2) ext_inject list.set_intros(2) surjective update_convs(3) update_convs(8))
    next
      assume "\<exists>A. \<not> is_safe A \<and> FakeSend1b A st st2"
      show ?thesis
        by (metis FakeSend1b.elims(1) \<open>\<exists>A. \<not> is_safe A \<and> FakeSend1b A st st2\<close> assms(2) ext_inject surjective update_convs(1))
    next
      assume "\<exists>A. \<not> is_safe A \<and> FakeSend2a A st st2"
      then show ?thesis
        by (metis FakeSend2a.simps assms(2) ext_inject surjective update_convs(1))
    qed
qed

lemma known_msgs_lrn_preserved:
  assumes "Spec f"
  shows "j \<ge> i \<longrightarrow> x \<in> set (known_msgs_lrn (f i) a) \<longrightarrow> x \<in> set (known_msgs_lrn (f j) a)"
proof (induction j)
  case 0
  then show ?case
    by simp
next
  case (Suc j)
  then show ?case
    by (metis Spec.elims(2) assms le_SucE next_known_msgs_lrn_preserved)
qed

lemma known_msgs_lrn_preserved_subset:
  assumes "Spec f"
      and "i \<le> j"
  shows "set (known_msgs_lrn (f i) a) \<subseteq> set (known_msgs_lrn (f j) a)"
  using assms known_msgs_lrn_preserved by blast








lemma Next_Preservation:
  assumes "Spec f"
      and "\<forall>st st2. Next st st2 \<longrightarrow> P st \<longrightarrow> P st2"
    shows "j \<ge> i \<longrightarrow> P (f i) \<longrightarrow> P (f j)"
proof (induction j)
  case 0
  then show ?case 
    by auto
next
  case (Suc j)
  then show ?case
    by (metis Spec.elims(2) assms(1) assms(2) le_SucE)
qed


lemma Process1a_Not_Process1bLearnerLoopStep:
  assumes "Process1a a ln st st2"
  shows "\<not> Process1bLearnerLoopStep a2 ln2 st st2"
proof -
  define new1b where "new1b = M1b a (ln # recent_msgs st a)"
  then show ?thesis
  proof (cases "WellFormed st new1b")
    case True
    then show ?thesis
      by (smt (verit) PreMessage.distinct(5) Process1a.elims(2) Process1bLearnerLoopStep.elims(2) Send.elims(1) assms list.inject not_Cons_self2)
  next
    case False
    then show ?thesis
      by (metis Process1a.elims(2) Process1bLearnerLoopStep.elims(2) Send.elims(1) assms new1b_def not_Cons_self2)
  qed
qed


lemma Wellformed_Conservation_Next:
  assumes "Next st st2"
      and "WellFormed st m"
    shows "WellFormed st2 m"
proof -
  have css: "ProposerSendAction st st2 \<or>
                (\<exists>A :: Acceptor. is_safe A
                            \<and> queued_msg st A = None 
                            \<and> (\<exists>m \<in> set (msgs st). Process1a A m st st2)) \<or>
                (\<exists>A :: Acceptor. is_safe A
                              \<and> queued_msg st A \<noteq> None 
                              \<and> Process1b A (the (queued_msg st A)) st st2) \<or>
                (\<exists>A :: Acceptor. is_safe A
                              \<and> queued_msg st A = None 
                              \<and> (\<exists>m \<in> set (msgs st). Process1b A m st st2)) \<or>
                (\<exists>A :: Acceptor. is_safe A
                              \<and> two_a_lrn_loop st A 
                              \<and> (\<exists>l :: Learner. Process1bLearnerLoopStep A l st st2)) \<or>
                (\<exists>A :: Acceptor. is_safe A
                              \<and> two_a_lrn_loop st A 
                              \<and> Process1bLearnerLoopDone A st st2) \<or>
                LearnerProcessAction st st2 \<or>
                (\<exists>A :: Acceptor. \<not> (is_safe A)
                              \<and> FakeSend1b A st st2) \<or>
                (\<exists>A :: Acceptor. \<not> (is_safe A)
                              \<and> FakeSend2a A st st2)
                "
                using assms next_split by presburger
    then show ?thesis
    proof (elim disjE)
      assume "ProposerSendAction st st2"
      then show ?thesis
        using assms(2) by auto
    next
      assume "\<exists>A. is_safe A \<and>
                queued_msg st A = None \<and>
                (\<exists>m\<in>set (msgs st).
                    Process1a A m st st2)"
      then show ?thesis
        by (metis Process1a.elims(2) WellFormed_monotone assms(2))
    next
      assume "\<exists>A :: Acceptor. is_safe A
                        \<and> queued_msg st A \<noteq> None 
                        \<and> Process1b A (the (queued_msg st A)) st st2"
      then show ?thesis
      proof -
        show ?thesis
          using \<open>\<exists>A. is_safe A \<and> queued_msg st A \<noteq> None \<and> Process1b A (the (queued_msg st A)) st st2\<close> assms(2) by force
      qed
    next
      assume "\<exists>A :: Acceptor. is_safe A
                  \<and> queued_msg st A = None 
                  \<and> (\<exists>m \<in> set (msgs st). Process1b A m st st2)"
      then show ?thesis
      proof -
        show ?thesis
          using \<open>\<exists>A. is_safe A \<and> queued_msg st A = None \<and> (\<exists>m\<in>set (msgs st). Process1b A m st st2)\<close> assms(2) by fastforce
      qed
    next
      assume "\<exists>A :: Acceptor. is_safe A
                        \<and> two_a_lrn_loop st A 
                        \<and> (\<exists>l :: Learner. Process1bLearnerLoopStep A l st st2)"
      then show ?thesis
        by (metis Process1bLearnerLoopStep.elims(2) WellFormed_monotone assms(2))
    next
      assume "\<exists>A. is_safe A \<and>
        two_a_lrn_loop st A \<and>
        Process1bLearnerLoopDone A st st2"
      then show ?thesis
        using assms(2) by auto
    next
      assume "LearnerProcessAction st st2"
      then show ?thesis
        by (metis (no_types, lifting) LearnerProcessAction.simps LearnerAction.simps LearnerDecide.elims(2) LearnerRecv.elims(2) WellFormed_monotone assms(2) ext_inject surjective update_convs(3) update_convs(8))
    next
      assume "\<exists>A. \<not> is_safe A \<and> FakeSend1b A st st2"
      show ?thesis
        by (metis FakeSend1b.simps WellFormed_monotone \<open>\<exists>A. \<not> is_safe A \<and> FakeSend1b A st st2\<close> assms(2) ext_inject surjective update_convs(1))
    next
      assume "\<exists>A. \<not> is_safe A \<and> FakeSend2a A st st2"
      then show ?thesis
        by (metis FakeSend2a.simps WellFormed_monotone assms(2) select_convs(9) surjective update_convs(1))
    qed
qed

lemma Wellformed_Conservation:
  assumes "Spec f"
      and "WellFormed (f i) m"
    shows "j \<ge> i \<longrightarrow> WellFormed (f j) m"
proof (induction j)
  case 0
  then show ?case 
    using assms(2) by blast
next
  case (Suc j)
  then show ?case
    by (metis Spec.elims(2) Wellformed_Conservation_Next assms(1) assms(2) le_SucE)
qed



lemma decision_Conservation_Next:
  assumes "Next st st2"
      and "v \<in> decision st L BB"
    shows "v \<in> decision st2 L BB"
proof -
  have css: "ProposerSendAction st st2 \<or>
                (\<exists>A :: Acceptor. is_safe A
                            \<and> queued_msg st A = None 
                            \<and> (\<exists>m \<in> set (msgs st). Process1a A m st st2)) \<or>
                (\<exists>A :: Acceptor. is_safe A
                              \<and> queued_msg st A \<noteq> None 
                              \<and> Process1b A (the (queued_msg st A)) st st2) \<or>
                (\<exists>A :: Acceptor. is_safe A
                              \<and> queued_msg st A = None 
                              \<and> (\<exists>m \<in> set (msgs st). Process1b A m st st2)) \<or>
                (\<exists>A :: Acceptor. is_safe A
                              \<and> two_a_lrn_loop st A 
                              \<and> (\<exists>l :: Learner. Process1bLearnerLoopStep A l st st2)) \<or>
                (\<exists>A :: Acceptor. is_safe A
                              \<and> two_a_lrn_loop st A 
                              \<and> Process1bLearnerLoopDone A st st2) \<or>
                LearnerProcessAction st st2 \<or>
                (\<exists>A :: Acceptor. \<not> (is_safe A)
                              \<and> FakeSend1b A st st2) \<or>
                (\<exists>A :: Acceptor. \<not> (is_safe A)
                              \<and> FakeSend2a A st st2)
                "
                using assms next_split by presburger
    then show ?thesis
    proof (elim disjE)
      assume "ProposerSendAction st st2"
      then show ?thesis
        using assms(2) by auto
    next
      assume "\<exists>A. is_safe A \<and>
                queued_msg st A = None \<and>
                (\<exists>m\<in>set (msgs st).
                    Process1a A m st st2)"
      then show ?thesis
        by (metis Process1a.elims(2) assms(2))
    next
      assume "\<exists>A :: Acceptor. is_safe A
                        \<and> queued_msg st A \<noteq> None 
                        \<and> Process1b A (the (queued_msg st A)) st st2"
      then show ?thesis
      proof -
        show ?thesis
          using \<open>\<exists>A. is_safe A \<and> queued_msg st A \<noteq> None \<and> Process1b A (the (queued_msg st A)) st st2\<close> assms(2) by force
      qed
    next
      assume "\<exists>A :: Acceptor. is_safe A
                  \<and> queued_msg st A = None 
                  \<and> (\<exists>m \<in> set (msgs st). Process1b A m st st2)"
      then show ?thesis
      proof -
        show ?thesis
          using \<open>\<exists>A. is_safe A \<and> queued_msg st A = None \<and> (\<exists>m\<in>set (msgs st). Process1b A m st st2)\<close> assms(2) by fastforce
      qed
    next
      assume "\<exists>A :: Acceptor. is_safe A
                        \<and> two_a_lrn_loop st A 
                        \<and> (\<exists>l :: Learner. Process1bLearnerLoopStep A l st st2)"
      then show ?thesis
        by (metis Process1bLearnerLoopStep.elims(2) assms(2))
    next
      assume "\<exists>A. is_safe A \<and>
        two_a_lrn_loop st A \<and>
        Process1bLearnerLoopDone A st st2"
      then show ?thesis
        using assms(2) by auto
    next
      assume "LearnerProcessAction st st2"
      then show ?thesis
        unfolding LearnerProcessAction.simps LearnerAction.simps
      proof (clarify)
        fix ln
        assume "(\<exists>m\<in>set (msgs st). LearnerRecv ln m st st2) \<or>
              (\<exists>blt val. LearnerDecide ln blt val st st2)"
        then show ?thesis
        proof (elim disjE; clarify)
          fix m
          assume "m \<in> set (msgs st)"
             and "LearnerRecv ln m st st2"
          then show ?thesis
            by (simp add: assms(2) surjective)
          next
            fix blt val
            assume "LearnerDecide ln blt val st st2"
            show ?thesis
            using \<open>LearnerDecide ln blt val st st2\<close> assms(2) by force
        qed
      qed
    next
      assume "\<exists>A. \<not> is_safe A \<and> FakeSend1b A st st2"
      show ?thesis
        by (metis FakeSend1b.simps \<open>\<exists>A. \<not> is_safe A \<and> FakeSend1b A st st2\<close> assms(2) ext_inject surjective update_convs(1))
    next
      assume "\<exists>A. \<not> is_safe A \<and> FakeSend2a A st st2"
      then show ?thesis
        by (metis FakeSend2a.simps assms(2) ext_inject surjective update_convs(1))
    qed
qed

lemma decision_Conservation:
  assumes "Spec f"
      and "v \<in> decision (f i) L BB"
    shows "j \<ge> i \<longrightarrow> v \<in> decision (f j) L BB"
proof (induction j)
  case 0
  then show ?case 
    using assms(2) by blast
next
  case (Suc j)
  then show ?case
    by (metis Spec.elims(2) decision_Conservation_Next assms(1) assms(2) le_SucE)
qed

lemma decision_Conservation_subset:
  assumes "Spec f"
      and "i \<le> j"
    shows "decision (f i) L BB \<subseteq> decision (f j) L BB"
  using assms(1) assms(2) decision_Conservation by blast

fun QueuedMsgSpec2 :: "State \<Rightarrow> bool" where
  "QueuedMsgSpec2 st = (
    \<forall>a :: Acceptor. is_safe a \<and> queued_msg st a \<noteq> None \<longrightarrow> 
      Recv_acc st a (the (queued_msg st a))
  )"


lemma QueuedMsgSpecInvariant2 :
  assumes "QueuedMsgSpec2 st"
      and "Next st st2"
      and "FullSafetyInvariant st"
  shows "QueuedMsgSpec2 st2"
  unfolding QueuedMsgSpec2.simps Recv_acc.simps
proof (clarify)
  fix a y
  assume "is_safe a"
     and "queued_msg st2 a = Some y"
  have css: "ProposerSendAction st st2 \<or>
                (\<exists>A :: Acceptor. is_safe A
                            \<and> queued_msg st A = None 
                            \<and> (\<exists>m \<in> set (msgs st). Process1a A m st st2)) \<or>
                (\<exists>A :: Acceptor. is_safe A
                              \<and> queued_msg st A \<noteq> None 
                              \<and> Process1b A (the (queued_msg st A)) st st2) \<or>
                (\<exists>A :: Acceptor. is_safe A
                              \<and> queued_msg st A = None 
                              \<and> (\<exists>m \<in> set (msgs st). Process1b A m st st2)) \<or>
                (\<exists>A :: Acceptor. is_safe A
                              \<and> two_a_lrn_loop st A 
                              \<and> (\<exists>l :: Learner. Process1bLearnerLoopStep A l st st2)) \<or>
                (\<exists>A :: Acceptor. is_safe A
                              \<and> two_a_lrn_loop st A 
                              \<and> Process1bLearnerLoopDone A st st2) \<or>
                LearnerProcessAction st st2 \<or>
                (\<exists>A :: Acceptor. \<not> (is_safe A)
                              \<and> FakeSend1b A st st2) \<or>
                (\<exists>A :: Acceptor. \<not> (is_safe A)
                              \<and> FakeSend2a A st st2)
                "
                using assms next_split by presburger
    then show "the (queued_msg st2 a) \<notin> set (known_msgs_acc st2 a) \<and>
               WellFormed st2 (the (queued_msg st2 a)) \<and>
               Proper_acc st2 a (the (queued_msg st2 a))"
    proof (elim disjE)
      assume "ProposerSendAction st st2"
      then show ?thesis
        by (smt (verit) Proper_acc.elims(2) Proper_acc.elims(3) ProposerSendAction.elims(2) QueuedMsgSpec2.simps Recv_acc.elims(1) Send1a.elims(2) Wellformed_Conservation_Next \<open>is_safe a\<close> \<open>queued_msg st2 a = Some y\<close> assms(1) assms(2) ext_inject not_None_eq surjective update_convs(1))
    next
      assume "\<exists>A. is_safe A \<and>
                queued_msg st A = None \<and>
                (\<exists>m\<in>set (msgs st).
                    Process1a A m st st2)"
      then show ?thesis
      proof (clarify)
        fix A m
        assume "is_safe A"
           and "queued_msg st A = None"
           and "m \<in> set (msgs st)"
           and "Process1a A m st st2"
        then show ?thesis
        proof (cases "A = a")
          case True
          have h1: "WellFormed st2 (the (queued_msg st2 a))"
            by (smt (verit, ccfv_threshold) Process1a.elims(2) True Wellformed_Conservation_Next \<open>Process1a A m st st2\<close> \<open>queued_msg st A = None\<close> \<open>queued_msg st2 a = Some y\<close> assms(2) option.discI option.sel)
          have "y = M1b a (m # recent_msgs st a)"
            by (smt (verit, best) Process1a.elims(2) True \<open>Process1a A m st st2\<close> \<open>queued_msg st A = None\<close> \<open>queued_msg st2 a = Some y\<close> option.discI option.sel)
          have "Recv_acc st a m"
            by (metis Process1a.elims(2) True \<open>Process1a A m st st2\<close>)
          have "Store_acc a m st st2"
            by (metis Process1a.elims(2) True \<open>Process1a A m st st2\<close>)
          have "Send y st st2"
            by (metis Process1a.elims(2) True \<open>Process1a A m st st2\<close> \<open>queued_msg st A = None\<close> \<open>queued_msg st2 a = Some y\<close> \<open>y = M1b a (m # recent_msgs st a)\<close> option.discI)
          have "Process1a a m st st2"
            using \<open>Process1a A m st st2\<close> True by blast
          have "m \<notin> set (known_msgs_acc st a)"
            by (meson Recv_acc.elims(2) \<open>Recv_acc st a m\<close>)
          have "known_msgs_acc st2 a =  m # known_msgs_acc st a"
            using \<open>Store_acc a m st st2\<close> by auto
          have "y \<notin> set (known_msgs_acc st a)"
            by (metis FullSafetyInvariant.elims(2) KnownMsgs_accSpec.elims(2) Proper_acc.elims(2) \<open>is_safe a\<close> \<open>m \<notin> set (known_msgs_acc st a)\<close> \<open>y = M1b a (m # recent_msgs st a)\<close> assms(3) list.set_intros(1) ref.simps(2))
          have h2: "y \<notin> set (known_msgs_acc st2 a)"
            by (metis Proper_acc.elims(2) Recv_acc.elims(2) \<open>Recv_acc st a m\<close> \<open>known_msgs_acc st2 a = m # known_msgs_acc st a\<close> \<open>y = M1b a (m # recent_msgs st a)\<close> \<open>y \<notin> set (known_msgs_acc st a)\<close> list.set_intros(1) ref.simps(2) set_ConsD)
          have h3: "Proper_acc st2 a y"
            by (metis (no_types, lifting) FullSafetyInvariant.elims(2) Proper_acc.elims(1) RecentMsgsSpec.elims(2) \<open>is_safe a\<close> \<open>known_msgs_acc st2 a = m # known_msgs_acc st a\<close> \<open>y = M1b a (m # recent_msgs st a)\<close> assms(3) insert_iff list.simps(15) ref.simps(2) subsetD)
          show ?thesis
            by (metis \<open>queued_msg st2 a = Some y\<close> h1 h2 h3 option.sel)
        next
          case False
          then show ?thesis
            by (smt (verit) Process1a.elims(2) Proper_acc.elims(2) Proper_acc.elims(3) QueuedMsgSpec2.simps Recv_acc.elims(1) Store_acc.elims(2) Wellformed_Conservation_Next \<open>Process1a A m st st2\<close> \<open>is_safe a\<close> \<open>queued_msg st2 a = Some y\<close> assms(1) assms(2) option.discI)
        qed
      qed
    next
      assume "\<exists>A :: Acceptor. is_safe A
                        \<and> queued_msg st A \<noteq> None 
                        \<and> Process1b A (the (queued_msg st A)) st st2"
      then show ?thesis
          unfolding Process1b.simps
      proof (clarify)
        fix A y2
        assume "queued_msg st2 = (\<lambda>x. if x = A then None else queued_msg st x)"
        have "A \<noteq> a"
          using \<open>queued_msg st2 = (\<lambda>x. if x = A then None else queued_msg st x)\<close> \<open>queued_msg st2 a = Some y\<close> by auto
        have "queued_msg st2 a = queued_msg st a"
          using \<open>A \<noteq> a\<close> \<open>queued_msg st2 = (\<lambda>x. if x = A then None else queued_msg st x)\<close> by presburger
        have h1: "WellFormed st2 (the (queued_msg st2 a))"
          by (metis QueuedMsgSpec2.elims(2) Recv_acc.elims(2) Wellformed_Conservation_Next \<open>is_safe a\<close> \<open>queued_msg st2 a = Some y\<close> \<open>queued_msg st2 a = queued_msg st a\<close> assms(1) assms(2) option.discI)
        have h2: "y \<notin> set (known_msgs_acc st2 a)"
        proof -
          obtain aa :: Acceptor where
            f1: "queued_msg st aa \<noteq> None \<and> Process1b aa (the (queued_msg st aa)) st st2"
            using \<open>\<exists>A. is_safe A \<and> queued_msg st A \<noteq> None \<and> Process1b A (the (queued_msg st A)) st st2\<close> by blast
          then have "\<And>a. a \<noteq> aa \<or> queued_msg st2 a = None"
            by simp
          then have "aa = A"
            using f1 by (metis \<open>queued_msg st2 = (\<lambda>x. if x = A then None else queued_msg st x)\<close>)
          then have "\<And>a. A = a \<or> known_msgs_acc st2 a = known_msgs_acc st a"
            using f1 by simp
          then show ?thesis
            by (metis QueuedMsgSpec2.elims(2) Recv_acc.elims(2) \<open>A \<noteq> a\<close> \<open>is_safe a\<close> \<open>queued_msg st2 a = Some y\<close> \<open>queued_msg st2 a = queued_msg st a\<close> assms(1) option.discI option.sel)
        qed
        have h3: "Proper_acc st2 a y"
          by (metis Proper_acc.elims(1) QueuedMsgSpec2.elims(2) Recv_acc.elims(2) \<open>is_safe a\<close> \<open>queued_msg st2 a = Some y\<close> \<open>queued_msg st2 a = queued_msg st a\<close> assms(1) assms(2) next_known_msgs_acc_preserved option.discI option.sel)
        show ?thesis
          by (metis \<open>queued_msg st2 a = Some y\<close> h1 h2 h3 option.sel)
      qed
    next
      assume "\<exists>A :: Acceptor. is_safe A
                  \<and> queued_msg st A = None 
                  \<and> (\<exists>m \<in> set (msgs st). Process1b A m st st2)"
      then show ?thesis
        unfolding Process1b.simps
      proof (clarify)
        fix A m
        assume "queued_msg st2 = (\<lambda>x. if x = A then None else queued_msg st x)"
           and "Store_acc A m st st2"
        have "A \<noteq> a"
          using \<open>queued_msg st2 = (\<lambda>x. if x = A then None else queued_msg st x)\<close> \<open>queued_msg st2 a = Some y\<close> by auto
        have "queued_msg st2 a = queued_msg st a"
          using \<open>A \<noteq> a\<close> \<open>queued_msg st2 = (\<lambda>x. if x = A then None else queued_msg st x)\<close> by presburger
        have h1: "WellFormed st2 (the (queued_msg st2 a))"
          by (metis QueuedMsgSpec2.elims(2) Recv_acc.elims(2) Wellformed_Conservation_Next \<open>is_safe a\<close> \<open>queued_msg st2 a = Some y\<close> \<open>queued_msg st2 a = queued_msg st a\<close> assms(1) assms(2) option.discI)
        have h3: "Proper_acc st2 a y"
          by (metis Proper_acc.elims(2) Proper_acc.elims(3) QueuedMsgSpec2.simps Recv_acc.elims(2) \<open>is_safe a\<close> \<open>queued_msg st2 a = Some y\<close> \<open>queued_msg st2 a = queued_msg st a\<close> assms(1) assms(2) next_known_msgs_acc_preserved option.distinct(1) option.sel)
        have h2: "y \<notin> set (known_msgs_acc st2 a)"
          by (metis QueuedMsgSpec2.elims(2) Recv_acc.elims(2) Store_acc.elims(2) \<open>A \<noteq> a\<close> \<open>Store_acc A m st st2\<close> \<open>is_safe a\<close> \<open>queued_msg st2 a = Some y\<close> \<open>queued_msg st2 a = queued_msg st a\<close> assms(1) option.discI option.sel)
        show ?thesis
          by (metis \<open>queued_msg st2 a = Some y\<close> h1 h2 h3 option.sel)
      qed
    next
      assume "\<exists>A :: Acceptor. is_safe A
                        \<and> two_a_lrn_loop st A 
                        \<and> (\<exists>l :: Learner. Process1bLearnerLoopStep A l st st2)"
      then show ?thesis
        by (smt (verit) FullSafetyInvariant.elims(2) Process1bLearnerLoopStep.elims(2) Proper_acc.elims(1) QueuedMsgSpec2.simps Recv_acc.elims(2) Store_acc.elims(2) Wellformed_Conservation_Next \<open>is_safe a\<close> \<open>queued_msg st2 a = Some y\<close> assms(1) assms(2) assms(3) option.discI twoaLearnerLoopSpec.elims(2))
    next
      assume "\<exists>A. is_safe A \<and>
        two_a_lrn_loop st A \<and>
        Process1bLearnerLoopDone A st st2"
      then show ?thesis
        by (smt (verit) Process1bLearnerLoopDone.elims(1) Proper_acc.elims(1) QueuedMsgSpec2.simps Recv_acc.elims(2) Wellformed_Conservation_Next \<open>is_safe a\<close> \<open>queued_msg st2 a = Some y\<close> assms(1) assms(2) ext_inject option.discI surjective update_convs(6))
    next
      assume "LearnerProcessAction st st2"
      then show ?thesis
        unfolding LearnerProcessAction.simps LearnerAction.simps
      proof (clarify)
        fix ln
        assume "(\<exists>m\<in>set (msgs st). LearnerRecv ln m st st2) \<or>
              (\<exists>blt val. LearnerDecide ln blt val st st2)"
        then show ?thesis
        proof (elim disjE; clarify)
          fix m
          assume "m \<in> set (msgs st)"
             and "LearnerRecv ln m st st2"
          then show ?thesis
            by (smt (verit) LearnerRecv.elims(2) Proper_acc.elims(1) QueuedMsgSpec2.simps Recv_acc.elims(2) Wellformed_Conservation_Next \<open>is_safe a\<close> \<open>queued_msg st2 a = Some y\<close> assms(1) assms(2) option.discI select_convs(2) select_convs(5) surjective update_convs(3))
          next
            fix blt val
            assume "LearnerDecide ln blt val st st2"
            show ?thesis
              by (smt (verit) LearnerDecide.elims(2) Proper_acc.elims(1) QueuedMsgSpec2.simps Recv_acc.elims(2) Wellformed_Conservation_Next \<open>LearnerDecide ln blt val st st2\<close> \<open>is_safe a\<close> \<open>queued_msg st2 a = Some y\<close> assms(1) assms(2) ext_inject option.discI surjective update_convs(8))
        qed
      qed
    next
      assume "\<exists>A. \<not> is_safe A \<and> FakeSend1b A st st2"
      show ?thesis
        by (smt (verit) FakeSend1b.elims(1) Proper_acc.elims(1) QueuedMsgSpec2.simps Recv_acc.elims(2) Wellformed_Conservation_Next \<open>\<exists>A. \<not> is_safe A \<and> FakeSend1b A st st2\<close> \<open>is_safe a\<close> \<open>queued_msg st2 a = Some y\<close> assms(1) assms(2) option.discI select_convs(2) select_convs(5) surjective update_convs(1))
    next
      assume "\<exists>A. \<not> is_safe A \<and> FakeSend2a A st st2"
      then show ?thesis
        by (smt (verit) FakeSend2a.simps Proper_acc.elims(1) QueuedMsgSpec2.simps Recv_acc.elims(1) Wellformed_Conservation_Next \<open>is_safe a\<close> \<open>queued_msg st2 a = Some y\<close> assms(1) assms(2) ext_inject option.discI surjective update_convs(1))
    qed
qed

lemma QueuedMsgSpec2_Conserved:
  assumes "Spec f"
    shows "QueuedMsgSpec2 (f i)"
proof (induction i)
  case 0
  then show ?case 
    by (metis Init.elims QueuedMsgResult QueuedMsgSpec1.elims(2) QueuedMsgSpec2.simps Spec.simps assms length_greater_0_conv length_pos_if_in_set select_convs(1))
next
  case (Suc j)
  then show ?case
    by (metis PreSafetyResult QueuedMsgSpecInvariant2 Spec.elims(2) assms)
qed

lemma BVal_Doesnt_Change:
  assumes "Next st st2"
  shows "BVal st = BVal st2"
proof -have css: "ProposerSendAction st st2 \<or>
                (\<exists>A :: Acceptor. is_safe A
                            \<and> queued_msg st A = None 
                            \<and> (\<exists>m \<in> set (msgs st). Process1a A m st st2)) \<or>
                (\<exists>A :: Acceptor. is_safe A
                              \<and> queued_msg st A \<noteq> None 
                              \<and> Process1b A (the (queued_msg st A)) st st2) \<or>
                (\<exists>A :: Acceptor. is_safe A
                              \<and> queued_msg st A = None 
                              \<and> (\<exists>m \<in> set (msgs st). Process1b A m st st2)) \<or>
                (\<exists>A :: Acceptor. is_safe A
                              \<and> two_a_lrn_loop st A 
                              \<and> (\<exists>l :: Learner. Process1bLearnerLoopStep A l st st2)) \<or>
                (\<exists>A :: Acceptor. is_safe A
                              \<and> two_a_lrn_loop st A 
                              \<and> Process1bLearnerLoopDone A st st2) \<or>
                LearnerProcessAction st st2 \<or>
                (\<exists>A :: Acceptor. \<not> (is_safe A)
                              \<and> FakeSend1b A st st2) \<or>
                (\<exists>A :: Acceptor. \<not> (is_safe A)
                              \<and> FakeSend2a A st st2)
                "
    using assms next_split by presburger
    then show ?thesis
    proof (elim disjE)
      assume "ProposerSendAction st st2"
      then show ?thesis
        by auto
    next
      assume "\<exists>A. is_safe A \<and>
                queued_msg st A = None \<and>
                (\<exists>m\<in>set (msgs st).
                    Process1a A m st st2)"
      then show ?thesis
        by (metis Process1a.elims(2))
    next
      assume "\<exists>A :: Acceptor. is_safe A
                        \<and> queued_msg st A \<noteq> None 
                        \<and> Process1b A (the (queued_msg st A)) st st2"
      then show ?thesis
      proof -
        show ?thesis
          using \<open>\<exists>A. is_safe A \<and> queued_msg st A \<noteq> None \<and> Process1b A (the (queued_msg st A)) st st2\<close> by force
      qed
    next
      assume "\<exists>A :: Acceptor. is_safe A
                  \<and> queued_msg st A = None 
                  \<and> (\<exists>m \<in> set (msgs st). Process1b A m st st2)"
      then show ?thesis
      proof -
        show ?thesis
          using \<open>\<exists>A. is_safe A \<and> queued_msg st A = None \<and> (\<exists>m\<in>set (msgs st). Process1b A m st st2)\<close> by force
      qed
    next
      assume "\<exists>A :: Acceptor. is_safe A
                        \<and> two_a_lrn_loop st A 
                        \<and> (\<exists>l :: Learner. Process1bLearnerLoopStep A l st st2)"
      then show ?thesis
        by (metis Process1bLearnerLoopStep.elims(2))
    next
      assume "\<exists>A. is_safe A \<and>
        two_a_lrn_loop st A \<and>
        Process1bLearnerLoopDone A st st2"
      then show ?thesis
        by auto
    next
      assume "LearnerProcessAction st st2"
      then show ?thesis
        by (smt (verit) LearnerAction.elims(2) LearnerDecide.elims(2) LearnerProcessAction.elims(1) LearnerRecv.elims(2) ext_inject surjective update_convs(3) update_convs(8))
    next
      assume "\<exists>A. \<not> is_safe A \<and> FakeSend1b A st st2"
      show ?thesis
        by (metis FakeSend1b.elims(2) \<open>\<exists>A. \<not> is_safe A \<and> FakeSend1b A st st2\<close> select_convs(9) surjective update_convs(1))
    next
      assume "\<exists>A. \<not> is_safe A \<and> FakeSend2a A st st2"
      then show ?thesis
        by (metis FakeSend2a.simps ext_inject surjective update_convs(1))
      qed
qed

lemma BVal_Constant_Ord:
  assumes "Spec f"
    shows "i \<le> j \<longrightarrow> BVal (f i) = BVal (f j)"
proof (induction j)
  case 0
  then show ?case 
    by fastforce
next
  case (Suc j)
  then show ?case
    by (smt (z3) BVal_Doesnt_Change Spec.elims(2) assms le_SucE)
qed

lemma BVal_Constant:
  assumes "Spec f"
    shows "BVal (f i) = BVal (f j)"
  by (metis BVal_Constant_Ord assms nat_le_linear)

lemma Wellformed_Constant:
  assumes "Spec f"
  shows "WellFormed (f i) m = WellFormed (f j) m"
  using BVal_Constant WellFormed_monotone assms by blast

lemma Choice_Made_Perminent_Next:
  assumes "ChosenIn st l b v"
      and "Next st st2"
    shows "ChosenIn st2 l b v"
proof -
  have mq: "known_msgs_lrn st2 l = known_msgs_lrn st l \<longrightarrow> ChosenIn st2 l b v"
    unfolding ChosenIn.simps Known2a.simps V.simps
    by (smt (verit) BVal_Doesnt_Change ChosenIn.simps Known2a.simps V.elims(2) assms(1) assms(2) mem_Collect_eq subset_iff)
  have css: "ProposerSendAction st st2 \<or>
                (\<exists>A :: Acceptor. is_safe A
                            \<and> queued_msg st A = None 
                            \<and> (\<exists>m \<in> set (msgs st). Process1a A m st st2)) \<or>
                (\<exists>A :: Acceptor. is_safe A
                              \<and> queued_msg st A \<noteq> None 
                              \<and> Process1b A (the (queued_msg st A)) st st2) \<or>
                (\<exists>A :: Acceptor. is_safe A
                              \<and> queued_msg st A = None 
                              \<and> (\<exists>m \<in> set (msgs st). Process1b A m st st2)) \<or>
                (\<exists>A :: Acceptor. is_safe A
                              \<and> two_a_lrn_loop st A 
                              \<and> (\<exists>l :: Learner. Process1bLearnerLoopStep A l st st2)) \<or>
                (\<exists>A :: Acceptor. is_safe A
                              \<and> two_a_lrn_loop st A 
                              \<and> Process1bLearnerLoopDone A st st2) \<or>
                LearnerProcessAction st st2 \<or>
                (\<exists>A :: Acceptor. \<not> (is_safe A)
                              \<and> FakeSend1b A st st2) \<or>
                (\<exists>A :: Acceptor. \<not> (is_safe A)
                              \<and> FakeSend2a A st st2)
                "
                using assms next_split by presburger
    then show ?thesis
    proof (elim disjE)
      assume "ProposerSendAction st st2"
      then show ?thesis
        using mq by fastforce
    next
      assume "\<exists>A. is_safe A \<and>
                queued_msg st A = None \<and>
                (\<exists>m\<in>set (msgs st).
                    Process1a A m st st2)"
      then show ?thesis
        by (metis Process1a.elims(2) Store_acc.elims(2) mq)
    next
      assume "\<exists>A :: Acceptor. is_safe A
                        \<and> queued_msg st A \<noteq> None 
                        \<and> Process1b A (the (queued_msg st A)) st st2"
      then show ?thesis
        by (metis Process1b.elims(2) Store_acc.elims(2) mq)
    next
      assume "\<exists>A :: Acceptor. is_safe A
                  \<and> queued_msg st A = None 
                  \<and> (\<exists>m \<in> set (msgs st). Process1b A m st st2)"
      then show ?thesis
        by (metis Process1b.elims(2) Store_acc.elims(1) mq)
    next
      assume "\<exists>A :: Acceptor. is_safe A
                        \<and> two_a_lrn_loop st A 
                        \<and> (\<exists>l :: Learner. Process1bLearnerLoopStep A l st st2)"
      then show ?thesis
        by (metis Process1bLearnerLoopStep.elims(2) Store_acc.elims(2) mq)
    next
      assume "\<exists>A. is_safe A \<and>
        two_a_lrn_loop st A \<and>
        Process1bLearnerLoopDone A st st2"
      then show ?thesis
        by (smt (z3) Process1bLearnerLoopDone.elims(1) ext_inject mq surjective update_convs(6))
    next
      assume "LearnerProcessAction st st2"
      then show ?thesis
        unfolding LearnerProcessAction.simps LearnerAction.simps
      proof (clarify)
        fix ln
        assume "(\<exists>m\<in>set (msgs st). LearnerRecv ln m st st2) \<or>
              (\<exists>blt val. LearnerDecide ln blt val st st2)"
        then show ?thesis
        proof (elim disjE; clarify)
          fix m
          assume "m \<in> set (msgs st)"
             and "LearnerRecv ln m st st2"
          then show ?thesis
            unfolding LearnerRecv.simps
          proof (cases "ln = l")
            case True
            have "known_msgs_lrn st2 l = m # known_msgs_lrn st l"
              by (smt (verit, del_insts) LearnerRecv.elims(2) True \<open>LearnerRecv ln m st st2\<close> select_convs(3) surjective update_convs(3))
            show ?thesis 
              by (smt (verit) ChosenIn.simps Known2a.simps LearnerRecv.elims(2) V.simps \<open>LearnerRecv ln m st st2\<close> assms(1) ext_inject list.set_intros(2) mem_Collect_eq subset_iff surjective update_convs(3))
          next
            case False
            then show ?thesis
              by (smt (verit, ccfv_threshold) LearnerRecv.elims(2) \<open>LearnerRecv ln m st st2\<close> ext_inject mq surjective update_convs(3))
          qed
          next
            fix blt val
            assume "LearnerDecide ln blt val st st2"
            then show ?thesis
              by (metis (no_types, lifting) LearnerDecide.elims(2) ext_inject mq surjective update_convs(8))
        qed
      qed
    next
      assume "\<exists>A. \<not> is_safe A \<and> FakeSend1b A st st2"
      show ?thesis
        by (metis FakeSend1b.elims(1) \<open>\<exists>A. \<not> is_safe A \<and> FakeSend1b A st st2\<close> mq select_convs(3) surjective update_convs(1))
    next
      assume "\<exists>A. \<not> is_safe A \<and> FakeSend2a A st st2"
      then show ?thesis
        by (metis FakeSend2a.simps mq select_convs(3) surjective update_convs(1))
    qed
qed


lemma Choice_Made_Perminent:
  assumes "Spec f"
      and "ChosenIn (f i) l b v"
    shows "j \<ge> i \<longrightarrow> ChosenIn (f j) l b v"
proof (induction j)
  case 0
  then show ?case 
    using assms(2) by blast
next
  case (Suc j)
  then show ?case
    by (metis Choice_Made_Perminent_Next Spec.simps assms(1) assms(2) le_Suc_eq)
qed


lemma M1a_Good:
  assumes "m \<in> set (msgs st)"
      and "type m = T1a"
      and "m \<notin> set (known_msgs_lrn st l)"
    shows "Proper_lrn st l m"
  by (metis MessageType.distinct(1) MessageType.distinct(3) Proper_lrn.simps assms(2) empty_iff ref.simps(1) type.elims)

fun Msg_ref_Spec :: "State \<Rightarrow> bool" where
  "Msg_ref_Spec st = (
    \<forall>m \<in> set (msgs st). is_safe (acc m) \<longrightarrow> ref m \<subseteq> set (msgs st)
  )"

lemma Msg_ref_Spec_Next:
  assumes "Next st st2"
      and "Msg_ref_Spec st"
      and "RecentMsgsSpec st"
      and "KnownMsgs_accSpec st"
    shows "Msg_ref_Spec st2"
proof -
  have css: "ProposerSendAction st st2 \<or>
                (\<exists>A :: Acceptor. is_safe A
                            \<and> queued_msg st A = None 
                            \<and> (\<exists>m \<in> set (msgs st). Process1a A m st st2)) \<or>
                (\<exists>A :: Acceptor. is_safe A
                              \<and> queued_msg st A \<noteq> None 
                              \<and> Process1b A (the (queued_msg st A)) st st2) \<or>
                (\<exists>A :: Acceptor. is_safe A
                              \<and> queued_msg st A = None 
                              \<and> (\<exists>m \<in> set (msgs st). Process1b A m st st2)) \<or>
                (\<exists>A :: Acceptor. is_safe A
                              \<and> two_a_lrn_loop st A 
                              \<and> (\<exists>l :: Learner. Process1bLearnerLoopStep A l st st2)) \<or>
                (\<exists>A :: Acceptor. is_safe A
                              \<and> two_a_lrn_loop st A 
                              \<and> Process1bLearnerLoopDone A st st2) \<or>
                LearnerProcessAction st st2 \<or>
                (\<exists>A :: Acceptor. \<not> (is_safe A)
                              \<and> FakeSend1b A st st2) \<or>
                (\<exists>A :: Acceptor. \<not> (is_safe A)
                              \<and> FakeSend2a A st st2)
                "
                using assms next_split by presburger
    then show ?thesis
    proof (elim disjE)
      assume "ProposerSendAction st st2"
      then show ?thesis
        by (smt (verit) Msg_ref_Spec.elims(1) ProposerSendAction.elims(2) Send1a.elims(2) assms(1) assms(2) empty_iff next_msgs_preserved ref.simps(1) select_convs(1) set_ConsD subsetD subsetI surjective update_convs(1))
    next
      assume "\<exists>A. is_safe A \<and>
                queued_msg st A = None \<and>
                (\<exists>m\<in>set (msgs st).
                    Process1a A m st st2)"
      then show ?thesis
      proof (clarify)
        fix A m
        assume "is_safe A"
           and "queued_msg st A = None"
           and "m \<in> set (msgs st)"
           and "Process1a A m st st2"
        define new1b where "new1b = M1b A (m # recent_msgs st A)"
        show ?thesis
        proof (cases "WellFormed st new1b")
          case True
          have "ref new1b \<subseteq> set (msgs st)"
            by (metis KnownMsgs_accSpec.elims(2) RecentMsgsSpec.elims(2) \<open>is_safe A\<close> \<open>m \<in> set (msgs st)\<close> assms(3) assms(4) new1b_def ref.simps(2) set_ConsD subsetD subsetI)
          have "msgs st2 = new1b # msgs st"
            by (metis Process1a.elims(2) Send.elims(1) True \<open>Process1a A m st st2\<close> new1b_def)
          then have "ref new1b \<subseteq> set (msgs st2)"
            using \<open>ref new1b \<subseteq> set (msgs st)\<close> by auto
          then show ?thesis
            using \<open>msgs st2 = new1b # msgs st\<close> assms(2) by auto
        next
          case False
          then show ?thesis
            by (metis Msg_ref_Spec.elims(2) Msg_ref_Spec.elims(3) Process1a.elims(2) \<open>Process1a A m st st2\<close> assms(2) new1b_def)
        qed
      qed
    next
      assume "\<exists>A :: Acceptor. is_safe A
                        \<and> queued_msg st A \<noteq> None 
                        \<and> Process1b A (the (queued_msg st A)) st st2"
      then show ?thesis
        by (metis Msg_ref_Spec.elims(2) Msg_ref_Spec.elims(3) Process1b.elims(2) assms(2))

    next
      assume "\<exists>A :: Acceptor. is_safe A
                  \<and> queued_msg st A = None 
                  \<and> (\<exists>m \<in> set (msgs st). Process1b A m st st2)"
      then show ?thesis
        by (metis Msg_ref_Spec.simps Process1b.elims(2) assms(2))
    next
      assume "\<exists>A :: Acceptor. is_safe A
                        \<and> two_a_lrn_loop st A 
                        \<and> (\<exists>l :: Learner. Process1bLearnerLoopStep A l st st2)"
      then show ?thesis
      proof (clarify)
        fix A l
        assume "is_safe A"
           and "two_a_lrn_loop st A"
           and "Process1bLearnerLoopStep A l st st2"
        define new2a where "new2a = M2a l A (recent_msgs st A)"
        show ?thesis
        proof (cases "WellFormed st new2a")
          case True
          then show ?thesis
            by (smt (verit) KnownMsgs_accSpec.elims(2) Msg_ref_Spec.simps Process1bLearnerLoopStep.elims(2) RecentMsgsSpec.elims(2) Send.elims(2) \<open>Process1bLearnerLoopStep A l st st2\<close> \<open>is_safe A\<close> assms(2) assms(3) assms(4) in_mono list.set_intros(2) ref.simps(3) set_ConsD subsetI)
        next
          case False
          then show ?thesis 
            by (metis Msg_ref_Spec.simps Process1bLearnerLoopStep.elims(2) \<open>Process1bLearnerLoopStep A l st st2\<close> assms(2) new2a_def)
        qed
      qed
    next
      assume "\<exists>A. is_safe A \<and>
        two_a_lrn_loop st A \<and>
        Process1bLearnerLoopDone A st st2"
      then show ?thesis
        by (smt (verit) Msg_ref_Spec.simps Process1bLearnerLoopDone.elims(1) assms(2) ext_inject surjective update_convs(6))
    next
      assume "LearnerProcessAction st st2"
      then show ?thesis
        unfolding LearnerProcessAction.simps LearnerAction.simps
      proof (clarify)
        fix ln
        assume "(\<exists>m\<in>set (msgs st). LearnerRecv ln m st st2) \<or>
              (\<exists>blt val. LearnerDecide ln blt val st st2)"
        then show ?thesis
        proof (elim disjE; clarify)
          fix m
          assume "m \<in> set (msgs st)"
             and "LearnerRecv ln m st st2"
          then show ?thesis
            unfolding LearnerRecv.simps
          proof (cases "ln = l")
            case True
            have "known_msgs_lrn st2 l = m # known_msgs_lrn st l"
              by (smt (verit, del_insts) LearnerRecv.elims(2) True \<open>LearnerRecv ln m st st2\<close> select_convs(3) surjective update_convs(3))
            show ?thesis 
              by (metis (no_types, lifting) LearnerRecv.elims(2) Msg_ref_Spec.simps \<open>LearnerRecv ln m st st2\<close> assms(2) select_convs(1) surjective update_convs(3))
          next
            case False
            then show ?thesis
              by (metis (no_types, lifting) LearnerRecv.elims(2) Msg_ref_Spec.simps \<open>LearnerRecv ln m st st2\<close> assms(2) select_convs(1) surjective update_convs(3))
          qed
          next
            fix blt val
            assume "LearnerDecide ln blt val st st2"
            then show ?thesis
              by (metis (no_types, lifting) LearnerDecide.elims(2) Msg_ref_Spec.simps assms(2) ext_inject surjective update_convs(8))
        qed
      qed
    next
      assume "\<exists>A. \<not> is_safe A \<and> FakeSend1b A st st2"
      show ?thesis
        by (smt (verit) FakeSend1b.elims(1) Msg_ref_Spec.simps \<open>\<exists>A. \<not> is_safe A \<and> FakeSend1b A st st2\<close> assms(2) hpaxos.acc.simps(2) list.set_intros(2) select_convs(1) set_ConsD subset_iff surjective update_convs(1))
    next
      assume "\<exists>A. \<not> is_safe A \<and> FakeSend2a A st st2"
      then show ?thesis
        unfolding FakeSend2a.simps Msg_ref_Spec.simps
      proof (clarify)
        fix m A fin ln x
        assume "m \<in> set (msgs st2)"
           and "\<not> is_safe A"
           and "let new2a = M2a ln A fin
               in WellFormed st new2a \<and>
                  st2 = st\<lparr>msgs := new2a # msgs st\<rparr>"
           and "is_safe (acc m)"
           and "x \<in> ref m"
        define new2a where "new2a = M2a ln A fin"
        have "\<not> is_safe (acc new2a)"
          by (simp add: \<open>\<not> is_safe A\<close> new2a_def)
        have "\<forall>m \<in> set (msgs st2). is_safe (acc new2a) \<longrightarrow> m \<in> set (msgs st)"
          using \<open>\<not> is_safe (acc new2a)\<close> by blast
        have "m \<noteq> new2a"
          using \<open>\<not> is_safe (acc new2a)\<close> \<open>is_safe (acc m)\<close> by blast
        have "ref m \<subseteq> set (msgs st)"
          by (metis Msg_ref_Spec.elims(2) \<open>is_safe (acc m)\<close> \<open>let new2a = M2a ln A fin in WellFormed st new2a \<and> st2 = st\<lparr>msgs := new2a # msgs st\<rparr>\<close> \<open>m \<in> set (msgs st2)\<close> \<open>m \<noteq> new2a\<close> assms(2) new2a_def select_convs(1) set_ConsD surjective update_convs(1))
        then show "x \<in> set (msgs st2)"
          using \<open>x \<in> ref m\<close> assms(1) next_msgs_preserved by blast
      qed
    qed
qed

lemma Msg_ref_Spec_Invariant:
  assumes "Spec f"
  shows "Msg_ref_Spec (f i)"
proof (induction i)
  case 0
  then show ?case 
    by (metis Init.elims Msg_ref_Spec.simps Spec.simps assms empty_iff empty_set select_convs(1))
next
  case (Suc i)
  then show ?case
    by (metis KnownMsgs_accSpecResult Msg_ref_Spec_Next RecentMsgsSpecResult Spec.elims(2) assms)
qed

fun WellFormed_Spec :: "State \<Rightarrow> bool" where
  "WellFormed_Spec st = (
    \<forall>m \<in> set (msgs st). is_safe (acc m) \<longrightarrow> WellFormed st m
  )"

lemma WellFormed_Spec_Next:
  assumes "Next st st2"
      and "WellFormed_Spec st"
      and "KnownMsgs_accSpec st"
    shows "WellFormed_Spec st2"
proof -
  have css: "ProposerSendAction st st2 \<or>
                (\<exists>A :: Acceptor. is_safe A
                            \<and> queued_msg st A = None 
                            \<and> (\<exists>m \<in> set (msgs st). Process1a A m st st2)) \<or>
                (\<exists>A :: Acceptor. is_safe A
                              \<and> queued_msg st A \<noteq> None 
                              \<and> Process1b A (the (queued_msg st A)) st st2) \<or>
                (\<exists>A :: Acceptor. is_safe A
                              \<and> queued_msg st A = None 
                              \<and> (\<exists>m \<in> set (msgs st). Process1b A m st st2)) \<or>
                (\<exists>A :: Acceptor. is_safe A
                              \<and> two_a_lrn_loop st A 
                              \<and> (\<exists>l :: Learner. Process1bLearnerLoopStep A l st st2)) \<or>
                (\<exists>A :: Acceptor. is_safe A
                              \<and> two_a_lrn_loop st A 
                              \<and> Process1bLearnerLoopDone A st st2) \<or>
                LearnerProcessAction st st2 \<or>
                (\<exists>A :: Acceptor. \<not> (is_safe A)
                              \<and> FakeSend1b A st st2) \<or>
                (\<exists>A :: Acceptor. \<not> (is_safe A)
                              \<and> FakeSend2a A st st2)
                "
                using assms next_split by presburger
    then show ?thesis
    proof (elim disjE)
      assume "ProposerSendAction st st2"
      then show ?thesis
          by (smt (verit) MessageType.distinct(1) MessageType.distinct(3) ProposerSendAction.elims(2) Send1a.elims(2) WellFormed.elims(1) WellFormed_Spec.elims(1) Wellformed_Conservation_Next assms(1) assms(2) isValidMessage.simps(1) select_convs(1) set_ConsD surjective type.simps(1) update_convs(1))
    next
      assume "\<exists>A. is_safe A \<and>
                queued_msg st A = None \<and>
                (\<exists>m\<in>set (msgs st).
                    Process1a A m st st2)"
      then show ?thesis
      proof (clarify)
        fix A m
        assume "is_safe A"
           and "queued_msg st A = None"
           and "m \<in> set (msgs st)"
           and "Process1a A m st st2"
        define new1b where "new1b = M1b A (m # recent_msgs st A)"
        show ?thesis
        proof (cases "WellFormed st new1b")
          case True
          then show ?thesis
            by (smt (verit) Process1a.elims(2) Send.elims(2) WellFormed_Spec.elims(1) Wellformed_Conservation_Next \<open>Process1a A m st st2\<close> assms(1) assms(2) set_ConsD)
        next
          case False
          then show ?thesis
            by (metis Process1a.elims(2) WellFormed_Spec.elims(1) Wellformed_Conservation_Next \<open>Process1a A m st st2\<close> assms(1) assms(2) new1b_def)
        qed
      qed
    next
      assume "\<exists>A :: Acceptor. is_safe A
                        \<and> queued_msg st A \<noteq> None 
                        \<and> Process1b A (the (queued_msg st A)) st st2"
      then show ?thesis
        by (metis Process1b.elims(2) WellFormed_Spec.elims(2) WellFormed_Spec.elims(3) Wellformed_Conservation_Next assms(1) assms(2))
    next
      assume "\<exists>A :: Acceptor. is_safe A
                  \<and> queued_msg st A = None 
                  \<and> (\<exists>m \<in> set (msgs st). Process1b A m st st2)"
      then show ?thesis
      proof (clarify)
        fix A m
        assume "is_safe A"
           and "queued_msg st A = None"
           and "m \<in> set (msgs st)"
        have "msgs st = msgs st2"
          using \<open>\<exists>A. is_safe A \<and> queued_msg st A = None \<and> (\<exists>m\<in>set (msgs st). Process1b A m st st2)\<close> by fastforce
        then show ?thesis
          by (metis WellFormed_Spec.elims(1) Wellformed_Conservation_Next assms(1) assms(2))
      qed
    next
      assume "\<exists>A :: Acceptor. is_safe A
                        \<and> two_a_lrn_loop st A 
                        \<and> (\<exists>l :: Learner. Process1bLearnerLoopStep A l st st2)"
      then show ?thesis
      proof (clarify)
        fix A l
        assume "is_safe A"
           and "two_a_lrn_loop st A"
           and "Process1bLearnerLoopStep A l st st2"
        define new2a where "new2a = M2a l A (recent_msgs st A)"
        show ?thesis
        proof (cases "WellFormed st new2a")
          case True
          then show ?thesis
            by (smt (verit) Process1bLearnerLoopStep.elims(2) Send.elims(2) WellFormed_Spec.elims(1) Wellformed_Conservation_Next \<open>Process1bLearnerLoopStep A l st st2\<close> assms(1) assms(2) set_ConsD)
        next
          case False
          then show ?thesis 
            by (metis Process1bLearnerLoopStep.elims(2) WellFormed_Spec.elims(1) Wellformed_Conservation_Next \<open>Process1bLearnerLoopStep A l st st2\<close> assms(1) assms(2) new2a_def)
        qed
      qed
    next
      assume "\<exists>A. is_safe A \<and>
        two_a_lrn_loop st A \<and>
        Process1bLearnerLoopDone A st st2"
      then show ?thesis
        by (metis (no_types, lifting) Process1bLearnerLoopDone.elims(1) WellFormed_Spec.elims(1) Wellformed_Conservation_Next assms(1) assms(2) select_convs(1) surjective update_convs(6))
    next
      assume "LearnerProcessAction st st2"
      then show ?thesis
        unfolding LearnerProcessAction.simps LearnerAction.simps
      proof (clarify)
        fix ln
        assume "(\<exists>m\<in>set (msgs st). LearnerRecv ln m st st2) \<or>
              (\<exists>blt val. LearnerDecide ln blt val st st2)"
        then show ?thesis
        proof (elim disjE; clarify)
          fix m
          assume "m \<in> set (msgs st)"
             and "LearnerRecv ln m st st2"
          then show ?thesis
            by (metis (no_types, lifting) LearnerRecv.elims(2) WellFormed_Spec.elims(1) Wellformed_Conservation_Next assms(1) assms(2) select_convs(1) surjective update_convs(3))
          next
            fix blt val
            assume "LearnerDecide ln blt val st st2"
            then show ?thesis
              by (metis (no_types, lifting) LearnerDecide.elims(2) WellFormed_Spec.elims(1) Wellformed_Conservation_Next assms(1) assms(2) select_convs(1) surjective update_convs(8))
        qed
      qed
    next
      assume "\<exists>A. \<not> is_safe A \<and> FakeSend1b A st st2"
      show ?thesis
        by (smt (z3) FakeSend1b.elims(1) WellFormed_Spec.elims(1) Wellformed_Conservation_Next \<open>\<exists>A. \<not> is_safe A \<and> FakeSend1b A st st2\<close> assms(1) assms(2) select_convs(1) set_ConsD surjective update_convs(1))
    next
      assume "\<exists>A. \<not> is_safe A \<and> FakeSend2a A st st2"
      then show ?thesis
        by (smt (z3) FakeSend2a.simps WellFormed_Spec.elims(1) Wellformed_Conservation_Next assms(1) assms(2) ext_inject set_ConsD surjective update_convs(1))
    qed
qed

lemma WellFormed_Spec_Invariant:
  assumes "Spec f"
  shows "WellFormed_Spec (f i)"
proof (induction i)
  case 0
  then show ?case 
    by (metis Init.elims WellFormed_Spec.simps Spec.simps assms empty_iff empty_set select_convs(1))
next
  case (Suc i)
  then show ?case
    by (metis KnownMsgs_accSpecResult WellFormed_Spec_Next Spec.elims(2) assms)
qed


fun Enabled :: "(State \<Rightarrow> State \<Rightarrow> bool) \<Rightarrow> State \<Rightarrow> bool" where
  "Enabled r st = (\<exists>st2. r st st2)"

lemma Exists_Enabled_Swap:
  shows "Enabled (\<lambda>st st2. \<exists>v. R v st st2) s = (\<exists>v. Enabled (R v) s)"  
  by auto

(* Send1a is always enabled.*)
lemma Send1a_Enabled:
  shows "Enabled (Send1a b) st = True"
  by fastforce

lemma Process1aAlt1:
  assumes "WellFormed st (M1b a (m # recent_msgs st a))"
      and "type m = T1a"
      and "Recv_acc st a m"
    shows "Process1a a m st (st\<lparr>msgs := M1b a (m # recent_msgs st a) # msgs st, 
                                recent_msgs := (
                                  \<lambda>a2. if a2 = a then [] 
                                                 else recent_msgs st a2),
                                queued_msg := (
                                  \<lambda>a2. if a2 = a then Some (M1b a (m # recent_msgs st a)) 
                                                 else queued_msg st a2),
                                known_msgs_acc := (
                                  \<lambda>x. if a = x 
                                      then m # known_msgs_acc st x
                                      else known_msgs_acc st x) \<rparr>)"
proof -
  define st2 where "st2 = (st\<lparr>msgs := M1b a (m # recent_msgs st a) # msgs st, 
                              recent_msgs := (
                                \<lambda>a2. if a2 = a then [] 
                                               else recent_msgs st a2),
                              queued_msg := (
                                \<lambda>a2. if a2 = a then Some (M1b a (m # recent_msgs st a)) 
                                               else queued_msg st a2),
                              known_msgs_acc := (
                                \<lambda>x. if a = x 
                                    then m # known_msgs_acc st x
                                    else known_msgs_acc st x) \<rparr>)"
  
  have "Store_acc a m st st2" 
    by (simp add: st2_def)
  have "Send (M1b a (m # recent_msgs st a)) st st2
          \<and> (recent_msgs st2 = (
              \<lambda>a2. if a2 = a then [] 
                             else recent_msgs st a2))
          \<and> (queued_msg st2 = (
              \<lambda>a2. if a2 = a then Some (M1b a (m # recent_msgs st a)) 
                             else queued_msg st a2))"
    by (simp add: st2_def)
  show ?thesis
    unfolding Process1a.simps
    by (smt (verit, ccfv_SIG) \<open>Send (M1b a (m # recent_msgs st a)) st st2 \<and> recent_msgs st2 = (\<lambda>a2. if a2 = a then [] else recent_msgs st a2) \<and> queued_msg st2 = (\<lambda>a2. if a2 = a then Some (M1b a (m # recent_msgs st a)) else queued_msg st a2)\<close> \<open>Store_acc a m st st2\<close> assms(1) assms(2) assms(3) ext_inject st2_def surjective update_convs(1) update_convs(2) update_convs(4) update_convs(5))
qed

lemma Process1aAlt2:
  assumes "\<not> WellFormed st (M1b a (m # recent_msgs st a))"
      and "type m = T1a"
      and "Recv_acc st a m"
    shows "Process1a a m st (st\<lparr>recent_msgs := (
                              \<lambda>a2. if a2 = a then m # recent_msgs st a2 
                                             else recent_msgs st a2),
                            known_msgs_acc := (
                                \<lambda>x. if a = x 
                                    then m # known_msgs_acc st x
                                    else known_msgs_acc st x)\<rparr>)"
proof -
  define st2 where "st2 = (st\<lparr>recent_msgs := (
                              \<lambda>a2. if a2 = a then m # recent_msgs st a2 
                                             else recent_msgs st a2),
                            known_msgs_acc := (
                                \<lambda>x. if a = x 
                                    then m # known_msgs_acc st x
                                    else known_msgs_acc st x)\<rparr>)"
  
  have "Store_acc a m st st2" 
    by (simp add: st2_def)
  have "(recent_msgs st2 = (
              \<lambda>a2. if a2 = a then m # recent_msgs st a2 
                             else recent_msgs st a2))
          \<and> (msgs st = msgs st2)
          \<and> (queued_msg st = queued_msg st2)"
    by (simp add: st2_def)
  show ?thesis
    unfolding Process1a.simps
    using assms(1) assms(2) assms(3) by auto
qed

lemma Process1a_Enabled:
  shows "Enabled (Process1a a m) st = (type m = T1a \<and> Recv_acc st a m)"
  by (metis (no_types, lifting) Enabled.simps Process1a.simps Process1aAlt1 Process1aAlt2)

lemma Process1a_Trans:
  assumes "m \<notin> set (known_msgs_acc st a2)"
      and "Enabled (Process1a a1 m) st"
    shows "Enabled (Process1a a2 m) st"
  by (metis MessageType.distinct(1) MessageType.distinct(3) Process1a_Enabled Proper_acc.elims(1) Recv_acc.elims(2) Recv_acc.elims(3) assms(1) assms(2) empty_iff ref.simps(1) type.elims)

lemma Process1bAlt1:
  assumes "\<forall> mb b :: Ballot. MaxBal st a b \<and> B m b \<longrightarrow> mb \<le> b"
      and "type m = T1b"
      and "Recv_acc st a m"
    shows "Process1b a m st (st\<lparr>recent_msgs := (
                                      \<lambda>x. if x = a 
                                          then m # recent_msgs st x
                                          else recent_msgs st x ),
                                known_msgs_acc := (
                                  \<lambda>x. if a = x 
                                      then m # known_msgs_acc st x
                                      else known_msgs_acc st x),
                                two_a_lrn_loop := (\<lambda>x.
                                    if x = a
                                    then True
                                    else two_a_lrn_loop st x),
                                 processed_lrns := (\<lambda>x.
                                      if x = a
                                      then {}
                                      else processed_lrns st x),
                                queued_msg := (\<lambda>x.
                                      if x = a
                                      then None
                                      else queued_msg st x) \<rparr>)"
proof -
  define st2 where "st2 = st\<lparr>recent_msgs := (
                                      \<lambda>x. if x = a 
                                          then m # recent_msgs st x
                                          else recent_msgs st x ),
                            known_msgs_acc := (
                              \<lambda>x. if a = x 
                                  then m # known_msgs_acc st x
                                  else known_msgs_acc st x),
                            two_a_lrn_loop := (\<lambda>x.
                                if x = a
                                then True
                                else two_a_lrn_loop st x),
                             processed_lrns := (\<lambda>x.
                                  if x = a
                                  then {}
                                  else processed_lrns st x),
                            queued_msg := (\<lambda>x.
                                  if x = a
                                  then None
                                  else queued_msg st x) \<rparr>"
  have "recent_msgs st2 = (
        \<lambda>x. if x = a 
            then m # recent_msgs st x
            else recent_msgs st x )" by (simp add: st2_def)
  have "queued_msg st2 = (\<lambda>x.
          if x = a
          then None
          else queued_msg st x)" by (simp add: st2_def)
  have "Store_acc a m st st2" by (simp add: st2_def)
  have "two_a_lrn_loop st2 = (\<lambda>x.
          if x = a
          then True
          else two_a_lrn_loop st x)
        \<and> processed_lrns st2 = (\<lambda>x.
          if x = a
          then {}
          else processed_lrns st x)" by (simp add: st2_def)
  have "(msgs st2 = msgs st)
    \<and> (decision st2 = decision st)
    \<and> (BVal st2 = BVal st)" by (simp add: st2_def)
  show ?thesis
    unfolding Process1b.simps
    using \<open>Store_acc a m st st2\<close> \<open>msgs st2 = msgs st \<and> decision st2 = decision st \<and> BVal st2 = BVal st\<close> \<open>queued_msg st2 = (\<lambda>x. if x = a then None else queued_msg st x)\<close> \<open>recent_msgs st2 = (\<lambda>x. if x = a then m # recent_msgs st x else recent_msgs st x)\<close> \<open>two_a_lrn_loop st2 = (\<lambda>x. if x = a then True else two_a_lrn_loop st x) \<and> processed_lrns st2 = (\<lambda>x. if x = a then {} else processed_lrns st x)\<close> assms(1) assms(2) assms(3) st2_def by fastforce
qed

lemma Process1bAlt2:
  assumes "\<not> (\<forall> mb b :: Ballot. MaxBal st a b \<and> B m b \<longrightarrow> mb \<le> b)"
      and "type m = T1b"
      and "Recv_acc st a m"
    shows "Process1b a m st (st\<lparr>recent_msgs := (
                                      \<lambda>x. if x = a 
                                          then m # recent_msgs st x
                                          else recent_msgs st x ),
                                known_msgs_acc := (
                                  \<lambda>x. if a = x 
                                      then m # known_msgs_acc st x
                                      else known_msgs_acc st x),
                                queued_msg := (\<lambda>x.
                                      if x = a
                                      then None
                                      else queued_msg st x) \<rparr>)"
proof -
  define st2 where "st2 = st\<lparr>recent_msgs := (
                                      \<lambda>x. if x = a 
                                          then m # recent_msgs st x
                                          else recent_msgs st x ),
                            known_msgs_acc := (
                              \<lambda>x. if a = x 
                                  then m # known_msgs_acc st x
                                  else known_msgs_acc st x),
                            queued_msg := (\<lambda>x.
                                  if x = a
                                  then None
                                  else queued_msg st x) \<rparr>"
  have "recent_msgs st2 = (
        \<lambda>x. if x = a 
            then m # recent_msgs st x
            else recent_msgs st x )" by (simp add: st2_def)
  have "queued_msg st2 = (\<lambda>x.
          if x = a
          then None
          else queued_msg st x)" by (simp add: st2_def)
  have "Store_acc a m st st2" by (simp add: st2_def)
  have "two_a_lrn_loop st2 = two_a_lrn_loop st
        \<and> processed_lrns st2 = processed_lrns st" by (simp add: st2_def)
  have "(msgs st2 = msgs st)
    \<and> (decision st2 = decision st)
    \<and> (BVal st2 = BVal st)" by (simp add: st2_def)
  show ?thesis
    unfolding Process1b.simps
    using \<open>Store_acc a m st st2\<close> \<open>msgs st2 = msgs st \<and> decision st2 = decision st \<and> BVal st2 = BVal st\<close> \<open>queued_msg st2 = (\<lambda>x. if x = a then None else queued_msg st x)\<close> \<open>recent_msgs st2 = (\<lambda>x. if x = a then m # recent_msgs st x else recent_msgs st x)\<close> \<open>two_a_lrn_loop st2 = two_a_lrn_loop st \<and> processed_lrns st2 = processed_lrns st\<close> assms(1) assms(2) assms(3) st2_def by blast
qed

lemma Process1b_Enabled:
  shows "Enabled (Process1b a m) st = (type m = T1b \<and> Recv_acc st a m)"
  by (smt (verit, best) Enabled.simps Process1b.simps Process1bAlt1 Process1bAlt2)

lemma Process2aAlt:
  assumes "type m = T2a"
      and "Recv_acc st a m"
    shows "Process2a a m st (st\<lparr>recent_msgs := (
                                  \<lambda>x. if x = a 
                                      then m # recent_msgs st x
                                      else recent_msgs st x ),
                                known_msgs_acc := (
                                      \<lambda>x. if a = x 
                                          then m # known_msgs_acc st x
                                          else known_msgs_acc st x
                                  )\<rparr>)"
proof -
  define st2 where "st2 = st\<lparr>recent_msgs := (
                                  \<lambda>x. if x = a 
                                      then m # recent_msgs st x
                                      else recent_msgs st x ),
                              known_msgs_acc := (
                                    \<lambda>x. if a = x 
                                        then m # known_msgs_acc st x
                                        else known_msgs_acc st x
                                )\<rparr>"
  have "Store_acc a m st st2
    \<and> recent_msgs st2 = (
        \<lambda>x. if x = a 
            then m # recent_msgs st x
            else recent_msgs st x )
    \<and> (msgs st2 = msgs st)
    \<and> (queued_msg st2 = queued_msg st)
    \<and> (two_a_lrn_loop st2 = two_a_lrn_loop st)
    \<and> (processed_lrns st2 = processed_lrns st)
    \<and> (decision st2 = decision st)
    \<and> (BVal st2 = BVal st)" by (simp add: st2_def)
  show ?thesis
    unfolding Process2a.simps
    using \<open>Store_acc a m st st2 \<and> recent_msgs st2 = (\<lambda>x. if x = a then m # recent_msgs st x else recent_msgs st x) \<and> msgs st2 = msgs st \<and> queued_msg st2 = queued_msg st \<and> two_a_lrn_loop st2 = two_a_lrn_loop st \<and> processed_lrns st2 = processed_lrns st \<and> decision st2 = decision st \<and> BVal st2 = BVal st\<close> assms(1) assms(2) st2_def by fastforce
qed

lemma Process2a_Enabled:
  shows "Enabled (Process2a a m) st = (type m = T2a \<and> Recv_acc st a m)"
  by (metis (no_types, lifting) Enabled.simps Process2a.simps Process2aAlt)

lemma Process1bLearnerLoopStepAlt1:
  assumes "WellFormed st (M2a ln a (recent_msgs st a))"
  shows "Process1bLearnerLoopStep a ln st (
                              st\<lparr>processed_lrns := (
                                    \<lambda>x . if x = a
                                         then {ln} \<union> processed_lrns st x
                                         else processed_lrns st x),
                                msgs := M2a ln a (recent_msgs st a) # msgs st, 
                                known_msgs_acc := (
                                    \<lambda>x. if a = x 
                                        then M2a ln a (recent_msgs st a) # known_msgs_acc st x
                                        else known_msgs_acc st x),
                                recent_msgs := (
                                    \<lambda>x . if x = a
                                       then [M2a ln a (recent_msgs st a)]
                                       else recent_msgs st x) \<rparr>)"
proof -
  define new2a where "new2a = M2a ln a (recent_msgs st a)"
  define st2 where "st2 = (st\<lparr>processed_lrns := (
                                    \<lambda>x . if x = a
                                         then {ln} \<union> processed_lrns st x
                                         else processed_lrns st x),
                                msgs := new2a # msgs st, 
                                known_msgs_acc := (
                                    \<lambda>x. if a = x 
                                        then new2a # known_msgs_acc st x
                                        else known_msgs_acc st x),
                                recent_msgs := (
                                    \<lambda>x . if x = a
                                       then [new2a]
                                       else recent_msgs st x) \<rparr>)"
  have "Send new2a st st2
          \<and> Store_acc a new2a st st2
          \<and> (recent_msgs st2 = (
              \<lambda>x . if x = a
                 then [new2a]
                 else recent_msgs st x))" 
    by (simp add: st2_def)
  have "processed_lrns st2 = (
          \<lambda>x . if x = a
               then {ln} \<union> processed_lrns st x
               else processed_lrns st x)" 
    by (simp add: st2_def)
  have "(queued_msg st2 = queued_msg st)
          \<and> (two_a_lrn_loop st2 = two_a_lrn_loop st)
          \<and> (decision st2 = decision st)
          \<and> (BVal st2 = BVal st)" 
    by (simp add: st2_def)
  show ?thesis
    unfolding Process1bLearnerLoopStep.simps simps
    using assms by force
qed

lemma Process1bLearnerLoopStepAlt2:
  assumes "\<not> WellFormed st (M2a ln a (recent_msgs st a))"
  shows "Process1bLearnerLoopStep a ln st (
                        st\<lparr>processed_lrns := (
                                    \<lambda>x . if x = a
                                         then {ln} \<union> processed_lrns st x
                                         else processed_lrns st x)\<rparr>)"
proof -
  define st2 where "st2 = st\<lparr>processed_lrns := (
                                    \<lambda>x . if x = a
                                         then {ln} \<union> processed_lrns st x
                                         else processed_lrns st x)\<rparr>"
  have "processed_lrns st2 = (
          \<lambda>x . if x = a
               then {ln} \<union> processed_lrns st x
               else processed_lrns st x)" 
    by (simp add: st2_def)
  have "(msgs st2 = msgs st)
          \<and> (known_msgs_acc st2 = known_msgs_acc st)
          \<and> (known_msgs_lrn st2 = known_msgs_lrn st)
          \<and> (recent_msgs st2 = recent_msgs st)" 
    by (simp add: st2_def)
  have "(queued_msg st2 = queued_msg st)
          \<and> (two_a_lrn_loop st2 = two_a_lrn_loop st)
          \<and> (decision st2 = decision st)
          \<and> (BVal st2 = BVal st)" 
    by (simp add: st2_def)
  show ?thesis
    unfolding Process1bLearnerLoopStep.simps
    using assms by force
qed

lemma Process1bLearnerLoopStep_Enabled:
  "Enabled (Process1bLearnerLoopStep a l) st = True"
  by (meson Enabled.elims(3) Process1bLearnerLoopStepAlt1 Process1bLearnerLoopStepAlt2)

lemma Process1bLearnerLoopDone_Enabled:
  "Enabled (Process1bLearnerLoopDone a) st = (\<forall>ln :: Learner. ln \<in> processed_lrns st a)"
  by auto

(* Process1bLearnerLoop is always enabled.*)
lemma Process1bLearnerLoop_Enabled:
  "Enabled (Process1bLearnerLoop a) st = True"
  by (metis Enabled.elims(1) Process1bLearnerLoop.elims(3) Process1bLearnerLoopDone_Enabled Process1bLearnerLoopStep_Enabled)

lemma AcceptorAction_Enabled:
  shows "Enabled (AcceptorAction a) st = (
    is_safe a \<and> (
      (\<not> two_a_lrn_loop st a \<and>
       ((queued_msg st a \<noteq> None \<and> 
         type (the (queued_msg st a)) = T1b \<and> 
         Recv_acc st a (the (queued_msg st a))) \<or> 
        (queued_msg st a = None \<and> (
          \<exists>m \<in> set (msgs st). Recv_acc st a m \<and> (type m = T1a \<or> type m = T1b)
        ))))
      \<or> two_a_lrn_loop st a)
  )"
  by (metis AcceptorAction.simps Enabled.elims(1) Process1a_Enabled Process1bLearnerLoop_Enabled Process1b_Enabled)

lemma AcceptorAction_NotEnabled:
  assumes "is_safe a"
  shows "\<not> Enabled (AcceptorAction a) st = (
     (queued_msg st a = None \<or> 
        type (the (queued_msg st a)) \<noteq> T1b \<or> 
        \<not> Recv_acc st a (the (queued_msg st a))) \<and> 
     (queued_msg st a \<noteq> None \<or> (
         \<forall>m \<in> set (msgs st). \<not> Recv_acc st a m \<or> (type m \<noteq> T1a \<and> type m \<noteq> T1b)
     ))
     \<and> \<not> two_a_lrn_loop st a
  )"
  by (metis AcceptorAction_Enabled assms)


lemma AcceptorAction_NotEnabled_Spec:
  assumes "Spec f"
      and "is_safe a"
  shows "\<not> Enabled (AcceptorAction a) (f i) = (
     (queued_msg (f i) a = None)
     \<and> \<not> (\<exists>m \<in> set (msgs (f i)). Recv_acc (f i) a m \<and> (type m = T1a \<or> type m = T1b))
     \<and> \<not> two_a_lrn_loop (f i) a
  )"
  by (metis AcceptorAction_NotEnabled QueuedMsgResult QueuedMsgSpec1.elims(2) QueuedMsgSpec2.elims(2) QueuedMsgSpec2_Conserved assms(1) assms(2))

lemma LearnerRecv_Enabled:
  shows "Enabled (LearnerRecv l m) st = Recv_lrn st l m"
  using Enabled.simps LearnerRecv.simps by presburger

lemma LearnerDecide_Enabled:
  shows "Enabled (LearnerDecide l b v) st = ChosenIn st l b v"
  using Enabled.simps LearnerDecide.simps by presburger

lemma LearnerAction_Enabled:
  shows "Enabled (LearnerAction l) st = (
      (\<exists>m\<in>set (msgs st). Recv_lrn st l m) \<or> 
      (\<exists>b v. ChosenIn st l b v))"
  by (metis Enabled.simps LearnerAction.elims(2) LearnerAction.elims(3) LearnerDecide_Enabled LearnerRecv_Enabled)



(*Weak fairness*)
fun WF :: "(State \<Rightarrow> State \<Rightarrow> bool) \<Rightarrow> (nat \<Rightarrow> State) \<Rightarrow> bool" where
  "WF p f = (
    \<forall>i. (\<forall>j \<ge> i. Enabled p (f j)) \<longrightarrow> (\<exists>j \<ge> i. p (f j) (f (1 + j)))
  )"

lemma Tran_Tran:
  shows "\<forall>x \<in> Tran m. Tran x \<subseteq> Tran m"
proof (induction m)
  case (M1a x)
  then show ?case
    by simp
next
  case (M1b x1a x2)
  then have "\<And>x1a x2. (\<And>x2a. x2a \<in> set x2 \<Longrightarrow>
                   \<forall>x\<in>Tran x2a.  Tran x \<subseteq> Tran x2a) \<Longrightarrow>
       \<forall>x\<in>{M1b x1a x2} \<union> \<Union> (set (map Tran x2)).
          Tran x \<subseteq> {M1b x1a x2} \<union> \<Union> (set (map Tran x2))"
    by (smt (verit, ccfv_SIG) Tran.simps(2) Union_iff imageE image_set insertE insert_is_Un insert_subset mk_disjoint_insert subsetI)
  then have "\<forall>x\<in>{M1b x1a x2} \<union> \<Union> (set (map Tran x2)).
               Tran x \<subseteq> {M1b x1a x2} \<union> \<Union> (set (map Tran x2))"
    using M1b by blast
  then show ?case
    by (metis Tran.simps(2) list.set_map)
next
  case (M2a x1a x2 x3)
  then have "\<And>x1a x2 x3.
       (\<And>x3a. x3a \<in> set x3 \<Longrightarrow> \<forall>x\<in>Tran x3a. Tran x \<subseteq> Tran x3a) \<Longrightarrow>
       \<forall>x\<in>{M2a x1a x2 x3} \<union> \<Union> (set (map Tran x3)).
          Tran x \<subseteq> {M2a x1a x2 x3} \<union> \<Union> (set (map Tran x3))"
    by (smt (verit, ccfv_SIG) Tran.simps(3) Union_iff imageE image_set insertE insert_is_Un insert_subset mk_disjoint_insert subsetI)
  then have "\<forall>x\<in>{M2a x1a x2 x3} \<union> \<Union> (set (map Tran x3)).
               Tran x \<subseteq> {M2a x1a x2 x3} \<union> \<Union> (set (map Tran x3))"
    using M2a by blast
  then show ?case
    by (metis Tran.simps(3) list.set_map)
qed

fun FullyWellFormed :: "State \<Rightarrow> PreMessage \<Rightarrow> bool" where
  "FullyWellFormed st m = (\<forall>x \<in> Tran m. WellFormed st x)"

lemma FullyWellFormed_Trans:
  shows "FullyWellFormed st m \<longrightarrow> (\<forall>x \<in> Tran m. FullyWellFormed st x)"
proof (induction m)
  case (M1a x)
  then show ?case 
    by (metis Tran.simps(1) singletonD)
next
  case (M1b x1a x2)
  then show ?case 
    by (metis FullyWellFormed.elims(1) Tran_Tran subset_iff)
next
  case (M2a x1a x2 x3)
  then show ?case
    by (metis FullyWellFormed.elims(1) Tran_Tran subset_iff)
qed


fun PresentlyWellFormed :: "State \<Rightarrow> PreMessage \<Rightarrow> bool" where
  "PresentlyWellFormed st m = (\<forall>x \<in> Tran m. x \<in> set (msgs st) \<and> WellFormed st x)"

lemma PresentlyWellFormed_Trans:
  shows "PresentlyWellFormed st m \<longrightarrow> (\<forall>x \<in> Tran m. PresentlyWellFormed st x)"
  by (induction m; metis PresentlyWellFormed.elims(1) Tran_Tran subset_iff)

lemma PresentlyWellFormed_Constant:
  assumes "Spec f"
      and "i \<le> j"
    shows "PresentlyWellFormed (f i) m \<longrightarrow> PresentlyWellFormed (f j) m"
  by (induction m; meson PresentlyWellFormed.simps Wellformed_Conservation assms(1) assms(2) msgs_preserved)

lemma Learner_Eventually_Gets_All_PresentlyWellFormed_Messages:
  assumes "Spec f"
      and "\<forall>m\<in>set (msgs (f i)). \<not> Enabled (LearnerRecv L m) (f i)"
    shows "PresentlyWellFormed (f i) m \<longrightarrow> m \<in> set (known_msgs_lrn (f i) L)"
proof (induction m; clarify)
  case (M1a x)
  assume "PresentlyWellFormed (f i) (M1a x)"
  then show "M1a x \<in> set (known_msgs_lrn (f i) L)" 
    by (metis LearnerRecv_Enabled M1a_Good PresentlyWellFormed.elims(2) Recv_lrn.elims(3) Tran.simps(1) assms(2) singletonI type.simps(1))
next
  case (M1b x1a x2)
  assume h: "(\<And>x2a. x2a \<in> set x2 \<Longrightarrow>
               PresentlyWellFormed (f i) x2a \<longrightarrow>
               x2a \<in> set (known_msgs_lrn (f i) L))"
      and "PresentlyWellFormed (f i) (M1b x1a x2)"
  have "M1b x1a x2 \<in> set (msgs (f i))"
    by (metis PresentlyWellFormed.elims(2) Tran.simps(2) Un_iff \<open>PresentlyWellFormed (f i) (M1b x1a x2)\<close> singletonI)
  have "WellFormed (f i) (M1b x1a x2)"
    by (metis PresentlyWellFormed.elims(2) Tran.simps(2) Un_iff \<open>PresentlyWellFormed (f i) (M1b x1a x2)\<close> singletonI)
  then have "\<forall>y\<in>Tran (M1b x1a x2). M1b x1a x2 \<noteq> y \<and> SameBallot (M1b x1a x2) y \<longrightarrow> type y = T1a"
    by (meson WellFormed.elims(2) type.simps(2))
  have "\<not> Enabled (LearnerRecv L (M1b x1a x2)) (f i)"
    using \<open>M1b x1a x2 \<in> set (msgs (f i))\<close> assms(2) by blast
  then have "\<not> Recv_lrn (f i) L (M1b x1a x2)"
    using LearnerRecv_Enabled by blast
  have "\<forall>r\<in>set x2. r \<in> set (msgs (f i))"
    by (metis Message_ref_Tran PresentlyWellFormed.elims(1) \<open>PresentlyWellFormed (f i) (M1b x1a x2)\<close> ref.simps(2))
  have "Proper_lrn (f i) L (M1b x1a x2)"
    using Message_ref_Tran PresentlyWellFormed_Trans Proper_lrn.simps \<open>PresentlyWellFormed (f i) (M1b x1a x2)\<close> h ref.simps(2) by blast
  show "M1b x1a x2 \<in> set (known_msgs_lrn (f i) L)"
    using Recv_lrn.simps \<open>Proper_lrn (f i) L (M1b x1a x2)\<close> \<open>WellFormed (f i) (M1b x1a x2)\<close> \<open>\<not> Recv_lrn (f i) L (M1b x1a x2)\<close> by presburger
next
  case (M2a x1a x2 x3)
  assume "(\<And>x3a. x3a \<in> set x3 \<Longrightarrow>
               PresentlyWellFormed (f i) x3a \<longrightarrow>
               x3a \<in> set (known_msgs_lrn (f i) L))"
      and "PresentlyWellFormed (f i) (M2a x1a x2 x3)"
  have "WellFormed (f i) (M2a x1a x2 x3)"
    by (metis PresentlyWellFormed.elims(1) Tran.simps(3) Un_iff \<open>PresentlyWellFormed (f i) (M2a x1a x2 x3)\<close> singletonI)
  have "Proper_lrn (f i) L (M2a x1a x2 x3)"
    using M2a Message_ref_Tran PresentlyWellFormed_Trans Proper_lrn.simps \<open>PresentlyWellFormed (f i) (M2a x1a x2 x3)\<close> ref.simps(3) by blast
  show "M2a x1a x2 x3 \<in> set (known_msgs_lrn (f i) L)" 
    by (metis LearnerRecv_Enabled PresentlyWellFormed.elims(1) Recv_lrn.elims(3) Tran.simps(3) Un_iff \<open>PresentlyWellFormed (f i) (M2a x1a x2 x3)\<close> \<open>Proper_lrn (f i) L (M2a x1a x2 x3)\<close> assms(2) singletonI)
qed







end