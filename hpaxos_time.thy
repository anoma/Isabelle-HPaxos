theory hpaxos_time
imports Main hpaxos hpaxos_safety hpaxos_aux
begin


lemma Process1a_Enables_Action:
  assumes "Enabled (Process1a a x) st"
      and "is_safe a"
      and "\<not> two_a_lrn_loop st a"
      and "queued_msg st a = None"
      and "x \<in> set (msgs st)"
    shows "Enabled (AcceptorAction a) st"
  using AcceptorAction_NotEnabled Process1a_Enabled assms(1) assms(2) assms(4) assms(5) by blast

lemma no_acceptor_no_Process1a:
  assumes "\<not> Enabled (AcceptorAction a) st"
      and "is_safe a"
      and "queued_msg st a = None"
      and "x \<in> set (msgs st)"
    shows "\<not> Enabled (Process1a a x) st"
  using AcceptorAction_NotEnabled Process1a_Enables_Action assms(1) assms(2) assms(3) assms(4) by blast

lemma Process1a_Req_known_msgs:
  assumes "Spec f"
      and "Process1a a x (f (i - 1)) (f i)"
    shows "x \<in> set (known_msgs_acc (f i) a)"
  by (metis Process1a.elims(2) Store_acc.elims(2) assms(2) in_set_member member_rec(1))



lemma ProposerSendAction_Preserves_AcceptorAction:
  assumes "ProposerSendAction st st2"
      and "Enabled (AcceptorAction a) st"
    shows "Enabled (AcceptorAction a) st2"
proof -
  have "ProposerSendAction st st2"
    using assms(1) by blast
  then show ?thesis
    unfolding ProposerSendAction.simps
  proof (elim exE)
    fix blt
    assume "Send1a blt st st2"
    have "is_safe a"
      using AcceptorAction_Enabled assms(2) by presburger
    show ?thesis
    proof (cases "two_a_lrn_loop st a")
      case True
      have "two_a_lrn_loop st2 a"
        using True \<open>Send1a blt st st2\<close> by fastforce
      show ?thesis
        using AcceptorAction_Enabled \<open>is_safe a\<close> \<open>two_a_lrn_loop st2 a\<close> by blast
    next
      case False
      have "\<not> two_a_lrn_loop st2 a"
        using False \<open>Send1a blt st st2\<close> by fastforce
      then show ?thesis
      proof (cases "queued_msg st a = None")
        case True
        have "\<exists>m \<in> set (msgs st). Recv_acc st a m \<and> (type m = T1a \<or> type m = T1b)"
          using AcceptorAction_NotEnabled False True \<open>is_safe a\<close> assms(2) by blast
        then show ?thesis
        proof (clarify)
          fix m
          assume "m \<in> set (msgs st)"
             and "Recv_acc st a m"
             and "type m = T1a \<or> type m = T1b"
          have "m \<in> set (msgs st2)"
            by (meson Next.elims(3) \<open>m \<in> set (msgs st)\<close> assms(1) next_msgs_preserved)
          have "Recv_acc st2 a m"
            by (smt (verit) Proper_acc.simps Recv_acc.elims(1) Send1a.simps WellFormed_monotone \<open>Recv_acc st a m\<close> \<open>Send1a blt st st2\<close> select_convs(2) select_convs(9) surjective update_convs(1))
          have q0: "\<exists>m \<in> set (msgs st2). Recv_acc st2 a m \<and> (type m = T1a \<or> type m = T1b)"
            using \<open>Recv_acc st2 a m\<close> \<open>m \<in> set (msgs st2)\<close> \<open>type m = T1a \<or> type m = T1b\<close> by blast
          have q1: "(queued_msg st a = None \<and> (
                      \<exists>m \<in> set (msgs st). Recv_acc st a m \<and> (type m = T1a \<or> type m = T1b)
                    ))"
            using True \<open>Recv_acc st a m\<close> \<open>m \<in> set (msgs st)\<close> \<open>type m = T1a \<or> type m = T1b\<close> by blast
          show ?thesis
            by (metis AcceptorAction_NotEnabled Send1a.elims(2) True \<open>Send1a blt st st2\<close> \<open>is_safe a\<close> ext_inject q0 surjective update_convs(1))
        qed
      next
        case False
        have "type (the (queued_msg st2 a)) = T1b \<and>
               Recv_acc st2 a (the (queued_msg st2 a))"
          by (smt (verit, ccfv_SIG) AcceptorAction_NotEnabled False Proper_acc.elims(1) Recv_acc.elims(1) Send1a.elims(2) WellFormed_monotone \<open>Send1a blt st st2\<close> \<open>\<not> two_a_lrn_loop st2 a\<close> \<open>is_safe a\<close> assms(2) ext_inject surjective update_convs(1))
        show ?thesis
          by (metis AcceptorAction_NotEnabled False Send1a.elims(1) \<open>Send1a blt st st2\<close> \<open>is_safe a\<close> \<open>type (the (queued_msg st2 a)) = T1b \<and> Recv_acc st2 a (the (queued_msg st2 a))\<close> select_convs(5) surjective update_convs(1))
      qed
    qed
  qed
qed

lemma FakeAcceptorAction_Preserves_AcceptorAction:
  assumes "FakeAcceptorAction st st2"
      and "Enabled (AcceptorAction a) st"
    shows "Enabled (AcceptorAction a) st2"
proof -
  have "FakeAcceptorAction st st2"
    using assms(1) by blast
  then show ?thesis
    unfolding FakeAcceptorAction.simps
  proof (clarify)
    fix a2
    have "is_safe a"
      using AcceptorAction_Enabled assms(2) by presburger
    assume "\<not> is_safe a2"
    assume "FakeSend1b a2 st st2 \<or> FakeSend2a a2 st st2"
    have "two_a_lrn_loop st2 a = two_a_lrn_loop st a"
      by (metis FakeSend1b.elims(1) FakeSend2a.elims(2) \<open>FakeSend1b a2 st st2 \<or> FakeSend2a a2 st st2\<close> select_convs(6) surjective update_convs(1))
    have "known_msgs_acc st2 a = known_msgs_acc st a"
      by (metis FakeSend1b.simps FakeSend2a.simps \<open>FakeSend1b a2 st st2 \<or> FakeSend2a a2 st st2\<close> select_convs(2) surjective update_convs(1))
    have "recent_msgs st2 a = recent_msgs st a"
      by (metis FakeSend1b.elims(1) FakeSend2a.elims(2) \<open>FakeSend1b a2 st st2 \<or> FakeSend2a a2 st st2\<close> select_convs(4) surjective update_convs(1))
    have "queued_msg st2 a = queued_msg st a"
      by (metis FakeSend1b.elims(1) FakeSend2a.simps \<open>FakeSend1b a2 st st2 \<or> FakeSend2a a2 st st2\<close> ext_inject surjective update_convs(1))
    show ?thesis
    proof (cases "two_a_lrn_loop st a")
      case True
      show ?thesis
        using AcceptorAction_NotEnabled True \<open>is_safe a\<close> \<open>two_a_lrn_loop st2 a = two_a_lrn_loop st a\<close> by blast
    next
      case False
      show ?thesis
      proof (cases "queued_msg st a = None")
        case True
        have "\<exists>m \<in> set (msgs st). Recv_acc st a m \<and> (type m = T1a \<or> type m = T1b)"
          using AcceptorAction_NotEnabled False True \<open>is_safe a\<close> assms(2) by blast
        then show ?thesis
        proof (clarify)
          fix m
          assume "m \<in> set (msgs st)"
             and "Recv_acc st a m"
             and "type m = T1a \<or> type m = T1b"
          have "m \<in> set (msgs st2)"
            by (meson Next.elims(3) \<open>m \<in> set (msgs st)\<close> assms(1) next_msgs_preserved)
          have "Recv_acc st2 a m"
            by (metis MessageType.distinct(3) MessageType.distinct(5) Proper_acc.elims(1) Recv_acc.elims(2) Recv_acc.elims(3) WellFormed.elims(1) \<open>Recv_acc st a m\<close> \<open>known_msgs_acc st2 a = known_msgs_acc st a\<close> \<open>type m = T1a \<or> type m = T1b\<close>)
          have q: "\<exists>m \<in> set (msgs st2). Recv_acc st2 a m \<and> (type m = T1a \<or> type m = T1b)"
            using \<open>Recv_acc st2 a m\<close> \<open>m \<in> set (msgs st2)\<close> \<open>type m = T1a \<or> type m = T1b\<close> by blast
          show ?thesis
            by (metis AcceptorAction_NotEnabled True \<open>is_safe a\<close> \<open>queued_msg st2 a = queued_msg st a\<close> q)
        qed
      next
        have TwoFalse: "\<not> two_a_lrn_loop st a"
          by (simp add: False)
        case False
        have "type (the (queued_msg st2 a)) = T1b \<and>
               Recv_acc st2 a (the (queued_msg st2 a))"
          by (smt (verit) AcceptorAction_NotEnabled False MessageType.distinct(5) Proper_acc.elims(1) Recv_acc.elims(2) Recv_acc.elims(3) TwoFalse WellFormed.elims(1) \<open>is_safe a\<close> \<open>known_msgs_acc st2 a = known_msgs_acc st a\<close> \<open>queued_msg st2 a = queued_msg st a\<close> assms(2))
        show ?thesis
          using AcceptorAction_NotEnabled False \<open>is_safe a\<close> \<open>queued_msg st2 a = queued_msg st a\<close> \<open>type (the (queued_msg st2 a)) = T1b \<and> Recv_acc st2 a (the (queued_msg st2 a))\<close> by presburger
      qed
    qed
  qed
qed

lemma LearnerAction_Preserves_AcceptorAction:
  assumes "LearnerProcessAction st st2"
      and "Enabled (AcceptorAction a) st"
    shows "Enabled (AcceptorAction a) st2"
proof -
  have "LearnerProcessAction st st2"
    using assms(1) by blast
  then show ?thesis
    unfolding LearnerProcessAction.simps LearnerAction.simps
  proof (clarify)
    fix ln
    have "is_safe a"
      using AcceptorAction_Enabled assms(2) by presburger
    assume "(\<exists>m\<in>set (msgs st). LearnerRecv ln m st st2) \<or>
            (\<exists>blt val. LearnerDecide ln blt val st st2)"
    have "two_a_lrn_loop st2 a = two_a_lrn_loop st a"
      by (metis (no_types, lifting) LearnerDecide.elims(1) LearnerRecv.elims(1) \<open>(\<exists>m\<in>set (msgs st). LearnerRecv ln m st st2) \<or> (\<exists>blt val. LearnerDecide ln blt val st st2)\<close> select_convs(6) surjective update_convs(3) update_convs(8))
    have "known_msgs_acc st2 a = known_msgs_acc st a"
      by (metis (no_types, lifting) LearnerDecide.elims(2) LearnerRecv.elims(2) \<open>(\<exists>m\<in>set (msgs st). LearnerRecv ln m st st2) \<or> (\<exists>blt val. LearnerDecide ln blt val st st2)\<close> select_convs(2) surjective update_convs(3) update_convs(8))
    have "recent_msgs st2 a = recent_msgs st a"
      by (metis (no_types, lifting) LearnerDecide.elims(1) LearnerRecv.elims(1) \<open>(\<exists>m\<in>set (msgs st). LearnerRecv ln m st st2) \<or> (\<exists>blt val. LearnerDecide ln blt val st st2)\<close> select_convs(4) surjective update_convs(3) update_convs(8))
    have "queued_msg st2 a = queued_msg st a"
      by (metis (no_types, lifting) LearnerDecide.elims(2) LearnerRecv.elims(2) \<open>(\<exists>m\<in>set (msgs st). LearnerRecv ln m st st2) \<or> (\<exists>blt val. LearnerDecide ln blt val st st2)\<close> ext_inject surjective update_convs(3) update_convs(8))
    show ?thesis
    proof (cases "two_a_lrn_loop st a")
      case True
      show ?thesis
        using AcceptorAction_NotEnabled True \<open>is_safe a\<close> \<open>two_a_lrn_loop st2 a = two_a_lrn_loop st a\<close> by blast
    next
      case False
      show ?thesis
      proof (cases "queued_msg st a = None")
        case True
        have "\<exists>m \<in> set (msgs st). Recv_acc st a m \<and> (type m = T1a \<or> type m = T1b)"
          using AcceptorAction_NotEnabled False True \<open>is_safe a\<close> assms(2) by blast
        then show ?thesis
        proof (clarify)
          fix m
          assume "m \<in> set (msgs st)"
             and "Recv_acc st a m"
             and "type m = T1a \<or> type m = T1b"
          have "m \<in> set (msgs st2)"
            by (meson Next.elims(3) \<open>m \<in> set (msgs st)\<close> assms(1) next_msgs_preserved)
          have "Recv_acc st2 a m"
            by (metis MessageType.distinct(3) MessageType.distinct(5) Proper_acc.elims(1) Recv_acc.elims(2) Recv_acc.elims(3) WellFormed.elims(1) \<open>Recv_acc st a m\<close> \<open>known_msgs_acc st2 a = known_msgs_acc st a\<close> \<open>type m = T1a \<or> type m = T1b\<close>)
          have q: "\<exists>m \<in> set (msgs st2). Recv_acc st2 a m \<and> (type m = T1a \<or> type m = T1b)"
            using \<open>Recv_acc st2 a m\<close> \<open>m \<in> set (msgs st2)\<close> \<open>type m = T1a \<or> type m = T1b\<close> by blast
          show ?thesis
            by (metis AcceptorAction_NotEnabled True \<open>is_safe a\<close> \<open>queued_msg st2 a = queued_msg st a\<close> q)
        qed
      next
        have TwoFalse: "\<not> two_a_lrn_loop st a"
          by (simp add: False)
        case False
        have "type (the (queued_msg st2 a)) = T1b \<and>
               Recv_acc st2 a (the (queued_msg st2 a))"
          by (smt (verit) AcceptorAction_NotEnabled False MessageType.distinct(5) Proper_acc.elims(1) Recv_acc.elims(2) Recv_acc.elims(3) TwoFalse WellFormed.elims(1) \<open>is_safe a\<close> \<open>known_msgs_acc st2 a = known_msgs_acc st a\<close> \<open>queued_msg st2 a = queued_msg st a\<close> assms(2))
        show ?thesis
          using AcceptorAction_NotEnabled False \<open>is_safe a\<close> \<open>queued_msg st2 a = queued_msg st a\<close> \<open>type (the (queued_msg st2 a)) = T1b \<and> Recv_acc st2 a (the (queued_msg st2 a))\<close> by presburger
      qed
    qed
  qed
qed

lemma Other_Process1a_Preserves_AcceptorAction:
  assumes "Process1a A m st st2"
      and "A \<noteq> a"
      and "Enabled (AcceptorAction a) st"
    shows "Enabled (AcceptorAction a) st2"
proof -
  have "recent_msgs st a = recent_msgs st2 a"
    by (metis Process1a.elims(2) assms(1) assms(2))
  have "queued_msg st a = queued_msg st2 a"
    by (metis Process1a.elims(2) assms(1) assms(2))
  have "two_a_lrn_loop st a = two_a_lrn_loop st2 a"
    by (metis Process1a.elims(2) assms(1))
  have "\<forall>m. Recv_acc st a m = Recv_acc st2 a m"
    by (smt (verit, best) Process1a.elims(2) Proper_acc.elims(1) Recv_acc.simps Store_acc.elims(2) WellFormed_monotone assms(1) assms(2))
  then show ?thesis
  proof (cases "two_a_lrn_loop st a")
    case True
    then show ?thesis
      using AcceptorAction_Enabled \<open>two_a_lrn_loop st a = two_a_lrn_loop st2 a\<close> assms(3) by presburger
  next
    case False
    then show ?thesis
    proof (cases "queued_msg st2 a = None")
      case True
      have "\<exists>m \<in> set (msgs st2). Recv_acc st2 a m \<and> (type m = T1a \<or> type m = T1b)"
        by (metis (full_types) AcceptorAction_Enabled False Process1a.elims(2) Send.elims(2) True \<open>\<forall>m. Recv_acc st a m = Recv_acc st2 a m\<close> \<open>queued_msg st a = queued_msg st2 a\<close> assms(1) assms(3) list.set_intros(2))
      show ?thesis
        using AcceptorAction_Enabled True \<open>\<exists>m\<in>set (msgs st2). Recv_acc st2 a m \<and> (type m = T1a \<or> type m = T1b)\<close> assms(3) by presburger
    next
      case False
      have "queued_msg st a \<noteq> None"
        by (simp add: False \<open>queued_msg st a = queued_msg st2 a\<close>)
      then show ?thesis 
        by (metis AcceptorAction_Enabled \<open>\<forall>m. Recv_acc st a m = Recv_acc st2 a m\<close> \<open>queued_msg st a = queued_msg st2 a\<close> \<open>two_a_lrn_loop st a = two_a_lrn_loop st2 a\<close> assms(3))
    qed
  qed
qed

lemma Other_Process1b_Preserves_AcceptorAction:
  assumes "Process1b A m st st2"
      and "A \<noteq> a"
      and "Enabled (AcceptorAction a) st"
    shows "Enabled (AcceptorAction a) st2"
proof -
  have "recent_msgs st a = recent_msgs st2 a"
    using assms(1) assms(2) by fastforce
  have "queued_msg st a = queued_msg st2 a"
    using Process1b.simps assms(1) assms(2) by presburger
  have "two_a_lrn_loop st a = two_a_lrn_loop st2 a"
    by (smt (verit, ccfv_SIG) Process1b.simps assms(1) assms(2))
  have "\<forall>m. Recv_acc st a m = Recv_acc st2 a m"
    using assms(1) assms(2) by force
  then show ?thesis
  proof (cases "two_a_lrn_loop st a")
    case True
    then show ?thesis
      using AcceptorAction_Enabled \<open>two_a_lrn_loop st a = two_a_lrn_loop st2 a\<close> assms(3) by presburger
  next
    case False
    then show ?thesis
    proof (cases "queued_msg st2 a = None")
      case True
      have "\<exists>m \<in> set (msgs st2). Recv_acc st2 a m \<and> (type m = T1a \<or> type m = T1b)"
        using AcceptorAction_Enabled False Process1b.simps True \<open>\<forall>m. Recv_acc st a m = Recv_acc st2 a m\<close> \<open>queued_msg st a = queued_msg st2 a\<close> assms(1) assms(3) by presburger
      show ?thesis
        using AcceptorAction_Enabled True \<open>\<exists>m\<in>set (msgs st2). Recv_acc st2 a m \<and> (type m = T1a \<or> type m = T1b)\<close> assms(3) by presburger
    next
      case False
      have "queued_msg st a \<noteq> None"
        by (simp add: False \<open>queued_msg st a = queued_msg st2 a\<close>)
      then show ?thesis 
        by (metis AcceptorAction_Enabled \<open>\<forall>m. Recv_acc st a m = Recv_acc st2 a m\<close> \<open>queued_msg st a = queued_msg st2 a\<close> \<open>two_a_lrn_loop st a = two_a_lrn_loop st2 a\<close> assms(3))
    qed
  qed
qed

lemma Other_Process1bLearnerLoopStep_Preserves_AcceptorAction:
  assumes "Process1bLearnerLoopStep A m st st2"
      and "A \<noteq> a"
      and "Enabled (AcceptorAction a) st"
    shows "Enabled (AcceptorAction a) st2"
proof -
  have "recent_msgs st a = recent_msgs st2 a"
    by (metis Process1bLearnerLoopStep.elims(2) assms(1) assms(2))
  have "queued_msg st a = queued_msg st2 a"
    by (metis Process1bLearnerLoopStep.simps assms(1))
  have "two_a_lrn_loop st a = two_a_lrn_loop st2 a"
    by (metis Process1bLearnerLoopStep.elims(2) assms(1))
  have "\<forall>m. Recv_acc st a m = Recv_acc st2 a m"
    by (smt (verit, ccfv_threshold) Process1bLearnerLoopStep.elims(2) Proper_acc.elims(1) Recv_acc.simps Store_acc.elims(2) WellFormed_monotone assms(1) assms(2))
  then show ?thesis
  proof (cases "two_a_lrn_loop st a")
    case True
    then show ?thesis
      using AcceptorAction_Enabled \<open>two_a_lrn_loop st a = two_a_lrn_loop st2 a\<close> assms(3) by presburger
  next
    case False
    then show ?thesis
    proof (cases "queued_msg st2 a = None")
      case True
      have "\<exists>m \<in> set (msgs st2). Recv_acc st2 a m \<and> (type m = T1a \<or> type m = T1b)"
        by (metis (full_types) AcceptorAction_Enabled False Process1bLearnerLoopStep.elims(2) Send.elims(2) True \<open>\<forall>m. Recv_acc st a m = Recv_acc st2 a m\<close> assms(1) assms(3) list.set_intros(2))
      show ?thesis
        using AcceptorAction_Enabled True \<open>\<exists>m\<in>set (msgs st2). Recv_acc st2 a m \<and> (type m = T1a \<or> type m = T1b)\<close> assms(3) by presburger
    next
      case False
      have "queued_msg st a \<noteq> None"
        by (simp add: False \<open>queued_msg st a = queued_msg st2 a\<close>)
      then show ?thesis 
        by (metis AcceptorAction_Enabled \<open>\<forall>m. Recv_acc st a m = Recv_acc st2 a m\<close> \<open>queued_msg st a = queued_msg st2 a\<close> \<open>two_a_lrn_loop st a = two_a_lrn_loop st2 a\<close> assms(3))
    qed
  qed
qed

lemma Other_Process1bLearnerLoopDone_Preserves_AcceptorAction:
  assumes "Process1bLearnerLoopDone A st st2"
      and "A \<noteq> a"
      and "Enabled (AcceptorAction a) st"
    shows "Enabled (AcceptorAction a) st2"
proof -
  have "recent_msgs st a = recent_msgs st2 a"
    using assms(1) by auto
  have "queued_msg st a = queued_msg st2 a"
    using assms(1) by auto
  have "two_a_lrn_loop st a = two_a_lrn_loop st2 a"
    using assms(1) assms(2) by auto
  have "\<forall>m. Recv_acc st a m = Recv_acc st2 a m"
    using assms(1) by auto
  then show ?thesis
  proof (cases "two_a_lrn_loop st a")
    case True
    then show ?thesis
      using AcceptorAction_Enabled \<open>two_a_lrn_loop st a = two_a_lrn_loop st2 a\<close> assms(3) by presburger
  next
    case False
    then show ?thesis
    proof (cases "queued_msg st2 a = None")
      case True
      have "\<exists>m \<in> set (msgs st). Recv_acc st2 a m \<and> (type m = T1a \<or> type m = T1b)"
        using AcceptorAction_Enabled False True \<open>\<forall>m. Recv_acc st a m = Recv_acc st2 a m\<close> \<open>queued_msg st a = queued_msg st2 a\<close> assms(3) by presburger
      then have "\<exists>m \<in> set (msgs st2). Recv_acc st2 a m \<and> (type m = T1a \<or> type m = T1b)"
        using assms(1) ext_inject surjective update_convs(6) by auto
      show ?thesis
        using AcceptorAction_Enabled True \<open>\<exists>m\<in>set (msgs st2). Recv_acc st2 a m \<and> (type m = T1a \<or> type m = T1b)\<close> assms(3) by presburger
    next
      case False
      have "queued_msg st a \<noteq> None"
        by (simp add: False \<open>queued_msg st a = queued_msg st2 a\<close>)
      then show ?thesis 
        by (metis AcceptorAction_Enabled \<open>\<forall>m. Recv_acc st a m = Recv_acc st2 a m\<close> \<open>queued_msg st a = queued_msg st2 a\<close> \<open>two_a_lrn_loop st a = two_a_lrn_loop st2 a\<close> assms(3))
    qed
  qed
qed


lemma only_AcceptorAction_disables_AcceptorAction:
  assumes "Next st st2"
      and "Enabled (AcceptorAction a) st"
      and "\<not> Enabled (AcceptorAction a) st2"
    shows "AcceptorAction a st st2"
proof -
  have "AcceptorProcessAction st st2"
    using FakeAcceptorAction_Preserves_AcceptorAction LearnerAction_Preserves_AcceptorAction Next.simps ProposerSendAction_Preserves_AcceptorAction assms(1) assms(2) assms(3) by blast
  then show ?thesis
    unfolding AcceptorProcessAction.simps
  proof (clarify)
    fix A
    assume "AcceptorAction A st st2"
    have "a = A"
      by (metis (full_types) AcceptorAction.elims(2) Other_Process1a_Preserves_AcceptorAction Other_Process1bLearnerLoopDone_Preserves_AcceptorAction Other_Process1bLearnerLoopStep_Preserves_AcceptorAction Other_Process1b_Preserves_AcceptorAction Process1bLearnerLoop.simps \<open>AcceptorAction A st st2\<close> assms(2) assms(3))
    then show ?thesis
      using \<open>AcceptorAction A st st2\<close> by blast 
  qed
qed



lemma Process1b_Not_Process1bLearnerLoopStep:
  assumes "Process1b a ln st st2"
  shows "\<not> Process1bLearnerLoopStep a2 ln2 st st2"
  by (smt (z3) Process1b.elims(1) Process1bLearnerLoopStep.elims(1) Send.elims(1) assms not_Cons_self)

lemma Process1b_Not_Process1a:
  assumes "Process1b a ln st st2"
  shows "\<not> Process1a a2 ln2 st st2"
  by (smt (z3) MessageType.simps(2) Process1a.simps Process1b.elims(1) assms list.distinct(1) list.inject not_Cons_self)

lemma Process1a_Not_Process1bLearnerLoopDone:
  assumes "Process1a a ln st st2"
  shows "\<not> Process1bLearnerLoopDone a2 st st2"
  by (smt (verit, best) Process1a.elims(2) Process1bLearnerLoopDone.elims(1) Send.elims(1) assms ext_inject not_Cons_self2 surjective update_convs(6))

lemma Process1b_Not_Process1bLearnerLoopDone:
  assumes "Process1b a ln st st2"
  shows "\<not> Process1bLearnerLoopDone a2 st st2"
  by (metis (mono_tags, lifting) Process1b.elims(2) Process1bLearnerLoopDone.elims(2) Store_acc.simps assms not_Cons_self select_convs(2) surjective update_convs(6))


lemma Process1a_Not_ProposerSendAction :
  assumes "Process1a a m st st2"
    shows "\<not> ProposerSendAction st st2"
  by (metis (no_types, lifting) Process1a.elims(2) ProposerSendAction.elims(2) Send1a.elims(2) Store_acc.elims(2) assms not_Cons_self2 select_convs(2) surjective update_convs(1))

lemma Process1a_Not_LearnerProcessAction :
  assumes "Process1a a m st st2"
    shows "\<not> LearnerProcessAction st st2"
  by (smt (verit) LearnerProcessAction.elims LearnerAction.elims(2) LearnerDecide.elims(2) LearnerRecv.elims(2) Process1a.elims(2) Send.elims(1) assms ext_inject not_Cons_self2 surjective update_convs(3) update_convs(8))

lemma Process1a_Not_FakeAcceptorAction :
  assumes "Process1a a m st st2"
    shows "\<not> FakeAcceptorAction st st2"
  by (metis FakeAcceptorAction.simps FakeSend1b.elims(1) FakeSend2a.simps Process1a.elims(2) Store_acc.elims(2) assms not_Cons_self2 select_convs(2) surjective update_convs(1))

lemma Process1a_Next_Implies_AcceptorAction:
  assumes "Next st st2"
      and "Process1a a m st st2"
    shows "AcceptorAction a st st2"
proof -
  have "AcceptorProcessAction st st2"
    using Next.simps Process1a_Not_FakeAcceptorAction Process1a_Not_LearnerProcessAction Process1a_Not_ProposerSendAction assms(1) assms(2) by blast
  then show ?thesis
    unfolding AcceptorProcessAction.simps
  proof (elim exE)
    fix a2
    assume "AcceptorAction a2 st st2"
    have "\<exists>m \<in> set (msgs st). Process1a a2 m st st2 \<or> Process1b a2 m st st2"
      by (metis AcceptorAction.simps Process1a_Not_Process1bLearnerLoopDone Process1a_Not_Process1bLearnerLoopStep Process1bLearnerLoop.elims(1) Process1b_Not_Process1a \<open>AcceptorAction a2 st st2\<close> assms(2))
    have "Process1a a2 m st st2"
      by (metis Process1a.elims(2) Process1b_Not_Process1a Store_acc.elims(2) \<open>\<exists>m\<in>set (msgs st). Process1a a2 m st st2 \<or> Process1b a2 m st st2\<close> assms(2) not_Cons_self2)
    have "a = a2"
      by (metis Process1a.simps Store_acc.elims(2) \<open>Process1a a2 m st st2\<close> assms(2) not_Cons_self)
    then show ?thesis
      using \<open>AcceptorAction a2 st st2\<close> by blast
  qed
qed





lemma Process1B_Not_ProposerSendAction :
  assumes "Process1b a m st st2"
    shows "\<not> ProposerSendAction st st2"
proof -
  have "recent_msgs st2 a \<noteq> recent_msgs st a"
    using assms by auto
  then show ?thesis
    by force
qed

lemma Process1b_Not_LearnerProcessAction :
  assumes "Process1b a m st st2"
    shows "\<not> LearnerProcessAction st st2"
proof -
  have "recent_msgs st2 a \<noteq> recent_msgs st a"
    using assms by auto
  then show ?thesis
    by force
qed

lemma Process1b_Not_FakeSend1b :
  assumes "Process1b a m st st2"
    shows "\<not> FakeSend1b a2 st st2"
  by (smt (z3) FakeSend1b.elims(1) Process1b.elims(1) assms not_Cons_self select_convs(4) surjective update_convs(1))

lemma Process1b_Not_FakeSend2a :
  assumes "Process1b a m st st2"
    shows "\<not> FakeSend2a a2 st st2"
proof -
  have "recent_msgs st2 a \<noteq> recent_msgs st a"
    using assms by auto
  then show ?thesis
    by (metis FakeSend2a.simps select_convs(4) surjective update_convs(1))
qed

lemma Process1b_Not_FakeAcceptorAction :
  assumes "Process1b a m st st2"
    shows "\<not> FakeAcceptorAction st st2"
  using FakeAcceptorAction.simps Process1b_Not_FakeSend1b Process1b_Not_FakeSend2a assms by presburger

lemma Process1b_Next_Implies_AcceptorAction:
  assumes "Next st st2"
      and "Process1b a m st st2"
    shows "AcceptorAction a st st2"
proof -
  have "AcceptorProcessAction st st2"
    using Next.simps Process1B_Not_ProposerSendAction Process1b_Not_FakeAcceptorAction Process1b_Not_LearnerProcessAction assms(1) assms(2) by blast
  then show ?thesis
    unfolding AcceptorProcessAction.simps
    proof (elim exE)
    fix a2
    assume "AcceptorAction a2 st st2"
    then show ?thesis
    proof (cases "queued_msg st a = None")
      case True
      then show ?thesis
        by (metis AcceptorAction.simps Process1b.elims(2) Process1bLearnerLoop.elims(2) Process1b_Not_Process1a Process1b_Not_Process1bLearnerLoopDone Process1b_Not_Process1bLearnerLoopStep \<open>AcceptorAction a2 st st2\<close> assms(2) not_Cons_self)
    next
      case False
      then show ?thesis
      proof -
        have f1: "\<And>aa. aa \<noteq> a \<or> queued_msg st2 aa = None"
          by (meson Process1b.elims(2) assms(2))
        have "\<forall>s a sa. \<exists>p. \<forall>sb aa sc ab sd se. (\<not> two_a_lrn_loop sb aa \<or> \<not> AcceptorAction aa sb sc \<or> Process1bLearnerLoop aa sb sc) \<and> (\<not> AcceptorAction ab sd se \<or> two_a_lrn_loop sd ab \<or> queued_msg sd ab = None \<or> Process1b ab (the (queued_msg sd ab)) sd se) \<and> (queued_msg s a \<noteq> None \<or> \<not> AcceptorAction a s sa \<or> two_a_lrn_loop s a \<or> Process1b a p s sa \<or> Process1a a p s sa)"
          using AcceptorAction.simps by blast
        then obtain pp :: "State \<Rightarrow> Acceptor \<Rightarrow> State \<Rightarrow> PreMessage" where
          f2: "\<And>s a sa aa sb sc sd ab se. (\<not> two_a_lrn_loop s a \<or> \<not> AcceptorAction a s sa \<or> Process1bLearnerLoop a s sa) \<and> (\<not> AcceptorAction aa sb sc \<or> two_a_lrn_loop sb aa \<or> queued_msg sb aa = None \<or> Process1b aa (the (queued_msg sb aa)) sb sc) \<and> (queued_msg sd ab \<noteq> None \<or> \<not> AcceptorAction ab sd se \<or> two_a_lrn_loop sd ab \<or> Process1b ab (pp sd ab se) sd se \<or> Process1a ab (pp sd ab se) sd se)"
          by metis
        then have "\<not> two_a_lrn_loop st a2"
          by (metis (no_types) Process1bLearnerLoop.simps Process1b_Not_Process1bLearnerLoopDone Process1b_Not_Process1bLearnerLoopStep \<open>AcceptorAction a2 st st2\<close> assms(2))
        then have "Process1a a2 (pp st a2 st2) st st2 \<or> a2 = a"
          using f2 f1 by (metis (full_types) False Process1b.elims(2) \<open>AcceptorAction a2 st st2\<close>)
        then have "a2 = a"
          using f1 by (metis (no_types) False Process1a.elims(2))
        then show ?thesis
          using \<open>AcceptorAction a2 st st2\<close> by force
      qed
    qed
  qed
qed




lemma Process1bLearnerLoopDone_Not_ProposerSendAction :
  assumes "Process1bLearnerLoopDone a st st2"
    shows "\<not> ProposerSendAction st st2"
  by (metis (no_types, lifting) Process1bLearnerLoopDone.elims(1) ProposerSendAction.elims(2) Send1a.elims(2) assms not_Cons_self select_convs(1) surjective update_convs(1) update_convs(6))

lemma Process1bLearnerLoopDone_Not_LearnerRecv :
  assumes "Process1bLearnerLoopDone a st st2"
    shows "\<not> LearnerRecv ln m st st2"
  by (smt (verit, best) LearnerRecv.elims(2) Process1bLearnerLoopDone.elims(1) assms ext_inject not_Cons_self2 surjective update_convs(3) update_convs(6))

lemma Process1bLearnerLoopDone_Not_LearnerDecide :
  assumes "Process1bLearnerLoopDone a st st2"
      and "st \<noteq> st2"
    shows "\<not> LearnerDecide ln blt val st st2"
  by (metis (no_types, lifting) LearnerDecide.elims(1) Process1bLearnerLoopDone.elims(2) assms(1) assms(2) select_convs(8) surjective update_convs(6) update_convs(8))

lemma Process1bLearnerLoopDone_Not_LearnerProcessAction :
  assumes "Process1bLearnerLoopDone a st st2"
      and "st \<noteq> st2"
    shows "\<not> LearnerProcessAction st st2"
  by (meson LearnerProcessAction.elims LearnerAction.elims(2) Process1bLearnerLoopDone_Not_LearnerDecide Process1bLearnerLoopDone_Not_LearnerRecv assms)

lemma Process1bLearnerLoopDone_Not_FakeSend1b :
  assumes "Process1bLearnerLoopDone a st st2"
    shows "\<not> FakeSend1b a2 st st2"
  by (smt (verit, ccfv_threshold) FakeSend1b.elims(1) Process1bLearnerLoopDone.elims(2) assms ext_inject not_Cons_self2 surjective update_convs(1) update_convs(6))

lemma Process1bLearnerLoopDone_Not_FakeSend2a :
  assumes "Process1bLearnerLoopDone a st st2"
    shows "\<not> FakeSend2a a2 st st2"
  by (smt (verit, ccfv_threshold) FakeSend2a.elims(2) Process1bLearnerLoopDone.simps assms ext_inject not_Cons_self2 surjective update_convs(1) update_convs(6))

lemma Process1bLearnerLoopDone_Not_FakeAcceptorAction :
  assumes "Process1bLearnerLoopDone a st st2"
    shows "\<not> FakeAcceptorAction st st2"
  using FakeAcceptorAction.simps Process1bLearnerLoopDone_Not_FakeSend1b Process1bLearnerLoopDone_Not_FakeSend2a assms by blast

lemma Process1bLearnerLoopDone_Next_Implies_AcceptorAction:
  assumes "Next st st2"
      and "Process1bLearnerLoopDone a st st2"
      and "st \<noteq> st2"
    shows "AcceptorAction a st st2"
proof -
  have "\<not> two_a_lrn_loop st2 a"
    using assms(2) by auto
  have "two_a_lrn_loop st \<noteq> two_a_lrn_loop st2"
    using assms(2) assms(3) by fastforce
  have "\<forall>A. A \<noteq> a \<longrightarrow> two_a_lrn_loop st A = two_a_lrn_loop st2 A"
    using assms(2) by auto
  have "two_a_lrn_loop st a \<noteq> two_a_lrn_loop st2 a"
    using \<open>\<forall>A. A \<noteq> a \<longrightarrow> two_a_lrn_loop st A = two_a_lrn_loop st2 A\<close> \<open>two_a_lrn_loop st \<noteq> two_a_lrn_loop st2\<close> by auto
  have "two_a_lrn_loop st a"
    using \<open>\<not> two_a_lrn_loop st2 a\<close> \<open>two_a_lrn_loop st a \<noteq> two_a_lrn_loop st2 a\<close> by blast
  have "AcceptorProcessAction st st2"
    using Next.simps Process1bLearnerLoopDone_Not_FakeAcceptorAction Process1bLearnerLoopDone_Not_LearnerProcessAction Process1bLearnerLoopDone_Not_ProposerSendAction assms(1) assms(2) assms(3) by blast
  then show ?thesis
    unfolding AcceptorProcessAction.simps
  proof (elim exE)
    fix a2
    assume "AcceptorAction a2 st st2"
    have "Process1bLearnerLoopDone a2 st st2"
      by (metis AcceptorAction.simps Process1a_Not_Process1bLearnerLoopDone Process1bLearnerLoop.simps Process1bLearnerLoopStep.elims(2) Process1b_Not_Process1bLearnerLoopDone \<open>AcceptorAction a2 st st2\<close> \<open>two_a_lrn_loop st \<noteq> two_a_lrn_loop st2\<close> assms(2))
    have "a = a2"
      using \<open>Process1bLearnerLoopDone a2 st st2\<close> \<open>\<not> two_a_lrn_loop st2 a\<close> \<open>two_a_lrn_loop st a\<close> surjective by fastforce
    show ?thesis
      using \<open>AcceptorAction a2 st st2\<close> \<open>a = a2\<close> by blast
  qed
qed


lemma Process1a_not_looping_Next:
  assumes "Next st st2"
  shows "(\<exists>m\<in>set (msgs st). Process1a a m st st2) \<longrightarrow> \<not> two_a_lrn_loop st a"
  by (meson AcceptorAction.elims(2) Process1a_Next_Implies_AcceptorAction Process1a_Not_Process1bLearnerLoopDone Process1a_Not_Process1bLearnerLoopStep Process1bLearnerLoop.elims(2) assms)

lemma Process1a_not_looping:
  assumes "Spec f"
  shows "(\<exists>m\<in>set (msgs (f i)). Process1a a m (f i) (f (1 + i))) \<longrightarrow> \<not> two_a_lrn_loop (f i) a"
proof (induction i)
  case 0
  then show ?case
    by (metis Init.simps Spec.simps assms select_convs(6))
next
  case (Suc i)
  then show ?case
    by (metis AcceptorAction.elims(2) Process1a.elims(2) Process1a_Next_Implies_AcceptorAction Process1a_Not_Process1bLearnerLoopDone Process1a_Not_Process1bLearnerLoopStep Process1bLearnerLoop.elims(2) Send.elims(2) Spec.elims(2) assms not_Cons_self plus_1_eq_Suc)
qed

lemma no_queue_during_loop_Next:
  assumes "Next st st2" 
      and "two_a_lrn_loop st a \<longrightarrow> queued_msg st a = None"
      and "(\<exists>m\<in>set (msgs st). Process1a a m st st2) \<longrightarrow> \<not> two_a_lrn_loop st a"
    shows "two_a_lrn_loop st2 a \<longrightarrow> queued_msg st2 a = None"
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
      proof (clarify)
        fix A m
        assume "is_safe A"
           and "queued_msg st A = None"
           and "m \<in> set (msgs st)"
           and "Process1a A m st st2"
           and "two_a_lrn_loop st2 a"
        then show "queued_msg st2 a = None"
        proof (cases "A = a")
          case True
          define new1b where "new1b = M1b A (m # recent_msgs st A)"
          show ?thesis
          proof (cases "WellFormed st new1b")
            case True
            then show ?thesis
              by (metis Process1a.elims(2) \<open>\<exists>A. is_safe A \<and> queued_msg st A = None \<and> (\<exists>m\<in>set (msgs st). Process1a A m st st2)\<close> \<open>two_a_lrn_loop st2 a\<close> assms(2) assms(3))
          next
            case False
            then show ?thesis
              by (metis Process1a.elims(2) True \<open>Process1a A m st st2\<close> \<open>queued_msg st A = None\<close> new1b_def)
          qed
        next
          case False
          then show ?thesis
            by (metis Process1a.elims(2) \<open>Process1a A m st st2\<close> \<open>two_a_lrn_loop st2 a\<close> assms(2))
        qed
      qed
    next
      assume "\<exists>A :: Acceptor. is_safe A
                        \<and> queued_msg st A \<noteq> None 
                        \<and> Process1b A (the (queued_msg st A)) st st2"
      then show ?thesis
        unfolding Process1b.simps
        by (metis (no_types, lifting) assms(2))
    next
      assume "\<exists>A :: Acceptor. is_safe A
                  \<and> queued_msg st A = None 
                  \<and> (\<exists>m \<in> set (msgs st). Process1b A m st st2)"
      then show ?thesis
        unfolding Process1b.simps
        by (metis assms(2))
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
      proof (clarify)
        fix A
        assume "is_safe A"
           and "two_a_lrn_loop st A"
           and "Process1bLearnerLoopDone A st st2"
           and "two_a_lrn_loop st2 a"
        then show "queued_msg st2 a = None"
        proof (cases "A = a")
          case True
          then show ?thesis
            using \<open>Process1bLearnerLoopDone A st st2\<close> \<open>two_a_lrn_loop st A\<close> assms(2) by auto
        next
          case False
          then show ?thesis
            using \<open>Process1bLearnerLoopDone A st st2\<close> \<open>two_a_lrn_loop st2 a\<close> assms(2) by auto
        qed
      qed
    next
      assume "LearnerProcessAction st st2"
      then show ?thesis
        by (smt (verit, del_insts) LearnerProcessAction.elims LearnerAction.elims(2) LearnerDecide.simps LearnerRecv.elims(2) assms(2) ext_inject surjective update_convs(3) update_convs(8))
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

lemma no_queue_during_loop:
  assumes "Spec f"
  shows "two_a_lrn_loop (f i) a \<longrightarrow> queued_msg (f i) a = None"
proof (induction i)
  case 0
  then show ?case
    by (metis Init.elims Spec.elims(2) assms ext_inject surjective)
next
  case (Suc i)
  then show ?case
    by (metis Process1a_not_looping Spec.elims(2) assms no_queue_during_loop_Next plus_1_eq_Suc)
qed

lemma ballot_present:
  shows "M1a b \<in> set l \<longrightarrow> b \<in> (Get1a ` set l)"
proof (induction l)
  case Nil
  then show ?case 
    by simp
next
  case (Cons a l)
  then show ?case
  proof (cases "a = M1a b")
    case True
    have "b \<in> Get1a ` set (M1a b # l)"
      by auto
    show ?thesis
      using True \<open>b \<in> Get1a ` set (M1a b # l)\<close> by presburger
  next
    case False
    then show ?thesis
      using local.Cons by auto
  qed
qed

lemma new_bal_unknown:
  assumes "\<forall>a \<in> Q. the (MaxBalO st a) < bal x"
      and "type x = T1a"
    shows "\<forall>a \<in> Q. x \<notin> set (known_msgs_acc st a)"
proof (clarify)
  fix a
  assume "a \<in> Q"
     and "x \<in> set (known_msgs_acc st a)"
  then show False
  proof (cases "known_msgs_acc st a")
    case Nil
    then show ?thesis
      using \<open>x \<in> set (known_msgs_acc st a)\<close> by auto
  next
    case (Cons m list)
    then show ?thesis 
    proof (cases x)
      case (M1a b)
      have "Max (Get1a ` set (known_msgs_acc st a)) < b"
        using M1a \<open>a \<in> Q\<close> assms(1) local.Cons by fastforce
      have "b \<in> Get1a ` set (known_msgs_acc st a)"
        using M1a \<open>x \<in> set (known_msgs_acc st a)\<close> ballot_present by blast
      have "b \<le> Max (set (map Get1a (known_msgs_acc st a)))"
        using \<open>b \<in> Get1a ` set (known_msgs_acc st a)\<close> by auto
      have "b \<le> Max (Get1a ` set (known_msgs_acc st a))"
        using \<open>b \<le> Max (set (map Get1a (known_msgs_acc st a)))\<close> by auto
      show ?thesis
        using \<open>Max (Get1a ` set (known_msgs_acc st a)) < b\<close> \<open>b \<le> Max (Get1a ` set (known_msgs_acc st a))\<close> verit_comp_simplify1(3) by blast
    next
      case (M1b _ _)
      then show ?thesis
        using assms(2) by auto
    next
      case (M2a _ _ _)
      then show ?thesis 
        using assms(2) by auto
    qed
  qed
qed



(*
There are four actions associated with AcceptorAction
1. Process1a
2. Process1b
3. Process1bLearnerLoopStep
4. Process1bLearnerLoopDone

Under what conditions can these disable AcceptorAction?

Preliminary hypotheses:

Process1a will enable AcceptorAction if it queues a 1b message.
If it's activated on a non-wellformed message, it may disable AcceptorAction 
  if that's the last pending message
  (Note: Proven)

Process1b will enable AcceptorAction when the message is a max ballot because it
  activates two_a_lrn_loop
  (Note: Proven)

Process1bLearnerLoopStep will maintain AcceptorAction since it doesn't disable two_a_lrn_loop
  (Note: Proven)

Process1bLearnerLoopDone may disable AcceptorAction if there are no messages left to proccess.
  (Note: Proven)

*)

(*
Note: 
  Can the well-formedness condition be weakened?
  Can it just be the wellformedness of m?
*)
lemma Process1a_Preserves_AcceptorAction:
  assumes "Spec f"
      and "Process1a a m (f i) (f (1 + i))"
      and "WellFormed (f i) (M1b a (m # recent_msgs (f i) a)) \<or> 
           (\<exists>m2 \<in> set (msgs (f i)). m2 \<noteq> m \<and> Recv_acc (f i) a m2 \<and> (type m2 = T1a \<or> type m2 = T1b))"
    shows "Enabled (AcceptorAction a) (f (1 + i))"
proof -
  have qa: "AcceptorAction a (f i) (f (1 + i))"
    by (metis Process1a.elims(2) Process1a_Next_Implies_AcceptorAction Process1a_Req_known_msgs Recv_acc.elims(2) Spec.elims(2) add_diff_cancel_left' assms(1) assms(2) plus_1_eq_Suc)
  define st where "st = (f i)"
  define st2 where "st2 = (f (1 + i))"
  define new1b where "new1b = M1b a (m # recent_msgs st a)"
  have "\<not> two_a_lrn_loop st2 a"
    by (metis AcceptorAction.elims(2) Process1a.elims(2) Process1a_Not_Process1bLearnerLoopDone Process1a_Not_Process1bLearnerLoopStep Process1bLearnerLoop.simps assms(2) qa st2_def)
  show ?thesis
  proof (cases "WellFormed st new1b")
    case True
    have "Send new1b st st2
          \<and> (recent_msgs st2 = (
              \<lambda>a2. if a2 = a then []
                             else recent_msgs st a2))
          \<and> (queued_msg st2 = (
              \<lambda>a2. if a2 = a then Some new1b 
                             else queued_msg st a2))"
      by (metis (full_types, opaque_lifting) Process1a.elims(2) True assms(2) new1b_def st2_def st_def)
    have "type new1b = T1b"
      using new1b_def by auto
    have "WellFormed st2 new1b"
      by (metis MessageType.distinct(5) True WellFormed.elims(1) \<open>type new1b = T1b\<close>)
    have "ref new1b = {m} \<union> set (recent_msgs st a)"
      using new1b_def by auto
    have "m \<in> set (known_msgs_acc st2 a)"
      using Process1a_Req_known_msgs assms(1) assms(2) diff_add_inverse st2_def by presburger
    have "\<forall>m \<in> set (recent_msgs st a). m \<in> set (known_msgs_acc st a)"
      by (metis AcceptorAction.elims(2) RecentMsgsSpec.elims(2) RecentMsgsSpecResult assms(1) qa st_def subset_code(1))
    have "\<forall>m \<in> set (recent_msgs st a). m \<in> set (known_msgs_acc st2 a)"
      using \<open>\<forall>m\<in>set (recent_msgs st a). m \<in> set (known_msgs_acc st a)\<close> assms(1) known_msgs_acc_preserved le_add2 st2_def st_def by blast
    have "Proper_acc st2 a new1b"
      by (simp add: \<open>\<forall>m\<in>set (recent_msgs st a). m \<in> set (known_msgs_acc st2 a)\<close> \<open>m \<in> set (known_msgs_acc st2 a)\<close> new1b_def)
    have "new1b \<notin> set (known_msgs_acc st2 a)"
      by (metis AcceptorAction.elims(2) KnownMsgs_accSpec.elims(2) KnownMsgs_accSpecResult Process1a.elims(2) Proper_acc.elims(2) Recv_acc.elims(2) Store_acc.elims(2) assms(1) assms(2) qa in_set_member member_rec(1) new1b_def ref.simps(2) st2_def)
    have "Recv_acc st2 a new1b"
      using Recv_acc.simps \<open>Proper_acc st2 a new1b\<close> \<open>WellFormed st2 new1b\<close> \<open>new1b \<notin> set (known_msgs_acc st2 a)\<close> by blast
    show ?thesis
      by (metis AcceptorAction.elims(2) AcceptorAction_NotEnabled \<open>Recv_acc st2 a new1b\<close> \<open>Send new1b st st2 \<and> recent_msgs st2 = (\<lambda>a2. if a2 = a then [] else recent_msgs st a2) \<and> queued_msg st2 = (\<lambda>a2. if a2 = a then Some new1b else queued_msg st a2)\<close> \<open>type new1b = T1b\<close> qa option.distinct(1) option.sel st2_def)
  next
    case False
    have "(recent_msgs st2 = (
              \<lambda>a2. if a2 = a then m # recent_msgs st a2 
                             else recent_msgs st a2))
          \<and> (msgs st = msgs st2)
          \<and> (queued_msg st = queued_msg st2)"
      by (metis (full_types, opaque_lifting) False Process1a.simps assms(2) new1b_def st2_def st_def)
    have "queued_msg st2 a = None"
      by (metis AcceptorAction.elims(2) Process1a_Not_Process1bLearnerLoopDone Process1a_Not_Process1bLearnerLoopStep Process1bLearnerLoop.simps Process1b_Not_Process1a \<open>recent_msgs st2 = (\<lambda>a2. if a2 = a then m # recent_msgs st a2 else recent_msgs st a2) \<and> msgs st = msgs st2 \<and> queued_msg st = queued_msg st2\<close> assms(2) qa st_def)
    have "\<exists>m2 \<in> set (msgs st2). Recv_acc st2 a m2 \<and> (type m2 = T1a \<or> type m2 = T1b)"
      by (smt (z3) False Process1a.simps Proper_acc.simps Recv_acc.simps Store_acc.elims(2) WellFormed_monotone assms(2) assms(3) list.set_intros(2) new1b_def set_ConsD st2_def st_def)
    show ?thesis
      by (metis AcceptorAction.elims(2) AcceptorAction_NotEnabled \<open>\<exists>m2\<in>set (msgs st2). Recv_acc st2 a m2 \<and> (type m2 = T1a \<or> type m2 = T1b)\<close> \<open>queued_msg st2 a = None\<close> qa st2_def)
  qed
qed

lemma Process1a_Disables_AcceptorAction:
  assumes "Spec f"
      and "Process1a a m (f i) (f (1 + i))"
      and "\<not> Enabled (AcceptorAction a) (f (1 + i))"
    shows "\<not> WellFormed (f i) (M1b a (m # recent_msgs (f i) a))"
      and "\<not> (\<exists>m2 \<in> set (msgs (f i)). m2 \<noteq> m \<and> Recv_acc (f i) a m2 \<and> (type m2 = T1a \<or> type m2 = T1b))"
  using Process1a_Preserves_AcceptorAction assms(1) assms(2) assms(3) apply blast
  using Process1a_Preserves_AcceptorAction assms(1) assms(2) assms(3) by blast  

lemma Process1b_Preserves_AcceptorAction:
  assumes "Spec f"
      and "Process1b a m (f i) (f (1 + i))"
      and "(\<forall> mb b :: Ballot. MaxBal (f i) a b \<and> B m b \<longrightarrow> mb \<le> b) \<or>
           (\<exists>m2 \<in> set (msgs (f i)). m2 \<noteq> m \<and> Recv_acc (f i) a m2 \<and> (type m2 = T1a \<or> type m2 = T1b))"
    shows "Enabled (AcceptorAction a) (f (1 + i))"
proof -
  define st where "st = f i"
  define st2 where "st2 = f (1 + i)"
  have qa: "AcceptorAction a st st2"
    by (metis Process1b.elims(2) Process1b_Next_Implies_AcceptorAction Spec.elims(2) Suc_eq_plus1_left assms(1) assms(2) not_Cons_self st2_def st_def)
  have "\<not> two_a_lrn_loop st a"
    by (metis AcceptorAction.elims(2) Process1bLearnerLoop.simps Process1b_Not_Process1bLearnerLoopDone Process1b_Not_Process1bLearnerLoopStep assms(2) qa st2_def st_def)
  then show ?thesis
  proof (cases "\<forall> mb b :: Ballot. MaxBal (f i) a b \<and> B m b \<longrightarrow> mb \<le> b")
    case True
    have "two_a_lrn_loop st2 a"
      sorry
    then show ?thesis
      by (metis AcceptorAction.elims(2) AcceptorAction_Enabled qa st2_def)
  next
    case False
    have "\<not> two_a_lrn_loop st2 a"
      sorry
    have "queued_msg st2 a = None"
      by (metis Process1b.elims(2) assms(2) st2_def)
    have "\<exists>m2 \<in> set (msgs st). m2 \<noteq> m \<and> Recv_acc st a m2 \<and> (type m2 = T1a \<or> type m2 = T1b)"
      using False assms(3) st_def by blast
    then have "\<exists>m2 \<in> set (msgs st2). Recv_acc st2 a m2 \<and> (type m2 = T1a \<or> type m2 = T1b)"
    proof (clarify)
      fix m2
      assume "m2 \<in> set (msgs st)"
         and "m2 \<noteq> m"
         and "Recv_acc st a m2"
         and "type m2 = T1a \<or> type m2 = T1b"
      have "m2 \<in> set (msgs st2)"
        by (metis Process1b.elims(2) \<open>m2 \<in> set (msgs st)\<close> assms(2) st2_def st_def)
      have "m2 \<notin> set (known_msgs_acc st2 a)"
        by (metis Process1b.elims(2) Recv_acc.elims(2) Store_acc.elims(2) \<open>Recv_acc st a m2\<close> \<open>m2 \<noteq> m\<close> assms(2) in_set_member member_rec(1) st2_def st_def)
      have "WellFormed st2 m2"
        using Recv_acc.simps Wellformed_Conservation \<open>Recv_acc st a m2\<close> assms(1) le_add2 st2_def st_def by blast
      have "Proper_acc st2 a m2"
        sorry
      have "Recv_acc st2 a m2"
        using Recv_acc.simps \<open>Proper_acc st2 a m2\<close> \<open>WellFormed st2 m2\<close> \<open>m2 \<notin> set (known_msgs_acc st2 a)\<close> by blast
      show ?thesis
        using \<open>Recv_acc st2 a m2\<close> \<open>m2 \<in> set (msgs st2)\<close> \<open>type m2 = T1a \<or> type m2 = T1b\<close> by blast
    qed
    then show ?thesis
      by (metis AcceptorAction.elims(2) AcceptorAction_NotEnabled \<open>queued_msg st2 a = None\<close> qa st2_def)
  qed
qed

lemma Process1b_Disables_AcceptorAction:
  assumes "Spec f"
      and "Process1b a m (f i) (f (1 + i))"
      and "\<not> Enabled (AcceptorAction a) (f (1 + i))"
    shows "\<not> (\<forall> mb b :: Ballot. MaxBal (f i) a b \<and> B m b \<longrightarrow> mb \<le> b)"
      and "\<not> (\<exists>m2 \<in> set (msgs (f i)). m2 \<noteq> m \<and> Recv_acc (f i) a m2 \<and> (type m2 = T1a \<or> type m2 = T1b))"
  using Process1b_Preserves_AcceptorAction assms(1) assms(2) assms(3) apply blast
  using Process1b_Preserves_AcceptorAction assms(1) assms(2) assms(3) by blast

lemma Process1bLearnerLoopStep_Preserves_AcceptorAction:
  assumes "Process1bLearnerLoopStep a ln st st2"
      and "AcceptorAction a st st2"
    shows "Enabled (AcceptorAction a) st2"
proof -
  have "two_a_lrn_loop st a"
    by (meson AcceptorAction.elims(2) Process1a_Not_Process1bLearnerLoopStep Process1b_Not_Process1bLearnerLoopStep assms(1) assms(2))
  then show ?thesis
    by (metis AcceptorAction.elims(2) AcceptorAction_Enabled Process1bLearnerLoopStep.elims(2) assms(1) assms(2))
qed

lemma Process1bLearnerLoopDone_Preserves_AcceptorAction:
  assumes "Spec f"
      and "Process1bLearnerLoopDone a (f i) (f (1 + i))"
      and "AcceptorAction a (f i) (f (1 + i))"
      and "\<exists>m \<in> set (msgs (f i)). Recv_acc (f i) a m \<and> (type m = T1a \<or> type m = T1b)"
    shows "Enabled (AcceptorAction a) (f (1 + i))"
proof -
  have "two_a_lrn_loop (f i) a"
    by (meson AcceptorAction.elims(2) Process1a_Not_Process1bLearnerLoopDone Process1b_Not_Process1bLearnerLoopDone assms(2) assms(3))
  have "queued_msg (f i) a = None"
    using \<open>two_a_lrn_loop (f i) a\<close> assms(1) no_queue_during_loop by blast
  have "queued_msg (f (1 + i)) a = None"
    using \<open>queued_msg (f i) a = None\<close> assms(2) by auto
  have "\<not> two_a_lrn_loop (f (1 + i)) a"
    using assms(2) by auto
  have "\<exists>m \<in> set (msgs (f (1 + i))). Recv_acc (f (1 + i)) a m \<and> (type m = T1a \<or> type m = T1b)"
    using assms(2) assms(4) by auto
  show ?thesis
    by (meson AcceptorAction.elims(2) AcceptorAction_NotEnabled \<open>\<exists>m\<in>set (msgs (f (1 + i))). Recv_acc (f (1 + i)) a m \<and> (type m = T1a \<or> type m = T1b)\<close> \<open>queued_msg (f (1 + i)) a = None\<close> assms(3))
qed

lemma Process1bLearnerLoopDone_Disables_AcceptorAction:
  assumes "Spec f"
      and "Process1bLearnerLoopDone a (f i) (f (1 + i))"
      and "AcceptorAction a (f i) (f (1 + i))"
      and "\<not> Enabled (AcceptorAction a) (f (1 + i))"
    shows "\<not> (\<exists>m \<in> set (msgs (f i)). Recv_acc (f i) a m \<and> (type m = T1a \<or> type m = T1b))"
  using Process1bLearnerLoopDone_Preserves_AcceptorAction assms(1) assms(2) assms(3) assms(4) by blast

lemma Process1bLearnerLoopDone_Preserves_AcceptorAction_INEQ:
  assumes "Spec f"
      and "Process1bLearnerLoopDone a (f i) (f (1 + i))"
      and "f i \<noteq> f (1 + i)"
      and "\<exists>m \<in> set (msgs (f i)). Recv_acc (f i) a m \<and> (type m = T1a \<or> type m = T1b)"
    shows "Enabled (AcceptorAction a) (f (1 + i))"
proof -
  have qa: "AcceptorAction a (f i) (f (1 + i))"
    by (metis Process1bLearnerLoopDone_Next_Implies_AcceptorAction Spec.elims(2) assms(1) assms(2) assms(3) plus_1_eq_Suc)
  have "two_a_lrn_loop (f i) a"
    by (meson AcceptorAction.elims(2) Process1a_Not_Process1bLearnerLoopDone Process1b_Not_Process1bLearnerLoopDone assms(2) qa)
  have "queued_msg (f i) a = None"
    using \<open>two_a_lrn_loop (f i) a\<close> assms(1) no_queue_during_loop by blast
  have "queued_msg (f (1 + i)) a = None"
    using \<open>queued_msg (f i) a = None\<close> assms(2) by auto
  have "\<not> two_a_lrn_loop (f (1 + i)) a"
    using assms(2) by auto
  have "\<exists>m \<in> set (msgs (f (1 + i))). Recv_acc (f (1 + i)) a m \<and> (type m = T1a \<or> type m = T1b)"
    using assms(2) assms(4) by auto
  show ?thesis
    by (meson AcceptorAction.elims(2) AcceptorAction_NotEnabled \<open>\<exists>m\<in>set (msgs (f (1 + i))). Recv_acc (f (1 + i)) a m \<and> (type m = T1a \<or> type m = T1b)\<close> \<open>queued_msg (f (1 + i)) a = None\<close> qa)
qed


fun three_cases :: "Acceptor \<Rightarrow> State \<Rightarrow> State \<Rightarrow> bool" where
  "three_cases a st st2 = (
           (\<exists>m. Process1a a m st st2 
              \<and> \<not> WellFormed st (M1b a (m # recent_msgs st a)) 
              \<and> \<not> (\<exists>m2 \<in> set (msgs st). m2 \<noteq> m \<and> Recv_acc st a m2 \<and> (type m2 = T1a \<or> type m2 = T1b))) \<or>
           (\<exists>m. Process1b a m st st2 
              \<and> \<not> (\<forall> mb b :: Ballot. MaxBal st a b \<and> B m b \<longrightarrow> mb \<le> b)
              \<and> \<not> (\<exists>m2 \<in> set (msgs st). m2 \<noteq> m \<and> Recv_acc st a m2 \<and> (type m2 = T1a \<or> type m2 = T1b))) \<or>
           (Process1bLearnerLoopDone a st st2 
              \<and> \<not> (\<exists>m \<in> set (msgs st). Recv_acc st a m \<and> (type m = T1a \<or> type m = T1b))))"

lemma Preserves_AcceptorAction_Disabled_Three_Cases_Pre:
  assumes "Spec f"
      and "Enabled (AcceptorAction a) (f i)"
      and "\<not> Enabled (AcceptorAction a) (f (1 + i))"
    shows "(\<exists>m. Process1a a m (f i) (f (1 + i)) 
              \<and> \<not> WellFormed (f i) (M1b a (m # recent_msgs (f i) a)) 
              \<and> \<not> (\<exists>m2 \<in> set (msgs (f i)). m2 \<noteq> m \<and> Recv_acc (f i) a m2 \<and> (type m2 = T1a \<or> type m2 = T1b))) \<or>
           (\<exists>m. Process1b a m (f i) (f (1 + i)) 
              \<and> \<not> (\<forall> mb b :: Ballot. MaxBal (f i) a b \<and> B m b \<longrightarrow> mb \<le> b)
              \<and> \<not> (\<exists>m2 \<in> set (msgs (f i)). m2 \<noteq> m \<and> Recv_acc (f i) a m2 \<and> (type m2 = T1a \<or> type m2 = T1b))) \<or>
           (Process1bLearnerLoopDone a (f i) (f (1 + i)) 
              \<and> \<not> (\<exists>m \<in> set (msgs (f i)). Recv_acc (f i) a m \<and> (type m = T1a \<or> type m = T1b)))"
proof -
  have "AcceptorAction a (f i) (f (1 + i))"
    by (metis Spec.elims(2) Suc_eq_plus1_left assms(1) assms(2) assms(3) only_AcceptorAction_disables_AcceptorAction)
  then have "(\<exists>m. Process1a a m (f i) (f (1 + i))) \<or>
             (\<exists>m. Process1b a m (f i) (f (1 + i))) \<or>
             Process1bLearnerLoopDone a (f i) (f (1 + i))"
    by (meson AcceptorAction.elims(2) Process1bLearnerLoop.elims(2) Process1bLearnerLoopStep_Preserves_AcceptorAction assms(3))
  then show ?thesis
  proof (elim disjE)
    assume "\<exists>m. Process1a a m (f i) (f (1 + i))"
    then show ?thesis
      using Process1a_Preserves_AcceptorAction assms(1) assms(3) by blast
  next
    assume "\<exists>m. Process1b a m (f i) (f (1 + i))"
    then show ?thesis
      by (metis Process1b_Preserves_AcceptorAction assms(1) assms(3))
  next
    assume "Process1bLearnerLoopDone a (f i) (f (1 + i))"
    then show ?thesis
      using Process1bLearnerLoopDone_Disables_AcceptorAction \<open>AcceptorAction a (f i) (f (1 + i))\<close> assms(1) assms(3) by presburger
  qed
qed

lemma Preserves_AcceptorAction_Disabled_Three_Cases:
  assumes "Spec f"
      and "Enabled (AcceptorAction a) (f i)"
      and "\<not> Enabled (AcceptorAction a) (f (1 + i))"
    shows "three_cases a (f i) (f (1 + i))"
  unfolding three_cases.simps
  using Preserves_AcceptorAction_Disabled_Three_Cases_Pre assms(1) assms(2) assms(3) by presburger


end