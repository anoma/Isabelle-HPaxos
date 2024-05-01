theory hpaxos_liveness
imports Main  hpaxos hpaxos_safety hpaxos_aux hpaxos_time
begin

lemma step_1a_then:
  assumes "Spec f"
      and "Send1a b (f i) (f (1 + i))"
      and "\<forall> mb :: Ballot. MaxBal (f i) a mb \<longrightarrow> mb < b"
      and "is_safe a"
    shows "M1a b \<in> set (msgs (f (1 + i)))"
      and "Enabled (AcceptorAction a) (f (1 + i))"
      and "\<forall> mb :: Ballot. MaxBal (f (1 + i)) a mb \<longrightarrow> mb < b"
proof -
  show "M1a b \<in> set (msgs (f (1 + i)))"
    using assms(2) by fastforce
next
  have "(M1a b) \<in> set (msgs (f (1 + i)))"
    using assms(2) by auto
  have "M1a b \<notin> set (known_msgs_acc (f i) a)"
    by (metis B_1a assms(3) bal.simps(1) maxbal_absence type.simps(1))
  then have "M1a b \<notin> set (known_msgs_acc (f (1 + i)) a)"
    using assms(2) by auto
  then have "Recv_acc (f (1 + i)) a (M1a b)"
    by simp
  then have "\<exists>m \<in> set (msgs (f (1 + i))). Recv_acc (f (1 + i)) a m \<and> (type m = T1a \<or> type m = T1b)"
    using \<open>M1a b \<in> set (msgs (f (1 + i)))\<close> type.simps(1) by blast
  then show "Enabled (AcceptorAction a) (f (1 + i))"
    using AcceptorAction_NotEnabled_Spec assms(1) assms(4) by presburger
next
  show "\<forall> mb :: Ballot. MaxBal (f (1 + i)) a mb \<longrightarrow> mb < b"
    using assms(2) assms(3) by force
qed

(*
Idea: Prove that the T1a message must eventually make its way to
known_msgs_acc a by the time AcceptorAction is disabled. Prove by
induction that the only way for this to happen is a proccess1a step. 

With appropriate assumptions, all proerties should continue to hold
as well.
*)
lemma step_1a_side:
  assumes "Spec f"
      and "M1a b \<notin> set (known_msgs_acc (f i) a)"
    shows "i < j \<and> M1a b \<in> set (known_msgs_acc (f j) a) \<longrightarrow>
           (\<exists>k. i \<le> k \<and> k < j \<and> 
              M1a b \<notin> set (known_msgs_acc (f k) a)
            \<and> Process1a a (M1a b) (f k) (f (1 + k)))"
proof (induction j)
  case 0
  then show ?case 
    by fastforce
next
  case (Suc j)
  show "i < Suc j \<and> M1a b \<in> set (known_msgs_acc (f (Suc j)) a) \<longrightarrow>
                 (\<exists>k\<ge>i. k < Suc j \<and> M1a b \<notin> set (known_msgs_acc (f k) a) \<and> Process1a a (M1a b) (f k) (f (1 + k)))"
  proof (cases "M1a b \<in> set (known_msgs_acc (f j) a)")
    case True
    then show ?thesis
      using Suc assms(2) less_Suc_eq by blast
  next
    case False
    then show ?thesis
    proof (clarify)
      assume "i < Suc j"
         and "M1a b \<in> set (known_msgs_acc (f (Suc j)) a)"
      have "Next (f j) (f (Suc j))"
        by (metis False Spec.elims(2) \<open>M1a b \<in> set (known_msgs_acc (f (Suc j)) a)\<close> assms(1))
      then have "\<not> (ProposerSendAction (f j) (f (Suc j)))"
        by (metis False ProposerSendAction.elims(2) Send1a.elims(2) \<open>M1a b \<in> set (known_msgs_acc (f (Suc j)) a)\<close> ext_inject surjective update_convs(1))
      have "\<forall> ln m. \<not> (LearnerRecv ln m (f j) (f (Suc j)))"
        by (smt (verit, ccfv_SIG) False LearnerRecv.simps \<open>M1a b \<in> set (known_msgs_acc (f (Suc j)) a)\<close> ext_inject surjective update_convs(3))
      have "\<forall> ln blt val. \<not> (LearnerDecide ln blt val (f j) (f (Suc j)))"
        using False \<open>M1a b \<in> set (known_msgs_acc (f (Suc j)) a)\<close> by force
      then have "\<forall>a. \<not> (LearnerProcessAction (f j) (f (Suc j)))"
        by (meson LearnerAction.elims(2) LearnerProcessAction.elims(1) \<open>\<forall>ln m. \<not> LearnerRecv ln m (f j) (f (Suc j))\<close>)
      have "\<forall>a. \<not> (FakeSend1b a (f j) (f (Suc j)))"
        by (metis FakeSend1b.elims(1) False \<open>M1a b \<in> set (known_msgs_acc (f (Suc j)) a)\<close> ext_inject surjective update_convs(1))
      have "\<forall>a. \<not> (FakeSend2a a (f j) (f (Suc j)))"
        by (metis FakeSend2a.simps False \<open>M1a b \<in> set (known_msgs_acc (f (Suc j)) a)\<close> ext_inject surjective update_convs(1))
      then have "\<not> (FakeAcceptorAction (f j) (f (Suc j)))"
        using FakeAcceptorAction.simps \<open>\<forall>a. \<not> FakeSend1b a (f j) (f (Suc j))\<close> by presburger
      then have "AcceptorProcessAction (f j) (f (Suc j))"
        by (meson LearnerAction.elims(2) LearnerProcessAction.elims(2) Next.simps \<open>Next (f j) (f (Suc j))\<close> \<open>\<forall>ln blt val. \<not> LearnerDecide ln blt val (f j) (f (Suc j))\<close> \<open>\<forall>ln m. \<not> LearnerRecv ln m (f j) (f (Suc j))\<close> \<open>\<not> ProposerSendAction (f j) (f (Suc j))\<close>)
      have "\<forall> A m. a \<noteq> A \<longrightarrow> \<not> (Process1a A m (f j) (f (Suc j)))"
        by (metis False Process1a.elims(2) Store_acc.elims(2) \<open>M1a b \<in> set (known_msgs_acc (f (Suc j)) a)\<close>)
      have "\<forall> A m. a \<noteq> A \<longrightarrow> \<not> (Process1b A m (f j) (f (Suc j)))"
        by (metis False Process1b.elims(2) Store_acc.elims(2) \<open>M1a b \<in> set (known_msgs_acc (f (Suc j)) a)\<close>)
      have "\<forall> a. \<not> (Process1bLearnerLoopDone a (f j) (f (Suc j)))"
        using False \<open>M1a b \<in> set (known_msgs_acc (f (Suc j)) a)\<close> by force
      have "\<forall> ln. \<not> (Process1bLearnerLoopStep a ln (f j) (f (Suc j)))"
        unfolding Process1bLearnerLoopStep.simps
        by (smt (verit, ccfv_SIG) False PreMessage.distinct(3) Store_acc.elims(2) \<open>M1a b \<in> set (known_msgs_acc (f (Suc j)) a)\<close> set_ConsD)  
      then have "\<forall> A. a \<noteq> A \<longrightarrow> \<not> AcceptorAction A (f j) (f (Suc j))"
      proof -
        { fix aa :: Acceptor
          have "known_msgs_acc (f (Suc j)) \<noteq> known_msgs_acc (f j) \<and> known_msgs_acc (f (Suc j)) a \<noteq> known_msgs_acc (f j) a"
            using False \<open>M1a b \<in> set (known_msgs_acc (f (Suc j)) a)\<close> by fastforce
          then have "aa = a \<or> \<not> AcceptorAction aa (f j) (f (Suc j))"
            by (metis (full_types) AcceptorAction.elims(2) Process1bLearnerLoop.elims(2) Process1bLearnerLoopStep.elims(2) Store_acc.elims(2) \<open>\<forall>A m. a \<noteq> A \<longrightarrow> \<not> Process1a A m (f j) (f (Suc j))\<close> \<open>\<forall>A m. a \<noteq> A \<longrightarrow> \<not> Process1b A m (f j) (f (Suc j))\<close> \<open>\<forall>a. \<not> Process1bLearnerLoopDone a (f j) (f (Suc j))\<close>) }
        then show ?thesis
          by (metis (no_types))
      qed
      then have "AcceptorAction a (f j) (f (Suc j))"
        by (metis AcceptorProcessAction.simps \<open>AcceptorProcessAction (f j) (f (Suc j))\<close>)
      have "\<forall> m. (M1a b) \<noteq> m \<longrightarrow> \<not> (Process1a a m (f j) (f (Suc j)))"
        unfolding Process1a.simps
        by (metis False Store_acc.elims(2) \<open>M1a b \<in> set (known_msgs_acc (f (Suc j)) a)\<close> set_ConsD)
      have "\<not> (Process1b a (M1a b) (f j) (f (Suc j)))"
        by simp
      have "\<forall> m. (M1a b) \<noteq> m \<longrightarrow> \<not> (Process1b a m (f j) (f (Suc j)))"
        unfolding Process1b.simps
        by (metis (no_types, lifting) False Store_acc.elims(2) \<open>M1a b \<in> set (known_msgs_acc (f (Suc j)) a)\<close> set_ConsD)
      then have "\<forall> m. \<not> (Process1b a m (f j) (f (Suc j)))"
        by (metis \<open>\<not> Process1b a (M1a b) (f j) (f (Suc j))\<close>)
      then have "Process1a a (M1a b) (f j) (f (Suc j))"
        by (metis AcceptorAction.elims(2) Process1bLearnerLoop.elims(2) \<open>AcceptorAction a (f j) (f (Suc j))\<close> \<open>\<forall>a. \<not> Process1bLearnerLoopDone a (f j) (f (Suc j))\<close> \<open>\<forall>ln. \<not> Process1bLearnerLoopStep a ln (f j) (f (Suc j))\<close> \<open>\<forall>m. M1a b \<noteq> m \<longrightarrow> \<not> Process1a a m (f j) (f (Suc j))\<close>)
      then show "(\<exists>k. i \<le> k \<and> k < Suc j \<and> 
              M1a b \<notin> set (known_msgs_acc (f k) a)
            \<and> Process1a a (M1a b) (f k) (f (1 + k)))"
        by (metis False \<open>i < Suc j\<close> less_Suc_eq less_Suc_eq_le plus_1_eq_Suc)
    qed
  qed
qed

lemma step_1b_side:
  assumes "Spec f"
      and "m \<notin> set (known_msgs_acc (f i) a)"
      and "type m = T1b"
    shows "i < j \<and> m \<in> set (known_msgs_acc (f j) a) \<longrightarrow>
           (\<exists>k. i \<le> k \<and> k < j \<and> 
              m \<notin> set (known_msgs_acc (f k) a)
            \<and> Process1b a m (f k) (f (1 + k)))"
proof (induction j)
  case 0
  then show ?case 
    by fastforce
next
  case (Suc j)
  show "i < Suc j \<and> m \<in> set (known_msgs_acc (f (Suc j)) a) \<longrightarrow>
                 (\<exists>k\<ge>i. k < Suc j \<and> m \<notin> set (known_msgs_acc (f k) a) \<and> Process1b a m (f k) (f (1 + k)))"
  proof (cases "m \<in> set (known_msgs_acc (f j) a)")
    case True
    then show ?thesis
      using Suc assms(2) assms(3) less_Suc_eq by blast
  next
    case False
    have "(\<forall>m \<in> set (known_msgs_acc (f (Suc j)) a). type m = T1b \<longrightarrow> m \<in> set (known_msgs_acc (f j) a)) \<longrightarrow> ?thesis"
      using False assms(3) by blast
    show ?thesis
    proof (clarify)
      assume "i < Suc j"
         and "m \<in> set (known_msgs_acc (f (Suc j)) a)"
      then have kne: "known_msgs_acc (f j) a \<noteq> known_msgs_acc (f (Suc j)) a"
        using False by force
      have "Next (f j) (f (Suc j))"
        by (metis False Spec.elims(2) \<open>m \<in> set (known_msgs_acc (f (Suc j)) a)\<close> assms(1))
      then have "\<not> (ProposerSendAction (f j) (f (Suc j)))"
        by (metis False ProposerSendAction.elims(2) Send1a.elims(2) \<open>m \<in> set (known_msgs_acc (f (Suc j)) a)\<close> ext_inject surjective update_convs(1))
      have "\<forall> ln m. \<not> (LearnerRecv ln m (f j) (f (Suc j)))"
        by (smt (verit, ccfv_SIG) False LearnerRecv.simps \<open>m \<in> set (known_msgs_acc (f (Suc j)) a)\<close> ext_inject surjective update_convs(3))
      have "\<forall> ln blt val. \<not> (LearnerDecide ln blt val (f j) (f (Suc j)))"
        using False \<open>m \<in> set (known_msgs_acc (f (Suc j)) a)\<close> by force
      then have "\<forall>a. \<not> (LearnerProcessAction (f j) (f (Suc j)))"
        by (meson LearnerAction.elims(2) LearnerProcessAction.elims(1) \<open>\<forall>ln m. \<not> LearnerRecv ln m (f j) (f (Suc j))\<close>)
      have "\<forall>a. \<not> (FakeSend1b a (f j) (f (Suc j)))"
        by (metis FakeSend1b.elims(1) False \<open>m \<in> set (known_msgs_acc (f (Suc j)) a)\<close> ext_inject surjective update_convs(1))
      have "\<forall>a. \<not> (FakeSend2a a (f j) (f (Suc j)))"
        by (metis FakeSend2a.simps False \<open>m \<in> set (known_msgs_acc (f (Suc j)) a)\<close> ext_inject surjective update_convs(1))
      then have "\<not> (FakeAcceptorAction (f j) (f (Suc j)))"
        using FakeAcceptorAction.simps \<open>\<forall>a. \<not> FakeSend1b a (f j) (f (Suc j))\<close> by presburger
      then have "AcceptorProcessAction (f j) (f (Suc j))"
        by (meson LearnerAction.elims(2) LearnerProcessAction.elims(2) Next.simps \<open>Next (f j) (f (Suc j))\<close> \<open>\<forall>ln blt val. \<not> LearnerDecide ln blt val (f j) (f (Suc j))\<close> \<open>\<forall>ln m. \<not> LearnerRecv ln m (f j) (f (Suc j))\<close> \<open>\<not> ProposerSendAction (f j) (f (Suc j))\<close>)
      have "\<forall> A m. a \<noteq> A \<longrightarrow> \<not> (Process1a A m (f j) (f (Suc j)))"
        by (metis False Process1a.elims(2) Store_acc.elims(2) \<open>m \<in> set (known_msgs_acc (f (Suc j)) a)\<close>)
      have "\<forall> A m. a \<noteq> A \<longrightarrow> \<not> (Process1b A m (f j) (f (Suc j)))"
        by (metis False Process1b.elims(2) Store_acc.elims(2) \<open>m \<in> set (known_msgs_acc (f (Suc j)) a)\<close>)
      have "\<forall> a. \<not> (Process1bLearnerLoopDone a (f j) (f (Suc j)))"
        using False \<open>m \<in> set (known_msgs_acc (f (Suc j)) a)\<close> by force
      have "\<forall> ln. \<not> (Process1bLearnerLoopStep a ln (f j) (f (Suc j)))"
        by (smt (verit) False MessageType.distinct(5) Process1bLearnerLoopStep.elims(2) Store_acc.elims(2) \<open>m \<in> set (known_msgs_acc (f (Suc j)) a)\<close> assms(3) set_ConsD type.simps(3))
      then have "\<forall> A. a \<noteq> A \<longrightarrow> \<not> AcceptorAction A (f j) (f (Suc j))"
      proof -
        { fix aa :: Acceptor
          have "known_msgs_acc (f (Suc j)) \<noteq> known_msgs_acc (f j) \<and> known_msgs_acc (f (Suc j)) a \<noteq> known_msgs_acc (f j) a"
            using False \<open>m \<in> set (known_msgs_acc (f (Suc j)) a)\<close> by fastforce
          then have "aa = a \<or> \<not> AcceptorAction aa (f j) (f (Suc j))"
            by (metis (full_types) AcceptorAction.elims(2) Process1bLearnerLoop.elims(2) Process1bLearnerLoopStep.elims(2) Store_acc.elims(2) \<open>\<forall>A m. a \<noteq> A \<longrightarrow> \<not> Process1a A m (f j) (f (Suc j))\<close> \<open>\<forall>A m. a \<noteq> A \<longrightarrow> \<not> Process1b A m (f j) (f (Suc j))\<close> \<open>\<forall>a. \<not> Process1bLearnerLoopDone a (f j) (f (Suc j))\<close>) }
        then show ?thesis
          by (metis (no_types))
      qed
      then have "AcceptorAction a (f j) (f (Suc j))"
        by (metis AcceptorProcessAction.simps \<open>AcceptorProcessAction (f j) (f (Suc j))\<close>)
      have "\<forall>m. \<not> (Process1a a m (f j) (f (Suc j)))"
        by (metis False MessageType.distinct(1) Process1a.elims(2) Store_acc.elims(2) \<open>m \<in> set (known_msgs_acc (f (Suc j)) a)\<close> assms(3) set_ConsD)
      have "\<forall> M. m \<noteq> M \<longrightarrow> \<not> (Process1b a M (f j) (f (Suc j)))"
        unfolding Process1b.simps
        by (metis False Store_acc.elims(2) \<open>m \<in> set (known_msgs_acc (f (Suc j)) a)\<close> set_ConsD)
      then have "Process1b a m (f j) (f (Suc j))"
        by (metis AcceptorAction.elims(2) Process1bLearnerLoop.elims(2) \<open>AcceptorAction a (f j) (f (Suc j))\<close> \<open>\<forall>a. \<not> Process1bLearnerLoopDone a (f j) (f (Suc j))\<close> \<open>\<forall>ln. \<not> Process1bLearnerLoopStep a ln (f j) (f (Suc j))\<close> \<open>\<forall>m. \<not> Process1a a m (f j) (f (Suc j))\<close>)
      then show "(\<exists>k. i \<le> k \<and> k < Suc j \<and> 
              m \<notin> set (known_msgs_acc (f k) a)
            \<and> Process1b a m (f k) (f (1 + k)))"
        by (metis False \<open>i < Suc j\<close> less_Suc_eq less_Suc_eq_le plus_1_eq_Suc)
    qed
  qed
qed

fun step_1a_invariant_1 :: "Acceptor set \<Rightarrow> Ballot \<Rightarrow> State \<Rightarrow> bool" where
  "step_1a_invariant_1 Q b st = (\<forall>a \<in> Q. \<forall> mb :: Ballot. MaxBal st a mb \<longrightarrow> mb \<le> b)"
fun step_1a_invariant_4 :: "Acceptor set \<Rightarrow> Ballot \<Rightarrow> State \<Rightarrow> bool" where
  "step_1a_invariant_4 Q b st = 
    (\<forall>a \<in> Q. \<not> (\<exists>M \<in> set (msgs st). M \<noteq> M1a b \<and> Recv_acc st a M \<and> type M = T1a))"
fun step_1a_invariant_5 :: "Acceptor set \<Rightarrow> Ballot \<Rightarrow> State \<Rightarrow> bool" where
  "step_1a_invariant_5 Q b st = 
    (\<forall>a\<in>Q. (\<forall>M\<in>set (msgs st).
      (type M = T1b \<or> type M = T2a) \<longrightarrow> (\<exists>mb. B M mb \<and> b \<ge> mb)))"
fun step_1a_invariant_6 :: "Acceptor \<Rightarrow> Ballot \<Rightarrow> State \<Rightarrow> bool" where
  "step_1a_invariant_6 a b st = (\<forall> mb :: Ballot. MaxBal st a mb \<longrightarrow> mb < b)"
fun step_1a_invariants :: "Acceptor \<Rightarrow> Acceptor set \<Rightarrow> Ballot \<Rightarrow> State \<Rightarrow> bool" where
  "step_1a_invariants a Q b st = (
      step_1a_invariant_1 Q b st \<and>
      step_1a_invariant_4 Q b st \<and>
      step_1a_invariant_5 Q b st \<and>
      step_1a_invariant_6 a b st
    )"

lemma step_1a_invariants:
  assumes "Spec f"
      and "M1a b \<in> set (msgs (f i))"
      and "is_safe a"
      and "a \<in> Q"
      and "M1a b \<notin> set (known_msgs_acc (f i) a)"

      and "step_1a_invariants a Q b (f i)"

    shows "i < j \<and> M1a b \<notin> set (known_msgs_acc (f j) a) \<and>
           (\<forall> k. i \<le> k \<and> k \<le> j \<longrightarrow> \<not> ProposerSendAction (f k) (f (1 + k))
                                  \<and> \<not> FakeAcceptorAction (f k) (f (1 + k))
                                  \<and> (\<forall>a. a \<notin> Q \<longrightarrow> \<not> AcceptorAction a (f k) (f (1 + k))))
           \<longrightarrow> (\<forall> k. i \<le> k \<and> k \<le> j \<longrightarrow> step_1a_invariants a Q b (f k))"
proof (induction j)
  case 0
  then show ?case
    by fastforce
next
  case (Suc j)
  assume ih:"i < j \<and> M1a b \<notin> set (known_msgs_acc (f j) a) \<and>
           (\<forall> k. i \<le> k \<and> k \<le> j \<longrightarrow> \<not> ProposerSendAction (f k) (f (1 + k))
                                  \<and> \<not> FakeAcceptorAction (f k) (f (1 + k))
                                  \<and> (\<forall>a. a \<notin> Q \<longrightarrow> \<not> AcceptorAction a (f k) (f (1 + k))))
           \<longrightarrow> (\<forall> k. i \<le> k \<and> k \<le> j \<longrightarrow> step_1a_invariants a Q b (f k))"
  then show ?case
  proof (clarify)
    fix k
    assume "i < Suc j"
       and "M1a b \<notin> set (known_msgs_acc (f (Suc j)) a)"
       and block: "\<forall>k. i \<le> k \<and> k \<le> Suc j \<longrightarrow>
                     \<not> ProposerSendAction (f k) (f (1 + k)) \<and>
                     \<not> FakeAcceptorAction (f k) (f (1 + k)) \<and>
                     (\<forall>a. a \<notin> Q \<longrightarrow> \<not> AcceptorAction a (f k) (f (1 + k)))"
       and "i \<le> k"
       and "k \<le> Suc j"
    have "M1a b \<notin> set (known_msgs_acc (f j) a)"
      by (metis \<open>M1a b \<notin> set (known_msgs_acc (f (Suc j)) a)\<close> assms(1) known_msgs_acc_preserved le_add2 plus_1_eq_Suc)
    have ihp: "(\<forall> k. i \<le> k \<and> k \<le> j \<longrightarrow> \<not> ProposerSendAction (f k) (f (1 + k))
                                  \<and> \<not> FakeAcceptorAction (f k) (f (1 + k))
                                  \<and> (\<forall>a. a \<notin> Q \<longrightarrow> \<not> AcceptorAction a (f k) (f (1 + k))))"
      using \<open>i \<le> k\<close> \<open>k \<le> Suc j\<close> block le_Suc_eq by blast
    show "step_1a_invariants a Q b (f k)"
    proof (cases "i = k")
      case True
      then show ?thesis
        using \<open>step_1a_invariants a Q b (f i)\<close> by fastforce
    next
      case False
      have "i < k"
        by (simp add: False \<open>i \<le> k\<close> nat_less_le)
      then have ihu: "step_1a_invariants a Q b (f j)"
        by (metis \<open>M1a b \<notin> set (known_msgs_acc (f j) a)\<close> \<open>i < Suc j\<close> assms(6) ih ihp less_Suc_eq less_or_eq_imp_le)
      then show ?thesis
      proof (cases "k \<noteq> Suc j")
        case True
        then show ?thesis
          by (metis False \<open>M1a b \<notin> set (known_msgs_acc (f j) a)\<close> \<open>i < Suc j\<close> \<open>i \<le> k\<close> \<open>k \<le> Suc j\<close> antisym ih ihp le_SucE less_antisym)
      next
        case False
        then have "k = Suc j"
          by simp
        have ihu1: "step_1a_invariant_1 Q b (f j)"
          using ihu step_1a_invariants.simps by blast
        have ihu4: "step_1a_invariant_4 Q b (f j)"
          using ihu step_1a_invariants.simps by blast
        have ihu5: "step_1a_invariant_5 Q b (f j)"
          using ihu step_1a_invariants.simps by blast
        have ihu6: "step_1a_invariant_6 a b (f j)"
          using ihu step_1a_invariants.simps by blast

        have r1: "\<forall>a \<in> Q. known_msgs_acc (f j) a = known_msgs_acc (f (Suc j)) a \<longrightarrow> (\<forall> mb :: Ballot. MaxBal (f k) a mb \<longrightarrow> mb \<le> b)"
          using ihu1 False by auto
        have r4: "(\<forall>m \<in> set (msgs (f (Suc j))). type m = T1a \<longrightarrow> m \<in> set (msgs (f j))) \<longrightarrow> step_1a_invariant_4 Q b (f k)"
          unfolding step_1a_invariant_4.simps
        proof (clarify)
          fix a M
          assume "\<forall>m\<in>set (msgs (f (Suc j))). type m = T1a \<longrightarrow> m \<in> set (msgs (f j))"
             and "a \<in> Q"
             and "M \<in> set (msgs (f k))"
             and "M \<noteq> M1a b"
             and "Recv_acc (f k) a M"
             and "type M = T1a"
          then show False
          proof (cases "M \<notin> set (known_msgs_acc (f k) a)")
            case True
            then have "M \<notin> set (known_msgs_acc (f j) a)"
              by (metis False assms(1) known_msgs_acc_preserved le_add2 plus_1_eq_Suc)
            then have "Recv_acc (f j) a M"
              by (metis MessageType.distinct(1) MessageType.distinct(3) Proper_acc.elims(1) Recv_acc.elims(2) Recv_acc.elims(3) Wellformed_Constant \<open>Recv_acc (f k) a M\<close> \<open>type M = T1a\<close> assms(1) empty_iff ref.simps(1) type.elims)
            then show ?thesis
              using False \<open>M \<in> set (msgs (f k))\<close> \<open>M \<noteq> M1a b\<close> \<open>\<forall>m\<in>set (msgs (f (Suc j))). type m = T1a \<longrightarrow> m \<in> set (msgs (f j))\<close> \<open>a \<in> Q\<close> \<open>type M = T1a\<close> ihu4 step_1a_invariant_4.simps by blast
          next
            case False
            then show ?thesis
              using Recv_acc.elims(2) \<open>Recv_acc (f k) a M\<close> by blast
          qed
        qed
        have r5: "msgs (f (Suc j)) = msgs (f j) \<and> (\<forall>a \<in> Q. known_msgs_acc (f j) a = known_msgs_acc (f (Suc j)) a) \<longrightarrow> step_1a_invariant_5 Q b (f k)"
          using ihu5
          unfolding step_1a_invariant_5.simps
          by (smt (verit) False MaxBal.simps Proper_acc.elims(1) Recv_acc.simps Wellformed_Constant assms(1))
        have r6: "known_msgs_acc (f j) a = known_msgs_acc (f (Suc j)) a \<longrightarrow> step_1a_invariant_6 a b (f k)"
          using ihu6
          unfolding step_1a_invariant_6.simps
          by (smt (verit) False MaxBal.simps Proper_acc.elims(1) Recv_acc.simps Wellformed_Constant assms(1))
      show ?thesis
      proof (cases "f j = f (Suc j)")
        case True
        then show ?thesis
          using False ihu by presburger
      next
        case False
        have "Next (f j) (f (Suc j))"
          using False Spec.simps assms(1) by blast
        have "\<not> (ProposerSendAction (f j) (f (Suc j)))"
          by (metis Suc_eq_plus1_left \<open>i < Suc j\<close> ihp le_refl less_Suc_eq_le)
        have "\<not> (FakeAcceptorAction (f j) (f (Suc j)))"
          by (metis Suc_eq_plus1_left \<open>i < Suc j\<close> ihp le_refl less_Suc_eq_le)
        have "\<forall>m \<in> set (msgs (f j)). \<not> (Process1a a m (f j) (f (Suc j)))"
          by (metis Process1a.elims(2) Process1a_Req_known_msgs \<open>M1a b \<notin> set (known_msgs_acc (f (Suc j)) a)\<close> assms(1) assms(4) diff_Suc_1 ihu4 step_1a_invariant_4.elims(2))
        have "\<forall>a. a \<notin> Q \<longrightarrow> (\<forall>m. \<not> (Process1a a m (f j) (f (Suc j))))"
          by (metis Process1a_Next_Implies_AcceptorAction \<open>Next (f j) (f (Suc j))\<close> \<open>i < Suc j\<close> block le_add2 less_Suc_eq_le plus_1_eq_Suc)
        have "\<forall>a. a \<notin> Q \<longrightarrow> (\<forall>m. \<not> (Process1b a m (f j) (f (Suc j))))"
          by (metis Process1b_Next_Implies_AcceptorAction \<open>Next (f j) (f (Suc j))\<close> \<open>i < Suc j\<close> block le_add2 less_Suc_eq_le plus_1_eq_Suc)
        have "\<forall>a. a \<notin> Q \<longrightarrow> (\<forall>m. \<not> (Process1bLearnerLoopStep a m (f j) (f (Suc j))))"
          by (metis False Process1bLearnerLoopStep_Next_Implies_AcceptorAction Suc_eq_plus1_left \<open>Next (f j) (f (Suc j))\<close> \<open>i < k\<close> \<open>k = Suc j\<close> ihp less_Suc_eq_le order_refl)
        have "\<forall>a. a \<notin> Q \<longrightarrow> (\<forall>m. \<not> (Process1bLearnerLoopDone a (f j) (f (Suc j))))"
          by (metis False Process1bLearnerLoopDone_Next_Implies_AcceptorAction Suc_eq_plus1 \<open>Next (f j) (f (Suc j))\<close> \<open>i < k\<close> \<open>k = Suc j\<close> add.commute ihp le_less_Suc_eq nat_le_linear)
        then show ?thesis
        proof (cases "LearnerProcessAction (f j) (f (Suc j))")
          case True
          then show ?thesis
            unfolding LearnerProcessAction.simps LearnerAction.simps
          proof (clarify)
            fix ln
            assume "(\<exists>m\<in>set (msgs (f j)). LearnerRecv ln m (f j) (f (Suc j))) \<or>
                    (\<exists>blt val. LearnerDecide ln blt val (f j) (f (Suc j)))"
            then show ?thesis
            proof (elim disjE)
              assume "\<exists>m\<in>set (msgs (f j)). LearnerRecv ln m (f j) (f (Suc j))"
              have "msgs (f j) = msgs (f (Suc j))"
                using \<open>\<exists>m\<in>set (msgs (f j)). LearnerRecv ln m (f j) (f (Suc j))\<close> by fastforce
              have "\<forall>a \<in> Q. known_msgs_acc (f j) a = known_msgs_acc (f (Suc j)) a"
                by (metis (no_types, lifting) LearnerRecv.elims(2) \<open>\<exists>m\<in>set (msgs (f j)). LearnerRecv ln m (f j) (f (Suc j))\<close> ext_inject surjective update_convs(3))
              have c1: "step_1a_invariant_1 Q b (f k)"
                unfolding step_1a_invariant_1.simps
                using \<open>\<forall>a\<in>Q. known_msgs_acc (f j) a = known_msgs_acc (f (Suc j)) a\<close> r1 by blast
              have c4: "step_1a_invariant_4 Q b (f k)"
                unfolding step_1a_invariant_4.simps
                by (metis \<open>msgs (f j) = msgs (f (Suc j))\<close> r4 step_1a_invariant_4.elims(2))
              have c5: "step_1a_invariant_5 Q b (f k)"
                unfolding step_1a_invariant_5.simps
                by (metis \<open>\<forall>a\<in>Q. known_msgs_acc (f j) a = known_msgs_acc (f (Suc j)) a\<close> \<open>msgs (f j) = msgs (f (Suc j))\<close> r5 step_1a_invariant_5.elims(2))
              have c6: "step_1a_invariant_6 a b (f k)"
                unfolding step_1a_invariant_6.simps
                using \<open>\<forall>a\<in>Q. known_msgs_acc (f j) a = known_msgs_acc (f (Suc j)) a\<close> assms(4) r6 step_1a_invariant_6.simps by blast
              then show ?thesis
                using c1 c4 c5 step_1a_invariants.simps by blast
            next
              assume "\<exists>blt val. LearnerDecide ln blt val (f j) (f (Suc j))"
              have "msgs (f j) = msgs (f (Suc j))"
                using \<open>\<exists>blt val. LearnerDecide ln blt val (f j) (f (Suc j))\<close> by force
              have "\<forall>a \<in> Q. known_msgs_acc (f j) a = known_msgs_acc (f (Suc j)) a"
                using \<open>\<exists>blt val. LearnerDecide ln blt val (f j) (f (Suc j))\<close> by fastforce
              have "step_1a_invariant_1 Q b (f k)"
                unfolding step_1a_invariant_1.simps
                using \<open>\<forall>a\<in>Q. known_msgs_acc (f j) a = known_msgs_acc (f (Suc j)) a\<close> r1 by blast
              have "step_1a_invariant_4 Q b (f k)"
                unfolding step_1a_invariant_4.simps
                by (metis \<open>msgs (f j) = msgs (f (Suc j))\<close> r4 step_1a_invariant_4.elims(2))
              have "step_1a_invariant_5 Q b (f k)"
                unfolding step_1a_invariant_5.simps
                by (metis \<open>\<forall>a\<in>Q. known_msgs_acc (f j) a = known_msgs_acc (f (Suc j)) a\<close> \<open>msgs (f j) = msgs (f (Suc j))\<close> r5 step_1a_invariant_5.elims(2))
              then show ?thesis
                using \<open>\<forall>a\<in>Q. known_msgs_acc (f j) a = known_msgs_acc (f (Suc j)) a\<close> \<open>step_1a_invariant_1 Q b (f k)\<close> \<open>step_1a_invariant_4 Q b (f k)\<close> assms(4) r6 step_1a_invariants.simps by blast
            qed
          qed
        next
          case False
          have "AcceptorProcessAction (f j) (f (Suc j))"
            using False Next.elims(2) \<open>Next (f j) (f (Suc j))\<close> \<open>\<not> FakeAcceptorAction (f j) (f (Suc j))\<close> \<open>\<not> ProposerSendAction (f j) (f (Suc j))\<close> by blast
          then have "(\<exists>A :: Acceptor. is_safe A
                                    \<and> queued_msg (f j) A = None 
                                    \<and> (\<exists>m \<in> set (msgs (f j)). Process1a A m (f j) (f (Suc j)))) \<or>
                      (\<exists>A :: Acceptor. is_safe A
                                    \<and> queued_msg (f j) A = None 
                                    \<and> (\<exists>m \<in> set (msgs (f j)). Process1b A m (f j) (f (Suc j)))) \<or>
                      (\<exists>A :: Acceptor. is_safe A
                                    \<and> queued_msg (f j) A \<noteq> None 
                                    \<and> Process1b A (the (queued_msg (f j) A)) (f j) (f (Suc j))) \<or>
                      (\<exists>A :: Acceptor. is_safe A
                                    \<and> two_a_lrn_loop (f j) A 
                                    \<and> (\<exists>l :: Learner. Process1bLearnerLoopStep A l (f j) (f (Suc j)))) \<or>
                      (\<exists>A :: Acceptor. is_safe A
                                    \<and> two_a_lrn_loop (f j) A 
                                    \<and> Process1bLearnerLoopDone A (f j) (f (Suc j)))"
            using Acceptor_split by blast
          then show ?thesis
          proof (elim disjE)
            assume "\<exists>A. is_safe A \<and>
              queued_msg (f j) A = None \<and>
              (\<exists>m\<in>set (msgs (f j)).
                  Process1a A m (f j) (f (Suc j)))"
            then show ?thesis
            proof (clarify)
              fix A m
              assume "is_safe A"
                 and "queued_msg (f j) A = None"
                 and "m \<in> set (msgs (f j))"
                 and "Process1a A m (f j) (f (Suc j))"
              have "type m = T1a"
                by (meson Process1a.elims(2) \<open>Process1a A m (f j) (f (Suc j))\<close>)
              then have "m = M1a b"
                by (meson Process1a.elims(2) \<open>Process1a A m (f j) (f (Suc j))\<close> \<open>\<forall>a. a \<notin> Q \<longrightarrow> (\<forall>m. \<not> Process1a a m (f j) (f (Suc j)))\<close> \<open>m \<in> set (msgs (f j))\<close> ihu4 step_1a_invariant_4.elims(2))
              have "A \<noteq> a"
                using \<open>Process1a A m (f j) (f (Suc j))\<close> \<open>\<forall>m\<in>set (msgs (f j)). \<not> Process1a a m (f j) (f (Suc j))\<close> \<open>m \<in> set (msgs (f j))\<close> by fastforce
              have "A \<in> Q"
                using \<open>Process1a A m (f j) (f (Suc j))\<close> \<open>\<forall>a. a \<notin> Q \<longrightarrow> (\<forall>m. \<not> Process1a a m (f j) (f (Suc j)))\<close> by blast
              have "\<forall>a. a \<noteq> A \<longrightarrow> known_msgs_acc (f j) a = known_msgs_acc (f (Suc j)) a"
                by (metis Process1a.elims(2) Store_acc.elims(2) \<open>Process1a A m (f j) (f (Suc j))\<close>)
              have "M1a b # known_msgs_acc (f j) A = known_msgs_acc (f (Suc j)) A"
                by (metis Process1a.elims(2) Store_acc.elims(2) \<open>Process1a A m (f j) (f (Suc j))\<close> \<open>m = M1a b\<close>)
              then have "M1a b # known_msgs_acc (f j) A = known_msgs_acc (f k) A"
                using \<open>k = Suc j\<close> by fastforce
              have "B (M1a b) b"
                by simp
              have "\<exists>m\<in>set (known_msgs_acc (f k) A). B m b"
                by (metis \<open>B (M1a b) b\<close> \<open>M1a b # known_msgs_acc (f j) A = known_msgs_acc (f (Suc j)) A\<close> \<open>k = Suc j\<close> list.set_intros(1))
              have "\<forall>b2. B (M1a b) b2 \<longrightarrow> b2 \<le> b"
                unfolding B.simps Tran.simps
                by fastforce
              then have "\<forall>x\<in>set (known_msgs_acc (f k) A). \<forall>b2. B x b2 \<longrightarrow> b2 \<le> b"
                using ihu1 
                unfolding step_1a_invariant_1.simps
                by (metis \<open>A \<in> Q\<close> \<open>M1a b # known_msgs_acc (f j) A = known_msgs_acc (f (Suc j)) A\<close> \<open>k = Suc j\<close> dual_order.trans maxbal_absence not_le_imp_less set_ConsD)
              have "B (M1a b) b"
                by simp
              have "\<exists>m\<in>set (known_msgs_acc (f k) A). B m b"
                by (metis \<open>B (M1a b) b\<close> \<open>M1a b # known_msgs_acc (f j) A = known_msgs_acc (f (Suc j)) A\<close> \<open>k = Suc j\<close> list.set_intros(1))
              have "\<forall>b2. B (M1a b) b2 \<longrightarrow> b2 \<le> b"
                unfolding B.simps Tran.simps
                by fastforce
              then have "\<forall>x\<in>set (known_msgs_acc (f k) A). \<forall>b2. B x b2 \<longrightarrow> b2 \<le> b"
                using ihu1 
                unfolding step_1a_invariant_1.simps
                using \<open>\<forall>x\<in>set (known_msgs_acc (f k) A). \<forall>b2. B x b2 \<longrightarrow> b2 \<le> b\<close> by fastforce
              have c1: "step_1a_invariant_1 Q b (f k)"
                unfolding step_1a_invariant_1.simps
              proof (clarify)
                fix a mb
                assume "a \<in> Q"
                   and "MaxBal (f k) a mb"
                then show "mb \<le> b"
                proof (cases "a = A")
                  case True
                  then show ?thesis
                    using MaxBal.simps \<open>MaxBal (f k) a mb\<close> \<open>\<forall>x\<in>set (known_msgs_acc (f k) A). \<forall>b2. B x b2 \<longrightarrow> b2 \<le> b\<close> by blast
                next
                  case False
                  then show ?thesis
                    using \<open>MaxBal (f k) a mb\<close> \<open>\<forall>a. a \<noteq> A \<longrightarrow> known_msgs_acc (f j) a = known_msgs_acc (f (Suc j)) a\<close> \<open>a \<in> Q\<close> r1 by blast
                qed
              qed
              have c4: "step_1a_invariant_4 Q b (f k)"
                by (smt (verit) MessageType.distinct(1) MessageType.distinct(3) PreMessage.distinct(1) Process1a.elims(2) Send.elims(2) \<open>\<exists>A. is_safe A \<and> queued_msg (f j) A = None \<and> (\<exists>m\<in>set (msgs (f j)). Process1a A m (f j) (f (Suc j)))\<close> r4 set_ConsD type.elims)

              have "(\<forall>ba. (\<forall>m \<in> set (recent_msgs (f j) A). B m ba \<longrightarrow> ba \<le> b))"
                by (metis RecentMsgsSpec.elims(2) RecentMsgsSpecResult \<open>\<forall>x\<in>set (known_msgs_acc (f k) A). \<forall>b2. B x b2 \<longrightarrow> b2 \<le> b\<close> \<open>is_safe A\<close> \<open>k = Suc j\<close> assms(1) known_msgs_acc_preserved less_Suc_eq_le nless_le order_refl subsetD)
              then have "(\<forall>ba. M1a ba \<in> \<Union> (set (map Tran (recent_msgs (f j) A))) \<longrightarrow> ba \<le> b)"
                by (smt (verit, del_insts) B_1a KnownMsgs_accSpec.elims(2) KnownMsgs_accSpecResult RecentMsgsSpec.elims(2) RecentMsgsSpecResult \<open>M1a b # known_msgs_acc (f j) A = known_msgs_acc (f (Suc j)) A\<close> \<open>\<forall>x\<in>set (known_msgs_acc (f k) A). \<forall>b2. B x b2 \<longrightarrow> b2 \<le> b\<close> \<open>is_safe A\<close> \<open>k = Suc j\<close> assms(1) bal.simps(1) imageE in_mono list.set_map mem_simps(9) set_subset_Cons type.simps(1))
              then have "B (M1b A (m # recent_msgs (f j) A)) b"
                by (simp add: \<open>m = M1a b\<close>)

              have c5: "step_1a_invariant_5 Q b (f k)"
                unfolding step_1a_invariant_5.simps
              proof (clarify)
                fix a M
                assume "a \<in> Q"
                   and "M \<in> set (msgs (f k))"
                   and "type M = T1b \<or> type M = T2a"
                then show "\<exists>mb. B M mb \<and> mb \<le> b"
                proof (cases "WellFormed (f j) (M1b A (m # recent_msgs (f j) A))")
                  case True
                  then show ?thesis
                    by (smt (verit) Process1a.elims(2) Send.elims(2) \<open>B (M1a b) b\<close> \<open>B (M1b A (m # recent_msgs (f j) A)) b\<close> \<open>M \<in> set (msgs (f k))\<close> \<open>Process1a A m (f j) (f (Suc j))\<close> \<open>\<forall>b2. B (M1a b) b2 \<longrightarrow> b2 \<le> b\<close> \<open>a \<in> Q\<close> \<open>k = Suc j\<close> \<open>type M = T1b \<or> type M = T2a\<close> ihu5 set_ConsD step_1a_invariant_5.elims(2))
                next
                  case False
                  have "M \<in> set (msgs (f j))"
                    by (metis False Process1a.elims(2) \<open>M \<in> set (msgs (f k))\<close> \<open>Process1a A m (f j) (f (Suc j))\<close> \<open>k = Suc j\<close>)
                  then show ?thesis
                    by (meson \<open>a \<in> Q\<close> \<open>type M = T1b \<or> type M = T2a\<close> ihu5 step_1a_invariant_5.elims(2))
                qed
              qed
              
              have c6: "step_1a_invariant_6 a b (f k)"
                using \<open>A \<noteq> a\<close> \<open>\<forall>a. a \<noteq> A \<longrightarrow> known_msgs_acc (f j) a = known_msgs_acc (f (Suc j)) a\<close> r6 by presburger

              show ?thesis
                using c1 c4 c5 c6 step_1a_invariants.simps by presburger
            qed
          next
            assume "\<exists>A. is_safe A \<and>
                        queued_msg (f j) A = None \<and>
                        (\<exists>m\<in>set (msgs (f j)). Process1b A m (f j) (f (Suc j)))"
            then show ?thesis
            proof (clarify)
              fix A m
              assume "is_safe A"
                 and "queued_msg (f j) A = None"
                 and "m\<in>set (msgs (f j))"
                 and "Process1b A m (f j) (f (Suc j))"

              have c4: "step_1a_invariant_4 Q b (f k)"
                by (smt (verit) Process1b.simps \<open>Process1b A m (f j) (f (Suc j))\<close> r4)

              have "Recv_acc (f j) A m"
                using Process1b.simps \<open>Process1b A m (f j) (f (Suc j))\<close> by blast
              have "type m = T1b"
                using Process1b.simps \<open>Process1b A m (f j) (f (Suc j))\<close> by blast
              have "A \<in> Q"
                using \<open>Process1b A m (f j) (f (Suc j))\<close> \<open>\<forall>a. a \<notin> Q \<longrightarrow> (\<forall>m. \<not> Process1b a m (f j) (f (Suc j)))\<close> by blast
              have "\<forall>a. a \<noteq> A \<longrightarrow> known_msgs_acc (f j) a = known_msgs_acc (f (Suc j)) a"
                by (metis Process1b.elims(2) Store_acc.elims(2) \<open>Process1b A m (f j) (f (Suc j))\<close>)
              have "m # known_msgs_acc (f j) A = known_msgs_acc (f (Suc j)) A"
                by (metis Process1b.elims(2) Store_acc.elims(2) \<open>Process1b A m (f j) (f (Suc j))\<close>)
              then have "m # known_msgs_acc (f j) A = known_msgs_acc (f k) A"
                using \<open>k = Suc j\<close> by fastforce
              have "B (M1a b) b"
                by simp
              have "\<forall>mb. B m mb \<longrightarrow> mb \<le> b"
                using ihu5
                by (metis B.simps \<open>m \<in> set (msgs (f j))\<close> \<open>type m = T1b\<close> assms(4) nle_le step_1a_invariant_5.elims(2))
              then have "\<forall>x\<in>set (known_msgs_acc (f k) A). \<forall>b2. B x b2 \<longrightarrow> b2 \<le> b"
                using ihu1 
                unfolding step_1a_invariant_1.simps
                by (metis \<open>A \<in> Q\<close> \<open>m # known_msgs_acc (f j) A = known_msgs_acc (f (Suc j)) A\<close> \<open>k = Suc j\<close> dual_order.trans maxbal_absence not_le_imp_less set_ConsD)
              have "(\<forall>ba. (\<forall>m \<in> set (recent_msgs (f j) A). B m ba \<longrightarrow> ba \<le> b))"
                by (metis RecentMsgsSpec.elims(2) RecentMsgsSpecResult \<open>\<forall>x\<in>set (known_msgs_acc (f k) A). \<forall>b2. B x b2 \<longrightarrow> b2 \<le> b\<close> \<open>is_safe A\<close> \<open>k = Suc j\<close> assms(1) known_msgs_acc_preserved less_Suc_eq_le nless_le order_refl subsetD)
              then have "(\<forall>ba. M1a ba \<in> \<Union> (set (map Tran (recent_msgs (f j) A))) \<longrightarrow> ba \<le> b)"
                by (smt (verit, del_insts) B_1a KnownMsgs_accSpec.elims(2) KnownMsgs_accSpecResult RecentMsgsSpec.elims(2) RecentMsgsSpecResult \<open>\<forall>x\<in>set (known_msgs_acc (f k) A). \<forall>b2. B x b2 \<longrightarrow> b2 \<le> b\<close> \<open>is_safe A\<close> \<open>k = Suc j\<close> assms(1) bal.simps(1) imageE in_mono known_msgs_acc_preserved le_add2 list.set_map mem_simps(9) plus_1_eq_Suc type.simps(1))
              then have "\<forall>l. \<forall>mb. B (M2a l A (m # recent_msgs (f j) A)) mb \<longrightarrow> mb \<le> b"
                using \<open>\<forall>mb. B m mb \<longrightarrow> mb \<le> b\<close> by auto

              have c1: "step_1a_invariant_1 Q b (f k)"
                unfolding step_1a_invariant_1.simps
                by (metis MaxBal.elims(2) \<open>\<forall>a. a \<noteq> A \<longrightarrow> known_msgs_acc (f j) a = known_msgs_acc (f (Suc j)) a\<close> \<open>\<forall>x\<in>set (known_msgs_acc (f k) A). \<forall>b2. B x b2 \<longrightarrow> b2 \<le> b\<close> r1)
              have c5: "step_1a_invariant_5 Q b (f k)"
                unfolding step_1a_invariant_5.simps
              proof (clarify)
                fix a M
                assume "a \<in> Q"
                   and "M \<in> set (msgs (f k))"
                   and "type M = T1b \<or> type M = T2a"
                have "M \<in> set (msgs (f j))"
                  using \<open>M \<in> set (msgs (f k))\<close> \<open>Process1b A m (f j) (f (Suc j))\<close> \<open>k = Suc j\<close> by force
                then show "\<exists>mb. B M mb \<and> mb \<le> b"
                  using ihu5 \<open>a \<in> Q\<close> \<open>type M = T1b \<or> type M = T2a\<close> by auto
              qed

              have "\<forall>m1 \<in> set (known_msgs_acc (f k) a). m1 = m \<or> m1 \<in> set (known_msgs_acc (f j) a)"
                by (metis \<open>\<forall>a. a \<noteq> A \<longrightarrow> known_msgs_acc (f j) a = known_msgs_acc (f (Suc j)) a\<close> \<open>k = Suc j\<close> \<open>m # known_msgs_acc (f j) A = known_msgs_acc (f k) A\<close> set_ConsD)
              then have c6: "step_1a_invariant_6 a b (f k)"
                unfolding step_1a_invariant_6.simps
                by (metis B.elims(2) KnownMsgs_accSpec.elims(2) KnownMsgs_accSpecResult MaxBal.simps \<open>M1a b \<notin> set (known_msgs_acc (f (Suc j)) a)\<close> \<open>k = Suc j\<close> assms(1) assms(3) assms(4) c1 in_mono nless_le step_1a_invariant_1.elims(2))

              show ?thesis
                using c1 c4 c5 c6 step_1a_invariants.simps by presburger
            qed
          next
            assume "\<exists>A. is_safe A \<and>
                      queued_msg (f j) A \<noteq> None \<and>
                      Process1b A (the (queued_msg (f j) A)) (f j) (f (Suc j))"
            then show ?thesis
            proof (clarify)
              fix A m
              assume "is_safe A"
                 and "queued_msg (f j) A = Some m"
                 and "Process1b A (the (queued_msg (f j) A)) (f j) (f (Suc j))"

              have c4: "step_1a_invariant_4 Q b (f k)"
                by (smt (verit) Process1b.simps \<open>Process1b A (the (queued_msg (f j) A)) (f j) (f (Suc j))\<close> r4)

              have "Recv_acc (f j) A m"
                by (metis Enabled.simps Process1b_Enabled \<open>Process1b A (the (queued_msg (f j) A)) (f j) (f (Suc j))\<close> \<open>queued_msg (f j) A = Some m\<close> option.sel)
              have "type m = T1b"
                by (metis Disabled_No_Step Process1b_Enabled \<open>Process1b A (the (queued_msg (f j) A)) (f j) (f (Suc j))\<close> \<open>queued_msg (f j) A = Some m\<close> option.sel)
              have "A \<in> Q"
                using \<open>Process1b A (the (queued_msg (f j) A)) (f j) (f (Suc j))\<close> \<open>\<forall>a. a \<notin> Q \<longrightarrow> (\<forall>m. \<not> Process1b a m (f j) (f (Suc j)))\<close> by blast
              have "\<forall>a. a \<noteq> A \<longrightarrow> known_msgs_acc (f j) a = known_msgs_acc (f (Suc j)) a"
                by (metis Process1b.elims(2) Store_acc.elims(2) \<open>Process1b A (the (queued_msg (f j) A)) (f j) (f (Suc j))\<close>)
              have "m # known_msgs_acc (f j) A = known_msgs_acc (f (Suc j)) A"
                by (metis Process1b.elims(2) Store_acc.elims(2) \<open>Process1b A (the (queued_msg (f j) A)) (f j) (f (Suc j))\<close> \<open>queued_msg (f j) A = Some m\<close> option.sel)
              then have "m # known_msgs_acc (f j) A = known_msgs_acc (f k) A"
                using \<open>k = Suc j\<close> by fastforce
              have "B (M1a b) b"
                by simp
              have "m \<in> set (msgs (f j))"
                by (metis QueuedMsgResult QueuedMsgSpec1.elims(2) \<open>is_safe A\<close> \<open>queued_msg (f j) A = Some m\<close> assms(1) option.discI option.sel)
              have "\<forall>mb. B m mb \<longrightarrow> mb \<le> b"
                using ihu5
                by (metis B.simps \<open>m \<in> set (msgs (f j))\<close> \<open>type m = T1b\<close> assms(4) nle_le step_1a_invariant_5.elims(2))
              then have "\<forall>x\<in>set (known_msgs_acc (f k) A). \<forall>b2. B x b2 \<longrightarrow> b2 \<le> b"
                using ihu1 
                unfolding step_1a_invariant_1.simps
                by (metis \<open>A \<in> Q\<close> \<open>m # known_msgs_acc (f j) A = known_msgs_acc (f (Suc j)) A\<close> \<open>k = Suc j\<close> dual_order.trans maxbal_absence not_le_imp_less set_ConsD)
              have "(\<forall>ba. (\<forall>m \<in> set (recent_msgs (f j) A). B m ba \<longrightarrow> ba \<le> b))"
                by (metis RecentMsgsSpec.elims(2) RecentMsgsSpecResult \<open>\<forall>x\<in>set (known_msgs_acc (f k) A). \<forall>b2. B x b2 \<longrightarrow> b2 \<le> b\<close> \<open>is_safe A\<close> \<open>k = Suc j\<close> assms(1) known_msgs_acc_preserved less_Suc_eq_le nless_le order_refl subsetD)
              then have "(\<forall>ba. M1a ba \<in> \<Union> (set (map Tran (recent_msgs (f j) A))) \<longrightarrow> ba \<le> b)"
                by (smt (verit, del_insts) B_1a KnownMsgs_accSpec.elims(2) KnownMsgs_accSpecResult RecentMsgsSpec.elims(2) RecentMsgsSpecResult \<open>\<forall>x\<in>set (known_msgs_acc (f k) A). \<forall>b2. B x b2 \<longrightarrow> b2 \<le> b\<close> \<open>is_safe A\<close> \<open>k = Suc j\<close> assms(1) bal.simps(1) imageE in_mono known_msgs_acc_preserved le_add2 list.set_map mem_simps(9) plus_1_eq_Suc type.simps(1))
              then have "\<forall>l. \<forall>mb. B (M2a l A (m # recent_msgs (f j) A)) mb \<longrightarrow> mb \<le> b"
                using \<open>\<forall>mb. B m mb \<longrightarrow> mb \<le> b\<close> by auto

              have c1: "step_1a_invariant_1 Q b (f k)"
                unfolding step_1a_invariant_1.simps
                by (metis MaxBal.elims(2) \<open>\<forall>a. a \<noteq> A \<longrightarrow> known_msgs_acc (f j) a = known_msgs_acc (f (Suc j)) a\<close> \<open>\<forall>x\<in>set (known_msgs_acc (f k) A). \<forall>b2. B x b2 \<longrightarrow> b2 \<le> b\<close> r1)
              have c5: "step_1a_invariant_5 Q b (f k)"
                unfolding step_1a_invariant_5.simps
              proof (clarify)
                fix a M
                assume "a \<in> Q"
                   and "M \<in> set (msgs (f k))"
                   and "type M = T1b \<or> type M = T2a"
                have "M \<in> set (msgs (f j))"
                  using \<open>M \<in> set (msgs (f k))\<close> \<open>Process1b A (the (queued_msg (f j) A)) (f j) (f (Suc j))\<close> \<open>k = Suc j\<close> by force
                then show "\<exists>mb. B M mb \<and> mb \<le> b"
                  using ihu5 \<open>a \<in> Q\<close> \<open>type M = T1b \<or> type M = T2a\<close> by auto
              qed

              have "\<forall>m1 \<in> set (known_msgs_acc (f k) a). m1 = m \<or> m1 \<in> set (known_msgs_acc (f j) a)"
                by (metis \<open>\<forall>a. a \<noteq> A \<longrightarrow> known_msgs_acc (f j) a = known_msgs_acc (f (Suc j)) a\<close> \<open>k = Suc j\<close> \<open>m # known_msgs_acc (f j) A = known_msgs_acc (f k) A\<close> set_ConsD)
              then have c6: "step_1a_invariant_6 a b (f k)"
                unfolding step_1a_invariant_6.simps
                by (metis B.elims(2) KnownMsgs_accSpec.elims(2) KnownMsgs_accSpecResult MaxBal.simps \<open>M1a b \<notin> set (known_msgs_acc (f (Suc j)) a)\<close> \<open>k = Suc j\<close> assms(1) assms(3) assms(4) c1 in_mono nless_le step_1a_invariant_1.elims(2))

              show ?thesis
                using c1 c4 c5 c6 step_1a_invariants.simps by presburger
            qed
          next
            assume "\<exists>A. is_safe A \<and>
                two_a_lrn_loop (f j) A \<and>
                (\<exists>l. Process1bLearnerLoopStep A l (f j) (f (Suc j)))"
            then show ?thesis
            proof (clarify)
              fix A l
              assume "is_safe A"
                 and "two_a_lrn_loop (f j) A"
                 and "Process1bLearnerLoopStep A l (f j) (f (Suc j))"
              define new2a where "new2a = M2a l A (recent_msgs (f j) A)"
              have "A \<in> Q"
                using \<open>Process1bLearnerLoopStep A l (f j) (f (Suc j))\<close> \<open>\<forall>a. a \<notin> Q \<longrightarrow> (\<forall>m. \<not> Process1bLearnerLoopStep a m (f j) (f (Suc j)))\<close> by blast
              then have "\<forall>x\<in>set (known_msgs_acc (f j) A). \<forall>b2. B x b2 \<longrightarrow> b2 \<le> b"
                by (metis dual_order.trans ihu1 linorder_le_cases maxbal_absence nat_less_le step_1a_invariant_1.elims(2))
              then have "(\<forall>ba. (\<forall>m \<in> set (recent_msgs (f j) A). B m ba \<longrightarrow> ba \<le> b))"
                by (meson RecentMsgsSpec.elims(2) RecentMsgsSpecResult \<open>is_safe A\<close> assms(1) subsetD)
              then have "(\<forall>ba. M1a ba \<in> \<Union> (set (map Tran (recent_msgs (f j) A))) \<longrightarrow> ba \<le> b)"
                by (smt (verit, del_insts) B_1a KnownMsgs_accSpec.elims(2) KnownMsgs_accSpecResult RecentMsgsSpec.elims(2) RecentMsgsSpecResult \<open>\<forall>x\<in>set (known_msgs_acc (f j) A). \<forall>b2. B x b2 \<longrightarrow> b2 \<le> b\<close> \<open>is_safe A\<close> \<open>k = Suc j\<close> assms(1) bal.simps(1) imageE in_mono known_msgs_acc_preserved le_add2 list.set_map mem_simps(9) plus_1_eq_Suc type.simps(1))
              then have "\<forall>l. \<forall>mb. B new2a mb \<longrightarrow> mb \<le> b"
                using new2a_def by auto
              have "\<forall>m1 \<in> set (known_msgs_acc (f k) A). m1 = new2a \<or> m1 \<in> set (known_msgs_acc (f j) A)"
                by (smt (verit) new2a_def Process1bLearnerLoopStep.elims(2) Store_acc.elims(2) \<open>Process1bLearnerLoopStep A l (f j) (f (Suc j))\<close> \<open>k = Suc j\<close> set_ConsD)
              then have "\<forall>mb. MaxBal (f k) A mb \<longrightarrow> mb \<le> b"
                by (metis MaxBal.simps \<open>\<forall>l mb. B new2a mb \<longrightarrow> mb \<le> b\<close> \<open>\<forall>x\<in>set (known_msgs_acc (f j) A). \<forall>b2. B x b2 \<longrightarrow> b2 \<le> b\<close>)

              have "\<forall>a. a \<noteq> A \<longrightarrow> known_msgs_acc (f k) a = known_msgs_acc (f j) a"
                by (metis Process1bLearnerLoopStep.elims(2) Store_acc.elims(2) \<open>Process1bLearnerLoopStep A l (f j) (f (Suc j))\<close> \<open>k = Suc j\<close>)

              have c1: "step_1a_invariant_1 Q b (f k)"
                unfolding step_1a_invariant_1.simps
                by (metis \<open>\<forall>a. a \<noteq> A \<longrightarrow> known_msgs_acc (f k) a = known_msgs_acc (f j) a\<close> \<open>\<forall>mb. MaxBal (f k) A mb \<longrightarrow> mb \<le> b\<close> \<open>k = Suc j\<close> r1)

              have "msgs (f k) = msgs (f j) \<or> msgs (f k) = new2a # msgs (f j)"
                by (metis Process1bLearnerLoopStep.elims(2) Send.elims(1) \<open>Process1bLearnerLoopStep A l (f j) (f (Suc j))\<close> \<open>k = Suc j\<close> new2a_def)
              then have "\<forall>m \<in> set (msgs (f k)). type m = T1a \<longrightarrow> m \<in> set (msgs (f j))"
                using new2a_def by force
              then have c4: "step_1a_invariant_4 Q b (f k)"
                using ihu4
                unfolding step_1a_invariant_4.simps
                by (metis \<open>k = Suc j\<close> r4 step_1a_invariant_4.elims(2))

              have "\<forall>m \<in> set (msgs (f k)). type m = T1b \<longrightarrow> m \<in> set (msgs (f j))"
                using \<open>msgs (f k) = msgs (f j) \<or> msgs (f k) = new2a # msgs (f j)\<close> new2a_def by fastforce


              have c6: "step_1a_invariant_6 a b (f k)"
                unfolding step_1a_invariant_6.simps
                by (metis B.elims(2) KnownMsgs_accSpec.elims(2) KnownMsgs_accSpecResult MaxBal.simps \<open>M1a b \<notin> set (known_msgs_acc (f (Suc j)) a)\<close> \<open>k = Suc j\<close> assms(1) assms(3) assms(4) c1 in_mono nless_le step_1a_invariant_1.elims(2))

              have "msgs (f k) = new2a # msgs (f j) \<longrightarrow> (\<exists>mb. B new2a mb)"
                using Messages_Have_Max_Ballots
                by (metis Process1bLearnerLoopStep.elims(2) WellFormed.elims(1) \<open>Process1bLearnerLoopStep A l (f j) (f (Suc j))\<close> \<open>k = Suc j\<close> assms(4) ihu5 list.set_intros(1) new2a_def step_1a_invariant_5.elims(2) type.simps(3))
              then have "msgs (f k) = new2a # msgs (f j) \<longrightarrow> (\<exists>mb. B new2a mb \<and> mb \<le> b)"
                by (meson \<open>\<forall>l mb. B new2a mb \<longrightarrow> mb \<le> b\<close>)
              then have c5: "step_1a_invariant_5 Q b (f k)"
                unfolding step_1a_invariant_5.simps
                using \<open>msgs (f k) = msgs (f j) \<or> msgs (f k) = new2a # msgs (f j)\<close> ihu5 by auto
              show ?thesis
                using c1 c4 c5 c6 step_1a_invariants.simps by presburger
            qed
          next
            assume "\<exists>A. is_safe A \<and>
                      two_a_lrn_loop (f j) A \<and>
                      Process1bLearnerLoopDone A (f j) (f (Suc j))"
            then show ?thesis
            proof (clarify)
              fix A
              assume "is_safe A"
                 and "two_a_lrn_loop (f j) A"
                 and "Process1bLearnerLoopDone A (f j) (f (Suc j))"
              have c1: "step_1a_invariant_1 Q b (f k)"
                unfolding step_1a_invariant_1.simps
                using \<open>Process1bLearnerLoopDone A (f j) (f (Suc j))\<close> r1 by auto
              have c4: "step_1a_invariant_4 Q b (f k)"
                unfolding step_1a_invariant_4.simps
                by (smt (verit) Process1bLearnerLoopDone.elims(1) \<open>Process1bLearnerLoopDone A (f j) (f (Suc j))\<close> ext_inject r4 step_1a_invariant_4.elims(2) surjective update_convs(6))
              have c5: "step_1a_invariant_5 Q b (f k)"
                unfolding step_1a_invariant_5.simps
                using \<open>Process1bLearnerLoopDone A (f j) (f (Suc j))\<close> \<open>k = Suc j\<close> ihu5 by auto
              have c6: "step_1a_invariant_6 a b (f k)"
                unfolding step_1a_invariant_6.simps
                by (metis B.elims(2) KnownMsgs_accSpec.elims(2) KnownMsgs_accSpecResult MaxBal.simps \<open>M1a b \<notin> set (known_msgs_acc (f (Suc j)) a)\<close> \<open>k = Suc j\<close> assms(1) assms(3) assms(4) c1 in_mono nless_le step_1a_invariant_1.elims(2))
              show ?thesis
                using c1 c4 c5 c6 step_1a_invariants.simps by presburger
            qed
          qed
        qed
      qed
    qed
  qed
qed


(*
Idea: One can establish that one of three things may happen.
  Given the specifics, we might be able to say "it's this, not this".
  e.g., if there's a T1a message, and nothing else, it must be a proccess1a.
  after that, it should still be the case that AcceptorAction is enabled, so the
  next step is possible. This should be enough to at least get to 
  the learner loop.

Edit: I don't believe this will work because this can't gaurantee that
the properties which hold at i will still hold at k.
*)
lemma from_1a_to_disabled:
  assumes "Spec f"
      and "Enabled (AcceptorAction a) (f i)"
    shows "i \<le> j \<and> \<not> Enabled (AcceptorAction a) (f j) \<longrightarrow>
           (\<exists>k. i \<le> k \<and> k < j \<and> three_cases a (f k) (f (1 + k)))"
proof (induction j)
  case 0
  then show ?case
    using assms(2) by force
next
  case (Suc j)
  assume "i \<le> j \<and> \<not> Enabled (AcceptorAction a) (f j) \<longrightarrow>
          (\<exists>k\<ge>i. k < j \<and> three_cases a (f k) (f (1 + k)))"
  then show "i \<le> Suc j \<and> \<not> Enabled (AcceptorAction a) (f (Suc j)) \<longrightarrow>
               (\<exists>k\<ge>i. k < Suc j \<and> three_cases a (f k) (f (1 + k)))"
  proof (cases "Enabled (AcceptorAction a) (f j)"; clarify)
    case True
    assume "i \<le> Suc j"
       and "\<not> Enabled (AcceptorAction a) (f (Suc j))"
    then show "\<exists>k\<ge>i. k < Suc j \<and> three_cases a (f k) (f (1 + k))"
      by (metis Preserves_AcceptorAction_Disabled_Three_Cases True assms(1) assms(2) le_SucE lessI plus_1_eq_Suc)
  next
    case False
    assume "i \<le> Suc j"
       and "\<not> Enabled (AcceptorAction a) (f (Suc j))"
    have "i \<noteq> Suc j"
      using \<open>\<not> Enabled (AcceptorAction a) (f (Suc j))\<close> assms(2) by blast
    then show "\<exists>k\<ge>i. k < Suc j \<and> three_cases a (f k) (f (1 + k))"
      by (meson False \<open>i \<le> Suc j\<close> \<open>i \<le> j \<and> \<not> Enabled (AcceptorAction a) (f j) \<longrightarrow> (\<exists>k\<ge>i. k < j \<and> three_cases a (f k) (f (1 + k)))\<close> le_SucE less_Suc_eq)
  qed
qed

fun three_Os :: "Acceptor \<Rightarrow> State \<Rightarrow> State \<Rightarrow> bool" where
  "three_Os a st st2 = (
           (\<exists>m. Process1a a m st st2) \<or>
           (\<exists>m. Process1b a m st st2) \<or>
           (Process1bLearnerLoopDone a st st2))"

lemma three_Os_reduce:
  shows "three_cases a st st2 \<longrightarrow> three_Os a st st2"
  using three_Os.simps three_cases.simps by blast

lemma from_1a_to_disabled_O:
  assumes "Spec f"
      and "Enabled (AcceptorAction a) (f i)"
    shows "i \<le> j \<and> \<not> Enabled (AcceptorAction a) (f j) \<longrightarrow>
           (\<exists>k. i \<le> k \<and> k < j \<and> three_Os a (f k) (f (1 + k)))"
  using assms(1) assms(2) from_1a_to_disabled three_Os_reduce by blast


lemma step_1a:
  assumes "Spec f"
      and "Send1a b (f i) (f (1 + i))"
      and "is_safe a"
      and "\<not> Enabled (AcceptorAction a) (f i)"
      and "i < j"
      and "\<not> Enabled (AcceptorAction a) (f j)"
      and "\<forall> k. i < k \<and> k < j \<longrightarrow> \<not> ProposerSendAction (f k) (f (1 + k))
                                \<and> \<not> FakeAcceptorAction (f k) (f (1 + k))"
    shows "\<exists>m \<in> set (msgs (f j)). 
                    acc m = a
                  \<and> type m = T1b
                  \<and> B m b"
proof -
  show ?thesis
    sorry
qed

lemma step_1aa:
  assumes "Spec f"
      and "Send1a b (f i) (f (1 + i))"
      and "\<not> Enabled (AcceptorAction a) (f i)"
      and "\<forall>a \<in> Q. \<not> Enabled (AcceptorAction a) (f i)"
      and "\<forall>a \<in> Q. \<forall> mb :: Ballot. MaxBal (f i) a mb \<longrightarrow> mb \<le> b"
      and "i < j"
      and "\<not> Enabled (AcceptorAction a) (f j)"
      and "\<forall> k. i < k \<and> k < j \<longrightarrow> \<not> ProposerSendAction (f k) (f (1 + k))
                                \<and> \<not> FakeAcceptorAction (f k) (f (1 + k))"
    shows "\<exists>m \<in> set (msgs (f j)). 
                    acc m = a
                  \<and> PresentlyWellFormed (f j) m
                  \<and> (\<forall>a \<in> Q. \<forall> b mb :: Ballot. MaxBal (f j) a mb \<and> B m b \<longrightarrow> mb \<le> b)
                  \<and> type m = T1b"
proof -
  show ?thesis
    sorry
qed

fun UnKnown2a_2 :: "State \<Rightarrow> Learner \<Rightarrow> Ballot \<Rightarrow> Value \<Rightarrow> PreMessage set" where
  "UnKnown2a_2 st l b v = 
    {x . x \<in> set (msgs st) 
      \<and> type x = T2a 
      \<and> lrn x = l 
      \<and> B x b 
      \<and> V st x v }"

fun Network_Assumption_2 :: "Acceptor set \<Rightarrow> Learner \<Rightarrow> Ballot \<Rightarrow> (nat \<Rightarrow> State) \<Rightarrow> bool" where
  "Network_Assumption_2 Q L BB f = (
    (\<exists>S i v. S \<subseteq> UnKnown2a_2 (f i) L BB v \<and> acc ` S = Q \<and>
           (\<exists>j \<ge> i. \<not> Enabled (\<lambda>st st2. \<exists>m \<in> set (msgs st). LearnerRecv L m st st2) (f j))) \<and>
    (WF (\<lambda>st st2. \<exists>v. LearnerDecide L BB v st st2) f)
  )"

fun Liveness_2 :: "(nat \<Rightarrow> State) \<Rightarrow> bool" where
  "Liveness_2 f = ( 
    \<forall> L :: Learner. \<forall> BB :: Ballot. \<forall>Q :: Acceptor set. 
    (\<forall>a \<in> Q. is_safe a) \<longrightarrow> TrustLive L Q \<longrightarrow> 
    Network_Assumption_2 Q L BB f \<longrightarrow> 
    (\<exists>j. decision (f j) L BB \<noteq> {})
  )"


lemma UnKnown2a_2_Conserved:
  assumes "Spec f"
      and "i \<le> j"
    shows "UnKnown2a_2 (f i) L BB v \<subseteq> UnKnown2a_2 (f j) L BB v"
proof -
  have "UnKnown2a_2 (f i) L BB v \<subseteq> set (msgs (f j))"
    by (metis (no_types, lifting) UnKnown2a_2.elims assms(1) assms(2) mem_Collect_eq msgs_preserved subsetI)
  have "BVal (f j) = BVal (f i)"
    using BVal_Constant \<open>Spec f\<close> by blast
  then have "UnKnown2a_2 (f i) L BB v \<subseteq> {x . V (f j) x v}"
    by fastforce
  show ?thesis
    using \<open>UnKnown2a_2 (f i) L BB v \<subseteq> set (msgs (f j))\<close> \<open>UnKnown2a_2 (f i) L BB v \<subseteq> {x. V (f j) x v}\<close> by auto
qed

theorem LivenessResult_2 :
  assumes "Spec f"
  shows "Liveness_2 f"
  unfolding Liveness_2.simps Network_Assumption_2.simps WF.simps
proof (clarify)
  fix L BB S i v j
  assume "Ball (acc ` S) is_safe"
     and "TrustLive L (acc ` S)"
     and h: "\<forall>i. (\<forall>j\<ge>i. Enabled (\<lambda>st st2. \<exists>v. LearnerDecide L BB v st st2) (f j)) \<longrightarrow>
             (\<exists>j\<ge>i. \<exists>v. LearnerDecide L BB v (f j) (f (1 + j)))"
     and "S \<subseteq> UnKnown2a_2 (f i) L BB v"
     and "i \<le> j"
     and hh: "\<not> Enabled (\<lambda>st st2. \<exists>m\<in>set (msgs st). LearnerRecv L m st st2) (f j)"
  have "TrustLive L (acc ` S)"
    using \<open>TrustLive L (acc ` S)\<close> by blast
  have "S \<subseteq> UnKnown2a_2 (f j) L BB v"
    using UnKnown2a_2_Conserved \<open>S \<subseteq> UnKnown2a_2 (f i) L BB v\<close> \<open>i \<le> j\<close> assms by blast
  have "\<forall>m\<in>S. m \<in> set (msgs (f j))"
    using \<open>S \<subseteq> UnKnown2a_2 (f j) L BB v\<close> by auto
  have "\<forall>m\<in>S. is_safe (acc m)"
    using \<open>Ball (acc ` S) is_safe\<close> by blast
  then have "\<forall>m\<in>S. m \<in> set (known_msgs_lrn (f j) L)"
    by (smt (verit, ccfv_threshold) Enabled.elims(1) Learner_Eventually_Gets_All_Safe_Messages \<open>\<forall>m\<in>S. m \<in> set (msgs (f j))\<close> assms hh)
  then have cha: "ChosenIn (f j) L BB v"
    using \<open>S \<subseteq> UnKnown2a_2 (f j) L BB v\<close> \<open>TrustLive L (acc ` S)\<close> by fastforce
  have h0: "\<forall>i. (\<forall>j\<ge>i. (\<exists>v. ChosenIn (f j) L BB v)) \<longrightarrow>
            (\<exists>j\<ge>i. \<exists>v. LearnerDecide L BB v (f j) (f (1 + j)))"
    using h by auto
  have "(\<forall>k\<ge>j. (\<exists>v. ChosenIn (f k) L BB v))"
    using Choice_Made_Perminent cha assms by blast
  then have "(\<exists>k\<ge>j. \<exists>v. LearnerDecide L BB v (f k) (f (1 + k)))"
    using h0 by blast
  then show "\<exists>j. decision (f j) L BB \<noteq> {}"
  proof (clarify)
    fix k v2
    assume "j \<le> k"
       and "LearnerDecide L BB v2 (f k) (f (1 + k))"
    then have "v2 \<in> decision (f (1 + k)) L BB"
      by force
    then show "\<exists>j. decision (f j) L BB \<noteq> {}"
      by blast
  qed
qed




lemma Network_Assumption_2_0:
  assumes "Spec f"
      and "S \<subseteq> UnKnown2a_2 (f i) L BB v"
      and "j \<ge> i"
      and "\<not> Enabled (\<lambda>st st2. \<exists>m \<in> set (msgs st). LearnerRecv L m st st2) (f j)"
      and "TrustLive L (acc ` S)"
    shows "ChosenIn (f j) L BB v"
proof -
  have "\<forall>m\<in>set (msgs (f j)). \<not> Enabled (LearnerRecv L m) (f j)"
    using assms(4) by auto
  then have "\<forall>m\<in>set (msgs (f j)). \<not> Recv_lrn (f j) L m"
    by auto
  have "S \<subseteq> UnKnown2a_2 (f j) L BB v"
    using UnKnown2a_2_Conserved assms(1) assms(2) assms(3) by blast
  have "is_quorum (acc ` S)"
    using TrustLiveAssumption assms(5) by blast
  then have "\<forall>a \<in> acc ` S. is_safe a"
    sledgehammer
  then have "\<forall>m \<in> S. is_safe (acc m)"
    sorry
  then have "\<forall>m\<in>S. m \<in> set (known_msgs_lrn (f j) L)"
    sorry
  then show ?thesis
    by (smt (verit) ChosenIn.simps Collect_mem_eq Collect_mono_iff Known2a.simps UnKnown2a_2.elims \<open>S \<subseteq> UnKnown2a_2 (f j) L BB v\<close> assms(5))
qed










(*
is_safe a \<and> (
      (\<not> two_a_lrn_loop st a \<and>
       ((queued_msg st a \<noteq> None \<and> 
         Process1b a (the (queued_msg st a)) st st2) \<or> 
        (queued_msg st a = None \<and> (
          \<exists>m \<in> set (msgs st). Process1a a m st st2 \<or> Process1b a m st st2
        ))))
      \<or> (two_a_lrn_loop st a \<and> 
         Process1bLearnerLoop a st st2)
  )
*)

lemma LearnerDecide_Enables_Perminent_Next:
  assumes "Spec f"
      and "Enabled (LearnerDecide L BB v) (f i)"
    shows "j \<ge> i \<longrightarrow> Enabled (LearnerDecide L BB v) (f j)"
  using Choice_Made_Perminent LearnerDecide_Enabled assms(1) assms(2) by blast










fun UnKnown2a :: "State \<Rightarrow> Learner \<Rightarrow> Ballot \<Rightarrow> Value \<Rightarrow> PreMessage set" where
  "UnKnown2a st l b v = 
    {x . x \<in> set (msgs st) 
      \<and> type x = T2a 
      \<and> lrn x = l 
      \<and> B x b 
      \<and> V st x v
      \<and> WellFormed st x
      \<and> Proper_lrn st l x  }"

lemma UnKnown2a_Conserved:
  assumes "Spec f"
      and "i \<le> j"
    shows "UnKnown2a (f i) L BB v \<subseteq> UnKnown2a (f j) L BB v"
proof -
  have "UnKnown2a (f i) L BB v \<subseteq> set (msgs (f j))"
    by (metis (no_types, lifting) UnKnown2a.elims assms(1) assms(2) mem_Collect_eq msgs_preserved subsetI)
  have "BVal (f j) = BVal (f i)"
    using BVal_Constant \<open>Spec f\<close> by blast
  then have "UnKnown2a (f i) L BB v \<subseteq> {x . V (f j) x v}"
    by fastforce
  have "\<forall>x. Proper_lrn (f i) L x \<longrightarrow> Proper_lrn (f j) L x"
    using Proper_lrn.simps assms(1) assms(2) known_msgs_lrn_preserved by blast
  show ?thesis
    sledgehammer
    by (smt (verit) Collect_mono_iff UnKnown2a.elims WellFormed_monotone \<open>BVal (f j) = BVal (f i)\<close> \<open>UnKnown2a (f i) L BB v \<subseteq> set (msgs (f j))\<close> \<open>UnKnown2a (f i) L BB v \<subseteq> {x. V (f j) x v}\<close> \<open>\<forall>x. Proper_lrn (f i) L x \<longrightarrow> Proper_lrn (f j) L x\<close> mem_Collect_eq subsetD)
qed

lemma Network_Assumption_1_0:
  assumes "Spec f"
      and "S \<subseteq> UnKnown2a (f i) L BB v"
      and "j \<ge> i"
      and "\<not> Enabled (\<lambda>st st2. \<exists>m \<in> set (msgs st). LearnerRecv L m st st2) (f j)"
      and "TrustLive L (acc ` S)"
    shows "ChosenIn (f j) L BB v"
proof -
  have "\<forall>m\<in>set (msgs (f j)). \<not> Enabled (LearnerRecv L m) (f j)"
    using assms(4) by auto
  then have "\<forall>m\<in>set (msgs (f j)). \<not> Recv_lrn (f j) L m"
    by auto
  then have h: "\<forall>m\<in>set (msgs (f j)). 
                 m \<in> UnKnown2a (f j) L BB v \<longrightarrow> 
                 m \<in> set (known_msgs_lrn (f j) L)"
    by auto
  have "S \<subseteq> UnKnown2a (f j) L BB v"
    using UnKnown2a_Conserved assms(1) assms(2) assms(3) by blast
  then have "\<forall>m\<in>S. m \<in> set (known_msgs_lrn (f j) L)"
    by (metis (mono_tags, lifting) UnKnown2a.elims h mem_Collect_eq subsetD)
  then have "S \<subseteq> Known2a (f j) L BB v"
    by (smt (verit, del_insts) Known2a.simps UnKnown2a.elims \<open>S \<subseteq> UnKnown2a (f j) L BB v\<close> mem_Collect_eq subsetD subsetI)
  then show ?thesis
    using assms(5) by auto
qed

fun Network_Assumption_1 :: "Acceptor set \<Rightarrow> Learner \<Rightarrow> Ballot \<Rightarrow> (nat \<Rightarrow> State) \<Rightarrow> bool" where
  "Network_Assumption_1 Q L BB f = (
    (\<exists>S i v. S \<subseteq> UnKnown2a (f i) L BB v \<and> acc ` S = Q \<and>
           (\<exists>j \<ge> i. \<not> Enabled (\<lambda>st st2. \<exists>m \<in> set (msgs st). LearnerRecv L m st st2) (f j))) \<and>
    (WF (\<lambda>st st2. \<exists>v. LearnerDecide L BB v st st2) f)
  )"

fun Liveness_1 :: "(nat \<Rightarrow> State) \<Rightarrow> bool" where
  "Liveness_1 f = ( 
    \<forall> L :: Learner. \<forall> BB :: Ballot. \<forall>Q :: Acceptor set. is_quorum Q \<longrightarrow>
    (\<forall>a \<in> Q. is_safe a) \<longrightarrow> TrustLive L Q \<longrightarrow> 
    (Network_Assumption_1 Q L BB f \<longrightarrow> 
    (\<exists>j. decision (f j) L BB \<noteq> {})
  ))"


theorem LivenessResult_1 :
  assumes "Spec f"
  shows "Liveness_1 f"
  unfolding Liveness_1.simps Network_Assumption_1.simps WF.simps
proof (clarify)
  fix L BB S i v j
  assume "is_quorum (acc ` S)"
     and "Ball (acc ` S) is_safe"
     and "TrustLive L (acc ` S)"
     and h: "\<forall>i. (\<forall>j\<ge>i. Enabled (\<lambda>st st2. \<exists>v. LearnerDecide L BB v st st2) (f j)) \<longrightarrow>
             (\<exists>j\<ge>i. \<exists>v. LearnerDecide L BB v (f j) (f (1 + j)))"
     and "S \<subseteq> UnKnown2a (f i) L BB v"
     and "i \<le> j"
     and hh: "\<not> Enabled (\<lambda>st st2. \<exists>m\<in>set (msgs st). LearnerRecv L m st st2) (f j)"
  have "TrustLive L (acc ` S)"
    using \<open>TrustLive L (acc ` S)\<close> by blast
  then have cha: "ChosenIn (f j) L BB v"
    using Network_Assumption_1_0 hh \<open>S \<subseteq> UnKnown2a (f i) L BB v\<close> \<open>j \<ge> i\<close> \<open>Spec f\<close> by blast
  have h0: "\<forall>i. (\<forall>j\<ge>i. (\<exists>v. ChosenIn (f j) L BB v)) \<longrightarrow>
            (\<exists>j\<ge>i. \<exists>v. LearnerDecide L BB v (f j) (f (1 + j)))"
    using h by auto
  have "(\<forall>k\<ge>j. (\<exists>v. ChosenIn (f k) L BB v))"
    using Choice_Made_Perminent cha assms by blast
  then have "(\<exists>k\<ge>j. \<exists>v. LearnerDecide L BB v (f k) (f (1 + k)))"
    using h0 by blast
  then show "\<exists>j. decision (f j) L BB \<noteq> {}"
  proof (clarify)
    fix k v2
    assume "j \<le> k"
       and "LearnerDecide L BB v2 (f k) (f (1 + k))"
    then have "v2 \<in> decision (f (1 + k)) L BB"
      by force
    then show "\<exists>j. decision (f j) L BB \<noteq> {}"
      by blast
  qed
qed

fun Network_Assumption_0 :: "Acceptor set \<Rightarrow> Learner \<Rightarrow> Ballot \<Rightarrow> (nat \<Rightarrow> State) \<Rightarrow> bool" where
  "Network_Assumption_0 Q L BB f = (
    (\<exists>i v. ChosenIn (f i) L BB v) \<and>
    (WF (\<lambda>st st2. \<exists>v. LearnerDecide L BB v st st2) f)
  )"

fun Liveness_0 :: "(nat \<Rightarrow> State) \<Rightarrow> bool" where
  "Liveness_0 f = ( 
    \<forall> L :: Learner. \<forall> BB :: Ballot. \<forall>Q :: Acceptor set. is_quorum Q \<longrightarrow>
    (\<forall>a \<in> Q. is_safe a) \<longrightarrow> TrustLive L Q \<longrightarrow> 
    (Network_Assumption_0 Q L BB f \<longrightarrow> 
    (\<exists>j. decision (f j) L BB \<noteq> {})
  ))"


theorem LivenessResult_0 :
  assumes "Spec f"
  shows "Liveness_0 f"
  unfolding Liveness_0.simps Network_Assumption_0.simps WF.simps
proof (clarify)
  fix L BB Q j v
  assume "is_quorum Q"
     and "Ball Q is_safe"
     and "TrustLive L Q"
     and h: "\<forall>i. (\<forall>j\<ge>i. Enabled (\<lambda>st st2. \<exists>v. LearnerDecide L BB v st st2) (f j)) \<longrightarrow>
             (\<exists>j\<ge>i. \<exists>v. LearnerDecide L BB v (f j) (f (1 + j)))"
     and cha: "ChosenIn (f j) L BB v"
  have h0: "\<forall>i. (\<forall>j\<ge>i. (\<exists>v. ChosenIn (f j) L BB v)) \<longrightarrow>
            (\<exists>j\<ge>i. \<exists>v. LearnerDecide L BB v (f j) (f (1 + j)))"
    using h by auto
  have "(\<forall>k\<ge>j. (\<exists>v. ChosenIn (f k) L BB v))"
    using Choice_Made_Perminent cha assms by blast
  then have "(\<exists>k\<ge>j. \<exists>v. LearnerDecide L BB v (f k) (f (1 + k)))"
    using h0 by blast
  then show "\<exists>j. decision (f j) L BB \<noteq> {}"
  proof (clarify)
    fix k v2
    assume "j \<le> k"
       and "LearnerDecide L BB v2 (f k) (f (1 + k))"
    then have "v2 \<in> decision (f (1 + k)) L BB"
      by force
    then show "\<exists>j. decision (f j) L BB \<noteq> {}"
      by blast
  qed
qed




















lemma all_message:
  assumes "Spec f"
      and "type x = T1a"
      and "\<forall>a \<in> Q. the (MaxBalO (f i) a) < bal x"
      and "\<exists>a \<in> Q. \<exists>j. i < j \<and> j < i + k \<and> Process1a a x (f (j - 1)) (f j)"
      and "\<forall>a \<in> Q. \<not> Enabled (AcceptorAction a) (f (i + k - 1))"
      and "\<forall>a \<in> Q. is_safe a"
    shows "\<forall>a \<in> Q. \<exists>j. i < j \<and> j < i + k \<and> Process1a a x (f (j - 1)) (f j)"
proof -
  have "\<forall>a \<in> Q. x \<notin> set (known_msgs_acc (f i) a)"
    using assms(2) assms(3) new_bal_unknown by blast
  have "\<forall>a \<in> Q. Enabled (Process1a a x) (f i)"
    by (metis MessageType.distinct(1) MessageType.distinct(3) Process1a.simps Process1a_Enabled Proper_acc.simps Recv_acc.elims(2) Recv_acc.elims(3) WellFormed.elims(1) \<open>\<forall>a\<in>Q. x \<notin> set (known_msgs_acc (f i) a)\<close> assms(4) empty_iff ref.simps(1) type.elims)
  have "\<exists>a \<in> Q. \<exists>j. i < j \<and> j < i + k \<and> Process1a a x (f (j - 1)) (f j)"
    using assms(4) by blast
  then show ?thesis
  proof (clarify)
    fix a0 j0 a
    assume "a \<in> Q"
       and "a0 \<in> Q"
       and "i < j0"
       and "j0 < i + k"
       and "Process1a a0 x (f (j0 - 1)) (f j0)"
    have "is_safe a0"
      using \<open>a0 \<in> Q\<close> assms(6) by blast
    have "x \<in> set (msgs (f j0))"
      using Process1a_Req_msgs \<open>Process1a a0 x (f (j0 - 1)) (f j0)\<close> \<open>is_safe a0\<close> assms(1) by blast
    have "x \<in> set (msgs (f (i + k - 1)))"
      by (metis Suc_eq_plus1 \<open>j0 < i + k\<close> \<open>x \<in> set (msgs (f j0))\<close> add_le_imp_le_diff assms(1) linorder_not_less msgs_preserved not_less_eq_eq)
    have "queued_msg (f (i + k - 1)) a = None"
      sorry
    have "\<not> Enabled (Process1a a x) (f (i + k - 1))"
      using \<open>a \<in> Q\<close> \<open>queued_msg (f (i + k - 1)) a = None\<close> \<open>x \<in> set (msgs (f (i + k - 1)))\<close> assms(5) assms(6) no_acceptor_no_Process1a by blast
    have "Enabled (Process1a a x) (f j0)"
      sorry
    show "\<exists>j. i < j \<and> j < i + k \<and> Process1a a x (f (j - 1)) (f j)"
      sorry
  qed
qed







(*Extract consecutive runs of given lengths from a stream*)
fun sequence_of_runs :: "nat \<Rightarrow> nat list \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> ('a list) list" where
  "sequence_of_runs start [] f = []" |
  "sequence_of_runs start (len # lens) f = 
    map f [start ..< start + len] # sequence_of_runs (start + len) lens f"

theorem sequence_of_runs_length:
  shows "length (sequence_of_runs start lens f) = length lens"
proof (induction lens arbitrary: start; simp) qed

definition message_delivered :: "Acceptor set \<Rightarrow> (nat \<Rightarrow> State) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "message_delivered Q f ib ie \<equiv> 
    (\<exists>x :: PreMessage. 
     (type x = T1a) \<and>
     (\<forall>a \<in> Q. the (MaxBalO (f ib) a) < bal x) \<and>
     (\<exists>a \<in> Q. \<exists>j. ib < j \<and> j < ie \<and> Process1a a x (f (j - 1)) (f j)))"
(*? (\<forall> a \<in> Q. \<forall>mb b :: Ballot. MaxBal (f ib) a b \<and> B x b \<longrightarrow> mb \<le> b) ?*)


definition message_unique :: "Acceptor set \<Rightarrow> (nat \<Rightarrow> State) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "message_unique Q f ib ie \<equiv> 
    (\<forall>m1 m2 :: PreMessage. 
          ((\<exists>a \<in> Q. \<exists>j. ib < j \<and> j < ie \<and> Process1a a m1 (f (j - 1)) (f j)) \<and>
           (\<exists>a \<in> Q. \<exists>j. ib < j \<and> j < ie \<and> Process1a a m2 (f (j - 1)) (f j))) \<longrightarrow>
           m1 = m2)"

definition no_message_delivered :: "Acceptor set \<Rightarrow> (nat \<Rightarrow> State) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "no_message_delivered Q f ib ie \<equiv> \<not> (\<exists>m :: PreMessage. (\<exists>a j. ib < j \<and> j < ie \<and> Process1a a m (f (j - 1)) (f j)))"

fun Network_Assumption :: "Acceptor set \<Rightarrow> (nat \<Rightarrow> State) \<Rightarrow> bool" where
  "Network_Assumption Q f = (
    \<exists>is :: nat list. length is = 14 \<and> sorted is \<and>
    (\<forall>i \<in> set (drop 1 is). \<forall>a \<in> Q. \<not>Enabled (AcceptorAction a) (f (i - 1))) \<and>

    message_delivered Q f (is ! 0) (is ! 1) \<and> message_unique Q f (is ! 0) (is ! 1) \<and>
    no_message_delivered Q f (is ! 1) (is ! 2) \<and>
    no_message_delivered Q f (is ! 2) (is ! 3) \<and>
    message_delivered Q f (is ! 4) (is ! 5) \<and> message_unique Q f (is ! 4) (is ! 5) \<and>
    no_message_delivered Q f (is ! 5) (is ! 6) \<and>
    no_message_delivered Q f (is ! 6) (is ! 7) \<and>
    no_message_delivered Q f (is ! 7) (is ! 8) \<and>
    no_message_delivered Q f (is ! 8) (is ! 9) \<and>
    message_delivered Q f (is ! 9) (is ! 10) \<and> message_unique Q f (is ! 9) (is ! 10) \<and>
    no_message_delivered Q f (is ! 10) (is ! 11) \<and>
    no_message_delivered Q f (is ! 11) (is ! 12) \<and>
    no_message_delivered Q f (is ! 12) (is ! 13)
  )"

fun Liveness :: "(nat \<Rightarrow> State) \<Rightarrow> bool" where
  "Liveness f = (
    \<forall> L :: Learner. \<forall> b :: Ballot. \<forall>Q :: Acceptor set. is_quorum Q \<longrightarrow>
    (\<forall>a \<in> Q. is_safe a) \<longrightarrow> TrustLive L Q \<longrightarrow> 
    (\<forall>i. Network_Assumption Q f \<longrightarrow> 
    (\<exists>j \<ge> i. \<exists> BB :: Ballot . decision (f j) L BB \<noteq> {})
  ))"


theorem LivenessResult :
  assumes "Spec f"
  shows "Liveness f"
  sorry

end











(*
lemma step_1a_invariants:
  assumes "Spec f"
      and "M1a b \<in> set (msgs (f i))"
      and "is_safe a"
      and "M1a b \<notin> set (known_msgs_acc (f i) a)"
      and "\<not> (\<exists>M \<in> set (msgs (f i)). M \<noteq> M1a b \<and> Recv_acc (f i) a M \<and> (type M = T1a \<or> type M = T1b))"
      and "\<forall> mb :: Ballot. MaxBal (f i) a mb \<longrightarrow> mb < b"
      and "queued_msg (f i) a = None"
      and "\<not> two_a_lrn_loop (f i) a"
    shows "i < j \<and> M1a b \<notin> set (known_msgs_acc (f j) a) \<and>
           (\<forall> k. i \<le> k \<and> k \<le> j \<longrightarrow> \<not> ProposerSendAction (f k) (f (1 + k))
                                      \<and> \<not> FakeAcceptorAction (f k) (f (1 + k)))
           \<longrightarrow>
           (\<forall> k. i \<le> k \<and> k \<le> j \<longrightarrow> \<not> (\<exists>M \<in> set (msgs (f k)). M \<noteq> M1a b \<and> Recv_acc (f k) a M \<and> (type M = T1a \<or> type M = T1b))
                                    \<and> (\<forall> mb :: Ballot. MaxBal (f k) a mb \<longrightarrow> mb < b)
                                    \<and> queued_msg (f k) a = None
                                    \<and> \<not> two_a_lrn_loop (f k) a)"
proof (induction j)
  case 0
  then show ?case
    by fastforce
next
  case (Suc j)
  assume ih:"i < j \<and>
         M1a b \<notin> set (known_msgs_acc (f j) a) \<and>
         (\<forall>k. i \<le> k \<and> k \<le> j \<longrightarrow>
              \<not> ProposerSendAction (f k) (f (1 + k)) \<and>
              \<not> FakeAcceptorAction (f k) (f (1 + k))) \<longrightarrow>
         (\<forall>k. i \<le> k \<and> k \<le> j \<longrightarrow>
              \<not> (\<exists>M\<in>set (msgs (f k)).
                     M \<noteq> M1a b \<and>
                     Recv_acc (f k) a M \<and> (type M = T1a \<or> type M = T1b)) \<and>
              (\<forall>mb. MaxBal (f k) a mb \<longrightarrow> mb < b)
                                    \<and> queued_msg (f k) a = None
                                    \<and> \<not> two_a_lrn_loop (f k) a)"
  then show ?case
  proof (clarify)
    fix k
    assume "i < Suc j"
       and "M1a b \<notin> set (known_msgs_acc (f (Suc j)) a)"
       and "\<forall>k. i \<le> k \<and> k \<le> Suc j \<longrightarrow>
             \<not> ProposerSendAction (f k) (f (1 + k)) \<and>
             \<not> FakeAcceptorAction (f k) (f (1 + k))"
       and "i \<le> k"
       and "k \<le> Suc j"
    have "M1a b \<notin> set (known_msgs_acc (f j) a)"
      by (metis \<open>M1a b \<notin> set (known_msgs_acc (f (Suc j)) a)\<close> assms(1) known_msgs_acc_preserved le_add2 plus_1_eq_Suc)
    have "(\<forall>k. i \<le> k \<and> k \<le> j \<longrightarrow>
              \<not> ProposerSendAction (f k) (f (1 + k)) \<and>
              \<not> FakeAcceptorAction (f k) (f (1 + k)))"
      using \<open>\<forall>k. i \<le> k \<and> k \<le> Suc j \<longrightarrow> \<not> ProposerSendAction (f k) (f (1 + k)) \<and> \<not> FakeAcceptorAction (f k) (f (1 + k))\<close> le_Suc_eq by presburger
    have ihu:"(\<forall>k. i \<le> k \<and> k \<le> j \<longrightarrow>
              \<not> (\<exists>M\<in>set (msgs (f k)).
                     M \<noteq> M1a b \<and>
                     Recv_acc (f k) a M \<and> (type M = T1a \<or> type M = T1b)) \<and>
              (\<forall>mb. MaxBal (f k) a mb \<longrightarrow> mb < b))"
      by (metis \<open>M1a b \<notin> set (known_msgs_acc (f j) a)\<close> \<open>\<forall>k. i \<le> k \<and> k \<le> j \<longrightarrow> \<not> ProposerSendAction (f k) (f (1 + k)) \<and> \<not> FakeAcceptorAction (f k) (f (1 + k))\<close> \<open>i < Suc j\<close> antisym assms(5) assms(6) ih less_SucE)
    show "\<not> (\<exists>M\<in>set (msgs (f k)).
                    M \<noteq> M1a b \<and>
                    Recv_acc (f k) a M \<and> (type M = T1a \<or> type M = T1b))
               \<and> (\<forall>mb. MaxBal (f k) a mb \<longrightarrow> mb < b)
                                    \<and> queued_msg (f k) a = None
                                    \<and> \<not> two_a_lrn_loop (f k) a"
    proof (cases "k \<noteq> Suc j")
      case True
      then show ?thesis 
        using \<open>\<forall>k. i \<le> k \<and> k \<le> j \<longrightarrow> \<not> (\<exists>M\<in>set (msgs (f k)). M \<noteq> M1a b \<and> Recv_acc (f k) a M \<and> (type M = T1a \<or> type M = T1b)) \<and> (\<forall>mb. MaxBal (f k) a mb \<longrightarrow> mb < b)\<close> \<open>i \<le> k\<close> \<open>k \<le> Suc j\<close> le_SucE by blast
    next
      case False
      have ihu1: "\<not> (\<exists>M\<in>set (msgs (f j)).
                     M \<noteq> M1a b \<and>
                     Recv_acc (f j) a M \<and> (type M = T1a \<or> type M = T1b))"
        using \<open>i < Suc j\<close> ihu less_Suc_eq_le by blast
      have ihu2: "(\<forall>mb. MaxBal (f j) a mb \<longrightarrow> mb < b)"
        using \<open>i < Suc j\<close> ihu less_Suc_eq_le by blast
      have r1: "known_msgs_acc (f j) a = known_msgs_acc (f (Suc j)) a \<longrightarrow> (\<forall>mb. MaxBal (f k) a mb \<longrightarrow> mb < b)"
        using False MaxBal.simps ihu2 by presburger
      have r2: "known_msgs_acc (f j) a = known_msgs_acc (f (Suc j)) a \<and> set (msgs (f j)) = set (msgs (f (Suc j))) 
            \<longrightarrow> \<not> (\<exists>M\<in>set (msgs (f k)). M \<noteq> M1a b \<and> Recv_acc (f k) a M \<and> (type M = T1a \<or> type M = T1b))"
        unfolding Recv_acc.simps Proper_acc.simps
        by (metis False Proper_acc.elims(1) Recv_acc.elims(3) Wellformed_Constant assms(1) ihu1)
      have r3: "queued_msg (f j) a = queued_msg (f (Suc j)) a \<longrightarrow> queued_msg (f k) a = None"
        by (metis False MessageType.distinct(1) QueuedMsgResult QueuedMsgSpec1.elims(2) QueuedMsgSpec2.elims(2) QueuedMsgSpec2_Conserved assms(1) assms(3) ihu1 type.simps(1))
      have r4: "two_a_lrn_loop (f j) a = two_a_lrn_loop (f (Suc j)) a \<longrightarrow> \<not> two_a_lrn_loop (f k) a "
        by (metis False Orderings.order_eq_iff \<open>M1a b \<notin> set (known_msgs_acc (f j) a)\<close> \<open>\<forall>k. i \<le> k \<and> k \<le> j \<longrightarrow> \<not> ProposerSendAction (f k) (f (1 + k)) \<and> \<not> FakeAcceptorAction (f k) (f (1 + k))\<close> \<open>i < Suc j\<close> assms(8) ih not_less_less_Suc_eq order_less_imp_le)
      show ?thesis
      proof (cases "f j = f (Suc j)")
        case True
        then show ?thesis
          by (metis False \<open>M1a b \<notin> set (known_msgs_acc (f j) a)\<close> \<open>\<forall>k. i \<le> k \<and> k \<le> j \<longrightarrow> \<not> ProposerSendAction (f k) (f (1 + k)) \<and> \<not> FakeAcceptorAction (f k) (f (1 + k))\<close> \<open>i < Suc j\<close> assms(7) assms(8) dual_order.eq_iff dual_order.strict_implies_order ih not_less_less_Suc_eq r1 r2)
      next
        case False
        have "Next (f j) (f (Suc j))"
          using False Spec.simps assms(1) by blast
        have "\<not> (ProposerSendAction (f j) (f (Suc j)))"
          by (metis \<open>\<forall>k. i \<le> k \<and> k \<le> Suc j \<longrightarrow> \<not> ProposerSendAction (f k) (f (1 + k)) \<and> \<not> FakeAcceptorAction (f k) (f (1 + k))\<close> \<open>i < Suc j\<close> le_add2 less_Suc_eq_le plus_1_eq_Suc)
        have "\<not> (FakeAcceptorAction (f j) (f (Suc j)))"
          by (metis \<open>\<forall>k. i \<le> k \<and> k \<le> Suc j \<longrightarrow> \<not> ProposerSendAction (f k) (f (1 + k)) \<and> \<not> FakeAcceptorAction (f k) (f (1 + k))\<close> \<open>i < Suc j\<close> le_add2 less_Suc_eq_le plus_1_eq_Suc)
        have "\<forall>m \<in> set (msgs (f j)). \<not> (Process1a a m (f j) (f (Suc j)))"
          by (metis Process1a.elims(2) Process1a_Req_known_msgs \<open>M1a b \<notin> set (known_msgs_acc (f (Suc j)) a)\<close> assms(1) diff_Suc_1 ihu1)
        have "\<forall>m \<in> set (msgs (f j)). \<not> (Process1b a m (f j) (f (Suc j)))"
          by (metis Enabled.simps MessageType.distinct(1) Process1b_Enabled ihu1 type.simps(1))
        then show ?thesis
        proof (cases "LearnerProcessAction (f j) (f (Suc j))")
          case True
          then show ?thesis
            unfolding LearnerProcessAction.simps LearnerAction.simps
          proof (clarify)
            fix ln
            assume "(\<exists>m\<in>set (msgs (f j)). LearnerRecv ln m (f j) (f (Suc j))) \<or>
                    (\<exists>blt val. LearnerDecide ln blt val (f j) (f (Suc j)))"
            then show ?thesis
              unfolding LearnerRecv.simps LearnerDecide.simps
            proof -
              assume a1: "(\<exists>m\<in>set (msgs (f j)). Recv_lrn (f j) ln m \<and> f (Suc j) = f j \<lparr>known_msgs_lrn := \<lambda>x. if ln = x then m # known_msgs_lrn (f j) x else known_msgs_lrn (f j) x\<rparr>) \<or> (\<exists>blt val. ChosenIn (f j) ln blt val \<and> f (Suc j) = f j \<lparr>decision := \<lambda>x y. if x = ln \<and> y = blt then {val} \<union> decision (f j) x y else decision (f j) x y\<rparr>)"
              have "i < j \<and> M1a b \<notin> set (known_msgs_acc (f j) a) \<and> (\<forall>n. i \<le> n \<and> n \<le> j \<longrightarrow> \<not> ProposerSendAction (f n) (f (1 + n)) \<and> \<not> FakeAcceptorAction (f n) (f (1 + n))) \<longrightarrow> (\<forall>n. i \<le> n \<and> n \<le> j \<longrightarrow> (\<forall>p. p \<notin> set (msgs (f n)) \<or> p = M1a b \<or> \<not> Recv_acc (f n) a p \<or> type p \<noteq> T1a \<and> type p \<noteq> T1b) \<and> (\<forall>na. MaxBal (f n) a na \<longrightarrow> na < b) \<and> queued_msg (f n) a = None \<and> \<not> two_a_lrn_loop (f n) a)"
                using ih by blast
              then have f2: "\<not> i < j \<or> (\<forall>n. \<not> i \<le> n \<or> \<not> n \<le> j \<or> (\<forall>p. p \<notin> set (msgs (f n)) \<or> p = M1a b \<or> \<not> Recv_acc (f n) a p \<or> type p \<noteq> T1a \<and> type p \<noteq> T1b) \<and> (\<forall>na. \<not> MaxBal (f n) a na \<or> na < b) \<and> queued_msg (f n) a = None \<and> \<not> two_a_lrn_loop (f n) a)"
                using \<open>M1a b \<notin> set (known_msgs_acc (f j) a)\<close> \<open>\<forall>k. i \<le> k \<and> k \<le> j \<longrightarrow> \<not> ProposerSendAction (f k) (f (1 + k)) \<and> \<not> FakeAcceptorAction (f k) (f (1 + k))\<close> by presburger
              have f3: "\<forall>n na. n < na \<or> \<not> n < Suc na \<or> na = n"
                using less_antisym by blast
              then have f4: "i < j \<or> j = i"
                using \<open>i < Suc j\<close> by blast
              have f5: "k < Suc j \<or> Suc j = k"
                using f3 \<open>k \<le> Suc j\<close> less_Suc_eq_le by blast
              obtain nn :: nat and pp :: PreMessage where
                f6: "((\<exists>p. p \<in> set (msgs (f k)) \<and> p \<noteq> M1a b \<and> Recv_acc (f k) a p \<and> (type p = T1a \<or> type p = T1b)) \<or> (\<exists>n. MaxBal (f k) a n \<and> \<not> n < b) \<or> queued_msg (f k) a \<noteq> None \<or> two_a_lrn_loop (f k) a) = (pp \<in> set (msgs (f k)) \<and> pp \<noteq> M1a b \<and> Recv_acc (f k) a pp \<and> (type pp = T1a \<or> type pp = T1b) \<or> MaxBal (f k) a nn \<and> \<not> nn < b \<or> queued_msg (f k) a \<noteq> None \<or> two_a_lrn_loop (f k) a)"
                by blast
              have f7: "\<lparr>msgs = msgs (f j), known_msgs_acc = known_msgs_acc (f j), known_msgs_lrn = \<lambda>l. if ln = l then v0_2 # known_msgs_lrn (f j) l else known_msgs_lrn (f j) l, recent_msgs = recent_msgs (f j), queued_msg = queued_msg (f j), two_a_lrn_loop = two_a_lrn_loop (f j), processed_lrns = processed_lrns (f j), decision = decision (f j), BVal = BVal (f j), \<dots> = more (f j)\<rparr> = f j\<lparr>known_msgs_lrn := \<lambda>l. if ln = l then v0_2 # known_msgs_lrn (f j) l else known_msgs_lrn (f j) l\<rparr>"
                by simp
              obtain ppa :: PreMessage and nna :: nat and vv :: Value where
                f8: "ppa \<in> set (msgs (f j)) \<and> Recv_lrn (f j) ln ppa \<and> f (Suc j) = f j \<lparr>known_msgs_lrn := \<lambda>l. if ln = l then ppa # known_msgs_lrn (f j) l else known_msgs_lrn (f j) l\<rparr> \<or> ChosenIn (f j) ln nna vv \<and> f (Suc j) = f j \<lparr>decision := \<lambda>l n. if l = ln \<and> n = nna then {vv} \<union> decision (f j) l n else decision (f j) l n\<rparr>"
                using a1 by blast
              have f9: "f (Suc j) = f j \<lparr>decision := \<lambda>l n. if l = ln \<and> n = nna then {vv} \<union> decision (f j) l n else decision (f j) l n\<rparr> \<longrightarrow> \<lparr>msgs = msgs (f j), known_msgs_acc = known_msgs_acc (f j), known_msgs_lrn = known_msgs_lrn (f j), recent_msgs = recent_msgs (f j), queued_msg = queued_msg (f j), two_a_lrn_loop = two_a_lrn_loop (f j), processed_lrns = processed_lrns (f j), decision = \<lambda>l n. if l = ln \<and> n = nna then {vv} \<union> decision (f j) l n else decision (f j) l n, BVal = BVal (f j), \<dots> = more (f j)\<rparr> = \<lparr>msgs = msgs (f (Suc j)), known_msgs_acc = known_msgs_acc (f (Suc j)), known_msgs_lrn = known_msgs_lrn (f (Suc j)), recent_msgs = recent_msgs (f (Suc j)), queued_msg = queued_msg (f (Suc j)), two_a_lrn_loop = two_a_lrn_loop (f (Suc j)), processed_lrns = processed_lrns (f (Suc j)), decision = decision (f (Suc j)), BVal = BVal (f (Suc j)), \<dots> = more (f (Suc j))\<rparr>"
                by simp
              have f10: "\<forall>ps f fa fb fc p fd fe ff u psa fg fh fi fj pa fk fl fm ua. (\<lparr>msgs = ps, known_msgs_acc = f, known_msgs_lrn = fa, recent_msgs = fb, queued_msg = fc, two_a_lrn_loop = p, processed_lrns = fd, decision = fe, BVal = ff, \<dots> = u::unit\<rparr> = \<lparr>msgs = psa, known_msgs_acc = fg, known_msgs_lrn = fh, recent_msgs = fi, queued_msg = fj, two_a_lrn_loop = pa, processed_lrns = fk, decision = fl, BVal = fm, \<dots> = ua\<rparr>) = (ps = psa \<and> f = fg \<and> fa = fh \<and> fb = fi \<and> fc = fj \<and> p = pa \<and> fd = fk \<and> fe = fl \<and> ff = fm \<and> u = ua)"
                by simp
              have f11: "i \<le> j"
                using \<open>i < Suc j\<close> by auto
              have f12: "queued_msg (f j) = queued_msg (f (Suc j)) \<and> queued_msg (f k) a \<noteq> None \<longrightarrow> queued_msg (f k) a = None"
                using f4 f3 f2 by (metis (no_types) \<open>i \<le> k\<close> \<open>k \<le> Suc j\<close> assms(7) less_Suc_eq_le linorder_not_less)
              moreover
              { assume "ppa \<notin> set (msgs (f j)) \<or> \<not> Recv_lrn (f j) ln ppa \<or> f (Suc j) \<noteq> f j \<lparr>known_msgs_lrn := \<lambda>l. if ln = l then ppa # known_msgs_lrn (f j) l else known_msgs_lrn (f j) l\<rparr>"
                moreover
                { assume "(msgs (f j) = msgs (f (Suc j)) \<and> known_msgs_acc (f j) = known_msgs_acc (f (Suc j)) \<and> known_msgs_lrn (f j) = known_msgs_lrn (f (Suc j)) \<and> recent_msgs (f j) = recent_msgs (f (Suc j)) \<and> queued_msg (f j) = queued_msg (f (Suc j)) \<and> two_a_lrn_loop (f j) = two_a_lrn_loop (f (Suc j)) \<and> processed_lrns (f j) = processed_lrns (f (Suc j)) \<and> (\<lambda>l n. if l = ln \<and> n = nna then {vv} \<union> decision (f j) l n else decision (f j) l n) = decision (f (Suc j)) \<and> BVal (f j) = BVal (f (Suc j)) \<and> more (f j) = more (f (Suc j))) \<and> \<not> two_a_lrn_loop (f (Suc j)) a"
                  then have "(msgs (f j) = msgs (f (Suc j)) \<and> known_msgs_acc (f j) = known_msgs_acc (f (Suc j)) \<and> known_msgs_lrn (f j) = known_msgs_lrn (f (Suc j)) \<and> recent_msgs (f j) = recent_msgs (f (Suc j)) \<and> queued_msg (f j) = queued_msg (f (Suc j)) \<and> two_a_lrn_loop (f j) = two_a_lrn_loop (f (Suc j)) \<and> processed_lrns (f j) = processed_lrns (f (Suc j)) \<and> (\<lambda>l n. if l = ln \<and> n = nna then {vv} \<union> decision (f j) l n else decision (f j) l n) = decision (f (Suc j)) \<and> BVal (f j) = BVal (f (Suc j)) \<and> more (f j) = more (f (Suc j))) \<and> Suc j \<noteq> k \<or> (msgs (f j) = msgs (f (Suc j)) \<and> known_msgs_acc (f j) = known_msgs_acc (f (Suc j)) \<and> known_msgs_lrn (f j) = known_msgs_lrn (f (Suc j)) \<and> recent_msgs (f j) = recent_msgs (f (Suc j)) \<and> queued_msg (f j) = queued_msg (f (Suc j)) \<and> two_a_lrn_loop (f j) = two_a_lrn_loop (f (Suc j)) \<and> processed_lrns (f j) = processed_lrns (f (Suc j)) \<and> (\<lambda>l n. if l = ln \<and> n = nna then {vv} \<union> decision (f j) l n else decision (f j) l n) = decision (f (Suc j)) \<and> BVal (f j) = BVal (f (Suc j)) \<and> more (f j) = more (f (Suc j))) \<and> \<not> two_a_lrn_loop (f k) a"
                    by meson }
                moreover
                { assume "(msgs (f j) = msgs (f (Suc j)) \<and> known_msgs_acc (f j) = known_msgs_acc (f (Suc j)) \<and> known_msgs_lrn (f j) = known_msgs_lrn (f (Suc j)) \<and> recent_msgs (f j) = recent_msgs (f (Suc j)) \<and> queued_msg (f j) = queued_msg (f (Suc j)) \<and> two_a_lrn_loop (f j) = two_a_lrn_loop (f (Suc j)) \<and> processed_lrns (f j) = processed_lrns (f (Suc j)) \<and> (\<lambda>l n. if l = ln \<and> n = nna then {vv} \<union> decision (f j) l n else decision (f j) l n) = decision (f (Suc j)) \<and> BVal (f j) = BVal (f (Suc j)) \<and> more (f j) = more (f (Suc j))) \<and> \<not> j \<le> j"
                  then have "(msgs (f j) = msgs (f (Suc j)) \<and> known_msgs_acc (f j) = known_msgs_acc (f (Suc j)) \<and> known_msgs_lrn (f j) = known_msgs_lrn (f (Suc j)) \<and> recent_msgs (f j) = recent_msgs (f (Suc j)) \<and> queued_msg (f j) = queued_msg (f (Suc j)) \<and> two_a_lrn_loop (f j) = two_a_lrn_loop (f (Suc j)) \<and> processed_lrns (f j) = processed_lrns (f (Suc j)) \<and> (\<lambda>l n. if l = ln \<and> n = nna then {vv} \<union> decision (f j) l n else decision (f j) l n) = decision (f (Suc j)) \<and> BVal (f j) = BVal (f (Suc j)) \<and> more (f j) = more (f (Suc j))) \<and> Suc j \<noteq> k \<or> (msgs (f j) = msgs (f (Suc j)) \<and> known_msgs_acc (f j) = known_msgs_acc (f (Suc j)) \<and> known_msgs_lrn (f j) = known_msgs_lrn (f (Suc j)) \<and> recent_msgs (f j) = recent_msgs (f (Suc j)) \<and> queued_msg (f j) = queued_msg (f (Suc j)) \<and> two_a_lrn_loop (f j) = two_a_lrn_loop (f (Suc j)) \<and> processed_lrns (f j) = processed_lrns (f (Suc j)) \<and> (\<lambda>l n. if l = ln \<and> n = nna then {vv} \<union> decision (f j) l n else decision (f j) l n) = decision (f (Suc j)) \<and> BVal (f j) = BVal (f (Suc j)) \<and> more (f j) = more (f (Suc j))) \<and> k \<le> j"
                    by force }
                ultimately have "(msgs (f j) = msgs (f (Suc j)) \<and> known_msgs_acc (f j) = known_msgs_acc (f (Suc j)) \<and> known_msgs_lrn (f j) = known_msgs_lrn (f (Suc j)) \<and> recent_msgs (f j) = recent_msgs (f (Suc j)) \<and> queued_msg (f j) = queued_msg (f (Suc j)) \<and> two_a_lrn_loop (f j) = two_a_lrn_loop (f (Suc j)) \<and> processed_lrns (f j) = processed_lrns (f (Suc j)) \<and> (\<lambda>l n. if l = ln \<and> n = nna then {vv} \<union> decision (f j) l n else decision (f j) l n) = decision (f (Suc j)) \<and> BVal (f j) = BVal (f (Suc j)) \<and> more (f j) = more (f (Suc j))) \<and> Suc j \<noteq> k \<or> (msgs (f j) = msgs (f (Suc j)) \<and> known_msgs_acc (f j) = known_msgs_acc (f (Suc j)) \<and> known_msgs_lrn (f j) = known_msgs_lrn (f (Suc j)) \<and> recent_msgs (f j) = recent_msgs (f (Suc j)) \<and> queued_msg (f j) = queued_msg (f (Suc j)) \<and> two_a_lrn_loop (f j) = two_a_lrn_loop (f (Suc j)) \<and> processed_lrns (f j) = processed_lrns (f (Suc j)) \<and> (\<lambda>l n. if l = ln \<and> n = nna then {vv} \<union> decision (f j) l n else decision (f j) l n) = decision (f (Suc j)) \<and> BVal (f j) = BVal (f (Suc j)) \<and> more (f j) = more (f (Suc j))) \<and> k \<le> j \<or> (msgs (f j) = msgs (f (Suc j)) \<and> known_msgs_acc (f j) = known_msgs_acc (f (Suc j)) \<and> known_msgs_lrn (f j) = known_msgs_lrn (f (Suc j)) \<and> recent_msgs (f j) = recent_msgs (f (Suc j)) \<and> queued_msg (f j) = queued_msg (f (Suc j)) \<and> two_a_lrn_loop (f j) = two_a_lrn_loop (f (Suc j)) \<and> processed_lrns (f j) = processed_lrns (f (Suc j)) \<and> (\<lambda>l n. if l = ln \<and> n = nna then {vv} \<union> decision (f j) l n else decision (f j) l n) = decision (f (Suc j)) \<and> BVal (f j) = BVal (f (Suc j)) \<and> more (f j) = more (f (Suc j))) \<and> j = i \<or> (msgs (f j) = msgs (f (Suc j)) \<and> known_msgs_acc (f j) = known_msgs_acc (f (Suc j)) \<and> known_msgs_lrn (f j) = known_msgs_lrn (f (Suc j)) \<and> recent_msgs (f j) = recent_msgs (f (Suc j)) \<and> queued_msg (f j) = queued_msg (f (Suc j)) \<and> two_a_lrn_loop (f j) = two_a_lrn_loop (f (Suc j)) \<and> processed_lrns (f j) = processed_lrns (f (Suc j)) \<and> (\<lambda>l n. if l = ln \<and> n = nna then {vv} \<union> decision (f j) l n else decision (f j) l n) = decision (f (Suc j)) \<and> BVal (f j) = BVal (f (Suc j)) \<and> more (f j) = more (f (Suc j))) \<and> \<not> two_a_lrn_loop (f k) a"
                  using f11 f10 f9 f8 f4 f2 by (smt (z3))
                then have "(pp \<notin> set (msgs (f k)) \<or> pp = M1a b \<or> \<not> Recv_acc (f k) a pp \<or> type pp \<noteq> T1a \<and> type pp \<noteq> T1b) \<and> (\<not> MaxBal (f k) a nn \<or> nn < b) \<and> queued_msg (f k) a = None \<and> \<not> two_a_lrn_loop (f k) a"
                  using f12 f5 f4 f3 f2 by (smt (z3) \<open>i \<le> k\<close> assms(8) less_Suc_eq_le linorder_not_less r1 r2) }
              ultimately show ?thesis
                using f10 f7 f6 f5 f4 f3 f2
                by (smt (z3) \<open>i \<le> k\<close> assms(8) less_Suc_eq_le linorder_not_less r1 r2 surjective update_convs(3))
            qed
          qed
        next
          case False
          have "AcceptorProcessAction (f j) (f (Suc j))"
            using False Next.elims(2) \<open>Next (f j) (f (Suc j))\<close> \<open>\<not> FakeAcceptorAction (f j) (f (Suc j))\<close> \<open>\<not> ProposerSendAction (f j) (f (Suc j))\<close> by blast
          then have "(\<exists>A :: Acceptor. is_safe A
                                    \<and> queued_msg (f j) A = None 
                                    \<and> (\<exists>m \<in> set (msgs (f j)). Process1a A m (f j) (f (Suc j)))) \<or>
                      (\<exists>A :: Acceptor. is_safe A
                                    \<and> queued_msg (f j) A \<noteq> None 
                                    \<and> Process1b A (the (queued_msg (f j) A)) (f j) (f (Suc j))) \<or>
                      (\<exists>A :: Acceptor. is_safe A
                                    \<and> queued_msg (f j) A = None 
                                    \<and> (\<exists>m \<in> set (msgs (f j)). Process1b A m (f j) (f (Suc j)))) \<or>
                      (\<exists>A :: Acceptor. is_safe A
                                    \<and> two_a_lrn_loop (f j) A 
                                    \<and> (\<exists>l :: Learner. Process1bLearnerLoopStep A l (f j) (f (Suc j)))) \<or>
                      (\<exists>A :: Acceptor. is_safe A
                                    \<and> two_a_lrn_loop (f j) A 
                                    \<and> Process1bLearnerLoopDone A (f j) (f (Suc j)))"
            using Acceptor_split by presburger
          then show ?thesis
          proof (elim disjE)
            assume "\<exists>A. is_safe A \<and>
              queued_msg (f j) A = None \<and>
              (\<exists>m\<in>set (msgs (f j)).
                  Process1a A m (f j) (f (Suc j)))"
            then show ?thesis
            proof (clarify)
              fix A m
              assume "is_safe A"
                 and "queued_msg (f j) A = None"
                 and "m \<in> set (msgs (f j))"
                 and "Process1a A m (f j) (f (Suc j))"
              define new1b where "new1b = M1b A (m # recent_msgs (f j) A)"
              have "WellFormed (f j) new1b"
                sorry
              then show ?thesis
                sorry
            qed
          next
            assume "\<exists>A. is_safe A \<and>
                      queued_msg (f j) A \<noteq> None \<and>
                      Process1b A (the (queued_msg (f j) A)) (f j) (f (Suc j))"
            then show ?thesis
            proof (clarify)
              fix A y
              assume "is_safe A"
                 and "queued_msg (f j) A = Some y"
                 and "Process1b A (the (queued_msg (f j) A)) (f j) (f (Suc j))"
              then show ?thesis
                unfolding Process1b.simps
                sorry
            qed
          next
            assume "\<exists>A. is_safe A \<and>
                        queued_msg (f j) A = None \<and>
                        (\<exists>m\<in>set (msgs (f j)). Process1b A m (f j) (f (Suc j)))"
            then show ?thesis
            proof (clarify)
              fix A m
              assume "is_safe A"
                 and "queued_msg (f j) A = None"
                 and "m\<in>set (msgs (f j))"
                 and "Process1b A m (f j) (f (Suc j))"
              then have "A \<noteq> a"
                sorry
              then show ?thesis
                sorry
            qed
          next
            assume "\<exists>A. is_safe A \<and>
                two_a_lrn_loop (f j) A \<and>
                (\<exists>l. Process1bLearnerLoopStep A l (f j) (f (Suc j)))"
            then show ?thesis
            proof (clarify)
              fix A l
              assume "is_safe A"
                 and "two_a_lrn_loop (f j) A"
                 and "Process1bLearnerLoopStep A l (f j) (f (Suc j))"
              then have "A \<noteq> a"
                sorry
              then show ?thesis
                sorry
            qed
          next
            assume "\<exists>A. is_safe A \<and>
                      two_a_lrn_loop (f j) A \<and>
                      Process1bLearnerLoopDone A (f j) (f (Suc j))"
            then show ?thesis
            proof (clarify)
              fix A
              assume "is_safe A"
                 and "two_a_lrn_loop (f j) A"
                 and "Process1bLearnerLoopDone A (f j) (f (Suc j))"
              then have "A \<noteq> a"
                sorry
              then show ?thesis
                sorry
            qed
          qed
        qed
      qed
    qed
  qed
qed

lemma step_1a_full:
  assumes "Spec f"
      and "M1a b \<in> set (msgs (f i))"
      and "\<forall> mb :: Ballot. MaxBal (f i) a mb \<longrightarrow> mb < b"
      and "is_safe a"
      and "M1a b \<notin> set (known_msgs_acc (f i) a)"
      and "\<not> (\<exists>M \<in> set (msgs (f i)). M \<noteq> M1a b \<and> Recv_acc (f i) a M \<and> (type M = T1a \<or> type M = T1b))"
    shows "M1a b \<in> set (known_msgs_acc (f (i + j)) a) \<and>
           (\<forall> k. i \<le> k \<and> k \<le> i + j \<longrightarrow> \<not> ProposerSendAction (f k) (f (1 + k))
                                      \<and> \<not> FakeAcceptorAction (f k) (f (1 + k)))
           \<longrightarrow>
           (\<exists>k. i \<le> k \<and> k < i + j \<and>
             (\<forall> mb :: Ballot. MaxBal (f k) a mb \<longrightarrow> mb < b) \<and>
             \<not> (\<exists>M \<in> set (msgs (f k)). M \<noteq> M1a b \<and> Recv_acc (f k) a M \<and> (type M = T1a \<or> type M = T1b)))"
proof (induction j)
  case 0
  then show ?case
    by (metis assms(5) verit_sum_simplify)
next
  case (Suc j)
  then show ?case sorry
qed

lemma step_:
  assumes "Spec f"
      and "M1a b \<in> set (msgs (f i))"
      and "\<forall> mb :: Ballot. MaxBal (f i) a mb \<longrightarrow> mb < b"
      and "is_safe a"
      and "M1a b \<notin> set (known_msgs_acc (f i) a)"
      and "\<not> (\<exists>M \<in> set (msgs (f i)). M \<noteq> M1a b \<and> Recv_acc (f i) a M \<and> (type M = T1a \<or> type M = T1b))"
    shows "i < j \<and> M1a b \<in> set (known_msgs_acc (f j) a) \<and>
           (\<forall> k. i < k \<and> k < j \<longrightarrow> \<not> ProposerSendAction (f k) (f (1 + k))
                                 \<and> \<not> FakeAcceptorAction (f k) (f (1 + k)))
           \<longrightarrow>
           (\<exists>k. i \<le> k \<and> k < j \<and> 
             M1a b \<notin> set (known_msgs_acc (f k) a) \<and>
             Process1a a (M1a b) (f k) (f (1 + k)) \<and>
             (\<forall> mb :: Ballot. MaxBal (f k) a mb \<longrightarrow> mb < b) \<and>
             \<not> (\<exists>M \<in> set (msgs (f k)). M \<noteq> M1a b \<and> Recv_acc (f k) a M \<and> (type M = T1a \<or> type M = T1b)))"
proof (induction j)
  case 0
  then show ?case 
    by fastforce
next
  case (Suc j)
  assume ih: "i < j \<and>
         M1a b \<in> set (known_msgs_acc (f j) a) \<and>
         (\<forall>k. i < k \<and> k < j \<longrightarrow>
              \<not> ProposerSendAction (f k) (f (1 + k)) \<and>
              \<not> FakeAcceptorAction (f k) (f (1 + k))) \<longrightarrow>
         (\<exists>k\<ge>i. k < j \<and>
                 M1a b \<notin> set (known_msgs_acc (f k) a) \<and>
                 Process1a a (M1a b) (f k) (f (1 + k)) \<and>
                 (\<forall>mb. MaxBal (f k) a mb \<longrightarrow> mb < b) \<and>
                 \<not> (\<exists>M\<in>set (msgs (f k)).
                        M \<noteq> M1a b \<and>
                        Recv_acc (f k) a M \<and>
                        (type M = T1a \<or> type M = T1b)))"
  show ?case
  proof (clarify)
    assume "i < Suc j"
       and "M1a b \<in> set (known_msgs_acc (f (Suc j)) a)"
       and "\<forall>k. i < k \<and> k < Suc j \<longrightarrow>
            \<not> ProposerSendAction (f k) (f (1 + k)) \<and>
            \<not> FakeAcceptorAction (f k) (f (1 + k))"
    then show "\<exists>k\<ge>i. k < Suc j \<and>
           M1a b \<notin> set (known_msgs_acc (f k) a) \<and>
           Process1a a (M1a b) (f k) (f (1 + k)) \<and>
           (\<forall>mb. MaxBal (f k) a mb \<longrightarrow> mb < b) \<and>
           \<not> (\<exists>M\<in>set (msgs (f k)).
                  M \<noteq> M1a b \<and>
                  Recv_acc (f k) a M \<and>
                  (type M = T1a \<or> type M = T1b))"
    proof (cases "i = j")
      case True
      then show ?thesis
        by (metis \<open>M1a b \<in> set (known_msgs_acc (f (Suc j)) a)\<close> \<open>i < Suc j\<close> assms(1) assms(2) assms(3) assms(4) assms(5) assms(6) le_less_Suc_eq step_1a_only)
    next
      case False
      have "i < j"
        using False \<open>i < Suc j\<close> by linarith
      have "(\<forall>k. i < k \<and> k < j \<longrightarrow>
              \<not> ProposerSendAction (f k) (f (1 + k)) \<and>
              \<not> FakeAcceptorAction (f k) (f (1 + k)))"
        using \<open>\<forall>k. i < k \<and> k < Suc j \<longrightarrow> \<not> ProposerSendAction (f k) (f (1 + k)) \<and> \<not> FakeAcceptorAction (f k) (f (1 + k))\<close> less_Suc_eq by blast
      then show ?thesis sorry
    qed


      proof (cases "M1a b \<in> set (known_msgs_acc (f j) a)")
        case True
        then show ?thesis
          by (metis Suc \<open>\<forall>k. i < k \<and> k < Suc j \<longrightarrow> \<not> ProposerSendAction (f k) (f (1 + k)) \<and> \<not> FakeAcceptorAction (f k) (f (1 + k))\<close> \<open>i < Suc j\<close> assms(5) less_Suc_eq)
      next
        case False
          have "Next (f j) (f (Suc j))"
            by (metis False Spec.elims(2) \<open>M1a b \<in> set (known_msgs_acc (f (Suc j)) a)\<close> assms(1))
          then have "\<not> (ProposerSendAction (f j) (f (Suc j)))"
            by (metis False ProposerSendAction.elims(2) Send1a.elims(2) \<open>M1a b \<in> set (known_msgs_acc (f (Suc j)) a)\<close> ext_inject surjective update_convs(1))
          have "\<forall> ln m. \<not> (LearnerRecv ln m (f j) (f (Suc j)))"
            by (smt (verit, ccfv_SIG) False LearnerRecv.simps \<open>M1a b \<in> set (known_msgs_acc (f (Suc j)) a)\<close> ext_inject surjective update_convs(3))
          have "\<forall> ln blt val. \<not> (LearnerDecide ln blt val (f j) (f (Suc j)))"
            using False \<open>M1a b \<in> set (known_msgs_acc (f (Suc j)) a)\<close> by force
          then have "\<forall>a. \<not> (LearnerProcessAction (f j) (f (Suc j)))"
            by (meson LearnerAction.elims(2) LearnerProcessAction.elims(1) \<open>\<forall>ln m. \<not> LearnerRecv ln m (f j) (f (Suc j))\<close>)
          have "\<forall>a. \<not> (FakeSend1b a (f j) (f (Suc j)))"
            by (metis FakeSend1b.elims(1) False \<open>M1a b \<in> set (known_msgs_acc (f (Suc j)) a)\<close> ext_inject surjective update_convs(1))
          have "\<forall>a. \<not> (FakeSend2a a (f j) (f (Suc j)))"
            by (metis FakeSend2a.simps False \<open>M1a b \<in> set (known_msgs_acc (f (Suc j)) a)\<close> ext_inject surjective update_convs(1))
          then have "\<not> (FakeAcceptorAction (f j) (f (Suc j)))"
            using FakeAcceptorAction.simps \<open>\<forall>a. \<not> FakeSend1b a (f j) (f (Suc j))\<close> by presburger
          then have "AcceptorProcessAction (f j) (f (Suc j))"
            by (meson LearnerAction.elims(2) LearnerProcessAction.elims(2) Next.simps \<open>Next (f j) (f (Suc j))\<close> \<open>\<forall>ln blt val. \<not> LearnerDecide ln blt val (f j) (f (Suc j))\<close> \<open>\<forall>ln m. \<not> LearnerRecv ln m (f j) (f (Suc j))\<close> \<open>\<not> ProposerSendAction (f j) (f (Suc j))\<close>)
          have "\<forall> A m. a \<noteq> A \<longrightarrow> \<not> (Process1a A m (f j) (f (Suc j)))"
            by (metis False Process1a.elims(2) Store_acc.elims(2) \<open>M1a b \<in> set (known_msgs_acc (f (Suc j)) a)\<close>)
          have "\<forall> A m. a \<noteq> A \<longrightarrow> \<not> (Process1b A m (f j) (f (Suc j)))"
            by (metis False Process1b.elims(2) Store_acc.elims(2) \<open>M1a b \<in> set (known_msgs_acc (f (Suc j)) a)\<close>)
          have "\<forall> a. \<not> (Process1bLearnerLoopDone a (f j) (f (Suc j)))"
            using False \<open>M1a b \<in> set (known_msgs_acc (f (Suc j)) a)\<close> by force
          have "\<forall> ln. \<not> (Process1bLearnerLoopStep a ln (f j) (f (Suc j)))"
            unfolding Process1bLearnerLoopStep.simps
            by (smt (verit, ccfv_SIG) False PreMessage.distinct(3) Store_acc.elims(2) \<open>M1a b \<in> set (known_msgs_acc (f (Suc j)) a)\<close> set_ConsD)  
          then have "\<forall> A. a \<noteq> A \<longrightarrow> \<not> AcceptorAction A (f j) (f (Suc j))"
          proof -
            { fix aa :: Acceptor
              have "known_msgs_acc (f (Suc j)) \<noteq> known_msgs_acc (f j) \<and> known_msgs_acc (f (Suc j)) a \<noteq> known_msgs_acc (f j) a"
                using False \<open>M1a b \<in> set (known_msgs_acc (f (Suc j)) a)\<close> by fastforce
              then have "aa = a \<or> \<not> AcceptorAction aa (f j) (f (Suc j))"
                by (metis (full_types) AcceptorAction.elims(2) Process1bLearnerLoop.elims(2) Process1bLearnerLoopStep.elims(2) Store_acc.elims(2) \<open>\<forall>A m. a \<noteq> A \<longrightarrow> \<not> Process1a A m (f j) (f (Suc j))\<close> \<open>\<forall>A m. a \<noteq> A \<longrightarrow> \<not> Process1b A m (f j) (f (Suc j))\<close> \<open>\<forall>a. \<not> Process1bLearnerLoopDone a (f j) (f (Suc j))\<close>) }
            then show ?thesis
              by (metis (no_types))
          qed
          then have "AcceptorAction a (f j) (f (Suc j))"
            by (metis AcceptorProcessAction.simps \<open>AcceptorProcessAction (f j) (f (Suc j))\<close>)
          have "\<forall> m. (M1a b) \<noteq> m \<longrightarrow> \<not> (Process1a a m (f j) (f (Suc j)))"
            unfolding Process1a.simps
            by (metis False Store_acc.elims(2) \<open>M1a b \<in> set (known_msgs_acc (f (Suc j)) a)\<close> set_ConsD)
          have "\<not> (Process1b a (M1a b) (f j) (f (Suc j)))"
            by simp
          have "\<forall> m. (M1a b) \<noteq> m \<longrightarrow> \<not> (Process1b a m (f j) (f (Suc j)))"
            unfolding Process1b.simps
            by (metis (no_types, lifting) False Store_acc.elims(2) \<open>M1a b \<in> set (known_msgs_acc (f (Suc j)) a)\<close> set_ConsD)
          then have "\<forall> m. \<not> (Process1b a m (f j) (f (Suc j)))"
            by (metis \<open>\<not> Process1b a (M1a b) (f j) (f (Suc j))\<close>)
          then have "Process1a a (M1a b) (f j) (f (Suc j))"
            by (metis AcceptorAction.elims(2) Process1bLearnerLoop.elims(2) \<open>AcceptorAction a (f j) (f (Suc j))\<close> \<open>\<forall>a. \<not> Process1bLearnerLoopDone a (f j) (f (Suc j))\<close> \<open>\<forall>ln. \<not> Process1bLearnerLoopStep a ln (f j) (f (Suc j))\<close> \<open>\<forall>m. M1a b \<noteq> m \<longrightarrow> \<not> Process1a a m (f j) (f (Suc j))\<close>)
          then have "\<exists>k. i \<le> k \<and> k < Suc j \<and> Process1a a (M1a b) (f k) (f (1 + k))"
            by (metis \<open>i < Suc j\<close> less_Suc_eq less_Suc_eq_le plus_1_eq_Suc)
          have "\<forall>k. i < k \<and> k < j \<longrightarrow>
              \<not> ProposerSendAction (f k) (f (1 + k)) \<and>
              \<not> FakeAcceptorAction (f k) (f (1 + k))"
            using \<open>\<forall>k. i < k \<and> k < Suc j \<longrightarrow> \<not> ProposerSendAction (f k) (f (1 + k)) \<and> \<not> FakeAcceptorAction (f k) (f (1 + k))\<close> less_Suc_eq by presburger
          show ?thesis
          proof (cases "i < j")
            case True
            have "\<exists>k\<ge>i. k < j \<and>
                 Process1a a (M1a b) (f k) (f (1 + k)) \<and>
                 (\<forall>mb. MaxBal (f k) a mb \<longrightarrow> mb < b) \<and>
                 \<not> (\<exists>M\<in>set (msgs (f k)).
                        M \<noteq> M1a b \<and>
                        Recv_acc (f k) a M \<and>
                        (type M = T1a \<or> type M = T1b))"
              sorry
            then show ?thesis sorry
          next
            case False
            have "i = j"
              using False \<open>i < Suc j\<close> less_Suc_eq by blast
            then show ?thesis
              using \<open>\<exists>k\<ge>i. k < Suc j \<and> Process1a a (M1a b) (f k) (f (1 + k))\<close> assms(3) assms(6) le_less_Suc_eq by blast
          qed
        qed
      qed

  qed
qed
*)