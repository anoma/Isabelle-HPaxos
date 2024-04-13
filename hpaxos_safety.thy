theory hpaxos_safety
imports Main hpaxos
begin

fun Safety :: "State \<Rightarrow> bool" where
  "Safety st = (
    \<forall>L1 L2 :: Learner. \<forall>B1 B2 :: Ballot. \<forall>V1 V2 :: Value.
        ent L1 L2
      \<and> V1 \<in> decision st L1 B1
      \<and> V2 \<in> decision st L2 B2
      \<longrightarrow> V1 = V2
  )"

(*Mostly enforced by types*)
fun TypeOK :: "State \<Rightarrow> bool" where
  "TypeOK st = (
    (\<forall>m \<in> set (msgs st). isValidMessage m) \<and>
    (\<forall>a :: Acceptor. \<forall>m \<in> set (known_msgs_acc st a). isValidMessage m) \<and>
    (\<forall>a :: Learner. \<forall>m \<in> set (known_msgs_lrn st a). isValidMessage m) \<and>
    (\<forall>a :: Acceptor. \<forall>m \<in> set (recent_msgs st a). isValidMessage m) \<and>
    (\<forall>a :: Acceptor. queued_msg st a \<noteq> None \<longrightarrow> isValidMessage (the (queued_msg st a)))
  )"

fun RecentMsgsSpec :: "State \<Rightarrow> bool" where
  "RecentMsgsSpec st = (
    \<forall>a :: Acceptor. is_safe a \<longrightarrow> 
      set (recent_msgs st a) \<subseteq> set (known_msgs_acc st a)
  )"

fun KnownMsgs_accSpec :: "State \<Rightarrow> bool" where
  "KnownMsgs_accSpec st = (
     \<forall>a :: Acceptor. is_safe a \<longrightarrow> 
      (\<forall>m \<in> set (known_msgs_acc st a). 
        m \<in> set (msgs st) \<and>
        Proper_acc st a m \<and>
        WellFormed st m \<and>
        Tran m \<subseteq> set (known_msgs_acc st a)
  ))"

fun KnownMsgs_lrnSpec :: "State \<Rightarrow> bool" where
  "KnownMsgs_lrnSpec st = (
     \<forall>l :: Learner. 
      (\<forall>m \<in> set (known_msgs_lrn st l). 
        m \<in> set (msgs st) \<and>
        Proper_lrn st l m \<and>
        WellFormed st m \<and>
        Tran m \<subseteq> set (known_msgs_lrn st l)
  ))"

fun QueuedMsgSpec1 :: "State \<Rightarrow> bool" where
  "QueuedMsgSpec1 st = (
    \<forall>a :: Acceptor. is_safe a \<and> queued_msg st a \<noteq> None \<longrightarrow> (
      type (the (queued_msg st a)) = T1b \<and>
      (the (queued_msg st a) \<in> set (msgs st)) \<and>
      (recent_msgs st a = [])
  ))"

fun twoaLearnerLoopSpec :: "State \<Rightarrow> bool" where "
  twoaLearnerLoopSpec st = (
    \<forall>a :: Acceptor. is_safe a \<and> two_a_lrn_loop st a \<longrightarrow>
      queued_msg st a = None
  )"

fun SentBy :: "State \<Rightarrow> Acceptor \<Rightarrow> PreMessage set" where
  "SentBy st a = {m \<in> set (msgs st) . type m \<noteq> T1a \<and> acc m = a}"

fun SafeAcceptorOwnMessagesRefsSpec :: "State \<Rightarrow> bool" where "
  SafeAcceptorOwnMessagesRefsSpec st = (
    \<forall>a :: Acceptor. is_safe a \<and> (SentBy st a \<noteq> {}) \<longrightarrow>
        (queued_msg st a = None \<longrightarrow> (
          \<exists> m0 \<in> set (recent_msgs st a). \<forall>m1 \<in> SentBy st a. m1 \<in> Tran m0)) \<and>
        (queued_msg st a \<noteq> None \<longrightarrow> (
          \<forall>m1 \<in> SentBy st a. m1 \<in> Tran (the (queued_msg st a))))
  )"

fun MsgsSafeAcceptorSpec :: "State \<Rightarrow> bool" where "
  MsgsSafeAcceptorSpec st = (
    \<forall>a :: Acceptor. is_safe a \<longrightarrow> (
    \<forall> m1 \<in> set(msgs st). \<forall> m2 \<in> set(msgs st).
    (type m1 \<noteq> T1a \<and> type m2 \<noteq> T1a \<and> acc m1 = a \<and> acc m2 = a) \<longrightarrow>
    (m1 \<in> Tran m1 \<or> m2 \<in> Tran m2)
  ))"

fun DecisionSpec :: "State \<Rightarrow> bool" where "
  DecisionSpec st = (
    \<forall>l :: Learner. \<forall>b :: Ballot. \<forall>v :: Value.
      v \<in> decision st l b \<longrightarrow> ChosenIn st l b v
  )"

fun FullSafetyInvariant :: "State \<Rightarrow> bool" where
  "FullSafetyInvariant st = (
    TypeOK st
    \<and> RecentMsgsSpec st
    \<and> KnownMsgs_accSpec st
    \<and> KnownMsgs_lrnSpec st
    \<and> QueuedMsgSpec1 st
    \<and> twoaLearnerLoopSpec st
    \<and> SafeAcceptorOwnMessagesRefsSpec st
    \<and> MsgsSafeAcceptorSpec st
    \<and> DecisionSpec st
    \<and> Safety st
  )"

lemma TypeOKInvariant :
  assumes "TypeOK st"
      and "Next st st2"
  shows "TypeOK st2"
  unfolding Next.simps
proof -
  have "Next st st2"
   using assms(2) by blast
  then show "TypeOK st2"
    unfolding Next.simps
  proof (elim disjE)
    assume p: "ProposerSendAction st st2"
    show ?thesis
      unfolding TypeOK.simps
    proof (intro conjI; clarify)
      fix x
      assume h: "x \<in> set (msgs st2)"
      show "isValidMessage x"
        using p h assms(1) by auto
    next 
      fix a x
      assume h: "x \<in> set (known_msgs_acc st2 a)"
      show "isValidMessage x"
        using p h assms(1) by force
    next
      fix a x
      assume h: "x \<in> set (known_msgs_lrn st2 a)"
      show "isValidMessage x"
        using p h assms(1) by force
    next
      fix a x
      assume h: "x \<in> set (recent_msgs st2 a)"
      show "isValidMessage x"
        using p h assms(1) by force
    next
      fix a y
      assume h: "queued_msg st2 a = Some y"
      show "isValidMessage (the (queued_msg st2 a))"
        using assms(1) h p by force
    qed
  next
    assume "AcceptorProcessAction st st2"
    then show ?thesis
      unfolding AcceptorProcessAction.simps AcceptorAction.simps
      proof (elim exE)
        fix a
        assume h: "is_safe a \<and>
                  (\<not> two_a_lrn_loop st a \<and>
                   (queued_msg st a \<noteq> None \<and>
                    Process1b a (the (queued_msg st a)) st st2 \<or>
                    queued_msg st a = None \<and>
                    (\<exists>m \<in> set (msgs st). Process1a a m st st2 \<or> Process1b a m st st2)) \<or>
                   two_a_lrn_loop st a \<and> Process1bLearnerLoop a st st2)"
        show ?thesis
        proof (cases "two_a_lrn_loop st a")
            case True
            have p: "Process1bLearnerLoop a st st2" 
              using True h by blast
            then show ?thesis
            unfolding Process1bLearnerLoop.simps
            proof (elim disjE)
              assume "\<exists>ln. ln \<notin> processed_lrns st a \<and>
                        Process1bLearnerLoopStep a ln st st2"
              then show ?thesis
              proof (elim exE)
                fix ln
                assume p: "ln \<notin> processed_lrns st a \<and>
                           Process1bLearnerLoopStep a ln st st2"
              then show ?thesis
                unfolding TypeOK.simps
              proof (intro conjI; clarify)
                fix x
                assume h: "x \<in> set (msgs st2)"
                show "isValidMessage x"
                  by (smt (z3) Process1bLearnerLoopStep.elims(2) Send.elims(2) TypeOK.elims(1) WellFormed.elims(2) \<open>\<exists>ln. ln \<notin> processed_lrns st a \<and> Process1bLearnerLoopStep a ln st st2\<close> assms(1) h set_ConsD)
              next 
                fix a x
                assume h: "x \<in> set (known_msgs_acc st2 a)"
                show "isValidMessage x"
                  by (smt (z3) Process1bLearnerLoopStep.elims(2) Store_acc.elims(2) TypeOK.elims(2) WellFormed.elims(1) assms(1) h p set_ConsD)
              next
                fix a x
                assume h: "x \<in> set (known_msgs_lrn st2 a)"
                show "isValidMessage x"
                  by (metis Process1bLearnerLoopStep.elims(2) Store_acc.elims(2) TypeOK.elims(2) assms(1) h p)
              next
                fix a x
                assume h: "x \<in> set (recent_msgs st2 a)"
                show "isValidMessage x"
                  by (smt (z3) Process1bLearnerLoopStep.elims(2) TypeOK.elims(2) WellFormed.elims(2) assms(1) empty_iff empty_set h p set_ConsD)
              next
                fix a y
                assume h: "queued_msg st2 a = Some y"
                show "isValidMessage (the (queued_msg st2 a))"
                  by (metis Process1bLearnerLoopStep.elims(2) TypeOK.elims(2) assms(1) h option.distinct(1) p)
              qed qed
            next
              assume p: "Process1bLearnerLoopDone a st st2"
              then show ?thesis
                unfolding TypeOK.simps
              proof (intro conjI; clarify)
                fix x
                assume h: "x \<in> set (msgs st2)"
                show "isValidMessage x"
                  using p h assms(1) by auto
              next 
                fix a x
                assume h: "x \<in> set (known_msgs_acc st2 a)"
                show "isValidMessage x"
                  using p h assms(1) by force
              next
                fix a x
                assume h: "x \<in> set (known_msgs_lrn st2 a)"
                show "isValidMessage x"
                  using p h assms(1) by force
              next
                fix a x
                assume h: "x \<in> set (recent_msgs st2 a)"
                show "isValidMessage x"
                  using p h assms(1) by force
              next
                fix a y
                assume h: "queued_msg st2 a = Some y"
                show "isValidMessage (the (queued_msg st2 a))"
                  using assms(1) h p by auto
              qed
            qed
          next
            case False
            have "(queued_msg st a \<noteq> None \<and>
                      Process1b a (the (queued_msg st a)) st st2 \<or>
                      queued_msg st a = None \<and>
                      (\<exists>m. Process1a a m st st2 \<or> Process1b a m st st2))"
              using False h by blast
            then show ?thesis
              proof (elim disjE)
                assume qp:"(queued_msg st a \<noteq> None) \<and>
                           (Process1b a (the (queued_msg st a)) st st2)"
                show ?thesis
                unfolding TypeOK.simps
                  proof (intro conjI; clarify)
                    fix x
                    assume h: "x \<in> set (msgs st2)"
                    show "isValidMessage x"
                      using qp h assms(1) by auto
                  next 
                    fix a x
                    assume h: "x \<in> set (known_msgs_acc st2 a)"
                    show "isValidMessage x"
                      by (smt (verit) Process1b.simps Store_acc.elims(2) TypeOK.elims(2) assms(1) h qp set_ConsD)
                  next
                    fix a x
                    assume h: "x \<in> set (known_msgs_lrn st2 a)"
                    show "isValidMessage x"
                      using qp h assms(1) by force
                  next
                    fix a x
                    assume h: "x \<in> set (recent_msgs st2 a)"
                    show "isValidMessage x"
                      by (smt (z3) Process1b.simps TypeOK.elims(1) assms(1) h qp set_ConsD)
                  next
                    fix a y
                    assume h: "queued_msg st2 a = Some y"
                    show "isValidMessage (the (queued_msg st2 a))"
                      by (smt (z3) Process1b.simps TypeOK.elims(1) assms(1) h option.distinct(1) qp)
                  qed
              next
                assume "queued_msg st a = None \<and>
                        (\<exists>m. Process1a a m st st2 \<or>
                             Process1b a m st st2)"
                then show ?thesis
                proof
                  have "\<exists>m. Process1a a m st st2 \<or> Process1b a m st st2"
                    using False h by blast
                  then show ?thesis
                  proof (elim exE)
                    fix m
                    assume "Process1a a m st st2 \<or> Process1b a m st st2"
                    then show ?thesis
                    proof (elim disjE)
                      assume p: "Process1a a m st st2"
                      show ?thesis
                        unfolding TypeOK.simps
                      proof (intro conjI; clarify)
                        fix x
                        assume h: "x \<in> set (msgs st2)"
                        have "Process1a a m st st2"
                          using p by blast
                        define new1b where "new1b = M1b a (m # recent_msgs st a)"
                        then show "isValidMessage x"
                        proof (cases "WellFormed st new1b")
                          case True
                          then show ?thesis
                            by (smt (z3) Process1a.elims(2) Send.elims(2) TypeOK.elims(2) WellFormed.elims(1) assms(1) h p set_ConsD)
                        next
                          case False
                          then show ?thesis
                            by (metis Process1a.elims(2) TypeOK.elims(2) assms(1) h new1b_def p)
                        qed  
                      next 
                        fix a x
                        assume h: "x \<in> set (known_msgs_acc st2 a)"
                        show "isValidMessage x"
                          by (metis Process1a.elims(2) Recv_acc.elims(2) Store_acc.elims(2) TypeOK.elims(2) WellFormed.elims(1) assms(1) h p set_ConsD)
                      next
                        fix a x
                        assume h: "x \<in> set (known_msgs_lrn st2 a)"
                        show "isValidMessage x"
                          by (metis Process1a.elims(2) Store_acc.elims(2) TypeOK.elims(2) assms(1) h p)
                      next
                        fix a x
                        assume h: "x \<in> set (recent_msgs st2 a)"
                        show "isValidMessage x"
                          by (metis (no_types, lifting) MessageType.distinct(1) MessageType.distinct(3) Process1a.elims(2) TypeOK.elims(2) assms(1) empty_iff empty_set h isValidMessage.simps(1) p set_ConsD type.elims)
                      next
                        fix a y
                        assume h: "queued_msg st2 a = Some y"
                        show "isValidMessage (the (queued_msg st2 a))"
                          by (metis (no_types, lifting) Process1a.elims(2) TypeOK.elims(2) WellFormed.simps assms(1) h option.distinct(1) option.sel p)
                      qed
                    next
                      assume p: "Process1b a m st st2"
                      show ?thesis
                        unfolding TypeOK.simps
                      proof (intro conjI; clarify)
                        fix x
                        assume h: "x \<in> set (msgs st2)"
                        show "isValidMessage x"
                          using assms(1) h p by fastforce
                      next 
                        fix a x
                        assume h: "x \<in> set (known_msgs_acc st2 a)"
                        show "isValidMessage x"
                          by (smt (verit, ccfv_threshold) Process1b.simps Recv_acc.elims(2) Store_acc.elims(2) TypeOK.elims(2) WellFormed.elims(2) assms(1) h p set_ConsD)
                      next
                        fix a x
                        assume h: "x \<in> set (known_msgs_lrn st2 a)"
                        show "isValidMessage x"
                          using assms(1) h p by fastforce
                      next
                        fix a x
                        assume h: "x \<in> set (recent_msgs st2 a)"
                        show "isValidMessage x"
                          by (smt (verit, best) Process1b.simps Recv_acc.elims(2) TypeOK.elims(2) WellFormed.elims(1) assms(1) h p set_ConsD)
                      next
                        fix a y
                        assume h: "queued_msg st2 a = Some y"
                        show "isValidMessage (the (queued_msg st2 a))"
                          by (smt (z3) Process1b.simps TypeOK.elims(1) assms(1) h option.distinct(1) p)
                      qed
                    qed
                  qed
                qed
              qed
          qed
      qed
  next
    assume "LearnerProcessAction st st2"
    show ?thesis
      unfolding TypeOK.simps
      proof (intro conjI; clarify)
      fix x
      assume h: "x \<in> set (msgs st2)"
      show "isValidMessage x"
        by (metis (no_types, lifting) LearnerProcessAction.simps LearnerAction.simps LearnerDecide.elims(2) LearnerRecv.elims(2) TypeOK.simps \<open>LearnerProcessAction st st2\<close> assms(1) ext_inject h surjective update_convs(3) update_convs(8))
    next 
      fix a x
      assume h: "x \<in> set (known_msgs_acc st2 a)"
      show "isValidMessage x"
        by (metis (no_types, lifting) LearnerProcessAction.simps LearnerAction.simps LearnerDecide.elims(2) LearnerRecv.elims(2) TypeOK.elims(2) \<open>LearnerProcessAction st st2\<close> assms(1) ext_inject h surjective update_convs(3) update_convs(8))
    next
      fix a x
      assume h: "x \<in> set (known_msgs_lrn st2 a)"
      have "LearnerProcessAction st st2"
        using \<open>LearnerProcessAction st st2\<close> by blast
      then show "isValidMessage x"
        unfolding LearnerProcessAction.simps LearnerAction.simps
      proof (elim exE)
        fix ln
        assume "(\<exists>m \<in> set (msgs st). LearnerRecv ln m st st2) \<or>
                (\<exists>blt val.
                    LearnerDecide ln blt val st
                     st2)"
        then show "isValidMessage x"
        proof (elim disjE)
          assume "\<exists>m \<in> set (msgs st). LearnerRecv ln m st st2"
          have "\<exists>m. LearnerRecv ln m st st2"
            using \<open>\<exists>m\<in>set (msgs st). LearnerRecv ln m st st2\<close> by blast
          then show ?thesis
          proof (elim exE)
            fix m
            assume "LearnerRecv ln m st st2"
            then show ?thesis
              by (smt (z3) LearnerRecv.elims(2) Recv_lrn.elims(2) TypeOK.elims(2) WellFormed.elims(1) assms(1) h set_ConsD simps(3) surjective update_convs(3))
          qed
        next
          assume "\<exists>blt val. LearnerDecide ln blt val st st2"
          then show ?thesis
            by (metis (no_types, lifting) LearnerDecide.elims(2) TypeOK.elims(2) assms(1) ext_inject h surjective update_convs(8))
        qed
    qed
    next
      fix a x
      assume h: "x \<in> set (recent_msgs st2 a)"
      show "isValidMessage x"
        by (metis (no_types, lifting) LearnerProcessAction.simps LearnerAction.simps LearnerDecide.elims(2) LearnerRecv.elims(2) TypeOK.elims(2) \<open>LearnerProcessAction st st2\<close> assms(1) ext_inject h surjective update_convs(3) update_convs(8))
    next
      fix a y
      assume h: "queued_msg st2 a = Some y"
      show "isValidMessage (the (queued_msg st2 a))"
        by (metis (no_types, lifting) LearnerProcessAction.simps LearnerAction.simps LearnerDecide.elims(2) LearnerRecv.elims(2) TypeOK.elims(2) \<open>LearnerProcessAction st st2\<close> assms(1) ext_inject h option.distinct(1) surjective update_convs(3) update_convs(8))
    qed
  next
    assume "FakeAcceptorAction st st2"
    then show ?thesis
      unfolding FakeAcceptorAction.simps TypeOK.simps
    proof (intro conjI; clarify)
      fix x a
      assume h: "x \<in> set (msgs st2)"
      assume "FakeSend1b a st st2 \<or> FakeSend2a a st st2"
      then show "isValidMessage x"
      proof (elim disjE)
        assume "FakeSend1b a st st2"
        then show ?thesis 
          unfolding FakeSend1b.simps
          by (metis (no_types, lifting) TypeOK.elims(1) WellFormed.elims(1) assms(1) h select_convs(1) set_ConsD surjective update_convs(1))
      next
        assume "FakeSend2a a st st2"
        then show ?thesis
          unfolding FakeSend2a.simps
          by (metis (no_types, lifting) TypeOK.elims(1) WellFormed.elims(1) assms(1) h select_convs(1) set_ConsD surjective update_convs(1))
      qed
    next
      fix a x
      assume h: "x \<in> set (known_msgs_acc st2 a)"
      show "isValidMessage x"
        by (metis FakeAcceptorAction.elims(2) FakeSend1b.simps FakeSend2a.simps TypeOK.elims(2) \<open>FakeAcceptorAction st st2\<close> assms(1) h select_convs(2) surjective update_convs(1))
    next
      fix a x
      assume h: "x \<in> set (known_msgs_lrn st2 a)"
      show "isValidMessage x"
        by (metis FakeAcceptorAction.elims(2) FakeSend1b.simps FakeSend2a.simps TypeOK.elims(2) \<open>FakeAcceptorAction st st2\<close> assms(1) ext_inject h surjective update_convs(1))
    next
      fix a x
      assume h: "x \<in> set (recent_msgs st2 a)"
      show "isValidMessage x"
        by (metis FakeAcceptorAction.elims(2) FakeSend1b.simps FakeSend2a.simps TypeOK.elims(2) \<open>FakeAcceptorAction st st2\<close> assms(1) ext_inject h surjective update_convs(1))
    next
      fix a y
      assume h: "queued_msg st2 a = Some y"
      show "isValidMessage (the (queued_msg st2 a))"
        by (metis FakeAcceptorAction.elims(2) FakeSend1b.elims(2) FakeSend2a.simps TypeOK.elims(2) \<open>FakeAcceptorAction st st2\<close> assms(1) ext_inject h option.distinct(1) surjective update_convs(1))
    qed
  qed
next

qed

lemma RecentMsgsaccSpecInvariant :
  assumes "RecentMsgsSpec st"
  assumes "Next st st2"
  shows "RecentMsgsSpec st2"
unfolding RecentMsgsSpec.simps
proof 
  fix a2
  show "is_safe a2 \<longrightarrow> set (recent_msgs st2 a2) \<subseteq> set (known_msgs_acc st2 a2)"
  proof (rule impI)
  assume "is_safe a2"
  have "Next st st2"
    using assms(2) by blast
  then show "set (recent_msgs st2 a2) \<subseteq> set (known_msgs_acc st2 a2)"
    unfolding Next.simps
  proof (elim disjE)
    assume "ProposerSendAction st st2"
    show ?thesis
      using \<open>ProposerSendAction st st2\<close> \<open>is_safe a2\<close> assms(1) by fastforce
  next
    assume "AcceptorProcessAction st st2"
    then show ?thesis
      unfolding AcceptorProcessAction.simps AcceptorAction.simps
      proof (elim exE)
        fix a
        assume h:"is_safe a \<and>
                  (\<not> two_a_lrn_loop st a \<and>
                   (queued_msg st a \<noteq> None \<and>
                    Process1b a (the (queued_msg st a)) st st2 \<or>
                    queued_msg st a = None \<and>
                    (\<exists>m \<in> set (msgs st). Process1a a m st st2 \<or> Process1b a m st st2)) \<or>
                   two_a_lrn_loop st a \<and> Process1bLearnerLoop a st st2)"
        show ?thesis
        proof (cases "two_a_lrn_loop st a")
            case True
            have "Process1bLearnerLoop a st st2" 
              using True h by blast
            then show ?thesis
            unfolding Process1bLearnerLoop.simps
            proof (elim disjE)
              assume "\<exists>ln. ln \<notin> processed_lrns st a \<and>
                        Process1bLearnerLoopStep a ln st st2"
              then show ?thesis
                by (smt (verit, best) Process1bLearnerLoopStep.elims(2) RecentMsgsSpec.elims(1) Store_acc.elims(2) \<open>is_safe a2\<close> assms(1) empty_iff empty_set list.set_intros(1) set_ConsD subsetI)
            next
              assume "Process1bLearnerLoopDone a st st2"
              then show ?thesis
                using \<open>is_safe a2\<close> assms(1) by auto
            qed
          next
            case False
            have "(queued_msg st a \<noteq> None \<and>
                      Process1b a (the (queued_msg st a)) st st2 \<or>
                      queued_msg st a = None \<and>
                      (\<exists>m. Process1a a m st st2 \<or> Process1b a m st st2))"
              using False h by blast
            then show ?thesis
              proof (elim disjE)
                assume "queued_msg st a \<noteq> None \<and>
                        Process1b a (the (queued_msg st a))
                         st st2"
                then show ?thesis
                  using \<open>is_safe a2\<close> assms(1) by auto
              next
                assume "queued_msg st a = None \<and>
                        (\<exists>m. Process1a a m st st2 \<or>
                             Process1b a m st st2)"
                then show ?thesis
                proof
                  have "\<exists>m. Process1a a m st st2 \<or> Process1b a m st st2"
                    using False h by blast
                  then show ?thesis
                  proof (elim exE)
                    fix m
                    assume "Process1a a m st st2 \<or> Process1b a m st st2"
                    then show ?thesis
                    proof (elim disjE)
                      assume "Process1a a m st st2"
                      then show ?thesis
                        by (smt (verit, best) Process1a.elims(2) RecentMsgsSpec.elims(1) Store_acc.elims(2) \<open>is_safe a2\<close> assms(1) empty_iff insert_iff list.set(1) list.simps(15) subsetD subsetI)
                    next
                      assume "Process1b a m st st2"
                      then show ?thesis
                        using \<open>is_safe a2\<close> assms(1) by auto
                    qed
                  qed
                qed
              qed
          qed
      qed
  next
    assume "LearnerProcessAction st st2"
    then show ?thesis
      unfolding LearnerProcessAction.simps LearnerAction.simps
    proof (elim exE)
      fix ln
      assume "(\<exists>m \<in> set (msgs st). LearnerRecv ln m st st2) \<or>
              (\<exists>blt val. LearnerDecide ln blt val st st2)"
      then show ?thesis
      proof (elim disjE)
        assume "\<exists>m \<in> set (msgs st). LearnerRecv ln m st st2"
        have "\<exists>m. LearnerRecv ln m st st2"
          using \<open>\<exists>m\<in>set (msgs st). LearnerRecv ln m st st2\<close> by blast
        then show ?thesis
          by (metis (no_types, lifting) LearnerRecv.elims(2) RecentMsgsSpec.elims(1) \<open>is_safe a2\<close> assms(1) ext_inject surjective update_convs(3))
      next
        assume "\<exists>blt val. LearnerDecide ln blt val st st2"
        then show ?thesis
          by (metis (no_types, lifting) LearnerDecide.elims(2) RecentMsgsSpec.simps \<open>is_safe a2\<close> assms(1) ext_inject surjective update_convs(8))
      qed
    qed
  next
    assume "FakeAcceptorAction st st2"
    then show ?thesis
      by (metis FakeAcceptorAction.elims(2) FakeSend1b.elims(2) FakeSend2a.simps RecentMsgsSpec.simps \<open>is_safe a2\<close> assms(1) ext_inject surjective update_convs(1))
  qed
qed
qed


lemma QueuedMsgSpecInvariant :
  assumes "twoaLearnerLoopSpec st"
  assumes "QueuedMsgSpec1 st"
  assumes "Next st st2"
  shows "QueuedMsgSpec1 st2"
  unfolding twoaLearnerLoopSpec.simps QueuedMsgSpec1.simps
proof 
  fix a2
  show "is_safe a2 \<and> queued_msg st2 a2 \<noteq> None \<longrightarrow>
         type (the (queued_msg st2 a2)) = T1b \<and>
         the (queued_msg st2 a2) \<in> set (msgs st2) \<and>
         recent_msgs st2 a2 = []"
  proof (rule impI)
  assume "is_safe a2 \<and>queued_msg st2 a2 \<noteq> None"
  have "Next st st2"
    using assms(3) by blast
  then show "type (the (queued_msg st2 a2)) = T1b \<and>
             the (queued_msg st2 a2) \<in> set (msgs st2) \<and>
             recent_msgs st2 a2 = []"
    unfolding Next.simps
  proof (elim disjE)
    assume "ProposerSendAction st st2"
    show ?thesis
      using \<open>ProposerSendAction st st2\<close> \<open>is_safe a2 \<and> queued_msg st2 a2 \<noteq> None\<close> assms(2) by force
  next
    assume "AcceptorProcessAction st st2"
    then show ?thesis
      unfolding AcceptorProcessAction.simps AcceptorAction.simps
      proof (elim exE)
        fix a
        assume h: "is_safe a \<and>
                  (\<not> two_a_lrn_loop st a \<and>
                   (queued_msg st a \<noteq> None \<and>
                    Process1b a (the (queued_msg st a)) st st2 \<or>
                    queued_msg st a = None \<and>
                    (\<exists>m \<in> set (msgs st). Process1a a m st st2 \<or> Process1b a m st st2)) \<or>
                   two_a_lrn_loop st a \<and> Process1bLearnerLoop a st st2)"
        show ?thesis
        proof (cases "two_a_lrn_loop st a")
            case True
            have "Process1bLearnerLoop a st st2" 
              using True h by blast
            then show ?thesis
            unfolding Process1bLearnerLoop.simps
            proof (elim disjE)
              assume "\<exists>ln. ln \<notin> processed_lrns st a \<and>
                        Process1bLearnerLoopStep a ln st st2"
              then show ?thesis
                by (smt (z3) Process1bLearnerLoopStep.elims(2) QueuedMsgSpec1.elims(1) Send.elims(2) True \<open>is_safe a2 \<and> queued_msg st2 a2 \<noteq> None\<close> assms(1) assms(2) list.set_intros(2) twoaLearnerLoopSpec.elims(1))
            next
              assume "Process1bLearnerLoopDone a st st2"
              then show ?thesis
                using \<open>is_safe a2 \<and> queued_msg st2 a2 \<noteq> None\<close> assms(2) by auto
            qed
          next
            case False
            have "(queued_msg st a \<noteq> None \<and>
                      Process1b a (the (queued_msg st a)) st st2 \<or>
                      queued_msg st a = None \<and>
                      (\<exists>m. Process1a a m st st2 \<or> Process1b a m st st2))"
              using False h by blast
            then show ?thesis
              proof (elim disjE)
                assume "queued_msg st a \<noteq> None \<and>
                        Process1b a (the (queued_msg st a))
                         st st2"
                then show ?thesis
                  by (smt (verit, best) Process1b.simps QueuedMsgSpec1.elims(1) \<open>is_safe a2 \<and> queued_msg st2 a2 \<noteq> None\<close> assms(2))
              next
                assume "queued_msg st a = None \<and>
                        (\<exists>m. Process1a a m st st2 \<or>
                             Process1b a m st st2)"
                then show ?thesis
                proof
                  have "\<exists>m. Process1a a m st st2 \<or> Process1b a m st st2"
                    using False h by blast
                  then show ?thesis
                  proof (elim exE)
                    fix m
                    assume "Process1a a m st st2 \<or> Process1b a m st st2"
                    then show ?thesis
                    proof (elim disjE)
                      assume "Process1a a m st st2"
                      then show ?thesis
                        by (smt (z3) Process1a.elims(2) QueuedMsgSpec1.elims(1) Send.elims(2) \<open>is_safe a2 \<and> queued_msg st2 a2 \<noteq> None\<close> \<open>queued_msg st a = None \<and> (\<exists>m. Process1a a m st st2 \<or> Process1b a m st st2)\<close> assms(2) insert_iff list.simps(15) option.sel type.simps(2))
                    next
                      assume "Process1b a m st st2"
                      then show ?thesis
                        by (smt (verit, ccfv_threshold) Process1b.simps QueuedMsgSpec1.elims(1) \<open>is_safe a2 \<and> queued_msg st2 a2 \<noteq> None\<close> assms(2))
                    qed
                  qed
                qed
              qed
          qed
      qed
  next
    assume "LearnerProcessAction st st2"
    then show ?thesis
      unfolding LearnerProcessAction.simps LearnerAction.simps
    proof (elim exE)
      fix ln
      assume "(\<exists>m \<in> set (msgs st). LearnerRecv ln m st st2) \<or>
              (\<exists>blt val. LearnerDecide ln blt val st st2)"
      then show ?thesis
      proof (elim disjE)
        assume "\<exists>m \<in> set (msgs st). LearnerRecv ln m st st2"
        have "\<exists>m. LearnerRecv ln m st st2"
          using \<open>\<exists>m\<in>set (msgs st). LearnerRecv ln m st st2\<close> by blast
        then show ?thesis
          by (smt (z3) LearnerRecv.elims(2) QueuedMsgSpec1.elims(1) \<open>is_safe a2 \<and> queued_msg st2 a2 \<noteq> None\<close> assms(2) ext_inject surjective update_convs(3))
      next
        assume "\<exists>blt val. LearnerDecide ln blt val st st2"
        then show ?thesis
          by (smt (verit, ccfv_SIG) LearnerDecide.elims(2) QueuedMsgSpec1.elims(1) \<open>is_safe a2 \<and> queued_msg st2 a2 \<noteq> None\<close> assms(2) ext_inject surjective update_convs(8))
      qed
    qed
  next
    assume "FakeAcceptorAction st st2"
    then show ?thesis
      by (smt (z3) FakeAcceptorAction.elims(2) FakeSend1b.elims(2) FakeSend2a.simps QueuedMsgSpec1.elims(1) \<open>is_safe a2 \<and> queued_msg st2 a2 \<noteq> None\<close> assms(2) ext_inject list.set_intros(2) surjective update_convs(1))
  qed
qed
qed

lemma twoaLearnerLoopSpecInvariant :
  assumes "twoaLearnerLoopSpec st"
  assumes "Next st st2"
  shows "twoaLearnerLoopSpec st2"
  unfolding twoaLearnerLoopSpec.simps
proof 
  fix a2
  show "is_safe a2 \<and> two_a_lrn_loop st2 a2 \<longrightarrow> queued_msg st2 a2 = None"
  proof (rule impI)
  assume "is_safe a2 \<and> two_a_lrn_loop st2 a2"
  have "Next st st2"
    using assms(2) by blast
  then show "queued_msg st2 a2 = None"
    unfolding Next.simps
  proof (elim disjE)
    assume "ProposerSendAction st st2"
    show ?thesis
      using \<open>ProposerSendAction st st2\<close> \<open>is_safe a2 \<and> two_a_lrn_loop st2 a2\<close> assms(1) by auto
  next
    assume "AcceptorProcessAction st st2"
    then show ?thesis
      unfolding AcceptorProcessAction.simps AcceptorAction.simps
      proof (elim exE)
        fix a
        assume h: "is_safe a \<and>
                  (\<not> two_a_lrn_loop st a \<and>
                   (queued_msg st a \<noteq> None \<and>
                    Process1b a (the (queued_msg st a)) st st2 \<or>
                    queued_msg st a = None \<and>
                    (\<exists>m \<in> set (msgs st). Process1a a m st st2 \<or> Process1b a m st st2)) \<or>
                   two_a_lrn_loop st a \<and> Process1bLearnerLoop a st st2)"
        show ?thesis
        proof (cases "two_a_lrn_loop st a")
          case True
          have "queued_msg st2 = queued_msg st"
            by (smt (verit) Process1bLearnerLoop.simps Process1bLearnerLoopDone.elims(2) Process1bLearnerLoopStep.elims(2) True ext_inject h surjective update_convs(6))
          show ?thesis
            by (smt (verit, del_insts) Process1bLearnerLoop.simps Process1bLearnerLoopDone.elims(2) Process1bLearnerLoopStep.elims(2) True \<open>is_safe a2 \<and> two_a_lrn_loop st2 a2\<close> assms(1) ext_inject h surjective twoaLearnerLoopSpec.elims(2) update_convs(6))
        next
          case False
          have "(queued_msg st a \<noteq> None \<and>
                    Process1b a (the (queued_msg st a)) st st2 \<or>
                    queued_msg st a = None \<and>
                    (\<exists>m. Process1a a m st st2 \<or> Process1b a m st st2))"
            using False h by blast
          then show ?thesis
            by (smt (z3) False Process1a.elims(2) Process1b.simps \<open>is_safe a2 \<and> two_a_lrn_loop st2 a2\<close> assms(1) twoaLearnerLoopSpec.elims(1))
          qed
        qed
  next
    assume "LearnerProcessAction st st2"
    then show ?thesis
      unfolding LearnerProcessAction.simps LearnerAction.simps
    proof (elim exE)
      fix ln
      assume "(\<exists>m \<in> set (msgs st). LearnerRecv ln m st st2) \<or>
              (\<exists>blt val. LearnerDecide ln blt val st st2)"
      then show ?thesis
      using \<open>is_safe a2 \<and> two_a_lrn_loop st2 a2\<close> assms(1) by auto
    qed
  next
    assume "FakeAcceptorAction st st2"
    then show ?thesis
      by (metis FakeAcceptorAction.elims(2) FakeSend1b.elims(2) FakeSend2a.simps \<open>is_safe a2 \<and> two_a_lrn_loop st2 a2\<close> assms(1) ext_inject surjective twoaLearnerLoopSpec.elims(2) update_convs(1))
  qed
qed
qed

lemma DecisionSpecInvariant :
  assumes "DecisionSpec st"
  assumes "Next st st2"
  shows "DecisionSpec st2"
unfolding DecisionSpec.simps
proof (clarify)
  fix l b v
  assume "v \<in> decision st2 l b"
  have "v \<in> decision st l b \<Longrightarrow> ChosenIn st l b v"
    using assms(1) by auto
  have "Next st st2"
    using assms(2) by blast
  then show "ChosenIn st2 l b v"
    unfolding Next.simps
  proof (elim disjE)
    assume "ProposerSendAction st st2"
    have "decision st2 l b = decision st l b"
      using \<open>ProposerSendAction st st2\<close> by force
    then show ?thesis
      using \<open>ProposerSendAction st st2\<close> \<open>v \<in> decision st l b \<Longrightarrow> ChosenIn st l b v\<close> \<open>v \<in> decision st2 l b\<close> subset_iff by fastforce
  next
    assume "AcceptorProcessAction st st2"
    then show ?thesis
      unfolding AcceptorProcessAction.simps AcceptorAction.simps
      proof (elim exE)
        fix a
        assume h: "is_safe a \<and>
                  (\<not> two_a_lrn_loop st a \<and>
                   (queued_msg st a \<noteq> None \<and>
                    Process1b a (the (queued_msg st a)) st st2 \<or>
                    queued_msg st a = None \<and>
                    (\<exists>m \<in> set (msgs st). Process1a a m st st2 \<or> Process1b a m st st2)) \<or>
                   two_a_lrn_loop st a \<and> Process1bLearnerLoop a st st2)"
        show ?thesis
          proof (cases "two_a_lrn_loop st a")
            case True
            have "Process1bLearnerLoop a st st2" 
              using True h by blast
            then show ?thesis
              unfolding Process1bLearnerLoop.simps
            proof (elim disjE)
              assume "\<exists>ln. ln \<notin> processed_lrns st a \<and>
                           Process1bLearnerLoopStep a ln st st2"
              then show ?thesis
                by (smt (verit, del_insts) ChosenIn.elims(1) Collect_cong Known2a.simps Process1bLearnerLoopStep.elims(2) Store_acc.elims(2) V.simps \<open>v \<in> decision st l b \<Longrightarrow> ChosenIn st l b v\<close> \<open>v \<in> decision st2 l b\<close>)
            next
              assume "Process1bLearnerLoopDone a st st2"
              then show ?thesis
                using \<open>v \<in> decision st l b \<Longrightarrow> ChosenIn st l b v\<close> \<open>v \<in> decision st2 l b\<close> by force
            qed
          next
            case False
            have "(queued_msg st a \<noteq> None \<and>
                      Process1b a (the (queued_msg st a)) st st2 \<or>
                      queued_msg st a = None \<and>
                      (\<exists>m. Process1a a m st st2 \<or> Process1b a m st st2))"
              using False h by blast
            then show ?thesis
              proof (elim disjE)
                assume "queued_msg st a \<noteq> None \<and>
                        Process1b a (the (queued_msg st a))
                         st st2"
                then show ?thesis
                  using \<open>v \<in> decision st l b \<Longrightarrow> ChosenIn st l b v\<close> \<open>v \<in> decision st2 l b\<close> by force
              next
                assume "queued_msg st a = None \<and>
                        (\<exists>m. Process1a a m st st2 \<or>
                             Process1b a m st st2)"
                then show ?thesis
                  by (smt (verit) ChosenIn.elims(1) Known2a.simps Process1a.elims(2) Process1b.simps Store_acc.elims(2) V.simps \<open>v \<in> decision st l b \<Longrightarrow> ChosenIn st l b v\<close> \<open>v \<in> decision st2 l b\<close> mem_Collect_eq subsetD subsetI)                
              qed
          qed
      qed
  next
    assume "LearnerProcessAction st st2"
    then show ?thesis
      unfolding LearnerProcessAction.simps LearnerAction.simps
    proof (elim exE)
      fix ln
      assume "(\<exists>m\<in>set (msgs st). LearnerRecv ln m st st2) \<or>
              (\<exists>blt val. LearnerDecide ln blt val st st2)"
      then show ?thesis
      proof (elim disjE)
        assume "\<exists>m\<in>set (msgs st). LearnerRecv ln m st st2"
        then show ?thesis
          by (smt (verit) ChosenIn.elims(1) Known2a.simps LearnerRecv.elims(2) V.simps \<open>v \<in> decision st l b \<Longrightarrow> ChosenIn st l b v\<close> \<open>v \<in> decision st2 l b\<close> ext_inject list.set_intros(2) mem_Collect_eq subsetD subsetI surjective update_convs(3))
      next
        assume "\<exists>blt val. LearnerDecide ln blt val st st2"
        then show ?thesis
        proof (clarify)
          fix blt val
          assume "LearnerDecide ln blt val st st2"
          then show ?thesis
            unfolding LearnerDecide.simps
            by (smt (verit, ccfv_threshold) ChosenIn.elims(2) ChosenIn.elims(3) Known2a.simps V.simps \<open>v \<in> decision st l b \<Longrightarrow> ChosenIn st l b v\<close> \<open>v \<in> decision st2 l b\<close> ext_inject insertE insert_is_Un mem_Collect_eq subsetD subsetI surjective update_convs(8))
        qed
      qed
    qed
  next
    assume "FakeAcceptorAction st st2"
    then show ?thesis
      by (smt (z3) ChosenIn.elims(1) Collect_cong FakeAcceptorAction.elims(2) FakeSend1b.elims(2) FakeSend2a.simps Known2a.simps V.simps \<open>v \<in> decision st l b \<Longrightarrow> ChosenIn st l b v\<close> \<open>v \<in> decision st2 l b\<close> ext_inject surjective update_convs(1))
  qed
qed


lemma Acceptor_split:
  assumes "AcceptorProcessAction st st2"
  shows "(\<exists>A :: Acceptor. is_safe A
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
                        \<and> Process1bLearnerLoopDone A st st2)"
  by (metis AcceptorAction.elims(2) AcceptorProcessAction.elims(2) Process1bLearnerLoop.elims(2) assms)

lemma Acceptor_split_full:
  assumes "AcceptorProcessAction st st2"
  shows "(\<exists>A :: Acceptor. is_safe A
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
                        \<and> (\<exists>l :: Learner. l \<notin> processed_lrns st A \<and> Process1bLearnerLoopStep A l st st2)) \<or>
          (\<exists>A :: Acceptor. is_safe A
                        \<and> two_a_lrn_loop st A 
                        \<and> Process1bLearnerLoopDone A st st2)"
  by (metis AcceptorAction.elims(2) AcceptorProcessAction.elims(2) Process1bLearnerLoop.elims(2) assms)


lemma next_split:
  assumes "Next st st2"
  shows "ProposerSendAction st st2 \<or>
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
                        \<and> FakeSend2a A st st2)"
proof -
  have "Next st st2"
    using assms(1) by blast
  then show ?thesis
    unfolding Next.simps
  proof (elim disjE)
    assume "ProposerSendAction st st2"
    then show ?thesis
      by blast
  next
    assume "AcceptorProcessAction st st2"
    then show ?thesis
      by (metis AcceptorAction.simps AcceptorProcessAction.elims(2) Process1bLearnerLoop.simps)
  next
    assume "LearnerProcessAction st st2"
    then show ?thesis
      by blast
  next
    assume "FakeAcceptorAction st st2"
    then show ?thesis
      by (meson FakeAcceptorAction.elims(2))
  qed
qed

lemma next_split_full:
  assumes "Next st st2"
  shows "ProposerSendAction st st2 \<or>
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
                        \<and> (\<exists>l :: Learner. l \<notin> processed_lrns st A \<and> Process1bLearnerLoopStep A l st st2)) \<or>
          (\<exists>A :: Acceptor. is_safe A
                        \<and> two_a_lrn_loop st A 
                        \<and> Process1bLearnerLoopDone A st st2) \<or>
          LearnerProcessAction st st2 \<or>
          (\<exists>A :: Acceptor. \<not> (is_safe A)
                        \<and> FakeSend1b A st st2) \<or>
          (\<exists>A :: Acceptor. \<not> (is_safe A)
                        \<and> FakeSend2a A st st2)"
proof -
  have "Next st st2"
    using assms(1) by blast
  then show ?thesis
    unfolding Next.simps
  proof (elim disjE)
    assume "ProposerSendAction st st2"
    then show ?thesis
      by blast
  next
    assume "AcceptorProcessAction st st2"
    then show ?thesis
      by (metis AcceptorAction.simps AcceptorProcessAction.elims(2) Process1bLearnerLoop.simps)
  next
    assume "LearnerProcessAction st st2"
    then show ?thesis
      by blast
  next
    assume "FakeAcceptorAction st st2"
    then show ?thesis
      by (meson FakeAcceptorAction.elims(2))
  qed
qed

lemma SafeAcceptorOwnMessagesRefsSpecInvariant :
  assumes "twoaLearnerLoopSpec st"
  assumes "SafeAcceptorOwnMessagesRefsSpec st"
  assumes "Next st st2"
  shows "SafeAcceptorOwnMessagesRefsSpec st2"
  unfolding SafeAcceptorOwnMessagesRefsSpec.simps
proof (clarify)
  fix A
  assume "is_safe A"
         "SentBy st2 A \<noteq> {}"
  have "\<exists>m :: PreMessage. m \<in> SentBy st2 A"
    using \<open>SentBy st2 A \<noteq> {}\<close> by blast
  then show "(queued_msg st2 A = None \<longrightarrow>
             (\<exists>m0\<in>set (recent_msgs st2 A).
              \<forall>m1\<in>SentBy st2 A. m1 \<in> Tran m0)) \<and>
         (queued_msg st2 A \<noteq> None \<longrightarrow>
          (\<forall>m1\<in>SentBy st2 A. m1 \<in> Tran (the (queued_msg st2 A))))"
  proof (elim exE)
    fix mm
    assume "mm \<in> SentBy st2 A"
    have css: "ProposerSendAction st st2 \<or>
          (\<exists>A :: Acceptor. is_safe A
                      \<and> queued_msg st A = None 
                      \<and> (\<exists>m :: PreMessage. Process1a A m st st2)) \<or>
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
      by (smt (verit, del_insts) assms(3) next_split)
    then show ?thesis
    proof (elim disjE)
      assume "ProposerSendAction st st2"
      then show ?thesis
      unfolding ProposerSendAction.simps
      proof (elim exE)
        fix blt
        assume "Send1a blt st st2"
        show ?thesis
        proof (cases "queued_msg st2 A = None")
          case True
          have h: "\<exists>m0\<in>set (recent_msgs st2 A). \<forall>m1\<in>SentBy st2 A. m1 \<in> Tran m0"
            using True \<open>Send1a blt st st2\<close> \<open>SentBy st2 A \<noteq> {}\<close> \<open>is_safe A\<close> assms(2) surjective by fastforce
          show ?thesis
            using True h by blast 
        next
          case False
          have h: "\<forall>m1\<in>SentBy st2 A. m1 \<in> Tran (the (queued_msg st2 A))"
            using False \<open>Send1a blt st st2\<close> \<open>SentBy st2 A \<noteq> {}\<close> \<open>is_safe A\<close> assms(2) surjective by fastforce
          show ?thesis
            using False h by blast
        qed
      qed
    next
      assume "\<exists>A :: Acceptor. is_safe A
                  \<and> queued_msg st A = None 
                  \<and> (\<exists>m :: PreMessage. Process1a A m st st2)"
      then show ?thesis
      proof (elim exE)
        fix acc
        assume h0: "is_safe acc \<and>
                 queued_msg st acc = None \<and>
                 (\<exists>m. Process1a acc m st st2)"
        have "\<exists>m. Process1a acc m st st2"
          using h0 by fastforce
        then show ?thesis
          proof (elim exE)
            fix m1a
            assume "Process1a acc m1a st st2"
            then show ?thesis
            proof (cases "acc \<noteq> A")
              case True
              have "SentBy st A = SentBy st2 A"
                by (smt (verit) Collect_cong Process1a.elims(2) Send.elims(2) SentBy.elims True \<open>Process1a acc m1a st st2\<close> hpaxos.acc.simps(2) insert_iff list.simps(15))
              show ?thesis
              proof -
                have "\<forall>a. queued_msg st2 = queued_msg st \<or> queued_msg st a = queued_msg st2 a \<or> acc = a"
                  by (metis (no_types) Process1a.elims(2) \<open>Process1a acc m1a st st2\<close>)
                then show ?thesis
                  by (metis (no_types) Process1a.elims(2) SafeAcceptorOwnMessagesRefsSpec.elims(2) True \<open>Process1a acc m1a st st2\<close> \<open>SentBy st A = SentBy st2 A\<close> \<open>SentBy st2 A \<noteq> {}\<close> \<open>is_safe A\<close> assms(2))
              qed
            next
              case False
              have "acc = A"
                using False by blast
              show ?thesis
              proof (cases "mm \<in> set (msgs st)")
                case True
                have "\<exists>m0 :: PreMessage. m0 \<in> set (recent_msgs st A) \<and>
                        (\<forall> m1 \<in> SentBy st A. m1 \<in> Tran(m0))"
                  using False True \<open>mm \<in> SentBy st2 A\<close> assms(2) h0 by auto
                then show ?thesis
                  by (smt (verit, del_insts) False Process1a.elims(2) Send.elims(2) SentBy.simps Set.set_insert Tran.simps(2) Un_iff Union_image_insert h0 insert_iff list.simps(15) mem_Collect_eq option.distinct(1) option.sel)
              next
                case False
                assume "mm \<notin> set (msgs st)"
                define new1b where "new1b = M1b acc (m1a # recent_msgs st acc)"
                have "WellFormed st new1b"
                  by (metis (mono_tags, lifting) False Process1a.elims(2) SentBy.elims \<open>Process1a acc m1a st st2\<close> \<open>mm \<in> SentBy st2 A\<close> mem_Collect_eq new1b_def)
                have "\<forall>m \<in> SentBy st2 A. m = new1b \<or> m \<in> SentBy st A"
                  by (metis (no_types, lifting) Process1a.elims(2) Send.elims(2) SentBy.elims \<open>Process1a acc m1a st st2\<close> mem_Collect_eq new1b_def set_ConsD)
                show ?thesis
                  by (smt (verit, del_insts) Process1a.elims(2) SafeAcceptorOwnMessagesRefsSpec.simps Tran.simps(2) UN_I Un_iff \<open>Process1a acc m1a st st2\<close> \<open>WellFormed st new1b\<close> \<open>\<forall>m\<in>SentBy st2 A. m = new1b \<or> m \<in> SentBy st A\<close> \<open>acc = A\<close> assms(2) h0 insert_iff new1b_def option.discI option.sel set_subset_Cons subset_code(1))
              qed
            qed
          qed
      qed
    next
      assume "\<exists>A :: Acceptor. is_safe A
                        \<and> queued_msg st A \<noteq> None 
                        \<and> Process1b A (the (queued_msg st A)) st st2"
      then show ?thesis
      proof (elim exE)
        fix acc
        assume "is_safe acc \<and>
                queued_msg st acc \<noteq> None \<and>
                Process1b acc (the (queued_msg st acc)) st st2"
        then show ?thesis
          by (smt (verit) Collect_cong Process1b.simps SafeAcceptorOwnMessagesRefsSpec.elims(2) SentBy.elims \<open>SentBy st2 A \<noteq> {}\<close> \<open>is_safe A\<close> assms(2) list.set_intros(1))
      qed
    next
      assume "\<exists>A :: Acceptor. is_safe A
                  \<and> queued_msg st A = None 
                  \<and> (\<exists>m \<in> set (msgs st). Process1b A m st st2)"
      then show ?thesis
        proof (elim exE)
          fix acc
          assume "is_safe acc \<and>
                  queued_msg st acc = None \<and>
                  (\<exists>m\<in>set (msgs st). Process1b acc m st st2)"
          show ?thesis
            by (smt (verit, ccfv_threshold) Process1b.simps SafeAcceptorOwnMessagesRefsSpec.elims(2) SentBy.elims \<open>is_safe A\<close> \<open>is_safe acc \<and> queued_msg st acc = None \<and> (\<exists>m\<in>set (msgs st). Process1b acc m st st2)\<close> \<open>mm \<in> SentBy st2 A\<close> assms(2) empty_iff insert_iff list.simps(15) mem_Collect_eq)
        qed
    next
      assume "\<exists>A :: Acceptor. is_safe A
                        \<and> two_a_lrn_loop st A 
                        \<and> (\<exists>l :: Learner. Process1bLearnerLoopStep A l st st2)"
      then show ?thesis
      proof (elim exE)
        fix acc
        assume h3: "is_safe acc \<and>
                two_a_lrn_loop st acc \<and>
                (\<exists>l. Process1bLearnerLoopStep acc l st st2)"
        have "\<exists>l. Process1bLearnerLoopStep acc l st st2" using h3 by blast
        then show ?thesis
        proof (elim exE)
          fix lrnn
          assume "Process1bLearnerLoopStep acc lrnn st st2"
          have "queued_msg st acc = None"
            by (meson assms(1) h3 twoaLearnerLoopSpec.elims(2))
          define new2a where "new2a = M2a lrnn acc (recent_msgs st acc)"
          show ?thesis
            proof (cases "WellFormed st new2a")
              case True
              assume "WellFormed st new2a"
              have "recent_msgs st2 =
                    (\<lambda>x. if x = acc then [new2a] else recent_msgs st x)"
                by (metis Process1bLearnerLoopStep.simps True \<open>Process1bLearnerLoopStep acc lrnn st st2\<close> new2a_def)
              show ?thesis
              proof (cases "acc = A")
                case True
                assume "acc = A"
                have "new2a \<in> Tran(new2a)"
                  using Tran.simps(3) new2a_def by blast
                have "new2a \<in> set (recent_msgs st2 A)"
                  by (simp add: True \<open>recent_msgs st2 = (\<lambda>x. if x = acc then [new2a] else recent_msgs st x)\<close>)
                show ?thesis
                proof (cases "SentBy st A \<noteq> {}")
                  case True
                  have "\<exists>m0 \<in> set (recent_msgs st A).
                          \<forall>m \<in> SentBy st A. m \<in> Tran m0"
                    by (metis SafeAcceptorOwnMessagesRefsSpec.elims(2) True \<open>acc = A\<close> \<open>is_safe A\<close> \<open>queued_msg st acc = None\<close> assms(2))
                  show ?thesis
                    by (smt (verit, ccfv_threshold) Process1bLearnerLoopStep.elims(2) Send.elims(2) SentBy.elims Tran.simps(3) UN_I UnCI \<open>Process1bLearnerLoopStep acc lrnn st st2\<close> \<open>\<exists>m0\<in>set (recent_msgs st A). \<forall>m\<in>SentBy st A. m \<in> Tran m0\<close> \<open>acc = A\<close> \<open>queued_msg st acc = None\<close> insert_iff list.simps(15) mem_Collect_eq)
                next
                  case False
                  show ?thesis
                    by (metis (no_types, lifting) False Process1bLearnerLoopStep.elims(2) Send.elims(2) SentBy.elims Tran.simps(3) True UnCI \<open>Process1bLearnerLoopStep acc lrnn st st2\<close> \<open>new2a \<in> set (recent_msgs st2 A)\<close> \<open>queued_msg st acc = None\<close> insertCI mem_Collect_eq new2a_def set_ConsD)
                qed
              next
                case False
                have "recent_msgs st2 A = recent_msgs st A"
                  using False \<open>recent_msgs st2 = (\<lambda>x. if x = acc then [new2a] else recent_msgs st x)\<close> by presburger
                have "queued_msg st2 A = queued_msg st A"
                  by (metis Process1bLearnerLoopStep.elims(2) \<open>Process1bLearnerLoopStep acc lrnn st st2\<close>)
                have "SentBy st2 A = SentBy st A"
                  by (smt (verit, ccfv_SIG) Collect_cong False Process1bLearnerLoopStep.elims(2) Send.elims(2) SentBy.elims \<open>Process1bLearnerLoopStep acc lrnn st st2\<close> hpaxos.acc.simps(3) insert_iff list.simps(15))
                have "Process1bLearnerLoopStep acc lrnn st st2"
                  using \<open>Process1bLearnerLoopStep acc lrnn st st2\<close> by blast
                show ?thesis
                  by (metis SafeAcceptorOwnMessagesRefsSpec.elims(2) \<open>SentBy st2 A = SentBy st A\<close> \<open>SentBy st2 A \<noteq> {}\<close> \<open>is_safe A\<close> \<open>queued_msg st2 A = queued_msg st A\<close> \<open>recent_msgs st2 A = recent_msgs st A\<close> assms(2))
              qed
            next
              case False
              have es: "msgs st2 = msgs st \<and>
                         recent_msgs st2 = recent_msgs st \<and>
                         queued_msg st2 = queued_msg st"
                by (metis False Process1bLearnerLoopStep.elims(2) \<open>Process1bLearnerLoopStep acc lrnn st st2\<close> new2a_def)
              show ?thesis
                using \<open>SentBy st2 A \<noteq> {}\<close> \<open>is_safe A\<close> assms(2) es by auto
            qed 
          qed 
        qed
    next
      assume "\<exists>A. is_safe A \<and>
        two_a_lrn_loop st A \<and>
        Process1bLearnerLoopDone A st st2"
      show ?thesis
        using \<open>SentBy st2 A \<noteq> {}\<close> \<open>\<exists>A. is_safe A \<and> two_a_lrn_loop st A \<and> Process1bLearnerLoopDone A st st2\<close> \<open>is_safe A\<close> assms(2) by force
    next
      assume "LearnerProcessAction st st2"
      have "recent_msgs st2 A = recent_msgs st A"
        by (smt (verit, best) LearnerProcessAction.simps LearnerAction.simps LearnerDecide.elims(2) LearnerRecv.elims(2) \<open>LearnerProcessAction st st2\<close> ext_inject surjective update_convs(3) update_convs(8))
      have "queued_msg st2 A = queued_msg st A"
        by (smt (verit, ccfv_threshold) LearnerProcessAction.simps LearnerAction.simps LearnerDecide.elims(2) LearnerRecv.elims(2) \<open>LearnerProcessAction st st2\<close> ext_inject surjective update_convs(3) update_convs(8))
      have "SentBy st2 A = SentBy st A"
        by (smt (verit, best) Collect_cong LearnerProcessAction.simps LearnerAction.simps LearnerDecide.elims(2) LearnerRecv.elims(2) SentBy.simps \<open>LearnerProcessAction st st2\<close> simps(1) surjective update_convs(3) update_convs(8))
      then show ?thesis
        using \<open>SentBy st2 A \<noteq> {}\<close> \<open>is_safe A\<close> \<open>queued_msg st2 A = queued_msg st A\<close> \<open>recent_msgs st2 A = recent_msgs st A\<close> assms(2) by auto
    next
      assume "\<exists>A. \<not> is_safe A \<and> FakeSend1b A st st2"
      have "recent_msgs st2 A = recent_msgs st A"
        by (metis FakeSend1b.elims(2) \<open>\<exists>A. \<not> is_safe A \<and> FakeSend1b A st st2\<close> select_convs(4) surjective update_convs(1))
      have "queued_msg st2 A = queued_msg st A"
        by (metis FakeSend1b.elims(2) \<open>\<exists>A. \<not> is_safe A \<and> FakeSend1b A st st2\<close> select_convs(5) surjective update_convs(1))
      have "SentBy st2 A = SentBy st A"
        by (smt (verit, best) Collect_cong FakeSend1b.simps SentBy.simps \<open>\<exists>A. \<not> is_safe A \<and> FakeSend1b A st st2\<close> \<open>is_safe A\<close> hpaxos.acc.simps(2) list.set_intros(2) set_ConsD simps(1) simps(11) surjective)
      show ?thesis
        by (metis SafeAcceptorOwnMessagesRefsSpec.elims(2) \<open>SentBy st2 A = SentBy st A\<close> \<open>SentBy st2 A \<noteq> {}\<close> \<open>is_safe A\<close> \<open>queued_msg st2 A = queued_msg st A\<close> \<open>recent_msgs st2 A = recent_msgs st A\<close> assms(2))
    next
      assume "\<exists>A. \<not> is_safe A \<and> FakeSend2a A st st2"
      have "recent_msgs st2 A = recent_msgs st A"
        by (metis FakeSend2a.simps \<open>\<exists>A. \<not> is_safe A \<and> FakeSend2a A st st2\<close> select_convs(4) surjective update_convs(1))
      have "queued_msg st2 A = queued_msg st A"
        by (metis FakeSend2a.simps \<open>\<exists>A. \<not> is_safe A \<and> FakeSend2a A st st2\<close> select_convs(5) surjective update_convs(1))
      have "SentBy st2 A = SentBy st A"
        by (smt (verit, best) Collect_cong FakeSend2a.simps SentBy.simps \<open>\<exists>A. \<not> is_safe A \<and> FakeSend2a A st st2\<close> \<open>is_safe A\<close> hpaxos.acc.simps(3) list.set_intros(2) set_ConsD simps(1) simps(11) surjective)
     then show ?thesis
       using \<open>SentBy st2 A \<noteq> {}\<close> \<open>is_safe A\<close> \<open>queued_msg st2 A = queued_msg st A\<close> \<open>recent_msgs st2 A = recent_msgs st A\<close> assms(2) by force
    qed
  qed
qed

lemma WellFormed_monotone :
  assumes "WellFormed st m"
      and "BVal st = BVal st2"
    shows "WellFormed st2 m"
  unfolding WellFormed.simps
proof (intro conjI)
  show "isValidMessage m"
    using WellFormed.elims(1) assms(1) by blast
next
  show "type m = T1b \<longrightarrow> (\<forall>y\<in>Tran m.
        m \<noteq> y \<and> SameBallot m y \<longrightarrow> type y = T1a)"
    by (meson WellFormed.elims(2) assms(1))
next
  have "q st = q st2"
    using q.simps Fresh.simps Con2as.simps Buried.simps V.simps \<open>BVal st = BVal st2\<close> by presburger
  show "type m = T2a \<longrightarrow> TrustLive (lrn m) (q st2 m)"
    by (metis WellFormed.elims(1) \<open>q st = q st2\<close> assms(1))
qed

lemma B_1a:
  assumes "type m = T1a"
  shows "B m (bal m)"
proof (cases m)
  fix b
  assume "m = M1a b"
  show "B m (bal m)"
    by (simp add: \<open>m = M1a b\<close>)
next
  fix x y
  assume "m = M1b x y"
  show "B m (bal m)"
    using \<open>m = M1b x y\<close> assms by force
next
  fix x y z
  assume "m = M2a x y z"
  show "B m (bal m)"
    using \<open>m = M2a x y z\<close> assms by force
qed

lemma Tran_eq:
  shows "Tran m = {m} \<union> \<Union> (Tran ` ref m)"
proof (induction m)
  case (M1a x)
  then show ?case 
    by simp
next
  case (M1b x1a x2)
  then show ?case
    by simp
next
  case (M2a x1a x2 x3)
  then show ?case
    by simp
qed

lemma KnownMsgsaccSpecInvariant :
  assumes "RecentMsgsSpec st"
  assumes "QueuedMsgSpec1 st"
  assumes "KnownMsgs_accSpec st"
  assumes "Next st st2"
  shows "KnownMsgs_accSpec st2"
  unfolding KnownMsgs_accSpec.simps
proof (clarify)
  fix AL M
  assume "is_safe AL"
         "M \<in> set (known_msgs_acc st2 AL)"
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
      by (metis AcceptorAction.simps AcceptorProcessAction.simps FakeAcceptorAction.elims(1) Next.elims(2) Process1bLearnerLoop.simps assms(4))
    then show "M \<in> set (msgs st2) \<and>
               Proper_acc st2 AL M \<and>
               WellFormed st2 M \<and>
               Tran M \<subseteq> set (known_msgs_acc st2 AL)"
    proof (elim disjE)
      assume "ProposerSendAction st st2"
      show ?thesis
        by (smt (verit, ccfv_SIG) KnownMsgs_accSpec.elims(2) Proper_acc.simps ProposerSendAction.elims(1) Send1a.elims(2) WellFormed_monotone \<open>M \<in> set (known_msgs_acc st2 AL)\<close> \<open>ProposerSendAction st st2\<close> \<open>is_safe AL\<close> assms(3) ext_inject list.set_intros(2) surjective update_convs(1))
    next
      assume "\<exists>A :: Acceptor. is_safe A
                  \<and> queued_msg st A = None 
                  \<and> (\<exists>m \<in> set (msgs st). Process1a A m st st2)"
      show ?thesis
        by (smt (verit, del_insts) KnownMsgs_accSpec.elims(2) MessageType.distinct(1) MessageType.simps(3) Process1a.elims(2) Proper_acc.simps Recv_acc.elims(2) Send.elims(2) Store_acc.elims(2) Tran.simps(1) WellFormed.elims(1) WellFormed_monotone \<open>M \<in> set (known_msgs_acc st2 AL)\<close> \<open>\<exists>A. is_safe A \<and> queued_msg st A = None \<and> (\<exists>m\<in>set (msgs st). Process1a A m st st2)\<close> \<open>is_safe AL\<close> assms(3) list.set_intros(2) set_ConsD singletonD subset_iff type.elims)
    next
      assume "\<exists>A :: Acceptor. is_safe A
                        \<and> queued_msg st A \<noteq> None 
                        \<and> Process1b A (the (queued_msg st A)) st st2"
      then show ?thesis
      proof (elim exE)
        fix acc
        assume "is_safe acc \<and>
                queued_msg st acc \<noteq> None \<and>
                Process1b acc (the (queued_msg st acc)) st st2"
        have h0: "Proper_acc st2 AL M"
          by (smt (verit) KnownMsgs_accSpec.elims(2) Process1b.simps Proper_acc.elims(2) Proper_acc.elims(3) Recv_acc.elims(2) Store_acc.elims(2) \<open>M \<in> set (known_msgs_acc st2 AL)\<close> \<open>is_safe AL\<close> \<open>is_safe acc \<and> queued_msg st acc \<noteq> None \<and> Process1b acc (the (queued_msg st acc)) st st2\<close> assms(3) list.set_intros(2) set_ConsD)
        have h1: "Tran M \<subseteq> set (known_msgs_acc st2 AL)"
          by (smt (verit, ccfv_threshold) KnownMsgs_accSpec.elims(2) Process1b.simps Proper_acc.elims(2) Recv_acc.elims(2) Store_acc.elims(2) Tran_eq UN_E Un_iff \<open>M \<in> set (known_msgs_acc st2 AL)\<close> \<open>\<exists>A. is_safe A \<and> queued_msg st A \<noteq> None \<and> Process1b A (the (queued_msg st A)) st st2\<close> \<open>is_safe AL\<close> assms(3) in_set_member member_rec(1) singletonD subset_eq)
        have h2: "WellFormed st2 M"
          by (smt (verit) KnownMsgs_accSpec.elims(2) Process1b.simps Recv_acc.elims(2) Store_acc.elims(2) WellFormed_monotone \<open>M \<in> set (known_msgs_acc st2 AL)\<close> \<open>\<exists>A. is_safe A \<and> queued_msg st A \<noteq> None \<and> Process1b A (the (queued_msg st A)) st st2\<close> \<open>is_safe AL\<close> assms(3) set_ConsD)
        have "\<forall>m. m \<in> set (known_msgs_acc st2 AL) \<longrightarrow> m \<in> set (msgs st2)"
          by (smt (z3) KnownMsgs_accSpec.simps Process1b.simps QueuedMsgSpec1.simps Store_acc.elims(2) \<open>\<exists>A. is_safe A \<and> queued_msg st A \<noteq> None \<and> Process1b A (the (queued_msg st A)) st st2\<close> \<open>is_safe AL\<close> assms(2) assms(3) set_ConsD)
        have "M \<in> set (msgs st2)"
          using \<open>M \<in> set (known_msgs_acc st2 AL)\<close> \<open>\<forall>m. m \<in> set (known_msgs_acc st2 AL) \<longrightarrow> m \<in> set (msgs st2)\<close> by blast
        then show ?thesis
          using h0 h1 h2 by blast
      qed
    next
      assume "\<exists>A :: Acceptor. is_safe A
                  \<and> queued_msg st A = None 
                  \<and> (\<exists>m \<in> set (msgs st). Process1b A m st st2)"
      then show ?thesis
        proof (elim exE)
          fix acc
          assume h3: "is_safe acc \<and>
                  queued_msg st acc = None \<and>
                  (\<exists>m\<in>set (msgs st). Process1b acc m st st2)"
          have "\<exists>m. m\<in>set (msgs st) \<and> Process1b acc m st st2"
            using h3 by blast
          then show ?thesis
          proof (elim exE)
            fix msg
            assume "msg\<in>set (msgs st) \<and> Process1b acc msg st st2"
              have "Tran M \<subseteq> set (known_msgs_acc st2 AL)"
                by (smt (verit, ccfv_threshold) KnownMsgs_accSpec.elims(2) Process1b.simps Proper_acc.elims(2) Recv_acc.elims(2) Store_acc.elims(2) Tran_eq UN_E Un_iff \<open>M \<in> set (known_msgs_acc st2 AL)\<close> \<open>\<exists>A. is_safe A \<and> queued_msg st A = None \<and> (\<exists>m\<in>set (msgs st). Process1b A m st st2)\<close> \<open>is_safe AL\<close> assms(3) in_set_member member_rec(1) singletonD subset_eq)
              then show ?thesis
                by (smt (verit, best) KnownMsgs_accSpec.elims(2) Process1b.simps Proper_acc.simps Recv_acc.elims(2) Store_acc.elims(2) WellFormed.elims(2) WellFormed_monotone \<open>M \<in> set (known_msgs_acc st2 AL)\<close> \<open>is_safe AL\<close> \<open>msg \<in> set (msgs st) \<and> Process1b acc msg st st2\<close> assms(3) list.set_intros(2) set_ConsD)
          qed
        qed
    next
      assume "\<exists>A :: Acceptor. is_safe A
                        \<and> two_a_lrn_loop st A 
                        \<and> (\<exists>l :: Learner. Process1bLearnerLoopStep A l st st2)"
      then show ?thesis
      proof (elim exE)
        fix acc
        assume h3: "is_safe acc \<and>
                two_a_lrn_loop st acc \<and>
                (\<exists>l. Process1bLearnerLoopStep acc l st st2)"
        have "\<exists>l. Process1bLearnerLoopStep acc l st st2" using h3 by blast
        then show ?thesis
        proof (elim exE)
          fix lrnn
          assume "Process1bLearnerLoopStep acc lrnn st st2"
          define new2a where "new2a = M2a lrnn acc (recent_msgs st acc)"
          have "WellFormed st2 M"
            by (smt (verit, ccfv_SIG) KnownMsgs_accSpec.elims(2) Process1bLearnerLoopStep.elims(2) Store_acc.elims(2) WellFormed_monotone \<open>M \<in> set (known_msgs_acc st2 AL)\<close> \<open>\<exists>A. is_safe A \<and> two_a_lrn_loop st A \<and> (\<exists>l. Process1bLearnerLoopStep A l st st2)\<close> \<open>is_safe AL\<close> assms(3) set_ConsD)
          have "set (known_msgs_acc st2 AL) \<subseteq> set (msgs st2)"
            by (smt (verit, ccfv_SIG) KnownMsgs_accSpec.elims(2) Process1bLearnerLoopStep.elims(2) Send.elims(2) Store_acc.elims(2) \<open>\<exists>A. is_safe A \<and> two_a_lrn_loop st A \<and> (\<exists>l. Process1bLearnerLoopStep A l st st2)\<close> \<open>is_safe AL\<close> assms(3) in_set_member member_rec(1) subsetI)
          have "Proper_acc st2 AL M"
            by (smt (verit, best) KnownMsgs_accSpec.elims(2) Process1bLearnerLoopStep.elims(2) Proper_acc.simps RecentMsgsSpec.simps Store_acc.elims(2) \<open>M \<in> set (known_msgs_acc st2 AL)\<close> \<open>is_safe AL\<close> assms(1) assms(3) h3 list.set_intros(2) ref.simps(3) set_ConsD subset_eq)
          show ?thesis
          proof (cases "WellFormed st new2a")
            case True
            assume "WellFormed st new2a"
            have "recent_msgs st2 =
                  (\<lambda>x. if x = acc then [new2a] else recent_msgs st x)"
              by (metis Process1bLearnerLoopStep.simps True \<open>Process1bLearnerLoopStep acc lrnn st st2\<close> new2a_def)
            show ?thesis
            proof (cases "acc = AL")
              case True
              assume "acc = AL"
              have "Tran M \<subseteq> set (known_msgs_acc st2 AL)"
                by (smt (verit, ccfv_threshold) KnownMsgs_accSpec.simps Process1bLearnerLoopStep.simps RecentMsgsSpec.simps RecentMsgsaccSpecInvariant Send.simps Store_acc.simps Tran_eq True UN_E Un_iff \<open>M \<in> set (known_msgs_acc st2 AL)\<close> \<open>Process1bLearnerLoopStep acc lrnn st st2\<close> \<open>WellFormed st new2a\<close> \<open>\<exists>A. is_safe A \<and> two_a_lrn_loop st A \<and> (\<exists>l. Process1bLearnerLoopStep A l st st2)\<close> assms(1) assms(3) assms(4) empty_set in_mono list.simps(15) new2a_def not_Cons_self2 ref.simps(3) set_ConsD subsetI subset_insertI2)
              show ?thesis
                using WellFormed.simps \<open>M \<in> set (known_msgs_acc st2 AL)\<close> \<open>Proper_acc st2 AL M\<close> \<open>Tran M \<subseteq> set (known_msgs_acc st2 AL)\<close> \<open>WellFormed st2 M\<close> \<open>set (known_msgs_acc st2 AL) \<subseteq> set (msgs st2)\<close> by blast
            next
              case False
              have "known_msgs_acc st2 = (\<lambda>x.
                      if x = acc then new2a # known_msgs_acc st acc
                                 else known_msgs_acc st x)"
                by (metis Process1bLearnerLoopStep.simps Store_acc.simps True \<open>Process1bLearnerLoopStep acc lrnn st st2\<close> new2a_def)
              have "M \<in> set (known_msgs_acc st AL)"
                using False \<open>M \<in> set (known_msgs_acc st2 AL)\<close> \<open>known_msgs_acc st2 = (\<lambda>x. if x = acc then new2a # known_msgs_acc st acc else known_msgs_acc st x)\<close> by auto
              show ?thesis
                by (metis False KnownMsgs_accSpec.elims(2) \<open>M \<in> set (known_msgs_acc st AL)\<close> \<open>Proper_acc st2 AL M\<close> \<open>WellFormed st2 M\<close> \<open>is_safe AL\<close> \<open>known_msgs_acc st2 = (\<lambda>x. if x = acc then new2a # known_msgs_acc st acc else known_msgs_acc st x)\<close> \<open>set (known_msgs_acc st2 AL) \<subseteq> set (msgs st2)\<close> assms(3) subsetD)
            qed
          next
            case False
            show ?thesis
              by (metis False KnownMsgs_accSpec.elims(2) Process1bLearnerLoopStep.elims(2) \<open>M \<in> set (known_msgs_acc st2 AL)\<close> \<open>Process1bLearnerLoopStep acc lrnn st st2\<close> \<open>Proper_acc st2 AL M\<close> \<open>WellFormed st2 M\<close> \<open>is_safe AL\<close> assms(3) new2a_def)
          qed 
        qed 
      qed
    next
      assume "\<exists>A. is_safe A \<and>
        two_a_lrn_loop st A \<and>
        Process1bLearnerLoopDone A st st2"
      then show ?thesis
        by (smt (verit, del_insts) KnownMsgs_accSpec.elims(1) Process1bLearnerLoopDone.elims(2) Proper_acc.elims(1) WellFormed_monotone \<open>M \<in> set (known_msgs_acc st2 AL)\<close> \<open>is_safe AL\<close> assms(3) simps(1) simps(2) simps(9) surjective update_convs(6))
    next
      assume "LearnerProcessAction st st2"
      then show ?thesis
        by (smt (verit) KnownMsgs_accSpec.elims(2) LearnerProcessAction.simps LearnerAction.simps LearnerDecide.elims(2) LearnerRecv.elims(2) Proper_acc.simps WellFormed_monotone \<open>M \<in> set (known_msgs_acc st2 AL)\<close> \<open>is_safe AL\<close> assms(3) ext_inject surjective update_convs(3) update_convs(8))
    next
      assume "\<exists>A. \<not> is_safe A \<and> FakeSend1b A st st2"
      show ?thesis
        by (smt (verit, ccfv_threshold) FakeSend1b.simps KnownMsgs_accSpec.elims(2) Proper_acc.simps WellFormed_monotone \<open>M \<in> set (known_msgs_acc st2 AL)\<close> \<open>\<exists>A. \<not> is_safe A \<and> FakeSend1b A st st2\<close> \<open>is_safe AL\<close> assms(3) ext_inject list.set_intros(2) surjective update_convs(1))
    next
      assume "\<exists>A. \<not> is_safe A \<and> FakeSend2a A st st2"
      show ?thesis
        by (smt (verit, best) FakeSend2a.simps KnownMsgs_accSpec.elims(2) Proper_acc.simps WellFormed_monotone \<open>M \<in> set (known_msgs_acc st2 AL)\<close> \<open>\<exists>A. \<not> is_safe A \<and> FakeSend2a A st st2\<close> \<open>is_safe AL\<close> assms(3) ext_inject list.set_intros(2) surjective update_convs(1))
    qed
  qed

lemma KnownMsgslrnSpecInvariant :
  assumes "KnownMsgs_lrnSpec st"
  assumes "Next st st2"
  shows "KnownMsgs_lrnSpec st2"
  unfolding KnownMsgs_lrnSpec.simps
proof (clarify)
  fix AL M
  assume "M \<in> set (known_msgs_lrn st2 AL)"
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
        using assms(2) next_split by presburger
    then show "M \<in> set (msgs st2) \<and>
               Proper_lrn st2 AL M \<and>
               WellFormed st2 M \<and>
               Tran M \<subseteq> set (known_msgs_lrn st2 AL)"
    proof (elim disjE)
      assume "ProposerSendAction st st2"
      then show ?thesis
        by (smt (verit) KnownMsgs_lrnSpec.elims(2) Proper_lrn.simps ProposerSendAction.elims(1) Send1a.elims(2) WellFormed_monotone \<open>M \<in> set (known_msgs_lrn st2 AL)\<close> assms(1) ext_inject list.set_intros(2) surjective update_convs(1))
    next
      assume "\<exists>A :: Acceptor. is_safe A
                  \<and> queued_msg st A = None 
                  \<and> (\<exists>m \<in> set (msgs st). Process1a A m st st2)"
      then show ?thesis
        by (metis KnownMsgs_lrnSpec.elims(2) Process1a.elims(2) Proper_lrn.elims(2) Proper_lrn.elims(3) Send.elims(2) Store_acc.elims(2) WellFormed_monotone \<open>M \<in> set (known_msgs_lrn st2 AL)\<close> assms(1) list.set_intros(2))
    next
      assume "\<exists>A :: Acceptor. is_safe A
                        \<and> queued_msg st A \<noteq> None 
                        \<and> Process1b A (the (queued_msg st A)) st st2"
      then show ?thesis
        by (smt (verit, best) KnownMsgs_lrnSpec.elims(2) Process1b.simps Proper_lrn.simps Store_acc.elims(2) WellFormed_monotone \<open>M \<in> set (known_msgs_lrn st2 AL)\<close> assms(1))
    next
      assume "\<exists>A :: Acceptor. is_safe A
                  \<and> queued_msg st A = None 
                  \<and> (\<exists>m \<in> set (msgs st). Process1b A m st st2)"
      then show ?thesis
        by (smt (verit, best) KnownMsgs_lrnSpec.elims(2) Process1b.simps Proper_lrn.simps Store_acc.elims(2) WellFormed_monotone \<open>M \<in> set (known_msgs_lrn st2 AL)\<close> assms(1))
    next
      assume "\<exists>A :: Acceptor. is_safe A
                        \<and> two_a_lrn_loop st A 
                        \<and> (\<exists>l :: Learner. Process1bLearnerLoopStep A l st st2)"
      then show ?thesis
        by (smt (verit, best) KnownMsgs_lrnSpec.elims(2) Process1bLearnerLoopStep.elims(2) Proper_lrn.simps Send.elims(2) Store_acc.elims(2) WellFormed_monotone \<open>M \<in> set (known_msgs_lrn st2 AL)\<close> assms(1) list.set_intros(2))
    next
      assume "\<exists>A. is_safe A \<and>
        two_a_lrn_loop st A \<and>
        Process1bLearnerLoopDone A st st2"
      then show ?thesis
        by (smt (verit, best) KnownMsgs_lrnSpec.elims(2) Process1bLearnerLoopDone.elims(1) Proper_lrn.simps WellFormed_monotone \<open>M \<in> set (known_msgs_lrn st2 AL)\<close> assms(1) ext_inject surjective update_convs(6))
    next
      assume "LearnerProcessAction st st2"
      then show ?thesis
        unfolding LearnerProcessAction.simps LearnerAction.simps
      proof (elim exE)
        fix ln
        assume "(\<exists>m \<in> set (msgs st). LearnerRecv ln m st st2) \<or>
                (\<exists>blt val. LearnerDecide ln blt val st st2)"
        then show ?thesis
        proof (elim disjE)
          assume "\<exists>m \<in> set (msgs st). LearnerRecv ln m st st2"
          have "\<exists>m. m \<in> set (msgs st) \<and> LearnerRecv ln m st st2"
            using \<open>\<exists>m\<in>set (msgs st). LearnerRecv ln m st st2\<close> by blast
          then show ?thesis
          proof (elim exE)
            fix m
            assume "m \<in> set (msgs st) \<and> LearnerRecv ln m st st2"
            have "WellFormed st2 M"
              by (smt (verit) KnownMsgs_lrnSpec.elims(2) LearnerRecv.elims(2) Recv_lrn.elims(2) WellFormed_monotone \<open>M \<in> set (known_msgs_lrn st2 AL)\<close> \<open>m \<in> set (msgs st) \<and> LearnerRecv ln m st st2\<close> assms(1) ext_inject set_ConsD surjective update_convs(3))
            have "Tran M \<subseteq> set (known_msgs_lrn st2 AL)"
              by (smt (verit) KnownMsgs_lrnSpec.elims(2) LearnerRecv.elims(2) Proper_lrn.elims(2) Recv_lrn.simps Tran_eq UN_E Un_iff \<open>M \<in> set (known_msgs_lrn st2 AL)\<close> \<open>\<exists>m. m \<in> set (msgs st) \<and> LearnerRecv ln m st st2\<close> assms(1) list.set_intros(2) set_ConsD simps(3) singletonD subset_iff surjective update_convs(3))
            show ?thesis
              by (smt (verit, ccfv_SIG) KnownMsgs_lrnSpec.elims(2) LearnerRecv.elims(2) Message_ref_Tran Proper_lrn.simps WellFormed.elims(2) \<open>M \<in> set (known_msgs_lrn st2 AL)\<close> \<open>Tran M \<subseteq> set (known_msgs_lrn st2 AL)\<close> \<open>WellFormed st2 M\<close> \<open>m \<in> set (msgs st) \<and> LearnerRecv ln m st st2\<close> assms(1) set_ConsD simps(1) simps(3) subset_iff surjective update_convs(3))
          qed
        next
          assume "\<exists>blt val. LearnerDecide ln blt val st st2"
          then show ?thesis
            by (smt (verit, best) KnownMsgs_lrnSpec.elims(2) LearnerDecide.elims(2) Proper_lrn.simps WellFormed_monotone \<open>M \<in> set (known_msgs_lrn st2 AL)\<close> assms(1) ext_inject surjective update_convs(8))
        qed
      qed
    next
      assume "\<exists>A. \<not> is_safe A \<and> FakeSend1b A st st2"
      have "WellFormed st2 M"
        by (metis FakeSend1b.simps KnownMsgs_lrnSpec.elims(2) WellFormed_monotone \<open>M \<in> set (known_msgs_lrn st2 AL)\<close> \<open>\<exists>A. \<not> is_safe A \<and> FakeSend1b A st st2\<close> assms(1) ext_inject surjective update_convs(1))
      have "Tran M \<subseteq> set (known_msgs_lrn st2 AL)"
        by (metis FakeSend1b.simps KnownMsgs_lrnSpec.elims(2) \<open>M \<in> set (known_msgs_lrn st2 AL)\<close> \<open>\<exists>A. \<not> is_safe A \<and> FakeSend1b A st st2\<close> assms(1) ext_inject surjective update_convs(1))
      show ?thesis
        by (smt (verit) FakeSend1b.simps KnownMsgs_lrnSpec.elims(2) Proper_lrn.simps \<open>M \<in> set (known_msgs_lrn st2 AL)\<close> \<open>WellFormed st2 M\<close> \<open>\<exists>A. \<not> is_safe A \<and> FakeSend1b A st st2\<close> assms(1) ext_inject list.set_intros(2) surjective update_convs(1))
    next
      assume "\<exists>A. \<not> is_safe A \<and> FakeSend2a A st st2"
      have "WellFormed st2 M"
        by (metis (no_types, lifting) FakeSend2a.simps KnownMsgs_lrnSpec.elims(2) WellFormed_monotone \<open>M \<in> set (known_msgs_lrn st2 AL)\<close> \<open>\<exists>A. \<not> is_safe A \<and> FakeSend2a A st st2\<close> assms(1) ext_inject surjective update_convs(1))
      have "Tran M \<subseteq> set (known_msgs_lrn st2 AL)"
        by (metis FakeSend2a.simps KnownMsgs_lrnSpec.elims(2) \<open>M \<in> set (known_msgs_lrn st2 AL)\<close> \<open>\<exists>A. \<not> is_safe A \<and> FakeSend2a A st st2\<close> assms(1) ext_inject surjective update_convs(1))
      show ?thesis
        by (smt (verit, del_insts) FakeSend2a.simps KnownMsgs_lrnSpec.elims(2) Proper_lrn.simps \<open>M \<in> set (known_msgs_lrn st2 AL)\<close> \<open>WellFormed st2 M\<close> \<open>\<exists>A. \<not> is_safe A \<and> FakeSend2a A st st2\<close> assms(1) list.set_intros(2) simps(1) simps(3) surjective update_convs(1))
  qed
qed

lemma MsgsSafeAcceptorSpecInvariant :
  assumes "SafeAcceptorOwnMessagesRefsSpec st"
  assumes "twoaLearnerLoopSpec st"
  assumes "MsgsSafeAcceptorSpec st"
  assumes "Next st st2"
  shows "MsgsSafeAcceptorSpec st2"
  unfolding MsgsSafeAcceptorSpec.simps
proof (clarify)
  fix a2 m1 m2
  assume "is_safe (acc m1)"
         "m1 \<in> set (msgs st2)"
         "m2 \<in> set (msgs st2)"
         "type m1 \<noteq> T1a"
         "type m2 \<noteq> T1a"
         "acc m2 = acc m1"
         "m2 \<notin> Tran m2"
  show "m1 \<in> Tran m1"
  proof
  have "Next st st2"
    using assms(4) by blast
  then show "m1 \<in> Tran m1"
    unfolding Next.simps
  proof (elim disjE)
    assume "ProposerSendAction st st2"
    show ?thesis
      by (metis Tran.simps(2) Tran.simps(3) UnCI \<open>type m1 \<noteq> T1a\<close> singletonI type.elims)
  next
    assume "AcceptorProcessAction st st2"
    then show ?thesis
      unfolding AcceptorProcessAction.simps AcceptorAction.simps
      proof (elim exE)
        fix a
        assume h: "is_safe a \<and>
                  (\<not> two_a_lrn_loop st a \<and>
                   (queued_msg st a \<noteq> None \<and>
                    Process1b a (the (queued_msg st a)) st st2 \<or>
                    queued_msg st a = None \<and>
                    (\<exists>m \<in> set (msgs st). Process1a a m st st2 \<or> Process1b a m st st2)) \<or>
                   two_a_lrn_loop st a \<and> Process1bLearnerLoop a st st2)"
        show ?thesis
        proof (cases "two_a_lrn_loop st a")
          case True
          have "Process1bLearnerLoop a st st2" 
            using True h by blast
          then show ?thesis
            by (metis Tran.simps(2) Tran.simps(3) UnCI \<open>type m1 \<noteq> T1a\<close> singletonI type.elims)
        next
          case False
          have "(queued_msg st a \<noteq> None \<and>
                    Process1b a (the (queued_msg st a)) st st2 \<or>
                    queued_msg st a = None \<and>
                    (\<exists>m. Process1a a m st st2 \<or> Process1b a m st st2))"
            using False h by blast
          then show ?thesis
            by (metis Tran.simps(2) Tran.simps(3) UnCI \<open>type m1 \<noteq> T1a\<close> equals0I option.distinct(1) option.simps(15) set_empty_eq singletonD type.elims)
          qed
        qed
  next
    assume "LearnerProcessAction st st2"
    then show ?thesis
      unfolding LearnerProcessAction.simps LearnerAction.simps
    proof (elim exE)
      fix ln
      assume "(\<exists>m \<in> set (msgs st). LearnerRecv ln m st st2) \<or>
              (\<exists>blt val. LearnerDecide ln blt val st st2)"
      then show ?thesis
        by (metis (no_types, lifting) LearnerDecide.elims(2) LearnerRecv.elims(2) MsgsSafeAcceptorSpec.elims(2) \<open>is_safe (acc m1)\<close> \<open>m1 \<in> set (msgs st2)\<close> \<open>type m1 \<noteq> T1a\<close> assms(3) ext_inject surjective update_convs(3) update_convs(8))
    qed
  next
    assume "FakeAcceptorAction st st2"
    then show ?thesis
      unfolding FakeAcceptorAction.simps
      by (metis Tran.simps(2) Tran.simps(3) UnCI \<open>type m1 \<noteq> T1a\<close> singletonI type.elims)
  qed
  show "Tran m1 \<subseteq> Tran m1"
    by simp
qed
qed

lemma SafetySpecInvariant :
  assumes "DecisionSpec st"
  assumes "Safety st"
  assumes "Next st st2"
  shows "Safety st2"
  unfolding Safety.simps
proof (clarify)
  fix L1 L2 B1 B2 V1 V2
  assume "ent L1 L2"
         "V1 \<in> decision st2 L1 B1"
         "V2 \<in> decision st2 L2 B2"
  then have "Next st st2"
    using assms(3) by blast
  then show "V1 = V2"
    unfolding Next.simps
    proof (elim disjE)
      assume "ProposerSendAction st st2"
      have "decision st2 = decision st"
        using \<open>ProposerSendAction st st2\<close> by auto
      then show ?thesis 
        using \<open>V1 \<in> decision st2 L1 B1\<close> \<open>V2 \<in> decision st2 L2 B2\<close> \<open>ent L1 L2\<close> assms(2) by force
    next
      assume "AcceptorProcessAction st st2"
      then show ?thesis 
        unfolding AcceptorProcessAction.simps AcceptorAction.simps
        proof (elim exE)
          fix a
          assume h: "is_safe a \<and>
                    (\<not> two_a_lrn_loop st a \<and>
                     (queued_msg st a \<noteq> None \<and>
                      Process1b a (the (queued_msg st a)) st st2 \<or>
                      queued_msg st a = None \<and>
                      (\<exists>m \<in> set (msgs st). Process1a a m st st2 \<or> Process1b a m st st2)) \<or>
                     two_a_lrn_loop st a \<and> Process1bLearnerLoop a st st2)"
          show ?thesis
          proof (cases "two_a_lrn_loop st a")
            case True
            have "Process1bLearnerLoop a st st2" 
              using True h by blast
            then show ?thesis
            unfolding Process1bLearnerLoop.simps
            proof (elim disjE)
              assume "\<exists>ln. ln \<notin> processed_lrns st a \<and>
                        Process1bLearnerLoopStep a ln st st2"
              then show ?thesis
                by (metis Process1bLearnerLoopStep.elims(2) Safety.elims(2) \<open>V1 \<in> decision st2 L1 B1\<close> \<open>V2 \<in> decision st2 L2 B2\<close> \<open>ent L1 L2\<close> assms(2))
            next
              assume "Process1bLearnerLoopDone a st st2"
              then show ?thesis
                using \<open>V1 \<in> decision st2 L1 B1\<close> \<open>V2 \<in> decision st2 L2 B2\<close> \<open>ent L1 L2\<close> assms(2) by auto
            qed
          next
            case False
            have "(queued_msg st a \<noteq> None \<and>
                      Process1b a (the (queued_msg st a)) st st2 \<or>
                      queued_msg st a = None \<and>
                      (\<exists>m. Process1a a m st st2 \<or> Process1b a m st st2))"
              using False h by blast
            then show ?thesis
              proof (elim disjE)
                assume "queued_msg st a \<noteq> None \<and>
                        Process1b a (the (queued_msg st a))
                         st st2"
                then show ?thesis
                  using \<open>V1 \<in> decision st2 L1 B1\<close> \<open>V2 \<in> decision st2 L2 B2\<close> \<open>ent L1 L2\<close> assms(2) by force
              next
                assume "queued_msg st a = None \<and>
                      (\<exists>m. Process1a a m st st2 \<or>
                           Process1b a m st
                            st2)"
                then show ?thesis
                  by (smt (verit, best) Process1a.elims(2) Process1b.simps Safety.elims(2) \<open>V1 \<in> decision st2 L1 B1\<close> \<open>V2 \<in> decision st2 L2 B2\<close> \<open>ent L1 L2\<close> assms(2))
              qed
          qed
        qed
    next
      assume "LearnerProcessAction st st2"
      then show ?thesis 
      unfolding LearnerProcessAction.simps LearnerAction.simps
      proof (elim exE)
        fix ln
        assume "(\<exists>m \<in> set (msgs st). LearnerRecv ln m st st2) \<or>
                (\<exists>blt val. LearnerDecide ln blt val st st2)"
        then show ?thesis
        proof (elim disjE)
          assume "\<exists>m \<in> set (msgs st). LearnerRecv ln m st st2"
          have "\<exists>m. LearnerRecv ln m st st2"
            using \<open>\<exists>m\<in>set (msgs st). LearnerRecv ln m st st2\<close> by blast
          have "decision st2 = decision st"
            using \<open>\<exists>m. LearnerRecv ln m st st2\<close> by fastforce
          then show ?thesis
            using \<open>V1 \<in> decision st2 L1 B1\<close> \<open>V2 \<in> decision st2 L2 B2\<close> \<open>ent L1 L2\<close> assms(2) by force
        next
          assume "\<exists>blt val. LearnerDecide ln blt val st st2"
          then show ?thesis
            unfolding LearnerDecide.simps Safety.simps ChosenIn.simps
          proof (elim exE)
          fix blt val
          assume "(\<exists>S \<subseteq> Known2a st ln blt val. TrustLive ln (acc ` S)) \<and>
                  st2 = st
                       \<lparr>decision :=
                          \<lambda>x y. if x = ln \<and> y = blt
                                 then {val} \<union> decision st x y
                                 else decision st x y\<rparr>"
          then show "V1 = V2"
          proof
            have sthyp: "st2 = st
                       \<lparr>decision :=
                          \<lambda>x y. if x = ln \<and> y = blt
                                 then {val} \<union> decision st x y
                                 else decision st x y\<rparr>"
              using \<open>(\<exists>S\<subseteq>Known2a st ln blt val. TrustLive ln (acc ` S)) \<and> st2 = st \<lparr>decision := \<lambda>x y. if x = ln \<and> y = blt then {val} \<union> decision st x y else decision st x y\<rparr>\<close> by blast
            have "\<exists>S \<subseteq> Known2a st ln blt val. TrustLive ln (acc ` S)"
              using \<open>(\<exists>S\<subseteq>Known2a st ln blt val. TrustLive ln (acc ` S)) \<and> st2 = st \<lparr>decision := \<lambda>x y. if x = ln \<and> y = blt then {val} \<union> decision st x y else decision st x y\<rparr>\<close> by blast
            then show "V1 = V2"
            proof (elim exE)
              fix S
              assume "S \<subseteq> Known2a st ln blt val \<and> TrustLive ln (acc ` S)"
              then show "V1 = V2"
                by (metis ChosenIn.elims(1) DecisionSpec.elims(1) DecisionSpecInvariant LearnerGraphAssumptionClosure LearnerGraphAssumptionValidity TrustSafeAssumption \<open>V1 \<in> decision st2 L1 B1\<close> \<open>V2 \<in> decision st2 L2 B2\<close> \<open>ent L1 L2\<close> assms(1) assms(3) dual_order.refl empty_iff ent.elims(1))
              qed
            qed
            qed
        qed
      qed
    next
      assume "FakeAcceptorAction st st2"
      then show ?thesis 
        unfolding FakeAcceptorAction.simps
        proof (elim exE)
          fix a
          assume "\<not> is_safe a \<and> (FakeSend1b a st st2 \<or>
                  FakeSend2a a st
                   st2)"
          have "FakeSend1b a st st2 \<or>
                FakeSend2a a st st2"
            using \<open>\<not> is_safe a \<and> (FakeSend1b a st st2 \<or> FakeSend2a a st st2)\<close> by blast
          then show ?thesis
          proof (elim disjE)
            assume "FakeSend1b a st st2"
            have "decision st2 = decision st"
              by (metis FakeSend1b.simps \<open>FakeSend1b a st st2\<close> ext_inject surjective update_convs(1))
            then show ?thesis
              using \<open>V1 \<in> decision st2 L1 B1\<close> \<open>V2 \<in> decision st2 L2 B2\<close> \<open>ent L1 L2\<close> assms(2) by force
          next
            assume "FakeSend2a a st st2"
            have "decision st2 = decision st"
              by (metis FakeSend2a.elims(2) \<open>FakeSend2a a st st2\<close> ext_inject surjective update_convs(1))
            then show ?thesis
              using \<open>V1 \<in> decision st2 L1 B1\<close> \<open>V2 \<in> decision st2 L2 B2\<close> \<open>ent L1 L2\<close> assms(2) by fastforce
          qed
        qed
    qed
  qed

lemma FullSafetyInvariantNext :
  assumes "FullSafetyInvariant st"
  assumes "Next st st2"
  shows "FullSafetyInvariant st2"
unfolding FullSafetyInvariant.simps
proof (intro conjI)
  show "TypeOK st2"
    using FullSafetyInvariant.simps TypeOKInvariant assms(1) assms(2) by blast
next
  show "RecentMsgsSpec st2"
    by (meson FullSafetyInvariant.elims(2) RecentMsgsaccSpecInvariant assms(1) assms(2))
next
  show "KnownMsgs_accSpec st2"
    using FullSafetyInvariant.simps KnownMsgsaccSpecInvariant assms(1) assms(2) by blast
next
  show "KnownMsgs_lrnSpec st2"
    using FullSafetyInvariant.simps KnownMsgslrnSpecInvariant assms(1) assms(2) by blast
next
  show "QueuedMsgSpec1 st2"
    using FullSafetyInvariant.simps QueuedMsgSpecInvariant assms(1) assms(2) by blast
next
  show "twoaLearnerLoopSpec st2"
    using FullSafetyInvariant.simps assms(1) assms(2) twoaLearnerLoopSpecInvariant by blast
next
  show "SafeAcceptorOwnMessagesRefsSpec st2"
    by (meson FullSafetyInvariant.elims(2) SafeAcceptorOwnMessagesRefsSpecInvariant assms(1) assms(2))
next
  show "MsgsSafeAcceptorSpec st2"
    using FullSafetyInvariant.simps MsgsSafeAcceptorSpecInvariant assms(1) assms(2) by blast
next
  show "DecisionSpec st2"
    by (meson DecisionSpecInvariant FullSafetyInvariant.elims(2) assms(1) assms(2))
next
  show "Safety st2"
    by (meson FullSafetyInvariant.elims(1) SafetySpecInvariant assms(1) assms(2))
qed

theorem PreSafetyResult :
  assumes "Spec f"
  shows "\<forall>n. FullSafetyInvariant (f n)"
proof
  fix n
  show "FullSafetyInvariant (f n)"
  proof (induction n)
    case 0
    have "\<forall>b. FullSafetyInvariant (Init b)"
      by (simp add: NoMessage_def)
    then show ?case
      by (metis Spec.simps assms)
  next
    case (Suc n)
    fix n
    assume hyp: "FullSafetyInvariant (f n)"
    then show "FullSafetyInvariant (f (Suc n))"
      by (metis FullSafetyInvariantNext Spec.elims(2) assms)
  qed
qed

theorem SafetyResult :
  assumes "Spec f"
  shows "\<forall>n. Safety (f n)"
  by (meson FullSafetyInvariant.elims(2) PreSafetyResult assms)

theorem TypeOKResult :
  assumes "Spec f"
  shows "\<forall>n. TypeOK (f n)"
  by (meson FullSafetyInvariant.elims(2) PreSafetyResult assms)

theorem RecentMsgsSpecResult :
  assumes "Spec f"
  shows "\<forall>n. RecentMsgsSpec (f n)"
  by (meson FullSafetyInvariant.elims(2) PreSafetyResult assms)

theorem KnownMsgs_accSpecResult :
  assumes "Spec f"
  shows "\<forall>n. KnownMsgs_accSpec (f n)"
  by (meson FullSafetyInvariant.elims(2) PreSafetyResult assms)

theorem KnownMsgs_lrnSpecResult :
  assumes "Spec f"
  shows "\<forall>n. KnownMsgs_lrnSpec (f n)"
  by (meson FullSafetyInvariant.elims(2) PreSafetyResult assms)

theorem QueuedMsgResult :
  assumes "Spec f"
  shows "\<forall>n. QueuedMsgSpec1 (f n)"
  by (meson FullSafetyInvariant.elims(2) PreSafetyResult assms)

theorem twoaLearnerLoopSpecResult :
  assumes "Spec f"
  shows "\<forall>n. twoaLearnerLoopSpec (f n)"
  by (meson FullSafetyInvariant.elims(2) PreSafetyResult assms)

theorem SafeAcceptorOwnMessagesRefsSpecResult :
  assumes "Spec f"
  shows "\<forall>n. SafeAcceptorOwnMessagesRefsSpec (f n)"
  by (meson FullSafetyInvariant.elims(2) PreSafetyResult assms)

theorem MsgsSafeAcceptorSpecResult :
  assumes "Spec f"
  shows "\<forall>n. MsgsSafeAcceptorSpec (f n)"
  by (meson FullSafetyInvariant.elims(2) PreSafetyResult assms)

theorem DecisionSpecResult :
  assumes "Spec f"
  shows "\<forall>n. DecisionSpec (f n)"
  by (meson FullSafetyInvariant.elims(2) PreSafetyResult assms)

end