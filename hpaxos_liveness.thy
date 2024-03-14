theory hpaxos_liveness
imports Main hpaxos
begin

fun Enabled :: "(State \<Rightarrow> State \<Rightarrow> bool) \<Rightarrow> State \<Rightarrow> bool" where
  "Enabled r st = (\<exists>st2. r st st2)"

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

fun Acceptor_Enabled :: "Acceptor \<Rightarrow> State \<Rightarrow> bool" where
  "Acceptor_Enabled a st = (
    (\<exists>m. Recv_acc st a m) \<or> (\<exists>ln :: Learner. ln \<notin> processed_lrns st a)
  )"


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

lemma LearnerRecv_Enabled:
  shows "Enabled (LearnerRecv l m) st = Recv_lrn st l m"
  using Enabled.simps LearnerRecv.simps by presburger

lemma LearnerDecide_Enabled:
  shows "Enabled (LearnerDecide l b v) st = ChosenIn st l b v"
  using Enabled.simps LearnerDecide.simps by presburger

fun WF :: "(State \<Rightarrow> State \<Rightarrow> bool) \<Rightarrow> (nat \<Rightarrow> State) \<Rightarrow> bool" where
  "WF p f = (
    \<forall>i. (\<forall>j \<ge> i. Enabled p (f j)) \<longrightarrow> (\<exists>j \<ge> i. p (f j) (f (j + 1)))
  )"

fun BallotLimit1 :: "(nat \<Rightarrow> State) \<Rightarrow> Ballot \<Rightarrow> nat \<Rightarrow> bool" where
  "BallotLimit1 f b i = (\<forall>m \<in> set (msgs (f i)). type m = T1a \<longrightarrow> bal m < b)"

fun BallotLimit2 :: "(nat \<Rightarrow> State) \<Rightarrow> Ballot \<Rightarrow> bool" where
  "BallotLimit2 f b = (\<forall>c :: Ballot. c > b \<longrightarrow> (\<forall>j. \<not> (Send1a c (f j) (f (1 + j)))))"

fun BallotSend :: "(nat \<Rightarrow> State) \<Rightarrow> Ballot \<Rightarrow> bool" where
  "BallotSend f b = (\<forall>i. \<exists>j \<ge> i. Send1a b (f j) (f (j + 1)))"

fun EventuallyProccess1a :: "(nat \<Rightarrow> State) \<Rightarrow> Ballot \<Rightarrow> Acceptor set \<Rightarrow> bool" where
  "EventuallyProccess1a f b Q = 
    (\<forall>m :: PreMessage. B m b \<longrightarrow> (\<forall>a \<in> Q. WF (Process1a a m) f))"

fun EventuallyProccess1b :: "(nat \<Rightarrow> State) \<Rightarrow> Ballot \<Rightarrow> Acceptor set \<Rightarrow> bool" where
  "EventuallyProccess1b f b Q = 
    (\<forall>m :: PreMessage. B m b \<longrightarrow> (\<forall>a \<in> Q. WF (Process1b a m) f))"

fun EventuallyProcess1bLearnerLoop :: "(nat \<Rightarrow> State) \<Rightarrow> Acceptor set \<Rightarrow> bool" where
  "EventuallyProcess1bLearnerLoop f Q = 
    (\<forall>a \<in> Q. \<forall>i. \<exists>j \<ge> i. Process1bLearnerLoop a (f j) (f (j + 1)))"

fun EventuallyLearnerRecv :: "(nat \<Rightarrow> State) \<Rightarrow> Learner \<Rightarrow> Ballot \<Rightarrow> bool" where
  "EventuallyLearnerRecv f L b = 
    (\<forall>m :: PreMessage. B m b \<longrightarrow> WF (LearnerRecv L m) f)"

fun EventuallyLearnerDecide :: "(nat \<Rightarrow> State) \<Rightarrow> Learner \<Rightarrow> Ballot \<Rightarrow> bool" where
  "EventuallyLearnerDecide f L b = 
    WF (\<lambda>st st2. \<exists> v :: Value. LearnerDecide L b v st st2) f"

fun Liveness_Assumptions :: "(nat \<Rightarrow> State) \<Rightarrow> Learner \<Rightarrow> Ballot \<Rightarrow> Acceptor set \<Rightarrow> nat \<Rightarrow> bool" where
 "Liveness_Assumptions f L b Q i = (
     BallotLimit1 f b i \<and>
     BallotLimit2 f b \<and>
     BallotSend f b \<and>
     EventuallyProccess1a f b Q \<and>
     EventuallyProccess1b f b Q \<and>
     EventuallyProcess1bLearnerLoop f Q \<and>
     EventuallyLearnerRecv f L b \<and>
     EventuallyLearnerDecide f L b
    )"

fun Liveness :: "(nat \<Rightarrow> State) \<Rightarrow> bool" where
  "Liveness f = (
    \<forall> L :: Learner. \<forall> b :: Ballot. \<forall>Q :: Acceptor set. is_quorum Q \<longrightarrow>
    (\<forall>a \<in> Q. is_safe a) \<longrightarrow> TrustLive L Q \<longrightarrow> 
    (\<forall>i. Liveness_Assumptions f L b Q i \<longrightarrow> 
    (\<exists>j \<ge> i. \<exists> BB :: Ballot . decision (f j) L BB \<noteq> {})
  ))"


theorem LivenessResult :
  assumes "Spec f"
  shows "Liveness f"
  sorry

end