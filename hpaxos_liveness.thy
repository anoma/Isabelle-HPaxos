theory hpaxos_liveness
imports Main hpaxos hpaxos_safety
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

lemma LearnerRecv_Enabled:
  shows "Enabled (LearnerRecv l m) st = Recv_lrn st l m"
  using Enabled.simps LearnerRecv.simps by presburger

lemma LearnerDecide_Enabled:
  shows "Enabled (LearnerDecide l b v) st = ChosenIn st l b v"
  using Enabled.simps LearnerDecide.simps by presburger

(*Weak fairness*)
fun WF :: "(State \<Rightarrow> State \<Rightarrow> bool) \<Rightarrow> (nat \<Rightarrow> State) \<Rightarrow> bool" where
  "WF p f = (
    \<forall>i. (\<forall>j \<ge> i. Enabled p (f j)) \<longrightarrow> (\<exists>j \<ge> i. p (f j) (f (j + 1)))
  )"

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

lemma Process1a_Req_msgs:
  assumes "Spec f"
      and "is_safe a"
      and "Process1a a x (f (i - 1)) (f i)"
    shows "x \<in> set (msgs (f i))"
proof -
  have "x \<in> set (known_msgs_acc (f i) a)"
    by (metis Process1a.elims(2) Store_acc.elims(2) assms(3) in_set_member member_rec(1))
  have q: "(\<forall>m \<in> set (known_msgs_acc (f i) a). 
          m \<in> set (msgs (f i)) \<and>
          Proper_acc (f i) a m \<and>
          WellFormed (f i) m \<and>
          Tran m \<subseteq> set (known_msgs_acc (f i) a) \<and>
          (\<exists>b :: Ballot. B m b)
    )"
    by (meson KnownMsgs_accSpec.elims(2) KnownMsgs_accSpecResult assms(1) assms(2))
  show ?thesis
    by (simp add: \<open>x \<in> set (known_msgs_acc (f i) a)\<close> q)
qed


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
  assumes "LearnerAction st st2"
      and "Enabled (AcceptorAction a) st"
    shows "Enabled (AcceptorAction a) st2"
proof -
  have "LearnerAction st st2"
    using assms(1) by blast
  then show ?thesis
    unfolding LearnerAction.simps
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


*)




(*
(queued_msg st a = None \<or> 
        type (the (queued_msg st a)) \<noteq> T1b \<or> 
        \<not> Recv_acc st a (the (queued_msg st a))) \<and> 
     (queued_msg st a \<noteq> None \<or> (
         \<forall>m \<in> set (msgs st). \<not> Recv_acc st a m \<or> (type m \<noteq> T1a \<and> type m \<noteq> T1b)
     ))
*)

(*
  proof (cases "queued_msg (f i) a = None")
    case True
    have "\<exists>m \<in> set (msgs st). Process1b a m st st2"
      using AcceptorAction.simps Process1b_Not_Process1a True \<open>\<not> two_a_lrn_loop st a\<close> assms(2) qa st2_def st_def by blast
    then show ?thesis sorry
  next
    case False
    have "Process1b a (the (queued_msg st a)) st st2"
      by (metis AcceptorAction.elims(2) False \<open>\<not> two_a_lrn_loop st a\<close> qa st_def)
    have "type (the (queued_msg st2 a)) \<noteq> T1b \<or> 
        \<not> Recv_acc st2 a (the (queued_msg st2 a))"
      sorry
    then show ?thesis sorry
  qed
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
      using assms(2) True st2_def by force
    then show ?thesis
      by (metis AcceptorAction.elims(2) AcceptorAction_Enabled qa st2_def)
  next
    case False
    have "\<not> two_a_lrn_loop st2 a"
      using False \<open>\<not> two_a_lrn_loop st a\<close> assms(2) st2_def st_def by auto
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
        by (metis Proper_acc.simps Recv_acc.elims(2) \<open>Recv_acc st a m2\<close> add.commute assms(1) spec_known_msgs_acc_preserved st2_def st_def)
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

lemma Preserves_AcceptorAction_Disabled_Three_Cases:
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

lemma AcceptorAction_Disabled_When_No_Messages:
  assumes "Spec f"
      and "Enabled (AcceptorAction a) (f i)"
      and "\<not> Enabled (AcceptorAction a) (f (1 + i))"
    shows "\<not> (\<exists>m \<in> set (msgs (f (i + 1))). Recv_acc (f (i + 1)) a m \<and> (type m = T1a \<or> type m = T1b))"
proof -
  have "(\<exists>m. Process1a a m (f i) (f (1 + i)) 
              \<and> \<not> WellFormed (f i) (M1b a (m # recent_msgs (f i) a)) 
              \<and> \<not> (\<exists>m2 \<in> set (msgs (f i)). m2 \<noteq> m \<and> Recv_acc (f i) a m2 \<and> (type m2 = T1a \<or> type m2 = T1b))) \<or>
        (\<exists>m. Process1b a m (f i) (f (1 + i)) 
              \<and> \<not> (\<forall> mb b :: Ballot. MaxBal (f i) a b \<and> B m b \<longrightarrow> mb \<le> b)
              \<and> \<not> (\<exists>m2 \<in> set (msgs (f i)). m2 \<noteq> m \<and> Recv_acc (f i) a m2 \<and> (type m2 = T1a \<or> type m2 = T1b))) \<or>
        (Process1bLearnerLoopDone a (f i) (f (1 + i)) 
              \<and> \<not> (\<exists>m \<in> set (msgs (f i)). Recv_acc (f i) a m \<and> (type m = T1a \<or> type m = T1b)))"
    using Preserves_AcceptorAction_Disabled_Three_Cases assms(1) assms(2) assms(3) by presburger
  then show ?thesis
  proof (elim disjE; clarify)
    fix m m2
    assume "Process1a a m (f i) (f (1 + i))"
       and "\<not> WellFormed (f i) (M1b a (m # recent_msgs (f i) a))"
       and "\<not> (\<exists>m2 \<in> set (msgs (f i)). m2 \<noteq> m \<and> Recv_acc (f i) a m2 \<and> (type m2 = T1a \<or> type m2 = T1b))"
       and "m2 \<in> set (msgs (f (i + 1)))"
       and "Recv_acc (f (i + 1)) a m2"
       and "type m2 = T1a \<or> type m2 = T1b"
    have "m2 \<noteq> m"
      by (metis Process1a.elims(2) Recv_acc.elims(2) Store_acc.elims(2) \<open>Process1a a m (f i) (f (1 + i))\<close> \<open>Recv_acc (f (i + 1)) a m2\<close> add.commute list.set_intros(1))
    have "m2 \<in> set (msgs (f i))"
      by (metis Process1a.elims(2) \<open>Process1a a m (f i) (f (1 + i))\<close> \<open>\<not> WellFormed (f i) (M1b a (m # recent_msgs (f i) a))\<close> \<open>m2 \<in> set (msgs (f (i + 1)))\<close> add.commute)
    show False
      by (metis (no_types, opaque_lifting) AcceptorAction_Enabled AcceptorAction_NotEnabled MessageType.distinct(1) Process1a.simps QueuedMsgResult QueuedMsgSpec1.elims(2) \<open>Process1a a m (f i) (f (1 + i))\<close> \<open>Recv_acc (f (i + 1)) a m2\<close> \<open>\<not> (\<exists>m2\<in>set (msgs (f i)). m2 \<noteq> m \<and> Recv_acc (f i) a m2 \<and> (type m2 = T1a \<or> type m2 = T1b))\<close> \<open>\<not> WellFormed (f i) (M1b a (m # recent_msgs (f i) a))\<close> \<open>m2 \<in> set (msgs (f (i + 1)))\<close> \<open>type m2 = T1a \<or> type m2 = T1b\<close> add.commute assms(1) assms(2) assms(3))
  next
    fix m m2
    assume "Process1b a m (f i) (f (1 + i))"
       and "\<not> (\<exists>m2 \<in> set (msgs (f i)). m2 \<noteq> m \<and> Recv_acc (f i) a m2 \<and> (type m2 = T1a \<or> type m2 = T1b))"
       and "m2 \<in> set (msgs (f (i + 1)))"
       and "Recv_acc (f (i + 1)) a m2"
       and "type m2 = T1a \<or> type m2 = T1b"
    have "m2 \<noteq> m"
      by (metis Process1b.elims(2) Recv_acc.elims(2) Store_acc.elims(2) \<open>Process1b a m (f i) (f (1 + i))\<close> \<open>Recv_acc (f (i + 1)) a m2\<close> add.commute list.set_intros(1))
    have "m2 \<in> set (msgs (f i))"
      by (metis Process1b.elims(2) \<open>Process1b a m (f i) (f (1 + i))\<close> \<open>m2 \<in> set (msgs (f (i + 1)))\<close> add.commute)
    show False
      by (metis (full_types) AcceptorAction_Enabled Process1b.elims(2) Suc_eq_plus1 \<open>Process1b a m (f i) (f (1 + i))\<close> \<open>Recv_acc (f (i + 1)) a m2\<close> \<open>m2 \<in> set (msgs (f (i + 1)))\<close> \<open>type m2 = T1a \<or> type m2 = T1b\<close> assms(2) assms(3) plus_1_eq_Suc)
  next
    fix m m2
    assume "Process1bLearnerLoopDone a (f i) (f (1 + i))"
       and "\<not> (\<exists>m \<in> set (msgs (f i)). Recv_acc (f i) a m \<and> (type m = T1a \<or> type m = T1b))"
       and "m2 \<in> set (msgs (f (i + 1)))"
       and "Recv_acc (f (i + 1)) a m2"
       and "type m2 = T1a \<or> type m2 = T1b"
    have "m2 \<in> set (msgs (f i))"
      using \<open>Process1bLearnerLoopDone a (f i) (f (1 + i))\<close> \<open>m2 \<in> set (msgs (f (i + 1)))\<close> by force
    have "Recv_acc (f i) a m2"
      using \<open>Process1bLearnerLoopDone a (f i) (f (1 + i))\<close> \<open>Recv_acc (f (i + 1)) a m2\<close> by auto
    show False
      using \<open>Recv_acc (f i) a m2\<close> \<open>\<not> (\<exists>m\<in>set (msgs (f i)). Recv_acc (f i) a m \<and> (type m = T1a \<or> type m = T1b))\<close> \<open>m2 \<in> set (msgs (f i))\<close> \<open>type m2 = T1a \<or> type m2 = T1b\<close> by blast
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


theorem LivenessResult :
  assumes "Spec f"
  shows "Liveness f"
  sorry

end