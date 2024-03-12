theory hpaxos_liveness
imports Main hpaxos hpaxos_safety
begin

(*
WF_vars(\E v \in Value : LearnerDecide(L, b, v))
*)

(* Send1a is always enabled.
fun Send1a_Enabled :: "Ballot \<Rightarrow> State \<Rightarrow> bool" where
  "Send1a_Enabled b st = True"
*)

fun Process1a_Enabled :: "Acceptor \<Rightarrow> PreMessage \<Rightarrow> State \<Rightarrow> bool" where
  "Process1a_Enabled a m st = (
    type m = T1a \<and>
    Recv_acc st a m
  )"

fun Process1b_Enabled :: "Acceptor \<Rightarrow> PreMessage \<Rightarrow> State \<Rightarrow> bool" where
  "Process1b_Enabled a m st = (
    type m = T1b
    \<and> Recv_acc st a m
  )"

(* Process1bLearnerLoop is always enabled.
fun Process1bLearnerLoop_Enabled :: "Acceptor \<Rightarrow> State \<Rightarrow> bool" where
  "Process1bLearnerLoop_Enabled a st = True"
*)

fun LearnerRecv_Enabled :: "Learner \<Rightarrow> PreMessage \<Rightarrow> State \<Rightarrow> bool" where
  "LearnerRecv_Enabled l m st = (
    Recv_lrn st l m
  )"

fun LearnerDecide_Enabled :: "Learner \<Rightarrow> Ballot \<Rightarrow> Value \<Rightarrow> State \<Rightarrow> bool" where
  "LearnerDecide_Enabled l b v st = ChosenIn st l b v"

fun WF :: "(State \<Rightarrow> bool) \<Rightarrow> (State \<Rightarrow> State \<Rightarrow> bool) \<Rightarrow> (nat \<Rightarrow> State) \<Rightarrow> bool" where
  "WF p_Enabled p f = (
    \<forall>i. (\<forall>j \<ge> i. p_Enabled (f j)) \<longrightarrow> (\<exists>j \<ge> i. p (f j) (f (j + 1)))
  )"


fun Liveness :: "(nat \<Rightarrow> State) \<Rightarrow> bool" where
  "Liveness f = (
    \<forall> L :: Learner. \<forall> b :: Ballot. \<forall>Q :: Acceptor set. is_quorum Q \<longrightarrow>
    (\<forall>a \<in> Q. is_safe a) \<and> (
    TrustLive L Q \<longrightarrow> (
    ((\<forall>m :: PreMessage. type m = T1a \<longrightarrow> bal m < b) \<and>
     (\<forall>c :: Ballot. c > b \<longrightarrow> (\<forall>j. \<not> (Send1a c (f j) (f (1 + j))))) \<and>
     (WF (\<lambda>x. True) (Send1a b) f) \<and>
     (\<forall>m :: PreMessage. B m b \<longrightarrow> (\<forall>a \<in> Q. WF (Process1a_Enabled a m) (Process1a a m) f)) \<and>
     (\<forall>m :: PreMessage. B m b \<longrightarrow> (\<forall>a \<in> Q. WF (Process1b_Enabled a m) (Process1b a m) f)) \<and>
     (\<forall>a \<in> Q. WF (\<lambda>x. True) (Process1bLearnerLoop a) f) \<and>
     (\<forall>m :: PreMessage. B m b \<longrightarrow> WF (LearnerRecv_Enabled L m) (LearnerRecv L m) f) \<and>
     (WF (\<lambda>st. \<exists> v :: Value. LearnerDecide_Enabled L b v st) 
         (\<lambda>st st2. \<exists> v :: Value. LearnerDecide L b v st st2) f)
    ) \<longrightarrow> (\<exists>j. \<exists> BB :: Ballot . decision (f j) L BB \<noteq> {})
  )))"



theorem LivenessResult :
  assumes "Spec f"
  shows "Liveness f"
sorry

end