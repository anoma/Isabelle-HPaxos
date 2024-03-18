theory hpaxos_liveness_old
imports Main hpaxos hpaxos_safety
begin

fun Termination_lrn :: "(nat \<Rightarrow> State) \<Rightarrow> Learner \<Rightarrow> bool" where
  "Termination_lrn f l = (\<exists>n :: nat. \<exists>b :: Ballot. decision (f n) l b \<noteq> {})"

fun Termination :: "(nat \<Rightarrow> State) \<Rightarrow> bool" where
  "Termination f = 
     (\<forall>l :: Learner.  
        (\<exists>Q :: Acceptor set. Q \<subseteq> {x . is_safe x} \<and> TrustLive l Q) \<longrightarrow>
        Termination_lrn f l)"

(*Extract consecutive runs of given lengths from a stream*)
fun sequence_of_runs :: "nat \<Rightarrow> nat list \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> ('a list) list" where
  "sequence_of_runs start [] f = []" |
  "sequence_of_runs start (len # lens) f = 
    map f [start ..< start + len] # sequence_of_runs (start + len) lens f"

theorem sequence_of_runs_length:
  shows "length (sequence_of_runs start lens f) = length lens"
proof (induction lens arbitrary: start; simp) qed

fun runs_assumption :: "Acceptor set \<Rightarrow> State \<Rightarrow> (State list) list \<Rightarrow> bool" where
  "runs_assumption qu st runs = True"

fun network_assumption :: "Learner \<Rightarrow> (nat \<Rightarrow> State) \<Rightarrow> bool" where
"network_assumption l f = 
    (\<exists>start lens qu. length lens = 13 \<and> (\<forall>i<13. lens ! i > 0) \<and> 
      TrustLive l qu \<and>
      runs_assumption qu (f (start - 1)) (sequence_of_runs start lens f))"






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


end