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



end