theory hpaxos_liveness
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

lemma sequence_of_runs_length_invar:
  shows "\<forall> start1 start2 f1 f2. 
           length (sequence_of_runs start1 lens f1) 
           = length (sequence_of_runs start2 lens f2)"
proof (induction lens; simp) qed

theorem sequence_of_runs_length:
  shows "length (sequence_of_runs start lens f) = length lens"
proof (induction lens)
  case Nil
  then show ?case by simp
next
  case (Cons a lens)
  then show ?case 
    by (metis length_Cons sequence_of_runs.simps(2) sequence_of_runs_length_invar)
qed



fun runs_assumption :: "(State list) list \<Rightarrow> bool" where
  "runs_assumption runs = True"

fun network_assumption :: "(nat \<Rightarrow> State) \<Rightarrow> bool" where
"network_assumption f = 
    (\<exists>start lens. length lens = 13 \<and> (\<forall>i<13. lens ! i > 0) \<and> 
                  runs_assumption (sequence_of_runs start lens f))"



end