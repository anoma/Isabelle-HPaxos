theory hpaxos
imports Main
begin

typedecl Acceptor
typedecl Learner

typedecl Value
consts arbitrary_Value :: Value

consts is_safe :: "Acceptor \<Rightarrow> bool"

(* Doesn't work since these aren't necessarily inhabited, 
  but these should be conceptually true

typedef SafeAcceptor = "{a::Acceptor. is_safe a}"
typedef FakeAcceptor = "{a::Acceptor. \<not> is_safe a}"
*)

type_synonym Ballot = nat
consts LastBallot :: Ballot

consts is_quorum :: "Acceptor set \<Rightarrow> bool"

axiomatization where
  safe_is_quorum: "is_quorum {x . is_safe x}"

typedef (overloaded) ByzQuorum = "{a::Acceptor set. is_quorum a}"
proof
  show "{x . is_safe x} \<in> {a::Acceptor set. is_quorum a}"
    using safe_is_quorum by simp
qed

(* Learner graph *)
(* ------------------------------------------------------------------- *)

consts TrustLive :: "Learner \<Rightarrow> Acceptor set \<Rightarrow> bool"
consts TrustSafe :: "Learner \<Rightarrow> Learner \<Rightarrow> Acceptor set \<Rightarrow> bool"

axiomatization where
  TrustLiveAssumption: "\<forall>l q. (TrustLive l q \<longrightarrow> is_quorum q)"

axiomatization where
  TrustSafeAssumption: "\<forall>l1 l2 q. (TrustSafe l1 l2 q \<longrightarrow> is_quorum q)"

axiomatization where
  LearnerGraphAssumptionSymmetry: 
    "\<forall>l1 l2 q. (TrustSafe l1 l2 q \<longrightarrow> TrustSafe l2 l1 q)"

axiomatization where
  LearnerGraphAssumptionTransitivity:
    "\<forall>l1 l2 l3 q. (TrustSafe l1 l2 q \<and> TrustSafe l2 l3 q \<longrightarrow> TrustSafe l1 l2 q)"

axiomatization where
  LearnerGraphAssumptionClosure:
    "\<forall>l1 l2 q Q. (TrustSafe l1 l2 q \<and> is_quorum Q \<and> q \<subseteq> Q \<longrightarrow> TrustSafe l1 l2 q2)"

axiomatization where
  LearnerGraphAssumptionValidity:
    "\<forall>l1 l2 q Q1 Q2. (
      TrustSafe l1 l2 q \<and> is_quorum Q1 \<and> is_quorum Q2 \<and>
      TrustLive l1 Q1 \<and> TrustLive l2 Q2 \<longrightarrow> (
      \<exists> N:: Acceptor. N \<in> q \<and> N \<in> Q1 \<and> N \<in> Q2))"

(* Entanglement relation *)
fun ent :: "Learner \<Rightarrow> Learner \<Rightarrow> bool" where
  "ent l1 l2 = TrustSafe l1 l2 {x . is_safe x}"

(* Messages *)
(* ------------------------------------------------------------------- *)

consts MaxRefCardinality :: nat

axiomatization where
  MaxRefCardinalityAssumption:
    "MaxRefCardinality \<ge> 1"

(*consts MaxMessageDepth :: nat*)

(*type_synonym MessageDepthRange = nat*)

(*
Morally, messages have the following inductive structure

M1a : \<forall> n: nat. Ballot \<Rightarrow> MessageRec n
M1b : \<forall> n: nat. Acceptor \<Rightarrow> FINSUBSET(MessageRec n, MessageDepthRange) \<Rightarrow> MessageRec (n + 1)
M2a : \<forall> n: nat. Learner \<Rightarrow> Acceptor \<Rightarrow> FINSUBSET(MessageRec n, MessageDepthRange) \<Rightarrow> MessageRec (n + 1)

Message \<equiv> \<Union>n. {MessageRec n}
*)

datatype PreMessage = 
  M1a Ballot 
| M1b Acceptor "PreMessage list" 
| M2a Learner Acceptor "PreMessage list"

fun isValidMessage :: "PreMessage \<Rightarrow> bool" where
  "isValidMessage (M1a _) = True" |
  "isValidMessage (M1b _ msgs) = (msgs \<noteq> [] \<and> length msgs \<le> MaxRefCardinality \<and> list_all isValidMessage msgs)" |
  "isValidMessage (M2a _ _ msgs) = (msgs \<noteq> [] \<and> length msgs \<le> MaxRefCardinality \<and> list_all isValidMessage msgs)"

typedef (overloaded) Message = "{a::PreMessage. isValidMessage a}"
proof
  show "M1a 0 \<in> {a::PreMessage. isValidMessage a}"
    by simp
qed

datatype MessageType = T1a | T1b | T2a

fun type :: "PreMessage \<Rightarrow> MessageType" where
  "type (M1a _) = T1a" |
  "type (M1b _ msgs) = T1b" |
  "type (M2a _ _ msgs) = T2a"

fun ref :: "PreMessage \<Rightarrow> PreMessage set" where
  "ref (M1a _) = {}" |
  "ref (M1b _ msgs) = set msgs" |
  "ref (M2a _ _ msgs) = set msgs"  

fun acc :: "PreMessage \<Rightarrow> Acceptor" where
  "acc (M1a _) = undefined" |
  "acc (M1b a _) = a" |
  "acc (M2a _ a _) = a"

fun lrn :: "PreMessage \<Rightarrow> Learner" where
  "lrn (M1a _) = undefined" |
  "lrn (M1b _ _) = undefined" |
  "lrn (M2a l _ _) = l"

(* Transitive references *)
(* ------------------------------------------------------------------- *)

(*If we always want TranDepthRange to be finite, we can simply do*)
fun TranF :: "nat \<Rightarrow> PreMessage \<Rightarrow> PreMessage set" where
  "TranF 0 m = {m}" |
  "TranF n (M1a a) = {M1a a}" |
  "TranF n (M1b a msgs) = {M1b a msgs} \<union> \<Union> (TranF (n-1) ` set msgs)" |
  "TranF n (M2a a l msgs) = {M2a a l msgs} \<union> \<Union> (TranF (n-1) ` set msgs)"  

(* This is Tran as it actually is in the original file *)
fun Tran :: "PreMessage \<Rightarrow> PreMessage set" where
  "Tran (M1a a) = {M1a a}" |
  "Tran (M1b a msgs) = {M1b a msgs} \<union> \<Union> (Tran ` set msgs)" |
  "Tran (M2a a l msgs) = {M2a a l msgs} \<union> \<Union> (Tran ` set msgs)"  

theorem Valid_contains_ballot:
  assumes "isValidMessage m"
  shows "\<exists>a. M1a a \<in> Tran m"
using assms
proof (induction m)
  case (M1a a)
  then show ?case by simp
next
  case (M1b a msgs)
  then show ?case
    by (metis Ball_set Tran.simps(2) UN_I UnCI isValidMessage.simps(2) last_in_set)
next
  case (M2a a l msgs)
  then show ?case
    by (metis Ball_set Tran.simps(3) UN_I UnCI isValidMessage.simps(3) last_in_set)
qed

(* Algorithm specification *)
(* ------------------------------------------------------------------- *)

(*
A bit different than the original.
The original returned the singleton set containing
The largest Ballot. Here, we just return the largest Ballot

Note that, in the case that a PreMessage isn't valid,
this may be in error as Max may be called on an empty set.
*)
fun Get1a :: "PreMessage \<Rightarrow> Ballot" where
  "Get1a m = Max {a . M1a a \<in> Tran m}"

fun B :: "PreMessage \<Rightarrow> Ballot \<Rightarrow> bool" where
  "B m bal = (bal = Get1a m)"

record State =
  msgs :: "PreMessage list"
  known_msgs_acc :: "Acceptor \<Rightarrow> PreMessage list"
  known_msgs_lrn :: "Learner \<Rightarrow> PreMessage list"
  recent_msgs_acc :: "Acceptor \<Rightarrow> PreMessage list"
  recent_msgs_lrn :: "Learner \<Rightarrow> PreMessage list"
  queued_msg :: "Acceptor \<Rightarrow> PreMessage option"
  two_a_lrn_loop :: "Acceptor \<Rightarrow> bool"
  processed_lrns :: "Acceptor \<Rightarrow> Learner set"
  decision :: "Learner \<Rightarrow> Ballot \<Rightarrow> Value set"
  BVal :: "Ballot \<Rightarrow> Value"

definition NoMessage :: "PreMessage option" where
  "NoMessage = None"

fun Init :: "(Ballot \<Rightarrow> Value) \<Rightarrow> State" where
  "Init bval = \<lparr> 
      msgs = [], 
      known_msgs_acc = (\<lambda>_. []), 
      known_msgs_lrn = (\<lambda>_. []), 
      recent_msgs_acc = (\<lambda>_. []), 
      recent_msgs_lrn = (\<lambda>_. []), 
      queued_msg = (\<lambda>_. NoMessage), 
      two_a_lrn_loop = (\<lambda>_. False), 
      processed_lrns = (\<lambda>_. {}), 
      decision = (\<lambda>_ _. {}), 
      BVal = bval 
    \<rparr>"

fun V :: "State \<Rightarrow> PreMessage \<Rightarrow> Value \<Rightarrow> bool" where
  "V st m val = (val = BVal st (Get1a m))"

(*Maximal ballot number of any messages known to acceptor a*)
(* Direct translation *)
fun MaxBalL :: "State \<Rightarrow> Acceptor \<Rightarrow> Ballot \<Rightarrow> bool" where
  "MaxBalL st a mbal = 
      ((\<exists> m \<in> set (known_msgs_acc st a). B m mbal)
      \<and> (\<forall> x \<in> set (known_msgs_acc st a).
          \<forall> b :: Ballot. B x b \<longrightarrow> b \<le> mbal))"

(*Better implementation*)
fun MaxBalO :: "State \<Rightarrow> Acceptor \<Rightarrow> Ballot option" where
  "MaxBalO st a = 
    (if known_msgs_acc st a = [] then None else
     Some (Max (Get1a ` set (known_msgs_acc st a))))"

fun MaxBal :: "State \<Rightarrow> Acceptor \<Rightarrow> Ballot \<Rightarrow> bool" where
  "MaxBal st a mbal = (Some mbal = MaxBalO st a)"

fun SameBallot :: "PreMessage \<Rightarrow> PreMessage \<Rightarrow> bool" where
  "SameBallot x y = (\<forall> b. B x b = B y b)"

(*
The acceptor is _caught_ in a message x if the transitive references of x
include evidence such as two messages both signed by the acceptor, in which
neither is featured in the other's transitive references.
*)
fun CaughtMsg :: "PreMessage \<Rightarrow> PreMessage set" where
  "CaughtMsg x = 
    { m . m \<in> Tran x 
        \<and> type m \<noteq> T1a
        \<and> (\<exists> m1 \<in> Tran x.
              type m1 \<noteq> T1a
           \<and> acc m = acc m1
           \<and> m \<notin> Tran m1
           \<and> m1 \<notin> Tran m
        ) }"

fun Caught :: "PreMessage \<Rightarrow> Acceptor set" where
  "Caught x = acc ` { m . m \<in> CaughtMsg x }"

fun ConByQuorum :: "Learner \<Rightarrow> Learner \<Rightarrow> PreMessage \<Rightarrow> Acceptor set \<Rightarrow> bool" where
  "ConByQuorum a b x S = (
      TrustSafe a b S \<and> 
      Caught x \<inter> S = {}
    )"

fun Con :: "Learner \<Rightarrow> PreMessage \<Rightarrow> Learner set" where
  "Con a x = {b . \<exists> S. is_quorum S \<and> ConByQuorum a b x S}"

(*
2a-message is _buried_ if there exists a quorum of acceptors that have seen
2a-messages with different values, the same learner, and higher ballot
numbers.
*)
fun Buried :: "State \<Rightarrow> PreMessage \<Rightarrow> PreMessage \<Rightarrow> bool" where
  "Buried st x y = 
    (let Q :: PreMessage set = 
      { m. m \<in> Tran y 
          \<and> (\<exists>z \<in> Tran m.
                  type z = T2a
                \<and> lrn z = lrn x
                \<and> (\<forall> bx bz :: Ballot.
                      B x bx \<and> B z bz \<longrightarrow> bx < bz
                  )
                \<and> (\<forall> vx vz :: Value.
                      V st x vx \<and> V st z vz \<longrightarrow> vx \<noteq> vz
                  )
            ) }
     in TrustLive (lrn x) (acc ` Q)
    )
  "

(* Connected 2a messages *)
fun Con2as :: "State \<Rightarrow> Learner \<Rightarrow> PreMessage \<Rightarrow> PreMessage set" where
  "Con2as st l x = 
    { m . m \<in> Tran x
        \<and> type m = T2a
        \<and> acc m = acc x
        \<and> \<not> (Buried st m x)
        \<and> lrn m \<in> Con l x
    }"

(*Fresh 1b messages*)
fun Fresh :: "State \<Rightarrow> Learner \<Rightarrow> PreMessage \<Rightarrow> bool" where
  "Fresh st l x =
    (\<forall>m \<in> Con2as st l x. \<forall>v :: Value. V st x v = V st m v)
  "

(* Quorum of messages referenced by 2a *)
fun q :: "State \<Rightarrow> PreMessage \<Rightarrow> Acceptor set" where
  "q st x =
    acc ` { m . m \<in> Tran x
                \<and> type m = T1b
                \<and> Fresh st (lrn x) m
                \<and> (\<forall>b :: Ballot. B m b = B x b)
          }"

fun WellFormed :: "State \<Rightarrow> PreMessage \<Rightarrow> bool" where
  "WellFormed st m = (
    isValidMessage m
    \<and> (\<exists> b :: Ballot. B m b)
    \<and> (type m = T1b \<longrightarrow> (\<forall>y \<in> Tran m. m \<noteq> y \<and> SameBallot m y \<longrightarrow> type y = T1a))
    \<and> (type m = T2a \<longrightarrow> TrustLive (lrn m) (q st m))
  )"


(*Transition Functions*)

(*Send(m) == msgs' = msgs \cup {m}*)
fun Send :: "PreMessage \<Rightarrow> State \<Rightarrow> State \<Rightarrow> bool" where
  "Send m st st2 = (msgs st2 = m # msgs st)"

(*Proper_acc(a, m) == \A r \in m.ref : r \in known_msgs[a]*)
fun Proper_acc :: "State \<Rightarrow> Acceptor \<Rightarrow> PreMessage \<Rightarrow> bool" where
  "Proper_acc st a m = (\<forall> r \<in> ref m. r \<in> set (known_msgs_acc st a))"

fun Proper_lrn :: "State \<Rightarrow> Learner \<Rightarrow> PreMessage \<Rightarrow> bool" where
  "Proper_lrn st l m = (\<forall> r \<in> ref m. r \<in> set (known_msgs_lrn st l))"

fun Recv_acc :: "State \<Rightarrow> Acceptor \<Rightarrow> PreMessage \<Rightarrow> bool" where
  "Recv_acc st a m = (
    m \<notin> set (known_msgs_acc st a)
    \<and> WellFormed st m
    \<and> Proper_acc st a m
  )"

fun Recv_lrn :: "State \<Rightarrow> Learner \<Rightarrow> PreMessage \<Rightarrow> bool" where
  "Recv_lrn st l m = (
    m \<notin> set (known_msgs_lrn st l)
    \<and> WellFormed st m
    \<and> Proper_lrn st l m
  )"

fun Store_acc :: "Acceptor \<Rightarrow> PreMessage \<Rightarrow> State \<Rightarrow> State \<Rightarrow> bool" where 
  "Store_acc a m st st2 = (
    known_msgs_acc st2 = (
        \<lambda>x. if a = x 
            then m # known_msgs_acc st x
            else known_msgs_acc st x
    )
    \<and> known_msgs_lrn st2 = known_msgs_lrn st
  )"

fun Store_lrn :: "Learner \<Rightarrow> PreMessage \<Rightarrow> State \<Rightarrow> State \<Rightarrow> bool" where 
  "Store_lrn l m st st2 = (
    known_msgs_lrn st2 = (
        \<lambda>x. if l = x 
            then m # known_msgs_lrn st x
            else known_msgs_lrn st x
    )
    \<and> known_msgs_acc st2 = known_msgs_acc st
  )"

fun Send1a :: "Ballot \<Rightarrow> State \<Rightarrow> State \<Rightarrow> bool" where
  "Send1a b st st2 = (st2 = st\<lparr>msgs := M1a b # msgs st\<rparr>)"

fun Known2a :: "State \<Rightarrow> Learner \<Rightarrow> Ballot \<Rightarrow> Value \<Rightarrow> PreMessage set" where
  "Known2a st l b v = 
    {x . x \<in> set (known_msgs_lrn st l) 
      \<and> type x = T2a 
      \<and> lrn x = l 
      \<and> B x b 
      \<and> V st x v  }"

(*
The following is invariant for queued_msg variable values.
For any safe acceptor A, if queued_msg[A] # NoMessage then
queued_msg[A] is a well-formed message of type "1b" sent by A,
having the direct references all known to A.
*)

(*Process1a, Process1b, and Process2a rolled into a function*)
fun Process :: "Acceptor \<Rightarrow> PreMessage \<Rightarrow> State \<Rightarrow> State" where
  "Process a m st = (
    if \<not> (Recv_acc st a m)
    then st
    else let stp = 
      st\<lparr>known_msgs_acc := 
          \<lambda>x. if a = x 
              then m # known_msgs_acc st x
              else known_msgs_acc st x\<rparr> in
    case m of
      M1a a2 \<Rightarrow> 
        let new1b = M1b a (m # recent_msgs_acc st a) in 
        if WellFormed st new1b
        then stp\<lparr>msgs := new1b # msgs st,
                 recent_msgs_acc := 
                   \<lambda>x. if x = a 
                       then [] 
                       else recent_msgs_acc st x,
                 queued_msg := 
                   \<lambda>x. if x = a 
                       then Some new1b 
                       else queued_msg st x\<rparr>
        else stp\<lparr>recent_msgs_acc :=
                   \<lambda>x. if x = a 
                       then m # recent_msgs_acc st x 
                       else recent_msgs_acc st x\<rparr>
    | M1b a2 ms \<Rightarrow> 
        let stpp = 
          stp\<lparr>queued_msg := 
                  \<lambda>x. if x = a
                      then None
                      else queued_msg st x,
              recent_msgs_acc :=
                  \<lambda>x. if x = a 
                      then m # recent_msgs_acc st x 
                      else recent_msgs_acc st x\<rparr> in
        if \<not> (\<forall> mb b :: Ballot. MaxBal st a b \<and> B m b \<longrightarrow> mb \<le> b)
        then stpp
        else stpp\<lparr>two_a_lrn_loop := 
                    \<lambda>x. if x = a
                        then True
                        else two_a_lrn_loop st x,
                  processed_lrns :=
                    \<lambda>x. if x = a
                        then {}
                        else processed_lrns st x\<rparr>
    | M2a a2 l ms \<Rightarrow> 
        stp\<lparr>recent_msgs_acc :=
                \<lambda>x. if x = a 
                    then m # recent_msgs_acc st x 
                    else recent_msgs_acc st x\<rparr>
  )"

(* Process1a as a predicate *)
fun Process1a :: "Acceptor \<Rightarrow> PreMessage \<Rightarrow> State \<Rightarrow> State \<Rightarrow> bool" where
  "Process1a a m st st2 = (
    let new1b = M1b a (m # recent_msgs_acc st a) in 
    type m = T1a
    \<and> Recv_acc st a m
    \<and> Store_acc a m st st2
    \<and> (if WellFormed st new1b
       then 
          Send new1b st st2
          \<and> (recent_msgs_acc st2 = (
              \<lambda>a2. if a2 = a then [] 
                             else recent_msgs_acc st a2))
          \<and> (queued_msg st2 = (
              \<lambda>a2. if a2 = a then Some new1b 
                             else queued_msg st a2))
       else 
          (recent_msgs_acc st2 = (
              \<lambda>a2. if a2 = a then m # recent_msgs_acc st a2 
                             else recent_msgs_acc st a2))
          \<and> (msgs st = msgs st2)
          \<and> (queued_msg st = queued_msg st2)
      )

    \<and> (recent_msgs_lrn st2 = recent_msgs_lrn st)
    \<and> (two_a_lrn_loop st2 = two_a_lrn_loop st)
    \<and> (processed_lrns st2 = processed_lrns st)
    \<and> (decision st2 = decision st)
    \<and> (BVal st2 = BVal st)
  )"

(* Process1b as a predicate *)
fun Process1b :: "Acceptor \<Rightarrow> PreMessage \<Rightarrow> State \<Rightarrow> State \<Rightarrow> bool" where
  "Process1b a m st st2 = (
    type m = T1b
    \<and> Recv_acc st a m
    \<and> Store_acc a m st st2
    \<and> recent_msgs_acc st2 = (
        \<lambda>x. if x = a 
            then m # recent_msgs_acc st x
            else recent_msgs_acc st x )
    \<and> recent_msgs_lrn st2 = recent_msgs_lrn st
    \<and> ((\<forall> mb b :: Ballot. MaxBal st a b \<and> B m b \<longrightarrow> mb \<le> b) \<longrightarrow>
        two_a_lrn_loop st2 = (\<lambda>x.
          if x = a
          then True
          else two_a_lrn_loop st x)
        \<and> processed_lrns st2 = (\<lambda>x.
          if x = a
          then {}
          else processed_lrns st x)
      )
    \<and> (\<not> (\<forall> mb b :: Ballot. MaxBal st a b \<and> B m b \<longrightarrow> mb \<le> b) \<longrightarrow>
        two_a_lrn_loop st2 = two_a_lrn_loop st
        \<and> processed_lrns st2 = processed_lrns st
      )
    \<and> (queued_msg st2 = (\<lambda>x.
          if x = a
          then None
          else queued_msg st x))

    \<and> (msgs st2 = msgs st)
    \<and> (decision st2 = decision st)
    \<and> (BVal st2 = BVal st)
  )"

(* Process2a as a predicate *)
fun Process2a :: "Acceptor \<Rightarrow> PreMessage \<Rightarrow> State \<Rightarrow> State \<Rightarrow> bool" where
  "Process2a a m st st2 = (
    type m = T2a
    \<and> Recv_acc st a m
    \<and> Store_acc a m st st2
    \<and> recent_msgs_acc st2 = (
        \<lambda>x. if x = a 
            then m # recent_msgs_acc st x
            else recent_msgs_acc st x )
    \<and> recent_msgs_lrn st2 = recent_msgs_lrn st

    \<and> (msgs st2 = msgs st)
    \<and> (queued_msg st2 = queued_msg st)
    \<and> (two_a_lrn_loop st2 = two_a_lrn_loop st)
    \<and> (processed_lrns st2 = processed_lrns st)
    \<and> (decision st2 = decision st)
    \<and> (BVal st2 = BVal st)
  )"

fun ProposerSendAction :: "State \<Rightarrow> State \<Rightarrow> bool" where
  "ProposerSendAction st st2 = (\<exists>bal :: Ballot. Send1a bal st st2)"

fun Process1bLearnerLoopStep :: "Acceptor \<Rightarrow> Learner \<Rightarrow> State \<Rightarrow> State \<Rightarrow> bool" where
  "Process1bLearnerLoopStep a ln st st2 = (
    let new2a = M2a ln a (recent_msgs_acc st a) in
    processed_lrns st2 = (
      \<lambda>x . if x = a
           then {ln} \<union> processed_lrns st x
           else processed_lrns st x)
    \<and> (if (WellFormed st new2a)
       then (
            Send new2a st st2
          \<and> Store_acc a new2a st st2
          \<and> (recent_msgs_acc st2 = (
              \<lambda>x . if x = a
                 then [new2a]
                 else recent_msgs_acc st x))
          \<and> (recent_msgs_lrn st2 = recent_msgs_lrn st)
          )
       else (
            (msgs st2 = msgs st)
          \<and> (known_msgs_acc st2 = known_msgs_acc st)
          \<and> (known_msgs_lrn st2 = known_msgs_lrn st)
          \<and> (recent_msgs_acc st2 = recent_msgs_acc st)
          \<and> (recent_msgs_lrn st2 = recent_msgs_lrn st)
          )
       )

    \<and> (queued_msg st2 = queued_msg st)
    \<and> (two_a_lrn_loop st2 = two_a_lrn_loop st)
    \<and> (decision st2 = decision st)
    \<and> (BVal st2 = BVal st)
  )"

(*Process1bLearnerLoopStep as a function*)
fun Process1bLearnerLoopStepFun :: "Acceptor \<Rightarrow> Learner \<Rightarrow> State \<Rightarrow> State" where
  "Process1bLearnerLoopStepFun a ln st = (
    let stp = st\<lparr>processed_lrns := (
                  \<lambda>x . if x = a
                       then {ln} \<union> processed_lrns st x
                       else processed_lrns st x)\<rparr>;
        new2a = M2a ln a (recent_msgs_acc st a) in
    if \<not> (WellFormed st new2a)
    then stp
    else 
      stp\<lparr>msgs := new2a # msgs st,
          known_msgs_acc := (
              \<lambda>x. if a = x 
                  then new2a # known_msgs_acc st x
                  else known_msgs_acc st x),
          recent_msgs_acc := (
              \<lambda>x . if x = a
                 then [new2a]
                 else recent_msgs_acc st x)\<rparr>
  )"

fun Process1bLearnerLoopDone :: "Acceptor \<Rightarrow> State \<Rightarrow> State \<Rightarrow> bool" where
  "Process1bLearnerLoopDone a st st2 = (
    (\<forall>ln :: Learner. ln \<in> processed_lrns st a)
    \<and> st2 = st\<lparr>two_a_lrn_loop := 
                \<lambda>x. if x = a
                    then False
                    else two_a_lrn_loop st x
        \<rparr>)"

fun Process1bLearnerLoop :: "Acceptor \<Rightarrow> State \<Rightarrow> State \<Rightarrow> bool" where
  "Process1bLearnerLoop a st st2 = (
    (\<exists>ln :: Learner. ln \<notin> processed_lrns st a \<and> Process1bLearnerLoopStep a ln st st2)
    \<or> Process1bLearnerLoopDone a st st2
  )"

fun AcceptorProcessAction :: "State \<Rightarrow> State \<Rightarrow> bool" where
  "AcceptorProcessAction st st2 = (
    \<exists>a :: Acceptor. is_safe a \<and> (
      (\<not> two_a_lrn_loop st a \<and>
       ((queued_msg st a \<noteq> None \<and> 
         Process1b a (the (queued_msg st a)) st st2) \<or> 
        (queued_msg st a = None \<and> (
          \<exists>m :: PreMessage. Process1a a m st st2 \<or> Process1b a m st st2
        ))))
      \<or> (two_a_lrn_loop st a \<and> 
         Process1bLearnerLoop a st st2)
  ))"

fun FakeSend1b :: "Acceptor \<Rightarrow> State \<Rightarrow> State \<Rightarrow> bool" where
  "FakeSend1b a st st2 = (
    \<exists>fin :: PreMessage list.
    let new1b = M1b a fin in
    WellFormed st new1b \<and>
    st2 = st\<lparr>msgs := new1b # msgs st\<rparr>
  )"

fun FakeSend2a :: "Acceptor \<Rightarrow> State \<Rightarrow> State \<Rightarrow> bool" where
  "FakeSend2a a st st2 = (
    \<exists>fin :: PreMessage list. \<exists>ln :: Learner.
    let new2a = M2a ln a fin in
    WellFormed st new2a \<and>
    st2 = st\<lparr>msgs := new2a # msgs st\<rparr>
  )"

fun LearnerRecv :: "Learner \<Rightarrow> PreMessage \<Rightarrow> State \<Rightarrow> State \<Rightarrow> bool" where
  "LearnerRecv l m st st2 = (
    Recv_lrn st l m \<and>
    st2 = st\<lparr> known_msgs_lrn := (
                \<lambda>x. if l = x 
                    then m # known_msgs_lrn st x
                    else known_msgs_lrn st x
    )\<rparr>
  )"

fun ChosenIn :: "State \<Rightarrow> Learner \<Rightarrow> Ballot \<Rightarrow> Value \<Rightarrow> bool" where
  "ChosenIn st l b v = (
      \<exists>S \<subseteq> Known2a st l b v. TrustLive l (acc ` S)
  )"

fun LearnerDecide :: "Learner \<Rightarrow> Ballot \<Rightarrow> Value \<Rightarrow> State \<Rightarrow> State \<Rightarrow> bool" where
  "LearnerDecide l b v st st2 = (
    ChosenIn st l b v \<and>
    st2 = st\<lparr>decision := \<lambda>x y.
              if x = l \<and> y = b
              then {v} \<union> decision st x y
              else decision st x y \<rparr>
  )"

fun LearnerAction :: "State \<Rightarrow> State \<Rightarrow> bool" where
  "LearnerAction st st2 = (
    \<exists>ln :: Learner.
      (\<exists>m :: PreMessage. LearnerRecv ln m st st2) \<or>
      (\<exists>bal :: Ballot. \<exists>val :: Value. LearnerDecide ln bal val st st2)
  )"

fun FakeAcceptorAction :: "State \<Rightarrow> State \<Rightarrow> bool" where
  "FakeAcceptorAction st st2 = (
    \<exists>a :: Acceptor. \<not> is_safe a \<and> (
      FakeSend1b a st st2 \<or>
      FakeSend2a a st st2
  ))"

fun Next :: "State \<Rightarrow> State \<Rightarrow> bool" where
  "Next st st2 = (
       ProposerSendAction st st2
     \<or> AcceptorProcessAction st st2
     \<or> LearnerAction st st2
     \<or> FakeAcceptorAction st st2
  )"

fun Spec :: "(nat \<Rightarrow> State) \<Rightarrow> bool" where
  "Spec f = (
    (\<exists>b :: Ballot \<Rightarrow> Value. f 0 = Init b) \<and>
    (\<forall>n :: nat. f n = f (Suc n) \<or> Next (f n) (f (Suc n)))
  )"

consts history :: "nat \<Rightarrow> State"

axiomatization where
  hist_spec: "Spec history"

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
    \<forall>m \<in> set (msgs st). isValidMessage m
  )"
(*
    msgs st \<in> SUBSET Message
    \<and> known_msgs \<in> [Acceptor \<union> Learner -> SUBSET Message]
    \<and> recent_msgs \<in> [Acceptor \<union> Learner -> SUBSET Message]
    \<and> queued_msg \<in> [Acceptor -> Message \<union> {NoMessage}]
    \<and> 2a_lrn_loop \<in> [Acceptor -> BOOLEAN]
    \<and> processed_lrns \<in> [Acceptor -> SUBSET Learner]
    \<and> decision \<in> [Learner \<times> Ballot -> SUBSET Value]
    \<and> BVal \<in> [Ballot -> Value]
*)

fun RecentMsgs_accSpec :: "State \<Rightarrow> bool" where
  "RecentMsgs_accSpec st = (
    \<forall>a :: Acceptor. is_safe a \<longrightarrow> 
      set (recent_msgs_acc st a) \<subseteq> set (known_msgs_acc st a)
  )"

fun RecentMsgs_lrnSpec :: "State \<Rightarrow> bool" where
  "RecentMsgs_lrnSpec st = (
    \<forall>l :: Learner.
      set (recent_msgs_lrn st l) \<subseteq> set (known_msgs_lrn st l)
  )"

fun KnownMsgs_accSpec :: "State \<Rightarrow> bool" where
  "KnownMsgs_accSpec st = (
     \<forall>a :: Acceptor. is_safe a \<longrightarrow> 
      (\<forall>m \<in> set (known_msgs_acc st a). 
        m \<in> set (msgs st) \<and>
        Proper_acc st a m \<and>
        WellFormed st m \<and>
        Tran m \<subseteq> set (known_msgs_acc st a) \<and>
        (\<exists>b :: Ballot. B m b)
  ))"

fun KnownMsgs_lrnSpec :: "State \<Rightarrow> bool" where
  "KnownMsgs_lrnSpec st = (
     \<forall>l :: Learner. 
      (\<forall>m \<in> set (known_msgs_lrn st l). 
        m \<in> set (msgs st) \<and>
        Proper_lrn st l m \<and>
        WellFormed st m \<and>
        Tran m \<subseteq> set (known_msgs_lrn st l) \<and>
        (\<exists>b :: Ballot. B m b)
  ))"

fun QueuedMsgSpec1 :: "State \<Rightarrow> bool" where
  "QueuedMsgSpec1 st = (
    \<forall>a :: Acceptor. is_safe a \<and> queued_msg st a \<noteq> None \<longrightarrow> (
      type (the (queued_msg st a)) = T1b \<and>
      isValidMessage (the (queued_msg st a)) \<and>
      (recent_msgs_acc st a = [])
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
          \<exists> m0 \<in> set (recent_msgs_acc st a). \<forall>m1 \<in> SentBy st a. m1 \<in> Tran m0)) \<and>
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

(*
DecisionSpec ==
    \A L \in Learner : \A BB \in Ballot : \A VV \in Value :
        VV \in decision[L, BB] => ChosenIn(L, BB, VV)
*)


fun FullSafetyInvariant :: "State \<Rightarrow> bool" where
  "FullSafetyInvariant st = (
    TypeOK st
    \<and> RecentMsgs_accSpec st
    \<and> RecentMsgs_lrnSpec st
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
  assumes "Next st st2"
  shows "TypeOK st2"
unfolding TypeOK.simps Next.simps
proof
  fix x
  assume "x \<in> set (msgs st2)"
  have "Next st st2"
   using assms(2) by blast
  then show "isValidMessage x"
    unfolding Next.simps
  proof (elim disjE)
    assume "ProposerSendAction st st2"
    show "isValidMessage x"
      using \<open>ProposerSendAction st st2\<close> \<open>x \<in> set (msgs st2)\<close> assms(1) by auto
  next
    assume "AcceptorProcessAction st st2"
    then show "isValidMessage x"
      unfolding AcceptorProcessAction.simps
      proof (elim exE)
        fix a
        assume "is_safe a \<and>
                  (\<not> two_a_lrn_loop st a \<and>
                   (queued_msg st a \<noteq> None \<and>
                    Process1b a (the (queued_msg st a)) st st2 \<or>
                    queued_msg st a = None \<and>
                    (\<exists>m. Process1a a m st st2 \<or> Process1b a m st st2)) \<or>
                   two_a_lrn_loop st a \<and> Process1bLearnerLoop a st st2)"
        show ?thesis
        proof (cases "two_a_lrn_loop st a")
            case True
            have "Process1bLearnerLoop a st st2" 
              using True \<open>is_safe a \<and> (\<not> two_a_lrn_loop st a \<and> (queued_msg st a \<noteq> None \<and> Process1b a (the (queued_msg st a)) st st2 \<or> queued_msg st a = None \<and> (\<exists>m. Process1a a m st st2 \<or> Process1b a m st st2)) \<or> two_a_lrn_loop st a \<and> Process1bLearnerLoop a st st2)\<close> by blast
            then show ?thesis
            unfolding Process1bLearnerLoop.simps
            proof (elim disjE)
              assume "\<exists>ln. ln \<notin> processed_lrns st a \<and>
                        Process1bLearnerLoopStep a ln st st2"
              then show ?thesis
                by (smt (verit, best) Process1bLearnerLoopStep.elims(2) Send.elims(2) TypeOK.elims(1) WellFormed.elims(2) \<open>x \<in> set (msgs st2)\<close> assms(1) set_ConsD)
            next
              assume "Process1bLearnerLoopDone a st st2"
              then show ?thesis
                using \<open>x \<in> set (msgs st2)\<close> assms(1) by force
            qed
          next
            case False
            have "(queued_msg st a \<noteq> None \<and>
                      Process1b a (the (queued_msg st a)) st st2 \<or>
                      queued_msg st a = None \<and>
                      (\<exists>m. Process1a a m st st2 \<or> Process1b a m st st2))"
              using False \<open>is_safe a \<and> (\<not> two_a_lrn_loop st a \<and> (queued_msg st a \<noteq> None \<and> Process1b a (the (queued_msg st a)) st st2 \<or> queued_msg st a = None \<and> (\<exists>m. Process1a a m st st2 \<or> Process1b a m st st2)) \<or> two_a_lrn_loop st a \<and> Process1bLearnerLoop a st st2)\<close> by presburger
            then show ?thesis
              proof (elim disjE)
                assume "queued_msg st a \<noteq> None \<and>
                        Process1b a (the (queued_msg st a))
                         st st2"
                then show ?thesis
                  by (metis Process1b.elims(2) TypeOK.elims(1) \<open>x \<in> set (msgs st2)\<close> assms(1))
              next
                assume "queued_msg st a = None \<and>
                        (\<exists>m. Process1a a m st st2 \<or>
                             Process1b a m st st2)"
                then show ?thesis
                proof
                  have "\<exists>m. Process1a a m st st2 \<or> Process1b a m st st2"
                    using False \<open>is_safe a \<and> (\<not> two_a_lrn_loop st a \<and> (queued_msg st a \<noteq> None \<and> Process1b a (the (queued_msg st a)) st st2 \<or> queued_msg st a = None \<and> (\<exists>m. Process1a a m st st2 \<or> Process1b a m st st2)) \<or> two_a_lrn_loop st a \<and> Process1bLearnerLoop a st st2)\<close> by blast
                  then show ?thesis
                  proof (elim exE)
                    fix m
                    assume "Process1a a m st st2 \<or> Process1b a m st st2"
                    then show ?thesis
                    proof (elim disjE)
                      assume "Process1a a m st st2"
                      then show ?thesis
                        by (smt (z3) Process1a.elims(2) Send.elims(2) TypeOK.elims(1) WellFormed.elims(1) \<open>x \<in> set (msgs st2)\<close> assms(1) set_ConsD)
                    next
                      assume "Process1b a m st st2"
                      then show ?thesis
                        by (metis Process1b.elims(2) TypeOK.elims(2) \<open>x \<in> set (msgs st2)\<close> assms(1))
                    qed
                  qed
                qed
              qed
          qed
      qed
  next
    assume "LearnerAction st st2"
    show "isValidMessage x"
      by (metis (no_types, lifting) LearnerAction.simps LearnerDecide.simps LearnerRecv.elims(2) TypeOK.elims(1) \<open>LearnerAction st st2\<close> \<open>x \<in> set (msgs st2)\<close> assms(1) simps(1) surjective update_convs(3) update_convs(9))
  next
    assume "FakeAcceptorAction st st2"
    then show "isValidMessage x"
      unfolding FakeAcceptorAction.simps
      by (smt (z3) FakeSend1b.elims(2) FakeSend2a.simps TypeOK.elims(1) WellFormed.elims(1) \<open>x \<in> set (msgs st2)\<close> assms(1) set_ConsD simps(1) simps(12) surjective)
  qed
qed

lemma RecentMsgsaccSpecInvariant :
  assumes "RecentMsgs_accSpec st"
  assumes "Next st st2"
  shows "RecentMsgs_accSpec st2"
unfolding RecentMsgs_accSpec.simps
proof 
  fix a2
  show "is_safe a2 \<longrightarrow> set (recent_msgs_acc st2 a2) \<subseteq> set (known_msgs_acc st2 a2)"
  proof (rule impI)
  assume "is_safe a2"
  have "Next st st2"
    using assms(2) by blast
  then show "set (recent_msgs_acc st2 a2) \<subseteq> set (known_msgs_acc st2 a2)"
    unfolding Next.simps
  proof (elim disjE)
    assume "ProposerSendAction st st2"
    show ?thesis
      using \<open>ProposerSendAction st st2\<close> \<open>is_safe a2\<close> assms(1) by fastforce
  next
    assume "AcceptorProcessAction st st2"
    then show ?thesis
      unfolding AcceptorProcessAction.simps
      proof (elim exE)
        fix a
        assume "is_safe a \<and>
                  (\<not> two_a_lrn_loop st a \<and>
                   (queued_msg st a \<noteq> None \<and>
                    Process1b a (the (queued_msg st a)) st st2 \<or>
                    queued_msg st a = None \<and>
                    (\<exists>m. Process1a a m st st2 \<or> Process1b a m st st2)) \<or>
                   two_a_lrn_loop st a \<and> Process1bLearnerLoop a st st2)"
        show ?thesis
        proof (cases "two_a_lrn_loop st a")
            case True
            have "Process1bLearnerLoop a st st2" 
              using True \<open>is_safe a \<and> (\<not> two_a_lrn_loop st a \<and> (queued_msg st a \<noteq> None \<and> Process1b a (the (queued_msg st a)) st st2 \<or> queued_msg st a = None \<and> (\<exists>m. Process1a a m st st2 \<or> Process1b a m st st2)) \<or> two_a_lrn_loop st a \<and> Process1bLearnerLoop a st st2)\<close> by blast
            then show ?thesis
            unfolding Process1bLearnerLoop.simps
            proof (elim disjE)
              assume "\<exists>ln. ln \<notin> processed_lrns st a \<and>
                        Process1bLearnerLoopStep a ln st st2"
              then show ?thesis
                by (smt (verit, best) Process1bLearnerLoopStep.elims(2) RecentMsgs_accSpec.elims(1) Store_acc.elims(2) \<open>is_safe a2\<close> assms(1) empty_iff empty_set list.set_intros(1) set_ConsD subsetI)
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
              using False \<open>is_safe a \<and> (\<not> two_a_lrn_loop st a \<and> (queued_msg st a \<noteq> None \<and> Process1b a (the (queued_msg st a)) st st2 \<or> queued_msg st a = None \<and> (\<exists>m. Process1a a m st st2 \<or> Process1b a m st st2)) \<or> two_a_lrn_loop st a \<and> Process1bLearnerLoop a st st2)\<close> by presburger
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
                    using False \<open>is_safe a \<and> (\<not> two_a_lrn_loop st a \<and> (queued_msg st a \<noteq> None \<and> Process1b a (the (queued_msg st a)) st st2 \<or> queued_msg st a = None \<and> (\<exists>m. Process1a a m st st2 \<or> Process1b a m st st2)) \<or> two_a_lrn_loop st a \<and> Process1bLearnerLoop a st st2)\<close> by blast
                  then show ?thesis
                  proof (elim exE)
                    fix m
                    assume "Process1a a m st st2 \<or> Process1b a m st st2"
                    then show ?thesis
                    proof (elim disjE)
                      assume "Process1a a m st st2"
                      then show ?thesis
                        by (smt (verit, best) Process1a.elims(2) RecentMsgs_accSpec.elims(1) Store_acc.elims(2) \<open>is_safe a2\<close> assms(1) empty_iff insert_iff list.set(1) list.simps(15) subsetD subsetI)
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
    assume "LearnerAction st st2"
    then show ?thesis
      unfolding LearnerAction.simps
    proof (elim exE)
      fix ln
      assume "(\<exists>m. LearnerRecv ln m st st2) \<or>
              (\<exists>bal val. LearnerDecide ln bal val st st2)"
      then show ?thesis
      proof (elim disjE)
        assume "\<exists>m. LearnerRecv ln m st st2"
        then show ?thesis
          by (metis (no_types, lifting) LearnerRecv.elims(2) RecentMsgs_accSpec.elims(1) \<open>is_safe a2\<close> assms(1) ext_inject surjective update_convs(3))
      next
        assume "\<exists>bal val. LearnerDecide ln bal val st st2"
        then show ?thesis
          by (metis (no_types, lifting) LearnerDecide.elims(2) RecentMsgs_accSpec.elims(1) \<open>is_safe a2\<close> assms(1) ext_inject surjective update_convs(9))
      qed
    qed
  next
    assume "FakeAcceptorAction st st2"
    then show ?thesis
      unfolding FakeAcceptorAction.simps
      by (metis FakeSend1b.elims(2) FakeSend2a.simps RecentMsgs_accSpec.elims(1) \<open>is_safe a2\<close> assms(1) simps(12) simps(2) simps(4) surjective)
  qed
qed
qed

lemma RecentMsgslrnSpecInvariant :
  assumes "RecentMsgs_lrnSpec st"
  assumes "Next st st2"
  shows "RecentMsgs_lrnSpec st2"
  unfolding RecentMsgs_lrnSpec.simps
proof 
  fix l
  have "Next st st2"
    using assms(2) by blast
  then show "set (recent_msgs_lrn st2 l) \<subseteq> set (known_msgs_lrn st2 l)"
    unfolding Next.simps
  proof (elim disjE)
    assume "ProposerSendAction st st2"
    show ?thesis
      using \<open>ProposerSendAction st st2\<close> assms(1) by force
  next
    assume "AcceptorProcessAction st st2"
    then show ?thesis
      unfolding AcceptorProcessAction.simps
      proof (elim exE)
        fix a
        assume "is_safe a \<and>
                  (\<not> two_a_lrn_loop st a \<and>
                   (queued_msg st a \<noteq> None \<and>
                    Process1b a (the (queued_msg st a)) st st2 \<or>
                    queued_msg st a = None \<and>
                    (\<exists>m. Process1a a m st st2 \<or> Process1b a m st st2)) \<or>
                   two_a_lrn_loop st a \<and> Process1bLearnerLoop a st st2)"
        show ?thesis
        proof (cases "two_a_lrn_loop st a")
            case True
            have "Process1bLearnerLoop a st st2" 
              using True \<open>is_safe a \<and> (\<not> two_a_lrn_loop st a \<and> (queued_msg st a \<noteq> None \<and> Process1b a (the (queued_msg st a)) st st2 \<or> queued_msg st a = None \<and> (\<exists>m. Process1a a m st st2 \<or> Process1b a m st st2)) \<or> two_a_lrn_loop st a \<and> Process1bLearnerLoop a st st2)\<close> by blast
            then show ?thesis
            by (smt (verit, del_insts) Process1bLearnerLoop.simps Process1bLearnerLoopDone.elims(1) Process1bLearnerLoopStep.elims(2) RecentMsgs_lrnSpec.elims(1) Store_acc.elims(2) assms(1) ext_inject surjective update_convs(7))
          next
            case False
            have "(queued_msg st a \<noteq> None \<and>
                      Process1b a (the (queued_msg st a)) st st2 \<or>
                      queued_msg st a = None \<and>
                      (\<exists>m. Process1a a m st st2 \<or> Process1b a m st st2))"
              using False \<open>is_safe a \<and> (\<not> two_a_lrn_loop st a \<and> (queued_msg st a \<noteq> None \<and> Process1b a (the (queued_msg st a)) st st2 \<or> queued_msg st a = None \<and> (\<exists>m. Process1a a m st st2 \<or> Process1b a m st st2)) \<or> two_a_lrn_loop st a \<and> Process1bLearnerLoop a st st2)\<close> by presburger
            then show ?thesis
              proof (elim disjE)
                assume "queued_msg st a \<noteq> None \<and>
                        Process1b a (the (queued_msg st a))
                         st st2"
                then show ?thesis
                  using assms(1) by auto
              next
                assume "queued_msg st a = None \<and>
                        (\<exists>m. Process1a a m st st2 \<or>
                             Process1b a m st st2)"
                then show ?thesis
                proof
                  have "\<exists>m. Process1a a m st st2 \<or> Process1b a m st st2"
                    using False \<open>is_safe a \<and> (\<not> two_a_lrn_loop st a \<and> (queued_msg st a \<noteq> None \<and> Process1b a (the (queued_msg st a)) st st2 \<or> queued_msg st a = None \<and> (\<exists>m. Process1a a m st st2 \<or> Process1b a m st st2)) \<or> two_a_lrn_loop st a \<and> Process1bLearnerLoop a st st2)\<close> by blast
                  then show ?thesis
                  proof (elim exE)
                    fix m
                    assume "Process1a a m st st2 \<or> Process1b a m st st2"
                    then show ?thesis
                    proof (elim disjE)
                      assume "Process1a a m st st2"
                      then show ?thesis
                        by (metis Process1a.elims(2) RecentMsgs_lrnSpec.elims(2) Store_acc.elims(2) assms(1))
                    next
                      assume "Process1b a m st st2"
                      then show ?thesis
                        by (metis Process1b.elims(2) RecentMsgs_lrnSpec.elims(2) Store_acc.elims(1) assms(1))
                    qed
                  qed
                qed
              qed
          qed
      qed
  next
    assume "LearnerAction st st2"
    then show ?thesis
      unfolding LearnerAction.simps
    proof (elim exE)
      fix ln
      assume "(\<exists>m. LearnerRecv ln m st st2) \<or>
              (\<exists>bal val. LearnerDecide ln bal val st st2)"
      then show ?thesis
      proof (elim disjE)
        assume "\<exists>m. LearnerRecv ln m st st2"
        then show ?thesis
          by (smt (verit, best) LearnerRecv.elims(2) RecentMsgs_lrnSpec.elims(2) assms(1) ext_inject list.set_intros(2) subsetD subsetI surjective update_convs(3))
      next
        assume "\<exists>bal val. LearnerDecide ln bal val st st2"
        then show ?thesis
          by (metis (no_types, lifting) LearnerDecide.elims(2) RecentMsgs_lrnSpec.elims(2) assms(1) simps(3) simps(5) surjective update_convs(9))
      qed
    qed
  next
    assume "FakeAcceptorAction st st2"
    then show ?thesis
      unfolding FakeAcceptorAction.simps
      by (metis FakeSend1b.elims(1) FakeSend2a.simps RecentMsgs_lrnSpec.elims(2) assms(1) ext_inject simps(12) surjective)
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
         isValidMessage (the (queued_msg st2 a2)) \<and>
         recent_msgs_acc st2 a2 = []"
  proof (rule impI)
  assume "is_safe a2 \<and>queued_msg st2 a2 \<noteq> None"
  have "Next st st2"
    using assms(3) by blast
  then show "type (the (queued_msg st2 a2)) = T1b \<and>
             isValidMessage (the (queued_msg st2 a2)) \<and>
             recent_msgs_acc st2 a2 = []"
    unfolding Next.simps
  proof (elim disjE)
    assume "ProposerSendAction st st2"
    show ?thesis
      using \<open>ProposerSendAction st st2\<close> \<open>is_safe a2 \<and> queued_msg st2 a2 \<noteq> None\<close> assms(2) by force
  next
    assume "AcceptorProcessAction st st2"
    then show ?thesis
      unfolding AcceptorProcessAction.simps
      proof (elim exE)
        fix a
        assume "is_safe a \<and>
                  (\<not> two_a_lrn_loop st a \<and>
                   (queued_msg st a \<noteq> None \<and>
                    Process1b a (the (queued_msg st a)) st st2 \<or>
                    queued_msg st a = None \<and>
                    (\<exists>m. Process1a a m st st2 \<or> Process1b a m st st2)) \<or>
                   two_a_lrn_loop st a \<and> Process1bLearnerLoop a st st2)"
        show ?thesis
        proof (cases "two_a_lrn_loop st a")
            case True
            have "Process1bLearnerLoop a st st2" 
              using True \<open>is_safe a \<and> (\<not> two_a_lrn_loop st a \<and> (queued_msg st a \<noteq> None \<and> Process1b a (the (queued_msg st a)) st st2 \<or> queued_msg st a = None \<and> (\<exists>m. Process1a a m st st2 \<or> Process1b a m st st2)) \<or> two_a_lrn_loop st a \<and> Process1bLearnerLoop a st st2)\<close> by blast
            then show ?thesis
            unfolding Process1bLearnerLoop.simps
            proof (elim disjE)
              assume "\<exists>ln. ln \<notin> processed_lrns st a \<and>
                        Process1bLearnerLoopStep a ln st st2"
              then show ?thesis
                by (metis (no_types, lifting) Process1bLearnerLoopStep.elims(2) QueuedMsgSpec1.elims(1) True \<open>is_safe a2 \<and> queued_msg st2 a2 \<noteq> None\<close> assms(1) assms(2) twoaLearnerLoopSpec.elims(1))
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
              using False \<open>is_safe a \<and> (\<not> two_a_lrn_loop st a \<and> (queued_msg st a \<noteq> None \<and> Process1b a (the (queued_msg st a)) st st2 \<or> queued_msg st a = None \<and> (\<exists>m. Process1a a m st st2 \<or> Process1b a m st st2)) \<or> two_a_lrn_loop st a \<and> Process1bLearnerLoop a st st2)\<close> by presburger
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
                    using False \<open>is_safe a \<and> (\<not> two_a_lrn_loop st a \<and> (queued_msg st a \<noteq> None \<and> Process1b a (the (queued_msg st a)) st st2 \<or> queued_msg st a = None \<and> (\<exists>m. Process1a a m st st2 \<or> Process1b a m st st2)) \<or> two_a_lrn_loop st a \<and> Process1bLearnerLoop a st st2)\<close> by blast
                  then show ?thesis
                  proof (elim exE)
                    fix m
                    assume "Process1a a m st st2 \<or> Process1b a m st st2"
                    then show ?thesis
                    proof (elim disjE)
                      assume "Process1a a m st st2"
                      then show ?thesis
                        by (smt (z3) Process1a.simps QueuedMsgSpec1.elims(1) WellFormed.elims(2) \<open>is_safe a2 \<and> queued_msg st2 a2 \<noteq> None\<close> \<open>queued_msg st a = None \<and> (\<exists>m. Process1a a m st st2 \<or> Process1b a m st st2)\<close> assms(2) option.collapse option.inject type.simps(2))
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
    assume "LearnerAction st st2"
    then show ?thesis
      unfolding LearnerAction.simps
    proof (elim exE)
      fix ln
      assume "(\<exists>m. LearnerRecv ln m st st2) \<or>
              (\<exists>bal val. LearnerDecide ln bal val st st2)"
      then show ?thesis
      proof (elim disjE)
        assume "\<exists>m. LearnerRecv ln m st st2"
        then show ?thesis
          by (smt (z3) LearnerRecv.elims(2) QueuedMsgSpec1.elims(1) \<open>is_safe a2 \<and> queued_msg st2 a2 \<noteq> None\<close> assms(2) simps(4) simps(6) surjective update_convs(3))
      next
        assume "\<exists>bal val. LearnerDecide ln bal val st st2"
        then show ?thesis
          by (smt (verit, ccfv_SIG) LearnerDecide.elims(2) QueuedMsgSpec1.elims(1) \<open>is_safe a2 \<and> queued_msg st2 a2 \<noteq> None\<close> assms(2) ext_inject surjective update_convs(9))
      qed
    qed
  next
    assume "FakeAcceptorAction st st2"
    then show ?thesis
      unfolding FakeAcceptorAction.simps
      by (metis FakeSend1b.elims(2) FakeSend2a.simps QueuedMsgSpec1.elims(1) \<open>is_safe a2 \<and> queued_msg st2 a2 \<noteq> None\<close> assms(2) ext_inject simps(12) surjective)
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
      unfolding AcceptorProcessAction.simps
      proof (elim exE)
        fix a
        assume "is_safe a \<and>
                  (\<not> two_a_lrn_loop st a \<and>
                   (queued_msg st a \<noteq> None \<and>
                    Process1b a (the (queued_msg st a)) st st2 \<or>
                    queued_msg st a = None \<and>
                    (\<exists>m. Process1a a m st st2 \<or> Process1b a m st st2)) \<or>
                   two_a_lrn_loop st a \<and> Process1bLearnerLoop a st st2)"
        show ?thesis
        proof (cases "two_a_lrn_loop st a")
          case True
          have "Process1bLearnerLoop a st st2" 
            using True \<open>is_safe a \<and> (\<not> two_a_lrn_loop st a \<and> (queued_msg st a \<noteq> None \<and> Process1b a (the (queued_msg st a)) st st2 \<or> queued_msg st a = None \<and> (\<exists>m. Process1a a m st st2 \<or> Process1b a m st st2)) \<or> two_a_lrn_loop st a \<and> Process1bLearnerLoop a st st2)\<close> by blast
          then show ?thesis
            by (smt (verit, best) Process1bLearnerLoop.simps Process1bLearnerLoopDone.elims(1) Process1bLearnerLoopStep.elims(2) \<open>is_safe a2 \<and> two_a_lrn_loop st2 a2\<close> assms(1) ext_inject surjective twoaLearnerLoopSpec.elims(1) update_convs(7))
        next
          case False
          have "(queued_msg st a \<noteq> None \<and>
                    Process1b a (the (queued_msg st a)) st st2 \<or>
                    queued_msg st a = None \<and>
                    (\<exists>m. Process1a a m st st2 \<or> Process1b a m st st2))"
            using False \<open>is_safe a \<and> (\<not> two_a_lrn_loop st a \<and> (queued_msg st a \<noteq> None \<and> Process1b a (the (queued_msg st a)) st st2 \<or> queued_msg st a = None \<and> (\<exists>m. Process1a a m st st2 \<or> Process1b a m st st2)) \<or> two_a_lrn_loop st a \<and> Process1bLearnerLoop a st st2)\<close> by presburger
          then show ?thesis
            by (smt (z3) False Process1a.elims(2) Process1b.simps \<open>is_safe a2 \<and> two_a_lrn_loop st2 a2\<close> assms(1) twoaLearnerLoopSpec.elims(1))
          qed
        qed
  next
    assume "LearnerAction st st2"
    then show ?thesis
      unfolding LearnerAction.simps
    proof (elim exE)
      fix ln
      assume "(\<exists>m. LearnerRecv ln m st st2) \<or>
              (\<exists>bal val. LearnerDecide ln bal val st st2)"
      then show ?thesis
      using \<open>is_safe a2 \<and> two_a_lrn_loop st2 a2\<close> assms(1) by auto
    qed
  next
    assume "FakeAcceptorAction st st2"
    then show ?thesis
      unfolding FakeAcceptorAction.simps
      by (metis FakeSend1b.simps FakeSend2a.simps \<open>is_safe a2 \<and> two_a_lrn_loop st2 a2\<close> assms(1) ext_inject simps(12) surjective twoaLearnerLoopSpec.elims(2))
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
      by (smt (verit, ccfv_SIG) ChosenIn.elims(1) Collect_cong Known2a.simps ProposerSendAction.elims(1) Send1a.elims(2) V.simps \<open>ProposerSendAction st st2\<close> \<open>v \<in> decision st l b \<Longrightarrow> ChosenIn st l b v\<close> \<open>v \<in> decision st2 l b\<close> select_convs(10) select_convs(3) surjective update_convs(1))
  next
    assume "AcceptorProcessAction st st2"
    then show ?thesis
      unfolding AcceptorProcessAction.simps
      proof (elim exE)
        fix a
        assume "is_safe a \<and>
                  (\<not> two_a_lrn_loop st a \<and>
                   (queued_msg st a \<noteq> None \<and>
                    Process1b a (the (queued_msg st a)) st st2 \<or>
                    queued_msg st a = None \<and>
                    (\<exists>m. Process1a a m st st2 \<or> Process1b a m st st2)) \<or>
                   two_a_lrn_loop st a \<and> Process1bLearnerLoop a st st2)"
        show ?thesis
        proof (cases "two_a_lrn_loop st a")
            case True
            have "Process1bLearnerLoop a st st2" 
              using True \<open>is_safe a \<and> (\<not> two_a_lrn_loop st a \<and> (queued_msg st a \<noteq> None \<and> Process1b a (the (queued_msg st a)) st st2 \<or> queued_msg st a = None \<and> (\<exists>m. Process1a a m st st2 \<or> Process1b a m st st2)) \<or> two_a_lrn_loop st a \<and> Process1bLearnerLoop a st st2)\<close> by blast
            then show ?thesis
              by (smt (verit, best) ChosenIn.elims(1) Collect_cong Known2a.simps Process1bLearnerLoop.simps Process1bLearnerLoopDone.elims(1) Process1bLearnerLoopStep.elims(2) Store_acc.elims(2) V.simps \<open>v \<in> decision st l b \<Longrightarrow> ChosenIn st l b v\<close> \<open>v \<in> decision st2 l b\<close> ext_inject surjective update_convs(7))
          next
            case False
            have "(queued_msg st a \<noteq> None \<and>
                      Process1b a (the (queued_msg st a)) st st2 \<or>
                      queued_msg st a = None \<and>
                      (\<exists>m. Process1a a m st st2 \<or> Process1b a m st st2))"
              using False \<open>is_safe a \<and> (\<not> two_a_lrn_loop st a \<and> (queued_msg st a \<noteq> None \<and> Process1b a (the (queued_msg st a)) st st2 \<or> queued_msg st a = None \<and> (\<exists>m. Process1a a m st st2 \<or> Process1b a m st st2)) \<or> two_a_lrn_loop st a \<and> Process1bLearnerLoop a st st2)\<close> by presburger
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
    assume "LearnerAction st st2"
    then show ?thesis
      by (smt (z3) ChosenIn.simps Known2a.simps LearnerAction.simps LearnerDecide.elims(2) LearnerRecv.elims(2) Un_iff V.simps \<open>v \<in> decision st l b \<Longrightarrow> ChosenIn st l b v\<close> \<open>v \<in> decision st2 l b\<close> empty_iff ext_inject insert_iff list.set_intros(2) mem_Collect_eq subsetD subsetI surjective update_convs(3) update_convs(9))
  next
    assume "FakeAcceptorAction st st2"
    then show ?thesis
      by (smt (z3) ChosenIn.elims(1) Collect_cong FakeAcceptorAction.elims(2) FakeSend1b.elims(2) FakeSend2a.simps Known2a.simps V.simps \<open>v \<in> decision st l b \<Longrightarrow> ChosenIn st l b v\<close> \<open>v \<in> decision st2 l b\<close> ext_inject surjective update_convs(1))
  qed
qed

lemma SafeAcceptorOwnMessagesRefsSpecInvariant :
  assumes "TypeOK st"
  assumes "twoaLearnerLoopSpec st"
  assumes "SafeAcceptorOwnMessagesRefsSpec st"
  assumes "Next st st2"
  shows "SafeAcceptorOwnMessagesRefsSpec st2"
  unfolding SafeAcceptorOwnMessagesRefsSpec.simps
proof (clarify)
  fix a2
  assume "is_safe a2"
         "SentBy st2 a2 \<noteq> {}"
  have "Next st st2"
    using assms(4) by blast
  then show "(queued_msg st2 a2 = None \<longrightarrow>
             (\<exists>m0\<in>set (recent_msgs_acc st2 a2).
              \<forall>m1\<in>SentBy st2 a2. m1 \<in> Tran m0)) \<and>
         (queued_msg st2 a2 \<noteq> None \<longrightarrow>
          (\<forall>m1\<in>SentBy st2 a2. m1 \<in> Tran (the (queued_msg st2 a2))))"
    unfolding Next.simps
  proof (elim disjE)
    assume "ProposerSendAction st st2"
    have "SentBy st a2 \<noteq> {}"
      using \<open>ProposerSendAction st st2\<close> \<open>SentBy st2 a2 \<noteq> {}\<close> by auto
    have hyp1: "queued_msg st a2 = None \<longrightarrow>
                 (\<exists>m0\<in>set (recent_msgs_acc st a2).
                  \<forall>m1\<in>SentBy st a2. m1 \<in> Tran m0)"
      using SafeAcceptorOwnMessagesRefsSpec.simps \<open>SentBy st a2 \<noteq> {}\<close> \<open>is_safe a2\<close> assms(3) by presburger
    have hyp2: "(queued_msg st a2 \<noteq> None \<longrightarrow>
          (\<forall>m1\<in>SentBy st a2. m1 \<in> Tran (the (queued_msg st a2))))"
      using SafeAcceptorOwnMessagesRefsSpec.simps \<open>SentBy st a2 \<noteq> {}\<close> \<open>is_safe a2\<close> assms(3) by presburger
    show ?thesis
    proof (intro conjI; clarify)
      assume "queued_msg st2 a2 = None"
      show "\<exists>m0\<in>set (recent_msgs_acc st2 a2).  \<forall>m1\<in>SentBy st2 a2. m1 \<in> Tran m0"
        using \<open>ProposerSendAction st st2\<close> \<open>SentBy st2 a2 \<noteq> {}\<close> \<open>is_safe a2\<close> \<open>queued_msg st2 a2 = None\<close> assms(3) by fastforce
    next
      fix m1 y
      assume "m1 \<in> SentBy st2 a2"
             "queued_msg st2 a2 = Some y"
      then show "m1 \<in> Tran (the (queued_msg st2 a2))"
        using \<open>ProposerSendAction st st2\<close> \<open>is_safe a2\<close> assms(3) mem_Collect_eq option.discI set_ConsD by fastforce
    qed
  next
    assume "AcceptorProcessAction st st2"
    then show ?thesis
    unfolding AcceptorProcessAction.simps
    proof (elim exE)
      fix a
      assume "is_safe a \<and>
                (\<not> two_a_lrn_loop st a \<and>
                 (queued_msg st a \<noteq> None \<and>
                  Process1b a (the (queued_msg st a)) st st2 \<or>
                  queued_msg st a = None \<and>
                  (\<exists>m. Process1a a m st st2 \<or> Process1b a m st st2)) \<or>
                 two_a_lrn_loop st a \<and> Process1bLearnerLoop a st st2)"
      show ?thesis
      proof (cases "two_a_lrn_loop st a")
          case True
          have "Process1bLearnerLoop a st st2" 
            using True \<open>is_safe a \<and> (\<not> two_a_lrn_loop st a \<and> (queued_msg st a \<noteq> None \<and> Process1b a (the (queued_msg st a)) st st2 \<or> queued_msg st a = None \<and> (\<exists>m. Process1a a m st st2 \<or> Process1b a m st st2)) \<or> two_a_lrn_loop st a \<and> Process1bLearnerLoop a st st2)\<close> by blast
          then show ?thesis
          unfolding Process1bLearnerLoop.simps
          proof (elim disjE)
            assume "\<exists>ln. ln \<notin> processed_lrns st a \<and>
                      Process1bLearnerLoopStep a ln st st2"          
            then show ?thesis
            proof (elim exE)
              fix ln
              assume "ln \<notin> processed_lrns st a \<and>
                      Process1bLearnerLoopStep a ln st st2"
              then show ?thesis
                unfolding Process1bLearnerLoopStep.simps
              proof (intro conjI; clarify)
                assume "queued_msg st2 a2 = None"
                have "queued_msg st2 = queued_msg st"
                  by (meson Process1bLearnerLoopStep.elims(2) \<open>ln \<notin> processed_lrns st a \<and> Process1bLearnerLoopStep a ln st st2\<close>)
                show "\<exists>m0\<in>set (recent_msgs_acc st2 a2).  \<forall>m1\<in>SentBy st2 a2. m1 \<in> Tran m0"
                proof (cases "WellFormed st (M2a ln a (recent_msgs_acc st a))")
                case True
                have "msgs st2 = (M2a ln a (recent_msgs_acc st a)) # msgs st"
                  by (meson Process1bLearnerLoopStep.elims(2) Send.elims(2) True \<open>ln \<notin> processed_lrns st a \<and> Process1bLearnerLoopStep a ln st st2\<close>)
                have "recent_msgs_acc st2 =
                        (\<lambda>x. if x = a then [M2a ln a (recent_msgs_acc st a)]
                              else recent_msgs_acc st x)"
                  by (metis Process1bLearnerLoopStep.elims(2) True \<open>ln \<notin> processed_lrns st a \<and> Process1bLearnerLoopStep a ln st st2\<close>)
                show ?thesis
                proof (cases "SentBy st a2 = {}")
                  case True
                  show ?thesis
                    sorry
                next
                  case False
                  have hyp: "(\<exists>m0\<in>set (recent_msgs_acc st a2). \<forall>m1\<in>SentBy st a2. m1 \<in> Tran m0)"
                    using False \<open>is_safe a2\<close> \<open>queued_msg st2 = queued_msg st\<close> \<open>queued_msg st2 a2 = None\<close> assms(3) by auto
                  show ?thesis
                    sorry
                qed
                next
                case False
                have "msgs st2 = msgs st"
                  by (meson False Process1bLearnerLoopStep.elims(2) \<open>ln \<notin> processed_lrns st a \<and> Process1bLearnerLoopStep a ln st st2\<close>)
                have "recent_msgs_acc st2 = recent_msgs_acc st"
                  by (meson False Process1bLearnerLoopStep.elims(2) \<open>ln \<notin> processed_lrns st a \<and> Process1bLearnerLoopStep a ln st st2\<close>)
                show ?thesis
                  using \<open>SentBy st2 a2 \<noteq> {}\<close> \<open>is_safe a2\<close> \<open>msgs st2 = msgs st\<close> \<open>queued_msg st2 = queued_msg st\<close> \<open>queued_msg st2 a2 = None\<close> \<open>recent_msgs_acc st2 = recent_msgs_acc st\<close> assms(3) by force
                qed
              next
                fix m1 y
                assume "m1 \<in> SentBy st2 a2"
                       "queued_msg st2 a2 = Some y"
                show "m1 \<in> Tran (the (queued_msg st2 a2))"
                  by (smt (verit) Process1bLearnerLoopStep.elims(2) SafeAcceptorOwnMessagesRefsSpec.elims(2) Send.elims(2) SentBy.elims True \<open>is_safe a2\<close> \<open>ln \<notin> processed_lrns st a \<and> Process1bLearnerLoopStep a ln st st2\<close> \<open>m1 \<in> SentBy st2 a2\<close> \<open>queued_msg st2 a2 = Some y\<close> assms(2) assms(3) empty_iff hpaxos.acc.simps(3) mem_Collect_eq option.discI set_ConsD twoaLearnerLoopSpec.elims(2))
              qed
           qed
          next
            assume "Process1bLearnerLoopDone a st st2"
            then show ?thesis
              unfolding Process1bLearnerLoopDone.simps
              sorry
          qed
        next
                case False
                have "(queued_msg st a \<noteq> None \<and>
                          Process1b a (the (queued_msg st a)) st st2 \<or>
                          queued_msg st a = None \<and>
                          (\<exists>m. Process1a a m st st2 \<or> Process1b a m st st2))"
                  using False \<open>is_safe a \<and> (\<not> two_a_lrn_loop st a \<and> (queued_msg st a \<noteq> None \<and> Process1b a (the (queued_msg st a)) st st2 \<or> queued_msg st a = None \<and> (\<exists>m. Process1a a m st st2 \<or> Process1b a m st st2)) \<or> two_a_lrn_loop st a \<and> Process1bLearnerLoop a st st2)\<close> by presburger
                then show ?thesis
                  proof (elim disjE)
                    assume "queued_msg st a \<noteq> None \<and>
                            Process1b a (the (queued_msg st a))
                             st st2"
                    then show ?thesis
                      sorry
                  next
                    assume "queued_msg st a = None \<and>
                            (\<exists>m. Process1a a m st st2 \<or>
                                 Process1b a m st st2)"
                    then show ?thesis
                    proof
                      have "\<exists>m. Process1a a m st st2 \<or> Process1b a m st st2"
                        using False \<open>is_safe a \<and> (\<not> two_a_lrn_loop st a \<and> (queued_msg st a \<noteq> None \<and> Process1b a (the (queued_msg st a)) st st2 \<or> queued_msg st a = None \<and> (\<exists>m. Process1a a m st st2 \<or> Process1b a m st st2)) \<or> two_a_lrn_loop st a \<and> Process1bLearnerLoop a st st2)\<close> by blast
                      then show ?thesis
                      proof (elim exE)
                        fix m
                        assume "Process1a a m st st2 \<or> Process1b a m st st2"
                        then show ?thesis
                        proof (elim disjE)
                          assume "Process1a a m st st2"
                          then show ?thesis
                            sorry
                        next
                          assume "Process1b a m st st2"
                          then show ?thesis
                            sorry
                        qed
                      qed
                    qed
                  qed
              qed
          qed
      next
        assume "LearnerAction st st2"
        then show ?thesis
          unfolding LearnerAction.simps
        proof (elim exE)
          fix ln
          assume "(\<exists>m. LearnerRecv ln m st st2) \<or>
                  (\<exists>bal val. LearnerDecide ln bal val st st2)"
          then show ?thesis
          proof (elim disjE)
            assume "\<exists>m. LearnerRecv ln m st st2"
            then show ?thesis
              sorry
          next
            assume "\<exists>bal val. LearnerDecide ln bal val st st2"
            then show ?thesis
              sorry
          qed
        qed
      next
        assume "FakeAcceptorAction st st2"
        then show ?thesis
          unfolding FakeAcceptorAction.simps
          sorry
      qed
    qed


lemma KnownMsgsaccSpecInvariant :
  assumes "RecentMsgs_accSpec st"
  assumes "QueuedMsgSpec1 st"
  assumes "KnownMsgs_accSpec st"
  assumes "Next st st2"
  shows "KnownMsgs_accSpec st2"
  unfolding KnownMsgs_accSpec.simps
proof (clarify)
  fix a2 m
  assume "is_safe a2"
         "m \<in> set (known_msgs_acc st2 a2)"
  have "Next st st2"
    using assms(4) by blast
  then show "m \<in> set (msgs st2) \<and>
        Proper_acc st2 a2 m \<and>
        WellFormed st2 m \<and>
        Tran m \<subseteq> set (known_msgs_acc st2 a2) \<and>
        Ex (B m)"
    unfolding Next.simps
  proof (elim disjE)
    assume "ProposerSendAction st st2"
    show ?thesis
    proof (intro conjI)
      show "m \<in> set (msgs st2)"
        using \<open>ProposerSendAction st st2\<close> \<open>is_safe a2\<close> \<open>m \<in> set (known_msgs_acc st2 a2)\<close> assms(3) by force
    next
      show "Proper_acc st2 a2 m"
        by (metis KnownMsgs_accSpec.elims(2) Proper_acc.elims(2) Proper_acc.elims(3) ProposerSendAction.elims(1) Send1a.elims(2) \<open>ProposerSendAction st st2\<close> \<open>is_safe a2\<close> \<open>m \<in> set (known_msgs_acc st2 a2)\<close> assms(3) simps(12) simps(2) surjective)
    next
      have "known_msgs_acc st2 a2 = known_msgs_acc st a2"
        using \<open>ProposerSendAction st st2\<close> by auto
      have "WellFormed st m"
        by (metis KnownMsgs_accSpec.elims(2) \<open>is_safe a2\<close> \<open>known_msgs_acc st2 a2 = known_msgs_acc st a2\<close> \<open>m \<in> set (known_msgs_acc st2 a2)\<close> assms(3))
      have "TrustLive (lrn m) (q st2 m) = TrustLive (lrn m) (q st m)"
        using \<open>ProposerSendAction st st2\<close> by fastforce
      show "WellFormed st2 m"
        by (metis WellFormed.elims(1) \<open>TrustLive (lrn m) (q st2 m) = TrustLive (lrn m) (q st m)\<close> \<open>WellFormed st m\<close>)
    next
      show "Tran m \<subseteq> set (known_msgs_acc st2 a2)"
        by (metis (mono_tags, lifting) KnownMsgs_accSpec.elims(2) ProposerSendAction.elims(1) Send1a.elims(2) \<open>ProposerSendAction st st2\<close> \<open>is_safe a2\<close> \<open>m \<in> set (known_msgs_acc st2 a2)\<close> assms(3) simps(12) simps(2) surjective)
    next
      show "Ex (B m)"
        by auto
    qed
  next
    assume "AcceptorProcessAction st st2"
    then show ?thesis
      unfolding AcceptorProcessAction.simps
      proof (elim exE)
        fix a
        assume "is_safe a \<and>
                  (\<not> two_a_lrn_loop st a \<and>
                   (queued_msg st a \<noteq> None \<and>
                    Process1b a (the (queued_msg st a)) st st2 \<or>
                    queued_msg st a = None \<and>
                    (\<exists>m. Process1a a m st st2 \<or> Process1b a m st st2)) \<or>
                   two_a_lrn_loop st a \<and> Process1bLearnerLoop a st st2)"
        show ?thesis
        proof (cases "two_a_lrn_loop st a")
            case True
            have "Process1bLearnerLoop a st st2" 
              using True \<open>is_safe a \<and> (\<not> two_a_lrn_loop st a \<and> (queued_msg st a \<noteq> None \<and> Process1b a (the (queued_msg st a)) st st2 \<or> queued_msg st a = None \<and> (\<exists>m. Process1a a m st st2 \<or> Process1b a m st st2)) \<or> two_a_lrn_loop st a \<and> Process1bLearnerLoop a st st2)\<close> by blast
            then show ?thesis
            unfolding Process1bLearnerLoop.simps
            proof (elim disjE)
              assume "\<exists>ln. ln \<notin> processed_lrns st a \<and>
                        Process1bLearnerLoopStep a ln st st2"
              then show ?thesis
              proof (elim exE)
                fix ln
                assume "ln \<notin> processed_lrns st a \<and>
                        Process1bLearnerLoopStep a ln st st2"
                show ?thesis
                proof (intro conjI)
                  show "m \<in> set (msgs st2)"
                    by (smt (verit, del_insts) KnownMsgs_accSpec.elims(2) Process1bLearnerLoopStep.elims(2) Send.elims(2) Store_acc.elims(2) \<open>\<exists>ln. ln \<notin> processed_lrns st a \<and> Process1bLearnerLoopStep a ln st st2\<close> \<open>is_safe a2\<close> \<open>m \<in> set (known_msgs_acc st2 a2)\<close> assms(3) in_set_member member_rec(1))
                next
                  show "Proper_acc st2 a2 m"
                    by (smt (verit, del_insts) KnownMsgs_accSpec.elims(2) Process1bLearnerLoopStep.elims(2) Proper_acc.elims(2) Proper_acc.elims(3) RecentMsgs_accSpec.simps Store_acc.elims(2) \<open>\<exists>ln. ln \<notin> processed_lrns st a \<and> Process1bLearnerLoopStep a ln st st2\<close> \<open>is_safe a2\<close> \<open>m \<in> set (known_msgs_acc st2 a2)\<close> assms(1) assms(3) list.set_intros(2) ref.simps(3) set_ConsD subsetD)
                next
                  show "WellFormed st2 m"
                    sorry
                next
                  show "Tran m \<subseteq> set (known_msgs_acc st2 a2)"
                    sorry
                next
                  show "Ex (B m)"
                    by auto
                qed
              qed
            next
              assume "Process1bLearnerLoopDone a st st2"
              then show ?thesis
                sorry
            qed
          next
            case False
            have "(queued_msg st a \<noteq> None \<and>
                      Process1b a (the (queued_msg st a)) st st2 \<or>
                      queued_msg st a = None \<and>
                      (\<exists>m. Process1a a m st st2 \<or> Process1b a m st st2))"
              using False \<open>is_safe a \<and> (\<not> two_a_lrn_loop st a \<and> (queued_msg st a \<noteq> None \<and> Process1b a (the (queued_msg st a)) st st2 \<or> queued_msg st a = None \<and> (\<exists>m. Process1a a m st st2 \<or> Process1b a m st st2)) \<or> two_a_lrn_loop st a \<and> Process1bLearnerLoop a st st2)\<close> by presburger
            then show ?thesis
              proof (elim disjE)
                assume "queued_msg st a \<noteq> None \<and>
                        Process1b a (the (queued_msg st a))
                         st st2"
                then show ?thesis
                  sorry
              next
                assume "queued_msg st a = None \<and>
                        (\<exists>m. Process1a a m st st2 \<or>
                             Process1b a m st st2)"
                then show ?thesis
                proof
                  have "\<exists>m. Process1a a m st st2 \<or> Process1b a m st st2"
                    using False \<open>is_safe a \<and> (\<not> two_a_lrn_loop st a \<and> (queued_msg st a \<noteq> None \<and> Process1b a (the (queued_msg st a)) st st2 \<or> queued_msg st a = None \<and> (\<exists>m. Process1a a m st st2 \<or> Process1b a m st st2)) \<or> two_a_lrn_loop st a \<and> Process1bLearnerLoop a st st2)\<close> by blast
                  then show ?thesis
                  proof (elim exE)
                    fix m
                    assume "Process1a a m st st2 \<or> Process1b a m st st2"
                    then show ?thesis
                    proof (elim disjE)
                      assume "Process1a a m st st2"
                      then show ?thesis
                        sorry
                    next
                      assume "Process1b a m st st2"
                      then show ?thesis
                        sorry
                    qed
                  qed
                qed
              qed
          qed
      qed
  next
    assume "LearnerAction st st2"
    then show ?thesis
      unfolding LearnerAction.simps
    proof (elim exE)
      fix ln
      assume "(\<exists>m. LearnerRecv ln m st st2) \<or>
              (\<exists>bal val. LearnerDecide ln bal val st st2)"
      then show ?thesis
      proof (elim disjE)
        assume "\<exists>m. LearnerRecv ln m st st2"
        then show ?thesis
          sorry
      next
        assume "\<exists>bal val. LearnerDecide ln bal val st st2"
        then show ?thesis
          sorry
      qed
    qed
  next
    assume "FakeAcceptorAction st st2"
    then show ?thesis
      unfolding FakeAcceptorAction.simps
      sorry
  qed
qed

lemma KnownMsgslrnSpecInvariant :
  assumes "RecentMsgs_lrnSpec st"
  assumes "QueuedMsgSpec1 st"
  assumes "KnownMsgs_lrnSpec st"
  assumes "Next st st2"
  shows "KnownMsgs_lrnSpec st2"
  unfolding KnownMsgs_lrnSpec.simps
  sorry

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
      unfolding AcceptorProcessAction.simps
      proof (elim exE)
        fix a
        assume "is_safe a \<and>
                  (\<not> two_a_lrn_loop st a \<and>
                   (queued_msg st a \<noteq> None \<and>
                    Process1b a (the (queued_msg st a)) st st2 \<or>
                    queued_msg st a = None \<and>
                    (\<exists>m. Process1a a m st st2 \<or> Process1b a m st st2)) \<or>
                   two_a_lrn_loop st a \<and> Process1bLearnerLoop a st st2)"
        show ?thesis
        proof (cases "two_a_lrn_loop st a")
          case True
          have "Process1bLearnerLoop a st st2" 
            using True \<open>is_safe a \<and> (\<not> two_a_lrn_loop st a \<and> (queued_msg st a \<noteq> None \<and> Process1b a (the (queued_msg st a)) st st2 \<or> queued_msg st a = None \<and> (\<exists>m. Process1a a m st st2 \<or> Process1b a m st st2)) \<or> two_a_lrn_loop st a \<and> Process1bLearnerLoop a st st2)\<close> by blast
          then show ?thesis
            by (metis Tran.simps(2) Tran.simps(3) UnCI \<open>type m1 \<noteq> T1a\<close> singletonI type.elims)
        next
          case False
          have "(queued_msg st a \<noteq> None \<and>
                    Process1b a (the (queued_msg st a)) st st2 \<or>
                    queued_msg st a = None \<and>
                    (\<exists>m. Process1a a m st st2 \<or> Process1b a m st st2))"
            using False \<open>is_safe a \<and> (\<not> two_a_lrn_loop st a \<and> (queued_msg st a \<noteq> None \<and> Process1b a (the (queued_msg st a)) st st2 \<or> queued_msg st a = None \<and> (\<exists>m. Process1a a m st st2 \<or> Process1b a m st st2)) \<or> two_a_lrn_loop st a \<and> Process1bLearnerLoop a st st2)\<close> by presburger
          then show ?thesis
            by (metis Tran.simps(2) Tran.simps(3) UnCI \<open>type m1 \<noteq> T1a\<close> equals0I option.distinct(1) option.simps(15) set_empty_eq singletonD type.elims)
          qed
        qed
  next
    assume "LearnerAction st st2"
    then show ?thesis
      unfolding LearnerAction.simps
    proof (elim exE)
      fix ln
      assume "(\<exists>m. LearnerRecv ln m st st2) \<or>
              (\<exists>bal val. LearnerDecide ln bal val st st2)"
      then show ?thesis
        by (metis (no_types, lifting) LearnerDecide.elims(2) LearnerRecv.elims(2) MsgsSafeAcceptorSpec.elims(2) \<open>is_safe (acc m1)\<close> \<open>m1 \<in> set (msgs st2)\<close> \<open>type m1 \<noteq> T1a\<close> assms(3) ext_inject surjective update_convs(3) update_convs(9))
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
        unfolding AcceptorProcessAction.simps
        proof (elim exE)
          fix a
          assume "is_safe a \<and>
                    (\<not> two_a_lrn_loop st a \<and>
                     (queued_msg st a \<noteq> None \<and>
                      Process1b a (the (queued_msg st a)) st st2 \<or>
                      queued_msg st a = None \<and>
                      (\<exists>m. Process1a a m st st2 \<or> Process1b a m st st2)) \<or>
                     two_a_lrn_loop st a \<and> Process1bLearnerLoop a st st2)"
          show ?thesis
          proof (cases "two_a_lrn_loop st a")
            case True
            have "Process1bLearnerLoop a st st2" 
              using True \<open>is_safe a \<and> (\<not> two_a_lrn_loop st a \<and> (queued_msg st a \<noteq> None \<and> Process1b a (the (queued_msg st a)) st st2 \<or> queued_msg st a = None \<and> (\<exists>m. Process1a a m st st2 \<or> Process1b a m st st2)) \<or> two_a_lrn_loop st a \<and> Process1bLearnerLoop a st st2)\<close> by blast
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
              using False \<open>is_safe a \<and> (\<not> two_a_lrn_loop st a \<and> (queued_msg st a \<noteq> None \<and> Process1b a (the (queued_msg st a)) st st2 \<or> queued_msg st a = None \<and> (\<exists>m. Process1a a m st st2 \<or> Process1b a m st st2)) \<or> two_a_lrn_loop st a \<and> Process1bLearnerLoop a st st2)\<close> by presburger
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
      assume "LearnerAction st st2"
      then show ?thesis 
      unfolding LearnerAction.simps
      proof (elim exE)
        fix ln
        assume "(\<exists>m. LearnerRecv ln m st
                st2) \<or>
                (\<exists>bal val.
                    LearnerDecide ln bal val st
                     st2)"
        then show ?thesis
        proof (elim disjE)
          assume "\<exists>m. LearnerRecv ln m st st2"
          have "decision st2 = decision st"
            using \<open>\<exists>m. LearnerRecv ln m st st2\<close> by fastforce
          then show ?thesis
            using \<open>V1 \<in> decision st2 L1 B1\<close> \<open>V2 \<in> decision st2 L2 B2\<close> \<open>ent L1 L2\<close> assms(2) by force
        next
          assume "\<exists>bal val. LearnerDecide ln bal val st st2"
          then show ?thesis
            unfolding LearnerDecide.simps Safety.simps ChosenIn.simps
          proof (elim exE)
          fix bal val
          assume "(\<exists>S \<subseteq> Known2a st ln bal val. TrustLive ln (acc ` S)) \<and>
                  st2 = st
                       \<lparr>decision :=
                          \<lambda>x y. if x = ln \<and> y = bal
                                 then {val} \<union> decision st x y
                                 else decision st x y\<rparr>"
          then show "V1 = V2"
          proof
            have sthyp: "st2 = st
                       \<lparr>decision :=
                          \<lambda>x y. if x = ln \<and> y = bal
                                 then {val} \<union> decision st x y
                                 else decision st x y\<rparr>"
              using \<open>(\<exists>S\<subseteq>Known2a st ln bal val. TrustLive ln (acc ` S)) \<and> st2 = st \<lparr>decision := \<lambda>x y. if x = ln \<and> y = bal then {val} \<union> decision st x y else decision st x y\<rparr>\<close> by blast
            have "\<exists>S \<subseteq> Known2a st ln bal val. TrustLive ln (acc ` S)"
              using \<open>(\<exists>S\<subseteq>Known2a st ln bal val. TrustLive ln (acc ` S)) \<and> st2 = st \<lparr>decision := \<lambda>x y. if x = ln \<and> y = bal then {val} \<union> decision st x y else decision st x y\<rparr>\<close> by blast
            then show "V1 = V2"
            proof (elim exE)
              fix S
              assume "S \<subseteq> Known2a st ln bal val \<and> TrustLive ln (acc ` S)"
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
              by (metis FakeSend1b.elims(2) \<open>FakeSend1b a st st2\<close> select_convs(9) simps(12) surjective)
            then show ?thesis
              using \<open>V1 \<in> decision st2 L1 B1\<close> \<open>V2 \<in> decision st2 L2 B2\<close> \<open>ent L1 L2\<close> assms(2) by force
          next
            assume "FakeSend2a a st st2"
            have "decision st2 = decision st"
              by (metis FakeSend2a.simps \<open>FakeSend2a a st st2\<close> select_convs(9) simps(12) surjective)
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
  show "RecentMsgs_accSpec st2"
    by (meson FullSafetyInvariant.elims(2) RecentMsgsaccSpecInvariant assms(1) assms(2))
next
  show "RecentMsgs_lrnSpec st2"
    by (meson FullSafetyInvariant.elims(2) RecentMsgslrnSpecInvariant assms(1) assms(2))
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

end