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

fun bal :: "PreMessage \<Rightarrow> Ballot" where
  "bal (M1a b) = b" |
  "bal (M1b _ _) = undefined" |
  "bal (M2a _ _ _) = undefined"

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

theorem Valid_contains_bltlot:
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

lemma Message_ref_Tran:
  shows "m2 \<in> ref m1 \<Longrightarrow> m2 \<in> Tran m1"
proof (induction m1)
  case (M1a x)
  show "m2 \<in> Tran (M1a x)"
    using M1a by auto
next
  case (M1b x r)
  fix x1a x2
  assume hyp: "\<And>x2a. x2a \<in> set x2 \<Longrightarrow>
             m2 \<in> ref x2a \<Longrightarrow>
             m2 \<in> Tran x2a"
          "m2 \<in> ref (M1b x1a x2)"
  show "m2 \<in> Tran (M1b x1a x2)"
    by (smt (z3) Tran.simps(1) Tran.simps(2) Tran.simps(3) Un_insert_left Un_insert_right Union_image_insert hyp(2) insertI1 insert_absorb isValidMessage.cases ref.simps(2))
next
  case (M2a x1a x2 x3)
  fix x1a x2 x3
  assume hyp: "\<And>x3a. x3a \<in> set x3 \<Longrightarrow>
             m2 \<in> ref x3a \<Longrightarrow>
             m2 \<in> Tran x3a"
          "m2 \<in> ref (M2a x1a x2 x3)"
  show "m2 \<in> Tran (M2a x1a x2 x3)"
    by (metis Tran.simps(1) Tran.simps(2) Tran.simps(3) UnCI Union_image_insert hyp(2) insertI1 insert_absorb ref.simps(3) type.elims)
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
  "B m blt = (blt = Get1a m)"

record State =
  msgs :: "PreMessage list"
  known_msgs_acc :: "Acceptor \<Rightarrow> PreMessage list"
  known_msgs_lrn :: "Learner \<Rightarrow> PreMessage list"
  recent_msgs :: "Acceptor \<Rightarrow> PreMessage list"
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
      recent_msgs = (\<lambda>_. []), 
      queued_msg = (\<lambda>_. NoMessage), 
      two_a_lrn_loop = (\<lambda>_. False), 
      processed_lrns = (\<lambda>_. {}), 
      decision = (\<lambda>_ _. {}), 
      BVal = bval 
    \<rparr>"

fun V :: "State \<Rightarrow> PreMessage \<Rightarrow> Value \<Rightarrow> bool" where
  "V st m val = (val = BVal st (Get1a m))"

(*Maximal bltlot number of any messages known to acceptor a*)
(* Direct translation (not used) *)
fun MaxBalL :: "State \<Rightarrow> Acceptor \<Rightarrow> Ballot \<Rightarrow> bool" where
  "MaxBalL st a mblt = 
      ((\<exists> m \<in> set (known_msgs_acc st a). B m mblt)
      \<and> (\<forall> x \<in> set (known_msgs_acc st a).
          \<forall> b :: Ballot. B x b \<longrightarrow> b \<le> mblt))"

(*Better implementation*)
fun MaxBalO :: "State \<Rightarrow> Acceptor \<Rightarrow> Ballot option" where
  "MaxBalO st a = 
    (if known_msgs_acc st a = [] then None else
     Some (Max (Get1a ` set (known_msgs_acc st a))))"

fun MaxBal :: "State \<Rightarrow> Acceptor \<Rightarrow> Ballot \<Rightarrow> bool" where
  "MaxBal st a mblt = (Some mblt = MaxBalO st a)"

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
2a-messages with different values, the same learner, and higher bltlot
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
        let new1b = M1b a (m # recent_msgs st a) in 
        if WellFormed st new1b
        then stp\<lparr>msgs := new1b # msgs st,
                 recent_msgs := 
                   \<lambda>x. if x = a 
                       then [] 
                       else recent_msgs st x,
                 queued_msg := 
                   \<lambda>x. if x = a 
                       then Some new1b 
                       else queued_msg st x\<rparr>
        else stp\<lparr>recent_msgs :=
                   \<lambda>x. if x = a 
                       then m # recent_msgs st x 
                       else recent_msgs st x\<rparr>
    | M1b a2 ms \<Rightarrow> 
        let stpp = 
          stp\<lparr>queued_msg := 
                  \<lambda>x. if x = a
                      then None
                      else queued_msg st x,
              recent_msgs :=
                  \<lambda>x. if x = a 
                      then m # recent_msgs st x 
                      else recent_msgs st x\<rparr> in
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
        stp\<lparr>recent_msgs :=
                \<lambda>x. if x = a 
                    then m # recent_msgs st x 
                    else recent_msgs st x\<rparr>
  )"

(**)

(* Process1a as a predicate *)
fun Process1a :: "Acceptor \<Rightarrow> PreMessage \<Rightarrow> State \<Rightarrow> State \<Rightarrow> bool" where
  "Process1a a m st st2 = (
    let new1b = M1b a (m # recent_msgs st a) in 
    type m = T1a
    \<and> Recv_acc st a m
    \<and> Store_acc a m st st2
    \<and> (if WellFormed st new1b
       then 
          Send new1b st st2
          \<and> (recent_msgs st2 = (
              \<lambda>a2. if a2 = a then []
                             else recent_msgs st a2))
          \<and> (queued_msg st2 = (
              \<lambda>a2. if a2 = a then Some new1b 
                             else queued_msg st a2))
       else 
          (recent_msgs st2 = (
              \<lambda>a2. if a2 = a then m # recent_msgs st a2 
                             else recent_msgs st a2))
          \<and> (msgs st = msgs st2)
          \<and> (queued_msg st = queued_msg st2)
      )

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
    \<and> recent_msgs st2 = (
        \<lambda>x. if x = a 
            then m # recent_msgs st x
            else recent_msgs st x )
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
    \<and> recent_msgs st2 = (
        \<lambda>x. if x = a 
            then m # recent_msgs st x
            else recent_msgs st x )

    \<and> (msgs st2 = msgs st)
    \<and> (queued_msg st2 = queued_msg st)
    \<and> (two_a_lrn_loop st2 = two_a_lrn_loop st)
    \<and> (processed_lrns st2 = processed_lrns st)
    \<and> (decision st2 = decision st)
    \<and> (BVal st2 = BVal st)
  )"

fun ProposerSendAction :: "State \<Rightarrow> State \<Rightarrow> bool" where
  "ProposerSendAction st st2 = (\<exists>blt :: Ballot. Send1a blt st st2)"

fun Process1bLearnerLoopStep :: "Acceptor \<Rightarrow> Learner \<Rightarrow> State \<Rightarrow> State \<Rightarrow> bool" where
  "Process1bLearnerLoopStep a ln st st2 = (
    let new2a = M2a ln a (recent_msgs st a) in
    processed_lrns st2 = (
      \<lambda>x . if x = a
           then {ln} \<union> processed_lrns st x
           else processed_lrns st x)
    \<and> (if (WellFormed st new2a)
       then (
            Send new2a st st2
          \<and> Store_acc a new2a st st2
          \<and> (recent_msgs st2 = (
              \<lambda>x . if x = a
                 then [new2a]
                 else recent_msgs st x))
          )
       else (
            (msgs st2 = msgs st)
          \<and> (known_msgs_acc st2 = known_msgs_acc st)
          \<and> (known_msgs_lrn st2 = known_msgs_lrn st)
          \<and> (recent_msgs st2 = recent_msgs st)
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
        new2a = M2a ln a (recent_msgs st a) in
    if \<not> (WellFormed st new2a)
    then stp
    else 
      stp\<lparr>msgs := new2a # msgs st,
          known_msgs_acc := (
              \<lambda>x. if a = x 
                  then new2a # known_msgs_acc st x
                  else known_msgs_acc st x),
          recent_msgs := (
              \<lambda>x . if x = a
                 then [new2a]
                 else recent_msgs st x)\<rparr>
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

fun AcceptorAction :: "Acceptor \<Rightarrow> State \<Rightarrow> State \<Rightarrow> bool" where
  "AcceptorAction a st st2 = (
    is_safe a \<and> (
      (\<not> two_a_lrn_loop st a \<and>
       ((queued_msg st a \<noteq> None \<and> 
         Process1b a (the (queued_msg st a)) st st2) \<or> 
        (queued_msg st a = None \<and> (
          \<exists>m \<in> set (msgs st). Process1a a m st st2 \<or> Process1b a m st st2
        ))))
      \<or> (two_a_lrn_loop st a \<and> 
         Process1bLearnerLoop a st st2)
  ))"

fun AcceptorProcessAction :: "State \<Rightarrow> State \<Rightarrow> bool" where
  "AcceptorProcessAction st st2 = (\<exists>a :: Acceptor. AcceptorAction a st st2)"

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
      (\<exists>m \<in> set (msgs st). LearnerRecv ln m st st2) \<or>
      (\<exists>blt :: Ballot. \<exists>val :: Value. LearnerDecide ln blt val st st2)
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

end