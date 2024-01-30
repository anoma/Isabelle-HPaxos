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

consts is_quorum :: "(Acceptor \<Rightarrow> bool) \<Rightarrow> bool"

axiomatization where
  safe_is_quorum: "is_quorum is_safe"

typedef (overloaded) ByzQuorum = "{a::Acceptor \<Rightarrow> bool. is_quorum a}"
proof
  show "is_safe \<in> {a::Acceptor \<Rightarrow> bool. is_quorum a}"
    using safe_is_quorum by simp
qed

(* Learner graph *)
(* ------------------------------------------------------------------- *)

consts TrustLive :: "Learner \<Rightarrow> (Acceptor \<Rightarrow> bool) \<Rightarrow> bool"
consts TrustSafe :: "Learner \<Rightarrow> Learner \<Rightarrow> (Acceptor \<Rightarrow> bool) \<Rightarrow> bool"

axiomatization where
  TrustLiveAssumption: "\<forall>l q. TrustLive l q \<Longrightarrow> is_quorum q"

axiomatization where
  TrustSafeAssumption: "\<forall>l1 l2 q. TrustSafe l1 l2 q \<Longrightarrow> is_quorum q"

axiomatization where
  LearnerGraphAssumptionSymmetry: 
    "\<forall>l1 l2 q. TrustSafe l1 l2 q \<Longrightarrow> TrustSafe l2 l1 q"

axiomatization where
  LearnerGraphAssumptionTransitivity:
    "\<forall>l1 l2 l3 q. TrustSafe l1 l2 q \<and> TrustSafe l2 l3 q \<Longrightarrow> TrustSafe l1 l2 q"

axiomatization where
  LearnerGraphAssumptionClosure:
    "\<forall>l1 l2 q Q. TrustSafe l1 l2 q \<and> is_quorum Q \<and> (\<forall>a . q a \<longrightarrow> Q a) \<Longrightarrow> TrustSafe l1 l2 q2"

axiomatization where
  LearnerGraphAssumptionValidity:
    "\<forall>l1 l2 q Q1 Q2. 
      TrustSafe l1 l2 q \<and> is_quorum Q1 \<and> is_quorum Q2 \<and>
      TrustLive l1 Q1 \<and> TrustLive l2 Q2 \<Longrightarrow>
      \<exists> N:: Acceptor. q N \<and> Q1 N \<and> Q2 N"

(* Entanglement relation *)
definition ent :: "Learner \<Rightarrow> Learner \<Rightarrow> bool" where
  "ent l1 l2 = TrustSafe l1 l2 is_safe"

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
  processed_lrns :: "Acceptor \<Rightarrow> Learner list"
  decision :: "Learner \<Rightarrow> Ballot \<Rightarrow> Value list"
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
      processed_lrns = (\<lambda>_. []), 
      decision = (\<lambda>_ _. []), 
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

fun ConByQuorum :: "Learner \<Rightarrow> Learner \<Rightarrow> PreMessage \<Rightarrow> (Acceptor \<Rightarrow> bool) \<Rightarrow> bool" where
  "ConByQuorum a b x S = (
      TrustSafe a b S \<and> 
      (\<forall> a \<in> Caught x. \<not> (S a))
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
     in TrustLive (lrn x) (\<lambda>a . a \<in> acc ` Q)
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
  "q st x = (
    let Q = { m . m \<in> Tran x
                \<and> type m = T1b
                \<and> Fresh st (lrn x) m
                \<and> (\<forall>b :: Ballot. B m b = B x b)
            }
    in acc ` Q
  )"





(*
11. bb
bb is a natural number since it's compared to Ballot

12. LL
LL is a Learner

13. QQ
QQ is the same sort of thing as SafeAcceptor, since it can be a subset of SafeAcceptor.
*)


end