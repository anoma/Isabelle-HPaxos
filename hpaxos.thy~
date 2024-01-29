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

type_synonym MessageDepthRange = nat

(*
Morally, messages have the following inductive structure

T1a : \<forall> n: nat. Ballot \<Rightarrow> MessageRec n
T1b : \<forall> n: nat. Acceptor \<Rightarrow> FINSUBSET(MessageRec n, MessageDepthRange) \<Rightarrow> MessageRec (n + 1)
T2a : \<forall> n: nat. Learner \<Rightarrow> Acceptor \<Rightarrow> FINSUBSET(MessageRec n, MessageDepthRange) \<Rightarrow> MessageRec (n + 1)

Message \<equiv> \<Union>n. {MessageRec n}
*)

datatype PreMessage = 
  T1a Ballot 
| T1b "Acceptor * PreMessage list" 
| T2a "Learner * Acceptor * PreMessage list"

fun isValidMessage :: "PreMessage \<Rightarrow> bool" where
  "isValidMessage (T1a _) = True" |
  "isValidMessage (T1b (_, msgs)) = (msgs \<noteq> [] \<and> length msgs \<le> MaxRefCardinality \<and> list_all isValidMessage msgs)" |
  "isValidMessage (T2a (_, _, msgs)) = (msgs \<noteq> [] \<and> length msgs \<le> MaxRefCardinality \<and> list_all isValidMessage msgs)"

typedef (overloaded) Message = "{a::PreMessage. isValidMessage a}"
proof
  show "T1a 0 \<in> {a::PreMessage. isValidMessage a}"
    by simp
qed

(* Transitive references *)
(* ------------------------------------------------------------------- *)



(*
11. bb
bb is a natural number since it's compared to Ballot

12. LL
LL is a Learner

13. QQ
QQ is the same sort of thing as SafeAcceptor, since it can be a subset of SafeAcceptor.
*)


end