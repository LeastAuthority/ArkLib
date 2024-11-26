/-
Copyright (c) 2024 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import VCVio
import ZKLib.Data.Math.Fin

/-!
# (Interactive) Oracle Reductions

We define (public-coin) interactive oracle reductions (IORs). This is an interactive protocol
between a prover and a verifier with the following format:

  - At the beginning, the prover and verifier both hold a public statement `x` (and potentially have
    access to some public parameters `pp`). The prover may also hold some private state which in
    particular may contain a witness `w` to the statement `x`.

  - In each round, the verifier sends some random challenges, and the prover sends back responses to
    the challenges. The responses are received as oracles by the verifier. The verifier is only
    allowed to query these oracles in specific ways.

  - At the end of the interaction, the verifier outputs a decision.

Along the way, we also define Interactive Proofs (IPs) as a special kind of IOPs where
the verifier can see the full messages. Our formalization also allows both prover and verifier
to have access to some shared oracle.

Note: the definition of IORs as defined above generalizes those found in the literature. When the
output relation is the Boolean relation (where `StmtOut = Bool`), then we recover a generalized
version of Interactive Oracle Proofs (IOPs) [BCS16]. The particular IOP considered in [BCS16] may be
called "point IOP" due to its query structure. We also get "polynomial IOP" [BCG+19] and "tensor
IOP" [BCG20] (and other kinds of IOPs) from our definition.

-/

set_option linter.docPrime false

open OracleComp OracleSpec SubSpec

section Prelude

-- Figure out where to put this instance
instance instDecidableEqOption {α : Type*} [DecidableEq α] : DecidableEq (Option α) := inferInstance

/-- `Sampleable` is a type class for types that can be sampled uniformly at random (via the VCV
    framework). This is mostly used for uniform sampling from challenges in an interactive protocol.
-/
class Sampleable (α : Type) extends Fintype α, Inhabited α, SelectableType α where
  [toDecidableEq : DecidableEq α]

instance {α : Type} [Sampleable α] : DecidableEq α := Sampleable.toDecidableEq

/-- Enum type for the direction of a round in a protocol specification -/
inductive Direction where
  | P_to_V -- Message
  | V_to_P -- Challenge
deriving DecidableEq, Inhabited, Repr

/-- Equivalence between `Direction` and `Fin 2`, sending `V_to_P` to `0` and `P_to_V` to `1`
(the choice is essentially arbitrary). -/
def DirectionEquivFin2 : Direction ≃ Fin 2 where
  toFun := fun dir => match dir with
    | .V_to_P => ⟨0, by decide⟩
    | .P_to_V => ⟨1, by decide⟩
  invFun := fun n => match n with
    | ⟨0, _⟩ => .V_to_P
    | ⟨1, _⟩ => .P_to_V
  left_inv := fun dir => match dir with
    | .P_to_V => rfl
    | .V_to_P => rfl
  right_inv := fun n => match n with
    | ⟨0, _⟩ => rfl
    | ⟨1, _⟩ => rfl

/-- This allows us to write `0` for `.V_to_P` and `1` for `.P_to_V`. -/
instance : Coe (Fin 2) Direction := ⟨DirectionEquivFin2.invFun⟩

end Prelude

section Format

/-- Type signature for an interactive protocol, with `n` messages exchanged. -/
@[reducible]
def ProtocolSpec (n : ℕ) := Fin n → Direction × Type

variable {n : ℕ}

namespace ProtocolSpec

abbrev getDir (pSpec : ProtocolSpec n) (i : Fin n) := pSpec i |>.1

abbrev getType (pSpec : ProtocolSpec n) (i : Fin n) := pSpec i |>.2

/-- We set the rewrite to follow `getDir` instead of `Prod.fst`? -/
@[simp]
theorem getDir_apply (pSpec : ProtocolSpec n) (i : Fin n) : pSpec.getDir i = (pSpec i).1 := rfl

@[simp]
theorem getType_apply (pSpec : ProtocolSpec n) (i : Fin n) : pSpec.getType i = (pSpec i).2 := rfl

/-- Subtype of `Fin n` for the indices corresponding to messages in a protocol specification -/
def MessageIndex (pSpec : ProtocolSpec n) :=
  {i : Fin n // pSpec.getDir i = Direction.P_to_V}

/-- Subtype of `Fin n` for the indices corresponding to challenges in a protocol specification -/
def ChallengeIndex (pSpec : ProtocolSpec n) :=
  {i : Fin n // pSpec.getDir i = Direction.V_to_P}

/-- The type of the `i`-th message in a protocol specification -/
@[inline, reducible]
def Message (pSpec : ProtocolSpec n) (i : MessageIndex pSpec) :=
  pSpec.getType i.val

/-- The type of the `i`-th challenge in a protocol specification -/
@[inline, reducible]
def Challenge (pSpec : ProtocolSpec n) (i : ChallengeIndex pSpec) :=
  pSpec.getType i.val

end ProtocolSpec

open ProtocolSpec

/-- The transcript of an interactive protocol, which is a list of messages and challenges -/
@[inline, reducible]
def Transcript (pSpec : ProtocolSpec n) := (i : Fin n) → pSpec.getType i

@[inline, reducible]
def PartialTranscript (pSpec : ProtocolSpec n) (m : ℕ) := (i : Fin n) → (i < m) → pSpec.getType i

def emptyPartialTranscript {pSpec : ProtocolSpec n} : PartialTranscript pSpec 0 :=
  fun i hi => by contradiction

variable {ι : Type}

variable {pSpec : ProtocolSpec n} {oSpec : OracleSpec ι} {State : Type}

@[inline, reducible]
def PartialTranscript.toFull {m : ℕ} (h : n ≤ m) (T : PartialTranscript pSpec m) :
    Transcript pSpec := fun i => T i (Nat.lt_of_lt_of_le i.isLt h)

def PartialTranscript.snoc {m : ℕ} (h : m < n) (msg : pSpec.getType ⟨m, h⟩)
    (T : PartialTranscript pSpec m) : PartialTranscript pSpec (m + 1) := fun i hi => by
  by_cases hi' : i < m
  · exact T i hi'
  · haveI : i = ⟨m, h⟩ := by ext; simp; exact Nat.eq_of_lt_succ_of_not_lt hi hi'
    exact this ▸ msg

@[inline, reducible]
def Transcript.messages (transcript : Transcript pSpec) (i : MessageIndex pSpec) :=
  transcript i.val

@[inline, reducible]
def Transcript.challenges (transcript : Transcript pSpec) (i : ChallengeIndex pSpec) :=
  transcript i.val

@[inline, reducible]
def Transcript.mk2 {pSpec : ProtocolSpec 2} (msg0 : pSpec.getType 0) (msg1 : pSpec.getType 1) :
    Transcript pSpec := fun | ⟨0, _⟩ => msg0 | ⟨1, _⟩ => msg1

theorem Transcript.mk2_eq_toFull_snoc_snoc {pSpec : ProtocolSpec 2} (msg0 : pSpec.getType 0)
    (msg1 : pSpec.getType 1) : Transcript.mk2 msg0 msg1 =
      (PartialTranscript.toFull (by simp)
        (PartialTranscript.snoc (by simp) msg1
          (PartialTranscript.snoc (by simp) msg0
            emptyPartialTranscript))) := by
  unfold Transcript.mk2 PartialTranscript.toFull PartialTranscript.snoc emptyPartialTranscript
  simp only [getType_apply, Nat.mod_succ, Nat.lt_one_iff, not_lt_zero', ↓reduceDIte, Fin.zero_eta,
    Fin.isValue, Nat.reduceMod, Nat.succ_eq_add_one, Nat.reduceAdd, Fin.mk_one]
  funext i
  by_cases hi : i = 0
  · subst hi; simp only [Fin.isValue, Fin.val_zero, ↓reduceDIte]
  · have : i = 1 := by omega
    subst this; simp only [Fin.isValue, Fin.val_one, one_ne_zero, ↓reduceDIte]

/-- `ToOracle` is a type class that provides an oracle interface for a type `Message`. It consists
  of a query type `Query`, a response type `Response`, and a function `oracle` that transforms
  a message `m : Message` into a function `Query → Response`. -/
@[ext]
class ToOracle (Message : Type) where
  Query : Type
  Response : Type
  oracle : Message → Query → Response

-- TODO: Notation for the type signature of an interactive protocol?

#eval "𝒫 ——⟦ 𝔽⦃≤ d⦄[X] ⟧⟶ 𝒱"

#eval "𝒫  ⟵⟦ 𝔽 ⟧—— 𝒱"

-- TODO: Notation for the objects / elements sent during the protocol?

#eval "𝒫  ——[ ∑ x ∈ D ^ᶠ (n - i), p ⸨X⦃i⦄, r, x⸩ ]⟶  𝒱"

#eval "𝒫  ⟵[ rᵢ ←$ 𝔽 ]—— 𝒱"

/-- Spec for the verifier's challenges, invoked in the process of running the protocol -/
@[simps]
def challengeOracle (pSpec : ProtocolSpec n) [S : ∀ i, Sampleable (pSpec.Challenge i)] :
    OracleSpec (ChallengeIndex pSpec) where
  domain := fun _ => Unit
  range := fun i => pSpec.Challenge i
  domain_decidableEq' := fun _ => decEq
  range_decidableEq' := fun i => @Sampleable.toDecidableEq _ (S i)
  range_inhabited' := fun i => @Sampleable.toInhabited _ (S i)
  range_fintype' := fun i => @Sampleable.toFintype _ (S i)


-- Add an indexer?
structure Indexer (pSpec : ProtocolSpec n) (oSpec : OracleSpec ι) (Index : Type)
    (Encoding : Type) where
  encode : Index → OracleComp oSpec Encoding
  [toOracle : ToOracle Encoding]

/-- Initialization of prover's state via loading the statement and witness -/
structure ProverIn (pSpec : ProtocolSpec n) (StmtIn WitIn PrvState : Type) where
  load : StmtIn → WitIn → PrvState

/-- Represents the interaction of a prover for a given protocol specification -/
structure ProverRound (pSpec : ProtocolSpec n) (oSpec : OracleSpec ι) (PrvState : Type) where
  /-- Send a message and update the prover's state -/
  sendMessage (i : MessageIndex pSpec) : PrvState → OracleComp oSpec (pSpec.Message i × PrvState)
  /-- Receive a challenge and update the prover's state -/
  receiveChallenge (i : ChallengeIndex pSpec) : PrvState → (pSpec.Challenge i) → PrvState

/-- The output of the prover, which is a function from the prover's state to the output witness -/
structure ProverOut (WitOut PrvState : Type) where
  output : PrvState → WitOut

/-- A prover for an interactive protocol consists of four functions:
  - `load` initializes the prover's state by taking in the input statement and witness
  - `receiveChallenge` updates the prover's state given a challenge
  - `sendMessage` sends a message and updates the prover's state
  - `output` returns the output witness from the prover's state -/
structure Prover (pSpec : ProtocolSpec n) (oSpec : OracleSpec ι)
    (StmtIn WitIn StmtOut WitOut PrvState : Type) extends
      ProverIn pSpec StmtIn WitIn PrvState,
      ProverRound pSpec oSpec PrvState,
      ProverOut WitOut PrvState

/-- A verifier of an interactive protocol is a function that takes in the input statement and the
  transcript, and performs an oracle computation that outputs a new statement -/
structure Verifier (pSpec : ProtocolSpec n) (oSpec : OracleSpec ι) (StmtIn StmtOut : Type) where
  verify : StmtIn → Transcript pSpec → OracleComp oSpec StmtOut

/-- A list of queries to the prover's messages -/
@[inline, reducible]
def QueryList (pSpec : ProtocolSpec n) [O : ∀ i, ToOracle (pSpec.Message i)] :=
  List ((i : MessageIndex pSpec) × (O i).Query)

/-- A list of responses to queries, computed from the prover's messages -/
@[inline, reducible]
def ResponseList (pSpec : ProtocolSpec n) [O : ∀ i, ToOracle (pSpec.Message i)] :=
  List ((i : MessageIndex pSpec) × (O i).Query × (O i).Response)

/-- An **oracle** verifier of an interactive oracle protocol may only make queries to the prover's
    messages (according to a specified interface defined by a `ToOracle` instance).

    Without loss of generality, an oracle verifier consists of two subroutines: `genQueries` and
    `verify` -/
structure OracleVerifier (pSpec : ProtocolSpec n) (oSpec : OracleSpec ι)
    [O : ∀ i, ToOracle (pSpec.Message i)] (StmtIn StmtOut : Type) where
  /-- `genQueries` takes in the statement and the challenges, and generates a list of queries of the
    form `(i, query)` to the prover's messages, where `i` is the round index and `query` is the
    query to the prover's message as an oracle -/
  genQueries : StmtIn → (∀ i, pSpec.Challenge i) → QueryList pSpec
  /-- `verify` takes in the statement, the challenges, and the list of responses, and performs an
    oracle computation that outputs a new statement -/
  verify : StmtIn → (∀ i, pSpec.Challenge i) → ResponseList pSpec → OracleComp oSpec StmtOut

/-- An oracle verifier can be seen as a (non-oracle) verifier in the natural way -/
def OracleVerifier.toVerifier {pSpec : ProtocolSpec n} {oSpec : OracleSpec ι}
    {StmtIn StmtOut : Type} [O : ∀ i, ToOracle (pSpec.Message i)]
    (verifier : OracleVerifier pSpec oSpec StmtIn StmtOut) :
    Verifier pSpec oSpec StmtIn StmtOut where
  verify := fun stmt transcript => do
    letI queries := verifier.genQueries stmt transcript.challenges
    letI responses := queries.map
      (fun q => ⟨q.1, q.2, (O q.1).oracle (transcript.messages q.1) q.2⟩)
    verifier.verify stmt transcript.challenges responses

/-- Make `OracleVerifier.toVerifier` a coercion -/
instance {pSpec : ProtocolSpec n} {oSpec : OracleSpec ι} {StmtIn StmtOut : Type}
    [∀ i, ToOracle (pSpec.Message i)] : Coe (OracleVerifier pSpec oSpec StmtIn StmtOut)
    (Verifier pSpec oSpec StmtIn StmtOut) :=
  ⟨OracleVerifier.toVerifier⟩

/-- An (interactive) reduction for a given protocol specification `pSpec`, and relative to oracles
  defined by `oSpec`, consists of a prover and a verifier. -/
structure Reduction (pSpec : ProtocolSpec n) (oSpec : OracleSpec ι)
    (StmtIn WitIn StmtOut WitOut PrvState : Type) where
  prover : Prover pSpec oSpec StmtIn WitIn StmtOut WitOut PrvState
  verifier : Verifier pSpec oSpec StmtIn StmtOut

/-- An (interactive) oracle reduction for a given protocol specification `pSpec`, and relative to
  oracles defined by `oSpec`, consists of a prover and an **oracle** verifier. -/
structure OracleReduction (pSpec : ProtocolSpec n) [∀ i, ToOracle (pSpec.Message i)]
    (oSpec : OracleSpec ι) (StmtIn WitIn StmtOut WitOut PrvState : Type) where
  prover : Prover pSpec oSpec StmtIn WitIn StmtOut WitOut PrvState
  verifier : OracleVerifier pSpec oSpec StmtIn StmtOut

/-- An interactive oracle reduction can be seen as an interactive reduction, via coercing the oracle
  verifier to a (normal) verifier -/
def OracleReduction.toReduction {pSpec : ProtocolSpec n} {oSpec : OracleSpec ι}
    {StmtIn WitIn StmtOut WitOut PrvState : Type} [∀ i, ToOracle (pSpec.Message i)]
    (oracleReduction : OracleReduction pSpec oSpec StmtIn WitIn StmtOut WitOut PrvState) :
      Reduction pSpec oSpec StmtIn WitIn StmtOut WitOut PrvState :=
  ⟨oracleReduction.prover, oracleReduction.verifier⟩

/-- Make `OracleReduction.toReduction` a coercion -/
instance {pSpec : ProtocolSpec n} [∀ i, ToOracle (pSpec.Message i)] {oSpec : OracleSpec ι}
    {StmtIn WitIn StmtOut WitOut PrvState : Type} :
    Coe (OracleReduction pSpec oSpec StmtIn WitIn StmtOut WitOut PrvState)
    (Reduction pSpec oSpec StmtIn WitIn StmtOut WitOut PrvState) :=
  ⟨OracleReduction.toReduction⟩

/-- An interactive proof is an interactive reduction where the output statement is a boolean and the
  witness is unit (and the output relation is the trivial one). -/
abbrev Proof (pSpec : ProtocolSpec n) (oSpec : OracleSpec ι) (Statement Witness PrvState : Type) :=
  Reduction pSpec oSpec Statement Witness Bool Unit PrvState

/-- An interactive oracle proof is an interactive oracle reduction where the output statement is a
  boolean and the witness is unit (and the output relation is the trivial one). -/
abbrev OracleProof (pSpec : ProtocolSpec n) [∀ i, ToOracle (pSpec.Message i)] (oSpec : OracleSpec ι)
    (Statement Witness PrvState : Type) :=
  OracleReduction pSpec oSpec Statement Witness Bool Unit PrvState

end Format

section Execution

variable {n : ℕ} {ι : Type} [DecidableEq ι] {pSpec : ProtocolSpec n} {oSpec : OracleSpec ι}
  {StmtIn WitIn StmtOut WitOut PrvState : Type}

/--
  Auxiliary function for running the prover in an interactive protocol. Given round index `i`,
  returns the transcript up to that round, the log of oracle queries made by the prover to `oSpec`
  up to that round, and the prover's state after that round.
-/
def Prover.runAux [∀ i, Sampleable (pSpec.Challenge i)] (stmt : StmtIn) (wit : WitIn)
    (i : Fin (n + 1)) (prover : Prover pSpec oSpec StmtIn WitIn StmtOut WitOut PrvState) :
      OracleComp (oSpec ++ₒ challengeOracle pSpec)
        (PartialTranscript pSpec i × QueryLog oSpec × PrvState) :=
  Fin.induction
    (pure ⟨emptyPartialTranscript, ∅, prover.load stmt wit⟩)
    (fun j ih => do
      let ⟨transcript, queryLog, state⟩ ← ih
      match hDir : pSpec.getDir j with
      | .V_to_P => do
        let challenge ← query (Sum.inr ⟨j, hDir⟩) ()
        haveI challenge : pSpec.Challenge ⟨j, hDir⟩ := by simpa only
        letI newState := prover.receiveChallenge ⟨j, hDir⟩ state challenge
        letI newTranscript := transcript.snoc (by simp) challenge
        return ⟨newTranscript, queryLog, newState⟩
      | .P_to_V => do
        let ⟨⟨msg, newState⟩, newQueryLog⟩ ← liftComp
          (simulate loggingOracle queryLog (prover.sendMessage ⟨j, hDir⟩ state))
        letI newTranscript := transcript.snoc j.isLt msg
        return ⟨newTranscript, newQueryLog, newState⟩)
    i

/--
  Run the prover in an interactive protocol. Returns the transcript along with the final prover's
  state
-/
def Prover.run [∀ i, Sampleable (pSpec.Challenge i)] (stmt : StmtIn) (wit : WitIn)
    (prover : Prover pSpec oSpec StmtIn WitIn StmtOut WitOut PrvState) :
      OracleComp (oSpec ++ₒ challengeOracle pSpec)
        (Transcript pSpec × QueryLog oSpec × WitOut) := do
  let ⟨transcript, queryLog, state⟩ ← prover.runAux stmt wit ⟨n, n.lt_add_one⟩
  return ⟨transcript.toFull (by simp only [le_refl]), queryLog, prover.output state⟩

/-- Run the (non-oracle) verifier in the interactive protocol. Simply reads the statement and the
  transcript, and outputs a decision.
-/
def Verifier.run (stmt : StmtIn) (transcript : Transcript pSpec)
    (verifier : Verifier pSpec oSpec StmtIn StmtOut) : OracleComp oSpec StmtOut :=
  verifier.verify stmt transcript

/-- Run the oracle verifier in the interactive protocol. Returns the verifier's output and the log
  of queries made by the verifier.
-/
def OracleVerifier.run [O : ∀ i, ToOracle (pSpec.Message i)] (stmt : StmtIn)
    (transcript : Transcript pSpec) (verifier : OracleVerifier pSpec oSpec StmtIn StmtOut) :
      OracleComp oSpec (ResponseList pSpec × StmtOut) := do
  let queries := verifier.genQueries stmt transcript.challenges
  let oracles := fun i => (O i).oracle (transcript.messages i)
  let responses := queries.map (fun q => ⟨q.1, q.2, oracles q.1 q.2⟩)
  let decision ← verifier.verify stmt transcript.challenges responses
  return ⟨responses, decision⟩

omit [DecidableEq ι] in
/-- Running an oracle verifier then discarding the query list is equivalent to
running a non-oracle verifier -/
@[simp]
theorem OracleVerifier.run_eq_run_verifier [∀ i, ToOracle (pSpec.Message i)] {stmt : StmtIn}
    {transcript : Transcript pSpec} {verifier : OracleVerifier pSpec oSpec StmtIn StmtOut} :
      Prod.snd <$> verifier.run stmt transcript = verifier.toVerifier.run stmt transcript := by
  simp only [OracleVerifier.run, map_bind, map_pure, bind_pure,
    Verifier.run, OracleVerifier.toVerifier]

/--
  An execution of an interactive reduction on a given initial statement and witness.

  Returns the verifier's decision, the transcript, the log of prover's queries to `oSpec`,
  and the prover's final state
-/
def Reduction.run [∀ i, Sampleable (pSpec.Challenge i)] (stmt : StmtIn) (wit : WitIn)
    (reduction : Reduction pSpec oSpec StmtIn WitIn StmtOut WitOut PrvState) :
      OracleComp (oSpec ++ₒ challengeOracle pSpec)
        (Transcript pSpec × QueryLog oSpec × StmtOut × WitOut) := do
  let (transcript, queryLog, witOut) ← reduction.prover.run stmt wit
  let stmtOut ← liftComp (reduction.verifier.run stmt transcript)
  return (transcript, queryLog, stmtOut, witOut)

/-- Run an interactive oracle reduction

Returns the verifier's decision, the transcript, the log of all verifier's oracle queries
to the prover's messages, the log of all prover's queries to `oSpec`, and the prover's final state

Note: we put `ResponseList pSpec` first so that the rest can be `Prod.snd`, which
we will show is the same result as doing `Protocol.run`.
-/
def OracleReduction.run [∀ i, Sampleable (pSpec.Challenge i)] [∀ i, ToOracle (pSpec.Message i)]
    (stmt : StmtIn) (wit : WitIn)
    (reduction : OracleReduction pSpec oSpec StmtIn WitIn StmtOut WitOut PrvState) :
      OracleComp (oSpec ++ₒ challengeOracle pSpec)
        (ResponseList pSpec × Transcript pSpec × QueryLog oSpec × StmtOut × WitOut) := do
  let ⟨transcript, queryLog, witOut⟩ ← reduction.prover.run stmt wit
  let ⟨messageQueries, stmtOut⟩ ← liftComp (reduction.verifier.run stmt transcript)
  return (messageQueries, transcript, queryLog, stmtOut, witOut)

omit [DecidableEq ι] in
/-- Running an oracle verifier then discarding the query list is equivalent to
running a non-oracle verifier -/
@[simp]
theorem OracleReduction.run_eq_run_reduction [DecidableEq ι] [∀ i, Sampleable (pSpec.Challenge i)]
    [∀ i, ToOracle (pSpec.Message i)] {stmt : StmtIn} {wit : WitIn}
    {oracleReduction : OracleReduction pSpec oSpec StmtIn WitIn StmtOut WitOut PrvState} :
      Prod.snd <$> oracleReduction.run stmt wit = oracleReduction.toReduction.run stmt wit := by
  simp [OracleReduction.run, Reduction.run, OracleReduction.toReduction, OracleVerifier.run,
    Verifier.run, OracleVerifier.toVerifier, liftComp]

end Execution

section Classes

namespace ProtocolSpec

variable {n : ℕ}

/-- A protocol specification with the prover speaking first -/
class ProverFirst (pSpec : ProtocolSpec n) [NeZero n] where
  prover_first' : (pSpec 0).1 = .P_to_V

/-- A protocol specification with the verifier speaking last -/
class VerifierLast (pSpec : ProtocolSpec n) [NeZero n] where
  verifier_last' : (pSpec (n - 1)).1 = .V_to_P

@[simp]
theorem prover_first (pSpec : ProtocolSpec n) [NeZero n] [h : ProverFirst pSpec] :
    (pSpec 0).1 = .P_to_V := h.prover_first'

@[simp]
theorem verifier_last (pSpec : ProtocolSpec n) [NeZero n] [h : VerifierLast pSpec] :
    (pSpec (n - 1)).1 = .V_to_P := h.verifier_last'

@[simp]
theorem verifier_last_of_two (pSpec : ProtocolSpec 2) [VerifierLast pSpec] :
    pSpec.getDir 1 = .V_to_P := verifier_last pSpec

/-- A protocol specification with a single round of interaction consisting of two messages, with the
  prover speaking first and the verifier speaking last

This notation is currently somewhat ambiguous, given that there are other valid ways of defining a
"single-round" protocol, such as letting the verifier speaks first, letting the prover speaks
multiple times, etc. -/
class IsSingleRound (pSpec : ProtocolSpec 2) extends ProverFirst pSpec, VerifierLast pSpec

variable {pSpec : ProtocolSpec 2}

/-- The first message is the only message from the prover to the verifier -/
instance [IsSingleRound pSpec] : Unique (pSpec.MessageIndex) where
  default := ⟨0, by simp [pSpec.prover_first]⟩
  uniq := fun ⟨i, hi⟩ => by
    congr
    contrapose! hi
    have : i = 1 := by omega
    subst this
    simp only [verifier_last_of_two, ne_eq, reduceCtorEq, not_false_eq_true]

/-- The second message is the only challenge from the verifier to the prover -/
instance [IsSingleRound pSpec] : Unique (pSpec.ChallengeIndex) where
  default := ⟨1, by simp [pSpec.verifier_last]⟩
  uniq := fun ⟨i, hi⟩ => by
    congr
    contrapose! hi
    have : i = 0 := by omega
    subst this
    simp only [prover_first, ne_eq, reduceCtorEq, not_false_eq_true]

instance [IsSingleRound pSpec] [h : ToOracle (pSpec.Message default)] :
    (i : pSpec.MessageIndex) → ToOracle (pSpec.Message i) := fun i => by
  haveI : i = default := Unique.uniq _ i
  subst this
  exact h

instance [IsSingleRound pSpec] [h : Sampleable (pSpec.Challenge default)] :
    (i : pSpec.ChallengeIndex) → Sampleable (pSpec.Challenge i) := fun i => by
  haveI : i = default := Unique.uniq _ i
  subst this
  exact h

variable [∀ i, Sampleable (pSpec.Challenge i)] {ι : Type} [DecidableEq ι] {oSpec : OracleSpec ι}
    {StmtIn WitIn StmtOut WitOut PrvState : Type}

/-- Simplification of the prover's execution in a single-round, two-message protocol where the
  prover speaks first -/
theorem Prover.run_of_isSingleRound [IsSingleRound pSpec] (stmt : StmtIn) (wit : WitIn)
    (prover : Prover pSpec oSpec StmtIn WitIn StmtOut WitOut PrvState) :
      prover.run stmt wit = (do
        let state := prover.load stmt wit
        let ⟨⟨msg, state⟩, queryLog⟩ ← liftComp
          (simulate loggingOracle ∅ (prover.sendMessage default state))
        let challenge ← query (Sum.inr default) ()
        let state := prover.receiveChallenge default state challenge
        let transcript := Transcript.mk2 msg challenge
        return (transcript, queryLog, prover.output state)) := by
  simp only [Prover.run, Prover.runAux, Fin.reduceFinMk, Fin.val_two,
    Fin.val_zero, Fin.coe_castSucc, Fin.val_succ, getDir_apply, bind_pure_comp, getType_apply,
    Fin.induction_two, Fin.val_one, pure_bind, map_bind]
  split <;> rename_i hDir0
  · exfalso; simp only [prover_first, reduceCtorEq] at hDir0
  split <;> rename_i hDir1
  swap
  · exfalso; simp only [verifier_last_of_two, reduceCtorEq] at hDir1
  simp only [Functor.map_map, bind_map_left, default]
  congr; funext x; congr; funext y
  rw [← Transcript.mk2_eq_toFull_snoc_snoc _ _]

-- theorem Reduction.run_of_isSingleRound [IsSingleRound pSpec]
--     (reduction : Reduction pSpec oSpec StmtIn WitIn StmtOut WitOut PrvState)
--     (stmt : StmtIn) (wit : WitIn) :
--       reduction.run stmt wit = do
--         let state := reduction.prover.load stmt wit
--         let ⟨⟨msg, state⟩, queryLog⟩ ← liftComp (simulate loggingOracle ∅
--           (reduction.prover.sendMessage default state))
--         let challenge := reduction.prover.receiveChallenge default state
--         let stmtOut ← reduction.verifier.verify stmt transcript
--         return (transcript, queryLog, stmtOut, reduction.prover.output state) := by sorry

end ProtocolSpec

end Classes
