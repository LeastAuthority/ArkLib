/-
Copyright (c) 2024 ZKLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ZKLib.Data.Math.Fin
import ZKLib.OracleReduction.Prelude
import ZKLib.OracleReduction.ToOracle
-- import Mathlib.Data.FinEnum

/-!
# Interactive (Oracle) Reductions

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

open OracleComp OracleSpec SubSpec

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
@[reducible]
def MessageIndex (pSpec : ProtocolSpec n) :=
  {i : Fin n // pSpec.getDir i = Direction.P_to_V}

/-- Subtype of `Fin n` for the indices corresponding to challenges in a protocol specification -/
@[reducible]
def ChallengeIndex (pSpec : ProtocolSpec n) :=
  {i : Fin n // pSpec.getDir i = Direction.V_to_P}

instance {pSpec : ProtocolSpec n} : CoeHead (MessageIndex pSpec) (Fin n) where
  coe := fun i => i.1
instance {pSpec : ProtocolSpec n} : CoeHead (ChallengeIndex pSpec) (Fin n) where
  coe := fun i => i.1

/-- The type of the `i`-th message in a protocol specification -/
@[reducible, inline, specialize]
def Message (pSpec : ProtocolSpec n) (i : MessageIndex pSpec) :=
  pSpec.getType i.val

/-- The type of the `i`-th challenge in a protocol specification -/
@[reducible, inline, specialize]
def Challenge (pSpec : ProtocolSpec n) (i : ChallengeIndex pSpec) :=
  pSpec.getType i.val

/-- There is only one protocol specification with 0 messages (the empty one) -/
instance : Unique (ProtocolSpec 0) := inferInstance

/-- A (partial) transcript of a protocol specification, indexed by some `k : Fin (n + 1)`, is a
    list of messages from the protocol for all indices `i` less than `k`. -/
@[reducible, inline, specialize]
def Transcript (k : Fin (n + 1)) (pSpec : ProtocolSpec n) :=
  (i : Fin k) → pSpec.getType (Fin.castLE (by omega) i)

instance {k : Fin 1} : Unique (Transcript k (default : ProtocolSpec 0)) where
  default := fun i => ()
  uniq := by solve_by_elim

instance {pSpec : ProtocolSpec n} : Unique (Transcript 0 pSpec) where
  default := fun i => Fin.elim0 i
  uniq := fun T => by ext i; exact Fin.elim0 i

/-- The full transcript of an interactive protocol, which is a list of messages and challenges -/
@[reducible, inline, specialize]
def FullTranscript (pSpec : ProtocolSpec n) := (i : Fin n) → pSpec.getType i

/-- There is only one full transcript (the empty one) for an empty protocol -/
instance : Unique (FullTranscript (default : ProtocolSpec 0)) := inferInstance

variable {pSpec : ProtocolSpec n}

-- instance instFinEnumMessageIndex : FinEnum pSpec.MessageIndex :=
--   FinEnum.Subtype.finEnum fun x ↦ pSpec.getDir x = Direction.P_to_V
-- instance instFinEnumChallengeIndex : FinEnum pSpec.ChallengeIndex :=
--   FinEnum.Subtype.finEnum fun x ↦ pSpec.getDir x = Direction.V_to_P

/-- Nicely, a transcript up to the last round of the protocol is definitionally equivalent to a full
    transcript. -/
@[inline]
abbrev Transcript.toFull (T : Transcript (Fin.last n) pSpec) : FullTranscript pSpec := T

/-- Add a message to the end of a partial transcript. This is definitionally equivalent to
    `Fin.snoc`. -/
@[inline]
abbrev Transcript.snoc {m : Fin n} (msg : pSpec.getType m)
    (T : Transcript m.castSucc pSpec) : Transcript m.succ pSpec := Fin.snoc T msg

@[reducible, inline, specialize]
def FullTranscript.messages (transcript : FullTranscript pSpec) (i : MessageIndex pSpec) :=
  transcript i.val

@[reducible, inline, specialize]
def FullTranscript.challenges (transcript : FullTranscript pSpec) (i : ChallengeIndex pSpec) :=
  transcript i.val

/-- Turn each verifier's challenge into an oracle, where querying a unit type gives back the
  challenge -/
@[reducible, inline, specialize]
instance instChallengeToOracle {pSpec : ProtocolSpec n} {i : pSpec.ChallengeIndex}
    [VCVCompatible (pSpec.Challenge i)] : ToOracle (pSpec.Challenge i) where
  Query := Unit
  Response := pSpec.Challenge i
  oracle := fun c _ => c
  query_decidableEq' := by simp only; infer_instance

-- /-- Turn each verifier's challenge into an oracle, where one needs to query
--   with an input statement
--   and a prior transcript to get a challenge (useful for Fiat-Shamir) -/
-- @[reducible, inline, specialize]
-- instance instChallengeToOracleFiatShamir {pSpec : ProtocolSpec n} {i : pSpec.ChallengeIndex}
--     {StmtIn : Type} [DecidableEq StmtIn] [h : ∀ j, DecidableEq (pSpec j).2]
--     [VCVCompatible (pSpec.Challenge i)] : ToOracle (pSpec.Challenge i) where
--   Query := StmtIn × Transcript i.1.castSucc pSpec
--   Response := pSpec.Challenge i
--   oracle := fun c _ => c
--   query_decidableEq' := by simp [Transcript]; infer_instance

end ProtocolSpec

open ProtocolSpec

-- Notation for the type signature of an interactive protocol
notation "𝒫——⟦" term "⟧⟶𝒱" => (Direction.P_to_V, term)
notation "𝒫⟵⟦" term "⟧——𝒱" => (Direction.V_to_P, term)

variable {ι : Type}

-- Add an indexer?
structure Indexer (pSpec : ProtocolSpec n) (oSpec : OracleSpec ι) (Index : Type)
    (Encoding : Type) where
  encode : Index → OracleComp oSpec Encoding
  [toOracle : ToOracle Encoding]

/-- The type signature for the prover's state at each round. For a protocol with `n` messages
  exchanged, there will be `(n + 1)` prover states, with the first state before the first message
  and the last state after the last message. -/
structure ProverState (n : ℕ) where
  PrvState : Fin (n + 1) → Type

/-- Initialization of prover's state via inputting the statement and witness -/
structure ProverIn (StmtIn WitIn PrvState : Type) where
  input : StmtIn → WitIn → PrvState

/-- Represents the interaction of a prover for a given protocol specification.

In each step, the prover gets access to the current state, then depending on the direction of the
step, the prover either sends a message or receives a challenge, and updates its state accordingly.

For maximum simplicity, we only define the `sendMessage` function as an oracle computation. All
other functions are pure. We may revisit this decision in the future.
-/
structure ProverRound (pSpec : ProtocolSpec n) (oSpec : OracleSpec ι)
    extends ProverState n where
  /-- Send a message and update the prover's state -/
  sendMessage (i : MessageIndex pSpec) :
    PrvState i.1.castSucc → OracleComp oSpec (pSpec.Message i × PrvState i.1.succ)
  /-- Receive a challenge and update the prover's state -/
  receiveChallenge (i : ChallengeIndex pSpec) :
    PrvState i.1.castSucc → (pSpec.Challenge i) → PrvState i.1.succ

/-- The output of the prover, which is a function from the prover's state to the output witness -/
structure ProverOut (StmtOut WitOut PrvState : Type) where
  output : PrvState → StmtOut × WitOut

/-- A prover for an interactive protocol with `n` messages consists of a sequence of internal states
    and a tuple of four functions:
  - `PrvState 0`, ..., `PrvState n` are the types for the prover's state at each round
  - `input` initializes the prover's state by taking in the input statement and witness
  - `receiveChallenge` updates the prover's state given a challenge
  - `sendMessage` sends a message and updates the prover's state
  - `output` returns the output statement and witness from the prover's state

Note that the output statement by the prover is present only to facilitate composing two provers
together. For security purposes, we will only use the output statement generated by the verifier. -/
structure Prover (pSpec : ProtocolSpec n) (oSpec : OracleSpec ι)
    (StmtIn WitIn StmtOut WitOut : Type) extends
      ProverState n,
      ProverIn StmtIn WitIn (PrvState 0),
      ProverRound pSpec oSpec,
      ProverOut StmtOut WitOut (PrvState (Fin.last n))

/-- A verifier of an interactive protocol is a function that takes in the input statement and the
  transcript, and performs an oracle computation that outputs a new statement -/
structure Verifier (pSpec : ProtocolSpec n) (oSpec : OracleSpec ι) (StmtIn StmtOut : Type) where
  verify : StmtIn → FullTranscript pSpec → OracleComp oSpec StmtOut

/-- A prover in an interactive **oracle** reduction is a prover in the non-oracle reduction whose
    input statement also consists of the underlying messages for the oracle statements -/
@[reducible, inline]
def OracleProver (pSpec : ProtocolSpec n) (oSpec : OracleSpec ι)
    (StmtIn WitIn StmtOut WitOut : Type)
    {ιₛᵢ : Type} (OStmtIn : ιₛᵢ → Type) {ιₛₒ : Type} (OStmtOut : ιₛₒ → Type) :=
  Prover pSpec oSpec (StmtIn × (∀ i, OStmtIn i)) WitIn (StmtOut × (∀ i, OStmtOut i)) WitOut

/--
A verifier of an interactive **oracle** reduction consists of:
  - an oracle computation `verify` that may make queries to each of the prover's messages and each
    of the oracles present in the statement (according to a specified interface defined by
    `ToOracle` instances).
  - output oracle statements `OStmtOut : ιₛₒ → Type`
  - an embedding `ιₛₒ ↪ ιₛᵢ ⊕ pSpec.MessageIndex`
  - a proof that the output oracle statements are a subset of the oracles present in the statement

The reason for the output indexing type & the embedding is that, since the verifier only gets oracle
access to the oracle statement & the prover's messages, its output oracle statements can only be a
subset of the oracles it has seen so far. -/
structure OracleVerifier (pSpec : ProtocolSpec n) (oSpec : OracleSpec ι)
    [Oₘ : ∀ i, ToOracle (pSpec.Message i)] (StmtIn StmtOut : Type)
    {ιₛᵢ : Type} (OStmtIn : ιₛᵢ → Type) [Oₛᵢ : ∀ i, ToOracle (OStmtIn i)]
    {ιₛₒ : Type} (OStmtOut : ιₛₒ → Type) where

  verify : StmtIn → (∀ i, pSpec.Challenge i) →
    OracleComp (oSpec ++ₒ ([OStmtIn]ₒ ++ₒ [pSpec.Message]ₒ)) StmtOut

  embed : ιₛₒ ↪ ιₛᵢ ⊕ pSpec.MessageIndex

  hEq : ∀ i, OStmtOut i = match embed i with
    | Sum.inl j => OStmtIn j
    | Sum.inr j => pSpec.Message j

-- Cannot find synthesization order...
-- instance {ιₛᵢ ιₘ ιₛₒ : Type} {OStmtIn : ιₛᵢ → Type} [Oₛᵢ : ∀ i, ToOracle (OStmtIn i)]
--     {Message : ιₘ → Type} [Oₘ : ∀ i, ToOracle (Message i)]
--     (OStmtOut : ιₛₒ → Type) (embed : ιₛₒ ↪ ιₛᵢ ⊕ ιₘ) :
--     ∀ i, OStmtOut i := fun i => by sorry

namespace OracleVerifier

variable {pSpec : ProtocolSpec n} {oSpec : OracleSpec ι}
    [Oₘ : ∀ i, ToOracle (pSpec.Message i)] {StmtIn StmtOut : Type}
    {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type} [Oₛᵢ : ∀ i, ToOracle (OStmtIn i)]
    {ιₛₒ : Type} {OStmtOut : ιₛₒ → Type}
    (verifier : OracleVerifier pSpec oSpec StmtIn StmtOut OStmtIn OStmtOut)

#check QueryLog

/-- The list of queries to the oracle statements and the transcript messages made by the verifier -/
def queries : QueryLog ([OStmtIn]ₒ ++ₒ [pSpec.Message]ₒ) := sorry

/-- An oracle verifier can be seen as a (non-oracle) verifier by providing the oracle interface
  using its knowledge of the oracle statements and the transcript messages in the clear -/
def toVerifier : Verifier pSpec oSpec (StmtIn × ∀ i, OStmtIn i) (StmtOut × (∀ i, OStmtOut i)) where
  verify := fun ⟨stmt, oStmt⟩ transcript => do
    let ⟨stmtOut, _⟩ ← simulate (routeOracles2 oSpec oStmt transcript.messages) ()
      (verifier.verify stmt transcript.challenges)
    letI oStmtOut := fun i => match h : verifier.embed i with
      | Sum.inl j => by simpa only [verifier.hEq, h] using (oStmt j)
      | Sum.inr j => by simpa only [verifier.hEq, h] using (transcript j)
    return (stmtOut, oStmtOut)

end OracleVerifier

/-- An (interactive) reduction for a given protocol specification `pSpec`, and relative to oracles
  defined by `oSpec`, consists of a prover and a verifier. -/
structure Reduction (pSpec : ProtocolSpec n) (oSpec : OracleSpec ι)
    (StmtIn WitIn StmtOut WitOut : Type) where
  prover : Prover pSpec oSpec StmtIn WitIn StmtOut WitOut
  verifier : Verifier pSpec oSpec StmtIn StmtOut

/-- An (interactive) oracle reduction for a given protocol specification `pSpec`, and relative to
  oracles defined by `oSpec`, consists of a prover and an **oracle** verifier. -/
structure OracleReduction (pSpec : ProtocolSpec n) [∀ i, ToOracle (pSpec.Message i)]
    (oSpec : OracleSpec ι) (StmtIn WitIn StmtOut WitOut : Type)
    {ιₛ : Type} (OStmtIn : ιₛ → Type) [Oₛ : ∀ i, ToOracle (OStmtIn i)]
    {ιₛₒ : Type} (OStmtOut : ιₛₒ → Type) where
  prover : OracleProver pSpec oSpec StmtIn WitIn StmtOut WitOut OStmtIn OStmtOut
  verifier : OracleVerifier pSpec oSpec StmtIn StmtOut OStmtIn OStmtOut

/-- An interactive oracle reduction can be seen as an interactive reduction, via coercing the
  oracle verifier to a (normal) verifier -/
def OracleReduction.toReduction {pSpec : ProtocolSpec n} {oSpec : OracleSpec ι}
    {StmtIn WitIn StmtOut WitOut : Type} [∀ i, ToOracle (pSpec.Message i)]
    {ιₛ : Type} {OStmtIn : ιₛ → Type} [Oₛ : ∀ i, ToOracle (OStmtIn i)]
    {ιₛₒ : Type} {OStmtOut : ιₛₒ → Type}
    (oracleReduction : OracleReduction pSpec oSpec StmtIn WitIn StmtOut WitOut OStmtIn OStmtOut) :
      Reduction pSpec oSpec (StmtIn × (∀ i, OStmtIn i)) WitIn
        (StmtOut × (∀ i, OStmtOut i)) WitOut :=
  ⟨oracleReduction.prover, oracleReduction.verifier.toVerifier⟩

/-- An **interactive proof (IP)** is an interactive reduction where the output statement is a
    boolean, the output witness is trivial (a `Unit`), and the relation checks whether the output
    statement is true. -/
abbrev Proof (pSpec : ProtocolSpec n) (oSpec : OracleSpec ι) (Statement Witness : Type) :=
  Reduction pSpec oSpec Statement Witness Bool Unit

/-- An **interactive oracle proof (IOP)** is an interactive oracle reduction where the output
    statement is a boolean, while both the output oracle statement & the output witness are
    trivial (`Unit` type).

    As a consequence, the output relation in an IOP is effectively a function `Bool → Prop`, which
    we can again assume to be the trivial one (sending `true` to `True`). -/
abbrev OracleProof (pSpec : ProtocolSpec n) (oSpec : OracleSpec ι)
    [Oₘ : ∀ i, ToOracle (pSpec.Message i)] (Statement Witness : Type)
    {ιₛ : Type} (OStatement : ιₛ → Type) [Oₛ : ∀ i, ToOracle (OStatement i)] :=
  OracleReduction pSpec oSpec Statement Witness Bool Unit OStatement (fun _ : Empty => Unit)

/-- A **non-interactive reduction** is an interactive reduction with only a single message from the
  prover to the verifier (and none in the other direction). -/
abbrev NonInteractiveReduction (oSpec : OracleSpec ι)
    (StmtIn WitIn StmtOut WitOut : Type) (Message : Type) :=
  Reduction ![(.P_to_V, Message)] oSpec StmtIn WitIn StmtOut WitOut

end Format

section Execution

open ProtocolSpec

variable {n : ℕ} {ι : Type} [DecidableEq ι] {pSpec : ProtocolSpec n} {oSpec : OracleSpec ι}
  {StmtIn WitIn StmtOut WitOut : Type}
  {ιₛᵢ : Type} [DecidableEq ιₛᵢ] {OStmtIn : ιₛᵢ → Type} [Oₛᵢ : ∀ i, ToOracle (OStmtIn i)]
  {ιₛₒ : Type} [DecidableEq ιₛₒ] {OStmtOut : ιₛₒ → Type}

/--
  Auxiliary function for running the prover in an interactive protocol. Given round index `i`,
  returns the transcript up to that round, the log of oracle queries made by the prover to `oSpec`
  up to that round, and the prover's state after that round.
-/
@[inline, specialize]
def Prover.runAux [∀ i, VCVCompatible (pSpec.Challenge i)] (stmt : StmtIn) (wit : WitIn)
    (i : Fin (n + 1)) (prover : Prover pSpec oSpec StmtIn WitIn StmtOut WitOut) :
      OracleComp (oSpec ++ₒ [pSpec.Challenge]ₒ)
        (pSpec.Transcript i × prover.PrvState i × QueryLog oSpec) :=
  Fin.induction
    (pure ⟨default, prover.input stmt wit, ∅⟩)
    (fun j ih => do
      let ⟨transcript, state, queryLog⟩ ← ih
      match hDir : pSpec.getDir j with
      | .V_to_P => do
        let challenge ← query (Sum.inr ⟨j, hDir⟩) ()
        letI challenge : pSpec.Challenge ⟨j, hDir⟩ := by simpa only
        let newState := prover.receiveChallenge ⟨j, hDir⟩ state challenge
        return ⟨transcript.snoc challenge, newState, queryLog⟩
      | .P_to_V => do
        let ⟨⟨msg, newState⟩, newQueryLog⟩ ← liftComp
          (simulate loggingOracle queryLog (prover.sendMessage ⟨j, hDir⟩ state))
        return ⟨transcript.snoc msg, newState, newQueryLog⟩)
    i

/--
  Run the prover in an interactive reduction. Returns the full transcript, the output statement and
  witness, and the log of oracle queries made by the prover.
-/
@[inline, specialize]
def Prover.run [∀ i, VCVCompatible (pSpec.Challenge i)] (stmt : StmtIn) (wit : WitIn)
    (prover : Prover pSpec oSpec StmtIn WitIn StmtOut WitOut) :
      OracleComp (oSpec ++ₒ [pSpec.Challenge]ₒ)
        (StmtOut × WitOut × FullTranscript pSpec × QueryLog oSpec) := do
  let ⟨transcript, state, queryLog⟩ ← prover.runAux stmt wit (Fin.last n)
  let ⟨stmtOut, witOut⟩ := prover.output state
  return ⟨stmtOut, witOut, transcript, queryLog⟩

/--
  Run the (non-oracle) verifier in an interactive reduction. It takes in the input statement and the
  transcript, and return the output statement along with the log of oracle queries made by the
  veirifer.
-/
@[inline, specialize]
def Verifier.run (stmt : StmtIn) (transcript : FullTranscript pSpec)
    (verifier : Verifier pSpec oSpec StmtIn StmtOut) :
      OracleComp oSpec (StmtOut × QueryLog oSpec) :=
  simulate loggingOracle ∅ (verifier.verify stmt transcript)

/-- Run the oracle verifier in the interactive protocol. Returns the verifier's output and the log
  of queries made by the verifier.
-/
@[inline, specialize]
def OracleVerifier.run [Oₘ : ∀ i, ToOracle (pSpec.Message i)]
    (stmt : StmtIn) (oStmtIn : ∀ i, OStmtIn i) (transcript : FullTranscript pSpec)
    (verifier : OracleVerifier pSpec oSpec StmtIn StmtOut OStmtIn OStmtOut) :
      OracleComp oSpec
        (StmtOut × QueryLog (oSpec ++ₒ ([OStmtIn]ₒ ++ₒ [pSpec.Message]ₒ))) := do
  let f := routeOracles2 oSpec oStmtIn transcript.messages
  let ⟨stmtOut, queryLog, _⟩ ← simulate (f ∘ₛₒ loggingOracle) ⟨∅, ()⟩
    (verifier.verify stmt transcript.challenges)
  return ⟨stmtOut, queryLog⟩

/-- Running an oracle verifier then discarding the query list is equivalent to
running a non-oracle verifier -/
@[simp]
theorem OracleVerifier.run_eq_run_verifier [∀ i, ToOracle (pSpec.Message i)] {stmt : StmtIn}
    {transcript : FullTranscript pSpec} {oStmt : ∀ i, OStmtIn i}
    {verifier : OracleVerifier pSpec oSpec StmtIn StmtOut OStmtIn OStmtOut} :
      Prod.fst <$> verifier.run stmt oStmt transcript =
        Prod.fst <$> Prod.fst <$> verifier.toVerifier.run ⟨stmt, oStmt⟩ transcript := by
  simp [OracleVerifier.run, Verifier.run, map_bind, map_pure, bind_pure,
    OracleVerifier.toVerifier, simulate_eq_map_simulate', routeOracles2]
  sorry

/--
  An execution of an interactive reduction on a given initial statement and witness.

  Returns the log of the prover's and the verifier's oracle queries, the full transcript, and the
  output statement and witness
-/
@[inline, specialize]
def Reduction.run [∀ i, VCVCompatible (pSpec.Challenge i)] (stmt : StmtIn) (wit : WitIn)
    (reduction : Reduction pSpec oSpec StmtIn WitIn StmtOut WitOut) :
      OracleComp (oSpec ++ₒ [pSpec.Challenge]ₒ)
        (StmtOut × WitOut × FullTranscript pSpec × QueryLog oSpec × QueryLog oSpec) := do
  let (_, witOut, transcript, proveQueryLog) ← reduction.prover.run stmt wit
  let ⟨stmtOut, verifyQueryLog⟩ ← liftComp (reduction.verifier.run stmt transcript)
  return (stmtOut, witOut, transcript, proveQueryLog, verifyQueryLog)

/-- Run an interactive oracle reduction. Returns the full transcript, the output statement and
  witness, the log of all prover's oracle queries, and the log of all verifier's oracle queries to
  the prover's messages and to the shared oracle.
-/
@[inline, specialize]
def OracleReduction.run [∀ i, VCVCompatible (pSpec.Challenge i)] [∀ i, ToOracle (pSpec.Message i)]
    (stmt : StmtIn) (wit : WitIn) (oStmt : ∀ i, OStmtIn i)
    (reduction : OracleReduction pSpec oSpec StmtIn WitIn StmtOut WitOut OStmtIn OStmtOut) :
      OracleComp (oSpec ++ₒ [pSpec.Challenge]ₒ)
        (StmtOut × WitOut × FullTranscript pSpec ×
          QueryLog oSpec × QueryLog (oSpec ++ₒ ([OStmtIn]ₒ ++ₒ [pSpec.Message]ₒ))) := do
  let ⟨_, witOut, transcript, proveQueryLog⟩ ← reduction.prover.run ⟨stmt, oStmt⟩ wit
  let ⟨stmtOut, verifyQueryLog⟩ ← liftComp (reduction.verifier.run stmt oStmt transcript)
  return (stmtOut, witOut, transcript, proveQueryLog, verifyQueryLog)

-- /-- Running an oracle verifier then discarding the query list is equivalent to
-- running a non-oracle verifier -/
-- @[simp]
-- theorem OracleReduction.run_eq_run_reduction [DecidableEq ι]
--     [∀ i, VCVCompatible (pSpec.Challenge i)]
--     [∀ i, ToOracle (pSpec.Message i)] {stmt : StmtIn} {wit : WitIn}
--     {oracleReduction : OracleReduction pSpec oSpec StmtIn WitIn StmtOut WitOut OStmt} :
--       Prod.snd <$> oracleReduction.run stmt wit = oracleReduction.toReduction.run stmt wit := by
--   simp [OracleReduction.run, Reduction.run, OracleReduction.toReduction, OracleVerifier.run,
--     Verifier.run, OracleVerifier.toVerifier, liftComp]

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

/-- A non-interactive protocol specification with a single message from the prover to the verifier-/
class NonInteractive (pSpec : ProtocolSpec 1) extends ProverFirst pSpec

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

instance [IsSingleRound pSpec] [h : VCVCompatible (pSpec.Challenge default)] :
    (i : pSpec.ChallengeIndex) → VCVCompatible (pSpec.Challenge i) := fun i => by
  haveI : i = default := Unique.uniq _ i
  subst this
  exact h

@[inline, reducible]
def FullTranscript.mk2 {pSpec : ProtocolSpec 2} (msg0 : pSpec.getType 0) (msg1 : pSpec.getType 1) :
    FullTranscript pSpec := fun | ⟨0, _⟩ => msg0 | ⟨1, _⟩ => msg1

theorem FullTranscript.mk2_eq_snoc_snoc {pSpec : ProtocolSpec 2} (msg0 : pSpec.getType 0)
    (msg1 : pSpec.getType 1) : FullTranscript.mk2 msg0 msg1 =
      ((default : pSpec.Transcript 0).snoc msg0).snoc msg1 := by
  unfold FullTranscript.mk2 Transcript.snoc
  simp only [default, getType_apply, Nat.mod_succ, Nat.lt_one_iff,
    not_lt_zero', ↓reduceDIte, Fin.zero_eta, Fin.isValue, Nat.reduceMod, Nat.succ_eq_add_one,
    Nat.reduceAdd, Fin.mk_one]
  funext i
  by_cases hi : i = 0
  · subst hi; simp [Fin.snoc]
  · have : i = 1 := by omega
    subst this; simp [Fin.snoc]

variable [∀ i, VCVCompatible (pSpec.Challenge i)] {ι : Type} [DecidableEq ι] {oSpec : OracleSpec ι}
    {StmtIn WitIn StmtOut WitOut : Type}

-- /-- Simplification of the prover's execution in a single-round, two-message protocol where the
--   prover speaks first -/
-- theorem Prover.run_of_isSingleRound [IsSingleRound pSpec] (stmt : StmtIn) (wit : WitIn)
--     (prover : Prover pSpec oSpec StmtIn WitIn StmtOut WitOut) :
--       prover.run stmt wit = (do
--         let state ← liftComp (prover.load stmt wit)
--         let ⟨⟨msg, state⟩, queryLog⟩ ← liftComp
--           (simulate loggingOracle ∅ (prover.sendMessage default state emptyTranscript))
--         let challenge ← query (Sum.inr default) ()
--         let state ← liftComp (prover.receiveChallenge default state transcript challenge)
--         let transcript := Transcript.mk2 msg challenge
--         let witOut := prover.output state
--         return (transcript, queryLog, witOut)) := by
--   simp [Prover.run, Prover.runAux, Fin.reduceFinMk, Fin.val_two,
--     Fin.val_zero, Fin.coe_castSucc, Fin.val_succ, getDir_apply, bind_pure_comp, getType_apply,
--     Fin.induction_two, Fin.val_one, pure_bind, map_bind, liftComp]
--   split <;> rename_i hDir0
--   · exfalso; simp only [prover_first, reduceCtorEq] at hDir0
--   split <;> rename_i hDir1
--   swap
--   · exfalso; simp only [verifier_last_of_two, reduceCtorEq] at hDir1
--   simp only [Functor.map_map, bind_map_left, default]
--   congr; funext x; congr; funext y;
--   simp only [Fin.isValue, map_bind, Functor.map_map, getDir_apply, Fin.succ_one_eq_two,
--     Fin.succ_zero_eq_one, queryBind_inj', true_and, exists_const]
--   funext chal; simp [OracleSpec.append] at chal
--   congr; funext state; congr
--   rw [← Transcript.mk2_eq_toFull_snoc_snoc _ _]

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
