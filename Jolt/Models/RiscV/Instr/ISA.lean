/-
 Copyright 2023 RISC Zero, Inc.

 Licensed under the Apache License, Version 2.0 (the "License");
 you may not use this file except in compliance with the License.
 You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software
 distributed under the License is distributed on an "AS IS" BASIS,
 WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 See the License for the specific language governing permissions and
 limitations under the License.
-/

import RiscV.Instr.Types
import RiscV.Mach.Mem
import RiscV.Mach.Reg
import RiscV.Monad

namespace RiscV.Instr.ISA

open RiscV.Instr.Types
open RiscV.Mach.Mem
open RiscV.Mach.Reg
open RiscV.Monad

structure ISA where
  Mnemonic: Type
  all: Array Mnemonic
  toString: Mnemonic -> String
  encode_mnemonic (m: Mnemonic): EncMnemonic
  run [MonadMachine M] (m: Mnemonic) (args: EncMnemonic.Args (encode_mnemonic m)): M Unit

namespace ISA
  def serialize_mnemonic (isa: ISA) (m: isa.Mnemonic): UInt32
    := (isa.encode_mnemonic m).serialize_mnemonic

  def code_matches (isa: ISA) (m: isa.Mnemonic) (x: UInt32): Bool
    := let mask := (isa.encode_mnemonic m).mask_mnemonic
      x &&& mask == isa.serialize_mnemonic m

  def deserialize_mnemonic (isa: ISA) (x: UInt32): Option isa.Mnemonic
    := Id.run do
        for mnemonic in isa.all do
          if isa.code_matches mnemonic x then return (some mnemonic)
        pure none

  def EncArgs (isa: ISA) (m: isa.Mnemonic): Type
    := (isa.encode_mnemonic m).EncArgs

  @[always_inline, inline]
  def deserialize_args (isa: ISA) (m: isa.Mnemonic) (x: UInt32): isa.EncArgs m
    := (isa.encode_mnemonic m).deserialize_args x

  def Args (isa: ISA) (m: isa.Mnemonic): Type
    := (isa.encode_mnemonic m).Args

  instance : ToString (Args isa m) where
    toString x := EncMnemonic.Args.ToString.toString x

  @[always_inline, inline]
  def decode_args (isa: ISA) (m: isa.Mnemonic) (x: isa.EncArgs m): isa.Args m
    := EncMnemonic.decode_args x

  def decode_to_string (isa: ISA) (instr: UInt32): Option String
    := Id.run do
          match isa.deserialize_mnemonic instr with
            | none => pure none
            | some mnemonic
                => do let enc_args := isa.deserialize_args mnemonic instr
                      let args := isa.decode_args mnemonic enc_args
                      pure (some s!"{isa.toString mnemonic}  {args}")

  @[always_inline, inline]
  def step [MonadMachine M] (isa: ISA): M Unit
    := do let pc <- RegFile.get_word .PC
          let instr <- Mem.get_word pc.toNat
          match isa.deserialize_mnemonic instr with
            | none => throw (.InvalidInstruction pc.toNat instr.toNat)
            | some mnemonic
                => do RegFile.set_word .PC (pc + 4)
                      let enc_args := isa.deserialize_args mnemonic instr
                      let args := isa.decode_args mnemonic enc_args
                      isa.run mnemonic args
end ISA

end RiscV.Instr.ISA
