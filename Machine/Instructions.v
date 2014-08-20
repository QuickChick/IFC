(* Machine instructions *)

Require Import ZArith.
Require Import List. Import ListNotations.

Definition regId := Z.

Inductive BinOpT : Type :=
| BAdd
| BMult.

Definition eval_binop (b : BinOpT) : Z -> Z -> option Z :=
  match b with
    | BAdd => fun z1 z2 => Some (z1 + z2)%Z
    | BMult => fun z1 z2 => Some (z1 * z2)%Z
  end.

Inductive Instruction : Type :=
  | Lab      : regId -> regId -> Instruction
  | MLab     : regId -> regId -> Instruction
  | PcLab    : regId -> Instruction
  | BCall    : regId -> regId -> regId -> Instruction
  | BRet     : Instruction
  | FlowsTo  : regId -> regId -> regId -> Instruction
  | LJoin    : regId -> regId -> regId -> Instruction
  | PutBot   : regId -> Instruction
  | Nop      : Instruction
  | Put (n : Z) : regId -> Instruction
  | BinOp (o : BinOpT) : regId -> regId -> regId -> Instruction
  | Jump     : regId -> Instruction
  | BNZ (n : Z) : regId -> Instruction
  | Load     : regId -> regId -> Instruction
  | Store    : regId -> regId -> Instruction
  | Alloc    : regId -> regId -> regId -> Instruction
  | PSetOff  : regId -> regId -> regId -> Instruction
  | Output   : regId -> Instruction
  | Halt     : Instruction
  | PGetOff  : regId -> regId -> Instruction
  | MSize    : regId -> regId -> Instruction.

Inductive OpCode : Type :=
  | OpLab
  | OpMLab
  | OpPcLab
  | OpBCall
  | OpBRet
  | OpFlowsTo
  | OpLJoin
  | OpPutBot
  | OpNop
  | OpPut
  | OpBinOp
  | OpJump
  | OpBNZ
  | OpLoad
  | OpStore
  | OpAlloc
  | OpPSetOff
  | OpOutput
  | OpPGetOff
  | OpMSize.

Definition opCodes :=
  [ OpLab
  ; OpMLab
  ; OpPcLab
  ; OpBCall
  ; OpBRet
  ; OpFlowsTo
  ; OpLJoin
  ; OpPutBot
  ; OpNop
  ; OpPut
  ; OpBinOp
  ; OpJump
  ; OpBNZ
  ; OpLoad
  ; OpStore
  ; OpAlloc
  ; OpPSetOff
  ; OpOutput
  ; OpPGetOff
  ; OpMSize ].

Lemma opCodes_correct : forall o : OpCode, In o opCodes.
Proof. intro o; simpl; destruct o; tauto. Qed.

Definition opCode_eq_dec : forall o1 o2 : OpCode,
  {o1 = o2} + {o1 <> o2}.
Proof. decide equality. Defined.

Definition opcode_of_instr (i : Instruction) : option OpCode :=
  match i with
  | Lab _ _       => Some OpLab
  | MLab _ _      => Some OpMLab
  | PcLab _       => Some OpPcLab
  | BCall _ _ _   => Some OpBCall
  | BRet          => Some OpBRet
  | FlowsTo _ _ _ => Some OpFlowsTo
  | LJoin _ _ _   => Some OpLJoin
  | PutBot _      => Some OpPutBot
  | Nop           => Some OpNop
  | Put _ _       => Some OpPut
  | BinOp _ _ _ _ => Some OpBinOp
  | Jump _        => Some OpJump
  | BNZ _ _       => Some OpBNZ
  | Load _ _      => Some OpLoad
  | Store _ _     => Some OpStore
  | Alloc _ _ _   => Some OpAlloc
  | PSetOff _ _ _ => Some OpPSetOff
  | Output _      => Some OpOutput
  | PGetOff _ _   => Some OpPGetOff
  | MSize _ _     => Some OpMSize
  | _             => None (* CH: halt has no opcode? why? *)
end.
