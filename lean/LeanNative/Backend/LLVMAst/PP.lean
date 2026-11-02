import LeanNative.Backend.LLVMAst.Syntax

namespace LeanNative.Backend.LLVMAst

open LeanNative.Backend.TargetIR

namespace PP

def ppInt (n : Nat) : String := TargetIR.ppInt n

def ppICmp : ICmpPred → String
  | .eq => "eq" | .ne => "ne" | .ult => "ult" | .ule => "ule" | .ugt => "ugt"
  | .uge => "uge" | .slt => "slt" | .sle => "sle" | .sgt => "sgt" | .sge => "sge"

def ppFCmp : FCmpPred → String
  | .oeq => "oeq" | .one => "one" | .olt => "olt" | .ole => "ole" | .ogt => "ogt" | .oge => "oge"
  | .ord => "ord" | .uno => "uno" | .ueq => "ueq" | .une => "une" | .ult => "ult" | .ule => "ule"
  | .ugt => "ugt" | .uge => "uge" | .true_ => "true" | .false_ => "false"

def ppFlags : OverflowFlags → String
  | .none => "" | .nsw => " nsw" | .nuw => " nuw" | .nswNuw => " nsw nuw"

def ppExact (exact : Bool) : String :=
  if exact then " exact" else ""

def ppVolatile (volatile : Bool) : String :=
  if volatile then " volatile" else ""

def ppOrdering : AtomicOrdering → String
  | .monotonic => "monotonic" | .acquire => "acquire" | .release => "release"
  | .acqRel => "acq_rel" | .seqCst => "seq_cst"

def ppRMW : AtomicRMWOp → String
  | .add => "add" | .sub => "sub" | .and_ => "and" | .or_ => "or" | .xor => "xor"
  | .nand => "nand" | .max => "max" | .min => "min" | .umax => "umax" | .umin => "umin" | .xchg => "xchg"

def ppCC : CallingConv → String
  | .ccc => "ccc" | .fastcc => "fastcc" | .coldcc => "coldcc"

def ppAttr : ParamAttr → String
  | .zeroext => "zeroext" | .signext => "signext" | .noalias => "noalias" | .noundef => "noundef"
  | .readonly => "readonly" | .writeonly => "writeonly" | .nocapture => "nocapture"

def ppLinkage : Linkage → String
  | .external => "" | .private_ => "private " | .internal => "internal " | .weakOdr => "weak_odr "

def hexDigit (n : Nat) : Char :=
  match n with
  | 0 => '0' | 1 => '1' | 2 => '2' | 3 => '3' | 4 => '4'
  | 5 => '5' | 6 => '6' | 7 => '7' | 8 => '8' | 9 => '9'
  | 10 => 'A' | 11 => 'B' | 12 => 'C' | 13 => 'D' | 14 => 'E'
  | _ => 'F'

def toHex16Aux : Nat → Nat → List Char → List Char
  | 0, _, acc => acc
  | k + 1, x, acc => toHex16Aux k (x / 16) (hexDigit (x % 16) :: acc)

def ppHex64 (u : UInt64) : String :=
  "0x" ++ String.ofList (toHex16Aux 16 u.toNat [])

def f32BitsToDoubleHexBits (b : BitVec 32) : UInt64 :=
  let raw := b.toNat
  let exp := (raw / 8388608) % 256
  let mant := raw % 8388608
  if exp == 255 && mant != 0 then
    let sign64 := if raw / 2147483648 == 1 then (1 : Nat) <<< 63 else 0
    let exp64 := (2047 : Nat) <<< 52
    let mant64 := mant <<< 29
    UInt64.ofNat (sign64 ||| exp64 ||| mant64)
  else
    (Float32.ofBits (UInt32.ofNat raw)).toFloat.toBits

def ppFloatHex (fw : FloatWidth) (b : BitVec fw.bits) : String :=
  match fw with
  | .f64 => ppHex64 b.toNat.toUInt64
  | .f32 => ppHex64 (f32BitsToDoubleHexBits b)

mutual
def typeChars : LLVMType → List Char
  | .void => ['v', 'o', 'i', 'd']
  | .int .i1 => ['i', '1']
  | .int .i8 => ['i', '8']
  | .int .i16 => ['i', '1', '6']
  | .int .i32 => ['i', '3', '2']
  | .int .i64 => ['i', '6', '4']
  | .int .i128 => ['i', '1', '2', '8']
  | .int .i256 => ['i', '2', '5', '6']
  | .int .i512 => ['i', '5', '1', '2']
  | .float .f32 => ['f', 'l', 'o', 'a', 't']
  | .float .f64 => ['d', 'o', 'u', 'b', 'l', 'e']
  | .ptr as_ =>
    if as_ == 0 then ['p', 't', 'r']
    else ['p', 't', 'r', ' ', 'a', 'd', 'd', 'r', 's', 'p', 'a', 'c', 'e', '('] ++ TargetIR.natDigits as_ ++ [')']
  | .structFields false .nil => ['{', ' ', '}']
  | .structFields true .nil => ['<', '{', ' ', '}', '>']
  | .structFields false (.cons h t) => ['{', ' '] ++ typeChars h ++ fieldsTailChars t ++ [' ', '}']
  | .structFields true (.cons h t) => ['<', '{', ' '] ++ typeChars h ++ fieldsTailChars t ++ [' ', '}', '>']
  | .array n et => ['['] ++ TargetIR.natDigits n ++ [' ', 'x', ' '] ++ typeChars et ++ [']']
  | .vec n et => ['<'] ++ TargetIR.natDigits n ++ [' ', 'x', ' '] ++ typeChars et ++ ['>']

def fieldsTailChars : LLVMTypeFields → List Char
  | .nil => []
  | .cons h t => [',', ' '] ++ typeChars h ++ fieldsTailChars t
end

def ppType (ty : LLVMType) : String :=
  String.ofList (typeChars ty)

mutual
def parseType : Nat → List Char → Option (LLVMType × List Char)
  | 0, _ => none
  | _ + 1, 'v' :: 'o' :: 'i' :: 'd' :: rest => some (.void, rest)
  | _ + 1, 'f' :: 'l' :: 'o' :: 'a' :: 't' :: rest => some (.float .f32, rest)
  | _ + 1, 'd' :: 'o' :: 'u' :: 'b' :: 'l' :: 'e' :: rest => some (.float .f64, rest)
  | _ + 1, 'i' :: '1' :: '2' :: '8' :: rest => some (.int .i128, rest)
  | _ + 1, 'i' :: '2' :: '5' :: '6' :: rest => some (.int .i256, rest)
  | _ + 1, 'i' :: '5' :: '1' :: '2' :: rest => some (.int .i512, rest)
  | _ + 1, 'i' :: '1' :: '6' :: rest => some (.int .i16, rest)
  | _ + 1, 'i' :: '3' :: '2' :: rest => some (.int .i32, rest)
  | _ + 1, 'i' :: '6' :: '4' :: rest => some (.int .i64, rest)
  | _ + 1, 'i' :: '8' :: rest => some (.int .i8, rest)
  | _ + 1, 'i' :: '1' :: rest => some (.int .i1, rest)
  | _ + 1, 'p' :: 't' :: 'r' :: ' ' :: 'a' :: 'd' :: 'd' :: 'r' :: 's' :: 'p' :: 'a' :: 'c' :: 'e' :: '(' :: cs =>
    match TargetIR.readDigits 0 cs with
    | (as_, ')' :: rest) => some (.ptr as_, rest)
    | _ => none
  | _ + 1, 'p' :: 't' :: 'r' :: rest => some (.ptr 0, rest)
  | _ + 1, '{' :: ' ' :: '}' :: rest => some (.structFields false .nil, rest)
  | _ + 1, '<' :: '{' :: ' ' :: '}' :: '>' :: rest => some (.structFields true .nil, rest)
  | fuel + 1, '{' :: ' ' :: cs =>
    match parseType fuel cs with
    | some (h, rest1) =>
      match parseFieldsTail fuel rest1 with
      | some (t, ' ' :: '}' :: rest2) => some (.structFields false (.cons h t), rest2)
      | _ => none
    | none => none
  | fuel + 1, '<' :: '{' :: ' ' :: cs =>
    match parseType fuel cs with
    | some (h, rest1) =>
      match parseFieldsTail fuel rest1 with
      | some (t, ' ' :: '}' :: '>' :: rest2) => some (.structFields true (.cons h t), rest2)
      | _ => none
    | none => none
  | fuel + 1, '[' :: cs =>
    match TargetIR.readDigits 0 cs with
    | (n, ' ' :: 'x' :: ' ' :: rest1) =>
      match parseType fuel rest1 with
      | some (et, ']' :: rest2) => some (.array n et, rest2)
      | _ => none
    | _ => none
  | fuel + 1, '<' :: cs =>
    match TargetIR.readDigits 0 cs with
    | (n, ' ' :: 'x' :: ' ' :: rest1) =>
      match parseType fuel rest1 with
      | some (et, '>' :: rest2) => some (.vec n et, rest2)
      | _ => none
    | _ => none
  | _ + 1, _ => none

def parseFieldsTail : Nat → List Char → Option (LLVMTypeFields × List Char)
  | 0, _ => none
  | fuel + 1, ',' :: ' ' :: cs =>
    match parseType fuel cs with
    | some (h, rest1) =>
      match parseFieldsTail fuel rest1 with
      | some (t, rest2) => some (.cons h t, rest2)
      | none => none
    | none => none
  | _ + 1, cs => some (.nil, cs)
end

mutual
def typeDepth : LLVMType → Nat
  | .void | .int _ | .float _ | .ptr _ => 1
  | .structFields _ fs => 1 + fieldsDepth fs
  | .array _ et => 1 + typeDepth et
  | .vec _ et => 1 + typeDepth et

def fieldsDepth : LLVMTypeFields → Nat
  | .nil => 1
  | .cons h t => 1 + Nat.max (typeDepth h) (fieldsDepth t)
end

inductive ValidTypeSuffix : List Char → Prop where
  | nil : ValidTypeSuffix []
  | comma (cs : List Char) : ValidTypeSuffix (',' :: cs)
  | closeBrace (cs : List Char) : ValidTypeSuffix (' ' :: '}' :: cs)
  | closeBracket (cs : List Char) : ValidTypeSuffix (']' :: cs)
  | closeAngle (cs : List Char) : ValidTypeSuffix ('>' :: cs)

inductive ValidTailSuffix : List Char → Prop where
  | closeBrace (cs : List Char) : ValidTailSuffix (' ' :: '}' :: cs)

def ppVal : Operand → String
  | .reg r => "%" ++ r
  | .global g => "@" ++ g
  | .constInt _ v => ppInt v.toNat
  | .constFloat fw v => ppFloatHex fw v
  | .constNull => "null"
  | .constUndef => "undef"
  | .constZero => "zeroinitializer"
  | .aggNil => ""
  | .aggCons h t => ppVal h ++ ", " ++ ppVal t
  | .poison => "poison"

def nthAggOperand : Operand → Nat → Operand
  | .aggCons h _, 0 => h
  | .aggCons _ t, k + 1 => nthAggOperand t k
  | _, _ => .poison

def structFieldTypesList : LLVMTypeFields → List LLVMType
  | .nil => []
  | .cons h t => h :: structFieldTypesList t

def ppBareValAux : Nat → LLVMType → Operand → String
  | 0, _, op => ppVal op
  | _ + 1, ty, .aggNil =>
    match ty with
    | .int _ => "0"
    | .float fw => ppFloatHex fw (BitVec.ofNat fw.bits 0)
    | .ptr _ => "null"
    | _ => "zeroinitializer"
  | _ + 1, ty, .constZero =>
    match ty with
    | .int _ => "0"
    | .float fw => ppFloatHex fw (BitVec.ofNat fw.bits 0)
    | .ptr _ => "null"
    | _ => "zeroinitializer"
  | fuel + 1, ty, op@(.aggCons _ _) =>
    match ty with
    | .vec n et =>
      "<" ++ String.intercalate ", " (repeatMapIdx n fun i =>
        ppType et ++ " " ++ ppBareValAux fuel et (nthAggOperand op i)) ++ ">"
    | .array n et =>
      "[" ++ String.intercalate ", " (repeatMapIdx n fun i =>
        ppType et ++ " " ++ ppBareValAux fuel et (nthAggOperand op i)) ++ "]"
    | .structFields packed fs =>
      let ftys := structFieldTypesList fs
      let inner := String.intercalate ", " (repeatMapIdx ftys.length fun i =>
        let fty := ftys.getD i .void
        ppType fty ++ " " ++ ppBareValAux fuel fty (nthAggOperand op i))
      if packed then "<{ " ++ inner ++ " }>" else "{ " ++ inner ++ " }"
    | _ => ppVal op
  | _ + 1, _, op => ppVal op

def ppBareVal (ty : LLVMType) (op : Operand) : String :=
  ppBareValAux (ty.sizeOfType + 1) ty op

def ppTypedOperand (ty : LLVMType) (op : Operand) : String :=
  ppType ty ++ " " ++ ppBareVal ty op

def ppAlign (align : Nat) : String :=
  if align != 0 && isPow2 align then ", align " ++ ppInt align else ""

def ppPtr (as_ : AddrSpace) : String :=
  ppType (.ptr as_)

def ppGEP (inbounds_ : Bool) (ty : LLVMType) (base : Operand) (idxs : List (IntWidth × Operand)) (as_ : AddrSpace) : String :=
  let ib := if inbounds_ then " inbounds" else ""
  let idxStr := String.join (idxs.map fun (w, op) => ", " ++ w.pp ++ " " ++ ppVal op)
  "getelementptr" ++ ib ++ " " ++ ppType ty ++ ", " ++ ppPtr as_ ++ " " ++ ppVal base ++ idxStr

def ppInstr : LLVMInstr → String
  | .alloca dst ty align =>
    "%" ++ dst ++ " = alloca " ++ ppType ty ++ ppAlign align
  | .load dst volatile ty ptrOp align as_ =>
    "%" ++ dst ++ " = load" ++ ppVolatile volatile ++ " " ++ ppType ty ++ ", " ++ ppPtr as_ ++ " " ++ ppVal ptrOp ++ ppAlign align
  | .store volatile ty valOp ptrOp align as_ =>
    "store" ++ ppVolatile volatile ++ " " ++ ppTypedOperand ty valOp ++ ", " ++ ppPtr as_ ++ " " ++ ppVal ptrOp ++ ppAlign align
  | .add dst flags w aOp bOp =>
    "%" ++ dst ++ " = add" ++ ppFlags flags ++ " " ++ w.pp ++ " " ++ ppVal aOp ++ ", " ++ ppVal bOp
  | .sub dst flags w aOp bOp =>
    "%" ++ dst ++ " = sub" ++ ppFlags flags ++ " " ++ w.pp ++ " " ++ ppVal aOp ++ ", " ++ ppVal bOp
  | .mul dst flags w aOp bOp =>
    "%" ++ dst ++ " = mul" ++ ppFlags flags ++ " " ++ w.pp ++ " " ++ ppVal aOp ++ ", " ++ ppVal bOp
  | .udiv dst exact w aOp bOp =>
    "%" ++ dst ++ " = udiv" ++ ppExact exact ++ " " ++ w.pp ++ " " ++ ppVal aOp ++ ", " ++ ppVal bOp
  | .sdiv dst exact w aOp bOp =>
    "%" ++ dst ++ " = sdiv" ++ ppExact exact ++ " " ++ w.pp ++ " " ++ ppVal aOp ++ ", " ++ ppVal bOp
  | .urem dst w aOp bOp =>
    "%" ++ dst ++ " = urem " ++ w.pp ++ " " ++ ppVal aOp ++ ", " ++ ppVal bOp
  | .srem dst w aOp bOp =>
    "%" ++ dst ++ " = srem " ++ w.pp ++ " " ++ ppVal aOp ++ ", " ++ ppVal bOp
  | .and_ dst w aOp bOp =>
    "%" ++ dst ++ " = and " ++ w.pp ++ " " ++ ppVal aOp ++ ", " ++ ppVal bOp
  | .or_ dst w aOp bOp =>
    "%" ++ dst ++ " = or " ++ w.pp ++ " " ++ ppVal aOp ++ ", " ++ ppVal bOp
  | .xor dst w aOp bOp =>
    "%" ++ dst ++ " = xor " ++ w.pp ++ " " ++ ppVal aOp ++ ", " ++ ppVal bOp
  | .shl dst flags w aOp bOp =>
    "%" ++ dst ++ " = shl" ++ ppFlags flags ++ " " ++ w.pp ++ " " ++ ppVal aOp ++ ", " ++ ppVal bOp
  | .lshr dst exact w aOp bOp =>
    "%" ++ dst ++ " = lshr" ++ ppExact exact ++ " " ++ w.pp ++ " " ++ ppVal aOp ++ ", " ++ ppVal bOp
  | .ashr dst exact w aOp bOp =>
    "%" ++ dst ++ " = ashr" ++ ppExact exact ++ " " ++ w.pp ++ " " ++ ppVal aOp ++ ", " ++ ppVal bOp
  | .icmp dst pred ty aOp bOp =>
    "%" ++ dst ++ " = icmp " ++ ppICmp pred ++ " " ++ ppType ty ++ " " ++ ppVal aOp ++ ", " ++ ppVal bOp
  | .fadd dst fw aOp bOp =>
    "%" ++ dst ++ " = fadd " ++ fw.pp ++ " " ++ ppVal aOp ++ ", " ++ ppVal bOp
  | .fsub dst fw aOp bOp =>
    "%" ++ dst ++ " = fsub " ++ fw.pp ++ " " ++ ppVal aOp ++ ", " ++ ppVal bOp
  | .fmul dst fw aOp bOp =>
    "%" ++ dst ++ " = fmul " ++ fw.pp ++ " " ++ ppVal aOp ++ ", " ++ ppVal bOp
  | .fdiv dst fw aOp bOp =>
    "%" ++ dst ++ " = fdiv " ++ fw.pp ++ " " ++ ppVal aOp ++ ", " ++ ppVal bOp
  | .fcmp dst pred fw aOp bOp =>
    "%" ++ dst ++ " = fcmp " ++ ppFCmp pred ++ " " ++ fw.pp ++ " " ++ ppVal aOp ++ ", " ++ ppVal bOp
  | .zext dst srcW op dstW =>
    "%" ++ dst ++ " = zext " ++ srcW.pp ++ " " ++ ppVal op ++ " to " ++ dstW.pp
  | .sext dst srcW op dstW =>
    "%" ++ dst ++ " = sext " ++ srcW.pp ++ " " ++ ppVal op ++ " to " ++ dstW.pp
  | .trunc dst srcW op dstW =>
    "%" ++ dst ++ " = trunc " ++ srcW.pp ++ " " ++ ppVal op ++ " to " ++ dstW.pp
  | .bitcast dst srcTy op dstTy =>
    "%" ++ dst ++ " = bitcast " ++ ppTypedOperand srcTy op ++ " to " ++ ppType dstTy
  | .inttoptr dst srcW op as_ =>
    "%" ++ dst ++ " = inttoptr " ++ srcW.pp ++ " " ++ ppVal op ++ " to " ++ ppType (.ptr as_)
  | .ptrtoint dst as_ op dstW =>
    "%" ++ dst ++ " = ptrtoint " ++ ppType (.ptr as_) ++ " " ++ ppVal op ++ " to " ++ dstW.pp
  | .getelementptr dst inbounds_ ty baseOp idxs as_ =>
    "%" ++ dst ++ " = " ++ ppGEP inbounds_ ty baseOp idxs as_
  | .select dst condOp ty tOp eOp =>
    "%" ++ dst ++ " = select i1 " ++ ppVal condOp ++ ", " ++ ppTypedOperand ty tOp ++ ", " ++ ppTypedOperand ty eOp
  | .call dst? retTy callee args cc =>
    let lhs := match dst? with | none => "" | some dst => "%" ++ dst ++ " = "
    let argStr := String.intercalate ", " (args.map fun (ty, op) => ppTypedOperand ty op)
    let ccStr := if cc == .ccc then "" else ppCC cc ++ " "
    lhs ++ "call " ++ ccStr ++ ppType retTy ++ " @" ++ callee ++ "(" ++ argStr ++ ")"
  | .atomicrmw dst op ptrOp ty valOp ord align as_ =>
    "%" ++ dst ++ " = atomicrmw " ++ ppRMW op ++ " " ++ ppPtr as_ ++ " " ++ ppVal ptrOp ++ ", " ++ ppTypedOperand ty valOp ++
      " " ++ ppOrdering ord ++ ppAlign align
  | .insertelement dst n et vecOp elemOp idxW idxOp =>
    "%" ++ dst ++ " = insertelement " ++ ppTypedOperand (.vec n et) vecOp ++ ", " ++
      ppTypedOperand et elemOp ++ ", " ++ idxW.pp ++ " " ++ ppVal idxOp
  | .extractelement dst n et vecOp idxW idxOp =>
    "%" ++ dst ++ " = extractelement " ++ ppTypedOperand (.vec n et) vecOp ++ ", " ++ idxW.pp ++ " " ++ ppVal idxOp
  | .shufflevector dst n m et aOp bOp mask =>
    let maskTy := "<" ++ ppInt mask.length ++ " x i32>"
    let maskVal := "<" ++ String.intercalate ", " (mask.map fun i => "i32 " ++ ppInt i) ++ ">"
    "%" ++ dst ++ " = shufflevector " ++ ppTypedOperand (.vec n et) aOp ++ ", " ++
      ppTypedOperand (.vec m et) bOp ++ ", " ++ maskTy ++ " " ++ maskVal
  | .insertvalue dst ty aggOp elemTy elemOp idxs =>
    "%" ++ dst ++ " = insertvalue " ++ ppTypedOperand ty aggOp ++ ", " ++ ppTypedOperand elemTy elemOp ++
      String.join (idxs.map fun i => ", " ++ ppInt i)
  | .extractvalue dst ty aggOp idxs =>
    "%" ++ dst ++ " = extractvalue " ++ ppTypedOperand ty aggOp ++ String.join (idxs.map fun i => ", " ++ ppInt i)

def ppTerm : Terminator → String
  | .br lbl => "br label %" ++ lbl
  | .condBr condOp tLbl eLbl =>
    "br i1 " ++ ppVal condOp ++ ", label %" ++ tLbl ++ ", label %" ++ eLbl
  | .switch w scrutOp defLbl cases =>
    let arms := String.intercalate "\n" (cases.map fun (k, lbl) =>
      "    " ++ w.pp ++ " " ++ ppInt k.toNat ++ ", label %" ++ lbl)
    "switch " ++ w.pp ++ " " ++ ppVal scrutOp ++ ", label %" ++ defLbl ++ " [\n" ++ arms ++ "\n  ]"
  | .ret none => "ret void"
  | .ret (some (ty, op)) => "ret " ++ ppTypedOperand ty op
  | .unreachable => "unreachable"

def ppPhi (p : PhiNode) : String :=
  let arms := String.intercalate ", " (p.incomings.map fun (op, lbl) => "[ " ++ ppBareVal p.ty op ++ ", %" ++ lbl ++ " ]")
  "%" ++ p.dst ++ " = phi " ++ ppType p.ty ++ " " ++ arms

def ppBlock (b : LLVMBlock) : String :=
  b.label ++ ":\n" ++ String.intercalate "\n"
    (b.phis.map (fun p => "  " ++ ppPhi p) ++ b.body.map (fun i => "  " ++ ppInstr i) ++ ["  " ++ ppTerm b.term])

def ppParam (p : LLVMParam) : String :=
  let attrs := if p.attrs.isEmpty then "" else " " ++ String.intercalate " " (p.attrs.map ppAttr)
  ppType p.ty ++ attrs ++ " %" ++ p.name

def ppFn (fn : LLVMFn) : String :=
  "define " ++ ppCC fn.cc ++ " " ++ ppType fn.retTy ++ " @" ++ fn.name ++ "(" ++
    String.intercalate ", " (fn.params.map ppParam) ++ ") {\n" ++
    String.intercalate "\n" (fn.blocks.map ppBlock) ++ "\n}"

def ppGlobal (g : LLVMGlobal) : String :=
  let kind := if g.isConstant then "constant " else "global "
  let link := if g.linkage == .external && g.init.isNone then "external " else ppLinkage g.linkage
  let body :=
    if g.linkage == .external && g.init.isNone then ppType g.ty
    else match g.init with
      | none => ppType g.ty ++ " zeroinitializer"
      | some op => ppTypedOperand g.ty op
  "@" ++ g.name ++ " = " ++ link ++ kind ++ body ++ ppAlign g.align

def ppExtern (e : LLVMExtern) : String :=
  "declare " ++ ppType e.retTy ++ " @" ++ e.name ++ "(" ++ String.intercalate ", " (e.paramTys.map ppType) ++ ")"

def ppModule (m : LLVMModule) : String :=
  String.intercalate "\n" ([
    "target datalayout = \"" ++ m.dataLayout ++ "\"",
    "target triple = \"" ++ m.triple ++ "\""
  ] ++ m.globals.map ppGlobal ++ m.externs.map ppExtern ++ m.fns.map ppFn)

end PP

end LeanNative.Backend.LLVMAst
