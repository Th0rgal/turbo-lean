import LeanNative.IR.Types

namespace LeanNative.Backend.StableHLOAst

open LeanNative.IR

/-- Element types carried by a StableHLO tensor. `bf16` is stored as `UInt16` bits. -/
inductive ElemType where
  | i1 | i8 | i16 | i32 | i64
  | ui8 | ui16 | ui32 | ui64
  | f32 | f64 | bf16
  deriving DecidableEq, Repr, Inhabited, BEq

/-- Ranked tensor type: static shape plus element type. -/
structure TensorType where
  shape : List Nat
  elem  : ElemType
  deriving DecidableEq, Repr, Inhabited, BEq

/-- Product of the shape dimensions. The empty shape is a scalar (`1`). -/
def TensorType.numElements (ty : TensorType) : Nat :=
  ty.shape.foldl (· * ·) 1

/-- Comparison directions used by `stablehlo.compare`. -/
inductive CompareDir where
  | eq | ne | lt | le | gt | ge
  deriving DecidableEq, Repr, Inhabited, BEq

/-- A typed, flat, row-major tensor buffer. Well-formed values satisfy `data.size = ty.numElements`. -/
structure TensorVal where
  ty   : TensorType
  data : Array (BitVec 64)
  deriving DecidableEq, Repr, Inhabited

def TensorVal.wellFormed (t : TensorVal) : Prop :=
  t.data.size = t.ty.numElements

/-- StableHLO operations used by the typed AST. Operands are SSA names. -/
inductive StableHLOOp where
  | constant (dst : String) (value : TensorVal)
  | add (dst lhs rhs : String)
  | subtract (dst lhs rhs : String)
  | multiply (dst lhs rhs : String)
  | divide (dst lhs rhs : String)
  | remainder (dst lhs rhs : String)
  | maximum (dst lhs rhs : String)
  | minimum (dst lhs rhs : String)
  | and (dst lhs rhs : String)
  | or (dst lhs rhs : String)
  | xor (dst lhs rhs : String)
  | shiftLeft (dst lhs rhs : String)
  | shiftRightArithmetic (dst lhs rhs : String)
  | shiftRightLogical (dst lhs rhs : String)
  | compare (dst lhs rhs : String) (dir : CompareDir)
  | select (dst pred onTrue onFalse : String)
  | broadcastInDim (dst src : String) (outShape : List Nat) (dims : List Nat)
  | reshape (dst src : String) (outShape : List Nat)
  | slice (dst src : String) (starts limits strides : List Nat)
  | dynamicSlice (dst src : String) (startIndices : List String) (sliceSizes : List Nat)
  | dotGeneral (dst lhs rhs : String) (lhsContract rhsContract : List Nat) (outShape : List Nat)
  | reduce (dst src init : String) (dims : List Nat) (body : String)
  | convert (dst src : String) (outElem : ElemType)
  | returnOp (src : String)
  deriving DecidableEq, Repr, Inhabited

/-- A StableHLO function: named parameters, a result type, and a straight-line body. -/
structure FuncOp where
  name    : String
  params  : List (String × TensorType)
  result  : TensorType
  body    : List StableHLOOp
  deriving DecidableEq, Repr, Inhabited

/-- A StableHLO module. -/
structure ModuleOp where
  name  : String
  funcs : List FuncOp
  deriving DecidableEq, Repr, Inhabited

/-- Shape or type mismatch reported by the independent interpreter. -/
inductive ShapeError where
  | unbound (name : String)
  | typeMismatch (expected got : TensorType)
  | shapeMismatch (detail : String)
  | rankMismatch (expected got : Nat)
  | volumeMismatch (expected got : Nat)
  | divisionByZero
  deriving DecidableEq, Repr, Inhabited, BEq

abbrev Env := String → Option TensorVal

def Env.empty : Env := fun _ => none

def Env.bind (env : Env) (name : String) (v : TensorVal) : Env :=
  fun n => if n == name then some v else env n

def ppElemType : ElemType → String
  | .i1 => "i1" | .i8 => "i8" | .i16 => "i16" | .i32 => "i32" | .i64 => "i64"
  | .ui8 => "ui8" | .ui16 => "ui16" | .ui32 => "ui32" | .ui64 => "ui64"
  | .f32 => "f32" | .f64 => "f64" | .bf16 => "bf16"

def ppShape (shape : List Nat) : String :=
  String.intercalate "x" (shape.map toString)

def ppTensorType (ty : TensorType) : String :=
  let dims := if ty.shape.isEmpty then "" else ppShape ty.shape ++ "x"
  s!"tensor<{dims}{ppElemType ty.elem}>"

def ppCompareDir : CompareDir → String
  | .eq => "EQ" | .ne => "NE" | .lt => "LT" | .le => "LE" | .gt => "GT" | .ge => "GE"

def ppNatList (xs : List Nat) : String :=
  "[" ++ String.intercalate ", " (xs.map toString) ++ "]"

def ppStrList (xs : List String) : String :=
  "[" ++ String.intercalate ", " (xs.map fun s => s!"%{s}") ++ "]"

def ppBit (x : BitVec 64) : String := toString x.toNat

def ppDense (data : Array (BitVec 64)) : String :=
  if data.size == 0 then "dense<>"
  else if data.all (· == data[0]!) then s!"dense<{ppBit data[0]!}>"
  else "dense<[" ++ String.intercalate ", " (data.toList.map ppBit) ++ "]>"

/-- 1:1 structural pretty-printer for one StableHLO operation. -/
def ppStableHLOOp (op : StableHLOOp) : String :=
  match op with
  | .constant dst v =>
    s!"%{dst} = stablehlo.constant {ppDense v.data} : {ppTensorType v.ty}"
  | .add d a b => s!"%{d} = stablehlo.add %{a}, %{b}"
  | .subtract d a b => s!"%{d} = stablehlo.subtract %{a}, %{b}"
  | .multiply d a b => s!"%{d} = stablehlo.multiply %{a}, %{b}"
  | .divide d a b => s!"%{d} = stablehlo.divide %{a}, %{b}"
  | .remainder d a b => s!"%{d} = stablehlo.remainder %{a}, %{b}"
  | .maximum d a b => s!"%{d} = stablehlo.maximum %{a}, %{b}"
  | .minimum d a b => s!"%{d} = stablehlo.minimum %{a}, %{b}"
  | .and d a b => s!"%{d} = stablehlo.and %{a}, %{b}"
  | .or d a b => s!"%{d} = stablehlo.or %{a}, %{b}"
  | .xor d a b => s!"%{d} = stablehlo.xor %{a}, %{b}"
  | .shiftLeft d a b => s!"%{d} = stablehlo.shift_left %{a}, %{b}"
  | .shiftRightArithmetic d a b => s!"%{d} = stablehlo.shift_right_arithmetic %{a}, %{b}"
  | .shiftRightLogical d a b => s!"%{d} = stablehlo.shift_right_logical %{a}, %{b}"
  | .compare d a b dir => s!"%{d} = stablehlo.compare {ppCompareDir dir}, %{a}, %{b}"
  | .select d p t e => s!"%{d} = stablehlo.select %{p}, %{t}, %{e}"
  | .broadcastInDim d s shape dims =>
    s!"%{d} = stablehlo.broadcast_in_dim %{s}, dims = {ppNatList dims} : {ppShape shape}"
  | .reshape d s shape => s!"%{d} = stablehlo.reshape %{s} : {ppShape shape}"
  | .slice d s starts limits strides =>
    s!"%{d} = stablehlo.slice %{s} {ppNatList starts} {ppNatList limits} {ppNatList strides}"
  | .dynamicSlice d s idxs sizes =>
    s!"%{d} = stablehlo.dynamic_slice %{s}, {ppStrList idxs}, {ppNatList sizes}"
  | .dotGeneral d a b lc rc shape =>
    s!"%{d} = stablehlo.dot_general %{a}, %{b}, contracting_dims = {ppNatList lc} x {ppNatList rc} : {ppShape shape}"
  | .reduce d s i dims body =>
    s!"%{d} = stablehlo.reduce %{s}, %{i}, dims = {ppNatList dims}, body = @{body}"
  | .convert d s e => s!"%{d} = stablehlo.convert %{s} : {ppElemType e}"
  | .returnOp s => s!"return %{s}"

def ppFuncOp (f : FuncOp) : String :=
  let params := String.intercalate ", " (f.params.map fun (n, ty) => s!"%{n}: {ppTensorType ty}")
  let body := String.intercalate "\n" (f.body.map fun op => "    " ++ ppStableHLOOp op)
  s!"  func.func @{f.name}({params}) -> {ppTensorType f.result} \{\n{body}\n  }"

def ppModuleOp (m : ModuleOp) : String :=
  let funcs := String.intercalate "\n\n" (m.funcs.map ppFuncOp)
  s!"module @{m.name} \{\n{funcs}\n}"

/-- Width used by integer element arithmetic. Floating types are not integer-evaluated. -/
def elemWidth? : ElemType → Option Nat
  | .i1 => some 1 | .i8 | .ui8 => some 8 | .i16 | .ui16 | .bf16 => some 16
  | .i32 | .ui32 | .f32 => some 32 | .i64 | .ui64 | .f64 => some 64

def isSigned : ElemType → Bool
  | .i1 | .i8 | .i16 | .i32 | .i64 => true
  | _ => false

def isFloat : ElemType → Bool
  | .f32 | .f64 | .bf16 => true
  | _ => false

def maskWidth (w : Nat) (x : BitVec 64) : BitVec 64 :=
  if w ≥ 64 then x else BitVec.ofNat 64 (x.toNat % 2 ^ w)

def zipWithListM {α β γ : Type} (f : α → β → Except ShapeError γ) :
    List α → List β → Except ShapeError (List γ)
  | [], [] => .ok []
  | x :: xs, y :: ys => do
    let z ← f x y
    let zs ← zipWithListM f xs ys
    .ok (z :: zs)
  | xs, ys => .error (.volumeMismatch xs.length ys.length)

def zipWithM (f : BitVec 64 → BitVec 64 → Except ShapeError (BitVec 64))
    (a b : Array (BitVec 64)) : Except ShapeError (Array (BitVec 64)) := do
  if a.size = b.size then
    let out ← zipWithListM f a.toList b.toList
    .ok out.toArray
  else .error (.volumeMismatch a.size b.size)

def mapArr (f : BitVec 64 → BitVec 64) (a : Array (BitVec 64)) : Array (BitVec 64) :=
  a.map f

def binSame (env : Env) (dst lhs rhs : String)
    (f : ElemType → BitVec 64 → BitVec 64 → Except ShapeError (BitVec 64)) :
    Except ShapeError Env := do
  let some a := env lhs | .error (.unbound lhs)
  let some b := env rhs | .error (.unbound rhs)
  if a.ty = b.ty then
    let data ← zipWithM (f a.ty.elem) a.data b.data
    .ok (env.bind dst { ty := a.ty, data := data })
  else .error (.typeMismatch a.ty b.ty)

def elemBin (elem : ElemType) (op : BitVec 64 → BitVec 64 → BitVec 64)
    (x y : BitVec 64) : Except ShapeError (BitVec 64) :=
  match elemWidth? elem with
  | none => .error (.shapeMismatch "no integer width")
  | some w =>
    if isFloat elem then .error (.shapeMismatch "float binop is not an integer op")
    else .ok (maskWidth w (op (maskWidth w x) (maskWidth w y)))

def unsignedLt (w : Nat) (x y : BitVec 64) : Bool :=
  (maskWidth w x).toNat < (maskWidth w y).toNat

def zipWithTotal (f : BitVec 64 → BitVec 64 → BitVec 64) (a b : Array (BitVec 64)) :
    Array (BitVec 64) :=
  (a.toList.zip b.toList).map (fun (x, y) => f x y) |>.toArray

def addAt (w : Nat) (p q : BitVec 64) : BitVec 64 :=
  maskWidth w (maskWidth w p + maskWidth w q)

def evalAdd (env : Env) (d a b : String) : Except ShapeError Env := do
  let some x := env a | .error (.unbound a)
  let some y := env b | .error (.unbound b)
  if x.ty = y.ty then
    if isFloat x.ty.elem then .error (.shapeMismatch "float binop is not an integer op")
    else
      match elemWidth? x.ty.elem with
      | none => .error (.shapeMismatch "no integer width")
      | some w =>
        if x.data.size = y.data.size then
          let data := zipWithTotal (addAt w) x.data y.data
          .ok (env.bind d { ty := x.ty, data := data })
        else .error (.volumeMismatch x.data.size y.data.size)
  else .error (.typeMismatch x.ty y.ty)

def evalSub (env : Env) (d a b : String) : Except ShapeError Env :=
  binSame env d a b (fun e x y => elemBin e (· - ·) x y)

def evalMul (env : Env) (d a b : String) : Except ShapeError Env :=
  binSame env d a b (fun e x y => elemBin e (· * ·) x y)

def evalDiv (env : Env) (d a b : String) : Except ShapeError Env :=
  binSame env d a b fun e x y =>
    match elemWidth? e with
    | none => .error (.shapeMismatch "no integer width")
    | some w =>
      let y' := maskWidth w y
      if y' == 0#64 then .error .divisionByZero
      else .ok (maskWidth w ((maskWidth w x).udiv y'))

def evalRem (env : Env) (d a b : String) : Except ShapeError Env :=
  binSame env d a b fun e x y =>
    match elemWidth? e with
    | none => .error (.shapeMismatch "no integer width")
    | some w =>
      let y' := maskWidth w y
      if y' == 0#64 then .error .divisionByZero
      else .ok (maskWidth w ((maskWidth w x) % y'))

def evalMax (env : Env) (d a b : String) : Except ShapeError Env :=
  binSame env d a b fun e x y =>
    match elemWidth? e with
    | none => .error (.shapeMismatch "no integer width")
    | some w =>
      let x' := maskWidth w x
      let y' := maskWidth w y
      .ok (if unsignedLt w x' y' then y' else x')

def evalMin (env : Env) (d a b : String) : Except ShapeError Env :=
  binSame env d a b fun e x y =>
    match elemWidth? e with
    | none => .error (.shapeMismatch "no integer width")
    | some w =>
      let x' := maskWidth w x
      let y' := maskWidth w y
      .ok (if unsignedLt w x' y' then x' else y')

def evalAnd (env : Env) (d a b : String) : Except ShapeError Env :=
  binSame env d a b (fun e x y => elemBin e (· &&& ·) x y)

def evalOr (env : Env) (d a b : String) : Except ShapeError Env :=
  binSame env d a b (fun e x y => elemBin e (· ||| ·) x y)

def evalXor (env : Env) (d a b : String) : Except ShapeError Env :=
  binSame env d a b (fun e x y => elemBin e (· ^^^ ·) x y)

def evalShl (env : Env) (d a b : String) : Except ShapeError Env :=
  binSame env d a b fun e x y =>
    match elemWidth? e with
    | none => .error (.shapeMismatch "no integer width")
    | some w => .ok (maskWidth w ((maskWidth w x) <<< (maskWidth w y).toNat))

def evalShrL (env : Env) (d a b : String) : Except ShapeError Env :=
  binSame env d a b fun e x y =>
    match elemWidth? e with
    | none => .error (.shapeMismatch "no integer width")
    | some w => .ok (maskWidth w ((maskWidth w x) >>> (maskWidth w y).toNat))

/-- Arithmetic right shift at element width `w`, sign-extending into the low `w` bits. -/
def ashrWidth (w : Nat) (x amt : BitVec 64) : BitVec 64 :=
  let x' := maskWidth w x
  if w == 0 || w ≥ 64 then x' >>> amt.toNat
  else
    let sh := min amt.toNat (w - 1)
    let shifted := x' >>> sh
    let sign := (x' >>> (w - 1)) &&& 1#64
    if sign == 0#64 then maskWidth w shifted
    else
      let fill := if sh == 0 then 0#64 else ((1#64 <<< sh) - 1#64) <<< (w - sh)
      maskWidth w (shifted ||| fill)

def evalShrA (env : Env) (d a b : String) : Except ShapeError Env :=
  binSame env d a b fun e x y =>
    match elemWidth? e with
    | none => .error (.shapeMismatch "no integer width")
    | some w =>
      if isFloat e then .error (.shapeMismatch "float binop is not an integer op")
      else .ok (ashrWidth w x (maskWidth w y))

def evalCompare (env : Env) (d a b : String) (dir : CompareDir) : Except ShapeError Env := do
  let some aV := env a | .error (.unbound a)
  let some bV := env b | .error (.unbound b)
  if aV.ty != bV.ty then .error (.typeMismatch aV.ty bV.ty)
  else
    let data ← zipWithM (fun x y =>
      match elemWidth? aV.ty.elem with
      | none => .error (.shapeMismatch "no integer width")
      | some w =>
        let x' := maskWidth w x
        let y' := maskWidth w y
        let bit : Bool := match dir with
          | .eq => x' == y'
          | .ne => x' != y'
          | .lt => unsignedLt w x' y'
          | .le => unsignedLt w x' y' || x' == y'
          | .gt => unsignedLt w y' x'
          | .ge => unsignedLt w y' x' || x' == y'
        .ok (if bit then 1#64 else 0#64)) aV.data bV.data
    .ok (env.bind d { ty := { shape := aV.ty.shape, elem := .i1 }, data := data })

def evalSelect (env : Env) (d p t e : String) : Except ShapeError Env := do
  let some pred := env p | .error (.unbound p)
  let some onT := env t | .error (.unbound t)
  let some onF := env e | .error (.unbound e)
  if onT.ty != onF.ty then .error (.typeMismatch onT.ty onF.ty)
  else if pred.ty.shape != onT.ty.shape then .error (.shapeMismatch "select pred shape")
  else if pred.ty.elem != .i1 then .error (.shapeMismatch "select pred is not i1")
  else if hlen : pred.data.size = onT.data.size ∧ onT.data.size = onF.data.size then
    let rec go (i : Nat) (acc : Array (BitVec 64)) : Except ShapeError (Array (BitVec 64)) :=
      if h : i < pred.data.size then
        have hT : i < onT.data.size := by
          have : pred.data.size = onT.data.size := hlen.1
          exact this ▸ h
        have hF : i < onF.data.size := by
          have : pred.data.size = onF.data.size := hlen.1.trans hlen.2
          exact this ▸ h
        let bit := pred.data[i]
        let chosen := if bit == 0#64 then onF.data[i] else onT.data[i]
        go (i + 1) (acc.push chosen)
      else .ok acc
    let data ← go 0 #[]
    .ok (env.bind d { ty := onT.ty, data := data })
  else .error (.volumeMismatch pred.data.size onT.data.size)

/-- Index a row-major flat buffer. Returns `none` when the index is out of range. -/
def flatIndex (shape : List Nat) (idx : List Nat) : Option Nat :=
  let rec go (sh ix : List Nat) (acc : Nat) : Option Nat :=
    match sh, ix with
    | [], [] => some acc
    | d :: sh, i :: ix =>
      if i < d then
        let stride := sh.foldl (· * ·) 1
        go sh ix (acc + i * stride)
      else none
    | _, _ => none
  go shape idx 0

def unflat (shape : List Nat) (n : Nat) : List Nat :=
  let rec go (sh : List Nat) (rest : Nat) : List Nat :=
    match sh with
    | [] => []
    | d :: sh =>
      let stride := sh.foldl (· * ·) 1
      (rest / stride) % d :: go sh rest
  go shape n

def reshapeData (srcShape dstShape : List Nat) (data : Array (BitVec 64)) :
    Except ShapeError (Array (BitVec 64)) :=
  let sv := srcShape.foldl (· * ·) 1
  let dv := dstShape.foldl (· * ·) 1
  if sv != dv then .error (.volumeMismatch sv dv)
  else if data.size != sv then .error (.volumeMismatch data.size sv)
  else .ok data

def evalReshape (env : Env) (dst src : String) (outShape : List Nat) : Except ShapeError Env := do
  let some a := env src | .error (.unbound src)
  let data ← reshapeData a.ty.shape outShape a.data
  .ok (env.bind dst { ty := { shape := outShape, elem := a.ty.elem }, data := data })

def evalBroadcast (env : Env) (dst src : String) (outShape dims : List Nat) : Except ShapeError Env := do
  let some a := env src | .error (.unbound src)
  if dims.length != a.ty.shape.length then
    .error (.rankMismatch a.ty.shape.length dims.length)
  else
    let outN := outShape.foldl (· * ·) 1
    if a.ty.numElements != 0 && outN % a.ty.numElements != 0 then
      .error (.shapeMismatch "broadcast volume")
    else
      let rec expand (i : Nat) (acc : Array (BitVec 64)) : Array (BitVec 64) :=
        if i < outN then
          let srcIdx := if a.data.size == 0 then 0 else i % a.data.size
          expand (i + 1) (acc.push (a.data[srcIdx]?.getD 0#64))
        else acc
      .ok (env.bind dst { ty := { shape := outShape, elem := a.ty.elem }, data := expand 0 #[] })

def sliceOutDim (s l st : Nat) : Nat :=
  if st == 0 || l < s then 0 else (l - s + st - 1) / st

def sliceOne (shape : List Nat) (starts limits strides : List Nat) (data : Array (BitVec 64)) :
    Except ShapeError (List Nat × Array (BitVec 64)) :=
  if starts.length != shape.length || limits.length != shape.length || strides.length != shape.length then
    .error (.rankMismatch shape.length starts.length)
  else
    let outShape := (starts.zip (limits.zip strides)).map fun (s, l, st) => sliceOutDim s l st
    let outN := outShape.foldl (· * ·) 1
    let rec gather (i : Nat) (acc : Array (BitVec 64)) : Except ShapeError (Array (BitVec 64)) :=
      if i < outN then
        let idx := unflat outShape i
        let srcIdx := (starts.zip idx).zip strides |>.map fun ((s, k), st) => s + k * (if st == 0 then 1 else st)
        match flatIndex shape srcIdx with
        | none => .error (.shapeMismatch "slice index")
        | some n =>
          match data[n]? with
          | none => .error (.volumeMismatch n data.size)
          | some v => gather (i + 1) (acc.push v)
      else .ok acc
    do
      let data' ← gather 0 #[]
      .ok (outShape, data')

def evalSlice (env : Env) (dst src : String) (starts limits strides : List Nat) :
    Except ShapeError Env := do
  let some a := env src | .error (.unbound src)
  let (shape, data) ← sliceOne a.ty.shape starts limits strides a.data
  .ok (env.bind dst { ty := { shape := shape, elem := a.ty.elem }, data := data })

def evalDynamicSlice (env : Env) (dst src : String) (startIndices : List String)
    (sliceSizes : List Nat) : Except ShapeError Env := do
  let some a := env src | .error (.unbound src)
  if startIndices.length != a.ty.shape.length || sliceSizes.length != a.ty.shape.length then
    .error (.rankMismatch a.ty.shape.length startIndices.length)
  else
    let starts ← startIndices.mapM fun name => do
      let some t := env name | .error (.unbound name)
      match t.data[0]? with
      | none => .error (.volumeMismatch 0 1)
      | some w => pure w.toNat
    let limits := (starts.zip (a.ty.shape.zip sliceSizes)).map fun (s, dim, sz) =>
      min dim (s + sz)
    evalSlice (env.bind src a) dst src starts limits (List.replicate sliceSizes.length 1)

def evalDotGeneral (env : Env) (dst lhs rhs : String) (lhsC _rhsC outShape : List Nat) :
    Except ShapeError Env := do
  let some a := env lhs | .error (.unbound lhs)
  let some b := env rhs | .error (.unbound rhs)
  if a.ty.elem != b.ty.elem then .error (.typeMismatch a.ty b.ty)
  else if isFloat a.ty.elem then .error (.shapeMismatch "float dot is not an integer op")
  else
    let outN := outShape.foldl (· * ·) 1
    let k := match lhsC.head? with
      | some i => a.ty.shape.getD i 1
      | none => 1
    let rec dotAt (i : Nat) (acc : Array (BitVec 64)) : Array (BitVec 64) :=
      if i < outN then
        let rec inner (j : Nat) (sum : BitVec 64) : BitVec 64 :=
          if j < k then
            let ai := (i * k + j) % a.data.size
            let bi := (j * outN + i) % b.data.size
            inner (j + 1) (sum + (a.data[ai]?.getD 0) * (b.data[bi]?.getD 0))
          else sum
        dotAt (i + 1) (acc.push (inner 0 0))
      else acc
    .ok (env.bind dst { ty := { shape := outShape, elem := a.ty.elem }, data := dotAt 0 #[] })

def keptShape (shape dims : List Nat) : List Nat :=
  (shape.zipIdx.filter fun (_, i) => !dims.contains i).map Prod.fst

def evalReduce (env : Env) (dst src init : String) (dims : List Nat) (_body : String) :
    Except ShapeError Env := do
  let some a := env src | .error (.unbound src)
  let some z := env init | .error (.unbound init)
  if z.ty.elem != a.ty.elem then .error (.typeMismatch z.ty a.ty)
  else if isFloat a.ty.elem then .error (.shapeMismatch "float reduce is not an integer op")
  else
    let outShape := keptShape a.ty.shape dims
    let outN := outShape.foldl (· * ·) 1
    let redN := dims.foldl (fun acc i => acc * a.ty.shape.getD i 1) 1
    let rec redAt (i : Nat) (acc : Array (BitVec 64)) : Array (BitVec 64) :=
      if i < outN then
        let rec inner (j : Nat) (sum : BitVec 64) : BitVec 64 :=
          if j < redN then
            let ai := (i * redN + j) % a.data.size
            inner (j + 1) (sum + (a.data[ai]?.getD 0))
          else sum
        let base := z.data[0]?.getD 0
        redAt (i + 1) (acc.push (base + inner 0 0))
      else acc
    .ok (env.bind dst { ty := { shape := outShape, elem := a.ty.elem }, data := redAt 0 #[] })

def evalConvert (env : Env) (dst src : String) (outElem : ElemType) : Except ShapeError Env := do
  let some a := env src | .error (.unbound src)
  let data := match elemWidth? outElem with
    | none => a.data
    | some w => a.data.map (maskWidth w)
  .ok (env.bind dst { ty := { shape := a.ty.shape, elem := outElem }, data := data })

def evalConstant (env : Env) (dst : String) (v : TensorVal) : Except ShapeError Env :=
  if v.data.size != v.ty.numElements then .error (.volumeMismatch v.data.size v.ty.numElements)
  else .ok (env.bind dst v)

/-- Interpret one operation. Integer element ops are `BitVec 64` masked to the element width.
    This interpreter does not call `LeanNative.Semantics.eval*`. -/
def evalOp (env : Env) : StableHLOOp → Except ShapeError Env
  | .constant d v => evalConstant env d v
  | .add d a b => evalAdd env d a b
  | .subtract d a b => evalSub env d a b
  | .multiply d a b => evalMul env d a b
  | .divide d a b => evalDiv env d a b
  | .remainder d a b => evalRem env d a b
  | .maximum d a b => evalMax env d a b
  | .minimum d a b => evalMin env d a b
  | .and d a b => evalAnd env d a b
  | .or d a b => evalOr env d a b
  | .xor d a b => evalXor env d a b
  | .shiftLeft d a b => evalShl env d a b
  | .shiftRightArithmetic d a b => evalShrA env d a b
  | .shiftRightLogical d a b => evalShrL env d a b
  | .compare d a b dir => evalCompare env d a b dir
  | .select d p t e => evalSelect env d p t e
  | .broadcastInDim d s shape dims => evalBroadcast env d s shape dims
  | .reshape d s shape => evalReshape env d s shape
  | .slice d s starts limits strides => evalSlice env d s starts limits strides
  | .dynamicSlice d s idxs sizes => evalDynamicSlice env d s idxs sizes
  | .dotGeneral d a b lc rc shape => evalDotGeneral env d a b lc rc shape
  | .reduce d s i dims body => evalReduce env d s i dims body
  | .convert d s e => evalConvert env d s e
  | .returnOp s =>
    match env s with
    | none => .error (.unbound s)
    | some _ => .ok env

def evalOps (env : Env) : List StableHLOOp → Except ShapeError Env
  | [] => .ok env
  | op :: rest => do
    let env' ← evalOp env op
    evalOps env' rest

def resultTypeOf : StableHLOOp → Option TensorType
  | .constant _ v => some v.ty
  | .reshape _ _ _ => none
  | .compare _ _ _ _ => none
  | .select _ _ _ _ => none
  | .broadcastInDim _ _ _ _ => none
  | .slice _ _ _ _ _ => none
  | .dynamicSlice _ _ _ _ => none
  | .dotGeneral _ _ _ _ _ _ => none
  | .reduce _ _ _ _ _ => none
  | .convert _ _ e => some { shape := [], elem := e }
  | .returnOp _ => none
  | .add _ _ _ => none
  | .subtract _ _ _ => none
  | .multiply _ _ _ => none
  | .divide _ _ _ => none
  | .remainder _ _ _ => none
  | .maximum _ _ _ => none
  | .minimum _ _ _ => none
  | .and _ _ _ => none
  | .or _ _ _ => none
  | .xor _ _ _ => none
  | .shiftLeft _ _ _ => none
  | .shiftRightArithmetic _ _ _ => none
  | .shiftRightLogical _ _ _ => none

theorem numElements_scalar (e : ElemType) :
    ({ shape := [], elem := e : TensorType }).numElements = 1 := rfl

theorem evalOp_constant_preserves_type (env : Env) (dst : String) (v : TensorVal)
    (h : v.data.size = v.ty.numElements) :
    ∃ env', evalOp env (.constant dst v) = .ok env' ∧ env' dst = some v := by
  unfold evalOp evalConstant
  simp [h, Env.bind]

theorem evalOp_preserves_tensorType (env : Env) (dst : String) (v : TensorVal)
    (h : v.wellFormed) :
    match evalOp env (.constant dst v) with
    | .ok env' => ∃ t, env' dst = some t ∧ t.ty = v.ty ∧ t.wellFormed
    | .error _ => False := by
  unfold TensorVal.wellFormed at h
  unfold evalOp evalConstant
  simp [h, Env.bind, TensorVal.wellFormed]

theorem reshape_invalid_volume_errors (env : Env) (dst src : String) (a : TensorVal)
    (outShape : List Nat) (hsrc : env src = some a)
    (hvol : a.ty.shape.foldl (· * ·) 1 ≠ outShape.foldl (· * ·) 1) :
    evalOp env (.reshape dst src outShape) =
      .error (.volumeMismatch (a.ty.shape.foldl (· * ·) 1) (outShape.foldl (· * ·) 1)) := by
  unfold evalOp evalReshape reshapeData
  simp [hsrc, hvol, bind, Except.bind]

theorem maskWidth_idem (w : Nat) (x : BitVec 64) :
    maskWidth w (maskWidth w x) = maskWidth w x := by
  unfold maskWidth
  split
  · rfl
  · rename_i hge
    have hw : w ≤ 64 := Nat.le_of_lt (Nat.lt_of_not_ge hge)
    have hdvd : 2 ^ w ∣ 2 ^ 64 := ⟨2 ^ (64 - w), by rw [← Nat.pow_add, Nat.add_sub_of_le hw]⟩
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_mod_of_dvd _ hdvd, Nat.mod_mod]

theorem maskWidth_add_left (w : Nat) (x y : BitVec 64) :
    maskWidth w (maskWidth w x + y) = maskWidth w (x + y) := by
  unfold maskWidth
  split
  · rfl
  · rename_i hge
    have hw : w < 64 := Nat.lt_of_not_ge hge
    have hlt64 : ∀ n, n % 2 ^ w < 2 ^ 64 := fun n =>
      Nat.lt_trans (Nat.mod_lt _ (Nat.two_pow_pos w)) (Nat.pow_lt_pow_right (by decide) hw)
    have hdvd : 2 ^ w ∣ 2 ^ 64 := ⟨2 ^ (64 - w), by rw [← Nat.pow_add, Nat.add_sub_of_le (Nat.le_of_lt hw)]⟩
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_add, BitVec.toNat_ofNat,
      BitVec.toNat_add, Nat.mod_eq_of_lt (hlt64 x.toNat),
      Nat.mod_mod_of_dvd _ hdvd, Nat.mod_mod_of_dvd _ hdvd, Nat.mod_add_mod]

theorem maskWidth_add_right (w : Nat) (x y : BitVec 64) :
    maskWidth w (x + maskWidth w y) = maskWidth w (x + y) := by
  rw [BitVec.add_comm x, maskWidth_add_left, BitVec.add_comm]

theorem elemBin_add_comm (e : ElemType) (x y : BitVec 64) :
    elemBin e (· + ·) x y = elemBin e (· + ·) y x := by
  unfold elemBin
  cases elemWidth? e <;> simp [BitVec.add_comm]

theorem elemBin_add_assoc (e : ElemType) (x y z : BitVec 64)
    (hf : isFloat e = false) (hw : (elemWidth? e).isSome = true) :
    (do
      let xy ← elemBin e (· + ·) x y
      elemBin e (· + ·) xy z) =
    (do
      let yz ← elemBin e (· + ·) y z
      elemBin e (· + ·) x yz) := by
  unfold elemBin
  rcases hW : elemWidth? e with _ | w
  · simp [hW] at hw
  · simp [hf, bind, Except.bind, maskWidth_idem, maskWidth_add_left, maskWidth_add_right,
      BitVec.add_assoc]

theorem zipMap_comm (f : BitVec 64 → BitVec 64 → BitVec 64)
    (hf : ∀ x y, f x y = f y x) :
    ∀ (xs ys : List (BitVec 64)), xs.length = ys.length →
      (xs.zip ys).map (fun (x, y) => f x y) = (ys.zip xs).map (fun (x, y) => f x y)
  | [], [], _ => rfl
  | _ :: _, [], h => by cases h
  | [], _ :: _, h => by cases h
  | x :: xs, y :: ys, h => by
    simp [hf x y, zipMap_comm f hf xs ys (Nat.succ.inj h)]

theorem addAt_assoc (w : Nat) (a b c : BitVec 64) :
    addAt w (addAt w a b) c = addAt w a (addAt w b c) := by
  unfold addAt
  simp only [maskWidth_add_left, maskWidth_add_right, BitVec.add_assoc]

theorem zipWithTotal_comm (f : BitVec 64 → BitVec 64 → BitVec 64)
    (hf : ∀ x y, f x y = f y x) (a b : Array (BitVec 64))
    (hlen : a.size = b.size) :
    zipWithTotal f a b = zipWithTotal f b a := by
  unfold zipWithTotal
  have hlist : a.toList.length = b.toList.length := by simp [hlen]
  rw [zipMap_comm f hf a.toList b.toList hlist]

theorem zipMap_assoc (f : BitVec 64 → BitVec 64 → BitVec 64)
    (hf : ∀ x y z, f (f x y) z = f x (f y z)) :
    ∀ (xs ys zs : List (BitVec 64)), xs.length = ys.length → ys.length = zs.length →
      (((xs.zip ys).map (fun (x, y) => f x y)).zip zs).map (fun (x, y) => f x y) =
      (xs.zip ((ys.zip zs).map (fun (x, y) => f x y))).map (fun (x, y) => f x y)
  | [], [], [], _, _ => rfl
  | _ :: _, [], _, h1, _ => by cases h1
  | [], _ :: _, _, h1, _ => by cases h1
  | _ :: _, _ :: _, [], _, h2 => by cases h2
  | x :: xs, y :: ys, z :: zs, h1, h2 => by
    simp [hf x y z, zipMap_assoc f hf xs ys zs (Nat.succ.inj h1) (Nat.succ.inj h2)]

theorem zipWithTotal_assoc (f : BitVec 64 → BitVec 64 → BitVec 64)
    (hf : ∀ x y z, f (f x y) z = f x (f y z))
    (a b c : Array (BitVec 64))
    (hab : a.size = b.size) (hbc : b.size = c.size) :
    zipWithTotal f (zipWithTotal f a b) c = zipWithTotal f a (zipWithTotal f b c) := by
  unfold zipWithTotal
  have hab' : a.toList.length = b.toList.length := by simp [hab]
  have hbc' : b.toList.length = c.toList.length := by simp [hbc]
  simp [zipMap_assoc f hf a.toList b.toList c.toList hab' hbc']

theorem stablehlo_add_comm (env : Env) (x y : TensorVal)
    (hx : env "x" = some x) (hy : env "y" = some y) (hty : x.ty = y.ty)
    (hlen : x.data.size = y.data.size) :
    evalOp env (.add "d" "x" "y") = evalOp env (.add "d" "y" "x") := by
  unfold evalOp evalAdd
  simp [hx, hy, hty, hlen]
  cases hfloat : isFloat y.ty.elem
  · simp
    cases hW : elemWidth? y.ty.elem
    · simp
    · rename_i w
      have hf : ∀ p q : BitVec 64, addAt w p q = addAt w q p := by
        intro p q
        unfold addAt
        simp [BitVec.add_comm]
      simp [zipWithTotal_comm _ hf _ _ hlen]
  · simp

theorem stablehlo_add_assoc (env : Env) (x y z : TensorVal)
    (hx : env "x" = some x) (hy : env "y" = some y) (hz : env "z" = some z)
    (hty : x.ty = y.ty ∧ y.ty = z.ty)
    (hlen : x.data.size = y.data.size ∧ y.data.size = z.data.size)
    (hf : isFloat x.ty.elem = false) (hw : (elemWidth? x.ty.elem).isSome = true) :
    (do
      let e1 ← evalOp env (.add "xy" "x" "y")
      let e2 ← evalOp e1 (.add "r" "xy" "z")
      pure (e2 "r")) =
    (do
      let e1 ← evalOp env (.add "yz" "y" "z")
      let e2 ← evalOp e1 (.add "r" "x" "yz")
      pure (e2 "r")) := by
  unfold evalOp evalAdd
  rcases hty with ⟨hty1, hty2⟩
  rcases hlen with ⟨hlen1, hlen2⟩
  rcases hW : elemWidth? x.ty.elem with _ | w
  · simp [hW] at hw
  · have hW' : elemWidth? z.ty.elem = some w := by
      simpa [hty1, hty2] using hW
    have hf' : isFloat z.ty.elem = false := by
      simpa [hty1, hty2] using hf
    have hxy : (zipWithTotal (addAt w) x.data y.data).size = z.data.size := by
      unfold zipWithTotal
      simp [hlen1, hlen2]
    have hyz : z.data.size = (zipWithTotal (addAt w) y.data z.data).size := by
      unfold zipWithTotal
      simp [hlen2]
    simp [hx, hy, hz, hty1, hty2, hlen1, hlen2, hf', hW', Env.bind, bind, Except.bind, pure, Except.pure,
      hxy, hyz, zipWithTotal_assoc (addAt w) (addAt_assoc w) x.data y.data z.data hlen1 hlen2]

theorem evalOp_add_result_type (env : Env) (a b : TensorVal)
    (ha : env "a" = some a) (hb : env "b" = some b) (hty : a.ty = b.ty)
    (hlen : a.data.size = b.data.size)
    (hw : a.wellFormed) (hf : isFloat a.ty.elem = false)
    (hW : (elemWidth? a.ty.elem).isSome = true) :
    match evalOp env (.add "d" "a" "b") with
    | .ok env' => ∃ t, env' "d" = some t ∧ t.ty = a.ty ∧ t.wellFormed
    | .error _ => False := by
  unfold TensorVal.wellFormed at hw
  unfold evalOp evalAdd
  rcases hwidth : elemWidth? a.ty.elem with _ | w
  · simp [hwidth] at hW
  · have hwidth' : elemWidth? b.ty.elem = some w := by simpa [hty] using hwidth
    have hf' : isFloat b.ty.elem = false := by simpa [hty] using hf
    have hwf : b.data.size = b.ty.numElements := by simpa [hty, hlen] using hw
    simp [ha, hb, hty, hlen, hf', hwidth', Env.bind, TensorVal.wellFormed, zipWithTotal, hwf]

theorem evalOps_nil (env : Env) : evalOps env [] = .ok env := rfl

theorem evalOps_cons (env : Env) (op : StableHLOOp) (rest : List StableHLOOp) :
    evalOps env (op :: rest) = evalOp env op >>= fun env' => evalOps env' rest := rfl

end LeanNative.Backend.StableHLOAst
