import LeanNative.Backend.StableHLOAst.Syntax

namespace LeanNative.Backend.StableHLOAst

open LeanNative.IR

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

def ppCompareType : ElemType → String
  | e => if isFloat e then "FLOAT" else if isSigned e then "SIGNED" else "UNSIGNED"

def ppNatList (xs : List Nat) : String :=
  "[" ++ String.intercalate ", " (xs.map toString) ++ "]"

def ppVarArgs (xs : List String) : String :=
  String.intercalate ", " (xs.map fun s => s!"%{s}")

def ppSliceRanges : List Nat → List Nat → List Nat → List String
  | st :: sts, lm :: lms, sr :: srs =>
    s!"{st}:{lm}:{sr}" :: ppSliceRanges sts lms srs
  | _, _, _ => []

def maskWidth (w : Nat) (x : BitVec 64) : BitVec 64 :=
  if w ≥ 64 then x else BitVec.ofNat 64 (x.toNat % 2 ^ w)

/-- Signed decimal when the element type is signed; `true`/`false` on `i1`; raw/float otherwise. -/
def ppBit (e : ElemType) (x : BitVec 64) : String :=
  if e == .i1 then
    if maskWidth 1 x == 0#64 then "false" else "true"
  else match intBitWidth? e with
  | some w =>
    let x' := maskWidth w x
    if isSigned e && w > 0 && w < 64 && x'.toNat ≥ 2 ^ (w - 1) then
      "-" ++ toString (2 ^ w - x'.toNat)
    else if isSigned e && w ≥ 64 && (x' >>> 63) == 1#64 then
      "-" ++ toString ((0#64 - x').toNat)
    else toString x'.toNat
  | none =>
    match e with
    | .f32 =>
      let bits := (maskWidth 32 x).toNat.toUInt32
      let f := (Float32.ofBits bits).toFloat
      if f.isNaN then "0x7FC00000"
      else if f == (1.0 / 0.0) then "0x7F800000"
      else if f == (-1.0 / 0.0) then "0xFF800000"
      else toString f
    | .f64 =>
      let f := Float.ofBits x.toNat.toUInt64
      if f.isNaN then "0x7FF8000000000000"
      else if f == (1.0 / 0.0) then "0x7FF0000000000000"
      else if f == (-1.0 / 0.0) then "0xFFF0000000000000"
      else toString f
    | _ =>
      let bits := ((maskWidth (storageBitWidth e) x).toNat <<< 16).toUInt32
      let f := (Float32.ofBits bits).toFloat
      if f.isNaN then "0x7FC0"
      else if f == (1.0 / 0.0) then "0x7F80"
      else if f == (-1.0 / 0.0) then "0xFF80"
      else toString f

def groupEvery (d : Nat) : Nat → List String → List String
  | 0, _ => []
  | n + 1, xs =>
    ("[" ++ String.intercalate ", " (xs.take d) ++ "]") :: groupEvery d n (xs.drop d)

def ppDense (ty : TensorType) (data : Array (BitVec 64)) : String :=
  if data.size == 0 then "dense<>"
  else if data.all (· == data[0]!) then s!"dense<{ppBit ty.elem data[0]!}>"
  else
    let strs := data.toList.map (ppBit ty.elem)
    let nested := ty.shape.foldr
      (fun d acc => if d == 0 then ["[]"] else groupEvery d (acc.length / d) acc)
      strs
    s!"dense<{nested.headD ""}>"

def unsignedLt (w : Nat) (x y : BitVec 64) : Bool :=
  (maskWidth w x).toNat < (maskWidth w y).toNat

/-- Two's-complement signed comparison of width-`w` values stored in the low bits. -/
def signedLt (w : Nat) (x y : BitVec 64) : Bool :=
  if w == 0 then false
  else if w ≥ 64 then decide (x.toInt < y.toInt)
  else
    let x' := (maskWidth w x).toNat
    let y' := (maskWidth w y).toNat
    let sign := 2 ^ (w - 1)
    let sx : Int := if x' ≥ sign then Int.ofNat x' - Int.ofNat (2 ^ w) else Int.ofNat x'
    let sy : Int := if y' ≥ sign then Int.ofNat y' - Int.ofNat (2 ^ w) else Int.ofNat y'
    decide (sx < sy)

def signExtend (inW outW : Nat) (x : BitVec 64) : BitVec 64 :=
  let x' := maskWidth inW x
  if outW ≤ inW || inW == 0 then maskWidth outW x'
  else if x'.toNat ≥ 2 ^ (inW - 1) then
    maskWidth outW (x' + (BitVec.ofNat 64 (2 ^ outW - 2 ^ inW)))
  else x'

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

/-- Reject a tensor whose buffer length disagrees with its static shape. -/
def checkWellFormed (t : TensorVal) : Except ShapeError Unit :=
  if t.data.size = t.ty.numElements then .ok ()
  else .error (.volumeMismatch t.data.size t.ty.numElements)

def lookup (env : Env) (name : String) : Except ShapeError TensorVal := do
  let some t := env name | .error (.unbound name)
  checkWellFormed t
  .ok t

def binSame (env : Env) (dst lhs rhs : String)
    (f : ElemType → BitVec 64 → BitVec 64 → Except ShapeError (BitVec 64)) :
    Except ShapeError Env := do
  let a ← lookup env lhs
  let b ← lookup env rhs
  if a.ty = b.ty then
    let data ← zipWithM (f a.ty.elem) a.data b.data
    .ok (env.bind dst { ty := a.ty, data := data })
  else .error (.typeMismatch a.ty b.ty)

def elemBin (elem : ElemType) (op : BitVec 64 → BitVec 64 → BitVec 64)
    (x y : BitVec 64) : Except ShapeError (BitVec 64) :=
  if isFloat elem then .error (.shapeMismatch "float binop is not an integer op")
  else match intBitWidth? elem with
    | none => .error (.shapeMismatch "no integer width")
    | some w => .ok (maskWidth w (op (maskWidth w x) (maskWidth w y)))

def zipWithTotal (f : BitVec 64 → BitVec 64 → BitVec 64) (a b : Array (BitVec 64)) :
    Array (BitVec 64) :=
  (a.toList.zip b.toList).map (fun (x, y) => f x y) |>.toArray

def addAt (w : Nat) (p q : BitVec 64) : BitVec 64 :=
  maskWidth w (maskWidth w p + maskWidth w q)

def evalAdd (env : Env) (d a b : String) : Except ShapeError Env := do
  let x ← lookup env a
  let y ← lookup env b
  if x.ty = y.ty then
    if isFloat x.ty.elem then .error (.shapeMismatch "float binop is not an integer op")
    else match intBitWidth? x.ty.elem with
      | none => .error (.shapeMismatch "no integer width")
      | some w =>
        if x.data.size = y.data.size then
          .ok (env.bind d { ty := x.ty, data := zipWithTotal (addAt w) x.data y.data })
        else .error (.volumeMismatch x.data.size y.data.size)
  else .error (.typeMismatch x.ty y.ty)

def evalSub (env : Env) (d a b : String) : Except ShapeError Env :=
  binSame env d a b (fun e x y => elemBin e (· - ·) x y)

def evalMul (env : Env) (d a b : String) : Except ShapeError Env :=
  binSame env d a b (fun e x y => elemBin e (· * ·) x y)

/-- Signed division at width `w`. `INT_MIN / -1` and `/ 0` are `divisionByZero`. -/
def sdivWidth (w : Nat) (x y : BitVec 64) : Except ShapeError (BitVec 64) :=
  let x' := maskWidth w x
  let y' := maskWidth w y
  if y' == 0#64 then .error .divisionByZero
  else if w ≥ 64 then
    if x' == 0x8000000000000000#64 && y' == BitVec.allOnes 64 then
      .error .divisionByZero
    else .ok (x'.sdiv y')
  else
    let sign := 2 ^ (w - 1)
    let negX := x'.toNat ≥ sign
    let negY := y'.toNat ≥ sign
    let ax := if negX then 2 ^ w - x'.toNat else x'.toNat
    let ay := if negY then 2 ^ w - y'.toNat else y'.toNat
    if ay == 0 then .error .divisionByZero
    else if negX && ax == sign && negY && ay == 1 then .error .divisionByZero
    else
      let q := ax / ay
      let q' := if negX != negY then 2 ^ w - q else q
      .ok (maskWidth w (BitVec.ofNat 64 q'))

/-- Signed remainder at width `w`, with the same overflow policy as `sdivWidth`. -/
def sremWidth (w : Nat) (x y : BitVec 64) : Except ShapeError (BitVec 64) :=
  let x' := maskWidth w x
  let y' := maskWidth w y
  if y' == 0#64 then .error .divisionByZero
  else if w ≥ 64 then
    if x' == 0x8000000000000000#64 && y' == BitVec.allOnes 64 then
      .error .divisionByZero
    else .ok (x'.srem y')
  else
    let sign := 2 ^ (w - 1)
    let negX := x'.toNat ≥ sign
    let negY := y'.toNat ≥ sign
    let ax := if negX then 2 ^ w - x'.toNat else x'.toNat
    let ay := if negY then 2 ^ w - y'.toNat else y'.toNat
    if ay == 0 then .error .divisionByZero
    else if negX && ax == sign && negY && ay == 1 then .error .divisionByZero
    else
      let r := ax % ay
      let r' := if negX && r != 0 then 2 ^ w - r else r
      .ok (maskWidth w (BitVec.ofNat 64 r'))

def evalDiv (env : Env) (d a b : String) : Except ShapeError Env :=
  binSame env d a b fun e x y =>
    if isFloat e then .error (.shapeMismatch "float binop is not an integer op")
    else match intBitWidth? e with
      | none => .error (.shapeMismatch "no integer width")
      | some w =>
        if isSigned e then sdivWidth w x y
        else
          let y' := maskWidth w y
          if y' == 0#64 then .error .divisionByZero
          else .ok (maskWidth w ((maskWidth w x).udiv y'))

def evalRem (env : Env) (d a b : String) : Except ShapeError Env :=
  binSame env d a b fun e x y =>
    if isFloat e then .error (.shapeMismatch "float binop is not an integer op")
    else match intBitWidth? e with
      | none => .error (.shapeMismatch "no integer width")
      | some w =>
        if isSigned e then sremWidth w x y
        else
          let y' := maskWidth w y
          if y' == 0#64 then .error .divisionByZero
          else .ok (maskWidth w ((maskWidth w x) % y'))

def evalMax (env : Env) (d a b : String) : Except ShapeError Env :=
  binSame env d a b fun e x y =>
    if isFloat e then .error (.shapeMismatch "float binop is not an integer op")
    else match intBitWidth? e with
      | none => .error (.shapeMismatch "no integer width")
      | some w =>
        let x' := maskWidth w x
        let y' := maskWidth w y
        let lt := if isSigned e then signedLt w x' y' else unsignedLt w x' y'
        .ok (if lt then y' else x')

def evalMin (env : Env) (d a b : String) : Except ShapeError Env :=
  binSame env d a b fun e x y =>
    if isFloat e then .error (.shapeMismatch "float binop is not an integer op")
    else match intBitWidth? e with
      | none => .error (.shapeMismatch "no integer width")
      | some w =>
        let x' := maskWidth w x
        let y' := maskWidth w y
        let lt := if isSigned e then signedLt w x' y' else unsignedLt w x' y'
        .ok (if lt then x' else y')

def evalAnd (env : Env) (d a b : String) : Except ShapeError Env :=
  binSame env d a b (fun e x y => elemBin e (· &&& ·) x y)

def evalOr (env : Env) (d a b : String) : Except ShapeError Env :=
  binSame env d a b (fun e x y => elemBin e (· ||| ·) x y)

def evalXor (env : Env) (d a b : String) : Except ShapeError Env :=
  binSame env d a b (fun e x y => elemBin e (· ^^^ ·) x y)

def evalShl (env : Env) (d a b : String) : Except ShapeError Env :=
  binSame env d a b fun e x y =>
    if isFloat e then .error (.shapeMismatch "float binop is not an integer op")
    else match intBitWidth? e with
      | none => .error (.shapeMismatch "no integer width")
      | some w =>
        let amt := (maskWidth w y).toNat
        if amt ≥ w then .ok 0#64
        else .ok (maskWidth w ((maskWidth w x) <<< amt))

def evalShrL (env : Env) (d a b : String) : Except ShapeError Env :=
  binSame env d a b fun e x y =>
    if isFloat e then .error (.shapeMismatch "float binop is not an integer op")
    else match intBitWidth? e with
      | none => .error (.shapeMismatch "no integer width")
      | some w =>
        let amt := (maskWidth w y).toNat
        if amt ≥ w then .ok 0#64
        else .ok (maskWidth w ((maskWidth w x) >>> amt))

/-- Arithmetic right shift. Signed types sign-fill and saturate at `amt ≥ w`;
    unsigned `shift_right_arithmetic` is a logical shift (StableHLO). -/
def ashrWidth (w : Nat) (signed : Bool) (x amt : BitVec 64) : BitVec 64 :=
  let x' := maskWidth w x
  let n := amt.toNat
  if !signed then
    if n ≥ w then 0#64 else maskWidth w (x' >>> n)
  else if w == 0 then 0#64
  else if w ≥ 64 then
    if n ≥ 64 then if (x' >>> 63) &&& 1#64 == 0#64 then 0#64 else BitVec.allOnes 64
    else
      let shifted := x' >>> n
      let sign := (x' >>> 63) &&& 1#64
      if sign == 0#64 || n == 0 then shifted
      else shifted ||| ((BitVec.allOnes 64) <<< (64 - n))
  else
    let sign := (x' >>> (w - 1)) &&& 1#64
    if n ≥ w then if sign == 0#64 then 0#64 else maskWidth w (BitVec.allOnes 64)
    else if n == 0 || sign == 0#64 then maskWidth w (x' >>> n)
    else
      let fill := ((1#64 <<< n) - 1#64) <<< (w - n)
      maskWidth w ((x' >>> n) ||| fill)

def evalShrA (env : Env) (d a b : String) : Except ShapeError Env :=
  binSame env d a b fun e x y =>
    if isFloat e then .error (.shapeMismatch "float binop is not an integer op")
    else match intBitWidth? e with
      | none => .error (.shapeMismatch "no integer width")
      | some w => .ok (ashrWidth w (isSigned e) x (maskWidth w y))

def evalCompare (env : Env) (d a b : String) (dir : CompareDir) : Except ShapeError Env := do
  let aV ← lookup env a
  let bV ← lookup env b
  if aV.ty != bV.ty then .error (.typeMismatch aV.ty bV.ty)
  else if isFloat aV.ty.elem then .error (.shapeMismatch "float compare is not an integer op")
  else
    let data ← zipWithM (fun x y =>
      match intBitWidth? aV.ty.elem with
      | none => .error (.shapeMismatch "no integer width")
      | some w =>
        let x' := maskWidth w x
        let y' := maskWidth w y
        let lt := if isSigned aV.ty.elem then signedLt w x' y' else unsignedLt w x' y'
        let gt := if isSigned aV.ty.elem then signedLt w y' x' else unsignedLt w y' x'
        let bit : Bool := match dir with
          | .eq => x' == y'
          | .ne => x' != y'
          | .lt => lt
          | .le => lt || x' == y'
          | .gt => gt
          | .ge => gt || x' == y'
        .ok (if bit then 1#64 else 0#64)) aV.data bV.data
    .ok (env.bind d { ty := { shape := aV.ty.shape, elem := .i1 }, data := data })

def selectData (pred onT onF : List (BitVec 64)) : List (BitVec 64) :=
  match pred, onT, onF with
  | p :: ps, t :: ts, f :: fs => (if p == 0#64 then f else t) :: selectData ps ts fs
  | _, _, _ => []

def evalSelect (env : Env) (d p t e : String) : Except ShapeError Env := do
  let pred ← lookup env p
  let onT ← lookup env t
  let onF ← lookup env e
  if onT.ty != onF.ty then .error (.typeMismatch onT.ty onF.ty)
  else if pred.ty.shape != onT.ty.shape then .error (.shapeMismatch "select pred shape")
  else if pred.ty.elem != .i1 then .error (.shapeMismatch "select pred is not i1")
  else if pred.data.size = onT.data.size ∧ onT.data.size = onF.data.size then
    let data := (selectData pred.data.toList onT.data.toList onF.data.toList).toArray
    .ok (env.bind d { ty := onT.ty, data := data })
  else .error (.volumeMismatch pred.data.size onT.data.size)

/-- Row-major flat index. `none` when a coordinate is out of range. -/
def flatIndex : List Nat → List Nat → Option Nat
  | [], [] => some 0
  | d :: sh, i :: ix =>
    if i < d then
      (flatIndex sh ix).map fun acc => acc + i * sh.foldl (· * ·) 1
    else none
  | _, _ => none

def unflat : List Nat → Nat → List Nat
  | [], _ => []
  | d :: sh, rest =>
    let stride := sh.foldl (· * ·) 1
    (rest / stride) % d :: unflat sh rest

def reshapeData (srcShape dstShape : List Nat) (data : Array (BitVec 64)) :
    Except ShapeError (Array (BitVec 64)) :=
  let sv := srcShape.foldl (· * ·) 1
  let dv := dstShape.foldl (· * ·) 1
  if sv != dv then .error (.volumeMismatch sv dv)
  else if data.size != sv then .error (.volumeMismatch data.size sv)
  else .ok data

def evalReshape (env : Env) (dst src : String) (outShape : List Nat) : Except ShapeError Env := do
  let a ← lookup env src
  let data ← reshapeData a.ty.shape outShape a.data
  .ok (env.bind dst { ty := { shape := outShape, elem := a.ty.elem }, data := data })

/-- `dims` strictly increasing, unique, and in range. -/
def dimsStrict (rank : Nat) (ds : List Nat) : Bool :=
  ds.all (· < rank) && (ds.zipIdx.all fun (d, i) => ds.take i |>.all (· < d))

def srcCoord (srcShape dims : List Nat) (outIdx : List Nat) (d : Nat) : Nat :=
  let sd := srcShape.getD (dims.idxOf d) 0
  let c := outIdx.getD d 0
  if sd == 1 then 0 else c

def broadcastAt (srcShape outShape dims : List Nat) (data : Array (BitVec 64)) (i : Nat) :
    Except ShapeError (BitVec 64) :=
  let outIdx := unflat outShape i
  let srcIdx := dims.map (srcCoord srcShape dims outIdx)
  match flatIndex srcShape srcIdx with
  | none => .error (.shapeMismatch "broadcast index")
  | some n =>
    match data[n]? with
    | none => .error (.volumeMismatch n data.size)
    | some v => .ok v

def mapRangeM (n : Nat) (f : Nat → Except ShapeError (BitVec 64)) :
    Except ShapeError (Array (BitVec 64)) :=
  (List.range n).foldlM (fun acc i => do
    let v ← f i
    .ok (acc.push v)) #[]

def evalBroadcast (env : Env) (dst src : String) (outShape dims : List Nat) :
    Except ShapeError Env := do
  let a ← lookup env src
  if dims.length != a.ty.shape.length then
    .error (.rankMismatch a.ty.shape.length dims.length)
  else if !dimsStrict outShape.length dims then
    .error (.shapeMismatch "broadcast dims not strictly increasing")
  else
    let ok := (a.ty.shape.zip dims).all fun (sd, d) =>
      match outShape[d]? with
      | some od => sd == 1 || sd == od
      | none => false
    if !ok then .error (.shapeMismatch "broadcast dim size")
    else
      let outN := outShape.foldl (· * ·) 1
      let data ← mapRangeM outN (broadcastAt a.ty.shape outShape dims a.data)
      .ok (env.bind dst { ty := { shape := outShape, elem := a.ty.elem }, data := data })

def sliceOutDim (dim s l st : Nat) : Option Nat :=
  if st == 0 || s > l || l > dim then none else some ((l - s + st - 1) / st)

def sliceOutDims : List Nat → List Nat → List Nat → List Nat → Except ShapeError (List Nat)
  | [], [], [], [] => .ok []
  | d :: ds, s :: ss, l :: ls, st :: sts => do
    match sliceOutDim d s l st with
    | none => .error (.shapeMismatch "slice bounds")
    | some n => do
      let rest ← sliceOutDims ds ss ls sts
      .ok (n :: rest)
  | _, _, _, _ => .error (.rankMismatch 0 0)

def sliceCoord (starts strides : List Nat) (idx : List Nat) : List Nat :=
  (starts.zip idx).zip strides |>.map fun ((s, k), st) => s + k * st

def sliceAt (shape outShape starts strides : List Nat) (data : Array (BitVec 64)) (i : Nat) :
    Except ShapeError (BitVec 64) :=
  let srcIdx := sliceCoord starts strides (unflat outShape i)
  match flatIndex shape srcIdx with
  | none => .error (.shapeMismatch "slice index")
  | some n =>
    match data[n]? with
    | none => .error (.volumeMismatch n data.size)
    | some v => .ok v

def sliceOne (shape : List Nat) (starts limits strides : List Nat) (data : Array (BitVec 64)) :
    Except ShapeError (List Nat × Array (BitVec 64)) :=
  if starts.length != shape.length || limits.length != shape.length ||
      strides.length != shape.length then
    .error (.rankMismatch shape.length starts.length)
  else do
    let outShape ← sliceOutDims shape starts limits strides
    let outN := outShape.foldl (· * ·) 1
    let data' ← mapRangeM outN (sliceAt shape outShape starts strides data)
    .ok (outShape, data')

def evalSlice (env : Env) (dst src : String) (starts limits strides : List Nat) :
    Except ShapeError Env := do
  let a ← lookup env src
  let (shape, data) ← sliceOne a.ty.shape starts limits strides a.data
  .ok (env.bind dst { ty := { shape := shape, elem := a.ty.elem }, data := data })

/-- Read a 0-D scalar integer start index, sign-aware. -/
def readStart (env : Env) (name : String) : Except ShapeError Int := do
  let t ← lookup env name
  if t.ty.shape != [] then .error (.shapeMismatch "dynamic_slice start is not scalar")
  else if isFloat t.ty.elem then .error (.shapeMismatch "dynamic_slice start is float")
  else match intBitWidth? t.ty.elem, t.data[0]? with
    | none, _ => .error (.shapeMismatch "dynamic_slice start width")
    | _, none => .error (.volumeMismatch 0 1)
    | some w, some bits =>
      let x := maskWidth w bits
      if isSigned t.ty.elem && w > 0 && w < 64 && x.toNat ≥ 2 ^ (w - 1) then
        .ok (Int.ofNat x.toNat - Int.ofNat (2 ^ w))
      else if isSigned t.ty.elem && w ≥ 64 then .ok x.toInt
      else .ok (Int.ofNat x.toNat)

def clampStart (dim sz : Nat) (signedStart : Int) : Nat :=
  let hi : Int := Int.ofNat (dim - sz)
  let lo : Int := if signedStart < 0 then 0 else signedStart
  let c := if lo > hi then hi else lo
  c.toNat

def evalDynamicSlice (env : Env) (dst src : String) (startIndices : List String)
    (sliceSizes : List Nat) : Except ShapeError Env := do
  let a ← lookup env src
  if startIndices.length != a.ty.shape.length || sliceSizes.length != a.ty.shape.length then
    .error (.rankMismatch a.ty.shape.length startIndices.length)
  else if !(a.ty.shape.zip sliceSizes).all fun (d, sz) => sz ≤ d then
    .error (.shapeMismatch "dynamic_slice size exceeds dim")
  else
    let idxTensors ← startIndices.mapM (lookup env)
    let sameElem := match idxTensors with
      | [] => true
      | t0 :: ts => ts.all fun t => t.ty.elem == t0.ty.elem
    if !sameElem then .error (.shapeMismatch "dynamic_slice start element type mismatch")
    else
      let starts ← startIndices.mapM (readStart env)
      let clamped := (starts.zip (a.ty.shape.zip sliceSizes)).map fun (s, dim, sz) =>
        clampStart dim sz s
      let limits := (clamped.zip sliceSizes).map fun (s, sz) => s + sz
      evalSlice env dst src clamped limits (List.replicate sliceSizes.length 1)

def complement (rank : Nat) (taken : List Nat) : List Nat :=
  (List.range rank).filter fun i => !taken.contains i

/-- Validate and index one `dot_general` operand: batch, contract, then free dims. -/
def dotOperandOk (shape batch contract : List Nat) : Except ShapeError (List Nat) := do
  if !dimsStrict shape.length batch || !dimsStrict shape.length contract then
    .error (.shapeMismatch "dot dims not strictly increasing")
  else if batch.any (contract.contains ·) then
    .error (.shapeMismatch "dot batch/contract overlap")
  else .ok (complement shape.length (batch ++ contract))

def axisAt (axes : List Nat) (coords : List Nat) (i : Nat) : Nat :=
  match axes.idxOf? i with
  | some k => coords.getD k 0
  | none => 0

def gatherIdx (shape : List Nat) (axes : List Nat) (coords : List Nat) : List Nat :=
  (List.range shape.length).map (axisAt axes coords)

def dotProductAt (w : Nat) (aShape bShape : List Nat)
    (aAxes bAxes : List Nat) (kShape : List Nat)
    (aData bData : Array (BitVec 64))
    (aCoords bCoords : List Nat) (sum : BitVec 64) (j : Nat) : Except ShapeError (BitVec 64) := do
  let kCoords := unflat kShape j
  let li := gatherIdx aShape aAxes (aCoords ++ kCoords)
  let ri := gatherIdx bShape bAxes (bCoords ++ kCoords)
  match flatIndex aShape li, flatIndex bShape ri with
  | some na, some nb =>
    match aData[na]?, bData[nb]? with
    | some va, some vb =>
      .ok (addAt w sum (maskWidth w (maskWidth w va * maskWidth w vb)))
    | _, _ => .error (.volumeMismatch na aData.size)
  | _, _ => .error (.shapeMismatch "dot index")

def dotAt (w : Nat) (outShape : List Nat) (batchN lhsFreeN : Nat)
    (aShape bShape kShape : List Nat) (aAxes bAxes : List Nat)
    (aData bData : Array (BitVec 64)) (i : Nat) : Except ShapeError (BitVec 64) := do
  let outIdx := unflat outShape i
  let bCoords := outIdx.take batchN
  let rest := outIdx.drop batchN
  let lFree := rest.take lhsFreeN
  let rFree := rest.drop lhsFreeN
  let kN := kShape.foldl (· * ·) 1
  (List.range kN).foldlM
    (dotProductAt w aShape bShape aAxes bAxes kShape aData bData
      (bCoords ++ lFree) (bCoords ++ rFree))
    0#64

def evalDotGeneral (env : Env) (dst lhs rhs : String)
    (lhsBatch rhsBatch lhsC rhsC outShape : List Nat) : Except ShapeError Env := do
  let a ← lookup env lhs
  let b ← lookup env rhs
  if a.ty.elem != b.ty.elem then .error (.typeMismatch a.ty b.ty)
  else if isFloat a.ty.elem then .error (.shapeMismatch "float dot is not an integer op")
  else
    let lhsFree ← dotOperandOk a.ty.shape lhsBatch lhsC
    let rhsFree ← dotOperandOk b.ty.shape rhsBatch rhsC
    let batchShape := lhsBatch.map fun i => a.ty.shape.getD i 0
    let lhsFreeShape := lhsFree.map fun i => a.ty.shape.getD i 0
    let rhsFreeShape := rhsFree.map fun i => b.ty.shape.getD i 0
    let expect := batchShape ++ lhsFreeShape ++ rhsFreeShape
    let kShape := lhsC.map fun i => a.ty.shape.getD i 0
    let kShapeR := rhsC.map fun i => b.ty.shape.getD i 0
    let batchR := rhsBatch.map fun i => b.ty.shape.getD i 0
    if lhsBatch.length != rhsBatch.length || lhsC.length != rhsC.length then
      .error (.rankMismatch lhsBatch.length rhsBatch.length)
    else if batchShape != batchR || kShape != kShapeR || outShape != expect then
      .error (.shapeMismatch "dot output shape")
    else match intBitWidth? a.ty.elem with
      | none => .error (.shapeMismatch "no integer width")
      | some w =>
        let outN := outShape.foldl (· * ·) 1
        let data ← mapRangeM outN
          (dotAt w outShape batchShape.length lhsFreeShape.length
            a.ty.shape b.ty.shape kShape
            (lhsBatch ++ lhsFree ++ lhsC) (rhsBatch ++ rhsFree ++ rhsC)
            a.data b.data)
        .ok (env.bind dst { ty := { shape := outShape, elem := a.ty.elem }, data := data })

def keptShape (shape dims : List Nat) : List Nat :=
  (shape.zipIdx.filter fun (_, i) => !dims.contains i).map Prod.fst

def reduceBody (b : String) : Option String :=
  match b.splitOn "_" with
  | "add" :: _ => some "add"
  | "mul" :: _ => some "multiply"
  | "max" :: _ => some "maximum"
  | "min" :: _ => some "minimum"
  | "and" :: _ => some "and"
  | "or" :: _ => some "or"
  | "xor" :: _ => some "xor"
  | _ => none

def reduceBodyMatches (body : String) (e : ElemType) : Bool :=
  let s := ppElemType e
  body == "add" || body == "mul" || body == "max" || body == "min" ||
    body == "and" || body == "or" || body == "xor" ||
    body == s!"add_{s}" || body == s!"mul_{s}" ||
    body == s!"max_{s}" || body == s!"min_{s}" ||
    body == s!"and_{s}" || body == s!"or_{s}" ||
    body == s!"xor_{s}"

def reduceOpOf (body : String) : String :=
  match body.splitOn "_" with
  | "add" :: _ => "add"
  | "mul" :: _ => "mul"
  | "max" :: _ => "max"
  | "min" :: _ => "min"
  | "and" :: _ => "and"
  | "or" :: _ => "or"
  | "xor" :: _ => "xor"
  | _ => body

def applyReduce (e : ElemType) (body : String) (x y : BitVec 64) :
    Except ShapeError (BitVec 64) :=
  match reduceOpOf body with
  | "add" => elemBin e (· + ·) x y
  | "mul" => elemBin e (· * ·) x y
  | "and" => elemBin e (· &&& ·) x y
  | "or" => elemBin e (· ||| ·) x y
  | "xor" => elemBin e (· ^^^ ·) x y
  | "max" | "min" =>
    if isFloat e then .error (.shapeMismatch "float reduce is not an integer op")
    else match intBitWidth? e with
      | none => .error (.shapeMismatch "no integer width")
      | some w =>
        let x' := maskWidth w x
        let y' := maskWidth w y
        let lt := if isSigned e then signedLt w x' y' else unsignedLt w x' y'
        .ok (if reduceOpOf body == "max" then (if lt then y' else x') else (if lt then x' else y'))
  | _ => .error (.shapeMismatch "unknown reduce body")

def reduceStep (e : ElemType) (body : String) (w : Nat)
    (shape : List Nat) (kept dims : List Nat) (redShape : List Nat)
    (data : Array (BitVec 64)) (keptCoords : List Nat) (sum : BitVec 64) (j : Nat) :
    Except ShapeError (BitVec 64) := do
  let redCoords := unflat redShape j
  let idx := gatherIdx shape (kept ++ dims) (keptCoords ++ redCoords)
  match flatIndex shape idx with
  | none => .error (.shapeMismatch "reduce index")
  | some n =>
    match data[n]? with
    | none => .error (.volumeMismatch n data.size)
    | some v => do
      let s ← applyReduce e body sum v
      .ok (maskWidth w s)

def reduceAt (e : ElemType) (body : String) (w : Nat)
    (shape outShape : List Nat) (kept dims : List Nat) (redShape : List Nat)
    (data : Array (BitVec 64)) (base : BitVec 64) (i : Nat) :
    Except ShapeError (BitVec 64) := do
  let keptCoords := unflat outShape i
  let redN := redShape.foldl (· * ·) 1
  (List.range redN).foldlM
    (reduceStep e body w shape kept dims redShape data keptCoords)
    (maskWidth w base)

def evalReduce (env : Env) (dst src init : String) (dims : List Nat) (body : String)
    (outShape : List Nat) : Except ShapeError Env := do
  let a ← lookup env src
  let z ← lookup env init
  if z.ty.shape != [] then .error (.shapeMismatch "reduce init is not scalar")
  else if z.ty.elem != a.ty.elem then .error (.typeMismatch z.ty a.ty)
  else if isFloat a.ty.elem then .error (.shapeMismatch "float reduce is not an integer op")
  else if !reduceBodyMatches body a.ty.elem then .error (.shapeMismatch "unknown reduce body")
  else if !dimsStrict a.ty.shape.length dims then
    .error (.shapeMismatch "reduce dims not strictly increasing")
  else if outShape != keptShape a.ty.shape dims then
    .error (.shapeMismatch "reduce output shape mismatch")
  else match intBitWidth? a.ty.elem, z.data[0]? with
    | none, _ => .error (.shapeMismatch "no integer width")
    | _, none => .error (.volumeMismatch 0 1)
    | some w, some base0 =>
      let kept := complement a.ty.shape.length dims
      let redShape := dims.map fun i => a.ty.shape.getD i 1
      let outN := outShape.foldl (· * ·) 1
      let data ← mapRangeM outN
        (reduceAt a.ty.elem body w a.ty.shape outShape kept dims redShape a.data base0)
      .ok (env.bind dst { ty := { shape := outShape, elem := a.ty.elem }, data := data })

def evalConvert (env : Env) (dst src : String) (outElem : ElemType) : Except ShapeError Env := do
  let a ← lookup env src
  if isFloat a.ty.elem || isFloat outElem then
    .error (.shapeMismatch "float convert is not an integer op")
  else match intBitWidth? a.ty.elem, intBitWidth? outElem with
    | some inW, some outW =>
      let data := a.data.map fun x =>
        if outElem == .i1 then if maskWidth inW x == 0#64 then 0#64 else 1#64
        else if isSigned a.ty.elem && outW > inW then signExtend inW outW x
        else maskWidth outW x
      .ok (env.bind dst { ty := { shape := a.ty.shape, elem := outElem }, data := data })
    | _, _ => .error (.shapeMismatch "no integer width")

def evalConstant (env : Env) (dst : String) (v : TensorVal) : Except ShapeError Env :=
  if v.data.size != v.ty.numElements then .error (.volumeMismatch v.data.size v.ty.numElements)
  else .ok (env.bind dst v)

/-- Interpret one operation. Integer element ops are `BitVec` masked to the element width.
    Floating element types fail closed on arithmetic/shift/compare/dot/reduce/convert ops.
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
  | .dotGeneral d a b lb rb lc rc shape => evalDotGeneral env d a b lb rb lc rc shape
  | .reduce d s i dims body shape => evalReduce env d s i dims body shape
  | .convert d s e => evalConvert env d s e
  | .returnOp s => do
    let _ ← lookup env s
    .ok env

def evalOps (env : Env) : List StableHLOOp → Except ShapeError Env
  | [] => .ok env
  | .returnOp s :: _ :: _ => do
    let _ ← lookup env s
    .error (.shapeMismatch "dead ops after return")
  | op :: rest => do
    let env' ← evalOp env op
    evalOps env' rest

/-- Exact result type of an op given the types of operands already bound. -/
def resultTypeOf (tenv : TypeEnv) : StableHLOOp → Option TensorType
  | .constant _ v => if v.data.size == v.ty.numElements then some v.ty else none
  | .add _ a b | .subtract _ a b | .multiply _ a b | .divide _ a b
  | .remainder _ a b | .maximum _ a b | .minimum _ a b
  | .and _ a b | .or _ a b | .xor _ a b
  | .shiftLeft _ a b | .shiftRightArithmetic _ a b | .shiftRightLogical _ a b =>
    match tenv a, tenv b with
    | some ta, some tb => if ta == tb then some ta else none
    | _, _ => none
  | .compare _ a b _ =>
    match tenv a, tenv b with
    | some ta, some tb => if ta == tb then some { ta with elem := .i1 } else none
    | _, _ => none
  | .select _ p t e =>
    match tenv p, tenv t, tenv e with
    | some tp, some tt, some te =>
      if tt == te && tp.elem == .i1 && tp.shape == tt.shape then some tt else none
    | _, _, _ => none
  | .broadcastInDim _ s shape dims =>
    tenv s |>.bind fun ty =>
      let ok := dims.length == ty.shape.length && dimsStrict shape.length dims &&
        ((ty.shape.zip dims).all fun (sd, d) =>
          match shape[d]? with
          | some od => sd == 1 || sd == od
          | none => false)
      if ok then some { ty with shape := shape } else none
  | .reshape _ s shape =>
    tenv s |>.bind fun ty =>
      if ty.shape.foldl (· * ·) 1 == shape.foldl (· * ·) 1 then some { ty with shape := shape }
      else none
  | .slice _ s starts limits strides =>
    tenv s |>.bind fun ty =>
      if starts.length != ty.shape.length || limits.length != ty.shape.length ||
          strides.length != ty.shape.length then none
      else
        match sliceOutDims ty.shape starts limits strides with
        | .ok outShape => some { ty with shape := outShape }
        | .error _ => none
  | .dynamicSlice _ s idxs sizes =>
    tenv s |>.bind fun ty =>
      let idxTys := idxs.filterMap tenv
      let idxOk := idxTys.length == idxs.length && (idxTys.all fun it => it.shape == [] && !isFloat it.elem)
      if idxs.length == ty.shape.length && sizes.length == ty.shape.length && idxOk &&
          ((ty.shape.zip sizes).all fun (d, sz) => sz ≤ d) then
        some { ty with shape := sizes }
      else none
  | .dotGeneral _ a b lb rb lc rc shape =>
    match tenv a, tenv b with
    | some ta, some tb =>
      match dotOperandOk ta.shape lb lc, dotOperandOk tb.shape rb rc with
      | .ok lf, .ok rf =>
        let bs := lb.map fun i => ta.shape.getD i 0
        let bsR := rb.map fun i => tb.shape.getD i 0
        let ks := lc.map fun i => ta.shape.getD i 0
        let ksR := rc.map fun i => tb.shape.getD i 0
        let expect := bs ++ (lf.map fun i => ta.shape.getD i 0) ++ (rf.map fun i => tb.shape.getD i 0)
        if ta.elem == tb.elem && lb.length == rb.length && lc.length == rc.length &&
            bs == bsR && ks == ksR && shape == expect then
          some { ta with shape := shape }
        else none
      | _, _ => none
    | _, _ => none
  | .reduce _ a i dims body shape =>
    match tenv a, tenv i with
    | some ta, some ti =>
      if ti.shape == [] && ti.elem == ta.elem && !isFloat ta.elem &&
          reduceBodyMatches body ta.elem &&
          dimsStrict ta.shape.length dims && shape == keptShape ta.shape dims then
        some { ta with shape := shape }
      else none
    | _, _ => none
  | .convert _ s e => tenv s |>.map fun ty => { ty with elem := e }
  | .returnOp _ => none

def bindResult (tenv : TypeEnv) (op : StableHLOOp) : TypeEnv :=
  match op, resultTypeOf tenv op with
  | .constant d _, some ty | .add d _ _, some ty | .subtract d _ _, some ty
  | .multiply d _ _, some ty | .divide d _ _, some ty | .remainder d _ _, some ty
  | .maximum d _ _, some ty | .minimum d _ _, some ty
  | .and d _ _, some ty | .or d _ _, some ty | .xor d _ _, some ty
  | .shiftLeft d _ _, some ty | .shiftRightArithmetic d _ _, some ty
  | .shiftRightLogical d _ _, some ty | .compare d _ _ _, some ty
  | .select d _ _ _, some ty | .broadcastInDim d _ _ _, some ty
  | .reshape d _ _, some ty | .slice d _ _ _ _, some ty
  | .dynamicSlice d _ _ _, some ty | .dotGeneral d _ _ _ _ _ _ _, some ty
  | .reduce d _ _ _ _ _, some ty | .convert d _ _, some ty => tenv.bind d ty
  | _, _ => tenv

def ppTyped (dst : String) (op : String) (ty : Option TensorType) : String :=
  match ty with
  | some t => s!"%{dst} = {op} : {ppTensorType t}"
  | none => s!"%{dst} = {op} : tensor<i64>"

def ppCompare (d a b : String) (dir : CompareDir) (ty : TensorType) : String :=
  let out := ppTensorType { ty with elem := .i1 }
  let inn := ppTensorType ty
  s!"%{d} = stablehlo.compare {ppCompareDir dir}, %{a}, %{b}, {ppCompareType ty.elem}"
    ++ s!" : ({inn}, {inn}) -> {out}"

def ppBroadcast (d s : String) (shape dims : List Nat) (ty : TensorType) : String :=
  let out := { ty with shape := shape }
  s!"%{d} = stablehlo.broadcast_in_dim %{s}, dims = {ppNatList dims}"
    ++ s!" : ({ppTensorType ty}) -> {ppTensorType out}"

def ppDot (d a b : String) (lb rb lc rc : List Nat) (shape : List Nat)
    (ta tb : TensorType) : String :=
  let out := ppTensorType { ta with shape := shape }
  let batchStr :=
    if lb.isEmpty && rb.isEmpty then ""
    else s!", batching_dims = {ppNatList lb} x {ppNatList rb}"
  s!"%{d} = stablehlo.dot_general %{a}, %{b}"
    ++ batchStr
    ++ s!", contracting_dims = {ppNatList lc} x {ppNatList rc}"
    ++ s!" : ({ppTensorType ta}, {ppTensorType tb}) -> {out}"

def ppReducer (body : String) (elem : ElemType) : String :=
  let sc := ppTensorType { shape := [], elem := elem }
  let opName := (reduceBody body).getD body
  s!"reducer(%arg0: {sc}, %arg1: {sc}) \{\n"
    ++ s!"      %sum = stablehlo.{opName} %arg0, %arg1 : {sc}\n"
    ++ s!"      stablehlo.return %sum : {sc}\n"
    ++ "    }"

def ppReduce (d s i : String) (dims : List Nat) (body : String) (shape : List Nat)
    (ts ti : TensorType) : String :=
  let out := { ts with shape := shape }
  s!"%{d} = stablehlo.reduce(%{s} init: %{i}) across dimensions = {ppNatList dims}"
    ++ s!" : ({ppTensorType ts}, {ppTensorType ti}) -> {ppTensorType out}"
    ++ s!" {ppReducer body ts.elem}"

/-- 1:1 structural pretty-printer. Every op and `return` carries an MLIR type. -/
def ppStableHLOOp (tenv : TypeEnv) (op : StableHLOOp) : String :=
  match op with
  | .constant dst v =>
    let bits := v.data.map (maskWidth (storageBitWidth v.ty.elem))
    s!"%{dst} = stablehlo.constant {ppDense v.ty bits} : {ppTensorType v.ty}"
  | .add d a b => ppTyped d s!"stablehlo.add %{a}, %{b}" (resultTypeOf tenv op)
  | .subtract d a b => ppTyped d s!"stablehlo.subtract %{a}, %{b}" (resultTypeOf tenv op)
  | .multiply d a b => ppTyped d s!"stablehlo.multiply %{a}, %{b}" (resultTypeOf tenv op)
  | .divide d a b => ppTyped d s!"stablehlo.divide %{a}, %{b}" (resultTypeOf tenv op)
  | .remainder d a b => ppTyped d s!"stablehlo.remainder %{a}, %{b}" (resultTypeOf tenv op)
  | .maximum d a b => ppTyped d s!"stablehlo.maximum %{a}, %{b}" (resultTypeOf tenv op)
  | .minimum d a b => ppTyped d s!"stablehlo.minimum %{a}, %{b}" (resultTypeOf tenv op)
  | .and d a b => ppTyped d s!"stablehlo.and %{a}, %{b}" (resultTypeOf tenv op)
  | .or d a b => ppTyped d s!"stablehlo.or %{a}, %{b}" (resultTypeOf tenv op)
  | .xor d a b => ppTyped d s!"stablehlo.xor %{a}, %{b}" (resultTypeOf tenv op)
  | .shiftLeft d a b => ppTyped d s!"stablehlo.shift_left %{a}, %{b}" (resultTypeOf tenv op)
  | .shiftRightArithmetic d a b =>
    ppTyped d s!"stablehlo.shift_right_arithmetic %{a}, %{b}" (resultTypeOf tenv op)
  | .shiftRightLogical d a b =>
    ppTyped d s!"stablehlo.shift_right_logical %{a}, %{b}" (resultTypeOf tenv op)
  | .compare d a b dir =>
    match tenv a, resultTypeOf tenv op with
    | some ty, some _ => ppCompare d a b dir ty
    | _, _ =>
      s!"%{d} = stablehlo.compare {ppCompareDir dir}, %{a}, %{b} : tensor<i1>"
  | .select d p t e =>
    match resultTypeOf tenv op, tenv p, tenv t with
    | some _, some pt, some tt =>
      s!"%{d} = stablehlo.select %{p}, %{t}, %{e} : {ppTensorType pt}, {ppTensorType tt}"
    | _, _, _ =>
      s!"%{d} = stablehlo.select %{p}, %{t}, %{e} : tensor<i1>, tensor<i64>"
  | .broadcastInDim d s shape dims =>
    match resultTypeOf tenv op, tenv s with
    | some _, some ty => ppBroadcast d s shape dims ty
    | _, _ =>
      s!"%{d} = stablehlo.broadcast_in_dim %{s}, dims = {ppNatList dims}"
        ++ s!" : (tensor<i64>) -> tensor<{ppShape shape}xi64>"
  | .reshape d s shape =>
    match resultTypeOf tenv op, tenv s with
    | some _, some ty =>
      let out := ppTensorType { ty with shape := shape }
      s!"%{d} = stablehlo.reshape %{s} : ({ppTensorType ty}) -> {out}"
    | _, _ =>
      s!"%{d} = stablehlo.reshape %{s} : (tensor<i64>) -> tensor<{ppShape shape}xi64>"
  | .slice d s starts limits strides =>
    let ranges := "[" ++ String.intercalate ", " (ppSliceRanges starts limits strides) ++ "]"
    match tenv s, resultTypeOf tenv op with
    | some sty, some oty =>
      s!"%{d} = stablehlo.slice %{s} {ranges} : ({ppTensorType sty}) -> {ppTensorType oty}"
    | _, _ =>
      ppTyped d s!"stablehlo.slice %{s} {ranges}" (some { shape := starts, elem := .i64 })
  | .dynamicSlice d s idxs sizes =>
    let opsStr := if idxs.isEmpty then s!"%{s}" else s!"%{s}, {ppVarArgs idxs}"
    match tenv s, resultTypeOf tenv op with
    | some sty, some oty =>
      let idxTys := String.intercalate ", "
        (idxs.map fun k => ppTensorType ((tenv k).getD { shape := [], elem := .i64 }))
      let inTys := if idxTys.isEmpty then ppTensorType sty else s!"{ppTensorType sty}, {idxTys}"
      s!"%{d} = stablehlo.dynamic_slice {opsStr}, sizes = {ppNatList sizes}"
        ++ s!" : ({inTys}) -> {ppTensorType oty}"
    | _, _ =>
      ppTyped d s!"stablehlo.dynamic_slice {opsStr}, sizes = {ppNatList sizes}"
        (some { shape := sizes, elem := .i64 })
  | .dotGeneral d a b lb rb lc rc shape =>
    match resultTypeOf tenv op, tenv a, tenv b with
    | some _, some ta, some tb => ppDot d a b lb rb lc rc shape ta tb
    | _, _, _ =>
      s!"%{d} = stablehlo.dot_general %{a}, %{b},"
        ++ s!" contracting_dims = {ppNatList lc} x {ppNatList rc}"
        ++ s!" : (tensor<i64>, tensor<i64>) -> tensor<{ppShape shape}xi64>"
  | .reduce d s i dims body shape =>
    match resultTypeOf tenv op, tenv s, tenv i with
    | some _, some ts, some ti => ppReduce d s i dims body shape ts ti
    | _, _, _ =>
      let out := ppTensorType { shape := shape, elem := .i64 }
      s!"%{d} = stablehlo.reduce(%{s} init: %{i}) across dimensions = {ppNatList dims} : {out}"
  | .convert d s e =>
    match resultTypeOf tenv op, tenv s with
    | some _, some ty =>
      let out := ppTensorType { ty with elem := e }
      s!"%{d} = stablehlo.convert %{s} : ({ppTensorType ty}) -> {out}"
    | _, _ =>
      s!"%{d} = stablehlo.convert %{s} : (tensor<i64>) -> tensor<{ppElemType e}>"
  | .returnOp s =>
    match tenv s with
    | some ty => s!"return %{s} : {ppTensorType ty}"
    | none => s!"return %{s} : tensor<i64>"

def ppBody (tenv : TypeEnv) : List StableHLOOp → List String
  | [] => []
  | op :: rest =>
    ("    " ++ ppStableHLOOp tenv op) :: ppBody (bindResult tenv op) rest

def ppFuncOp (f : FuncOp) : String :=
  let params := String.intercalate ", " (f.params.map fun (n, ty) => s!"%{n}: {ppTensorType ty}")
  let tenv0 := f.params.foldl (fun e (n, ty) => e.bind n ty) TypeEnv.empty
  let body := String.intercalate "\n" (ppBody tenv0 f.body)
  s!"  func.func @{f.name}({params}) -> {ppTensorType f.result} \{\n{body}\n  }"

def ppModuleOp (m : ModuleOp) : String :=
  let funcs := String.intercalate "\n\n" (m.funcs.map ppFuncOp)
  s!"module @{m.name} \{\n{funcs}\n}"

def bindArgs (env : Env) : List (String × TensorType) → List TensorVal → Except ShapeError Env
  | [], [] => .ok env
  | (n, ty) :: ps, v :: vs =>
    if v.ty != ty then .error (.typeMismatch ty v.ty)
    else do
      checkWellFormed v
      bindArgs (env.bind n v) ps vs
  | _, _ => .error (.rankMismatch 0 0)

/-- Evaluate a function body against concrete arguments and check the returned type. -/
def evalFuncOp (f : FuncOp) (args : List TensorVal) : Except ShapeError TensorVal := do
  if args.length != f.params.length then
    .error (.rankMismatch f.params.length args.length)
  else
    let env ← bindArgs Env.empty f.params args
    let env' ← evalOps env f.body
    match f.body.getLast? with
    | some (.returnOp name) =>
      let v ← lookup env' name
      if v.ty != f.result then .error (.typeMismatch f.result v.ty) else .ok v
    | _ => .error (.shapeMismatch "func body does not return")

def evalModuleOp (m : ModuleOp) (func : String) (args : List TensorVal) :
    Except ShapeError TensorVal :=
  match m.funcs.find? fun f => f.name == func with
  | none => .error (.unbound func)
  | some f => evalFuncOp f args

end LeanNative.Backend.StableHLOAst
