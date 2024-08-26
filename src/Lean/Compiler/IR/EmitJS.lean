/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Runtime
import Lean.Compiler.NameMangling
import Lean.Compiler.ExportAttr
import Lean.Compiler.InitAttr
import Lean.Compiler.IR.CompilerM
import Lean.Compiler.IR.EmitUtil
import Lean.Compiler.IR.NormIds
import Lean.Compiler.IR.SimpCase
import Lean.Compiler.IR.Boxing

namespace Lean.IR.EmitJS
open ExplicitBoxing (requiresBoxedVersion mkBoxedName isBoxedName)

/--
The main function that is going to run the entire application.
-/
def leanMainFn := "lean_main"

/--
The compilation context.
-/
structure Context where
  env          : Environment
  modName      : Name
  joinPointMap : JPParamsMap := {}
  mainFn       : FunId := default
  mainParams   : Array Param := #[]
  indent       : String := ""

/--
The compilation monad.
-/
abbrev CompileM := ReaderT Context (EStateM String String)

namespace CompileM

def throwUnknownVar {α : Type} (x : VarId) : CompileM α :=
  throw s!"unknown variable '{x}'"

@[inline]
def getEnv : CompileM Environment :=
  Context.env <$> read

@[inline]
def getModName : CompileM Name :=
  Context.modName <$> read

def getDecl (n : Name) : CompileM Decl := do
  let env ← getEnv
  match findEnvDecl env n with
  | some d => pure d
  | none   => throw s!"unknown declaration '{n}'"

@[inline]
def scope : CompileM α → CompileM α :=
  ReaderT.adapt (λctx => {ctx with indent := ctx.indent ++ "    "})

@[inline]
def emit {α : Type} [ToString α] (a : α) : CompileM Unit :=
  modify fun out => out ++ toString a

@[inline]
def emitLn {α : Type} [ToString α] (a : α) : CompileM Unit := do
  emit a;
  emit "\n"

@[inline]
def invalidExportName {α : Type} (n : Name) : CompileM α :=
  throw s!"invalid export name '{n}'"

end CompileM

namespace JS

/--
Mangle a `Name` into a Javascript name that contains $ instead of dots.
-/
def mangle (n : Name) (pre : String := "") : String :=
    pre ++ jsMangleAux n
  where
    jsMangleAux : Name → String
      | Name.anonymous => ""
      | Name.str p s =>
        let m := String.mangle s
        match p with
        | Name.anonymous => m
        | p => jsMangleAux p ++ "$" ++ m
      | Name.num p n => jsMangleAux p ++ "$" ++ toString n ++ "$"

/--
Compiles an `Arg` to a javascript `Arg`.
-/
def arg : Arg → String
  | Arg.var x => toString x
  | _ => "_"

/--
Transforms a `Name` tos omething that is supported in JS.
-/
def toName (n : Name) : CompileM String := do
  let env ← CompileM.getEnv;
  match getExportNameFor? env n with
  | some (.str .anonymous s) => pure s
  | some _ => CompileM.invalidExportName n
  | none => if n == `main then pure leanMainFn else pure (mangle n)

/--
To JS Init name
-/
def toInitName (n : Name) : CompileM String := do
  let env ← CompileM.getEnv;
  -- TODO: we should support simple export names only
  match getExportNameFor? env n with
  | some (.str .anonymous s) => return "_init_" ++ s
  | some _ => CompileM.invalidExportName n
  | none => pure ("_init_" ++ (mangle n))

namespace Emit

@[inline]
def text (text : String) : CompileM Unit :=
  CompileM.emit text

@[inline]
def indent : CompileM Unit :=
  CompileM.emit =<< Context.indent <$> read

@[inline]
def emitArg (arg : Arg) : CompileM Unit :=
  CompileM.emit <| JS.arg arg

@[inline]
def comment (a : CompileM Unit) : CompileM Unit := do
  CompileM.emit "//";
  a
  CompileM.emit "\n"

/--
Emits a JS name
-/
@[inline]
def nl : CompileM Unit :=
  CompileM.emit "\n"

/--
Emits a semicolon.
-/
@[inline]
def semi : CompileM Unit :=
  CompileM.emit ";"

/--
Emits a JS name
-/
@[inline]
def name (n : Name) : CompileM Unit :=
  toName n >>= CompileM.emit

/--
Emits a JS Init name
-/
@[inline]
def initName (n : Name) : CompileM Unit :=
  toInitName n >>= CompileM.emit

/--
Pretty prints an array
-/
@[inline]
def array [Inhabited α] (emit : α → CompileM Unit) (array: Array α) (sep : String := "") : CompileM Unit :=
  array.size.forM fun i => do
    if i > 0 ∧ sep ≠ "" then text sep
    emit array[i]!

/--
Emits a JS Function
-/
@[inline]
def emitFunction (fname : String) (args : Array String) (body : CompileM Unit) : CompileM Unit := do
  indent; text "\nfunction ";
  text fname;
  text "(";
  array text args (sep := ", ");
  text ")";
  text " {";
  nl
  let res ← CompileM.scope body
  indent; text "}"; nl
  return res

/--
Emits a JS block `{ }`
-/
@[inline]
def emitJSBlock (body : CompileM Unit) : CompileM Unit := do
  text "{"; nl
  let res ← CompileM.scope body
  nl; indent; text "}"; nl
  return res

/--
Emits a JS `let` declaration
-/
@[inline]
def emitLet (lname : String) (value : Option (CompileM Unit) := none) : CompileM Unit := do
  indent; text "let ";
  text lname;

  if let some val := value then
    text " = ";
    discard <| val

  text ";";
  nl

/--
Emits a JS `let` declaration
-/
@[inline]
def emitConst (lname : String) (value : CompileM Unit) : CompileM Unit := do
  indent; text "const ";
  text lname;

  text " = ";
  value

  text ";";
  nl
/--
Emits a JS set variable declaration
-/
@[inline]
def emitSet (lname : String) (value : (CompileM Unit)) : CompileM Unit := do
  indent; text lname;

  text " = ";
  discard <| value

  semi
  nl

/--
Emits a JS function call
-/
@[inline]
def emitCall (fname : String) (args : Array (CompileM Unit) := #[]) : CompileM Unit := do
  text fname;
  text "(";
  array id args (sep := ", ");
  text ")";

/--
Emits a JS function call with compileM as name
-/
@[inline]
def emitCall' (fname : CompileM Unit) (args : Array (CompileM Unit) := #[]) : CompileM Unit := do
  fname;
  text "(";
  array id args (sep := ", ");
  text ")";
/--
Emits statement
-/
@[inline]
def stmt (comp : CompileM Unit) : CompileM Unit := do
  indent;
  comp;
  semi;
  nl

/--
Emits a JS `if` statement
-/
@[inline]
def emitJSIf (cond : CompileM Unit) (thenBody : CompileM Unit) (elseBody? : Option (CompileM Unit) := none) : CompileM Unit := do
  indent; text "if (";
  discard <| cond;
  text ") {"; nl
  let _ ← CompileM.scope thenBody;
  indent; text "}";
  if let some elseBody := elseBody? then
    text " else {"; nl
    let _ ← CompileM.scope elseBody;
    indent; text "}";
  nl
/--
Emits a JS `if` statement
-/
@[inline]
def emitIfElse (cond : CompileM Unit) (thenBody : CompileM Unit) (elseBody? : CompileM Unit) : CompileM Unit := do
  emitJSIf cond thenBody elseBody?

/--
Emits a JS `switch` statement
-/
@[inline]
def emitSwitch (expr : CompileM Unit) (cases : Array (CompileM Unit × CompileM Unit)) (default? : Option (CompileM Unit) := none) : CompileM Unit := do
  indent; text "switch (";
  discard <| expr;
  text ") {"; nl
  for (caseExpr, caseBody) in cases do
    indent; text "case ";
    discard <| caseExpr;
    text ":";
    let _ ← CompileM.scope (emitJSBlock caseBody); nl
  if let some defaultBody := default? then
    indent; text "default:"; nl
    let _ ← CompileM.scope defaultBody
    nl
  indent; text "}"; nl

/--
Emits a JS `while` loop with label
-/
@[inline]
def emitWhile (label : Option String := none) (cond : CompileM Unit) (body : CompileM Unit) : CompileM Unit := do
  indent
  match label with
  | some lbl => do text lbl; text ": ";
  | none => pure ()
  text "while (";
  discard <| cond;
  text ") {"; nl
  let _ ← CompileM.scope body;
  indent; text "}"; nl

/--
Emits a JS block `{ }`
-/
@[inline]
def emitIndex (name : String) (index : String) : CompileM Unit := do
  text name
  text "["
  text index
  text "]"

/--
Emits a JS `return` statement
-/
@[inline]
def emitReturn (value : CompileM Unit) : CompileM Unit := do
  indent; text "return ";
  let val ← value;
  text ";";
  nl
  return val

/--
Emits a JS `continue` statement
-/
@[inline]
def emitContinue (label? : Option String := none) : CompileM Unit := do
  indent; text "continue";
  if let some lbl := label? then
    text " "; text lbl;
  text ";";
  nl

/--
Emits a JS function call as a statement
-/
@[inline]
def emitStmtCall (fname : String) (args : Array (CompileM Unit) := #[]) : CompileM Unit := do
  stmt <| emitCall fname args

end Emit
end JS

def getJPParams (j : JoinPointId) : CompileM (Array Param) := do
  let ctx ← read;
  match ctx.joinPointMap[j]? with
  | some ps => pure ps
  | none    => throw "unknown join point"

namespace Emit
open CompileM
open JS JS.Emit

def mkWorld : CompileM Unit :=
  emitCall "lean_io_mk_world"

def setPanicMessage (enable : Bool) : CompileM Unit :=
  emitStmtCall "lean_set_panic_messages" #[text $ toString enable]

def initializeLean : CompileM Unit :=
  emitStmtCall "lean_initialize"

def initializeLeanRuntimeModule : CompileM Unit :=
  emitStmtCall "lean_initialize_runtime_module"

def markEndInitialization : CompileM Unit :=
  emitStmtCall "lean_io_mark_end_initialization"

def finalizeTaskManager : CompileM Unit :=
  emitStmtCall "lean_finalize_task_manager"

def initializeTaskManager : CompileM Unit :=
  emitStmtCall "lean_init_task_manager"

def isResultOk (res : CompileM Unit) : CompileM Unit :=
  emitCall "lean_io_result_is_ok" #[res]

def getResultValue (res : CompileM Unit) : CompileM Unit :=
  emitCall "lean_io_result_get_value" #[res]

def showError (res : CompileM Unit) : CompileM Unit :=
  emitStmtCall "lean_io_result_show_error" #[res]

def decrementRef (res : CompileM Unit) : CompileM Unit :=
  emitStmtCall "lean_dec_ref" #[res]

def ctorAlloc (tag : String) (numFields : String) (fieldSize : String) : CompileM Unit :=
  emitCall "lean_alloc_ctor" #[text tag, text numFields, text fieldSize]

def ctorSet (obj : String) (place : String) (value : String) : CompileM Unit :=
  emitCall "lean_ctor_set" #[text obj, text place, text value]

def string (name : String) : CompileM Unit :=
  Emit.text s!"\"{name}\""

def emitCallOrVar (name : String) (args : Array (CompileM Unit)) : CompileM Unit :=
  if args.size > 0 then
    emitCall name args
  else
    emit name

def emitCallOrVar' (name : CompileM Unit) (args : Array (CompileM Unit)) : CompileM Unit :=
  if args.size > 0 then
    emitCall' name args
  else
    name


/--
Emits the main function.
-/
def emitMainFn : CompileM Unit := do
  match (← CompileM.getDecl `main) with
  | .fdecl (xs := params) .. => do
    unless params.size = 2 ∨ params.size = 1 do
      throw "invalid main function, incorrect arity when generating code"

    let env ← CompileM.getEnv
    let usesLeanAPI := usesModuleFrom env `Lean

    Emit.emitFunction "main" #["argc", "argv"] do
      emitLet "bin";
      emitLet "result"

      if usesLeanAPI then
        initializeLean
      else
        initializeLeanRuntimeModule

      let modName ← getModName
      let initName := mkModuleInitializationFunctionName modName

      setPanicMessage false
      emitSet "result" (emitCall initName #[text "1", mkWorld])
      setPanicMessage true
      markEndInitialization

      emitJSIf
        -- Cond
        do isResultOk (text "res")
        --- Then branch
        do
          decrementRef (text "res")
          initializeTaskManager
          if params.size = 2 then
              emitSet "bin" (text "0")
              emitLet "i" (text "argc")
              emitWhile none (text "i > 1") do
                emitLet "n"
                stmt (text "i--")
                emitSet "n" (ctorAlloc "1" "2" "0")
                stmt (ctorSet "n" "0" "argv[i]")
                stmt (ctorSet "n" "1" "bin")
                emitSet "res" (emitCall leanMainFn #[text "bin", mkWorld])
            else
                emitSet "res" (emitCall leanMainFn #[mkWorld])
        -- Else
        none

      finalizeTaskManager

      let retTy := env.find? `main |>.get! |>.type |>.getForallBody
      let retTy := retTy.appArg!

      emitJSIf
        do isResultOk (text "res")
        do emitLet "ret" (text <| if retTy.constName? == some ``UInt32 then "lean_io_result_get_value(res)" else "0")
           decrementRef (text "res")
           emitReturn (text "ret")
        (some <|
          do showError (text "res")
             decrementRef (text "res")
             emitReturn (text "ret"))

  | _ => throw "function declaration expected"

/--
Emits the file header.
-/
def emitFileHeader : CompileM Unit := do
  let env ← CompileM.getEnv
  let modName ← getModName
  comment (do text "Lean JS compiler output")
  comment (do text ("Module: " ++ toString modName))
  comment (do text "Imports:"; array emit env.imports (sep := " "))

def emitFnDeclAux (decl : Decl) (cppBaseName : String) (isExternal : Bool) : CompileM Unit := do
  let ps := decl.params

  if isExternal then
    emitFunction cppBaseName #[] (pure ())

  if ps.isEmpty then
    emitLet cppBaseName

/--
Emits a function declaration.
-/
def emitFnDecl (decl : Decl) (isExternal : Bool) : CompileM Unit := do
  let cppBaseName ← JS.toName decl.name
  emitFnDeclAux decl cppBaseName isExternal

/--
Emits an external declaration.
-/
def emitExternDeclAux (decl : Decl) (cNameStr : String) : CompileM Unit := do
  let env ← CompileM.getEnv
  let extC := isExternC env decl.name
  emitFnDeclAux decl cNameStr extC

def getJPParams (j : JoinPointId) : CompileM (Array Param) := do
  let ctx ← read;
  match ctx.joinPointMap[j]? with
  | some ps => pure ps
  | none    => throw "unknown join point"

def declareParams (ps : Array Param) : CompileM Unit :=
  ps.forM fun p => emitLet (toString p.x)

partial def declareVars : FnBody → Bool → CompileM Bool
  | e@(FnBody.vdecl x _ _ b), d => do
    if isTailCallTo (← read).mainFn e
      then pure d
      else emitLet (toString x); declareVars b true
  | FnBody.jdecl _ xs _ b, d => do declareParams xs; declareVars b (d || xs.size > 0)
  | e, d => if e.isTerminal then pure d else declareVars e.body d

def Acc := Array (String × FnBody)

def emitTag (x : String) (xType : IRType) : CompileM Unit := do
  if xType.isObj then
    emitCall "lean_obj_tag" #[text x]
  else
    Emit.text x

def emitInc (x : VarId) (n : Nat) (checkRef : Bool) : CompileM Unit := do
  let fn := if checkRef then (if n == 1 then "lean_inc" else "lean_inc_n") else (if n == 1 then "lean_inc_ref" else "lean_inc_ref_n")
  emitStmtCall fn #[emit x, text (toString n)]

def emitDec (x : VarId) (n : Nat) (checkRef : Bool) : CompileM Unit := do
  let fn := if checkRef then "lean_dec" else "lean_dec_ref"
  emitStmtCall fn #[emit x, text (toString n)]

def emitDel (x : VarId) : CompileM Unit := do
  emitStmtCall "lean_free_object" #[emit x]

def emitSetTag (x : VarId) (i : Nat) : CompileM Unit := do
  emitStmtCall "lean_ctor_set_tag" #[emit x, text (toString i)]

def emitCtorSet (x : VarId) (i : Nat) (y : String) : CompileM Unit := do
  emitStmtCall "lean_ctor_set" #[emit x, text (toString i), text y]

def emitOffset (n : Nat) (offset : Nat) : CompileM Unit := do
  if n > 0 then
    Emit.text $ "8 * " ++ toString n ++ (if offset > 0 then " + " ++ toString offset else "")
  else
    Emit.text (toString offset)

def emitUSet (x : String) (n : Nat) (y : String) : CompileM Unit := do
  emitStmtCall "lean_ctor_set_usize" #[text x, text (toString n), text y]

def emitSSet (x : String) (n : Nat) (offset : Nat) (y : String) (_t : IRType) : CompileM Unit := do
  emitStmtCall "lean_ctor_set_scalar" #[text x, (emitOffset n offset), text y]

def isTailCall (x : VarId) (v : Expr) (b : FnBody) : CompileM Bool := do
  let ctx ← read;
  match v, b with
  | Expr.fap f _, FnBody.ret (Arg.var y) => return f == ctx.mainFn && x == y
  | _, _ => pure false

def paramEqArg (p : Param) (x : Arg) : Bool :=
  match x with
  | Arg.var x => p.x == x
  | _ => false

def overwriteParam (ps : Array Param) (ys : Array Arg) : Bool :=
  let n := ps.size;
  n.any fun i =>
    let p := ps[i]!
    (i+1, n).anyI fun j => paramEqArg p ys[j]!

def emitTailCall (v : Expr) : CompileM Unit :=
  match v with
  | Expr.fap _ ys => do
    let ctx ← read
    let ps := ctx.mainParams
    unless ps.size == ys.size do throw "invalid tail call"
    if overwriteParam ps ys then
      emitJSBlock do
        ps.size.forM fun i => do
          let p := ps[i]!
          let y := ys[i]!
          unless paramEqArg p y do
            emitLet s!"_temp_{i}" (emitArg y)
        ps.size.forM fun i => do
          let p := ps[i]!
          let y := ys[i]!
          unless paramEqArg p y do
            emitSet (toString p.x) (text s!"_tmp_{i}")
    else
      ys.size.forM fun i => do
        let p := ps[i]!
        let y := ys[i]!
        unless paramEqArg p y do
          emitSet (toString p.x) (emitArg y)
    emitContinue "function_loop"
  | _ => throw "bug at emitTailCall"

def isIf (alts : Array Alt) : Option (Nat × FnBody × FnBody) :=
  if alts.size != 2 then none
  else match alts[0]! with
    | Alt.ctor c b => some (c.cidx, b, alts[1]!.body)
    | _            => none

def emitJmp (j : JoinPointId) (xs : Array Arg) : CompileM Unit := do
  let ps ← getJPParams j
  unless xs.size == ps.size do throw "invalid goto"
  xs.size.forM fun i => do
    let p := ps[i]!
    let x := xs[i]!
    emitSet (toString p.x) (emitArg x)
  emitSet "state" (text <| s!"\"{toString j}\"")
  emitContinue "function_loop"

def toHexDigit (c : Nat) : String :=
  String.singleton c.digitChar

def quoteString (s : String) : String :=
  let q := "\"";
  let q := s.foldl
    (fun q c => q ++
      if c == '\n' then "\\n"
      else if c == '\r' then "\\r"
      else if c == '\t' then "\\t"
      else if c == '\\' then "\\\\"
      else if c == '\"' then "\\\""
      else if c == '?' then "\\?" -- avoid trigraphs
      else if c.toNat <= 31 then
        "\\x" ++ toHexDigit (c.toNat / 16) ++ toHexDigit (c.toNat % 16)
      -- TODO(Leo): we should use `\unnnn` for escaping unicode characters.
      else String.singleton c)
    q;
  q ++ "\""

def emitIsShared (z : VarId) (x : VarId) : CompileM Unit := do
  emitSet (toString z) (emitCall "!lean_is_exclusive" #[emit x])

def emitLit (z : VarId) (v : LitVal) : CompileM Unit := do
  let lit := match v with
    | LitVal.num v => emit v
    | LitVal.str v => emit (quoteString v)
  emitSet (toString z) lit

def emitUnbox (z : VarId) (x : VarId) : CompileM Unit := do
  emitSet (toString z) (emit x)

def emitBox (z : VarId) (x : VarId) : CompileM Unit := do
  emitSet (toString z) (emit x)

def emitApp (z : VarId) (f : VarId) (ys : Array Arg) : CompileM Unit :=
  if ys.size > closureMaxArgs then do
    emitJSBlock do
      emitLet "_aargs" (some (do text "["; array emitArg ys (sep := ", "); text "]"))
      emitSet (toString z) (emitCall "lean_apply_m" #[emit f, emit ys.size, text "_aargs"])
  else do
    emitSet (toString z) (emitCall s!"lean_apply_{ys.size}" (#[emit f] ++ ys.map emitArg))

def emitPartialApp (z : VarId) (f : FunId) (ys : Array Arg) : CompileM Unit := do
  let decl ← CompileM.getDecl f
  let arity := decl.params.size;
  emitSet (toString z) (emitCall "lean_alloc_closure" #[name f, emit arity, emit ys.size])
  ys.size.forM fun i => do
    let y := ys[i]!
    emitStmtCall "lean_closure_set" #[emit z, emit i, emitArg y]

def toStringArgs (ys : Array Arg) : List String :=
  ys.toList.map arg

def emitSimpleExternalCall (f : String) (ps : Array Param) (ys : Array Arg) : CompileM Unit := do
  let res ← ys.size.foldM (init := #[]) fun i n =>
      if ps[i]!.ty.isIrrelevant
        then pure n
        else pure (n.push (emitArg ys[i]!))

  emitCall f res

def emitExternCall (f : FunId) (ps : Array Param) (extData : ExternAttrData) (ys : Array Arg) : CompileM Unit :=
  match getExternEntryFor extData `c with
  | some (ExternEntry.standard _ extFn) => emitSimpleExternalCall extFn ps ys
  | some (ExternEntry.inline _ pat)     => do emit (expandExternPattern pat (toStringArgs ys));
  | some (ExternEntry.foreign _ extFn)  => emitSimpleExternalCall extFn ps ys
  | _ => throw s!"failed to emit extern application '{f}'"

def emitFullApp (z : VarId) (f : FunId) (ys : Array Arg) : CompileM Unit := do
  let decl ← CompileM.getDecl f

  emitSet (toString z) do
    match decl with
    | Decl.extern _ ps _ extData => emitExternCall f ps extData ys
    | _ => emitCallOrVar' (name f) (ys.map emitArg)

def emitProj (z : VarId) (i : Nat) (x : VarId) : CompileM Unit := do
  emitSet (toString z) (emitCall "lean_ctor_get" #[emit x, emit i])

def emitUProj (z : VarId) (i : Nat) (x : VarId) : CompileM Unit := do
  emitSet (toString z) (emitCall "lean_ctor_get" #[emit x, emit i])

def emitSProj (z : VarId) (n : Nat) (x : VarId) : CompileM Unit := do
  emitSet (toString z) (emitCall "lean_ctor_get" #[emit x, emit n])

def emitAllocCtor (c : CtorInfo) : CompileM Unit := do
  emitCall "lean_alloc_ctor" #[emit c.cidx, emit c.size, emit (c.ssize + c.usize)]

def emitCtorSetArgs (z : VarId) (ys : Array Arg) : CompileM Unit :=
  ys.size.forM fun i => do
    stmt <| emitCall "lean_ctor_set" #[emit z, emit i, emitArg ys[i]!]

def emitCtor (z : VarId) (c : CtorInfo) (ys : Array Arg) : CompileM Unit := do
  if c.size == 0 && c.usize == 0 && c.ssize == 0 then do
    emitSet (toString z) (emit c.cidx)
  else do
    emitSet (toString z) (emitAllocCtor c);
    emitCtorSetArgs z ys

def emitReset (z : VarId) (n : Nat) (x : VarId) : CompileM Unit := do
  emitJSIf (emitCall "lean_is_exclusive" #[emit x])
    (do
      n.forM fun i => do emitCall "lean_ctor_release" #[emit x, emit i]
      emitSet (toString z) (emit x))
    (some do
      decrementRef (emit x)
      emitSet (toString z) (emit 0))

def emitReuse (z : VarId) (x : VarId) (c : CtorInfo) (updtHeader : Bool) (ys : Array Arg) : CompileM Unit := do
  emitJSIf (emitCall "lean_is_scalar" #[emit x])
    (emitSet (toString z) (emitAllocCtor c))
    (emitSet (toString z) (emit x))

  if updtHeader then
    emitStmtCall "lean_ctor_set_tag" #[emit z, emit c.cidx]
    emitCtorSetArgs z ys

def emitVDecl (z : VarId) (v : Expr) : CompileM Unit :=
  match v with
  | .ctor c ys => emitCtor z c ys
  | .reset n x => emitReset z n x
  | .reuse x c u ys => emitReuse z x c u ys
  | .proj i x => emitProj z i x
  | .uproj i x => emitUProj z i x
  | .sproj n _ x => emitSProj z n x
  | .fap c ys => emitFullApp z c ys
  | .pap c ys => emitPartialApp z c ys
  | .ap x ys => emitApp z x ys
  | .box _ x => emitBox z x
  | .unbox x => emitUnbox z x
  | .isShared x => emitIsShared z x
  | .lit v => emitLit z v

mutual

partial def emitIf (x : VarId) (xType : IRType) (tag : Nat) (t : FnBody) (e : FnBody) : CompileM Unit := do
  emitJSIf (do emitTag (toString x) xType; text " == "; emit tag) (emitBlock t) (emitBlock e)

partial def emitCase (x : VarId) (xType : IRType) (alts : Array Alt) : CompileM Unit :=
  match isIf alts with
  | some (tag, t, e) => emitIf x xType tag t e
  | _ => do
    let mut newAlts := #[]
    let mut default := none
    let alts := ensureHasDefault alts;

    for alt in alts do
      match alt with
      | .ctor c b => newAlts := newAlts.push (emit c.cidx, emitBlock b)
      | .default b => default := some (emitBlock b)

    emitSwitch (emitTag (toString x) xType) newAlts default

partial def emitBlock : FnBody → CompileM Unit
  | d@(.vdecl x _ v b) => do
    let ctx ← read
    if isTailCallTo ctx.mainFn d then
      emitTailCall v
    else
      emitVDecl x v
      emitBlock b
  | .inc x n c p b => do
    unless p do emitInc x n c
    emitBlock b
  | .dec x n c p b => do
    unless p do emitDec x n c
    emitBlock b
  | .jdecl _ _  _ b => do emitBlock b
  | .del x b => do emitDel x; emitBlock b
  | .setTag x i b => do emitSetTag x i; emitBlock b
  | .set x i y b => do emitCtorSet x i (arg y); emitBlock b
  | .uset x i y b => do emitUSet (toString x) i (toString y); emitBlock b
  | .sset x i o y t b => do emitSSet (toString x) i o (toString y) t; emitBlock b
  | .mdata _ b => do emitBlock b
  | .ret x => do emitReturn (emitArg x);
  | .case _ x xType alts => do emitCase x xType alts
  | .jmp j xs => do emitJmp j xs
  | .unreachable => emitLn "lean_internal_panic_unreachable();"

partial def accJPs (array : Acc) : FnBody → Acc
  | FnBody.jdecl j _  v b => let acc := accJPs (array.push (s!"\"{j}\"", v)) v; accJPs acc b
  | e => if e.isTerminal then array else accJPs array e.body

partial def emitFnBody (b : FnBody) : CompileM (Array (String × FnBody)) := do
  return accJPs #[("\"_start\"", b)] b

end

def emitFDecl (decl : Decl) (mainFn : FunId) (mainParams : Array Param) (b : FnBody) : CompileM Unit := do
  let baseName ← JS.toName mainFn
  let funName := if mainParams.size > 0 then baseName else "_init_" ++ baseName

  let isBoxedOrClosure := mainParams.size > closureMaxArgs && isBoxedName decl.name

  let args := if isBoxedOrClosure
    then #["args"]
    else mainParams.map (toString ∘ Param.x)

  emitFunction funName args do
    if isBoxedOrClosure then
      mainParams.size.forM fun idx =>
        let param := mainParams[idx]!
        emitLet (toString param.x) (emitIndex "_args" (toString idx))

    let alts ← withReader (fun ctx => { ctx with mainFn, mainParams }) (scope (emitFnBody b))

    let declared ← declareVars b false
    if declared then emitLn ""

    if alts.size > 1 then
      emitLet "state" (string "_start")
      emitWhile (label := some "function_loop")
        do text "true"
        do let conds := alts.map (λ(x, y) => (text x, emitBlock y))
           emitSwitch (text "state") conds
    else
      emitBlock alts[0]!.2


def emitDeclAux (d : Decl) : CompileM Unit := do
  let env ← CompileM.getEnv
  let (_, joinPointMap) := mkVarJPMaps d

  withReader (fun ctx => { ctx with joinPointMap }) do
    unless hasInitAttr env d.name do
      match d with
      | .fdecl (f := f) (xs := xs) (body := b) .. => emitFDecl d f xs b
      | _ => pure ()

/--
Emits a declaration.
-/
def emitDecl (d : Decl) : CompileM Unit := do
  let d := d.normalizeIds;
  try
    emitDeclAux d
  catch err =>
    throw s!"{err}\ncompiling:\n{d}"

/--
Emit a collection of declarations.
-/
def emitFns : CompileM Unit := do
  let env ← CompileM.getEnv
  let decls := getDecls env
  decls.reverse.forM emitDecl

/--
Emits a persistence call.
-/
def emitMarkPersistent (d : Decl) (n : Name) : CompileM Unit := do
  if d.resultType.isObj then
    emitStmtCall "lean_mark_persistent" #[Emit.name n]

/--
Emits the function declarations and variables.
-/
def emitFnDecls : CompileM Unit := do
  let env ← CompileM.getEnv
  let decls := getDecls env
  let modDecls  : NameSet := decls.foldl (fun s d => s.insert d.name) {}
  let usedDecls : NameSet := decls.foldl (fun s d => collectUsedDecls env d (s.insert d.name)) {}
  let usedDecls := usedDecls.toList

  usedDecls.forM fun n => do
    let decl ← CompileM.getDecl n;
    match getExternNameFor env `c decl.name with
    | some cName => emitExternDeclAux decl cName
    | none => emitFnDecl decl (!modDecls.contains n)

def hasMainFn : CompileM Bool := do
  let env ← CompileM.getEnv
  let decls := getDecls env
  return decls.any (fun d => d.name == `main)

def emitMainFnIfNeeded : CompileM Unit := do
  if (← hasMainFn) then emitMainFn

def emitDeclInit (d : Decl) : CompileM Unit := do
  let env ← CompileM.getEnv
  let n := d.name
  if isIOUnitInitFn env n then
    let action := do
      emitSet "res" (emitCall' (name n) #[mkWorld])
      emitJSIf (emitCall "lean_io_result_is_error" #[text "res"])
        (emitReturn (text "res"))
      decrementRef (text "res")
    if isIOUnitBuiltinInitFn env n then emitJSIf (text "builtin") action else action
  else if d.params.size == 0 then
    match getInitFnNameFor? env d.name with
    | none => emitSet (mangle n) (emitCall' (name n) #[]); emitMarkPersistent d n
    | some initFn => do
      let needIf := getBuiltinInitFnNameFor? env d.name |>.isSome
      let action := do
        emitSet "res" (emitCall' (name initFn) #[mkWorld])
        emitJSIf (emitCall "lean_io_result_is_error" #[emit "res"]) (emitReturn (emit "res"))
        emitSet (mangle n) (getResultValue (emit "res"))

        unless d.resultType.isScalar do
          emitMarkPersistent d n

        decrementRef (emit "res")

      if needIf then emitJSIf (text "builtin") action else action

def emitInitFn : CompileM Unit := do
  let env ← CompileM.getEnv
  let modName ← getModName

  /-
  env.imports.forM fun imp =>
    emitLn ("lean_object* " ++ mkModuleInitializationFunctionName imp.module ++ "(uint8_t builtin, lean_object*);")
  -/

  emitLet "Ginit" (emit false)

  emitFunction (mkModuleInitializationFunctionName modName) #["builtin", "w"] do
    emitLet "res"

    emitJSIf (emit "GInit")
      (emitReturn mkWorld)
      none

    emitSet "GInit" (emit "true")

    env.imports.forM fun imp => do
      emitSet "res" (emitCall (toString <| mkModuleInitializationFunctionName imp.module) #[text "builtin", mkWorld])
      emitJSIf (emitCall "lean_io_result_is_error" #[emit "res"])
        (emitReturn (text "res"))
        none
      decrementRef (text "res")

    let decls := getDecls env
    decls.reverse.forM emitDeclInit
    emitReturn (text "0")

def main : CompileM Unit := do
  emitFileHeader
  emitFnDecls
  emitFns
  emitInitFn
  emitMainFnIfNeeded

end Emit
end EmitJS

@[export lean_ir_emit_js]
def emitJS (env : Environment) (modName : Name) : Except String String :=
  match (EmitJS.Emit.main { env := env, modName := modName }).run "" with
  | EStateM.Result.ok    _   s => Except.ok s
  | EStateM.Result.error err _ => Except.error err

end Lean.IR
