/-
Paper–Lean audit extractor.

Run inside the target project's Lake environment:

  lake env lean --run <paper-lean-audit>/lean/Extract.lean <config.json> <out.json>

The configuration names the modules to import, the declarations of the map, the
declarations whose proofs are traced, the library boundary and the namespaces
opened for pretty-printing (see README). The output is deterministic: keys and
lists are sorted, positions are line/column pairs and files are module-relative.
-/
import Lean

open Lean Meta Elab

namespace PaperLeanAudit

structure Config where
  imports : Array Name
  declarations : Array Name
  mapped : Array Name
  trace : Array Name
  projectModules : Array Name
  boundaryModules : Array Name
  boundaryNamespaces : Array Name
  opens : Array Name
  skipEarlierProofs : Bool
  followInstances : Bool
  unfoldMaxChars : Nat

def jsonNames (j : Json) (key : String) : Array Name :=
  match j.getObjValAs? (Array String) key with
  | .ok xs => xs.map String.toName
  | .error _ => #[]

def Config.ofJson (j : Json) : Config :=
  let decls := jsonNames j "declarations"
  let mapped := jsonNames j "mapped"
  { imports := jsonNames j "imports"
    declarations := decls
    mapped := if mapped.isEmpty then decls else mapped
    trace := jsonNames j "trace"
    projectModules := jsonNames j "project_modules"
    boundaryModules := jsonNames j "boundary_modules"
    boundaryNamespaces := jsonNames j "boundary_namespaces"
    opens := jsonNames j "open"
    skipEarlierProofs := (j.getObjValAs? Bool "skip_earlier_proofs").toOption.getD true
    followInstances := (j.getObjValAs? Bool "follow_instances").toOption.getD false
    unfoldMaxChars := (j.getObjValAs? Nat "unfold_max_chars").toOption.getD 6000 }

def hex64 (h : UInt64) : String :=
  let s := String.ofList (Nat.toDigits 16 h.toNat)
  String.ofList (List.replicate (16 - s.length) '0') ++ s

def userName (n : Name) : Name := (privateToUserName? n).getD n

/-- Sorted, deduplicated string array. -/
def sortStrings (xs : Array String) : Array String :=
  (xs.qsort (· < ·)).toList.eraseDups.toArray

def sortNames (s : NameSet) : Array String :=
  sortStrings (s.toArray.map (·.toString))

structure Ctx where
  cfg : Config
  env : Environment

def Ctx.moduleOf (c : Ctx) (n : Name) : Option Name :=
  match c.env.getModuleIdxFor? n with
  | some i => some c.env.header.moduleNames[i.toNat]!
  | none => if c.env.contains n then some c.env.mainModule else none

def Ctx.isProject (c : Ctx) (n : Name) : Bool :=
  match c.moduleOf n with
  | none => false
  | some m =>
    (c.cfg.projectModules.isEmpty || c.cfg.projectModules.any (·.isPrefixOf m)) &&
      !(c.cfg.boundaryModules.any (·.isPrefixOf m)) &&
      !(c.cfg.boundaryNamespaces.any (·.isPrefixOf (userName n)))

/-- Constructors, recursors, projections and auxiliary eliminators stand for
their inductive type. -/
partial def Ctx.owner (c : Ctx) (n : Name) : Name :=
  match c.env.find? n with
  | some (.ctorInfo i) => i.induct
  | some (.recInfo _) => n.getPrefix
  | _ =>
    if let some info := c.env.getProjectionFnInfo? n then c.owner info.ctorName
    else if isAuxRecursor c.env n || isNoConfusion c.env n then n.getPrefix
    else n

/-- Compiler and elaborator auxiliaries are followed but not listed. -/
def Ctx.isAux (c : Ctx) (n : Name) : Bool :=
  (userName n).isInternalDetail || isMatcherCore c.env n

def Ctx.isInstance (c : Ctx) (n : Name) : Bool := Meta.isInstanceCore c.env n

def kindOf (c : Ctx) (n : Name) : ConstantInfo → String
  | .thmInfo _ => "theorem"
  | .defnInfo _ => if c.isInstance n then "instance" else "def"
  | .axiomInfo _ => "axiom"
  | .opaqueInfo _ => "opaque"
  | .inductInfo i => if isStructure c.env n then (if isClass c.env n then "class" else "structure") else
      if i.isRec then "inductive" else "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"
  | .quotInfo _ => "quot"

def valueOf (ci : ConstantInfo) : Option Expr := ci.value? (allowOpaque := true)

/-- Hash of the type, or of the value, constructors and fields of a definition. -/
def typeHash (ci : ConstantInfo) : UInt64 :=
  mixHash (hash ci.levelParams) (hash ci.type)

def bodyHash (env : Environment) (ci : ConstantInfo) : UInt64 :=
  match ci with
  | .inductInfo i => i.ctors.foldl (init := hash i.numParams) fun h ctor =>
      match env.find? ctor with
      | some cc => mixHash h (mixHash (hash ctor) (hash cc.type))
      | none => h
  | _ => match valueOf ci with
    | some v => mixHash 0x9e3779b97f4a7c15 (hash v)
    | none => 0

/-! ### Statement context -/

partial def Ctx.context (c : Ctx) (roots : Array Name) : Array Name := Id.run do
  let mut todo := roots.toList
  let mut seen : NameSet := {}
  let mut out : NameSet := {}
  while true do
    match todo with
    | [] => break
    | n :: rest =>
      todo := rest
      let o := c.owner n
      if seen.contains o then continue
      seen := seen.insert o
      unless c.isProject o do continue
      let some ci := c.env.find? o | continue
      if ci matches .thmInfo _ then continue
      let mut next : Array Name := ci.type.getUsedConstants
      let follow := !c.isInstance o || c.cfg.followInstances
      if follow then
        if let some v := valueOf ci then next := next ++ v.getUsedConstants
      if let .inductInfo i := ci then
        for ctor in i.ctors do
          if let some cc := c.env.find? ctor then next := next ++ cc.type.getUsedConstants
      unless c.isAux o do out := out.insert o
      todo := next.toList ++ todo
  return (sortNames out).map String.toName

/-- Project definitions used directly by the type and body of `n` (through
auxiliaries, not through other definitions). -/
partial def Ctx.directDeps (c : Ctx) (n : Name) : Array Name := Id.run do
  let some ci := c.env.find? n | return #[]
  let start : Array Name := match ci with
    | .thmInfo _ => ci.type.getUsedConstants
    | .inductInfo i => ci.type.getUsedConstants ++ i.ctors.toArray.flatMap fun ctor =>
        ((c.env.find? ctor).map (·.type.getUsedConstants)).getD #[]
    | _ => ci.type.getUsedConstants ++
        (if c.isInstance n && !c.cfg.followInstances then #[] else
          ((valueOf ci).map (·.getUsedConstants)).getD #[])
  let mut todo := start.toList
  let mut seen : NameSet := ({} : NameSet).insert n
  let mut out : NameSet := {}
  while true do
    match todo with
    | [] => break
    | m :: rest =>
      todo := rest
      let o := c.owner m
      if seen.contains o then continue
      seen := seen.insert o
      unless c.isProject o do continue
      let some cj := c.env.find? o | continue
      if cj matches .thmInfo _ then continue
      if c.isAux o then
        let more := cj.type.getUsedConstants ++ ((valueOf cj).map (·.getUsedConstants)).getD #[]
        todo := more.toList ++ todo
      else out := out.insert o
  return (sortNames out).map String.toName

/-! ### Uses through unmapped helpers -/

structure Uses where
  mapped : NameSet := {}
  helpers : NameSet := {}
  library : NameSet := {}

partial def Ctx.uses (c : Ctx) (root : Name) : Uses := Id.run do
  let mappedSet : NameSet := c.cfg.mapped.foldl (·.insert ·) {}
  let some ci := c.env.find? root | return {}
  let some v := valueOf ci | return {}
  let mut todo := v.getUsedConstants.toList
  let mut seen : NameSet := ({} : NameSet).insert root
  let mut u : Uses := {}
  while true do
    match todo with
    | [] => break
    | n :: rest =>
      todo := rest
      if seen.contains n then continue
      seen := seen.insert n
      let some ci := c.env.find? n | continue
      if mappedSet.contains n && ci matches .thmInfo _ then
        u := { u with mapped := u.mapped.insert n }
        continue
      if c.isProject n then
        match ci with
        | .thmInfo _ =>
          unless c.isAux n do u := { u with helpers := u.helpers.insert n }
          if let some v := valueOf ci then todo := v.getUsedConstants.toList ++ todo
        | _ =>
          if c.isAux n then
            if let some v := valueOf ci then todo := v.getUsedConstants.toList ++ todo
      else if ci matches .thmInfo _ then
        u := { u with library := u.library.insert n }
  return u

/-- For each unmapped project theorem reachable from `roots`, the mapped
theorems it reaches (memoised depth-first search). -/
partial def Ctx.viaHelpers (c : Ctx) (roots : Array Name) : Std.HashMap Name NameSet := Id.run do
  let mappedSet : NameSet := c.cfg.mapped.foldl (·.insert ·) {}
  let mut memo : Std.HashMap Name NameSet := {}
  -- Iterative post-order to avoid deep recursion on long helper chains.
  let mut stack : List (Name × Bool) := roots.toList.map (·, false)
  while true do
    match stack with
    | [] => break
    | (n, done) :: rest =>
      stack := rest
      if memo.contains n then continue
      let deps := match c.env.find? n with
        | some ci => ((valueOf ci).map Expr.getUsedConstants).getD #[]
        | none => #[]
      let helpers := deps.filter fun d => !mappedSet.contains d && c.isProject d &&
        match c.env.find? d with
        | some (.thmInfo _) => true
        | some ci => c.isAux d && (valueOf ci).isSome
        | none => false
      if done then
        let mut acc : NameSet := {}
        for d in deps do
          if mappedSet.contains d && (c.env.find? d matches some (.thmInfo _)) then acc := acc.insert d
        for h in helpers do
          for m in memo.getD h {} do acc := acc.insert m
        memo := memo.insert n acc
      else
        stack := (n, true) :: (helpers.toList.filter (!memo.contains ·)).map (·, false) ++ stack
  return memo

/-! ### Pretty-printing -/

def Ctx.runMeta (c : Ctx) (ns : Name) (x : MetaM α) : IO α := do
  let openDecls := c.cfg.opens.toList.map fun n => OpenDecl.simple n []
  let opts : Options := ({} : Options)
    |>.set `maxHeartbeats (0 : Nat)
  let coreCtx : Core.Context := {
    fileName := "<paper-lean-audit>", fileMap := default, options := opts,
    currNamespace := ns, openDecls, maxHeartbeats := 0 }
  let coreSt : Core.State := { env := c.env.setExporting false }
  let x' : CoreM α := do
    for n in c.cfg.opens do activateScoped n
    x.run' {}
  let (a, _) ← x'.toIO coreCtx coreSt
  return a

def fmt (f : Format) : String := f.pretty 100

def posJson (p : Position) : Json := Json.arr #[toJson p.line, toJson p.column]

def rangeJson (r : DeclarationRange) : Json :=
  Json.mkObj [("start", posJson r.pos), ("end", posJson r.endPos)]

/-- Text of `[start, end)` given as line/column positions (columns in codepoints). -/
def sliceLines (lines : Array String) (s e : Position) : String := Id.run do
  let mut out : Array String := #[]
  for i in [s.line : e.line + 1] do
    let some l := lines[i - 1]? | continue
    let cs := l.toList
    let a := if i == s.line then s.column else 0
    let b := if i == e.line then e.column else cs.length
    out := out.push (String.ofList ((cs.drop a).take (b - a)))
  return "\n".intercalate out.toList

structure Sources where
  sp : SearchPath
  cache : IO.Ref (Std.HashMap Name (Array String))

def Sources.lines (s : Sources) (mod : Name) : IO (Option (Array String)) := do
  if let some ls := (← s.cache.get)[mod]? then return some ls
  let some path ← s.sp.findModuleWithExt "lean" mod | return none
  let text ← IO.FS.readFile path
  let ls := (text.splitOn "\n").toArray
  s.cache.modify (·.insert mod ls)
  return some ls

def modFile (mod : Name) : String :=
  (modToFilePath "" mod "lean").toString.dropWhile (· == '/') |>.toString

/-- Common location fields: module, file, range, source text and docstring. -/
def Ctx.location (c : Ctx) (src : Sources) (n : Name) : IO (List (String × Json)) := do
  let mut fields : List (String × Json) := []
  if let some m := c.moduleOf n then
    fields := fields ++ [("module", Json.str m.toString), ("file", Json.str (modFile m))]
    let ranges ← c.runMeta .anonymous (findDeclarationRanges? n)
    if let some r := ranges then
      fields := fields ++ [("range", rangeJson r.range)]
      if let some ls ← src.lines m then
        fields := fields ++ [("source", Json.str (sliceLines ls r.range.pos r.range.endPos))]
  if let some d ← findDocString? c.env n then
    fields := fields ++ [("doc", Json.str d.trimAscii.toString)]
  return fields

def Ctx.signature (c : Ctx) (n : Name) : IO String :=
  c.runMeta (userName n).getPrefix do
    return fmt (← PrettyPrinter.ppSignature n).fmt

/-- The type with project definitions unfolded down to the library boundary. -/
def Ctx.unfolded (c : Ctx) (ci : ConstantInfo) : IO (Option String) := do
  let p (n : Name) : Bool := c.isProject n && !c.isInstance n &&
    match c.env.find? n with
    | some (.defnInfo _) => true
    | _ => false
  let s ← c.runMeta (userName ci.name).getPrefix do
    let e ← deltaExpand ci.type p
    if e == ci.type then return none
    let e ← Core.betaReduce e
    let f ← withOptions (fun o => o.set `pp.maxSteps (20000 : Nat)) (ppExpr e)
    return some (fmt f)
  return s.filter (·.length ≤ c.cfg.unfoldMaxChars)

/-! ### Unused binders -/

/-- Pair the leading ∀-binders of the type with the λ-binders of the proof:
(index, used by the proof, used later in the statement). -/
partial def binderUse (t v : Expr) (k : Nat) (acc : Array (Nat × Bool × Bool)) :
    Nat × Array (Nat × Bool × Bool) :=
  match t.consumeMData, v.consumeMData with
  | .forallE _ _ tb _, .lam _ _ vb _ =>
    binderUse tb vb (k + 1) (acc.push (k, vb.hasLooseBVar 0, tb.hasLooseBVar 0))
  | _, _ => (k, acc)

def Ctx.unused (c : Ctx) (ci : ConstantInfo) : IO (Array Json) := do
  let some v := valueOf ci | return #[]
  let (n, flags) := binderUse ci.type v 0 #[]
  if n == 0 then return #[]
  c.runMeta (userName ci.name).getPrefix do
    forallBoundedTelescope ci.type n fun xs _ => do
      let mut out := #[]
      for (i, usedByProof, usedInStatement) in flags do
        if usedByProof then continue
        let x := xs[i]!
        let ld ← x.fvarId!.getDecl
        let ty ← inferType x
        let isProp ← Meta.isProp ty
        let bi := match ld.binderInfo with
          | .default => "explicit" | .implicit => "implicit"
          | .strictImplicit => "strict-implicit" | .instImplicit => "instance"
        out := out.push <| Json.mkObj [
          ("index", i), ("name", Json.str ld.userName.eraseMacroScopes.toString),
          ("binder", Json.str bi), ("type", Json.str (fmt (← ppExpr ty))),
          ("prop", Json.bool isProp), ("in_statement", Json.bool usedInStatement)]
      return out

/-! ### Proof-state traces from info trees -/

def sortObj (xs : Array (String × Json)) : Json :=
  Json.mkObj (xs.qsort (fun a b => a.1 < b.1)).toList


def containerKinds : List Name :=
  [``Lean.Parser.Tactic.tacticSeq, ``Lean.Parser.Tactic.tacticSeq1Indented,
   ``Lean.Parser.Tactic.tacticSeqBracketed, ``Lean.Parser.Term.byTactic,
   ``Lean.Parser.Tactic.paren, ``Lean.cdot, ``Lean.Parser.Tactic.case,
   ``Lean.Parser.Tactic.«tactic_<;>_», `by, identKind, nullKind]

def hypName (n : Name) : String :=
  if n.hasMacroScopes then n.eraseMacroScopes.toString ++ "✝" else n.toString

def ppGoal (ci : ContextInfo) (mctx : MetavarContext) (g : MVarId) : IO Json :=
  ({ ci with mctx } : ContextInfo).runMetaM {} do
    let some decl := mctx.findDecl? g | return Json.null
    withLCtx decl.lctx decl.localInstances do
      let mut hyps := #[]
      for ld in decl.lctx do
        if ld.isImplementationDetail then continue
        let ty ← ppExpr (← instantiateMVars ld.type)
        let mut fields := [("name", Json.str (hypName ld.userName)), ("type", Json.str (fmt ty))]
        if let some v := ld.value? then
          fields := fields ++ [("value", Json.str (fmt (← ppExpr (← instantiateMVars v))))]
        hyps := hyps.push (Json.mkObj fields)
      let target ← ppExpr (← instantiateMVars decl.type)
      let tag := if decl.userName.isAnonymous then "" else hypName decl.userName
      return Json.mkObj [("tag", Json.str tag), ("hyps", Json.arr hyps), ("target", Json.str (fmt target))]

structure Step where
  start : Position
  stop : Position
  depth : Nat
  parent : Option Nat
  json : List (String × Json)

structure TraceTarget where
  name : Name
  start : String.Pos.Raw
  stop : String.Pos.Raw

def Ctx.stepUses (c : Ctx) (mctx : MetavarContext) (goals : List MVarId) : Json × Json := Id.run do
  let mut proj : NameSet := {}
  let mut lib : NameSet := {}
  for g in goals do
    let e := (instantiateMVarsCore mctx (.mvar g)).1
    for n in e.getUsedConstants do
      let some ci := c.env.find? n | continue
      unless ci matches .thmInfo _ do continue
      if c.isAux n then continue
      if c.isProject n then proj := proj.insert n else lib := lib.insert n
  return (Json.arr ((sortNames proj).map Json.str), Json.arr ((sortNames lib).map Json.str))

partial def Ctx.collectSteps (c : Ctx) (fileMap : FileMap) (text : String) (t : TraceTarget)
    (trees : Array InfoTree) : IO (Array Json) := do
  let steps ← IO.mkRef (#[] : Array Step)
  let seen ← IO.mkRef (#[] : Array (String.Pos.Raw × String.Pos.Raw))
  let rec go (ctx? : Option ContextInfo) (parent : Option Nat) (depth : Nat) : InfoTree → IO Unit
    | .context pci t => go (pci.mergeIntoOuter? ctx?) parent depth t
    | .hole _ => pure ()
    | .node info children => do
      let mut parent := parent
      let mut depth := depth
      if let (some ctx, .ofTacticInfo ti) := (ctx?, info) then
        if let (some a, some b) := (ti.stx.getPos? (canonicalOnly := true),
            ti.stx.getTailPos? (canonicalOnly := true)) then
          if t.start ≤ a && b ≤ t.stop && !containerKinds.contains ti.stx.getKind && !ti.stx.isAtom &&
              !(← seen.get).contains (a, b) then
            seen.modify (·.push (a, b))
            let before ← ti.goalsBefore.toArray.mapM (ppGoal ctx ti.mctxBefore)
            let after ← ti.goalsAfter.toArray.mapM (ppGoal ctx ti.mctxAfter)
            let (proj, lib) := c.stepUses ti.mctxAfter ti.goalsBefore
            let sp := fileMap.toPosition a
            let ep := fileMap.toPosition b
            let idx := (← steps.get).size
            steps.modify (·.push {
              start := sp, stop := ep, depth, parent
              json := [("kind", Json.str ti.stx.getKind.toString),
                ("text", Json.str (String.Pos.Raw.extract text a b)),
                ("goals_before", Json.arr before), ("goals_after", Json.arr after),
                ("uses_project", proj), ("uses_library", lib)] })
            parent := some idx
            depth := depth + 1
      for ch in children do go ctx? parent depth ch
  for tree in trees do go none none 0 tree
  let ss ← steps.get
  return ss.mapIdx fun i s => Json.mkObj ([("index", Json.num i),
    ("range", Json.mkObj [("start", posJson s.start), ("end", posJson s.stop)]),
    ("depth", Json.num s.depth),
    ("parent", match s.parent with | some p => Json.num p | none => Json.null)] ++ s.json)

open Frontend in
partial def traceLoop (inputCtx : Parser.InputContext) (tts : Array TraceTarget)
  (lastStop : String.Pos.Raw) (skip : Bool) : FrontendM Unit := do
  updateCmdPos
  let s ← get
  if lastStop ≤ s.parserState.pos then return
  let scope := s.commandState.scopes.head!
  let pmctx := { env := s.commandState.env, options := scope.opts,
                 currNamespace := scope.currNamespace, openDecls := scope.openDecls }
  let (cmd, ps, msgs) := Parser.parseCommand inputCtx pmctx s.parserState s.commandState.messages
  setParserState ps
  setMessages msgs
  let a := (cmd.getPos?).getD 0
  let b := (cmd.getTailPos?).getD 0
  let traced := tts.any fun t => a ≤ t.start && t.start < b
  modify fun st => { st with commandState := { st.commandState with
    scopes := match st.commandState.scopes with
      | h :: rest => { h with opts := h.opts.setBool `debug.byAsSorry (skip && !traced) } :: rest
      | [] => [] } }
  elabCommandAtFrontend cmd
  unless Parser.isTerminalCommand cmd do traceLoop inputCtx tts lastStop skip

open Frontend in
/-- Re-elaborate `mod` from source with info trees and collect the tactic steps
of the target declarations (name, start, end). Commands other than the targets
may have their proofs replaced by `sorry` (`skip_earlier_proofs`): the kernel
check is the project's own build, the trace only needs the proof states. This
runs in its own process, because a second `importModules` in one process does
not give a usable environment. -/
def traceModule (cfg : Config) (mod : Name) (targets : Array (Name × Position × Position)) :
    IO Json := do
  initSearchPath (← findSysroot)
  unsafe enableInitializersExecution
  let sp ← getSrcSearchPath
  let some path ← sp.findModuleWithExt "lean" mod
    | throw (IO.userError s!"no source for {mod}")
  let text ← IO.FS.readFile path
  let inputCtx := Parser.mkInputContext text (modFile mod)
  let fileMap := inputCtx.fileMap
  let tts : Array TraceTarget := targets.map fun (n, a, b) =>
    { name := n, start := fileMap.ofPosition a, stop := fileMap.ofPosition b }
  let lastStop := tts.foldl (fun m t => if m < t.stop then t.stop else m) 0
  let opts : Options := ({} : Options) |>.setBool `Elab.async false |>.set `maxHeartbeats (0 : Nat)
  let (header, parserState, messages) ← Parser.parseHeader inputCtx
  let (env, messages) ← processHeader header opts messages inputCtx (mainModule := mod)
  let cmdState := { Command.mkState env messages opts with infoState := { enabled := true } }
  let loop := traceLoop inputCtx tts lastStop cfg.skipEarlierProofs
  let ((), st) ← (loop { inputCtx }).run { commandState := cmdState, parserState, cmdPos := parserState.pos }
  let errs := st.commandState.messages.toList.filter (·.severity == .error)
  unless errs.isEmpty do
    let m ← errs.head!.toString
    throw (IO.userError s!"re-elaborating {mod} failed: {m}")
  let c : Ctx := { cfg, env := st.commandState.env }
  let trees := st.commandState.infoState.trees.toArray
  let mut out := #[]
  for t in tts do
    out := out.push (t.name.toString, Json.mkObj [("steps", Json.arr (← c.collectSteps fileMap text t trees))])
  return sortObj out

/-! ### Main -/

def Ctx.contextEntry (c : Ctx) (src : Sources) (n : Name) : IO Json := do
  let some ci := c.env.find? n | return Json.null
  let loc ← c.location src n
  return Json.mkObj ([("kind", Json.str (kindOf c n ci)),
    ("signature", Json.str (← c.signature n)),
    ("type_hash", Json.str (hex64 (typeHash ci))),
    ("body_hash", Json.str (hex64 (bodyHash c.env ci))),
    ("instance", Json.bool (c.isInstance n)),
    ("deps", Json.arr ((c.directDeps n).map (Json.str ·.toString)))] ++ loc)

def Ctx.closureHash (c : Ctx) (ci : ConstantInfo) (ctxNames : Array Name) : UInt64 :=
  ctxNames.foldl (init := typeHash ci) fun h n =>
    match c.env.find? n with
    | some cj => mixHash h (mixHash (hash n) (mixHash (typeHash cj) (bodyHash c.env cj)))
    | none => h

def run (cfg : Config) : IO Json := do
  initSearchPath (← findSysroot)
  unsafe enableInitializersExecution
  let env ← importModules (cfg.imports.map fun m => { module := m, importAll := true }) {}
    (level := .private) (loadExts := true)
  let c : Ctx := { cfg, env }
  let src : Sources := { sp := ← getSrcSearchPath, cache := ← IO.mkRef {} }
  let mut decls : Array (String × Json) := #[]
  let mut ctxAll : NameSet := {}
  let mut missing : Array String := #[]
  for n in cfg.declarations do
    let some ci := env.find? n | missing := missing.push n.toString; continue
    -- A definition's context includes its body; a theorem's only its statement.
    let roots := match ci with
      | .thmInfo _ => ci.type.getUsedConstants
      | _ => #[n]
    let ctxNames := (c.context roots).filter (· != n)
    ctxAll := ctxNames.foldl (·.insert ·) ctxAll
    let u := c.uses n
    let mut viaFields : List (String × Json) := []
    if cfg.trace.contains n then
      let memo := c.viaHelpers u.helpers.toArray
      let via := (sortNames u.helpers).filterMap fun h =>
        let ms := memo.getD h.toName {}
        if ms.isEmpty then none else some (h, Json.arr ((sortNames ms).map Json.str))
      viaFields := [("via", Json.mkObj via.toList)]
    let uses := Json.mkObj <| viaFields ++ [("mapped", Json.arr ((sortNames u.mapped).map Json.str)),
      ("helpers", Json.arr ((sortNames u.helpers).map Json.str)),
      ("library", Json.arr ((sortNames u.library).map Json.str))]
    let mut fields := [("kind", Json.str (kindOf c n ci)),
      ("signature", Json.str (← c.signature n)),
      ("context", Json.arr (ctxNames.map (Json.str ·.toString))),
      ("deps", Json.arr ((c.directDeps n).map (Json.str ·.toString))),
      ("type_hash", Json.str (hex64 (typeHash ci))),
      ("body_hash", Json.str (hex64 (bodyHash env ci))),
      ("closure_hash", Json.str (hex64 (c.closureHash ci ctxNames))),
      ("unused", Json.arr (← c.unused ci)), ("uses", uses)]
    if let some s ← c.unfolded ci then fields := fields ++ [("unfolded", Json.str s)]
    decls := decls.push (n.toString, Json.mkObj (fields ++ (← c.location src n)))
  let mut ctxEntries : Array (String × Json) := #[]
  for n in sortNames ctxAll do
    ctxEntries := ctxEntries.push (n, ← c.contextEntry src n.toName)
  unless missing.isEmpty do
    throw (IO.userError s!"unknown declarations: {sortStrings missing}")
  return Json.mkObj [
    ("schema", "paper-lean-audit/extraction-1"),
    ("environment", Json.mkObj [("lean_version", Json.str Lean.versionString),
      ("lean_githash", Json.str Lean.githash),
      ("imports", Json.arr (cfg.imports.map (Json.str ·.toString)))]),
    ("boundary", Json.mkObj [
      ("project_modules", Json.arr (cfg.projectModules.map (Json.str ·.toString))),
      ("boundary_modules", Json.arr (cfg.boundaryModules.map (Json.str ·.toString))),
      ("boundary_namespaces", Json.arr (cfg.boundaryNamespaces.map (Json.str ·.toString)))]),
    ("declarations", sortObj decls), ("context", sortObj ctxEntries)]

end PaperLeanAudit

def parsePos (j : Json) : Option Position :=
  match j.getArrVal? 0, j.getArrVal? 1 with
  | .ok l, .ok c => match l.getNat?, c.getNat? with
    | .ok l, .ok c => some ⟨l, c⟩
    | _, _ => none
  | _, _ => none

def main (args : List String) : IO UInt32 := do
  match args with
  | ["extract", cfgPath, outPath] =>
    let cfgJson ← IO.ofExcept (Json.parse (← IO.FS.readFile cfgPath))
    let out ← PaperLeanAudit.run (PaperLeanAudit.Config.ofJson cfgJson)
    IO.FS.writeFile outPath (out.pretty 120 ++ "\n")
    return 0
  | ["trace", cfgPath, outPath] =>
    let cfgJson ← IO.ofExcept (Json.parse (← IO.FS.readFile cfgPath))
    let mod := ((cfgJson.getObjValAs? String "module").toOption.getD "").toName
    let targets := match cfgJson.getObjValAs? (Array Json) "targets" with
      | .ok ts => ts.filterMap fun t => do
          let n ← (t.getObjValAs? String "name").toOption
          let a ← (t.getObjVal? "start").toOption.bind parsePos
          let b ← (t.getObjVal? "end").toOption.bind parsePos
          return (n.toName, a, b)
      | .error _ => #[]
    let out ← PaperLeanAudit.traceModule (PaperLeanAudit.Config.ofJson cfgJson) mod targets
    IO.FS.writeFile outPath (out.pretty 120 ++ "\n")
    return 0
  | _ =>
    IO.eprintln "usage: lake env lean --run Extract.lean (extract|trace) <config.json> <out.json>"
    return 2
