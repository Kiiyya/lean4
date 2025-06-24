/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich, Marc Huisinga
-/
prelude
import Lean.Server.Requests

namespace Lean.Server.FileWorker
open Lsp
open RequestM

/--
`SyntaxNodeKind`s for which the syntax node and its children receive no semantic highlighting.
-/
def noHighlightKinds : Array SyntaxNodeKind := #[
  -- usually have special highlighting by the client
  ``Lean.Parser.Term.sorry,
  ``Lean.Parser.Term.type,
  ``Lean.Parser.Term.prop,
  -- not really keywords
  `antiquotName,
  ``Lean.Parser.Command.docComment,
  ``Lean.Parser.Command.moduleDoc]

-- TODO: make extensible, or don't
/-- Keywords for which a specific semantic token is provided. -/
def keywordSemanticTokenMap : RBMap String SemanticTokenType compare :=
  RBMap.empty
    |>.insert "sorry" .leanSorryLike
    |>.insert "admit" .leanSorryLike
    |>.insert "stop" .leanSorryLike
    |>.insert "#exit" .leanSorryLike

/-- Semantic token information for a given `Syntax`. -/
structure LeanSemanticToken where
  /-- Syntax of the semantic token. -/
  stx  : Syntax
  /-- Type of the semantic token. -/
  type : SemanticTokenType
  /-- Modifiers on the semantic token, for example `binder`, `mutable`, `prop`, ... -/
  mods : List SemanticTokenModifier

/-- Semantic token information with absolute LSP positions. -/
structure AbsoluteLspSemanticToken where
  /-- Start position of the semantic token. -/
  pos     : Lsp.Position
  /-- End position of the semantic token. -/
  tailPos : Lsp.Position
  type    : SemanticTokenType
  mods    : List SemanticTokenModifier
  deriving BEq, Hashable, FromJson, ToJson

/--
Given a set of `LeanSemanticToken`, computes the `AbsoluteLspSemanticToken` with absolute
LSP position information for each token.
-/
def computeAbsoluteLspSemanticTokens
    (text     : FileMap)
    (beginPos : String.Pos)
    (endPos?  : Option String.Pos)
    (tokens   : Array LeanSemanticToken)
    : Array AbsoluteLspSemanticToken :=
  tokens.filterMap fun ⟨stx, tokenType, tokenMods⟩ => do
    let (pos, tailPos) := (← stx.getPos?, ← stx.getTailPos?)
    guard <| beginPos <= pos && endPos?.all (pos < ·)
    let (lspPos, lspTailPos) := (text.utf8PosToLspPos pos, text.utf8PosToLspPos tailPos)
    return ⟨lspPos, lspTailPos, tokenType, tokenMods⟩

/-- Filters all duplicate semantic tokens with the same `pos`, `tailPos` and `type`. -/
def filterDuplicateSemanticTokens (tokens : Array AbsoluteLspSemanticToken) : Array AbsoluteLspSemanticToken :=
  tokens.groupByKey id |>.toArray.map (·.1)

/--
Given a set of `AbsoluteLspSemanticToken`, computes the LSP `SemanticTokens` data with
token-relative positioning.
See https://microsoft.github.io/language-server-protocol/specifications/lsp/3.17/specification/#textDocument_semanticTokens.
-/
def computeDeltaLspSemanticTokens (tokens : Array AbsoluteLspSemanticToken) : SemanticTokens := Id.run do
  let tokens := tokens.qsort fun a b => a.pos < b.pos || a.pos == b.pos && a.tailPos < b.tailPos
  let mut data : Array Nat := Array.mkEmpty (5*tokens.size)
  let mut lastPos : Lsp.Position := ⟨0, 0⟩
  for ⟨pos, tailPos, tokenType, tokenMods⟩ in tokens do
    let deltaLine := pos.line - lastPos.line
    let deltaStart := pos.character - (if pos.line == lastPos.line then lastPos.character else 0)
    let length := tailPos.character - pos.character
    let tokenType := tokenType.toNat
    let tokenModifiers := SemanticTokenModifier.encode tokenMods
    data := data ++ #[deltaLine, deltaStart, length, tokenType, tokenModifiers]
    lastPos := pos
  return { data }

/-- Analyzes the type (and the type's type) in order to apply `prop`, `type`, `proof` modifiers.
  - If `ty` is `... -> Prop`, then `prop` is added.
  - If `ty` is `... -> Type _`, then `type` is added.
  - If `ty : Prop`, then `proof` is added.
-/
def classifyType (ty : Expr) : MetaM <| List SemanticTokenModifier := do
  -- ty is of form `... -> F ...`
  Meta.forallTelescope ty.consumeTypeAnnotations.consumeMData (cleanupAnnotations := true) fun _ body => do
    let mut mods := []
    if ty.isForall then mods := .func :: mods
    let body <- instantiateMVars body
    match body.getAppFn.consumeTypeAnnotations.consumeMData with
    | .sort .zero => mods := .prop :: mods
    | .sort _     => mods := .type :: mods
    | _ =>
      -- let tyty <- Meta.inferType ty >>= Meta.whnf >>= instantiateMVars
      let tyty <- Meta.inferType ty >>= instantiateMVars
      match tyty with
      | .sort .zero => mods := .proof :: mods
      | .sort _ => mods := .value :: mods
      | _ => pure ()
    return mods

/-- Create a `Expr.const ci.name levels` where the levels are inferred from the expectedType
  by comparing `ci.type` and `expectedType`. -/
private def createConstFor (ci : ConstantInfo) (expectedType : Expr) : MetaM Expr := do
  let mvars : List Level <- Meta.mkFreshLevelMVarsFor ci
  let ty := ci.type.instantiateLevelParams ci.levelParams mvars
  if <- Meta.isDefEq ty expectedType then
    let levels <- mvars.mapM fun l => do
      if let some level := <- Lean.getLevelMVarAssignment? l.mvarId! then
        return level
      else return default
    return Expr.const ci.name levels
  else Meta.mkConstWithFreshMVarLevels ci.name

inductive SumOrProdLike
| neither
| sum
| prod

/-- Get the `T` from `... -> T`. -/
def getTarget (expr : Expr) : MetaM Expr := sorry
/--
  - `Vec ...` gives sum-like.
  - `Prod ...` gives prod-like.
  - `
 -/
def getTypeLikeness (expr : Expr) : MetaM SumOrProdLike := sorry

private partial def classifyConst (expr : Expr) : MetaM <| Option (SemanticTokenType × SumOrProdLike) := do
  -- let mut mods := []
  let expr <- instantiateMVars expr
  let .const name _ := expr | return none
  let some constInfo := (<- getEnv).find? name | return none
  match constInfo with
  | .inductInfo info =>
    if Lean.isClass (<- getEnv) name then
      return some ⟨.interface, .neither⟩
    if Lean.isStructureLike (<- getEnv) name then
      return some ⟨.struct, .neither⟩
    return some ⟨.enum, .neither⟩
  | .ctorInfo info =>
    return some ⟨.enumMember, sorry⟩
  | .defnInfo _info =>
    if (<- getEnv).isProjectionFn name then
      return some ⟨.property, mods⟩
    return some ⟨.function, mods⟩
  | .opaqueInfo info => return some ⟨.function, mods⟩
  | .axiomInfo info => return some ⟨.axiom, mods⟩
  | .thmInfo _ => return some ⟨.theorem, mods⟩
  | .recInfo _info => return some ⟨.recursor, mods⟩
  | .quotInfo _info => return some ⟨.quot, mods⟩

private partial def highlightIdent (termInfo : Elab.TermInfo) (ctxInfo : Elab.ContextInfo) : MetaM <| Option <| LeanSemanticToken := do
-- private partial def highlightIdent (stx : Syntax) (expr : Expr) : MetaM <| Option <| LeanSemanticToken := do
  let expr := termInfo.expr
  let stx := termInfo.stx
  -- let expr <- instantiateMVars expr
  -- dbg_trace "highlightImp {stx} has expr {expr}"
  let mut mods := []
  -- if termInfo.isBinder then mods := .declaration :: mods
  match expr.getAppFn with -- TODO also respect abbrevs, so if `abbrev ListN := List Nat`, then expr `List Nat`.
  | .sort .zero => return some ⟨stx, .sort0, []⟩
  | .sort _ => return some ⟨stx, .sortN, []⟩
  | .fvar fvarId => do
    let some localDecl := (<- getLCtx).find? fvarId
      |
        dbg_trace "ierbfdsvkzjcxn"
        return none
    if localDecl.isLet then mods := .«let» :: mods
    -- Recall that `isAuxDecl` is an auxiliary declaration used to elaborate a recursive definition.
    if localDecl.isAuxDecl then
      let constName := (<- getCurrNamespace) ++ localDecl.userName
      let some ci := (<- getEnv).find? constName | -- I don't know what the proper way to resolve names is. This fails if we `def Nat.add`. -- TODO use realizeGlobalConstant
        dbg_trace "BUG env has no {constName} Have auxDecl with user name {localDecl.userName}, and currNamespace = {<- getCurrNamespace}"
        return none
      let const <- createConstFor ci localDecl.type
      let lctx' := (<- getLCtx).replaceFVarId localDecl.fvarId const
      let expr' := expr.replaceFVarId localDecl.fvarId const
      Meta.withLCtx lctx' (<- Meta.getLocalInstances) do
        highlightIdent stx expr' -- retry, having replaced fvar auxDecl for actual environment item
    else
      return some ⟨stx, .variable, (<- classifyType localDecl.type) ++ mods⟩ -- TODO fix
  | expr@(.const name _) =>
    let expr <- instantiateMVars expr
    let some constInfo := (<- getEnv).find? name | return none
    mods := <- classifyType (<- Meta.inferType expr) -- infer common `type`, `prop`, `value`, `proof`,... modifiers
    sorry

  | .proj typeName field val =>
    -- TODO: It is possible to have `Expr.proj` without associated StructureInfo, in which case the below will fail:
    let some si := Lean.getStructureInfo? (<- getEnv) typeName |
      dbg_trace "alskdjfhadsf"
      return none
    let some projFnName := si.getProjFn? field |
      dbg_trace "skadlfhasidfuha"
      return none
    let expr := Expr.app (<- Meta.mkConstWithFreshMVarLevels projFnName) val
    highlightIdent stx expr
  | _ => do
    dbg_trace "BUG {stx} fails to highlight :(, expr is {expr}, where the root ctor is Expr.{expr.ctorName}."
    -- -- fallback:
    -- let ty <- Meta.inferType expr
    -- mods := (<- classifyType ty) ++ mods
    return none

/-- Collects all semantic tokens from the given `Elab.InfoTree`. -/
partial def collectInfoBasedSemanticTokens (i : Elab.InfoTree) (envAfter : Environment) : RequestM <| List LeanSemanticToken := do
  let notFlat <- i.deepestNodesM fun ctxInfo elabInfo _ => do
    let .ofTermInfo termInfo := elabInfo | return none
    let .original .. := termInfo.stx.getHeadInfo | return none
    -- let tmp <- ctxInfo.runMetaM termInfo.lctx <| Meta.withReducible <| withEnv envAfter <| do
    let tmp <- termInfo.runMetaM ctxInfo <| Meta.withReducible <| withEnv envAfter <| go termInfo.expr termInfo.stx
    return some tmp
  return notFlat.flatten
where
  go (expr : Expr) (stx : Syntax) : MetaM (List LeanSemanticToken) := do
    match stx with
    -- ! Wait, recursively adding `go` makes no sense, it's all the same expr anyway...
    -- dbg_trace "{dbgIndent d}go {repr stx}"
    | `($s₁.$s₂:ident) => do -- For example `NS.c.add`
      -- dbg_trace "{dbgIndent d}go[$e₁.$e₂:ident] {stx}"
      return (<- go expr s₁) ++ (<- highlightIdent termInfo ctxInfo).toList
    -- | `($s₁.$s₂:fieldIdx) => do -- For example `NS.c.2`
    --   -- dbg_trace "{dbgIndent d}go[$e₁.$e₂:fieldIdx] {stx}"
    --   return (<- go expr s₁) ++ (<- highlightIdent s₂ expr).toList
    | `(@$_:ident)                       => Option.toList <$> highlightIdent stx expr
    | `(Parser.Term.dotIdent| .$_:ident) => Option.toList <$> highlightIdent stx expr
    | `($_:ident)                        => Option.toList <$> highlightIdent stx expr
    | _ =>
      if stx.isOfKind choiceKind then go expr stx[0]
      else stx.getArgs.foldlM (fun tokens stx => return tokens ++ (<- go expr stx)) []


def computeSemanticTokens  (doc : EditableDocument) (beginPos : String.Pos)
    (endPos? : Option String.Pos) (snaps : List Snapshots.Snapshot) : RequestM SemanticTokens := do
  let mut leanSemanticTokens : Array LeanSemanticToken := #[]
  for h : i in [0 : snaps.length] do
    let snap := snaps[i]
    let snapAfter := snaps[i + 1]?.getD snap -- okay, because files end with `Command.eoi`. We need the snap after the current snap in order to have the fully elaborated auxDecl.
    if snap.endPos <= beginPos then
      continue
    -- let syntaxBasedSemanticTokens := collectSyntaxBasedSemanticTokens snap.stx
    let infoBasedSemanticTokens <- collectInfoBasedSemanticTokens snap.infoTree snapAfter.env
    leanSemanticTokens := leanSemanticTokens ++ /- syntaxBasedSemanticTokens ++ -/ infoBasedSemanticTokens.toArray
    RequestM.checkCancelled
  let absoluteLspSemanticTokens := computeAbsoluteLspSemanticTokens doc.meta.text beginPos endPos? leanSemanticTokens
  RequestM.checkCancelled
  let absoluteLspSemanticTokens := filterDuplicateSemanticTokens absoluteLspSemanticTokens
  RequestM.checkCancelled
  let semanticTokens := computeDeltaLspSemanticTokens absoluteLspSemanticTokens
  return semanticTokens

structure SemanticTokensState where
  deriving TypeName, Inhabited

/-- Computes all semantic tokens for the document. -/
def handleSemanticTokensFull (_ : SemanticTokensParams) (_ : SemanticTokensState)
    : RequestM (LspResponse SemanticTokens × SemanticTokensState) := do
  let ctx ← read
  let doc ← readDoc
  -- Only grabs the finished prefix so that we do not need to wait for elaboration to complete
  -- for the full file before sending a response. This means that the response will be incomplete,
  -- which we mitigate by regularly sending `workspace/semanticTokens/refresh` requests in the
  -- `FileWorker` to tell the client to re-compute the semantic tokens.
  let (snaps, _, isComplete) ← doc.cmdSnaps.getFinishedPrefixWithTimeout 3000 (cancelTks := ctx.cancelTk.cancellationTasks)
  let response ← computeSemanticTokens doc 0 none snaps
  return ({ response, isComplete }, ⟨⟩)

def handleSemanticTokensDidChange (_ : DidChangeTextDocumentParams)
    : StateT SemanticTokensState RequestM Unit := do
  return

/-- Computes the semantic tokens in the range provided by `p`. -/
def handleSemanticTokensRange (p : SemanticTokensRangeParams)
    : RequestM (RequestTask SemanticTokens) := do
  let doc ← readDoc
  let text := doc.meta.text
  let beginPos := text.lspPosToUtf8Pos p.range.start
  let endPos := text.lspPosToUtf8Pos p.range.end
  let t := doc.cmdSnaps.waitUntil (·.endPos >= endPos)
  mapTaskCostly t fun (snaps, _) =>
    computeSemanticTokens doc beginPos endPos snaps

builtin_initialize
  registerLspRequestHandler
    "textDocument/semanticTokens/range"
    SemanticTokensRangeParams
    SemanticTokens
    handleSemanticTokensRange
  registerPartialStatefulLspRequestHandler
    "textDocument/semanticTokens/full"
    "workspace/semanticTokens/refresh"
    2000
    SemanticTokensParams
    SemanticTokens
    SemanticTokensState
    ⟨⟩
    handleSemanticTokensFull
    handleSemanticTokensDidChange

end Lean.Server.FileWorker
