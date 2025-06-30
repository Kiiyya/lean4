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

inductive ValOrType where | type | value -- | universe
inductive TypeOrProp where | type | prop

/-- Analyze an expression which might be an abbreviation, projection, or auxDecl. -/
partial def analyze (expr : Expr) (cont : Expr -> Option ConstantInfo -> MetaM α) : MetaM α := do
  let expr <- instantiateExprMVars expr
  -- `expr` can be `Vec ℝ`, e.g. if the original expr was an `abbrev Vecℝ := Vec ℝ` and we unfolded it.
  let f := expr.getAppFn
  match f with
  | .const name _ =>
    let constInfo <- getConstInfo name
    if let .defnInfo di := constInfo then
      if di.hints.isAbbrev then
        if let some f' <- Meta.unfoldDefinition? f then
          return <- analyze (expr.updateFn f') cont
    cont expr constInfo
  -- | .proj structName fieldIdx obj => sorry -- todo
  | .fvar id =>
    let some localDecl := (<- getLCtx).find? id | cont expr none

    -- try to replace auxDecl with an actual `.const` after the command as been elaborated
    if localDecl.isImplementationDetail || localDecl.isAuxDecl then
      let constName := (<- getCurrNamespace) ++ localDecl.userName
      let some ci := (<- getEnv).find? constName -- I don't know what the proper way to resolve names is. This fails if we `def Nat.add`
        -- | dbg_trace "BUG env has no {constName} Have auxDecl with user name {localDecl.userName}, and currNamespace = {<- getCurrNamespace}"
        | cont expr none -- this sometimes fails even if it shouldn't, I have no clue why.
      let const <- createConstFor ci localDecl.type
      let lctx' := (<- getLCtx).replaceFVarId localDecl.fvarId const
      let expr' := expr.replaceFVarId localDecl.fvarId const
      Meta.withLCtx lctx' (<- Meta.getLocalInstances) do
        analyze expr' cont
    else
      cont expr none
  | _ => cont expr none

set_option linter.unusedVariables false

/-- Analyze a type `(a₁ : A₁) -> (a₂ : A₂) -> ... -> Target` in a way convenient for semantic
  highlighting. Potentially unfolds some abbreviations. Invokes the continuation `cont` with:
  - `exprType`: Potentially slightly simplified original `exprType`,
  - `params = [a₁, a₂, ...]` as local decls,
  - `Target`,
  - `T` from `Target ≡ (T ...)`,
  - `constInfo`: Info of `T` if it is a constant.  -/
def analyzeType
  (exprType : Expr)
  (cont : (exprType : Expr) -> (params : Array Expr) -> (Target T : Expr) -> TypeOrProp -> ValOrType -> Option ConstantInfo -> MetaM α)
  : MetaM α := do
  let exprType <- instantiateExprMVars exprType
  Meta.forallTelescope exprType (cleanupAnnotations := true) fun params Target => do
    let T := Target.getAppFn -- todo make look through abbrevs
    let constInfo <- Option.sequence (T.constName?.map getConstInfo)
    match Target with
    | .sort .zero => cont exprType params Target T .prop .type constInfo
    | .sort _     => cont exprType params Target T .type .type constInfo
    | _ =>
      Meta.forallTelescope (<- Meta.inferType exprType >>= instantiateExprMVars) fun _ exprTypeType => do
        match exprTypeType with
        | .sort .zero => cont exprType params Target T .prop .value constInfo
        | .sort _     => cont exprType params Target T .type .value constInfo
        | _           => cont exprType params Target T .type .value constInfo -- should never happen, but whatever

/- Highlight an expression. Some examples:
  - If `termInfo.expr` is `Vec`, so has type `Type -> Nat -> Type`, we look at:
    1. The expr itself, so `Vec`, in order to figure out whether it is sum-like or prod-like, via `ConstantInfo`.
    2. The type of the expr, so `Type -> Nat -> Type`, in order to figure out whether it is `⟨propOrType, valueOrType⟩`.
-/
partial def highlight (termInfo : Elab.TermInfo) : MetaM (Option LeanSemanticToken) := do
  analyze termInfo.expr fun expr exprConstInfo? => do
    analyzeType (<- Meta.inferType expr) fun exprType params Target T typeOrProp valOrType exprTypeConstInfo? => do
      let mut mods : List SemanticTokenModifier := []
      if termInfo.isBinder then mods := .declaration :: mods
      if params.size > 0 then mods := .func :: mods -- todo ignore implicit, instance, auto params
      match (typeOrProp, valOrType) with
      | (.type, .type) => mods := .type :: mods
      | (.type, .value) => mods := .value :: mods
      | (.prop, .type) => mods := .prop :: mods
      | (.prop, .value) => mods := .proof :: mods

      let env <- getEnv
      let stx := termInfo.stx
      match exprConstInfo? with
      | some (.inductInfo ii) =>
        let isClass := Lean.isClass env ii.name
        let isStruct := Lean.isStructureLike env ii.name
        if isClass then mods := .typeclass :: mods
        if isStruct then mods := .productLike :: mods else mods := .sumLike :: mods
        match (isClass, isStruct) with
        | (true, _) => return some ⟨stx, .interface, mods⟩
        | (false, true) => return some ⟨stx, .struct, mods⟩
        | (false, false) => return some ⟨stx, .enum, mods⟩
      | some (.ctorInfo ci) =>
        let isStruct := Lean.isStructureLike env ci.induct
        if isStruct then
          mods := .sumLike :: mods
          return some ⟨stx, .constructor, mods⟩ -- this is e.g. `Prod.mk`
        else
          mods := .productLike :: mods
          return some ⟨stx, .enumMember, mods⟩
      | some (.defnInfo di) =>
        if env.isProjectionFn di.name then -- e.g. `Prod.fst`
          -- return some ⟨stx, .property, .productLike :: mods⟩
          return some ⟨stx, .property, mods⟩
        return some ⟨stx, .function, mods⟩
      | some _ => return none -- todo
      | none =>
        match expr with
        | .sort .zero => return some ⟨stx, .sort0, mods⟩
        | .sort _ => return some ⟨stx, .sortN, mods⟩
        | .fvar id =>
          let ldecl := (<- getLCtx).find? id
          -- if ldecl.map (not ·.isLet) |>.getD false then
          --   return some ⟨stx, .parameter, mods⟩ -- if the localDecl is not a let-binder, it (probably) is a parameter
          return some ⟨stx, .variable, mods⟩
        | _ => return none -- todo

/-- Collects all semantic tokens from the given `Elab.InfoTree`. -/
partial def collectInfoBasedSemanticTokens (i : Elab.InfoTree) (envAfter : Environment) : RequestM <| List LeanSemanticToken := do
  let notFlat <- i.deepestNodesM fun ctxInfo elabInfo _ => do
    let .ofTermInfo termInfo := elabInfo | return none
    let .original .. := termInfo.stx.getHeadInfo | return none
    termInfo.runMetaM ctxInfo do
      withEnv envAfter do
        Meta.withReducible do -- we want to unfold `abbrev`, e.g. `abbrev Vec3f := Vec 3 Float` should be highlighted the same likeness of `Vec`, and not def-like.
          -- return some (<- go termInfo.expr termInfo.stx)
          Option.map ([·]) <$> highlight termInfo
  return notFlat.flatten
-- where
--   go (expr : Expr) (stx : Syntax) : MetaM (List LeanSemanticToken) := do
--     match stx with
--     -- ! Wait, recursively adding `go` makes no sense, it's all the same expr anyway...
--     -- dbg_trace "{dbgIndent d}go {repr stx}"
--     | `($s₁.$s₂:ident) => do -- For example `NS.c.add`
--       -- dbg_trace "{dbgIndent d}go[$e₁.$e₂:ident] {stx}"
--       return (<- go expr s₁) ++ (<- highlightIdent termInfo ctxInfo).toList
--     -- | `($s₁.$s₂:fieldIdx) => do -- For example `NS.c.2`
--     --   -- dbg_trace "{dbgIndent d}go[$e₁.$e₂:fieldIdx] {stx}"
--     --   return (<- go expr s₁) ++ (<- highlightIdent s₂ expr).toList
--     | `(@$_:ident)                       => Option.toList <$> highlightIdent stx expr
--     | `(Parser.Term.dotIdent| .$_:ident) => Option.toList <$> highlightIdent stx expr
--     | `($_:ident)                        => Option.toList <$> highlightIdent stx expr
--     | _ =>
--       if stx.isOfKind choiceKind then go expr stx[0]
--       else stx.getArgs.foldlM (fun tokens stx => return tokens ++ (<- go expr stx)) []


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
