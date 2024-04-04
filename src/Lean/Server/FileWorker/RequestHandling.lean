/-
Copyright (c) 2021 Wojciech Nawrocki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Wojciech Nawrocki, Marc Huisinga
-/
prelude
import Lean.DeclarationRange

import Lean.Data.Json
import Lean.Data.Lsp

import Lean.Server.FileWorker.Utils
import Lean.Server.Requests
import Lean.Server.Completion
import Lean.Server.References
import Lean.Server.GoTo

import Lean.Widget.InteractiveGoal
import Lean.Widget.Diff

namespace Lean.Server.FileWorker
open Lsp
open RequestM
open Snapshots

def handleCompletion (p : CompletionParams)
    : RequestM (RequestTask CompletionList) := do
  let doc ← readDoc
  let text := doc.meta.text
  let pos := text.lspPosToUtf8Pos p.position
  let caps := (← read).initParams.capabilities
  -- dbg_trace ">> handleCompletion invoked {pos}"
  -- NOTE: use `+ 1` since we sometimes want to consider invalid input technically after the command,
  -- such as a trailing dot after an option name. This shouldn't be a problem since any subsequent
  -- command starts with a keyword that (currently?) does not participate in completion.
  withWaitFindSnap doc (·.endPos + ' ' >= pos)
    (notFoundX :=
      -- work around https://github.com/microsoft/vscode/issues/155738
      -- this is important when a snapshot cannot be found because it was aborted
      pure { items := #[{label := "-"}], isIncomplete := true })
    (x := fun snap => do
      if let some r ← Completion.find? p doc.meta.text pos snap.infoTree caps then
        return r
      return { items := #[ ], isIncomplete := true })

/--
Handles `completionItem/resolve` requests that are sent by the client after the user selects
a completion item that was provided by `textDocument/completion`. Resolving the item fills the
`detail?` field of the item with the pretty-printed type.
This control flow is necessary because pretty-printing the type for every single completion item
(even those never selected by the user) is inefficient.
-/
def handleCompletionItemResolve (item : CompletionItem)
    : RequestM (RequestTask CompletionItem) := do
  let doc ← readDoc
  let text := doc.meta.text
  let some (data : CompletionItemDataWithId) := item.data?.bind fun data => (fromJson? data).toOption
    | return .pure item
  let some id := data.id?
    | return .pure item
  let pos := text.lspPosToUtf8Pos data.params.position
  withWaitFindSnap doc (·.endPos + ' ' >= pos)
    (notFoundX := pure item)
    (x := fun snap => Completion.resolveCompletionItem? text pos snap.infoTree item id)

open Elab in
def handleHover (p : HoverParams)
    : RequestM (RequestTask (Option Hover)) := do
  let doc ← readDoc
  let text := doc.meta.text
  let mkHover (s : String) (r : String.Range) : Hover := {
    contents := {
      kind := MarkupKind.markdown
      value := s
    }
    range? := r.toLspRange text
  }

  let hoverPos := text.lspPosToUtf8Pos p.position
  withWaitFindSnap doc (fun s => s.endPos > hoverPos)
    (notFoundX := pure none) fun snap => do
      -- try to find parser docstring from syntax tree
      let stack? := snap.stx.findStack? (·.getRange?.any (·.contains hoverPos))
      let stxDoc? ← match stack? with
        | some stack => stack.findSomeM? fun (stx, _) => do
          let .node _ kind _ := stx | pure none
          return (← findDocString? snap.env kind).map (·, stx.getRange?.get!)
        | none => pure none

      -- now try info tree
      if let some ictx := snap.infoTree.hoverableInfoAt? hoverPos then
        if let some range := ictx.info.range? then
          -- prefer info tree if at least as specific as parser docstring
          if stxDoc?.all fun (_, stxRange) => stxRange.includes range then
            if let some hoverFmt ← ictx.info.fmtHover? ictx.ctx then
              return mkHover (toString hoverFmt.fmt) range

      if let some (doc, range) := stxDoc? then
        return mkHover doc range

      return none

open Elab GoToKind in
def locationLinksOfInfo (kind : GoToKind) (ictx : InfoWithCtx)
    (infoTree? : Option InfoTree := none) : RequestM (Array LocationLink) := do
  let rc ← read
  let doc ← readDoc
  let text := doc.meta.text

  let locationLinksFromDecl (i : Elab.Info) (n : Name) :=
    locationLinksFromDecl rc.srcSearchPath doc.meta.uri n <| (·.toLspRange text) <$> i.range?

  let locationLinksFromBinder (i : Elab.Info) (id : FVarId) := do
    if let some i' := infoTree? >>= InfoTree.findInfo? fun
        | Info.ofTermInfo { isBinder := true, expr := Expr.fvar id' .., .. } => id' == id
        | _ => false then
      if let some r := i'.range? then
        let r := r.toLspRange text
        let ll : LocationLink := {
          originSelectionRange? := (·.toLspRange text) <$> i.range?
          targetUri := doc.meta.uri
          targetRange := r
          targetSelectionRange := r
        }
        return #[ll]
    return #[]

  let locationLinksFromImport (i : Elab.Info) := do
    let name := i.stx[2].getId
    if let some modUri ← documentUriFromModule rc.srcSearchPath name then
      let range := { start := ⟨0, 0⟩, «end» := ⟨0, 0⟩ : Range }
      let ll : LocationLink := {
        originSelectionRange? := (·.toLspRange text) <$> i.stx[2].getRange? (canonicalOnly := true)
        targetUri := modUri
        targetRange := range
        targetSelectionRange := range
      }
      return #[ll]
    return #[]

  let i := ictx.info
  let ci := ictx.ctx
  let children := ictx.children
  match i with
  | .ofTermInfo ti =>
    let mut expr := ti.expr
    if kind == type then
      expr ← ci.runMetaM i.lctx do
        return Expr.getAppFn (← instantiateMVars (← Meta.inferType expr))
    match expr with
    | Expr.const n .. => return ← ci.runMetaM i.lctx <| locationLinksFromDecl i n
    | Expr.fvar id .. => return ← ci.runMetaM i.lctx <| locationLinksFromBinder i id
    | _ => pure ()

    -- Check whether this `TermInfo` node is directly responsible for its `.expr`.
    -- This is the case iff all of its children represent strictly smaller subexpressions;
    -- it is sufficient to check this of all direct children of this node (and that its elaborator didn't expand it as a macro)
    let isExprGenerator := children.all fun
      | .node (Info.ofTermInfo info) _ => info.expr != expr
      | .node (Info.ofMacroExpansionInfo _) _ => false
      | _ => true

    -- don't go-to-instance if this `TermInfo` didn't directly generate its `.expr`
    if kind != declaration && isExprGenerator then
      -- go-to-definition on a projection application of a typeclass
      -- should return all instances generated by TC
      expr ← ci.runMetaM i.lctx do instantiateMVars expr
      if let .const n _ := expr.getAppFn then
        -- also include constant along with instance results
        let mut results ← ci.runMetaM i.lctx <| locationLinksFromDecl i n
        if let some info := ci.env.getProjectionFnInfo? n then
          let mut elaborators := default
          if let some ei := i.toElabInfo? then do
            -- also include elaborator along with instance results, as this wouldn't be accessible otherwise
            if ei.elaborator != `Delab -- prevent an error if this `TermInfo` came from the infoview
              && ei.elaborator != `Lean.Elab.Term.elabApp && ei.elaborator != `Lean.Elab.Term.elabIdent -- don't include trivial elaborators
              then do
              elaborators ← ci.runMetaM i.lctx <| locationLinksFromDecl i ei.elaborator
          let instIdx := info.numParams
          let appArgs := expr.getAppArgs
          let rec extractInstances : Expr → RequestM (Array Name)
            | .const declName _ => do
              if ← ci.runMetaM i.lctx do Lean.Meta.isInstance declName then pure #[declName] else pure #[]
            | .app fn arg => do pure $ (← extractInstances fn).append (← extractInstances arg)
            | _ => pure #[]
          if let some instArg := appArgs.get? instIdx then
            for inst in (← extractInstances instArg) do
              results := results.append (← ci.runMetaM i.lctx <| locationLinksFromDecl i inst)
            results := results.append elaborators -- put elaborators at the end of the results
        return results
  | .ofFieldInfo fi =>
    if kind == type then
      let expr ← ci.runMetaM i.lctx do
        instantiateMVars (← Meta.inferType fi.val)
      if let some n := expr.getAppFn.constName? then
        return ← ci.runMetaM i.lctx <| locationLinksFromDecl i n
    else
      return ← ci.runMetaM i.lctx <| locationLinksFromDecl i fi.projName
  | .ofOptionInfo oi =>
    return ← ci.runMetaM i.lctx <| locationLinksFromDecl i oi.declName
  | .ofCommandInfo ⟨`import, _⟩ =>
    if kind == definition || kind == declaration then
      return ← ci.runMetaM i.lctx <| locationLinksFromImport i
  | _ => pure ()
  -- If other go-tos fail, we try to show the elaborator or parser
  if let some ei := i.toElabInfo? then
    if kind == declaration && ci.env.contains ei.stx.getKind then
      return ← ci.runMetaM i.lctx <| locationLinksFromDecl i ei.stx.getKind
    if kind == definition && ci.env.contains ei.elaborator then
      return ← ci.runMetaM i.lctx <| locationLinksFromDecl i ei.elaborator
  return #[]

open Elab GoToKind in
def handleDefinition (kind : GoToKind) (p : TextDocumentPositionParams)
    : RequestM (RequestTask (Array LocationLink)) := do
  let doc ← readDoc
  let text := doc.meta.text
  let hoverPos := text.lspPosToUtf8Pos p.position

  withWaitFindSnap doc (fun s => s.endPos > hoverPos)
    (notFoundX := pure #[]) fun snap => do
      if let some infoWithCtx := snap.infoTree.hoverableInfoAt? (omitIdentApps := true) (includeStop := true /- #767 -/) hoverPos then
        locationLinksOfInfo kind infoWithCtx snap.infoTree
      else return #[]

open RequestM in
def getInteractiveGoals (p : Lsp.PlainGoalParams) : RequestM (RequestTask (Option Widget.InteractiveGoals)) := do
  let doc ← readDoc
  let text := doc.meta.text
  let hoverPos := text.lspPosToUtf8Pos p.position
  -- NOTE: use `>=` since the cursor can be *after* the input
  withWaitFindSnap doc (fun s => s.endPos >= hoverPos)
    (notFoundX := return none) fun snap => do
      if let rs@(_ :: _) := snap.infoTree.goalsAt? doc.meta.text hoverPos then
        let goals : List Widget.InteractiveGoals ← rs.mapM fun { ctxInfo := ci, tacticInfo := ti, useAfter := useAfter, .. } => do
          let ciAfter := { ci with mctx := ti.mctxAfter }
          let ci := if useAfter then ciAfter else { ci with mctx := ti.mctxBefore }
          -- compute the interactive goals
          let goals ← ci.runMetaM {} (do
            let goals := List.toArray <| if useAfter then ti.goalsAfter else ti.goalsBefore
            let goals ← goals.mapM Widget.goalToInteractive
            return {goals}
          )
          -- compute the goal diff
          let goals ← ciAfter.runMetaM {} (do
              try
                Widget.diffInteractiveGoals useAfter ti goals
              catch _ =>
                -- fail silently, since this is just a bonus feature
                return goals
          )
          return goals
        return some <| goals.foldl (· ++ ·) ∅
      else
        return none

open Elab in
def handlePlainGoal (p : PlainGoalParams)
    : RequestM (RequestTask (Option PlainGoal)) := do
  let t ← getInteractiveGoals p
  return t.map <| Except.map <| Option.map <| fun {goals, ..} =>
    if goals.isEmpty then
      { goals := #[], rendered := "no goals" }
    else
      let goalStrs := goals.map (toString ·.pretty)
      let goalBlocks := goalStrs.map fun goal => s!"```lean
{goal}
```"
      let md := String.intercalate "\n---\n" goalBlocks.toList
      { goals := goalStrs, rendered := md }

def getInteractiveTermGoal (p : Lsp.PlainTermGoalParams)
    : RequestM (RequestTask (Option Widget.InteractiveTermGoal)) := do
  let doc ← readDoc
  let text := doc.meta.text
  let hoverPos := text.lspPosToUtf8Pos p.position
  withWaitFindSnap doc (fun s => s.endPos > hoverPos)
    (notFoundX := pure none) fun snap => do
      if let some {ctx := ci, info := i@(Elab.Info.ofTermInfo ti), ..} := snap.infoTree.termGoalAt? hoverPos then
        let ty ← ci.runMetaM i.lctx do
          instantiateMVars <| ti.expectedType?.getD (← Meta.inferType ti.expr)
        -- for binders, hide the last hypothesis (the binder itself)
        let lctx' := if ti.isBinder then i.lctx.pop else i.lctx
        let goal ← ci.runMetaM lctx' do
          Widget.goalToInteractive (← Meta.mkFreshExprMVar ty).mvarId!
        let range := if let some r := i.range? then r.toLspRange text else ⟨p.position, p.position⟩
        return some { goal with range, term := ⟨ti⟩ }
      else
        return none

def handlePlainTermGoal (p : PlainTermGoalParams)
    : RequestM (RequestTask (Option PlainTermGoal)) := do
  let t ← getInteractiveTermGoal p
  return t.map <| Except.map <| Option.map fun goal =>
    { goal := toString goal.pretty
      range := goal.range
    }

partial def handleDocumentHighlight (p : DocumentHighlightParams)
    : RequestM (RequestTask (Array DocumentHighlight)) := do
  let doc ← readDoc
  let text := doc.meta.text
  let pos := text.lspPosToUtf8Pos p.position

  let rec highlightReturn? (doRange? : Option Range) : Syntax → Option DocumentHighlight
    | `(doElem|return%$i $e) => Id.run do
      if let some range := i.getRange? then
        if range.contains pos then
          return some { range := doRange?.getD (range.toLspRange text), kind? := DocumentHighlightKind.text }
      highlightReturn? doRange? e
    | `(do%$i $elems) => highlightReturn? (i.getRange?.get!.toLspRange text) elems
    | stx => stx.getArgs.findSome? (highlightReturn? doRange?)

  let highlightRefs? (snaps : Array Snapshot) : IO (Option (Array DocumentHighlight)) := do
    let trees := snaps.map (·.infoTree)
    let refs : Lsp.ModuleRefs ← findModuleRefs text trees |>.toLspModuleRefs
    let mut ranges := #[]
    for ident in refs.findAt p.position do
      if let some info := refs.find? ident then
        if let some ⟨definitionRange, _⟩ := info.definition? then
          ranges := ranges.push definitionRange
        ranges := ranges.append <| info.usages.map (·.range)
    if ranges.isEmpty then
      return none
    return some <| ranges.map ({ range := ·, kind? := DocumentHighlightKind.text })

  withWaitFindSnap doc (fun s => s.endPos > pos)
    (notFoundX := pure #[]) fun snap => do
      let (snaps, _) ← doc.cmdSnaps.getFinishedPrefix
      if let some his ← highlightRefs? snaps.toArray then
        return his
      if let some hi := highlightReturn? none snap.stx then
        return #[hi]
      return #[]

structure NamespaceEntry where
  /-- The list of the name components introduced by this namespace command,
  in reverse order so that `end` will peel them off from the front. -/
  name : List Name
  stx : Syntax
  selection : Syntax
  prevSiblings : Array DocumentSymbol

def NamespaceEntry.finish (text : FileMap) (syms : Array DocumentSymbol) (endStx : Option Syntax) :
    NamespaceEntry → Array DocumentSymbol
  | { name, stx, selection, prevSiblings, .. } =>
    -- we can assume that commands always have at least one position (see `parseCommand`)
    let range := match endStx with
      | some endStx => (mkNullNode #[stx, endStx]).getRange?.get!
      | none        =>  { stx.getRange?.get! with stop := text.source.endPos }
    let name := name.foldr (fun x y => y ++ x) Name.anonymous
    prevSiblings.push <| DocumentSymbol.mk {
      -- anonymous sections are represented by `«»` name components
      name := if name == `«» then "<section>" else name.toString
      kind := .namespace
      range := range.toLspRange text
      selectionRange := selection.getRange?.getD range |>.toLspRange text
      children? := syms
    }

open Parser.Command in
partial def handleDocumentSymbol (_ : DocumentSymbolParams)
    : RequestM (RequestTask DocumentSymbolResult) := do
  let doc ← readDoc
  -- bad: we have to wait on elaboration of the entire file before we can report document symbols
  let t := doc.cmdSnaps.waitAll
  mapTask t fun (snaps, _) => do
    let mut stxs := snaps.map (·.stx)
    return { syms := toDocumentSymbols doc.meta.text stxs #[] [] }
where
  toDocumentSymbols (text : FileMap) (stxs : List Syntax)
      (syms : Array DocumentSymbol) (stack : List NamespaceEntry) :
      Array DocumentSymbol :=
    match stxs with
    | [] => stack.foldl (fun syms entry => entry.finish text syms none) syms
    | stx::stxs => match stx with
      | `(namespace $id)  =>
        let entry := { name := id.getId.componentsRev, stx, selection := id, prevSiblings := syms }
        toDocumentSymbols text stxs #[] (entry :: stack)
      | `(section $(id)?) =>
        let name := id.map (·.getId.componentsRev) |>.getD [`«»]
        let entry := { name, stx, selection := id.map (·.raw) |>.getD stx, prevSiblings := syms }
        toDocumentSymbols text stxs #[] (entry :: stack)
      | `(end $(id)?) =>
        let rec popStack n syms
          | [] => toDocumentSymbols text stxs syms []
          | entry :: stack =>
            if entry.name.length == n then
              let syms := entry.finish text syms stx
              toDocumentSymbols text stxs syms stack
            else if entry.name.length > n then
              let syms := { entry with name := entry.name.take n, prevSiblings := #[] }.finish text syms stx
              toDocumentSymbols text stxs syms ({ entry with name := entry.name.drop n } :: stack)
            else
              let syms := entry.finish text syms stx
              popStack (n - entry.name.length) syms stack
        popStack (id.map (·.getId.getNumParts) |>.getD 1) syms stack
      | _ => Id.run do
        unless stx.isOfKind ``Lean.Parser.Command.declaration do
          return toDocumentSymbols text stxs syms stack
        if let some stxRange := stx.getRange? then
          let (name, selection) := match stx with
            | `($_:declModifiers $_:attrKind instance $[$np:namedPrio]? $[$id$[.{$ls,*}]?]? $sig:declSig $_) =>
              ((·.getId.toString) <$> id |>.getD s!"instance {sig.raw.reprint.getD ""}", id.map (·.raw) |>.getD sig)
            | _ =>
              match stx.getArg 1 |>.getArg 1 with
              | `(declId|$id$[.{$ls,*}]?) => (id.raw.getId.toString, id)
              | _ =>
                let stx10 : Syntax := (stx.getArg 1).getArg 0 -- TODO: stx[1][0] times out
                (stx10.isIdOrAtom?.getD "<unknown>", stx10)
          if let some selRange := selection.getRange? then
            let sym := DocumentSymbol.mk {
              name := name
              kind := SymbolKind.method
              range := stxRange.toLspRange text
              selectionRange := selRange.toLspRange text
            }
            return toDocumentSymbols text stxs (syms.push sym) stack
        toDocumentSymbols text stxs syms stack

structure SemanticTokensContext where
  beginPos : String.Pos
  endPos?  : Option String.Pos
  text     : FileMap
  snap     : Snapshot
  envAfter  : Environment
  doc       : EditableDocument

structure SemanticTokensState where
  data       : Array Nat
  /-- LSP expects token positions to be relative to the last token. -/
  lastLspPos : Lsp.Position

private abbrev SemanticTokenT (m : Type -> Type) (α : Type) := ReaderT SemanticTokensContext (StateT SemanticTokensState m) α
private abbrev SemanticTokenM := SemanticTokenT RequestM


-- TODO: Remove HasRange helper
class HasRange (α : Type) extends ToString α where
  range? : α -> Option String.Range
instance: HasRange Syntax := ⟨Syntax.getRange?⟩
instance: ToString String.Range := ⟨fun ⟨a, b⟩ => s!"({a} .. {b} : String.Range)"⟩
instance: HasRange String.Range := ⟨Option.some⟩

/-- Append a token for the range of `stx`. -/
private def addToken [HasRange S] (stx : S) (type : SemanticTokenType) (mods : List SemanticTokenModifier := []) : SemanticTokenM PUnit := do
  -- dbg_trace "addToken {stx} (({repr type} {repr mods}))"
  let ⟨beginPos, endPos?, text, _, _, _⟩ ← read
  let some ⟨pos, tailPos⟩ := HasRange.range? stx
    | return
  unless beginPos <= pos && endPos?.all (pos < ·)  do
    return
  let lspPos := (← get).lastLspPos
  let lspPos' := text.utf8PosToLspPos pos
  let deltaLine := lspPos'.line - lspPos.line
  let deltaStart := lspPos'.character - (if lspPos'.line == lspPos.line then lspPos.character else 0)
  let length := (text.utf8PosToLspPos tailPos).character - lspPos'.character
  let tokenType := type.toNat
  let tokenModifiers := encodeSemanticTokenModifiers mods
  let data := #[deltaLine, deltaStart, length, tokenType, tokenModifiers]
  -- dbg_trace "addedToken {repr data}"
  modify fun st => {
    data := st.data ++ data
    lastLspPos := lspPos'
  }

/-- Create a `Expr.const ci.name levels` where the levels are inferred from the expectedType
  by comparing `ci.type` and `expectedType`. -/
private def createConstFor (ci : ConstantInfo) (expectedType : Expr) : MetaM Expr := do
  let mvars : List Level <- Meta.mkFreshLevelMVarsFor ci
  let ty := ci.type.instantiateLevelParams ci.levelParams mvars
  if <- Meta.isDefEq ty expectedType then
    let levels <- mvars.mapM fun l => do
      if let some level := <- Lean.getLevelMVarAssignment? l.mvarId! then
        return level
      else
        -- dbg_trace "BUG: createConstFor failed, since a level mvar didn't get assigned."
        return default
    return Expr.const ci.name levels
  else
    -- dbg_trace "BUG createConstFor failed since isDefEq failed: {ty} =?= {expectedType}"
    Meta.mkConstWithFreshMVarLevels ci.name

private def miniWhnf (e : Expr) : MetaM Expr := do
  let e := e.consumeTypeAnnotations
  let e := e.consumeMData
  -- unfold reducible definitions
  let some e <- Meta.unfoldDefinition? e -- no `|>.getDM e` ? :(
    | return e
  return e

/-- Analyzes the type (and the type's type) in order to apply `prop`, `type`, `proof` modifiers.
  - If `ty` is `... -> Prop`, then `prop` is added.
  - If `ty` is `... -> Type _`, then `type` is added.
  - If `ty : Prop`, then `proof` is added.
  -/
private def helper (ty : Expr) : MetaM <| List SemanticTokenModifier := do
  -- ty is of form `... -> F ...`
  Meta.forallTelescope ty.consumeTypeAnnotations.consumeMData fun _ body => do
    let mut mods := []
    if ty.isForall then mods := .func :: mods
    -- let body <- Meta.whnf body >>= instantiateMVars -- body is now `F ...`
    -- let F <- Meta.whnf body.getAppFn >>= instantiateMVars
    let body <- instantiateMVars body
    let F := body.getAppFn.consumeTypeAnnotations.consumeMData

    -- if (<- getEnv).contains ``Monad then
    --   let tcType := .app (<- Meta.mkConstWithFreshMVarLevels ``Monad) F
    --   if let some _ := <- Meta.synthInstance? tcType then
    --     mods := .monadic :: mods
    --   -- dbg_trace "ty is {ty}, body is {body}, F is {F}"
    --   -- dbg_trace "tcType is {tcType}"

    match F with
    | .sort .zero => mods := .prop :: mods
    | .sort _ => mods := .type :: mods
    | _ => do
      let tyty <- Meta.inferType ty >>= Meta.whnf >>= instantiateMVars
      -- dbg_trace "helper ty is {ty}, F is {F}, tyty is {tyty}"
      match tyty with
      | .sort .zero => mods := .proof :: mods
      | .sort _ => mods := .value :: mods
      | _ => pure ()
    return mods

private def highlightConst (expr : Expr) : MetaM <| Option <| SemanticTokenType × List SemanticTokenModifier := do
  let expr <- instantiateMVars expr
  let .const name _levels := expr | panic! "highlightConst: expr needs to be Expr.const"
  let some constInfo := (<- getEnv).find? name | return none
    -- | dbg_trace "!BUG {stx} is const with name {name} but has no constant info in env."; return none
  let mut mods <- Meta.inferType expr >>= instantiateMVars >>= helper -- infer `type`, `prop`, `value`, `proof`, `func` modifiers
  match constInfo with
  | .inductInfo info =>
    if info.isUnsafe then mods := .unsafe :: mods
    if info.isNested then mods := .nested :: mods
    if info.isRec then mods := .nested :: mods
    if info.isReflexive then mods := .reflexive :: mods
    if Lean.isClass (<- getEnv) name then mods := .typeclass :: mods
    if Lean.isStructureLike (<- getEnv) name then mods := .struct :: mods
    return some (.type, mods)
  | .ctorInfo info =>
    if info.isUnsafe then mods := .«unsafe» :: mods
    return some (.enumMember, mods)
  | .defnInfo _info =>
    if (<- getEnv).isProjectionFn name then mods := .proj :: mods
    return some (.function, mods)
  | .opaqueInfo info =>
    if info.isUnsafe then mods := .«unsafe» :: mods
    mods := .«partial» :: mods
    return some (.function, mods)
  | .axiomInfo info =>
    if info.isUnsafe then mods := .«unsafe» :: mods
    return some (.axiom, mods)
  | .thmInfo _ => return some (.theorem, mods)
  | .recInfo _info => return some (.recursor, mods)
  | .quotInfo _info => return some (.quot, mods)

/-- `envAfter` is used to resolve the names of auxDecls. -/
private partial def highlightImp [HasRange S] (stx : S) (expr : Expr) (isBinder : Bool) (currNamespace : Name) : MetaM <| Option <| SemanticTokenType × List SemanticTokenModifier := do
  let expr <- instantiateMVars expr
  -- dbg_trace "highlightImp {stx} has expr {expr}"

  -- -- If expr is an abbreviation, Meta.whnf will unroll it. If the result is a lambda telescope,
  -- -- we enter it. If then the result is an application chain, inspect the application function.
  -- -- If the function is a constant, inherit from that. Otherwise, pretend we are a def.
  -- let expr <- Meta.whnf expr >>= instantiateMVars -- unroll abbrev

  -- Meta.lambdaTelescope expr fun _abbrevFVars expr => do
  -- Once this works decently enough, try moving some of the logic out of MetaM.
  let mut mods := []
  if isBinder then mods := SemanticTokenModifier.declaration :: mods
  match expr.getAppFn with -- if `abbrev ListN := List Nat`, then expr `List Nat`.
  | .sort .zero => return some (.sort0, [])
  | .sort _ => return some (.sortN, [])
  | .fvar fvarId => do
    let some localDecl := (<- getLCtx).find? fvarId
      | --dbg_trace "!BUG {stx} is an fvar, but not in ti.lctx"
        return none
    if localDecl.isLet then mods := .«let» :: mods
    -- Recall that `isAuxDecl` is an auxiliary declaration used to elaborate a recursive definition.
    if localDecl.isAuxDecl then
      let constName := currNamespace ++ localDecl.userName
      let some ci := (<- getEnv).find? constName -- I don't know what the proper way to resolve names is. This fails if we `def Nat.add`.
        | return none
        -- | dbg_trace "BUG env has no {constName} Have auxDecl with user name {localDecl.userName}, and currNamespace = {currNamespace}"; return none
      let const <- createConstFor ci localDecl.type
      let lctx' := (<- getLCtx).replaceFVarId localDecl.fvarId const
      let expr' := expr.replaceFVarId localDecl.fvarId const
      Meta.withLCtx lctx' (<- Meta.getLocalInstances) do
        highlightImp stx expr' isBinder currNamespace -- retry
    else
      return some (.variable, (<- helper localDecl.type) ++ mods) -- TODO fix
  | e@(.const ..) =>
    let res <- highlightConst e
    return res.map fun (tt, tm) => (tt, tm ++ mods)
  | _ => do
    -- dbg_trace "BUG {stx} fails to highlight :(, expr repr is {repr expr}. Doing Fallback."
    -- fallback:
    let ty <- Meta.inferType expr
    mods := (<- helper ty) ++ mods
    return some (.unknown, mods)

/-- Get TermInfos relevant to this range. -/
private def filterInfos (range : String.Range) : SemanticTokenM <| List (Elab.ContextInfo × Elab.TermInfo) := do
  let tis := (← read).snap.infoTree.deepestNodes fun
  | (ctxInfo : Elab.ContextInfo), i@(Elab.Info.ofTermInfo ti), _ => match i.pos? with
    | some ipos => do
      -- dbg_trace "** POS={ipos} ;; {i.stx} ;; rangeContains = {range.contains ipos}"
      if range.contains ipos then some (ctxInfo, ti) else none
    | _         => none
  | _, _, _ => none
  return tis

/--
  Highlight a piece of syntax, usually an identifier, but also operators, keywords, etc.

  The `infos` are pre-filtered info tree nodes relevant to this syntax node. Can be more than one.
-/
private def highlight [HasRange S] (stx : S) (ti : Elab.TermInfo) (ctxInfo : Elab.ContextInfo) : SemanticTokenT RequestM Unit := do
  -- let some range := stx.getRange?
  --   | return
  -- let tis <- filterInfos range
  -- dbg_trace "#### HIGHLIGHT [{range.start}..{range.stop}] {stx} HAVE FILTERED INFOS {tis.map (fun (_, ti) => ti.expr)}"

  -- let mut lastPos := range.start
  -- for (ctxInfo, ti) in tis do
  --   -- avoid reporting same position twice; the info node can occur multiple times if
  --   -- e.g. the term is elaborated multiple times
  --   -- TODO: smarter way of selecting which info(s) to use than just "first best".
  --   let pos := ti.stx.getPos?.get!
  --   if pos < lastPos then
  --     continue
  --   lastPos := pos

    let envAfter := (<- read).envAfter
    let res <- ctxInfo.runMetaM ti.lctx <| Meta.withReducible do
      withEnv envAfter do
        highlightImp stx ti.expr ti.isBinder ctxInfo.currNamespace
    if let some (tt, tmods) := res then
      addToken stx tt tmods

open IO in
def timeit' [MonadLiftT BaseIO m] [Monad m] (msg : Nat -> String) (f : m α) : m α := do
  let _start <- monoNanosNow
  let result <- f
  let _finish <- monoNanosNow
  -- dbg_trace "{msg ((finish - start) / 1000)}"
  return result

#check Prod.snd


-- TODO: delete later
private def dbgIndent : Nat -> String
| .zero => ""
| .succ k => ">" ++ dbgIndent k

partial def dbgPrintInfoTree (tree : Elab.InfoTree) (d := 0) : RequestM String := do
  let res <- match tree with
  | .context _contextInfo sub =>
    return s!"{dbgIndent d} IT.context ? \n{<- dbgPrintInfoTree sub (d+1)}"
  | .hole _mvarId => pure s!"{dbgIndent d} IT.hole\n"
  | .node info children =>
    let xxx := match info with
    | .ofTermInfo       i => s!".ofTermInfo       ‖{i.stx}‖ {i.expr}"
    | .ofCommandInfo    i => s!".ofCommandInfo    ‖{i.stx}‖"
    | .ofFieldInfo      i => s!".ofFieldInfo      ‖{i.stx}‖ projName = {i.projName}, val = {i.val}"
    -- | .ofCompletionInfo i => s!".ofCompletionInfo ‖{i.stx}‖ ..."
    | .ofFVarAliasInfo  i => s!".ofFVarAliasInfo            userName={i.userName} id={Expr.fvar i.id} baseId={Expr.fvar i.baseId} "
    | _ => ".other"
    let children := (<- children.mapM (dbgPrintInfoTree . (d+1))).toList
    return s!"{dbgIndent d} IT.node $ {xxx}\n{children.map String.data |>.join |>.asString}"

#synth ToString Syntax
#check Syntax.instToStringSyntax
#check Syntax.isOfKind
#check Lean.Parser.Term.proj
#check Lean.Parser.Term.app

partial def handleSemanticTokens (beginPos : String.Pos) (endPos? : Option String.Pos)
    : RequestM (RequestTask SemanticTokens) := do
  let doc ← readDoc
  match endPos? with
  | none =>
    -- Only grabs the finished prefix so that we do not need to wait for elaboration to complete
    -- for the full file before sending a response. This means that the response will be incomplete,
    -- which we mitigate by regularly sending `workspace/semanticTokens/refresh` requests in the
    -- `FileWorker` to tell the client to re-compute the semantic tokens.
    let (snaps, _) ← doc.cmdSnaps.getFinishedPrefix
    asTask <| run doc snaps
  | some endPos =>
    let t := doc.cmdSnaps.waitUntil (·.endPos >= endPos)
    mapTask t fun (snaps, _) => run doc snaps
where
  run doc snaps : RequestM SemanticTokens :=
    StateT.run' (s := { data := #[], lastLspPos := ⟨0, 0⟩ : SemanticTokensState }) do
      timeit' (s!"handleSemanticTokens needed { · } µs") do
        -- every command (`def`, `structure`, ...) results in its own snapshot.
        for h : i in [0 : snaps.length] do
          let s := snaps[i]
          if s.endPos <= beginPos then
            continue
          let sAfter := snaps[i + 1]?.getD s -- should always be fine, as files end with `Command.eoi`.
          ReaderT.run (r := SemanticTokensContext.mk beginPos endPos? doc.meta.text s sAfter.env doc) do
            -- dbg_trace "#### SNAP {s.stx}"
            let _dbg_tree : Elab.InfoTree := s.infoTree
            -- dbg_trace s!"{<- dbgPrintInfoTree _dbg_tree}"
            go s.stx
        return { data := (← get).data }
  go (stx : Syntax) (d : Nat := 0) : SemanticTokenM Unit := do
    -- dbg_trace "{dbgIndent d}go {repr stx}"
    match stx with
    | `($e₁.$e₂:ident) => do -- For example `NS.c.add`
      -- dbg_trace "{dbgIndent d}go[$e₁.$e₂:ident] {stx}"
      go e₁ (d + 1)
      goIdent e₂ (d + 1)
    | `($e₁.$e₂:fieldIdx) => do -- For example `NS.c.2`
      -- dbg_trace "{dbgIndent d}go[$e₁.$e₂:fieldIdx] {stx}"
      go e₁ (d + 1)
      goIdent e₂ (d + 1)
    | `(@$_:ident) | `(.$_:ident) =>
      goIdent stx d
    | `($e:ident) =>
      goIdent e d
    | _ =>
      if stx.isOfKind choiceKind then go stx[0] d
      else stx.getArgs.forM (go . (d+1))

  /-- Syntax nodes don't have enough granularity, for example `xs.length` with `xs : List α` is
    represented as just one `Syntax.ident`.
    There are `TermInfo`s available for `xs` and `length`, so use them to "chop up" the syntax node
    then calling `highlight` on fake, more granular, syntax nodes.
  -/
  goIdent (stx : Syntax) (_d : Nat) : SemanticTokenM Unit := do
    -- dbg_trace "{dbgIndent d}goIdent {repr stx}"
    let some range := stx.getRange? | return
    let infos <- filterInfos range
    -- dbg_trace s!"goIdent {stx} infos are {infos.map (·.2.stx)}"
    infos.forM fun (ci, ti) => do
      highlight ti.stx ti ci

    -- if let some info := infos.get? 0 then -- TODO: make not hacky
    --   highlight info.2.stx info.2 info.1

    -- let f := fun lhs (contextInfo, info) => do
    --   highlight info.stx info contextInfo
    -- let _ <- infos.foldlM f sorry

def handleSemanticTokensFull (_ : SemanticTokensParams)
    : RequestM (RequestTask SemanticTokens) := do
  handleSemanticTokens 0 none

def handleSemanticTokensRange (p : SemanticTokensRangeParams)
    : RequestM (RequestTask SemanticTokens) := do
  let doc ← readDoc
  let text := doc.meta.text
  let beginPos := text.lspPosToUtf8Pos p.range.start
  let endPos := text.lspPosToUtf8Pos p.range.end
  handleSemanticTokens beginPos endPos


partial def handleFoldingRange (_ : FoldingRangeParams)
  : RequestM (RequestTask (Array FoldingRange)) := do
  let doc ← readDoc
  let t := doc.cmdSnaps.waitAll
  mapTask t fun (snaps, _) => do
    let stxs := snaps.map (·.stx)
    let (_, ranges) ← StateT.run (addRanges doc.meta.text [] stxs) #[]
    return ranges
  where
    isImport stx := stx.isOfKind ``Lean.Parser.Module.header || stx.isOfKind ``Lean.Parser.Command.open

    addRanges (text : FileMap) sections
    | [] => do
      if let (_, start)::rest := sections then
        addRange text FoldingRangeKind.region start text.source.endPos
        addRanges text rest []
    | stx::stxs => match stx with
      | `(namespace $id)  =>
        addRanges text ((id.getId.getNumParts, stx.getPos?)::sections) stxs
      | `(section $(id)?) =>
        addRanges text ((id.map (·.getId.getNumParts) |>.getD 1, stx.getPos?)::sections) stxs
      | `(end $(id)?) => do
        let rec popRanges n sections := do
          if let (size, start)::rest := sections then
            if size == n then
              addRange text FoldingRangeKind.region start stx.getTailPos?
              addRanges text rest stxs
            else if size > n then
              -- we don't add a range here because vscode doesn't like
              -- multiple folding regions with the same start line
              addRanges text ((size - n, start)::rest) stxs
            else
              addRange text FoldingRangeKind.region start stx.getTailPos?
              popRanges (n - size) rest
          else
            addRanges text sections stxs
        popRanges (id.map (·.getId.getNumParts) |>.getD 1) sections
      | `(mutual $body* end) => do
        addRangeFromSyntax text FoldingRangeKind.region stx
        addRanges text [] body.raw.toList
        addRanges text sections stxs
      | _ => do
        if isImport stx then
          let (imports, stxs) := stxs.span isImport
          let last := imports.getLastD stx
          addRange text FoldingRangeKind.imports stx.getPos? last.getTailPos?
          addRanges text sections stxs
        else
          addCommandRange text stx
          addRanges text sections stxs

    addCommandRange text stx :=
      match stx.getKind with
      | `Lean.Parser.Command.moduleDoc =>
        addRangeFromSyntax text FoldingRangeKind.comment stx
      | ``Lean.Parser.Command.declaration => do
        -- When visiting a declaration, attempt to fold the doc comment
        -- separately to the main definition.
        -- We never fold other modifiers, such as annotations.
        if let `($dm:declModifiers $decl) := stx then
          if let some comment := dm.raw[0].getOptional? then
            addRangeFromSyntax text FoldingRangeKind.comment comment

          addRangeFromSyntax text FoldingRangeKind.region decl
        else
          addRangeFromSyntax text FoldingRangeKind.region stx
      | _ =>
        addRangeFromSyntax text FoldingRangeKind.region stx

    addRangeFromSyntax (text : FileMap) kind stx := addRange text kind stx.getPos? stx.getTailPos?

    addRange (text : FileMap) kind start? stop? := do
      if let (some startP, some endP) := (start?, stop?) then
        let startP := text.utf8PosToLspPos startP
        let endP := text.utf8PosToLspPos endP
        if startP.line != endP.line then
          modify fun st => st.push
            { startLine := startP.line
              endLine := endP.line
              kind? := some kind }

partial def handleWaitForDiagnostics (p : WaitForDiagnosticsParams)
    : RequestM (RequestTask WaitForDiagnostics) := do
  let rec waitLoop : RequestM EditableDocument := do
    let doc ← readDoc
    if p.version ≤ doc.meta.version then
      return doc
    else
      IO.sleep 50
      waitLoop
  let t ← RequestM.asTask waitLoop
  RequestM.bindTask t fun doc? => do
    let doc ← liftExcept doc?
    return doc.reporter.map fun _ => pure WaitForDiagnostics.mk

builtin_initialize
  registerLspRequestHandler
    "textDocument/waitForDiagnostics"
    WaitForDiagnosticsParams
    WaitForDiagnostics
    handleWaitForDiagnostics
  registerLspRequestHandler
    "textDocument/completion"
    CompletionParams
    CompletionList
    handleCompletion
  registerLspRequestHandler
    "completionItem/resolve"
    CompletionItem
    CompletionItem
    handleCompletionItemResolve
  registerLspRequestHandler
    "textDocument/hover"
    HoverParams
    (Option Hover)
    handleHover
  registerLspRequestHandler
    "textDocument/declaration"
    TextDocumentPositionParams
    (Array LocationLink)
    (handleDefinition GoToKind.declaration)
  registerLspRequestHandler
    "textDocument/definition"
    TextDocumentPositionParams
    (Array LocationLink)
    (handleDefinition GoToKind.definition)
  registerLspRequestHandler
    "textDocument/typeDefinition"
    TextDocumentPositionParams
    (Array LocationLink)
    (handleDefinition GoToKind.type)
  registerLspRequestHandler
    "textDocument/documentHighlight"
    DocumentHighlightParams
    DocumentHighlightResult
    handleDocumentHighlight
  registerLspRequestHandler
    "textDocument/documentSymbol"
    DocumentSymbolParams
    DocumentSymbolResult
    handleDocumentSymbol
  registerLspRequestHandler
    "textDocument/semanticTokens/full"
    SemanticTokensParams
    SemanticTokens
    handleSemanticTokensFull
  registerLspRequestHandler
    "textDocument/semanticTokens/range"
    SemanticTokensRangeParams
    SemanticTokens
    handleSemanticTokensRange
  registerLspRequestHandler
    "textDocument/foldingRange"
    FoldingRangeParams
    (Array FoldingRange)
    handleFoldingRange
  registerLspRequestHandler
    "$/lean/plainGoal"
    PlainGoalParams
    (Option PlainGoal)
    handlePlainGoal
  registerLspRequestHandler
    "$/lean/plainTermGoal"
    PlainTermGoalParams
    (Option PlainTermGoal)
    handlePlainTermGoal

end Lean.Server.FileWorker
