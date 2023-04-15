
import Mathlib.Util.Frontend
import Mathlib.Order.Height

open Lean System

namespace Lean.Elab

/-- Extract the range of a `Syntax` expressed as lines and columns. -/
-- Extracted from the private declaration `Lean.Elab.formatStxRange`,
-- in `Lean.Elab.InfoTree.Main`.
def stxRange (fileMap : FileMap) (stx : Syntax) : Position × Position :=
  let pos    := stx.getPos?.getD 0
  let endPos := stx.getTailPos?.getD pos
  (fileMap.toPosition pos, fileMap.toPosition endPos)

end Lean.Elab

namespace Lean.Elab.InfoTree

/-- Analogue of `Lean.Elab.InfoTree.findInfo?`, but that returns all results. -/
partial def findAllInfo (t : InfoTree) (ctx : Option ContextInfo) (p : Info → Bool) :
    List (Info × Option ContextInfo) :=
  match t with
  | context ctx t => t.findAllInfo ctx p
  | node i ts  => (if p i then [(i, ctx)] else []) ++ ts.toList.bind (fun t => t.findAllInfo ctx p)
  | _ => []

/-- Return all `TacticInfo` nodes in an `InfoTree` corresponding to tactics,
each equipped with its relevant `ContextInfo`. -/
def findTacticNodes (t : InfoTree) : List (TacticInfo × ContextInfo) :=
  let infos := t.findAllInfo none fun i => match i with
    | .ofTacticInfo _ => true
    | _ => false
  infos.filterMap fun p => match p with
  | (.ofTacticInfo i, some ctx) => (i, ctx)
  | _ => none

-- /--
-- Finds all tactic invocations in an `InfoTree`, reporting
-- * the `ContextInfo` at that point,
-- * the `Syntax` of the tactic
-- * the `List MVarId` of goals before and after the tactic
-- * and the start and end positions of the tactic in the file.
-- -/
-- def tactics (t : InfoTree) :
--     List (ContextInfo × Syntax × List MVarId × List MVarId × Position × Position) :=
--   t.findTacticNodes.map fun ⟨i, ctx⟩ =>
--     ({ ctx with mctx := i.mctxBefore }, i.stx, i.goalsBefore, i.goalsAfter, stxRange ctx.fileMap i.stx)

/-- Discard any enclosing `InfoTree.context` layers. -/
def consumeContext : InfoTree → InfoTree
  | .context _ t => t.consumeContext
  | t => t

/-- Is this `InfoTree` a `TermInfo` for some `Expr`? -/
def ofExpr? (i : InfoTree) : Option Expr := match i with
  | .node (.ofTermInfo i) _ => some i.expr
  | _ => none

/-- Is this `InfoTree` a `TermInfo` for some `Name`? -/
def ofName? (i : InfoTree) : Option Name := i.ofExpr?.bind Expr.constName?

def elabDecl? (t : InfoTree) : Option (Name × InfoTree) :=
  match t.consumeContext with
  | .node (.ofCommandInfo i) c => if i.elaborator == `Lean.Elab.Command.elabDeclaration then
      -- this is hacky: we are relying on the ordering of the child nodes.
      match c.toList.getLast? with
      | some r => match r.consumeContext.ofName? with
        | some n => some (n, t)
        | none => none
      | none => none
    else
      none
  | _ => none

end Lean.Elab.InfoTree

open Lean Elab

def moduleSource (mod : Name) : IO String := do
  IO.FS.readFile (modToFilePath "." mod "lean")

def compileModule (mod : Name) : IO (Environment × List Message × List InfoTree) := do
  Lean.Elab.IO.processInput (← moduleSource mod) none {}

def moduleInfoTrees (mod : Name) : IO (List InfoTree) := do
  let (_env, _msgs, trees) ← compileModule mod
  return trees


/-- Compiles the source file for the named module,
and returns a list containing the name and generated info tree for each declaration. -/
def moduleDeclInfoTrees (mod : Name) : IO (List (Name × InfoTree)) := do
  let trees ← moduleInfoTrees mod
  return trees.filterMap InfoTree.elabDecl?

def declInfoTree (decl : Name) : MetaM InfoTree := do
  match ← findModuleOf? decl with
  | none => throwError s!"Could not determine the module {decl} was declared in."
  | some m =>
      let r ← moduleDeclInfoTrees m
      -- match r.find? fun p => p.1 = decl with
      match r.head? with
      | none => throwError s!"Did not find InfoTree for {decl} in {m}!"
      | some (_, t) => return t

open Lean.Elab

def foo (mod : Name) : IO (List Format) := do
  let trees ← moduleInfoTrees mod
  trees.mapM InfoTree.format


def foo2 (mod : Name) : IO (List Format) := do
  let trees ← moduleDeclInfoTrees mod
  trees.mapM fun (n, t) => do return format (n, ← t.format)

def fs : Syntax → Bool
-- | `(term| by $_tac) => false
| Syntax.node _ `Lean.Parser.Term.byTactic _ => false
| Syntax.node _ `Lean.Parser.Tactic.tacticSeq _ => false
| Syntax.node _ `Lean.Parser.Tactic.tacticSeq1Indented _ => false
| Syntax.node _ `Lean.Parser.Tactic.«tactic_<;>_» _ => false
| Syntax.node _ `Lean.Parser.Tactic.paren _ => false
| Syntax.atom _ _ => false
| _ => true

def tactics (mod : Name) : IO (List (Name × Format)) := do
  let trees ← moduleDeclInfoTrees mod
  let r : List (Name × List Syntax) := trees.map fun (n, t) => (n, t.findTacticNodes.map (fun p => p.1.stx) |>.filter fs)
  return r.map fun p => (p.1, format p.2)

def tactics2 (decl : Name) : MetaM (List Format) := do
  let tree ← declInfoTree decl
  let r : List Syntax := tree.findTacticNodes.map (fun p => p.1.stx) |>.filter fs
  return r.map format

#eval tactics `Mathlib.Order.Height


-- #eval tactics2 `Set.exists_chain_of_le_chainHeight
