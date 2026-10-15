/-!
Tests the fork's semantic highlighting: token types and modifiers derived from elaboration info,
e.g. structures vs. inductives vs. classes, types vs. props vs. values vs. proofs, constructors,
projections, theorems, sorts, local variables, recursive references and `example`s.
-/

structure Point where
  x : Nat
  y : Nat

inductive Color where
  | red
  | green

class Shape (α : Type) where
  area : α → Nat

instance : Shape Point where
  area p := p.x

def Point.origin : Point := ⟨Nat.zero, Nat.zero⟩

def addX (p : Point) (n : Nat) : Point := { p with x := p.x + n }

def IsOrigin (p : Point) : Prop := p.x = Nat.zero ∧ p.y = Nat.zero

theorem origin_isOrigin : IsOrigin Point.origin := ⟨rfl, rfl⟩

def useProof (h : IsOrigin Point.origin) : Point.origin.x = Nat.zero := h.1

def favorite : Color := Color.green

def mkPair (a : Nat) : Nat × Nat := Prod.mk a a

def sorts (α : Type) (P : Prop) : Type := α

def countDown : Nat → Nat
  | Nat.zero => Nat.zero
  | Nat.succ n => countDown n

def withLet (n : Nat) : Nat :=
  let m := Nat.succ n
  m

example (p : Point) : Nat := p.y
--^ textDocument/semanticTokens/full
