/-!
Tests that `abbrev`s are highlighted like the head of their unfolding, with modifiers reflecting the
abbrev's own type. Abbrevs with parameters used to receive no semantic token at all.
-/

structure Vec (α : Type) (n : Nat) where
  data : Array α

inductive Shape where
  | circle
  | square

def IsBig (n : Nat) : Prop := n = Nat.zero

abbrev Vec3f : Type := Vec Float Nat.zero
abbrev Vec3 (α : Type) : Type := Vec α Nat.zero
abbrev VecImplicit {α : Type} : Type := Vec α Nat.zero
abbrev Shapes (n : Nat) : Type := Vec Shape n
abbrev MyShape := Shape
abbrev IsBig' (n : Nat) : Prop := IsBig n
abbrev MySort (α : Type) : Type := α

def useAbbrevs (v : Vec3f) (w : Vec3 Nat) (u : @VecImplicit Nat) (s : Shapes Nat.zero)
    (t : MyShape) (h : IsBig' Nat.zero) (x : MySort Nat) : Vec Float Nat.zero := v
--^ textDocument/semanticTokens/full
