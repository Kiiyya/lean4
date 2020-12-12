/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich

The Reader monad transformer for passing immutable State.
-/
prelude
import Init.Control.Basic
import Init.Control.Id
import Init.Control.Except

namespace ReaderT

@[inline] protected def orElse [Alternative m] (x₁ x₂ : ReaderT ρ m α) : ReaderT ρ m α :=
  fun s => x₁ s <|> x₂ s

@[inline] protected def failure [Alternative m] : ReaderT ρ m α :=
  fun s => failure

instance [Monad m] [Alternative m] : Alternative (ReaderT ρ m) where
  failure := ReaderT.failure
  orElse  := ReaderT.orElse

end ReaderT

instance : MonadControl m (ReaderT ρ m) where
  stM      := id
  liftWith f ctx := f fun x => x ctx
  restoreM x ctx := x

instance ReaderT.tryFinally [MonadFinally m] [Monad m] : MonadFinally (ReaderT ρ m) where
  tryFinally' x h ctx := tryFinally' (x ctx) (fun a? => h a? ctx)
