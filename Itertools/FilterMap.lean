/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Mac Malone
-/

namespace Itertools

--------------------------------------------------------------------------------
-- # Filter
--------------------------------------------------------------------------------

/-- A monadic iterable transformer that performs a filter. -/
def MFilter {m : Type → Type u} {α : Type}
  (predM : α → m Bool) (ρ : Type v) := ρ

namespace MFilter
variable {m : Type → Type v} {α : Type} {predM : α → m Bool}

@[inline] def iter (self : MFilter predM ρ) : ρ := self
@[inline] nonrec def predM (self : MFilter predM ρ) := predM

@[inline] protected def forIn [ForIn m ρ α] [Monad m]
(self : MFilter predM ρ) (init : β) (f : α → β → m (ForInStep β)) : m β :=
  forIn self.iter init fun a b => do
    if (← predM a) then f a b else ForInStep.yield b

instance [ForIn m ρ α] : ForIn m (MFilter predM ρ) α := ⟨MFilter.forIn⟩
end MFilter

/-- A pure iterable transformer that performs a filter. -/
abbrev Filter {α : Type} (pred : α → Bool) (ρ : Type u) :=
  MFilter (m := Id) pred ρ

@[inline] nonrec def Filter.pred {m : Type → Type v} {pred : α → Bool}
  (self : Filter pred ρ) := pred

/-- Filter values from `iter` that do not satisfy `predM`. -/
@[inline] def filterM {m : Type → Type u} (predM : α → m Bool) (iter : ρ) :
  MFilter predM ρ := iter

/-- Filter values from `iter` that do not satisfy `pred`. -/
@[inline] def filter (pred : α → Bool) (iter : ρ) : Filter pred ρ := iter

--------------------------------------------------------------------------------
-- # Map
--------------------------------------------------------------------------------

/-- A monadic iterable transformer that performs a map. -/
def MMap {m : Type u → Type u'} {α : Type v} {α' : Type u}
  (fnM : α → m α') (ρ : Type w) := ρ

namespace MMap
variable {m : Type u → Type v} {α : Type v} {α' : Type u} {fnM : α → m α'}

@[inline] def iter (self : MMap fnM ρ) : ρ := self
@[inline] nonrec def fnM (self : MMap fnM ρ) := fnM

@[inline] protected def forIn [ForIn m ρ α] [Monad m]
(self : MMap fnM ρ) (init : β) (f : α' → β → m (ForInStep β)) : m β :=
  forIn self.iter init fun a b => do f (← fnM a) b

instance [ForIn m ρ α] : ForIn m (MMap fnM ρ) α' := ⟨MMap.forIn⟩
end MMap

/-- A pure iterable transformer that performs a map. -/
abbrev Map {α : Type u} {α' : Type v} (fn : α → α') (ρ : Type w) :=
  MMap (m := Id) fn ρ

@[inline] nonrec def Map.fn {fn : α → α'} (self : Map fn ρ) := fn

/-- Apply `fnM` to each value from `iter` to produce a new iterable. -/
@[inline] def mapM {m : Type → Type u} (fnM : α → m α') (iter : ρ) :
  MMap fnM ρ := iter

/-- Apply `fn` to each value from `iter` to produce a new iterable. -/
@[inline] def map (fn : α → α') (iter : ρ) : Map fn ρ := iter
