/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Mac Malone
-/

namespace Itertools

/-- A monadic iterable transformer that iterates until `predM` is satisfied. -/
def MUntil {m : Type → Type u} {α : Type}
  (predM : α → m Bool) (ρ : Type v) := ρ

namespace MUntil
variable {m : Type → Type v} {α : Type} {predM : α → m Bool}

@[inline] def iter (self : MUntil predM ρ) : ρ := self
@[inline] nonrec def predM (self : MUntil predM ρ) := predM

@[inline] protected def forIn [ForIn m ρ α] [Monad m]
(self : MUntil predM ρ) (init : β) (f : α → β → m (ForInStep β)) : m β :=
  forIn self.iter init fun a b => do
    if (← predM a) then ForInStep.done b else f a b

instance [ForIn m ρ α] : ForIn m (MUntil predM ρ) α := ⟨MUntil.forIn⟩
end MUntil

/-- A monadic iterable transformer that iterates until `pred` is satisfied. -/
abbrev Until {α : Type} (pred : α → Bool) (ρ : Type u) :=
  MUntil (m := Id) pred ρ

/-- Iterate until `predM` is satisfied. -/
def untilM {m : Type → Type u} (predM : α → m Bool) (iter : ρ) :
  MUntil predM ρ := iter

/-- Iterate until `pred` is satisfied. -/
def until (pred : α → Bool) (iter : ρ) : Until pred ρ := iter
