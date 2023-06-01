/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Mac Malone
-/

namespace Itertools

/-- A monadic iterable transformer that iterates until `predM` is satisfied. -/
def MStopIf {m : Type → Type u} {α : Type}
  (predM : α → m Bool) (ρ : Type v) := ρ

namespace MStopIf
variable {m : Type → Type v} {α : Type} {predM : α → m Bool}

@[inline] def iter (self : MStopIf predM ρ) : ρ := self
@[inline] protected def forIn [ForIn m ρ α] [Monad m]
(self : MStopIf predM ρ) (init : β) (f : α → β → m (ForInStep β)) : m β :=
  forIn self.iter init fun a b => do
    if (← predM a) then return ForInStep.done b else f a b

instance [ForIn m ρ α] : ForIn m (MStopIf predM ρ) α := ⟨MStopIf.forIn⟩
end MStopIf

/-- A monadic iterable transformer that iterates until `pred` is satisfied. -/
abbrev StopIf {α : Type} (pred : α → Bool) (ρ : Type u) :=
  MStopIf (m := Id) pred ρ

/-- Iterate until `predM` is satisfied. -/
def stopIfM {m : Type → Type u} (predM : α → m Bool) (iter : ρ) :
  MStopIf predM ρ := iter

/-- Iterate until `pred` is satisfied. -/
def stopIf (pred : α → Bool) (iter : ρ) : StopIf pred ρ := iter
