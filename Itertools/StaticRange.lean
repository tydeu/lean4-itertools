/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Mac Malone
-/

namespace Itertools

/-- A type-level `Std.Range`. -/
def StaticRange {α : Type u} (start stop step : α) : Type := PUnit

namespace StaticRange
variable {α : Type u} {start stop step : α}

@[inline] nonrec def start (self : StaticRange start stop step) := start
@[inline] nonrec def stop (self : StaticRange start stop step) := stop
@[inline] nonrec def step (self : StaticRange start stop step) := step

variable [LE α] [(a b : α) → Decidable (a ≤ b)] [Add α]

@[inline] protected partial def forIn [Monad m]
(self : StaticRange start stop step) (init : β) (f : α → β → m (ForInStep β)) : m β := do
  let rec @[specialize] loop i b := do
    if i ≥ stop then
      pure b
    else
      match (← f i b) with
      | ForInStep.done b => pure b
      | ForInStep.yield b => loop (i + step) b
  loop start init

instance : ForIn m (StaticRange start stop step) α := ⟨StaticRange.forIn⟩
end StaticRange

/-- Generate an iterable static range of numeric values. -/
@[inline] def range [OfNat α 0] [OfNat α 1] (stop : α) (start : α := 0) (step : α := 1) :
  StaticRange start stop step := ⟨⟩
