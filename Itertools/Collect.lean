/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Mac Malone
-/

namespace Itertools

/-- Produce a `List` from a monadic iterable in reverse order. -/
@[inline] def revListM [ForIn m ρ α] [Monad m] (iter : ρ) : m (List α) := do
  let mut lst := []
  for a in iter do
    lst := a :: lst
  return lst

/-- Produce a `List` from a pure iterable in reverse order. -/
@[inline] def revList [ForIn Id ρ α] (iter : ρ) : List α :=
  Id.run <| revListM iter

/-- Produce a `List` from a monadic iterable. -/
@[inline] def listM [ForIn m ρ α] [Monad m] (iter : ρ) : m (List α) :=
  (·.reverse) <$> revListM iter

/-- Produce a `List` from a pure iterable. -/
@[inline] def list [ForIn Id ρ α] (iter : ρ) : List α :=
  revList iter |>.reverse

instance [ForIn Id ρ α] : Coe ρ (List α) := ⟨list⟩

/-- Produce an `Array` from a monadic iterable. -/
@[inline] def arrayM [ForIn m ρ α] [Monad m] (iter : ρ) : m (Array α) := do
  let mut arr := #[]
  for a in iter do
    arr := arr.push a
  return arr

/-- Produce an `Array` from a pure iterable. -/
@[inline] def array [ForIn Id ρ α] (iter : ρ) : Array α :=
  Id.run <| arrayM iter

instance [ForIn Id ρ α] : Coe ρ (Array α) := ⟨array⟩
