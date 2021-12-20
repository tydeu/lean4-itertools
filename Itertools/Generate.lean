/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Mac Malone
-/

namespace Itertools

--------------------------------------------------------------------------------
-- # Partial Generator
--------------------------------------------------------------------------------

/-- A monadic generator that stops if/when wither `initM` or `stepM` return `none`. -/
def MGenerateSome {m : Type u → Type v} {α : Type u}
  (initM : m (Option α)) (stepM : α → m (Option α)) : Type := PUnit

namespace MGenerateSome
variable {m : Type u → Type v} {α : Type u}
variable {initM : m (Option α)} {stepM : α → m (Option α)}

@[inline] nonrec def initM (self : MGenerateSome initM stepM) := initM
@[inline] nonrec def stepM (self : MGenerateSome initM stepM) := stepM

@[inline] protected partial def forIn [Monad m]
(self : MGenerateSome initM stepM) (init : β) (f : α → β → m (ForInStep β)) : m β := do
  let rec @[specialize] loop a b := do
    match (← f a b) with
    | ForInStep.yield b =>
      match (← stepM a) with
      | some a => loop a b
      | none => pure b
    | ForInStep.done b => pure b
  match (← initM) with
  | some a => loop a init
  | none => pure init

instance : ForIn m (MGenerateSome initM stepM) α := ⟨MGenerateSome.forIn⟩
end MGenerateSome

/-- A pure generator that stops if/when wither `init` or `step` returns `none`. -/
abbrev GenerateSome {α : Type u} (init : Option α) (step : α → Option α)  :=
  MGenerateSome (m := Id) init step

namespace GenerateSome
variable {α : Type u} {init : Option α} {step : α → Option α}
@[inline] nonrec def init (self : GenerateSome init step) := init
@[inline] nonrec def step (self : GenerateSome init step) := step
end GenerateSome

/--
Generate a iterable of values within the monad `m`,
starting with `init` and continuing with `step` until either returns `none`.
-/
@[inline] def generateSomeM {m : Type u → Type v}
  (initM : m (Option α)) (stepM : α → m (Option α)) :
  MGenerateSome initM stepM := ⟨⟩

/--
Generate a iterable of values,
starting with `init` and continuing with `step` until either returns `none`.
-/
@[inline] def generateSome (init : Option α) (step : α → Option α) :
  GenerateSome init step := ⟨⟩

--------------------------------------------------------------------------------
-- # Infinite Generator
--------------------------------------------------------------------------------

/- A monadic generator, starts with `initM` and progresses with `stepM` forever. -/
def MGenerate {m : Type u → Type v} {α : Type u}
  (initM : m α) (stepM : α → m α) : Type := PUnit

namespace MGenerate
variable {m : Type u → Type v} {α : Type u}
variable {initM : m α} {stepM : α → m α}

@[inline] nonrec def initM (self : MGenerate initM stepM) := initM
@[inline] nonrec def stepM (self : MGenerate initM stepM) := stepM

@[inline] protected partial def forIn [Monad m]
(self : MGenerate initM stepM) (init : β) (f : α → β → m (ForInStep β)) : m β := do
  let rec @[specialize] loop a b := do
    match (← f a b) with
    | ForInStep.yield b => loop (← stepM a) b
    | ForInStep.done b => pure b
  loop (← initM) init

instance : ForIn m (MGenerate initM stepM) α := ⟨MGenerate.forIn⟩
end MGenerate

/- A pure generator, starts with `init` and progresses with `step` forever. -/
abbrev Generate {α : Type u} (init : α) (step : α → α)  :=
  MGenerate (m := Id) init step

namespace Generate
variable {α : Type u} {init : α} {step : α → α}
@[inline] nonrec def init (self : Generate init step) := init
@[inline] nonrec def step (self : Generate init step) := step
end Generate

/--
Generate a iterable of values within the monad `m`,
starting with `initM` and continuing infinitely with `stepM`.
-/
@[inline] def generateM {m : Type u → Type v}
  (initM : m α) (stepM : α → m α) :
  MGenerate initM stepM := ⟨⟩

/--
Generate a iterable of values,
starting with `init` and continuing infinitely with `step`.
-/
@[inline] def generate (init : α) (step : α → α) :
  Generate init step := ⟨⟩


--------------------------------------------------------------------------------
-- # Generator Transformer
--------------------------------------------------------------------------------

/-- A monadic iterable transformer, that generates values alongside its iterable. -/
def MGenerateEach {σ : Type u} {m : Type u → Type v}
  (initM : m σ) (stepM : σ → m σ) (ρ : Type w) := ρ

namespace MGenerateEach
variable {σ : Type u} {m : Type u → Type v} {ρ : Type w}
variable {initM : m σ} {stepM : σ → m σ}

@[inline] def iter (self : MGenerateEach initM stepM ρ) : ρ := self
@[inline] nonrec def initM (self : MGenerateEach initM stepM ρ) := initM
@[inline] nonrec def stepM (self : MGenerateEach initM stepM ρ) := stepM

@[inline] protected def forIn [ForIn m ρ α] [Monad m]
(self : MGenerateEach initM stepM ρ) (init : β) (f : (σ × α) → β → m (ForInStep β)) : m β := do
  Prod.snd <$> forIn self.iter (← initM, init) fun a (i, b) => do
    match (← f (i, a) b) with
    | ForInStep.yield b => ForInStep.yield (← stepM i, b)
    | ForInStep.done b => ForInStep.done (i, b)

instance [ForIn m ρ α] : ForIn m (MGenerateEach initM stepM ρ) (σ × α) := ⟨MGenerateEach.forIn⟩
end MGenerateEach

/-- A pure iterable transformer, that generates values alongside its iterable. -/
abbrev GenerateEach {σ : Type u} (init : σ) (step : σ → σ) (ρ : Type v) :=
  MGenerateEach (m := Id) init step ρ

namespace GenerateEach
variable {σ : Type u} {init : σ} {step : σ → σ} {ρ : Type v}
@[inline] nonrec def init (self : GenerateEach init step ρ) := init
@[inline] nonrec def step (self : GenerateEach init step ρ) := step
end GenerateEach

/-- Generate values alongside `iter`, producing a iterable of the product. -/
def generateEachM {m : Type u → Type v} (initM : m σ) (stepM : σ → m σ) (iter : ρ) :
  MGenerateEach initM stepM ρ := iter

/-- Generate values alongside `iter`, producing a iterable of the product. -/
def generateEach (init : σ) (step : σ → σ) (iter : ρ) :
  GenerateEach init step ρ := iter

/-- Attach an index starting at `start` and stepping by `step` to `iter`. -/
def enumerate (iter : ρ) (start := 0) (step := 1) :=
  iter |> generateEach start fun n => n + step
