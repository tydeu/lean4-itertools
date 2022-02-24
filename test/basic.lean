/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Mac Malone
-/

import Itertools

open Itertools

set_option trace.compiler.ir.result true

def foo :=
  generate 0 (· + 1)
  |> until (· == 10)
  |> filter (· % 2 == 0)
  |> map (· * 2)
  |> array

def foo' :=
  range 10
  |> filter (· % 2 == 0)
  |> map (· * 2)
  |> array

def test1 :=
  array <| filter (fun i => i % 2 == 0) [0:5]

def test2 :=
  array <| filter (fun (i, (_ : Nat)) => i % 2 == 0) <| enumerate [0:5]

def test3 :=
  array <| enumerate [0:5]

def test4 :=
  generate 0 (· + 1)
  |> until (· == 10)
  |> array

def testInf :=
  generate 0 (· + 1)
  |> array

set_option trace.compiler.ir.result false

#eval foo
#eval foo'
#eval test1
#eval test2
#eval test3
#eval test4
