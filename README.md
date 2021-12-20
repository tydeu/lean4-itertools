# Lean 4 Itertools

This package provides an assortment of abstraction tools for performing iterations.

```lean
def foo :=
  generate 0 (· + 1)
  |> until (· == 10)
  |> filter (· % 2 == 0)
  |> map (· * 2)
  |> array

#eval foo -- #[0, 4, 8, 12, 16]
````

It makes heavy use of type-level iterators and the `@[inline]` amd `@[specialize]` attributes to produce highly efficient code. This way, write iterators using the tools provided is just as efficient as writing the loop manually.

```text
def Itertools.MGenerate.forIn.loop._at.foo._spec_1 (x_1 : obj) (x_2 : obj) : obj :=
  let x_3 : obj := 10;
  let x_4 : u8 := Nat.decEq x_1 x_3;
  case x_4 : u8 of
  Bool.false →
    let x_5 : obj := 2;
    let x_6 : obj := Nat.mod x_1 x_5;
    let x_7 : obj := 0;
    let x_8 : u8 := Nat.decEq x_6 x_7;
    dec x_6;
    case x_8 : u8 of
    Bool.false →
      let x_9 : obj := 1;
      let x_10 : obj := Nat.add x_1 x_9;
      dec x_1;
      let x_11 : obj := Itertools.MGenerate.forIn.loop._at.foo._spec_1 x_10 x_2;
      ret x_11
    Bool.true →
      let x_12 : obj := Nat.mul x_1 x_5;
      let x_13 : obj := Array.push ◾ x_2 x_12;
      let x_14 : obj := 1;
      let x_15 : obj := Nat.add x_1 x_14;
      dec x_1;
      let x_16 : obj := Itertools.MGenerate.forIn.loop._at.foo._spec_1 x_15 x_13;
      ret x_16
  Bool.true →
    dec x_1;
    ret x_2
def foo._closed_1 : obj :=
  let x_1 : obj := 0;
  let x_2 : obj := Array.mkEmpty ◾ x_1;
  ret x_2
def foo : obj :=
  let x_1 : obj := 0;
  let x_2 : obj := foo._closed_1;
  let x_3 : obj := Itertools.MGenerate.forIn.loop._at.foo._spec_1 x_1 x_2;
  ret x_3
```

It is currently a **work-in-progress**, but isn't everything?
