import Lake
open Lake DSL

package itertools

@[default_target]
lean_lib Itertools

script test do
  let testFile : FilePath := "test" / "basic.lean"
  let eOutFile := testFile.withExtension "expected.out"
  let eOut ← IO.FS.readFile eOutFile
  let out ← IO.Process.output {
    cmd := (← getLean).toString, args := #[testFile.toString], env := ← getAugmentedEnv
  }
  let pOut := out.stderr ++ out.stdout
  let pOutFile := testFile.withExtension "produced.out"
  IO.FS.writeFile pOutFile pOut
  if eOut = pOut then
    IO.eprintln s!"{testFile}: output matched"
    return 0
  else
    IO.eprintln s!"{testFile}: produced output did not match expected output"
    return 1
