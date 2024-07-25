import Lake
open Lake DSL

def libcpp : String :=
  if System.Platform.isWindows then "libstdc++-6.dll"
  else if System.Platform.isOSX then "libc++.dylib"
  else "libstdc++.so.6"

package cvc5 {
  precompileModules := true
  moreGlobalServerArgs := #[s!"--load-dynlib={libcpp}"]
  extraDepTargets := #[`libcvc5]
}

@[default_target]
lean_lib cvc5 {
  moreLeanArgs := #[s!"--load-dynlib={libcpp}"]
}

def Lake.unzip (file : FilePath) (dir : FilePath) : LogIO PUnit := do
  IO.FS.createDirAll dir
  proc (quiet := true) {
    cmd := "unzip"
    args := #["-d", dir.toString, file.toString]
  }

def cvc5.url := "https://github.com/abdoo8080/cvc5/releases/download"

def cvc5.version := "v0.0.1"

def cvc5.os :=
  if System.Platform.isWindows then "Win64"
  else if System.Platform.isOSX then "macOS"
  else "Linux"

def cvc5.arch :=
  if System.Platform.target.startsWith "x86_64" then "x86_64"
  else "arm64"

def cvc5.target := s!"{os}-{arch}-static"

target libcvc5 pkg : Unit := do
  if !(← (pkg.lakeDir / s!"cvc5-{cvc5.target}").pathExists) then
    let zipPath := pkg.lakeDir / s!"cvc5-{cvc5.target}.zip"
    download s!"{cvc5.url}/{cvc5.version}/cvc5-{cvc5.target}.zip" zipPath
    unzip zipPath pkg.lakeDir
    IO.FS.removeFile zipPath
  return pure ()

def Lake.compileStaticLib'
  (libFile : FilePath) (oFiles : Array FilePath)
  (ar : FilePath := "ar")
: LogIO Unit := do
  createParentDirs libFile
  proc {
    cmd := ar.toString
    args := #["csqL", libFile.toString] ++ oFiles.map toString
  }

/-- Build a static library from object file jobs using the `ar` packaged with Lean. -/
def Lake.buildStaticLib'
  (libFile : FilePath) (oFileJobs : Array (BuildJob FilePath))
: SpawnM (BuildJob FilePath) :=
  buildFileAfterDepArray libFile oFileJobs fun oFiles => do
    compileStaticLib' libFile oFiles (← getLeanAr)

target ffiO pkg : FilePath := do
  let oFile := pkg.buildDir / "ffi" / "ffi.o"
  let srcJob ← inputFile <| pkg.dir / "ffi" / "ffi.cpp"
  let flags := #[
    "-std=c++17",
    "-I", (← getLeanIncludeDir).toString,
    "-I", (pkg.lakeDir / s!"cvc5-{cvc5.target}" / "include").toString,
    "-fPIC"
  ]
  buildO oFile srcJob flags

extern_lib libffi pkg := do
  let name := nameToStaticLib "ffi"
  let libFile := pkg.nativeLibDir / name
  let ffiO ← fetch (pkg.target ``ffiO)
  let staticLibPath (lib : String) :=
    pkg.lakeDir / s!"cvc5-{cvc5.target}" / "lib" / nameToStaticLib lib
  let libcadical := pure (staticLibPath "cadical")
  let libcvc5 := pure (staticLibPath "cvc5")
  let libcvc5parser := pure (staticLibPath "cvc5parser")
  let libgmp := pure (staticLibPath "gmp")
  let libpicpoly := pure (staticLibPath "picpoly")
  let libpicpolyxx := pure (staticLibPath "picpolyxx")
  let mut libs := #[ffiO, libcadical, libcvc5, libcvc5parser, libpicpoly, libpicpolyxx]
  if System.Platform.isOSX then libs := libs.push libgmp
  buildStaticLib' libFile libs



section test

open System

partial def readAllFiles (dir : FilePath) : IO (Array FilePath) := do
  let mut files := #[]
  for entry in (← FilePath.readDir dir) do
    if ← entry.path.isDir then
      files := (← readAllFiles entry.path) ++ files
    else
      files := files.push entry.path
  return files

/-- Naive implementation. -/
partial def isSubstring (sub str : String) (start := 0) : Bool := Id.run do
  let mut idx := start
  let mut okay := true
  for c in sub.data do
    match str.get? <| String.Pos.mk idx with
    | none =>
      return false
    | some c' =>
      if c = c' then
        idx := idx.succ
        continue
      else
        okay := false
        break
  if okay then
    return true
  else
    return isSubstring sub str start.succ

/-- Run with `lake script run test` or just `lake test`.

The input arguments `args` define a `cargo`-style filter over the tests to run. If empty, then all
tests run. Otherwise, a test with path `path` runs iff there is a `arg ∈ args` such that `arg` is a
substring of `path`.
-/
@[test_runner]
script test args := do
  if args.any fun arg => arg = "-h" ∨ arg = "--help" then
    showReadme
    return 0

  /- True if the file is accepted by the user's filter. -/
  let isFileRequested : FilePath → Bool :=
    if let [] := args
    then fun _ => true
    else fun file =>
      let file := file.toString
      args.any fun arg => isSubstring arg file

  /- Total number of tests, including ignored ones. -/
  let mut total := 0
  /- Tests to run, i.e. requested by the user. -/
  let mut todo := #[]

  -- sets `total` and `todo`
  for file in ← readAllFiles (FilePath.mk "Test") do
    if file.extension = "lean" then
      total := total.succ
      if isFileRequested file then
        todo := todo.push file

  /- Test tasks to join. -/
  let mut tasks := []

  -- nothing to do, warn user
  if todo.isEmpty then
    if total = 0 then
      println! "`Test` directory does not contain any `.lean` file"
    else
      println! "none of the {total} test{plural total} in `Test` match your filter {args}"
  else
    -- let's do this
    println! "running {todo.size} test{plural todo.size}..."

    -- spawn test tasks, populate `tasks`
    for file in todo do
      let task ← IO.asTask (runTest file (← readThe Lake.Context))
      tasks := task :: tasks

  -- join all `tasks` and count failures
  let mut failed := 0
  for task in tasks do
    let okay ← IO.ofExcept task.get
    if ¬ okay then
      failed := failed.succ

  -- produce final summary
  let success := todo.size - failed
  let failed_blah :=
    if failed = 0 then "" else s!"\n- ❌ {failed} test{plural failed} failed"
  let ignored_blah :=
    let ignored := total - todo.size
    if ignored = 0 then "" else s!"\n- ⏭️  {ignored} test{plural ignored} ignored by your filter"

  println! "\ndone running {todo.size} test{plural todo.size}
- ✅ {success} successful test{plural success}{failed_blah}{ignored_blah}\
    "

  if 0 < failed then
    return 1
  else
    return 0
where
  /-- Returns `""` if the input natural is `1`, `"s"` otherwise. -/
  plural : Nat → String
  | 1 => ""
  | _ => "s"

  /-- Shows the test framework's readme. -/
  showReadme : ScriptM Unit := do
    let path : FilePath := "Test/readme.md"
    if ¬ (← path.pathExists) ∨ (← path.isDir) then
      IO.eprintln s!"file `{path}` does not exist, did you modify this repository?"
    else
      let help ← IO.FS.readFile path
      println! "The following is the content of `{path}`.\n\n"
      println! help

  /-- Returns `true` if the test succeeded, `false` otherwise.

  Will search for an *"expected output file"* `<file>.expected`. If none is found, then the test is
  expected to have return code `0` and produce no output.
  -/
  runTest (file : FilePath) : ScriptM Bool := do
    -- files for expected stdout/stderr
    let expectedFile := file.withExtension "expected"
    let expectedErrFile := expectedFile.withExtension "err"

    -- extract expected stdout string
    let expectedOut ←
      if ← expectedFile.pathExists then
        if ← expectedFile.isDir then
          println! "\
            [{file}] illegal expected output path `{expectedFile}`: \
            expected file, found directory\
          "
          return false
        else
          IO.FS.readFile expectedFile
      else
        pure ""
    -- trimmed version of stdout for user convenience
    let expectedOut := expectedOut.trim

    -- extract expected stderr string and whether we're confirming a success or a failure
    let (expectedErr, expectSuccess) ←
      if ← expectedErrFile.pathExists then
        if ← expectedErrFile.isDir then
          println! "\
            [{file}] illegal expected error output path `{expectedErrFile}`: \
            expected file, found directory\
          "
          return false
        else
          pure (← IO.FS.readFile expectedFile, false)
      else
        pure ("", true)
    -- trimmed version of stderr for user convenience
    let expectedErr := expectedErr.trim

    -- run the test, retrieve the output
    let imports ← Lean.parseImports' (← IO.FS.readFile file) file.fileName.get!
    let modules ← imports.filterMapM (findModule? ∘ Lean.Import.module)
    let out ← IO.Process.output {
      cmd := (← getLean).toString
      args :=
        #[s!"--load-dynlib={libcpp}"]
        ++ modules.map (s!"--load-dynlib={·.dynlibFile}")
        ++ #[file.toString]
      env := ← getAugmentedEnv
    }

    -- trim stdout and stderr for user convenience
    let (stdout, stderr) := (out.stdout.trim, out.stderr.trim)

    /- stores the strings that discuss what failed
      note that these strings all start with a newline
    -/
    let mut failures := #[]

    -- confirm success/failure
    if (expectSuccess ∧ out.exitCode ≠ 0) ∨ (¬ expectSuccess ∧ out.exitCode = 0) then
      let exp :=
        if expectSuccess then "exit code `0`" else "non-zero exit code"
      failures := failures.push s!"
  - expected {exp}, got exit code {out.exitCode}\
        "

    -- confirm stdout
    if stdout ≠ expectedOut then
      failures := failures.push s!"
  - expected stdout
    ```
    {expectedOut}
    ```

    but got
    ```
    {stdout}
    ```\
      "

    -- confirm stderr
    if stderr ≠ expectedErr then
      failures := failures.push s!"
  - expected stderr
    ```
    {expectedErr}
    ```

    but got
    ```
    {stderr}
    ```\
      "

    -- final test report
    if failures.isEmpty then
      println! "- ✅ `{file}`: success"
      return true
    else
      let blah := failures.foldl String.append ""
      println! "- ❌ `{file}`: failure{blah}"
      return false

end test
