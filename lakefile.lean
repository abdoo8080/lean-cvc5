import Lake

open Lake DSL System

package cvc5 where
  precompileModules := true
  preferReleaseBuild := true

def Lake.unzip (file : FilePath) (dir : FilePath) : LogIO PUnit := do
  IO.FS.createDirAll dir
  proc (quiet := true) {
    cmd := "unzip"
    args := #["-d", dir.toString, file.toString]
  }

def cvc5.url := "https://github.com/abdoo8080/cvc5/releases/download"

def cvc5.version := "e852a84"

def cvc5.os :=
  if System.Platform.isWindows then "Win64"
  else if System.Platform.isOSX then "macOS"
  else "Linux"

def cvc5.arch :=
  if System.Platform.target.startsWith "x86_64" then "x86_64"
  else "arm64"

def cvc5.target := s!"{os}-{arch}-static"

open IO.Process in
def generateEnums (cppDir : FilePath) (pkg : NPackage _package.name) : IO Unit := do
  let { exitCode, stdout, stderr } ← output {
    cmd := "lean"
    args := #[
      "--run", (pkg.srcDir / "PreBuild.lean").toString,
      -- arguments for `PreBuild.lean` binary: C++ source dir and lean target dir
      cppDir.toString, (pkg.srcDir / "cvc5").toString
    ]
  }
  if 0 < exitCode then
    throw <| .userError s!"C++ to Lean `enum` translation failed with exit code `{exitCode}`:\n\n\
```stdout
{stdout}
```

```stderr
{stderr}
```\
    "

/-- Initialization script.

- download cvc5 release files;
- generate/update lean-enumerations.
-/
script init do
  let ws ← getWorkspace
  let args := ws.lakeArgs?.getD #[]
  let v := Verbosity.normal
  let v := if args.contains "-q" || args.contains "--quiet" then Verbosity.quiet else v
  let v := if args.contains "-v" || args.contains "--verbose" then Verbosity.verbose else v
  let exitCode ← LoggerIO.toBaseIO (minLv := v.minLogLv) <| ws.runLakeT do
    if let some pkg ← findPackage? _package.name then
      let cvc5Dir := pkg.buildDir / s!"cvc5-{cvc5.target}"
      let zipPath := cvc5Dir.addExtension "zip"
      if ← cvc5Dir.pathExists then
        IO.FS.removeDirAll cvc5Dir
      download s!"{cvc5.url}/{cvc5.version}/cvc5-{cvc5.target}.zip" zipPath
      unzip zipPath pkg.buildDir
      IO.FS.removeFile zipPath
      generateEnums (cvc5Dir / "include" / "cvc5") pkg
      return 0
    else
      logError "package not found"
      return 1
  return ⟨exitCode.getD 1⟩

def Lake.compileStaticLib'
  (libFile : FilePath) (oFiles : Array FilePath)
  (ar : FilePath := "ar") (thin := false)
: LogIO Unit := do
  createParentDirs libFile
  let args := #["csqL"]
  let args := if thin then args.push "--thin" else args
  let args := args.push libFile.toString ++ (← mkArgs libFile <| oFiles.map toString)
  proc {cmd := ar.toString, args}

/-- Build a static library from object file jobs using the Lean toolchain's `ar`. -/
def Lake.buildStaticLib'
  (libFile : FilePath) (oFileJobs : Array (Job FilePath)) (thin :=  false)
: SpawnM (Job FilePath) :=
  (Job.collectArray oFileJobs).mapM fun oFiles => do
    buildFileUnlessUpToDate' libFile do
      compileStaticLib' libFile oFiles (← getLeanAr) thin
    return libFile

input_file ffi.cpp where
  path := "ffi" / "ffi.cpp"
  text := true

target ffi.o pkg : FilePath := do
  pkg.afterBuildCacheAsync do
    let srcJob ← ffi.cpp.fetch
    let oFile := pkg.buildDir / "ffi" / "ffi.o"
    let flags := #[
      "-std=c++17",
      "-stdlib=libc++",
      "-I", (← getLeanIncludeDir).toString,
      "-I", (pkg.buildDir / s!"cvc5-{cvc5.target}" / "include").toString,
      "-fPIC"
    ]
    buildO (compiler := "clang") oFile srcJob flags

def libs := #["cadical", "cvc5", "cvc5parser", "gmp", "gmpxx", "picpoly", "picpolyxx"]

target libffi pkg : FilePath := do
  let ffiO ← ffi.o.fetch
  let libs := libs.map (pure <| pkg.buildDir / s!"cvc5-{cvc5.target}" / "lib" / nameToStaticLib ·)
  let libFile := pkg.staticLibDir / nameToStaticLib "ffi"
  buildStaticLib' libFile (libs.push ffiO)

@[default_target]
lean_lib cvc5 where
  moreLinkObjs := #[libffi]

@[test_driver]
lean_lib cvc5Test where
  globs := #[Glob.submodules `cvc5Test]
