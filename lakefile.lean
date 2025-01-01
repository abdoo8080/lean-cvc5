import Lake

open Lake DSL System

package cvc5 where
  precompileModules := true
  preferReleaseBuild := true

@[default_target]
lean_lib cvc5

@[test_driver]
lean_lib cvc5Test where
  globs := #[Glob.submodules `cvc5Test]

def Lake.unzip (file : FilePath) (dir : FilePath) : LogIO PUnit := do
  IO.FS.createDirAll dir
  proc (quiet := true) {
    cmd := "unzip"
    args := #["-d", dir.toString, file.toString]
  }

def cvc5.url := "https://github.com/abdoo8080/cvc5/releases/download"

def cvc5.version := "cvc5-1.2.1"

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
      "--", -- arguments for `PreBuild.lean` binary: C++ source dir and lean target dir
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

target libcvc5 pkg : FilePath := do
  let cvc5Dir := pkg.buildDir / s!"cvc5-{cvc5.target}"
  if !(← cvc5Dir.pathExists) then
    let zipPath := pkg.buildDir / s!"cvc5-{cvc5.target}.zip"
    download s!"{cvc5.url}/{cvc5.version}/cvc5-{cvc5.target}.zip" zipPath
    unzip zipPath pkg.buildDir
    IO.FS.removeFile zipPath
    generateEnums (cvc5Dir / "include" / "cvc5") pkg
  return pure cvc5Dir

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

target ffi.o pkg : FilePath := do
  let cvc5Dir ← fetch (pkg.target ``libcvc5)
  cvc5Dir.bindAsync fun cvc5Dir cvc5Trace => do
    let oFile := pkg.buildDir / "ffi" / "ffi.o"
    let srcJob ← inputBinFile <| pkg.dir / "ffi" / "ffi.cpp"
    let flags := #[
      "-std=c++17",
      "-stdlib=libc++",
      "-I", (← getLeanIncludeDir).toString,
      "-I", (cvc5Dir / "include").toString,
      "-fPIC"
    ]
    buildO oFile srcJob flags (extraDepTrace := pure cvc5Trace)

extern_lib libffi pkg := do
  let ffiO ← fetch (pkg.target ``ffi.o)
  let cvc5Dir ← fetch (pkg.target ``libcvc5)
  cvc5Dir.bindAsync fun cvc5Dir cvc5Trace => do
    let name := nameToStaticLib "ffi"
    let libFile := pkg.nativeLibDir / name
    let staticLibPath (lib : String) :=
      cvc5Dir / "lib" / nameToStaticLib lib
    let libcadical := pure (staticLibPath "cadical", cvc5Trace)
    let libcvc5 := pure (staticLibPath "cvc5", cvc5Trace)
    let libcvc5parser := pure (staticLibPath "cvc5parser", cvc5Trace)
    let libgmp := pure (staticLibPath "gmp", cvc5Trace)
    let libgmpxx := pure (staticLibPath "gmpxx", cvc5Trace)
    let libpicpoly := pure (staticLibPath "picpoly", cvc5Trace)
    let libpicpolyxx := pure (staticLibPath "picpolyxx", cvc5Trace)
    let mut libs := #[ffiO, libcadical, libcvc5, libcvc5parser, libgmp, libgmpxx, libpicpoly, libpicpolyxx]
    buildStaticLib' libFile libs
