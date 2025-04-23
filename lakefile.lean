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

def cvc5.version := "802460d"

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

/-- Post-update script script.

- remove `libffi.*` files if any;
- download cvc5 release files;
- generate/update lean-enumerations.
-/
post_update pkg do
  let log {m : Type → Type} [Monad m] [MonadLog m] (s : String) : m _ :=
    logVerbose s!"{s}"
  -- remove files that are sensitive to API/cvc5 version changes
  let libDir := pkg.leanLibDir
  if ← libDir.pathExists then
    for file in ← libDir.readDir do
      if file.root = libDir ∧ file.fileName.startsWith "libffi" then
        log s!"removing ffi build file {file.path}"
        IO.FS.removeFile file.path
  -- download/unzip cvc5 archive if needed
  let cvc5ZipDir := pkg.buildDir / s!"cvc5-{cvc5.target}"
  if ← cvc5ZipDir.pathExists then
    log s!"cvc5 C++ interface up to date, nothing to do"
  else
    let zipUrl := s!"{cvc5.url}/{cvc5.version}/cvc5-{cvc5.target}.zip"
    log s!"downloading `{zipUrl}`"
    let zipPath := cvc5ZipDir.addExtension "zip"
    if ← cvc5ZipDir.pathExists then
      IO.FS.removeDirAll cvc5ZipDir
    download zipUrl zipPath
    log s!"extracting `{zipPath}`"
    unzip zipPath pkg.buildDir
    IO.FS.removeFile zipPath
    log s!"generating lean-level enum-like types"
    generateEnums (cvc5ZipDir / "include" / "cvc5") pkg
  log "done"

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
  (libFile : FilePath) (oFileJobs : Array (Job FilePath))
: SpawnM (Job FilePath) :=
  buildFileAfterDep libFile (.collectArray oFileJobs) fun oFiles => do
    compileStaticLib' libFile oFiles (← getLeanAr)

target ffi.o pkg : FilePath := do
  pkg.afterBuildCacheAsync do
    let oFile := pkg.buildDir / "ffi" / "ffi.o"
    let srcJob ← inputBinFile <| pkg.dir / "ffi" / "ffi.cpp"
    let flags := #[
      "-std=c++17",
      "-stdlib=libc++",
      "-I", (← getLeanIncludeDir).toString,
      "-I", (pkg.buildDir / s!"cvc5-{cvc5.target}" / "include").toString,
      "-fPIC"
    ]
    buildO oFile srcJob flags

def libs := #["cadical", "cvc5", "cvc5parser", "gmp", "gmpxx", "picpoly", "picpolyxx"]

extern_lib libffi pkg := do
  let ffiO ← fetch (pkg.target ``ffi.o)
  let libs := libs.map (pure <| pkg.buildDir / s!"cvc5-{cvc5.target}" / "lib" / nameToStaticLib ·)
  let libFile := pkg.nativeLibDir / nameToStaticLib "ffi"
  buildStaticLib' libFile (libs.push ffiO)
