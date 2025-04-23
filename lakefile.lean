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

namespace cvc5
def url := "https://github.com/abdoo8080/cvc5/releases/download"

def version := "802460d"

def os :=
  if System.Platform.isWindows then "Win64"
  else if System.Platform.isOSX then "macOS"
  else "Linux"

def arch :=
  if System.Platform.target.startsWith "x86_64" then "x86_64"
  else "arm64"

def osArchTarget := s!"{os}-{arch}-static"

namespace zip

def stem : String := "cvc5-" ++ osArchTarget

/-- Name of the directory the archive unzips to. -/
def extractedDirName : FilePath := cvc5.zip.stem
/-- Path to the directory the archive unzips to. -/
def extractedDir (root : FilePath) : FilePath := root / extractedDirName

/-- Name of the archive. -/
def fileName : FilePath := FilePath.addExtension cvc5.zip.stem "zip"
/-- Path to the archive. -/
def file (root : FilePath) : FilePath := root / fileName

/-- URL of the cvc5 C++ archive. -/
def url : String := s!"{cvc5.url}/{cvc5.version}/{cvc5.zip.fileName}"

end zip

/-- Name of the directory that eventually stores the cvc5 sources. -/
def srcDirName : FilePath := s!"{cvc5.zip.stem}-{cvc5.version}"
/-- Path to the directory that eventually stores the cvC5 sources. -/
def srcDir (root : FilePath) : FilePath := root / srcDirName

/-- Name of the C++ library `leanc` will bind. -/
def libFfiName := "cvc5ffi"

end cvc5

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
      "-I", (cvc5.srcDir pkg.buildDir / "include").toString,
      "-fPIC"
    ]
    buildO oFile srcJob flags

def libs := #["cadical", "cvc5", "cvc5parser", "gmp", "gmpxx", "picpoly", "picpolyxx"]

extern_lib cvc5ffi pkg := do
  let logV {m : Type → Type} [Monad m] [MonadLog m] (s : String) : m PUnit :=
    logVerbose s!"[{pkg.name}] {s}"
  -- remove files that are sensitive to API/cvc5 version changes, we're only here because this is
  -- the first build or `ffi/ffi.cpp` has changed
  logV "running"
  let libDir := pkg.leanLibDir
  logV s!"checking `{libDir}`"
  if ← libDir.pathExists then
    let libFfiNamePref := s!"lib{cvc5.libFfiName}"
    for entry in ← libDir.readDir do
      if entry.root = libDir ∧ entry.fileName.startsWith libFfiNamePref then
        logV s!"removing ffi build file {entry.path}"
        IO.FS.removeFile entry.path
  -- download/unzip cvc5 archive if needed
  let srcDir := cvc5.srcDir pkg.buildDir
  if ← srcDir.pathExists then
    logV s!"cvc5 C++ interface up to date"
  else
    logV "setting up cvc5"
    if ← pkg.buildDir.pathExists then
      -- remove any directory that starts with `cvc5.osArchTarget`
      for entry in ← pkg.buildDir.readDir do
        let path := entry.path
        if ← path.isDir then
          let rm :=
            path.fileName.map (fun s => s.startsWith cvc5.osArchTarget)
            |>.getD false
          if rm then IO.FS.removeDirAll path
    let zipFile := cvc5.zip.file pkg.buildDir
    logV s!"- download `{cvc5.zip.url}`"
    download cvc5.zip.url zipFile
    logV s!"- extracting to `{srcDir}`"
    unzip zipFile pkg.buildDir
    IO.FS.rename (cvc5.zip.extractedDir pkg.buildDir) srcDir
    IO.FS.removeFile zipFile
    let cppDir := srcDir / "include" / "cvc5"
    logV s!"- generate lean-level enum-like types ← `{cppDir}`"
    generateEnums cppDir pkg
    logV "done"
  let ffiO ← fetch (pkg.target ``ffi.o)
  logV s!"building FFI static library"
  let libs := libs.map (pure <| srcDir / "lib" / nameToStaticLib ·)
  let libFile := pkg.nativeLibDir / nameToStaticLib cvc5.libFfiName
  buildStaticLib' libFile (libs.push ffiO)
