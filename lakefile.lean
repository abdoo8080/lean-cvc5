import Lake
open Lake DSL

require std from git "https://github.com/leanprover/std4" @ "v4.4.0"
require Qq from git "https://github.com/leanprover-community/quote4" @ "master"

package cvc5 {
  -- srcDir := ""
  precompileModules := true
  moreGlobalServerArgs := #[s!"--load-dynlib={nameToSharedLib "c++"}.1"]
  extraDepTargets := #[`cvc5.cpp]
}

@[default_target]
lean_lib cvc5 {
  moreLeanArgs := #[s!"--load-dynlib={nameToSharedLib "c++"}.1"]
}

def unzip (name : String) (file : FilePath) (dir : FilePath) : LogIO Unit := do
  logVerbose s!"Extracting {name}"
  proc {
    cmd := "unzip"
    args := #["-qd", dir.toString, file.toString]
  }

target cvc5.cpp pkg : Unit := do
  if !(← (pkg.lakeDir / "cvc5").pathExists) then
    download "cvc5" "https://github.com/abdoo8080/lean-smt/releases/download/cvc5/cvc5.zip" (pkg.lakeDir / "cvc5.zip")
    unzip "cvc5" (pkg.lakeDir / "cvc5.zip") pkg.lakeDir
    IO.FS.removeFile (pkg.lakeDir / "cvc5.zip")
  return pure ()

open Lean in
def count [BEq α] [Hashable α] (xs : List α) : HashMap α Nat :=
  go {} xs
where
  go (cs : HashMap α Nat) : List α → HashMap α Nat
    | []      => cs
    | x :: xs =>
      if cs.contains x then
        go (cs.insert x ((cs.find! x) + 1)) xs
      else
        go (cs.insert x 1) xs

def libONames (aFile : FilePath) (ar : FilePath) : BuildM (List FilePath) := do
  logStep s!"Extracting {aFile.fileName.get!}"
  let out ← captureProc {
    cmd := ar.toString
    args := #["t", aFile.toString]
  }
  return (out.split (· == '\n')).map (.mk ·)

def extractO (dir aFile oFile : FilePath) (n : Nat) (ar : FilePath) := do
  proc {
    cmd := ar.toString
    args := #["xN", s!"{n}", "--output", dir.toString, aFile.toString, oFile.toString]
  }
  IO.FS.createDirAll dir
  proc {
    cmd := "mv"
    args := #[(dir / oFile).toString, ((dir / oFile).withExtension s!"{n}.o").toString]
  }

def extractOs (dir aFile oFile : FilePath) (ar : FilePath) : Nat → BuildM Unit
  | 0 => return
  | n + 1 => extractO dir aFile oFile (n + 1) ar >>= fun () => extractOs dir aFile oFile ar n

def getLibOs (lakeDir : FilePath) (name : String) : BuildM (Array (BuildJob FilePath)) := do
  let osDir := lakeDir / "cvc5" / "lib" / name
  if !(← osDir.pathExists) then
    let libA := lakeDir / "cvc5" / "lib" / nameToStaticLib name
    let cvc5Os ← libONames libA (← getLeanAr)
    (count cvc5Os).forM (extractOs osDir libA · (← getLeanAr))
  let cvc5Os ← osDir.readDir
  (cvc5Os.map (·.path)).mapM (inputFile ·)

target cadical.os pkg : Array (BuildJob FilePath) := getLibOs pkg.lakeDir "cadical" >>= pure ∘ pure
target cvc5.os pkg : Array (BuildJob FilePath) := getLibOs pkg.lakeDir "cvc5" >>= pure ∘ pure
target cvc5parser.os pkg : Array (BuildJob FilePath) := getLibOs pkg.lakeDir "cvc5parser" >>= pure ∘ pure
-- target picpoly.os pkg : Array (BuildJob FilePath) := getLibOs pkg.buildDir "picpoly" >>= pure ∘ pure
-- target picpolyxx.os pkg : Array (BuildJob FilePath) := getLibOs pkg.buildDir "picpolyxx" >>= pure ∘ pure

target os pkg : Array (BuildJob FilePath) := do
  let cadicalOs ← fetch (pkg.target ``cadical.os)
  let cvc5Os ← fetch (pkg.target ``cvc5.os)
  let cvc5parserOs ← fetch (pkg.target ``cvc5parser.os)
  -- let picpoly ← fetch (pkg.target ``picpoly.os)
  -- let picpolyxx ← fetch (pkg.target ``picpolyxx.os)
  let os ← BuildJob.collectArray #[cadicalOs, cvc5Os, cvc5parserOs] --, picpoly, picpolyxx]
  return os.map (Array.concatMap id)

def compileO' (name : String) (oFile srcFile : FilePath)
(moreArgs : Array String := #[]) (compiler : FilePath := "cc") : BuildM Unit := do
  logStep s!"Compiling {name}"
  createParentDirs oFile
  proc {
    cmd := compiler.toString
    args := #["-c", "-o", oFile.toString, srcFile.toString] ++ moreArgs
    env := #[("LD_LIBRARY_PATH", none)]
  }

@[inline] def buildO' (name : String)
(oFile : FilePath) (srcJob : BuildJob FilePath)
(weakArgs traceArgs : Array String := #[]) (compiler : FilePath := "cc")
(extraDepTrace : BuildM _ := pure BuildTrace.nil) : SchedulerM (BuildJob FilePath) :=
  let extraDepTrace := return mixTrace (← extraDepTrace) (← computeHash traceArgs)
  buildFileAfterDep oFile srcJob (extraDepTrace := extraDepTrace) fun srcFile => do
    compileO' name oFile srcFile (weakArgs ++ traceArgs) compiler

target ffi.o pkg : FilePath := do
  let oFile := pkg.buildDir / "ffi" / "ffi.o"
  let srcJob ← inputFile <| pkg.dir / "ffi" / "ffi.cpp"
  let flags := #["-stdlib=libc++", "-std=c++17", "-I", (← getLeanIncludeDir).toString, "-I", (pkg.lakeDir / "cvc5" / "include").toString, "-fPIC"]
  buildO' "ffi.cpp" oFile srcJob flags #[] "clang++-15"

extern_lib libcvc5ffi pkg := do
  let name := nameToStaticLib "cvc5ffi"
  let ffiO ← fetch <| pkg.target ``ffi.o
  let os ← fetch (pkg.target ``os)
  let libFile := pkg.nativeLibDir / name
  (os.map (·.push ffiO)).bindAsync fun oFileJobs depTrace => do
    buildFileAfterDepArray libFile oFileJobs (fun oFiles => do
      compileStaticLib name libFile oFiles (← getLeanAr))
      (pure depTrace)
