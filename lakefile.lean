import Lake

open Lake DSL System

package cvc5 where
  preferReleaseBuild := true

def Lake.unzip (file : FilePath) (dir : FilePath) : LogIO PUnit := do
  IO.FS.createDirAll dir
  proc (quiet := true) {
    cmd := "unzip"
    args := #["-d", dir.toString, file.toString]
  }

def uncompress (file : FilePath) (dir : FilePath) : LogIO PUnit := do
  if Platform.isWindows || Platform.isOSX then
    untar file dir
  else
    unzip file dir

def cvc5.url := "https://github.com/abdoo8080/cvc5/releases/download"

def cvc5.version := "8aeaa19"

def cvc5.os :=
  if Platform.isWindows then "Win64"
  else if Platform.isOSX then "macOS"
  else "Linux"

def cvc5.arch :=
  if Platform.target.startsWith "x86_64" then "x86_64"
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

/-- Post update hook.

- download cvc5 release files;
- generate/update lean-enumerations.
-/
post_update pkg do
  let cvc5Dir := pkg.dir / s!"cvc5-{cvc5.target}"
  let zipPath := cvc5Dir.addExtension "zip"
  if ← cvc5Dir.pathExists then
    IO.FS.removeDirAll cvc5Dir
  download s!"{cvc5.url}/{cvc5.version}/cvc5-{cvc5.target}.zip" zipPath
  uncompress zipPath pkg.dir
  IO.FS.removeFile zipPath
  generateEnums (cvc5Dir / "include" / "cvc5") pkg

input_file ffi.cpp where
  path := "ffi" / "ffi.cpp"
  text := true

target ffi.o pkg : FilePath := do
  let srcJob ← ffi.cpp.fetch
  let oFile := pkg.buildDir / "ffi" / "ffi.o"
  let flags := #[
    "-std=c++17",
    "-stdlib=libc++",
    "-DCVC5_STATIC_DEFINE",
    "-DLEAN_EXPORTING",
    "-I", (← getLeanIncludeDir).toString,
    "-I", (pkg.dir / s!"cvc5-{cvc5.target}" / "include").toString,
    "-fPIC"
  ]
  buildO oFile srcJob flags

input_file libcadical where
  path := s!"cvc5-{cvc5.target}" / "lib" / nameToStaticLib "cadical"

input_file libcvc5 where
  path := s!"cvc5-{cvc5.target}" / "lib" / nameToStaticLib "cvc5"

input_file libcvc5parser where
  path := s!"cvc5-{cvc5.target}" / "lib" / nameToStaticLib "cvc5parser"

input_file libgmp where
  path := s!"cvc5-{cvc5.target}" / "lib" / nameToStaticLib "gmp"

input_file libgmpxx where
  path := s!"cvc5-{cvc5.target}" / "lib" / nameToStaticLib "gmpxx"

input_file libpicpoly where
  path := s!"cvc5-{cvc5.target}" / "lib" / nameToStaticLib "picpoly"

input_file libpicpolyxx where
  path := s!"cvc5-{cvc5.target}" / "lib" / nameToStaticLib "picpolyxx"

input_file libucrt where
  path := s!"cvc5-{cvc5.target}" / "lib" / nameToStaticLib "ucrt"

def libs : Array (Target FilePath) :=
  if Platform.isWindows then
    #[ffi.o, libcadical, libcvc5, libcvc5parser, libgmp, libgmpxx, libpicpoly, libpicpolyxx, libucrt]
  else
    #[ffi.o, libcadical, libcvc5, libcvc5parser, libgmp, libgmpxx, libpicpoly, libpicpolyxx]

@[default_target]
lean_lib cvc5 where
  precompileModules := true
  moreLinkObjs := libs

@[test_driver]
lean_lib cvc5Test where
  globs := #[Glob.submodules `cvc5Test]
