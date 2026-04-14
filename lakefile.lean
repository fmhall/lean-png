import Lake
open System Lake DSL

/-- Run `pkg-config` and split the output into flags. Returns `#[]` on failure. -/
def pkgConfig (pkg : String) (flag : String) : IO (Array String) := do
  let out ← IO.Process.output { cmd := "pkg-config", args := #[flag, pkg] }
  if out.exitCode != 0 then return #[]
  return out.stdout.trimAscii.toString.splitOn " " |>.filter (· ≠ "") |>.toArray

/-- Get libpng include flags, respecting `LIBPNG_CFLAGS` env var override. -/
def libpngCFlags : IO (Array String) := do
  if let some flags := (← IO.getEnv "LIBPNG_CFLAGS") then
    return flags.trimAscii.toString.splitOn " " |>.filter (· ≠ "") |>.toArray
  pkgConfig "libpng" "--cflags"

/-- Extract `-L` library paths from `NIX_LDFLAGS` (set by nix-shell). -/
def nixLdLibPaths : IO (Array String) := do
  let some val := (← IO.getEnv "NIX_LDFLAGS") | return #[]
  return val.splitOn " " |>.filter (·.startsWith "-L") |>.toArray

/-- Get link flags for libpng and zlib. -/
def linkFlags : IO (Array String) := do
  let libPaths ← nixLdLibPaths
  let pngFlags ← pkgConfig "libpng" "--libs"
  if !pngFlags.isEmpty then
    return pngFlags
  return libPaths ++ #["-lpng", "-lz"]

package «lean-png» where
  moreLinkArgs := run_io linkFlags
  testDriver := "test"

require zipCommon from git "https://github.com/kim-em/lean-zip-common" @ "87480b0"
require leanZip from git "https://github.com/kim-em/lean-zip"

lean_lib Png

-- libpng FFI
input_file png_ffi.c where
  path := "c" / "png_ffi.c"
  text := true

target png_ffi.o pkg : FilePath := do
  let srcJob ← png_ffi.c.fetch
  let oFile := pkg.buildDir / "c" / "png_ffi.o"
  let weakArgs := #["-I", (← getLeanIncludeDir).toString] ++ (← libpngCFlags)
  let hardArgs := if Platform.isWindows then #[] else #["-fPIC"]
  buildO oFile srcJob weakArgs hardArgs "cc"

extern_lib libpng_ffi pkg := do
  let ffiO ← png_ffi.o.fetch
  let name := nameToStaticLib "png_ffi"
  buildStaticLib (pkg.staticLibDir / name) #[ffiO]

lean_lib PngTest where
  globs := #[.submodules `PngTest]

@[default_target]
lean_exe test where
  root := `PngTest

lean_exe bench where
  root := `PngBench
