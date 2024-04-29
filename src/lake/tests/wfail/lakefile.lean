import Lake
open Lake DSL

package test

lean_lib Warn

target warn : PUnit := Job.async do
  logWarning "foo"
  return ((), .nil)

target warnArt pkg : PUnit := Job.async do
  let warnArtFile := pkg.buildDir / "warn_art"
  (((), ·)) <$> buildFileUnlessUpToDate warnArtFile .nil do
    logWarning "foo-file"
    createParentDirs warnArtFile
    IO.FS.writeFile warnArtFile ""
