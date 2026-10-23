import Lake
open Lake DSL

package «xmss-security» where
  version := v!"0.1.0"

require VCVio from git "https://github.com/Verified-zkEVM/VCVio.git" @ "cbd4144"

@[default_target]
lean_lib Xmss

/-- The SLH-DSA development has no root file: every module in the folder belongs to it. -/
@[default_target]
lean_lib «SLH-DSA-SHAKE-128s» where
  globs := #[.submodules `«SLH-DSA-SHAKE-128s»]

/-- Runs the specification on NIST's ACVP vectors: `lake exe slh-dsa-kat`. -/
lean_exe «slh-dsa-kat» where
  root := `«SLH-DSA-SHAKE-128s».Test.Run
