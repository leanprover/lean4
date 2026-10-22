module

import Lean

/-! Date validation, package classification, defaults, and unknown deprecation provenance. -/

open Lean

run_cmd do
  for value in ["all", "0001-01-01", "2000-02-29", "2024-02-29", "9999-12-31"] do
    if let .error msg := Deprecation.validateOption `deprecation.warnings (.ofString value) then
      throwError "{msg}"
  for value in ["", "today", "ALL", "all ", "v4.37.0", "1900-02-29", "2023-02-29",
      "2024-00-01", "2024-13-01", "2024-01-00", "2024-04-31", "2024-2-29",
      "2024-02-29 ", "-0001-01-01", "+2024-02-29", "10000-01-01"] do
    if (Deprecation.validateOption `deprecation.warnings (.ofString value)).isOk then
      throwError "accepted invalid cutoff {value}"

run_cmd do
  let env ← getEnv
  let defaults : Options := {}
  unless deprecation.warnings.local.get defaults == "all" do
    throwError "current-package warnings must default to immediate"
  unless Deprecation.shouldWarn env defaults (some env.mainModule) (some "2099-01-01") do
    throwError "current-module warnings must default to immediate"
  let consumer := env.setModulePackage (some "consumer")
  if Deprecation.shouldWarn consumer defaults (some `Init) (some "2099-01-01") then
    throwError "dependency warnings must default to delayed"
  let opts := deprecation.warnings.local.set
    (deprecation.warnings.set defaults "2000-01-01") "2000-01-02"
  unless Deprecation.shouldWarn env opts (some `Init) (some "2000-01-02") do
    throwError "untagged imported modules must share the bootstrap package"
  if Deprecation.shouldWarn consumer opts (some `Init) (some "2000-01-02") then
    throwError "untagged imports must be dependencies of a tagged package"
  unless Deprecation.shouldWarn consumer opts (some consumer.mainModule) (some "2000-01-02") do
    throwError "current-module ownership must not depend on imports"
  for origin in [none, some `Unknown.Module] do
    unless Deprecation.shouldWarn consumer opts origin (some "2099-01-01") do
      throwError "unknown origins must warn immediately"
