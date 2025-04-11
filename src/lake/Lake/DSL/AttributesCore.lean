/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
prelude
import Lake.Util.OrderedTagAttribute

open Lean
namespace Lake

builtin_initialize packageAttr : OrderedTagAttribute ←
  registerOrderedTagAttribute `package "mark a definition as a Lake package configuration"

builtin_initialize packageDepAttr : OrderedTagAttribute ←
  registerOrderedTagAttribute `package_dep "mark a definition as a Lake package dependency"

builtin_initialize postUpdateAttr : OrderedTagAttribute ←
  registerOrderedTagAttribute `post_update "mark a definition as a Lake package post-update hook"

builtin_initialize scriptAttr : OrderedTagAttribute ←
  registerOrderedTagAttribute `script "mark a definition as a Lake script"

builtin_initialize defaultScriptAttr : OrderedTagAttribute ←
  registerOrderedTagAttribute `default_script "mark a Lake script as the package's default"
    fun name => do
      unless (← getEnv <&> (scriptAttr.hasTag · name)) do
        throwError "attribute `default_script` can only be used on a `script`"

builtin_initialize leanLibAttr : OrderedTagAttribute ←
  registerOrderedTagAttribute `lean_lib "mark a definition as a Lake Lean library target configuration"

builtin_initialize leanExeAttr : OrderedTagAttribute ←
  registerOrderedTagAttribute `lean_exe "mark a definition as a Lake Lean executable target configuration"

builtin_initialize externLibAttr : OrderedTagAttribute ←
  registerOrderedTagAttribute `extern_lib "mark a definition as a Lake external library target"

builtin_initialize inputFileAttr : OrderedTagAttribute ←
  registerOrderedTagAttribute `input_file "mark a definition as a Lake input file target"

builtin_initialize inputDirAttr : OrderedTagAttribute ←
  registerOrderedTagAttribute `input_dir "mark a definition as a Lake input directory target"

builtin_initialize targetAttr : OrderedTagAttribute ←
  registerOrderedTagAttribute `target "mark a definition as a Lake target"

builtin_initialize defaultTargetAttr : OrderedTagAttribute ←
  registerOrderedTagAttribute `default_target "mark a Lake target as the package's default"
    fun name => do
      let valid ← getEnv <&> fun env =>
        targetAttr.hasTag env name
      unless valid do
        throwError "attribute `default_target` can only be used on a target (e.g., `lean_lib`, `lean_exe`)"

builtin_initialize testDriverAttr : OrderedTagAttribute ←
  registerOrderedTagAttribute `test_driver "mark a Lake script, executable, or library as package's test driver"
    fun name => do
      let valid ← getEnv <&> fun env =>
        scriptAttr.hasTag env name ||
        leanExeAttr.hasTag env name ||
        leanLibAttr.hasTag env name
      unless valid do
        throwError "attribute `test_driver` can only be used on a `script`, `lean_exe`, or `lean_lib`"

builtin_initialize lintDriverAttr : OrderedTagAttribute ←
  registerOrderedTagAttribute `lint_driver "mark a Lake script or executable as package's linter"
    fun name => do
      let valid ← getEnv <&> fun env =>
        scriptAttr.hasTag env name ||
        leanExeAttr.hasTag env name
      unless valid do
        throwError "attribute `lint_driver` can only be used on a `script` or `lean_exe`"

builtin_initialize moduleFacetAttr : OrderedTagAttribute ←
  registerOrderedTagAttribute `module_facet "mark a definition as a Lake module facet"

builtin_initialize packageFacetAttr : OrderedTagAttribute ←
  registerOrderedTagAttribute `package_facet "mark a definition as a Lake package facet"

builtin_initialize libraryFacetAttr : OrderedTagAttribute ←
  registerOrderedTagAttribute `library_facet "mark a definition as a Lake library facet"
