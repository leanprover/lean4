    /*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Jared Roesch
*/
#include "cpp_compiler.h"
#include "util/process.h"

namespace lean {
  cpp_compiler & cpp_compiler::link(std::string lib) {
      m_link.push_back(lib);
      return *this;
  }

  cpp_compiler & cpp_compiler::library_path(std::string lib_path) {
      m_library_paths.push_back(lib_path);
      return *this;
  }

  cpp_compiler & cpp_compiler::include_path(std::string include_path) {
      m_include_paths.push_back(include_path);
      return *this;
  }

  cpp_compiler & cpp_compiler::debug(bool on) {
      m_debug = on;
      return *this;
  }

  cpp_compiler & cpp_compiler::file(std::string file_path) {
      m_files.push_back(file_path);
      return *this;
  }

  cpp_compiler::cpp_compiler() : m_library_paths(), m_include_paths(), m_files(), m_link(), m_debug(false) {}

  cpp_compiler & cpp_compiler::shared_library(bool on) {
      m_shared = on;
      return *this;
  }

  cpp_compiler & cpp_compiler::pic(bool on) {
      m_pic = on;
      return * this;
  }

  void cpp_compiler::run() {
      process p("g++");
      p.arg("-std=c++11");

      if (m_pic) {
          p.arg("-fPIC");
      }

      if (m_shared) {
          p.arg("-shared");
      }

      // Add all the library paths.
      for (auto include_path : m_include_paths) {
          std::string arg("-I");
          arg += include_path;
          p.arg(arg);
      }

      // Add all the link paths.
      for (auto link_path : m_library_paths) {
          std::string arg("-L");
          arg += link_path;
          p.arg(arg);
      }

      // Add all the files
      for (auto file_path : m_files) {
          p.arg(file_path);
      }

      // Add all the link arguments.
      for (auto link: m_link) {
          std::string arg("-l");
          arg += link;
          p.arg(arg);
      }

      if (m_debug) {
          p.arg("-g");
      }

      p.run();
  }

  // Setup a compiler for building executables.
  cpp_compiler mk_executable_compiler() {
      cpp_compiler gpp;
      gpp.link(LEAN_STATIC_LIB);
      return gpp;
  }

  // Setup a compiler for building dynamic libraries.
  cpp_compiler mk_shared_compiler() {
      cpp_compiler gpp;
      gpp.link(LEAN_SHARED_LIB);
      gpp.pic(true);
      gpp.shared_library(true);
      return gpp;
  }
}
