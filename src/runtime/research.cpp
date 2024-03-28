#include "runtime/research.h"

#include <assert.h>

#include <cstdint>
#include <cstdlib>  // For std::getenv
#include <fstream>
#include <iostream>

#include "runtime/alloc.h"
#include "runtime/exception.h"
#include "runtime/memory.h"
#include "util/io.h"
#include "runtime/optional.h"

// returns if we enable verbose logging.
bool research_isResearchLogVerbose() {
  const char *_var = std::getenv("RESEARCH_LOG_VERBOSE");
  if (!_var) {
    throw lean::throwable(
        "expected environment variable to be 'true/false' for "
        "RESEARCH_LOG_VERBOSE, but was unset");
  } else {
    std::string var(_var);
    if (var != "true" && var != "TRUE" && var != "1" && var != "false" &&
        var != "FALSE" && var != "0") {
      throw lean::throwable("expected environment variable to be 'true/false' for 'RESEARCH_LOG_VERBOSE', found '"+ var + "'");
    }
    return var == "true" || var == "TRUE" || var == "1";
  }
}

bool getEnvVarBool(const char *name) {
  const char *_var = std::getenv(name);
  if (!_var) {
    throw lean::throwable(
        std::string("expected environment variable to be 'true/false' for '") +
        name + ", but was unset");
  } else {
    std::string var(_var);
    if (var != "true" && var != "TRUE" && var != "1" && var != "false" &&
        var != "FALSE" && var != "0") {
      throw lean::throwable(
          std::string("expected environment variable to be 'true/false' for ") +
          name + ", found '" + var + "'");
    }
    const bool out = var == "true" || var == "TRUE" || var == "1";
    if (research_isResearchLogVerbose()) {
      std::cerr << "found env var " << name << " = raw(" << var
                << ") | parsed: " << out << "\n";
    }
    return out;
  }
}

// return an environment variable which must exist.
std::string getEnvVarString(const char *name) {
  const char *_var = std::getenv(name);
  if (!_var) {
      throw lean::throwable(std::string("expected environment variable to be string for '") + name + "'\n");
  } else {
    std::string(_var);
  }
}

extern "C" {
uint8_t research_isReuseAcrossConstructorsEnabled(lean_object *) {
  return getEnvVarBool("RESEARCH_IS_REUSE_ACROSS_CONSTRUCTORS_ENABLED");
}

}  // end extern "C"
   //

extern "C" {
// dump allocator info into logfile.
// TODO: rename into research_runtime_dump_allocator_log_at_end_of_run();
void research_dump_allocator_log() {
  const char *envVarName = "RESEARCH_LEAN_PROFILER_CSV_PATH";
  std::string out_path = getEnvVarString(envVarName);
  if (out_path == "") {
    return;
  }

  std::ofstream *of = NULL;
  std::ostream *o = NULL;
  if (out_path == "-") {
    o = &std::cerr;
  } else {
    of = new std::ofstream(out_path, std::ios::app);
    o = of;
  }

  assert(o);

  if (research_isResearchLogVerbose()) {
    std::cerr << "writing profiling information " << " to file '" << out_path << "'" << "\n";
  }

  (*o << "rss, " << lean::get_peak_rss()) << "\n";
  (*o << "num_alloc, " << lean::allocator::get_num_alloc()) << "\n";
  (*o << "num_small_alloc, " << lean::allocator::get_num_small_alloc()) << "\n";
  (*o << "num_dealloc, " << lean::allocator::get_num_dealloc()) << "\n";
  (*o << "num_small_dealloc, " << lean::allocator::get_num_small_dealloc())
      << "\n";
  (*o << "num_segments, " << lean::allocator::get_num_segments()) << "\n";
  (*o << "num_pages, " << lean::allocator::get_num_pages()) << "\n";
  (*o << "num_exports, " << lean::allocator::get_num_exports()) << "\n";
  (*o << "num_recycled_pages, " << lean::allocator::get_num_recycled_pages())
      << "\n";
  if (of) {
    delete of;
  }
}
}  // end extern C
