// Lean compiler output
// Module: init.env_ext
// Imports:
#include "runtime/object.h"
#include "runtime/apply.h"
#include "runtime/io.h"
#include "kernel/builtin.h"
typedef lean::object obj;
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#endif
static bool _G_initialized = false;
void initialize_init_env__ext() {
 if (_G_initialized) return;
 _G_initialized = true;
}
