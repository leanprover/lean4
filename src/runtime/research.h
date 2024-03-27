#pragma once
#include "util/io.h"
#include "runtime/optional.h"

lean::optional<std::string> getEnvVarMayExistNonemptyString(const char *name);
bool research_isResearchLogVerbose();

extern "C" {
uint8_t research_isReuseAcrossConstructorsEnabled(lean_object *);
}
