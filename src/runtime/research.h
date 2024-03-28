#pragma once
#include "util/io.h"
#include "runtime/optional.h"



std::string getEnvVarString(const char *name);
bool research_isResearchLogVerbose();

extern "C" {
uint8_t research_isReuseAcrossConstructorsEnabled(lean_object *);
}
