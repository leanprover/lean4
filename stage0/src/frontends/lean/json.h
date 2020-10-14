/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Gabriel Ebner
*/
#ifdef LEAN_JSON
#pragma once
#include "library/messages.h"
#include "kernel/environment.h"
#include "util/json.hpp"

namespace lean {

using json = nlohmann::json;

json json_of_severity(message_severity sev);

json json_of_message(message const & msg);

void print_json(std::ostream &, message const & msg);

}
#endif
