/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Gabriel Ebner
*/
#include <string>
#include "library/messages.h"

namespace lean {

message::message(parser_exception const & ex) :
        message(ex.get_file_name(), *ex.get_pos(),
                ERROR, ex.get_msg()) {}

}
