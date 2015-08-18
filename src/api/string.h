/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <string>
namespace lean {
char const * mk_string(std::string const &);
char const * mk_string(char const *);
void del_string(char const *);
}
