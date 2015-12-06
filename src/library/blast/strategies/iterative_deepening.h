/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "library/blast/strategy.h"
namespace lean {
namespace blast {
strategy iterative_deepening(strategy const & s, unsigned init, unsigned inc, unsigned max);
}}
