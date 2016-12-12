/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Gabriel Ebner
*/
#pragma once
#include <utility>
#include "util/name.h"
#include "util/int64.h"

namespace lean {

typedef pair<unsigned, unsigned> pos_info; //!< Line and column information

typedef uint64 period;

struct message_bucket_id {
    message_bucket_id() {}
    message_bucket_id(name const & bucket, period version) : m_bucket(bucket), m_version(version) {}

    name m_bucket;
    period m_version = 0;
};

}
