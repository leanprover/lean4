/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <string>
#include <vector>
#include <limits>
#include "util/int64.h"

namespace lean {
/** \brief The bitap algorithm (aka Baeza-Yates–Gonnet algorithm) for approximate string matching.
    Reference: http://dl.acm.org/citation.cfm?doid=135239.135244
*/
class bitap_fuzzy_search {
    static constexpr unsigned mask_size = std::numeric_limits<unsigned char>::max()+1;
    unsigned            m_pattern_size;
    uint64              m_pattern_mask[mask_size];
    unsigned            m_k;
    std::vector<uint64> m_R;
public:
    /** \brief Create a searcher for the given pattern (upto k errors).

        \pre pattern.size() < 63
    */
    bitap_fuzzy_search(std::string const & pattern, unsigned k);
    /** \brief Return the position of pattern in text with upto k "errors"
        Return std::string::npos if the pattern does not occur in text.
    */
    size_t operator()(std::string const & text);

    bool match(std::string const & text) { return operator()(text) != std::string::npos; }
};
}
