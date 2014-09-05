/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include <iostream>
#include "util/exception.h"
#include "util/bitap_fuzzy_search.h"

namespace lean {
bitap_fuzzy_search::bitap_fuzzy_search(std::string const & pattern, unsigned k):
    m_R(k+1) {
    if (pattern.size() > 63)
        throw exception("pattern is too long");
    m_k            = k;
    m_pattern_size = pattern.size();
    for (unsigned i = 0; i < mask_size; i++)
        m_pattern_mask[i] = ~static_cast<uint64>(0);
    for (unsigned i = 0; i < m_pattern_size; i++) {
        unsigned u = static_cast<unsigned char>(pattern[i]);
        m_pattern_mask[u] &= ~(static_cast<uint64>(1) << i);
    }
}

size_t bitap_fuzzy_search::operator()(std::string const & text) {
    if (m_pattern_size == 0)
        return 0;
    for (unsigned i = 0; i < m_k+1; i++)
        m_R[i] = ~static_cast<uint64>(1);

    unsigned text_sz = text.size();
    for (unsigned i = 0; i < text_sz; i++) {
        uint64 old_Rd1 = m_R[0];
        unsigned u     = static_cast<unsigned char>(text[i]);
        uint64 Sc      = m_pattern_mask[u];
        m_R[0] = (m_R[0] | Sc) << 1;

        for (unsigned d = 1; d < m_k+1; d++) {
            uint64 tmp = m_R[d];
            m_R[d]     =
                // Case 1. there is a match with <= d errors upto this point, and
                // current character is matching
                ((m_R[d] | Sc) << 1) &
                // Case 2. there is a match with <= d-1 errors upto this point.
                // This case corresponds to substitution.
                (old_Rd1 << 1) &
                // Case 3. there is a match with <= d-1 errors upto this point.
                // This case corresponds to deletion.
                (m_R[d-1] << 1) &
                // Case 3. there is a match with <= d-1 errors upto this point.
                // This case corresponds to insertion.
                old_Rd1;
            old_Rd1    = tmp;
        }

        if ((m_R[m_k] & (static_cast<uint64>(1) << m_pattern_size)) == 0)
            return i - m_pattern_size + 1;
    }
    return std::string::npos;
}
}
