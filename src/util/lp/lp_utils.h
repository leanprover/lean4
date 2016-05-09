/*
  Copyright (c) 2013 Microsoft Corporation. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.

  Author: Lev Nachmanson
  This file should be present in z3 and in Lean.
*/
#pragma once
#include <string>
#include "util/lp/numeric_pair.h"
#ifdef lp_for_z3
namespace lean {
    inline void throw_exception(const std::string & str) {
         throw default_exception(str);
    }
    typedef z3_exception exception;
#ifdef LEAN_DEBUG
    inline void lean_assert(bool b) {}
#else
    #define lean_assert(_x_) {}
 #endif
    inline void lean_unreachable() { lean_assert(false); }
    template <typename X> inline X zero_of_type() { return numeric_traits<X>::zero(); }
    template <typename X> inline X one_of_type() { return numeric_traits<X>::one(); }
    template <typename X> inline bool is_zero(const X & v) { return numeric_traits<X>::is_zero(v); }
    template <typename X> inline bool precise() { return numeric_traits<X>::precise();}
}
namespace std {
template<>
struct hash<rational> {
    inline size_t operator()(const rational & v) const {
        return v.hash();
    }
};
}

template <class T>
inline void hash_combine(std::size_t & seed, const T & v) {
    seed ^= std::hash<T>()(v) + 0x9e3779b9 + (seed << 6) + (seed >> 2);
}

namespace std {
template<typename S, typename T> struct hash<pair<S, T>> {
    inline size_t operator()(const pair<S, T> & v) const {
        size_t seed = 0;
        hash_combine(seed, v.first);
        hash_combine(seed, v.second);
        return seed;
    }
};
}
#else // else  of #if  lp_for_z3
#include <utility>
#include <functional>
#include "util/numerics/mpq.h"
#include "util/numerics/numeric_traits.h"
#include "util/numerics/double.h"
#include "util/debug.h"
#ifdef __CLANG__
#pragma clang diagnostic push
#pragma clang diagnostic ignored "-Wmismatched-tags"
#endif
namespace std {
template<>
struct hash<lean::mpq> {
    inline size_t operator()(const lean::mpq & v) const {
        return v.hash();
    }
};
}
namespace lean {
template <typename X> inline bool  precise() { return numeric_traits<X>::precise();}
template <typename X> inline X one_of_type() { return numeric_traits<X>::one(); }
template <typename X> inline bool is_zero(const X & v) { return numeric_traits<X>::is_zero(v); }
template <typename X> inline double  get_double(const X & v) { return numeric_traits<X>::get_double(v); }
template <typename T> inline T zero_of_type() {return numeric_traits<T>::zero();}
inline void throw_exception(std::string str) { throw exception(str); }
template <typename T> inline T from_string(std::string const & str) { lean_unreachable();}
template <> double inline from_string<double>(std::string const & str) { return atof(str.c_str());}
template <> mpq inline from_string<mpq>(std::string const & str) {
    return mpq(atof(str.c_str()));
}
} // closing lp
template <class T>
inline void hash_combine(std::size_t & seed, const T & v) {
    seed ^= std::hash<T>()(v) + 0x9e3779b9 + (seed << 6) + (seed >> 2);
}

namespace std {
template<typename S, typename T> struct hash<pair<S, T>> {
    inline size_t operator()(const pair<S, T> & v) const {
        size_t seed = 0;
        hash_combine(seed, v.first);
        hash_combine(seed, v.second);
        return seed;
    }
};
}
#ifdef __CLANG__
#pragma clang diagnostic pop
#endif
#endif
