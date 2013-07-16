/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved. 
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura 
*/
#pragma once

// Macros for defining numeral classes
#define DEFINE_ORDER_OPS(T)                                             \
friend bool operator==(T const & a, T const & b) { return cmp(a, b) == 0; } \
friend bool operator!=(T const & a, T const & b) { return cmp(a, b) != 0; } \
friend bool operator<(T const & a, T const & b) { return cmp(a, b) < 0; } \
friend bool operator>(T const & a, T const & b) { return cmp(a, b) > 0; } \
friend bool operator<=(T const & a, T const & b) { return cmp(a, b) <= 0; } \
friend bool operator>=(T const & a, T const & b) { return cmp(a, b) >= 0; } \
friend bool operator==(T const & a, unsigned b) { return cmp(a, b) == 0; } \
friend bool operator!=(T const & a, unsigned b) { return cmp(a, b) != 0; } \
friend bool operator<(T const & a, unsigned b) { return cmp(a, b) < 0; } \
friend bool operator>(T const & a, unsigned b) { return cmp(a, b) > 0; } \
friend bool operator<=(T const & a, unsigned b) { return cmp(a, b) <= 0; } \
friend bool operator>=(T const & a, unsigned b) { return cmp(a, b) >= 0; } \
friend bool operator==(T const & a, int b) { return cmp(a, b) == 0; }   \
friend bool operator!=(T const & a, int b) { return cmp(a, b) != 0; }   \
friend bool operator<(T const & a, int b) { return cmp(a, b) < 0; }     \
friend bool operator>(T const & a, int b) { return cmp(a, b) > 0; }     \
friend bool operator<=(T const & a, int b) { return cmp(a, b) <= 0; }   \
friend bool operator>=(T const & a, int b) { return cmp(a, b) >= 0; }   \
friend bool operator==(unsigned a, T const & b) { return cmp(b, a) == 0; } \
friend bool operator!=(unsigned a, T const & b) { return cmp(b, a) != 0; } \
friend bool operator<(unsigned a, T const & b) { return cmp(b, a) > 0; } \
friend bool operator>(unsigned a, T const & b) { return cmp(b, a) < 0; } \
friend bool operator<=(unsigned a, T const & b) { return cmp(b, a) >= 0; } \
friend bool operator>=(unsigned a, T const & b) { return cmp(b, a) <= 0; } \
friend bool operator==(int a, T const & b) { return cmp(b, a) == 0; }   \
friend bool operator!=(int a, T const & b) { return cmp(b, a) != 0; }   \
friend bool operator<(int a, T const & b) { return cmp(b, a) > 0; }     \
friend bool operator>(int a, T const & b) { return cmp(b, a) < 0; }     \
friend bool operator<=(int a, T const & b) { return cmp(b, a) >= 0; }   \
friend bool operator>=(int a, T const & b) { return cmp(b, a) <= 0; } 


#define DEFINE_SIGN_METHODS()                   \
bool is_pos() const { return sgn() > 0; }       \
bool is_neg() const { return sgn() < 0; }       \
bool is_zero() const { return sgn() == 0; }     \
bool is_nonpos() const { return !is_pos(); }    \
bool is_nonneg() const { return !is_neg(); }

#define DEFINE_ARITH_OPS(T)                                             \
friend T operator+(T a, T const & b) { return a += b; }                 \
friend T operator-(T a, T const & b) { return a -= b; }                 \
friend T operator*(T a, T const & b) { return a *= b; }                 \
friend T operator/(T a, T const & b) { return a /= b; }                 \
friend T operator+(T a, unsigned b)  { return a += b; }                 \
friend T operator-(T a, unsigned b) { return a -= b; }                  \
friend T operator*(T a, unsigned b) { return a *= b; }                  \
friend T operator/(T a, unsigned b) { return a /= b; }                  \
friend T operator+(T a, int b)  { return a += b; }                      \
friend T operator-(T a, int b) { return a -= b; }                       \
friend T operator*(T a, int b) { return a *= b; }                       \
friend T operator/(T a, int b) { return a /= b; }                       \
friend T operator+(unsigned a, T b) { return b += a; }                  \
friend T operator-(unsigned a, T b) { b.neg(); return b += a; }         \
friend T operator*(unsigned a, T b) { return b *= a; }                  \
friend T operator/(unsigned a, T const & b) { T r(a); return r /= b; }  \
friend T operator+(int a, T b) { return b += a; }                       \
friend T operator-(int a, T b) { b.neg(); return b += a; }              \
friend T operator*(int a, T b) { return b *= a; }                       \
friend T operator/(int a, T const & b) { T r(a); return r /= b; }
