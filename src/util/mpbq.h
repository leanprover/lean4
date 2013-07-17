/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved. 
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura 
*/
#pragma once
#include "mpz.h"

namespace lean {

// Multiple precision binary rationals 
class mpbq {
    mpz      m_num;
    unsigned m_k;
    void normalize();
public:
    mpbq():m_k(0) {}
    mpbq(mpbq const & v):m_num(v.m_num), m_k(v.m_k) {}
    mpbq(mpbq && v);
    mpbq(mpz const & v):m_num(v), m_k(0) {}
    mpbq(int n):m_num(n), m_k(0) {}
    mpbq(int n, unsigned k):m_num(n), m_k(k) { normalize(); }
    ~mpbq() {}

    void swap(mpbq & o) { m_num.swap(o.m_num); std::swap(m_k, o.m_k); }

    unsigned hash() const { return m_num.hash(); }

    int sgn() const { return m_num.sgn(); }
    friend int sgn(mpbq const & a) { return a.sgn(); }
    bool is_pos() const { return sgn() > 0; } 
    bool is_neg() const { return sgn() < 0; }
    bool is_zero() const { return sgn() == 0; }
    bool is_nonpos() const { return !is_pos(); }
    bool is_nonneg() const { return !is_neg(); }

    void neg() { m_num.neg(); }
    friend mpbq neg(mpbq a) { a.neg(); return a; }

    void abs() { m_num.abs(); }
    friend mpbq abs(mpbq a) { a.abs(); return a; }

    mpz const & get_numerator() const { return m_num; }
    unsigned get_k() const { return m_k; }
    bool is_integer() const { return m_k == 0; }
    
    friend int cmp(mpbq const & a, mpbq const & b);
    friend int cmp(mpbq const & a, mpz const & b);
    friend int cmp(mpbq const & a, unsigned b) { return cmp(a, mpbq(b)); }
    friend int cmp(mpbq const & a, int b) { return cmp(a, mpbq(b)); }

    friend bool operator<(mpbq const & a, mpbq const & b) { return cmp(a, b) < 0; } 
    friend bool operator<(mpbq const & a, mpz const & b) { return cmp(a, b) < 0; } 
    friend bool operator<(mpbq const & a, unsigned b) { return cmp(a, b) < 0; } 
    friend bool operator<(mpbq const & a, int b) { return cmp(a, b) < 0; }     
    friend bool operator<(unsigned a, mpbq const & b) { return cmp(b, a) > 0; } 
    friend bool operator<(int a, mpbq const & b) { return cmp(b, a) > 0; }     
    friend bool operator<(mpz const & a, mpbq const & b) { return cmp(b, a) > 0; }     

    friend bool operator>(mpbq const & a, mpbq const & b) { return cmp(a, b) > 0; } 
    friend bool operator>(mpbq const & a, mpz const & b) { return cmp(a, b) > 0; } 
    friend bool operator>(mpbq const & a, unsigned b) { return cmp(a, b) > 0; } 
    friend bool operator>(mpbq const & a, int b) { return cmp(a, b) > 0; }     
    friend bool operator>(unsigned a, mpbq const & b) { return cmp(b, a) > 0; } 
    friend bool operator>(int a, mpbq const & b) { return cmp(b, a) > 0; }     
    friend bool operator>(mpz const & a, mpbq const & b) { return cmp(b, a) > 0; }     

    friend bool operator<=(mpbq const & a, mpbq const & b) { return cmp(a, b) <= 0; } 
    friend bool operator<=(mpbq const & a, mpz const & b) { return cmp(a, b) <= 0; } 
    friend bool operator<=(mpbq const & a, unsigned b) { return cmp(a, b) <= 0; } 
    friend bool operator<=(mpbq const & a, int b) { return cmp(a, b) <= 0; }     
    friend bool operator<=(unsigned a, mpbq const & b) { return cmp(b, a) > 0; } 
    friend bool operator<=(int a, mpbq const & b) { return cmp(b, a) > 0; }     
    friend bool operator<=(mpz const & a, mpbq const & b) { return cmp(b, a) > 0; }     

    friend bool operator>=(mpbq const & a, mpbq const & b) { return cmp(a, b) >= 0; } 
    friend bool operator>=(mpbq const & a, mpz const & b) { return cmp(a, b) >= 0; } 
    friend bool operator>=(mpbq const & a, unsigned b) { return cmp(a, b) >= 0; } 
    friend bool operator>=(mpbq const & a, int b) { return cmp(a, b) >= 0; }     
    friend bool operator>=(unsigned a, mpbq const & b) { return cmp(b, a) > 0; } 
    friend bool operator>=(int a, mpbq const & b) { return cmp(b, a) > 0; }     
    friend bool operator>=(mpz const & a, mpbq const & b) { return cmp(b, a) > 0; }     

    friend bool operator==(mpbq const & a, mpbq const & b) { return a.m_k == b.m_k && a.m_num == b.m_num; }
    friend bool operator==(mpbq const & a, mpz const & b) { return a.is_integer() && a.m_num == b; }
    friend bool operator==(mpbq const & a, unsigned int b) { return a.is_integer() && a.m_num == b; }
    friend bool operator==(mpbq const & a, int b) { return a.is_integer() && a.m_num == b; }
    friend bool operator==(mpz const & a, mpbq const & b) { return operator==(b, a); }
    friend bool operator==(unsigned int a, mpbq const & b) { return operator==(b, a); }
    friend bool operator==(int a, mpbq const & b) { return operator==(b, a); }

    friend bool operator!=(mpbq const & a, mpbq const & b) { return !operator==(a,b); }
    friend bool operator!=(mpbq const & a, mpz const & b) { return !operator==(a,b); }
    friend bool operator!=(mpz const & a, mpbq const & b) { return !operator==(a,b); }
    friend bool operator!=(mpbq const & a, unsigned int b) { return !operator==(a,b); }
    friend bool operator!=(mpbq const & a, int b) { return !operator==(a,b); }
    friend bool operator!=(unsigned int a, mpbq const & b) { return !operator==(a,b); }
    friend bool operator!=(int a, mpbq const & b) { return !operator==(a,b); }

    mpbq & operator+=(mpbq const & a);
    mpbq & operator+=(unsigned a);
    mpbq & operator+=(int a);

    mpbq & operator-=(mpbq const & a);
    mpbq & operator-=(unsigned a);
    mpbq & operator-=(int a);

    mpbq & operator*=(mpbq const & a);
    mpbq & operator*=(unsigned a);
    mpbq & operator*=(int a);

    friend mpbq operator+(mpbq a, mpbq const & b) { return a += b; } 
    friend mpbq operator+(mpbq a, mpz const & b) { return a += b; } 
    friend mpbq operator+(mpbq a, unsigned b)  { return a += b; }         
    friend mpbq operator+(mpbq a, int b)  { return a += b; }              
    friend mpbq operator+(mpz const & a, mpbq b) { return b += a; }
    friend mpbq operator+(unsigned a, mpbq b) { return b += a; }          
    friend mpbq operator+(int a, mpbq b) { return b += a; }               

    friend mpbq operator-(mpbq a, mpbq const & b) { return a -= b; } 
    friend mpbq operator-(mpbq a, mpz const & b) { return a -= b; } 
    friend mpbq operator-(mpbq a, unsigned b) { return a -= b; }          
    friend mpbq operator-(mpbq a, int b) { return a -= b; }               
    friend mpbq operator-(mpz const & a, mpbq b) { b.neg(); return b += a; }
    friend mpbq operator-(unsigned a, mpbq b) { b.neg(); return b += a; } 
    friend mpbq operator-(int a, mpbq b) { b.neg(); return b += a; }      

    friend mpbq operator*(mpbq a, mpbq const & b) { return a *= b; }
    friend mpbq operator*(mpbq a, mpz const & b) { return a *= b; }
    friend mpbq operator*(mpbq a, unsigned b) { return a *= b; }          
    friend mpbq operator*(mpbq a, int b) { return a *= b; }               
    friend mpbq operator*(mpz const & a, mpbq b) { return b *= a; }
    friend mpbq operator*(unsigned a, mpbq b) { return b *= a; }          
    friend mpbq operator*(int a, mpbq b) { return b *= a; }

    mpbq & operator++() { return operator+=(1); }
    mpbq operator++(int) { mpbq r(*this); ++(*this); return r; }

    mpbq & operator--() { return operator-=(1); }
    mpbq operator--(int) { mpbq r(*this); --(*this); return r; }
    
    friend std::ostream & operator<<(std::ostream & out, mpbq const & v);
};

}
