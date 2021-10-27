/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    mpn.h

Abstract:

    Multi Precision Natural Numbers

Author:

    Christoph Wintersteiger (cwinter) 2011-11-16.

Revision History:

--*/
#pragma once
#include <stddef.h>

namespace lean {
typedef unsigned int mpn_digit;

int mpn_compare(mpn_digit const * a, size_t lnga,
                mpn_digit const * b, size_t lngb);

void mpn_add(mpn_digit const * a, size_t lnga,
             mpn_digit const * b, size_t lngb,
             mpn_digit *c, size_t lngc_alloc,
             size_t * plngc);

void mpn_sub(mpn_digit const * a, size_t lnga,
             mpn_digit const * b, size_t lngb,
             mpn_digit * c, mpn_digit * pborrow);

void mpn_mul(mpn_digit const * a, size_t lnga,
             mpn_digit const * b, size_t lngb,
             mpn_digit * c);

void mpn_div(mpn_digit const * numer, size_t lnum,
             mpn_digit const * denom, size_t lden,
             mpn_digit * quot,
             mpn_digit * rem);

char * mpn_to_string(mpn_digit const * a, size_t lng,
                     char * buf, size_t lbuf);
}
