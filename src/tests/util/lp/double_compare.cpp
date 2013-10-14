/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Lev Nachmanson
*/

// This file is needed for testing. It can be called with two or three
// strings represinting double numbers. If the absolute value of the
// difference between the first two numbers is less than the third
// one, then 0 is returned. Otherwise 1 is returned. If the number of
// arguments is two and the numbers are small then 0 returned.  If the
// numbers are not too small then 0 returned when the absolute value
// of their difference is smaller than one percent of their maximal
// abs value. If the number parameters is not 2 or 3, or the arguments
// cannot be converted to doubles then -1 is returned


#include <iostream>
using namespace std;
#include <stdlib.h>
#include <math.h>

int main(int argn, char * const * argv) {
    if (argn != 4 && argn != 3) {
        cout << "Usage is \"n1 n2 [n3]" << endl;
        return 2;
    }

    double a = atof(argv[1]);
    double b = atof(argv[2]);
    if (argn == 4) {
        double c = atof(argv[3]);
        if (fabs(a - b) < c) {
            return 0;
        }
        return 1;
    }

    // argn == 3
    double maxval = max(fabs(a), fabs(b));
    if (maxval < 0.000001) {
        return 0;
    }

    double one_percent = maxval / 100;
    if (fabs(a - b) > one_percent) {
        return 1;
    }
    return 0;
}
