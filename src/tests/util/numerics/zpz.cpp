/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <iostream>
#include <sstream>
#include "util/test.h"
#include "util/numerics/zpz.h"
using namespace lean;

static void tst1() {
    zpz z(1, 7);
    lean_assert(z.p() == 7);
    lean_assert(z.get_unsigned_int() == 1);
    lean_assert(z.hash() == 1);
    z += 2;
    lean_assert(z == 3);
    z -= 1;
    lean_assert(z == zpz(2, 7));
    z -= zpz(3, 7);
    lean_assert(z == 6);
    z.neg();
    lean_assert(z == 1);
    z += zpz(1, 7);
    z *= zpz(2, 7);
    lean_assert(z == 4);
    z *= 2;
    lean_assert(z == 1);
    z.inv();
    lean_assert(z == 1);
    z /= 3;
    lean_assert(z == 5);
    z /= zpz(2, 7);
    lean_assert(z == 6);
    z.neg();
    lean_assert(z == 1);
    z++;
    lean_assert(z == 2);
    z--;
    --z;
    z--;
    lean_assert(z == 6);
    ++z;
    lean_assert(z == 0);
    z = 4;
    lean_assert(z == 4);
    z.set_p(3);
    lean_assert(z == 1);
    lean_assert(z.p() == 3);
    z.set_p(7);
    lean_assert(z.p() == 7);
    zpz w(3, 13);
    swap(z, w);
    lean_assert(z == 3 && z.p() == 13);
    lean_assert(w == 1 && w.p() == 7);
    w = z;
    lean_assert(w == 3 && w.p() == 13);
    lean_assert(zpz(3, 7) == zpz(3, 13));
    lean_assert(zpz(3, 7) != zpz(4, 7));
    lean_assert(zpz(3, 7) < zpz(5, 13));
    lean_assert(zpz(5, 7) > zpz(3, 13));
    lean_assert(zpz(5, 7) >= zpz(3, 13));
    lean_assert(zpz(5, 7) >= zpz(5, 13));
    lean_assert(zpz(3, 7) < zpz(5, 13));
    lean_assert(zpz(3, 7) <= zpz(5, 13));
    lean_assert(zpz(5, 7) <= zpz(5, 13));

    lean_assert(zpz(3, 7) == 3);
    lean_assert(zpz(3, 7) != 4);
    lean_assert(zpz(3, 7) < 5);
    lean_assert(zpz(5, 7) > 3);
    lean_assert(zpz(5, 7) >= 3);
    lean_assert(zpz(5, 7) >= 5);
    lean_assert(zpz(3, 7) < 5);
    lean_assert(zpz(3, 7) <= 5);
    lean_assert(zpz(5, 7) <= 5);

    lean_assert(3 == zpz(3, 13));
    lean_assert(3 != zpz(4, 7));
    lean_assert(3 < zpz(5, 13));
    lean_assert(5 > zpz(3, 13));
    lean_assert(5 >= zpz(3, 13));
    lean_assert(5 >= zpz(5, 13));
    lean_assert(3 < zpz(5, 13));
    lean_assert(3 <= zpz(5, 13));
    lean_assert(5 <= zpz(5, 13));

    lean_assert(zpz(1, 7) + zpz(4, 7) == 5);
    lean_assert(zpz(1, 7) - zpz(3, 7) == 5);
    lean_assert(zpz(2, 7) * zpz(3, 7) == 6);
    lean_assert(zpz(2, 7) * zpz(4, 7) == 1);
    lean_assert(zpz(1, 7) / zpz(3, 7) == 5);

    lean_assert(zpz(1, 7) + 4 == 5);
    lean_assert(zpz(1, 7) - 3 == 5);
    lean_assert(zpz(2, 7) * 3 == 6);
    lean_assert(zpz(2, 7) * 4 == 1);
    lean_assert(zpz(1, 7) / 3 == 5);

    lean_assert(1 + zpz(4, 7) == 5);
    lean_assert(1 - zpz(3, 7) == 5);
    lean_assert(2 * zpz(3, 7) == 6);
    lean_assert(2 * zpz(4, 7) == 1);
    lean_assert(1 / zpz(3, 7) == 5);
    std::ostringstream out;
    z = 3;
    out << z;
    lean_assert(out.str() == "3");
}

int main() {
    tst1();
    return has_violations() ? 1 : 0;
}
