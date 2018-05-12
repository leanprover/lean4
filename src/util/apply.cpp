
/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
// DO NOT EDIT, this is an automatically generated file
// Generated using script: ../../gen/apply.lean
#include "util/apply.h"
namespace lean {
#define obj lean_obj
#define fx(i) closure_arg_cptr(f)[i]

static obj* fix_args(obj* f, unsigned n, obj*const* as) {
    unsigned arity = closure_arity(f);
    unsigned fixed = closure_num_fixed(f);
    unsigned new_fixed = fixed + n;
    lean_assert(new_fixed < arity);
    obj * r = alloc_closure(closure_fun(f), arity, new_fixed);
    obj ** source = closure_arg_cptr(f);
    obj ** target = closure_arg_cptr(r);
    for (unsigned i = 0; i < fixed; i++, source++, target++) {
        *target = *source;
        if (!is_scalar(*target)) inc_ref(*target);
    }
    for (unsigned i = 0; i < n; i++, as++, target++) {
        *target = *as;
        if (!is_scalar(*target)) inc_ref(*target);
    }
    inc_ref(r);
    return r;
}

static inline obj* fix_args(obj* f, std::initializer_list<obj*> const & l) {
    return fix_args(f, l.size(), l.begin());
}
typedef obj* (*fn1)(obj*); // NOLINT
#define FN1(f) reinterpret_cast<fn1>(closure_fun(f))
typedef obj* (*fn2)(obj*, obj*); // NOLINT
#define FN2(f) reinterpret_cast<fn2>(closure_fun(f))
typedef obj* (*fn3)(obj*, obj*, obj*); // NOLINT
#define FN3(f) reinterpret_cast<fn3>(closure_fun(f))
typedef obj* (*fn4)(obj*, obj*, obj*, obj*); // NOLINT
#define FN4(f) reinterpret_cast<fn4>(closure_fun(f))
typedef obj* (*fn5)(obj*, obj*, obj*, obj*, obj*); // NOLINT
#define FN5(f) reinterpret_cast<fn5>(closure_fun(f))
typedef obj* (*fn6)(obj*, obj*, obj*, obj*, obj*, obj*); // NOLINT
#define FN6(f) reinterpret_cast<fn6>(closure_fun(f))
typedef obj* (*fn7)(obj*, obj*, obj*, obj*, obj*, obj*, obj*); // NOLINT
#define FN7(f) reinterpret_cast<fn7>(closure_fun(f))
typedef obj* (*fn8)(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*); // NOLINT
#define FN8(f) reinterpret_cast<fn8>(closure_fun(f))
typedef obj* (*fn9)(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*); // NOLINT
#define FN9(f) reinterpret_cast<fn9>(closure_fun(f))
typedef obj* (*fn10)(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*); // NOLINT
#define FN10(f) reinterpret_cast<fn10>(closure_fun(f))
typedef obj* (*fn11)(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*); // NOLINT
#define FN11(f) reinterpret_cast<fn11>(closure_fun(f))
typedef obj* (*fn12)(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*); // NOLINT
#define FN12(f) reinterpret_cast<fn12>(closure_fun(f))
typedef obj* (*fn13)(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*); // NOLINT
#define FN13(f) reinterpret_cast<fn13>(closure_fun(f))
typedef obj* (*fn14)(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*); // NOLINT
#define FN14(f) reinterpret_cast<fn14>(closure_fun(f))
typedef obj* (*fn15)(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*); // NOLINT
#define FN15(f) reinterpret_cast<fn15>(closure_fun(f))
typedef obj* (*fn16)(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*); // NOLINT
#define FN16(f) reinterpret_cast<fn16>(closure_fun(f))
typedef obj* (*fnn)(obj**); // NOLINT
#define FNN(f) reinterpret_cast<fnn>(closure_fun(f))
static obj* curry(obj* f, unsigned n, obj** as) {
switch (n) {
case 0: lean_unreachable();
case 1: return FN1(f)(as[0]);
case 2: return FN2(f)(as[0], as[1]);
case 3: return FN3(f)(as[0], as[1], as[2]);
case 4: return FN4(f)(as[0], as[1], as[2], as[3]);
case 5: return FN5(f)(as[0], as[1], as[2], as[3], as[4]);
case 6: return FN6(f)(as[0], as[1], as[2], as[3], as[4], as[5]);
case 7: return FN7(f)(as[0], as[1], as[2], as[3], as[4], as[5], as[6]);
case 8: return FN8(f)(as[0], as[1], as[2], as[3], as[4], as[5], as[6], as[7]);
case 9: return FN9(f)(as[0], as[1], as[2], as[3], as[4], as[5], as[6], as[7], as[8]);
case 10: return FN10(f)(as[0], as[1], as[2], as[3], as[4], as[5], as[6], as[7], as[8], as[9]);
case 11: return FN11(f)(as[0], as[1], as[2], as[3], as[4], as[5], as[6], as[7], as[8], as[9], as[10]);
case 12: return FN12(f)(as[0], as[1], as[2], as[3], as[4], as[5], as[6], as[7], as[8], as[9], as[10], as[11]);
case 13: return FN13(f)(as[0], as[1], as[2], as[3], as[4], as[5], as[6], as[7], as[8], as[9], as[10], as[11], as[12]);
case 14: return FN14(f)(as[0], as[1], as[2], as[3], as[4], as[5], as[6], as[7], as[8], as[9], as[10], as[11], as[12], as[13]);
case 15: return FN15(f)(as[0], as[1], as[2], as[3], as[4], as[5], as[6], as[7], as[8], as[9], as[10], as[11], as[12], as[13], as[14]);
case 16: return FN16(f)(as[0], as[1], as[2], as[3], as[4], as[5], as[6], as[7], as[8], as[9], as[10], as[11], as[12], as[13], as[14], as[15]);
default: return FNN(f)(as);
}
}
obj* apply_n(obj*, unsigned, obj**);
static inline obj* apply_nc(obj* f, unsigned n, obj** as) { obj* r = apply_n(f, n, as); dec_ref_core(f); return r; }
obj* apply_1(obj* f, obj* a1) {
unsigned arity = closure_arity(f);
unsigned fixed = closure_num_fixed(f);
if (arity == fixed + 1) {
  switch (arity) {
  case 1: return FN1(f)(a1);
  case 2: return FN2(f)(fx(0), a1);
  case 3: return FN3(f)(fx(0), fx(1), a1);
  case 4: return FN4(f)(fx(0), fx(1), fx(2), a1);
  case 5: return FN5(f)(fx(0), fx(1), fx(2), fx(3), a1);
  case 6: return FN6(f)(fx(0), fx(1), fx(2), fx(3), fx(4), a1);
  case 7: return FN7(f)(fx(0), fx(1), fx(2), fx(3), fx(4), fx(5), a1);
  case 8: return FN8(f)(fx(0), fx(1), fx(2), fx(3), fx(4), fx(5), fx(6), a1);
  case 9: return FN9(f)(fx(0), fx(1), fx(2), fx(3), fx(4), fx(5), fx(6), fx(7), a1);
  case 10: return FN10(f)(fx(0), fx(1), fx(2), fx(3), fx(4), fx(5), fx(6), fx(7), fx(8), a1);
  case 11: return FN11(f)(fx(0), fx(1), fx(2), fx(3), fx(4), fx(5), fx(6), fx(7), fx(8), fx(9), a1);
  case 12: return FN12(f)(fx(0), fx(1), fx(2), fx(3), fx(4), fx(5), fx(6), fx(7), fx(8), fx(9), fx(10), a1);
  case 13: return FN13(f)(fx(0), fx(1), fx(2), fx(3), fx(4), fx(5), fx(6), fx(7), fx(8), fx(9), fx(10), fx(11), a1);
  case 14: return FN14(f)(fx(0), fx(1), fx(2), fx(3), fx(4), fx(5), fx(6), fx(7), fx(8), fx(9), fx(10), fx(11), fx(12), a1);
  case 15: return FN15(f)(fx(0), fx(1), fx(2), fx(3), fx(4), fx(5), fx(6), fx(7), fx(8), fx(9), fx(10), fx(11), fx(12), fx(13), a1);
  case 16: return FN16(f)(fx(0), fx(1), fx(2), fx(3), fx(4), fx(5), fx(6), fx(7), fx(8), fx(9), fx(10), fx(11), fx(12), fx(13), fx(14), a1);
  default:
    lean_assert(arity > 16);
    fx(arity-1) = a1;
    return FNN(f)(closure_arg_cptr(f));
  }
} else if (arity < fixed + 1) {
  lean_assert(fixed < arity);
  lean_unreachable();
} else {
  return fix_args(f, {a1});
}
}
obj* apply_2(obj* f, obj* a1, obj* a2) {
unsigned arity = closure_arity(f);
unsigned fixed = closure_num_fixed(f);
if (arity == fixed + 2) {
  switch (arity) {
  case 2: return FN2(f)(a1, a2);
  case 3: return FN3(f)(fx(0), a1, a2);
  case 4: return FN4(f)(fx(0), fx(1), a1, a2);
  case 5: return FN5(f)(fx(0), fx(1), fx(2), a1, a2);
  case 6: return FN6(f)(fx(0), fx(1), fx(2), fx(3), a1, a2);
  case 7: return FN7(f)(fx(0), fx(1), fx(2), fx(3), fx(4), a1, a2);
  case 8: return FN8(f)(fx(0), fx(1), fx(2), fx(3), fx(4), fx(5), a1, a2);
  case 9: return FN9(f)(fx(0), fx(1), fx(2), fx(3), fx(4), fx(5), fx(6), a1, a2);
  case 10: return FN10(f)(fx(0), fx(1), fx(2), fx(3), fx(4), fx(5), fx(6), fx(7), a1, a2);
  case 11: return FN11(f)(fx(0), fx(1), fx(2), fx(3), fx(4), fx(5), fx(6), fx(7), fx(8), a1, a2);
  case 12: return FN12(f)(fx(0), fx(1), fx(2), fx(3), fx(4), fx(5), fx(6), fx(7), fx(8), fx(9), a1, a2);
  case 13: return FN13(f)(fx(0), fx(1), fx(2), fx(3), fx(4), fx(5), fx(6), fx(7), fx(8), fx(9), fx(10), a1, a2);
  case 14: return FN14(f)(fx(0), fx(1), fx(2), fx(3), fx(4), fx(5), fx(6), fx(7), fx(8), fx(9), fx(10), fx(11), a1, a2);
  case 15: return FN15(f)(fx(0), fx(1), fx(2), fx(3), fx(4), fx(5), fx(6), fx(7), fx(8), fx(9), fx(10), fx(11), fx(12), a1, a2);
  case 16: return FN16(f)(fx(0), fx(1), fx(2), fx(3), fx(4), fx(5), fx(6), fx(7), fx(8), fx(9), fx(10), fx(11), fx(12), fx(13), a1, a2);
  default:
    lean_assert(arity > 16);
    fx(arity-2) = a1;
    fx(arity-1) = a2;
    return FNN(f)(closure_arg_cptr(f));
  }
} else if (arity < fixed + 2) {
  obj * as[2] = { a1, a2 };
  if (arity > 16) {
    for (unsigned i = 0; i < arity-fixed; i++) fx(fixed+i) = as[i];
    return apply_nc(FNN(f)(closure_arg_cptr(f)), 2+fixed-arity, as+arity-fixed);
  } else {
    obj* args[16];
    for (unsigned i = 0; i < fixed; i++) args[i] = fx(i);
    for (unsigned i = 0; i < arity-fixed; i++) args[fixed+i] = as[i];
    return apply_nc(curry(f, arity, args), 2+fixed-arity, as+arity-fixed);
  }
} else {
  return fix_args(f, {a1, a2});
}
}
obj* apply_3(obj* f, obj* a1, obj* a2, obj* a3) {
unsigned arity = closure_arity(f);
unsigned fixed = closure_num_fixed(f);
if (arity == fixed + 3) {
  switch (arity) {
  case 3: return FN3(f)(a1, a2, a3);
  case 4: return FN4(f)(fx(0), a1, a2, a3);
  case 5: return FN5(f)(fx(0), fx(1), a1, a2, a3);
  case 6: return FN6(f)(fx(0), fx(1), fx(2), a1, a2, a3);
  case 7: return FN7(f)(fx(0), fx(1), fx(2), fx(3), a1, a2, a3);
  case 8: return FN8(f)(fx(0), fx(1), fx(2), fx(3), fx(4), a1, a2, a3);
  case 9: return FN9(f)(fx(0), fx(1), fx(2), fx(3), fx(4), fx(5), a1, a2, a3);
  case 10: return FN10(f)(fx(0), fx(1), fx(2), fx(3), fx(4), fx(5), fx(6), a1, a2, a3);
  case 11: return FN11(f)(fx(0), fx(1), fx(2), fx(3), fx(4), fx(5), fx(6), fx(7), a1, a2, a3);
  case 12: return FN12(f)(fx(0), fx(1), fx(2), fx(3), fx(4), fx(5), fx(6), fx(7), fx(8), a1, a2, a3);
  case 13: return FN13(f)(fx(0), fx(1), fx(2), fx(3), fx(4), fx(5), fx(6), fx(7), fx(8), fx(9), a1, a2, a3);
  case 14: return FN14(f)(fx(0), fx(1), fx(2), fx(3), fx(4), fx(5), fx(6), fx(7), fx(8), fx(9), fx(10), a1, a2, a3);
  case 15: return FN15(f)(fx(0), fx(1), fx(2), fx(3), fx(4), fx(5), fx(6), fx(7), fx(8), fx(9), fx(10), fx(11), a1, a2, a3);
  case 16: return FN16(f)(fx(0), fx(1), fx(2), fx(3), fx(4), fx(5), fx(6), fx(7), fx(8), fx(9), fx(10), fx(11), fx(12), a1, a2, a3);
  default:
    lean_assert(arity > 16);
    fx(arity-3) = a1;
    fx(arity-2) = a2;
    fx(arity-1) = a3;
    return FNN(f)(closure_arg_cptr(f));
  }
} else if (arity < fixed + 3) {
  obj * as[3] = { a1, a2, a3 };
  if (arity > 16) {
    for (unsigned i = 0; i < arity-fixed; i++) fx(fixed+i) = as[i];
    return apply_nc(FNN(f)(closure_arg_cptr(f)), 3+fixed-arity, as+arity-fixed);
  } else {
    obj* args[16];
    for (unsigned i = 0; i < fixed; i++) args[i] = fx(i);
    for (unsigned i = 0; i < arity-fixed; i++) args[fixed+i] = as[i];
    return apply_nc(curry(f, arity, args), 3+fixed-arity, as+arity-fixed);
  }
} else {
  return fix_args(f, {a1, a2, a3});
}
}
obj* apply_4(obj* f, obj* a1, obj* a2, obj* a3, obj* a4) {
unsigned arity = closure_arity(f);
unsigned fixed = closure_num_fixed(f);
if (arity == fixed + 4) {
  switch (arity) {
  case 4: return FN4(f)(a1, a2, a3, a4);
  case 5: return FN5(f)(fx(0), a1, a2, a3, a4);
  case 6: return FN6(f)(fx(0), fx(1), a1, a2, a3, a4);
  case 7: return FN7(f)(fx(0), fx(1), fx(2), a1, a2, a3, a4);
  case 8: return FN8(f)(fx(0), fx(1), fx(2), fx(3), a1, a2, a3, a4);
  case 9: return FN9(f)(fx(0), fx(1), fx(2), fx(3), fx(4), a1, a2, a3, a4);
  case 10: return FN10(f)(fx(0), fx(1), fx(2), fx(3), fx(4), fx(5), a1, a2, a3, a4);
  case 11: return FN11(f)(fx(0), fx(1), fx(2), fx(3), fx(4), fx(5), fx(6), a1, a2, a3, a4);
  case 12: return FN12(f)(fx(0), fx(1), fx(2), fx(3), fx(4), fx(5), fx(6), fx(7), a1, a2, a3, a4);
  case 13: return FN13(f)(fx(0), fx(1), fx(2), fx(3), fx(4), fx(5), fx(6), fx(7), fx(8), a1, a2, a3, a4);
  case 14: return FN14(f)(fx(0), fx(1), fx(2), fx(3), fx(4), fx(5), fx(6), fx(7), fx(8), fx(9), a1, a2, a3, a4);
  case 15: return FN15(f)(fx(0), fx(1), fx(2), fx(3), fx(4), fx(5), fx(6), fx(7), fx(8), fx(9), fx(10), a1, a2, a3, a4);
  case 16: return FN16(f)(fx(0), fx(1), fx(2), fx(3), fx(4), fx(5), fx(6), fx(7), fx(8), fx(9), fx(10), fx(11), a1, a2, a3, a4);
  default:
    lean_assert(arity > 16);
    fx(arity-4) = a1;
    fx(arity-3) = a2;
    fx(arity-2) = a3;
    fx(arity-1) = a4;
    return FNN(f)(closure_arg_cptr(f));
  }
} else if (arity < fixed + 4) {
  obj * as[4] = { a1, a2, a3, a4 };
  if (arity > 16) {
    for (unsigned i = 0; i < arity-fixed; i++) fx(fixed+i) = as[i];
    return apply_nc(FNN(f)(closure_arg_cptr(f)), 4+fixed-arity, as+arity-fixed);
  } else {
    obj* args[16];
    for (unsigned i = 0; i < fixed; i++) args[i] = fx(i);
    for (unsigned i = 0; i < arity-fixed; i++) args[fixed+i] = as[i];
    return apply_nc(curry(f, arity, args), 4+fixed-arity, as+arity-fixed);
  }
} else {
  return fix_args(f, {a1, a2, a3, a4});
}
}
obj* apply_5(obj* f, obj* a1, obj* a2, obj* a3, obj* a4, obj* a5) {
unsigned arity = closure_arity(f);
unsigned fixed = closure_num_fixed(f);
if (arity == fixed + 5) {
  switch (arity) {
  case 5: return FN5(f)(a1, a2, a3, a4, a5);
  case 6: return FN6(f)(fx(0), a1, a2, a3, a4, a5);
  case 7: return FN7(f)(fx(0), fx(1), a1, a2, a3, a4, a5);
  case 8: return FN8(f)(fx(0), fx(1), fx(2), a1, a2, a3, a4, a5);
  case 9: return FN9(f)(fx(0), fx(1), fx(2), fx(3), a1, a2, a3, a4, a5);
  case 10: return FN10(f)(fx(0), fx(1), fx(2), fx(3), fx(4), a1, a2, a3, a4, a5);
  case 11: return FN11(f)(fx(0), fx(1), fx(2), fx(3), fx(4), fx(5), a1, a2, a3, a4, a5);
  case 12: return FN12(f)(fx(0), fx(1), fx(2), fx(3), fx(4), fx(5), fx(6), a1, a2, a3, a4, a5);
  case 13: return FN13(f)(fx(0), fx(1), fx(2), fx(3), fx(4), fx(5), fx(6), fx(7), a1, a2, a3, a4, a5);
  case 14: return FN14(f)(fx(0), fx(1), fx(2), fx(3), fx(4), fx(5), fx(6), fx(7), fx(8), a1, a2, a3, a4, a5);
  case 15: return FN15(f)(fx(0), fx(1), fx(2), fx(3), fx(4), fx(5), fx(6), fx(7), fx(8), fx(9), a1, a2, a3, a4, a5);
  case 16: return FN16(f)(fx(0), fx(1), fx(2), fx(3), fx(4), fx(5), fx(6), fx(7), fx(8), fx(9), fx(10), a1, a2, a3, a4, a5);
  default:
    lean_assert(arity > 16);
    fx(arity-5) = a1;
    fx(arity-4) = a2;
    fx(arity-3) = a3;
    fx(arity-2) = a4;
    fx(arity-1) = a5;
    return FNN(f)(closure_arg_cptr(f));
  }
} else if (arity < fixed + 5) {
  obj * as[5] = { a1, a2, a3, a4, a5 };
  if (arity > 16) {
    for (unsigned i = 0; i < arity-fixed; i++) fx(fixed+i) = as[i];
    return apply_nc(FNN(f)(closure_arg_cptr(f)), 5+fixed-arity, as+arity-fixed);
  } else {
    obj* args[16];
    for (unsigned i = 0; i < fixed; i++) args[i] = fx(i);
    for (unsigned i = 0; i < arity-fixed; i++) args[fixed+i] = as[i];
    return apply_nc(curry(f, arity, args), 5+fixed-arity, as+arity-fixed);
  }
} else {
  return fix_args(f, {a1, a2, a3, a4, a5});
}
}
obj* apply_6(obj* f, obj* a1, obj* a2, obj* a3, obj* a4, obj* a5, obj* a6) {
unsigned arity = closure_arity(f);
unsigned fixed = closure_num_fixed(f);
if (arity == fixed + 6) {
  switch (arity) {
  case 6: return FN6(f)(a1, a2, a3, a4, a5, a6);
  case 7: return FN7(f)(fx(0), a1, a2, a3, a4, a5, a6);
  case 8: return FN8(f)(fx(0), fx(1), a1, a2, a3, a4, a5, a6);
  case 9: return FN9(f)(fx(0), fx(1), fx(2), a1, a2, a3, a4, a5, a6);
  case 10: return FN10(f)(fx(0), fx(1), fx(2), fx(3), a1, a2, a3, a4, a5, a6);
  case 11: return FN11(f)(fx(0), fx(1), fx(2), fx(3), fx(4), a1, a2, a3, a4, a5, a6);
  case 12: return FN12(f)(fx(0), fx(1), fx(2), fx(3), fx(4), fx(5), a1, a2, a3, a4, a5, a6);
  case 13: return FN13(f)(fx(0), fx(1), fx(2), fx(3), fx(4), fx(5), fx(6), a1, a2, a3, a4, a5, a6);
  case 14: return FN14(f)(fx(0), fx(1), fx(2), fx(3), fx(4), fx(5), fx(6), fx(7), a1, a2, a3, a4, a5, a6);
  case 15: return FN15(f)(fx(0), fx(1), fx(2), fx(3), fx(4), fx(5), fx(6), fx(7), fx(8), a1, a2, a3, a4, a5, a6);
  case 16: return FN16(f)(fx(0), fx(1), fx(2), fx(3), fx(4), fx(5), fx(6), fx(7), fx(8), fx(9), a1, a2, a3, a4, a5, a6);
  default:
    lean_assert(arity > 16);
    fx(arity-6) = a1;
    fx(arity-5) = a2;
    fx(arity-4) = a3;
    fx(arity-3) = a4;
    fx(arity-2) = a5;
    fx(arity-1) = a6;
    return FNN(f)(closure_arg_cptr(f));
  }
} else if (arity < fixed + 6) {
  obj * as[6] = { a1, a2, a3, a4, a5, a6 };
  if (arity > 16) {
    for (unsigned i = 0; i < arity-fixed; i++) fx(fixed+i) = as[i];
    return apply_nc(FNN(f)(closure_arg_cptr(f)), 6+fixed-arity, as+arity-fixed);
  } else {
    obj* args[16];
    for (unsigned i = 0; i < fixed; i++) args[i] = fx(i);
    for (unsigned i = 0; i < arity-fixed; i++) args[fixed+i] = as[i];
    return apply_nc(curry(f, arity, args), 6+fixed-arity, as+arity-fixed);
  }
} else {
  return fix_args(f, {a1, a2, a3, a4, a5, a6});
}
}
obj* apply_7(obj* f, obj* a1, obj* a2, obj* a3, obj* a4, obj* a5, obj* a6, obj* a7) {
unsigned arity = closure_arity(f);
unsigned fixed = closure_num_fixed(f);
if (arity == fixed + 7) {
  switch (arity) {
  case 7: return FN7(f)(a1, a2, a3, a4, a5, a6, a7);
  case 8: return FN8(f)(fx(0), a1, a2, a3, a4, a5, a6, a7);
  case 9: return FN9(f)(fx(0), fx(1), a1, a2, a3, a4, a5, a6, a7);
  case 10: return FN10(f)(fx(0), fx(1), fx(2), a1, a2, a3, a4, a5, a6, a7);
  case 11: return FN11(f)(fx(0), fx(1), fx(2), fx(3), a1, a2, a3, a4, a5, a6, a7);
  case 12: return FN12(f)(fx(0), fx(1), fx(2), fx(3), fx(4), a1, a2, a3, a4, a5, a6, a7);
  case 13: return FN13(f)(fx(0), fx(1), fx(2), fx(3), fx(4), fx(5), a1, a2, a3, a4, a5, a6, a7);
  case 14: return FN14(f)(fx(0), fx(1), fx(2), fx(3), fx(4), fx(5), fx(6), a1, a2, a3, a4, a5, a6, a7);
  case 15: return FN15(f)(fx(0), fx(1), fx(2), fx(3), fx(4), fx(5), fx(6), fx(7), a1, a2, a3, a4, a5, a6, a7);
  case 16: return FN16(f)(fx(0), fx(1), fx(2), fx(3), fx(4), fx(5), fx(6), fx(7), fx(8), a1, a2, a3, a4, a5, a6, a7);
  default:
    lean_assert(arity > 16);
    fx(arity-7) = a1;
    fx(arity-6) = a2;
    fx(arity-5) = a3;
    fx(arity-4) = a4;
    fx(arity-3) = a5;
    fx(arity-2) = a6;
    fx(arity-1) = a7;
    return FNN(f)(closure_arg_cptr(f));
  }
} else if (arity < fixed + 7) {
  obj * as[7] = { a1, a2, a3, a4, a5, a6, a7 };
  if (arity > 16) {
    for (unsigned i = 0; i < arity-fixed; i++) fx(fixed+i) = as[i];
    return apply_nc(FNN(f)(closure_arg_cptr(f)), 7+fixed-arity, as+arity-fixed);
  } else {
    obj* args[16];
    for (unsigned i = 0; i < fixed; i++) args[i] = fx(i);
    for (unsigned i = 0; i < arity-fixed; i++) args[fixed+i] = as[i];
    return apply_nc(curry(f, arity, args), 7+fixed-arity, as+arity-fixed);
  }
} else {
  return fix_args(f, {a1, a2, a3, a4, a5, a6, a7});
}
}
obj* apply_8(obj* f, obj* a1, obj* a2, obj* a3, obj* a4, obj* a5, obj* a6, obj* a7, obj* a8) {
unsigned arity = closure_arity(f);
unsigned fixed = closure_num_fixed(f);
if (arity == fixed + 8) {
  switch (arity) {
  case 8: return FN8(f)(a1, a2, a3, a4, a5, a6, a7, a8);
  case 9: return FN9(f)(fx(0), a1, a2, a3, a4, a5, a6, a7, a8);
  case 10: return FN10(f)(fx(0), fx(1), a1, a2, a3, a4, a5, a6, a7, a8);
  case 11: return FN11(f)(fx(0), fx(1), fx(2), a1, a2, a3, a4, a5, a6, a7, a8);
  case 12: return FN12(f)(fx(0), fx(1), fx(2), fx(3), a1, a2, a3, a4, a5, a6, a7, a8);
  case 13: return FN13(f)(fx(0), fx(1), fx(2), fx(3), fx(4), a1, a2, a3, a4, a5, a6, a7, a8);
  case 14: return FN14(f)(fx(0), fx(1), fx(2), fx(3), fx(4), fx(5), a1, a2, a3, a4, a5, a6, a7, a8);
  case 15: return FN15(f)(fx(0), fx(1), fx(2), fx(3), fx(4), fx(5), fx(6), a1, a2, a3, a4, a5, a6, a7, a8);
  case 16: return FN16(f)(fx(0), fx(1), fx(2), fx(3), fx(4), fx(5), fx(6), fx(7), a1, a2, a3, a4, a5, a6, a7, a8);
  default:
    lean_assert(arity > 16);
    fx(arity-8) = a1;
    fx(arity-7) = a2;
    fx(arity-6) = a3;
    fx(arity-5) = a4;
    fx(arity-4) = a5;
    fx(arity-3) = a6;
    fx(arity-2) = a7;
    fx(arity-1) = a8;
    return FNN(f)(closure_arg_cptr(f));
  }
} else if (arity < fixed + 8) {
  obj * as[8] = { a1, a2, a3, a4, a5, a6, a7, a8 };
  if (arity > 16) {
    for (unsigned i = 0; i < arity-fixed; i++) fx(fixed+i) = as[i];
    return apply_nc(FNN(f)(closure_arg_cptr(f)), 8+fixed-arity, as+arity-fixed);
  } else {
    obj* args[16];
    for (unsigned i = 0; i < fixed; i++) args[i] = fx(i);
    for (unsigned i = 0; i < arity-fixed; i++) args[fixed+i] = as[i];
    return apply_nc(curry(f, arity, args), 8+fixed-arity, as+arity-fixed);
  }
} else {
  return fix_args(f, {a1, a2, a3, a4, a5, a6, a7, a8});
}
}
obj* apply_9(obj* f, obj* a1, obj* a2, obj* a3, obj* a4, obj* a5, obj* a6, obj* a7, obj* a8, obj* a9) {
unsigned arity = closure_arity(f);
unsigned fixed = closure_num_fixed(f);
if (arity == fixed + 9) {
  switch (arity) {
  case 9: return FN9(f)(a1, a2, a3, a4, a5, a6, a7, a8, a9);
  case 10: return FN10(f)(fx(0), a1, a2, a3, a4, a5, a6, a7, a8, a9);
  case 11: return FN11(f)(fx(0), fx(1), a1, a2, a3, a4, a5, a6, a7, a8, a9);
  case 12: return FN12(f)(fx(0), fx(1), fx(2), a1, a2, a3, a4, a5, a6, a7, a8, a9);
  case 13: return FN13(f)(fx(0), fx(1), fx(2), fx(3), a1, a2, a3, a4, a5, a6, a7, a8, a9);
  case 14: return FN14(f)(fx(0), fx(1), fx(2), fx(3), fx(4), a1, a2, a3, a4, a5, a6, a7, a8, a9);
  case 15: return FN15(f)(fx(0), fx(1), fx(2), fx(3), fx(4), fx(5), a1, a2, a3, a4, a5, a6, a7, a8, a9);
  case 16: return FN16(f)(fx(0), fx(1), fx(2), fx(3), fx(4), fx(5), fx(6), a1, a2, a3, a4, a5, a6, a7, a8, a9);
  default:
    lean_assert(arity > 16);
    fx(arity-9) = a1;
    fx(arity-8) = a2;
    fx(arity-7) = a3;
    fx(arity-6) = a4;
    fx(arity-5) = a5;
    fx(arity-4) = a6;
    fx(arity-3) = a7;
    fx(arity-2) = a8;
    fx(arity-1) = a9;
    return FNN(f)(closure_arg_cptr(f));
  }
} else if (arity < fixed + 9) {
  obj * as[9] = { a1, a2, a3, a4, a5, a6, a7, a8, a9 };
  if (arity > 16) {
    for (unsigned i = 0; i < arity-fixed; i++) fx(fixed+i) = as[i];
    return apply_nc(FNN(f)(closure_arg_cptr(f)), 9+fixed-arity, as+arity-fixed);
  } else {
    obj* args[16];
    for (unsigned i = 0; i < fixed; i++) args[i] = fx(i);
    for (unsigned i = 0; i < arity-fixed; i++) args[fixed+i] = as[i];
    return apply_nc(curry(f, arity, args), 9+fixed-arity, as+arity-fixed);
  }
} else {
  return fix_args(f, {a1, a2, a3, a4, a5, a6, a7, a8, a9});
}
}
obj* apply_10(obj* f, obj* a1, obj* a2, obj* a3, obj* a4, obj* a5, obj* a6, obj* a7, obj* a8, obj* a9, obj* a10) {
unsigned arity = closure_arity(f);
unsigned fixed = closure_num_fixed(f);
if (arity == fixed + 10) {
  switch (arity) {
  case 10: return FN10(f)(a1, a2, a3, a4, a5, a6, a7, a8, a9, a10);
  case 11: return FN11(f)(fx(0), a1, a2, a3, a4, a5, a6, a7, a8, a9, a10);
  case 12: return FN12(f)(fx(0), fx(1), a1, a2, a3, a4, a5, a6, a7, a8, a9, a10);
  case 13: return FN13(f)(fx(0), fx(1), fx(2), a1, a2, a3, a4, a5, a6, a7, a8, a9, a10);
  case 14: return FN14(f)(fx(0), fx(1), fx(2), fx(3), a1, a2, a3, a4, a5, a6, a7, a8, a9, a10);
  case 15: return FN15(f)(fx(0), fx(1), fx(2), fx(3), fx(4), a1, a2, a3, a4, a5, a6, a7, a8, a9, a10);
  case 16: return FN16(f)(fx(0), fx(1), fx(2), fx(3), fx(4), fx(5), a1, a2, a3, a4, a5, a6, a7, a8, a9, a10);
  default:
    lean_assert(arity > 16);
    fx(arity-10) = a1;
    fx(arity-9) = a2;
    fx(arity-8) = a3;
    fx(arity-7) = a4;
    fx(arity-6) = a5;
    fx(arity-5) = a6;
    fx(arity-4) = a7;
    fx(arity-3) = a8;
    fx(arity-2) = a9;
    fx(arity-1) = a10;
    return FNN(f)(closure_arg_cptr(f));
  }
} else if (arity < fixed + 10) {
  obj * as[10] = { a1, a2, a3, a4, a5, a6, a7, a8, a9, a10 };
  if (arity > 16) {
    for (unsigned i = 0; i < arity-fixed; i++) fx(fixed+i) = as[i];
    return apply_nc(FNN(f)(closure_arg_cptr(f)), 10+fixed-arity, as+arity-fixed);
  } else {
    obj* args[16];
    for (unsigned i = 0; i < fixed; i++) args[i] = fx(i);
    for (unsigned i = 0; i < arity-fixed; i++) args[fixed+i] = as[i];
    return apply_nc(curry(f, arity, args), 10+fixed-arity, as+arity-fixed);
  }
} else {
  return fix_args(f, {a1, a2, a3, a4, a5, a6, a7, a8, a9, a10});
}
}
obj* apply_11(obj* f, obj* a1, obj* a2, obj* a3, obj* a4, obj* a5, obj* a6, obj* a7, obj* a8, obj* a9, obj* a10, obj* a11) {
unsigned arity = closure_arity(f);
unsigned fixed = closure_num_fixed(f);
if (arity == fixed + 11) {
  switch (arity) {
  case 11: return FN11(f)(a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11);
  case 12: return FN12(f)(fx(0), a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11);
  case 13: return FN13(f)(fx(0), fx(1), a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11);
  case 14: return FN14(f)(fx(0), fx(1), fx(2), a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11);
  case 15: return FN15(f)(fx(0), fx(1), fx(2), fx(3), a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11);
  case 16: return FN16(f)(fx(0), fx(1), fx(2), fx(3), fx(4), a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11);
  default:
    lean_assert(arity > 16);
    fx(arity-11) = a1;
    fx(arity-10) = a2;
    fx(arity-9) = a3;
    fx(arity-8) = a4;
    fx(arity-7) = a5;
    fx(arity-6) = a6;
    fx(arity-5) = a7;
    fx(arity-4) = a8;
    fx(arity-3) = a9;
    fx(arity-2) = a10;
    fx(arity-1) = a11;
    return FNN(f)(closure_arg_cptr(f));
  }
} else if (arity < fixed + 11) {
  obj * as[11] = { a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11 };
  if (arity > 16) {
    for (unsigned i = 0; i < arity-fixed; i++) fx(fixed+i) = as[i];
    return apply_nc(FNN(f)(closure_arg_cptr(f)), 11+fixed-arity, as+arity-fixed);
  } else {
    obj* args[16];
    for (unsigned i = 0; i < fixed; i++) args[i] = fx(i);
    for (unsigned i = 0; i < arity-fixed; i++) args[fixed+i] = as[i];
    return apply_nc(curry(f, arity, args), 11+fixed-arity, as+arity-fixed);
  }
} else {
  return fix_args(f, {a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11});
}
}
obj* apply_12(obj* f, obj* a1, obj* a2, obj* a3, obj* a4, obj* a5, obj* a6, obj* a7, obj* a8, obj* a9, obj* a10, obj* a11, obj* a12) {
unsigned arity = closure_arity(f);
unsigned fixed = closure_num_fixed(f);
if (arity == fixed + 12) {
  switch (arity) {
  case 12: return FN12(f)(a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12);
  case 13: return FN13(f)(fx(0), a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12);
  case 14: return FN14(f)(fx(0), fx(1), a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12);
  case 15: return FN15(f)(fx(0), fx(1), fx(2), a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12);
  case 16: return FN16(f)(fx(0), fx(1), fx(2), fx(3), a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12);
  default:
    lean_assert(arity > 16);
    fx(arity-12) = a1;
    fx(arity-11) = a2;
    fx(arity-10) = a3;
    fx(arity-9) = a4;
    fx(arity-8) = a5;
    fx(arity-7) = a6;
    fx(arity-6) = a7;
    fx(arity-5) = a8;
    fx(arity-4) = a9;
    fx(arity-3) = a10;
    fx(arity-2) = a11;
    fx(arity-1) = a12;
    return FNN(f)(closure_arg_cptr(f));
  }
} else if (arity < fixed + 12) {
  obj * as[12] = { a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12 };
  if (arity > 16) {
    for (unsigned i = 0; i < arity-fixed; i++) fx(fixed+i) = as[i];
    return apply_nc(FNN(f)(closure_arg_cptr(f)), 12+fixed-arity, as+arity-fixed);
  } else {
    obj* args[16];
    for (unsigned i = 0; i < fixed; i++) args[i] = fx(i);
    for (unsigned i = 0; i < arity-fixed; i++) args[fixed+i] = as[i];
    return apply_nc(curry(f, arity, args), 12+fixed-arity, as+arity-fixed);
  }
} else {
  return fix_args(f, {a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12});
}
}
obj* apply_13(obj* f, obj* a1, obj* a2, obj* a3, obj* a4, obj* a5, obj* a6, obj* a7, obj* a8, obj* a9, obj* a10, obj* a11, obj* a12, obj* a13) {
unsigned arity = closure_arity(f);
unsigned fixed = closure_num_fixed(f);
if (arity == fixed + 13) {
  switch (arity) {
  case 13: return FN13(f)(a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13);
  case 14: return FN14(f)(fx(0), a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13);
  case 15: return FN15(f)(fx(0), fx(1), a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13);
  case 16: return FN16(f)(fx(0), fx(1), fx(2), a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13);
  default:
    lean_assert(arity > 16);
    fx(arity-13) = a1;
    fx(arity-12) = a2;
    fx(arity-11) = a3;
    fx(arity-10) = a4;
    fx(arity-9) = a5;
    fx(arity-8) = a6;
    fx(arity-7) = a7;
    fx(arity-6) = a8;
    fx(arity-5) = a9;
    fx(arity-4) = a10;
    fx(arity-3) = a11;
    fx(arity-2) = a12;
    fx(arity-1) = a13;
    return FNN(f)(closure_arg_cptr(f));
  }
} else if (arity < fixed + 13) {
  obj * as[13] = { a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13 };
  if (arity > 16) {
    for (unsigned i = 0; i < arity-fixed; i++) fx(fixed+i) = as[i];
    return apply_nc(FNN(f)(closure_arg_cptr(f)), 13+fixed-arity, as+arity-fixed);
  } else {
    obj* args[16];
    for (unsigned i = 0; i < fixed; i++) args[i] = fx(i);
    for (unsigned i = 0; i < arity-fixed; i++) args[fixed+i] = as[i];
    return apply_nc(curry(f, arity, args), 13+fixed-arity, as+arity-fixed);
  }
} else {
  return fix_args(f, {a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13});
}
}
obj* apply_14(obj* f, obj* a1, obj* a2, obj* a3, obj* a4, obj* a5, obj* a6, obj* a7, obj* a8, obj* a9, obj* a10, obj* a11, obj* a12, obj* a13, obj* a14) {
unsigned arity = closure_arity(f);
unsigned fixed = closure_num_fixed(f);
if (arity == fixed + 14) {
  switch (arity) {
  case 14: return FN14(f)(a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14);
  case 15: return FN15(f)(fx(0), a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14);
  case 16: return FN16(f)(fx(0), fx(1), a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14);
  default:
    lean_assert(arity > 16);
    fx(arity-14) = a1;
    fx(arity-13) = a2;
    fx(arity-12) = a3;
    fx(arity-11) = a4;
    fx(arity-10) = a5;
    fx(arity-9) = a6;
    fx(arity-8) = a7;
    fx(arity-7) = a8;
    fx(arity-6) = a9;
    fx(arity-5) = a10;
    fx(arity-4) = a11;
    fx(arity-3) = a12;
    fx(arity-2) = a13;
    fx(arity-1) = a14;
    return FNN(f)(closure_arg_cptr(f));
  }
} else if (arity < fixed + 14) {
  obj * as[14] = { a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14 };
  if (arity > 16) {
    for (unsigned i = 0; i < arity-fixed; i++) fx(fixed+i) = as[i];
    return apply_nc(FNN(f)(closure_arg_cptr(f)), 14+fixed-arity, as+arity-fixed);
  } else {
    obj* args[16];
    for (unsigned i = 0; i < fixed; i++) args[i] = fx(i);
    for (unsigned i = 0; i < arity-fixed; i++) args[fixed+i] = as[i];
    return apply_nc(curry(f, arity, args), 14+fixed-arity, as+arity-fixed);
  }
} else {
  return fix_args(f, {a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14});
}
}
obj* apply_15(obj* f, obj* a1, obj* a2, obj* a3, obj* a4, obj* a5, obj* a6, obj* a7, obj* a8, obj* a9, obj* a10, obj* a11, obj* a12, obj* a13, obj* a14, obj* a15) {
unsigned arity = closure_arity(f);
unsigned fixed = closure_num_fixed(f);
if (arity == fixed + 15) {
  switch (arity) {
  case 15: return FN15(f)(a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15);
  case 16: return FN16(f)(fx(0), a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15);
  default:
    lean_assert(arity > 16);
    fx(arity-15) = a1;
    fx(arity-14) = a2;
    fx(arity-13) = a3;
    fx(arity-12) = a4;
    fx(arity-11) = a5;
    fx(arity-10) = a6;
    fx(arity-9) = a7;
    fx(arity-8) = a8;
    fx(arity-7) = a9;
    fx(arity-6) = a10;
    fx(arity-5) = a11;
    fx(arity-4) = a12;
    fx(arity-3) = a13;
    fx(arity-2) = a14;
    fx(arity-1) = a15;
    return FNN(f)(closure_arg_cptr(f));
  }
} else if (arity < fixed + 15) {
  obj * as[15] = { a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15 };
  if (arity > 16) {
    for (unsigned i = 0; i < arity-fixed; i++) fx(fixed+i) = as[i];
    return apply_nc(FNN(f)(closure_arg_cptr(f)), 15+fixed-arity, as+arity-fixed);
  } else {
    obj* args[16];
    for (unsigned i = 0; i < fixed; i++) args[i] = fx(i);
    for (unsigned i = 0; i < arity-fixed; i++) args[fixed+i] = as[i];
    return apply_nc(curry(f, arity, args), 15+fixed-arity, as+arity-fixed);
  }
} else {
  return fix_args(f, {a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15});
}
}
obj* apply_16(obj* f, obj* a1, obj* a2, obj* a3, obj* a4, obj* a5, obj* a6, obj* a7, obj* a8, obj* a9, obj* a10, obj* a11, obj* a12, obj* a13, obj* a14, obj* a15, obj* a16) {
unsigned arity = closure_arity(f);
unsigned fixed = closure_num_fixed(f);
if (arity == fixed + 16) {
  switch (arity) {
  case 16: return FN16(f)(a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16);
  default:
    lean_assert(arity > 16);
    fx(arity-16) = a1;
    fx(arity-15) = a2;
    fx(arity-14) = a3;
    fx(arity-13) = a4;
    fx(arity-12) = a5;
    fx(arity-11) = a6;
    fx(arity-10) = a7;
    fx(arity-9) = a8;
    fx(arity-8) = a9;
    fx(arity-7) = a10;
    fx(arity-6) = a11;
    fx(arity-5) = a12;
    fx(arity-4) = a13;
    fx(arity-3) = a14;
    fx(arity-2) = a15;
    fx(arity-1) = a16;
    return FNN(f)(closure_arg_cptr(f));
  }
} else if (arity < fixed + 16) {
  obj * as[16] = { a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16 };
  if (arity > 16) {
    for (unsigned i = 0; i < arity-fixed; i++) fx(fixed+i) = as[i];
    return apply_nc(FNN(f)(closure_arg_cptr(f)), 16+fixed-arity, as+arity-fixed);
  } else {
    obj* args[16];
    for (unsigned i = 0; i < fixed; i++) args[i] = fx(i);
    for (unsigned i = 0; i < arity-fixed; i++) args[fixed+i] = as[i];
    return apply_nc(curry(f, arity, args), 16+fixed-arity, as+arity-fixed);
  }
} else {
  return fix_args(f, {a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16});
}
}
obj* apply_m(obj* f, unsigned n, obj** as) {
lean_assert(n > 16);
unsigned arity = closure_arity(f);
unsigned fixed = closure_num_fixed(f);
if (arity == fixed + n) {
  for (unsigned i = 0; i < n; i++) fx(arity-n+i) = as[i];
  return FNN(f)(closure_arg_cptr(f));
} else if (arity < fixed + n) {
  for (unsigned i = 0; i < arity-fixed; i++) fx(fixed+i) = as[i];
  return apply_nc(FNN(f)(closure_arg_cptr(f)), n+fixed-arity, as+arity-fixed);
} else {
  return fix_args(f, n, as);
}
}
obj* apply_n(obj* f, unsigned n, obj** as) {
switch (n) {
case 0: lean_unreachable();
case 1: return apply_1(f, as[0]);
case 2: return apply_2(f, as[0], as[1]);
case 3: return apply_3(f, as[0], as[1], as[2]);
case 4: return apply_4(f, as[0], as[1], as[2], as[3]);
case 5: return apply_5(f, as[0], as[1], as[2], as[3], as[4]);
case 6: return apply_6(f, as[0], as[1], as[2], as[3], as[4], as[5]);
case 7: return apply_7(f, as[0], as[1], as[2], as[3], as[4], as[5], as[6]);
case 8: return apply_8(f, as[0], as[1], as[2], as[3], as[4], as[5], as[6], as[7]);
case 9: return apply_9(f, as[0], as[1], as[2], as[3], as[4], as[5], as[6], as[7], as[8]);
case 10: return apply_10(f, as[0], as[1], as[2], as[3], as[4], as[5], as[6], as[7], as[8], as[9]);
case 11: return apply_11(f, as[0], as[1], as[2], as[3], as[4], as[5], as[6], as[7], as[8], as[9], as[10]);
case 12: return apply_12(f, as[0], as[1], as[2], as[3], as[4], as[5], as[6], as[7], as[8], as[9], as[10], as[11]);
case 13: return apply_13(f, as[0], as[1], as[2], as[3], as[4], as[5], as[6], as[7], as[8], as[9], as[10], as[11], as[12]);
case 14: return apply_14(f, as[0], as[1], as[2], as[3], as[4], as[5], as[6], as[7], as[8], as[9], as[10], as[11], as[12], as[13]);
case 15: return apply_15(f, as[0], as[1], as[2], as[3], as[4], as[5], as[6], as[7], as[8], as[9], as[10], as[11], as[12], as[13], as[14]);
case 16: return apply_16(f, as[0], as[1], as[2], as[3], as[4], as[5], as[6], as[7], as[8], as[9], as[10], as[11], as[12], as[13], as[14], as[15]);
default: return apply_m(f, n, as);
}
}
}
