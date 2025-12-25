/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
// DO NOT EDIT, this is an automatically generated file
// Generated using script: ../../gen/apply.lean
#include "runtime/apply.h"
namespace lean {
#define obj lean_object
#define fx(i) lean_closure_arg_cptr(f)[i]

static obj* fix_args(obj* f, unsigned n, obj*const* as) {
    unsigned arity = lean_closure_arity(f);
    unsigned fixed = lean_closure_num_fixed(f);
    unsigned new_fixed = fixed + n;
    lean_assert(new_fixed < arity);
    obj * r = lean_alloc_closure(lean_closure_fun(f), arity, new_fixed);
    obj ** source = lean_closure_arg_cptr(f);
    obj ** target = lean_closure_arg_cptr(r);
    if (!lean_is_exclusive(f)) {
      for (unsigned i = 0; i < fixed; i++, source++, target++) {
          *target = *source;
          lean_inc(*target);
      }
      lean_dec_ref(f);
    } else {
      for (unsigned i = 0; i < fixed; i++, source++, target++) {
          *target = *source;
      }
      lean_free_object(f);
    }
    for (unsigned i = 0; i < n; i++, as++, target++) {
        *target = *as;
    }
    return r;
}

static inline obj* fix_args(obj* f, std::initializer_list<obj*> const & l) {
    return fix_args(f, l.size(), l.begin());
}
typedef obj* (*fn1)(obj*); // NOLINT
#define FN1(f) reinterpret_cast<fn1>(lean_closure_fun(f))
typedef obj* (*fn2)(obj*, obj*); // NOLINT
#define FN2(f) reinterpret_cast<fn2>(lean_closure_fun(f))
typedef obj* (*fn3)(obj*, obj*, obj*); // NOLINT
#define FN3(f) reinterpret_cast<fn3>(lean_closure_fun(f))
typedef obj* (*fn4)(obj*, obj*, obj*, obj*); // NOLINT
#define FN4(f) reinterpret_cast<fn4>(lean_closure_fun(f))
typedef obj* (*fn5)(obj*, obj*, obj*, obj*, obj*); // NOLINT
#define FN5(f) reinterpret_cast<fn5>(lean_closure_fun(f))
typedef obj* (*fn6)(obj*, obj*, obj*, obj*, obj*, obj*); // NOLINT
#define FN6(f) reinterpret_cast<fn6>(lean_closure_fun(f))
typedef obj* (*fn7)(obj*, obj*, obj*, obj*, obj*, obj*, obj*); // NOLINT
#define FN7(f) reinterpret_cast<fn7>(lean_closure_fun(f))
typedef obj* (*fn8)(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*); // NOLINT
#define FN8(f) reinterpret_cast<fn8>(lean_closure_fun(f))
typedef obj* (*fn9)(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*); // NOLINT
#define FN9(f) reinterpret_cast<fn9>(lean_closure_fun(f))
typedef obj* (*fn10)(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*); // NOLINT
#define FN10(f) reinterpret_cast<fn10>(lean_closure_fun(f))
typedef obj* (*fn11)(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*); // NOLINT
#define FN11(f) reinterpret_cast<fn11>(lean_closure_fun(f))
typedef obj* (*fn12)(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*); // NOLINT
#define FN12(f) reinterpret_cast<fn12>(lean_closure_fun(f))
typedef obj* (*fn13)(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*); // NOLINT
#define FN13(f) reinterpret_cast<fn13>(lean_closure_fun(f))
typedef obj* (*fn14)(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*); // NOLINT
#define FN14(f) reinterpret_cast<fn14>(lean_closure_fun(f))
typedef obj* (*fn15)(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*); // NOLINT
#define FN15(f) reinterpret_cast<fn15>(lean_closure_fun(f))
typedef obj* (*fn16)(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*); // NOLINT
#define FN16(f) reinterpret_cast<fn16>(lean_closure_fun(f))
typedef obj* (*fnn)(obj**); // NOLINT
#define FNN(f) reinterpret_cast<fnn>(lean_closure_fun(f))
obj* curry(void* f, unsigned n, obj** as) {
switch (n) {
case 0: lean_unreachable();
case 1: return reinterpret_cast<fn1>(f)(as[0]);
case 2: return reinterpret_cast<fn2>(f)(as[0], as[1]);
case 3: return reinterpret_cast<fn3>(f)(as[0], as[1], as[2]);
case 4: return reinterpret_cast<fn4>(f)(as[0], as[1], as[2], as[3]);
case 5: return reinterpret_cast<fn5>(f)(as[0], as[1], as[2], as[3], as[4]);
case 6: return reinterpret_cast<fn6>(f)(as[0], as[1], as[2], as[3], as[4], as[5]);
case 7: return reinterpret_cast<fn7>(f)(as[0], as[1], as[2], as[3], as[4], as[5], as[6]);
case 8: return reinterpret_cast<fn8>(f)(as[0], as[1], as[2], as[3], as[4], as[5], as[6], as[7]);
case 9: return reinterpret_cast<fn9>(f)(as[0], as[1], as[2], as[3], as[4], as[5], as[6], as[7], as[8]);
case 10: return reinterpret_cast<fn10>(f)(as[0], as[1], as[2], as[3], as[4], as[5], as[6], as[7], as[8], as[9]);
case 11: return reinterpret_cast<fn11>(f)(as[0], as[1], as[2], as[3], as[4], as[5], as[6], as[7], as[8], as[9], as[10]);
case 12: return reinterpret_cast<fn12>(f)(as[0], as[1], as[2], as[3], as[4], as[5], as[6], as[7], as[8], as[9], as[10], as[11]);
case 13: return reinterpret_cast<fn13>(f)(as[0], as[1], as[2], as[3], as[4], as[5], as[6], as[7], as[8], as[9], as[10], as[11], as[12]);
case 14: return reinterpret_cast<fn14>(f)(as[0], as[1], as[2], as[3], as[4], as[5], as[6], as[7], as[8], as[9], as[10], as[11], as[12], as[13]);
case 15: return reinterpret_cast<fn15>(f)(as[0], as[1], as[2], as[3], as[4], as[5], as[6], as[7], as[8], as[9], as[10], as[11], as[12], as[13], as[14]);
case 16: return reinterpret_cast<fn16>(f)(as[0], as[1], as[2], as[3], as[4], as[5], as[6], as[7], as[8], as[9], as[10], as[11], as[12], as[13], as[14], as[15]);
default: return reinterpret_cast<fnn>(f)(as);
}
}
static obj* curry(obj* f, unsigned n, obj** as) { return curry(lean_closure_fun(f), n, as); }
extern "C" obj* lean_apply_n(obj*, unsigned, obj**);
extern "C" LEAN_EXPORT obj* lean_apply_1(obj* f, obj* a1) {
if (lean_is_scalar(f)) { lean_dec(a1); return f; } // f is an erased proof
unsigned arity = lean_closure_arity(f);
unsigned fixed = lean_closure_num_fixed(f);
if (arity == fixed + 1) {
  if (lean_is_exclusive(f)) {
    switch (arity) {
    case 1: { fn1 fn = FN1(f); lean_free_object(f); return fn(a1); }
    case 2: { obj* fx0 = fx(0); fn2 fn = FN2(f); lean_free_object(f); return fn(fx0, a1); }
    case 3: { obj* fx0 = fx(0); obj* fx1 = fx(1); fn3 fn = FN3(f); lean_free_object(f); return fn(fx0, fx1, a1); }
    case 4: { obj* fx0 = fx(0); obj* fx1 = fx(1); obj* fx2 = fx(2); fn4 fn = FN4(f); lean_free_object(f); return fn(fx0, fx1, fx2, a1); }
    case 5: { obj* fx0 = fx(0); obj* fx1 = fx(1); obj* fx2 = fx(2); obj* fx3 = fx(3); fn5 fn = FN5(f); lean_free_object(f); return fn(fx0, fx1, fx2, fx3, a1); }
    case 6: { obj* fx0 = fx(0); obj* fx1 = fx(1); obj* fx2 = fx(2); obj* fx3 = fx(3); obj* fx4 = fx(4); fn6 fn = FN6(f); lean_free_object(f); return fn(fx0, fx1, fx2, fx3, fx4, a1); }
    case 7: { obj* fx0 = fx(0); obj* fx1 = fx(1); obj* fx2 = fx(2); obj* fx3 = fx(3); obj* fx4 = fx(4); obj* fx5 = fx(5); fn7 fn = FN7(f); lean_free_object(f); return fn(fx0, fx1, fx2, fx3, fx4, fx5, a1); }
    case 8: { obj* fx0 = fx(0); obj* fx1 = fx(1); obj* fx2 = fx(2); obj* fx3 = fx(3); obj* fx4 = fx(4); obj* fx5 = fx(5); obj* fx6 = fx(6); fn8 fn = FN8(f); lean_free_object(f); return fn(fx0, fx1, fx2, fx3, fx4, fx5, fx6, a1); }
    case 9: { obj* fx0 = fx(0); obj* fx1 = fx(1); obj* fx2 = fx(2); obj* fx3 = fx(3); obj* fx4 = fx(4); obj* fx5 = fx(5); obj* fx6 = fx(6); obj* fx7 = fx(7); fn9 fn = FN9(f); lean_free_object(f); return fn(fx0, fx1, fx2, fx3, fx4, fx5, fx6, fx7, a1); }
    case 10: { obj* fx0 = fx(0); obj* fx1 = fx(1); obj* fx2 = fx(2); obj* fx3 = fx(3); obj* fx4 = fx(4); obj* fx5 = fx(5); obj* fx6 = fx(6); obj* fx7 = fx(7); obj* fx8 = fx(8); fn10 fn = FN10(f); lean_free_object(f); return fn(fx0, fx1, fx2, fx3, fx4, fx5, fx6, fx7, fx8, a1); }
    case 11: { obj* fx0 = fx(0); obj* fx1 = fx(1); obj* fx2 = fx(2); obj* fx3 = fx(3); obj* fx4 = fx(4); obj* fx5 = fx(5); obj* fx6 = fx(6); obj* fx7 = fx(7); obj* fx8 = fx(8); obj* fx9 = fx(9); fn11 fn = FN11(f); lean_free_object(f); return fn(fx0, fx1, fx2, fx3, fx4, fx5, fx6, fx7, fx8, fx9, a1); }
    case 12: { obj* fx0 = fx(0); obj* fx1 = fx(1); obj* fx2 = fx(2); obj* fx3 = fx(3); obj* fx4 = fx(4); obj* fx5 = fx(5); obj* fx6 = fx(6); obj* fx7 = fx(7); obj* fx8 = fx(8); obj* fx9 = fx(9); obj* fx10 = fx(10); fn12 fn = FN12(f); lean_free_object(f); return fn(fx0, fx1, fx2, fx3, fx4, fx5, fx6, fx7, fx8, fx9, fx10, a1); }
    case 13: { obj* fx0 = fx(0); obj* fx1 = fx(1); obj* fx2 = fx(2); obj* fx3 = fx(3); obj* fx4 = fx(4); obj* fx5 = fx(5); obj* fx6 = fx(6); obj* fx7 = fx(7); obj* fx8 = fx(8); obj* fx9 = fx(9); obj* fx10 = fx(10); obj* fx11 = fx(11); fn13 fn = FN13(f); lean_free_object(f); return fn(fx0, fx1, fx2, fx3, fx4, fx5, fx6, fx7, fx8, fx9, fx10, fx11, a1); }
    case 14: { obj* fx0 = fx(0); obj* fx1 = fx(1); obj* fx2 = fx(2); obj* fx3 = fx(3); obj* fx4 = fx(4); obj* fx5 = fx(5); obj* fx6 = fx(6); obj* fx7 = fx(7); obj* fx8 = fx(8); obj* fx9 = fx(9); obj* fx10 = fx(10); obj* fx11 = fx(11); obj* fx12 = fx(12); fn14 fn = FN14(f); lean_free_object(f); return fn(fx0, fx1, fx2, fx3, fx4, fx5, fx6, fx7, fx8, fx9, fx10, fx11, fx12, a1); }
    case 15: { obj* fx0 = fx(0); obj* fx1 = fx(1); obj* fx2 = fx(2); obj* fx3 = fx(3); obj* fx4 = fx(4); obj* fx5 = fx(5); obj* fx6 = fx(6); obj* fx7 = fx(7); obj* fx8 = fx(8); obj* fx9 = fx(9); obj* fx10 = fx(10); obj* fx11 = fx(11); obj* fx12 = fx(12); obj* fx13 = fx(13); fn15 fn = FN15(f); lean_free_object(f); return fn(fx0, fx1, fx2, fx3, fx4, fx5, fx6, fx7, fx8, fx9, fx10, fx11, fx12, fx13, a1); }
    case 16: { obj* fx0 = fx(0); obj* fx1 = fx(1); obj* fx2 = fx(2); obj* fx3 = fx(3); obj* fx4 = fx(4); obj* fx5 = fx(5); obj* fx6 = fx(6); obj* fx7 = fx(7); obj* fx8 = fx(8); obj* fx9 = fx(9); obj* fx10 = fx(10); obj* fx11 = fx(11); obj* fx12 = fx(12); obj* fx13 = fx(13); obj* fx14 = fx(14); fn16 fn = FN16(f); lean_free_object(f); return fn(fx0, fx1, fx2, fx3, fx4, fx5, fx6, fx7, fx8, fx9, fx10, fx11, fx12, fx13, fx14, a1); }
    }
  }
  switch (arity) {
  case 1: { fn1 fn = FN1(f); lean_dec_ref(f); return fn(a1); }
  case 2: { obj* fx0 = fx(0); lean_inc(fx0); fn2 fn = FN2(f); lean_dec_ref(f); return fn(fx0, a1); }
  case 3: { obj* fx0 = fx(0); obj* fx1 = fx(1); lean_inc(fx0); lean_inc(fx1); fn3 fn = FN3(f); lean_dec_ref(f); return fn(fx0, fx1, a1); }
  case 4: { obj* fx0 = fx(0); obj* fx1 = fx(1); obj* fx2 = fx(2); lean_inc(fx0); lean_inc(fx1); lean_inc(fx2); fn4 fn = FN4(f); lean_dec_ref(f); return fn(fx0, fx1, fx2, a1); }
  case 5: { obj* fx0 = fx(0); obj* fx1 = fx(1); obj* fx2 = fx(2); obj* fx3 = fx(3); lean_inc(fx0); lean_inc(fx1); lean_inc(fx2); lean_inc(fx3); fn5 fn = FN5(f); lean_dec_ref(f); return fn(fx0, fx1, fx2, fx3, a1); }
  case 6: { obj* fx0 = fx(0); obj* fx1 = fx(1); obj* fx2 = fx(2); obj* fx3 = fx(3); obj* fx4 = fx(4); lean_inc(fx0); lean_inc(fx1); lean_inc(fx2); lean_inc(fx3); lean_inc(fx4); fn6 fn = FN6(f); lean_dec_ref(f); return fn(fx0, fx1, fx2, fx3, fx4, a1); }
  case 7: { obj* fx0 = fx(0); obj* fx1 = fx(1); obj* fx2 = fx(2); obj* fx3 = fx(3); obj* fx4 = fx(4); obj* fx5 = fx(5); lean_inc(fx0); lean_inc(fx1); lean_inc(fx2); lean_inc(fx3); lean_inc(fx4); lean_inc(fx5); fn7 fn = FN7(f); lean_dec_ref(f); return fn(fx0, fx1, fx2, fx3, fx4, fx5, a1); }
  case 8: { obj* fx0 = fx(0); obj* fx1 = fx(1); obj* fx2 = fx(2); obj* fx3 = fx(3); obj* fx4 = fx(4); obj* fx5 = fx(5); obj* fx6 = fx(6); lean_inc(fx0); lean_inc(fx1); lean_inc(fx2); lean_inc(fx3); lean_inc(fx4); lean_inc(fx5); lean_inc(fx6); fn8 fn = FN8(f); lean_dec_ref(f); return fn(fx0, fx1, fx2, fx3, fx4, fx5, fx6, a1); }
  case 9: { obj* fx0 = fx(0); obj* fx1 = fx(1); obj* fx2 = fx(2); obj* fx3 = fx(3); obj* fx4 = fx(4); obj* fx5 = fx(5); obj* fx6 = fx(6); obj* fx7 = fx(7); lean_inc(fx0); lean_inc(fx1); lean_inc(fx2); lean_inc(fx3); lean_inc(fx4); lean_inc(fx5); lean_inc(fx6); lean_inc(fx7); fn9 fn = FN9(f); lean_dec_ref(f); return fn(fx0, fx1, fx2, fx3, fx4, fx5, fx6, fx7, a1); }
  case 10: { obj* fx0 = fx(0); obj* fx1 = fx(1); obj* fx2 = fx(2); obj* fx3 = fx(3); obj* fx4 = fx(4); obj* fx5 = fx(5); obj* fx6 = fx(6); obj* fx7 = fx(7); obj* fx8 = fx(8); lean_inc(fx0); lean_inc(fx1); lean_inc(fx2); lean_inc(fx3); lean_inc(fx4); lean_inc(fx5); lean_inc(fx6); lean_inc(fx7); lean_inc(fx8); fn10 fn = FN10(f); lean_dec_ref(f); return fn(fx0, fx1, fx2, fx3, fx4, fx5, fx6, fx7, fx8, a1); }
  case 11: { obj* fx0 = fx(0); obj* fx1 = fx(1); obj* fx2 = fx(2); obj* fx3 = fx(3); obj* fx4 = fx(4); obj* fx5 = fx(5); obj* fx6 = fx(6); obj* fx7 = fx(7); obj* fx8 = fx(8); obj* fx9 = fx(9); lean_inc(fx0); lean_inc(fx1); lean_inc(fx2); lean_inc(fx3); lean_inc(fx4); lean_inc(fx5); lean_inc(fx6); lean_inc(fx7); lean_inc(fx8); lean_inc(fx9); fn11 fn = FN11(f); lean_dec_ref(f); return fn(fx0, fx1, fx2, fx3, fx4, fx5, fx6, fx7, fx8, fx9, a1); }
  case 12: { obj* fx0 = fx(0); obj* fx1 = fx(1); obj* fx2 = fx(2); obj* fx3 = fx(3); obj* fx4 = fx(4); obj* fx5 = fx(5); obj* fx6 = fx(6); obj* fx7 = fx(7); obj* fx8 = fx(8); obj* fx9 = fx(9); obj* fx10 = fx(10); lean_inc(fx0); lean_inc(fx1); lean_inc(fx2); lean_inc(fx3); lean_inc(fx4); lean_inc(fx5); lean_inc(fx6); lean_inc(fx7); lean_inc(fx8); lean_inc(fx9); lean_inc(fx10); fn12 fn = FN12(f); lean_dec_ref(f); return fn(fx0, fx1, fx2, fx3, fx4, fx5, fx6, fx7, fx8, fx9, fx10, a1); }
  case 13: { obj* fx0 = fx(0); obj* fx1 = fx(1); obj* fx2 = fx(2); obj* fx3 = fx(3); obj* fx4 = fx(4); obj* fx5 = fx(5); obj* fx6 = fx(6); obj* fx7 = fx(7); obj* fx8 = fx(8); obj* fx9 = fx(9); obj* fx10 = fx(10); obj* fx11 = fx(11); lean_inc(fx0); lean_inc(fx1); lean_inc(fx2); lean_inc(fx3); lean_inc(fx4); lean_inc(fx5); lean_inc(fx6); lean_inc(fx7); lean_inc(fx8); lean_inc(fx9); lean_inc(fx10); lean_inc(fx11); fn13 fn = FN13(f); lean_dec_ref(f); return fn(fx0, fx1, fx2, fx3, fx4, fx5, fx6, fx7, fx8, fx9, fx10, fx11, a1); }
  case 14: { obj* fx0 = fx(0); obj* fx1 = fx(1); obj* fx2 = fx(2); obj* fx3 = fx(3); obj* fx4 = fx(4); obj* fx5 = fx(5); obj* fx6 = fx(6); obj* fx7 = fx(7); obj* fx8 = fx(8); obj* fx9 = fx(9); obj* fx10 = fx(10); obj* fx11 = fx(11); obj* fx12 = fx(12); lean_inc(fx0); lean_inc(fx1); lean_inc(fx2); lean_inc(fx3); lean_inc(fx4); lean_inc(fx5); lean_inc(fx6); lean_inc(fx7); lean_inc(fx8); lean_inc(fx9); lean_inc(fx10); lean_inc(fx11); lean_inc(fx12); fn14 fn = FN14(f); lean_dec_ref(f); return fn(fx0, fx1, fx2, fx3, fx4, fx5, fx6, fx7, fx8, fx9, fx10, fx11, fx12, a1); }
  case 15: { obj* fx0 = fx(0); obj* fx1 = fx(1); obj* fx2 = fx(2); obj* fx3 = fx(3); obj* fx4 = fx(4); obj* fx5 = fx(5); obj* fx6 = fx(6); obj* fx7 = fx(7); obj* fx8 = fx(8); obj* fx9 = fx(9); obj* fx10 = fx(10); obj* fx11 = fx(11); obj* fx12 = fx(12); obj* fx13 = fx(13); lean_inc(fx0); lean_inc(fx1); lean_inc(fx2); lean_inc(fx3); lean_inc(fx4); lean_inc(fx5); lean_inc(fx6); lean_inc(fx7); lean_inc(fx8); lean_inc(fx9); lean_inc(fx10); lean_inc(fx11); lean_inc(fx12); lean_inc(fx13); fn15 fn = FN15(f); lean_dec_ref(f); return fn(fx0, fx1, fx2, fx3, fx4, fx5, fx6, fx7, fx8, fx9, fx10, fx11, fx12, fx13, a1); }
  case 16: { obj* fx0 = fx(0); obj* fx1 = fx(1); obj* fx2 = fx(2); obj* fx3 = fx(3); obj* fx4 = fx(4); obj* fx5 = fx(5); obj* fx6 = fx(6); obj* fx7 = fx(7); obj* fx8 = fx(8); obj* fx9 = fx(9); obj* fx10 = fx(10); obj* fx11 = fx(11); obj* fx12 = fx(12); obj* fx13 = fx(13); obj* fx14 = fx(14); lean_inc(fx0); lean_inc(fx1); lean_inc(fx2); lean_inc(fx3); lean_inc(fx4); lean_inc(fx5); lean_inc(fx6); lean_inc(fx7); lean_inc(fx8); lean_inc(fx9); lean_inc(fx10); lean_inc(fx11); lean_inc(fx12); lean_inc(fx13); lean_inc(fx14); fn16 fn = FN16(f); lean_dec_ref(f); return fn(fx0, fx1, fx2, fx3, fx4, fx5, fx6, fx7, fx8, fx9, fx10, fx11, fx12, fx13, fx14, a1); }
  default:
    lean_assert(arity > 16);
    obj * as[1] = { a1 };
    obj ** args = static_cast<obj**>(LEAN_ALLOCA(arity*sizeof(obj*))); // NOLINT
    for (unsigned i = 0; i < fixed; i++) { lean_inc(fx(i)); args[i] = fx(i); }
    for (unsigned i = 0; i < 1; i++) args[fixed+i] = as[i];
    fnn fn = FNN(f);
    lean_dec_ref(f);
    return fn(args);
  }
} else if (arity < fixed + 1) {
  lean_assert(fixed < arity);
  lean_unreachable();
} else {
  return fix_args(f, {a1});
}
}
extern "C" LEAN_EXPORT obj* lean_apply_2(obj* f, obj* a1, obj* a2) {
if (lean_is_scalar(f)) { lean_dec(a1); lean_dec(a2); return f; } // f is an erased proof
unsigned arity = lean_closure_arity(f);
unsigned fixed = lean_closure_num_fixed(f);
if (arity == fixed + 2) {
  if (lean_is_exclusive(f)) {
    switch (arity) {
    case 2: { fn2 fn = FN2(f); lean_free_object(f); return fn(a1, a2); }
    case 3: { obj* fx0 = fx(0); fn3 fn = FN3(f); lean_free_object(f); return fn(fx0, a1, a2); }
    case 4: { obj* fx0 = fx(0); obj* fx1 = fx(1); fn4 fn = FN4(f); lean_free_object(f); return fn(fx0, fx1, a1, a2); }
    case 5: { obj* fx0 = fx(0); obj* fx1 = fx(1); obj* fx2 = fx(2); fn5 fn = FN5(f); lean_free_object(f); return fn(fx0, fx1, fx2, a1, a2); }
    case 6: { obj* fx0 = fx(0); obj* fx1 = fx(1); obj* fx2 = fx(2); obj* fx3 = fx(3); fn6 fn = FN6(f); lean_free_object(f); return fn(fx0, fx1, fx2, fx3, a1, a2); }
    case 7: { obj* fx0 = fx(0); obj* fx1 = fx(1); obj* fx2 = fx(2); obj* fx3 = fx(3); obj* fx4 = fx(4); fn7 fn = FN7(f); lean_free_object(f); return fn(fx0, fx1, fx2, fx3, fx4, a1, a2); }
    case 8: { obj* fx0 = fx(0); obj* fx1 = fx(1); obj* fx2 = fx(2); obj* fx3 = fx(3); obj* fx4 = fx(4); obj* fx5 = fx(5); fn8 fn = FN8(f); lean_free_object(f); return fn(fx0, fx1, fx2, fx3, fx4, fx5, a1, a2); }
    case 9: { obj* fx0 = fx(0); obj* fx1 = fx(1); obj* fx2 = fx(2); obj* fx3 = fx(3); obj* fx4 = fx(4); obj* fx5 = fx(5); obj* fx6 = fx(6); fn9 fn = FN9(f); lean_free_object(f); return fn(fx0, fx1, fx2, fx3, fx4, fx5, fx6, a1, a2); }
    case 10: { obj* fx0 = fx(0); obj* fx1 = fx(1); obj* fx2 = fx(2); obj* fx3 = fx(3); obj* fx4 = fx(4); obj* fx5 = fx(5); obj* fx6 = fx(6); obj* fx7 = fx(7); fn10 fn = FN10(f); lean_free_object(f); return fn(fx0, fx1, fx2, fx3, fx4, fx5, fx6, fx7, a1, a2); }
    case 11: { obj* fx0 = fx(0); obj* fx1 = fx(1); obj* fx2 = fx(2); obj* fx3 = fx(3); obj* fx4 = fx(4); obj* fx5 = fx(5); obj* fx6 = fx(6); obj* fx7 = fx(7); obj* fx8 = fx(8); fn11 fn = FN11(f); lean_free_object(f); return fn(fx0, fx1, fx2, fx3, fx4, fx5, fx6, fx7, fx8, a1, a2); }
    case 12: { obj* fx0 = fx(0); obj* fx1 = fx(1); obj* fx2 = fx(2); obj* fx3 = fx(3); obj* fx4 = fx(4); obj* fx5 = fx(5); obj* fx6 = fx(6); obj* fx7 = fx(7); obj* fx8 = fx(8); obj* fx9 = fx(9); fn12 fn = FN12(f); lean_free_object(f); return fn(fx0, fx1, fx2, fx3, fx4, fx5, fx6, fx7, fx8, fx9, a1, a2); }
    case 13: { obj* fx0 = fx(0); obj* fx1 = fx(1); obj* fx2 = fx(2); obj* fx3 = fx(3); obj* fx4 = fx(4); obj* fx5 = fx(5); obj* fx6 = fx(6); obj* fx7 = fx(7); obj* fx8 = fx(8); obj* fx9 = fx(9); obj* fx10 = fx(10); fn13 fn = FN13(f); lean_free_object(f); return fn(fx0, fx1, fx2, fx3, fx4, fx5, fx6, fx7, fx8, fx9, fx10, a1, a2); }
    case 14: { obj* fx0 = fx(0); obj* fx1 = fx(1); obj* fx2 = fx(2); obj* fx3 = fx(3); obj* fx4 = fx(4); obj* fx5 = fx(5); obj* fx6 = fx(6); obj* fx7 = fx(7); obj* fx8 = fx(8); obj* fx9 = fx(9); obj* fx10 = fx(10); obj* fx11 = fx(11); fn14 fn = FN14(f); lean_free_object(f); return fn(fx0, fx1, fx2, fx3, fx4, fx5, fx6, fx7, fx8, fx9, fx10, fx11, a1, a2); }
    case 15: { obj* fx0 = fx(0); obj* fx1 = fx(1); obj* fx2 = fx(2); obj* fx3 = fx(3); obj* fx4 = fx(4); obj* fx5 = fx(5); obj* fx6 = fx(6); obj* fx7 = fx(7); obj* fx8 = fx(8); obj* fx9 = fx(9); obj* fx10 = fx(10); obj* fx11 = fx(11); obj* fx12 = fx(12); fn15 fn = FN15(f); lean_free_object(f); return fn(fx0, fx1, fx2, fx3, fx4, fx5, fx6, fx7, fx8, fx9, fx10, fx11, fx12, a1, a2); }
    case 16: { obj* fx0 = fx(0); obj* fx1 = fx(1); obj* fx2 = fx(2); obj* fx3 = fx(3); obj* fx4 = fx(4); obj* fx5 = fx(5); obj* fx6 = fx(6); obj* fx7 = fx(7); obj* fx8 = fx(8); obj* fx9 = fx(9); obj* fx10 = fx(10); obj* fx11 = fx(11); obj* fx12 = fx(12); obj* fx13 = fx(13); fn16 fn = FN16(f); lean_free_object(f); return fn(fx0, fx1, fx2, fx3, fx4, fx5, fx6, fx7, fx8, fx9, fx10, fx11, fx12, fx13, a1, a2); }
    }
  }
  switch (arity) {
  case 2: { fn2 fn = FN2(f); lean_dec_ref(f); return fn(a1, a2); }
  case 3: { obj* fx0 = fx(0); lean_inc(fx0); fn3 fn = FN3(f); lean_dec_ref(f); return fn(fx0, a1, a2); }
  case 4: { obj* fx0 = fx(0); obj* fx1 = fx(1); lean_inc(fx0); lean_inc(fx1); fn4 fn = FN4(f); lean_dec_ref(f); return fn(fx0, fx1, a1, a2); }
  case 5: { obj* fx0 = fx(0); obj* fx1 = fx(1); obj* fx2 = fx(2); lean_inc(fx0); lean_inc(fx1); lean_inc(fx2); fn5 fn = FN5(f); lean_dec_ref(f); return fn(fx0, fx1, fx2, a1, a2); }
  case 6: { obj* fx0 = fx(0); obj* fx1 = fx(1); obj* fx2 = fx(2); obj* fx3 = fx(3); lean_inc(fx0); lean_inc(fx1); lean_inc(fx2); lean_inc(fx3); fn6 fn = FN6(f); lean_dec_ref(f); return fn(fx0, fx1, fx2, fx3, a1, a2); }
  case 7: { obj* fx0 = fx(0); obj* fx1 = fx(1); obj* fx2 = fx(2); obj* fx3 = fx(3); obj* fx4 = fx(4); lean_inc(fx0); lean_inc(fx1); lean_inc(fx2); lean_inc(fx3); lean_inc(fx4); fn7 fn = FN7(f); lean_dec_ref(f); return fn(fx0, fx1, fx2, fx3, fx4, a1, a2); }
  case 8: { obj* fx0 = fx(0); obj* fx1 = fx(1); obj* fx2 = fx(2); obj* fx3 = fx(3); obj* fx4 = fx(4); obj* fx5 = fx(5); lean_inc(fx0); lean_inc(fx1); lean_inc(fx2); lean_inc(fx3); lean_inc(fx4); lean_inc(fx5); fn8 fn = FN8(f); lean_dec_ref(f); return fn(fx0, fx1, fx2, fx3, fx4, fx5, a1, a2); }
  case 9: { obj* fx0 = fx(0); obj* fx1 = fx(1); obj* fx2 = fx(2); obj* fx3 = fx(3); obj* fx4 = fx(4); obj* fx5 = fx(5); obj* fx6 = fx(6); lean_inc(fx0); lean_inc(fx1); lean_inc(fx2); lean_inc(fx3); lean_inc(fx4); lean_inc(fx5); lean_inc(fx6); fn9 fn = FN9(f); lean_dec_ref(f); return fn(fx0, fx1, fx2, fx3, fx4, fx5, fx6, a1, a2); }
  case 10: { obj* fx0 = fx(0); obj* fx1 = fx(1); obj* fx2 = fx(2); obj* fx3 = fx(3); obj* fx4 = fx(4); obj* fx5 = fx(5); obj* fx6 = fx(6); obj* fx7 = fx(7); lean_inc(fx0); lean_inc(fx1); lean_inc(fx2); lean_inc(fx3); lean_inc(fx4); lean_inc(fx5); lean_inc(fx6); lean_inc(fx7); fn10 fn = FN10(f); lean_dec_ref(f); return fn(fx0, fx1, fx2, fx3, fx4, fx5, fx6, fx7, a1, a2); }
  case 11: { obj* fx0 = fx(0); obj* fx1 = fx(1); obj* fx2 = fx(2); obj* fx3 = fx(3); obj* fx4 = fx(4); obj* fx5 = fx(5); obj* fx6 = fx(6); obj* fx7 = fx(7); obj* fx8 = fx(8); lean_inc(fx0); lean_inc(fx1); lean_inc(fx2); lean_inc(fx3); lean_inc(fx4); lean_inc(fx5); lean_inc(fx6); lean_inc(fx7); lean_inc(fx8); fn11 fn = FN11(f); lean_dec_ref(f); return fn(fx0, fx1, fx2, fx3, fx4, fx5, fx6, fx7, fx8, a1, a2); }
  case 12: { obj* fx0 = fx(0); obj* fx1 = fx(1); obj* fx2 = fx(2); obj* fx3 = fx(3); obj* fx4 = fx(4); obj* fx5 = fx(5); obj* fx6 = fx(6); obj* fx7 = fx(7); obj* fx8 = fx(8); obj* fx9 = fx(9); lean_inc(fx0); lean_inc(fx1); lean_inc(fx2); lean_inc(fx3); lean_inc(fx4); lean_inc(fx5); lean_inc(fx6); lean_inc(fx7); lean_inc(fx8); lean_inc(fx9); fn12 fn = FN12(f); lean_dec_ref(f); return fn(fx0, fx1, fx2, fx3, fx4, fx5, fx6, fx7, fx8, fx9, a1, a2); }
  case 13: { obj* fx0 = fx(0); obj* fx1 = fx(1); obj* fx2 = fx(2); obj* fx3 = fx(3); obj* fx4 = fx(4); obj* fx5 = fx(5); obj* fx6 = fx(6); obj* fx7 = fx(7); obj* fx8 = fx(8); obj* fx9 = fx(9); obj* fx10 = fx(10); lean_inc(fx0); lean_inc(fx1); lean_inc(fx2); lean_inc(fx3); lean_inc(fx4); lean_inc(fx5); lean_inc(fx6); lean_inc(fx7); lean_inc(fx8); lean_inc(fx9); lean_inc(fx10); fn13 fn = FN13(f); lean_dec_ref(f); return fn(fx0, fx1, fx2, fx3, fx4, fx5, fx6, fx7, fx8, fx9, fx10, a1, a2); }
  case 14: { obj* fx0 = fx(0); obj* fx1 = fx(1); obj* fx2 = fx(2); obj* fx3 = fx(3); obj* fx4 = fx(4); obj* fx5 = fx(5); obj* fx6 = fx(6); obj* fx7 = fx(7); obj* fx8 = fx(8); obj* fx9 = fx(9); obj* fx10 = fx(10); obj* fx11 = fx(11); lean_inc(fx0); lean_inc(fx1); lean_inc(fx2); lean_inc(fx3); lean_inc(fx4); lean_inc(fx5); lean_inc(fx6); lean_inc(fx7); lean_inc(fx8); lean_inc(fx9); lean_inc(fx10); lean_inc(fx11); fn14 fn = FN14(f); lean_dec_ref(f); return fn(fx0, fx1, fx2, fx3, fx4, fx5, fx6, fx7, fx8, fx9, fx10, fx11, a1, a2); }
  case 15: { obj* fx0 = fx(0); obj* fx1 = fx(1); obj* fx2 = fx(2); obj* fx3 = fx(3); obj* fx4 = fx(4); obj* fx5 = fx(5); obj* fx6 = fx(6); obj* fx7 = fx(7); obj* fx8 = fx(8); obj* fx9 = fx(9); obj* fx10 = fx(10); obj* fx11 = fx(11); obj* fx12 = fx(12); lean_inc(fx0); lean_inc(fx1); lean_inc(fx2); lean_inc(fx3); lean_inc(fx4); lean_inc(fx5); lean_inc(fx6); lean_inc(fx7); lean_inc(fx8); lean_inc(fx9); lean_inc(fx10); lean_inc(fx11); lean_inc(fx12); fn15 fn = FN15(f); lean_dec_ref(f); return fn(fx0, fx1, fx2, fx3, fx4, fx5, fx6, fx7, fx8, fx9, fx10, fx11, fx12, a1, a2); }
  case 16: { obj* fx0 = fx(0); obj* fx1 = fx(1); obj* fx2 = fx(2); obj* fx3 = fx(3); obj* fx4 = fx(4); obj* fx5 = fx(5); obj* fx6 = fx(6); obj* fx7 = fx(7); obj* fx8 = fx(8); obj* fx9 = fx(9); obj* fx10 = fx(10); obj* fx11 = fx(11); obj* fx12 = fx(12); obj* fx13 = fx(13); lean_inc(fx0); lean_inc(fx1); lean_inc(fx2); lean_inc(fx3); lean_inc(fx4); lean_inc(fx5); lean_inc(fx6); lean_inc(fx7); lean_inc(fx8); lean_inc(fx9); lean_inc(fx10); lean_inc(fx11); lean_inc(fx12); lean_inc(fx13); fn16 fn = FN16(f); lean_dec_ref(f); return fn(fx0, fx1, fx2, fx3, fx4, fx5, fx6, fx7, fx8, fx9, fx10, fx11, fx12, fx13, a1, a2); }
  default:
    lean_assert(arity > 16);
    obj * as[2] = { a1, a2 };
    obj ** args = static_cast<obj**>(LEAN_ALLOCA(arity*sizeof(obj*))); // NOLINT
    for (unsigned i = 0; i < fixed; i++) { lean_inc(fx(i)); args[i] = fx(i); }
    for (unsigned i = 0; i < 2; i++) args[fixed+i] = as[i];
    fnn fn = FNN(f);
    lean_dec_ref(f);
    return fn(args);
  }
} else if (arity < fixed + 2) {
  obj * as[2] = { a1, a2 };
  obj ** args = static_cast<obj**>(LEAN_ALLOCA(arity*sizeof(obj*))); // NOLINT
  for (unsigned i = 0; i < fixed; i++) { lean_inc(fx(i)); args[i] = fx(i); }
  for (unsigned i = 0; i < arity-fixed; i++) args[fixed+i] = as[i];
  obj * new_f = curry(f, arity, args);
  lean_dec_ref(f);
  return lean_apply_n(new_f, 2+fixed-arity, &as[arity-fixed]);
} else {
  return fix_args(f, {a1, a2});
}
}
extern "C" LEAN_EXPORT obj* lean_apply_3(obj* f, obj* a1, obj* a2, obj* a3) {
if (lean_is_scalar(f)) { lean_dec(a1); lean_dec(a2); lean_dec(a3); return f; } // f is an erased proof
unsigned arity = lean_closure_arity(f);
unsigned fixed = lean_closure_num_fixed(f);
if (arity == fixed + 3) {
  if (lean_is_exclusive(f)) {
    switch (arity) {
    case 3: { fn3 fn = FN3(f); lean_free_object(f); return fn(a1, a2, a3); }
    case 4: { obj* fx0 = fx(0); fn4 fn = FN4(f); lean_free_object(f); return fn(fx0, a1, a2, a3); }
    case 5: { obj* fx0 = fx(0); obj* fx1 = fx(1); fn5 fn = FN5(f); lean_free_object(f); return fn(fx0, fx1, a1, a2, a3); }
    case 6: { obj* fx0 = fx(0); obj* fx1 = fx(1); obj* fx2 = fx(2); fn6 fn = FN6(f); lean_free_object(f); return fn(fx0, fx1, fx2, a1, a2, a3); }
    case 7: { obj* fx0 = fx(0); obj* fx1 = fx(1); obj* fx2 = fx(2); obj* fx3 = fx(3); fn7 fn = FN7(f); lean_free_object(f); return fn(fx0, fx1, fx2, fx3, a1, a2, a3); }
    case 8: { obj* fx0 = fx(0); obj* fx1 = fx(1); obj* fx2 = fx(2); obj* fx3 = fx(3); obj* fx4 = fx(4); fn8 fn = FN8(f); lean_free_object(f); return fn(fx0, fx1, fx2, fx3, fx4, a1, a2, a3); }
    case 9: { obj* fx0 = fx(0); obj* fx1 = fx(1); obj* fx2 = fx(2); obj* fx3 = fx(3); obj* fx4 = fx(4); obj* fx5 = fx(5); fn9 fn = FN9(f); lean_free_object(f); return fn(fx0, fx1, fx2, fx3, fx4, fx5, a1, a2, a3); }
    case 10: { obj* fx0 = fx(0); obj* fx1 = fx(1); obj* fx2 = fx(2); obj* fx3 = fx(3); obj* fx4 = fx(4); obj* fx5 = fx(5); obj* fx6 = fx(6); fn10 fn = FN10(f); lean_free_object(f); return fn(fx0, fx1, fx2, fx3, fx4, fx5, fx6, a1, a2, a3); }
    case 11: { obj* fx0 = fx(0); obj* fx1 = fx(1); obj* fx2 = fx(2); obj* fx3 = fx(3); obj* fx4 = fx(4); obj* fx5 = fx(5); obj* fx6 = fx(6); obj* fx7 = fx(7); fn11 fn = FN11(f); lean_free_object(f); return fn(fx0, fx1, fx2, fx3, fx4, fx5, fx6, fx7, a1, a2, a3); }
    case 12: { obj* fx0 = fx(0); obj* fx1 = fx(1); obj* fx2 = fx(2); obj* fx3 = fx(3); obj* fx4 = fx(4); obj* fx5 = fx(5); obj* fx6 = fx(6); obj* fx7 = fx(7); obj* fx8 = fx(8); fn12 fn = FN12(f); lean_free_object(f); return fn(fx0, fx1, fx2, fx3, fx4, fx5, fx6, fx7, fx8, a1, a2, a3); }
    case 13: { obj* fx0 = fx(0); obj* fx1 = fx(1); obj* fx2 = fx(2); obj* fx3 = fx(3); obj* fx4 = fx(4); obj* fx5 = fx(5); obj* fx6 = fx(6); obj* fx7 = fx(7); obj* fx8 = fx(8); obj* fx9 = fx(9); fn13 fn = FN13(f); lean_free_object(f); return fn(fx0, fx1, fx2, fx3, fx4, fx5, fx6, fx7, fx8, fx9, a1, a2, a3); }
    case 14: { obj* fx0 = fx(0); obj* fx1 = fx(1); obj* fx2 = fx(2); obj* fx3 = fx(3); obj* fx4 = fx(4); obj* fx5 = fx(5); obj* fx6 = fx(6); obj* fx7 = fx(7); obj* fx8 = fx(8); obj* fx9 = fx(9); obj* fx10 = fx(10); fn14 fn = FN14(f); lean_free_object(f); return fn(fx0, fx1, fx2, fx3, fx4, fx5, fx6, fx7, fx8, fx9, fx10, a1, a2, a3); }
    case 15: { obj* fx0 = fx(0); obj* fx1 = fx(1); obj* fx2 = fx(2); obj* fx3 = fx(3); obj* fx4 = fx(4); obj* fx5 = fx(5); obj* fx6 = fx(6); obj* fx7 = fx(7); obj* fx8 = fx(8); obj* fx9 = fx(9); obj* fx10 = fx(10); obj* fx11 = fx(11); fn15 fn = FN15(f); lean_free_object(f); return fn(fx0, fx1, fx2, fx3, fx4, fx5, fx6, fx7, fx8, fx9, fx10, fx11, a1, a2, a3); }
    case 16: { obj* fx0 = fx(0); obj* fx1 = fx(1); obj* fx2 = fx(2); obj* fx3 = fx(3); obj* fx4 = fx(4); obj* fx5 = fx(5); obj* fx6 = fx(6); obj* fx7 = fx(7); obj* fx8 = fx(8); obj* fx9 = fx(9); obj* fx10 = fx(10); obj* fx11 = fx(11); obj* fx12 = fx(12); fn16 fn = FN16(f); lean_free_object(f); return fn(fx0, fx1, fx2, fx3, fx4, fx5, fx6, fx7, fx8, fx9, fx10, fx11, fx12, a1, a2, a3); }
    }
  }
  switch (arity) {
  case 3: { fn3 fn = FN3(f); lean_dec_ref(f); return fn(a1, a2, a3); }
  case 4: { obj* fx0 = fx(0); lean_inc(fx0); fn4 fn = FN4(f); lean_dec_ref(f); return fn(fx0, a1, a2, a3); }
  case 5: { obj* fx0 = fx(0); obj* fx1 = fx(1); lean_inc(fx0); lean_inc(fx1); fn5 fn = FN5(f); lean_dec_ref(f); return fn(fx0, fx1, a1, a2, a3); }
  case 6: { obj* fx0 = fx(0); obj* fx1 = fx(1); obj* fx2 = fx(2); lean_inc(fx0); lean_inc(fx1); lean_inc(fx2); fn6 fn = FN6(f); lean_dec_ref(f); return fn(fx0, fx1, fx2, a1, a2, a3); }
  case 7: { obj* fx0 = fx(0); obj* fx1 = fx(1); obj* fx2 = fx(2); obj* fx3 = fx(3); lean_inc(fx0); lean_inc(fx1); lean_inc(fx2); lean_inc(fx3); fn7 fn = FN7(f); lean_dec_ref(f); return fn(fx0, fx1, fx2, fx3, a1, a2, a3); }
  case 8: { obj* fx0 = fx(0); obj* fx1 = fx(1); obj* fx2 = fx(2); obj* fx3 = fx(3); obj* fx4 = fx(4); lean_inc(fx0); lean_inc(fx1); lean_inc(fx2); lean_inc(fx3); lean_inc(fx4); fn8 fn = FN8(f); lean_dec_ref(f); return fn(fx0, fx1, fx2, fx3, fx4, a1, a2, a3); }
  case 9: { obj* fx0 = fx(0); obj* fx1 = fx(1); obj* fx2 = fx(2); obj* fx3 = fx(3); obj* fx4 = fx(4); obj* fx5 = fx(5); lean_inc(fx0); lean_inc(fx1); lean_inc(fx2); lean_inc(fx3); lean_inc(fx4); lean_inc(fx5); fn9 fn = FN9(f); lean_dec_ref(f); return fn(fx0, fx1, fx2, fx3, fx4, fx5, a1, a2, a3); }
  case 10: { obj* fx0 = fx(0); obj* fx1 = fx(1); obj* fx2 = fx(2); obj* fx3 = fx(3); obj* fx4 = fx(4); obj* fx5 = fx(5); obj* fx6 = fx(6); lean_inc(fx0); lean_inc(fx1); lean_inc(fx2); lean_inc(fx3); lean_inc(fx4); lean_inc(fx5); lean_inc(fx6); fn10 fn = FN10(f); lean_dec_ref(f); return fn(fx0, fx1, fx2, fx3, fx4, fx5, fx6, a1, a2, a3); }
  case 11: { obj* fx0 = fx(0); obj* fx1 = fx(1); obj* fx2 = fx(2); obj* fx3 = fx(3); obj* fx4 = fx(4); obj* fx5 = fx(5); obj* fx6 = fx(6); obj* fx7 = fx(7); lean_inc(fx0); lean_inc(fx1); lean_inc(fx2); lean_inc(fx3); lean_inc(fx4); lean_inc(fx5); lean_inc(fx6); lean_inc(fx7); fn11 fn = FN11(f); lean_dec_ref(f); return fn(fx0, fx1, fx2, fx3, fx4, fx5, fx6, fx7, a1, a2, a3); }
  case 12: { obj* fx0 = fx(0); obj* fx1 = fx(1); obj* fx2 = fx(2); obj* fx3 = fx(3); obj* fx4 = fx(4); obj* fx5 = fx(5); obj* fx6 = fx(6); obj* fx7 = fx(7); obj* fx8 = fx(8); lean_inc(fx0); lean_inc(fx1); lean_inc(fx2); lean_inc(fx3); lean_inc(fx4); lean_inc(fx5); lean_inc(fx6); lean_inc(fx7); lean_inc(fx8); fn12 fn = FN12(f); lean_dec_ref(f); return fn(fx0, fx1, fx2, fx3, fx4, fx5, fx6, fx7, fx8, a1, a2, a3); }
  case 13: { obj* fx0 = fx(0); obj* fx1 = fx(1); obj* fx2 = fx(2); obj* fx3 = fx(3); obj* fx4 = fx(4); obj* fx5 = fx(5); obj* fx6 = fx(6); obj* fx7 = fx(7); obj* fx8 = fx(8); obj* fx9 = fx(9); lean_inc(fx0); lean_inc(fx1); lean_inc(fx2); lean_inc(fx3); lean_inc(fx4); lean_inc(fx5); lean_inc(fx6); lean_inc(fx7); lean_inc(fx8); lean_inc(fx9); fn13 fn = FN13(f); lean_dec_ref(f); return fn(fx0, fx1, fx2, fx3, fx4, fx5, fx6, fx7, fx8, fx9, a1, a2, a3); }
  case 14: { obj* fx0 = fx(0); obj* fx1 = fx(1); obj* fx2 = fx(2); obj* fx3 = fx(3); obj* fx4 = fx(4); obj* fx5 = fx(5); obj* fx6 = fx(6); obj* fx7 = fx(7); obj* fx8 = fx(8); obj* fx9 = fx(9); obj* fx10 = fx(10); lean_inc(fx0); lean_inc(fx1); lean_inc(fx2); lean_inc(fx3); lean_inc(fx4); lean_inc(fx5); lean_inc(fx6); lean_inc(fx7); lean_inc(fx8); lean_inc(fx9); lean_inc(fx10); fn14 fn = FN14(f); lean_dec_ref(f); return fn(fx0, fx1, fx2, fx3, fx4, fx5, fx6, fx7, fx8, fx9, fx10, a1, a2, a3); }
  case 15: { obj* fx0 = fx(0); obj* fx1 = fx(1); obj* fx2 = fx(2); obj* fx3 = fx(3); obj* fx4 = fx(4); obj* fx5 = fx(5); obj* fx6 = fx(6); obj* fx7 = fx(7); obj* fx8 = fx(8); obj* fx9 = fx(9); obj* fx10 = fx(10); obj* fx11 = fx(11); lean_inc(fx0); lean_inc(fx1); lean_inc(fx2); lean_inc(fx3); lean_inc(fx4); lean_inc(fx5); lean_inc(fx6); lean_inc(fx7); lean_inc(fx8); lean_inc(fx9); lean_inc(fx10); lean_inc(fx11); fn15 fn = FN15(f); lean_dec_ref(f); return fn(fx0, fx1, fx2, fx3, fx4, fx5, fx6, fx7, fx8, fx9, fx10, fx11, a1, a2, a3); }
  case 16: { obj* fx0 = fx(0); obj* fx1 = fx(1); obj* fx2 = fx(2); obj* fx3 = fx(3); obj* fx4 = fx(4); obj* fx5 = fx(5); obj* fx6 = fx(6); obj* fx7 = fx(7); obj* fx8 = fx(8); obj* fx9 = fx(9); obj* fx10 = fx(10); obj* fx11 = fx(11); obj* fx12 = fx(12); lean_inc(fx0); lean_inc(fx1); lean_inc(fx2); lean_inc(fx3); lean_inc(fx4); lean_inc(fx5); lean_inc(fx6); lean_inc(fx7); lean_inc(fx8); lean_inc(fx9); lean_inc(fx10); lean_inc(fx11); lean_inc(fx12); fn16 fn = FN16(f); lean_dec_ref(f); return fn(fx0, fx1, fx2, fx3, fx4, fx5, fx6, fx7, fx8, fx9, fx10, fx11, fx12, a1, a2, a3); }
  default:
    lean_assert(arity > 16);
    obj * as[3] = { a1, a2, a3 };
    obj ** args = static_cast<obj**>(LEAN_ALLOCA(arity*sizeof(obj*))); // NOLINT
    for (unsigned i = 0; i < fixed; i++) { lean_inc(fx(i)); args[i] = fx(i); }
    for (unsigned i = 0; i < 3; i++) args[fixed+i] = as[i];
    fnn fn = FNN(f);
    lean_dec_ref(f);
    return fn(args);
  }
} else if (arity < fixed + 3) {
  obj * as[3] = { a1, a2, a3 };
  obj ** args = static_cast<obj**>(LEAN_ALLOCA(arity*sizeof(obj*))); // NOLINT
  for (unsigned i = 0; i < fixed; i++) { lean_inc(fx(i)); args[i] = fx(i); }
  for (unsigned i = 0; i < arity-fixed; i++) args[fixed+i] = as[i];
  obj * new_f = curry(f, arity, args);
  lean_dec_ref(f);
  return lean_apply_n(new_f, 3+fixed-arity, &as[arity-fixed]);
} else {
  return fix_args(f, {a1, a2, a3});
}
}
extern "C" LEAN_EXPORT obj* lean_apply_4(obj* f, obj* a1, obj* a2, obj* a3, obj* a4) {
if (lean_is_scalar(f)) { lean_dec(a1); lean_dec(a2); lean_dec(a3); lean_dec(a4); return f; } // f is an erased proof
unsigned arity = lean_closure_arity(f);
unsigned fixed = lean_closure_num_fixed(f);
if (arity == fixed + 4) {
  if (lean_is_exclusive(f)) {
    switch (arity) {
    case 4: { fn4 fn = FN4(f); lean_free_object(f); return fn(a1, a2, a3, a4); }
    case 5: { obj* fx0 = fx(0); fn5 fn = FN5(f); lean_free_object(f); return fn(fx0, a1, a2, a3, a4); }
    case 6: { obj* fx0 = fx(0); obj* fx1 = fx(1); fn6 fn = FN6(f); lean_free_object(f); return fn(fx0, fx1, a1, a2, a3, a4); }
    case 7: { obj* fx0 = fx(0); obj* fx1 = fx(1); obj* fx2 = fx(2); fn7 fn = FN7(f); lean_free_object(f); return fn(fx0, fx1, fx2, a1, a2, a3, a4); }
    case 8: { obj* fx0 = fx(0); obj* fx1 = fx(1); obj* fx2 = fx(2); obj* fx3 = fx(3); fn8 fn = FN8(f); lean_free_object(f); return fn(fx0, fx1, fx2, fx3, a1, a2, a3, a4); }
    case 9: { obj* fx0 = fx(0); obj* fx1 = fx(1); obj* fx2 = fx(2); obj* fx3 = fx(3); obj* fx4 = fx(4); fn9 fn = FN9(f); lean_free_object(f); return fn(fx0, fx1, fx2, fx3, fx4, a1, a2, a3, a4); }
    case 10: { obj* fx0 = fx(0); obj* fx1 = fx(1); obj* fx2 = fx(2); obj* fx3 = fx(3); obj* fx4 = fx(4); obj* fx5 = fx(5); fn10 fn = FN10(f); lean_free_object(f); return fn(fx0, fx1, fx2, fx3, fx4, fx5, a1, a2, a3, a4); }
    case 11: { obj* fx0 = fx(0); obj* fx1 = fx(1); obj* fx2 = fx(2); obj* fx3 = fx(3); obj* fx4 = fx(4); obj* fx5 = fx(5); obj* fx6 = fx(6); fn11 fn = FN11(f); lean_free_object(f); return fn(fx0, fx1, fx2, fx3, fx4, fx5, fx6, a1, a2, a3, a4); }
    case 12: { obj* fx0 = fx(0); obj* fx1 = fx(1); obj* fx2 = fx(2); obj* fx3 = fx(3); obj* fx4 = fx(4); obj* fx5 = fx(5); obj* fx6 = fx(6); obj* fx7 = fx(7); fn12 fn = FN12(f); lean_free_object(f); return fn(fx0, fx1, fx2, fx3, fx4, fx5, fx6, fx7, a1, a2, a3, a4); }
    case 13: { obj* fx0 = fx(0); obj* fx1 = fx(1); obj* fx2 = fx(2); obj* fx3 = fx(3); obj* fx4 = fx(4); obj* fx5 = fx(5); obj* fx6 = fx(6); obj* fx7 = fx(7); obj* fx8 = fx(8); fn13 fn = FN13(f); lean_free_object(f); return fn(fx0, fx1, fx2, fx3, fx4, fx5, fx6, fx7, fx8, a1, a2, a3, a4); }
    case 14: { obj* fx0 = fx(0); obj* fx1 = fx(1); obj* fx2 = fx(2); obj* fx3 = fx(3); obj* fx4 = fx(4); obj* fx5 = fx(5); obj* fx6 = fx(6); obj* fx7 = fx(7); obj* fx8 = fx(8); obj* fx9 = fx(9); fn14 fn = FN14(f); lean_free_object(f); return fn(fx0, fx1, fx2, fx3, fx4, fx5, fx6, fx7, fx8, fx9, a1, a2, a3, a4); }
    case 15: { obj* fx0 = fx(0); obj* fx1 = fx(1); obj* fx2 = fx(2); obj* fx3 = fx(3); obj* fx4 = fx(4); obj* fx5 = fx(5); obj* fx6 = fx(6); obj* fx7 = fx(7); obj* fx8 = fx(8); obj* fx9 = fx(9); obj* fx10 = fx(10); fn15 fn = FN15(f); lean_free_object(f); return fn(fx0, fx1, fx2, fx3, fx4, fx5, fx6, fx7, fx8, fx9, fx10, a1, a2, a3, a4); }
    case 16: { obj* fx0 = fx(0); obj* fx1 = fx(1); obj* fx2 = fx(2); obj* fx3 = fx(3); obj* fx4 = fx(4); obj* fx5 = fx(5); obj* fx6 = fx(6); obj* fx7 = fx(7); obj* fx8 = fx(8); obj* fx9 = fx(9); obj* fx10 = fx(10); obj* fx11 = fx(11); fn16 fn = FN16(f); lean_free_object(f); return fn(fx0, fx1, fx2, fx3, fx4, fx5, fx6, fx7, fx8, fx9, fx10, fx11, a1, a2, a3, a4); }
    }
  }
  switch (arity) {
  case 4: { fn4 fn = FN4(f); lean_dec_ref(f); return fn(a1, a2, a3, a4); }
  case 5: { obj* fx0 = fx(0); lean_inc(fx0); fn5 fn = FN5(f); lean_dec_ref(f); return fn(fx0, a1, a2, a3, a4); }
  case 6: { obj* fx0 = fx(0); obj* fx1 = fx(1); lean_inc(fx0); lean_inc(fx1); fn6 fn = FN6(f); lean_dec_ref(f); return fn(fx0, fx1, a1, a2, a3, a4); }
  case 7: { obj* fx0 = fx(0); obj* fx1 = fx(1); obj* fx2 = fx(2); lean_inc(fx0); lean_inc(fx1); lean_inc(fx2); fn7 fn = FN7(f); lean_dec_ref(f); return fn(fx0, fx1, fx2, a1, a2, a3, a4); }
  case 8: { obj* fx0 = fx(0); obj* fx1 = fx(1); obj* fx2 = fx(2); obj* fx3 = fx(3); lean_inc(fx0); lean_inc(fx1); lean_inc(fx2); lean_inc(fx3); fn8 fn = FN8(f); lean_dec_ref(f); return fn(fx0, fx1, fx2, fx3, a1, a2, a3, a4); }
  case 9: { obj* fx0 = fx(0); obj* fx1 = fx(1); obj* fx2 = fx(2); obj* fx3 = fx(3); obj* fx4 = fx(4); lean_inc(fx0); lean_inc(fx1); lean_inc(fx2); lean_inc(fx3); lean_inc(fx4); fn9 fn = FN9(f); lean_dec_ref(f); return fn(fx0, fx1, fx2, fx3, fx4, a1, a2, a3, a4); }
  case 10: { obj* fx0 = fx(0); obj* fx1 = fx(1); obj* fx2 = fx(2); obj* fx3 = fx(3); obj* fx4 = fx(4); obj* fx5 = fx(5); lean_inc(fx0); lean_inc(fx1); lean_inc(fx2); lean_inc(fx3); lean_inc(fx4); lean_inc(fx5); fn10 fn = FN10(f); lean_dec_ref(f); return fn(fx0, fx1, fx2, fx3, fx4, fx5, a1, a2, a3, a4); }
  case 11: { obj* fx0 = fx(0); obj* fx1 = fx(1); obj* fx2 = fx(2); obj* fx3 = fx(3); obj* fx4 = fx(4); obj* fx5 = fx(5); obj* fx6 = fx(6); lean_inc(fx0); lean_inc(fx1); lean_inc(fx2); lean_inc(fx3); lean_inc(fx4); lean_inc(fx5); lean_inc(fx6); fn11 fn = FN11(f); lean_dec_ref(f); return fn(fx0, fx1, fx2, fx3, fx4, fx5, fx6, a1, a2, a3, a4); }
  case 12: { obj* fx0 = fx(0); obj* fx1 = fx(1); obj* fx2 = fx(2); obj* fx3 = fx(3); obj* fx4 = fx(4); obj* fx5 = fx(5); obj* fx6 = fx(6); obj* fx7 = fx(7); lean_inc(fx0); lean_inc(fx1); lean_inc(fx2); lean_inc(fx3); lean_inc(fx4); lean_inc(fx5); lean_inc(fx6); lean_inc(fx7); fn12 fn = FN12(f); lean_dec_ref(f); return fn(fx0, fx1, fx2, fx3, fx4, fx5, fx6, fx7, a1, a2, a3, a4); }
  case 13: { obj* fx0 = fx(0); obj* fx1 = fx(1); obj* fx2 = fx(2); obj* fx3 = fx(3); obj* fx4 = fx(4); obj* fx5 = fx(5); obj* fx6 = fx(6); obj* fx7 = fx(7); obj* fx8 = fx(8); lean_inc(fx0); lean_inc(fx1); lean_inc(fx2); lean_inc(fx3); lean_inc(fx4); lean_inc(fx5); lean_inc(fx6); lean_inc(fx7); lean_inc(fx8); fn13 fn = FN13(f); lean_dec_ref(f); return fn(fx0, fx1, fx2, fx3, fx4, fx5, fx6, fx7, fx8, a1, a2, a3, a4); }
  case 14: { obj* fx0 = fx(0); obj* fx1 = fx(1); obj* fx2 = fx(2); obj* fx3 = fx(3); obj* fx4 = fx(4); obj* fx5 = fx(5); obj* fx6 = fx(6); obj* fx7 = fx(7); obj* fx8 = fx(8); obj* fx9 = fx(9); lean_inc(fx0); lean_inc(fx1); lean_inc(fx2); lean_inc(fx3); lean_inc(fx4); lean_inc(fx5); lean_inc(fx6); lean_inc(fx7); lean_inc(fx8); lean_inc(fx9); fn14 fn = FN14(f); lean_dec_ref(f); return fn(fx0, fx1, fx2, fx3, fx4, fx5, fx6, fx7, fx8, fx9, a1, a2, a3, a4); }
  case 15: { obj* fx0 = fx(0); obj* fx1 = fx(1); obj* fx2 = fx(2); obj* fx3 = fx(3); obj* fx4 = fx(4); obj* fx5 = fx(5); obj* fx6 = fx(6); obj* fx7 = fx(7); obj* fx8 = fx(8); obj* fx9 = fx(9); obj* fx10 = fx(10); lean_inc(fx0); lean_inc(fx1); lean_inc(fx2); lean_inc(fx3); lean_inc(fx4); lean_inc(fx5); lean_inc(fx6); lean_inc(fx7); lean_inc(fx8); lean_inc(fx9); lean_inc(fx10); fn15 fn = FN15(f); lean_dec_ref(f); return fn(fx0, fx1, fx2, fx3, fx4, fx5, fx6, fx7, fx8, fx9, fx10, a1, a2, a3, a4); }
  case 16: { obj* fx0 = fx(0); obj* fx1 = fx(1); obj* fx2 = fx(2); obj* fx3 = fx(3); obj* fx4 = fx(4); obj* fx5 = fx(5); obj* fx6 = fx(6); obj* fx7 = fx(7); obj* fx8 = fx(8); obj* fx9 = fx(9); obj* fx10 = fx(10); obj* fx11 = fx(11); lean_inc(fx0); lean_inc(fx1); lean_inc(fx2); lean_inc(fx3); lean_inc(fx4); lean_inc(fx5); lean_inc(fx6); lean_inc(fx7); lean_inc(fx8); lean_inc(fx9); lean_inc(fx10); lean_inc(fx11); fn16 fn = FN16(f); lean_dec_ref(f); return fn(fx0, fx1, fx2, fx3, fx4, fx5, fx6, fx7, fx8, fx9, fx10, fx11, a1, a2, a3, a4); }
  default:
    lean_assert(arity > 16);
    obj * as[4] = { a1, a2, a3, a4 };
    obj ** args = static_cast<obj**>(LEAN_ALLOCA(arity*sizeof(obj*))); // NOLINT
    for (unsigned i = 0; i < fixed; i++) { lean_inc(fx(i)); args[i] = fx(i); }
    for (unsigned i = 0; i < 4; i++) args[fixed+i] = as[i];
    fnn fn = FNN(f);
    lean_dec_ref(f);
    return fn(args);
  }
} else if (arity < fixed + 4) {
  obj * as[4] = { a1, a2, a3, a4 };
  obj ** args = static_cast<obj**>(LEAN_ALLOCA(arity*sizeof(obj*))); // NOLINT
  for (unsigned i = 0; i < fixed; i++) { lean_inc(fx(i)); args[i] = fx(i); }
  for (unsigned i = 0; i < arity-fixed; i++) args[fixed+i] = as[i];
  obj * new_f = curry(f, arity, args);
  lean_dec_ref(f);
  return lean_apply_n(new_f, 4+fixed-arity, &as[arity-fixed]);
} else {
  return fix_args(f, {a1, a2, a3, a4});
}
}
extern "C" LEAN_EXPORT obj* lean_apply_5(obj* f, obj* a1, obj* a2, obj* a3, obj* a4, obj* a5) {
if (lean_is_scalar(f)) { lean_dec(a1); lean_dec(a2); lean_dec(a3); lean_dec(a4); lean_dec(a5); return f; } // f is an erased proof
unsigned arity = lean_closure_arity(f);
unsigned fixed = lean_closure_num_fixed(f);
if (arity == fixed + 5) {
  if (lean_is_exclusive(f)) {
    switch (arity) {
    case 5: { fn5 fn = FN5(f); lean_free_object(f); return fn(a1, a2, a3, a4, a5); }
    case 6: { obj* fx0 = fx(0); fn6 fn = FN6(f); lean_free_object(f); return fn(fx0, a1, a2, a3, a4, a5); }
    case 7: { obj* fx0 = fx(0); obj* fx1 = fx(1); fn7 fn = FN7(f); lean_free_object(f); return fn(fx0, fx1, a1, a2, a3, a4, a5); }
    case 8: { obj* fx0 = fx(0); obj* fx1 = fx(1); obj* fx2 = fx(2); fn8 fn = FN8(f); lean_free_object(f); return fn(fx0, fx1, fx2, a1, a2, a3, a4, a5); }
    case 9: { obj* fx0 = fx(0); obj* fx1 = fx(1); obj* fx2 = fx(2); obj* fx3 = fx(3); fn9 fn = FN9(f); lean_free_object(f); return fn(fx0, fx1, fx2, fx3, a1, a2, a3, a4, a5); }
    case 10: { obj* fx0 = fx(0); obj* fx1 = fx(1); obj* fx2 = fx(2); obj* fx3 = fx(3); obj* fx4 = fx(4); fn10 fn = FN10(f); lean_free_object(f); return fn(fx0, fx1, fx2, fx3, fx4, a1, a2, a3, a4, a5); }
    case 11: { obj* fx0 = fx(0); obj* fx1 = fx(1); obj* fx2 = fx(2); obj* fx3 = fx(3); obj* fx4 = fx(4); obj* fx5 = fx(5); fn11 fn = FN11(f); lean_free_object(f); return fn(fx0, fx1, fx2, fx3, fx4, fx5, a1, a2, a3, a4, a5); }
    case 12: { obj* fx0 = fx(0); obj* fx1 = fx(1); obj* fx2 = fx(2); obj* fx3 = fx(3); obj* fx4 = fx(4); obj* fx5 = fx(5); obj* fx6 = fx(6); fn12 fn = FN12(f); lean_free_object(f); return fn(fx0, fx1, fx2, fx3, fx4, fx5, fx6, a1, a2, a3, a4, a5); }
    case 13: { obj* fx0 = fx(0); obj* fx1 = fx(1); obj* fx2 = fx(2); obj* fx3 = fx(3); obj* fx4 = fx(4); obj* fx5 = fx(5); obj* fx6 = fx(6); obj* fx7 = fx(7); fn13 fn = FN13(f); lean_free_object(f); return fn(fx0, fx1, fx2, fx3, fx4, fx5, fx6, fx7, a1, a2, a3, a4, a5); }
    case 14: { obj* fx0 = fx(0); obj* fx1 = fx(1); obj* fx2 = fx(2); obj* fx3 = fx(3); obj* fx4 = fx(4); obj* fx5 = fx(5); obj* fx6 = fx(6); obj* fx7 = fx(7); obj* fx8 = fx(8); fn14 fn = FN14(f); lean_free_object(f); return fn(fx0, fx1, fx2, fx3, fx4, fx5, fx6, fx7, fx8, a1, a2, a3, a4, a5); }
    case 15: { obj* fx0 = fx(0); obj* fx1 = fx(1); obj* fx2 = fx(2); obj* fx3 = fx(3); obj* fx4 = fx(4); obj* fx5 = fx(5); obj* fx6 = fx(6); obj* fx7 = fx(7); obj* fx8 = fx(8); obj* fx9 = fx(9); fn15 fn = FN15(f); lean_free_object(f); return fn(fx0, fx1, fx2, fx3, fx4, fx5, fx6, fx7, fx8, fx9, a1, a2, a3, a4, a5); }
    case 16: { obj* fx0 = fx(0); obj* fx1 = fx(1); obj* fx2 = fx(2); obj* fx3 = fx(3); obj* fx4 = fx(4); obj* fx5 = fx(5); obj* fx6 = fx(6); obj* fx7 = fx(7); obj* fx8 = fx(8); obj* fx9 = fx(9); obj* fx10 = fx(10); fn16 fn = FN16(f); lean_free_object(f); return fn(fx0, fx1, fx2, fx3, fx4, fx5, fx6, fx7, fx8, fx9, fx10, a1, a2, a3, a4, a5); }
    }
  }
  switch (arity) {
  case 5: { fn5 fn = FN5(f); lean_dec_ref(f); return fn(a1, a2, a3, a4, a5); }
  case 6: { obj* fx0 = fx(0); lean_inc(fx0); fn6 fn = FN6(f); lean_dec_ref(f); return fn(fx0, a1, a2, a3, a4, a5); }
  case 7: { obj* fx0 = fx(0); obj* fx1 = fx(1); lean_inc(fx0); lean_inc(fx1); fn7 fn = FN7(f); lean_dec_ref(f); return fn(fx0, fx1, a1, a2, a3, a4, a5); }
  case 8: { obj* fx0 = fx(0); obj* fx1 = fx(1); obj* fx2 = fx(2); lean_inc(fx0); lean_inc(fx1); lean_inc(fx2); fn8 fn = FN8(f); lean_dec_ref(f); return fn(fx0, fx1, fx2, a1, a2, a3, a4, a5); }
  case 9: { obj* fx0 = fx(0); obj* fx1 = fx(1); obj* fx2 = fx(2); obj* fx3 = fx(3); lean_inc(fx0); lean_inc(fx1); lean_inc(fx2); lean_inc(fx3); fn9 fn = FN9(f); lean_dec_ref(f); return fn(fx0, fx1, fx2, fx3, a1, a2, a3, a4, a5); }
  case 10: { obj* fx0 = fx(0); obj* fx1 = fx(1); obj* fx2 = fx(2); obj* fx3 = fx(3); obj* fx4 = fx(4); lean_inc(fx0); lean_inc(fx1); lean_inc(fx2); lean_inc(fx3); lean_inc(fx4); fn10 fn = FN10(f); lean_dec_ref(f); return fn(fx0, fx1, fx2, fx3, fx4, a1, a2, a3, a4, a5); }
  case 11: { obj* fx0 = fx(0); obj* fx1 = fx(1); obj* fx2 = fx(2); obj* fx3 = fx(3); obj* fx4 = fx(4); obj* fx5 = fx(5); lean_inc(fx0); lean_inc(fx1); lean_inc(fx2); lean_inc(fx3); lean_inc(fx4); lean_inc(fx5); fn11 fn = FN11(f); lean_dec_ref(f); return fn(fx0, fx1, fx2, fx3, fx4, fx5, a1, a2, a3, a4, a5); }
  case 12: { obj* fx0 = fx(0); obj* fx1 = fx(1); obj* fx2 = fx(2); obj* fx3 = fx(3); obj* fx4 = fx(4); obj* fx5 = fx(5); obj* fx6 = fx(6); lean_inc(fx0); lean_inc(fx1); lean_inc(fx2); lean_inc(fx3); lean_inc(fx4); lean_inc(fx5); lean_inc(fx6); fn12 fn = FN12(f); lean_dec_ref(f); return fn(fx0, fx1, fx2, fx3, fx4, fx5, fx6, a1, a2, a3, a4, a5); }
  case 13: { obj* fx0 = fx(0); obj* fx1 = fx(1); obj* fx2 = fx(2); obj* fx3 = fx(3); obj* fx4 = fx(4); obj* fx5 = fx(5); obj* fx6 = fx(6); obj* fx7 = fx(7); lean_inc(fx0); lean_inc(fx1); lean_inc(fx2); lean_inc(fx3); lean_inc(fx4); lean_inc(fx5); lean_inc(fx6); lean_inc(fx7); fn13 fn = FN13(f); lean_dec_ref(f); return fn(fx0, fx1, fx2, fx3, fx4, fx5, fx6, fx7, a1, a2, a3, a4, a5); }
  case 14: { obj* fx0 = fx(0); obj* fx1 = fx(1); obj* fx2 = fx(2); obj* fx3 = fx(3); obj* fx4 = fx(4); obj* fx5 = fx(5); obj* fx6 = fx(6); obj* fx7 = fx(7); obj* fx8 = fx(8); lean_inc(fx0); lean_inc(fx1); lean_inc(fx2); lean_inc(fx3); lean_inc(fx4); lean_inc(fx5); lean_inc(fx6); lean_inc(fx7); lean_inc(fx8); fn14 fn = FN14(f); lean_dec_ref(f); return fn(fx0, fx1, fx2, fx3, fx4, fx5, fx6, fx7, fx8, a1, a2, a3, a4, a5); }
  case 15: { obj* fx0 = fx(0); obj* fx1 = fx(1); obj* fx2 = fx(2); obj* fx3 = fx(3); obj* fx4 = fx(4); obj* fx5 = fx(5); obj* fx6 = fx(6); obj* fx7 = fx(7); obj* fx8 = fx(8); obj* fx9 = fx(9); lean_inc(fx0); lean_inc(fx1); lean_inc(fx2); lean_inc(fx3); lean_inc(fx4); lean_inc(fx5); lean_inc(fx6); lean_inc(fx7); lean_inc(fx8); lean_inc(fx9); fn15 fn = FN15(f); lean_dec_ref(f); return fn(fx0, fx1, fx2, fx3, fx4, fx5, fx6, fx7, fx8, fx9, a1, a2, a3, a4, a5); }
  case 16: { obj* fx0 = fx(0); obj* fx1 = fx(1); obj* fx2 = fx(2); obj* fx3 = fx(3); obj* fx4 = fx(4); obj* fx5 = fx(5); obj* fx6 = fx(6); obj* fx7 = fx(7); obj* fx8 = fx(8); obj* fx9 = fx(9); obj* fx10 = fx(10); lean_inc(fx0); lean_inc(fx1); lean_inc(fx2); lean_inc(fx3); lean_inc(fx4); lean_inc(fx5); lean_inc(fx6); lean_inc(fx7); lean_inc(fx8); lean_inc(fx9); lean_inc(fx10); fn16 fn = FN16(f); lean_dec_ref(f); return fn(fx0, fx1, fx2, fx3, fx4, fx5, fx6, fx7, fx8, fx9, fx10, a1, a2, a3, a4, a5); }
  default:
    lean_assert(arity > 16);
    obj * as[5] = { a1, a2, a3, a4, a5 };
    obj ** args = static_cast<obj**>(LEAN_ALLOCA(arity*sizeof(obj*))); // NOLINT
    for (unsigned i = 0; i < fixed; i++) { lean_inc(fx(i)); args[i] = fx(i); }
    for (unsigned i = 0; i < 5; i++) args[fixed+i] = as[i];
    fnn fn = FNN(f);
    lean_dec_ref(f);
    return fn(args);
  }
} else if (arity < fixed + 5) {
  obj * as[5] = { a1, a2, a3, a4, a5 };
  obj ** args = static_cast<obj**>(LEAN_ALLOCA(arity*sizeof(obj*))); // NOLINT
  for (unsigned i = 0; i < fixed; i++) { lean_inc(fx(i)); args[i] = fx(i); }
  for (unsigned i = 0; i < arity-fixed; i++) args[fixed+i] = as[i];
  obj * new_f = curry(f, arity, args);
  lean_dec_ref(f);
  return lean_apply_n(new_f, 5+fixed-arity, &as[arity-fixed]);
} else {
  return fix_args(f, {a1, a2, a3, a4, a5});
}
}
extern "C" LEAN_EXPORT obj* lean_apply_6(obj* f, obj* a1, obj* a2, obj* a3, obj* a4, obj* a5, obj* a6) {
if (lean_is_scalar(f)) { lean_dec(a1); lean_dec(a2); lean_dec(a3); lean_dec(a4); lean_dec(a5); lean_dec(a6); return f; } // f is an erased proof
unsigned arity = lean_closure_arity(f);
unsigned fixed = lean_closure_num_fixed(f);
if (arity == fixed + 6) {
  if (lean_is_exclusive(f)) {
    switch (arity) {
    case 6: { fn6 fn = FN6(f); lean_free_object(f); return fn(a1, a2, a3, a4, a5, a6); }
    case 7: { obj* fx0 = fx(0); fn7 fn = FN7(f); lean_free_object(f); return fn(fx0, a1, a2, a3, a4, a5, a6); }
    case 8: { obj* fx0 = fx(0); obj* fx1 = fx(1); fn8 fn = FN8(f); lean_free_object(f); return fn(fx0, fx1, a1, a2, a3, a4, a5, a6); }
    case 9: { obj* fx0 = fx(0); obj* fx1 = fx(1); obj* fx2 = fx(2); fn9 fn = FN9(f); lean_free_object(f); return fn(fx0, fx1, fx2, a1, a2, a3, a4, a5, a6); }
    case 10: { obj* fx0 = fx(0); obj* fx1 = fx(1); obj* fx2 = fx(2); obj* fx3 = fx(3); fn10 fn = FN10(f); lean_free_object(f); return fn(fx0, fx1, fx2, fx3, a1, a2, a3, a4, a5, a6); }
    case 11: { obj* fx0 = fx(0); obj* fx1 = fx(1); obj* fx2 = fx(2); obj* fx3 = fx(3); obj* fx4 = fx(4); fn11 fn = FN11(f); lean_free_object(f); return fn(fx0, fx1, fx2, fx3, fx4, a1, a2, a3, a4, a5, a6); }
    case 12: { obj* fx0 = fx(0); obj* fx1 = fx(1); obj* fx2 = fx(2); obj* fx3 = fx(3); obj* fx4 = fx(4); obj* fx5 = fx(5); fn12 fn = FN12(f); lean_free_object(f); return fn(fx0, fx1, fx2, fx3, fx4, fx5, a1, a2, a3, a4, a5, a6); }
    case 13: { obj* fx0 = fx(0); obj* fx1 = fx(1); obj* fx2 = fx(2); obj* fx3 = fx(3); obj* fx4 = fx(4); obj* fx5 = fx(5); obj* fx6 = fx(6); fn13 fn = FN13(f); lean_free_object(f); return fn(fx0, fx1, fx2, fx3, fx4, fx5, fx6, a1, a2, a3, a4, a5, a6); }
    case 14: { obj* fx0 = fx(0); obj* fx1 = fx(1); obj* fx2 = fx(2); obj* fx3 = fx(3); obj* fx4 = fx(4); obj* fx5 = fx(5); obj* fx6 = fx(6); obj* fx7 = fx(7); fn14 fn = FN14(f); lean_free_object(f); return fn(fx0, fx1, fx2, fx3, fx4, fx5, fx6, fx7, a1, a2, a3, a4, a5, a6); }
    case 15: { obj* fx0 = fx(0); obj* fx1 = fx(1); obj* fx2 = fx(2); obj* fx3 = fx(3); obj* fx4 = fx(4); obj* fx5 = fx(5); obj* fx6 = fx(6); obj* fx7 = fx(7); obj* fx8 = fx(8); fn15 fn = FN15(f); lean_free_object(f); return fn(fx0, fx1, fx2, fx3, fx4, fx5, fx6, fx7, fx8, a1, a2, a3, a4, a5, a6); }
    case 16: { obj* fx0 = fx(0); obj* fx1 = fx(1); obj* fx2 = fx(2); obj* fx3 = fx(3); obj* fx4 = fx(4); obj* fx5 = fx(5); obj* fx6 = fx(6); obj* fx7 = fx(7); obj* fx8 = fx(8); obj* fx9 = fx(9); fn16 fn = FN16(f); lean_free_object(f); return fn(fx0, fx1, fx2, fx3, fx4, fx5, fx6, fx7, fx8, fx9, a1, a2, a3, a4, a5, a6); }
    }
  }
  switch (arity) {
  case 6: { fn6 fn = FN6(f); lean_dec_ref(f); return fn(a1, a2, a3, a4, a5, a6); }
  case 7: { obj* fx0 = fx(0); lean_inc(fx0); fn7 fn = FN7(f); lean_dec_ref(f); return fn(fx0, a1, a2, a3, a4, a5, a6); }
  case 8: { obj* fx0 = fx(0); obj* fx1 = fx(1); lean_inc(fx0); lean_inc(fx1); fn8 fn = FN8(f); lean_dec_ref(f); return fn(fx0, fx1, a1, a2, a3, a4, a5, a6); }
  case 9: { obj* fx0 = fx(0); obj* fx1 = fx(1); obj* fx2 = fx(2); lean_inc(fx0); lean_inc(fx1); lean_inc(fx2); fn9 fn = FN9(f); lean_dec_ref(f); return fn(fx0, fx1, fx2, a1, a2, a3, a4, a5, a6); }
  case 10: { obj* fx0 = fx(0); obj* fx1 = fx(1); obj* fx2 = fx(2); obj* fx3 = fx(3); lean_inc(fx0); lean_inc(fx1); lean_inc(fx2); lean_inc(fx3); fn10 fn = FN10(f); lean_dec_ref(f); return fn(fx0, fx1, fx2, fx3, a1, a2, a3, a4, a5, a6); }
  case 11: { obj* fx0 = fx(0); obj* fx1 = fx(1); obj* fx2 = fx(2); obj* fx3 = fx(3); obj* fx4 = fx(4); lean_inc(fx0); lean_inc(fx1); lean_inc(fx2); lean_inc(fx3); lean_inc(fx4); fn11 fn = FN11(f); lean_dec_ref(f); return fn(fx0, fx1, fx2, fx3, fx4, a1, a2, a3, a4, a5, a6); }
  case 12: { obj* fx0 = fx(0); obj* fx1 = fx(1); obj* fx2 = fx(2); obj* fx3 = fx(3); obj* fx4 = fx(4); obj* fx5 = fx(5); lean_inc(fx0); lean_inc(fx1); lean_inc(fx2); lean_inc(fx3); lean_inc(fx4); lean_inc(fx5); fn12 fn = FN12(f); lean_dec_ref(f); return fn(fx0, fx1, fx2, fx3, fx4, fx5, a1, a2, a3, a4, a5, a6); }
  case 13: { obj* fx0 = fx(0); obj* fx1 = fx(1); obj* fx2 = fx(2); obj* fx3 = fx(3); obj* fx4 = fx(4); obj* fx5 = fx(5); obj* fx6 = fx(6); lean_inc(fx0); lean_inc(fx1); lean_inc(fx2); lean_inc(fx3); lean_inc(fx4); lean_inc(fx5); lean_inc(fx6); fn13 fn = FN13(f); lean_dec_ref(f); return fn(fx0, fx1, fx2, fx3, fx4, fx5, fx6, a1, a2, a3, a4, a5, a6); }
  case 14: { obj* fx0 = fx(0); obj* fx1 = fx(1); obj* fx2 = fx(2); obj* fx3 = fx(3); obj* fx4 = fx(4); obj* fx5 = fx(5); obj* fx6 = fx(6); obj* fx7 = fx(7); lean_inc(fx0); lean_inc(fx1); lean_inc(fx2); lean_inc(fx3); lean_inc(fx4); lean_inc(fx5); lean_inc(fx6); lean_inc(fx7); fn14 fn = FN14(f); lean_dec_ref(f); return fn(fx0, fx1, fx2, fx3, fx4, fx5, fx6, fx7, a1, a2, a3, a4, a5, a6); }
  case 15: { obj* fx0 = fx(0); obj* fx1 = fx(1); obj* fx2 = fx(2); obj* fx3 = fx(3); obj* fx4 = fx(4); obj* fx5 = fx(5); obj* fx6 = fx(6); obj* fx7 = fx(7); obj* fx8 = fx(8); lean_inc(fx0); lean_inc(fx1); lean_inc(fx2); lean_inc(fx3); lean_inc(fx4); lean_inc(fx5); lean_inc(fx6); lean_inc(fx7); lean_inc(fx8); fn15 fn = FN15(f); lean_dec_ref(f); return fn(fx0, fx1, fx2, fx3, fx4, fx5, fx6, fx7, fx8, a1, a2, a3, a4, a5, a6); }
  case 16: { obj* fx0 = fx(0); obj* fx1 = fx(1); obj* fx2 = fx(2); obj* fx3 = fx(3); obj* fx4 = fx(4); obj* fx5 = fx(5); obj* fx6 = fx(6); obj* fx7 = fx(7); obj* fx8 = fx(8); obj* fx9 = fx(9); lean_inc(fx0); lean_inc(fx1); lean_inc(fx2); lean_inc(fx3); lean_inc(fx4); lean_inc(fx5); lean_inc(fx6); lean_inc(fx7); lean_inc(fx8); lean_inc(fx9); fn16 fn = FN16(f); lean_dec_ref(f); return fn(fx0, fx1, fx2, fx3, fx4, fx5, fx6, fx7, fx8, fx9, a1, a2, a3, a4, a5, a6); }
  default:
    lean_assert(arity > 16);
    obj * as[6] = { a1, a2, a3, a4, a5, a6 };
    obj ** args = static_cast<obj**>(LEAN_ALLOCA(arity*sizeof(obj*))); // NOLINT
    for (unsigned i = 0; i < fixed; i++) { lean_inc(fx(i)); args[i] = fx(i); }
    for (unsigned i = 0; i < 6; i++) args[fixed+i] = as[i];
    fnn fn = FNN(f);
    lean_dec_ref(f);
    return fn(args);
  }
} else if (arity < fixed + 6) {
  obj * as[6] = { a1, a2, a3, a4, a5, a6 };
  obj ** args = static_cast<obj**>(LEAN_ALLOCA(arity*sizeof(obj*))); // NOLINT
  for (unsigned i = 0; i < fixed; i++) { lean_inc(fx(i)); args[i] = fx(i); }
  for (unsigned i = 0; i < arity-fixed; i++) args[fixed+i] = as[i];
  obj * new_f = curry(f, arity, args);
  lean_dec_ref(f);
  return lean_apply_n(new_f, 6+fixed-arity, &as[arity-fixed]);
} else {
  return fix_args(f, {a1, a2, a3, a4, a5, a6});
}
}
extern "C" LEAN_EXPORT obj* lean_apply_7(obj* f, obj* a1, obj* a2, obj* a3, obj* a4, obj* a5, obj* a6, obj* a7) {
if (lean_is_scalar(f)) { lean_dec(a1); lean_dec(a2); lean_dec(a3); lean_dec(a4); lean_dec(a5); lean_dec(a6); lean_dec(a7); return f; } // f is an erased proof
unsigned arity = lean_closure_arity(f);
unsigned fixed = lean_closure_num_fixed(f);
if (arity == fixed + 7) {
  if (lean_is_exclusive(f)) {
    switch (arity) {
    case 7: { fn7 fn = FN7(f); lean_free_object(f); return fn(a1, a2, a3, a4, a5, a6, a7); }
    case 8: { obj* fx0 = fx(0); fn8 fn = FN8(f); lean_free_object(f); return fn(fx0, a1, a2, a3, a4, a5, a6, a7); }
    case 9: { obj* fx0 = fx(0); obj* fx1 = fx(1); fn9 fn = FN9(f); lean_free_object(f); return fn(fx0, fx1, a1, a2, a3, a4, a5, a6, a7); }
    case 10: { obj* fx0 = fx(0); obj* fx1 = fx(1); obj* fx2 = fx(2); fn10 fn = FN10(f); lean_free_object(f); return fn(fx0, fx1, fx2, a1, a2, a3, a4, a5, a6, a7); }
    case 11: { obj* fx0 = fx(0); obj* fx1 = fx(1); obj* fx2 = fx(2); obj* fx3 = fx(3); fn11 fn = FN11(f); lean_free_object(f); return fn(fx0, fx1, fx2, fx3, a1, a2, a3, a4, a5, a6, a7); }
    case 12: { obj* fx0 = fx(0); obj* fx1 = fx(1); obj* fx2 = fx(2); obj* fx3 = fx(3); obj* fx4 = fx(4); fn12 fn = FN12(f); lean_free_object(f); return fn(fx0, fx1, fx2, fx3, fx4, a1, a2, a3, a4, a5, a6, a7); }
    case 13: { obj* fx0 = fx(0); obj* fx1 = fx(1); obj* fx2 = fx(2); obj* fx3 = fx(3); obj* fx4 = fx(4); obj* fx5 = fx(5); fn13 fn = FN13(f); lean_free_object(f); return fn(fx0, fx1, fx2, fx3, fx4, fx5, a1, a2, a3, a4, a5, a6, a7); }
    case 14: { obj* fx0 = fx(0); obj* fx1 = fx(1); obj* fx2 = fx(2); obj* fx3 = fx(3); obj* fx4 = fx(4); obj* fx5 = fx(5); obj* fx6 = fx(6); fn14 fn = FN14(f); lean_free_object(f); return fn(fx0, fx1, fx2, fx3, fx4, fx5, fx6, a1, a2, a3, a4, a5, a6, a7); }
    case 15: { obj* fx0 = fx(0); obj* fx1 = fx(1); obj* fx2 = fx(2); obj* fx3 = fx(3); obj* fx4 = fx(4); obj* fx5 = fx(5); obj* fx6 = fx(6); obj* fx7 = fx(7); fn15 fn = FN15(f); lean_free_object(f); return fn(fx0, fx1, fx2, fx3, fx4, fx5, fx6, fx7, a1, a2, a3, a4, a5, a6, a7); }
    case 16: { obj* fx0 = fx(0); obj* fx1 = fx(1); obj* fx2 = fx(2); obj* fx3 = fx(3); obj* fx4 = fx(4); obj* fx5 = fx(5); obj* fx6 = fx(6); obj* fx7 = fx(7); obj* fx8 = fx(8); fn16 fn = FN16(f); lean_free_object(f); return fn(fx0, fx1, fx2, fx3, fx4, fx5, fx6, fx7, fx8, a1, a2, a3, a4, a5, a6, a7); }
    }
  }
  switch (arity) {
  case 7: { fn7 fn = FN7(f); lean_dec_ref(f); return fn(a1, a2, a3, a4, a5, a6, a7); }
  case 8: { obj* fx0 = fx(0); lean_inc(fx0); fn8 fn = FN8(f); lean_dec_ref(f); return fn(fx0, a1, a2, a3, a4, a5, a6, a7); }
  case 9: { obj* fx0 = fx(0); obj* fx1 = fx(1); lean_inc(fx0); lean_inc(fx1); fn9 fn = FN9(f); lean_dec_ref(f); return fn(fx0, fx1, a1, a2, a3, a4, a5, a6, a7); }
  case 10: { obj* fx0 = fx(0); obj* fx1 = fx(1); obj* fx2 = fx(2); lean_inc(fx0); lean_inc(fx1); lean_inc(fx2); fn10 fn = FN10(f); lean_dec_ref(f); return fn(fx0, fx1, fx2, a1, a2, a3, a4, a5, a6, a7); }
  case 11: { obj* fx0 = fx(0); obj* fx1 = fx(1); obj* fx2 = fx(2); obj* fx3 = fx(3); lean_inc(fx0); lean_inc(fx1); lean_inc(fx2); lean_inc(fx3); fn11 fn = FN11(f); lean_dec_ref(f); return fn(fx0, fx1, fx2, fx3, a1, a2, a3, a4, a5, a6, a7); }
  case 12: { obj* fx0 = fx(0); obj* fx1 = fx(1); obj* fx2 = fx(2); obj* fx3 = fx(3); obj* fx4 = fx(4); lean_inc(fx0); lean_inc(fx1); lean_inc(fx2); lean_inc(fx3); lean_inc(fx4); fn12 fn = FN12(f); lean_dec_ref(f); return fn(fx0, fx1, fx2, fx3, fx4, a1, a2, a3, a4, a5, a6, a7); }
  case 13: { obj* fx0 = fx(0); obj* fx1 = fx(1); obj* fx2 = fx(2); obj* fx3 = fx(3); obj* fx4 = fx(4); obj* fx5 = fx(5); lean_inc(fx0); lean_inc(fx1); lean_inc(fx2); lean_inc(fx3); lean_inc(fx4); lean_inc(fx5); fn13 fn = FN13(f); lean_dec_ref(f); return fn(fx0, fx1, fx2, fx3, fx4, fx5, a1, a2, a3, a4, a5, a6, a7); }
  case 14: { obj* fx0 = fx(0); obj* fx1 = fx(1); obj* fx2 = fx(2); obj* fx3 = fx(3); obj* fx4 = fx(4); obj* fx5 = fx(5); obj* fx6 = fx(6); lean_inc(fx0); lean_inc(fx1); lean_inc(fx2); lean_inc(fx3); lean_inc(fx4); lean_inc(fx5); lean_inc(fx6); fn14 fn = FN14(f); lean_dec_ref(f); return fn(fx0, fx1, fx2, fx3, fx4, fx5, fx6, a1, a2, a3, a4, a5, a6, a7); }
  case 15: { obj* fx0 = fx(0); obj* fx1 = fx(1); obj* fx2 = fx(2); obj* fx3 = fx(3); obj* fx4 = fx(4); obj* fx5 = fx(5); obj* fx6 = fx(6); obj* fx7 = fx(7); lean_inc(fx0); lean_inc(fx1); lean_inc(fx2); lean_inc(fx3); lean_inc(fx4); lean_inc(fx5); lean_inc(fx6); lean_inc(fx7); fn15 fn = FN15(f); lean_dec_ref(f); return fn(fx0, fx1, fx2, fx3, fx4, fx5, fx6, fx7, a1, a2, a3, a4, a5, a6, a7); }
  case 16: { obj* fx0 = fx(0); obj* fx1 = fx(1); obj* fx2 = fx(2); obj* fx3 = fx(3); obj* fx4 = fx(4); obj* fx5 = fx(5); obj* fx6 = fx(6); obj* fx7 = fx(7); obj* fx8 = fx(8); lean_inc(fx0); lean_inc(fx1); lean_inc(fx2); lean_inc(fx3); lean_inc(fx4); lean_inc(fx5); lean_inc(fx6); lean_inc(fx7); lean_inc(fx8); fn16 fn = FN16(f); lean_dec_ref(f); return fn(fx0, fx1, fx2, fx3, fx4, fx5, fx6, fx7, fx8, a1, a2, a3, a4, a5, a6, a7); }
  default:
    lean_assert(arity > 16);
    obj * as[7] = { a1, a2, a3, a4, a5, a6, a7 };
    obj ** args = static_cast<obj**>(LEAN_ALLOCA(arity*sizeof(obj*))); // NOLINT
    for (unsigned i = 0; i < fixed; i++) { lean_inc(fx(i)); args[i] = fx(i); }
    for (unsigned i = 0; i < 7; i++) args[fixed+i] = as[i];
    fnn fn = FNN(f);
    lean_dec_ref(f);
    return fn(args);
  }
} else if (arity < fixed + 7) {
  obj * as[7] = { a1, a2, a3, a4, a5, a6, a7 };
  obj ** args = static_cast<obj**>(LEAN_ALLOCA(arity*sizeof(obj*))); // NOLINT
  for (unsigned i = 0; i < fixed; i++) { lean_inc(fx(i)); args[i] = fx(i); }
  for (unsigned i = 0; i < arity-fixed; i++) args[fixed+i] = as[i];
  obj * new_f = curry(f, arity, args);
  lean_dec_ref(f);
  return lean_apply_n(new_f, 7+fixed-arity, &as[arity-fixed]);
} else {
  return fix_args(f, {a1, a2, a3, a4, a5, a6, a7});
}
}
extern "C" LEAN_EXPORT obj* lean_apply_8(obj* f, obj* a1, obj* a2, obj* a3, obj* a4, obj* a5, obj* a6, obj* a7, obj* a8) {
if (lean_is_scalar(f)) { lean_dec(a1); lean_dec(a2); lean_dec(a3); lean_dec(a4); lean_dec(a5); lean_dec(a6); lean_dec(a7); lean_dec(a8); return f; } // f is an erased proof
unsigned arity = lean_closure_arity(f);
unsigned fixed = lean_closure_num_fixed(f);
if (arity == fixed + 8) {
  if (lean_is_exclusive(f)) {
    switch (arity) {
    case 8: { fn8 fn = FN8(f); lean_free_object(f); return fn(a1, a2, a3, a4, a5, a6, a7, a8); }
    case 9: { obj* fx0 = fx(0); fn9 fn = FN9(f); lean_free_object(f); return fn(fx0, a1, a2, a3, a4, a5, a6, a7, a8); }
    case 10: { obj* fx0 = fx(0); obj* fx1 = fx(1); fn10 fn = FN10(f); lean_free_object(f); return fn(fx0, fx1, a1, a2, a3, a4, a5, a6, a7, a8); }
    case 11: { obj* fx0 = fx(0); obj* fx1 = fx(1); obj* fx2 = fx(2); fn11 fn = FN11(f); lean_free_object(f); return fn(fx0, fx1, fx2, a1, a2, a3, a4, a5, a6, a7, a8); }
    case 12: { obj* fx0 = fx(0); obj* fx1 = fx(1); obj* fx2 = fx(2); obj* fx3 = fx(3); fn12 fn = FN12(f); lean_free_object(f); return fn(fx0, fx1, fx2, fx3, a1, a2, a3, a4, a5, a6, a7, a8); }
    case 13: { obj* fx0 = fx(0); obj* fx1 = fx(1); obj* fx2 = fx(2); obj* fx3 = fx(3); obj* fx4 = fx(4); fn13 fn = FN13(f); lean_free_object(f); return fn(fx0, fx1, fx2, fx3, fx4, a1, a2, a3, a4, a5, a6, a7, a8); }
    case 14: { obj* fx0 = fx(0); obj* fx1 = fx(1); obj* fx2 = fx(2); obj* fx3 = fx(3); obj* fx4 = fx(4); obj* fx5 = fx(5); fn14 fn = FN14(f); lean_free_object(f); return fn(fx0, fx1, fx2, fx3, fx4, fx5, a1, a2, a3, a4, a5, a6, a7, a8); }
    case 15: { obj* fx0 = fx(0); obj* fx1 = fx(1); obj* fx2 = fx(2); obj* fx3 = fx(3); obj* fx4 = fx(4); obj* fx5 = fx(5); obj* fx6 = fx(6); fn15 fn = FN15(f); lean_free_object(f); return fn(fx0, fx1, fx2, fx3, fx4, fx5, fx6, a1, a2, a3, a4, a5, a6, a7, a8); }
    case 16: { obj* fx0 = fx(0); obj* fx1 = fx(1); obj* fx2 = fx(2); obj* fx3 = fx(3); obj* fx4 = fx(4); obj* fx5 = fx(5); obj* fx6 = fx(6); obj* fx7 = fx(7); fn16 fn = FN16(f); lean_free_object(f); return fn(fx0, fx1, fx2, fx3, fx4, fx5, fx6, fx7, a1, a2, a3, a4, a5, a6, a7, a8); }
    }
  }
  switch (arity) {
  case 8: { fn8 fn = FN8(f); lean_dec_ref(f); return fn(a1, a2, a3, a4, a5, a6, a7, a8); }
  case 9: { obj* fx0 = fx(0); lean_inc(fx0); fn9 fn = FN9(f); lean_dec_ref(f); return fn(fx0, a1, a2, a3, a4, a5, a6, a7, a8); }
  case 10: { obj* fx0 = fx(0); obj* fx1 = fx(1); lean_inc(fx0); lean_inc(fx1); fn10 fn = FN10(f); lean_dec_ref(f); return fn(fx0, fx1, a1, a2, a3, a4, a5, a6, a7, a8); }
  case 11: { obj* fx0 = fx(0); obj* fx1 = fx(1); obj* fx2 = fx(2); lean_inc(fx0); lean_inc(fx1); lean_inc(fx2); fn11 fn = FN11(f); lean_dec_ref(f); return fn(fx0, fx1, fx2, a1, a2, a3, a4, a5, a6, a7, a8); }
  case 12: { obj* fx0 = fx(0); obj* fx1 = fx(1); obj* fx2 = fx(2); obj* fx3 = fx(3); lean_inc(fx0); lean_inc(fx1); lean_inc(fx2); lean_inc(fx3); fn12 fn = FN12(f); lean_dec_ref(f); return fn(fx0, fx1, fx2, fx3, a1, a2, a3, a4, a5, a6, a7, a8); }
  case 13: { obj* fx0 = fx(0); obj* fx1 = fx(1); obj* fx2 = fx(2); obj* fx3 = fx(3); obj* fx4 = fx(4); lean_inc(fx0); lean_inc(fx1); lean_inc(fx2); lean_inc(fx3); lean_inc(fx4); fn13 fn = FN13(f); lean_dec_ref(f); return fn(fx0, fx1, fx2, fx3, fx4, a1, a2, a3, a4, a5, a6, a7, a8); }
  case 14: { obj* fx0 = fx(0); obj* fx1 = fx(1); obj* fx2 = fx(2); obj* fx3 = fx(3); obj* fx4 = fx(4); obj* fx5 = fx(5); lean_inc(fx0); lean_inc(fx1); lean_inc(fx2); lean_inc(fx3); lean_inc(fx4); lean_inc(fx5); fn14 fn = FN14(f); lean_dec_ref(f); return fn(fx0, fx1, fx2, fx3, fx4, fx5, a1, a2, a3, a4, a5, a6, a7, a8); }
  case 15: { obj* fx0 = fx(0); obj* fx1 = fx(1); obj* fx2 = fx(2); obj* fx3 = fx(3); obj* fx4 = fx(4); obj* fx5 = fx(5); obj* fx6 = fx(6); lean_inc(fx0); lean_inc(fx1); lean_inc(fx2); lean_inc(fx3); lean_inc(fx4); lean_inc(fx5); lean_inc(fx6); fn15 fn = FN15(f); lean_dec_ref(f); return fn(fx0, fx1, fx2, fx3, fx4, fx5, fx6, a1, a2, a3, a4, a5, a6, a7, a8); }
  case 16: { obj* fx0 = fx(0); obj* fx1 = fx(1); obj* fx2 = fx(2); obj* fx3 = fx(3); obj* fx4 = fx(4); obj* fx5 = fx(5); obj* fx6 = fx(6); obj* fx7 = fx(7); lean_inc(fx0); lean_inc(fx1); lean_inc(fx2); lean_inc(fx3); lean_inc(fx4); lean_inc(fx5); lean_inc(fx6); lean_inc(fx7); fn16 fn = FN16(f); lean_dec_ref(f); return fn(fx0, fx1, fx2, fx3, fx4, fx5, fx6, fx7, a1, a2, a3, a4, a5, a6, a7, a8); }
  default:
    lean_assert(arity > 16);
    obj * as[8] = { a1, a2, a3, a4, a5, a6, a7, a8 };
    obj ** args = static_cast<obj**>(LEAN_ALLOCA(arity*sizeof(obj*))); // NOLINT
    for (unsigned i = 0; i < fixed; i++) { lean_inc(fx(i)); args[i] = fx(i); }
    for (unsigned i = 0; i < 8; i++) args[fixed+i] = as[i];
    fnn fn = FNN(f);
    lean_dec_ref(f);
    return fn(args);
  }
} else if (arity < fixed + 8) {
  obj * as[8] = { a1, a2, a3, a4, a5, a6, a7, a8 };
  obj ** args = static_cast<obj**>(LEAN_ALLOCA(arity*sizeof(obj*))); // NOLINT
  for (unsigned i = 0; i < fixed; i++) { lean_inc(fx(i)); args[i] = fx(i); }
  for (unsigned i = 0; i < arity-fixed; i++) args[fixed+i] = as[i];
  obj * new_f = curry(f, arity, args);
  lean_dec_ref(f);
  return lean_apply_n(new_f, 8+fixed-arity, &as[arity-fixed]);
} else {
  return fix_args(f, {a1, a2, a3, a4, a5, a6, a7, a8});
}
}
extern "C" LEAN_EXPORT obj* lean_apply_9(obj* f, obj* a1, obj* a2, obj* a3, obj* a4, obj* a5, obj* a6, obj* a7, obj* a8, obj* a9) {
if (lean_is_scalar(f)) { lean_dec(a1); lean_dec(a2); lean_dec(a3); lean_dec(a4); lean_dec(a5); lean_dec(a6); lean_dec(a7); lean_dec(a8); lean_dec(a9); return f; } // f is an erased proof
unsigned arity = lean_closure_arity(f);
unsigned fixed = lean_closure_num_fixed(f);
if (arity == fixed + 9) {
  if (lean_is_exclusive(f)) {
    switch (arity) {
    case 9: { fn9 fn = FN9(f); lean_free_object(f); return fn(a1, a2, a3, a4, a5, a6, a7, a8, a9); }
    case 10: { obj* fx0 = fx(0); fn10 fn = FN10(f); lean_free_object(f); return fn(fx0, a1, a2, a3, a4, a5, a6, a7, a8, a9); }
    case 11: { obj* fx0 = fx(0); obj* fx1 = fx(1); fn11 fn = FN11(f); lean_free_object(f); return fn(fx0, fx1, a1, a2, a3, a4, a5, a6, a7, a8, a9); }
    case 12: { obj* fx0 = fx(0); obj* fx1 = fx(1); obj* fx2 = fx(2); fn12 fn = FN12(f); lean_free_object(f); return fn(fx0, fx1, fx2, a1, a2, a3, a4, a5, a6, a7, a8, a9); }
    case 13: { obj* fx0 = fx(0); obj* fx1 = fx(1); obj* fx2 = fx(2); obj* fx3 = fx(3); fn13 fn = FN13(f); lean_free_object(f); return fn(fx0, fx1, fx2, fx3, a1, a2, a3, a4, a5, a6, a7, a8, a9); }
    case 14: { obj* fx0 = fx(0); obj* fx1 = fx(1); obj* fx2 = fx(2); obj* fx3 = fx(3); obj* fx4 = fx(4); fn14 fn = FN14(f); lean_free_object(f); return fn(fx0, fx1, fx2, fx3, fx4, a1, a2, a3, a4, a5, a6, a7, a8, a9); }
    case 15: { obj* fx0 = fx(0); obj* fx1 = fx(1); obj* fx2 = fx(2); obj* fx3 = fx(3); obj* fx4 = fx(4); obj* fx5 = fx(5); fn15 fn = FN15(f); lean_free_object(f); return fn(fx0, fx1, fx2, fx3, fx4, fx5, a1, a2, a3, a4, a5, a6, a7, a8, a9); }
    case 16: { obj* fx0 = fx(0); obj* fx1 = fx(1); obj* fx2 = fx(2); obj* fx3 = fx(3); obj* fx4 = fx(4); obj* fx5 = fx(5); obj* fx6 = fx(6); fn16 fn = FN16(f); lean_free_object(f); return fn(fx0, fx1, fx2, fx3, fx4, fx5, fx6, a1, a2, a3, a4, a5, a6, a7, a8, a9); }
    }
  }
  switch (arity) {
  case 9: { fn9 fn = FN9(f); lean_dec_ref(f); return fn(a1, a2, a3, a4, a5, a6, a7, a8, a9); }
  case 10: { obj* fx0 = fx(0); lean_inc(fx0); fn10 fn = FN10(f); lean_dec_ref(f); return fn(fx0, a1, a2, a3, a4, a5, a6, a7, a8, a9); }
  case 11: { obj* fx0 = fx(0); obj* fx1 = fx(1); lean_inc(fx0); lean_inc(fx1); fn11 fn = FN11(f); lean_dec_ref(f); return fn(fx0, fx1, a1, a2, a3, a4, a5, a6, a7, a8, a9); }
  case 12: { obj* fx0 = fx(0); obj* fx1 = fx(1); obj* fx2 = fx(2); lean_inc(fx0); lean_inc(fx1); lean_inc(fx2); fn12 fn = FN12(f); lean_dec_ref(f); return fn(fx0, fx1, fx2, a1, a2, a3, a4, a5, a6, a7, a8, a9); }
  case 13: { obj* fx0 = fx(0); obj* fx1 = fx(1); obj* fx2 = fx(2); obj* fx3 = fx(3); lean_inc(fx0); lean_inc(fx1); lean_inc(fx2); lean_inc(fx3); fn13 fn = FN13(f); lean_dec_ref(f); return fn(fx0, fx1, fx2, fx3, a1, a2, a3, a4, a5, a6, a7, a8, a9); }
  case 14: { obj* fx0 = fx(0); obj* fx1 = fx(1); obj* fx2 = fx(2); obj* fx3 = fx(3); obj* fx4 = fx(4); lean_inc(fx0); lean_inc(fx1); lean_inc(fx2); lean_inc(fx3); lean_inc(fx4); fn14 fn = FN14(f); lean_dec_ref(f); return fn(fx0, fx1, fx2, fx3, fx4, a1, a2, a3, a4, a5, a6, a7, a8, a9); }
  case 15: { obj* fx0 = fx(0); obj* fx1 = fx(1); obj* fx2 = fx(2); obj* fx3 = fx(3); obj* fx4 = fx(4); obj* fx5 = fx(5); lean_inc(fx0); lean_inc(fx1); lean_inc(fx2); lean_inc(fx3); lean_inc(fx4); lean_inc(fx5); fn15 fn = FN15(f); lean_dec_ref(f); return fn(fx0, fx1, fx2, fx3, fx4, fx5, a1, a2, a3, a4, a5, a6, a7, a8, a9); }
  case 16: { obj* fx0 = fx(0); obj* fx1 = fx(1); obj* fx2 = fx(2); obj* fx3 = fx(3); obj* fx4 = fx(4); obj* fx5 = fx(5); obj* fx6 = fx(6); lean_inc(fx0); lean_inc(fx1); lean_inc(fx2); lean_inc(fx3); lean_inc(fx4); lean_inc(fx5); lean_inc(fx6); fn16 fn = FN16(f); lean_dec_ref(f); return fn(fx0, fx1, fx2, fx3, fx4, fx5, fx6, a1, a2, a3, a4, a5, a6, a7, a8, a9); }
  default:
    lean_assert(arity > 16);
    obj * as[9] = { a1, a2, a3, a4, a5, a6, a7, a8, a9 };
    obj ** args = static_cast<obj**>(LEAN_ALLOCA(arity*sizeof(obj*))); // NOLINT
    for (unsigned i = 0; i < fixed; i++) { lean_inc(fx(i)); args[i] = fx(i); }
    for (unsigned i = 0; i < 9; i++) args[fixed+i] = as[i];
    fnn fn = FNN(f);
    lean_dec_ref(f);
    return fn(args);
  }
} else if (arity < fixed + 9) {
  obj * as[9] = { a1, a2, a3, a4, a5, a6, a7, a8, a9 };
  obj ** args = static_cast<obj**>(LEAN_ALLOCA(arity*sizeof(obj*))); // NOLINT
  for (unsigned i = 0; i < fixed; i++) { lean_inc(fx(i)); args[i] = fx(i); }
  for (unsigned i = 0; i < arity-fixed; i++) args[fixed+i] = as[i];
  obj * new_f = curry(f, arity, args);
  lean_dec_ref(f);
  return lean_apply_n(new_f, 9+fixed-arity, &as[arity-fixed]);
} else {
  return fix_args(f, {a1, a2, a3, a4, a5, a6, a7, a8, a9});
}
}
extern "C" LEAN_EXPORT obj* lean_apply_10(obj* f, obj* a1, obj* a2, obj* a3, obj* a4, obj* a5, obj* a6, obj* a7, obj* a8, obj* a9, obj* a10) {
if (lean_is_scalar(f)) { lean_dec(a1); lean_dec(a2); lean_dec(a3); lean_dec(a4); lean_dec(a5); lean_dec(a6); lean_dec(a7); lean_dec(a8); lean_dec(a9); lean_dec(a10); return f; } // f is an erased proof
unsigned arity = lean_closure_arity(f);
unsigned fixed = lean_closure_num_fixed(f);
if (arity == fixed + 10) {
  if (lean_is_exclusive(f)) {
    switch (arity) {
    case 10: { fn10 fn = FN10(f); lean_free_object(f); return fn(a1, a2, a3, a4, a5, a6, a7, a8, a9, a10); }
    case 11: { obj* fx0 = fx(0); fn11 fn = FN11(f); lean_free_object(f); return fn(fx0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10); }
    case 12: { obj* fx0 = fx(0); obj* fx1 = fx(1); fn12 fn = FN12(f); lean_free_object(f); return fn(fx0, fx1, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10); }
    case 13: { obj* fx0 = fx(0); obj* fx1 = fx(1); obj* fx2 = fx(2); fn13 fn = FN13(f); lean_free_object(f); return fn(fx0, fx1, fx2, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10); }
    case 14: { obj* fx0 = fx(0); obj* fx1 = fx(1); obj* fx2 = fx(2); obj* fx3 = fx(3); fn14 fn = FN14(f); lean_free_object(f); return fn(fx0, fx1, fx2, fx3, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10); }
    case 15: { obj* fx0 = fx(0); obj* fx1 = fx(1); obj* fx2 = fx(2); obj* fx3 = fx(3); obj* fx4 = fx(4); fn15 fn = FN15(f); lean_free_object(f); return fn(fx0, fx1, fx2, fx3, fx4, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10); }
    case 16: { obj* fx0 = fx(0); obj* fx1 = fx(1); obj* fx2 = fx(2); obj* fx3 = fx(3); obj* fx4 = fx(4); obj* fx5 = fx(5); fn16 fn = FN16(f); lean_free_object(f); return fn(fx0, fx1, fx2, fx3, fx4, fx5, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10); }
    }
  }
  switch (arity) {
  case 10: { fn10 fn = FN10(f); lean_dec_ref(f); return fn(a1, a2, a3, a4, a5, a6, a7, a8, a9, a10); }
  case 11: { obj* fx0 = fx(0); lean_inc(fx0); fn11 fn = FN11(f); lean_dec_ref(f); return fn(fx0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10); }
  case 12: { obj* fx0 = fx(0); obj* fx1 = fx(1); lean_inc(fx0); lean_inc(fx1); fn12 fn = FN12(f); lean_dec_ref(f); return fn(fx0, fx1, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10); }
  case 13: { obj* fx0 = fx(0); obj* fx1 = fx(1); obj* fx2 = fx(2); lean_inc(fx0); lean_inc(fx1); lean_inc(fx2); fn13 fn = FN13(f); lean_dec_ref(f); return fn(fx0, fx1, fx2, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10); }
  case 14: { obj* fx0 = fx(0); obj* fx1 = fx(1); obj* fx2 = fx(2); obj* fx3 = fx(3); lean_inc(fx0); lean_inc(fx1); lean_inc(fx2); lean_inc(fx3); fn14 fn = FN14(f); lean_dec_ref(f); return fn(fx0, fx1, fx2, fx3, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10); }
  case 15: { obj* fx0 = fx(0); obj* fx1 = fx(1); obj* fx2 = fx(2); obj* fx3 = fx(3); obj* fx4 = fx(4); lean_inc(fx0); lean_inc(fx1); lean_inc(fx2); lean_inc(fx3); lean_inc(fx4); fn15 fn = FN15(f); lean_dec_ref(f); return fn(fx0, fx1, fx2, fx3, fx4, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10); }
  case 16: { obj* fx0 = fx(0); obj* fx1 = fx(1); obj* fx2 = fx(2); obj* fx3 = fx(3); obj* fx4 = fx(4); obj* fx5 = fx(5); lean_inc(fx0); lean_inc(fx1); lean_inc(fx2); lean_inc(fx3); lean_inc(fx4); lean_inc(fx5); fn16 fn = FN16(f); lean_dec_ref(f); return fn(fx0, fx1, fx2, fx3, fx4, fx5, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10); }
  default:
    lean_assert(arity > 16);
    obj * as[10] = { a1, a2, a3, a4, a5, a6, a7, a8, a9, a10 };
    obj ** args = static_cast<obj**>(LEAN_ALLOCA(arity*sizeof(obj*))); // NOLINT
    for (unsigned i = 0; i < fixed; i++) { lean_inc(fx(i)); args[i] = fx(i); }
    for (unsigned i = 0; i < 10; i++) args[fixed+i] = as[i];
    fnn fn = FNN(f);
    lean_dec_ref(f);
    return fn(args);
  }
} else if (arity < fixed + 10) {
  obj * as[10] = { a1, a2, a3, a4, a5, a6, a7, a8, a9, a10 };
  obj ** args = static_cast<obj**>(LEAN_ALLOCA(arity*sizeof(obj*))); // NOLINT
  for (unsigned i = 0; i < fixed; i++) { lean_inc(fx(i)); args[i] = fx(i); }
  for (unsigned i = 0; i < arity-fixed; i++) args[fixed+i] = as[i];
  obj * new_f = curry(f, arity, args);
  lean_dec_ref(f);
  return lean_apply_n(new_f, 10+fixed-arity, &as[arity-fixed]);
} else {
  return fix_args(f, {a1, a2, a3, a4, a5, a6, a7, a8, a9, a10});
}
}
extern "C" LEAN_EXPORT obj* lean_apply_11(obj* f, obj* a1, obj* a2, obj* a3, obj* a4, obj* a5, obj* a6, obj* a7, obj* a8, obj* a9, obj* a10, obj* a11) {
if (lean_is_scalar(f)) { lean_dec(a1); lean_dec(a2); lean_dec(a3); lean_dec(a4); lean_dec(a5); lean_dec(a6); lean_dec(a7); lean_dec(a8); lean_dec(a9); lean_dec(a10); lean_dec(a11); return f; } // f is an erased proof
unsigned arity = lean_closure_arity(f);
unsigned fixed = lean_closure_num_fixed(f);
if (arity == fixed + 11) {
  if (lean_is_exclusive(f)) {
    switch (arity) {
    case 11: { fn11 fn = FN11(f); lean_free_object(f); return fn(a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11); }
    case 12: { obj* fx0 = fx(0); fn12 fn = FN12(f); lean_free_object(f); return fn(fx0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11); }
    case 13: { obj* fx0 = fx(0); obj* fx1 = fx(1); fn13 fn = FN13(f); lean_free_object(f); return fn(fx0, fx1, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11); }
    case 14: { obj* fx0 = fx(0); obj* fx1 = fx(1); obj* fx2 = fx(2); fn14 fn = FN14(f); lean_free_object(f); return fn(fx0, fx1, fx2, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11); }
    case 15: { obj* fx0 = fx(0); obj* fx1 = fx(1); obj* fx2 = fx(2); obj* fx3 = fx(3); fn15 fn = FN15(f); lean_free_object(f); return fn(fx0, fx1, fx2, fx3, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11); }
    case 16: { obj* fx0 = fx(0); obj* fx1 = fx(1); obj* fx2 = fx(2); obj* fx3 = fx(3); obj* fx4 = fx(4); fn16 fn = FN16(f); lean_free_object(f); return fn(fx0, fx1, fx2, fx3, fx4, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11); }
    }
  }
  switch (arity) {
  case 11: { fn11 fn = FN11(f); lean_dec_ref(f); return fn(a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11); }
  case 12: { obj* fx0 = fx(0); lean_inc(fx0); fn12 fn = FN12(f); lean_dec_ref(f); return fn(fx0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11); }
  case 13: { obj* fx0 = fx(0); obj* fx1 = fx(1); lean_inc(fx0); lean_inc(fx1); fn13 fn = FN13(f); lean_dec_ref(f); return fn(fx0, fx1, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11); }
  case 14: { obj* fx0 = fx(0); obj* fx1 = fx(1); obj* fx2 = fx(2); lean_inc(fx0); lean_inc(fx1); lean_inc(fx2); fn14 fn = FN14(f); lean_dec_ref(f); return fn(fx0, fx1, fx2, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11); }
  case 15: { obj* fx0 = fx(0); obj* fx1 = fx(1); obj* fx2 = fx(2); obj* fx3 = fx(3); lean_inc(fx0); lean_inc(fx1); lean_inc(fx2); lean_inc(fx3); fn15 fn = FN15(f); lean_dec_ref(f); return fn(fx0, fx1, fx2, fx3, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11); }
  case 16: { obj* fx0 = fx(0); obj* fx1 = fx(1); obj* fx2 = fx(2); obj* fx3 = fx(3); obj* fx4 = fx(4); lean_inc(fx0); lean_inc(fx1); lean_inc(fx2); lean_inc(fx3); lean_inc(fx4); fn16 fn = FN16(f); lean_dec_ref(f); return fn(fx0, fx1, fx2, fx3, fx4, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11); }
  default:
    lean_assert(arity > 16);
    obj * as[11] = { a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11 };
    obj ** args = static_cast<obj**>(LEAN_ALLOCA(arity*sizeof(obj*))); // NOLINT
    for (unsigned i = 0; i < fixed; i++) { lean_inc(fx(i)); args[i] = fx(i); }
    for (unsigned i = 0; i < 11; i++) args[fixed+i] = as[i];
    fnn fn = FNN(f);
    lean_dec_ref(f);
    return fn(args);
  }
} else if (arity < fixed + 11) {
  obj * as[11] = { a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11 };
  obj ** args = static_cast<obj**>(LEAN_ALLOCA(arity*sizeof(obj*))); // NOLINT
  for (unsigned i = 0; i < fixed; i++) { lean_inc(fx(i)); args[i] = fx(i); }
  for (unsigned i = 0; i < arity-fixed; i++) args[fixed+i] = as[i];
  obj * new_f = curry(f, arity, args);
  lean_dec_ref(f);
  return lean_apply_n(new_f, 11+fixed-arity, &as[arity-fixed]);
} else {
  return fix_args(f, {a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11});
}
}
extern "C" LEAN_EXPORT obj* lean_apply_12(obj* f, obj* a1, obj* a2, obj* a3, obj* a4, obj* a5, obj* a6, obj* a7, obj* a8, obj* a9, obj* a10, obj* a11, obj* a12) {
if (lean_is_scalar(f)) { lean_dec(a1); lean_dec(a2); lean_dec(a3); lean_dec(a4); lean_dec(a5); lean_dec(a6); lean_dec(a7); lean_dec(a8); lean_dec(a9); lean_dec(a10); lean_dec(a11); lean_dec(a12); return f; } // f is an erased proof
unsigned arity = lean_closure_arity(f);
unsigned fixed = lean_closure_num_fixed(f);
if (arity == fixed + 12) {
  if (lean_is_exclusive(f)) {
    switch (arity) {
    case 12: { fn12 fn = FN12(f); lean_free_object(f); return fn(a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12); }
    case 13: { obj* fx0 = fx(0); fn13 fn = FN13(f); lean_free_object(f); return fn(fx0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12); }
    case 14: { obj* fx0 = fx(0); obj* fx1 = fx(1); fn14 fn = FN14(f); lean_free_object(f); return fn(fx0, fx1, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12); }
    case 15: { obj* fx0 = fx(0); obj* fx1 = fx(1); obj* fx2 = fx(2); fn15 fn = FN15(f); lean_free_object(f); return fn(fx0, fx1, fx2, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12); }
    case 16: { obj* fx0 = fx(0); obj* fx1 = fx(1); obj* fx2 = fx(2); obj* fx3 = fx(3); fn16 fn = FN16(f); lean_free_object(f); return fn(fx0, fx1, fx2, fx3, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12); }
    }
  }
  switch (arity) {
  case 12: { fn12 fn = FN12(f); lean_dec_ref(f); return fn(a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12); }
  case 13: { obj* fx0 = fx(0); lean_inc(fx0); fn13 fn = FN13(f); lean_dec_ref(f); return fn(fx0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12); }
  case 14: { obj* fx0 = fx(0); obj* fx1 = fx(1); lean_inc(fx0); lean_inc(fx1); fn14 fn = FN14(f); lean_dec_ref(f); return fn(fx0, fx1, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12); }
  case 15: { obj* fx0 = fx(0); obj* fx1 = fx(1); obj* fx2 = fx(2); lean_inc(fx0); lean_inc(fx1); lean_inc(fx2); fn15 fn = FN15(f); lean_dec_ref(f); return fn(fx0, fx1, fx2, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12); }
  case 16: { obj* fx0 = fx(0); obj* fx1 = fx(1); obj* fx2 = fx(2); obj* fx3 = fx(3); lean_inc(fx0); lean_inc(fx1); lean_inc(fx2); lean_inc(fx3); fn16 fn = FN16(f); lean_dec_ref(f); return fn(fx0, fx1, fx2, fx3, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12); }
  default:
    lean_assert(arity > 16);
    obj * as[12] = { a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12 };
    obj ** args = static_cast<obj**>(LEAN_ALLOCA(arity*sizeof(obj*))); // NOLINT
    for (unsigned i = 0; i < fixed; i++) { lean_inc(fx(i)); args[i] = fx(i); }
    for (unsigned i = 0; i < 12; i++) args[fixed+i] = as[i];
    fnn fn = FNN(f);
    lean_dec_ref(f);
    return fn(args);
  }
} else if (arity < fixed + 12) {
  obj * as[12] = { a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12 };
  obj ** args = static_cast<obj**>(LEAN_ALLOCA(arity*sizeof(obj*))); // NOLINT
  for (unsigned i = 0; i < fixed; i++) { lean_inc(fx(i)); args[i] = fx(i); }
  for (unsigned i = 0; i < arity-fixed; i++) args[fixed+i] = as[i];
  obj * new_f = curry(f, arity, args);
  lean_dec_ref(f);
  return lean_apply_n(new_f, 12+fixed-arity, &as[arity-fixed]);
} else {
  return fix_args(f, {a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12});
}
}
extern "C" LEAN_EXPORT obj* lean_apply_13(obj* f, obj* a1, obj* a2, obj* a3, obj* a4, obj* a5, obj* a6, obj* a7, obj* a8, obj* a9, obj* a10, obj* a11, obj* a12, obj* a13) {
if (lean_is_scalar(f)) { lean_dec(a1); lean_dec(a2); lean_dec(a3); lean_dec(a4); lean_dec(a5); lean_dec(a6); lean_dec(a7); lean_dec(a8); lean_dec(a9); lean_dec(a10); lean_dec(a11); lean_dec(a12); lean_dec(a13); return f; } // f is an erased proof
unsigned arity = lean_closure_arity(f);
unsigned fixed = lean_closure_num_fixed(f);
if (arity == fixed + 13) {
  if (lean_is_exclusive(f)) {
    switch (arity) {
    case 13: { fn13 fn = FN13(f); lean_free_object(f); return fn(a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13); }
    case 14: { obj* fx0 = fx(0); fn14 fn = FN14(f); lean_free_object(f); return fn(fx0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13); }
    case 15: { obj* fx0 = fx(0); obj* fx1 = fx(1); fn15 fn = FN15(f); lean_free_object(f); return fn(fx0, fx1, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13); }
    case 16: { obj* fx0 = fx(0); obj* fx1 = fx(1); obj* fx2 = fx(2); fn16 fn = FN16(f); lean_free_object(f); return fn(fx0, fx1, fx2, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13); }
    }
  }
  switch (arity) {
  case 13: { fn13 fn = FN13(f); lean_dec_ref(f); return fn(a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13); }
  case 14: { obj* fx0 = fx(0); lean_inc(fx0); fn14 fn = FN14(f); lean_dec_ref(f); return fn(fx0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13); }
  case 15: { obj* fx0 = fx(0); obj* fx1 = fx(1); lean_inc(fx0); lean_inc(fx1); fn15 fn = FN15(f); lean_dec_ref(f); return fn(fx0, fx1, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13); }
  case 16: { obj* fx0 = fx(0); obj* fx1 = fx(1); obj* fx2 = fx(2); lean_inc(fx0); lean_inc(fx1); lean_inc(fx2); fn16 fn = FN16(f); lean_dec_ref(f); return fn(fx0, fx1, fx2, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13); }
  default:
    lean_assert(arity > 16);
    obj * as[13] = { a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13 };
    obj ** args = static_cast<obj**>(LEAN_ALLOCA(arity*sizeof(obj*))); // NOLINT
    for (unsigned i = 0; i < fixed; i++) { lean_inc(fx(i)); args[i] = fx(i); }
    for (unsigned i = 0; i < 13; i++) args[fixed+i] = as[i];
    fnn fn = FNN(f);
    lean_dec_ref(f);
    return fn(args);
  }
} else if (arity < fixed + 13) {
  obj * as[13] = { a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13 };
  obj ** args = static_cast<obj**>(LEAN_ALLOCA(arity*sizeof(obj*))); // NOLINT
  for (unsigned i = 0; i < fixed; i++) { lean_inc(fx(i)); args[i] = fx(i); }
  for (unsigned i = 0; i < arity-fixed; i++) args[fixed+i] = as[i];
  obj * new_f = curry(f, arity, args);
  lean_dec_ref(f);
  return lean_apply_n(new_f, 13+fixed-arity, &as[arity-fixed]);
} else {
  return fix_args(f, {a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13});
}
}
extern "C" LEAN_EXPORT obj* lean_apply_14(obj* f, obj* a1, obj* a2, obj* a3, obj* a4, obj* a5, obj* a6, obj* a7, obj* a8, obj* a9, obj* a10, obj* a11, obj* a12, obj* a13, obj* a14) {
if (lean_is_scalar(f)) { lean_dec(a1); lean_dec(a2); lean_dec(a3); lean_dec(a4); lean_dec(a5); lean_dec(a6); lean_dec(a7); lean_dec(a8); lean_dec(a9); lean_dec(a10); lean_dec(a11); lean_dec(a12); lean_dec(a13); lean_dec(a14); return f; } // f is an erased proof
unsigned arity = lean_closure_arity(f);
unsigned fixed = lean_closure_num_fixed(f);
if (arity == fixed + 14) {
  if (lean_is_exclusive(f)) {
    switch (arity) {
    case 14: { fn14 fn = FN14(f); lean_free_object(f); return fn(a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14); }
    case 15: { obj* fx0 = fx(0); fn15 fn = FN15(f); lean_free_object(f); return fn(fx0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14); }
    case 16: { obj* fx0 = fx(0); obj* fx1 = fx(1); fn16 fn = FN16(f); lean_free_object(f); return fn(fx0, fx1, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14); }
    }
  }
  switch (arity) {
  case 14: { fn14 fn = FN14(f); lean_dec_ref(f); return fn(a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14); }
  case 15: { obj* fx0 = fx(0); lean_inc(fx0); fn15 fn = FN15(f); lean_dec_ref(f); return fn(fx0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14); }
  case 16: { obj* fx0 = fx(0); obj* fx1 = fx(1); lean_inc(fx0); lean_inc(fx1); fn16 fn = FN16(f); lean_dec_ref(f); return fn(fx0, fx1, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14); }
  default:
    lean_assert(arity > 16);
    obj * as[14] = { a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14 };
    obj ** args = static_cast<obj**>(LEAN_ALLOCA(arity*sizeof(obj*))); // NOLINT
    for (unsigned i = 0; i < fixed; i++) { lean_inc(fx(i)); args[i] = fx(i); }
    for (unsigned i = 0; i < 14; i++) args[fixed+i] = as[i];
    fnn fn = FNN(f);
    lean_dec_ref(f);
    return fn(args);
  }
} else if (arity < fixed + 14) {
  obj * as[14] = { a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14 };
  obj ** args = static_cast<obj**>(LEAN_ALLOCA(arity*sizeof(obj*))); // NOLINT
  for (unsigned i = 0; i < fixed; i++) { lean_inc(fx(i)); args[i] = fx(i); }
  for (unsigned i = 0; i < arity-fixed; i++) args[fixed+i] = as[i];
  obj * new_f = curry(f, arity, args);
  lean_dec_ref(f);
  return lean_apply_n(new_f, 14+fixed-arity, &as[arity-fixed]);
} else {
  return fix_args(f, {a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14});
}
}
extern "C" LEAN_EXPORT obj* lean_apply_15(obj* f, obj* a1, obj* a2, obj* a3, obj* a4, obj* a5, obj* a6, obj* a7, obj* a8, obj* a9, obj* a10, obj* a11, obj* a12, obj* a13, obj* a14, obj* a15) {
if (lean_is_scalar(f)) { lean_dec(a1); lean_dec(a2); lean_dec(a3); lean_dec(a4); lean_dec(a5); lean_dec(a6); lean_dec(a7); lean_dec(a8); lean_dec(a9); lean_dec(a10); lean_dec(a11); lean_dec(a12); lean_dec(a13); lean_dec(a14); lean_dec(a15); return f; } // f is an erased proof
unsigned arity = lean_closure_arity(f);
unsigned fixed = lean_closure_num_fixed(f);
if (arity == fixed + 15) {
  if (lean_is_exclusive(f)) {
    switch (arity) {
    case 15: { fn15 fn = FN15(f); lean_free_object(f); return fn(a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15); }
    case 16: { obj* fx0 = fx(0); fn16 fn = FN16(f); lean_free_object(f); return fn(fx0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15); }
    }
  }
  switch (arity) {
  case 15: { fn15 fn = FN15(f); lean_dec_ref(f); return fn(a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15); }
  case 16: { obj* fx0 = fx(0); lean_inc(fx0); fn16 fn = FN16(f); lean_dec_ref(f); return fn(fx0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15); }
  default:
    lean_assert(arity > 16);
    obj * as[15] = { a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15 };
    obj ** args = static_cast<obj**>(LEAN_ALLOCA(arity*sizeof(obj*))); // NOLINT
    for (unsigned i = 0; i < fixed; i++) { lean_inc(fx(i)); args[i] = fx(i); }
    for (unsigned i = 0; i < 15; i++) args[fixed+i] = as[i];
    fnn fn = FNN(f);
    lean_dec_ref(f);
    return fn(args);
  }
} else if (arity < fixed + 15) {
  obj * as[15] = { a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15 };
  obj ** args = static_cast<obj**>(LEAN_ALLOCA(arity*sizeof(obj*))); // NOLINT
  for (unsigned i = 0; i < fixed; i++) { lean_inc(fx(i)); args[i] = fx(i); }
  for (unsigned i = 0; i < arity-fixed; i++) args[fixed+i] = as[i];
  obj * new_f = curry(f, arity, args);
  lean_dec_ref(f);
  return lean_apply_n(new_f, 15+fixed-arity, &as[arity-fixed]);
} else {
  return fix_args(f, {a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15});
}
}
extern "C" LEAN_EXPORT obj* lean_apply_16(obj* f, obj* a1, obj* a2, obj* a3, obj* a4, obj* a5, obj* a6, obj* a7, obj* a8, obj* a9, obj* a10, obj* a11, obj* a12, obj* a13, obj* a14, obj* a15, obj* a16) {
if (lean_is_scalar(f)) { lean_dec(a1); lean_dec(a2); lean_dec(a3); lean_dec(a4); lean_dec(a5); lean_dec(a6); lean_dec(a7); lean_dec(a8); lean_dec(a9); lean_dec(a10); lean_dec(a11); lean_dec(a12); lean_dec(a13); lean_dec(a14); lean_dec(a15); lean_dec(a16); return f; } // f is an erased proof
unsigned arity = lean_closure_arity(f);
unsigned fixed = lean_closure_num_fixed(f);
if (arity == fixed + 16) {
  if (lean_is_exclusive(f)) {
    switch (arity) {
    case 16: { fn16 fn = FN16(f); lean_free_object(f); return fn(a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16); }
    }
  }
  switch (arity) {
  case 16: { fn16 fn = FN16(f); lean_dec_ref(f); return fn(a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16); }
  default:
    lean_assert(arity > 16);
    obj * as[16] = { a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16 };
    obj ** args = static_cast<obj**>(LEAN_ALLOCA(arity*sizeof(obj*))); // NOLINT
    for (unsigned i = 0; i < fixed; i++) { lean_inc(fx(i)); args[i] = fx(i); }
    for (unsigned i = 0; i < 16; i++) args[fixed+i] = as[i];
    fnn fn = FNN(f);
    lean_dec_ref(f);
    return fn(args);
  }
} else if (arity < fixed + 16) {
  obj * as[16] = { a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16 };
  obj ** args = static_cast<obj**>(LEAN_ALLOCA(arity*sizeof(obj*))); // NOLINT
  for (unsigned i = 0; i < fixed; i++) { lean_inc(fx(i)); args[i] = fx(i); }
  for (unsigned i = 0; i < arity-fixed; i++) args[fixed+i] = as[i];
  obj * new_f = curry(f, arity, args);
  lean_dec_ref(f);
  return lean_apply_n(new_f, 16+fixed-arity, &as[arity-fixed]);
} else {
  return fix_args(f, {a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16});
}
}
extern "C" LEAN_EXPORT obj* lean_apply_m(obj* f, unsigned n, obj** as) {
lean_assert(n > 16);
if (lean_is_scalar(f)) { for (unsigned i = 0; i < n; i++) { lean_dec(as[i]); } return f; } // f is an erased proof
unsigned arity = lean_closure_arity(f);
unsigned fixed = lean_closure_num_fixed(f);
if (arity == fixed + n) {
  obj ** args = static_cast<obj**>(LEAN_ALLOCA(arity*sizeof(obj*))); // NOLINT
  for (unsigned i = 0; i < fixed; i++) { lean_inc(fx(i)); args[i] = fx(i); }
  for (unsigned i = 0; i < n; i++) args[fixed+i] = as[i];
  fnn fn = FNN(f);
  lean_dec_ref(f);
  obj * r = fn(args);
  return r;
} else if (arity < fixed + n) {
  obj ** args = static_cast<obj**>(LEAN_ALLOCA(arity*sizeof(obj*))); // NOLINT
  for (unsigned i = 0; i < fixed; i++) { lean_inc(fx(i)); args[i] = fx(i); }
  for (unsigned i = 0; i < arity-fixed; i++) args[fixed+i] = as[i];
  fnn fn = FNN(f);
  lean_dec_ref(f);
  obj * new_f = fn(args);
  return lean_apply_n(new_f, n+fixed-arity, &as[arity-fixed]);
} else {
  return fix_args(f, n, as);
}
}
extern "C" LEAN_EXPORT obj* lean_apply_n(obj* f, unsigned n, obj** as) {
switch (n) {
case 0: lean_unreachable();
case 1: return lean_apply_1(f, as[0]);
case 2: return lean_apply_2(f, as[0], as[1]);
case 3: return lean_apply_3(f, as[0], as[1], as[2]);
case 4: return lean_apply_4(f, as[0], as[1], as[2], as[3]);
case 5: return lean_apply_5(f, as[0], as[1], as[2], as[3], as[4]);
case 6: return lean_apply_6(f, as[0], as[1], as[2], as[3], as[4], as[5]);
case 7: return lean_apply_7(f, as[0], as[1], as[2], as[3], as[4], as[5], as[6]);
case 8: return lean_apply_8(f, as[0], as[1], as[2], as[3], as[4], as[5], as[6], as[7]);
case 9: return lean_apply_9(f, as[0], as[1], as[2], as[3], as[4], as[5], as[6], as[7], as[8]);
case 10: return lean_apply_10(f, as[0], as[1], as[2], as[3], as[4], as[5], as[6], as[7], as[8], as[9]);
case 11: return lean_apply_11(f, as[0], as[1], as[2], as[3], as[4], as[5], as[6], as[7], as[8], as[9], as[10]);
case 12: return lean_apply_12(f, as[0], as[1], as[2], as[3], as[4], as[5], as[6], as[7], as[8], as[9], as[10], as[11]);
case 13: return lean_apply_13(f, as[0], as[1], as[2], as[3], as[4], as[5], as[6], as[7], as[8], as[9], as[10], as[11], as[12]);
case 14: return lean_apply_14(f, as[0], as[1], as[2], as[3], as[4], as[5], as[6], as[7], as[8], as[9], as[10], as[11], as[12], as[13]);
case 15: return lean_apply_15(f, as[0], as[1], as[2], as[3], as[4], as[5], as[6], as[7], as[8], as[9], as[10], as[11], as[12], as[13], as[14]);
case 16: return lean_apply_16(f, as[0], as[1], as[2], as[3], as[4], as[5], as[6], as[7], as[8], as[9], as[10], as[11], as[12], as[13], as[14], as[15]);
default: return lean_apply_m(f, n, as);
}
}
}
