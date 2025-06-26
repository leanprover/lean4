// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.SimpUtil
// Imports: Lean.Meta.Tactic.Simp.Simproc Lean.Meta.Tactic.Grind.Simp Lean.Meta.Tactic.Grind.MatchDiscrOnly Lean.Meta.Tactic.Grind.MatchCond Lean.Meta.Tactic.Simp.BuiltinSimprocs.List
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkSimpExt(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3_;
static lean_object* l_Lean_Meta_Grind_simpBoolEq___redArg___closed__13;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Meta_Simp_getSEvalSimprocs___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_simpBoolEq___redArg___closed__1;
static lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpBoolEq_declare__14___closed__8____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_844_;
static lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__11;
static lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__7;
static lean_object* l_Lean_Meta_Grind_normalizeImp___closed__8;
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_isEmpty___at___Lean_Meta_Grind_registerNormTheorems_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_registerNormTheorems(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpBoolEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_normalizeImp___closed__6;
static lean_object* l_Lean_Meta_Grind_normalizeImp___closed__7;
lean_object* l_Lean_Meta_Grind_addSimpMatchDiscrsOnly(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_simpBoolEq___redArg___closed__7;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Grind_registerNormTheorems_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getSimprocs___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpBoolEq___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_simpBoolEq___redArg___closed__10;
static lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__5;
static lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpBoolEq_declare__14___closed__6____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_844_;
static lean_object* l_Lean_Meta_Grind_simpBoolEq___redArg___closed__6;
static lean_object* l_Lean_Meta_Grind_normalizeImp___closed__0;
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__12;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getSimpContext(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_normalizeImp___closed__5;
lean_object* l_Lean_Meta_getSimpCongrTheorems___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_simpBoolEq___redArg___closed__8;
static lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__10;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_normExt;
static lean_object* l_Lean_Meta_Grind_normalizeImp___closed__4;
static lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpBoolEq_declare__14___closed__3____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_844_;
static lean_object* l_Lean_Meta_Grind_simpBoolEq___redArg___closed__12;
lean_object* l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_simp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_normalizeImp___closed__3;
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_Simprocs_add(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpBoolEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_getSimprocs___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getSimpContext___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getSimprocs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_mkContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Grind_registerNormTheorems_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_Simprocs_erase(lean_object*, lean_object*);
lean_object* l_Lean_Meta_addSimpTheorem(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3_;
static lean_object* l_Lean_Meta_Grind_simpBoolEq___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getSimprocs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpBoolEq_declare__14____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_844_(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__3;
static lean_object* l_Lean_Meta_Grind_initFn___closed__3____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3_;
static lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__0;
static lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpBoolEq_declare__14___closed__9____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_844_;
static lean_object* l_Lean_Meta_Grind_registerNormTheorems___closed__2;
static lean_object* l_Lean_Meta_Grind_getSimprocs___redArg___closed__3;
static lean_object* l_Lean_Meta_Grind_simpBoolEq___redArg___closed__11;
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isEmpty___at___Lean_Meta_Grind_registerNormTheorems_spec__2___redArg___boxed(lean_object*);
lean_object* l_Lean_Meta_Simp_registerBuiltinSimproc(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Grind_registerNormTheorems_spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getSimpContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_initFn___closed__4____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3_;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_initFn____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3_(lean_object*);
static lean_object* l_Lean_Meta_Grind_simpBoolEq___redArg___closed__4;
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Grind_registerNormTheorems_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpBoolEq_declare__14___closed__4____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_844_;
LEAN_EXPORT lean_object* lean_grind_normalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_getSimprocs___redArg___closed__2;
static lean_object* l_Lean_Meta_Grind_simpBoolEq___redArg___closed__5;
lean_object* l_Lean_Expr_getAppFn(lean_object*);
static lean_object* l_Lean_Meta_Grind_simpBoolEq___redArg___closed__0;
static lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__6;
static lean_object* l_Lean_Meta_Grind_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3_;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_getSimprocs___redArg___closed__1;
static lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpBoolEq_declare__14___closed__7____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_844_;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isEmpty___at___Lean_Meta_Grind_registerNormTheorems_spec__2___boxed(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__8;
static lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__4;
static lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpBoolEq_declare__14___closed__2____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_844_;
size_t lean_usize_add(size_t, size_t);
static lean_object* l_Lean_Meta_Grind_normalizeImp___closed__1;
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
static lean_object* l_Lean_Meta_Grind_simpBoolEq___redArg___closed__9;
static lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpBoolEq_declare__14___closed__1____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_844_;
static lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__9;
lean_object* l_Lean_Name_mkStr1(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__2;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_normalizeImp___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_registerNormTheorems___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SimpExtension_getTheorems___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_registerNormTheorems___closed__1;
static lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__1;
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget(lean_object*);
static lean_object* l_Lean_Meta_Grind_simpBoolEq___redArg___closed__3;
lean_object* l_Lean_Meta_Grind_addPreMatchCondSimproc(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getSimprocs___redArg___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_PersistentHashMap_Node_isEmpty___redArg(lean_object*);
static lean_object* l_Lean_Meta_Grind_registerNormTheorems___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getSimpContext___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_isEmpty___at___Lean_Meta_Grind_registerNormTheorems_spec__2(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpBoolEq_declare__14___closed__5____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_844_;
static lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpBoolEq_declare__14___closed__0____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_844_;
static lean_object* l_Lean_Meta_Grind_getSimpContext___redArg___closed__0;
static lean_object* _init_l_Lean_Meta_Grind_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Meta", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Grind", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_initFn___closed__3____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("normExt", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_initFn___closed__4____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_Grind_initFn___closed__3____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3_;
x_2 = l_Lean_Meta_Grind_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3_;
x_3 = l_Lean_Meta_Grind_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3_;
x_4 = l_Lean_Meta_Grind_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3_;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_initFn____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_Grind_initFn___closed__4____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3_;
x_3 = l_Lean_Meta_mkSimpExt(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Grind_registerNormTheorems_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_5, x_4);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_6);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_19; uint8_t x_20; lean_object* x_21; 
lean_dec(x_6);
x_14 = lean_array_uget(x_3, x_5);
x_15 = lean_box(0);
x_16 = lean_box(0);
x_17 = lean_unsigned_to_nat(1000u);
x_18 = lean_unbox(x_15);
x_19 = lean_unbox(x_15);
x_20 = lean_unbox(x_16);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_1);
x_21 = l_Lean_Meta_addSimpTheorem(x_1, x_14, x_18, x_19, x_20, x_17, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; size_t x_23; size_t x_24; 
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = 1;
x_24 = lean_usize_add(x_5, x_23);
lean_inc(x_2);
{
size_t _tmp_4 = x_24;
lean_object* _tmp_5 = x_2;
lean_object* _tmp_10 = x_22;
x_5 = _tmp_4;
x_6 = _tmp_5;
x_11 = _tmp_10;
}
goto _start;
}
else
{
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Grind_registerNormTheorems_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_5, x_4);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_6);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_19; lean_object* x_20; 
lean_dec(x_6);
x_14 = lean_array_uget(x_3, x_5);
x_15 = lean_box(0);
x_16 = lean_box(0);
x_17 = lean_unsigned_to_nat(1000u);
x_18 = lean_unbox(x_15);
x_19 = lean_unbox(x_16);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_1);
x_20 = l_Lean_Meta_addSimpTheorem(x_1, x_14, x_12, x_18, x_19, x_17, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; size_t x_22; size_t x_23; 
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = 1;
x_23 = lean_usize_add(x_5, x_22);
lean_inc(x_2);
{
size_t _tmp_4 = x_23;
lean_object* _tmp_5 = x_2;
lean_object* _tmp_10 = x_21;
x_5 = _tmp_4;
x_6 = _tmp_5;
x_11 = _tmp_10;
}
goto _start;
}
else
{
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
return x_20;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_isEmpty___at___Lean_Meta_Grind_registerNormTheorems_spec__2___redArg(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_Lean_PersistentHashMap_Node_isEmpty___redArg(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_isEmpty___at___Lean_Meta_Grind_registerNormTheorems_spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Lean_PersistentHashMap_Node_isEmpty___redArg(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_registerNormTheorems___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Grind_normExt;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_registerNormTheorems___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("`grind` normalization theorems have already been initialized", 60, 60);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_registerNormTheorems___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_registerNormTheorems___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_registerNormTheorems(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_8 = l_Lean_Meta_Grind_registerNormTheorems___closed__0;
x_9 = l_Lean_Meta_SimpExtension_getTheorems___redArg(x_8, x_6, x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 2);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_PersistentHashMap_Node_isEmpty___redArg(x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = l_Lean_Meta_Grind_registerNormTheorems___closed__2;
x_15 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_14, x_3, x_4, x_5, x_6, x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_15;
}
else
{
lean_object* x_16; size_t x_17; size_t x_18; lean_object* x_19; 
x_16 = lean_box(0);
x_17 = lean_array_size(x_1);
x_18 = 0;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_19 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Grind_registerNormTheorems_spec__0(x_8, x_16, x_1, x_17, x_18, x_16, x_3, x_4, x_5, x_6, x_11);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; size_t x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_array_size(x_2);
x_22 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Grind_registerNormTheorems_spec__1(x_8, x_16, x_2, x_21, x_18, x_16, x_3, x_4, x_5, x_6, x_20);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_22, 0);
lean_dec(x_24);
lean_ctor_set(x_22, 0, x_16);
return x_22;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_dec(x_22);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_16);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
else
{
return x_22;
}
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Grind_registerNormTheorems_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_14 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Grind_registerNormTheorems_spec__0(x_1, x_2, x_3, x_12, x_13, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_3);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Grind_registerNormTheorems_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_14 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Grind_registerNormTheorems_spec__1(x_1, x_2, x_3, x_12, x_13, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_3);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isEmpty___at___Lean_Meta_Grind_registerNormTheorems_spec__2___redArg___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_PersistentHashMap_isEmpty___at___Lean_Meta_Grind_registerNormTheorems_spec__2___redArg(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isEmpty___at___Lean_Meta_Grind_registerNormTheorems_spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_PersistentHashMap_isEmpty___at___Lean_Meta_Grind_registerNormTheorems_spec__2(x_1, x_2);
lean_dec(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_registerNormTheorems___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Grind_registerNormTheorems(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Bool", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("not", 3, 3);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__1;
x_2 = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("BEq", 3, 3);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("beq", 3, 3);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__4;
x_2 = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__3;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Decidable", 9, 9);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("decide", 6, 6);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__7;
x_2 = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__6;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("and", 3, 3);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__9;
x_2 = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("or", 2, 2);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__11;
x_2 = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_10; uint8_t x_11; 
x_10 = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__10;
x_11 = lean_name_eq(x_1, x_10);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__12;
x_13 = lean_name_eq(x_1, x_12);
x_2 = x_13;
goto block_9;
}
else
{
x_2 = x_11;
goto block_9;
}
block_9:
{
if (x_2 == 0)
{
lean_object* x_3; uint8_t x_4; 
x_3 = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__2;
x_4 = lean_name_eq(x_1, x_3);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__5;
x_6 = lean_name_eq(x_1, x_5);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__8;
x_8 = lean_name_eq(x_1, x_7);
return x_8;
}
else
{
return x_6;
}
}
else
{
return x_4;
}
}
else
{
return x_2;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpBoolEq___redArg___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpBoolEq___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Eq", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpBoolEq___redArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_simpBoolEq___redArg___closed__1;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpBoolEq___redArg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("true", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpBoolEq___redArg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Grind_simpBoolEq___redArg___closed__3;
x_2 = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpBoolEq___redArg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Grind_simpBoolEq___redArg___closed__4;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpBoolEq___redArg___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("bool_eq_to_prop", 15, 15);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpBoolEq___redArg___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_Grind_simpBoolEq___redArg___closed__6;
x_2 = l_Lean_Meta_Grind_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3_;
x_3 = l_Lean_Meta_Grind_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3_;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpBoolEq___redArg___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Grind_simpBoolEq___redArg___closed__7;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpBoolEq___redArg___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("flip_bool_eq", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpBoolEq___redArg___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_Grind_simpBoolEq___redArg___closed__9;
x_2 = l_Lean_Meta_Grind_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3_;
x_3 = l_Lean_Meta_Grind_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3_;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpBoolEq___redArg___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Grind_simpBoolEq___redArg___closed__10;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpBoolEq___redArg___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("false", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpBoolEq___redArg___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Grind_simpBoolEq___redArg___closed__12;
x_2 = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpBoolEq___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_14; uint8_t x_15; 
x_7 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_1, x_3, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_10 = x_7;
} else {
 lean_dec_ref(x_7);
 x_10 = lean_box(0);
}
x_14 = l_Lean_Expr_cleanupAnnotations(x_8);
x_15 = l_Lean_Expr_isApp(x_14);
if (x_15 == 0)
{
lean_dec(x_14);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
goto block_13;
}
else
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
x_17 = l_Lean_Expr_appFnCleanup___redArg(x_14);
x_18 = l_Lean_Expr_isApp(x_17);
if (x_18 == 0)
{
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
goto block_13;
}
else
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
x_20 = l_Lean_Expr_appFnCleanup___redArg(x_17);
x_21 = l_Lean_Expr_isApp(x_20);
if (x_21 == 0)
{
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_16);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
goto block_13;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; uint8_t x_26; 
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
x_23 = l_Lean_Expr_appFnCleanup___redArg(x_20);
x_24 = l_Lean_Meta_Grind_simpBoolEq___redArg___closed__2;
x_25 = l_Lean_Expr_isConstOf(x_23, x_24);
if (x_25 == 0)
{
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_19);
lean_dec(x_16);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
goto block_13;
}
else
{
lean_object* x_53; 
lean_dec(x_10);
x_53 = l_Lean_Expr_getAppFn(x_16);
if (lean_obj_tag(x_53) == 4)
{
lean_object* x_54; lean_object* x_55; uint8_t x_56; uint8_t x_67; lean_object* x_79; uint8_t x_80; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
lean_dec(x_53);
x_79 = l_Lean_Meta_Grind_simpBoolEq___redArg___closed__4;
x_80 = lean_name_eq(x_54, x_79);
if (x_80 == 0)
{
lean_object* x_81; uint8_t x_82; 
x_81 = l_Lean_Meta_Grind_simpBoolEq___redArg___closed__13;
x_82 = lean_name_eq(x_54, x_81);
x_67 = x_82;
goto block_78;
}
else
{
x_67 = x_80;
goto block_78;
}
block_66:
{
if (x_56 == 0)
{
uint8_t x_57; 
x_57 = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget(x_55);
lean_dec(x_55);
if (x_57 == 0)
{
uint8_t x_58; 
x_58 = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget(x_54);
lean_dec(x_54);
x_26 = x_58;
goto block_52;
}
else
{
lean_dec(x_54);
x_26 = x_57;
goto block_52;
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_inc(x_19);
lean_inc(x_16);
x_59 = l_Lean_mkApp3(x_23, x_22, x_16, x_19);
x_60 = l_Lean_Meta_Grind_simpBoolEq___redArg___closed__11;
x_61 = l_Lean_mkAppB(x_60, x_19, x_16);
x_62 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_62, 0, x_61);
x_63 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_63, 0, x_59);
lean_ctor_set(x_63, 1, x_62);
lean_ctor_set_uint8(x_63, sizeof(void*)*2, x_25);
x_64 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_64, 0, x_63);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_9);
return x_65;
}
}
block_78:
{
if (x_67 == 0)
{
lean_object* x_68; 
x_68 = l_Lean_Expr_getAppFn(x_19);
if (lean_obj_tag(x_68) == 4)
{
lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
lean_dec(x_68);
x_70 = l_Lean_Meta_Grind_simpBoolEq___redArg___closed__4;
x_71 = lean_name_eq(x_69, x_70);
if (x_71 == 0)
{
lean_object* x_72; uint8_t x_73; 
x_72 = l_Lean_Meta_Grind_simpBoolEq___redArg___closed__13;
x_73 = lean_name_eq(x_69, x_72);
x_55 = x_69;
x_56 = x_73;
goto block_66;
}
else
{
x_55 = x_69;
x_56 = x_71;
goto block_66;
}
}
else
{
lean_object* x_74; lean_object* x_75; 
lean_dec(x_68);
lean_dec(x_54);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_19);
lean_dec(x_16);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_74 = l_Lean_Meta_Grind_simpBoolEq___redArg___closed__0;
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_9);
return x_75;
}
}
else
{
lean_object* x_76; lean_object* x_77; 
lean_dec(x_54);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_19);
lean_dec(x_16);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_76 = l_Lean_Meta_Grind_simpBoolEq___redArg___closed__0;
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_9);
return x_77;
}
}
}
else
{
lean_object* x_83; lean_object* x_84; 
lean_dec(x_53);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_19);
lean_dec(x_16);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_83 = l_Lean_Meta_Grind_simpBoolEq___redArg___closed__0;
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_9);
return x_84;
}
}
block_52:
{
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_19);
lean_dec(x_16);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_27 = l_Lean_Meta_Grind_simpBoolEq___redArg___closed__0;
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_9);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_29 = l_Lean_Meta_Grind_simpBoolEq___redArg___closed__5;
lean_inc(x_19);
lean_inc(x_22);
lean_inc(x_23);
x_30 = l_Lean_mkApp3(x_23, x_22, x_19, x_29);
lean_inc(x_16);
x_31 = l_Lean_mkApp3(x_23, x_22, x_16, x_29);
x_32 = l_Lean_Meta_mkEq(x_30, x_31, x_2, x_3, x_4, x_5, x_9);
if (lean_obj_tag(x_32) == 0)
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_34 = lean_ctor_get(x_32, 0);
x_35 = l_Lean_Meta_Grind_simpBoolEq___redArg___closed__8;
x_36 = l_Lean_mkAppB(x_35, x_19, x_16);
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_36);
x_38 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_38, 0, x_34);
lean_ctor_set(x_38, 1, x_37);
lean_ctor_set_uint8(x_38, sizeof(void*)*2, x_25);
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_32, 0, x_39);
return x_32;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_40 = lean_ctor_get(x_32, 0);
x_41 = lean_ctor_get(x_32, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_32);
x_42 = l_Lean_Meta_Grind_simpBoolEq___redArg___closed__8;
x_43 = l_Lean_mkAppB(x_42, x_19, x_16);
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_43);
x_45 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_45, 0, x_40);
lean_ctor_set(x_45, 1, x_44);
lean_ctor_set_uint8(x_45, sizeof(void*)*2, x_25);
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_45);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_41);
return x_47;
}
}
else
{
uint8_t x_48; 
lean_dec(x_19);
lean_dec(x_16);
x_48 = !lean_is_exclusive(x_32);
if (x_48 == 0)
{
return x_32;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_32, 0);
x_50 = lean_ctor_get(x_32, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_32);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
}
}
}
}
block_13:
{
lean_object* x_11; lean_object* x_12; 
x_11 = l_Lean_Meta_Grind_simpBoolEq___redArg___closed__0;
if (lean_is_scalar(x_10)) {
 x_12 = lean_alloc_ctor(0, 2, 0);
} else {
 x_12 = x_10;
}
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_9);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpBoolEq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Grind_simpBoolEq___redArg(x_1, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpBoolEq___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Grind_simpBoolEq(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpBoolEq_declare__14___closed__0____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_844_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("simpBoolEq", 10, 10);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpBoolEq_declare__14___closed__1____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_844_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpBoolEq_declare__14___closed__0____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_844_;
x_2 = l_Lean_Meta_Grind_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3_;
x_3 = l_Lean_Meta_Grind_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3_;
x_4 = l_Lean_Meta_Grind_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3_;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpBoolEq_declare__14___closed__2____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_844_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(3u);
x_2 = l_Lean_Meta_Grind_simpBoolEq___redArg___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpBoolEq_declare__14___closed__3____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_844_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpBoolEq_declare__14___closed__4____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_844_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpBoolEq_declare__14___closed__3____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_844_;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpBoolEq_declare__14___closed__5____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_844_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpBoolEq_declare__14___closed__6____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_844_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpBoolEq_declare__14___closed__2____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_844_;
x_2 = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpBoolEq_declare__14___closed__5____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_844_;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpBoolEq_declare__14___closed__7____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_844_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpBoolEq_declare__14___closed__4____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_844_;
x_2 = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpBoolEq_declare__14___closed__6____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_844_;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpBoolEq_declare__14___closed__8____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_844_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(3);
x_2 = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpBoolEq_declare__14___closed__7____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_844_;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpBoolEq_declare__14___closed__9____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_844_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(3);
x_2 = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpBoolEq_declare__14___closed__8____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_844_;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpBoolEq_declare__14____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_844_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpBoolEq_declare__14___closed__1____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_844_;
x_3 = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpBoolEq_declare__14___closed__9____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_844_;
x_4 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_simpBoolEq___boxed), 9, 0);
x_5 = l_Lean_Meta_Simp_registerBuiltinSimproc(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_Grind_getSimprocs___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("List", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_getSimprocs___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("reduceReplicate", 15, 15);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_getSimprocs___redArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Grind_getSimprocs___redArg___closed__1;
x_2 = l_Lean_Meta_Grind_getSimprocs___redArg___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_getSimprocs___redArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getSimprocs___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = l_Lean_Meta_Simp_getSEvalSimprocs___redArg(x_2, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = l_Lean_Meta_Grind_getSimprocs___redArg___closed__2;
x_8 = l_Lean_Meta_Simp_Simprocs_erase(x_5, x_7);
x_9 = l_Lean_Meta_Grind_addSimpMatchDiscrsOnly(x_8, x_1, x_2, x_6);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_Meta_Grind_addPreMatchCondSimproc(x_10, x_1, x_2, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpBoolEq_declare__14___closed__1____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_844_;
x_16 = lean_box(0);
x_17 = lean_unbox(x_16);
x_18 = l_Lean_Meta_Simp_Simprocs_add(x_13, x_15, x_17, x_1, x_2, x_14);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = l_Lean_Meta_Grind_getSimprocs___redArg___closed__3;
x_22 = lean_array_push(x_21, x_20);
lean_ctor_set(x_18, 0, x_22);
return x_18;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_18, 0);
x_24 = lean_ctor_get(x_18, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_18);
x_25 = l_Lean_Meta_Grind_getSimprocs___redArg___closed__3;
x_26 = lean_array_push(x_25, x_23);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_24);
return x_27;
}
}
else
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_18);
if (x_28 == 0)
{
return x_18;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_18, 0);
x_30 = lean_ctor_get(x_18, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_18);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
else
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_12);
if (x_32 == 0)
{
return x_12;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_12, 0);
x_34 = lean_ctor_get(x_12, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_12);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
else
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_9);
if (x_36 == 0)
{
return x_9;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_9, 0);
x_38 = lean_ctor_get(x_9, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_9);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getSimprocs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Meta_Grind_getSimprocs___redArg(x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getSimprocs___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_Grind_getSimprocs___redArg(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getSimprocs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Meta_Grind_getSimprocs(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_Meta_Grind_getSimpContext___redArg___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getSimpContext___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_21; uint8_t x_22; uint8_t x_23; uint8_t x_24; uint8_t x_25; uint8_t x_26; uint8_t x_27; uint8_t x_28; uint8_t x_29; uint8_t x_30; uint8_t x_31; uint8_t x_32; uint8_t x_33; uint8_t x_34; uint8_t x_35; uint8_t x_36; uint8_t x_37; uint8_t x_38; uint8_t x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_5 = l_Lean_Meta_Grind_registerNormTheorems___closed__0;
x_6 = l_Lean_Meta_SimpExtension_getTheorems___redArg(x_5, x_3, x_4);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_Lean_Meta_getSimpCongrTheorems___redArg(x_3, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get_uint8(x_1, sizeof(void*)*6 + 15);
x_13 = lean_ctor_get_uint8(x_1, sizeof(void*)*6 + 16);
x_14 = lean_unsigned_to_nat(100000u);
x_15 = lean_unsigned_to_nat(2u);
x_16 = lean_box(0);
x_17 = lean_box(1);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 2, 23);
lean_ctor_set(x_19, 0, x_14);
lean_ctor_set(x_19, 1, x_15);
x_20 = lean_unbox(x_16);
lean_ctor_set_uint8(x_19, sizeof(void*)*2, x_20);
x_21 = lean_unbox(x_17);
lean_ctor_set_uint8(x_19, sizeof(void*)*2 + 1, x_21);
x_22 = lean_unbox(x_16);
lean_ctor_set_uint8(x_19, sizeof(void*)*2 + 2, x_22);
lean_ctor_set_uint8(x_19, sizeof(void*)*2 + 3, x_13);
x_23 = lean_unbox(x_17);
lean_ctor_set_uint8(x_19, sizeof(void*)*2 + 4, x_23);
x_24 = lean_unbox(x_17);
lean_ctor_set_uint8(x_19, sizeof(void*)*2 + 5, x_24);
x_25 = lean_unbox(x_18);
lean_ctor_set_uint8(x_19, sizeof(void*)*2 + 6, x_25);
x_26 = lean_unbox(x_17);
lean_ctor_set_uint8(x_19, sizeof(void*)*2 + 7, x_26);
x_27 = lean_unbox(x_17);
lean_ctor_set_uint8(x_19, sizeof(void*)*2 + 8, x_27);
x_28 = lean_unbox(x_16);
lean_ctor_set_uint8(x_19, sizeof(void*)*2 + 9, x_28);
x_29 = lean_unbox(x_17);
lean_ctor_set_uint8(x_19, sizeof(void*)*2 + 10, x_29);
x_30 = lean_unbox(x_16);
lean_ctor_set_uint8(x_19, sizeof(void*)*2 + 11, x_30);
x_31 = lean_unbox(x_17);
lean_ctor_set_uint8(x_19, sizeof(void*)*2 + 12, x_31);
x_32 = lean_unbox(x_17);
lean_ctor_set_uint8(x_19, sizeof(void*)*2 + 13, x_32);
x_33 = lean_unbox(x_16);
lean_ctor_set_uint8(x_19, sizeof(void*)*2 + 14, x_33);
x_34 = lean_unbox(x_16);
lean_ctor_set_uint8(x_19, sizeof(void*)*2 + 15, x_34);
lean_ctor_set_uint8(x_19, sizeof(void*)*2 + 16, x_12);
x_35 = lean_unbox(x_17);
lean_ctor_set_uint8(x_19, sizeof(void*)*2 + 17, x_35);
x_36 = lean_unbox(x_17);
lean_ctor_set_uint8(x_19, sizeof(void*)*2 + 18, x_36);
x_37 = lean_unbox(x_17);
lean_ctor_set_uint8(x_19, sizeof(void*)*2 + 19, x_37);
x_38 = lean_unbox(x_16);
lean_ctor_set_uint8(x_19, sizeof(void*)*2 + 20, x_38);
x_39 = lean_unbox(x_17);
lean_ctor_set_uint8(x_19, sizeof(void*)*2 + 21, x_39);
x_40 = lean_unbox(x_17);
lean_ctor_set_uint8(x_19, sizeof(void*)*2 + 22, x_40);
x_41 = l_Lean_Meta_Grind_getSimpContext___redArg___closed__0;
x_42 = lean_array_push(x_41, x_7);
x_43 = l_Lean_Meta_Simp_mkContext___redArg(x_19, x_42, x_10, x_2, x_3, x_11);
return x_43;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getSimpContext(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_Grind_getSimpContext___redArg(x_1, x_2, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getSimpContext___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_Grind_getSimpContext___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getSimpContext___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_Grind_getSimpContext(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
static lean_object* _init_l_Lean_Meta_Grind_normalizeImp___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_normalizeImp___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_normalizeImp___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_normalizeImp___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Meta_Grind_normalizeImp___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_normalizeImp___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_normalizeImp___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_normalizeImp___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_normalizeImp___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_normalizeImp___closed__4;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_normalizeImp___closed__6() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Meta_Grind_normalizeImp___closed__4;
x_4 = l_Lean_Meta_Grind_normalizeImp___closed__5;
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_2);
lean_ctor_set_usize(x_5, 4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_Grind_normalizeImp___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_Grind_normalizeImp___closed__6;
x_2 = l_Lean_Meta_Grind_normalizeImp___closed__3;
x_3 = l_Lean_Meta_Grind_normalizeImp___closed__1;
x_4 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set(x_4, 2, x_2);
lean_ctor_set(x_4, 3, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Grind_normalizeImp___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Grind_normalizeImp___closed__7;
x_2 = l_Lean_Meta_Grind_normalizeImp___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* lean_grind_normalize(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = l_Lean_Meta_Grind_getSimpContext___redArg(x_2, x_3, x_6, x_7);
lean_dec(x_2);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_Meta_Grind_getSimprocs___redArg(x_5, x_6, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_box(0);
x_15 = l_Lean_Meta_Grind_normalizeImp___closed__8;
x_16 = l_Lean_Meta_simp(x_1, x_9, x_12, x_14, x_15, x_3, x_4, x_5, x_6, x_13);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec(x_17);
x_19 = !lean_is_exclusive(x_16);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_16, 0);
lean_dec(x_20);
x_21 = lean_ctor_get(x_18, 0);
lean_inc(x_21);
lean_dec(x_18);
lean_ctor_set(x_16, 0, x_21);
return x_16;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_16, 1);
lean_inc(x_22);
lean_dec(x_16);
x_23 = lean_ctor_get(x_18, 0);
lean_inc(x_23);
lean_dec(x_18);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
return x_24;
}
}
else
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_16);
if (x_25 == 0)
{
return x_16;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_16, 0);
x_27 = lean_ctor_get(x_16, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_16);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
else
{
uint8_t x_29; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_29 = !lean_is_exclusive(x_11);
if (x_29 == 0)
{
return x_11;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_11, 0);
x_31 = lean_ctor_get(x_11, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_11);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
lean_object* initialize_Lean_Meta_Tactic_Simp_Simproc(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Simp(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_MatchDiscrOnly(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_MatchCond(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_SimpUtil(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Simp_Simproc(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Simp(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_MatchDiscrOnly(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_MatchCond(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_Grind_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3_ = _init_l_Lean_Meta_Grind_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3_();
lean_mark_persistent(l_Lean_Meta_Grind_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3_);
l_Lean_Meta_Grind_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3_ = _init_l_Lean_Meta_Grind_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3_();
lean_mark_persistent(l_Lean_Meta_Grind_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3_);
l_Lean_Meta_Grind_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3_ = _init_l_Lean_Meta_Grind_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3_();
lean_mark_persistent(l_Lean_Meta_Grind_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3_);
l_Lean_Meta_Grind_initFn___closed__3____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3_ = _init_l_Lean_Meta_Grind_initFn___closed__3____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3_();
lean_mark_persistent(l_Lean_Meta_Grind_initFn___closed__3____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3_);
l_Lean_Meta_Grind_initFn___closed__4____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3_ = _init_l_Lean_Meta_Grind_initFn___closed__4____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3_();
lean_mark_persistent(l_Lean_Meta_Grind_initFn___closed__4____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3_);
if (builtin) {res = l_Lean_Meta_Grind_initFn____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_Grind_normExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_Grind_normExt);
lean_dec_ref(res);
}l_Lean_Meta_Grind_registerNormTheorems___closed__0 = _init_l_Lean_Meta_Grind_registerNormTheorems___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_registerNormTheorems___closed__0);
l_Lean_Meta_Grind_registerNormTheorems___closed__1 = _init_l_Lean_Meta_Grind_registerNormTheorems___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_registerNormTheorems___closed__1);
l_Lean_Meta_Grind_registerNormTheorems___closed__2 = _init_l_Lean_Meta_Grind_registerNormTheorems___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_registerNormTheorems___closed__2);
l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__0 = _init_l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__0();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__0);
l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__1 = _init_l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__1);
l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__2 = _init_l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__2);
l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__3 = _init_l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__3);
l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__4 = _init_l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__4();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__4);
l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__5 = _init_l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__5();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__5);
l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__6 = _init_l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__6();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__6);
l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__7 = _init_l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__7();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__7);
l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__8 = _init_l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__8();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__8);
l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__9 = _init_l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__9();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__9);
l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__10 = _init_l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__10();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__10);
l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__11 = _init_l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__11();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__11);
l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__12 = _init_l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__12();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__12);
l_Lean_Meta_Grind_simpBoolEq___redArg___closed__0 = _init_l_Lean_Meta_Grind_simpBoolEq___redArg___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_simpBoolEq___redArg___closed__0);
l_Lean_Meta_Grind_simpBoolEq___redArg___closed__1 = _init_l_Lean_Meta_Grind_simpBoolEq___redArg___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_simpBoolEq___redArg___closed__1);
l_Lean_Meta_Grind_simpBoolEq___redArg___closed__2 = _init_l_Lean_Meta_Grind_simpBoolEq___redArg___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_simpBoolEq___redArg___closed__2);
l_Lean_Meta_Grind_simpBoolEq___redArg___closed__3 = _init_l_Lean_Meta_Grind_simpBoolEq___redArg___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_simpBoolEq___redArg___closed__3);
l_Lean_Meta_Grind_simpBoolEq___redArg___closed__4 = _init_l_Lean_Meta_Grind_simpBoolEq___redArg___closed__4();
lean_mark_persistent(l_Lean_Meta_Grind_simpBoolEq___redArg___closed__4);
l_Lean_Meta_Grind_simpBoolEq___redArg___closed__5 = _init_l_Lean_Meta_Grind_simpBoolEq___redArg___closed__5();
lean_mark_persistent(l_Lean_Meta_Grind_simpBoolEq___redArg___closed__5);
l_Lean_Meta_Grind_simpBoolEq___redArg___closed__6 = _init_l_Lean_Meta_Grind_simpBoolEq___redArg___closed__6();
lean_mark_persistent(l_Lean_Meta_Grind_simpBoolEq___redArg___closed__6);
l_Lean_Meta_Grind_simpBoolEq___redArg___closed__7 = _init_l_Lean_Meta_Grind_simpBoolEq___redArg___closed__7();
lean_mark_persistent(l_Lean_Meta_Grind_simpBoolEq___redArg___closed__7);
l_Lean_Meta_Grind_simpBoolEq___redArg___closed__8 = _init_l_Lean_Meta_Grind_simpBoolEq___redArg___closed__8();
lean_mark_persistent(l_Lean_Meta_Grind_simpBoolEq___redArg___closed__8);
l_Lean_Meta_Grind_simpBoolEq___redArg___closed__9 = _init_l_Lean_Meta_Grind_simpBoolEq___redArg___closed__9();
lean_mark_persistent(l_Lean_Meta_Grind_simpBoolEq___redArg___closed__9);
l_Lean_Meta_Grind_simpBoolEq___redArg___closed__10 = _init_l_Lean_Meta_Grind_simpBoolEq___redArg___closed__10();
lean_mark_persistent(l_Lean_Meta_Grind_simpBoolEq___redArg___closed__10);
l_Lean_Meta_Grind_simpBoolEq___redArg___closed__11 = _init_l_Lean_Meta_Grind_simpBoolEq___redArg___closed__11();
lean_mark_persistent(l_Lean_Meta_Grind_simpBoolEq___redArg___closed__11);
l_Lean_Meta_Grind_simpBoolEq___redArg___closed__12 = _init_l_Lean_Meta_Grind_simpBoolEq___redArg___closed__12();
lean_mark_persistent(l_Lean_Meta_Grind_simpBoolEq___redArg___closed__12);
l_Lean_Meta_Grind_simpBoolEq___redArg___closed__13 = _init_l_Lean_Meta_Grind_simpBoolEq___redArg___closed__13();
lean_mark_persistent(l_Lean_Meta_Grind_simpBoolEq___redArg___closed__13);
l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpBoolEq_declare__14___closed__0____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_844_ = _init_l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpBoolEq_declare__14___closed__0____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_844_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpBoolEq_declare__14___closed__0____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_844_);
l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpBoolEq_declare__14___closed__1____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_844_ = _init_l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpBoolEq_declare__14___closed__1____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_844_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpBoolEq_declare__14___closed__1____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_844_);
l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpBoolEq_declare__14___closed__2____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_844_ = _init_l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpBoolEq_declare__14___closed__2____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_844_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpBoolEq_declare__14___closed__2____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_844_);
l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpBoolEq_declare__14___closed__3____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_844_ = _init_l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpBoolEq_declare__14___closed__3____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_844_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpBoolEq_declare__14___closed__3____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_844_);
l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpBoolEq_declare__14___closed__4____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_844_ = _init_l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpBoolEq_declare__14___closed__4____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_844_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpBoolEq_declare__14___closed__4____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_844_);
l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpBoolEq_declare__14___closed__5____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_844_ = _init_l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpBoolEq_declare__14___closed__5____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_844_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpBoolEq_declare__14___closed__5____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_844_);
l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpBoolEq_declare__14___closed__6____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_844_ = _init_l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpBoolEq_declare__14___closed__6____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_844_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpBoolEq_declare__14___closed__6____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_844_);
l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpBoolEq_declare__14___closed__7____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_844_ = _init_l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpBoolEq_declare__14___closed__7____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_844_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpBoolEq_declare__14___closed__7____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_844_);
l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpBoolEq_declare__14___closed__8____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_844_ = _init_l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpBoolEq_declare__14___closed__8____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_844_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpBoolEq_declare__14___closed__8____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_844_);
l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpBoolEq_declare__14___closed__9____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_844_ = _init_l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpBoolEq_declare__14___closed__9____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_844_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpBoolEq_declare__14___closed__9____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_844_);
if (builtin) {res = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpBoolEq_declare__14____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_844_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Meta_Grind_getSimprocs___redArg___closed__0 = _init_l_Lean_Meta_Grind_getSimprocs___redArg___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_getSimprocs___redArg___closed__0);
l_Lean_Meta_Grind_getSimprocs___redArg___closed__1 = _init_l_Lean_Meta_Grind_getSimprocs___redArg___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_getSimprocs___redArg___closed__1);
l_Lean_Meta_Grind_getSimprocs___redArg___closed__2 = _init_l_Lean_Meta_Grind_getSimprocs___redArg___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_getSimprocs___redArg___closed__2);
l_Lean_Meta_Grind_getSimprocs___redArg___closed__3 = _init_l_Lean_Meta_Grind_getSimprocs___redArg___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_getSimprocs___redArg___closed__3);
l_Lean_Meta_Grind_getSimpContext___redArg___closed__0 = _init_l_Lean_Meta_Grind_getSimpContext___redArg___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_getSimpContext___redArg___closed__0);
l_Lean_Meta_Grind_normalizeImp___closed__0 = _init_l_Lean_Meta_Grind_normalizeImp___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_normalizeImp___closed__0);
l_Lean_Meta_Grind_normalizeImp___closed__1 = _init_l_Lean_Meta_Grind_normalizeImp___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_normalizeImp___closed__1);
l_Lean_Meta_Grind_normalizeImp___closed__2 = _init_l_Lean_Meta_Grind_normalizeImp___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_normalizeImp___closed__2);
l_Lean_Meta_Grind_normalizeImp___closed__3 = _init_l_Lean_Meta_Grind_normalizeImp___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_normalizeImp___closed__3);
l_Lean_Meta_Grind_normalizeImp___closed__4 = _init_l_Lean_Meta_Grind_normalizeImp___closed__4();
lean_mark_persistent(l_Lean_Meta_Grind_normalizeImp___closed__4);
l_Lean_Meta_Grind_normalizeImp___closed__5 = _init_l_Lean_Meta_Grind_normalizeImp___closed__5();
lean_mark_persistent(l_Lean_Meta_Grind_normalizeImp___closed__5);
l_Lean_Meta_Grind_normalizeImp___closed__6 = _init_l_Lean_Meta_Grind_normalizeImp___closed__6();
lean_mark_persistent(l_Lean_Meta_Grind_normalizeImp___closed__6);
l_Lean_Meta_Grind_normalizeImp___closed__7 = _init_l_Lean_Meta_Grind_normalizeImp___closed__7();
lean_mark_persistent(l_Lean_Meta_Grind_normalizeImp___closed__7);
l_Lean_Meta_Grind_normalizeImp___closed__8 = _init_l_Lean_Meta_Grind_normalizeImp___closed__8();
lean_mark_persistent(l_Lean_Meta_Grind_normalizeImp___closed__8);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
