// Lean compiler output
// Module: Lean.Compiler.LCNF.PrettyPrinter
// Imports: Init Lean.PrettyPrinter Lean.Compiler.LCNF.CompilerM
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_pp_letVarTypes;
static lean_object* l_Lean_Compiler_LCNF_PP_ppExpr___closed__13;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
static lean_object* l_Lean_Compiler_LCNF_ppDecl___lambda__1___closed__1;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_PP_ppFunDecl___closed__2;
lean_object* l_Lean_LocalDecl_userName(lean_object*);
lean_object* l_Std_Format_indentD(lean_object*);
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_Compiler_LCNF_ppDecl___spec__1(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
static lean_object* l_Lean_Compiler_LCNF_PP_ppLetDecl___closed__5;
static lean_object* l_Lean_Compiler_LCNF_PP_ppExpr___closed__2;
static lean_object* l_Lean_Compiler_LCNF_PP_ppFunDecl___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_indentD(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_PP_ppLetDecl___closed__3;
lean_object* l_Lean_Meta_ppExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_PP_ppCode___closed__5;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_prefixJoin___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toSubarray___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_run(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_PP_ppExpr___closed__6;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppFVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_PP_ppArg___closed__3;
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_prefixJoin___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_PP_ppExpr___closed__12;
extern lean_object* l_Lean_levelZero;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_run___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppCode(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_PP_ppExpr___closed__19;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppAlt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppFunDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppLetDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
uint8_t l_Lean_Option_get___at_Lean_getSanitizeNames___spec__1(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_PP_ppExpr___closed__11;
static lean_object* l_Lean_Compiler_LCNF_PP_ppParam___closed__7;
static lean_object* l_Lean_Compiler_LCNF_PP_ppParams___closed__1;
lean_object* lean_nat_sub(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_PP_ppCode___closed__6;
static lean_object* l_Lean_Compiler_LCNF_PP_ppArg___closed__1;
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_PP_ppParam___closed__3;
static lean_object* l_Lean_Compiler_LCNF_PP_ppExpr___closed__10;
static lean_object* l_Lean_Compiler_LCNF_PP_ppArgs___closed__1;
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(lean_object*, lean_object*);
lean_object* l_Nat_repr(lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_PP_ppParam___closed__5;
extern lean_object* l_Lean_Expr_instHashableExpr;
lean_object* l_Std_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Meta_InfoCacheKey_instHashableInfoCacheKey___boxed(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_PP_ppExpr___closed__16;
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_Compiler_LCNF_ppDecl___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_PP_ppCode___closed__3;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppCode(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_prefixJoin___spec__1___rarg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_PP_ppArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppParams___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppParam(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_PP_ppExpr___closed__20;
size_t lean_usize_of_nat(lean_object*);
extern lean_object* l_Lean_pp_explicit;
static lean_object* l_Lean_Compiler_LCNF_PP_ppCode___closed__10;
lean_object* l_instBEqProd___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_PP_ppParam___closed__6;
extern lean_object* l_Lean_pp_funBinderTypes;
static lean_object* l_Lean_Compiler_LCNF_PP_ppCode___closed__7;
static lean_object* l_Lean_Compiler_LCNF_PP_ppAlt___closed__5;
static lean_object* l_Lean_Compiler_LCNF_PP_ppAlt___closed__3;
static lean_object* l_Lean_Compiler_LCNF_PP_ppAlt___closed__1;
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join___spec__1___rarg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_LCtx_toLocalContext(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_PP_ppAlt___closed__2;
static lean_object* l_Lean_Compiler_LCNF_PP_ppParam___closed__2;
static lean_object* l_Subarray_forInUnsafe_loop___at___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join___spec__1___rarg___closed__3;
static lean_object* l_Lean_Compiler_LCNF_PP_ppAlt___closed__4;
static lean_object* l_Lean_Compiler_LCNF_PP_ppCode___closed__11;
static lean_object* l_Lean_Compiler_LCNF_PP_ppLetDecl___closed__4;
static lean_object* l_Lean_Compiler_LCNF_PP_ppExpr___closed__15;
static lean_object* l_Lean_Compiler_LCNF_PP_ppExpr___closed__3;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppParam___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_PP_ppParam___closed__1;
static lean_object* l_Lean_Compiler_LCNF_PP_run___rarg___closed__1;
static lean_object* l_Lean_Compiler_LCNF_PP_ppCode___closed__9;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_prefixJoin(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_PP_ppParam___closed__8;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_prefixJoin___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instHashableProd___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ppDecl___lambda__1___closed__2;
static lean_object* l_Lean_Compiler_LCNF_PP_ppParam___closed__4;
extern lean_object* l_Lean_Expr_instBEqExpr;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppFVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_PP_ppParam___closed__9;
lean_object* lean_string_length(lean_object*);
static lean_object* l_Subarray_forInUnsafe_loop___at___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join___spec__1___rarg___closed__1;
static lean_object* l_Lean_Compiler_LCNF_PP_ppAlt___closed__6;
static lean_object* l_Lean_Compiler_LCNF_PP_ppExpr___closed__14;
static lean_object* l_Lean_Compiler_LCNF_PP_ppExpr___closed__5;
static lean_object* l_Lean_Compiler_LCNF_PP_ppExpr___closed__18;
lean_object* l_Lean_Expr_getAppFn(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_PP_ppExpr___closed__4;
static lean_object* l_Lean_Compiler_LCNF_PP_ppLetDecl___closed__1;
static lean_object* l_Lean_Compiler_LCNF_PP_ppCode___closed__2;
static lean_object* l_Lean_Compiler_LCNF_PP_ppExpr___closed__17;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_prefixJoin___spec__1(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_PP_ppExpr___closed__8;
static lean_object* l_Lean_Compiler_LCNF_PP_ppCode___closed__4;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppDecl___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_PP_ppLetDecl___closed__2;
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_PP_ppExpr___closed__1;
static lean_object* l_Subarray_forInUnsafe_loop___at___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join___spec__1___rarg___closed__2;
static lean_object* l_Lean_Compiler_LCNF_PP_ppCode___closed__8;
extern lean_object* l_Lean_pp_sanitizeNames;
static lean_object* l_Lean_Compiler_LCNF_PP_ppValue___closed__1;
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Lean_Option_set___at_Lean_Meta_withPPInaccessibleNamesImp___spec__2(lean_object*, lean_object*, uint8_t);
static lean_object* l_Subarray_forInUnsafe_loop___at___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join___spec__1___rarg___closed__4;
static lean_object* l_Lean_Compiler_LCNF_PP_ppExpr___closed__7;
static lean_object* l_Lean_Compiler_LCNF_PP_ppValue___closed__2;
static lean_object* l_Lean_Compiler_LCNF_PP_ppExpr___closed__9;
static lean_object* l_Lean_Compiler_LCNF_PP_ppCode___closed__1;
lean_object* l_Lean_Compiler_LCNF_getLocalDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_PP_ppApp___closed__1;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_indentD(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Format_indentD(x_1);
return x_2;
}
}
static lean_object* _init_l_Subarray_forInUnsafe_loop___at___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join___spec__1___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("", 0);
return x_1;
}
}
static lean_object* _init_l_Subarray_forInUnsafe_loop___at___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join___spec__1___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Subarray_forInUnsafe_loop___at___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join___spec__1___rarg___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Subarray_forInUnsafe_loop___at___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join___spec__1___rarg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(" ", 1);
return x_1;
}
}
static lean_object* _init_l_Subarray_forInUnsafe_loop___at___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join___spec__1___rarg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Subarray_forInUnsafe_loop___at___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join___spec__1___rarg___closed__3;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join___spec__1___rarg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_lt(x_4, x_3);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_5);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_2, 0);
x_14 = lean_array_uget(x_13, x_4);
lean_inc(x_1);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_15 = lean_apply_6(x_1, x_14, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; size_t x_24; size_t x_25; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Subarray_forInUnsafe_loop___at___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join___spec__1___rarg___closed__2;
x_19 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_5);
x_20 = l_Subarray_forInUnsafe_loop___at___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join___spec__1___rarg___closed__4;
x_21 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_16);
x_23 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_18);
x_24 = 1;
x_25 = lean_usize_add(x_4, x_24);
x_4 = x_25;
x_5 = x_23;
x_10 = x_17;
goto _start;
}
else
{
uint8_t x_27; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_27 = !lean_is_exclusive(x_15);
if (x_27 == 0)
{
return x_15;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_15, 0);
x_29 = lean_ctor_get(x_15, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_15);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Subarray_forInUnsafe_loop___at___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join___spec__1___rarg___boxed), 10, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_array_get_size(x_1);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_nat_dec_lt(x_9, x_8);
lean_dec(x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_7);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_array_fget(x_1, x_9);
lean_inc(x_2);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_14 = lean_apply_6(x_2, x_13, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; size_t x_21; lean_object* x_22; size_t x_23; lean_object* x_24; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_array_get_size(x_1);
x_18 = lean_unsigned_to_nat(1u);
x_19 = l_Array_toSubarray___rarg(x_1, x_18, x_17);
x_20 = lean_ctor_get(x_19, 2);
lean_inc(x_20);
x_21 = lean_usize_of_nat(x_20);
lean_dec(x_20);
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
x_23 = lean_usize_of_nat(x_22);
lean_dec(x_22);
x_24 = l_Subarray_forInUnsafe_loop___at___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join___spec__1___rarg(x_2, x_19, x_21, x_23, x_15, x_3, x_4, x_5, x_6, x_16);
lean_dec(x_19);
if (lean_obj_tag(x_24) == 0)
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
return x_24;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_24, 0);
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_24);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
else
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_24);
if (x_29 == 0)
{
return x_24;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_24, 0);
x_31 = lean_ctor_get(x_24, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_24);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
else
{
uint8_t x_33; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_14);
if (x_33 == 0)
{
return x_14;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_14, 0);
x_35 = lean_ctor_get(x_14, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_14);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join___rarg), 7, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = l_Subarray_forInUnsafe_loop___at___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join___spec__1___rarg(x_1, x_2, x_11, x_12, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_prefixJoin___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
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
lean_object* x_14; lean_object* x_15; 
x_14 = lean_array_uget(x_3, x_5);
lean_inc(x_2);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_15 = lean_apply_6(x_2, x_14, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; size_t x_25; size_t x_26; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Subarray_forInUnsafe_loop___at___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join___spec__1___rarg___closed__2;
x_19 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_6);
x_20 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
lean_inc(x_1);
x_21 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_1);
x_22 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_18);
x_23 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_16);
x_24 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_18);
x_25 = 1;
x_26 = lean_usize_add(x_5, x_25);
x_5 = x_26;
x_6 = x_24;
x_11 = x_17;
goto _start;
}
else
{
uint8_t x_28; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_28 = !lean_is_exclusive(x_15);
if (x_28 == 0)
{
return x_15;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_15, 0);
x_30 = lean_ctor_get(x_15, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_15);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_prefixJoin___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_forInUnsafe_loop___at___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_prefixJoin___spec__1___rarg___boxed), 11, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_prefixJoin___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_array_get_size(x_2);
x_10 = lean_usize_of_nat(x_9);
lean_dec(x_9);
x_11 = 0;
x_12 = lean_box(0);
x_13 = l_Array_forInUnsafe_loop___at___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_prefixJoin___spec__1___rarg(x_1, x_3, x_2, x_10, x_11, x_12, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
return x_13;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_13);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_13);
if (x_18 == 0)
{
return x_13;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_13, 0);
x_20 = lean_ctor_get(x_13, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_13);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_prefixJoin(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_prefixJoin___rarg___boxed), 8, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_prefixJoin___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_14 = l_Array_forInUnsafe_loop___at___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_prefixJoin___spec__1___rarg(x_1, x_2, x_3, x_12, x_13, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_3);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_prefixJoin___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_prefixJoin___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppFVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Compiler_LCNF_getLocalDecl(x_1, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = l_Lean_LocalDecl_userName(x_9);
lean_dec(x_9);
x_11 = 1;
x_12 = l_Lean_Name_toString(x_10, x_11);
x_13 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_7, 0, x_13);
return x_7;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_14 = lean_ctor_get(x_7, 0);
x_15 = lean_ctor_get(x_7, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_7);
x_16 = l_Lean_LocalDecl_userName(x_14);
lean_dec(x_14);
x_17 = 1;
x_18 = l_Lean_Name_toString(x_16, x_17);
x_19 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_15);
return x_20;
}
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_7);
if (x_21 == 0)
{
return x_7;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_7, 0);
x_23 = lean_ctor_get(x_7, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_7);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppFVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Compiler_LCNF_PP_ppFVar(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_PP_ppExpr___closed__1() {
_start:
{
uint8_t x_1; uint8_t x_2; uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_1 = 0;
x_2 = 1;
x_3 = 1;
x_4 = 0;
x_5 = lean_alloc_ctor(0, 0, 14);
lean_ctor_set_uint8(x_5, 0, x_1);
lean_ctor_set_uint8(x_5, 1, x_1);
lean_ctor_set_uint8(x_5, 2, x_1);
lean_ctor_set_uint8(x_5, 3, x_1);
lean_ctor_set_uint8(x_5, 4, x_1);
lean_ctor_set_uint8(x_5, 5, x_2);
lean_ctor_set_uint8(x_5, 6, x_3);
lean_ctor_set_uint8(x_5, 7, x_1);
lean_ctor_set_uint8(x_5, 8, x_3);
lean_ctor_set_uint8(x_5, 9, x_3);
lean_ctor_set_uint8(x_5, 10, x_1);
lean_ctor_set_uint8(x_5, 11, x_3);
lean_ctor_set_uint8(x_5, 12, x_3);
lean_ctor_set_uint8(x_5, 13, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_PP_ppExpr___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_PP_ppExpr___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = l_Std_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_PP_ppExpr___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_PP_ppExpr___closed__3;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_PP_ppExpr___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_PP_ppExpr___closed__4;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_PP_ppExpr___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_PP_ppExpr___closed__4;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_PP_ppExpr___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_PP_ppExpr___closed__4;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_PP_ppExpr___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Compiler_LCNF_PP_ppExpr___closed__5;
x_3 = l_Lean_Compiler_LCNF_PP_ppExpr___closed__6;
x_4 = l_Lean_Compiler_LCNF_PP_ppExpr___closed__7;
x_5 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_1);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_3);
lean_ctor_set(x_5, 4, x_4);
lean_ctor_set(x_5, 5, x_2);
lean_ctor_set(x_5, 6, x_3);
lean_ctor_set(x_5, 7, x_3);
return x_5;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_PP_ppExpr___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_PP_ppExpr___closed__4;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_PP_ppExpr___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_InfoCacheKey_instHashableInfoCacheKey___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_PP_ppExpr___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_PP_ppExpr___closed__4;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_PP_ppExpr___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_PP_ppExpr___closed__4;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_PP_ppExpr___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_instBEqExpr;
x_2 = lean_alloc_closure((void*)(l_instBEqProd___rarg), 4, 2);
lean_closure_set(x_2, 0, x_1);
lean_closure_set(x_2, 1, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_PP_ppExpr___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_instHashableExpr;
x_2 = lean_alloc_closure((void*)(l_instHashableProd___rarg___boxed), 3, 2);
lean_closure_set(x_2, 0, x_1);
lean_closure_set(x_2, 1, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_PP_ppExpr___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_PP_ppExpr___closed__4;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_PP_ppExpr___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Compiler_LCNF_PP_ppExpr___closed__9;
x_2 = l_Lean_Compiler_LCNF_PP_ppExpr___closed__11;
x_3 = l_Lean_Compiler_LCNF_PP_ppExpr___closed__12;
x_4 = l_Lean_Compiler_LCNF_PP_ppExpr___closed__15;
x_5 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_1);
lean_ctor_set(x_5, 4, x_1);
lean_ctor_set(x_5, 5, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_PP_ppExpr___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_PP_ppExpr___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_PP_ppExpr___closed__17;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_PP_ppExpr___closed__19() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = l_Lean_Compiler_LCNF_PP_ppExpr___closed__18;
x_3 = l_Lean_Compiler_LCNF_PP_ppExpr___closed__17;
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_4);
lean_ctor_set(x_5, 3, x_4);
lean_ctor_set_usize(x_5, 4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_PP_ppExpr___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_LCNF_PP_ppExpr___closed__8;
x_3 = l_Lean_Compiler_LCNF_PP_ppExpr___closed__16;
x_4 = l_Lean_Compiler_LCNF_PP_ppExpr___closed__19;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_1);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppExpr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_7 = lean_box(0);
x_8 = l_Lean_Compiler_LCNF_PP_ppExpr___closed__1;
x_9 = l_Lean_Compiler_LCNF_PP_ppExpr___closed__2;
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_11, 0, x_8);
lean_ctor_set(x_11, 1, x_2);
lean_ctor_set(x_11, 2, x_9);
lean_ctor_set(x_11, 3, x_7);
lean_ctor_set(x_11, 4, x_10);
lean_ctor_set(x_11, 5, x_7);
x_12 = lean_st_ref_get(x_5, x_6);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = l_Lean_Compiler_LCNF_PP_ppExpr___closed__20;
x_15 = lean_st_mk_ref(x_14, x_13);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Lean_Meta_ppExpr(x_1, x_11, x_16, x_4, x_5, x_17);
lean_dec(x_11);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_st_ref_get(x_5, x_20);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_st_ref_get(x_16, x_22);
lean_dec(x_16);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_23, 0);
lean_dec(x_25);
lean_ctor_set(x_23, 0, x_19);
return x_23;
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_dec(x_23);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_19);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
else
{
uint8_t x_28; 
lean_dec(x_16);
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
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppExpr___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Compiler_LCNF_PP_ppExpr(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_7;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_PP_ppArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_pp_explicit;
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_PP_ppArg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("_", 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_PP_ppArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_PP_ppArg___closed__2;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = l_Lean_Expr_isFVar(x_1);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_4, 2);
x_9 = l_Lean_Compiler_LCNF_PP_ppArg___closed__1;
x_10 = l_Lean_Option_get___at_Lean_getSanitizeNames___spec__1(x_8, x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_2);
lean_dec(x_1);
x_11 = l_Lean_Compiler_LCNF_PP_ppArg___closed__3;
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_6);
return x_12;
}
else
{
lean_object* x_13; 
x_13 = l_Lean_Compiler_LCNF_PP_ppExpr(x_1, x_2, x_3, x_4, x_5, x_6);
return x_13;
}
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = l_Lean_Expr_fvarId_x21(x_1);
x_15 = l_Lean_Compiler_LCNF_PP_ppFVar(x_14, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Compiler_LCNF_PP_ppArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_7;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_PP_ppArgs___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_PP_ppArg___boxed), 6, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppArgs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_Compiler_LCNF_PP_ppArgs___closed__1;
x_8 = l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join___rarg(x_1, x_7, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_PP_ppApp___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_levelZero;
x_2 = l_Lean_Expr_sort___override(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppApp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_Expr_getAppFn(x_1);
lean_inc(x_2);
x_8 = l_Lean_Compiler_LCNF_PP_ppExpr(x_7, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_unsigned_to_nat(0u);
x_12 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_1, x_11);
x_13 = l_Lean_Compiler_LCNF_PP_ppApp___closed__1;
lean_inc(x_12);
x_14 = lean_mk_array(x_12, x_13);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_sub(x_12, x_15);
lean_dec(x_12);
x_17 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_14, x_16);
x_18 = l_Lean_Compiler_LCNF_PP_ppArgs___closed__1;
x_19 = l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join___rarg(x_17, x_18, x_2, x_3, x_4, x_5, x_10);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = l_Subarray_forInUnsafe_loop___at___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join___spec__1___rarg___closed__2;
x_23 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_9);
x_24 = l_Subarray_forInUnsafe_loop___at___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join___spec__1___rarg___closed__4;
x_25 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_21);
x_27 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_22);
lean_ctor_set(x_19, 0, x_27);
return x_19;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_28 = lean_ctor_get(x_19, 0);
x_29 = lean_ctor_get(x_19, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_19);
x_30 = l_Subarray_forInUnsafe_loop___at___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join___spec__1___rarg___closed__2;
x_31 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_9);
x_32 = l_Subarray_forInUnsafe_loop___at___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join___spec__1___rarg___closed__4;
x_33 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
x_34 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_28);
x_35 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_30);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_29);
return x_36;
}
}
else
{
uint8_t x_37; 
lean_dec(x_9);
x_37 = !lean_is_exclusive(x_19);
if (x_37 == 0)
{
return x_19;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_19, 0);
x_39 = lean_ctor_get(x_19, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_19);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
else
{
uint8_t x_41; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_41 = !lean_is_exclusive(x_8);
if (x_41 == 0)
{
return x_8;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_8, 0);
x_43 = lean_ctor_get(x_8, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_8);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_PP_ppValue___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(" # ", 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_PP_ppValue___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_PP_ppValue___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppValue(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 1:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = l_Lean_Compiler_LCNF_PP_ppFVar(x_7, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
case 5:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_PP_ppApp(x_1, x_2, x_3, x_4, x_5, x_6);
return x_9;
}
case 11:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 2);
lean_inc(x_11);
lean_dec(x_1);
x_12 = l_Lean_Compiler_LCNF_PP_ppArg(x_11, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = l_Subarray_forInUnsafe_loop___at___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join___spec__1___rarg___closed__2;
x_16 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
x_17 = l_Lean_Compiler_LCNF_PP_ppValue___closed__2;
x_18 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = l_Nat_repr(x_10);
x_20 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_21, 0, x_18);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_15);
lean_ctor_set(x_12, 0, x_22);
return x_12;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_23 = lean_ctor_get(x_12, 0);
x_24 = lean_ctor_get(x_12, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_12);
x_25 = l_Subarray_forInUnsafe_loop___at___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join___spec__1___rarg___closed__2;
x_26 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_23);
x_27 = l_Lean_Compiler_LCNF_PP_ppValue___closed__2;
x_28 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = l_Nat_repr(x_10);
x_30 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_30, 0, x_29);
x_31 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_31, 0, x_28);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_25);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_24);
return x_33;
}
}
else
{
uint8_t x_34; 
lean_dec(x_10);
x_34 = !lean_is_exclusive(x_12);
if (x_34 == 0)
{
return x_12;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_12, 0);
x_36 = lean_ctor_get(x_12, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_12);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
default: 
{
lean_object* x_38; 
x_38 = l_Lean_Compiler_LCNF_PP_ppExpr(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_38;
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_PP_ppParam___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_pp_funBinderTypes;
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_PP_ppParam___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(" : ", 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_PP_ppParam___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_PP_ppParam___closed__2;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_PP_ppParam___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("(", 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_PP_ppParam___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_PP_ppParam___closed__4;
x_2 = lean_string_length(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_PP_ppParam___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_PP_ppParam___closed__5;
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_PP_ppParam___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_PP_ppParam___closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_PP_ppParam___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(")", 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_PP_ppParam___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_PP_ppParam___closed__8;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppParam(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_4, 2);
x_8 = l_Lean_Compiler_LCNF_PP_ppParam___closed__1;
x_9 = l_Lean_Option_get___at_Lean_getSanitizeNames___spec__1(x_7, x_8);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_2);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_dec(x_1);
x_11 = 1;
x_12 = l_Lean_Name_toString(x_10, x_11);
x_13 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_6);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_1, 2);
lean_inc(x_15);
x_16 = l_Lean_Compiler_LCNF_PP_ppExpr(x_15, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_ctor_get(x_1, 1);
lean_inc(x_19);
lean_dec(x_1);
x_20 = 1;
x_21 = l_Lean_Name_toString(x_19, x_20);
x_22 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_23 = l_Subarray_forInUnsafe_loop___at___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join___spec__1___rarg___closed__2;
x_24 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
x_25 = l_Lean_Compiler_LCNF_PP_ppParam___closed__3;
x_26 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_18);
x_28 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_23);
x_29 = l_Lean_Compiler_LCNF_PP_ppParam___closed__7;
x_30 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
x_31 = l_Lean_Compiler_LCNF_PP_ppParam___closed__9;
x_32 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
x_33 = l_Lean_Compiler_LCNF_PP_ppParam___closed__6;
x_34 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
x_35 = 0;
x_36 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set_uint8(x_36, sizeof(void*)*1, x_35);
lean_ctor_set(x_16, 0, x_36);
return x_16;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; lean_object* x_56; lean_object* x_57; 
x_37 = lean_ctor_get(x_16, 0);
x_38 = lean_ctor_get(x_16, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_16);
x_39 = lean_ctor_get(x_1, 1);
lean_inc(x_39);
lean_dec(x_1);
x_40 = 1;
x_41 = l_Lean_Name_toString(x_39, x_40);
x_42 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_42, 0, x_41);
x_43 = l_Subarray_forInUnsafe_loop___at___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join___spec__1___rarg___closed__2;
x_44 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_42);
x_45 = l_Lean_Compiler_LCNF_PP_ppParam___closed__3;
x_46 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
x_47 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_37);
x_48 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_43);
x_49 = l_Lean_Compiler_LCNF_PP_ppParam___closed__7;
x_50 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_48);
x_51 = l_Lean_Compiler_LCNF_PP_ppParam___closed__9;
x_52 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
x_53 = l_Lean_Compiler_LCNF_PP_ppParam___closed__6;
x_54 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_52);
x_55 = 0;
x_56 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set_uint8(x_56, sizeof(void*)*1, x_55);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_38);
return x_57;
}
}
else
{
uint8_t x_58; 
lean_dec(x_1);
x_58 = !lean_is_exclusive(x_16);
if (x_58 == 0)
{
return x_16;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_16, 0);
x_60 = lean_ctor_get(x_16, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_16);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppParam___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Compiler_LCNF_PP_ppParam(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_7;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_PP_ppParams___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_PP_ppParam___boxed), 6, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppParams(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = l_Subarray_forInUnsafe_loop___at___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join___spec__1___rarg___closed__4;
x_8 = l_Lean_Compiler_LCNF_PP_ppParams___closed__1;
x_9 = l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_prefixJoin___rarg(x_7, x_1, x_8, x_2, x_3, x_4, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppParams___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Compiler_LCNF_PP_ppParams(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_1);
return x_7;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_PP_ppLetDecl___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_pp_letVarTypes;
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_PP_ppLetDecl___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("let ", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_PP_ppLetDecl___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_PP_ppLetDecl___closed__2;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_PP_ppLetDecl___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(" := ", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_PP_ppLetDecl___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_PP_ppLetDecl___closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppLetDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_4, 2);
lean_inc(x_7);
x_8 = l_Lean_Compiler_LCNF_PP_ppLetDecl___closed__1;
x_9 = l_Lean_Option_get___at_Lean_getSanitizeNames___spec__1(x_7, x_8);
lean_dec(x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_1, 3);
lean_inc(x_10);
x_11 = l_Lean_Compiler_LCNF_PP_ppValue(x_10, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
lean_dec(x_1);
x_15 = 1;
x_16 = l_Lean_Name_toString(x_14, x_15);
x_17 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_18 = l_Lean_Compiler_LCNF_PP_ppLetDecl___closed__3;
x_19 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
x_20 = l_Lean_Compiler_LCNF_PP_ppLetDecl___closed__5;
x_21 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_13);
x_23 = l_Subarray_forInUnsafe_loop___at___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join___spec__1___rarg___closed__2;
x_24 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
lean_ctor_set(x_11, 0, x_24);
return x_11;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_25 = lean_ctor_get(x_11, 0);
x_26 = lean_ctor_get(x_11, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_11);
x_27 = lean_ctor_get(x_1, 1);
lean_inc(x_27);
lean_dec(x_1);
x_28 = 1;
x_29 = l_Lean_Name_toString(x_27, x_28);
x_30 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_30, 0, x_29);
x_31 = l_Lean_Compiler_LCNF_PP_ppLetDecl___closed__3;
x_32 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
x_33 = l_Lean_Compiler_LCNF_PP_ppLetDecl___closed__5;
x_34 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
x_35 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_25);
x_36 = l_Subarray_forInUnsafe_loop___at___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join___spec__1___rarg___closed__2;
x_37 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_26);
return x_38;
}
}
else
{
uint8_t x_39; 
lean_dec(x_1);
x_39 = !lean_is_exclusive(x_11);
if (x_39 == 0)
{
return x_11;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_11, 0);
x_41 = lean_ctor_get(x_11, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_11);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_1, 2);
lean_inc(x_43);
lean_inc(x_2);
x_44 = l_Lean_Compiler_LCNF_PP_ppExpr(x_43, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = lean_ctor_get(x_1, 3);
lean_inc(x_47);
x_48 = l_Lean_Compiler_LCNF_PP_ppValue(x_47, x_2, x_3, x_4, x_5, x_46);
if (lean_obj_tag(x_48) == 0)
{
uint8_t x_49; 
x_49 = !lean_is_exclusive(x_48);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; uint8_t x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_50 = lean_ctor_get(x_48, 0);
x_51 = lean_ctor_get(x_1, 1);
lean_inc(x_51);
lean_dec(x_1);
x_52 = 1;
x_53 = l_Lean_Name_toString(x_51, x_52);
x_54 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_54, 0, x_53);
x_55 = l_Lean_Compiler_LCNF_PP_ppLetDecl___closed__3;
x_56 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_54);
x_57 = l_Lean_Compiler_LCNF_PP_ppParam___closed__3;
x_58 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
x_59 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_45);
x_60 = l_Lean_Compiler_LCNF_PP_ppLetDecl___closed__5;
x_61 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
x_62 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_50);
x_63 = l_Subarray_forInUnsafe_loop___at___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join___spec__1___rarg___closed__2;
x_64 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
lean_ctor_set(x_48, 0, x_64);
return x_48;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_65 = lean_ctor_get(x_48, 0);
x_66 = lean_ctor_get(x_48, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_48);
x_67 = lean_ctor_get(x_1, 1);
lean_inc(x_67);
lean_dec(x_1);
x_68 = 1;
x_69 = l_Lean_Name_toString(x_67, x_68);
x_70 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_70, 0, x_69);
x_71 = l_Lean_Compiler_LCNF_PP_ppLetDecl___closed__3;
x_72 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_70);
x_73 = l_Lean_Compiler_LCNF_PP_ppParam___closed__3;
x_74 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
x_75 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_45);
x_76 = l_Lean_Compiler_LCNF_PP_ppLetDecl___closed__5;
x_77 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
x_78 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_65);
x_79 = l_Subarray_forInUnsafe_loop___at___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join___spec__1___rarg___closed__2;
x_80 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_66);
return x_81;
}
}
else
{
uint8_t x_82; 
lean_dec(x_45);
lean_dec(x_1);
x_82 = !lean_is_exclusive(x_48);
if (x_82 == 0)
{
return x_48;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_48, 0);
x_84 = lean_ctor_get(x_48, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_48);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
return x_85;
}
}
}
else
{
uint8_t x_86; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_86 = !lean_is_exclusive(x_44);
if (x_86 == 0)
{
return x_44;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_44, 0);
x_88 = lean_ctor_get(x_44, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_44);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
return x_89;
}
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_PP_ppFunDecl___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(" :=", 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_PP_ppFunDecl___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_PP_ppFunDecl___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppFunDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_1, 2);
lean_inc(x_7);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_8 = l_Lean_Compiler_LCNF_PP_ppParams(x_7, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_ctor_get(x_1, 4);
lean_inc(x_11);
x_12 = l_Lean_Compiler_LCNF_PP_ppCode(x_11, x_2, x_3, x_4, x_5, x_10);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_1, 1);
lean_inc(x_15);
lean_dec(x_1);
x_16 = 1;
x_17 = l_Lean_Name_toString(x_15, x_16);
x_18 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = l_Subarray_forInUnsafe_loop___at___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join___spec__1___rarg___closed__2;
x_20 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
x_21 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
x_22 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_9);
x_23 = l_Lean_Compiler_LCNF_PP_ppFunDecl___closed__2;
x_24 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = l_Std_Format_indentD(x_14);
x_26 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_19);
lean_ctor_set(x_12, 0, x_27);
return x_12;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_28 = lean_ctor_get(x_12, 0);
x_29 = lean_ctor_get(x_12, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_12);
x_30 = lean_ctor_get(x_1, 1);
lean_inc(x_30);
lean_dec(x_1);
x_31 = 1;
x_32 = l_Lean_Name_toString(x_30, x_31);
x_33 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_33, 0, x_32);
x_34 = l_Subarray_forInUnsafe_loop___at___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join___spec__1___rarg___closed__2;
x_35 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
x_36 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
x_37 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_9);
x_38 = l_Lean_Compiler_LCNF_PP_ppFunDecl___closed__2;
x_39 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
x_40 = l_Std_Format_indentD(x_28);
x_41 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
x_42 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_34);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_29);
return x_43;
}
}
else
{
uint8_t x_44; 
lean_dec(x_9);
lean_dec(x_1);
x_44 = !lean_is_exclusive(x_12);
if (x_44 == 0)
{
return x_12;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_12, 0);
x_46 = lean_ctor_get(x_12, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_12);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
else
{
uint8_t x_48; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_48 = !lean_is_exclusive(x_8);
if (x_48 == 0)
{
return x_8;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_8, 0);
x_50 = lean_ctor_get(x_8, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_8);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_PP_ppCode___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("fun ", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_PP_ppCode___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_PP_ppCode___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_PP_ppCode___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("jp ", 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_PP_ppCode___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_PP_ppCode___closed__3;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_PP_ppCode___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("goto ", 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_PP_ppCode___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_PP_ppCode___closed__5;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_PP_ppCode___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_PP_ppAlt), 6, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_PP_ppCode___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("cases ", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_PP_ppCode___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_PP_ppCode___closed__8;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_PP_ppCode___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("⊥", 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_PP_ppCode___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_PP_ppCode___closed__10;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppCode(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_dec(x_1);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_9 = l_Lean_Compiler_LCNF_PP_ppLetDecl(x_7, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_Compiler_LCNF_PP_ppCode(x_8, x_2, x_3, x_4, x_5, x_11);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_box(1);
x_16 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_16, 0, x_10);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_14);
lean_ctor_set(x_12, 0, x_17);
return x_12;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_18 = lean_ctor_get(x_12, 0);
x_19 = lean_ctor_get(x_12, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_12);
x_20 = lean_box(1);
x_21 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_21, 0, x_10);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_18);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_19);
return x_23;
}
}
else
{
uint8_t x_24; 
lean_dec(x_10);
x_24 = !lean_is_exclusive(x_12);
if (x_24 == 0)
{
return x_12;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_12, 0);
x_26 = lean_ctor_get(x_12, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_12);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
else
{
uint8_t x_28; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_28 = !lean_is_exclusive(x_9);
if (x_28 == 0)
{
return x_9;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_9, 0);
x_30 = lean_ctor_get(x_9, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_9);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
case 1:
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_1, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_1, 1);
lean_inc(x_33);
lean_dec(x_1);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_34 = l_Lean_Compiler_LCNF_PP_ppFunDecl(x_32, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = l_Lean_Compiler_LCNF_PP_ppCode(x_33, x_2, x_3, x_4, x_5, x_36);
if (lean_obj_tag(x_37) == 0)
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_39 = lean_ctor_get(x_37, 0);
x_40 = l_Lean_Compiler_LCNF_PP_ppCode___closed__2;
x_41 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_35);
x_42 = lean_box(1);
x_43 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
x_44 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_39);
lean_ctor_set(x_37, 0, x_44);
return x_37;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_45 = lean_ctor_get(x_37, 0);
x_46 = lean_ctor_get(x_37, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_37);
x_47 = l_Lean_Compiler_LCNF_PP_ppCode___closed__2;
x_48 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_35);
x_49 = lean_box(1);
x_50 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
x_51 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_45);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_46);
return x_52;
}
}
else
{
uint8_t x_53; 
lean_dec(x_35);
x_53 = !lean_is_exclusive(x_37);
if (x_53 == 0)
{
return x_37;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_37, 0);
x_55 = lean_ctor_get(x_37, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_37);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
else
{
uint8_t x_57; 
lean_dec(x_33);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_57 = !lean_is_exclusive(x_34);
if (x_57 == 0)
{
return x_34;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_34, 0);
x_59 = lean_ctor_get(x_34, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_34);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
case 2:
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_1, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_1, 1);
lean_inc(x_62);
lean_dec(x_1);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_63 = l_Lean_Compiler_LCNF_PP_ppFunDecl(x_61, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec(x_63);
x_66 = l_Lean_Compiler_LCNF_PP_ppCode(x_62, x_2, x_3, x_4, x_5, x_65);
if (lean_obj_tag(x_66) == 0)
{
uint8_t x_67; 
x_67 = !lean_is_exclusive(x_66);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_68 = lean_ctor_get(x_66, 0);
x_69 = l_Lean_Compiler_LCNF_PP_ppCode___closed__4;
x_70 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_64);
x_71 = lean_box(1);
x_72 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
x_73 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_68);
lean_ctor_set(x_66, 0, x_73);
return x_66;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_74 = lean_ctor_get(x_66, 0);
x_75 = lean_ctor_get(x_66, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_66);
x_76 = l_Lean_Compiler_LCNF_PP_ppCode___closed__4;
x_77 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_64);
x_78 = lean_box(1);
x_79 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
x_80 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_74);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_75);
return x_81;
}
}
else
{
uint8_t x_82; 
lean_dec(x_64);
x_82 = !lean_is_exclusive(x_66);
if (x_82 == 0)
{
return x_66;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_66, 0);
x_84 = lean_ctor_get(x_66, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_66);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
return x_85;
}
}
}
else
{
uint8_t x_86; 
lean_dec(x_62);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_86 = !lean_is_exclusive(x_63);
if (x_86 == 0)
{
return x_63;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_63, 0);
x_88 = lean_ctor_get(x_63, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_63);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
return x_89;
}
}
}
case 3:
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_1, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_1, 1);
lean_inc(x_91);
lean_dec(x_1);
x_92 = l_Lean_Compiler_LCNF_PP_ppFVar(x_90, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_92, 1);
lean_inc(x_94);
lean_dec(x_92);
x_95 = l_Lean_Compiler_LCNF_PP_ppArgs___closed__1;
x_96 = l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join___rarg(x_91, x_95, x_2, x_3, x_4, x_5, x_94);
if (lean_obj_tag(x_96) == 0)
{
uint8_t x_97; 
x_97 = !lean_is_exclusive(x_96);
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_98 = lean_ctor_get(x_96, 0);
x_99 = l_Lean_Compiler_LCNF_PP_ppCode___closed__6;
x_100 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_93);
x_101 = l_Subarray_forInUnsafe_loop___at___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join___spec__1___rarg___closed__4;
x_102 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set(x_102, 1, x_101);
x_103 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_98);
x_104 = l_Subarray_forInUnsafe_loop___at___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join___spec__1___rarg___closed__2;
x_105 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_105, 0, x_103);
lean_ctor_set(x_105, 1, x_104);
lean_ctor_set(x_96, 0, x_105);
return x_96;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_106 = lean_ctor_get(x_96, 0);
x_107 = lean_ctor_get(x_96, 1);
lean_inc(x_107);
lean_inc(x_106);
lean_dec(x_96);
x_108 = l_Lean_Compiler_LCNF_PP_ppCode___closed__6;
x_109 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_109, 0, x_108);
lean_ctor_set(x_109, 1, x_93);
x_110 = l_Subarray_forInUnsafe_loop___at___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join___spec__1___rarg___closed__4;
x_111 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_111, 0, x_109);
lean_ctor_set(x_111, 1, x_110);
x_112 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_106);
x_113 = l_Subarray_forInUnsafe_loop___at___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join___spec__1___rarg___closed__2;
x_114 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_114, 0, x_112);
lean_ctor_set(x_114, 1, x_113);
x_115 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_107);
return x_115;
}
}
else
{
uint8_t x_116; 
lean_dec(x_93);
x_116 = !lean_is_exclusive(x_96);
if (x_116 == 0)
{
return x_96;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_117 = lean_ctor_get(x_96, 0);
x_118 = lean_ctor_get(x_96, 1);
lean_inc(x_118);
lean_inc(x_117);
lean_dec(x_96);
x_119 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_119, 0, x_117);
lean_ctor_set(x_119, 1, x_118);
return x_119;
}
}
}
else
{
uint8_t x_120; 
lean_dec(x_91);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_120 = !lean_is_exclusive(x_92);
if (x_120 == 0)
{
return x_92;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_121 = lean_ctor_get(x_92, 0);
x_122 = lean_ctor_get(x_92, 1);
lean_inc(x_122);
lean_inc(x_121);
lean_dec(x_92);
x_123 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_123, 0, x_121);
lean_ctor_set(x_123, 1, x_122);
return x_123;
}
}
}
case 4:
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_124 = lean_ctor_get(x_1, 0);
lean_inc(x_124);
lean_dec(x_1);
x_125 = lean_ctor_get(x_124, 2);
lean_inc(x_125);
x_126 = l_Lean_Compiler_LCNF_PP_ppFVar(x_125, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_126) == 0)
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_127 = lean_ctor_get(x_126, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_126, 1);
lean_inc(x_128);
lean_dec(x_126);
x_129 = lean_ctor_get(x_124, 3);
lean_inc(x_129);
lean_dec(x_124);
x_130 = lean_box(1);
x_131 = l_Lean_Compiler_LCNF_PP_ppCode___closed__7;
x_132 = l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_prefixJoin___rarg(x_130, x_129, x_131, x_2, x_3, x_4, x_5, x_128);
lean_dec(x_129);
if (lean_obj_tag(x_132) == 0)
{
uint8_t x_133; 
x_133 = !lean_is_exclusive(x_132);
if (x_133 == 0)
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_134 = lean_ctor_get(x_132, 0);
x_135 = l_Lean_Compiler_LCNF_PP_ppCode___closed__9;
x_136 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_136, 0, x_135);
lean_ctor_set(x_136, 1, x_127);
x_137 = l_Subarray_forInUnsafe_loop___at___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join___spec__1___rarg___closed__2;
x_138 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_138, 0, x_136);
lean_ctor_set(x_138, 1, x_137);
x_139 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_139, 0, x_138);
lean_ctor_set(x_139, 1, x_134);
x_140 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_140, 0, x_139);
lean_ctor_set(x_140, 1, x_137);
lean_ctor_set(x_132, 0, x_140);
return x_132;
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_141 = lean_ctor_get(x_132, 0);
x_142 = lean_ctor_get(x_132, 1);
lean_inc(x_142);
lean_inc(x_141);
lean_dec(x_132);
x_143 = l_Lean_Compiler_LCNF_PP_ppCode___closed__9;
x_144 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_144, 0, x_143);
lean_ctor_set(x_144, 1, x_127);
x_145 = l_Subarray_forInUnsafe_loop___at___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join___spec__1___rarg___closed__2;
x_146 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_146, 0, x_144);
lean_ctor_set(x_146, 1, x_145);
x_147 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_147, 0, x_146);
lean_ctor_set(x_147, 1, x_141);
x_148 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_148, 0, x_147);
lean_ctor_set(x_148, 1, x_145);
x_149 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_149, 0, x_148);
lean_ctor_set(x_149, 1, x_142);
return x_149;
}
}
else
{
uint8_t x_150; 
lean_dec(x_127);
x_150 = !lean_is_exclusive(x_132);
if (x_150 == 0)
{
return x_132;
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_151 = lean_ctor_get(x_132, 0);
x_152 = lean_ctor_get(x_132, 1);
lean_inc(x_152);
lean_inc(x_151);
lean_dec(x_132);
x_153 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_153, 0, x_151);
lean_ctor_set(x_153, 1, x_152);
return x_153;
}
}
}
else
{
uint8_t x_154; 
lean_dec(x_124);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_154 = !lean_is_exclusive(x_126);
if (x_154 == 0)
{
return x_126;
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_155 = lean_ctor_get(x_126, 0);
x_156 = lean_ctor_get(x_126, 1);
lean_inc(x_156);
lean_inc(x_155);
lean_dec(x_126);
x_157 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_157, 0, x_155);
lean_ctor_set(x_157, 1, x_156);
return x_157;
}
}
}
case 5:
{
lean_object* x_158; lean_object* x_159; 
x_158 = lean_ctor_get(x_1, 0);
lean_inc(x_158);
lean_dec(x_1);
x_159 = l_Lean_Compiler_LCNF_PP_ppFVar(x_158, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_159;
}
default: 
{
lean_object* x_160; lean_object* x_161; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_160 = l_Lean_Compiler_LCNF_PP_ppCode___closed__11;
x_161 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_161, 0, x_160);
lean_ctor_set(x_161, 1, x_6);
return x_161;
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_PP_ppAlt___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("| ", 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_PP_ppAlt___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_PP_ppAlt___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_PP_ppAlt___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(" =>", 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_PP_ppAlt___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_PP_ppAlt___closed__3;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_PP_ppAlt___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("| _ =>", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_PP_ppAlt___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_PP_ppAlt___closed__5;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppAlt(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 2);
lean_inc(x_9);
lean_dec(x_1);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_10 = l_Lean_Compiler_LCNF_PP_ppParams(x_8, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_8);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Compiler_LCNF_PP_ppCode(x_9, x_2, x_3, x_4, x_5, x_12);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = 1;
x_17 = l_Lean_Name_toString(x_7, x_16);
x_18 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = l_Lean_Compiler_LCNF_PP_ppAlt___closed__2;
x_20 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
x_21 = l_Subarray_forInUnsafe_loop___at___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join___spec__1___rarg___closed__2;
x_22 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_11);
x_24 = l_Lean_Compiler_LCNF_PP_ppAlt___closed__4;
x_25 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = l_Std_Format_indentD(x_15);
x_27 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_21);
lean_ctor_set(x_13, 0, x_28);
return x_13;
}
else
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_29 = lean_ctor_get(x_13, 0);
x_30 = lean_ctor_get(x_13, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_13);
x_31 = 1;
x_32 = l_Lean_Name_toString(x_7, x_31);
x_33 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_33, 0, x_32);
x_34 = l_Lean_Compiler_LCNF_PP_ppAlt___closed__2;
x_35 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
x_36 = l_Subarray_forInUnsafe_loop___at___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join___spec__1___rarg___closed__2;
x_37 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
x_38 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_11);
x_39 = l_Lean_Compiler_LCNF_PP_ppAlt___closed__4;
x_40 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
x_41 = l_Std_Format_indentD(x_29);
x_42 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_36);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_30);
return x_44;
}
}
else
{
uint8_t x_45; 
lean_dec(x_11);
lean_dec(x_7);
x_45 = !lean_is_exclusive(x_13);
if (x_45 == 0)
{
return x_13;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_13, 0);
x_47 = lean_ctor_get(x_13, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_13);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
else
{
uint8_t x_49; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_49 = !lean_is_exclusive(x_10);
if (x_49 == 0)
{
return x_10;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_10, 0);
x_51 = lean_ctor_get(x_10, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_10);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
else
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_ctor_get(x_1, 0);
lean_inc(x_53);
lean_dec(x_1);
x_54 = l_Lean_Compiler_LCNF_PP_ppCode(x_53, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_54) == 0)
{
uint8_t x_55; 
x_55 = !lean_is_exclusive(x_54);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_56 = lean_ctor_get(x_54, 0);
x_57 = l_Std_Format_indentD(x_56);
x_58 = l_Lean_Compiler_LCNF_PP_ppAlt___closed__6;
x_59 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_57);
x_60 = l_Subarray_forInUnsafe_loop___at___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join___spec__1___rarg___closed__2;
x_61 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
lean_ctor_set(x_54, 0, x_61);
return x_54;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_62 = lean_ctor_get(x_54, 0);
x_63 = lean_ctor_get(x_54, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_54);
x_64 = l_Std_Format_indentD(x_62);
x_65 = l_Lean_Compiler_LCNF_PP_ppAlt___closed__6;
x_66 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_64);
x_67 = l_Subarray_forInUnsafe_loop___at___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join___spec__1___rarg___closed__2;
x_68 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_63);
return x_69;
}
}
else
{
uint8_t x_70; 
x_70 = !lean_is_exclusive(x_54);
if (x_70 == 0)
{
return x_54;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_54, 0);
x_72 = lean_ctor_get(x_54, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_54);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
return x_73;
}
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_PP_run___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_pp_sanitizeNames;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_run___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_7 = lean_ctor_get(x_3, 2);
x_8 = l_Lean_Compiler_LCNF_PP_run___rarg___closed__1;
x_9 = 0;
x_10 = l_Lean_Option_set___at_Lean_Meta_withPPInaccessibleNamesImp___spec__2(x_7, x_8, x_9);
lean_ctor_set(x_3, 2, x_10);
x_11 = lean_st_ref_get(x_4, x_5);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_st_ref_get(x_2, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_Compiler_LCNF_LCtx_toLocalContext(x_16);
x_18 = lean_apply_5(x_1, x_17, x_2, x_3, x_4, x_15);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_19 = lean_ctor_get(x_3, 0);
x_20 = lean_ctor_get(x_3, 1);
x_21 = lean_ctor_get(x_3, 2);
x_22 = lean_ctor_get(x_3, 3);
x_23 = lean_ctor_get(x_3, 4);
x_24 = lean_ctor_get(x_3, 5);
x_25 = lean_ctor_get(x_3, 6);
x_26 = lean_ctor_get(x_3, 7);
x_27 = lean_ctor_get(x_3, 8);
x_28 = lean_ctor_get(x_3, 9);
x_29 = lean_ctor_get(x_3, 10);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_3);
x_30 = l_Lean_Compiler_LCNF_PP_run___rarg___closed__1;
x_31 = 0;
x_32 = l_Lean_Option_set___at_Lean_Meta_withPPInaccessibleNamesImp___spec__2(x_21, x_30, x_31);
x_33 = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(x_33, 0, x_19);
lean_ctor_set(x_33, 1, x_20);
lean_ctor_set(x_33, 2, x_32);
lean_ctor_set(x_33, 3, x_22);
lean_ctor_set(x_33, 4, x_23);
lean_ctor_set(x_33, 5, x_24);
lean_ctor_set(x_33, 6, x_25);
lean_ctor_set(x_33, 7, x_26);
lean_ctor_set(x_33, 8, x_27);
lean_ctor_set(x_33, 9, x_28);
lean_ctor_set(x_33, 10, x_29);
x_34 = lean_st_ref_get(x_4, x_5);
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
lean_dec(x_34);
x_36 = lean_st_ref_get(x_2, x_35);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = lean_ctor_get(x_37, 0);
lean_inc(x_39);
lean_dec(x_37);
x_40 = l_Lean_Compiler_LCNF_LCtx_toLocalContext(x_39);
x_41 = lean_apply_5(x_1, x_40, x_2, x_33, x_4, x_38);
return x_41;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_run(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_PP_run___rarg), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppCode(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_PP_ppCode), 6, 1);
lean_closure_set(x_6, 0, x_1);
x_7 = l_Lean_Compiler_LCNF_PP_run___rarg(x_6, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_Compiler_LCNF_ppDecl___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_8 = lean_apply_5(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_apply_6(x_2, x_9, x_3, x_4, x_5, x_6, x_10);
return x_11;
}
else
{
uint8_t x_12; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_12 = !lean_is_exclusive(x_8);
if (x_12 == 0)
{
return x_8;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_8, 0);
x_14 = lean_ctor_get(x_8, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_8);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_Compiler_LCNF_ppDecl___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Compiler_LCNF_ppDecl___spec__1___rarg), 7, 0);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ppDecl___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("def ", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ppDecl___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_ppDecl___lambda__1___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppDecl___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_1, 4);
lean_inc(x_8);
x_9 = l_Lean_Compiler_LCNF_PP_ppCode(x_8, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
lean_dec(x_1);
x_13 = 1;
x_14 = l_Lean_Name_toString(x_12, x_13);
x_15 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = l_Lean_Compiler_LCNF_ppDecl___lambda__1___closed__2;
x_17 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
x_18 = l_Subarray_forInUnsafe_loop___at___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join___spec__1___rarg___closed__2;
x_19 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_2);
x_21 = l_Lean_Compiler_LCNF_PP_ppFunDecl___closed__2;
x_22 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = l_Std_Format_indentD(x_11);
x_24 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_18);
lean_ctor_set(x_9, 0, x_25);
return x_9;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_26 = lean_ctor_get(x_9, 0);
x_27 = lean_ctor_get(x_9, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_9);
x_28 = lean_ctor_get(x_1, 0);
lean_inc(x_28);
lean_dec(x_1);
x_29 = 1;
x_30 = l_Lean_Name_toString(x_28, x_29);
x_31 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_31, 0, x_30);
x_32 = l_Lean_Compiler_LCNF_ppDecl___lambda__1___closed__2;
x_33 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
x_34 = l_Subarray_forInUnsafe_loop___at___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join___spec__1___rarg___closed__2;
x_35 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
x_36 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_2);
x_37 = l_Lean_Compiler_LCNF_PP_ppFunDecl___closed__2;
x_38 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
x_39 = l_Std_Format_indentD(x_26);
x_40 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
x_41 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_34);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_27);
return x_42;
}
}
else
{
uint8_t x_43; 
lean_dec(x_2);
lean_dec(x_1);
x_43 = !lean_is_exclusive(x_9);
if (x_43 == 0)
{
return x_9;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_9, 0);
x_45 = lean_ctor_get(x_9, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_9);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_1, 3);
lean_inc(x_6);
x_7 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_PP_ppParams___boxed), 6, 1);
lean_closure_set(x_7, 0, x_6);
x_8 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ppDecl___lambda__1), 7, 1);
lean_closure_set(x_8, 0, x_1);
x_9 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Compiler_LCNF_ppDecl___spec__1___rarg), 7, 2);
lean_closure_set(x_9, 0, x_7);
lean_closure_set(x_9, 1, x_8);
x_10 = l_Lean_Compiler_LCNF_PP_run___rarg(x_9, x_2, x_3, x_4, x_5);
return x_10;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_PrettyPrinter(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_CompilerM(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_LCNF_PrettyPrinter(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_PrettyPrinter(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_CompilerM(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Subarray_forInUnsafe_loop___at___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join___spec__1___rarg___closed__1 = _init_l_Subarray_forInUnsafe_loop___at___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join___spec__1___rarg___closed__1();
lean_mark_persistent(l_Subarray_forInUnsafe_loop___at___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join___spec__1___rarg___closed__1);
l_Subarray_forInUnsafe_loop___at___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join___spec__1___rarg___closed__2 = _init_l_Subarray_forInUnsafe_loop___at___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join___spec__1___rarg___closed__2();
lean_mark_persistent(l_Subarray_forInUnsafe_loop___at___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join___spec__1___rarg___closed__2);
l_Subarray_forInUnsafe_loop___at___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join___spec__1___rarg___closed__3 = _init_l_Subarray_forInUnsafe_loop___at___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join___spec__1___rarg___closed__3();
lean_mark_persistent(l_Subarray_forInUnsafe_loop___at___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join___spec__1___rarg___closed__3);
l_Subarray_forInUnsafe_loop___at___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join___spec__1___rarg___closed__4 = _init_l_Subarray_forInUnsafe_loop___at___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join___spec__1___rarg___closed__4();
lean_mark_persistent(l_Subarray_forInUnsafe_loop___at___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join___spec__1___rarg___closed__4);
l_Lean_Compiler_LCNF_PP_ppExpr___closed__1 = _init_l_Lean_Compiler_LCNF_PP_ppExpr___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_PP_ppExpr___closed__1);
l_Lean_Compiler_LCNF_PP_ppExpr___closed__2 = _init_l_Lean_Compiler_LCNF_PP_ppExpr___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_PP_ppExpr___closed__2);
l_Lean_Compiler_LCNF_PP_ppExpr___closed__3 = _init_l_Lean_Compiler_LCNF_PP_ppExpr___closed__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_PP_ppExpr___closed__3);
l_Lean_Compiler_LCNF_PP_ppExpr___closed__4 = _init_l_Lean_Compiler_LCNF_PP_ppExpr___closed__4();
lean_mark_persistent(l_Lean_Compiler_LCNF_PP_ppExpr___closed__4);
l_Lean_Compiler_LCNF_PP_ppExpr___closed__5 = _init_l_Lean_Compiler_LCNF_PP_ppExpr___closed__5();
lean_mark_persistent(l_Lean_Compiler_LCNF_PP_ppExpr___closed__5);
l_Lean_Compiler_LCNF_PP_ppExpr___closed__6 = _init_l_Lean_Compiler_LCNF_PP_ppExpr___closed__6();
lean_mark_persistent(l_Lean_Compiler_LCNF_PP_ppExpr___closed__6);
l_Lean_Compiler_LCNF_PP_ppExpr___closed__7 = _init_l_Lean_Compiler_LCNF_PP_ppExpr___closed__7();
lean_mark_persistent(l_Lean_Compiler_LCNF_PP_ppExpr___closed__7);
l_Lean_Compiler_LCNF_PP_ppExpr___closed__8 = _init_l_Lean_Compiler_LCNF_PP_ppExpr___closed__8();
lean_mark_persistent(l_Lean_Compiler_LCNF_PP_ppExpr___closed__8);
l_Lean_Compiler_LCNF_PP_ppExpr___closed__9 = _init_l_Lean_Compiler_LCNF_PP_ppExpr___closed__9();
lean_mark_persistent(l_Lean_Compiler_LCNF_PP_ppExpr___closed__9);
l_Lean_Compiler_LCNF_PP_ppExpr___closed__10 = _init_l_Lean_Compiler_LCNF_PP_ppExpr___closed__10();
lean_mark_persistent(l_Lean_Compiler_LCNF_PP_ppExpr___closed__10);
l_Lean_Compiler_LCNF_PP_ppExpr___closed__11 = _init_l_Lean_Compiler_LCNF_PP_ppExpr___closed__11();
lean_mark_persistent(l_Lean_Compiler_LCNF_PP_ppExpr___closed__11);
l_Lean_Compiler_LCNF_PP_ppExpr___closed__12 = _init_l_Lean_Compiler_LCNF_PP_ppExpr___closed__12();
lean_mark_persistent(l_Lean_Compiler_LCNF_PP_ppExpr___closed__12);
l_Lean_Compiler_LCNF_PP_ppExpr___closed__13 = _init_l_Lean_Compiler_LCNF_PP_ppExpr___closed__13();
lean_mark_persistent(l_Lean_Compiler_LCNF_PP_ppExpr___closed__13);
l_Lean_Compiler_LCNF_PP_ppExpr___closed__14 = _init_l_Lean_Compiler_LCNF_PP_ppExpr___closed__14();
lean_mark_persistent(l_Lean_Compiler_LCNF_PP_ppExpr___closed__14);
l_Lean_Compiler_LCNF_PP_ppExpr___closed__15 = _init_l_Lean_Compiler_LCNF_PP_ppExpr___closed__15();
lean_mark_persistent(l_Lean_Compiler_LCNF_PP_ppExpr___closed__15);
l_Lean_Compiler_LCNF_PP_ppExpr___closed__16 = _init_l_Lean_Compiler_LCNF_PP_ppExpr___closed__16();
lean_mark_persistent(l_Lean_Compiler_LCNF_PP_ppExpr___closed__16);
l_Lean_Compiler_LCNF_PP_ppExpr___closed__17 = _init_l_Lean_Compiler_LCNF_PP_ppExpr___closed__17();
lean_mark_persistent(l_Lean_Compiler_LCNF_PP_ppExpr___closed__17);
l_Lean_Compiler_LCNF_PP_ppExpr___closed__18 = _init_l_Lean_Compiler_LCNF_PP_ppExpr___closed__18();
lean_mark_persistent(l_Lean_Compiler_LCNF_PP_ppExpr___closed__18);
l_Lean_Compiler_LCNF_PP_ppExpr___closed__19 = _init_l_Lean_Compiler_LCNF_PP_ppExpr___closed__19();
lean_mark_persistent(l_Lean_Compiler_LCNF_PP_ppExpr___closed__19);
l_Lean_Compiler_LCNF_PP_ppExpr___closed__20 = _init_l_Lean_Compiler_LCNF_PP_ppExpr___closed__20();
lean_mark_persistent(l_Lean_Compiler_LCNF_PP_ppExpr___closed__20);
l_Lean_Compiler_LCNF_PP_ppArg___closed__1 = _init_l_Lean_Compiler_LCNF_PP_ppArg___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_PP_ppArg___closed__1);
l_Lean_Compiler_LCNF_PP_ppArg___closed__2 = _init_l_Lean_Compiler_LCNF_PP_ppArg___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_PP_ppArg___closed__2);
l_Lean_Compiler_LCNF_PP_ppArg___closed__3 = _init_l_Lean_Compiler_LCNF_PP_ppArg___closed__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_PP_ppArg___closed__3);
l_Lean_Compiler_LCNF_PP_ppArgs___closed__1 = _init_l_Lean_Compiler_LCNF_PP_ppArgs___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_PP_ppArgs___closed__1);
l_Lean_Compiler_LCNF_PP_ppApp___closed__1 = _init_l_Lean_Compiler_LCNF_PP_ppApp___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_PP_ppApp___closed__1);
l_Lean_Compiler_LCNF_PP_ppValue___closed__1 = _init_l_Lean_Compiler_LCNF_PP_ppValue___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_PP_ppValue___closed__1);
l_Lean_Compiler_LCNF_PP_ppValue___closed__2 = _init_l_Lean_Compiler_LCNF_PP_ppValue___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_PP_ppValue___closed__2);
l_Lean_Compiler_LCNF_PP_ppParam___closed__1 = _init_l_Lean_Compiler_LCNF_PP_ppParam___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_PP_ppParam___closed__1);
l_Lean_Compiler_LCNF_PP_ppParam___closed__2 = _init_l_Lean_Compiler_LCNF_PP_ppParam___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_PP_ppParam___closed__2);
l_Lean_Compiler_LCNF_PP_ppParam___closed__3 = _init_l_Lean_Compiler_LCNF_PP_ppParam___closed__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_PP_ppParam___closed__3);
l_Lean_Compiler_LCNF_PP_ppParam___closed__4 = _init_l_Lean_Compiler_LCNF_PP_ppParam___closed__4();
lean_mark_persistent(l_Lean_Compiler_LCNF_PP_ppParam___closed__4);
l_Lean_Compiler_LCNF_PP_ppParam___closed__5 = _init_l_Lean_Compiler_LCNF_PP_ppParam___closed__5();
lean_mark_persistent(l_Lean_Compiler_LCNF_PP_ppParam___closed__5);
l_Lean_Compiler_LCNF_PP_ppParam___closed__6 = _init_l_Lean_Compiler_LCNF_PP_ppParam___closed__6();
lean_mark_persistent(l_Lean_Compiler_LCNF_PP_ppParam___closed__6);
l_Lean_Compiler_LCNF_PP_ppParam___closed__7 = _init_l_Lean_Compiler_LCNF_PP_ppParam___closed__7();
lean_mark_persistent(l_Lean_Compiler_LCNF_PP_ppParam___closed__7);
l_Lean_Compiler_LCNF_PP_ppParam___closed__8 = _init_l_Lean_Compiler_LCNF_PP_ppParam___closed__8();
lean_mark_persistent(l_Lean_Compiler_LCNF_PP_ppParam___closed__8);
l_Lean_Compiler_LCNF_PP_ppParam___closed__9 = _init_l_Lean_Compiler_LCNF_PP_ppParam___closed__9();
lean_mark_persistent(l_Lean_Compiler_LCNF_PP_ppParam___closed__9);
l_Lean_Compiler_LCNF_PP_ppParams___closed__1 = _init_l_Lean_Compiler_LCNF_PP_ppParams___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_PP_ppParams___closed__1);
l_Lean_Compiler_LCNF_PP_ppLetDecl___closed__1 = _init_l_Lean_Compiler_LCNF_PP_ppLetDecl___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_PP_ppLetDecl___closed__1);
l_Lean_Compiler_LCNF_PP_ppLetDecl___closed__2 = _init_l_Lean_Compiler_LCNF_PP_ppLetDecl___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_PP_ppLetDecl___closed__2);
l_Lean_Compiler_LCNF_PP_ppLetDecl___closed__3 = _init_l_Lean_Compiler_LCNF_PP_ppLetDecl___closed__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_PP_ppLetDecl___closed__3);
l_Lean_Compiler_LCNF_PP_ppLetDecl___closed__4 = _init_l_Lean_Compiler_LCNF_PP_ppLetDecl___closed__4();
lean_mark_persistent(l_Lean_Compiler_LCNF_PP_ppLetDecl___closed__4);
l_Lean_Compiler_LCNF_PP_ppLetDecl___closed__5 = _init_l_Lean_Compiler_LCNF_PP_ppLetDecl___closed__5();
lean_mark_persistent(l_Lean_Compiler_LCNF_PP_ppLetDecl___closed__5);
l_Lean_Compiler_LCNF_PP_ppFunDecl___closed__1 = _init_l_Lean_Compiler_LCNF_PP_ppFunDecl___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_PP_ppFunDecl___closed__1);
l_Lean_Compiler_LCNF_PP_ppFunDecl___closed__2 = _init_l_Lean_Compiler_LCNF_PP_ppFunDecl___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_PP_ppFunDecl___closed__2);
l_Lean_Compiler_LCNF_PP_ppCode___closed__1 = _init_l_Lean_Compiler_LCNF_PP_ppCode___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_PP_ppCode___closed__1);
l_Lean_Compiler_LCNF_PP_ppCode___closed__2 = _init_l_Lean_Compiler_LCNF_PP_ppCode___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_PP_ppCode___closed__2);
l_Lean_Compiler_LCNF_PP_ppCode___closed__3 = _init_l_Lean_Compiler_LCNF_PP_ppCode___closed__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_PP_ppCode___closed__3);
l_Lean_Compiler_LCNF_PP_ppCode___closed__4 = _init_l_Lean_Compiler_LCNF_PP_ppCode___closed__4();
lean_mark_persistent(l_Lean_Compiler_LCNF_PP_ppCode___closed__4);
l_Lean_Compiler_LCNF_PP_ppCode___closed__5 = _init_l_Lean_Compiler_LCNF_PP_ppCode___closed__5();
lean_mark_persistent(l_Lean_Compiler_LCNF_PP_ppCode___closed__5);
l_Lean_Compiler_LCNF_PP_ppCode___closed__6 = _init_l_Lean_Compiler_LCNF_PP_ppCode___closed__6();
lean_mark_persistent(l_Lean_Compiler_LCNF_PP_ppCode___closed__6);
l_Lean_Compiler_LCNF_PP_ppCode___closed__7 = _init_l_Lean_Compiler_LCNF_PP_ppCode___closed__7();
lean_mark_persistent(l_Lean_Compiler_LCNF_PP_ppCode___closed__7);
l_Lean_Compiler_LCNF_PP_ppCode___closed__8 = _init_l_Lean_Compiler_LCNF_PP_ppCode___closed__8();
lean_mark_persistent(l_Lean_Compiler_LCNF_PP_ppCode___closed__8);
l_Lean_Compiler_LCNF_PP_ppCode___closed__9 = _init_l_Lean_Compiler_LCNF_PP_ppCode___closed__9();
lean_mark_persistent(l_Lean_Compiler_LCNF_PP_ppCode___closed__9);
l_Lean_Compiler_LCNF_PP_ppCode___closed__10 = _init_l_Lean_Compiler_LCNF_PP_ppCode___closed__10();
lean_mark_persistent(l_Lean_Compiler_LCNF_PP_ppCode___closed__10);
l_Lean_Compiler_LCNF_PP_ppCode___closed__11 = _init_l_Lean_Compiler_LCNF_PP_ppCode___closed__11();
lean_mark_persistent(l_Lean_Compiler_LCNF_PP_ppCode___closed__11);
l_Lean_Compiler_LCNF_PP_ppAlt___closed__1 = _init_l_Lean_Compiler_LCNF_PP_ppAlt___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_PP_ppAlt___closed__1);
l_Lean_Compiler_LCNF_PP_ppAlt___closed__2 = _init_l_Lean_Compiler_LCNF_PP_ppAlt___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_PP_ppAlt___closed__2);
l_Lean_Compiler_LCNF_PP_ppAlt___closed__3 = _init_l_Lean_Compiler_LCNF_PP_ppAlt___closed__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_PP_ppAlt___closed__3);
l_Lean_Compiler_LCNF_PP_ppAlt___closed__4 = _init_l_Lean_Compiler_LCNF_PP_ppAlt___closed__4();
lean_mark_persistent(l_Lean_Compiler_LCNF_PP_ppAlt___closed__4);
l_Lean_Compiler_LCNF_PP_ppAlt___closed__5 = _init_l_Lean_Compiler_LCNF_PP_ppAlt___closed__5();
lean_mark_persistent(l_Lean_Compiler_LCNF_PP_ppAlt___closed__5);
l_Lean_Compiler_LCNF_PP_ppAlt___closed__6 = _init_l_Lean_Compiler_LCNF_PP_ppAlt___closed__6();
lean_mark_persistent(l_Lean_Compiler_LCNF_PP_ppAlt___closed__6);
l_Lean_Compiler_LCNF_PP_run___rarg___closed__1 = _init_l_Lean_Compiler_LCNF_PP_run___rarg___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_PP_run___rarg___closed__1);
l_Lean_Compiler_LCNF_ppDecl___lambda__1___closed__1 = _init_l_Lean_Compiler_LCNF_ppDecl___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_ppDecl___lambda__1___closed__1);
l_Lean_Compiler_LCNF_ppDecl___lambda__1___closed__2 = _init_l_Lean_Compiler_LCNF_ppDecl___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_ppDecl___lambda__1___closed__2);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
