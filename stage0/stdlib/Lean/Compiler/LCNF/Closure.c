// Lean compiler output
// Module: Lean.Compiler.LCNF.Closure
// Imports: Lean.Util.ForEachExprWhere Lean.Compiler.LCNF.CompilerM
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Closure_collectParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Closure_collectParams___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Closure_markVisited___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
lean_object* l_Lean_Compiler_LCNF_findFunDecl_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Closure_collectType___closed__1;
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_instInhabitedReaderT___rarg___boxed(lean_object*, lean_object*);
extern lean_object* l_Lean_ForEachExprWhere_initCache;
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_checked___at_Lean_Compiler_LCNF_Closure_collectType___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Closure_collectFVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Closure_collectLetValue___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Closure_collectType___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visit___at_Lean_Compiler_LCNF_Closure_collectType___spec__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at_Lean_Compiler_LCNF_Closure_collectFVar___spec__1___closed__1;
extern lean_object* l_instInhabitedPUnit;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Closure_collectCode___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visited___at_Lean_Compiler_LCNF_Closure_collectType___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_panic___at_Lean_Compiler_LCNF_Closure_collectFVar___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Closure_collectParams___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visit_go___at_Lean_Compiler_LCNF_Closure_collectType___spec__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Closure_collectLetValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Closure_collectCode___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at_Lean_CollectMVars_visit___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_RBNode_findCore___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__2(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Closure_collectFVar___closed__4;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Closure_collectArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Closure_collectFVar___closed__1;
uint64_t l_Lean_Expr_hash(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visit_go___at_Lean_Compiler_LCNF_Closure_collectType___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Closure_run___rarg___closed__1;
static lean_object* l_Lean_Compiler_LCNF_Closure_collectType___closed__2;
size_t lean_usize_mod(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Closure_run(lean_object*);
extern lean_object* l_Lean_Compiler_LCNF_instMonadCompilerM;
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visit_go___at_Lean_Compiler_LCNF_Closure_collectType___spec__2___lambda__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Closure_collectParams___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Closure_markVisited(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Closure_collectFVar___closed__2;
lean_object* l_Lean_Expr_isFVar___boxed(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Closure_collectFVar___closed__3;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_findLetDecl_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Closure_run___rarg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Closure_collectType___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Closure_run___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_RBNode_insert___at_Lean_FVarIdSet_insert___spec__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at_Lean_Compiler_LCNF_Closure_collectFVar___spec__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visit___at_Lean_Compiler_LCNF_Closure_collectType___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
lean_object* lean_array_mk(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Closure_collectLetValue___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_CollectMVars_visit___spec__2(lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visit_go___at_Lean_Compiler_LCNF_Closure_collectType___spec__2___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_checked___at_Lean_Compiler_LCNF_Closure_collectType___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_instInhabitedOfMonad___rarg(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Closure_collectCode(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visited___at_Lean_Compiler_LCNF_Closure_collectType___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
static lean_object* l_panic___at_Lean_Compiler_LCNF_Closure_collectFVar___spec__1___closed__3;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_findParam_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isForall(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_ReaderT_instMonad___rarg(lean_object*);
size_t lean_usize_land(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Closure_collectFunDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Closure_collectType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Closure_markVisited(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_st_ref_take(x_3, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_13 = lean_ctor_get(x_10, 0);
x_14 = lean_box(0);
x_15 = l_Lean_RBNode_insert___at_Lean_FVarIdSet_insert___spec__1(x_13, x_1, x_14);
lean_ctor_set(x_10, 0, x_15);
x_16 = lean_st_ref_set(x_3, x_10, x_11);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_16, 0);
lean_dec(x_18);
lean_ctor_set(x_16, 0, x_14);
return x_16;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_14);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_21 = lean_ctor_get(x_10, 0);
x_22 = lean_ctor_get(x_10, 1);
x_23 = lean_ctor_get(x_10, 2);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_10);
x_24 = lean_box(0);
x_25 = l_Lean_RBNode_insert___at_Lean_FVarIdSet_insert___spec__1(x_21, x_1, x_24);
x_26 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_22);
lean_ctor_set(x_26, 2, x_23);
x_27 = lean_st_ref_set(x_3, x_26, x_11);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 lean_ctor_release(x_27, 1);
 x_29 = x_27;
} else {
 lean_dec_ref(x_27);
 x_29 = lean_box(0);
}
if (lean_is_scalar(x_29)) {
 x_30 = lean_alloc_ctor(0, 2, 0);
} else {
 x_30 = x_29;
}
lean_ctor_set(x_30, 0, x_24);
lean_ctor_set(x_30, 1, x_28);
return x_30;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Closure_markVisited___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_Closure_markVisited(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Closure_collectParams___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_eq(x_2, x_3);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; 
lean_dec(x_4);
x_13 = lean_array_uget(x_1, x_2);
x_14 = lean_ctor_get(x_13, 2);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_alloc_closure((void*)(l_Lean_Expr_isFVar___boxed), 1, 0);
x_16 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Closure_collectType___lambda__1___boxed), 8, 0);
x_17 = 0;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_18 = l_Lean_ForEachExprWhere_visit___at_Lean_Compiler_LCNF_Closure_collectType___spec__1(x_15, x_16, x_14, x_17, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; size_t x_21; size_t x_22; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = 1;
x_22 = lean_usize_add(x_2, x_21);
x_2 = x_22;
x_4 = x_19;
x_11 = x_20;
goto _start;
}
else
{
uint8_t x_24; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_24 = !lean_is_exclusive(x_18);
if (x_24 == 0)
{
return x_18;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_18, 0);
x_26 = lean_ctor_get(x_18, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_18);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
else
{
lean_object* x_28; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_4);
lean_ctor_set(x_28, 1, x_11);
return x_28;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Closure_collectParams(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_array_get_size(x_1);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_nat_dec_lt(x_10, x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_8);
return x_13;
}
else
{
uint8_t x_14; 
x_14 = lean_nat_dec_le(x_9, x_9);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_8);
return x_16;
}
else
{
size_t x_17; size_t x_18; lean_object* x_19; lean_object* x_20; 
x_17 = 0;
x_18 = lean_usize_of_nat(x_9);
lean_dec(x_9);
x_19 = lean_box(0);
x_20 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Closure_collectParams___spec__1(x_1, x_17, x_18, x_19, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visited___at_Lean_Compiler_LCNF_Closure_collectType___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_st_ref_get(x_2, x_9);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; size_t x_14; size_t x_15; size_t x_16; lean_object* x_17; lean_object* x_18; size_t x_19; uint8_t x_20; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_10, 1);
x_14 = lean_ptr_addr(x_1);
x_15 = 8191;
x_16 = lean_usize_mod(x_14, x_15);
x_17 = lean_ctor_get(x_12, 0);
lean_inc(x_17);
lean_dec(x_12);
x_18 = lean_array_uget(x_17, x_16);
lean_dec(x_17);
x_19 = lean_ptr_addr(x_18);
lean_dec(x_18);
x_20 = lean_usize_dec_eq(x_19, x_14);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
lean_free_object(x_10);
x_21 = lean_st_ref_take(x_2, x_13);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = !lean_is_exclusive(x_22);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_25 = lean_ctor_get(x_22, 0);
x_26 = lean_array_uset(x_25, x_16, x_1);
lean_ctor_set(x_22, 0, x_26);
x_27 = lean_st_ref_set(x_2, x_22, x_23);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; uint8_t x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_27, 0);
lean_dec(x_29);
x_30 = 0;
x_31 = lean_box(x_30);
lean_ctor_set(x_27, 0, x_31);
return x_27;
}
else
{
lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_27, 1);
lean_inc(x_32);
lean_dec(x_27);
x_33 = 0;
x_34 = lean_box(x_33);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_32);
return x_35;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; lean_object* x_44; lean_object* x_45; 
x_36 = lean_ctor_get(x_22, 0);
x_37 = lean_ctor_get(x_22, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_22);
x_38 = lean_array_uset(x_36, x_16, x_1);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
x_40 = lean_st_ref_set(x_2, x_39, x_23);
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 x_42 = x_40;
} else {
 lean_dec_ref(x_40);
 x_42 = lean_box(0);
}
x_43 = 0;
x_44 = lean_box(x_43);
if (lean_is_scalar(x_42)) {
 x_45 = lean_alloc_ctor(0, 2, 0);
} else {
 x_45 = x_42;
}
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_41);
return x_45;
}
}
else
{
uint8_t x_46; lean_object* x_47; 
lean_dec(x_1);
x_46 = 1;
x_47 = lean_box(x_46);
lean_ctor_set(x_10, 0, x_47);
return x_10;
}
}
else
{
lean_object* x_48; lean_object* x_49; size_t x_50; size_t x_51; size_t x_52; lean_object* x_53; lean_object* x_54; size_t x_55; uint8_t x_56; 
x_48 = lean_ctor_get(x_10, 0);
x_49 = lean_ctor_get(x_10, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_10);
x_50 = lean_ptr_addr(x_1);
x_51 = 8191;
x_52 = lean_usize_mod(x_50, x_51);
x_53 = lean_ctor_get(x_48, 0);
lean_inc(x_53);
lean_dec(x_48);
x_54 = lean_array_uget(x_53, x_52);
lean_dec(x_53);
x_55 = lean_ptr_addr(x_54);
lean_dec(x_54);
x_56 = lean_usize_dec_eq(x_55, x_50);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; lean_object* x_69; lean_object* x_70; 
x_57 = lean_st_ref_take(x_2, x_49);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
x_60 = lean_ctor_get(x_58, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_58, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 x_62 = x_58;
} else {
 lean_dec_ref(x_58);
 x_62 = lean_box(0);
}
x_63 = lean_array_uset(x_60, x_52, x_1);
if (lean_is_scalar(x_62)) {
 x_64 = lean_alloc_ctor(0, 2, 0);
} else {
 x_64 = x_62;
}
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_61);
x_65 = lean_st_ref_set(x_2, x_64, x_59);
x_66 = lean_ctor_get(x_65, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_67 = x_65;
} else {
 lean_dec_ref(x_65);
 x_67 = lean_box(0);
}
x_68 = 0;
x_69 = lean_box(x_68);
if (lean_is_scalar(x_67)) {
 x_70 = lean_alloc_ctor(0, 2, 0);
} else {
 x_70 = x_67;
}
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_66);
return x_70;
}
else
{
uint8_t x_71; lean_object* x_72; lean_object* x_73; 
lean_dec(x_1);
x_71 = 1;
x_72 = lean_box(x_71);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_49);
return x_73;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_checked___at_Lean_Compiler_LCNF_Closure_collectType___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_st_ref_get(x_2, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = !lean_is_exclusive(x_10);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint64_t x_18; uint64_t x_19; uint64_t x_20; uint64_t x_21; uint64_t x_22; uint64_t x_23; uint64_t x_24; size_t x_25; size_t x_26; size_t x_27; size_t x_28; size_t x_29; lean_object* x_30; uint8_t x_31; 
x_14 = lean_ctor_get(x_10, 1);
x_15 = lean_ctor_get(x_10, 0);
lean_dec(x_15);
x_16 = lean_ctor_get(x_12, 1);
lean_inc(x_16);
lean_dec(x_12);
x_17 = lean_array_get_size(x_16);
x_18 = l_Lean_Expr_hash(x_1);
x_19 = 32;
x_20 = lean_uint64_shift_right(x_18, x_19);
x_21 = lean_uint64_xor(x_18, x_20);
x_22 = 16;
x_23 = lean_uint64_shift_right(x_21, x_22);
x_24 = lean_uint64_xor(x_21, x_23);
x_25 = lean_uint64_to_usize(x_24);
x_26 = lean_usize_of_nat(x_17);
lean_dec(x_17);
x_27 = 1;
x_28 = lean_usize_sub(x_26, x_27);
x_29 = lean_usize_land(x_25, x_28);
x_30 = lean_array_uget(x_16, x_29);
lean_dec(x_16);
x_31 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_CollectMVars_visit___spec__1(x_1, x_30);
lean_dec(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
lean_free_object(x_10);
x_32 = lean_st_ref_take(x_2, x_14);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
x_35 = lean_ctor_get(x_32, 1);
lean_inc(x_35);
lean_dec(x_32);
x_36 = !lean_is_exclusive(x_33);
if (x_36 == 0)
{
lean_object* x_37; uint8_t x_38; 
x_37 = lean_ctor_get(x_33, 1);
lean_dec(x_37);
x_38 = !lean_is_exclusive(x_34);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; size_t x_42; size_t x_43; size_t x_44; lean_object* x_45; uint8_t x_46; 
x_39 = lean_ctor_get(x_34, 0);
x_40 = lean_ctor_get(x_34, 1);
x_41 = lean_array_get_size(x_40);
x_42 = lean_usize_of_nat(x_41);
lean_dec(x_41);
x_43 = lean_usize_sub(x_42, x_27);
x_44 = lean_usize_land(x_25, x_43);
x_45 = lean_array_uget(x_40, x_44);
x_46 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_CollectMVars_visit___spec__1(x_1, x_45);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_47 = lean_unsigned_to_nat(1u);
x_48 = lean_nat_add(x_39, x_47);
lean_dec(x_39);
x_49 = lean_box(0);
x_50 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_50, 0, x_1);
lean_ctor_set(x_50, 1, x_49);
lean_ctor_set(x_50, 2, x_45);
x_51 = lean_array_uset(x_40, x_44, x_50);
x_52 = lean_unsigned_to_nat(4u);
x_53 = lean_nat_mul(x_48, x_52);
x_54 = lean_unsigned_to_nat(3u);
x_55 = lean_nat_div(x_53, x_54);
lean_dec(x_53);
x_56 = lean_array_get_size(x_51);
x_57 = lean_nat_dec_le(x_55, x_56);
lean_dec(x_56);
lean_dec(x_55);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_58 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_CollectMVars_visit___spec__2(x_51);
lean_ctor_set(x_34, 1, x_58);
lean_ctor_set(x_34, 0, x_48);
x_59 = lean_st_ref_set(x_2, x_33, x_35);
x_60 = !lean_is_exclusive(x_59);
if (x_60 == 0)
{
lean_object* x_61; uint8_t x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_59, 0);
lean_dec(x_61);
x_62 = 0;
x_63 = lean_box(x_62);
lean_ctor_set(x_59, 0, x_63);
return x_59;
}
else
{
lean_object* x_64; uint8_t x_65; lean_object* x_66; lean_object* x_67; 
x_64 = lean_ctor_get(x_59, 1);
lean_inc(x_64);
lean_dec(x_59);
x_65 = 0;
x_66 = lean_box(x_65);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_64);
return x_67;
}
}
else
{
lean_object* x_68; uint8_t x_69; 
lean_ctor_set(x_34, 1, x_51);
lean_ctor_set(x_34, 0, x_48);
x_68 = lean_st_ref_set(x_2, x_33, x_35);
x_69 = !lean_is_exclusive(x_68);
if (x_69 == 0)
{
lean_object* x_70; uint8_t x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_68, 0);
lean_dec(x_70);
x_71 = 0;
x_72 = lean_box(x_71);
lean_ctor_set(x_68, 0, x_72);
return x_68;
}
else
{
lean_object* x_73; uint8_t x_74; lean_object* x_75; lean_object* x_76; 
x_73 = lean_ctor_get(x_68, 1);
lean_inc(x_73);
lean_dec(x_68);
x_74 = 0;
x_75 = lean_box(x_74);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_73);
return x_76;
}
}
}
else
{
lean_object* x_77; uint8_t x_78; 
lean_dec(x_45);
lean_dec(x_1);
x_77 = lean_st_ref_set(x_2, x_33, x_35);
x_78 = !lean_is_exclusive(x_77);
if (x_78 == 0)
{
lean_object* x_79; uint8_t x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_77, 0);
lean_dec(x_79);
x_80 = 0;
x_81 = lean_box(x_80);
lean_ctor_set(x_77, 0, x_81);
return x_77;
}
else
{
lean_object* x_82; uint8_t x_83; lean_object* x_84; lean_object* x_85; 
x_82 = lean_ctor_get(x_77, 1);
lean_inc(x_82);
lean_dec(x_77);
x_83 = 0;
x_84 = lean_box(x_83);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_82);
return x_85;
}
}
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; size_t x_89; size_t x_90; size_t x_91; lean_object* x_92; uint8_t x_93; 
x_86 = lean_ctor_get(x_34, 0);
x_87 = lean_ctor_get(x_34, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_34);
x_88 = lean_array_get_size(x_87);
x_89 = lean_usize_of_nat(x_88);
lean_dec(x_88);
x_90 = lean_usize_sub(x_89, x_27);
x_91 = lean_usize_land(x_25, x_90);
x_92 = lean_array_uget(x_87, x_91);
x_93 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_CollectMVars_visit___spec__1(x_1, x_92);
if (x_93 == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; uint8_t x_104; 
x_94 = lean_unsigned_to_nat(1u);
x_95 = lean_nat_add(x_86, x_94);
lean_dec(x_86);
x_96 = lean_box(0);
x_97 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_97, 0, x_1);
lean_ctor_set(x_97, 1, x_96);
lean_ctor_set(x_97, 2, x_92);
x_98 = lean_array_uset(x_87, x_91, x_97);
x_99 = lean_unsigned_to_nat(4u);
x_100 = lean_nat_mul(x_95, x_99);
x_101 = lean_unsigned_to_nat(3u);
x_102 = lean_nat_div(x_100, x_101);
lean_dec(x_100);
x_103 = lean_array_get_size(x_98);
x_104 = lean_nat_dec_le(x_102, x_103);
lean_dec(x_103);
lean_dec(x_102);
if (x_104 == 0)
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; uint8_t x_110; lean_object* x_111; lean_object* x_112; 
x_105 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_CollectMVars_visit___spec__2(x_98);
x_106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_106, 0, x_95);
lean_ctor_set(x_106, 1, x_105);
lean_ctor_set(x_33, 1, x_106);
x_107 = lean_st_ref_set(x_2, x_33, x_35);
x_108 = lean_ctor_get(x_107, 1);
lean_inc(x_108);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 lean_ctor_release(x_107, 1);
 x_109 = x_107;
} else {
 lean_dec_ref(x_107);
 x_109 = lean_box(0);
}
x_110 = 0;
x_111 = lean_box(x_110);
if (lean_is_scalar(x_109)) {
 x_112 = lean_alloc_ctor(0, 2, 0);
} else {
 x_112 = x_109;
}
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_108);
return x_112;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; uint8_t x_117; lean_object* x_118; lean_object* x_119; 
x_113 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_113, 0, x_95);
lean_ctor_set(x_113, 1, x_98);
lean_ctor_set(x_33, 1, x_113);
x_114 = lean_st_ref_set(x_2, x_33, x_35);
x_115 = lean_ctor_get(x_114, 1);
lean_inc(x_115);
if (lean_is_exclusive(x_114)) {
 lean_ctor_release(x_114, 0);
 lean_ctor_release(x_114, 1);
 x_116 = x_114;
} else {
 lean_dec_ref(x_114);
 x_116 = lean_box(0);
}
x_117 = 0;
x_118 = lean_box(x_117);
if (lean_is_scalar(x_116)) {
 x_119 = lean_alloc_ctor(0, 2, 0);
} else {
 x_119 = x_116;
}
lean_ctor_set(x_119, 0, x_118);
lean_ctor_set(x_119, 1, x_115);
return x_119;
}
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; uint8_t x_124; lean_object* x_125; lean_object* x_126; 
lean_dec(x_92);
lean_dec(x_1);
x_120 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_120, 0, x_86);
lean_ctor_set(x_120, 1, x_87);
lean_ctor_set(x_33, 1, x_120);
x_121 = lean_st_ref_set(x_2, x_33, x_35);
x_122 = lean_ctor_get(x_121, 1);
lean_inc(x_122);
if (lean_is_exclusive(x_121)) {
 lean_ctor_release(x_121, 0);
 lean_ctor_release(x_121, 1);
 x_123 = x_121;
} else {
 lean_dec_ref(x_121);
 x_123 = lean_box(0);
}
x_124 = 0;
x_125 = lean_box(x_124);
if (lean_is_scalar(x_123)) {
 x_126 = lean_alloc_ctor(0, 2, 0);
} else {
 x_126 = x_123;
}
lean_ctor_set(x_126, 0, x_125);
lean_ctor_set(x_126, 1, x_122);
return x_126;
}
}
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; size_t x_132; size_t x_133; size_t x_134; lean_object* x_135; uint8_t x_136; 
x_127 = lean_ctor_get(x_33, 0);
lean_inc(x_127);
lean_dec(x_33);
x_128 = lean_ctor_get(x_34, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_34, 1);
lean_inc(x_129);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 x_130 = x_34;
} else {
 lean_dec_ref(x_34);
 x_130 = lean_box(0);
}
x_131 = lean_array_get_size(x_129);
x_132 = lean_usize_of_nat(x_131);
lean_dec(x_131);
x_133 = lean_usize_sub(x_132, x_27);
x_134 = lean_usize_land(x_25, x_133);
x_135 = lean_array_uget(x_129, x_134);
x_136 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_CollectMVars_visit___spec__1(x_1, x_135);
if (x_136 == 0)
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; uint8_t x_147; 
x_137 = lean_unsigned_to_nat(1u);
x_138 = lean_nat_add(x_128, x_137);
lean_dec(x_128);
x_139 = lean_box(0);
x_140 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_140, 0, x_1);
lean_ctor_set(x_140, 1, x_139);
lean_ctor_set(x_140, 2, x_135);
x_141 = lean_array_uset(x_129, x_134, x_140);
x_142 = lean_unsigned_to_nat(4u);
x_143 = lean_nat_mul(x_138, x_142);
x_144 = lean_unsigned_to_nat(3u);
x_145 = lean_nat_div(x_143, x_144);
lean_dec(x_143);
x_146 = lean_array_get_size(x_141);
x_147 = lean_nat_dec_le(x_145, x_146);
lean_dec(x_146);
lean_dec(x_145);
if (x_147 == 0)
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; uint8_t x_154; lean_object* x_155; lean_object* x_156; 
x_148 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_CollectMVars_visit___spec__2(x_141);
if (lean_is_scalar(x_130)) {
 x_149 = lean_alloc_ctor(0, 2, 0);
} else {
 x_149 = x_130;
}
lean_ctor_set(x_149, 0, x_138);
lean_ctor_set(x_149, 1, x_148);
x_150 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_150, 0, x_127);
lean_ctor_set(x_150, 1, x_149);
x_151 = lean_st_ref_set(x_2, x_150, x_35);
x_152 = lean_ctor_get(x_151, 1);
lean_inc(x_152);
if (lean_is_exclusive(x_151)) {
 lean_ctor_release(x_151, 0);
 lean_ctor_release(x_151, 1);
 x_153 = x_151;
} else {
 lean_dec_ref(x_151);
 x_153 = lean_box(0);
}
x_154 = 0;
x_155 = lean_box(x_154);
if (lean_is_scalar(x_153)) {
 x_156 = lean_alloc_ctor(0, 2, 0);
} else {
 x_156 = x_153;
}
lean_ctor_set(x_156, 0, x_155);
lean_ctor_set(x_156, 1, x_152);
return x_156;
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; uint8_t x_162; lean_object* x_163; lean_object* x_164; 
if (lean_is_scalar(x_130)) {
 x_157 = lean_alloc_ctor(0, 2, 0);
} else {
 x_157 = x_130;
}
lean_ctor_set(x_157, 0, x_138);
lean_ctor_set(x_157, 1, x_141);
x_158 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_158, 0, x_127);
lean_ctor_set(x_158, 1, x_157);
x_159 = lean_st_ref_set(x_2, x_158, x_35);
x_160 = lean_ctor_get(x_159, 1);
lean_inc(x_160);
if (lean_is_exclusive(x_159)) {
 lean_ctor_release(x_159, 0);
 lean_ctor_release(x_159, 1);
 x_161 = x_159;
} else {
 lean_dec_ref(x_159);
 x_161 = lean_box(0);
}
x_162 = 0;
x_163 = lean_box(x_162);
if (lean_is_scalar(x_161)) {
 x_164 = lean_alloc_ctor(0, 2, 0);
} else {
 x_164 = x_161;
}
lean_ctor_set(x_164, 0, x_163);
lean_ctor_set(x_164, 1, x_160);
return x_164;
}
}
else
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; uint8_t x_170; lean_object* x_171; lean_object* x_172; 
lean_dec(x_135);
lean_dec(x_1);
if (lean_is_scalar(x_130)) {
 x_165 = lean_alloc_ctor(0, 2, 0);
} else {
 x_165 = x_130;
}
lean_ctor_set(x_165, 0, x_128);
lean_ctor_set(x_165, 1, x_129);
x_166 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_166, 0, x_127);
lean_ctor_set(x_166, 1, x_165);
x_167 = lean_st_ref_set(x_2, x_166, x_35);
x_168 = lean_ctor_get(x_167, 1);
lean_inc(x_168);
if (lean_is_exclusive(x_167)) {
 lean_ctor_release(x_167, 0);
 lean_ctor_release(x_167, 1);
 x_169 = x_167;
} else {
 lean_dec_ref(x_167);
 x_169 = lean_box(0);
}
x_170 = 0;
x_171 = lean_box(x_170);
if (lean_is_scalar(x_169)) {
 x_172 = lean_alloc_ctor(0, 2, 0);
} else {
 x_172 = x_169;
}
lean_ctor_set(x_172, 0, x_171);
lean_ctor_set(x_172, 1, x_168);
return x_172;
}
}
}
else
{
uint8_t x_173; lean_object* x_174; 
lean_dec(x_1);
x_173 = 1;
x_174 = lean_box(x_173);
lean_ctor_set(x_10, 0, x_174);
return x_10;
}
}
else
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; uint64_t x_178; uint64_t x_179; uint64_t x_180; uint64_t x_181; uint64_t x_182; uint64_t x_183; uint64_t x_184; size_t x_185; size_t x_186; size_t x_187; size_t x_188; size_t x_189; lean_object* x_190; uint8_t x_191; 
x_175 = lean_ctor_get(x_10, 1);
lean_inc(x_175);
lean_dec(x_10);
x_176 = lean_ctor_get(x_12, 1);
lean_inc(x_176);
lean_dec(x_12);
x_177 = lean_array_get_size(x_176);
x_178 = l_Lean_Expr_hash(x_1);
x_179 = 32;
x_180 = lean_uint64_shift_right(x_178, x_179);
x_181 = lean_uint64_xor(x_178, x_180);
x_182 = 16;
x_183 = lean_uint64_shift_right(x_181, x_182);
x_184 = lean_uint64_xor(x_181, x_183);
x_185 = lean_uint64_to_usize(x_184);
x_186 = lean_usize_of_nat(x_177);
lean_dec(x_177);
x_187 = 1;
x_188 = lean_usize_sub(x_186, x_187);
x_189 = lean_usize_land(x_185, x_188);
x_190 = lean_array_uget(x_176, x_189);
lean_dec(x_176);
x_191 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_CollectMVars_visit___spec__1(x_1, x_190);
lean_dec(x_190);
if (x_191 == 0)
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; size_t x_202; size_t x_203; size_t x_204; lean_object* x_205; uint8_t x_206; 
x_192 = lean_st_ref_take(x_2, x_175);
x_193 = lean_ctor_get(x_192, 0);
lean_inc(x_193);
x_194 = lean_ctor_get(x_193, 1);
lean_inc(x_194);
x_195 = lean_ctor_get(x_192, 1);
lean_inc(x_195);
lean_dec(x_192);
x_196 = lean_ctor_get(x_193, 0);
lean_inc(x_196);
if (lean_is_exclusive(x_193)) {
 lean_ctor_release(x_193, 0);
 lean_ctor_release(x_193, 1);
 x_197 = x_193;
} else {
 lean_dec_ref(x_193);
 x_197 = lean_box(0);
}
x_198 = lean_ctor_get(x_194, 0);
lean_inc(x_198);
x_199 = lean_ctor_get(x_194, 1);
lean_inc(x_199);
if (lean_is_exclusive(x_194)) {
 lean_ctor_release(x_194, 0);
 lean_ctor_release(x_194, 1);
 x_200 = x_194;
} else {
 lean_dec_ref(x_194);
 x_200 = lean_box(0);
}
x_201 = lean_array_get_size(x_199);
x_202 = lean_usize_of_nat(x_201);
lean_dec(x_201);
x_203 = lean_usize_sub(x_202, x_187);
x_204 = lean_usize_land(x_185, x_203);
x_205 = lean_array_uget(x_199, x_204);
x_206 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_CollectMVars_visit___spec__1(x_1, x_205);
if (x_206 == 0)
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; uint8_t x_217; 
x_207 = lean_unsigned_to_nat(1u);
x_208 = lean_nat_add(x_198, x_207);
lean_dec(x_198);
x_209 = lean_box(0);
x_210 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_210, 0, x_1);
lean_ctor_set(x_210, 1, x_209);
lean_ctor_set(x_210, 2, x_205);
x_211 = lean_array_uset(x_199, x_204, x_210);
x_212 = lean_unsigned_to_nat(4u);
x_213 = lean_nat_mul(x_208, x_212);
x_214 = lean_unsigned_to_nat(3u);
x_215 = lean_nat_div(x_213, x_214);
lean_dec(x_213);
x_216 = lean_array_get_size(x_211);
x_217 = lean_nat_dec_le(x_215, x_216);
lean_dec(x_216);
lean_dec(x_215);
if (x_217 == 0)
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; uint8_t x_224; lean_object* x_225; lean_object* x_226; 
x_218 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_CollectMVars_visit___spec__2(x_211);
if (lean_is_scalar(x_200)) {
 x_219 = lean_alloc_ctor(0, 2, 0);
} else {
 x_219 = x_200;
}
lean_ctor_set(x_219, 0, x_208);
lean_ctor_set(x_219, 1, x_218);
if (lean_is_scalar(x_197)) {
 x_220 = lean_alloc_ctor(0, 2, 0);
} else {
 x_220 = x_197;
}
lean_ctor_set(x_220, 0, x_196);
lean_ctor_set(x_220, 1, x_219);
x_221 = lean_st_ref_set(x_2, x_220, x_195);
x_222 = lean_ctor_get(x_221, 1);
lean_inc(x_222);
if (lean_is_exclusive(x_221)) {
 lean_ctor_release(x_221, 0);
 lean_ctor_release(x_221, 1);
 x_223 = x_221;
} else {
 lean_dec_ref(x_221);
 x_223 = lean_box(0);
}
x_224 = 0;
x_225 = lean_box(x_224);
if (lean_is_scalar(x_223)) {
 x_226 = lean_alloc_ctor(0, 2, 0);
} else {
 x_226 = x_223;
}
lean_ctor_set(x_226, 0, x_225);
lean_ctor_set(x_226, 1, x_222);
return x_226;
}
else
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; uint8_t x_232; lean_object* x_233; lean_object* x_234; 
if (lean_is_scalar(x_200)) {
 x_227 = lean_alloc_ctor(0, 2, 0);
} else {
 x_227 = x_200;
}
lean_ctor_set(x_227, 0, x_208);
lean_ctor_set(x_227, 1, x_211);
if (lean_is_scalar(x_197)) {
 x_228 = lean_alloc_ctor(0, 2, 0);
} else {
 x_228 = x_197;
}
lean_ctor_set(x_228, 0, x_196);
lean_ctor_set(x_228, 1, x_227);
x_229 = lean_st_ref_set(x_2, x_228, x_195);
x_230 = lean_ctor_get(x_229, 1);
lean_inc(x_230);
if (lean_is_exclusive(x_229)) {
 lean_ctor_release(x_229, 0);
 lean_ctor_release(x_229, 1);
 x_231 = x_229;
} else {
 lean_dec_ref(x_229);
 x_231 = lean_box(0);
}
x_232 = 0;
x_233 = lean_box(x_232);
if (lean_is_scalar(x_231)) {
 x_234 = lean_alloc_ctor(0, 2, 0);
} else {
 x_234 = x_231;
}
lean_ctor_set(x_234, 0, x_233);
lean_ctor_set(x_234, 1, x_230);
return x_234;
}
}
else
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; uint8_t x_240; lean_object* x_241; lean_object* x_242; 
lean_dec(x_205);
lean_dec(x_1);
if (lean_is_scalar(x_200)) {
 x_235 = lean_alloc_ctor(0, 2, 0);
} else {
 x_235 = x_200;
}
lean_ctor_set(x_235, 0, x_198);
lean_ctor_set(x_235, 1, x_199);
if (lean_is_scalar(x_197)) {
 x_236 = lean_alloc_ctor(0, 2, 0);
} else {
 x_236 = x_197;
}
lean_ctor_set(x_236, 0, x_196);
lean_ctor_set(x_236, 1, x_235);
x_237 = lean_st_ref_set(x_2, x_236, x_195);
x_238 = lean_ctor_get(x_237, 1);
lean_inc(x_238);
if (lean_is_exclusive(x_237)) {
 lean_ctor_release(x_237, 0);
 lean_ctor_release(x_237, 1);
 x_239 = x_237;
} else {
 lean_dec_ref(x_237);
 x_239 = lean_box(0);
}
x_240 = 0;
x_241 = lean_box(x_240);
if (lean_is_scalar(x_239)) {
 x_242 = lean_alloc_ctor(0, 2, 0);
} else {
 x_242 = x_239;
}
lean_ctor_set(x_242, 0, x_241);
lean_ctor_set(x_242, 1, x_238);
return x_242;
}
}
else
{
uint8_t x_243; lean_object* x_244; lean_object* x_245; 
lean_dec(x_1);
x_243 = 1;
x_244 = lean_box(x_243);
x_245 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_245, 0, x_244);
lean_ctor_set(x_245, 1, x_175);
return x_245;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visit_go___at_Lean_Compiler_LCNF_Closure_collectType___spec__2___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 5:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_1, 1);
lean_inc(x_15);
lean_dec(x_1);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_3);
lean_inc(x_2);
x_16 = l_Lean_ForEachExprWhere_visit_go___at_Lean_Compiler_LCNF_Closure_collectType___spec__2(x_2, x_3, x_4, x_14, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = l_Lean_ForEachExprWhere_visit_go___at_Lean_Compiler_LCNF_Closure_collectType___spec__2(x_2, x_3, x_4, x_15, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_17);
return x_18;
}
else
{
uint8_t x_19; 
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
x_19 = !lean_is_exclusive(x_16);
if (x_19 == 0)
{
return x_16;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_16, 0);
x_21 = lean_ctor_get(x_16, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_16);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
case 6:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_1, 1);
lean_inc(x_23);
x_24 = lean_ctor_get(x_1, 2);
lean_inc(x_24);
lean_dec(x_1);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_3);
lean_inc(x_2);
x_25 = l_Lean_ForEachExprWhere_visit_go___at_Lean_Compiler_LCNF_Closure_collectType___spec__2(x_2, x_3, x_4, x_23, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec(x_25);
x_27 = l_Lean_ForEachExprWhere_visit_go___at_Lean_Compiler_LCNF_Closure_collectType___spec__2(x_2, x_3, x_4, x_24, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_26);
return x_27;
}
else
{
uint8_t x_28; 
lean_dec(x_24);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
x_28 = !lean_is_exclusive(x_25);
if (x_28 == 0)
{
return x_25;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_25, 0);
x_30 = lean_ctor_get(x_25, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_25);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
case 7:
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_1, 1);
lean_inc(x_32);
x_33 = lean_ctor_get(x_1, 2);
lean_inc(x_33);
lean_dec(x_1);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_3);
lean_inc(x_2);
x_34 = l_Lean_ForEachExprWhere_visit_go___at_Lean_Compiler_LCNF_Closure_collectType___spec__2(x_2, x_3, x_4, x_32, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
lean_dec(x_34);
x_36 = l_Lean_ForEachExprWhere_visit_go___at_Lean_Compiler_LCNF_Closure_collectType___spec__2(x_2, x_3, x_4, x_33, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_35);
return x_36;
}
else
{
uint8_t x_37; 
lean_dec(x_33);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
x_37 = !lean_is_exclusive(x_34);
if (x_37 == 0)
{
return x_34;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_34, 0);
x_39 = lean_ctor_get(x_34, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_34);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
case 8:
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_41 = lean_ctor_get(x_1, 1);
lean_inc(x_41);
x_42 = lean_ctor_get(x_1, 2);
lean_inc(x_42);
x_43 = lean_ctor_get(x_1, 3);
lean_inc(x_43);
lean_dec(x_1);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_3);
lean_inc(x_2);
x_44 = l_Lean_ForEachExprWhere_visit_go___at_Lean_Compiler_LCNF_Closure_collectType___spec__2(x_2, x_3, x_4, x_41, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
lean_dec(x_44);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_3);
lean_inc(x_2);
x_46 = l_Lean_ForEachExprWhere_visit_go___at_Lean_Compiler_LCNF_Closure_collectType___spec__2(x_2, x_3, x_4, x_42, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_45);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_46, 1);
lean_inc(x_47);
lean_dec(x_46);
x_48 = l_Lean_ForEachExprWhere_visit_go___at_Lean_Compiler_LCNF_Closure_collectType___spec__2(x_2, x_3, x_4, x_43, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_47);
return x_48;
}
else
{
uint8_t x_49; 
lean_dec(x_43);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
x_49 = !lean_is_exclusive(x_46);
if (x_49 == 0)
{
return x_46;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_46, 0);
x_51 = lean_ctor_get(x_46, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_46);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
else
{
uint8_t x_53; 
lean_dec(x_43);
lean_dec(x_42);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
x_53 = !lean_is_exclusive(x_44);
if (x_53 == 0)
{
return x_44;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_44, 0);
x_55 = lean_ctor_get(x_44, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_44);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
case 10:
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_1, 1);
lean_inc(x_57);
lean_dec(x_1);
x_58 = l_Lean_ForEachExprWhere_visit_go___at_Lean_Compiler_LCNF_Closure_collectType___spec__2(x_2, x_3, x_4, x_57, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_58;
}
case 11:
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_ctor_get(x_1, 2);
lean_inc(x_59);
lean_dec(x_1);
x_60 = l_Lean_ForEachExprWhere_visit_go___at_Lean_Compiler_LCNF_Closure_collectType___spec__2(x_2, x_3, x_4, x_59, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_60;
}
default: 
{
lean_object* x_61; lean_object* x_62; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_61 = lean_box(0);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_13);
return x_62;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visit_go___at_Lean_Compiler_LCNF_Closure_collectType___spec__2(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
lean_inc(x_4);
x_13 = l_Lean_ForEachExprWhere_visited___at_Lean_Compiler_LCNF_Closure_collectType___spec__3(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_unbox(x_14);
lean_dec(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec(x_13);
lean_inc(x_1);
lean_inc(x_4);
x_17 = lean_apply_1(x_1, x_4);
x_18 = lean_unbox(x_17);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_box(0);
x_20 = l_Lean_ForEachExprWhere_visit_go___at_Lean_Compiler_LCNF_Closure_collectType___spec__2___lambda__1(x_4, x_1, x_2, x_3, x_19, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_16);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
lean_inc(x_4);
x_21 = l_Lean_ForEachExprWhere_checked___at_Lean_Compiler_LCNF_Closure_collectType___spec__4(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_16);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_unbox(x_22);
lean_dec(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
lean_inc(x_2);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_25 = lean_apply_8(x_2, x_4, x_6, x_7, x_8, x_9, x_10, x_11, x_24);
if (lean_obj_tag(x_25) == 0)
{
if (x_3 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec(x_25);
x_27 = lean_box(0);
x_28 = l_Lean_ForEachExprWhere_visit_go___at_Lean_Compiler_LCNF_Closure_collectType___spec__2___lambda__1(x_4, x_1, x_2, x_3, x_27, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_26);
return x_28;
}
else
{
uint8_t x_29; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_29 = !lean_is_exclusive(x_25);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_25, 0);
lean_dec(x_30);
x_31 = lean_box(0);
lean_ctor_set(x_25, 0, x_31);
return x_25;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_25, 1);
lean_inc(x_32);
lean_dec(x_25);
x_33 = lean_box(0);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
return x_34;
}
}
}
else
{
uint8_t x_35; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_35 = !lean_is_exclusive(x_25);
if (x_35 == 0)
{
return x_25;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_25, 0);
x_37 = lean_ctor_get(x_25, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_25);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_21, 1);
lean_inc(x_39);
lean_dec(x_21);
x_40 = lean_box(0);
x_41 = l_Lean_ForEachExprWhere_visit_go___at_Lean_Compiler_LCNF_Closure_collectType___spec__2___lambda__1(x_4, x_1, x_2, x_3, x_40, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_39);
return x_41;
}
}
}
else
{
uint8_t x_42; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_42 = !lean_is_exclusive(x_13);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_13, 0);
lean_dec(x_43);
x_44 = lean_box(0);
lean_ctor_set(x_13, 0, x_44);
return x_13;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_13, 1);
lean_inc(x_45);
lean_dec(x_13);
x_46 = lean_box(0);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_45);
return x_47;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visit___at_Lean_Compiler_LCNF_Closure_collectType___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = l_Lean_ForEachExprWhere_initCache;
x_13 = lean_st_mk_ref(x_12, x_11);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_ForEachExprWhere_visit_go___at_Lean_Compiler_LCNF_Closure_collectType___spec__2(x_1, x_2, x_4, x_3, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_st_ref_get(x_14, x_18);
lean_dec(x_14);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_19, 0);
lean_dec(x_21);
lean_ctor_set(x_19, 0, x_17);
return x_19;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_17);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
else
{
uint8_t x_24; 
lean_dec(x_14);
x_24 = !lean_is_exclusive(x_16);
if (x_24 == 0)
{
return x_16;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_16, 0);
x_26 = lean_ctor_get(x_16, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_16);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Closure_collectType___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = l_Lean_Expr_fvarId_x21(x_1);
x_10 = l_Lean_Compiler_LCNF_Closure_collectFVar(x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Closure_collectType___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Expr_isFVar___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Closure_collectType___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Closure_collectType___lambda__1___boxed), 8, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Closure_collectType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_9 = l_Lean_Compiler_LCNF_Closure_collectType___closed__1;
x_10 = l_Lean_Compiler_LCNF_Closure_collectType___closed__2;
x_11 = 0;
x_12 = l_Lean_ForEachExprWhere_visit___at_Lean_Compiler_LCNF_Closure_collectType___spec__1(x_9, x_10, x_1, x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_12;
}
}
static lean_object* _init_l_panic___at_Lean_Compiler_LCNF_Closure_collectFVar___spec__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_instMonadCompilerM;
x_2 = l_ReaderT_instMonad___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_panic___at_Lean_Compiler_LCNF_Closure_collectFVar___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_panic___at_Lean_Compiler_LCNF_Closure_collectFVar___spec__1___closed__1;
x_2 = l_instInhabitedPUnit;
x_3 = l_instInhabitedOfMonad___rarg(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_panic___at_Lean_Compiler_LCNF_Closure_collectFVar___spec__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_panic___at_Lean_Compiler_LCNF_Closure_collectFVar___spec__1___closed__2;
x_2 = lean_alloc_closure((void*)(l_instInhabitedReaderT___rarg___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_Compiler_LCNF_Closure_collectFVar___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = l_panic___at_Lean_Compiler_LCNF_Closure_collectFVar___spec__1___closed__3;
x_10 = lean_panic_fn(x_9, x_1);
x_11 = lean_apply_7(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Closure_collectFVar___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Compiler.LCNF.Closure", 26, 26);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Closure_collectFVar___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Compiler.LCNF.Closure.collectFVar", 38, 38);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Closure_collectFVar___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Closure_collectFVar___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Compiler_LCNF_Closure_collectFVar___closed__1;
x_2 = l_Lean_Compiler_LCNF_Closure_collectFVar___closed__2;
x_3 = lean_unsigned_to_nat(151u);
x_4 = lean_unsigned_to_nat(10u);
x_5 = l_Lean_Compiler_LCNF_Closure_collectFVar___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Closure_collectFVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_st_ref_get(x_3, x_8);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_RBNode_findCore___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__2(x_13, x_1);
lean_dec(x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; uint8_t x_16; 
lean_free_object(x_9);
lean_inc(x_1);
x_15 = l_Lean_Compiler_LCNF_Closure_markVisited(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_12);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_17 = lean_ctor_get(x_15, 1);
x_18 = lean_ctor_get(x_15, 0);
lean_dec(x_18);
x_19 = lean_ctor_get(x_2, 0);
lean_inc(x_19);
lean_inc(x_1);
x_20 = lean_apply_1(x_19, x_1);
x_21 = lean_unbox(x_20);
lean_dec(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_22 = lean_box(0);
lean_ctor_set(x_15, 0, x_22);
return x_15;
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_free_object(x_15);
x_23 = l_Lean_Compiler_LCNF_findFunDecl_x3f(x_1, x_4, x_5, x_6, x_7, x_17);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l_Lean_Compiler_LCNF_findParam_x3f(x_1, x_4, x_5, x_6, x_7, x_25);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = l_Lean_Compiler_LCNF_findLetDecl_x3f(x_1, x_4, x_5, x_6, x_7, x_28);
lean_dec(x_1);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = l_Lean_Compiler_LCNF_Closure_collectFVar___closed__4;
x_33 = l_panic___at_Lean_Compiler_LCNF_Closure_collectFVar___spec__1(x_32, x_2, x_3, x_4, x_5, x_6, x_7, x_31);
return x_33;
}
else
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_30);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; lean_object* x_44; 
x_35 = lean_ctor_get(x_30, 0);
x_36 = lean_ctor_get(x_29, 1);
lean_inc(x_36);
lean_dec(x_29);
x_37 = lean_ctor_get(x_35, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_35, 1);
lean_inc(x_38);
x_39 = lean_ctor_get(x_35, 2);
lean_inc(x_39);
x_40 = lean_ctor_get(x_35, 3);
lean_inc(x_40);
x_41 = lean_alloc_closure((void*)(l_Lean_Expr_isFVar___boxed), 1, 0);
x_42 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Closure_collectType___lambda__1___boxed), 8, 0);
x_43 = 0;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_39);
x_44 = l_Lean_ForEachExprWhere_visit___at_Lean_Compiler_LCNF_Closure_collectType___spec__1(x_41, x_42, x_39, x_43, x_2, x_3, x_4, x_5, x_6, x_7, x_36);
if (lean_obj_tag(x_44) == 0)
{
uint8_t x_45; 
x_45 = lean_ctor_get_uint8(x_2, sizeof(void*)*2);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = lean_ctor_get(x_2, 1);
lean_inc(x_47);
lean_inc(x_37);
x_48 = lean_apply_1(x_47, x_37);
x_49 = lean_unbox(x_48);
lean_dec(x_48);
if (x_49 == 0)
{
lean_object* x_50; 
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_37);
lean_inc(x_3);
x_50 = l_Lean_Compiler_LCNF_Closure_collectLetValue(x_40, x_2, x_3, x_4, x_5, x_6, x_7, x_46);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_51 = lean_ctor_get(x_50, 1);
lean_inc(x_51);
lean_dec(x_50);
x_52 = lean_st_ref_take(x_3, x_51);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
x_55 = !lean_is_exclusive(x_53);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_56 = lean_ctor_get(x_53, 2);
lean_ctor_set_tag(x_30, 0);
x_57 = lean_array_push(x_56, x_30);
lean_ctor_set(x_53, 2, x_57);
x_58 = lean_st_ref_set(x_3, x_53, x_54);
lean_dec(x_3);
x_59 = !lean_is_exclusive(x_58);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_58, 0);
lean_dec(x_60);
x_61 = lean_box(0);
lean_ctor_set(x_58, 0, x_61);
return x_58;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_58, 1);
lean_inc(x_62);
lean_dec(x_58);
x_63 = lean_box(0);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_62);
return x_64;
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_65 = lean_ctor_get(x_53, 0);
x_66 = lean_ctor_get(x_53, 1);
x_67 = lean_ctor_get(x_53, 2);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_53);
lean_ctor_set_tag(x_30, 0);
x_68 = lean_array_push(x_67, x_30);
x_69 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_69, 0, x_65);
lean_ctor_set(x_69, 1, x_66);
lean_ctor_set(x_69, 2, x_68);
x_70 = lean_st_ref_set(x_3, x_69, x_54);
lean_dec(x_3);
x_71 = lean_ctor_get(x_70, 1);
lean_inc(x_71);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 lean_ctor_release(x_70, 1);
 x_72 = x_70;
} else {
 lean_dec_ref(x_70);
 x_72 = lean_box(0);
}
x_73 = lean_box(0);
if (lean_is_scalar(x_72)) {
 x_74 = lean_alloc_ctor(0, 2, 0);
} else {
 x_74 = x_72;
}
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_71);
return x_74;
}
}
else
{
uint8_t x_75; 
lean_free_object(x_30);
lean_dec(x_35);
lean_dec(x_3);
x_75 = !lean_is_exclusive(x_50);
if (x_75 == 0)
{
return x_50;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_50, 0);
x_77 = lean_ctor_get(x_50, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_50);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
return x_78;
}
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; 
lean_dec(x_40);
lean_free_object(x_30);
lean_dec(x_35);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_79 = lean_st_ref_take(x_3, x_46);
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
lean_dec(x_79);
x_82 = !lean_is_exclusive(x_80);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_83 = lean_ctor_get(x_80, 1);
x_84 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_84, 0, x_37);
lean_ctor_set(x_84, 1, x_38);
lean_ctor_set(x_84, 2, x_39);
lean_ctor_set_uint8(x_84, sizeof(void*)*3, x_43);
x_85 = lean_array_push(x_83, x_84);
lean_ctor_set(x_80, 1, x_85);
x_86 = lean_st_ref_set(x_3, x_80, x_81);
lean_dec(x_3);
x_87 = !lean_is_exclusive(x_86);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; 
x_88 = lean_ctor_get(x_86, 0);
lean_dec(x_88);
x_89 = lean_box(0);
lean_ctor_set(x_86, 0, x_89);
return x_86;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_86, 1);
lean_inc(x_90);
lean_dec(x_86);
x_91 = lean_box(0);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_90);
return x_92;
}
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_93 = lean_ctor_get(x_80, 0);
x_94 = lean_ctor_get(x_80, 1);
x_95 = lean_ctor_get(x_80, 2);
lean_inc(x_95);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_80);
x_96 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_96, 0, x_37);
lean_ctor_set(x_96, 1, x_38);
lean_ctor_set(x_96, 2, x_39);
lean_ctor_set_uint8(x_96, sizeof(void*)*3, x_43);
x_97 = lean_array_push(x_94, x_96);
x_98 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_98, 0, x_93);
lean_ctor_set(x_98, 1, x_97);
lean_ctor_set(x_98, 2, x_95);
x_99 = lean_st_ref_set(x_3, x_98, x_81);
lean_dec(x_3);
x_100 = lean_ctor_get(x_99, 1);
lean_inc(x_100);
if (lean_is_exclusive(x_99)) {
 lean_ctor_release(x_99, 0);
 lean_ctor_release(x_99, 1);
 x_101 = x_99;
} else {
 lean_dec_ref(x_99);
 x_101 = lean_box(0);
}
x_102 = lean_box(0);
if (lean_is_scalar(x_101)) {
 x_103 = lean_alloc_ctor(0, 2, 0);
} else {
 x_103 = x_101;
}
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_100);
return x_103;
}
}
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; uint8_t x_108; 
lean_dec(x_40);
lean_free_object(x_30);
lean_dec(x_35);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_104 = lean_ctor_get(x_44, 1);
lean_inc(x_104);
lean_dec(x_44);
x_105 = lean_st_ref_take(x_3, x_104);
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_105, 1);
lean_inc(x_107);
lean_dec(x_105);
x_108 = !lean_is_exclusive(x_106);
if (x_108 == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; uint8_t x_113; 
x_109 = lean_ctor_get(x_106, 1);
x_110 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_110, 0, x_37);
lean_ctor_set(x_110, 1, x_38);
lean_ctor_set(x_110, 2, x_39);
lean_ctor_set_uint8(x_110, sizeof(void*)*3, x_43);
x_111 = lean_array_push(x_109, x_110);
lean_ctor_set(x_106, 1, x_111);
x_112 = lean_st_ref_set(x_3, x_106, x_107);
lean_dec(x_3);
x_113 = !lean_is_exclusive(x_112);
if (x_113 == 0)
{
lean_object* x_114; lean_object* x_115; 
x_114 = lean_ctor_get(x_112, 0);
lean_dec(x_114);
x_115 = lean_box(0);
lean_ctor_set(x_112, 0, x_115);
return x_112;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_116 = lean_ctor_get(x_112, 1);
lean_inc(x_116);
lean_dec(x_112);
x_117 = lean_box(0);
x_118 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_118, 0, x_117);
lean_ctor_set(x_118, 1, x_116);
return x_118;
}
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_119 = lean_ctor_get(x_106, 0);
x_120 = lean_ctor_get(x_106, 1);
x_121 = lean_ctor_get(x_106, 2);
lean_inc(x_121);
lean_inc(x_120);
lean_inc(x_119);
lean_dec(x_106);
x_122 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_122, 0, x_37);
lean_ctor_set(x_122, 1, x_38);
lean_ctor_set(x_122, 2, x_39);
lean_ctor_set_uint8(x_122, sizeof(void*)*3, x_43);
x_123 = lean_array_push(x_120, x_122);
x_124 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_124, 0, x_119);
lean_ctor_set(x_124, 1, x_123);
lean_ctor_set(x_124, 2, x_121);
x_125 = lean_st_ref_set(x_3, x_124, x_107);
lean_dec(x_3);
x_126 = lean_ctor_get(x_125, 1);
lean_inc(x_126);
if (lean_is_exclusive(x_125)) {
 lean_ctor_release(x_125, 0);
 lean_ctor_release(x_125, 1);
 x_127 = x_125;
} else {
 lean_dec_ref(x_125);
 x_127 = lean_box(0);
}
x_128 = lean_box(0);
if (lean_is_scalar(x_127)) {
 x_129 = lean_alloc_ctor(0, 2, 0);
} else {
 x_129 = x_127;
}
lean_ctor_set(x_129, 0, x_128);
lean_ctor_set(x_129, 1, x_126);
return x_129;
}
}
}
else
{
uint8_t x_130; 
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_37);
lean_free_object(x_30);
lean_dec(x_35);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_130 = !lean_is_exclusive(x_44);
if (x_130 == 0)
{
return x_44;
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_131 = lean_ctor_get(x_44, 0);
x_132 = lean_ctor_get(x_44, 1);
lean_inc(x_132);
lean_inc(x_131);
lean_dec(x_44);
x_133 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_133, 0, x_131);
lean_ctor_set(x_133, 1, x_132);
return x_133;
}
}
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; uint8_t x_142; lean_object* x_143; 
x_134 = lean_ctor_get(x_30, 0);
lean_inc(x_134);
lean_dec(x_30);
x_135 = lean_ctor_get(x_29, 1);
lean_inc(x_135);
lean_dec(x_29);
x_136 = lean_ctor_get(x_134, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_134, 1);
lean_inc(x_137);
x_138 = lean_ctor_get(x_134, 2);
lean_inc(x_138);
x_139 = lean_ctor_get(x_134, 3);
lean_inc(x_139);
x_140 = lean_alloc_closure((void*)(l_Lean_Expr_isFVar___boxed), 1, 0);
x_141 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Closure_collectType___lambda__1___boxed), 8, 0);
x_142 = 0;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_138);
x_143 = l_Lean_ForEachExprWhere_visit___at_Lean_Compiler_LCNF_Closure_collectType___spec__1(x_140, x_141, x_138, x_142, x_2, x_3, x_4, x_5, x_6, x_7, x_135);
if (lean_obj_tag(x_143) == 0)
{
uint8_t x_144; 
x_144 = lean_ctor_get_uint8(x_2, sizeof(void*)*2);
if (x_144 == 0)
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; uint8_t x_148; 
x_145 = lean_ctor_get(x_143, 1);
lean_inc(x_145);
lean_dec(x_143);
x_146 = lean_ctor_get(x_2, 1);
lean_inc(x_146);
lean_inc(x_136);
x_147 = lean_apply_1(x_146, x_136);
x_148 = lean_unbox(x_147);
lean_dec(x_147);
if (x_148 == 0)
{
lean_object* x_149; 
lean_dec(x_138);
lean_dec(x_137);
lean_dec(x_136);
lean_inc(x_3);
x_149 = l_Lean_Compiler_LCNF_Closure_collectLetValue(x_139, x_2, x_3, x_4, x_5, x_6, x_7, x_145);
if (lean_obj_tag(x_149) == 0)
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_150 = lean_ctor_get(x_149, 1);
lean_inc(x_150);
lean_dec(x_149);
x_151 = lean_st_ref_take(x_3, x_150);
x_152 = lean_ctor_get(x_151, 0);
lean_inc(x_152);
x_153 = lean_ctor_get(x_151, 1);
lean_inc(x_153);
lean_dec(x_151);
x_154 = lean_ctor_get(x_152, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_152, 1);
lean_inc(x_155);
x_156 = lean_ctor_get(x_152, 2);
lean_inc(x_156);
if (lean_is_exclusive(x_152)) {
 lean_ctor_release(x_152, 0);
 lean_ctor_release(x_152, 1);
 lean_ctor_release(x_152, 2);
 x_157 = x_152;
} else {
 lean_dec_ref(x_152);
 x_157 = lean_box(0);
}
x_158 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_158, 0, x_134);
x_159 = lean_array_push(x_156, x_158);
if (lean_is_scalar(x_157)) {
 x_160 = lean_alloc_ctor(0, 3, 0);
} else {
 x_160 = x_157;
}
lean_ctor_set(x_160, 0, x_154);
lean_ctor_set(x_160, 1, x_155);
lean_ctor_set(x_160, 2, x_159);
x_161 = lean_st_ref_set(x_3, x_160, x_153);
lean_dec(x_3);
x_162 = lean_ctor_get(x_161, 1);
lean_inc(x_162);
if (lean_is_exclusive(x_161)) {
 lean_ctor_release(x_161, 0);
 lean_ctor_release(x_161, 1);
 x_163 = x_161;
} else {
 lean_dec_ref(x_161);
 x_163 = lean_box(0);
}
x_164 = lean_box(0);
if (lean_is_scalar(x_163)) {
 x_165 = lean_alloc_ctor(0, 2, 0);
} else {
 x_165 = x_163;
}
lean_ctor_set(x_165, 0, x_164);
lean_ctor_set(x_165, 1, x_162);
return x_165;
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
lean_dec(x_134);
lean_dec(x_3);
x_166 = lean_ctor_get(x_149, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_149, 1);
lean_inc(x_167);
if (lean_is_exclusive(x_149)) {
 lean_ctor_release(x_149, 0);
 lean_ctor_release(x_149, 1);
 x_168 = x_149;
} else {
 lean_dec_ref(x_149);
 x_168 = lean_box(0);
}
if (lean_is_scalar(x_168)) {
 x_169 = lean_alloc_ctor(1, 2, 0);
} else {
 x_169 = x_168;
}
lean_ctor_set(x_169, 0, x_166);
lean_ctor_set(x_169, 1, x_167);
return x_169;
}
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; 
lean_dec(x_139);
lean_dec(x_134);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_170 = lean_st_ref_take(x_3, x_145);
x_171 = lean_ctor_get(x_170, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_170, 1);
lean_inc(x_172);
lean_dec(x_170);
x_173 = lean_ctor_get(x_171, 0);
lean_inc(x_173);
x_174 = lean_ctor_get(x_171, 1);
lean_inc(x_174);
x_175 = lean_ctor_get(x_171, 2);
lean_inc(x_175);
if (lean_is_exclusive(x_171)) {
 lean_ctor_release(x_171, 0);
 lean_ctor_release(x_171, 1);
 lean_ctor_release(x_171, 2);
 x_176 = x_171;
} else {
 lean_dec_ref(x_171);
 x_176 = lean_box(0);
}
x_177 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_177, 0, x_136);
lean_ctor_set(x_177, 1, x_137);
lean_ctor_set(x_177, 2, x_138);
lean_ctor_set_uint8(x_177, sizeof(void*)*3, x_142);
x_178 = lean_array_push(x_174, x_177);
if (lean_is_scalar(x_176)) {
 x_179 = lean_alloc_ctor(0, 3, 0);
} else {
 x_179 = x_176;
}
lean_ctor_set(x_179, 0, x_173);
lean_ctor_set(x_179, 1, x_178);
lean_ctor_set(x_179, 2, x_175);
x_180 = lean_st_ref_set(x_3, x_179, x_172);
lean_dec(x_3);
x_181 = lean_ctor_get(x_180, 1);
lean_inc(x_181);
if (lean_is_exclusive(x_180)) {
 lean_ctor_release(x_180, 0);
 lean_ctor_release(x_180, 1);
 x_182 = x_180;
} else {
 lean_dec_ref(x_180);
 x_182 = lean_box(0);
}
x_183 = lean_box(0);
if (lean_is_scalar(x_182)) {
 x_184 = lean_alloc_ctor(0, 2, 0);
} else {
 x_184 = x_182;
}
lean_ctor_set(x_184, 0, x_183);
lean_ctor_set(x_184, 1, x_181);
return x_184;
}
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; 
lean_dec(x_139);
lean_dec(x_134);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_185 = lean_ctor_get(x_143, 1);
lean_inc(x_185);
lean_dec(x_143);
x_186 = lean_st_ref_take(x_3, x_185);
x_187 = lean_ctor_get(x_186, 0);
lean_inc(x_187);
x_188 = lean_ctor_get(x_186, 1);
lean_inc(x_188);
lean_dec(x_186);
x_189 = lean_ctor_get(x_187, 0);
lean_inc(x_189);
x_190 = lean_ctor_get(x_187, 1);
lean_inc(x_190);
x_191 = lean_ctor_get(x_187, 2);
lean_inc(x_191);
if (lean_is_exclusive(x_187)) {
 lean_ctor_release(x_187, 0);
 lean_ctor_release(x_187, 1);
 lean_ctor_release(x_187, 2);
 x_192 = x_187;
} else {
 lean_dec_ref(x_187);
 x_192 = lean_box(0);
}
x_193 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_193, 0, x_136);
lean_ctor_set(x_193, 1, x_137);
lean_ctor_set(x_193, 2, x_138);
lean_ctor_set_uint8(x_193, sizeof(void*)*3, x_142);
x_194 = lean_array_push(x_190, x_193);
if (lean_is_scalar(x_192)) {
 x_195 = lean_alloc_ctor(0, 3, 0);
} else {
 x_195 = x_192;
}
lean_ctor_set(x_195, 0, x_189);
lean_ctor_set(x_195, 1, x_194);
lean_ctor_set(x_195, 2, x_191);
x_196 = lean_st_ref_set(x_3, x_195, x_188);
lean_dec(x_3);
x_197 = lean_ctor_get(x_196, 1);
lean_inc(x_197);
if (lean_is_exclusive(x_196)) {
 lean_ctor_release(x_196, 0);
 lean_ctor_release(x_196, 1);
 x_198 = x_196;
} else {
 lean_dec_ref(x_196);
 x_198 = lean_box(0);
}
x_199 = lean_box(0);
if (lean_is_scalar(x_198)) {
 x_200 = lean_alloc_ctor(0, 2, 0);
} else {
 x_200 = x_198;
}
lean_ctor_set(x_200, 0, x_199);
lean_ctor_set(x_200, 1, x_197);
return x_200;
}
}
else
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; 
lean_dec(x_139);
lean_dec(x_138);
lean_dec(x_137);
lean_dec(x_136);
lean_dec(x_134);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_201 = lean_ctor_get(x_143, 0);
lean_inc(x_201);
x_202 = lean_ctor_get(x_143, 1);
lean_inc(x_202);
if (lean_is_exclusive(x_143)) {
 lean_ctor_release(x_143, 0);
 lean_ctor_release(x_143, 1);
 x_203 = x_143;
} else {
 lean_dec_ref(x_143);
 x_203 = lean_box(0);
}
if (lean_is_scalar(x_203)) {
 x_204 = lean_alloc_ctor(1, 2, 0);
} else {
 x_204 = x_203;
}
lean_ctor_set(x_204, 0, x_201);
lean_ctor_set(x_204, 1, x_202);
return x_204;
}
}
}
}
else
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; uint8_t x_210; lean_object* x_211; 
lean_dec(x_1);
x_205 = lean_ctor_get(x_26, 1);
lean_inc(x_205);
lean_dec(x_26);
x_206 = lean_ctor_get(x_27, 0);
lean_inc(x_206);
lean_dec(x_27);
x_207 = lean_ctor_get(x_206, 2);
lean_inc(x_207);
x_208 = lean_alloc_closure((void*)(l_Lean_Expr_isFVar___boxed), 1, 0);
x_209 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Closure_collectType___lambda__1___boxed), 8, 0);
x_210 = 0;
lean_inc(x_3);
x_211 = l_Lean_ForEachExprWhere_visit___at_Lean_Compiler_LCNF_Closure_collectType___spec__1(x_208, x_209, x_207, x_210, x_2, x_3, x_4, x_5, x_6, x_7, x_205);
if (lean_obj_tag(x_211) == 0)
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; uint8_t x_216; 
x_212 = lean_ctor_get(x_211, 1);
lean_inc(x_212);
lean_dec(x_211);
x_213 = lean_st_ref_take(x_3, x_212);
x_214 = lean_ctor_get(x_213, 0);
lean_inc(x_214);
x_215 = lean_ctor_get(x_213, 1);
lean_inc(x_215);
lean_dec(x_213);
x_216 = !lean_is_exclusive(x_214);
if (x_216 == 0)
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; uint8_t x_220; 
x_217 = lean_ctor_get(x_214, 1);
x_218 = lean_array_push(x_217, x_206);
lean_ctor_set(x_214, 1, x_218);
x_219 = lean_st_ref_set(x_3, x_214, x_215);
lean_dec(x_3);
x_220 = !lean_is_exclusive(x_219);
if (x_220 == 0)
{
lean_object* x_221; lean_object* x_222; 
x_221 = lean_ctor_get(x_219, 0);
lean_dec(x_221);
x_222 = lean_box(0);
lean_ctor_set(x_219, 0, x_222);
return x_219;
}
else
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; 
x_223 = lean_ctor_get(x_219, 1);
lean_inc(x_223);
lean_dec(x_219);
x_224 = lean_box(0);
x_225 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_225, 0, x_224);
lean_ctor_set(x_225, 1, x_223);
return x_225;
}
}
else
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; 
x_226 = lean_ctor_get(x_214, 0);
x_227 = lean_ctor_get(x_214, 1);
x_228 = lean_ctor_get(x_214, 2);
lean_inc(x_228);
lean_inc(x_227);
lean_inc(x_226);
lean_dec(x_214);
x_229 = lean_array_push(x_227, x_206);
x_230 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_230, 0, x_226);
lean_ctor_set(x_230, 1, x_229);
lean_ctor_set(x_230, 2, x_228);
x_231 = lean_st_ref_set(x_3, x_230, x_215);
lean_dec(x_3);
x_232 = lean_ctor_get(x_231, 1);
lean_inc(x_232);
if (lean_is_exclusive(x_231)) {
 lean_ctor_release(x_231, 0);
 lean_ctor_release(x_231, 1);
 x_233 = x_231;
} else {
 lean_dec_ref(x_231);
 x_233 = lean_box(0);
}
x_234 = lean_box(0);
if (lean_is_scalar(x_233)) {
 x_235 = lean_alloc_ctor(0, 2, 0);
} else {
 x_235 = x_233;
}
lean_ctor_set(x_235, 0, x_234);
lean_ctor_set(x_235, 1, x_232);
return x_235;
}
}
else
{
uint8_t x_236; 
lean_dec(x_206);
lean_dec(x_3);
x_236 = !lean_is_exclusive(x_211);
if (x_236 == 0)
{
return x_211;
}
else
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; 
x_237 = lean_ctor_get(x_211, 0);
x_238 = lean_ctor_get(x_211, 1);
lean_inc(x_238);
lean_inc(x_237);
lean_dec(x_211);
x_239 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_239, 0, x_237);
lean_ctor_set(x_239, 1, x_238);
return x_239;
}
}
}
}
else
{
uint8_t x_240; 
lean_dec(x_1);
x_240 = lean_ctor_get_uint8(x_2, sizeof(void*)*2);
if (x_240 == 0)
{
uint8_t x_241; 
x_241 = !lean_is_exclusive(x_24);
if (x_241 == 0)
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; uint8_t x_249; 
x_242 = lean_ctor_get(x_24, 0);
x_243 = lean_ctor_get(x_23, 1);
lean_inc(x_243);
lean_dec(x_23);
x_244 = lean_ctor_get(x_2, 1);
lean_inc(x_244);
x_245 = lean_ctor_get(x_242, 0);
lean_inc(x_245);
x_246 = lean_ctor_get(x_242, 1);
lean_inc(x_246);
x_247 = lean_ctor_get(x_242, 3);
lean_inc(x_247);
lean_inc(x_245);
x_248 = lean_apply_1(x_244, x_245);
x_249 = lean_unbox(x_248);
lean_dec(x_248);
if (x_249 == 0)
{
lean_object* x_250; 
lean_dec(x_247);
lean_dec(x_246);
lean_dec(x_245);
lean_inc(x_3);
lean_inc(x_242);
x_250 = l_Lean_Compiler_LCNF_Closure_collectFunDecl(x_242, x_2, x_3, x_4, x_5, x_6, x_7, x_243);
if (lean_obj_tag(x_250) == 0)
{
lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; uint8_t x_255; 
x_251 = lean_ctor_get(x_250, 1);
lean_inc(x_251);
lean_dec(x_250);
x_252 = lean_st_ref_take(x_3, x_251);
x_253 = lean_ctor_get(x_252, 0);
lean_inc(x_253);
x_254 = lean_ctor_get(x_252, 1);
lean_inc(x_254);
lean_dec(x_252);
x_255 = !lean_is_exclusive(x_253);
if (x_255 == 0)
{
lean_object* x_256; lean_object* x_257; lean_object* x_258; uint8_t x_259; 
x_256 = lean_ctor_get(x_253, 2);
x_257 = lean_array_push(x_256, x_24);
lean_ctor_set(x_253, 2, x_257);
x_258 = lean_st_ref_set(x_3, x_253, x_254);
lean_dec(x_3);
x_259 = !lean_is_exclusive(x_258);
if (x_259 == 0)
{
lean_object* x_260; lean_object* x_261; 
x_260 = lean_ctor_get(x_258, 0);
lean_dec(x_260);
x_261 = lean_box(0);
lean_ctor_set(x_258, 0, x_261);
return x_258;
}
else
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; 
x_262 = lean_ctor_get(x_258, 1);
lean_inc(x_262);
lean_dec(x_258);
x_263 = lean_box(0);
x_264 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_264, 0, x_263);
lean_ctor_set(x_264, 1, x_262);
return x_264;
}
}
else
{
lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; 
x_265 = lean_ctor_get(x_253, 0);
x_266 = lean_ctor_get(x_253, 1);
x_267 = lean_ctor_get(x_253, 2);
lean_inc(x_267);
lean_inc(x_266);
lean_inc(x_265);
lean_dec(x_253);
x_268 = lean_array_push(x_267, x_24);
x_269 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_269, 0, x_265);
lean_ctor_set(x_269, 1, x_266);
lean_ctor_set(x_269, 2, x_268);
x_270 = lean_st_ref_set(x_3, x_269, x_254);
lean_dec(x_3);
x_271 = lean_ctor_get(x_270, 1);
lean_inc(x_271);
if (lean_is_exclusive(x_270)) {
 lean_ctor_release(x_270, 0);
 lean_ctor_release(x_270, 1);
 x_272 = x_270;
} else {
 lean_dec_ref(x_270);
 x_272 = lean_box(0);
}
x_273 = lean_box(0);
if (lean_is_scalar(x_272)) {
 x_274 = lean_alloc_ctor(0, 2, 0);
} else {
 x_274 = x_272;
}
lean_ctor_set(x_274, 0, x_273);
lean_ctor_set(x_274, 1, x_271);
return x_274;
}
}
else
{
uint8_t x_275; 
lean_free_object(x_24);
lean_dec(x_242);
lean_dec(x_3);
x_275 = !lean_is_exclusive(x_250);
if (x_275 == 0)
{
return x_250;
}
else
{
lean_object* x_276; lean_object* x_277; lean_object* x_278; 
x_276 = lean_ctor_get(x_250, 0);
x_277 = lean_ctor_get(x_250, 1);
lean_inc(x_277);
lean_inc(x_276);
lean_dec(x_250);
x_278 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_278, 0, x_276);
lean_ctor_set(x_278, 1, x_277);
return x_278;
}
}
}
else
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; uint8_t x_282; 
lean_free_object(x_24);
lean_dec(x_242);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_279 = lean_st_ref_take(x_3, x_243);
x_280 = lean_ctor_get(x_279, 0);
lean_inc(x_280);
x_281 = lean_ctor_get(x_279, 1);
lean_inc(x_281);
lean_dec(x_279);
x_282 = !lean_is_exclusive(x_280);
if (x_282 == 0)
{
lean_object* x_283; uint8_t x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; uint8_t x_288; 
x_283 = lean_ctor_get(x_280, 1);
x_284 = 0;
x_285 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_285, 0, x_245);
lean_ctor_set(x_285, 1, x_246);
lean_ctor_set(x_285, 2, x_247);
lean_ctor_set_uint8(x_285, sizeof(void*)*3, x_284);
x_286 = lean_array_push(x_283, x_285);
lean_ctor_set(x_280, 1, x_286);
x_287 = lean_st_ref_set(x_3, x_280, x_281);
lean_dec(x_3);
x_288 = !lean_is_exclusive(x_287);
if (x_288 == 0)
{
lean_object* x_289; lean_object* x_290; 
x_289 = lean_ctor_get(x_287, 0);
lean_dec(x_289);
x_290 = lean_box(0);
lean_ctor_set(x_287, 0, x_290);
return x_287;
}
else
{
lean_object* x_291; lean_object* x_292; lean_object* x_293; 
x_291 = lean_ctor_get(x_287, 1);
lean_inc(x_291);
lean_dec(x_287);
x_292 = lean_box(0);
x_293 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_293, 0, x_292);
lean_ctor_set(x_293, 1, x_291);
return x_293;
}
}
else
{
lean_object* x_294; lean_object* x_295; lean_object* x_296; uint8_t x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; 
x_294 = lean_ctor_get(x_280, 0);
x_295 = lean_ctor_get(x_280, 1);
x_296 = lean_ctor_get(x_280, 2);
lean_inc(x_296);
lean_inc(x_295);
lean_inc(x_294);
lean_dec(x_280);
x_297 = 0;
x_298 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_298, 0, x_245);
lean_ctor_set(x_298, 1, x_246);
lean_ctor_set(x_298, 2, x_247);
lean_ctor_set_uint8(x_298, sizeof(void*)*3, x_297);
x_299 = lean_array_push(x_295, x_298);
x_300 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_300, 0, x_294);
lean_ctor_set(x_300, 1, x_299);
lean_ctor_set(x_300, 2, x_296);
x_301 = lean_st_ref_set(x_3, x_300, x_281);
lean_dec(x_3);
x_302 = lean_ctor_get(x_301, 1);
lean_inc(x_302);
if (lean_is_exclusive(x_301)) {
 lean_ctor_release(x_301, 0);
 lean_ctor_release(x_301, 1);
 x_303 = x_301;
} else {
 lean_dec_ref(x_301);
 x_303 = lean_box(0);
}
x_304 = lean_box(0);
if (lean_is_scalar(x_303)) {
 x_305 = lean_alloc_ctor(0, 2, 0);
} else {
 x_305 = x_303;
}
lean_ctor_set(x_305, 0, x_304);
lean_ctor_set(x_305, 1, x_302);
return x_305;
}
}
}
else
{
lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; uint8_t x_313; 
x_306 = lean_ctor_get(x_24, 0);
lean_inc(x_306);
lean_dec(x_24);
x_307 = lean_ctor_get(x_23, 1);
lean_inc(x_307);
lean_dec(x_23);
x_308 = lean_ctor_get(x_2, 1);
lean_inc(x_308);
x_309 = lean_ctor_get(x_306, 0);
lean_inc(x_309);
x_310 = lean_ctor_get(x_306, 1);
lean_inc(x_310);
x_311 = lean_ctor_get(x_306, 3);
lean_inc(x_311);
lean_inc(x_309);
x_312 = lean_apply_1(x_308, x_309);
x_313 = lean_unbox(x_312);
lean_dec(x_312);
if (x_313 == 0)
{
lean_object* x_314; 
lean_dec(x_311);
lean_dec(x_310);
lean_dec(x_309);
lean_inc(x_3);
lean_inc(x_306);
x_314 = l_Lean_Compiler_LCNF_Closure_collectFunDecl(x_306, x_2, x_3, x_4, x_5, x_6, x_7, x_307);
if (lean_obj_tag(x_314) == 0)
{
lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; 
x_315 = lean_ctor_get(x_314, 1);
lean_inc(x_315);
lean_dec(x_314);
x_316 = lean_st_ref_take(x_3, x_315);
x_317 = lean_ctor_get(x_316, 0);
lean_inc(x_317);
x_318 = lean_ctor_get(x_316, 1);
lean_inc(x_318);
lean_dec(x_316);
x_319 = lean_ctor_get(x_317, 0);
lean_inc(x_319);
x_320 = lean_ctor_get(x_317, 1);
lean_inc(x_320);
x_321 = lean_ctor_get(x_317, 2);
lean_inc(x_321);
if (lean_is_exclusive(x_317)) {
 lean_ctor_release(x_317, 0);
 lean_ctor_release(x_317, 1);
 lean_ctor_release(x_317, 2);
 x_322 = x_317;
} else {
 lean_dec_ref(x_317);
 x_322 = lean_box(0);
}
x_323 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_323, 0, x_306);
x_324 = lean_array_push(x_321, x_323);
if (lean_is_scalar(x_322)) {
 x_325 = lean_alloc_ctor(0, 3, 0);
} else {
 x_325 = x_322;
}
lean_ctor_set(x_325, 0, x_319);
lean_ctor_set(x_325, 1, x_320);
lean_ctor_set(x_325, 2, x_324);
x_326 = lean_st_ref_set(x_3, x_325, x_318);
lean_dec(x_3);
x_327 = lean_ctor_get(x_326, 1);
lean_inc(x_327);
if (lean_is_exclusive(x_326)) {
 lean_ctor_release(x_326, 0);
 lean_ctor_release(x_326, 1);
 x_328 = x_326;
} else {
 lean_dec_ref(x_326);
 x_328 = lean_box(0);
}
x_329 = lean_box(0);
if (lean_is_scalar(x_328)) {
 x_330 = lean_alloc_ctor(0, 2, 0);
} else {
 x_330 = x_328;
}
lean_ctor_set(x_330, 0, x_329);
lean_ctor_set(x_330, 1, x_327);
return x_330;
}
else
{
lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; 
lean_dec(x_306);
lean_dec(x_3);
x_331 = lean_ctor_get(x_314, 0);
lean_inc(x_331);
x_332 = lean_ctor_get(x_314, 1);
lean_inc(x_332);
if (lean_is_exclusive(x_314)) {
 lean_ctor_release(x_314, 0);
 lean_ctor_release(x_314, 1);
 x_333 = x_314;
} else {
 lean_dec_ref(x_314);
 x_333 = lean_box(0);
}
if (lean_is_scalar(x_333)) {
 x_334 = lean_alloc_ctor(1, 2, 0);
} else {
 x_334 = x_333;
}
lean_ctor_set(x_334, 0, x_331);
lean_ctor_set(x_334, 1, x_332);
return x_334;
}
}
else
{
lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; uint8_t x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; 
lean_dec(x_306);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_335 = lean_st_ref_take(x_3, x_307);
x_336 = lean_ctor_get(x_335, 0);
lean_inc(x_336);
x_337 = lean_ctor_get(x_335, 1);
lean_inc(x_337);
lean_dec(x_335);
x_338 = lean_ctor_get(x_336, 0);
lean_inc(x_338);
x_339 = lean_ctor_get(x_336, 1);
lean_inc(x_339);
x_340 = lean_ctor_get(x_336, 2);
lean_inc(x_340);
if (lean_is_exclusive(x_336)) {
 lean_ctor_release(x_336, 0);
 lean_ctor_release(x_336, 1);
 lean_ctor_release(x_336, 2);
 x_341 = x_336;
} else {
 lean_dec_ref(x_336);
 x_341 = lean_box(0);
}
x_342 = 0;
x_343 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_343, 0, x_309);
lean_ctor_set(x_343, 1, x_310);
lean_ctor_set(x_343, 2, x_311);
lean_ctor_set_uint8(x_343, sizeof(void*)*3, x_342);
x_344 = lean_array_push(x_339, x_343);
if (lean_is_scalar(x_341)) {
 x_345 = lean_alloc_ctor(0, 3, 0);
} else {
 x_345 = x_341;
}
lean_ctor_set(x_345, 0, x_338);
lean_ctor_set(x_345, 1, x_344);
lean_ctor_set(x_345, 2, x_340);
x_346 = lean_st_ref_set(x_3, x_345, x_337);
lean_dec(x_3);
x_347 = lean_ctor_get(x_346, 1);
lean_inc(x_347);
if (lean_is_exclusive(x_346)) {
 lean_ctor_release(x_346, 0);
 lean_ctor_release(x_346, 1);
 x_348 = x_346;
} else {
 lean_dec_ref(x_346);
 x_348 = lean_box(0);
}
x_349 = lean_box(0);
if (lean_is_scalar(x_348)) {
 x_350 = lean_alloc_ctor(0, 2, 0);
} else {
 x_350 = x_348;
}
lean_ctor_set(x_350, 0, x_349);
lean_ctor_set(x_350, 1, x_347);
return x_350;
}
}
}
else
{
lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; uint8_t x_356; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_351 = lean_ctor_get(x_23, 1);
lean_inc(x_351);
lean_dec(x_23);
x_352 = lean_ctor_get(x_24, 0);
lean_inc(x_352);
lean_dec(x_24);
x_353 = lean_st_ref_take(x_3, x_351);
x_354 = lean_ctor_get(x_353, 0);
lean_inc(x_354);
x_355 = lean_ctor_get(x_353, 1);
lean_inc(x_355);
lean_dec(x_353);
x_356 = !lean_is_exclusive(x_354);
if (x_356 == 0)
{
lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; uint8_t x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; uint8_t x_365; 
x_357 = lean_ctor_get(x_354, 1);
x_358 = lean_ctor_get(x_352, 0);
lean_inc(x_358);
x_359 = lean_ctor_get(x_352, 1);
lean_inc(x_359);
x_360 = lean_ctor_get(x_352, 3);
lean_inc(x_360);
lean_dec(x_352);
x_361 = 0;
x_362 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_362, 0, x_358);
lean_ctor_set(x_362, 1, x_359);
lean_ctor_set(x_362, 2, x_360);
lean_ctor_set_uint8(x_362, sizeof(void*)*3, x_361);
x_363 = lean_array_push(x_357, x_362);
lean_ctor_set(x_354, 1, x_363);
x_364 = lean_st_ref_set(x_3, x_354, x_355);
lean_dec(x_3);
x_365 = !lean_is_exclusive(x_364);
if (x_365 == 0)
{
lean_object* x_366; lean_object* x_367; 
x_366 = lean_ctor_get(x_364, 0);
lean_dec(x_366);
x_367 = lean_box(0);
lean_ctor_set(x_364, 0, x_367);
return x_364;
}
else
{
lean_object* x_368; lean_object* x_369; lean_object* x_370; 
x_368 = lean_ctor_get(x_364, 1);
lean_inc(x_368);
lean_dec(x_364);
x_369 = lean_box(0);
x_370 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_370, 0, x_369);
lean_ctor_set(x_370, 1, x_368);
return x_370;
}
}
else
{
lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; uint8_t x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; 
x_371 = lean_ctor_get(x_354, 0);
x_372 = lean_ctor_get(x_354, 1);
x_373 = lean_ctor_get(x_354, 2);
lean_inc(x_373);
lean_inc(x_372);
lean_inc(x_371);
lean_dec(x_354);
x_374 = lean_ctor_get(x_352, 0);
lean_inc(x_374);
x_375 = lean_ctor_get(x_352, 1);
lean_inc(x_375);
x_376 = lean_ctor_get(x_352, 3);
lean_inc(x_376);
lean_dec(x_352);
x_377 = 0;
x_378 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_378, 0, x_374);
lean_ctor_set(x_378, 1, x_375);
lean_ctor_set(x_378, 2, x_376);
lean_ctor_set_uint8(x_378, sizeof(void*)*3, x_377);
x_379 = lean_array_push(x_372, x_378);
x_380 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_380, 0, x_371);
lean_ctor_set(x_380, 1, x_379);
lean_ctor_set(x_380, 2, x_373);
x_381 = lean_st_ref_set(x_3, x_380, x_355);
lean_dec(x_3);
x_382 = lean_ctor_get(x_381, 1);
lean_inc(x_382);
if (lean_is_exclusive(x_381)) {
 lean_ctor_release(x_381, 0);
 lean_ctor_release(x_381, 1);
 x_383 = x_381;
} else {
 lean_dec_ref(x_381);
 x_383 = lean_box(0);
}
x_384 = lean_box(0);
if (lean_is_scalar(x_383)) {
 x_385 = lean_alloc_ctor(0, 2, 0);
} else {
 x_385 = x_383;
}
lean_ctor_set(x_385, 0, x_384);
lean_ctor_set(x_385, 1, x_382);
return x_385;
}
}
}
}
}
else
{
lean_object* x_386; lean_object* x_387; lean_object* x_388; uint8_t x_389; 
x_386 = lean_ctor_get(x_15, 1);
lean_inc(x_386);
lean_dec(x_15);
x_387 = lean_ctor_get(x_2, 0);
lean_inc(x_387);
lean_inc(x_1);
x_388 = lean_apply_1(x_387, x_1);
x_389 = lean_unbox(x_388);
lean_dec(x_388);
if (x_389 == 0)
{
lean_object* x_390; lean_object* x_391; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_390 = lean_box(0);
x_391 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_391, 0, x_390);
lean_ctor_set(x_391, 1, x_386);
return x_391;
}
else
{
lean_object* x_392; lean_object* x_393; 
x_392 = l_Lean_Compiler_LCNF_findFunDecl_x3f(x_1, x_4, x_5, x_6, x_7, x_386);
x_393 = lean_ctor_get(x_392, 0);
lean_inc(x_393);
if (lean_obj_tag(x_393) == 0)
{
lean_object* x_394; lean_object* x_395; lean_object* x_396; 
x_394 = lean_ctor_get(x_392, 1);
lean_inc(x_394);
lean_dec(x_392);
x_395 = l_Lean_Compiler_LCNF_findParam_x3f(x_1, x_4, x_5, x_6, x_7, x_394);
x_396 = lean_ctor_get(x_395, 0);
lean_inc(x_396);
if (lean_obj_tag(x_396) == 0)
{
lean_object* x_397; lean_object* x_398; lean_object* x_399; 
x_397 = lean_ctor_get(x_395, 1);
lean_inc(x_397);
lean_dec(x_395);
x_398 = l_Lean_Compiler_LCNF_findLetDecl_x3f(x_1, x_4, x_5, x_6, x_7, x_397);
lean_dec(x_1);
x_399 = lean_ctor_get(x_398, 0);
lean_inc(x_399);
if (lean_obj_tag(x_399) == 0)
{
lean_object* x_400; lean_object* x_401; lean_object* x_402; 
x_400 = lean_ctor_get(x_398, 1);
lean_inc(x_400);
lean_dec(x_398);
x_401 = l_Lean_Compiler_LCNF_Closure_collectFVar___closed__4;
x_402 = l_panic___at_Lean_Compiler_LCNF_Closure_collectFVar___spec__1(x_401, x_2, x_3, x_4, x_5, x_6, x_7, x_400);
return x_402;
}
else
{
lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; uint8_t x_412; lean_object* x_413; 
x_403 = lean_ctor_get(x_399, 0);
lean_inc(x_403);
if (lean_is_exclusive(x_399)) {
 lean_ctor_release(x_399, 0);
 x_404 = x_399;
} else {
 lean_dec_ref(x_399);
 x_404 = lean_box(0);
}
x_405 = lean_ctor_get(x_398, 1);
lean_inc(x_405);
lean_dec(x_398);
x_406 = lean_ctor_get(x_403, 0);
lean_inc(x_406);
x_407 = lean_ctor_get(x_403, 1);
lean_inc(x_407);
x_408 = lean_ctor_get(x_403, 2);
lean_inc(x_408);
x_409 = lean_ctor_get(x_403, 3);
lean_inc(x_409);
x_410 = lean_alloc_closure((void*)(l_Lean_Expr_isFVar___boxed), 1, 0);
x_411 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Closure_collectType___lambda__1___boxed), 8, 0);
x_412 = 0;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_408);
x_413 = l_Lean_ForEachExprWhere_visit___at_Lean_Compiler_LCNF_Closure_collectType___spec__1(x_410, x_411, x_408, x_412, x_2, x_3, x_4, x_5, x_6, x_7, x_405);
if (lean_obj_tag(x_413) == 0)
{
uint8_t x_414; 
x_414 = lean_ctor_get_uint8(x_2, sizeof(void*)*2);
if (x_414 == 0)
{
lean_object* x_415; lean_object* x_416; lean_object* x_417; uint8_t x_418; 
x_415 = lean_ctor_get(x_413, 1);
lean_inc(x_415);
lean_dec(x_413);
x_416 = lean_ctor_get(x_2, 1);
lean_inc(x_416);
lean_inc(x_406);
x_417 = lean_apply_1(x_416, x_406);
x_418 = lean_unbox(x_417);
lean_dec(x_417);
if (x_418 == 0)
{
lean_object* x_419; 
lean_dec(x_408);
lean_dec(x_407);
lean_dec(x_406);
lean_inc(x_3);
x_419 = l_Lean_Compiler_LCNF_Closure_collectLetValue(x_409, x_2, x_3, x_4, x_5, x_6, x_7, x_415);
if (lean_obj_tag(x_419) == 0)
{
lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; 
x_420 = lean_ctor_get(x_419, 1);
lean_inc(x_420);
lean_dec(x_419);
x_421 = lean_st_ref_take(x_3, x_420);
x_422 = lean_ctor_get(x_421, 0);
lean_inc(x_422);
x_423 = lean_ctor_get(x_421, 1);
lean_inc(x_423);
lean_dec(x_421);
x_424 = lean_ctor_get(x_422, 0);
lean_inc(x_424);
x_425 = lean_ctor_get(x_422, 1);
lean_inc(x_425);
x_426 = lean_ctor_get(x_422, 2);
lean_inc(x_426);
if (lean_is_exclusive(x_422)) {
 lean_ctor_release(x_422, 0);
 lean_ctor_release(x_422, 1);
 lean_ctor_release(x_422, 2);
 x_427 = x_422;
} else {
 lean_dec_ref(x_422);
 x_427 = lean_box(0);
}
if (lean_is_scalar(x_404)) {
 x_428 = lean_alloc_ctor(0, 1, 0);
} else {
 x_428 = x_404;
 lean_ctor_set_tag(x_428, 0);
}
lean_ctor_set(x_428, 0, x_403);
x_429 = lean_array_push(x_426, x_428);
if (lean_is_scalar(x_427)) {
 x_430 = lean_alloc_ctor(0, 3, 0);
} else {
 x_430 = x_427;
}
lean_ctor_set(x_430, 0, x_424);
lean_ctor_set(x_430, 1, x_425);
lean_ctor_set(x_430, 2, x_429);
x_431 = lean_st_ref_set(x_3, x_430, x_423);
lean_dec(x_3);
x_432 = lean_ctor_get(x_431, 1);
lean_inc(x_432);
if (lean_is_exclusive(x_431)) {
 lean_ctor_release(x_431, 0);
 lean_ctor_release(x_431, 1);
 x_433 = x_431;
} else {
 lean_dec_ref(x_431);
 x_433 = lean_box(0);
}
x_434 = lean_box(0);
if (lean_is_scalar(x_433)) {
 x_435 = lean_alloc_ctor(0, 2, 0);
} else {
 x_435 = x_433;
}
lean_ctor_set(x_435, 0, x_434);
lean_ctor_set(x_435, 1, x_432);
return x_435;
}
else
{
lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; 
lean_dec(x_404);
lean_dec(x_403);
lean_dec(x_3);
x_436 = lean_ctor_get(x_419, 0);
lean_inc(x_436);
x_437 = lean_ctor_get(x_419, 1);
lean_inc(x_437);
if (lean_is_exclusive(x_419)) {
 lean_ctor_release(x_419, 0);
 lean_ctor_release(x_419, 1);
 x_438 = x_419;
} else {
 lean_dec_ref(x_419);
 x_438 = lean_box(0);
}
if (lean_is_scalar(x_438)) {
 x_439 = lean_alloc_ctor(1, 2, 0);
} else {
 x_439 = x_438;
}
lean_ctor_set(x_439, 0, x_436);
lean_ctor_set(x_439, 1, x_437);
return x_439;
}
}
else
{
lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; 
lean_dec(x_409);
lean_dec(x_404);
lean_dec(x_403);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_440 = lean_st_ref_take(x_3, x_415);
x_441 = lean_ctor_get(x_440, 0);
lean_inc(x_441);
x_442 = lean_ctor_get(x_440, 1);
lean_inc(x_442);
lean_dec(x_440);
x_443 = lean_ctor_get(x_441, 0);
lean_inc(x_443);
x_444 = lean_ctor_get(x_441, 1);
lean_inc(x_444);
x_445 = lean_ctor_get(x_441, 2);
lean_inc(x_445);
if (lean_is_exclusive(x_441)) {
 lean_ctor_release(x_441, 0);
 lean_ctor_release(x_441, 1);
 lean_ctor_release(x_441, 2);
 x_446 = x_441;
} else {
 lean_dec_ref(x_441);
 x_446 = lean_box(0);
}
x_447 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_447, 0, x_406);
lean_ctor_set(x_447, 1, x_407);
lean_ctor_set(x_447, 2, x_408);
lean_ctor_set_uint8(x_447, sizeof(void*)*3, x_412);
x_448 = lean_array_push(x_444, x_447);
if (lean_is_scalar(x_446)) {
 x_449 = lean_alloc_ctor(0, 3, 0);
} else {
 x_449 = x_446;
}
lean_ctor_set(x_449, 0, x_443);
lean_ctor_set(x_449, 1, x_448);
lean_ctor_set(x_449, 2, x_445);
x_450 = lean_st_ref_set(x_3, x_449, x_442);
lean_dec(x_3);
x_451 = lean_ctor_get(x_450, 1);
lean_inc(x_451);
if (lean_is_exclusive(x_450)) {
 lean_ctor_release(x_450, 0);
 lean_ctor_release(x_450, 1);
 x_452 = x_450;
} else {
 lean_dec_ref(x_450);
 x_452 = lean_box(0);
}
x_453 = lean_box(0);
if (lean_is_scalar(x_452)) {
 x_454 = lean_alloc_ctor(0, 2, 0);
} else {
 x_454 = x_452;
}
lean_ctor_set(x_454, 0, x_453);
lean_ctor_set(x_454, 1, x_451);
return x_454;
}
}
else
{
lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; 
lean_dec(x_409);
lean_dec(x_404);
lean_dec(x_403);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_455 = lean_ctor_get(x_413, 1);
lean_inc(x_455);
lean_dec(x_413);
x_456 = lean_st_ref_take(x_3, x_455);
x_457 = lean_ctor_get(x_456, 0);
lean_inc(x_457);
x_458 = lean_ctor_get(x_456, 1);
lean_inc(x_458);
lean_dec(x_456);
x_459 = lean_ctor_get(x_457, 0);
lean_inc(x_459);
x_460 = lean_ctor_get(x_457, 1);
lean_inc(x_460);
x_461 = lean_ctor_get(x_457, 2);
lean_inc(x_461);
if (lean_is_exclusive(x_457)) {
 lean_ctor_release(x_457, 0);
 lean_ctor_release(x_457, 1);
 lean_ctor_release(x_457, 2);
 x_462 = x_457;
} else {
 lean_dec_ref(x_457);
 x_462 = lean_box(0);
}
x_463 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_463, 0, x_406);
lean_ctor_set(x_463, 1, x_407);
lean_ctor_set(x_463, 2, x_408);
lean_ctor_set_uint8(x_463, sizeof(void*)*3, x_412);
x_464 = lean_array_push(x_460, x_463);
if (lean_is_scalar(x_462)) {
 x_465 = lean_alloc_ctor(0, 3, 0);
} else {
 x_465 = x_462;
}
lean_ctor_set(x_465, 0, x_459);
lean_ctor_set(x_465, 1, x_464);
lean_ctor_set(x_465, 2, x_461);
x_466 = lean_st_ref_set(x_3, x_465, x_458);
lean_dec(x_3);
x_467 = lean_ctor_get(x_466, 1);
lean_inc(x_467);
if (lean_is_exclusive(x_466)) {
 lean_ctor_release(x_466, 0);
 lean_ctor_release(x_466, 1);
 x_468 = x_466;
} else {
 lean_dec_ref(x_466);
 x_468 = lean_box(0);
}
x_469 = lean_box(0);
if (lean_is_scalar(x_468)) {
 x_470 = lean_alloc_ctor(0, 2, 0);
} else {
 x_470 = x_468;
}
lean_ctor_set(x_470, 0, x_469);
lean_ctor_set(x_470, 1, x_467);
return x_470;
}
}
else
{
lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; 
lean_dec(x_409);
lean_dec(x_408);
lean_dec(x_407);
lean_dec(x_406);
lean_dec(x_404);
lean_dec(x_403);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_471 = lean_ctor_get(x_413, 0);
lean_inc(x_471);
x_472 = lean_ctor_get(x_413, 1);
lean_inc(x_472);
if (lean_is_exclusive(x_413)) {
 lean_ctor_release(x_413, 0);
 lean_ctor_release(x_413, 1);
 x_473 = x_413;
} else {
 lean_dec_ref(x_413);
 x_473 = lean_box(0);
}
if (lean_is_scalar(x_473)) {
 x_474 = lean_alloc_ctor(1, 2, 0);
} else {
 x_474 = x_473;
}
lean_ctor_set(x_474, 0, x_471);
lean_ctor_set(x_474, 1, x_472);
return x_474;
}
}
}
else
{
lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; uint8_t x_480; lean_object* x_481; 
lean_dec(x_1);
x_475 = lean_ctor_get(x_395, 1);
lean_inc(x_475);
lean_dec(x_395);
x_476 = lean_ctor_get(x_396, 0);
lean_inc(x_476);
lean_dec(x_396);
x_477 = lean_ctor_get(x_476, 2);
lean_inc(x_477);
x_478 = lean_alloc_closure((void*)(l_Lean_Expr_isFVar___boxed), 1, 0);
x_479 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Closure_collectType___lambda__1___boxed), 8, 0);
x_480 = 0;
lean_inc(x_3);
x_481 = l_Lean_ForEachExprWhere_visit___at_Lean_Compiler_LCNF_Closure_collectType___spec__1(x_478, x_479, x_477, x_480, x_2, x_3, x_4, x_5, x_6, x_7, x_475);
if (lean_obj_tag(x_481) == 0)
{
lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; 
x_482 = lean_ctor_get(x_481, 1);
lean_inc(x_482);
lean_dec(x_481);
x_483 = lean_st_ref_take(x_3, x_482);
x_484 = lean_ctor_get(x_483, 0);
lean_inc(x_484);
x_485 = lean_ctor_get(x_483, 1);
lean_inc(x_485);
lean_dec(x_483);
x_486 = lean_ctor_get(x_484, 0);
lean_inc(x_486);
x_487 = lean_ctor_get(x_484, 1);
lean_inc(x_487);
x_488 = lean_ctor_get(x_484, 2);
lean_inc(x_488);
if (lean_is_exclusive(x_484)) {
 lean_ctor_release(x_484, 0);
 lean_ctor_release(x_484, 1);
 lean_ctor_release(x_484, 2);
 x_489 = x_484;
} else {
 lean_dec_ref(x_484);
 x_489 = lean_box(0);
}
x_490 = lean_array_push(x_487, x_476);
if (lean_is_scalar(x_489)) {
 x_491 = lean_alloc_ctor(0, 3, 0);
} else {
 x_491 = x_489;
}
lean_ctor_set(x_491, 0, x_486);
lean_ctor_set(x_491, 1, x_490);
lean_ctor_set(x_491, 2, x_488);
x_492 = lean_st_ref_set(x_3, x_491, x_485);
lean_dec(x_3);
x_493 = lean_ctor_get(x_492, 1);
lean_inc(x_493);
if (lean_is_exclusive(x_492)) {
 lean_ctor_release(x_492, 0);
 lean_ctor_release(x_492, 1);
 x_494 = x_492;
} else {
 lean_dec_ref(x_492);
 x_494 = lean_box(0);
}
x_495 = lean_box(0);
if (lean_is_scalar(x_494)) {
 x_496 = lean_alloc_ctor(0, 2, 0);
} else {
 x_496 = x_494;
}
lean_ctor_set(x_496, 0, x_495);
lean_ctor_set(x_496, 1, x_493);
return x_496;
}
else
{
lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; 
lean_dec(x_476);
lean_dec(x_3);
x_497 = lean_ctor_get(x_481, 0);
lean_inc(x_497);
x_498 = lean_ctor_get(x_481, 1);
lean_inc(x_498);
if (lean_is_exclusive(x_481)) {
 lean_ctor_release(x_481, 0);
 lean_ctor_release(x_481, 1);
 x_499 = x_481;
} else {
 lean_dec_ref(x_481);
 x_499 = lean_box(0);
}
if (lean_is_scalar(x_499)) {
 x_500 = lean_alloc_ctor(1, 2, 0);
} else {
 x_500 = x_499;
}
lean_ctor_set(x_500, 0, x_497);
lean_ctor_set(x_500, 1, x_498);
return x_500;
}
}
}
else
{
uint8_t x_501; 
lean_dec(x_1);
x_501 = lean_ctor_get_uint8(x_2, sizeof(void*)*2);
if (x_501 == 0)
{
lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; uint8_t x_510; 
x_502 = lean_ctor_get(x_393, 0);
lean_inc(x_502);
if (lean_is_exclusive(x_393)) {
 lean_ctor_release(x_393, 0);
 x_503 = x_393;
} else {
 lean_dec_ref(x_393);
 x_503 = lean_box(0);
}
x_504 = lean_ctor_get(x_392, 1);
lean_inc(x_504);
lean_dec(x_392);
x_505 = lean_ctor_get(x_2, 1);
lean_inc(x_505);
x_506 = lean_ctor_get(x_502, 0);
lean_inc(x_506);
x_507 = lean_ctor_get(x_502, 1);
lean_inc(x_507);
x_508 = lean_ctor_get(x_502, 3);
lean_inc(x_508);
lean_inc(x_506);
x_509 = lean_apply_1(x_505, x_506);
x_510 = lean_unbox(x_509);
lean_dec(x_509);
if (x_510 == 0)
{
lean_object* x_511; 
lean_dec(x_508);
lean_dec(x_507);
lean_dec(x_506);
lean_inc(x_3);
lean_inc(x_502);
x_511 = l_Lean_Compiler_LCNF_Closure_collectFunDecl(x_502, x_2, x_3, x_4, x_5, x_6, x_7, x_504);
if (lean_obj_tag(x_511) == 0)
{
lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; 
x_512 = lean_ctor_get(x_511, 1);
lean_inc(x_512);
lean_dec(x_511);
x_513 = lean_st_ref_take(x_3, x_512);
x_514 = lean_ctor_get(x_513, 0);
lean_inc(x_514);
x_515 = lean_ctor_get(x_513, 1);
lean_inc(x_515);
lean_dec(x_513);
x_516 = lean_ctor_get(x_514, 0);
lean_inc(x_516);
x_517 = lean_ctor_get(x_514, 1);
lean_inc(x_517);
x_518 = lean_ctor_get(x_514, 2);
lean_inc(x_518);
if (lean_is_exclusive(x_514)) {
 lean_ctor_release(x_514, 0);
 lean_ctor_release(x_514, 1);
 lean_ctor_release(x_514, 2);
 x_519 = x_514;
} else {
 lean_dec_ref(x_514);
 x_519 = lean_box(0);
}
if (lean_is_scalar(x_503)) {
 x_520 = lean_alloc_ctor(1, 1, 0);
} else {
 x_520 = x_503;
}
lean_ctor_set(x_520, 0, x_502);
x_521 = lean_array_push(x_518, x_520);
if (lean_is_scalar(x_519)) {
 x_522 = lean_alloc_ctor(0, 3, 0);
} else {
 x_522 = x_519;
}
lean_ctor_set(x_522, 0, x_516);
lean_ctor_set(x_522, 1, x_517);
lean_ctor_set(x_522, 2, x_521);
x_523 = lean_st_ref_set(x_3, x_522, x_515);
lean_dec(x_3);
x_524 = lean_ctor_get(x_523, 1);
lean_inc(x_524);
if (lean_is_exclusive(x_523)) {
 lean_ctor_release(x_523, 0);
 lean_ctor_release(x_523, 1);
 x_525 = x_523;
} else {
 lean_dec_ref(x_523);
 x_525 = lean_box(0);
}
x_526 = lean_box(0);
if (lean_is_scalar(x_525)) {
 x_527 = lean_alloc_ctor(0, 2, 0);
} else {
 x_527 = x_525;
}
lean_ctor_set(x_527, 0, x_526);
lean_ctor_set(x_527, 1, x_524);
return x_527;
}
else
{
lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; 
lean_dec(x_503);
lean_dec(x_502);
lean_dec(x_3);
x_528 = lean_ctor_get(x_511, 0);
lean_inc(x_528);
x_529 = lean_ctor_get(x_511, 1);
lean_inc(x_529);
if (lean_is_exclusive(x_511)) {
 lean_ctor_release(x_511, 0);
 lean_ctor_release(x_511, 1);
 x_530 = x_511;
} else {
 lean_dec_ref(x_511);
 x_530 = lean_box(0);
}
if (lean_is_scalar(x_530)) {
 x_531 = lean_alloc_ctor(1, 2, 0);
} else {
 x_531 = x_530;
}
lean_ctor_set(x_531, 0, x_528);
lean_ctor_set(x_531, 1, x_529);
return x_531;
}
}
else
{
lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; uint8_t x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; 
lean_dec(x_503);
lean_dec(x_502);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_532 = lean_st_ref_take(x_3, x_504);
x_533 = lean_ctor_get(x_532, 0);
lean_inc(x_533);
x_534 = lean_ctor_get(x_532, 1);
lean_inc(x_534);
lean_dec(x_532);
x_535 = lean_ctor_get(x_533, 0);
lean_inc(x_535);
x_536 = lean_ctor_get(x_533, 1);
lean_inc(x_536);
x_537 = lean_ctor_get(x_533, 2);
lean_inc(x_537);
if (lean_is_exclusive(x_533)) {
 lean_ctor_release(x_533, 0);
 lean_ctor_release(x_533, 1);
 lean_ctor_release(x_533, 2);
 x_538 = x_533;
} else {
 lean_dec_ref(x_533);
 x_538 = lean_box(0);
}
x_539 = 0;
x_540 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_540, 0, x_506);
lean_ctor_set(x_540, 1, x_507);
lean_ctor_set(x_540, 2, x_508);
lean_ctor_set_uint8(x_540, sizeof(void*)*3, x_539);
x_541 = lean_array_push(x_536, x_540);
if (lean_is_scalar(x_538)) {
 x_542 = lean_alloc_ctor(0, 3, 0);
} else {
 x_542 = x_538;
}
lean_ctor_set(x_542, 0, x_535);
lean_ctor_set(x_542, 1, x_541);
lean_ctor_set(x_542, 2, x_537);
x_543 = lean_st_ref_set(x_3, x_542, x_534);
lean_dec(x_3);
x_544 = lean_ctor_get(x_543, 1);
lean_inc(x_544);
if (lean_is_exclusive(x_543)) {
 lean_ctor_release(x_543, 0);
 lean_ctor_release(x_543, 1);
 x_545 = x_543;
} else {
 lean_dec_ref(x_543);
 x_545 = lean_box(0);
}
x_546 = lean_box(0);
if (lean_is_scalar(x_545)) {
 x_547 = lean_alloc_ctor(0, 2, 0);
} else {
 x_547 = x_545;
}
lean_ctor_set(x_547, 0, x_546);
lean_ctor_set(x_547, 1, x_544);
return x_547;
}
}
else
{
lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; uint8_t x_560; lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_565; lean_object* x_566; lean_object* x_567; lean_object* x_568; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_548 = lean_ctor_get(x_392, 1);
lean_inc(x_548);
lean_dec(x_392);
x_549 = lean_ctor_get(x_393, 0);
lean_inc(x_549);
lean_dec(x_393);
x_550 = lean_st_ref_take(x_3, x_548);
x_551 = lean_ctor_get(x_550, 0);
lean_inc(x_551);
x_552 = lean_ctor_get(x_550, 1);
lean_inc(x_552);
lean_dec(x_550);
x_553 = lean_ctor_get(x_551, 0);
lean_inc(x_553);
x_554 = lean_ctor_get(x_551, 1);
lean_inc(x_554);
x_555 = lean_ctor_get(x_551, 2);
lean_inc(x_555);
if (lean_is_exclusive(x_551)) {
 lean_ctor_release(x_551, 0);
 lean_ctor_release(x_551, 1);
 lean_ctor_release(x_551, 2);
 x_556 = x_551;
} else {
 lean_dec_ref(x_551);
 x_556 = lean_box(0);
}
x_557 = lean_ctor_get(x_549, 0);
lean_inc(x_557);
x_558 = lean_ctor_get(x_549, 1);
lean_inc(x_558);
x_559 = lean_ctor_get(x_549, 3);
lean_inc(x_559);
lean_dec(x_549);
x_560 = 0;
x_561 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_561, 0, x_557);
lean_ctor_set(x_561, 1, x_558);
lean_ctor_set(x_561, 2, x_559);
lean_ctor_set_uint8(x_561, sizeof(void*)*3, x_560);
x_562 = lean_array_push(x_554, x_561);
if (lean_is_scalar(x_556)) {
 x_563 = lean_alloc_ctor(0, 3, 0);
} else {
 x_563 = x_556;
}
lean_ctor_set(x_563, 0, x_553);
lean_ctor_set(x_563, 1, x_562);
lean_ctor_set(x_563, 2, x_555);
x_564 = lean_st_ref_set(x_3, x_563, x_552);
lean_dec(x_3);
x_565 = lean_ctor_get(x_564, 1);
lean_inc(x_565);
if (lean_is_exclusive(x_564)) {
 lean_ctor_release(x_564, 0);
 lean_ctor_release(x_564, 1);
 x_566 = x_564;
} else {
 lean_dec_ref(x_564);
 x_566 = lean_box(0);
}
x_567 = lean_box(0);
if (lean_is_scalar(x_566)) {
 x_568 = lean_alloc_ctor(0, 2, 0);
} else {
 x_568 = x_566;
}
lean_ctor_set(x_568, 0, x_567);
lean_ctor_set(x_568, 1, x_565);
return x_568;
}
}
}
}
}
else
{
lean_object* x_569; 
lean_dec(x_14);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_569 = lean_box(0);
lean_ctor_set(x_9, 0, x_569);
return x_9;
}
}
else
{
lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; 
x_570 = lean_ctor_get(x_9, 0);
x_571 = lean_ctor_get(x_9, 1);
lean_inc(x_571);
lean_inc(x_570);
lean_dec(x_9);
x_572 = lean_ctor_get(x_570, 0);
lean_inc(x_572);
lean_dec(x_570);
x_573 = l_Lean_RBNode_findCore___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__2(x_572, x_1);
lean_dec(x_572);
if (lean_obj_tag(x_573) == 0)
{
lean_object* x_574; lean_object* x_575; lean_object* x_576; lean_object* x_577; lean_object* x_578; uint8_t x_579; 
lean_inc(x_1);
x_574 = l_Lean_Compiler_LCNF_Closure_markVisited(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_571);
x_575 = lean_ctor_get(x_574, 1);
lean_inc(x_575);
if (lean_is_exclusive(x_574)) {
 lean_ctor_release(x_574, 0);
 lean_ctor_release(x_574, 1);
 x_576 = x_574;
} else {
 lean_dec_ref(x_574);
 x_576 = lean_box(0);
}
x_577 = lean_ctor_get(x_2, 0);
lean_inc(x_577);
lean_inc(x_1);
x_578 = lean_apply_1(x_577, x_1);
x_579 = lean_unbox(x_578);
lean_dec(x_578);
if (x_579 == 0)
{
lean_object* x_580; lean_object* x_581; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_580 = lean_box(0);
if (lean_is_scalar(x_576)) {
 x_581 = lean_alloc_ctor(0, 2, 0);
} else {
 x_581 = x_576;
}
lean_ctor_set(x_581, 0, x_580);
lean_ctor_set(x_581, 1, x_575);
return x_581;
}
else
{
lean_object* x_582; lean_object* x_583; 
lean_dec(x_576);
x_582 = l_Lean_Compiler_LCNF_findFunDecl_x3f(x_1, x_4, x_5, x_6, x_7, x_575);
x_583 = lean_ctor_get(x_582, 0);
lean_inc(x_583);
if (lean_obj_tag(x_583) == 0)
{
lean_object* x_584; lean_object* x_585; lean_object* x_586; 
x_584 = lean_ctor_get(x_582, 1);
lean_inc(x_584);
lean_dec(x_582);
x_585 = l_Lean_Compiler_LCNF_findParam_x3f(x_1, x_4, x_5, x_6, x_7, x_584);
x_586 = lean_ctor_get(x_585, 0);
lean_inc(x_586);
if (lean_obj_tag(x_586) == 0)
{
lean_object* x_587; lean_object* x_588; lean_object* x_589; 
x_587 = lean_ctor_get(x_585, 1);
lean_inc(x_587);
lean_dec(x_585);
x_588 = l_Lean_Compiler_LCNF_findLetDecl_x3f(x_1, x_4, x_5, x_6, x_7, x_587);
lean_dec(x_1);
x_589 = lean_ctor_get(x_588, 0);
lean_inc(x_589);
if (lean_obj_tag(x_589) == 0)
{
lean_object* x_590; lean_object* x_591; lean_object* x_592; 
x_590 = lean_ctor_get(x_588, 1);
lean_inc(x_590);
lean_dec(x_588);
x_591 = l_Lean_Compiler_LCNF_Closure_collectFVar___closed__4;
x_592 = l_panic___at_Lean_Compiler_LCNF_Closure_collectFVar___spec__1(x_591, x_2, x_3, x_4, x_5, x_6, x_7, x_590);
return x_592;
}
else
{
lean_object* x_593; lean_object* x_594; lean_object* x_595; lean_object* x_596; lean_object* x_597; lean_object* x_598; lean_object* x_599; lean_object* x_600; lean_object* x_601; uint8_t x_602; lean_object* x_603; 
x_593 = lean_ctor_get(x_589, 0);
lean_inc(x_593);
if (lean_is_exclusive(x_589)) {
 lean_ctor_release(x_589, 0);
 x_594 = x_589;
} else {
 lean_dec_ref(x_589);
 x_594 = lean_box(0);
}
x_595 = lean_ctor_get(x_588, 1);
lean_inc(x_595);
lean_dec(x_588);
x_596 = lean_ctor_get(x_593, 0);
lean_inc(x_596);
x_597 = lean_ctor_get(x_593, 1);
lean_inc(x_597);
x_598 = lean_ctor_get(x_593, 2);
lean_inc(x_598);
x_599 = lean_ctor_get(x_593, 3);
lean_inc(x_599);
x_600 = lean_alloc_closure((void*)(l_Lean_Expr_isFVar___boxed), 1, 0);
x_601 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Closure_collectType___lambda__1___boxed), 8, 0);
x_602 = 0;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_598);
x_603 = l_Lean_ForEachExprWhere_visit___at_Lean_Compiler_LCNF_Closure_collectType___spec__1(x_600, x_601, x_598, x_602, x_2, x_3, x_4, x_5, x_6, x_7, x_595);
if (lean_obj_tag(x_603) == 0)
{
uint8_t x_604; 
x_604 = lean_ctor_get_uint8(x_2, sizeof(void*)*2);
if (x_604 == 0)
{
lean_object* x_605; lean_object* x_606; lean_object* x_607; uint8_t x_608; 
x_605 = lean_ctor_get(x_603, 1);
lean_inc(x_605);
lean_dec(x_603);
x_606 = lean_ctor_get(x_2, 1);
lean_inc(x_606);
lean_inc(x_596);
x_607 = lean_apply_1(x_606, x_596);
x_608 = lean_unbox(x_607);
lean_dec(x_607);
if (x_608 == 0)
{
lean_object* x_609; 
lean_dec(x_598);
lean_dec(x_597);
lean_dec(x_596);
lean_inc(x_3);
x_609 = l_Lean_Compiler_LCNF_Closure_collectLetValue(x_599, x_2, x_3, x_4, x_5, x_6, x_7, x_605);
if (lean_obj_tag(x_609) == 0)
{
lean_object* x_610; lean_object* x_611; lean_object* x_612; lean_object* x_613; lean_object* x_614; lean_object* x_615; lean_object* x_616; lean_object* x_617; lean_object* x_618; lean_object* x_619; lean_object* x_620; lean_object* x_621; lean_object* x_622; lean_object* x_623; lean_object* x_624; lean_object* x_625; 
x_610 = lean_ctor_get(x_609, 1);
lean_inc(x_610);
lean_dec(x_609);
x_611 = lean_st_ref_take(x_3, x_610);
x_612 = lean_ctor_get(x_611, 0);
lean_inc(x_612);
x_613 = lean_ctor_get(x_611, 1);
lean_inc(x_613);
lean_dec(x_611);
x_614 = lean_ctor_get(x_612, 0);
lean_inc(x_614);
x_615 = lean_ctor_get(x_612, 1);
lean_inc(x_615);
x_616 = lean_ctor_get(x_612, 2);
lean_inc(x_616);
if (lean_is_exclusive(x_612)) {
 lean_ctor_release(x_612, 0);
 lean_ctor_release(x_612, 1);
 lean_ctor_release(x_612, 2);
 x_617 = x_612;
} else {
 lean_dec_ref(x_612);
 x_617 = lean_box(0);
}
if (lean_is_scalar(x_594)) {
 x_618 = lean_alloc_ctor(0, 1, 0);
} else {
 x_618 = x_594;
 lean_ctor_set_tag(x_618, 0);
}
lean_ctor_set(x_618, 0, x_593);
x_619 = lean_array_push(x_616, x_618);
if (lean_is_scalar(x_617)) {
 x_620 = lean_alloc_ctor(0, 3, 0);
} else {
 x_620 = x_617;
}
lean_ctor_set(x_620, 0, x_614);
lean_ctor_set(x_620, 1, x_615);
lean_ctor_set(x_620, 2, x_619);
x_621 = lean_st_ref_set(x_3, x_620, x_613);
lean_dec(x_3);
x_622 = lean_ctor_get(x_621, 1);
lean_inc(x_622);
if (lean_is_exclusive(x_621)) {
 lean_ctor_release(x_621, 0);
 lean_ctor_release(x_621, 1);
 x_623 = x_621;
} else {
 lean_dec_ref(x_621);
 x_623 = lean_box(0);
}
x_624 = lean_box(0);
if (lean_is_scalar(x_623)) {
 x_625 = lean_alloc_ctor(0, 2, 0);
} else {
 x_625 = x_623;
}
lean_ctor_set(x_625, 0, x_624);
lean_ctor_set(x_625, 1, x_622);
return x_625;
}
else
{
lean_object* x_626; lean_object* x_627; lean_object* x_628; lean_object* x_629; 
lean_dec(x_594);
lean_dec(x_593);
lean_dec(x_3);
x_626 = lean_ctor_get(x_609, 0);
lean_inc(x_626);
x_627 = lean_ctor_get(x_609, 1);
lean_inc(x_627);
if (lean_is_exclusive(x_609)) {
 lean_ctor_release(x_609, 0);
 lean_ctor_release(x_609, 1);
 x_628 = x_609;
} else {
 lean_dec_ref(x_609);
 x_628 = lean_box(0);
}
if (lean_is_scalar(x_628)) {
 x_629 = lean_alloc_ctor(1, 2, 0);
} else {
 x_629 = x_628;
}
lean_ctor_set(x_629, 0, x_626);
lean_ctor_set(x_629, 1, x_627);
return x_629;
}
}
else
{
lean_object* x_630; lean_object* x_631; lean_object* x_632; lean_object* x_633; lean_object* x_634; lean_object* x_635; lean_object* x_636; lean_object* x_637; lean_object* x_638; lean_object* x_639; lean_object* x_640; lean_object* x_641; lean_object* x_642; lean_object* x_643; lean_object* x_644; 
lean_dec(x_599);
lean_dec(x_594);
lean_dec(x_593);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_630 = lean_st_ref_take(x_3, x_605);
x_631 = lean_ctor_get(x_630, 0);
lean_inc(x_631);
x_632 = lean_ctor_get(x_630, 1);
lean_inc(x_632);
lean_dec(x_630);
x_633 = lean_ctor_get(x_631, 0);
lean_inc(x_633);
x_634 = lean_ctor_get(x_631, 1);
lean_inc(x_634);
x_635 = lean_ctor_get(x_631, 2);
lean_inc(x_635);
if (lean_is_exclusive(x_631)) {
 lean_ctor_release(x_631, 0);
 lean_ctor_release(x_631, 1);
 lean_ctor_release(x_631, 2);
 x_636 = x_631;
} else {
 lean_dec_ref(x_631);
 x_636 = lean_box(0);
}
x_637 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_637, 0, x_596);
lean_ctor_set(x_637, 1, x_597);
lean_ctor_set(x_637, 2, x_598);
lean_ctor_set_uint8(x_637, sizeof(void*)*3, x_602);
x_638 = lean_array_push(x_634, x_637);
if (lean_is_scalar(x_636)) {
 x_639 = lean_alloc_ctor(0, 3, 0);
} else {
 x_639 = x_636;
}
lean_ctor_set(x_639, 0, x_633);
lean_ctor_set(x_639, 1, x_638);
lean_ctor_set(x_639, 2, x_635);
x_640 = lean_st_ref_set(x_3, x_639, x_632);
lean_dec(x_3);
x_641 = lean_ctor_get(x_640, 1);
lean_inc(x_641);
if (lean_is_exclusive(x_640)) {
 lean_ctor_release(x_640, 0);
 lean_ctor_release(x_640, 1);
 x_642 = x_640;
} else {
 lean_dec_ref(x_640);
 x_642 = lean_box(0);
}
x_643 = lean_box(0);
if (lean_is_scalar(x_642)) {
 x_644 = lean_alloc_ctor(0, 2, 0);
} else {
 x_644 = x_642;
}
lean_ctor_set(x_644, 0, x_643);
lean_ctor_set(x_644, 1, x_641);
return x_644;
}
}
else
{
lean_object* x_645; lean_object* x_646; lean_object* x_647; lean_object* x_648; lean_object* x_649; lean_object* x_650; lean_object* x_651; lean_object* x_652; lean_object* x_653; lean_object* x_654; lean_object* x_655; lean_object* x_656; lean_object* x_657; lean_object* x_658; lean_object* x_659; lean_object* x_660; 
lean_dec(x_599);
lean_dec(x_594);
lean_dec(x_593);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_645 = lean_ctor_get(x_603, 1);
lean_inc(x_645);
lean_dec(x_603);
x_646 = lean_st_ref_take(x_3, x_645);
x_647 = lean_ctor_get(x_646, 0);
lean_inc(x_647);
x_648 = lean_ctor_get(x_646, 1);
lean_inc(x_648);
lean_dec(x_646);
x_649 = lean_ctor_get(x_647, 0);
lean_inc(x_649);
x_650 = lean_ctor_get(x_647, 1);
lean_inc(x_650);
x_651 = lean_ctor_get(x_647, 2);
lean_inc(x_651);
if (lean_is_exclusive(x_647)) {
 lean_ctor_release(x_647, 0);
 lean_ctor_release(x_647, 1);
 lean_ctor_release(x_647, 2);
 x_652 = x_647;
} else {
 lean_dec_ref(x_647);
 x_652 = lean_box(0);
}
x_653 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_653, 0, x_596);
lean_ctor_set(x_653, 1, x_597);
lean_ctor_set(x_653, 2, x_598);
lean_ctor_set_uint8(x_653, sizeof(void*)*3, x_602);
x_654 = lean_array_push(x_650, x_653);
if (lean_is_scalar(x_652)) {
 x_655 = lean_alloc_ctor(0, 3, 0);
} else {
 x_655 = x_652;
}
lean_ctor_set(x_655, 0, x_649);
lean_ctor_set(x_655, 1, x_654);
lean_ctor_set(x_655, 2, x_651);
x_656 = lean_st_ref_set(x_3, x_655, x_648);
lean_dec(x_3);
x_657 = lean_ctor_get(x_656, 1);
lean_inc(x_657);
if (lean_is_exclusive(x_656)) {
 lean_ctor_release(x_656, 0);
 lean_ctor_release(x_656, 1);
 x_658 = x_656;
} else {
 lean_dec_ref(x_656);
 x_658 = lean_box(0);
}
x_659 = lean_box(0);
if (lean_is_scalar(x_658)) {
 x_660 = lean_alloc_ctor(0, 2, 0);
} else {
 x_660 = x_658;
}
lean_ctor_set(x_660, 0, x_659);
lean_ctor_set(x_660, 1, x_657);
return x_660;
}
}
else
{
lean_object* x_661; lean_object* x_662; lean_object* x_663; lean_object* x_664; 
lean_dec(x_599);
lean_dec(x_598);
lean_dec(x_597);
lean_dec(x_596);
lean_dec(x_594);
lean_dec(x_593);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_661 = lean_ctor_get(x_603, 0);
lean_inc(x_661);
x_662 = lean_ctor_get(x_603, 1);
lean_inc(x_662);
if (lean_is_exclusive(x_603)) {
 lean_ctor_release(x_603, 0);
 lean_ctor_release(x_603, 1);
 x_663 = x_603;
} else {
 lean_dec_ref(x_603);
 x_663 = lean_box(0);
}
if (lean_is_scalar(x_663)) {
 x_664 = lean_alloc_ctor(1, 2, 0);
} else {
 x_664 = x_663;
}
lean_ctor_set(x_664, 0, x_661);
lean_ctor_set(x_664, 1, x_662);
return x_664;
}
}
}
else
{
lean_object* x_665; lean_object* x_666; lean_object* x_667; lean_object* x_668; lean_object* x_669; uint8_t x_670; lean_object* x_671; 
lean_dec(x_1);
x_665 = lean_ctor_get(x_585, 1);
lean_inc(x_665);
lean_dec(x_585);
x_666 = lean_ctor_get(x_586, 0);
lean_inc(x_666);
lean_dec(x_586);
x_667 = lean_ctor_get(x_666, 2);
lean_inc(x_667);
x_668 = lean_alloc_closure((void*)(l_Lean_Expr_isFVar___boxed), 1, 0);
x_669 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Closure_collectType___lambda__1___boxed), 8, 0);
x_670 = 0;
lean_inc(x_3);
x_671 = l_Lean_ForEachExprWhere_visit___at_Lean_Compiler_LCNF_Closure_collectType___spec__1(x_668, x_669, x_667, x_670, x_2, x_3, x_4, x_5, x_6, x_7, x_665);
if (lean_obj_tag(x_671) == 0)
{
lean_object* x_672; lean_object* x_673; lean_object* x_674; lean_object* x_675; lean_object* x_676; lean_object* x_677; lean_object* x_678; lean_object* x_679; lean_object* x_680; lean_object* x_681; lean_object* x_682; lean_object* x_683; lean_object* x_684; lean_object* x_685; lean_object* x_686; 
x_672 = lean_ctor_get(x_671, 1);
lean_inc(x_672);
lean_dec(x_671);
x_673 = lean_st_ref_take(x_3, x_672);
x_674 = lean_ctor_get(x_673, 0);
lean_inc(x_674);
x_675 = lean_ctor_get(x_673, 1);
lean_inc(x_675);
lean_dec(x_673);
x_676 = lean_ctor_get(x_674, 0);
lean_inc(x_676);
x_677 = lean_ctor_get(x_674, 1);
lean_inc(x_677);
x_678 = lean_ctor_get(x_674, 2);
lean_inc(x_678);
if (lean_is_exclusive(x_674)) {
 lean_ctor_release(x_674, 0);
 lean_ctor_release(x_674, 1);
 lean_ctor_release(x_674, 2);
 x_679 = x_674;
} else {
 lean_dec_ref(x_674);
 x_679 = lean_box(0);
}
x_680 = lean_array_push(x_677, x_666);
if (lean_is_scalar(x_679)) {
 x_681 = lean_alloc_ctor(0, 3, 0);
} else {
 x_681 = x_679;
}
lean_ctor_set(x_681, 0, x_676);
lean_ctor_set(x_681, 1, x_680);
lean_ctor_set(x_681, 2, x_678);
x_682 = lean_st_ref_set(x_3, x_681, x_675);
lean_dec(x_3);
x_683 = lean_ctor_get(x_682, 1);
lean_inc(x_683);
if (lean_is_exclusive(x_682)) {
 lean_ctor_release(x_682, 0);
 lean_ctor_release(x_682, 1);
 x_684 = x_682;
} else {
 lean_dec_ref(x_682);
 x_684 = lean_box(0);
}
x_685 = lean_box(0);
if (lean_is_scalar(x_684)) {
 x_686 = lean_alloc_ctor(0, 2, 0);
} else {
 x_686 = x_684;
}
lean_ctor_set(x_686, 0, x_685);
lean_ctor_set(x_686, 1, x_683);
return x_686;
}
else
{
lean_object* x_687; lean_object* x_688; lean_object* x_689; lean_object* x_690; 
lean_dec(x_666);
lean_dec(x_3);
x_687 = lean_ctor_get(x_671, 0);
lean_inc(x_687);
x_688 = lean_ctor_get(x_671, 1);
lean_inc(x_688);
if (lean_is_exclusive(x_671)) {
 lean_ctor_release(x_671, 0);
 lean_ctor_release(x_671, 1);
 x_689 = x_671;
} else {
 lean_dec_ref(x_671);
 x_689 = lean_box(0);
}
if (lean_is_scalar(x_689)) {
 x_690 = lean_alloc_ctor(1, 2, 0);
} else {
 x_690 = x_689;
}
lean_ctor_set(x_690, 0, x_687);
lean_ctor_set(x_690, 1, x_688);
return x_690;
}
}
}
else
{
uint8_t x_691; 
lean_dec(x_1);
x_691 = lean_ctor_get_uint8(x_2, sizeof(void*)*2);
if (x_691 == 0)
{
lean_object* x_692; lean_object* x_693; lean_object* x_694; lean_object* x_695; lean_object* x_696; lean_object* x_697; lean_object* x_698; lean_object* x_699; uint8_t x_700; 
x_692 = lean_ctor_get(x_583, 0);
lean_inc(x_692);
if (lean_is_exclusive(x_583)) {
 lean_ctor_release(x_583, 0);
 x_693 = x_583;
} else {
 lean_dec_ref(x_583);
 x_693 = lean_box(0);
}
x_694 = lean_ctor_get(x_582, 1);
lean_inc(x_694);
lean_dec(x_582);
x_695 = lean_ctor_get(x_2, 1);
lean_inc(x_695);
x_696 = lean_ctor_get(x_692, 0);
lean_inc(x_696);
x_697 = lean_ctor_get(x_692, 1);
lean_inc(x_697);
x_698 = lean_ctor_get(x_692, 3);
lean_inc(x_698);
lean_inc(x_696);
x_699 = lean_apply_1(x_695, x_696);
x_700 = lean_unbox(x_699);
lean_dec(x_699);
if (x_700 == 0)
{
lean_object* x_701; 
lean_dec(x_698);
lean_dec(x_697);
lean_dec(x_696);
lean_inc(x_3);
lean_inc(x_692);
x_701 = l_Lean_Compiler_LCNF_Closure_collectFunDecl(x_692, x_2, x_3, x_4, x_5, x_6, x_7, x_694);
if (lean_obj_tag(x_701) == 0)
{
lean_object* x_702; lean_object* x_703; lean_object* x_704; lean_object* x_705; lean_object* x_706; lean_object* x_707; lean_object* x_708; lean_object* x_709; lean_object* x_710; lean_object* x_711; lean_object* x_712; lean_object* x_713; lean_object* x_714; lean_object* x_715; lean_object* x_716; lean_object* x_717; 
x_702 = lean_ctor_get(x_701, 1);
lean_inc(x_702);
lean_dec(x_701);
x_703 = lean_st_ref_take(x_3, x_702);
x_704 = lean_ctor_get(x_703, 0);
lean_inc(x_704);
x_705 = lean_ctor_get(x_703, 1);
lean_inc(x_705);
lean_dec(x_703);
x_706 = lean_ctor_get(x_704, 0);
lean_inc(x_706);
x_707 = lean_ctor_get(x_704, 1);
lean_inc(x_707);
x_708 = lean_ctor_get(x_704, 2);
lean_inc(x_708);
if (lean_is_exclusive(x_704)) {
 lean_ctor_release(x_704, 0);
 lean_ctor_release(x_704, 1);
 lean_ctor_release(x_704, 2);
 x_709 = x_704;
} else {
 lean_dec_ref(x_704);
 x_709 = lean_box(0);
}
if (lean_is_scalar(x_693)) {
 x_710 = lean_alloc_ctor(1, 1, 0);
} else {
 x_710 = x_693;
}
lean_ctor_set(x_710, 0, x_692);
x_711 = lean_array_push(x_708, x_710);
if (lean_is_scalar(x_709)) {
 x_712 = lean_alloc_ctor(0, 3, 0);
} else {
 x_712 = x_709;
}
lean_ctor_set(x_712, 0, x_706);
lean_ctor_set(x_712, 1, x_707);
lean_ctor_set(x_712, 2, x_711);
x_713 = lean_st_ref_set(x_3, x_712, x_705);
lean_dec(x_3);
x_714 = lean_ctor_get(x_713, 1);
lean_inc(x_714);
if (lean_is_exclusive(x_713)) {
 lean_ctor_release(x_713, 0);
 lean_ctor_release(x_713, 1);
 x_715 = x_713;
} else {
 lean_dec_ref(x_713);
 x_715 = lean_box(0);
}
x_716 = lean_box(0);
if (lean_is_scalar(x_715)) {
 x_717 = lean_alloc_ctor(0, 2, 0);
} else {
 x_717 = x_715;
}
lean_ctor_set(x_717, 0, x_716);
lean_ctor_set(x_717, 1, x_714);
return x_717;
}
else
{
lean_object* x_718; lean_object* x_719; lean_object* x_720; lean_object* x_721; 
lean_dec(x_693);
lean_dec(x_692);
lean_dec(x_3);
x_718 = lean_ctor_get(x_701, 0);
lean_inc(x_718);
x_719 = lean_ctor_get(x_701, 1);
lean_inc(x_719);
if (lean_is_exclusive(x_701)) {
 lean_ctor_release(x_701, 0);
 lean_ctor_release(x_701, 1);
 x_720 = x_701;
} else {
 lean_dec_ref(x_701);
 x_720 = lean_box(0);
}
if (lean_is_scalar(x_720)) {
 x_721 = lean_alloc_ctor(1, 2, 0);
} else {
 x_721 = x_720;
}
lean_ctor_set(x_721, 0, x_718);
lean_ctor_set(x_721, 1, x_719);
return x_721;
}
}
else
{
lean_object* x_722; lean_object* x_723; lean_object* x_724; lean_object* x_725; lean_object* x_726; lean_object* x_727; lean_object* x_728; uint8_t x_729; lean_object* x_730; lean_object* x_731; lean_object* x_732; lean_object* x_733; lean_object* x_734; lean_object* x_735; lean_object* x_736; lean_object* x_737; 
lean_dec(x_693);
lean_dec(x_692);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_722 = lean_st_ref_take(x_3, x_694);
x_723 = lean_ctor_get(x_722, 0);
lean_inc(x_723);
x_724 = lean_ctor_get(x_722, 1);
lean_inc(x_724);
lean_dec(x_722);
x_725 = lean_ctor_get(x_723, 0);
lean_inc(x_725);
x_726 = lean_ctor_get(x_723, 1);
lean_inc(x_726);
x_727 = lean_ctor_get(x_723, 2);
lean_inc(x_727);
if (lean_is_exclusive(x_723)) {
 lean_ctor_release(x_723, 0);
 lean_ctor_release(x_723, 1);
 lean_ctor_release(x_723, 2);
 x_728 = x_723;
} else {
 lean_dec_ref(x_723);
 x_728 = lean_box(0);
}
x_729 = 0;
x_730 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_730, 0, x_696);
lean_ctor_set(x_730, 1, x_697);
lean_ctor_set(x_730, 2, x_698);
lean_ctor_set_uint8(x_730, sizeof(void*)*3, x_729);
x_731 = lean_array_push(x_726, x_730);
if (lean_is_scalar(x_728)) {
 x_732 = lean_alloc_ctor(0, 3, 0);
} else {
 x_732 = x_728;
}
lean_ctor_set(x_732, 0, x_725);
lean_ctor_set(x_732, 1, x_731);
lean_ctor_set(x_732, 2, x_727);
x_733 = lean_st_ref_set(x_3, x_732, x_724);
lean_dec(x_3);
x_734 = lean_ctor_get(x_733, 1);
lean_inc(x_734);
if (lean_is_exclusive(x_733)) {
 lean_ctor_release(x_733, 0);
 lean_ctor_release(x_733, 1);
 x_735 = x_733;
} else {
 lean_dec_ref(x_733);
 x_735 = lean_box(0);
}
x_736 = lean_box(0);
if (lean_is_scalar(x_735)) {
 x_737 = lean_alloc_ctor(0, 2, 0);
} else {
 x_737 = x_735;
}
lean_ctor_set(x_737, 0, x_736);
lean_ctor_set(x_737, 1, x_734);
return x_737;
}
}
else
{
lean_object* x_738; lean_object* x_739; lean_object* x_740; lean_object* x_741; lean_object* x_742; lean_object* x_743; lean_object* x_744; lean_object* x_745; lean_object* x_746; lean_object* x_747; lean_object* x_748; lean_object* x_749; uint8_t x_750; lean_object* x_751; lean_object* x_752; lean_object* x_753; lean_object* x_754; lean_object* x_755; lean_object* x_756; lean_object* x_757; lean_object* x_758; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_738 = lean_ctor_get(x_582, 1);
lean_inc(x_738);
lean_dec(x_582);
x_739 = lean_ctor_get(x_583, 0);
lean_inc(x_739);
lean_dec(x_583);
x_740 = lean_st_ref_take(x_3, x_738);
x_741 = lean_ctor_get(x_740, 0);
lean_inc(x_741);
x_742 = lean_ctor_get(x_740, 1);
lean_inc(x_742);
lean_dec(x_740);
x_743 = lean_ctor_get(x_741, 0);
lean_inc(x_743);
x_744 = lean_ctor_get(x_741, 1);
lean_inc(x_744);
x_745 = lean_ctor_get(x_741, 2);
lean_inc(x_745);
if (lean_is_exclusive(x_741)) {
 lean_ctor_release(x_741, 0);
 lean_ctor_release(x_741, 1);
 lean_ctor_release(x_741, 2);
 x_746 = x_741;
} else {
 lean_dec_ref(x_741);
 x_746 = lean_box(0);
}
x_747 = lean_ctor_get(x_739, 0);
lean_inc(x_747);
x_748 = lean_ctor_get(x_739, 1);
lean_inc(x_748);
x_749 = lean_ctor_get(x_739, 3);
lean_inc(x_749);
lean_dec(x_739);
x_750 = 0;
x_751 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_751, 0, x_747);
lean_ctor_set(x_751, 1, x_748);
lean_ctor_set(x_751, 2, x_749);
lean_ctor_set_uint8(x_751, sizeof(void*)*3, x_750);
x_752 = lean_array_push(x_744, x_751);
if (lean_is_scalar(x_746)) {
 x_753 = lean_alloc_ctor(0, 3, 0);
} else {
 x_753 = x_746;
}
lean_ctor_set(x_753, 0, x_743);
lean_ctor_set(x_753, 1, x_752);
lean_ctor_set(x_753, 2, x_745);
x_754 = lean_st_ref_set(x_3, x_753, x_742);
lean_dec(x_3);
x_755 = lean_ctor_get(x_754, 1);
lean_inc(x_755);
if (lean_is_exclusive(x_754)) {
 lean_ctor_release(x_754, 0);
 lean_ctor_release(x_754, 1);
 x_756 = x_754;
} else {
 lean_dec_ref(x_754);
 x_756 = lean_box(0);
}
x_757 = lean_box(0);
if (lean_is_scalar(x_756)) {
 x_758 = lean_alloc_ctor(0, 2, 0);
} else {
 x_758 = x_756;
}
lean_ctor_set(x_758, 0, x_757);
lean_ctor_set(x_758, 1, x_755);
return x_758;
}
}
}
}
else
{
lean_object* x_759; lean_object* x_760; 
lean_dec(x_573);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_759 = lean_box(0);
x_760 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_760, 0, x_759);
lean_ctor_set(x_760, 1, x_571);
return x_760;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Closure_collectLetValue___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_eq(x_2, x_3);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_4);
x_13 = lean_array_uget(x_1, x_2);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_14 = l_Lean_Compiler_LCNF_Closure_collectArg(x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = 1;
x_18 = lean_usize_add(x_2, x_17);
x_2 = x_18;
x_4 = x_15;
x_11 = x_16;
goto _start;
}
else
{
uint8_t x_20; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_20 = !lean_is_exclusive(x_14);
if (x_20 == 0)
{
return x_14;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_14, 0);
x_22 = lean_ctor_get(x_14, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_14);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
else
{
lean_object* x_24; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_4);
lean_ctor_set(x_24, 1, x_11);
return x_24;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Closure_collectLetValue(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 2:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_1, 2);
lean_inc(x_9);
lean_dec(x_1);
x_10 = l_Lean_Compiler_LCNF_Closure_collectFVar(x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
case 3:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_1, 2);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_array_get_size(x_11);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_nat_dec_lt(x_13, x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_8);
return x_16;
}
else
{
uint8_t x_17; 
x_17 = lean_nat_dec_le(x_12, x_12);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_8);
return x_19;
}
else
{
size_t x_20; size_t x_21; lean_object* x_22; lean_object* x_23; 
x_20 = 0;
x_21 = lean_usize_of_nat(x_12);
lean_dec(x_12);
x_22 = lean_box(0);
x_23 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Closure_collectLetValue___spec__1(x_11, x_20, x_21, x_22, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_11);
return x_23;
}
}
}
case 4:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_1, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_1, 1);
lean_inc(x_25);
lean_dec(x_1);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_26 = l_Lean_Compiler_LCNF_Closure_collectFVar(x_24, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_26) == 0)
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_28 = lean_ctor_get(x_26, 1);
x_29 = lean_ctor_get(x_26, 0);
lean_dec(x_29);
x_30 = lean_array_get_size(x_25);
x_31 = lean_unsigned_to_nat(0u);
x_32 = lean_nat_dec_lt(x_31, x_30);
if (x_32 == 0)
{
lean_object* x_33; 
lean_dec(x_30);
lean_dec(x_25);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_33 = lean_box(0);
lean_ctor_set(x_26, 0, x_33);
return x_26;
}
else
{
uint8_t x_34; 
x_34 = lean_nat_dec_le(x_30, x_30);
if (x_34 == 0)
{
lean_object* x_35; 
lean_dec(x_30);
lean_dec(x_25);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_35 = lean_box(0);
lean_ctor_set(x_26, 0, x_35);
return x_26;
}
else
{
size_t x_36; size_t x_37; lean_object* x_38; lean_object* x_39; 
lean_free_object(x_26);
x_36 = 0;
x_37 = lean_usize_of_nat(x_30);
lean_dec(x_30);
x_38 = lean_box(0);
x_39 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Closure_collectLetValue___spec__1(x_25, x_36, x_37, x_38, x_2, x_3, x_4, x_5, x_6, x_7, x_28);
lean_dec(x_25);
return x_39;
}
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_40 = lean_ctor_get(x_26, 1);
lean_inc(x_40);
lean_dec(x_26);
x_41 = lean_array_get_size(x_25);
x_42 = lean_unsigned_to_nat(0u);
x_43 = lean_nat_dec_lt(x_42, x_41);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; 
lean_dec(x_41);
lean_dec(x_25);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_44 = lean_box(0);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_40);
return x_45;
}
else
{
uint8_t x_46; 
x_46 = lean_nat_dec_le(x_41, x_41);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; 
lean_dec(x_41);
lean_dec(x_25);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_47 = lean_box(0);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_40);
return x_48;
}
else
{
size_t x_49; size_t x_50; lean_object* x_51; lean_object* x_52; 
x_49 = 0;
x_50 = lean_usize_of_nat(x_41);
lean_dec(x_41);
x_51 = lean_box(0);
x_52 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Closure_collectLetValue___spec__1(x_25, x_49, x_50, x_51, x_2, x_3, x_4, x_5, x_6, x_7, x_40);
lean_dec(x_25);
return x_52;
}
}
}
}
else
{
uint8_t x_53; 
lean_dec(x_25);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_53 = !lean_is_exclusive(x_26);
if (x_53 == 0)
{
return x_26;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_26, 0);
x_55 = lean_ctor_get(x_26, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_26);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
default: 
{
lean_object* x_57; lean_object* x_58; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_57 = lean_box(0);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_8);
return x_58;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Closure_collectArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
case 1:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
lean_dec(x_1);
x_12 = l_Lean_Compiler_LCNF_Closure_collectFVar(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_12;
}
default: 
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
lean_dec(x_1);
x_14 = lean_alloc_closure((void*)(l_Lean_Expr_isFVar___boxed), 1, 0);
x_15 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Closure_collectType___lambda__1___boxed), 8, 0);
x_16 = 0;
x_17 = l_Lean_ForEachExprWhere_visit___at_Lean_Compiler_LCNF_Closure_collectType___spec__1(x_14, x_15, x_13, x_16, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Closure_collectFunDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_1, 3);
lean_inc(x_9);
x_10 = lean_alloc_closure((void*)(l_Lean_Expr_isFVar___boxed), 1, 0);
x_11 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Closure_collectType___lambda__1___boxed), 8, 0);
x_12 = 0;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_13 = l_Lean_ForEachExprWhere_visit___at_Lean_Compiler_LCNF_Closure_collectType___spec__1(x_10, x_11, x_9, x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_ctor_get(x_1, 2);
lean_inc(x_15);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_16 = l_Lean_Compiler_LCNF_Closure_collectParams(x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_14);
lean_dec(x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_ctor_get(x_1, 4);
lean_inc(x_18);
lean_dec(x_1);
x_19 = !lean_is_exclusive(x_2);
if (x_19 == 0)
{
uint8_t x_20; lean_object* x_21; 
x_20 = 1;
lean_ctor_set_uint8(x_2, sizeof(void*)*2, x_20);
x_21 = l_Lean_Compiler_LCNF_Closure_collectCode(x_18, x_2, x_3, x_4, x_5, x_6, x_7, x_17);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_2, 0);
x_23 = lean_ctor_get(x_2, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_2);
x_24 = 1;
x_25 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_25, 0, x_22);
lean_ctor_set(x_25, 1, x_23);
lean_ctor_set_uint8(x_25, sizeof(void*)*2, x_24);
x_26 = l_Lean_Compiler_LCNF_Closure_collectCode(x_18, x_25, x_3, x_4, x_5, x_6, x_7, x_17);
return x_26;
}
}
else
{
uint8_t x_27; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_27 = !lean_is_exclusive(x_16);
if (x_27 == 0)
{
return x_16;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_16, 0);
x_29 = lean_ctor_get(x_16, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_16);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
else
{
uint8_t x_31; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_31 = !lean_is_exclusive(x_13);
if (x_31 == 0)
{
return x_13;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_13, 0);
x_33 = lean_ctor_get(x_13, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_13);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Closure_collectCode___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_eq(x_2, x_3);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_4);
x_13 = lean_array_uget(x_1, x_2);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 2);
lean_inc(x_15);
lean_dec(x_13);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_16 = l_Lean_Compiler_LCNF_Closure_collectParams(x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_14);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_18 = l_Lean_Compiler_LCNF_Closure_collectCode(x_15, x_5, x_6, x_7, x_8, x_9, x_10, x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; size_t x_21; size_t x_22; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = 1;
x_22 = lean_usize_add(x_2, x_21);
x_2 = x_22;
x_4 = x_19;
x_11 = x_20;
goto _start;
}
else
{
uint8_t x_24; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_24 = !lean_is_exclusive(x_18);
if (x_24 == 0)
{
return x_18;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_18, 0);
x_26 = lean_ctor_get(x_18, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_18);
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
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_28 = !lean_is_exclusive(x_16);
if (x_28 == 0)
{
return x_16;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_16, 0);
x_30 = lean_ctor_get(x_16, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_16);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_13, 0);
lean_inc(x_32);
lean_dec(x_13);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_33 = l_Lean_Compiler_LCNF_Closure_collectCode(x_32, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; size_t x_36; size_t x_37; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = 1;
x_37 = lean_usize_add(x_2, x_36);
x_2 = x_37;
x_4 = x_34;
x_11 = x_35;
goto _start;
}
else
{
uint8_t x_39; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_39 = !lean_is_exclusive(x_33);
if (x_39 == 0)
{
return x_33;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_33, 0);
x_41 = lean_ctor_get(x_33, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_33);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
}
else
{
lean_object* x_43; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_4);
lean_ctor_set(x_43, 1, x_11);
return x_43;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Closure_collectCode(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_ctor_get(x_9, 2);
lean_inc(x_11);
x_12 = lean_alloc_closure((void*)(l_Lean_Expr_isFVar___boxed), 1, 0);
x_13 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Closure_collectType___lambda__1___boxed), 8, 0);
x_14 = 0;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_11);
x_15 = l_Lean_ForEachExprWhere_visit___at_Lean_Compiler_LCNF_Closure_collectType___spec__1(x_12, x_13, x_11, x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = lean_ctor_get_uint8(x_2, sizeof(void*)*2);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; 
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_9, 3);
lean_inc(x_18);
lean_dec(x_9);
x_19 = lean_ctor_get(x_2, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_2, 1);
lean_inc(x_20);
x_21 = l_Lean_Expr_isForall(x_11);
lean_dec(x_11);
x_22 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_22, 0, x_19);
lean_ctor_set(x_22, 1, x_20);
lean_ctor_set_uint8(x_22, sizeof(void*)*2, x_21);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_23 = l_Lean_Compiler_LCNF_Closure_collectLetValue(x_18, x_22, x_3, x_4, x_5, x_6, x_7, x_17);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
x_1 = x_10;
x_8 = x_24;
goto _start;
}
else
{
uint8_t x_26; 
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_26 = !lean_is_exclusive(x_23);
if (x_26 == 0)
{
return x_23;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_23, 0);
x_28 = lean_ctor_get(x_23, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_23);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_11);
x_30 = lean_ctor_get(x_15, 1);
lean_inc(x_30);
lean_dec(x_15);
x_31 = lean_ctor_get(x_9, 3);
lean_inc(x_31);
lean_dec(x_9);
x_32 = lean_ctor_get(x_2, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_2, 1);
lean_inc(x_33);
x_34 = 1;
x_35 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_35, 0, x_32);
lean_ctor_set(x_35, 1, x_33);
lean_ctor_set_uint8(x_35, sizeof(void*)*2, x_34);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_36 = l_Lean_Compiler_LCNF_Closure_collectLetValue(x_31, x_35, x_3, x_4, x_5, x_6, x_7, x_30);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; 
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
lean_dec(x_36);
x_1 = x_10;
x_8 = x_37;
goto _start;
}
else
{
uint8_t x_39; 
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_39 = !lean_is_exclusive(x_36);
if (x_39 == 0)
{
return x_36;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_36, 0);
x_41 = lean_ctor_get(x_36, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_36);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
}
else
{
uint8_t x_43; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_43 = !lean_is_exclusive(x_15);
if (x_43 == 0)
{
return x_15;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_15, 0);
x_45 = lean_ctor_get(x_15, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_15);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
case 3:
{
uint8_t x_47; 
x_47 = !lean_is_exclusive(x_1);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_48 = lean_ctor_get(x_1, 1);
x_49 = lean_ctor_get(x_1, 0);
lean_dec(x_49);
x_50 = lean_array_get_size(x_48);
x_51 = lean_unsigned_to_nat(0u);
x_52 = lean_nat_dec_lt(x_51, x_50);
if (x_52 == 0)
{
lean_object* x_53; 
lean_dec(x_50);
lean_dec(x_48);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_53 = lean_box(0);
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 1, x_8);
lean_ctor_set(x_1, 0, x_53);
return x_1;
}
else
{
uint8_t x_54; 
x_54 = lean_nat_dec_le(x_50, x_50);
if (x_54 == 0)
{
lean_object* x_55; 
lean_dec(x_50);
lean_dec(x_48);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_55 = lean_box(0);
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 1, x_8);
lean_ctor_set(x_1, 0, x_55);
return x_1;
}
else
{
size_t x_56; size_t x_57; lean_object* x_58; lean_object* x_59; 
lean_free_object(x_1);
x_56 = 0;
x_57 = lean_usize_of_nat(x_50);
lean_dec(x_50);
x_58 = lean_box(0);
x_59 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Closure_collectLetValue___spec__1(x_48, x_56, x_57, x_58, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_48);
return x_59;
}
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_60 = lean_ctor_get(x_1, 1);
lean_inc(x_60);
lean_dec(x_1);
x_61 = lean_array_get_size(x_60);
x_62 = lean_unsigned_to_nat(0u);
x_63 = lean_nat_dec_lt(x_62, x_61);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; 
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_64 = lean_box(0);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_8);
return x_65;
}
else
{
uint8_t x_66; 
x_66 = lean_nat_dec_le(x_61, x_61);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; 
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_67 = lean_box(0);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_8);
return x_68;
}
else
{
size_t x_69; size_t x_70; lean_object* x_71; lean_object* x_72; 
x_69 = 0;
x_70 = lean_usize_of_nat(x_61);
lean_dec(x_61);
x_71 = lean_box(0);
x_72 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Closure_collectLetValue___spec__1(x_60, x_69, x_70, x_71, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_60);
return x_72;
}
}
}
}
case 4:
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; lean_object* x_78; 
x_73 = lean_ctor_get(x_1, 0);
lean_inc(x_73);
lean_dec(x_1);
x_74 = lean_ctor_get(x_73, 1);
lean_inc(x_74);
x_75 = lean_alloc_closure((void*)(l_Lean_Expr_isFVar___boxed), 1, 0);
x_76 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Closure_collectType___lambda__1___boxed), 8, 0);
x_77 = 0;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_78 = l_Lean_ForEachExprWhere_visit___at_Lean_Compiler_LCNF_Closure_collectType___spec__1(x_75, x_76, x_74, x_77, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_78, 1);
lean_inc(x_79);
lean_dec(x_78);
x_80 = lean_ctor_get(x_73, 2);
lean_inc(x_80);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_81 = l_Lean_Compiler_LCNF_Closure_collectFVar(x_80, x_2, x_3, x_4, x_5, x_6, x_7, x_79);
if (lean_obj_tag(x_81) == 0)
{
uint8_t x_82; 
x_82 = !lean_is_exclusive(x_81);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; 
x_83 = lean_ctor_get(x_81, 1);
x_84 = lean_ctor_get(x_81, 0);
lean_dec(x_84);
x_85 = lean_ctor_get(x_73, 3);
lean_inc(x_85);
lean_dec(x_73);
x_86 = lean_array_get_size(x_85);
x_87 = lean_unsigned_to_nat(0u);
x_88 = lean_nat_dec_lt(x_87, x_86);
if (x_88 == 0)
{
lean_object* x_89; 
lean_dec(x_86);
lean_dec(x_85);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_89 = lean_box(0);
lean_ctor_set(x_81, 0, x_89);
return x_81;
}
else
{
uint8_t x_90; 
x_90 = lean_nat_dec_le(x_86, x_86);
if (x_90 == 0)
{
lean_object* x_91; 
lean_dec(x_86);
lean_dec(x_85);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_91 = lean_box(0);
lean_ctor_set(x_81, 0, x_91);
return x_81;
}
else
{
size_t x_92; size_t x_93; lean_object* x_94; lean_object* x_95; 
lean_free_object(x_81);
x_92 = 0;
x_93 = lean_usize_of_nat(x_86);
lean_dec(x_86);
x_94 = lean_box(0);
x_95 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Closure_collectCode___spec__1(x_85, x_92, x_93, x_94, x_2, x_3, x_4, x_5, x_6, x_7, x_83);
lean_dec(x_85);
return x_95;
}
}
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; uint8_t x_100; 
x_96 = lean_ctor_get(x_81, 1);
lean_inc(x_96);
lean_dec(x_81);
x_97 = lean_ctor_get(x_73, 3);
lean_inc(x_97);
lean_dec(x_73);
x_98 = lean_array_get_size(x_97);
x_99 = lean_unsigned_to_nat(0u);
x_100 = lean_nat_dec_lt(x_99, x_98);
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; 
lean_dec(x_98);
lean_dec(x_97);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_101 = lean_box(0);
x_102 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_96);
return x_102;
}
else
{
uint8_t x_103; 
x_103 = lean_nat_dec_le(x_98, x_98);
if (x_103 == 0)
{
lean_object* x_104; lean_object* x_105; 
lean_dec(x_98);
lean_dec(x_97);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_104 = lean_box(0);
x_105 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_96);
return x_105;
}
else
{
size_t x_106; size_t x_107; lean_object* x_108; lean_object* x_109; 
x_106 = 0;
x_107 = lean_usize_of_nat(x_98);
lean_dec(x_98);
x_108 = lean_box(0);
x_109 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Closure_collectCode___spec__1(x_97, x_106, x_107, x_108, x_2, x_3, x_4, x_5, x_6, x_7, x_96);
lean_dec(x_97);
return x_109;
}
}
}
}
else
{
uint8_t x_110; 
lean_dec(x_73);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_110 = !lean_is_exclusive(x_81);
if (x_110 == 0)
{
return x_81;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_ctor_get(x_81, 0);
x_112 = lean_ctor_get(x_81, 1);
lean_inc(x_112);
lean_inc(x_111);
lean_dec(x_81);
x_113 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_113, 0, x_111);
lean_ctor_set(x_113, 1, x_112);
return x_113;
}
}
}
else
{
uint8_t x_114; 
lean_dec(x_73);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_114 = !lean_is_exclusive(x_78);
if (x_114 == 0)
{
return x_78;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_115 = lean_ctor_get(x_78, 0);
x_116 = lean_ctor_get(x_78, 1);
lean_inc(x_116);
lean_inc(x_115);
lean_dec(x_78);
x_117 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_117, 0, x_115);
lean_ctor_set(x_117, 1, x_116);
return x_117;
}
}
}
case 5:
{
lean_object* x_118; lean_object* x_119; 
x_118 = lean_ctor_get(x_1, 0);
lean_inc(x_118);
lean_dec(x_1);
x_119 = l_Lean_Compiler_LCNF_Closure_collectFVar(x_118, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_119;
}
case 6:
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; uint8_t x_123; lean_object* x_124; 
x_120 = lean_ctor_get(x_1, 0);
lean_inc(x_120);
lean_dec(x_1);
x_121 = lean_alloc_closure((void*)(l_Lean_Expr_isFVar___boxed), 1, 0);
x_122 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Closure_collectType___lambda__1___boxed), 8, 0);
x_123 = 0;
x_124 = l_Lean_ForEachExprWhere_visit___at_Lean_Compiler_LCNF_Closure_collectType___spec__1(x_121, x_122, x_120, x_123, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_124;
}
default: 
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_125 = lean_ctor_get(x_1, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_1, 1);
lean_inc(x_126);
lean_dec(x_1);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_127 = l_Lean_Compiler_LCNF_Closure_collectFunDecl(x_125, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_127) == 0)
{
lean_object* x_128; 
x_128 = lean_ctor_get(x_127, 1);
lean_inc(x_128);
lean_dec(x_127);
x_1 = x_126;
x_8 = x_128;
goto _start;
}
else
{
uint8_t x_130; 
lean_dec(x_126);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_130 = !lean_is_exclusive(x_127);
if (x_130 == 0)
{
return x_127;
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_131 = lean_ctor_get(x_127, 0);
x_132 = lean_ctor_get(x_127, 1);
lean_inc(x_132);
lean_inc(x_131);
lean_dec(x_127);
x_133 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_133, 0, x_131);
lean_ctor_set(x_133, 1, x_132);
return x_133;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Closure_collectParams___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Closure_collectParams___spec__1(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Closure_collectParams___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_Closure_collectParams(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visited___at_Lean_Compiler_LCNF_Closure_collectType___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_ForEachExprWhere_visited___at_Lean_Compiler_LCNF_Closure_collectType___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_checked___at_Lean_Compiler_LCNF_Closure_collectType___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_ForEachExprWhere_checked___at_Lean_Compiler_LCNF_Closure_collectType___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visit_go___at_Lean_Compiler_LCNF_Closure_collectType___spec__2___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_4);
lean_dec(x_4);
x_15 = l_Lean_ForEachExprWhere_visit_go___at_Lean_Compiler_LCNF_Closure_collectType___spec__2___lambda__1(x_1, x_2, x_3, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_6);
lean_dec(x_5);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visit_go___at_Lean_Compiler_LCNF_Closure_collectType___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_3);
lean_dec(x_3);
x_14 = l_Lean_ForEachExprWhere_visit_go___at_Lean_Compiler_LCNF_Closure_collectType___spec__2(x_1, x_2, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_5);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visit___at_Lean_Compiler_LCNF_Closure_collectType___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_4);
lean_dec(x_4);
x_13 = l_Lean_ForEachExprWhere_visit___at_Lean_Compiler_LCNF_Closure_collectType___spec__1(x_1, x_2, x_3, x_12, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Closure_collectType___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_Closure_collectType___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Closure_collectLetValue___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Closure_collectLetValue___spec__1(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Closure_collectCode___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Closure_collectCode___spec__1(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_1);
return x_14;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Closure_run___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_array_mk(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Closure_run___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_LCNF_Closure_run___rarg___closed__1;
x_3 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 2, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Closure_run___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = 0;
x_10 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_10, 0, x_2);
lean_ctor_set(x_10, 1, x_3);
lean_ctor_set_uint8(x_10, sizeof(void*)*2, x_9);
x_11 = l_Lean_Compiler_LCNF_Closure_run___rarg___closed__2;
x_12 = lean_st_mk_ref(x_11, x_8);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
x_16 = lean_apply_7(x_1, x_10, x_14, x_4, x_5, x_6, x_7, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_st_ref_get(x_14, x_18);
lean_dec(x_14);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 2);
lean_inc(x_23);
lean_dec(x_21);
lean_ctor_set(x_12, 1, x_23);
lean_ctor_set(x_12, 0, x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_17);
lean_ctor_set(x_24, 1, x_12);
lean_ctor_set(x_19, 0, x_24);
return x_19;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_25 = lean_ctor_get(x_19, 0);
x_26 = lean_ctor_get(x_19, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_19);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
x_28 = lean_ctor_get(x_25, 2);
lean_inc(x_28);
lean_dec(x_25);
lean_ctor_set(x_12, 1, x_28);
lean_ctor_set(x_12, 0, x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_17);
lean_ctor_set(x_29, 1, x_12);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_26);
return x_30;
}
}
else
{
uint8_t x_31; 
lean_free_object(x_12);
lean_dec(x_14);
x_31 = !lean_is_exclusive(x_16);
if (x_31 == 0)
{
return x_16;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_16, 0);
x_33 = lean_ctor_get(x_16, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_16);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_12, 0);
x_36 = lean_ctor_get(x_12, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_12);
lean_inc(x_35);
x_37 = lean_apply_7(x_1, x_10, x_35, x_4, x_5, x_6, x_7, x_36);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = lean_st_ref_get(x_35, x_39);
lean_dec(x_35);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 x_43 = x_40;
} else {
 lean_dec_ref(x_40);
 x_43 = lean_box(0);
}
x_44 = lean_ctor_get(x_41, 1);
lean_inc(x_44);
x_45 = lean_ctor_get(x_41, 2);
lean_inc(x_45);
lean_dec(x_41);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_38);
lean_ctor_set(x_47, 1, x_46);
if (lean_is_scalar(x_43)) {
 x_48 = lean_alloc_ctor(0, 2, 0);
} else {
 x_48 = x_43;
}
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_42);
return x_48;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_dec(x_35);
x_49 = lean_ctor_get(x_37, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_37, 1);
lean_inc(x_50);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 x_51 = x_37;
} else {
 lean_dec_ref(x_37);
 x_51 = lean_box(0);
}
if (lean_is_scalar(x_51)) {
 x_52 = lean_alloc_ctor(1, 2, 0);
} else {
 x_52 = x_51;
}
lean_ctor_set(x_52, 0, x_49);
lean_ctor_set(x_52, 1, x_50);
return x_52;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Closure_run(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Closure_run___rarg), 8, 0);
return x_2;
}
}
lean_object* initialize_Lean_Util_ForEachExprWhere(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_CompilerM(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_LCNF_Closure(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Util_ForEachExprWhere(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_CompilerM(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Compiler_LCNF_Closure_collectType___closed__1 = _init_l_Lean_Compiler_LCNF_Closure_collectType___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_Closure_collectType___closed__1);
l_Lean_Compiler_LCNF_Closure_collectType___closed__2 = _init_l_Lean_Compiler_LCNF_Closure_collectType___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_Closure_collectType___closed__2);
l_panic___at_Lean_Compiler_LCNF_Closure_collectFVar___spec__1___closed__1 = _init_l_panic___at_Lean_Compiler_LCNF_Closure_collectFVar___spec__1___closed__1();
lean_mark_persistent(l_panic___at_Lean_Compiler_LCNF_Closure_collectFVar___spec__1___closed__1);
l_panic___at_Lean_Compiler_LCNF_Closure_collectFVar___spec__1___closed__2 = _init_l_panic___at_Lean_Compiler_LCNF_Closure_collectFVar___spec__1___closed__2();
lean_mark_persistent(l_panic___at_Lean_Compiler_LCNF_Closure_collectFVar___spec__1___closed__2);
l_panic___at_Lean_Compiler_LCNF_Closure_collectFVar___spec__1___closed__3 = _init_l_panic___at_Lean_Compiler_LCNF_Closure_collectFVar___spec__1___closed__3();
lean_mark_persistent(l_panic___at_Lean_Compiler_LCNF_Closure_collectFVar___spec__1___closed__3);
l_Lean_Compiler_LCNF_Closure_collectFVar___closed__1 = _init_l_Lean_Compiler_LCNF_Closure_collectFVar___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_Closure_collectFVar___closed__1);
l_Lean_Compiler_LCNF_Closure_collectFVar___closed__2 = _init_l_Lean_Compiler_LCNF_Closure_collectFVar___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_Closure_collectFVar___closed__2);
l_Lean_Compiler_LCNF_Closure_collectFVar___closed__3 = _init_l_Lean_Compiler_LCNF_Closure_collectFVar___closed__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_Closure_collectFVar___closed__3);
l_Lean_Compiler_LCNF_Closure_collectFVar___closed__4 = _init_l_Lean_Compiler_LCNF_Closure_collectFVar___closed__4();
lean_mark_persistent(l_Lean_Compiler_LCNF_Closure_collectFVar___closed__4);
l_Lean_Compiler_LCNF_Closure_run___rarg___closed__1 = _init_l_Lean_Compiler_LCNF_Closure_run___rarg___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_Closure_run___rarg___closed__1);
l_Lean_Compiler_LCNF_Closure_run___rarg___closed__2 = _init_l_Lean_Compiler_LCNF_Closure_run___rarg___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_Closure_run___rarg___closed__2);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
