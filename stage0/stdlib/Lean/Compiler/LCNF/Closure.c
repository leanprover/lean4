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
x_3 = lean_unsigned_to_nat(141u);
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
lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
lean_dec(x_44);
x_46 = lean_ctor_get(x_2, 1);
lean_inc(x_46);
lean_inc(x_37);
x_47 = lean_apply_1(x_46, x_37);
x_48 = lean_unbox(x_47);
lean_dec(x_47);
if (x_48 == 0)
{
lean_object* x_49; 
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_37);
lean_inc(x_3);
x_49 = l_Lean_Compiler_LCNF_Closure_collectLetValue(x_40, x_2, x_3, x_4, x_5, x_6, x_7, x_45);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_50 = lean_ctor_get(x_49, 1);
lean_inc(x_50);
lean_dec(x_49);
x_51 = lean_st_ref_take(x_3, x_50);
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
x_54 = !lean_is_exclusive(x_52);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_55 = lean_ctor_get(x_52, 2);
lean_ctor_set_tag(x_30, 0);
x_56 = lean_array_push(x_55, x_30);
lean_ctor_set(x_52, 2, x_56);
x_57 = lean_st_ref_set(x_3, x_52, x_53);
lean_dec(x_3);
x_58 = !lean_is_exclusive(x_57);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_ctor_get(x_57, 0);
lean_dec(x_59);
x_60 = lean_box(0);
lean_ctor_set(x_57, 0, x_60);
return x_57;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_57, 1);
lean_inc(x_61);
lean_dec(x_57);
x_62 = lean_box(0);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_61);
return x_63;
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_64 = lean_ctor_get(x_52, 0);
x_65 = lean_ctor_get(x_52, 1);
x_66 = lean_ctor_get(x_52, 2);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_52);
lean_ctor_set_tag(x_30, 0);
x_67 = lean_array_push(x_66, x_30);
x_68 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_68, 0, x_64);
lean_ctor_set(x_68, 1, x_65);
lean_ctor_set(x_68, 2, x_67);
x_69 = lean_st_ref_set(x_3, x_68, x_53);
lean_dec(x_3);
x_70 = lean_ctor_get(x_69, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_71 = x_69;
} else {
 lean_dec_ref(x_69);
 x_71 = lean_box(0);
}
x_72 = lean_box(0);
if (lean_is_scalar(x_71)) {
 x_73 = lean_alloc_ctor(0, 2, 0);
} else {
 x_73 = x_71;
}
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_70);
return x_73;
}
}
else
{
uint8_t x_74; 
lean_free_object(x_30);
lean_dec(x_35);
lean_dec(x_3);
x_74 = !lean_is_exclusive(x_49);
if (x_74 == 0)
{
return x_49;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_49, 0);
x_76 = lean_ctor_get(x_49, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_49);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
return x_77;
}
}
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; 
lean_dec(x_40);
lean_free_object(x_30);
lean_dec(x_35);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_78 = lean_st_ref_take(x_3, x_45);
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
lean_dec(x_78);
x_81 = !lean_is_exclusive(x_79);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; 
x_82 = lean_ctor_get(x_79, 1);
x_83 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_83, 0, x_37);
lean_ctor_set(x_83, 1, x_38);
lean_ctor_set(x_83, 2, x_39);
lean_ctor_set_uint8(x_83, sizeof(void*)*3, x_43);
x_84 = lean_array_push(x_82, x_83);
lean_ctor_set(x_79, 1, x_84);
x_85 = lean_st_ref_set(x_3, x_79, x_80);
lean_dec(x_3);
x_86 = !lean_is_exclusive(x_85);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; 
x_87 = lean_ctor_get(x_85, 0);
lean_dec(x_87);
x_88 = lean_box(0);
lean_ctor_set(x_85, 0, x_88);
return x_85;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_85, 1);
lean_inc(x_89);
lean_dec(x_85);
x_90 = lean_box(0);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_89);
return x_91;
}
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_92 = lean_ctor_get(x_79, 0);
x_93 = lean_ctor_get(x_79, 1);
x_94 = lean_ctor_get(x_79, 2);
lean_inc(x_94);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_79);
x_95 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_95, 0, x_37);
lean_ctor_set(x_95, 1, x_38);
lean_ctor_set(x_95, 2, x_39);
lean_ctor_set_uint8(x_95, sizeof(void*)*3, x_43);
x_96 = lean_array_push(x_93, x_95);
x_97 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_97, 0, x_92);
lean_ctor_set(x_97, 1, x_96);
lean_ctor_set(x_97, 2, x_94);
x_98 = lean_st_ref_set(x_3, x_97, x_80);
lean_dec(x_3);
x_99 = lean_ctor_get(x_98, 1);
lean_inc(x_99);
if (lean_is_exclusive(x_98)) {
 lean_ctor_release(x_98, 0);
 lean_ctor_release(x_98, 1);
 x_100 = x_98;
} else {
 lean_dec_ref(x_98);
 x_100 = lean_box(0);
}
x_101 = lean_box(0);
if (lean_is_scalar(x_100)) {
 x_102 = lean_alloc_ctor(0, 2, 0);
} else {
 x_102 = x_100;
}
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_99);
return x_102;
}
}
}
else
{
uint8_t x_103; 
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
x_103 = !lean_is_exclusive(x_44);
if (x_103 == 0)
{
return x_44;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_104 = lean_ctor_get(x_44, 0);
x_105 = lean_ctor_get(x_44, 1);
lean_inc(x_105);
lean_inc(x_104);
lean_dec(x_44);
x_106 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_106, 0, x_104);
lean_ctor_set(x_106, 1, x_105);
return x_106;
}
}
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; uint8_t x_115; lean_object* x_116; 
x_107 = lean_ctor_get(x_30, 0);
lean_inc(x_107);
lean_dec(x_30);
x_108 = lean_ctor_get(x_29, 1);
lean_inc(x_108);
lean_dec(x_29);
x_109 = lean_ctor_get(x_107, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_107, 1);
lean_inc(x_110);
x_111 = lean_ctor_get(x_107, 2);
lean_inc(x_111);
x_112 = lean_ctor_get(x_107, 3);
lean_inc(x_112);
x_113 = lean_alloc_closure((void*)(l_Lean_Expr_isFVar___boxed), 1, 0);
x_114 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Closure_collectType___lambda__1___boxed), 8, 0);
x_115 = 0;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_111);
x_116 = l_Lean_ForEachExprWhere_visit___at_Lean_Compiler_LCNF_Closure_collectType___spec__1(x_113, x_114, x_111, x_115, x_2, x_3, x_4, x_5, x_6, x_7, x_108);
if (lean_obj_tag(x_116) == 0)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; uint8_t x_120; 
x_117 = lean_ctor_get(x_116, 1);
lean_inc(x_117);
lean_dec(x_116);
x_118 = lean_ctor_get(x_2, 1);
lean_inc(x_118);
lean_inc(x_109);
x_119 = lean_apply_1(x_118, x_109);
x_120 = lean_unbox(x_119);
lean_dec(x_119);
if (x_120 == 0)
{
lean_object* x_121; 
lean_dec(x_111);
lean_dec(x_110);
lean_dec(x_109);
lean_inc(x_3);
x_121 = l_Lean_Compiler_LCNF_Closure_collectLetValue(x_112, x_2, x_3, x_4, x_5, x_6, x_7, x_117);
if (lean_obj_tag(x_121) == 0)
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_122 = lean_ctor_get(x_121, 1);
lean_inc(x_122);
lean_dec(x_121);
x_123 = lean_st_ref_take(x_3, x_122);
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_123, 1);
lean_inc(x_125);
lean_dec(x_123);
x_126 = lean_ctor_get(x_124, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_124, 1);
lean_inc(x_127);
x_128 = lean_ctor_get(x_124, 2);
lean_inc(x_128);
if (lean_is_exclusive(x_124)) {
 lean_ctor_release(x_124, 0);
 lean_ctor_release(x_124, 1);
 lean_ctor_release(x_124, 2);
 x_129 = x_124;
} else {
 lean_dec_ref(x_124);
 x_129 = lean_box(0);
}
x_130 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_130, 0, x_107);
x_131 = lean_array_push(x_128, x_130);
if (lean_is_scalar(x_129)) {
 x_132 = lean_alloc_ctor(0, 3, 0);
} else {
 x_132 = x_129;
}
lean_ctor_set(x_132, 0, x_126);
lean_ctor_set(x_132, 1, x_127);
lean_ctor_set(x_132, 2, x_131);
x_133 = lean_st_ref_set(x_3, x_132, x_125);
lean_dec(x_3);
x_134 = lean_ctor_get(x_133, 1);
lean_inc(x_134);
if (lean_is_exclusive(x_133)) {
 lean_ctor_release(x_133, 0);
 lean_ctor_release(x_133, 1);
 x_135 = x_133;
} else {
 lean_dec_ref(x_133);
 x_135 = lean_box(0);
}
x_136 = lean_box(0);
if (lean_is_scalar(x_135)) {
 x_137 = lean_alloc_ctor(0, 2, 0);
} else {
 x_137 = x_135;
}
lean_ctor_set(x_137, 0, x_136);
lean_ctor_set(x_137, 1, x_134);
return x_137;
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
lean_dec(x_107);
lean_dec(x_3);
x_138 = lean_ctor_get(x_121, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_121, 1);
lean_inc(x_139);
if (lean_is_exclusive(x_121)) {
 lean_ctor_release(x_121, 0);
 lean_ctor_release(x_121, 1);
 x_140 = x_121;
} else {
 lean_dec_ref(x_121);
 x_140 = lean_box(0);
}
if (lean_is_scalar(x_140)) {
 x_141 = lean_alloc_ctor(1, 2, 0);
} else {
 x_141 = x_140;
}
lean_ctor_set(x_141, 0, x_138);
lean_ctor_set(x_141, 1, x_139);
return x_141;
}
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
lean_dec(x_112);
lean_dec(x_107);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_142 = lean_st_ref_take(x_3, x_117);
x_143 = lean_ctor_get(x_142, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_142, 1);
lean_inc(x_144);
lean_dec(x_142);
x_145 = lean_ctor_get(x_143, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_143, 1);
lean_inc(x_146);
x_147 = lean_ctor_get(x_143, 2);
lean_inc(x_147);
if (lean_is_exclusive(x_143)) {
 lean_ctor_release(x_143, 0);
 lean_ctor_release(x_143, 1);
 lean_ctor_release(x_143, 2);
 x_148 = x_143;
} else {
 lean_dec_ref(x_143);
 x_148 = lean_box(0);
}
x_149 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_149, 0, x_109);
lean_ctor_set(x_149, 1, x_110);
lean_ctor_set(x_149, 2, x_111);
lean_ctor_set_uint8(x_149, sizeof(void*)*3, x_115);
x_150 = lean_array_push(x_146, x_149);
if (lean_is_scalar(x_148)) {
 x_151 = lean_alloc_ctor(0, 3, 0);
} else {
 x_151 = x_148;
}
lean_ctor_set(x_151, 0, x_145);
lean_ctor_set(x_151, 1, x_150);
lean_ctor_set(x_151, 2, x_147);
x_152 = lean_st_ref_set(x_3, x_151, x_144);
lean_dec(x_3);
x_153 = lean_ctor_get(x_152, 1);
lean_inc(x_153);
if (lean_is_exclusive(x_152)) {
 lean_ctor_release(x_152, 0);
 lean_ctor_release(x_152, 1);
 x_154 = x_152;
} else {
 lean_dec_ref(x_152);
 x_154 = lean_box(0);
}
x_155 = lean_box(0);
if (lean_is_scalar(x_154)) {
 x_156 = lean_alloc_ctor(0, 2, 0);
} else {
 x_156 = x_154;
}
lean_ctor_set(x_156, 0, x_155);
lean_ctor_set(x_156, 1, x_153);
return x_156;
}
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
lean_dec(x_112);
lean_dec(x_111);
lean_dec(x_110);
lean_dec(x_109);
lean_dec(x_107);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_157 = lean_ctor_get(x_116, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_116, 1);
lean_inc(x_158);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 lean_ctor_release(x_116, 1);
 x_159 = x_116;
} else {
 lean_dec_ref(x_116);
 x_159 = lean_box(0);
}
if (lean_is_scalar(x_159)) {
 x_160 = lean_alloc_ctor(1, 2, 0);
} else {
 x_160 = x_159;
}
lean_ctor_set(x_160, 0, x_157);
lean_ctor_set(x_160, 1, x_158);
return x_160;
}
}
}
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; uint8_t x_166; lean_object* x_167; 
lean_dec(x_1);
x_161 = lean_ctor_get(x_26, 1);
lean_inc(x_161);
lean_dec(x_26);
x_162 = lean_ctor_get(x_27, 0);
lean_inc(x_162);
lean_dec(x_27);
x_163 = lean_ctor_get(x_162, 2);
lean_inc(x_163);
x_164 = lean_alloc_closure((void*)(l_Lean_Expr_isFVar___boxed), 1, 0);
x_165 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Closure_collectType___lambda__1___boxed), 8, 0);
x_166 = 0;
lean_inc(x_3);
x_167 = l_Lean_ForEachExprWhere_visit___at_Lean_Compiler_LCNF_Closure_collectType___spec__1(x_164, x_165, x_163, x_166, x_2, x_3, x_4, x_5, x_6, x_7, x_161);
if (lean_obj_tag(x_167) == 0)
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; uint8_t x_172; 
x_168 = lean_ctor_get(x_167, 1);
lean_inc(x_168);
lean_dec(x_167);
x_169 = lean_st_ref_take(x_3, x_168);
x_170 = lean_ctor_get(x_169, 0);
lean_inc(x_170);
x_171 = lean_ctor_get(x_169, 1);
lean_inc(x_171);
lean_dec(x_169);
x_172 = !lean_is_exclusive(x_170);
if (x_172 == 0)
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; uint8_t x_176; 
x_173 = lean_ctor_get(x_170, 1);
x_174 = lean_array_push(x_173, x_162);
lean_ctor_set(x_170, 1, x_174);
x_175 = lean_st_ref_set(x_3, x_170, x_171);
lean_dec(x_3);
x_176 = !lean_is_exclusive(x_175);
if (x_176 == 0)
{
lean_object* x_177; lean_object* x_178; 
x_177 = lean_ctor_get(x_175, 0);
lean_dec(x_177);
x_178 = lean_box(0);
lean_ctor_set(x_175, 0, x_178);
return x_175;
}
else
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_179 = lean_ctor_get(x_175, 1);
lean_inc(x_179);
lean_dec(x_175);
x_180 = lean_box(0);
x_181 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_181, 0, x_180);
lean_ctor_set(x_181, 1, x_179);
return x_181;
}
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; 
x_182 = lean_ctor_get(x_170, 0);
x_183 = lean_ctor_get(x_170, 1);
x_184 = lean_ctor_get(x_170, 2);
lean_inc(x_184);
lean_inc(x_183);
lean_inc(x_182);
lean_dec(x_170);
x_185 = lean_array_push(x_183, x_162);
x_186 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_186, 0, x_182);
lean_ctor_set(x_186, 1, x_185);
lean_ctor_set(x_186, 2, x_184);
x_187 = lean_st_ref_set(x_3, x_186, x_171);
lean_dec(x_3);
x_188 = lean_ctor_get(x_187, 1);
lean_inc(x_188);
if (lean_is_exclusive(x_187)) {
 lean_ctor_release(x_187, 0);
 lean_ctor_release(x_187, 1);
 x_189 = x_187;
} else {
 lean_dec_ref(x_187);
 x_189 = lean_box(0);
}
x_190 = lean_box(0);
if (lean_is_scalar(x_189)) {
 x_191 = lean_alloc_ctor(0, 2, 0);
} else {
 x_191 = x_189;
}
lean_ctor_set(x_191, 0, x_190);
lean_ctor_set(x_191, 1, x_188);
return x_191;
}
}
else
{
uint8_t x_192; 
lean_dec(x_162);
lean_dec(x_3);
x_192 = !lean_is_exclusive(x_167);
if (x_192 == 0)
{
return x_167;
}
else
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; 
x_193 = lean_ctor_get(x_167, 0);
x_194 = lean_ctor_get(x_167, 1);
lean_inc(x_194);
lean_inc(x_193);
lean_dec(x_167);
x_195 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_195, 0, x_193);
lean_ctor_set(x_195, 1, x_194);
return x_195;
}
}
}
}
else
{
uint8_t x_196; 
lean_dec(x_1);
x_196 = !lean_is_exclusive(x_24);
if (x_196 == 0)
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; uint8_t x_204; 
x_197 = lean_ctor_get(x_24, 0);
x_198 = lean_ctor_get(x_23, 1);
lean_inc(x_198);
lean_dec(x_23);
x_199 = lean_ctor_get(x_2, 1);
lean_inc(x_199);
x_200 = lean_ctor_get(x_197, 0);
lean_inc(x_200);
x_201 = lean_ctor_get(x_197, 1);
lean_inc(x_201);
x_202 = lean_ctor_get(x_197, 3);
lean_inc(x_202);
lean_inc(x_200);
x_203 = lean_apply_1(x_199, x_200);
x_204 = lean_unbox(x_203);
lean_dec(x_203);
if (x_204 == 0)
{
lean_object* x_205; 
lean_dec(x_202);
lean_dec(x_201);
lean_dec(x_200);
lean_inc(x_3);
lean_inc(x_197);
x_205 = l_Lean_Compiler_LCNF_Closure_collectFunDecl(x_197, x_2, x_3, x_4, x_5, x_6, x_7, x_198);
if (lean_obj_tag(x_205) == 0)
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; uint8_t x_210; 
x_206 = lean_ctor_get(x_205, 1);
lean_inc(x_206);
lean_dec(x_205);
x_207 = lean_st_ref_take(x_3, x_206);
x_208 = lean_ctor_get(x_207, 0);
lean_inc(x_208);
x_209 = lean_ctor_get(x_207, 1);
lean_inc(x_209);
lean_dec(x_207);
x_210 = !lean_is_exclusive(x_208);
if (x_210 == 0)
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; uint8_t x_214; 
x_211 = lean_ctor_get(x_208, 2);
x_212 = lean_array_push(x_211, x_24);
lean_ctor_set(x_208, 2, x_212);
x_213 = lean_st_ref_set(x_3, x_208, x_209);
lean_dec(x_3);
x_214 = !lean_is_exclusive(x_213);
if (x_214 == 0)
{
lean_object* x_215; lean_object* x_216; 
x_215 = lean_ctor_get(x_213, 0);
lean_dec(x_215);
x_216 = lean_box(0);
lean_ctor_set(x_213, 0, x_216);
return x_213;
}
else
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; 
x_217 = lean_ctor_get(x_213, 1);
lean_inc(x_217);
lean_dec(x_213);
x_218 = lean_box(0);
x_219 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_219, 0, x_218);
lean_ctor_set(x_219, 1, x_217);
return x_219;
}
}
else
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; 
x_220 = lean_ctor_get(x_208, 0);
x_221 = lean_ctor_get(x_208, 1);
x_222 = lean_ctor_get(x_208, 2);
lean_inc(x_222);
lean_inc(x_221);
lean_inc(x_220);
lean_dec(x_208);
x_223 = lean_array_push(x_222, x_24);
x_224 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_224, 0, x_220);
lean_ctor_set(x_224, 1, x_221);
lean_ctor_set(x_224, 2, x_223);
x_225 = lean_st_ref_set(x_3, x_224, x_209);
lean_dec(x_3);
x_226 = lean_ctor_get(x_225, 1);
lean_inc(x_226);
if (lean_is_exclusive(x_225)) {
 lean_ctor_release(x_225, 0);
 lean_ctor_release(x_225, 1);
 x_227 = x_225;
} else {
 lean_dec_ref(x_225);
 x_227 = lean_box(0);
}
x_228 = lean_box(0);
if (lean_is_scalar(x_227)) {
 x_229 = lean_alloc_ctor(0, 2, 0);
} else {
 x_229 = x_227;
}
lean_ctor_set(x_229, 0, x_228);
lean_ctor_set(x_229, 1, x_226);
return x_229;
}
}
else
{
uint8_t x_230; 
lean_free_object(x_24);
lean_dec(x_197);
lean_dec(x_3);
x_230 = !lean_is_exclusive(x_205);
if (x_230 == 0)
{
return x_205;
}
else
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; 
x_231 = lean_ctor_get(x_205, 0);
x_232 = lean_ctor_get(x_205, 1);
lean_inc(x_232);
lean_inc(x_231);
lean_dec(x_205);
x_233 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_233, 0, x_231);
lean_ctor_set(x_233, 1, x_232);
return x_233;
}
}
}
else
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; uint8_t x_237; 
lean_free_object(x_24);
lean_dec(x_197);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_234 = lean_st_ref_take(x_3, x_198);
x_235 = lean_ctor_get(x_234, 0);
lean_inc(x_235);
x_236 = lean_ctor_get(x_234, 1);
lean_inc(x_236);
lean_dec(x_234);
x_237 = !lean_is_exclusive(x_235);
if (x_237 == 0)
{
lean_object* x_238; uint8_t x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; uint8_t x_243; 
x_238 = lean_ctor_get(x_235, 1);
x_239 = 0;
x_240 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_240, 0, x_200);
lean_ctor_set(x_240, 1, x_201);
lean_ctor_set(x_240, 2, x_202);
lean_ctor_set_uint8(x_240, sizeof(void*)*3, x_239);
x_241 = lean_array_push(x_238, x_240);
lean_ctor_set(x_235, 1, x_241);
x_242 = lean_st_ref_set(x_3, x_235, x_236);
lean_dec(x_3);
x_243 = !lean_is_exclusive(x_242);
if (x_243 == 0)
{
lean_object* x_244; lean_object* x_245; 
x_244 = lean_ctor_get(x_242, 0);
lean_dec(x_244);
x_245 = lean_box(0);
lean_ctor_set(x_242, 0, x_245);
return x_242;
}
else
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; 
x_246 = lean_ctor_get(x_242, 1);
lean_inc(x_246);
lean_dec(x_242);
x_247 = lean_box(0);
x_248 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_248, 0, x_247);
lean_ctor_set(x_248, 1, x_246);
return x_248;
}
}
else
{
lean_object* x_249; lean_object* x_250; lean_object* x_251; uint8_t x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; 
x_249 = lean_ctor_get(x_235, 0);
x_250 = lean_ctor_get(x_235, 1);
x_251 = lean_ctor_get(x_235, 2);
lean_inc(x_251);
lean_inc(x_250);
lean_inc(x_249);
lean_dec(x_235);
x_252 = 0;
x_253 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_253, 0, x_200);
lean_ctor_set(x_253, 1, x_201);
lean_ctor_set(x_253, 2, x_202);
lean_ctor_set_uint8(x_253, sizeof(void*)*3, x_252);
x_254 = lean_array_push(x_250, x_253);
x_255 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_255, 0, x_249);
lean_ctor_set(x_255, 1, x_254);
lean_ctor_set(x_255, 2, x_251);
x_256 = lean_st_ref_set(x_3, x_255, x_236);
lean_dec(x_3);
x_257 = lean_ctor_get(x_256, 1);
lean_inc(x_257);
if (lean_is_exclusive(x_256)) {
 lean_ctor_release(x_256, 0);
 lean_ctor_release(x_256, 1);
 x_258 = x_256;
} else {
 lean_dec_ref(x_256);
 x_258 = lean_box(0);
}
x_259 = lean_box(0);
if (lean_is_scalar(x_258)) {
 x_260 = lean_alloc_ctor(0, 2, 0);
} else {
 x_260 = x_258;
}
lean_ctor_set(x_260, 0, x_259);
lean_ctor_set(x_260, 1, x_257);
return x_260;
}
}
}
else
{
lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; uint8_t x_268; 
x_261 = lean_ctor_get(x_24, 0);
lean_inc(x_261);
lean_dec(x_24);
x_262 = lean_ctor_get(x_23, 1);
lean_inc(x_262);
lean_dec(x_23);
x_263 = lean_ctor_get(x_2, 1);
lean_inc(x_263);
x_264 = lean_ctor_get(x_261, 0);
lean_inc(x_264);
x_265 = lean_ctor_get(x_261, 1);
lean_inc(x_265);
x_266 = lean_ctor_get(x_261, 3);
lean_inc(x_266);
lean_inc(x_264);
x_267 = lean_apply_1(x_263, x_264);
x_268 = lean_unbox(x_267);
lean_dec(x_267);
if (x_268 == 0)
{
lean_object* x_269; 
lean_dec(x_266);
lean_dec(x_265);
lean_dec(x_264);
lean_inc(x_3);
lean_inc(x_261);
x_269 = l_Lean_Compiler_LCNF_Closure_collectFunDecl(x_261, x_2, x_3, x_4, x_5, x_6, x_7, x_262);
if (lean_obj_tag(x_269) == 0)
{
lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; 
x_270 = lean_ctor_get(x_269, 1);
lean_inc(x_270);
lean_dec(x_269);
x_271 = lean_st_ref_take(x_3, x_270);
x_272 = lean_ctor_get(x_271, 0);
lean_inc(x_272);
x_273 = lean_ctor_get(x_271, 1);
lean_inc(x_273);
lean_dec(x_271);
x_274 = lean_ctor_get(x_272, 0);
lean_inc(x_274);
x_275 = lean_ctor_get(x_272, 1);
lean_inc(x_275);
x_276 = lean_ctor_get(x_272, 2);
lean_inc(x_276);
if (lean_is_exclusive(x_272)) {
 lean_ctor_release(x_272, 0);
 lean_ctor_release(x_272, 1);
 lean_ctor_release(x_272, 2);
 x_277 = x_272;
} else {
 lean_dec_ref(x_272);
 x_277 = lean_box(0);
}
x_278 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_278, 0, x_261);
x_279 = lean_array_push(x_276, x_278);
if (lean_is_scalar(x_277)) {
 x_280 = lean_alloc_ctor(0, 3, 0);
} else {
 x_280 = x_277;
}
lean_ctor_set(x_280, 0, x_274);
lean_ctor_set(x_280, 1, x_275);
lean_ctor_set(x_280, 2, x_279);
x_281 = lean_st_ref_set(x_3, x_280, x_273);
lean_dec(x_3);
x_282 = lean_ctor_get(x_281, 1);
lean_inc(x_282);
if (lean_is_exclusive(x_281)) {
 lean_ctor_release(x_281, 0);
 lean_ctor_release(x_281, 1);
 x_283 = x_281;
} else {
 lean_dec_ref(x_281);
 x_283 = lean_box(0);
}
x_284 = lean_box(0);
if (lean_is_scalar(x_283)) {
 x_285 = lean_alloc_ctor(0, 2, 0);
} else {
 x_285 = x_283;
}
lean_ctor_set(x_285, 0, x_284);
lean_ctor_set(x_285, 1, x_282);
return x_285;
}
else
{
lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; 
lean_dec(x_261);
lean_dec(x_3);
x_286 = lean_ctor_get(x_269, 0);
lean_inc(x_286);
x_287 = lean_ctor_get(x_269, 1);
lean_inc(x_287);
if (lean_is_exclusive(x_269)) {
 lean_ctor_release(x_269, 0);
 lean_ctor_release(x_269, 1);
 x_288 = x_269;
} else {
 lean_dec_ref(x_269);
 x_288 = lean_box(0);
}
if (lean_is_scalar(x_288)) {
 x_289 = lean_alloc_ctor(1, 2, 0);
} else {
 x_289 = x_288;
}
lean_ctor_set(x_289, 0, x_286);
lean_ctor_set(x_289, 1, x_287);
return x_289;
}
}
else
{
lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; uint8_t x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; 
lean_dec(x_261);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_290 = lean_st_ref_take(x_3, x_262);
x_291 = lean_ctor_get(x_290, 0);
lean_inc(x_291);
x_292 = lean_ctor_get(x_290, 1);
lean_inc(x_292);
lean_dec(x_290);
x_293 = lean_ctor_get(x_291, 0);
lean_inc(x_293);
x_294 = lean_ctor_get(x_291, 1);
lean_inc(x_294);
x_295 = lean_ctor_get(x_291, 2);
lean_inc(x_295);
if (lean_is_exclusive(x_291)) {
 lean_ctor_release(x_291, 0);
 lean_ctor_release(x_291, 1);
 lean_ctor_release(x_291, 2);
 x_296 = x_291;
} else {
 lean_dec_ref(x_291);
 x_296 = lean_box(0);
}
x_297 = 0;
x_298 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_298, 0, x_264);
lean_ctor_set(x_298, 1, x_265);
lean_ctor_set(x_298, 2, x_266);
lean_ctor_set_uint8(x_298, sizeof(void*)*3, x_297);
x_299 = lean_array_push(x_294, x_298);
if (lean_is_scalar(x_296)) {
 x_300 = lean_alloc_ctor(0, 3, 0);
} else {
 x_300 = x_296;
}
lean_ctor_set(x_300, 0, x_293);
lean_ctor_set(x_300, 1, x_299);
lean_ctor_set(x_300, 2, x_295);
x_301 = lean_st_ref_set(x_3, x_300, x_292);
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
}
}
else
{
lean_object* x_306; lean_object* x_307; lean_object* x_308; uint8_t x_309; 
x_306 = lean_ctor_get(x_15, 1);
lean_inc(x_306);
lean_dec(x_15);
x_307 = lean_ctor_get(x_2, 0);
lean_inc(x_307);
lean_inc(x_1);
x_308 = lean_apply_1(x_307, x_1);
x_309 = lean_unbox(x_308);
lean_dec(x_308);
if (x_309 == 0)
{
lean_object* x_310; lean_object* x_311; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_310 = lean_box(0);
x_311 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_311, 0, x_310);
lean_ctor_set(x_311, 1, x_306);
return x_311;
}
else
{
lean_object* x_312; lean_object* x_313; 
x_312 = l_Lean_Compiler_LCNF_findFunDecl_x3f(x_1, x_4, x_5, x_6, x_7, x_306);
x_313 = lean_ctor_get(x_312, 0);
lean_inc(x_313);
if (lean_obj_tag(x_313) == 0)
{
lean_object* x_314; lean_object* x_315; lean_object* x_316; 
x_314 = lean_ctor_get(x_312, 1);
lean_inc(x_314);
lean_dec(x_312);
x_315 = l_Lean_Compiler_LCNF_findParam_x3f(x_1, x_4, x_5, x_6, x_7, x_314);
x_316 = lean_ctor_get(x_315, 0);
lean_inc(x_316);
if (lean_obj_tag(x_316) == 0)
{
lean_object* x_317; lean_object* x_318; lean_object* x_319; 
x_317 = lean_ctor_get(x_315, 1);
lean_inc(x_317);
lean_dec(x_315);
x_318 = l_Lean_Compiler_LCNF_findLetDecl_x3f(x_1, x_4, x_5, x_6, x_7, x_317);
lean_dec(x_1);
x_319 = lean_ctor_get(x_318, 0);
lean_inc(x_319);
if (lean_obj_tag(x_319) == 0)
{
lean_object* x_320; lean_object* x_321; lean_object* x_322; 
x_320 = lean_ctor_get(x_318, 1);
lean_inc(x_320);
lean_dec(x_318);
x_321 = l_Lean_Compiler_LCNF_Closure_collectFVar___closed__4;
x_322 = l_panic___at_Lean_Compiler_LCNF_Closure_collectFVar___spec__1(x_321, x_2, x_3, x_4, x_5, x_6, x_7, x_320);
return x_322;
}
else
{
lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; uint8_t x_332; lean_object* x_333; 
x_323 = lean_ctor_get(x_319, 0);
lean_inc(x_323);
if (lean_is_exclusive(x_319)) {
 lean_ctor_release(x_319, 0);
 x_324 = x_319;
} else {
 lean_dec_ref(x_319);
 x_324 = lean_box(0);
}
x_325 = lean_ctor_get(x_318, 1);
lean_inc(x_325);
lean_dec(x_318);
x_326 = lean_ctor_get(x_323, 0);
lean_inc(x_326);
x_327 = lean_ctor_get(x_323, 1);
lean_inc(x_327);
x_328 = lean_ctor_get(x_323, 2);
lean_inc(x_328);
x_329 = lean_ctor_get(x_323, 3);
lean_inc(x_329);
x_330 = lean_alloc_closure((void*)(l_Lean_Expr_isFVar___boxed), 1, 0);
x_331 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Closure_collectType___lambda__1___boxed), 8, 0);
x_332 = 0;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_328);
x_333 = l_Lean_ForEachExprWhere_visit___at_Lean_Compiler_LCNF_Closure_collectType___spec__1(x_330, x_331, x_328, x_332, x_2, x_3, x_4, x_5, x_6, x_7, x_325);
if (lean_obj_tag(x_333) == 0)
{
lean_object* x_334; lean_object* x_335; lean_object* x_336; uint8_t x_337; 
x_334 = lean_ctor_get(x_333, 1);
lean_inc(x_334);
lean_dec(x_333);
x_335 = lean_ctor_get(x_2, 1);
lean_inc(x_335);
lean_inc(x_326);
x_336 = lean_apply_1(x_335, x_326);
x_337 = lean_unbox(x_336);
lean_dec(x_336);
if (x_337 == 0)
{
lean_object* x_338; 
lean_dec(x_328);
lean_dec(x_327);
lean_dec(x_326);
lean_inc(x_3);
x_338 = l_Lean_Compiler_LCNF_Closure_collectLetValue(x_329, x_2, x_3, x_4, x_5, x_6, x_7, x_334);
if (lean_obj_tag(x_338) == 0)
{
lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; 
x_339 = lean_ctor_get(x_338, 1);
lean_inc(x_339);
lean_dec(x_338);
x_340 = lean_st_ref_take(x_3, x_339);
x_341 = lean_ctor_get(x_340, 0);
lean_inc(x_341);
x_342 = lean_ctor_get(x_340, 1);
lean_inc(x_342);
lean_dec(x_340);
x_343 = lean_ctor_get(x_341, 0);
lean_inc(x_343);
x_344 = lean_ctor_get(x_341, 1);
lean_inc(x_344);
x_345 = lean_ctor_get(x_341, 2);
lean_inc(x_345);
if (lean_is_exclusive(x_341)) {
 lean_ctor_release(x_341, 0);
 lean_ctor_release(x_341, 1);
 lean_ctor_release(x_341, 2);
 x_346 = x_341;
} else {
 lean_dec_ref(x_341);
 x_346 = lean_box(0);
}
if (lean_is_scalar(x_324)) {
 x_347 = lean_alloc_ctor(0, 1, 0);
} else {
 x_347 = x_324;
 lean_ctor_set_tag(x_347, 0);
}
lean_ctor_set(x_347, 0, x_323);
x_348 = lean_array_push(x_345, x_347);
if (lean_is_scalar(x_346)) {
 x_349 = lean_alloc_ctor(0, 3, 0);
} else {
 x_349 = x_346;
}
lean_ctor_set(x_349, 0, x_343);
lean_ctor_set(x_349, 1, x_344);
lean_ctor_set(x_349, 2, x_348);
x_350 = lean_st_ref_set(x_3, x_349, x_342);
lean_dec(x_3);
x_351 = lean_ctor_get(x_350, 1);
lean_inc(x_351);
if (lean_is_exclusive(x_350)) {
 lean_ctor_release(x_350, 0);
 lean_ctor_release(x_350, 1);
 x_352 = x_350;
} else {
 lean_dec_ref(x_350);
 x_352 = lean_box(0);
}
x_353 = lean_box(0);
if (lean_is_scalar(x_352)) {
 x_354 = lean_alloc_ctor(0, 2, 0);
} else {
 x_354 = x_352;
}
lean_ctor_set(x_354, 0, x_353);
lean_ctor_set(x_354, 1, x_351);
return x_354;
}
else
{
lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; 
lean_dec(x_324);
lean_dec(x_323);
lean_dec(x_3);
x_355 = lean_ctor_get(x_338, 0);
lean_inc(x_355);
x_356 = lean_ctor_get(x_338, 1);
lean_inc(x_356);
if (lean_is_exclusive(x_338)) {
 lean_ctor_release(x_338, 0);
 lean_ctor_release(x_338, 1);
 x_357 = x_338;
} else {
 lean_dec_ref(x_338);
 x_357 = lean_box(0);
}
if (lean_is_scalar(x_357)) {
 x_358 = lean_alloc_ctor(1, 2, 0);
} else {
 x_358 = x_357;
}
lean_ctor_set(x_358, 0, x_355);
lean_ctor_set(x_358, 1, x_356);
return x_358;
}
}
else
{
lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; 
lean_dec(x_329);
lean_dec(x_324);
lean_dec(x_323);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_359 = lean_st_ref_take(x_3, x_334);
x_360 = lean_ctor_get(x_359, 0);
lean_inc(x_360);
x_361 = lean_ctor_get(x_359, 1);
lean_inc(x_361);
lean_dec(x_359);
x_362 = lean_ctor_get(x_360, 0);
lean_inc(x_362);
x_363 = lean_ctor_get(x_360, 1);
lean_inc(x_363);
x_364 = lean_ctor_get(x_360, 2);
lean_inc(x_364);
if (lean_is_exclusive(x_360)) {
 lean_ctor_release(x_360, 0);
 lean_ctor_release(x_360, 1);
 lean_ctor_release(x_360, 2);
 x_365 = x_360;
} else {
 lean_dec_ref(x_360);
 x_365 = lean_box(0);
}
x_366 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_366, 0, x_326);
lean_ctor_set(x_366, 1, x_327);
lean_ctor_set(x_366, 2, x_328);
lean_ctor_set_uint8(x_366, sizeof(void*)*3, x_332);
x_367 = lean_array_push(x_363, x_366);
if (lean_is_scalar(x_365)) {
 x_368 = lean_alloc_ctor(0, 3, 0);
} else {
 x_368 = x_365;
}
lean_ctor_set(x_368, 0, x_362);
lean_ctor_set(x_368, 1, x_367);
lean_ctor_set(x_368, 2, x_364);
x_369 = lean_st_ref_set(x_3, x_368, x_361);
lean_dec(x_3);
x_370 = lean_ctor_get(x_369, 1);
lean_inc(x_370);
if (lean_is_exclusive(x_369)) {
 lean_ctor_release(x_369, 0);
 lean_ctor_release(x_369, 1);
 x_371 = x_369;
} else {
 lean_dec_ref(x_369);
 x_371 = lean_box(0);
}
x_372 = lean_box(0);
if (lean_is_scalar(x_371)) {
 x_373 = lean_alloc_ctor(0, 2, 0);
} else {
 x_373 = x_371;
}
lean_ctor_set(x_373, 0, x_372);
lean_ctor_set(x_373, 1, x_370);
return x_373;
}
}
else
{
lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; 
lean_dec(x_329);
lean_dec(x_328);
lean_dec(x_327);
lean_dec(x_326);
lean_dec(x_324);
lean_dec(x_323);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_374 = lean_ctor_get(x_333, 0);
lean_inc(x_374);
x_375 = lean_ctor_get(x_333, 1);
lean_inc(x_375);
if (lean_is_exclusive(x_333)) {
 lean_ctor_release(x_333, 0);
 lean_ctor_release(x_333, 1);
 x_376 = x_333;
} else {
 lean_dec_ref(x_333);
 x_376 = lean_box(0);
}
if (lean_is_scalar(x_376)) {
 x_377 = lean_alloc_ctor(1, 2, 0);
} else {
 x_377 = x_376;
}
lean_ctor_set(x_377, 0, x_374);
lean_ctor_set(x_377, 1, x_375);
return x_377;
}
}
}
else
{
lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; uint8_t x_383; lean_object* x_384; 
lean_dec(x_1);
x_378 = lean_ctor_get(x_315, 1);
lean_inc(x_378);
lean_dec(x_315);
x_379 = lean_ctor_get(x_316, 0);
lean_inc(x_379);
lean_dec(x_316);
x_380 = lean_ctor_get(x_379, 2);
lean_inc(x_380);
x_381 = lean_alloc_closure((void*)(l_Lean_Expr_isFVar___boxed), 1, 0);
x_382 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Closure_collectType___lambda__1___boxed), 8, 0);
x_383 = 0;
lean_inc(x_3);
x_384 = l_Lean_ForEachExprWhere_visit___at_Lean_Compiler_LCNF_Closure_collectType___spec__1(x_381, x_382, x_380, x_383, x_2, x_3, x_4, x_5, x_6, x_7, x_378);
if (lean_obj_tag(x_384) == 0)
{
lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; 
x_385 = lean_ctor_get(x_384, 1);
lean_inc(x_385);
lean_dec(x_384);
x_386 = lean_st_ref_take(x_3, x_385);
x_387 = lean_ctor_get(x_386, 0);
lean_inc(x_387);
x_388 = lean_ctor_get(x_386, 1);
lean_inc(x_388);
lean_dec(x_386);
x_389 = lean_ctor_get(x_387, 0);
lean_inc(x_389);
x_390 = lean_ctor_get(x_387, 1);
lean_inc(x_390);
x_391 = lean_ctor_get(x_387, 2);
lean_inc(x_391);
if (lean_is_exclusive(x_387)) {
 lean_ctor_release(x_387, 0);
 lean_ctor_release(x_387, 1);
 lean_ctor_release(x_387, 2);
 x_392 = x_387;
} else {
 lean_dec_ref(x_387);
 x_392 = lean_box(0);
}
x_393 = lean_array_push(x_390, x_379);
if (lean_is_scalar(x_392)) {
 x_394 = lean_alloc_ctor(0, 3, 0);
} else {
 x_394 = x_392;
}
lean_ctor_set(x_394, 0, x_389);
lean_ctor_set(x_394, 1, x_393);
lean_ctor_set(x_394, 2, x_391);
x_395 = lean_st_ref_set(x_3, x_394, x_388);
lean_dec(x_3);
x_396 = lean_ctor_get(x_395, 1);
lean_inc(x_396);
if (lean_is_exclusive(x_395)) {
 lean_ctor_release(x_395, 0);
 lean_ctor_release(x_395, 1);
 x_397 = x_395;
} else {
 lean_dec_ref(x_395);
 x_397 = lean_box(0);
}
x_398 = lean_box(0);
if (lean_is_scalar(x_397)) {
 x_399 = lean_alloc_ctor(0, 2, 0);
} else {
 x_399 = x_397;
}
lean_ctor_set(x_399, 0, x_398);
lean_ctor_set(x_399, 1, x_396);
return x_399;
}
else
{
lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; 
lean_dec(x_379);
lean_dec(x_3);
x_400 = lean_ctor_get(x_384, 0);
lean_inc(x_400);
x_401 = lean_ctor_get(x_384, 1);
lean_inc(x_401);
if (lean_is_exclusive(x_384)) {
 lean_ctor_release(x_384, 0);
 lean_ctor_release(x_384, 1);
 x_402 = x_384;
} else {
 lean_dec_ref(x_384);
 x_402 = lean_box(0);
}
if (lean_is_scalar(x_402)) {
 x_403 = lean_alloc_ctor(1, 2, 0);
} else {
 x_403 = x_402;
}
lean_ctor_set(x_403, 0, x_400);
lean_ctor_set(x_403, 1, x_401);
return x_403;
}
}
}
else
{
lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; uint8_t x_412; 
lean_dec(x_1);
x_404 = lean_ctor_get(x_313, 0);
lean_inc(x_404);
if (lean_is_exclusive(x_313)) {
 lean_ctor_release(x_313, 0);
 x_405 = x_313;
} else {
 lean_dec_ref(x_313);
 x_405 = lean_box(0);
}
x_406 = lean_ctor_get(x_312, 1);
lean_inc(x_406);
lean_dec(x_312);
x_407 = lean_ctor_get(x_2, 1);
lean_inc(x_407);
x_408 = lean_ctor_get(x_404, 0);
lean_inc(x_408);
x_409 = lean_ctor_get(x_404, 1);
lean_inc(x_409);
x_410 = lean_ctor_get(x_404, 3);
lean_inc(x_410);
lean_inc(x_408);
x_411 = lean_apply_1(x_407, x_408);
x_412 = lean_unbox(x_411);
lean_dec(x_411);
if (x_412 == 0)
{
lean_object* x_413; 
lean_dec(x_410);
lean_dec(x_409);
lean_dec(x_408);
lean_inc(x_3);
lean_inc(x_404);
x_413 = l_Lean_Compiler_LCNF_Closure_collectFunDecl(x_404, x_2, x_3, x_4, x_5, x_6, x_7, x_406);
if (lean_obj_tag(x_413) == 0)
{
lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; 
x_414 = lean_ctor_get(x_413, 1);
lean_inc(x_414);
lean_dec(x_413);
x_415 = lean_st_ref_take(x_3, x_414);
x_416 = lean_ctor_get(x_415, 0);
lean_inc(x_416);
x_417 = lean_ctor_get(x_415, 1);
lean_inc(x_417);
lean_dec(x_415);
x_418 = lean_ctor_get(x_416, 0);
lean_inc(x_418);
x_419 = lean_ctor_get(x_416, 1);
lean_inc(x_419);
x_420 = lean_ctor_get(x_416, 2);
lean_inc(x_420);
if (lean_is_exclusive(x_416)) {
 lean_ctor_release(x_416, 0);
 lean_ctor_release(x_416, 1);
 lean_ctor_release(x_416, 2);
 x_421 = x_416;
} else {
 lean_dec_ref(x_416);
 x_421 = lean_box(0);
}
if (lean_is_scalar(x_405)) {
 x_422 = lean_alloc_ctor(1, 1, 0);
} else {
 x_422 = x_405;
}
lean_ctor_set(x_422, 0, x_404);
x_423 = lean_array_push(x_420, x_422);
if (lean_is_scalar(x_421)) {
 x_424 = lean_alloc_ctor(0, 3, 0);
} else {
 x_424 = x_421;
}
lean_ctor_set(x_424, 0, x_418);
lean_ctor_set(x_424, 1, x_419);
lean_ctor_set(x_424, 2, x_423);
x_425 = lean_st_ref_set(x_3, x_424, x_417);
lean_dec(x_3);
x_426 = lean_ctor_get(x_425, 1);
lean_inc(x_426);
if (lean_is_exclusive(x_425)) {
 lean_ctor_release(x_425, 0);
 lean_ctor_release(x_425, 1);
 x_427 = x_425;
} else {
 lean_dec_ref(x_425);
 x_427 = lean_box(0);
}
x_428 = lean_box(0);
if (lean_is_scalar(x_427)) {
 x_429 = lean_alloc_ctor(0, 2, 0);
} else {
 x_429 = x_427;
}
lean_ctor_set(x_429, 0, x_428);
lean_ctor_set(x_429, 1, x_426);
return x_429;
}
else
{
lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; 
lean_dec(x_405);
lean_dec(x_404);
lean_dec(x_3);
x_430 = lean_ctor_get(x_413, 0);
lean_inc(x_430);
x_431 = lean_ctor_get(x_413, 1);
lean_inc(x_431);
if (lean_is_exclusive(x_413)) {
 lean_ctor_release(x_413, 0);
 lean_ctor_release(x_413, 1);
 x_432 = x_413;
} else {
 lean_dec_ref(x_413);
 x_432 = lean_box(0);
}
if (lean_is_scalar(x_432)) {
 x_433 = lean_alloc_ctor(1, 2, 0);
} else {
 x_433 = x_432;
}
lean_ctor_set(x_433, 0, x_430);
lean_ctor_set(x_433, 1, x_431);
return x_433;
}
}
else
{
lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; uint8_t x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; 
lean_dec(x_405);
lean_dec(x_404);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_434 = lean_st_ref_take(x_3, x_406);
x_435 = lean_ctor_get(x_434, 0);
lean_inc(x_435);
x_436 = lean_ctor_get(x_434, 1);
lean_inc(x_436);
lean_dec(x_434);
x_437 = lean_ctor_get(x_435, 0);
lean_inc(x_437);
x_438 = lean_ctor_get(x_435, 1);
lean_inc(x_438);
x_439 = lean_ctor_get(x_435, 2);
lean_inc(x_439);
if (lean_is_exclusive(x_435)) {
 lean_ctor_release(x_435, 0);
 lean_ctor_release(x_435, 1);
 lean_ctor_release(x_435, 2);
 x_440 = x_435;
} else {
 lean_dec_ref(x_435);
 x_440 = lean_box(0);
}
x_441 = 0;
x_442 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_442, 0, x_408);
lean_ctor_set(x_442, 1, x_409);
lean_ctor_set(x_442, 2, x_410);
lean_ctor_set_uint8(x_442, sizeof(void*)*3, x_441);
x_443 = lean_array_push(x_438, x_442);
if (lean_is_scalar(x_440)) {
 x_444 = lean_alloc_ctor(0, 3, 0);
} else {
 x_444 = x_440;
}
lean_ctor_set(x_444, 0, x_437);
lean_ctor_set(x_444, 1, x_443);
lean_ctor_set(x_444, 2, x_439);
x_445 = lean_st_ref_set(x_3, x_444, x_436);
lean_dec(x_3);
x_446 = lean_ctor_get(x_445, 1);
lean_inc(x_446);
if (lean_is_exclusive(x_445)) {
 lean_ctor_release(x_445, 0);
 lean_ctor_release(x_445, 1);
 x_447 = x_445;
} else {
 lean_dec_ref(x_445);
 x_447 = lean_box(0);
}
x_448 = lean_box(0);
if (lean_is_scalar(x_447)) {
 x_449 = lean_alloc_ctor(0, 2, 0);
} else {
 x_449 = x_447;
}
lean_ctor_set(x_449, 0, x_448);
lean_ctor_set(x_449, 1, x_446);
return x_449;
}
}
}
}
}
else
{
lean_object* x_450; 
lean_dec(x_14);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_450 = lean_box(0);
lean_ctor_set(x_9, 0, x_450);
return x_9;
}
}
else
{
lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; 
x_451 = lean_ctor_get(x_9, 0);
x_452 = lean_ctor_get(x_9, 1);
lean_inc(x_452);
lean_inc(x_451);
lean_dec(x_9);
x_453 = lean_ctor_get(x_451, 0);
lean_inc(x_453);
lean_dec(x_451);
x_454 = l_Lean_RBNode_findCore___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__2(x_453, x_1);
lean_dec(x_453);
if (lean_obj_tag(x_454) == 0)
{
lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; uint8_t x_460; 
lean_inc(x_1);
x_455 = l_Lean_Compiler_LCNF_Closure_markVisited(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_452);
x_456 = lean_ctor_get(x_455, 1);
lean_inc(x_456);
if (lean_is_exclusive(x_455)) {
 lean_ctor_release(x_455, 0);
 lean_ctor_release(x_455, 1);
 x_457 = x_455;
} else {
 lean_dec_ref(x_455);
 x_457 = lean_box(0);
}
x_458 = lean_ctor_get(x_2, 0);
lean_inc(x_458);
lean_inc(x_1);
x_459 = lean_apply_1(x_458, x_1);
x_460 = lean_unbox(x_459);
lean_dec(x_459);
if (x_460 == 0)
{
lean_object* x_461; lean_object* x_462; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_461 = lean_box(0);
if (lean_is_scalar(x_457)) {
 x_462 = lean_alloc_ctor(0, 2, 0);
} else {
 x_462 = x_457;
}
lean_ctor_set(x_462, 0, x_461);
lean_ctor_set(x_462, 1, x_456);
return x_462;
}
else
{
lean_object* x_463; lean_object* x_464; 
lean_dec(x_457);
x_463 = l_Lean_Compiler_LCNF_findFunDecl_x3f(x_1, x_4, x_5, x_6, x_7, x_456);
x_464 = lean_ctor_get(x_463, 0);
lean_inc(x_464);
if (lean_obj_tag(x_464) == 0)
{
lean_object* x_465; lean_object* x_466; lean_object* x_467; 
x_465 = lean_ctor_get(x_463, 1);
lean_inc(x_465);
lean_dec(x_463);
x_466 = l_Lean_Compiler_LCNF_findParam_x3f(x_1, x_4, x_5, x_6, x_7, x_465);
x_467 = lean_ctor_get(x_466, 0);
lean_inc(x_467);
if (lean_obj_tag(x_467) == 0)
{
lean_object* x_468; lean_object* x_469; lean_object* x_470; 
x_468 = lean_ctor_get(x_466, 1);
lean_inc(x_468);
lean_dec(x_466);
x_469 = l_Lean_Compiler_LCNF_findLetDecl_x3f(x_1, x_4, x_5, x_6, x_7, x_468);
lean_dec(x_1);
x_470 = lean_ctor_get(x_469, 0);
lean_inc(x_470);
if (lean_obj_tag(x_470) == 0)
{
lean_object* x_471; lean_object* x_472; lean_object* x_473; 
x_471 = lean_ctor_get(x_469, 1);
lean_inc(x_471);
lean_dec(x_469);
x_472 = l_Lean_Compiler_LCNF_Closure_collectFVar___closed__4;
x_473 = l_panic___at_Lean_Compiler_LCNF_Closure_collectFVar___spec__1(x_472, x_2, x_3, x_4, x_5, x_6, x_7, x_471);
return x_473;
}
else
{
lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; uint8_t x_483; lean_object* x_484; 
x_474 = lean_ctor_get(x_470, 0);
lean_inc(x_474);
if (lean_is_exclusive(x_470)) {
 lean_ctor_release(x_470, 0);
 x_475 = x_470;
} else {
 lean_dec_ref(x_470);
 x_475 = lean_box(0);
}
x_476 = lean_ctor_get(x_469, 1);
lean_inc(x_476);
lean_dec(x_469);
x_477 = lean_ctor_get(x_474, 0);
lean_inc(x_477);
x_478 = lean_ctor_get(x_474, 1);
lean_inc(x_478);
x_479 = lean_ctor_get(x_474, 2);
lean_inc(x_479);
x_480 = lean_ctor_get(x_474, 3);
lean_inc(x_480);
x_481 = lean_alloc_closure((void*)(l_Lean_Expr_isFVar___boxed), 1, 0);
x_482 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Closure_collectType___lambda__1___boxed), 8, 0);
x_483 = 0;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_479);
x_484 = l_Lean_ForEachExprWhere_visit___at_Lean_Compiler_LCNF_Closure_collectType___spec__1(x_481, x_482, x_479, x_483, x_2, x_3, x_4, x_5, x_6, x_7, x_476);
if (lean_obj_tag(x_484) == 0)
{
lean_object* x_485; lean_object* x_486; lean_object* x_487; uint8_t x_488; 
x_485 = lean_ctor_get(x_484, 1);
lean_inc(x_485);
lean_dec(x_484);
x_486 = lean_ctor_get(x_2, 1);
lean_inc(x_486);
lean_inc(x_477);
x_487 = lean_apply_1(x_486, x_477);
x_488 = lean_unbox(x_487);
lean_dec(x_487);
if (x_488 == 0)
{
lean_object* x_489; 
lean_dec(x_479);
lean_dec(x_478);
lean_dec(x_477);
lean_inc(x_3);
x_489 = l_Lean_Compiler_LCNF_Closure_collectLetValue(x_480, x_2, x_3, x_4, x_5, x_6, x_7, x_485);
if (lean_obj_tag(x_489) == 0)
{
lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; 
x_490 = lean_ctor_get(x_489, 1);
lean_inc(x_490);
lean_dec(x_489);
x_491 = lean_st_ref_take(x_3, x_490);
x_492 = lean_ctor_get(x_491, 0);
lean_inc(x_492);
x_493 = lean_ctor_get(x_491, 1);
lean_inc(x_493);
lean_dec(x_491);
x_494 = lean_ctor_get(x_492, 0);
lean_inc(x_494);
x_495 = lean_ctor_get(x_492, 1);
lean_inc(x_495);
x_496 = lean_ctor_get(x_492, 2);
lean_inc(x_496);
if (lean_is_exclusive(x_492)) {
 lean_ctor_release(x_492, 0);
 lean_ctor_release(x_492, 1);
 lean_ctor_release(x_492, 2);
 x_497 = x_492;
} else {
 lean_dec_ref(x_492);
 x_497 = lean_box(0);
}
if (lean_is_scalar(x_475)) {
 x_498 = lean_alloc_ctor(0, 1, 0);
} else {
 x_498 = x_475;
 lean_ctor_set_tag(x_498, 0);
}
lean_ctor_set(x_498, 0, x_474);
x_499 = lean_array_push(x_496, x_498);
if (lean_is_scalar(x_497)) {
 x_500 = lean_alloc_ctor(0, 3, 0);
} else {
 x_500 = x_497;
}
lean_ctor_set(x_500, 0, x_494);
lean_ctor_set(x_500, 1, x_495);
lean_ctor_set(x_500, 2, x_499);
x_501 = lean_st_ref_set(x_3, x_500, x_493);
lean_dec(x_3);
x_502 = lean_ctor_get(x_501, 1);
lean_inc(x_502);
if (lean_is_exclusive(x_501)) {
 lean_ctor_release(x_501, 0);
 lean_ctor_release(x_501, 1);
 x_503 = x_501;
} else {
 lean_dec_ref(x_501);
 x_503 = lean_box(0);
}
x_504 = lean_box(0);
if (lean_is_scalar(x_503)) {
 x_505 = lean_alloc_ctor(0, 2, 0);
} else {
 x_505 = x_503;
}
lean_ctor_set(x_505, 0, x_504);
lean_ctor_set(x_505, 1, x_502);
return x_505;
}
else
{
lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; 
lean_dec(x_475);
lean_dec(x_474);
lean_dec(x_3);
x_506 = lean_ctor_get(x_489, 0);
lean_inc(x_506);
x_507 = lean_ctor_get(x_489, 1);
lean_inc(x_507);
if (lean_is_exclusive(x_489)) {
 lean_ctor_release(x_489, 0);
 lean_ctor_release(x_489, 1);
 x_508 = x_489;
} else {
 lean_dec_ref(x_489);
 x_508 = lean_box(0);
}
if (lean_is_scalar(x_508)) {
 x_509 = lean_alloc_ctor(1, 2, 0);
} else {
 x_509 = x_508;
}
lean_ctor_set(x_509, 0, x_506);
lean_ctor_set(x_509, 1, x_507);
return x_509;
}
}
else
{
lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; 
lean_dec(x_480);
lean_dec(x_475);
lean_dec(x_474);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_510 = lean_st_ref_take(x_3, x_485);
x_511 = lean_ctor_get(x_510, 0);
lean_inc(x_511);
x_512 = lean_ctor_get(x_510, 1);
lean_inc(x_512);
lean_dec(x_510);
x_513 = lean_ctor_get(x_511, 0);
lean_inc(x_513);
x_514 = lean_ctor_get(x_511, 1);
lean_inc(x_514);
x_515 = lean_ctor_get(x_511, 2);
lean_inc(x_515);
if (lean_is_exclusive(x_511)) {
 lean_ctor_release(x_511, 0);
 lean_ctor_release(x_511, 1);
 lean_ctor_release(x_511, 2);
 x_516 = x_511;
} else {
 lean_dec_ref(x_511);
 x_516 = lean_box(0);
}
x_517 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_517, 0, x_477);
lean_ctor_set(x_517, 1, x_478);
lean_ctor_set(x_517, 2, x_479);
lean_ctor_set_uint8(x_517, sizeof(void*)*3, x_483);
x_518 = lean_array_push(x_514, x_517);
if (lean_is_scalar(x_516)) {
 x_519 = lean_alloc_ctor(0, 3, 0);
} else {
 x_519 = x_516;
}
lean_ctor_set(x_519, 0, x_513);
lean_ctor_set(x_519, 1, x_518);
lean_ctor_set(x_519, 2, x_515);
x_520 = lean_st_ref_set(x_3, x_519, x_512);
lean_dec(x_3);
x_521 = lean_ctor_get(x_520, 1);
lean_inc(x_521);
if (lean_is_exclusive(x_520)) {
 lean_ctor_release(x_520, 0);
 lean_ctor_release(x_520, 1);
 x_522 = x_520;
} else {
 lean_dec_ref(x_520);
 x_522 = lean_box(0);
}
x_523 = lean_box(0);
if (lean_is_scalar(x_522)) {
 x_524 = lean_alloc_ctor(0, 2, 0);
} else {
 x_524 = x_522;
}
lean_ctor_set(x_524, 0, x_523);
lean_ctor_set(x_524, 1, x_521);
return x_524;
}
}
else
{
lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; 
lean_dec(x_480);
lean_dec(x_479);
lean_dec(x_478);
lean_dec(x_477);
lean_dec(x_475);
lean_dec(x_474);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_525 = lean_ctor_get(x_484, 0);
lean_inc(x_525);
x_526 = lean_ctor_get(x_484, 1);
lean_inc(x_526);
if (lean_is_exclusive(x_484)) {
 lean_ctor_release(x_484, 0);
 lean_ctor_release(x_484, 1);
 x_527 = x_484;
} else {
 lean_dec_ref(x_484);
 x_527 = lean_box(0);
}
if (lean_is_scalar(x_527)) {
 x_528 = lean_alloc_ctor(1, 2, 0);
} else {
 x_528 = x_527;
}
lean_ctor_set(x_528, 0, x_525);
lean_ctor_set(x_528, 1, x_526);
return x_528;
}
}
}
else
{
lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; uint8_t x_534; lean_object* x_535; 
lean_dec(x_1);
x_529 = lean_ctor_get(x_466, 1);
lean_inc(x_529);
lean_dec(x_466);
x_530 = lean_ctor_get(x_467, 0);
lean_inc(x_530);
lean_dec(x_467);
x_531 = lean_ctor_get(x_530, 2);
lean_inc(x_531);
x_532 = lean_alloc_closure((void*)(l_Lean_Expr_isFVar___boxed), 1, 0);
x_533 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Closure_collectType___lambda__1___boxed), 8, 0);
x_534 = 0;
lean_inc(x_3);
x_535 = l_Lean_ForEachExprWhere_visit___at_Lean_Compiler_LCNF_Closure_collectType___spec__1(x_532, x_533, x_531, x_534, x_2, x_3, x_4, x_5, x_6, x_7, x_529);
if (lean_obj_tag(x_535) == 0)
{
lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; 
x_536 = lean_ctor_get(x_535, 1);
lean_inc(x_536);
lean_dec(x_535);
x_537 = lean_st_ref_take(x_3, x_536);
x_538 = lean_ctor_get(x_537, 0);
lean_inc(x_538);
x_539 = lean_ctor_get(x_537, 1);
lean_inc(x_539);
lean_dec(x_537);
x_540 = lean_ctor_get(x_538, 0);
lean_inc(x_540);
x_541 = lean_ctor_get(x_538, 1);
lean_inc(x_541);
x_542 = lean_ctor_get(x_538, 2);
lean_inc(x_542);
if (lean_is_exclusive(x_538)) {
 lean_ctor_release(x_538, 0);
 lean_ctor_release(x_538, 1);
 lean_ctor_release(x_538, 2);
 x_543 = x_538;
} else {
 lean_dec_ref(x_538);
 x_543 = lean_box(0);
}
x_544 = lean_array_push(x_541, x_530);
if (lean_is_scalar(x_543)) {
 x_545 = lean_alloc_ctor(0, 3, 0);
} else {
 x_545 = x_543;
}
lean_ctor_set(x_545, 0, x_540);
lean_ctor_set(x_545, 1, x_544);
lean_ctor_set(x_545, 2, x_542);
x_546 = lean_st_ref_set(x_3, x_545, x_539);
lean_dec(x_3);
x_547 = lean_ctor_get(x_546, 1);
lean_inc(x_547);
if (lean_is_exclusive(x_546)) {
 lean_ctor_release(x_546, 0);
 lean_ctor_release(x_546, 1);
 x_548 = x_546;
} else {
 lean_dec_ref(x_546);
 x_548 = lean_box(0);
}
x_549 = lean_box(0);
if (lean_is_scalar(x_548)) {
 x_550 = lean_alloc_ctor(0, 2, 0);
} else {
 x_550 = x_548;
}
lean_ctor_set(x_550, 0, x_549);
lean_ctor_set(x_550, 1, x_547);
return x_550;
}
else
{
lean_object* x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; 
lean_dec(x_530);
lean_dec(x_3);
x_551 = lean_ctor_get(x_535, 0);
lean_inc(x_551);
x_552 = lean_ctor_get(x_535, 1);
lean_inc(x_552);
if (lean_is_exclusive(x_535)) {
 lean_ctor_release(x_535, 0);
 lean_ctor_release(x_535, 1);
 x_553 = x_535;
} else {
 lean_dec_ref(x_535);
 x_553 = lean_box(0);
}
if (lean_is_scalar(x_553)) {
 x_554 = lean_alloc_ctor(1, 2, 0);
} else {
 x_554 = x_553;
}
lean_ctor_set(x_554, 0, x_551);
lean_ctor_set(x_554, 1, x_552);
return x_554;
}
}
}
else
{
lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; lean_object* x_561; lean_object* x_562; uint8_t x_563; 
lean_dec(x_1);
x_555 = lean_ctor_get(x_464, 0);
lean_inc(x_555);
if (lean_is_exclusive(x_464)) {
 lean_ctor_release(x_464, 0);
 x_556 = x_464;
} else {
 lean_dec_ref(x_464);
 x_556 = lean_box(0);
}
x_557 = lean_ctor_get(x_463, 1);
lean_inc(x_557);
lean_dec(x_463);
x_558 = lean_ctor_get(x_2, 1);
lean_inc(x_558);
x_559 = lean_ctor_get(x_555, 0);
lean_inc(x_559);
x_560 = lean_ctor_get(x_555, 1);
lean_inc(x_560);
x_561 = lean_ctor_get(x_555, 3);
lean_inc(x_561);
lean_inc(x_559);
x_562 = lean_apply_1(x_558, x_559);
x_563 = lean_unbox(x_562);
lean_dec(x_562);
if (x_563 == 0)
{
lean_object* x_564; 
lean_dec(x_561);
lean_dec(x_560);
lean_dec(x_559);
lean_inc(x_3);
lean_inc(x_555);
x_564 = l_Lean_Compiler_LCNF_Closure_collectFunDecl(x_555, x_2, x_3, x_4, x_5, x_6, x_7, x_557);
if (lean_obj_tag(x_564) == 0)
{
lean_object* x_565; lean_object* x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; lean_object* x_575; lean_object* x_576; lean_object* x_577; lean_object* x_578; lean_object* x_579; lean_object* x_580; 
x_565 = lean_ctor_get(x_564, 1);
lean_inc(x_565);
lean_dec(x_564);
x_566 = lean_st_ref_take(x_3, x_565);
x_567 = lean_ctor_get(x_566, 0);
lean_inc(x_567);
x_568 = lean_ctor_get(x_566, 1);
lean_inc(x_568);
lean_dec(x_566);
x_569 = lean_ctor_get(x_567, 0);
lean_inc(x_569);
x_570 = lean_ctor_get(x_567, 1);
lean_inc(x_570);
x_571 = lean_ctor_get(x_567, 2);
lean_inc(x_571);
if (lean_is_exclusive(x_567)) {
 lean_ctor_release(x_567, 0);
 lean_ctor_release(x_567, 1);
 lean_ctor_release(x_567, 2);
 x_572 = x_567;
} else {
 lean_dec_ref(x_567);
 x_572 = lean_box(0);
}
if (lean_is_scalar(x_556)) {
 x_573 = lean_alloc_ctor(1, 1, 0);
} else {
 x_573 = x_556;
}
lean_ctor_set(x_573, 0, x_555);
x_574 = lean_array_push(x_571, x_573);
if (lean_is_scalar(x_572)) {
 x_575 = lean_alloc_ctor(0, 3, 0);
} else {
 x_575 = x_572;
}
lean_ctor_set(x_575, 0, x_569);
lean_ctor_set(x_575, 1, x_570);
lean_ctor_set(x_575, 2, x_574);
x_576 = lean_st_ref_set(x_3, x_575, x_568);
lean_dec(x_3);
x_577 = lean_ctor_get(x_576, 1);
lean_inc(x_577);
if (lean_is_exclusive(x_576)) {
 lean_ctor_release(x_576, 0);
 lean_ctor_release(x_576, 1);
 x_578 = x_576;
} else {
 lean_dec_ref(x_576);
 x_578 = lean_box(0);
}
x_579 = lean_box(0);
if (lean_is_scalar(x_578)) {
 x_580 = lean_alloc_ctor(0, 2, 0);
} else {
 x_580 = x_578;
}
lean_ctor_set(x_580, 0, x_579);
lean_ctor_set(x_580, 1, x_577);
return x_580;
}
else
{
lean_object* x_581; lean_object* x_582; lean_object* x_583; lean_object* x_584; 
lean_dec(x_556);
lean_dec(x_555);
lean_dec(x_3);
x_581 = lean_ctor_get(x_564, 0);
lean_inc(x_581);
x_582 = lean_ctor_get(x_564, 1);
lean_inc(x_582);
if (lean_is_exclusive(x_564)) {
 lean_ctor_release(x_564, 0);
 lean_ctor_release(x_564, 1);
 x_583 = x_564;
} else {
 lean_dec_ref(x_564);
 x_583 = lean_box(0);
}
if (lean_is_scalar(x_583)) {
 x_584 = lean_alloc_ctor(1, 2, 0);
} else {
 x_584 = x_583;
}
lean_ctor_set(x_584, 0, x_581);
lean_ctor_set(x_584, 1, x_582);
return x_584;
}
}
else
{
lean_object* x_585; lean_object* x_586; lean_object* x_587; lean_object* x_588; lean_object* x_589; lean_object* x_590; lean_object* x_591; uint8_t x_592; lean_object* x_593; lean_object* x_594; lean_object* x_595; lean_object* x_596; lean_object* x_597; lean_object* x_598; lean_object* x_599; lean_object* x_600; 
lean_dec(x_556);
lean_dec(x_555);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_585 = lean_st_ref_take(x_3, x_557);
x_586 = lean_ctor_get(x_585, 0);
lean_inc(x_586);
x_587 = lean_ctor_get(x_585, 1);
lean_inc(x_587);
lean_dec(x_585);
x_588 = lean_ctor_get(x_586, 0);
lean_inc(x_588);
x_589 = lean_ctor_get(x_586, 1);
lean_inc(x_589);
x_590 = lean_ctor_get(x_586, 2);
lean_inc(x_590);
if (lean_is_exclusive(x_586)) {
 lean_ctor_release(x_586, 0);
 lean_ctor_release(x_586, 1);
 lean_ctor_release(x_586, 2);
 x_591 = x_586;
} else {
 lean_dec_ref(x_586);
 x_591 = lean_box(0);
}
x_592 = 0;
x_593 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_593, 0, x_559);
lean_ctor_set(x_593, 1, x_560);
lean_ctor_set(x_593, 2, x_561);
lean_ctor_set_uint8(x_593, sizeof(void*)*3, x_592);
x_594 = lean_array_push(x_589, x_593);
if (lean_is_scalar(x_591)) {
 x_595 = lean_alloc_ctor(0, 3, 0);
} else {
 x_595 = x_591;
}
lean_ctor_set(x_595, 0, x_588);
lean_ctor_set(x_595, 1, x_594);
lean_ctor_set(x_595, 2, x_590);
x_596 = lean_st_ref_set(x_3, x_595, x_587);
lean_dec(x_3);
x_597 = lean_ctor_get(x_596, 1);
lean_inc(x_597);
if (lean_is_exclusive(x_596)) {
 lean_ctor_release(x_596, 0);
 lean_ctor_release(x_596, 1);
 x_598 = x_596;
} else {
 lean_dec_ref(x_596);
 x_598 = lean_box(0);
}
x_599 = lean_box(0);
if (lean_is_scalar(x_598)) {
 x_600 = lean_alloc_ctor(0, 2, 0);
} else {
 x_600 = x_598;
}
lean_ctor_set(x_600, 0, x_599);
lean_ctor_set(x_600, 1, x_597);
return x_600;
}
}
}
}
else
{
lean_object* x_601; lean_object* x_602; 
lean_dec(x_454);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_601 = lean_box(0);
x_602 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_602, 0, x_601);
lean_ctor_set(x_602, 1, x_452);
return x_602;
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
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_ctor_get(x_1, 4);
lean_inc(x_18);
lean_dec(x_1);
x_19 = l_Lean_Compiler_LCNF_Closure_collectCode(x_18, x_2, x_3, x_4, x_5, x_6, x_7, x_17);
return x_19;
}
else
{
uint8_t x_20; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_20 = !lean_is_exclusive(x_16);
if (x_20 == 0)
{
return x_16;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_16, 0);
x_22 = lean_ctor_get(x_16, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_16);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
else
{
uint8_t x_24; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_24 = !lean_is_exclusive(x_13);
if (x_24 == 0)
{
return x_13;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_13, 0);
x_26 = lean_ctor_get(x_13, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_13);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
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
x_15 = l_Lean_ForEachExprWhere_visit___at_Lean_Compiler_LCNF_Closure_collectType___spec__1(x_12, x_13, x_11, x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_ctor_get(x_9, 3);
lean_inc(x_17);
lean_dec(x_9);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_18 = l_Lean_Compiler_LCNF_Closure_collectLetValue(x_17, x_2, x_3, x_4, x_5, x_6, x_7, x_16);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_1 = x_10;
x_8 = x_19;
goto _start;
}
else
{
uint8_t x_21; 
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_21 = !lean_is_exclusive(x_18);
if (x_21 == 0)
{
return x_18;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_18, 0);
x_23 = lean_ctor_get(x_18, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_18);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
else
{
uint8_t x_25; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_25 = !lean_is_exclusive(x_15);
if (x_25 == 0)
{
return x_15;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_15, 0);
x_27 = lean_ctor_get(x_15, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_15);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
case 3:
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_1);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_30 = lean_ctor_get(x_1, 1);
x_31 = lean_ctor_get(x_1, 0);
lean_dec(x_31);
x_32 = lean_array_get_size(x_30);
x_33 = lean_unsigned_to_nat(0u);
x_34 = lean_nat_dec_lt(x_33, x_32);
if (x_34 == 0)
{
lean_object* x_35; 
lean_dec(x_32);
lean_dec(x_30);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_35 = lean_box(0);
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 1, x_8);
lean_ctor_set(x_1, 0, x_35);
return x_1;
}
else
{
uint8_t x_36; 
x_36 = lean_nat_dec_le(x_32, x_32);
if (x_36 == 0)
{
lean_object* x_37; 
lean_dec(x_32);
lean_dec(x_30);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_37 = lean_box(0);
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 1, x_8);
lean_ctor_set(x_1, 0, x_37);
return x_1;
}
else
{
size_t x_38; size_t x_39; lean_object* x_40; lean_object* x_41; 
lean_free_object(x_1);
x_38 = 0;
x_39 = lean_usize_of_nat(x_32);
lean_dec(x_32);
x_40 = lean_box(0);
x_41 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Closure_collectLetValue___spec__1(x_30, x_38, x_39, x_40, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_30);
return x_41;
}
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_42 = lean_ctor_get(x_1, 1);
lean_inc(x_42);
lean_dec(x_1);
x_43 = lean_array_get_size(x_42);
x_44 = lean_unsigned_to_nat(0u);
x_45 = lean_nat_dec_lt(x_44, x_43);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; 
lean_dec(x_43);
lean_dec(x_42);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_46 = lean_box(0);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_8);
return x_47;
}
else
{
uint8_t x_48; 
x_48 = lean_nat_dec_le(x_43, x_43);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; 
lean_dec(x_43);
lean_dec(x_42);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_49 = lean_box(0);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_8);
return x_50;
}
else
{
size_t x_51; size_t x_52; lean_object* x_53; lean_object* x_54; 
x_51 = 0;
x_52 = lean_usize_of_nat(x_43);
lean_dec(x_43);
x_53 = lean_box(0);
x_54 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Closure_collectLetValue___spec__1(x_42, x_51, x_52, x_53, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_42);
return x_54;
}
}
}
}
case 4:
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; lean_object* x_60; 
x_55 = lean_ctor_get(x_1, 0);
lean_inc(x_55);
lean_dec(x_1);
x_56 = lean_ctor_get(x_55, 1);
lean_inc(x_56);
x_57 = lean_alloc_closure((void*)(l_Lean_Expr_isFVar___boxed), 1, 0);
x_58 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Closure_collectType___lambda__1___boxed), 8, 0);
x_59 = 0;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_60 = l_Lean_ForEachExprWhere_visit___at_Lean_Compiler_LCNF_Closure_collectType___spec__1(x_57, x_58, x_56, x_59, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_60, 1);
lean_inc(x_61);
lean_dec(x_60);
x_62 = lean_ctor_get(x_55, 2);
lean_inc(x_62);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_63 = l_Lean_Compiler_LCNF_Closure_collectFVar(x_62, x_2, x_3, x_4, x_5, x_6, x_7, x_61);
if (lean_obj_tag(x_63) == 0)
{
uint8_t x_64; 
x_64 = !lean_is_exclusive(x_63);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_65 = lean_ctor_get(x_63, 1);
x_66 = lean_ctor_get(x_63, 0);
lean_dec(x_66);
x_67 = lean_ctor_get(x_55, 3);
lean_inc(x_67);
lean_dec(x_55);
x_68 = lean_array_get_size(x_67);
x_69 = lean_unsigned_to_nat(0u);
x_70 = lean_nat_dec_lt(x_69, x_68);
if (x_70 == 0)
{
lean_object* x_71; 
lean_dec(x_68);
lean_dec(x_67);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_71 = lean_box(0);
lean_ctor_set(x_63, 0, x_71);
return x_63;
}
else
{
uint8_t x_72; 
x_72 = lean_nat_dec_le(x_68, x_68);
if (x_72 == 0)
{
lean_object* x_73; 
lean_dec(x_68);
lean_dec(x_67);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_73 = lean_box(0);
lean_ctor_set(x_63, 0, x_73);
return x_63;
}
else
{
size_t x_74; size_t x_75; lean_object* x_76; lean_object* x_77; 
lean_free_object(x_63);
x_74 = 0;
x_75 = lean_usize_of_nat(x_68);
lean_dec(x_68);
x_76 = lean_box(0);
x_77 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Closure_collectCode___spec__1(x_67, x_74, x_75, x_76, x_2, x_3, x_4, x_5, x_6, x_7, x_65);
lean_dec(x_67);
return x_77;
}
}
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; 
x_78 = lean_ctor_get(x_63, 1);
lean_inc(x_78);
lean_dec(x_63);
x_79 = lean_ctor_get(x_55, 3);
lean_inc(x_79);
lean_dec(x_55);
x_80 = lean_array_get_size(x_79);
x_81 = lean_unsigned_to_nat(0u);
x_82 = lean_nat_dec_lt(x_81, x_80);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; 
lean_dec(x_80);
lean_dec(x_79);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_83 = lean_box(0);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_78);
return x_84;
}
else
{
uint8_t x_85; 
x_85 = lean_nat_dec_le(x_80, x_80);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; 
lean_dec(x_80);
lean_dec(x_79);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_86 = lean_box(0);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_78);
return x_87;
}
else
{
size_t x_88; size_t x_89; lean_object* x_90; lean_object* x_91; 
x_88 = 0;
x_89 = lean_usize_of_nat(x_80);
lean_dec(x_80);
x_90 = lean_box(0);
x_91 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Closure_collectCode___spec__1(x_79, x_88, x_89, x_90, x_2, x_3, x_4, x_5, x_6, x_7, x_78);
lean_dec(x_79);
return x_91;
}
}
}
}
else
{
uint8_t x_92; 
lean_dec(x_55);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_92 = !lean_is_exclusive(x_63);
if (x_92 == 0)
{
return x_63;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_63, 0);
x_94 = lean_ctor_get(x_63, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_63);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
return x_95;
}
}
}
else
{
uint8_t x_96; 
lean_dec(x_55);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_96 = !lean_is_exclusive(x_60);
if (x_96 == 0)
{
return x_60;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_60, 0);
x_98 = lean_ctor_get(x_60, 1);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_60);
x_99 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set(x_99, 1, x_98);
return x_99;
}
}
}
case 5:
{
lean_object* x_100; lean_object* x_101; 
x_100 = lean_ctor_get(x_1, 0);
lean_inc(x_100);
lean_dec(x_1);
x_101 = l_Lean_Compiler_LCNF_Closure_collectFVar(x_100, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_101;
}
case 6:
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; uint8_t x_105; lean_object* x_106; 
x_102 = lean_ctor_get(x_1, 0);
lean_inc(x_102);
lean_dec(x_1);
x_103 = lean_alloc_closure((void*)(l_Lean_Expr_isFVar___boxed), 1, 0);
x_104 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Closure_collectType___lambda__1___boxed), 8, 0);
x_105 = 0;
x_106 = l_Lean_ForEachExprWhere_visit___at_Lean_Compiler_LCNF_Closure_collectType___spec__1(x_103, x_104, x_102, x_105, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_106;
}
default: 
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_107 = lean_ctor_get(x_1, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_1, 1);
lean_inc(x_108);
lean_dec(x_1);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_109 = l_Lean_Compiler_LCNF_Closure_collectFunDecl(x_107, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_109) == 0)
{
lean_object* x_110; 
x_110 = lean_ctor_get(x_109, 1);
lean_inc(x_110);
lean_dec(x_109);
x_1 = x_108;
x_8 = x_110;
goto _start;
}
else
{
uint8_t x_112; 
lean_dec(x_108);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_112 = !lean_is_exclusive(x_109);
if (x_112 == 0)
{
return x_109;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_113 = lean_ctor_get(x_109, 0);
x_114 = lean_ctor_get(x_109, 1);
lean_inc(x_114);
lean_inc(x_113);
lean_dec(x_109);
x_115 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_115, 0, x_113);
lean_ctor_set(x_115, 1, x_114);
return x_115;
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
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_2);
lean_ctor_set(x_9, 1, x_3);
x_10 = l_Lean_Compiler_LCNF_Closure_run___rarg___closed__2;
x_11 = lean_st_mk_ref(x_10, x_8);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
x_15 = lean_apply_7(x_1, x_9, x_13, x_4, x_5, x_6, x_7, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_st_ref_get(x_13, x_17);
lean_dec(x_13);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 2);
lean_inc(x_22);
lean_dec(x_20);
lean_ctor_set(x_11, 1, x_22);
lean_ctor_set(x_11, 0, x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_16);
lean_ctor_set(x_23, 1, x_11);
lean_ctor_set(x_18, 0, x_23);
return x_18;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_24 = lean_ctor_get(x_18, 0);
x_25 = lean_ctor_get(x_18, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_18);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
x_27 = lean_ctor_get(x_24, 2);
lean_inc(x_27);
lean_dec(x_24);
lean_ctor_set(x_11, 1, x_27);
lean_ctor_set(x_11, 0, x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_16);
lean_ctor_set(x_28, 1, x_11);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_25);
return x_29;
}
}
else
{
uint8_t x_30; 
lean_free_object(x_11);
lean_dec(x_13);
x_30 = !lean_is_exclusive(x_15);
if (x_30 == 0)
{
return x_15;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_15, 0);
x_32 = lean_ctor_get(x_15, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_15);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_11, 0);
x_35 = lean_ctor_get(x_11, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_11);
lean_inc(x_34);
x_36 = lean_apply_7(x_1, x_9, x_34, x_4, x_5, x_6, x_7, x_35);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = lean_st_ref_get(x_34, x_38);
lean_dec(x_34);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 x_42 = x_39;
} else {
 lean_dec_ref(x_39);
 x_42 = lean_box(0);
}
x_43 = lean_ctor_get(x_40, 1);
lean_inc(x_43);
x_44 = lean_ctor_get(x_40, 2);
lean_inc(x_44);
lean_dec(x_40);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_37);
lean_ctor_set(x_46, 1, x_45);
if (lean_is_scalar(x_42)) {
 x_47 = lean_alloc_ctor(0, 2, 0);
} else {
 x_47 = x_42;
}
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_41);
return x_47;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_34);
x_48 = lean_ctor_get(x_36, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_36, 1);
lean_inc(x_49);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_50 = x_36;
} else {
 lean_dec_ref(x_36);
 x_50 = lean_box(0);
}
if (lean_is_scalar(x_50)) {
 x_51 = lean_alloc_ctor(1, 2, 0);
} else {
 x_51 = x_50;
}
lean_ctor_set(x_51, 0, x_48);
lean_ctor_set(x_51, 1, x_49);
return x_51;
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
