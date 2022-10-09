// Lean compiler output
// Module: Lean.Compiler.LCNF.Closure
// Imports: Init Lean.Util.ForEachExpr Lean.Compiler.LCNF.CompilerM
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
size_t lean_usize_add(size_t, size_t);
static lean_object* l_Lean_Compiler_LCNF_Closure_collectFVar___closed__3;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Closure_collectFVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
static lean_object* l_Lean_Compiler_LCNF_Closure_State_params___default___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Closure_State_params___default;
static lean_object* l_panic___at_Lean_Compiler_LCNF_Closure_collectFVar___spec__2___closed__2;
LEAN_EXPORT lean_object* l_Lean_RBNode_findCore___at_Lean_Compiler_LCNF_Closure_collectFVar___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Closure_collectCode___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Closure_collectCode___spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at_Lean_Compiler_LCNF_Closure_collectFVar___spec__2___closed__1;
static lean_object* l_panic___at_Lean_Compiler_LCNF_Closure_collectFVar___spec__2___closed__4;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Closure_collectParams___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Closure_run___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_HashMapImp_find_x3f___at_Lean_ForEachExpr_visit___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_findParam_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Closure_collectCode___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at_Lean_Compiler_LCNF_Closure_collectFVar___spec__2___closed__3;
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___at_Lean_Compiler_LCNF_Closure_collectExpr___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkHashMapImp___rarg(lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Closure_collectCode___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Closure_collectExpr___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabited___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Closure_collectExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_quickCmp(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_findCore___at_Lean_Compiler_LCNF_Closure_collectFVar___spec__1___boxed(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_HashMap_insert___at_Lean_ForEachExpr_visit___spec__3(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Closure_collectFVar___closed__2;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Closure_State_visited___default;
lean_object* l_Lean_RBNode_insert___at___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectExpr___spec__1(lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_Compiler_LCNF_findFunDecl_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Closure_collectParams___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Closure_collectExpr___closed__2;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Closure_State_decls___default;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Closure_run(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Closure_collectExpr___closed__1;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Closure_run___rarg___closed__1;
lean_object* l_instInhabitedReaderT___rarg___boxed(lean_object*, lean_object*);
extern lean_object* l_Lean_Core_instMonadCoreM;
static lean_object* l_panic___at_Lean_Compiler_LCNF_Closure_collectFVar___spec__2___closed__5;
static lean_object* l_Lean_Compiler_LCNF_Closure_collectFVar___closed__4;
lean_object* l_Lean_Compiler_LCNF_findLetDecl_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadReaderT___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___at_Lean_Compiler_LCNF_Closure_collectExpr___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Closure_collectCode(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at_Lean_Compiler_LCNF_Closure_collectFVar___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Closure_markVisited(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Closure_collectFVar___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Closure_collectFunDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_instInhabitedPUnit;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Closure_markVisited___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Closure_collectParams___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* _init_l_Lean_Compiler_LCNF_Closure_State_visited___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Closure_State_params___default___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Closure_State_params___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Compiler_LCNF_Closure_State_params___default___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Closure_State_decls___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Compiler_LCNF_Closure_State_params___default___closed__1;
return x_1;
}
}
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
x_15 = l_Lean_RBNode_insert___at___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectExpr___spec__1(x_13, x_1, x_14);
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
x_25 = l_Lean_RBNode_insert___at___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectExpr___spec__1(x_21, x_1, x_24);
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
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_4);
x_13 = lean_array_uget(x_1, x_2);
x_14 = lean_ctor_get(x_13, 2);
lean_inc(x_14);
lean_dec(x_13);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_15 = l_Lean_Compiler_LCNF_Closure_collectExpr(x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = 1;
x_19 = lean_usize_add(x_2, x_18);
x_2 = x_19;
x_4 = x_16;
x_11 = x_17;
goto _start;
}
else
{
uint8_t x_21; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_21 = !lean_is_exclusive(x_15);
if (x_21 == 0)
{
return x_15;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_15, 0);
x_23 = lean_ctor_get(x_15, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_15);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
else
{
lean_object* x_25; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_4);
lean_ctor_set(x_25, 1, x_11);
return x_25;
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
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___at_Lean_Compiler_LCNF_Closure_collectExpr___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_23; uint8_t x_24; 
x_23 = lean_st_ref_get(x_3, x_10);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_23, 0);
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_2);
x_27 = l_Lean_HashMapImp_find_x3f___at_Lean_ForEachExpr_visit___spec__1(x_25, x_2);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; 
lean_free_object(x_23);
lean_inc(x_1);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_28 = lean_apply_8(x_1, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_26);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; uint8_t x_30; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_unbox(x_29);
lean_dec(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_dec(x_28);
x_32 = lean_box(0);
x_11 = x_32;
x_12 = x_31;
goto block_22;
}
else
{
switch (lean_obj_tag(x_2)) {
case 5:
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_ctor_get(x_28, 1);
lean_inc(x_33);
lean_dec(x_28);
x_34 = lean_ctor_get(x_2, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_2, 1);
lean_inc(x_35);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_36 = l_Lean_ForEachExpr_visit___at_Lean_Compiler_LCNF_Closure_collectExpr___spec__1(x_1, x_34, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_33);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
lean_dec(x_36);
x_38 = l_Lean_ForEachExpr_visit___at_Lean_Compiler_LCNF_Closure_collectExpr___spec__1(x_1, x_35, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_37);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_11 = x_39;
x_12 = x_40;
goto block_22;
}
else
{
uint8_t x_41; 
lean_dec(x_2);
x_41 = !lean_is_exclusive(x_38);
if (x_41 == 0)
{
return x_38;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_38, 0);
x_43 = lean_ctor_get(x_38, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_38);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
else
{
uint8_t x_45; 
lean_dec(x_35);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_45 = !lean_is_exclusive(x_36);
if (x_45 == 0)
{
return x_36;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_36, 0);
x_47 = lean_ctor_get(x_36, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_36);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
case 6:
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_49 = lean_ctor_get(x_28, 1);
lean_inc(x_49);
lean_dec(x_28);
x_50 = lean_ctor_get(x_2, 1);
lean_inc(x_50);
x_51 = lean_ctor_get(x_2, 2);
lean_inc(x_51);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_52 = l_Lean_ForEachExpr_visit___at_Lean_Compiler_LCNF_Closure_collectExpr___spec__1(x_1, x_50, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_49);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_ctor_get(x_52, 1);
lean_inc(x_53);
lean_dec(x_52);
x_54 = l_Lean_ForEachExpr_visit___at_Lean_Compiler_LCNF_Closure_collectExpr___spec__1(x_1, x_51, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_53);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
x_11 = x_55;
x_12 = x_56;
goto block_22;
}
else
{
uint8_t x_57; 
lean_dec(x_2);
x_57 = !lean_is_exclusive(x_54);
if (x_57 == 0)
{
return x_54;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_54, 0);
x_59 = lean_ctor_get(x_54, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_54);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
else
{
uint8_t x_61; 
lean_dec(x_51);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_61 = !lean_is_exclusive(x_52);
if (x_61 == 0)
{
return x_52;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_52, 0);
x_63 = lean_ctor_get(x_52, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_52);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
}
case 7:
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_65 = lean_ctor_get(x_28, 1);
lean_inc(x_65);
lean_dec(x_28);
x_66 = lean_ctor_get(x_2, 1);
lean_inc(x_66);
x_67 = lean_ctor_get(x_2, 2);
lean_inc(x_67);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_68 = l_Lean_ForEachExpr_visit___at_Lean_Compiler_LCNF_Closure_collectExpr___spec__1(x_1, x_66, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_65);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_ctor_get(x_68, 1);
lean_inc(x_69);
lean_dec(x_68);
x_70 = l_Lean_ForEachExpr_visit___at_Lean_Compiler_LCNF_Closure_collectExpr___spec__1(x_1, x_67, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_69);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; 
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
lean_dec(x_70);
x_11 = x_71;
x_12 = x_72;
goto block_22;
}
else
{
uint8_t x_73; 
lean_dec(x_2);
x_73 = !lean_is_exclusive(x_70);
if (x_73 == 0)
{
return x_70;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_70, 0);
x_75 = lean_ctor_get(x_70, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_70);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
return x_76;
}
}
}
else
{
uint8_t x_77; 
lean_dec(x_67);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_77 = !lean_is_exclusive(x_68);
if (x_77 == 0)
{
return x_68;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_68, 0);
x_79 = lean_ctor_get(x_68, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_68);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
}
}
case 8:
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_81 = lean_ctor_get(x_28, 1);
lean_inc(x_81);
lean_dec(x_28);
x_82 = lean_ctor_get(x_2, 1);
lean_inc(x_82);
x_83 = lean_ctor_get(x_2, 2);
lean_inc(x_83);
x_84 = lean_ctor_get(x_2, 3);
lean_inc(x_84);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_85 = l_Lean_ForEachExpr_visit___at_Lean_Compiler_LCNF_Closure_collectExpr___spec__1(x_1, x_82, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_81);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; lean_object* x_87; 
x_86 = lean_ctor_get(x_85, 1);
lean_inc(x_86);
lean_dec(x_85);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_87 = l_Lean_ForEachExpr_visit___at_Lean_Compiler_LCNF_Closure_collectExpr___spec__1(x_1, x_83, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_86);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; lean_object* x_89; 
x_88 = lean_ctor_get(x_87, 1);
lean_inc(x_88);
lean_dec(x_87);
x_89 = l_Lean_ForEachExpr_visit___at_Lean_Compiler_LCNF_Closure_collectExpr___spec__1(x_1, x_84, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_88);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; lean_object* x_91; 
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_89, 1);
lean_inc(x_91);
lean_dec(x_89);
x_11 = x_90;
x_12 = x_91;
goto block_22;
}
else
{
uint8_t x_92; 
lean_dec(x_2);
x_92 = !lean_is_exclusive(x_89);
if (x_92 == 0)
{
return x_89;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_89, 0);
x_94 = lean_ctor_get(x_89, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_89);
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
lean_dec(x_84);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_96 = !lean_is_exclusive(x_87);
if (x_96 == 0)
{
return x_87;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_87, 0);
x_98 = lean_ctor_get(x_87, 1);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_87);
x_99 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set(x_99, 1, x_98);
return x_99;
}
}
}
else
{
uint8_t x_100; 
lean_dec(x_84);
lean_dec(x_83);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_100 = !lean_is_exclusive(x_85);
if (x_100 == 0)
{
return x_85;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_85, 0);
x_102 = lean_ctor_get(x_85, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_85);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
return x_103;
}
}
}
case 10:
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_104 = lean_ctor_get(x_28, 1);
lean_inc(x_104);
lean_dec(x_28);
x_105 = lean_ctor_get(x_2, 1);
lean_inc(x_105);
x_106 = l_Lean_ForEachExpr_visit___at_Lean_Compiler_LCNF_Closure_collectExpr___spec__1(x_1, x_105, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_104);
if (lean_obj_tag(x_106) == 0)
{
lean_object* x_107; lean_object* x_108; 
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_106, 1);
lean_inc(x_108);
lean_dec(x_106);
x_11 = x_107;
x_12 = x_108;
goto block_22;
}
else
{
uint8_t x_109; 
lean_dec(x_2);
x_109 = !lean_is_exclusive(x_106);
if (x_109 == 0)
{
return x_106;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_110 = lean_ctor_get(x_106, 0);
x_111 = lean_ctor_get(x_106, 1);
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_106);
x_112 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
return x_112;
}
}
}
case 11:
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_113 = lean_ctor_get(x_28, 1);
lean_inc(x_113);
lean_dec(x_28);
x_114 = lean_ctor_get(x_2, 2);
lean_inc(x_114);
x_115 = l_Lean_ForEachExpr_visit___at_Lean_Compiler_LCNF_Closure_collectExpr___spec__1(x_1, x_114, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_113);
if (lean_obj_tag(x_115) == 0)
{
lean_object* x_116; lean_object* x_117; 
x_116 = lean_ctor_get(x_115, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_115, 1);
lean_inc(x_117);
lean_dec(x_115);
x_11 = x_116;
x_12 = x_117;
goto block_22;
}
else
{
uint8_t x_118; 
lean_dec(x_2);
x_118 = !lean_is_exclusive(x_115);
if (x_118 == 0)
{
return x_115;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_119 = lean_ctor_get(x_115, 0);
x_120 = lean_ctor_get(x_115, 1);
lean_inc(x_120);
lean_inc(x_119);
lean_dec(x_115);
x_121 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_121, 0, x_119);
lean_ctor_set(x_121, 1, x_120);
return x_121;
}
}
}
default: 
{
lean_object* x_122; lean_object* x_123; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_122 = lean_ctor_get(x_28, 1);
lean_inc(x_122);
lean_dec(x_28);
x_123 = lean_box(0);
x_11 = x_123;
x_12 = x_122;
goto block_22;
}
}
}
}
else
{
uint8_t x_124; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_124 = !lean_is_exclusive(x_28);
if (x_124 == 0)
{
return x_28;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_125 = lean_ctor_get(x_28, 0);
x_126 = lean_ctor_get(x_28, 1);
lean_inc(x_126);
lean_inc(x_125);
lean_dec(x_28);
x_127 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_127, 0, x_125);
lean_ctor_set(x_127, 1, x_126);
return x_127;
}
}
}
else
{
lean_object* x_128; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_128 = lean_ctor_get(x_27, 0);
lean_inc(x_128);
lean_dec(x_27);
lean_ctor_set(x_23, 0, x_128);
return x_23;
}
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_129 = lean_ctor_get(x_23, 0);
x_130 = lean_ctor_get(x_23, 1);
lean_inc(x_130);
lean_inc(x_129);
lean_dec(x_23);
lean_inc(x_2);
x_131 = l_Lean_HashMapImp_find_x3f___at_Lean_ForEachExpr_visit___spec__1(x_129, x_2);
if (lean_obj_tag(x_131) == 0)
{
lean_object* x_132; 
lean_inc(x_1);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_132 = lean_apply_8(x_1, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_130);
if (lean_obj_tag(x_132) == 0)
{
lean_object* x_133; uint8_t x_134; 
x_133 = lean_ctor_get(x_132, 0);
lean_inc(x_133);
x_134 = lean_unbox(x_133);
lean_dec(x_133);
if (x_134 == 0)
{
lean_object* x_135; lean_object* x_136; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_135 = lean_ctor_get(x_132, 1);
lean_inc(x_135);
lean_dec(x_132);
x_136 = lean_box(0);
x_11 = x_136;
x_12 = x_135;
goto block_22;
}
else
{
switch (lean_obj_tag(x_2)) {
case 5:
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_137 = lean_ctor_get(x_132, 1);
lean_inc(x_137);
lean_dec(x_132);
x_138 = lean_ctor_get(x_2, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_2, 1);
lean_inc(x_139);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_140 = l_Lean_ForEachExpr_visit___at_Lean_Compiler_LCNF_Closure_collectExpr___spec__1(x_1, x_138, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_137);
if (lean_obj_tag(x_140) == 0)
{
lean_object* x_141; lean_object* x_142; 
x_141 = lean_ctor_get(x_140, 1);
lean_inc(x_141);
lean_dec(x_140);
x_142 = l_Lean_ForEachExpr_visit___at_Lean_Compiler_LCNF_Closure_collectExpr___spec__1(x_1, x_139, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_141);
if (lean_obj_tag(x_142) == 0)
{
lean_object* x_143; lean_object* x_144; 
x_143 = lean_ctor_get(x_142, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_142, 1);
lean_inc(x_144);
lean_dec(x_142);
x_11 = x_143;
x_12 = x_144;
goto block_22;
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
lean_dec(x_2);
x_145 = lean_ctor_get(x_142, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_142, 1);
lean_inc(x_146);
if (lean_is_exclusive(x_142)) {
 lean_ctor_release(x_142, 0);
 lean_ctor_release(x_142, 1);
 x_147 = x_142;
} else {
 lean_dec_ref(x_142);
 x_147 = lean_box(0);
}
if (lean_is_scalar(x_147)) {
 x_148 = lean_alloc_ctor(1, 2, 0);
} else {
 x_148 = x_147;
}
lean_ctor_set(x_148, 0, x_145);
lean_ctor_set(x_148, 1, x_146);
return x_148;
}
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
lean_dec(x_139);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_149 = lean_ctor_get(x_140, 0);
lean_inc(x_149);
x_150 = lean_ctor_get(x_140, 1);
lean_inc(x_150);
if (lean_is_exclusive(x_140)) {
 lean_ctor_release(x_140, 0);
 lean_ctor_release(x_140, 1);
 x_151 = x_140;
} else {
 lean_dec_ref(x_140);
 x_151 = lean_box(0);
}
if (lean_is_scalar(x_151)) {
 x_152 = lean_alloc_ctor(1, 2, 0);
} else {
 x_152 = x_151;
}
lean_ctor_set(x_152, 0, x_149);
lean_ctor_set(x_152, 1, x_150);
return x_152;
}
}
case 6:
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_153 = lean_ctor_get(x_132, 1);
lean_inc(x_153);
lean_dec(x_132);
x_154 = lean_ctor_get(x_2, 1);
lean_inc(x_154);
x_155 = lean_ctor_get(x_2, 2);
lean_inc(x_155);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_156 = l_Lean_ForEachExpr_visit___at_Lean_Compiler_LCNF_Closure_collectExpr___spec__1(x_1, x_154, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_153);
if (lean_obj_tag(x_156) == 0)
{
lean_object* x_157; lean_object* x_158; 
x_157 = lean_ctor_get(x_156, 1);
lean_inc(x_157);
lean_dec(x_156);
x_158 = l_Lean_ForEachExpr_visit___at_Lean_Compiler_LCNF_Closure_collectExpr___spec__1(x_1, x_155, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_157);
if (lean_obj_tag(x_158) == 0)
{
lean_object* x_159; lean_object* x_160; 
x_159 = lean_ctor_get(x_158, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_158, 1);
lean_inc(x_160);
lean_dec(x_158);
x_11 = x_159;
x_12 = x_160;
goto block_22;
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
lean_dec(x_2);
x_161 = lean_ctor_get(x_158, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_158, 1);
lean_inc(x_162);
if (lean_is_exclusive(x_158)) {
 lean_ctor_release(x_158, 0);
 lean_ctor_release(x_158, 1);
 x_163 = x_158;
} else {
 lean_dec_ref(x_158);
 x_163 = lean_box(0);
}
if (lean_is_scalar(x_163)) {
 x_164 = lean_alloc_ctor(1, 2, 0);
} else {
 x_164 = x_163;
}
lean_ctor_set(x_164, 0, x_161);
lean_ctor_set(x_164, 1, x_162);
return x_164;
}
}
else
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
lean_dec(x_155);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_165 = lean_ctor_get(x_156, 0);
lean_inc(x_165);
x_166 = lean_ctor_get(x_156, 1);
lean_inc(x_166);
if (lean_is_exclusive(x_156)) {
 lean_ctor_release(x_156, 0);
 lean_ctor_release(x_156, 1);
 x_167 = x_156;
} else {
 lean_dec_ref(x_156);
 x_167 = lean_box(0);
}
if (lean_is_scalar(x_167)) {
 x_168 = lean_alloc_ctor(1, 2, 0);
} else {
 x_168 = x_167;
}
lean_ctor_set(x_168, 0, x_165);
lean_ctor_set(x_168, 1, x_166);
return x_168;
}
}
case 7:
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_169 = lean_ctor_get(x_132, 1);
lean_inc(x_169);
lean_dec(x_132);
x_170 = lean_ctor_get(x_2, 1);
lean_inc(x_170);
x_171 = lean_ctor_get(x_2, 2);
lean_inc(x_171);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_172 = l_Lean_ForEachExpr_visit___at_Lean_Compiler_LCNF_Closure_collectExpr___spec__1(x_1, x_170, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_169);
if (lean_obj_tag(x_172) == 0)
{
lean_object* x_173; lean_object* x_174; 
x_173 = lean_ctor_get(x_172, 1);
lean_inc(x_173);
lean_dec(x_172);
x_174 = l_Lean_ForEachExpr_visit___at_Lean_Compiler_LCNF_Closure_collectExpr___spec__1(x_1, x_171, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_173);
if (lean_obj_tag(x_174) == 0)
{
lean_object* x_175; lean_object* x_176; 
x_175 = lean_ctor_get(x_174, 0);
lean_inc(x_175);
x_176 = lean_ctor_get(x_174, 1);
lean_inc(x_176);
lean_dec(x_174);
x_11 = x_175;
x_12 = x_176;
goto block_22;
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
lean_dec(x_2);
x_177 = lean_ctor_get(x_174, 0);
lean_inc(x_177);
x_178 = lean_ctor_get(x_174, 1);
lean_inc(x_178);
if (lean_is_exclusive(x_174)) {
 lean_ctor_release(x_174, 0);
 lean_ctor_release(x_174, 1);
 x_179 = x_174;
} else {
 lean_dec_ref(x_174);
 x_179 = lean_box(0);
}
if (lean_is_scalar(x_179)) {
 x_180 = lean_alloc_ctor(1, 2, 0);
} else {
 x_180 = x_179;
}
lean_ctor_set(x_180, 0, x_177);
lean_ctor_set(x_180, 1, x_178);
return x_180;
}
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; 
lean_dec(x_171);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_181 = lean_ctor_get(x_172, 0);
lean_inc(x_181);
x_182 = lean_ctor_get(x_172, 1);
lean_inc(x_182);
if (lean_is_exclusive(x_172)) {
 lean_ctor_release(x_172, 0);
 lean_ctor_release(x_172, 1);
 x_183 = x_172;
} else {
 lean_dec_ref(x_172);
 x_183 = lean_box(0);
}
if (lean_is_scalar(x_183)) {
 x_184 = lean_alloc_ctor(1, 2, 0);
} else {
 x_184 = x_183;
}
lean_ctor_set(x_184, 0, x_181);
lean_ctor_set(x_184, 1, x_182);
return x_184;
}
}
case 8:
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; 
x_185 = lean_ctor_get(x_132, 1);
lean_inc(x_185);
lean_dec(x_132);
x_186 = lean_ctor_get(x_2, 1);
lean_inc(x_186);
x_187 = lean_ctor_get(x_2, 2);
lean_inc(x_187);
x_188 = lean_ctor_get(x_2, 3);
lean_inc(x_188);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_189 = l_Lean_ForEachExpr_visit___at_Lean_Compiler_LCNF_Closure_collectExpr___spec__1(x_1, x_186, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_185);
if (lean_obj_tag(x_189) == 0)
{
lean_object* x_190; lean_object* x_191; 
x_190 = lean_ctor_get(x_189, 1);
lean_inc(x_190);
lean_dec(x_189);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_191 = l_Lean_ForEachExpr_visit___at_Lean_Compiler_LCNF_Closure_collectExpr___spec__1(x_1, x_187, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_190);
if (lean_obj_tag(x_191) == 0)
{
lean_object* x_192; lean_object* x_193; 
x_192 = lean_ctor_get(x_191, 1);
lean_inc(x_192);
lean_dec(x_191);
x_193 = l_Lean_ForEachExpr_visit___at_Lean_Compiler_LCNF_Closure_collectExpr___spec__1(x_1, x_188, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_192);
if (lean_obj_tag(x_193) == 0)
{
lean_object* x_194; lean_object* x_195; 
x_194 = lean_ctor_get(x_193, 0);
lean_inc(x_194);
x_195 = lean_ctor_get(x_193, 1);
lean_inc(x_195);
lean_dec(x_193);
x_11 = x_194;
x_12 = x_195;
goto block_22;
}
else
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; 
lean_dec(x_2);
x_196 = lean_ctor_get(x_193, 0);
lean_inc(x_196);
x_197 = lean_ctor_get(x_193, 1);
lean_inc(x_197);
if (lean_is_exclusive(x_193)) {
 lean_ctor_release(x_193, 0);
 lean_ctor_release(x_193, 1);
 x_198 = x_193;
} else {
 lean_dec_ref(x_193);
 x_198 = lean_box(0);
}
if (lean_is_scalar(x_198)) {
 x_199 = lean_alloc_ctor(1, 2, 0);
} else {
 x_199 = x_198;
}
lean_ctor_set(x_199, 0, x_196);
lean_ctor_set(x_199, 1, x_197);
return x_199;
}
}
else
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; 
lean_dec(x_188);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_200 = lean_ctor_get(x_191, 0);
lean_inc(x_200);
x_201 = lean_ctor_get(x_191, 1);
lean_inc(x_201);
if (lean_is_exclusive(x_191)) {
 lean_ctor_release(x_191, 0);
 lean_ctor_release(x_191, 1);
 x_202 = x_191;
} else {
 lean_dec_ref(x_191);
 x_202 = lean_box(0);
}
if (lean_is_scalar(x_202)) {
 x_203 = lean_alloc_ctor(1, 2, 0);
} else {
 x_203 = x_202;
}
lean_ctor_set(x_203, 0, x_200);
lean_ctor_set(x_203, 1, x_201);
return x_203;
}
}
else
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; 
lean_dec(x_188);
lean_dec(x_187);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_204 = lean_ctor_get(x_189, 0);
lean_inc(x_204);
x_205 = lean_ctor_get(x_189, 1);
lean_inc(x_205);
if (lean_is_exclusive(x_189)) {
 lean_ctor_release(x_189, 0);
 lean_ctor_release(x_189, 1);
 x_206 = x_189;
} else {
 lean_dec_ref(x_189);
 x_206 = lean_box(0);
}
if (lean_is_scalar(x_206)) {
 x_207 = lean_alloc_ctor(1, 2, 0);
} else {
 x_207 = x_206;
}
lean_ctor_set(x_207, 0, x_204);
lean_ctor_set(x_207, 1, x_205);
return x_207;
}
}
case 10:
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; 
x_208 = lean_ctor_get(x_132, 1);
lean_inc(x_208);
lean_dec(x_132);
x_209 = lean_ctor_get(x_2, 1);
lean_inc(x_209);
x_210 = l_Lean_ForEachExpr_visit___at_Lean_Compiler_LCNF_Closure_collectExpr___spec__1(x_1, x_209, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_208);
if (lean_obj_tag(x_210) == 0)
{
lean_object* x_211; lean_object* x_212; 
x_211 = lean_ctor_get(x_210, 0);
lean_inc(x_211);
x_212 = lean_ctor_get(x_210, 1);
lean_inc(x_212);
lean_dec(x_210);
x_11 = x_211;
x_12 = x_212;
goto block_22;
}
else
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; 
lean_dec(x_2);
x_213 = lean_ctor_get(x_210, 0);
lean_inc(x_213);
x_214 = lean_ctor_get(x_210, 1);
lean_inc(x_214);
if (lean_is_exclusive(x_210)) {
 lean_ctor_release(x_210, 0);
 lean_ctor_release(x_210, 1);
 x_215 = x_210;
} else {
 lean_dec_ref(x_210);
 x_215 = lean_box(0);
}
if (lean_is_scalar(x_215)) {
 x_216 = lean_alloc_ctor(1, 2, 0);
} else {
 x_216 = x_215;
}
lean_ctor_set(x_216, 0, x_213);
lean_ctor_set(x_216, 1, x_214);
return x_216;
}
}
case 11:
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; 
x_217 = lean_ctor_get(x_132, 1);
lean_inc(x_217);
lean_dec(x_132);
x_218 = lean_ctor_get(x_2, 2);
lean_inc(x_218);
x_219 = l_Lean_ForEachExpr_visit___at_Lean_Compiler_LCNF_Closure_collectExpr___spec__1(x_1, x_218, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_217);
if (lean_obj_tag(x_219) == 0)
{
lean_object* x_220; lean_object* x_221; 
x_220 = lean_ctor_get(x_219, 0);
lean_inc(x_220);
x_221 = lean_ctor_get(x_219, 1);
lean_inc(x_221);
lean_dec(x_219);
x_11 = x_220;
x_12 = x_221;
goto block_22;
}
else
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; 
lean_dec(x_2);
x_222 = lean_ctor_get(x_219, 0);
lean_inc(x_222);
x_223 = lean_ctor_get(x_219, 1);
lean_inc(x_223);
if (lean_is_exclusive(x_219)) {
 lean_ctor_release(x_219, 0);
 lean_ctor_release(x_219, 1);
 x_224 = x_219;
} else {
 lean_dec_ref(x_219);
 x_224 = lean_box(0);
}
if (lean_is_scalar(x_224)) {
 x_225 = lean_alloc_ctor(1, 2, 0);
} else {
 x_225 = x_224;
}
lean_ctor_set(x_225, 0, x_222);
lean_ctor_set(x_225, 1, x_223);
return x_225;
}
}
default: 
{
lean_object* x_226; lean_object* x_227; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_226 = lean_ctor_get(x_132, 1);
lean_inc(x_226);
lean_dec(x_132);
x_227 = lean_box(0);
x_11 = x_227;
x_12 = x_226;
goto block_22;
}
}
}
}
else
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_228 = lean_ctor_get(x_132, 0);
lean_inc(x_228);
x_229 = lean_ctor_get(x_132, 1);
lean_inc(x_229);
if (lean_is_exclusive(x_132)) {
 lean_ctor_release(x_132, 0);
 lean_ctor_release(x_132, 1);
 x_230 = x_132;
} else {
 lean_dec_ref(x_132);
 x_230 = lean_box(0);
}
if (lean_is_scalar(x_230)) {
 x_231 = lean_alloc_ctor(1, 2, 0);
} else {
 x_231 = x_230;
}
lean_ctor_set(x_231, 0, x_228);
lean_ctor_set(x_231, 1, x_229);
return x_231;
}
}
else
{
lean_object* x_232; lean_object* x_233; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_232 = lean_ctor_get(x_131, 0);
lean_inc(x_232);
lean_dec(x_131);
x_233 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_233, 0, x_232);
lean_ctor_set(x_233, 1, x_130);
return x_233;
}
}
block_22:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_13 = lean_st_ref_take(x_3, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
lean_inc(x_11);
x_16 = l_Lean_HashMap_insert___at_Lean_ForEachExpr_visit___spec__3(x_14, x_2, x_11);
x_17 = lean_st_ref_set(x_3, x_16, x_15);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_17, 0);
lean_dec(x_19);
lean_ctor_set(x_17, 0, x_11);
return x_17;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_11);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Closure_collectExpr___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec(x_1);
x_10 = l_Lean_Compiler_LCNF_Closure_collectFVar(x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_10, 0);
lean_dec(x_12);
x_13 = 1;
x_14 = lean_box(x_13);
lean_ctor_set(x_10, 0, x_14);
return x_10;
}
else
{
lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_10, 1);
lean_inc(x_15);
lean_dec(x_10);
x_16 = 1;
x_17 = lean_box(x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_15);
return x_18;
}
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_10);
if (x_19 == 0)
{
return x_10;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_10, 0);
x_21 = lean_ctor_get(x_10, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_10);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
else
{
uint8_t x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_23 = 1;
x_24 = lean_box(x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_8);
return x_25;
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Closure_collectExpr___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_mkHashMapImp___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Closure_collectExpr___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Closure_collectExpr___lambda__1), 8, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Closure_collectExpr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = l_Lean_Compiler_LCNF_Closure_collectExpr___closed__1;
x_10 = lean_st_mk_ref(x_9, x_8);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Compiler_LCNF_Closure_collectExpr___closed__2;
x_14 = l_Lean_ForEachExpr_visit___at_Lean_Compiler_LCNF_Closure_collectExpr___spec__1(x_13, x_1, x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_st_ref_get(x_11, x_16);
lean_dec(x_11);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_17, 0);
lean_dec(x_19);
lean_ctor_set(x_17, 0, x_15);
return x_17;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_15);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
else
{
uint8_t x_22; 
lean_dec(x_11);
x_22 = !lean_is_exclusive(x_14);
if (x_22 == 0)
{
return x_14;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_14, 0);
x_24 = lean_ctor_get(x_14, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_14);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_findCore___at_Lean_Compiler_LCNF_Closure_collectFVar___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_1, 2);
x_7 = lean_ctor_get(x_1, 3);
x_8 = l_Lean_Name_quickCmp(x_2, x_5);
switch (x_8) {
case 0:
{
x_1 = x_4;
goto _start;
}
case 1:
{
lean_object* x_10; lean_object* x_11; 
lean_inc(x_6);
lean_inc(x_5);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_5);
lean_ctor_set(x_10, 1, x_6);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
default: 
{
x_1 = x_7;
goto _start;
}
}
}
}
}
static lean_object* _init_l_panic___at_Lean_Compiler_LCNF_Closure_collectFVar___spec__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Core_instMonadCoreM;
x_2 = l_ReaderT_instMonadReaderT___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_panic___at_Lean_Compiler_LCNF_Closure_collectFVar___spec__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_panic___at_Lean_Compiler_LCNF_Closure_collectFVar___spec__2___closed__1;
x_2 = l_ReaderT_instMonadReaderT___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_panic___at_Lean_Compiler_LCNF_Closure_collectFVar___spec__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_panic___at_Lean_Compiler_LCNF_Closure_collectFVar___spec__2___closed__2;
x_2 = l_ReaderT_instMonadReaderT___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_panic___at_Lean_Compiler_LCNF_Closure_collectFVar___spec__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_panic___at_Lean_Compiler_LCNF_Closure_collectFVar___spec__2___closed__3;
x_2 = l_instInhabitedPUnit;
x_3 = l_instInhabited___rarg(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_panic___at_Lean_Compiler_LCNF_Closure_collectFVar___spec__2___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_panic___at_Lean_Compiler_LCNF_Closure_collectFVar___spec__2___closed__4;
x_2 = lean_alloc_closure((void*)(l_instInhabitedReaderT___rarg___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_Compiler_LCNF_Closure_collectFVar___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = l_panic___at_Lean_Compiler_LCNF_Closure_collectFVar___spec__2___closed__5;
x_10 = lean_panic_fn(x_9, x_1);
x_11 = lean_apply_7(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Closure_collectFVar___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.Compiler.LCNF.Closure", 26);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Closure_collectFVar___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.Compiler.LCNF.Closure.collectFVar", 38);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Closure_collectFVar___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("unreachable code has been reached", 33);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Closure_collectFVar___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Compiler_LCNF_Closure_collectFVar___closed__1;
x_2 = l_Lean_Compiler_LCNF_Closure_collectFVar___closed__2;
x_3 = lean_unsigned_to_nat(127u);
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
x_14 = l_Lean_RBNode_findCore___at_Lean_Compiler_LCNF_Closure_collectFVar___spec__1(x_13, x_1);
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
lean_inc(x_1);
x_23 = l_Lean_Compiler_LCNF_findFunDecl_x3f(x_1, x_4, x_5, x_6, x_7, x_17);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
lean_inc(x_1);
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
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = l_Lean_Compiler_LCNF_Closure_collectFVar___closed__4;
x_33 = l_panic___at_Lean_Compiler_LCNF_Closure_collectFVar___spec__2(x_32, x_2, x_3, x_4, x_5, x_6, x_7, x_31);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_34 = lean_ctor_get(x_30, 0);
lean_inc(x_34);
lean_dec(x_30);
x_35 = lean_ctor_get(x_29, 1);
lean_inc(x_35);
lean_dec(x_29);
x_36 = lean_ctor_get(x_34, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_34, 1);
lean_inc(x_37);
x_38 = lean_ctor_get(x_34, 2);
lean_inc(x_38);
x_39 = lean_ctor_get(x_34, 3);
lean_inc(x_39);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_38);
x_40 = l_Lean_Compiler_LCNF_Closure_collectExpr(x_38, x_2, x_3, x_4, x_5, x_6, x_7, x_35);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
lean_dec(x_40);
x_42 = lean_ctor_get(x_2, 1);
lean_inc(x_42);
lean_inc(x_36);
x_43 = lean_apply_1(x_42, x_36);
x_44 = lean_unbox(x_43);
lean_dec(x_43);
if (x_44 == 0)
{
lean_object* x_45; 
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_36);
lean_inc(x_3);
x_45 = l_Lean_Compiler_LCNF_Closure_collectExpr(x_39, x_2, x_3, x_4, x_5, x_6, x_7, x_41);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_46 = lean_ctor_get(x_45, 1);
lean_inc(x_46);
lean_dec(x_45);
x_47 = lean_st_ref_take(x_3, x_46);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
x_50 = !lean_is_exclusive(x_48);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_51 = lean_ctor_get(x_48, 2);
x_52 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_52, 0, x_34);
x_53 = lean_array_push(x_51, x_52);
lean_ctor_set(x_48, 2, x_53);
x_54 = lean_st_ref_set(x_3, x_48, x_49);
lean_dec(x_3);
x_55 = !lean_is_exclusive(x_54);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_54, 0);
lean_dec(x_56);
x_57 = lean_box(0);
lean_ctor_set(x_54, 0, x_57);
return x_54;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_54, 1);
lean_inc(x_58);
lean_dec(x_54);
x_59 = lean_box(0);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_58);
return x_60;
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_61 = lean_ctor_get(x_48, 0);
x_62 = lean_ctor_get(x_48, 1);
x_63 = lean_ctor_get(x_48, 2);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_48);
x_64 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_64, 0, x_34);
x_65 = lean_array_push(x_63, x_64);
x_66 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_66, 0, x_61);
lean_ctor_set(x_66, 1, x_62);
lean_ctor_set(x_66, 2, x_65);
x_67 = lean_st_ref_set(x_3, x_66, x_49);
lean_dec(x_3);
x_68 = lean_ctor_get(x_67, 1);
lean_inc(x_68);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 lean_ctor_release(x_67, 1);
 x_69 = x_67;
} else {
 lean_dec_ref(x_67);
 x_69 = lean_box(0);
}
x_70 = lean_box(0);
if (lean_is_scalar(x_69)) {
 x_71 = lean_alloc_ctor(0, 2, 0);
} else {
 x_71 = x_69;
}
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_68);
return x_71;
}
}
else
{
uint8_t x_72; 
lean_dec(x_34);
lean_dec(x_3);
x_72 = !lean_is_exclusive(x_45);
if (x_72 == 0)
{
return x_45;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_45, 0);
x_74 = lean_ctor_get(x_45, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_45);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
return x_75;
}
}
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; 
lean_dec(x_39);
lean_dec(x_34);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_76 = lean_st_ref_take(x_3, x_41);
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec(x_76);
x_79 = !lean_is_exclusive(x_77);
if (x_79 == 0)
{
lean_object* x_80; uint8_t x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; 
x_80 = lean_ctor_get(x_77, 1);
x_81 = 0;
x_82 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_82, 0, x_36);
lean_ctor_set(x_82, 1, x_37);
lean_ctor_set(x_82, 2, x_38);
lean_ctor_set_uint8(x_82, sizeof(void*)*3, x_81);
x_83 = lean_array_push(x_80, x_82);
lean_ctor_set(x_77, 1, x_83);
x_84 = lean_st_ref_set(x_3, x_77, x_78);
lean_dec(x_3);
x_85 = !lean_is_exclusive(x_84);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; 
x_86 = lean_ctor_get(x_84, 0);
lean_dec(x_86);
x_87 = lean_box(0);
lean_ctor_set(x_84, 0, x_87);
return x_84;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_84, 1);
lean_inc(x_88);
lean_dec(x_84);
x_89 = lean_box(0);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_88);
return x_90;
}
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; uint8_t x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_91 = lean_ctor_get(x_77, 0);
x_92 = lean_ctor_get(x_77, 1);
x_93 = lean_ctor_get(x_77, 2);
lean_inc(x_93);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_77);
x_94 = 0;
x_95 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_95, 0, x_36);
lean_ctor_set(x_95, 1, x_37);
lean_ctor_set(x_95, 2, x_38);
lean_ctor_set_uint8(x_95, sizeof(void*)*3, x_94);
x_96 = lean_array_push(x_92, x_95);
x_97 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_97, 0, x_91);
lean_ctor_set(x_97, 1, x_96);
lean_ctor_set(x_97, 2, x_93);
x_98 = lean_st_ref_set(x_3, x_97, x_78);
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
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_34);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_103 = !lean_is_exclusive(x_40);
if (x_103 == 0)
{
return x_40;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_104 = lean_ctor_get(x_40, 0);
x_105 = lean_ctor_get(x_40, 1);
lean_inc(x_105);
lean_inc(x_104);
lean_dec(x_40);
x_106 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_106, 0, x_104);
lean_ctor_set(x_106, 1, x_105);
return x_106;
}
}
}
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
lean_dec(x_1);
x_107 = lean_ctor_get(x_26, 1);
lean_inc(x_107);
lean_dec(x_26);
x_108 = lean_ctor_get(x_27, 0);
lean_inc(x_108);
lean_dec(x_27);
x_109 = lean_ctor_get(x_108, 2);
lean_inc(x_109);
lean_inc(x_3);
x_110 = l_Lean_Compiler_LCNF_Closure_collectExpr(x_109, x_2, x_3, x_4, x_5, x_6, x_7, x_107);
if (lean_obj_tag(x_110) == 0)
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; uint8_t x_115; 
x_111 = lean_ctor_get(x_110, 1);
lean_inc(x_111);
lean_dec(x_110);
x_112 = lean_st_ref_take(x_3, x_111);
x_113 = lean_ctor_get(x_112, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_112, 1);
lean_inc(x_114);
lean_dec(x_112);
x_115 = !lean_is_exclusive(x_113);
if (x_115 == 0)
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; uint8_t x_119; 
x_116 = lean_ctor_get(x_113, 1);
x_117 = lean_array_push(x_116, x_108);
lean_ctor_set(x_113, 1, x_117);
x_118 = lean_st_ref_set(x_3, x_113, x_114);
lean_dec(x_3);
x_119 = !lean_is_exclusive(x_118);
if (x_119 == 0)
{
lean_object* x_120; lean_object* x_121; 
x_120 = lean_ctor_get(x_118, 0);
lean_dec(x_120);
x_121 = lean_box(0);
lean_ctor_set(x_118, 0, x_121);
return x_118;
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_122 = lean_ctor_get(x_118, 1);
lean_inc(x_122);
lean_dec(x_118);
x_123 = lean_box(0);
x_124 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_124, 0, x_123);
lean_ctor_set(x_124, 1, x_122);
return x_124;
}
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_125 = lean_ctor_get(x_113, 0);
x_126 = lean_ctor_get(x_113, 1);
x_127 = lean_ctor_get(x_113, 2);
lean_inc(x_127);
lean_inc(x_126);
lean_inc(x_125);
lean_dec(x_113);
x_128 = lean_array_push(x_126, x_108);
x_129 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_129, 0, x_125);
lean_ctor_set(x_129, 1, x_128);
lean_ctor_set(x_129, 2, x_127);
x_130 = lean_st_ref_set(x_3, x_129, x_114);
lean_dec(x_3);
x_131 = lean_ctor_get(x_130, 1);
lean_inc(x_131);
if (lean_is_exclusive(x_130)) {
 lean_ctor_release(x_130, 0);
 lean_ctor_release(x_130, 1);
 x_132 = x_130;
} else {
 lean_dec_ref(x_130);
 x_132 = lean_box(0);
}
x_133 = lean_box(0);
if (lean_is_scalar(x_132)) {
 x_134 = lean_alloc_ctor(0, 2, 0);
} else {
 x_134 = x_132;
}
lean_ctor_set(x_134, 0, x_133);
lean_ctor_set(x_134, 1, x_131);
return x_134;
}
}
else
{
uint8_t x_135; 
lean_dec(x_108);
lean_dec(x_3);
x_135 = !lean_is_exclusive(x_110);
if (x_135 == 0)
{
return x_110;
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_136 = lean_ctor_get(x_110, 0);
x_137 = lean_ctor_get(x_110, 1);
lean_inc(x_137);
lean_inc(x_136);
lean_dec(x_110);
x_138 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_138, 0, x_136);
lean_ctor_set(x_138, 1, x_137);
return x_138;
}
}
}
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; uint8_t x_146; 
lean_dec(x_1);
x_139 = lean_ctor_get(x_24, 0);
lean_inc(x_139);
lean_dec(x_24);
x_140 = lean_ctor_get(x_23, 1);
lean_inc(x_140);
lean_dec(x_23);
x_141 = lean_ctor_get(x_2, 1);
lean_inc(x_141);
x_142 = lean_ctor_get(x_139, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_139, 1);
lean_inc(x_143);
x_144 = lean_ctor_get(x_139, 3);
lean_inc(x_144);
lean_inc(x_142);
x_145 = lean_apply_1(x_141, x_142);
x_146 = lean_unbox(x_145);
lean_dec(x_145);
if (x_146 == 0)
{
lean_object* x_147; 
lean_dec(x_144);
lean_dec(x_143);
lean_dec(x_142);
lean_inc(x_3);
lean_inc(x_139);
x_147 = l_Lean_Compiler_LCNF_Closure_collectFunDecl(x_139, x_2, x_3, x_4, x_5, x_6, x_7, x_140);
if (lean_obj_tag(x_147) == 0)
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; uint8_t x_152; 
x_148 = lean_ctor_get(x_147, 1);
lean_inc(x_148);
lean_dec(x_147);
x_149 = lean_st_ref_take(x_3, x_148);
x_150 = lean_ctor_get(x_149, 0);
lean_inc(x_150);
x_151 = lean_ctor_get(x_149, 1);
lean_inc(x_151);
lean_dec(x_149);
x_152 = !lean_is_exclusive(x_150);
if (x_152 == 0)
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; uint8_t x_157; 
x_153 = lean_ctor_get(x_150, 2);
x_154 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_154, 0, x_139);
x_155 = lean_array_push(x_153, x_154);
lean_ctor_set(x_150, 2, x_155);
x_156 = lean_st_ref_set(x_3, x_150, x_151);
lean_dec(x_3);
x_157 = !lean_is_exclusive(x_156);
if (x_157 == 0)
{
lean_object* x_158; lean_object* x_159; 
x_158 = lean_ctor_get(x_156, 0);
lean_dec(x_158);
x_159 = lean_box(0);
lean_ctor_set(x_156, 0, x_159);
return x_156;
}
else
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_160 = lean_ctor_get(x_156, 1);
lean_inc(x_160);
lean_dec(x_156);
x_161 = lean_box(0);
x_162 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_162, 0, x_161);
lean_ctor_set(x_162, 1, x_160);
return x_162;
}
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_163 = lean_ctor_get(x_150, 0);
x_164 = lean_ctor_get(x_150, 1);
x_165 = lean_ctor_get(x_150, 2);
lean_inc(x_165);
lean_inc(x_164);
lean_inc(x_163);
lean_dec(x_150);
x_166 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_166, 0, x_139);
x_167 = lean_array_push(x_165, x_166);
x_168 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_168, 0, x_163);
lean_ctor_set(x_168, 1, x_164);
lean_ctor_set(x_168, 2, x_167);
x_169 = lean_st_ref_set(x_3, x_168, x_151);
lean_dec(x_3);
x_170 = lean_ctor_get(x_169, 1);
lean_inc(x_170);
if (lean_is_exclusive(x_169)) {
 lean_ctor_release(x_169, 0);
 lean_ctor_release(x_169, 1);
 x_171 = x_169;
} else {
 lean_dec_ref(x_169);
 x_171 = lean_box(0);
}
x_172 = lean_box(0);
if (lean_is_scalar(x_171)) {
 x_173 = lean_alloc_ctor(0, 2, 0);
} else {
 x_173 = x_171;
}
lean_ctor_set(x_173, 0, x_172);
lean_ctor_set(x_173, 1, x_170);
return x_173;
}
}
else
{
uint8_t x_174; 
lean_dec(x_139);
lean_dec(x_3);
x_174 = !lean_is_exclusive(x_147);
if (x_174 == 0)
{
return x_147;
}
else
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; 
x_175 = lean_ctor_get(x_147, 0);
x_176 = lean_ctor_get(x_147, 1);
lean_inc(x_176);
lean_inc(x_175);
lean_dec(x_147);
x_177 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_177, 0, x_175);
lean_ctor_set(x_177, 1, x_176);
return x_177;
}
}
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; uint8_t x_181; 
lean_dec(x_139);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_178 = lean_st_ref_take(x_3, x_140);
x_179 = lean_ctor_get(x_178, 0);
lean_inc(x_179);
x_180 = lean_ctor_get(x_178, 1);
lean_inc(x_180);
lean_dec(x_178);
x_181 = !lean_is_exclusive(x_179);
if (x_181 == 0)
{
lean_object* x_182; uint8_t x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; uint8_t x_187; 
x_182 = lean_ctor_get(x_179, 1);
x_183 = 0;
x_184 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_184, 0, x_142);
lean_ctor_set(x_184, 1, x_143);
lean_ctor_set(x_184, 2, x_144);
lean_ctor_set_uint8(x_184, sizeof(void*)*3, x_183);
x_185 = lean_array_push(x_182, x_184);
lean_ctor_set(x_179, 1, x_185);
x_186 = lean_st_ref_set(x_3, x_179, x_180);
lean_dec(x_3);
x_187 = !lean_is_exclusive(x_186);
if (x_187 == 0)
{
lean_object* x_188; lean_object* x_189; 
x_188 = lean_ctor_get(x_186, 0);
lean_dec(x_188);
x_189 = lean_box(0);
lean_ctor_set(x_186, 0, x_189);
return x_186;
}
else
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; 
x_190 = lean_ctor_get(x_186, 1);
lean_inc(x_190);
lean_dec(x_186);
x_191 = lean_box(0);
x_192 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_192, 0, x_191);
lean_ctor_set(x_192, 1, x_190);
return x_192;
}
}
else
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; uint8_t x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; 
x_193 = lean_ctor_get(x_179, 0);
x_194 = lean_ctor_get(x_179, 1);
x_195 = lean_ctor_get(x_179, 2);
lean_inc(x_195);
lean_inc(x_194);
lean_inc(x_193);
lean_dec(x_179);
x_196 = 0;
x_197 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_197, 0, x_142);
lean_ctor_set(x_197, 1, x_143);
lean_ctor_set(x_197, 2, x_144);
lean_ctor_set_uint8(x_197, sizeof(void*)*3, x_196);
x_198 = lean_array_push(x_194, x_197);
x_199 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_199, 0, x_193);
lean_ctor_set(x_199, 1, x_198);
lean_ctor_set(x_199, 2, x_195);
x_200 = lean_st_ref_set(x_3, x_199, x_180);
lean_dec(x_3);
x_201 = lean_ctor_get(x_200, 1);
lean_inc(x_201);
if (lean_is_exclusive(x_200)) {
 lean_ctor_release(x_200, 0);
 lean_ctor_release(x_200, 1);
 x_202 = x_200;
} else {
 lean_dec_ref(x_200);
 x_202 = lean_box(0);
}
x_203 = lean_box(0);
if (lean_is_scalar(x_202)) {
 x_204 = lean_alloc_ctor(0, 2, 0);
} else {
 x_204 = x_202;
}
lean_ctor_set(x_204, 0, x_203);
lean_ctor_set(x_204, 1, x_201);
return x_204;
}
}
}
}
}
else
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; uint8_t x_208; 
x_205 = lean_ctor_get(x_15, 1);
lean_inc(x_205);
lean_dec(x_15);
x_206 = lean_ctor_get(x_2, 0);
lean_inc(x_206);
lean_inc(x_1);
x_207 = lean_apply_1(x_206, x_1);
x_208 = lean_unbox(x_207);
lean_dec(x_207);
if (x_208 == 0)
{
lean_object* x_209; lean_object* x_210; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_209 = lean_box(0);
x_210 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_210, 0, x_209);
lean_ctor_set(x_210, 1, x_205);
return x_210;
}
else
{
lean_object* x_211; lean_object* x_212; 
lean_inc(x_1);
x_211 = l_Lean_Compiler_LCNF_findFunDecl_x3f(x_1, x_4, x_5, x_6, x_7, x_205);
x_212 = lean_ctor_get(x_211, 0);
lean_inc(x_212);
if (lean_obj_tag(x_212) == 0)
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; 
x_213 = lean_ctor_get(x_211, 1);
lean_inc(x_213);
lean_dec(x_211);
lean_inc(x_1);
x_214 = l_Lean_Compiler_LCNF_findParam_x3f(x_1, x_4, x_5, x_6, x_7, x_213);
x_215 = lean_ctor_get(x_214, 0);
lean_inc(x_215);
if (lean_obj_tag(x_215) == 0)
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; 
x_216 = lean_ctor_get(x_214, 1);
lean_inc(x_216);
lean_dec(x_214);
x_217 = l_Lean_Compiler_LCNF_findLetDecl_x3f(x_1, x_4, x_5, x_6, x_7, x_216);
x_218 = lean_ctor_get(x_217, 0);
lean_inc(x_218);
if (lean_obj_tag(x_218) == 0)
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; 
x_219 = lean_ctor_get(x_217, 1);
lean_inc(x_219);
lean_dec(x_217);
x_220 = l_Lean_Compiler_LCNF_Closure_collectFVar___closed__4;
x_221 = l_panic___at_Lean_Compiler_LCNF_Closure_collectFVar___spec__2(x_220, x_2, x_3, x_4, x_5, x_6, x_7, x_219);
return x_221;
}
else
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; 
x_222 = lean_ctor_get(x_218, 0);
lean_inc(x_222);
lean_dec(x_218);
x_223 = lean_ctor_get(x_217, 1);
lean_inc(x_223);
lean_dec(x_217);
x_224 = lean_ctor_get(x_222, 0);
lean_inc(x_224);
x_225 = lean_ctor_get(x_222, 1);
lean_inc(x_225);
x_226 = lean_ctor_get(x_222, 2);
lean_inc(x_226);
x_227 = lean_ctor_get(x_222, 3);
lean_inc(x_227);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_226);
x_228 = l_Lean_Compiler_LCNF_Closure_collectExpr(x_226, x_2, x_3, x_4, x_5, x_6, x_7, x_223);
if (lean_obj_tag(x_228) == 0)
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; uint8_t x_232; 
x_229 = lean_ctor_get(x_228, 1);
lean_inc(x_229);
lean_dec(x_228);
x_230 = lean_ctor_get(x_2, 1);
lean_inc(x_230);
lean_inc(x_224);
x_231 = lean_apply_1(x_230, x_224);
x_232 = lean_unbox(x_231);
lean_dec(x_231);
if (x_232 == 0)
{
lean_object* x_233; 
lean_dec(x_226);
lean_dec(x_225);
lean_dec(x_224);
lean_inc(x_3);
x_233 = l_Lean_Compiler_LCNF_Closure_collectExpr(x_227, x_2, x_3, x_4, x_5, x_6, x_7, x_229);
if (lean_obj_tag(x_233) == 0)
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; 
x_234 = lean_ctor_get(x_233, 1);
lean_inc(x_234);
lean_dec(x_233);
x_235 = lean_st_ref_take(x_3, x_234);
x_236 = lean_ctor_get(x_235, 0);
lean_inc(x_236);
x_237 = lean_ctor_get(x_235, 1);
lean_inc(x_237);
lean_dec(x_235);
x_238 = lean_ctor_get(x_236, 0);
lean_inc(x_238);
x_239 = lean_ctor_get(x_236, 1);
lean_inc(x_239);
x_240 = lean_ctor_get(x_236, 2);
lean_inc(x_240);
if (lean_is_exclusive(x_236)) {
 lean_ctor_release(x_236, 0);
 lean_ctor_release(x_236, 1);
 lean_ctor_release(x_236, 2);
 x_241 = x_236;
} else {
 lean_dec_ref(x_236);
 x_241 = lean_box(0);
}
x_242 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_242, 0, x_222);
x_243 = lean_array_push(x_240, x_242);
if (lean_is_scalar(x_241)) {
 x_244 = lean_alloc_ctor(0, 3, 0);
} else {
 x_244 = x_241;
}
lean_ctor_set(x_244, 0, x_238);
lean_ctor_set(x_244, 1, x_239);
lean_ctor_set(x_244, 2, x_243);
x_245 = lean_st_ref_set(x_3, x_244, x_237);
lean_dec(x_3);
x_246 = lean_ctor_get(x_245, 1);
lean_inc(x_246);
if (lean_is_exclusive(x_245)) {
 lean_ctor_release(x_245, 0);
 lean_ctor_release(x_245, 1);
 x_247 = x_245;
} else {
 lean_dec_ref(x_245);
 x_247 = lean_box(0);
}
x_248 = lean_box(0);
if (lean_is_scalar(x_247)) {
 x_249 = lean_alloc_ctor(0, 2, 0);
} else {
 x_249 = x_247;
}
lean_ctor_set(x_249, 0, x_248);
lean_ctor_set(x_249, 1, x_246);
return x_249;
}
else
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; 
lean_dec(x_222);
lean_dec(x_3);
x_250 = lean_ctor_get(x_233, 0);
lean_inc(x_250);
x_251 = lean_ctor_get(x_233, 1);
lean_inc(x_251);
if (lean_is_exclusive(x_233)) {
 lean_ctor_release(x_233, 0);
 lean_ctor_release(x_233, 1);
 x_252 = x_233;
} else {
 lean_dec_ref(x_233);
 x_252 = lean_box(0);
}
if (lean_is_scalar(x_252)) {
 x_253 = lean_alloc_ctor(1, 2, 0);
} else {
 x_253 = x_252;
}
lean_ctor_set(x_253, 0, x_250);
lean_ctor_set(x_253, 1, x_251);
return x_253;
}
}
else
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; uint8_t x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; 
lean_dec(x_227);
lean_dec(x_222);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_254 = lean_st_ref_take(x_3, x_229);
x_255 = lean_ctor_get(x_254, 0);
lean_inc(x_255);
x_256 = lean_ctor_get(x_254, 1);
lean_inc(x_256);
lean_dec(x_254);
x_257 = lean_ctor_get(x_255, 0);
lean_inc(x_257);
x_258 = lean_ctor_get(x_255, 1);
lean_inc(x_258);
x_259 = lean_ctor_get(x_255, 2);
lean_inc(x_259);
if (lean_is_exclusive(x_255)) {
 lean_ctor_release(x_255, 0);
 lean_ctor_release(x_255, 1);
 lean_ctor_release(x_255, 2);
 x_260 = x_255;
} else {
 lean_dec_ref(x_255);
 x_260 = lean_box(0);
}
x_261 = 0;
x_262 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_262, 0, x_224);
lean_ctor_set(x_262, 1, x_225);
lean_ctor_set(x_262, 2, x_226);
lean_ctor_set_uint8(x_262, sizeof(void*)*3, x_261);
x_263 = lean_array_push(x_258, x_262);
if (lean_is_scalar(x_260)) {
 x_264 = lean_alloc_ctor(0, 3, 0);
} else {
 x_264 = x_260;
}
lean_ctor_set(x_264, 0, x_257);
lean_ctor_set(x_264, 1, x_263);
lean_ctor_set(x_264, 2, x_259);
x_265 = lean_st_ref_set(x_3, x_264, x_256);
lean_dec(x_3);
x_266 = lean_ctor_get(x_265, 1);
lean_inc(x_266);
if (lean_is_exclusive(x_265)) {
 lean_ctor_release(x_265, 0);
 lean_ctor_release(x_265, 1);
 x_267 = x_265;
} else {
 lean_dec_ref(x_265);
 x_267 = lean_box(0);
}
x_268 = lean_box(0);
if (lean_is_scalar(x_267)) {
 x_269 = lean_alloc_ctor(0, 2, 0);
} else {
 x_269 = x_267;
}
lean_ctor_set(x_269, 0, x_268);
lean_ctor_set(x_269, 1, x_266);
return x_269;
}
}
else
{
lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; 
lean_dec(x_227);
lean_dec(x_226);
lean_dec(x_225);
lean_dec(x_224);
lean_dec(x_222);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_270 = lean_ctor_get(x_228, 0);
lean_inc(x_270);
x_271 = lean_ctor_get(x_228, 1);
lean_inc(x_271);
if (lean_is_exclusive(x_228)) {
 lean_ctor_release(x_228, 0);
 lean_ctor_release(x_228, 1);
 x_272 = x_228;
} else {
 lean_dec_ref(x_228);
 x_272 = lean_box(0);
}
if (lean_is_scalar(x_272)) {
 x_273 = lean_alloc_ctor(1, 2, 0);
} else {
 x_273 = x_272;
}
lean_ctor_set(x_273, 0, x_270);
lean_ctor_set(x_273, 1, x_271);
return x_273;
}
}
}
else
{
lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; 
lean_dec(x_1);
x_274 = lean_ctor_get(x_214, 1);
lean_inc(x_274);
lean_dec(x_214);
x_275 = lean_ctor_get(x_215, 0);
lean_inc(x_275);
lean_dec(x_215);
x_276 = lean_ctor_get(x_275, 2);
lean_inc(x_276);
lean_inc(x_3);
x_277 = l_Lean_Compiler_LCNF_Closure_collectExpr(x_276, x_2, x_3, x_4, x_5, x_6, x_7, x_274);
if (lean_obj_tag(x_277) == 0)
{
lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; 
x_278 = lean_ctor_get(x_277, 1);
lean_inc(x_278);
lean_dec(x_277);
x_279 = lean_st_ref_take(x_3, x_278);
x_280 = lean_ctor_get(x_279, 0);
lean_inc(x_280);
x_281 = lean_ctor_get(x_279, 1);
lean_inc(x_281);
lean_dec(x_279);
x_282 = lean_ctor_get(x_280, 0);
lean_inc(x_282);
x_283 = lean_ctor_get(x_280, 1);
lean_inc(x_283);
x_284 = lean_ctor_get(x_280, 2);
lean_inc(x_284);
if (lean_is_exclusive(x_280)) {
 lean_ctor_release(x_280, 0);
 lean_ctor_release(x_280, 1);
 lean_ctor_release(x_280, 2);
 x_285 = x_280;
} else {
 lean_dec_ref(x_280);
 x_285 = lean_box(0);
}
x_286 = lean_array_push(x_283, x_275);
if (lean_is_scalar(x_285)) {
 x_287 = lean_alloc_ctor(0, 3, 0);
} else {
 x_287 = x_285;
}
lean_ctor_set(x_287, 0, x_282);
lean_ctor_set(x_287, 1, x_286);
lean_ctor_set(x_287, 2, x_284);
x_288 = lean_st_ref_set(x_3, x_287, x_281);
lean_dec(x_3);
x_289 = lean_ctor_get(x_288, 1);
lean_inc(x_289);
if (lean_is_exclusive(x_288)) {
 lean_ctor_release(x_288, 0);
 lean_ctor_release(x_288, 1);
 x_290 = x_288;
} else {
 lean_dec_ref(x_288);
 x_290 = lean_box(0);
}
x_291 = lean_box(0);
if (lean_is_scalar(x_290)) {
 x_292 = lean_alloc_ctor(0, 2, 0);
} else {
 x_292 = x_290;
}
lean_ctor_set(x_292, 0, x_291);
lean_ctor_set(x_292, 1, x_289);
return x_292;
}
else
{
lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; 
lean_dec(x_275);
lean_dec(x_3);
x_293 = lean_ctor_get(x_277, 0);
lean_inc(x_293);
x_294 = lean_ctor_get(x_277, 1);
lean_inc(x_294);
if (lean_is_exclusive(x_277)) {
 lean_ctor_release(x_277, 0);
 lean_ctor_release(x_277, 1);
 x_295 = x_277;
} else {
 lean_dec_ref(x_277);
 x_295 = lean_box(0);
}
if (lean_is_scalar(x_295)) {
 x_296 = lean_alloc_ctor(1, 2, 0);
} else {
 x_296 = x_295;
}
lean_ctor_set(x_296, 0, x_293);
lean_ctor_set(x_296, 1, x_294);
return x_296;
}
}
}
else
{
lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; uint8_t x_304; 
lean_dec(x_1);
x_297 = lean_ctor_get(x_212, 0);
lean_inc(x_297);
lean_dec(x_212);
x_298 = lean_ctor_get(x_211, 1);
lean_inc(x_298);
lean_dec(x_211);
x_299 = lean_ctor_get(x_2, 1);
lean_inc(x_299);
x_300 = lean_ctor_get(x_297, 0);
lean_inc(x_300);
x_301 = lean_ctor_get(x_297, 1);
lean_inc(x_301);
x_302 = lean_ctor_get(x_297, 3);
lean_inc(x_302);
lean_inc(x_300);
x_303 = lean_apply_1(x_299, x_300);
x_304 = lean_unbox(x_303);
lean_dec(x_303);
if (x_304 == 0)
{
lean_object* x_305; 
lean_dec(x_302);
lean_dec(x_301);
lean_dec(x_300);
lean_inc(x_3);
lean_inc(x_297);
x_305 = l_Lean_Compiler_LCNF_Closure_collectFunDecl(x_297, x_2, x_3, x_4, x_5, x_6, x_7, x_298);
if (lean_obj_tag(x_305) == 0)
{
lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; 
x_306 = lean_ctor_get(x_305, 1);
lean_inc(x_306);
lean_dec(x_305);
x_307 = lean_st_ref_take(x_3, x_306);
x_308 = lean_ctor_get(x_307, 0);
lean_inc(x_308);
x_309 = lean_ctor_get(x_307, 1);
lean_inc(x_309);
lean_dec(x_307);
x_310 = lean_ctor_get(x_308, 0);
lean_inc(x_310);
x_311 = lean_ctor_get(x_308, 1);
lean_inc(x_311);
x_312 = lean_ctor_get(x_308, 2);
lean_inc(x_312);
if (lean_is_exclusive(x_308)) {
 lean_ctor_release(x_308, 0);
 lean_ctor_release(x_308, 1);
 lean_ctor_release(x_308, 2);
 x_313 = x_308;
} else {
 lean_dec_ref(x_308);
 x_313 = lean_box(0);
}
x_314 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_314, 0, x_297);
x_315 = lean_array_push(x_312, x_314);
if (lean_is_scalar(x_313)) {
 x_316 = lean_alloc_ctor(0, 3, 0);
} else {
 x_316 = x_313;
}
lean_ctor_set(x_316, 0, x_310);
lean_ctor_set(x_316, 1, x_311);
lean_ctor_set(x_316, 2, x_315);
x_317 = lean_st_ref_set(x_3, x_316, x_309);
lean_dec(x_3);
x_318 = lean_ctor_get(x_317, 1);
lean_inc(x_318);
if (lean_is_exclusive(x_317)) {
 lean_ctor_release(x_317, 0);
 lean_ctor_release(x_317, 1);
 x_319 = x_317;
} else {
 lean_dec_ref(x_317);
 x_319 = lean_box(0);
}
x_320 = lean_box(0);
if (lean_is_scalar(x_319)) {
 x_321 = lean_alloc_ctor(0, 2, 0);
} else {
 x_321 = x_319;
}
lean_ctor_set(x_321, 0, x_320);
lean_ctor_set(x_321, 1, x_318);
return x_321;
}
else
{
lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; 
lean_dec(x_297);
lean_dec(x_3);
x_322 = lean_ctor_get(x_305, 0);
lean_inc(x_322);
x_323 = lean_ctor_get(x_305, 1);
lean_inc(x_323);
if (lean_is_exclusive(x_305)) {
 lean_ctor_release(x_305, 0);
 lean_ctor_release(x_305, 1);
 x_324 = x_305;
} else {
 lean_dec_ref(x_305);
 x_324 = lean_box(0);
}
if (lean_is_scalar(x_324)) {
 x_325 = lean_alloc_ctor(1, 2, 0);
} else {
 x_325 = x_324;
}
lean_ctor_set(x_325, 0, x_322);
lean_ctor_set(x_325, 1, x_323);
return x_325;
}
}
else
{
lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; uint8_t x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; 
lean_dec(x_297);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_326 = lean_st_ref_take(x_3, x_298);
x_327 = lean_ctor_get(x_326, 0);
lean_inc(x_327);
x_328 = lean_ctor_get(x_326, 1);
lean_inc(x_328);
lean_dec(x_326);
x_329 = lean_ctor_get(x_327, 0);
lean_inc(x_329);
x_330 = lean_ctor_get(x_327, 1);
lean_inc(x_330);
x_331 = lean_ctor_get(x_327, 2);
lean_inc(x_331);
if (lean_is_exclusive(x_327)) {
 lean_ctor_release(x_327, 0);
 lean_ctor_release(x_327, 1);
 lean_ctor_release(x_327, 2);
 x_332 = x_327;
} else {
 lean_dec_ref(x_327);
 x_332 = lean_box(0);
}
x_333 = 0;
x_334 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_334, 0, x_300);
lean_ctor_set(x_334, 1, x_301);
lean_ctor_set(x_334, 2, x_302);
lean_ctor_set_uint8(x_334, sizeof(void*)*3, x_333);
x_335 = lean_array_push(x_330, x_334);
if (lean_is_scalar(x_332)) {
 x_336 = lean_alloc_ctor(0, 3, 0);
} else {
 x_336 = x_332;
}
lean_ctor_set(x_336, 0, x_329);
lean_ctor_set(x_336, 1, x_335);
lean_ctor_set(x_336, 2, x_331);
x_337 = lean_st_ref_set(x_3, x_336, x_328);
lean_dec(x_3);
x_338 = lean_ctor_get(x_337, 1);
lean_inc(x_338);
if (lean_is_exclusive(x_337)) {
 lean_ctor_release(x_337, 0);
 lean_ctor_release(x_337, 1);
 x_339 = x_337;
} else {
 lean_dec_ref(x_337);
 x_339 = lean_box(0);
}
x_340 = lean_box(0);
if (lean_is_scalar(x_339)) {
 x_341 = lean_alloc_ctor(0, 2, 0);
} else {
 x_341 = x_339;
}
lean_ctor_set(x_341, 0, x_340);
lean_ctor_set(x_341, 1, x_338);
return x_341;
}
}
}
}
}
else
{
lean_object* x_342; 
lean_dec(x_14);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_342 = lean_box(0);
lean_ctor_set(x_9, 0, x_342);
return x_9;
}
}
else
{
lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; 
x_343 = lean_ctor_get(x_9, 0);
x_344 = lean_ctor_get(x_9, 1);
lean_inc(x_344);
lean_inc(x_343);
lean_dec(x_9);
x_345 = lean_ctor_get(x_343, 0);
lean_inc(x_345);
lean_dec(x_343);
x_346 = l_Lean_RBNode_findCore___at_Lean_Compiler_LCNF_Closure_collectFVar___spec__1(x_345, x_1);
lean_dec(x_345);
if (lean_obj_tag(x_346) == 0)
{
lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; uint8_t x_352; 
lean_inc(x_1);
x_347 = l_Lean_Compiler_LCNF_Closure_markVisited(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_344);
x_348 = lean_ctor_get(x_347, 1);
lean_inc(x_348);
if (lean_is_exclusive(x_347)) {
 lean_ctor_release(x_347, 0);
 lean_ctor_release(x_347, 1);
 x_349 = x_347;
} else {
 lean_dec_ref(x_347);
 x_349 = lean_box(0);
}
x_350 = lean_ctor_get(x_2, 0);
lean_inc(x_350);
lean_inc(x_1);
x_351 = lean_apply_1(x_350, x_1);
x_352 = lean_unbox(x_351);
lean_dec(x_351);
if (x_352 == 0)
{
lean_object* x_353; lean_object* x_354; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_353 = lean_box(0);
if (lean_is_scalar(x_349)) {
 x_354 = lean_alloc_ctor(0, 2, 0);
} else {
 x_354 = x_349;
}
lean_ctor_set(x_354, 0, x_353);
lean_ctor_set(x_354, 1, x_348);
return x_354;
}
else
{
lean_object* x_355; lean_object* x_356; 
lean_dec(x_349);
lean_inc(x_1);
x_355 = l_Lean_Compiler_LCNF_findFunDecl_x3f(x_1, x_4, x_5, x_6, x_7, x_348);
x_356 = lean_ctor_get(x_355, 0);
lean_inc(x_356);
if (lean_obj_tag(x_356) == 0)
{
lean_object* x_357; lean_object* x_358; lean_object* x_359; 
x_357 = lean_ctor_get(x_355, 1);
lean_inc(x_357);
lean_dec(x_355);
lean_inc(x_1);
x_358 = l_Lean_Compiler_LCNF_findParam_x3f(x_1, x_4, x_5, x_6, x_7, x_357);
x_359 = lean_ctor_get(x_358, 0);
lean_inc(x_359);
if (lean_obj_tag(x_359) == 0)
{
lean_object* x_360; lean_object* x_361; lean_object* x_362; 
x_360 = lean_ctor_get(x_358, 1);
lean_inc(x_360);
lean_dec(x_358);
x_361 = l_Lean_Compiler_LCNF_findLetDecl_x3f(x_1, x_4, x_5, x_6, x_7, x_360);
x_362 = lean_ctor_get(x_361, 0);
lean_inc(x_362);
if (lean_obj_tag(x_362) == 0)
{
lean_object* x_363; lean_object* x_364; lean_object* x_365; 
x_363 = lean_ctor_get(x_361, 1);
lean_inc(x_363);
lean_dec(x_361);
x_364 = l_Lean_Compiler_LCNF_Closure_collectFVar___closed__4;
x_365 = l_panic___at_Lean_Compiler_LCNF_Closure_collectFVar___spec__2(x_364, x_2, x_3, x_4, x_5, x_6, x_7, x_363);
return x_365;
}
else
{
lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; 
x_366 = lean_ctor_get(x_362, 0);
lean_inc(x_366);
lean_dec(x_362);
x_367 = lean_ctor_get(x_361, 1);
lean_inc(x_367);
lean_dec(x_361);
x_368 = lean_ctor_get(x_366, 0);
lean_inc(x_368);
x_369 = lean_ctor_get(x_366, 1);
lean_inc(x_369);
x_370 = lean_ctor_get(x_366, 2);
lean_inc(x_370);
x_371 = lean_ctor_get(x_366, 3);
lean_inc(x_371);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_370);
x_372 = l_Lean_Compiler_LCNF_Closure_collectExpr(x_370, x_2, x_3, x_4, x_5, x_6, x_7, x_367);
if (lean_obj_tag(x_372) == 0)
{
lean_object* x_373; lean_object* x_374; lean_object* x_375; uint8_t x_376; 
x_373 = lean_ctor_get(x_372, 1);
lean_inc(x_373);
lean_dec(x_372);
x_374 = lean_ctor_get(x_2, 1);
lean_inc(x_374);
lean_inc(x_368);
x_375 = lean_apply_1(x_374, x_368);
x_376 = lean_unbox(x_375);
lean_dec(x_375);
if (x_376 == 0)
{
lean_object* x_377; 
lean_dec(x_370);
lean_dec(x_369);
lean_dec(x_368);
lean_inc(x_3);
x_377 = l_Lean_Compiler_LCNF_Closure_collectExpr(x_371, x_2, x_3, x_4, x_5, x_6, x_7, x_373);
if (lean_obj_tag(x_377) == 0)
{
lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; 
x_378 = lean_ctor_get(x_377, 1);
lean_inc(x_378);
lean_dec(x_377);
x_379 = lean_st_ref_take(x_3, x_378);
x_380 = lean_ctor_get(x_379, 0);
lean_inc(x_380);
x_381 = lean_ctor_get(x_379, 1);
lean_inc(x_381);
lean_dec(x_379);
x_382 = lean_ctor_get(x_380, 0);
lean_inc(x_382);
x_383 = lean_ctor_get(x_380, 1);
lean_inc(x_383);
x_384 = lean_ctor_get(x_380, 2);
lean_inc(x_384);
if (lean_is_exclusive(x_380)) {
 lean_ctor_release(x_380, 0);
 lean_ctor_release(x_380, 1);
 lean_ctor_release(x_380, 2);
 x_385 = x_380;
} else {
 lean_dec_ref(x_380);
 x_385 = lean_box(0);
}
x_386 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_386, 0, x_366);
x_387 = lean_array_push(x_384, x_386);
if (lean_is_scalar(x_385)) {
 x_388 = lean_alloc_ctor(0, 3, 0);
} else {
 x_388 = x_385;
}
lean_ctor_set(x_388, 0, x_382);
lean_ctor_set(x_388, 1, x_383);
lean_ctor_set(x_388, 2, x_387);
x_389 = lean_st_ref_set(x_3, x_388, x_381);
lean_dec(x_3);
x_390 = lean_ctor_get(x_389, 1);
lean_inc(x_390);
if (lean_is_exclusive(x_389)) {
 lean_ctor_release(x_389, 0);
 lean_ctor_release(x_389, 1);
 x_391 = x_389;
} else {
 lean_dec_ref(x_389);
 x_391 = lean_box(0);
}
x_392 = lean_box(0);
if (lean_is_scalar(x_391)) {
 x_393 = lean_alloc_ctor(0, 2, 0);
} else {
 x_393 = x_391;
}
lean_ctor_set(x_393, 0, x_392);
lean_ctor_set(x_393, 1, x_390);
return x_393;
}
else
{
lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; 
lean_dec(x_366);
lean_dec(x_3);
x_394 = lean_ctor_get(x_377, 0);
lean_inc(x_394);
x_395 = lean_ctor_get(x_377, 1);
lean_inc(x_395);
if (lean_is_exclusive(x_377)) {
 lean_ctor_release(x_377, 0);
 lean_ctor_release(x_377, 1);
 x_396 = x_377;
} else {
 lean_dec_ref(x_377);
 x_396 = lean_box(0);
}
if (lean_is_scalar(x_396)) {
 x_397 = lean_alloc_ctor(1, 2, 0);
} else {
 x_397 = x_396;
}
lean_ctor_set(x_397, 0, x_394);
lean_ctor_set(x_397, 1, x_395);
return x_397;
}
}
else
{
lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; uint8_t x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; 
lean_dec(x_371);
lean_dec(x_366);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_398 = lean_st_ref_take(x_3, x_373);
x_399 = lean_ctor_get(x_398, 0);
lean_inc(x_399);
x_400 = lean_ctor_get(x_398, 1);
lean_inc(x_400);
lean_dec(x_398);
x_401 = lean_ctor_get(x_399, 0);
lean_inc(x_401);
x_402 = lean_ctor_get(x_399, 1);
lean_inc(x_402);
x_403 = lean_ctor_get(x_399, 2);
lean_inc(x_403);
if (lean_is_exclusive(x_399)) {
 lean_ctor_release(x_399, 0);
 lean_ctor_release(x_399, 1);
 lean_ctor_release(x_399, 2);
 x_404 = x_399;
} else {
 lean_dec_ref(x_399);
 x_404 = lean_box(0);
}
x_405 = 0;
x_406 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_406, 0, x_368);
lean_ctor_set(x_406, 1, x_369);
lean_ctor_set(x_406, 2, x_370);
lean_ctor_set_uint8(x_406, sizeof(void*)*3, x_405);
x_407 = lean_array_push(x_402, x_406);
if (lean_is_scalar(x_404)) {
 x_408 = lean_alloc_ctor(0, 3, 0);
} else {
 x_408 = x_404;
}
lean_ctor_set(x_408, 0, x_401);
lean_ctor_set(x_408, 1, x_407);
lean_ctor_set(x_408, 2, x_403);
x_409 = lean_st_ref_set(x_3, x_408, x_400);
lean_dec(x_3);
x_410 = lean_ctor_get(x_409, 1);
lean_inc(x_410);
if (lean_is_exclusive(x_409)) {
 lean_ctor_release(x_409, 0);
 lean_ctor_release(x_409, 1);
 x_411 = x_409;
} else {
 lean_dec_ref(x_409);
 x_411 = lean_box(0);
}
x_412 = lean_box(0);
if (lean_is_scalar(x_411)) {
 x_413 = lean_alloc_ctor(0, 2, 0);
} else {
 x_413 = x_411;
}
lean_ctor_set(x_413, 0, x_412);
lean_ctor_set(x_413, 1, x_410);
return x_413;
}
}
else
{
lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; 
lean_dec(x_371);
lean_dec(x_370);
lean_dec(x_369);
lean_dec(x_368);
lean_dec(x_366);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_414 = lean_ctor_get(x_372, 0);
lean_inc(x_414);
x_415 = lean_ctor_get(x_372, 1);
lean_inc(x_415);
if (lean_is_exclusive(x_372)) {
 lean_ctor_release(x_372, 0);
 lean_ctor_release(x_372, 1);
 x_416 = x_372;
} else {
 lean_dec_ref(x_372);
 x_416 = lean_box(0);
}
if (lean_is_scalar(x_416)) {
 x_417 = lean_alloc_ctor(1, 2, 0);
} else {
 x_417 = x_416;
}
lean_ctor_set(x_417, 0, x_414);
lean_ctor_set(x_417, 1, x_415);
return x_417;
}
}
}
else
{
lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; 
lean_dec(x_1);
x_418 = lean_ctor_get(x_358, 1);
lean_inc(x_418);
lean_dec(x_358);
x_419 = lean_ctor_get(x_359, 0);
lean_inc(x_419);
lean_dec(x_359);
x_420 = lean_ctor_get(x_419, 2);
lean_inc(x_420);
lean_inc(x_3);
x_421 = l_Lean_Compiler_LCNF_Closure_collectExpr(x_420, x_2, x_3, x_4, x_5, x_6, x_7, x_418);
if (lean_obj_tag(x_421) == 0)
{
lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; 
x_422 = lean_ctor_get(x_421, 1);
lean_inc(x_422);
lean_dec(x_421);
x_423 = lean_st_ref_take(x_3, x_422);
x_424 = lean_ctor_get(x_423, 0);
lean_inc(x_424);
x_425 = lean_ctor_get(x_423, 1);
lean_inc(x_425);
lean_dec(x_423);
x_426 = lean_ctor_get(x_424, 0);
lean_inc(x_426);
x_427 = lean_ctor_get(x_424, 1);
lean_inc(x_427);
x_428 = lean_ctor_get(x_424, 2);
lean_inc(x_428);
if (lean_is_exclusive(x_424)) {
 lean_ctor_release(x_424, 0);
 lean_ctor_release(x_424, 1);
 lean_ctor_release(x_424, 2);
 x_429 = x_424;
} else {
 lean_dec_ref(x_424);
 x_429 = lean_box(0);
}
x_430 = lean_array_push(x_427, x_419);
if (lean_is_scalar(x_429)) {
 x_431 = lean_alloc_ctor(0, 3, 0);
} else {
 x_431 = x_429;
}
lean_ctor_set(x_431, 0, x_426);
lean_ctor_set(x_431, 1, x_430);
lean_ctor_set(x_431, 2, x_428);
x_432 = lean_st_ref_set(x_3, x_431, x_425);
lean_dec(x_3);
x_433 = lean_ctor_get(x_432, 1);
lean_inc(x_433);
if (lean_is_exclusive(x_432)) {
 lean_ctor_release(x_432, 0);
 lean_ctor_release(x_432, 1);
 x_434 = x_432;
} else {
 lean_dec_ref(x_432);
 x_434 = lean_box(0);
}
x_435 = lean_box(0);
if (lean_is_scalar(x_434)) {
 x_436 = lean_alloc_ctor(0, 2, 0);
} else {
 x_436 = x_434;
}
lean_ctor_set(x_436, 0, x_435);
lean_ctor_set(x_436, 1, x_433);
return x_436;
}
else
{
lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; 
lean_dec(x_419);
lean_dec(x_3);
x_437 = lean_ctor_get(x_421, 0);
lean_inc(x_437);
x_438 = lean_ctor_get(x_421, 1);
lean_inc(x_438);
if (lean_is_exclusive(x_421)) {
 lean_ctor_release(x_421, 0);
 lean_ctor_release(x_421, 1);
 x_439 = x_421;
} else {
 lean_dec_ref(x_421);
 x_439 = lean_box(0);
}
if (lean_is_scalar(x_439)) {
 x_440 = lean_alloc_ctor(1, 2, 0);
} else {
 x_440 = x_439;
}
lean_ctor_set(x_440, 0, x_437);
lean_ctor_set(x_440, 1, x_438);
return x_440;
}
}
}
else
{
lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; uint8_t x_448; 
lean_dec(x_1);
x_441 = lean_ctor_get(x_356, 0);
lean_inc(x_441);
lean_dec(x_356);
x_442 = lean_ctor_get(x_355, 1);
lean_inc(x_442);
lean_dec(x_355);
x_443 = lean_ctor_get(x_2, 1);
lean_inc(x_443);
x_444 = lean_ctor_get(x_441, 0);
lean_inc(x_444);
x_445 = lean_ctor_get(x_441, 1);
lean_inc(x_445);
x_446 = lean_ctor_get(x_441, 3);
lean_inc(x_446);
lean_inc(x_444);
x_447 = lean_apply_1(x_443, x_444);
x_448 = lean_unbox(x_447);
lean_dec(x_447);
if (x_448 == 0)
{
lean_object* x_449; 
lean_dec(x_446);
lean_dec(x_445);
lean_dec(x_444);
lean_inc(x_3);
lean_inc(x_441);
x_449 = l_Lean_Compiler_LCNF_Closure_collectFunDecl(x_441, x_2, x_3, x_4, x_5, x_6, x_7, x_442);
if (lean_obj_tag(x_449) == 0)
{
lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; 
x_450 = lean_ctor_get(x_449, 1);
lean_inc(x_450);
lean_dec(x_449);
x_451 = lean_st_ref_take(x_3, x_450);
x_452 = lean_ctor_get(x_451, 0);
lean_inc(x_452);
x_453 = lean_ctor_get(x_451, 1);
lean_inc(x_453);
lean_dec(x_451);
x_454 = lean_ctor_get(x_452, 0);
lean_inc(x_454);
x_455 = lean_ctor_get(x_452, 1);
lean_inc(x_455);
x_456 = lean_ctor_get(x_452, 2);
lean_inc(x_456);
if (lean_is_exclusive(x_452)) {
 lean_ctor_release(x_452, 0);
 lean_ctor_release(x_452, 1);
 lean_ctor_release(x_452, 2);
 x_457 = x_452;
} else {
 lean_dec_ref(x_452);
 x_457 = lean_box(0);
}
x_458 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_458, 0, x_441);
x_459 = lean_array_push(x_456, x_458);
if (lean_is_scalar(x_457)) {
 x_460 = lean_alloc_ctor(0, 3, 0);
} else {
 x_460 = x_457;
}
lean_ctor_set(x_460, 0, x_454);
lean_ctor_set(x_460, 1, x_455);
lean_ctor_set(x_460, 2, x_459);
x_461 = lean_st_ref_set(x_3, x_460, x_453);
lean_dec(x_3);
x_462 = lean_ctor_get(x_461, 1);
lean_inc(x_462);
if (lean_is_exclusive(x_461)) {
 lean_ctor_release(x_461, 0);
 lean_ctor_release(x_461, 1);
 x_463 = x_461;
} else {
 lean_dec_ref(x_461);
 x_463 = lean_box(0);
}
x_464 = lean_box(0);
if (lean_is_scalar(x_463)) {
 x_465 = lean_alloc_ctor(0, 2, 0);
} else {
 x_465 = x_463;
}
lean_ctor_set(x_465, 0, x_464);
lean_ctor_set(x_465, 1, x_462);
return x_465;
}
else
{
lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; 
lean_dec(x_441);
lean_dec(x_3);
x_466 = lean_ctor_get(x_449, 0);
lean_inc(x_466);
x_467 = lean_ctor_get(x_449, 1);
lean_inc(x_467);
if (lean_is_exclusive(x_449)) {
 lean_ctor_release(x_449, 0);
 lean_ctor_release(x_449, 1);
 x_468 = x_449;
} else {
 lean_dec_ref(x_449);
 x_468 = lean_box(0);
}
if (lean_is_scalar(x_468)) {
 x_469 = lean_alloc_ctor(1, 2, 0);
} else {
 x_469 = x_468;
}
lean_ctor_set(x_469, 0, x_466);
lean_ctor_set(x_469, 1, x_467);
return x_469;
}
}
else
{
lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; uint8_t x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; 
lean_dec(x_441);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_470 = lean_st_ref_take(x_3, x_442);
x_471 = lean_ctor_get(x_470, 0);
lean_inc(x_471);
x_472 = lean_ctor_get(x_470, 1);
lean_inc(x_472);
lean_dec(x_470);
x_473 = lean_ctor_get(x_471, 0);
lean_inc(x_473);
x_474 = lean_ctor_get(x_471, 1);
lean_inc(x_474);
x_475 = lean_ctor_get(x_471, 2);
lean_inc(x_475);
if (lean_is_exclusive(x_471)) {
 lean_ctor_release(x_471, 0);
 lean_ctor_release(x_471, 1);
 lean_ctor_release(x_471, 2);
 x_476 = x_471;
} else {
 lean_dec_ref(x_471);
 x_476 = lean_box(0);
}
x_477 = 0;
x_478 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_478, 0, x_444);
lean_ctor_set(x_478, 1, x_445);
lean_ctor_set(x_478, 2, x_446);
lean_ctor_set_uint8(x_478, sizeof(void*)*3, x_477);
x_479 = lean_array_push(x_474, x_478);
if (lean_is_scalar(x_476)) {
 x_480 = lean_alloc_ctor(0, 3, 0);
} else {
 x_480 = x_476;
}
lean_ctor_set(x_480, 0, x_473);
lean_ctor_set(x_480, 1, x_479);
lean_ctor_set(x_480, 2, x_475);
x_481 = lean_st_ref_set(x_3, x_480, x_472);
lean_dec(x_3);
x_482 = lean_ctor_get(x_481, 1);
lean_inc(x_482);
if (lean_is_exclusive(x_481)) {
 lean_ctor_release(x_481, 0);
 lean_ctor_release(x_481, 1);
 x_483 = x_481;
} else {
 lean_dec_ref(x_481);
 x_483 = lean_box(0);
}
x_484 = lean_box(0);
if (lean_is_scalar(x_483)) {
 x_485 = lean_alloc_ctor(0, 2, 0);
} else {
 x_485 = x_483;
}
lean_ctor_set(x_485, 0, x_484);
lean_ctor_set(x_485, 1, x_482);
return x_485;
}
}
}
}
else
{
lean_object* x_486; lean_object* x_487; 
lean_dec(x_346);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_486 = lean_box(0);
x_487 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_487, 0, x_486);
lean_ctor_set(x_487, 1, x_344);
return x_487;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Closure_collectFunDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_1, 3);
lean_inc(x_9);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_10 = l_Lean_Compiler_LCNF_Closure_collectExpr(x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_ctor_get(x_1, 2);
lean_inc(x_12);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_13 = l_Lean_Compiler_LCNF_Closure_collectParams(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_11);
lean_dec(x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_ctor_get(x_1, 4);
lean_inc(x_15);
lean_dec(x_1);
x_16 = l_Lean_Compiler_LCNF_Closure_collectCode(x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_14);
return x_16;
}
else
{
uint8_t x_17; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_17 = !lean_is_exclusive(x_13);
if (x_17 == 0)
{
return x_13;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_13, 0);
x_19 = lean_ctor_get(x_13, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_13);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
else
{
uint8_t x_21; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_21 = !lean_is_exclusive(x_10);
if (x_21 == 0)
{
return x_10;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_10, 0);
x_23 = lean_ctor_get(x_10, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_10);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
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
lean_object* x_13; lean_object* x_14; 
lean_dec(x_4);
x_13 = lean_array_uget(x_1, x_2);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_14 = l_Lean_Compiler_LCNF_Closure_collectExpr(x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Closure_collectCode___spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
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
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_ctor_get(x_9, 2);
lean_inc(x_11);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_12 = l_Lean_Compiler_LCNF_Closure_collectExpr(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_ctor_get(x_9, 3);
lean_inc(x_14);
lean_dec(x_9);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_15 = l_Lean_Compiler_LCNF_Closure_collectExpr(x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_13);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_1 = x_10;
x_8 = x_16;
goto _start;
}
else
{
uint8_t x_18; 
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_18 = !lean_is_exclusive(x_15);
if (x_18 == 0)
{
return x_15;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_15, 0);
x_20 = lean_ctor_get(x_15, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_15);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
else
{
uint8_t x_22; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_22 = !lean_is_exclusive(x_12);
if (x_22 == 0)
{
return x_12;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_12, 0);
x_24 = lean_ctor_get(x_12, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_12);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
case 3:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_26 = lean_ctor_get(x_1, 1);
lean_inc(x_26);
lean_dec(x_1);
x_27 = lean_array_get_size(x_26);
x_28 = lean_unsigned_to_nat(0u);
x_29 = lean_nat_dec_lt(x_28, x_27);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_8);
return x_31;
}
else
{
uint8_t x_32; 
x_32 = lean_nat_dec_le(x_27, x_27);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_33 = lean_box(0);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_8);
return x_34;
}
else
{
size_t x_35; size_t x_36; lean_object* x_37; lean_object* x_38; 
x_35 = 0;
x_36 = lean_usize_of_nat(x_27);
lean_dec(x_27);
x_37 = lean_box(0);
x_38 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Closure_collectCode___spec__1(x_26, x_35, x_36, x_37, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_26);
return x_38;
}
}
}
case 4:
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_1, 0);
lean_inc(x_39);
lean_dec(x_1);
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_41 = l_Lean_Compiler_LCNF_Closure_collectExpr(x_40, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_41, 1);
lean_inc(x_42);
lean_dec(x_41);
x_43 = lean_ctor_get(x_39, 2);
lean_inc(x_43);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_44 = l_Lean_Compiler_LCNF_Closure_collectFVar(x_43, x_2, x_3, x_4, x_5, x_6, x_7, x_42);
if (lean_obj_tag(x_44) == 0)
{
uint8_t x_45; 
x_45 = !lean_is_exclusive(x_44);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_46 = lean_ctor_get(x_44, 1);
x_47 = lean_ctor_get(x_44, 0);
lean_dec(x_47);
x_48 = lean_ctor_get(x_39, 3);
lean_inc(x_48);
lean_dec(x_39);
x_49 = lean_array_get_size(x_48);
x_50 = lean_unsigned_to_nat(0u);
x_51 = lean_nat_dec_lt(x_50, x_49);
if (x_51 == 0)
{
lean_object* x_52; 
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_52 = lean_box(0);
lean_ctor_set(x_44, 0, x_52);
return x_44;
}
else
{
uint8_t x_53; 
x_53 = lean_nat_dec_le(x_49, x_49);
if (x_53 == 0)
{
lean_object* x_54; 
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_54 = lean_box(0);
lean_ctor_set(x_44, 0, x_54);
return x_44;
}
else
{
size_t x_55; size_t x_56; lean_object* x_57; lean_object* x_58; 
lean_free_object(x_44);
x_55 = 0;
x_56 = lean_usize_of_nat(x_49);
lean_dec(x_49);
x_57 = lean_box(0);
x_58 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Closure_collectCode___spec__2(x_48, x_55, x_56, x_57, x_2, x_3, x_4, x_5, x_6, x_7, x_46);
lean_dec(x_48);
return x_58;
}
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_59 = lean_ctor_get(x_44, 1);
lean_inc(x_59);
lean_dec(x_44);
x_60 = lean_ctor_get(x_39, 3);
lean_inc(x_60);
lean_dec(x_39);
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
lean_ctor_set(x_65, 1, x_59);
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
lean_ctor_set(x_68, 1, x_59);
return x_68;
}
else
{
size_t x_69; size_t x_70; lean_object* x_71; lean_object* x_72; 
x_69 = 0;
x_70 = lean_usize_of_nat(x_61);
lean_dec(x_61);
x_71 = lean_box(0);
x_72 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Closure_collectCode___spec__2(x_60, x_69, x_70, x_71, x_2, x_3, x_4, x_5, x_6, x_7, x_59);
lean_dec(x_60);
return x_72;
}
}
}
}
else
{
uint8_t x_73; 
lean_dec(x_39);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_73 = !lean_is_exclusive(x_44);
if (x_73 == 0)
{
return x_44;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_44, 0);
x_75 = lean_ctor_get(x_44, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_44);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
return x_76;
}
}
}
else
{
uint8_t x_77; 
lean_dec(x_39);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_77 = !lean_is_exclusive(x_41);
if (x_77 == 0)
{
return x_41;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_41, 0);
x_79 = lean_ctor_get(x_41, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_41);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
}
}
case 5:
{
lean_object* x_81; lean_object* x_82; 
x_81 = lean_ctor_get(x_1, 0);
lean_inc(x_81);
lean_dec(x_1);
x_82 = l_Lean_Compiler_LCNF_Closure_collectFVar(x_81, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_82;
}
case 6:
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_ctor_get(x_1, 0);
lean_inc(x_83);
lean_dec(x_1);
x_84 = l_Lean_Compiler_LCNF_Closure_collectExpr(x_83, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_84;
}
default: 
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_1, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_1, 1);
lean_inc(x_86);
lean_dec(x_1);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_87 = l_Lean_Compiler_LCNF_Closure_collectFunDecl(x_85, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; 
x_88 = lean_ctor_get(x_87, 1);
lean_inc(x_88);
lean_dec(x_87);
x_1 = x_86;
x_8 = x_88;
goto _start;
}
else
{
uint8_t x_90; 
lean_dec(x_86);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_90 = !lean_is_exclusive(x_87);
if (x_90 == 0)
{
return x_87;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_87, 0);
x_92 = lean_ctor_get(x_87, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_87);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
return x_93;
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
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___at_Lean_Compiler_LCNF_Closure_collectExpr___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_ForEachExpr_visit___at_Lean_Compiler_LCNF_Closure_collectExpr___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_findCore___at_Lean_Compiler_LCNF_Closure_collectFVar___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_RBNode_findCore___at_Lean_Compiler_LCNF_Closure_collectFVar___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
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
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Closure_collectCode___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Closure_collectCode___spec__2(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_1);
return x_14;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Closure_run___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_LCNF_Closure_State_params___default___closed__1;
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
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_2);
lean_ctor_set(x_9, 1, x_3);
x_10 = l_Lean_Compiler_LCNF_Closure_run___rarg___closed__1;
x_11 = lean_st_mk_ref(x_10, x_8);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
lean_inc(x_12);
x_14 = lean_apply_7(x_1, x_9, x_12, x_4, x_5, x_6, x_7, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_st_ref_get(x_12, x_16);
lean_dec(x_12);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 2);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_15);
lean_ctor_set(x_23, 1, x_22);
lean_ctor_set(x_17, 0, x_23);
return x_17;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_24 = lean_ctor_get(x_17, 0);
x_25 = lean_ctor_get(x_17, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_17);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
x_27 = lean_ctor_get(x_24, 2);
lean_inc(x_27);
lean_dec(x_24);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_15);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_25);
return x_30;
}
}
else
{
uint8_t x_31; 
lean_dec(x_12);
x_31 = !lean_is_exclusive(x_14);
if (x_31 == 0)
{
return x_14;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_14, 0);
x_33 = lean_ctor_get(x_14, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_14);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
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
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Util_ForEachExpr(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_CompilerM(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_LCNF_Closure(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_ForEachExpr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_CompilerM(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Compiler_LCNF_Closure_State_visited___default = _init_l_Lean_Compiler_LCNF_Closure_State_visited___default();
lean_mark_persistent(l_Lean_Compiler_LCNF_Closure_State_visited___default);
l_Lean_Compiler_LCNF_Closure_State_params___default___closed__1 = _init_l_Lean_Compiler_LCNF_Closure_State_params___default___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_Closure_State_params___default___closed__1);
l_Lean_Compiler_LCNF_Closure_State_params___default = _init_l_Lean_Compiler_LCNF_Closure_State_params___default();
lean_mark_persistent(l_Lean_Compiler_LCNF_Closure_State_params___default);
l_Lean_Compiler_LCNF_Closure_State_decls___default = _init_l_Lean_Compiler_LCNF_Closure_State_decls___default();
lean_mark_persistent(l_Lean_Compiler_LCNF_Closure_State_decls___default);
l_Lean_Compiler_LCNF_Closure_collectExpr___closed__1 = _init_l_Lean_Compiler_LCNF_Closure_collectExpr___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_Closure_collectExpr___closed__1);
l_Lean_Compiler_LCNF_Closure_collectExpr___closed__2 = _init_l_Lean_Compiler_LCNF_Closure_collectExpr___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_Closure_collectExpr___closed__2);
l_panic___at_Lean_Compiler_LCNF_Closure_collectFVar___spec__2___closed__1 = _init_l_panic___at_Lean_Compiler_LCNF_Closure_collectFVar___spec__2___closed__1();
lean_mark_persistent(l_panic___at_Lean_Compiler_LCNF_Closure_collectFVar___spec__2___closed__1);
l_panic___at_Lean_Compiler_LCNF_Closure_collectFVar___spec__2___closed__2 = _init_l_panic___at_Lean_Compiler_LCNF_Closure_collectFVar___spec__2___closed__2();
lean_mark_persistent(l_panic___at_Lean_Compiler_LCNF_Closure_collectFVar___spec__2___closed__2);
l_panic___at_Lean_Compiler_LCNF_Closure_collectFVar___spec__2___closed__3 = _init_l_panic___at_Lean_Compiler_LCNF_Closure_collectFVar___spec__2___closed__3();
lean_mark_persistent(l_panic___at_Lean_Compiler_LCNF_Closure_collectFVar___spec__2___closed__3);
l_panic___at_Lean_Compiler_LCNF_Closure_collectFVar___spec__2___closed__4 = _init_l_panic___at_Lean_Compiler_LCNF_Closure_collectFVar___spec__2___closed__4();
lean_mark_persistent(l_panic___at_Lean_Compiler_LCNF_Closure_collectFVar___spec__2___closed__4);
l_panic___at_Lean_Compiler_LCNF_Closure_collectFVar___spec__2___closed__5 = _init_l_panic___at_Lean_Compiler_LCNF_Closure_collectFVar___spec__2___closed__5();
lean_mark_persistent(l_panic___at_Lean_Compiler_LCNF_Closure_collectFVar___spec__2___closed__5);
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
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
