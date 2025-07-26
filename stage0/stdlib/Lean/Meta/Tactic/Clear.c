// Lean compiler output
// Module: Lean.Meta.Tactic.Clear
// Imports: Lean.Meta.Tactic.Util
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
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_PersistentArray_forMAux___at___Lean_PersistentArray_forM___at___Lean_LocalContext_forM___at___Lean_MVarId_clear_spec__0_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___at___Lean_LocalContext_forM___at___Lean_MVarId_clear_spec__0_spec__0___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Lean_MVarId_tryClearMany_x27_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lean_PersistentArray_forMAux___at___Lean_PersistentArray_forM___at___Lean_LocalContext_forM___at___Lean_MVarId_clear_spec__0_spec__0_spec__0___lam__0___closed__4;
static lean_object* l_Lean_MVarId_clear___lam__1___closed__2;
lean_object* l_Lean_Meta_mkFreshExprMVarAt(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___Lean_MVarId_clear_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_checkNotAssigned(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_clear___lam__1___closed__1;
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_mk_array(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___at___Lean_LocalContext_forM___at___Lean_MVarId_clear_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_exprDependsOn___at___Lean_MVarId_clear_spec__5___redArg___closed__2;
lean_object* l_Lean_MVarId_getTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_clear___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_PersistentArray_forMAux___at___Lean_PersistentArray_forM___at___Lean_LocalContext_forM___at___Lean_MVarId_clear_spec__0_spec__0_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_MVarId_clear___lam__0(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Lean_MVarId_tryClearMany_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_tryClearMany_x27___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Lean_MVarId_tryClearMany_x27_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___at___Lean_PersistentArray_forM___at___Lean_LocalContext_forM___at___Lean_MVarId_clear_spec__0_spec__0_spec__0___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_withContext___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_findFinIdx_x3f_loop___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___Lean_MVarId_clear_spec__5___redArg___lam__1___boxed(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_exprDependsOn___at___Lean_MVarId_clear_spec__5___redArg___lam__1(lean_object*, lean_object*);
static lean_object* l_Lean_PersistentArray_forMAux___at___Lean_PersistentArray_forM___at___Lean_LocalContext_forM___at___Lean_MVarId_clear_spec__0_spec__0_spec__0___lam__0___closed__5;
static lean_object* l_Lean_exprDependsOn___at___Lean_MVarId_clear_spec__5___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_MVarId_tryClearMany_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PersistentArray_forMAux___at___Lean_PersistentArray_forM___at___Lean_LocalContext_forM___at___Lean_MVarId_clear_spec__0_spec__0_spec__0___lam__0___closed__0;
static lean_object* l_Lean_PersistentArray_forMAux___at___Lean_PersistentArray_forM___at___Lean_LocalContext_forM___at___Lean_MVarId_clear_spec__0_spec__0_spec__0___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___at___Lean_PersistentArray_forM___at___Lean_LocalContext_forM___at___Lean_MVarId_clear_spec__0_spec__0_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_PersistentArray_forMAux___at___Lean_PersistentArray_forM___at___Lean_LocalContext_forM___at___Lean_MVarId_clear_spec__0_spec__0_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_clear(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_clear___closed__1;
static lean_object* l_Lean_MVarId_clear___lam__1___closed__3;
uint8_t l_Lean_LocalContext_contains(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_tryClearMany___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___at___Lean_LocalContext_forM___at___Lean_MVarId_clear_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_clear___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___at___Lean_LocalContext_forM___at___Lean_MVarId_clear_spec__0_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_eraseIdx___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_clear___lam__1___closed__0;
static lean_object* l_Lean_PersistentArray_forMAux___at___Lean_PersistentArray_forM___at___Lean_LocalContext_forM___at___Lean_MVarId_clear_spec__0_spec__0_spec__0___lam__0___closed__2;
static lean_object* l_Lean_MVarId_clear___closed__0;
lean_object* l_Lean_MVarId_getDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___Lean_MVarId_clear_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_local_ctx_erase(lean_object*, lean_object*);
lean_object* l_Lean_Meta_SavedState_restore___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___Lean_MVarId_clear_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_saveState___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PersistentArray_forMAux___at___Lean_PersistentArray_forM___at___Lean_LocalContext_forM___at___Lean_MVarId_clear_spec__0_spec__0_spec__0___lam__0___closed__3;
static lean_object* l_Lean_exprDependsOn___at___Lean_MVarId_clear_spec__5___redArg___closed__4;
LEAN_EXPORT lean_object* l_Lean_MVarId_tryClear(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___at___Lean_PersistentArray_forM___at___Lean_LocalContext_forM___at___Lean_MVarId_clear_spec__0_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_MVarId_tryClearMany(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
LEAN_EXPORT uint8_t l_Lean_exprDependsOn___at___Lean_MVarId_clear_spec__5___redArg___lam__0(lean_object*);
static lean_object* l_Lean_exprDependsOn___at___Lean_MVarId_clear_spec__5___redArg___closed__0;
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___at___Lean_PersistentArray_forM___at___Lean_LocalContext_forM___at___Lean_MVarId_clear_spec__0_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_forM___at___Lean_MVarId_clear_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLocalInstances___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Lean_MVarId_tryClearMany_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_throwTacticEx___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_exprDependsOn___at___Lean_MVarId_clear_spec__5___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___Lean_MVarId_clear_spec__5___redArg___lam__0___boxed(lean_object*);
lean_object* l_Lean_MVarId_assign___at___Lean_Meta_getLevel_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_sortFVarsByContextOrder(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_LocalDecl_toExpr(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_forM___at___Lean_MVarId_clear_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_PersistentArray_forMAux___at___Lean_PersistentArray_forM___at___Lean_LocalContext_forM___at___Lean_MVarId_clear_spec__0_spec__0_spec__0_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___Lean_MVarId_clear_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_localDeclDependsOn___at___Lean_FVarId_hasForwardDeps_spec__0___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_PersistentArray_forMAux___at___Lean_PersistentArray_forM___at___Lean_LocalContext_forM___at___Lean_MVarId_clear_spec__0_spec__0_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_usize_dec_eq(x_5, x_6);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_array_uget(x_4, x_5);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_15 = l_Lean_PersistentArray_forMAux___at___Lean_PersistentArray_forM___at___Lean_LocalContext_forM___at___Lean_MVarId_clear_spec__0_spec__0_spec__0(x_1, x_2, x_3, x_14, x_8, x_9, x_10, x_11, x_12);
lean_dec_ref(x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec_ref(x_15);
x_18 = 1;
x_19 = lean_usize_add(x_5, x_18);
x_5 = x_19;
x_7 = x_16;
x_12 = x_17;
goto _start;
}
else
{
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_15;
}
}
else
{
lean_object* x_21; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_7);
lean_ctor_set(x_21, 1, x_12);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_PersistentArray_forMAux___at___Lean_PersistentArray_forM___at___Lean_LocalContext_forM___at___Lean_MVarId_clear_spec__0_spec__0_spec__0_spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_eq(x_3, x_4);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_array_uget(x_2, x_3);
lean_inc_ref(x_1);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_13 = lean_apply_6(x_1, x_12, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec_ref(x_13);
x_16 = 1;
x_17 = lean_usize_add(x_3, x_16);
x_3 = x_17;
x_5 = x_14;
x_10 = x_15;
goto _start;
}
else
{
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_1);
return x_13;
}
}
else
{
lean_object* x_19; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_1);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_5);
lean_ctor_set(x_19, 1, x_10);
return x_19;
}
}
}
static lean_object* _init_l_Lean_PersistentArray_forMAux___at___Lean_PersistentArray_forM___at___Lean_LocalContext_forM___at___Lean_MVarId_clear_spec__0_spec__0_spec__0___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("variable '", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lean_PersistentArray_forMAux___at___Lean_PersistentArray_forM___at___Lean_LocalContext_forM___at___Lean_MVarId_clear_spec__0_spec__0_spec__0___lam__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PersistentArray_forMAux___at___Lean_PersistentArray_forM___at___Lean_LocalContext_forM___at___Lean_MVarId_clear_spec__0_spec__0_spec__0___lam__0___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PersistentArray_forMAux___at___Lean_PersistentArray_forM___at___Lean_LocalContext_forM___at___Lean_MVarId_clear_spec__0_spec__0_spec__0___lam__0___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("' depends on '", 14, 14);
return x_1;
}
}
static lean_object* _init_l_Lean_PersistentArray_forMAux___at___Lean_PersistentArray_forM___at___Lean_LocalContext_forM___at___Lean_MVarId_clear_spec__0_spec__0_spec__0___lam__0___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PersistentArray_forMAux___at___Lean_PersistentArray_forM___at___Lean_LocalContext_forM___at___Lean_MVarId_clear_spec__0_spec__0_spec__0___lam__0___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PersistentArray_forMAux___at___Lean_PersistentArray_forM___at___Lean_LocalContext_forM___at___Lean_MVarId_clear_spec__0_spec__0_spec__0___lam__0___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("'", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_PersistentArray_forMAux___at___Lean_PersistentArray_forM___at___Lean_LocalContext_forM___at___Lean_MVarId_clear_spec__0_spec__0_spec__0___lam__0___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PersistentArray_forMAux___at___Lean_PersistentArray_forM___at___Lean_LocalContext_forM___at___Lean_MVarId_clear_spec__0_spec__0_spec__0___lam__0___closed__4;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___at___Lean_PersistentArray_forM___at___Lean_LocalContext_forM___at___Lean_MVarId_clear_spec__0_spec__0_spec__0___lam__0(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_43; 
x_13 = lean_ctor_get(x_5, 0);
lean_inc(x_13);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 x_14 = x_5;
} else {
 lean_dec_ref(x_5);
 x_14 = lean_box(0);
}
x_43 = lean_ctor_get(x_13, 1);
lean_inc(x_43);
x_15 = x_43;
goto block_42;
block_42:
{
uint8_t x_16; 
x_16 = lean_name_eq(x_15, x_1);
lean_dec(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
lean_inc(x_1);
lean_inc(x_13);
x_17 = l_Lean_localDeclDependsOn___at___Lean_FVarId_hasForwardDeps_spec__0___redArg(x_13, x_1, x_2, x_7, x_10);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_unbox(x_18);
lean_dec(x_18);
if (x_19 == 0)
{
uint8_t x_20; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_20 = !lean_is_exclusive(x_17);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_17, 0);
lean_dec(x_21);
x_22 = lean_box(0);
lean_ctor_set(x_17, 0, x_22);
return x_17;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_17, 1);
lean_inc(x_23);
lean_dec(x_17);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_26 = lean_ctor_get(x_17, 1);
lean_inc(x_26);
lean_dec_ref(x_17);
x_27 = l_Lean_PersistentArray_forMAux___at___Lean_PersistentArray_forM___at___Lean_LocalContext_forM___at___Lean_MVarId_clear_spec__0_spec__0_spec__0___lam__0___closed__1;
x_28 = l_Lean_LocalDecl_toExpr(x_13);
x_29 = l_Lean_MessageData_ofExpr(x_28);
x_30 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_30, 0, x_27);
lean_ctor_set(x_30, 1, x_29);
x_31 = l_Lean_PersistentArray_forMAux___at___Lean_PersistentArray_forM___at___Lean_LocalContext_forM___at___Lean_MVarId_clear_spec__0_spec__0_spec__0___lam__0___closed__3;
x_32 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
x_33 = l_Lean_Expr_fvar___override(x_1);
x_34 = l_Lean_MessageData_ofExpr(x_33);
x_35 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_35, 0, x_32);
lean_ctor_set(x_35, 1, x_34);
x_36 = l_Lean_PersistentArray_forMAux___at___Lean_PersistentArray_forM___at___Lean_LocalContext_forM___at___Lean_MVarId_clear_spec__0_spec__0_spec__0___lam__0___closed__5;
x_37 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
if (lean_is_scalar(x_14)) {
 x_38 = lean_alloc_ctor(1, 1, 0);
} else {
 x_38 = x_14;
}
lean_ctor_set(x_38, 0, x_37);
x_39 = l_Lean_Meta_throwTacticEx___redArg(x_3, x_4, x_38, x_6, x_7, x_8, x_9, x_26);
return x_39;
}
}
else
{
lean_object* x_40; lean_object* x_41; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_40 = lean_box(0);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_10);
return x_41;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___at___Lean_PersistentArray_forM___at___Lean_LocalContext_forM___at___Lean_MVarId_clear_spec__0_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_10 = lean_ctor_get(x_4, 0);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_array_get_size(x_10);
x_13 = lean_box(0);
x_14 = lean_nat_dec_lt(x_11, x_12);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_9);
return x_15;
}
else
{
uint8_t x_16; 
x_16 = lean_nat_dec_le(x_12, x_12);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_13);
lean_ctor_set(x_17, 1, x_9);
return x_17;
}
else
{
size_t x_18; size_t x_19; lean_object* x_20; 
x_18 = 0;
x_19 = lean_usize_of_nat(x_12);
lean_dec(x_12);
x_20 = l_Array_foldlMUnsafe_fold___at___Lean_PersistentArray_forMAux___at___Lean_PersistentArray_forM___at___Lean_LocalContext_forM___at___Lean_MVarId_clear_spec__0_spec__0_spec__0_spec__0(x_1, x_2, x_3, x_10, x_18, x_19, x_13, x_5, x_6, x_7, x_8, x_9);
return x_20;
}
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_21 = lean_ctor_get(x_4, 0);
x_22 = lean_unsigned_to_nat(0u);
x_23 = lean_array_get_size(x_21);
x_24 = lean_box(0);
x_25 = lean_nat_dec_lt(x_22, x_23);
if (x_25 == 0)
{
lean_object* x_26; 
lean_dec(x_23);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_9);
return x_26;
}
else
{
uint8_t x_27; 
x_27 = lean_nat_dec_le(x_23, x_23);
if (x_27 == 0)
{
lean_object* x_28; 
lean_dec(x_23);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_24);
lean_ctor_set(x_28, 1, x_9);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; size_t x_31; size_t x_32; lean_object* x_33; 
x_29 = lean_box(x_27);
x_30 = lean_alloc_closure((void*)(l_Lean_PersistentArray_forMAux___at___Lean_PersistentArray_forM___at___Lean_LocalContext_forM___at___Lean_MVarId_clear_spec__0_spec__0_spec__0___lam__0___boxed), 10, 4);
lean_closure_set(x_30, 0, x_1);
lean_closure_set(x_30, 1, x_29);
lean_closure_set(x_30, 2, x_2);
lean_closure_set(x_30, 3, x_3);
x_31 = 0;
x_32 = lean_usize_of_nat(x_23);
lean_dec(x_23);
x_33 = l_Array_foldlMUnsafe_fold___at___Lean_PersistentArray_forMAux___at___Lean_PersistentArray_forM___at___Lean_LocalContext_forM___at___Lean_MVarId_clear_spec__0_spec__0_spec__0_spec__1(x_30, x_21, x_31, x_32, x_24, x_5, x_6, x_7, x_8, x_9);
return x_33;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___at___Lean_LocalContext_forM___at___Lean_MVarId_clear_spec__0_spec__0___lam__0(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_43; 
x_13 = lean_ctor_get(x_5, 0);
lean_inc(x_13);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 x_14 = x_5;
} else {
 lean_dec_ref(x_5);
 x_14 = lean_box(0);
}
x_43 = lean_ctor_get(x_13, 1);
lean_inc(x_43);
x_15 = x_43;
goto block_42;
block_42:
{
uint8_t x_16; 
x_16 = lean_name_eq(x_15, x_1);
lean_dec(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
lean_inc(x_1);
lean_inc(x_13);
x_17 = l_Lean_localDeclDependsOn___at___Lean_FVarId_hasForwardDeps_spec__0___redArg(x_13, x_1, x_2, x_7, x_10);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_unbox(x_18);
lean_dec(x_18);
if (x_19 == 0)
{
uint8_t x_20; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_20 = !lean_is_exclusive(x_17);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_17, 0);
lean_dec(x_21);
x_22 = lean_box(0);
lean_ctor_set(x_17, 0, x_22);
return x_17;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_17, 1);
lean_inc(x_23);
lean_dec(x_17);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_26 = lean_ctor_get(x_17, 1);
lean_inc(x_26);
lean_dec_ref(x_17);
x_27 = l_Lean_PersistentArray_forMAux___at___Lean_PersistentArray_forM___at___Lean_LocalContext_forM___at___Lean_MVarId_clear_spec__0_spec__0_spec__0___lam__0___closed__1;
x_28 = l_Lean_LocalDecl_toExpr(x_13);
x_29 = l_Lean_MessageData_ofExpr(x_28);
x_30 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_30, 0, x_27);
lean_ctor_set(x_30, 1, x_29);
x_31 = l_Lean_PersistentArray_forMAux___at___Lean_PersistentArray_forM___at___Lean_LocalContext_forM___at___Lean_MVarId_clear_spec__0_spec__0_spec__0___lam__0___closed__3;
x_32 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
x_33 = l_Lean_Expr_fvar___override(x_1);
x_34 = l_Lean_MessageData_ofExpr(x_33);
x_35 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_35, 0, x_32);
lean_ctor_set(x_35, 1, x_34);
x_36 = l_Lean_PersistentArray_forMAux___at___Lean_PersistentArray_forM___at___Lean_LocalContext_forM___at___Lean_MVarId_clear_spec__0_spec__0_spec__0___lam__0___closed__5;
x_37 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
if (lean_is_scalar(x_14)) {
 x_38 = lean_alloc_ctor(1, 1, 0);
} else {
 x_38 = x_14;
}
lean_ctor_set(x_38, 0, x_37);
x_39 = l_Lean_Meta_throwTacticEx___redArg(x_3, x_4, x_38, x_6, x_7, x_8, x_9, x_26);
return x_39;
}
}
else
{
lean_object* x_40; lean_object* x_41; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_40 = lean_box(0);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_10);
return x_41;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___at___Lean_LocalContext_forM___at___Lean_MVarId_clear_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_4, 0);
x_11 = lean_ctor_get(x_4, 1);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_12 = l_Lean_PersistentArray_forMAux___at___Lean_PersistentArray_forM___at___Lean_LocalContext_forM___at___Lean_MVarId_clear_spec__0_spec__0_spec__0(x_1, x_2, x_3, x_10, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_14 = lean_ctor_get(x_12, 1);
x_15 = lean_ctor_get(x_12, 0);
lean_dec(x_15);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_array_get_size(x_11);
x_18 = lean_box(0);
x_19 = lean_nat_dec_lt(x_16, x_17);
if (x_19 == 0)
{
lean_dec(x_17);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
lean_ctor_set(x_12, 0, x_18);
return x_12;
}
else
{
uint8_t x_20; 
x_20 = lean_nat_dec_le(x_17, x_17);
if (x_20 == 0)
{
lean_dec(x_17);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
lean_ctor_set(x_12, 0, x_18);
return x_12;
}
else
{
lean_object* x_21; lean_object* x_22; size_t x_23; size_t x_24; lean_object* x_25; 
lean_free_object(x_12);
x_21 = lean_box(x_20);
x_22 = lean_alloc_closure((void*)(l_Lean_PersistentArray_forM___at___Lean_LocalContext_forM___at___Lean_MVarId_clear_spec__0_spec__0___lam__0___boxed), 10, 4);
lean_closure_set(x_22, 0, x_1);
lean_closure_set(x_22, 1, x_21);
lean_closure_set(x_22, 2, x_2);
lean_closure_set(x_22, 3, x_3);
x_23 = 0;
x_24 = lean_usize_of_nat(x_17);
lean_dec(x_17);
x_25 = l_Array_foldlMUnsafe_fold___at___Lean_PersistentArray_forMAux___at___Lean_PersistentArray_forM___at___Lean_LocalContext_forM___at___Lean_MVarId_clear_spec__0_spec__0_spec__0_spec__1(x_22, x_11, x_23, x_24, x_18, x_5, x_6, x_7, x_8, x_14);
return x_25;
}
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_26 = lean_ctor_get(x_12, 1);
lean_inc(x_26);
lean_dec(x_12);
x_27 = lean_unsigned_to_nat(0u);
x_28 = lean_array_get_size(x_11);
x_29 = lean_box(0);
x_30 = lean_nat_dec_lt(x_27, x_28);
if (x_30 == 0)
{
lean_object* x_31; 
lean_dec(x_28);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_26);
return x_31;
}
else
{
uint8_t x_32; 
x_32 = lean_nat_dec_le(x_28, x_28);
if (x_32 == 0)
{
lean_object* x_33; 
lean_dec(x_28);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_29);
lean_ctor_set(x_33, 1, x_26);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; size_t x_36; size_t x_37; lean_object* x_38; 
x_34 = lean_box(x_32);
x_35 = lean_alloc_closure((void*)(l_Lean_PersistentArray_forM___at___Lean_LocalContext_forM___at___Lean_MVarId_clear_spec__0_spec__0___lam__0___boxed), 10, 4);
lean_closure_set(x_35, 0, x_1);
lean_closure_set(x_35, 1, x_34);
lean_closure_set(x_35, 2, x_2);
lean_closure_set(x_35, 3, x_3);
x_36 = 0;
x_37 = lean_usize_of_nat(x_28);
lean_dec(x_28);
x_38 = l_Array_foldlMUnsafe_fold___at___Lean_PersistentArray_forMAux___at___Lean_PersistentArray_forM___at___Lean_LocalContext_forM___at___Lean_MVarId_clear_spec__0_spec__0_spec__0_spec__1(x_35, x_11, x_36, x_37, x_29, x_5, x_6, x_7, x_8, x_26);
return x_38;
}
}
}
}
else
{
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_forM___at___Lean_MVarId_clear_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_4, 1);
x_11 = l_Lean_PersistentArray_forM___at___Lean_LocalContext_forM___at___Lean_MVarId_clear_spec__0_spec__0(x_1, x_2, x_3, x_10, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT uint8_t l_Lean_exprDependsOn___at___Lean_MVarId_clear_spec__5___redArg___lam__0(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = 0;
return x_2;
}
}
LEAN_EXPORT uint8_t l_Lean_exprDependsOn___at___Lean_MVarId_clear_spec__5___redArg___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_name_eq(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_exprDependsOn___at___Lean_MVarId_clear_spec__5___redArg___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = lean_unsigned_to_nat(8u);
x_3 = lean_nat_mul(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_exprDependsOn___at___Lean_MVarId_clear_spec__5___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(3u);
x_2 = l_Lean_exprDependsOn___at___Lean_MVarId_clear_spec__5___redArg___closed__0;
x_3 = lean_nat_div(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_exprDependsOn___at___Lean_MVarId_clear_spec__5___redArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_exprDependsOn___at___Lean_MVarId_clear_spec__5___redArg___closed__1;
x_2 = l_Nat_nextPowerOfTwo(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_exprDependsOn___at___Lean_MVarId_clear_spec__5___redArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_exprDependsOn___at___Lean_MVarId_clear_spec__5___redArg___closed__2;
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_exprDependsOn___at___Lean_MVarId_clear_spec__5___redArg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_exprDependsOn___at___Lean_MVarId_clear_spec__5___redArg___closed__3;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___Lean_MVarId_clear_spec__5___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_st_ref_get(x_3, x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_34; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
x_40 = lean_ctor_get(x_7, 0);
lean_inc_ref(x_40);
lean_dec(x_7);
x_41 = lean_alloc_closure((void*)(l_Lean_exprDependsOn___at___Lean_MVarId_clear_spec__5___redArg___lam__0___boxed), 1, 0);
x_42 = lean_alloc_closure((void*)(l_Lean_exprDependsOn___at___Lean_MVarId_clear_spec__5___redArg___lam__1___boxed), 2, 1);
lean_closure_set(x_42, 0, x_2);
x_43 = l_Lean_exprDependsOn___at___Lean_MVarId_clear_spec__5___redArg___closed__4;
lean_inc_ref(x_40);
lean_ctor_set(x_5, 1, x_40);
lean_ctor_set(x_5, 0, x_43);
x_44 = l_Lean_Expr_hasFVar(x_1);
if (x_44 == 0)
{
uint8_t x_45; 
x_45 = l_Lean_Expr_hasMVar(x_1);
if (x_45 == 0)
{
lean_dec_ref(x_5);
lean_dec_ref(x_42);
lean_dec_ref(x_41);
lean_dec_ref(x_1);
x_9 = x_45;
x_10 = x_40;
goto block_33;
}
else
{
lean_object* x_46; 
lean_dec_ref(x_40);
x_46 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_42, x_41, x_1, x_5);
x_34 = x_46;
goto block_39;
}
}
else
{
lean_object* x_47; 
lean_dec_ref(x_40);
x_47 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_42, x_41, x_1, x_5);
x_34 = x_47;
goto block_39;
}
block_33:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_st_ref_take(x_3, x_8);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec_ref(x_11);
x_14 = !lean_is_exclusive(x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_ctor_get(x_12, 0);
lean_dec(x_15);
lean_ctor_set(x_12, 0, x_10);
x_16 = lean_st_ref_set(x_3, x_12, x_13);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_16, 0);
lean_dec(x_18);
x_19 = lean_box(x_9);
lean_ctor_set(x_16, 0, x_19);
return x_16;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_16, 1);
lean_inc(x_20);
lean_dec(x_16);
x_21 = lean_box(x_9);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_23 = lean_ctor_get(x_12, 1);
x_24 = lean_ctor_get(x_12, 2);
x_25 = lean_ctor_get(x_12, 3);
x_26 = lean_ctor_get(x_12, 4);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_12);
x_27 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_27, 0, x_10);
lean_ctor_set(x_27, 1, x_23);
lean_ctor_set(x_27, 2, x_24);
lean_ctor_set(x_27, 3, x_25);
lean_ctor_set(x_27, 4, x_26);
x_28 = lean_st_ref_set(x_3, x_27, x_13);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 x_30 = x_28;
} else {
 lean_dec_ref(x_28);
 x_30 = lean_box(0);
}
x_31 = lean_box(x_9);
if (lean_is_scalar(x_30)) {
 x_32 = lean_alloc_ctor(0, 2, 0);
} else {
 x_32 = x_30;
}
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_29);
return x_32;
}
}
block_39:
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 0);
lean_inc(x_36);
lean_dec_ref(x_34);
x_37 = lean_ctor_get(x_35, 1);
lean_inc_ref(x_37);
lean_dec(x_35);
x_38 = lean_unbox(x_36);
lean_dec(x_36);
x_9 = x_38;
x_10 = x_37;
goto block_33;
}
}
else
{
lean_object* x_48; lean_object* x_49; uint8_t x_50; lean_object* x_51; lean_object* x_67; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; 
x_48 = lean_ctor_get(x_5, 0);
x_49 = lean_ctor_get(x_5, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_5);
x_73 = lean_ctor_get(x_48, 0);
lean_inc_ref(x_73);
lean_dec(x_48);
x_74 = lean_alloc_closure((void*)(l_Lean_exprDependsOn___at___Lean_MVarId_clear_spec__5___redArg___lam__0___boxed), 1, 0);
x_75 = lean_alloc_closure((void*)(l_Lean_exprDependsOn___at___Lean_MVarId_clear_spec__5___redArg___lam__1___boxed), 2, 1);
lean_closure_set(x_75, 0, x_2);
x_76 = l_Lean_exprDependsOn___at___Lean_MVarId_clear_spec__5___redArg___closed__4;
lean_inc_ref(x_73);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_73);
x_78 = l_Lean_Expr_hasFVar(x_1);
if (x_78 == 0)
{
uint8_t x_79; 
x_79 = l_Lean_Expr_hasMVar(x_1);
if (x_79 == 0)
{
lean_dec_ref(x_77);
lean_dec_ref(x_75);
lean_dec_ref(x_74);
lean_dec_ref(x_1);
x_50 = x_79;
x_51 = x_73;
goto block_66;
}
else
{
lean_object* x_80; 
lean_dec_ref(x_73);
x_80 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_75, x_74, x_1, x_77);
x_67 = x_80;
goto block_72;
}
}
else
{
lean_object* x_81; 
lean_dec_ref(x_73);
x_81 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_75, x_74, x_1, x_77);
x_67 = x_81;
goto block_72;
}
block_66:
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_52 = lean_st_ref_take(x_3, x_49);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec_ref(x_52);
x_55 = lean_ctor_get(x_53, 1);
lean_inc_ref(x_55);
x_56 = lean_ctor_get(x_53, 2);
lean_inc(x_56);
x_57 = lean_ctor_get(x_53, 3);
lean_inc_ref(x_57);
x_58 = lean_ctor_get(x_53, 4);
lean_inc_ref(x_58);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 lean_ctor_release(x_53, 1);
 lean_ctor_release(x_53, 2);
 lean_ctor_release(x_53, 3);
 lean_ctor_release(x_53, 4);
 x_59 = x_53;
} else {
 lean_dec_ref(x_53);
 x_59 = lean_box(0);
}
if (lean_is_scalar(x_59)) {
 x_60 = lean_alloc_ctor(0, 5, 0);
} else {
 x_60 = x_59;
}
lean_ctor_set(x_60, 0, x_51);
lean_ctor_set(x_60, 1, x_55);
lean_ctor_set(x_60, 2, x_56);
lean_ctor_set(x_60, 3, x_57);
lean_ctor_set(x_60, 4, x_58);
x_61 = lean_st_ref_set(x_3, x_60, x_54);
x_62 = lean_ctor_get(x_61, 1);
lean_inc(x_62);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 x_63 = x_61;
} else {
 lean_dec_ref(x_61);
 x_63 = lean_box(0);
}
x_64 = lean_box(x_50);
if (lean_is_scalar(x_63)) {
 x_65 = lean_alloc_ctor(0, 2, 0);
} else {
 x_65 = x_63;
}
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_62);
return x_65;
}
block_72:
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_68 = lean_ctor_get(x_67, 1);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 0);
lean_inc(x_69);
lean_dec_ref(x_67);
x_70 = lean_ctor_get(x_68, 1);
lean_inc_ref(x_70);
lean_dec(x_68);
x_71 = lean_unbox(x_69);
lean_dec(x_69);
x_50 = x_71;
x_51 = x_70;
goto block_66;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___Lean_MVarId_clear_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_exprDependsOn___at___Lean_MVarId_clear_spec__5___redArg(x_1, x_2, x_4, x_7);
return x_8;
}
}
LEAN_EXPORT uint8_t l_Lean_MVarId_clear___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_2, 1);
x_4 = l_Lean_Expr_fvarId_x21(x_3);
x_5 = lean_name_eq(x_4, x_1);
lean_dec(x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_MVarId_clear___lam__1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unknown variable '", 18, 18);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_clear___lam__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MVarId_clear___lam__1___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MVarId_clear___lam__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("target depends on '", 19, 19);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_clear___lam__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MVarId_clear___lam__1___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_clear___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_32; 
lean_inc(x_2);
lean_inc(x_1);
x_32 = l_Lean_MVarId_checkNotAssigned(x_1, x_2, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
lean_dec_ref(x_32);
x_34 = lean_ctor_get(x_5, 2);
lean_inc_ref(x_34);
lean_inc_ref(x_34);
x_35 = l_Lean_LocalContext_contains(x_34, x_3);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
lean_dec_ref(x_34);
lean_dec_ref(x_4);
x_36 = l_Lean_MVarId_clear___lam__1___closed__1;
x_37 = l_Lean_Expr_fvar___override(x_3);
x_38 = l_Lean_MessageData_ofExpr(x_37);
x_39 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_39, 0, x_36);
lean_ctor_set(x_39, 1, x_38);
x_40 = l_Lean_PersistentArray_forMAux___at___Lean_PersistentArray_forM___at___Lean_LocalContext_forM___at___Lean_MVarId_clear_spec__0_spec__0_spec__0___lam__0___closed__5;
x_41 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_41);
x_43 = l_Lean_Meta_throwTacticEx___redArg(x_2, x_1, x_42, x_5, x_6, x_7, x_8, x_33);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_44 = !lean_is_exclusive(x_43);
if (x_44 == 0)
{
return x_43;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_43, 0);
x_46 = lean_ctor_get(x_43, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_43);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
else
{
lean_object* x_48; 
lean_inc(x_1);
x_48 = l_Lean_MVarId_getTag(x_1, x_5, x_6, x_7, x_8, x_33);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec_ref(x_48);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_1);
lean_inc(x_2);
lean_inc(x_3);
x_51 = l_Lean_LocalContext_forM___at___Lean_MVarId_clear_spec__0(x_3, x_2, x_1, x_34, x_5, x_6, x_7, x_8, x_50);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_51, 1);
lean_inc(x_52);
lean_dec_ref(x_51);
lean_inc(x_1);
x_53 = l_Lean_MVarId_getDecl(x_1, x_5, x_6, x_7, x_8, x_52);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec_ref(x_53);
x_56 = lean_ctor_get(x_54, 2);
lean_inc_ref(x_56);
lean_dec(x_54);
lean_inc(x_3);
lean_inc_ref(x_56);
x_57 = l_Lean_exprDependsOn___at___Lean_MVarId_clear_spec__5___redArg(x_56, x_3, x_6, x_55);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_unbox(x_58);
lean_dec(x_58);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_2);
x_60 = lean_ctor_get(x_57, 1);
lean_inc(x_60);
lean_dec_ref(x_57);
x_61 = l_Lean_Meta_getLocalInstances___redArg(x_5, x_60);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec_ref(x_61);
x_64 = lean_local_ctx_erase(x_34, x_3);
x_65 = lean_unsigned_to_nat(0u);
x_66 = l_Array_findFinIdx_x3f_loop___redArg(x_4, x_62, x_65);
if (lean_obj_tag(x_66) == 0)
{
x_10 = x_6;
x_11 = x_8;
x_12 = x_7;
x_13 = x_56;
x_14 = x_64;
x_15 = x_63;
x_16 = x_5;
x_17 = x_49;
x_18 = x_62;
goto block_31;
}
else
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
lean_dec_ref(x_66);
x_68 = l_Array_eraseIdx___redArg(x_62, x_67);
x_10 = x_6;
x_11 = x_8;
x_12 = x_7;
x_13 = x_56;
x_14 = x_64;
x_15 = x_63;
x_16 = x_5;
x_17 = x_49;
x_18 = x_68;
goto block_31;
}
}
else
{
uint8_t x_69; 
lean_dec_ref(x_56);
lean_dec(x_49);
lean_dec_ref(x_34);
lean_dec_ref(x_4);
x_69 = !lean_is_exclusive(x_57);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; 
x_70 = lean_ctor_get(x_57, 1);
x_71 = lean_ctor_get(x_57, 0);
lean_dec(x_71);
x_72 = l_Lean_MVarId_clear___lam__1___closed__3;
x_73 = l_Lean_Expr_fvar___override(x_3);
x_74 = l_Lean_MessageData_ofExpr(x_73);
lean_ctor_set_tag(x_57, 7);
lean_ctor_set(x_57, 1, x_74);
lean_ctor_set(x_57, 0, x_72);
x_75 = l_Lean_PersistentArray_forMAux___at___Lean_PersistentArray_forM___at___Lean_LocalContext_forM___at___Lean_MVarId_clear_spec__0_spec__0_spec__0___lam__0___closed__5;
x_76 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_76, 0, x_57);
lean_ctor_set(x_76, 1, x_75);
x_77 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_77, 0, x_76);
x_78 = l_Lean_Meta_throwTacticEx___redArg(x_2, x_1, x_77, x_5, x_6, x_7, x_8, x_70);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_79 = !lean_is_exclusive(x_78);
if (x_79 == 0)
{
return x_78;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_78, 0);
x_81 = lean_ctor_get(x_78, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_78);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
return x_82;
}
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_83 = lean_ctor_get(x_57, 1);
lean_inc(x_83);
lean_dec(x_57);
x_84 = l_Lean_MVarId_clear___lam__1___closed__3;
x_85 = l_Lean_Expr_fvar___override(x_3);
x_86 = l_Lean_MessageData_ofExpr(x_85);
x_87 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_87, 0, x_84);
lean_ctor_set(x_87, 1, x_86);
x_88 = l_Lean_PersistentArray_forMAux___at___Lean_PersistentArray_forM___at___Lean_LocalContext_forM___at___Lean_MVarId_clear_spec__0_spec__0_spec__0___lam__0___closed__5;
x_89 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
x_90 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_90, 0, x_89);
x_91 = l_Lean_Meta_throwTacticEx___redArg(x_2, x_1, x_90, x_5, x_6, x_7, x_8, x_83);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_91, 1);
lean_inc(x_93);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 lean_ctor_release(x_91, 1);
 x_94 = x_91;
} else {
 lean_dec_ref(x_91);
 x_94 = lean_box(0);
}
if (lean_is_scalar(x_94)) {
 x_95 = lean_alloc_ctor(1, 2, 0);
} else {
 x_95 = x_94;
}
lean_ctor_set(x_95, 0, x_92);
lean_ctor_set(x_95, 1, x_93);
return x_95;
}
}
}
else
{
uint8_t x_96; 
lean_dec(x_49);
lean_dec_ref(x_34);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_96 = !lean_is_exclusive(x_53);
if (x_96 == 0)
{
return x_53;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_53, 0);
x_98 = lean_ctor_get(x_53, 1);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_53);
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
lean_dec(x_49);
lean_dec_ref(x_34);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_100 = !lean_is_exclusive(x_51);
if (x_100 == 0)
{
return x_51;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_51, 0);
x_102 = lean_ctor_get(x_51, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_51);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
return x_103;
}
}
}
else
{
uint8_t x_104; 
lean_dec_ref(x_34);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_104 = !lean_is_exclusive(x_48);
if (x_104 == 0)
{
return x_48;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_105 = lean_ctor_get(x_48, 0);
x_106 = lean_ctor_get(x_48, 1);
lean_inc(x_106);
lean_inc(x_105);
lean_dec(x_48);
x_107 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_107, 0, x_105);
lean_ctor_set(x_107, 1, x_106);
return x_107;
}
}
}
}
else
{
uint8_t x_108; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_108 = !lean_is_exclusive(x_32);
if (x_108 == 0)
{
return x_32;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = lean_ctor_get(x_32, 0);
x_110 = lean_ctor_get(x_32, 1);
lean_inc(x_110);
lean_inc(x_109);
lean_dec(x_32);
x_111 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_111, 0, x_109);
lean_ctor_set(x_111, 1, x_110);
return x_111;
}
}
block_31:
{
uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_19 = 2;
x_20 = lean_unsigned_to_nat(0u);
x_21 = l_Lean_Meta_mkFreshExprMVarAt(x_14, x_18, x_13, x_19, x_17, x_20, x_16, x_10, x_12, x_11, x_15);
lean_dec(x_11);
lean_dec_ref(x_12);
lean_dec_ref(x_16);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec_ref(x_21);
lean_inc(x_22);
x_24 = l_Lean_MVarId_assign___at___Lean_Meta_getLevel_spec__0___redArg(x_1, x_22, x_10, x_23);
lean_dec(x_10);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_24, 0);
lean_dec(x_26);
x_27 = l_Lean_Expr_mvarId_x21(x_22);
lean_dec(x_22);
lean_ctor_set(x_24, 0, x_27);
return x_24;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_24, 1);
lean_inc(x_28);
lean_dec(x_24);
x_29 = l_Lean_Expr_mvarId_x21(x_22);
lean_dec(x_22);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
return x_30;
}
}
}
}
static lean_object* _init_l_Lean_MVarId_clear___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("clear", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_clear___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MVarId_clear___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_clear(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_inc(x_2);
x_8 = lean_alloc_closure((void*)(l_Lean_MVarId_clear___lam__0___boxed), 2, 1);
lean_closure_set(x_8, 0, x_2);
x_9 = l_Lean_MVarId_clear___closed__1;
lean_inc(x_1);
x_10 = lean_alloc_closure((void*)(l_Lean_MVarId_clear___lam__1), 9, 4);
lean_closure_set(x_10, 0, x_1);
lean_closure_set(x_10, 1, x_9);
lean_closure_set(x_10, 2, x_2);
lean_closure_set(x_10, 3, x_8);
x_11 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp_spec__1___redArg(x_1, x_10, x_3, x_4, x_5, x_6, x_7);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_PersistentArray_forMAux___at___Lean_PersistentArray_forM___at___Lean_LocalContext_forM___at___Lean_MVarId_clear_spec__0_spec__0_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_14 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_15 = l_Array_foldlMUnsafe_fold___at___Lean_PersistentArray_forMAux___at___Lean_PersistentArray_forM___at___Lean_LocalContext_forM___at___Lean_MVarId_clear_spec__0_spec__0_spec__0_spec__0(x_1, x_2, x_3, x_4, x_13, x_14, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec_ref(x_4);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_PersistentArray_forMAux___at___Lean_PersistentArray_forM___at___Lean_LocalContext_forM___at___Lean_MVarId_clear_spec__0_spec__0_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = l_Array_foldlMUnsafe_fold___at___Lean_PersistentArray_forMAux___at___Lean_PersistentArray_forM___at___Lean_LocalContext_forM___at___Lean_MVarId_clear_spec__0_spec__0_spec__0_spec__1(x_1, x_2, x_11, x_12, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec_ref(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___at___Lean_PersistentArray_forM___at___Lean_LocalContext_forM___at___Lean_MVarId_clear_spec__0_spec__0_spec__0___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_2);
x_12 = l_Lean_PersistentArray_forMAux___at___Lean_PersistentArray_forM___at___Lean_LocalContext_forM___at___Lean_MVarId_clear_spec__0_spec__0_spec__0___lam__0(x_1, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___at___Lean_PersistentArray_forM___at___Lean_LocalContext_forM___at___Lean_MVarId_clear_spec__0_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_PersistentArray_forMAux___at___Lean_PersistentArray_forM___at___Lean_LocalContext_forM___at___Lean_MVarId_clear_spec__0_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec_ref(x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___at___Lean_LocalContext_forM___at___Lean_MVarId_clear_spec__0_spec__0___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_2);
x_12 = l_Lean_PersistentArray_forM___at___Lean_LocalContext_forM___at___Lean_MVarId_clear_spec__0_spec__0___lam__0(x_1, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___at___Lean_LocalContext_forM___at___Lean_MVarId_clear_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_PersistentArray_forM___at___Lean_LocalContext_forM___at___Lean_MVarId_clear_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec_ref(x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_forM___at___Lean_MVarId_clear_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_LocalContext_forM___at___Lean_MVarId_clear_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec_ref(x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___Lean_MVarId_clear_spec__5___redArg___lam__0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_exprDependsOn___at___Lean_MVarId_clear_spec__5___redArg___lam__0(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___Lean_MVarId_clear_spec__5___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_exprDependsOn___at___Lean_MVarId_clear_spec__5___redArg___lam__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___Lean_MVarId_clear_spec__5___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_exprDependsOn___at___Lean_MVarId_clear_spec__5___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___Lean_MVarId_clear_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_exprDependsOn___at___Lean_MVarId_clear_spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_clear___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_MVarId_clear___lam__0(x_1, x_2);
lean_dec_ref(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_tryClear(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = l_Lean_Meta_saveState___redArg(x_4, x_6, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec_ref(x_8);
lean_inc(x_6);
lean_inc(x_4);
lean_inc(x_1);
x_11 = l_Lean_MVarId_clear(x_1, x_2, x_3, x_4, x_5, x_6, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_21; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
x_21 = l_Lean_Exception_isInterrupt(x_12);
if (x_21 == 0)
{
uint8_t x_22; 
x_22 = l_Lean_Exception_isRuntime(x_12);
lean_dec(x_12);
x_14 = x_22;
goto block_20;
}
else
{
lean_dec(x_12);
x_14 = x_21;
goto block_20;
}
block_20:
{
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
lean_dec_ref(x_11);
x_15 = l_Lean_Meta_SavedState_restore___redArg(x_9, x_4, x_6, x_13);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_9);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_15, 0);
lean_dec(x_17);
lean_ctor_set(x_15, 0, x_1);
return x_15;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_1);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
else
{
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
return x_11;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Lean_MVarId_tryClearMany_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_eq(x_2, x_3);
if (x_10 == 0)
{
size_t x_11; size_t x_12; lean_object* x_13; lean_object* x_14; 
x_11 = 1;
x_12 = lean_usize_sub(x_2, x_11);
x_13 = lean_array_uget(x_1, x_12);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_14 = l_Lean_MVarId_tryClear(x_4, x_13, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec_ref(x_14);
x_2 = x_12;
x_4 = x_15;
x_9 = x_16;
goto _start;
}
else
{
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_14;
}
}
else
{
lean_object* x_18; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_4);
lean_ctor_set(x_18, 1, x_9);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_tryClearMany(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_array_get_size(x_2);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_nat_dec_lt(x_9, x_8);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_1);
lean_ctor_set(x_11, 1, x_7);
return x_11;
}
else
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_usize_of_nat(x_8);
lean_dec(x_8);
x_13 = 0;
x_14 = l_Array_foldrMUnsafe_fold___at___Lean_MVarId_tryClearMany_spec__0(x_2, x_12, x_13, x_1, x_3, x_4, x_5, x_6, x_7);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Lean_MVarId_tryClearMany_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l_Array_foldrMUnsafe_fold___at___Lean_MVarId_tryClearMany_spec__0(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec_ref(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_tryClearMany___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_MVarId_tryClearMany(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Lean_MVarId_tryClearMany_x27_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_eq(x_2, x_3);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; size_t x_14; size_t x_15; lean_object* x_16; lean_object* x_17; 
x_11 = lean_ctor_get(x_4, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_4, 1);
lean_inc(x_12);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 x_13 = x_4;
} else {
 lean_dec_ref(x_4);
 x_13 = lean_box(0);
}
x_14 = 1;
x_15 = lean_usize_sub(x_2, x_14);
x_16 = lean_array_uget(x_1, x_15);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_16);
lean_inc(x_11);
x_17 = l_Lean_MVarId_tryClear(x_11, x_16, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_24; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec_ref(x_17);
x_24 = lean_name_eq(x_11, x_18);
lean_dec(x_11);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_array_push(x_12, x_16);
x_20 = x_25;
goto block_23;
}
else
{
lean_dec(x_16);
x_20 = x_12;
goto block_23;
}
block_23:
{
lean_object* x_21; 
if (lean_is_scalar(x_13)) {
 x_21 = lean_alloc_ctor(0, 2, 0);
} else {
 x_21 = x_13;
}
lean_ctor_set(x_21, 0, x_18);
lean_ctor_set(x_21, 1, x_20);
x_2 = x_15;
x_4 = x_21;
x_9 = x_19;
goto _start;
}
}
else
{
uint8_t x_26; 
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_26 = !lean_is_exclusive(x_17);
if (x_26 == 0)
{
return x_17;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_17, 0);
x_28 = lean_ctor_get(x_17, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_17);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
else
{
lean_object* x_30; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_4);
lean_ctor_set(x_30, 1, x_9);
return x_30;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_tryClearMany_x27___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_8 = lean_ctor_get(x_3, 2);
lean_inc_ref(x_8);
x_9 = l_Lean_LocalContext_sortFVarsByContextOrder(x_8, x_1);
x_10 = lean_array_get_size(x_9);
x_11 = lean_mk_empty_array_with_capacity(x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_2);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_nat_dec_lt(x_13, x_10);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_12);
lean_ctor_set(x_15, 1, x_7);
return x_15;
}
else
{
size_t x_16; size_t x_17; lean_object* x_18; 
x_16 = lean_usize_of_nat(x_10);
lean_dec(x_10);
x_17 = 0;
x_18 = l_Array_foldrMUnsafe_fold___at___Lean_MVarId_tryClearMany_x27_spec__0(x_9, x_16, x_17, x_12, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_9);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_tryClearMany_x27(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
lean_inc(x_1);
x_8 = lean_alloc_closure((void*)(l_Lean_MVarId_tryClearMany_x27___lam__0), 7, 2);
lean_closure_set(x_8, 0, x_2);
lean_closure_set(x_8, 1, x_1);
x_9 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp_spec__1___redArg(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Lean_MVarId_tryClearMany_x27_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l_Array_foldrMUnsafe_fold___at___Lean_MVarId_tryClearMany_x27_spec__0(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec_ref(x_1);
return x_12;
}
}
lean_object* initialize_Lean_Meta_Tactic_Util(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Clear(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Util(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_PersistentArray_forMAux___at___Lean_PersistentArray_forM___at___Lean_LocalContext_forM___at___Lean_MVarId_clear_spec__0_spec__0_spec__0___lam__0___closed__0 = _init_l_Lean_PersistentArray_forMAux___at___Lean_PersistentArray_forM___at___Lean_LocalContext_forM___at___Lean_MVarId_clear_spec__0_spec__0_spec__0___lam__0___closed__0();
lean_mark_persistent(l_Lean_PersistentArray_forMAux___at___Lean_PersistentArray_forM___at___Lean_LocalContext_forM___at___Lean_MVarId_clear_spec__0_spec__0_spec__0___lam__0___closed__0);
l_Lean_PersistentArray_forMAux___at___Lean_PersistentArray_forM___at___Lean_LocalContext_forM___at___Lean_MVarId_clear_spec__0_spec__0_spec__0___lam__0___closed__1 = _init_l_Lean_PersistentArray_forMAux___at___Lean_PersistentArray_forM___at___Lean_LocalContext_forM___at___Lean_MVarId_clear_spec__0_spec__0_spec__0___lam__0___closed__1();
lean_mark_persistent(l_Lean_PersistentArray_forMAux___at___Lean_PersistentArray_forM___at___Lean_LocalContext_forM___at___Lean_MVarId_clear_spec__0_spec__0_spec__0___lam__0___closed__1);
l_Lean_PersistentArray_forMAux___at___Lean_PersistentArray_forM___at___Lean_LocalContext_forM___at___Lean_MVarId_clear_spec__0_spec__0_spec__0___lam__0___closed__2 = _init_l_Lean_PersistentArray_forMAux___at___Lean_PersistentArray_forM___at___Lean_LocalContext_forM___at___Lean_MVarId_clear_spec__0_spec__0_spec__0___lam__0___closed__2();
lean_mark_persistent(l_Lean_PersistentArray_forMAux___at___Lean_PersistentArray_forM___at___Lean_LocalContext_forM___at___Lean_MVarId_clear_spec__0_spec__0_spec__0___lam__0___closed__2);
l_Lean_PersistentArray_forMAux___at___Lean_PersistentArray_forM___at___Lean_LocalContext_forM___at___Lean_MVarId_clear_spec__0_spec__0_spec__0___lam__0___closed__3 = _init_l_Lean_PersistentArray_forMAux___at___Lean_PersistentArray_forM___at___Lean_LocalContext_forM___at___Lean_MVarId_clear_spec__0_spec__0_spec__0___lam__0___closed__3();
lean_mark_persistent(l_Lean_PersistentArray_forMAux___at___Lean_PersistentArray_forM___at___Lean_LocalContext_forM___at___Lean_MVarId_clear_spec__0_spec__0_spec__0___lam__0___closed__3);
l_Lean_PersistentArray_forMAux___at___Lean_PersistentArray_forM___at___Lean_LocalContext_forM___at___Lean_MVarId_clear_spec__0_spec__0_spec__0___lam__0___closed__4 = _init_l_Lean_PersistentArray_forMAux___at___Lean_PersistentArray_forM___at___Lean_LocalContext_forM___at___Lean_MVarId_clear_spec__0_spec__0_spec__0___lam__0___closed__4();
lean_mark_persistent(l_Lean_PersistentArray_forMAux___at___Lean_PersistentArray_forM___at___Lean_LocalContext_forM___at___Lean_MVarId_clear_spec__0_spec__0_spec__0___lam__0___closed__4);
l_Lean_PersistentArray_forMAux___at___Lean_PersistentArray_forM___at___Lean_LocalContext_forM___at___Lean_MVarId_clear_spec__0_spec__0_spec__0___lam__0___closed__5 = _init_l_Lean_PersistentArray_forMAux___at___Lean_PersistentArray_forM___at___Lean_LocalContext_forM___at___Lean_MVarId_clear_spec__0_spec__0_spec__0___lam__0___closed__5();
lean_mark_persistent(l_Lean_PersistentArray_forMAux___at___Lean_PersistentArray_forM___at___Lean_LocalContext_forM___at___Lean_MVarId_clear_spec__0_spec__0_spec__0___lam__0___closed__5);
l_Lean_exprDependsOn___at___Lean_MVarId_clear_spec__5___redArg___closed__0 = _init_l_Lean_exprDependsOn___at___Lean_MVarId_clear_spec__5___redArg___closed__0();
lean_mark_persistent(l_Lean_exprDependsOn___at___Lean_MVarId_clear_spec__5___redArg___closed__0);
l_Lean_exprDependsOn___at___Lean_MVarId_clear_spec__5___redArg___closed__1 = _init_l_Lean_exprDependsOn___at___Lean_MVarId_clear_spec__5___redArg___closed__1();
lean_mark_persistent(l_Lean_exprDependsOn___at___Lean_MVarId_clear_spec__5___redArg___closed__1);
l_Lean_exprDependsOn___at___Lean_MVarId_clear_spec__5___redArg___closed__2 = _init_l_Lean_exprDependsOn___at___Lean_MVarId_clear_spec__5___redArg___closed__2();
lean_mark_persistent(l_Lean_exprDependsOn___at___Lean_MVarId_clear_spec__5___redArg___closed__2);
l_Lean_exprDependsOn___at___Lean_MVarId_clear_spec__5___redArg___closed__3 = _init_l_Lean_exprDependsOn___at___Lean_MVarId_clear_spec__5___redArg___closed__3();
lean_mark_persistent(l_Lean_exprDependsOn___at___Lean_MVarId_clear_spec__5___redArg___closed__3);
l_Lean_exprDependsOn___at___Lean_MVarId_clear_spec__5___redArg___closed__4 = _init_l_Lean_exprDependsOn___at___Lean_MVarId_clear_spec__5___redArg___closed__4();
lean_mark_persistent(l_Lean_exprDependsOn___at___Lean_MVarId_clear_spec__5___redArg___closed__4);
l_Lean_MVarId_clear___lam__1___closed__0 = _init_l_Lean_MVarId_clear___lam__1___closed__0();
lean_mark_persistent(l_Lean_MVarId_clear___lam__1___closed__0);
l_Lean_MVarId_clear___lam__1___closed__1 = _init_l_Lean_MVarId_clear___lam__1___closed__1();
lean_mark_persistent(l_Lean_MVarId_clear___lam__1___closed__1);
l_Lean_MVarId_clear___lam__1___closed__2 = _init_l_Lean_MVarId_clear___lam__1___closed__2();
lean_mark_persistent(l_Lean_MVarId_clear___lam__1___closed__2);
l_Lean_MVarId_clear___lam__1___closed__3 = _init_l_Lean_MVarId_clear___lam__1___closed__3();
lean_mark_persistent(l_Lean_MVarId_clear___lam__1___closed__3);
l_Lean_MVarId_clear___closed__0 = _init_l_Lean_MVarId_clear___closed__0();
lean_mark_persistent(l_Lean_MVarId_clear___closed__0);
l_Lean_MVarId_clear___closed__1 = _init_l_Lean_MVarId_clear___closed__1();
lean_mark_persistent(l_Lean_MVarId_clear___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
