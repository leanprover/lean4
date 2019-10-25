// Lean compiler output
// Module: Init.Lean.TypeContext
// Imports: Init.Control.Reader Init.Lean.NameGenerator Init.Lean.Environment Init.Lean.LocalContext Init.Lean.Trace
#include "runtime/lean.h"
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
lean_object* l_Lean_AbstractTypeContext_instantiateExprMVars___rarg___closed__1;
lean_object* l___private_Init_Lean_TypeContext_1__getOptions(lean_object*, lean_object*);
lean_object* l_Lean_AbstractTypeContext_InstantiateExprMVars_main___main___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_update_app(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_AbstractTypeContext_InstantiateExprMVars_checkCache___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_List_mmap___main___at_Lean_AbstractTypeContext_InstantiateExprMVars_main___main___spec__1(lean_object*);
lean_object* l_Lean_AbstractTypeContext_InstantiateExprMVars_visit(lean_object*);
lean_object* l_Lean_AbstractTypeContext_tracer___closed__3;
lean_object* l_List_foldr___main___at_Lean_AbstractTypeContext_hasAssignedMVar___main___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
size_t lean_expr_hash(lean_object*);
lean_object* l_Lean_AbstractTypeContext_isExprAssigned___rarg___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_level_has_mvar(lean_object*);
uint8_t l_Lean_metavarContextIsAbstractMetavarContext___lambda__1(lean_object*);
lean_object* l_Lean_MetavarContext_getExprMVarLCtx(lean_object*, lean_object*);
uint8_t l_Lean_AbstractTypeContext_hasAssignedMVar___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_metavar_ctx_erase_delayed(lean_object*, lean_object*);
lean_object* l_Lean_AbstractTypeContext_hasAssignedMVar___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_TCState_backtrackable___lambda__2(lean_object*, lean_object*);
lean_object* l_Lean_TCState_backtrackable___lambda__1___boxed(lean_object*);
lean_object* lean_metavar_ctx_get_delayed_assignment(lean_object*, lean_object*);
lean_object* l_Lean_Expr_updateLet_x21(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_MetavarContext_mkMetavarContext___closed__1;
lean_object* l_Lean_AbstractTypeContext_isLevelAssigned(lean_object*);
lean_object* l___private_Init_Lean_TypeContext_2__getTraceState(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_HashMapImp_find___at_Lean_AbstractTypeContext_InstantiateExprMVars_checkCache___spec__1___boxed(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_AbstractTypeContext_InstantiateExprMVars_checkCache(lean_object*);
lean_object* l___private_Init_Lean_TypeContext_2__getTraceState___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_metavar_ctx_get_expr_assignment(lean_object*, lean_object*);
lean_object* l_Lean_metavarContextIsAbstractMetavarContext___closed__3;
lean_object* l___private_Init_Lean_TypeContext_1__getOptions___rarg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_getExprMVarType(lean_object*, lean_object*);
lean_object* l_Lean_AbstractTypeContext_InstantiateExprMVars_main___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_AssocList_mfoldl___main___at_Lean_AbstractTypeContext_InstantiateExprMVars_checkCache___spec__7(lean_object*, lean_object*);
uint8_t l_Lean_AbstractTypeContext_isLevelAssigned___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_update_forall(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* lean_level_update_succ(lean_object*, lean_object*);
lean_object* l_Lean_TCState_backtrackable___closed__3;
lean_object* l_Lean_AbstractTypeContext_hasAssignedMVar(lean_object*);
lean_object* l_Lean_AbstractTypeContext_InstantiateExprMVars_main___main(lean_object*);
lean_object* l_Lean_AbstractTypeContext_hasAssignedMVar___main(lean_object*);
lean_object* l_Lean_AbstractTypeContext_instantiateLevelMVars(lean_object*);
lean_object* l_Lean_TCState_backtrackable___lambda__1(lean_object*);
lean_object* l_List_foldr___main___at_Lean_AbstractTypeContext_hasAssignedMVar___main___spec__1(lean_object*);
lean_object* l___private_Init_Lean_TypeContext_1__getOptions___rarg(lean_object*, lean_object*);
lean_object* l_Lean_AbstractTypeContext_instantiateExprMVars___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_List_mmap___main___at_Lean_AbstractTypeContext_InstantiateExprMVars_main___main___spec__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_HashMapImp_expand___at_Lean_AbstractTypeContext_InstantiateExprMVars_checkCache___spec__5(lean_object*, lean_object*);
lean_object* l_Lean_metavarContextIsAbstractMetavarContext;
lean_object* l_Lean_TCState_backtrackable___closed__2;
lean_object* l_Lean_AbstractTypeContext_hasAssignedLevelMVar___rarg___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_constName___closed__1;
lean_object* l_AssocList_contains___main___at_Lean_AbstractTypeContext_InstantiateExprMVars_checkCache___spec__4___boxed(lean_object*, lean_object*);
lean_object* l_Lean_AbstractTypeContext_isLevelAssigned___rarg___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Lean_AbstractTypeContext_tracer___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_AbstractTypeContext_hasAssignedMVar___main___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_metavarContextIsAbstractMetavarContext___closed__2;
lean_object* l_Lean_AbstractTypeContext_tracer___closed__2;
extern lean_object* l_Lean_Expr_updateProj_x21___closed__1;
lean_object* l_HashMapImp_insert___at_Lean_AbstractTypeContext_InstantiateExprMVars_checkCache___spec__3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_AbstractTypeContext_hasAssignedLevelMVar___main(lean_object*);
uint8_t l_AssocList_contains___main___at_Lean_AbstractTypeContext_InstantiateExprMVars_checkCache___spec__4(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_expr_update_const(lean_object*, lean_object*);
lean_object* l_HashMapImp_moveEntries___main___at_Lean_AbstractTypeContext_InstantiateExprMVars_checkCache___spec__6(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_metavarContextIsAbstractMetavarContext___lambda__1___boxed(lean_object*);
lean_object* l_Lean_metavarContextIsAbstractMetavarContext___closed__7;
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_metavar_ctx_assign_expr(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_AbstractTypeContext_tracer___closed__1;
lean_object* lean_expr_update_proj(lean_object*, lean_object*);
lean_object* l_HashMapImp_find___at_Lean_AbstractTypeContext_InstantiateExprMVars_checkCache___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_metavarContextIsAbstractMetavarContext___closed__8;
lean_object* l_Lean_AbstractTypeContext_tracer___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_update_mdata(lean_object*, lean_object*);
lean_object* l_Lean_TCState_backtrackable___closed__1;
lean_object* l_Lean_TCState_backtrackable(lean_object*, lean_object*);
lean_object* l_Lean_AbstractTypeContext_instantiateLevelMVars___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_AbstractTypeContext_InstantiateExprMVars_main(lean_object*);
lean_object* l_Lean_metavarContextIsAbstractMetavarContext___closed__4;
lean_object* l_Lean_AbstractTypeContext_tracer(lean_object*, lean_object*);
lean_object* lean_metavar_ctx_get_level_assignment(lean_object*, lean_object*);
lean_object* lean_expr_update_lambda(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_metavarContextIsAbstractMetavarContext___closed__6;
extern lean_object* l_Lean_Level_updateSucc_x21___closed__1;
lean_object* l_Lean_metavarContextIsAbstractMetavarContext___closed__9;
lean_object* l_Lean_AbstractTypeContext_instantiateLevelMVars___main___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_TypeContext_2__getTraceState___rarg(lean_object*);
lean_object* l_Lean_AbstractTypeContext_InstantiateExprMVars_getMCtx___rarg(lean_object*);
lean_object* l_Lean_metavarContextIsAbstractMetavarContext___closed__11;
lean_object* l_Lean_AbstractTypeContext_tracer___closed__4;
extern lean_object* l_Lean_Level_updateIMax_x21___closed__1;
size_t lean_usize_modn(size_t, lean_object*);
lean_object* l_Lean_AbstractTypeContext_hasAssignedLevelMVar___main___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_AssocList_find___main___at_Lean_AbstractTypeContext_InstantiateExprMVars_checkCache___spec__2___boxed(lean_object*, lean_object*);
uint8_t l_Lean_AbstractTypeContext_hasAssignedLevelMVar___main___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_AbstractTypeContext_isExprAssigned(lean_object*);
lean_object* l_Lean_AbstractTypeContext_InstantiateExprMVars_instantiateLevelMVars___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_AssocList_find___main___at_Lean_AbstractTypeContext_InstantiateExprMVars_checkCache___spec__2(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_AbstractTypeContext_hasAssignedMVar___main___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_metavarContextIsAbstractMetavarContext___closed__1;
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_mkHashMapImp___rarg(lean_object*);
lean_object* l_Lean_metavarContextIsAbstractMetavarContext___closed__5;
lean_object* lean_metavar_ctx_assign_delayed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t l_List_foldr___main___at_Lean_AbstractTypeContext_hasAssignedMVar___main___spec__1___rarg(lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* lean_level_update_max(lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_has_expr_mvar(lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_updateMData_x21___closed__1;
lean_object* l_Lean_AbstractTypeContext_InstantiateExprMVars_getMCtx(lean_object*);
lean_object* l_AssocList_replace___main___at_Lean_AbstractTypeContext_InstantiateExprMVars_checkCache___spec__8(lean_object*, lean_object*, lean_object*);
lean_object* l_panicWithPos___at_Lean_Expr_bindingDomain___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_AbstractTypeContext_instantiateLevelMVars___main(lean_object*);
lean_object* lean_expr_update_sort(lean_object*, lean_object*);
lean_object* l_Lean_AbstractTypeContext_InstantiateExprMVars_visit___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_AbstractTypeContext_InstantiateExprMVars_instantiateLevelMVars(lean_object*);
lean_object* lean_metavar_ctx_assign_level(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Lean_metavarContextIsAbstractMetavarContext___closed__10;
lean_object* l_mkHashMap___at_Lean_AbstractTypeContext_instantiateExprMVars___spec__1(lean_object*);
uint8_t l_Lean_AbstractTypeContext_isExprAssigned___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_panicWithPos___at_Lean_Level_updateSucc_x21___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_AbstractTypeContext_hasAssignedLevelMVar___rarg(lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_has_level_mvar(lean_object*);
lean_object* l_Lean_AbstractTypeContext_hasAssignedLevelMVar(lean_object*);
lean_object* l_Lean_AbstractTypeContext_instantiateExprMVars(lean_object*);
lean_object* l_Lean_TCState_backtrackable___lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
return x_2;
}
}
lean_object* l_Lean_TCState_backtrackable___lambda__2(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 0);
lean_dec(x_4);
lean_ctor_set(x_1, 0, x_2);
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_1, 2);
x_7 = lean_ctor_get(x_1, 3);
x_8 = lean_ctor_get_uint8(x_1, sizeof(void*)*5);
x_9 = lean_ctor_get(x_1, 4);
lean_inc(x_9);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_1);
x_10 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_10, 0, x_2);
lean_ctor_set(x_10, 1, x_5);
lean_ctor_set(x_10, 2, x_6);
lean_ctor_set(x_10, 3, x_7);
lean_ctor_set(x_10, 4, x_9);
lean_ctor_set_uint8(x_10, sizeof(void*)*5, x_8);
return x_10;
}
}
}
lean_object* _init_l_Lean_TCState_backtrackable___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_TCState_backtrackable___lambda__1___boxed), 1, 0);
return x_1;
}
}
lean_object* _init_l_Lean_TCState_backtrackable___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_TCState_backtrackable___lambda__2), 2, 0);
return x_1;
}
}
lean_object* _init_l_Lean_TCState_backtrackable___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_TCState_backtrackable___closed__1;
x_2 = l_Lean_TCState_backtrackable___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_Lean_TCState_backtrackable(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_TCState_backtrackable___closed__3;
return x_3;
}
}
lean_object* l_Lean_TCState_backtrackable___lambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_TCState_backtrackable___lambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
uint8_t l_Lean_AbstractTypeContext_isLevelAssigned___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 2);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_2(x_4, x_2, x_3);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = 0;
return x_6;
}
else
{
uint8_t x_7; 
lean_dec(x_5);
x_7 = 1;
return x_7;
}
}
}
lean_object* l_Lean_AbstractTypeContext_isLevelAssigned(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_AbstractTypeContext_isLevelAssigned___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_Lean_AbstractTypeContext_isLevelAssigned___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_AbstractTypeContext_isLevelAssigned___rarg(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
uint8_t l_Lean_AbstractTypeContext_isExprAssigned___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 5);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_2(x_4, x_2, x_3);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = 0;
return x_6;
}
else
{
uint8_t x_7; 
lean_dec(x_5);
x_7 = 1;
return x_7;
}
}
}
lean_object* l_Lean_AbstractTypeContext_isExprAssigned(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_AbstractTypeContext_isExprAssigned___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_Lean_AbstractTypeContext_isExprAssigned___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_AbstractTypeContext_isExprAssigned___rarg(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
uint8_t l_Lean_AbstractTypeContext_hasAssignedLevelMVar___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_3)) {
case 1:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
lean_inc(x_4);
x_5 = lean_level_has_mvar(x_4);
if (x_5 == 0)
{
uint8_t x_6; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_6 = 0;
return x_6;
}
else
{
x_3 = x_4;
goto _start;
}
}
case 2:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
lean_dec(x_3);
lean_inc(x_8);
x_10 = lean_level_has_mvar(x_8);
if (x_10 == 0)
{
uint8_t x_11; 
lean_dec(x_8);
lean_inc(x_9);
x_11 = lean_level_has_mvar(x_9);
if (x_11 == 0)
{
uint8_t x_12; 
lean_dec(x_9);
lean_dec(x_2);
lean_dec(x_1);
x_12 = 0;
return x_12;
}
else
{
x_3 = x_9;
goto _start;
}
}
else
{
uint8_t x_14; 
lean_inc(x_2);
lean_inc(x_1);
x_14 = l_Lean_AbstractTypeContext_hasAssignedLevelMVar___main___rarg(x_1, x_2, x_8);
if (x_14 == 0)
{
uint8_t x_15; 
lean_inc(x_9);
x_15 = lean_level_has_mvar(x_9);
if (x_15 == 0)
{
lean_dec(x_9);
lean_dec(x_2);
lean_dec(x_1);
return x_14;
}
else
{
x_3 = x_9;
goto _start;
}
}
else
{
uint8_t x_17; 
lean_dec(x_9);
lean_dec(x_2);
lean_dec(x_1);
x_17 = 1;
return x_17;
}
}
}
case 3:
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = lean_ctor_get(x_3, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_3, 1);
lean_inc(x_19);
lean_dec(x_3);
lean_inc(x_18);
x_20 = lean_level_has_mvar(x_18);
if (x_20 == 0)
{
uint8_t x_21; 
lean_dec(x_18);
lean_inc(x_19);
x_21 = lean_level_has_mvar(x_19);
if (x_21 == 0)
{
uint8_t x_22; 
lean_dec(x_19);
lean_dec(x_2);
lean_dec(x_1);
x_22 = 0;
return x_22;
}
else
{
x_3 = x_19;
goto _start;
}
}
else
{
uint8_t x_24; 
lean_inc(x_2);
lean_inc(x_1);
x_24 = l_Lean_AbstractTypeContext_hasAssignedLevelMVar___main___rarg(x_1, x_2, x_18);
if (x_24 == 0)
{
uint8_t x_25; 
lean_inc(x_19);
x_25 = lean_level_has_mvar(x_19);
if (x_25 == 0)
{
lean_dec(x_19);
lean_dec(x_2);
lean_dec(x_1);
return x_24;
}
else
{
x_3 = x_19;
goto _start;
}
}
else
{
uint8_t x_27; 
lean_dec(x_19);
lean_dec(x_2);
lean_dec(x_1);
x_27 = 1;
return x_27;
}
}
}
case 5:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_3, 0);
lean_inc(x_28);
lean_dec(x_3);
x_29 = lean_ctor_get(x_1, 2);
lean_inc(x_29);
lean_dec(x_1);
x_30 = lean_apply_2(x_29, x_2, x_28);
if (lean_obj_tag(x_30) == 0)
{
uint8_t x_31; 
x_31 = 0;
return x_31;
}
else
{
uint8_t x_32; 
lean_dec(x_30);
x_32 = 1;
return x_32;
}
}
default: 
{
uint8_t x_33; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_33 = 0;
return x_33;
}
}
}
}
lean_object* l_Lean_AbstractTypeContext_hasAssignedLevelMVar___main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_AbstractTypeContext_hasAssignedLevelMVar___main___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_Lean_AbstractTypeContext_hasAssignedLevelMVar___main___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_AbstractTypeContext_hasAssignedLevelMVar___main___rarg(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
uint8_t l_Lean_AbstractTypeContext_hasAssignedLevelMVar___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_AbstractTypeContext_hasAssignedLevelMVar___main___rarg(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_AbstractTypeContext_hasAssignedLevelMVar(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_AbstractTypeContext_hasAssignedLevelMVar___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_Lean_AbstractTypeContext_hasAssignedLevelMVar___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_AbstractTypeContext_hasAssignedLevelMVar___rarg(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
uint8_t l_List_foldr___main___at_Lean_AbstractTypeContext_hasAssignedMVar___main___spec__1___rarg(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_7 = l_List_foldr___main___at_Lean_AbstractTypeContext_hasAssignedMVar___main___spec__1___rarg(x_1, x_2, x_3, x_6);
x_8 = l_Lean_AbstractTypeContext_hasAssignedLevelMVar___main___rarg(x_1, x_2, x_5);
if (x_8 == 0)
{
return x_7;
}
else
{
uint8_t x_9; 
x_9 = 1;
return x_9;
}
}
}
}
lean_object* l_List_foldr___main___at_Lean_AbstractTypeContext_hasAssignedMVar___main___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_foldr___main___at_Lean_AbstractTypeContext_hasAssignedMVar___main___spec__1___rarg___boxed), 4, 0);
return x_2;
}
}
uint8_t l_Lean_AbstractTypeContext_hasAssignedMVar___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_3)) {
case 2:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_ctor_get(x_1, 5);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_2(x_5, x_2, x_4);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = 0;
return x_7;
}
else
{
uint8_t x_8; 
lean_dec(x_6);
x_8 = 1;
return x_8;
}
}
case 3:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_3, 0);
lean_inc(x_9);
lean_dec(x_3);
x_10 = l_Lean_AbstractTypeContext_hasAssignedLevelMVar___main___rarg(x_1, x_2, x_9);
return x_10;
}
case 4:
{
lean_object* x_11; uint8_t x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_3, 1);
lean_inc(x_11);
lean_dec(x_3);
x_12 = 0;
x_13 = l_List_foldr___main___at_Lean_AbstractTypeContext_hasAssignedMVar___main___spec__1___rarg(x_1, x_2, x_12, x_11);
return x_13;
}
case 5:
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_ctor_get(x_3, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_3, 1);
lean_inc(x_15);
lean_dec(x_3);
x_16 = lean_expr_has_expr_mvar(x_14);
if (x_16 == 0)
{
uint8_t x_17; 
x_17 = lean_expr_has_level_mvar(x_14);
if (x_17 == 0)
{
uint8_t x_18; 
lean_dec(x_14);
x_18 = lean_expr_has_expr_mvar(x_15);
if (x_18 == 0)
{
uint8_t x_19; 
x_19 = lean_expr_has_level_mvar(x_15);
if (x_19 == 0)
{
uint8_t x_20; 
lean_dec(x_15);
lean_dec(x_2);
lean_dec(x_1);
x_20 = 0;
return x_20;
}
else
{
x_3 = x_15;
goto _start;
}
}
else
{
x_3 = x_15;
goto _start;
}
}
else
{
uint8_t x_23; 
lean_inc(x_2);
lean_inc(x_1);
x_23 = l_Lean_AbstractTypeContext_hasAssignedMVar___main___rarg(x_1, x_2, x_14);
if (x_23 == 0)
{
uint8_t x_24; 
x_24 = lean_expr_has_expr_mvar(x_15);
if (x_24 == 0)
{
uint8_t x_25; 
x_25 = lean_expr_has_level_mvar(x_15);
if (x_25 == 0)
{
lean_dec(x_15);
lean_dec(x_2);
lean_dec(x_1);
return x_23;
}
else
{
x_3 = x_15;
goto _start;
}
}
else
{
x_3 = x_15;
goto _start;
}
}
else
{
uint8_t x_28; 
lean_dec(x_15);
lean_dec(x_2);
lean_dec(x_1);
x_28 = 1;
return x_28;
}
}
}
else
{
uint8_t x_29; 
lean_inc(x_2);
lean_inc(x_1);
x_29 = l_Lean_AbstractTypeContext_hasAssignedMVar___main___rarg(x_1, x_2, x_14);
if (x_29 == 0)
{
uint8_t x_30; 
x_30 = lean_expr_has_expr_mvar(x_15);
if (x_30 == 0)
{
uint8_t x_31; 
x_31 = lean_expr_has_level_mvar(x_15);
if (x_31 == 0)
{
lean_dec(x_15);
lean_dec(x_2);
lean_dec(x_1);
return x_29;
}
else
{
x_3 = x_15;
goto _start;
}
}
else
{
x_3 = x_15;
goto _start;
}
}
else
{
uint8_t x_34; 
lean_dec(x_15);
lean_dec(x_2);
lean_dec(x_1);
x_34 = 1;
return x_34;
}
}
}
case 6:
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_35 = lean_ctor_get(x_3, 1);
lean_inc(x_35);
x_36 = lean_ctor_get(x_3, 2);
lean_inc(x_36);
lean_dec(x_3);
x_37 = lean_expr_has_expr_mvar(x_35);
if (x_37 == 0)
{
uint8_t x_38; 
x_38 = lean_expr_has_level_mvar(x_35);
if (x_38 == 0)
{
uint8_t x_39; 
lean_dec(x_35);
x_39 = lean_expr_has_expr_mvar(x_36);
if (x_39 == 0)
{
uint8_t x_40; 
x_40 = lean_expr_has_level_mvar(x_36);
if (x_40 == 0)
{
uint8_t x_41; 
lean_dec(x_36);
lean_dec(x_2);
lean_dec(x_1);
x_41 = 0;
return x_41;
}
else
{
x_3 = x_36;
goto _start;
}
}
else
{
x_3 = x_36;
goto _start;
}
}
else
{
uint8_t x_44; 
lean_inc(x_2);
lean_inc(x_1);
x_44 = l_Lean_AbstractTypeContext_hasAssignedMVar___main___rarg(x_1, x_2, x_35);
if (x_44 == 0)
{
uint8_t x_45; 
x_45 = lean_expr_has_expr_mvar(x_36);
if (x_45 == 0)
{
uint8_t x_46; 
x_46 = lean_expr_has_level_mvar(x_36);
if (x_46 == 0)
{
lean_dec(x_36);
lean_dec(x_2);
lean_dec(x_1);
return x_44;
}
else
{
x_3 = x_36;
goto _start;
}
}
else
{
x_3 = x_36;
goto _start;
}
}
else
{
uint8_t x_49; 
lean_dec(x_36);
lean_dec(x_2);
lean_dec(x_1);
x_49 = 1;
return x_49;
}
}
}
else
{
uint8_t x_50; 
lean_inc(x_2);
lean_inc(x_1);
x_50 = l_Lean_AbstractTypeContext_hasAssignedMVar___main___rarg(x_1, x_2, x_35);
if (x_50 == 0)
{
uint8_t x_51; 
x_51 = lean_expr_has_expr_mvar(x_36);
if (x_51 == 0)
{
uint8_t x_52; 
x_52 = lean_expr_has_level_mvar(x_36);
if (x_52 == 0)
{
lean_dec(x_36);
lean_dec(x_2);
lean_dec(x_1);
return x_50;
}
else
{
x_3 = x_36;
goto _start;
}
}
else
{
x_3 = x_36;
goto _start;
}
}
else
{
uint8_t x_55; 
lean_dec(x_36);
lean_dec(x_2);
lean_dec(x_1);
x_55 = 1;
return x_55;
}
}
}
case 7:
{
lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_56 = lean_ctor_get(x_3, 1);
lean_inc(x_56);
x_57 = lean_ctor_get(x_3, 2);
lean_inc(x_57);
lean_dec(x_3);
x_58 = lean_expr_has_expr_mvar(x_56);
if (x_58 == 0)
{
uint8_t x_59; 
x_59 = lean_expr_has_level_mvar(x_56);
if (x_59 == 0)
{
uint8_t x_60; 
lean_dec(x_56);
x_60 = lean_expr_has_expr_mvar(x_57);
if (x_60 == 0)
{
uint8_t x_61; 
x_61 = lean_expr_has_level_mvar(x_57);
if (x_61 == 0)
{
uint8_t x_62; 
lean_dec(x_57);
lean_dec(x_2);
lean_dec(x_1);
x_62 = 0;
return x_62;
}
else
{
x_3 = x_57;
goto _start;
}
}
else
{
x_3 = x_57;
goto _start;
}
}
else
{
uint8_t x_65; 
lean_inc(x_2);
lean_inc(x_1);
x_65 = l_Lean_AbstractTypeContext_hasAssignedMVar___main___rarg(x_1, x_2, x_56);
if (x_65 == 0)
{
uint8_t x_66; 
x_66 = lean_expr_has_expr_mvar(x_57);
if (x_66 == 0)
{
uint8_t x_67; 
x_67 = lean_expr_has_level_mvar(x_57);
if (x_67 == 0)
{
lean_dec(x_57);
lean_dec(x_2);
lean_dec(x_1);
return x_65;
}
else
{
x_3 = x_57;
goto _start;
}
}
else
{
x_3 = x_57;
goto _start;
}
}
else
{
uint8_t x_70; 
lean_dec(x_57);
lean_dec(x_2);
lean_dec(x_1);
x_70 = 1;
return x_70;
}
}
}
else
{
uint8_t x_71; 
lean_inc(x_2);
lean_inc(x_1);
x_71 = l_Lean_AbstractTypeContext_hasAssignedMVar___main___rarg(x_1, x_2, x_56);
if (x_71 == 0)
{
uint8_t x_72; 
x_72 = lean_expr_has_expr_mvar(x_57);
if (x_72 == 0)
{
uint8_t x_73; 
x_73 = lean_expr_has_level_mvar(x_57);
if (x_73 == 0)
{
lean_dec(x_57);
lean_dec(x_2);
lean_dec(x_1);
return x_71;
}
else
{
x_3 = x_57;
goto _start;
}
}
else
{
x_3 = x_57;
goto _start;
}
}
else
{
uint8_t x_76; 
lean_dec(x_57);
lean_dec(x_2);
lean_dec(x_1);
x_76 = 1;
return x_76;
}
}
}
case 8:
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; uint8_t x_101; 
x_77 = lean_ctor_get(x_3, 1);
lean_inc(x_77);
x_78 = lean_ctor_get(x_3, 2);
lean_inc(x_78);
x_79 = lean_ctor_get(x_3, 3);
lean_inc(x_79);
lean_dec(x_3);
x_101 = lean_expr_has_expr_mvar(x_77);
if (x_101 == 0)
{
uint8_t x_102; 
x_102 = lean_expr_has_level_mvar(x_77);
if (x_102 == 0)
{
uint8_t x_103; 
lean_dec(x_77);
x_103 = 0;
x_80 = x_103;
goto block_100;
}
else
{
uint8_t x_104; 
lean_inc(x_2);
lean_inc(x_1);
x_104 = l_Lean_AbstractTypeContext_hasAssignedMVar___main___rarg(x_1, x_2, x_77);
if (x_104 == 0)
{
x_80 = x_104;
goto block_100;
}
else
{
uint8_t x_105; 
lean_dec(x_79);
lean_dec(x_78);
lean_dec(x_2);
lean_dec(x_1);
x_105 = 1;
return x_105;
}
}
}
else
{
uint8_t x_106; 
lean_inc(x_2);
lean_inc(x_1);
x_106 = l_Lean_AbstractTypeContext_hasAssignedMVar___main___rarg(x_1, x_2, x_77);
if (x_106 == 0)
{
x_80 = x_106;
goto block_100;
}
else
{
uint8_t x_107; 
lean_dec(x_79);
lean_dec(x_78);
lean_dec(x_2);
lean_dec(x_1);
x_107 = 1;
return x_107;
}
}
block_100:
{
uint8_t x_81; 
x_81 = lean_expr_has_expr_mvar(x_78);
if (x_81 == 0)
{
uint8_t x_82; 
x_82 = lean_expr_has_level_mvar(x_78);
if (x_82 == 0)
{
lean_dec(x_78);
if (x_80 == 0)
{
uint8_t x_83; 
x_83 = lean_expr_has_expr_mvar(x_79);
if (x_83 == 0)
{
uint8_t x_84; 
x_84 = lean_expr_has_level_mvar(x_79);
if (x_84 == 0)
{
lean_dec(x_79);
lean_dec(x_2);
lean_dec(x_1);
return x_80;
}
else
{
x_3 = x_79;
goto _start;
}
}
else
{
x_3 = x_79;
goto _start;
}
}
else
{
uint8_t x_87; 
lean_dec(x_79);
lean_dec(x_2);
lean_dec(x_1);
x_87 = 1;
return x_87;
}
}
else
{
uint8_t x_88; 
lean_inc(x_2);
lean_inc(x_1);
x_88 = l_Lean_AbstractTypeContext_hasAssignedMVar___main___rarg(x_1, x_2, x_78);
if (x_88 == 0)
{
uint8_t x_89; 
x_89 = lean_expr_has_expr_mvar(x_79);
if (x_89 == 0)
{
uint8_t x_90; 
x_90 = lean_expr_has_level_mvar(x_79);
if (x_90 == 0)
{
lean_dec(x_79);
lean_dec(x_2);
lean_dec(x_1);
return x_88;
}
else
{
x_3 = x_79;
goto _start;
}
}
else
{
x_3 = x_79;
goto _start;
}
}
else
{
uint8_t x_93; 
lean_dec(x_79);
lean_dec(x_2);
lean_dec(x_1);
x_93 = 1;
return x_93;
}
}
}
else
{
uint8_t x_94; 
lean_inc(x_2);
lean_inc(x_1);
x_94 = l_Lean_AbstractTypeContext_hasAssignedMVar___main___rarg(x_1, x_2, x_78);
if (x_94 == 0)
{
uint8_t x_95; 
x_95 = lean_expr_has_expr_mvar(x_79);
if (x_95 == 0)
{
uint8_t x_96; 
x_96 = lean_expr_has_level_mvar(x_79);
if (x_96 == 0)
{
lean_dec(x_79);
lean_dec(x_2);
lean_dec(x_1);
return x_94;
}
else
{
x_3 = x_79;
goto _start;
}
}
else
{
x_3 = x_79;
goto _start;
}
}
else
{
uint8_t x_99; 
lean_dec(x_79);
lean_dec(x_2);
lean_dec(x_1);
x_99 = 1;
return x_99;
}
}
}
}
case 10:
{
lean_object* x_108; uint8_t x_109; 
x_108 = lean_ctor_get(x_3, 1);
lean_inc(x_108);
lean_dec(x_3);
x_109 = lean_expr_has_expr_mvar(x_108);
if (x_109 == 0)
{
uint8_t x_110; 
x_110 = lean_expr_has_level_mvar(x_108);
if (x_110 == 0)
{
uint8_t x_111; 
lean_dec(x_108);
lean_dec(x_2);
lean_dec(x_1);
x_111 = 0;
return x_111;
}
else
{
x_3 = x_108;
goto _start;
}
}
else
{
x_3 = x_108;
goto _start;
}
}
case 11:
{
lean_object* x_114; uint8_t x_115; 
x_114 = lean_ctor_get(x_3, 2);
lean_inc(x_114);
lean_dec(x_3);
x_115 = lean_expr_has_expr_mvar(x_114);
if (x_115 == 0)
{
uint8_t x_116; 
x_116 = lean_expr_has_level_mvar(x_114);
if (x_116 == 0)
{
uint8_t x_117; 
lean_dec(x_114);
lean_dec(x_2);
lean_dec(x_1);
x_117 = 0;
return x_117;
}
else
{
x_3 = x_114;
goto _start;
}
}
else
{
x_3 = x_114;
goto _start;
}
}
default: 
{
uint8_t x_120; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_120 = 0;
return x_120;
}
}
}
}
lean_object* l_Lean_AbstractTypeContext_hasAssignedMVar___main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_AbstractTypeContext_hasAssignedMVar___main___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_List_foldr___main___at_Lean_AbstractTypeContext_hasAssignedMVar___main___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_unbox(x_3);
lean_dec(x_3);
x_6 = l_List_foldr___main___at_Lean_AbstractTypeContext_hasAssignedMVar___main___spec__1___rarg(x_1, x_2, x_5, x_4);
x_7 = lean_box(x_6);
return x_7;
}
}
lean_object* l_Lean_AbstractTypeContext_hasAssignedMVar___main___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_AbstractTypeContext_hasAssignedMVar___main___rarg(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
uint8_t l_Lean_AbstractTypeContext_hasAssignedMVar___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_AbstractTypeContext_hasAssignedMVar___main___rarg(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_AbstractTypeContext_hasAssignedMVar(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_AbstractTypeContext_hasAssignedMVar___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_Lean_AbstractTypeContext_hasAssignedMVar___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_AbstractTypeContext_hasAssignedMVar___rarg(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
lean_object* l_Lean_AbstractTypeContext_instantiateLevelMVars___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 1:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = l_Lean_AbstractTypeContext_instantiateLevelMVars___main___rarg(x_1, x_4, x_3);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_level_update_succ(x_2, x_7);
lean_ctor_set(x_5, 0, x_8);
return x_5;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_5, 0);
x_10 = lean_ctor_get(x_5, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_5);
x_11 = lean_level_update_succ(x_2, x_9);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
}
case 2:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_13 = lean_ctor_get(x_2, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_2, 1);
lean_inc(x_14);
lean_inc(x_1);
x_15 = l_Lean_AbstractTypeContext_instantiateLevelMVars___main___rarg(x_1, x_13, x_3);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Lean_AbstractTypeContext_instantiateLevelMVars___main___rarg(x_1, x_14, x_17);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_level_update_max(x_2, x_16, x_20);
lean_ctor_set(x_18, 0, x_21);
return x_18;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_18, 0);
x_23 = lean_ctor_get(x_18, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_18);
x_24 = lean_level_update_max(x_2, x_16, x_22);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
return x_25;
}
}
case 3:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_26 = lean_ctor_get(x_2, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_2, 1);
lean_inc(x_27);
lean_dec(x_2);
lean_inc(x_1);
x_28 = l_Lean_AbstractTypeContext_instantiateLevelMVars___main___rarg(x_1, x_26, x_3);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec(x_28);
x_30 = l_Lean_AbstractTypeContext_instantiateLevelMVars___main___rarg(x_1, x_27, x_29);
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_32 = lean_ctor_get(x_30, 0);
lean_dec(x_32);
x_33 = l_Lean_Level_updateSucc_x21___closed__1;
x_34 = lean_unsigned_to_nat(218u);
x_35 = lean_unsigned_to_nat(17u);
x_36 = l_Lean_Level_updateIMax_x21___closed__1;
x_37 = l_panicWithPos___at_Lean_Level_updateSucc_x21___spec__1(x_33, x_34, x_35, x_36);
lean_ctor_set(x_30, 0, x_37);
return x_30;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_38 = lean_ctor_get(x_30, 1);
lean_inc(x_38);
lean_dec(x_30);
x_39 = l_Lean_Level_updateSucc_x21___closed__1;
x_40 = lean_unsigned_to_nat(218u);
x_41 = lean_unsigned_to_nat(17u);
x_42 = l_Lean_Level_updateIMax_x21___closed__1;
x_43 = l_panicWithPos___at_Lean_Level_updateSucc_x21___spec__1(x_39, x_40, x_41, x_42);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_38);
return x_44;
}
}
case 5:
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_2, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_1, 2);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_3);
x_47 = lean_apply_2(x_46, x_3, x_45);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; 
lean_dec(x_45);
lean_dec(x_1);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_2);
lean_ctor_set(x_48, 1, x_3);
return x_48;
}
else
{
lean_object* x_49; uint8_t x_50; 
lean_dec(x_2);
x_49 = lean_ctor_get(x_47, 0);
lean_inc(x_49);
lean_dec(x_47);
lean_inc(x_49);
x_50 = lean_level_has_mvar(x_49);
if (x_50 == 0)
{
lean_object* x_51; 
lean_dec(x_45);
lean_dec(x_1);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_3);
return x_51;
}
else
{
lean_object* x_52; uint8_t x_53; 
lean_inc(x_1);
x_52 = l_Lean_AbstractTypeContext_instantiateLevelMVars___main___rarg(x_1, x_49, x_3);
x_53 = !lean_is_exclusive(x_52);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_54 = lean_ctor_get(x_52, 0);
x_55 = lean_ctor_get(x_52, 1);
x_56 = lean_ctor_get(x_1, 3);
lean_inc(x_56);
lean_dec(x_1);
lean_inc(x_54);
x_57 = lean_apply_3(x_56, x_55, x_45, x_54);
lean_ctor_set(x_52, 1, x_57);
return x_52;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_58 = lean_ctor_get(x_52, 0);
x_59 = lean_ctor_get(x_52, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_52);
x_60 = lean_ctor_get(x_1, 3);
lean_inc(x_60);
lean_dec(x_1);
lean_inc(x_58);
x_61 = lean_apply_3(x_60, x_59, x_45, x_58);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_58);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
}
default: 
{
lean_object* x_63; 
lean_dec(x_1);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_2);
lean_ctor_set(x_63, 1, x_3);
return x_63;
}
}
}
}
lean_object* l_Lean_AbstractTypeContext_instantiateLevelMVars___main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_AbstractTypeContext_instantiateLevelMVars___main___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_AbstractTypeContext_instantiateLevelMVars___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_AbstractTypeContext_instantiateLevelMVars___main___rarg(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_AbstractTypeContext_instantiateLevelMVars(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_AbstractTypeContext_instantiateLevelMVars___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_AbstractTypeContext_InstantiateExprMVars_instantiateLevelMVars___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = l_Lean_AbstractTypeContext_instantiateLevelMVars___main___rarg(x_1, x_2, x_5);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_6, 1);
lean_ctor_set(x_3, 0, x_8);
lean_ctor_set(x_6, 1, x_3);
return x_6;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_6, 0);
x_10 = lean_ctor_get(x_6, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_6);
lean_ctor_set(x_3, 0, x_10);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_3);
return x_11;
}
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_12 = lean_ctor_get(x_3, 0);
x_13 = lean_ctor_get(x_3, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_3);
x_14 = l_Lean_AbstractTypeContext_instantiateLevelMVars___main___rarg(x_1, x_2, x_12);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_17 = x_14;
} else {
 lean_dec_ref(x_14);
 x_17 = lean_box(0);
}
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_13);
if (lean_is_scalar(x_17)) {
 x_19 = lean_alloc_ctor(0, 2, 0);
} else {
 x_19 = x_17;
}
lean_ctor_set(x_19, 0, x_15);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
lean_object* l_Lean_AbstractTypeContext_InstantiateExprMVars_instantiateLevelMVars(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_AbstractTypeContext_InstantiateExprMVars_instantiateLevelMVars___rarg), 3, 0);
return x_2;
}
}
lean_object* l_AssocList_find___main___at_Lean_AbstractTypeContext_InstantiateExprMVars_checkCache___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 2);
x_7 = lean_expr_eqv(x_4, x_1);
if (x_7 == 0)
{
x_2 = x_6;
goto _start;
}
else
{
lean_object* x_9; 
lean_inc(x_5);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_5);
return x_9;
}
}
}
}
lean_object* l_HashMapImp_find___at_Lean_AbstractTypeContext_InstantiateExprMVars_checkCache___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; size_t x_5; size_t x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
x_5 = lean_expr_hash(x_2);
x_6 = lean_usize_modn(x_5, x_4);
lean_dec(x_4);
x_7 = lean_array_uget(x_3, x_6);
x_8 = l_AssocList_find___main___at_Lean_AbstractTypeContext_InstantiateExprMVars_checkCache___spec__2(x_2, x_7);
lean_dec(x_7);
return x_8;
}
}
uint8_t l_AssocList_contains___main___at_Lean_AbstractTypeContext_InstantiateExprMVars_checkCache___spec__4(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_expr_eqv(x_4, x_1);
if (x_6 == 0)
{
x_2 = x_5;
goto _start;
}
else
{
uint8_t x_8; 
x_8 = 1;
return x_8;
}
}
}
}
lean_object* l_AssocList_mfoldl___main___at_Lean_AbstractTypeContext_InstantiateExprMVars_checkCache___spec__7(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_array_get_size(x_1);
x_7 = lean_expr_hash(x_4);
x_8 = lean_usize_modn(x_7, x_6);
lean_dec(x_6);
x_9 = lean_array_uget(x_1, x_8);
lean_ctor_set(x_2, 2, x_9);
x_10 = lean_array_uset(x_1, x_8, x_2);
x_1 = x_10;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_12 = lean_ctor_get(x_2, 0);
x_13 = lean_ctor_get(x_2, 1);
x_14 = lean_ctor_get(x_2, 2);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_2);
x_15 = lean_array_get_size(x_1);
x_16 = lean_expr_hash(x_12);
x_17 = lean_usize_modn(x_16, x_15);
lean_dec(x_15);
x_18 = lean_array_uget(x_1, x_17);
x_19 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_19, 0, x_12);
lean_ctor_set(x_19, 1, x_13);
lean_ctor_set(x_19, 2, x_18);
x_20 = lean_array_uset(x_1, x_17, x_19);
x_1 = x_20;
x_2 = x_14;
goto _start;
}
}
}
}
lean_object* l_HashMapImp_moveEntries___main___at_Lean_AbstractTypeContext_InstantiateExprMVars_checkCache___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_1, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_array_fget(x_2, x_1);
x_7 = lean_box(0);
x_8 = lean_array_fset(x_2, x_1, x_7);
x_9 = l_AssocList_mfoldl___main___at_Lean_AbstractTypeContext_InstantiateExprMVars_checkCache___spec__7(x_3, x_6);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_1, x_10);
lean_dec(x_1);
x_1 = x_11;
x_2 = x_8;
x_3 = x_9;
goto _start;
}
}
}
lean_object* l_HashMapImp_expand___at_Lean_AbstractTypeContext_InstantiateExprMVars_checkCache___spec__5(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_3 = lean_array_get_size(x_2);
x_4 = lean_unsigned_to_nat(2u);
x_5 = lean_nat_mul(x_3, x_4);
lean_dec(x_3);
x_6 = lean_box(0);
x_7 = lean_mk_array(x_5, x_6);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_HashMapImp_moveEntries___main___at_Lean_AbstractTypeContext_InstantiateExprMVars_checkCache___spec__6(x_8, x_2, x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
lean_object* l_AssocList_replace___main___at_Lean_AbstractTypeContext_InstantiateExprMVars_checkCache___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_ctor_get(x_3, 2);
x_8 = lean_expr_eqv(x_5, x_1);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = l_AssocList_replace___main___at_Lean_AbstractTypeContext_InstantiateExprMVars_checkCache___spec__8(x_1, x_2, x_7);
lean_ctor_set(x_3, 2, x_9);
return x_3;
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 0, x_1);
return x_3;
}
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_3, 0);
x_11 = lean_ctor_get(x_3, 1);
x_12 = lean_ctor_get(x_3, 2);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_3);
x_13 = lean_expr_eqv(x_10, x_1);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = l_AssocList_replace___main___at_Lean_AbstractTypeContext_InstantiateExprMVars_checkCache___spec__8(x_1, x_2, x_12);
x_15 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_15, 0, x_10);
lean_ctor_set(x_15, 1, x_11);
lean_ctor_set(x_15, 2, x_14);
return x_15;
}
else
{
lean_object* x_16; 
lean_dec(x_11);
lean_dec(x_10);
x_16 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_2);
lean_ctor_set(x_16, 2, x_12);
return x_16;
}
}
}
}
}
lean_object* l_HashMapImp_insert___at_Lean_AbstractTypeContext_InstantiateExprMVars_checkCache___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; lean_object* x_10; uint8_t x_11; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_array_get_size(x_6);
x_8 = lean_expr_hash(x_2);
x_9 = lean_usize_modn(x_8, x_7);
x_10 = lean_array_uget(x_6, x_9);
x_11 = l_AssocList_contains___main___at_Lean_AbstractTypeContext_InstantiateExprMVars_checkCache___spec__4(x_2, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_5, x_12);
lean_dec(x_5);
x_14 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_14, 0, x_2);
lean_ctor_set(x_14, 1, x_3);
lean_ctor_set(x_14, 2, x_10);
x_15 = lean_array_uset(x_6, x_9, x_14);
x_16 = lean_nat_dec_le(x_13, x_7);
lean_dec(x_7);
if (x_16 == 0)
{
lean_object* x_17; 
lean_free_object(x_1);
x_17 = l_HashMapImp_expand___at_Lean_AbstractTypeContext_InstantiateExprMVars_checkCache___spec__5(x_13, x_15);
return x_17;
}
else
{
lean_ctor_set(x_1, 1, x_15);
lean_ctor_set(x_1, 0, x_13);
return x_1;
}
}
else
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_7);
x_18 = l_AssocList_replace___main___at_Lean_AbstractTypeContext_InstantiateExprMVars_checkCache___spec__8(x_2, x_3, x_10);
x_19 = lean_array_uset(x_6, x_9, x_18);
lean_ctor_set(x_1, 1, x_19);
return x_1;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; size_t x_23; size_t x_24; lean_object* x_25; uint8_t x_26; 
x_20 = lean_ctor_get(x_1, 0);
x_21 = lean_ctor_get(x_1, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_1);
x_22 = lean_array_get_size(x_21);
x_23 = lean_expr_hash(x_2);
x_24 = lean_usize_modn(x_23, x_22);
x_25 = lean_array_uget(x_21, x_24);
x_26 = l_AssocList_contains___main___at_Lean_AbstractTypeContext_InstantiateExprMVars_checkCache___spec__4(x_2, x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_27 = lean_unsigned_to_nat(1u);
x_28 = lean_nat_add(x_20, x_27);
lean_dec(x_20);
x_29 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_29, 0, x_2);
lean_ctor_set(x_29, 1, x_3);
lean_ctor_set(x_29, 2, x_25);
x_30 = lean_array_uset(x_21, x_24, x_29);
x_31 = lean_nat_dec_le(x_28, x_22);
lean_dec(x_22);
if (x_31 == 0)
{
lean_object* x_32; 
x_32 = l_HashMapImp_expand___at_Lean_AbstractTypeContext_InstantiateExprMVars_checkCache___spec__5(x_28, x_30);
return x_32;
}
else
{
lean_object* x_33; 
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_28);
lean_ctor_set(x_33, 1, x_30);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_22);
x_34 = l_AssocList_replace___main___at_Lean_AbstractTypeContext_InstantiateExprMVars_checkCache___spec__8(x_2, x_3, x_25);
x_35 = lean_array_uset(x_21, x_24, x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_20);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
lean_object* l_Lean_AbstractTypeContext_InstantiateExprMVars_checkCache___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
x_5 = l_HashMapImp_find___at_Lean_AbstractTypeContext_InstantiateExprMVars_checkCache___spec__1(x_4, x_1);
lean_dec(x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; uint8_t x_7; 
lean_inc(x_1);
x_6 = lean_apply_2(x_2, x_1, x_3);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_6, 1);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_6, 0);
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
x_12 = l_HashMapImp_insert___at_Lean_AbstractTypeContext_InstantiateExprMVars_checkCache___spec__3(x_11, x_1, x_10);
lean_ctor_set(x_8, 1, x_12);
return x_6;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_6, 0);
x_14 = lean_ctor_get(x_8, 0);
x_15 = lean_ctor_get(x_8, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_8);
lean_inc(x_13);
x_16 = l_HashMapImp_insert___at_Lean_AbstractTypeContext_InstantiateExprMVars_checkCache___spec__3(x_15, x_1, x_13);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_16);
lean_ctor_set(x_6, 1, x_17);
return x_6;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_18 = lean_ctor_get(x_6, 1);
x_19 = lean_ctor_get(x_6, 0);
lean_inc(x_18);
lean_inc(x_19);
lean_dec(x_6);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 x_22 = x_18;
} else {
 lean_dec_ref(x_18);
 x_22 = lean_box(0);
}
lean_inc(x_19);
x_23 = l_HashMapImp_insert___at_Lean_AbstractTypeContext_InstantiateExprMVars_checkCache___spec__3(x_21, x_1, x_19);
if (lean_is_scalar(x_22)) {
 x_24 = lean_alloc_ctor(0, 2, 0);
} else {
 x_24 = x_22;
}
lean_ctor_set(x_24, 0, x_20);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_19);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_2);
lean_dec(x_1);
x_26 = lean_ctor_get(x_5, 0);
lean_inc(x_26);
lean_dec(x_5);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_3);
return x_27;
}
}
}
lean_object* l_Lean_AbstractTypeContext_InstantiateExprMVars_checkCache(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_AbstractTypeContext_InstantiateExprMVars_checkCache___rarg), 3, 0);
return x_2;
}
}
lean_object* l_AssocList_find___main___at_Lean_AbstractTypeContext_InstantiateExprMVars_checkCache___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_AssocList_find___main___at_Lean_AbstractTypeContext_InstantiateExprMVars_checkCache___spec__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_HashMapImp_find___at_Lean_AbstractTypeContext_InstantiateExprMVars_checkCache___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_HashMapImp_find___at_Lean_AbstractTypeContext_InstantiateExprMVars_checkCache___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_AssocList_contains___main___at_Lean_AbstractTypeContext_InstantiateExprMVars_checkCache___spec__4___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_AssocList_contains___main___at_Lean_AbstractTypeContext_InstantiateExprMVars_checkCache___spec__4(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Lean_AbstractTypeContext_InstantiateExprMVars_visit___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_expr_has_expr_mvar(x_2);
if (x_4 == 0)
{
uint8_t x_5; 
x_5 = lean_expr_has_level_mvar(x_2);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_1);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_3);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_3, 1);
lean_inc(x_7);
x_8 = l_HashMapImp_find___at_Lean_AbstractTypeContext_InstantiateExprMVars_checkCache___spec__1(x_7, x_2);
lean_dec(x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; uint8_t x_10; 
lean_inc(x_2);
x_9 = lean_apply_2(x_1, x_2, x_3);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_9, 1);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_9, 0);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
x_15 = l_HashMapImp_insert___at_Lean_AbstractTypeContext_InstantiateExprMVars_checkCache___spec__3(x_14, x_2, x_13);
lean_ctor_set(x_11, 1, x_15);
return x_9;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_9, 0);
x_17 = lean_ctor_get(x_11, 0);
x_18 = lean_ctor_get(x_11, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_11);
lean_inc(x_16);
x_19 = l_HashMapImp_insert___at_Lean_AbstractTypeContext_InstantiateExprMVars_checkCache___spec__3(x_18, x_2, x_16);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_17);
lean_ctor_set(x_20, 1, x_19);
lean_ctor_set(x_9, 1, x_20);
return x_9;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_21 = lean_ctor_get(x_9, 1);
x_22 = lean_ctor_get(x_9, 0);
lean_inc(x_21);
lean_inc(x_22);
lean_dec(x_9);
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 x_25 = x_21;
} else {
 lean_dec_ref(x_21);
 x_25 = lean_box(0);
}
lean_inc(x_22);
x_26 = l_HashMapImp_insert___at_Lean_AbstractTypeContext_InstantiateExprMVars_checkCache___spec__3(x_24, x_2, x_22);
if (lean_is_scalar(x_25)) {
 x_27 = lean_alloc_ctor(0, 2, 0);
} else {
 x_27 = x_25;
}
lean_ctor_set(x_27, 0, x_23);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_22);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; 
lean_dec(x_2);
lean_dec(x_1);
x_29 = lean_ctor_get(x_8, 0);
lean_inc(x_29);
lean_dec(x_8);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_3);
return x_30;
}
}
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_3, 1);
lean_inc(x_31);
x_32 = l_HashMapImp_find___at_Lean_AbstractTypeContext_InstantiateExprMVars_checkCache___spec__1(x_31, x_2);
lean_dec(x_31);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; uint8_t x_34; 
lean_inc(x_2);
x_33 = lean_apply_2(x_1, x_2, x_3);
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; uint8_t x_36; 
x_35 = lean_ctor_get(x_33, 1);
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_33, 0);
x_38 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
x_39 = l_HashMapImp_insert___at_Lean_AbstractTypeContext_InstantiateExprMVars_checkCache___spec__3(x_38, x_2, x_37);
lean_ctor_set(x_35, 1, x_39);
return x_33;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_40 = lean_ctor_get(x_33, 0);
x_41 = lean_ctor_get(x_35, 0);
x_42 = lean_ctor_get(x_35, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_35);
lean_inc(x_40);
x_43 = l_HashMapImp_insert___at_Lean_AbstractTypeContext_InstantiateExprMVars_checkCache___spec__3(x_42, x_2, x_40);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_41);
lean_ctor_set(x_44, 1, x_43);
lean_ctor_set(x_33, 1, x_44);
return x_33;
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_45 = lean_ctor_get(x_33, 1);
x_46 = lean_ctor_get(x_33, 0);
lean_inc(x_45);
lean_inc(x_46);
lean_dec(x_33);
x_47 = lean_ctor_get(x_45, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_45, 1);
lean_inc(x_48);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_49 = x_45;
} else {
 lean_dec_ref(x_45);
 x_49 = lean_box(0);
}
lean_inc(x_46);
x_50 = l_HashMapImp_insert___at_Lean_AbstractTypeContext_InstantiateExprMVars_checkCache___spec__3(x_48, x_2, x_46);
if (lean_is_scalar(x_49)) {
 x_51 = lean_alloc_ctor(0, 2, 0);
} else {
 x_51 = x_49;
}
lean_ctor_set(x_51, 0, x_47);
lean_ctor_set(x_51, 1, x_50);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_46);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
else
{
lean_object* x_53; lean_object* x_54; 
lean_dec(x_2);
lean_dec(x_1);
x_53 = lean_ctor_get(x_32, 0);
lean_inc(x_53);
lean_dec(x_32);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_3);
return x_54;
}
}
}
}
lean_object* l_Lean_AbstractTypeContext_InstantiateExprMVars_visit(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_AbstractTypeContext_InstantiateExprMVars_visit___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_AbstractTypeContext_InstantiateExprMVars_getMCtx___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_AbstractTypeContext_InstantiateExprMVars_getMCtx(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_AbstractTypeContext_InstantiateExprMVars_getMCtx___rarg), 1, 0);
return x_2;
}
}
lean_object* l_List_mmap___main___at_Lean_AbstractTypeContext_InstantiateExprMVars_main___main___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_1);
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_2);
if (x_6 == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_3);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get(x_2, 1);
x_10 = lean_ctor_get(x_3, 0);
lean_inc(x_1);
x_11 = l_Lean_AbstractTypeContext_instantiateLevelMVars___main___rarg(x_1, x_8, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
lean_ctor_set(x_3, 0, x_13);
x_14 = l_List_mmap___main___at_Lean_AbstractTypeContext_InstantiateExprMVars_main___main___spec__1___rarg(x_1, x_9, x_3);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_14, 0);
lean_ctor_set(x_2, 1, x_16);
lean_ctor_set(x_2, 0, x_12);
lean_ctor_set(x_14, 0, x_2);
return x_14;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_14, 0);
x_18 = lean_ctor_get(x_14, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_14);
lean_ctor_set(x_2, 1, x_17);
lean_ctor_set(x_2, 0, x_12);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_2);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_20 = lean_ctor_get(x_2, 0);
x_21 = lean_ctor_get(x_2, 1);
x_22 = lean_ctor_get(x_3, 0);
x_23 = lean_ctor_get(x_3, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_3);
lean_inc(x_1);
x_24 = l_Lean_AbstractTypeContext_instantiateLevelMVars___main___rarg(x_1, x_20, x_22);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_23);
x_28 = l_List_mmap___main___at_Lean_AbstractTypeContext_InstantiateExprMVars_main___main___spec__1___rarg(x_1, x_21, x_27);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 x_31 = x_28;
} else {
 lean_dec_ref(x_28);
 x_31 = lean_box(0);
}
lean_ctor_set(x_2, 1, x_29);
lean_ctor_set(x_2, 0, x_25);
if (lean_is_scalar(x_31)) {
 x_32 = lean_alloc_ctor(0, 2, 0);
} else {
 x_32 = x_31;
}
lean_ctor_set(x_32, 0, x_2);
lean_ctor_set(x_32, 1, x_30);
return x_32;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_33 = lean_ctor_get(x_2, 0);
x_34 = lean_ctor_get(x_2, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_2);
x_35 = lean_ctor_get(x_3, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_3, 1);
lean_inc(x_36);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 x_37 = x_3;
} else {
 lean_dec_ref(x_3);
 x_37 = lean_box(0);
}
lean_inc(x_1);
x_38 = l_Lean_AbstractTypeContext_instantiateLevelMVars___main___rarg(x_1, x_33, x_35);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
if (lean_is_scalar(x_37)) {
 x_41 = lean_alloc_ctor(0, 2, 0);
} else {
 x_41 = x_37;
}
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_36);
x_42 = l_List_mmap___main___at_Lean_AbstractTypeContext_InstantiateExprMVars_main___main___spec__1___rarg(x_1, x_34, x_41);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 x_45 = x_42;
} else {
 lean_dec_ref(x_42);
 x_45 = lean_box(0);
}
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_39);
lean_ctor_set(x_46, 1, x_43);
if (lean_is_scalar(x_45)) {
 x_47 = lean_alloc_ctor(0, 2, 0);
} else {
 x_47 = x_45;
}
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_44);
return x_47;
}
}
}
}
lean_object* l_List_mmap___main___at_Lean_AbstractTypeContext_InstantiateExprMVars_main___main___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_mmap___main___at_Lean_AbstractTypeContext_InstantiateExprMVars_main___main___spec__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_AbstractTypeContext_InstantiateExprMVars_main___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_16; lean_object* x_17; lean_object* x_27; lean_object* x_28; 
switch (lean_obj_tag(x_2)) {
case 2:
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_50; lean_object* x_51; 
x_38 = lean_ctor_get(x_2, 0);
lean_inc(x_38);
x_50 = lean_ctor_get(x_3, 1);
lean_inc(x_50);
x_51 = l_HashMapImp_find___at_Lean_AbstractTypeContext_InstantiateExprMVars_checkCache___spec__1(x_50, x_2);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_3, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_1, 5);
lean_inc(x_53);
lean_inc(x_38);
lean_inc(x_52);
x_54 = lean_apply_2(x_53, x_52, x_38);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_1, 10);
lean_inc(x_55);
lean_inc(x_38);
x_56 = lean_apply_2(x_55, x_52, x_38);
if (lean_obj_tag(x_56) == 0)
{
lean_dec(x_50);
lean_dec(x_38);
lean_dec(x_1);
lean_inc(x_2);
x_4 = x_2;
x_5 = x_3;
goto block_15;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_82; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
lean_dec(x_56);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
x_60 = lean_ctor_get(x_57, 2);
lean_inc(x_60);
lean_dec(x_57);
x_82 = lean_expr_has_expr_mvar(x_60);
if (x_82 == 0)
{
uint8_t x_83; 
x_83 = lean_expr_has_level_mvar(x_60);
if (x_83 == 0)
{
lean_dec(x_50);
x_61 = x_60;
x_62 = x_3;
goto block_81;
}
else
{
lean_object* x_84; 
x_84 = l_HashMapImp_find___at_Lean_AbstractTypeContext_InstantiateExprMVars_checkCache___spec__1(x_50, x_60);
lean_dec(x_50);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; 
lean_inc(x_60);
lean_inc(x_1);
x_85 = l_Lean_AbstractTypeContext_InstantiateExprMVars_main___main___rarg(x_1, x_60, x_3);
x_86 = lean_ctor_get(x_85, 1);
lean_inc(x_86);
x_87 = lean_ctor_get(x_85, 0);
lean_inc(x_87);
lean_dec(x_85);
x_88 = !lean_is_exclusive(x_86);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; 
x_89 = lean_ctor_get(x_86, 1);
lean_inc(x_87);
x_90 = l_HashMapImp_insert___at_Lean_AbstractTypeContext_InstantiateExprMVars_checkCache___spec__3(x_89, x_60, x_87);
lean_ctor_set(x_86, 1, x_90);
x_61 = x_87;
x_62 = x_86;
goto block_81;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_91 = lean_ctor_get(x_86, 0);
x_92 = lean_ctor_get(x_86, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_86);
lean_inc(x_87);
x_93 = l_HashMapImp_insert___at_Lean_AbstractTypeContext_InstantiateExprMVars_checkCache___spec__3(x_92, x_60, x_87);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_91);
lean_ctor_set(x_94, 1, x_93);
x_61 = x_87;
x_62 = x_94;
goto block_81;
}
}
else
{
lean_object* x_95; 
lean_dec(x_60);
x_95 = lean_ctor_get(x_84, 0);
lean_inc(x_95);
lean_dec(x_84);
x_61 = x_95;
x_62 = x_3;
goto block_81;
}
}
}
else
{
lean_object* x_96; 
x_96 = l_HashMapImp_find___at_Lean_AbstractTypeContext_InstantiateExprMVars_checkCache___spec__1(x_50, x_60);
lean_dec(x_50);
if (lean_obj_tag(x_96) == 0)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; uint8_t x_100; 
lean_inc(x_60);
lean_inc(x_1);
x_97 = l_Lean_AbstractTypeContext_InstantiateExprMVars_main___main___rarg(x_1, x_60, x_3);
x_98 = lean_ctor_get(x_97, 1);
lean_inc(x_98);
x_99 = lean_ctor_get(x_97, 0);
lean_inc(x_99);
lean_dec(x_97);
x_100 = !lean_is_exclusive(x_98);
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; 
x_101 = lean_ctor_get(x_98, 1);
lean_inc(x_99);
x_102 = l_HashMapImp_insert___at_Lean_AbstractTypeContext_InstantiateExprMVars_checkCache___spec__3(x_101, x_60, x_99);
lean_ctor_set(x_98, 1, x_102);
x_61 = x_99;
x_62 = x_98;
goto block_81;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_103 = lean_ctor_get(x_98, 0);
x_104 = lean_ctor_get(x_98, 1);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_98);
lean_inc(x_99);
x_105 = l_HashMapImp_insert___at_Lean_AbstractTypeContext_InstantiateExprMVars_checkCache___spec__3(x_104, x_60, x_99);
x_106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_106, 0, x_103);
lean_ctor_set(x_106, 1, x_105);
x_61 = x_99;
x_62 = x_106;
goto block_81;
}
}
else
{
lean_object* x_107; 
lean_dec(x_60);
x_107 = lean_ctor_get(x_96, 0);
lean_inc(x_107);
lean_dec(x_96);
x_61 = x_107;
x_62 = x_3;
goto block_81;
}
}
block_81:
{
uint8_t x_63; 
x_63 = lean_expr_has_expr_mvar(x_61);
if (x_63 == 0)
{
uint8_t x_64; 
x_64 = lean_expr_has_level_mvar(x_61);
if (x_64 == 0)
{
lean_dec(x_61);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_38);
lean_dec(x_1);
lean_inc(x_2);
x_4 = x_2;
x_5 = x_62;
goto block_15;
}
else
{
lean_object* x_65; uint8_t x_66; 
x_65 = lean_ctor_get(x_1, 9);
lean_inc(x_65);
lean_dec(x_1);
x_66 = !lean_is_exclusive(x_62);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_62, 0);
x_68 = lean_apply_5(x_65, x_67, x_38, x_58, x_59, x_61);
lean_ctor_set(x_62, 0, x_68);
lean_inc(x_2);
x_4 = x_2;
x_5 = x_62;
goto block_15;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_69 = lean_ctor_get(x_62, 0);
x_70 = lean_ctor_get(x_62, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_62);
x_71 = lean_apply_5(x_65, x_69, x_38, x_58, x_59, x_61);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_70);
lean_inc(x_2);
x_4 = x_2;
x_5 = x_72;
goto block_15;
}
}
}
else
{
lean_object* x_73; uint8_t x_74; 
x_73 = lean_ctor_get(x_1, 9);
lean_inc(x_73);
lean_dec(x_1);
x_74 = !lean_is_exclusive(x_62);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; 
x_75 = lean_ctor_get(x_62, 0);
x_76 = lean_apply_5(x_73, x_75, x_38, x_58, x_59, x_61);
lean_ctor_set(x_62, 0, x_76);
lean_inc(x_2);
x_4 = x_2;
x_5 = x_62;
goto block_15;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_77 = lean_ctor_get(x_62, 0);
x_78 = lean_ctor_get(x_62, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_62);
x_79 = lean_apply_5(x_73, x_77, x_38, x_58, x_59, x_61);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_78);
lean_inc(x_2);
x_4 = x_2;
x_5 = x_80;
goto block_15;
}
}
}
}
}
else
{
lean_object* x_108; uint8_t x_109; 
lean_dec(x_52);
x_108 = lean_ctor_get(x_54, 0);
lean_inc(x_108);
lean_dec(x_54);
x_109 = lean_expr_has_expr_mvar(x_108);
if (x_109 == 0)
{
uint8_t x_110; 
x_110 = lean_expr_has_level_mvar(x_108);
if (x_110 == 0)
{
lean_dec(x_50);
x_39 = x_108;
x_40 = x_3;
goto block_49;
}
else
{
lean_object* x_111; 
x_111 = l_HashMapImp_find___at_Lean_AbstractTypeContext_InstantiateExprMVars_checkCache___spec__1(x_50, x_108);
lean_dec(x_50);
if (lean_obj_tag(x_111) == 0)
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; uint8_t x_115; 
lean_inc(x_108);
lean_inc(x_1);
x_112 = l_Lean_AbstractTypeContext_InstantiateExprMVars_main___main___rarg(x_1, x_108, x_3);
x_113 = lean_ctor_get(x_112, 1);
lean_inc(x_113);
x_114 = lean_ctor_get(x_112, 0);
lean_inc(x_114);
lean_dec(x_112);
x_115 = !lean_is_exclusive(x_113);
if (x_115 == 0)
{
lean_object* x_116; lean_object* x_117; 
x_116 = lean_ctor_get(x_113, 1);
lean_inc(x_114);
x_117 = l_HashMapImp_insert___at_Lean_AbstractTypeContext_InstantiateExprMVars_checkCache___spec__3(x_116, x_108, x_114);
lean_ctor_set(x_113, 1, x_117);
x_39 = x_114;
x_40 = x_113;
goto block_49;
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_118 = lean_ctor_get(x_113, 0);
x_119 = lean_ctor_get(x_113, 1);
lean_inc(x_119);
lean_inc(x_118);
lean_dec(x_113);
lean_inc(x_114);
x_120 = l_HashMapImp_insert___at_Lean_AbstractTypeContext_InstantiateExprMVars_checkCache___spec__3(x_119, x_108, x_114);
x_121 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_121, 0, x_118);
lean_ctor_set(x_121, 1, x_120);
x_39 = x_114;
x_40 = x_121;
goto block_49;
}
}
else
{
lean_object* x_122; 
lean_dec(x_108);
x_122 = lean_ctor_get(x_111, 0);
lean_inc(x_122);
lean_dec(x_111);
x_39 = x_122;
x_40 = x_3;
goto block_49;
}
}
}
else
{
lean_object* x_123; 
x_123 = l_HashMapImp_find___at_Lean_AbstractTypeContext_InstantiateExprMVars_checkCache___spec__1(x_50, x_108);
lean_dec(x_50);
if (lean_obj_tag(x_123) == 0)
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; uint8_t x_127; 
lean_inc(x_108);
lean_inc(x_1);
x_124 = l_Lean_AbstractTypeContext_InstantiateExprMVars_main___main___rarg(x_1, x_108, x_3);
x_125 = lean_ctor_get(x_124, 1);
lean_inc(x_125);
x_126 = lean_ctor_get(x_124, 0);
lean_inc(x_126);
lean_dec(x_124);
x_127 = !lean_is_exclusive(x_125);
if (x_127 == 0)
{
lean_object* x_128; lean_object* x_129; 
x_128 = lean_ctor_get(x_125, 1);
lean_inc(x_126);
x_129 = l_HashMapImp_insert___at_Lean_AbstractTypeContext_InstantiateExprMVars_checkCache___spec__3(x_128, x_108, x_126);
lean_ctor_set(x_125, 1, x_129);
x_39 = x_126;
x_40 = x_125;
goto block_49;
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_130 = lean_ctor_get(x_125, 0);
x_131 = lean_ctor_get(x_125, 1);
lean_inc(x_131);
lean_inc(x_130);
lean_dec(x_125);
lean_inc(x_126);
x_132 = l_HashMapImp_insert___at_Lean_AbstractTypeContext_InstantiateExprMVars_checkCache___spec__3(x_131, x_108, x_126);
x_133 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_133, 0, x_130);
lean_ctor_set(x_133, 1, x_132);
x_39 = x_126;
x_40 = x_133;
goto block_49;
}
}
else
{
lean_object* x_134; 
lean_dec(x_108);
x_134 = lean_ctor_get(x_123, 0);
lean_inc(x_134);
lean_dec(x_123);
x_39 = x_134;
x_40 = x_3;
goto block_49;
}
}
}
}
else
{
lean_object* x_135; lean_object* x_136; 
lean_dec(x_50);
lean_dec(x_38);
lean_dec(x_2);
lean_dec(x_1);
x_135 = lean_ctor_get(x_51, 0);
lean_inc(x_135);
lean_dec(x_51);
x_136 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_136, 0, x_135);
lean_ctor_set(x_136, 1, x_3);
return x_136;
}
block_49:
{
lean_object* x_41; uint8_t x_42; 
x_41 = lean_ctor_get(x_1, 6);
lean_inc(x_41);
lean_dec(x_1);
x_42 = !lean_is_exclusive(x_40);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_40, 0);
lean_inc(x_39);
x_44 = lean_apply_3(x_41, x_43, x_38, x_39);
lean_ctor_set(x_40, 0, x_44);
x_4 = x_39;
x_5 = x_40;
goto block_15;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_45 = lean_ctor_get(x_40, 0);
x_46 = lean_ctor_get(x_40, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_40);
lean_inc(x_39);
x_47 = lean_apply_3(x_41, x_45, x_38, x_39);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_46);
x_4 = x_39;
x_5 = x_48;
goto block_15;
}
}
}
case 3:
{
lean_object* x_137; uint8_t x_138; 
x_137 = lean_ctor_get(x_2, 0);
lean_inc(x_137);
x_138 = !lean_is_exclusive(x_3);
if (x_138 == 0)
{
lean_object* x_139; lean_object* x_140; uint8_t x_141; 
x_139 = lean_ctor_get(x_3, 0);
x_140 = l_Lean_AbstractTypeContext_instantiateLevelMVars___main___rarg(x_1, x_137, x_139);
x_141 = !lean_is_exclusive(x_140);
if (x_141 == 0)
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_142 = lean_ctor_get(x_140, 0);
x_143 = lean_ctor_get(x_140, 1);
lean_ctor_set(x_3, 0, x_143);
x_144 = lean_expr_update_sort(x_2, x_142);
lean_ctor_set(x_140, 1, x_3);
lean_ctor_set(x_140, 0, x_144);
return x_140;
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_145 = lean_ctor_get(x_140, 0);
x_146 = lean_ctor_get(x_140, 1);
lean_inc(x_146);
lean_inc(x_145);
lean_dec(x_140);
lean_ctor_set(x_3, 0, x_146);
x_147 = lean_expr_update_sort(x_2, x_145);
x_148 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_148, 0, x_147);
lean_ctor_set(x_148, 1, x_3);
return x_148;
}
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_149 = lean_ctor_get(x_3, 0);
x_150 = lean_ctor_get(x_3, 1);
lean_inc(x_150);
lean_inc(x_149);
lean_dec(x_3);
x_151 = l_Lean_AbstractTypeContext_instantiateLevelMVars___main___rarg(x_1, x_137, x_149);
x_152 = lean_ctor_get(x_151, 0);
lean_inc(x_152);
x_153 = lean_ctor_get(x_151, 1);
lean_inc(x_153);
if (lean_is_exclusive(x_151)) {
 lean_ctor_release(x_151, 0);
 lean_ctor_release(x_151, 1);
 x_154 = x_151;
} else {
 lean_dec_ref(x_151);
 x_154 = lean_box(0);
}
x_155 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_155, 0, x_153);
lean_ctor_set(x_155, 1, x_150);
x_156 = lean_expr_update_sort(x_2, x_152);
if (lean_is_scalar(x_154)) {
 x_157 = lean_alloc_ctor(0, 2, 0);
} else {
 x_157 = x_154;
}
lean_ctor_set(x_157, 0, x_156);
lean_ctor_set(x_157, 1, x_155);
return x_157;
}
}
case 4:
{
lean_object* x_158; lean_object* x_159; uint8_t x_160; 
x_158 = lean_ctor_get(x_2, 1);
lean_inc(x_158);
x_159 = l_List_mmap___main___at_Lean_AbstractTypeContext_InstantiateExprMVars_main___main___spec__1___rarg(x_1, x_158, x_3);
x_160 = !lean_is_exclusive(x_159);
if (x_160 == 0)
{
lean_object* x_161; lean_object* x_162; 
x_161 = lean_ctor_get(x_159, 0);
x_162 = lean_expr_update_const(x_2, x_161);
lean_ctor_set(x_159, 0, x_162);
return x_159;
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_163 = lean_ctor_get(x_159, 0);
x_164 = lean_ctor_get(x_159, 1);
lean_inc(x_164);
lean_inc(x_163);
lean_dec(x_159);
x_165 = lean_expr_update_const(x_2, x_163);
x_166 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_166, 0, x_165);
lean_ctor_set(x_166, 1, x_164);
return x_166;
}
}
case 5:
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; uint8_t x_232; 
x_167 = lean_ctor_get(x_2, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_2, 1);
lean_inc(x_168);
x_232 = lean_expr_has_expr_mvar(x_167);
if (x_232 == 0)
{
uint8_t x_233; 
x_233 = lean_expr_has_level_mvar(x_167);
if (x_233 == 0)
{
x_169 = x_167;
x_170 = x_3;
goto block_231;
}
else
{
lean_object* x_234; lean_object* x_235; 
x_234 = lean_ctor_get(x_3, 1);
lean_inc(x_234);
x_235 = l_HashMapImp_find___at_Lean_AbstractTypeContext_InstantiateExprMVars_checkCache___spec__1(x_234, x_167);
lean_dec(x_234);
if (lean_obj_tag(x_235) == 0)
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; uint8_t x_239; 
lean_inc(x_167);
lean_inc(x_1);
x_236 = l_Lean_AbstractTypeContext_InstantiateExprMVars_main___main___rarg(x_1, x_167, x_3);
x_237 = lean_ctor_get(x_236, 1);
lean_inc(x_237);
x_238 = lean_ctor_get(x_236, 0);
lean_inc(x_238);
lean_dec(x_236);
x_239 = !lean_is_exclusive(x_237);
if (x_239 == 0)
{
lean_object* x_240; lean_object* x_241; 
x_240 = lean_ctor_get(x_237, 1);
lean_inc(x_238);
x_241 = l_HashMapImp_insert___at_Lean_AbstractTypeContext_InstantiateExprMVars_checkCache___spec__3(x_240, x_167, x_238);
lean_ctor_set(x_237, 1, x_241);
x_169 = x_238;
x_170 = x_237;
goto block_231;
}
else
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; 
x_242 = lean_ctor_get(x_237, 0);
x_243 = lean_ctor_get(x_237, 1);
lean_inc(x_243);
lean_inc(x_242);
lean_dec(x_237);
lean_inc(x_238);
x_244 = l_HashMapImp_insert___at_Lean_AbstractTypeContext_InstantiateExprMVars_checkCache___spec__3(x_243, x_167, x_238);
x_245 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_245, 0, x_242);
lean_ctor_set(x_245, 1, x_244);
x_169 = x_238;
x_170 = x_245;
goto block_231;
}
}
else
{
lean_object* x_246; 
lean_dec(x_167);
x_246 = lean_ctor_get(x_235, 0);
lean_inc(x_246);
lean_dec(x_235);
x_169 = x_246;
x_170 = x_3;
goto block_231;
}
}
}
else
{
lean_object* x_247; lean_object* x_248; 
x_247 = lean_ctor_get(x_3, 1);
lean_inc(x_247);
x_248 = l_HashMapImp_find___at_Lean_AbstractTypeContext_InstantiateExprMVars_checkCache___spec__1(x_247, x_167);
lean_dec(x_247);
if (lean_obj_tag(x_248) == 0)
{
lean_object* x_249; lean_object* x_250; lean_object* x_251; uint8_t x_252; 
lean_inc(x_167);
lean_inc(x_1);
x_249 = l_Lean_AbstractTypeContext_InstantiateExprMVars_main___main___rarg(x_1, x_167, x_3);
x_250 = lean_ctor_get(x_249, 1);
lean_inc(x_250);
x_251 = lean_ctor_get(x_249, 0);
lean_inc(x_251);
lean_dec(x_249);
x_252 = !lean_is_exclusive(x_250);
if (x_252 == 0)
{
lean_object* x_253; lean_object* x_254; 
x_253 = lean_ctor_get(x_250, 1);
lean_inc(x_251);
x_254 = l_HashMapImp_insert___at_Lean_AbstractTypeContext_InstantiateExprMVars_checkCache___spec__3(x_253, x_167, x_251);
lean_ctor_set(x_250, 1, x_254);
x_169 = x_251;
x_170 = x_250;
goto block_231;
}
else
{
lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; 
x_255 = lean_ctor_get(x_250, 0);
x_256 = lean_ctor_get(x_250, 1);
lean_inc(x_256);
lean_inc(x_255);
lean_dec(x_250);
lean_inc(x_251);
x_257 = l_HashMapImp_insert___at_Lean_AbstractTypeContext_InstantiateExprMVars_checkCache___spec__3(x_256, x_167, x_251);
x_258 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_258, 0, x_255);
lean_ctor_set(x_258, 1, x_257);
x_169 = x_251;
x_170 = x_258;
goto block_231;
}
}
else
{
lean_object* x_259; 
lean_dec(x_167);
x_259 = lean_ctor_get(x_248, 0);
lean_inc(x_259);
lean_dec(x_248);
x_169 = x_259;
x_170 = x_3;
goto block_231;
}
}
block_231:
{
uint8_t x_171; 
x_171 = lean_expr_has_expr_mvar(x_168);
if (x_171 == 0)
{
uint8_t x_172; 
x_172 = lean_expr_has_level_mvar(x_168);
if (x_172 == 0)
{
lean_object* x_173; lean_object* x_174; 
lean_dec(x_1);
x_173 = lean_expr_update_app(x_2, x_169, x_168);
x_174 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_174, 0, x_173);
lean_ctor_set(x_174, 1, x_170);
return x_174;
}
else
{
lean_object* x_175; lean_object* x_176; 
x_175 = lean_ctor_get(x_170, 1);
lean_inc(x_175);
x_176 = l_HashMapImp_find___at_Lean_AbstractTypeContext_InstantiateExprMVars_checkCache___spec__1(x_175, x_168);
lean_dec(x_175);
if (lean_obj_tag(x_176) == 0)
{
lean_object* x_177; uint8_t x_178; 
lean_inc(x_168);
x_177 = l_Lean_AbstractTypeContext_InstantiateExprMVars_main___main___rarg(x_1, x_168, x_170);
x_178 = !lean_is_exclusive(x_177);
if (x_178 == 0)
{
lean_object* x_179; uint8_t x_180; 
x_179 = lean_ctor_get(x_177, 1);
x_180 = !lean_is_exclusive(x_179);
if (x_180 == 0)
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_181 = lean_ctor_get(x_177, 0);
x_182 = lean_ctor_get(x_179, 1);
lean_inc(x_181);
x_183 = l_HashMapImp_insert___at_Lean_AbstractTypeContext_InstantiateExprMVars_checkCache___spec__3(x_182, x_168, x_181);
lean_ctor_set(x_179, 1, x_183);
x_184 = lean_expr_update_app(x_2, x_169, x_181);
lean_ctor_set(x_177, 0, x_184);
return x_177;
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; 
x_185 = lean_ctor_get(x_177, 0);
x_186 = lean_ctor_get(x_179, 0);
x_187 = lean_ctor_get(x_179, 1);
lean_inc(x_187);
lean_inc(x_186);
lean_dec(x_179);
lean_inc(x_185);
x_188 = l_HashMapImp_insert___at_Lean_AbstractTypeContext_InstantiateExprMVars_checkCache___spec__3(x_187, x_168, x_185);
x_189 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_189, 0, x_186);
lean_ctor_set(x_189, 1, x_188);
x_190 = lean_expr_update_app(x_2, x_169, x_185);
lean_ctor_set(x_177, 1, x_189);
lean_ctor_set(x_177, 0, x_190);
return x_177;
}
}
else
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; 
x_191 = lean_ctor_get(x_177, 1);
x_192 = lean_ctor_get(x_177, 0);
lean_inc(x_191);
lean_inc(x_192);
lean_dec(x_177);
x_193 = lean_ctor_get(x_191, 0);
lean_inc(x_193);
x_194 = lean_ctor_get(x_191, 1);
lean_inc(x_194);
if (lean_is_exclusive(x_191)) {
 lean_ctor_release(x_191, 0);
 lean_ctor_release(x_191, 1);
 x_195 = x_191;
} else {
 lean_dec_ref(x_191);
 x_195 = lean_box(0);
}
lean_inc(x_192);
x_196 = l_HashMapImp_insert___at_Lean_AbstractTypeContext_InstantiateExprMVars_checkCache___spec__3(x_194, x_168, x_192);
if (lean_is_scalar(x_195)) {
 x_197 = lean_alloc_ctor(0, 2, 0);
} else {
 x_197 = x_195;
}
lean_ctor_set(x_197, 0, x_193);
lean_ctor_set(x_197, 1, x_196);
x_198 = lean_expr_update_app(x_2, x_169, x_192);
x_199 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_199, 0, x_198);
lean_ctor_set(x_199, 1, x_197);
return x_199;
}
}
else
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; 
lean_dec(x_168);
lean_dec(x_1);
x_200 = lean_ctor_get(x_176, 0);
lean_inc(x_200);
lean_dec(x_176);
x_201 = lean_expr_update_app(x_2, x_169, x_200);
x_202 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_202, 0, x_201);
lean_ctor_set(x_202, 1, x_170);
return x_202;
}
}
}
else
{
lean_object* x_203; lean_object* x_204; 
x_203 = lean_ctor_get(x_170, 1);
lean_inc(x_203);
x_204 = l_HashMapImp_find___at_Lean_AbstractTypeContext_InstantiateExprMVars_checkCache___spec__1(x_203, x_168);
lean_dec(x_203);
if (lean_obj_tag(x_204) == 0)
{
lean_object* x_205; uint8_t x_206; 
lean_inc(x_168);
x_205 = l_Lean_AbstractTypeContext_InstantiateExprMVars_main___main___rarg(x_1, x_168, x_170);
x_206 = !lean_is_exclusive(x_205);
if (x_206 == 0)
{
lean_object* x_207; uint8_t x_208; 
x_207 = lean_ctor_get(x_205, 1);
x_208 = !lean_is_exclusive(x_207);
if (x_208 == 0)
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; 
x_209 = lean_ctor_get(x_205, 0);
x_210 = lean_ctor_get(x_207, 1);
lean_inc(x_209);
x_211 = l_HashMapImp_insert___at_Lean_AbstractTypeContext_InstantiateExprMVars_checkCache___spec__3(x_210, x_168, x_209);
lean_ctor_set(x_207, 1, x_211);
x_212 = lean_expr_update_app(x_2, x_169, x_209);
lean_ctor_set(x_205, 0, x_212);
return x_205;
}
else
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; 
x_213 = lean_ctor_get(x_205, 0);
x_214 = lean_ctor_get(x_207, 0);
x_215 = lean_ctor_get(x_207, 1);
lean_inc(x_215);
lean_inc(x_214);
lean_dec(x_207);
lean_inc(x_213);
x_216 = l_HashMapImp_insert___at_Lean_AbstractTypeContext_InstantiateExprMVars_checkCache___spec__3(x_215, x_168, x_213);
x_217 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_217, 0, x_214);
lean_ctor_set(x_217, 1, x_216);
x_218 = lean_expr_update_app(x_2, x_169, x_213);
lean_ctor_set(x_205, 1, x_217);
lean_ctor_set(x_205, 0, x_218);
return x_205;
}
}
else
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; 
x_219 = lean_ctor_get(x_205, 1);
x_220 = lean_ctor_get(x_205, 0);
lean_inc(x_219);
lean_inc(x_220);
lean_dec(x_205);
x_221 = lean_ctor_get(x_219, 0);
lean_inc(x_221);
x_222 = lean_ctor_get(x_219, 1);
lean_inc(x_222);
if (lean_is_exclusive(x_219)) {
 lean_ctor_release(x_219, 0);
 lean_ctor_release(x_219, 1);
 x_223 = x_219;
} else {
 lean_dec_ref(x_219);
 x_223 = lean_box(0);
}
lean_inc(x_220);
x_224 = l_HashMapImp_insert___at_Lean_AbstractTypeContext_InstantiateExprMVars_checkCache___spec__3(x_222, x_168, x_220);
if (lean_is_scalar(x_223)) {
 x_225 = lean_alloc_ctor(0, 2, 0);
} else {
 x_225 = x_223;
}
lean_ctor_set(x_225, 0, x_221);
lean_ctor_set(x_225, 1, x_224);
x_226 = lean_expr_update_app(x_2, x_169, x_220);
x_227 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_227, 0, x_226);
lean_ctor_set(x_227, 1, x_225);
return x_227;
}
}
else
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; 
lean_dec(x_168);
lean_dec(x_1);
x_228 = lean_ctor_get(x_204, 0);
lean_inc(x_228);
lean_dec(x_204);
x_229 = lean_expr_update_app(x_2, x_169, x_228);
x_230 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_230, 0, x_229);
lean_ctor_set(x_230, 1, x_170);
return x_230;
}
}
}
}
case 6:
{
uint8_t x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; uint8_t x_326; 
x_260 = lean_ctor_get_uint8(x_2, sizeof(void*)*3);
x_261 = lean_ctor_get(x_2, 1);
lean_inc(x_261);
x_262 = lean_ctor_get(x_2, 2);
lean_inc(x_262);
x_326 = lean_expr_has_expr_mvar(x_261);
if (x_326 == 0)
{
uint8_t x_327; 
x_327 = lean_expr_has_level_mvar(x_261);
if (x_327 == 0)
{
x_263 = x_261;
x_264 = x_3;
goto block_325;
}
else
{
lean_object* x_328; lean_object* x_329; 
x_328 = lean_ctor_get(x_3, 1);
lean_inc(x_328);
x_329 = l_HashMapImp_find___at_Lean_AbstractTypeContext_InstantiateExprMVars_checkCache___spec__1(x_328, x_261);
lean_dec(x_328);
if (lean_obj_tag(x_329) == 0)
{
lean_object* x_330; lean_object* x_331; lean_object* x_332; uint8_t x_333; 
lean_inc(x_261);
lean_inc(x_1);
x_330 = l_Lean_AbstractTypeContext_InstantiateExprMVars_main___main___rarg(x_1, x_261, x_3);
x_331 = lean_ctor_get(x_330, 1);
lean_inc(x_331);
x_332 = lean_ctor_get(x_330, 0);
lean_inc(x_332);
lean_dec(x_330);
x_333 = !lean_is_exclusive(x_331);
if (x_333 == 0)
{
lean_object* x_334; lean_object* x_335; 
x_334 = lean_ctor_get(x_331, 1);
lean_inc(x_332);
x_335 = l_HashMapImp_insert___at_Lean_AbstractTypeContext_InstantiateExprMVars_checkCache___spec__3(x_334, x_261, x_332);
lean_ctor_set(x_331, 1, x_335);
x_263 = x_332;
x_264 = x_331;
goto block_325;
}
else
{
lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; 
x_336 = lean_ctor_get(x_331, 0);
x_337 = lean_ctor_get(x_331, 1);
lean_inc(x_337);
lean_inc(x_336);
lean_dec(x_331);
lean_inc(x_332);
x_338 = l_HashMapImp_insert___at_Lean_AbstractTypeContext_InstantiateExprMVars_checkCache___spec__3(x_337, x_261, x_332);
x_339 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_339, 0, x_336);
lean_ctor_set(x_339, 1, x_338);
x_263 = x_332;
x_264 = x_339;
goto block_325;
}
}
else
{
lean_object* x_340; 
lean_dec(x_261);
x_340 = lean_ctor_get(x_329, 0);
lean_inc(x_340);
lean_dec(x_329);
x_263 = x_340;
x_264 = x_3;
goto block_325;
}
}
}
else
{
lean_object* x_341; lean_object* x_342; 
x_341 = lean_ctor_get(x_3, 1);
lean_inc(x_341);
x_342 = l_HashMapImp_find___at_Lean_AbstractTypeContext_InstantiateExprMVars_checkCache___spec__1(x_341, x_261);
lean_dec(x_341);
if (lean_obj_tag(x_342) == 0)
{
lean_object* x_343; lean_object* x_344; lean_object* x_345; uint8_t x_346; 
lean_inc(x_261);
lean_inc(x_1);
x_343 = l_Lean_AbstractTypeContext_InstantiateExprMVars_main___main___rarg(x_1, x_261, x_3);
x_344 = lean_ctor_get(x_343, 1);
lean_inc(x_344);
x_345 = lean_ctor_get(x_343, 0);
lean_inc(x_345);
lean_dec(x_343);
x_346 = !lean_is_exclusive(x_344);
if (x_346 == 0)
{
lean_object* x_347; lean_object* x_348; 
x_347 = lean_ctor_get(x_344, 1);
lean_inc(x_345);
x_348 = l_HashMapImp_insert___at_Lean_AbstractTypeContext_InstantiateExprMVars_checkCache___spec__3(x_347, x_261, x_345);
lean_ctor_set(x_344, 1, x_348);
x_263 = x_345;
x_264 = x_344;
goto block_325;
}
else
{
lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; 
x_349 = lean_ctor_get(x_344, 0);
x_350 = lean_ctor_get(x_344, 1);
lean_inc(x_350);
lean_inc(x_349);
lean_dec(x_344);
lean_inc(x_345);
x_351 = l_HashMapImp_insert___at_Lean_AbstractTypeContext_InstantiateExprMVars_checkCache___spec__3(x_350, x_261, x_345);
x_352 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_352, 0, x_349);
lean_ctor_set(x_352, 1, x_351);
x_263 = x_345;
x_264 = x_352;
goto block_325;
}
}
else
{
lean_object* x_353; 
lean_dec(x_261);
x_353 = lean_ctor_get(x_342, 0);
lean_inc(x_353);
lean_dec(x_342);
x_263 = x_353;
x_264 = x_3;
goto block_325;
}
}
block_325:
{
uint8_t x_265; 
x_265 = lean_expr_has_expr_mvar(x_262);
if (x_265 == 0)
{
uint8_t x_266; 
x_266 = lean_expr_has_level_mvar(x_262);
if (x_266 == 0)
{
lean_object* x_267; lean_object* x_268; 
lean_dec(x_1);
x_267 = lean_expr_update_lambda(x_2, x_260, x_263, x_262);
x_268 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_268, 0, x_267);
lean_ctor_set(x_268, 1, x_264);
return x_268;
}
else
{
lean_object* x_269; lean_object* x_270; 
x_269 = lean_ctor_get(x_264, 1);
lean_inc(x_269);
x_270 = l_HashMapImp_find___at_Lean_AbstractTypeContext_InstantiateExprMVars_checkCache___spec__1(x_269, x_262);
lean_dec(x_269);
if (lean_obj_tag(x_270) == 0)
{
lean_object* x_271; uint8_t x_272; 
lean_inc(x_262);
x_271 = l_Lean_AbstractTypeContext_InstantiateExprMVars_main___main___rarg(x_1, x_262, x_264);
x_272 = !lean_is_exclusive(x_271);
if (x_272 == 0)
{
lean_object* x_273; uint8_t x_274; 
x_273 = lean_ctor_get(x_271, 1);
x_274 = !lean_is_exclusive(x_273);
if (x_274 == 0)
{
lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; 
x_275 = lean_ctor_get(x_271, 0);
x_276 = lean_ctor_get(x_273, 1);
lean_inc(x_275);
x_277 = l_HashMapImp_insert___at_Lean_AbstractTypeContext_InstantiateExprMVars_checkCache___spec__3(x_276, x_262, x_275);
lean_ctor_set(x_273, 1, x_277);
x_278 = lean_expr_update_lambda(x_2, x_260, x_263, x_275);
lean_ctor_set(x_271, 0, x_278);
return x_271;
}
else
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; 
x_279 = lean_ctor_get(x_271, 0);
x_280 = lean_ctor_get(x_273, 0);
x_281 = lean_ctor_get(x_273, 1);
lean_inc(x_281);
lean_inc(x_280);
lean_dec(x_273);
lean_inc(x_279);
x_282 = l_HashMapImp_insert___at_Lean_AbstractTypeContext_InstantiateExprMVars_checkCache___spec__3(x_281, x_262, x_279);
x_283 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_283, 0, x_280);
lean_ctor_set(x_283, 1, x_282);
x_284 = lean_expr_update_lambda(x_2, x_260, x_263, x_279);
lean_ctor_set(x_271, 1, x_283);
lean_ctor_set(x_271, 0, x_284);
return x_271;
}
}
else
{
lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; 
x_285 = lean_ctor_get(x_271, 1);
x_286 = lean_ctor_get(x_271, 0);
lean_inc(x_285);
lean_inc(x_286);
lean_dec(x_271);
x_287 = lean_ctor_get(x_285, 0);
lean_inc(x_287);
x_288 = lean_ctor_get(x_285, 1);
lean_inc(x_288);
if (lean_is_exclusive(x_285)) {
 lean_ctor_release(x_285, 0);
 lean_ctor_release(x_285, 1);
 x_289 = x_285;
} else {
 lean_dec_ref(x_285);
 x_289 = lean_box(0);
}
lean_inc(x_286);
x_290 = l_HashMapImp_insert___at_Lean_AbstractTypeContext_InstantiateExprMVars_checkCache___spec__3(x_288, x_262, x_286);
if (lean_is_scalar(x_289)) {
 x_291 = lean_alloc_ctor(0, 2, 0);
} else {
 x_291 = x_289;
}
lean_ctor_set(x_291, 0, x_287);
lean_ctor_set(x_291, 1, x_290);
x_292 = lean_expr_update_lambda(x_2, x_260, x_263, x_286);
x_293 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_293, 0, x_292);
lean_ctor_set(x_293, 1, x_291);
return x_293;
}
}
else
{
lean_object* x_294; lean_object* x_295; lean_object* x_296; 
lean_dec(x_262);
lean_dec(x_1);
x_294 = lean_ctor_get(x_270, 0);
lean_inc(x_294);
lean_dec(x_270);
x_295 = lean_expr_update_lambda(x_2, x_260, x_263, x_294);
x_296 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_296, 0, x_295);
lean_ctor_set(x_296, 1, x_264);
return x_296;
}
}
}
else
{
lean_object* x_297; lean_object* x_298; 
x_297 = lean_ctor_get(x_264, 1);
lean_inc(x_297);
x_298 = l_HashMapImp_find___at_Lean_AbstractTypeContext_InstantiateExprMVars_checkCache___spec__1(x_297, x_262);
lean_dec(x_297);
if (lean_obj_tag(x_298) == 0)
{
lean_object* x_299; uint8_t x_300; 
lean_inc(x_262);
x_299 = l_Lean_AbstractTypeContext_InstantiateExprMVars_main___main___rarg(x_1, x_262, x_264);
x_300 = !lean_is_exclusive(x_299);
if (x_300 == 0)
{
lean_object* x_301; uint8_t x_302; 
x_301 = lean_ctor_get(x_299, 1);
x_302 = !lean_is_exclusive(x_301);
if (x_302 == 0)
{
lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; 
x_303 = lean_ctor_get(x_299, 0);
x_304 = lean_ctor_get(x_301, 1);
lean_inc(x_303);
x_305 = l_HashMapImp_insert___at_Lean_AbstractTypeContext_InstantiateExprMVars_checkCache___spec__3(x_304, x_262, x_303);
lean_ctor_set(x_301, 1, x_305);
x_306 = lean_expr_update_lambda(x_2, x_260, x_263, x_303);
lean_ctor_set(x_299, 0, x_306);
return x_299;
}
else
{
lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; 
x_307 = lean_ctor_get(x_299, 0);
x_308 = lean_ctor_get(x_301, 0);
x_309 = lean_ctor_get(x_301, 1);
lean_inc(x_309);
lean_inc(x_308);
lean_dec(x_301);
lean_inc(x_307);
x_310 = l_HashMapImp_insert___at_Lean_AbstractTypeContext_InstantiateExprMVars_checkCache___spec__3(x_309, x_262, x_307);
x_311 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_311, 0, x_308);
lean_ctor_set(x_311, 1, x_310);
x_312 = lean_expr_update_lambda(x_2, x_260, x_263, x_307);
lean_ctor_set(x_299, 1, x_311);
lean_ctor_set(x_299, 0, x_312);
return x_299;
}
}
else
{
lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; 
x_313 = lean_ctor_get(x_299, 1);
x_314 = lean_ctor_get(x_299, 0);
lean_inc(x_313);
lean_inc(x_314);
lean_dec(x_299);
x_315 = lean_ctor_get(x_313, 0);
lean_inc(x_315);
x_316 = lean_ctor_get(x_313, 1);
lean_inc(x_316);
if (lean_is_exclusive(x_313)) {
 lean_ctor_release(x_313, 0);
 lean_ctor_release(x_313, 1);
 x_317 = x_313;
} else {
 lean_dec_ref(x_313);
 x_317 = lean_box(0);
}
lean_inc(x_314);
x_318 = l_HashMapImp_insert___at_Lean_AbstractTypeContext_InstantiateExprMVars_checkCache___spec__3(x_316, x_262, x_314);
if (lean_is_scalar(x_317)) {
 x_319 = lean_alloc_ctor(0, 2, 0);
} else {
 x_319 = x_317;
}
lean_ctor_set(x_319, 0, x_315);
lean_ctor_set(x_319, 1, x_318);
x_320 = lean_expr_update_lambda(x_2, x_260, x_263, x_314);
x_321 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_321, 0, x_320);
lean_ctor_set(x_321, 1, x_319);
return x_321;
}
}
else
{
lean_object* x_322; lean_object* x_323; lean_object* x_324; 
lean_dec(x_262);
lean_dec(x_1);
x_322 = lean_ctor_get(x_298, 0);
lean_inc(x_322);
lean_dec(x_298);
x_323 = lean_expr_update_lambda(x_2, x_260, x_263, x_322);
x_324 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_324, 0, x_323);
lean_ctor_set(x_324, 1, x_264);
return x_324;
}
}
}
}
case 7:
{
uint8_t x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; uint8_t x_420; 
x_354 = lean_ctor_get_uint8(x_2, sizeof(void*)*3);
x_355 = lean_ctor_get(x_2, 1);
lean_inc(x_355);
x_356 = lean_ctor_get(x_2, 2);
lean_inc(x_356);
x_420 = lean_expr_has_expr_mvar(x_355);
if (x_420 == 0)
{
uint8_t x_421; 
x_421 = lean_expr_has_level_mvar(x_355);
if (x_421 == 0)
{
x_357 = x_355;
x_358 = x_3;
goto block_419;
}
else
{
lean_object* x_422; lean_object* x_423; 
x_422 = lean_ctor_get(x_3, 1);
lean_inc(x_422);
x_423 = l_HashMapImp_find___at_Lean_AbstractTypeContext_InstantiateExprMVars_checkCache___spec__1(x_422, x_355);
lean_dec(x_422);
if (lean_obj_tag(x_423) == 0)
{
lean_object* x_424; lean_object* x_425; lean_object* x_426; uint8_t x_427; 
lean_inc(x_355);
lean_inc(x_1);
x_424 = l_Lean_AbstractTypeContext_InstantiateExprMVars_main___main___rarg(x_1, x_355, x_3);
x_425 = lean_ctor_get(x_424, 1);
lean_inc(x_425);
x_426 = lean_ctor_get(x_424, 0);
lean_inc(x_426);
lean_dec(x_424);
x_427 = !lean_is_exclusive(x_425);
if (x_427 == 0)
{
lean_object* x_428; lean_object* x_429; 
x_428 = lean_ctor_get(x_425, 1);
lean_inc(x_426);
x_429 = l_HashMapImp_insert___at_Lean_AbstractTypeContext_InstantiateExprMVars_checkCache___spec__3(x_428, x_355, x_426);
lean_ctor_set(x_425, 1, x_429);
x_357 = x_426;
x_358 = x_425;
goto block_419;
}
else
{
lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; 
x_430 = lean_ctor_get(x_425, 0);
x_431 = lean_ctor_get(x_425, 1);
lean_inc(x_431);
lean_inc(x_430);
lean_dec(x_425);
lean_inc(x_426);
x_432 = l_HashMapImp_insert___at_Lean_AbstractTypeContext_InstantiateExprMVars_checkCache___spec__3(x_431, x_355, x_426);
x_433 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_433, 0, x_430);
lean_ctor_set(x_433, 1, x_432);
x_357 = x_426;
x_358 = x_433;
goto block_419;
}
}
else
{
lean_object* x_434; 
lean_dec(x_355);
x_434 = lean_ctor_get(x_423, 0);
lean_inc(x_434);
lean_dec(x_423);
x_357 = x_434;
x_358 = x_3;
goto block_419;
}
}
}
else
{
lean_object* x_435; lean_object* x_436; 
x_435 = lean_ctor_get(x_3, 1);
lean_inc(x_435);
x_436 = l_HashMapImp_find___at_Lean_AbstractTypeContext_InstantiateExprMVars_checkCache___spec__1(x_435, x_355);
lean_dec(x_435);
if (lean_obj_tag(x_436) == 0)
{
lean_object* x_437; lean_object* x_438; lean_object* x_439; uint8_t x_440; 
lean_inc(x_355);
lean_inc(x_1);
x_437 = l_Lean_AbstractTypeContext_InstantiateExprMVars_main___main___rarg(x_1, x_355, x_3);
x_438 = lean_ctor_get(x_437, 1);
lean_inc(x_438);
x_439 = lean_ctor_get(x_437, 0);
lean_inc(x_439);
lean_dec(x_437);
x_440 = !lean_is_exclusive(x_438);
if (x_440 == 0)
{
lean_object* x_441; lean_object* x_442; 
x_441 = lean_ctor_get(x_438, 1);
lean_inc(x_439);
x_442 = l_HashMapImp_insert___at_Lean_AbstractTypeContext_InstantiateExprMVars_checkCache___spec__3(x_441, x_355, x_439);
lean_ctor_set(x_438, 1, x_442);
x_357 = x_439;
x_358 = x_438;
goto block_419;
}
else
{
lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; 
x_443 = lean_ctor_get(x_438, 0);
x_444 = lean_ctor_get(x_438, 1);
lean_inc(x_444);
lean_inc(x_443);
lean_dec(x_438);
lean_inc(x_439);
x_445 = l_HashMapImp_insert___at_Lean_AbstractTypeContext_InstantiateExprMVars_checkCache___spec__3(x_444, x_355, x_439);
x_446 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_446, 0, x_443);
lean_ctor_set(x_446, 1, x_445);
x_357 = x_439;
x_358 = x_446;
goto block_419;
}
}
else
{
lean_object* x_447; 
lean_dec(x_355);
x_447 = lean_ctor_get(x_436, 0);
lean_inc(x_447);
lean_dec(x_436);
x_357 = x_447;
x_358 = x_3;
goto block_419;
}
}
block_419:
{
uint8_t x_359; 
x_359 = lean_expr_has_expr_mvar(x_356);
if (x_359 == 0)
{
uint8_t x_360; 
x_360 = lean_expr_has_level_mvar(x_356);
if (x_360 == 0)
{
lean_object* x_361; lean_object* x_362; 
lean_dec(x_1);
x_361 = lean_expr_update_forall(x_2, x_354, x_357, x_356);
x_362 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_362, 0, x_361);
lean_ctor_set(x_362, 1, x_358);
return x_362;
}
else
{
lean_object* x_363; lean_object* x_364; 
x_363 = lean_ctor_get(x_358, 1);
lean_inc(x_363);
x_364 = l_HashMapImp_find___at_Lean_AbstractTypeContext_InstantiateExprMVars_checkCache___spec__1(x_363, x_356);
lean_dec(x_363);
if (lean_obj_tag(x_364) == 0)
{
lean_object* x_365; uint8_t x_366; 
lean_inc(x_356);
x_365 = l_Lean_AbstractTypeContext_InstantiateExprMVars_main___main___rarg(x_1, x_356, x_358);
x_366 = !lean_is_exclusive(x_365);
if (x_366 == 0)
{
lean_object* x_367; uint8_t x_368; 
x_367 = lean_ctor_get(x_365, 1);
x_368 = !lean_is_exclusive(x_367);
if (x_368 == 0)
{
lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; 
x_369 = lean_ctor_get(x_365, 0);
x_370 = lean_ctor_get(x_367, 1);
lean_inc(x_369);
x_371 = l_HashMapImp_insert___at_Lean_AbstractTypeContext_InstantiateExprMVars_checkCache___spec__3(x_370, x_356, x_369);
lean_ctor_set(x_367, 1, x_371);
x_372 = lean_expr_update_forall(x_2, x_354, x_357, x_369);
lean_ctor_set(x_365, 0, x_372);
return x_365;
}
else
{
lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; 
x_373 = lean_ctor_get(x_365, 0);
x_374 = lean_ctor_get(x_367, 0);
x_375 = lean_ctor_get(x_367, 1);
lean_inc(x_375);
lean_inc(x_374);
lean_dec(x_367);
lean_inc(x_373);
x_376 = l_HashMapImp_insert___at_Lean_AbstractTypeContext_InstantiateExprMVars_checkCache___spec__3(x_375, x_356, x_373);
x_377 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_377, 0, x_374);
lean_ctor_set(x_377, 1, x_376);
x_378 = lean_expr_update_forall(x_2, x_354, x_357, x_373);
lean_ctor_set(x_365, 1, x_377);
lean_ctor_set(x_365, 0, x_378);
return x_365;
}
}
else
{
lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; 
x_379 = lean_ctor_get(x_365, 1);
x_380 = lean_ctor_get(x_365, 0);
lean_inc(x_379);
lean_inc(x_380);
lean_dec(x_365);
x_381 = lean_ctor_get(x_379, 0);
lean_inc(x_381);
x_382 = lean_ctor_get(x_379, 1);
lean_inc(x_382);
if (lean_is_exclusive(x_379)) {
 lean_ctor_release(x_379, 0);
 lean_ctor_release(x_379, 1);
 x_383 = x_379;
} else {
 lean_dec_ref(x_379);
 x_383 = lean_box(0);
}
lean_inc(x_380);
x_384 = l_HashMapImp_insert___at_Lean_AbstractTypeContext_InstantiateExprMVars_checkCache___spec__3(x_382, x_356, x_380);
if (lean_is_scalar(x_383)) {
 x_385 = lean_alloc_ctor(0, 2, 0);
} else {
 x_385 = x_383;
}
lean_ctor_set(x_385, 0, x_381);
lean_ctor_set(x_385, 1, x_384);
x_386 = lean_expr_update_forall(x_2, x_354, x_357, x_380);
x_387 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_387, 0, x_386);
lean_ctor_set(x_387, 1, x_385);
return x_387;
}
}
else
{
lean_object* x_388; lean_object* x_389; lean_object* x_390; 
lean_dec(x_356);
lean_dec(x_1);
x_388 = lean_ctor_get(x_364, 0);
lean_inc(x_388);
lean_dec(x_364);
x_389 = lean_expr_update_forall(x_2, x_354, x_357, x_388);
x_390 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_390, 0, x_389);
lean_ctor_set(x_390, 1, x_358);
return x_390;
}
}
}
else
{
lean_object* x_391; lean_object* x_392; 
x_391 = lean_ctor_get(x_358, 1);
lean_inc(x_391);
x_392 = l_HashMapImp_find___at_Lean_AbstractTypeContext_InstantiateExprMVars_checkCache___spec__1(x_391, x_356);
lean_dec(x_391);
if (lean_obj_tag(x_392) == 0)
{
lean_object* x_393; uint8_t x_394; 
lean_inc(x_356);
x_393 = l_Lean_AbstractTypeContext_InstantiateExprMVars_main___main___rarg(x_1, x_356, x_358);
x_394 = !lean_is_exclusive(x_393);
if (x_394 == 0)
{
lean_object* x_395; uint8_t x_396; 
x_395 = lean_ctor_get(x_393, 1);
x_396 = !lean_is_exclusive(x_395);
if (x_396 == 0)
{
lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; 
x_397 = lean_ctor_get(x_393, 0);
x_398 = lean_ctor_get(x_395, 1);
lean_inc(x_397);
x_399 = l_HashMapImp_insert___at_Lean_AbstractTypeContext_InstantiateExprMVars_checkCache___spec__3(x_398, x_356, x_397);
lean_ctor_set(x_395, 1, x_399);
x_400 = lean_expr_update_forall(x_2, x_354, x_357, x_397);
lean_ctor_set(x_393, 0, x_400);
return x_393;
}
else
{
lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; 
x_401 = lean_ctor_get(x_393, 0);
x_402 = lean_ctor_get(x_395, 0);
x_403 = lean_ctor_get(x_395, 1);
lean_inc(x_403);
lean_inc(x_402);
lean_dec(x_395);
lean_inc(x_401);
x_404 = l_HashMapImp_insert___at_Lean_AbstractTypeContext_InstantiateExprMVars_checkCache___spec__3(x_403, x_356, x_401);
x_405 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_405, 0, x_402);
lean_ctor_set(x_405, 1, x_404);
x_406 = lean_expr_update_forall(x_2, x_354, x_357, x_401);
lean_ctor_set(x_393, 1, x_405);
lean_ctor_set(x_393, 0, x_406);
return x_393;
}
}
else
{
lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; 
x_407 = lean_ctor_get(x_393, 1);
x_408 = lean_ctor_get(x_393, 0);
lean_inc(x_407);
lean_inc(x_408);
lean_dec(x_393);
x_409 = lean_ctor_get(x_407, 0);
lean_inc(x_409);
x_410 = lean_ctor_get(x_407, 1);
lean_inc(x_410);
if (lean_is_exclusive(x_407)) {
 lean_ctor_release(x_407, 0);
 lean_ctor_release(x_407, 1);
 x_411 = x_407;
} else {
 lean_dec_ref(x_407);
 x_411 = lean_box(0);
}
lean_inc(x_408);
x_412 = l_HashMapImp_insert___at_Lean_AbstractTypeContext_InstantiateExprMVars_checkCache___spec__3(x_410, x_356, x_408);
if (lean_is_scalar(x_411)) {
 x_413 = lean_alloc_ctor(0, 2, 0);
} else {
 x_413 = x_411;
}
lean_ctor_set(x_413, 0, x_409);
lean_ctor_set(x_413, 1, x_412);
x_414 = lean_expr_update_forall(x_2, x_354, x_357, x_408);
x_415 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_415, 0, x_414);
lean_ctor_set(x_415, 1, x_413);
return x_415;
}
}
else
{
lean_object* x_416; lean_object* x_417; lean_object* x_418; 
lean_dec(x_356);
lean_dec(x_1);
x_416 = lean_ctor_get(x_392, 0);
lean_inc(x_416);
lean_dec(x_392);
x_417 = lean_expr_update_forall(x_2, x_354, x_357, x_416);
x_418 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_418, 0, x_417);
lean_ctor_set(x_418, 1, x_358);
return x_418;
}
}
}
}
case 8:
{
lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_514; lean_object* x_515; uint8_t x_552; 
x_448 = lean_ctor_get(x_2, 1);
lean_inc(x_448);
x_449 = lean_ctor_get(x_2, 2);
lean_inc(x_449);
x_450 = lean_ctor_get(x_2, 3);
lean_inc(x_450);
x_552 = lean_expr_has_expr_mvar(x_448);
if (x_552 == 0)
{
uint8_t x_553; 
x_553 = lean_expr_has_level_mvar(x_448);
if (x_553 == 0)
{
x_514 = x_448;
x_515 = x_3;
goto block_551;
}
else
{
lean_object* x_554; lean_object* x_555; 
x_554 = lean_ctor_get(x_3, 1);
lean_inc(x_554);
x_555 = l_HashMapImp_find___at_Lean_AbstractTypeContext_InstantiateExprMVars_checkCache___spec__1(x_554, x_448);
lean_dec(x_554);
if (lean_obj_tag(x_555) == 0)
{
lean_object* x_556; lean_object* x_557; lean_object* x_558; uint8_t x_559; 
lean_inc(x_448);
lean_inc(x_1);
x_556 = l_Lean_AbstractTypeContext_InstantiateExprMVars_main___main___rarg(x_1, x_448, x_3);
x_557 = lean_ctor_get(x_556, 1);
lean_inc(x_557);
x_558 = lean_ctor_get(x_556, 0);
lean_inc(x_558);
lean_dec(x_556);
x_559 = !lean_is_exclusive(x_557);
if (x_559 == 0)
{
lean_object* x_560; lean_object* x_561; 
x_560 = lean_ctor_get(x_557, 1);
lean_inc(x_558);
x_561 = l_HashMapImp_insert___at_Lean_AbstractTypeContext_InstantiateExprMVars_checkCache___spec__3(x_560, x_448, x_558);
lean_ctor_set(x_557, 1, x_561);
x_514 = x_558;
x_515 = x_557;
goto block_551;
}
else
{
lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_565; 
x_562 = lean_ctor_get(x_557, 0);
x_563 = lean_ctor_get(x_557, 1);
lean_inc(x_563);
lean_inc(x_562);
lean_dec(x_557);
lean_inc(x_558);
x_564 = l_HashMapImp_insert___at_Lean_AbstractTypeContext_InstantiateExprMVars_checkCache___spec__3(x_563, x_448, x_558);
x_565 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_565, 0, x_562);
lean_ctor_set(x_565, 1, x_564);
x_514 = x_558;
x_515 = x_565;
goto block_551;
}
}
else
{
lean_object* x_566; 
lean_dec(x_448);
x_566 = lean_ctor_get(x_555, 0);
lean_inc(x_566);
lean_dec(x_555);
x_514 = x_566;
x_515 = x_3;
goto block_551;
}
}
}
else
{
lean_object* x_567; lean_object* x_568; 
x_567 = lean_ctor_get(x_3, 1);
lean_inc(x_567);
x_568 = l_HashMapImp_find___at_Lean_AbstractTypeContext_InstantiateExprMVars_checkCache___spec__1(x_567, x_448);
lean_dec(x_567);
if (lean_obj_tag(x_568) == 0)
{
lean_object* x_569; lean_object* x_570; lean_object* x_571; uint8_t x_572; 
lean_inc(x_448);
lean_inc(x_1);
x_569 = l_Lean_AbstractTypeContext_InstantiateExprMVars_main___main___rarg(x_1, x_448, x_3);
x_570 = lean_ctor_get(x_569, 1);
lean_inc(x_570);
x_571 = lean_ctor_get(x_569, 0);
lean_inc(x_571);
lean_dec(x_569);
x_572 = !lean_is_exclusive(x_570);
if (x_572 == 0)
{
lean_object* x_573; lean_object* x_574; 
x_573 = lean_ctor_get(x_570, 1);
lean_inc(x_571);
x_574 = l_HashMapImp_insert___at_Lean_AbstractTypeContext_InstantiateExprMVars_checkCache___spec__3(x_573, x_448, x_571);
lean_ctor_set(x_570, 1, x_574);
x_514 = x_571;
x_515 = x_570;
goto block_551;
}
else
{
lean_object* x_575; lean_object* x_576; lean_object* x_577; lean_object* x_578; 
x_575 = lean_ctor_get(x_570, 0);
x_576 = lean_ctor_get(x_570, 1);
lean_inc(x_576);
lean_inc(x_575);
lean_dec(x_570);
lean_inc(x_571);
x_577 = l_HashMapImp_insert___at_Lean_AbstractTypeContext_InstantiateExprMVars_checkCache___spec__3(x_576, x_448, x_571);
x_578 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_578, 0, x_575);
lean_ctor_set(x_578, 1, x_577);
x_514 = x_571;
x_515 = x_578;
goto block_551;
}
}
else
{
lean_object* x_579; 
lean_dec(x_448);
x_579 = lean_ctor_get(x_568, 0);
lean_inc(x_579);
lean_dec(x_568);
x_514 = x_579;
x_515 = x_3;
goto block_551;
}
}
block_513:
{
uint8_t x_453; 
x_453 = lean_expr_has_expr_mvar(x_450);
if (x_453 == 0)
{
uint8_t x_454; 
x_454 = lean_expr_has_level_mvar(x_450);
if (x_454 == 0)
{
lean_object* x_455; lean_object* x_456; 
lean_dec(x_1);
x_455 = lean_apply_1(x_451, x_450);
x_456 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_456, 0, x_455);
lean_ctor_set(x_456, 1, x_452);
return x_456;
}
else
{
lean_object* x_457; lean_object* x_458; 
x_457 = lean_ctor_get(x_452, 1);
lean_inc(x_457);
x_458 = l_HashMapImp_find___at_Lean_AbstractTypeContext_InstantiateExprMVars_checkCache___spec__1(x_457, x_450);
lean_dec(x_457);
if (lean_obj_tag(x_458) == 0)
{
lean_object* x_459; uint8_t x_460; 
lean_inc(x_450);
x_459 = l_Lean_AbstractTypeContext_InstantiateExprMVars_main___main___rarg(x_1, x_450, x_452);
x_460 = !lean_is_exclusive(x_459);
if (x_460 == 0)
{
lean_object* x_461; uint8_t x_462; 
x_461 = lean_ctor_get(x_459, 1);
x_462 = !lean_is_exclusive(x_461);
if (x_462 == 0)
{
lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; 
x_463 = lean_ctor_get(x_459, 0);
x_464 = lean_ctor_get(x_461, 1);
lean_inc(x_463);
x_465 = l_HashMapImp_insert___at_Lean_AbstractTypeContext_InstantiateExprMVars_checkCache___spec__3(x_464, x_450, x_463);
lean_ctor_set(x_461, 1, x_465);
x_466 = lean_apply_1(x_451, x_463);
lean_ctor_set(x_459, 0, x_466);
return x_459;
}
else
{
lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; 
x_467 = lean_ctor_get(x_459, 0);
x_468 = lean_ctor_get(x_461, 0);
x_469 = lean_ctor_get(x_461, 1);
lean_inc(x_469);
lean_inc(x_468);
lean_dec(x_461);
lean_inc(x_467);
x_470 = l_HashMapImp_insert___at_Lean_AbstractTypeContext_InstantiateExprMVars_checkCache___spec__3(x_469, x_450, x_467);
x_471 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_471, 0, x_468);
lean_ctor_set(x_471, 1, x_470);
x_472 = lean_apply_1(x_451, x_467);
lean_ctor_set(x_459, 1, x_471);
lean_ctor_set(x_459, 0, x_472);
return x_459;
}
}
else
{
lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; 
x_473 = lean_ctor_get(x_459, 1);
x_474 = lean_ctor_get(x_459, 0);
lean_inc(x_473);
lean_inc(x_474);
lean_dec(x_459);
x_475 = lean_ctor_get(x_473, 0);
lean_inc(x_475);
x_476 = lean_ctor_get(x_473, 1);
lean_inc(x_476);
if (lean_is_exclusive(x_473)) {
 lean_ctor_release(x_473, 0);
 lean_ctor_release(x_473, 1);
 x_477 = x_473;
} else {
 lean_dec_ref(x_473);
 x_477 = lean_box(0);
}
lean_inc(x_474);
x_478 = l_HashMapImp_insert___at_Lean_AbstractTypeContext_InstantiateExprMVars_checkCache___spec__3(x_476, x_450, x_474);
if (lean_is_scalar(x_477)) {
 x_479 = lean_alloc_ctor(0, 2, 0);
} else {
 x_479 = x_477;
}
lean_ctor_set(x_479, 0, x_475);
lean_ctor_set(x_479, 1, x_478);
x_480 = lean_apply_1(x_451, x_474);
x_481 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_481, 0, x_480);
lean_ctor_set(x_481, 1, x_479);
return x_481;
}
}
else
{
lean_object* x_482; lean_object* x_483; lean_object* x_484; 
lean_dec(x_450);
lean_dec(x_1);
x_482 = lean_ctor_get(x_458, 0);
lean_inc(x_482);
lean_dec(x_458);
x_483 = lean_apply_1(x_451, x_482);
x_484 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_484, 0, x_483);
lean_ctor_set(x_484, 1, x_452);
return x_484;
}
}
}
else
{
lean_object* x_485; lean_object* x_486; 
x_485 = lean_ctor_get(x_452, 1);
lean_inc(x_485);
x_486 = l_HashMapImp_find___at_Lean_AbstractTypeContext_InstantiateExprMVars_checkCache___spec__1(x_485, x_450);
lean_dec(x_485);
if (lean_obj_tag(x_486) == 0)
{
lean_object* x_487; uint8_t x_488; 
lean_inc(x_450);
x_487 = l_Lean_AbstractTypeContext_InstantiateExprMVars_main___main___rarg(x_1, x_450, x_452);
x_488 = !lean_is_exclusive(x_487);
if (x_488 == 0)
{
lean_object* x_489; uint8_t x_490; 
x_489 = lean_ctor_get(x_487, 1);
x_490 = !lean_is_exclusive(x_489);
if (x_490 == 0)
{
lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; 
x_491 = lean_ctor_get(x_487, 0);
x_492 = lean_ctor_get(x_489, 1);
lean_inc(x_491);
x_493 = l_HashMapImp_insert___at_Lean_AbstractTypeContext_InstantiateExprMVars_checkCache___spec__3(x_492, x_450, x_491);
lean_ctor_set(x_489, 1, x_493);
x_494 = lean_apply_1(x_451, x_491);
lean_ctor_set(x_487, 0, x_494);
return x_487;
}
else
{
lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; 
x_495 = lean_ctor_get(x_487, 0);
x_496 = lean_ctor_get(x_489, 0);
x_497 = lean_ctor_get(x_489, 1);
lean_inc(x_497);
lean_inc(x_496);
lean_dec(x_489);
lean_inc(x_495);
x_498 = l_HashMapImp_insert___at_Lean_AbstractTypeContext_InstantiateExprMVars_checkCache___spec__3(x_497, x_450, x_495);
x_499 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_499, 0, x_496);
lean_ctor_set(x_499, 1, x_498);
x_500 = lean_apply_1(x_451, x_495);
lean_ctor_set(x_487, 1, x_499);
lean_ctor_set(x_487, 0, x_500);
return x_487;
}
}
else
{
lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; 
x_501 = lean_ctor_get(x_487, 1);
x_502 = lean_ctor_get(x_487, 0);
lean_inc(x_501);
lean_inc(x_502);
lean_dec(x_487);
x_503 = lean_ctor_get(x_501, 0);
lean_inc(x_503);
x_504 = lean_ctor_get(x_501, 1);
lean_inc(x_504);
if (lean_is_exclusive(x_501)) {
 lean_ctor_release(x_501, 0);
 lean_ctor_release(x_501, 1);
 x_505 = x_501;
} else {
 lean_dec_ref(x_501);
 x_505 = lean_box(0);
}
lean_inc(x_502);
x_506 = l_HashMapImp_insert___at_Lean_AbstractTypeContext_InstantiateExprMVars_checkCache___spec__3(x_504, x_450, x_502);
if (lean_is_scalar(x_505)) {
 x_507 = lean_alloc_ctor(0, 2, 0);
} else {
 x_507 = x_505;
}
lean_ctor_set(x_507, 0, x_503);
lean_ctor_set(x_507, 1, x_506);
x_508 = lean_apply_1(x_451, x_502);
x_509 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_509, 0, x_508);
lean_ctor_set(x_509, 1, x_507);
return x_509;
}
}
else
{
lean_object* x_510; lean_object* x_511; lean_object* x_512; 
lean_dec(x_450);
lean_dec(x_1);
x_510 = lean_ctor_get(x_486, 0);
lean_inc(x_510);
lean_dec(x_486);
x_511 = lean_apply_1(x_451, x_510);
x_512 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_512, 0, x_511);
lean_ctor_set(x_512, 1, x_452);
return x_512;
}
}
}
block_551:
{
uint8_t x_516; 
x_516 = lean_expr_has_expr_mvar(x_449);
if (x_516 == 0)
{
uint8_t x_517; 
x_517 = lean_expr_has_level_mvar(x_449);
if (x_517 == 0)
{
lean_object* x_518; 
x_518 = lean_alloc_closure((void*)(l_Lean_Expr_updateLet_x21), 4, 3);
lean_closure_set(x_518, 0, x_2);
lean_closure_set(x_518, 1, x_514);
lean_closure_set(x_518, 2, x_449);
x_451 = x_518;
x_452 = x_515;
goto block_513;
}
else
{
lean_object* x_519; lean_object* x_520; 
x_519 = lean_ctor_get(x_515, 1);
lean_inc(x_519);
x_520 = l_HashMapImp_find___at_Lean_AbstractTypeContext_InstantiateExprMVars_checkCache___spec__1(x_519, x_449);
lean_dec(x_519);
if (lean_obj_tag(x_520) == 0)
{
lean_object* x_521; lean_object* x_522; lean_object* x_523; uint8_t x_524; 
lean_inc(x_449);
lean_inc(x_1);
x_521 = l_Lean_AbstractTypeContext_InstantiateExprMVars_main___main___rarg(x_1, x_449, x_515);
x_522 = lean_ctor_get(x_521, 1);
lean_inc(x_522);
x_523 = lean_ctor_get(x_521, 0);
lean_inc(x_523);
lean_dec(x_521);
x_524 = !lean_is_exclusive(x_522);
if (x_524 == 0)
{
lean_object* x_525; lean_object* x_526; lean_object* x_527; 
x_525 = lean_ctor_get(x_522, 1);
lean_inc(x_523);
x_526 = l_HashMapImp_insert___at_Lean_AbstractTypeContext_InstantiateExprMVars_checkCache___spec__3(x_525, x_449, x_523);
lean_ctor_set(x_522, 1, x_526);
x_527 = lean_alloc_closure((void*)(l_Lean_Expr_updateLet_x21), 4, 3);
lean_closure_set(x_527, 0, x_2);
lean_closure_set(x_527, 1, x_514);
lean_closure_set(x_527, 2, x_523);
x_451 = x_527;
x_452 = x_522;
goto block_513;
}
else
{
lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; 
x_528 = lean_ctor_get(x_522, 0);
x_529 = lean_ctor_get(x_522, 1);
lean_inc(x_529);
lean_inc(x_528);
lean_dec(x_522);
lean_inc(x_523);
x_530 = l_HashMapImp_insert___at_Lean_AbstractTypeContext_InstantiateExprMVars_checkCache___spec__3(x_529, x_449, x_523);
x_531 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_531, 0, x_528);
lean_ctor_set(x_531, 1, x_530);
x_532 = lean_alloc_closure((void*)(l_Lean_Expr_updateLet_x21), 4, 3);
lean_closure_set(x_532, 0, x_2);
lean_closure_set(x_532, 1, x_514);
lean_closure_set(x_532, 2, x_523);
x_451 = x_532;
x_452 = x_531;
goto block_513;
}
}
else
{
lean_object* x_533; lean_object* x_534; 
lean_dec(x_449);
x_533 = lean_ctor_get(x_520, 0);
lean_inc(x_533);
lean_dec(x_520);
x_534 = lean_alloc_closure((void*)(l_Lean_Expr_updateLet_x21), 4, 3);
lean_closure_set(x_534, 0, x_2);
lean_closure_set(x_534, 1, x_514);
lean_closure_set(x_534, 2, x_533);
x_451 = x_534;
x_452 = x_515;
goto block_513;
}
}
}
else
{
lean_object* x_535; lean_object* x_536; 
x_535 = lean_ctor_get(x_515, 1);
lean_inc(x_535);
x_536 = l_HashMapImp_find___at_Lean_AbstractTypeContext_InstantiateExprMVars_checkCache___spec__1(x_535, x_449);
lean_dec(x_535);
if (lean_obj_tag(x_536) == 0)
{
lean_object* x_537; lean_object* x_538; lean_object* x_539; uint8_t x_540; 
lean_inc(x_449);
lean_inc(x_1);
x_537 = l_Lean_AbstractTypeContext_InstantiateExprMVars_main___main___rarg(x_1, x_449, x_515);
x_538 = lean_ctor_get(x_537, 1);
lean_inc(x_538);
x_539 = lean_ctor_get(x_537, 0);
lean_inc(x_539);
lean_dec(x_537);
x_540 = !lean_is_exclusive(x_538);
if (x_540 == 0)
{
lean_object* x_541; lean_object* x_542; lean_object* x_543; 
x_541 = lean_ctor_get(x_538, 1);
lean_inc(x_539);
x_542 = l_HashMapImp_insert___at_Lean_AbstractTypeContext_InstantiateExprMVars_checkCache___spec__3(x_541, x_449, x_539);
lean_ctor_set(x_538, 1, x_542);
x_543 = lean_alloc_closure((void*)(l_Lean_Expr_updateLet_x21), 4, 3);
lean_closure_set(x_543, 0, x_2);
lean_closure_set(x_543, 1, x_514);
lean_closure_set(x_543, 2, x_539);
x_451 = x_543;
x_452 = x_538;
goto block_513;
}
else
{
lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; 
x_544 = lean_ctor_get(x_538, 0);
x_545 = lean_ctor_get(x_538, 1);
lean_inc(x_545);
lean_inc(x_544);
lean_dec(x_538);
lean_inc(x_539);
x_546 = l_HashMapImp_insert___at_Lean_AbstractTypeContext_InstantiateExprMVars_checkCache___spec__3(x_545, x_449, x_539);
x_547 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_547, 0, x_544);
lean_ctor_set(x_547, 1, x_546);
x_548 = lean_alloc_closure((void*)(l_Lean_Expr_updateLet_x21), 4, 3);
lean_closure_set(x_548, 0, x_2);
lean_closure_set(x_548, 1, x_514);
lean_closure_set(x_548, 2, x_539);
x_451 = x_548;
x_452 = x_547;
goto block_513;
}
}
else
{
lean_object* x_549; lean_object* x_550; 
lean_dec(x_449);
x_549 = lean_ctor_get(x_536, 0);
lean_inc(x_549);
lean_dec(x_536);
x_550 = lean_alloc_closure((void*)(l_Lean_Expr_updateLet_x21), 4, 3);
lean_closure_set(x_550, 0, x_2);
lean_closure_set(x_550, 1, x_514);
lean_closure_set(x_550, 2, x_549);
x_451 = x_550;
x_452 = x_515;
goto block_513;
}
}
}
}
case 10:
{
lean_object* x_580; uint8_t x_581; 
x_580 = lean_ctor_get(x_2, 1);
lean_inc(x_580);
x_581 = lean_expr_has_expr_mvar(x_580);
if (x_581 == 0)
{
uint8_t x_582; 
x_582 = lean_expr_has_level_mvar(x_580);
if (x_582 == 0)
{
lean_dec(x_1);
x_16 = x_580;
x_17 = x_3;
goto block_26;
}
else
{
lean_object* x_583; lean_object* x_584; 
x_583 = lean_ctor_get(x_3, 1);
lean_inc(x_583);
x_584 = l_HashMapImp_find___at_Lean_AbstractTypeContext_InstantiateExprMVars_checkCache___spec__1(x_583, x_580);
lean_dec(x_583);
if (lean_obj_tag(x_584) == 0)
{
lean_object* x_585; lean_object* x_586; lean_object* x_587; uint8_t x_588; 
lean_inc(x_580);
x_585 = l_Lean_AbstractTypeContext_InstantiateExprMVars_main___main___rarg(x_1, x_580, x_3);
x_586 = lean_ctor_get(x_585, 1);
lean_inc(x_586);
x_587 = lean_ctor_get(x_585, 0);
lean_inc(x_587);
lean_dec(x_585);
x_588 = !lean_is_exclusive(x_586);
if (x_588 == 0)
{
lean_object* x_589; lean_object* x_590; 
x_589 = lean_ctor_get(x_586, 1);
lean_inc(x_587);
x_590 = l_HashMapImp_insert___at_Lean_AbstractTypeContext_InstantiateExprMVars_checkCache___spec__3(x_589, x_580, x_587);
lean_ctor_set(x_586, 1, x_590);
x_16 = x_587;
x_17 = x_586;
goto block_26;
}
else
{
lean_object* x_591; lean_object* x_592; lean_object* x_593; lean_object* x_594; 
x_591 = lean_ctor_get(x_586, 0);
x_592 = lean_ctor_get(x_586, 1);
lean_inc(x_592);
lean_inc(x_591);
lean_dec(x_586);
lean_inc(x_587);
x_593 = l_HashMapImp_insert___at_Lean_AbstractTypeContext_InstantiateExprMVars_checkCache___spec__3(x_592, x_580, x_587);
x_594 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_594, 0, x_591);
lean_ctor_set(x_594, 1, x_593);
x_16 = x_587;
x_17 = x_594;
goto block_26;
}
}
else
{
lean_object* x_595; 
lean_dec(x_580);
lean_dec(x_1);
x_595 = lean_ctor_get(x_584, 0);
lean_inc(x_595);
lean_dec(x_584);
x_16 = x_595;
x_17 = x_3;
goto block_26;
}
}
}
else
{
lean_object* x_596; lean_object* x_597; 
x_596 = lean_ctor_get(x_3, 1);
lean_inc(x_596);
x_597 = l_HashMapImp_find___at_Lean_AbstractTypeContext_InstantiateExprMVars_checkCache___spec__1(x_596, x_580);
lean_dec(x_596);
if (lean_obj_tag(x_597) == 0)
{
lean_object* x_598; lean_object* x_599; lean_object* x_600; uint8_t x_601; 
lean_inc(x_580);
x_598 = l_Lean_AbstractTypeContext_InstantiateExprMVars_main___main___rarg(x_1, x_580, x_3);
x_599 = lean_ctor_get(x_598, 1);
lean_inc(x_599);
x_600 = lean_ctor_get(x_598, 0);
lean_inc(x_600);
lean_dec(x_598);
x_601 = !lean_is_exclusive(x_599);
if (x_601 == 0)
{
lean_object* x_602; lean_object* x_603; 
x_602 = lean_ctor_get(x_599, 1);
lean_inc(x_600);
x_603 = l_HashMapImp_insert___at_Lean_AbstractTypeContext_InstantiateExprMVars_checkCache___spec__3(x_602, x_580, x_600);
lean_ctor_set(x_599, 1, x_603);
x_16 = x_600;
x_17 = x_599;
goto block_26;
}
else
{
lean_object* x_604; lean_object* x_605; lean_object* x_606; lean_object* x_607; 
x_604 = lean_ctor_get(x_599, 0);
x_605 = lean_ctor_get(x_599, 1);
lean_inc(x_605);
lean_inc(x_604);
lean_dec(x_599);
lean_inc(x_600);
x_606 = l_HashMapImp_insert___at_Lean_AbstractTypeContext_InstantiateExprMVars_checkCache___spec__3(x_605, x_580, x_600);
x_607 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_607, 0, x_604);
lean_ctor_set(x_607, 1, x_606);
x_16 = x_600;
x_17 = x_607;
goto block_26;
}
}
else
{
lean_object* x_608; 
lean_dec(x_580);
lean_dec(x_1);
x_608 = lean_ctor_get(x_597, 0);
lean_inc(x_608);
lean_dec(x_597);
x_16 = x_608;
x_17 = x_3;
goto block_26;
}
}
}
case 11:
{
lean_object* x_609; uint8_t x_610; 
x_609 = lean_ctor_get(x_2, 2);
lean_inc(x_609);
x_610 = lean_expr_has_expr_mvar(x_609);
if (x_610 == 0)
{
uint8_t x_611; 
x_611 = lean_expr_has_level_mvar(x_609);
if (x_611 == 0)
{
lean_dec(x_1);
x_27 = x_609;
x_28 = x_3;
goto block_37;
}
else
{
lean_object* x_612; lean_object* x_613; 
x_612 = lean_ctor_get(x_3, 1);
lean_inc(x_612);
x_613 = l_HashMapImp_find___at_Lean_AbstractTypeContext_InstantiateExprMVars_checkCache___spec__1(x_612, x_609);
lean_dec(x_612);
if (lean_obj_tag(x_613) == 0)
{
lean_object* x_614; lean_object* x_615; lean_object* x_616; uint8_t x_617; 
lean_inc(x_609);
x_614 = l_Lean_AbstractTypeContext_InstantiateExprMVars_main___main___rarg(x_1, x_609, x_3);
x_615 = lean_ctor_get(x_614, 1);
lean_inc(x_615);
x_616 = lean_ctor_get(x_614, 0);
lean_inc(x_616);
lean_dec(x_614);
x_617 = !lean_is_exclusive(x_615);
if (x_617 == 0)
{
lean_object* x_618; lean_object* x_619; 
x_618 = lean_ctor_get(x_615, 1);
lean_inc(x_616);
x_619 = l_HashMapImp_insert___at_Lean_AbstractTypeContext_InstantiateExprMVars_checkCache___spec__3(x_618, x_609, x_616);
lean_ctor_set(x_615, 1, x_619);
x_27 = x_616;
x_28 = x_615;
goto block_37;
}
else
{
lean_object* x_620; lean_object* x_621; lean_object* x_622; lean_object* x_623; 
x_620 = lean_ctor_get(x_615, 0);
x_621 = lean_ctor_get(x_615, 1);
lean_inc(x_621);
lean_inc(x_620);
lean_dec(x_615);
lean_inc(x_616);
x_622 = l_HashMapImp_insert___at_Lean_AbstractTypeContext_InstantiateExprMVars_checkCache___spec__3(x_621, x_609, x_616);
x_623 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_623, 0, x_620);
lean_ctor_set(x_623, 1, x_622);
x_27 = x_616;
x_28 = x_623;
goto block_37;
}
}
else
{
lean_object* x_624; 
lean_dec(x_609);
lean_dec(x_1);
x_624 = lean_ctor_get(x_613, 0);
lean_inc(x_624);
lean_dec(x_613);
x_27 = x_624;
x_28 = x_3;
goto block_37;
}
}
}
else
{
lean_object* x_625; lean_object* x_626; 
x_625 = lean_ctor_get(x_3, 1);
lean_inc(x_625);
x_626 = l_HashMapImp_find___at_Lean_AbstractTypeContext_InstantiateExprMVars_checkCache___spec__1(x_625, x_609);
lean_dec(x_625);
if (lean_obj_tag(x_626) == 0)
{
lean_object* x_627; lean_object* x_628; lean_object* x_629; uint8_t x_630; 
lean_inc(x_609);
x_627 = l_Lean_AbstractTypeContext_InstantiateExprMVars_main___main___rarg(x_1, x_609, x_3);
x_628 = lean_ctor_get(x_627, 1);
lean_inc(x_628);
x_629 = lean_ctor_get(x_627, 0);
lean_inc(x_629);
lean_dec(x_627);
x_630 = !lean_is_exclusive(x_628);
if (x_630 == 0)
{
lean_object* x_631; lean_object* x_632; 
x_631 = lean_ctor_get(x_628, 1);
lean_inc(x_629);
x_632 = l_HashMapImp_insert___at_Lean_AbstractTypeContext_InstantiateExprMVars_checkCache___spec__3(x_631, x_609, x_629);
lean_ctor_set(x_628, 1, x_632);
x_27 = x_629;
x_28 = x_628;
goto block_37;
}
else
{
lean_object* x_633; lean_object* x_634; lean_object* x_635; lean_object* x_636; 
x_633 = lean_ctor_get(x_628, 0);
x_634 = lean_ctor_get(x_628, 1);
lean_inc(x_634);
lean_inc(x_633);
lean_dec(x_628);
lean_inc(x_629);
x_635 = l_HashMapImp_insert___at_Lean_AbstractTypeContext_InstantiateExprMVars_checkCache___spec__3(x_634, x_609, x_629);
x_636 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_636, 0, x_633);
lean_ctor_set(x_636, 1, x_635);
x_27 = x_629;
x_28 = x_636;
goto block_37;
}
}
else
{
lean_object* x_637; 
lean_dec(x_609);
lean_dec(x_1);
x_637 = lean_ctor_get(x_626, 0);
lean_inc(x_637);
lean_dec(x_626);
x_27 = x_637;
x_28 = x_3;
goto block_37;
}
}
}
default: 
{
lean_object* x_638; 
lean_dec(x_1);
x_638 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_638, 0, x_2);
lean_ctor_set(x_638, 1, x_3);
return x_638;
}
}
block_15:
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_4);
x_8 = l_HashMapImp_insert___at_Lean_AbstractTypeContext_InstantiateExprMVars_checkCache___spec__3(x_7, x_2, x_4);
lean_ctor_set(x_5, 1, x_8);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_4);
lean_ctor_set(x_9, 1, x_5);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_5, 0);
x_11 = lean_ctor_get(x_5, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_5);
lean_inc(x_4);
x_12 = l_HashMapImp_insert___at_Lean_AbstractTypeContext_InstantiateExprMVars_checkCache___spec__3(x_11, x_2, x_4);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_4);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
block_26:
{
if (lean_obj_tag(x_2) == 10)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_expr_update_mdata(x_2, x_16);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_16);
lean_dec(x_2);
x_20 = l_Lean_Expr_constName___closed__1;
x_21 = lean_unsigned_to_nat(372u);
x_22 = lean_unsigned_to_nat(15u);
x_23 = l_Lean_Expr_updateMData_x21___closed__1;
x_24 = l_panicWithPos___at_Lean_Expr_bindingDomain___spec__1(x_20, x_21, x_22, x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_17);
return x_25;
}
}
block_37:
{
if (lean_obj_tag(x_2) == 11)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_expr_update_proj(x_2, x_27);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_27);
lean_dec(x_2);
x_31 = l_Lean_Expr_constName___closed__1;
x_32 = lean_unsigned_to_nat(377u);
x_33 = lean_unsigned_to_nat(16u);
x_34 = l_Lean_Expr_updateProj_x21___closed__1;
x_35 = l_panicWithPos___at_Lean_Expr_bindingDomain___spec__1(x_31, x_32, x_33, x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_28);
return x_36;
}
}
}
}
lean_object* l_Lean_AbstractTypeContext_InstantiateExprMVars_main___main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_AbstractTypeContext_InstantiateExprMVars_main___main___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_AbstractTypeContext_InstantiateExprMVars_main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_AbstractTypeContext_InstantiateExprMVars_main___main___rarg(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_AbstractTypeContext_InstantiateExprMVars_main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_AbstractTypeContext_InstantiateExprMVars_main___rarg), 3, 0);
return x_2;
}
}
lean_object* l_mkHashMap___at_Lean_AbstractTypeContext_instantiateExprMVars___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_mkHashMapImp___rarg(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_AbstractTypeContext_instantiateExprMVars___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = l_mkHashMapImp___rarg(x_1);
return x_2;
}
}
lean_object* l_Lean_AbstractTypeContext_instantiateExprMVars___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = l_Lean_AbstractTypeContext_instantiateExprMVars___rarg___closed__1;
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
x_6 = l_Lean_AbstractTypeContext_InstantiateExprMVars_main___main___rarg(x_1, x_2, x_5);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_6, 1);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec(x_8);
lean_ctor_set(x_6, 1, x_9);
return x_6;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_6, 0);
x_11 = lean_ctor_get(x_6, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_6);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
}
lean_object* l_Lean_AbstractTypeContext_instantiateExprMVars(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_AbstractTypeContext_instantiateExprMVars___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Init_Lean_TypeContext_1__getOptions___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 3);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
return x_5;
}
}
lean_object* l___private_Init_Lean_TypeContext_1__getOptions(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_Init_Lean_TypeContext_1__getOptions___rarg___boxed), 2, 0);
return x_3;
}
}
lean_object* l___private_Init_Lean_TypeContext_1__getOptions___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Init_Lean_TypeContext_1__getOptions___rarg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l___private_Init_Lean_TypeContext_2__getTraceState___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 3);
lean_inc(x_2);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l___private_Init_Lean_TypeContext_2__getTraceState(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l___private_Init_Lean_TypeContext_2__getTraceState___rarg), 1, 0);
return x_4;
}
}
lean_object* l___private_Init_Lean_TypeContext_2__getTraceState___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Lean_TypeContext_2__getTraceState(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
lean_object* l_Lean_AbstractTypeContext_tracer___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_3, 3);
x_6 = lean_apply_1(x_1, x_5);
lean_ctor_set(x_3, 3, x_6);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_3);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_9 = lean_ctor_get(x_3, 0);
x_10 = lean_ctor_get(x_3, 1);
x_11 = lean_ctor_get(x_3, 2);
x_12 = lean_ctor_get(x_3, 3);
x_13 = lean_ctor_get_uint8(x_3, sizeof(void*)*5);
x_14 = lean_ctor_get(x_3, 4);
lean_inc(x_14);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_3);
x_15 = lean_apply_1(x_1, x_12);
x_16 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_16, 0, x_9);
lean_ctor_set(x_16, 1, x_10);
lean_ctor_set(x_16, 2, x_11);
lean_ctor_set(x_16, 3, x_15);
lean_ctor_set(x_16, 4, x_14);
lean_ctor_set_uint8(x_16, sizeof(void*)*5, x_13);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
}
lean_object* _init_l_Lean_AbstractTypeContext_tracer___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Init_Lean_TypeContext_2__getTraceState___boxed), 3, 2);
lean_closure_set(x_1, 0, lean_box(0));
lean_closure_set(x_1, 1, lean_box(0));
return x_1;
}
}
lean_object* _init_l_Lean_AbstractTypeContext_tracer___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Init_Lean_TypeContext_1__getOptions___rarg___boxed), 2, 0);
return x_1;
}
}
lean_object* _init_l_Lean_AbstractTypeContext_tracer___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_AbstractTypeContext_tracer___lambda__1___boxed), 3, 0);
return x_1;
}
}
lean_object* _init_l_Lean_AbstractTypeContext_tracer___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_AbstractTypeContext_tracer___closed__2;
x_2 = l_Lean_AbstractTypeContext_tracer___closed__3;
x_3 = l_Lean_AbstractTypeContext_tracer___closed__1;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* l_Lean_AbstractTypeContext_tracer(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_AbstractTypeContext_tracer___closed__4;
return x_3;
}
}
lean_object* l_Lean_AbstractTypeContext_tracer___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_AbstractTypeContext_tracer___lambda__1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
uint8_t l_Lean_metavarContextIsAbstractMetavarContext___lambda__1(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = 1;
return x_2;
}
}
lean_object* _init_l_Lean_metavarContextIsAbstractMetavarContext___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_metavarContextIsAbstractMetavarContext___lambda__1___boxed), 1, 0);
return x_1;
}
}
lean_object* _init_l_Lean_metavarContextIsAbstractMetavarContext___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(lean_metavar_ctx_get_level_assignment), 2, 0);
return x_1;
}
}
lean_object* _init_l_Lean_metavarContextIsAbstractMetavarContext___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(lean_metavar_ctx_assign_level), 3, 0);
return x_1;
}
}
lean_object* _init_l_Lean_metavarContextIsAbstractMetavarContext___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(lean_metavar_ctx_get_expr_assignment), 2, 0);
return x_1;
}
}
lean_object* _init_l_Lean_metavarContextIsAbstractMetavarContext___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(lean_metavar_ctx_assign_expr), 3, 0);
return x_1;
}
}
lean_object* _init_l_Lean_metavarContextIsAbstractMetavarContext___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_MetavarContext_getExprMVarLCtx), 2, 0);
return x_1;
}
}
lean_object* _init_l_Lean_metavarContextIsAbstractMetavarContext___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_MetavarContext_getExprMVarType), 2, 0);
return x_1;
}
}
lean_object* _init_l_Lean_metavarContextIsAbstractMetavarContext___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(lean_metavar_ctx_assign_delayed), 5, 0);
return x_1;
}
}
lean_object* _init_l_Lean_metavarContextIsAbstractMetavarContext___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(lean_metavar_ctx_get_delayed_assignment), 2, 0);
return x_1;
}
}
lean_object* _init_l_Lean_metavarContextIsAbstractMetavarContext___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(lean_metavar_ctx_erase_delayed), 2, 0);
return x_1;
}
}
lean_object* _init_l_Lean_metavarContextIsAbstractMetavarContext___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_1 = l_Lean_MetavarContext_mkMetavarContext___closed__1;
x_2 = l_Lean_metavarContextIsAbstractMetavarContext___closed__1;
x_3 = l_Lean_metavarContextIsAbstractMetavarContext___closed__2;
x_4 = l_Lean_metavarContextIsAbstractMetavarContext___closed__3;
x_5 = l_Lean_metavarContextIsAbstractMetavarContext___closed__4;
x_6 = l_Lean_metavarContextIsAbstractMetavarContext___closed__5;
x_7 = l_Lean_metavarContextIsAbstractMetavarContext___closed__6;
x_8 = l_Lean_metavarContextIsAbstractMetavarContext___closed__7;
x_9 = 0;
x_10 = l_Lean_metavarContextIsAbstractMetavarContext___closed__8;
x_11 = l_Lean_metavarContextIsAbstractMetavarContext___closed__9;
x_12 = l_Lean_metavarContextIsAbstractMetavarContext___closed__10;
x_13 = lean_alloc_ctor(0, 12, 1);
lean_ctor_set(x_13, 0, x_1);
lean_ctor_set(x_13, 1, x_2);
lean_ctor_set(x_13, 2, x_3);
lean_ctor_set(x_13, 3, x_4);
lean_ctor_set(x_13, 4, x_2);
lean_ctor_set(x_13, 5, x_5);
lean_ctor_set(x_13, 6, x_6);
lean_ctor_set(x_13, 7, x_7);
lean_ctor_set(x_13, 8, x_8);
lean_ctor_set(x_13, 9, x_10);
lean_ctor_set(x_13, 10, x_11);
lean_ctor_set(x_13, 11, x_12);
lean_ctor_set_uint8(x_13, sizeof(void*)*12, x_9);
return x_13;
}
}
lean_object* _init_l_Lean_metavarContextIsAbstractMetavarContext() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_metavarContextIsAbstractMetavarContext___closed__11;
return x_1;
}
}
lean_object* l_Lean_metavarContextIsAbstractMetavarContext___lambda__1___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_metavarContextIsAbstractMetavarContext___lambda__1(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* initialize_Init_Control_Reader(lean_object*);
lean_object* initialize_Init_Lean_NameGenerator(lean_object*);
lean_object* initialize_Init_Lean_Environment(lean_object*);
lean_object* initialize_Init_Lean_LocalContext(lean_object*);
lean_object* initialize_Init_Lean_Trace(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Lean_TypeContext(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Control_Reader(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_NameGenerator(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Environment(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_LocalContext(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Trace(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_TCState_backtrackable___closed__1 = _init_l_Lean_TCState_backtrackable___closed__1();
lean_mark_persistent(l_Lean_TCState_backtrackable___closed__1);
l_Lean_TCState_backtrackable___closed__2 = _init_l_Lean_TCState_backtrackable___closed__2();
lean_mark_persistent(l_Lean_TCState_backtrackable___closed__2);
l_Lean_TCState_backtrackable___closed__3 = _init_l_Lean_TCState_backtrackable___closed__3();
lean_mark_persistent(l_Lean_TCState_backtrackable___closed__3);
l_Lean_AbstractTypeContext_instantiateExprMVars___rarg___closed__1 = _init_l_Lean_AbstractTypeContext_instantiateExprMVars___rarg___closed__1();
lean_mark_persistent(l_Lean_AbstractTypeContext_instantiateExprMVars___rarg___closed__1);
l_Lean_AbstractTypeContext_tracer___closed__1 = _init_l_Lean_AbstractTypeContext_tracer___closed__1();
lean_mark_persistent(l_Lean_AbstractTypeContext_tracer___closed__1);
l_Lean_AbstractTypeContext_tracer___closed__2 = _init_l_Lean_AbstractTypeContext_tracer___closed__2();
lean_mark_persistent(l_Lean_AbstractTypeContext_tracer___closed__2);
l_Lean_AbstractTypeContext_tracer___closed__3 = _init_l_Lean_AbstractTypeContext_tracer___closed__3();
lean_mark_persistent(l_Lean_AbstractTypeContext_tracer___closed__3);
l_Lean_AbstractTypeContext_tracer___closed__4 = _init_l_Lean_AbstractTypeContext_tracer___closed__4();
lean_mark_persistent(l_Lean_AbstractTypeContext_tracer___closed__4);
l_Lean_metavarContextIsAbstractMetavarContext___closed__1 = _init_l_Lean_metavarContextIsAbstractMetavarContext___closed__1();
lean_mark_persistent(l_Lean_metavarContextIsAbstractMetavarContext___closed__1);
l_Lean_metavarContextIsAbstractMetavarContext___closed__2 = _init_l_Lean_metavarContextIsAbstractMetavarContext___closed__2();
lean_mark_persistent(l_Lean_metavarContextIsAbstractMetavarContext___closed__2);
l_Lean_metavarContextIsAbstractMetavarContext___closed__3 = _init_l_Lean_metavarContextIsAbstractMetavarContext___closed__3();
lean_mark_persistent(l_Lean_metavarContextIsAbstractMetavarContext___closed__3);
l_Lean_metavarContextIsAbstractMetavarContext___closed__4 = _init_l_Lean_metavarContextIsAbstractMetavarContext___closed__4();
lean_mark_persistent(l_Lean_metavarContextIsAbstractMetavarContext___closed__4);
l_Lean_metavarContextIsAbstractMetavarContext___closed__5 = _init_l_Lean_metavarContextIsAbstractMetavarContext___closed__5();
lean_mark_persistent(l_Lean_metavarContextIsAbstractMetavarContext___closed__5);
l_Lean_metavarContextIsAbstractMetavarContext___closed__6 = _init_l_Lean_metavarContextIsAbstractMetavarContext___closed__6();
lean_mark_persistent(l_Lean_metavarContextIsAbstractMetavarContext___closed__6);
l_Lean_metavarContextIsAbstractMetavarContext___closed__7 = _init_l_Lean_metavarContextIsAbstractMetavarContext___closed__7();
lean_mark_persistent(l_Lean_metavarContextIsAbstractMetavarContext___closed__7);
l_Lean_metavarContextIsAbstractMetavarContext___closed__8 = _init_l_Lean_metavarContextIsAbstractMetavarContext___closed__8();
lean_mark_persistent(l_Lean_metavarContextIsAbstractMetavarContext___closed__8);
l_Lean_metavarContextIsAbstractMetavarContext___closed__9 = _init_l_Lean_metavarContextIsAbstractMetavarContext___closed__9();
lean_mark_persistent(l_Lean_metavarContextIsAbstractMetavarContext___closed__9);
l_Lean_metavarContextIsAbstractMetavarContext___closed__10 = _init_l_Lean_metavarContextIsAbstractMetavarContext___closed__10();
lean_mark_persistent(l_Lean_metavarContextIsAbstractMetavarContext___closed__10);
l_Lean_metavarContextIsAbstractMetavarContext___closed__11 = _init_l_Lean_metavarContextIsAbstractMetavarContext___closed__11();
lean_mark_persistent(l_Lean_metavarContextIsAbstractMetavarContext___closed__11);
l_Lean_metavarContextIsAbstractMetavarContext = _init_l_Lean_metavarContextIsAbstractMetavarContext();
lean_mark_persistent(l_Lean_metavarContextIsAbstractMetavarContext);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
