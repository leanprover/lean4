// Lean compiler output
// Module: Init.Lean.Util.Closure
// Imports: Init.Default Init.Lean.MetavarContext Init.Lean.Environment Init.Lean.Util.FoldConsts
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
lean_object* l_Lean_Closure_mkNewLevelParam___closed__1;
lean_object* lean_expr_update_forall(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Closure_mkNewLevelParam___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Closure_mkNewLevelParam___closed__2;
lean_object* l_Lean_Closure_mkLetDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_HashMapImp_find_x3f___at_Lean_Closure_visitExpr___spec__1(lean_object*, lean_object*);
lean_object* l_HashMapImp_find_x3f___at_Lean_Closure_visitLevel___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Closure_getUserName(lean_object*, lean_object*, lean_object*);
lean_object* l_HashMapImp_insert___at_Lean_Closure_visitExpr___spec__3(lean_object*, lean_object*, lean_object*);
lean_object* l_HashMapImp_find_x3f___at_Lean_Closure_visitExpr___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Closure_collectLevel___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Closure_mkLetDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_update_mdata(lean_object*, lean_object*);
lean_object* l_List_mapM___main___at_Lean_Closure_collectExprAux___main___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_local_ctx_mk_let_decl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_updateMData_x21___closed__2;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
extern lean_object* l_Array_empty___closed__1;
uint8_t l_Lean_Level_hasMVar(lean_object*);
extern lean_object* l_Lean_MetavarContext_getDecl___closed__2;
uint8_t l_AssocList_contains___main___at_Lean_Closure_visitExpr___spec__4(lean_object*, lean_object*);
size_t l_Lean_Level_hash(lean_object*);
lean_object* l_Lean_Closure_collectLevelAux___main___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_AssocList_contains___main___at_Lean_Closure_visitLevel___spec__4___boxed(lean_object*, lean_object*);
extern lean_object* l_Lean_Level_Inhabited;
uint8_t l_Lean_Level_hasParam(lean_object*);
lean_object* l_HashMapImp_find_x3f___at_Lean_Closure_visitLevel___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Closure_mkFreshFVarId(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_AssocList_find_x3f___main___at_Lean_Closure_visitLevel___spec__2___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Closure_collectLevel(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Level_updateMax_x21___closed__2;
extern lean_object* l_Lean_Expr_updateLambdaE_x21___closed__1;
uint32_t l_UInt32_add(uint32_t, uint32_t);
uint8_t l_Lean_Environment_hasUnsafe(lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_getFVars(lean_object*);
extern lean_object* l_Lean_LocalContext_Inhabited___closed__2;
lean_object* l_Lean_mkAuxDefinition(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_mkHashMap___at_Lean_Closure_mkClosure___spec__3(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_Closure_mkClosure___closed__4;
uint8_t l_Lean_Expr_hasLevelParam(lean_object*);
lean_object* l_Lean_Closure_mkNextUserName___rarg(lean_object*);
lean_object* l_AssocList_find_x3f___main___at_Lean_Closure_visitExpr___spec__2(lean_object*, lean_object*);
lean_object* lean_level_update_max(lean_object*, lean_object*, lean_object*);
lean_object* l_AssocList_find_x3f___main___at_Lean_Closure_visitExpr___spec__2___boxed(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_appendIndexAfter(lean_object*, lean_object*);
lean_object* l_AssocList_foldlM___main___at_Lean_Closure_visitExpr___spec__7(lean_object*, lean_object*);
lean_object* l_Lean_Closure_collectLevelAux___main(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Closure_mkClosure___closed__5;
lean_object* l_HashMapImp_expand___at_Lean_Closure_visitExpr___spec__5(lean_object*, lean_object*);
size_t l_Lean_Expr_hash(lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Lean_Closure_mkFreshFVarId___rarg(lean_object*);
lean_object* l_Lean_Closure_mkClosure___closed__6;
lean_object* l_HashMapImp_moveEntries___main___at_Lean_Closure_visitLevel___spec__6(lean_object*, lean_object*, lean_object*);
size_t lean_usize_modn(size_t, lean_object*);
lean_object* l_Lean_getMaxHeight(lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_updateApp_x21___closed__1;
lean_object* l_Lean_Closure_collectLevelAux(lean_object*, lean_object*, lean_object*);
lean_object* l_HashMapImp_moveEntries___main___at_Lean_Closure_visitExpr___spec__6(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Closure_mkClosure___closed__3;
lean_object* l_mkHashMapImp___rarg(lean_object*);
lean_object* lean_expr_update_let(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Closure_collectExprAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
lean_object* l_Lean_Closure_collectLevelAux___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_Data_binderInfo(uint64_t);
lean_object* l_Lean_Closure_mkLocalDecl(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_update_proj(lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_updateProj_x21___closed__2;
lean_object* lean_local_ctx_mk_local_decl(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_HashMapImp_insert___at_Lean_Closure_visitLevel___spec__3(lean_object*, lean_object*, lean_object*);
lean_object* l_AssocList_replace___main___at_Lean_Closure_visitExpr___spec__8(lean_object*, lean_object*, lean_object*);
lean_object* l_AssocList_find_x3f___main___at_Lean_Closure_visitLevel___spec__2(lean_object*, lean_object*);
lean_object* lean_level_update_imax(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Closure_mkNextUserName(lean_object*);
uint8_t lean_expr_equal(lean_object*, lean_object*);
lean_object* lean_expr_update_sort(lean_object*, lean_object*);
lean_object* l_List_mapM___main___at_Lean_Closure_collectExprAux___main___spec__1(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_Closure_mkClosure___closed__1;
lean_object* l_Lean_Environment_addAndCompile(lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_Lean_Closure_mkNextUserName___rarg___closed__1;
lean_object* l_Lean_Closure_mkClosure(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Level_updateSucc_x21___closed__2;
lean_object* l_Lean_LocalContext_mkLambda(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Closure_mkClosure___closed__2;
lean_object* l_Lean_Closure_mkNextUserName___rarg___closed__2;
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_metavar_ctx_find_decl(lean_object*, lean_object*);
lean_object* l_AssocList_foldlM___main___at_Lean_Closure_visitLevel___spec__7(lean_object*, lean_object*);
lean_object* l_HashMapImp_expand___at_Lean_Closure_visitLevel___spec__5(lean_object*, lean_object*);
lean_object* l_ShareCommonT_withShareCommon___at_Lean_Closure_mkClosure___spec__1(lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_updateLet_x21___closed__1;
lean_object* lean_expr_update_lambda(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* lean_level_update_succ(lean_object*, lean_object*);
extern lean_object* l_Lean_LocalContext_get_x21___closed__1;
lean_object* l_Array_toList___rarg(lean_object*);
extern lean_object* l_Lean_Expr_Inhabited;
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_Closure_mkFreshFVarId___boxed(lean_object*);
lean_object* l_Lean_Closure_mkLocalDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_mkHashMap___at_Lean_Closure_mkClosure___spec__2(lean_object*);
lean_object* l_Lean_Closure_collectExprAux___main(lean_object*, lean_object*, lean_object*);
extern lean_object* l_ShareCommon_State_empty;
lean_object* l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_local_ctx_find(lean_object*, lean_object*);
lean_object* l_Lean_mkLevelParam(lean_object*);
lean_object* l_Lean_LocalContext_mkForall(lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_update_app(lean_object*, lean_object*, lean_object*);
lean_object* l_AssocList_replace___main___at_Lean_Closure_visitLevel___spec__8(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Closure_mkNextUserName___boxed(lean_object*);
lean_object* lean_state_sharecommon(lean_object*, lean_object*);
uint8_t lean_level_eq(lean_object*, lean_object*);
lean_object* l_Lean_Closure_visitExpr(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
lean_object* l_Lean_Closure_mkNewLevelParam(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Closure_getUserName___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Closure_collectExpr(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_updateForallE_x21___closed__1;
lean_object* lean_name_mk_numeral(lean_object*, lean_object*);
lean_object* lean_expr_update_const(lean_object*, lean_object*);
extern lean_object* l_Lean_Level_updateIMax_x21___closed__2;
lean_object* l_Lean_Closure_visitLevel(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_AssocList_contains___main___at_Lean_Closure_visitLevel___spec__4(lean_object*, lean_object*);
lean_object* l_AssocList_contains___main___at_Lean_Closure_visitExpr___spec__4___boxed(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_mkAuxDefinition___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_AssocList_find_x3f___main___at_Lean_Closure_visitLevel___spec__2(lean_object* x_1, lean_object* x_2) {
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
x_7 = lean_level_eq(x_4, x_1);
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
lean_object* l_HashMapImp_find_x3f___at_Lean_Closure_visitLevel___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; size_t x_5; size_t x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
x_5 = l_Lean_Level_hash(x_2);
x_6 = lean_usize_modn(x_5, x_4);
lean_dec(x_4);
x_7 = lean_array_uget(x_3, x_6);
x_8 = l_AssocList_find_x3f___main___at_Lean_Closure_visitLevel___spec__2(x_2, x_7);
lean_dec(x_7);
return x_8;
}
}
uint8_t l_AssocList_contains___main___at_Lean_Closure_visitLevel___spec__4(lean_object* x_1, lean_object* x_2) {
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
x_6 = lean_level_eq(x_4, x_1);
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
lean_object* l_AssocList_foldlM___main___at_Lean_Closure_visitLevel___spec__7(lean_object* x_1, lean_object* x_2) {
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
x_7 = l_Lean_Level_hash(x_4);
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
x_16 = l_Lean_Level_hash(x_12);
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
lean_object* l_HashMapImp_moveEntries___main___at_Lean_Closure_visitLevel___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_AssocList_foldlM___main___at_Lean_Closure_visitLevel___spec__7(x_3, x_6);
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
lean_object* l_HashMapImp_expand___at_Lean_Closure_visitLevel___spec__5(lean_object* x_1, lean_object* x_2) {
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
x_9 = l_HashMapImp_moveEntries___main___at_Lean_Closure_visitLevel___spec__6(x_8, x_2, x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
lean_object* l_AssocList_replace___main___at_Lean_Closure_visitLevel___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_8 = lean_level_eq(x_5, x_1);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = l_AssocList_replace___main___at_Lean_Closure_visitLevel___spec__8(x_1, x_2, x_7);
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
x_13 = lean_level_eq(x_10, x_1);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = l_AssocList_replace___main___at_Lean_Closure_visitLevel___spec__8(x_1, x_2, x_12);
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
lean_object* l_HashMapImp_insert___at_Lean_Closure_visitLevel___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_8 = l_Lean_Level_hash(x_2);
x_9 = lean_usize_modn(x_8, x_7);
x_10 = lean_array_uget(x_6, x_9);
x_11 = l_AssocList_contains___main___at_Lean_Closure_visitLevel___spec__4(x_2, x_10);
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
x_17 = l_HashMapImp_expand___at_Lean_Closure_visitLevel___spec__5(x_13, x_15);
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
x_18 = l_AssocList_replace___main___at_Lean_Closure_visitLevel___spec__8(x_2, x_3, x_10);
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
x_23 = l_Lean_Level_hash(x_2);
x_24 = lean_usize_modn(x_23, x_22);
x_25 = lean_array_uget(x_21, x_24);
x_26 = l_AssocList_contains___main___at_Lean_Closure_visitLevel___spec__4(x_2, x_25);
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
x_32 = l_HashMapImp_expand___at_Lean_Closure_visitLevel___spec__5(x_28, x_30);
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
x_34 = l_AssocList_replace___main___at_Lean_Closure_visitLevel___spec__8(x_2, x_3, x_25);
x_35 = lean_array_uset(x_21, x_24, x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_20);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
lean_object* l_Lean_Closure_visitLevel(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_49; 
x_49 = l_Lean_Level_hasMVar(x_2);
if (x_49 == 0)
{
uint8_t x_50; 
x_50 = l_Lean_Level_hasParam(x_2);
if (x_50 == 0)
{
lean_object* x_51; 
lean_dec(x_3);
lean_dec(x_1);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_2);
lean_ctor_set(x_51, 1, x_4);
return x_51;
}
else
{
lean_object* x_52; 
x_52 = lean_box(0);
x_5 = x_52;
goto block_48;
}
}
else
{
lean_object* x_53; 
x_53 = lean_box(0);
x_5 = x_53;
goto block_48;
}
block_48:
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_5);
x_6 = lean_ctor_get(x_4, 2);
lean_inc(x_6);
x_7 = l_HashMapImp_find_x3f___at_Lean_Closure_visitLevel___spec__1(x_6, x_2);
lean_dec(x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
lean_inc(x_2);
x_8 = lean_apply_3(x_1, x_2, x_3, x_4);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_8, 1);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_8, 0);
x_13 = lean_ctor_get(x_10, 2);
lean_inc(x_12);
x_14 = l_HashMapImp_insert___at_Lean_Closure_visitLevel___spec__3(x_13, x_2, x_12);
lean_ctor_set(x_10, 2, x_14);
return x_8;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_15 = lean_ctor_get(x_8, 0);
x_16 = lean_ctor_get(x_10, 0);
x_17 = lean_ctor_get(x_10, 1);
x_18 = lean_ctor_get(x_10, 2);
x_19 = lean_ctor_get(x_10, 3);
x_20 = lean_ctor_get(x_10, 4);
x_21 = lean_ctor_get(x_10, 5);
x_22 = lean_ctor_get(x_10, 6);
x_23 = lean_ctor_get(x_10, 7);
x_24 = lean_ctor_get(x_10, 8);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_10);
lean_inc(x_15);
x_25 = l_HashMapImp_insert___at_Lean_Closure_visitLevel___spec__3(x_18, x_2, x_15);
x_26 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_26, 0, x_16);
lean_ctor_set(x_26, 1, x_17);
lean_ctor_set(x_26, 2, x_25);
lean_ctor_set(x_26, 3, x_19);
lean_ctor_set(x_26, 4, x_20);
lean_ctor_set(x_26, 5, x_21);
lean_ctor_set(x_26, 6, x_22);
lean_ctor_set(x_26, 7, x_23);
lean_ctor_set(x_26, 8, x_24);
lean_ctor_set(x_8, 1, x_26);
return x_8;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_27 = lean_ctor_get(x_8, 1);
x_28 = lean_ctor_get(x_8, 0);
lean_inc(x_27);
lean_inc(x_28);
lean_dec(x_8);
x_29 = lean_ctor_get(x_27, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
x_31 = lean_ctor_get(x_27, 2);
lean_inc(x_31);
x_32 = lean_ctor_get(x_27, 3);
lean_inc(x_32);
x_33 = lean_ctor_get(x_27, 4);
lean_inc(x_33);
x_34 = lean_ctor_get(x_27, 5);
lean_inc(x_34);
x_35 = lean_ctor_get(x_27, 6);
lean_inc(x_35);
x_36 = lean_ctor_get(x_27, 7);
lean_inc(x_36);
x_37 = lean_ctor_get(x_27, 8);
lean_inc(x_37);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 lean_ctor_release(x_27, 1);
 lean_ctor_release(x_27, 2);
 lean_ctor_release(x_27, 3);
 lean_ctor_release(x_27, 4);
 lean_ctor_release(x_27, 5);
 lean_ctor_release(x_27, 6);
 lean_ctor_release(x_27, 7);
 lean_ctor_release(x_27, 8);
 x_38 = x_27;
} else {
 lean_dec_ref(x_27);
 x_38 = lean_box(0);
}
lean_inc(x_28);
x_39 = l_HashMapImp_insert___at_Lean_Closure_visitLevel___spec__3(x_31, x_2, x_28);
if (lean_is_scalar(x_38)) {
 x_40 = lean_alloc_ctor(0, 9, 0);
} else {
 x_40 = x_38;
}
lean_ctor_set(x_40, 0, x_29);
lean_ctor_set(x_40, 1, x_30);
lean_ctor_set(x_40, 2, x_39);
lean_ctor_set(x_40, 3, x_32);
lean_ctor_set(x_40, 4, x_33);
lean_ctor_set(x_40, 5, x_34);
lean_ctor_set(x_40, 6, x_35);
lean_ctor_set(x_40, 7, x_36);
lean_ctor_set(x_40, 8, x_37);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_28);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
else
{
uint8_t x_42; 
lean_dec(x_2);
x_42 = !lean_is_exclusive(x_8);
if (x_42 == 0)
{
return x_8;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_8, 0);
x_44 = lean_ctor_get(x_8, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_8);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
else
{
lean_object* x_46; lean_object* x_47; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_46 = lean_ctor_get(x_7, 0);
lean_inc(x_46);
lean_dec(x_7);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_4);
return x_47;
}
}
}
}
lean_object* l_AssocList_find_x3f___main___at_Lean_Closure_visitLevel___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_AssocList_find_x3f___main___at_Lean_Closure_visitLevel___spec__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_HashMapImp_find_x3f___at_Lean_Closure_visitLevel___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_HashMapImp_find_x3f___at_Lean_Closure_visitLevel___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_AssocList_contains___main___at_Lean_Closure_visitLevel___spec__4___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_AssocList_contains___main___at_Lean_Closure_visitLevel___spec__4(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* _init_l_Lean_Closure_mkNewLevelParam___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("u");
return x_1;
}
}
lean_object* _init_l_Lean_Closure_mkNewLevelParam___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Closure_mkNewLevelParam___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Closure_mkNewLevelParam(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_5 = lean_ctor_get(x_3, 4);
x_6 = lean_ctor_get(x_3, 5);
x_7 = lean_ctor_get(x_3, 6);
x_8 = l_Lean_Closure_mkNewLevelParam___closed__2;
lean_inc(x_6);
x_9 = l_Lean_Name_appendIndexAfter(x_8, x_6);
lean_inc(x_9);
x_10 = lean_array_push(x_5, x_9);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_6, x_11);
lean_dec(x_6);
x_13 = lean_array_push(x_7, x_1);
lean_ctor_set(x_3, 6, x_13);
lean_ctor_set(x_3, 5, x_12);
lean_ctor_set(x_3, 4, x_10);
x_14 = l_Lean_mkLevelParam(x_9);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_3);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_16 = lean_ctor_get(x_3, 0);
x_17 = lean_ctor_get(x_3, 1);
x_18 = lean_ctor_get(x_3, 2);
x_19 = lean_ctor_get(x_3, 3);
x_20 = lean_ctor_get(x_3, 4);
x_21 = lean_ctor_get(x_3, 5);
x_22 = lean_ctor_get(x_3, 6);
x_23 = lean_ctor_get(x_3, 7);
x_24 = lean_ctor_get(x_3, 8);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_3);
x_25 = l_Lean_Closure_mkNewLevelParam___closed__2;
lean_inc(x_21);
x_26 = l_Lean_Name_appendIndexAfter(x_25, x_21);
lean_inc(x_26);
x_27 = lean_array_push(x_20, x_26);
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_nat_add(x_21, x_28);
lean_dec(x_21);
x_30 = lean_array_push(x_22, x_1);
x_31 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_31, 0, x_16);
lean_ctor_set(x_31, 1, x_17);
lean_ctor_set(x_31, 2, x_18);
lean_ctor_set(x_31, 3, x_19);
lean_ctor_set(x_31, 4, x_27);
lean_ctor_set(x_31, 5, x_29);
lean_ctor_set(x_31, 6, x_30);
lean_ctor_set(x_31, 7, x_23);
lean_ctor_set(x_31, 8, x_24);
x_32 = l_Lean_mkLevelParam(x_26);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
return x_33;
}
}
}
lean_object* l_Lean_Closure_mkNewLevelParam___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Closure_mkNewLevelParam(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_Closure_collectLevelAux___main(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_1);
lean_ctor_set(x_13, 1, x_3);
return x_13;
}
case 1:
{
lean_object* x_14; lean_object* x_15; uint8_t x_37; 
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
x_37 = l_Lean_Level_hasMVar(x_14);
if (x_37 == 0)
{
uint8_t x_38; 
x_38 = l_Lean_Level_hasParam(x_14);
if (x_38 == 0)
{
x_4 = x_14;
x_5 = x_3;
goto block_12;
}
else
{
lean_object* x_39; 
x_39 = lean_box(0);
x_15 = x_39;
goto block_36;
}
}
else
{
lean_object* x_40; 
x_40 = lean_box(0);
x_15 = x_40;
goto block_36;
}
block_36:
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_15);
x_16 = lean_ctor_get(x_3, 2);
lean_inc(x_16);
x_17 = l_HashMapImp_find_x3f___at_Lean_Closure_visitLevel___spec__1(x_16, x_14);
lean_dec(x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
lean_inc(x_14);
x_18 = l_Lean_Closure_collectLevelAux___main(x_14, x_2, x_3);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
lean_dec(x_18);
x_21 = !lean_is_exclusive(x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_19, 2);
lean_inc(x_20);
x_23 = l_HashMapImp_insert___at_Lean_Closure_visitLevel___spec__3(x_22, x_14, x_20);
lean_ctor_set(x_19, 2, x_23);
x_4 = x_20;
x_5 = x_19;
goto block_12;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_24 = lean_ctor_get(x_19, 0);
x_25 = lean_ctor_get(x_19, 1);
x_26 = lean_ctor_get(x_19, 2);
x_27 = lean_ctor_get(x_19, 3);
x_28 = lean_ctor_get(x_19, 4);
x_29 = lean_ctor_get(x_19, 5);
x_30 = lean_ctor_get(x_19, 6);
x_31 = lean_ctor_get(x_19, 7);
x_32 = lean_ctor_get(x_19, 8);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_19);
lean_inc(x_20);
x_33 = l_HashMapImp_insert___at_Lean_Closure_visitLevel___spec__3(x_26, x_14, x_20);
x_34 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_34, 0, x_24);
lean_ctor_set(x_34, 1, x_25);
lean_ctor_set(x_34, 2, x_33);
lean_ctor_set(x_34, 3, x_27);
lean_ctor_set(x_34, 4, x_28);
lean_ctor_set(x_34, 5, x_29);
lean_ctor_set(x_34, 6, x_30);
lean_ctor_set(x_34, 7, x_31);
lean_ctor_set(x_34, 8, x_32);
x_4 = x_20;
x_5 = x_34;
goto block_12;
}
}
else
{
lean_object* x_35; 
lean_dec(x_14);
x_35 = lean_ctor_get(x_17, 0);
lean_inc(x_35);
lean_dec(x_17);
x_4 = x_35;
x_5 = x_3;
goto block_12;
}
}
}
case 2:
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_81; uint8_t x_103; 
x_41 = lean_ctor_get(x_1, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_1, 1);
lean_inc(x_42);
x_103 = l_Lean_Level_hasMVar(x_41);
if (x_103 == 0)
{
uint8_t x_104; 
x_104 = l_Lean_Level_hasParam(x_41);
if (x_104 == 0)
{
x_43 = x_41;
x_44 = x_3;
goto block_80;
}
else
{
lean_object* x_105; 
x_105 = lean_box(0);
x_81 = x_105;
goto block_102;
}
}
else
{
lean_object* x_106; 
x_106 = lean_box(0);
x_81 = x_106;
goto block_102;
}
block_80:
{
lean_object* x_45; lean_object* x_46; lean_object* x_54; uint8_t x_76; 
x_76 = l_Lean_Level_hasMVar(x_42);
if (x_76 == 0)
{
uint8_t x_77; 
x_77 = l_Lean_Level_hasParam(x_42);
if (x_77 == 0)
{
x_45 = x_42;
x_46 = x_44;
goto block_53;
}
else
{
lean_object* x_78; 
x_78 = lean_box(0);
x_54 = x_78;
goto block_75;
}
}
else
{
lean_object* x_79; 
x_79 = lean_box(0);
x_54 = x_79;
goto block_75;
}
block_53:
{
if (lean_obj_tag(x_1) == 2)
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_level_update_max(x_1, x_43, x_45);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_46);
return x_48;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_dec(x_45);
lean_dec(x_43);
lean_dec(x_1);
x_49 = l_Lean_Level_Inhabited;
x_50 = l_Lean_Level_updateMax_x21___closed__2;
x_51 = lean_panic_fn(x_49, x_50);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_46);
return x_52;
}
}
block_75:
{
lean_object* x_55; lean_object* x_56; 
lean_dec(x_54);
x_55 = lean_ctor_get(x_44, 2);
lean_inc(x_55);
x_56 = l_HashMapImp_find_x3f___at_Lean_Closure_visitLevel___spec__1(x_55, x_42);
lean_dec(x_55);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
lean_inc(x_42);
x_57 = l_Lean_Closure_collectLevelAux___main(x_42, x_2, x_44);
x_58 = lean_ctor_get(x_57, 1);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 0);
lean_inc(x_59);
lean_dec(x_57);
x_60 = !lean_is_exclusive(x_58);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_58, 2);
lean_inc(x_59);
x_62 = l_HashMapImp_insert___at_Lean_Closure_visitLevel___spec__3(x_61, x_42, x_59);
lean_ctor_set(x_58, 2, x_62);
x_45 = x_59;
x_46 = x_58;
goto block_53;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_63 = lean_ctor_get(x_58, 0);
x_64 = lean_ctor_get(x_58, 1);
x_65 = lean_ctor_get(x_58, 2);
x_66 = lean_ctor_get(x_58, 3);
x_67 = lean_ctor_get(x_58, 4);
x_68 = lean_ctor_get(x_58, 5);
x_69 = lean_ctor_get(x_58, 6);
x_70 = lean_ctor_get(x_58, 7);
x_71 = lean_ctor_get(x_58, 8);
lean_inc(x_71);
lean_inc(x_70);
lean_inc(x_69);
lean_inc(x_68);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_58);
lean_inc(x_59);
x_72 = l_HashMapImp_insert___at_Lean_Closure_visitLevel___spec__3(x_65, x_42, x_59);
x_73 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_73, 0, x_63);
lean_ctor_set(x_73, 1, x_64);
lean_ctor_set(x_73, 2, x_72);
lean_ctor_set(x_73, 3, x_66);
lean_ctor_set(x_73, 4, x_67);
lean_ctor_set(x_73, 5, x_68);
lean_ctor_set(x_73, 6, x_69);
lean_ctor_set(x_73, 7, x_70);
lean_ctor_set(x_73, 8, x_71);
x_45 = x_59;
x_46 = x_73;
goto block_53;
}
}
else
{
lean_object* x_74; 
lean_dec(x_42);
x_74 = lean_ctor_get(x_56, 0);
lean_inc(x_74);
lean_dec(x_56);
x_45 = x_74;
x_46 = x_44;
goto block_53;
}
}
}
block_102:
{
lean_object* x_82; lean_object* x_83; 
lean_dec(x_81);
x_82 = lean_ctor_get(x_3, 2);
lean_inc(x_82);
x_83 = l_HashMapImp_find_x3f___at_Lean_Closure_visitLevel___spec__1(x_82, x_41);
lean_dec(x_82);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; 
lean_inc(x_41);
x_84 = l_Lean_Closure_collectLevelAux___main(x_41, x_2, x_3);
x_85 = lean_ctor_get(x_84, 1);
lean_inc(x_85);
x_86 = lean_ctor_get(x_84, 0);
lean_inc(x_86);
lean_dec(x_84);
x_87 = !lean_is_exclusive(x_85);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; 
x_88 = lean_ctor_get(x_85, 2);
lean_inc(x_86);
x_89 = l_HashMapImp_insert___at_Lean_Closure_visitLevel___spec__3(x_88, x_41, x_86);
lean_ctor_set(x_85, 2, x_89);
x_43 = x_86;
x_44 = x_85;
goto block_80;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_90 = lean_ctor_get(x_85, 0);
x_91 = lean_ctor_get(x_85, 1);
x_92 = lean_ctor_get(x_85, 2);
x_93 = lean_ctor_get(x_85, 3);
x_94 = lean_ctor_get(x_85, 4);
x_95 = lean_ctor_get(x_85, 5);
x_96 = lean_ctor_get(x_85, 6);
x_97 = lean_ctor_get(x_85, 7);
x_98 = lean_ctor_get(x_85, 8);
lean_inc(x_98);
lean_inc(x_97);
lean_inc(x_96);
lean_inc(x_95);
lean_inc(x_94);
lean_inc(x_93);
lean_inc(x_92);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_85);
lean_inc(x_86);
x_99 = l_HashMapImp_insert___at_Lean_Closure_visitLevel___spec__3(x_92, x_41, x_86);
x_100 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_100, 0, x_90);
lean_ctor_set(x_100, 1, x_91);
lean_ctor_set(x_100, 2, x_99);
lean_ctor_set(x_100, 3, x_93);
lean_ctor_set(x_100, 4, x_94);
lean_ctor_set(x_100, 5, x_95);
lean_ctor_set(x_100, 6, x_96);
lean_ctor_set(x_100, 7, x_97);
lean_ctor_set(x_100, 8, x_98);
x_43 = x_86;
x_44 = x_100;
goto block_80;
}
}
else
{
lean_object* x_101; 
lean_dec(x_41);
x_101 = lean_ctor_get(x_83, 0);
lean_inc(x_101);
lean_dec(x_83);
x_43 = x_101;
x_44 = x_3;
goto block_80;
}
}
}
case 3:
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_147; uint8_t x_169; 
x_107 = lean_ctor_get(x_1, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_1, 1);
lean_inc(x_108);
x_169 = l_Lean_Level_hasMVar(x_107);
if (x_169 == 0)
{
uint8_t x_170; 
x_170 = l_Lean_Level_hasParam(x_107);
if (x_170 == 0)
{
x_109 = x_107;
x_110 = x_3;
goto block_146;
}
else
{
lean_object* x_171; 
x_171 = lean_box(0);
x_147 = x_171;
goto block_168;
}
}
else
{
lean_object* x_172; 
x_172 = lean_box(0);
x_147 = x_172;
goto block_168;
}
block_146:
{
lean_object* x_111; lean_object* x_112; lean_object* x_120; uint8_t x_142; 
x_142 = l_Lean_Level_hasMVar(x_108);
if (x_142 == 0)
{
uint8_t x_143; 
x_143 = l_Lean_Level_hasParam(x_108);
if (x_143 == 0)
{
x_111 = x_108;
x_112 = x_110;
goto block_119;
}
else
{
lean_object* x_144; 
x_144 = lean_box(0);
x_120 = x_144;
goto block_141;
}
}
else
{
lean_object* x_145; 
x_145 = lean_box(0);
x_120 = x_145;
goto block_141;
}
block_119:
{
if (lean_obj_tag(x_1) == 3)
{
lean_object* x_113; lean_object* x_114; 
x_113 = lean_level_update_imax(x_1, x_109, x_111);
x_114 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_114, 0, x_113);
lean_ctor_set(x_114, 1, x_112);
return x_114;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
lean_dec(x_111);
lean_dec(x_109);
lean_dec(x_1);
x_115 = l_Lean_Level_Inhabited;
x_116 = l_Lean_Level_updateIMax_x21___closed__2;
x_117 = lean_panic_fn(x_115, x_116);
x_118 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_118, 0, x_117);
lean_ctor_set(x_118, 1, x_112);
return x_118;
}
}
block_141:
{
lean_object* x_121; lean_object* x_122; 
lean_dec(x_120);
x_121 = lean_ctor_get(x_110, 2);
lean_inc(x_121);
x_122 = l_HashMapImp_find_x3f___at_Lean_Closure_visitLevel___spec__1(x_121, x_108);
lean_dec(x_121);
if (lean_obj_tag(x_122) == 0)
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; uint8_t x_126; 
lean_inc(x_108);
x_123 = l_Lean_Closure_collectLevelAux___main(x_108, x_2, x_110);
x_124 = lean_ctor_get(x_123, 1);
lean_inc(x_124);
x_125 = lean_ctor_get(x_123, 0);
lean_inc(x_125);
lean_dec(x_123);
x_126 = !lean_is_exclusive(x_124);
if (x_126 == 0)
{
lean_object* x_127; lean_object* x_128; 
x_127 = lean_ctor_get(x_124, 2);
lean_inc(x_125);
x_128 = l_HashMapImp_insert___at_Lean_Closure_visitLevel___spec__3(x_127, x_108, x_125);
lean_ctor_set(x_124, 2, x_128);
x_111 = x_125;
x_112 = x_124;
goto block_119;
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_129 = lean_ctor_get(x_124, 0);
x_130 = lean_ctor_get(x_124, 1);
x_131 = lean_ctor_get(x_124, 2);
x_132 = lean_ctor_get(x_124, 3);
x_133 = lean_ctor_get(x_124, 4);
x_134 = lean_ctor_get(x_124, 5);
x_135 = lean_ctor_get(x_124, 6);
x_136 = lean_ctor_get(x_124, 7);
x_137 = lean_ctor_get(x_124, 8);
lean_inc(x_137);
lean_inc(x_136);
lean_inc(x_135);
lean_inc(x_134);
lean_inc(x_133);
lean_inc(x_132);
lean_inc(x_131);
lean_inc(x_130);
lean_inc(x_129);
lean_dec(x_124);
lean_inc(x_125);
x_138 = l_HashMapImp_insert___at_Lean_Closure_visitLevel___spec__3(x_131, x_108, x_125);
x_139 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_139, 0, x_129);
lean_ctor_set(x_139, 1, x_130);
lean_ctor_set(x_139, 2, x_138);
lean_ctor_set(x_139, 3, x_132);
lean_ctor_set(x_139, 4, x_133);
lean_ctor_set(x_139, 5, x_134);
lean_ctor_set(x_139, 6, x_135);
lean_ctor_set(x_139, 7, x_136);
lean_ctor_set(x_139, 8, x_137);
x_111 = x_125;
x_112 = x_139;
goto block_119;
}
}
else
{
lean_object* x_140; 
lean_dec(x_108);
x_140 = lean_ctor_get(x_122, 0);
lean_inc(x_140);
lean_dec(x_122);
x_111 = x_140;
x_112 = x_110;
goto block_119;
}
}
}
block_168:
{
lean_object* x_148; lean_object* x_149; 
lean_dec(x_147);
x_148 = lean_ctor_get(x_3, 2);
lean_inc(x_148);
x_149 = l_HashMapImp_find_x3f___at_Lean_Closure_visitLevel___spec__1(x_148, x_107);
lean_dec(x_148);
if (lean_obj_tag(x_149) == 0)
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; uint8_t x_153; 
lean_inc(x_107);
x_150 = l_Lean_Closure_collectLevelAux___main(x_107, x_2, x_3);
x_151 = lean_ctor_get(x_150, 1);
lean_inc(x_151);
x_152 = lean_ctor_get(x_150, 0);
lean_inc(x_152);
lean_dec(x_150);
x_153 = !lean_is_exclusive(x_151);
if (x_153 == 0)
{
lean_object* x_154; lean_object* x_155; 
x_154 = lean_ctor_get(x_151, 2);
lean_inc(x_152);
x_155 = l_HashMapImp_insert___at_Lean_Closure_visitLevel___spec__3(x_154, x_107, x_152);
lean_ctor_set(x_151, 2, x_155);
x_109 = x_152;
x_110 = x_151;
goto block_146;
}
else
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_156 = lean_ctor_get(x_151, 0);
x_157 = lean_ctor_get(x_151, 1);
x_158 = lean_ctor_get(x_151, 2);
x_159 = lean_ctor_get(x_151, 3);
x_160 = lean_ctor_get(x_151, 4);
x_161 = lean_ctor_get(x_151, 5);
x_162 = lean_ctor_get(x_151, 6);
x_163 = lean_ctor_get(x_151, 7);
x_164 = lean_ctor_get(x_151, 8);
lean_inc(x_164);
lean_inc(x_163);
lean_inc(x_162);
lean_inc(x_161);
lean_inc(x_160);
lean_inc(x_159);
lean_inc(x_158);
lean_inc(x_157);
lean_inc(x_156);
lean_dec(x_151);
lean_inc(x_152);
x_165 = l_HashMapImp_insert___at_Lean_Closure_visitLevel___spec__3(x_158, x_107, x_152);
x_166 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_166, 0, x_156);
lean_ctor_set(x_166, 1, x_157);
lean_ctor_set(x_166, 2, x_165);
lean_ctor_set(x_166, 3, x_159);
lean_ctor_set(x_166, 4, x_160);
lean_ctor_set(x_166, 5, x_161);
lean_ctor_set(x_166, 6, x_162);
lean_ctor_set(x_166, 7, x_163);
lean_ctor_set(x_166, 8, x_164);
x_109 = x_152;
x_110 = x_166;
goto block_146;
}
}
else
{
lean_object* x_167; 
lean_dec(x_107);
x_167 = lean_ctor_get(x_149, 0);
lean_inc(x_167);
lean_dec(x_149);
x_109 = x_167;
x_110 = x_3;
goto block_146;
}
}
}
default: 
{
lean_object* x_173; 
x_173 = l_Lean_Closure_mkNewLevelParam(x_1, x_2, x_3);
return x_173;
}
}
block_12:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_level_update_succ(x_1, x_4);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_4);
lean_dec(x_1);
x_8 = l_Lean_Level_Inhabited;
x_9 = l_Lean_Level_updateSucc_x21___closed__2;
x_10 = lean_panic_fn(x_8, x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_5);
return x_11;
}
}
}
}
lean_object* l_Lean_Closure_collectLevelAux___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Closure_collectLevelAux___main(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_Closure_collectLevelAux(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Closure_collectLevelAux___main(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_Closure_collectLevelAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Closure_collectLevelAux(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_Closure_collectLevel(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_44; 
x_44 = l_Lean_Level_hasMVar(x_1);
if (x_44 == 0)
{
uint8_t x_45; 
x_45 = l_Lean_Level_hasParam(x_1);
if (x_45 == 0)
{
lean_object* x_46; 
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_1);
lean_ctor_set(x_46, 1, x_3);
return x_46;
}
else
{
lean_object* x_47; 
x_47 = lean_box(0);
x_4 = x_47;
goto block_43;
}
}
else
{
lean_object* x_48; 
x_48 = lean_box(0);
x_4 = x_48;
goto block_43;
}
block_43:
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_4);
x_5 = lean_ctor_get(x_3, 2);
lean_inc(x_5);
x_6 = l_HashMapImp_find_x3f___at_Lean_Closure_visitLevel___spec__1(x_5, x_1);
lean_dec(x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; uint8_t x_8; 
lean_inc(x_1);
x_7 = l_Lean_Closure_collectLevelAux___main(x_1, x_2, x_3);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_7, 1);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_7, 0);
x_12 = lean_ctor_get(x_9, 2);
lean_inc(x_11);
x_13 = l_HashMapImp_insert___at_Lean_Closure_visitLevel___spec__3(x_12, x_1, x_11);
lean_ctor_set(x_9, 2, x_13);
return x_7;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_14 = lean_ctor_get(x_7, 0);
x_15 = lean_ctor_get(x_9, 0);
x_16 = lean_ctor_get(x_9, 1);
x_17 = lean_ctor_get(x_9, 2);
x_18 = lean_ctor_get(x_9, 3);
x_19 = lean_ctor_get(x_9, 4);
x_20 = lean_ctor_get(x_9, 5);
x_21 = lean_ctor_get(x_9, 6);
x_22 = lean_ctor_get(x_9, 7);
x_23 = lean_ctor_get(x_9, 8);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_9);
lean_inc(x_14);
x_24 = l_HashMapImp_insert___at_Lean_Closure_visitLevel___spec__3(x_17, x_1, x_14);
x_25 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_25, 0, x_15);
lean_ctor_set(x_25, 1, x_16);
lean_ctor_set(x_25, 2, x_24);
lean_ctor_set(x_25, 3, x_18);
lean_ctor_set(x_25, 4, x_19);
lean_ctor_set(x_25, 5, x_20);
lean_ctor_set(x_25, 6, x_21);
lean_ctor_set(x_25, 7, x_22);
lean_ctor_set(x_25, 8, x_23);
lean_ctor_set(x_7, 1, x_25);
return x_7;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_26 = lean_ctor_get(x_7, 1);
x_27 = lean_ctor_get(x_7, 0);
lean_inc(x_26);
lean_inc(x_27);
lean_dec(x_7);
x_28 = lean_ctor_get(x_26, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
x_30 = lean_ctor_get(x_26, 2);
lean_inc(x_30);
x_31 = lean_ctor_get(x_26, 3);
lean_inc(x_31);
x_32 = lean_ctor_get(x_26, 4);
lean_inc(x_32);
x_33 = lean_ctor_get(x_26, 5);
lean_inc(x_33);
x_34 = lean_ctor_get(x_26, 6);
lean_inc(x_34);
x_35 = lean_ctor_get(x_26, 7);
lean_inc(x_35);
x_36 = lean_ctor_get(x_26, 8);
lean_inc(x_36);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 lean_ctor_release(x_26, 2);
 lean_ctor_release(x_26, 3);
 lean_ctor_release(x_26, 4);
 lean_ctor_release(x_26, 5);
 lean_ctor_release(x_26, 6);
 lean_ctor_release(x_26, 7);
 lean_ctor_release(x_26, 8);
 x_37 = x_26;
} else {
 lean_dec_ref(x_26);
 x_37 = lean_box(0);
}
lean_inc(x_27);
x_38 = l_HashMapImp_insert___at_Lean_Closure_visitLevel___spec__3(x_30, x_1, x_27);
if (lean_is_scalar(x_37)) {
 x_39 = lean_alloc_ctor(0, 9, 0);
} else {
 x_39 = x_37;
}
lean_ctor_set(x_39, 0, x_28);
lean_ctor_set(x_39, 1, x_29);
lean_ctor_set(x_39, 2, x_38);
lean_ctor_set(x_39, 3, x_31);
lean_ctor_set(x_39, 4, x_32);
lean_ctor_set(x_39, 5, x_33);
lean_ctor_set(x_39, 6, x_34);
lean_ctor_set(x_39, 7, x_35);
lean_ctor_set(x_39, 8, x_36);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_27);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
else
{
lean_object* x_41; lean_object* x_42; 
lean_dec(x_1);
x_41 = lean_ctor_get(x_6, 0);
lean_inc(x_41);
lean_dec(x_6);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_3);
return x_42;
}
}
}
}
lean_object* l_Lean_Closure_collectLevel___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Closure_collectLevel(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_Closure_mkFreshFVarId___rarg(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_inc(x_5);
x_7 = lean_name_mk_numeral(x_5, x_6);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_add(x_6, x_8);
lean_dec(x_6);
lean_ctor_set(x_3, 1, x_9);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_7);
lean_ctor_set(x_10, 1, x_1);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_11 = lean_ctor_get(x_3, 0);
x_12 = lean_ctor_get(x_3, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_3);
lean_inc(x_12);
lean_inc(x_11);
x_13 = lean_name_mk_numeral(x_11, x_12);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_12, x_14);
lean_dec(x_12);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_11);
lean_ctor_set(x_16, 1, x_15);
lean_ctor_set(x_1, 1, x_16);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_13);
lean_ctor_set(x_17, 1, x_1);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_18 = lean_ctor_get(x_1, 1);
x_19 = lean_ctor_get(x_1, 0);
x_20 = lean_ctor_get(x_1, 2);
x_21 = lean_ctor_get(x_1, 3);
x_22 = lean_ctor_get(x_1, 4);
x_23 = lean_ctor_get(x_1, 5);
x_24 = lean_ctor_get(x_1, 6);
x_25 = lean_ctor_get(x_1, 7);
x_26 = lean_ctor_get(x_1, 8);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_18);
lean_inc(x_19);
lean_dec(x_1);
x_27 = lean_ctor_get(x_18, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_18, 1);
lean_inc(x_28);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 x_29 = x_18;
} else {
 lean_dec_ref(x_18);
 x_29 = lean_box(0);
}
lean_inc(x_28);
lean_inc(x_27);
x_30 = lean_name_mk_numeral(x_27, x_28);
x_31 = lean_unsigned_to_nat(1u);
x_32 = lean_nat_add(x_28, x_31);
lean_dec(x_28);
if (lean_is_scalar(x_29)) {
 x_33 = lean_alloc_ctor(0, 2, 0);
} else {
 x_33 = x_29;
}
lean_ctor_set(x_33, 0, x_27);
lean_ctor_set(x_33, 1, x_32);
x_34 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_34, 0, x_19);
lean_ctor_set(x_34, 1, x_33);
lean_ctor_set(x_34, 2, x_20);
lean_ctor_set(x_34, 3, x_21);
lean_ctor_set(x_34, 4, x_22);
lean_ctor_set(x_34, 5, x_23);
lean_ctor_set(x_34, 6, x_24);
lean_ctor_set(x_34, 7, x_25);
lean_ctor_set(x_34, 8, x_26);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_30);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
lean_object* l_Lean_Closure_mkFreshFVarId(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Closure_mkFreshFVarId___rarg), 1, 0);
return x_2;
}
}
lean_object* l_Lean_Closure_mkFreshFVarId___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Closure_mkFreshFVarId(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Closure_mkNextUserName___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_x");
return x_1;
}
}
lean_object* _init_l_Lean_Closure_mkNextUserName___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Closure_mkNextUserName___rarg___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Closure_mkNextUserName___rarg(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_1, 7);
x_4 = l_Lean_Closure_mkNextUserName___rarg___closed__2;
lean_inc(x_3);
x_5 = l_Lean_Name_appendIndexAfter(x_4, x_3);
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_add(x_3, x_6);
lean_dec(x_3);
lean_ctor_set(x_1, 7, x_7);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_1);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
x_11 = lean_ctor_get(x_1, 2);
x_12 = lean_ctor_get(x_1, 3);
x_13 = lean_ctor_get(x_1, 4);
x_14 = lean_ctor_get(x_1, 5);
x_15 = lean_ctor_get(x_1, 6);
x_16 = lean_ctor_get(x_1, 7);
x_17 = lean_ctor_get(x_1, 8);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_1);
x_18 = l_Lean_Closure_mkNextUserName___rarg___closed__2;
lean_inc(x_16);
x_19 = l_Lean_Name_appendIndexAfter(x_18, x_16);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_add(x_16, x_20);
lean_dec(x_16);
x_22 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_22, 0, x_9);
lean_ctor_set(x_22, 1, x_10);
lean_ctor_set(x_22, 2, x_11);
lean_ctor_set(x_22, 3, x_12);
lean_ctor_set(x_22, 4, x_13);
lean_ctor_set(x_22, 5, x_14);
lean_ctor_set(x_22, 6, x_15);
lean_ctor_set(x_22, 7, x_21);
lean_ctor_set(x_22, 8, x_17);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_19);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
lean_object* l_Lean_Closure_mkNextUserName(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Closure_mkNextUserName___rarg), 1, 0);
return x_2;
}
}
lean_object* l_Lean_Closure_mkNextUserName___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Closure_mkNextUserName(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Closure_getUserName(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; 
x_4 = l_Lean_Closure_mkNextUserName___rarg(x_3);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_3);
return x_6;
}
}
}
lean_object* l_Lean_Closure_getUserName___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Closure_getUserName(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Closure_mkLocalDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = l_Lean_Closure_getUserName(x_1, x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = l_Lean_Closure_mkFreshFVarId___rarg(x_7);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_8, 1);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_8, 0);
x_13 = lean_ctor_get(x_10, 0);
x_14 = 0;
lean_inc(x_12);
x_15 = lean_local_ctx_mk_local_decl(x_13, x_12, x_6, x_2, x_14);
lean_ctor_set(x_10, 0, x_15);
x_16 = l_Lean_mkFVar(x_12);
lean_ctor_set(x_8, 0, x_16);
return x_8;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_17 = lean_ctor_get(x_8, 0);
x_18 = lean_ctor_get(x_10, 0);
x_19 = lean_ctor_get(x_10, 1);
x_20 = lean_ctor_get(x_10, 2);
x_21 = lean_ctor_get(x_10, 3);
x_22 = lean_ctor_get(x_10, 4);
x_23 = lean_ctor_get(x_10, 5);
x_24 = lean_ctor_get(x_10, 6);
x_25 = lean_ctor_get(x_10, 7);
x_26 = lean_ctor_get(x_10, 8);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_10);
x_27 = 0;
lean_inc(x_17);
x_28 = lean_local_ctx_mk_local_decl(x_18, x_17, x_6, x_2, x_27);
x_29 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_19);
lean_ctor_set(x_29, 2, x_20);
lean_ctor_set(x_29, 3, x_21);
lean_ctor_set(x_29, 4, x_22);
lean_ctor_set(x_29, 5, x_23);
lean_ctor_set(x_29, 6, x_24);
lean_ctor_set(x_29, 7, x_25);
lean_ctor_set(x_29, 8, x_26);
x_30 = l_Lean_mkFVar(x_17);
lean_ctor_set(x_8, 1, x_29);
lean_ctor_set(x_8, 0, x_30);
return x_8;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_31 = lean_ctor_get(x_8, 1);
x_32 = lean_ctor_get(x_8, 0);
lean_inc(x_31);
lean_inc(x_32);
lean_dec(x_8);
x_33 = lean_ctor_get(x_31, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
x_35 = lean_ctor_get(x_31, 2);
lean_inc(x_35);
x_36 = lean_ctor_get(x_31, 3);
lean_inc(x_36);
x_37 = lean_ctor_get(x_31, 4);
lean_inc(x_37);
x_38 = lean_ctor_get(x_31, 5);
lean_inc(x_38);
x_39 = lean_ctor_get(x_31, 6);
lean_inc(x_39);
x_40 = lean_ctor_get(x_31, 7);
lean_inc(x_40);
x_41 = lean_ctor_get(x_31, 8);
lean_inc(x_41);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 lean_ctor_release(x_31, 2);
 lean_ctor_release(x_31, 3);
 lean_ctor_release(x_31, 4);
 lean_ctor_release(x_31, 5);
 lean_ctor_release(x_31, 6);
 lean_ctor_release(x_31, 7);
 lean_ctor_release(x_31, 8);
 x_42 = x_31;
} else {
 lean_dec_ref(x_31);
 x_42 = lean_box(0);
}
x_43 = 0;
lean_inc(x_32);
x_44 = lean_local_ctx_mk_local_decl(x_33, x_32, x_6, x_2, x_43);
if (lean_is_scalar(x_42)) {
 x_45 = lean_alloc_ctor(0, 9, 0);
} else {
 x_45 = x_42;
}
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_34);
lean_ctor_set(x_45, 2, x_35);
lean_ctor_set(x_45, 3, x_36);
lean_ctor_set(x_45, 4, x_37);
lean_ctor_set(x_45, 5, x_38);
lean_ctor_set(x_45, 6, x_39);
lean_ctor_set(x_45, 7, x_40);
lean_ctor_set(x_45, 8, x_41);
x_46 = l_Lean_mkFVar(x_32);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_45);
return x_47;
}
}
}
lean_object* l_Lean_Closure_mkLocalDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Closure_mkLocalDecl(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Closure_mkLetDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = l_Lean_Closure_mkFreshFVarId___rarg(x_5);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_6, 1);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_6, 0);
x_11 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
x_12 = lean_local_ctx_mk_let_decl(x_11, x_10, x_1, x_2, x_3);
lean_ctor_set(x_8, 0, x_12);
x_13 = l_Lean_mkFVar(x_10);
lean_ctor_set(x_6, 0, x_13);
return x_6;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_14 = lean_ctor_get(x_6, 0);
x_15 = lean_ctor_get(x_8, 0);
x_16 = lean_ctor_get(x_8, 1);
x_17 = lean_ctor_get(x_8, 2);
x_18 = lean_ctor_get(x_8, 3);
x_19 = lean_ctor_get(x_8, 4);
x_20 = lean_ctor_get(x_8, 5);
x_21 = lean_ctor_get(x_8, 6);
x_22 = lean_ctor_get(x_8, 7);
x_23 = lean_ctor_get(x_8, 8);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_8);
lean_inc(x_14);
x_24 = lean_local_ctx_mk_let_decl(x_15, x_14, x_1, x_2, x_3);
x_25 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_16);
lean_ctor_set(x_25, 2, x_17);
lean_ctor_set(x_25, 3, x_18);
lean_ctor_set(x_25, 4, x_19);
lean_ctor_set(x_25, 5, x_20);
lean_ctor_set(x_25, 6, x_21);
lean_ctor_set(x_25, 7, x_22);
lean_ctor_set(x_25, 8, x_23);
x_26 = l_Lean_mkFVar(x_14);
lean_ctor_set(x_6, 1, x_25);
lean_ctor_set(x_6, 0, x_26);
return x_6;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_27 = lean_ctor_get(x_6, 1);
x_28 = lean_ctor_get(x_6, 0);
lean_inc(x_27);
lean_inc(x_28);
lean_dec(x_6);
x_29 = lean_ctor_get(x_27, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
x_31 = lean_ctor_get(x_27, 2);
lean_inc(x_31);
x_32 = lean_ctor_get(x_27, 3);
lean_inc(x_32);
x_33 = lean_ctor_get(x_27, 4);
lean_inc(x_33);
x_34 = lean_ctor_get(x_27, 5);
lean_inc(x_34);
x_35 = lean_ctor_get(x_27, 6);
lean_inc(x_35);
x_36 = lean_ctor_get(x_27, 7);
lean_inc(x_36);
x_37 = lean_ctor_get(x_27, 8);
lean_inc(x_37);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 lean_ctor_release(x_27, 1);
 lean_ctor_release(x_27, 2);
 lean_ctor_release(x_27, 3);
 lean_ctor_release(x_27, 4);
 lean_ctor_release(x_27, 5);
 lean_ctor_release(x_27, 6);
 lean_ctor_release(x_27, 7);
 lean_ctor_release(x_27, 8);
 x_38 = x_27;
} else {
 lean_dec_ref(x_27);
 x_38 = lean_box(0);
}
lean_inc(x_28);
x_39 = lean_local_ctx_mk_let_decl(x_29, x_28, x_1, x_2, x_3);
if (lean_is_scalar(x_38)) {
 x_40 = lean_alloc_ctor(0, 9, 0);
} else {
 x_40 = x_38;
}
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_30);
lean_ctor_set(x_40, 2, x_31);
lean_ctor_set(x_40, 3, x_32);
lean_ctor_set(x_40, 4, x_33);
lean_ctor_set(x_40, 5, x_34);
lean_ctor_set(x_40, 6, x_35);
lean_ctor_set(x_40, 7, x_36);
lean_ctor_set(x_40, 8, x_37);
x_41 = l_Lean_mkFVar(x_28);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_40);
return x_42;
}
}
}
lean_object* l_Lean_Closure_mkLetDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Closure_mkLetDecl(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
return x_6;
}
}
lean_object* l_AssocList_find_x3f___main___at_Lean_Closure_visitExpr___spec__2(lean_object* x_1, lean_object* x_2) {
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
x_7 = lean_expr_equal(x_4, x_1);
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
lean_object* l_HashMapImp_find_x3f___at_Lean_Closure_visitExpr___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; size_t x_5; size_t x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
x_5 = l_Lean_Expr_hash(x_2);
x_6 = lean_usize_modn(x_5, x_4);
lean_dec(x_4);
x_7 = lean_array_uget(x_3, x_6);
x_8 = l_AssocList_find_x3f___main___at_Lean_Closure_visitExpr___spec__2(x_2, x_7);
lean_dec(x_7);
return x_8;
}
}
uint8_t l_AssocList_contains___main___at_Lean_Closure_visitExpr___spec__4(lean_object* x_1, lean_object* x_2) {
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
x_6 = lean_expr_equal(x_4, x_1);
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
lean_object* l_AssocList_foldlM___main___at_Lean_Closure_visitExpr___spec__7(lean_object* x_1, lean_object* x_2) {
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
x_7 = l_Lean_Expr_hash(x_4);
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
x_16 = l_Lean_Expr_hash(x_12);
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
lean_object* l_HashMapImp_moveEntries___main___at_Lean_Closure_visitExpr___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_AssocList_foldlM___main___at_Lean_Closure_visitExpr___spec__7(x_3, x_6);
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
lean_object* l_HashMapImp_expand___at_Lean_Closure_visitExpr___spec__5(lean_object* x_1, lean_object* x_2) {
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
x_9 = l_HashMapImp_moveEntries___main___at_Lean_Closure_visitExpr___spec__6(x_8, x_2, x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
lean_object* l_AssocList_replace___main___at_Lean_Closure_visitExpr___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_8 = lean_expr_equal(x_5, x_1);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = l_AssocList_replace___main___at_Lean_Closure_visitExpr___spec__8(x_1, x_2, x_7);
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
x_13 = lean_expr_equal(x_10, x_1);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = l_AssocList_replace___main___at_Lean_Closure_visitExpr___spec__8(x_1, x_2, x_12);
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
lean_object* l_HashMapImp_insert___at_Lean_Closure_visitExpr___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_8 = l_Lean_Expr_hash(x_2);
x_9 = lean_usize_modn(x_8, x_7);
x_10 = lean_array_uget(x_6, x_9);
x_11 = l_AssocList_contains___main___at_Lean_Closure_visitExpr___spec__4(x_2, x_10);
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
x_17 = l_HashMapImp_expand___at_Lean_Closure_visitExpr___spec__5(x_13, x_15);
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
x_18 = l_AssocList_replace___main___at_Lean_Closure_visitExpr___spec__8(x_2, x_3, x_10);
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
x_23 = l_Lean_Expr_hash(x_2);
x_24 = lean_usize_modn(x_23, x_22);
x_25 = lean_array_uget(x_21, x_24);
x_26 = l_AssocList_contains___main___at_Lean_Closure_visitExpr___spec__4(x_2, x_25);
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
x_32 = l_HashMapImp_expand___at_Lean_Closure_visitExpr___spec__5(x_28, x_30);
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
x_34 = l_AssocList_replace___main___at_Lean_Closure_visitExpr___spec__8(x_2, x_3, x_25);
x_35 = lean_array_uset(x_21, x_24, x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_20);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
lean_object* l_Lean_Closure_visitExpr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_49; 
x_49 = l_Lean_Expr_hasLevelParam(x_2);
if (x_49 == 0)
{
uint8_t x_50; 
x_50 = l_Lean_Expr_hasFVar(x_2);
if (x_50 == 0)
{
uint8_t x_51; 
x_51 = l_Lean_Expr_hasMVar(x_2);
if (x_51 == 0)
{
lean_object* x_52; 
lean_dec(x_3);
lean_dec(x_1);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_2);
lean_ctor_set(x_52, 1, x_4);
return x_52;
}
else
{
lean_object* x_53; 
x_53 = lean_box(0);
x_5 = x_53;
goto block_48;
}
}
else
{
lean_object* x_54; 
x_54 = lean_box(0);
x_5 = x_54;
goto block_48;
}
}
else
{
lean_object* x_55; 
x_55 = lean_box(0);
x_5 = x_55;
goto block_48;
}
block_48:
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_5);
x_6 = lean_ctor_get(x_4, 3);
lean_inc(x_6);
x_7 = l_HashMapImp_find_x3f___at_Lean_Closure_visitExpr___spec__1(x_6, x_2);
lean_dec(x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
lean_inc(x_2);
x_8 = lean_apply_3(x_1, x_2, x_3, x_4);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_8, 1);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_8, 0);
x_13 = lean_ctor_get(x_10, 3);
lean_inc(x_12);
x_14 = l_HashMapImp_insert___at_Lean_Closure_visitExpr___spec__3(x_13, x_2, x_12);
lean_ctor_set(x_10, 3, x_14);
return x_8;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_15 = lean_ctor_get(x_8, 0);
x_16 = lean_ctor_get(x_10, 0);
x_17 = lean_ctor_get(x_10, 1);
x_18 = lean_ctor_get(x_10, 2);
x_19 = lean_ctor_get(x_10, 3);
x_20 = lean_ctor_get(x_10, 4);
x_21 = lean_ctor_get(x_10, 5);
x_22 = lean_ctor_get(x_10, 6);
x_23 = lean_ctor_get(x_10, 7);
x_24 = lean_ctor_get(x_10, 8);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_10);
lean_inc(x_15);
x_25 = l_HashMapImp_insert___at_Lean_Closure_visitExpr___spec__3(x_19, x_2, x_15);
x_26 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_26, 0, x_16);
lean_ctor_set(x_26, 1, x_17);
lean_ctor_set(x_26, 2, x_18);
lean_ctor_set(x_26, 3, x_25);
lean_ctor_set(x_26, 4, x_20);
lean_ctor_set(x_26, 5, x_21);
lean_ctor_set(x_26, 6, x_22);
lean_ctor_set(x_26, 7, x_23);
lean_ctor_set(x_26, 8, x_24);
lean_ctor_set(x_8, 1, x_26);
return x_8;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_27 = lean_ctor_get(x_8, 1);
x_28 = lean_ctor_get(x_8, 0);
lean_inc(x_27);
lean_inc(x_28);
lean_dec(x_8);
x_29 = lean_ctor_get(x_27, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
x_31 = lean_ctor_get(x_27, 2);
lean_inc(x_31);
x_32 = lean_ctor_get(x_27, 3);
lean_inc(x_32);
x_33 = lean_ctor_get(x_27, 4);
lean_inc(x_33);
x_34 = lean_ctor_get(x_27, 5);
lean_inc(x_34);
x_35 = lean_ctor_get(x_27, 6);
lean_inc(x_35);
x_36 = lean_ctor_get(x_27, 7);
lean_inc(x_36);
x_37 = lean_ctor_get(x_27, 8);
lean_inc(x_37);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 lean_ctor_release(x_27, 1);
 lean_ctor_release(x_27, 2);
 lean_ctor_release(x_27, 3);
 lean_ctor_release(x_27, 4);
 lean_ctor_release(x_27, 5);
 lean_ctor_release(x_27, 6);
 lean_ctor_release(x_27, 7);
 lean_ctor_release(x_27, 8);
 x_38 = x_27;
} else {
 lean_dec_ref(x_27);
 x_38 = lean_box(0);
}
lean_inc(x_28);
x_39 = l_HashMapImp_insert___at_Lean_Closure_visitExpr___spec__3(x_32, x_2, x_28);
if (lean_is_scalar(x_38)) {
 x_40 = lean_alloc_ctor(0, 9, 0);
} else {
 x_40 = x_38;
}
lean_ctor_set(x_40, 0, x_29);
lean_ctor_set(x_40, 1, x_30);
lean_ctor_set(x_40, 2, x_31);
lean_ctor_set(x_40, 3, x_39);
lean_ctor_set(x_40, 4, x_33);
lean_ctor_set(x_40, 5, x_34);
lean_ctor_set(x_40, 6, x_35);
lean_ctor_set(x_40, 7, x_36);
lean_ctor_set(x_40, 8, x_37);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_28);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
else
{
uint8_t x_42; 
lean_dec(x_2);
x_42 = !lean_is_exclusive(x_8);
if (x_42 == 0)
{
return x_8;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_8, 0);
x_44 = lean_ctor_get(x_8, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_8);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
else
{
lean_object* x_46; lean_object* x_47; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_46 = lean_ctor_get(x_7, 0);
lean_inc(x_46);
lean_dec(x_7);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_4);
return x_47;
}
}
}
}
lean_object* l_AssocList_find_x3f___main___at_Lean_Closure_visitExpr___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_AssocList_find_x3f___main___at_Lean_Closure_visitExpr___spec__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_HashMapImp_find_x3f___at_Lean_Closure_visitExpr___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_HashMapImp_find_x3f___at_Lean_Closure_visitExpr___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_AssocList_contains___main___at_Lean_Closure_visitExpr___spec__4___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_AssocList_contains___main___at_Lean_Closure_visitExpr___spec__4(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_List_mapM___main___at_Lean_Closure_collectExprAux___main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_1);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_1, 1);
x_9 = l_Lean_Closure_collectLevel(x_7, x_2, x_3);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_List_mapM___main___at_Lean_Closure_collectExprAux___main___spec__1(x_8, x_2, x_11);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_12, 0);
lean_ctor_set(x_1, 1, x_14);
lean_ctor_set(x_1, 0, x_10);
lean_ctor_set(x_12, 0, x_1);
return x_12;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_12, 0);
x_16 = lean_ctor_get(x_12, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_12);
lean_ctor_set(x_1, 1, x_15);
lean_ctor_set(x_1, 0, x_10);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_1);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_18 = lean_ctor_get(x_1, 0);
x_19 = lean_ctor_get(x_1, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_1);
x_20 = l_Lean_Closure_collectLevel(x_18, x_2, x_3);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l_List_mapM___main___at_Lean_Closure_collectExprAux___main___spec__1(x_19, x_2, x_22);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 lean_ctor_release(x_23, 1);
 x_26 = x_23;
} else {
 lean_dec_ref(x_23);
 x_26 = lean_box(0);
}
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_21);
lean_ctor_set(x_27, 1, x_24);
if (lean_is_scalar(x_26)) {
 x_28 = lean_alloc_ctor(0, 2, 0);
} else {
 x_28 = x_26;
}
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_25);
return x_28;
}
}
}
}
lean_object* l_Lean_Closure_collectExprAux___main(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_13; lean_object* x_14; 
switch (lean_obj_tag(x_1)) {
case 1:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_1, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_2, 1);
lean_inc(x_23);
x_24 = lean_local_ctx_find(x_23, x_22);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_2);
lean_dec(x_1);
x_25 = l_Lean_LocalContext_get_x21___closed__1;
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_3);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_24, 0);
lean_inc(x_27);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 x_28 = x_24;
} else {
 lean_dec_ref(x_24);
 x_28 = lean_box(0);
}
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_67; uint8_t x_93; 
x_29 = lean_ctor_get(x_27, 2);
lean_inc(x_29);
x_30 = lean_ctor_get(x_27, 3);
lean_inc(x_30);
lean_dec(x_27);
x_93 = l_Lean_Expr_hasLevelParam(x_30);
if (x_93 == 0)
{
uint8_t x_94; 
x_94 = l_Lean_Expr_hasFVar(x_30);
if (x_94 == 0)
{
uint8_t x_95; 
x_95 = l_Lean_Expr_hasMVar(x_30);
if (x_95 == 0)
{
x_31 = x_30;
x_32 = x_3;
goto block_66;
}
else
{
lean_object* x_96; 
x_96 = lean_box(0);
x_67 = x_96;
goto block_92;
}
}
else
{
lean_object* x_97; 
x_97 = lean_box(0);
x_67 = x_97;
goto block_92;
}
}
else
{
lean_object* x_98; 
x_98 = lean_box(0);
x_67 = x_98;
goto block_92;
}
block_66:
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; 
if (lean_is_scalar(x_28)) {
 x_33 = lean_alloc_ctor(1, 1, 0);
} else {
 x_33 = x_28;
}
lean_ctor_set(x_33, 0, x_29);
x_34 = l_Lean_Closure_mkLocalDecl(x_33, x_31, x_2, x_32);
lean_dec(x_2);
lean_dec(x_33);
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
lean_object* x_36; uint8_t x_37; 
x_36 = lean_ctor_get(x_34, 1);
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_36, 8);
x_39 = lean_array_push(x_38, x_1);
lean_ctor_set(x_36, 8, x_39);
return x_34;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_40 = lean_ctor_get(x_36, 0);
x_41 = lean_ctor_get(x_36, 1);
x_42 = lean_ctor_get(x_36, 2);
x_43 = lean_ctor_get(x_36, 3);
x_44 = lean_ctor_get(x_36, 4);
x_45 = lean_ctor_get(x_36, 5);
x_46 = lean_ctor_get(x_36, 6);
x_47 = lean_ctor_get(x_36, 7);
x_48 = lean_ctor_get(x_36, 8);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_36);
x_49 = lean_array_push(x_48, x_1);
x_50 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_50, 0, x_40);
lean_ctor_set(x_50, 1, x_41);
lean_ctor_set(x_50, 2, x_42);
lean_ctor_set(x_50, 3, x_43);
lean_ctor_set(x_50, 4, x_44);
lean_ctor_set(x_50, 5, x_45);
lean_ctor_set(x_50, 6, x_46);
lean_ctor_set(x_50, 7, x_47);
lean_ctor_set(x_50, 8, x_49);
lean_ctor_set(x_34, 1, x_50);
return x_34;
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_51 = lean_ctor_get(x_34, 1);
x_52 = lean_ctor_get(x_34, 0);
lean_inc(x_51);
lean_inc(x_52);
lean_dec(x_34);
x_53 = lean_ctor_get(x_51, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_51, 1);
lean_inc(x_54);
x_55 = lean_ctor_get(x_51, 2);
lean_inc(x_55);
x_56 = lean_ctor_get(x_51, 3);
lean_inc(x_56);
x_57 = lean_ctor_get(x_51, 4);
lean_inc(x_57);
x_58 = lean_ctor_get(x_51, 5);
lean_inc(x_58);
x_59 = lean_ctor_get(x_51, 6);
lean_inc(x_59);
x_60 = lean_ctor_get(x_51, 7);
lean_inc(x_60);
x_61 = lean_ctor_get(x_51, 8);
lean_inc(x_61);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 lean_ctor_release(x_51, 1);
 lean_ctor_release(x_51, 2);
 lean_ctor_release(x_51, 3);
 lean_ctor_release(x_51, 4);
 lean_ctor_release(x_51, 5);
 lean_ctor_release(x_51, 6);
 lean_ctor_release(x_51, 7);
 lean_ctor_release(x_51, 8);
 x_62 = x_51;
} else {
 lean_dec_ref(x_51);
 x_62 = lean_box(0);
}
x_63 = lean_array_push(x_61, x_1);
if (lean_is_scalar(x_62)) {
 x_64 = lean_alloc_ctor(0, 9, 0);
} else {
 x_64 = x_62;
}
lean_ctor_set(x_64, 0, x_53);
lean_ctor_set(x_64, 1, x_54);
lean_ctor_set(x_64, 2, x_55);
lean_ctor_set(x_64, 3, x_56);
lean_ctor_set(x_64, 4, x_57);
lean_ctor_set(x_64, 5, x_58);
lean_ctor_set(x_64, 6, x_59);
lean_ctor_set(x_64, 7, x_60);
lean_ctor_set(x_64, 8, x_63);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_52);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
block_92:
{
lean_object* x_68; lean_object* x_69; 
lean_dec(x_67);
x_68 = lean_ctor_get(x_3, 3);
lean_inc(x_68);
x_69 = l_HashMapImp_find_x3f___at_Lean_Closure_visitExpr___spec__1(x_68, x_30);
lean_dec(x_68);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; 
lean_inc(x_2);
lean_inc(x_30);
x_70 = l_Lean_Closure_collectExprAux___main(x_30, x_2, x_3);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; uint8_t x_73; 
x_71 = lean_ctor_get(x_70, 1);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 0);
lean_inc(x_72);
lean_dec(x_70);
x_73 = !lean_is_exclusive(x_71);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; 
x_74 = lean_ctor_get(x_71, 3);
lean_inc(x_72);
x_75 = l_HashMapImp_insert___at_Lean_Closure_visitExpr___spec__3(x_74, x_30, x_72);
lean_ctor_set(x_71, 3, x_75);
x_31 = x_72;
x_32 = x_71;
goto block_66;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_76 = lean_ctor_get(x_71, 0);
x_77 = lean_ctor_get(x_71, 1);
x_78 = lean_ctor_get(x_71, 2);
x_79 = lean_ctor_get(x_71, 3);
x_80 = lean_ctor_get(x_71, 4);
x_81 = lean_ctor_get(x_71, 5);
x_82 = lean_ctor_get(x_71, 6);
x_83 = lean_ctor_get(x_71, 7);
x_84 = lean_ctor_get(x_71, 8);
lean_inc(x_84);
lean_inc(x_83);
lean_inc(x_82);
lean_inc(x_81);
lean_inc(x_80);
lean_inc(x_79);
lean_inc(x_78);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_71);
lean_inc(x_72);
x_85 = l_HashMapImp_insert___at_Lean_Closure_visitExpr___spec__3(x_79, x_30, x_72);
x_86 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_86, 0, x_76);
lean_ctor_set(x_86, 1, x_77);
lean_ctor_set(x_86, 2, x_78);
lean_ctor_set(x_86, 3, x_85);
lean_ctor_set(x_86, 4, x_80);
lean_ctor_set(x_86, 5, x_81);
lean_ctor_set(x_86, 6, x_82);
lean_ctor_set(x_86, 7, x_83);
lean_ctor_set(x_86, 8, x_84);
x_31 = x_72;
x_32 = x_86;
goto block_66;
}
}
else
{
uint8_t x_87; 
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_2);
lean_dec(x_1);
x_87 = !lean_is_exclusive(x_70);
if (x_87 == 0)
{
return x_70;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_70, 0);
x_89 = lean_ctor_get(x_70, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_70);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set(x_90, 1, x_89);
return x_90;
}
}
}
else
{
lean_object* x_91; 
lean_dec(x_30);
x_91 = lean_ctor_get(x_69, 0);
lean_inc(x_91);
lean_dec(x_69);
x_31 = x_91;
x_32 = x_3;
goto block_66;
}
}
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_141; uint8_t x_167; 
lean_dec(x_28);
lean_dec(x_1);
x_99 = lean_ctor_get(x_27, 2);
lean_inc(x_99);
x_100 = lean_ctor_get(x_27, 3);
lean_inc(x_100);
x_101 = lean_ctor_get(x_27, 4);
lean_inc(x_101);
lean_dec(x_27);
x_167 = l_Lean_Expr_hasLevelParam(x_100);
if (x_167 == 0)
{
uint8_t x_168; 
x_168 = l_Lean_Expr_hasFVar(x_100);
if (x_168 == 0)
{
uint8_t x_169; 
x_169 = l_Lean_Expr_hasMVar(x_100);
if (x_169 == 0)
{
x_102 = x_100;
x_103 = x_3;
goto block_140;
}
else
{
lean_object* x_170; 
x_170 = lean_box(0);
x_141 = x_170;
goto block_166;
}
}
else
{
lean_object* x_171; 
x_171 = lean_box(0);
x_141 = x_171;
goto block_166;
}
}
else
{
lean_object* x_172; 
x_172 = lean_box(0);
x_141 = x_172;
goto block_166;
}
block_140:
{
lean_object* x_104; uint8_t x_133; 
x_133 = l_Lean_Expr_hasLevelParam(x_101);
if (x_133 == 0)
{
uint8_t x_134; 
x_134 = l_Lean_Expr_hasFVar(x_101);
if (x_134 == 0)
{
uint8_t x_135; 
x_135 = l_Lean_Expr_hasMVar(x_101);
if (x_135 == 0)
{
lean_object* x_136; 
x_136 = l_Lean_Closure_mkLetDecl(x_99, x_102, x_101, x_2, x_103);
lean_dec(x_2);
return x_136;
}
else
{
lean_object* x_137; 
x_137 = lean_box(0);
x_104 = x_137;
goto block_132;
}
}
else
{
lean_object* x_138; 
x_138 = lean_box(0);
x_104 = x_138;
goto block_132;
}
}
else
{
lean_object* x_139; 
x_139 = lean_box(0);
x_104 = x_139;
goto block_132;
}
block_132:
{
lean_object* x_105; lean_object* x_106; 
lean_dec(x_104);
x_105 = lean_ctor_get(x_103, 3);
lean_inc(x_105);
x_106 = l_HashMapImp_find_x3f___at_Lean_Closure_visitExpr___spec__1(x_105, x_101);
lean_dec(x_105);
if (lean_obj_tag(x_106) == 0)
{
lean_object* x_107; 
lean_inc(x_2);
lean_inc(x_101);
x_107 = l_Lean_Closure_collectExprAux___main(x_101, x_2, x_103);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; lean_object* x_109; uint8_t x_110; 
x_108 = lean_ctor_get(x_107, 1);
lean_inc(x_108);
x_109 = lean_ctor_get(x_107, 0);
lean_inc(x_109);
lean_dec(x_107);
x_110 = !lean_is_exclusive(x_108);
if (x_110 == 0)
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_ctor_get(x_108, 3);
lean_inc(x_109);
x_112 = l_HashMapImp_insert___at_Lean_Closure_visitExpr___spec__3(x_111, x_101, x_109);
lean_ctor_set(x_108, 3, x_112);
x_113 = l_Lean_Closure_mkLetDecl(x_99, x_102, x_109, x_2, x_108);
lean_dec(x_2);
return x_113;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_114 = lean_ctor_get(x_108, 0);
x_115 = lean_ctor_get(x_108, 1);
x_116 = lean_ctor_get(x_108, 2);
x_117 = lean_ctor_get(x_108, 3);
x_118 = lean_ctor_get(x_108, 4);
x_119 = lean_ctor_get(x_108, 5);
x_120 = lean_ctor_get(x_108, 6);
x_121 = lean_ctor_get(x_108, 7);
x_122 = lean_ctor_get(x_108, 8);
lean_inc(x_122);
lean_inc(x_121);
lean_inc(x_120);
lean_inc(x_119);
lean_inc(x_118);
lean_inc(x_117);
lean_inc(x_116);
lean_inc(x_115);
lean_inc(x_114);
lean_dec(x_108);
lean_inc(x_109);
x_123 = l_HashMapImp_insert___at_Lean_Closure_visitExpr___spec__3(x_117, x_101, x_109);
x_124 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_124, 0, x_114);
lean_ctor_set(x_124, 1, x_115);
lean_ctor_set(x_124, 2, x_116);
lean_ctor_set(x_124, 3, x_123);
lean_ctor_set(x_124, 4, x_118);
lean_ctor_set(x_124, 5, x_119);
lean_ctor_set(x_124, 6, x_120);
lean_ctor_set(x_124, 7, x_121);
lean_ctor_set(x_124, 8, x_122);
x_125 = l_Lean_Closure_mkLetDecl(x_99, x_102, x_109, x_2, x_124);
lean_dec(x_2);
return x_125;
}
}
else
{
uint8_t x_126; 
lean_dec(x_102);
lean_dec(x_101);
lean_dec(x_99);
lean_dec(x_2);
x_126 = !lean_is_exclusive(x_107);
if (x_126 == 0)
{
return x_107;
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_127 = lean_ctor_get(x_107, 0);
x_128 = lean_ctor_get(x_107, 1);
lean_inc(x_128);
lean_inc(x_127);
lean_dec(x_107);
x_129 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_129, 0, x_127);
lean_ctor_set(x_129, 1, x_128);
return x_129;
}
}
}
else
{
lean_object* x_130; lean_object* x_131; 
lean_dec(x_101);
x_130 = lean_ctor_get(x_106, 0);
lean_inc(x_130);
lean_dec(x_106);
x_131 = l_Lean_Closure_mkLetDecl(x_99, x_102, x_130, x_2, x_103);
lean_dec(x_2);
return x_131;
}
}
}
block_166:
{
lean_object* x_142; lean_object* x_143; 
lean_dec(x_141);
x_142 = lean_ctor_get(x_3, 3);
lean_inc(x_142);
x_143 = l_HashMapImp_find_x3f___at_Lean_Closure_visitExpr___spec__1(x_142, x_100);
lean_dec(x_142);
if (lean_obj_tag(x_143) == 0)
{
lean_object* x_144; 
lean_inc(x_2);
lean_inc(x_100);
x_144 = l_Lean_Closure_collectExprAux___main(x_100, x_2, x_3);
if (lean_obj_tag(x_144) == 0)
{
lean_object* x_145; lean_object* x_146; uint8_t x_147; 
x_145 = lean_ctor_get(x_144, 1);
lean_inc(x_145);
x_146 = lean_ctor_get(x_144, 0);
lean_inc(x_146);
lean_dec(x_144);
x_147 = !lean_is_exclusive(x_145);
if (x_147 == 0)
{
lean_object* x_148; lean_object* x_149; 
x_148 = lean_ctor_get(x_145, 3);
lean_inc(x_146);
x_149 = l_HashMapImp_insert___at_Lean_Closure_visitExpr___spec__3(x_148, x_100, x_146);
lean_ctor_set(x_145, 3, x_149);
x_102 = x_146;
x_103 = x_145;
goto block_140;
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_150 = lean_ctor_get(x_145, 0);
x_151 = lean_ctor_get(x_145, 1);
x_152 = lean_ctor_get(x_145, 2);
x_153 = lean_ctor_get(x_145, 3);
x_154 = lean_ctor_get(x_145, 4);
x_155 = lean_ctor_get(x_145, 5);
x_156 = lean_ctor_get(x_145, 6);
x_157 = lean_ctor_get(x_145, 7);
x_158 = lean_ctor_get(x_145, 8);
lean_inc(x_158);
lean_inc(x_157);
lean_inc(x_156);
lean_inc(x_155);
lean_inc(x_154);
lean_inc(x_153);
lean_inc(x_152);
lean_inc(x_151);
lean_inc(x_150);
lean_dec(x_145);
lean_inc(x_146);
x_159 = l_HashMapImp_insert___at_Lean_Closure_visitExpr___spec__3(x_153, x_100, x_146);
x_160 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_160, 0, x_150);
lean_ctor_set(x_160, 1, x_151);
lean_ctor_set(x_160, 2, x_152);
lean_ctor_set(x_160, 3, x_159);
lean_ctor_set(x_160, 4, x_154);
lean_ctor_set(x_160, 5, x_155);
lean_ctor_set(x_160, 6, x_156);
lean_ctor_set(x_160, 7, x_157);
lean_ctor_set(x_160, 8, x_158);
x_102 = x_146;
x_103 = x_160;
goto block_140;
}
}
else
{
uint8_t x_161; 
lean_dec(x_101);
lean_dec(x_100);
lean_dec(x_99);
lean_dec(x_2);
x_161 = !lean_is_exclusive(x_144);
if (x_161 == 0)
{
return x_144;
}
else
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_162 = lean_ctor_get(x_144, 0);
x_163 = lean_ctor_get(x_144, 1);
lean_inc(x_163);
lean_inc(x_162);
lean_dec(x_144);
x_164 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_164, 0, x_162);
lean_ctor_set(x_164, 1, x_163);
return x_164;
}
}
}
else
{
lean_object* x_165; 
lean_dec(x_100);
x_165 = lean_ctor_get(x_143, 0);
lean_inc(x_165);
lean_dec(x_143);
x_102 = x_165;
x_103 = x_3;
goto block_140;
}
}
}
}
}
case 2:
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_210; lean_object* x_211; 
x_173 = lean_ctor_get(x_1, 0);
lean_inc(x_173);
x_210 = lean_ctor_get(x_2, 0);
lean_inc(x_210);
x_211 = lean_metavar_ctx_find_decl(x_210, x_173);
if (lean_obj_tag(x_211) == 0)
{
lean_object* x_212; lean_object* x_213; 
lean_dec(x_2);
lean_dec(x_1);
x_212 = l_Lean_MetavarContext_getDecl___closed__2;
x_213 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_213, 0, x_212);
lean_ctor_set(x_213, 1, x_3);
return x_213;
}
else
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; uint8_t x_242; 
x_214 = lean_ctor_get(x_211, 0);
lean_inc(x_214);
lean_dec(x_211);
x_215 = lean_ctor_get(x_214, 2);
lean_inc(x_215);
lean_dec(x_214);
x_242 = l_Lean_Expr_hasLevelParam(x_215);
if (x_242 == 0)
{
uint8_t x_243; 
x_243 = l_Lean_Expr_hasFVar(x_215);
if (x_243 == 0)
{
uint8_t x_244; 
x_244 = l_Lean_Expr_hasMVar(x_215);
if (x_244 == 0)
{
x_174 = x_215;
x_175 = x_3;
goto block_209;
}
else
{
lean_object* x_245; 
x_245 = lean_box(0);
x_216 = x_245;
goto block_241;
}
}
else
{
lean_object* x_246; 
x_246 = lean_box(0);
x_216 = x_246;
goto block_241;
}
}
else
{
lean_object* x_247; 
x_247 = lean_box(0);
x_216 = x_247;
goto block_241;
}
block_241:
{
lean_object* x_217; lean_object* x_218; 
lean_dec(x_216);
x_217 = lean_ctor_get(x_3, 3);
lean_inc(x_217);
x_218 = l_HashMapImp_find_x3f___at_Lean_Closure_visitExpr___spec__1(x_217, x_215);
lean_dec(x_217);
if (lean_obj_tag(x_218) == 0)
{
lean_object* x_219; 
lean_inc(x_2);
lean_inc(x_215);
x_219 = l_Lean_Closure_collectExprAux___main(x_215, x_2, x_3);
if (lean_obj_tag(x_219) == 0)
{
lean_object* x_220; lean_object* x_221; uint8_t x_222; 
x_220 = lean_ctor_get(x_219, 1);
lean_inc(x_220);
x_221 = lean_ctor_get(x_219, 0);
lean_inc(x_221);
lean_dec(x_219);
x_222 = !lean_is_exclusive(x_220);
if (x_222 == 0)
{
lean_object* x_223; lean_object* x_224; 
x_223 = lean_ctor_get(x_220, 3);
lean_inc(x_221);
x_224 = l_HashMapImp_insert___at_Lean_Closure_visitExpr___spec__3(x_223, x_215, x_221);
lean_ctor_set(x_220, 3, x_224);
x_174 = x_221;
x_175 = x_220;
goto block_209;
}
else
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; 
x_225 = lean_ctor_get(x_220, 0);
x_226 = lean_ctor_get(x_220, 1);
x_227 = lean_ctor_get(x_220, 2);
x_228 = lean_ctor_get(x_220, 3);
x_229 = lean_ctor_get(x_220, 4);
x_230 = lean_ctor_get(x_220, 5);
x_231 = lean_ctor_get(x_220, 6);
x_232 = lean_ctor_get(x_220, 7);
x_233 = lean_ctor_get(x_220, 8);
lean_inc(x_233);
lean_inc(x_232);
lean_inc(x_231);
lean_inc(x_230);
lean_inc(x_229);
lean_inc(x_228);
lean_inc(x_227);
lean_inc(x_226);
lean_inc(x_225);
lean_dec(x_220);
lean_inc(x_221);
x_234 = l_HashMapImp_insert___at_Lean_Closure_visitExpr___spec__3(x_228, x_215, x_221);
x_235 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_235, 0, x_225);
lean_ctor_set(x_235, 1, x_226);
lean_ctor_set(x_235, 2, x_227);
lean_ctor_set(x_235, 3, x_234);
lean_ctor_set(x_235, 4, x_229);
lean_ctor_set(x_235, 5, x_230);
lean_ctor_set(x_235, 6, x_231);
lean_ctor_set(x_235, 7, x_232);
lean_ctor_set(x_235, 8, x_233);
x_174 = x_221;
x_175 = x_235;
goto block_209;
}
}
else
{
uint8_t x_236; 
lean_dec(x_215);
lean_dec(x_2);
lean_dec(x_1);
x_236 = !lean_is_exclusive(x_219);
if (x_236 == 0)
{
return x_219;
}
else
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; 
x_237 = lean_ctor_get(x_219, 0);
x_238 = lean_ctor_get(x_219, 1);
lean_inc(x_238);
lean_inc(x_237);
lean_dec(x_219);
x_239 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_239, 0, x_237);
lean_ctor_set(x_239, 1, x_238);
return x_239;
}
}
}
else
{
lean_object* x_240; 
lean_dec(x_215);
x_240 = lean_ctor_get(x_218, 0);
lean_inc(x_240);
lean_dec(x_218);
x_174 = x_240;
x_175 = x_3;
goto block_209;
}
}
}
block_209:
{
lean_object* x_176; lean_object* x_177; uint8_t x_178; 
x_176 = lean_box(0);
x_177 = l_Lean_Closure_mkLocalDecl(x_176, x_174, x_2, x_175);
lean_dec(x_2);
x_178 = !lean_is_exclusive(x_177);
if (x_178 == 0)
{
lean_object* x_179; uint8_t x_180; 
x_179 = lean_ctor_get(x_177, 1);
x_180 = !lean_is_exclusive(x_179);
if (x_180 == 0)
{
lean_object* x_181; lean_object* x_182; 
x_181 = lean_ctor_get(x_179, 8);
x_182 = lean_array_push(x_181, x_1);
lean_ctor_set(x_179, 8, x_182);
return x_177;
}
else
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; 
x_183 = lean_ctor_get(x_179, 0);
x_184 = lean_ctor_get(x_179, 1);
x_185 = lean_ctor_get(x_179, 2);
x_186 = lean_ctor_get(x_179, 3);
x_187 = lean_ctor_get(x_179, 4);
x_188 = lean_ctor_get(x_179, 5);
x_189 = lean_ctor_get(x_179, 6);
x_190 = lean_ctor_get(x_179, 7);
x_191 = lean_ctor_get(x_179, 8);
lean_inc(x_191);
lean_inc(x_190);
lean_inc(x_189);
lean_inc(x_188);
lean_inc(x_187);
lean_inc(x_186);
lean_inc(x_185);
lean_inc(x_184);
lean_inc(x_183);
lean_dec(x_179);
x_192 = lean_array_push(x_191, x_1);
x_193 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_193, 0, x_183);
lean_ctor_set(x_193, 1, x_184);
lean_ctor_set(x_193, 2, x_185);
lean_ctor_set(x_193, 3, x_186);
lean_ctor_set(x_193, 4, x_187);
lean_ctor_set(x_193, 5, x_188);
lean_ctor_set(x_193, 6, x_189);
lean_ctor_set(x_193, 7, x_190);
lean_ctor_set(x_193, 8, x_192);
lean_ctor_set(x_177, 1, x_193);
return x_177;
}
}
else
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; 
x_194 = lean_ctor_get(x_177, 1);
x_195 = lean_ctor_get(x_177, 0);
lean_inc(x_194);
lean_inc(x_195);
lean_dec(x_177);
x_196 = lean_ctor_get(x_194, 0);
lean_inc(x_196);
x_197 = lean_ctor_get(x_194, 1);
lean_inc(x_197);
x_198 = lean_ctor_get(x_194, 2);
lean_inc(x_198);
x_199 = lean_ctor_get(x_194, 3);
lean_inc(x_199);
x_200 = lean_ctor_get(x_194, 4);
lean_inc(x_200);
x_201 = lean_ctor_get(x_194, 5);
lean_inc(x_201);
x_202 = lean_ctor_get(x_194, 6);
lean_inc(x_202);
x_203 = lean_ctor_get(x_194, 7);
lean_inc(x_203);
x_204 = lean_ctor_get(x_194, 8);
lean_inc(x_204);
if (lean_is_exclusive(x_194)) {
 lean_ctor_release(x_194, 0);
 lean_ctor_release(x_194, 1);
 lean_ctor_release(x_194, 2);
 lean_ctor_release(x_194, 3);
 lean_ctor_release(x_194, 4);
 lean_ctor_release(x_194, 5);
 lean_ctor_release(x_194, 6);
 lean_ctor_release(x_194, 7);
 lean_ctor_release(x_194, 8);
 x_205 = x_194;
} else {
 lean_dec_ref(x_194);
 x_205 = lean_box(0);
}
x_206 = lean_array_push(x_204, x_1);
if (lean_is_scalar(x_205)) {
 x_207 = lean_alloc_ctor(0, 9, 0);
} else {
 x_207 = x_205;
}
lean_ctor_set(x_207, 0, x_196);
lean_ctor_set(x_207, 1, x_197);
lean_ctor_set(x_207, 2, x_198);
lean_ctor_set(x_207, 3, x_199);
lean_ctor_set(x_207, 4, x_200);
lean_ctor_set(x_207, 5, x_201);
lean_ctor_set(x_207, 6, x_202);
lean_ctor_set(x_207, 7, x_203);
lean_ctor_set(x_207, 8, x_206);
x_208 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_208, 0, x_195);
lean_ctor_set(x_208, 1, x_207);
return x_208;
}
}
}
case 3:
{
lean_object* x_248; lean_object* x_249; uint8_t x_250; 
x_248 = lean_ctor_get(x_1, 0);
lean_inc(x_248);
x_249 = l_Lean_Closure_collectLevel(x_248, x_2, x_3);
lean_dec(x_2);
x_250 = !lean_is_exclusive(x_249);
if (x_250 == 0)
{
lean_object* x_251; lean_object* x_252; 
x_251 = lean_ctor_get(x_249, 0);
x_252 = lean_expr_update_sort(x_1, x_251);
lean_ctor_set(x_249, 0, x_252);
return x_249;
}
else
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; 
x_253 = lean_ctor_get(x_249, 0);
x_254 = lean_ctor_get(x_249, 1);
lean_inc(x_254);
lean_inc(x_253);
lean_dec(x_249);
x_255 = lean_expr_update_sort(x_1, x_253);
x_256 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_256, 0, x_255);
lean_ctor_set(x_256, 1, x_254);
return x_256;
}
}
case 4:
{
lean_object* x_257; lean_object* x_258; uint8_t x_259; 
x_257 = lean_ctor_get(x_1, 1);
lean_inc(x_257);
x_258 = l_List_mapM___main___at_Lean_Closure_collectExprAux___main___spec__1(x_257, x_2, x_3);
lean_dec(x_2);
x_259 = !lean_is_exclusive(x_258);
if (x_259 == 0)
{
lean_object* x_260; lean_object* x_261; 
x_260 = lean_ctor_get(x_258, 0);
x_261 = lean_expr_update_const(x_1, x_260);
lean_ctor_set(x_258, 0, x_261);
return x_258;
}
else
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; 
x_262 = lean_ctor_get(x_258, 0);
x_263 = lean_ctor_get(x_258, 1);
lean_inc(x_263);
lean_inc(x_262);
lean_dec(x_258);
x_264 = lean_expr_update_const(x_1, x_262);
x_265 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_265, 0, x_264);
lean_ctor_set(x_265, 1, x_263);
return x_265;
}
}
case 5:
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_312; uint8_t x_338; 
x_266 = lean_ctor_get(x_1, 0);
lean_inc(x_266);
x_267 = lean_ctor_get(x_1, 1);
lean_inc(x_267);
x_338 = l_Lean_Expr_hasLevelParam(x_266);
if (x_338 == 0)
{
uint8_t x_339; 
x_339 = l_Lean_Expr_hasFVar(x_266);
if (x_339 == 0)
{
uint8_t x_340; 
x_340 = l_Lean_Expr_hasMVar(x_266);
if (x_340 == 0)
{
x_268 = x_266;
x_269 = x_3;
goto block_311;
}
else
{
lean_object* x_341; 
x_341 = lean_box(0);
x_312 = x_341;
goto block_337;
}
}
else
{
lean_object* x_342; 
x_342 = lean_box(0);
x_312 = x_342;
goto block_337;
}
}
else
{
lean_object* x_343; 
x_343 = lean_box(0);
x_312 = x_343;
goto block_337;
}
block_311:
{
lean_object* x_270; lean_object* x_271; lean_object* x_279; uint8_t x_305; 
x_305 = l_Lean_Expr_hasLevelParam(x_267);
if (x_305 == 0)
{
uint8_t x_306; 
x_306 = l_Lean_Expr_hasFVar(x_267);
if (x_306 == 0)
{
uint8_t x_307; 
x_307 = l_Lean_Expr_hasMVar(x_267);
if (x_307 == 0)
{
lean_dec(x_2);
x_270 = x_267;
x_271 = x_269;
goto block_278;
}
else
{
lean_object* x_308; 
x_308 = lean_box(0);
x_279 = x_308;
goto block_304;
}
}
else
{
lean_object* x_309; 
x_309 = lean_box(0);
x_279 = x_309;
goto block_304;
}
}
else
{
lean_object* x_310; 
x_310 = lean_box(0);
x_279 = x_310;
goto block_304;
}
block_278:
{
if (lean_obj_tag(x_1) == 5)
{
lean_object* x_272; lean_object* x_273; 
x_272 = lean_expr_update_app(x_1, x_268, x_270);
x_273 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_273, 0, x_272);
lean_ctor_set(x_273, 1, x_271);
return x_273;
}
else
{
lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; 
lean_dec(x_270);
lean_dec(x_268);
lean_dec(x_1);
x_274 = l_Lean_Expr_Inhabited;
x_275 = l_Lean_Expr_updateApp_x21___closed__1;
x_276 = lean_panic_fn(x_274, x_275);
x_277 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_277, 0, x_276);
lean_ctor_set(x_277, 1, x_271);
return x_277;
}
}
block_304:
{
lean_object* x_280; lean_object* x_281; 
lean_dec(x_279);
x_280 = lean_ctor_get(x_269, 3);
lean_inc(x_280);
x_281 = l_HashMapImp_find_x3f___at_Lean_Closure_visitExpr___spec__1(x_280, x_267);
lean_dec(x_280);
if (lean_obj_tag(x_281) == 0)
{
lean_object* x_282; 
lean_inc(x_267);
x_282 = l_Lean_Closure_collectExprAux___main(x_267, x_2, x_269);
if (lean_obj_tag(x_282) == 0)
{
lean_object* x_283; lean_object* x_284; uint8_t x_285; 
x_283 = lean_ctor_get(x_282, 1);
lean_inc(x_283);
x_284 = lean_ctor_get(x_282, 0);
lean_inc(x_284);
lean_dec(x_282);
x_285 = !lean_is_exclusive(x_283);
if (x_285 == 0)
{
lean_object* x_286; lean_object* x_287; 
x_286 = lean_ctor_get(x_283, 3);
lean_inc(x_284);
x_287 = l_HashMapImp_insert___at_Lean_Closure_visitExpr___spec__3(x_286, x_267, x_284);
lean_ctor_set(x_283, 3, x_287);
x_270 = x_284;
x_271 = x_283;
goto block_278;
}
else
{
lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; 
x_288 = lean_ctor_get(x_283, 0);
x_289 = lean_ctor_get(x_283, 1);
x_290 = lean_ctor_get(x_283, 2);
x_291 = lean_ctor_get(x_283, 3);
x_292 = lean_ctor_get(x_283, 4);
x_293 = lean_ctor_get(x_283, 5);
x_294 = lean_ctor_get(x_283, 6);
x_295 = lean_ctor_get(x_283, 7);
x_296 = lean_ctor_get(x_283, 8);
lean_inc(x_296);
lean_inc(x_295);
lean_inc(x_294);
lean_inc(x_293);
lean_inc(x_292);
lean_inc(x_291);
lean_inc(x_290);
lean_inc(x_289);
lean_inc(x_288);
lean_dec(x_283);
lean_inc(x_284);
x_297 = l_HashMapImp_insert___at_Lean_Closure_visitExpr___spec__3(x_291, x_267, x_284);
x_298 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_298, 0, x_288);
lean_ctor_set(x_298, 1, x_289);
lean_ctor_set(x_298, 2, x_290);
lean_ctor_set(x_298, 3, x_297);
lean_ctor_set(x_298, 4, x_292);
lean_ctor_set(x_298, 5, x_293);
lean_ctor_set(x_298, 6, x_294);
lean_ctor_set(x_298, 7, x_295);
lean_ctor_set(x_298, 8, x_296);
x_270 = x_284;
x_271 = x_298;
goto block_278;
}
}
else
{
uint8_t x_299; 
lean_dec(x_268);
lean_dec(x_267);
lean_dec(x_1);
x_299 = !lean_is_exclusive(x_282);
if (x_299 == 0)
{
return x_282;
}
else
{
lean_object* x_300; lean_object* x_301; lean_object* x_302; 
x_300 = lean_ctor_get(x_282, 0);
x_301 = lean_ctor_get(x_282, 1);
lean_inc(x_301);
lean_inc(x_300);
lean_dec(x_282);
x_302 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_302, 0, x_300);
lean_ctor_set(x_302, 1, x_301);
return x_302;
}
}
}
else
{
lean_object* x_303; 
lean_dec(x_267);
lean_dec(x_2);
x_303 = lean_ctor_get(x_281, 0);
lean_inc(x_303);
lean_dec(x_281);
x_270 = x_303;
x_271 = x_269;
goto block_278;
}
}
}
block_337:
{
lean_object* x_313; lean_object* x_314; 
lean_dec(x_312);
x_313 = lean_ctor_get(x_3, 3);
lean_inc(x_313);
x_314 = l_HashMapImp_find_x3f___at_Lean_Closure_visitExpr___spec__1(x_313, x_266);
lean_dec(x_313);
if (lean_obj_tag(x_314) == 0)
{
lean_object* x_315; 
lean_inc(x_2);
lean_inc(x_266);
x_315 = l_Lean_Closure_collectExprAux___main(x_266, x_2, x_3);
if (lean_obj_tag(x_315) == 0)
{
lean_object* x_316; lean_object* x_317; uint8_t x_318; 
x_316 = lean_ctor_get(x_315, 1);
lean_inc(x_316);
x_317 = lean_ctor_get(x_315, 0);
lean_inc(x_317);
lean_dec(x_315);
x_318 = !lean_is_exclusive(x_316);
if (x_318 == 0)
{
lean_object* x_319; lean_object* x_320; 
x_319 = lean_ctor_get(x_316, 3);
lean_inc(x_317);
x_320 = l_HashMapImp_insert___at_Lean_Closure_visitExpr___spec__3(x_319, x_266, x_317);
lean_ctor_set(x_316, 3, x_320);
x_268 = x_317;
x_269 = x_316;
goto block_311;
}
else
{
lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; 
x_321 = lean_ctor_get(x_316, 0);
x_322 = lean_ctor_get(x_316, 1);
x_323 = lean_ctor_get(x_316, 2);
x_324 = lean_ctor_get(x_316, 3);
x_325 = lean_ctor_get(x_316, 4);
x_326 = lean_ctor_get(x_316, 5);
x_327 = lean_ctor_get(x_316, 6);
x_328 = lean_ctor_get(x_316, 7);
x_329 = lean_ctor_get(x_316, 8);
lean_inc(x_329);
lean_inc(x_328);
lean_inc(x_327);
lean_inc(x_326);
lean_inc(x_325);
lean_inc(x_324);
lean_inc(x_323);
lean_inc(x_322);
lean_inc(x_321);
lean_dec(x_316);
lean_inc(x_317);
x_330 = l_HashMapImp_insert___at_Lean_Closure_visitExpr___spec__3(x_324, x_266, x_317);
x_331 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_331, 0, x_321);
lean_ctor_set(x_331, 1, x_322);
lean_ctor_set(x_331, 2, x_323);
lean_ctor_set(x_331, 3, x_330);
lean_ctor_set(x_331, 4, x_325);
lean_ctor_set(x_331, 5, x_326);
lean_ctor_set(x_331, 6, x_327);
lean_ctor_set(x_331, 7, x_328);
lean_ctor_set(x_331, 8, x_329);
x_268 = x_317;
x_269 = x_331;
goto block_311;
}
}
else
{
uint8_t x_332; 
lean_dec(x_267);
lean_dec(x_266);
lean_dec(x_2);
lean_dec(x_1);
x_332 = !lean_is_exclusive(x_315);
if (x_332 == 0)
{
return x_315;
}
else
{
lean_object* x_333; lean_object* x_334; lean_object* x_335; 
x_333 = lean_ctor_get(x_315, 0);
x_334 = lean_ctor_get(x_315, 1);
lean_inc(x_334);
lean_inc(x_333);
lean_dec(x_315);
x_335 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_335, 0, x_333);
lean_ctor_set(x_335, 1, x_334);
return x_335;
}
}
}
else
{
lean_object* x_336; 
lean_dec(x_266);
x_336 = lean_ctor_get(x_314, 0);
lean_inc(x_336);
lean_dec(x_314);
x_268 = x_336;
x_269 = x_3;
goto block_311;
}
}
}
case 6:
{
lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_392; uint8_t x_418; 
x_344 = lean_ctor_get(x_1, 1);
lean_inc(x_344);
x_345 = lean_ctor_get(x_1, 2);
lean_inc(x_345);
x_418 = l_Lean_Expr_hasLevelParam(x_344);
if (x_418 == 0)
{
uint8_t x_419; 
x_419 = l_Lean_Expr_hasFVar(x_344);
if (x_419 == 0)
{
uint8_t x_420; 
x_420 = l_Lean_Expr_hasMVar(x_344);
if (x_420 == 0)
{
x_346 = x_344;
x_347 = x_3;
goto block_391;
}
else
{
lean_object* x_421; 
x_421 = lean_box(0);
x_392 = x_421;
goto block_417;
}
}
else
{
lean_object* x_422; 
x_422 = lean_box(0);
x_392 = x_422;
goto block_417;
}
}
else
{
lean_object* x_423; 
x_423 = lean_box(0);
x_392 = x_423;
goto block_417;
}
block_391:
{
lean_object* x_348; lean_object* x_349; lean_object* x_359; uint8_t x_385; 
x_385 = l_Lean_Expr_hasLevelParam(x_345);
if (x_385 == 0)
{
uint8_t x_386; 
x_386 = l_Lean_Expr_hasFVar(x_345);
if (x_386 == 0)
{
uint8_t x_387; 
x_387 = l_Lean_Expr_hasMVar(x_345);
if (x_387 == 0)
{
lean_dec(x_2);
x_348 = x_345;
x_349 = x_347;
goto block_358;
}
else
{
lean_object* x_388; 
x_388 = lean_box(0);
x_359 = x_388;
goto block_384;
}
}
else
{
lean_object* x_389; 
x_389 = lean_box(0);
x_359 = x_389;
goto block_384;
}
}
else
{
lean_object* x_390; 
x_390 = lean_box(0);
x_359 = x_390;
goto block_384;
}
block_358:
{
if (lean_obj_tag(x_1) == 6)
{
uint64_t x_350; uint8_t x_351; lean_object* x_352; lean_object* x_353; 
x_350 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
x_351 = (uint8_t)((x_350 << 24) >> 61);
x_352 = lean_expr_update_lambda(x_1, x_351, x_346, x_348);
x_353 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_353, 0, x_352);
lean_ctor_set(x_353, 1, x_349);
return x_353;
}
else
{
lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; 
lean_dec(x_348);
lean_dec(x_346);
lean_dec(x_1);
x_354 = l_Lean_Expr_Inhabited;
x_355 = l_Lean_Expr_updateLambdaE_x21___closed__1;
x_356 = lean_panic_fn(x_354, x_355);
x_357 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_357, 0, x_356);
lean_ctor_set(x_357, 1, x_349);
return x_357;
}
}
block_384:
{
lean_object* x_360; lean_object* x_361; 
lean_dec(x_359);
x_360 = lean_ctor_get(x_347, 3);
lean_inc(x_360);
x_361 = l_HashMapImp_find_x3f___at_Lean_Closure_visitExpr___spec__1(x_360, x_345);
lean_dec(x_360);
if (lean_obj_tag(x_361) == 0)
{
lean_object* x_362; 
lean_inc(x_345);
x_362 = l_Lean_Closure_collectExprAux___main(x_345, x_2, x_347);
if (lean_obj_tag(x_362) == 0)
{
lean_object* x_363; lean_object* x_364; uint8_t x_365; 
x_363 = lean_ctor_get(x_362, 1);
lean_inc(x_363);
x_364 = lean_ctor_get(x_362, 0);
lean_inc(x_364);
lean_dec(x_362);
x_365 = !lean_is_exclusive(x_363);
if (x_365 == 0)
{
lean_object* x_366; lean_object* x_367; 
x_366 = lean_ctor_get(x_363, 3);
lean_inc(x_364);
x_367 = l_HashMapImp_insert___at_Lean_Closure_visitExpr___spec__3(x_366, x_345, x_364);
lean_ctor_set(x_363, 3, x_367);
x_348 = x_364;
x_349 = x_363;
goto block_358;
}
else
{
lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; 
x_368 = lean_ctor_get(x_363, 0);
x_369 = lean_ctor_get(x_363, 1);
x_370 = lean_ctor_get(x_363, 2);
x_371 = lean_ctor_get(x_363, 3);
x_372 = lean_ctor_get(x_363, 4);
x_373 = lean_ctor_get(x_363, 5);
x_374 = lean_ctor_get(x_363, 6);
x_375 = lean_ctor_get(x_363, 7);
x_376 = lean_ctor_get(x_363, 8);
lean_inc(x_376);
lean_inc(x_375);
lean_inc(x_374);
lean_inc(x_373);
lean_inc(x_372);
lean_inc(x_371);
lean_inc(x_370);
lean_inc(x_369);
lean_inc(x_368);
lean_dec(x_363);
lean_inc(x_364);
x_377 = l_HashMapImp_insert___at_Lean_Closure_visitExpr___spec__3(x_371, x_345, x_364);
x_378 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_378, 0, x_368);
lean_ctor_set(x_378, 1, x_369);
lean_ctor_set(x_378, 2, x_370);
lean_ctor_set(x_378, 3, x_377);
lean_ctor_set(x_378, 4, x_372);
lean_ctor_set(x_378, 5, x_373);
lean_ctor_set(x_378, 6, x_374);
lean_ctor_set(x_378, 7, x_375);
lean_ctor_set(x_378, 8, x_376);
x_348 = x_364;
x_349 = x_378;
goto block_358;
}
}
else
{
uint8_t x_379; 
lean_dec(x_346);
lean_dec(x_345);
lean_dec(x_1);
x_379 = !lean_is_exclusive(x_362);
if (x_379 == 0)
{
return x_362;
}
else
{
lean_object* x_380; lean_object* x_381; lean_object* x_382; 
x_380 = lean_ctor_get(x_362, 0);
x_381 = lean_ctor_get(x_362, 1);
lean_inc(x_381);
lean_inc(x_380);
lean_dec(x_362);
x_382 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_382, 0, x_380);
lean_ctor_set(x_382, 1, x_381);
return x_382;
}
}
}
else
{
lean_object* x_383; 
lean_dec(x_345);
lean_dec(x_2);
x_383 = lean_ctor_get(x_361, 0);
lean_inc(x_383);
lean_dec(x_361);
x_348 = x_383;
x_349 = x_347;
goto block_358;
}
}
}
block_417:
{
lean_object* x_393; lean_object* x_394; 
lean_dec(x_392);
x_393 = lean_ctor_get(x_3, 3);
lean_inc(x_393);
x_394 = l_HashMapImp_find_x3f___at_Lean_Closure_visitExpr___spec__1(x_393, x_344);
lean_dec(x_393);
if (lean_obj_tag(x_394) == 0)
{
lean_object* x_395; 
lean_inc(x_2);
lean_inc(x_344);
x_395 = l_Lean_Closure_collectExprAux___main(x_344, x_2, x_3);
if (lean_obj_tag(x_395) == 0)
{
lean_object* x_396; lean_object* x_397; uint8_t x_398; 
x_396 = lean_ctor_get(x_395, 1);
lean_inc(x_396);
x_397 = lean_ctor_get(x_395, 0);
lean_inc(x_397);
lean_dec(x_395);
x_398 = !lean_is_exclusive(x_396);
if (x_398 == 0)
{
lean_object* x_399; lean_object* x_400; 
x_399 = lean_ctor_get(x_396, 3);
lean_inc(x_397);
x_400 = l_HashMapImp_insert___at_Lean_Closure_visitExpr___spec__3(x_399, x_344, x_397);
lean_ctor_set(x_396, 3, x_400);
x_346 = x_397;
x_347 = x_396;
goto block_391;
}
else
{
lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; 
x_401 = lean_ctor_get(x_396, 0);
x_402 = lean_ctor_get(x_396, 1);
x_403 = lean_ctor_get(x_396, 2);
x_404 = lean_ctor_get(x_396, 3);
x_405 = lean_ctor_get(x_396, 4);
x_406 = lean_ctor_get(x_396, 5);
x_407 = lean_ctor_get(x_396, 6);
x_408 = lean_ctor_get(x_396, 7);
x_409 = lean_ctor_get(x_396, 8);
lean_inc(x_409);
lean_inc(x_408);
lean_inc(x_407);
lean_inc(x_406);
lean_inc(x_405);
lean_inc(x_404);
lean_inc(x_403);
lean_inc(x_402);
lean_inc(x_401);
lean_dec(x_396);
lean_inc(x_397);
x_410 = l_HashMapImp_insert___at_Lean_Closure_visitExpr___spec__3(x_404, x_344, x_397);
x_411 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_411, 0, x_401);
lean_ctor_set(x_411, 1, x_402);
lean_ctor_set(x_411, 2, x_403);
lean_ctor_set(x_411, 3, x_410);
lean_ctor_set(x_411, 4, x_405);
lean_ctor_set(x_411, 5, x_406);
lean_ctor_set(x_411, 6, x_407);
lean_ctor_set(x_411, 7, x_408);
lean_ctor_set(x_411, 8, x_409);
x_346 = x_397;
x_347 = x_411;
goto block_391;
}
}
else
{
uint8_t x_412; 
lean_dec(x_345);
lean_dec(x_344);
lean_dec(x_2);
lean_dec(x_1);
x_412 = !lean_is_exclusive(x_395);
if (x_412 == 0)
{
return x_395;
}
else
{
lean_object* x_413; lean_object* x_414; lean_object* x_415; 
x_413 = lean_ctor_get(x_395, 0);
x_414 = lean_ctor_get(x_395, 1);
lean_inc(x_414);
lean_inc(x_413);
lean_dec(x_395);
x_415 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_415, 0, x_413);
lean_ctor_set(x_415, 1, x_414);
return x_415;
}
}
}
else
{
lean_object* x_416; 
lean_dec(x_344);
x_416 = lean_ctor_get(x_394, 0);
lean_inc(x_416);
lean_dec(x_394);
x_346 = x_416;
x_347 = x_3;
goto block_391;
}
}
}
case 7:
{
lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_472; uint8_t x_498; 
x_424 = lean_ctor_get(x_1, 1);
lean_inc(x_424);
x_425 = lean_ctor_get(x_1, 2);
lean_inc(x_425);
x_498 = l_Lean_Expr_hasLevelParam(x_424);
if (x_498 == 0)
{
uint8_t x_499; 
x_499 = l_Lean_Expr_hasFVar(x_424);
if (x_499 == 0)
{
uint8_t x_500; 
x_500 = l_Lean_Expr_hasMVar(x_424);
if (x_500 == 0)
{
x_426 = x_424;
x_427 = x_3;
goto block_471;
}
else
{
lean_object* x_501; 
x_501 = lean_box(0);
x_472 = x_501;
goto block_497;
}
}
else
{
lean_object* x_502; 
x_502 = lean_box(0);
x_472 = x_502;
goto block_497;
}
}
else
{
lean_object* x_503; 
x_503 = lean_box(0);
x_472 = x_503;
goto block_497;
}
block_471:
{
lean_object* x_428; lean_object* x_429; lean_object* x_439; uint8_t x_465; 
x_465 = l_Lean_Expr_hasLevelParam(x_425);
if (x_465 == 0)
{
uint8_t x_466; 
x_466 = l_Lean_Expr_hasFVar(x_425);
if (x_466 == 0)
{
uint8_t x_467; 
x_467 = l_Lean_Expr_hasMVar(x_425);
if (x_467 == 0)
{
lean_dec(x_2);
x_428 = x_425;
x_429 = x_427;
goto block_438;
}
else
{
lean_object* x_468; 
x_468 = lean_box(0);
x_439 = x_468;
goto block_464;
}
}
else
{
lean_object* x_469; 
x_469 = lean_box(0);
x_439 = x_469;
goto block_464;
}
}
else
{
lean_object* x_470; 
x_470 = lean_box(0);
x_439 = x_470;
goto block_464;
}
block_438:
{
if (lean_obj_tag(x_1) == 7)
{
uint64_t x_430; uint8_t x_431; lean_object* x_432; lean_object* x_433; 
x_430 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
x_431 = (uint8_t)((x_430 << 24) >> 61);
x_432 = lean_expr_update_forall(x_1, x_431, x_426, x_428);
x_433 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_433, 0, x_432);
lean_ctor_set(x_433, 1, x_429);
return x_433;
}
else
{
lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; 
lean_dec(x_428);
lean_dec(x_426);
lean_dec(x_1);
x_434 = l_Lean_Expr_Inhabited;
x_435 = l_Lean_Expr_updateForallE_x21___closed__1;
x_436 = lean_panic_fn(x_434, x_435);
x_437 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_437, 0, x_436);
lean_ctor_set(x_437, 1, x_429);
return x_437;
}
}
block_464:
{
lean_object* x_440; lean_object* x_441; 
lean_dec(x_439);
x_440 = lean_ctor_get(x_427, 3);
lean_inc(x_440);
x_441 = l_HashMapImp_find_x3f___at_Lean_Closure_visitExpr___spec__1(x_440, x_425);
lean_dec(x_440);
if (lean_obj_tag(x_441) == 0)
{
lean_object* x_442; 
lean_inc(x_425);
x_442 = l_Lean_Closure_collectExprAux___main(x_425, x_2, x_427);
if (lean_obj_tag(x_442) == 0)
{
lean_object* x_443; lean_object* x_444; uint8_t x_445; 
x_443 = lean_ctor_get(x_442, 1);
lean_inc(x_443);
x_444 = lean_ctor_get(x_442, 0);
lean_inc(x_444);
lean_dec(x_442);
x_445 = !lean_is_exclusive(x_443);
if (x_445 == 0)
{
lean_object* x_446; lean_object* x_447; 
x_446 = lean_ctor_get(x_443, 3);
lean_inc(x_444);
x_447 = l_HashMapImp_insert___at_Lean_Closure_visitExpr___spec__3(x_446, x_425, x_444);
lean_ctor_set(x_443, 3, x_447);
x_428 = x_444;
x_429 = x_443;
goto block_438;
}
else
{
lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; 
x_448 = lean_ctor_get(x_443, 0);
x_449 = lean_ctor_get(x_443, 1);
x_450 = lean_ctor_get(x_443, 2);
x_451 = lean_ctor_get(x_443, 3);
x_452 = lean_ctor_get(x_443, 4);
x_453 = lean_ctor_get(x_443, 5);
x_454 = lean_ctor_get(x_443, 6);
x_455 = lean_ctor_get(x_443, 7);
x_456 = lean_ctor_get(x_443, 8);
lean_inc(x_456);
lean_inc(x_455);
lean_inc(x_454);
lean_inc(x_453);
lean_inc(x_452);
lean_inc(x_451);
lean_inc(x_450);
lean_inc(x_449);
lean_inc(x_448);
lean_dec(x_443);
lean_inc(x_444);
x_457 = l_HashMapImp_insert___at_Lean_Closure_visitExpr___spec__3(x_451, x_425, x_444);
x_458 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_458, 0, x_448);
lean_ctor_set(x_458, 1, x_449);
lean_ctor_set(x_458, 2, x_450);
lean_ctor_set(x_458, 3, x_457);
lean_ctor_set(x_458, 4, x_452);
lean_ctor_set(x_458, 5, x_453);
lean_ctor_set(x_458, 6, x_454);
lean_ctor_set(x_458, 7, x_455);
lean_ctor_set(x_458, 8, x_456);
x_428 = x_444;
x_429 = x_458;
goto block_438;
}
}
else
{
uint8_t x_459; 
lean_dec(x_426);
lean_dec(x_425);
lean_dec(x_1);
x_459 = !lean_is_exclusive(x_442);
if (x_459 == 0)
{
return x_442;
}
else
{
lean_object* x_460; lean_object* x_461; lean_object* x_462; 
x_460 = lean_ctor_get(x_442, 0);
x_461 = lean_ctor_get(x_442, 1);
lean_inc(x_461);
lean_inc(x_460);
lean_dec(x_442);
x_462 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_462, 0, x_460);
lean_ctor_set(x_462, 1, x_461);
return x_462;
}
}
}
else
{
lean_object* x_463; 
lean_dec(x_425);
lean_dec(x_2);
x_463 = lean_ctor_get(x_441, 0);
lean_inc(x_463);
lean_dec(x_441);
x_428 = x_463;
x_429 = x_427;
goto block_438;
}
}
}
block_497:
{
lean_object* x_473; lean_object* x_474; 
lean_dec(x_472);
x_473 = lean_ctor_get(x_3, 3);
lean_inc(x_473);
x_474 = l_HashMapImp_find_x3f___at_Lean_Closure_visitExpr___spec__1(x_473, x_424);
lean_dec(x_473);
if (lean_obj_tag(x_474) == 0)
{
lean_object* x_475; 
lean_inc(x_2);
lean_inc(x_424);
x_475 = l_Lean_Closure_collectExprAux___main(x_424, x_2, x_3);
if (lean_obj_tag(x_475) == 0)
{
lean_object* x_476; lean_object* x_477; uint8_t x_478; 
x_476 = lean_ctor_get(x_475, 1);
lean_inc(x_476);
x_477 = lean_ctor_get(x_475, 0);
lean_inc(x_477);
lean_dec(x_475);
x_478 = !lean_is_exclusive(x_476);
if (x_478 == 0)
{
lean_object* x_479; lean_object* x_480; 
x_479 = lean_ctor_get(x_476, 3);
lean_inc(x_477);
x_480 = l_HashMapImp_insert___at_Lean_Closure_visitExpr___spec__3(x_479, x_424, x_477);
lean_ctor_set(x_476, 3, x_480);
x_426 = x_477;
x_427 = x_476;
goto block_471;
}
else
{
lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; 
x_481 = lean_ctor_get(x_476, 0);
x_482 = lean_ctor_get(x_476, 1);
x_483 = lean_ctor_get(x_476, 2);
x_484 = lean_ctor_get(x_476, 3);
x_485 = lean_ctor_get(x_476, 4);
x_486 = lean_ctor_get(x_476, 5);
x_487 = lean_ctor_get(x_476, 6);
x_488 = lean_ctor_get(x_476, 7);
x_489 = lean_ctor_get(x_476, 8);
lean_inc(x_489);
lean_inc(x_488);
lean_inc(x_487);
lean_inc(x_486);
lean_inc(x_485);
lean_inc(x_484);
lean_inc(x_483);
lean_inc(x_482);
lean_inc(x_481);
lean_dec(x_476);
lean_inc(x_477);
x_490 = l_HashMapImp_insert___at_Lean_Closure_visitExpr___spec__3(x_484, x_424, x_477);
x_491 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_491, 0, x_481);
lean_ctor_set(x_491, 1, x_482);
lean_ctor_set(x_491, 2, x_483);
lean_ctor_set(x_491, 3, x_490);
lean_ctor_set(x_491, 4, x_485);
lean_ctor_set(x_491, 5, x_486);
lean_ctor_set(x_491, 6, x_487);
lean_ctor_set(x_491, 7, x_488);
lean_ctor_set(x_491, 8, x_489);
x_426 = x_477;
x_427 = x_491;
goto block_471;
}
}
else
{
uint8_t x_492; 
lean_dec(x_425);
lean_dec(x_424);
lean_dec(x_2);
lean_dec(x_1);
x_492 = !lean_is_exclusive(x_475);
if (x_492 == 0)
{
return x_475;
}
else
{
lean_object* x_493; lean_object* x_494; lean_object* x_495; 
x_493 = lean_ctor_get(x_475, 0);
x_494 = lean_ctor_get(x_475, 1);
lean_inc(x_494);
lean_inc(x_493);
lean_dec(x_475);
x_495 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_495, 0, x_493);
lean_ctor_set(x_495, 1, x_494);
return x_495;
}
}
}
else
{
lean_object* x_496; 
lean_dec(x_424);
x_496 = lean_ctor_get(x_474, 0);
lean_inc(x_496);
lean_dec(x_474);
x_426 = x_496;
x_427 = x_3;
goto block_471;
}
}
}
case 8:
{
lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_586; uint8_t x_612; 
x_504 = lean_ctor_get(x_1, 1);
lean_inc(x_504);
x_505 = lean_ctor_get(x_1, 2);
lean_inc(x_505);
x_506 = lean_ctor_get(x_1, 3);
lean_inc(x_506);
x_612 = l_Lean_Expr_hasLevelParam(x_504);
if (x_612 == 0)
{
uint8_t x_613; 
x_613 = l_Lean_Expr_hasFVar(x_504);
if (x_613 == 0)
{
uint8_t x_614; 
x_614 = l_Lean_Expr_hasMVar(x_504);
if (x_614 == 0)
{
x_507 = x_504;
x_508 = x_3;
goto block_585;
}
else
{
lean_object* x_615; 
x_615 = lean_box(0);
x_586 = x_615;
goto block_611;
}
}
else
{
lean_object* x_616; 
x_616 = lean_box(0);
x_586 = x_616;
goto block_611;
}
}
else
{
lean_object* x_617; 
x_617 = lean_box(0);
x_586 = x_617;
goto block_611;
}
block_585:
{
lean_object* x_509; lean_object* x_510; lean_object* x_553; uint8_t x_579; 
x_579 = l_Lean_Expr_hasLevelParam(x_505);
if (x_579 == 0)
{
uint8_t x_580; 
x_580 = l_Lean_Expr_hasFVar(x_505);
if (x_580 == 0)
{
uint8_t x_581; 
x_581 = l_Lean_Expr_hasMVar(x_505);
if (x_581 == 0)
{
x_509 = x_505;
x_510 = x_508;
goto block_552;
}
else
{
lean_object* x_582; 
x_582 = lean_box(0);
x_553 = x_582;
goto block_578;
}
}
else
{
lean_object* x_583; 
x_583 = lean_box(0);
x_553 = x_583;
goto block_578;
}
}
else
{
lean_object* x_584; 
x_584 = lean_box(0);
x_553 = x_584;
goto block_578;
}
block_552:
{
lean_object* x_511; lean_object* x_512; lean_object* x_520; uint8_t x_546; 
x_546 = l_Lean_Expr_hasLevelParam(x_506);
if (x_546 == 0)
{
uint8_t x_547; 
x_547 = l_Lean_Expr_hasFVar(x_506);
if (x_547 == 0)
{
uint8_t x_548; 
x_548 = l_Lean_Expr_hasMVar(x_506);
if (x_548 == 0)
{
lean_dec(x_2);
x_511 = x_506;
x_512 = x_510;
goto block_519;
}
else
{
lean_object* x_549; 
x_549 = lean_box(0);
x_520 = x_549;
goto block_545;
}
}
else
{
lean_object* x_550; 
x_550 = lean_box(0);
x_520 = x_550;
goto block_545;
}
}
else
{
lean_object* x_551; 
x_551 = lean_box(0);
x_520 = x_551;
goto block_545;
}
block_519:
{
if (lean_obj_tag(x_1) == 8)
{
lean_object* x_513; lean_object* x_514; 
x_513 = lean_expr_update_let(x_1, x_507, x_509, x_511);
x_514 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_514, 0, x_513);
lean_ctor_set(x_514, 1, x_512);
return x_514;
}
else
{
lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; 
lean_dec(x_511);
lean_dec(x_509);
lean_dec(x_507);
lean_dec(x_1);
x_515 = l_Lean_Expr_Inhabited;
x_516 = l_Lean_Expr_updateLet_x21___closed__1;
x_517 = lean_panic_fn(x_515, x_516);
x_518 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_518, 0, x_517);
lean_ctor_set(x_518, 1, x_512);
return x_518;
}
}
block_545:
{
lean_object* x_521; lean_object* x_522; 
lean_dec(x_520);
x_521 = lean_ctor_get(x_510, 3);
lean_inc(x_521);
x_522 = l_HashMapImp_find_x3f___at_Lean_Closure_visitExpr___spec__1(x_521, x_506);
lean_dec(x_521);
if (lean_obj_tag(x_522) == 0)
{
lean_object* x_523; 
lean_inc(x_506);
x_523 = l_Lean_Closure_collectExprAux___main(x_506, x_2, x_510);
if (lean_obj_tag(x_523) == 0)
{
lean_object* x_524; lean_object* x_525; uint8_t x_526; 
x_524 = lean_ctor_get(x_523, 1);
lean_inc(x_524);
x_525 = lean_ctor_get(x_523, 0);
lean_inc(x_525);
lean_dec(x_523);
x_526 = !lean_is_exclusive(x_524);
if (x_526 == 0)
{
lean_object* x_527; lean_object* x_528; 
x_527 = lean_ctor_get(x_524, 3);
lean_inc(x_525);
x_528 = l_HashMapImp_insert___at_Lean_Closure_visitExpr___spec__3(x_527, x_506, x_525);
lean_ctor_set(x_524, 3, x_528);
x_511 = x_525;
x_512 = x_524;
goto block_519;
}
else
{
lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; 
x_529 = lean_ctor_get(x_524, 0);
x_530 = lean_ctor_get(x_524, 1);
x_531 = lean_ctor_get(x_524, 2);
x_532 = lean_ctor_get(x_524, 3);
x_533 = lean_ctor_get(x_524, 4);
x_534 = lean_ctor_get(x_524, 5);
x_535 = lean_ctor_get(x_524, 6);
x_536 = lean_ctor_get(x_524, 7);
x_537 = lean_ctor_get(x_524, 8);
lean_inc(x_537);
lean_inc(x_536);
lean_inc(x_535);
lean_inc(x_534);
lean_inc(x_533);
lean_inc(x_532);
lean_inc(x_531);
lean_inc(x_530);
lean_inc(x_529);
lean_dec(x_524);
lean_inc(x_525);
x_538 = l_HashMapImp_insert___at_Lean_Closure_visitExpr___spec__3(x_532, x_506, x_525);
x_539 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_539, 0, x_529);
lean_ctor_set(x_539, 1, x_530);
lean_ctor_set(x_539, 2, x_531);
lean_ctor_set(x_539, 3, x_538);
lean_ctor_set(x_539, 4, x_533);
lean_ctor_set(x_539, 5, x_534);
lean_ctor_set(x_539, 6, x_535);
lean_ctor_set(x_539, 7, x_536);
lean_ctor_set(x_539, 8, x_537);
x_511 = x_525;
x_512 = x_539;
goto block_519;
}
}
else
{
uint8_t x_540; 
lean_dec(x_509);
lean_dec(x_507);
lean_dec(x_506);
lean_dec(x_1);
x_540 = !lean_is_exclusive(x_523);
if (x_540 == 0)
{
return x_523;
}
else
{
lean_object* x_541; lean_object* x_542; lean_object* x_543; 
x_541 = lean_ctor_get(x_523, 0);
x_542 = lean_ctor_get(x_523, 1);
lean_inc(x_542);
lean_inc(x_541);
lean_dec(x_523);
x_543 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_543, 0, x_541);
lean_ctor_set(x_543, 1, x_542);
return x_543;
}
}
}
else
{
lean_object* x_544; 
lean_dec(x_506);
lean_dec(x_2);
x_544 = lean_ctor_get(x_522, 0);
lean_inc(x_544);
lean_dec(x_522);
x_511 = x_544;
x_512 = x_510;
goto block_519;
}
}
}
block_578:
{
lean_object* x_554; lean_object* x_555; 
lean_dec(x_553);
x_554 = lean_ctor_get(x_508, 3);
lean_inc(x_554);
x_555 = l_HashMapImp_find_x3f___at_Lean_Closure_visitExpr___spec__1(x_554, x_505);
lean_dec(x_554);
if (lean_obj_tag(x_555) == 0)
{
lean_object* x_556; 
lean_inc(x_2);
lean_inc(x_505);
x_556 = l_Lean_Closure_collectExprAux___main(x_505, x_2, x_508);
if (lean_obj_tag(x_556) == 0)
{
lean_object* x_557; lean_object* x_558; uint8_t x_559; 
x_557 = lean_ctor_get(x_556, 1);
lean_inc(x_557);
x_558 = lean_ctor_get(x_556, 0);
lean_inc(x_558);
lean_dec(x_556);
x_559 = !lean_is_exclusive(x_557);
if (x_559 == 0)
{
lean_object* x_560; lean_object* x_561; 
x_560 = lean_ctor_get(x_557, 3);
lean_inc(x_558);
x_561 = l_HashMapImp_insert___at_Lean_Closure_visitExpr___spec__3(x_560, x_505, x_558);
lean_ctor_set(x_557, 3, x_561);
x_509 = x_558;
x_510 = x_557;
goto block_552;
}
else
{
lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_565; lean_object* x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; 
x_562 = lean_ctor_get(x_557, 0);
x_563 = lean_ctor_get(x_557, 1);
x_564 = lean_ctor_get(x_557, 2);
x_565 = lean_ctor_get(x_557, 3);
x_566 = lean_ctor_get(x_557, 4);
x_567 = lean_ctor_get(x_557, 5);
x_568 = lean_ctor_get(x_557, 6);
x_569 = lean_ctor_get(x_557, 7);
x_570 = lean_ctor_get(x_557, 8);
lean_inc(x_570);
lean_inc(x_569);
lean_inc(x_568);
lean_inc(x_567);
lean_inc(x_566);
lean_inc(x_565);
lean_inc(x_564);
lean_inc(x_563);
lean_inc(x_562);
lean_dec(x_557);
lean_inc(x_558);
x_571 = l_HashMapImp_insert___at_Lean_Closure_visitExpr___spec__3(x_565, x_505, x_558);
x_572 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_572, 0, x_562);
lean_ctor_set(x_572, 1, x_563);
lean_ctor_set(x_572, 2, x_564);
lean_ctor_set(x_572, 3, x_571);
lean_ctor_set(x_572, 4, x_566);
lean_ctor_set(x_572, 5, x_567);
lean_ctor_set(x_572, 6, x_568);
lean_ctor_set(x_572, 7, x_569);
lean_ctor_set(x_572, 8, x_570);
x_509 = x_558;
x_510 = x_572;
goto block_552;
}
}
else
{
uint8_t x_573; 
lean_dec(x_507);
lean_dec(x_506);
lean_dec(x_505);
lean_dec(x_2);
lean_dec(x_1);
x_573 = !lean_is_exclusive(x_556);
if (x_573 == 0)
{
return x_556;
}
else
{
lean_object* x_574; lean_object* x_575; lean_object* x_576; 
x_574 = lean_ctor_get(x_556, 0);
x_575 = lean_ctor_get(x_556, 1);
lean_inc(x_575);
lean_inc(x_574);
lean_dec(x_556);
x_576 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_576, 0, x_574);
lean_ctor_set(x_576, 1, x_575);
return x_576;
}
}
}
else
{
lean_object* x_577; 
lean_dec(x_505);
x_577 = lean_ctor_get(x_555, 0);
lean_inc(x_577);
lean_dec(x_555);
x_509 = x_577;
x_510 = x_508;
goto block_552;
}
}
}
block_611:
{
lean_object* x_587; lean_object* x_588; 
lean_dec(x_586);
x_587 = lean_ctor_get(x_3, 3);
lean_inc(x_587);
x_588 = l_HashMapImp_find_x3f___at_Lean_Closure_visitExpr___spec__1(x_587, x_504);
lean_dec(x_587);
if (lean_obj_tag(x_588) == 0)
{
lean_object* x_589; 
lean_inc(x_2);
lean_inc(x_504);
x_589 = l_Lean_Closure_collectExprAux___main(x_504, x_2, x_3);
if (lean_obj_tag(x_589) == 0)
{
lean_object* x_590; lean_object* x_591; uint8_t x_592; 
x_590 = lean_ctor_get(x_589, 1);
lean_inc(x_590);
x_591 = lean_ctor_get(x_589, 0);
lean_inc(x_591);
lean_dec(x_589);
x_592 = !lean_is_exclusive(x_590);
if (x_592 == 0)
{
lean_object* x_593; lean_object* x_594; 
x_593 = lean_ctor_get(x_590, 3);
lean_inc(x_591);
x_594 = l_HashMapImp_insert___at_Lean_Closure_visitExpr___spec__3(x_593, x_504, x_591);
lean_ctor_set(x_590, 3, x_594);
x_507 = x_591;
x_508 = x_590;
goto block_585;
}
else
{
lean_object* x_595; lean_object* x_596; lean_object* x_597; lean_object* x_598; lean_object* x_599; lean_object* x_600; lean_object* x_601; lean_object* x_602; lean_object* x_603; lean_object* x_604; lean_object* x_605; 
x_595 = lean_ctor_get(x_590, 0);
x_596 = lean_ctor_get(x_590, 1);
x_597 = lean_ctor_get(x_590, 2);
x_598 = lean_ctor_get(x_590, 3);
x_599 = lean_ctor_get(x_590, 4);
x_600 = lean_ctor_get(x_590, 5);
x_601 = lean_ctor_get(x_590, 6);
x_602 = lean_ctor_get(x_590, 7);
x_603 = lean_ctor_get(x_590, 8);
lean_inc(x_603);
lean_inc(x_602);
lean_inc(x_601);
lean_inc(x_600);
lean_inc(x_599);
lean_inc(x_598);
lean_inc(x_597);
lean_inc(x_596);
lean_inc(x_595);
lean_dec(x_590);
lean_inc(x_591);
x_604 = l_HashMapImp_insert___at_Lean_Closure_visitExpr___spec__3(x_598, x_504, x_591);
x_605 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_605, 0, x_595);
lean_ctor_set(x_605, 1, x_596);
lean_ctor_set(x_605, 2, x_597);
lean_ctor_set(x_605, 3, x_604);
lean_ctor_set(x_605, 4, x_599);
lean_ctor_set(x_605, 5, x_600);
lean_ctor_set(x_605, 6, x_601);
lean_ctor_set(x_605, 7, x_602);
lean_ctor_set(x_605, 8, x_603);
x_507 = x_591;
x_508 = x_605;
goto block_585;
}
}
else
{
uint8_t x_606; 
lean_dec(x_506);
lean_dec(x_505);
lean_dec(x_504);
lean_dec(x_2);
lean_dec(x_1);
x_606 = !lean_is_exclusive(x_589);
if (x_606 == 0)
{
return x_589;
}
else
{
lean_object* x_607; lean_object* x_608; lean_object* x_609; 
x_607 = lean_ctor_get(x_589, 0);
x_608 = lean_ctor_get(x_589, 1);
lean_inc(x_608);
lean_inc(x_607);
lean_dec(x_589);
x_609 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_609, 0, x_607);
lean_ctor_set(x_609, 1, x_608);
return x_609;
}
}
}
else
{
lean_object* x_610; 
lean_dec(x_504);
x_610 = lean_ctor_get(x_588, 0);
lean_inc(x_610);
lean_dec(x_588);
x_507 = x_610;
x_508 = x_3;
goto block_585;
}
}
}
case 10:
{
lean_object* x_618; lean_object* x_619; uint8_t x_645; 
x_618 = lean_ctor_get(x_1, 1);
lean_inc(x_618);
x_645 = l_Lean_Expr_hasLevelParam(x_618);
if (x_645 == 0)
{
uint8_t x_646; 
x_646 = l_Lean_Expr_hasFVar(x_618);
if (x_646 == 0)
{
uint8_t x_647; 
x_647 = l_Lean_Expr_hasMVar(x_618);
if (x_647 == 0)
{
lean_dec(x_2);
x_4 = x_618;
x_5 = x_3;
goto block_12;
}
else
{
lean_object* x_648; 
x_648 = lean_box(0);
x_619 = x_648;
goto block_644;
}
}
else
{
lean_object* x_649; 
x_649 = lean_box(0);
x_619 = x_649;
goto block_644;
}
}
else
{
lean_object* x_650; 
x_650 = lean_box(0);
x_619 = x_650;
goto block_644;
}
block_644:
{
lean_object* x_620; lean_object* x_621; 
lean_dec(x_619);
x_620 = lean_ctor_get(x_3, 3);
lean_inc(x_620);
x_621 = l_HashMapImp_find_x3f___at_Lean_Closure_visitExpr___spec__1(x_620, x_618);
lean_dec(x_620);
if (lean_obj_tag(x_621) == 0)
{
lean_object* x_622; 
lean_inc(x_618);
x_622 = l_Lean_Closure_collectExprAux___main(x_618, x_2, x_3);
if (lean_obj_tag(x_622) == 0)
{
lean_object* x_623; lean_object* x_624; uint8_t x_625; 
x_623 = lean_ctor_get(x_622, 1);
lean_inc(x_623);
x_624 = lean_ctor_get(x_622, 0);
lean_inc(x_624);
lean_dec(x_622);
x_625 = !lean_is_exclusive(x_623);
if (x_625 == 0)
{
lean_object* x_626; lean_object* x_627; 
x_626 = lean_ctor_get(x_623, 3);
lean_inc(x_624);
x_627 = l_HashMapImp_insert___at_Lean_Closure_visitExpr___spec__3(x_626, x_618, x_624);
lean_ctor_set(x_623, 3, x_627);
x_4 = x_624;
x_5 = x_623;
goto block_12;
}
else
{
lean_object* x_628; lean_object* x_629; lean_object* x_630; lean_object* x_631; lean_object* x_632; lean_object* x_633; lean_object* x_634; lean_object* x_635; lean_object* x_636; lean_object* x_637; lean_object* x_638; 
x_628 = lean_ctor_get(x_623, 0);
x_629 = lean_ctor_get(x_623, 1);
x_630 = lean_ctor_get(x_623, 2);
x_631 = lean_ctor_get(x_623, 3);
x_632 = lean_ctor_get(x_623, 4);
x_633 = lean_ctor_get(x_623, 5);
x_634 = lean_ctor_get(x_623, 6);
x_635 = lean_ctor_get(x_623, 7);
x_636 = lean_ctor_get(x_623, 8);
lean_inc(x_636);
lean_inc(x_635);
lean_inc(x_634);
lean_inc(x_633);
lean_inc(x_632);
lean_inc(x_631);
lean_inc(x_630);
lean_inc(x_629);
lean_inc(x_628);
lean_dec(x_623);
lean_inc(x_624);
x_637 = l_HashMapImp_insert___at_Lean_Closure_visitExpr___spec__3(x_631, x_618, x_624);
x_638 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_638, 0, x_628);
lean_ctor_set(x_638, 1, x_629);
lean_ctor_set(x_638, 2, x_630);
lean_ctor_set(x_638, 3, x_637);
lean_ctor_set(x_638, 4, x_632);
lean_ctor_set(x_638, 5, x_633);
lean_ctor_set(x_638, 6, x_634);
lean_ctor_set(x_638, 7, x_635);
lean_ctor_set(x_638, 8, x_636);
x_4 = x_624;
x_5 = x_638;
goto block_12;
}
}
else
{
uint8_t x_639; 
lean_dec(x_618);
lean_dec(x_1);
x_639 = !lean_is_exclusive(x_622);
if (x_639 == 0)
{
return x_622;
}
else
{
lean_object* x_640; lean_object* x_641; lean_object* x_642; 
x_640 = lean_ctor_get(x_622, 0);
x_641 = lean_ctor_get(x_622, 1);
lean_inc(x_641);
lean_inc(x_640);
lean_dec(x_622);
x_642 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_642, 0, x_640);
lean_ctor_set(x_642, 1, x_641);
return x_642;
}
}
}
else
{
lean_object* x_643; 
lean_dec(x_618);
lean_dec(x_2);
x_643 = lean_ctor_get(x_621, 0);
lean_inc(x_643);
lean_dec(x_621);
x_4 = x_643;
x_5 = x_3;
goto block_12;
}
}
}
case 11:
{
lean_object* x_651; lean_object* x_652; uint8_t x_678; 
x_651 = lean_ctor_get(x_1, 2);
lean_inc(x_651);
x_678 = l_Lean_Expr_hasLevelParam(x_651);
if (x_678 == 0)
{
uint8_t x_679; 
x_679 = l_Lean_Expr_hasFVar(x_651);
if (x_679 == 0)
{
uint8_t x_680; 
x_680 = l_Lean_Expr_hasMVar(x_651);
if (x_680 == 0)
{
lean_dec(x_2);
x_13 = x_651;
x_14 = x_3;
goto block_21;
}
else
{
lean_object* x_681; 
x_681 = lean_box(0);
x_652 = x_681;
goto block_677;
}
}
else
{
lean_object* x_682; 
x_682 = lean_box(0);
x_652 = x_682;
goto block_677;
}
}
else
{
lean_object* x_683; 
x_683 = lean_box(0);
x_652 = x_683;
goto block_677;
}
block_677:
{
lean_object* x_653; lean_object* x_654; 
lean_dec(x_652);
x_653 = lean_ctor_get(x_3, 3);
lean_inc(x_653);
x_654 = l_HashMapImp_find_x3f___at_Lean_Closure_visitExpr___spec__1(x_653, x_651);
lean_dec(x_653);
if (lean_obj_tag(x_654) == 0)
{
lean_object* x_655; 
lean_inc(x_651);
x_655 = l_Lean_Closure_collectExprAux___main(x_651, x_2, x_3);
if (lean_obj_tag(x_655) == 0)
{
lean_object* x_656; lean_object* x_657; uint8_t x_658; 
x_656 = lean_ctor_get(x_655, 1);
lean_inc(x_656);
x_657 = lean_ctor_get(x_655, 0);
lean_inc(x_657);
lean_dec(x_655);
x_658 = !lean_is_exclusive(x_656);
if (x_658 == 0)
{
lean_object* x_659; lean_object* x_660; 
x_659 = lean_ctor_get(x_656, 3);
lean_inc(x_657);
x_660 = l_HashMapImp_insert___at_Lean_Closure_visitExpr___spec__3(x_659, x_651, x_657);
lean_ctor_set(x_656, 3, x_660);
x_13 = x_657;
x_14 = x_656;
goto block_21;
}
else
{
lean_object* x_661; lean_object* x_662; lean_object* x_663; lean_object* x_664; lean_object* x_665; lean_object* x_666; lean_object* x_667; lean_object* x_668; lean_object* x_669; lean_object* x_670; lean_object* x_671; 
x_661 = lean_ctor_get(x_656, 0);
x_662 = lean_ctor_get(x_656, 1);
x_663 = lean_ctor_get(x_656, 2);
x_664 = lean_ctor_get(x_656, 3);
x_665 = lean_ctor_get(x_656, 4);
x_666 = lean_ctor_get(x_656, 5);
x_667 = lean_ctor_get(x_656, 6);
x_668 = lean_ctor_get(x_656, 7);
x_669 = lean_ctor_get(x_656, 8);
lean_inc(x_669);
lean_inc(x_668);
lean_inc(x_667);
lean_inc(x_666);
lean_inc(x_665);
lean_inc(x_664);
lean_inc(x_663);
lean_inc(x_662);
lean_inc(x_661);
lean_dec(x_656);
lean_inc(x_657);
x_670 = l_HashMapImp_insert___at_Lean_Closure_visitExpr___spec__3(x_664, x_651, x_657);
x_671 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_671, 0, x_661);
lean_ctor_set(x_671, 1, x_662);
lean_ctor_set(x_671, 2, x_663);
lean_ctor_set(x_671, 3, x_670);
lean_ctor_set(x_671, 4, x_665);
lean_ctor_set(x_671, 5, x_666);
lean_ctor_set(x_671, 6, x_667);
lean_ctor_set(x_671, 7, x_668);
lean_ctor_set(x_671, 8, x_669);
x_13 = x_657;
x_14 = x_671;
goto block_21;
}
}
else
{
uint8_t x_672; 
lean_dec(x_651);
lean_dec(x_1);
x_672 = !lean_is_exclusive(x_655);
if (x_672 == 0)
{
return x_655;
}
else
{
lean_object* x_673; lean_object* x_674; lean_object* x_675; 
x_673 = lean_ctor_get(x_655, 0);
x_674 = lean_ctor_get(x_655, 1);
lean_inc(x_674);
lean_inc(x_673);
lean_dec(x_655);
x_675 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_675, 0, x_673);
lean_ctor_set(x_675, 1, x_674);
return x_675;
}
}
}
else
{
lean_object* x_676; 
lean_dec(x_651);
lean_dec(x_2);
x_676 = lean_ctor_get(x_654, 0);
lean_inc(x_676);
lean_dec(x_654);
x_13 = x_676;
x_14 = x_3;
goto block_21;
}
}
}
default: 
{
lean_object* x_684; 
lean_dec(x_2);
x_684 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_684, 0, x_1);
lean_ctor_set(x_684, 1, x_3);
return x_684;
}
}
block_12:
{
if (lean_obj_tag(x_1) == 10)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_expr_update_mdata(x_1, x_4);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_4);
lean_dec(x_1);
x_8 = l_Lean_Expr_Inhabited;
x_9 = l_Lean_Expr_updateMData_x21___closed__2;
x_10 = lean_panic_fn(x_8, x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_5);
return x_11;
}
}
block_21:
{
if (lean_obj_tag(x_1) == 11)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_expr_update_proj(x_1, x_13);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_13);
lean_dec(x_1);
x_17 = l_Lean_Expr_Inhabited;
x_18 = l_Lean_Expr_updateProj_x21___closed__2;
x_19 = lean_panic_fn(x_17, x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_14);
return x_20;
}
}
}
}
lean_object* l_List_mapM___main___at_Lean_Closure_collectExprAux___main___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_mapM___main___at_Lean_Closure_collectExprAux___main___spec__1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_Closure_collectExprAux(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Closure_collectExprAux___main(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_Closure_collectExpr(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_48; 
x_48 = l_Lean_Expr_hasLevelParam(x_1);
if (x_48 == 0)
{
uint8_t x_49; 
x_49 = l_Lean_Expr_hasFVar(x_1);
if (x_49 == 0)
{
uint8_t x_50; 
x_50 = l_Lean_Expr_hasMVar(x_1);
if (x_50 == 0)
{
lean_object* x_51; 
lean_dec(x_2);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_1);
lean_ctor_set(x_51, 1, x_3);
return x_51;
}
else
{
lean_object* x_52; 
x_52 = lean_box(0);
x_4 = x_52;
goto block_47;
}
}
else
{
lean_object* x_53; 
x_53 = lean_box(0);
x_4 = x_53;
goto block_47;
}
}
else
{
lean_object* x_54; 
x_54 = lean_box(0);
x_4 = x_54;
goto block_47;
}
block_47:
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_4);
x_5 = lean_ctor_get(x_3, 3);
lean_inc(x_5);
x_6 = l_HashMapImp_find_x3f___at_Lean_Closure_visitExpr___spec__1(x_5, x_1);
lean_dec(x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; 
lean_inc(x_1);
x_7 = l_Lean_Closure_collectExprAux___main(x_1, x_2, x_3);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_7, 1);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_7, 0);
x_12 = lean_ctor_get(x_9, 3);
lean_inc(x_11);
x_13 = l_HashMapImp_insert___at_Lean_Closure_visitExpr___spec__3(x_12, x_1, x_11);
lean_ctor_set(x_9, 3, x_13);
return x_7;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_14 = lean_ctor_get(x_7, 0);
x_15 = lean_ctor_get(x_9, 0);
x_16 = lean_ctor_get(x_9, 1);
x_17 = lean_ctor_get(x_9, 2);
x_18 = lean_ctor_get(x_9, 3);
x_19 = lean_ctor_get(x_9, 4);
x_20 = lean_ctor_get(x_9, 5);
x_21 = lean_ctor_get(x_9, 6);
x_22 = lean_ctor_get(x_9, 7);
x_23 = lean_ctor_get(x_9, 8);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_9);
lean_inc(x_14);
x_24 = l_HashMapImp_insert___at_Lean_Closure_visitExpr___spec__3(x_18, x_1, x_14);
x_25 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_25, 0, x_15);
lean_ctor_set(x_25, 1, x_16);
lean_ctor_set(x_25, 2, x_17);
lean_ctor_set(x_25, 3, x_24);
lean_ctor_set(x_25, 4, x_19);
lean_ctor_set(x_25, 5, x_20);
lean_ctor_set(x_25, 6, x_21);
lean_ctor_set(x_25, 7, x_22);
lean_ctor_set(x_25, 8, x_23);
lean_ctor_set(x_7, 1, x_25);
return x_7;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_26 = lean_ctor_get(x_7, 1);
x_27 = lean_ctor_get(x_7, 0);
lean_inc(x_26);
lean_inc(x_27);
lean_dec(x_7);
x_28 = lean_ctor_get(x_26, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
x_30 = lean_ctor_get(x_26, 2);
lean_inc(x_30);
x_31 = lean_ctor_get(x_26, 3);
lean_inc(x_31);
x_32 = lean_ctor_get(x_26, 4);
lean_inc(x_32);
x_33 = lean_ctor_get(x_26, 5);
lean_inc(x_33);
x_34 = lean_ctor_get(x_26, 6);
lean_inc(x_34);
x_35 = lean_ctor_get(x_26, 7);
lean_inc(x_35);
x_36 = lean_ctor_get(x_26, 8);
lean_inc(x_36);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 lean_ctor_release(x_26, 2);
 lean_ctor_release(x_26, 3);
 lean_ctor_release(x_26, 4);
 lean_ctor_release(x_26, 5);
 lean_ctor_release(x_26, 6);
 lean_ctor_release(x_26, 7);
 lean_ctor_release(x_26, 8);
 x_37 = x_26;
} else {
 lean_dec_ref(x_26);
 x_37 = lean_box(0);
}
lean_inc(x_27);
x_38 = l_HashMapImp_insert___at_Lean_Closure_visitExpr___spec__3(x_31, x_1, x_27);
if (lean_is_scalar(x_37)) {
 x_39 = lean_alloc_ctor(0, 9, 0);
} else {
 x_39 = x_37;
}
lean_ctor_set(x_39, 0, x_28);
lean_ctor_set(x_39, 1, x_29);
lean_ctor_set(x_39, 2, x_30);
lean_ctor_set(x_39, 3, x_38);
lean_ctor_set(x_39, 4, x_32);
lean_ctor_set(x_39, 5, x_33);
lean_ctor_set(x_39, 6, x_34);
lean_ctor_set(x_39, 7, x_35);
lean_ctor_set(x_39, 8, x_36);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_27);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
else
{
uint8_t x_41; 
lean_dec(x_1);
x_41 = !lean_is_exclusive(x_7);
if (x_41 == 0)
{
return x_7;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_7, 0);
x_43 = lean_ctor_get(x_7, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_7);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
else
{
lean_object* x_45; lean_object* x_46; 
lean_dec(x_2);
lean_dec(x_1);
x_45 = lean_ctor_get(x_6, 0);
lean_inc(x_45);
lean_dec(x_6);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_3);
return x_46;
}
}
}
}
lean_object* l_ShareCommonT_withShareCommon___at_Lean_Closure_mkClosure___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_state_sharecommon(x_2, x_1);
return x_3;
}
}
lean_object* l_mkHashMap___at_Lean_Closure_mkClosure___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_mkHashMapImp___rarg(x_1);
return x_2;
}
}
lean_object* l_mkHashMap___at_Lean_Closure_mkClosure___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_mkHashMapImp___rarg(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Closure_mkClosure___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_closure");
return x_1;
}
}
lean_object* _init_l_Lean_Closure_mkClosure___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Closure_mkClosure___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Closure_mkClosure___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Closure_mkClosure___closed__2;
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Closure_mkClosure___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = l_mkHashMapImp___rarg(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Closure_mkClosure___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = l_mkHashMapImp___rarg(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Closure_mkClosure___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = l_Lean_LocalContext_Inhabited___closed__2;
x_2 = l_Lean_Closure_mkClosure___closed__3;
x_3 = l_Lean_Closure_mkClosure___closed__4;
x_4 = l_Lean_Closure_mkClosure___closed__5;
x_5 = l_Array_empty___closed__1;
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_2);
lean_ctor_set(x_7, 2, x_3);
lean_ctor_set(x_7, 3, x_4);
lean_ctor_set(x_7, 4, x_5);
lean_ctor_set(x_7, 5, x_6);
lean_ctor_set(x_7, 6, x_5);
lean_ctor_set(x_7, 7, x_6);
lean_ctor_set(x_7, 8, x_5);
return x_7;
}
}
lean_object* l_Lean_Closure_mkClosure(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_5 = l_ShareCommon_State_empty;
x_6 = lean_state_sharecommon(x_5, x_3);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_state_sharecommon(x_8, x_4);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
lean_dec(x_12);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_1);
lean_ctor_set(x_30, 1, x_2);
x_31 = l_Lean_Closure_mkClosure___closed__6;
lean_inc(x_30);
x_32 = l_Lean_Closure_collectExpr(x_7, x_30, x_31);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = l_Lean_Closure_collectExpr(x_11, x_30, x_34);
if (lean_obj_tag(x_35) == 0)
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
lean_object* x_37; 
x_37 = lean_ctor_get(x_35, 0);
lean_ctor_set(x_9, 1, x_37);
lean_ctor_set(x_9, 0, x_33);
lean_ctor_set(x_35, 0, x_9);
x_13 = x_35;
goto block_29;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_35, 0);
x_39 = lean_ctor_get(x_35, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_35);
lean_ctor_set(x_9, 1, x_38);
lean_ctor_set(x_9, 0, x_33);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_9);
lean_ctor_set(x_40, 1, x_39);
x_13 = x_40;
goto block_29;
}
}
else
{
uint8_t x_41; 
lean_dec(x_33);
lean_free_object(x_9);
x_41 = !lean_is_exclusive(x_35);
if (x_41 == 0)
{
x_13 = x_35;
goto block_29;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_35, 0);
x_43 = lean_ctor_get(x_35, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_35);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
x_13 = x_44;
goto block_29;
}
}
}
else
{
uint8_t x_45; 
lean_dec(x_30);
lean_free_object(x_9);
lean_dec(x_11);
x_45 = !lean_is_exclusive(x_32);
if (x_45 == 0)
{
x_13 = x_32;
goto block_29;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_32, 0);
x_47 = lean_ctor_get(x_32, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_32);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
x_13 = x_48;
goto block_29;
}
}
block_29:
{
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_18 = lean_ctor_get(x_15, 0);
lean_inc(x_18);
x_19 = l_Lean_LocalContext_getFVars(x_18);
lean_inc(x_18);
x_20 = l_Lean_LocalContext_mkForall(x_18, x_19, x_16);
lean_dec(x_16);
x_21 = l_Lean_LocalContext_mkLambda(x_18, x_19, x_17);
lean_dec(x_17);
lean_dec(x_19);
x_22 = lean_ctor_get(x_15, 4);
lean_inc(x_22);
x_23 = lean_ctor_get(x_15, 6);
lean_inc(x_23);
x_24 = lean_ctor_get(x_15, 8);
lean_inc(x_24);
lean_dec(x_15);
x_25 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_25, 0, x_22);
lean_ctor_set(x_25, 1, x_20);
lean_ctor_set(x_25, 2, x_21);
lean_ctor_set(x_25, 3, x_23);
lean_ctor_set(x_25, 4, x_24);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_25);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_13, 0);
lean_inc(x_27);
lean_dec(x_13);
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_27);
return x_28;
}
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_49 = lean_ctor_get(x_9, 0);
lean_inc(x_49);
lean_dec(x_9);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_1);
lean_ctor_set(x_67, 1, x_2);
x_68 = l_Lean_Closure_mkClosure___closed__6;
lean_inc(x_67);
x_69 = l_Lean_Closure_collectExpr(x_7, x_67, x_68);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
x_72 = l_Lean_Closure_collectExpr(x_49, x_67, x_71);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 x_75 = x_72;
} else {
 lean_dec_ref(x_72);
 x_75 = lean_box(0);
}
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_70);
lean_ctor_set(x_76, 1, x_73);
if (lean_is_scalar(x_75)) {
 x_77 = lean_alloc_ctor(0, 2, 0);
} else {
 x_77 = x_75;
}
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_74);
x_50 = x_77;
goto block_66;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
lean_dec(x_70);
x_78 = lean_ctor_get(x_72, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_72, 1);
lean_inc(x_79);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 x_80 = x_72;
} else {
 lean_dec_ref(x_72);
 x_80 = lean_box(0);
}
if (lean_is_scalar(x_80)) {
 x_81 = lean_alloc_ctor(1, 2, 0);
} else {
 x_81 = x_80;
}
lean_ctor_set(x_81, 0, x_78);
lean_ctor_set(x_81, 1, x_79);
x_50 = x_81;
goto block_66;
}
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
lean_dec(x_67);
lean_dec(x_49);
x_82 = lean_ctor_get(x_69, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_69, 1);
lean_inc(x_83);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_84 = x_69;
} else {
 lean_dec_ref(x_69);
 x_84 = lean_box(0);
}
if (lean_is_scalar(x_84)) {
 x_85 = lean_alloc_ctor(1, 2, 0);
} else {
 x_85 = x_84;
}
lean_ctor_set(x_85, 0, x_82);
lean_ctor_set(x_85, 1, x_83);
x_50 = x_85;
goto block_66;
}
block_66:
{
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_53 = lean_ctor_get(x_51, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_51, 1);
lean_inc(x_54);
lean_dec(x_51);
x_55 = lean_ctor_get(x_52, 0);
lean_inc(x_55);
x_56 = l_Lean_LocalContext_getFVars(x_55);
lean_inc(x_55);
x_57 = l_Lean_LocalContext_mkForall(x_55, x_56, x_53);
lean_dec(x_53);
x_58 = l_Lean_LocalContext_mkLambda(x_55, x_56, x_54);
lean_dec(x_54);
lean_dec(x_56);
x_59 = lean_ctor_get(x_52, 4);
lean_inc(x_59);
x_60 = lean_ctor_get(x_52, 6);
lean_inc(x_60);
x_61 = lean_ctor_get(x_52, 8);
lean_inc(x_61);
lean_dec(x_52);
x_62 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_62, 0, x_59);
lean_ctor_set(x_62, 1, x_57);
lean_ctor_set(x_62, 2, x_58);
lean_ctor_set(x_62, 3, x_60);
lean_ctor_set(x_62, 4, x_61);
x_63 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_63, 0, x_62);
return x_63;
}
else
{
lean_object* x_64; lean_object* x_65; 
x_64 = lean_ctor_get(x_50, 0);
lean_inc(x_64);
lean_dec(x_50);
x_65 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_65, 0, x_64);
return x_65;
}
}
}
}
}
lean_object* l_Lean_mkAuxDefinition(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Closure_mkClosure(x_3, x_4, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
lean_dec(x_5);
lean_dec(x_1);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_alloc_ctor(11, 1, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_8, 0, x_11);
return x_8;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_8, 0);
lean_inc(x_12);
lean_dec(x_8);
x_13 = lean_alloc_ctor(11, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint32_t x_22; uint32_t x_23; uint32_t x_24; lean_object* x_25; uint8_t x_26; 
x_15 = lean_ctor_get(x_8, 0);
lean_inc(x_15);
lean_dec(x_8);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = l_Array_toList___rarg(x_16);
lean_dec(x_16);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_inc(x_18);
lean_inc(x_5);
x_19 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_19, 0, x_5);
lean_ctor_set(x_19, 1, x_17);
lean_ctor_set(x_19, 2, x_18);
x_20 = lean_ctor_get(x_15, 2);
lean_inc(x_20);
lean_inc(x_20);
lean_inc(x_1);
x_21 = l_Lean_getMaxHeight(x_1, x_20);
x_22 = lean_unbox_uint32(x_21);
lean_dec(x_21);
x_23 = 1;
x_24 = x_22 + x_23;
x_25 = lean_alloc_ctor(2, 0, 4);
lean_ctor_set_uint32(x_25, 0, x_24);
lean_inc(x_1);
x_26 = l_Lean_Environment_hasUnsafe(x_1, x_18);
if (x_26 == 0)
{
uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_inc(x_20);
lean_inc(x_1);
x_27 = l_Lean_Environment_hasUnsafe(x_1, x_20);
x_28 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_28, 0, x_19);
lean_ctor_set(x_28, 1, x_20);
lean_ctor_set(x_28, 2, x_25);
lean_ctor_set_uint8(x_28, sizeof(void*)*3, x_27);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_28);
x_30 = l_Lean_Environment_addAndCompile(x_1, x_2, x_29);
lean_dec(x_29);
if (lean_obj_tag(x_30) == 0)
{
uint8_t x_31; 
lean_dec(x_15);
lean_dec(x_5);
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
return x_30;
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_30, 0);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_33, 0, x_32);
return x_33;
}
}
else
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_30);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_35 = lean_ctor_get(x_30, 0);
x_36 = lean_ctor_get(x_15, 3);
lean_inc(x_36);
x_37 = l_Array_toList___rarg(x_36);
lean_dec(x_36);
x_38 = l_Lean_mkConst(x_5, x_37);
x_39 = lean_ctor_get(x_15, 4);
lean_inc(x_39);
lean_dec(x_15);
x_40 = lean_unsigned_to_nat(0u);
x_41 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_39, x_39, x_40, x_38);
lean_dec(x_39);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_35);
lean_ctor_set(x_30, 0, x_42);
return x_30;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_43 = lean_ctor_get(x_30, 0);
lean_inc(x_43);
lean_dec(x_30);
x_44 = lean_ctor_get(x_15, 3);
lean_inc(x_44);
x_45 = l_Array_toList___rarg(x_44);
lean_dec(x_44);
x_46 = l_Lean_mkConst(x_5, x_45);
x_47 = lean_ctor_get(x_15, 4);
lean_inc(x_47);
lean_dec(x_15);
x_48 = lean_unsigned_to_nat(0u);
x_49 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_47, x_47, x_48, x_46);
lean_dec(x_47);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_43);
x_51 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_51, 0, x_50);
return x_51;
}
}
}
else
{
uint8_t x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_52 = 1;
x_53 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_53, 0, x_19);
lean_ctor_set(x_53, 1, x_20);
lean_ctor_set(x_53, 2, x_25);
lean_ctor_set_uint8(x_53, sizeof(void*)*3, x_52);
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_53);
x_55 = l_Lean_Environment_addAndCompile(x_1, x_2, x_54);
lean_dec(x_54);
if (lean_obj_tag(x_55) == 0)
{
uint8_t x_56; 
lean_dec(x_15);
lean_dec(x_5);
x_56 = !lean_is_exclusive(x_55);
if (x_56 == 0)
{
return x_55;
}
else
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_55, 0);
lean_inc(x_57);
lean_dec(x_55);
x_58 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_58, 0, x_57);
return x_58;
}
}
else
{
uint8_t x_59; 
x_59 = !lean_is_exclusive(x_55);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_60 = lean_ctor_get(x_55, 0);
x_61 = lean_ctor_get(x_15, 3);
lean_inc(x_61);
x_62 = l_Array_toList___rarg(x_61);
lean_dec(x_61);
x_63 = l_Lean_mkConst(x_5, x_62);
x_64 = lean_ctor_get(x_15, 4);
lean_inc(x_64);
lean_dec(x_15);
x_65 = lean_unsigned_to_nat(0u);
x_66 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_64, x_64, x_65, x_63);
lean_dec(x_64);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_60);
lean_ctor_set(x_55, 0, x_67);
return x_55;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_68 = lean_ctor_get(x_55, 0);
lean_inc(x_68);
lean_dec(x_55);
x_69 = lean_ctor_get(x_15, 3);
lean_inc(x_69);
x_70 = l_Array_toList___rarg(x_69);
lean_dec(x_69);
x_71 = l_Lean_mkConst(x_5, x_70);
x_72 = lean_ctor_get(x_15, 4);
lean_inc(x_72);
lean_dec(x_15);
x_73 = lean_unsigned_to_nat(0u);
x_74 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_72, x_72, x_73, x_71);
lean_dec(x_72);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_68);
x_76 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_76, 0, x_75);
return x_76;
}
}
}
}
}
}
lean_object* l_Lean_mkAuxDefinition___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_mkAuxDefinition(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_8;
}
}
lean_object* initialize_Init_Default(lean_object*);
lean_object* initialize_Init_Lean_MetavarContext(lean_object*);
lean_object* initialize_Init_Lean_Environment(lean_object*);
lean_object* initialize_Init_Lean_Util_FoldConsts(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Lean_Util_Closure(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Default(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_MetavarContext(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Environment(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Util_FoldConsts(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Closure_mkNewLevelParam___closed__1 = _init_l_Lean_Closure_mkNewLevelParam___closed__1();
lean_mark_persistent(l_Lean_Closure_mkNewLevelParam___closed__1);
l_Lean_Closure_mkNewLevelParam___closed__2 = _init_l_Lean_Closure_mkNewLevelParam___closed__2();
lean_mark_persistent(l_Lean_Closure_mkNewLevelParam___closed__2);
l_Lean_Closure_mkNextUserName___rarg___closed__1 = _init_l_Lean_Closure_mkNextUserName___rarg___closed__1();
lean_mark_persistent(l_Lean_Closure_mkNextUserName___rarg___closed__1);
l_Lean_Closure_mkNextUserName___rarg___closed__2 = _init_l_Lean_Closure_mkNextUserName___rarg___closed__2();
lean_mark_persistent(l_Lean_Closure_mkNextUserName___rarg___closed__2);
l_Lean_Closure_mkClosure___closed__1 = _init_l_Lean_Closure_mkClosure___closed__1();
lean_mark_persistent(l_Lean_Closure_mkClosure___closed__1);
l_Lean_Closure_mkClosure___closed__2 = _init_l_Lean_Closure_mkClosure___closed__2();
lean_mark_persistent(l_Lean_Closure_mkClosure___closed__2);
l_Lean_Closure_mkClosure___closed__3 = _init_l_Lean_Closure_mkClosure___closed__3();
lean_mark_persistent(l_Lean_Closure_mkClosure___closed__3);
l_Lean_Closure_mkClosure___closed__4 = _init_l_Lean_Closure_mkClosure___closed__4();
lean_mark_persistent(l_Lean_Closure_mkClosure___closed__4);
l_Lean_Closure_mkClosure___closed__5 = _init_l_Lean_Closure_mkClosure___closed__5();
lean_mark_persistent(l_Lean_Closure_mkClosure___closed__5);
l_Lean_Closure_mkClosure___closed__6 = _init_l_Lean_Closure_mkClosure___closed__6();
lean_mark_persistent(l_Lean_Closure_mkClosure___closed__6);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
