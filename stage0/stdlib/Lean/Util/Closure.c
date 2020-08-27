// Lean compiler output
// Module: Lean.Util.Closure
// Imports: Init Std.ShareCommon Lean.MetavarContext Lean.Environment Lean.Util.FoldConsts
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
lean_object* l_Lean_Closure_mkNewLevelParam___closed__1;
lean_object* lean_expr_update_forall(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Closure_mkNewLevelParam___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Closure_mkNewLevelParam___closed__2;
lean_object* l_Lean_Closure_mkLetDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Closure_getUserName(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_mkHashMap___at_Lean_Closure_mkClosure___spec__5(lean_object*);
lean_object* l_Std_mkHashMap___at_Lean_Closure_mkClosure___spec__6(lean_object*);
extern lean_object* l_Lean_MetavarContext_MkBinding_Lean_MonadHashMapCacheAdapter___closed__1;
lean_object* l_Lean_Closure_collectLevel___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_instantiateMVars(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Closure_Lean_MonadNameGenerator;
lean_object* l_Lean_Closure_mkLetDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_update_mdata(lean_object*, lean_object*);
lean_object* l_Lean_Closure_ExprToClose_inhabited___closed__1;
lean_object* l_List_mapM___main___at_Lean_Closure_collectExprAux___main___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_local_ctx_mk_let_decl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_updateMData_x21___closed__2;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Closure_Lean_MonadNameGenerator___closed__4;
extern lean_object* l_Array_empty___closed__1;
uint8_t l_Lean_Level_hasMVar(lean_object*);
extern lean_object* l_Lean_MetavarContext_getDecl___closed__2;
extern lean_object* l_Std_ShareCommon_State_empty;
lean_object* l_Std_HashMapImp_moveEntries___main___at_Lean_Closure_visitExpr___spec__6(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Closure_Lean_MonadNameGenerator___lambda__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Closure_Lean_MonadNameGenerator___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
size_t l_Lean_Level_hash(lean_object*);
lean_object* l_Lean_Closure_collectLevelAux___main___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
extern lean_object* l_Lean_Level_Inhabited;
lean_object* l_Lean_Closure_Lean_MonadNameGenerator___closed__1;
uint8_t l_Lean_Level_hasParam(lean_object*);
lean_object* l_Std_HashMapImp_moveEntries___main___at_Lean_Closure_visitLevel___spec__6(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Std_AssocList_find_x3f___main___at_Lean_Closure_visitExpr___spec__2___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Closure_collectLevel(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Level_updateMax_x21___closed__2;
extern lean_object* l_Lean_Expr_updateLambdaE_x21___closed__1;
lean_object* l_Lean_LocalContext_getFVars(lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_Closure_mkClosure___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_LocalContext_Inhabited___closed__2;
lean_object* l_Lean_Closure_getMCtx(lean_object*);
lean_object* l_Lean_Closure_getMCtx___rarg(lean_object*);
lean_object* l_Std_HashMapImp_find_x3f___at_Lean_Closure_visitExpr___spec__1(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_Closure_mkClosure___closed__4;
extern lean_object* l_Lean_Expr_Inhabited___closed__1;
lean_object* lean_state_sharecommon(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasLevelParam(lean_object*);
lean_object* l_Std_HashMapImp_find_x3f___at_Lean_Closure_visitExpr___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Closure_mkNextUserName___rarg(lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_Closure_mkClosure___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_AssocList_find_x3f___main___at_Lean_Closure_visitLevel___spec__2(lean_object*, lean_object*);
lean_object* l_Std_HashMapImp_insert___at_Lean_Closure_visitExpr___spec__3(lean_object*, lean_object*, lean_object*);
lean_object* lean_level_update_max(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_HashMapImp_expand___at_Lean_Closure_visitLevel___spec__5(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_mkHashMapImp___rarg(lean_object*);
lean_object* l_Lean_Name_appendIndexAfter(lean_object*, lean_object*);
uint8_t l_Std_AssocList_contains___main___at_Lean_Closure_visitLevel___spec__4(lean_object*, lean_object*);
lean_object* l_Lean_Closure_collectLevelAux___main(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Closure_mkClosure___closed__5;
lean_object* l_Lean_mkFreshId___at_Lean_Closure_mkLocalDecl___spec__1(lean_object*);
size_t l_Lean_Expr_hash(lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_Closure_mkClosure___spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_AssocList_contains___main___at_Lean_Closure_visitLevel___spec__4___boxed(lean_object*, lean_object*);
lean_object* l_Std_HashMapImp_expand___at_Lean_Closure_visitExpr___spec__5(lean_object*, lean_object*);
size_t lean_usize_modn(size_t, lean_object*);
extern lean_object* l_Lean_Expr_updateApp_x21___closed__1;
lean_object* l_Lean_Closure_collectLevelAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Closure_mkValueTypeClosure(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Array_umapMAux___main___at_Lean_Closure_mkClosure___spec__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_HashMapImp_insert___at_Lean_Closure_visitLevel___spec__3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Closure_Lean_MonadNameGenerator___lambda__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Closure_mkClosure___closed__3;
lean_object* lean_expr_update_let(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Closure_collectExprAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
lean_object* l_Lean_Closure_getMCtx___boxed(lean_object*);
lean_object* l_Lean_Closure_collectLevelAux___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_Data_binderInfo(uint64_t);
lean_object* l_Lean_mkFreshId___at_Lean_Closure_mkLocalDecl___spec__1___boxed(lean_object*);
lean_object* l_Std_HashMapImp_find_x3f___at_Lean_Closure_visitLevel___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Std_AssocList_foldlM___main___at_Lean_Closure_visitLevel___spec__7(lean_object*, lean_object*);
lean_object* l_Lean_Closure_mkLocalDecl(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* lean_expr_update_proj(lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_updateProj_x21___closed__2;
lean_object* lean_local_ctx_mk_local_decl(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Std_AssocList_foldlM___main___at_Lean_Closure_visitExpr___spec__7(lean_object*, lean_object*);
lean_object* lean_level_update_imax(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Closure_mkNextUserName(lean_object*);
lean_object* l_Lean_mkFreshId___at_Lean_Closure_mkLocalDecl___spec__1___rarg(lean_object*);
lean_object* l_Lean_Closure_mkClosure___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_AssocList_replace___main___at_Lean_Closure_visitLevel___spec__8(lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_equal(lean_object*, lean_object*);
lean_object* lean_expr_update_sort(lean_object*, lean_object*);
lean_object* l_List_mapM___main___at_Lean_Closure_collectExprAux___main___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Closure_instantiateMVars___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_Closure_mkClosure___closed__1;
lean_object* l_Std_AssocList_contains___main___at_Lean_Closure_visitExpr___spec__4___boxed(lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_Lean_Closure_mkNextUserName___rarg___closed__1;
lean_object* l_Lean_Closure_mkClosure(lean_object*, lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_Level_updateSucc_x21___closed__2;
lean_object* l_Lean_LocalContext_mkLambda(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Closure_mkClosure___closed__2;
lean_object* l_Lean_Closure_Lean_MonadNameGenerator___closed__3;
lean_object* l_Lean_Closure_mkNextUserName___rarg___closed__2;
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_metavar_ctx_find_decl(lean_object*, lean_object*);
extern lean_object* l_Lean_mkAppStx___closed__9;
extern lean_object* l_Lean_Expr_updateLet_x21___closed__1;
lean_object* lean_expr_update_lambda(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* lean_level_update_succ(lean_object*, lean_object*);
extern lean_object* l_Lean_LocalContext_get_x21___closed__1;
uint8_t l_Std_AssocList_contains___main___at_Lean_Closure_visitExpr___spec__4(lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_Inhabited;
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_Closure_mkLocalDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_AssocList_replace___main___at_Lean_Closure_visitExpr___spec__8(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Closure_collectExprAux___main(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_ShareCommonT_withShareCommon___at_Lean_Closure_mkClosure___spec__1(lean_object*, lean_object*);
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*);
lean_object* lean_local_ctx_find(lean_object*, lean_object*);
lean_object* l_ReaderT_bind___at_Lean_Closure_Lean_MonadNameGenerator___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_mkLevelParam(lean_object*);
lean_object* l_Lean_LocalContext_mkForall(lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_update_app(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Closure_mkNextUserName___boxed(lean_object*);
uint8_t lean_level_eq(lean_object*, lean_object*);
lean_object* l_Lean_Closure_visitExpr(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Closure_ExprToClose_inhabited;
uint8_t l_Lean_Expr_hasFVar(lean_object*);
lean_object* l_Lean_Closure_mkNewLevelParam(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Closure_Lean_MonadNameGenerator___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Closure_getUserName___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Closure_collectExpr(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_updateForallE_x21___closed__1;
lean_object* lean_name_mk_numeral(lean_object*, lean_object*);
lean_object* lean_expr_update_const(lean_object*, lean_object*);
extern lean_object* l_Lean_Level_updateIMax_x21___closed__2;
lean_object* l_Lean_Closure_instantiateMVars(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Closure_visitLevel(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_HashMapImp_find_x3f___at_Lean_Closure_visitLevel___spec__1(lean_object*, lean_object*);
lean_object* l_ReaderT_bind___at_Lean_Closure_Lean_MonadNameGenerator___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Closure_Lean_MonadNameGenerator___closed__2;
lean_object* l_Std_AssocList_find_x3f___main___at_Lean_Closure_visitExpr___spec__2(lean_object*, lean_object*);
lean_object* l_Lean_Closure_mkValueTypeClosure___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Std_AssocList_find_x3f___main___at_Lean_Closure_visitLevel___spec__2___boxed(lean_object*, lean_object*);
lean_object* l_Std_AssocList_find_x3f___main___at_Lean_Closure_visitLevel___spec__2(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Std_HashMapImp_find_x3f___at_Lean_Closure_visitLevel___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; size_t x_5; size_t x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
x_5 = l_Lean_Level_hash(x_2);
x_6 = lean_usize_modn(x_5, x_4);
lean_dec(x_4);
x_7 = lean_array_uget(x_3, x_6);
x_8 = l_Std_AssocList_find_x3f___main___at_Lean_Closure_visitLevel___spec__2(x_2, x_7);
lean_dec(x_7);
return x_8;
}
}
uint8_t l_Std_AssocList_contains___main___at_Lean_Closure_visitLevel___spec__4(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Std_AssocList_foldlM___main___at_Lean_Closure_visitLevel___spec__7(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Std_HashMapImp_moveEntries___main___at_Lean_Closure_visitLevel___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_Std_AssocList_foldlM___main___at_Lean_Closure_visitLevel___spec__7(x_3, x_6);
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
lean_object* l_Std_HashMapImp_expand___at_Lean_Closure_visitLevel___spec__5(lean_object* x_1, lean_object* x_2) {
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
x_9 = l_Std_HashMapImp_moveEntries___main___at_Lean_Closure_visitLevel___spec__6(x_8, x_2, x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
lean_object* l_Std_AssocList_replace___main___at_Lean_Closure_visitLevel___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_Std_AssocList_replace___main___at_Lean_Closure_visitLevel___spec__8(x_1, x_2, x_7);
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
x_14 = l_Std_AssocList_replace___main___at_Lean_Closure_visitLevel___spec__8(x_1, x_2, x_12);
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
lean_object* l_Std_HashMapImp_insert___at_Lean_Closure_visitLevel___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_11 = l_Std_AssocList_contains___main___at_Lean_Closure_visitLevel___spec__4(x_2, x_10);
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
x_17 = l_Std_HashMapImp_expand___at_Lean_Closure_visitLevel___spec__5(x_13, x_15);
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
x_18 = l_Std_AssocList_replace___main___at_Lean_Closure_visitLevel___spec__8(x_2, x_3, x_10);
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
x_26 = l_Std_AssocList_contains___main___at_Lean_Closure_visitLevel___spec__4(x_2, x_25);
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
x_32 = l_Std_HashMapImp_expand___at_Lean_Closure_visitLevel___spec__5(x_28, x_30);
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
x_34 = l_Std_AssocList_replace___main___at_Lean_Closure_visitLevel___spec__8(x_2, x_3, x_25);
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
lean_object* x_5; uint8_t x_51; 
x_51 = l_Lean_Level_hasMVar(x_2);
if (x_51 == 0)
{
uint8_t x_52; 
x_52 = l_Lean_Level_hasParam(x_2);
if (x_52 == 0)
{
lean_object* x_53; 
lean_dec(x_3);
lean_dec(x_1);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_2);
lean_ctor_set(x_53, 1, x_4);
return x_53;
}
else
{
lean_object* x_54; 
x_54 = lean_box(0);
x_5 = x_54;
goto block_50;
}
}
else
{
lean_object* x_55; 
x_55 = lean_box(0);
x_5 = x_55;
goto block_50;
}
block_50:
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_5);
x_6 = lean_ctor_get(x_4, 3);
lean_inc(x_6);
x_7 = l_Std_HashMapImp_find_x3f___at_Lean_Closure_visitLevel___spec__1(x_6, x_2);
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
x_14 = l_Std_HashMapImp_insert___at_Lean_Closure_visitLevel___spec__3(x_13, x_2, x_12);
lean_ctor_set(x_10, 3, x_14);
return x_8;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
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
x_25 = lean_ctor_get(x_10, 9);
lean_inc(x_25);
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
x_26 = l_Std_HashMapImp_insert___at_Lean_Closure_visitLevel___spec__3(x_19, x_2, x_15);
x_27 = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(x_27, 0, x_16);
lean_ctor_set(x_27, 1, x_17);
lean_ctor_set(x_27, 2, x_18);
lean_ctor_set(x_27, 3, x_26);
lean_ctor_set(x_27, 4, x_20);
lean_ctor_set(x_27, 5, x_21);
lean_ctor_set(x_27, 6, x_22);
lean_ctor_set(x_27, 7, x_23);
lean_ctor_set(x_27, 8, x_24);
lean_ctor_set(x_27, 9, x_25);
lean_ctor_set(x_8, 1, x_27);
return x_8;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_28 = lean_ctor_get(x_8, 1);
x_29 = lean_ctor_get(x_8, 0);
lean_inc(x_28);
lean_inc(x_29);
lean_dec(x_8);
x_30 = lean_ctor_get(x_28, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
x_32 = lean_ctor_get(x_28, 2);
lean_inc(x_32);
x_33 = lean_ctor_get(x_28, 3);
lean_inc(x_33);
x_34 = lean_ctor_get(x_28, 4);
lean_inc(x_34);
x_35 = lean_ctor_get(x_28, 5);
lean_inc(x_35);
x_36 = lean_ctor_get(x_28, 6);
lean_inc(x_36);
x_37 = lean_ctor_get(x_28, 7);
lean_inc(x_37);
x_38 = lean_ctor_get(x_28, 8);
lean_inc(x_38);
x_39 = lean_ctor_get(x_28, 9);
lean_inc(x_39);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 lean_ctor_release(x_28, 2);
 lean_ctor_release(x_28, 3);
 lean_ctor_release(x_28, 4);
 lean_ctor_release(x_28, 5);
 lean_ctor_release(x_28, 6);
 lean_ctor_release(x_28, 7);
 lean_ctor_release(x_28, 8);
 lean_ctor_release(x_28, 9);
 x_40 = x_28;
} else {
 lean_dec_ref(x_28);
 x_40 = lean_box(0);
}
lean_inc(x_29);
x_41 = l_Std_HashMapImp_insert___at_Lean_Closure_visitLevel___spec__3(x_33, x_2, x_29);
if (lean_is_scalar(x_40)) {
 x_42 = lean_alloc_ctor(0, 10, 0);
} else {
 x_42 = x_40;
}
lean_ctor_set(x_42, 0, x_30);
lean_ctor_set(x_42, 1, x_31);
lean_ctor_set(x_42, 2, x_32);
lean_ctor_set(x_42, 3, x_41);
lean_ctor_set(x_42, 4, x_34);
lean_ctor_set(x_42, 5, x_35);
lean_ctor_set(x_42, 6, x_36);
lean_ctor_set(x_42, 7, x_37);
lean_ctor_set(x_42, 8, x_38);
lean_ctor_set(x_42, 9, x_39);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_29);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
else
{
uint8_t x_44; 
lean_dec(x_2);
x_44 = !lean_is_exclusive(x_8);
if (x_44 == 0)
{
return x_8;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_8, 0);
x_46 = lean_ctor_get(x_8, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_8);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
else
{
lean_object* x_48; lean_object* x_49; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_48 = lean_ctor_get(x_7, 0);
lean_inc(x_48);
lean_dec(x_7);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_4);
return x_49;
}
}
}
}
lean_object* l_Std_AssocList_find_x3f___main___at_Lean_Closure_visitLevel___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_AssocList_find_x3f___main___at_Lean_Closure_visitLevel___spec__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Std_HashMapImp_find_x3f___at_Lean_Closure_visitLevel___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_HashMapImp_find_x3f___at_Lean_Closure_visitLevel___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Std_AssocList_contains___main___at_Lean_Closure_visitLevel___spec__4___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_AssocList_contains___main___at_Lean_Closure_visitLevel___spec__4(x_1, x_2);
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
x_5 = lean_ctor_get(x_3, 5);
x_6 = lean_ctor_get(x_3, 6);
x_7 = lean_ctor_get(x_3, 7);
x_8 = l_Lean_Closure_mkNewLevelParam___closed__2;
lean_inc(x_6);
x_9 = l_Lean_Name_appendIndexAfter(x_8, x_6);
lean_inc(x_9);
x_10 = lean_array_push(x_5, x_9);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_6, x_11);
lean_dec(x_6);
x_13 = lean_array_push(x_7, x_1);
lean_ctor_set(x_3, 7, x_13);
lean_ctor_set(x_3, 6, x_12);
lean_ctor_set(x_3, 5, x_10);
x_14 = l_Lean_mkLevelParam(x_9);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_3);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_16 = lean_ctor_get(x_3, 0);
x_17 = lean_ctor_get(x_3, 1);
x_18 = lean_ctor_get(x_3, 2);
x_19 = lean_ctor_get(x_3, 3);
x_20 = lean_ctor_get(x_3, 4);
x_21 = lean_ctor_get(x_3, 5);
x_22 = lean_ctor_get(x_3, 6);
x_23 = lean_ctor_get(x_3, 7);
x_24 = lean_ctor_get(x_3, 8);
x_25 = lean_ctor_get(x_3, 9);
lean_inc(x_25);
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
x_26 = l_Lean_Closure_mkNewLevelParam___closed__2;
lean_inc(x_22);
x_27 = l_Lean_Name_appendIndexAfter(x_26, x_22);
lean_inc(x_27);
x_28 = lean_array_push(x_21, x_27);
x_29 = lean_unsigned_to_nat(1u);
x_30 = lean_nat_add(x_22, x_29);
lean_dec(x_22);
x_31 = lean_array_push(x_23, x_1);
x_32 = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(x_32, 0, x_16);
lean_ctor_set(x_32, 1, x_17);
lean_ctor_set(x_32, 2, x_18);
lean_ctor_set(x_32, 3, x_19);
lean_ctor_set(x_32, 4, x_20);
lean_ctor_set(x_32, 5, x_28);
lean_ctor_set(x_32, 6, x_30);
lean_ctor_set(x_32, 7, x_31);
lean_ctor_set(x_32, 8, x_24);
lean_ctor_set(x_32, 9, x_25);
x_33 = l_Lean_mkLevelParam(x_27);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
return x_34;
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
lean_object* l_Lean_Closure_getMCtx___rarg(lean_object* x_1) {
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
lean_object* l_Lean_Closure_getMCtx(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Closure_getMCtx___rarg), 1, 0);
return x_2;
}
}
lean_object* l_Lean_Closure_getMCtx___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Closure_getMCtx(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Closure_instantiateMVars(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = l_Lean_MetavarContext_instantiateMVars(x_5, x_1);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
lean_ctor_set(x_3, 0, x_8);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_3);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_10 = lean_ctor_get(x_3, 0);
x_11 = lean_ctor_get(x_3, 1);
x_12 = lean_ctor_get(x_3, 2);
x_13 = lean_ctor_get(x_3, 3);
x_14 = lean_ctor_get(x_3, 4);
x_15 = lean_ctor_get(x_3, 5);
x_16 = lean_ctor_get(x_3, 6);
x_17 = lean_ctor_get(x_3, 7);
x_18 = lean_ctor_get(x_3, 8);
x_19 = lean_ctor_get(x_3, 9);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_3);
x_20 = l_Lean_MetavarContext_instantiateMVars(x_10, x_1);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_11);
lean_ctor_set(x_23, 2, x_12);
lean_ctor_set(x_23, 3, x_13);
lean_ctor_set(x_23, 4, x_14);
lean_ctor_set(x_23, 5, x_15);
lean_ctor_set(x_23, 6, x_16);
lean_ctor_set(x_23, 7, x_17);
lean_ctor_set(x_23, 8, x_18);
lean_ctor_set(x_23, 9, x_19);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_21);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
lean_object* l_Lean_Closure_instantiateMVars___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Closure_instantiateMVars(x_1, x_2, x_3);
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
lean_object* x_14; lean_object* x_15; uint8_t x_38; 
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
x_38 = l_Lean_Level_hasMVar(x_14);
if (x_38 == 0)
{
uint8_t x_39; 
x_39 = l_Lean_Level_hasParam(x_14);
if (x_39 == 0)
{
x_4 = x_14;
x_5 = x_3;
goto block_12;
}
else
{
lean_object* x_40; 
x_40 = lean_box(0);
x_15 = x_40;
goto block_37;
}
}
else
{
lean_object* x_41; 
x_41 = lean_box(0);
x_15 = x_41;
goto block_37;
}
block_37:
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_15);
x_16 = lean_ctor_get(x_3, 3);
lean_inc(x_16);
x_17 = l_Std_HashMapImp_find_x3f___at_Lean_Closure_visitLevel___spec__1(x_16, x_14);
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
x_22 = lean_ctor_get(x_19, 3);
lean_inc(x_20);
x_23 = l_Std_HashMapImp_insert___at_Lean_Closure_visitLevel___spec__3(x_22, x_14, x_20);
lean_ctor_set(x_19, 3, x_23);
x_4 = x_20;
x_5 = x_19;
goto block_12;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_24 = lean_ctor_get(x_19, 0);
x_25 = lean_ctor_get(x_19, 1);
x_26 = lean_ctor_get(x_19, 2);
x_27 = lean_ctor_get(x_19, 3);
x_28 = lean_ctor_get(x_19, 4);
x_29 = lean_ctor_get(x_19, 5);
x_30 = lean_ctor_get(x_19, 6);
x_31 = lean_ctor_get(x_19, 7);
x_32 = lean_ctor_get(x_19, 8);
x_33 = lean_ctor_get(x_19, 9);
lean_inc(x_33);
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
x_34 = l_Std_HashMapImp_insert___at_Lean_Closure_visitLevel___spec__3(x_27, x_14, x_20);
x_35 = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(x_35, 0, x_24);
lean_ctor_set(x_35, 1, x_25);
lean_ctor_set(x_35, 2, x_26);
lean_ctor_set(x_35, 3, x_34);
lean_ctor_set(x_35, 4, x_28);
lean_ctor_set(x_35, 5, x_29);
lean_ctor_set(x_35, 6, x_30);
lean_ctor_set(x_35, 7, x_31);
lean_ctor_set(x_35, 8, x_32);
lean_ctor_set(x_35, 9, x_33);
x_4 = x_20;
x_5 = x_35;
goto block_12;
}
}
else
{
lean_object* x_36; 
lean_dec(x_14);
x_36 = lean_ctor_get(x_17, 0);
lean_inc(x_36);
lean_dec(x_17);
x_4 = x_36;
x_5 = x_3;
goto block_12;
}
}
}
case 2:
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_83; uint8_t x_106; 
x_42 = lean_ctor_get(x_1, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_1, 1);
lean_inc(x_43);
x_106 = l_Lean_Level_hasMVar(x_42);
if (x_106 == 0)
{
uint8_t x_107; 
x_107 = l_Lean_Level_hasParam(x_42);
if (x_107 == 0)
{
x_44 = x_42;
x_45 = x_3;
goto block_82;
}
else
{
lean_object* x_108; 
x_108 = lean_box(0);
x_83 = x_108;
goto block_105;
}
}
else
{
lean_object* x_109; 
x_109 = lean_box(0);
x_83 = x_109;
goto block_105;
}
block_82:
{
lean_object* x_46; lean_object* x_47; lean_object* x_55; uint8_t x_78; 
x_78 = l_Lean_Level_hasMVar(x_43);
if (x_78 == 0)
{
uint8_t x_79; 
x_79 = l_Lean_Level_hasParam(x_43);
if (x_79 == 0)
{
x_46 = x_43;
x_47 = x_45;
goto block_54;
}
else
{
lean_object* x_80; 
x_80 = lean_box(0);
x_55 = x_80;
goto block_77;
}
}
else
{
lean_object* x_81; 
x_81 = lean_box(0);
x_55 = x_81;
goto block_77;
}
block_54:
{
if (lean_obj_tag(x_1) == 2)
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_level_update_max(x_1, x_44, x_46);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_47);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_dec(x_46);
lean_dec(x_44);
lean_dec(x_1);
x_50 = l_Lean_Level_Inhabited;
x_51 = l_Lean_Level_updateMax_x21___closed__2;
x_52 = lean_panic_fn(x_50, x_51);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_47);
return x_53;
}
}
block_77:
{
lean_object* x_56; lean_object* x_57; 
lean_dec(x_55);
x_56 = lean_ctor_get(x_45, 3);
lean_inc(x_56);
x_57 = l_Std_HashMapImp_find_x3f___at_Lean_Closure_visitLevel___spec__1(x_56, x_43);
lean_dec(x_56);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
lean_inc(x_43);
x_58 = l_Lean_Closure_collectLevelAux___main(x_43, x_2, x_45);
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 0);
lean_inc(x_60);
lean_dec(x_58);
x_61 = !lean_is_exclusive(x_59);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_59, 3);
lean_inc(x_60);
x_63 = l_Std_HashMapImp_insert___at_Lean_Closure_visitLevel___spec__3(x_62, x_43, x_60);
lean_ctor_set(x_59, 3, x_63);
x_46 = x_60;
x_47 = x_59;
goto block_54;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_64 = lean_ctor_get(x_59, 0);
x_65 = lean_ctor_get(x_59, 1);
x_66 = lean_ctor_get(x_59, 2);
x_67 = lean_ctor_get(x_59, 3);
x_68 = lean_ctor_get(x_59, 4);
x_69 = lean_ctor_get(x_59, 5);
x_70 = lean_ctor_get(x_59, 6);
x_71 = lean_ctor_get(x_59, 7);
x_72 = lean_ctor_get(x_59, 8);
x_73 = lean_ctor_get(x_59, 9);
lean_inc(x_73);
lean_inc(x_72);
lean_inc(x_71);
lean_inc(x_70);
lean_inc(x_69);
lean_inc(x_68);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_59);
lean_inc(x_60);
x_74 = l_Std_HashMapImp_insert___at_Lean_Closure_visitLevel___spec__3(x_67, x_43, x_60);
x_75 = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(x_75, 0, x_64);
lean_ctor_set(x_75, 1, x_65);
lean_ctor_set(x_75, 2, x_66);
lean_ctor_set(x_75, 3, x_74);
lean_ctor_set(x_75, 4, x_68);
lean_ctor_set(x_75, 5, x_69);
lean_ctor_set(x_75, 6, x_70);
lean_ctor_set(x_75, 7, x_71);
lean_ctor_set(x_75, 8, x_72);
lean_ctor_set(x_75, 9, x_73);
x_46 = x_60;
x_47 = x_75;
goto block_54;
}
}
else
{
lean_object* x_76; 
lean_dec(x_43);
x_76 = lean_ctor_get(x_57, 0);
lean_inc(x_76);
lean_dec(x_57);
x_46 = x_76;
x_47 = x_45;
goto block_54;
}
}
}
block_105:
{
lean_object* x_84; lean_object* x_85; 
lean_dec(x_83);
x_84 = lean_ctor_get(x_3, 3);
lean_inc(x_84);
x_85 = l_Std_HashMapImp_find_x3f___at_Lean_Closure_visitLevel___spec__1(x_84, x_42);
lean_dec(x_84);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; 
lean_inc(x_42);
x_86 = l_Lean_Closure_collectLevelAux___main(x_42, x_2, x_3);
x_87 = lean_ctor_get(x_86, 1);
lean_inc(x_87);
x_88 = lean_ctor_get(x_86, 0);
lean_inc(x_88);
lean_dec(x_86);
x_89 = !lean_is_exclusive(x_87);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; 
x_90 = lean_ctor_get(x_87, 3);
lean_inc(x_88);
x_91 = l_Std_HashMapImp_insert___at_Lean_Closure_visitLevel___spec__3(x_90, x_42, x_88);
lean_ctor_set(x_87, 3, x_91);
x_44 = x_88;
x_45 = x_87;
goto block_82;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_92 = lean_ctor_get(x_87, 0);
x_93 = lean_ctor_get(x_87, 1);
x_94 = lean_ctor_get(x_87, 2);
x_95 = lean_ctor_get(x_87, 3);
x_96 = lean_ctor_get(x_87, 4);
x_97 = lean_ctor_get(x_87, 5);
x_98 = lean_ctor_get(x_87, 6);
x_99 = lean_ctor_get(x_87, 7);
x_100 = lean_ctor_get(x_87, 8);
x_101 = lean_ctor_get(x_87, 9);
lean_inc(x_101);
lean_inc(x_100);
lean_inc(x_99);
lean_inc(x_98);
lean_inc(x_97);
lean_inc(x_96);
lean_inc(x_95);
lean_inc(x_94);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_87);
lean_inc(x_88);
x_102 = l_Std_HashMapImp_insert___at_Lean_Closure_visitLevel___spec__3(x_95, x_42, x_88);
x_103 = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(x_103, 0, x_92);
lean_ctor_set(x_103, 1, x_93);
lean_ctor_set(x_103, 2, x_94);
lean_ctor_set(x_103, 3, x_102);
lean_ctor_set(x_103, 4, x_96);
lean_ctor_set(x_103, 5, x_97);
lean_ctor_set(x_103, 6, x_98);
lean_ctor_set(x_103, 7, x_99);
lean_ctor_set(x_103, 8, x_100);
lean_ctor_set(x_103, 9, x_101);
x_44 = x_88;
x_45 = x_103;
goto block_82;
}
}
else
{
lean_object* x_104; 
lean_dec(x_42);
x_104 = lean_ctor_get(x_85, 0);
lean_inc(x_104);
lean_dec(x_85);
x_44 = x_104;
x_45 = x_3;
goto block_82;
}
}
}
case 3:
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_151; uint8_t x_174; 
x_110 = lean_ctor_get(x_1, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_1, 1);
lean_inc(x_111);
x_174 = l_Lean_Level_hasMVar(x_110);
if (x_174 == 0)
{
uint8_t x_175; 
x_175 = l_Lean_Level_hasParam(x_110);
if (x_175 == 0)
{
x_112 = x_110;
x_113 = x_3;
goto block_150;
}
else
{
lean_object* x_176; 
x_176 = lean_box(0);
x_151 = x_176;
goto block_173;
}
}
else
{
lean_object* x_177; 
x_177 = lean_box(0);
x_151 = x_177;
goto block_173;
}
block_150:
{
lean_object* x_114; lean_object* x_115; lean_object* x_123; uint8_t x_146; 
x_146 = l_Lean_Level_hasMVar(x_111);
if (x_146 == 0)
{
uint8_t x_147; 
x_147 = l_Lean_Level_hasParam(x_111);
if (x_147 == 0)
{
x_114 = x_111;
x_115 = x_113;
goto block_122;
}
else
{
lean_object* x_148; 
x_148 = lean_box(0);
x_123 = x_148;
goto block_145;
}
}
else
{
lean_object* x_149; 
x_149 = lean_box(0);
x_123 = x_149;
goto block_145;
}
block_122:
{
if (lean_obj_tag(x_1) == 3)
{
lean_object* x_116; lean_object* x_117; 
x_116 = lean_level_update_imax(x_1, x_112, x_114);
x_117 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_117, 0, x_116);
lean_ctor_set(x_117, 1, x_115);
return x_117;
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
lean_dec(x_114);
lean_dec(x_112);
lean_dec(x_1);
x_118 = l_Lean_Level_Inhabited;
x_119 = l_Lean_Level_updateIMax_x21___closed__2;
x_120 = lean_panic_fn(x_118, x_119);
x_121 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_121, 0, x_120);
lean_ctor_set(x_121, 1, x_115);
return x_121;
}
}
block_145:
{
lean_object* x_124; lean_object* x_125; 
lean_dec(x_123);
x_124 = lean_ctor_get(x_113, 3);
lean_inc(x_124);
x_125 = l_Std_HashMapImp_find_x3f___at_Lean_Closure_visitLevel___spec__1(x_124, x_111);
lean_dec(x_124);
if (lean_obj_tag(x_125) == 0)
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; uint8_t x_129; 
lean_inc(x_111);
x_126 = l_Lean_Closure_collectLevelAux___main(x_111, x_2, x_113);
x_127 = lean_ctor_get(x_126, 1);
lean_inc(x_127);
x_128 = lean_ctor_get(x_126, 0);
lean_inc(x_128);
lean_dec(x_126);
x_129 = !lean_is_exclusive(x_127);
if (x_129 == 0)
{
lean_object* x_130; lean_object* x_131; 
x_130 = lean_ctor_get(x_127, 3);
lean_inc(x_128);
x_131 = l_Std_HashMapImp_insert___at_Lean_Closure_visitLevel___spec__3(x_130, x_111, x_128);
lean_ctor_set(x_127, 3, x_131);
x_114 = x_128;
x_115 = x_127;
goto block_122;
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_132 = lean_ctor_get(x_127, 0);
x_133 = lean_ctor_get(x_127, 1);
x_134 = lean_ctor_get(x_127, 2);
x_135 = lean_ctor_get(x_127, 3);
x_136 = lean_ctor_get(x_127, 4);
x_137 = lean_ctor_get(x_127, 5);
x_138 = lean_ctor_get(x_127, 6);
x_139 = lean_ctor_get(x_127, 7);
x_140 = lean_ctor_get(x_127, 8);
x_141 = lean_ctor_get(x_127, 9);
lean_inc(x_141);
lean_inc(x_140);
lean_inc(x_139);
lean_inc(x_138);
lean_inc(x_137);
lean_inc(x_136);
lean_inc(x_135);
lean_inc(x_134);
lean_inc(x_133);
lean_inc(x_132);
lean_dec(x_127);
lean_inc(x_128);
x_142 = l_Std_HashMapImp_insert___at_Lean_Closure_visitLevel___spec__3(x_135, x_111, x_128);
x_143 = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(x_143, 0, x_132);
lean_ctor_set(x_143, 1, x_133);
lean_ctor_set(x_143, 2, x_134);
lean_ctor_set(x_143, 3, x_142);
lean_ctor_set(x_143, 4, x_136);
lean_ctor_set(x_143, 5, x_137);
lean_ctor_set(x_143, 6, x_138);
lean_ctor_set(x_143, 7, x_139);
lean_ctor_set(x_143, 8, x_140);
lean_ctor_set(x_143, 9, x_141);
x_114 = x_128;
x_115 = x_143;
goto block_122;
}
}
else
{
lean_object* x_144; 
lean_dec(x_111);
x_144 = lean_ctor_get(x_125, 0);
lean_inc(x_144);
lean_dec(x_125);
x_114 = x_144;
x_115 = x_113;
goto block_122;
}
}
}
block_173:
{
lean_object* x_152; lean_object* x_153; 
lean_dec(x_151);
x_152 = lean_ctor_get(x_3, 3);
lean_inc(x_152);
x_153 = l_Std_HashMapImp_find_x3f___at_Lean_Closure_visitLevel___spec__1(x_152, x_110);
lean_dec(x_152);
if (lean_obj_tag(x_153) == 0)
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; uint8_t x_157; 
lean_inc(x_110);
x_154 = l_Lean_Closure_collectLevelAux___main(x_110, x_2, x_3);
x_155 = lean_ctor_get(x_154, 1);
lean_inc(x_155);
x_156 = lean_ctor_get(x_154, 0);
lean_inc(x_156);
lean_dec(x_154);
x_157 = !lean_is_exclusive(x_155);
if (x_157 == 0)
{
lean_object* x_158; lean_object* x_159; 
x_158 = lean_ctor_get(x_155, 3);
lean_inc(x_156);
x_159 = l_Std_HashMapImp_insert___at_Lean_Closure_visitLevel___spec__3(x_158, x_110, x_156);
lean_ctor_set(x_155, 3, x_159);
x_112 = x_156;
x_113 = x_155;
goto block_150;
}
else
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_160 = lean_ctor_get(x_155, 0);
x_161 = lean_ctor_get(x_155, 1);
x_162 = lean_ctor_get(x_155, 2);
x_163 = lean_ctor_get(x_155, 3);
x_164 = lean_ctor_get(x_155, 4);
x_165 = lean_ctor_get(x_155, 5);
x_166 = lean_ctor_get(x_155, 6);
x_167 = lean_ctor_get(x_155, 7);
x_168 = lean_ctor_get(x_155, 8);
x_169 = lean_ctor_get(x_155, 9);
lean_inc(x_169);
lean_inc(x_168);
lean_inc(x_167);
lean_inc(x_166);
lean_inc(x_165);
lean_inc(x_164);
lean_inc(x_163);
lean_inc(x_162);
lean_inc(x_161);
lean_inc(x_160);
lean_dec(x_155);
lean_inc(x_156);
x_170 = l_Std_HashMapImp_insert___at_Lean_Closure_visitLevel___spec__3(x_163, x_110, x_156);
x_171 = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(x_171, 0, x_160);
lean_ctor_set(x_171, 1, x_161);
lean_ctor_set(x_171, 2, x_162);
lean_ctor_set(x_171, 3, x_170);
lean_ctor_set(x_171, 4, x_164);
lean_ctor_set(x_171, 5, x_165);
lean_ctor_set(x_171, 6, x_166);
lean_ctor_set(x_171, 7, x_167);
lean_ctor_set(x_171, 8, x_168);
lean_ctor_set(x_171, 9, x_169);
x_112 = x_156;
x_113 = x_171;
goto block_150;
}
}
else
{
lean_object* x_172; 
lean_dec(x_110);
x_172 = lean_ctor_get(x_153, 0);
lean_inc(x_172);
lean_dec(x_153);
x_112 = x_172;
x_113 = x_3;
goto block_150;
}
}
}
default: 
{
lean_object* x_178; 
x_178 = l_Lean_Closure_mkNewLevelParam(x_1, x_2, x_3);
return x_178;
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
lean_object* x_4; uint8_t x_46; 
x_46 = l_Lean_Level_hasMVar(x_1);
if (x_46 == 0)
{
uint8_t x_47; 
x_47 = l_Lean_Level_hasParam(x_1);
if (x_47 == 0)
{
lean_object* x_48; 
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_1);
lean_ctor_set(x_48, 1, x_3);
return x_48;
}
else
{
lean_object* x_49; 
x_49 = lean_box(0);
x_4 = x_49;
goto block_45;
}
}
else
{
lean_object* x_50; 
x_50 = lean_box(0);
x_4 = x_50;
goto block_45;
}
block_45:
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_4);
x_5 = lean_ctor_get(x_3, 3);
lean_inc(x_5);
x_6 = l_Std_HashMapImp_find_x3f___at_Lean_Closure_visitLevel___spec__1(x_5, x_1);
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
x_12 = lean_ctor_get(x_9, 3);
lean_inc(x_11);
x_13 = l_Std_HashMapImp_insert___at_Lean_Closure_visitLevel___spec__3(x_12, x_1, x_11);
lean_ctor_set(x_9, 3, x_13);
return x_7;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
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
x_24 = lean_ctor_get(x_9, 9);
lean_inc(x_24);
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
x_25 = l_Std_HashMapImp_insert___at_Lean_Closure_visitLevel___spec__3(x_18, x_1, x_14);
x_26 = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(x_26, 0, x_15);
lean_ctor_set(x_26, 1, x_16);
lean_ctor_set(x_26, 2, x_17);
lean_ctor_set(x_26, 3, x_25);
lean_ctor_set(x_26, 4, x_19);
lean_ctor_set(x_26, 5, x_20);
lean_ctor_set(x_26, 6, x_21);
lean_ctor_set(x_26, 7, x_22);
lean_ctor_set(x_26, 8, x_23);
lean_ctor_set(x_26, 9, x_24);
lean_ctor_set(x_7, 1, x_26);
return x_7;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_27 = lean_ctor_get(x_7, 1);
x_28 = lean_ctor_get(x_7, 0);
lean_inc(x_27);
lean_inc(x_28);
lean_dec(x_7);
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
x_38 = lean_ctor_get(x_27, 9);
lean_inc(x_38);
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
 lean_ctor_release(x_27, 9);
 x_39 = x_27;
} else {
 lean_dec_ref(x_27);
 x_39 = lean_box(0);
}
lean_inc(x_28);
x_40 = l_Std_HashMapImp_insert___at_Lean_Closure_visitLevel___spec__3(x_32, x_1, x_28);
if (lean_is_scalar(x_39)) {
 x_41 = lean_alloc_ctor(0, 10, 0);
} else {
 x_41 = x_39;
}
lean_ctor_set(x_41, 0, x_29);
lean_ctor_set(x_41, 1, x_30);
lean_ctor_set(x_41, 2, x_31);
lean_ctor_set(x_41, 3, x_40);
lean_ctor_set(x_41, 4, x_33);
lean_ctor_set(x_41, 5, x_34);
lean_ctor_set(x_41, 6, x_35);
lean_ctor_set(x_41, 7, x_36);
lean_ctor_set(x_41, 8, x_37);
lean_ctor_set(x_41, 9, x_38);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_28);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
else
{
lean_object* x_43; lean_object* x_44; 
lean_dec(x_1);
x_43 = lean_ctor_get(x_6, 0);
lean_inc(x_43);
lean_dec(x_6);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_3);
return x_44;
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
lean_object* l_ReaderT_bind___at_Lean_Closure_Lean_MonadNameGenerator___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_3);
x_5 = lean_apply_2(x_1, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_apply_3(x_2, x_6, x_3, x_7);
return x_8;
}
else
{
uint8_t x_9; 
lean_dec(x_3);
lean_dec(x_2);
x_9 = !lean_is_exclusive(x_5);
if (x_9 == 0)
{
return x_5;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_5, 0);
x_11 = lean_ctor_get(x_5, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_5);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
}
}
lean_object* l_ReaderT_bind___at_Lean_Closure_Lean_MonadNameGenerator___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Closure_Lean_MonadNameGenerator___spec__1___rarg), 4, 0);
return x_3;
}
}
lean_object* l_Lean_Closure_Lean_MonadNameGenerator___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 2);
lean_inc(x_4);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
}
lean_object* l_Lean_Closure_Lean_MonadNameGenerator___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 2);
lean_dec(x_5);
lean_ctor_set(x_3, 2, x_1);
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_8 = lean_ctor_get(x_3, 0);
x_9 = lean_ctor_get(x_3, 1);
x_10 = lean_ctor_get(x_3, 3);
x_11 = lean_ctor_get(x_3, 4);
x_12 = lean_ctor_get(x_3, 5);
x_13 = lean_ctor_get(x_3, 6);
x_14 = lean_ctor_get(x_3, 7);
x_15 = lean_ctor_get(x_3, 8);
x_16 = lean_ctor_get(x_3, 9);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_3);
x_17 = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(x_17, 0, x_8);
lean_ctor_set(x_17, 1, x_9);
lean_ctor_set(x_17, 2, x_1);
lean_ctor_set(x_17, 3, x_10);
lean_ctor_set(x_17, 4, x_11);
lean_ctor_set(x_17, 5, x_12);
lean_ctor_set(x_17, 6, x_13);
lean_ctor_set(x_17, 7, x_14);
lean_ctor_set(x_17, 8, x_15);
lean_ctor_set(x_17, 9, x_16);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
}
lean_object* _init_l_Lean_Closure_Lean_MonadNameGenerator___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Closure_Lean_MonadNameGenerator___lambda__1___boxed), 3, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Closure_Lean_MonadNameGenerator___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_MetavarContext_MkBinding_Lean_MonadHashMapCacheAdapter___closed__1;
x_2 = l_Lean_Closure_Lean_MonadNameGenerator___closed__1;
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Closure_Lean_MonadNameGenerator___spec__1___rarg), 4, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Closure_Lean_MonadNameGenerator___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Closure_Lean_MonadNameGenerator___lambda__2___boxed), 3, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Closure_Lean_MonadNameGenerator___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Closure_Lean_MonadNameGenerator___closed__2;
x_2 = l_Lean_Closure_Lean_MonadNameGenerator___closed__3;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Closure_Lean_MonadNameGenerator() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Closure_Lean_MonadNameGenerator___closed__4;
return x_1;
}
}
lean_object* l_Lean_Closure_Lean_MonadNameGenerator___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Closure_Lean_MonadNameGenerator___lambda__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Closure_Lean_MonadNameGenerator___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Closure_Lean_MonadNameGenerator___lambda__2(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
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
x_3 = lean_ctor_get(x_1, 8);
x_4 = l_Lean_Closure_mkNextUserName___rarg___closed__2;
lean_inc(x_3);
x_5 = l_Lean_Name_appendIndexAfter(x_4, x_3);
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_add(x_3, x_6);
lean_dec(x_3);
lean_ctor_set(x_1, 8, x_7);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_1);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
x_11 = lean_ctor_get(x_1, 2);
x_12 = lean_ctor_get(x_1, 3);
x_13 = lean_ctor_get(x_1, 4);
x_14 = lean_ctor_get(x_1, 5);
x_15 = lean_ctor_get(x_1, 6);
x_16 = lean_ctor_get(x_1, 7);
x_17 = lean_ctor_get(x_1, 8);
x_18 = lean_ctor_get(x_1, 9);
lean_inc(x_18);
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
x_19 = l_Lean_Closure_mkNextUserName___rarg___closed__2;
lean_inc(x_17);
x_20 = l_Lean_Name_appendIndexAfter(x_19, x_17);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_add(x_17, x_21);
lean_dec(x_17);
x_23 = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(x_23, 0, x_9);
lean_ctor_set(x_23, 1, x_10);
lean_ctor_set(x_23, 2, x_11);
lean_ctor_set(x_23, 3, x_12);
lean_ctor_set(x_23, 4, x_13);
lean_ctor_set(x_23, 5, x_14);
lean_ctor_set(x_23, 6, x_15);
lean_ctor_set(x_23, 7, x_16);
lean_ctor_set(x_23, 8, x_22);
lean_ctor_set(x_23, 9, x_18);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_20);
lean_ctor_set(x_24, 1, x_23);
return x_24;
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
lean_object* l_Lean_mkFreshId___at_Lean_Closure_mkLocalDecl___spec__1___rarg(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_1, 2);
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
lean_ctor_set(x_1, 2, x_16);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_13);
lean_ctor_set(x_17, 1, x_1);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_18 = lean_ctor_get(x_1, 2);
x_19 = lean_ctor_get(x_1, 0);
x_20 = lean_ctor_get(x_1, 1);
x_21 = lean_ctor_get(x_1, 3);
x_22 = lean_ctor_get(x_1, 4);
x_23 = lean_ctor_get(x_1, 5);
x_24 = lean_ctor_get(x_1, 6);
x_25 = lean_ctor_get(x_1, 7);
x_26 = lean_ctor_get(x_1, 8);
x_27 = lean_ctor_get(x_1, 9);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_18);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_1);
x_28 = lean_ctor_get(x_18, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_18, 1);
lean_inc(x_29);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 x_30 = x_18;
} else {
 lean_dec_ref(x_18);
 x_30 = lean_box(0);
}
lean_inc(x_29);
lean_inc(x_28);
x_31 = lean_name_mk_numeral(x_28, x_29);
x_32 = lean_unsigned_to_nat(1u);
x_33 = lean_nat_add(x_29, x_32);
lean_dec(x_29);
if (lean_is_scalar(x_30)) {
 x_34 = lean_alloc_ctor(0, 2, 0);
} else {
 x_34 = x_30;
}
lean_ctor_set(x_34, 0, x_28);
lean_ctor_set(x_34, 1, x_33);
x_35 = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(x_35, 0, x_19);
lean_ctor_set(x_35, 1, x_20);
lean_ctor_set(x_35, 2, x_34);
lean_ctor_set(x_35, 3, x_21);
lean_ctor_set(x_35, 4, x_22);
lean_ctor_set(x_35, 5, x_23);
lean_ctor_set(x_35, 6, x_24);
lean_ctor_set(x_35, 7, x_25);
lean_ctor_set(x_35, 8, x_26);
lean_ctor_set(x_35, 9, x_27);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_31);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
lean_object* l_Lean_mkFreshId___at_Lean_Closure_mkLocalDecl___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_mkFreshId___at_Lean_Closure_mkLocalDecl___spec__1___rarg), 1, 0);
return x_2;
}
}
lean_object* l_Lean_Closure_mkLocalDecl(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = l_Lean_Closure_getUserName(x_1, x_4, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_Lean_mkFreshId___at_Lean_Closure_mkLocalDecl___spec__1___rarg(x_8);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_9, 1);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_9, 0);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
x_15 = lean_local_ctx_mk_local_decl(x_14, x_13, x_7, x_2, x_3);
lean_ctor_set(x_11, 1, x_15);
x_16 = l_Lean_mkFVar(x_13);
lean_ctor_set(x_9, 0, x_16);
return x_9;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_17 = lean_ctor_get(x_9, 0);
x_18 = lean_ctor_get(x_11, 0);
x_19 = lean_ctor_get(x_11, 1);
x_20 = lean_ctor_get(x_11, 2);
x_21 = lean_ctor_get(x_11, 3);
x_22 = lean_ctor_get(x_11, 4);
x_23 = lean_ctor_get(x_11, 5);
x_24 = lean_ctor_get(x_11, 6);
x_25 = lean_ctor_get(x_11, 7);
x_26 = lean_ctor_get(x_11, 8);
x_27 = lean_ctor_get(x_11, 9);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_11);
lean_inc(x_17);
x_28 = lean_local_ctx_mk_local_decl(x_19, x_17, x_7, x_2, x_3);
x_29 = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(x_29, 0, x_18);
lean_ctor_set(x_29, 1, x_28);
lean_ctor_set(x_29, 2, x_20);
lean_ctor_set(x_29, 3, x_21);
lean_ctor_set(x_29, 4, x_22);
lean_ctor_set(x_29, 5, x_23);
lean_ctor_set(x_29, 6, x_24);
lean_ctor_set(x_29, 7, x_25);
lean_ctor_set(x_29, 8, x_26);
lean_ctor_set(x_29, 9, x_27);
x_30 = l_Lean_mkFVar(x_17);
lean_ctor_set(x_9, 1, x_29);
lean_ctor_set(x_9, 0, x_30);
return x_9;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_31 = lean_ctor_get(x_9, 1);
x_32 = lean_ctor_get(x_9, 0);
lean_inc(x_31);
lean_inc(x_32);
lean_dec(x_9);
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
x_42 = lean_ctor_get(x_31, 9);
lean_inc(x_42);
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
 lean_ctor_release(x_31, 9);
 x_43 = x_31;
} else {
 lean_dec_ref(x_31);
 x_43 = lean_box(0);
}
lean_inc(x_32);
x_44 = lean_local_ctx_mk_local_decl(x_34, x_32, x_7, x_2, x_3);
if (lean_is_scalar(x_43)) {
 x_45 = lean_alloc_ctor(0, 10, 0);
} else {
 x_45 = x_43;
}
lean_ctor_set(x_45, 0, x_33);
lean_ctor_set(x_45, 1, x_44);
lean_ctor_set(x_45, 2, x_35);
lean_ctor_set(x_45, 3, x_36);
lean_ctor_set(x_45, 4, x_37);
lean_ctor_set(x_45, 5, x_38);
lean_ctor_set(x_45, 6, x_39);
lean_ctor_set(x_45, 7, x_40);
lean_ctor_set(x_45, 8, x_41);
lean_ctor_set(x_45, 9, x_42);
x_46 = l_Lean_mkFVar(x_32);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_45);
return x_47;
}
}
}
lean_object* l_Lean_mkFreshId___at_Lean_Closure_mkLocalDecl___spec__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_mkFreshId___at_Lean_Closure_mkLocalDecl___spec__1(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Closure_mkLocalDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_3);
lean_dec(x_3);
x_7 = l_Lean_Closure_mkLocalDecl(x_1, x_2, x_6, x_4, x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Lean_Closure_mkLetDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = l_Lean_mkFreshId___at_Lean_Closure_mkLocalDecl___spec__1___rarg(x_5);
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
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
x_12 = lean_local_ctx_mk_let_decl(x_11, x_10, x_1, x_2, x_3);
lean_ctor_set(x_8, 1, x_12);
x_13 = l_Lean_mkFVar(x_10);
lean_ctor_set(x_6, 0, x_13);
return x_6;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
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
x_24 = lean_ctor_get(x_8, 9);
lean_inc(x_24);
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
x_25 = lean_local_ctx_mk_let_decl(x_16, x_14, x_1, x_2, x_3);
x_26 = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(x_26, 0, x_15);
lean_ctor_set(x_26, 1, x_25);
lean_ctor_set(x_26, 2, x_17);
lean_ctor_set(x_26, 3, x_18);
lean_ctor_set(x_26, 4, x_19);
lean_ctor_set(x_26, 5, x_20);
lean_ctor_set(x_26, 6, x_21);
lean_ctor_set(x_26, 7, x_22);
lean_ctor_set(x_26, 8, x_23);
lean_ctor_set(x_26, 9, x_24);
x_27 = l_Lean_mkFVar(x_14);
lean_ctor_set(x_6, 1, x_26);
lean_ctor_set(x_6, 0, x_27);
return x_6;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_28 = lean_ctor_get(x_6, 1);
x_29 = lean_ctor_get(x_6, 0);
lean_inc(x_28);
lean_inc(x_29);
lean_dec(x_6);
x_30 = lean_ctor_get(x_28, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
x_32 = lean_ctor_get(x_28, 2);
lean_inc(x_32);
x_33 = lean_ctor_get(x_28, 3);
lean_inc(x_33);
x_34 = lean_ctor_get(x_28, 4);
lean_inc(x_34);
x_35 = lean_ctor_get(x_28, 5);
lean_inc(x_35);
x_36 = lean_ctor_get(x_28, 6);
lean_inc(x_36);
x_37 = lean_ctor_get(x_28, 7);
lean_inc(x_37);
x_38 = lean_ctor_get(x_28, 8);
lean_inc(x_38);
x_39 = lean_ctor_get(x_28, 9);
lean_inc(x_39);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 lean_ctor_release(x_28, 2);
 lean_ctor_release(x_28, 3);
 lean_ctor_release(x_28, 4);
 lean_ctor_release(x_28, 5);
 lean_ctor_release(x_28, 6);
 lean_ctor_release(x_28, 7);
 lean_ctor_release(x_28, 8);
 lean_ctor_release(x_28, 9);
 x_40 = x_28;
} else {
 lean_dec_ref(x_28);
 x_40 = lean_box(0);
}
lean_inc(x_29);
x_41 = lean_local_ctx_mk_let_decl(x_31, x_29, x_1, x_2, x_3);
if (lean_is_scalar(x_40)) {
 x_42 = lean_alloc_ctor(0, 10, 0);
} else {
 x_42 = x_40;
}
lean_ctor_set(x_42, 0, x_30);
lean_ctor_set(x_42, 1, x_41);
lean_ctor_set(x_42, 2, x_32);
lean_ctor_set(x_42, 3, x_33);
lean_ctor_set(x_42, 4, x_34);
lean_ctor_set(x_42, 5, x_35);
lean_ctor_set(x_42, 6, x_36);
lean_ctor_set(x_42, 7, x_37);
lean_ctor_set(x_42, 8, x_38);
lean_ctor_set(x_42, 9, x_39);
x_43 = l_Lean_mkFVar(x_29);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_42);
return x_44;
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
lean_object* l_Std_AssocList_find_x3f___main___at_Lean_Closure_visitExpr___spec__2(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Std_HashMapImp_find_x3f___at_Lean_Closure_visitExpr___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; size_t x_5; size_t x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
x_5 = l_Lean_Expr_hash(x_2);
x_6 = lean_usize_modn(x_5, x_4);
lean_dec(x_4);
x_7 = lean_array_uget(x_3, x_6);
x_8 = l_Std_AssocList_find_x3f___main___at_Lean_Closure_visitExpr___spec__2(x_2, x_7);
lean_dec(x_7);
return x_8;
}
}
uint8_t l_Std_AssocList_contains___main___at_Lean_Closure_visitExpr___spec__4(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Std_AssocList_foldlM___main___at_Lean_Closure_visitExpr___spec__7(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Std_HashMapImp_moveEntries___main___at_Lean_Closure_visitExpr___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_Std_AssocList_foldlM___main___at_Lean_Closure_visitExpr___spec__7(x_3, x_6);
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
lean_object* l_Std_HashMapImp_expand___at_Lean_Closure_visitExpr___spec__5(lean_object* x_1, lean_object* x_2) {
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
x_9 = l_Std_HashMapImp_moveEntries___main___at_Lean_Closure_visitExpr___spec__6(x_8, x_2, x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
lean_object* l_Std_AssocList_replace___main___at_Lean_Closure_visitExpr___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_Std_AssocList_replace___main___at_Lean_Closure_visitExpr___spec__8(x_1, x_2, x_7);
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
x_14 = l_Std_AssocList_replace___main___at_Lean_Closure_visitExpr___spec__8(x_1, x_2, x_12);
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
lean_object* l_Std_HashMapImp_insert___at_Lean_Closure_visitExpr___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_11 = l_Std_AssocList_contains___main___at_Lean_Closure_visitExpr___spec__4(x_2, x_10);
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
x_17 = l_Std_HashMapImp_expand___at_Lean_Closure_visitExpr___spec__5(x_13, x_15);
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
x_18 = l_Std_AssocList_replace___main___at_Lean_Closure_visitExpr___spec__8(x_2, x_3, x_10);
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
x_26 = l_Std_AssocList_contains___main___at_Lean_Closure_visitExpr___spec__4(x_2, x_25);
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
x_32 = l_Std_HashMapImp_expand___at_Lean_Closure_visitExpr___spec__5(x_28, x_30);
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
x_34 = l_Std_AssocList_replace___main___at_Lean_Closure_visitExpr___spec__8(x_2, x_3, x_25);
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
lean_object* x_5; uint8_t x_51; 
x_51 = l_Lean_Expr_hasLevelParam(x_2);
if (x_51 == 0)
{
uint8_t x_52; 
x_52 = l_Lean_Expr_hasFVar(x_2);
if (x_52 == 0)
{
uint8_t x_53; 
x_53 = l_Lean_Expr_hasMVar(x_2);
if (x_53 == 0)
{
lean_object* x_54; 
lean_dec(x_3);
lean_dec(x_1);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_2);
lean_ctor_set(x_54, 1, x_4);
return x_54;
}
else
{
lean_object* x_55; 
x_55 = lean_box(0);
x_5 = x_55;
goto block_50;
}
}
else
{
lean_object* x_56; 
x_56 = lean_box(0);
x_5 = x_56;
goto block_50;
}
}
else
{
lean_object* x_57; 
x_57 = lean_box(0);
x_5 = x_57;
goto block_50;
}
block_50:
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_5);
x_6 = lean_ctor_get(x_4, 4);
lean_inc(x_6);
x_7 = l_Std_HashMapImp_find_x3f___at_Lean_Closure_visitExpr___spec__1(x_6, x_2);
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
x_13 = lean_ctor_get(x_10, 4);
lean_inc(x_12);
x_14 = l_Std_HashMapImp_insert___at_Lean_Closure_visitExpr___spec__3(x_13, x_2, x_12);
lean_ctor_set(x_10, 4, x_14);
return x_8;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
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
x_25 = lean_ctor_get(x_10, 9);
lean_inc(x_25);
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
x_26 = l_Std_HashMapImp_insert___at_Lean_Closure_visitExpr___spec__3(x_20, x_2, x_15);
x_27 = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(x_27, 0, x_16);
lean_ctor_set(x_27, 1, x_17);
lean_ctor_set(x_27, 2, x_18);
lean_ctor_set(x_27, 3, x_19);
lean_ctor_set(x_27, 4, x_26);
lean_ctor_set(x_27, 5, x_21);
lean_ctor_set(x_27, 6, x_22);
lean_ctor_set(x_27, 7, x_23);
lean_ctor_set(x_27, 8, x_24);
lean_ctor_set(x_27, 9, x_25);
lean_ctor_set(x_8, 1, x_27);
return x_8;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_28 = lean_ctor_get(x_8, 1);
x_29 = lean_ctor_get(x_8, 0);
lean_inc(x_28);
lean_inc(x_29);
lean_dec(x_8);
x_30 = lean_ctor_get(x_28, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
x_32 = lean_ctor_get(x_28, 2);
lean_inc(x_32);
x_33 = lean_ctor_get(x_28, 3);
lean_inc(x_33);
x_34 = lean_ctor_get(x_28, 4);
lean_inc(x_34);
x_35 = lean_ctor_get(x_28, 5);
lean_inc(x_35);
x_36 = lean_ctor_get(x_28, 6);
lean_inc(x_36);
x_37 = lean_ctor_get(x_28, 7);
lean_inc(x_37);
x_38 = lean_ctor_get(x_28, 8);
lean_inc(x_38);
x_39 = lean_ctor_get(x_28, 9);
lean_inc(x_39);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 lean_ctor_release(x_28, 2);
 lean_ctor_release(x_28, 3);
 lean_ctor_release(x_28, 4);
 lean_ctor_release(x_28, 5);
 lean_ctor_release(x_28, 6);
 lean_ctor_release(x_28, 7);
 lean_ctor_release(x_28, 8);
 lean_ctor_release(x_28, 9);
 x_40 = x_28;
} else {
 lean_dec_ref(x_28);
 x_40 = lean_box(0);
}
lean_inc(x_29);
x_41 = l_Std_HashMapImp_insert___at_Lean_Closure_visitExpr___spec__3(x_34, x_2, x_29);
if (lean_is_scalar(x_40)) {
 x_42 = lean_alloc_ctor(0, 10, 0);
} else {
 x_42 = x_40;
}
lean_ctor_set(x_42, 0, x_30);
lean_ctor_set(x_42, 1, x_31);
lean_ctor_set(x_42, 2, x_32);
lean_ctor_set(x_42, 3, x_33);
lean_ctor_set(x_42, 4, x_41);
lean_ctor_set(x_42, 5, x_35);
lean_ctor_set(x_42, 6, x_36);
lean_ctor_set(x_42, 7, x_37);
lean_ctor_set(x_42, 8, x_38);
lean_ctor_set(x_42, 9, x_39);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_29);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
else
{
uint8_t x_44; 
lean_dec(x_2);
x_44 = !lean_is_exclusive(x_8);
if (x_44 == 0)
{
return x_8;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_8, 0);
x_46 = lean_ctor_get(x_8, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_8);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
else
{
lean_object* x_48; lean_object* x_49; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_48 = lean_ctor_get(x_7, 0);
lean_inc(x_48);
lean_dec(x_7);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_4);
return x_49;
}
}
}
}
lean_object* l_Std_AssocList_find_x3f___main___at_Lean_Closure_visitExpr___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_AssocList_find_x3f___main___at_Lean_Closure_visitExpr___spec__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Std_HashMapImp_find_x3f___at_Lean_Closure_visitExpr___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_HashMapImp_find_x3f___at_Lean_Closure_visitExpr___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Std_AssocList_contains___main___at_Lean_Closure_visitExpr___spec__4___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_AssocList_contains___main___at_Lean_Closure_visitExpr___spec__4(x_1, x_2);
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
x_23 = lean_ctor_get(x_2, 0);
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
lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_73; uint8_t x_100; 
x_29 = lean_ctor_get(x_27, 2);
lean_inc(x_29);
x_30 = lean_ctor_get(x_27, 3);
lean_inc(x_30);
x_31 = lean_ctor_get_uint8(x_27, sizeof(void*)*4);
lean_dec(x_27);
x_32 = l_Lean_Closure_instantiateMVars(x_30, x_2, x_3);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_100 = l_Lean_Expr_hasLevelParam(x_33);
if (x_100 == 0)
{
uint8_t x_101; 
x_101 = l_Lean_Expr_hasFVar(x_33);
if (x_101 == 0)
{
uint8_t x_102; 
x_102 = l_Lean_Expr_hasMVar(x_33);
if (x_102 == 0)
{
x_35 = x_33;
x_36 = x_34;
goto block_72;
}
else
{
lean_object* x_103; 
x_103 = lean_box(0);
x_73 = x_103;
goto block_99;
}
}
else
{
lean_object* x_104; 
x_104 = lean_box(0);
x_73 = x_104;
goto block_99;
}
}
else
{
lean_object* x_105; 
x_105 = lean_box(0);
x_73 = x_105;
goto block_99;
}
block_72:
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; 
if (lean_is_scalar(x_28)) {
 x_37 = lean_alloc_ctor(1, 1, 0);
} else {
 x_37 = x_28;
}
lean_ctor_set(x_37, 0, x_29);
x_38 = l_Lean_Closure_mkLocalDecl(x_37, x_35, x_31, x_2, x_36);
lean_dec(x_2);
lean_dec(x_37);
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
lean_object* x_40; uint8_t x_41; 
x_40 = lean_ctor_get(x_38, 1);
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_40, 9);
x_43 = lean_array_push(x_42, x_1);
lean_ctor_set(x_40, 9, x_43);
return x_38;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_44 = lean_ctor_get(x_40, 0);
x_45 = lean_ctor_get(x_40, 1);
x_46 = lean_ctor_get(x_40, 2);
x_47 = lean_ctor_get(x_40, 3);
x_48 = lean_ctor_get(x_40, 4);
x_49 = lean_ctor_get(x_40, 5);
x_50 = lean_ctor_get(x_40, 6);
x_51 = lean_ctor_get(x_40, 7);
x_52 = lean_ctor_get(x_40, 8);
x_53 = lean_ctor_get(x_40, 9);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_40);
x_54 = lean_array_push(x_53, x_1);
x_55 = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(x_55, 0, x_44);
lean_ctor_set(x_55, 1, x_45);
lean_ctor_set(x_55, 2, x_46);
lean_ctor_set(x_55, 3, x_47);
lean_ctor_set(x_55, 4, x_48);
lean_ctor_set(x_55, 5, x_49);
lean_ctor_set(x_55, 6, x_50);
lean_ctor_set(x_55, 7, x_51);
lean_ctor_set(x_55, 8, x_52);
lean_ctor_set(x_55, 9, x_54);
lean_ctor_set(x_38, 1, x_55);
return x_38;
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_56 = lean_ctor_get(x_38, 1);
x_57 = lean_ctor_get(x_38, 0);
lean_inc(x_56);
lean_inc(x_57);
lean_dec(x_38);
x_58 = lean_ctor_get(x_56, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_56, 1);
lean_inc(x_59);
x_60 = lean_ctor_get(x_56, 2);
lean_inc(x_60);
x_61 = lean_ctor_get(x_56, 3);
lean_inc(x_61);
x_62 = lean_ctor_get(x_56, 4);
lean_inc(x_62);
x_63 = lean_ctor_get(x_56, 5);
lean_inc(x_63);
x_64 = lean_ctor_get(x_56, 6);
lean_inc(x_64);
x_65 = lean_ctor_get(x_56, 7);
lean_inc(x_65);
x_66 = lean_ctor_get(x_56, 8);
lean_inc(x_66);
x_67 = lean_ctor_get(x_56, 9);
lean_inc(x_67);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 lean_ctor_release(x_56, 1);
 lean_ctor_release(x_56, 2);
 lean_ctor_release(x_56, 3);
 lean_ctor_release(x_56, 4);
 lean_ctor_release(x_56, 5);
 lean_ctor_release(x_56, 6);
 lean_ctor_release(x_56, 7);
 lean_ctor_release(x_56, 8);
 lean_ctor_release(x_56, 9);
 x_68 = x_56;
} else {
 lean_dec_ref(x_56);
 x_68 = lean_box(0);
}
x_69 = lean_array_push(x_67, x_1);
if (lean_is_scalar(x_68)) {
 x_70 = lean_alloc_ctor(0, 10, 0);
} else {
 x_70 = x_68;
}
lean_ctor_set(x_70, 0, x_58);
lean_ctor_set(x_70, 1, x_59);
lean_ctor_set(x_70, 2, x_60);
lean_ctor_set(x_70, 3, x_61);
lean_ctor_set(x_70, 4, x_62);
lean_ctor_set(x_70, 5, x_63);
lean_ctor_set(x_70, 6, x_64);
lean_ctor_set(x_70, 7, x_65);
lean_ctor_set(x_70, 8, x_66);
lean_ctor_set(x_70, 9, x_69);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_57);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
block_99:
{
lean_object* x_74; lean_object* x_75; 
lean_dec(x_73);
x_74 = lean_ctor_get(x_34, 4);
lean_inc(x_74);
x_75 = l_Std_HashMapImp_find_x3f___at_Lean_Closure_visitExpr___spec__1(x_74, x_33);
lean_dec(x_74);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; 
lean_inc(x_2);
lean_inc(x_33);
x_76 = l_Lean_Closure_collectExprAux___main(x_33, x_2, x_34);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; uint8_t x_79; 
x_77 = lean_ctor_get(x_76, 1);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 0);
lean_inc(x_78);
lean_dec(x_76);
x_79 = !lean_is_exclusive(x_77);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; 
x_80 = lean_ctor_get(x_77, 4);
lean_inc(x_78);
x_81 = l_Std_HashMapImp_insert___at_Lean_Closure_visitExpr___spec__3(x_80, x_33, x_78);
lean_ctor_set(x_77, 4, x_81);
x_35 = x_78;
x_36 = x_77;
goto block_72;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_82 = lean_ctor_get(x_77, 0);
x_83 = lean_ctor_get(x_77, 1);
x_84 = lean_ctor_get(x_77, 2);
x_85 = lean_ctor_get(x_77, 3);
x_86 = lean_ctor_get(x_77, 4);
x_87 = lean_ctor_get(x_77, 5);
x_88 = lean_ctor_get(x_77, 6);
x_89 = lean_ctor_get(x_77, 7);
x_90 = lean_ctor_get(x_77, 8);
x_91 = lean_ctor_get(x_77, 9);
lean_inc(x_91);
lean_inc(x_90);
lean_inc(x_89);
lean_inc(x_88);
lean_inc(x_87);
lean_inc(x_86);
lean_inc(x_85);
lean_inc(x_84);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_77);
lean_inc(x_78);
x_92 = l_Std_HashMapImp_insert___at_Lean_Closure_visitExpr___spec__3(x_86, x_33, x_78);
x_93 = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(x_93, 0, x_82);
lean_ctor_set(x_93, 1, x_83);
lean_ctor_set(x_93, 2, x_84);
lean_ctor_set(x_93, 3, x_85);
lean_ctor_set(x_93, 4, x_92);
lean_ctor_set(x_93, 5, x_87);
lean_ctor_set(x_93, 6, x_88);
lean_ctor_set(x_93, 7, x_89);
lean_ctor_set(x_93, 8, x_90);
lean_ctor_set(x_93, 9, x_91);
x_35 = x_78;
x_36 = x_93;
goto block_72;
}
}
else
{
uint8_t x_94; 
lean_dec(x_33);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_2);
lean_dec(x_1);
x_94 = !lean_is_exclusive(x_76);
if (x_94 == 0)
{
return x_76;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_76, 0);
x_96 = lean_ctor_get(x_76, 1);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_76);
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
return x_97;
}
}
}
else
{
lean_object* x_98; 
lean_dec(x_33);
x_98 = lean_ctor_get(x_75, 0);
lean_inc(x_98);
lean_dec(x_75);
x_35 = x_98;
x_36 = x_34;
goto block_72;
}
}
}
else
{
uint8_t x_106; 
lean_dec(x_28);
lean_dec(x_1);
x_106 = lean_ctor_get_uint8(x_2, sizeof(void*)*1);
if (x_106 == 0)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_156; uint8_t x_183; 
x_107 = lean_ctor_get(x_27, 2);
lean_inc(x_107);
x_108 = lean_ctor_get(x_27, 3);
lean_inc(x_108);
x_109 = lean_ctor_get(x_27, 4);
lean_inc(x_109);
lean_dec(x_27);
x_110 = l_Lean_Closure_instantiateMVars(x_108, x_2, x_3);
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_110, 1);
lean_inc(x_112);
lean_dec(x_110);
x_183 = l_Lean_Expr_hasLevelParam(x_111);
if (x_183 == 0)
{
uint8_t x_184; 
x_184 = l_Lean_Expr_hasFVar(x_111);
if (x_184 == 0)
{
uint8_t x_185; 
x_185 = l_Lean_Expr_hasMVar(x_111);
if (x_185 == 0)
{
x_113 = x_111;
x_114 = x_112;
goto block_155;
}
else
{
lean_object* x_186; 
x_186 = lean_box(0);
x_156 = x_186;
goto block_182;
}
}
else
{
lean_object* x_187; 
x_187 = lean_box(0);
x_156 = x_187;
goto block_182;
}
}
else
{
lean_object* x_188; 
x_188 = lean_box(0);
x_156 = x_188;
goto block_182;
}
block_155:
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; uint8_t x_148; 
x_115 = l_Lean_Closure_instantiateMVars(x_109, x_2, x_114);
x_116 = lean_ctor_get(x_115, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_115, 1);
lean_inc(x_117);
lean_dec(x_115);
x_148 = l_Lean_Expr_hasLevelParam(x_116);
if (x_148 == 0)
{
uint8_t x_149; 
x_149 = l_Lean_Expr_hasFVar(x_116);
if (x_149 == 0)
{
uint8_t x_150; 
x_150 = l_Lean_Expr_hasMVar(x_116);
if (x_150 == 0)
{
lean_object* x_151; 
x_151 = l_Lean_Closure_mkLetDecl(x_107, x_113, x_116, x_2, x_117);
lean_dec(x_2);
return x_151;
}
else
{
lean_object* x_152; 
x_152 = lean_box(0);
x_118 = x_152;
goto block_147;
}
}
else
{
lean_object* x_153; 
x_153 = lean_box(0);
x_118 = x_153;
goto block_147;
}
}
else
{
lean_object* x_154; 
x_154 = lean_box(0);
x_118 = x_154;
goto block_147;
}
block_147:
{
lean_object* x_119; lean_object* x_120; 
lean_dec(x_118);
x_119 = lean_ctor_get(x_117, 4);
lean_inc(x_119);
x_120 = l_Std_HashMapImp_find_x3f___at_Lean_Closure_visitExpr___spec__1(x_119, x_116);
lean_dec(x_119);
if (lean_obj_tag(x_120) == 0)
{
lean_object* x_121; 
lean_inc(x_2);
lean_inc(x_116);
x_121 = l_Lean_Closure_collectExprAux___main(x_116, x_2, x_117);
if (lean_obj_tag(x_121) == 0)
{
lean_object* x_122; lean_object* x_123; uint8_t x_124; 
x_122 = lean_ctor_get(x_121, 1);
lean_inc(x_122);
x_123 = lean_ctor_get(x_121, 0);
lean_inc(x_123);
lean_dec(x_121);
x_124 = !lean_is_exclusive(x_122);
if (x_124 == 0)
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_125 = lean_ctor_get(x_122, 4);
lean_inc(x_123);
x_126 = l_Std_HashMapImp_insert___at_Lean_Closure_visitExpr___spec__3(x_125, x_116, x_123);
lean_ctor_set(x_122, 4, x_126);
x_127 = l_Lean_Closure_mkLetDecl(x_107, x_113, x_123, x_2, x_122);
lean_dec(x_2);
return x_127;
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_128 = lean_ctor_get(x_122, 0);
x_129 = lean_ctor_get(x_122, 1);
x_130 = lean_ctor_get(x_122, 2);
x_131 = lean_ctor_get(x_122, 3);
x_132 = lean_ctor_get(x_122, 4);
x_133 = lean_ctor_get(x_122, 5);
x_134 = lean_ctor_get(x_122, 6);
x_135 = lean_ctor_get(x_122, 7);
x_136 = lean_ctor_get(x_122, 8);
x_137 = lean_ctor_get(x_122, 9);
lean_inc(x_137);
lean_inc(x_136);
lean_inc(x_135);
lean_inc(x_134);
lean_inc(x_133);
lean_inc(x_132);
lean_inc(x_131);
lean_inc(x_130);
lean_inc(x_129);
lean_inc(x_128);
lean_dec(x_122);
lean_inc(x_123);
x_138 = l_Std_HashMapImp_insert___at_Lean_Closure_visitExpr___spec__3(x_132, x_116, x_123);
x_139 = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(x_139, 0, x_128);
lean_ctor_set(x_139, 1, x_129);
lean_ctor_set(x_139, 2, x_130);
lean_ctor_set(x_139, 3, x_131);
lean_ctor_set(x_139, 4, x_138);
lean_ctor_set(x_139, 5, x_133);
lean_ctor_set(x_139, 6, x_134);
lean_ctor_set(x_139, 7, x_135);
lean_ctor_set(x_139, 8, x_136);
lean_ctor_set(x_139, 9, x_137);
x_140 = l_Lean_Closure_mkLetDecl(x_107, x_113, x_123, x_2, x_139);
lean_dec(x_2);
return x_140;
}
}
else
{
uint8_t x_141; 
lean_dec(x_116);
lean_dec(x_113);
lean_dec(x_107);
lean_dec(x_2);
x_141 = !lean_is_exclusive(x_121);
if (x_141 == 0)
{
return x_121;
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_142 = lean_ctor_get(x_121, 0);
x_143 = lean_ctor_get(x_121, 1);
lean_inc(x_143);
lean_inc(x_142);
lean_dec(x_121);
x_144 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_144, 0, x_142);
lean_ctor_set(x_144, 1, x_143);
return x_144;
}
}
}
else
{
lean_object* x_145; lean_object* x_146; 
lean_dec(x_116);
x_145 = lean_ctor_get(x_120, 0);
lean_inc(x_145);
lean_dec(x_120);
x_146 = l_Lean_Closure_mkLetDecl(x_107, x_113, x_145, x_2, x_117);
lean_dec(x_2);
return x_146;
}
}
}
block_182:
{
lean_object* x_157; lean_object* x_158; 
lean_dec(x_156);
x_157 = lean_ctor_get(x_112, 4);
lean_inc(x_157);
x_158 = l_Std_HashMapImp_find_x3f___at_Lean_Closure_visitExpr___spec__1(x_157, x_111);
lean_dec(x_157);
if (lean_obj_tag(x_158) == 0)
{
lean_object* x_159; 
lean_inc(x_2);
lean_inc(x_111);
x_159 = l_Lean_Closure_collectExprAux___main(x_111, x_2, x_112);
if (lean_obj_tag(x_159) == 0)
{
lean_object* x_160; lean_object* x_161; uint8_t x_162; 
x_160 = lean_ctor_get(x_159, 1);
lean_inc(x_160);
x_161 = lean_ctor_get(x_159, 0);
lean_inc(x_161);
lean_dec(x_159);
x_162 = !lean_is_exclusive(x_160);
if (x_162 == 0)
{
lean_object* x_163; lean_object* x_164; 
x_163 = lean_ctor_get(x_160, 4);
lean_inc(x_161);
x_164 = l_Std_HashMapImp_insert___at_Lean_Closure_visitExpr___spec__3(x_163, x_111, x_161);
lean_ctor_set(x_160, 4, x_164);
x_113 = x_161;
x_114 = x_160;
goto block_155;
}
else
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; 
x_165 = lean_ctor_get(x_160, 0);
x_166 = lean_ctor_get(x_160, 1);
x_167 = lean_ctor_get(x_160, 2);
x_168 = lean_ctor_get(x_160, 3);
x_169 = lean_ctor_get(x_160, 4);
x_170 = lean_ctor_get(x_160, 5);
x_171 = lean_ctor_get(x_160, 6);
x_172 = lean_ctor_get(x_160, 7);
x_173 = lean_ctor_get(x_160, 8);
x_174 = lean_ctor_get(x_160, 9);
lean_inc(x_174);
lean_inc(x_173);
lean_inc(x_172);
lean_inc(x_171);
lean_inc(x_170);
lean_inc(x_169);
lean_inc(x_168);
lean_inc(x_167);
lean_inc(x_166);
lean_inc(x_165);
lean_dec(x_160);
lean_inc(x_161);
x_175 = l_Std_HashMapImp_insert___at_Lean_Closure_visitExpr___spec__3(x_169, x_111, x_161);
x_176 = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(x_176, 0, x_165);
lean_ctor_set(x_176, 1, x_166);
lean_ctor_set(x_176, 2, x_167);
lean_ctor_set(x_176, 3, x_168);
lean_ctor_set(x_176, 4, x_175);
lean_ctor_set(x_176, 5, x_170);
lean_ctor_set(x_176, 6, x_171);
lean_ctor_set(x_176, 7, x_172);
lean_ctor_set(x_176, 8, x_173);
lean_ctor_set(x_176, 9, x_174);
x_113 = x_161;
x_114 = x_176;
goto block_155;
}
}
else
{
uint8_t x_177; 
lean_dec(x_111);
lean_dec(x_109);
lean_dec(x_107);
lean_dec(x_2);
x_177 = !lean_is_exclusive(x_159);
if (x_177 == 0)
{
return x_159;
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_178 = lean_ctor_get(x_159, 0);
x_179 = lean_ctor_get(x_159, 1);
lean_inc(x_179);
lean_inc(x_178);
lean_dec(x_159);
x_180 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_180, 0, x_178);
lean_ctor_set(x_180, 1, x_179);
return x_180;
}
}
}
else
{
lean_object* x_181; 
lean_dec(x_111);
x_181 = lean_ctor_get(x_158, 0);
lean_inc(x_181);
lean_dec(x_158);
x_113 = x_181;
x_114 = x_112;
goto block_155;
}
}
}
else
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; uint8_t x_240; 
x_189 = lean_ctor_get(x_27, 4);
lean_inc(x_189);
lean_dec(x_27);
x_190 = l_Lean_Closure_instantiateMVars(x_189, x_2, x_3);
x_191 = lean_ctor_get(x_190, 0);
lean_inc(x_191);
x_192 = lean_ctor_get(x_190, 1);
lean_inc(x_192);
if (lean_is_exclusive(x_190)) {
 lean_ctor_release(x_190, 0);
 lean_ctor_release(x_190, 1);
 x_193 = x_190;
} else {
 lean_dec_ref(x_190);
 x_193 = lean_box(0);
}
x_240 = l_Lean_Expr_hasLevelParam(x_191);
if (x_240 == 0)
{
uint8_t x_241; 
x_241 = l_Lean_Expr_hasFVar(x_191);
if (x_241 == 0)
{
uint8_t x_242; 
x_242 = l_Lean_Expr_hasMVar(x_191);
if (x_242 == 0)
{
lean_object* x_243; 
lean_dec(x_193);
lean_dec(x_2);
x_243 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_243, 0, x_191);
lean_ctor_set(x_243, 1, x_192);
return x_243;
}
else
{
lean_object* x_244; 
x_244 = lean_box(0);
x_194 = x_244;
goto block_239;
}
}
else
{
lean_object* x_245; 
x_245 = lean_box(0);
x_194 = x_245;
goto block_239;
}
}
else
{
lean_object* x_246; 
x_246 = lean_box(0);
x_194 = x_246;
goto block_239;
}
block_239:
{
lean_object* x_195; lean_object* x_196; 
lean_dec(x_194);
x_195 = lean_ctor_get(x_192, 4);
lean_inc(x_195);
x_196 = l_Std_HashMapImp_find_x3f___at_Lean_Closure_visitExpr___spec__1(x_195, x_191);
lean_dec(x_195);
if (lean_obj_tag(x_196) == 0)
{
lean_object* x_197; 
lean_dec(x_193);
lean_inc(x_191);
x_197 = l_Lean_Closure_collectExprAux___main(x_191, x_2, x_192);
if (lean_obj_tag(x_197) == 0)
{
uint8_t x_198; 
x_198 = !lean_is_exclusive(x_197);
if (x_198 == 0)
{
lean_object* x_199; uint8_t x_200; 
x_199 = lean_ctor_get(x_197, 1);
x_200 = !lean_is_exclusive(x_199);
if (x_200 == 0)
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; 
x_201 = lean_ctor_get(x_197, 0);
x_202 = lean_ctor_get(x_199, 4);
lean_inc(x_201);
x_203 = l_Std_HashMapImp_insert___at_Lean_Closure_visitExpr___spec__3(x_202, x_191, x_201);
lean_ctor_set(x_199, 4, x_203);
return x_197;
}
else
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; 
x_204 = lean_ctor_get(x_197, 0);
x_205 = lean_ctor_get(x_199, 0);
x_206 = lean_ctor_get(x_199, 1);
x_207 = lean_ctor_get(x_199, 2);
x_208 = lean_ctor_get(x_199, 3);
x_209 = lean_ctor_get(x_199, 4);
x_210 = lean_ctor_get(x_199, 5);
x_211 = lean_ctor_get(x_199, 6);
x_212 = lean_ctor_get(x_199, 7);
x_213 = lean_ctor_get(x_199, 8);
x_214 = lean_ctor_get(x_199, 9);
lean_inc(x_214);
lean_inc(x_213);
lean_inc(x_212);
lean_inc(x_211);
lean_inc(x_210);
lean_inc(x_209);
lean_inc(x_208);
lean_inc(x_207);
lean_inc(x_206);
lean_inc(x_205);
lean_dec(x_199);
lean_inc(x_204);
x_215 = l_Std_HashMapImp_insert___at_Lean_Closure_visitExpr___spec__3(x_209, x_191, x_204);
x_216 = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(x_216, 0, x_205);
lean_ctor_set(x_216, 1, x_206);
lean_ctor_set(x_216, 2, x_207);
lean_ctor_set(x_216, 3, x_208);
lean_ctor_set(x_216, 4, x_215);
lean_ctor_set(x_216, 5, x_210);
lean_ctor_set(x_216, 6, x_211);
lean_ctor_set(x_216, 7, x_212);
lean_ctor_set(x_216, 8, x_213);
lean_ctor_set(x_216, 9, x_214);
lean_ctor_set(x_197, 1, x_216);
return x_197;
}
}
else
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; 
x_217 = lean_ctor_get(x_197, 1);
x_218 = lean_ctor_get(x_197, 0);
lean_inc(x_217);
lean_inc(x_218);
lean_dec(x_197);
x_219 = lean_ctor_get(x_217, 0);
lean_inc(x_219);
x_220 = lean_ctor_get(x_217, 1);
lean_inc(x_220);
x_221 = lean_ctor_get(x_217, 2);
lean_inc(x_221);
x_222 = lean_ctor_get(x_217, 3);
lean_inc(x_222);
x_223 = lean_ctor_get(x_217, 4);
lean_inc(x_223);
x_224 = lean_ctor_get(x_217, 5);
lean_inc(x_224);
x_225 = lean_ctor_get(x_217, 6);
lean_inc(x_225);
x_226 = lean_ctor_get(x_217, 7);
lean_inc(x_226);
x_227 = lean_ctor_get(x_217, 8);
lean_inc(x_227);
x_228 = lean_ctor_get(x_217, 9);
lean_inc(x_228);
if (lean_is_exclusive(x_217)) {
 lean_ctor_release(x_217, 0);
 lean_ctor_release(x_217, 1);
 lean_ctor_release(x_217, 2);
 lean_ctor_release(x_217, 3);
 lean_ctor_release(x_217, 4);
 lean_ctor_release(x_217, 5);
 lean_ctor_release(x_217, 6);
 lean_ctor_release(x_217, 7);
 lean_ctor_release(x_217, 8);
 lean_ctor_release(x_217, 9);
 x_229 = x_217;
} else {
 lean_dec_ref(x_217);
 x_229 = lean_box(0);
}
lean_inc(x_218);
x_230 = l_Std_HashMapImp_insert___at_Lean_Closure_visitExpr___spec__3(x_223, x_191, x_218);
if (lean_is_scalar(x_229)) {
 x_231 = lean_alloc_ctor(0, 10, 0);
} else {
 x_231 = x_229;
}
lean_ctor_set(x_231, 0, x_219);
lean_ctor_set(x_231, 1, x_220);
lean_ctor_set(x_231, 2, x_221);
lean_ctor_set(x_231, 3, x_222);
lean_ctor_set(x_231, 4, x_230);
lean_ctor_set(x_231, 5, x_224);
lean_ctor_set(x_231, 6, x_225);
lean_ctor_set(x_231, 7, x_226);
lean_ctor_set(x_231, 8, x_227);
lean_ctor_set(x_231, 9, x_228);
x_232 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_232, 0, x_218);
lean_ctor_set(x_232, 1, x_231);
return x_232;
}
}
else
{
uint8_t x_233; 
lean_dec(x_191);
x_233 = !lean_is_exclusive(x_197);
if (x_233 == 0)
{
return x_197;
}
else
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; 
x_234 = lean_ctor_get(x_197, 0);
x_235 = lean_ctor_get(x_197, 1);
lean_inc(x_235);
lean_inc(x_234);
lean_dec(x_197);
x_236 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_236, 0, x_234);
lean_ctor_set(x_236, 1, x_235);
return x_236;
}
}
}
else
{
lean_object* x_237; lean_object* x_238; 
lean_dec(x_191);
lean_dec(x_2);
x_237 = lean_ctor_get(x_196, 0);
lean_inc(x_237);
lean_dec(x_196);
if (lean_is_scalar(x_193)) {
 x_238 = lean_alloc_ctor(0, 2, 0);
} else {
 x_238 = x_193;
}
lean_ctor_set(x_238, 0, x_237);
lean_ctor_set(x_238, 1, x_192);
return x_238;
}
}
}
}
}
}
case 2:
{
lean_object* x_247; lean_object* x_248; uint8_t x_249; 
x_247 = lean_ctor_get(x_1, 0);
lean_inc(x_247);
x_248 = l_Lean_Closure_getMCtx___rarg(x_3);
x_249 = !lean_is_exclusive(x_248);
if (x_249 == 0)
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; 
x_250 = lean_ctor_get(x_248, 0);
x_251 = lean_ctor_get(x_248, 1);
x_252 = lean_metavar_ctx_find_decl(x_250, x_247);
if (lean_obj_tag(x_252) == 0)
{
lean_object* x_253; 
lean_dec(x_2);
lean_dec(x_1);
x_253 = l_Lean_MetavarContext_getDecl___closed__2;
lean_ctor_set_tag(x_248, 1);
lean_ctor_set(x_248, 0, x_253);
return x_248;
}
else
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_298; uint8_t x_325; 
lean_free_object(x_248);
x_254 = lean_ctor_get(x_252, 0);
lean_inc(x_254);
lean_dec(x_252);
x_255 = lean_ctor_get(x_254, 2);
lean_inc(x_255);
lean_dec(x_254);
x_256 = l_Lean_Closure_instantiateMVars(x_255, x_2, x_251);
x_257 = lean_ctor_get(x_256, 0);
lean_inc(x_257);
x_258 = lean_ctor_get(x_256, 1);
lean_inc(x_258);
lean_dec(x_256);
x_325 = l_Lean_Expr_hasLevelParam(x_257);
if (x_325 == 0)
{
uint8_t x_326; 
x_326 = l_Lean_Expr_hasFVar(x_257);
if (x_326 == 0)
{
uint8_t x_327; 
x_327 = l_Lean_Expr_hasMVar(x_257);
if (x_327 == 0)
{
x_259 = x_257;
x_260 = x_258;
goto block_297;
}
else
{
lean_object* x_328; 
x_328 = lean_box(0);
x_298 = x_328;
goto block_324;
}
}
else
{
lean_object* x_329; 
x_329 = lean_box(0);
x_298 = x_329;
goto block_324;
}
}
else
{
lean_object* x_330; 
x_330 = lean_box(0);
x_298 = x_330;
goto block_324;
}
block_297:
{
lean_object* x_261; uint8_t x_262; lean_object* x_263; uint8_t x_264; 
x_261 = lean_box(0);
x_262 = 0;
x_263 = l_Lean_Closure_mkLocalDecl(x_261, x_259, x_262, x_2, x_260);
lean_dec(x_2);
x_264 = !lean_is_exclusive(x_263);
if (x_264 == 0)
{
lean_object* x_265; uint8_t x_266; 
x_265 = lean_ctor_get(x_263, 1);
x_266 = !lean_is_exclusive(x_265);
if (x_266 == 0)
{
lean_object* x_267; lean_object* x_268; 
x_267 = lean_ctor_get(x_265, 9);
x_268 = lean_array_push(x_267, x_1);
lean_ctor_set(x_265, 9, x_268);
return x_263;
}
else
{
lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; 
x_269 = lean_ctor_get(x_265, 0);
x_270 = lean_ctor_get(x_265, 1);
x_271 = lean_ctor_get(x_265, 2);
x_272 = lean_ctor_get(x_265, 3);
x_273 = lean_ctor_get(x_265, 4);
x_274 = lean_ctor_get(x_265, 5);
x_275 = lean_ctor_get(x_265, 6);
x_276 = lean_ctor_get(x_265, 7);
x_277 = lean_ctor_get(x_265, 8);
x_278 = lean_ctor_get(x_265, 9);
lean_inc(x_278);
lean_inc(x_277);
lean_inc(x_276);
lean_inc(x_275);
lean_inc(x_274);
lean_inc(x_273);
lean_inc(x_272);
lean_inc(x_271);
lean_inc(x_270);
lean_inc(x_269);
lean_dec(x_265);
x_279 = lean_array_push(x_278, x_1);
x_280 = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(x_280, 0, x_269);
lean_ctor_set(x_280, 1, x_270);
lean_ctor_set(x_280, 2, x_271);
lean_ctor_set(x_280, 3, x_272);
lean_ctor_set(x_280, 4, x_273);
lean_ctor_set(x_280, 5, x_274);
lean_ctor_set(x_280, 6, x_275);
lean_ctor_set(x_280, 7, x_276);
lean_ctor_set(x_280, 8, x_277);
lean_ctor_set(x_280, 9, x_279);
lean_ctor_set(x_263, 1, x_280);
return x_263;
}
}
else
{
lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; 
x_281 = lean_ctor_get(x_263, 1);
x_282 = lean_ctor_get(x_263, 0);
lean_inc(x_281);
lean_inc(x_282);
lean_dec(x_263);
x_283 = lean_ctor_get(x_281, 0);
lean_inc(x_283);
x_284 = lean_ctor_get(x_281, 1);
lean_inc(x_284);
x_285 = lean_ctor_get(x_281, 2);
lean_inc(x_285);
x_286 = lean_ctor_get(x_281, 3);
lean_inc(x_286);
x_287 = lean_ctor_get(x_281, 4);
lean_inc(x_287);
x_288 = lean_ctor_get(x_281, 5);
lean_inc(x_288);
x_289 = lean_ctor_get(x_281, 6);
lean_inc(x_289);
x_290 = lean_ctor_get(x_281, 7);
lean_inc(x_290);
x_291 = lean_ctor_get(x_281, 8);
lean_inc(x_291);
x_292 = lean_ctor_get(x_281, 9);
lean_inc(x_292);
if (lean_is_exclusive(x_281)) {
 lean_ctor_release(x_281, 0);
 lean_ctor_release(x_281, 1);
 lean_ctor_release(x_281, 2);
 lean_ctor_release(x_281, 3);
 lean_ctor_release(x_281, 4);
 lean_ctor_release(x_281, 5);
 lean_ctor_release(x_281, 6);
 lean_ctor_release(x_281, 7);
 lean_ctor_release(x_281, 8);
 lean_ctor_release(x_281, 9);
 x_293 = x_281;
} else {
 lean_dec_ref(x_281);
 x_293 = lean_box(0);
}
x_294 = lean_array_push(x_292, x_1);
if (lean_is_scalar(x_293)) {
 x_295 = lean_alloc_ctor(0, 10, 0);
} else {
 x_295 = x_293;
}
lean_ctor_set(x_295, 0, x_283);
lean_ctor_set(x_295, 1, x_284);
lean_ctor_set(x_295, 2, x_285);
lean_ctor_set(x_295, 3, x_286);
lean_ctor_set(x_295, 4, x_287);
lean_ctor_set(x_295, 5, x_288);
lean_ctor_set(x_295, 6, x_289);
lean_ctor_set(x_295, 7, x_290);
lean_ctor_set(x_295, 8, x_291);
lean_ctor_set(x_295, 9, x_294);
x_296 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_296, 0, x_282);
lean_ctor_set(x_296, 1, x_295);
return x_296;
}
}
block_324:
{
lean_object* x_299; lean_object* x_300; 
lean_dec(x_298);
x_299 = lean_ctor_get(x_258, 4);
lean_inc(x_299);
x_300 = l_Std_HashMapImp_find_x3f___at_Lean_Closure_visitExpr___spec__1(x_299, x_257);
lean_dec(x_299);
if (lean_obj_tag(x_300) == 0)
{
lean_object* x_301; 
lean_inc(x_2);
lean_inc(x_257);
x_301 = l_Lean_Closure_collectExprAux___main(x_257, x_2, x_258);
if (lean_obj_tag(x_301) == 0)
{
lean_object* x_302; lean_object* x_303; uint8_t x_304; 
x_302 = lean_ctor_get(x_301, 1);
lean_inc(x_302);
x_303 = lean_ctor_get(x_301, 0);
lean_inc(x_303);
lean_dec(x_301);
x_304 = !lean_is_exclusive(x_302);
if (x_304 == 0)
{
lean_object* x_305; lean_object* x_306; 
x_305 = lean_ctor_get(x_302, 4);
lean_inc(x_303);
x_306 = l_Std_HashMapImp_insert___at_Lean_Closure_visitExpr___spec__3(x_305, x_257, x_303);
lean_ctor_set(x_302, 4, x_306);
x_259 = x_303;
x_260 = x_302;
goto block_297;
}
else
{
lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; 
x_307 = lean_ctor_get(x_302, 0);
x_308 = lean_ctor_get(x_302, 1);
x_309 = lean_ctor_get(x_302, 2);
x_310 = lean_ctor_get(x_302, 3);
x_311 = lean_ctor_get(x_302, 4);
x_312 = lean_ctor_get(x_302, 5);
x_313 = lean_ctor_get(x_302, 6);
x_314 = lean_ctor_get(x_302, 7);
x_315 = lean_ctor_get(x_302, 8);
x_316 = lean_ctor_get(x_302, 9);
lean_inc(x_316);
lean_inc(x_315);
lean_inc(x_314);
lean_inc(x_313);
lean_inc(x_312);
lean_inc(x_311);
lean_inc(x_310);
lean_inc(x_309);
lean_inc(x_308);
lean_inc(x_307);
lean_dec(x_302);
lean_inc(x_303);
x_317 = l_Std_HashMapImp_insert___at_Lean_Closure_visitExpr___spec__3(x_311, x_257, x_303);
x_318 = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(x_318, 0, x_307);
lean_ctor_set(x_318, 1, x_308);
lean_ctor_set(x_318, 2, x_309);
lean_ctor_set(x_318, 3, x_310);
lean_ctor_set(x_318, 4, x_317);
lean_ctor_set(x_318, 5, x_312);
lean_ctor_set(x_318, 6, x_313);
lean_ctor_set(x_318, 7, x_314);
lean_ctor_set(x_318, 8, x_315);
lean_ctor_set(x_318, 9, x_316);
x_259 = x_303;
x_260 = x_318;
goto block_297;
}
}
else
{
uint8_t x_319; 
lean_dec(x_257);
lean_dec(x_2);
lean_dec(x_1);
x_319 = !lean_is_exclusive(x_301);
if (x_319 == 0)
{
return x_301;
}
else
{
lean_object* x_320; lean_object* x_321; lean_object* x_322; 
x_320 = lean_ctor_get(x_301, 0);
x_321 = lean_ctor_get(x_301, 1);
lean_inc(x_321);
lean_inc(x_320);
lean_dec(x_301);
x_322 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_322, 0, x_320);
lean_ctor_set(x_322, 1, x_321);
return x_322;
}
}
}
else
{
lean_object* x_323; 
lean_dec(x_257);
x_323 = lean_ctor_get(x_300, 0);
lean_inc(x_323);
lean_dec(x_300);
x_259 = x_323;
x_260 = x_258;
goto block_297;
}
}
}
}
else
{
lean_object* x_331; lean_object* x_332; lean_object* x_333; 
x_331 = lean_ctor_get(x_248, 0);
x_332 = lean_ctor_get(x_248, 1);
lean_inc(x_332);
lean_inc(x_331);
lean_dec(x_248);
x_333 = lean_metavar_ctx_find_decl(x_331, x_247);
if (lean_obj_tag(x_333) == 0)
{
lean_object* x_334; lean_object* x_335; 
lean_dec(x_2);
lean_dec(x_1);
x_334 = l_Lean_MetavarContext_getDecl___closed__2;
x_335 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_335, 0, x_334);
lean_ctor_set(x_335, 1, x_332);
return x_335;
}
else
{
lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_364; uint8_t x_389; 
x_336 = lean_ctor_get(x_333, 0);
lean_inc(x_336);
lean_dec(x_333);
x_337 = lean_ctor_get(x_336, 2);
lean_inc(x_337);
lean_dec(x_336);
x_338 = l_Lean_Closure_instantiateMVars(x_337, x_2, x_332);
x_339 = lean_ctor_get(x_338, 0);
lean_inc(x_339);
x_340 = lean_ctor_get(x_338, 1);
lean_inc(x_340);
lean_dec(x_338);
x_389 = l_Lean_Expr_hasLevelParam(x_339);
if (x_389 == 0)
{
uint8_t x_390; 
x_390 = l_Lean_Expr_hasFVar(x_339);
if (x_390 == 0)
{
uint8_t x_391; 
x_391 = l_Lean_Expr_hasMVar(x_339);
if (x_391 == 0)
{
x_341 = x_339;
x_342 = x_340;
goto block_363;
}
else
{
lean_object* x_392; 
x_392 = lean_box(0);
x_364 = x_392;
goto block_388;
}
}
else
{
lean_object* x_393; 
x_393 = lean_box(0);
x_364 = x_393;
goto block_388;
}
}
else
{
lean_object* x_394; 
x_394 = lean_box(0);
x_364 = x_394;
goto block_388;
}
block_363:
{
lean_object* x_343; uint8_t x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; 
x_343 = lean_box(0);
x_344 = 0;
x_345 = l_Lean_Closure_mkLocalDecl(x_343, x_341, x_344, x_2, x_342);
lean_dec(x_2);
x_346 = lean_ctor_get(x_345, 1);
lean_inc(x_346);
x_347 = lean_ctor_get(x_345, 0);
lean_inc(x_347);
if (lean_is_exclusive(x_345)) {
 lean_ctor_release(x_345, 0);
 lean_ctor_release(x_345, 1);
 x_348 = x_345;
} else {
 lean_dec_ref(x_345);
 x_348 = lean_box(0);
}
x_349 = lean_ctor_get(x_346, 0);
lean_inc(x_349);
x_350 = lean_ctor_get(x_346, 1);
lean_inc(x_350);
x_351 = lean_ctor_get(x_346, 2);
lean_inc(x_351);
x_352 = lean_ctor_get(x_346, 3);
lean_inc(x_352);
x_353 = lean_ctor_get(x_346, 4);
lean_inc(x_353);
x_354 = lean_ctor_get(x_346, 5);
lean_inc(x_354);
x_355 = lean_ctor_get(x_346, 6);
lean_inc(x_355);
x_356 = lean_ctor_get(x_346, 7);
lean_inc(x_356);
x_357 = lean_ctor_get(x_346, 8);
lean_inc(x_357);
x_358 = lean_ctor_get(x_346, 9);
lean_inc(x_358);
if (lean_is_exclusive(x_346)) {
 lean_ctor_release(x_346, 0);
 lean_ctor_release(x_346, 1);
 lean_ctor_release(x_346, 2);
 lean_ctor_release(x_346, 3);
 lean_ctor_release(x_346, 4);
 lean_ctor_release(x_346, 5);
 lean_ctor_release(x_346, 6);
 lean_ctor_release(x_346, 7);
 lean_ctor_release(x_346, 8);
 lean_ctor_release(x_346, 9);
 x_359 = x_346;
} else {
 lean_dec_ref(x_346);
 x_359 = lean_box(0);
}
x_360 = lean_array_push(x_358, x_1);
if (lean_is_scalar(x_359)) {
 x_361 = lean_alloc_ctor(0, 10, 0);
} else {
 x_361 = x_359;
}
lean_ctor_set(x_361, 0, x_349);
lean_ctor_set(x_361, 1, x_350);
lean_ctor_set(x_361, 2, x_351);
lean_ctor_set(x_361, 3, x_352);
lean_ctor_set(x_361, 4, x_353);
lean_ctor_set(x_361, 5, x_354);
lean_ctor_set(x_361, 6, x_355);
lean_ctor_set(x_361, 7, x_356);
lean_ctor_set(x_361, 8, x_357);
lean_ctor_set(x_361, 9, x_360);
if (lean_is_scalar(x_348)) {
 x_362 = lean_alloc_ctor(0, 2, 0);
} else {
 x_362 = x_348;
}
lean_ctor_set(x_362, 0, x_347);
lean_ctor_set(x_362, 1, x_361);
return x_362;
}
block_388:
{
lean_object* x_365; lean_object* x_366; 
lean_dec(x_364);
x_365 = lean_ctor_get(x_340, 4);
lean_inc(x_365);
x_366 = l_Std_HashMapImp_find_x3f___at_Lean_Closure_visitExpr___spec__1(x_365, x_339);
lean_dec(x_365);
if (lean_obj_tag(x_366) == 0)
{
lean_object* x_367; 
lean_inc(x_2);
lean_inc(x_339);
x_367 = l_Lean_Closure_collectExprAux___main(x_339, x_2, x_340);
if (lean_obj_tag(x_367) == 0)
{
lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; 
x_368 = lean_ctor_get(x_367, 1);
lean_inc(x_368);
x_369 = lean_ctor_get(x_367, 0);
lean_inc(x_369);
lean_dec(x_367);
x_370 = lean_ctor_get(x_368, 0);
lean_inc(x_370);
x_371 = lean_ctor_get(x_368, 1);
lean_inc(x_371);
x_372 = lean_ctor_get(x_368, 2);
lean_inc(x_372);
x_373 = lean_ctor_get(x_368, 3);
lean_inc(x_373);
x_374 = lean_ctor_get(x_368, 4);
lean_inc(x_374);
x_375 = lean_ctor_get(x_368, 5);
lean_inc(x_375);
x_376 = lean_ctor_get(x_368, 6);
lean_inc(x_376);
x_377 = lean_ctor_get(x_368, 7);
lean_inc(x_377);
x_378 = lean_ctor_get(x_368, 8);
lean_inc(x_378);
x_379 = lean_ctor_get(x_368, 9);
lean_inc(x_379);
if (lean_is_exclusive(x_368)) {
 lean_ctor_release(x_368, 0);
 lean_ctor_release(x_368, 1);
 lean_ctor_release(x_368, 2);
 lean_ctor_release(x_368, 3);
 lean_ctor_release(x_368, 4);
 lean_ctor_release(x_368, 5);
 lean_ctor_release(x_368, 6);
 lean_ctor_release(x_368, 7);
 lean_ctor_release(x_368, 8);
 lean_ctor_release(x_368, 9);
 x_380 = x_368;
} else {
 lean_dec_ref(x_368);
 x_380 = lean_box(0);
}
lean_inc(x_369);
x_381 = l_Std_HashMapImp_insert___at_Lean_Closure_visitExpr___spec__3(x_374, x_339, x_369);
if (lean_is_scalar(x_380)) {
 x_382 = lean_alloc_ctor(0, 10, 0);
} else {
 x_382 = x_380;
}
lean_ctor_set(x_382, 0, x_370);
lean_ctor_set(x_382, 1, x_371);
lean_ctor_set(x_382, 2, x_372);
lean_ctor_set(x_382, 3, x_373);
lean_ctor_set(x_382, 4, x_381);
lean_ctor_set(x_382, 5, x_375);
lean_ctor_set(x_382, 6, x_376);
lean_ctor_set(x_382, 7, x_377);
lean_ctor_set(x_382, 8, x_378);
lean_ctor_set(x_382, 9, x_379);
x_341 = x_369;
x_342 = x_382;
goto block_363;
}
else
{
lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; 
lean_dec(x_339);
lean_dec(x_2);
lean_dec(x_1);
x_383 = lean_ctor_get(x_367, 0);
lean_inc(x_383);
x_384 = lean_ctor_get(x_367, 1);
lean_inc(x_384);
if (lean_is_exclusive(x_367)) {
 lean_ctor_release(x_367, 0);
 lean_ctor_release(x_367, 1);
 x_385 = x_367;
} else {
 lean_dec_ref(x_367);
 x_385 = lean_box(0);
}
if (lean_is_scalar(x_385)) {
 x_386 = lean_alloc_ctor(1, 2, 0);
} else {
 x_386 = x_385;
}
lean_ctor_set(x_386, 0, x_383);
lean_ctor_set(x_386, 1, x_384);
return x_386;
}
}
else
{
lean_object* x_387; 
lean_dec(x_339);
x_387 = lean_ctor_get(x_366, 0);
lean_inc(x_387);
lean_dec(x_366);
x_341 = x_387;
x_342 = x_340;
goto block_363;
}
}
}
}
}
case 3:
{
lean_object* x_395; lean_object* x_396; uint8_t x_397; 
x_395 = lean_ctor_get(x_1, 0);
lean_inc(x_395);
x_396 = l_Lean_Closure_collectLevel(x_395, x_2, x_3);
lean_dec(x_2);
x_397 = !lean_is_exclusive(x_396);
if (x_397 == 0)
{
lean_object* x_398; lean_object* x_399; 
x_398 = lean_ctor_get(x_396, 0);
x_399 = lean_expr_update_sort(x_1, x_398);
lean_ctor_set(x_396, 0, x_399);
return x_396;
}
else
{
lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; 
x_400 = lean_ctor_get(x_396, 0);
x_401 = lean_ctor_get(x_396, 1);
lean_inc(x_401);
lean_inc(x_400);
lean_dec(x_396);
x_402 = lean_expr_update_sort(x_1, x_400);
x_403 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_403, 0, x_402);
lean_ctor_set(x_403, 1, x_401);
return x_403;
}
}
case 4:
{
lean_object* x_404; lean_object* x_405; uint8_t x_406; 
x_404 = lean_ctor_get(x_1, 1);
lean_inc(x_404);
x_405 = l_List_mapM___main___at_Lean_Closure_collectExprAux___main___spec__1(x_404, x_2, x_3);
lean_dec(x_2);
x_406 = !lean_is_exclusive(x_405);
if (x_406 == 0)
{
lean_object* x_407; lean_object* x_408; 
x_407 = lean_ctor_get(x_405, 0);
x_408 = lean_expr_update_const(x_1, x_407);
lean_ctor_set(x_405, 0, x_408);
return x_405;
}
else
{
lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; 
x_409 = lean_ctor_get(x_405, 0);
x_410 = lean_ctor_get(x_405, 1);
lean_inc(x_410);
lean_inc(x_409);
lean_dec(x_405);
x_411 = lean_expr_update_const(x_1, x_409);
x_412 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_412, 0, x_411);
lean_ctor_set(x_412, 1, x_410);
return x_412;
}
}
case 5:
{
lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_460; uint8_t x_487; 
x_413 = lean_ctor_get(x_1, 0);
lean_inc(x_413);
x_414 = lean_ctor_get(x_1, 1);
lean_inc(x_414);
x_487 = l_Lean_Expr_hasLevelParam(x_413);
if (x_487 == 0)
{
uint8_t x_488; 
x_488 = l_Lean_Expr_hasFVar(x_413);
if (x_488 == 0)
{
uint8_t x_489; 
x_489 = l_Lean_Expr_hasMVar(x_413);
if (x_489 == 0)
{
x_415 = x_413;
x_416 = x_3;
goto block_459;
}
else
{
lean_object* x_490; 
x_490 = lean_box(0);
x_460 = x_490;
goto block_486;
}
}
else
{
lean_object* x_491; 
x_491 = lean_box(0);
x_460 = x_491;
goto block_486;
}
}
else
{
lean_object* x_492; 
x_492 = lean_box(0);
x_460 = x_492;
goto block_486;
}
block_459:
{
lean_object* x_417; lean_object* x_418; lean_object* x_426; uint8_t x_453; 
x_453 = l_Lean_Expr_hasLevelParam(x_414);
if (x_453 == 0)
{
uint8_t x_454; 
x_454 = l_Lean_Expr_hasFVar(x_414);
if (x_454 == 0)
{
uint8_t x_455; 
x_455 = l_Lean_Expr_hasMVar(x_414);
if (x_455 == 0)
{
lean_dec(x_2);
x_417 = x_414;
x_418 = x_416;
goto block_425;
}
else
{
lean_object* x_456; 
x_456 = lean_box(0);
x_426 = x_456;
goto block_452;
}
}
else
{
lean_object* x_457; 
x_457 = lean_box(0);
x_426 = x_457;
goto block_452;
}
}
else
{
lean_object* x_458; 
x_458 = lean_box(0);
x_426 = x_458;
goto block_452;
}
block_425:
{
if (lean_obj_tag(x_1) == 5)
{
lean_object* x_419; lean_object* x_420; 
x_419 = lean_expr_update_app(x_1, x_415, x_417);
x_420 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_420, 0, x_419);
lean_ctor_set(x_420, 1, x_418);
return x_420;
}
else
{
lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; 
lean_dec(x_417);
lean_dec(x_415);
lean_dec(x_1);
x_421 = l_Lean_Expr_Inhabited;
x_422 = l_Lean_Expr_updateApp_x21___closed__1;
x_423 = lean_panic_fn(x_421, x_422);
x_424 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_424, 0, x_423);
lean_ctor_set(x_424, 1, x_418);
return x_424;
}
}
block_452:
{
lean_object* x_427; lean_object* x_428; 
lean_dec(x_426);
x_427 = lean_ctor_get(x_416, 4);
lean_inc(x_427);
x_428 = l_Std_HashMapImp_find_x3f___at_Lean_Closure_visitExpr___spec__1(x_427, x_414);
lean_dec(x_427);
if (lean_obj_tag(x_428) == 0)
{
lean_object* x_429; 
lean_inc(x_414);
x_429 = l_Lean_Closure_collectExprAux___main(x_414, x_2, x_416);
if (lean_obj_tag(x_429) == 0)
{
lean_object* x_430; lean_object* x_431; uint8_t x_432; 
x_430 = lean_ctor_get(x_429, 1);
lean_inc(x_430);
x_431 = lean_ctor_get(x_429, 0);
lean_inc(x_431);
lean_dec(x_429);
x_432 = !lean_is_exclusive(x_430);
if (x_432 == 0)
{
lean_object* x_433; lean_object* x_434; 
x_433 = lean_ctor_get(x_430, 4);
lean_inc(x_431);
x_434 = l_Std_HashMapImp_insert___at_Lean_Closure_visitExpr___spec__3(x_433, x_414, x_431);
lean_ctor_set(x_430, 4, x_434);
x_417 = x_431;
x_418 = x_430;
goto block_425;
}
else
{
lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; 
x_435 = lean_ctor_get(x_430, 0);
x_436 = lean_ctor_get(x_430, 1);
x_437 = lean_ctor_get(x_430, 2);
x_438 = lean_ctor_get(x_430, 3);
x_439 = lean_ctor_get(x_430, 4);
x_440 = lean_ctor_get(x_430, 5);
x_441 = lean_ctor_get(x_430, 6);
x_442 = lean_ctor_get(x_430, 7);
x_443 = lean_ctor_get(x_430, 8);
x_444 = lean_ctor_get(x_430, 9);
lean_inc(x_444);
lean_inc(x_443);
lean_inc(x_442);
lean_inc(x_441);
lean_inc(x_440);
lean_inc(x_439);
lean_inc(x_438);
lean_inc(x_437);
lean_inc(x_436);
lean_inc(x_435);
lean_dec(x_430);
lean_inc(x_431);
x_445 = l_Std_HashMapImp_insert___at_Lean_Closure_visitExpr___spec__3(x_439, x_414, x_431);
x_446 = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(x_446, 0, x_435);
lean_ctor_set(x_446, 1, x_436);
lean_ctor_set(x_446, 2, x_437);
lean_ctor_set(x_446, 3, x_438);
lean_ctor_set(x_446, 4, x_445);
lean_ctor_set(x_446, 5, x_440);
lean_ctor_set(x_446, 6, x_441);
lean_ctor_set(x_446, 7, x_442);
lean_ctor_set(x_446, 8, x_443);
lean_ctor_set(x_446, 9, x_444);
x_417 = x_431;
x_418 = x_446;
goto block_425;
}
}
else
{
uint8_t x_447; 
lean_dec(x_415);
lean_dec(x_414);
lean_dec(x_1);
x_447 = !lean_is_exclusive(x_429);
if (x_447 == 0)
{
return x_429;
}
else
{
lean_object* x_448; lean_object* x_449; lean_object* x_450; 
x_448 = lean_ctor_get(x_429, 0);
x_449 = lean_ctor_get(x_429, 1);
lean_inc(x_449);
lean_inc(x_448);
lean_dec(x_429);
x_450 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_450, 0, x_448);
lean_ctor_set(x_450, 1, x_449);
return x_450;
}
}
}
else
{
lean_object* x_451; 
lean_dec(x_414);
lean_dec(x_2);
x_451 = lean_ctor_get(x_428, 0);
lean_inc(x_451);
lean_dec(x_428);
x_417 = x_451;
x_418 = x_416;
goto block_425;
}
}
}
block_486:
{
lean_object* x_461; lean_object* x_462; 
lean_dec(x_460);
x_461 = lean_ctor_get(x_3, 4);
lean_inc(x_461);
x_462 = l_Std_HashMapImp_find_x3f___at_Lean_Closure_visitExpr___spec__1(x_461, x_413);
lean_dec(x_461);
if (lean_obj_tag(x_462) == 0)
{
lean_object* x_463; 
lean_inc(x_2);
lean_inc(x_413);
x_463 = l_Lean_Closure_collectExprAux___main(x_413, x_2, x_3);
if (lean_obj_tag(x_463) == 0)
{
lean_object* x_464; lean_object* x_465; uint8_t x_466; 
x_464 = lean_ctor_get(x_463, 1);
lean_inc(x_464);
x_465 = lean_ctor_get(x_463, 0);
lean_inc(x_465);
lean_dec(x_463);
x_466 = !lean_is_exclusive(x_464);
if (x_466 == 0)
{
lean_object* x_467; lean_object* x_468; 
x_467 = lean_ctor_get(x_464, 4);
lean_inc(x_465);
x_468 = l_Std_HashMapImp_insert___at_Lean_Closure_visitExpr___spec__3(x_467, x_413, x_465);
lean_ctor_set(x_464, 4, x_468);
x_415 = x_465;
x_416 = x_464;
goto block_459;
}
else
{
lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; 
x_469 = lean_ctor_get(x_464, 0);
x_470 = lean_ctor_get(x_464, 1);
x_471 = lean_ctor_get(x_464, 2);
x_472 = lean_ctor_get(x_464, 3);
x_473 = lean_ctor_get(x_464, 4);
x_474 = lean_ctor_get(x_464, 5);
x_475 = lean_ctor_get(x_464, 6);
x_476 = lean_ctor_get(x_464, 7);
x_477 = lean_ctor_get(x_464, 8);
x_478 = lean_ctor_get(x_464, 9);
lean_inc(x_478);
lean_inc(x_477);
lean_inc(x_476);
lean_inc(x_475);
lean_inc(x_474);
lean_inc(x_473);
lean_inc(x_472);
lean_inc(x_471);
lean_inc(x_470);
lean_inc(x_469);
lean_dec(x_464);
lean_inc(x_465);
x_479 = l_Std_HashMapImp_insert___at_Lean_Closure_visitExpr___spec__3(x_473, x_413, x_465);
x_480 = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(x_480, 0, x_469);
lean_ctor_set(x_480, 1, x_470);
lean_ctor_set(x_480, 2, x_471);
lean_ctor_set(x_480, 3, x_472);
lean_ctor_set(x_480, 4, x_479);
lean_ctor_set(x_480, 5, x_474);
lean_ctor_set(x_480, 6, x_475);
lean_ctor_set(x_480, 7, x_476);
lean_ctor_set(x_480, 8, x_477);
lean_ctor_set(x_480, 9, x_478);
x_415 = x_465;
x_416 = x_480;
goto block_459;
}
}
else
{
uint8_t x_481; 
lean_dec(x_414);
lean_dec(x_413);
lean_dec(x_2);
lean_dec(x_1);
x_481 = !lean_is_exclusive(x_463);
if (x_481 == 0)
{
return x_463;
}
else
{
lean_object* x_482; lean_object* x_483; lean_object* x_484; 
x_482 = lean_ctor_get(x_463, 0);
x_483 = lean_ctor_get(x_463, 1);
lean_inc(x_483);
lean_inc(x_482);
lean_dec(x_463);
x_484 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_484, 0, x_482);
lean_ctor_set(x_484, 1, x_483);
return x_484;
}
}
}
else
{
lean_object* x_485; 
lean_dec(x_413);
x_485 = lean_ctor_get(x_462, 0);
lean_inc(x_485);
lean_dec(x_462);
x_415 = x_485;
x_416 = x_3;
goto block_459;
}
}
}
case 6:
{
lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_542; uint8_t x_569; 
x_493 = lean_ctor_get(x_1, 1);
lean_inc(x_493);
x_494 = lean_ctor_get(x_1, 2);
lean_inc(x_494);
x_569 = l_Lean_Expr_hasLevelParam(x_493);
if (x_569 == 0)
{
uint8_t x_570; 
x_570 = l_Lean_Expr_hasFVar(x_493);
if (x_570 == 0)
{
uint8_t x_571; 
x_571 = l_Lean_Expr_hasMVar(x_493);
if (x_571 == 0)
{
x_495 = x_493;
x_496 = x_3;
goto block_541;
}
else
{
lean_object* x_572; 
x_572 = lean_box(0);
x_542 = x_572;
goto block_568;
}
}
else
{
lean_object* x_573; 
x_573 = lean_box(0);
x_542 = x_573;
goto block_568;
}
}
else
{
lean_object* x_574; 
x_574 = lean_box(0);
x_542 = x_574;
goto block_568;
}
block_541:
{
lean_object* x_497; lean_object* x_498; lean_object* x_508; uint8_t x_535; 
x_535 = l_Lean_Expr_hasLevelParam(x_494);
if (x_535 == 0)
{
uint8_t x_536; 
x_536 = l_Lean_Expr_hasFVar(x_494);
if (x_536 == 0)
{
uint8_t x_537; 
x_537 = l_Lean_Expr_hasMVar(x_494);
if (x_537 == 0)
{
lean_dec(x_2);
x_497 = x_494;
x_498 = x_496;
goto block_507;
}
else
{
lean_object* x_538; 
x_538 = lean_box(0);
x_508 = x_538;
goto block_534;
}
}
else
{
lean_object* x_539; 
x_539 = lean_box(0);
x_508 = x_539;
goto block_534;
}
}
else
{
lean_object* x_540; 
x_540 = lean_box(0);
x_508 = x_540;
goto block_534;
}
block_507:
{
if (lean_obj_tag(x_1) == 6)
{
uint64_t x_499; uint8_t x_500; lean_object* x_501; lean_object* x_502; 
x_499 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
x_500 = (uint8_t)((x_499 << 24) >> 61);
x_501 = lean_expr_update_lambda(x_1, x_500, x_495, x_497);
x_502 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_502, 0, x_501);
lean_ctor_set(x_502, 1, x_498);
return x_502;
}
else
{
lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; 
lean_dec(x_497);
lean_dec(x_495);
lean_dec(x_1);
x_503 = l_Lean_Expr_Inhabited;
x_504 = l_Lean_Expr_updateLambdaE_x21___closed__1;
x_505 = lean_panic_fn(x_503, x_504);
x_506 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_506, 0, x_505);
lean_ctor_set(x_506, 1, x_498);
return x_506;
}
}
block_534:
{
lean_object* x_509; lean_object* x_510; 
lean_dec(x_508);
x_509 = lean_ctor_get(x_496, 4);
lean_inc(x_509);
x_510 = l_Std_HashMapImp_find_x3f___at_Lean_Closure_visitExpr___spec__1(x_509, x_494);
lean_dec(x_509);
if (lean_obj_tag(x_510) == 0)
{
lean_object* x_511; 
lean_inc(x_494);
x_511 = l_Lean_Closure_collectExprAux___main(x_494, x_2, x_496);
if (lean_obj_tag(x_511) == 0)
{
lean_object* x_512; lean_object* x_513; uint8_t x_514; 
x_512 = lean_ctor_get(x_511, 1);
lean_inc(x_512);
x_513 = lean_ctor_get(x_511, 0);
lean_inc(x_513);
lean_dec(x_511);
x_514 = !lean_is_exclusive(x_512);
if (x_514 == 0)
{
lean_object* x_515; lean_object* x_516; 
x_515 = lean_ctor_get(x_512, 4);
lean_inc(x_513);
x_516 = l_Std_HashMapImp_insert___at_Lean_Closure_visitExpr___spec__3(x_515, x_494, x_513);
lean_ctor_set(x_512, 4, x_516);
x_497 = x_513;
x_498 = x_512;
goto block_507;
}
else
{
lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; 
x_517 = lean_ctor_get(x_512, 0);
x_518 = lean_ctor_get(x_512, 1);
x_519 = lean_ctor_get(x_512, 2);
x_520 = lean_ctor_get(x_512, 3);
x_521 = lean_ctor_get(x_512, 4);
x_522 = lean_ctor_get(x_512, 5);
x_523 = lean_ctor_get(x_512, 6);
x_524 = lean_ctor_get(x_512, 7);
x_525 = lean_ctor_get(x_512, 8);
x_526 = lean_ctor_get(x_512, 9);
lean_inc(x_526);
lean_inc(x_525);
lean_inc(x_524);
lean_inc(x_523);
lean_inc(x_522);
lean_inc(x_521);
lean_inc(x_520);
lean_inc(x_519);
lean_inc(x_518);
lean_inc(x_517);
lean_dec(x_512);
lean_inc(x_513);
x_527 = l_Std_HashMapImp_insert___at_Lean_Closure_visitExpr___spec__3(x_521, x_494, x_513);
x_528 = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(x_528, 0, x_517);
lean_ctor_set(x_528, 1, x_518);
lean_ctor_set(x_528, 2, x_519);
lean_ctor_set(x_528, 3, x_520);
lean_ctor_set(x_528, 4, x_527);
lean_ctor_set(x_528, 5, x_522);
lean_ctor_set(x_528, 6, x_523);
lean_ctor_set(x_528, 7, x_524);
lean_ctor_set(x_528, 8, x_525);
lean_ctor_set(x_528, 9, x_526);
x_497 = x_513;
x_498 = x_528;
goto block_507;
}
}
else
{
uint8_t x_529; 
lean_dec(x_495);
lean_dec(x_494);
lean_dec(x_1);
x_529 = !lean_is_exclusive(x_511);
if (x_529 == 0)
{
return x_511;
}
else
{
lean_object* x_530; lean_object* x_531; lean_object* x_532; 
x_530 = lean_ctor_get(x_511, 0);
x_531 = lean_ctor_get(x_511, 1);
lean_inc(x_531);
lean_inc(x_530);
lean_dec(x_511);
x_532 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_532, 0, x_530);
lean_ctor_set(x_532, 1, x_531);
return x_532;
}
}
}
else
{
lean_object* x_533; 
lean_dec(x_494);
lean_dec(x_2);
x_533 = lean_ctor_get(x_510, 0);
lean_inc(x_533);
lean_dec(x_510);
x_497 = x_533;
x_498 = x_496;
goto block_507;
}
}
}
block_568:
{
lean_object* x_543; lean_object* x_544; 
lean_dec(x_542);
x_543 = lean_ctor_get(x_3, 4);
lean_inc(x_543);
x_544 = l_Std_HashMapImp_find_x3f___at_Lean_Closure_visitExpr___spec__1(x_543, x_493);
lean_dec(x_543);
if (lean_obj_tag(x_544) == 0)
{
lean_object* x_545; 
lean_inc(x_2);
lean_inc(x_493);
x_545 = l_Lean_Closure_collectExprAux___main(x_493, x_2, x_3);
if (lean_obj_tag(x_545) == 0)
{
lean_object* x_546; lean_object* x_547; uint8_t x_548; 
x_546 = lean_ctor_get(x_545, 1);
lean_inc(x_546);
x_547 = lean_ctor_get(x_545, 0);
lean_inc(x_547);
lean_dec(x_545);
x_548 = !lean_is_exclusive(x_546);
if (x_548 == 0)
{
lean_object* x_549; lean_object* x_550; 
x_549 = lean_ctor_get(x_546, 4);
lean_inc(x_547);
x_550 = l_Std_HashMapImp_insert___at_Lean_Closure_visitExpr___spec__3(x_549, x_493, x_547);
lean_ctor_set(x_546, 4, x_550);
x_495 = x_547;
x_496 = x_546;
goto block_541;
}
else
{
lean_object* x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; lean_object* x_561; lean_object* x_562; 
x_551 = lean_ctor_get(x_546, 0);
x_552 = lean_ctor_get(x_546, 1);
x_553 = lean_ctor_get(x_546, 2);
x_554 = lean_ctor_get(x_546, 3);
x_555 = lean_ctor_get(x_546, 4);
x_556 = lean_ctor_get(x_546, 5);
x_557 = lean_ctor_get(x_546, 6);
x_558 = lean_ctor_get(x_546, 7);
x_559 = lean_ctor_get(x_546, 8);
x_560 = lean_ctor_get(x_546, 9);
lean_inc(x_560);
lean_inc(x_559);
lean_inc(x_558);
lean_inc(x_557);
lean_inc(x_556);
lean_inc(x_555);
lean_inc(x_554);
lean_inc(x_553);
lean_inc(x_552);
lean_inc(x_551);
lean_dec(x_546);
lean_inc(x_547);
x_561 = l_Std_HashMapImp_insert___at_Lean_Closure_visitExpr___spec__3(x_555, x_493, x_547);
x_562 = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(x_562, 0, x_551);
lean_ctor_set(x_562, 1, x_552);
lean_ctor_set(x_562, 2, x_553);
lean_ctor_set(x_562, 3, x_554);
lean_ctor_set(x_562, 4, x_561);
lean_ctor_set(x_562, 5, x_556);
lean_ctor_set(x_562, 6, x_557);
lean_ctor_set(x_562, 7, x_558);
lean_ctor_set(x_562, 8, x_559);
lean_ctor_set(x_562, 9, x_560);
x_495 = x_547;
x_496 = x_562;
goto block_541;
}
}
else
{
uint8_t x_563; 
lean_dec(x_494);
lean_dec(x_493);
lean_dec(x_2);
lean_dec(x_1);
x_563 = !lean_is_exclusive(x_545);
if (x_563 == 0)
{
return x_545;
}
else
{
lean_object* x_564; lean_object* x_565; lean_object* x_566; 
x_564 = lean_ctor_get(x_545, 0);
x_565 = lean_ctor_get(x_545, 1);
lean_inc(x_565);
lean_inc(x_564);
lean_dec(x_545);
x_566 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_566, 0, x_564);
lean_ctor_set(x_566, 1, x_565);
return x_566;
}
}
}
else
{
lean_object* x_567; 
lean_dec(x_493);
x_567 = lean_ctor_get(x_544, 0);
lean_inc(x_567);
lean_dec(x_544);
x_495 = x_567;
x_496 = x_3;
goto block_541;
}
}
}
case 7:
{
lean_object* x_575; lean_object* x_576; lean_object* x_577; lean_object* x_578; lean_object* x_624; uint8_t x_651; 
x_575 = lean_ctor_get(x_1, 1);
lean_inc(x_575);
x_576 = lean_ctor_get(x_1, 2);
lean_inc(x_576);
x_651 = l_Lean_Expr_hasLevelParam(x_575);
if (x_651 == 0)
{
uint8_t x_652; 
x_652 = l_Lean_Expr_hasFVar(x_575);
if (x_652 == 0)
{
uint8_t x_653; 
x_653 = l_Lean_Expr_hasMVar(x_575);
if (x_653 == 0)
{
x_577 = x_575;
x_578 = x_3;
goto block_623;
}
else
{
lean_object* x_654; 
x_654 = lean_box(0);
x_624 = x_654;
goto block_650;
}
}
else
{
lean_object* x_655; 
x_655 = lean_box(0);
x_624 = x_655;
goto block_650;
}
}
else
{
lean_object* x_656; 
x_656 = lean_box(0);
x_624 = x_656;
goto block_650;
}
block_623:
{
lean_object* x_579; lean_object* x_580; lean_object* x_590; uint8_t x_617; 
x_617 = l_Lean_Expr_hasLevelParam(x_576);
if (x_617 == 0)
{
uint8_t x_618; 
x_618 = l_Lean_Expr_hasFVar(x_576);
if (x_618 == 0)
{
uint8_t x_619; 
x_619 = l_Lean_Expr_hasMVar(x_576);
if (x_619 == 0)
{
lean_dec(x_2);
x_579 = x_576;
x_580 = x_578;
goto block_589;
}
else
{
lean_object* x_620; 
x_620 = lean_box(0);
x_590 = x_620;
goto block_616;
}
}
else
{
lean_object* x_621; 
x_621 = lean_box(0);
x_590 = x_621;
goto block_616;
}
}
else
{
lean_object* x_622; 
x_622 = lean_box(0);
x_590 = x_622;
goto block_616;
}
block_589:
{
if (lean_obj_tag(x_1) == 7)
{
uint64_t x_581; uint8_t x_582; lean_object* x_583; lean_object* x_584; 
x_581 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
x_582 = (uint8_t)((x_581 << 24) >> 61);
x_583 = lean_expr_update_forall(x_1, x_582, x_577, x_579);
x_584 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_584, 0, x_583);
lean_ctor_set(x_584, 1, x_580);
return x_584;
}
else
{
lean_object* x_585; lean_object* x_586; lean_object* x_587; lean_object* x_588; 
lean_dec(x_579);
lean_dec(x_577);
lean_dec(x_1);
x_585 = l_Lean_Expr_Inhabited;
x_586 = l_Lean_Expr_updateForallE_x21___closed__1;
x_587 = lean_panic_fn(x_585, x_586);
x_588 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_588, 0, x_587);
lean_ctor_set(x_588, 1, x_580);
return x_588;
}
}
block_616:
{
lean_object* x_591; lean_object* x_592; 
lean_dec(x_590);
x_591 = lean_ctor_get(x_578, 4);
lean_inc(x_591);
x_592 = l_Std_HashMapImp_find_x3f___at_Lean_Closure_visitExpr___spec__1(x_591, x_576);
lean_dec(x_591);
if (lean_obj_tag(x_592) == 0)
{
lean_object* x_593; 
lean_inc(x_576);
x_593 = l_Lean_Closure_collectExprAux___main(x_576, x_2, x_578);
if (lean_obj_tag(x_593) == 0)
{
lean_object* x_594; lean_object* x_595; uint8_t x_596; 
x_594 = lean_ctor_get(x_593, 1);
lean_inc(x_594);
x_595 = lean_ctor_get(x_593, 0);
lean_inc(x_595);
lean_dec(x_593);
x_596 = !lean_is_exclusive(x_594);
if (x_596 == 0)
{
lean_object* x_597; lean_object* x_598; 
x_597 = lean_ctor_get(x_594, 4);
lean_inc(x_595);
x_598 = l_Std_HashMapImp_insert___at_Lean_Closure_visitExpr___spec__3(x_597, x_576, x_595);
lean_ctor_set(x_594, 4, x_598);
x_579 = x_595;
x_580 = x_594;
goto block_589;
}
else
{
lean_object* x_599; lean_object* x_600; lean_object* x_601; lean_object* x_602; lean_object* x_603; lean_object* x_604; lean_object* x_605; lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; lean_object* x_610; 
x_599 = lean_ctor_get(x_594, 0);
x_600 = lean_ctor_get(x_594, 1);
x_601 = lean_ctor_get(x_594, 2);
x_602 = lean_ctor_get(x_594, 3);
x_603 = lean_ctor_get(x_594, 4);
x_604 = lean_ctor_get(x_594, 5);
x_605 = lean_ctor_get(x_594, 6);
x_606 = lean_ctor_get(x_594, 7);
x_607 = lean_ctor_get(x_594, 8);
x_608 = lean_ctor_get(x_594, 9);
lean_inc(x_608);
lean_inc(x_607);
lean_inc(x_606);
lean_inc(x_605);
lean_inc(x_604);
lean_inc(x_603);
lean_inc(x_602);
lean_inc(x_601);
lean_inc(x_600);
lean_inc(x_599);
lean_dec(x_594);
lean_inc(x_595);
x_609 = l_Std_HashMapImp_insert___at_Lean_Closure_visitExpr___spec__3(x_603, x_576, x_595);
x_610 = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(x_610, 0, x_599);
lean_ctor_set(x_610, 1, x_600);
lean_ctor_set(x_610, 2, x_601);
lean_ctor_set(x_610, 3, x_602);
lean_ctor_set(x_610, 4, x_609);
lean_ctor_set(x_610, 5, x_604);
lean_ctor_set(x_610, 6, x_605);
lean_ctor_set(x_610, 7, x_606);
lean_ctor_set(x_610, 8, x_607);
lean_ctor_set(x_610, 9, x_608);
x_579 = x_595;
x_580 = x_610;
goto block_589;
}
}
else
{
uint8_t x_611; 
lean_dec(x_577);
lean_dec(x_576);
lean_dec(x_1);
x_611 = !lean_is_exclusive(x_593);
if (x_611 == 0)
{
return x_593;
}
else
{
lean_object* x_612; lean_object* x_613; lean_object* x_614; 
x_612 = lean_ctor_get(x_593, 0);
x_613 = lean_ctor_get(x_593, 1);
lean_inc(x_613);
lean_inc(x_612);
lean_dec(x_593);
x_614 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_614, 0, x_612);
lean_ctor_set(x_614, 1, x_613);
return x_614;
}
}
}
else
{
lean_object* x_615; 
lean_dec(x_576);
lean_dec(x_2);
x_615 = lean_ctor_get(x_592, 0);
lean_inc(x_615);
lean_dec(x_592);
x_579 = x_615;
x_580 = x_578;
goto block_589;
}
}
}
block_650:
{
lean_object* x_625; lean_object* x_626; 
lean_dec(x_624);
x_625 = lean_ctor_get(x_3, 4);
lean_inc(x_625);
x_626 = l_Std_HashMapImp_find_x3f___at_Lean_Closure_visitExpr___spec__1(x_625, x_575);
lean_dec(x_625);
if (lean_obj_tag(x_626) == 0)
{
lean_object* x_627; 
lean_inc(x_2);
lean_inc(x_575);
x_627 = l_Lean_Closure_collectExprAux___main(x_575, x_2, x_3);
if (lean_obj_tag(x_627) == 0)
{
lean_object* x_628; lean_object* x_629; uint8_t x_630; 
x_628 = lean_ctor_get(x_627, 1);
lean_inc(x_628);
x_629 = lean_ctor_get(x_627, 0);
lean_inc(x_629);
lean_dec(x_627);
x_630 = !lean_is_exclusive(x_628);
if (x_630 == 0)
{
lean_object* x_631; lean_object* x_632; 
x_631 = lean_ctor_get(x_628, 4);
lean_inc(x_629);
x_632 = l_Std_HashMapImp_insert___at_Lean_Closure_visitExpr___spec__3(x_631, x_575, x_629);
lean_ctor_set(x_628, 4, x_632);
x_577 = x_629;
x_578 = x_628;
goto block_623;
}
else
{
lean_object* x_633; lean_object* x_634; lean_object* x_635; lean_object* x_636; lean_object* x_637; lean_object* x_638; lean_object* x_639; lean_object* x_640; lean_object* x_641; lean_object* x_642; lean_object* x_643; lean_object* x_644; 
x_633 = lean_ctor_get(x_628, 0);
x_634 = lean_ctor_get(x_628, 1);
x_635 = lean_ctor_get(x_628, 2);
x_636 = lean_ctor_get(x_628, 3);
x_637 = lean_ctor_get(x_628, 4);
x_638 = lean_ctor_get(x_628, 5);
x_639 = lean_ctor_get(x_628, 6);
x_640 = lean_ctor_get(x_628, 7);
x_641 = lean_ctor_get(x_628, 8);
x_642 = lean_ctor_get(x_628, 9);
lean_inc(x_642);
lean_inc(x_641);
lean_inc(x_640);
lean_inc(x_639);
lean_inc(x_638);
lean_inc(x_637);
lean_inc(x_636);
lean_inc(x_635);
lean_inc(x_634);
lean_inc(x_633);
lean_dec(x_628);
lean_inc(x_629);
x_643 = l_Std_HashMapImp_insert___at_Lean_Closure_visitExpr___spec__3(x_637, x_575, x_629);
x_644 = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(x_644, 0, x_633);
lean_ctor_set(x_644, 1, x_634);
lean_ctor_set(x_644, 2, x_635);
lean_ctor_set(x_644, 3, x_636);
lean_ctor_set(x_644, 4, x_643);
lean_ctor_set(x_644, 5, x_638);
lean_ctor_set(x_644, 6, x_639);
lean_ctor_set(x_644, 7, x_640);
lean_ctor_set(x_644, 8, x_641);
lean_ctor_set(x_644, 9, x_642);
x_577 = x_629;
x_578 = x_644;
goto block_623;
}
}
else
{
uint8_t x_645; 
lean_dec(x_576);
lean_dec(x_575);
lean_dec(x_2);
lean_dec(x_1);
x_645 = !lean_is_exclusive(x_627);
if (x_645 == 0)
{
return x_627;
}
else
{
lean_object* x_646; lean_object* x_647; lean_object* x_648; 
x_646 = lean_ctor_get(x_627, 0);
x_647 = lean_ctor_get(x_627, 1);
lean_inc(x_647);
lean_inc(x_646);
lean_dec(x_627);
x_648 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_648, 0, x_646);
lean_ctor_set(x_648, 1, x_647);
return x_648;
}
}
}
else
{
lean_object* x_649; 
lean_dec(x_575);
x_649 = lean_ctor_get(x_626, 0);
lean_inc(x_649);
lean_dec(x_626);
x_577 = x_649;
x_578 = x_3;
goto block_623;
}
}
}
case 8:
{
lean_object* x_657; lean_object* x_658; lean_object* x_659; lean_object* x_660; lean_object* x_661; lean_object* x_741; uint8_t x_768; 
x_657 = lean_ctor_get(x_1, 1);
lean_inc(x_657);
x_658 = lean_ctor_get(x_1, 2);
lean_inc(x_658);
x_659 = lean_ctor_get(x_1, 3);
lean_inc(x_659);
x_768 = l_Lean_Expr_hasLevelParam(x_657);
if (x_768 == 0)
{
uint8_t x_769; 
x_769 = l_Lean_Expr_hasFVar(x_657);
if (x_769 == 0)
{
uint8_t x_770; 
x_770 = l_Lean_Expr_hasMVar(x_657);
if (x_770 == 0)
{
x_660 = x_657;
x_661 = x_3;
goto block_740;
}
else
{
lean_object* x_771; 
x_771 = lean_box(0);
x_741 = x_771;
goto block_767;
}
}
else
{
lean_object* x_772; 
x_772 = lean_box(0);
x_741 = x_772;
goto block_767;
}
}
else
{
lean_object* x_773; 
x_773 = lean_box(0);
x_741 = x_773;
goto block_767;
}
block_740:
{
lean_object* x_662; lean_object* x_663; lean_object* x_707; uint8_t x_734; 
x_734 = l_Lean_Expr_hasLevelParam(x_658);
if (x_734 == 0)
{
uint8_t x_735; 
x_735 = l_Lean_Expr_hasFVar(x_658);
if (x_735 == 0)
{
uint8_t x_736; 
x_736 = l_Lean_Expr_hasMVar(x_658);
if (x_736 == 0)
{
x_662 = x_658;
x_663 = x_661;
goto block_706;
}
else
{
lean_object* x_737; 
x_737 = lean_box(0);
x_707 = x_737;
goto block_733;
}
}
else
{
lean_object* x_738; 
x_738 = lean_box(0);
x_707 = x_738;
goto block_733;
}
}
else
{
lean_object* x_739; 
x_739 = lean_box(0);
x_707 = x_739;
goto block_733;
}
block_706:
{
lean_object* x_664; lean_object* x_665; lean_object* x_673; uint8_t x_700; 
x_700 = l_Lean_Expr_hasLevelParam(x_659);
if (x_700 == 0)
{
uint8_t x_701; 
x_701 = l_Lean_Expr_hasFVar(x_659);
if (x_701 == 0)
{
uint8_t x_702; 
x_702 = l_Lean_Expr_hasMVar(x_659);
if (x_702 == 0)
{
lean_dec(x_2);
x_664 = x_659;
x_665 = x_663;
goto block_672;
}
else
{
lean_object* x_703; 
x_703 = lean_box(0);
x_673 = x_703;
goto block_699;
}
}
else
{
lean_object* x_704; 
x_704 = lean_box(0);
x_673 = x_704;
goto block_699;
}
}
else
{
lean_object* x_705; 
x_705 = lean_box(0);
x_673 = x_705;
goto block_699;
}
block_672:
{
if (lean_obj_tag(x_1) == 8)
{
lean_object* x_666; lean_object* x_667; 
x_666 = lean_expr_update_let(x_1, x_660, x_662, x_664);
x_667 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_667, 0, x_666);
lean_ctor_set(x_667, 1, x_665);
return x_667;
}
else
{
lean_object* x_668; lean_object* x_669; lean_object* x_670; lean_object* x_671; 
lean_dec(x_664);
lean_dec(x_662);
lean_dec(x_660);
lean_dec(x_1);
x_668 = l_Lean_Expr_Inhabited;
x_669 = l_Lean_Expr_updateLet_x21___closed__1;
x_670 = lean_panic_fn(x_668, x_669);
x_671 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_671, 0, x_670);
lean_ctor_set(x_671, 1, x_665);
return x_671;
}
}
block_699:
{
lean_object* x_674; lean_object* x_675; 
lean_dec(x_673);
x_674 = lean_ctor_get(x_663, 4);
lean_inc(x_674);
x_675 = l_Std_HashMapImp_find_x3f___at_Lean_Closure_visitExpr___spec__1(x_674, x_659);
lean_dec(x_674);
if (lean_obj_tag(x_675) == 0)
{
lean_object* x_676; 
lean_inc(x_659);
x_676 = l_Lean_Closure_collectExprAux___main(x_659, x_2, x_663);
if (lean_obj_tag(x_676) == 0)
{
lean_object* x_677; lean_object* x_678; uint8_t x_679; 
x_677 = lean_ctor_get(x_676, 1);
lean_inc(x_677);
x_678 = lean_ctor_get(x_676, 0);
lean_inc(x_678);
lean_dec(x_676);
x_679 = !lean_is_exclusive(x_677);
if (x_679 == 0)
{
lean_object* x_680; lean_object* x_681; 
x_680 = lean_ctor_get(x_677, 4);
lean_inc(x_678);
x_681 = l_Std_HashMapImp_insert___at_Lean_Closure_visitExpr___spec__3(x_680, x_659, x_678);
lean_ctor_set(x_677, 4, x_681);
x_664 = x_678;
x_665 = x_677;
goto block_672;
}
else
{
lean_object* x_682; lean_object* x_683; lean_object* x_684; lean_object* x_685; lean_object* x_686; lean_object* x_687; lean_object* x_688; lean_object* x_689; lean_object* x_690; lean_object* x_691; lean_object* x_692; lean_object* x_693; 
x_682 = lean_ctor_get(x_677, 0);
x_683 = lean_ctor_get(x_677, 1);
x_684 = lean_ctor_get(x_677, 2);
x_685 = lean_ctor_get(x_677, 3);
x_686 = lean_ctor_get(x_677, 4);
x_687 = lean_ctor_get(x_677, 5);
x_688 = lean_ctor_get(x_677, 6);
x_689 = lean_ctor_get(x_677, 7);
x_690 = lean_ctor_get(x_677, 8);
x_691 = lean_ctor_get(x_677, 9);
lean_inc(x_691);
lean_inc(x_690);
lean_inc(x_689);
lean_inc(x_688);
lean_inc(x_687);
lean_inc(x_686);
lean_inc(x_685);
lean_inc(x_684);
lean_inc(x_683);
lean_inc(x_682);
lean_dec(x_677);
lean_inc(x_678);
x_692 = l_Std_HashMapImp_insert___at_Lean_Closure_visitExpr___spec__3(x_686, x_659, x_678);
x_693 = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(x_693, 0, x_682);
lean_ctor_set(x_693, 1, x_683);
lean_ctor_set(x_693, 2, x_684);
lean_ctor_set(x_693, 3, x_685);
lean_ctor_set(x_693, 4, x_692);
lean_ctor_set(x_693, 5, x_687);
lean_ctor_set(x_693, 6, x_688);
lean_ctor_set(x_693, 7, x_689);
lean_ctor_set(x_693, 8, x_690);
lean_ctor_set(x_693, 9, x_691);
x_664 = x_678;
x_665 = x_693;
goto block_672;
}
}
else
{
uint8_t x_694; 
lean_dec(x_662);
lean_dec(x_660);
lean_dec(x_659);
lean_dec(x_1);
x_694 = !lean_is_exclusive(x_676);
if (x_694 == 0)
{
return x_676;
}
else
{
lean_object* x_695; lean_object* x_696; lean_object* x_697; 
x_695 = lean_ctor_get(x_676, 0);
x_696 = lean_ctor_get(x_676, 1);
lean_inc(x_696);
lean_inc(x_695);
lean_dec(x_676);
x_697 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_697, 0, x_695);
lean_ctor_set(x_697, 1, x_696);
return x_697;
}
}
}
else
{
lean_object* x_698; 
lean_dec(x_659);
lean_dec(x_2);
x_698 = lean_ctor_get(x_675, 0);
lean_inc(x_698);
lean_dec(x_675);
x_664 = x_698;
x_665 = x_663;
goto block_672;
}
}
}
block_733:
{
lean_object* x_708; lean_object* x_709; 
lean_dec(x_707);
x_708 = lean_ctor_get(x_661, 4);
lean_inc(x_708);
x_709 = l_Std_HashMapImp_find_x3f___at_Lean_Closure_visitExpr___spec__1(x_708, x_658);
lean_dec(x_708);
if (lean_obj_tag(x_709) == 0)
{
lean_object* x_710; 
lean_inc(x_2);
lean_inc(x_658);
x_710 = l_Lean_Closure_collectExprAux___main(x_658, x_2, x_661);
if (lean_obj_tag(x_710) == 0)
{
lean_object* x_711; lean_object* x_712; uint8_t x_713; 
x_711 = lean_ctor_get(x_710, 1);
lean_inc(x_711);
x_712 = lean_ctor_get(x_710, 0);
lean_inc(x_712);
lean_dec(x_710);
x_713 = !lean_is_exclusive(x_711);
if (x_713 == 0)
{
lean_object* x_714; lean_object* x_715; 
x_714 = lean_ctor_get(x_711, 4);
lean_inc(x_712);
x_715 = l_Std_HashMapImp_insert___at_Lean_Closure_visitExpr___spec__3(x_714, x_658, x_712);
lean_ctor_set(x_711, 4, x_715);
x_662 = x_712;
x_663 = x_711;
goto block_706;
}
else
{
lean_object* x_716; lean_object* x_717; lean_object* x_718; lean_object* x_719; lean_object* x_720; lean_object* x_721; lean_object* x_722; lean_object* x_723; lean_object* x_724; lean_object* x_725; lean_object* x_726; lean_object* x_727; 
x_716 = lean_ctor_get(x_711, 0);
x_717 = lean_ctor_get(x_711, 1);
x_718 = lean_ctor_get(x_711, 2);
x_719 = lean_ctor_get(x_711, 3);
x_720 = lean_ctor_get(x_711, 4);
x_721 = lean_ctor_get(x_711, 5);
x_722 = lean_ctor_get(x_711, 6);
x_723 = lean_ctor_get(x_711, 7);
x_724 = lean_ctor_get(x_711, 8);
x_725 = lean_ctor_get(x_711, 9);
lean_inc(x_725);
lean_inc(x_724);
lean_inc(x_723);
lean_inc(x_722);
lean_inc(x_721);
lean_inc(x_720);
lean_inc(x_719);
lean_inc(x_718);
lean_inc(x_717);
lean_inc(x_716);
lean_dec(x_711);
lean_inc(x_712);
x_726 = l_Std_HashMapImp_insert___at_Lean_Closure_visitExpr___spec__3(x_720, x_658, x_712);
x_727 = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(x_727, 0, x_716);
lean_ctor_set(x_727, 1, x_717);
lean_ctor_set(x_727, 2, x_718);
lean_ctor_set(x_727, 3, x_719);
lean_ctor_set(x_727, 4, x_726);
lean_ctor_set(x_727, 5, x_721);
lean_ctor_set(x_727, 6, x_722);
lean_ctor_set(x_727, 7, x_723);
lean_ctor_set(x_727, 8, x_724);
lean_ctor_set(x_727, 9, x_725);
x_662 = x_712;
x_663 = x_727;
goto block_706;
}
}
else
{
uint8_t x_728; 
lean_dec(x_660);
lean_dec(x_659);
lean_dec(x_658);
lean_dec(x_2);
lean_dec(x_1);
x_728 = !lean_is_exclusive(x_710);
if (x_728 == 0)
{
return x_710;
}
else
{
lean_object* x_729; lean_object* x_730; lean_object* x_731; 
x_729 = lean_ctor_get(x_710, 0);
x_730 = lean_ctor_get(x_710, 1);
lean_inc(x_730);
lean_inc(x_729);
lean_dec(x_710);
x_731 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_731, 0, x_729);
lean_ctor_set(x_731, 1, x_730);
return x_731;
}
}
}
else
{
lean_object* x_732; 
lean_dec(x_658);
x_732 = lean_ctor_get(x_709, 0);
lean_inc(x_732);
lean_dec(x_709);
x_662 = x_732;
x_663 = x_661;
goto block_706;
}
}
}
block_767:
{
lean_object* x_742; lean_object* x_743; 
lean_dec(x_741);
x_742 = lean_ctor_get(x_3, 4);
lean_inc(x_742);
x_743 = l_Std_HashMapImp_find_x3f___at_Lean_Closure_visitExpr___spec__1(x_742, x_657);
lean_dec(x_742);
if (lean_obj_tag(x_743) == 0)
{
lean_object* x_744; 
lean_inc(x_2);
lean_inc(x_657);
x_744 = l_Lean_Closure_collectExprAux___main(x_657, x_2, x_3);
if (lean_obj_tag(x_744) == 0)
{
lean_object* x_745; lean_object* x_746; uint8_t x_747; 
x_745 = lean_ctor_get(x_744, 1);
lean_inc(x_745);
x_746 = lean_ctor_get(x_744, 0);
lean_inc(x_746);
lean_dec(x_744);
x_747 = !lean_is_exclusive(x_745);
if (x_747 == 0)
{
lean_object* x_748; lean_object* x_749; 
x_748 = lean_ctor_get(x_745, 4);
lean_inc(x_746);
x_749 = l_Std_HashMapImp_insert___at_Lean_Closure_visitExpr___spec__3(x_748, x_657, x_746);
lean_ctor_set(x_745, 4, x_749);
x_660 = x_746;
x_661 = x_745;
goto block_740;
}
else
{
lean_object* x_750; lean_object* x_751; lean_object* x_752; lean_object* x_753; lean_object* x_754; lean_object* x_755; lean_object* x_756; lean_object* x_757; lean_object* x_758; lean_object* x_759; lean_object* x_760; lean_object* x_761; 
x_750 = lean_ctor_get(x_745, 0);
x_751 = lean_ctor_get(x_745, 1);
x_752 = lean_ctor_get(x_745, 2);
x_753 = lean_ctor_get(x_745, 3);
x_754 = lean_ctor_get(x_745, 4);
x_755 = lean_ctor_get(x_745, 5);
x_756 = lean_ctor_get(x_745, 6);
x_757 = lean_ctor_get(x_745, 7);
x_758 = lean_ctor_get(x_745, 8);
x_759 = lean_ctor_get(x_745, 9);
lean_inc(x_759);
lean_inc(x_758);
lean_inc(x_757);
lean_inc(x_756);
lean_inc(x_755);
lean_inc(x_754);
lean_inc(x_753);
lean_inc(x_752);
lean_inc(x_751);
lean_inc(x_750);
lean_dec(x_745);
lean_inc(x_746);
x_760 = l_Std_HashMapImp_insert___at_Lean_Closure_visitExpr___spec__3(x_754, x_657, x_746);
x_761 = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(x_761, 0, x_750);
lean_ctor_set(x_761, 1, x_751);
lean_ctor_set(x_761, 2, x_752);
lean_ctor_set(x_761, 3, x_753);
lean_ctor_set(x_761, 4, x_760);
lean_ctor_set(x_761, 5, x_755);
lean_ctor_set(x_761, 6, x_756);
lean_ctor_set(x_761, 7, x_757);
lean_ctor_set(x_761, 8, x_758);
lean_ctor_set(x_761, 9, x_759);
x_660 = x_746;
x_661 = x_761;
goto block_740;
}
}
else
{
uint8_t x_762; 
lean_dec(x_659);
lean_dec(x_658);
lean_dec(x_657);
lean_dec(x_2);
lean_dec(x_1);
x_762 = !lean_is_exclusive(x_744);
if (x_762 == 0)
{
return x_744;
}
else
{
lean_object* x_763; lean_object* x_764; lean_object* x_765; 
x_763 = lean_ctor_get(x_744, 0);
x_764 = lean_ctor_get(x_744, 1);
lean_inc(x_764);
lean_inc(x_763);
lean_dec(x_744);
x_765 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_765, 0, x_763);
lean_ctor_set(x_765, 1, x_764);
return x_765;
}
}
}
else
{
lean_object* x_766; 
lean_dec(x_657);
x_766 = lean_ctor_get(x_743, 0);
lean_inc(x_766);
lean_dec(x_743);
x_660 = x_766;
x_661 = x_3;
goto block_740;
}
}
}
case 10:
{
lean_object* x_774; lean_object* x_775; uint8_t x_802; 
x_774 = lean_ctor_get(x_1, 1);
lean_inc(x_774);
x_802 = l_Lean_Expr_hasLevelParam(x_774);
if (x_802 == 0)
{
uint8_t x_803; 
x_803 = l_Lean_Expr_hasFVar(x_774);
if (x_803 == 0)
{
uint8_t x_804; 
x_804 = l_Lean_Expr_hasMVar(x_774);
if (x_804 == 0)
{
lean_dec(x_2);
x_4 = x_774;
x_5 = x_3;
goto block_12;
}
else
{
lean_object* x_805; 
x_805 = lean_box(0);
x_775 = x_805;
goto block_801;
}
}
else
{
lean_object* x_806; 
x_806 = lean_box(0);
x_775 = x_806;
goto block_801;
}
}
else
{
lean_object* x_807; 
x_807 = lean_box(0);
x_775 = x_807;
goto block_801;
}
block_801:
{
lean_object* x_776; lean_object* x_777; 
lean_dec(x_775);
x_776 = lean_ctor_get(x_3, 4);
lean_inc(x_776);
x_777 = l_Std_HashMapImp_find_x3f___at_Lean_Closure_visitExpr___spec__1(x_776, x_774);
lean_dec(x_776);
if (lean_obj_tag(x_777) == 0)
{
lean_object* x_778; 
lean_inc(x_774);
x_778 = l_Lean_Closure_collectExprAux___main(x_774, x_2, x_3);
if (lean_obj_tag(x_778) == 0)
{
lean_object* x_779; lean_object* x_780; uint8_t x_781; 
x_779 = lean_ctor_get(x_778, 1);
lean_inc(x_779);
x_780 = lean_ctor_get(x_778, 0);
lean_inc(x_780);
lean_dec(x_778);
x_781 = !lean_is_exclusive(x_779);
if (x_781 == 0)
{
lean_object* x_782; lean_object* x_783; 
x_782 = lean_ctor_get(x_779, 4);
lean_inc(x_780);
x_783 = l_Std_HashMapImp_insert___at_Lean_Closure_visitExpr___spec__3(x_782, x_774, x_780);
lean_ctor_set(x_779, 4, x_783);
x_4 = x_780;
x_5 = x_779;
goto block_12;
}
else
{
lean_object* x_784; lean_object* x_785; lean_object* x_786; lean_object* x_787; lean_object* x_788; lean_object* x_789; lean_object* x_790; lean_object* x_791; lean_object* x_792; lean_object* x_793; lean_object* x_794; lean_object* x_795; 
x_784 = lean_ctor_get(x_779, 0);
x_785 = lean_ctor_get(x_779, 1);
x_786 = lean_ctor_get(x_779, 2);
x_787 = lean_ctor_get(x_779, 3);
x_788 = lean_ctor_get(x_779, 4);
x_789 = lean_ctor_get(x_779, 5);
x_790 = lean_ctor_get(x_779, 6);
x_791 = lean_ctor_get(x_779, 7);
x_792 = lean_ctor_get(x_779, 8);
x_793 = lean_ctor_get(x_779, 9);
lean_inc(x_793);
lean_inc(x_792);
lean_inc(x_791);
lean_inc(x_790);
lean_inc(x_789);
lean_inc(x_788);
lean_inc(x_787);
lean_inc(x_786);
lean_inc(x_785);
lean_inc(x_784);
lean_dec(x_779);
lean_inc(x_780);
x_794 = l_Std_HashMapImp_insert___at_Lean_Closure_visitExpr___spec__3(x_788, x_774, x_780);
x_795 = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(x_795, 0, x_784);
lean_ctor_set(x_795, 1, x_785);
lean_ctor_set(x_795, 2, x_786);
lean_ctor_set(x_795, 3, x_787);
lean_ctor_set(x_795, 4, x_794);
lean_ctor_set(x_795, 5, x_789);
lean_ctor_set(x_795, 6, x_790);
lean_ctor_set(x_795, 7, x_791);
lean_ctor_set(x_795, 8, x_792);
lean_ctor_set(x_795, 9, x_793);
x_4 = x_780;
x_5 = x_795;
goto block_12;
}
}
else
{
uint8_t x_796; 
lean_dec(x_774);
lean_dec(x_1);
x_796 = !lean_is_exclusive(x_778);
if (x_796 == 0)
{
return x_778;
}
else
{
lean_object* x_797; lean_object* x_798; lean_object* x_799; 
x_797 = lean_ctor_get(x_778, 0);
x_798 = lean_ctor_get(x_778, 1);
lean_inc(x_798);
lean_inc(x_797);
lean_dec(x_778);
x_799 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_799, 0, x_797);
lean_ctor_set(x_799, 1, x_798);
return x_799;
}
}
}
else
{
lean_object* x_800; 
lean_dec(x_774);
lean_dec(x_2);
x_800 = lean_ctor_get(x_777, 0);
lean_inc(x_800);
lean_dec(x_777);
x_4 = x_800;
x_5 = x_3;
goto block_12;
}
}
}
case 11:
{
lean_object* x_808; lean_object* x_809; uint8_t x_836; 
x_808 = lean_ctor_get(x_1, 2);
lean_inc(x_808);
x_836 = l_Lean_Expr_hasLevelParam(x_808);
if (x_836 == 0)
{
uint8_t x_837; 
x_837 = l_Lean_Expr_hasFVar(x_808);
if (x_837 == 0)
{
uint8_t x_838; 
x_838 = l_Lean_Expr_hasMVar(x_808);
if (x_838 == 0)
{
lean_dec(x_2);
x_13 = x_808;
x_14 = x_3;
goto block_21;
}
else
{
lean_object* x_839; 
x_839 = lean_box(0);
x_809 = x_839;
goto block_835;
}
}
else
{
lean_object* x_840; 
x_840 = lean_box(0);
x_809 = x_840;
goto block_835;
}
}
else
{
lean_object* x_841; 
x_841 = lean_box(0);
x_809 = x_841;
goto block_835;
}
block_835:
{
lean_object* x_810; lean_object* x_811; 
lean_dec(x_809);
x_810 = lean_ctor_get(x_3, 4);
lean_inc(x_810);
x_811 = l_Std_HashMapImp_find_x3f___at_Lean_Closure_visitExpr___spec__1(x_810, x_808);
lean_dec(x_810);
if (lean_obj_tag(x_811) == 0)
{
lean_object* x_812; 
lean_inc(x_808);
x_812 = l_Lean_Closure_collectExprAux___main(x_808, x_2, x_3);
if (lean_obj_tag(x_812) == 0)
{
lean_object* x_813; lean_object* x_814; uint8_t x_815; 
x_813 = lean_ctor_get(x_812, 1);
lean_inc(x_813);
x_814 = lean_ctor_get(x_812, 0);
lean_inc(x_814);
lean_dec(x_812);
x_815 = !lean_is_exclusive(x_813);
if (x_815 == 0)
{
lean_object* x_816; lean_object* x_817; 
x_816 = lean_ctor_get(x_813, 4);
lean_inc(x_814);
x_817 = l_Std_HashMapImp_insert___at_Lean_Closure_visitExpr___spec__3(x_816, x_808, x_814);
lean_ctor_set(x_813, 4, x_817);
x_13 = x_814;
x_14 = x_813;
goto block_21;
}
else
{
lean_object* x_818; lean_object* x_819; lean_object* x_820; lean_object* x_821; lean_object* x_822; lean_object* x_823; lean_object* x_824; lean_object* x_825; lean_object* x_826; lean_object* x_827; lean_object* x_828; lean_object* x_829; 
x_818 = lean_ctor_get(x_813, 0);
x_819 = lean_ctor_get(x_813, 1);
x_820 = lean_ctor_get(x_813, 2);
x_821 = lean_ctor_get(x_813, 3);
x_822 = lean_ctor_get(x_813, 4);
x_823 = lean_ctor_get(x_813, 5);
x_824 = lean_ctor_get(x_813, 6);
x_825 = lean_ctor_get(x_813, 7);
x_826 = lean_ctor_get(x_813, 8);
x_827 = lean_ctor_get(x_813, 9);
lean_inc(x_827);
lean_inc(x_826);
lean_inc(x_825);
lean_inc(x_824);
lean_inc(x_823);
lean_inc(x_822);
lean_inc(x_821);
lean_inc(x_820);
lean_inc(x_819);
lean_inc(x_818);
lean_dec(x_813);
lean_inc(x_814);
x_828 = l_Std_HashMapImp_insert___at_Lean_Closure_visitExpr___spec__3(x_822, x_808, x_814);
x_829 = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(x_829, 0, x_818);
lean_ctor_set(x_829, 1, x_819);
lean_ctor_set(x_829, 2, x_820);
lean_ctor_set(x_829, 3, x_821);
lean_ctor_set(x_829, 4, x_828);
lean_ctor_set(x_829, 5, x_823);
lean_ctor_set(x_829, 6, x_824);
lean_ctor_set(x_829, 7, x_825);
lean_ctor_set(x_829, 8, x_826);
lean_ctor_set(x_829, 9, x_827);
x_13 = x_814;
x_14 = x_829;
goto block_21;
}
}
else
{
uint8_t x_830; 
lean_dec(x_808);
lean_dec(x_1);
x_830 = !lean_is_exclusive(x_812);
if (x_830 == 0)
{
return x_812;
}
else
{
lean_object* x_831; lean_object* x_832; lean_object* x_833; 
x_831 = lean_ctor_get(x_812, 0);
x_832 = lean_ctor_get(x_812, 1);
lean_inc(x_832);
lean_inc(x_831);
lean_dec(x_812);
x_833 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_833, 0, x_831);
lean_ctor_set(x_833, 1, x_832);
return x_833;
}
}
}
else
{
lean_object* x_834; 
lean_dec(x_808);
lean_dec(x_2);
x_834 = lean_ctor_get(x_811, 0);
lean_inc(x_834);
lean_dec(x_811);
x_13 = x_834;
x_14 = x_3;
goto block_21;
}
}
}
default: 
{
lean_object* x_842; 
lean_dec(x_2);
x_842 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_842, 0, x_1);
lean_ctor_set(x_842, 1, x_3);
return x_842;
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_54; 
x_4 = l_Lean_Closure_instantiateMVars(x_1, x_2, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 x_7 = x_4;
} else {
 lean_dec_ref(x_4);
 x_7 = lean_box(0);
}
x_54 = l_Lean_Expr_hasLevelParam(x_5);
if (x_54 == 0)
{
uint8_t x_55; 
x_55 = l_Lean_Expr_hasFVar(x_5);
if (x_55 == 0)
{
uint8_t x_56; 
x_56 = l_Lean_Expr_hasMVar(x_5);
if (x_56 == 0)
{
lean_object* x_57; 
lean_dec(x_7);
lean_dec(x_2);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_5);
lean_ctor_set(x_57, 1, x_6);
return x_57;
}
else
{
lean_object* x_58; 
x_58 = lean_box(0);
x_8 = x_58;
goto block_53;
}
}
else
{
lean_object* x_59; 
x_59 = lean_box(0);
x_8 = x_59;
goto block_53;
}
}
else
{
lean_object* x_60; 
x_60 = lean_box(0);
x_8 = x_60;
goto block_53;
}
block_53:
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_8);
x_9 = lean_ctor_get(x_6, 4);
lean_inc(x_9);
x_10 = l_Std_HashMapImp_find_x3f___at_Lean_Closure_visitExpr___spec__1(x_9, x_5);
lean_dec(x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
lean_dec(x_7);
lean_inc(x_5);
x_11 = l_Lean_Closure_collectExprAux___main(x_5, x_2, x_6);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_11, 1);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_11, 0);
x_16 = lean_ctor_get(x_13, 4);
lean_inc(x_15);
x_17 = l_Std_HashMapImp_insert___at_Lean_Closure_visitExpr___spec__3(x_16, x_5, x_15);
lean_ctor_set(x_13, 4, x_17);
return x_11;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_18 = lean_ctor_get(x_11, 0);
x_19 = lean_ctor_get(x_13, 0);
x_20 = lean_ctor_get(x_13, 1);
x_21 = lean_ctor_get(x_13, 2);
x_22 = lean_ctor_get(x_13, 3);
x_23 = lean_ctor_get(x_13, 4);
x_24 = lean_ctor_get(x_13, 5);
x_25 = lean_ctor_get(x_13, 6);
x_26 = lean_ctor_get(x_13, 7);
x_27 = lean_ctor_get(x_13, 8);
x_28 = lean_ctor_get(x_13, 9);
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
lean_dec(x_13);
lean_inc(x_18);
x_29 = l_Std_HashMapImp_insert___at_Lean_Closure_visitExpr___spec__3(x_23, x_5, x_18);
x_30 = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(x_30, 0, x_19);
lean_ctor_set(x_30, 1, x_20);
lean_ctor_set(x_30, 2, x_21);
lean_ctor_set(x_30, 3, x_22);
lean_ctor_set(x_30, 4, x_29);
lean_ctor_set(x_30, 5, x_24);
lean_ctor_set(x_30, 6, x_25);
lean_ctor_set(x_30, 7, x_26);
lean_ctor_set(x_30, 8, x_27);
lean_ctor_set(x_30, 9, x_28);
lean_ctor_set(x_11, 1, x_30);
return x_11;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_31 = lean_ctor_get(x_11, 1);
x_32 = lean_ctor_get(x_11, 0);
lean_inc(x_31);
lean_inc(x_32);
lean_dec(x_11);
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
x_42 = lean_ctor_get(x_31, 9);
lean_inc(x_42);
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
 lean_ctor_release(x_31, 9);
 x_43 = x_31;
} else {
 lean_dec_ref(x_31);
 x_43 = lean_box(0);
}
lean_inc(x_32);
x_44 = l_Std_HashMapImp_insert___at_Lean_Closure_visitExpr___spec__3(x_37, x_5, x_32);
if (lean_is_scalar(x_43)) {
 x_45 = lean_alloc_ctor(0, 10, 0);
} else {
 x_45 = x_43;
}
lean_ctor_set(x_45, 0, x_33);
lean_ctor_set(x_45, 1, x_34);
lean_ctor_set(x_45, 2, x_35);
lean_ctor_set(x_45, 3, x_36);
lean_ctor_set(x_45, 4, x_44);
lean_ctor_set(x_45, 5, x_38);
lean_ctor_set(x_45, 6, x_39);
lean_ctor_set(x_45, 7, x_40);
lean_ctor_set(x_45, 8, x_41);
lean_ctor_set(x_45, 9, x_42);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_32);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
else
{
uint8_t x_47; 
lean_dec(x_5);
x_47 = !lean_is_exclusive(x_11);
if (x_47 == 0)
{
return x_11;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_11, 0);
x_49 = lean_ctor_get(x_11, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_11);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
else
{
lean_object* x_51; lean_object* x_52; 
lean_dec(x_5);
lean_dec(x_2);
x_51 = lean_ctor_get(x_10, 0);
lean_inc(x_51);
lean_dec(x_10);
if (lean_is_scalar(x_7)) {
 x_52 = lean_alloc_ctor(0, 2, 0);
} else {
 x_52 = x_7;
}
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_6);
return x_52;
}
}
}
}
lean_object* _init_l_Lean_Closure_ExprToClose_inhabited___closed__1() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l_Lean_Expr_Inhabited___closed__1;
x_2 = 0;
x_3 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Closure_ExprToClose_inhabited() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Closure_ExprToClose_inhabited___closed__1;
return x_1;
}
}
lean_object* l_Std_ShareCommonT_withShareCommon___at_Lean_Closure_mkClosure___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_state_sharecommon(x_2, x_1);
return x_3;
}
}
lean_object* l_Array_umapMAux___main___at_Lean_Closure_mkClosure___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_1, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_1);
x_6 = x_2;
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_8 = lean_array_fget(x_2, x_1);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_array_fset(x_2, x_1, x_9);
x_11 = x_8;
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_state_sharecommon(x_3, x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
lean_ctor_set(x_11, 0, x_15);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_add(x_1, x_17);
x_19 = x_11;
x_20 = lean_array_fset(x_10, x_1, x_19);
lean_dec(x_1);
x_1 = x_18;
x_2 = x_20;
x_3 = x_16;
goto _start;
}
else
{
lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_22 = lean_ctor_get(x_11, 0);
x_23 = lean_ctor_get_uint8(x_11, sizeof(void*)*1);
lean_inc(x_22);
lean_dec(x_11);
x_24 = lean_state_sharecommon(x_3, x_22);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set_uint8(x_27, sizeof(void*)*1, x_23);
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_nat_add(x_1, x_28);
x_30 = x_27;
x_31 = lean_array_fset(x_10, x_1, x_30);
lean_dec(x_1);
x_1 = x_29;
x_2 = x_31;
x_3 = x_26;
goto _start;
}
}
}
}
lean_object* l_Array_umapMAux___main___at_Lean_Closure_mkClosure___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_2);
x_6 = lean_nat_dec_lt(x_1, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
lean_dec(x_1);
x_7 = x_2;
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_4);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_array_fget(x_2, x_1);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_array_fset(x_2, x_1, x_10);
x_12 = x_9;
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec(x_12);
lean_inc(x_3);
x_14 = l_Lean_Closure_collectExpr(x_13, x_3, x_4);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_add(x_1, x_17);
x_19 = x_15;
x_20 = lean_array_fset(x_11, x_1, x_19);
lean_dec(x_1);
x_1 = x_18;
x_2 = x_20;
x_4 = x_16;
goto _start;
}
else
{
uint8_t x_22; 
lean_dec(x_11);
lean_dec(x_3);
lean_dec(x_1);
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
}
lean_object* l_Array_umapMAux___main___at_Lean_Closure_mkClosure___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_5);
x_7 = lean_nat_dec_lt(x_4, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_4);
lean_dec(x_2);
x_8 = x_5;
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; 
x_9 = lean_array_fget(x_5, x_4);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_array_fset(x_5, x_4, x_10);
x_12 = x_9;
x_13 = l_Lean_Closure_ExprToClose_inhabited;
x_14 = lean_array_get(x_13, x_1, x_4);
x_15 = lean_ctor_get_uint8(x_14, sizeof(void*)*1);
lean_dec(x_14);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_add(x_4, x_16);
if (x_15 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_inc(x_2);
x_18 = l_Lean_LocalContext_mkLambda(x_2, x_3, x_12);
lean_dec(x_12);
x_19 = x_18;
x_20 = lean_array_fset(x_11, x_4, x_19);
lean_dec(x_4);
x_4 = x_17;
x_5 = x_20;
goto _start;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_inc(x_2);
x_22 = l_Lean_LocalContext_mkForall(x_2, x_3, x_12);
lean_dec(x_12);
x_23 = x_22;
x_24 = lean_array_fset(x_11, x_4, x_23);
lean_dec(x_4);
x_4 = x_17;
x_5 = x_24;
goto _start;
}
}
}
}
lean_object* l_Std_mkHashMap___at_Lean_Closure_mkClosure___spec__5(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_mkHashMapImp___rarg(x_1);
return x_2;
}
}
lean_object* l_Std_mkHashMap___at_Lean_Closure_mkClosure___spec__6(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_mkHashMapImp___rarg(x_1);
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
x_2 = l_Std_mkHashMapImp___rarg(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Closure_mkClosure___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = l_Std_mkHashMapImp___rarg(x_1);
return x_2;
}
}
lean_object* l_Lean_Closure_mkClosure(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_5 = x_3;
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Closure_mkClosure___spec__2), 3, 2);
lean_closure_set(x_7, 0, x_6);
lean_closure_set(x_7, 1, x_5);
x_8 = l_Std_ShareCommon_State_empty;
x_9 = x_7;
x_10 = lean_apply_1(x_9, x_8);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
lean_inc(x_11);
x_12 = x_11;
x_13 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Closure_mkClosure___spec__3), 4, 2);
lean_closure_set(x_13, 0, x_6);
lean_closure_set(x_13, 1, x_12);
x_32 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_32, 0, x_2);
lean_ctor_set_uint8(x_32, sizeof(void*)*1, x_4);
x_33 = l_Lean_LocalContext_Inhabited___closed__2;
x_34 = l_Lean_Closure_mkClosure___closed__3;
x_35 = l_Lean_Closure_mkClosure___closed__4;
x_36 = l_Lean_Closure_mkClosure___closed__5;
x_37 = l_Array_empty___closed__1;
x_38 = lean_unsigned_to_nat(1u);
x_39 = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(x_39, 0, x_1);
lean_ctor_set(x_39, 1, x_33);
lean_ctor_set(x_39, 2, x_34);
lean_ctor_set(x_39, 3, x_35);
lean_ctor_set(x_39, 4, x_36);
lean_ctor_set(x_39, 5, x_37);
lean_ctor_set(x_39, 6, x_38);
lean_ctor_set(x_39, 7, x_37);
lean_ctor_set(x_39, 8, x_38);
lean_ctor_set(x_39, 9, x_37);
x_40 = x_13;
x_41 = lean_apply_2(x_40, x_32, x_39);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = l_Lean_Closure_getMCtx___rarg(x_43);
x_45 = !lean_is_exclusive(x_44);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_44, 0);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_42);
lean_ctor_set(x_47, 1, x_46);
lean_ctor_set(x_44, 0, x_47);
x_14 = x_44;
goto block_31;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_48 = lean_ctor_get(x_44, 0);
x_49 = lean_ctor_get(x_44, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_44);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_42);
lean_ctor_set(x_50, 1, x_48);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_49);
x_14 = x_51;
goto block_31;
}
}
else
{
uint8_t x_52; 
x_52 = !lean_is_exclusive(x_41);
if (x_52 == 0)
{
x_14 = x_41;
goto block_31;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_41, 0);
x_54 = lean_ctor_get(x_41, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_41);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
x_14 = x_55;
goto block_31;
}
}
block_31:
{
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
x_20 = l_Lean_LocalContext_getFVars(x_19);
x_21 = x_17;
x_22 = l_Array_umapMAux___main___at_Lean_Closure_mkClosure___spec__4(x_11, x_19, x_20, x_6, x_21);
lean_dec(x_20);
lean_dec(x_11);
x_23 = x_22;
x_24 = lean_ctor_get(x_16, 5);
lean_inc(x_24);
x_25 = lean_ctor_get(x_16, 7);
lean_inc(x_25);
x_26 = lean_ctor_get(x_16, 9);
lean_inc(x_26);
lean_dec(x_16);
x_27 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_27, 0, x_24);
lean_ctor_set(x_27, 1, x_23);
lean_ctor_set(x_27, 2, x_25);
lean_ctor_set(x_27, 3, x_26);
lean_ctor_set(x_27, 4, x_18);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_27);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; 
lean_dec(x_11);
x_29 = lean_ctor_get(x_14, 0);
lean_inc(x_29);
lean_dec(x_14);
x_30 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_30, 0, x_29);
return x_30;
}
}
}
}
lean_object* l_Array_umapMAux___main___at_Lean_Closure_mkClosure___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_umapMAux___main___at_Lean_Closure_mkClosure___spec__4(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Lean_Closure_mkClosure___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_4);
lean_dec(x_4);
x_6 = l_Lean_Closure_mkClosure(x_1, x_2, x_3, x_5);
return x_6;
}
}
lean_object* l_Lean_Closure_mkValueTypeClosure(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_6 = 1;
x_7 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_7, 0, x_3);
lean_ctor_set_uint8(x_7, sizeof(void*)*1, x_6);
x_8 = 0;
x_9 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_9, 0, x_4);
lean_ctor_set_uint8(x_9, sizeof(void*)*1, x_8);
x_10 = l_Lean_mkAppStx___closed__9;
x_11 = lean_array_push(x_10, x_7);
x_12 = lean_array_push(x_11, x_9);
x_13 = l_Lean_Closure_mkClosure(x_1, x_2, x_12, x_5);
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
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_13);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_18 = lean_ctor_get(x_13, 0);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
x_21 = lean_ctor_get(x_18, 2);
lean_inc(x_21);
x_22 = lean_ctor_get(x_18, 3);
lean_inc(x_22);
x_23 = lean_ctor_get(x_18, 4);
lean_inc(x_23);
lean_dec(x_18);
x_24 = l_Lean_Expr_Inhabited;
x_25 = lean_unsigned_to_nat(0u);
x_26 = lean_array_get(x_24, x_20, x_25);
x_27 = lean_unsigned_to_nat(1u);
x_28 = lean_array_get(x_24, x_20, x_27);
lean_dec(x_20);
x_29 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_29, 0, x_19);
lean_ctor_set(x_29, 1, x_26);
lean_ctor_set(x_29, 2, x_28);
lean_ctor_set(x_29, 3, x_21);
lean_ctor_set(x_29, 4, x_22);
lean_ctor_set(x_29, 5, x_23);
lean_ctor_set(x_13, 0, x_29);
return x_13;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_30 = lean_ctor_get(x_13, 0);
lean_inc(x_30);
lean_dec(x_13);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
x_33 = lean_ctor_get(x_30, 2);
lean_inc(x_33);
x_34 = lean_ctor_get(x_30, 3);
lean_inc(x_34);
x_35 = lean_ctor_get(x_30, 4);
lean_inc(x_35);
lean_dec(x_30);
x_36 = l_Lean_Expr_Inhabited;
x_37 = lean_unsigned_to_nat(0u);
x_38 = lean_array_get(x_36, x_32, x_37);
x_39 = lean_unsigned_to_nat(1u);
x_40 = lean_array_get(x_36, x_32, x_39);
lean_dec(x_32);
x_41 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_41, 0, x_31);
lean_ctor_set(x_41, 1, x_38);
lean_ctor_set(x_41, 2, x_40);
lean_ctor_set(x_41, 3, x_33);
lean_ctor_set(x_41, 4, x_34);
lean_ctor_set(x_41, 5, x_35);
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_41);
return x_42;
}
}
}
}
lean_object* l_Lean_Closure_mkValueTypeClosure___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_5);
lean_dec(x_5);
x_7 = l_Lean_Closure_mkValueTypeClosure(x_1, x_2, x_3, x_4, x_6);
return x_7;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Std_ShareCommon(lean_object*);
lean_object* initialize_Lean_MetavarContext(lean_object*);
lean_object* initialize_Lean_Environment(lean_object*);
lean_object* initialize_Lean_Util_FoldConsts(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Util_Closure(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_ShareCommon(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_MetavarContext(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Environment(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_FoldConsts(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Closure_mkNewLevelParam___closed__1 = _init_l_Lean_Closure_mkNewLevelParam___closed__1();
lean_mark_persistent(l_Lean_Closure_mkNewLevelParam___closed__1);
l_Lean_Closure_mkNewLevelParam___closed__2 = _init_l_Lean_Closure_mkNewLevelParam___closed__2();
lean_mark_persistent(l_Lean_Closure_mkNewLevelParam___closed__2);
l_Lean_Closure_Lean_MonadNameGenerator___closed__1 = _init_l_Lean_Closure_Lean_MonadNameGenerator___closed__1();
lean_mark_persistent(l_Lean_Closure_Lean_MonadNameGenerator___closed__1);
l_Lean_Closure_Lean_MonadNameGenerator___closed__2 = _init_l_Lean_Closure_Lean_MonadNameGenerator___closed__2();
lean_mark_persistent(l_Lean_Closure_Lean_MonadNameGenerator___closed__2);
l_Lean_Closure_Lean_MonadNameGenerator___closed__3 = _init_l_Lean_Closure_Lean_MonadNameGenerator___closed__3();
lean_mark_persistent(l_Lean_Closure_Lean_MonadNameGenerator___closed__3);
l_Lean_Closure_Lean_MonadNameGenerator___closed__4 = _init_l_Lean_Closure_Lean_MonadNameGenerator___closed__4();
lean_mark_persistent(l_Lean_Closure_Lean_MonadNameGenerator___closed__4);
l_Lean_Closure_Lean_MonadNameGenerator = _init_l_Lean_Closure_Lean_MonadNameGenerator();
lean_mark_persistent(l_Lean_Closure_Lean_MonadNameGenerator);
l_Lean_Closure_mkNextUserName___rarg___closed__1 = _init_l_Lean_Closure_mkNextUserName___rarg___closed__1();
lean_mark_persistent(l_Lean_Closure_mkNextUserName___rarg___closed__1);
l_Lean_Closure_mkNextUserName___rarg___closed__2 = _init_l_Lean_Closure_mkNextUserName___rarg___closed__2();
lean_mark_persistent(l_Lean_Closure_mkNextUserName___rarg___closed__2);
l_Lean_Closure_ExprToClose_inhabited___closed__1 = _init_l_Lean_Closure_ExprToClose_inhabited___closed__1();
lean_mark_persistent(l_Lean_Closure_ExprToClose_inhabited___closed__1);
l_Lean_Closure_ExprToClose_inhabited = _init_l_Lean_Closure_ExprToClose_inhabited();
lean_mark_persistent(l_Lean_Closure_ExprToClose_inhabited);
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
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
