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
lean_object* l_Std_mkHashMap___at_Lean_Closure_mkClosure___spec__2(lean_object*);
lean_object* l_Lean_Closure_getUserName(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Closure_mkLetDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_update_mdata(lean_object*, lean_object*);
lean_object* lean_local_ctx_mk_let_decl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_updateMData_x21___closed__2;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_metavar_ctx_get_expr_assignment(lean_object*, lean_object*);
extern lean_object* l_Array_empty___closed__1;
uint8_t l_Lean_Level_hasMVar(lean_object*);
extern lean_object* l_Lean_MetavarContext_getDecl___closed__2;
extern lean_object* l_Std_ShareCommon_State_empty;
lean_object* l_Std_HashMapImp_moveEntries___main___at_Lean_Closure_visitExpr___spec__6(lean_object*, lean_object*, lean_object*);
size_t l_Lean_Level_hash(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
extern lean_object* l_Lean_Level_Inhabited;
uint8_t l_Lean_Level_hasParam(lean_object*);
lean_object* l_Std_HashMapImp_moveEntries___main___at_Lean_Closure_visitLevel___spec__6(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Closure_mkFreshFVarId(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Std_AssocList_find_x3f___main___at_Lean_Closure_visitExpr___spec__2___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Closure_collectLevel(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Level_updateMax_x21___closed__2;
extern lean_object* l_Lean_Expr_updateLambdaE_x21___closed__1;
uint32_t l_UInt32_add(uint32_t, uint32_t);
uint8_t l_Lean_Environment_hasUnsafe(lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_getFVars(lean_object*);
extern lean_object* l_Lean_LocalContext_Inhabited___closed__2;
lean_object* l_Lean_mkAuxDefinition(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Std_HashMapImp_find_x3f___at_Lean_Closure_visitExpr___spec__1(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_Closure_mkClosure___closed__4;
lean_object* lean_state_sharecommon(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasLevelParam(lean_object*);
lean_object* lean_metavar_ctx_get_level_assignment(lean_object*, lean_object*);
lean_object* l_Std_HashMapImp_find_x3f___at_Lean_Closure_visitExpr___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Closure_mkNextUserName___rarg(lean_object*);
lean_object* l_Std_AssocList_find_x3f___main___at_Lean_Closure_visitLevel___spec__2(lean_object*, lean_object*);
lean_object* l_Std_HashMapImp_insert___at_Lean_Closure_visitExpr___spec__3(lean_object*, lean_object*, lean_object*);
lean_object* lean_level_update_max(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_HashMapImp_expand___at_Lean_Closure_visitLevel___spec__5(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_mkHashMapImp___rarg(lean_object*);
lean_object* l_Lean_Name_appendIndexAfter(lean_object*, lean_object*);
uint8_t l_Std_AssocList_contains___main___at_Lean_Closure_visitLevel___spec__4(lean_object*, lean_object*);
lean_object* l_Lean_Closure_collectLevelAux___main(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Closure_mkClosure___closed__5;
size_t l_Lean_Expr_hash(lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Lean_Closure_mkFreshFVarId___rarg(lean_object*);
lean_object* l_Std_AssocList_contains___main___at_Lean_Closure_visitLevel___spec__4___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Closure_mkClosure___closed__6;
lean_object* l_Std_HashMapImp_expand___at_Lean_Closure_visitExpr___spec__5(lean_object*, lean_object*);
size_t lean_usize_modn(size_t, lean_object*);
lean_object* l_Lean_getMaxHeight(lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_updateApp_x21___closed__1;
lean_object* l_Lean_Closure_collectLevelAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_HashMapImp_insert___at_Lean_Closure_visitLevel___spec__3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Closure_mkClosure___closed__3;
lean_object* lean_expr_update_let(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Closure_collectExprAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
uint8_t l_Lean_Expr_Data_binderInfo(uint64_t);
lean_object* l_Std_HashMapImp_find_x3f___at_Lean_Closure_visitLevel___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Std_AssocList_foldlM___main___at_Lean_Closure_visitLevel___spec__7(lean_object*, lean_object*);
lean_object* l_Std_mkHashMap___at_Lean_Closure_mkClosure___spec__3(lean_object*);
lean_object* l_Lean_Closure_mkLocalDecl(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* lean_expr_update_proj(lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_updateProj_x21___closed__2;
lean_object* lean_local_ctx_mk_local_decl(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Std_AssocList_foldlM___main___at_Lean_Closure_visitExpr___spec__7(lean_object*, lean_object*);
lean_object* lean_level_update_imax(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Closure_mkNextUserName(lean_object*);
lean_object* l_Lean_Closure_mkClosure___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_AssocList_replace___main___at_Lean_Closure_visitLevel___spec__8(lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_equal(lean_object*, lean_object*);
lean_object* lean_expr_update_sort(lean_object*, lean_object*);
lean_object* l_List_mapM___main___at_Lean_Closure_collectExprAux___main___spec__1(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_Closure_mkClosure___closed__1;
lean_object* l_Lean_Environment_addAndCompile(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_AssocList_contains___main___at_Lean_Closure_visitExpr___spec__4___boxed(lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_Lean_Closure_mkNextUserName___rarg___closed__1;
lean_object* l_Lean_Closure_mkClosure(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_Level_updateSucc_x21___closed__2;
lean_object* l_Lean_LocalContext_mkLambda(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Closure_mkClosure___closed__2;
lean_object* l_Lean_Closure_mkNextUserName___rarg___closed__2;
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_metavar_ctx_find_decl(lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_updateLet_x21___closed__1;
lean_object* lean_expr_update_lambda(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* lean_level_update_succ(lean_object*, lean_object*);
extern lean_object* l_Lean_LocalContext_get_x21___closed__1;
uint8_t l_Std_AssocList_contains___main___at_Lean_Closure_visitExpr___spec__4(lean_object*, lean_object*);
lean_object* l_Array_toList___rarg(lean_object*);
extern lean_object* l_Lean_Expr_Inhabited;
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_Closure_mkFreshFVarId___boxed(lean_object*);
lean_object* l_Lean_Closure_mkLocalDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_AssocList_replace___main___at_Lean_Closure_visitExpr___spec__8(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Closure_collectExprAux___main(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_ShareCommonT_withShareCommon___at_Lean_Closure_mkClosure___spec__1(lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_local_ctx_find(lean_object*, lean_object*);
lean_object* l_Lean_mkLevelParam(lean_object*);
lean_object* l_Lean_LocalContext_mkForall(lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_update_app(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Closure_mkNextUserName___boxed(lean_object*);
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
lean_object* l_Std_HashMapImp_find_x3f___at_Lean_Closure_visitLevel___spec__1(lean_object*, lean_object*);
lean_object* l_Std_AssocList_find_x3f___main___at_Lean_Closure_visitExpr___spec__2(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_mkAuxDefinition___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
x_13 = lean_ctor_get(x_10, 2);
lean_inc(x_12);
x_14 = l_Std_HashMapImp_insert___at_Lean_Closure_visitLevel___spec__3(x_13, x_2, x_12);
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
x_25 = l_Std_HashMapImp_insert___at_Lean_Closure_visitLevel___spec__3(x_18, x_2, x_15);
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
x_39 = l_Std_HashMapImp_insert___at_Lean_Closure_visitLevel___spec__3(x_31, x_2, x_28);
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
x_5 = lean_ctor_get(x_3, 4);
x_6 = lean_ctor_get(x_3, 5);
x_7 = lean_ctor_get(x_3, 6);
x_8 = l_Lean_Closure_mkNewLevelParam___closed__2;
lean_inc(x_6);
x_9 = l_Lean_Name_appendIndexAfter(x_8, x_6);
lean_inc(x_9);
x_10 = l_Lean_mkLevelParam(x_9);
x_11 = lean_array_push(x_5, x_9);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_6, x_12);
lean_dec(x_6);
x_14 = lean_array_push(x_7, x_1);
lean_ctor_set(x_3, 6, x_14);
lean_ctor_set(x_3, 5, x_13);
lean_ctor_set(x_3, 4, x_11);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_10);
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
x_27 = l_Lean_mkLevelParam(x_26);
x_28 = lean_array_push(x_20, x_26);
x_29 = lean_unsigned_to_nat(1u);
x_30 = lean_nat_add(x_21, x_29);
lean_dec(x_21);
x_31 = lean_array_push(x_22, x_1);
x_32 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_32, 0, x_16);
lean_ctor_set(x_32, 1, x_17);
lean_ctor_set(x_32, 2, x_18);
lean_ctor_set(x_32, 3, x_19);
lean_ctor_set(x_32, 4, x_28);
lean_ctor_set(x_32, 5, x_30);
lean_ctor_set(x_32, 6, x_31);
lean_ctor_set(x_32, 7, x_23);
lean_ctor_set(x_32, 8, x_24);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_27);
lean_ctor_set(x_33, 1, x_32);
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
lean_dec(x_2);
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
lean_dec(x_2);
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
x_22 = lean_ctor_get(x_19, 2);
lean_inc(x_20);
x_23 = l_Std_HashMapImp_insert___at_Lean_Closure_visitLevel___spec__3(x_22, x_14, x_20);
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
x_33 = l_Std_HashMapImp_insert___at_Lean_Closure_visitLevel___spec__3(x_26, x_14, x_20);
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
lean_dec(x_2);
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
lean_dec(x_2);
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
x_56 = l_Std_HashMapImp_find_x3f___at_Lean_Closure_visitLevel___spec__1(x_55, x_42);
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
x_62 = l_Std_HashMapImp_insert___at_Lean_Closure_visitLevel___spec__3(x_61, x_42, x_59);
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
x_72 = l_Std_HashMapImp_insert___at_Lean_Closure_visitLevel___spec__3(x_65, x_42, x_59);
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
lean_dec(x_2);
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
x_83 = l_Std_HashMapImp_find_x3f___at_Lean_Closure_visitLevel___spec__1(x_82, x_41);
lean_dec(x_82);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; 
lean_inc(x_2);
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
x_89 = l_Std_HashMapImp_insert___at_Lean_Closure_visitLevel___spec__3(x_88, x_41, x_86);
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
x_99 = l_Std_HashMapImp_insert___at_Lean_Closure_visitLevel___spec__3(x_92, x_41, x_86);
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
lean_dec(x_2);
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
x_122 = l_Std_HashMapImp_find_x3f___at_Lean_Closure_visitLevel___spec__1(x_121, x_108);
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
x_128 = l_Std_HashMapImp_insert___at_Lean_Closure_visitLevel___spec__3(x_127, x_108, x_125);
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
x_138 = l_Std_HashMapImp_insert___at_Lean_Closure_visitLevel___spec__3(x_131, x_108, x_125);
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
lean_dec(x_2);
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
x_149 = l_Std_HashMapImp_find_x3f___at_Lean_Closure_visitLevel___spec__1(x_148, x_107);
lean_dec(x_148);
if (lean_obj_tag(x_149) == 0)
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; uint8_t x_153; 
lean_inc(x_2);
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
x_155 = l_Std_HashMapImp_insert___at_Lean_Closure_visitLevel___spec__3(x_154, x_107, x_152);
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
x_165 = l_Std_HashMapImp_insert___at_Lean_Closure_visitLevel___spec__3(x_158, x_107, x_152);
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
case 4:
{
lean_object* x_173; 
x_173 = l_Lean_Closure_mkNewLevelParam(x_1, x_2, x_3);
lean_dec(x_2);
return x_173;
}
default: 
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; 
x_174 = lean_ctor_get(x_1, 0);
lean_inc(x_174);
x_175 = lean_ctor_get(x_2, 0);
lean_inc(x_175);
x_176 = lean_metavar_ctx_get_level_assignment(x_175, x_174);
if (lean_obj_tag(x_176) == 0)
{
lean_object* x_177; 
x_177 = l_Lean_Closure_mkNewLevelParam(x_1, x_2, x_3);
lean_dec(x_2);
return x_177;
}
else
{
lean_object* x_178; lean_object* x_179; uint8_t x_219; 
lean_dec(x_1);
x_178 = lean_ctor_get(x_176, 0);
lean_inc(x_178);
lean_dec(x_176);
x_219 = l_Lean_Level_hasMVar(x_178);
if (x_219 == 0)
{
uint8_t x_220; 
x_220 = l_Lean_Level_hasParam(x_178);
if (x_220 == 0)
{
lean_object* x_221; 
lean_dec(x_2);
x_221 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_221, 0, x_178);
lean_ctor_set(x_221, 1, x_3);
return x_221;
}
else
{
lean_object* x_222; 
x_222 = lean_box(0);
x_179 = x_222;
goto block_218;
}
}
else
{
lean_object* x_223; 
x_223 = lean_box(0);
x_179 = x_223;
goto block_218;
}
block_218:
{
lean_object* x_180; lean_object* x_181; 
lean_dec(x_179);
x_180 = lean_ctor_get(x_3, 2);
lean_inc(x_180);
x_181 = l_Std_HashMapImp_find_x3f___at_Lean_Closure_visitLevel___spec__1(x_180, x_178);
lean_dec(x_180);
if (lean_obj_tag(x_181) == 0)
{
lean_object* x_182; uint8_t x_183; 
lean_inc(x_178);
x_182 = l_Lean_Closure_collectLevelAux___main(x_178, x_2, x_3);
x_183 = !lean_is_exclusive(x_182);
if (x_183 == 0)
{
lean_object* x_184; uint8_t x_185; 
x_184 = lean_ctor_get(x_182, 1);
x_185 = !lean_is_exclusive(x_184);
if (x_185 == 0)
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; 
x_186 = lean_ctor_get(x_182, 0);
x_187 = lean_ctor_get(x_184, 2);
lean_inc(x_186);
x_188 = l_Std_HashMapImp_insert___at_Lean_Closure_visitLevel___spec__3(x_187, x_178, x_186);
lean_ctor_set(x_184, 2, x_188);
return x_182;
}
else
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; 
x_189 = lean_ctor_get(x_182, 0);
x_190 = lean_ctor_get(x_184, 0);
x_191 = lean_ctor_get(x_184, 1);
x_192 = lean_ctor_get(x_184, 2);
x_193 = lean_ctor_get(x_184, 3);
x_194 = lean_ctor_get(x_184, 4);
x_195 = lean_ctor_get(x_184, 5);
x_196 = lean_ctor_get(x_184, 6);
x_197 = lean_ctor_get(x_184, 7);
x_198 = lean_ctor_get(x_184, 8);
lean_inc(x_198);
lean_inc(x_197);
lean_inc(x_196);
lean_inc(x_195);
lean_inc(x_194);
lean_inc(x_193);
lean_inc(x_192);
lean_inc(x_191);
lean_inc(x_190);
lean_dec(x_184);
lean_inc(x_189);
x_199 = l_Std_HashMapImp_insert___at_Lean_Closure_visitLevel___spec__3(x_192, x_178, x_189);
x_200 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_200, 0, x_190);
lean_ctor_set(x_200, 1, x_191);
lean_ctor_set(x_200, 2, x_199);
lean_ctor_set(x_200, 3, x_193);
lean_ctor_set(x_200, 4, x_194);
lean_ctor_set(x_200, 5, x_195);
lean_ctor_set(x_200, 6, x_196);
lean_ctor_set(x_200, 7, x_197);
lean_ctor_set(x_200, 8, x_198);
lean_ctor_set(x_182, 1, x_200);
return x_182;
}
}
else
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; 
x_201 = lean_ctor_get(x_182, 1);
x_202 = lean_ctor_get(x_182, 0);
lean_inc(x_201);
lean_inc(x_202);
lean_dec(x_182);
x_203 = lean_ctor_get(x_201, 0);
lean_inc(x_203);
x_204 = lean_ctor_get(x_201, 1);
lean_inc(x_204);
x_205 = lean_ctor_get(x_201, 2);
lean_inc(x_205);
x_206 = lean_ctor_get(x_201, 3);
lean_inc(x_206);
x_207 = lean_ctor_get(x_201, 4);
lean_inc(x_207);
x_208 = lean_ctor_get(x_201, 5);
lean_inc(x_208);
x_209 = lean_ctor_get(x_201, 6);
lean_inc(x_209);
x_210 = lean_ctor_get(x_201, 7);
lean_inc(x_210);
x_211 = lean_ctor_get(x_201, 8);
lean_inc(x_211);
if (lean_is_exclusive(x_201)) {
 lean_ctor_release(x_201, 0);
 lean_ctor_release(x_201, 1);
 lean_ctor_release(x_201, 2);
 lean_ctor_release(x_201, 3);
 lean_ctor_release(x_201, 4);
 lean_ctor_release(x_201, 5);
 lean_ctor_release(x_201, 6);
 lean_ctor_release(x_201, 7);
 lean_ctor_release(x_201, 8);
 x_212 = x_201;
} else {
 lean_dec_ref(x_201);
 x_212 = lean_box(0);
}
lean_inc(x_202);
x_213 = l_Std_HashMapImp_insert___at_Lean_Closure_visitLevel___spec__3(x_205, x_178, x_202);
if (lean_is_scalar(x_212)) {
 x_214 = lean_alloc_ctor(0, 9, 0);
} else {
 x_214 = x_212;
}
lean_ctor_set(x_214, 0, x_203);
lean_ctor_set(x_214, 1, x_204);
lean_ctor_set(x_214, 2, x_213);
lean_ctor_set(x_214, 3, x_206);
lean_ctor_set(x_214, 4, x_207);
lean_ctor_set(x_214, 5, x_208);
lean_ctor_set(x_214, 6, x_209);
lean_ctor_set(x_214, 7, x_210);
lean_ctor_set(x_214, 8, x_211);
x_215 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_215, 0, x_202);
lean_ctor_set(x_215, 1, x_214);
return x_215;
}
}
else
{
lean_object* x_216; lean_object* x_217; 
lean_dec(x_178);
lean_dec(x_2);
x_216 = lean_ctor_get(x_181, 0);
lean_inc(x_216);
lean_dec(x_181);
x_217 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_217, 0, x_216);
lean_ctor_set(x_217, 1, x_3);
return x_217;
}
}
}
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
lean_object* l_Lean_Closure_collectLevelAux(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Closure_collectLevelAux___main(x_1, x_2, x_3);
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
lean_dec(x_2);
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
x_12 = lean_ctor_get(x_9, 2);
lean_inc(x_11);
x_13 = l_Std_HashMapImp_insert___at_Lean_Closure_visitLevel___spec__3(x_12, x_1, x_11);
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
x_24 = l_Std_HashMapImp_insert___at_Lean_Closure_visitLevel___spec__3(x_17, x_1, x_14);
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
x_38 = l_Std_HashMapImp_insert___at_Lean_Closure_visitLevel___spec__3(x_30, x_1, x_27);
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
lean_dec(x_2);
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
x_9 = l_Lean_Closure_mkFreshFVarId___rarg(x_8);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
x_13 = l_Lean_mkFVar(x_11);
x_14 = !lean_is_exclusive(x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_12, 0);
x_16 = lean_local_ctx_mk_local_decl(x_15, x_11, x_7, x_2, x_3);
lean_ctor_set(x_12, 0, x_16);
lean_ctor_set(x_9, 0, x_13);
return x_9;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_17 = lean_ctor_get(x_12, 0);
x_18 = lean_ctor_get(x_12, 1);
x_19 = lean_ctor_get(x_12, 2);
x_20 = lean_ctor_get(x_12, 3);
x_21 = lean_ctor_get(x_12, 4);
x_22 = lean_ctor_get(x_12, 5);
x_23 = lean_ctor_get(x_12, 6);
x_24 = lean_ctor_get(x_12, 7);
x_25 = lean_ctor_get(x_12, 8);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_12);
x_26 = lean_local_ctx_mk_local_decl(x_17, x_11, x_7, x_2, x_3);
x_27 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_18);
lean_ctor_set(x_27, 2, x_19);
lean_ctor_set(x_27, 3, x_20);
lean_ctor_set(x_27, 4, x_21);
lean_ctor_set(x_27, 5, x_22);
lean_ctor_set(x_27, 6, x_23);
lean_ctor_set(x_27, 7, x_24);
lean_ctor_set(x_27, 8, x_25);
lean_ctor_set(x_9, 1, x_27);
lean_ctor_set(x_9, 0, x_13);
return x_9;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_28 = lean_ctor_get(x_9, 0);
x_29 = lean_ctor_get(x_9, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_9);
lean_inc(x_28);
x_30 = l_Lean_mkFVar(x_28);
x_31 = lean_ctor_get(x_29, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_29, 1);
lean_inc(x_32);
x_33 = lean_ctor_get(x_29, 2);
lean_inc(x_33);
x_34 = lean_ctor_get(x_29, 3);
lean_inc(x_34);
x_35 = lean_ctor_get(x_29, 4);
lean_inc(x_35);
x_36 = lean_ctor_get(x_29, 5);
lean_inc(x_36);
x_37 = lean_ctor_get(x_29, 6);
lean_inc(x_37);
x_38 = lean_ctor_get(x_29, 7);
lean_inc(x_38);
x_39 = lean_ctor_get(x_29, 8);
lean_inc(x_39);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 lean_ctor_release(x_29, 2);
 lean_ctor_release(x_29, 3);
 lean_ctor_release(x_29, 4);
 lean_ctor_release(x_29, 5);
 lean_ctor_release(x_29, 6);
 lean_ctor_release(x_29, 7);
 lean_ctor_release(x_29, 8);
 x_40 = x_29;
} else {
 lean_dec_ref(x_29);
 x_40 = lean_box(0);
}
x_41 = lean_local_ctx_mk_local_decl(x_31, x_28, x_7, x_2, x_3);
if (lean_is_scalar(x_40)) {
 x_42 = lean_alloc_ctor(0, 9, 0);
} else {
 x_42 = x_40;
}
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_32);
lean_ctor_set(x_42, 2, x_33);
lean_ctor_set(x_42, 3, x_34);
lean_ctor_set(x_42, 4, x_35);
lean_ctor_set(x_42, 5, x_36);
lean_ctor_set(x_42, 6, x_37);
lean_ctor_set(x_42, 7, x_38);
lean_ctor_set(x_42, 8, x_39);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_30);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
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
x_6 = l_Lean_Closure_mkFreshFVarId___rarg(x_5);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
x_10 = l_Lean_mkFVar(x_8);
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_9, 0);
x_13 = lean_local_ctx_mk_let_decl(x_12, x_8, x_1, x_2, x_3);
lean_ctor_set(x_9, 0, x_13);
lean_ctor_set(x_6, 0, x_10);
return x_6;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_14 = lean_ctor_get(x_9, 0);
x_15 = lean_ctor_get(x_9, 1);
x_16 = lean_ctor_get(x_9, 2);
x_17 = lean_ctor_get(x_9, 3);
x_18 = lean_ctor_get(x_9, 4);
x_19 = lean_ctor_get(x_9, 5);
x_20 = lean_ctor_get(x_9, 6);
x_21 = lean_ctor_get(x_9, 7);
x_22 = lean_ctor_get(x_9, 8);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_9);
x_23 = lean_local_ctx_mk_let_decl(x_14, x_8, x_1, x_2, x_3);
x_24 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_15);
lean_ctor_set(x_24, 2, x_16);
lean_ctor_set(x_24, 3, x_17);
lean_ctor_set(x_24, 4, x_18);
lean_ctor_set(x_24, 5, x_19);
lean_ctor_set(x_24, 6, x_20);
lean_ctor_set(x_24, 7, x_21);
lean_ctor_set(x_24, 8, x_22);
lean_ctor_set(x_6, 1, x_24);
lean_ctor_set(x_6, 0, x_10);
return x_6;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_25 = lean_ctor_get(x_6, 0);
x_26 = lean_ctor_get(x_6, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_6);
lean_inc(x_25);
x_27 = l_Lean_mkFVar(x_25);
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
x_38 = lean_local_ctx_mk_let_decl(x_28, x_25, x_1, x_2, x_3);
if (lean_is_scalar(x_37)) {
 x_39 = lean_alloc_ctor(0, 9, 0);
} else {
 x_39 = x_37;
}
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_29);
lean_ctor_set(x_39, 2, x_30);
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
x_13 = lean_ctor_get(x_10, 3);
lean_inc(x_12);
x_14 = l_Std_HashMapImp_insert___at_Lean_Closure_visitExpr___spec__3(x_13, x_2, x_12);
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
x_25 = l_Std_HashMapImp_insert___at_Lean_Closure_visitExpr___spec__3(x_19, x_2, x_15);
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
x_39 = l_Std_HashMapImp_insert___at_Lean_Closure_visitExpr___spec__3(x_32, x_2, x_28);
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
lean_dec(x_2);
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
lean_inc(x_2);
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
lean_inc(x_2);
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
lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_68; uint8_t x_94; 
x_29 = lean_ctor_get(x_27, 2);
lean_inc(x_29);
x_30 = lean_ctor_get(x_27, 3);
lean_inc(x_30);
x_31 = lean_ctor_get_uint8(x_27, sizeof(void*)*4);
lean_dec(x_27);
x_94 = l_Lean_Expr_hasLevelParam(x_30);
if (x_94 == 0)
{
uint8_t x_95; 
x_95 = l_Lean_Expr_hasFVar(x_30);
if (x_95 == 0)
{
uint8_t x_96; 
x_96 = l_Lean_Expr_hasMVar(x_30);
if (x_96 == 0)
{
x_32 = x_30;
x_33 = x_3;
goto block_67;
}
else
{
lean_object* x_97; 
x_97 = lean_box(0);
x_68 = x_97;
goto block_93;
}
}
else
{
lean_object* x_98; 
x_98 = lean_box(0);
x_68 = x_98;
goto block_93;
}
}
else
{
lean_object* x_99; 
x_99 = lean_box(0);
x_68 = x_99;
goto block_93;
}
block_67:
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; 
if (lean_is_scalar(x_28)) {
 x_34 = lean_alloc_ctor(1, 1, 0);
} else {
 x_34 = x_28;
}
lean_ctor_set(x_34, 0, x_29);
x_35 = l_Lean_Closure_mkLocalDecl(x_34, x_32, x_31, x_2, x_33);
lean_dec(x_2);
lean_dec(x_34);
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
lean_object* x_37; uint8_t x_38; 
x_37 = lean_ctor_get(x_35, 1);
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_37, 8);
x_40 = lean_array_push(x_39, x_1);
lean_ctor_set(x_37, 8, x_40);
return x_35;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_41 = lean_ctor_get(x_37, 0);
x_42 = lean_ctor_get(x_37, 1);
x_43 = lean_ctor_get(x_37, 2);
x_44 = lean_ctor_get(x_37, 3);
x_45 = lean_ctor_get(x_37, 4);
x_46 = lean_ctor_get(x_37, 5);
x_47 = lean_ctor_get(x_37, 6);
x_48 = lean_ctor_get(x_37, 7);
x_49 = lean_ctor_get(x_37, 8);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_37);
x_50 = lean_array_push(x_49, x_1);
x_51 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_51, 0, x_41);
lean_ctor_set(x_51, 1, x_42);
lean_ctor_set(x_51, 2, x_43);
lean_ctor_set(x_51, 3, x_44);
lean_ctor_set(x_51, 4, x_45);
lean_ctor_set(x_51, 5, x_46);
lean_ctor_set(x_51, 6, x_47);
lean_ctor_set(x_51, 7, x_48);
lean_ctor_set(x_51, 8, x_50);
lean_ctor_set(x_35, 1, x_51);
return x_35;
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_52 = lean_ctor_get(x_35, 1);
x_53 = lean_ctor_get(x_35, 0);
lean_inc(x_52);
lean_inc(x_53);
lean_dec(x_35);
x_54 = lean_ctor_get(x_52, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_52, 1);
lean_inc(x_55);
x_56 = lean_ctor_get(x_52, 2);
lean_inc(x_56);
x_57 = lean_ctor_get(x_52, 3);
lean_inc(x_57);
x_58 = lean_ctor_get(x_52, 4);
lean_inc(x_58);
x_59 = lean_ctor_get(x_52, 5);
lean_inc(x_59);
x_60 = lean_ctor_get(x_52, 6);
lean_inc(x_60);
x_61 = lean_ctor_get(x_52, 7);
lean_inc(x_61);
x_62 = lean_ctor_get(x_52, 8);
lean_inc(x_62);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 lean_ctor_release(x_52, 2);
 lean_ctor_release(x_52, 3);
 lean_ctor_release(x_52, 4);
 lean_ctor_release(x_52, 5);
 lean_ctor_release(x_52, 6);
 lean_ctor_release(x_52, 7);
 lean_ctor_release(x_52, 8);
 x_63 = x_52;
} else {
 lean_dec_ref(x_52);
 x_63 = lean_box(0);
}
x_64 = lean_array_push(x_62, x_1);
if (lean_is_scalar(x_63)) {
 x_65 = lean_alloc_ctor(0, 9, 0);
} else {
 x_65 = x_63;
}
lean_ctor_set(x_65, 0, x_54);
lean_ctor_set(x_65, 1, x_55);
lean_ctor_set(x_65, 2, x_56);
lean_ctor_set(x_65, 3, x_57);
lean_ctor_set(x_65, 4, x_58);
lean_ctor_set(x_65, 5, x_59);
lean_ctor_set(x_65, 6, x_60);
lean_ctor_set(x_65, 7, x_61);
lean_ctor_set(x_65, 8, x_64);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_53);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
block_93:
{
lean_object* x_69; lean_object* x_70; 
lean_dec(x_68);
x_69 = lean_ctor_get(x_3, 3);
lean_inc(x_69);
x_70 = l_Std_HashMapImp_find_x3f___at_Lean_Closure_visitExpr___spec__1(x_69, x_30);
lean_dec(x_69);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; 
lean_inc(x_2);
lean_inc(x_30);
x_71 = l_Lean_Closure_collectExprAux___main(x_30, x_2, x_3);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_72 = lean_ctor_get(x_71, 1);
lean_inc(x_72);
x_73 = lean_ctor_get(x_71, 0);
lean_inc(x_73);
lean_dec(x_71);
x_74 = !lean_is_exclusive(x_72);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; 
x_75 = lean_ctor_get(x_72, 3);
lean_inc(x_73);
x_76 = l_Std_HashMapImp_insert___at_Lean_Closure_visitExpr___spec__3(x_75, x_30, x_73);
lean_ctor_set(x_72, 3, x_76);
x_32 = x_73;
x_33 = x_72;
goto block_67;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_77 = lean_ctor_get(x_72, 0);
x_78 = lean_ctor_get(x_72, 1);
x_79 = lean_ctor_get(x_72, 2);
x_80 = lean_ctor_get(x_72, 3);
x_81 = lean_ctor_get(x_72, 4);
x_82 = lean_ctor_get(x_72, 5);
x_83 = lean_ctor_get(x_72, 6);
x_84 = lean_ctor_get(x_72, 7);
x_85 = lean_ctor_get(x_72, 8);
lean_inc(x_85);
lean_inc(x_84);
lean_inc(x_83);
lean_inc(x_82);
lean_inc(x_81);
lean_inc(x_80);
lean_inc(x_79);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_72);
lean_inc(x_73);
x_86 = l_Std_HashMapImp_insert___at_Lean_Closure_visitExpr___spec__3(x_80, x_30, x_73);
x_87 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_87, 0, x_77);
lean_ctor_set(x_87, 1, x_78);
lean_ctor_set(x_87, 2, x_79);
lean_ctor_set(x_87, 3, x_86);
lean_ctor_set(x_87, 4, x_81);
lean_ctor_set(x_87, 5, x_82);
lean_ctor_set(x_87, 6, x_83);
lean_ctor_set(x_87, 7, x_84);
lean_ctor_set(x_87, 8, x_85);
x_32 = x_73;
x_33 = x_87;
goto block_67;
}
}
else
{
uint8_t x_88; 
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_2);
lean_dec(x_1);
x_88 = !lean_is_exclusive(x_71);
if (x_88 == 0)
{
return x_71;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_71, 0);
x_90 = lean_ctor_get(x_71, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_71);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
return x_91;
}
}
}
else
{
lean_object* x_92; 
lean_dec(x_30);
x_92 = lean_ctor_get(x_70, 0);
lean_inc(x_92);
lean_dec(x_70);
x_32 = x_92;
x_33 = x_3;
goto block_67;
}
}
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_142; uint8_t x_168; 
lean_dec(x_28);
lean_dec(x_1);
x_100 = lean_ctor_get(x_27, 2);
lean_inc(x_100);
x_101 = lean_ctor_get(x_27, 3);
lean_inc(x_101);
x_102 = lean_ctor_get(x_27, 4);
lean_inc(x_102);
lean_dec(x_27);
x_168 = lean_ctor_get_uint8(x_2, sizeof(void*)*2);
if (x_168 == 0)
{
uint8_t x_169; 
x_169 = l_Lean_Expr_hasLevelParam(x_101);
if (x_169 == 0)
{
uint8_t x_170; 
x_170 = l_Lean_Expr_hasFVar(x_101);
if (x_170 == 0)
{
uint8_t x_171; 
x_171 = l_Lean_Expr_hasMVar(x_101);
if (x_171 == 0)
{
x_103 = x_101;
x_104 = x_3;
goto block_141;
}
else
{
lean_object* x_172; 
x_172 = lean_box(0);
x_142 = x_172;
goto block_167;
}
}
else
{
lean_object* x_173; 
x_173 = lean_box(0);
x_142 = x_173;
goto block_167;
}
}
else
{
lean_object* x_174; 
x_174 = lean_box(0);
x_142 = x_174;
goto block_167;
}
}
else
{
lean_object* x_175; uint8_t x_219; 
lean_dec(x_101);
lean_dec(x_100);
x_219 = l_Lean_Expr_hasLevelParam(x_102);
if (x_219 == 0)
{
uint8_t x_220; 
x_220 = l_Lean_Expr_hasFVar(x_102);
if (x_220 == 0)
{
uint8_t x_221; 
x_221 = l_Lean_Expr_hasMVar(x_102);
if (x_221 == 0)
{
lean_object* x_222; 
lean_dec(x_2);
x_222 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_222, 0, x_102);
lean_ctor_set(x_222, 1, x_3);
return x_222;
}
else
{
lean_object* x_223; 
x_223 = lean_box(0);
x_175 = x_223;
goto block_218;
}
}
else
{
lean_object* x_224; 
x_224 = lean_box(0);
x_175 = x_224;
goto block_218;
}
}
else
{
lean_object* x_225; 
x_225 = lean_box(0);
x_175 = x_225;
goto block_218;
}
block_218:
{
lean_object* x_176; lean_object* x_177; 
lean_dec(x_175);
x_176 = lean_ctor_get(x_3, 3);
lean_inc(x_176);
x_177 = l_Std_HashMapImp_find_x3f___at_Lean_Closure_visitExpr___spec__1(x_176, x_102);
lean_dec(x_176);
if (lean_obj_tag(x_177) == 0)
{
lean_object* x_178; 
lean_inc(x_102);
x_178 = l_Lean_Closure_collectExprAux___main(x_102, x_2, x_3);
if (lean_obj_tag(x_178) == 0)
{
uint8_t x_179; 
x_179 = !lean_is_exclusive(x_178);
if (x_179 == 0)
{
lean_object* x_180; uint8_t x_181; 
x_180 = lean_ctor_get(x_178, 1);
x_181 = !lean_is_exclusive(x_180);
if (x_181 == 0)
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_182 = lean_ctor_get(x_178, 0);
x_183 = lean_ctor_get(x_180, 3);
lean_inc(x_182);
x_184 = l_Std_HashMapImp_insert___at_Lean_Closure_visitExpr___spec__3(x_183, x_102, x_182);
lean_ctor_set(x_180, 3, x_184);
return x_178;
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; 
x_185 = lean_ctor_get(x_178, 0);
x_186 = lean_ctor_get(x_180, 0);
x_187 = lean_ctor_get(x_180, 1);
x_188 = lean_ctor_get(x_180, 2);
x_189 = lean_ctor_get(x_180, 3);
x_190 = lean_ctor_get(x_180, 4);
x_191 = lean_ctor_get(x_180, 5);
x_192 = lean_ctor_get(x_180, 6);
x_193 = lean_ctor_get(x_180, 7);
x_194 = lean_ctor_get(x_180, 8);
lean_inc(x_194);
lean_inc(x_193);
lean_inc(x_192);
lean_inc(x_191);
lean_inc(x_190);
lean_inc(x_189);
lean_inc(x_188);
lean_inc(x_187);
lean_inc(x_186);
lean_dec(x_180);
lean_inc(x_185);
x_195 = l_Std_HashMapImp_insert___at_Lean_Closure_visitExpr___spec__3(x_189, x_102, x_185);
x_196 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_196, 0, x_186);
lean_ctor_set(x_196, 1, x_187);
lean_ctor_set(x_196, 2, x_188);
lean_ctor_set(x_196, 3, x_195);
lean_ctor_set(x_196, 4, x_190);
lean_ctor_set(x_196, 5, x_191);
lean_ctor_set(x_196, 6, x_192);
lean_ctor_set(x_196, 7, x_193);
lean_ctor_set(x_196, 8, x_194);
lean_ctor_set(x_178, 1, x_196);
return x_178;
}
}
else
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; 
x_197 = lean_ctor_get(x_178, 1);
x_198 = lean_ctor_get(x_178, 0);
lean_inc(x_197);
lean_inc(x_198);
lean_dec(x_178);
x_199 = lean_ctor_get(x_197, 0);
lean_inc(x_199);
x_200 = lean_ctor_get(x_197, 1);
lean_inc(x_200);
x_201 = lean_ctor_get(x_197, 2);
lean_inc(x_201);
x_202 = lean_ctor_get(x_197, 3);
lean_inc(x_202);
x_203 = lean_ctor_get(x_197, 4);
lean_inc(x_203);
x_204 = lean_ctor_get(x_197, 5);
lean_inc(x_204);
x_205 = lean_ctor_get(x_197, 6);
lean_inc(x_205);
x_206 = lean_ctor_get(x_197, 7);
lean_inc(x_206);
x_207 = lean_ctor_get(x_197, 8);
lean_inc(x_207);
if (lean_is_exclusive(x_197)) {
 lean_ctor_release(x_197, 0);
 lean_ctor_release(x_197, 1);
 lean_ctor_release(x_197, 2);
 lean_ctor_release(x_197, 3);
 lean_ctor_release(x_197, 4);
 lean_ctor_release(x_197, 5);
 lean_ctor_release(x_197, 6);
 lean_ctor_release(x_197, 7);
 lean_ctor_release(x_197, 8);
 x_208 = x_197;
} else {
 lean_dec_ref(x_197);
 x_208 = lean_box(0);
}
lean_inc(x_198);
x_209 = l_Std_HashMapImp_insert___at_Lean_Closure_visitExpr___spec__3(x_202, x_102, x_198);
if (lean_is_scalar(x_208)) {
 x_210 = lean_alloc_ctor(0, 9, 0);
} else {
 x_210 = x_208;
}
lean_ctor_set(x_210, 0, x_199);
lean_ctor_set(x_210, 1, x_200);
lean_ctor_set(x_210, 2, x_201);
lean_ctor_set(x_210, 3, x_209);
lean_ctor_set(x_210, 4, x_203);
lean_ctor_set(x_210, 5, x_204);
lean_ctor_set(x_210, 6, x_205);
lean_ctor_set(x_210, 7, x_206);
lean_ctor_set(x_210, 8, x_207);
x_211 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_211, 0, x_198);
lean_ctor_set(x_211, 1, x_210);
return x_211;
}
}
else
{
uint8_t x_212; 
lean_dec(x_102);
x_212 = !lean_is_exclusive(x_178);
if (x_212 == 0)
{
return x_178;
}
else
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; 
x_213 = lean_ctor_get(x_178, 0);
x_214 = lean_ctor_get(x_178, 1);
lean_inc(x_214);
lean_inc(x_213);
lean_dec(x_178);
x_215 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_215, 0, x_213);
lean_ctor_set(x_215, 1, x_214);
return x_215;
}
}
}
else
{
lean_object* x_216; lean_object* x_217; 
lean_dec(x_102);
lean_dec(x_2);
x_216 = lean_ctor_get(x_177, 0);
lean_inc(x_216);
lean_dec(x_177);
x_217 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_217, 0, x_216);
lean_ctor_set(x_217, 1, x_3);
return x_217;
}
}
}
block_141:
{
lean_object* x_105; uint8_t x_134; 
x_134 = l_Lean_Expr_hasLevelParam(x_102);
if (x_134 == 0)
{
uint8_t x_135; 
x_135 = l_Lean_Expr_hasFVar(x_102);
if (x_135 == 0)
{
uint8_t x_136; 
x_136 = l_Lean_Expr_hasMVar(x_102);
if (x_136 == 0)
{
lean_object* x_137; 
x_137 = l_Lean_Closure_mkLetDecl(x_100, x_103, x_102, x_2, x_104);
lean_dec(x_2);
return x_137;
}
else
{
lean_object* x_138; 
x_138 = lean_box(0);
x_105 = x_138;
goto block_133;
}
}
else
{
lean_object* x_139; 
x_139 = lean_box(0);
x_105 = x_139;
goto block_133;
}
}
else
{
lean_object* x_140; 
x_140 = lean_box(0);
x_105 = x_140;
goto block_133;
}
block_133:
{
lean_object* x_106; lean_object* x_107; 
lean_dec(x_105);
x_106 = lean_ctor_get(x_104, 3);
lean_inc(x_106);
x_107 = l_Std_HashMapImp_find_x3f___at_Lean_Closure_visitExpr___spec__1(x_106, x_102);
lean_dec(x_106);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; 
lean_inc(x_2);
lean_inc(x_102);
x_108 = l_Lean_Closure_collectExprAux___main(x_102, x_2, x_104);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; lean_object* x_110; uint8_t x_111; 
x_109 = lean_ctor_get(x_108, 1);
lean_inc(x_109);
x_110 = lean_ctor_get(x_108, 0);
lean_inc(x_110);
lean_dec(x_108);
x_111 = !lean_is_exclusive(x_109);
if (x_111 == 0)
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_ctor_get(x_109, 3);
lean_inc(x_110);
x_113 = l_Std_HashMapImp_insert___at_Lean_Closure_visitExpr___spec__3(x_112, x_102, x_110);
lean_ctor_set(x_109, 3, x_113);
x_114 = l_Lean_Closure_mkLetDecl(x_100, x_103, x_110, x_2, x_109);
lean_dec(x_2);
return x_114;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_115 = lean_ctor_get(x_109, 0);
x_116 = lean_ctor_get(x_109, 1);
x_117 = lean_ctor_get(x_109, 2);
x_118 = lean_ctor_get(x_109, 3);
x_119 = lean_ctor_get(x_109, 4);
x_120 = lean_ctor_get(x_109, 5);
x_121 = lean_ctor_get(x_109, 6);
x_122 = lean_ctor_get(x_109, 7);
x_123 = lean_ctor_get(x_109, 8);
lean_inc(x_123);
lean_inc(x_122);
lean_inc(x_121);
lean_inc(x_120);
lean_inc(x_119);
lean_inc(x_118);
lean_inc(x_117);
lean_inc(x_116);
lean_inc(x_115);
lean_dec(x_109);
lean_inc(x_110);
x_124 = l_Std_HashMapImp_insert___at_Lean_Closure_visitExpr___spec__3(x_118, x_102, x_110);
x_125 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_125, 0, x_115);
lean_ctor_set(x_125, 1, x_116);
lean_ctor_set(x_125, 2, x_117);
lean_ctor_set(x_125, 3, x_124);
lean_ctor_set(x_125, 4, x_119);
lean_ctor_set(x_125, 5, x_120);
lean_ctor_set(x_125, 6, x_121);
lean_ctor_set(x_125, 7, x_122);
lean_ctor_set(x_125, 8, x_123);
x_126 = l_Lean_Closure_mkLetDecl(x_100, x_103, x_110, x_2, x_125);
lean_dec(x_2);
return x_126;
}
}
else
{
uint8_t x_127; 
lean_dec(x_103);
lean_dec(x_102);
lean_dec(x_100);
lean_dec(x_2);
x_127 = !lean_is_exclusive(x_108);
if (x_127 == 0)
{
return x_108;
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_128 = lean_ctor_get(x_108, 0);
x_129 = lean_ctor_get(x_108, 1);
lean_inc(x_129);
lean_inc(x_128);
lean_dec(x_108);
x_130 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_130, 0, x_128);
lean_ctor_set(x_130, 1, x_129);
return x_130;
}
}
}
else
{
lean_object* x_131; lean_object* x_132; 
lean_dec(x_102);
x_131 = lean_ctor_get(x_107, 0);
lean_inc(x_131);
lean_dec(x_107);
x_132 = l_Lean_Closure_mkLetDecl(x_100, x_103, x_131, x_2, x_104);
lean_dec(x_2);
return x_132;
}
}
}
block_167:
{
lean_object* x_143; lean_object* x_144; 
lean_dec(x_142);
x_143 = lean_ctor_get(x_3, 3);
lean_inc(x_143);
x_144 = l_Std_HashMapImp_find_x3f___at_Lean_Closure_visitExpr___spec__1(x_143, x_101);
lean_dec(x_143);
if (lean_obj_tag(x_144) == 0)
{
lean_object* x_145; 
lean_inc(x_2);
lean_inc(x_101);
x_145 = l_Lean_Closure_collectExprAux___main(x_101, x_2, x_3);
if (lean_obj_tag(x_145) == 0)
{
lean_object* x_146; lean_object* x_147; uint8_t x_148; 
x_146 = lean_ctor_get(x_145, 1);
lean_inc(x_146);
x_147 = lean_ctor_get(x_145, 0);
lean_inc(x_147);
lean_dec(x_145);
x_148 = !lean_is_exclusive(x_146);
if (x_148 == 0)
{
lean_object* x_149; lean_object* x_150; 
x_149 = lean_ctor_get(x_146, 3);
lean_inc(x_147);
x_150 = l_Std_HashMapImp_insert___at_Lean_Closure_visitExpr___spec__3(x_149, x_101, x_147);
lean_ctor_set(x_146, 3, x_150);
x_103 = x_147;
x_104 = x_146;
goto block_141;
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_151 = lean_ctor_get(x_146, 0);
x_152 = lean_ctor_get(x_146, 1);
x_153 = lean_ctor_get(x_146, 2);
x_154 = lean_ctor_get(x_146, 3);
x_155 = lean_ctor_get(x_146, 4);
x_156 = lean_ctor_get(x_146, 5);
x_157 = lean_ctor_get(x_146, 6);
x_158 = lean_ctor_get(x_146, 7);
x_159 = lean_ctor_get(x_146, 8);
lean_inc(x_159);
lean_inc(x_158);
lean_inc(x_157);
lean_inc(x_156);
lean_inc(x_155);
lean_inc(x_154);
lean_inc(x_153);
lean_inc(x_152);
lean_inc(x_151);
lean_dec(x_146);
lean_inc(x_147);
x_160 = l_Std_HashMapImp_insert___at_Lean_Closure_visitExpr___spec__3(x_154, x_101, x_147);
x_161 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_161, 0, x_151);
lean_ctor_set(x_161, 1, x_152);
lean_ctor_set(x_161, 2, x_153);
lean_ctor_set(x_161, 3, x_160);
lean_ctor_set(x_161, 4, x_155);
lean_ctor_set(x_161, 5, x_156);
lean_ctor_set(x_161, 6, x_157);
lean_ctor_set(x_161, 7, x_158);
lean_ctor_set(x_161, 8, x_159);
x_103 = x_147;
x_104 = x_161;
goto block_141;
}
}
else
{
uint8_t x_162; 
lean_dec(x_102);
lean_dec(x_101);
lean_dec(x_100);
lean_dec(x_2);
x_162 = !lean_is_exclusive(x_145);
if (x_162 == 0)
{
return x_145;
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_163 = lean_ctor_get(x_145, 0);
x_164 = lean_ctor_get(x_145, 1);
lean_inc(x_164);
lean_inc(x_163);
lean_dec(x_145);
x_165 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_165, 0, x_163);
lean_ctor_set(x_165, 1, x_164);
return x_165;
}
}
}
else
{
lean_object* x_166; 
lean_dec(x_101);
x_166 = lean_ctor_get(x_144, 0);
lean_inc(x_166);
lean_dec(x_144);
x_103 = x_166;
x_104 = x_3;
goto block_141;
}
}
}
}
}
case 2:
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_264; lean_object* x_265; 
x_226 = lean_ctor_get(x_1, 0);
lean_inc(x_226);
x_264 = lean_ctor_get(x_2, 0);
lean_inc(x_264);
lean_inc(x_226);
lean_inc(x_264);
x_265 = lean_metavar_ctx_find_decl(x_264, x_226);
if (lean_obj_tag(x_265) == 0)
{
lean_object* x_266; lean_object* x_267; 
lean_dec(x_264);
lean_dec(x_226);
lean_dec(x_2);
lean_dec(x_1);
x_266 = l_Lean_MetavarContext_getDecl___closed__2;
x_267 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_267, 0, x_266);
lean_ctor_set(x_267, 1, x_3);
return x_267;
}
else
{
lean_object* x_268; lean_object* x_269; 
x_268 = lean_ctor_get(x_265, 0);
lean_inc(x_268);
lean_dec(x_265);
x_269 = lean_metavar_ctx_get_expr_assignment(x_264, x_226);
if (lean_obj_tag(x_269) == 0)
{
lean_object* x_270; lean_object* x_271; uint8_t x_297; 
x_270 = lean_ctor_get(x_268, 2);
lean_inc(x_270);
lean_dec(x_268);
x_297 = l_Lean_Expr_hasLevelParam(x_270);
if (x_297 == 0)
{
uint8_t x_298; 
x_298 = l_Lean_Expr_hasFVar(x_270);
if (x_298 == 0)
{
uint8_t x_299; 
x_299 = l_Lean_Expr_hasMVar(x_270);
if (x_299 == 0)
{
x_227 = x_270;
x_228 = x_3;
goto block_263;
}
else
{
lean_object* x_300; 
x_300 = lean_box(0);
x_271 = x_300;
goto block_296;
}
}
else
{
lean_object* x_301; 
x_301 = lean_box(0);
x_271 = x_301;
goto block_296;
}
}
else
{
lean_object* x_302; 
x_302 = lean_box(0);
x_271 = x_302;
goto block_296;
}
block_296:
{
lean_object* x_272; lean_object* x_273; 
lean_dec(x_271);
x_272 = lean_ctor_get(x_3, 3);
lean_inc(x_272);
x_273 = l_Std_HashMapImp_find_x3f___at_Lean_Closure_visitExpr___spec__1(x_272, x_270);
lean_dec(x_272);
if (lean_obj_tag(x_273) == 0)
{
lean_object* x_274; 
lean_inc(x_2);
lean_inc(x_270);
x_274 = l_Lean_Closure_collectExprAux___main(x_270, x_2, x_3);
if (lean_obj_tag(x_274) == 0)
{
lean_object* x_275; lean_object* x_276; uint8_t x_277; 
x_275 = lean_ctor_get(x_274, 1);
lean_inc(x_275);
x_276 = lean_ctor_get(x_274, 0);
lean_inc(x_276);
lean_dec(x_274);
x_277 = !lean_is_exclusive(x_275);
if (x_277 == 0)
{
lean_object* x_278; lean_object* x_279; 
x_278 = lean_ctor_get(x_275, 3);
lean_inc(x_276);
x_279 = l_Std_HashMapImp_insert___at_Lean_Closure_visitExpr___spec__3(x_278, x_270, x_276);
lean_ctor_set(x_275, 3, x_279);
x_227 = x_276;
x_228 = x_275;
goto block_263;
}
else
{
lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; 
x_280 = lean_ctor_get(x_275, 0);
x_281 = lean_ctor_get(x_275, 1);
x_282 = lean_ctor_get(x_275, 2);
x_283 = lean_ctor_get(x_275, 3);
x_284 = lean_ctor_get(x_275, 4);
x_285 = lean_ctor_get(x_275, 5);
x_286 = lean_ctor_get(x_275, 6);
x_287 = lean_ctor_get(x_275, 7);
x_288 = lean_ctor_get(x_275, 8);
lean_inc(x_288);
lean_inc(x_287);
lean_inc(x_286);
lean_inc(x_285);
lean_inc(x_284);
lean_inc(x_283);
lean_inc(x_282);
lean_inc(x_281);
lean_inc(x_280);
lean_dec(x_275);
lean_inc(x_276);
x_289 = l_Std_HashMapImp_insert___at_Lean_Closure_visitExpr___spec__3(x_283, x_270, x_276);
x_290 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_290, 0, x_280);
lean_ctor_set(x_290, 1, x_281);
lean_ctor_set(x_290, 2, x_282);
lean_ctor_set(x_290, 3, x_289);
lean_ctor_set(x_290, 4, x_284);
lean_ctor_set(x_290, 5, x_285);
lean_ctor_set(x_290, 6, x_286);
lean_ctor_set(x_290, 7, x_287);
lean_ctor_set(x_290, 8, x_288);
x_227 = x_276;
x_228 = x_290;
goto block_263;
}
}
else
{
uint8_t x_291; 
lean_dec(x_270);
lean_dec(x_2);
lean_dec(x_1);
x_291 = !lean_is_exclusive(x_274);
if (x_291 == 0)
{
return x_274;
}
else
{
lean_object* x_292; lean_object* x_293; lean_object* x_294; 
x_292 = lean_ctor_get(x_274, 0);
x_293 = lean_ctor_get(x_274, 1);
lean_inc(x_293);
lean_inc(x_292);
lean_dec(x_274);
x_294 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_294, 0, x_292);
lean_ctor_set(x_294, 1, x_293);
return x_294;
}
}
}
else
{
lean_object* x_295; 
lean_dec(x_270);
x_295 = lean_ctor_get(x_273, 0);
lean_inc(x_295);
lean_dec(x_273);
x_227 = x_295;
x_228 = x_3;
goto block_263;
}
}
}
else
{
lean_object* x_303; lean_object* x_304; uint8_t x_348; 
lean_dec(x_268);
lean_dec(x_1);
x_303 = lean_ctor_get(x_269, 0);
lean_inc(x_303);
lean_dec(x_269);
x_348 = l_Lean_Expr_hasLevelParam(x_303);
if (x_348 == 0)
{
uint8_t x_349; 
x_349 = l_Lean_Expr_hasFVar(x_303);
if (x_349 == 0)
{
uint8_t x_350; 
x_350 = l_Lean_Expr_hasMVar(x_303);
if (x_350 == 0)
{
lean_object* x_351; 
lean_dec(x_2);
x_351 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_351, 0, x_303);
lean_ctor_set(x_351, 1, x_3);
return x_351;
}
else
{
lean_object* x_352; 
x_352 = lean_box(0);
x_304 = x_352;
goto block_347;
}
}
else
{
lean_object* x_353; 
x_353 = lean_box(0);
x_304 = x_353;
goto block_347;
}
}
else
{
lean_object* x_354; 
x_354 = lean_box(0);
x_304 = x_354;
goto block_347;
}
block_347:
{
lean_object* x_305; lean_object* x_306; 
lean_dec(x_304);
x_305 = lean_ctor_get(x_3, 3);
lean_inc(x_305);
x_306 = l_Std_HashMapImp_find_x3f___at_Lean_Closure_visitExpr___spec__1(x_305, x_303);
lean_dec(x_305);
if (lean_obj_tag(x_306) == 0)
{
lean_object* x_307; 
lean_inc(x_303);
x_307 = l_Lean_Closure_collectExprAux___main(x_303, x_2, x_3);
if (lean_obj_tag(x_307) == 0)
{
uint8_t x_308; 
x_308 = !lean_is_exclusive(x_307);
if (x_308 == 0)
{
lean_object* x_309; uint8_t x_310; 
x_309 = lean_ctor_get(x_307, 1);
x_310 = !lean_is_exclusive(x_309);
if (x_310 == 0)
{
lean_object* x_311; lean_object* x_312; lean_object* x_313; 
x_311 = lean_ctor_get(x_307, 0);
x_312 = lean_ctor_get(x_309, 3);
lean_inc(x_311);
x_313 = l_Std_HashMapImp_insert___at_Lean_Closure_visitExpr___spec__3(x_312, x_303, x_311);
lean_ctor_set(x_309, 3, x_313);
return x_307;
}
else
{
lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; 
x_314 = lean_ctor_get(x_307, 0);
x_315 = lean_ctor_get(x_309, 0);
x_316 = lean_ctor_get(x_309, 1);
x_317 = lean_ctor_get(x_309, 2);
x_318 = lean_ctor_get(x_309, 3);
x_319 = lean_ctor_get(x_309, 4);
x_320 = lean_ctor_get(x_309, 5);
x_321 = lean_ctor_get(x_309, 6);
x_322 = lean_ctor_get(x_309, 7);
x_323 = lean_ctor_get(x_309, 8);
lean_inc(x_323);
lean_inc(x_322);
lean_inc(x_321);
lean_inc(x_320);
lean_inc(x_319);
lean_inc(x_318);
lean_inc(x_317);
lean_inc(x_316);
lean_inc(x_315);
lean_dec(x_309);
lean_inc(x_314);
x_324 = l_Std_HashMapImp_insert___at_Lean_Closure_visitExpr___spec__3(x_318, x_303, x_314);
x_325 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_325, 0, x_315);
lean_ctor_set(x_325, 1, x_316);
lean_ctor_set(x_325, 2, x_317);
lean_ctor_set(x_325, 3, x_324);
lean_ctor_set(x_325, 4, x_319);
lean_ctor_set(x_325, 5, x_320);
lean_ctor_set(x_325, 6, x_321);
lean_ctor_set(x_325, 7, x_322);
lean_ctor_set(x_325, 8, x_323);
lean_ctor_set(x_307, 1, x_325);
return x_307;
}
}
else
{
lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; 
x_326 = lean_ctor_get(x_307, 1);
x_327 = lean_ctor_get(x_307, 0);
lean_inc(x_326);
lean_inc(x_327);
lean_dec(x_307);
x_328 = lean_ctor_get(x_326, 0);
lean_inc(x_328);
x_329 = lean_ctor_get(x_326, 1);
lean_inc(x_329);
x_330 = lean_ctor_get(x_326, 2);
lean_inc(x_330);
x_331 = lean_ctor_get(x_326, 3);
lean_inc(x_331);
x_332 = lean_ctor_get(x_326, 4);
lean_inc(x_332);
x_333 = lean_ctor_get(x_326, 5);
lean_inc(x_333);
x_334 = lean_ctor_get(x_326, 6);
lean_inc(x_334);
x_335 = lean_ctor_get(x_326, 7);
lean_inc(x_335);
x_336 = lean_ctor_get(x_326, 8);
lean_inc(x_336);
if (lean_is_exclusive(x_326)) {
 lean_ctor_release(x_326, 0);
 lean_ctor_release(x_326, 1);
 lean_ctor_release(x_326, 2);
 lean_ctor_release(x_326, 3);
 lean_ctor_release(x_326, 4);
 lean_ctor_release(x_326, 5);
 lean_ctor_release(x_326, 6);
 lean_ctor_release(x_326, 7);
 lean_ctor_release(x_326, 8);
 x_337 = x_326;
} else {
 lean_dec_ref(x_326);
 x_337 = lean_box(0);
}
lean_inc(x_327);
x_338 = l_Std_HashMapImp_insert___at_Lean_Closure_visitExpr___spec__3(x_331, x_303, x_327);
if (lean_is_scalar(x_337)) {
 x_339 = lean_alloc_ctor(0, 9, 0);
} else {
 x_339 = x_337;
}
lean_ctor_set(x_339, 0, x_328);
lean_ctor_set(x_339, 1, x_329);
lean_ctor_set(x_339, 2, x_330);
lean_ctor_set(x_339, 3, x_338);
lean_ctor_set(x_339, 4, x_332);
lean_ctor_set(x_339, 5, x_333);
lean_ctor_set(x_339, 6, x_334);
lean_ctor_set(x_339, 7, x_335);
lean_ctor_set(x_339, 8, x_336);
x_340 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_340, 0, x_327);
lean_ctor_set(x_340, 1, x_339);
return x_340;
}
}
else
{
uint8_t x_341; 
lean_dec(x_303);
x_341 = !lean_is_exclusive(x_307);
if (x_341 == 0)
{
return x_307;
}
else
{
lean_object* x_342; lean_object* x_343; lean_object* x_344; 
x_342 = lean_ctor_get(x_307, 0);
x_343 = lean_ctor_get(x_307, 1);
lean_inc(x_343);
lean_inc(x_342);
lean_dec(x_307);
x_344 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_344, 0, x_342);
lean_ctor_set(x_344, 1, x_343);
return x_344;
}
}
}
else
{
lean_object* x_345; lean_object* x_346; 
lean_dec(x_303);
lean_dec(x_2);
x_345 = lean_ctor_get(x_306, 0);
lean_inc(x_345);
lean_dec(x_306);
x_346 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_346, 0, x_345);
lean_ctor_set(x_346, 1, x_3);
return x_346;
}
}
}
}
block_263:
{
lean_object* x_229; uint8_t x_230; lean_object* x_231; uint8_t x_232; 
x_229 = lean_box(0);
x_230 = 0;
x_231 = l_Lean_Closure_mkLocalDecl(x_229, x_227, x_230, x_2, x_228);
lean_dec(x_2);
x_232 = !lean_is_exclusive(x_231);
if (x_232 == 0)
{
lean_object* x_233; uint8_t x_234; 
x_233 = lean_ctor_get(x_231, 1);
x_234 = !lean_is_exclusive(x_233);
if (x_234 == 0)
{
lean_object* x_235; lean_object* x_236; 
x_235 = lean_ctor_get(x_233, 8);
x_236 = lean_array_push(x_235, x_1);
lean_ctor_set(x_233, 8, x_236);
return x_231;
}
else
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; 
x_237 = lean_ctor_get(x_233, 0);
x_238 = lean_ctor_get(x_233, 1);
x_239 = lean_ctor_get(x_233, 2);
x_240 = lean_ctor_get(x_233, 3);
x_241 = lean_ctor_get(x_233, 4);
x_242 = lean_ctor_get(x_233, 5);
x_243 = lean_ctor_get(x_233, 6);
x_244 = lean_ctor_get(x_233, 7);
x_245 = lean_ctor_get(x_233, 8);
lean_inc(x_245);
lean_inc(x_244);
lean_inc(x_243);
lean_inc(x_242);
lean_inc(x_241);
lean_inc(x_240);
lean_inc(x_239);
lean_inc(x_238);
lean_inc(x_237);
lean_dec(x_233);
x_246 = lean_array_push(x_245, x_1);
x_247 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_247, 0, x_237);
lean_ctor_set(x_247, 1, x_238);
lean_ctor_set(x_247, 2, x_239);
lean_ctor_set(x_247, 3, x_240);
lean_ctor_set(x_247, 4, x_241);
lean_ctor_set(x_247, 5, x_242);
lean_ctor_set(x_247, 6, x_243);
lean_ctor_set(x_247, 7, x_244);
lean_ctor_set(x_247, 8, x_246);
lean_ctor_set(x_231, 1, x_247);
return x_231;
}
}
else
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; 
x_248 = lean_ctor_get(x_231, 1);
x_249 = lean_ctor_get(x_231, 0);
lean_inc(x_248);
lean_inc(x_249);
lean_dec(x_231);
x_250 = lean_ctor_get(x_248, 0);
lean_inc(x_250);
x_251 = lean_ctor_get(x_248, 1);
lean_inc(x_251);
x_252 = lean_ctor_get(x_248, 2);
lean_inc(x_252);
x_253 = lean_ctor_get(x_248, 3);
lean_inc(x_253);
x_254 = lean_ctor_get(x_248, 4);
lean_inc(x_254);
x_255 = lean_ctor_get(x_248, 5);
lean_inc(x_255);
x_256 = lean_ctor_get(x_248, 6);
lean_inc(x_256);
x_257 = lean_ctor_get(x_248, 7);
lean_inc(x_257);
x_258 = lean_ctor_get(x_248, 8);
lean_inc(x_258);
if (lean_is_exclusive(x_248)) {
 lean_ctor_release(x_248, 0);
 lean_ctor_release(x_248, 1);
 lean_ctor_release(x_248, 2);
 lean_ctor_release(x_248, 3);
 lean_ctor_release(x_248, 4);
 lean_ctor_release(x_248, 5);
 lean_ctor_release(x_248, 6);
 lean_ctor_release(x_248, 7);
 lean_ctor_release(x_248, 8);
 x_259 = x_248;
} else {
 lean_dec_ref(x_248);
 x_259 = lean_box(0);
}
x_260 = lean_array_push(x_258, x_1);
if (lean_is_scalar(x_259)) {
 x_261 = lean_alloc_ctor(0, 9, 0);
} else {
 x_261 = x_259;
}
lean_ctor_set(x_261, 0, x_250);
lean_ctor_set(x_261, 1, x_251);
lean_ctor_set(x_261, 2, x_252);
lean_ctor_set(x_261, 3, x_253);
lean_ctor_set(x_261, 4, x_254);
lean_ctor_set(x_261, 5, x_255);
lean_ctor_set(x_261, 6, x_256);
lean_ctor_set(x_261, 7, x_257);
lean_ctor_set(x_261, 8, x_260);
x_262 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_262, 0, x_249);
lean_ctor_set(x_262, 1, x_261);
return x_262;
}
}
}
case 3:
{
lean_object* x_355; lean_object* x_356; uint8_t x_357; 
x_355 = lean_ctor_get(x_1, 0);
lean_inc(x_355);
x_356 = l_Lean_Closure_collectLevel(x_355, x_2, x_3);
x_357 = !lean_is_exclusive(x_356);
if (x_357 == 0)
{
lean_object* x_358; lean_object* x_359; 
x_358 = lean_ctor_get(x_356, 0);
x_359 = lean_expr_update_sort(x_1, x_358);
lean_ctor_set(x_356, 0, x_359);
return x_356;
}
else
{
lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; 
x_360 = lean_ctor_get(x_356, 0);
x_361 = lean_ctor_get(x_356, 1);
lean_inc(x_361);
lean_inc(x_360);
lean_dec(x_356);
x_362 = lean_expr_update_sort(x_1, x_360);
x_363 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_363, 0, x_362);
lean_ctor_set(x_363, 1, x_361);
return x_363;
}
}
case 4:
{
lean_object* x_364; lean_object* x_365; uint8_t x_366; 
x_364 = lean_ctor_get(x_1, 1);
lean_inc(x_364);
x_365 = l_List_mapM___main___at_Lean_Closure_collectExprAux___main___spec__1(x_364, x_2, x_3);
x_366 = !lean_is_exclusive(x_365);
if (x_366 == 0)
{
lean_object* x_367; lean_object* x_368; 
x_367 = lean_ctor_get(x_365, 0);
x_368 = lean_expr_update_const(x_1, x_367);
lean_ctor_set(x_365, 0, x_368);
return x_365;
}
else
{
lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; 
x_369 = lean_ctor_get(x_365, 0);
x_370 = lean_ctor_get(x_365, 1);
lean_inc(x_370);
lean_inc(x_369);
lean_dec(x_365);
x_371 = lean_expr_update_const(x_1, x_369);
x_372 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_372, 0, x_371);
lean_ctor_set(x_372, 1, x_370);
return x_372;
}
}
case 5:
{
lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_419; uint8_t x_445; 
x_373 = lean_ctor_get(x_1, 0);
lean_inc(x_373);
x_374 = lean_ctor_get(x_1, 1);
lean_inc(x_374);
x_445 = l_Lean_Expr_hasLevelParam(x_373);
if (x_445 == 0)
{
uint8_t x_446; 
x_446 = l_Lean_Expr_hasFVar(x_373);
if (x_446 == 0)
{
uint8_t x_447; 
x_447 = l_Lean_Expr_hasMVar(x_373);
if (x_447 == 0)
{
x_375 = x_373;
x_376 = x_3;
goto block_418;
}
else
{
lean_object* x_448; 
x_448 = lean_box(0);
x_419 = x_448;
goto block_444;
}
}
else
{
lean_object* x_449; 
x_449 = lean_box(0);
x_419 = x_449;
goto block_444;
}
}
else
{
lean_object* x_450; 
x_450 = lean_box(0);
x_419 = x_450;
goto block_444;
}
block_418:
{
lean_object* x_377; lean_object* x_378; lean_object* x_386; uint8_t x_412; 
x_412 = l_Lean_Expr_hasLevelParam(x_374);
if (x_412 == 0)
{
uint8_t x_413; 
x_413 = l_Lean_Expr_hasFVar(x_374);
if (x_413 == 0)
{
uint8_t x_414; 
x_414 = l_Lean_Expr_hasMVar(x_374);
if (x_414 == 0)
{
lean_dec(x_2);
x_377 = x_374;
x_378 = x_376;
goto block_385;
}
else
{
lean_object* x_415; 
x_415 = lean_box(0);
x_386 = x_415;
goto block_411;
}
}
else
{
lean_object* x_416; 
x_416 = lean_box(0);
x_386 = x_416;
goto block_411;
}
}
else
{
lean_object* x_417; 
x_417 = lean_box(0);
x_386 = x_417;
goto block_411;
}
block_385:
{
if (lean_obj_tag(x_1) == 5)
{
lean_object* x_379; lean_object* x_380; 
x_379 = lean_expr_update_app(x_1, x_375, x_377);
x_380 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_380, 0, x_379);
lean_ctor_set(x_380, 1, x_378);
return x_380;
}
else
{
lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; 
lean_dec(x_377);
lean_dec(x_375);
lean_dec(x_1);
x_381 = l_Lean_Expr_Inhabited;
x_382 = l_Lean_Expr_updateApp_x21___closed__1;
x_383 = lean_panic_fn(x_381, x_382);
x_384 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_384, 0, x_383);
lean_ctor_set(x_384, 1, x_378);
return x_384;
}
}
block_411:
{
lean_object* x_387; lean_object* x_388; 
lean_dec(x_386);
x_387 = lean_ctor_get(x_376, 3);
lean_inc(x_387);
x_388 = l_Std_HashMapImp_find_x3f___at_Lean_Closure_visitExpr___spec__1(x_387, x_374);
lean_dec(x_387);
if (lean_obj_tag(x_388) == 0)
{
lean_object* x_389; 
lean_inc(x_374);
x_389 = l_Lean_Closure_collectExprAux___main(x_374, x_2, x_376);
if (lean_obj_tag(x_389) == 0)
{
lean_object* x_390; lean_object* x_391; uint8_t x_392; 
x_390 = lean_ctor_get(x_389, 1);
lean_inc(x_390);
x_391 = lean_ctor_get(x_389, 0);
lean_inc(x_391);
lean_dec(x_389);
x_392 = !lean_is_exclusive(x_390);
if (x_392 == 0)
{
lean_object* x_393; lean_object* x_394; 
x_393 = lean_ctor_get(x_390, 3);
lean_inc(x_391);
x_394 = l_Std_HashMapImp_insert___at_Lean_Closure_visitExpr___spec__3(x_393, x_374, x_391);
lean_ctor_set(x_390, 3, x_394);
x_377 = x_391;
x_378 = x_390;
goto block_385;
}
else
{
lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; 
x_395 = lean_ctor_get(x_390, 0);
x_396 = lean_ctor_get(x_390, 1);
x_397 = lean_ctor_get(x_390, 2);
x_398 = lean_ctor_get(x_390, 3);
x_399 = lean_ctor_get(x_390, 4);
x_400 = lean_ctor_get(x_390, 5);
x_401 = lean_ctor_get(x_390, 6);
x_402 = lean_ctor_get(x_390, 7);
x_403 = lean_ctor_get(x_390, 8);
lean_inc(x_403);
lean_inc(x_402);
lean_inc(x_401);
lean_inc(x_400);
lean_inc(x_399);
lean_inc(x_398);
lean_inc(x_397);
lean_inc(x_396);
lean_inc(x_395);
lean_dec(x_390);
lean_inc(x_391);
x_404 = l_Std_HashMapImp_insert___at_Lean_Closure_visitExpr___spec__3(x_398, x_374, x_391);
x_405 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_405, 0, x_395);
lean_ctor_set(x_405, 1, x_396);
lean_ctor_set(x_405, 2, x_397);
lean_ctor_set(x_405, 3, x_404);
lean_ctor_set(x_405, 4, x_399);
lean_ctor_set(x_405, 5, x_400);
lean_ctor_set(x_405, 6, x_401);
lean_ctor_set(x_405, 7, x_402);
lean_ctor_set(x_405, 8, x_403);
x_377 = x_391;
x_378 = x_405;
goto block_385;
}
}
else
{
uint8_t x_406; 
lean_dec(x_375);
lean_dec(x_374);
lean_dec(x_1);
x_406 = !lean_is_exclusive(x_389);
if (x_406 == 0)
{
return x_389;
}
else
{
lean_object* x_407; lean_object* x_408; lean_object* x_409; 
x_407 = lean_ctor_get(x_389, 0);
x_408 = lean_ctor_get(x_389, 1);
lean_inc(x_408);
lean_inc(x_407);
lean_dec(x_389);
x_409 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_409, 0, x_407);
lean_ctor_set(x_409, 1, x_408);
return x_409;
}
}
}
else
{
lean_object* x_410; 
lean_dec(x_374);
lean_dec(x_2);
x_410 = lean_ctor_get(x_388, 0);
lean_inc(x_410);
lean_dec(x_388);
x_377 = x_410;
x_378 = x_376;
goto block_385;
}
}
}
block_444:
{
lean_object* x_420; lean_object* x_421; 
lean_dec(x_419);
x_420 = lean_ctor_get(x_3, 3);
lean_inc(x_420);
x_421 = l_Std_HashMapImp_find_x3f___at_Lean_Closure_visitExpr___spec__1(x_420, x_373);
lean_dec(x_420);
if (lean_obj_tag(x_421) == 0)
{
lean_object* x_422; 
lean_inc(x_2);
lean_inc(x_373);
x_422 = l_Lean_Closure_collectExprAux___main(x_373, x_2, x_3);
if (lean_obj_tag(x_422) == 0)
{
lean_object* x_423; lean_object* x_424; uint8_t x_425; 
x_423 = lean_ctor_get(x_422, 1);
lean_inc(x_423);
x_424 = lean_ctor_get(x_422, 0);
lean_inc(x_424);
lean_dec(x_422);
x_425 = !lean_is_exclusive(x_423);
if (x_425 == 0)
{
lean_object* x_426; lean_object* x_427; 
x_426 = lean_ctor_get(x_423, 3);
lean_inc(x_424);
x_427 = l_Std_HashMapImp_insert___at_Lean_Closure_visitExpr___spec__3(x_426, x_373, x_424);
lean_ctor_set(x_423, 3, x_427);
x_375 = x_424;
x_376 = x_423;
goto block_418;
}
else
{
lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; 
x_428 = lean_ctor_get(x_423, 0);
x_429 = lean_ctor_get(x_423, 1);
x_430 = lean_ctor_get(x_423, 2);
x_431 = lean_ctor_get(x_423, 3);
x_432 = lean_ctor_get(x_423, 4);
x_433 = lean_ctor_get(x_423, 5);
x_434 = lean_ctor_get(x_423, 6);
x_435 = lean_ctor_get(x_423, 7);
x_436 = lean_ctor_get(x_423, 8);
lean_inc(x_436);
lean_inc(x_435);
lean_inc(x_434);
lean_inc(x_433);
lean_inc(x_432);
lean_inc(x_431);
lean_inc(x_430);
lean_inc(x_429);
lean_inc(x_428);
lean_dec(x_423);
lean_inc(x_424);
x_437 = l_Std_HashMapImp_insert___at_Lean_Closure_visitExpr___spec__3(x_431, x_373, x_424);
x_438 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_438, 0, x_428);
lean_ctor_set(x_438, 1, x_429);
lean_ctor_set(x_438, 2, x_430);
lean_ctor_set(x_438, 3, x_437);
lean_ctor_set(x_438, 4, x_432);
lean_ctor_set(x_438, 5, x_433);
lean_ctor_set(x_438, 6, x_434);
lean_ctor_set(x_438, 7, x_435);
lean_ctor_set(x_438, 8, x_436);
x_375 = x_424;
x_376 = x_438;
goto block_418;
}
}
else
{
uint8_t x_439; 
lean_dec(x_374);
lean_dec(x_373);
lean_dec(x_2);
lean_dec(x_1);
x_439 = !lean_is_exclusive(x_422);
if (x_439 == 0)
{
return x_422;
}
else
{
lean_object* x_440; lean_object* x_441; lean_object* x_442; 
x_440 = lean_ctor_get(x_422, 0);
x_441 = lean_ctor_get(x_422, 1);
lean_inc(x_441);
lean_inc(x_440);
lean_dec(x_422);
x_442 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_442, 0, x_440);
lean_ctor_set(x_442, 1, x_441);
return x_442;
}
}
}
else
{
lean_object* x_443; 
lean_dec(x_373);
x_443 = lean_ctor_get(x_421, 0);
lean_inc(x_443);
lean_dec(x_421);
x_375 = x_443;
x_376 = x_3;
goto block_418;
}
}
}
case 6:
{
lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_499; uint8_t x_525; 
x_451 = lean_ctor_get(x_1, 1);
lean_inc(x_451);
x_452 = lean_ctor_get(x_1, 2);
lean_inc(x_452);
x_525 = l_Lean_Expr_hasLevelParam(x_451);
if (x_525 == 0)
{
uint8_t x_526; 
x_526 = l_Lean_Expr_hasFVar(x_451);
if (x_526 == 0)
{
uint8_t x_527; 
x_527 = l_Lean_Expr_hasMVar(x_451);
if (x_527 == 0)
{
x_453 = x_451;
x_454 = x_3;
goto block_498;
}
else
{
lean_object* x_528; 
x_528 = lean_box(0);
x_499 = x_528;
goto block_524;
}
}
else
{
lean_object* x_529; 
x_529 = lean_box(0);
x_499 = x_529;
goto block_524;
}
}
else
{
lean_object* x_530; 
x_530 = lean_box(0);
x_499 = x_530;
goto block_524;
}
block_498:
{
lean_object* x_455; lean_object* x_456; lean_object* x_466; uint8_t x_492; 
x_492 = l_Lean_Expr_hasLevelParam(x_452);
if (x_492 == 0)
{
uint8_t x_493; 
x_493 = l_Lean_Expr_hasFVar(x_452);
if (x_493 == 0)
{
uint8_t x_494; 
x_494 = l_Lean_Expr_hasMVar(x_452);
if (x_494 == 0)
{
lean_dec(x_2);
x_455 = x_452;
x_456 = x_454;
goto block_465;
}
else
{
lean_object* x_495; 
x_495 = lean_box(0);
x_466 = x_495;
goto block_491;
}
}
else
{
lean_object* x_496; 
x_496 = lean_box(0);
x_466 = x_496;
goto block_491;
}
}
else
{
lean_object* x_497; 
x_497 = lean_box(0);
x_466 = x_497;
goto block_491;
}
block_465:
{
if (lean_obj_tag(x_1) == 6)
{
uint64_t x_457; uint8_t x_458; lean_object* x_459; lean_object* x_460; 
x_457 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
x_458 = (uint8_t)((x_457 << 24) >> 61);
x_459 = lean_expr_update_lambda(x_1, x_458, x_453, x_455);
x_460 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_460, 0, x_459);
lean_ctor_set(x_460, 1, x_456);
return x_460;
}
else
{
lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; 
lean_dec(x_455);
lean_dec(x_453);
lean_dec(x_1);
x_461 = l_Lean_Expr_Inhabited;
x_462 = l_Lean_Expr_updateLambdaE_x21___closed__1;
x_463 = lean_panic_fn(x_461, x_462);
x_464 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_464, 0, x_463);
lean_ctor_set(x_464, 1, x_456);
return x_464;
}
}
block_491:
{
lean_object* x_467; lean_object* x_468; 
lean_dec(x_466);
x_467 = lean_ctor_get(x_454, 3);
lean_inc(x_467);
x_468 = l_Std_HashMapImp_find_x3f___at_Lean_Closure_visitExpr___spec__1(x_467, x_452);
lean_dec(x_467);
if (lean_obj_tag(x_468) == 0)
{
lean_object* x_469; 
lean_inc(x_452);
x_469 = l_Lean_Closure_collectExprAux___main(x_452, x_2, x_454);
if (lean_obj_tag(x_469) == 0)
{
lean_object* x_470; lean_object* x_471; uint8_t x_472; 
x_470 = lean_ctor_get(x_469, 1);
lean_inc(x_470);
x_471 = lean_ctor_get(x_469, 0);
lean_inc(x_471);
lean_dec(x_469);
x_472 = !lean_is_exclusive(x_470);
if (x_472 == 0)
{
lean_object* x_473; lean_object* x_474; 
x_473 = lean_ctor_get(x_470, 3);
lean_inc(x_471);
x_474 = l_Std_HashMapImp_insert___at_Lean_Closure_visitExpr___spec__3(x_473, x_452, x_471);
lean_ctor_set(x_470, 3, x_474);
x_455 = x_471;
x_456 = x_470;
goto block_465;
}
else
{
lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; 
x_475 = lean_ctor_get(x_470, 0);
x_476 = lean_ctor_get(x_470, 1);
x_477 = lean_ctor_get(x_470, 2);
x_478 = lean_ctor_get(x_470, 3);
x_479 = lean_ctor_get(x_470, 4);
x_480 = lean_ctor_get(x_470, 5);
x_481 = lean_ctor_get(x_470, 6);
x_482 = lean_ctor_get(x_470, 7);
x_483 = lean_ctor_get(x_470, 8);
lean_inc(x_483);
lean_inc(x_482);
lean_inc(x_481);
lean_inc(x_480);
lean_inc(x_479);
lean_inc(x_478);
lean_inc(x_477);
lean_inc(x_476);
lean_inc(x_475);
lean_dec(x_470);
lean_inc(x_471);
x_484 = l_Std_HashMapImp_insert___at_Lean_Closure_visitExpr___spec__3(x_478, x_452, x_471);
x_485 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_485, 0, x_475);
lean_ctor_set(x_485, 1, x_476);
lean_ctor_set(x_485, 2, x_477);
lean_ctor_set(x_485, 3, x_484);
lean_ctor_set(x_485, 4, x_479);
lean_ctor_set(x_485, 5, x_480);
lean_ctor_set(x_485, 6, x_481);
lean_ctor_set(x_485, 7, x_482);
lean_ctor_set(x_485, 8, x_483);
x_455 = x_471;
x_456 = x_485;
goto block_465;
}
}
else
{
uint8_t x_486; 
lean_dec(x_453);
lean_dec(x_452);
lean_dec(x_1);
x_486 = !lean_is_exclusive(x_469);
if (x_486 == 0)
{
return x_469;
}
else
{
lean_object* x_487; lean_object* x_488; lean_object* x_489; 
x_487 = lean_ctor_get(x_469, 0);
x_488 = lean_ctor_get(x_469, 1);
lean_inc(x_488);
lean_inc(x_487);
lean_dec(x_469);
x_489 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_489, 0, x_487);
lean_ctor_set(x_489, 1, x_488);
return x_489;
}
}
}
else
{
lean_object* x_490; 
lean_dec(x_452);
lean_dec(x_2);
x_490 = lean_ctor_get(x_468, 0);
lean_inc(x_490);
lean_dec(x_468);
x_455 = x_490;
x_456 = x_454;
goto block_465;
}
}
}
block_524:
{
lean_object* x_500; lean_object* x_501; 
lean_dec(x_499);
x_500 = lean_ctor_get(x_3, 3);
lean_inc(x_500);
x_501 = l_Std_HashMapImp_find_x3f___at_Lean_Closure_visitExpr___spec__1(x_500, x_451);
lean_dec(x_500);
if (lean_obj_tag(x_501) == 0)
{
lean_object* x_502; 
lean_inc(x_2);
lean_inc(x_451);
x_502 = l_Lean_Closure_collectExprAux___main(x_451, x_2, x_3);
if (lean_obj_tag(x_502) == 0)
{
lean_object* x_503; lean_object* x_504; uint8_t x_505; 
x_503 = lean_ctor_get(x_502, 1);
lean_inc(x_503);
x_504 = lean_ctor_get(x_502, 0);
lean_inc(x_504);
lean_dec(x_502);
x_505 = !lean_is_exclusive(x_503);
if (x_505 == 0)
{
lean_object* x_506; lean_object* x_507; 
x_506 = lean_ctor_get(x_503, 3);
lean_inc(x_504);
x_507 = l_Std_HashMapImp_insert___at_Lean_Closure_visitExpr___spec__3(x_506, x_451, x_504);
lean_ctor_set(x_503, 3, x_507);
x_453 = x_504;
x_454 = x_503;
goto block_498;
}
else
{
lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; 
x_508 = lean_ctor_get(x_503, 0);
x_509 = lean_ctor_get(x_503, 1);
x_510 = lean_ctor_get(x_503, 2);
x_511 = lean_ctor_get(x_503, 3);
x_512 = lean_ctor_get(x_503, 4);
x_513 = lean_ctor_get(x_503, 5);
x_514 = lean_ctor_get(x_503, 6);
x_515 = lean_ctor_get(x_503, 7);
x_516 = lean_ctor_get(x_503, 8);
lean_inc(x_516);
lean_inc(x_515);
lean_inc(x_514);
lean_inc(x_513);
lean_inc(x_512);
lean_inc(x_511);
lean_inc(x_510);
lean_inc(x_509);
lean_inc(x_508);
lean_dec(x_503);
lean_inc(x_504);
x_517 = l_Std_HashMapImp_insert___at_Lean_Closure_visitExpr___spec__3(x_511, x_451, x_504);
x_518 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_518, 0, x_508);
lean_ctor_set(x_518, 1, x_509);
lean_ctor_set(x_518, 2, x_510);
lean_ctor_set(x_518, 3, x_517);
lean_ctor_set(x_518, 4, x_512);
lean_ctor_set(x_518, 5, x_513);
lean_ctor_set(x_518, 6, x_514);
lean_ctor_set(x_518, 7, x_515);
lean_ctor_set(x_518, 8, x_516);
x_453 = x_504;
x_454 = x_518;
goto block_498;
}
}
else
{
uint8_t x_519; 
lean_dec(x_452);
lean_dec(x_451);
lean_dec(x_2);
lean_dec(x_1);
x_519 = !lean_is_exclusive(x_502);
if (x_519 == 0)
{
return x_502;
}
else
{
lean_object* x_520; lean_object* x_521; lean_object* x_522; 
x_520 = lean_ctor_get(x_502, 0);
x_521 = lean_ctor_get(x_502, 1);
lean_inc(x_521);
lean_inc(x_520);
lean_dec(x_502);
x_522 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_522, 0, x_520);
lean_ctor_set(x_522, 1, x_521);
return x_522;
}
}
}
else
{
lean_object* x_523; 
lean_dec(x_451);
x_523 = lean_ctor_get(x_501, 0);
lean_inc(x_523);
lean_dec(x_501);
x_453 = x_523;
x_454 = x_3;
goto block_498;
}
}
}
case 7:
{
lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_579; uint8_t x_605; 
x_531 = lean_ctor_get(x_1, 1);
lean_inc(x_531);
x_532 = lean_ctor_get(x_1, 2);
lean_inc(x_532);
x_605 = l_Lean_Expr_hasLevelParam(x_531);
if (x_605 == 0)
{
uint8_t x_606; 
x_606 = l_Lean_Expr_hasFVar(x_531);
if (x_606 == 0)
{
uint8_t x_607; 
x_607 = l_Lean_Expr_hasMVar(x_531);
if (x_607 == 0)
{
x_533 = x_531;
x_534 = x_3;
goto block_578;
}
else
{
lean_object* x_608; 
x_608 = lean_box(0);
x_579 = x_608;
goto block_604;
}
}
else
{
lean_object* x_609; 
x_609 = lean_box(0);
x_579 = x_609;
goto block_604;
}
}
else
{
lean_object* x_610; 
x_610 = lean_box(0);
x_579 = x_610;
goto block_604;
}
block_578:
{
lean_object* x_535; lean_object* x_536; lean_object* x_546; uint8_t x_572; 
x_572 = l_Lean_Expr_hasLevelParam(x_532);
if (x_572 == 0)
{
uint8_t x_573; 
x_573 = l_Lean_Expr_hasFVar(x_532);
if (x_573 == 0)
{
uint8_t x_574; 
x_574 = l_Lean_Expr_hasMVar(x_532);
if (x_574 == 0)
{
lean_dec(x_2);
x_535 = x_532;
x_536 = x_534;
goto block_545;
}
else
{
lean_object* x_575; 
x_575 = lean_box(0);
x_546 = x_575;
goto block_571;
}
}
else
{
lean_object* x_576; 
x_576 = lean_box(0);
x_546 = x_576;
goto block_571;
}
}
else
{
lean_object* x_577; 
x_577 = lean_box(0);
x_546 = x_577;
goto block_571;
}
block_545:
{
if (lean_obj_tag(x_1) == 7)
{
uint64_t x_537; uint8_t x_538; lean_object* x_539; lean_object* x_540; 
x_537 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
x_538 = (uint8_t)((x_537 << 24) >> 61);
x_539 = lean_expr_update_forall(x_1, x_538, x_533, x_535);
x_540 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_540, 0, x_539);
lean_ctor_set(x_540, 1, x_536);
return x_540;
}
else
{
lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; 
lean_dec(x_535);
lean_dec(x_533);
lean_dec(x_1);
x_541 = l_Lean_Expr_Inhabited;
x_542 = l_Lean_Expr_updateForallE_x21___closed__1;
x_543 = lean_panic_fn(x_541, x_542);
x_544 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_544, 0, x_543);
lean_ctor_set(x_544, 1, x_536);
return x_544;
}
}
block_571:
{
lean_object* x_547; lean_object* x_548; 
lean_dec(x_546);
x_547 = lean_ctor_get(x_534, 3);
lean_inc(x_547);
x_548 = l_Std_HashMapImp_find_x3f___at_Lean_Closure_visitExpr___spec__1(x_547, x_532);
lean_dec(x_547);
if (lean_obj_tag(x_548) == 0)
{
lean_object* x_549; 
lean_inc(x_532);
x_549 = l_Lean_Closure_collectExprAux___main(x_532, x_2, x_534);
if (lean_obj_tag(x_549) == 0)
{
lean_object* x_550; lean_object* x_551; uint8_t x_552; 
x_550 = lean_ctor_get(x_549, 1);
lean_inc(x_550);
x_551 = lean_ctor_get(x_549, 0);
lean_inc(x_551);
lean_dec(x_549);
x_552 = !lean_is_exclusive(x_550);
if (x_552 == 0)
{
lean_object* x_553; lean_object* x_554; 
x_553 = lean_ctor_get(x_550, 3);
lean_inc(x_551);
x_554 = l_Std_HashMapImp_insert___at_Lean_Closure_visitExpr___spec__3(x_553, x_532, x_551);
lean_ctor_set(x_550, 3, x_554);
x_535 = x_551;
x_536 = x_550;
goto block_545;
}
else
{
lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_565; 
x_555 = lean_ctor_get(x_550, 0);
x_556 = lean_ctor_get(x_550, 1);
x_557 = lean_ctor_get(x_550, 2);
x_558 = lean_ctor_get(x_550, 3);
x_559 = lean_ctor_get(x_550, 4);
x_560 = lean_ctor_get(x_550, 5);
x_561 = lean_ctor_get(x_550, 6);
x_562 = lean_ctor_get(x_550, 7);
x_563 = lean_ctor_get(x_550, 8);
lean_inc(x_563);
lean_inc(x_562);
lean_inc(x_561);
lean_inc(x_560);
lean_inc(x_559);
lean_inc(x_558);
lean_inc(x_557);
lean_inc(x_556);
lean_inc(x_555);
lean_dec(x_550);
lean_inc(x_551);
x_564 = l_Std_HashMapImp_insert___at_Lean_Closure_visitExpr___spec__3(x_558, x_532, x_551);
x_565 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_565, 0, x_555);
lean_ctor_set(x_565, 1, x_556);
lean_ctor_set(x_565, 2, x_557);
lean_ctor_set(x_565, 3, x_564);
lean_ctor_set(x_565, 4, x_559);
lean_ctor_set(x_565, 5, x_560);
lean_ctor_set(x_565, 6, x_561);
lean_ctor_set(x_565, 7, x_562);
lean_ctor_set(x_565, 8, x_563);
x_535 = x_551;
x_536 = x_565;
goto block_545;
}
}
else
{
uint8_t x_566; 
lean_dec(x_533);
lean_dec(x_532);
lean_dec(x_1);
x_566 = !lean_is_exclusive(x_549);
if (x_566 == 0)
{
return x_549;
}
else
{
lean_object* x_567; lean_object* x_568; lean_object* x_569; 
x_567 = lean_ctor_get(x_549, 0);
x_568 = lean_ctor_get(x_549, 1);
lean_inc(x_568);
lean_inc(x_567);
lean_dec(x_549);
x_569 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_569, 0, x_567);
lean_ctor_set(x_569, 1, x_568);
return x_569;
}
}
}
else
{
lean_object* x_570; 
lean_dec(x_532);
lean_dec(x_2);
x_570 = lean_ctor_get(x_548, 0);
lean_inc(x_570);
lean_dec(x_548);
x_535 = x_570;
x_536 = x_534;
goto block_545;
}
}
}
block_604:
{
lean_object* x_580; lean_object* x_581; 
lean_dec(x_579);
x_580 = lean_ctor_get(x_3, 3);
lean_inc(x_580);
x_581 = l_Std_HashMapImp_find_x3f___at_Lean_Closure_visitExpr___spec__1(x_580, x_531);
lean_dec(x_580);
if (lean_obj_tag(x_581) == 0)
{
lean_object* x_582; 
lean_inc(x_2);
lean_inc(x_531);
x_582 = l_Lean_Closure_collectExprAux___main(x_531, x_2, x_3);
if (lean_obj_tag(x_582) == 0)
{
lean_object* x_583; lean_object* x_584; uint8_t x_585; 
x_583 = lean_ctor_get(x_582, 1);
lean_inc(x_583);
x_584 = lean_ctor_get(x_582, 0);
lean_inc(x_584);
lean_dec(x_582);
x_585 = !lean_is_exclusive(x_583);
if (x_585 == 0)
{
lean_object* x_586; lean_object* x_587; 
x_586 = lean_ctor_get(x_583, 3);
lean_inc(x_584);
x_587 = l_Std_HashMapImp_insert___at_Lean_Closure_visitExpr___spec__3(x_586, x_531, x_584);
lean_ctor_set(x_583, 3, x_587);
x_533 = x_584;
x_534 = x_583;
goto block_578;
}
else
{
lean_object* x_588; lean_object* x_589; lean_object* x_590; lean_object* x_591; lean_object* x_592; lean_object* x_593; lean_object* x_594; lean_object* x_595; lean_object* x_596; lean_object* x_597; lean_object* x_598; 
x_588 = lean_ctor_get(x_583, 0);
x_589 = lean_ctor_get(x_583, 1);
x_590 = lean_ctor_get(x_583, 2);
x_591 = lean_ctor_get(x_583, 3);
x_592 = lean_ctor_get(x_583, 4);
x_593 = lean_ctor_get(x_583, 5);
x_594 = lean_ctor_get(x_583, 6);
x_595 = lean_ctor_get(x_583, 7);
x_596 = lean_ctor_get(x_583, 8);
lean_inc(x_596);
lean_inc(x_595);
lean_inc(x_594);
lean_inc(x_593);
lean_inc(x_592);
lean_inc(x_591);
lean_inc(x_590);
lean_inc(x_589);
lean_inc(x_588);
lean_dec(x_583);
lean_inc(x_584);
x_597 = l_Std_HashMapImp_insert___at_Lean_Closure_visitExpr___spec__3(x_591, x_531, x_584);
x_598 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_598, 0, x_588);
lean_ctor_set(x_598, 1, x_589);
lean_ctor_set(x_598, 2, x_590);
lean_ctor_set(x_598, 3, x_597);
lean_ctor_set(x_598, 4, x_592);
lean_ctor_set(x_598, 5, x_593);
lean_ctor_set(x_598, 6, x_594);
lean_ctor_set(x_598, 7, x_595);
lean_ctor_set(x_598, 8, x_596);
x_533 = x_584;
x_534 = x_598;
goto block_578;
}
}
else
{
uint8_t x_599; 
lean_dec(x_532);
lean_dec(x_531);
lean_dec(x_2);
lean_dec(x_1);
x_599 = !lean_is_exclusive(x_582);
if (x_599 == 0)
{
return x_582;
}
else
{
lean_object* x_600; lean_object* x_601; lean_object* x_602; 
x_600 = lean_ctor_get(x_582, 0);
x_601 = lean_ctor_get(x_582, 1);
lean_inc(x_601);
lean_inc(x_600);
lean_dec(x_582);
x_602 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_602, 0, x_600);
lean_ctor_set(x_602, 1, x_601);
return x_602;
}
}
}
else
{
lean_object* x_603; 
lean_dec(x_531);
x_603 = lean_ctor_get(x_581, 0);
lean_inc(x_603);
lean_dec(x_581);
x_533 = x_603;
x_534 = x_3;
goto block_578;
}
}
}
case 8:
{
lean_object* x_611; lean_object* x_612; lean_object* x_613; lean_object* x_614; lean_object* x_615; lean_object* x_693; uint8_t x_719; 
x_611 = lean_ctor_get(x_1, 1);
lean_inc(x_611);
x_612 = lean_ctor_get(x_1, 2);
lean_inc(x_612);
x_613 = lean_ctor_get(x_1, 3);
lean_inc(x_613);
x_719 = l_Lean_Expr_hasLevelParam(x_611);
if (x_719 == 0)
{
uint8_t x_720; 
x_720 = l_Lean_Expr_hasFVar(x_611);
if (x_720 == 0)
{
uint8_t x_721; 
x_721 = l_Lean_Expr_hasMVar(x_611);
if (x_721 == 0)
{
x_614 = x_611;
x_615 = x_3;
goto block_692;
}
else
{
lean_object* x_722; 
x_722 = lean_box(0);
x_693 = x_722;
goto block_718;
}
}
else
{
lean_object* x_723; 
x_723 = lean_box(0);
x_693 = x_723;
goto block_718;
}
}
else
{
lean_object* x_724; 
x_724 = lean_box(0);
x_693 = x_724;
goto block_718;
}
block_692:
{
lean_object* x_616; lean_object* x_617; lean_object* x_660; uint8_t x_686; 
x_686 = l_Lean_Expr_hasLevelParam(x_612);
if (x_686 == 0)
{
uint8_t x_687; 
x_687 = l_Lean_Expr_hasFVar(x_612);
if (x_687 == 0)
{
uint8_t x_688; 
x_688 = l_Lean_Expr_hasMVar(x_612);
if (x_688 == 0)
{
x_616 = x_612;
x_617 = x_615;
goto block_659;
}
else
{
lean_object* x_689; 
x_689 = lean_box(0);
x_660 = x_689;
goto block_685;
}
}
else
{
lean_object* x_690; 
x_690 = lean_box(0);
x_660 = x_690;
goto block_685;
}
}
else
{
lean_object* x_691; 
x_691 = lean_box(0);
x_660 = x_691;
goto block_685;
}
block_659:
{
lean_object* x_618; lean_object* x_619; lean_object* x_627; uint8_t x_653; 
x_653 = l_Lean_Expr_hasLevelParam(x_613);
if (x_653 == 0)
{
uint8_t x_654; 
x_654 = l_Lean_Expr_hasFVar(x_613);
if (x_654 == 0)
{
uint8_t x_655; 
x_655 = l_Lean_Expr_hasMVar(x_613);
if (x_655 == 0)
{
lean_dec(x_2);
x_618 = x_613;
x_619 = x_617;
goto block_626;
}
else
{
lean_object* x_656; 
x_656 = lean_box(0);
x_627 = x_656;
goto block_652;
}
}
else
{
lean_object* x_657; 
x_657 = lean_box(0);
x_627 = x_657;
goto block_652;
}
}
else
{
lean_object* x_658; 
x_658 = lean_box(0);
x_627 = x_658;
goto block_652;
}
block_626:
{
if (lean_obj_tag(x_1) == 8)
{
lean_object* x_620; lean_object* x_621; 
x_620 = lean_expr_update_let(x_1, x_614, x_616, x_618);
x_621 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_621, 0, x_620);
lean_ctor_set(x_621, 1, x_619);
return x_621;
}
else
{
lean_object* x_622; lean_object* x_623; lean_object* x_624; lean_object* x_625; 
lean_dec(x_618);
lean_dec(x_616);
lean_dec(x_614);
lean_dec(x_1);
x_622 = l_Lean_Expr_Inhabited;
x_623 = l_Lean_Expr_updateLet_x21___closed__1;
x_624 = lean_panic_fn(x_622, x_623);
x_625 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_625, 0, x_624);
lean_ctor_set(x_625, 1, x_619);
return x_625;
}
}
block_652:
{
lean_object* x_628; lean_object* x_629; 
lean_dec(x_627);
x_628 = lean_ctor_get(x_617, 3);
lean_inc(x_628);
x_629 = l_Std_HashMapImp_find_x3f___at_Lean_Closure_visitExpr___spec__1(x_628, x_613);
lean_dec(x_628);
if (lean_obj_tag(x_629) == 0)
{
lean_object* x_630; 
lean_inc(x_613);
x_630 = l_Lean_Closure_collectExprAux___main(x_613, x_2, x_617);
if (lean_obj_tag(x_630) == 0)
{
lean_object* x_631; lean_object* x_632; uint8_t x_633; 
x_631 = lean_ctor_get(x_630, 1);
lean_inc(x_631);
x_632 = lean_ctor_get(x_630, 0);
lean_inc(x_632);
lean_dec(x_630);
x_633 = !lean_is_exclusive(x_631);
if (x_633 == 0)
{
lean_object* x_634; lean_object* x_635; 
x_634 = lean_ctor_get(x_631, 3);
lean_inc(x_632);
x_635 = l_Std_HashMapImp_insert___at_Lean_Closure_visitExpr___spec__3(x_634, x_613, x_632);
lean_ctor_set(x_631, 3, x_635);
x_618 = x_632;
x_619 = x_631;
goto block_626;
}
else
{
lean_object* x_636; lean_object* x_637; lean_object* x_638; lean_object* x_639; lean_object* x_640; lean_object* x_641; lean_object* x_642; lean_object* x_643; lean_object* x_644; lean_object* x_645; lean_object* x_646; 
x_636 = lean_ctor_get(x_631, 0);
x_637 = lean_ctor_get(x_631, 1);
x_638 = lean_ctor_get(x_631, 2);
x_639 = lean_ctor_get(x_631, 3);
x_640 = lean_ctor_get(x_631, 4);
x_641 = lean_ctor_get(x_631, 5);
x_642 = lean_ctor_get(x_631, 6);
x_643 = lean_ctor_get(x_631, 7);
x_644 = lean_ctor_get(x_631, 8);
lean_inc(x_644);
lean_inc(x_643);
lean_inc(x_642);
lean_inc(x_641);
lean_inc(x_640);
lean_inc(x_639);
lean_inc(x_638);
lean_inc(x_637);
lean_inc(x_636);
lean_dec(x_631);
lean_inc(x_632);
x_645 = l_Std_HashMapImp_insert___at_Lean_Closure_visitExpr___spec__3(x_639, x_613, x_632);
x_646 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_646, 0, x_636);
lean_ctor_set(x_646, 1, x_637);
lean_ctor_set(x_646, 2, x_638);
lean_ctor_set(x_646, 3, x_645);
lean_ctor_set(x_646, 4, x_640);
lean_ctor_set(x_646, 5, x_641);
lean_ctor_set(x_646, 6, x_642);
lean_ctor_set(x_646, 7, x_643);
lean_ctor_set(x_646, 8, x_644);
x_618 = x_632;
x_619 = x_646;
goto block_626;
}
}
else
{
uint8_t x_647; 
lean_dec(x_616);
lean_dec(x_614);
lean_dec(x_613);
lean_dec(x_1);
x_647 = !lean_is_exclusive(x_630);
if (x_647 == 0)
{
return x_630;
}
else
{
lean_object* x_648; lean_object* x_649; lean_object* x_650; 
x_648 = lean_ctor_get(x_630, 0);
x_649 = lean_ctor_get(x_630, 1);
lean_inc(x_649);
lean_inc(x_648);
lean_dec(x_630);
x_650 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_650, 0, x_648);
lean_ctor_set(x_650, 1, x_649);
return x_650;
}
}
}
else
{
lean_object* x_651; 
lean_dec(x_613);
lean_dec(x_2);
x_651 = lean_ctor_get(x_629, 0);
lean_inc(x_651);
lean_dec(x_629);
x_618 = x_651;
x_619 = x_617;
goto block_626;
}
}
}
block_685:
{
lean_object* x_661; lean_object* x_662; 
lean_dec(x_660);
x_661 = lean_ctor_get(x_615, 3);
lean_inc(x_661);
x_662 = l_Std_HashMapImp_find_x3f___at_Lean_Closure_visitExpr___spec__1(x_661, x_612);
lean_dec(x_661);
if (lean_obj_tag(x_662) == 0)
{
lean_object* x_663; 
lean_inc(x_2);
lean_inc(x_612);
x_663 = l_Lean_Closure_collectExprAux___main(x_612, x_2, x_615);
if (lean_obj_tag(x_663) == 0)
{
lean_object* x_664; lean_object* x_665; uint8_t x_666; 
x_664 = lean_ctor_get(x_663, 1);
lean_inc(x_664);
x_665 = lean_ctor_get(x_663, 0);
lean_inc(x_665);
lean_dec(x_663);
x_666 = !lean_is_exclusive(x_664);
if (x_666 == 0)
{
lean_object* x_667; lean_object* x_668; 
x_667 = lean_ctor_get(x_664, 3);
lean_inc(x_665);
x_668 = l_Std_HashMapImp_insert___at_Lean_Closure_visitExpr___spec__3(x_667, x_612, x_665);
lean_ctor_set(x_664, 3, x_668);
x_616 = x_665;
x_617 = x_664;
goto block_659;
}
else
{
lean_object* x_669; lean_object* x_670; lean_object* x_671; lean_object* x_672; lean_object* x_673; lean_object* x_674; lean_object* x_675; lean_object* x_676; lean_object* x_677; lean_object* x_678; lean_object* x_679; 
x_669 = lean_ctor_get(x_664, 0);
x_670 = lean_ctor_get(x_664, 1);
x_671 = lean_ctor_get(x_664, 2);
x_672 = lean_ctor_get(x_664, 3);
x_673 = lean_ctor_get(x_664, 4);
x_674 = lean_ctor_get(x_664, 5);
x_675 = lean_ctor_get(x_664, 6);
x_676 = lean_ctor_get(x_664, 7);
x_677 = lean_ctor_get(x_664, 8);
lean_inc(x_677);
lean_inc(x_676);
lean_inc(x_675);
lean_inc(x_674);
lean_inc(x_673);
lean_inc(x_672);
lean_inc(x_671);
lean_inc(x_670);
lean_inc(x_669);
lean_dec(x_664);
lean_inc(x_665);
x_678 = l_Std_HashMapImp_insert___at_Lean_Closure_visitExpr___spec__3(x_672, x_612, x_665);
x_679 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_679, 0, x_669);
lean_ctor_set(x_679, 1, x_670);
lean_ctor_set(x_679, 2, x_671);
lean_ctor_set(x_679, 3, x_678);
lean_ctor_set(x_679, 4, x_673);
lean_ctor_set(x_679, 5, x_674);
lean_ctor_set(x_679, 6, x_675);
lean_ctor_set(x_679, 7, x_676);
lean_ctor_set(x_679, 8, x_677);
x_616 = x_665;
x_617 = x_679;
goto block_659;
}
}
else
{
uint8_t x_680; 
lean_dec(x_614);
lean_dec(x_613);
lean_dec(x_612);
lean_dec(x_2);
lean_dec(x_1);
x_680 = !lean_is_exclusive(x_663);
if (x_680 == 0)
{
return x_663;
}
else
{
lean_object* x_681; lean_object* x_682; lean_object* x_683; 
x_681 = lean_ctor_get(x_663, 0);
x_682 = lean_ctor_get(x_663, 1);
lean_inc(x_682);
lean_inc(x_681);
lean_dec(x_663);
x_683 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_683, 0, x_681);
lean_ctor_set(x_683, 1, x_682);
return x_683;
}
}
}
else
{
lean_object* x_684; 
lean_dec(x_612);
x_684 = lean_ctor_get(x_662, 0);
lean_inc(x_684);
lean_dec(x_662);
x_616 = x_684;
x_617 = x_615;
goto block_659;
}
}
}
block_718:
{
lean_object* x_694; lean_object* x_695; 
lean_dec(x_693);
x_694 = lean_ctor_get(x_3, 3);
lean_inc(x_694);
x_695 = l_Std_HashMapImp_find_x3f___at_Lean_Closure_visitExpr___spec__1(x_694, x_611);
lean_dec(x_694);
if (lean_obj_tag(x_695) == 0)
{
lean_object* x_696; 
lean_inc(x_2);
lean_inc(x_611);
x_696 = l_Lean_Closure_collectExprAux___main(x_611, x_2, x_3);
if (lean_obj_tag(x_696) == 0)
{
lean_object* x_697; lean_object* x_698; uint8_t x_699; 
x_697 = lean_ctor_get(x_696, 1);
lean_inc(x_697);
x_698 = lean_ctor_get(x_696, 0);
lean_inc(x_698);
lean_dec(x_696);
x_699 = !lean_is_exclusive(x_697);
if (x_699 == 0)
{
lean_object* x_700; lean_object* x_701; 
x_700 = lean_ctor_get(x_697, 3);
lean_inc(x_698);
x_701 = l_Std_HashMapImp_insert___at_Lean_Closure_visitExpr___spec__3(x_700, x_611, x_698);
lean_ctor_set(x_697, 3, x_701);
x_614 = x_698;
x_615 = x_697;
goto block_692;
}
else
{
lean_object* x_702; lean_object* x_703; lean_object* x_704; lean_object* x_705; lean_object* x_706; lean_object* x_707; lean_object* x_708; lean_object* x_709; lean_object* x_710; lean_object* x_711; lean_object* x_712; 
x_702 = lean_ctor_get(x_697, 0);
x_703 = lean_ctor_get(x_697, 1);
x_704 = lean_ctor_get(x_697, 2);
x_705 = lean_ctor_get(x_697, 3);
x_706 = lean_ctor_get(x_697, 4);
x_707 = lean_ctor_get(x_697, 5);
x_708 = lean_ctor_get(x_697, 6);
x_709 = lean_ctor_get(x_697, 7);
x_710 = lean_ctor_get(x_697, 8);
lean_inc(x_710);
lean_inc(x_709);
lean_inc(x_708);
lean_inc(x_707);
lean_inc(x_706);
lean_inc(x_705);
lean_inc(x_704);
lean_inc(x_703);
lean_inc(x_702);
lean_dec(x_697);
lean_inc(x_698);
x_711 = l_Std_HashMapImp_insert___at_Lean_Closure_visitExpr___spec__3(x_705, x_611, x_698);
x_712 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_712, 0, x_702);
lean_ctor_set(x_712, 1, x_703);
lean_ctor_set(x_712, 2, x_704);
lean_ctor_set(x_712, 3, x_711);
lean_ctor_set(x_712, 4, x_706);
lean_ctor_set(x_712, 5, x_707);
lean_ctor_set(x_712, 6, x_708);
lean_ctor_set(x_712, 7, x_709);
lean_ctor_set(x_712, 8, x_710);
x_614 = x_698;
x_615 = x_712;
goto block_692;
}
}
else
{
uint8_t x_713; 
lean_dec(x_613);
lean_dec(x_612);
lean_dec(x_611);
lean_dec(x_2);
lean_dec(x_1);
x_713 = !lean_is_exclusive(x_696);
if (x_713 == 0)
{
return x_696;
}
else
{
lean_object* x_714; lean_object* x_715; lean_object* x_716; 
x_714 = lean_ctor_get(x_696, 0);
x_715 = lean_ctor_get(x_696, 1);
lean_inc(x_715);
lean_inc(x_714);
lean_dec(x_696);
x_716 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_716, 0, x_714);
lean_ctor_set(x_716, 1, x_715);
return x_716;
}
}
}
else
{
lean_object* x_717; 
lean_dec(x_611);
x_717 = lean_ctor_get(x_695, 0);
lean_inc(x_717);
lean_dec(x_695);
x_614 = x_717;
x_615 = x_3;
goto block_692;
}
}
}
case 10:
{
lean_object* x_725; lean_object* x_726; uint8_t x_752; 
x_725 = lean_ctor_get(x_1, 1);
lean_inc(x_725);
x_752 = l_Lean_Expr_hasLevelParam(x_725);
if (x_752 == 0)
{
uint8_t x_753; 
x_753 = l_Lean_Expr_hasFVar(x_725);
if (x_753 == 0)
{
uint8_t x_754; 
x_754 = l_Lean_Expr_hasMVar(x_725);
if (x_754 == 0)
{
lean_dec(x_2);
x_4 = x_725;
x_5 = x_3;
goto block_12;
}
else
{
lean_object* x_755; 
x_755 = lean_box(0);
x_726 = x_755;
goto block_751;
}
}
else
{
lean_object* x_756; 
x_756 = lean_box(0);
x_726 = x_756;
goto block_751;
}
}
else
{
lean_object* x_757; 
x_757 = lean_box(0);
x_726 = x_757;
goto block_751;
}
block_751:
{
lean_object* x_727; lean_object* x_728; 
lean_dec(x_726);
x_727 = lean_ctor_get(x_3, 3);
lean_inc(x_727);
x_728 = l_Std_HashMapImp_find_x3f___at_Lean_Closure_visitExpr___spec__1(x_727, x_725);
lean_dec(x_727);
if (lean_obj_tag(x_728) == 0)
{
lean_object* x_729; 
lean_inc(x_725);
x_729 = l_Lean_Closure_collectExprAux___main(x_725, x_2, x_3);
if (lean_obj_tag(x_729) == 0)
{
lean_object* x_730; lean_object* x_731; uint8_t x_732; 
x_730 = lean_ctor_get(x_729, 1);
lean_inc(x_730);
x_731 = lean_ctor_get(x_729, 0);
lean_inc(x_731);
lean_dec(x_729);
x_732 = !lean_is_exclusive(x_730);
if (x_732 == 0)
{
lean_object* x_733; lean_object* x_734; 
x_733 = lean_ctor_get(x_730, 3);
lean_inc(x_731);
x_734 = l_Std_HashMapImp_insert___at_Lean_Closure_visitExpr___spec__3(x_733, x_725, x_731);
lean_ctor_set(x_730, 3, x_734);
x_4 = x_731;
x_5 = x_730;
goto block_12;
}
else
{
lean_object* x_735; lean_object* x_736; lean_object* x_737; lean_object* x_738; lean_object* x_739; lean_object* x_740; lean_object* x_741; lean_object* x_742; lean_object* x_743; lean_object* x_744; lean_object* x_745; 
x_735 = lean_ctor_get(x_730, 0);
x_736 = lean_ctor_get(x_730, 1);
x_737 = lean_ctor_get(x_730, 2);
x_738 = lean_ctor_get(x_730, 3);
x_739 = lean_ctor_get(x_730, 4);
x_740 = lean_ctor_get(x_730, 5);
x_741 = lean_ctor_get(x_730, 6);
x_742 = lean_ctor_get(x_730, 7);
x_743 = lean_ctor_get(x_730, 8);
lean_inc(x_743);
lean_inc(x_742);
lean_inc(x_741);
lean_inc(x_740);
lean_inc(x_739);
lean_inc(x_738);
lean_inc(x_737);
lean_inc(x_736);
lean_inc(x_735);
lean_dec(x_730);
lean_inc(x_731);
x_744 = l_Std_HashMapImp_insert___at_Lean_Closure_visitExpr___spec__3(x_738, x_725, x_731);
x_745 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_745, 0, x_735);
lean_ctor_set(x_745, 1, x_736);
lean_ctor_set(x_745, 2, x_737);
lean_ctor_set(x_745, 3, x_744);
lean_ctor_set(x_745, 4, x_739);
lean_ctor_set(x_745, 5, x_740);
lean_ctor_set(x_745, 6, x_741);
lean_ctor_set(x_745, 7, x_742);
lean_ctor_set(x_745, 8, x_743);
x_4 = x_731;
x_5 = x_745;
goto block_12;
}
}
else
{
uint8_t x_746; 
lean_dec(x_725);
lean_dec(x_1);
x_746 = !lean_is_exclusive(x_729);
if (x_746 == 0)
{
return x_729;
}
else
{
lean_object* x_747; lean_object* x_748; lean_object* x_749; 
x_747 = lean_ctor_get(x_729, 0);
x_748 = lean_ctor_get(x_729, 1);
lean_inc(x_748);
lean_inc(x_747);
lean_dec(x_729);
x_749 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_749, 0, x_747);
lean_ctor_set(x_749, 1, x_748);
return x_749;
}
}
}
else
{
lean_object* x_750; 
lean_dec(x_725);
lean_dec(x_2);
x_750 = lean_ctor_get(x_728, 0);
lean_inc(x_750);
lean_dec(x_728);
x_4 = x_750;
x_5 = x_3;
goto block_12;
}
}
}
case 11:
{
lean_object* x_758; lean_object* x_759; uint8_t x_785; 
x_758 = lean_ctor_get(x_1, 2);
lean_inc(x_758);
x_785 = l_Lean_Expr_hasLevelParam(x_758);
if (x_785 == 0)
{
uint8_t x_786; 
x_786 = l_Lean_Expr_hasFVar(x_758);
if (x_786 == 0)
{
uint8_t x_787; 
x_787 = l_Lean_Expr_hasMVar(x_758);
if (x_787 == 0)
{
lean_dec(x_2);
x_13 = x_758;
x_14 = x_3;
goto block_21;
}
else
{
lean_object* x_788; 
x_788 = lean_box(0);
x_759 = x_788;
goto block_784;
}
}
else
{
lean_object* x_789; 
x_789 = lean_box(0);
x_759 = x_789;
goto block_784;
}
}
else
{
lean_object* x_790; 
x_790 = lean_box(0);
x_759 = x_790;
goto block_784;
}
block_784:
{
lean_object* x_760; lean_object* x_761; 
lean_dec(x_759);
x_760 = lean_ctor_get(x_3, 3);
lean_inc(x_760);
x_761 = l_Std_HashMapImp_find_x3f___at_Lean_Closure_visitExpr___spec__1(x_760, x_758);
lean_dec(x_760);
if (lean_obj_tag(x_761) == 0)
{
lean_object* x_762; 
lean_inc(x_758);
x_762 = l_Lean_Closure_collectExprAux___main(x_758, x_2, x_3);
if (lean_obj_tag(x_762) == 0)
{
lean_object* x_763; lean_object* x_764; uint8_t x_765; 
x_763 = lean_ctor_get(x_762, 1);
lean_inc(x_763);
x_764 = lean_ctor_get(x_762, 0);
lean_inc(x_764);
lean_dec(x_762);
x_765 = !lean_is_exclusive(x_763);
if (x_765 == 0)
{
lean_object* x_766; lean_object* x_767; 
x_766 = lean_ctor_get(x_763, 3);
lean_inc(x_764);
x_767 = l_Std_HashMapImp_insert___at_Lean_Closure_visitExpr___spec__3(x_766, x_758, x_764);
lean_ctor_set(x_763, 3, x_767);
x_13 = x_764;
x_14 = x_763;
goto block_21;
}
else
{
lean_object* x_768; lean_object* x_769; lean_object* x_770; lean_object* x_771; lean_object* x_772; lean_object* x_773; lean_object* x_774; lean_object* x_775; lean_object* x_776; lean_object* x_777; lean_object* x_778; 
x_768 = lean_ctor_get(x_763, 0);
x_769 = lean_ctor_get(x_763, 1);
x_770 = lean_ctor_get(x_763, 2);
x_771 = lean_ctor_get(x_763, 3);
x_772 = lean_ctor_get(x_763, 4);
x_773 = lean_ctor_get(x_763, 5);
x_774 = lean_ctor_get(x_763, 6);
x_775 = lean_ctor_get(x_763, 7);
x_776 = lean_ctor_get(x_763, 8);
lean_inc(x_776);
lean_inc(x_775);
lean_inc(x_774);
lean_inc(x_773);
lean_inc(x_772);
lean_inc(x_771);
lean_inc(x_770);
lean_inc(x_769);
lean_inc(x_768);
lean_dec(x_763);
lean_inc(x_764);
x_777 = l_Std_HashMapImp_insert___at_Lean_Closure_visitExpr___spec__3(x_771, x_758, x_764);
x_778 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_778, 0, x_768);
lean_ctor_set(x_778, 1, x_769);
lean_ctor_set(x_778, 2, x_770);
lean_ctor_set(x_778, 3, x_777);
lean_ctor_set(x_778, 4, x_772);
lean_ctor_set(x_778, 5, x_773);
lean_ctor_set(x_778, 6, x_774);
lean_ctor_set(x_778, 7, x_775);
lean_ctor_set(x_778, 8, x_776);
x_13 = x_764;
x_14 = x_778;
goto block_21;
}
}
else
{
uint8_t x_779; 
lean_dec(x_758);
lean_dec(x_1);
x_779 = !lean_is_exclusive(x_762);
if (x_779 == 0)
{
return x_762;
}
else
{
lean_object* x_780; lean_object* x_781; lean_object* x_782; 
x_780 = lean_ctor_get(x_762, 0);
x_781 = lean_ctor_get(x_762, 1);
lean_inc(x_781);
lean_inc(x_780);
lean_dec(x_762);
x_782 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_782, 0, x_780);
lean_ctor_set(x_782, 1, x_781);
return x_782;
}
}
}
else
{
lean_object* x_783; 
lean_dec(x_758);
lean_dec(x_2);
x_783 = lean_ctor_get(x_761, 0);
lean_inc(x_783);
lean_dec(x_761);
x_13 = x_783;
x_14 = x_3;
goto block_21;
}
}
}
default: 
{
lean_object* x_791; 
lean_dec(x_2);
x_791 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_791, 0, x_1);
lean_ctor_set(x_791, 1, x_3);
return x_791;
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
x_6 = l_Std_HashMapImp_find_x3f___at_Lean_Closure_visitExpr___spec__1(x_5, x_1);
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
x_13 = l_Std_HashMapImp_insert___at_Lean_Closure_visitExpr___spec__3(x_12, x_1, x_11);
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
x_24 = l_Std_HashMapImp_insert___at_Lean_Closure_visitExpr___spec__3(x_18, x_1, x_14);
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
x_38 = l_Std_HashMapImp_insert___at_Lean_Closure_visitExpr___spec__3(x_31, x_1, x_27);
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
lean_object* l_Std_ShareCommonT_withShareCommon___at_Lean_Closure_mkClosure___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_state_sharecommon(x_2, x_1);
return x_3;
}
}
lean_object* l_Std_mkHashMap___at_Lean_Closure_mkClosure___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_mkHashMapImp___rarg(x_1);
return x_2;
}
}
lean_object* l_Std_mkHashMap___at_Lean_Closure_mkClosure___spec__3(lean_object* x_1) {
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
lean_object* l_Lean_Closure_mkClosure(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_6 = l_Std_ShareCommon_State_empty;
x_7 = lean_state_sharecommon(x_6, x_3);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_state_sharecommon(x_9, x_4);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_10, 1);
lean_dec(x_13);
x_31 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_31, 0, x_1);
lean_ctor_set(x_31, 1, x_2);
lean_ctor_set_uint8(x_31, sizeof(void*)*2, x_5);
x_32 = l_Lean_Closure_mkClosure___closed__6;
lean_inc(x_31);
x_33 = l_Lean_Closure_collectExpr(x_8, x_31, x_32);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = l_Lean_Closure_collectExpr(x_12, x_31, x_35);
if (lean_obj_tag(x_36) == 0)
{
uint8_t x_37; 
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
lean_object* x_38; 
x_38 = lean_ctor_get(x_36, 0);
lean_ctor_set(x_10, 1, x_38);
lean_ctor_set(x_10, 0, x_34);
lean_ctor_set(x_36, 0, x_10);
x_14 = x_36;
goto block_30;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_36, 0);
x_40 = lean_ctor_get(x_36, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_36);
lean_ctor_set(x_10, 1, x_39);
lean_ctor_set(x_10, 0, x_34);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_10);
lean_ctor_set(x_41, 1, x_40);
x_14 = x_41;
goto block_30;
}
}
else
{
uint8_t x_42; 
lean_dec(x_34);
lean_free_object(x_10);
x_42 = !lean_is_exclusive(x_36);
if (x_42 == 0)
{
x_14 = x_36;
goto block_30;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_36, 0);
x_44 = lean_ctor_get(x_36, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_36);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
x_14 = x_45;
goto block_30;
}
}
}
else
{
uint8_t x_46; 
lean_dec(x_31);
lean_free_object(x_10);
lean_dec(x_12);
x_46 = !lean_is_exclusive(x_33);
if (x_46 == 0)
{
x_14 = x_33;
goto block_30;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_33, 0);
x_48 = lean_ctor_get(x_33, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_33);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
x_14 = x_49;
goto block_30;
}
}
block_30:
{
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
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
x_19 = lean_ctor_get(x_16, 0);
lean_inc(x_19);
x_20 = l_Lean_LocalContext_getFVars(x_19);
lean_inc(x_19);
x_21 = l_Lean_LocalContext_mkForall(x_19, x_20, x_17);
lean_dec(x_17);
x_22 = l_Lean_LocalContext_mkLambda(x_19, x_20, x_18);
lean_dec(x_18);
lean_dec(x_20);
x_23 = lean_ctor_get(x_16, 4);
lean_inc(x_23);
x_24 = lean_ctor_get(x_16, 6);
lean_inc(x_24);
x_25 = lean_ctor_get(x_16, 8);
lean_inc(x_25);
lean_dec(x_16);
x_26 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_26, 0, x_23);
lean_ctor_set(x_26, 1, x_21);
lean_ctor_set(x_26, 2, x_22);
lean_ctor_set(x_26, 3, x_24);
lean_ctor_set(x_26, 4, x_25);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_26);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_14, 0);
lean_inc(x_28);
lean_dec(x_14);
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_28);
return x_29;
}
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_50 = lean_ctor_get(x_10, 0);
lean_inc(x_50);
lean_dec(x_10);
x_68 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_68, 0, x_1);
lean_ctor_set(x_68, 1, x_2);
lean_ctor_set_uint8(x_68, sizeof(void*)*2, x_5);
x_69 = l_Lean_Closure_mkClosure___closed__6;
lean_inc(x_68);
x_70 = l_Lean_Closure_collectExpr(x_8, x_68, x_69);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
lean_dec(x_70);
x_73 = l_Lean_Closure_collectExpr(x_50, x_68, x_72);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 x_76 = x_73;
} else {
 lean_dec_ref(x_73);
 x_76 = lean_box(0);
}
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_71);
lean_ctor_set(x_77, 1, x_74);
if (lean_is_scalar(x_76)) {
 x_78 = lean_alloc_ctor(0, 2, 0);
} else {
 x_78 = x_76;
}
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_75);
x_51 = x_78;
goto block_67;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
lean_dec(x_71);
x_79 = lean_ctor_get(x_73, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_73, 1);
lean_inc(x_80);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 x_81 = x_73;
} else {
 lean_dec_ref(x_73);
 x_81 = lean_box(0);
}
if (lean_is_scalar(x_81)) {
 x_82 = lean_alloc_ctor(1, 2, 0);
} else {
 x_82 = x_81;
}
lean_ctor_set(x_82, 0, x_79);
lean_ctor_set(x_82, 1, x_80);
x_51 = x_82;
goto block_67;
}
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
lean_dec(x_68);
lean_dec(x_50);
x_83 = lean_ctor_get(x_70, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_70, 1);
lean_inc(x_84);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 lean_ctor_release(x_70, 1);
 x_85 = x_70;
} else {
 lean_dec_ref(x_70);
 x_85 = lean_box(0);
}
if (lean_is_scalar(x_85)) {
 x_86 = lean_alloc_ctor(1, 2, 0);
} else {
 x_86 = x_85;
}
lean_ctor_set(x_86, 0, x_83);
lean_ctor_set(x_86, 1, x_84);
x_51 = x_86;
goto block_67;
}
block_67:
{
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
x_54 = lean_ctor_get(x_52, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_52, 1);
lean_inc(x_55);
lean_dec(x_52);
x_56 = lean_ctor_get(x_53, 0);
lean_inc(x_56);
x_57 = l_Lean_LocalContext_getFVars(x_56);
lean_inc(x_56);
x_58 = l_Lean_LocalContext_mkForall(x_56, x_57, x_54);
lean_dec(x_54);
x_59 = l_Lean_LocalContext_mkLambda(x_56, x_57, x_55);
lean_dec(x_55);
lean_dec(x_57);
x_60 = lean_ctor_get(x_53, 4);
lean_inc(x_60);
x_61 = lean_ctor_get(x_53, 6);
lean_inc(x_61);
x_62 = lean_ctor_get(x_53, 8);
lean_inc(x_62);
lean_dec(x_53);
x_63 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_63, 0, x_60);
lean_ctor_set(x_63, 1, x_58);
lean_ctor_set(x_63, 2, x_59);
lean_ctor_set(x_63, 3, x_61);
lean_ctor_set(x_63, 4, x_62);
x_64 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_64, 0, x_63);
return x_64;
}
else
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_ctor_get(x_51, 0);
lean_inc(x_65);
lean_dec(x_51);
x_66 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_66, 0, x_65);
return x_66;
}
}
}
}
}
lean_object* l_Lean_Closure_mkClosure___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_5);
lean_dec(x_5);
x_7 = l_Lean_Closure_mkClosure(x_1, x_2, x_3, x_4, x_6);
return x_7;
}
}
lean_object* l_Lean_mkAuxDefinition(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, uint8_t x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Closure_mkClosure(x_3, x_4, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
lean_dec(x_5);
lean_dec(x_1);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_alloc_ctor(11, 1, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_9, 0, x_12);
return x_9;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_9, 0);
lean_inc(x_13);
lean_dec(x_9);
x_14 = lean_alloc_ctor(11, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint32_t x_23; uint32_t x_24; uint32_t x_25; lean_object* x_26; uint8_t x_27; 
x_16 = lean_ctor_get(x_9, 0);
lean_inc(x_16);
lean_dec(x_9);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = l_Array_toList___rarg(x_17);
lean_dec(x_17);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_inc(x_19);
lean_inc(x_5);
x_20 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_20, 0, x_5);
lean_ctor_set(x_20, 1, x_18);
lean_ctor_set(x_20, 2, x_19);
x_21 = lean_ctor_get(x_16, 2);
lean_inc(x_21);
lean_inc(x_21);
lean_inc(x_1);
x_22 = l_Lean_getMaxHeight(x_1, x_21);
x_23 = lean_unbox_uint32(x_22);
lean_dec(x_22);
x_24 = 1;
x_25 = x_23 + x_24;
x_26 = lean_alloc_ctor(2, 0, 4);
lean_ctor_set_uint32(x_26, 0, x_25);
lean_inc(x_1);
x_27 = l_Lean_Environment_hasUnsafe(x_1, x_19);
if (x_27 == 0)
{
uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_inc(x_21);
lean_inc(x_1);
x_28 = l_Lean_Environment_hasUnsafe(x_1, x_21);
x_29 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_29, 0, x_20);
lean_ctor_set(x_29, 1, x_21);
lean_ctor_set(x_29, 2, x_26);
lean_ctor_set_uint8(x_29, sizeof(void*)*3, x_28);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_29);
x_31 = l_Lean_Environment_addAndCompile(x_1, x_2, x_30);
lean_dec(x_30);
if (lean_obj_tag(x_31) == 0)
{
uint8_t x_32; 
lean_dec(x_16);
lean_dec(x_5);
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
return x_31;
}
else
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_31, 0);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_34, 0, x_33);
return x_34;
}
}
else
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_31);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_36 = lean_ctor_get(x_31, 0);
x_37 = lean_ctor_get(x_16, 3);
lean_inc(x_37);
x_38 = l_Array_toList___rarg(x_37);
lean_dec(x_37);
x_39 = l_Lean_mkConst(x_5, x_38);
x_40 = lean_ctor_get(x_16, 4);
lean_inc(x_40);
lean_dec(x_16);
x_41 = lean_unsigned_to_nat(0u);
x_42 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_40, x_40, x_41, x_39);
lean_dec(x_40);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_36);
lean_ctor_set(x_31, 0, x_43);
return x_31;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_44 = lean_ctor_get(x_31, 0);
lean_inc(x_44);
lean_dec(x_31);
x_45 = lean_ctor_get(x_16, 3);
lean_inc(x_45);
x_46 = l_Array_toList___rarg(x_45);
lean_dec(x_45);
x_47 = l_Lean_mkConst(x_5, x_46);
x_48 = lean_ctor_get(x_16, 4);
lean_inc(x_48);
lean_dec(x_16);
x_49 = lean_unsigned_to_nat(0u);
x_50 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_48, x_48, x_49, x_47);
lean_dec(x_48);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_44);
x_52 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_52, 0, x_51);
return x_52;
}
}
}
else
{
uint8_t x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_53 = 1;
x_54 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_54, 0, x_20);
lean_ctor_set(x_54, 1, x_21);
lean_ctor_set(x_54, 2, x_26);
lean_ctor_set_uint8(x_54, sizeof(void*)*3, x_53);
x_55 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_55, 0, x_54);
x_56 = l_Lean_Environment_addAndCompile(x_1, x_2, x_55);
lean_dec(x_55);
if (lean_obj_tag(x_56) == 0)
{
uint8_t x_57; 
lean_dec(x_16);
lean_dec(x_5);
x_57 = !lean_is_exclusive(x_56);
if (x_57 == 0)
{
return x_56;
}
else
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_56, 0);
lean_inc(x_58);
lean_dec(x_56);
x_59 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_59, 0, x_58);
return x_59;
}
}
else
{
uint8_t x_60; 
x_60 = !lean_is_exclusive(x_56);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_61 = lean_ctor_get(x_56, 0);
x_62 = lean_ctor_get(x_16, 3);
lean_inc(x_62);
x_63 = l_Array_toList___rarg(x_62);
lean_dec(x_62);
x_64 = l_Lean_mkConst(x_5, x_63);
x_65 = lean_ctor_get(x_16, 4);
lean_inc(x_65);
lean_dec(x_16);
x_66 = lean_unsigned_to_nat(0u);
x_67 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_65, x_65, x_66, x_64);
lean_dec(x_65);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_61);
lean_ctor_set(x_56, 0, x_68);
return x_56;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_69 = lean_ctor_get(x_56, 0);
lean_inc(x_69);
lean_dec(x_56);
x_70 = lean_ctor_get(x_16, 3);
lean_inc(x_70);
x_71 = l_Array_toList___rarg(x_70);
lean_dec(x_70);
x_72 = l_Lean_mkConst(x_5, x_71);
x_73 = lean_ctor_get(x_16, 4);
lean_inc(x_73);
lean_dec(x_16);
x_74 = lean_unsigned_to_nat(0u);
x_75 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_73, x_73, x_74, x_72);
lean_dec(x_73);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_69);
x_77 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_77, 0, x_76);
return x_77;
}
}
}
}
}
}
lean_object* l_Lean_mkAuxDefinition___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_8);
lean_dec(x_8);
x_10 = l_Lean_mkAuxDefinition(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_9);
lean_dec(x_2);
return x_10;
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
