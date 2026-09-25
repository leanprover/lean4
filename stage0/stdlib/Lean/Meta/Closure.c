// Lean compiler output
// Module: Lean.Meta.Closure
// Imports: public import Lean.Meta.Check public import Lean.Meta.Tactic.AuxLemma import Lean.Util.ForEachExpr
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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
uint8_t l_Lean_ExprStructEq_beq(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instInhabitedCoreM___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
extern lean_object* l_Lean_instEmptyCollectionFVarIdHashSet;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_fvarId(lean_object*);
uint64_t l_Lean_instHashableFVarId_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
uint64_t l_Lean_Expr_hash(lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t l_Lean_LocalDecl_isLet(lean_object*, uint8_t);
lean_object* l_instMonadEIO___redArg();
lean_object* l_StateRefT_x27_instMonad___redArg(lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_pure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_bind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
lean_object* l_Lean_MetavarContext_getDelayedMVarAssignmentCore_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
uint64_t l_Lean_Level_hash(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_get_x21(lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_index(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_expr_abstract_range(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkForall(lean_object*, uint8_t, lean_object*, lean_object*);
uint8_t lean_expr_has_loose_bvar(lean_object*, lean_object*);
lean_object* lean_expr_lower_loose_bvars(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_Environment_hasUnsafe(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkLambda(lean_object*, uint8_t, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* l_Lean_Meta_check(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_ExprStructEq_hash(lean_object*);
uint8_t l_Lean_Expr_hasLevelParam(lean_object*);
size_t lean_ptr_addr(lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_instBEqBinderInfo_beq(uint8_t, uint8_t);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
uint8_t lean_level_eq(lean_object*, lean_object*);
lean_object* l_Lean_Level_succ___override(lean_object*);
uint8_t l_Lean_Level_hasMVar(lean_object*);
uint8_t l_Lean_Level_hasParam(lean_object*);
lean_object* l_Lean_mkLevelMax_x27(lean_object*, lean_object*);
lean_object* l_Lean_simpLevelMax_x27(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkLevelIMax_x27(lean_object*, lean_object*);
lean_object* l_Lean_simpLevelIMax_x27(lean_object*, lean_object*, lean_object*);
lean_object* lean_name_append_index_after(lean_object*, lean_object*);
lean_object* l_Lean_mkLevelParam(lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
uint8_t l_ptrEqList___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FVarId_getValue_x3f___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_pop(lean_object*);
lean_object* l_Lean_FVarId_getDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getZetaDeltaFVarIds___redArg(lean_object*);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_replaceFVarId(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_reverse___redArg(lean_object*);
lean_object* l_Lean_LocalDecl_toExpr(lean_object*);
lean_object* lean_expr_abstract(lean_object*, lean_object*);
lean_object* l_Lean_Meta_instInhabitedMetaM___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAuxLemma(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Nat_foldRev___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Level_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Level_hash___boxed(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ExprStructEq_hash___boxed(lean_object*);
lean_object* l_Lean_ExprStructEq_beq___boxed(lean_object*, lean_object*);
uint32_t l_Lean_getMaxHeight(lean_object*, lean_object*);
uint32_t lean_uint32_add(uint32_t, uint32_t);
lean_object* l_Lean_addDecl(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_compileDecl(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_headBeta(lean_object*);
static const lean_ctor_object l_Lean_Meta_Closure_instInhabitedToProcessElement_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Closure_instInhabitedToProcessElement_default___closed__0 = (const lean_object*)&l_Lean_Meta_Closure_instInhabitedToProcessElement_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Closure_instInhabitedToProcessElement_default = (const lean_object*)&l_Lean_Meta_Closure_instInhabitedToProcessElement_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Closure_instInhabitedToProcessElement = (const lean_object*)&l_Lean_Meta_Closure_instInhabitedToProcessElement_default___closed__0_value;
static const lean_closure_object l_Lean_Meta_Closure_visitLevel___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Level_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Closure_visitLevel___closed__0 = (const lean_object*)&l_Lean_Meta_Closure_visitLevel___closed__0_value;
static const lean_closure_object l_Lean_Meta_Closure_visitLevel___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Level_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Closure_visitLevel___closed__1 = (const lean_object*)&l_Lean_Meta_Closure_visitLevel___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_visitLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_visitLevel___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Closure_visitExpr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_ExprStructEq_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Closure_visitExpr___closed__0 = (const lean_object*)&l_Lean_Meta_Closure_visitExpr___closed__0_value;
static const lean_closure_object l_Lean_Meta_Closure_visitExpr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_ExprStructEq_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Closure_visitExpr___closed__1 = (const lean_object*)&l_Lean_Meta_Closure_visitExpr___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_visitExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_visitExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Closure_mkNewLevelParam___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "u"};
static const lean_object* l_Lean_Meta_Closure_mkNewLevelParam___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Closure_mkNewLevelParam___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Closure_mkNewLevelParam___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Closure_mkNewLevelParam___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(232, 178, 247, 241, 102, 42, 87, 174)}};
static const lean_object* l_Lean_Meta_Closure_mkNewLevelParam___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Closure_mkNewLevelParam___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkNewLevelParam___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkNewLevelParam___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkNewLevelParam(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkNewLevelParam___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Closure_collectLevelAux_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectLevelAux_spec__1_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectLevelAux_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectLevelAux_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectLevelAux_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__4_spec__5_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__4_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__4___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectLevelAux___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectLevelAux___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectLevelAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectLevelAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectLevelAux_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectLevelAux_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectLevelAux_spec__1_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectLevelAux_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__4_spec__5_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectLevel___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectLevel___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectLevel___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Closure_preprocess_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Closure_preprocess_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Closure_preprocess_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Closure_preprocess_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_preprocess(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_preprocess___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Closure_mkNextUserName___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_x"};
static const lean_object* l_Lean_Meta_Closure_mkNextUserName___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Closure_mkNextUserName___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Closure_mkNextUserName___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Closure_mkNextUserName___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(181, 1, 28, 251, 11, 9, 217, 106)}};
static const lean_object* l_Lean_Meta_Closure_mkNextUserName___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Closure_mkNextUserName___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkNextUserName___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkNextUserName___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkNextUserName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkNextUserName___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushToProcess___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushToProcess___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushToProcess(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushToProcess___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Closure_collectExprAux_spec__5___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Closure_collectExprAux_spec__5___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Closure_collectExprAux_spec__5___redArg(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Closure_collectExprAux_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Closure_collectExprAux_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Closure_collectExprAux_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Closure_collectExprAux_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Closure_collectExprAux_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Closure_collectExprAux_spec__3_spec__7___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Closure_collectExprAux_spec__3_spec__7___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00Lean_Meta_Closure_collectExprAux_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00Lean_Meta_Closure_collectExprAux_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectExprAux___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectExprAux___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__3_spec__6_spec__10___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__3_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__3___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectExprAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectExprAux___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectExprAux___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectExprAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Closure_collectExprAux_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Closure_collectExprAux_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Closure_collectExprAux_spec__3_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Closure_collectExprAux_spec__3_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__3_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__3_spec__6_spec__10(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pickNextToProcessAux(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pickNextToProcess_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pickNextToProcess_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pickNextToProcess_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pickNextToProcess_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushFVarArg___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushFVarArg___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushFVarArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushFVarArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushLocalDecl(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushLocalDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Closure_process_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Closure_process_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Closure_process_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Closure_process_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_process(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_process___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Closure_process_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Closure_process_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkBinding___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkBinding___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Closure_mkBinding___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_LocalDecl_toExpr, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Closure_mkBinding___closed__0 = (const lean_object*)&l_Lean_Meta_Closure_mkBinding___closed__0_value;
static const lean_closure_object l_Lean_Meta_Closure_mkBinding___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Closure_mkBinding___closed__1 = (const lean_object*)&l_Lean_Meta_Closure_mkBinding___closed__1_value;
static const lean_closure_object l_Lean_Meta_Closure_mkBinding___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Closure_mkBinding___closed__2 = (const lean_object*)&l_Lean_Meta_Closure_mkBinding___closed__2_value;
static const lean_closure_object l_Lean_Meta_Closure_mkBinding___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Closure_mkBinding___closed__3 = (const lean_object*)&l_Lean_Meta_Closure_mkBinding___closed__3_value;
static const lean_closure_object l_Lean_Meta_Closure_mkBinding___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Closure_mkBinding___closed__4 = (const lean_object*)&l_Lean_Meta_Closure_mkBinding___closed__4_value;
static const lean_closure_object l_Lean_Meta_Closure_mkBinding___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Closure_mkBinding___closed__5 = (const lean_object*)&l_Lean_Meta_Closure_mkBinding___closed__5_value;
static const lean_closure_object l_Lean_Meta_Closure_mkBinding___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Closure_mkBinding___closed__6 = (const lean_object*)&l_Lean_Meta_Closure_mkBinding___closed__6_value;
static const lean_closure_object l_Lean_Meta_Closure_mkBinding___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Closure_mkBinding___closed__7 = (const lean_object*)&l_Lean_Meta_Closure_mkBinding___closed__7_value;
static const lean_ctor_object l_Lean_Meta_Closure_mkBinding___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_Closure_mkBinding___closed__1_value),((lean_object*)&l_Lean_Meta_Closure_mkBinding___closed__2_value)}};
static const lean_object* l_Lean_Meta_Closure_mkBinding___closed__8 = (const lean_object*)&l_Lean_Meta_Closure_mkBinding___closed__8_value;
static const lean_ctor_object l_Lean_Meta_Closure_mkBinding___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_Closure_mkBinding___closed__8_value),((lean_object*)&l_Lean_Meta_Closure_mkBinding___closed__3_value),((lean_object*)&l_Lean_Meta_Closure_mkBinding___closed__4_value),((lean_object*)&l_Lean_Meta_Closure_mkBinding___closed__5_value),((lean_object*)&l_Lean_Meta_Closure_mkBinding___closed__6_value)}};
static const lean_object* l_Lean_Meta_Closure_mkBinding___closed__9 = (const lean_object*)&l_Lean_Meta_Closure_mkBinding___closed__9_value;
static const lean_ctor_object l_Lean_Meta_Closure_mkBinding___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_Closure_mkBinding___closed__9_value),((lean_object*)&l_Lean_Meta_Closure_mkBinding___closed__7_value)}};
static const lean_object* l_Lean_Meta_Closure_mkBinding___closed__10 = (const lean_object*)&l_Lean_Meta_Closure_mkBinding___closed__10_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkBinding(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkBinding___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Closure_mkLambda_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Closure_mkLambda_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_Meta_Closure_mkLambda_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_Meta_Closure_mkLambda_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Lean_Meta_Closure_mkLambda_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Lean_Meta_Closure_mkLambda_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkLambda(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkLambda___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_Meta_Closure_mkForall_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_Meta_Closure_mkForall_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Lean_Meta_Closure_mkForall_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Lean_Meta_Closure_mkForall_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkForall(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkForall___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkValueTypeClosureAux___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkValueTypeClosureAux___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkValueTypeClosureAux___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkValueTypeClosureAux___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__0;
static lean_once_cell_t l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__1;
static lean_once_cell_t l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkValueTypeClosureAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkValueTypeClosureAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4___closed__0;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4___closed__1 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4___closed__1_value;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4___closed__2 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4___closed__2_value;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__4_spec__6_spec__11___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__4_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__4___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__6_spec__9___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__6_spec__9___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__6___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__13___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__12_spec__17_spec__18___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__12_spec__17___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__12___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__11___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__11___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__4;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6___closed__0;
static const lean_string_object l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__0;
static lean_once_cell_t l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__1;
static const lean_string_object l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 84, .m_capacity = 84, .m_length = 83, .m_data = "assertion violation: !decl.isLet (allowNondep := true) -- should all be cdecls\n    "};
static const lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__4 = (const lean_object*)&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__4_value;
static const lean_string_object l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 63, .m_capacity = 63, .m_length = 62, .m_data = "_private.Lean.Meta.Closure.0.Lean.Meta.Closure.sortDecls.visit"};
static const lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__3 = (const lean_object*)&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__3_value;
static const lean_string_object l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "Lean.Meta.Closure"};
static const lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__2 = (const lean_object*)&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__5;
static const lean_string_object l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 47, .m_capacity = 47, .m_length = 46, .m_data = "cycle detected in sorting abstracted variables"};
static const lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__6 = (const lean_object*)&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__6_value;
static lean_once_cell_t l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__7;
static const lean_string_object l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Closure"};
static const lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__9 = (const lean_object*)&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__9_value;
static const lean_string_object l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__8 = (const lean_object*)&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__8_value;
static const lean_ctor_object l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__8_value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__10_value_aux_0),((lean_object*)&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__9_value),LEAN_SCALAR_PTR_LITERAL(248, 96, 54, 247, 94, 45, 114, 27)}};
static const lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__10 = (const lean_object*)&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__10_value;
static const lean_string_object l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__11 = (const lean_object*)&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__11_value;
static const lean_ctor_object l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__11_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__12 = (const lean_object*)&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__12_value;
static lean_once_cell_t l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__13;
static const lean_string_object l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "Sorting decl "};
static const lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__14 = (const lean_object*)&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__14_value;
static lean_once_cell_t l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__15;
static const lean_string_object l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = " : "};
static const lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__16 = (const lean_object*)&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__16_value;
static lean_once_cell_t l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__17;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__4_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__6_spec__9(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__6_spec__9___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__11(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__11___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__12(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__13(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__4_spec__6_spec__11(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__12_spec__17(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__12_spec__17_spec__18(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instInhabitedCoreM___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__1___closed__0 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__1___closed__0_value;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__4(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__2___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 57, .m_capacity = 57, .m_length = 56, .m_data = "_private.Lean.Meta.Closure.0.Lean.Meta.Closure.sortDecls"};
static const lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__0 = (const lean_object*)&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 59, .m_capacity = 59, .m_length = 58, .m_data = "assertion violation: sortedDecls.size = sortedArgs.size\n  "};
static const lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__1 = (const lean_object*)&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__1_value;
static lean_once_cell_t l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__2;
static const lean_string_object l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 59, .m_capacity = 59, .m_length = 58, .m_data = "assertion violation: toSortDecls.size = toSortArgs.size\n  "};
static const lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__3 = (const lean_object*)&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__3_value;
static lean_once_cell_t l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__4;
static lean_once_cell_t l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__5;
static lean_once_cell_t l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__6;
static const lean_string_object l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "Sorted fvars: "};
static const lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__7 = (const lean_object*)&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__7_value;
static lean_once_cell_t l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__8;
static const lean_string_object l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 66, .m_capacity = 66, .m_length = 65, .m_data = "MVars to abstract, topologically sorting the abstracted variables"};
static const lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__9 = (const lean_object*)&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__9_value;
static lean_once_cell_t l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__10;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00Lean_Meta_Closure_mkValueTypeClosure_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instInhabitedMetaM___redArg___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Meta_Closure_mkValueTypeClosure_spec__1___closed__0 = (const lean_object*)&l_panic___at___00Lean_Meta_Closure_mkValueTypeClosure_spec__1___closed__0_value;
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Closure_mkValueTypeClosure_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Closure_mkValueTypeClosure_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_Meta_Closure_mkValueTypeClosure_spec__0_spec__1(lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_Meta_Closure_mkValueTypeClosure_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_Meta_Closure_mkValueTypeClosure_spec__0_spec__0(lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_Meta_Closure_mkValueTypeClosure_spec__0_spec__0_spec__2(lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_Meta_Closure_mkValueTypeClosure_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_Meta_Closure_mkValueTypeClosure_spec__0_spec__0___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyM___at___00Lean_Meta_Closure_mkValueTypeClosure_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___at___00Lean_Meta_Closure_mkValueTypeClosure_spec__0___boxed(lean_object*);
static lean_once_cell_t l_Lean_Meta_Closure_mkValueTypeClosure___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Closure_mkValueTypeClosure___closed__0;
static lean_once_cell_t l_Lean_Meta_Closure_mkValueTypeClosure___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Closure_mkValueTypeClosure___closed__1;
static const lean_array_object l_Lean_Meta_Closure_mkValueTypeClosure___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_Closure_mkValueTypeClosure___closed__2 = (const lean_object*)&l_Lean_Meta_Closure_mkValueTypeClosure___closed__2_value;
static lean_once_cell_t l_Lean_Meta_Closure_mkValueTypeClosure___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Closure_mkValueTypeClosure___closed__3;
static const lean_string_object l_Lean_Meta_Closure_mkValueTypeClosure___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Lean.Meta.Closure.mkValueTypeClosure"};
static const lean_object* l_Lean_Meta_Closure_mkValueTypeClosure___closed__4 = (const lean_object*)&l_Lean_Meta_Closure_mkValueTypeClosure___closed__4_value;
static const lean_string_object l_Lean_Meta_Closure_mkValueTypeClosure___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 124, .m_capacity = 124, .m_length = 123, .m_data = "assertion violation: !value.hasFVar  -- In case https://github.com/leanprover/lean4/issues/10705 resurfaces in a new way\n  "};
static const lean_object* l_Lean_Meta_Closure_mkValueTypeClosure___closed__5 = (const lean_object*)&l_Lean_Meta_Closure_mkValueTypeClosure___closed__5_value;
static lean_once_cell_t l_Lean_Meta_Closure_mkValueTypeClosure___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Closure_mkValueTypeClosure___closed__6;
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkValueTypeClosure(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkValueTypeClosure___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkAuxDefinition_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkAuxDefinition_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkAuxDefinition_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkAuxDefinition_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkAuxDefinition(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkAuxDefinition___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkAuxDefinitionFor(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkAuxDefinitionFor___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkAuxTheorem(lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkAuxTheorem___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__8_value),LEAN_SCALAR_PTR_LITERAL(30, 196, 118, 96, 111, 225, 34, 188)}};
static const lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__9_value),LEAN_SCALAR_PTR_LITERAL(249, 97, 222, 101, 51, 127, 178, 83)}};
static const lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(220, 178, 96, 6, 241, 231, 113, 20)}};
static const lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(253, 127, 178, 186, 28, 24, 102, 169)}};
static const lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__8_value),LEAN_SCALAR_PTR_LITERAL(21, 173, 206, 0, 127, 57, 105, 236)}};
static const lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(60, 19, 238, 0, 111, 115, 19, 38)}};
static const lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(53, 126, 95, 11, 82, 59, 71, 144)}};
static const lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(160, 8, 231, 231, 52, 89, 133, 183)}};
static const lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__8_value),LEAN_SCALAR_PTR_LITERAL(12, 6, 147, 100, 167, 240, 247, 134)}};
static const lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__9_value),LEAN_SCALAR_PTR_LITERAL(211, 133, 26, 59, 130, 208, 63, 13)}};
static const lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2__value),((lean_object*)(((size_t)(210311863) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 50, 125, 89, 33, 200, 89, 48)}};
static const lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(215, 43, 172, 82, 181, 165, 145, 47)}};
static const lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(63, 121, 24, 171, 140, 146, 97, 79)}};
static const lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(122, 57, 62, 99, 250, 159, 110, 171)}};
static const lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_initFn_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_initFn_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_visitLevel(lean_object* v_f_7_, lean_object* v_u_8_, lean_object* v_a_9_, lean_object* v_a_10_, lean_object* v_a_11_, lean_object* v_a_12_, lean_object* v_a_13_, lean_object* v_a_14_){
_start:
{
lean_object* v___x_16_; lean_object* v___x_17_; uint8_t v___x_61_; 
v___x_16_ = ((lean_object*)(l_Lean_Meta_Closure_visitLevel___closed__0));
v___x_17_ = ((lean_object*)(l_Lean_Meta_Closure_visitLevel___closed__1));
v___x_61_ = l_Lean_Level_hasMVar(v_u_8_);
if (v___x_61_ == 0)
{
uint8_t v___x_62_; 
v___x_62_ = l_Lean_Level_hasParam(v_u_8_);
if (v___x_62_ == 0)
{
lean_object* v___x_63_; 
lean_dec_ref(v_f_7_);
v___x_63_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_63_, 0, v_u_8_);
return v___x_63_;
}
else
{
goto v___jp_18_;
}
}
else
{
goto v___jp_18_;
}
v___jp_18_:
{
lean_object* v___x_19_; lean_object* v_visitedLevel_20_; lean_object* v___x_21_; 
v___x_19_ = lean_st_ref_get(v_a_10_);
v_visitedLevel_20_ = lean_ctor_get(v___x_19_, 0);
lean_inc_ref(v_visitedLevel_20_);
lean_dec(v___x_19_);
lean_inc(v_u_8_);
v___x_21_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v___x_16_, v___x_17_, v_visitedLevel_20_, v_u_8_);
lean_dec_ref(v_visitedLevel_20_);
if (lean_obj_tag(v___x_21_) == 0)
{
lean_object* v___x_22_; 
lean_inc(v_a_14_);
lean_inc_ref(v_a_13_);
lean_inc(v_a_12_);
lean_inc_ref(v_a_11_);
lean_inc(v_a_10_);
lean_inc_ref(v_a_9_);
lean_inc(v_u_8_);
v___x_22_ = lean_apply_8(v_f_7_, v_u_8_, v_a_9_, v_a_10_, v_a_11_, v_a_12_, v_a_13_, v_a_14_, lean_box(0));
if (lean_obj_tag(v___x_22_) == 0)
{
lean_object* v_a_23_; lean_object* v___x_25_; uint8_t v_isShared_26_; uint8_t v_isSharedCheck_52_; 
v_a_23_ = lean_ctor_get(v___x_22_, 0);
v_isSharedCheck_52_ = !lean_is_exclusive(v___x_22_);
if (v_isSharedCheck_52_ == 0)
{
v___x_25_ = v___x_22_;
v_isShared_26_ = v_isSharedCheck_52_;
goto v_resetjp_24_;
}
else
{
lean_inc(v_a_23_);
lean_dec(v___x_22_);
v___x_25_ = lean_box(0);
v_isShared_26_ = v_isSharedCheck_52_;
goto v_resetjp_24_;
}
v_resetjp_24_:
{
lean_object* v___x_27_; lean_object* v_visitedLevel_28_; lean_object* v_visitedExpr_29_; lean_object* v_levelParams_30_; lean_object* v_nextLevelIdx_31_; lean_object* v_levelArgs_32_; lean_object* v_newLocalDecls_33_; lean_object* v_newLocalDeclsForMVars_34_; lean_object* v_newLetDecls_35_; lean_object* v_nextExprIdx_36_; lean_object* v_exprMVarArgs_37_; lean_object* v_exprFVarArgs_38_; lean_object* v_toProcess_39_; lean_object* v___x_41_; uint8_t v_isShared_42_; uint8_t v_isSharedCheck_51_; 
v___x_27_ = lean_st_ref_take(v_a_10_);
v_visitedLevel_28_ = lean_ctor_get(v___x_27_, 0);
v_visitedExpr_29_ = lean_ctor_get(v___x_27_, 1);
v_levelParams_30_ = lean_ctor_get(v___x_27_, 2);
v_nextLevelIdx_31_ = lean_ctor_get(v___x_27_, 3);
v_levelArgs_32_ = lean_ctor_get(v___x_27_, 4);
v_newLocalDecls_33_ = lean_ctor_get(v___x_27_, 5);
v_newLocalDeclsForMVars_34_ = lean_ctor_get(v___x_27_, 6);
v_newLetDecls_35_ = lean_ctor_get(v___x_27_, 7);
v_nextExprIdx_36_ = lean_ctor_get(v___x_27_, 8);
v_exprMVarArgs_37_ = lean_ctor_get(v___x_27_, 9);
v_exprFVarArgs_38_ = lean_ctor_get(v___x_27_, 10);
v_toProcess_39_ = lean_ctor_get(v___x_27_, 11);
v_isSharedCheck_51_ = !lean_is_exclusive(v___x_27_);
if (v_isSharedCheck_51_ == 0)
{
v___x_41_ = v___x_27_;
v_isShared_42_ = v_isSharedCheck_51_;
goto v_resetjp_40_;
}
else
{
lean_inc(v_toProcess_39_);
lean_inc(v_exprFVarArgs_38_);
lean_inc(v_exprMVarArgs_37_);
lean_inc(v_nextExprIdx_36_);
lean_inc(v_newLetDecls_35_);
lean_inc(v_newLocalDeclsForMVars_34_);
lean_inc(v_newLocalDecls_33_);
lean_inc(v_levelArgs_32_);
lean_inc(v_nextLevelIdx_31_);
lean_inc(v_levelParams_30_);
lean_inc(v_visitedExpr_29_);
lean_inc(v_visitedLevel_28_);
lean_dec(v___x_27_);
v___x_41_ = lean_box(0);
v_isShared_42_ = v_isSharedCheck_51_;
goto v_resetjp_40_;
}
v_resetjp_40_:
{
lean_object* v___x_43_; lean_object* v___x_45_; 
lean_inc(v_a_23_);
v___x_43_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___x_16_, v___x_17_, v_visitedLevel_28_, v_u_8_, v_a_23_);
if (v_isShared_42_ == 0)
{
lean_ctor_set(v___x_41_, 0, v___x_43_);
v___x_45_ = v___x_41_;
goto v_reusejp_44_;
}
else
{
lean_object* v_reuseFailAlloc_50_; 
v_reuseFailAlloc_50_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_50_, 0, v___x_43_);
lean_ctor_set(v_reuseFailAlloc_50_, 1, v_visitedExpr_29_);
lean_ctor_set(v_reuseFailAlloc_50_, 2, v_levelParams_30_);
lean_ctor_set(v_reuseFailAlloc_50_, 3, v_nextLevelIdx_31_);
lean_ctor_set(v_reuseFailAlloc_50_, 4, v_levelArgs_32_);
lean_ctor_set(v_reuseFailAlloc_50_, 5, v_newLocalDecls_33_);
lean_ctor_set(v_reuseFailAlloc_50_, 6, v_newLocalDeclsForMVars_34_);
lean_ctor_set(v_reuseFailAlloc_50_, 7, v_newLetDecls_35_);
lean_ctor_set(v_reuseFailAlloc_50_, 8, v_nextExprIdx_36_);
lean_ctor_set(v_reuseFailAlloc_50_, 9, v_exprMVarArgs_37_);
lean_ctor_set(v_reuseFailAlloc_50_, 10, v_exprFVarArgs_38_);
lean_ctor_set(v_reuseFailAlloc_50_, 11, v_toProcess_39_);
v___x_45_ = v_reuseFailAlloc_50_;
goto v_reusejp_44_;
}
v_reusejp_44_:
{
lean_object* v___x_46_; lean_object* v___x_48_; 
v___x_46_ = lean_st_ref_put(v_a_10_, v___x_45_);
if (v_isShared_26_ == 0)
{
v___x_48_ = v___x_25_;
goto v_reusejp_47_;
}
else
{
lean_object* v_reuseFailAlloc_49_; 
v_reuseFailAlloc_49_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_49_, 0, v_a_23_);
v___x_48_ = v_reuseFailAlloc_49_;
goto v_reusejp_47_;
}
v_reusejp_47_:
{
return v___x_48_;
}
}
}
}
}
else
{
lean_dec(v_u_8_);
return v___x_22_;
}
}
else
{
lean_object* v_val_53_; lean_object* v___x_55_; uint8_t v_isShared_56_; uint8_t v_isSharedCheck_60_; 
lean_dec(v_u_8_);
lean_dec_ref(v_f_7_);
v_val_53_ = lean_ctor_get(v___x_21_, 0);
v_isSharedCheck_60_ = !lean_is_exclusive(v___x_21_);
if (v_isSharedCheck_60_ == 0)
{
v___x_55_ = v___x_21_;
v_isShared_56_ = v_isSharedCheck_60_;
goto v_resetjp_54_;
}
else
{
lean_inc(v_val_53_);
lean_dec(v___x_21_);
v___x_55_ = lean_box(0);
v_isShared_56_ = v_isSharedCheck_60_;
goto v_resetjp_54_;
}
v_resetjp_54_:
{
lean_object* v___x_58_; 
if (v_isShared_56_ == 0)
{
lean_ctor_set_tag(v___x_55_, 0);
v___x_58_ = v___x_55_;
goto v_reusejp_57_;
}
else
{
lean_object* v_reuseFailAlloc_59_; 
v_reuseFailAlloc_59_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_59_, 0, v_val_53_);
v___x_58_ = v_reuseFailAlloc_59_;
goto v_reusejp_57_;
}
v_reusejp_57_:
{
return v___x_58_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_visitLevel___boxed(lean_object* v_f_64_, lean_object* v_u_65_, lean_object* v_a_66_, lean_object* v_a_67_, lean_object* v_a_68_, lean_object* v_a_69_, lean_object* v_a_70_, lean_object* v_a_71_, lean_object* v_a_72_){
_start:
{
lean_object* v_res_73_; 
v_res_73_ = l_Lean_Meta_Closure_visitLevel(v_f_64_, v_u_65_, v_a_66_, v_a_67_, v_a_68_, v_a_69_, v_a_70_, v_a_71_);
lean_dec(v_a_71_);
lean_dec_ref(v_a_70_);
lean_dec(v_a_69_);
lean_dec_ref(v_a_68_);
lean_dec(v_a_67_);
lean_dec_ref(v_a_66_);
return v_res_73_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_visitExpr(lean_object* v_f_76_, lean_object* v_e_77_, lean_object* v_a_78_, lean_object* v_a_79_, lean_object* v_a_80_, lean_object* v_a_81_, lean_object* v_a_82_, lean_object* v_a_83_){
_start:
{
lean_object* v___x_85_; lean_object* v___x_86_; uint8_t v___x_130_; 
v___x_85_ = ((lean_object*)(l_Lean_Meta_Closure_visitExpr___closed__0));
v___x_86_ = ((lean_object*)(l_Lean_Meta_Closure_visitExpr___closed__1));
v___x_130_ = l_Lean_Expr_hasLevelParam(v_e_77_);
if (v___x_130_ == 0)
{
uint8_t v___x_131_; 
v___x_131_ = l_Lean_Expr_hasFVar(v_e_77_);
if (v___x_131_ == 0)
{
uint8_t v___x_132_; 
v___x_132_ = l_Lean_Expr_hasMVar(v_e_77_);
if (v___x_132_ == 0)
{
lean_object* v___x_133_; 
lean_dec_ref(v_f_76_);
v___x_133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_133_, 0, v_e_77_);
return v___x_133_;
}
else
{
goto v___jp_87_;
}
}
else
{
goto v___jp_87_;
}
}
else
{
goto v___jp_87_;
}
v___jp_87_:
{
lean_object* v___x_88_; lean_object* v_visitedExpr_89_; lean_object* v___x_90_; 
v___x_88_ = lean_st_ref_get(v_a_79_);
v_visitedExpr_89_ = lean_ctor_get(v___x_88_, 1);
lean_inc_ref(v_visitedExpr_89_);
lean_dec(v___x_88_);
lean_inc_ref(v_e_77_);
v___x_90_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v___x_85_, v___x_86_, v_visitedExpr_89_, v_e_77_);
lean_dec_ref(v_visitedExpr_89_);
if (lean_obj_tag(v___x_90_) == 0)
{
lean_object* v___x_91_; 
lean_inc(v_a_83_);
lean_inc_ref(v_a_82_);
lean_inc(v_a_81_);
lean_inc_ref(v_a_80_);
lean_inc(v_a_79_);
lean_inc_ref(v_a_78_);
lean_inc_ref(v_e_77_);
v___x_91_ = lean_apply_8(v_f_76_, v_e_77_, v_a_78_, v_a_79_, v_a_80_, v_a_81_, v_a_82_, v_a_83_, lean_box(0));
if (lean_obj_tag(v___x_91_) == 0)
{
lean_object* v_a_92_; lean_object* v___x_94_; uint8_t v_isShared_95_; uint8_t v_isSharedCheck_121_; 
v_a_92_ = lean_ctor_get(v___x_91_, 0);
v_isSharedCheck_121_ = !lean_is_exclusive(v___x_91_);
if (v_isSharedCheck_121_ == 0)
{
v___x_94_ = v___x_91_;
v_isShared_95_ = v_isSharedCheck_121_;
goto v_resetjp_93_;
}
else
{
lean_inc(v_a_92_);
lean_dec(v___x_91_);
v___x_94_ = lean_box(0);
v_isShared_95_ = v_isSharedCheck_121_;
goto v_resetjp_93_;
}
v_resetjp_93_:
{
lean_object* v___x_96_; lean_object* v_visitedLevel_97_; lean_object* v_visitedExpr_98_; lean_object* v_levelParams_99_; lean_object* v_nextLevelIdx_100_; lean_object* v_levelArgs_101_; lean_object* v_newLocalDecls_102_; lean_object* v_newLocalDeclsForMVars_103_; lean_object* v_newLetDecls_104_; lean_object* v_nextExprIdx_105_; lean_object* v_exprMVarArgs_106_; lean_object* v_exprFVarArgs_107_; lean_object* v_toProcess_108_; lean_object* v___x_110_; uint8_t v_isShared_111_; uint8_t v_isSharedCheck_120_; 
v___x_96_ = lean_st_ref_take(v_a_79_);
v_visitedLevel_97_ = lean_ctor_get(v___x_96_, 0);
v_visitedExpr_98_ = lean_ctor_get(v___x_96_, 1);
v_levelParams_99_ = lean_ctor_get(v___x_96_, 2);
v_nextLevelIdx_100_ = lean_ctor_get(v___x_96_, 3);
v_levelArgs_101_ = lean_ctor_get(v___x_96_, 4);
v_newLocalDecls_102_ = lean_ctor_get(v___x_96_, 5);
v_newLocalDeclsForMVars_103_ = lean_ctor_get(v___x_96_, 6);
v_newLetDecls_104_ = lean_ctor_get(v___x_96_, 7);
v_nextExprIdx_105_ = lean_ctor_get(v___x_96_, 8);
v_exprMVarArgs_106_ = lean_ctor_get(v___x_96_, 9);
v_exprFVarArgs_107_ = lean_ctor_get(v___x_96_, 10);
v_toProcess_108_ = lean_ctor_get(v___x_96_, 11);
v_isSharedCheck_120_ = !lean_is_exclusive(v___x_96_);
if (v_isSharedCheck_120_ == 0)
{
v___x_110_ = v___x_96_;
v_isShared_111_ = v_isSharedCheck_120_;
goto v_resetjp_109_;
}
else
{
lean_inc(v_toProcess_108_);
lean_inc(v_exprFVarArgs_107_);
lean_inc(v_exprMVarArgs_106_);
lean_inc(v_nextExprIdx_105_);
lean_inc(v_newLetDecls_104_);
lean_inc(v_newLocalDeclsForMVars_103_);
lean_inc(v_newLocalDecls_102_);
lean_inc(v_levelArgs_101_);
lean_inc(v_nextLevelIdx_100_);
lean_inc(v_levelParams_99_);
lean_inc(v_visitedExpr_98_);
lean_inc(v_visitedLevel_97_);
lean_dec(v___x_96_);
v___x_110_ = lean_box(0);
v_isShared_111_ = v_isSharedCheck_120_;
goto v_resetjp_109_;
}
v_resetjp_109_:
{
lean_object* v___x_112_; lean_object* v___x_114_; 
lean_inc(v_a_92_);
v___x_112_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___x_85_, v___x_86_, v_visitedExpr_98_, v_e_77_, v_a_92_);
if (v_isShared_111_ == 0)
{
lean_ctor_set(v___x_110_, 1, v___x_112_);
v___x_114_ = v___x_110_;
goto v_reusejp_113_;
}
else
{
lean_object* v_reuseFailAlloc_119_; 
v_reuseFailAlloc_119_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_119_, 0, v_visitedLevel_97_);
lean_ctor_set(v_reuseFailAlloc_119_, 1, v___x_112_);
lean_ctor_set(v_reuseFailAlloc_119_, 2, v_levelParams_99_);
lean_ctor_set(v_reuseFailAlloc_119_, 3, v_nextLevelIdx_100_);
lean_ctor_set(v_reuseFailAlloc_119_, 4, v_levelArgs_101_);
lean_ctor_set(v_reuseFailAlloc_119_, 5, v_newLocalDecls_102_);
lean_ctor_set(v_reuseFailAlloc_119_, 6, v_newLocalDeclsForMVars_103_);
lean_ctor_set(v_reuseFailAlloc_119_, 7, v_newLetDecls_104_);
lean_ctor_set(v_reuseFailAlloc_119_, 8, v_nextExprIdx_105_);
lean_ctor_set(v_reuseFailAlloc_119_, 9, v_exprMVarArgs_106_);
lean_ctor_set(v_reuseFailAlloc_119_, 10, v_exprFVarArgs_107_);
lean_ctor_set(v_reuseFailAlloc_119_, 11, v_toProcess_108_);
v___x_114_ = v_reuseFailAlloc_119_;
goto v_reusejp_113_;
}
v_reusejp_113_:
{
lean_object* v___x_115_; lean_object* v___x_117_; 
v___x_115_ = lean_st_ref_put(v_a_79_, v___x_114_);
if (v_isShared_95_ == 0)
{
v___x_117_ = v___x_94_;
goto v_reusejp_116_;
}
else
{
lean_object* v_reuseFailAlloc_118_; 
v_reuseFailAlloc_118_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_118_, 0, v_a_92_);
v___x_117_ = v_reuseFailAlloc_118_;
goto v_reusejp_116_;
}
v_reusejp_116_:
{
return v___x_117_;
}
}
}
}
}
else
{
lean_dec_ref(v_e_77_);
return v___x_91_;
}
}
else
{
lean_object* v_val_122_; lean_object* v___x_124_; uint8_t v_isShared_125_; uint8_t v_isSharedCheck_129_; 
lean_dec_ref(v_e_77_);
lean_dec_ref(v_f_76_);
v_val_122_ = lean_ctor_get(v___x_90_, 0);
v_isSharedCheck_129_ = !lean_is_exclusive(v___x_90_);
if (v_isSharedCheck_129_ == 0)
{
v___x_124_ = v___x_90_;
v_isShared_125_ = v_isSharedCheck_129_;
goto v_resetjp_123_;
}
else
{
lean_inc(v_val_122_);
lean_dec(v___x_90_);
v___x_124_ = lean_box(0);
v_isShared_125_ = v_isSharedCheck_129_;
goto v_resetjp_123_;
}
v_resetjp_123_:
{
lean_object* v___x_127_; 
if (v_isShared_125_ == 0)
{
lean_ctor_set_tag(v___x_124_, 0);
v___x_127_ = v___x_124_;
goto v_reusejp_126_;
}
else
{
lean_object* v_reuseFailAlloc_128_; 
v_reuseFailAlloc_128_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_128_, 0, v_val_122_);
v___x_127_ = v_reuseFailAlloc_128_;
goto v_reusejp_126_;
}
v_reusejp_126_:
{
return v___x_127_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_visitExpr___boxed(lean_object* v_f_134_, lean_object* v_e_135_, lean_object* v_a_136_, lean_object* v_a_137_, lean_object* v_a_138_, lean_object* v_a_139_, lean_object* v_a_140_, lean_object* v_a_141_, lean_object* v_a_142_){
_start:
{
lean_object* v_res_143_; 
v_res_143_ = l_Lean_Meta_Closure_visitExpr(v_f_134_, v_e_135_, v_a_136_, v_a_137_, v_a_138_, v_a_139_, v_a_140_, v_a_141_);
lean_dec(v_a_141_);
lean_dec_ref(v_a_140_);
lean_dec(v_a_139_);
lean_dec_ref(v_a_138_);
lean_dec(v_a_137_);
lean_dec_ref(v_a_136_);
return v_res_143_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkNewLevelParam___redArg(lean_object* v_u_147_, lean_object* v_a_148_){
_start:
{
lean_object* v___x_150_; lean_object* v_nextLevelIdx_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v_visitedLevel_155_; lean_object* v_visitedExpr_156_; lean_object* v_levelParams_157_; lean_object* v_nextLevelIdx_158_; lean_object* v_levelArgs_159_; lean_object* v_newLocalDecls_160_; lean_object* v_newLocalDeclsForMVars_161_; lean_object* v_newLetDecls_162_; lean_object* v_nextExprIdx_163_; lean_object* v_exprMVarArgs_164_; lean_object* v_exprFVarArgs_165_; lean_object* v_toProcess_166_; lean_object* v___x_168_; uint8_t v_isShared_169_; uint8_t v_isSharedCheck_180_; 
v___x_150_ = lean_st_ref_get(v_a_148_);
v_nextLevelIdx_151_ = lean_ctor_get(v___x_150_, 3);
lean_inc(v_nextLevelIdx_151_);
lean_dec(v___x_150_);
v___x_152_ = ((lean_object*)(l_Lean_Meta_Closure_mkNewLevelParam___redArg___closed__1));
v___x_153_ = lean_name_append_index_after(v___x_152_, v_nextLevelIdx_151_);
v___x_154_ = lean_st_ref_take(v_a_148_);
v_visitedLevel_155_ = lean_ctor_get(v___x_154_, 0);
v_visitedExpr_156_ = lean_ctor_get(v___x_154_, 1);
v_levelParams_157_ = lean_ctor_get(v___x_154_, 2);
v_nextLevelIdx_158_ = lean_ctor_get(v___x_154_, 3);
v_levelArgs_159_ = lean_ctor_get(v___x_154_, 4);
v_newLocalDecls_160_ = lean_ctor_get(v___x_154_, 5);
v_newLocalDeclsForMVars_161_ = lean_ctor_get(v___x_154_, 6);
v_newLetDecls_162_ = lean_ctor_get(v___x_154_, 7);
v_nextExprIdx_163_ = lean_ctor_get(v___x_154_, 8);
v_exprMVarArgs_164_ = lean_ctor_get(v___x_154_, 9);
v_exprFVarArgs_165_ = lean_ctor_get(v___x_154_, 10);
v_toProcess_166_ = lean_ctor_get(v___x_154_, 11);
v_isSharedCheck_180_ = !lean_is_exclusive(v___x_154_);
if (v_isSharedCheck_180_ == 0)
{
v___x_168_ = v___x_154_;
v_isShared_169_ = v_isSharedCheck_180_;
goto v_resetjp_167_;
}
else
{
lean_inc(v_toProcess_166_);
lean_inc(v_exprFVarArgs_165_);
lean_inc(v_exprMVarArgs_164_);
lean_inc(v_nextExprIdx_163_);
lean_inc(v_newLetDecls_162_);
lean_inc(v_newLocalDeclsForMVars_161_);
lean_inc(v_newLocalDecls_160_);
lean_inc(v_levelArgs_159_);
lean_inc(v_nextLevelIdx_158_);
lean_inc(v_levelParams_157_);
lean_inc(v_visitedExpr_156_);
lean_inc(v_visitedLevel_155_);
lean_dec(v___x_154_);
v___x_168_ = lean_box(0);
v_isShared_169_ = v_isSharedCheck_180_;
goto v_resetjp_167_;
}
v_resetjp_167_:
{
lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_175_; 
lean_inc(v___x_153_);
v___x_170_ = lean_array_push(v_levelParams_157_, v___x_153_);
v___x_171_ = lean_unsigned_to_nat(1u);
v___x_172_ = lean_nat_add(v_nextLevelIdx_158_, v___x_171_);
lean_dec(v_nextLevelIdx_158_);
v___x_173_ = lean_array_push(v_levelArgs_159_, v_u_147_);
if (v_isShared_169_ == 0)
{
lean_ctor_set(v___x_168_, 4, v___x_173_);
lean_ctor_set(v___x_168_, 3, v___x_172_);
lean_ctor_set(v___x_168_, 2, v___x_170_);
v___x_175_ = v___x_168_;
goto v_reusejp_174_;
}
else
{
lean_object* v_reuseFailAlloc_179_; 
v_reuseFailAlloc_179_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_179_, 0, v_visitedLevel_155_);
lean_ctor_set(v_reuseFailAlloc_179_, 1, v_visitedExpr_156_);
lean_ctor_set(v_reuseFailAlloc_179_, 2, v___x_170_);
lean_ctor_set(v_reuseFailAlloc_179_, 3, v___x_172_);
lean_ctor_set(v_reuseFailAlloc_179_, 4, v___x_173_);
lean_ctor_set(v_reuseFailAlloc_179_, 5, v_newLocalDecls_160_);
lean_ctor_set(v_reuseFailAlloc_179_, 6, v_newLocalDeclsForMVars_161_);
lean_ctor_set(v_reuseFailAlloc_179_, 7, v_newLetDecls_162_);
lean_ctor_set(v_reuseFailAlloc_179_, 8, v_nextExprIdx_163_);
lean_ctor_set(v_reuseFailAlloc_179_, 9, v_exprMVarArgs_164_);
lean_ctor_set(v_reuseFailAlloc_179_, 10, v_exprFVarArgs_165_);
lean_ctor_set(v_reuseFailAlloc_179_, 11, v_toProcess_166_);
v___x_175_ = v_reuseFailAlloc_179_;
goto v_reusejp_174_;
}
v_reusejp_174_:
{
lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; 
v___x_176_ = lean_st_ref_put(v_a_148_, v___x_175_);
v___x_177_ = l_Lean_mkLevelParam(v___x_153_);
v___x_178_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_178_, 0, v___x_177_);
return v___x_178_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkNewLevelParam___redArg___boxed(lean_object* v_u_181_, lean_object* v_a_182_, lean_object* v_a_183_){
_start:
{
lean_object* v_res_184_; 
v_res_184_ = l_Lean_Meta_Closure_mkNewLevelParam___redArg(v_u_181_, v_a_182_);
lean_dec(v_a_182_);
return v_res_184_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkNewLevelParam(lean_object* v_u_185_, lean_object* v_a_186_, lean_object* v_a_187_, lean_object* v_a_188_, lean_object* v_a_189_, lean_object* v_a_190_, lean_object* v_a_191_){
_start:
{
lean_object* v___x_193_; 
v___x_193_ = l_Lean_Meta_Closure_mkNewLevelParam___redArg(v_u_185_, v_a_187_);
return v___x_193_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkNewLevelParam___boxed(lean_object* v_u_194_, lean_object* v_a_195_, lean_object* v_a_196_, lean_object* v_a_197_, lean_object* v_a_198_, lean_object* v_a_199_, lean_object* v_a_200_, lean_object* v_a_201_){
_start:
{
lean_object* v_res_202_; 
v_res_202_ = l_Lean_Meta_Closure_mkNewLevelParam(v_u_194_, v_a_195_, v_a_196_, v_a_197_, v_a_198_, v_a_199_, v_a_200_);
lean_dec(v_a_200_);
lean_dec_ref(v_a_199_);
lean_dec(v_a_198_);
lean_dec_ref(v_a_197_);
lean_dec(v_a_196_);
lean_dec_ref(v_a_195_);
return v_res_202_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Closure_collectLevelAux_spec__0(lean_object* v_msg_203_){
_start:
{
lean_object* v___x_204_; lean_object* v___x_205_; 
v___x_204_ = lean_box(0);
v___x_205_ = lean_panic_fn_borrowed(v___x_204_, v_msg_203_);
return v___x_205_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectLevelAux_spec__1_spec__1___redArg(lean_object* v_a_206_, lean_object* v_x_207_){
_start:
{
if (lean_obj_tag(v_x_207_) == 0)
{
lean_object* v___x_208_; 
v___x_208_ = lean_box(0);
return v___x_208_;
}
else
{
lean_object* v_key_209_; lean_object* v_value_210_; lean_object* v_tail_211_; uint8_t v___x_212_; 
v_key_209_ = lean_ctor_get(v_x_207_, 0);
v_value_210_ = lean_ctor_get(v_x_207_, 1);
v_tail_211_ = lean_ctor_get(v_x_207_, 2);
v___x_212_ = lean_level_eq(v_key_209_, v_a_206_);
if (v___x_212_ == 0)
{
v_x_207_ = v_tail_211_;
goto _start;
}
else
{
lean_object* v___x_214_; 
lean_inc(v_value_210_);
v___x_214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_214_, 0, v_value_210_);
return v___x_214_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectLevelAux_spec__1_spec__1___redArg___boxed(lean_object* v_a_215_, lean_object* v_x_216_){
_start:
{
lean_object* v_res_217_; 
v_res_217_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectLevelAux_spec__1_spec__1___redArg(v_a_215_, v_x_216_);
lean_dec(v_x_216_);
lean_dec(v_a_215_);
return v_res_217_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectLevelAux_spec__1___redArg(lean_object* v_m_218_, lean_object* v_a_219_){
_start:
{
lean_object* v_buckets_220_; lean_object* v___x_221_; uint64_t v___x_222_; uint64_t v___x_223_; uint64_t v___x_224_; uint64_t v_fold_225_; uint64_t v___x_226_; uint64_t v___x_227_; uint64_t v___x_228_; size_t v___x_229_; size_t v___x_230_; size_t v___x_231_; size_t v___x_232_; size_t v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; 
v_buckets_220_ = lean_ctor_get(v_m_218_, 1);
v___x_221_ = lean_array_get_size(v_buckets_220_);
v___x_222_ = l_Lean_Level_hash(v_a_219_);
v___x_223_ = 32ULL;
v___x_224_ = lean_uint64_shift_right(v___x_222_, v___x_223_);
v_fold_225_ = lean_uint64_xor(v___x_222_, v___x_224_);
v___x_226_ = 16ULL;
v___x_227_ = lean_uint64_shift_right(v_fold_225_, v___x_226_);
v___x_228_ = lean_uint64_xor(v_fold_225_, v___x_227_);
v___x_229_ = lean_uint64_to_usize(v___x_228_);
v___x_230_ = lean_usize_of_nat(v___x_221_);
v___x_231_ = ((size_t)1ULL);
v___x_232_ = lean_usize_sub(v___x_230_, v___x_231_);
v___x_233_ = lean_usize_land(v___x_229_, v___x_232_);
v___x_234_ = lean_array_uget_borrowed(v_buckets_220_, v___x_233_);
v___x_235_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectLevelAux_spec__1_spec__1___redArg(v_a_219_, v___x_234_);
return v___x_235_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectLevelAux_spec__1___redArg___boxed(lean_object* v_m_236_, lean_object* v_a_237_){
_start:
{
lean_object* v_res_238_; 
v_res_238_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectLevelAux_spec__1___redArg(v_m_236_, v_a_237_);
lean_dec(v_a_237_);
lean_dec_ref(v_m_236_);
return v_res_238_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__4_spec__5_spec__6___redArg(lean_object* v_x_239_, lean_object* v_x_240_){
_start:
{
if (lean_obj_tag(v_x_240_) == 0)
{
return v_x_239_;
}
else
{
lean_object* v_key_241_; lean_object* v_value_242_; lean_object* v_tail_243_; lean_object* v___x_245_; uint8_t v_isShared_246_; uint8_t v_isSharedCheck_266_; 
v_key_241_ = lean_ctor_get(v_x_240_, 0);
v_value_242_ = lean_ctor_get(v_x_240_, 1);
v_tail_243_ = lean_ctor_get(v_x_240_, 2);
v_isSharedCheck_266_ = !lean_is_exclusive(v_x_240_);
if (v_isSharedCheck_266_ == 0)
{
v___x_245_ = v_x_240_;
v_isShared_246_ = v_isSharedCheck_266_;
goto v_resetjp_244_;
}
else
{
lean_inc(v_tail_243_);
lean_inc(v_value_242_);
lean_inc(v_key_241_);
lean_dec(v_x_240_);
v___x_245_ = lean_box(0);
v_isShared_246_ = v_isSharedCheck_266_;
goto v_resetjp_244_;
}
v_resetjp_244_:
{
lean_object* v___x_247_; uint64_t v___x_248_; uint64_t v___x_249_; uint64_t v___x_250_; uint64_t v_fold_251_; uint64_t v___x_252_; uint64_t v___x_253_; uint64_t v___x_254_; size_t v___x_255_; size_t v___x_256_; size_t v___x_257_; size_t v___x_258_; size_t v___x_259_; lean_object* v___x_260_; lean_object* v___x_262_; 
v___x_247_ = lean_array_get_size(v_x_239_);
v___x_248_ = l_Lean_Level_hash(v_key_241_);
v___x_249_ = 32ULL;
v___x_250_ = lean_uint64_shift_right(v___x_248_, v___x_249_);
v_fold_251_ = lean_uint64_xor(v___x_248_, v___x_250_);
v___x_252_ = 16ULL;
v___x_253_ = lean_uint64_shift_right(v_fold_251_, v___x_252_);
v___x_254_ = lean_uint64_xor(v_fold_251_, v___x_253_);
v___x_255_ = lean_uint64_to_usize(v___x_254_);
v___x_256_ = lean_usize_of_nat(v___x_247_);
v___x_257_ = ((size_t)1ULL);
v___x_258_ = lean_usize_sub(v___x_256_, v___x_257_);
v___x_259_ = lean_usize_land(v___x_255_, v___x_258_);
v___x_260_ = lean_array_uget_borrowed(v_x_239_, v___x_259_);
lean_inc(v___x_260_);
if (v_isShared_246_ == 0)
{
lean_ctor_set(v___x_245_, 2, v___x_260_);
v___x_262_ = v___x_245_;
goto v_reusejp_261_;
}
else
{
lean_object* v_reuseFailAlloc_265_; 
v_reuseFailAlloc_265_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_265_, 0, v_key_241_);
lean_ctor_set(v_reuseFailAlloc_265_, 1, v_value_242_);
lean_ctor_set(v_reuseFailAlloc_265_, 2, v___x_260_);
v___x_262_ = v_reuseFailAlloc_265_;
goto v_reusejp_261_;
}
v_reusejp_261_:
{
lean_object* v___x_263_; 
v___x_263_ = lean_array_uset(v_x_239_, v___x_259_, v___x_262_);
v_x_239_ = v___x_263_;
v_x_240_ = v_tail_243_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__4_spec__5___redArg(lean_object* v_i_267_, lean_object* v_source_268_, lean_object* v_target_269_){
_start:
{
lean_object* v___x_270_; uint8_t v___x_271_; 
v___x_270_ = lean_array_get_size(v_source_268_);
v___x_271_ = lean_nat_dec_lt(v_i_267_, v___x_270_);
if (v___x_271_ == 0)
{
lean_dec_ref(v_source_268_);
lean_dec(v_i_267_);
return v_target_269_;
}
else
{
lean_object* v_es_272_; lean_object* v___x_273_; lean_object* v_source_274_; lean_object* v_target_275_; lean_object* v___x_276_; lean_object* v___x_277_; 
v_es_272_ = lean_array_fget(v_source_268_, v_i_267_);
v___x_273_ = lean_box(0);
v_source_274_ = lean_array_fset(v_source_268_, v_i_267_, v___x_273_);
v_target_275_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__4_spec__5_spec__6___redArg(v_target_269_, v_es_272_);
v___x_276_ = lean_unsigned_to_nat(1u);
v___x_277_ = lean_nat_add(v_i_267_, v___x_276_);
lean_dec(v_i_267_);
v_i_267_ = v___x_277_;
v_source_268_ = v_source_274_;
v_target_269_ = v_target_275_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__4___redArg(lean_object* v_data_279_){
_start:
{
lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v_nbuckets_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; 
v___x_280_ = lean_array_get_size(v_data_279_);
v___x_281_ = lean_unsigned_to_nat(2u);
v_nbuckets_282_ = lean_nat_mul(v___x_280_, v___x_281_);
v___x_283_ = lean_unsigned_to_nat(0u);
v___x_284_ = lean_box(0);
v___x_285_ = lean_mk_array(v_nbuckets_282_, v___x_284_);
v___x_286_ = lean_array_propagate_mark(v_data_279_, v___x_285_);
v___x_287_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__4_spec__5___redArg(v___x_283_, v_data_279_, v___x_286_);
return v___x_287_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__3___redArg(lean_object* v_a_288_, lean_object* v_x_289_){
_start:
{
if (lean_obj_tag(v_x_289_) == 0)
{
uint8_t v___x_290_; 
v___x_290_ = 0;
return v___x_290_;
}
else
{
lean_object* v_key_291_; lean_object* v_tail_292_; uint8_t v___x_293_; 
v_key_291_ = lean_ctor_get(v_x_289_, 0);
v_tail_292_ = lean_ctor_get(v_x_289_, 2);
v___x_293_ = lean_level_eq(v_key_291_, v_a_288_);
if (v___x_293_ == 0)
{
v_x_289_ = v_tail_292_;
goto _start;
}
else
{
return v___x_293_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__3___redArg___boxed(lean_object* v_a_295_, lean_object* v_x_296_){
_start:
{
uint8_t v_res_297_; lean_object* v_r_298_; 
v_res_297_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__3___redArg(v_a_295_, v_x_296_);
lean_dec(v_x_296_);
lean_dec(v_a_295_);
v_r_298_ = lean_box(v_res_297_);
return v_r_298_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__5___redArg(lean_object* v_a_299_, lean_object* v_b_300_, lean_object* v_x_301_){
_start:
{
if (lean_obj_tag(v_x_301_) == 0)
{
lean_dec(v_b_300_);
lean_dec(v_a_299_);
return v_x_301_;
}
else
{
lean_object* v_key_302_; lean_object* v_value_303_; lean_object* v_tail_304_; lean_object* v___x_306_; uint8_t v_isShared_307_; uint8_t v_isSharedCheck_316_; 
v_key_302_ = lean_ctor_get(v_x_301_, 0);
v_value_303_ = lean_ctor_get(v_x_301_, 1);
v_tail_304_ = lean_ctor_get(v_x_301_, 2);
v_isSharedCheck_316_ = !lean_is_exclusive(v_x_301_);
if (v_isSharedCheck_316_ == 0)
{
v___x_306_ = v_x_301_;
v_isShared_307_ = v_isSharedCheck_316_;
goto v_resetjp_305_;
}
else
{
lean_inc(v_tail_304_);
lean_inc(v_value_303_);
lean_inc(v_key_302_);
lean_dec(v_x_301_);
v___x_306_ = lean_box(0);
v_isShared_307_ = v_isSharedCheck_316_;
goto v_resetjp_305_;
}
v_resetjp_305_:
{
uint8_t v___x_308_; 
v___x_308_ = lean_level_eq(v_key_302_, v_a_299_);
if (v___x_308_ == 0)
{
lean_object* v___x_309_; lean_object* v___x_311_; 
v___x_309_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__5___redArg(v_a_299_, v_b_300_, v_tail_304_);
if (v_isShared_307_ == 0)
{
lean_ctor_set(v___x_306_, 2, v___x_309_);
v___x_311_ = v___x_306_;
goto v_reusejp_310_;
}
else
{
lean_object* v_reuseFailAlloc_312_; 
v_reuseFailAlloc_312_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_312_, 0, v_key_302_);
lean_ctor_set(v_reuseFailAlloc_312_, 1, v_value_303_);
lean_ctor_set(v_reuseFailAlloc_312_, 2, v___x_309_);
v___x_311_ = v_reuseFailAlloc_312_;
goto v_reusejp_310_;
}
v_reusejp_310_:
{
return v___x_311_;
}
}
else
{
lean_object* v___x_314_; 
lean_dec(v_value_303_);
lean_dec(v_key_302_);
if (v_isShared_307_ == 0)
{
lean_ctor_set(v___x_306_, 1, v_b_300_);
lean_ctor_set(v___x_306_, 0, v_a_299_);
v___x_314_ = v___x_306_;
goto v_reusejp_313_;
}
else
{
lean_object* v_reuseFailAlloc_315_; 
v_reuseFailAlloc_315_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_315_, 0, v_a_299_);
lean_ctor_set(v_reuseFailAlloc_315_, 1, v_b_300_);
lean_ctor_set(v_reuseFailAlloc_315_, 2, v_tail_304_);
v___x_314_ = v_reuseFailAlloc_315_;
goto v_reusejp_313_;
}
v_reusejp_313_:
{
return v___x_314_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2___redArg(lean_object* v_m_317_, lean_object* v_a_318_, lean_object* v_b_319_){
_start:
{
lean_object* v_size_320_; lean_object* v_buckets_321_; lean_object* v___x_323_; uint8_t v_isShared_324_; uint8_t v_isSharedCheck_364_; 
v_size_320_ = lean_ctor_get(v_m_317_, 0);
v_buckets_321_ = lean_ctor_get(v_m_317_, 1);
v_isSharedCheck_364_ = !lean_is_exclusive(v_m_317_);
if (v_isSharedCheck_364_ == 0)
{
v___x_323_ = v_m_317_;
v_isShared_324_ = v_isSharedCheck_364_;
goto v_resetjp_322_;
}
else
{
lean_inc(v_buckets_321_);
lean_inc(v_size_320_);
lean_dec(v_m_317_);
v___x_323_ = lean_box(0);
v_isShared_324_ = v_isSharedCheck_364_;
goto v_resetjp_322_;
}
v_resetjp_322_:
{
lean_object* v___x_325_; uint64_t v___x_326_; uint64_t v___x_327_; uint64_t v___x_328_; uint64_t v_fold_329_; uint64_t v___x_330_; uint64_t v___x_331_; uint64_t v___x_332_; size_t v___x_333_; size_t v___x_334_; size_t v___x_335_; size_t v___x_336_; size_t v___x_337_; lean_object* v_bkt_338_; uint8_t v___x_339_; 
v___x_325_ = lean_array_get_size(v_buckets_321_);
v___x_326_ = l_Lean_Level_hash(v_a_318_);
v___x_327_ = 32ULL;
v___x_328_ = lean_uint64_shift_right(v___x_326_, v___x_327_);
v_fold_329_ = lean_uint64_xor(v___x_326_, v___x_328_);
v___x_330_ = 16ULL;
v___x_331_ = lean_uint64_shift_right(v_fold_329_, v___x_330_);
v___x_332_ = lean_uint64_xor(v_fold_329_, v___x_331_);
v___x_333_ = lean_uint64_to_usize(v___x_332_);
v___x_334_ = lean_usize_of_nat(v___x_325_);
v___x_335_ = ((size_t)1ULL);
v___x_336_ = lean_usize_sub(v___x_334_, v___x_335_);
v___x_337_ = lean_usize_land(v___x_333_, v___x_336_);
v_bkt_338_ = lean_array_uget_borrowed(v_buckets_321_, v___x_337_);
v___x_339_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__3___redArg(v_a_318_, v_bkt_338_);
if (v___x_339_ == 0)
{
lean_object* v___x_340_; lean_object* v_size_x27_341_; lean_object* v___x_342_; lean_object* v_buckets_x27_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; uint8_t v___x_349_; 
v___x_340_ = lean_unsigned_to_nat(1u);
v_size_x27_341_ = lean_nat_add(v_size_320_, v___x_340_);
lean_dec(v_size_320_);
lean_inc(v_bkt_338_);
v___x_342_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_342_, 0, v_a_318_);
lean_ctor_set(v___x_342_, 1, v_b_319_);
lean_ctor_set(v___x_342_, 2, v_bkt_338_);
v_buckets_x27_343_ = lean_array_uset(v_buckets_321_, v___x_337_, v___x_342_);
v___x_344_ = lean_unsigned_to_nat(4u);
v___x_345_ = lean_nat_mul(v_size_x27_341_, v___x_344_);
v___x_346_ = lean_unsigned_to_nat(3u);
v___x_347_ = lean_nat_div(v___x_345_, v___x_346_);
lean_dec(v___x_345_);
v___x_348_ = lean_array_get_size(v_buckets_x27_343_);
v___x_349_ = lean_nat_dec_le(v___x_347_, v___x_348_);
lean_dec(v___x_347_);
if (v___x_349_ == 0)
{
lean_object* v_val_350_; lean_object* v___x_352_; 
v_val_350_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__4___redArg(v_buckets_x27_343_);
if (v_isShared_324_ == 0)
{
lean_ctor_set(v___x_323_, 1, v_val_350_);
lean_ctor_set(v___x_323_, 0, v_size_x27_341_);
v___x_352_ = v___x_323_;
goto v_reusejp_351_;
}
else
{
lean_object* v_reuseFailAlloc_353_; 
v_reuseFailAlloc_353_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_353_, 0, v_size_x27_341_);
lean_ctor_set(v_reuseFailAlloc_353_, 1, v_val_350_);
v___x_352_ = v_reuseFailAlloc_353_;
goto v_reusejp_351_;
}
v_reusejp_351_:
{
return v___x_352_;
}
}
else
{
lean_object* v___x_355_; 
if (v_isShared_324_ == 0)
{
lean_ctor_set(v___x_323_, 1, v_buckets_x27_343_);
lean_ctor_set(v___x_323_, 0, v_size_x27_341_);
v___x_355_ = v___x_323_;
goto v_reusejp_354_;
}
else
{
lean_object* v_reuseFailAlloc_356_; 
v_reuseFailAlloc_356_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_356_, 0, v_size_x27_341_);
lean_ctor_set(v_reuseFailAlloc_356_, 1, v_buckets_x27_343_);
v___x_355_ = v_reuseFailAlloc_356_;
goto v_reusejp_354_;
}
v_reusejp_354_:
{
return v___x_355_;
}
}
}
else
{
lean_object* v___x_357_; lean_object* v_buckets_x27_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_362_; 
lean_inc(v_bkt_338_);
v___x_357_ = lean_box(0);
v_buckets_x27_358_ = lean_array_uset(v_buckets_321_, v___x_337_, v___x_357_);
v___x_359_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__5___redArg(v_a_318_, v_b_319_, v_bkt_338_);
v___x_360_ = lean_array_uset(v_buckets_x27_358_, v___x_337_, v___x_359_);
if (v_isShared_324_ == 0)
{
lean_ctor_set(v___x_323_, 1, v___x_360_);
v___x_362_ = v___x_323_;
goto v_reusejp_361_;
}
else
{
lean_object* v_reuseFailAlloc_363_; 
v_reuseFailAlloc_363_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_363_, 0, v_size_320_);
lean_ctor_set(v_reuseFailAlloc_363_, 1, v___x_360_);
v___x_362_ = v_reuseFailAlloc_363_;
goto v_reusejp_361_;
}
v_reusejp_361_:
{
return v___x_362_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectLevelAux___redArg(lean_object* v_x_365_, lean_object* v_a_366_){
_start:
{
switch(lean_obj_tag(v_x_365_))
{
case 0:
{
lean_object* v___x_368_; 
v___x_368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_368_, 0, v_x_365_);
return v___x_368_;
}
case 1:
{
lean_object* v_a_369_; lean_object* v_a_371_; uint8_t v___x_408_; 
v_a_369_ = lean_ctor_get(v_x_365_, 0);
v___x_408_ = l_Lean_Level_hasMVar(v_a_369_);
if (v___x_408_ == 0)
{
uint8_t v___x_409_; 
v___x_409_ = l_Lean_Level_hasParam(v_a_369_);
if (v___x_409_ == 0)
{
lean_inc(v_a_369_);
v_a_371_ = v_a_369_;
goto v___jp_370_;
}
else
{
goto v___jp_378_;
}
}
else
{
goto v___jp_378_;
}
v___jp_370_:
{
size_t v___x_372_; size_t v___x_373_; uint8_t v___x_374_; 
v___x_372_ = lean_ptr_addr(v_a_369_);
v___x_373_ = lean_ptr_addr(v_a_371_);
v___x_374_ = lean_usize_dec_eq(v___x_372_, v___x_373_);
if (v___x_374_ == 0)
{
lean_object* v___x_375_; lean_object* v___x_376_; 
lean_dec_ref_known(v_x_365_, 1);
v___x_375_ = l_Lean_Level_succ___override(v_a_371_);
v___x_376_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_376_, 0, v___x_375_);
return v___x_376_;
}
else
{
lean_object* v___x_377_; 
lean_dec(v_a_371_);
v___x_377_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_377_, 0, v_x_365_);
return v___x_377_;
}
}
v___jp_378_:
{
lean_object* v___x_379_; lean_object* v_visitedLevel_380_; lean_object* v___x_381_; 
v___x_379_ = lean_st_ref_get(v_a_366_);
v_visitedLevel_380_ = lean_ctor_get(v___x_379_, 0);
lean_inc_ref(v_visitedLevel_380_);
lean_dec(v___x_379_);
v___x_381_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectLevelAux_spec__1___redArg(v_visitedLevel_380_, v_a_369_);
lean_dec_ref(v_visitedLevel_380_);
if (lean_obj_tag(v___x_381_) == 0)
{
lean_object* v___x_382_; 
lean_inc(v_a_369_);
v___x_382_ = l_Lean_Meta_Closure_collectLevelAux___redArg(v_a_369_, v_a_366_);
if (lean_obj_tag(v___x_382_) == 0)
{
lean_object* v_a_383_; lean_object* v___x_384_; lean_object* v_visitedLevel_385_; lean_object* v_visitedExpr_386_; lean_object* v_levelParams_387_; lean_object* v_nextLevelIdx_388_; lean_object* v_levelArgs_389_; lean_object* v_newLocalDecls_390_; lean_object* v_newLocalDeclsForMVars_391_; lean_object* v_newLetDecls_392_; lean_object* v_nextExprIdx_393_; lean_object* v_exprMVarArgs_394_; lean_object* v_exprFVarArgs_395_; lean_object* v_toProcess_396_; lean_object* v___x_398_; uint8_t v_isShared_399_; uint8_t v_isSharedCheck_405_; 
v_a_383_ = lean_ctor_get(v___x_382_, 0);
lean_inc(v_a_383_);
lean_dec_ref_known(v___x_382_, 1);
v___x_384_ = lean_st_ref_take(v_a_366_);
v_visitedLevel_385_ = lean_ctor_get(v___x_384_, 0);
v_visitedExpr_386_ = lean_ctor_get(v___x_384_, 1);
v_levelParams_387_ = lean_ctor_get(v___x_384_, 2);
v_nextLevelIdx_388_ = lean_ctor_get(v___x_384_, 3);
v_levelArgs_389_ = lean_ctor_get(v___x_384_, 4);
v_newLocalDecls_390_ = lean_ctor_get(v___x_384_, 5);
v_newLocalDeclsForMVars_391_ = lean_ctor_get(v___x_384_, 6);
v_newLetDecls_392_ = lean_ctor_get(v___x_384_, 7);
v_nextExprIdx_393_ = lean_ctor_get(v___x_384_, 8);
v_exprMVarArgs_394_ = lean_ctor_get(v___x_384_, 9);
v_exprFVarArgs_395_ = lean_ctor_get(v___x_384_, 10);
v_toProcess_396_ = lean_ctor_get(v___x_384_, 11);
v_isSharedCheck_405_ = !lean_is_exclusive(v___x_384_);
if (v_isSharedCheck_405_ == 0)
{
v___x_398_ = v___x_384_;
v_isShared_399_ = v_isSharedCheck_405_;
goto v_resetjp_397_;
}
else
{
lean_inc(v_toProcess_396_);
lean_inc(v_exprFVarArgs_395_);
lean_inc(v_exprMVarArgs_394_);
lean_inc(v_nextExprIdx_393_);
lean_inc(v_newLetDecls_392_);
lean_inc(v_newLocalDeclsForMVars_391_);
lean_inc(v_newLocalDecls_390_);
lean_inc(v_levelArgs_389_);
lean_inc(v_nextLevelIdx_388_);
lean_inc(v_levelParams_387_);
lean_inc(v_visitedExpr_386_);
lean_inc(v_visitedLevel_385_);
lean_dec(v___x_384_);
v___x_398_ = lean_box(0);
v_isShared_399_ = v_isSharedCheck_405_;
goto v_resetjp_397_;
}
v_resetjp_397_:
{
lean_object* v___x_400_; lean_object* v___x_402_; 
lean_inc(v_a_383_);
lean_inc(v_a_369_);
v___x_400_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2___redArg(v_visitedLevel_385_, v_a_369_, v_a_383_);
if (v_isShared_399_ == 0)
{
lean_ctor_set(v___x_398_, 0, v___x_400_);
v___x_402_ = v___x_398_;
goto v_reusejp_401_;
}
else
{
lean_object* v_reuseFailAlloc_404_; 
v_reuseFailAlloc_404_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_404_, 0, v___x_400_);
lean_ctor_set(v_reuseFailAlloc_404_, 1, v_visitedExpr_386_);
lean_ctor_set(v_reuseFailAlloc_404_, 2, v_levelParams_387_);
lean_ctor_set(v_reuseFailAlloc_404_, 3, v_nextLevelIdx_388_);
lean_ctor_set(v_reuseFailAlloc_404_, 4, v_levelArgs_389_);
lean_ctor_set(v_reuseFailAlloc_404_, 5, v_newLocalDecls_390_);
lean_ctor_set(v_reuseFailAlloc_404_, 6, v_newLocalDeclsForMVars_391_);
lean_ctor_set(v_reuseFailAlloc_404_, 7, v_newLetDecls_392_);
lean_ctor_set(v_reuseFailAlloc_404_, 8, v_nextExprIdx_393_);
lean_ctor_set(v_reuseFailAlloc_404_, 9, v_exprMVarArgs_394_);
lean_ctor_set(v_reuseFailAlloc_404_, 10, v_exprFVarArgs_395_);
lean_ctor_set(v_reuseFailAlloc_404_, 11, v_toProcess_396_);
v___x_402_ = v_reuseFailAlloc_404_;
goto v_reusejp_401_;
}
v_reusejp_401_:
{
lean_object* v___x_403_; 
v___x_403_ = lean_st_ref_put(v_a_366_, v___x_402_);
v_a_371_ = v_a_383_;
goto v___jp_370_;
}
}
}
else
{
if (lean_obj_tag(v___x_382_) == 0)
{
lean_object* v_a_406_; 
v_a_406_ = lean_ctor_get(v___x_382_, 0);
lean_inc(v_a_406_);
lean_dec_ref_known(v___x_382_, 1);
v_a_371_ = v_a_406_;
goto v___jp_370_;
}
else
{
lean_dec_ref_known(v_x_365_, 1);
return v___x_382_;
}
}
}
else
{
lean_object* v_val_407_; 
v_val_407_ = lean_ctor_get(v___x_381_, 0);
lean_inc(v_val_407_);
lean_dec_ref_known(v___x_381_, 1);
v_a_371_ = v_val_407_;
goto v___jp_370_;
}
}
}
case 2:
{
lean_object* v_a_410_; lean_object* v_a_411_; lean_object* v___y_413_; lean_object* v_a_414_; lean_object* v___y_428_; lean_object* v_a_459_; uint8_t v___x_492_; 
v_a_410_ = lean_ctor_get(v_x_365_, 0);
v_a_411_ = lean_ctor_get(v_x_365_, 1);
v___x_492_ = l_Lean_Level_hasMVar(v_a_410_);
if (v___x_492_ == 0)
{
uint8_t v___x_493_; 
v___x_493_ = l_Lean_Level_hasParam(v_a_410_);
if (v___x_493_ == 0)
{
lean_inc(v_a_410_);
v_a_459_ = v_a_410_;
goto v___jp_458_;
}
else
{
goto v___jp_462_;
}
}
else
{
goto v___jp_462_;
}
v___jp_412_:
{
size_t v___x_415_; size_t v___x_416_; uint8_t v___x_417_; 
v___x_415_ = lean_ptr_addr(v_a_410_);
v___x_416_ = lean_ptr_addr(v___y_413_);
v___x_417_ = lean_usize_dec_eq(v___x_415_, v___x_416_);
if (v___x_417_ == 0)
{
lean_object* v___x_418_; lean_object* v___x_419_; 
lean_dec_ref_known(v_x_365_, 2);
v___x_418_ = l_Lean_mkLevelMax_x27(v___y_413_, v_a_414_);
v___x_419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_419_, 0, v___x_418_);
return v___x_419_;
}
else
{
size_t v___x_420_; size_t v___x_421_; uint8_t v___x_422_; 
v___x_420_ = lean_ptr_addr(v_a_411_);
v___x_421_ = lean_ptr_addr(v_a_414_);
v___x_422_ = lean_usize_dec_eq(v___x_420_, v___x_421_);
if (v___x_422_ == 0)
{
lean_object* v___x_423_; lean_object* v___x_424_; 
lean_dec_ref_known(v_x_365_, 2);
v___x_423_ = l_Lean_mkLevelMax_x27(v___y_413_, v_a_414_);
v___x_424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_424_, 0, v___x_423_);
return v___x_424_;
}
else
{
lean_object* v___x_425_; lean_object* v___x_426_; 
v___x_425_ = l_Lean_simpLevelMax_x27(v___y_413_, v_a_414_, v_x_365_);
lean_dec_ref_known(v_x_365_, 2);
lean_dec(v_a_414_);
lean_dec(v___y_413_);
v___x_426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_426_, 0, v___x_425_);
return v___x_426_;
}
}
}
v___jp_427_:
{
lean_object* v___x_429_; lean_object* v_visitedLevel_430_; lean_object* v___x_431_; 
v___x_429_ = lean_st_ref_get(v_a_366_);
v_visitedLevel_430_ = lean_ctor_get(v___x_429_, 0);
lean_inc_ref(v_visitedLevel_430_);
lean_dec(v___x_429_);
v___x_431_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectLevelAux_spec__1___redArg(v_visitedLevel_430_, v_a_411_);
lean_dec_ref(v_visitedLevel_430_);
if (lean_obj_tag(v___x_431_) == 0)
{
lean_object* v___x_432_; 
lean_inc(v_a_411_);
v___x_432_ = l_Lean_Meta_Closure_collectLevelAux___redArg(v_a_411_, v_a_366_);
if (lean_obj_tag(v___x_432_) == 0)
{
lean_object* v_a_433_; lean_object* v___x_434_; lean_object* v_visitedLevel_435_; lean_object* v_visitedExpr_436_; lean_object* v_levelParams_437_; lean_object* v_nextLevelIdx_438_; lean_object* v_levelArgs_439_; lean_object* v_newLocalDecls_440_; lean_object* v_newLocalDeclsForMVars_441_; lean_object* v_newLetDecls_442_; lean_object* v_nextExprIdx_443_; lean_object* v_exprMVarArgs_444_; lean_object* v_exprFVarArgs_445_; lean_object* v_toProcess_446_; lean_object* v___x_448_; uint8_t v_isShared_449_; uint8_t v_isSharedCheck_455_; 
v_a_433_ = lean_ctor_get(v___x_432_, 0);
lean_inc(v_a_433_);
lean_dec_ref_known(v___x_432_, 1);
v___x_434_ = lean_st_ref_take(v_a_366_);
v_visitedLevel_435_ = lean_ctor_get(v___x_434_, 0);
v_visitedExpr_436_ = lean_ctor_get(v___x_434_, 1);
v_levelParams_437_ = lean_ctor_get(v___x_434_, 2);
v_nextLevelIdx_438_ = lean_ctor_get(v___x_434_, 3);
v_levelArgs_439_ = lean_ctor_get(v___x_434_, 4);
v_newLocalDecls_440_ = lean_ctor_get(v___x_434_, 5);
v_newLocalDeclsForMVars_441_ = lean_ctor_get(v___x_434_, 6);
v_newLetDecls_442_ = lean_ctor_get(v___x_434_, 7);
v_nextExprIdx_443_ = lean_ctor_get(v___x_434_, 8);
v_exprMVarArgs_444_ = lean_ctor_get(v___x_434_, 9);
v_exprFVarArgs_445_ = lean_ctor_get(v___x_434_, 10);
v_toProcess_446_ = lean_ctor_get(v___x_434_, 11);
v_isSharedCheck_455_ = !lean_is_exclusive(v___x_434_);
if (v_isSharedCheck_455_ == 0)
{
v___x_448_ = v___x_434_;
v_isShared_449_ = v_isSharedCheck_455_;
goto v_resetjp_447_;
}
else
{
lean_inc(v_toProcess_446_);
lean_inc(v_exprFVarArgs_445_);
lean_inc(v_exprMVarArgs_444_);
lean_inc(v_nextExprIdx_443_);
lean_inc(v_newLetDecls_442_);
lean_inc(v_newLocalDeclsForMVars_441_);
lean_inc(v_newLocalDecls_440_);
lean_inc(v_levelArgs_439_);
lean_inc(v_nextLevelIdx_438_);
lean_inc(v_levelParams_437_);
lean_inc(v_visitedExpr_436_);
lean_inc(v_visitedLevel_435_);
lean_dec(v___x_434_);
v___x_448_ = lean_box(0);
v_isShared_449_ = v_isSharedCheck_455_;
goto v_resetjp_447_;
}
v_resetjp_447_:
{
lean_object* v___x_450_; lean_object* v___x_452_; 
lean_inc(v_a_433_);
lean_inc(v_a_411_);
v___x_450_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2___redArg(v_visitedLevel_435_, v_a_411_, v_a_433_);
if (v_isShared_449_ == 0)
{
lean_ctor_set(v___x_448_, 0, v___x_450_);
v___x_452_ = v___x_448_;
goto v_reusejp_451_;
}
else
{
lean_object* v_reuseFailAlloc_454_; 
v_reuseFailAlloc_454_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_454_, 0, v___x_450_);
lean_ctor_set(v_reuseFailAlloc_454_, 1, v_visitedExpr_436_);
lean_ctor_set(v_reuseFailAlloc_454_, 2, v_levelParams_437_);
lean_ctor_set(v_reuseFailAlloc_454_, 3, v_nextLevelIdx_438_);
lean_ctor_set(v_reuseFailAlloc_454_, 4, v_levelArgs_439_);
lean_ctor_set(v_reuseFailAlloc_454_, 5, v_newLocalDecls_440_);
lean_ctor_set(v_reuseFailAlloc_454_, 6, v_newLocalDeclsForMVars_441_);
lean_ctor_set(v_reuseFailAlloc_454_, 7, v_newLetDecls_442_);
lean_ctor_set(v_reuseFailAlloc_454_, 8, v_nextExprIdx_443_);
lean_ctor_set(v_reuseFailAlloc_454_, 9, v_exprMVarArgs_444_);
lean_ctor_set(v_reuseFailAlloc_454_, 10, v_exprFVarArgs_445_);
lean_ctor_set(v_reuseFailAlloc_454_, 11, v_toProcess_446_);
v___x_452_ = v_reuseFailAlloc_454_;
goto v_reusejp_451_;
}
v_reusejp_451_:
{
lean_object* v___x_453_; 
v___x_453_ = lean_st_ref_put(v_a_366_, v___x_452_);
v___y_413_ = v___y_428_;
v_a_414_ = v_a_433_;
goto v___jp_412_;
}
}
}
else
{
if (lean_obj_tag(v___x_432_) == 0)
{
lean_object* v_a_456_; 
v_a_456_ = lean_ctor_get(v___x_432_, 0);
lean_inc(v_a_456_);
lean_dec_ref_known(v___x_432_, 1);
v___y_413_ = v___y_428_;
v_a_414_ = v_a_456_;
goto v___jp_412_;
}
else
{
lean_dec(v___y_428_);
lean_dec_ref_known(v_x_365_, 2);
return v___x_432_;
}
}
}
else
{
lean_object* v_val_457_; 
v_val_457_ = lean_ctor_get(v___x_431_, 0);
lean_inc(v_val_457_);
lean_dec_ref_known(v___x_431_, 1);
v___y_413_ = v___y_428_;
v_a_414_ = v_val_457_;
goto v___jp_412_;
}
}
v___jp_458_:
{
uint8_t v___x_460_; 
v___x_460_ = l_Lean_Level_hasMVar(v_a_411_);
if (v___x_460_ == 0)
{
uint8_t v___x_461_; 
v___x_461_ = l_Lean_Level_hasParam(v_a_411_);
if (v___x_461_ == 0)
{
lean_inc(v_a_411_);
v___y_413_ = v_a_459_;
v_a_414_ = v_a_411_;
goto v___jp_412_;
}
else
{
v___y_428_ = v_a_459_;
goto v___jp_427_;
}
}
else
{
v___y_428_ = v_a_459_;
goto v___jp_427_;
}
}
v___jp_462_:
{
lean_object* v___x_463_; lean_object* v_visitedLevel_464_; lean_object* v___x_465_; 
v___x_463_ = lean_st_ref_get(v_a_366_);
v_visitedLevel_464_ = lean_ctor_get(v___x_463_, 0);
lean_inc_ref(v_visitedLevel_464_);
lean_dec(v___x_463_);
v___x_465_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectLevelAux_spec__1___redArg(v_visitedLevel_464_, v_a_410_);
lean_dec_ref(v_visitedLevel_464_);
if (lean_obj_tag(v___x_465_) == 0)
{
lean_object* v___x_466_; 
lean_inc(v_a_410_);
v___x_466_ = l_Lean_Meta_Closure_collectLevelAux___redArg(v_a_410_, v_a_366_);
if (lean_obj_tag(v___x_466_) == 0)
{
lean_object* v_a_467_; lean_object* v___x_468_; lean_object* v_visitedLevel_469_; lean_object* v_visitedExpr_470_; lean_object* v_levelParams_471_; lean_object* v_nextLevelIdx_472_; lean_object* v_levelArgs_473_; lean_object* v_newLocalDecls_474_; lean_object* v_newLocalDeclsForMVars_475_; lean_object* v_newLetDecls_476_; lean_object* v_nextExprIdx_477_; lean_object* v_exprMVarArgs_478_; lean_object* v_exprFVarArgs_479_; lean_object* v_toProcess_480_; lean_object* v___x_482_; uint8_t v_isShared_483_; uint8_t v_isSharedCheck_489_; 
v_a_467_ = lean_ctor_get(v___x_466_, 0);
lean_inc(v_a_467_);
lean_dec_ref_known(v___x_466_, 1);
v___x_468_ = lean_st_ref_take(v_a_366_);
v_visitedLevel_469_ = lean_ctor_get(v___x_468_, 0);
v_visitedExpr_470_ = lean_ctor_get(v___x_468_, 1);
v_levelParams_471_ = lean_ctor_get(v___x_468_, 2);
v_nextLevelIdx_472_ = lean_ctor_get(v___x_468_, 3);
v_levelArgs_473_ = lean_ctor_get(v___x_468_, 4);
v_newLocalDecls_474_ = lean_ctor_get(v___x_468_, 5);
v_newLocalDeclsForMVars_475_ = lean_ctor_get(v___x_468_, 6);
v_newLetDecls_476_ = lean_ctor_get(v___x_468_, 7);
v_nextExprIdx_477_ = lean_ctor_get(v___x_468_, 8);
v_exprMVarArgs_478_ = lean_ctor_get(v___x_468_, 9);
v_exprFVarArgs_479_ = lean_ctor_get(v___x_468_, 10);
v_toProcess_480_ = lean_ctor_get(v___x_468_, 11);
v_isSharedCheck_489_ = !lean_is_exclusive(v___x_468_);
if (v_isSharedCheck_489_ == 0)
{
v___x_482_ = v___x_468_;
v_isShared_483_ = v_isSharedCheck_489_;
goto v_resetjp_481_;
}
else
{
lean_inc(v_toProcess_480_);
lean_inc(v_exprFVarArgs_479_);
lean_inc(v_exprMVarArgs_478_);
lean_inc(v_nextExprIdx_477_);
lean_inc(v_newLetDecls_476_);
lean_inc(v_newLocalDeclsForMVars_475_);
lean_inc(v_newLocalDecls_474_);
lean_inc(v_levelArgs_473_);
lean_inc(v_nextLevelIdx_472_);
lean_inc(v_levelParams_471_);
lean_inc(v_visitedExpr_470_);
lean_inc(v_visitedLevel_469_);
lean_dec(v___x_468_);
v___x_482_ = lean_box(0);
v_isShared_483_ = v_isSharedCheck_489_;
goto v_resetjp_481_;
}
v_resetjp_481_:
{
lean_object* v___x_484_; lean_object* v___x_486_; 
lean_inc(v_a_467_);
lean_inc(v_a_410_);
v___x_484_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2___redArg(v_visitedLevel_469_, v_a_410_, v_a_467_);
if (v_isShared_483_ == 0)
{
lean_ctor_set(v___x_482_, 0, v___x_484_);
v___x_486_ = v___x_482_;
goto v_reusejp_485_;
}
else
{
lean_object* v_reuseFailAlloc_488_; 
v_reuseFailAlloc_488_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_488_, 0, v___x_484_);
lean_ctor_set(v_reuseFailAlloc_488_, 1, v_visitedExpr_470_);
lean_ctor_set(v_reuseFailAlloc_488_, 2, v_levelParams_471_);
lean_ctor_set(v_reuseFailAlloc_488_, 3, v_nextLevelIdx_472_);
lean_ctor_set(v_reuseFailAlloc_488_, 4, v_levelArgs_473_);
lean_ctor_set(v_reuseFailAlloc_488_, 5, v_newLocalDecls_474_);
lean_ctor_set(v_reuseFailAlloc_488_, 6, v_newLocalDeclsForMVars_475_);
lean_ctor_set(v_reuseFailAlloc_488_, 7, v_newLetDecls_476_);
lean_ctor_set(v_reuseFailAlloc_488_, 8, v_nextExprIdx_477_);
lean_ctor_set(v_reuseFailAlloc_488_, 9, v_exprMVarArgs_478_);
lean_ctor_set(v_reuseFailAlloc_488_, 10, v_exprFVarArgs_479_);
lean_ctor_set(v_reuseFailAlloc_488_, 11, v_toProcess_480_);
v___x_486_ = v_reuseFailAlloc_488_;
goto v_reusejp_485_;
}
v_reusejp_485_:
{
lean_object* v___x_487_; 
v___x_487_ = lean_st_ref_put(v_a_366_, v___x_486_);
v_a_459_ = v_a_467_;
goto v___jp_458_;
}
}
}
else
{
if (lean_obj_tag(v___x_466_) == 0)
{
lean_object* v_a_490_; 
v_a_490_ = lean_ctor_get(v___x_466_, 0);
lean_inc(v_a_490_);
lean_dec_ref_known(v___x_466_, 1);
v_a_459_ = v_a_490_;
goto v___jp_458_;
}
else
{
lean_dec_ref_known(v_x_365_, 2);
return v___x_466_;
}
}
}
else
{
lean_object* v_val_491_; 
v_val_491_ = lean_ctor_get(v___x_465_, 0);
lean_inc(v_val_491_);
lean_dec_ref_known(v___x_465_, 1);
v_a_459_ = v_val_491_;
goto v___jp_458_;
}
}
}
case 3:
{
lean_object* v_a_494_; lean_object* v_a_495_; lean_object* v___y_497_; lean_object* v_a_498_; lean_object* v___y_512_; lean_object* v_a_543_; uint8_t v___x_576_; 
v_a_494_ = lean_ctor_get(v_x_365_, 0);
v_a_495_ = lean_ctor_get(v_x_365_, 1);
v___x_576_ = l_Lean_Level_hasMVar(v_a_494_);
if (v___x_576_ == 0)
{
uint8_t v___x_577_; 
v___x_577_ = l_Lean_Level_hasParam(v_a_494_);
if (v___x_577_ == 0)
{
lean_inc(v_a_494_);
v_a_543_ = v_a_494_;
goto v___jp_542_;
}
else
{
goto v___jp_546_;
}
}
else
{
goto v___jp_546_;
}
v___jp_496_:
{
size_t v___x_499_; size_t v___x_500_; uint8_t v___x_501_; 
v___x_499_ = lean_ptr_addr(v_a_494_);
v___x_500_ = lean_ptr_addr(v___y_497_);
v___x_501_ = lean_usize_dec_eq(v___x_499_, v___x_500_);
if (v___x_501_ == 0)
{
lean_object* v___x_502_; lean_object* v___x_503_; 
lean_dec_ref_known(v_x_365_, 2);
v___x_502_ = l_Lean_mkLevelIMax_x27(v___y_497_, v_a_498_);
v___x_503_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_503_, 0, v___x_502_);
return v___x_503_;
}
else
{
size_t v___x_504_; size_t v___x_505_; uint8_t v___x_506_; 
v___x_504_ = lean_ptr_addr(v_a_495_);
v___x_505_ = lean_ptr_addr(v_a_498_);
v___x_506_ = lean_usize_dec_eq(v___x_504_, v___x_505_);
if (v___x_506_ == 0)
{
lean_object* v___x_507_; lean_object* v___x_508_; 
lean_dec_ref_known(v_x_365_, 2);
v___x_507_ = l_Lean_mkLevelIMax_x27(v___y_497_, v_a_498_);
v___x_508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_508_, 0, v___x_507_);
return v___x_508_;
}
else
{
lean_object* v___x_509_; lean_object* v___x_510_; 
v___x_509_ = l_Lean_simpLevelIMax_x27(v___y_497_, v_a_498_, v_x_365_);
lean_dec_ref_known(v_x_365_, 2);
v___x_510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_510_, 0, v___x_509_);
return v___x_510_;
}
}
}
v___jp_511_:
{
lean_object* v___x_513_; lean_object* v_visitedLevel_514_; lean_object* v___x_515_; 
v___x_513_ = lean_st_ref_get(v_a_366_);
v_visitedLevel_514_ = lean_ctor_get(v___x_513_, 0);
lean_inc_ref(v_visitedLevel_514_);
lean_dec(v___x_513_);
v___x_515_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectLevelAux_spec__1___redArg(v_visitedLevel_514_, v_a_495_);
lean_dec_ref(v_visitedLevel_514_);
if (lean_obj_tag(v___x_515_) == 0)
{
lean_object* v___x_516_; 
lean_inc(v_a_495_);
v___x_516_ = l_Lean_Meta_Closure_collectLevelAux___redArg(v_a_495_, v_a_366_);
if (lean_obj_tag(v___x_516_) == 0)
{
lean_object* v_a_517_; lean_object* v___x_518_; lean_object* v_visitedLevel_519_; lean_object* v_visitedExpr_520_; lean_object* v_levelParams_521_; lean_object* v_nextLevelIdx_522_; lean_object* v_levelArgs_523_; lean_object* v_newLocalDecls_524_; lean_object* v_newLocalDeclsForMVars_525_; lean_object* v_newLetDecls_526_; lean_object* v_nextExprIdx_527_; lean_object* v_exprMVarArgs_528_; lean_object* v_exprFVarArgs_529_; lean_object* v_toProcess_530_; lean_object* v___x_532_; uint8_t v_isShared_533_; uint8_t v_isSharedCheck_539_; 
v_a_517_ = lean_ctor_get(v___x_516_, 0);
lean_inc(v_a_517_);
lean_dec_ref_known(v___x_516_, 1);
v___x_518_ = lean_st_ref_take(v_a_366_);
v_visitedLevel_519_ = lean_ctor_get(v___x_518_, 0);
v_visitedExpr_520_ = lean_ctor_get(v___x_518_, 1);
v_levelParams_521_ = lean_ctor_get(v___x_518_, 2);
v_nextLevelIdx_522_ = lean_ctor_get(v___x_518_, 3);
v_levelArgs_523_ = lean_ctor_get(v___x_518_, 4);
v_newLocalDecls_524_ = lean_ctor_get(v___x_518_, 5);
v_newLocalDeclsForMVars_525_ = lean_ctor_get(v___x_518_, 6);
v_newLetDecls_526_ = lean_ctor_get(v___x_518_, 7);
v_nextExprIdx_527_ = lean_ctor_get(v___x_518_, 8);
v_exprMVarArgs_528_ = lean_ctor_get(v___x_518_, 9);
v_exprFVarArgs_529_ = lean_ctor_get(v___x_518_, 10);
v_toProcess_530_ = lean_ctor_get(v___x_518_, 11);
v_isSharedCheck_539_ = !lean_is_exclusive(v___x_518_);
if (v_isSharedCheck_539_ == 0)
{
v___x_532_ = v___x_518_;
v_isShared_533_ = v_isSharedCheck_539_;
goto v_resetjp_531_;
}
else
{
lean_inc(v_toProcess_530_);
lean_inc(v_exprFVarArgs_529_);
lean_inc(v_exprMVarArgs_528_);
lean_inc(v_nextExprIdx_527_);
lean_inc(v_newLetDecls_526_);
lean_inc(v_newLocalDeclsForMVars_525_);
lean_inc(v_newLocalDecls_524_);
lean_inc(v_levelArgs_523_);
lean_inc(v_nextLevelIdx_522_);
lean_inc(v_levelParams_521_);
lean_inc(v_visitedExpr_520_);
lean_inc(v_visitedLevel_519_);
lean_dec(v___x_518_);
v___x_532_ = lean_box(0);
v_isShared_533_ = v_isSharedCheck_539_;
goto v_resetjp_531_;
}
v_resetjp_531_:
{
lean_object* v___x_534_; lean_object* v___x_536_; 
lean_inc(v_a_517_);
lean_inc(v_a_495_);
v___x_534_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2___redArg(v_visitedLevel_519_, v_a_495_, v_a_517_);
if (v_isShared_533_ == 0)
{
lean_ctor_set(v___x_532_, 0, v___x_534_);
v___x_536_ = v___x_532_;
goto v_reusejp_535_;
}
else
{
lean_object* v_reuseFailAlloc_538_; 
v_reuseFailAlloc_538_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_538_, 0, v___x_534_);
lean_ctor_set(v_reuseFailAlloc_538_, 1, v_visitedExpr_520_);
lean_ctor_set(v_reuseFailAlloc_538_, 2, v_levelParams_521_);
lean_ctor_set(v_reuseFailAlloc_538_, 3, v_nextLevelIdx_522_);
lean_ctor_set(v_reuseFailAlloc_538_, 4, v_levelArgs_523_);
lean_ctor_set(v_reuseFailAlloc_538_, 5, v_newLocalDecls_524_);
lean_ctor_set(v_reuseFailAlloc_538_, 6, v_newLocalDeclsForMVars_525_);
lean_ctor_set(v_reuseFailAlloc_538_, 7, v_newLetDecls_526_);
lean_ctor_set(v_reuseFailAlloc_538_, 8, v_nextExprIdx_527_);
lean_ctor_set(v_reuseFailAlloc_538_, 9, v_exprMVarArgs_528_);
lean_ctor_set(v_reuseFailAlloc_538_, 10, v_exprFVarArgs_529_);
lean_ctor_set(v_reuseFailAlloc_538_, 11, v_toProcess_530_);
v___x_536_ = v_reuseFailAlloc_538_;
goto v_reusejp_535_;
}
v_reusejp_535_:
{
lean_object* v___x_537_; 
v___x_537_ = lean_st_ref_put(v_a_366_, v___x_536_);
v___y_497_ = v___y_512_;
v_a_498_ = v_a_517_;
goto v___jp_496_;
}
}
}
else
{
if (lean_obj_tag(v___x_516_) == 0)
{
lean_object* v_a_540_; 
v_a_540_ = lean_ctor_get(v___x_516_, 0);
lean_inc(v_a_540_);
lean_dec_ref_known(v___x_516_, 1);
v___y_497_ = v___y_512_;
v_a_498_ = v_a_540_;
goto v___jp_496_;
}
else
{
lean_dec(v___y_512_);
lean_dec_ref_known(v_x_365_, 2);
return v___x_516_;
}
}
}
else
{
lean_object* v_val_541_; 
v_val_541_ = lean_ctor_get(v___x_515_, 0);
lean_inc(v_val_541_);
lean_dec_ref_known(v___x_515_, 1);
v___y_497_ = v___y_512_;
v_a_498_ = v_val_541_;
goto v___jp_496_;
}
}
v___jp_542_:
{
uint8_t v___x_544_; 
v___x_544_ = l_Lean_Level_hasMVar(v_a_495_);
if (v___x_544_ == 0)
{
uint8_t v___x_545_; 
v___x_545_ = l_Lean_Level_hasParam(v_a_495_);
if (v___x_545_ == 0)
{
lean_inc(v_a_495_);
v___y_497_ = v_a_543_;
v_a_498_ = v_a_495_;
goto v___jp_496_;
}
else
{
v___y_512_ = v_a_543_;
goto v___jp_511_;
}
}
else
{
v___y_512_ = v_a_543_;
goto v___jp_511_;
}
}
v___jp_546_:
{
lean_object* v___x_547_; lean_object* v_visitedLevel_548_; lean_object* v___x_549_; 
v___x_547_ = lean_st_ref_get(v_a_366_);
v_visitedLevel_548_ = lean_ctor_get(v___x_547_, 0);
lean_inc_ref(v_visitedLevel_548_);
lean_dec(v___x_547_);
v___x_549_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectLevelAux_spec__1___redArg(v_visitedLevel_548_, v_a_494_);
lean_dec_ref(v_visitedLevel_548_);
if (lean_obj_tag(v___x_549_) == 0)
{
lean_object* v___x_550_; 
lean_inc(v_a_494_);
v___x_550_ = l_Lean_Meta_Closure_collectLevelAux___redArg(v_a_494_, v_a_366_);
if (lean_obj_tag(v___x_550_) == 0)
{
lean_object* v_a_551_; lean_object* v___x_552_; lean_object* v_visitedLevel_553_; lean_object* v_visitedExpr_554_; lean_object* v_levelParams_555_; lean_object* v_nextLevelIdx_556_; lean_object* v_levelArgs_557_; lean_object* v_newLocalDecls_558_; lean_object* v_newLocalDeclsForMVars_559_; lean_object* v_newLetDecls_560_; lean_object* v_nextExprIdx_561_; lean_object* v_exprMVarArgs_562_; lean_object* v_exprFVarArgs_563_; lean_object* v_toProcess_564_; lean_object* v___x_566_; uint8_t v_isShared_567_; uint8_t v_isSharedCheck_573_; 
v_a_551_ = lean_ctor_get(v___x_550_, 0);
lean_inc(v_a_551_);
lean_dec_ref_known(v___x_550_, 1);
v___x_552_ = lean_st_ref_take(v_a_366_);
v_visitedLevel_553_ = lean_ctor_get(v___x_552_, 0);
v_visitedExpr_554_ = lean_ctor_get(v___x_552_, 1);
v_levelParams_555_ = lean_ctor_get(v___x_552_, 2);
v_nextLevelIdx_556_ = lean_ctor_get(v___x_552_, 3);
v_levelArgs_557_ = lean_ctor_get(v___x_552_, 4);
v_newLocalDecls_558_ = lean_ctor_get(v___x_552_, 5);
v_newLocalDeclsForMVars_559_ = lean_ctor_get(v___x_552_, 6);
v_newLetDecls_560_ = lean_ctor_get(v___x_552_, 7);
v_nextExprIdx_561_ = lean_ctor_get(v___x_552_, 8);
v_exprMVarArgs_562_ = lean_ctor_get(v___x_552_, 9);
v_exprFVarArgs_563_ = lean_ctor_get(v___x_552_, 10);
v_toProcess_564_ = lean_ctor_get(v___x_552_, 11);
v_isSharedCheck_573_ = !lean_is_exclusive(v___x_552_);
if (v_isSharedCheck_573_ == 0)
{
v___x_566_ = v___x_552_;
v_isShared_567_ = v_isSharedCheck_573_;
goto v_resetjp_565_;
}
else
{
lean_inc(v_toProcess_564_);
lean_inc(v_exprFVarArgs_563_);
lean_inc(v_exprMVarArgs_562_);
lean_inc(v_nextExprIdx_561_);
lean_inc(v_newLetDecls_560_);
lean_inc(v_newLocalDeclsForMVars_559_);
lean_inc(v_newLocalDecls_558_);
lean_inc(v_levelArgs_557_);
lean_inc(v_nextLevelIdx_556_);
lean_inc(v_levelParams_555_);
lean_inc(v_visitedExpr_554_);
lean_inc(v_visitedLevel_553_);
lean_dec(v___x_552_);
v___x_566_ = lean_box(0);
v_isShared_567_ = v_isSharedCheck_573_;
goto v_resetjp_565_;
}
v_resetjp_565_:
{
lean_object* v___x_568_; lean_object* v___x_570_; 
lean_inc(v_a_551_);
lean_inc(v_a_494_);
v___x_568_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2___redArg(v_visitedLevel_553_, v_a_494_, v_a_551_);
if (v_isShared_567_ == 0)
{
lean_ctor_set(v___x_566_, 0, v___x_568_);
v___x_570_ = v___x_566_;
goto v_reusejp_569_;
}
else
{
lean_object* v_reuseFailAlloc_572_; 
v_reuseFailAlloc_572_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_572_, 0, v___x_568_);
lean_ctor_set(v_reuseFailAlloc_572_, 1, v_visitedExpr_554_);
lean_ctor_set(v_reuseFailAlloc_572_, 2, v_levelParams_555_);
lean_ctor_set(v_reuseFailAlloc_572_, 3, v_nextLevelIdx_556_);
lean_ctor_set(v_reuseFailAlloc_572_, 4, v_levelArgs_557_);
lean_ctor_set(v_reuseFailAlloc_572_, 5, v_newLocalDecls_558_);
lean_ctor_set(v_reuseFailAlloc_572_, 6, v_newLocalDeclsForMVars_559_);
lean_ctor_set(v_reuseFailAlloc_572_, 7, v_newLetDecls_560_);
lean_ctor_set(v_reuseFailAlloc_572_, 8, v_nextExprIdx_561_);
lean_ctor_set(v_reuseFailAlloc_572_, 9, v_exprMVarArgs_562_);
lean_ctor_set(v_reuseFailAlloc_572_, 10, v_exprFVarArgs_563_);
lean_ctor_set(v_reuseFailAlloc_572_, 11, v_toProcess_564_);
v___x_570_ = v_reuseFailAlloc_572_;
goto v_reusejp_569_;
}
v_reusejp_569_:
{
lean_object* v___x_571_; 
v___x_571_ = lean_st_ref_put(v_a_366_, v___x_570_);
v_a_543_ = v_a_551_;
goto v___jp_542_;
}
}
}
else
{
if (lean_obj_tag(v___x_550_) == 0)
{
lean_object* v_a_574_; 
v_a_574_ = lean_ctor_get(v___x_550_, 0);
lean_inc(v_a_574_);
lean_dec_ref_known(v___x_550_, 1);
v_a_543_ = v_a_574_;
goto v___jp_542_;
}
else
{
lean_dec_ref_known(v_x_365_, 2);
return v___x_550_;
}
}
}
else
{
lean_object* v_val_575_; 
v_val_575_ = lean_ctor_get(v___x_549_, 0);
lean_inc(v_val_575_);
lean_dec_ref_known(v___x_549_, 1);
v_a_543_ = v_val_575_;
goto v___jp_542_;
}
}
}
default: 
{
lean_object* v___x_578_; 
v___x_578_ = l_Lean_Meta_Closure_mkNewLevelParam___redArg(v_x_365_, v_a_366_);
return v___x_578_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectLevelAux___redArg___boxed(lean_object* v_x_579_, lean_object* v_a_580_, lean_object* v_a_581_){
_start:
{
lean_object* v_res_582_; 
v_res_582_ = l_Lean_Meta_Closure_collectLevelAux___redArg(v_x_579_, v_a_580_);
lean_dec(v_a_580_);
return v_res_582_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectLevelAux(lean_object* v_x_583_, lean_object* v_a_584_, lean_object* v_a_585_, lean_object* v_a_586_, lean_object* v_a_587_, lean_object* v_a_588_, lean_object* v_a_589_){
_start:
{
lean_object* v___x_591_; 
v___x_591_ = l_Lean_Meta_Closure_collectLevelAux___redArg(v_x_583_, v_a_585_);
return v___x_591_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectLevelAux___boxed(lean_object* v_x_592_, lean_object* v_a_593_, lean_object* v_a_594_, lean_object* v_a_595_, lean_object* v_a_596_, lean_object* v_a_597_, lean_object* v_a_598_, lean_object* v_a_599_){
_start:
{
lean_object* v_res_600_; 
v_res_600_ = l_Lean_Meta_Closure_collectLevelAux(v_x_592_, v_a_593_, v_a_594_, v_a_595_, v_a_596_, v_a_597_, v_a_598_);
lean_dec(v_a_598_);
lean_dec_ref(v_a_597_);
lean_dec(v_a_596_);
lean_dec_ref(v_a_595_);
lean_dec(v_a_594_);
lean_dec_ref(v_a_593_);
return v_res_600_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectLevelAux_spec__1(lean_object* v_00_u03b2_601_, lean_object* v_m_602_, lean_object* v_a_603_){
_start:
{
lean_object* v___x_604_; 
v___x_604_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectLevelAux_spec__1___redArg(v_m_602_, v_a_603_);
return v___x_604_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectLevelAux_spec__1___boxed(lean_object* v_00_u03b2_605_, lean_object* v_m_606_, lean_object* v_a_607_){
_start:
{
lean_object* v_res_608_; 
v_res_608_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectLevelAux_spec__1(v_00_u03b2_605_, v_m_606_, v_a_607_);
lean_dec(v_a_607_);
lean_dec_ref(v_m_606_);
return v_res_608_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2(lean_object* v_00_u03b2_609_, lean_object* v_m_610_, lean_object* v_a_611_, lean_object* v_b_612_){
_start:
{
lean_object* v___x_613_; 
v___x_613_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2___redArg(v_m_610_, v_a_611_, v_b_612_);
return v___x_613_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectLevelAux_spec__1_spec__1(lean_object* v_00_u03b2_614_, lean_object* v_a_615_, lean_object* v_x_616_){
_start:
{
lean_object* v___x_617_; 
v___x_617_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectLevelAux_spec__1_spec__1___redArg(v_a_615_, v_x_616_);
return v___x_617_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectLevelAux_spec__1_spec__1___boxed(lean_object* v_00_u03b2_618_, lean_object* v_a_619_, lean_object* v_x_620_){
_start:
{
lean_object* v_res_621_; 
v_res_621_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectLevelAux_spec__1_spec__1(v_00_u03b2_618_, v_a_619_, v_x_620_);
lean_dec(v_x_620_);
lean_dec(v_a_619_);
return v_res_621_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__3(lean_object* v_00_u03b2_622_, lean_object* v_a_623_, lean_object* v_x_624_){
_start:
{
uint8_t v___x_625_; 
v___x_625_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__3___redArg(v_a_623_, v_x_624_);
return v___x_625_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__3___boxed(lean_object* v_00_u03b2_626_, lean_object* v_a_627_, lean_object* v_x_628_){
_start:
{
uint8_t v_res_629_; lean_object* v_r_630_; 
v_res_629_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__3(v_00_u03b2_626_, v_a_627_, v_x_628_);
lean_dec(v_x_628_);
lean_dec(v_a_627_);
v_r_630_ = lean_box(v_res_629_);
return v_r_630_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__4(lean_object* v_00_u03b2_631_, lean_object* v_data_632_){
_start:
{
lean_object* v___x_633_; 
v___x_633_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__4___redArg(v_data_632_);
return v___x_633_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__5(lean_object* v_00_u03b2_634_, lean_object* v_a_635_, lean_object* v_b_636_, lean_object* v_x_637_){
_start:
{
lean_object* v___x_638_; 
v___x_638_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__5___redArg(v_a_635_, v_b_636_, v_x_637_);
return v___x_638_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_639_, lean_object* v_i_640_, lean_object* v_source_641_, lean_object* v_target_642_){
_start:
{
lean_object* v___x_643_; 
v___x_643_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__4_spec__5___redArg(v_i_640_, v_source_641_, v_target_642_);
return v___x_643_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__4_spec__5_spec__6(lean_object* v_00_u03b2_644_, lean_object* v_x_645_, lean_object* v_x_646_){
_start:
{
lean_object* v___x_647_; 
v___x_647_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__4_spec__5_spec__6___redArg(v_x_645_, v_x_646_);
return v___x_647_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectLevel___redArg(lean_object* v_u_648_, lean_object* v_a_649_){
_start:
{
uint8_t v___x_694_; 
v___x_694_ = l_Lean_Level_hasMVar(v_u_648_);
if (v___x_694_ == 0)
{
uint8_t v___x_695_; 
v___x_695_ = l_Lean_Level_hasParam(v_u_648_);
if (v___x_695_ == 0)
{
lean_object* v___x_696_; 
v___x_696_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_696_, 0, v_u_648_);
return v___x_696_;
}
else
{
goto v___jp_651_;
}
}
else
{
goto v___jp_651_;
}
v___jp_651_:
{
lean_object* v___x_652_; lean_object* v_visitedLevel_653_; lean_object* v___x_654_; 
v___x_652_ = lean_st_ref_get(v_a_649_);
v_visitedLevel_653_ = lean_ctor_get(v___x_652_, 0);
lean_inc_ref(v_visitedLevel_653_);
lean_dec(v___x_652_);
v___x_654_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectLevelAux_spec__1___redArg(v_visitedLevel_653_, v_u_648_);
lean_dec_ref(v_visitedLevel_653_);
if (lean_obj_tag(v___x_654_) == 0)
{
lean_object* v___x_655_; 
lean_inc(v_u_648_);
v___x_655_ = l_Lean_Meta_Closure_collectLevelAux___redArg(v_u_648_, v_a_649_);
if (lean_obj_tag(v___x_655_) == 0)
{
lean_object* v_a_656_; lean_object* v___x_658_; uint8_t v_isShared_659_; uint8_t v_isSharedCheck_685_; 
v_a_656_ = lean_ctor_get(v___x_655_, 0);
v_isSharedCheck_685_ = !lean_is_exclusive(v___x_655_);
if (v_isSharedCheck_685_ == 0)
{
v___x_658_ = v___x_655_;
v_isShared_659_ = v_isSharedCheck_685_;
goto v_resetjp_657_;
}
else
{
lean_inc(v_a_656_);
lean_dec(v___x_655_);
v___x_658_ = lean_box(0);
v_isShared_659_ = v_isSharedCheck_685_;
goto v_resetjp_657_;
}
v_resetjp_657_:
{
lean_object* v___x_660_; lean_object* v_visitedLevel_661_; lean_object* v_visitedExpr_662_; lean_object* v_levelParams_663_; lean_object* v_nextLevelIdx_664_; lean_object* v_levelArgs_665_; lean_object* v_newLocalDecls_666_; lean_object* v_newLocalDeclsForMVars_667_; lean_object* v_newLetDecls_668_; lean_object* v_nextExprIdx_669_; lean_object* v_exprMVarArgs_670_; lean_object* v_exprFVarArgs_671_; lean_object* v_toProcess_672_; lean_object* v___x_674_; uint8_t v_isShared_675_; uint8_t v_isSharedCheck_684_; 
v___x_660_ = lean_st_ref_take(v_a_649_);
v_visitedLevel_661_ = lean_ctor_get(v___x_660_, 0);
v_visitedExpr_662_ = lean_ctor_get(v___x_660_, 1);
v_levelParams_663_ = lean_ctor_get(v___x_660_, 2);
v_nextLevelIdx_664_ = lean_ctor_get(v___x_660_, 3);
v_levelArgs_665_ = lean_ctor_get(v___x_660_, 4);
v_newLocalDecls_666_ = lean_ctor_get(v___x_660_, 5);
v_newLocalDeclsForMVars_667_ = lean_ctor_get(v___x_660_, 6);
v_newLetDecls_668_ = lean_ctor_get(v___x_660_, 7);
v_nextExprIdx_669_ = lean_ctor_get(v___x_660_, 8);
v_exprMVarArgs_670_ = lean_ctor_get(v___x_660_, 9);
v_exprFVarArgs_671_ = lean_ctor_get(v___x_660_, 10);
v_toProcess_672_ = lean_ctor_get(v___x_660_, 11);
v_isSharedCheck_684_ = !lean_is_exclusive(v___x_660_);
if (v_isSharedCheck_684_ == 0)
{
v___x_674_ = v___x_660_;
v_isShared_675_ = v_isSharedCheck_684_;
goto v_resetjp_673_;
}
else
{
lean_inc(v_toProcess_672_);
lean_inc(v_exprFVarArgs_671_);
lean_inc(v_exprMVarArgs_670_);
lean_inc(v_nextExprIdx_669_);
lean_inc(v_newLetDecls_668_);
lean_inc(v_newLocalDeclsForMVars_667_);
lean_inc(v_newLocalDecls_666_);
lean_inc(v_levelArgs_665_);
lean_inc(v_nextLevelIdx_664_);
lean_inc(v_levelParams_663_);
lean_inc(v_visitedExpr_662_);
lean_inc(v_visitedLevel_661_);
lean_dec(v___x_660_);
v___x_674_ = lean_box(0);
v_isShared_675_ = v_isSharedCheck_684_;
goto v_resetjp_673_;
}
v_resetjp_673_:
{
lean_object* v___x_676_; lean_object* v___x_678_; 
lean_inc(v_a_656_);
v___x_676_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2___redArg(v_visitedLevel_661_, v_u_648_, v_a_656_);
if (v_isShared_675_ == 0)
{
lean_ctor_set(v___x_674_, 0, v___x_676_);
v___x_678_ = v___x_674_;
goto v_reusejp_677_;
}
else
{
lean_object* v_reuseFailAlloc_683_; 
v_reuseFailAlloc_683_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_683_, 0, v___x_676_);
lean_ctor_set(v_reuseFailAlloc_683_, 1, v_visitedExpr_662_);
lean_ctor_set(v_reuseFailAlloc_683_, 2, v_levelParams_663_);
lean_ctor_set(v_reuseFailAlloc_683_, 3, v_nextLevelIdx_664_);
lean_ctor_set(v_reuseFailAlloc_683_, 4, v_levelArgs_665_);
lean_ctor_set(v_reuseFailAlloc_683_, 5, v_newLocalDecls_666_);
lean_ctor_set(v_reuseFailAlloc_683_, 6, v_newLocalDeclsForMVars_667_);
lean_ctor_set(v_reuseFailAlloc_683_, 7, v_newLetDecls_668_);
lean_ctor_set(v_reuseFailAlloc_683_, 8, v_nextExprIdx_669_);
lean_ctor_set(v_reuseFailAlloc_683_, 9, v_exprMVarArgs_670_);
lean_ctor_set(v_reuseFailAlloc_683_, 10, v_exprFVarArgs_671_);
lean_ctor_set(v_reuseFailAlloc_683_, 11, v_toProcess_672_);
v___x_678_ = v_reuseFailAlloc_683_;
goto v_reusejp_677_;
}
v_reusejp_677_:
{
lean_object* v___x_679_; lean_object* v___x_681_; 
v___x_679_ = lean_st_ref_put(v_a_649_, v___x_678_);
if (v_isShared_659_ == 0)
{
v___x_681_ = v___x_658_;
goto v_reusejp_680_;
}
else
{
lean_object* v_reuseFailAlloc_682_; 
v_reuseFailAlloc_682_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_682_, 0, v_a_656_);
v___x_681_ = v_reuseFailAlloc_682_;
goto v_reusejp_680_;
}
v_reusejp_680_:
{
return v___x_681_;
}
}
}
}
}
else
{
lean_dec(v_u_648_);
return v___x_655_;
}
}
else
{
lean_object* v_val_686_; lean_object* v___x_688_; uint8_t v_isShared_689_; uint8_t v_isSharedCheck_693_; 
lean_dec(v_u_648_);
v_val_686_ = lean_ctor_get(v___x_654_, 0);
v_isSharedCheck_693_ = !lean_is_exclusive(v___x_654_);
if (v_isSharedCheck_693_ == 0)
{
v___x_688_ = v___x_654_;
v_isShared_689_ = v_isSharedCheck_693_;
goto v_resetjp_687_;
}
else
{
lean_inc(v_val_686_);
lean_dec(v___x_654_);
v___x_688_ = lean_box(0);
v_isShared_689_ = v_isSharedCheck_693_;
goto v_resetjp_687_;
}
v_resetjp_687_:
{
lean_object* v___x_691_; 
if (v_isShared_689_ == 0)
{
lean_ctor_set_tag(v___x_688_, 0);
v___x_691_ = v___x_688_;
goto v_reusejp_690_;
}
else
{
lean_object* v_reuseFailAlloc_692_; 
v_reuseFailAlloc_692_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_692_, 0, v_val_686_);
v___x_691_ = v_reuseFailAlloc_692_;
goto v_reusejp_690_;
}
v_reusejp_690_:
{
return v___x_691_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectLevel___redArg___boxed(lean_object* v_u_697_, lean_object* v_a_698_, lean_object* v_a_699_){
_start:
{
lean_object* v_res_700_; 
v_res_700_ = l_Lean_Meta_Closure_collectLevel___redArg(v_u_697_, v_a_698_);
lean_dec(v_a_698_);
return v_res_700_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectLevel(lean_object* v_u_701_, lean_object* v_a_702_, lean_object* v_a_703_, lean_object* v_a_704_, lean_object* v_a_705_, lean_object* v_a_706_, lean_object* v_a_707_){
_start:
{
lean_object* v___x_709_; 
v___x_709_ = l_Lean_Meta_Closure_collectLevel___redArg(v_u_701_, v_a_703_);
return v___x_709_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectLevel___boxed(lean_object* v_u_710_, lean_object* v_a_711_, lean_object* v_a_712_, lean_object* v_a_713_, lean_object* v_a_714_, lean_object* v_a_715_, lean_object* v_a_716_, lean_object* v_a_717_){
_start:
{
lean_object* v_res_718_; 
v_res_718_ = l_Lean_Meta_Closure_collectLevel(v_u_710_, v_a_711_, v_a_712_, v_a_713_, v_a_714_, v_a_715_, v_a_716_);
lean_dec(v_a_716_);
lean_dec_ref(v_a_715_);
lean_dec(v_a_714_);
lean_dec_ref(v_a_713_);
lean_dec(v_a_712_);
lean_dec_ref(v_a_711_);
return v_res_718_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Closure_preprocess_spec__0___redArg(lean_object* v_e_719_, lean_object* v___y_720_){
_start:
{
uint8_t v___x_722_; 
v___x_722_ = l_Lean_Expr_hasMVar(v_e_719_);
if (v___x_722_ == 0)
{
lean_object* v___x_723_; 
v___x_723_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_723_, 0, v_e_719_);
return v___x_723_;
}
else
{
lean_object* v___x_724_; lean_object* v_mctx_725_; lean_object* v___x_726_; lean_object* v_fst_727_; lean_object* v_snd_728_; lean_object* v___x_729_; lean_object* v_cache_730_; lean_object* v_zetaDeltaFVarIds_731_; lean_object* v_postponed_732_; lean_object* v_diag_733_; lean_object* v___x_735_; uint8_t v_isShared_736_; uint8_t v_isSharedCheck_742_; 
v___x_724_ = lean_st_ref_get(v___y_720_);
v_mctx_725_ = lean_ctor_get(v___x_724_, 0);
lean_inc_ref(v_mctx_725_);
lean_dec(v___x_724_);
v___x_726_ = l_Lean_instantiateMVarsCore(v_mctx_725_, v_e_719_);
v_fst_727_ = lean_ctor_get(v___x_726_, 0);
lean_inc(v_fst_727_);
v_snd_728_ = lean_ctor_get(v___x_726_, 1);
lean_inc(v_snd_728_);
lean_dec_ref(v___x_726_);
v___x_729_ = lean_st_ref_take(v___y_720_);
v_cache_730_ = lean_ctor_get(v___x_729_, 1);
v_zetaDeltaFVarIds_731_ = lean_ctor_get(v___x_729_, 2);
v_postponed_732_ = lean_ctor_get(v___x_729_, 3);
v_diag_733_ = lean_ctor_get(v___x_729_, 4);
v_isSharedCheck_742_ = !lean_is_exclusive(v___x_729_);
if (v_isSharedCheck_742_ == 0)
{
lean_object* v_unused_743_; 
v_unused_743_ = lean_ctor_get(v___x_729_, 0);
lean_dec(v_unused_743_);
v___x_735_ = v___x_729_;
v_isShared_736_ = v_isSharedCheck_742_;
goto v_resetjp_734_;
}
else
{
lean_inc(v_diag_733_);
lean_inc(v_postponed_732_);
lean_inc(v_zetaDeltaFVarIds_731_);
lean_inc(v_cache_730_);
lean_dec(v___x_729_);
v___x_735_ = lean_box(0);
v_isShared_736_ = v_isSharedCheck_742_;
goto v_resetjp_734_;
}
v_resetjp_734_:
{
lean_object* v___x_738_; 
if (v_isShared_736_ == 0)
{
lean_ctor_set(v___x_735_, 0, v_snd_728_);
v___x_738_ = v___x_735_;
goto v_reusejp_737_;
}
else
{
lean_object* v_reuseFailAlloc_741_; 
v_reuseFailAlloc_741_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_741_, 0, v_snd_728_);
lean_ctor_set(v_reuseFailAlloc_741_, 1, v_cache_730_);
lean_ctor_set(v_reuseFailAlloc_741_, 2, v_zetaDeltaFVarIds_731_);
lean_ctor_set(v_reuseFailAlloc_741_, 3, v_postponed_732_);
lean_ctor_set(v_reuseFailAlloc_741_, 4, v_diag_733_);
v___x_738_ = v_reuseFailAlloc_741_;
goto v_reusejp_737_;
}
v_reusejp_737_:
{
lean_object* v___x_739_; lean_object* v___x_740_; 
v___x_739_ = lean_st_ref_put(v___y_720_, v___x_738_);
v___x_740_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_740_, 0, v_fst_727_);
return v___x_740_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Closure_preprocess_spec__0___redArg___boxed(lean_object* v_e_744_, lean_object* v___y_745_, lean_object* v___y_746_){
_start:
{
lean_object* v_res_747_; 
v_res_747_ = l_Lean_instantiateMVars___at___00Lean_Meta_Closure_preprocess_spec__0___redArg(v_e_744_, v___y_745_);
lean_dec(v___y_745_);
return v_res_747_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Closure_preprocess_spec__0(lean_object* v_e_748_, lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_, lean_object* v___y_754_){
_start:
{
lean_object* v___x_756_; 
v___x_756_ = l_Lean_instantiateMVars___at___00Lean_Meta_Closure_preprocess_spec__0___redArg(v_e_748_, v___y_752_);
return v___x_756_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Closure_preprocess_spec__0___boxed(lean_object* v_e_757_, lean_object* v___y_758_, lean_object* v___y_759_, lean_object* v___y_760_, lean_object* v___y_761_, lean_object* v___y_762_, lean_object* v___y_763_, lean_object* v___y_764_){
_start:
{
lean_object* v_res_765_; 
v_res_765_ = l_Lean_instantiateMVars___at___00Lean_Meta_Closure_preprocess_spec__0(v_e_757_, v___y_758_, v___y_759_, v___y_760_, v___y_761_, v___y_762_, v___y_763_);
lean_dec(v___y_763_);
lean_dec_ref(v___y_762_);
lean_dec(v___y_761_);
lean_dec_ref(v___y_760_);
lean_dec(v___y_759_);
lean_dec_ref(v___y_758_);
return v_res_765_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_preprocess(lean_object* v_e_766_, lean_object* v_a_767_, lean_object* v_a_768_, lean_object* v_a_769_, lean_object* v_a_770_, lean_object* v_a_771_, lean_object* v_a_772_){
_start:
{
lean_object* v___x_774_; uint8_t v_zetaDelta_775_; 
v___x_774_ = l_Lean_instantiateMVars___at___00Lean_Meta_Closure_preprocess_spec__0___redArg(v_e_766_, v_a_770_);
v_zetaDelta_775_ = lean_ctor_get_uint8(v_a_767_, 0);
if (v_zetaDelta_775_ == 0)
{
uint8_t v_hasLetDecls_776_; 
v_hasLetDecls_776_ = lean_ctor_get_uint8(v_a_767_, 1);
if (v_hasLetDecls_776_ == 0)
{
return v___x_774_;
}
else
{
lean_object* v_a_777_; uint8_t v___x_778_; lean_object* v___x_779_; 
v_a_777_ = lean_ctor_get(v___x_774_, 0);
lean_inc_n(v_a_777_, 2);
lean_dec_ref(v___x_774_);
v___x_778_ = 0;
v___x_779_ = l_Lean_Meta_check(v_a_777_, v___x_778_, v_a_769_, v_a_770_, v_a_771_, v_a_772_);
if (lean_obj_tag(v___x_779_) == 0)
{
lean_object* v___x_781_; uint8_t v_isShared_782_; uint8_t v_isSharedCheck_786_; 
v_isSharedCheck_786_ = !lean_is_exclusive(v___x_779_);
if (v_isSharedCheck_786_ == 0)
{
lean_object* v_unused_787_; 
v_unused_787_ = lean_ctor_get(v___x_779_, 0);
lean_dec(v_unused_787_);
v___x_781_ = v___x_779_;
v_isShared_782_ = v_isSharedCheck_786_;
goto v_resetjp_780_;
}
else
{
lean_dec(v___x_779_);
v___x_781_ = lean_box(0);
v_isShared_782_ = v_isSharedCheck_786_;
goto v_resetjp_780_;
}
v_resetjp_780_:
{
lean_object* v___x_784_; 
if (v_isShared_782_ == 0)
{
lean_ctor_set(v___x_781_, 0, v_a_777_);
v___x_784_ = v___x_781_;
goto v_reusejp_783_;
}
else
{
lean_object* v_reuseFailAlloc_785_; 
v_reuseFailAlloc_785_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_785_, 0, v_a_777_);
v___x_784_ = v_reuseFailAlloc_785_;
goto v_reusejp_783_;
}
v_reusejp_783_:
{
return v___x_784_;
}
}
}
else
{
lean_object* v_a_788_; lean_object* v___x_790_; uint8_t v_isShared_791_; uint8_t v_isSharedCheck_795_; 
lean_dec(v_a_777_);
v_a_788_ = lean_ctor_get(v___x_779_, 0);
v_isSharedCheck_795_ = !lean_is_exclusive(v___x_779_);
if (v_isSharedCheck_795_ == 0)
{
v___x_790_ = v___x_779_;
v_isShared_791_ = v_isSharedCheck_795_;
goto v_resetjp_789_;
}
else
{
lean_inc(v_a_788_);
lean_dec(v___x_779_);
v___x_790_ = lean_box(0);
v_isShared_791_ = v_isSharedCheck_795_;
goto v_resetjp_789_;
}
v_resetjp_789_:
{
lean_object* v___x_793_; 
if (v_isShared_791_ == 0)
{
v___x_793_ = v___x_790_;
goto v_reusejp_792_;
}
else
{
lean_object* v_reuseFailAlloc_794_; 
v_reuseFailAlloc_794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_794_, 0, v_a_788_);
v___x_793_ = v_reuseFailAlloc_794_;
goto v_reusejp_792_;
}
v_reusejp_792_:
{
return v___x_793_;
}
}
}
}
}
else
{
return v___x_774_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_preprocess___boxed(lean_object* v_e_796_, lean_object* v_a_797_, lean_object* v_a_798_, lean_object* v_a_799_, lean_object* v_a_800_, lean_object* v_a_801_, lean_object* v_a_802_, lean_object* v_a_803_){
_start:
{
lean_object* v_res_804_; 
v_res_804_ = l_Lean_Meta_Closure_preprocess(v_e_796_, v_a_797_, v_a_798_, v_a_799_, v_a_800_, v_a_801_, v_a_802_);
lean_dec(v_a_802_);
lean_dec_ref(v_a_801_);
lean_dec(v_a_800_);
lean_dec_ref(v_a_799_);
lean_dec(v_a_798_);
lean_dec_ref(v_a_797_);
return v_res_804_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkNextUserName___redArg(lean_object* v_a_808_){
_start:
{
lean_object* v___x_810_; lean_object* v_nextExprIdx_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v_visitedLevel_815_; lean_object* v_visitedExpr_816_; lean_object* v_levelParams_817_; lean_object* v_nextLevelIdx_818_; lean_object* v_levelArgs_819_; lean_object* v_newLocalDecls_820_; lean_object* v_newLocalDeclsForMVars_821_; lean_object* v_newLetDecls_822_; lean_object* v_nextExprIdx_823_; lean_object* v_exprMVarArgs_824_; lean_object* v_exprFVarArgs_825_; lean_object* v_toProcess_826_; lean_object* v___x_828_; uint8_t v_isShared_829_; uint8_t v_isSharedCheck_837_; 
v___x_810_ = lean_st_ref_get(v_a_808_);
v_nextExprIdx_811_ = lean_ctor_get(v___x_810_, 8);
lean_inc(v_nextExprIdx_811_);
lean_dec(v___x_810_);
v___x_812_ = ((lean_object*)(l_Lean_Meta_Closure_mkNextUserName___redArg___closed__1));
v___x_813_ = lean_name_append_index_after(v___x_812_, v_nextExprIdx_811_);
v___x_814_ = lean_st_ref_take(v_a_808_);
v_visitedLevel_815_ = lean_ctor_get(v___x_814_, 0);
v_visitedExpr_816_ = lean_ctor_get(v___x_814_, 1);
v_levelParams_817_ = lean_ctor_get(v___x_814_, 2);
v_nextLevelIdx_818_ = lean_ctor_get(v___x_814_, 3);
v_levelArgs_819_ = lean_ctor_get(v___x_814_, 4);
v_newLocalDecls_820_ = lean_ctor_get(v___x_814_, 5);
v_newLocalDeclsForMVars_821_ = lean_ctor_get(v___x_814_, 6);
v_newLetDecls_822_ = lean_ctor_get(v___x_814_, 7);
v_nextExprIdx_823_ = lean_ctor_get(v___x_814_, 8);
v_exprMVarArgs_824_ = lean_ctor_get(v___x_814_, 9);
v_exprFVarArgs_825_ = lean_ctor_get(v___x_814_, 10);
v_toProcess_826_ = lean_ctor_get(v___x_814_, 11);
v_isSharedCheck_837_ = !lean_is_exclusive(v___x_814_);
if (v_isSharedCheck_837_ == 0)
{
v___x_828_ = v___x_814_;
v_isShared_829_ = v_isSharedCheck_837_;
goto v_resetjp_827_;
}
else
{
lean_inc(v_toProcess_826_);
lean_inc(v_exprFVarArgs_825_);
lean_inc(v_exprMVarArgs_824_);
lean_inc(v_nextExprIdx_823_);
lean_inc(v_newLetDecls_822_);
lean_inc(v_newLocalDeclsForMVars_821_);
lean_inc(v_newLocalDecls_820_);
lean_inc(v_levelArgs_819_);
lean_inc(v_nextLevelIdx_818_);
lean_inc(v_levelParams_817_);
lean_inc(v_visitedExpr_816_);
lean_inc(v_visitedLevel_815_);
lean_dec(v___x_814_);
v___x_828_ = lean_box(0);
v_isShared_829_ = v_isSharedCheck_837_;
goto v_resetjp_827_;
}
v_resetjp_827_:
{
lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_833_; 
v___x_830_ = lean_unsigned_to_nat(1u);
v___x_831_ = lean_nat_add(v_nextExprIdx_823_, v___x_830_);
lean_dec(v_nextExprIdx_823_);
if (v_isShared_829_ == 0)
{
lean_ctor_set(v___x_828_, 8, v___x_831_);
v___x_833_ = v___x_828_;
goto v_reusejp_832_;
}
else
{
lean_object* v_reuseFailAlloc_836_; 
v_reuseFailAlloc_836_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_836_, 0, v_visitedLevel_815_);
lean_ctor_set(v_reuseFailAlloc_836_, 1, v_visitedExpr_816_);
lean_ctor_set(v_reuseFailAlloc_836_, 2, v_levelParams_817_);
lean_ctor_set(v_reuseFailAlloc_836_, 3, v_nextLevelIdx_818_);
lean_ctor_set(v_reuseFailAlloc_836_, 4, v_levelArgs_819_);
lean_ctor_set(v_reuseFailAlloc_836_, 5, v_newLocalDecls_820_);
lean_ctor_set(v_reuseFailAlloc_836_, 6, v_newLocalDeclsForMVars_821_);
lean_ctor_set(v_reuseFailAlloc_836_, 7, v_newLetDecls_822_);
lean_ctor_set(v_reuseFailAlloc_836_, 8, v___x_831_);
lean_ctor_set(v_reuseFailAlloc_836_, 9, v_exprMVarArgs_824_);
lean_ctor_set(v_reuseFailAlloc_836_, 10, v_exprFVarArgs_825_);
lean_ctor_set(v_reuseFailAlloc_836_, 11, v_toProcess_826_);
v___x_833_ = v_reuseFailAlloc_836_;
goto v_reusejp_832_;
}
v_reusejp_832_:
{
lean_object* v___x_834_; lean_object* v___x_835_; 
v___x_834_ = lean_st_ref_put(v_a_808_, v___x_833_);
v___x_835_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_835_, 0, v___x_813_);
return v___x_835_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkNextUserName___redArg___boxed(lean_object* v_a_838_, lean_object* v_a_839_){
_start:
{
lean_object* v_res_840_; 
v_res_840_ = l_Lean_Meta_Closure_mkNextUserName___redArg(v_a_838_);
lean_dec(v_a_838_);
return v_res_840_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkNextUserName(lean_object* v_a_841_, lean_object* v_a_842_, lean_object* v_a_843_, lean_object* v_a_844_, lean_object* v_a_845_, lean_object* v_a_846_){
_start:
{
lean_object* v___x_848_; 
v___x_848_ = l_Lean_Meta_Closure_mkNextUserName___redArg(v_a_842_);
return v___x_848_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkNextUserName___boxed(lean_object* v_a_849_, lean_object* v_a_850_, lean_object* v_a_851_, lean_object* v_a_852_, lean_object* v_a_853_, lean_object* v_a_854_, lean_object* v_a_855_){
_start:
{
lean_object* v_res_856_; 
v_res_856_ = l_Lean_Meta_Closure_mkNextUserName(v_a_849_, v_a_850_, v_a_851_, v_a_852_, v_a_853_, v_a_854_);
lean_dec(v_a_854_);
lean_dec_ref(v_a_853_);
lean_dec(v_a_852_);
lean_dec_ref(v_a_851_);
lean_dec(v_a_850_);
lean_dec_ref(v_a_849_);
return v_res_856_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushToProcess___redArg(lean_object* v_elem_857_, lean_object* v_a_858_){
_start:
{
lean_object* v___x_860_; lean_object* v_visitedLevel_861_; lean_object* v_visitedExpr_862_; lean_object* v_levelParams_863_; lean_object* v_nextLevelIdx_864_; lean_object* v_levelArgs_865_; lean_object* v_newLocalDecls_866_; lean_object* v_newLocalDeclsForMVars_867_; lean_object* v_newLetDecls_868_; lean_object* v_nextExprIdx_869_; lean_object* v_exprMVarArgs_870_; lean_object* v_exprFVarArgs_871_; lean_object* v_toProcess_872_; lean_object* v___x_874_; uint8_t v_isShared_875_; uint8_t v_isSharedCheck_883_; 
v___x_860_ = lean_st_ref_take(v_a_858_);
v_visitedLevel_861_ = lean_ctor_get(v___x_860_, 0);
v_visitedExpr_862_ = lean_ctor_get(v___x_860_, 1);
v_levelParams_863_ = lean_ctor_get(v___x_860_, 2);
v_nextLevelIdx_864_ = lean_ctor_get(v___x_860_, 3);
v_levelArgs_865_ = lean_ctor_get(v___x_860_, 4);
v_newLocalDecls_866_ = lean_ctor_get(v___x_860_, 5);
v_newLocalDeclsForMVars_867_ = lean_ctor_get(v___x_860_, 6);
v_newLetDecls_868_ = lean_ctor_get(v___x_860_, 7);
v_nextExprIdx_869_ = lean_ctor_get(v___x_860_, 8);
v_exprMVarArgs_870_ = lean_ctor_get(v___x_860_, 9);
v_exprFVarArgs_871_ = lean_ctor_get(v___x_860_, 10);
v_toProcess_872_ = lean_ctor_get(v___x_860_, 11);
v_isSharedCheck_883_ = !lean_is_exclusive(v___x_860_);
if (v_isSharedCheck_883_ == 0)
{
v___x_874_ = v___x_860_;
v_isShared_875_ = v_isSharedCheck_883_;
goto v_resetjp_873_;
}
else
{
lean_inc(v_toProcess_872_);
lean_inc(v_exprFVarArgs_871_);
lean_inc(v_exprMVarArgs_870_);
lean_inc(v_nextExprIdx_869_);
lean_inc(v_newLetDecls_868_);
lean_inc(v_newLocalDeclsForMVars_867_);
lean_inc(v_newLocalDecls_866_);
lean_inc(v_levelArgs_865_);
lean_inc(v_nextLevelIdx_864_);
lean_inc(v_levelParams_863_);
lean_inc(v_visitedExpr_862_);
lean_inc(v_visitedLevel_861_);
lean_dec(v___x_860_);
v___x_874_ = lean_box(0);
v_isShared_875_ = v_isSharedCheck_883_;
goto v_resetjp_873_;
}
v_resetjp_873_:
{
lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_879_; 
v___x_876_ = lean_box(0);
v___x_877_ = lean_array_push(v_toProcess_872_, v_elem_857_);
if (v_isShared_875_ == 0)
{
lean_ctor_set(v___x_874_, 11, v___x_877_);
v___x_879_ = v___x_874_;
goto v_reusejp_878_;
}
else
{
lean_object* v_reuseFailAlloc_882_; 
v_reuseFailAlloc_882_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_882_, 0, v_visitedLevel_861_);
lean_ctor_set(v_reuseFailAlloc_882_, 1, v_visitedExpr_862_);
lean_ctor_set(v_reuseFailAlloc_882_, 2, v_levelParams_863_);
lean_ctor_set(v_reuseFailAlloc_882_, 3, v_nextLevelIdx_864_);
lean_ctor_set(v_reuseFailAlloc_882_, 4, v_levelArgs_865_);
lean_ctor_set(v_reuseFailAlloc_882_, 5, v_newLocalDecls_866_);
lean_ctor_set(v_reuseFailAlloc_882_, 6, v_newLocalDeclsForMVars_867_);
lean_ctor_set(v_reuseFailAlloc_882_, 7, v_newLetDecls_868_);
lean_ctor_set(v_reuseFailAlloc_882_, 8, v_nextExprIdx_869_);
lean_ctor_set(v_reuseFailAlloc_882_, 9, v_exprMVarArgs_870_);
lean_ctor_set(v_reuseFailAlloc_882_, 10, v_exprFVarArgs_871_);
lean_ctor_set(v_reuseFailAlloc_882_, 11, v___x_877_);
v___x_879_ = v_reuseFailAlloc_882_;
goto v_reusejp_878_;
}
v_reusejp_878_:
{
lean_object* v___x_880_; lean_object* v___x_881_; 
v___x_880_ = lean_st_ref_put(v_a_858_, v___x_879_);
v___x_881_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_881_, 0, v___x_876_);
return v___x_881_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushToProcess___redArg___boxed(lean_object* v_elem_884_, lean_object* v_a_885_, lean_object* v_a_886_){
_start:
{
lean_object* v_res_887_; 
v_res_887_ = l_Lean_Meta_Closure_pushToProcess___redArg(v_elem_884_, v_a_885_);
lean_dec(v_a_885_);
return v_res_887_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushToProcess(lean_object* v_elem_888_, lean_object* v_a_889_, lean_object* v_a_890_, lean_object* v_a_891_, lean_object* v_a_892_, lean_object* v_a_893_, lean_object* v_a_894_){
_start:
{
lean_object* v___x_896_; 
v___x_896_ = l_Lean_Meta_Closure_pushToProcess___redArg(v_elem_888_, v_a_890_);
return v___x_896_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushToProcess___boxed(lean_object* v_elem_897_, lean_object* v_a_898_, lean_object* v_a_899_, lean_object* v_a_900_, lean_object* v_a_901_, lean_object* v_a_902_, lean_object* v_a_903_, lean_object* v_a_904_){
_start:
{
lean_object* v_res_905_; 
v_res_905_ = l_Lean_Meta_Closure_pushToProcess(v_elem_897_, v_a_898_, v_a_899_, v_a_900_, v_a_901_, v_a_902_, v_a_903_);
lean_dec(v_a_903_);
lean_dec_ref(v_a_902_);
lean_dec(v_a_901_);
lean_dec_ref(v_a_900_);
lean_dec(v_a_899_);
lean_dec_ref(v_a_898_);
return v_res_905_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__4___redArg(lean_object* v_mvarId_906_, lean_object* v___y_907_){
_start:
{
lean_object* v___x_909_; lean_object* v_mctx_910_; lean_object* v___x_911_; lean_object* v___x_912_; 
v___x_909_ = lean_st_ref_get(v___y_907_);
v_mctx_910_ = lean_ctor_get(v___x_909_, 0);
lean_inc_ref(v_mctx_910_);
lean_dec(v___x_909_);
v___x_911_ = l_Lean_MetavarContext_getDelayedMVarAssignmentCore_x3f(v_mctx_910_, v_mvarId_906_);
lean_dec_ref(v_mctx_910_);
v___x_912_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_912_, 0, v___x_911_);
return v___x_912_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__4___redArg___boxed(lean_object* v_mvarId_913_, lean_object* v___y_914_, lean_object* v___y_915_){
_start:
{
lean_object* v_res_916_; 
v_res_916_ = l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__4___redArg(v_mvarId_913_, v___y_914_);
lean_dec(v___y_914_);
lean_dec(v_mvarId_913_);
return v_res_916_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__4(lean_object* v_mvarId_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_){
_start:
{
lean_object* v___x_925_; 
v___x_925_ = l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__4___redArg(v_mvarId_917_, v___y_921_);
return v___x_925_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__4___boxed(lean_object* v_mvarId_926_, lean_object* v___y_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_, lean_object* v___y_932_, lean_object* v___y_933_){
_start:
{
lean_object* v_res_934_; 
v_res_934_ = l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__4(v_mvarId_926_, v___y_927_, v___y_928_, v___y_929_, v___y_930_, v___y_931_, v___y_932_);
lean_dec(v___y_932_);
lean_dec_ref(v___y_931_);
lean_dec(v___y_930_);
lean_dec_ref(v___y_929_);
lean_dec(v___y_928_);
lean_dec_ref(v___y_927_);
lean_dec(v_mvarId_926_);
return v_res_934_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Closure_collectExprAux_spec__5___redArg___lam__0(lean_object* v_k_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v_b_938_, lean_object* v_c_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_, lean_object* v___y_943_){
_start:
{
lean_object* v___x_945_; 
lean_inc(v___y_943_);
lean_inc_ref(v___y_942_);
lean_inc(v___y_941_);
lean_inc_ref(v___y_940_);
lean_inc(v___y_937_);
lean_inc_ref(v___y_936_);
v___x_945_ = lean_apply_9(v_k_935_, v_b_938_, v_c_939_, v___y_936_, v___y_937_, v___y_940_, v___y_941_, v___y_942_, v___y_943_, lean_box(0));
return v___x_945_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Closure_collectExprAux_spec__5___redArg___lam__0___boxed(lean_object* v_k_946_, lean_object* v___y_947_, lean_object* v___y_948_, lean_object* v_b_949_, lean_object* v_c_950_, lean_object* v___y_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_){
_start:
{
lean_object* v_res_956_; 
v_res_956_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Closure_collectExprAux_spec__5___redArg___lam__0(v_k_946_, v___y_947_, v___y_948_, v_b_949_, v_c_950_, v___y_951_, v___y_952_, v___y_953_, v___y_954_);
lean_dec(v___y_954_);
lean_dec_ref(v___y_953_);
lean_dec(v___y_952_);
lean_dec_ref(v___y_951_);
lean_dec(v___y_948_);
lean_dec_ref(v___y_947_);
return v_res_956_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Closure_collectExprAux_spec__5___redArg(lean_object* v_type_957_, lean_object* v_maxFVars_x3f_958_, lean_object* v_k_959_, uint8_t v_cleanupAnnotations_960_, uint8_t v_whnfType_961_, lean_object* v___y_962_, lean_object* v___y_963_, lean_object* v___y_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_){
_start:
{
lean_object* v___f_969_; lean_object* v___x_970_; 
lean_inc(v___y_963_);
lean_inc_ref(v___y_962_);
v___f_969_ = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Closure_collectExprAux_spec__5___redArg___lam__0___boxed), 10, 3);
lean_closure_set(v___f_969_, 0, v_k_959_);
lean_closure_set(v___f_969_, 1, v___y_962_);
lean_closure_set(v___f_969_, 2, v___y_963_);
v___x_970_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_957_, v_maxFVars_x3f_958_, v___f_969_, v_cleanupAnnotations_960_, v_whnfType_961_, v___y_964_, v___y_965_, v___y_966_, v___y_967_);
if (lean_obj_tag(v___x_970_) == 0)
{
return v___x_970_;
}
else
{
lean_object* v_a_971_; lean_object* v___x_973_; uint8_t v_isShared_974_; uint8_t v_isSharedCheck_978_; 
v_a_971_ = lean_ctor_get(v___x_970_, 0);
v_isSharedCheck_978_ = !lean_is_exclusive(v___x_970_);
if (v_isSharedCheck_978_ == 0)
{
v___x_973_ = v___x_970_;
v_isShared_974_ = v_isSharedCheck_978_;
goto v_resetjp_972_;
}
else
{
lean_inc(v_a_971_);
lean_dec(v___x_970_);
v___x_973_ = lean_box(0);
v_isShared_974_ = v_isSharedCheck_978_;
goto v_resetjp_972_;
}
v_resetjp_972_:
{
lean_object* v___x_976_; 
if (v_isShared_974_ == 0)
{
v___x_976_ = v___x_973_;
goto v_reusejp_975_;
}
else
{
lean_object* v_reuseFailAlloc_977_; 
v_reuseFailAlloc_977_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_977_, 0, v_a_971_);
v___x_976_ = v_reuseFailAlloc_977_;
goto v_reusejp_975_;
}
v_reusejp_975_:
{
return v___x_976_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Closure_collectExprAux_spec__5___redArg___boxed(lean_object* v_type_979_, lean_object* v_maxFVars_x3f_980_, lean_object* v_k_981_, lean_object* v_cleanupAnnotations_982_, lean_object* v_whnfType_983_, lean_object* v___y_984_, lean_object* v___y_985_, lean_object* v___y_986_, lean_object* v___y_987_, lean_object* v___y_988_, lean_object* v___y_989_, lean_object* v___y_990_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_991_; uint8_t v_whnfType_boxed_992_; lean_object* v_res_993_; 
v_cleanupAnnotations_boxed_991_ = lean_unbox(v_cleanupAnnotations_982_);
v_whnfType_boxed_992_ = lean_unbox(v_whnfType_983_);
v_res_993_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Closure_collectExprAux_spec__5___redArg(v_type_979_, v_maxFVars_x3f_980_, v_k_981_, v_cleanupAnnotations_boxed_991_, v_whnfType_boxed_992_, v___y_984_, v___y_985_, v___y_986_, v___y_987_, v___y_988_, v___y_989_);
lean_dec(v___y_989_);
lean_dec_ref(v___y_988_);
lean_dec(v___y_987_);
lean_dec_ref(v___y_986_);
lean_dec(v___y_985_);
lean_dec_ref(v___y_984_);
return v_res_993_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Closure_collectExprAux_spec__5(lean_object* v_00_u03b1_994_, lean_object* v_type_995_, lean_object* v_maxFVars_x3f_996_, lean_object* v_k_997_, uint8_t v_cleanupAnnotations_998_, uint8_t v_whnfType_999_, lean_object* v___y_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_){
_start:
{
lean_object* v___x_1007_; 
v___x_1007_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Closure_collectExprAux_spec__5___redArg(v_type_995_, v_maxFVars_x3f_996_, v_k_997_, v_cleanupAnnotations_998_, v_whnfType_999_, v___y_1000_, v___y_1001_, v___y_1002_, v___y_1003_, v___y_1004_, v___y_1005_);
return v___x_1007_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Closure_collectExprAux_spec__5___boxed(lean_object* v_00_u03b1_1008_, lean_object* v_type_1009_, lean_object* v_maxFVars_x3f_1010_, lean_object* v_k_1011_, lean_object* v_cleanupAnnotations_1012_, lean_object* v_whnfType_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1021_; uint8_t v_whnfType_boxed_1022_; lean_object* v_res_1023_; 
v_cleanupAnnotations_boxed_1021_ = lean_unbox(v_cleanupAnnotations_1012_);
v_whnfType_boxed_1022_ = lean_unbox(v_whnfType_1013_);
v_res_1023_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Closure_collectExprAux_spec__5(v_00_u03b1_1008_, v_type_1009_, v_maxFVars_x3f_1010_, v_k_1011_, v_cleanupAnnotations_boxed_1021_, v_whnfType_boxed_1022_, v___y_1014_, v___y_1015_, v___y_1016_, v___y_1017_, v___y_1018_, v___y_1019_);
lean_dec(v___y_1019_);
lean_dec_ref(v___y_1018_);
lean_dec(v___y_1017_);
lean_dec_ref(v___y_1016_);
lean_dec(v___y_1015_);
lean_dec_ref(v___y_1014_);
return v_res_1023_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0_spec__0___redArg(lean_object* v_a_1024_, lean_object* v_x_1025_){
_start:
{
if (lean_obj_tag(v_x_1025_) == 0)
{
lean_object* v___x_1026_; 
v___x_1026_ = lean_box(0);
return v___x_1026_;
}
else
{
lean_object* v_key_1027_; lean_object* v_value_1028_; lean_object* v_tail_1029_; uint8_t v___x_1030_; 
v_key_1027_ = lean_ctor_get(v_x_1025_, 0);
v_value_1028_ = lean_ctor_get(v_x_1025_, 1);
v_tail_1029_ = lean_ctor_get(v_x_1025_, 2);
v___x_1030_ = l_Lean_ExprStructEq_beq(v_key_1027_, v_a_1024_);
if (v___x_1030_ == 0)
{
v_x_1025_ = v_tail_1029_;
goto _start;
}
else
{
lean_object* v___x_1032_; 
lean_inc(v_value_1028_);
v___x_1032_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1032_, 0, v_value_1028_);
return v___x_1032_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0_spec__0___redArg___boxed(lean_object* v_a_1033_, lean_object* v_x_1034_){
_start:
{
lean_object* v_res_1035_; 
v_res_1035_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0_spec__0___redArg(v_a_1033_, v_x_1034_);
lean_dec(v_x_1034_);
lean_dec_ref(v_a_1033_);
return v_res_1035_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0___redArg(lean_object* v_m_1036_, lean_object* v_a_1037_){
_start:
{
lean_object* v_buckets_1038_; lean_object* v___x_1039_; uint64_t v___x_1040_; uint64_t v___x_1041_; uint64_t v___x_1042_; uint64_t v_fold_1043_; uint64_t v___x_1044_; uint64_t v___x_1045_; uint64_t v___x_1046_; size_t v___x_1047_; size_t v___x_1048_; size_t v___x_1049_; size_t v___x_1050_; size_t v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; 
v_buckets_1038_ = lean_ctor_get(v_m_1036_, 1);
v___x_1039_ = lean_array_get_size(v_buckets_1038_);
v___x_1040_ = l_Lean_ExprStructEq_hash(v_a_1037_);
v___x_1041_ = 32ULL;
v___x_1042_ = lean_uint64_shift_right(v___x_1040_, v___x_1041_);
v_fold_1043_ = lean_uint64_xor(v___x_1040_, v___x_1042_);
v___x_1044_ = 16ULL;
v___x_1045_ = lean_uint64_shift_right(v_fold_1043_, v___x_1044_);
v___x_1046_ = lean_uint64_xor(v_fold_1043_, v___x_1045_);
v___x_1047_ = lean_uint64_to_usize(v___x_1046_);
v___x_1048_ = lean_usize_of_nat(v___x_1039_);
v___x_1049_ = ((size_t)1ULL);
v___x_1050_ = lean_usize_sub(v___x_1048_, v___x_1049_);
v___x_1051_ = lean_usize_land(v___x_1047_, v___x_1050_);
v___x_1052_ = lean_array_uget_borrowed(v_buckets_1038_, v___x_1051_);
v___x_1053_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0_spec__0___redArg(v_a_1037_, v___x_1052_);
return v___x_1053_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0___redArg___boxed(lean_object* v_m_1054_, lean_object* v_a_1055_){
_start:
{
lean_object* v_res_1056_; 
v_res_1056_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0___redArg(v_m_1054_, v_a_1055_);
lean_dec_ref(v_a_1055_);
lean_dec_ref(v_m_1054_);
return v_res_1056_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Closure_collectExprAux_spec__2___redArg(lean_object* v_x_1057_, lean_object* v_x_1058_, lean_object* v___y_1059_){
_start:
{
if (lean_obj_tag(v_x_1057_) == 0)
{
lean_object* v___x_1061_; lean_object* v___x_1062_; 
v___x_1061_ = l_List_reverse___redArg(v_x_1058_);
v___x_1062_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1062_, 0, v___x_1061_);
return v___x_1062_;
}
else
{
lean_object* v_head_1063_; lean_object* v_tail_1064_; lean_object* v___x_1066_; uint8_t v_isShared_1067_; uint8_t v_isSharedCheck_1082_; 
v_head_1063_ = lean_ctor_get(v_x_1057_, 0);
v_tail_1064_ = lean_ctor_get(v_x_1057_, 1);
v_isSharedCheck_1082_ = !lean_is_exclusive(v_x_1057_);
if (v_isSharedCheck_1082_ == 0)
{
v___x_1066_ = v_x_1057_;
v_isShared_1067_ = v_isSharedCheck_1082_;
goto v_resetjp_1065_;
}
else
{
lean_inc(v_tail_1064_);
lean_inc(v_head_1063_);
lean_dec(v_x_1057_);
v___x_1066_ = lean_box(0);
v_isShared_1067_ = v_isSharedCheck_1082_;
goto v_resetjp_1065_;
}
v_resetjp_1065_:
{
lean_object* v___x_1068_; 
v___x_1068_ = l_Lean_Meta_Closure_collectLevel___redArg(v_head_1063_, v___y_1059_);
if (lean_obj_tag(v___x_1068_) == 0)
{
lean_object* v_a_1069_; lean_object* v___x_1071_; 
v_a_1069_ = lean_ctor_get(v___x_1068_, 0);
lean_inc(v_a_1069_);
lean_dec_ref_known(v___x_1068_, 1);
if (v_isShared_1067_ == 0)
{
lean_ctor_set(v___x_1066_, 1, v_x_1058_);
lean_ctor_set(v___x_1066_, 0, v_a_1069_);
v___x_1071_ = v___x_1066_;
goto v_reusejp_1070_;
}
else
{
lean_object* v_reuseFailAlloc_1073_; 
v_reuseFailAlloc_1073_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1073_, 0, v_a_1069_);
lean_ctor_set(v_reuseFailAlloc_1073_, 1, v_x_1058_);
v___x_1071_ = v_reuseFailAlloc_1073_;
goto v_reusejp_1070_;
}
v_reusejp_1070_:
{
v_x_1057_ = v_tail_1064_;
v_x_1058_ = v___x_1071_;
goto _start;
}
}
else
{
lean_object* v_a_1074_; lean_object* v___x_1076_; uint8_t v_isShared_1077_; uint8_t v_isSharedCheck_1081_; 
lean_del_object(v___x_1066_);
lean_dec(v_tail_1064_);
lean_dec(v_x_1058_);
v_a_1074_ = lean_ctor_get(v___x_1068_, 0);
v_isSharedCheck_1081_ = !lean_is_exclusive(v___x_1068_);
if (v_isSharedCheck_1081_ == 0)
{
v___x_1076_ = v___x_1068_;
v_isShared_1077_ = v_isSharedCheck_1081_;
goto v_resetjp_1075_;
}
else
{
lean_inc(v_a_1074_);
lean_dec(v___x_1068_);
v___x_1076_ = lean_box(0);
v_isShared_1077_ = v_isSharedCheck_1081_;
goto v_resetjp_1075_;
}
v_resetjp_1075_:
{
lean_object* v___x_1079_; 
if (v_isShared_1077_ == 0)
{
v___x_1079_ = v___x_1076_;
goto v_reusejp_1078_;
}
else
{
lean_object* v_reuseFailAlloc_1080_; 
v_reuseFailAlloc_1080_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1080_, 0, v_a_1074_);
v___x_1079_ = v_reuseFailAlloc_1080_;
goto v_reusejp_1078_;
}
v_reusejp_1078_:
{
return v___x_1079_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Closure_collectExprAux_spec__2___redArg___boxed(lean_object* v_x_1083_, lean_object* v_x_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_){
_start:
{
lean_object* v_res_1087_; 
v_res_1087_ = l_List_mapM_loop___at___00Lean_Meta_Closure_collectExprAux_spec__2___redArg(v_x_1083_, v_x_1084_, v___y_1085_);
lean_dec(v___y_1085_);
return v_res_1087_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Closure_collectExprAux_spec__3_spec__7___redArg(lean_object* v___y_1088_){
_start:
{
lean_object* v___x_1090_; lean_object* v_ngen_1091_; lean_object* v_namePrefix_1092_; lean_object* v_idx_1093_; lean_object* v___x_1095_; uint8_t v_isShared_1096_; uint8_t v_isSharedCheck_1123_; 
v___x_1090_ = lean_st_ref_get(v___y_1088_);
v_ngen_1091_ = lean_ctor_get(v___x_1090_, 2);
lean_inc_ref(v_ngen_1091_);
lean_dec(v___x_1090_);
v_namePrefix_1092_ = lean_ctor_get(v_ngen_1091_, 0);
v_idx_1093_ = lean_ctor_get(v_ngen_1091_, 1);
v_isSharedCheck_1123_ = !lean_is_exclusive(v_ngen_1091_);
if (v_isSharedCheck_1123_ == 0)
{
v___x_1095_ = v_ngen_1091_;
v_isShared_1096_ = v_isSharedCheck_1123_;
goto v_resetjp_1094_;
}
else
{
lean_inc(v_idx_1093_);
lean_inc(v_namePrefix_1092_);
lean_dec(v_ngen_1091_);
v___x_1095_ = lean_box(0);
v_isShared_1096_ = v_isSharedCheck_1123_;
goto v_resetjp_1094_;
}
v_resetjp_1094_:
{
lean_object* v_r_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1101_; 
lean_inc(v_idx_1093_);
lean_inc(v_namePrefix_1092_);
v_r_1097_ = l_Lean_Name_num___override(v_namePrefix_1092_, v_idx_1093_);
v___x_1098_ = lean_unsigned_to_nat(1u);
v___x_1099_ = lean_nat_add(v_idx_1093_, v___x_1098_);
lean_dec(v_idx_1093_);
if (v_isShared_1096_ == 0)
{
lean_ctor_set(v___x_1095_, 1, v___x_1099_);
v___x_1101_ = v___x_1095_;
goto v_reusejp_1100_;
}
else
{
lean_object* v_reuseFailAlloc_1122_; 
v_reuseFailAlloc_1122_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1122_, 0, v_namePrefix_1092_);
lean_ctor_set(v_reuseFailAlloc_1122_, 1, v___x_1099_);
v___x_1101_ = v_reuseFailAlloc_1122_;
goto v_reusejp_1100_;
}
v_reusejp_1100_:
{
lean_object* v___x_1102_; lean_object* v_env_1103_; lean_object* v_nextMacroScope_1104_; lean_object* v_auxDeclNGen_1105_; lean_object* v_traceState_1106_; lean_object* v_cache_1107_; lean_object* v_recordedDeps_1108_; lean_object* v_messages_1109_; lean_object* v_infoState_1110_; lean_object* v_snapshotTasks_1111_; lean_object* v___x_1113_; uint8_t v_isShared_1114_; uint8_t v_isSharedCheck_1120_; 
v___x_1102_ = lean_st_ref_take(v___y_1088_);
v_env_1103_ = lean_ctor_get(v___x_1102_, 0);
v_nextMacroScope_1104_ = lean_ctor_get(v___x_1102_, 1);
v_auxDeclNGen_1105_ = lean_ctor_get(v___x_1102_, 3);
v_traceState_1106_ = lean_ctor_get(v___x_1102_, 4);
v_cache_1107_ = lean_ctor_get(v___x_1102_, 5);
v_recordedDeps_1108_ = lean_ctor_get(v___x_1102_, 6);
v_messages_1109_ = lean_ctor_get(v___x_1102_, 7);
v_infoState_1110_ = lean_ctor_get(v___x_1102_, 8);
v_snapshotTasks_1111_ = lean_ctor_get(v___x_1102_, 9);
v_isSharedCheck_1120_ = !lean_is_exclusive(v___x_1102_);
if (v_isSharedCheck_1120_ == 0)
{
lean_object* v_unused_1121_; 
v_unused_1121_ = lean_ctor_get(v___x_1102_, 2);
lean_dec(v_unused_1121_);
v___x_1113_ = v___x_1102_;
v_isShared_1114_ = v_isSharedCheck_1120_;
goto v_resetjp_1112_;
}
else
{
lean_inc(v_snapshotTasks_1111_);
lean_inc(v_infoState_1110_);
lean_inc(v_messages_1109_);
lean_inc(v_recordedDeps_1108_);
lean_inc(v_cache_1107_);
lean_inc(v_traceState_1106_);
lean_inc(v_auxDeclNGen_1105_);
lean_inc(v_nextMacroScope_1104_);
lean_inc(v_env_1103_);
lean_dec(v___x_1102_);
v___x_1113_ = lean_box(0);
v_isShared_1114_ = v_isSharedCheck_1120_;
goto v_resetjp_1112_;
}
v_resetjp_1112_:
{
lean_object* v___x_1116_; 
if (v_isShared_1114_ == 0)
{
lean_ctor_set(v___x_1113_, 2, v___x_1101_);
v___x_1116_ = v___x_1113_;
goto v_reusejp_1115_;
}
else
{
lean_object* v_reuseFailAlloc_1119_; 
v_reuseFailAlloc_1119_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1119_, 0, v_env_1103_);
lean_ctor_set(v_reuseFailAlloc_1119_, 1, v_nextMacroScope_1104_);
lean_ctor_set(v_reuseFailAlloc_1119_, 2, v___x_1101_);
lean_ctor_set(v_reuseFailAlloc_1119_, 3, v_auxDeclNGen_1105_);
lean_ctor_set(v_reuseFailAlloc_1119_, 4, v_traceState_1106_);
lean_ctor_set(v_reuseFailAlloc_1119_, 5, v_cache_1107_);
lean_ctor_set(v_reuseFailAlloc_1119_, 6, v_recordedDeps_1108_);
lean_ctor_set(v_reuseFailAlloc_1119_, 7, v_messages_1109_);
lean_ctor_set(v_reuseFailAlloc_1119_, 8, v_infoState_1110_);
lean_ctor_set(v_reuseFailAlloc_1119_, 9, v_snapshotTasks_1111_);
v___x_1116_ = v_reuseFailAlloc_1119_;
goto v_reusejp_1115_;
}
v_reusejp_1115_:
{
lean_object* v___x_1117_; lean_object* v___x_1118_; 
v___x_1117_ = lean_st_ref_put(v___y_1088_, v___x_1116_);
v___x_1118_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1118_, 0, v_r_1097_);
return v___x_1118_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Closure_collectExprAux_spec__3_spec__7___redArg___boxed(lean_object* v___y_1124_, lean_object* v___y_1125_){
_start:
{
lean_object* v_res_1126_; 
v_res_1126_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Closure_collectExprAux_spec__3_spec__7___redArg(v___y_1124_);
lean_dec(v___y_1124_);
return v_res_1126_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00Lean_Meta_Closure_collectExprAux_spec__3(lean_object* v___y_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_){
_start:
{
lean_object* v___x_1134_; lean_object* v_a_1135_; lean_object* v___x_1137_; uint8_t v_isShared_1138_; uint8_t v_isSharedCheck_1142_; 
v___x_1134_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Closure_collectExprAux_spec__3_spec__7___redArg(v___y_1132_);
v_a_1135_ = lean_ctor_get(v___x_1134_, 0);
v_isSharedCheck_1142_ = !lean_is_exclusive(v___x_1134_);
if (v_isSharedCheck_1142_ == 0)
{
v___x_1137_ = v___x_1134_;
v_isShared_1138_ = v_isSharedCheck_1142_;
goto v_resetjp_1136_;
}
else
{
lean_inc(v_a_1135_);
lean_dec(v___x_1134_);
v___x_1137_ = lean_box(0);
v_isShared_1138_ = v_isSharedCheck_1142_;
goto v_resetjp_1136_;
}
v_resetjp_1136_:
{
lean_object* v___x_1140_; 
if (v_isShared_1138_ == 0)
{
v___x_1140_ = v___x_1137_;
goto v_reusejp_1139_;
}
else
{
lean_object* v_reuseFailAlloc_1141_; 
v_reuseFailAlloc_1141_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1141_, 0, v_a_1135_);
v___x_1140_ = v_reuseFailAlloc_1141_;
goto v_reusejp_1139_;
}
v_reusejp_1139_:
{
return v___x_1140_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00Lean_Meta_Closure_collectExprAux_spec__3___boxed(lean_object* v___y_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_){
_start:
{
lean_object* v_res_1150_; 
v_res_1150_ = l_Lean_mkFreshFVarId___at___00Lean_Meta_Closure_collectExprAux_spec__3(v___y_1143_, v___y_1144_, v___y_1145_, v___y_1146_, v___y_1147_, v___y_1148_);
lean_dec(v___y_1148_);
lean_dec_ref(v___y_1147_);
lean_dec(v___y_1146_);
lean_dec_ref(v___y_1145_);
lean_dec(v___y_1144_);
lean_dec_ref(v___y_1143_);
return v_res_1150_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectExprAux___lam__1(lean_object* v_e_1151_, lean_object* v_args_1152_, lean_object* v_x_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_){
_start:
{
lean_object* v___x_1161_; uint8_t v___x_1162_; uint8_t v___x_1163_; uint8_t v___x_1164_; lean_object* v___x_1165_; 
v___x_1161_ = l_Lean_mkAppN(v_e_1151_, v_args_1152_);
v___x_1162_ = 0;
v___x_1163_ = 1;
v___x_1164_ = 1;
v___x_1165_ = l_Lean_Meta_mkLambdaFVars(v_args_1152_, v___x_1161_, v___x_1162_, v___x_1163_, v___x_1162_, v___x_1163_, v___x_1164_, v___y_1156_, v___y_1157_, v___y_1158_, v___y_1159_);
return v___x_1165_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectExprAux___lam__1___boxed(lean_object* v_e_1166_, lean_object* v_args_1167_, lean_object* v_x_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_){
_start:
{
lean_object* v_res_1176_; 
v_res_1176_ = l_Lean_Meta_Closure_collectExprAux___lam__1(v_e_1166_, v_args_1167_, v_x_1168_, v___y_1169_, v___y_1170_, v___y_1171_, v___y_1172_, v___y_1173_, v___y_1174_);
lean_dec(v___y_1174_);
lean_dec_ref(v___y_1173_);
lean_dec(v___y_1172_);
lean_dec_ref(v___y_1171_);
lean_dec(v___y_1170_);
lean_dec_ref(v___y_1169_);
lean_dec_ref(v_x_1168_);
lean_dec_ref(v_args_1167_);
return v_res_1176_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__3_spec__6_spec__10___redArg(lean_object* v_x_1177_, lean_object* v_x_1178_){
_start:
{
if (lean_obj_tag(v_x_1178_) == 0)
{
return v_x_1177_;
}
else
{
lean_object* v_key_1179_; lean_object* v_value_1180_; lean_object* v_tail_1181_; lean_object* v___x_1183_; uint8_t v_isShared_1184_; uint8_t v_isSharedCheck_1204_; 
v_key_1179_ = lean_ctor_get(v_x_1178_, 0);
v_value_1180_ = lean_ctor_get(v_x_1178_, 1);
v_tail_1181_ = lean_ctor_get(v_x_1178_, 2);
v_isSharedCheck_1204_ = !lean_is_exclusive(v_x_1178_);
if (v_isSharedCheck_1204_ == 0)
{
v___x_1183_ = v_x_1178_;
v_isShared_1184_ = v_isSharedCheck_1204_;
goto v_resetjp_1182_;
}
else
{
lean_inc(v_tail_1181_);
lean_inc(v_value_1180_);
lean_inc(v_key_1179_);
lean_dec(v_x_1178_);
v___x_1183_ = lean_box(0);
v_isShared_1184_ = v_isSharedCheck_1204_;
goto v_resetjp_1182_;
}
v_resetjp_1182_:
{
lean_object* v___x_1185_; uint64_t v___x_1186_; uint64_t v___x_1187_; uint64_t v___x_1188_; uint64_t v_fold_1189_; uint64_t v___x_1190_; uint64_t v___x_1191_; uint64_t v___x_1192_; size_t v___x_1193_; size_t v___x_1194_; size_t v___x_1195_; size_t v___x_1196_; size_t v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1200_; 
v___x_1185_ = lean_array_get_size(v_x_1177_);
v___x_1186_ = l_Lean_ExprStructEq_hash(v_key_1179_);
v___x_1187_ = 32ULL;
v___x_1188_ = lean_uint64_shift_right(v___x_1186_, v___x_1187_);
v_fold_1189_ = lean_uint64_xor(v___x_1186_, v___x_1188_);
v___x_1190_ = 16ULL;
v___x_1191_ = lean_uint64_shift_right(v_fold_1189_, v___x_1190_);
v___x_1192_ = lean_uint64_xor(v_fold_1189_, v___x_1191_);
v___x_1193_ = lean_uint64_to_usize(v___x_1192_);
v___x_1194_ = lean_usize_of_nat(v___x_1185_);
v___x_1195_ = ((size_t)1ULL);
v___x_1196_ = lean_usize_sub(v___x_1194_, v___x_1195_);
v___x_1197_ = lean_usize_land(v___x_1193_, v___x_1196_);
v___x_1198_ = lean_array_uget_borrowed(v_x_1177_, v___x_1197_);
lean_inc(v___x_1198_);
if (v_isShared_1184_ == 0)
{
lean_ctor_set(v___x_1183_, 2, v___x_1198_);
v___x_1200_ = v___x_1183_;
goto v_reusejp_1199_;
}
else
{
lean_object* v_reuseFailAlloc_1203_; 
v_reuseFailAlloc_1203_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1203_, 0, v_key_1179_);
lean_ctor_set(v_reuseFailAlloc_1203_, 1, v_value_1180_);
lean_ctor_set(v_reuseFailAlloc_1203_, 2, v___x_1198_);
v___x_1200_ = v_reuseFailAlloc_1203_;
goto v_reusejp_1199_;
}
v_reusejp_1199_:
{
lean_object* v___x_1201_; 
v___x_1201_ = lean_array_uset(v_x_1177_, v___x_1197_, v___x_1200_);
v_x_1177_ = v___x_1201_;
v_x_1178_ = v_tail_1181_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__3_spec__6___redArg(lean_object* v_i_1205_, lean_object* v_source_1206_, lean_object* v_target_1207_){
_start:
{
lean_object* v___x_1208_; uint8_t v___x_1209_; 
v___x_1208_ = lean_array_get_size(v_source_1206_);
v___x_1209_ = lean_nat_dec_lt(v_i_1205_, v___x_1208_);
if (v___x_1209_ == 0)
{
lean_dec_ref(v_source_1206_);
lean_dec(v_i_1205_);
return v_target_1207_;
}
else
{
lean_object* v_es_1210_; lean_object* v___x_1211_; lean_object* v_source_1212_; lean_object* v_target_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; 
v_es_1210_ = lean_array_fget(v_source_1206_, v_i_1205_);
v___x_1211_ = lean_box(0);
v_source_1212_ = lean_array_fset(v_source_1206_, v_i_1205_, v___x_1211_);
v_target_1213_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__3_spec__6_spec__10___redArg(v_target_1207_, v_es_1210_);
v___x_1214_ = lean_unsigned_to_nat(1u);
v___x_1215_ = lean_nat_add(v_i_1205_, v___x_1214_);
lean_dec(v_i_1205_);
v_i_1205_ = v___x_1215_;
v_source_1206_ = v_source_1212_;
v_target_1207_ = v_target_1213_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__3___redArg(lean_object* v_data_1217_){
_start:
{
lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v_nbuckets_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; 
v___x_1218_ = lean_array_get_size(v_data_1217_);
v___x_1219_ = lean_unsigned_to_nat(2u);
v_nbuckets_1220_ = lean_nat_mul(v___x_1218_, v___x_1219_);
v___x_1221_ = lean_unsigned_to_nat(0u);
v___x_1222_ = lean_box(0);
v___x_1223_ = lean_mk_array(v_nbuckets_1220_, v___x_1222_);
v___x_1224_ = lean_array_propagate_mark(v_data_1217_, v___x_1223_);
v___x_1225_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__3_spec__6___redArg(v___x_1221_, v_data_1217_, v___x_1224_);
return v___x_1225_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__4___redArg(lean_object* v_a_1226_, lean_object* v_b_1227_, lean_object* v_x_1228_){
_start:
{
if (lean_obj_tag(v_x_1228_) == 0)
{
lean_dec(v_b_1227_);
lean_dec_ref(v_a_1226_);
return v_x_1228_;
}
else
{
lean_object* v_key_1229_; lean_object* v_value_1230_; lean_object* v_tail_1231_; lean_object* v___x_1233_; uint8_t v_isShared_1234_; uint8_t v_isSharedCheck_1243_; 
v_key_1229_ = lean_ctor_get(v_x_1228_, 0);
v_value_1230_ = lean_ctor_get(v_x_1228_, 1);
v_tail_1231_ = lean_ctor_get(v_x_1228_, 2);
v_isSharedCheck_1243_ = !lean_is_exclusive(v_x_1228_);
if (v_isSharedCheck_1243_ == 0)
{
v___x_1233_ = v_x_1228_;
v_isShared_1234_ = v_isSharedCheck_1243_;
goto v_resetjp_1232_;
}
else
{
lean_inc(v_tail_1231_);
lean_inc(v_value_1230_);
lean_inc(v_key_1229_);
lean_dec(v_x_1228_);
v___x_1233_ = lean_box(0);
v_isShared_1234_ = v_isSharedCheck_1243_;
goto v_resetjp_1232_;
}
v_resetjp_1232_:
{
uint8_t v___x_1235_; 
v___x_1235_ = l_Lean_ExprStructEq_beq(v_key_1229_, v_a_1226_);
if (v___x_1235_ == 0)
{
lean_object* v___x_1236_; lean_object* v___x_1238_; 
v___x_1236_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__4___redArg(v_a_1226_, v_b_1227_, v_tail_1231_);
if (v_isShared_1234_ == 0)
{
lean_ctor_set(v___x_1233_, 2, v___x_1236_);
v___x_1238_ = v___x_1233_;
goto v_reusejp_1237_;
}
else
{
lean_object* v_reuseFailAlloc_1239_; 
v_reuseFailAlloc_1239_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1239_, 0, v_key_1229_);
lean_ctor_set(v_reuseFailAlloc_1239_, 1, v_value_1230_);
lean_ctor_set(v_reuseFailAlloc_1239_, 2, v___x_1236_);
v___x_1238_ = v_reuseFailAlloc_1239_;
goto v_reusejp_1237_;
}
v_reusejp_1237_:
{
return v___x_1238_;
}
}
else
{
lean_object* v___x_1241_; 
lean_dec(v_value_1230_);
lean_dec(v_key_1229_);
if (v_isShared_1234_ == 0)
{
lean_ctor_set(v___x_1233_, 1, v_b_1227_);
lean_ctor_set(v___x_1233_, 0, v_a_1226_);
v___x_1241_ = v___x_1233_;
goto v_reusejp_1240_;
}
else
{
lean_object* v_reuseFailAlloc_1242_; 
v_reuseFailAlloc_1242_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1242_, 0, v_a_1226_);
lean_ctor_set(v_reuseFailAlloc_1242_, 1, v_b_1227_);
lean_ctor_set(v_reuseFailAlloc_1242_, 2, v_tail_1231_);
v___x_1241_ = v_reuseFailAlloc_1242_;
goto v_reusejp_1240_;
}
v_reusejp_1240_:
{
return v___x_1241_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__2___redArg(lean_object* v_a_1244_, lean_object* v_x_1245_){
_start:
{
if (lean_obj_tag(v_x_1245_) == 0)
{
uint8_t v___x_1246_; 
v___x_1246_ = 0;
return v___x_1246_;
}
else
{
lean_object* v_key_1247_; lean_object* v_tail_1248_; uint8_t v___x_1249_; 
v_key_1247_ = lean_ctor_get(v_x_1245_, 0);
v_tail_1248_ = lean_ctor_get(v_x_1245_, 2);
v___x_1249_ = l_Lean_ExprStructEq_beq(v_key_1247_, v_a_1244_);
if (v___x_1249_ == 0)
{
v_x_1245_ = v_tail_1248_;
goto _start;
}
else
{
return v___x_1249_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__2___redArg___boxed(lean_object* v_a_1251_, lean_object* v_x_1252_){
_start:
{
uint8_t v_res_1253_; lean_object* v_r_1254_; 
v_res_1253_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__2___redArg(v_a_1251_, v_x_1252_);
lean_dec(v_x_1252_);
lean_dec_ref(v_a_1251_);
v_r_1254_ = lean_box(v_res_1253_);
return v_r_1254_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1___redArg(lean_object* v_m_1255_, lean_object* v_a_1256_, lean_object* v_b_1257_){
_start:
{
lean_object* v_size_1258_; lean_object* v_buckets_1259_; lean_object* v___x_1261_; uint8_t v_isShared_1262_; uint8_t v_isSharedCheck_1302_; 
v_size_1258_ = lean_ctor_get(v_m_1255_, 0);
v_buckets_1259_ = lean_ctor_get(v_m_1255_, 1);
v_isSharedCheck_1302_ = !lean_is_exclusive(v_m_1255_);
if (v_isSharedCheck_1302_ == 0)
{
v___x_1261_ = v_m_1255_;
v_isShared_1262_ = v_isSharedCheck_1302_;
goto v_resetjp_1260_;
}
else
{
lean_inc(v_buckets_1259_);
lean_inc(v_size_1258_);
lean_dec(v_m_1255_);
v___x_1261_ = lean_box(0);
v_isShared_1262_ = v_isSharedCheck_1302_;
goto v_resetjp_1260_;
}
v_resetjp_1260_:
{
lean_object* v___x_1263_; uint64_t v___x_1264_; uint64_t v___x_1265_; uint64_t v___x_1266_; uint64_t v_fold_1267_; uint64_t v___x_1268_; uint64_t v___x_1269_; uint64_t v___x_1270_; size_t v___x_1271_; size_t v___x_1272_; size_t v___x_1273_; size_t v___x_1274_; size_t v___x_1275_; lean_object* v_bkt_1276_; uint8_t v___x_1277_; 
v___x_1263_ = lean_array_get_size(v_buckets_1259_);
v___x_1264_ = l_Lean_ExprStructEq_hash(v_a_1256_);
v___x_1265_ = 32ULL;
v___x_1266_ = lean_uint64_shift_right(v___x_1264_, v___x_1265_);
v_fold_1267_ = lean_uint64_xor(v___x_1264_, v___x_1266_);
v___x_1268_ = 16ULL;
v___x_1269_ = lean_uint64_shift_right(v_fold_1267_, v___x_1268_);
v___x_1270_ = lean_uint64_xor(v_fold_1267_, v___x_1269_);
v___x_1271_ = lean_uint64_to_usize(v___x_1270_);
v___x_1272_ = lean_usize_of_nat(v___x_1263_);
v___x_1273_ = ((size_t)1ULL);
v___x_1274_ = lean_usize_sub(v___x_1272_, v___x_1273_);
v___x_1275_ = lean_usize_land(v___x_1271_, v___x_1274_);
v_bkt_1276_ = lean_array_uget_borrowed(v_buckets_1259_, v___x_1275_);
v___x_1277_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__2___redArg(v_a_1256_, v_bkt_1276_);
if (v___x_1277_ == 0)
{
lean_object* v___x_1278_; lean_object* v_size_x27_1279_; lean_object* v___x_1280_; lean_object* v_buckets_x27_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; uint8_t v___x_1287_; 
v___x_1278_ = lean_unsigned_to_nat(1u);
v_size_x27_1279_ = lean_nat_add(v_size_1258_, v___x_1278_);
lean_dec(v_size_1258_);
lean_inc(v_bkt_1276_);
v___x_1280_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1280_, 0, v_a_1256_);
lean_ctor_set(v___x_1280_, 1, v_b_1257_);
lean_ctor_set(v___x_1280_, 2, v_bkt_1276_);
v_buckets_x27_1281_ = lean_array_uset(v_buckets_1259_, v___x_1275_, v___x_1280_);
v___x_1282_ = lean_unsigned_to_nat(4u);
v___x_1283_ = lean_nat_mul(v_size_x27_1279_, v___x_1282_);
v___x_1284_ = lean_unsigned_to_nat(3u);
v___x_1285_ = lean_nat_div(v___x_1283_, v___x_1284_);
lean_dec(v___x_1283_);
v___x_1286_ = lean_array_get_size(v_buckets_x27_1281_);
v___x_1287_ = lean_nat_dec_le(v___x_1285_, v___x_1286_);
lean_dec(v___x_1285_);
if (v___x_1287_ == 0)
{
lean_object* v_val_1288_; lean_object* v___x_1290_; 
v_val_1288_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__3___redArg(v_buckets_x27_1281_);
if (v_isShared_1262_ == 0)
{
lean_ctor_set(v___x_1261_, 1, v_val_1288_);
lean_ctor_set(v___x_1261_, 0, v_size_x27_1279_);
v___x_1290_ = v___x_1261_;
goto v_reusejp_1289_;
}
else
{
lean_object* v_reuseFailAlloc_1291_; 
v_reuseFailAlloc_1291_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1291_, 0, v_size_x27_1279_);
lean_ctor_set(v_reuseFailAlloc_1291_, 1, v_val_1288_);
v___x_1290_ = v_reuseFailAlloc_1291_;
goto v_reusejp_1289_;
}
v_reusejp_1289_:
{
return v___x_1290_;
}
}
else
{
lean_object* v___x_1293_; 
if (v_isShared_1262_ == 0)
{
lean_ctor_set(v___x_1261_, 1, v_buckets_x27_1281_);
lean_ctor_set(v___x_1261_, 0, v_size_x27_1279_);
v___x_1293_ = v___x_1261_;
goto v_reusejp_1292_;
}
else
{
lean_object* v_reuseFailAlloc_1294_; 
v_reuseFailAlloc_1294_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1294_, 0, v_size_x27_1279_);
lean_ctor_set(v_reuseFailAlloc_1294_, 1, v_buckets_x27_1281_);
v___x_1293_ = v_reuseFailAlloc_1294_;
goto v_reusejp_1292_;
}
v_reusejp_1292_:
{
return v___x_1293_;
}
}
}
else
{
lean_object* v___x_1295_; lean_object* v_buckets_x27_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1300_; 
lean_inc(v_bkt_1276_);
v___x_1295_ = lean_box(0);
v_buckets_x27_1296_ = lean_array_uset(v_buckets_1259_, v___x_1275_, v___x_1295_);
v___x_1297_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__4___redArg(v_a_1256_, v_b_1257_, v_bkt_1276_);
v___x_1298_ = lean_array_uset(v_buckets_x27_1296_, v___x_1275_, v___x_1297_);
if (v_isShared_1262_ == 0)
{
lean_ctor_set(v___x_1261_, 1, v___x_1298_);
v___x_1300_ = v___x_1261_;
goto v_reusejp_1299_;
}
else
{
lean_object* v_reuseFailAlloc_1301_; 
v_reuseFailAlloc_1301_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1301_, 0, v_size_1258_);
lean_ctor_set(v_reuseFailAlloc_1301_, 1, v___x_1298_);
v___x_1300_ = v_reuseFailAlloc_1301_;
goto v_reusejp_1299_;
}
v_reusejp_1299_:
{
return v___x_1300_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectExprAux(lean_object* v_e_1303_, lean_object* v_a_1304_, lean_object* v_a_1305_, lean_object* v_a_1306_, lean_object* v_a_1307_, lean_object* v_a_1308_, lean_object* v_a_1309_){
_start:
{
switch(lean_obj_tag(v_e_1303_))
{
case 11:
{
lean_object* v_typeName_1311_; lean_object* v_idx_1312_; lean_object* v_struct_1313_; lean_object* v___x_1314_; 
v_typeName_1311_ = lean_ctor_get(v_e_1303_, 0);
v_idx_1312_ = lean_ctor_get(v_e_1303_, 1);
v_struct_1313_ = lean_ctor_get(v_e_1303_, 2);
lean_inc_ref(v_struct_1313_);
v___x_1314_ = l_Lean_Meta_Closure_collectExprAux___lam__0(v_struct_1313_, v_a_1304_, v_a_1305_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
if (lean_obj_tag(v___x_1314_) == 0)
{
lean_object* v_a_1315_; lean_object* v___x_1317_; uint8_t v_isShared_1318_; uint8_t v_isSharedCheck_1329_; 
v_a_1315_ = lean_ctor_get(v___x_1314_, 0);
v_isSharedCheck_1329_ = !lean_is_exclusive(v___x_1314_);
if (v_isSharedCheck_1329_ == 0)
{
v___x_1317_ = v___x_1314_;
v_isShared_1318_ = v_isSharedCheck_1329_;
goto v_resetjp_1316_;
}
else
{
lean_inc(v_a_1315_);
lean_dec(v___x_1314_);
v___x_1317_ = lean_box(0);
v_isShared_1318_ = v_isSharedCheck_1329_;
goto v_resetjp_1316_;
}
v_resetjp_1316_:
{
size_t v___x_1319_; size_t v___x_1320_; uint8_t v___x_1321_; 
v___x_1319_ = lean_ptr_addr(v_struct_1313_);
v___x_1320_ = lean_ptr_addr(v_a_1315_);
v___x_1321_ = lean_usize_dec_eq(v___x_1319_, v___x_1320_);
if (v___x_1321_ == 0)
{
lean_object* v___x_1322_; lean_object* v___x_1324_; 
lean_inc(v_idx_1312_);
lean_inc(v_typeName_1311_);
lean_dec_ref_known(v_e_1303_, 3);
v___x_1322_ = l_Lean_Expr_proj___override(v_typeName_1311_, v_idx_1312_, v_a_1315_);
if (v_isShared_1318_ == 0)
{
lean_ctor_set(v___x_1317_, 0, v___x_1322_);
v___x_1324_ = v___x_1317_;
goto v_reusejp_1323_;
}
else
{
lean_object* v_reuseFailAlloc_1325_; 
v_reuseFailAlloc_1325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1325_, 0, v___x_1322_);
v___x_1324_ = v_reuseFailAlloc_1325_;
goto v_reusejp_1323_;
}
v_reusejp_1323_:
{
return v___x_1324_;
}
}
else
{
lean_object* v___x_1327_; 
lean_dec(v_a_1315_);
if (v_isShared_1318_ == 0)
{
lean_ctor_set(v___x_1317_, 0, v_e_1303_);
v___x_1327_ = v___x_1317_;
goto v_reusejp_1326_;
}
else
{
lean_object* v_reuseFailAlloc_1328_; 
v_reuseFailAlloc_1328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1328_, 0, v_e_1303_);
v___x_1327_ = v_reuseFailAlloc_1328_;
goto v_reusejp_1326_;
}
v_reusejp_1326_:
{
return v___x_1327_;
}
}
}
}
else
{
lean_dec_ref_known(v_e_1303_, 3);
return v___x_1314_;
}
}
case 7:
{
lean_object* v_binderName_1330_; lean_object* v_binderType_1331_; lean_object* v_body_1332_; uint8_t v_binderInfo_1333_; lean_object* v___x_1334_; 
v_binderName_1330_ = lean_ctor_get(v_e_1303_, 0);
v_binderType_1331_ = lean_ctor_get(v_e_1303_, 1);
v_body_1332_ = lean_ctor_get(v_e_1303_, 2);
v_binderInfo_1333_ = lean_ctor_get_uint8(v_e_1303_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_1331_);
v___x_1334_ = l_Lean_Meta_Closure_collectExprAux___lam__0(v_binderType_1331_, v_a_1304_, v_a_1305_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
if (lean_obj_tag(v___x_1334_) == 0)
{
lean_object* v_a_1335_; lean_object* v___x_1336_; 
v_a_1335_ = lean_ctor_get(v___x_1334_, 0);
lean_inc(v_a_1335_);
lean_dec_ref_known(v___x_1334_, 1);
lean_inc_ref(v_body_1332_);
v___x_1336_ = l_Lean_Meta_Closure_collectExprAux___lam__0(v_body_1332_, v_a_1304_, v_a_1305_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
if (lean_obj_tag(v___x_1336_) == 0)
{
lean_object* v_a_1337_; lean_object* v___x_1339_; uint8_t v_isShared_1340_; uint8_t v_isSharedCheck_1363_; 
v_a_1337_ = lean_ctor_get(v___x_1336_, 0);
v_isSharedCheck_1363_ = !lean_is_exclusive(v___x_1336_);
if (v_isSharedCheck_1363_ == 0)
{
v___x_1339_ = v___x_1336_;
v_isShared_1340_ = v_isSharedCheck_1363_;
goto v_resetjp_1338_;
}
else
{
lean_inc(v_a_1337_);
lean_dec(v___x_1336_);
v___x_1339_ = lean_box(0);
v_isShared_1340_ = v_isSharedCheck_1363_;
goto v_resetjp_1338_;
}
v_resetjp_1338_:
{
size_t v___x_1341_; size_t v___x_1342_; uint8_t v___x_1343_; 
v___x_1341_ = lean_ptr_addr(v_binderType_1331_);
v___x_1342_ = lean_ptr_addr(v_a_1335_);
v___x_1343_ = lean_usize_dec_eq(v___x_1341_, v___x_1342_);
if (v___x_1343_ == 0)
{
lean_object* v___x_1344_; lean_object* v___x_1346_; 
lean_inc(v_binderName_1330_);
lean_dec_ref_known(v_e_1303_, 3);
v___x_1344_ = l_Lean_Expr_forallE___override(v_binderName_1330_, v_a_1335_, v_a_1337_, v_binderInfo_1333_);
if (v_isShared_1340_ == 0)
{
lean_ctor_set(v___x_1339_, 0, v___x_1344_);
v___x_1346_ = v___x_1339_;
goto v_reusejp_1345_;
}
else
{
lean_object* v_reuseFailAlloc_1347_; 
v_reuseFailAlloc_1347_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1347_, 0, v___x_1344_);
v___x_1346_ = v_reuseFailAlloc_1347_;
goto v_reusejp_1345_;
}
v_reusejp_1345_:
{
return v___x_1346_;
}
}
else
{
size_t v___x_1348_; size_t v___x_1349_; uint8_t v___x_1350_; 
v___x_1348_ = lean_ptr_addr(v_body_1332_);
v___x_1349_ = lean_ptr_addr(v_a_1337_);
v___x_1350_ = lean_usize_dec_eq(v___x_1348_, v___x_1349_);
if (v___x_1350_ == 0)
{
lean_object* v___x_1351_; lean_object* v___x_1353_; 
lean_inc(v_binderName_1330_);
lean_dec_ref_known(v_e_1303_, 3);
v___x_1351_ = l_Lean_Expr_forallE___override(v_binderName_1330_, v_a_1335_, v_a_1337_, v_binderInfo_1333_);
if (v_isShared_1340_ == 0)
{
lean_ctor_set(v___x_1339_, 0, v___x_1351_);
v___x_1353_ = v___x_1339_;
goto v_reusejp_1352_;
}
else
{
lean_object* v_reuseFailAlloc_1354_; 
v_reuseFailAlloc_1354_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1354_, 0, v___x_1351_);
v___x_1353_ = v_reuseFailAlloc_1354_;
goto v_reusejp_1352_;
}
v_reusejp_1352_:
{
return v___x_1353_;
}
}
else
{
uint8_t v___x_1355_; 
v___x_1355_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_1333_, v_binderInfo_1333_);
if (v___x_1355_ == 0)
{
lean_object* v___x_1356_; lean_object* v___x_1358_; 
lean_inc(v_binderName_1330_);
lean_dec_ref_known(v_e_1303_, 3);
v___x_1356_ = l_Lean_Expr_forallE___override(v_binderName_1330_, v_a_1335_, v_a_1337_, v_binderInfo_1333_);
if (v_isShared_1340_ == 0)
{
lean_ctor_set(v___x_1339_, 0, v___x_1356_);
v___x_1358_ = v___x_1339_;
goto v_reusejp_1357_;
}
else
{
lean_object* v_reuseFailAlloc_1359_; 
v_reuseFailAlloc_1359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1359_, 0, v___x_1356_);
v___x_1358_ = v_reuseFailAlloc_1359_;
goto v_reusejp_1357_;
}
v_reusejp_1357_:
{
return v___x_1358_;
}
}
else
{
lean_object* v___x_1361_; 
lean_dec(v_a_1337_);
lean_dec(v_a_1335_);
if (v_isShared_1340_ == 0)
{
lean_ctor_set(v___x_1339_, 0, v_e_1303_);
v___x_1361_ = v___x_1339_;
goto v_reusejp_1360_;
}
else
{
lean_object* v_reuseFailAlloc_1362_; 
v_reuseFailAlloc_1362_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1362_, 0, v_e_1303_);
v___x_1361_ = v_reuseFailAlloc_1362_;
goto v_reusejp_1360_;
}
v_reusejp_1360_:
{
return v___x_1361_;
}
}
}
}
}
}
else
{
lean_dec(v_a_1335_);
lean_dec_ref_known(v_e_1303_, 3);
return v___x_1336_;
}
}
else
{
lean_dec_ref_known(v_e_1303_, 3);
return v___x_1334_;
}
}
case 6:
{
lean_object* v_binderName_1364_; lean_object* v_binderType_1365_; lean_object* v_body_1366_; uint8_t v_binderInfo_1367_; lean_object* v___x_1368_; 
v_binderName_1364_ = lean_ctor_get(v_e_1303_, 0);
v_binderType_1365_ = lean_ctor_get(v_e_1303_, 1);
v_body_1366_ = lean_ctor_get(v_e_1303_, 2);
v_binderInfo_1367_ = lean_ctor_get_uint8(v_e_1303_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_1365_);
v___x_1368_ = l_Lean_Meta_Closure_collectExprAux___lam__0(v_binderType_1365_, v_a_1304_, v_a_1305_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
if (lean_obj_tag(v___x_1368_) == 0)
{
lean_object* v_a_1369_; lean_object* v___x_1370_; 
v_a_1369_ = lean_ctor_get(v___x_1368_, 0);
lean_inc(v_a_1369_);
lean_dec_ref_known(v___x_1368_, 1);
lean_inc_ref(v_body_1366_);
v___x_1370_ = l_Lean_Meta_Closure_collectExprAux___lam__0(v_body_1366_, v_a_1304_, v_a_1305_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
if (lean_obj_tag(v___x_1370_) == 0)
{
lean_object* v_a_1371_; lean_object* v___x_1373_; uint8_t v_isShared_1374_; uint8_t v_isSharedCheck_1397_; 
v_a_1371_ = lean_ctor_get(v___x_1370_, 0);
v_isSharedCheck_1397_ = !lean_is_exclusive(v___x_1370_);
if (v_isSharedCheck_1397_ == 0)
{
v___x_1373_ = v___x_1370_;
v_isShared_1374_ = v_isSharedCheck_1397_;
goto v_resetjp_1372_;
}
else
{
lean_inc(v_a_1371_);
lean_dec(v___x_1370_);
v___x_1373_ = lean_box(0);
v_isShared_1374_ = v_isSharedCheck_1397_;
goto v_resetjp_1372_;
}
v_resetjp_1372_:
{
size_t v___x_1375_; size_t v___x_1376_; uint8_t v___x_1377_; 
v___x_1375_ = lean_ptr_addr(v_binderType_1365_);
v___x_1376_ = lean_ptr_addr(v_a_1369_);
v___x_1377_ = lean_usize_dec_eq(v___x_1375_, v___x_1376_);
if (v___x_1377_ == 0)
{
lean_object* v___x_1378_; lean_object* v___x_1380_; 
lean_inc(v_binderName_1364_);
lean_dec_ref_known(v_e_1303_, 3);
v___x_1378_ = l_Lean_Expr_lam___override(v_binderName_1364_, v_a_1369_, v_a_1371_, v_binderInfo_1367_);
if (v_isShared_1374_ == 0)
{
lean_ctor_set(v___x_1373_, 0, v___x_1378_);
v___x_1380_ = v___x_1373_;
goto v_reusejp_1379_;
}
else
{
lean_object* v_reuseFailAlloc_1381_; 
v_reuseFailAlloc_1381_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1381_, 0, v___x_1378_);
v___x_1380_ = v_reuseFailAlloc_1381_;
goto v_reusejp_1379_;
}
v_reusejp_1379_:
{
return v___x_1380_;
}
}
else
{
size_t v___x_1382_; size_t v___x_1383_; uint8_t v___x_1384_; 
v___x_1382_ = lean_ptr_addr(v_body_1366_);
v___x_1383_ = lean_ptr_addr(v_a_1371_);
v___x_1384_ = lean_usize_dec_eq(v___x_1382_, v___x_1383_);
if (v___x_1384_ == 0)
{
lean_object* v___x_1385_; lean_object* v___x_1387_; 
lean_inc(v_binderName_1364_);
lean_dec_ref_known(v_e_1303_, 3);
v___x_1385_ = l_Lean_Expr_lam___override(v_binderName_1364_, v_a_1369_, v_a_1371_, v_binderInfo_1367_);
if (v_isShared_1374_ == 0)
{
lean_ctor_set(v___x_1373_, 0, v___x_1385_);
v___x_1387_ = v___x_1373_;
goto v_reusejp_1386_;
}
else
{
lean_object* v_reuseFailAlloc_1388_; 
v_reuseFailAlloc_1388_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1388_, 0, v___x_1385_);
v___x_1387_ = v_reuseFailAlloc_1388_;
goto v_reusejp_1386_;
}
v_reusejp_1386_:
{
return v___x_1387_;
}
}
else
{
uint8_t v___x_1389_; 
v___x_1389_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_1367_, v_binderInfo_1367_);
if (v___x_1389_ == 0)
{
lean_object* v___x_1390_; lean_object* v___x_1392_; 
lean_inc(v_binderName_1364_);
lean_dec_ref_known(v_e_1303_, 3);
v___x_1390_ = l_Lean_Expr_lam___override(v_binderName_1364_, v_a_1369_, v_a_1371_, v_binderInfo_1367_);
if (v_isShared_1374_ == 0)
{
lean_ctor_set(v___x_1373_, 0, v___x_1390_);
v___x_1392_ = v___x_1373_;
goto v_reusejp_1391_;
}
else
{
lean_object* v_reuseFailAlloc_1393_; 
v_reuseFailAlloc_1393_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1393_, 0, v___x_1390_);
v___x_1392_ = v_reuseFailAlloc_1393_;
goto v_reusejp_1391_;
}
v_reusejp_1391_:
{
return v___x_1392_;
}
}
else
{
lean_object* v___x_1395_; 
lean_dec(v_a_1371_);
lean_dec(v_a_1369_);
if (v_isShared_1374_ == 0)
{
lean_ctor_set(v___x_1373_, 0, v_e_1303_);
v___x_1395_ = v___x_1373_;
goto v_reusejp_1394_;
}
else
{
lean_object* v_reuseFailAlloc_1396_; 
v_reuseFailAlloc_1396_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1396_, 0, v_e_1303_);
v___x_1395_ = v_reuseFailAlloc_1396_;
goto v_reusejp_1394_;
}
v_reusejp_1394_:
{
return v___x_1395_;
}
}
}
}
}
}
else
{
lean_dec(v_a_1369_);
lean_dec_ref_known(v_e_1303_, 3);
return v___x_1370_;
}
}
else
{
lean_dec_ref_known(v_e_1303_, 3);
return v___x_1368_;
}
}
case 8:
{
lean_object* v_declName_1398_; lean_object* v_type_1399_; lean_object* v_value_1400_; lean_object* v_body_1401_; uint8_t v_nondep_1402_; lean_object* v___x_1403_; 
v_declName_1398_ = lean_ctor_get(v_e_1303_, 0);
v_type_1399_ = lean_ctor_get(v_e_1303_, 1);
v_value_1400_ = lean_ctor_get(v_e_1303_, 2);
v_body_1401_ = lean_ctor_get(v_e_1303_, 3);
v_nondep_1402_ = lean_ctor_get_uint8(v_e_1303_, sizeof(void*)*4 + 8);
lean_inc_ref(v_type_1399_);
v___x_1403_ = l_Lean_Meta_Closure_collectExprAux___lam__0(v_type_1399_, v_a_1304_, v_a_1305_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
if (lean_obj_tag(v___x_1403_) == 0)
{
lean_object* v_a_1404_; lean_object* v___x_1405_; 
v_a_1404_ = lean_ctor_get(v___x_1403_, 0);
lean_inc(v_a_1404_);
lean_dec_ref_known(v___x_1403_, 1);
lean_inc_ref(v_value_1400_);
v___x_1405_ = l_Lean_Meta_Closure_collectExprAux___lam__0(v_value_1400_, v_a_1304_, v_a_1305_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
if (lean_obj_tag(v___x_1405_) == 0)
{
lean_object* v_a_1406_; lean_object* v___x_1407_; 
v_a_1406_ = lean_ctor_get(v___x_1405_, 0);
lean_inc(v_a_1406_);
lean_dec_ref_known(v___x_1405_, 1);
lean_inc_ref(v_body_1401_);
v___x_1407_ = l_Lean_Meta_Closure_collectExprAux___lam__0(v_body_1401_, v_a_1304_, v_a_1305_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
if (lean_obj_tag(v___x_1407_) == 0)
{
lean_object* v_a_1408_; lean_object* v___x_1410_; uint8_t v_isShared_1411_; uint8_t v_isSharedCheck_1436_; 
v_a_1408_ = lean_ctor_get(v___x_1407_, 0);
v_isSharedCheck_1436_ = !lean_is_exclusive(v___x_1407_);
if (v_isSharedCheck_1436_ == 0)
{
v___x_1410_ = v___x_1407_;
v_isShared_1411_ = v_isSharedCheck_1436_;
goto v_resetjp_1409_;
}
else
{
lean_inc(v_a_1408_);
lean_dec(v___x_1407_);
v___x_1410_ = lean_box(0);
v_isShared_1411_ = v_isSharedCheck_1436_;
goto v_resetjp_1409_;
}
v_resetjp_1409_:
{
size_t v___x_1412_; size_t v___x_1413_; uint8_t v___x_1414_; 
v___x_1412_ = lean_ptr_addr(v_type_1399_);
v___x_1413_ = lean_ptr_addr(v_a_1404_);
v___x_1414_ = lean_usize_dec_eq(v___x_1412_, v___x_1413_);
if (v___x_1414_ == 0)
{
lean_object* v___x_1415_; lean_object* v___x_1417_; 
lean_inc(v_declName_1398_);
lean_dec_ref_known(v_e_1303_, 4);
v___x_1415_ = l_Lean_Expr_letE___override(v_declName_1398_, v_a_1404_, v_a_1406_, v_a_1408_, v_nondep_1402_);
if (v_isShared_1411_ == 0)
{
lean_ctor_set(v___x_1410_, 0, v___x_1415_);
v___x_1417_ = v___x_1410_;
goto v_reusejp_1416_;
}
else
{
lean_object* v_reuseFailAlloc_1418_; 
v_reuseFailAlloc_1418_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1418_, 0, v___x_1415_);
v___x_1417_ = v_reuseFailAlloc_1418_;
goto v_reusejp_1416_;
}
v_reusejp_1416_:
{
return v___x_1417_;
}
}
else
{
size_t v___x_1419_; size_t v___x_1420_; uint8_t v___x_1421_; 
v___x_1419_ = lean_ptr_addr(v_value_1400_);
v___x_1420_ = lean_ptr_addr(v_a_1406_);
v___x_1421_ = lean_usize_dec_eq(v___x_1419_, v___x_1420_);
if (v___x_1421_ == 0)
{
lean_object* v___x_1422_; lean_object* v___x_1424_; 
lean_inc(v_declName_1398_);
lean_dec_ref_known(v_e_1303_, 4);
v___x_1422_ = l_Lean_Expr_letE___override(v_declName_1398_, v_a_1404_, v_a_1406_, v_a_1408_, v_nondep_1402_);
if (v_isShared_1411_ == 0)
{
lean_ctor_set(v___x_1410_, 0, v___x_1422_);
v___x_1424_ = v___x_1410_;
goto v_reusejp_1423_;
}
else
{
lean_object* v_reuseFailAlloc_1425_; 
v_reuseFailAlloc_1425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1425_, 0, v___x_1422_);
v___x_1424_ = v_reuseFailAlloc_1425_;
goto v_reusejp_1423_;
}
v_reusejp_1423_:
{
return v___x_1424_;
}
}
else
{
size_t v___x_1426_; size_t v___x_1427_; uint8_t v___x_1428_; 
v___x_1426_ = lean_ptr_addr(v_body_1401_);
v___x_1427_ = lean_ptr_addr(v_a_1408_);
v___x_1428_ = lean_usize_dec_eq(v___x_1426_, v___x_1427_);
if (v___x_1428_ == 0)
{
lean_object* v___x_1429_; lean_object* v___x_1431_; 
lean_inc(v_declName_1398_);
lean_dec_ref_known(v_e_1303_, 4);
v___x_1429_ = l_Lean_Expr_letE___override(v_declName_1398_, v_a_1404_, v_a_1406_, v_a_1408_, v_nondep_1402_);
if (v_isShared_1411_ == 0)
{
lean_ctor_set(v___x_1410_, 0, v___x_1429_);
v___x_1431_ = v___x_1410_;
goto v_reusejp_1430_;
}
else
{
lean_object* v_reuseFailAlloc_1432_; 
v_reuseFailAlloc_1432_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1432_, 0, v___x_1429_);
v___x_1431_ = v_reuseFailAlloc_1432_;
goto v_reusejp_1430_;
}
v_reusejp_1430_:
{
return v___x_1431_;
}
}
else
{
lean_object* v___x_1434_; 
lean_dec(v_a_1408_);
lean_dec(v_a_1406_);
lean_dec(v_a_1404_);
if (v_isShared_1411_ == 0)
{
lean_ctor_set(v___x_1410_, 0, v_e_1303_);
v___x_1434_ = v___x_1410_;
goto v_reusejp_1433_;
}
else
{
lean_object* v_reuseFailAlloc_1435_; 
v_reuseFailAlloc_1435_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1435_, 0, v_e_1303_);
v___x_1434_ = v_reuseFailAlloc_1435_;
goto v_reusejp_1433_;
}
v_reusejp_1433_:
{
return v___x_1434_;
}
}
}
}
}
}
else
{
lean_dec(v_a_1406_);
lean_dec(v_a_1404_);
lean_dec_ref_known(v_e_1303_, 4);
return v___x_1407_;
}
}
else
{
lean_dec(v_a_1404_);
lean_dec_ref_known(v_e_1303_, 4);
return v___x_1405_;
}
}
else
{
lean_dec_ref_known(v_e_1303_, 4);
return v___x_1403_;
}
}
case 5:
{
lean_object* v_fn_1437_; lean_object* v_arg_1438_; lean_object* v___x_1439_; 
v_fn_1437_ = lean_ctor_get(v_e_1303_, 0);
v_arg_1438_ = lean_ctor_get(v_e_1303_, 1);
lean_inc_ref(v_fn_1437_);
v___x_1439_ = l_Lean_Meta_Closure_collectExprAux___lam__0(v_fn_1437_, v_a_1304_, v_a_1305_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
if (lean_obj_tag(v___x_1439_) == 0)
{
lean_object* v_a_1440_; lean_object* v___x_1441_; 
v_a_1440_ = lean_ctor_get(v___x_1439_, 0);
lean_inc(v_a_1440_);
lean_dec_ref_known(v___x_1439_, 1);
lean_inc_ref(v_arg_1438_);
v___x_1441_ = l_Lean_Meta_Closure_collectExprAux___lam__0(v_arg_1438_, v_a_1304_, v_a_1305_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
if (lean_obj_tag(v___x_1441_) == 0)
{
lean_object* v_a_1442_; lean_object* v___x_1444_; uint8_t v_isShared_1445_; uint8_t v_isSharedCheck_1463_; 
v_a_1442_ = lean_ctor_get(v___x_1441_, 0);
v_isSharedCheck_1463_ = !lean_is_exclusive(v___x_1441_);
if (v_isSharedCheck_1463_ == 0)
{
v___x_1444_ = v___x_1441_;
v_isShared_1445_ = v_isSharedCheck_1463_;
goto v_resetjp_1443_;
}
else
{
lean_inc(v_a_1442_);
lean_dec(v___x_1441_);
v___x_1444_ = lean_box(0);
v_isShared_1445_ = v_isSharedCheck_1463_;
goto v_resetjp_1443_;
}
v_resetjp_1443_:
{
size_t v___x_1446_; size_t v___x_1447_; uint8_t v___x_1448_; 
v___x_1446_ = lean_ptr_addr(v_fn_1437_);
v___x_1447_ = lean_ptr_addr(v_a_1440_);
v___x_1448_ = lean_usize_dec_eq(v___x_1446_, v___x_1447_);
if (v___x_1448_ == 0)
{
lean_object* v___x_1449_; lean_object* v___x_1451_; 
lean_dec_ref_known(v_e_1303_, 2);
v___x_1449_ = l_Lean_Expr_app___override(v_a_1440_, v_a_1442_);
if (v_isShared_1445_ == 0)
{
lean_ctor_set(v___x_1444_, 0, v___x_1449_);
v___x_1451_ = v___x_1444_;
goto v_reusejp_1450_;
}
else
{
lean_object* v_reuseFailAlloc_1452_; 
v_reuseFailAlloc_1452_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1452_, 0, v___x_1449_);
v___x_1451_ = v_reuseFailAlloc_1452_;
goto v_reusejp_1450_;
}
v_reusejp_1450_:
{
return v___x_1451_;
}
}
else
{
size_t v___x_1453_; size_t v___x_1454_; uint8_t v___x_1455_; 
v___x_1453_ = lean_ptr_addr(v_arg_1438_);
v___x_1454_ = lean_ptr_addr(v_a_1442_);
v___x_1455_ = lean_usize_dec_eq(v___x_1453_, v___x_1454_);
if (v___x_1455_ == 0)
{
lean_object* v___x_1456_; lean_object* v___x_1458_; 
lean_dec_ref_known(v_e_1303_, 2);
v___x_1456_ = l_Lean_Expr_app___override(v_a_1440_, v_a_1442_);
if (v_isShared_1445_ == 0)
{
lean_ctor_set(v___x_1444_, 0, v___x_1456_);
v___x_1458_ = v___x_1444_;
goto v_reusejp_1457_;
}
else
{
lean_object* v_reuseFailAlloc_1459_; 
v_reuseFailAlloc_1459_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1459_, 0, v___x_1456_);
v___x_1458_ = v_reuseFailAlloc_1459_;
goto v_reusejp_1457_;
}
v_reusejp_1457_:
{
return v___x_1458_;
}
}
else
{
lean_object* v___x_1461_; 
lean_dec(v_a_1442_);
lean_dec(v_a_1440_);
if (v_isShared_1445_ == 0)
{
lean_ctor_set(v___x_1444_, 0, v_e_1303_);
v___x_1461_ = v___x_1444_;
goto v_reusejp_1460_;
}
else
{
lean_object* v_reuseFailAlloc_1462_; 
v_reuseFailAlloc_1462_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1462_, 0, v_e_1303_);
v___x_1461_ = v_reuseFailAlloc_1462_;
goto v_reusejp_1460_;
}
v_reusejp_1460_:
{
return v___x_1461_;
}
}
}
}
}
else
{
lean_dec(v_a_1440_);
lean_dec_ref_known(v_e_1303_, 2);
return v___x_1441_;
}
}
else
{
lean_dec_ref_known(v_e_1303_, 2);
return v___x_1439_;
}
}
case 10:
{
lean_object* v_data_1464_; lean_object* v_expr_1465_; lean_object* v___x_1466_; 
v_data_1464_ = lean_ctor_get(v_e_1303_, 0);
v_expr_1465_ = lean_ctor_get(v_e_1303_, 1);
lean_inc_ref(v_expr_1465_);
v___x_1466_ = l_Lean_Meta_Closure_collectExprAux___lam__0(v_expr_1465_, v_a_1304_, v_a_1305_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
if (lean_obj_tag(v___x_1466_) == 0)
{
lean_object* v_a_1467_; lean_object* v___x_1469_; uint8_t v_isShared_1470_; uint8_t v_isSharedCheck_1481_; 
v_a_1467_ = lean_ctor_get(v___x_1466_, 0);
v_isSharedCheck_1481_ = !lean_is_exclusive(v___x_1466_);
if (v_isSharedCheck_1481_ == 0)
{
v___x_1469_ = v___x_1466_;
v_isShared_1470_ = v_isSharedCheck_1481_;
goto v_resetjp_1468_;
}
else
{
lean_inc(v_a_1467_);
lean_dec(v___x_1466_);
v___x_1469_ = lean_box(0);
v_isShared_1470_ = v_isSharedCheck_1481_;
goto v_resetjp_1468_;
}
v_resetjp_1468_:
{
size_t v___x_1471_; size_t v___x_1472_; uint8_t v___x_1473_; 
v___x_1471_ = lean_ptr_addr(v_expr_1465_);
v___x_1472_ = lean_ptr_addr(v_a_1467_);
v___x_1473_ = lean_usize_dec_eq(v___x_1471_, v___x_1472_);
if (v___x_1473_ == 0)
{
lean_object* v___x_1474_; lean_object* v___x_1476_; 
lean_inc(v_data_1464_);
lean_dec_ref_known(v_e_1303_, 2);
v___x_1474_ = l_Lean_Expr_mdata___override(v_data_1464_, v_a_1467_);
if (v_isShared_1470_ == 0)
{
lean_ctor_set(v___x_1469_, 0, v___x_1474_);
v___x_1476_ = v___x_1469_;
goto v_reusejp_1475_;
}
else
{
lean_object* v_reuseFailAlloc_1477_; 
v_reuseFailAlloc_1477_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1477_, 0, v___x_1474_);
v___x_1476_ = v_reuseFailAlloc_1477_;
goto v_reusejp_1475_;
}
v_reusejp_1475_:
{
return v___x_1476_;
}
}
else
{
lean_object* v___x_1479_; 
lean_dec(v_a_1467_);
if (v_isShared_1470_ == 0)
{
lean_ctor_set(v___x_1469_, 0, v_e_1303_);
v___x_1479_ = v___x_1469_;
goto v_reusejp_1478_;
}
else
{
lean_object* v_reuseFailAlloc_1480_; 
v_reuseFailAlloc_1480_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1480_, 0, v_e_1303_);
v___x_1479_ = v_reuseFailAlloc_1480_;
goto v_reusejp_1478_;
}
v_reusejp_1478_:
{
return v___x_1479_;
}
}
}
}
else
{
lean_dec_ref_known(v_e_1303_, 2);
return v___x_1466_;
}
}
case 3:
{
lean_object* v_u_1482_; lean_object* v___x_1483_; 
v_u_1482_ = lean_ctor_get(v_e_1303_, 0);
lean_inc(v_u_1482_);
v___x_1483_ = l_Lean_Meta_Closure_collectLevel___redArg(v_u_1482_, v_a_1305_);
if (lean_obj_tag(v___x_1483_) == 0)
{
lean_object* v_a_1484_; lean_object* v___x_1486_; uint8_t v_isShared_1487_; uint8_t v_isSharedCheck_1498_; 
v_a_1484_ = lean_ctor_get(v___x_1483_, 0);
v_isSharedCheck_1498_ = !lean_is_exclusive(v___x_1483_);
if (v_isSharedCheck_1498_ == 0)
{
v___x_1486_ = v___x_1483_;
v_isShared_1487_ = v_isSharedCheck_1498_;
goto v_resetjp_1485_;
}
else
{
lean_inc(v_a_1484_);
lean_dec(v___x_1483_);
v___x_1486_ = lean_box(0);
v_isShared_1487_ = v_isSharedCheck_1498_;
goto v_resetjp_1485_;
}
v_resetjp_1485_:
{
size_t v___x_1488_; size_t v___x_1489_; uint8_t v___x_1490_; 
v___x_1488_ = lean_ptr_addr(v_u_1482_);
v___x_1489_ = lean_ptr_addr(v_a_1484_);
v___x_1490_ = lean_usize_dec_eq(v___x_1488_, v___x_1489_);
if (v___x_1490_ == 0)
{
lean_object* v___x_1491_; lean_object* v___x_1493_; 
lean_dec_ref_known(v_e_1303_, 1);
v___x_1491_ = l_Lean_Expr_sort___override(v_a_1484_);
if (v_isShared_1487_ == 0)
{
lean_ctor_set(v___x_1486_, 0, v___x_1491_);
v___x_1493_ = v___x_1486_;
goto v_reusejp_1492_;
}
else
{
lean_object* v_reuseFailAlloc_1494_; 
v_reuseFailAlloc_1494_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1494_, 0, v___x_1491_);
v___x_1493_ = v_reuseFailAlloc_1494_;
goto v_reusejp_1492_;
}
v_reusejp_1492_:
{
return v___x_1493_;
}
}
else
{
lean_object* v___x_1496_; 
lean_dec(v_a_1484_);
if (v_isShared_1487_ == 0)
{
lean_ctor_set(v___x_1486_, 0, v_e_1303_);
v___x_1496_ = v___x_1486_;
goto v_reusejp_1495_;
}
else
{
lean_object* v_reuseFailAlloc_1497_; 
v_reuseFailAlloc_1497_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1497_, 0, v_e_1303_);
v___x_1496_ = v_reuseFailAlloc_1497_;
goto v_reusejp_1495_;
}
v_reusejp_1495_:
{
return v___x_1496_;
}
}
}
}
else
{
lean_object* v_a_1499_; lean_object* v___x_1501_; uint8_t v_isShared_1502_; uint8_t v_isSharedCheck_1506_; 
lean_dec_ref_known(v_e_1303_, 1);
v_a_1499_ = lean_ctor_get(v___x_1483_, 0);
v_isSharedCheck_1506_ = !lean_is_exclusive(v___x_1483_);
if (v_isSharedCheck_1506_ == 0)
{
v___x_1501_ = v___x_1483_;
v_isShared_1502_ = v_isSharedCheck_1506_;
goto v_resetjp_1500_;
}
else
{
lean_inc(v_a_1499_);
lean_dec(v___x_1483_);
v___x_1501_ = lean_box(0);
v_isShared_1502_ = v_isSharedCheck_1506_;
goto v_resetjp_1500_;
}
v_resetjp_1500_:
{
lean_object* v___x_1504_; 
if (v_isShared_1502_ == 0)
{
v___x_1504_ = v___x_1501_;
goto v_reusejp_1503_;
}
else
{
lean_object* v_reuseFailAlloc_1505_; 
v_reuseFailAlloc_1505_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1505_, 0, v_a_1499_);
v___x_1504_ = v_reuseFailAlloc_1505_;
goto v_reusejp_1503_;
}
v_reusejp_1503_:
{
return v___x_1504_;
}
}
}
}
case 4:
{
lean_object* v_declName_1507_; lean_object* v_us_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; 
v_declName_1507_ = lean_ctor_get(v_e_1303_, 0);
v_us_1508_ = lean_ctor_get(v_e_1303_, 1);
v___x_1509_ = lean_box(0);
lean_inc(v_us_1508_);
v___x_1510_ = l_List_mapM_loop___at___00Lean_Meta_Closure_collectExprAux_spec__2___redArg(v_us_1508_, v___x_1509_, v_a_1305_);
if (lean_obj_tag(v___x_1510_) == 0)
{
lean_object* v_a_1511_; lean_object* v___x_1513_; uint8_t v_isShared_1514_; uint8_t v_isSharedCheck_1523_; 
v_a_1511_ = lean_ctor_get(v___x_1510_, 0);
v_isSharedCheck_1523_ = !lean_is_exclusive(v___x_1510_);
if (v_isSharedCheck_1523_ == 0)
{
v___x_1513_ = v___x_1510_;
v_isShared_1514_ = v_isSharedCheck_1523_;
goto v_resetjp_1512_;
}
else
{
lean_inc(v_a_1511_);
lean_dec(v___x_1510_);
v___x_1513_ = lean_box(0);
v_isShared_1514_ = v_isSharedCheck_1523_;
goto v_resetjp_1512_;
}
v_resetjp_1512_:
{
uint8_t v___x_1515_; 
v___x_1515_ = l_ptrEqList___redArg(v_us_1508_, v_a_1511_);
if (v___x_1515_ == 0)
{
lean_object* v___x_1516_; lean_object* v___x_1518_; 
lean_inc(v_declName_1507_);
lean_dec_ref_known(v_e_1303_, 2);
v___x_1516_ = l_Lean_Expr_const___override(v_declName_1507_, v_a_1511_);
if (v_isShared_1514_ == 0)
{
lean_ctor_set(v___x_1513_, 0, v___x_1516_);
v___x_1518_ = v___x_1513_;
goto v_reusejp_1517_;
}
else
{
lean_object* v_reuseFailAlloc_1519_; 
v_reuseFailAlloc_1519_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1519_, 0, v___x_1516_);
v___x_1518_ = v_reuseFailAlloc_1519_;
goto v_reusejp_1517_;
}
v_reusejp_1517_:
{
return v___x_1518_;
}
}
else
{
lean_object* v___x_1521_; 
lean_dec(v_a_1511_);
if (v_isShared_1514_ == 0)
{
lean_ctor_set(v___x_1513_, 0, v_e_1303_);
v___x_1521_ = v___x_1513_;
goto v_reusejp_1520_;
}
else
{
lean_object* v_reuseFailAlloc_1522_; 
v_reuseFailAlloc_1522_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1522_, 0, v_e_1303_);
v___x_1521_ = v_reuseFailAlloc_1522_;
goto v_reusejp_1520_;
}
v_reusejp_1520_:
{
return v___x_1521_;
}
}
}
}
else
{
lean_object* v_a_1524_; lean_object* v___x_1526_; uint8_t v_isShared_1527_; uint8_t v_isSharedCheck_1531_; 
lean_dec_ref_known(v_e_1303_, 2);
v_a_1524_ = lean_ctor_get(v___x_1510_, 0);
v_isSharedCheck_1531_ = !lean_is_exclusive(v___x_1510_);
if (v_isSharedCheck_1531_ == 0)
{
v___x_1526_ = v___x_1510_;
v_isShared_1527_ = v_isSharedCheck_1531_;
goto v_resetjp_1525_;
}
else
{
lean_inc(v_a_1524_);
lean_dec(v___x_1510_);
v___x_1526_ = lean_box(0);
v_isShared_1527_ = v_isSharedCheck_1531_;
goto v_resetjp_1525_;
}
v_resetjp_1525_:
{
lean_object* v___x_1529_; 
if (v_isShared_1527_ == 0)
{
v___x_1529_ = v___x_1526_;
goto v_reusejp_1528_;
}
else
{
lean_object* v_reuseFailAlloc_1530_; 
v_reuseFailAlloc_1530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1530_, 0, v_a_1524_);
v___x_1529_ = v_reuseFailAlloc_1530_;
goto v_reusejp_1528_;
}
v_reusejp_1528_:
{
return v___x_1529_;
}
}
}
}
case 2:
{
lean_object* v_mvarId_1532_; lean_object* v___f_1533_; lean_object* v___x_1534_; 
v_mvarId_1532_ = lean_ctor_get(v_e_1303_, 0);
lean_inc_ref(v_e_1303_);
v___f_1533_ = lean_alloc_closure((void*)(l_Lean_Meta_Closure_collectExprAux___lam__1___boxed), 10, 1);
lean_closure_set(v___f_1533_, 0, v_e_1303_);
lean_inc(v_mvarId_1532_);
v___x_1534_ = l_Lean_MVarId_getDecl(v_mvarId_1532_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
if (lean_obj_tag(v___x_1534_) == 0)
{
lean_object* v_a_1535_; lean_object* v_type_1536_; lean_object* v___x_1537_; 
v_a_1535_ = lean_ctor_get(v___x_1534_, 0);
lean_inc(v_a_1535_);
lean_dec_ref_known(v___x_1534_, 1);
v_type_1536_ = lean_ctor_get(v_a_1535_, 2);
lean_inc_ref_n(v_type_1536_, 2);
lean_dec(v_a_1535_);
v___x_1537_ = l_Lean_Meta_Closure_preprocess(v_type_1536_, v_a_1304_, v_a_1305_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
if (lean_obj_tag(v___x_1537_) == 0)
{
lean_object* v_a_1538_; lean_object* v___x_1539_; 
v_a_1538_ = lean_ctor_get(v___x_1537_, 0);
lean_inc(v_a_1538_);
lean_dec_ref_known(v___x_1537_, 1);
v___x_1539_ = l_Lean_Meta_Closure_collectExprAux___lam__0(v_a_1538_, v_a_1304_, v_a_1305_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
if (lean_obj_tag(v___x_1539_) == 0)
{
lean_object* v_a_1540_; lean_object* v___x_1541_; 
v_a_1540_ = lean_ctor_get(v___x_1539_, 0);
lean_inc(v_a_1540_);
lean_dec_ref_known(v___x_1539_, 1);
v___x_1541_ = l_Lean_mkFreshFVarId___at___00Lean_Meta_Closure_collectExprAux_spec__3(v_a_1304_, v_a_1305_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
if (lean_obj_tag(v___x_1541_) == 0)
{
lean_object* v_a_1542_; lean_object* v___x_1543_; 
v_a_1542_ = lean_ctor_get(v___x_1541_, 0);
lean_inc(v_a_1542_);
lean_dec_ref_known(v___x_1541_, 1);
v___x_1543_ = l_Lean_Meta_Closure_mkNextUserName___redArg(v_a_1305_);
if (lean_obj_tag(v___x_1543_) == 0)
{
lean_object* v_a_1544_; lean_object* v___x_1546_; uint8_t v_isShared_1547_; uint8_t v_isSharedCheck_1605_; 
v_a_1544_ = lean_ctor_get(v___x_1543_, 0);
v_isSharedCheck_1605_ = !lean_is_exclusive(v___x_1543_);
if (v_isSharedCheck_1605_ == 0)
{
v___x_1546_ = v___x_1543_;
v_isShared_1547_ = v_isSharedCheck_1605_;
goto v_resetjp_1545_;
}
else
{
lean_inc(v_a_1544_);
lean_dec(v___x_1543_);
v___x_1546_ = lean_box(0);
v_isShared_1547_ = v_isSharedCheck_1605_;
goto v_resetjp_1545_;
}
v_resetjp_1545_:
{
lean_object* v_e_x27_1549_; lean_object* v___y_1550_; lean_object* v___x_1582_; 
v___x_1582_ = l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__4___redArg(v_mvarId_1532_, v_a_1307_);
if (lean_obj_tag(v___x_1582_) == 0)
{
lean_object* v_a_1583_; 
v_a_1583_ = lean_ctor_get(v___x_1582_, 0);
lean_inc(v_a_1583_);
lean_dec_ref_known(v___x_1582_, 1);
if (lean_obj_tag(v_a_1583_) == 1)
{
lean_object* v_val_1584_; lean_object* v___x_1586_; uint8_t v_isShared_1587_; uint8_t v_isSharedCheck_1596_; 
lean_dec_ref_known(v_e_1303_, 1);
v_val_1584_ = lean_ctor_get(v_a_1583_, 0);
v_isSharedCheck_1596_ = !lean_is_exclusive(v_a_1583_);
if (v_isSharedCheck_1596_ == 0)
{
v___x_1586_ = v_a_1583_;
v_isShared_1587_ = v_isSharedCheck_1596_;
goto v_resetjp_1585_;
}
else
{
lean_inc(v_val_1584_);
lean_dec(v_a_1583_);
v___x_1586_ = lean_box(0);
v_isShared_1587_ = v_isSharedCheck_1596_;
goto v_resetjp_1585_;
}
v_resetjp_1585_:
{
lean_object* v_fvars_1588_; lean_object* v___x_1589_; lean_object* v___x_1591_; 
v_fvars_1588_ = lean_ctor_get(v_val_1584_, 0);
lean_inc_ref(v_fvars_1588_);
lean_dec(v_val_1584_);
v___x_1589_ = lean_array_get_size(v_fvars_1588_);
lean_dec_ref(v_fvars_1588_);
if (v_isShared_1587_ == 0)
{
lean_ctor_set(v___x_1586_, 0, v___x_1589_);
v___x_1591_ = v___x_1586_;
goto v_reusejp_1590_;
}
else
{
lean_object* v_reuseFailAlloc_1595_; 
v_reuseFailAlloc_1595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1595_, 0, v___x_1589_);
v___x_1591_ = v_reuseFailAlloc_1595_;
goto v_reusejp_1590_;
}
v_reusejp_1590_:
{
uint8_t v___x_1592_; lean_object* v___x_1593_; 
v___x_1592_ = 0;
v___x_1593_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Closure_collectExprAux_spec__5___redArg(v_type_1536_, v___x_1591_, v___f_1533_, v___x_1592_, v___x_1592_, v_a_1304_, v_a_1305_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
if (lean_obj_tag(v___x_1593_) == 0)
{
lean_object* v_a_1594_; 
v_a_1594_ = lean_ctor_get(v___x_1593_, 0);
lean_inc(v_a_1594_);
lean_dec_ref_known(v___x_1593_, 1);
v_e_x27_1549_ = v_a_1594_;
v___y_1550_ = v_a_1305_;
goto v___jp_1548_;
}
else
{
lean_del_object(v___x_1546_);
lean_dec(v_a_1544_);
lean_dec(v_a_1542_);
lean_dec(v_a_1540_);
return v___x_1593_;
}
}
}
}
else
{
lean_dec(v_a_1583_);
lean_dec_ref(v_type_1536_);
lean_dec_ref(v___f_1533_);
v_e_x27_1549_ = v_e_1303_;
v___y_1550_ = v_a_1305_;
goto v___jp_1548_;
}
}
else
{
lean_object* v_a_1597_; lean_object* v___x_1599_; uint8_t v_isShared_1600_; uint8_t v_isSharedCheck_1604_; 
lean_del_object(v___x_1546_);
lean_dec(v_a_1544_);
lean_dec(v_a_1542_);
lean_dec(v_a_1540_);
lean_dec_ref(v_type_1536_);
lean_dec_ref(v___f_1533_);
lean_dec_ref_known(v_e_1303_, 1);
v_a_1597_ = lean_ctor_get(v___x_1582_, 0);
v_isSharedCheck_1604_ = !lean_is_exclusive(v___x_1582_);
if (v_isSharedCheck_1604_ == 0)
{
v___x_1599_ = v___x_1582_;
v_isShared_1600_ = v_isSharedCheck_1604_;
goto v_resetjp_1598_;
}
else
{
lean_inc(v_a_1597_);
lean_dec(v___x_1582_);
v___x_1599_ = lean_box(0);
v_isShared_1600_ = v_isSharedCheck_1604_;
goto v_resetjp_1598_;
}
v_resetjp_1598_:
{
lean_object* v___x_1602_; 
if (v_isShared_1600_ == 0)
{
v___x_1602_ = v___x_1599_;
goto v_reusejp_1601_;
}
else
{
lean_object* v_reuseFailAlloc_1603_; 
v_reuseFailAlloc_1603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1603_, 0, v_a_1597_);
v___x_1602_ = v_reuseFailAlloc_1603_;
goto v_reusejp_1601_;
}
v_reusejp_1601_:
{
return v___x_1602_;
}
}
}
v___jp_1548_:
{
lean_object* v___x_1551_; lean_object* v_visitedLevel_1552_; lean_object* v_visitedExpr_1553_; lean_object* v_levelParams_1554_; lean_object* v_nextLevelIdx_1555_; lean_object* v_levelArgs_1556_; lean_object* v_newLocalDecls_1557_; lean_object* v_newLocalDeclsForMVars_1558_; lean_object* v_newLetDecls_1559_; lean_object* v_nextExprIdx_1560_; lean_object* v_exprMVarArgs_1561_; lean_object* v_exprFVarArgs_1562_; lean_object* v_toProcess_1563_; lean_object* v___x_1565_; uint8_t v_isShared_1566_; uint8_t v_isSharedCheck_1581_; 
v___x_1551_ = lean_st_ref_take(v___y_1550_);
v_visitedLevel_1552_ = lean_ctor_get(v___x_1551_, 0);
v_visitedExpr_1553_ = lean_ctor_get(v___x_1551_, 1);
v_levelParams_1554_ = lean_ctor_get(v___x_1551_, 2);
v_nextLevelIdx_1555_ = lean_ctor_get(v___x_1551_, 3);
v_levelArgs_1556_ = lean_ctor_get(v___x_1551_, 4);
v_newLocalDecls_1557_ = lean_ctor_get(v___x_1551_, 5);
v_newLocalDeclsForMVars_1558_ = lean_ctor_get(v___x_1551_, 6);
v_newLetDecls_1559_ = lean_ctor_get(v___x_1551_, 7);
v_nextExprIdx_1560_ = lean_ctor_get(v___x_1551_, 8);
v_exprMVarArgs_1561_ = lean_ctor_get(v___x_1551_, 9);
v_exprFVarArgs_1562_ = lean_ctor_get(v___x_1551_, 10);
v_toProcess_1563_ = lean_ctor_get(v___x_1551_, 11);
v_isSharedCheck_1581_ = !lean_is_exclusive(v___x_1551_);
if (v_isSharedCheck_1581_ == 0)
{
v___x_1565_ = v___x_1551_;
v_isShared_1566_ = v_isSharedCheck_1581_;
goto v_resetjp_1564_;
}
else
{
lean_inc(v_toProcess_1563_);
lean_inc(v_exprFVarArgs_1562_);
lean_inc(v_exprMVarArgs_1561_);
lean_inc(v_nextExprIdx_1560_);
lean_inc(v_newLetDecls_1559_);
lean_inc(v_newLocalDeclsForMVars_1558_);
lean_inc(v_newLocalDecls_1557_);
lean_inc(v_levelArgs_1556_);
lean_inc(v_nextLevelIdx_1555_);
lean_inc(v_levelParams_1554_);
lean_inc(v_visitedExpr_1553_);
lean_inc(v_visitedLevel_1552_);
lean_dec(v___x_1551_);
v___x_1565_ = lean_box(0);
v_isShared_1566_ = v_isSharedCheck_1581_;
goto v_resetjp_1564_;
}
v_resetjp_1564_:
{
lean_object* v___x_1567_; uint8_t v___x_1568_; uint8_t v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1574_; 
v___x_1567_ = lean_unsigned_to_nat(0u);
v___x_1568_ = 0;
v___x_1569_ = 0;
lean_inc(v_a_1542_);
v___x_1570_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_1570_, 0, v___x_1567_);
lean_ctor_set(v___x_1570_, 1, v_a_1542_);
lean_ctor_set(v___x_1570_, 2, v_a_1544_);
lean_ctor_set(v___x_1570_, 3, v_a_1540_);
lean_ctor_set_uint8(v___x_1570_, sizeof(void*)*4, v___x_1568_);
lean_ctor_set_uint8(v___x_1570_, sizeof(void*)*4 + 1, v___x_1569_);
v___x_1571_ = lean_array_push(v_newLocalDeclsForMVars_1558_, v___x_1570_);
v___x_1572_ = lean_array_push(v_exprMVarArgs_1561_, v_e_x27_1549_);
if (v_isShared_1566_ == 0)
{
lean_ctor_set(v___x_1565_, 9, v___x_1572_);
lean_ctor_set(v___x_1565_, 6, v___x_1571_);
v___x_1574_ = v___x_1565_;
goto v_reusejp_1573_;
}
else
{
lean_object* v_reuseFailAlloc_1580_; 
v_reuseFailAlloc_1580_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_1580_, 0, v_visitedLevel_1552_);
lean_ctor_set(v_reuseFailAlloc_1580_, 1, v_visitedExpr_1553_);
lean_ctor_set(v_reuseFailAlloc_1580_, 2, v_levelParams_1554_);
lean_ctor_set(v_reuseFailAlloc_1580_, 3, v_nextLevelIdx_1555_);
lean_ctor_set(v_reuseFailAlloc_1580_, 4, v_levelArgs_1556_);
lean_ctor_set(v_reuseFailAlloc_1580_, 5, v_newLocalDecls_1557_);
lean_ctor_set(v_reuseFailAlloc_1580_, 6, v___x_1571_);
lean_ctor_set(v_reuseFailAlloc_1580_, 7, v_newLetDecls_1559_);
lean_ctor_set(v_reuseFailAlloc_1580_, 8, v_nextExprIdx_1560_);
lean_ctor_set(v_reuseFailAlloc_1580_, 9, v___x_1572_);
lean_ctor_set(v_reuseFailAlloc_1580_, 10, v_exprFVarArgs_1562_);
lean_ctor_set(v_reuseFailAlloc_1580_, 11, v_toProcess_1563_);
v___x_1574_ = v_reuseFailAlloc_1580_;
goto v_reusejp_1573_;
}
v_reusejp_1573_:
{
lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1578_; 
v___x_1575_ = lean_st_ref_put(v___y_1550_, v___x_1574_);
v___x_1576_ = l_Lean_mkFVar(v_a_1542_);
if (v_isShared_1547_ == 0)
{
lean_ctor_set(v___x_1546_, 0, v___x_1576_);
v___x_1578_ = v___x_1546_;
goto v_reusejp_1577_;
}
else
{
lean_object* v_reuseFailAlloc_1579_; 
v_reuseFailAlloc_1579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1579_, 0, v___x_1576_);
v___x_1578_ = v_reuseFailAlloc_1579_;
goto v_reusejp_1577_;
}
v_reusejp_1577_:
{
return v___x_1578_;
}
}
}
}
}
}
else
{
lean_object* v_a_1606_; lean_object* v___x_1608_; uint8_t v_isShared_1609_; uint8_t v_isSharedCheck_1613_; 
lean_dec(v_a_1542_);
lean_dec(v_a_1540_);
lean_dec_ref(v_type_1536_);
lean_dec_ref(v___f_1533_);
lean_dec_ref_known(v_e_1303_, 1);
v_a_1606_ = lean_ctor_get(v___x_1543_, 0);
v_isSharedCheck_1613_ = !lean_is_exclusive(v___x_1543_);
if (v_isSharedCheck_1613_ == 0)
{
v___x_1608_ = v___x_1543_;
v_isShared_1609_ = v_isSharedCheck_1613_;
goto v_resetjp_1607_;
}
else
{
lean_inc(v_a_1606_);
lean_dec(v___x_1543_);
v___x_1608_ = lean_box(0);
v_isShared_1609_ = v_isSharedCheck_1613_;
goto v_resetjp_1607_;
}
v_resetjp_1607_:
{
lean_object* v___x_1611_; 
if (v_isShared_1609_ == 0)
{
v___x_1611_ = v___x_1608_;
goto v_reusejp_1610_;
}
else
{
lean_object* v_reuseFailAlloc_1612_; 
v_reuseFailAlloc_1612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1612_, 0, v_a_1606_);
v___x_1611_ = v_reuseFailAlloc_1612_;
goto v_reusejp_1610_;
}
v_reusejp_1610_:
{
return v___x_1611_;
}
}
}
}
else
{
lean_object* v_a_1614_; lean_object* v___x_1616_; uint8_t v_isShared_1617_; uint8_t v_isSharedCheck_1621_; 
lean_dec(v_a_1540_);
lean_dec_ref(v_type_1536_);
lean_dec_ref(v___f_1533_);
lean_dec_ref_known(v_e_1303_, 1);
v_a_1614_ = lean_ctor_get(v___x_1541_, 0);
v_isSharedCheck_1621_ = !lean_is_exclusive(v___x_1541_);
if (v_isSharedCheck_1621_ == 0)
{
v___x_1616_ = v___x_1541_;
v_isShared_1617_ = v_isSharedCheck_1621_;
goto v_resetjp_1615_;
}
else
{
lean_inc(v_a_1614_);
lean_dec(v___x_1541_);
v___x_1616_ = lean_box(0);
v_isShared_1617_ = v_isSharedCheck_1621_;
goto v_resetjp_1615_;
}
v_resetjp_1615_:
{
lean_object* v___x_1619_; 
if (v_isShared_1617_ == 0)
{
v___x_1619_ = v___x_1616_;
goto v_reusejp_1618_;
}
else
{
lean_object* v_reuseFailAlloc_1620_; 
v_reuseFailAlloc_1620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1620_, 0, v_a_1614_);
v___x_1619_ = v_reuseFailAlloc_1620_;
goto v_reusejp_1618_;
}
v_reusejp_1618_:
{
return v___x_1619_;
}
}
}
}
else
{
lean_dec_ref(v_type_1536_);
lean_dec_ref(v___f_1533_);
lean_dec_ref_known(v_e_1303_, 1);
return v___x_1539_;
}
}
else
{
lean_dec_ref(v_type_1536_);
lean_dec_ref(v___f_1533_);
lean_dec_ref_known(v_e_1303_, 1);
return v___x_1537_;
}
}
else
{
lean_object* v_a_1622_; lean_object* v___x_1624_; uint8_t v_isShared_1625_; uint8_t v_isSharedCheck_1629_; 
lean_dec_ref(v___f_1533_);
lean_dec_ref_known(v_e_1303_, 1);
v_a_1622_ = lean_ctor_get(v___x_1534_, 0);
v_isSharedCheck_1629_ = !lean_is_exclusive(v___x_1534_);
if (v_isSharedCheck_1629_ == 0)
{
v___x_1624_ = v___x_1534_;
v_isShared_1625_ = v_isSharedCheck_1629_;
goto v_resetjp_1623_;
}
else
{
lean_inc(v_a_1622_);
lean_dec(v___x_1534_);
v___x_1624_ = lean_box(0);
v_isShared_1625_ = v_isSharedCheck_1629_;
goto v_resetjp_1623_;
}
v_resetjp_1623_:
{
lean_object* v___x_1627_; 
if (v_isShared_1625_ == 0)
{
v___x_1627_ = v___x_1624_;
goto v_reusejp_1626_;
}
else
{
lean_object* v_reuseFailAlloc_1628_; 
v_reuseFailAlloc_1628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1628_, 0, v_a_1622_);
v___x_1627_ = v_reuseFailAlloc_1628_;
goto v_reusejp_1626_;
}
v_reusejp_1626_:
{
return v___x_1627_;
}
}
}
}
case 1:
{
lean_object* v_fvarId_1630_; lean_object* v___y_1632_; lean_object* v___y_1633_; lean_object* v___y_1634_; lean_object* v___y_1635_; lean_object* v___y_1636_; lean_object* v___y_1637_; uint8_t v___x_1667_; lean_object* v___x_1668_; 
v_fvarId_1630_ = lean_ctor_get(v_e_1303_, 0);
lean_inc_n(v_fvarId_1630_, 2);
lean_dec_ref_known(v_e_1303_, 1);
v___x_1667_ = 0;
v___x_1668_ = l_Lean_FVarId_getValue_x3f___redArg(v_fvarId_1630_, v___x_1667_, v_a_1306_, v_a_1308_, v_a_1309_);
if (lean_obj_tag(v___x_1668_) == 0)
{
uint8_t v_zetaDelta_1669_; 
v_zetaDelta_1669_ = lean_ctor_get_uint8(v_a_1304_, 0);
if (v_zetaDelta_1669_ == 1)
{
lean_object* v_a_1670_; 
v_a_1670_ = lean_ctor_get(v___x_1668_, 0);
lean_inc(v_a_1670_);
lean_dec_ref_known(v___x_1668_, 1);
if (lean_obj_tag(v_a_1670_) == 1)
{
lean_object* v_val_1671_; lean_object* v___x_1672_; 
lean_dec(v_fvarId_1630_);
v_val_1671_ = lean_ctor_get(v_a_1670_, 0);
lean_inc(v_val_1671_);
lean_dec_ref_known(v_a_1670_, 1);
v___x_1672_ = l_Lean_Meta_Closure_preprocess(v_val_1671_, v_a_1304_, v_a_1305_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
if (lean_obj_tag(v___x_1672_) == 0)
{
lean_object* v_a_1673_; lean_object* v___x_1674_; 
v_a_1673_ = lean_ctor_get(v___x_1672_, 0);
lean_inc(v_a_1673_);
lean_dec_ref_known(v___x_1672_, 1);
v___x_1674_ = l_Lean_Meta_Closure_collectExprAux___lam__0(v_a_1673_, v_a_1304_, v_a_1305_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
return v___x_1674_;
}
else
{
return v___x_1672_;
}
}
else
{
lean_dec(v_a_1670_);
v___y_1632_ = v_a_1304_;
v___y_1633_ = v_a_1305_;
v___y_1634_ = v_a_1306_;
v___y_1635_ = v_a_1307_;
v___y_1636_ = v_a_1308_;
v___y_1637_ = v_a_1309_;
goto v___jp_1631_;
}
}
else
{
lean_dec_ref_known(v___x_1668_, 1);
v___y_1632_ = v_a_1304_;
v___y_1633_ = v_a_1305_;
v___y_1634_ = v_a_1306_;
v___y_1635_ = v_a_1307_;
v___y_1636_ = v_a_1308_;
v___y_1637_ = v_a_1309_;
goto v___jp_1631_;
}
}
else
{
lean_object* v_a_1675_; lean_object* v___x_1677_; uint8_t v_isShared_1678_; uint8_t v_isSharedCheck_1682_; 
lean_dec(v_fvarId_1630_);
v_a_1675_ = lean_ctor_get(v___x_1668_, 0);
v_isSharedCheck_1682_ = !lean_is_exclusive(v___x_1668_);
if (v_isSharedCheck_1682_ == 0)
{
v___x_1677_ = v___x_1668_;
v_isShared_1678_ = v_isSharedCheck_1682_;
goto v_resetjp_1676_;
}
else
{
lean_inc(v_a_1675_);
lean_dec(v___x_1668_);
v___x_1677_ = lean_box(0);
v_isShared_1678_ = v_isSharedCheck_1682_;
goto v_resetjp_1676_;
}
v_resetjp_1676_:
{
lean_object* v___x_1680_; 
if (v_isShared_1678_ == 0)
{
v___x_1680_ = v___x_1677_;
goto v_reusejp_1679_;
}
else
{
lean_object* v_reuseFailAlloc_1681_; 
v_reuseFailAlloc_1681_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1681_, 0, v_a_1675_);
v___x_1680_ = v_reuseFailAlloc_1681_;
goto v_reusejp_1679_;
}
v_reusejp_1679_:
{
return v___x_1680_;
}
}
}
v___jp_1631_:
{
lean_object* v___x_1638_; 
v___x_1638_ = l_Lean_mkFreshFVarId___at___00Lean_Meta_Closure_collectExprAux_spec__3(v___y_1632_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_, v___y_1637_);
if (lean_obj_tag(v___x_1638_) == 0)
{
lean_object* v_a_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; 
v_a_1639_ = lean_ctor_get(v___x_1638_, 0);
lean_inc_n(v_a_1639_, 2);
lean_dec_ref_known(v___x_1638_, 1);
v___x_1640_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1640_, 0, v_fvarId_1630_);
lean_ctor_set(v___x_1640_, 1, v_a_1639_);
v___x_1641_ = l_Lean_Meta_Closure_pushToProcess___redArg(v___x_1640_, v___y_1633_);
if (lean_obj_tag(v___x_1641_) == 0)
{
lean_object* v___x_1643_; uint8_t v_isShared_1644_; uint8_t v_isSharedCheck_1649_; 
v_isSharedCheck_1649_ = !lean_is_exclusive(v___x_1641_);
if (v_isSharedCheck_1649_ == 0)
{
lean_object* v_unused_1650_; 
v_unused_1650_ = lean_ctor_get(v___x_1641_, 0);
lean_dec(v_unused_1650_);
v___x_1643_ = v___x_1641_;
v_isShared_1644_ = v_isSharedCheck_1649_;
goto v_resetjp_1642_;
}
else
{
lean_dec(v___x_1641_);
v___x_1643_ = lean_box(0);
v_isShared_1644_ = v_isSharedCheck_1649_;
goto v_resetjp_1642_;
}
v_resetjp_1642_:
{
lean_object* v___x_1645_; lean_object* v___x_1647_; 
v___x_1645_ = l_Lean_mkFVar(v_a_1639_);
if (v_isShared_1644_ == 0)
{
lean_ctor_set(v___x_1643_, 0, v___x_1645_);
v___x_1647_ = v___x_1643_;
goto v_reusejp_1646_;
}
else
{
lean_object* v_reuseFailAlloc_1648_; 
v_reuseFailAlloc_1648_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1648_, 0, v___x_1645_);
v___x_1647_ = v_reuseFailAlloc_1648_;
goto v_reusejp_1646_;
}
v_reusejp_1646_:
{
return v___x_1647_;
}
}
}
else
{
lean_object* v_a_1651_; lean_object* v___x_1653_; uint8_t v_isShared_1654_; uint8_t v_isSharedCheck_1658_; 
lean_dec(v_a_1639_);
v_a_1651_ = lean_ctor_get(v___x_1641_, 0);
v_isSharedCheck_1658_ = !lean_is_exclusive(v___x_1641_);
if (v_isSharedCheck_1658_ == 0)
{
v___x_1653_ = v___x_1641_;
v_isShared_1654_ = v_isSharedCheck_1658_;
goto v_resetjp_1652_;
}
else
{
lean_inc(v_a_1651_);
lean_dec(v___x_1641_);
v___x_1653_ = lean_box(0);
v_isShared_1654_ = v_isSharedCheck_1658_;
goto v_resetjp_1652_;
}
v_resetjp_1652_:
{
lean_object* v___x_1656_; 
if (v_isShared_1654_ == 0)
{
v___x_1656_ = v___x_1653_;
goto v_reusejp_1655_;
}
else
{
lean_object* v_reuseFailAlloc_1657_; 
v_reuseFailAlloc_1657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1657_, 0, v_a_1651_);
v___x_1656_ = v_reuseFailAlloc_1657_;
goto v_reusejp_1655_;
}
v_reusejp_1655_:
{
return v___x_1656_;
}
}
}
}
else
{
lean_object* v_a_1659_; lean_object* v___x_1661_; uint8_t v_isShared_1662_; uint8_t v_isSharedCheck_1666_; 
lean_dec(v_fvarId_1630_);
v_a_1659_ = lean_ctor_get(v___x_1638_, 0);
v_isSharedCheck_1666_ = !lean_is_exclusive(v___x_1638_);
if (v_isSharedCheck_1666_ == 0)
{
v___x_1661_ = v___x_1638_;
v_isShared_1662_ = v_isSharedCheck_1666_;
goto v_resetjp_1660_;
}
else
{
lean_inc(v_a_1659_);
lean_dec(v___x_1638_);
v___x_1661_ = lean_box(0);
v_isShared_1662_ = v_isSharedCheck_1666_;
goto v_resetjp_1660_;
}
v_resetjp_1660_:
{
lean_object* v___x_1664_; 
if (v_isShared_1662_ == 0)
{
v___x_1664_ = v___x_1661_;
goto v_reusejp_1663_;
}
else
{
lean_object* v_reuseFailAlloc_1665_; 
v_reuseFailAlloc_1665_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1665_, 0, v_a_1659_);
v___x_1664_ = v_reuseFailAlloc_1665_;
goto v_reusejp_1663_;
}
v_reusejp_1663_:
{
return v___x_1664_;
}
}
}
}
}
default: 
{
lean_object* v___x_1683_; 
v___x_1683_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1683_, 0, v_e_1303_);
return v___x_1683_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectExprAux___lam__0(lean_object* v_e_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_){
_start:
{
uint8_t v___x_1735_; 
v___x_1735_ = l_Lean_Expr_hasLevelParam(v_e_1684_);
if (v___x_1735_ == 0)
{
uint8_t v___x_1736_; 
v___x_1736_ = l_Lean_Expr_hasFVar(v_e_1684_);
if (v___x_1736_ == 0)
{
uint8_t v___x_1737_; 
v___x_1737_ = l_Lean_Expr_hasMVar(v_e_1684_);
if (v___x_1737_ == 0)
{
lean_object* v___x_1738_; 
v___x_1738_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1738_, 0, v_e_1684_);
return v___x_1738_;
}
else
{
goto v___jp_1692_;
}
}
else
{
goto v___jp_1692_;
}
}
else
{
goto v___jp_1692_;
}
v___jp_1692_:
{
lean_object* v___x_1693_; lean_object* v_visitedExpr_1694_; lean_object* v___x_1695_; 
v___x_1693_ = lean_st_ref_get(v___y_1686_);
v_visitedExpr_1694_ = lean_ctor_get(v___x_1693_, 1);
lean_inc_ref(v_visitedExpr_1694_);
lean_dec(v___x_1693_);
v___x_1695_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0___redArg(v_visitedExpr_1694_, v_e_1684_);
lean_dec_ref(v_visitedExpr_1694_);
if (lean_obj_tag(v___x_1695_) == 0)
{
lean_object* v___x_1696_; 
lean_inc_ref(v_e_1684_);
v___x_1696_ = l_Lean_Meta_Closure_collectExprAux(v_e_1684_, v___y_1685_, v___y_1686_, v___y_1687_, v___y_1688_, v___y_1689_, v___y_1690_);
if (lean_obj_tag(v___x_1696_) == 0)
{
lean_object* v_a_1697_; lean_object* v___x_1699_; uint8_t v_isShared_1700_; uint8_t v_isSharedCheck_1726_; 
v_a_1697_ = lean_ctor_get(v___x_1696_, 0);
v_isSharedCheck_1726_ = !lean_is_exclusive(v___x_1696_);
if (v_isSharedCheck_1726_ == 0)
{
v___x_1699_ = v___x_1696_;
v_isShared_1700_ = v_isSharedCheck_1726_;
goto v_resetjp_1698_;
}
else
{
lean_inc(v_a_1697_);
lean_dec(v___x_1696_);
v___x_1699_ = lean_box(0);
v_isShared_1700_ = v_isSharedCheck_1726_;
goto v_resetjp_1698_;
}
v_resetjp_1698_:
{
lean_object* v___x_1701_; lean_object* v_visitedLevel_1702_; lean_object* v_visitedExpr_1703_; lean_object* v_levelParams_1704_; lean_object* v_nextLevelIdx_1705_; lean_object* v_levelArgs_1706_; lean_object* v_newLocalDecls_1707_; lean_object* v_newLocalDeclsForMVars_1708_; lean_object* v_newLetDecls_1709_; lean_object* v_nextExprIdx_1710_; lean_object* v_exprMVarArgs_1711_; lean_object* v_exprFVarArgs_1712_; lean_object* v_toProcess_1713_; lean_object* v___x_1715_; uint8_t v_isShared_1716_; uint8_t v_isSharedCheck_1725_; 
v___x_1701_ = lean_st_ref_take(v___y_1686_);
v_visitedLevel_1702_ = lean_ctor_get(v___x_1701_, 0);
v_visitedExpr_1703_ = lean_ctor_get(v___x_1701_, 1);
v_levelParams_1704_ = lean_ctor_get(v___x_1701_, 2);
v_nextLevelIdx_1705_ = lean_ctor_get(v___x_1701_, 3);
v_levelArgs_1706_ = lean_ctor_get(v___x_1701_, 4);
v_newLocalDecls_1707_ = lean_ctor_get(v___x_1701_, 5);
v_newLocalDeclsForMVars_1708_ = lean_ctor_get(v___x_1701_, 6);
v_newLetDecls_1709_ = lean_ctor_get(v___x_1701_, 7);
v_nextExprIdx_1710_ = lean_ctor_get(v___x_1701_, 8);
v_exprMVarArgs_1711_ = lean_ctor_get(v___x_1701_, 9);
v_exprFVarArgs_1712_ = lean_ctor_get(v___x_1701_, 10);
v_toProcess_1713_ = lean_ctor_get(v___x_1701_, 11);
v_isSharedCheck_1725_ = !lean_is_exclusive(v___x_1701_);
if (v_isSharedCheck_1725_ == 0)
{
v___x_1715_ = v___x_1701_;
v_isShared_1716_ = v_isSharedCheck_1725_;
goto v_resetjp_1714_;
}
else
{
lean_inc(v_toProcess_1713_);
lean_inc(v_exprFVarArgs_1712_);
lean_inc(v_exprMVarArgs_1711_);
lean_inc(v_nextExprIdx_1710_);
lean_inc(v_newLetDecls_1709_);
lean_inc(v_newLocalDeclsForMVars_1708_);
lean_inc(v_newLocalDecls_1707_);
lean_inc(v_levelArgs_1706_);
lean_inc(v_nextLevelIdx_1705_);
lean_inc(v_levelParams_1704_);
lean_inc(v_visitedExpr_1703_);
lean_inc(v_visitedLevel_1702_);
lean_dec(v___x_1701_);
v___x_1715_ = lean_box(0);
v_isShared_1716_ = v_isSharedCheck_1725_;
goto v_resetjp_1714_;
}
v_resetjp_1714_:
{
lean_object* v___x_1717_; lean_object* v___x_1719_; 
lean_inc(v_a_1697_);
v___x_1717_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1___redArg(v_visitedExpr_1703_, v_e_1684_, v_a_1697_);
if (v_isShared_1716_ == 0)
{
lean_ctor_set(v___x_1715_, 1, v___x_1717_);
v___x_1719_ = v___x_1715_;
goto v_reusejp_1718_;
}
else
{
lean_object* v_reuseFailAlloc_1724_; 
v_reuseFailAlloc_1724_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_1724_, 0, v_visitedLevel_1702_);
lean_ctor_set(v_reuseFailAlloc_1724_, 1, v___x_1717_);
lean_ctor_set(v_reuseFailAlloc_1724_, 2, v_levelParams_1704_);
lean_ctor_set(v_reuseFailAlloc_1724_, 3, v_nextLevelIdx_1705_);
lean_ctor_set(v_reuseFailAlloc_1724_, 4, v_levelArgs_1706_);
lean_ctor_set(v_reuseFailAlloc_1724_, 5, v_newLocalDecls_1707_);
lean_ctor_set(v_reuseFailAlloc_1724_, 6, v_newLocalDeclsForMVars_1708_);
lean_ctor_set(v_reuseFailAlloc_1724_, 7, v_newLetDecls_1709_);
lean_ctor_set(v_reuseFailAlloc_1724_, 8, v_nextExprIdx_1710_);
lean_ctor_set(v_reuseFailAlloc_1724_, 9, v_exprMVarArgs_1711_);
lean_ctor_set(v_reuseFailAlloc_1724_, 10, v_exprFVarArgs_1712_);
lean_ctor_set(v_reuseFailAlloc_1724_, 11, v_toProcess_1713_);
v___x_1719_ = v_reuseFailAlloc_1724_;
goto v_reusejp_1718_;
}
v_reusejp_1718_:
{
lean_object* v___x_1720_; lean_object* v___x_1722_; 
v___x_1720_ = lean_st_ref_put(v___y_1686_, v___x_1719_);
if (v_isShared_1700_ == 0)
{
v___x_1722_ = v___x_1699_;
goto v_reusejp_1721_;
}
else
{
lean_object* v_reuseFailAlloc_1723_; 
v_reuseFailAlloc_1723_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1723_, 0, v_a_1697_);
v___x_1722_ = v_reuseFailAlloc_1723_;
goto v_reusejp_1721_;
}
v_reusejp_1721_:
{
return v___x_1722_;
}
}
}
}
}
else
{
lean_dec_ref(v_e_1684_);
return v___x_1696_;
}
}
else
{
lean_object* v_val_1727_; lean_object* v___x_1729_; uint8_t v_isShared_1730_; uint8_t v_isSharedCheck_1734_; 
lean_dec_ref(v_e_1684_);
v_val_1727_ = lean_ctor_get(v___x_1695_, 0);
v_isSharedCheck_1734_ = !lean_is_exclusive(v___x_1695_);
if (v_isSharedCheck_1734_ == 0)
{
v___x_1729_ = v___x_1695_;
v_isShared_1730_ = v_isSharedCheck_1734_;
goto v_resetjp_1728_;
}
else
{
lean_inc(v_val_1727_);
lean_dec(v___x_1695_);
v___x_1729_ = lean_box(0);
v_isShared_1730_ = v_isSharedCheck_1734_;
goto v_resetjp_1728_;
}
v_resetjp_1728_:
{
lean_object* v___x_1732_; 
if (v_isShared_1730_ == 0)
{
lean_ctor_set_tag(v___x_1729_, 0);
v___x_1732_ = v___x_1729_;
goto v_reusejp_1731_;
}
else
{
lean_object* v_reuseFailAlloc_1733_; 
v_reuseFailAlloc_1733_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1733_, 0, v_val_1727_);
v___x_1732_ = v_reuseFailAlloc_1733_;
goto v_reusejp_1731_;
}
v_reusejp_1731_:
{
return v___x_1732_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectExprAux___lam__0___boxed(lean_object* v_e_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_, lean_object* v___y_1746_){
_start:
{
lean_object* v_res_1747_; 
v_res_1747_ = l_Lean_Meta_Closure_collectExprAux___lam__0(v_e_1739_, v___y_1740_, v___y_1741_, v___y_1742_, v___y_1743_, v___y_1744_, v___y_1745_);
lean_dec(v___y_1745_);
lean_dec_ref(v___y_1744_);
lean_dec(v___y_1743_);
lean_dec_ref(v___y_1742_);
lean_dec(v___y_1741_);
lean_dec_ref(v___y_1740_);
return v_res_1747_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectExprAux___boxed(lean_object* v_e_1748_, lean_object* v_a_1749_, lean_object* v_a_1750_, lean_object* v_a_1751_, lean_object* v_a_1752_, lean_object* v_a_1753_, lean_object* v_a_1754_, lean_object* v_a_1755_){
_start:
{
lean_object* v_res_1756_; 
v_res_1756_ = l_Lean_Meta_Closure_collectExprAux(v_e_1748_, v_a_1749_, v_a_1750_, v_a_1751_, v_a_1752_, v_a_1753_, v_a_1754_);
lean_dec(v_a_1754_);
lean_dec_ref(v_a_1753_);
lean_dec(v_a_1752_);
lean_dec_ref(v_a_1751_);
lean_dec(v_a_1750_);
lean_dec_ref(v_a_1749_);
return v_res_1756_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0(lean_object* v_00_u03b2_1757_, lean_object* v_m_1758_, lean_object* v_a_1759_){
_start:
{
lean_object* v___x_1760_; 
v___x_1760_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0___redArg(v_m_1758_, v_a_1759_);
return v___x_1760_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0___boxed(lean_object* v_00_u03b2_1761_, lean_object* v_m_1762_, lean_object* v_a_1763_){
_start:
{
lean_object* v_res_1764_; 
v_res_1764_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0(v_00_u03b2_1761_, v_m_1762_, v_a_1763_);
lean_dec_ref(v_a_1763_);
lean_dec_ref(v_m_1762_);
return v_res_1764_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1(lean_object* v_00_u03b2_1765_, lean_object* v_m_1766_, lean_object* v_a_1767_, lean_object* v_b_1768_){
_start:
{
lean_object* v___x_1769_; 
v___x_1769_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1___redArg(v_m_1766_, v_a_1767_, v_b_1768_);
return v___x_1769_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Closure_collectExprAux_spec__2(lean_object* v_x_1770_, lean_object* v_x_1771_, lean_object* v___y_1772_, lean_object* v___y_1773_, lean_object* v___y_1774_, lean_object* v___y_1775_, lean_object* v___y_1776_, lean_object* v___y_1777_){
_start:
{
lean_object* v___x_1779_; 
v___x_1779_ = l_List_mapM_loop___at___00Lean_Meta_Closure_collectExprAux_spec__2___redArg(v_x_1770_, v_x_1771_, v___y_1773_);
return v___x_1779_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Closure_collectExprAux_spec__2___boxed(lean_object* v_x_1780_, lean_object* v_x_1781_, lean_object* v___y_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_){
_start:
{
lean_object* v_res_1789_; 
v_res_1789_ = l_List_mapM_loop___at___00Lean_Meta_Closure_collectExprAux_spec__2(v_x_1780_, v_x_1781_, v___y_1782_, v___y_1783_, v___y_1784_, v___y_1785_, v___y_1786_, v___y_1787_);
lean_dec(v___y_1787_);
lean_dec_ref(v___y_1786_);
lean_dec(v___y_1785_);
lean_dec_ref(v___y_1784_);
lean_dec(v___y_1783_);
lean_dec_ref(v___y_1782_);
return v_res_1789_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Closure_collectExprAux_spec__3_spec__7(lean_object* v___y_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_, lean_object* v___y_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_){
_start:
{
lean_object* v___x_1797_; 
v___x_1797_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Closure_collectExprAux_spec__3_spec__7___redArg(v___y_1795_);
return v___x_1797_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Closure_collectExprAux_spec__3_spec__7___boxed(lean_object* v___y_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_){
_start:
{
lean_object* v_res_1805_; 
v_res_1805_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Closure_collectExprAux_spec__3_spec__7(v___y_1798_, v___y_1799_, v___y_1800_, v___y_1801_, v___y_1802_, v___y_1803_);
lean_dec(v___y_1803_);
lean_dec_ref(v___y_1802_);
lean_dec(v___y_1801_);
lean_dec_ref(v___y_1800_);
lean_dec(v___y_1799_);
lean_dec_ref(v___y_1798_);
return v_res_1805_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0_spec__0(lean_object* v_00_u03b2_1806_, lean_object* v_a_1807_, lean_object* v_x_1808_){
_start:
{
lean_object* v___x_1809_; 
v___x_1809_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0_spec__0___redArg(v_a_1807_, v_x_1808_);
return v___x_1809_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1810_, lean_object* v_a_1811_, lean_object* v_x_1812_){
_start:
{
lean_object* v_res_1813_; 
v_res_1813_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0_spec__0(v_00_u03b2_1810_, v_a_1811_, v_x_1812_);
lean_dec(v_x_1812_);
lean_dec_ref(v_a_1811_);
return v_res_1813_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__2(lean_object* v_00_u03b2_1814_, lean_object* v_a_1815_, lean_object* v_x_1816_){
_start:
{
uint8_t v___x_1817_; 
v___x_1817_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__2___redArg(v_a_1815_, v_x_1816_);
return v___x_1817_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1818_, lean_object* v_a_1819_, lean_object* v_x_1820_){
_start:
{
uint8_t v_res_1821_; lean_object* v_r_1822_; 
v_res_1821_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__2(v_00_u03b2_1818_, v_a_1819_, v_x_1820_);
lean_dec(v_x_1820_);
lean_dec_ref(v_a_1819_);
v_r_1822_ = lean_box(v_res_1821_);
return v_r_1822_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__3(lean_object* v_00_u03b2_1823_, lean_object* v_data_1824_){
_start:
{
lean_object* v___x_1825_; 
v___x_1825_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__3___redArg(v_data_1824_);
return v___x_1825_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__4(lean_object* v_00_u03b2_1826_, lean_object* v_a_1827_, lean_object* v_b_1828_, lean_object* v_x_1829_){
_start:
{
lean_object* v___x_1830_; 
v___x_1830_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__4___redArg(v_a_1827_, v_b_1828_, v_x_1829_);
return v___x_1830_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__3_spec__6(lean_object* v_00_u03b2_1831_, lean_object* v_i_1832_, lean_object* v_source_1833_, lean_object* v_target_1834_){
_start:
{
lean_object* v___x_1835_; 
v___x_1835_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__3_spec__6___redArg(v_i_1832_, v_source_1833_, v_target_1834_);
return v___x_1835_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__3_spec__6_spec__10(lean_object* v_00_u03b2_1836_, lean_object* v_x_1837_, lean_object* v_x_1838_){
_start:
{
lean_object* v___x_1839_; 
v___x_1839_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__3_spec__6_spec__10___redArg(v_x_1837_, v_x_1838_);
return v___x_1839_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectExpr(lean_object* v_e_1840_, lean_object* v_a_1841_, lean_object* v_a_1842_, lean_object* v_a_1843_, lean_object* v_a_1844_, lean_object* v_a_1845_, lean_object* v_a_1846_){
_start:
{
lean_object* v___x_1848_; 
v___x_1848_ = l_Lean_Meta_Closure_preprocess(v_e_1840_, v_a_1841_, v_a_1842_, v_a_1843_, v_a_1844_, v_a_1845_, v_a_1846_);
if (lean_obj_tag(v___x_1848_) == 0)
{
lean_object* v_a_1849_; uint8_t v___x_1893_; 
v_a_1849_ = lean_ctor_get(v___x_1848_, 0);
lean_inc(v_a_1849_);
v___x_1893_ = l_Lean_Expr_hasLevelParam(v_a_1849_);
if (v___x_1893_ == 0)
{
uint8_t v___x_1894_; 
v___x_1894_ = l_Lean_Expr_hasFVar(v_a_1849_);
if (v___x_1894_ == 0)
{
uint8_t v___x_1895_; 
v___x_1895_ = l_Lean_Expr_hasMVar(v_a_1849_);
if (v___x_1895_ == 0)
{
lean_dec(v_a_1849_);
return v___x_1848_;
}
else
{
lean_dec_ref_known(v___x_1848_, 1);
goto v___jp_1850_;
}
}
else
{
lean_dec_ref_known(v___x_1848_, 1);
goto v___jp_1850_;
}
}
else
{
lean_dec_ref_known(v___x_1848_, 1);
goto v___jp_1850_;
}
v___jp_1850_:
{
lean_object* v___x_1851_; lean_object* v_visitedExpr_1852_; lean_object* v___x_1853_; 
v___x_1851_ = lean_st_ref_get(v_a_1842_);
v_visitedExpr_1852_ = lean_ctor_get(v___x_1851_, 1);
lean_inc_ref(v_visitedExpr_1852_);
lean_dec(v___x_1851_);
v___x_1853_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0___redArg(v_visitedExpr_1852_, v_a_1849_);
lean_dec_ref(v_visitedExpr_1852_);
if (lean_obj_tag(v___x_1853_) == 0)
{
lean_object* v___x_1854_; 
lean_inc(v_a_1849_);
v___x_1854_ = l_Lean_Meta_Closure_collectExprAux(v_a_1849_, v_a_1841_, v_a_1842_, v_a_1843_, v_a_1844_, v_a_1845_, v_a_1846_);
if (lean_obj_tag(v___x_1854_) == 0)
{
lean_object* v_a_1855_; lean_object* v___x_1857_; uint8_t v_isShared_1858_; uint8_t v_isSharedCheck_1884_; 
v_a_1855_ = lean_ctor_get(v___x_1854_, 0);
v_isSharedCheck_1884_ = !lean_is_exclusive(v___x_1854_);
if (v_isSharedCheck_1884_ == 0)
{
v___x_1857_ = v___x_1854_;
v_isShared_1858_ = v_isSharedCheck_1884_;
goto v_resetjp_1856_;
}
else
{
lean_inc(v_a_1855_);
lean_dec(v___x_1854_);
v___x_1857_ = lean_box(0);
v_isShared_1858_ = v_isSharedCheck_1884_;
goto v_resetjp_1856_;
}
v_resetjp_1856_:
{
lean_object* v___x_1859_; lean_object* v_visitedLevel_1860_; lean_object* v_visitedExpr_1861_; lean_object* v_levelParams_1862_; lean_object* v_nextLevelIdx_1863_; lean_object* v_levelArgs_1864_; lean_object* v_newLocalDecls_1865_; lean_object* v_newLocalDeclsForMVars_1866_; lean_object* v_newLetDecls_1867_; lean_object* v_nextExprIdx_1868_; lean_object* v_exprMVarArgs_1869_; lean_object* v_exprFVarArgs_1870_; lean_object* v_toProcess_1871_; lean_object* v___x_1873_; uint8_t v_isShared_1874_; uint8_t v_isSharedCheck_1883_; 
v___x_1859_ = lean_st_ref_take(v_a_1842_);
v_visitedLevel_1860_ = lean_ctor_get(v___x_1859_, 0);
v_visitedExpr_1861_ = lean_ctor_get(v___x_1859_, 1);
v_levelParams_1862_ = lean_ctor_get(v___x_1859_, 2);
v_nextLevelIdx_1863_ = lean_ctor_get(v___x_1859_, 3);
v_levelArgs_1864_ = lean_ctor_get(v___x_1859_, 4);
v_newLocalDecls_1865_ = lean_ctor_get(v___x_1859_, 5);
v_newLocalDeclsForMVars_1866_ = lean_ctor_get(v___x_1859_, 6);
v_newLetDecls_1867_ = lean_ctor_get(v___x_1859_, 7);
v_nextExprIdx_1868_ = lean_ctor_get(v___x_1859_, 8);
v_exprMVarArgs_1869_ = lean_ctor_get(v___x_1859_, 9);
v_exprFVarArgs_1870_ = lean_ctor_get(v___x_1859_, 10);
v_toProcess_1871_ = lean_ctor_get(v___x_1859_, 11);
v_isSharedCheck_1883_ = !lean_is_exclusive(v___x_1859_);
if (v_isSharedCheck_1883_ == 0)
{
v___x_1873_ = v___x_1859_;
v_isShared_1874_ = v_isSharedCheck_1883_;
goto v_resetjp_1872_;
}
else
{
lean_inc(v_toProcess_1871_);
lean_inc(v_exprFVarArgs_1870_);
lean_inc(v_exprMVarArgs_1869_);
lean_inc(v_nextExprIdx_1868_);
lean_inc(v_newLetDecls_1867_);
lean_inc(v_newLocalDeclsForMVars_1866_);
lean_inc(v_newLocalDecls_1865_);
lean_inc(v_levelArgs_1864_);
lean_inc(v_nextLevelIdx_1863_);
lean_inc(v_levelParams_1862_);
lean_inc(v_visitedExpr_1861_);
lean_inc(v_visitedLevel_1860_);
lean_dec(v___x_1859_);
v___x_1873_ = lean_box(0);
v_isShared_1874_ = v_isSharedCheck_1883_;
goto v_resetjp_1872_;
}
v_resetjp_1872_:
{
lean_object* v___x_1875_; lean_object* v___x_1877_; 
lean_inc(v_a_1855_);
v___x_1875_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1___redArg(v_visitedExpr_1861_, v_a_1849_, v_a_1855_);
if (v_isShared_1874_ == 0)
{
lean_ctor_set(v___x_1873_, 1, v___x_1875_);
v___x_1877_ = v___x_1873_;
goto v_reusejp_1876_;
}
else
{
lean_object* v_reuseFailAlloc_1882_; 
v_reuseFailAlloc_1882_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_1882_, 0, v_visitedLevel_1860_);
lean_ctor_set(v_reuseFailAlloc_1882_, 1, v___x_1875_);
lean_ctor_set(v_reuseFailAlloc_1882_, 2, v_levelParams_1862_);
lean_ctor_set(v_reuseFailAlloc_1882_, 3, v_nextLevelIdx_1863_);
lean_ctor_set(v_reuseFailAlloc_1882_, 4, v_levelArgs_1864_);
lean_ctor_set(v_reuseFailAlloc_1882_, 5, v_newLocalDecls_1865_);
lean_ctor_set(v_reuseFailAlloc_1882_, 6, v_newLocalDeclsForMVars_1866_);
lean_ctor_set(v_reuseFailAlloc_1882_, 7, v_newLetDecls_1867_);
lean_ctor_set(v_reuseFailAlloc_1882_, 8, v_nextExprIdx_1868_);
lean_ctor_set(v_reuseFailAlloc_1882_, 9, v_exprMVarArgs_1869_);
lean_ctor_set(v_reuseFailAlloc_1882_, 10, v_exprFVarArgs_1870_);
lean_ctor_set(v_reuseFailAlloc_1882_, 11, v_toProcess_1871_);
v___x_1877_ = v_reuseFailAlloc_1882_;
goto v_reusejp_1876_;
}
v_reusejp_1876_:
{
lean_object* v___x_1878_; lean_object* v___x_1880_; 
v___x_1878_ = lean_st_ref_put(v_a_1842_, v___x_1877_);
if (v_isShared_1858_ == 0)
{
v___x_1880_ = v___x_1857_;
goto v_reusejp_1879_;
}
else
{
lean_object* v_reuseFailAlloc_1881_; 
v_reuseFailAlloc_1881_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1881_, 0, v_a_1855_);
v___x_1880_ = v_reuseFailAlloc_1881_;
goto v_reusejp_1879_;
}
v_reusejp_1879_:
{
return v___x_1880_;
}
}
}
}
}
else
{
lean_dec(v_a_1849_);
return v___x_1854_;
}
}
else
{
lean_object* v_val_1885_; lean_object* v___x_1887_; uint8_t v_isShared_1888_; uint8_t v_isSharedCheck_1892_; 
lean_dec(v_a_1849_);
v_val_1885_ = lean_ctor_get(v___x_1853_, 0);
v_isSharedCheck_1892_ = !lean_is_exclusive(v___x_1853_);
if (v_isSharedCheck_1892_ == 0)
{
v___x_1887_ = v___x_1853_;
v_isShared_1888_ = v_isSharedCheck_1892_;
goto v_resetjp_1886_;
}
else
{
lean_inc(v_val_1885_);
lean_dec(v___x_1853_);
v___x_1887_ = lean_box(0);
v_isShared_1888_ = v_isSharedCheck_1892_;
goto v_resetjp_1886_;
}
v_resetjp_1886_:
{
lean_object* v___x_1890_; 
if (v_isShared_1888_ == 0)
{
lean_ctor_set_tag(v___x_1887_, 0);
v___x_1890_ = v___x_1887_;
goto v_reusejp_1889_;
}
else
{
lean_object* v_reuseFailAlloc_1891_; 
v_reuseFailAlloc_1891_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1891_, 0, v_val_1885_);
v___x_1890_ = v_reuseFailAlloc_1891_;
goto v_reusejp_1889_;
}
v_reusejp_1889_:
{
return v___x_1890_;
}
}
}
}
}
else
{
return v___x_1848_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectExpr___boxed(lean_object* v_e_1896_, lean_object* v_a_1897_, lean_object* v_a_1898_, lean_object* v_a_1899_, lean_object* v_a_1900_, lean_object* v_a_1901_, lean_object* v_a_1902_, lean_object* v_a_1903_){
_start:
{
lean_object* v_res_1904_; 
v_res_1904_ = l_Lean_Meta_Closure_collectExpr(v_e_1896_, v_a_1897_, v_a_1898_, v_a_1899_, v_a_1900_, v_a_1901_, v_a_1902_);
lean_dec(v_a_1902_);
lean_dec_ref(v_a_1901_);
lean_dec(v_a_1900_);
lean_dec_ref(v_a_1899_);
lean_dec(v_a_1898_);
lean_dec_ref(v_a_1897_);
return v_res_1904_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pickNextToProcessAux(lean_object* v_lctx_1905_, lean_object* v_i_1906_, lean_object* v_toProcess_1907_, lean_object* v_elem_1908_){
_start:
{
lean_object* v___x_1909_; uint8_t v___x_1910_; 
v___x_1909_ = lean_array_get_size(v_toProcess_1907_);
v___x_1910_ = lean_nat_dec_lt(v_i_1906_, v___x_1909_);
if (v___x_1910_ == 0)
{
lean_object* v___x_1911_; 
lean_dec(v_i_1906_);
lean_dec_ref(v_lctx_1905_);
v___x_1911_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1911_, 0, v_elem_1908_);
lean_ctor_set(v___x_1911_, 1, v_toProcess_1907_);
return v___x_1911_;
}
else
{
lean_object* v_fvarId_1912_; lean_object* v_elem_x27_1913_; lean_object* v_fvarId_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; uint8_t v___x_1919_; 
v_fvarId_1912_ = lean_ctor_get(v_elem_1908_, 0);
v_elem_x27_1913_ = lean_array_fget_borrowed(v_toProcess_1907_, v_i_1906_);
v_fvarId_1914_ = lean_ctor_get(v_elem_x27_1913_, 0);
lean_inc(v_fvarId_1912_);
lean_inc_ref_n(v_lctx_1905_, 2);
v___x_1915_ = l_Lean_LocalContext_get_x21(v_lctx_1905_, v_fvarId_1912_);
v___x_1916_ = l_Lean_LocalDecl_index(v___x_1915_);
lean_dec_ref(v___x_1915_);
lean_inc(v_fvarId_1914_);
v___x_1917_ = l_Lean_LocalContext_get_x21(v_lctx_1905_, v_fvarId_1914_);
v___x_1918_ = l_Lean_LocalDecl_index(v___x_1917_);
lean_dec_ref(v___x_1917_);
v___x_1919_ = lean_nat_dec_lt(v___x_1916_, v___x_1918_);
lean_dec(v___x_1918_);
lean_dec(v___x_1916_);
if (v___x_1919_ == 0)
{
lean_object* v___x_1920_; lean_object* v___x_1921_; 
v___x_1920_ = lean_unsigned_to_nat(1u);
v___x_1921_ = lean_nat_add(v_i_1906_, v___x_1920_);
lean_dec(v_i_1906_);
v_i_1906_ = v___x_1921_;
goto _start;
}
else
{
lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; 
lean_inc(v_elem_x27_1913_);
v___x_1923_ = lean_unsigned_to_nat(1u);
v___x_1924_ = lean_nat_add(v_i_1906_, v___x_1923_);
v___x_1925_ = lean_array_fset(v_toProcess_1907_, v_i_1906_, v_elem_1908_);
lean_dec(v_i_1906_);
v_i_1906_ = v___x_1924_;
v_toProcess_1907_ = v___x_1925_;
v_elem_1908_ = v_elem_x27_1913_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pickNextToProcess_x3f___redArg(lean_object* v_a_1927_, lean_object* v_a_1928_){
_start:
{
lean_object* v_lctx_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; lean_object* v_toProcess_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; uint8_t v___x_1936_; 
v_lctx_1930_ = lean_ctor_get(v_a_1928_, 2);
v___x_1931_ = ((lean_object*)(l_Lean_Meta_Closure_instInhabitedToProcessElement_default));
v___x_1932_ = lean_st_ref_get(v_a_1927_);
v_toProcess_1933_ = lean_ctor_get(v___x_1932_, 11);
lean_inc_ref(v_toProcess_1933_);
lean_dec(v___x_1932_);
v___x_1934_ = lean_array_get_size(v_toProcess_1933_);
lean_dec_ref(v_toProcess_1933_);
v___x_1935_ = lean_unsigned_to_nat(0u);
v___x_1936_ = lean_nat_dec_eq(v___x_1934_, v___x_1935_);
if (v___x_1936_ == 0)
{
lean_object* v___x_1937_; lean_object* v_visitedLevel_1938_; lean_object* v_visitedExpr_1939_; lean_object* v_levelParams_1940_; lean_object* v_nextLevelIdx_1941_; lean_object* v_levelArgs_1942_; lean_object* v_newLocalDecls_1943_; lean_object* v_newLocalDeclsForMVars_1944_; lean_object* v_newLetDecls_1945_; lean_object* v_nextExprIdx_1946_; lean_object* v_exprMVarArgs_1947_; lean_object* v_exprFVarArgs_1948_; lean_object* v_toProcess_1949_; lean_object* v___x_1951_; uint8_t v_isShared_1952_; uint8_t v_isSharedCheck_1967_; 
v___x_1937_ = lean_st_ref_take(v_a_1927_);
v_visitedLevel_1938_ = lean_ctor_get(v___x_1937_, 0);
v_visitedExpr_1939_ = lean_ctor_get(v___x_1937_, 1);
v_levelParams_1940_ = lean_ctor_get(v___x_1937_, 2);
v_nextLevelIdx_1941_ = lean_ctor_get(v___x_1937_, 3);
v_levelArgs_1942_ = lean_ctor_get(v___x_1937_, 4);
v_newLocalDecls_1943_ = lean_ctor_get(v___x_1937_, 5);
v_newLocalDeclsForMVars_1944_ = lean_ctor_get(v___x_1937_, 6);
v_newLetDecls_1945_ = lean_ctor_get(v___x_1937_, 7);
v_nextExprIdx_1946_ = lean_ctor_get(v___x_1937_, 8);
v_exprMVarArgs_1947_ = lean_ctor_get(v___x_1937_, 9);
v_exprFVarArgs_1948_ = lean_ctor_get(v___x_1937_, 10);
v_toProcess_1949_ = lean_ctor_get(v___x_1937_, 11);
v_isSharedCheck_1967_ = !lean_is_exclusive(v___x_1937_);
if (v_isSharedCheck_1967_ == 0)
{
v___x_1951_ = v___x_1937_;
v_isShared_1952_ = v_isSharedCheck_1967_;
goto v_resetjp_1950_;
}
else
{
lean_inc(v_toProcess_1949_);
lean_inc(v_exprFVarArgs_1948_);
lean_inc(v_exprMVarArgs_1947_);
lean_inc(v_nextExprIdx_1946_);
lean_inc(v_newLetDecls_1945_);
lean_inc(v_newLocalDeclsForMVars_1944_);
lean_inc(v_newLocalDecls_1943_);
lean_inc(v_levelArgs_1942_);
lean_inc(v_nextLevelIdx_1941_);
lean_inc(v_levelParams_1940_);
lean_inc(v_visitedExpr_1939_);
lean_inc(v_visitedLevel_1938_);
lean_dec(v___x_1937_);
v___x_1951_ = lean_box(0);
v_isShared_1952_ = v_isSharedCheck_1967_;
goto v_resetjp_1950_;
}
v_resetjp_1950_:
{
lean_object* v___x_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; lean_object* v_fst_1959_; lean_object* v_snd_1960_; lean_object* v___x_1961_; lean_object* v___x_1963_; 
v___x_1953_ = lean_array_get_size(v_toProcess_1949_);
v___x_1954_ = lean_unsigned_to_nat(1u);
v___x_1955_ = lean_nat_sub(v___x_1953_, v___x_1954_);
v___x_1956_ = lean_array_get(v___x_1931_, v_toProcess_1949_, v___x_1955_);
lean_dec(v___x_1955_);
v___x_1957_ = lean_array_pop(v_toProcess_1949_);
lean_inc_ref(v_lctx_1930_);
v___x_1958_ = l_Lean_Meta_Closure_pickNextToProcessAux(v_lctx_1930_, v___x_1935_, v___x_1957_, v___x_1956_);
v_fst_1959_ = lean_ctor_get(v___x_1958_, 0);
lean_inc(v_fst_1959_);
v_snd_1960_ = lean_ctor_get(v___x_1958_, 1);
lean_inc(v_snd_1960_);
lean_dec_ref(v___x_1958_);
v___x_1961_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1961_, 0, v_fst_1959_);
if (v_isShared_1952_ == 0)
{
lean_ctor_set(v___x_1951_, 11, v_snd_1960_);
v___x_1963_ = v___x_1951_;
goto v_reusejp_1962_;
}
else
{
lean_object* v_reuseFailAlloc_1966_; 
v_reuseFailAlloc_1966_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_1966_, 0, v_visitedLevel_1938_);
lean_ctor_set(v_reuseFailAlloc_1966_, 1, v_visitedExpr_1939_);
lean_ctor_set(v_reuseFailAlloc_1966_, 2, v_levelParams_1940_);
lean_ctor_set(v_reuseFailAlloc_1966_, 3, v_nextLevelIdx_1941_);
lean_ctor_set(v_reuseFailAlloc_1966_, 4, v_levelArgs_1942_);
lean_ctor_set(v_reuseFailAlloc_1966_, 5, v_newLocalDecls_1943_);
lean_ctor_set(v_reuseFailAlloc_1966_, 6, v_newLocalDeclsForMVars_1944_);
lean_ctor_set(v_reuseFailAlloc_1966_, 7, v_newLetDecls_1945_);
lean_ctor_set(v_reuseFailAlloc_1966_, 8, v_nextExprIdx_1946_);
lean_ctor_set(v_reuseFailAlloc_1966_, 9, v_exprMVarArgs_1947_);
lean_ctor_set(v_reuseFailAlloc_1966_, 10, v_exprFVarArgs_1948_);
lean_ctor_set(v_reuseFailAlloc_1966_, 11, v_snd_1960_);
v___x_1963_ = v_reuseFailAlloc_1966_;
goto v_reusejp_1962_;
}
v_reusejp_1962_:
{
lean_object* v___x_1964_; lean_object* v___x_1965_; 
v___x_1964_ = lean_st_ref_put(v_a_1927_, v___x_1963_);
v___x_1965_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1965_, 0, v___x_1961_);
return v___x_1965_;
}
}
}
else
{
lean_object* v___x_1968_; lean_object* v___x_1969_; 
v___x_1968_ = lean_box(0);
v___x_1969_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1969_, 0, v___x_1968_);
return v___x_1969_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pickNextToProcess_x3f___redArg___boxed(lean_object* v_a_1970_, lean_object* v_a_1971_, lean_object* v_a_1972_){
_start:
{
lean_object* v_res_1973_; 
v_res_1973_ = l_Lean_Meta_Closure_pickNextToProcess_x3f___redArg(v_a_1970_, v_a_1971_);
lean_dec_ref(v_a_1971_);
lean_dec(v_a_1970_);
return v_res_1973_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pickNextToProcess_x3f(lean_object* v_a_1974_, lean_object* v_a_1975_, lean_object* v_a_1976_, lean_object* v_a_1977_, lean_object* v_a_1978_, lean_object* v_a_1979_){
_start:
{
lean_object* v___x_1981_; 
v___x_1981_ = l_Lean_Meta_Closure_pickNextToProcess_x3f___redArg(v_a_1975_, v_a_1976_);
return v___x_1981_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pickNextToProcess_x3f___boxed(lean_object* v_a_1982_, lean_object* v_a_1983_, lean_object* v_a_1984_, lean_object* v_a_1985_, lean_object* v_a_1986_, lean_object* v_a_1987_, lean_object* v_a_1988_){
_start:
{
lean_object* v_res_1989_; 
v_res_1989_ = l_Lean_Meta_Closure_pickNextToProcess_x3f(v_a_1982_, v_a_1983_, v_a_1984_, v_a_1985_, v_a_1986_, v_a_1987_);
lean_dec(v_a_1987_);
lean_dec_ref(v_a_1986_);
lean_dec(v_a_1985_);
lean_dec_ref(v_a_1984_);
lean_dec(v_a_1983_);
lean_dec_ref(v_a_1982_);
return v_res_1989_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushFVarArg___redArg(lean_object* v_e_1990_, lean_object* v_a_1991_){
_start:
{
lean_object* v___x_1993_; lean_object* v_visitedLevel_1994_; lean_object* v_visitedExpr_1995_; lean_object* v_levelParams_1996_; lean_object* v_nextLevelIdx_1997_; lean_object* v_levelArgs_1998_; lean_object* v_newLocalDecls_1999_; lean_object* v_newLocalDeclsForMVars_2000_; lean_object* v_newLetDecls_2001_; lean_object* v_nextExprIdx_2002_; lean_object* v_exprMVarArgs_2003_; lean_object* v_exprFVarArgs_2004_; lean_object* v_toProcess_2005_; lean_object* v___x_2007_; uint8_t v_isShared_2008_; uint8_t v_isSharedCheck_2016_; 
v___x_1993_ = lean_st_ref_take(v_a_1991_);
v_visitedLevel_1994_ = lean_ctor_get(v___x_1993_, 0);
v_visitedExpr_1995_ = lean_ctor_get(v___x_1993_, 1);
v_levelParams_1996_ = lean_ctor_get(v___x_1993_, 2);
v_nextLevelIdx_1997_ = lean_ctor_get(v___x_1993_, 3);
v_levelArgs_1998_ = lean_ctor_get(v___x_1993_, 4);
v_newLocalDecls_1999_ = lean_ctor_get(v___x_1993_, 5);
v_newLocalDeclsForMVars_2000_ = lean_ctor_get(v___x_1993_, 6);
v_newLetDecls_2001_ = lean_ctor_get(v___x_1993_, 7);
v_nextExprIdx_2002_ = lean_ctor_get(v___x_1993_, 8);
v_exprMVarArgs_2003_ = lean_ctor_get(v___x_1993_, 9);
v_exprFVarArgs_2004_ = lean_ctor_get(v___x_1993_, 10);
v_toProcess_2005_ = lean_ctor_get(v___x_1993_, 11);
v_isSharedCheck_2016_ = !lean_is_exclusive(v___x_1993_);
if (v_isSharedCheck_2016_ == 0)
{
v___x_2007_ = v___x_1993_;
v_isShared_2008_ = v_isSharedCheck_2016_;
goto v_resetjp_2006_;
}
else
{
lean_inc(v_toProcess_2005_);
lean_inc(v_exprFVarArgs_2004_);
lean_inc(v_exprMVarArgs_2003_);
lean_inc(v_nextExprIdx_2002_);
lean_inc(v_newLetDecls_2001_);
lean_inc(v_newLocalDeclsForMVars_2000_);
lean_inc(v_newLocalDecls_1999_);
lean_inc(v_levelArgs_1998_);
lean_inc(v_nextLevelIdx_1997_);
lean_inc(v_levelParams_1996_);
lean_inc(v_visitedExpr_1995_);
lean_inc(v_visitedLevel_1994_);
lean_dec(v___x_1993_);
v___x_2007_ = lean_box(0);
v_isShared_2008_ = v_isSharedCheck_2016_;
goto v_resetjp_2006_;
}
v_resetjp_2006_:
{
lean_object* v___x_2009_; lean_object* v___x_2010_; lean_object* v___x_2012_; 
v___x_2009_ = lean_box(0);
v___x_2010_ = lean_array_push(v_exprFVarArgs_2004_, v_e_1990_);
if (v_isShared_2008_ == 0)
{
lean_ctor_set(v___x_2007_, 10, v___x_2010_);
v___x_2012_ = v___x_2007_;
goto v_reusejp_2011_;
}
else
{
lean_object* v_reuseFailAlloc_2015_; 
v_reuseFailAlloc_2015_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_2015_, 0, v_visitedLevel_1994_);
lean_ctor_set(v_reuseFailAlloc_2015_, 1, v_visitedExpr_1995_);
lean_ctor_set(v_reuseFailAlloc_2015_, 2, v_levelParams_1996_);
lean_ctor_set(v_reuseFailAlloc_2015_, 3, v_nextLevelIdx_1997_);
lean_ctor_set(v_reuseFailAlloc_2015_, 4, v_levelArgs_1998_);
lean_ctor_set(v_reuseFailAlloc_2015_, 5, v_newLocalDecls_1999_);
lean_ctor_set(v_reuseFailAlloc_2015_, 6, v_newLocalDeclsForMVars_2000_);
lean_ctor_set(v_reuseFailAlloc_2015_, 7, v_newLetDecls_2001_);
lean_ctor_set(v_reuseFailAlloc_2015_, 8, v_nextExprIdx_2002_);
lean_ctor_set(v_reuseFailAlloc_2015_, 9, v_exprMVarArgs_2003_);
lean_ctor_set(v_reuseFailAlloc_2015_, 10, v___x_2010_);
lean_ctor_set(v_reuseFailAlloc_2015_, 11, v_toProcess_2005_);
v___x_2012_ = v_reuseFailAlloc_2015_;
goto v_reusejp_2011_;
}
v_reusejp_2011_:
{
lean_object* v___x_2013_; lean_object* v___x_2014_; 
v___x_2013_ = lean_st_ref_put(v_a_1991_, v___x_2012_);
v___x_2014_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2014_, 0, v___x_2009_);
return v___x_2014_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushFVarArg___redArg___boxed(lean_object* v_e_2017_, lean_object* v_a_2018_, lean_object* v_a_2019_){
_start:
{
lean_object* v_res_2020_; 
v_res_2020_ = l_Lean_Meta_Closure_pushFVarArg___redArg(v_e_2017_, v_a_2018_);
lean_dec(v_a_2018_);
return v_res_2020_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushFVarArg(lean_object* v_e_2021_, lean_object* v_a_2022_, lean_object* v_a_2023_, lean_object* v_a_2024_, lean_object* v_a_2025_, lean_object* v_a_2026_, lean_object* v_a_2027_){
_start:
{
lean_object* v___x_2029_; 
v___x_2029_ = l_Lean_Meta_Closure_pushFVarArg___redArg(v_e_2021_, v_a_2023_);
return v___x_2029_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushFVarArg___boxed(lean_object* v_e_2030_, lean_object* v_a_2031_, lean_object* v_a_2032_, lean_object* v_a_2033_, lean_object* v_a_2034_, lean_object* v_a_2035_, lean_object* v_a_2036_, lean_object* v_a_2037_){
_start:
{
lean_object* v_res_2038_; 
v_res_2038_ = l_Lean_Meta_Closure_pushFVarArg(v_e_2030_, v_a_2031_, v_a_2032_, v_a_2033_, v_a_2034_, v_a_2035_, v_a_2036_);
lean_dec(v_a_2036_);
lean_dec_ref(v_a_2035_);
lean_dec(v_a_2034_);
lean_dec_ref(v_a_2033_);
lean_dec(v_a_2032_);
lean_dec_ref(v_a_2031_);
return v_res_2038_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushLocalDecl(lean_object* v_newFVarId_2039_, lean_object* v_userName_2040_, lean_object* v_type_2041_, uint8_t v_bi_2042_, lean_object* v_a_2043_, lean_object* v_a_2044_, lean_object* v_a_2045_, lean_object* v_a_2046_, lean_object* v_a_2047_, lean_object* v_a_2048_){
_start:
{
lean_object* v___x_2050_; 
v___x_2050_ = l_Lean_Meta_Closure_collectExpr(v_type_2041_, v_a_2043_, v_a_2044_, v_a_2045_, v_a_2046_, v_a_2047_, v_a_2048_);
if (lean_obj_tag(v___x_2050_) == 0)
{
lean_object* v_a_2051_; lean_object* v___x_2053_; uint8_t v_isShared_2054_; uint8_t v_isSharedCheck_2084_; 
v_a_2051_ = lean_ctor_get(v___x_2050_, 0);
v_isSharedCheck_2084_ = !lean_is_exclusive(v___x_2050_);
if (v_isSharedCheck_2084_ == 0)
{
v___x_2053_ = v___x_2050_;
v_isShared_2054_ = v_isSharedCheck_2084_;
goto v_resetjp_2052_;
}
else
{
lean_inc(v_a_2051_);
lean_dec(v___x_2050_);
v___x_2053_ = lean_box(0);
v_isShared_2054_ = v_isSharedCheck_2084_;
goto v_resetjp_2052_;
}
v_resetjp_2052_:
{
lean_object* v___x_2055_; lean_object* v_visitedLevel_2056_; lean_object* v_visitedExpr_2057_; lean_object* v_levelParams_2058_; lean_object* v_nextLevelIdx_2059_; lean_object* v_levelArgs_2060_; lean_object* v_newLocalDecls_2061_; lean_object* v_newLocalDeclsForMVars_2062_; lean_object* v_newLetDecls_2063_; lean_object* v_nextExprIdx_2064_; lean_object* v_exprMVarArgs_2065_; lean_object* v_exprFVarArgs_2066_; lean_object* v_toProcess_2067_; lean_object* v___x_2069_; uint8_t v_isShared_2070_; uint8_t v_isSharedCheck_2083_; 
v___x_2055_ = lean_st_ref_take(v_a_2044_);
v_visitedLevel_2056_ = lean_ctor_get(v___x_2055_, 0);
v_visitedExpr_2057_ = lean_ctor_get(v___x_2055_, 1);
v_levelParams_2058_ = lean_ctor_get(v___x_2055_, 2);
v_nextLevelIdx_2059_ = lean_ctor_get(v___x_2055_, 3);
v_levelArgs_2060_ = lean_ctor_get(v___x_2055_, 4);
v_newLocalDecls_2061_ = lean_ctor_get(v___x_2055_, 5);
v_newLocalDeclsForMVars_2062_ = lean_ctor_get(v___x_2055_, 6);
v_newLetDecls_2063_ = lean_ctor_get(v___x_2055_, 7);
v_nextExprIdx_2064_ = lean_ctor_get(v___x_2055_, 8);
v_exprMVarArgs_2065_ = lean_ctor_get(v___x_2055_, 9);
v_exprFVarArgs_2066_ = lean_ctor_get(v___x_2055_, 10);
v_toProcess_2067_ = lean_ctor_get(v___x_2055_, 11);
v_isSharedCheck_2083_ = !lean_is_exclusive(v___x_2055_);
if (v_isSharedCheck_2083_ == 0)
{
v___x_2069_ = v___x_2055_;
v_isShared_2070_ = v_isSharedCheck_2083_;
goto v_resetjp_2068_;
}
else
{
lean_inc(v_toProcess_2067_);
lean_inc(v_exprFVarArgs_2066_);
lean_inc(v_exprMVarArgs_2065_);
lean_inc(v_nextExprIdx_2064_);
lean_inc(v_newLetDecls_2063_);
lean_inc(v_newLocalDeclsForMVars_2062_);
lean_inc(v_newLocalDecls_2061_);
lean_inc(v_levelArgs_2060_);
lean_inc(v_nextLevelIdx_2059_);
lean_inc(v_levelParams_2058_);
lean_inc(v_visitedExpr_2057_);
lean_inc(v_visitedLevel_2056_);
lean_dec(v___x_2055_);
v___x_2069_ = lean_box(0);
v_isShared_2070_ = v_isSharedCheck_2083_;
goto v_resetjp_2068_;
}
v_resetjp_2068_:
{
lean_object* v___x_2071_; lean_object* v___x_2072_; uint8_t v___x_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2077_; 
v___x_2071_ = lean_box(0);
v___x_2072_ = lean_unsigned_to_nat(0u);
v___x_2073_ = 0;
v___x_2074_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2074_, 0, v___x_2072_);
lean_ctor_set(v___x_2074_, 1, v_newFVarId_2039_);
lean_ctor_set(v___x_2074_, 2, v_userName_2040_);
lean_ctor_set(v___x_2074_, 3, v_a_2051_);
lean_ctor_set_uint8(v___x_2074_, sizeof(void*)*4, v_bi_2042_);
lean_ctor_set_uint8(v___x_2074_, sizeof(void*)*4 + 1, v___x_2073_);
v___x_2075_ = lean_array_push(v_newLocalDecls_2061_, v___x_2074_);
if (v_isShared_2070_ == 0)
{
lean_ctor_set(v___x_2069_, 5, v___x_2075_);
v___x_2077_ = v___x_2069_;
goto v_reusejp_2076_;
}
else
{
lean_object* v_reuseFailAlloc_2082_; 
v_reuseFailAlloc_2082_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_2082_, 0, v_visitedLevel_2056_);
lean_ctor_set(v_reuseFailAlloc_2082_, 1, v_visitedExpr_2057_);
lean_ctor_set(v_reuseFailAlloc_2082_, 2, v_levelParams_2058_);
lean_ctor_set(v_reuseFailAlloc_2082_, 3, v_nextLevelIdx_2059_);
lean_ctor_set(v_reuseFailAlloc_2082_, 4, v_levelArgs_2060_);
lean_ctor_set(v_reuseFailAlloc_2082_, 5, v___x_2075_);
lean_ctor_set(v_reuseFailAlloc_2082_, 6, v_newLocalDeclsForMVars_2062_);
lean_ctor_set(v_reuseFailAlloc_2082_, 7, v_newLetDecls_2063_);
lean_ctor_set(v_reuseFailAlloc_2082_, 8, v_nextExprIdx_2064_);
lean_ctor_set(v_reuseFailAlloc_2082_, 9, v_exprMVarArgs_2065_);
lean_ctor_set(v_reuseFailAlloc_2082_, 10, v_exprFVarArgs_2066_);
lean_ctor_set(v_reuseFailAlloc_2082_, 11, v_toProcess_2067_);
v___x_2077_ = v_reuseFailAlloc_2082_;
goto v_reusejp_2076_;
}
v_reusejp_2076_:
{
lean_object* v___x_2078_; lean_object* v___x_2080_; 
v___x_2078_ = lean_st_ref_put(v_a_2044_, v___x_2077_);
if (v_isShared_2054_ == 0)
{
lean_ctor_set(v___x_2053_, 0, v___x_2071_);
v___x_2080_ = v___x_2053_;
goto v_reusejp_2079_;
}
else
{
lean_object* v_reuseFailAlloc_2081_; 
v_reuseFailAlloc_2081_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2081_, 0, v___x_2071_);
v___x_2080_ = v_reuseFailAlloc_2081_;
goto v_reusejp_2079_;
}
v_reusejp_2079_:
{
return v___x_2080_;
}
}
}
}
}
else
{
lean_object* v_a_2085_; lean_object* v___x_2087_; uint8_t v_isShared_2088_; uint8_t v_isSharedCheck_2092_; 
lean_dec(v_userName_2040_);
lean_dec(v_newFVarId_2039_);
v_a_2085_ = lean_ctor_get(v___x_2050_, 0);
v_isSharedCheck_2092_ = !lean_is_exclusive(v___x_2050_);
if (v_isSharedCheck_2092_ == 0)
{
v___x_2087_ = v___x_2050_;
v_isShared_2088_ = v_isSharedCheck_2092_;
goto v_resetjp_2086_;
}
else
{
lean_inc(v_a_2085_);
lean_dec(v___x_2050_);
v___x_2087_ = lean_box(0);
v_isShared_2088_ = v_isSharedCheck_2092_;
goto v_resetjp_2086_;
}
v_resetjp_2086_:
{
lean_object* v___x_2090_; 
if (v_isShared_2088_ == 0)
{
v___x_2090_ = v___x_2087_;
goto v_reusejp_2089_;
}
else
{
lean_object* v_reuseFailAlloc_2091_; 
v_reuseFailAlloc_2091_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2091_, 0, v_a_2085_);
v___x_2090_ = v_reuseFailAlloc_2091_;
goto v_reusejp_2089_;
}
v_reusejp_2089_:
{
return v___x_2090_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushLocalDecl___boxed(lean_object* v_newFVarId_2093_, lean_object* v_userName_2094_, lean_object* v_type_2095_, lean_object* v_bi_2096_, lean_object* v_a_2097_, lean_object* v_a_2098_, lean_object* v_a_2099_, lean_object* v_a_2100_, lean_object* v_a_2101_, lean_object* v_a_2102_, lean_object* v_a_2103_){
_start:
{
uint8_t v_bi_boxed_2104_; lean_object* v_res_2105_; 
v_bi_boxed_2104_ = lean_unbox(v_bi_2096_);
v_res_2105_ = l_Lean_Meta_Closure_pushLocalDecl(v_newFVarId_2093_, v_userName_2094_, v_type_2095_, v_bi_boxed_2104_, v_a_2097_, v_a_2098_, v_a_2099_, v_a_2100_, v_a_2101_, v_a_2102_);
lean_dec(v_a_2102_);
lean_dec_ref(v_a_2101_);
lean_dec(v_a_2100_);
lean_dec_ref(v_a_2099_);
lean_dec(v_a_2098_);
lean_dec_ref(v_a_2097_);
return v_res_2105_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Closure_process_spec__0___redArg(lean_object* v_k_2106_, lean_object* v_t_2107_){
_start:
{
if (lean_obj_tag(v_t_2107_) == 0)
{
lean_object* v_k_2108_; lean_object* v_l_2109_; lean_object* v_r_2110_; uint8_t v___x_2111_; 
v_k_2108_ = lean_ctor_get(v_t_2107_, 1);
v_l_2109_ = lean_ctor_get(v_t_2107_, 3);
v_r_2110_ = lean_ctor_get(v_t_2107_, 4);
v___x_2111_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_2106_, v_k_2108_);
switch(v___x_2111_)
{
case 0:
{
v_t_2107_ = v_l_2109_;
goto _start;
}
case 1:
{
uint8_t v___x_2113_; 
v___x_2113_ = 1;
return v___x_2113_;
}
default: 
{
v_t_2107_ = v_r_2110_;
goto _start;
}
}
}
else
{
uint8_t v___x_2115_; 
v___x_2115_ = 0;
return v___x_2115_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Closure_process_spec__0___redArg___boxed(lean_object* v_k_2116_, lean_object* v_t_2117_){
_start:
{
uint8_t v_res_2118_; lean_object* v_r_2119_; 
v_res_2118_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Closure_process_spec__0___redArg(v_k_2116_, v_t_2117_);
lean_dec(v_t_2117_);
lean_dec(v_k_2116_);
v_r_2119_ = lean_box(v_res_2118_);
return v_r_2119_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Closure_process_spec__1(lean_object* v_newFVarId_2120_, lean_object* v_a_2121_, size_t v_sz_2122_, size_t v_i_2123_, lean_object* v_bs_2124_){
_start:
{
uint8_t v___x_2125_; 
v___x_2125_ = lean_usize_dec_lt(v_i_2123_, v_sz_2122_);
if (v___x_2125_ == 0)
{
lean_dec(v_newFVarId_2120_);
return v_bs_2124_;
}
else
{
lean_object* v_v_2126_; lean_object* v___x_2127_; lean_object* v_bs_x27_2128_; lean_object* v___x_2129_; size_t v___x_2130_; size_t v___x_2131_; lean_object* v___x_2132_; 
v_v_2126_ = lean_array_uget(v_bs_2124_, v_i_2123_);
v___x_2127_ = lean_unsigned_to_nat(0u);
v_bs_x27_2128_ = lean_array_uset(v_bs_2124_, v_i_2123_, v___x_2127_);
lean_inc(v_newFVarId_2120_);
v___x_2129_ = l_Lean_LocalDecl_replaceFVarId(v_newFVarId_2120_, v_a_2121_, v_v_2126_);
v___x_2130_ = ((size_t)1ULL);
v___x_2131_ = lean_usize_add(v_i_2123_, v___x_2130_);
v___x_2132_ = lean_array_uset(v_bs_x27_2128_, v_i_2123_, v___x_2129_);
v_i_2123_ = v___x_2131_;
v_bs_2124_ = v___x_2132_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Closure_process_spec__1___boxed(lean_object* v_newFVarId_2134_, lean_object* v_a_2135_, lean_object* v_sz_2136_, lean_object* v_i_2137_, lean_object* v_bs_2138_){
_start:
{
size_t v_sz_boxed_2139_; size_t v_i_boxed_2140_; lean_object* v_res_2141_; 
v_sz_boxed_2139_ = lean_unbox_usize(v_sz_2136_);
lean_dec(v_sz_2136_);
v_i_boxed_2140_ = lean_unbox_usize(v_i_2137_);
lean_dec(v_i_2137_);
v_res_2141_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Closure_process_spec__1(v_newFVarId_2134_, v_a_2135_, v_sz_boxed_2139_, v_i_boxed_2140_, v_bs_2138_);
lean_dec_ref(v_a_2135_);
return v_res_2141_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_process(lean_object* v_a_2142_, lean_object* v_a_2143_, lean_object* v_a_2144_, lean_object* v_a_2145_, lean_object* v_a_2146_, lean_object* v_a_2147_){
_start:
{
lean_object* v___x_2149_; 
v___x_2149_ = l_Lean_Meta_Closure_pickNextToProcess_x3f___redArg(v_a_2143_, v_a_2144_);
if (lean_obj_tag(v___x_2149_) == 0)
{
lean_object* v_a_2150_; lean_object* v___x_2152_; uint8_t v_isShared_2153_; uint8_t v_isSharedCheck_2277_; 
v_a_2150_ = lean_ctor_get(v___x_2149_, 0);
v_isSharedCheck_2277_ = !lean_is_exclusive(v___x_2149_);
if (v_isSharedCheck_2277_ == 0)
{
v___x_2152_ = v___x_2149_;
v_isShared_2153_ = v_isSharedCheck_2277_;
goto v_resetjp_2151_;
}
else
{
lean_inc(v_a_2150_);
lean_dec(v___x_2149_);
v___x_2152_ = lean_box(0);
v_isShared_2153_ = v_isSharedCheck_2277_;
goto v_resetjp_2151_;
}
v_resetjp_2151_:
{
if (lean_obj_tag(v_a_2150_) == 0)
{
lean_object* v___x_2154_; lean_object* v___x_2156_; 
v___x_2154_ = lean_box(0);
if (v_isShared_2153_ == 0)
{
lean_ctor_set(v___x_2152_, 0, v___x_2154_);
v___x_2156_ = v___x_2152_;
goto v_reusejp_2155_;
}
else
{
lean_object* v_reuseFailAlloc_2157_; 
v_reuseFailAlloc_2157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2157_, 0, v___x_2154_);
v___x_2156_ = v_reuseFailAlloc_2157_;
goto v_reusejp_2155_;
}
v_reusejp_2155_:
{
return v___x_2156_;
}
}
else
{
lean_object* v_val_2158_; lean_object* v_fvarId_2159_; lean_object* v_newFVarId_2160_; lean_object* v___x_2161_; 
lean_del_object(v___x_2152_);
v_val_2158_ = lean_ctor_get(v_a_2150_, 0);
lean_inc(v_val_2158_);
lean_dec_ref_known(v_a_2150_, 1);
v_fvarId_2159_ = lean_ctor_get(v_val_2158_, 0);
lean_inc_n(v_fvarId_2159_, 2);
v_newFVarId_2160_ = lean_ctor_get(v_val_2158_, 1);
lean_inc(v_newFVarId_2160_);
lean_dec(v_val_2158_);
v___x_2161_ = l_Lean_FVarId_getDecl___redArg(v_fvarId_2159_, v_a_2144_, v_a_2146_, v_a_2147_);
if (lean_obj_tag(v___x_2161_) == 0)
{
lean_object* v_a_2162_; 
v_a_2162_ = lean_ctor_get(v___x_2161_, 0);
lean_inc(v_a_2162_);
lean_dec_ref_known(v___x_2161_, 1);
if (lean_obj_tag(v_a_2162_) == 0)
{
lean_object* v_userName_2163_; lean_object* v_type_2164_; uint8_t v_bi_2165_; lean_object* v___x_2166_; 
v_userName_2163_ = lean_ctor_get(v_a_2162_, 2);
lean_inc(v_userName_2163_);
v_type_2164_ = lean_ctor_get(v_a_2162_, 3);
lean_inc_ref(v_type_2164_);
v_bi_2165_ = lean_ctor_get_uint8(v_a_2162_, sizeof(void*)*4);
lean_dec_ref_known(v_a_2162_, 4);
v___x_2166_ = l_Lean_Meta_Closure_pushLocalDecl(v_newFVarId_2160_, v_userName_2163_, v_type_2164_, v_bi_2165_, v_a_2142_, v_a_2143_, v_a_2144_, v_a_2145_, v_a_2146_, v_a_2147_);
if (lean_obj_tag(v___x_2166_) == 0)
{
lean_object* v___x_2167_; lean_object* v___x_2168_; 
lean_dec_ref_known(v___x_2166_, 1);
v___x_2167_ = l_Lean_mkFVar(v_fvarId_2159_);
v___x_2168_ = l_Lean_Meta_Closure_pushFVarArg___redArg(v___x_2167_, v_a_2143_);
if (lean_obj_tag(v___x_2168_) == 0)
{
lean_dec_ref_known(v___x_2168_, 1);
goto _start;
}
else
{
return v___x_2168_;
}
}
else
{
lean_dec(v_fvarId_2159_);
return v___x_2166_;
}
}
else
{
lean_object* v_userName_2170_; lean_object* v_type_2171_; lean_object* v_value_2172_; uint8_t v_nondep_2173_; lean_object* v___x_2175_; uint8_t v_isShared_2176_; uint8_t v_isSharedCheck_2266_; 
v_userName_2170_ = lean_ctor_get(v_a_2162_, 2);
v_type_2171_ = lean_ctor_get(v_a_2162_, 3);
v_value_2172_ = lean_ctor_get(v_a_2162_, 4);
v_nondep_2173_ = lean_ctor_get_uint8(v_a_2162_, sizeof(void*)*5);
v_isSharedCheck_2266_ = !lean_is_exclusive(v_a_2162_);
if (v_isSharedCheck_2266_ == 0)
{
lean_object* v_unused_2267_; lean_object* v_unused_2268_; 
v_unused_2267_ = lean_ctor_get(v_a_2162_, 1);
lean_dec(v_unused_2267_);
v_unused_2268_ = lean_ctor_get(v_a_2162_, 0);
lean_dec(v_unused_2268_);
v___x_2175_ = v_a_2162_;
v_isShared_2176_ = v_isSharedCheck_2266_;
goto v_resetjp_2174_;
}
else
{
lean_inc(v_value_2172_);
lean_inc(v_type_2171_);
lean_inc(v_userName_2170_);
lean_dec(v_a_2162_);
v___x_2175_ = lean_box(0);
v_isShared_2176_ = v_isSharedCheck_2266_;
goto v_resetjp_2174_;
}
v_resetjp_2174_:
{
lean_object* v___x_2177_; 
v___x_2177_ = l_Lean_Meta_getZetaDeltaFVarIds___redArg(v_a_2145_);
if (lean_obj_tag(v___x_2177_) == 0)
{
lean_object* v_a_2178_; 
v_a_2178_ = lean_ctor_get(v___x_2177_, 0);
lean_inc(v_a_2178_);
lean_dec_ref_known(v___x_2177_, 1);
if (v_nondep_2173_ == 0)
{
uint8_t v___x_2185_; 
v___x_2185_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Closure_process_spec__0___redArg(v_fvarId_2159_, v_a_2178_);
lean_dec(v_a_2178_);
if (v___x_2185_ == 0)
{
lean_del_object(v___x_2175_);
lean_dec_ref(v_value_2172_);
goto v___jp_2179_;
}
else
{
lean_object* v___x_2186_; 
lean_dec(v_fvarId_2159_);
v___x_2186_ = l_Lean_Meta_Closure_collectExpr(v_type_2171_, v_a_2142_, v_a_2143_, v_a_2144_, v_a_2145_, v_a_2146_, v_a_2147_);
if (lean_obj_tag(v___x_2186_) == 0)
{
lean_object* v_a_2187_; lean_object* v___x_2188_; 
v_a_2187_ = lean_ctor_get(v___x_2186_, 0);
lean_inc(v_a_2187_);
lean_dec_ref_known(v___x_2186_, 1);
v___x_2188_ = l_Lean_Meta_Closure_collectExpr(v_value_2172_, v_a_2142_, v_a_2143_, v_a_2144_, v_a_2145_, v_a_2146_, v_a_2147_);
if (lean_obj_tag(v___x_2188_) == 0)
{
lean_object* v_a_2189_; lean_object* v___x_2190_; lean_object* v_visitedLevel_2191_; lean_object* v_visitedExpr_2192_; lean_object* v_levelParams_2193_; lean_object* v_nextLevelIdx_2194_; lean_object* v_levelArgs_2195_; lean_object* v_newLocalDecls_2196_; lean_object* v_newLocalDeclsForMVars_2197_; lean_object* v_newLetDecls_2198_; lean_object* v_nextExprIdx_2199_; lean_object* v_exprMVarArgs_2200_; lean_object* v_exprFVarArgs_2201_; lean_object* v_toProcess_2202_; lean_object* v___x_2204_; uint8_t v_isShared_2205_; uint8_t v_isSharedCheck_2241_; 
v_a_2189_ = lean_ctor_get(v___x_2188_, 0);
lean_inc(v_a_2189_);
lean_dec_ref_known(v___x_2188_, 1);
v___x_2190_ = lean_st_ref_take(v_a_2143_);
v_visitedLevel_2191_ = lean_ctor_get(v___x_2190_, 0);
v_visitedExpr_2192_ = lean_ctor_get(v___x_2190_, 1);
v_levelParams_2193_ = lean_ctor_get(v___x_2190_, 2);
v_nextLevelIdx_2194_ = lean_ctor_get(v___x_2190_, 3);
v_levelArgs_2195_ = lean_ctor_get(v___x_2190_, 4);
v_newLocalDecls_2196_ = lean_ctor_get(v___x_2190_, 5);
v_newLocalDeclsForMVars_2197_ = lean_ctor_get(v___x_2190_, 6);
v_newLetDecls_2198_ = lean_ctor_get(v___x_2190_, 7);
v_nextExprIdx_2199_ = lean_ctor_get(v___x_2190_, 8);
v_exprMVarArgs_2200_ = lean_ctor_get(v___x_2190_, 9);
v_exprFVarArgs_2201_ = lean_ctor_get(v___x_2190_, 10);
v_toProcess_2202_ = lean_ctor_get(v___x_2190_, 11);
v_isSharedCheck_2241_ = !lean_is_exclusive(v___x_2190_);
if (v_isSharedCheck_2241_ == 0)
{
v___x_2204_ = v___x_2190_;
v_isShared_2205_ = v_isSharedCheck_2241_;
goto v_resetjp_2203_;
}
else
{
lean_inc(v_toProcess_2202_);
lean_inc(v_exprFVarArgs_2201_);
lean_inc(v_exprMVarArgs_2200_);
lean_inc(v_nextExprIdx_2199_);
lean_inc(v_newLetDecls_2198_);
lean_inc(v_newLocalDeclsForMVars_2197_);
lean_inc(v_newLocalDecls_2196_);
lean_inc(v_levelArgs_2195_);
lean_inc(v_nextLevelIdx_2194_);
lean_inc(v_levelParams_2193_);
lean_inc(v_visitedExpr_2192_);
lean_inc(v_visitedLevel_2191_);
lean_dec(v___x_2190_);
v___x_2204_ = lean_box(0);
v_isShared_2205_ = v_isSharedCheck_2241_;
goto v_resetjp_2203_;
}
v_resetjp_2203_:
{
lean_object* v___x_2206_; uint8_t v___x_2207_; lean_object* v___x_2209_; 
v___x_2206_ = lean_unsigned_to_nat(0u);
v___x_2207_ = 0;
lean_inc(v_a_2189_);
lean_inc(v_newFVarId_2160_);
if (v_isShared_2176_ == 0)
{
lean_ctor_set(v___x_2175_, 4, v_a_2189_);
lean_ctor_set(v___x_2175_, 3, v_a_2187_);
lean_ctor_set(v___x_2175_, 1, v_newFVarId_2160_);
lean_ctor_set(v___x_2175_, 0, v___x_2206_);
v___x_2209_ = v___x_2175_;
goto v_reusejp_2208_;
}
else
{
lean_object* v_reuseFailAlloc_2240_; 
v_reuseFailAlloc_2240_ = lean_alloc_ctor(1, 5, 2);
lean_ctor_set(v_reuseFailAlloc_2240_, 0, v___x_2206_);
lean_ctor_set(v_reuseFailAlloc_2240_, 1, v_newFVarId_2160_);
lean_ctor_set(v_reuseFailAlloc_2240_, 2, v_userName_2170_);
lean_ctor_set(v_reuseFailAlloc_2240_, 3, v_a_2187_);
lean_ctor_set(v_reuseFailAlloc_2240_, 4, v_a_2189_);
lean_ctor_set_uint8(v_reuseFailAlloc_2240_, sizeof(void*)*5, v_nondep_2173_);
v___x_2209_ = v_reuseFailAlloc_2240_;
goto v_reusejp_2208_;
}
v_reusejp_2208_:
{
lean_object* v___x_2210_; lean_object* v___x_2212_; 
lean_ctor_set_uint8(v___x_2209_, sizeof(void*)*5 + 1, v___x_2207_);
v___x_2210_ = lean_array_push(v_newLetDecls_2198_, v___x_2209_);
if (v_isShared_2205_ == 0)
{
lean_ctor_set(v___x_2204_, 7, v___x_2210_);
v___x_2212_ = v___x_2204_;
goto v_reusejp_2211_;
}
else
{
lean_object* v_reuseFailAlloc_2239_; 
v_reuseFailAlloc_2239_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_2239_, 0, v_visitedLevel_2191_);
lean_ctor_set(v_reuseFailAlloc_2239_, 1, v_visitedExpr_2192_);
lean_ctor_set(v_reuseFailAlloc_2239_, 2, v_levelParams_2193_);
lean_ctor_set(v_reuseFailAlloc_2239_, 3, v_nextLevelIdx_2194_);
lean_ctor_set(v_reuseFailAlloc_2239_, 4, v_levelArgs_2195_);
lean_ctor_set(v_reuseFailAlloc_2239_, 5, v_newLocalDecls_2196_);
lean_ctor_set(v_reuseFailAlloc_2239_, 6, v_newLocalDeclsForMVars_2197_);
lean_ctor_set(v_reuseFailAlloc_2239_, 7, v___x_2210_);
lean_ctor_set(v_reuseFailAlloc_2239_, 8, v_nextExprIdx_2199_);
lean_ctor_set(v_reuseFailAlloc_2239_, 9, v_exprMVarArgs_2200_);
lean_ctor_set(v_reuseFailAlloc_2239_, 10, v_exprFVarArgs_2201_);
lean_ctor_set(v_reuseFailAlloc_2239_, 11, v_toProcess_2202_);
v___x_2212_ = v_reuseFailAlloc_2239_;
goto v_reusejp_2211_;
}
v_reusejp_2211_:
{
lean_object* v___x_2213_; lean_object* v___x_2214_; lean_object* v_visitedLevel_2215_; lean_object* v_visitedExpr_2216_; lean_object* v_levelParams_2217_; lean_object* v_nextLevelIdx_2218_; lean_object* v_levelArgs_2219_; lean_object* v_newLocalDecls_2220_; lean_object* v_newLocalDeclsForMVars_2221_; lean_object* v_newLetDecls_2222_; lean_object* v_nextExprIdx_2223_; lean_object* v_exprMVarArgs_2224_; lean_object* v_exprFVarArgs_2225_; lean_object* v_toProcess_2226_; lean_object* v___x_2228_; uint8_t v_isShared_2229_; uint8_t v_isSharedCheck_2238_; 
v___x_2213_ = lean_st_ref_put(v_a_2143_, v___x_2212_);
v___x_2214_ = lean_st_ref_take(v_a_2143_);
v_visitedLevel_2215_ = lean_ctor_get(v___x_2214_, 0);
v_visitedExpr_2216_ = lean_ctor_get(v___x_2214_, 1);
v_levelParams_2217_ = lean_ctor_get(v___x_2214_, 2);
v_nextLevelIdx_2218_ = lean_ctor_get(v___x_2214_, 3);
v_levelArgs_2219_ = lean_ctor_get(v___x_2214_, 4);
v_newLocalDecls_2220_ = lean_ctor_get(v___x_2214_, 5);
v_newLocalDeclsForMVars_2221_ = lean_ctor_get(v___x_2214_, 6);
v_newLetDecls_2222_ = lean_ctor_get(v___x_2214_, 7);
v_nextExprIdx_2223_ = lean_ctor_get(v___x_2214_, 8);
v_exprMVarArgs_2224_ = lean_ctor_get(v___x_2214_, 9);
v_exprFVarArgs_2225_ = lean_ctor_get(v___x_2214_, 10);
v_toProcess_2226_ = lean_ctor_get(v___x_2214_, 11);
v_isSharedCheck_2238_ = !lean_is_exclusive(v___x_2214_);
if (v_isSharedCheck_2238_ == 0)
{
v___x_2228_ = v___x_2214_;
v_isShared_2229_ = v_isSharedCheck_2238_;
goto v_resetjp_2227_;
}
else
{
lean_inc(v_toProcess_2226_);
lean_inc(v_exprFVarArgs_2225_);
lean_inc(v_exprMVarArgs_2224_);
lean_inc(v_nextExprIdx_2223_);
lean_inc(v_newLetDecls_2222_);
lean_inc(v_newLocalDeclsForMVars_2221_);
lean_inc(v_newLocalDecls_2220_);
lean_inc(v_levelArgs_2219_);
lean_inc(v_nextLevelIdx_2218_);
lean_inc(v_levelParams_2217_);
lean_inc(v_visitedExpr_2216_);
lean_inc(v_visitedLevel_2215_);
lean_dec(v___x_2214_);
v___x_2228_ = lean_box(0);
v_isShared_2229_ = v_isSharedCheck_2238_;
goto v_resetjp_2227_;
}
v_resetjp_2227_:
{
size_t v_sz_2230_; size_t v___x_2231_; lean_object* v___x_2232_; lean_object* v___x_2234_; 
v_sz_2230_ = lean_array_size(v_newLocalDecls_2220_);
v___x_2231_ = ((size_t)0ULL);
v___x_2232_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Closure_process_spec__1(v_newFVarId_2160_, v_a_2189_, v_sz_2230_, v___x_2231_, v_newLocalDecls_2220_);
lean_dec(v_a_2189_);
if (v_isShared_2229_ == 0)
{
lean_ctor_set(v___x_2228_, 5, v___x_2232_);
v___x_2234_ = v___x_2228_;
goto v_reusejp_2233_;
}
else
{
lean_object* v_reuseFailAlloc_2237_; 
v_reuseFailAlloc_2237_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_2237_, 0, v_visitedLevel_2215_);
lean_ctor_set(v_reuseFailAlloc_2237_, 1, v_visitedExpr_2216_);
lean_ctor_set(v_reuseFailAlloc_2237_, 2, v_levelParams_2217_);
lean_ctor_set(v_reuseFailAlloc_2237_, 3, v_nextLevelIdx_2218_);
lean_ctor_set(v_reuseFailAlloc_2237_, 4, v_levelArgs_2219_);
lean_ctor_set(v_reuseFailAlloc_2237_, 5, v___x_2232_);
lean_ctor_set(v_reuseFailAlloc_2237_, 6, v_newLocalDeclsForMVars_2221_);
lean_ctor_set(v_reuseFailAlloc_2237_, 7, v_newLetDecls_2222_);
lean_ctor_set(v_reuseFailAlloc_2237_, 8, v_nextExprIdx_2223_);
lean_ctor_set(v_reuseFailAlloc_2237_, 9, v_exprMVarArgs_2224_);
lean_ctor_set(v_reuseFailAlloc_2237_, 10, v_exprFVarArgs_2225_);
lean_ctor_set(v_reuseFailAlloc_2237_, 11, v_toProcess_2226_);
v___x_2234_ = v_reuseFailAlloc_2237_;
goto v_reusejp_2233_;
}
v_reusejp_2233_:
{
lean_object* v___x_2235_; 
v___x_2235_ = lean_st_ref_put(v_a_2143_, v___x_2234_);
goto _start;
}
}
}
}
}
}
else
{
lean_object* v_a_2242_; lean_object* v___x_2244_; uint8_t v_isShared_2245_; uint8_t v_isSharedCheck_2249_; 
lean_dec(v_a_2187_);
lean_del_object(v___x_2175_);
lean_dec(v_userName_2170_);
lean_dec(v_newFVarId_2160_);
v_a_2242_ = lean_ctor_get(v___x_2188_, 0);
v_isSharedCheck_2249_ = !lean_is_exclusive(v___x_2188_);
if (v_isSharedCheck_2249_ == 0)
{
v___x_2244_ = v___x_2188_;
v_isShared_2245_ = v_isSharedCheck_2249_;
goto v_resetjp_2243_;
}
else
{
lean_inc(v_a_2242_);
lean_dec(v___x_2188_);
v___x_2244_ = lean_box(0);
v_isShared_2245_ = v_isSharedCheck_2249_;
goto v_resetjp_2243_;
}
v_resetjp_2243_:
{
lean_object* v___x_2247_; 
if (v_isShared_2245_ == 0)
{
v___x_2247_ = v___x_2244_;
goto v_reusejp_2246_;
}
else
{
lean_object* v_reuseFailAlloc_2248_; 
v_reuseFailAlloc_2248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2248_, 0, v_a_2242_);
v___x_2247_ = v_reuseFailAlloc_2248_;
goto v_reusejp_2246_;
}
v_reusejp_2246_:
{
return v___x_2247_;
}
}
}
}
else
{
lean_object* v_a_2250_; lean_object* v___x_2252_; uint8_t v_isShared_2253_; uint8_t v_isSharedCheck_2257_; 
lean_del_object(v___x_2175_);
lean_dec_ref(v_value_2172_);
lean_dec(v_userName_2170_);
lean_dec(v_newFVarId_2160_);
v_a_2250_ = lean_ctor_get(v___x_2186_, 0);
v_isSharedCheck_2257_ = !lean_is_exclusive(v___x_2186_);
if (v_isSharedCheck_2257_ == 0)
{
v___x_2252_ = v___x_2186_;
v_isShared_2253_ = v_isSharedCheck_2257_;
goto v_resetjp_2251_;
}
else
{
lean_inc(v_a_2250_);
lean_dec(v___x_2186_);
v___x_2252_ = lean_box(0);
v_isShared_2253_ = v_isSharedCheck_2257_;
goto v_resetjp_2251_;
}
v_resetjp_2251_:
{
lean_object* v___x_2255_; 
if (v_isShared_2253_ == 0)
{
v___x_2255_ = v___x_2252_;
goto v_reusejp_2254_;
}
else
{
lean_object* v_reuseFailAlloc_2256_; 
v_reuseFailAlloc_2256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2256_, 0, v_a_2250_);
v___x_2255_ = v_reuseFailAlloc_2256_;
goto v_reusejp_2254_;
}
v_reusejp_2254_:
{
return v___x_2255_;
}
}
}
}
}
else
{
lean_dec(v_a_2178_);
lean_del_object(v___x_2175_);
lean_dec_ref(v_value_2172_);
goto v___jp_2179_;
}
v___jp_2179_:
{
uint8_t v___x_2180_; lean_object* v___x_2181_; 
v___x_2180_ = 0;
v___x_2181_ = l_Lean_Meta_Closure_pushLocalDecl(v_newFVarId_2160_, v_userName_2170_, v_type_2171_, v___x_2180_, v_a_2142_, v_a_2143_, v_a_2144_, v_a_2145_, v_a_2146_, v_a_2147_);
if (lean_obj_tag(v___x_2181_) == 0)
{
lean_object* v___x_2182_; lean_object* v___x_2183_; 
lean_dec_ref_known(v___x_2181_, 1);
v___x_2182_ = l_Lean_mkFVar(v_fvarId_2159_);
v___x_2183_ = l_Lean_Meta_Closure_pushFVarArg___redArg(v___x_2182_, v_a_2143_);
if (lean_obj_tag(v___x_2183_) == 0)
{
lean_dec_ref_known(v___x_2183_, 1);
goto _start;
}
else
{
return v___x_2183_;
}
}
else
{
lean_dec(v_fvarId_2159_);
return v___x_2181_;
}
}
}
else
{
lean_object* v_a_2258_; lean_object* v___x_2260_; uint8_t v_isShared_2261_; uint8_t v_isSharedCheck_2265_; 
lean_del_object(v___x_2175_);
lean_dec_ref(v_value_2172_);
lean_dec_ref(v_type_2171_);
lean_dec(v_userName_2170_);
lean_dec(v_newFVarId_2160_);
lean_dec(v_fvarId_2159_);
v_a_2258_ = lean_ctor_get(v___x_2177_, 0);
v_isSharedCheck_2265_ = !lean_is_exclusive(v___x_2177_);
if (v_isSharedCheck_2265_ == 0)
{
v___x_2260_ = v___x_2177_;
v_isShared_2261_ = v_isSharedCheck_2265_;
goto v_resetjp_2259_;
}
else
{
lean_inc(v_a_2258_);
lean_dec(v___x_2177_);
v___x_2260_ = lean_box(0);
v_isShared_2261_ = v_isSharedCheck_2265_;
goto v_resetjp_2259_;
}
v_resetjp_2259_:
{
lean_object* v___x_2263_; 
if (v_isShared_2261_ == 0)
{
v___x_2263_ = v___x_2260_;
goto v_reusejp_2262_;
}
else
{
lean_object* v_reuseFailAlloc_2264_; 
v_reuseFailAlloc_2264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2264_, 0, v_a_2258_);
v___x_2263_ = v_reuseFailAlloc_2264_;
goto v_reusejp_2262_;
}
v_reusejp_2262_:
{
return v___x_2263_;
}
}
}
}
}
}
else
{
lean_object* v_a_2269_; lean_object* v___x_2271_; uint8_t v_isShared_2272_; uint8_t v_isSharedCheck_2276_; 
lean_dec(v_newFVarId_2160_);
lean_dec(v_fvarId_2159_);
v_a_2269_ = lean_ctor_get(v___x_2161_, 0);
v_isSharedCheck_2276_ = !lean_is_exclusive(v___x_2161_);
if (v_isSharedCheck_2276_ == 0)
{
v___x_2271_ = v___x_2161_;
v_isShared_2272_ = v_isSharedCheck_2276_;
goto v_resetjp_2270_;
}
else
{
lean_inc(v_a_2269_);
lean_dec(v___x_2161_);
v___x_2271_ = lean_box(0);
v_isShared_2272_ = v_isSharedCheck_2276_;
goto v_resetjp_2270_;
}
v_resetjp_2270_:
{
lean_object* v___x_2274_; 
if (v_isShared_2272_ == 0)
{
v___x_2274_ = v___x_2271_;
goto v_reusejp_2273_;
}
else
{
lean_object* v_reuseFailAlloc_2275_; 
v_reuseFailAlloc_2275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2275_, 0, v_a_2269_);
v___x_2274_ = v_reuseFailAlloc_2275_;
goto v_reusejp_2273_;
}
v_reusejp_2273_:
{
return v___x_2274_;
}
}
}
}
}
}
else
{
lean_object* v_a_2278_; lean_object* v___x_2280_; uint8_t v_isShared_2281_; uint8_t v_isSharedCheck_2285_; 
v_a_2278_ = lean_ctor_get(v___x_2149_, 0);
v_isSharedCheck_2285_ = !lean_is_exclusive(v___x_2149_);
if (v_isSharedCheck_2285_ == 0)
{
v___x_2280_ = v___x_2149_;
v_isShared_2281_ = v_isSharedCheck_2285_;
goto v_resetjp_2279_;
}
else
{
lean_inc(v_a_2278_);
lean_dec(v___x_2149_);
v___x_2280_ = lean_box(0);
v_isShared_2281_ = v_isSharedCheck_2285_;
goto v_resetjp_2279_;
}
v_resetjp_2279_:
{
lean_object* v___x_2283_; 
if (v_isShared_2281_ == 0)
{
v___x_2283_ = v___x_2280_;
goto v_reusejp_2282_;
}
else
{
lean_object* v_reuseFailAlloc_2284_; 
v_reuseFailAlloc_2284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2284_, 0, v_a_2278_);
v___x_2283_ = v_reuseFailAlloc_2284_;
goto v_reusejp_2282_;
}
v_reusejp_2282_:
{
return v___x_2283_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_process___boxed(lean_object* v_a_2286_, lean_object* v_a_2287_, lean_object* v_a_2288_, lean_object* v_a_2289_, lean_object* v_a_2290_, lean_object* v_a_2291_, lean_object* v_a_2292_){
_start:
{
lean_object* v_res_2293_; 
v_res_2293_ = l_Lean_Meta_Closure_process(v_a_2286_, v_a_2287_, v_a_2288_, v_a_2289_, v_a_2290_, v_a_2291_);
lean_dec(v_a_2291_);
lean_dec_ref(v_a_2290_);
lean_dec(v_a_2289_);
lean_dec_ref(v_a_2288_);
lean_dec(v_a_2287_);
lean_dec_ref(v_a_2286_);
return v_res_2293_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Closure_process_spec__0(lean_object* v_00_u03b2_2294_, lean_object* v_k_2295_, lean_object* v_t_2296_){
_start:
{
uint8_t v___x_2297_; 
v___x_2297_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Closure_process_spec__0___redArg(v_k_2295_, v_t_2296_);
return v___x_2297_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Closure_process_spec__0___boxed(lean_object* v_00_u03b2_2298_, lean_object* v_k_2299_, lean_object* v_t_2300_){
_start:
{
uint8_t v_res_2301_; lean_object* v_r_2302_; 
v_res_2301_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Closure_process_spec__0(v_00_u03b2_2298_, v_k_2299_, v_t_2300_);
lean_dec(v_t_2300_);
lean_dec(v_k_2299_);
v_r_2302_ = lean_box(v_res_2301_);
return v_r_2302_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkBinding___lam__0(lean_object* v_decls_2303_, lean_object* v_xs_2304_, uint8_t v_isLambda_2305_, lean_object* v_i_2306_, lean_object* v_x_2307_, lean_object* v_b_2308_){
_start:
{
lean_object* v_decl_2309_; 
v_decl_2309_ = lean_array_fget_borrowed(v_decls_2303_, v_i_2306_);
if (lean_obj_tag(v_decl_2309_) == 0)
{
lean_object* v_userName_2310_; lean_object* v_type_2311_; uint8_t v_bi_2312_; lean_object* v_ty_2313_; 
v_userName_2310_ = lean_ctor_get(v_decl_2309_, 2);
v_type_2311_ = lean_ctor_get(v_decl_2309_, 3);
v_bi_2312_ = lean_ctor_get_uint8(v_decl_2309_, sizeof(void*)*4);
v_ty_2313_ = lean_expr_abstract_range(v_type_2311_, v_i_2306_, v_xs_2304_);
if (v_isLambda_2305_ == 0)
{
lean_object* v___x_2314_; 
lean_inc(v_userName_2310_);
v___x_2314_ = l_Lean_mkForall(v_userName_2310_, v_bi_2312_, v_ty_2313_, v_b_2308_);
return v___x_2314_;
}
else
{
lean_object* v___x_2315_; 
lean_inc(v_userName_2310_);
v___x_2315_ = l_Lean_mkLambda(v_userName_2310_, v_bi_2312_, v_ty_2313_, v_b_2308_);
return v___x_2315_;
}
}
else
{
lean_object* v_userName_2316_; lean_object* v_type_2317_; lean_object* v_value_2318_; uint8_t v_nondep_2319_; lean_object* v___x_2320_; uint8_t v___x_2321_; 
v_userName_2316_ = lean_ctor_get(v_decl_2309_, 2);
v_type_2317_ = lean_ctor_get(v_decl_2309_, 3);
v_value_2318_ = lean_ctor_get(v_decl_2309_, 4);
v_nondep_2319_ = lean_ctor_get_uint8(v_decl_2309_, sizeof(void*)*5);
v___x_2320_ = lean_unsigned_to_nat(0u);
v___x_2321_ = lean_expr_has_loose_bvar(v_b_2308_, v___x_2320_);
if (v___x_2321_ == 0)
{
lean_object* v___x_2322_; lean_object* v___x_2323_; 
v___x_2322_ = lean_unsigned_to_nat(1u);
v___x_2323_ = lean_expr_lower_loose_bvars(v_b_2308_, v___x_2322_, v___x_2322_);
lean_dec_ref(v_b_2308_);
return v___x_2323_;
}
else
{
lean_object* v_ty_2324_; lean_object* v_val_2325_; lean_object* v___x_2326_; 
v_ty_2324_ = lean_expr_abstract_range(v_type_2317_, v_i_2306_, v_xs_2304_);
v_val_2325_ = lean_expr_abstract_range(v_value_2318_, v_i_2306_, v_xs_2304_);
lean_inc(v_userName_2316_);
v___x_2326_ = l_Lean_Expr_letE___override(v_userName_2316_, v_ty_2324_, v_val_2325_, v_b_2308_, v_nondep_2319_);
return v___x_2326_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkBinding___lam__0___boxed(lean_object* v_decls_2327_, lean_object* v_xs_2328_, lean_object* v_isLambda_2329_, lean_object* v_i_2330_, lean_object* v_x_2331_, lean_object* v_b_2332_){
_start:
{
uint8_t v_isLambda_boxed_2333_; lean_object* v_res_2334_; 
v_isLambda_boxed_2333_ = lean_unbox(v_isLambda_2329_);
v_res_2334_ = l_Lean_Meta_Closure_mkBinding___lam__0(v_decls_2327_, v_xs_2328_, v_isLambda_boxed_2333_, v_i_2330_, v_x_2331_, v_b_2332_);
lean_dec(v_i_2330_);
lean_dec_ref(v_xs_2328_);
lean_dec_ref(v_decls_2327_);
return v_res_2334_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkBinding(uint8_t v_isLambda_2355_, lean_object* v_decls_2356_, lean_object* v_b_2357_){
_start:
{
lean_object* v___f_2358_; lean_object* v___x_2359_; size_t v_sz_2360_; size_t v___x_2361_; lean_object* v_xs_2362_; lean_object* v___x_2363_; lean_object* v___f_2364_; lean_object* v_b_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; 
v___f_2358_ = ((lean_object*)(l_Lean_Meta_Closure_mkBinding___closed__0));
v___x_2359_ = ((lean_object*)(l_Lean_Meta_Closure_mkBinding___closed__10));
v_sz_2360_ = lean_array_size(v_decls_2356_);
v___x_2361_ = ((size_t)0ULL);
lean_inc_ref_n(v_decls_2356_, 2);
v_xs_2362_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2359_, v___f_2358_, v_sz_2360_, v___x_2361_, v_decls_2356_);
v___x_2363_ = lean_box(v_isLambda_2355_);
lean_inc(v_xs_2362_);
v___f_2364_ = lean_alloc_closure((void*)(l_Lean_Meta_Closure_mkBinding___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2364_, 0, v_decls_2356_);
lean_closure_set(v___f_2364_, 1, v_xs_2362_);
lean_closure_set(v___f_2364_, 2, v___x_2363_);
v_b_2365_ = lean_expr_abstract(v_b_2357_, v_xs_2362_);
lean_dec(v_xs_2362_);
v___x_2366_ = lean_array_get_size(v_decls_2356_);
lean_dec_ref(v_decls_2356_);
v___x_2367_ = l_Nat_foldRev___redArg(v___x_2366_, v___f_2364_, v_b_2365_);
return v___x_2367_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkBinding___boxed(lean_object* v_isLambda_2368_, lean_object* v_decls_2369_, lean_object* v_b_2370_){
_start:
{
uint8_t v_isLambda_boxed_2371_; lean_object* v_res_2372_; 
v_isLambda_boxed_2371_ = lean_unbox(v_isLambda_2368_);
v_res_2372_ = l_Lean_Meta_Closure_mkBinding(v_isLambda_boxed_2371_, v_decls_2369_, v_b_2370_);
lean_dec_ref(v_b_2370_);
return v_res_2372_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Closure_mkLambda_spec__0(size_t v_sz_2373_, size_t v_i_2374_, lean_object* v_bs_2375_){
_start:
{
uint8_t v___x_2376_; 
v___x_2376_ = lean_usize_dec_lt(v_i_2374_, v_sz_2373_);
if (v___x_2376_ == 0)
{
return v_bs_2375_;
}
else
{
lean_object* v_v_2377_; lean_object* v___x_2378_; lean_object* v_bs_x27_2379_; lean_object* v___x_2380_; size_t v___x_2381_; size_t v___x_2382_; lean_object* v___x_2383_; 
v_v_2377_ = lean_array_uget(v_bs_2375_, v_i_2374_);
v___x_2378_ = lean_unsigned_to_nat(0u);
v_bs_x27_2379_ = lean_array_uset(v_bs_2375_, v_i_2374_, v___x_2378_);
v___x_2380_ = l_Lean_LocalDecl_toExpr(v_v_2377_);
v___x_2381_ = ((size_t)1ULL);
v___x_2382_ = lean_usize_add(v_i_2374_, v___x_2381_);
v___x_2383_ = lean_array_uset(v_bs_x27_2379_, v_i_2374_, v___x_2380_);
v_i_2374_ = v___x_2382_;
v_bs_2375_ = v___x_2383_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Closure_mkLambda_spec__0___boxed(lean_object* v_sz_2385_, lean_object* v_i_2386_, lean_object* v_bs_2387_){
_start:
{
size_t v_sz_boxed_2388_; size_t v_i_boxed_2389_; lean_object* v_res_2390_; 
v_sz_boxed_2388_ = lean_unbox_usize(v_sz_2385_);
lean_dec(v_sz_2385_);
v_i_boxed_2389_ = lean_unbox_usize(v_i_2386_);
lean_dec(v_i_2386_);
v_res_2390_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Closure_mkLambda_spec__0(v_sz_boxed_2388_, v_i_boxed_2389_, v_bs_2387_);
return v_res_2390_;
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_Meta_Closure_mkLambda_spec__1_spec__1(lean_object* v_decls_2391_, lean_object* v_xs_2392_, lean_object* v_x_2393_, lean_object* v_x_2394_){
_start:
{
lean_object* v_zero_2395_; uint8_t v_isZero_2396_; 
v_zero_2395_ = lean_unsigned_to_nat(0u);
v_isZero_2396_ = lean_nat_dec_eq(v_x_2393_, v_zero_2395_);
if (v_isZero_2396_ == 1)
{
lean_dec(v_x_2393_);
return v_x_2394_;
}
else
{
lean_object* v_one_2397_; lean_object* v_n_2398_; lean_object* v_decl_2399_; 
v_one_2397_ = lean_unsigned_to_nat(1u);
v_n_2398_ = lean_nat_sub(v_x_2393_, v_one_2397_);
lean_dec(v_x_2393_);
v_decl_2399_ = lean_array_fget_borrowed(v_decls_2391_, v_n_2398_);
if (lean_obj_tag(v_decl_2399_) == 0)
{
lean_object* v_userName_2400_; lean_object* v_type_2401_; uint8_t v_bi_2402_; lean_object* v_ty_2403_; lean_object* v___x_2404_; 
v_userName_2400_ = lean_ctor_get(v_decl_2399_, 2);
v_type_2401_ = lean_ctor_get(v_decl_2399_, 3);
v_bi_2402_ = lean_ctor_get_uint8(v_decl_2399_, sizeof(void*)*4);
v_ty_2403_ = lean_expr_abstract_range(v_type_2401_, v_n_2398_, v_xs_2392_);
lean_inc(v_userName_2400_);
v___x_2404_ = l_Lean_mkLambda(v_userName_2400_, v_bi_2402_, v_ty_2403_, v_x_2394_);
v_x_2393_ = v_n_2398_;
v_x_2394_ = v___x_2404_;
goto _start;
}
else
{
lean_object* v_userName_2406_; lean_object* v_type_2407_; lean_object* v_value_2408_; uint8_t v_nondep_2409_; uint8_t v___x_2410_; 
v_userName_2406_ = lean_ctor_get(v_decl_2399_, 2);
v_type_2407_ = lean_ctor_get(v_decl_2399_, 3);
v_value_2408_ = lean_ctor_get(v_decl_2399_, 4);
v_nondep_2409_ = lean_ctor_get_uint8(v_decl_2399_, sizeof(void*)*5);
v___x_2410_ = lean_expr_has_loose_bvar(v_x_2394_, v_zero_2395_);
if (v___x_2410_ == 0)
{
lean_object* v___x_2411_; 
v___x_2411_ = lean_expr_lower_loose_bvars(v_x_2394_, v_one_2397_, v_one_2397_);
lean_dec_ref(v_x_2394_);
v_x_2393_ = v_n_2398_;
v_x_2394_ = v___x_2411_;
goto _start;
}
else
{
lean_object* v_ty_2413_; lean_object* v_val_2414_; lean_object* v___x_2415_; 
v_ty_2413_ = lean_expr_abstract_range(v_type_2407_, v_n_2398_, v_xs_2392_);
v_val_2414_ = lean_expr_abstract_range(v_value_2408_, v_n_2398_, v_xs_2392_);
lean_inc(v_userName_2406_);
v___x_2415_ = l_Lean_Expr_letE___override(v_userName_2406_, v_ty_2413_, v_val_2414_, v_x_2394_, v_nondep_2409_);
v_x_2393_ = v_n_2398_;
v_x_2394_ = v___x_2415_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_Meta_Closure_mkLambda_spec__1_spec__1___boxed(lean_object* v_decls_2417_, lean_object* v_xs_2418_, lean_object* v_x_2419_, lean_object* v_x_2420_){
_start:
{
lean_object* v_res_2421_; 
v_res_2421_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_Meta_Closure_mkLambda_spec__1_spec__1(v_decls_2417_, v_xs_2418_, v_x_2419_, v_x_2420_);
lean_dec_ref(v_xs_2418_);
lean_dec_ref(v_decls_2417_);
return v_res_2421_;
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Lean_Meta_Closure_mkLambda_spec__1(lean_object* v_decls_2422_, lean_object* v_xs_2423_, lean_object* v_x_2424_, lean_object* v_x_2425_){
_start:
{
lean_object* v_zero_2426_; uint8_t v_isZero_2427_; 
v_zero_2426_ = lean_unsigned_to_nat(0u);
v_isZero_2427_ = lean_nat_dec_eq(v_x_2424_, v_zero_2426_);
if (v_isZero_2427_ == 1)
{
return v_x_2425_;
}
else
{
lean_object* v_one_2428_; lean_object* v_n_2429_; lean_object* v_decl_2430_; 
v_one_2428_ = lean_unsigned_to_nat(1u);
v_n_2429_ = lean_nat_sub(v_x_2424_, v_one_2428_);
v_decl_2430_ = lean_array_fget_borrowed(v_decls_2422_, v_n_2429_);
if (lean_obj_tag(v_decl_2430_) == 0)
{
lean_object* v_userName_2431_; lean_object* v_type_2432_; uint8_t v_bi_2433_; lean_object* v_ty_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; 
v_userName_2431_ = lean_ctor_get(v_decl_2430_, 2);
v_type_2432_ = lean_ctor_get(v_decl_2430_, 3);
v_bi_2433_ = lean_ctor_get_uint8(v_decl_2430_, sizeof(void*)*4);
v_ty_2434_ = lean_expr_abstract_range(v_type_2432_, v_n_2429_, v_xs_2423_);
lean_inc(v_userName_2431_);
v___x_2435_ = l_Lean_mkLambda(v_userName_2431_, v_bi_2433_, v_ty_2434_, v_x_2425_);
v___x_2436_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_Meta_Closure_mkLambda_spec__1_spec__1(v_decls_2422_, v_xs_2423_, v_n_2429_, v___x_2435_);
return v___x_2436_;
}
else
{
lean_object* v_userName_2437_; lean_object* v_type_2438_; lean_object* v_value_2439_; uint8_t v_nondep_2440_; uint8_t v___x_2441_; 
v_userName_2437_ = lean_ctor_get(v_decl_2430_, 2);
v_type_2438_ = lean_ctor_get(v_decl_2430_, 3);
v_value_2439_ = lean_ctor_get(v_decl_2430_, 4);
v_nondep_2440_ = lean_ctor_get_uint8(v_decl_2430_, sizeof(void*)*5);
v___x_2441_ = lean_expr_has_loose_bvar(v_x_2425_, v_zero_2426_);
if (v___x_2441_ == 0)
{
lean_object* v___x_2442_; lean_object* v___x_2443_; 
v___x_2442_ = lean_expr_lower_loose_bvars(v_x_2425_, v_one_2428_, v_one_2428_);
lean_dec_ref(v_x_2425_);
v___x_2443_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_Meta_Closure_mkLambda_spec__1_spec__1(v_decls_2422_, v_xs_2423_, v_n_2429_, v___x_2442_);
return v___x_2443_;
}
else
{
lean_object* v_ty_2444_; lean_object* v_val_2445_; lean_object* v___x_2446_; lean_object* v___x_2447_; 
v_ty_2444_ = lean_expr_abstract_range(v_type_2438_, v_n_2429_, v_xs_2423_);
v_val_2445_ = lean_expr_abstract_range(v_value_2439_, v_n_2429_, v_xs_2423_);
lean_inc(v_userName_2437_);
v___x_2446_ = l_Lean_Expr_letE___override(v_userName_2437_, v_ty_2444_, v_val_2445_, v_x_2425_, v_nondep_2440_);
v___x_2447_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_Meta_Closure_mkLambda_spec__1_spec__1(v_decls_2422_, v_xs_2423_, v_n_2429_, v___x_2446_);
return v___x_2447_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Lean_Meta_Closure_mkLambda_spec__1___boxed(lean_object* v_decls_2448_, lean_object* v_xs_2449_, lean_object* v_x_2450_, lean_object* v_x_2451_){
_start:
{
lean_object* v_res_2452_; 
v_res_2452_ = l_Nat_foldRev___at___00Lean_Meta_Closure_mkLambda_spec__1(v_decls_2448_, v_xs_2449_, v_x_2450_, v_x_2451_);
lean_dec(v_x_2450_);
lean_dec_ref(v_xs_2449_);
lean_dec_ref(v_decls_2448_);
return v_res_2452_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkLambda(lean_object* v_decls_2453_, lean_object* v_b_2454_){
_start:
{
size_t v_sz_2455_; size_t v___x_2456_; lean_object* v_xs_2457_; lean_object* v_b_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; 
v_sz_2455_ = lean_array_size(v_decls_2453_);
v___x_2456_ = ((size_t)0ULL);
lean_inc_ref(v_decls_2453_);
v_xs_2457_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Closure_mkLambda_spec__0(v_sz_2455_, v___x_2456_, v_decls_2453_);
v_b_2458_ = lean_expr_abstract(v_b_2454_, v_xs_2457_);
v___x_2459_ = lean_array_get_size(v_decls_2453_);
v___x_2460_ = l_Nat_foldRev___at___00Lean_Meta_Closure_mkLambda_spec__1(v_decls_2453_, v_xs_2457_, v___x_2459_, v_b_2458_);
lean_dec_ref(v_xs_2457_);
lean_dec_ref(v_decls_2453_);
return v___x_2460_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkLambda___boxed(lean_object* v_decls_2461_, lean_object* v_b_2462_){
_start:
{
lean_object* v_res_2463_; 
v_res_2463_ = l_Lean_Meta_Closure_mkLambda(v_decls_2461_, v_b_2462_);
lean_dec_ref(v_b_2462_);
return v_res_2463_;
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_Meta_Closure_mkForall_spec__0_spec__0(lean_object* v_decls_2464_, lean_object* v_xs_2465_, lean_object* v_x_2466_, lean_object* v_x_2467_){
_start:
{
lean_object* v_zero_2468_; uint8_t v_isZero_2469_; 
v_zero_2468_ = lean_unsigned_to_nat(0u);
v_isZero_2469_ = lean_nat_dec_eq(v_x_2466_, v_zero_2468_);
if (v_isZero_2469_ == 1)
{
lean_dec(v_x_2466_);
return v_x_2467_;
}
else
{
lean_object* v_one_2470_; lean_object* v_n_2471_; lean_object* v_decl_2472_; 
v_one_2470_ = lean_unsigned_to_nat(1u);
v_n_2471_ = lean_nat_sub(v_x_2466_, v_one_2470_);
lean_dec(v_x_2466_);
v_decl_2472_ = lean_array_fget_borrowed(v_decls_2464_, v_n_2471_);
if (lean_obj_tag(v_decl_2472_) == 0)
{
lean_object* v_userName_2473_; lean_object* v_type_2474_; uint8_t v_bi_2475_; lean_object* v_ty_2476_; lean_object* v___x_2477_; 
v_userName_2473_ = lean_ctor_get(v_decl_2472_, 2);
v_type_2474_ = lean_ctor_get(v_decl_2472_, 3);
v_bi_2475_ = lean_ctor_get_uint8(v_decl_2472_, sizeof(void*)*4);
v_ty_2476_ = lean_expr_abstract_range(v_type_2474_, v_n_2471_, v_xs_2465_);
lean_inc(v_userName_2473_);
v___x_2477_ = l_Lean_mkForall(v_userName_2473_, v_bi_2475_, v_ty_2476_, v_x_2467_);
v_x_2466_ = v_n_2471_;
v_x_2467_ = v___x_2477_;
goto _start;
}
else
{
lean_object* v_userName_2479_; lean_object* v_type_2480_; lean_object* v_value_2481_; uint8_t v_nondep_2482_; uint8_t v___x_2483_; 
v_userName_2479_ = lean_ctor_get(v_decl_2472_, 2);
v_type_2480_ = lean_ctor_get(v_decl_2472_, 3);
v_value_2481_ = lean_ctor_get(v_decl_2472_, 4);
v_nondep_2482_ = lean_ctor_get_uint8(v_decl_2472_, sizeof(void*)*5);
v___x_2483_ = lean_expr_has_loose_bvar(v_x_2467_, v_zero_2468_);
if (v___x_2483_ == 0)
{
lean_object* v___x_2484_; 
v___x_2484_ = lean_expr_lower_loose_bvars(v_x_2467_, v_one_2470_, v_one_2470_);
lean_dec_ref(v_x_2467_);
v_x_2466_ = v_n_2471_;
v_x_2467_ = v___x_2484_;
goto _start;
}
else
{
lean_object* v_ty_2486_; lean_object* v_val_2487_; lean_object* v___x_2488_; 
v_ty_2486_ = lean_expr_abstract_range(v_type_2480_, v_n_2471_, v_xs_2465_);
v_val_2487_ = lean_expr_abstract_range(v_value_2481_, v_n_2471_, v_xs_2465_);
lean_inc(v_userName_2479_);
v___x_2488_ = l_Lean_Expr_letE___override(v_userName_2479_, v_ty_2486_, v_val_2487_, v_x_2467_, v_nondep_2482_);
v_x_2466_ = v_n_2471_;
v_x_2467_ = v___x_2488_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_Meta_Closure_mkForall_spec__0_spec__0___boxed(lean_object* v_decls_2490_, lean_object* v_xs_2491_, lean_object* v_x_2492_, lean_object* v_x_2493_){
_start:
{
lean_object* v_res_2494_; 
v_res_2494_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_Meta_Closure_mkForall_spec__0_spec__0(v_decls_2490_, v_xs_2491_, v_x_2492_, v_x_2493_);
lean_dec_ref(v_xs_2491_);
lean_dec_ref(v_decls_2490_);
return v_res_2494_;
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Lean_Meta_Closure_mkForall_spec__0(lean_object* v_decls_2495_, lean_object* v_xs_2496_, lean_object* v_x_2497_, lean_object* v_x_2498_){
_start:
{
lean_object* v_zero_2499_; uint8_t v_isZero_2500_; 
v_zero_2499_ = lean_unsigned_to_nat(0u);
v_isZero_2500_ = lean_nat_dec_eq(v_x_2497_, v_zero_2499_);
if (v_isZero_2500_ == 1)
{
return v_x_2498_;
}
else
{
lean_object* v_one_2501_; lean_object* v_n_2502_; lean_object* v_decl_2503_; 
v_one_2501_ = lean_unsigned_to_nat(1u);
v_n_2502_ = lean_nat_sub(v_x_2497_, v_one_2501_);
v_decl_2503_ = lean_array_fget_borrowed(v_decls_2495_, v_n_2502_);
if (lean_obj_tag(v_decl_2503_) == 0)
{
lean_object* v_userName_2504_; lean_object* v_type_2505_; uint8_t v_bi_2506_; lean_object* v_ty_2507_; lean_object* v___x_2508_; lean_object* v___x_2509_; 
v_userName_2504_ = lean_ctor_get(v_decl_2503_, 2);
v_type_2505_ = lean_ctor_get(v_decl_2503_, 3);
v_bi_2506_ = lean_ctor_get_uint8(v_decl_2503_, sizeof(void*)*4);
v_ty_2507_ = lean_expr_abstract_range(v_type_2505_, v_n_2502_, v_xs_2496_);
lean_inc(v_userName_2504_);
v___x_2508_ = l_Lean_mkForall(v_userName_2504_, v_bi_2506_, v_ty_2507_, v_x_2498_);
v___x_2509_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_Meta_Closure_mkForall_spec__0_spec__0(v_decls_2495_, v_xs_2496_, v_n_2502_, v___x_2508_);
return v___x_2509_;
}
else
{
lean_object* v_userName_2510_; lean_object* v_type_2511_; lean_object* v_value_2512_; uint8_t v_nondep_2513_; uint8_t v___x_2514_; 
v_userName_2510_ = lean_ctor_get(v_decl_2503_, 2);
v_type_2511_ = lean_ctor_get(v_decl_2503_, 3);
v_value_2512_ = lean_ctor_get(v_decl_2503_, 4);
v_nondep_2513_ = lean_ctor_get_uint8(v_decl_2503_, sizeof(void*)*5);
v___x_2514_ = lean_expr_has_loose_bvar(v_x_2498_, v_zero_2499_);
if (v___x_2514_ == 0)
{
lean_object* v___x_2515_; lean_object* v___x_2516_; 
v___x_2515_ = lean_expr_lower_loose_bvars(v_x_2498_, v_one_2501_, v_one_2501_);
lean_dec_ref(v_x_2498_);
v___x_2516_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_Meta_Closure_mkForall_spec__0_spec__0(v_decls_2495_, v_xs_2496_, v_n_2502_, v___x_2515_);
return v___x_2516_;
}
else
{
lean_object* v_ty_2517_; lean_object* v_val_2518_; lean_object* v___x_2519_; lean_object* v___x_2520_; 
v_ty_2517_ = lean_expr_abstract_range(v_type_2511_, v_n_2502_, v_xs_2496_);
v_val_2518_ = lean_expr_abstract_range(v_value_2512_, v_n_2502_, v_xs_2496_);
lean_inc(v_userName_2510_);
v___x_2519_ = l_Lean_Expr_letE___override(v_userName_2510_, v_ty_2517_, v_val_2518_, v_x_2498_, v_nondep_2513_);
v___x_2520_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_Meta_Closure_mkForall_spec__0_spec__0(v_decls_2495_, v_xs_2496_, v_n_2502_, v___x_2519_);
return v___x_2520_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Lean_Meta_Closure_mkForall_spec__0___boxed(lean_object* v_decls_2521_, lean_object* v_xs_2522_, lean_object* v_x_2523_, lean_object* v_x_2524_){
_start:
{
lean_object* v_res_2525_; 
v_res_2525_ = l_Nat_foldRev___at___00Lean_Meta_Closure_mkForall_spec__0(v_decls_2521_, v_xs_2522_, v_x_2523_, v_x_2524_);
lean_dec(v_x_2523_);
lean_dec_ref(v_xs_2522_);
lean_dec_ref(v_decls_2521_);
return v_res_2525_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkForall(lean_object* v_decls_2526_, lean_object* v_b_2527_){
_start:
{
size_t v_sz_2528_; size_t v___x_2529_; lean_object* v_xs_2530_; lean_object* v_b_2531_; lean_object* v___x_2532_; lean_object* v___x_2533_; 
v_sz_2528_ = lean_array_size(v_decls_2526_);
v___x_2529_ = ((size_t)0ULL);
lean_inc_ref(v_decls_2526_);
v_xs_2530_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Closure_mkLambda_spec__0(v_sz_2528_, v___x_2529_, v_decls_2526_);
v_b_2531_ = lean_expr_abstract(v_b_2527_, v_xs_2530_);
v___x_2532_ = lean_array_get_size(v_decls_2526_);
v___x_2533_ = l_Nat_foldRev___at___00Lean_Meta_Closure_mkForall_spec__0(v_decls_2526_, v_xs_2530_, v___x_2532_, v_b_2531_);
lean_dec_ref(v_xs_2530_);
lean_dec_ref(v_decls_2526_);
return v___x_2533_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkForall___boxed(lean_object* v_decls_2534_, lean_object* v_b_2535_){
_start:
{
lean_object* v_res_2536_; 
v_res_2536_ = l_Lean_Meta_Closure_mkForall(v_decls_2534_, v_b_2535_);
lean_dec_ref(v_b_2535_);
return v_res_2536_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkValueTypeClosureAux___lam__0(lean_object* v_a_2537_, lean_object* v_cache_2538_, lean_object* v_a_x3f_2539_){
_start:
{
lean_object* v___x_2541_; lean_object* v_mctx_2542_; lean_object* v_zetaDeltaFVarIds_2543_; lean_object* v_postponed_2544_; lean_object* v_diag_2545_; lean_object* v___x_2547_; uint8_t v_isShared_2548_; uint8_t v_isSharedCheck_2555_; 
v___x_2541_ = lean_st_ref_take(v_a_2537_);
v_mctx_2542_ = lean_ctor_get(v___x_2541_, 0);
v_zetaDeltaFVarIds_2543_ = lean_ctor_get(v___x_2541_, 2);
v_postponed_2544_ = lean_ctor_get(v___x_2541_, 3);
v_diag_2545_ = lean_ctor_get(v___x_2541_, 4);
v_isSharedCheck_2555_ = !lean_is_exclusive(v___x_2541_);
if (v_isSharedCheck_2555_ == 0)
{
lean_object* v_unused_2556_; 
v_unused_2556_ = lean_ctor_get(v___x_2541_, 1);
lean_dec(v_unused_2556_);
v___x_2547_ = v___x_2541_;
v_isShared_2548_ = v_isSharedCheck_2555_;
goto v_resetjp_2546_;
}
else
{
lean_inc(v_diag_2545_);
lean_inc(v_postponed_2544_);
lean_inc(v_zetaDeltaFVarIds_2543_);
lean_inc(v_mctx_2542_);
lean_dec(v___x_2541_);
v___x_2547_ = lean_box(0);
v_isShared_2548_ = v_isSharedCheck_2555_;
goto v_resetjp_2546_;
}
v_resetjp_2546_:
{
lean_object* v___x_2549_; lean_object* v___x_2551_; 
v___x_2549_ = lean_box(0);
if (v_isShared_2548_ == 0)
{
lean_ctor_set(v___x_2547_, 1, v_cache_2538_);
v___x_2551_ = v___x_2547_;
goto v_reusejp_2550_;
}
else
{
lean_object* v_reuseFailAlloc_2554_; 
v_reuseFailAlloc_2554_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2554_, 0, v_mctx_2542_);
lean_ctor_set(v_reuseFailAlloc_2554_, 1, v_cache_2538_);
lean_ctor_set(v_reuseFailAlloc_2554_, 2, v_zetaDeltaFVarIds_2543_);
lean_ctor_set(v_reuseFailAlloc_2554_, 3, v_postponed_2544_);
lean_ctor_set(v_reuseFailAlloc_2554_, 4, v_diag_2545_);
v___x_2551_ = v_reuseFailAlloc_2554_;
goto v_reusejp_2550_;
}
v_reusejp_2550_:
{
lean_object* v___x_2552_; lean_object* v___x_2553_; 
v___x_2552_ = lean_st_ref_put(v_a_2537_, v___x_2551_);
v___x_2553_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2553_, 0, v___x_2549_);
return v___x_2553_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkValueTypeClosureAux___lam__0___boxed(lean_object* v_a_2557_, lean_object* v_cache_2558_, lean_object* v_a_x3f_2559_, lean_object* v___y_2560_){
_start:
{
lean_object* v_res_2561_; 
v_res_2561_ = l_Lean_Meta_Closure_mkValueTypeClosureAux___lam__0(v_a_2557_, v_cache_2558_, v_a_x3f_2559_);
lean_dec(v_a_x3f_2559_);
lean_dec(v_a_2557_);
return v_res_2561_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkValueTypeClosureAux___lam__1(lean_object* v_a_2562_, lean_object* v_zetaDeltaFVarIds_2563_, lean_object* v_a_x3f_2564_){
_start:
{
lean_object* v___x_2566_; lean_object* v_mctx_2567_; lean_object* v_cache_2568_; lean_object* v_postponed_2569_; lean_object* v_diag_2570_; lean_object* v___x_2572_; uint8_t v_isShared_2573_; uint8_t v_isSharedCheck_2580_; 
v___x_2566_ = lean_st_ref_take(v_a_2562_);
v_mctx_2567_ = lean_ctor_get(v___x_2566_, 0);
v_cache_2568_ = lean_ctor_get(v___x_2566_, 1);
v_postponed_2569_ = lean_ctor_get(v___x_2566_, 3);
v_diag_2570_ = lean_ctor_get(v___x_2566_, 4);
v_isSharedCheck_2580_ = !lean_is_exclusive(v___x_2566_);
if (v_isSharedCheck_2580_ == 0)
{
lean_object* v_unused_2581_; 
v_unused_2581_ = lean_ctor_get(v___x_2566_, 2);
lean_dec(v_unused_2581_);
v___x_2572_ = v___x_2566_;
v_isShared_2573_ = v_isSharedCheck_2580_;
goto v_resetjp_2571_;
}
else
{
lean_inc(v_diag_2570_);
lean_inc(v_postponed_2569_);
lean_inc(v_cache_2568_);
lean_inc(v_mctx_2567_);
lean_dec(v___x_2566_);
v___x_2572_ = lean_box(0);
v_isShared_2573_ = v_isSharedCheck_2580_;
goto v_resetjp_2571_;
}
v_resetjp_2571_:
{
lean_object* v___x_2574_; lean_object* v___x_2576_; 
v___x_2574_ = lean_box(0);
if (v_isShared_2573_ == 0)
{
lean_ctor_set(v___x_2572_, 2, v_zetaDeltaFVarIds_2563_);
v___x_2576_ = v___x_2572_;
goto v_reusejp_2575_;
}
else
{
lean_object* v_reuseFailAlloc_2579_; 
v_reuseFailAlloc_2579_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2579_, 0, v_mctx_2567_);
lean_ctor_set(v_reuseFailAlloc_2579_, 1, v_cache_2568_);
lean_ctor_set(v_reuseFailAlloc_2579_, 2, v_zetaDeltaFVarIds_2563_);
lean_ctor_set(v_reuseFailAlloc_2579_, 3, v_postponed_2569_);
lean_ctor_set(v_reuseFailAlloc_2579_, 4, v_diag_2570_);
v___x_2576_ = v_reuseFailAlloc_2579_;
goto v_reusejp_2575_;
}
v_reusejp_2575_:
{
lean_object* v___x_2577_; lean_object* v___x_2578_; 
v___x_2577_ = lean_st_ref_put(v_a_2562_, v___x_2576_);
v___x_2578_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2578_, 0, v___x_2574_);
return v___x_2578_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkValueTypeClosureAux___lam__1___boxed(lean_object* v_a_2582_, lean_object* v_zetaDeltaFVarIds_2583_, lean_object* v_a_x3f_2584_, lean_object* v___y_2585_){
_start:
{
lean_object* v_res_2586_; 
v_res_2586_ = l_Lean_Meta_Closure_mkValueTypeClosureAux___lam__1(v_a_2582_, v_zetaDeltaFVarIds_2583_, v_a_x3f_2584_);
lean_dec(v_a_x3f_2584_);
lean_dec(v_a_2582_);
return v_res_2586_;
}
}
static lean_object* _init_l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__0(void){
_start:
{
lean_object* v___x_2587_; 
v___x_2587_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_2587_;
}
}
static lean_object* _init_l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__1(void){
_start:
{
lean_object* v___x_2588_; lean_object* v___x_2589_; 
v___x_2588_ = lean_obj_once(&l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__0, &l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__0_once, _init_l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__0);
v___x_2589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2589_, 0, v___x_2588_);
return v___x_2589_;
}
}
static lean_object* _init_l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__2(void){
_start:
{
lean_object* v___x_2590_; lean_object* v___x_2591_; 
v___x_2590_ = lean_obj_once(&l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__1, &l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__1_once, _init_l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__1);
v___x_2591_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2591_, 0, v___x_2590_);
lean_ctor_set(v___x_2591_, 1, v___x_2590_);
lean_ctor_set(v___x_2591_, 2, v___x_2590_);
lean_ctor_set(v___x_2591_, 3, v___x_2590_);
lean_ctor_set(v___x_2591_, 4, v___x_2590_);
lean_ctor_set(v___x_2591_, 5, v___x_2590_);
return v___x_2591_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkValueTypeClosureAux(lean_object* v_type_2592_, lean_object* v_value_2593_, lean_object* v_a_2594_, lean_object* v_a_2595_, lean_object* v_a_2596_, lean_object* v_a_2597_, lean_object* v_a_2598_, lean_object* v_a_2599_){
_start:
{
lean_object* v___x_2601_; lean_object* v___x_2602_; lean_object* v_cache_2603_; lean_object* v_a_2605_; lean_object* v___x_2616_; lean_object* v_mctx_2617_; lean_object* v_zetaDeltaFVarIds_2618_; lean_object* v_postponed_2619_; lean_object* v_diag_2620_; lean_object* v___x_2622_; uint8_t v_isShared_2623_; uint8_t v_isSharedCheck_2686_; 
v___x_2601_ = lean_box(1);
v___x_2602_ = lean_st_ref_get(v_a_2597_);
v_cache_2603_ = lean_ctor_get(v___x_2602_, 1);
lean_inc_ref(v_cache_2603_);
lean_dec(v___x_2602_);
v___x_2616_ = lean_st_ref_take(v_a_2597_);
v_mctx_2617_ = lean_ctor_get(v___x_2616_, 0);
v_zetaDeltaFVarIds_2618_ = lean_ctor_get(v___x_2616_, 2);
v_postponed_2619_ = lean_ctor_get(v___x_2616_, 3);
v_diag_2620_ = lean_ctor_get(v___x_2616_, 4);
v_isSharedCheck_2686_ = !lean_is_exclusive(v___x_2616_);
if (v_isSharedCheck_2686_ == 0)
{
lean_object* v_unused_2687_; 
v_unused_2687_ = lean_ctor_get(v___x_2616_, 1);
lean_dec(v_unused_2687_);
v___x_2622_ = v___x_2616_;
v_isShared_2623_ = v_isSharedCheck_2686_;
goto v_resetjp_2621_;
}
else
{
lean_inc(v_diag_2620_);
lean_inc(v_postponed_2619_);
lean_inc(v_zetaDeltaFVarIds_2618_);
lean_inc(v_mctx_2617_);
lean_dec(v___x_2616_);
v___x_2622_ = lean_box(0);
v_isShared_2623_ = v_isSharedCheck_2686_;
goto v_resetjp_2621_;
}
v___jp_2604_:
{
lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v___x_2609_; uint8_t v_isShared_2610_; uint8_t v_isSharedCheck_2614_; 
v___x_2606_ = lean_box(0);
v___x_2607_ = l_Lean_Meta_Closure_mkValueTypeClosureAux___lam__0(v_a_2597_, v_cache_2603_, v___x_2606_);
v_isSharedCheck_2614_ = !lean_is_exclusive(v___x_2607_);
if (v_isSharedCheck_2614_ == 0)
{
lean_object* v_unused_2615_; 
v_unused_2615_ = lean_ctor_get(v___x_2607_, 0);
lean_dec(v_unused_2615_);
v___x_2609_ = v___x_2607_;
v_isShared_2610_ = v_isSharedCheck_2614_;
goto v_resetjp_2608_;
}
else
{
lean_dec(v___x_2607_);
v___x_2609_ = lean_box(0);
v_isShared_2610_ = v_isSharedCheck_2614_;
goto v_resetjp_2608_;
}
v_resetjp_2608_:
{
lean_object* v___x_2612_; 
if (v_isShared_2610_ == 0)
{
lean_ctor_set_tag(v___x_2609_, 1);
lean_ctor_set(v___x_2609_, 0, v_a_2605_);
v___x_2612_ = v___x_2609_;
goto v_reusejp_2611_;
}
else
{
lean_object* v_reuseFailAlloc_2613_; 
v_reuseFailAlloc_2613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2613_, 0, v_a_2605_);
v___x_2612_ = v_reuseFailAlloc_2613_;
goto v_reusejp_2611_;
}
v_reusejp_2611_:
{
return v___x_2612_;
}
}
}
v_resetjp_2621_:
{
lean_object* v___x_2624_; lean_object* v___x_2626_; 
v___x_2624_ = lean_obj_once(&l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__2, &l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__2_once, _init_l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__2);
if (v_isShared_2623_ == 0)
{
lean_ctor_set(v___x_2622_, 1, v___x_2624_);
v___x_2626_ = v___x_2622_;
goto v_reusejp_2625_;
}
else
{
lean_object* v_reuseFailAlloc_2685_; 
v_reuseFailAlloc_2685_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2685_, 0, v_mctx_2617_);
lean_ctor_set(v_reuseFailAlloc_2685_, 1, v___x_2624_);
lean_ctor_set(v_reuseFailAlloc_2685_, 2, v_zetaDeltaFVarIds_2618_);
lean_ctor_set(v_reuseFailAlloc_2685_, 3, v_postponed_2619_);
lean_ctor_set(v_reuseFailAlloc_2685_, 4, v_diag_2620_);
v___x_2626_ = v_reuseFailAlloc_2685_;
goto v_reusejp_2625_;
}
v_reusejp_2625_:
{
lean_object* v___x_2627_; lean_object* v_keyedConfig_2628_; lean_object* v_zetaDeltaSet_2629_; lean_object* v_lctx_2630_; lean_object* v_localInstances_2631_; lean_object* v_defEqCtx_x3f_2632_; lean_object* v_synthPendingDepth_2633_; lean_object* v_customCanUnfoldPredicate_x3f_2634_; uint8_t v_univApprox_2635_; uint8_t v_inTypeClassResolution_2636_; uint8_t v_cacheInferType_2637_; uint8_t v___x_2638_; lean_object* v___x_2639_; lean_object* v___x_2640_; lean_object* v_mctx_2641_; lean_object* v_cache_2642_; lean_object* v_zetaDeltaFVarIds_2643_; lean_object* v_postponed_2644_; lean_object* v_diag_2645_; lean_object* v___x_2647_; uint8_t v_isShared_2648_; uint8_t v_isSharedCheck_2684_; 
v___x_2627_ = lean_st_ref_put(v_a_2597_, v___x_2626_);
v_keyedConfig_2628_ = lean_ctor_get(v_a_2596_, 0);
v_zetaDeltaSet_2629_ = lean_ctor_get(v_a_2596_, 1);
v_lctx_2630_ = lean_ctor_get(v_a_2596_, 2);
v_localInstances_2631_ = lean_ctor_get(v_a_2596_, 3);
v_defEqCtx_x3f_2632_ = lean_ctor_get(v_a_2596_, 4);
v_synthPendingDepth_2633_ = lean_ctor_get(v_a_2596_, 5);
v_customCanUnfoldPredicate_x3f_2634_ = lean_ctor_get(v_a_2596_, 6);
v_univApprox_2635_ = lean_ctor_get_uint8(v_a_2596_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2636_ = lean_ctor_get_uint8(v_a_2596_, sizeof(void*)*7 + 2);
v_cacheInferType_2637_ = lean_ctor_get_uint8(v_a_2596_, sizeof(void*)*7 + 3);
v___x_2638_ = 1;
lean_inc(v_customCanUnfoldPredicate_x3f_2634_);
lean_inc(v_synthPendingDepth_2633_);
lean_inc(v_defEqCtx_x3f_2632_);
lean_inc_ref(v_localInstances_2631_);
lean_inc_ref(v_lctx_2630_);
lean_inc(v_zetaDeltaSet_2629_);
lean_inc_ref(v_keyedConfig_2628_);
v___x_2639_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2639_, 0, v_keyedConfig_2628_);
lean_ctor_set(v___x_2639_, 1, v_zetaDeltaSet_2629_);
lean_ctor_set(v___x_2639_, 2, v_lctx_2630_);
lean_ctor_set(v___x_2639_, 3, v_localInstances_2631_);
lean_ctor_set(v___x_2639_, 4, v_defEqCtx_x3f_2632_);
lean_ctor_set(v___x_2639_, 5, v_synthPendingDepth_2633_);
lean_ctor_set(v___x_2639_, 6, v_customCanUnfoldPredicate_x3f_2634_);
lean_ctor_set_uint8(v___x_2639_, sizeof(void*)*7, v___x_2638_);
lean_ctor_set_uint8(v___x_2639_, sizeof(void*)*7 + 1, v_univApprox_2635_);
lean_ctor_set_uint8(v___x_2639_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2636_);
lean_ctor_set_uint8(v___x_2639_, sizeof(void*)*7 + 3, v_cacheInferType_2637_);
v___x_2640_ = lean_st_ref_take(v_a_2597_);
v_mctx_2641_ = lean_ctor_get(v___x_2640_, 0);
v_cache_2642_ = lean_ctor_get(v___x_2640_, 1);
v_zetaDeltaFVarIds_2643_ = lean_ctor_get(v___x_2640_, 2);
v_postponed_2644_ = lean_ctor_get(v___x_2640_, 3);
v_diag_2645_ = lean_ctor_get(v___x_2640_, 4);
v_isSharedCheck_2684_ = !lean_is_exclusive(v___x_2640_);
if (v_isSharedCheck_2684_ == 0)
{
v___x_2647_ = v___x_2640_;
v_isShared_2648_ = v_isSharedCheck_2684_;
goto v_resetjp_2646_;
}
else
{
lean_inc(v_diag_2645_);
lean_inc(v_postponed_2644_);
lean_inc(v_zetaDeltaFVarIds_2643_);
lean_inc(v_cache_2642_);
lean_inc(v_mctx_2641_);
lean_dec(v___x_2640_);
v___x_2647_ = lean_box(0);
v_isShared_2648_ = v_isSharedCheck_2684_;
goto v_resetjp_2646_;
}
v_resetjp_2646_:
{
lean_object* v_a_2650_; lean_object* v___x_2654_; 
if (v_isShared_2648_ == 0)
{
lean_ctor_set(v___x_2647_, 2, v___x_2601_);
v___x_2654_ = v___x_2647_;
goto v_reusejp_2653_;
}
else
{
lean_object* v_reuseFailAlloc_2683_; 
v_reuseFailAlloc_2683_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2683_, 0, v_mctx_2641_);
lean_ctor_set(v_reuseFailAlloc_2683_, 1, v_cache_2642_);
lean_ctor_set(v_reuseFailAlloc_2683_, 2, v___x_2601_);
lean_ctor_set(v_reuseFailAlloc_2683_, 3, v_postponed_2644_);
lean_ctor_set(v_reuseFailAlloc_2683_, 4, v_diag_2645_);
v___x_2654_ = v_reuseFailAlloc_2683_;
goto v_reusejp_2653_;
}
v___jp_2649_:
{
lean_object* v___x_2651_; lean_object* v___x_2652_; 
v___x_2651_ = lean_box(0);
v___x_2652_ = l_Lean_Meta_Closure_mkValueTypeClosureAux___lam__1(v_a_2597_, v_zetaDeltaFVarIds_2643_, v___x_2651_);
lean_dec_ref(v___x_2652_);
v_a_2605_ = v_a_2650_;
goto v___jp_2604_;
}
v_reusejp_2653_:
{
lean_object* v___x_2655_; lean_object* v___x_2656_; 
v___x_2655_ = lean_st_ref_put(v_a_2597_, v___x_2654_);
v___x_2656_ = l_Lean_Meta_Closure_collectExpr(v_type_2592_, v_a_2594_, v_a_2595_, v___x_2639_, v_a_2597_, v_a_2598_, v_a_2599_);
if (lean_obj_tag(v___x_2656_) == 0)
{
lean_object* v_a_2657_; lean_object* v___x_2658_; 
v_a_2657_ = lean_ctor_get(v___x_2656_, 0);
lean_inc(v_a_2657_);
lean_dec_ref_known(v___x_2656_, 1);
v___x_2658_ = l_Lean_Meta_Closure_collectExpr(v_value_2593_, v_a_2594_, v_a_2595_, v___x_2639_, v_a_2597_, v_a_2598_, v_a_2599_);
if (lean_obj_tag(v___x_2658_) == 0)
{
lean_object* v_a_2659_; lean_object* v___x_2660_; 
v_a_2659_ = lean_ctor_get(v___x_2658_, 0);
lean_inc(v_a_2659_);
lean_dec_ref_known(v___x_2658_, 1);
v___x_2660_ = l_Lean_Meta_Closure_process(v_a_2594_, v_a_2595_, v___x_2639_, v_a_2597_, v_a_2598_, v_a_2599_);
lean_dec_ref_known(v___x_2639_, 7);
if (lean_obj_tag(v___x_2660_) == 0)
{
lean_object* v___x_2662_; uint8_t v_isShared_2663_; uint8_t v_isSharedCheck_2678_; 
v_isSharedCheck_2678_ = !lean_is_exclusive(v___x_2660_);
if (v_isSharedCheck_2678_ == 0)
{
lean_object* v_unused_2679_; 
v_unused_2679_ = lean_ctor_get(v___x_2660_, 0);
lean_dec(v_unused_2679_);
v___x_2662_ = v___x_2660_;
v_isShared_2663_ = v_isSharedCheck_2678_;
goto v_resetjp_2661_;
}
else
{
lean_dec(v___x_2660_);
v___x_2662_ = lean_box(0);
v_isShared_2663_ = v_isSharedCheck_2678_;
goto v_resetjp_2661_;
}
v_resetjp_2661_:
{
lean_object* v___x_2664_; lean_object* v___x_2666_; 
v___x_2664_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2664_, 0, v_a_2657_);
lean_ctor_set(v___x_2664_, 1, v_a_2659_);
lean_inc_ref(v___x_2664_);
if (v_isShared_2663_ == 0)
{
lean_ctor_set_tag(v___x_2662_, 1);
lean_ctor_set(v___x_2662_, 0, v___x_2664_);
v___x_2666_ = v___x_2662_;
goto v_reusejp_2665_;
}
else
{
lean_object* v_reuseFailAlloc_2677_; 
v_reuseFailAlloc_2677_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2677_, 0, v___x_2664_);
v___x_2666_ = v_reuseFailAlloc_2677_;
goto v_reusejp_2665_;
}
v_reusejp_2665_:
{
lean_object* v___x_2667_; lean_object* v___x_2668_; lean_object* v___x_2670_; uint8_t v_isShared_2671_; uint8_t v_isSharedCheck_2675_; 
v___x_2667_ = l_Lean_Meta_Closure_mkValueTypeClosureAux___lam__1(v_a_2597_, v_zetaDeltaFVarIds_2643_, v___x_2666_);
lean_dec_ref(v___x_2667_);
v___x_2668_ = l_Lean_Meta_Closure_mkValueTypeClosureAux___lam__0(v_a_2597_, v_cache_2603_, v___x_2666_);
lean_dec_ref(v___x_2666_);
v_isSharedCheck_2675_ = !lean_is_exclusive(v___x_2668_);
if (v_isSharedCheck_2675_ == 0)
{
lean_object* v_unused_2676_; 
v_unused_2676_ = lean_ctor_get(v___x_2668_, 0);
lean_dec(v_unused_2676_);
v___x_2670_ = v___x_2668_;
v_isShared_2671_ = v_isSharedCheck_2675_;
goto v_resetjp_2669_;
}
else
{
lean_dec(v___x_2668_);
v___x_2670_ = lean_box(0);
v_isShared_2671_ = v_isSharedCheck_2675_;
goto v_resetjp_2669_;
}
v_resetjp_2669_:
{
lean_object* v___x_2673_; 
if (v_isShared_2671_ == 0)
{
lean_ctor_set(v___x_2670_, 0, v___x_2664_);
v___x_2673_ = v___x_2670_;
goto v_reusejp_2672_;
}
else
{
lean_object* v_reuseFailAlloc_2674_; 
v_reuseFailAlloc_2674_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2674_, 0, v___x_2664_);
v___x_2673_ = v_reuseFailAlloc_2674_;
goto v_reusejp_2672_;
}
v_reusejp_2672_:
{
return v___x_2673_;
}
}
}
}
}
else
{
lean_object* v_a_2680_; 
lean_dec(v_a_2659_);
lean_dec(v_a_2657_);
v_a_2680_ = lean_ctor_get(v___x_2660_, 0);
lean_inc(v_a_2680_);
lean_dec_ref_known(v___x_2660_, 1);
v_a_2650_ = v_a_2680_;
goto v___jp_2649_;
}
}
else
{
lean_object* v_a_2681_; 
lean_dec(v_a_2657_);
lean_dec_ref_known(v___x_2639_, 7);
v_a_2681_ = lean_ctor_get(v___x_2658_, 0);
lean_inc(v_a_2681_);
lean_dec_ref_known(v___x_2658_, 1);
v_a_2650_ = v_a_2681_;
goto v___jp_2649_;
}
}
else
{
lean_object* v_a_2682_; 
lean_dec_ref_known(v___x_2639_, 7);
lean_dec_ref(v_value_2593_);
v_a_2682_ = lean_ctor_get(v___x_2656_, 0);
lean_inc(v_a_2682_);
lean_dec_ref_known(v___x_2656_, 1);
v_a_2650_ = v_a_2682_;
goto v___jp_2649_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkValueTypeClosureAux___boxed(lean_object* v_type_2688_, lean_object* v_value_2689_, lean_object* v_a_2690_, lean_object* v_a_2691_, lean_object* v_a_2692_, lean_object* v_a_2693_, lean_object* v_a_2694_, lean_object* v_a_2695_, lean_object* v_a_2696_){
_start:
{
lean_object* v_res_2697_; 
v_res_2697_ = l_Lean_Meta_Closure_mkValueTypeClosureAux(v_type_2688_, v_value_2689_, v_a_2690_, v_a_2691_, v_a_2692_, v_a_2693_, v_a_2694_, v_a_2695_);
lean_dec(v_a_2695_);
lean_dec_ref(v_a_2694_);
lean_dec(v_a_2693_);
lean_dec_ref(v_a_2692_);
lean_dec(v_a_2691_);
lean_dec_ref(v_a_2690_);
return v_res_2697_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4___closed__0(void){
_start:
{
lean_object* v___x_2698_; 
v___x_2698_ = l_instMonadEIO___redArg();
return v___x_2698_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4(lean_object* v_msg_2701_, lean_object* v___y_2702_, lean_object* v___y_2703_, lean_object* v___y_2704_){
_start:
{
lean_object* v___x_2706_; lean_object* v___x_2707_; lean_object* v_toApplicative_2708_; lean_object* v___x_2710_; uint8_t v_isShared_2711_; uint8_t v_isSharedCheck_2749_; 
v___x_2706_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4___closed__0, &l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4___closed__0);
v___x_2707_ = l_StateRefT_x27_instMonad___redArg(v___x_2706_);
v_toApplicative_2708_ = lean_ctor_get(v___x_2707_, 0);
v_isSharedCheck_2749_ = !lean_is_exclusive(v___x_2707_);
if (v_isSharedCheck_2749_ == 0)
{
lean_object* v_unused_2750_; 
v_unused_2750_ = lean_ctor_get(v___x_2707_, 1);
lean_dec(v_unused_2750_);
v___x_2710_ = v___x_2707_;
v_isShared_2711_ = v_isSharedCheck_2749_;
goto v_resetjp_2709_;
}
else
{
lean_inc(v_toApplicative_2708_);
lean_dec(v___x_2707_);
v___x_2710_ = lean_box(0);
v_isShared_2711_ = v_isSharedCheck_2749_;
goto v_resetjp_2709_;
}
v_resetjp_2709_:
{
lean_object* v_toFunctor_2712_; lean_object* v_toSeq_2713_; lean_object* v_toSeqLeft_2714_; lean_object* v_toSeqRight_2715_; lean_object* v___x_2717_; uint8_t v_isShared_2718_; uint8_t v_isSharedCheck_2747_; 
v_toFunctor_2712_ = lean_ctor_get(v_toApplicative_2708_, 0);
v_toSeq_2713_ = lean_ctor_get(v_toApplicative_2708_, 2);
v_toSeqLeft_2714_ = lean_ctor_get(v_toApplicative_2708_, 3);
v_toSeqRight_2715_ = lean_ctor_get(v_toApplicative_2708_, 4);
v_isSharedCheck_2747_ = !lean_is_exclusive(v_toApplicative_2708_);
if (v_isSharedCheck_2747_ == 0)
{
lean_object* v_unused_2748_; 
v_unused_2748_ = lean_ctor_get(v_toApplicative_2708_, 1);
lean_dec(v_unused_2748_);
v___x_2717_ = v_toApplicative_2708_;
v_isShared_2718_ = v_isSharedCheck_2747_;
goto v_resetjp_2716_;
}
else
{
lean_inc(v_toSeqRight_2715_);
lean_inc(v_toSeqLeft_2714_);
lean_inc(v_toSeq_2713_);
lean_inc(v_toFunctor_2712_);
lean_dec(v_toApplicative_2708_);
v___x_2717_ = lean_box(0);
v_isShared_2718_ = v_isSharedCheck_2747_;
goto v_resetjp_2716_;
}
v_resetjp_2716_:
{
lean_object* v___f_2719_; lean_object* v___f_2720_; lean_object* v___f_2721_; lean_object* v___f_2722_; lean_object* v___x_2723_; lean_object* v___f_2724_; lean_object* v___f_2725_; lean_object* v___f_2726_; lean_object* v___x_2728_; 
v___f_2719_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4___closed__1));
v___f_2720_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4___closed__2));
lean_inc_ref(v_toFunctor_2712_);
v___f_2721_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2721_, 0, v_toFunctor_2712_);
v___f_2722_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2722_, 0, v_toFunctor_2712_);
v___x_2723_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2723_, 0, v___f_2721_);
lean_ctor_set(v___x_2723_, 1, v___f_2722_);
v___f_2724_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2724_, 0, v_toSeqRight_2715_);
v___f_2725_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2725_, 0, v_toSeqLeft_2714_);
v___f_2726_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2726_, 0, v_toSeq_2713_);
if (v_isShared_2718_ == 0)
{
lean_ctor_set(v___x_2717_, 4, v___f_2724_);
lean_ctor_set(v___x_2717_, 3, v___f_2725_);
lean_ctor_set(v___x_2717_, 2, v___f_2726_);
lean_ctor_set(v___x_2717_, 1, v___f_2719_);
lean_ctor_set(v___x_2717_, 0, v___x_2723_);
v___x_2728_ = v___x_2717_;
goto v_reusejp_2727_;
}
else
{
lean_object* v_reuseFailAlloc_2746_; 
v_reuseFailAlloc_2746_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2746_, 0, v___x_2723_);
lean_ctor_set(v_reuseFailAlloc_2746_, 1, v___f_2719_);
lean_ctor_set(v_reuseFailAlloc_2746_, 2, v___f_2726_);
lean_ctor_set(v_reuseFailAlloc_2746_, 3, v___f_2725_);
lean_ctor_set(v_reuseFailAlloc_2746_, 4, v___f_2724_);
v___x_2728_ = v_reuseFailAlloc_2746_;
goto v_reusejp_2727_;
}
v_reusejp_2727_:
{
lean_object* v___x_2730_; 
if (v_isShared_2711_ == 0)
{
lean_ctor_set(v___x_2710_, 1, v___f_2720_);
lean_ctor_set(v___x_2710_, 0, v___x_2728_);
v___x_2730_ = v___x_2710_;
goto v_reusejp_2729_;
}
else
{
lean_object* v_reuseFailAlloc_2745_; 
v_reuseFailAlloc_2745_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2745_, 0, v___x_2728_);
lean_ctor_set(v_reuseFailAlloc_2745_, 1, v___f_2720_);
v___x_2730_ = v_reuseFailAlloc_2745_;
goto v_reusejp_2729_;
}
v_reusejp_2729_:
{
lean_object* v___f_2731_; lean_object* v___f_2732_; lean_object* v___f_2733_; lean_object* v___f_2734_; lean_object* v___x_2735_; lean_object* v___x_2736_; lean_object* v___x_2737_; lean_object* v___x_2738_; lean_object* v___x_2739_; lean_object* v___x_2740_; lean_object* v___x_2741_; lean_object* v___x_2742_; lean_object* v___x_12469__overap_2743_; lean_object* v___x_2744_; 
lean_inc_ref_n(v___x_2730_, 6);
v___f_2731_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2731_, 0, v___x_2730_);
v___f_2732_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2732_, 0, v___x_2730_);
v___f_2733_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_2733_, 0, v___x_2730_);
v___f_2734_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_2734_, 0, v___x_2730_);
v___x_2735_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_2735_, 0, lean_box(0));
lean_closure_set(v___x_2735_, 1, lean_box(0));
lean_closure_set(v___x_2735_, 2, v___x_2730_);
v___x_2736_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2736_, 0, v___x_2735_);
lean_ctor_set(v___x_2736_, 1, v___f_2731_);
v___x_2737_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_2737_, 0, lean_box(0));
lean_closure_set(v___x_2737_, 1, lean_box(0));
lean_closure_set(v___x_2737_, 2, v___x_2730_);
v___x_2738_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2738_, 0, v___x_2736_);
lean_ctor_set(v___x_2738_, 1, v___x_2737_);
lean_ctor_set(v___x_2738_, 2, v___f_2732_);
lean_ctor_set(v___x_2738_, 3, v___f_2733_);
lean_ctor_set(v___x_2738_, 4, v___f_2734_);
v___x_2739_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_2739_, 0, lean_box(0));
lean_closure_set(v___x_2739_, 1, lean_box(0));
lean_closure_set(v___x_2739_, 2, v___x_2730_);
v___x_2740_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2740_, 0, v___x_2738_);
lean_ctor_set(v___x_2740_, 1, v___x_2739_);
v___x_2741_ = lean_box(0);
v___x_2742_ = l_instInhabitedOfMonad___redArg(v___x_2740_, v___x_2741_);
v___x_12469__overap_2743_ = lean_panic_fn_borrowed(v___x_2742_, v_msg_2701_);
lean_dec(v___x_2742_);
lean_inc(v___y_2704_);
lean_inc_ref(v___y_2703_);
v___x_2744_ = lean_apply_4(v___x_12469__overap_2743_, v___y_2702_, v___y_2703_, v___y_2704_, lean_box(0));
return v___x_2744_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4___boxed(lean_object* v_msg_2751_, lean_object* v___y_2752_, lean_object* v___y_2753_, lean_object* v___y_2754_, lean_object* v___y_2755_){
_start:
{
lean_object* v_res_2756_; 
v_res_2756_ = l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4(v_msg_2751_, v___y_2752_, v___y_2753_, v___y_2754_);
lean_dec(v___y_2754_);
lean_dec_ref(v___y_2753_);
return v_res_2756_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1_spec__2___redArg(lean_object* v_a_2757_, lean_object* v_x_2758_){
_start:
{
if (lean_obj_tag(v_x_2758_) == 0)
{
uint8_t v___x_2759_; 
v___x_2759_ = 0;
return v___x_2759_;
}
else
{
lean_object* v_key_2760_; lean_object* v_tail_2761_; uint8_t v___x_2762_; 
v_key_2760_ = lean_ctor_get(v_x_2758_, 0);
v_tail_2761_ = lean_ctor_get(v_x_2758_, 2);
v___x_2762_ = l_Lean_instBEqFVarId_beq(v_key_2760_, v_a_2757_);
if (v___x_2762_ == 0)
{
v_x_2758_ = v_tail_2761_;
goto _start;
}
else
{
return v___x_2762_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1_spec__2___redArg___boxed(lean_object* v_a_2764_, lean_object* v_x_2765_){
_start:
{
uint8_t v_res_2766_; lean_object* v_r_2767_; 
v_res_2766_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1_spec__2___redArg(v_a_2764_, v_x_2765_);
lean_dec(v_x_2765_);
lean_dec(v_a_2764_);
v_r_2767_ = lean_box(v_res_2766_);
return v_r_2767_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__4_spec__6_spec__11___redArg(lean_object* v_x_2768_, lean_object* v_x_2769_){
_start:
{
if (lean_obj_tag(v_x_2769_) == 0)
{
return v_x_2768_;
}
else
{
lean_object* v_key_2770_; lean_object* v_value_2771_; lean_object* v_tail_2772_; lean_object* v___x_2774_; uint8_t v_isShared_2775_; uint8_t v_isSharedCheck_2795_; 
v_key_2770_ = lean_ctor_get(v_x_2769_, 0);
v_value_2771_ = lean_ctor_get(v_x_2769_, 1);
v_tail_2772_ = lean_ctor_get(v_x_2769_, 2);
v_isSharedCheck_2795_ = !lean_is_exclusive(v_x_2769_);
if (v_isSharedCheck_2795_ == 0)
{
v___x_2774_ = v_x_2769_;
v_isShared_2775_ = v_isSharedCheck_2795_;
goto v_resetjp_2773_;
}
else
{
lean_inc(v_tail_2772_);
lean_inc(v_value_2771_);
lean_inc(v_key_2770_);
lean_dec(v_x_2769_);
v___x_2774_ = lean_box(0);
v_isShared_2775_ = v_isSharedCheck_2795_;
goto v_resetjp_2773_;
}
v_resetjp_2773_:
{
lean_object* v___x_2776_; uint64_t v___x_2777_; uint64_t v___x_2778_; uint64_t v___x_2779_; uint64_t v_fold_2780_; uint64_t v___x_2781_; uint64_t v___x_2782_; uint64_t v___x_2783_; size_t v___x_2784_; size_t v___x_2785_; size_t v___x_2786_; size_t v___x_2787_; size_t v___x_2788_; lean_object* v___x_2789_; lean_object* v___x_2791_; 
v___x_2776_ = lean_array_get_size(v_x_2768_);
v___x_2777_ = l_Lean_instHashableFVarId_hash(v_key_2770_);
v___x_2778_ = 32ULL;
v___x_2779_ = lean_uint64_shift_right(v___x_2777_, v___x_2778_);
v_fold_2780_ = lean_uint64_xor(v___x_2777_, v___x_2779_);
v___x_2781_ = 16ULL;
v___x_2782_ = lean_uint64_shift_right(v_fold_2780_, v___x_2781_);
v___x_2783_ = lean_uint64_xor(v_fold_2780_, v___x_2782_);
v___x_2784_ = lean_uint64_to_usize(v___x_2783_);
v___x_2785_ = lean_usize_of_nat(v___x_2776_);
v___x_2786_ = ((size_t)1ULL);
v___x_2787_ = lean_usize_sub(v___x_2785_, v___x_2786_);
v___x_2788_ = lean_usize_land(v___x_2784_, v___x_2787_);
v___x_2789_ = lean_array_uget_borrowed(v_x_2768_, v___x_2788_);
lean_inc(v___x_2789_);
if (v_isShared_2775_ == 0)
{
lean_ctor_set(v___x_2774_, 2, v___x_2789_);
v___x_2791_ = v___x_2774_;
goto v_reusejp_2790_;
}
else
{
lean_object* v_reuseFailAlloc_2794_; 
v_reuseFailAlloc_2794_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2794_, 0, v_key_2770_);
lean_ctor_set(v_reuseFailAlloc_2794_, 1, v_value_2771_);
lean_ctor_set(v_reuseFailAlloc_2794_, 2, v___x_2789_);
v___x_2791_ = v_reuseFailAlloc_2794_;
goto v_reusejp_2790_;
}
v_reusejp_2790_:
{
lean_object* v___x_2792_; 
v___x_2792_ = lean_array_uset(v_x_2768_, v___x_2788_, v___x_2791_);
v_x_2768_ = v___x_2792_;
v_x_2769_ = v_tail_2772_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__4_spec__6___redArg(lean_object* v_i_2796_, lean_object* v_source_2797_, lean_object* v_target_2798_){
_start:
{
lean_object* v___x_2799_; uint8_t v___x_2800_; 
v___x_2799_ = lean_array_get_size(v_source_2797_);
v___x_2800_ = lean_nat_dec_lt(v_i_2796_, v___x_2799_);
if (v___x_2800_ == 0)
{
lean_dec_ref(v_source_2797_);
lean_dec(v_i_2796_);
return v_target_2798_;
}
else
{
lean_object* v_es_2801_; lean_object* v___x_2802_; lean_object* v_source_2803_; lean_object* v_target_2804_; lean_object* v___x_2805_; lean_object* v___x_2806_; 
v_es_2801_ = lean_array_fget(v_source_2797_, v_i_2796_);
v___x_2802_ = lean_box(0);
v_source_2803_ = lean_array_fset(v_source_2797_, v_i_2796_, v___x_2802_);
v_target_2804_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__4_spec__6_spec__11___redArg(v_target_2798_, v_es_2801_);
v___x_2805_ = lean_unsigned_to_nat(1u);
v___x_2806_ = lean_nat_add(v_i_2796_, v___x_2805_);
lean_dec(v_i_2796_);
v_i_2796_ = v___x_2806_;
v_source_2797_ = v_source_2803_;
v_target_2798_ = v_target_2804_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__4___redArg(lean_object* v_data_2808_){
_start:
{
lean_object* v___x_2809_; lean_object* v___x_2810_; lean_object* v_nbuckets_2811_; lean_object* v___x_2812_; lean_object* v___x_2813_; lean_object* v___x_2814_; lean_object* v___x_2815_; lean_object* v___x_2816_; 
v___x_2809_ = lean_array_get_size(v_data_2808_);
v___x_2810_ = lean_unsigned_to_nat(2u);
v_nbuckets_2811_ = lean_nat_mul(v___x_2809_, v___x_2810_);
v___x_2812_ = lean_unsigned_to_nat(0u);
v___x_2813_ = lean_box(0);
v___x_2814_ = lean_mk_array(v_nbuckets_2811_, v___x_2813_);
v___x_2815_ = lean_array_propagate_mark(v_data_2808_, v___x_2814_);
v___x_2816_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__4_spec__6___redArg(v___x_2812_, v_data_2808_, v___x_2815_);
return v___x_2816_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2___redArg(lean_object* v_m_2817_, lean_object* v_a_2818_, lean_object* v_b_2819_){
_start:
{
lean_object* v_size_2820_; lean_object* v_buckets_2821_; lean_object* v___x_2822_; uint64_t v___x_2823_; uint64_t v___x_2824_; uint64_t v___x_2825_; uint64_t v_fold_2826_; uint64_t v___x_2827_; uint64_t v___x_2828_; uint64_t v___x_2829_; size_t v___x_2830_; size_t v___x_2831_; size_t v___x_2832_; size_t v___x_2833_; size_t v___x_2834_; lean_object* v_bkt_2835_; uint8_t v___x_2836_; 
v_size_2820_ = lean_ctor_get(v_m_2817_, 0);
v_buckets_2821_ = lean_ctor_get(v_m_2817_, 1);
v___x_2822_ = lean_array_get_size(v_buckets_2821_);
v___x_2823_ = l_Lean_instHashableFVarId_hash(v_a_2818_);
v___x_2824_ = 32ULL;
v___x_2825_ = lean_uint64_shift_right(v___x_2823_, v___x_2824_);
v_fold_2826_ = lean_uint64_xor(v___x_2823_, v___x_2825_);
v___x_2827_ = 16ULL;
v___x_2828_ = lean_uint64_shift_right(v_fold_2826_, v___x_2827_);
v___x_2829_ = lean_uint64_xor(v_fold_2826_, v___x_2828_);
v___x_2830_ = lean_uint64_to_usize(v___x_2829_);
v___x_2831_ = lean_usize_of_nat(v___x_2822_);
v___x_2832_ = ((size_t)1ULL);
v___x_2833_ = lean_usize_sub(v___x_2831_, v___x_2832_);
v___x_2834_ = lean_usize_land(v___x_2830_, v___x_2833_);
v_bkt_2835_ = lean_array_uget_borrowed(v_buckets_2821_, v___x_2834_);
v___x_2836_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1_spec__2___redArg(v_a_2818_, v_bkt_2835_);
if (v___x_2836_ == 0)
{
lean_object* v___x_2838_; uint8_t v_isShared_2839_; uint8_t v_isSharedCheck_2857_; 
lean_inc_ref(v_buckets_2821_);
lean_inc(v_size_2820_);
v_isSharedCheck_2857_ = !lean_is_exclusive(v_m_2817_);
if (v_isSharedCheck_2857_ == 0)
{
lean_object* v_unused_2858_; lean_object* v_unused_2859_; 
v_unused_2858_ = lean_ctor_get(v_m_2817_, 1);
lean_dec(v_unused_2858_);
v_unused_2859_ = lean_ctor_get(v_m_2817_, 0);
lean_dec(v_unused_2859_);
v___x_2838_ = v_m_2817_;
v_isShared_2839_ = v_isSharedCheck_2857_;
goto v_resetjp_2837_;
}
else
{
lean_dec(v_m_2817_);
v___x_2838_ = lean_box(0);
v_isShared_2839_ = v_isSharedCheck_2857_;
goto v_resetjp_2837_;
}
v_resetjp_2837_:
{
lean_object* v___x_2840_; lean_object* v_size_x27_2841_; lean_object* v___x_2842_; lean_object* v_buckets_x27_2843_; lean_object* v___x_2844_; lean_object* v___x_2845_; lean_object* v___x_2846_; lean_object* v___x_2847_; lean_object* v___x_2848_; uint8_t v___x_2849_; 
v___x_2840_ = lean_unsigned_to_nat(1u);
v_size_x27_2841_ = lean_nat_add(v_size_2820_, v___x_2840_);
lean_dec(v_size_2820_);
lean_inc(v_bkt_2835_);
v___x_2842_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2842_, 0, v_a_2818_);
lean_ctor_set(v___x_2842_, 1, v_b_2819_);
lean_ctor_set(v___x_2842_, 2, v_bkt_2835_);
v_buckets_x27_2843_ = lean_array_uset(v_buckets_2821_, v___x_2834_, v___x_2842_);
v___x_2844_ = lean_unsigned_to_nat(4u);
v___x_2845_ = lean_nat_mul(v_size_x27_2841_, v___x_2844_);
v___x_2846_ = lean_unsigned_to_nat(3u);
v___x_2847_ = lean_nat_div(v___x_2845_, v___x_2846_);
lean_dec(v___x_2845_);
v___x_2848_ = lean_array_get_size(v_buckets_x27_2843_);
v___x_2849_ = lean_nat_dec_le(v___x_2847_, v___x_2848_);
lean_dec(v___x_2847_);
if (v___x_2849_ == 0)
{
lean_object* v_val_2850_; lean_object* v___x_2852_; 
v_val_2850_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__4___redArg(v_buckets_x27_2843_);
if (v_isShared_2839_ == 0)
{
lean_ctor_set(v___x_2838_, 1, v_val_2850_);
lean_ctor_set(v___x_2838_, 0, v_size_x27_2841_);
v___x_2852_ = v___x_2838_;
goto v_reusejp_2851_;
}
else
{
lean_object* v_reuseFailAlloc_2853_; 
v_reuseFailAlloc_2853_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2853_, 0, v_size_x27_2841_);
lean_ctor_set(v_reuseFailAlloc_2853_, 1, v_val_2850_);
v___x_2852_ = v_reuseFailAlloc_2853_;
goto v_reusejp_2851_;
}
v_reusejp_2851_:
{
return v___x_2852_;
}
}
else
{
lean_object* v___x_2855_; 
if (v_isShared_2839_ == 0)
{
lean_ctor_set(v___x_2838_, 1, v_buckets_x27_2843_);
lean_ctor_set(v___x_2838_, 0, v_size_x27_2841_);
v___x_2855_ = v___x_2838_;
goto v_reusejp_2854_;
}
else
{
lean_object* v_reuseFailAlloc_2856_; 
v_reuseFailAlloc_2856_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2856_, 0, v_size_x27_2841_);
lean_ctor_set(v_reuseFailAlloc_2856_, 1, v_buckets_x27_2843_);
v___x_2855_ = v_reuseFailAlloc_2856_;
goto v_reusejp_2854_;
}
v_reusejp_2854_:
{
return v___x_2855_;
}
}
}
}
else
{
lean_dec(v_b_2819_);
lean_dec(v_a_2818_);
return v_m_2817_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1___redArg(lean_object* v_m_2860_, lean_object* v_a_2861_){
_start:
{
lean_object* v_buckets_2862_; lean_object* v___x_2863_; uint64_t v___x_2864_; uint64_t v___x_2865_; uint64_t v___x_2866_; uint64_t v_fold_2867_; uint64_t v___x_2868_; uint64_t v___x_2869_; uint64_t v___x_2870_; size_t v___x_2871_; size_t v___x_2872_; size_t v___x_2873_; size_t v___x_2874_; size_t v___x_2875_; lean_object* v___x_2876_; uint8_t v___x_2877_; 
v_buckets_2862_ = lean_ctor_get(v_m_2860_, 1);
v___x_2863_ = lean_array_get_size(v_buckets_2862_);
v___x_2864_ = l_Lean_instHashableFVarId_hash(v_a_2861_);
v___x_2865_ = 32ULL;
v___x_2866_ = lean_uint64_shift_right(v___x_2864_, v___x_2865_);
v_fold_2867_ = lean_uint64_xor(v___x_2864_, v___x_2866_);
v___x_2868_ = 16ULL;
v___x_2869_ = lean_uint64_shift_right(v_fold_2867_, v___x_2868_);
v___x_2870_ = lean_uint64_xor(v_fold_2867_, v___x_2869_);
v___x_2871_ = lean_uint64_to_usize(v___x_2870_);
v___x_2872_ = lean_usize_of_nat(v___x_2863_);
v___x_2873_ = ((size_t)1ULL);
v___x_2874_ = lean_usize_sub(v___x_2872_, v___x_2873_);
v___x_2875_ = lean_usize_land(v___x_2871_, v___x_2874_);
v___x_2876_ = lean_array_uget_borrowed(v_buckets_2862_, v___x_2875_);
v___x_2877_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1_spec__2___redArg(v_a_2861_, v___x_2876_);
return v___x_2877_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1___redArg___boxed(lean_object* v_m_2878_, lean_object* v_a_2879_){
_start:
{
uint8_t v_res_2880_; lean_object* v_r_2881_; 
v_res_2880_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1___redArg(v_m_2878_, v_a_2879_);
lean_dec(v_a_2879_);
lean_dec_ref(v_m_2878_);
v_r_2881_ = lean_box(v_res_2880_);
return v_r_2881_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__6_spec__9___redArg(lean_object* v_a_2882_, lean_object* v_x_2883_){
_start:
{
if (lean_obj_tag(v_x_2883_) == 0)
{
lean_object* v___x_2884_; 
v___x_2884_ = lean_box(0);
return v___x_2884_;
}
else
{
lean_object* v_key_2885_; lean_object* v_value_2886_; lean_object* v_tail_2887_; uint8_t v___x_2888_; 
v_key_2885_ = lean_ctor_get(v_x_2883_, 0);
v_value_2886_ = lean_ctor_get(v_x_2883_, 1);
v_tail_2887_ = lean_ctor_get(v_x_2883_, 2);
v___x_2888_ = lean_expr_eqv(v_key_2885_, v_a_2882_);
if (v___x_2888_ == 0)
{
v_x_2883_ = v_tail_2887_;
goto _start;
}
else
{
lean_object* v___x_2890_; 
lean_inc(v_value_2886_);
v___x_2890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2890_, 0, v_value_2886_);
return v___x_2890_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__6_spec__9___redArg___boxed(lean_object* v_a_2891_, lean_object* v_x_2892_){
_start:
{
lean_object* v_res_2893_; 
v_res_2893_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__6_spec__9___redArg(v_a_2891_, v_x_2892_);
lean_dec(v_x_2892_);
lean_dec_ref(v_a_2891_);
return v_res_2893_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__6___redArg(lean_object* v_m_2894_, lean_object* v_a_2895_){
_start:
{
lean_object* v_buckets_2896_; lean_object* v___x_2897_; uint64_t v___x_2898_; uint64_t v___x_2899_; uint64_t v___x_2900_; uint64_t v_fold_2901_; uint64_t v___x_2902_; uint64_t v___x_2903_; uint64_t v___x_2904_; size_t v___x_2905_; size_t v___x_2906_; size_t v___x_2907_; size_t v___x_2908_; size_t v___x_2909_; lean_object* v___x_2910_; lean_object* v___x_2911_; 
v_buckets_2896_ = lean_ctor_get(v_m_2894_, 1);
v___x_2897_ = lean_array_get_size(v_buckets_2896_);
v___x_2898_ = l_Lean_Expr_hash(v_a_2895_);
v___x_2899_ = 32ULL;
v___x_2900_ = lean_uint64_shift_right(v___x_2898_, v___x_2899_);
v_fold_2901_ = lean_uint64_xor(v___x_2898_, v___x_2900_);
v___x_2902_ = 16ULL;
v___x_2903_ = lean_uint64_shift_right(v_fold_2901_, v___x_2902_);
v___x_2904_ = lean_uint64_xor(v_fold_2901_, v___x_2903_);
v___x_2905_ = lean_uint64_to_usize(v___x_2904_);
v___x_2906_ = lean_usize_of_nat(v___x_2897_);
v___x_2907_ = ((size_t)1ULL);
v___x_2908_ = lean_usize_sub(v___x_2906_, v___x_2907_);
v___x_2909_ = lean_usize_land(v___x_2905_, v___x_2908_);
v___x_2910_ = lean_array_uget_borrowed(v_buckets_2896_, v___x_2909_);
v___x_2911_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__6_spec__9___redArg(v_a_2895_, v___x_2910_);
return v___x_2911_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__6___redArg___boxed(lean_object* v_m_2912_, lean_object* v_a_2913_){
_start:
{
lean_object* v_res_2914_; 
v_res_2914_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__6___redArg(v_m_2912_, v_a_2913_);
lean_dec_ref(v_a_2913_);
lean_dec_ref(v_m_2912_);
return v_res_2914_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__13___redArg(lean_object* v_a_2915_, lean_object* v_b_2916_, lean_object* v_x_2917_){
_start:
{
if (lean_obj_tag(v_x_2917_) == 0)
{
lean_dec(v_b_2916_);
lean_dec_ref(v_a_2915_);
return v_x_2917_;
}
else
{
lean_object* v_key_2918_; lean_object* v_value_2919_; lean_object* v_tail_2920_; lean_object* v___x_2922_; uint8_t v_isShared_2923_; uint8_t v_isSharedCheck_2932_; 
v_key_2918_ = lean_ctor_get(v_x_2917_, 0);
v_value_2919_ = lean_ctor_get(v_x_2917_, 1);
v_tail_2920_ = lean_ctor_get(v_x_2917_, 2);
v_isSharedCheck_2932_ = !lean_is_exclusive(v_x_2917_);
if (v_isSharedCheck_2932_ == 0)
{
v___x_2922_ = v_x_2917_;
v_isShared_2923_ = v_isSharedCheck_2932_;
goto v_resetjp_2921_;
}
else
{
lean_inc(v_tail_2920_);
lean_inc(v_value_2919_);
lean_inc(v_key_2918_);
lean_dec(v_x_2917_);
v___x_2922_ = lean_box(0);
v_isShared_2923_ = v_isSharedCheck_2932_;
goto v_resetjp_2921_;
}
v_resetjp_2921_:
{
uint8_t v___x_2924_; 
v___x_2924_ = lean_expr_eqv(v_key_2918_, v_a_2915_);
if (v___x_2924_ == 0)
{
lean_object* v___x_2925_; lean_object* v___x_2927_; 
v___x_2925_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__13___redArg(v_a_2915_, v_b_2916_, v_tail_2920_);
if (v_isShared_2923_ == 0)
{
lean_ctor_set(v___x_2922_, 2, v___x_2925_);
v___x_2927_ = v___x_2922_;
goto v_reusejp_2926_;
}
else
{
lean_object* v_reuseFailAlloc_2928_; 
v_reuseFailAlloc_2928_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2928_, 0, v_key_2918_);
lean_ctor_set(v_reuseFailAlloc_2928_, 1, v_value_2919_);
lean_ctor_set(v_reuseFailAlloc_2928_, 2, v___x_2925_);
v___x_2927_ = v_reuseFailAlloc_2928_;
goto v_reusejp_2926_;
}
v_reusejp_2926_:
{
return v___x_2927_;
}
}
else
{
lean_object* v___x_2930_; 
lean_dec(v_value_2919_);
lean_dec(v_key_2918_);
if (v_isShared_2923_ == 0)
{
lean_ctor_set(v___x_2922_, 1, v_b_2916_);
lean_ctor_set(v___x_2922_, 0, v_a_2915_);
v___x_2930_ = v___x_2922_;
goto v_reusejp_2929_;
}
else
{
lean_object* v_reuseFailAlloc_2931_; 
v_reuseFailAlloc_2931_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2931_, 0, v_a_2915_);
lean_ctor_set(v_reuseFailAlloc_2931_, 1, v_b_2916_);
lean_ctor_set(v_reuseFailAlloc_2931_, 2, v_tail_2920_);
v___x_2930_ = v_reuseFailAlloc_2931_;
goto v_reusejp_2929_;
}
v_reusejp_2929_:
{
return v___x_2930_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__12_spec__17_spec__18___redArg(lean_object* v_x_2933_, lean_object* v_x_2934_){
_start:
{
if (lean_obj_tag(v_x_2934_) == 0)
{
return v_x_2933_;
}
else
{
lean_object* v_key_2935_; lean_object* v_value_2936_; lean_object* v_tail_2937_; lean_object* v___x_2939_; uint8_t v_isShared_2940_; uint8_t v_isSharedCheck_2960_; 
v_key_2935_ = lean_ctor_get(v_x_2934_, 0);
v_value_2936_ = lean_ctor_get(v_x_2934_, 1);
v_tail_2937_ = lean_ctor_get(v_x_2934_, 2);
v_isSharedCheck_2960_ = !lean_is_exclusive(v_x_2934_);
if (v_isSharedCheck_2960_ == 0)
{
v___x_2939_ = v_x_2934_;
v_isShared_2940_ = v_isSharedCheck_2960_;
goto v_resetjp_2938_;
}
else
{
lean_inc(v_tail_2937_);
lean_inc(v_value_2936_);
lean_inc(v_key_2935_);
lean_dec(v_x_2934_);
v___x_2939_ = lean_box(0);
v_isShared_2940_ = v_isSharedCheck_2960_;
goto v_resetjp_2938_;
}
v_resetjp_2938_:
{
lean_object* v___x_2941_; uint64_t v___x_2942_; uint64_t v___x_2943_; uint64_t v___x_2944_; uint64_t v_fold_2945_; uint64_t v___x_2946_; uint64_t v___x_2947_; uint64_t v___x_2948_; size_t v___x_2949_; size_t v___x_2950_; size_t v___x_2951_; size_t v___x_2952_; size_t v___x_2953_; lean_object* v___x_2954_; lean_object* v___x_2956_; 
v___x_2941_ = lean_array_get_size(v_x_2933_);
v___x_2942_ = l_Lean_Expr_hash(v_key_2935_);
v___x_2943_ = 32ULL;
v___x_2944_ = lean_uint64_shift_right(v___x_2942_, v___x_2943_);
v_fold_2945_ = lean_uint64_xor(v___x_2942_, v___x_2944_);
v___x_2946_ = 16ULL;
v___x_2947_ = lean_uint64_shift_right(v_fold_2945_, v___x_2946_);
v___x_2948_ = lean_uint64_xor(v_fold_2945_, v___x_2947_);
v___x_2949_ = lean_uint64_to_usize(v___x_2948_);
v___x_2950_ = lean_usize_of_nat(v___x_2941_);
v___x_2951_ = ((size_t)1ULL);
v___x_2952_ = lean_usize_sub(v___x_2950_, v___x_2951_);
v___x_2953_ = lean_usize_land(v___x_2949_, v___x_2952_);
v___x_2954_ = lean_array_uget_borrowed(v_x_2933_, v___x_2953_);
lean_inc(v___x_2954_);
if (v_isShared_2940_ == 0)
{
lean_ctor_set(v___x_2939_, 2, v___x_2954_);
v___x_2956_ = v___x_2939_;
goto v_reusejp_2955_;
}
else
{
lean_object* v_reuseFailAlloc_2959_; 
v_reuseFailAlloc_2959_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2959_, 0, v_key_2935_);
lean_ctor_set(v_reuseFailAlloc_2959_, 1, v_value_2936_);
lean_ctor_set(v_reuseFailAlloc_2959_, 2, v___x_2954_);
v___x_2956_ = v_reuseFailAlloc_2959_;
goto v_reusejp_2955_;
}
v_reusejp_2955_:
{
lean_object* v___x_2957_; 
v___x_2957_ = lean_array_uset(v_x_2933_, v___x_2953_, v___x_2956_);
v_x_2933_ = v___x_2957_;
v_x_2934_ = v_tail_2937_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__12_spec__17___redArg(lean_object* v_i_2961_, lean_object* v_source_2962_, lean_object* v_target_2963_){
_start:
{
lean_object* v___x_2964_; uint8_t v___x_2965_; 
v___x_2964_ = lean_array_get_size(v_source_2962_);
v___x_2965_ = lean_nat_dec_lt(v_i_2961_, v___x_2964_);
if (v___x_2965_ == 0)
{
lean_dec_ref(v_source_2962_);
lean_dec(v_i_2961_);
return v_target_2963_;
}
else
{
lean_object* v_es_2966_; lean_object* v___x_2967_; lean_object* v_source_2968_; lean_object* v_target_2969_; lean_object* v___x_2970_; lean_object* v___x_2971_; 
v_es_2966_ = lean_array_fget(v_source_2962_, v_i_2961_);
v___x_2967_ = lean_box(0);
v_source_2968_ = lean_array_fset(v_source_2962_, v_i_2961_, v___x_2967_);
v_target_2969_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__12_spec__17_spec__18___redArg(v_target_2963_, v_es_2966_);
v___x_2970_ = lean_unsigned_to_nat(1u);
v___x_2971_ = lean_nat_add(v_i_2961_, v___x_2970_);
lean_dec(v_i_2961_);
v_i_2961_ = v___x_2971_;
v_source_2962_ = v_source_2968_;
v_target_2963_ = v_target_2969_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__12___redArg(lean_object* v_data_2973_){
_start:
{
lean_object* v___x_2974_; lean_object* v___x_2975_; lean_object* v_nbuckets_2976_; lean_object* v___x_2977_; lean_object* v___x_2978_; lean_object* v___x_2979_; lean_object* v___x_2980_; lean_object* v___x_2981_; 
v___x_2974_ = lean_array_get_size(v_data_2973_);
v___x_2975_ = lean_unsigned_to_nat(2u);
v_nbuckets_2976_ = lean_nat_mul(v___x_2974_, v___x_2975_);
v___x_2977_ = lean_unsigned_to_nat(0u);
v___x_2978_ = lean_box(0);
v___x_2979_ = lean_mk_array(v_nbuckets_2976_, v___x_2978_);
v___x_2980_ = lean_array_propagate_mark(v_data_2973_, v___x_2979_);
v___x_2981_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__12_spec__17___redArg(v___x_2977_, v_data_2973_, v___x_2980_);
return v___x_2981_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__11___redArg(lean_object* v_a_2982_, lean_object* v_x_2983_){
_start:
{
if (lean_obj_tag(v_x_2983_) == 0)
{
uint8_t v___x_2984_; 
v___x_2984_ = 0;
return v___x_2984_;
}
else
{
lean_object* v_key_2985_; lean_object* v_tail_2986_; uint8_t v___x_2987_; 
v_key_2985_ = lean_ctor_get(v_x_2983_, 0);
v_tail_2986_ = lean_ctor_get(v_x_2983_, 2);
v___x_2987_ = lean_expr_eqv(v_key_2985_, v_a_2982_);
if (v___x_2987_ == 0)
{
v_x_2983_ = v_tail_2986_;
goto _start;
}
else
{
return v___x_2987_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__11___redArg___boxed(lean_object* v_a_2989_, lean_object* v_x_2990_){
_start:
{
uint8_t v_res_2991_; lean_object* v_r_2992_; 
v_res_2991_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__11___redArg(v_a_2989_, v_x_2990_);
lean_dec(v_x_2990_);
lean_dec_ref(v_a_2989_);
v_r_2992_ = lean_box(v_res_2991_);
return v_r_2992_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7___redArg(lean_object* v_m_2993_, lean_object* v_a_2994_, lean_object* v_b_2995_){
_start:
{
lean_object* v_size_2996_; lean_object* v_buckets_2997_; lean_object* v___x_2999_; uint8_t v_isShared_3000_; uint8_t v_isSharedCheck_3040_; 
v_size_2996_ = lean_ctor_get(v_m_2993_, 0);
v_buckets_2997_ = lean_ctor_get(v_m_2993_, 1);
v_isSharedCheck_3040_ = !lean_is_exclusive(v_m_2993_);
if (v_isSharedCheck_3040_ == 0)
{
v___x_2999_ = v_m_2993_;
v_isShared_3000_ = v_isSharedCheck_3040_;
goto v_resetjp_2998_;
}
else
{
lean_inc(v_buckets_2997_);
lean_inc(v_size_2996_);
lean_dec(v_m_2993_);
v___x_2999_ = lean_box(0);
v_isShared_3000_ = v_isSharedCheck_3040_;
goto v_resetjp_2998_;
}
v_resetjp_2998_:
{
lean_object* v___x_3001_; uint64_t v___x_3002_; uint64_t v___x_3003_; uint64_t v___x_3004_; uint64_t v_fold_3005_; uint64_t v___x_3006_; uint64_t v___x_3007_; uint64_t v___x_3008_; size_t v___x_3009_; size_t v___x_3010_; size_t v___x_3011_; size_t v___x_3012_; size_t v___x_3013_; lean_object* v_bkt_3014_; uint8_t v___x_3015_; 
v___x_3001_ = lean_array_get_size(v_buckets_2997_);
v___x_3002_ = l_Lean_Expr_hash(v_a_2994_);
v___x_3003_ = 32ULL;
v___x_3004_ = lean_uint64_shift_right(v___x_3002_, v___x_3003_);
v_fold_3005_ = lean_uint64_xor(v___x_3002_, v___x_3004_);
v___x_3006_ = 16ULL;
v___x_3007_ = lean_uint64_shift_right(v_fold_3005_, v___x_3006_);
v___x_3008_ = lean_uint64_xor(v_fold_3005_, v___x_3007_);
v___x_3009_ = lean_uint64_to_usize(v___x_3008_);
v___x_3010_ = lean_usize_of_nat(v___x_3001_);
v___x_3011_ = ((size_t)1ULL);
v___x_3012_ = lean_usize_sub(v___x_3010_, v___x_3011_);
v___x_3013_ = lean_usize_land(v___x_3009_, v___x_3012_);
v_bkt_3014_ = lean_array_uget_borrowed(v_buckets_2997_, v___x_3013_);
v___x_3015_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__11___redArg(v_a_2994_, v_bkt_3014_);
if (v___x_3015_ == 0)
{
lean_object* v___x_3016_; lean_object* v_size_x27_3017_; lean_object* v___x_3018_; lean_object* v_buckets_x27_3019_; lean_object* v___x_3020_; lean_object* v___x_3021_; lean_object* v___x_3022_; lean_object* v___x_3023_; lean_object* v___x_3024_; uint8_t v___x_3025_; 
v___x_3016_ = lean_unsigned_to_nat(1u);
v_size_x27_3017_ = lean_nat_add(v_size_2996_, v___x_3016_);
lean_dec(v_size_2996_);
lean_inc(v_bkt_3014_);
v___x_3018_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3018_, 0, v_a_2994_);
lean_ctor_set(v___x_3018_, 1, v_b_2995_);
lean_ctor_set(v___x_3018_, 2, v_bkt_3014_);
v_buckets_x27_3019_ = lean_array_uset(v_buckets_2997_, v___x_3013_, v___x_3018_);
v___x_3020_ = lean_unsigned_to_nat(4u);
v___x_3021_ = lean_nat_mul(v_size_x27_3017_, v___x_3020_);
v___x_3022_ = lean_unsigned_to_nat(3u);
v___x_3023_ = lean_nat_div(v___x_3021_, v___x_3022_);
lean_dec(v___x_3021_);
v___x_3024_ = lean_array_get_size(v_buckets_x27_3019_);
v___x_3025_ = lean_nat_dec_le(v___x_3023_, v___x_3024_);
lean_dec(v___x_3023_);
if (v___x_3025_ == 0)
{
lean_object* v_val_3026_; lean_object* v___x_3028_; 
v_val_3026_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__12___redArg(v_buckets_x27_3019_);
if (v_isShared_3000_ == 0)
{
lean_ctor_set(v___x_2999_, 1, v_val_3026_);
lean_ctor_set(v___x_2999_, 0, v_size_x27_3017_);
v___x_3028_ = v___x_2999_;
goto v_reusejp_3027_;
}
else
{
lean_object* v_reuseFailAlloc_3029_; 
v_reuseFailAlloc_3029_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3029_, 0, v_size_x27_3017_);
lean_ctor_set(v_reuseFailAlloc_3029_, 1, v_val_3026_);
v___x_3028_ = v_reuseFailAlloc_3029_;
goto v_reusejp_3027_;
}
v_reusejp_3027_:
{
return v___x_3028_;
}
}
else
{
lean_object* v___x_3031_; 
if (v_isShared_3000_ == 0)
{
lean_ctor_set(v___x_2999_, 1, v_buckets_x27_3019_);
lean_ctor_set(v___x_2999_, 0, v_size_x27_3017_);
v___x_3031_ = v___x_2999_;
goto v_reusejp_3030_;
}
else
{
lean_object* v_reuseFailAlloc_3032_; 
v_reuseFailAlloc_3032_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3032_, 0, v_size_x27_3017_);
lean_ctor_set(v_reuseFailAlloc_3032_, 1, v_buckets_x27_3019_);
v___x_3031_ = v_reuseFailAlloc_3032_;
goto v_reusejp_3030_;
}
v_reusejp_3030_:
{
return v___x_3031_;
}
}
}
else
{
lean_object* v___x_3033_; lean_object* v_buckets_x27_3034_; lean_object* v___x_3035_; lean_object* v___x_3036_; lean_object* v___x_3038_; 
lean_inc(v_bkt_3014_);
v___x_3033_ = lean_box(0);
v_buckets_x27_3034_ = lean_array_uset(v_buckets_2997_, v___x_3013_, v___x_3033_);
v___x_3035_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__13___redArg(v_a_2994_, v_b_2995_, v_bkt_3014_);
v___x_3036_ = lean_array_uset(v_buckets_x27_3034_, v___x_3013_, v___x_3035_);
if (v_isShared_3000_ == 0)
{
lean_ctor_set(v___x_2999_, 1, v___x_3036_);
v___x_3038_ = v___x_2999_;
goto v_reusejp_3037_;
}
else
{
lean_object* v_reuseFailAlloc_3039_; 
v_reuseFailAlloc_3039_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3039_, 0, v_size_2996_);
lean_ctor_set(v_reuseFailAlloc_3039_, 1, v___x_3036_);
v___x_3038_ = v_reuseFailAlloc_3039_;
goto v_reusejp_3037_;
}
v_reusejp_3037_:
{
return v___x_3038_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3(lean_object* v_g_3041_, lean_object* v_e_3042_, lean_object* v_a_3043_, lean_object* v___y_3044_, lean_object* v___y_3045_, lean_object* v___y_3046_){
_start:
{
lean_object* v_a_3049_; lean_object* v_fst_3050_; lean_object* v___y_3056_; lean_object* v___x_3059_; lean_object* v___x_3060_; 
v___x_3059_ = lean_st_ref_get(v_a_3043_);
v___x_3060_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__6___redArg(v___x_3059_, v_e_3042_);
lean_dec(v___x_3059_);
if (lean_obj_tag(v___x_3060_) == 0)
{
lean_object* v___x_3061_; 
lean_inc_ref(v_g_3041_);
lean_inc(v___y_3046_);
lean_inc_ref(v___y_3045_);
lean_inc_ref(v_e_3042_);
v___x_3061_ = lean_apply_5(v_g_3041_, v_e_3042_, v___y_3044_, v___y_3045_, v___y_3046_, lean_box(0));
if (lean_obj_tag(v___x_3061_) == 0)
{
lean_object* v_a_3062_; lean_object* v_fst_3063_; lean_object* v_snd_3064_; lean_object* v___x_3066_; uint8_t v_isShared_3067_; uint8_t v_isSharedCheck_3109_; 
v_a_3062_ = lean_ctor_get(v___x_3061_, 0);
lean_inc(v_a_3062_);
lean_dec_ref_known(v___x_3061_, 1);
v_fst_3063_ = lean_ctor_get(v_a_3062_, 0);
v_snd_3064_ = lean_ctor_get(v_a_3062_, 1);
v_isSharedCheck_3109_ = !lean_is_exclusive(v_a_3062_);
if (v_isSharedCheck_3109_ == 0)
{
v___x_3066_ = v_a_3062_;
v_isShared_3067_ = v_isSharedCheck_3109_;
goto v_resetjp_3065_;
}
else
{
lean_inc(v_snd_3064_);
lean_inc(v_fst_3063_);
lean_dec(v_a_3062_);
v___x_3066_ = lean_box(0);
v_isShared_3067_ = v_isSharedCheck_3109_;
goto v_resetjp_3065_;
}
v_resetjp_3065_:
{
lean_object* v_d_3069_; lean_object* v_b_3070_; lean_object* v___y_3071_; uint8_t v___x_3076_; 
v___x_3076_ = lean_unbox(v_fst_3063_);
lean_dec(v_fst_3063_);
if (v___x_3076_ == 0)
{
lean_object* v___x_3077_; lean_object* v___x_3079_; 
lean_dec_ref(v_g_3041_);
v___x_3077_ = lean_box(0);
if (v_isShared_3067_ == 0)
{
lean_ctor_set(v___x_3066_, 0, v___x_3077_);
v___x_3079_ = v___x_3066_;
goto v_reusejp_3078_;
}
else
{
lean_object* v_reuseFailAlloc_3080_; 
v_reuseFailAlloc_3080_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3080_, 0, v___x_3077_);
lean_ctor_set(v_reuseFailAlloc_3080_, 1, v_snd_3064_);
v___x_3079_ = v_reuseFailAlloc_3080_;
goto v_reusejp_3078_;
}
v_reusejp_3078_:
{
v_a_3049_ = v___x_3079_;
v_fst_3050_ = v___x_3077_;
goto v___jp_3048_;
}
}
else
{
switch(lean_obj_tag(v_e_3042_))
{
case 7:
{
lean_object* v_binderType_3081_; lean_object* v_body_3082_; 
lean_del_object(v___x_3066_);
v_binderType_3081_ = lean_ctor_get(v_e_3042_, 1);
v_body_3082_ = lean_ctor_get(v_e_3042_, 2);
lean_inc_ref(v_body_3082_);
lean_inc_ref(v_binderType_3081_);
v_d_3069_ = v_binderType_3081_;
v_b_3070_ = v_body_3082_;
v___y_3071_ = v_a_3043_;
goto v___jp_3068_;
}
case 6:
{
lean_object* v_binderType_3083_; lean_object* v_body_3084_; 
lean_del_object(v___x_3066_);
v_binderType_3083_ = lean_ctor_get(v_e_3042_, 1);
v_body_3084_ = lean_ctor_get(v_e_3042_, 2);
lean_inc_ref(v_body_3084_);
lean_inc_ref(v_binderType_3083_);
v_d_3069_ = v_binderType_3083_;
v_b_3070_ = v_body_3084_;
v___y_3071_ = v_a_3043_;
goto v___jp_3068_;
}
case 8:
{
lean_object* v_type_3085_; lean_object* v_value_3086_; lean_object* v_body_3087_; lean_object* v___x_3088_; 
lean_del_object(v___x_3066_);
v_type_3085_ = lean_ctor_get(v_e_3042_, 1);
v_value_3086_ = lean_ctor_get(v_e_3042_, 2);
v_body_3087_ = lean_ctor_get(v_e_3042_, 3);
lean_inc_ref(v_type_3085_);
lean_inc_ref(v_g_3041_);
v___x_3088_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3(v_g_3041_, v_type_3085_, v_a_3043_, v_snd_3064_, v___y_3045_, v___y_3046_);
if (lean_obj_tag(v___x_3088_) == 0)
{
lean_object* v_a_3089_; lean_object* v_snd_3090_; lean_object* v___x_3091_; 
v_a_3089_ = lean_ctor_get(v___x_3088_, 0);
lean_inc(v_a_3089_);
lean_dec_ref_known(v___x_3088_, 1);
v_snd_3090_ = lean_ctor_get(v_a_3089_, 1);
lean_inc(v_snd_3090_);
lean_dec(v_a_3089_);
lean_inc_ref(v_value_3086_);
lean_inc_ref(v_g_3041_);
v___x_3091_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3(v_g_3041_, v_value_3086_, v_a_3043_, v_snd_3090_, v___y_3045_, v___y_3046_);
if (lean_obj_tag(v___x_3091_) == 0)
{
lean_object* v_a_3092_; lean_object* v_snd_3093_; lean_object* v___x_3094_; 
v_a_3092_ = lean_ctor_get(v___x_3091_, 0);
lean_inc(v_a_3092_);
lean_dec_ref_known(v___x_3091_, 1);
v_snd_3093_ = lean_ctor_get(v_a_3092_, 1);
lean_inc(v_snd_3093_);
lean_dec(v_a_3092_);
lean_inc_ref(v_body_3087_);
v___x_3094_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3(v_g_3041_, v_body_3087_, v_a_3043_, v_snd_3093_, v___y_3045_, v___y_3046_);
v___y_3056_ = v___x_3094_;
goto v___jp_3055_;
}
else
{
lean_dec_ref(v_g_3041_);
v___y_3056_ = v___x_3091_;
goto v___jp_3055_;
}
}
else
{
lean_dec_ref(v_g_3041_);
v___y_3056_ = v___x_3088_;
goto v___jp_3055_;
}
}
case 5:
{
lean_object* v_fn_3095_; lean_object* v_arg_3096_; lean_object* v___x_3097_; 
lean_del_object(v___x_3066_);
v_fn_3095_ = lean_ctor_get(v_e_3042_, 0);
v_arg_3096_ = lean_ctor_get(v_e_3042_, 1);
lean_inc_ref(v_fn_3095_);
lean_inc_ref(v_g_3041_);
v___x_3097_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3(v_g_3041_, v_fn_3095_, v_a_3043_, v_snd_3064_, v___y_3045_, v___y_3046_);
if (lean_obj_tag(v___x_3097_) == 0)
{
lean_object* v_a_3098_; lean_object* v_snd_3099_; lean_object* v___x_3100_; 
v_a_3098_ = lean_ctor_get(v___x_3097_, 0);
lean_inc(v_a_3098_);
lean_dec_ref_known(v___x_3097_, 1);
v_snd_3099_ = lean_ctor_get(v_a_3098_, 1);
lean_inc(v_snd_3099_);
lean_dec(v_a_3098_);
lean_inc_ref(v_arg_3096_);
v___x_3100_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3(v_g_3041_, v_arg_3096_, v_a_3043_, v_snd_3099_, v___y_3045_, v___y_3046_);
v___y_3056_ = v___x_3100_;
goto v___jp_3055_;
}
else
{
lean_dec_ref(v_g_3041_);
v___y_3056_ = v___x_3097_;
goto v___jp_3055_;
}
}
case 10:
{
lean_object* v_expr_3101_; lean_object* v___x_3102_; 
lean_del_object(v___x_3066_);
v_expr_3101_ = lean_ctor_get(v_e_3042_, 1);
lean_inc_ref(v_expr_3101_);
v___x_3102_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3(v_g_3041_, v_expr_3101_, v_a_3043_, v_snd_3064_, v___y_3045_, v___y_3046_);
v___y_3056_ = v___x_3102_;
goto v___jp_3055_;
}
case 11:
{
lean_object* v_struct_3103_; lean_object* v___x_3104_; 
lean_del_object(v___x_3066_);
v_struct_3103_ = lean_ctor_get(v_e_3042_, 2);
lean_inc_ref(v_struct_3103_);
v___x_3104_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3(v_g_3041_, v_struct_3103_, v_a_3043_, v_snd_3064_, v___y_3045_, v___y_3046_);
v___y_3056_ = v___x_3104_;
goto v___jp_3055_;
}
default: 
{
lean_object* v___x_3105_; lean_object* v___x_3107_; 
lean_dec_ref(v_g_3041_);
v___x_3105_ = lean_box(0);
if (v_isShared_3067_ == 0)
{
lean_ctor_set(v___x_3066_, 0, v___x_3105_);
v___x_3107_ = v___x_3066_;
goto v_reusejp_3106_;
}
else
{
lean_object* v_reuseFailAlloc_3108_; 
v_reuseFailAlloc_3108_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3108_, 0, v___x_3105_);
lean_ctor_set(v_reuseFailAlloc_3108_, 1, v_snd_3064_);
v___x_3107_ = v_reuseFailAlloc_3108_;
goto v_reusejp_3106_;
}
v_reusejp_3106_:
{
v_a_3049_ = v___x_3107_;
v_fst_3050_ = v___x_3105_;
goto v___jp_3048_;
}
}
}
}
v___jp_3068_:
{
lean_object* v___x_3072_; 
lean_inc_ref(v_g_3041_);
v___x_3072_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3(v_g_3041_, v_d_3069_, v___y_3071_, v_snd_3064_, v___y_3045_, v___y_3046_);
if (lean_obj_tag(v___x_3072_) == 0)
{
lean_object* v_a_3073_; lean_object* v_snd_3074_; lean_object* v___x_3075_; 
v_a_3073_ = lean_ctor_get(v___x_3072_, 0);
lean_inc(v_a_3073_);
lean_dec_ref_known(v___x_3072_, 1);
v_snd_3074_ = lean_ctor_get(v_a_3073_, 1);
lean_inc(v_snd_3074_);
lean_dec(v_a_3073_);
v___x_3075_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3(v_g_3041_, v_b_3070_, v___y_3071_, v_snd_3074_, v___y_3045_, v___y_3046_);
v___y_3056_ = v___x_3075_;
goto v___jp_3055_;
}
else
{
lean_dec_ref(v_b_3070_);
lean_dec_ref(v_g_3041_);
v___y_3056_ = v___x_3072_;
goto v___jp_3055_;
}
}
}
}
else
{
lean_object* v_a_3110_; lean_object* v___x_3112_; uint8_t v_isShared_3113_; uint8_t v_isSharedCheck_3117_; 
lean_dec_ref(v_e_3042_);
lean_dec_ref(v_g_3041_);
v_a_3110_ = lean_ctor_get(v___x_3061_, 0);
v_isSharedCheck_3117_ = !lean_is_exclusive(v___x_3061_);
if (v_isSharedCheck_3117_ == 0)
{
v___x_3112_ = v___x_3061_;
v_isShared_3113_ = v_isSharedCheck_3117_;
goto v_resetjp_3111_;
}
else
{
lean_inc(v_a_3110_);
lean_dec(v___x_3061_);
v___x_3112_ = lean_box(0);
v_isShared_3113_ = v_isSharedCheck_3117_;
goto v_resetjp_3111_;
}
v_resetjp_3111_:
{
lean_object* v___x_3115_; 
if (v_isShared_3113_ == 0)
{
v___x_3115_ = v___x_3112_;
goto v_reusejp_3114_;
}
else
{
lean_object* v_reuseFailAlloc_3116_; 
v_reuseFailAlloc_3116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3116_, 0, v_a_3110_);
v___x_3115_ = v_reuseFailAlloc_3116_;
goto v_reusejp_3114_;
}
v_reusejp_3114_:
{
return v___x_3115_;
}
}
}
}
else
{
lean_object* v_val_3118_; lean_object* v___x_3120_; uint8_t v_isShared_3121_; uint8_t v_isSharedCheck_3126_; 
lean_dec_ref(v_e_3042_);
lean_dec_ref(v_g_3041_);
v_val_3118_ = lean_ctor_get(v___x_3060_, 0);
v_isSharedCheck_3126_ = !lean_is_exclusive(v___x_3060_);
if (v_isSharedCheck_3126_ == 0)
{
v___x_3120_ = v___x_3060_;
v_isShared_3121_ = v_isSharedCheck_3126_;
goto v_resetjp_3119_;
}
else
{
lean_inc(v_val_3118_);
lean_dec(v___x_3060_);
v___x_3120_ = lean_box(0);
v_isShared_3121_ = v_isSharedCheck_3126_;
goto v_resetjp_3119_;
}
v_resetjp_3119_:
{
lean_object* v___x_3122_; lean_object* v___x_3124_; 
v___x_3122_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3122_, 0, v_val_3118_);
lean_ctor_set(v___x_3122_, 1, v___y_3044_);
if (v_isShared_3121_ == 0)
{
lean_ctor_set_tag(v___x_3120_, 0);
lean_ctor_set(v___x_3120_, 0, v___x_3122_);
v___x_3124_ = v___x_3120_;
goto v_reusejp_3123_;
}
else
{
lean_object* v_reuseFailAlloc_3125_; 
v_reuseFailAlloc_3125_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3125_, 0, v___x_3122_);
v___x_3124_ = v_reuseFailAlloc_3125_;
goto v_reusejp_3123_;
}
v_reusejp_3123_:
{
return v___x_3124_;
}
}
}
v___jp_3048_:
{
lean_object* v___x_3051_; lean_object* v___x_3052_; lean_object* v___x_3053_; lean_object* v___x_3054_; 
v___x_3051_ = lean_st_ref_take(v_a_3043_);
v___x_3052_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7___redArg(v___x_3051_, v_e_3042_, v_fst_3050_);
v___x_3053_ = lean_st_ref_put(v_a_3043_, v___x_3052_);
v___x_3054_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3054_, 0, v_a_3049_);
return v___x_3054_;
}
v___jp_3055_:
{
if (lean_obj_tag(v___y_3056_) == 0)
{
lean_object* v_a_3057_; lean_object* v_fst_3058_; 
v_a_3057_ = lean_ctor_get(v___y_3056_, 0);
lean_inc(v_a_3057_);
lean_dec_ref_known(v___y_3056_, 1);
v_fst_3058_ = lean_ctor_get(v_a_3057_, 0);
lean_inc(v_fst_3058_);
v_a_3049_ = v_a_3057_;
v_fst_3050_ = v_fst_3058_;
goto v___jp_3048_;
}
else
{
lean_dec_ref(v_e_3042_);
return v___y_3056_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3___boxed(lean_object* v_g_3127_, lean_object* v_e_3128_, lean_object* v_a_3129_, lean_object* v___y_3130_, lean_object* v___y_3131_, lean_object* v___y_3132_, lean_object* v___y_3133_){
_start:
{
lean_object* v_res_3134_; 
v_res_3134_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3(v_g_3127_, v_e_3128_, v_a_3129_, v___y_3130_, v___y_3131_, v___y_3132_);
lean_dec(v___y_3132_);
lean_dec_ref(v___y_3131_);
lean_dec(v_a_3129_);
return v_res_3134_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__0(void){
_start:
{
lean_object* v___x_3135_; lean_object* v___x_3136_; 
v___x_3135_ = lean_obj_once(&l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__0, &l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__0_once, _init_l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__0);
v___x_3136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3136_, 0, v___x_3135_);
return v___x_3136_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__1(void){
_start:
{
lean_object* v___x_3137_; lean_object* v___x_3138_; lean_object* v___x_3139_; 
v___x_3137_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__0);
v___x_3138_ = lean_unsigned_to_nat(0u);
v___x_3139_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_3139_, 0, v___x_3138_);
lean_ctor_set(v___x_3139_, 1, v___x_3138_);
lean_ctor_set(v___x_3139_, 2, v___x_3138_);
lean_ctor_set(v___x_3139_, 3, v___x_3138_);
lean_ctor_set(v___x_3139_, 4, v___x_3137_);
lean_ctor_set(v___x_3139_, 5, v___x_3137_);
lean_ctor_set(v___x_3139_, 6, v___x_3137_);
lean_ctor_set(v___x_3139_, 7, v___x_3137_);
lean_ctor_set(v___x_3139_, 8, v___x_3137_);
lean_ctor_set(v___x_3139_, 9, v___x_3137_);
lean_ctor_set(v___x_3139_, 10, v___x_3137_);
return v___x_3139_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__2(void){
_start:
{
lean_object* v___x_3140_; lean_object* v___x_3141_; lean_object* v___x_3142_; 
v___x_3140_ = lean_unsigned_to_nat(32u);
v___x_3141_ = lean_mk_empty_array_with_capacity(v___x_3140_);
v___x_3142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3142_, 0, v___x_3141_);
return v___x_3142_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__3(void){
_start:
{
size_t v___x_3143_; lean_object* v___x_3144_; lean_object* v___x_3145_; lean_object* v___x_3146_; lean_object* v___x_3147_; lean_object* v___x_3148_; 
v___x_3143_ = ((size_t)5ULL);
v___x_3144_ = lean_unsigned_to_nat(0u);
v___x_3145_ = lean_unsigned_to_nat(32u);
v___x_3146_ = lean_mk_empty_array_with_capacity(v___x_3145_);
v___x_3147_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__2);
v___x_3148_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3148_, 0, v___x_3147_);
lean_ctor_set(v___x_3148_, 1, v___x_3146_);
lean_ctor_set(v___x_3148_, 2, v___x_3144_);
lean_ctor_set(v___x_3148_, 3, v___x_3144_);
lean_ctor_set_usize(v___x_3148_, 4, v___x_3143_);
return v___x_3148_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__4(void){
_start:
{
lean_object* v___x_3149_; lean_object* v___x_3150_; lean_object* v___x_3151_; lean_object* v___x_3152_; 
v___x_3149_ = lean_box(1);
v___x_3150_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__3);
v___x_3151_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__0);
v___x_3152_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3152_, 0, v___x_3151_);
lean_ctor_set(v___x_3152_, 1, v___x_3150_);
lean_ctor_set(v___x_3152_, 2, v___x_3149_);
return v___x_3152_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10(lean_object* v_msgData_3153_, lean_object* v___y_3154_, lean_object* v___y_3155_){
_start:
{
lean_object* v___x_3157_; lean_object* v_toCold_3158_; lean_object* v_env_3159_; lean_object* v_options_3160_; lean_object* v___x_3161_; lean_object* v___x_3162_; lean_object* v___x_3163_; lean_object* v___x_3164_; lean_object* v___x_3165_; 
v___x_3157_ = lean_st_ref_get(v___y_3155_);
v_toCold_3158_ = lean_ctor_get(v___y_3154_, 0);
v_env_3159_ = lean_ctor_get(v___x_3157_, 0);
lean_inc_ref(v_env_3159_);
lean_dec(v___x_3157_);
v_options_3160_ = lean_ctor_get(v_toCold_3158_, 2);
v___x_3161_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__1);
v___x_3162_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__4);
lean_inc_ref(v_options_3160_);
v___x_3163_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3163_, 0, v_env_3159_);
lean_ctor_set(v___x_3163_, 1, v___x_3161_);
lean_ctor_set(v___x_3163_, 2, v___x_3162_);
lean_ctor_set(v___x_3163_, 3, v_options_3160_);
v___x_3164_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_3164_, 0, v___x_3163_);
lean_ctor_set(v___x_3164_, 1, v_msgData_3153_);
v___x_3165_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3165_, 0, v___x_3164_);
return v___x_3165_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___boxed(lean_object* v_msgData_3166_, lean_object* v___y_3167_, lean_object* v___y_3168_, lean_object* v___y_3169_){
_start:
{
lean_object* v_res_3170_; 
v_res_3170_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10(v_msgData_3166_, v___y_3167_, v___y_3168_);
lean_dec(v___y_3168_);
lean_dec_ref(v___y_3167_);
return v_res_3170_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5___redArg(lean_object* v_msg_3171_, lean_object* v___y_3172_, lean_object* v___y_3173_){
_start:
{
lean_object* v_ref_3175_; lean_object* v___x_3176_; lean_object* v_a_3177_; lean_object* v___x_3179_; uint8_t v_isShared_3180_; uint8_t v_isSharedCheck_3185_; 
v_ref_3175_ = lean_ctor_get(v___y_3172_, 2);
v___x_3176_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10(v_msg_3171_, v___y_3172_, v___y_3173_);
v_a_3177_ = lean_ctor_get(v___x_3176_, 0);
v_isSharedCheck_3185_ = !lean_is_exclusive(v___x_3176_);
if (v_isSharedCheck_3185_ == 0)
{
v___x_3179_ = v___x_3176_;
v_isShared_3180_ = v_isSharedCheck_3185_;
goto v_resetjp_3178_;
}
else
{
lean_inc(v_a_3177_);
lean_dec(v___x_3176_);
v___x_3179_ = lean_box(0);
v_isShared_3180_ = v_isSharedCheck_3185_;
goto v_resetjp_3178_;
}
v_resetjp_3178_:
{
lean_object* v___x_3181_; lean_object* v___x_3183_; 
lean_inc(v_ref_3175_);
v___x_3181_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3181_, 0, v_ref_3175_);
lean_ctor_set(v___x_3181_, 1, v_a_3177_);
if (v_isShared_3180_ == 0)
{
lean_ctor_set_tag(v___x_3179_, 1);
lean_ctor_set(v___x_3179_, 0, v___x_3181_);
v___x_3183_ = v___x_3179_;
goto v_reusejp_3182_;
}
else
{
lean_object* v_reuseFailAlloc_3184_; 
v_reuseFailAlloc_3184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3184_, 0, v___x_3181_);
v___x_3183_ = v_reuseFailAlloc_3184_;
goto v_reusejp_3182_;
}
v_reusejp_3182_:
{
return v___x_3183_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5___redArg___boxed(lean_object* v_msg_3186_, lean_object* v___y_3187_, lean_object* v___y_3188_, lean_object* v___y_3189_){
_start:
{
lean_object* v_res_3190_; 
v_res_3190_ = l_Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5___redArg(v_msg_3186_, v___y_3187_, v___y_3188_);
lean_dec(v___y_3188_);
lean_dec_ref(v___y_3187_);
return v_res_3190_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6___closed__0(void){
_start:
{
lean_object* v___x_3191_; double v___x_3192_; 
v___x_3191_ = lean_unsigned_to_nat(0u);
v___x_3192_ = lean_float_of_nat(v___x_3191_);
return v___x_3192_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6(lean_object* v_cls_3196_, lean_object* v_msg_3197_, lean_object* v___y_3198_, lean_object* v___y_3199_, lean_object* v___y_3200_){
_start:
{
lean_object* v_ref_3202_; lean_object* v___x_3203_; lean_object* v_a_3204_; lean_object* v___x_3206_; uint8_t v_isShared_3207_; uint8_t v_isSharedCheck_3250_; 
v_ref_3202_ = lean_ctor_get(v___y_3199_, 2);
v___x_3203_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10(v_msg_3197_, v___y_3199_, v___y_3200_);
v_a_3204_ = lean_ctor_get(v___x_3203_, 0);
v_isSharedCheck_3250_ = !lean_is_exclusive(v___x_3203_);
if (v_isSharedCheck_3250_ == 0)
{
v___x_3206_ = v___x_3203_;
v_isShared_3207_ = v_isSharedCheck_3250_;
goto v_resetjp_3205_;
}
else
{
lean_inc(v_a_3204_);
lean_dec(v___x_3203_);
v___x_3206_ = lean_box(0);
v_isShared_3207_ = v_isSharedCheck_3250_;
goto v_resetjp_3205_;
}
v_resetjp_3205_:
{
lean_object* v___x_3208_; lean_object* v_traceState_3209_; lean_object* v_env_3210_; lean_object* v_nextMacroScope_3211_; lean_object* v_ngen_3212_; lean_object* v_auxDeclNGen_3213_; lean_object* v_cache_3214_; lean_object* v_recordedDeps_3215_; lean_object* v_messages_3216_; lean_object* v_infoState_3217_; lean_object* v_snapshotTasks_3218_; lean_object* v___x_3220_; uint8_t v_isShared_3221_; uint8_t v_isSharedCheck_3249_; 
v___x_3208_ = lean_st_ref_take(v___y_3200_);
v_traceState_3209_ = lean_ctor_get(v___x_3208_, 4);
v_env_3210_ = lean_ctor_get(v___x_3208_, 0);
v_nextMacroScope_3211_ = lean_ctor_get(v___x_3208_, 1);
v_ngen_3212_ = lean_ctor_get(v___x_3208_, 2);
v_auxDeclNGen_3213_ = lean_ctor_get(v___x_3208_, 3);
v_cache_3214_ = lean_ctor_get(v___x_3208_, 5);
v_recordedDeps_3215_ = lean_ctor_get(v___x_3208_, 6);
v_messages_3216_ = lean_ctor_get(v___x_3208_, 7);
v_infoState_3217_ = lean_ctor_get(v___x_3208_, 8);
v_snapshotTasks_3218_ = lean_ctor_get(v___x_3208_, 9);
v_isSharedCheck_3249_ = !lean_is_exclusive(v___x_3208_);
if (v_isSharedCheck_3249_ == 0)
{
v___x_3220_ = v___x_3208_;
v_isShared_3221_ = v_isSharedCheck_3249_;
goto v_resetjp_3219_;
}
else
{
lean_inc(v_snapshotTasks_3218_);
lean_inc(v_infoState_3217_);
lean_inc(v_messages_3216_);
lean_inc(v_recordedDeps_3215_);
lean_inc(v_cache_3214_);
lean_inc(v_traceState_3209_);
lean_inc(v_auxDeclNGen_3213_);
lean_inc(v_ngen_3212_);
lean_inc(v_nextMacroScope_3211_);
lean_inc(v_env_3210_);
lean_dec(v___x_3208_);
v___x_3220_ = lean_box(0);
v_isShared_3221_ = v_isSharedCheck_3249_;
goto v_resetjp_3219_;
}
v_resetjp_3219_:
{
uint64_t v_tid_3222_; lean_object* v_traces_3223_; lean_object* v___x_3225_; uint8_t v_isShared_3226_; uint8_t v_isSharedCheck_3248_; 
v_tid_3222_ = lean_ctor_get_uint64(v_traceState_3209_, sizeof(void*)*1);
v_traces_3223_ = lean_ctor_get(v_traceState_3209_, 0);
v_isSharedCheck_3248_ = !lean_is_exclusive(v_traceState_3209_);
if (v_isSharedCheck_3248_ == 0)
{
v___x_3225_ = v_traceState_3209_;
v_isShared_3226_ = v_isSharedCheck_3248_;
goto v_resetjp_3224_;
}
else
{
lean_inc(v_traces_3223_);
lean_dec(v_traceState_3209_);
v___x_3225_ = lean_box(0);
v_isShared_3226_ = v_isSharedCheck_3248_;
goto v_resetjp_3224_;
}
v_resetjp_3224_:
{
lean_object* v___x_3227_; lean_object* v___x_3228_; double v___x_3229_; uint8_t v___x_3230_; lean_object* v___x_3231_; lean_object* v___x_3232_; lean_object* v___x_3233_; lean_object* v___x_3234_; lean_object* v___x_3235_; lean_object* v___x_3236_; lean_object* v___x_3238_; 
v___x_3227_ = lean_box(0);
v___x_3228_ = lean_box(0);
v___x_3229_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6___closed__0);
v___x_3230_ = 0;
v___x_3231_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6___closed__1));
v___x_3232_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3232_, 0, v_cls_3196_);
lean_ctor_set(v___x_3232_, 1, v___x_3228_);
lean_ctor_set(v___x_3232_, 2, v___x_3231_);
lean_ctor_set_float(v___x_3232_, sizeof(void*)*3, v___x_3229_);
lean_ctor_set_float(v___x_3232_, sizeof(void*)*3 + 8, v___x_3229_);
lean_ctor_set_uint8(v___x_3232_, sizeof(void*)*3 + 16, v___x_3230_);
v___x_3233_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6___closed__2));
v___x_3234_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3234_, 0, v___x_3232_);
lean_ctor_set(v___x_3234_, 1, v_a_3204_);
lean_ctor_set(v___x_3234_, 2, v___x_3233_);
lean_inc(v_ref_3202_);
v___x_3235_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3235_, 0, v_ref_3202_);
lean_ctor_set(v___x_3235_, 1, v___x_3234_);
v___x_3236_ = l_Lean_PersistentArray_push___redArg(v_traces_3223_, v___x_3235_);
if (v_isShared_3226_ == 0)
{
lean_ctor_set(v___x_3225_, 0, v___x_3236_);
v___x_3238_ = v___x_3225_;
goto v_reusejp_3237_;
}
else
{
lean_object* v_reuseFailAlloc_3247_; 
v_reuseFailAlloc_3247_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3247_, 0, v___x_3236_);
lean_ctor_set_uint64(v_reuseFailAlloc_3247_, sizeof(void*)*1, v_tid_3222_);
v___x_3238_ = v_reuseFailAlloc_3247_;
goto v_reusejp_3237_;
}
v_reusejp_3237_:
{
lean_object* v___x_3240_; 
if (v_isShared_3221_ == 0)
{
lean_ctor_set(v___x_3220_, 4, v___x_3238_);
v___x_3240_ = v___x_3220_;
goto v_reusejp_3239_;
}
else
{
lean_object* v_reuseFailAlloc_3246_; 
v_reuseFailAlloc_3246_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3246_, 0, v_env_3210_);
lean_ctor_set(v_reuseFailAlloc_3246_, 1, v_nextMacroScope_3211_);
lean_ctor_set(v_reuseFailAlloc_3246_, 2, v_ngen_3212_);
lean_ctor_set(v_reuseFailAlloc_3246_, 3, v_auxDeclNGen_3213_);
lean_ctor_set(v_reuseFailAlloc_3246_, 4, v___x_3238_);
lean_ctor_set(v_reuseFailAlloc_3246_, 5, v_cache_3214_);
lean_ctor_set(v_reuseFailAlloc_3246_, 6, v_recordedDeps_3215_);
lean_ctor_set(v_reuseFailAlloc_3246_, 7, v_messages_3216_);
lean_ctor_set(v_reuseFailAlloc_3246_, 8, v_infoState_3217_);
lean_ctor_set(v_reuseFailAlloc_3246_, 9, v_snapshotTasks_3218_);
v___x_3240_ = v_reuseFailAlloc_3246_;
goto v_reusejp_3239_;
}
v_reusejp_3239_:
{
lean_object* v___x_3241_; lean_object* v___x_3242_; lean_object* v___x_3244_; 
v___x_3241_ = lean_st_ref_put(v___y_3200_, v___x_3240_);
v___x_3242_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3242_, 0, v___x_3227_);
lean_ctor_set(v___x_3242_, 1, v___y_3198_);
if (v_isShared_3207_ == 0)
{
lean_ctor_set(v___x_3206_, 0, v___x_3242_);
v___x_3244_ = v___x_3206_;
goto v_reusejp_3243_;
}
else
{
lean_object* v_reuseFailAlloc_3245_; 
v_reuseFailAlloc_3245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3245_, 0, v___x_3242_);
v___x_3244_ = v_reuseFailAlloc_3245_;
goto v_reusejp_3243_;
}
v_reusejp_3243_:
{
return v___x_3244_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6___boxed(lean_object* v_cls_3251_, lean_object* v_msg_3252_, lean_object* v___y_3253_, lean_object* v___y_3254_, lean_object* v___y_3255_, lean_object* v___y_3256_){
_start:
{
lean_object* v_res_3257_; 
v_res_3257_ = l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6(v_cls_3251_, v_msg_3252_, v___y_3253_, v___y_3254_, v___y_3255_);
lean_dec(v___y_3255_);
lean_dec_ref(v___y_3254_);
return v_res_3257_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0_spec__0___redArg(lean_object* v_a_3258_, lean_object* v_x_3259_){
_start:
{
if (lean_obj_tag(v_x_3259_) == 0)
{
lean_object* v___x_3260_; 
v___x_3260_ = lean_box(0);
return v___x_3260_;
}
else
{
lean_object* v_key_3261_; lean_object* v_value_3262_; lean_object* v_tail_3263_; uint8_t v___x_3264_; 
v_key_3261_ = lean_ctor_get(v_x_3259_, 0);
v_value_3262_ = lean_ctor_get(v_x_3259_, 1);
v_tail_3263_ = lean_ctor_get(v_x_3259_, 2);
v___x_3264_ = l_Lean_instBEqFVarId_beq(v_key_3261_, v_a_3258_);
if (v___x_3264_ == 0)
{
v_x_3259_ = v_tail_3263_;
goto _start;
}
else
{
lean_object* v___x_3266_; 
lean_inc(v_value_3262_);
v___x_3266_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3266_, 0, v_value_3262_);
return v___x_3266_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0_spec__0___redArg___boxed(lean_object* v_a_3267_, lean_object* v_x_3268_){
_start:
{
lean_object* v_res_3269_; 
v_res_3269_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0_spec__0___redArg(v_a_3267_, v_x_3268_);
lean_dec(v_x_3268_);
lean_dec(v_a_3267_);
return v_res_3269_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0___redArg(lean_object* v_m_3270_, lean_object* v_a_3271_){
_start:
{
lean_object* v_buckets_3272_; lean_object* v___x_3273_; uint64_t v___x_3274_; uint64_t v___x_3275_; uint64_t v___x_3276_; uint64_t v_fold_3277_; uint64_t v___x_3278_; uint64_t v___x_3279_; uint64_t v___x_3280_; size_t v___x_3281_; size_t v___x_3282_; size_t v___x_3283_; size_t v___x_3284_; size_t v___x_3285_; lean_object* v___x_3286_; lean_object* v___x_3287_; 
v_buckets_3272_ = lean_ctor_get(v_m_3270_, 1);
v___x_3273_ = lean_array_get_size(v_buckets_3272_);
v___x_3274_ = l_Lean_instHashableFVarId_hash(v_a_3271_);
v___x_3275_ = 32ULL;
v___x_3276_ = lean_uint64_shift_right(v___x_3274_, v___x_3275_);
v_fold_3277_ = lean_uint64_xor(v___x_3274_, v___x_3276_);
v___x_3278_ = 16ULL;
v___x_3279_ = lean_uint64_shift_right(v_fold_3277_, v___x_3278_);
v___x_3280_ = lean_uint64_xor(v_fold_3277_, v___x_3279_);
v___x_3281_ = lean_uint64_to_usize(v___x_3280_);
v___x_3282_ = lean_usize_of_nat(v___x_3273_);
v___x_3283_ = ((size_t)1ULL);
v___x_3284_ = lean_usize_sub(v___x_3282_, v___x_3283_);
v___x_3285_ = lean_usize_land(v___x_3281_, v___x_3284_);
v___x_3286_ = lean_array_uget_borrowed(v_buckets_3272_, v___x_3285_);
v___x_3287_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0_spec__0___redArg(v_a_3271_, v___x_3286_);
return v___x_3287_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0___redArg___boxed(lean_object* v_m_3288_, lean_object* v_a_3289_){
_start:
{
lean_object* v_res_3290_; 
v_res_3290_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0___redArg(v_m_3288_, v_a_3289_);
lean_dec(v_a_3289_);
lean_dec_ref(v_m_3288_);
return v_res_3290_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___lam__0___boxed(lean_object* v___x_3291_, lean_object* v_m_3292_, lean_object* v_e_3293_, lean_object* v___y_3294_, lean_object* v___y_3295_, lean_object* v___y_3296_, lean_object* v___y_3297_){
_start:
{
uint8_t v___x_17711__boxed_3298_; lean_object* v_res_3299_; 
v___x_17711__boxed_3298_ = lean_unbox(v___x_3291_);
v_res_3299_ = l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___lam__0(v___x_17711__boxed_3298_, v_m_3292_, v_e_3293_, v___y_3294_, v___y_3295_, v___y_3296_);
lean_dec(v___y_3296_);
lean_dec_ref(v___y_3295_);
lean_dec_ref(v_e_3293_);
return v_res_3299_;
}
}
static lean_object* _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__0(void){
_start:
{
lean_object* v___x_3300_; lean_object* v___x_3301_; lean_object* v___x_3302_; 
v___x_3300_ = lean_box(0);
v___x_3301_ = lean_unsigned_to_nat(16u);
v___x_3302_ = lean_mk_array(v___x_3301_, v___x_3300_);
return v___x_3302_;
}
}
static lean_object* _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__1(void){
_start:
{
lean_object* v___x_3303_; lean_object* v___x_3304_; lean_object* v___x_3305_; 
v___x_3303_ = lean_obj_once(&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__0, &l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__0_once, _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__0);
v___x_3304_ = lean_unsigned_to_nat(0u);
v___x_3305_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3305_, 0, v___x_3304_);
lean_ctor_set(v___x_3305_, 1, v___x_3303_);
return v___x_3305_;
}
}
static lean_object* _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__5(void){
_start:
{
lean_object* v___x_3309_; lean_object* v___x_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; lean_object* v___x_3313_; lean_object* v___x_3314_; 
v___x_3309_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__4));
v___x_3310_ = lean_unsigned_to_nat(4u);
v___x_3311_ = lean_unsigned_to_nat(390u);
v___x_3312_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__3));
v___x_3313_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__2));
v___x_3314_ = l_mkPanicMessageWithDecl(v___x_3313_, v___x_3312_, v___x_3311_, v___x_3310_, v___x_3309_);
return v___x_3314_;
}
}
static lean_object* _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__7(void){
_start:
{
lean_object* v___x_3316_; lean_object* v___x_3317_; 
v___x_3316_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__6));
v___x_3317_ = l_Lean_stringToMessageData(v___x_3316_);
return v___x_3317_;
}
}
static lean_object* _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__13(void){
_start:
{
lean_object* v___x_3326_; lean_object* v___x_3327_; lean_object* v___x_3328_; 
v___x_3326_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__10));
v___x_3327_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__12));
v___x_3328_ = l_Lean_Name_append(v___x_3327_, v___x_3326_);
return v___x_3328_;
}
}
static lean_object* _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__15(void){
_start:
{
lean_object* v___x_3330_; lean_object* v___x_3331_; 
v___x_3330_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__14));
v___x_3331_ = l_Lean_stringToMessageData(v___x_3330_);
return v___x_3331_;
}
}
static lean_object* _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__17(void){
_start:
{
lean_object* v___x_3333_; lean_object* v___x_3334_; 
v___x_3333_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__16));
v___x_3334_ = l_Lean_stringToMessageData(v___x_3333_);
return v___x_3334_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit(lean_object* v_m_3335_, lean_object* v_fvarId_3336_, lean_object* v_a_3337_, lean_object* v_a_3338_, lean_object* v_a_3339_){
_start:
{
lean_object* v___x_3341_; 
v___x_3341_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0___redArg(v_m_3335_, v_fvarId_3336_);
if (lean_obj_tag(v___x_3341_) == 1)
{
lean_object* v_val_3342_; lean_object* v___x_3344_; uint8_t v_isShared_3345_; uint8_t v_isSharedCheck_3456_; 
v_val_3342_ = lean_ctor_get(v___x_3341_, 0);
v_isSharedCheck_3456_ = !lean_is_exclusive(v___x_3341_);
if (v_isSharedCheck_3456_ == 0)
{
v___x_3344_ = v___x_3341_;
v_isShared_3345_ = v_isSharedCheck_3456_;
goto v_resetjp_3343_;
}
else
{
lean_inc(v_val_3342_);
lean_dec(v___x_3341_);
v___x_3344_ = lean_box(0);
v_isShared_3345_ = v_isSharedCheck_3456_;
goto v_resetjp_3343_;
}
v_resetjp_3343_:
{
lean_object* v_fst_3346_; lean_object* v_snd_3347_; lean_object* v___x_3349_; uint8_t v_isShared_3350_; uint8_t v_isSharedCheck_3455_; 
v_fst_3346_ = lean_ctor_get(v_val_3342_, 0);
v_snd_3347_ = lean_ctor_get(v_val_3342_, 1);
v_isSharedCheck_3455_ = !lean_is_exclusive(v_val_3342_);
if (v_isSharedCheck_3455_ == 0)
{
v___x_3349_ = v_val_3342_;
v_isShared_3350_ = v_isSharedCheck_3455_;
goto v_resetjp_3348_;
}
else
{
lean_inc(v_snd_3347_);
lean_inc(v_fst_3346_);
lean_dec(v_val_3342_);
v___x_3349_ = lean_box(0);
v_isShared_3350_ = v_isSharedCheck_3455_;
goto v_resetjp_3348_;
}
v_resetjp_3348_:
{
lean_object* v_tempMark_3351_; lean_object* v_doneMark_3352_; lean_object* v___x_3353_; uint8_t v___x_3354_; 
v_tempMark_3351_ = lean_ctor_get(v_a_3337_, 0);
v_doneMark_3352_ = lean_ctor_get(v_a_3337_, 1);
v___x_3353_ = l_Lean_LocalDecl_fvarId(v_fst_3346_);
v___x_3354_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1___redArg(v_doneMark_3352_, v___x_3353_);
if (v___x_3354_ == 0)
{
lean_object* v_toCold_3355_; lean_object* v_options_3356_; lean_object* v_inheritedTraceOptions_3357_; uint8_t v_hasTrace_3358_; uint8_t v___x_3359_; lean_object* v___x_3360_; lean_object* v___f_3361_; lean_object* v___y_3363_; lean_object* v___y_3364_; lean_object* v___y_3365_; lean_object* v___y_3416_; lean_object* v___y_3417_; lean_object* v___y_3418_; lean_object* v___y_3423_; lean_object* v_tempMark_3424_; lean_object* v___y_3425_; lean_object* v___y_3426_; 
lean_del_object(v___x_3349_);
lean_del_object(v___x_3344_);
v_toCold_3355_ = lean_ctor_get(v_a_3338_, 0);
v_options_3356_ = lean_ctor_get(v_toCold_3355_, 2);
v_inheritedTraceOptions_3357_ = lean_ctor_get(v_toCold_3355_, 11);
v_hasTrace_3358_ = lean_ctor_get_uint8(v_options_3356_, sizeof(void*)*1);
v___x_3359_ = 1;
v___x_3360_ = lean_box(v___x_3359_);
v___f_3361_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___lam__0___boxed), 7, 2);
lean_closure_set(v___f_3361_, 0, v___x_3360_);
lean_closure_set(v___f_3361_, 1, v_m_3335_);
if (v_hasTrace_3358_ == 0)
{
lean_inc_ref(v_tempMark_3351_);
v___y_3423_ = v_a_3337_;
v_tempMark_3424_ = v_tempMark_3351_;
v___y_3425_ = v_a_3338_;
v___y_3426_ = v_a_3339_;
goto v___jp_3422_;
}
else
{
lean_object* v___x_3432_; lean_object* v___x_3433_; uint8_t v___x_3434_; 
v___x_3432_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__10));
v___x_3433_ = lean_obj_once(&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__13, &l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__13_once, _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__13);
v___x_3434_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3357_, v_options_3356_, v___x_3433_);
if (v___x_3434_ == 0)
{
lean_inc_ref(v_tempMark_3351_);
v___y_3423_ = v_a_3337_;
v_tempMark_3424_ = v_tempMark_3351_;
v___y_3425_ = v_a_3338_;
v___y_3426_ = v_a_3339_;
goto v___jp_3422_;
}
else
{
lean_object* v___x_3435_; lean_object* v___x_3436_; lean_object* v___x_3437_; lean_object* v___x_3438_; lean_object* v___x_3439_; lean_object* v___x_3440_; lean_object* v___x_3441_; lean_object* v___x_3442_; lean_object* v___x_3443_; lean_object* v___x_3444_; 
v___x_3435_ = lean_obj_once(&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__15, &l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__15_once, _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__15);
lean_inc(v___x_3353_);
v___x_3436_ = l_Lean_mkFVar(v___x_3353_);
v___x_3437_ = l_Lean_MessageData_ofExpr(v___x_3436_);
v___x_3438_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3438_, 0, v___x_3435_);
lean_ctor_set(v___x_3438_, 1, v___x_3437_);
v___x_3439_ = lean_obj_once(&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__17, &l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__17_once, _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__17);
v___x_3440_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3440_, 0, v___x_3438_);
lean_ctor_set(v___x_3440_, 1, v___x_3439_);
v___x_3441_ = l_Lean_LocalDecl_type(v_fst_3346_);
v___x_3442_ = l_Lean_MessageData_ofExpr(v___x_3441_);
v___x_3443_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3443_, 0, v___x_3440_);
lean_ctor_set(v___x_3443_, 1, v___x_3442_);
v___x_3444_ = l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6(v___x_3432_, v___x_3443_, v_a_3337_, v_a_3338_, v_a_3339_);
if (lean_obj_tag(v___x_3444_) == 0)
{
lean_object* v_a_3445_; lean_object* v_snd_3446_; lean_object* v_tempMark_3447_; 
v_a_3445_ = lean_ctor_get(v___x_3444_, 0);
lean_inc(v_a_3445_);
lean_dec_ref_known(v___x_3444_, 1);
v_snd_3446_ = lean_ctor_get(v_a_3445_, 1);
lean_inc(v_snd_3446_);
lean_dec(v_a_3445_);
v_tempMark_3447_ = lean_ctor_get(v_snd_3446_, 0);
lean_inc_ref(v_tempMark_3447_);
v___y_3423_ = v_snd_3446_;
v_tempMark_3424_ = v_tempMark_3447_;
v___y_3425_ = v_a_3338_;
v___y_3426_ = v_a_3339_;
goto v___jp_3422_;
}
else
{
lean_dec_ref(v___f_3361_);
lean_dec(v___x_3353_);
lean_dec(v_snd_3347_);
lean_dec(v_fst_3346_);
return v___x_3444_;
}
}
}
v___jp_3362_:
{
lean_object* v_tempMark_3366_; lean_object* v_doneMark_3367_; lean_object* v_newDecls_3368_; lean_object* v_newArgs_3369_; lean_object* v___x_3371_; uint8_t v_isShared_3372_; uint8_t v_isSharedCheck_3414_; 
v_tempMark_3366_ = lean_ctor_get(v___y_3365_, 0);
v_doneMark_3367_ = lean_ctor_get(v___y_3365_, 1);
v_newDecls_3368_ = lean_ctor_get(v___y_3365_, 2);
v_newArgs_3369_ = lean_ctor_get(v___y_3365_, 3);
v_isSharedCheck_3414_ = !lean_is_exclusive(v___y_3365_);
if (v_isSharedCheck_3414_ == 0)
{
v___x_3371_ = v___y_3365_;
v_isShared_3372_ = v_isSharedCheck_3414_;
goto v_resetjp_3370_;
}
else
{
lean_inc(v_newArgs_3369_);
lean_inc(v_newDecls_3368_);
lean_inc(v_doneMark_3367_);
lean_inc(v_tempMark_3366_);
lean_dec(v___y_3365_);
v___x_3371_ = lean_box(0);
v_isShared_3372_ = v_isSharedCheck_3414_;
goto v_resetjp_3370_;
}
v_resetjp_3370_:
{
lean_object* v___x_3373_; lean_object* v___x_3374_; lean_object* v___x_3376_; 
v___x_3373_ = lean_box(0);
lean_inc(v___x_3353_);
v___x_3374_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2___redArg(v_tempMark_3366_, v___x_3353_, v___x_3373_);
if (v_isShared_3372_ == 0)
{
lean_ctor_set(v___x_3371_, 0, v___x_3374_);
v___x_3376_ = v___x_3371_;
goto v_reusejp_3375_;
}
else
{
lean_object* v_reuseFailAlloc_3413_; 
v_reuseFailAlloc_3413_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3413_, 0, v___x_3374_);
lean_ctor_set(v_reuseFailAlloc_3413_, 1, v_doneMark_3367_);
lean_ctor_set(v_reuseFailAlloc_3413_, 2, v_newDecls_3368_);
lean_ctor_set(v_reuseFailAlloc_3413_, 3, v_newArgs_3369_);
v___x_3376_ = v_reuseFailAlloc_3413_;
goto v_reusejp_3375_;
}
v_reusejp_3375_:
{
lean_object* v___x_3377_; lean_object* v___x_3378_; lean_object* v___x_3379_; lean_object* v___x_3380_; 
v___x_3377_ = l_Lean_LocalDecl_type(v_fst_3346_);
v___x_3378_ = lean_obj_once(&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__1, &l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__1_once, _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__1);
v___x_3379_ = lean_st_mk_ref(v___x_3378_);
v___x_3380_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3(v___f_3361_, v___x_3377_, v___x_3379_, v___x_3376_, v___y_3363_, v___y_3364_);
if (lean_obj_tag(v___x_3380_) == 0)
{
lean_object* v_a_3381_; lean_object* v___x_3383_; uint8_t v_isShared_3384_; uint8_t v_isSharedCheck_3412_; 
v_a_3381_ = lean_ctor_get(v___x_3380_, 0);
v_isSharedCheck_3412_ = !lean_is_exclusive(v___x_3380_);
if (v_isSharedCheck_3412_ == 0)
{
v___x_3383_ = v___x_3380_;
v_isShared_3384_ = v_isSharedCheck_3412_;
goto v_resetjp_3382_;
}
else
{
lean_inc(v_a_3381_);
lean_dec(v___x_3380_);
v___x_3383_ = lean_box(0);
v_isShared_3384_ = v_isSharedCheck_3412_;
goto v_resetjp_3382_;
}
v_resetjp_3382_:
{
lean_object* v_snd_3385_; lean_object* v___x_3387_; uint8_t v_isShared_3388_; uint8_t v_isSharedCheck_3410_; 
v_snd_3385_ = lean_ctor_get(v_a_3381_, 1);
v_isSharedCheck_3410_ = !lean_is_exclusive(v_a_3381_);
if (v_isSharedCheck_3410_ == 0)
{
lean_object* v_unused_3411_; 
v_unused_3411_ = lean_ctor_get(v_a_3381_, 0);
lean_dec(v_unused_3411_);
v___x_3387_ = v_a_3381_;
v_isShared_3388_ = v_isSharedCheck_3410_;
goto v_resetjp_3386_;
}
else
{
lean_inc(v_snd_3385_);
lean_dec(v_a_3381_);
v___x_3387_ = lean_box(0);
v_isShared_3388_ = v_isSharedCheck_3410_;
goto v_resetjp_3386_;
}
v_resetjp_3386_:
{
lean_object* v___x_3389_; lean_object* v_tempMark_3390_; lean_object* v_doneMark_3391_; lean_object* v_newDecls_3392_; lean_object* v_newArgs_3393_; lean_object* v___x_3395_; uint8_t v_isShared_3396_; uint8_t v_isSharedCheck_3409_; 
v___x_3389_ = lean_st_ref_get(v___x_3379_);
lean_dec(v___x_3379_);
lean_dec(v___x_3389_);
v_tempMark_3390_ = lean_ctor_get(v_snd_3385_, 0);
v_doneMark_3391_ = lean_ctor_get(v_snd_3385_, 1);
v_newDecls_3392_ = lean_ctor_get(v_snd_3385_, 2);
v_newArgs_3393_ = lean_ctor_get(v_snd_3385_, 3);
v_isSharedCheck_3409_ = !lean_is_exclusive(v_snd_3385_);
if (v_isSharedCheck_3409_ == 0)
{
v___x_3395_ = v_snd_3385_;
v_isShared_3396_ = v_isSharedCheck_3409_;
goto v_resetjp_3394_;
}
else
{
lean_inc(v_newArgs_3393_);
lean_inc(v_newDecls_3392_);
lean_inc(v_doneMark_3391_);
lean_inc(v_tempMark_3390_);
lean_dec(v_snd_3385_);
v___x_3395_ = lean_box(0);
v_isShared_3396_ = v_isSharedCheck_3409_;
goto v_resetjp_3394_;
}
v_resetjp_3394_:
{
lean_object* v___x_3397_; lean_object* v___x_3398_; lean_object* v___x_3399_; lean_object* v___x_3401_; 
v___x_3397_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2___redArg(v_doneMark_3391_, v___x_3353_, v___x_3373_);
v___x_3398_ = lean_array_push(v_newDecls_3392_, v_fst_3346_);
v___x_3399_ = lean_array_push(v_newArgs_3393_, v_snd_3347_);
if (v_isShared_3396_ == 0)
{
lean_ctor_set(v___x_3395_, 3, v___x_3399_);
lean_ctor_set(v___x_3395_, 2, v___x_3398_);
lean_ctor_set(v___x_3395_, 1, v___x_3397_);
v___x_3401_ = v___x_3395_;
goto v_reusejp_3400_;
}
else
{
lean_object* v_reuseFailAlloc_3408_; 
v_reuseFailAlloc_3408_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3408_, 0, v_tempMark_3390_);
lean_ctor_set(v_reuseFailAlloc_3408_, 1, v___x_3397_);
lean_ctor_set(v_reuseFailAlloc_3408_, 2, v___x_3398_);
lean_ctor_set(v_reuseFailAlloc_3408_, 3, v___x_3399_);
v___x_3401_ = v_reuseFailAlloc_3408_;
goto v_reusejp_3400_;
}
v_reusejp_3400_:
{
lean_object* v___x_3403_; 
if (v_isShared_3388_ == 0)
{
lean_ctor_set(v___x_3387_, 1, v___x_3401_);
lean_ctor_set(v___x_3387_, 0, v___x_3373_);
v___x_3403_ = v___x_3387_;
goto v_reusejp_3402_;
}
else
{
lean_object* v_reuseFailAlloc_3407_; 
v_reuseFailAlloc_3407_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3407_, 0, v___x_3373_);
lean_ctor_set(v_reuseFailAlloc_3407_, 1, v___x_3401_);
v___x_3403_ = v_reuseFailAlloc_3407_;
goto v_reusejp_3402_;
}
v_reusejp_3402_:
{
lean_object* v___x_3405_; 
if (v_isShared_3384_ == 0)
{
lean_ctor_set(v___x_3383_, 0, v___x_3403_);
v___x_3405_ = v___x_3383_;
goto v_reusejp_3404_;
}
else
{
lean_object* v_reuseFailAlloc_3406_; 
v_reuseFailAlloc_3406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3406_, 0, v___x_3403_);
v___x_3405_ = v_reuseFailAlloc_3406_;
goto v_reusejp_3404_;
}
v_reusejp_3404_:
{
return v___x_3405_;
}
}
}
}
}
}
}
else
{
lean_dec(v___x_3379_);
lean_dec(v___x_3353_);
lean_dec(v_snd_3347_);
lean_dec(v_fst_3346_);
return v___x_3380_;
}
}
}
}
v___jp_3415_:
{
uint8_t v___x_3419_; 
v___x_3419_ = l_Lean_LocalDecl_isLet(v_fst_3346_, v___x_3359_);
if (v___x_3419_ == 0)
{
v___y_3363_ = v___y_3417_;
v___y_3364_ = v___y_3418_;
v___y_3365_ = v___y_3416_;
goto v___jp_3362_;
}
else
{
if (v___x_3354_ == 0)
{
lean_object* v___x_3420_; lean_object* v___x_3421_; 
lean_dec_ref(v___f_3361_);
lean_dec(v___x_3353_);
lean_dec(v_snd_3347_);
lean_dec(v_fst_3346_);
v___x_3420_ = lean_obj_once(&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__5, &l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__5_once, _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__5);
v___x_3421_ = l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4(v___x_3420_, v___y_3416_, v___y_3417_, v___y_3418_);
return v___x_3421_;
}
else
{
v___y_3363_ = v___y_3417_;
v___y_3364_ = v___y_3418_;
v___y_3365_ = v___y_3416_;
goto v___jp_3362_;
}
}
}
v___jp_3422_:
{
uint8_t v___x_3427_; 
v___x_3427_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1___redArg(v_tempMark_3424_, v___x_3353_);
lean_dec_ref(v_tempMark_3424_);
if (v___x_3427_ == 0)
{
v___y_3416_ = v___y_3423_;
v___y_3417_ = v___y_3425_;
v___y_3418_ = v___y_3426_;
goto v___jp_3415_;
}
else
{
lean_object* v___x_3428_; lean_object* v___x_3429_; 
lean_dec_ref(v___y_3423_);
v___x_3428_ = lean_obj_once(&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__7, &l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__7_once, _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__7);
v___x_3429_ = l_Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5___redArg(v___x_3428_, v___y_3425_, v___y_3426_);
if (lean_obj_tag(v___x_3429_) == 0)
{
lean_object* v_a_3430_; lean_object* v_snd_3431_; 
v_a_3430_ = lean_ctor_get(v___x_3429_, 0);
lean_inc(v_a_3430_);
lean_dec_ref_known(v___x_3429_, 1);
v_snd_3431_ = lean_ctor_get(v_a_3430_, 1);
lean_inc(v_snd_3431_);
lean_dec(v_a_3430_);
v___y_3416_ = v_snd_3431_;
v___y_3417_ = v___y_3425_;
v___y_3418_ = v___y_3426_;
goto v___jp_3415_;
}
else
{
lean_dec_ref(v___f_3361_);
lean_dec(v___x_3353_);
lean_dec(v_snd_3347_);
lean_dec(v_fst_3346_);
return v___x_3429_;
}
}
}
}
else
{
lean_object* v___x_3448_; lean_object* v___x_3450_; 
lean_dec(v___x_3353_);
lean_dec(v_snd_3347_);
lean_dec(v_fst_3346_);
lean_dec_ref(v_m_3335_);
v___x_3448_ = lean_box(0);
if (v_isShared_3350_ == 0)
{
lean_ctor_set(v___x_3349_, 1, v_a_3337_);
lean_ctor_set(v___x_3349_, 0, v___x_3448_);
v___x_3450_ = v___x_3349_;
goto v_reusejp_3449_;
}
else
{
lean_object* v_reuseFailAlloc_3454_; 
v_reuseFailAlloc_3454_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3454_, 0, v___x_3448_);
lean_ctor_set(v_reuseFailAlloc_3454_, 1, v_a_3337_);
v___x_3450_ = v_reuseFailAlloc_3454_;
goto v_reusejp_3449_;
}
v_reusejp_3449_:
{
lean_object* v___x_3452_; 
if (v_isShared_3345_ == 0)
{
lean_ctor_set_tag(v___x_3344_, 0);
lean_ctor_set(v___x_3344_, 0, v___x_3450_);
v___x_3452_ = v___x_3344_;
goto v_reusejp_3451_;
}
else
{
lean_object* v_reuseFailAlloc_3453_; 
v_reuseFailAlloc_3453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3453_, 0, v___x_3450_);
v___x_3452_ = v_reuseFailAlloc_3453_;
goto v_reusejp_3451_;
}
v_reusejp_3451_:
{
return v___x_3452_;
}
}
}
}
}
}
else
{
lean_object* v___x_3457_; lean_object* v___x_3458_; lean_object* v___x_3459_; 
lean_dec(v___x_3341_);
lean_dec_ref(v_m_3335_);
v___x_3457_ = lean_box(0);
v___x_3458_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3458_, 0, v___x_3457_);
lean_ctor_set(v___x_3458_, 1, v_a_3337_);
v___x_3459_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3459_, 0, v___x_3458_);
return v___x_3459_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___lam__0(uint8_t v___x_3460_, lean_object* v_m_3461_, lean_object* v_e_3462_, lean_object* v___y_3463_, lean_object* v___y_3464_, lean_object* v___y_3465_){
_start:
{
lean_object* v___y_3468_; uint8_t v___x_3472_; 
v___x_3472_ = l_Lean_Expr_hasFVar(v_e_3462_);
if (v___x_3472_ == 0)
{
lean_object* v___x_3473_; lean_object* v___x_3474_; lean_object* v___x_3475_; 
lean_dec_ref(v_m_3461_);
v___x_3473_ = lean_box(v___x_3472_);
v___x_3474_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3474_, 0, v___x_3473_);
lean_ctor_set(v___x_3474_, 1, v___y_3463_);
v___x_3475_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3475_, 0, v___x_3474_);
return v___x_3475_;
}
else
{
uint8_t v___x_3476_; 
v___x_3476_ = l_Lean_Expr_isFVar(v_e_3462_);
if (v___x_3476_ == 0)
{
lean_dec_ref(v_m_3461_);
v___y_3468_ = v___y_3463_;
goto v___jp_3467_;
}
else
{
lean_object* v___x_3477_; lean_object* v___x_3478_; 
v___x_3477_ = l_Lean_Expr_fvarId_x21(v_e_3462_);
v___x_3478_ = l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit(v_m_3461_, v___x_3477_, v___y_3463_, v___y_3464_, v___y_3465_);
lean_dec(v___x_3477_);
if (lean_obj_tag(v___x_3478_) == 0)
{
lean_object* v_a_3479_; lean_object* v_snd_3480_; 
v_a_3479_ = lean_ctor_get(v___x_3478_, 0);
lean_inc(v_a_3479_);
lean_dec_ref_known(v___x_3478_, 1);
v_snd_3480_ = lean_ctor_get(v_a_3479_, 1);
lean_inc(v_snd_3480_);
lean_dec(v_a_3479_);
v___y_3468_ = v_snd_3480_;
goto v___jp_3467_;
}
else
{
lean_object* v_a_3481_; lean_object* v___x_3483_; uint8_t v_isShared_3484_; uint8_t v_isSharedCheck_3488_; 
v_a_3481_ = lean_ctor_get(v___x_3478_, 0);
v_isSharedCheck_3488_ = !lean_is_exclusive(v___x_3478_);
if (v_isSharedCheck_3488_ == 0)
{
v___x_3483_ = v___x_3478_;
v_isShared_3484_ = v_isSharedCheck_3488_;
goto v_resetjp_3482_;
}
else
{
lean_inc(v_a_3481_);
lean_dec(v___x_3478_);
v___x_3483_ = lean_box(0);
v_isShared_3484_ = v_isSharedCheck_3488_;
goto v_resetjp_3482_;
}
v_resetjp_3482_:
{
lean_object* v___x_3486_; 
if (v_isShared_3484_ == 0)
{
v___x_3486_ = v___x_3483_;
goto v_reusejp_3485_;
}
else
{
lean_object* v_reuseFailAlloc_3487_; 
v_reuseFailAlloc_3487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3487_, 0, v_a_3481_);
v___x_3486_ = v_reuseFailAlloc_3487_;
goto v_reusejp_3485_;
}
v_reusejp_3485_:
{
return v___x_3486_;
}
}
}
}
}
v___jp_3467_:
{
lean_object* v___x_3469_; lean_object* v___x_3470_; lean_object* v___x_3471_; 
v___x_3469_ = lean_box(v___x_3460_);
v___x_3470_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3470_, 0, v___x_3469_);
lean_ctor_set(v___x_3470_, 1, v___y_3468_);
v___x_3471_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3471_, 0, v___x_3470_);
return v___x_3471_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___boxed(lean_object* v_m_3489_, lean_object* v_fvarId_3490_, lean_object* v_a_3491_, lean_object* v_a_3492_, lean_object* v_a_3493_, lean_object* v_a_3494_){
_start:
{
lean_object* v_res_3495_; 
v_res_3495_ = l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit(v_m_3489_, v_fvarId_3490_, v_a_3491_, v_a_3492_, v_a_3493_);
lean_dec(v_a_3493_);
lean_dec_ref(v_a_3492_);
lean_dec(v_fvarId_3490_);
return v_res_3495_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0(lean_object* v_00_u03b2_3496_, lean_object* v_m_3497_, lean_object* v_a_3498_){
_start:
{
lean_object* v___x_3499_; 
v___x_3499_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0___redArg(v_m_3497_, v_a_3498_);
return v___x_3499_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0___boxed(lean_object* v_00_u03b2_3500_, lean_object* v_m_3501_, lean_object* v_a_3502_){
_start:
{
lean_object* v_res_3503_; 
v_res_3503_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0(v_00_u03b2_3500_, v_m_3501_, v_a_3502_);
lean_dec(v_a_3502_);
lean_dec_ref(v_m_3501_);
return v_res_3503_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1(lean_object* v_00_u03b2_3504_, lean_object* v_m_3505_, lean_object* v_a_3506_){
_start:
{
uint8_t v___x_3507_; 
v___x_3507_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1___redArg(v_m_3505_, v_a_3506_);
return v___x_3507_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1___boxed(lean_object* v_00_u03b2_3508_, lean_object* v_m_3509_, lean_object* v_a_3510_){
_start:
{
uint8_t v_res_3511_; lean_object* v_r_3512_; 
v_res_3511_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1(v_00_u03b2_3508_, v_m_3509_, v_a_3510_);
lean_dec(v_a_3510_);
lean_dec_ref(v_m_3509_);
v_r_3512_ = lean_box(v_res_3511_);
return v_r_3512_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2(lean_object* v_00_u03b2_3513_, lean_object* v_m_3514_, lean_object* v_a_3515_, lean_object* v_b_3516_){
_start:
{
lean_object* v___x_3517_; 
v___x_3517_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2___redArg(v_m_3514_, v_a_3515_, v_b_3516_);
return v___x_3517_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5(lean_object* v_00_u03b1_3518_, lean_object* v_msg_3519_, lean_object* v___y_3520_, lean_object* v___y_3521_, lean_object* v___y_3522_){
_start:
{
lean_object* v___x_3524_; 
v___x_3524_ = l_Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5___redArg(v_msg_3519_, v___y_3521_, v___y_3522_);
return v___x_3524_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5___boxed(lean_object* v_00_u03b1_3525_, lean_object* v_msg_3526_, lean_object* v___y_3527_, lean_object* v___y_3528_, lean_object* v___y_3529_, lean_object* v___y_3530_){
_start:
{
lean_object* v_res_3531_; 
v_res_3531_ = l_Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5(v_00_u03b1_3525_, v_msg_3526_, v___y_3527_, v___y_3528_, v___y_3529_);
lean_dec(v___y_3529_);
lean_dec_ref(v___y_3528_);
lean_dec_ref(v___y_3527_);
return v_res_3531_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0_spec__0(lean_object* v_00_u03b2_3532_, lean_object* v_a_3533_, lean_object* v_x_3534_){
_start:
{
lean_object* v___x_3535_; 
v___x_3535_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0_spec__0___redArg(v_a_3533_, v_x_3534_);
return v___x_3535_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3536_, lean_object* v_a_3537_, lean_object* v_x_3538_){
_start:
{
lean_object* v_res_3539_; 
v_res_3539_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0_spec__0(v_00_u03b2_3536_, v_a_3537_, v_x_3538_);
lean_dec(v_x_3538_);
lean_dec(v_a_3537_);
return v_res_3539_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1_spec__2(lean_object* v_00_u03b2_3540_, lean_object* v_a_3541_, lean_object* v_x_3542_){
_start:
{
uint8_t v___x_3543_; 
v___x_3543_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1_spec__2___redArg(v_a_3541_, v_x_3542_);
return v___x_3543_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1_spec__2___boxed(lean_object* v_00_u03b2_3544_, lean_object* v_a_3545_, lean_object* v_x_3546_){
_start:
{
uint8_t v_res_3547_; lean_object* v_r_3548_; 
v_res_3547_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1_spec__2(v_00_u03b2_3544_, v_a_3545_, v_x_3546_);
lean_dec(v_x_3546_);
lean_dec(v_a_3545_);
v_r_3548_ = lean_box(v_res_3547_);
return v_r_3548_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__4(lean_object* v_00_u03b2_3549_, lean_object* v_data_3550_){
_start:
{
lean_object* v___x_3551_; 
v___x_3551_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__4___redArg(v_data_3550_);
return v___x_3551_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__6(lean_object* v_00_u03b2_3552_, lean_object* v_m_3553_, lean_object* v_a_3554_){
_start:
{
lean_object* v___x_3555_; 
v___x_3555_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__6___redArg(v_m_3553_, v_a_3554_);
return v___x_3555_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__6___boxed(lean_object* v_00_u03b2_3556_, lean_object* v_m_3557_, lean_object* v_a_3558_){
_start:
{
lean_object* v_res_3559_; 
v_res_3559_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__6(v_00_u03b2_3556_, v_m_3557_, v_a_3558_);
lean_dec_ref(v_a_3558_);
lean_dec_ref(v_m_3557_);
return v_res_3559_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7(lean_object* v_00_u03b2_3560_, lean_object* v_m_3561_, lean_object* v_a_3562_, lean_object* v_b_3563_){
_start:
{
lean_object* v___x_3564_; 
v___x_3564_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7___redArg(v_m_3561_, v_a_3562_, v_b_3563_);
return v___x_3564_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__4_spec__6(lean_object* v_00_u03b2_3565_, lean_object* v_i_3566_, lean_object* v_source_3567_, lean_object* v_target_3568_){
_start:
{
lean_object* v___x_3569_; 
v___x_3569_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__4_spec__6___redArg(v_i_3566_, v_source_3567_, v_target_3568_);
return v___x_3569_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__6_spec__9(lean_object* v_00_u03b2_3570_, lean_object* v_a_3571_, lean_object* v_x_3572_){
_start:
{
lean_object* v___x_3573_; 
v___x_3573_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__6_spec__9___redArg(v_a_3571_, v_x_3572_);
return v___x_3573_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__6_spec__9___boxed(lean_object* v_00_u03b2_3574_, lean_object* v_a_3575_, lean_object* v_x_3576_){
_start:
{
lean_object* v_res_3577_; 
v_res_3577_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__6_spec__9(v_00_u03b2_3574_, v_a_3575_, v_x_3576_);
lean_dec(v_x_3576_);
lean_dec_ref(v_a_3575_);
return v_res_3577_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__11(lean_object* v_00_u03b2_3578_, lean_object* v_a_3579_, lean_object* v_x_3580_){
_start:
{
uint8_t v___x_3581_; 
v___x_3581_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__11___redArg(v_a_3579_, v_x_3580_);
return v___x_3581_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__11___boxed(lean_object* v_00_u03b2_3582_, lean_object* v_a_3583_, lean_object* v_x_3584_){
_start:
{
uint8_t v_res_3585_; lean_object* v_r_3586_; 
v_res_3585_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__11(v_00_u03b2_3582_, v_a_3583_, v_x_3584_);
lean_dec(v_x_3584_);
lean_dec_ref(v_a_3583_);
v_r_3586_ = lean_box(v_res_3585_);
return v_r_3586_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__12(lean_object* v_00_u03b2_3587_, lean_object* v_data_3588_){
_start:
{
lean_object* v___x_3589_; 
v___x_3589_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__12___redArg(v_data_3588_);
return v___x_3589_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__13(lean_object* v_00_u03b2_3590_, lean_object* v_a_3591_, lean_object* v_b_3592_, lean_object* v_x_3593_){
_start:
{
lean_object* v___x_3594_; 
v___x_3594_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__13___redArg(v_a_3591_, v_b_3592_, v_x_3593_);
return v___x_3594_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__4_spec__6_spec__11(lean_object* v_00_u03b2_3595_, lean_object* v_x_3596_, lean_object* v_x_3597_){
_start:
{
lean_object* v___x_3598_; 
v___x_3598_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__4_spec__6_spec__11___redArg(v_x_3596_, v_x_3597_);
return v___x_3598_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__12_spec__17(lean_object* v_00_u03b2_3599_, lean_object* v_i_3600_, lean_object* v_source_3601_, lean_object* v_target_3602_){
_start:
{
lean_object* v___x_3603_; 
v___x_3603_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__12_spec__17___redArg(v_i_3600_, v_source_3601_, v_target_3602_);
return v___x_3603_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__12_spec__17_spec__18(lean_object* v_00_u03b2_3604_, lean_object* v_x_3605_, lean_object* v_x_3606_){
_start:
{
lean_object* v___x_3607_; 
v___x_3607_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__12_spec__17_spec__18___redArg(v_x_3605_, v_x_3606_);
return v___x_3607_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__1(lean_object* v_msg_3609_, lean_object* v___y_3610_, lean_object* v___y_3611_){
_start:
{
lean_object* v___f_3613_; lean_object* v___x_7408__overap_3614_; lean_object* v___x_3615_; 
v___f_3613_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__1___closed__0));
v___x_7408__overap_3614_ = lean_panic_fn_borrowed(v___f_3613_, v_msg_3609_);
lean_inc(v___y_3611_);
lean_inc_ref(v___y_3610_);
v___x_3615_ = lean_apply_3(v___x_7408__overap_3614_, v___y_3610_, v___y_3611_, lean_box(0));
return v___x_3615_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__1___boxed(lean_object* v_msg_3616_, lean_object* v___y_3617_, lean_object* v___y_3618_, lean_object* v___y_3619_){
_start:
{
lean_object* v_res_3620_; 
v_res_3620_ = l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__1(v_msg_3616_, v___y_3617_, v___y_3618_);
lean_dec(v___y_3618_);
lean_dec_ref(v___y_3617_);
return v_res_3620_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___lam__0(lean_object* v_newDecls_3621_, lean_object* v_newArgs_3622_, lean_object* v_____r_3623_, lean_object* v___y_3624_, lean_object* v___y_3625_, lean_object* v___y_3626_){
_start:
{
lean_object* v___x_3628_; lean_object* v___x_3629_; lean_object* v___x_3630_; 
v___x_3628_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3628_, 0, v_newDecls_3621_);
lean_ctor_set(v___x_3628_, 1, v_newArgs_3622_);
v___x_3629_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3629_, 0, v___x_3628_);
lean_ctor_set(v___x_3629_, 1, v___y_3624_);
v___x_3630_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3630_, 0, v___x_3629_);
return v___x_3630_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___lam__0___boxed(lean_object* v_newDecls_3631_, lean_object* v_newArgs_3632_, lean_object* v_____r_3633_, lean_object* v___y_3634_, lean_object* v___y_3635_, lean_object* v___y_3636_, lean_object* v___y_3637_){
_start:
{
lean_object* v_res_3638_; 
v_res_3638_ = l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___lam__0(v_newDecls_3631_, v_newArgs_3632_, v_____r_3633_, v___y_3634_, v___y_3635_, v___y_3636_);
lean_dec(v___y_3636_);
lean_dec_ref(v___y_3635_);
return v_res_3638_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__6(lean_object* v_cls_3639_, lean_object* v_msg_3640_, lean_object* v___y_3641_, lean_object* v___y_3642_){
_start:
{
lean_object* v_ref_3644_; lean_object* v___x_3645_; lean_object* v_a_3646_; lean_object* v___x_3648_; uint8_t v_isShared_3649_; uint8_t v_isSharedCheck_3691_; 
v_ref_3644_ = lean_ctor_get(v___y_3641_, 2);
v___x_3645_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10(v_msg_3640_, v___y_3641_, v___y_3642_);
v_a_3646_ = lean_ctor_get(v___x_3645_, 0);
v_isSharedCheck_3691_ = !lean_is_exclusive(v___x_3645_);
if (v_isSharedCheck_3691_ == 0)
{
v___x_3648_ = v___x_3645_;
v_isShared_3649_ = v_isSharedCheck_3691_;
goto v_resetjp_3647_;
}
else
{
lean_inc(v_a_3646_);
lean_dec(v___x_3645_);
v___x_3648_ = lean_box(0);
v_isShared_3649_ = v_isSharedCheck_3691_;
goto v_resetjp_3647_;
}
v_resetjp_3647_:
{
lean_object* v___x_3650_; lean_object* v_traceState_3651_; lean_object* v_env_3652_; lean_object* v_nextMacroScope_3653_; lean_object* v_ngen_3654_; lean_object* v_auxDeclNGen_3655_; lean_object* v_cache_3656_; lean_object* v_recordedDeps_3657_; lean_object* v_messages_3658_; lean_object* v_infoState_3659_; lean_object* v_snapshotTasks_3660_; lean_object* v___x_3662_; uint8_t v_isShared_3663_; uint8_t v_isSharedCheck_3690_; 
v___x_3650_ = lean_st_ref_take(v___y_3642_);
v_traceState_3651_ = lean_ctor_get(v___x_3650_, 4);
v_env_3652_ = lean_ctor_get(v___x_3650_, 0);
v_nextMacroScope_3653_ = lean_ctor_get(v___x_3650_, 1);
v_ngen_3654_ = lean_ctor_get(v___x_3650_, 2);
v_auxDeclNGen_3655_ = lean_ctor_get(v___x_3650_, 3);
v_cache_3656_ = lean_ctor_get(v___x_3650_, 5);
v_recordedDeps_3657_ = lean_ctor_get(v___x_3650_, 6);
v_messages_3658_ = lean_ctor_get(v___x_3650_, 7);
v_infoState_3659_ = lean_ctor_get(v___x_3650_, 8);
v_snapshotTasks_3660_ = lean_ctor_get(v___x_3650_, 9);
v_isSharedCheck_3690_ = !lean_is_exclusive(v___x_3650_);
if (v_isSharedCheck_3690_ == 0)
{
v___x_3662_ = v___x_3650_;
v_isShared_3663_ = v_isSharedCheck_3690_;
goto v_resetjp_3661_;
}
else
{
lean_inc(v_snapshotTasks_3660_);
lean_inc(v_infoState_3659_);
lean_inc(v_messages_3658_);
lean_inc(v_recordedDeps_3657_);
lean_inc(v_cache_3656_);
lean_inc(v_traceState_3651_);
lean_inc(v_auxDeclNGen_3655_);
lean_inc(v_ngen_3654_);
lean_inc(v_nextMacroScope_3653_);
lean_inc(v_env_3652_);
lean_dec(v___x_3650_);
v___x_3662_ = lean_box(0);
v_isShared_3663_ = v_isSharedCheck_3690_;
goto v_resetjp_3661_;
}
v_resetjp_3661_:
{
uint64_t v_tid_3664_; lean_object* v_traces_3665_; lean_object* v___x_3667_; uint8_t v_isShared_3668_; uint8_t v_isSharedCheck_3689_; 
v_tid_3664_ = lean_ctor_get_uint64(v_traceState_3651_, sizeof(void*)*1);
v_traces_3665_ = lean_ctor_get(v_traceState_3651_, 0);
v_isSharedCheck_3689_ = !lean_is_exclusive(v_traceState_3651_);
if (v_isSharedCheck_3689_ == 0)
{
v___x_3667_ = v_traceState_3651_;
v_isShared_3668_ = v_isSharedCheck_3689_;
goto v_resetjp_3666_;
}
else
{
lean_inc(v_traces_3665_);
lean_dec(v_traceState_3651_);
v___x_3667_ = lean_box(0);
v_isShared_3668_ = v_isSharedCheck_3689_;
goto v_resetjp_3666_;
}
v_resetjp_3666_:
{
lean_object* v___x_3669_; lean_object* v___x_3670_; double v___x_3671_; uint8_t v___x_3672_; lean_object* v___x_3673_; lean_object* v___x_3674_; lean_object* v___x_3675_; lean_object* v___x_3676_; lean_object* v___x_3677_; lean_object* v___x_3678_; lean_object* v___x_3680_; 
v___x_3669_ = lean_box(0);
v___x_3670_ = lean_box(0);
v___x_3671_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6___closed__0);
v___x_3672_ = 0;
v___x_3673_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6___closed__1));
v___x_3674_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3674_, 0, v_cls_3639_);
lean_ctor_set(v___x_3674_, 1, v___x_3670_);
lean_ctor_set(v___x_3674_, 2, v___x_3673_);
lean_ctor_set_float(v___x_3674_, sizeof(void*)*3, v___x_3671_);
lean_ctor_set_float(v___x_3674_, sizeof(void*)*3 + 8, v___x_3671_);
lean_ctor_set_uint8(v___x_3674_, sizeof(void*)*3 + 16, v___x_3672_);
v___x_3675_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6___closed__2));
v___x_3676_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3676_, 0, v___x_3674_);
lean_ctor_set(v___x_3676_, 1, v_a_3646_);
lean_ctor_set(v___x_3676_, 2, v___x_3675_);
lean_inc(v_ref_3644_);
v___x_3677_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3677_, 0, v_ref_3644_);
lean_ctor_set(v___x_3677_, 1, v___x_3676_);
v___x_3678_ = l_Lean_PersistentArray_push___redArg(v_traces_3665_, v___x_3677_);
if (v_isShared_3668_ == 0)
{
lean_ctor_set(v___x_3667_, 0, v___x_3678_);
v___x_3680_ = v___x_3667_;
goto v_reusejp_3679_;
}
else
{
lean_object* v_reuseFailAlloc_3688_; 
v_reuseFailAlloc_3688_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3688_, 0, v___x_3678_);
lean_ctor_set_uint64(v_reuseFailAlloc_3688_, sizeof(void*)*1, v_tid_3664_);
v___x_3680_ = v_reuseFailAlloc_3688_;
goto v_reusejp_3679_;
}
v_reusejp_3679_:
{
lean_object* v___x_3682_; 
if (v_isShared_3663_ == 0)
{
lean_ctor_set(v___x_3662_, 4, v___x_3680_);
v___x_3682_ = v___x_3662_;
goto v_reusejp_3681_;
}
else
{
lean_object* v_reuseFailAlloc_3687_; 
v_reuseFailAlloc_3687_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3687_, 0, v_env_3652_);
lean_ctor_set(v_reuseFailAlloc_3687_, 1, v_nextMacroScope_3653_);
lean_ctor_set(v_reuseFailAlloc_3687_, 2, v_ngen_3654_);
lean_ctor_set(v_reuseFailAlloc_3687_, 3, v_auxDeclNGen_3655_);
lean_ctor_set(v_reuseFailAlloc_3687_, 4, v___x_3680_);
lean_ctor_set(v_reuseFailAlloc_3687_, 5, v_cache_3656_);
lean_ctor_set(v_reuseFailAlloc_3687_, 6, v_recordedDeps_3657_);
lean_ctor_set(v_reuseFailAlloc_3687_, 7, v_messages_3658_);
lean_ctor_set(v_reuseFailAlloc_3687_, 8, v_infoState_3659_);
lean_ctor_set(v_reuseFailAlloc_3687_, 9, v_snapshotTasks_3660_);
v___x_3682_ = v_reuseFailAlloc_3687_;
goto v_reusejp_3681_;
}
v_reusejp_3681_:
{
lean_object* v___x_3683_; lean_object* v___x_3685_; 
v___x_3683_ = lean_st_ref_put(v___y_3642_, v___x_3682_);
if (v_isShared_3649_ == 0)
{
lean_ctor_set(v___x_3648_, 0, v___x_3669_);
v___x_3685_ = v___x_3648_;
goto v_reusejp_3684_;
}
else
{
lean_object* v_reuseFailAlloc_3686_; 
v_reuseFailAlloc_3686_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3686_, 0, v___x_3669_);
v___x_3685_ = v_reuseFailAlloc_3686_;
goto v_reusejp_3684_;
}
v_reusejp_3684_:
{
return v___x_3685_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__6___boxed(lean_object* v_cls_3692_, lean_object* v_msg_3693_, lean_object* v___y_3694_, lean_object* v___y_3695_, lean_object* v___y_3696_){
_start:
{
lean_object* v_res_3697_; 
v_res_3697_ = l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__6(v_cls_3692_, v_msg_3693_, v___y_3694_, v___y_3695_);
lean_dec(v___y_3695_);
lean_dec_ref(v___y_3694_);
return v_res_3697_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__4(size_t v_sz_3698_, size_t v_i_3699_, lean_object* v_bs_3700_){
_start:
{
uint8_t v___x_3701_; 
v___x_3701_ = lean_usize_dec_lt(v_i_3699_, v_sz_3698_);
if (v___x_3701_ == 0)
{
return v_bs_3700_;
}
else
{
lean_object* v_v_3702_; lean_object* v___x_3703_; lean_object* v_bs_x27_3704_; lean_object* v___x_3705_; lean_object* v___x_3706_; size_t v___x_3707_; size_t v___x_3708_; lean_object* v___x_3709_; 
v_v_3702_ = lean_array_uget(v_bs_3700_, v_i_3699_);
v___x_3703_ = lean_unsigned_to_nat(0u);
v_bs_x27_3704_ = lean_array_uset(v_bs_3700_, v_i_3699_, v___x_3703_);
v___x_3705_ = l_Lean_LocalDecl_fvarId(v_v_3702_);
lean_dec(v_v_3702_);
v___x_3706_ = l_Lean_mkFVar(v___x_3705_);
v___x_3707_ = ((size_t)1ULL);
v___x_3708_ = lean_usize_add(v_i_3699_, v___x_3707_);
v___x_3709_ = lean_array_uset(v_bs_x27_3704_, v_i_3699_, v___x_3706_);
v_i_3699_ = v___x_3708_;
v_bs_3700_ = v___x_3709_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__4___boxed(lean_object* v_sz_3711_, lean_object* v_i_3712_, lean_object* v_bs_3713_){
_start:
{
size_t v_sz_boxed_3714_; size_t v_i_boxed_3715_; lean_object* v_res_3716_; 
v_sz_boxed_3714_ = lean_unbox_usize(v_sz_3711_);
lean_dec(v_sz_3711_);
v_i_boxed_3715_ = lean_unbox_usize(v_i_3712_);
lean_dec(v_i_3712_);
v_res_3716_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__4(v_sz_boxed_3714_, v_i_boxed_3715_, v_bs_3713_);
return v_res_3716_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__3(lean_object* v___x_3717_, lean_object* v_as_3718_, size_t v_sz_3719_, size_t v_i_3720_, lean_object* v_b_3721_, lean_object* v___y_3722_, lean_object* v___y_3723_, lean_object* v___y_3724_){
_start:
{
uint8_t v___x_3726_; 
v___x_3726_ = lean_usize_dec_lt(v_i_3720_, v_sz_3719_);
if (v___x_3726_ == 0)
{
lean_object* v___x_3727_; lean_object* v___x_3728_; 
lean_dec_ref(v___x_3717_);
v___x_3727_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3727_, 0, v_b_3721_);
lean_ctor_set(v___x_3727_, 1, v___y_3722_);
v___x_3728_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3728_, 0, v___x_3727_);
return v___x_3728_;
}
else
{
lean_object* v___x_3729_; lean_object* v_a_3730_; lean_object* v___x_3731_; lean_object* v___x_3732_; 
v___x_3729_ = lean_box(0);
v_a_3730_ = lean_array_uget_borrowed(v_as_3718_, v_i_3720_);
v___x_3731_ = l_Lean_LocalDecl_fvarId(v_a_3730_);
lean_inc_ref(v___x_3717_);
v___x_3732_ = l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit(v___x_3717_, v___x_3731_, v___y_3722_, v___y_3723_, v___y_3724_);
lean_dec(v___x_3731_);
if (lean_obj_tag(v___x_3732_) == 0)
{
lean_object* v_a_3733_; lean_object* v_snd_3734_; size_t v___x_3735_; size_t v___x_3736_; 
v_a_3733_ = lean_ctor_get(v___x_3732_, 0);
lean_inc(v_a_3733_);
lean_dec_ref_known(v___x_3732_, 1);
v_snd_3734_ = lean_ctor_get(v_a_3733_, 1);
lean_inc(v_snd_3734_);
lean_dec(v_a_3733_);
v___x_3735_ = ((size_t)1ULL);
v___x_3736_ = lean_usize_add(v_i_3720_, v___x_3735_);
v_i_3720_ = v___x_3736_;
v_b_3721_ = v___x_3729_;
v___y_3722_ = v_snd_3734_;
goto _start;
}
else
{
lean_dec_ref(v___x_3717_);
return v___x_3732_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__3___boxed(lean_object* v___x_3738_, lean_object* v_as_3739_, lean_object* v_sz_3740_, lean_object* v_i_3741_, lean_object* v_b_3742_, lean_object* v___y_3743_, lean_object* v___y_3744_, lean_object* v___y_3745_, lean_object* v___y_3746_){
_start:
{
size_t v_sz_boxed_3747_; size_t v_i_boxed_3748_; lean_object* v_res_3749_; 
v_sz_boxed_3747_ = lean_unbox_usize(v_sz_3740_);
lean_dec(v_sz_3740_);
v_i_boxed_3748_ = lean_unbox_usize(v_i_3741_);
lean_dec(v_i_3741_);
v_res_3749_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__3(v___x_3738_, v_as_3739_, v_sz_boxed_3747_, v_i_boxed_3748_, v_b_3742_, v___y_3743_, v___y_3744_, v___y_3745_);
lean_dec(v___y_3745_);
lean_dec_ref(v___y_3744_);
lean_dec_ref(v_as_3739_);
return v_res_3749_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__5(lean_object* v_a_3750_, lean_object* v_a_3751_){
_start:
{
if (lean_obj_tag(v_a_3750_) == 0)
{
lean_object* v___x_3752_; 
v___x_3752_ = l_List_reverse___redArg(v_a_3751_);
return v___x_3752_;
}
else
{
lean_object* v_head_3753_; lean_object* v_tail_3754_; lean_object* v___x_3756_; uint8_t v_isShared_3757_; uint8_t v_isSharedCheck_3763_; 
v_head_3753_ = lean_ctor_get(v_a_3750_, 0);
v_tail_3754_ = lean_ctor_get(v_a_3750_, 1);
v_isSharedCheck_3763_ = !lean_is_exclusive(v_a_3750_);
if (v_isSharedCheck_3763_ == 0)
{
v___x_3756_ = v_a_3750_;
v_isShared_3757_ = v_isSharedCheck_3763_;
goto v_resetjp_3755_;
}
else
{
lean_inc(v_tail_3754_);
lean_inc(v_head_3753_);
lean_dec(v_a_3750_);
v___x_3756_ = lean_box(0);
v_isShared_3757_ = v_isSharedCheck_3763_;
goto v_resetjp_3755_;
}
v_resetjp_3755_:
{
lean_object* v___x_3758_; lean_object* v___x_3760_; 
v___x_3758_ = l_Lean_MessageData_ofExpr(v_head_3753_);
if (v_isShared_3757_ == 0)
{
lean_ctor_set(v___x_3756_, 1, v_a_3751_);
lean_ctor_set(v___x_3756_, 0, v___x_3758_);
v___x_3760_ = v___x_3756_;
goto v_reusejp_3759_;
}
else
{
lean_object* v_reuseFailAlloc_3762_; 
v_reuseFailAlloc_3762_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3762_, 0, v___x_3758_);
lean_ctor_set(v_reuseFailAlloc_3762_, 1, v_a_3751_);
v___x_3760_ = v_reuseFailAlloc_3762_;
goto v_reusejp_3759_;
}
v_reusejp_3759_:
{
v_a_3750_ = v_tail_3754_;
v_a_3751_ = v___x_3760_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__0_spec__0___redArg(lean_object* v_a_3764_, lean_object* v_b_3765_, lean_object* v_x_3766_){
_start:
{
if (lean_obj_tag(v_x_3766_) == 0)
{
lean_dec(v_b_3765_);
lean_dec(v_a_3764_);
return v_x_3766_;
}
else
{
lean_object* v_key_3767_; lean_object* v_value_3768_; lean_object* v_tail_3769_; lean_object* v___x_3771_; uint8_t v_isShared_3772_; uint8_t v_isSharedCheck_3781_; 
v_key_3767_ = lean_ctor_get(v_x_3766_, 0);
v_value_3768_ = lean_ctor_get(v_x_3766_, 1);
v_tail_3769_ = lean_ctor_get(v_x_3766_, 2);
v_isSharedCheck_3781_ = !lean_is_exclusive(v_x_3766_);
if (v_isSharedCheck_3781_ == 0)
{
v___x_3771_ = v_x_3766_;
v_isShared_3772_ = v_isSharedCheck_3781_;
goto v_resetjp_3770_;
}
else
{
lean_inc(v_tail_3769_);
lean_inc(v_value_3768_);
lean_inc(v_key_3767_);
lean_dec(v_x_3766_);
v___x_3771_ = lean_box(0);
v_isShared_3772_ = v_isSharedCheck_3781_;
goto v_resetjp_3770_;
}
v_resetjp_3770_:
{
uint8_t v___x_3773_; 
v___x_3773_ = l_Lean_instBEqFVarId_beq(v_key_3767_, v_a_3764_);
if (v___x_3773_ == 0)
{
lean_object* v___x_3774_; lean_object* v___x_3776_; 
v___x_3774_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__0_spec__0___redArg(v_a_3764_, v_b_3765_, v_tail_3769_);
if (v_isShared_3772_ == 0)
{
lean_ctor_set(v___x_3771_, 2, v___x_3774_);
v___x_3776_ = v___x_3771_;
goto v_reusejp_3775_;
}
else
{
lean_object* v_reuseFailAlloc_3777_; 
v_reuseFailAlloc_3777_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3777_, 0, v_key_3767_);
lean_ctor_set(v_reuseFailAlloc_3777_, 1, v_value_3768_);
lean_ctor_set(v_reuseFailAlloc_3777_, 2, v___x_3774_);
v___x_3776_ = v_reuseFailAlloc_3777_;
goto v_reusejp_3775_;
}
v_reusejp_3775_:
{
return v___x_3776_;
}
}
else
{
lean_object* v___x_3779_; 
lean_dec(v_value_3768_);
lean_dec(v_key_3767_);
if (v_isShared_3772_ == 0)
{
lean_ctor_set(v___x_3771_, 1, v_b_3765_);
lean_ctor_set(v___x_3771_, 0, v_a_3764_);
v___x_3779_ = v___x_3771_;
goto v_reusejp_3778_;
}
else
{
lean_object* v_reuseFailAlloc_3780_; 
v_reuseFailAlloc_3780_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3780_, 0, v_a_3764_);
lean_ctor_set(v_reuseFailAlloc_3780_, 1, v_b_3765_);
lean_ctor_set(v_reuseFailAlloc_3780_, 2, v_tail_3769_);
v___x_3779_ = v_reuseFailAlloc_3780_;
goto v_reusejp_3778_;
}
v_reusejp_3778_:
{
return v___x_3779_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__0___redArg(lean_object* v_m_3782_, lean_object* v_a_3783_, lean_object* v_b_3784_){
_start:
{
lean_object* v_size_3785_; lean_object* v_buckets_3786_; lean_object* v___x_3788_; uint8_t v_isShared_3789_; uint8_t v_isSharedCheck_3829_; 
v_size_3785_ = lean_ctor_get(v_m_3782_, 0);
v_buckets_3786_ = lean_ctor_get(v_m_3782_, 1);
v_isSharedCheck_3829_ = !lean_is_exclusive(v_m_3782_);
if (v_isSharedCheck_3829_ == 0)
{
v___x_3788_ = v_m_3782_;
v_isShared_3789_ = v_isSharedCheck_3829_;
goto v_resetjp_3787_;
}
else
{
lean_inc(v_buckets_3786_);
lean_inc(v_size_3785_);
lean_dec(v_m_3782_);
v___x_3788_ = lean_box(0);
v_isShared_3789_ = v_isSharedCheck_3829_;
goto v_resetjp_3787_;
}
v_resetjp_3787_:
{
lean_object* v___x_3790_; uint64_t v___x_3791_; uint64_t v___x_3792_; uint64_t v___x_3793_; uint64_t v_fold_3794_; uint64_t v___x_3795_; uint64_t v___x_3796_; uint64_t v___x_3797_; size_t v___x_3798_; size_t v___x_3799_; size_t v___x_3800_; size_t v___x_3801_; size_t v___x_3802_; lean_object* v_bkt_3803_; uint8_t v___x_3804_; 
v___x_3790_ = lean_array_get_size(v_buckets_3786_);
v___x_3791_ = l_Lean_instHashableFVarId_hash(v_a_3783_);
v___x_3792_ = 32ULL;
v___x_3793_ = lean_uint64_shift_right(v___x_3791_, v___x_3792_);
v_fold_3794_ = lean_uint64_xor(v___x_3791_, v___x_3793_);
v___x_3795_ = 16ULL;
v___x_3796_ = lean_uint64_shift_right(v_fold_3794_, v___x_3795_);
v___x_3797_ = lean_uint64_xor(v_fold_3794_, v___x_3796_);
v___x_3798_ = lean_uint64_to_usize(v___x_3797_);
v___x_3799_ = lean_usize_of_nat(v___x_3790_);
v___x_3800_ = ((size_t)1ULL);
v___x_3801_ = lean_usize_sub(v___x_3799_, v___x_3800_);
v___x_3802_ = lean_usize_land(v___x_3798_, v___x_3801_);
v_bkt_3803_ = lean_array_uget_borrowed(v_buckets_3786_, v___x_3802_);
v___x_3804_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1_spec__2___redArg(v_a_3783_, v_bkt_3803_);
if (v___x_3804_ == 0)
{
lean_object* v___x_3805_; lean_object* v_size_x27_3806_; lean_object* v___x_3807_; lean_object* v_buckets_x27_3808_; lean_object* v___x_3809_; lean_object* v___x_3810_; lean_object* v___x_3811_; lean_object* v___x_3812_; lean_object* v___x_3813_; uint8_t v___x_3814_; 
v___x_3805_ = lean_unsigned_to_nat(1u);
v_size_x27_3806_ = lean_nat_add(v_size_3785_, v___x_3805_);
lean_dec(v_size_3785_);
lean_inc(v_bkt_3803_);
v___x_3807_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3807_, 0, v_a_3783_);
lean_ctor_set(v___x_3807_, 1, v_b_3784_);
lean_ctor_set(v___x_3807_, 2, v_bkt_3803_);
v_buckets_x27_3808_ = lean_array_uset(v_buckets_3786_, v___x_3802_, v___x_3807_);
v___x_3809_ = lean_unsigned_to_nat(4u);
v___x_3810_ = lean_nat_mul(v_size_x27_3806_, v___x_3809_);
v___x_3811_ = lean_unsigned_to_nat(3u);
v___x_3812_ = lean_nat_div(v___x_3810_, v___x_3811_);
lean_dec(v___x_3810_);
v___x_3813_ = lean_array_get_size(v_buckets_x27_3808_);
v___x_3814_ = lean_nat_dec_le(v___x_3812_, v___x_3813_);
lean_dec(v___x_3812_);
if (v___x_3814_ == 0)
{
lean_object* v_val_3815_; lean_object* v___x_3817_; 
v_val_3815_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__4___redArg(v_buckets_x27_3808_);
if (v_isShared_3789_ == 0)
{
lean_ctor_set(v___x_3788_, 1, v_val_3815_);
lean_ctor_set(v___x_3788_, 0, v_size_x27_3806_);
v___x_3817_ = v___x_3788_;
goto v_reusejp_3816_;
}
else
{
lean_object* v_reuseFailAlloc_3818_; 
v_reuseFailAlloc_3818_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3818_, 0, v_size_x27_3806_);
lean_ctor_set(v_reuseFailAlloc_3818_, 1, v_val_3815_);
v___x_3817_ = v_reuseFailAlloc_3818_;
goto v_reusejp_3816_;
}
v_reusejp_3816_:
{
return v___x_3817_;
}
}
else
{
lean_object* v___x_3820_; 
if (v_isShared_3789_ == 0)
{
lean_ctor_set(v___x_3788_, 1, v_buckets_x27_3808_);
lean_ctor_set(v___x_3788_, 0, v_size_x27_3806_);
v___x_3820_ = v___x_3788_;
goto v_reusejp_3819_;
}
else
{
lean_object* v_reuseFailAlloc_3821_; 
v_reuseFailAlloc_3821_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3821_, 0, v_size_x27_3806_);
lean_ctor_set(v_reuseFailAlloc_3821_, 1, v_buckets_x27_3808_);
v___x_3820_ = v_reuseFailAlloc_3821_;
goto v_reusejp_3819_;
}
v_reusejp_3819_:
{
return v___x_3820_;
}
}
}
else
{
lean_object* v___x_3822_; lean_object* v_buckets_x27_3823_; lean_object* v___x_3824_; lean_object* v___x_3825_; lean_object* v___x_3827_; 
lean_inc(v_bkt_3803_);
v___x_3822_ = lean_box(0);
v_buckets_x27_3823_ = lean_array_uset(v_buckets_3786_, v___x_3802_, v___x_3822_);
v___x_3824_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__0_spec__0___redArg(v_a_3783_, v_b_3784_, v_bkt_3803_);
v___x_3825_ = lean_array_uset(v_buckets_x27_3823_, v___x_3802_, v___x_3824_);
if (v_isShared_3789_ == 0)
{
lean_ctor_set(v___x_3788_, 1, v___x_3825_);
v___x_3827_ = v___x_3788_;
goto v_reusejp_3826_;
}
else
{
lean_object* v_reuseFailAlloc_3828_; 
v_reuseFailAlloc_3828_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3828_, 0, v_size_3785_);
lean_ctor_set(v_reuseFailAlloc_3828_, 1, v___x_3825_);
v___x_3827_ = v_reuseFailAlloc_3828_;
goto v_reusejp_3826_;
}
v_reusejp_3826_:
{
return v___x_3827_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__2___redArg(lean_object* v_as_3830_, size_t v_sz_3831_, size_t v_i_3832_, lean_object* v_b_3833_){
_start:
{
uint8_t v___x_3835_; 
v___x_3835_ = lean_usize_dec_lt(v_i_3832_, v_sz_3831_);
if (v___x_3835_ == 0)
{
lean_object* v___x_3836_; 
v___x_3836_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3836_, 0, v_b_3833_);
return v___x_3836_;
}
else
{
lean_object* v_snd_3837_; lean_object* v_fst_3838_; lean_object* v___x_3840_; uint8_t v_isShared_3841_; uint8_t v_isSharedCheck_3873_; 
v_snd_3837_ = lean_ctor_get(v_b_3833_, 1);
v_fst_3838_ = lean_ctor_get(v_b_3833_, 0);
v_isSharedCheck_3873_ = !lean_is_exclusive(v_b_3833_);
if (v_isSharedCheck_3873_ == 0)
{
v___x_3840_ = v_b_3833_;
v_isShared_3841_ = v_isSharedCheck_3873_;
goto v_resetjp_3839_;
}
else
{
lean_inc(v_snd_3837_);
lean_inc(v_fst_3838_);
lean_dec(v_b_3833_);
v___x_3840_ = lean_box(0);
v_isShared_3841_ = v_isSharedCheck_3873_;
goto v_resetjp_3839_;
}
v_resetjp_3839_:
{
lean_object* v_array_3842_; lean_object* v_start_3843_; lean_object* v_stop_3844_; uint8_t v___x_3845_; 
v_array_3842_ = lean_ctor_get(v_snd_3837_, 0);
v_start_3843_ = lean_ctor_get(v_snd_3837_, 1);
v_stop_3844_ = lean_ctor_get(v_snd_3837_, 2);
v___x_3845_ = lean_nat_dec_lt(v_start_3843_, v_stop_3844_);
if (v___x_3845_ == 0)
{
lean_object* v___x_3847_; 
if (v_isShared_3841_ == 0)
{
v___x_3847_ = v___x_3840_;
goto v_reusejp_3846_;
}
else
{
lean_object* v_reuseFailAlloc_3849_; 
v_reuseFailAlloc_3849_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3849_, 0, v_fst_3838_);
lean_ctor_set(v_reuseFailAlloc_3849_, 1, v_snd_3837_);
v___x_3847_ = v_reuseFailAlloc_3849_;
goto v_reusejp_3846_;
}
v_reusejp_3846_:
{
lean_object* v___x_3848_; 
v___x_3848_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3848_, 0, v___x_3847_);
return v___x_3848_;
}
}
else
{
lean_object* v___x_3851_; uint8_t v_isShared_3852_; uint8_t v_isSharedCheck_3869_; 
lean_inc(v_stop_3844_);
lean_inc(v_start_3843_);
lean_inc_ref(v_array_3842_);
v_isSharedCheck_3869_ = !lean_is_exclusive(v_snd_3837_);
if (v_isSharedCheck_3869_ == 0)
{
lean_object* v_unused_3870_; lean_object* v_unused_3871_; lean_object* v_unused_3872_; 
v_unused_3870_ = lean_ctor_get(v_snd_3837_, 2);
lean_dec(v_unused_3870_);
v_unused_3871_ = lean_ctor_get(v_snd_3837_, 1);
lean_dec(v_unused_3871_);
v_unused_3872_ = lean_ctor_get(v_snd_3837_, 0);
lean_dec(v_unused_3872_);
v___x_3851_ = v_snd_3837_;
v_isShared_3852_ = v_isSharedCheck_3869_;
goto v_resetjp_3850_;
}
else
{
lean_dec(v_snd_3837_);
v___x_3851_ = lean_box(0);
v_isShared_3852_ = v_isSharedCheck_3869_;
goto v_resetjp_3850_;
}
v_resetjp_3850_:
{
lean_object* v_a_3853_; lean_object* v___x_3854_; lean_object* v___x_3855_; lean_object* v___x_3856_; lean_object* v___x_3858_; 
v_a_3853_ = lean_array_uget_borrowed(v_as_3830_, v_i_3832_);
v___x_3854_ = lean_array_fget(v_array_3842_, v_start_3843_);
v___x_3855_ = lean_unsigned_to_nat(1u);
v___x_3856_ = lean_nat_add(v_start_3843_, v___x_3855_);
lean_dec(v_start_3843_);
if (v_isShared_3852_ == 0)
{
lean_ctor_set(v___x_3851_, 1, v___x_3856_);
v___x_3858_ = v___x_3851_;
goto v_reusejp_3857_;
}
else
{
lean_object* v_reuseFailAlloc_3868_; 
v_reuseFailAlloc_3868_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3868_, 0, v_array_3842_);
lean_ctor_set(v_reuseFailAlloc_3868_, 1, v___x_3856_);
lean_ctor_set(v_reuseFailAlloc_3868_, 2, v_stop_3844_);
v___x_3858_ = v_reuseFailAlloc_3868_;
goto v_reusejp_3857_;
}
v_reusejp_3857_:
{
lean_object* v___x_3859_; lean_object* v___x_3861_; 
v___x_3859_ = l_Lean_LocalDecl_fvarId(v_a_3853_);
lean_inc(v_a_3853_);
if (v_isShared_3841_ == 0)
{
lean_ctor_set(v___x_3840_, 1, v___x_3854_);
lean_ctor_set(v___x_3840_, 0, v_a_3853_);
v___x_3861_ = v___x_3840_;
goto v_reusejp_3860_;
}
else
{
lean_object* v_reuseFailAlloc_3867_; 
v_reuseFailAlloc_3867_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3867_, 0, v_a_3853_);
lean_ctor_set(v_reuseFailAlloc_3867_, 1, v___x_3854_);
v___x_3861_ = v_reuseFailAlloc_3867_;
goto v_reusejp_3860_;
}
v_reusejp_3860_:
{
lean_object* v___x_3862_; lean_object* v___x_3863_; size_t v___x_3864_; size_t v___x_3865_; 
v___x_3862_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__0___redArg(v_fst_3838_, v___x_3859_, v___x_3861_);
v___x_3863_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3863_, 0, v___x_3862_);
lean_ctor_set(v___x_3863_, 1, v___x_3858_);
v___x_3864_ = ((size_t)1ULL);
v___x_3865_ = lean_usize_add(v_i_3832_, v___x_3864_);
v_i_3832_ = v___x_3865_;
v_b_3833_ = v___x_3863_;
goto _start;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__2___redArg___boxed(lean_object* v_as_3874_, lean_object* v_sz_3875_, lean_object* v_i_3876_, lean_object* v_b_3877_, lean_object* v___y_3878_){
_start:
{
size_t v_sz_boxed_3879_; size_t v_i_boxed_3880_; lean_object* v_res_3881_; 
v_sz_boxed_3879_ = lean_unbox_usize(v_sz_3875_);
lean_dec(v_sz_3875_);
v_i_boxed_3880_ = lean_unbox_usize(v_i_3876_);
lean_dec(v_i_3876_);
v_res_3881_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__2___redArg(v_as_3874_, v_sz_boxed_3879_, v_i_boxed_3880_, v_b_3877_);
lean_dec_ref(v_as_3874_);
return v_res_3881_;
}
}
static lean_object* _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__2(void){
_start:
{
lean_object* v___x_3884_; lean_object* v___x_3885_; lean_object* v___x_3886_; lean_object* v___x_3887_; lean_object* v___x_3888_; lean_object* v___x_3889_; 
v___x_3884_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__1));
v___x_3885_ = lean_unsigned_to_nat(2u);
v___x_3886_ = lean_unsigned_to_nat(372u);
v___x_3887_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__0));
v___x_3888_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__2));
v___x_3889_ = l_mkPanicMessageWithDecl(v___x_3888_, v___x_3887_, v___x_3886_, v___x_3885_, v___x_3884_);
return v___x_3889_;
}
}
static lean_object* _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__4(void){
_start:
{
lean_object* v___x_3891_; lean_object* v___x_3892_; lean_object* v___x_3893_; lean_object* v___x_3894_; lean_object* v___x_3895_; lean_object* v___x_3896_; 
v___x_3891_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__3));
v___x_3892_ = lean_unsigned_to_nat(2u);
v___x_3893_ = lean_unsigned_to_nat(373u);
v___x_3894_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__0));
v___x_3895_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__2));
v___x_3896_ = l_mkPanicMessageWithDecl(v___x_3895_, v___x_3894_, v___x_3893_, v___x_3892_, v___x_3891_);
return v___x_3896_;
}
}
static lean_object* _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__5(void){
_start:
{
lean_object* v___x_3897_; lean_object* v___x_3898_; lean_object* v___x_3899_; 
v___x_3897_ = lean_box(0);
v___x_3898_ = lean_unsigned_to_nat(16u);
v___x_3899_ = lean_mk_array(v___x_3898_, v___x_3897_);
return v___x_3899_;
}
}
static lean_object* _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__6(void){
_start:
{
lean_object* v___x_3900_; lean_object* v___x_3901_; lean_object* v___x_3902_; 
v___x_3900_ = lean_obj_once(&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__5, &l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__5_once, _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__5);
v___x_3901_ = lean_unsigned_to_nat(0u);
v___x_3902_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3902_, 0, v___x_3901_);
lean_ctor_set(v___x_3902_, 1, v___x_3900_);
return v___x_3902_;
}
}
static lean_object* _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__8(void){
_start:
{
lean_object* v___x_3904_; lean_object* v___x_3905_; 
v___x_3904_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__7));
v___x_3905_ = l_Lean_stringToMessageData(v___x_3904_);
return v___x_3905_;
}
}
static lean_object* _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__10(void){
_start:
{
lean_object* v___x_3907_; lean_object* v___x_3908_; 
v___x_3907_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__9));
v___x_3908_ = l_Lean_stringToMessageData(v___x_3907_);
return v___x_3908_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls(lean_object* v_sortedDecls_3909_, lean_object* v_sortedArgs_3910_, lean_object* v_toSortDecls_3911_, lean_object* v_toSortArgs_3912_, lean_object* v_a_3913_, lean_object* v_a_3914_){
_start:
{
lean_object* v___y_3917_; lean_object* v___y_3936_; lean_object* v___y_3937_; lean_object* v___y_3938_; lean_object* v___y_3939_; lean_object* v_snd_3940_; lean_object* v___x_3942_; lean_object* v___x_3943_; uint8_t v___x_3944_; 
v___x_3942_ = lean_array_get_size(v_sortedDecls_3909_);
v___x_3943_ = lean_array_get_size(v_sortedArgs_3910_);
v___x_3944_ = lean_nat_dec_eq(v___x_3942_, v___x_3943_);
if (v___x_3944_ == 0)
{
lean_object* v___x_3945_; lean_object* v___x_3946_; 
lean_dec_ref(v_toSortArgs_3912_);
lean_dec_ref(v_sortedArgs_3910_);
lean_dec_ref(v_sortedDecls_3909_);
v___x_3945_ = lean_obj_once(&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__2, &l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__2_once, _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__2);
v___x_3946_ = l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__1(v___x_3945_, v_a_3913_, v_a_3914_);
return v___x_3946_;
}
else
{
lean_object* v___x_3947_; lean_object* v___x_3948_; uint8_t v___x_3949_; 
v___x_3947_ = lean_array_get_size(v_toSortDecls_3911_);
v___x_3948_ = lean_array_get_size(v_toSortArgs_3912_);
v___x_3949_ = lean_nat_dec_eq(v___x_3947_, v___x_3948_);
if (v___x_3949_ == 0)
{
lean_object* v___x_3950_; lean_object* v___x_3951_; 
lean_dec_ref(v_toSortArgs_3912_);
lean_dec_ref(v_sortedArgs_3910_);
lean_dec_ref(v_sortedDecls_3909_);
v___x_3950_ = lean_obj_once(&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__4, &l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__4_once, _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__4);
v___x_3951_ = l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__1(v___x_3950_, v_a_3913_, v_a_3914_);
return v___x_3951_;
}
else
{
lean_object* v___x_3952_; uint8_t v___x_3953_; 
v___x_3952_ = lean_unsigned_to_nat(0u);
v___x_3953_ = lean_nat_dec_eq(v___x_3947_, v___x_3952_);
if (v___x_3953_ == 0)
{
lean_object* v_toCold_3954_; lean_object* v_options_3955_; lean_object* v_inheritedTraceOptions_3956_; uint8_t v_hasTrace_3957_; lean_object* v___x_3958_; lean_object* v_cls_3959_; lean_object* v___y_3961_; lean_object* v___y_3962_; 
v_toCold_3954_ = lean_ctor_get(v_a_3913_, 0);
v_options_3955_ = lean_ctor_get(v_toCold_3954_, 2);
v_inheritedTraceOptions_3956_ = lean_ctor_get(v_toCold_3954_, 11);
v_hasTrace_3957_ = lean_ctor_get_uint8(v_options_3955_, sizeof(void*)*1);
v___x_3958_ = l_Lean_instEmptyCollectionFVarIdHashSet;
v_cls_3959_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__10));
if (v_hasTrace_3957_ == 0)
{
v___y_3961_ = v_a_3913_;
v___y_3962_ = v_a_3914_;
goto v___jp_3960_;
}
else
{
lean_object* v___x_4063_; uint8_t v___x_4064_; 
v___x_4063_ = lean_obj_once(&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__13, &l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__13_once, _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__13);
v___x_4064_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3956_, v_options_3955_, v___x_4063_);
if (v___x_4064_ == 0)
{
v___y_3961_ = v_a_3913_;
v___y_3962_ = v_a_3914_;
goto v___jp_3960_;
}
else
{
lean_object* v___x_4065_; lean_object* v___x_4066_; 
v___x_4065_ = lean_obj_once(&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__10, &l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__10_once, _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__10);
v___x_4066_ = l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__6(v_cls_3959_, v___x_4065_, v_a_3913_, v_a_3914_);
if (lean_obj_tag(v___x_4066_) == 0)
{
lean_dec_ref_known(v___x_4066_, 1);
v___y_3961_ = v_a_3913_;
v___y_3962_ = v_a_3914_;
goto v___jp_3960_;
}
else
{
lean_object* v_a_4067_; lean_object* v___x_4069_; uint8_t v_isShared_4070_; uint8_t v_isSharedCheck_4074_; 
lean_dec_ref(v_toSortArgs_3912_);
lean_dec_ref(v_sortedArgs_3910_);
lean_dec_ref(v_sortedDecls_3909_);
v_a_4067_ = lean_ctor_get(v___x_4066_, 0);
v_isSharedCheck_4074_ = !lean_is_exclusive(v___x_4066_);
if (v_isSharedCheck_4074_ == 0)
{
v___x_4069_ = v___x_4066_;
v_isShared_4070_ = v_isSharedCheck_4074_;
goto v_resetjp_4068_;
}
else
{
lean_inc(v_a_4067_);
lean_dec(v___x_4066_);
v___x_4069_ = lean_box(0);
v_isShared_4070_ = v_isSharedCheck_4074_;
goto v_resetjp_4068_;
}
v_resetjp_4068_:
{
lean_object* v___x_4072_; 
if (v_isShared_4070_ == 0)
{
v___x_4072_ = v___x_4069_;
goto v_reusejp_4071_;
}
else
{
lean_object* v_reuseFailAlloc_4073_; 
v_reuseFailAlloc_4073_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4073_, 0, v_a_4067_);
v___x_4072_ = v_reuseFailAlloc_4073_;
goto v_reusejp_4071_;
}
v_reusejp_4071_:
{
return v___x_4072_;
}
}
}
}
}
v___jp_3960_:
{
lean_object* v___x_3963_; lean_object* v___x_3964_; lean_object* v___x_3965_; size_t v_sz_3966_; size_t v___x_3967_; lean_object* v___x_3968_; 
v___x_3963_ = lean_obj_once(&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__6, &l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__6_once, _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__6);
v___x_3964_ = l_Array_toSubarray___redArg(v_sortedArgs_3910_, v___x_3952_, v___x_3943_);
v___x_3965_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3965_, 0, v___x_3963_);
lean_ctor_set(v___x_3965_, 1, v___x_3964_);
v_sz_3966_ = lean_array_size(v_sortedDecls_3909_);
v___x_3967_ = ((size_t)0ULL);
v___x_3968_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__2___redArg(v_sortedDecls_3909_, v_sz_3966_, v___x_3967_, v___x_3965_);
if (lean_obj_tag(v___x_3968_) == 0)
{
lean_object* v_a_3969_; lean_object* v_fst_3970_; lean_object* v___x_3972_; uint8_t v_isShared_3973_; uint8_t v_isSharedCheck_4053_; 
v_a_3969_ = lean_ctor_get(v___x_3968_, 0);
lean_inc(v_a_3969_);
lean_dec_ref_known(v___x_3968_, 1);
v_fst_3970_ = lean_ctor_get(v_a_3969_, 0);
v_isSharedCheck_4053_ = !lean_is_exclusive(v_a_3969_);
if (v_isSharedCheck_4053_ == 0)
{
lean_object* v_unused_4054_; 
v_unused_4054_ = lean_ctor_get(v_a_3969_, 1);
lean_dec(v_unused_4054_);
v___x_3972_ = v_a_3969_;
v_isShared_3973_ = v_isSharedCheck_4053_;
goto v_resetjp_3971_;
}
else
{
lean_inc(v_fst_3970_);
lean_dec(v_a_3969_);
v___x_3972_ = lean_box(0);
v_isShared_3973_ = v_isSharedCheck_4053_;
goto v_resetjp_3971_;
}
v_resetjp_3971_:
{
lean_object* v___x_3974_; lean_object* v___x_3976_; 
v___x_3974_ = l_Array_toSubarray___redArg(v_toSortArgs_3912_, v___x_3952_, v___x_3948_);
if (v_isShared_3973_ == 0)
{
lean_ctor_set(v___x_3972_, 1, v___x_3974_);
v___x_3976_ = v___x_3972_;
goto v_reusejp_3975_;
}
else
{
lean_object* v_reuseFailAlloc_4052_; 
v_reuseFailAlloc_4052_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4052_, 0, v_fst_3970_);
lean_ctor_set(v_reuseFailAlloc_4052_, 1, v___x_3974_);
v___x_3976_ = v_reuseFailAlloc_4052_;
goto v_reusejp_3975_;
}
v_reusejp_3975_:
{
size_t v_sz_3977_; lean_object* v___x_3978_; 
v_sz_3977_ = lean_array_size(v_toSortDecls_3911_);
v___x_3978_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__2___redArg(v_toSortDecls_3911_, v_sz_3977_, v___x_3967_, v___x_3976_);
if (lean_obj_tag(v___x_3978_) == 0)
{
lean_object* v_a_3979_; lean_object* v_fst_3980_; lean_object* v_size_3981_; lean_object* v___x_3982_; lean_object* v___x_3983_; lean_object* v___x_3984_; lean_object* v___x_3985_; 
v_a_3979_ = lean_ctor_get(v___x_3978_, 0);
lean_inc(v_a_3979_);
lean_dec_ref_known(v___x_3978_, 1);
v_fst_3980_ = lean_ctor_get(v_a_3979_, 0);
lean_inc_n(v_fst_3980_, 2);
lean_dec(v_a_3979_);
v_size_3981_ = lean_ctor_get(v_fst_3980_, 0);
v___x_3982_ = lean_mk_empty_array_with_capacity(v_size_3981_);
lean_inc_ref(v___x_3982_);
v___x_3983_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3983_, 0, v___x_3958_);
lean_ctor_set(v___x_3983_, 1, v___x_3958_);
lean_ctor_set(v___x_3983_, 2, v___x_3982_);
lean_ctor_set(v___x_3983_, 3, v___x_3982_);
v___x_3984_ = lean_box(0);
v___x_3985_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__3(v_fst_3980_, v_sortedDecls_3909_, v_sz_3966_, v___x_3967_, v___x_3984_, v___x_3983_, v___y_3961_, v___y_3962_);
lean_dec_ref(v_sortedDecls_3909_);
if (lean_obj_tag(v___x_3985_) == 0)
{
lean_object* v_a_3986_; lean_object* v_snd_3987_; lean_object* v___x_3988_; 
v_a_3986_ = lean_ctor_get(v___x_3985_, 0);
lean_inc(v_a_3986_);
lean_dec_ref_known(v___x_3985_, 1);
v_snd_3987_ = lean_ctor_get(v_a_3986_, 1);
lean_inc(v_snd_3987_);
lean_dec(v_a_3986_);
v___x_3988_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__3(v_fst_3980_, v_toSortDecls_3911_, v_sz_3977_, v___x_3967_, v___x_3984_, v_snd_3987_, v___y_3961_, v___y_3962_);
if (lean_obj_tag(v___x_3988_) == 0)
{
lean_object* v_a_3989_; lean_object* v_snd_3990_; lean_object* v___x_3992_; uint8_t v_isShared_3993_; uint8_t v_isSharedCheck_4026_; 
v_a_3989_ = lean_ctor_get(v___x_3988_, 0);
lean_inc(v_a_3989_);
lean_dec_ref_known(v___x_3988_, 1);
v_snd_3990_ = lean_ctor_get(v_a_3989_, 1);
v_isSharedCheck_4026_ = !lean_is_exclusive(v_a_3989_);
if (v_isSharedCheck_4026_ == 0)
{
lean_object* v_unused_4027_; 
v_unused_4027_ = lean_ctor_get(v_a_3989_, 0);
lean_dec(v_unused_4027_);
v___x_3992_ = v_a_3989_;
v_isShared_3993_ = v_isSharedCheck_4026_;
goto v_resetjp_3991_;
}
else
{
lean_inc(v_snd_3990_);
lean_dec(v_a_3989_);
v___x_3992_ = lean_box(0);
v_isShared_3993_ = v_isSharedCheck_4026_;
goto v_resetjp_3991_;
}
v_resetjp_3991_:
{
lean_object* v_toCold_3994_; lean_object* v_options_3995_; lean_object* v_newDecls_3996_; lean_object* v_newArgs_3997_; lean_object* v_inheritedTraceOptions_3998_; uint8_t v_hasTrace_3999_; lean_object* v___f_4000_; 
v_toCold_3994_ = lean_ctor_get(v___y_3961_, 0);
v_options_3995_ = lean_ctor_get(v_toCold_3994_, 2);
v_newDecls_3996_ = lean_ctor_get(v_snd_3990_, 2);
v_newArgs_3997_ = lean_ctor_get(v_snd_3990_, 3);
v_inheritedTraceOptions_3998_ = lean_ctor_get(v_toCold_3994_, 11);
v_hasTrace_3999_ = lean_ctor_get_uint8(v_options_3995_, sizeof(void*)*1);
lean_inc_ref(v_newArgs_3997_);
lean_inc_ref(v_newDecls_3996_);
v___f_4000_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___lam__0___boxed), 7, 2);
lean_closure_set(v___f_4000_, 0, v_newDecls_3996_);
lean_closure_set(v___f_4000_, 1, v_newArgs_3997_);
if (v_hasTrace_3999_ == 0)
{
lean_del_object(v___x_3992_);
v___y_3936_ = v___f_4000_;
v___y_3937_ = v___y_3962_;
v___y_3938_ = v___y_3961_;
v___y_3939_ = v___x_3984_;
v_snd_3940_ = v_snd_3990_;
goto v___jp_3935_;
}
else
{
lean_object* v___x_4001_; uint8_t v___x_4002_; 
v___x_4001_ = lean_obj_once(&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__13, &l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__13_once, _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__13);
v___x_4002_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3998_, v_options_3995_, v___x_4001_);
if (v___x_4002_ == 0)
{
lean_del_object(v___x_3992_);
v___y_3936_ = v___f_4000_;
v___y_3937_ = v___y_3962_;
v___y_3938_ = v___y_3961_;
v___y_3939_ = v___x_3984_;
v_snd_3940_ = v_snd_3990_;
goto v___jp_3935_;
}
else
{
lean_object* v___x_4003_; size_t v_sz_4004_; lean_object* v___x_4005_; lean_object* v___x_4006_; lean_object* v___x_4007_; lean_object* v___x_4008_; lean_object* v___x_4009_; lean_object* v___x_4011_; 
lean_inc_ref(v_newArgs_3997_);
lean_inc_ref_n(v_newDecls_3996_, 2);
lean_dec_ref(v___f_4000_);
v___x_4003_ = lean_obj_once(&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__8, &l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__8_once, _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__8);
v_sz_4004_ = lean_array_size(v_newDecls_3996_);
v___x_4005_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__4(v_sz_4004_, v___x_3967_, v_newDecls_3996_);
v___x_4006_ = lean_array_to_list(v___x_4005_);
v___x_4007_ = lean_box(0);
v___x_4008_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__5(v___x_4006_, v___x_4007_);
v___x_4009_ = l_Lean_MessageData_ofList(v___x_4008_);
if (v_isShared_3993_ == 0)
{
lean_ctor_set_tag(v___x_3992_, 7);
lean_ctor_set(v___x_3992_, 1, v___x_4009_);
lean_ctor_set(v___x_3992_, 0, v___x_4003_);
v___x_4011_ = v___x_3992_;
goto v_reusejp_4010_;
}
else
{
lean_object* v_reuseFailAlloc_4025_; 
v_reuseFailAlloc_4025_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4025_, 0, v___x_4003_);
lean_ctor_set(v_reuseFailAlloc_4025_, 1, v___x_4009_);
v___x_4011_ = v_reuseFailAlloc_4025_;
goto v_reusejp_4010_;
}
v_reusejp_4010_:
{
lean_object* v___x_4012_; 
v___x_4012_ = l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6(v_cls_3959_, v___x_4011_, v_snd_3990_, v___y_3961_, v___y_3962_);
if (lean_obj_tag(v___x_4012_) == 0)
{
lean_object* v_a_4013_; lean_object* v_fst_4014_; lean_object* v_snd_4015_; lean_object* v___x_4016_; 
v_a_4013_ = lean_ctor_get(v___x_4012_, 0);
lean_inc(v_a_4013_);
lean_dec_ref_known(v___x_4012_, 1);
v_fst_4014_ = lean_ctor_get(v_a_4013_, 0);
lean_inc(v_fst_4014_);
v_snd_4015_ = lean_ctor_get(v_a_4013_, 1);
lean_inc(v_snd_4015_);
lean_dec(v_a_4013_);
v___x_4016_ = l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___lam__0(v_newDecls_3996_, v_newArgs_3997_, v_fst_4014_, v_snd_4015_, v___y_3961_, v___y_3962_);
v___y_3917_ = v___x_4016_;
goto v___jp_3916_;
}
else
{
lean_object* v_a_4017_; lean_object* v___x_4019_; uint8_t v_isShared_4020_; uint8_t v_isSharedCheck_4024_; 
lean_dec_ref(v_newArgs_3997_);
lean_dec_ref(v_newDecls_3996_);
v_a_4017_ = lean_ctor_get(v___x_4012_, 0);
v_isSharedCheck_4024_ = !lean_is_exclusive(v___x_4012_);
if (v_isSharedCheck_4024_ == 0)
{
v___x_4019_ = v___x_4012_;
v_isShared_4020_ = v_isSharedCheck_4024_;
goto v_resetjp_4018_;
}
else
{
lean_inc(v_a_4017_);
lean_dec(v___x_4012_);
v___x_4019_ = lean_box(0);
v_isShared_4020_ = v_isSharedCheck_4024_;
goto v_resetjp_4018_;
}
v_resetjp_4018_:
{
lean_object* v___x_4022_; 
if (v_isShared_4020_ == 0)
{
v___x_4022_ = v___x_4019_;
goto v_reusejp_4021_;
}
else
{
lean_object* v_reuseFailAlloc_4023_; 
v_reuseFailAlloc_4023_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4023_, 0, v_a_4017_);
v___x_4022_ = v_reuseFailAlloc_4023_;
goto v_reusejp_4021_;
}
v_reusejp_4021_:
{
return v___x_4022_;
}
}
}
}
}
}
}
}
else
{
lean_object* v_a_4028_; lean_object* v___x_4030_; uint8_t v_isShared_4031_; uint8_t v_isSharedCheck_4035_; 
v_a_4028_ = lean_ctor_get(v___x_3988_, 0);
v_isSharedCheck_4035_ = !lean_is_exclusive(v___x_3988_);
if (v_isSharedCheck_4035_ == 0)
{
v___x_4030_ = v___x_3988_;
v_isShared_4031_ = v_isSharedCheck_4035_;
goto v_resetjp_4029_;
}
else
{
lean_inc(v_a_4028_);
lean_dec(v___x_3988_);
v___x_4030_ = lean_box(0);
v_isShared_4031_ = v_isSharedCheck_4035_;
goto v_resetjp_4029_;
}
v_resetjp_4029_:
{
lean_object* v___x_4033_; 
if (v_isShared_4031_ == 0)
{
v___x_4033_ = v___x_4030_;
goto v_reusejp_4032_;
}
else
{
lean_object* v_reuseFailAlloc_4034_; 
v_reuseFailAlloc_4034_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4034_, 0, v_a_4028_);
v___x_4033_ = v_reuseFailAlloc_4034_;
goto v_reusejp_4032_;
}
v_reusejp_4032_:
{
return v___x_4033_;
}
}
}
}
else
{
lean_object* v_a_4036_; lean_object* v___x_4038_; uint8_t v_isShared_4039_; uint8_t v_isSharedCheck_4043_; 
lean_dec(v_fst_3980_);
v_a_4036_ = lean_ctor_get(v___x_3985_, 0);
v_isSharedCheck_4043_ = !lean_is_exclusive(v___x_3985_);
if (v_isSharedCheck_4043_ == 0)
{
v___x_4038_ = v___x_3985_;
v_isShared_4039_ = v_isSharedCheck_4043_;
goto v_resetjp_4037_;
}
else
{
lean_inc(v_a_4036_);
lean_dec(v___x_3985_);
v___x_4038_ = lean_box(0);
v_isShared_4039_ = v_isSharedCheck_4043_;
goto v_resetjp_4037_;
}
v_resetjp_4037_:
{
lean_object* v___x_4041_; 
if (v_isShared_4039_ == 0)
{
v___x_4041_ = v___x_4038_;
goto v_reusejp_4040_;
}
else
{
lean_object* v_reuseFailAlloc_4042_; 
v_reuseFailAlloc_4042_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4042_, 0, v_a_4036_);
v___x_4041_ = v_reuseFailAlloc_4042_;
goto v_reusejp_4040_;
}
v_reusejp_4040_:
{
return v___x_4041_;
}
}
}
}
else
{
lean_object* v_a_4044_; lean_object* v___x_4046_; uint8_t v_isShared_4047_; uint8_t v_isSharedCheck_4051_; 
lean_dec_ref(v_sortedDecls_3909_);
v_a_4044_ = lean_ctor_get(v___x_3978_, 0);
v_isSharedCheck_4051_ = !lean_is_exclusive(v___x_3978_);
if (v_isSharedCheck_4051_ == 0)
{
v___x_4046_ = v___x_3978_;
v_isShared_4047_ = v_isSharedCheck_4051_;
goto v_resetjp_4045_;
}
else
{
lean_inc(v_a_4044_);
lean_dec(v___x_3978_);
v___x_4046_ = lean_box(0);
v_isShared_4047_ = v_isSharedCheck_4051_;
goto v_resetjp_4045_;
}
v_resetjp_4045_:
{
lean_object* v___x_4049_; 
if (v_isShared_4047_ == 0)
{
v___x_4049_ = v___x_4046_;
goto v_reusejp_4048_;
}
else
{
lean_object* v_reuseFailAlloc_4050_; 
v_reuseFailAlloc_4050_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4050_, 0, v_a_4044_);
v___x_4049_ = v_reuseFailAlloc_4050_;
goto v_reusejp_4048_;
}
v_reusejp_4048_:
{
return v___x_4049_;
}
}
}
}
}
}
else
{
lean_object* v_a_4055_; lean_object* v___x_4057_; uint8_t v_isShared_4058_; uint8_t v_isSharedCheck_4062_; 
lean_dec_ref(v_toSortArgs_3912_);
lean_dec_ref(v_sortedDecls_3909_);
v_a_4055_ = lean_ctor_get(v___x_3968_, 0);
v_isSharedCheck_4062_ = !lean_is_exclusive(v___x_3968_);
if (v_isSharedCheck_4062_ == 0)
{
v___x_4057_ = v___x_3968_;
v_isShared_4058_ = v_isSharedCheck_4062_;
goto v_resetjp_4056_;
}
else
{
lean_inc(v_a_4055_);
lean_dec(v___x_3968_);
v___x_4057_ = lean_box(0);
v_isShared_4058_ = v_isSharedCheck_4062_;
goto v_resetjp_4056_;
}
v_resetjp_4056_:
{
lean_object* v___x_4060_; 
if (v_isShared_4058_ == 0)
{
v___x_4060_ = v___x_4057_;
goto v_reusejp_4059_;
}
else
{
lean_object* v_reuseFailAlloc_4061_; 
v_reuseFailAlloc_4061_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4061_, 0, v_a_4055_);
v___x_4060_ = v_reuseFailAlloc_4061_;
goto v_reusejp_4059_;
}
v_reusejp_4059_:
{
return v___x_4060_;
}
}
}
}
}
else
{
lean_object* v___x_4075_; lean_object* v___x_4076_; 
lean_dec_ref(v_toSortArgs_3912_);
v___x_4075_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4075_, 0, v_sortedDecls_3909_);
lean_ctor_set(v___x_4075_, 1, v_sortedArgs_3910_);
v___x_4076_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4076_, 0, v___x_4075_);
return v___x_4076_;
}
}
}
v___jp_3916_:
{
if (lean_obj_tag(v___y_3917_) == 0)
{
lean_object* v_a_3918_; lean_object* v___x_3920_; uint8_t v_isShared_3921_; uint8_t v_isSharedCheck_3926_; 
v_a_3918_ = lean_ctor_get(v___y_3917_, 0);
v_isSharedCheck_3926_ = !lean_is_exclusive(v___y_3917_);
if (v_isSharedCheck_3926_ == 0)
{
v___x_3920_ = v___y_3917_;
v_isShared_3921_ = v_isSharedCheck_3926_;
goto v_resetjp_3919_;
}
else
{
lean_inc(v_a_3918_);
lean_dec(v___y_3917_);
v___x_3920_ = lean_box(0);
v_isShared_3921_ = v_isSharedCheck_3926_;
goto v_resetjp_3919_;
}
v_resetjp_3919_:
{
lean_object* v_fst_3922_; lean_object* v___x_3924_; 
v_fst_3922_ = lean_ctor_get(v_a_3918_, 0);
lean_inc(v_fst_3922_);
lean_dec(v_a_3918_);
if (v_isShared_3921_ == 0)
{
lean_ctor_set(v___x_3920_, 0, v_fst_3922_);
v___x_3924_ = v___x_3920_;
goto v_reusejp_3923_;
}
else
{
lean_object* v_reuseFailAlloc_3925_; 
v_reuseFailAlloc_3925_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3925_, 0, v_fst_3922_);
v___x_3924_ = v_reuseFailAlloc_3925_;
goto v_reusejp_3923_;
}
v_reusejp_3923_:
{
return v___x_3924_;
}
}
}
else
{
lean_object* v_a_3927_; lean_object* v___x_3929_; uint8_t v_isShared_3930_; uint8_t v_isSharedCheck_3934_; 
v_a_3927_ = lean_ctor_get(v___y_3917_, 0);
v_isSharedCheck_3934_ = !lean_is_exclusive(v___y_3917_);
if (v_isSharedCheck_3934_ == 0)
{
v___x_3929_ = v___y_3917_;
v_isShared_3930_ = v_isSharedCheck_3934_;
goto v_resetjp_3928_;
}
else
{
lean_inc(v_a_3927_);
lean_dec(v___y_3917_);
v___x_3929_ = lean_box(0);
v_isShared_3930_ = v_isSharedCheck_3934_;
goto v_resetjp_3928_;
}
v_resetjp_3928_:
{
lean_object* v___x_3932_; 
if (v_isShared_3930_ == 0)
{
v___x_3932_ = v___x_3929_;
goto v_reusejp_3931_;
}
else
{
lean_object* v_reuseFailAlloc_3933_; 
v_reuseFailAlloc_3933_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3933_, 0, v_a_3927_);
v___x_3932_ = v_reuseFailAlloc_3933_;
goto v_reusejp_3931_;
}
v_reusejp_3931_:
{
return v___x_3932_;
}
}
}
}
v___jp_3935_:
{
lean_object* v___x_3941_; 
lean_inc(v___y_3937_);
lean_inc_ref(v___y_3938_);
v___x_3941_ = lean_apply_5(v___y_3936_, v___y_3939_, v_snd_3940_, v___y_3938_, v___y_3937_, lean_box(0));
v___y_3917_ = v___x_3941_;
goto v___jp_3916_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___boxed(lean_object* v_sortedDecls_4077_, lean_object* v_sortedArgs_4078_, lean_object* v_toSortDecls_4079_, lean_object* v_toSortArgs_4080_, lean_object* v_a_4081_, lean_object* v_a_4082_, lean_object* v_a_4083_){
_start:
{
lean_object* v_res_4084_; 
v_res_4084_ = l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls(v_sortedDecls_4077_, v_sortedArgs_4078_, v_toSortDecls_4079_, v_toSortArgs_4080_, v_a_4081_, v_a_4082_);
lean_dec(v_a_4082_);
lean_dec_ref(v_a_4081_);
lean_dec_ref(v_toSortDecls_4079_);
return v_res_4084_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__0(lean_object* v_00_u03b2_4085_, lean_object* v_m_4086_, lean_object* v_a_4087_, lean_object* v_b_4088_){
_start:
{
lean_object* v___x_4089_; 
v___x_4089_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__0___redArg(v_m_4086_, v_a_4087_, v_b_4088_);
return v___x_4089_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__2(lean_object* v_as_4090_, size_t v_sz_4091_, size_t v_i_4092_, lean_object* v_b_4093_, lean_object* v___y_4094_, lean_object* v___y_4095_){
_start:
{
lean_object* v___x_4097_; 
v___x_4097_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__2___redArg(v_as_4090_, v_sz_4091_, v_i_4092_, v_b_4093_);
return v___x_4097_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__2___boxed(lean_object* v_as_4098_, lean_object* v_sz_4099_, lean_object* v_i_4100_, lean_object* v_b_4101_, lean_object* v___y_4102_, lean_object* v___y_4103_, lean_object* v___y_4104_){
_start:
{
size_t v_sz_boxed_4105_; size_t v_i_boxed_4106_; lean_object* v_res_4107_; 
v_sz_boxed_4105_ = lean_unbox_usize(v_sz_4099_);
lean_dec(v_sz_4099_);
v_i_boxed_4106_ = lean_unbox_usize(v_i_4100_);
lean_dec(v_i_4100_);
v_res_4107_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__2(v_as_4098_, v_sz_boxed_4105_, v_i_boxed_4106_, v_b_4101_, v___y_4102_, v___y_4103_);
lean_dec(v___y_4103_);
lean_dec_ref(v___y_4102_);
lean_dec_ref(v_as_4098_);
return v_res_4107_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__0_spec__0(lean_object* v_00_u03b2_4108_, lean_object* v_a_4109_, lean_object* v_b_4110_, lean_object* v_x_4111_){
_start:
{
lean_object* v___x_4112_; 
v___x_4112_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__0_spec__0___redArg(v_a_4109_, v_b_4110_, v_x_4111_);
return v___x_4112_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Closure_mkValueTypeClosure_spec__1(lean_object* v_msg_4114_, lean_object* v___y_4115_, lean_object* v___y_4116_, lean_object* v___y_4117_, lean_object* v___y_4118_){
_start:
{
lean_object* v___f_4120_; lean_object* v___x_1735__overap_4121_; lean_object* v___x_4122_; 
v___f_4120_ = ((lean_object*)(l_panic___at___00Lean_Meta_Closure_mkValueTypeClosure_spec__1___closed__0));
v___x_1735__overap_4121_ = lean_panic_fn_borrowed(v___f_4120_, v_msg_4114_);
lean_inc(v___y_4118_);
lean_inc_ref(v___y_4117_);
lean_inc(v___y_4116_);
lean_inc_ref(v___y_4115_);
v___x_4122_ = lean_apply_5(v___x_1735__overap_4121_, v___y_4115_, v___y_4116_, v___y_4117_, v___y_4118_, lean_box(0));
return v___x_4122_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Closure_mkValueTypeClosure_spec__1___boxed(lean_object* v_msg_4123_, lean_object* v___y_4124_, lean_object* v___y_4125_, lean_object* v___y_4126_, lean_object* v___y_4127_, lean_object* v___y_4128_){
_start:
{
lean_object* v_res_4129_; 
v_res_4129_ = l_panic___at___00Lean_Meta_Closure_mkValueTypeClosure_spec__1(v_msg_4123_, v___y_4124_, v___y_4125_, v___y_4126_, v___y_4127_);
lean_dec(v___y_4127_);
lean_dec_ref(v___y_4126_);
lean_dec(v___y_4125_);
lean_dec_ref(v___y_4124_);
return v_res_4129_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_Meta_Closure_mkValueTypeClosure_spec__0_spec__1(lean_object* v_as_4130_, size_t v_i_4131_, size_t v_stop_4132_){
_start:
{
uint8_t v___x_4137_; 
v___x_4137_ = lean_usize_dec_eq(v_i_4131_, v_stop_4132_);
if (v___x_4137_ == 0)
{
lean_object* v___x_4138_; 
v___x_4138_ = lean_array_uget_borrowed(v_as_4130_, v_i_4131_);
if (lean_obj_tag(v___x_4138_) == 0)
{
goto v___jp_4133_;
}
else
{
lean_object* v_val_4139_; uint8_t v___x_4140_; 
v_val_4139_ = lean_ctor_get(v___x_4138_, 0);
v___x_4140_ = l_Lean_LocalDecl_isLet(v_val_4139_, v___x_4137_);
if (v___x_4140_ == 0)
{
goto v___jp_4133_;
}
else
{
return v___x_4140_;
}
}
}
else
{
uint8_t v___x_4141_; 
v___x_4141_ = 0;
return v___x_4141_;
}
v___jp_4133_:
{
size_t v___x_4134_; size_t v___x_4135_; 
v___x_4134_ = ((size_t)1ULL);
v___x_4135_ = lean_usize_add(v_i_4131_, v___x_4134_);
v_i_4131_ = v___x_4135_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_Meta_Closure_mkValueTypeClosure_spec__0_spec__1___boxed(lean_object* v_as_4142_, lean_object* v_i_4143_, lean_object* v_stop_4144_){
_start:
{
size_t v_i_boxed_4145_; size_t v_stop_boxed_4146_; uint8_t v_res_4147_; lean_object* v_r_4148_; 
v_i_boxed_4145_ = lean_unbox_usize(v_i_4143_);
lean_dec(v_i_4143_);
v_stop_boxed_4146_ = lean_unbox_usize(v_stop_4144_);
lean_dec(v_stop_4144_);
v_res_4147_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_Meta_Closure_mkValueTypeClosure_spec__0_spec__1(v_as_4142_, v_i_boxed_4145_, v_stop_boxed_4146_);
lean_dec_ref(v_as_4142_);
v_r_4148_ = lean_box(v_res_4147_);
return v_r_4148_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_Meta_Closure_mkValueTypeClosure_spec__0_spec__0(lean_object* v_x_4149_){
_start:
{
if (lean_obj_tag(v_x_4149_) == 0)
{
lean_object* v_cs_4150_; lean_object* v___x_4151_; lean_object* v___x_4152_; uint8_t v___x_4153_; 
v_cs_4150_ = lean_ctor_get(v_x_4149_, 0);
v___x_4151_ = lean_unsigned_to_nat(0u);
v___x_4152_ = lean_array_get_size(v_cs_4150_);
v___x_4153_ = lean_nat_dec_lt(v___x_4151_, v___x_4152_);
if (v___x_4153_ == 0)
{
return v___x_4153_;
}
else
{
if (v___x_4153_ == 0)
{
return v___x_4153_;
}
else
{
size_t v___x_4154_; size_t v___x_4155_; uint8_t v___x_4156_; 
v___x_4154_ = ((size_t)0ULL);
v___x_4155_ = lean_usize_of_nat(v___x_4152_);
v___x_4156_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_Meta_Closure_mkValueTypeClosure_spec__0_spec__0_spec__2(v_cs_4150_, v___x_4154_, v___x_4155_);
return v___x_4156_;
}
}
}
else
{
lean_object* v_vs_4157_; lean_object* v___x_4158_; lean_object* v___x_4159_; uint8_t v___x_4160_; 
v_vs_4157_ = lean_ctor_get(v_x_4149_, 0);
v___x_4158_ = lean_unsigned_to_nat(0u);
v___x_4159_ = lean_array_get_size(v_vs_4157_);
v___x_4160_ = lean_nat_dec_lt(v___x_4158_, v___x_4159_);
if (v___x_4160_ == 0)
{
return v___x_4160_;
}
else
{
if (v___x_4160_ == 0)
{
return v___x_4160_;
}
else
{
size_t v___x_4161_; size_t v___x_4162_; uint8_t v___x_4163_; 
v___x_4161_ = ((size_t)0ULL);
v___x_4162_ = lean_usize_of_nat(v___x_4159_);
v___x_4163_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_Meta_Closure_mkValueTypeClosure_spec__0_spec__1(v_vs_4157_, v___x_4161_, v___x_4162_);
return v___x_4163_;
}
}
}
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_Meta_Closure_mkValueTypeClosure_spec__0_spec__0_spec__2(lean_object* v_as_4164_, size_t v_i_4165_, size_t v_stop_4166_){
_start:
{
uint8_t v___x_4167_; 
v___x_4167_ = lean_usize_dec_eq(v_i_4165_, v_stop_4166_);
if (v___x_4167_ == 0)
{
lean_object* v___x_4168_; uint8_t v___x_4169_; 
v___x_4168_ = lean_array_uget_borrowed(v_as_4164_, v_i_4165_);
v___x_4169_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_Meta_Closure_mkValueTypeClosure_spec__0_spec__0(v___x_4168_);
if (v___x_4169_ == 0)
{
size_t v___x_4170_; size_t v___x_4171_; 
v___x_4170_ = ((size_t)1ULL);
v___x_4171_ = lean_usize_add(v_i_4165_, v___x_4170_);
v_i_4165_ = v___x_4171_;
goto _start;
}
else
{
return v___x_4169_;
}
}
else
{
uint8_t v___x_4173_; 
v___x_4173_ = 0;
return v___x_4173_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_Meta_Closure_mkValueTypeClosure_spec__0_spec__0_spec__2___boxed(lean_object* v_as_4174_, lean_object* v_i_4175_, lean_object* v_stop_4176_){
_start:
{
size_t v_i_boxed_4177_; size_t v_stop_boxed_4178_; uint8_t v_res_4179_; lean_object* v_r_4180_; 
v_i_boxed_4177_ = lean_unbox_usize(v_i_4175_);
lean_dec(v_i_4175_);
v_stop_boxed_4178_ = lean_unbox_usize(v_stop_4176_);
lean_dec(v_stop_4176_);
v_res_4179_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_Meta_Closure_mkValueTypeClosure_spec__0_spec__0_spec__2(v_as_4174_, v_i_boxed_4177_, v_stop_boxed_4178_);
lean_dec_ref(v_as_4174_);
v_r_4180_ = lean_box(v_res_4179_);
return v_r_4180_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_Meta_Closure_mkValueTypeClosure_spec__0_spec__0___boxed(lean_object* v_x_4181_){
_start:
{
uint8_t v_res_4182_; lean_object* v_r_4183_; 
v_res_4182_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_Meta_Closure_mkValueTypeClosure_spec__0_spec__0(v_x_4181_);
lean_dec_ref(v_x_4181_);
v_r_4183_ = lean_box(v_res_4182_);
return v_r_4183_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyM___at___00Lean_Meta_Closure_mkValueTypeClosure_spec__0(lean_object* v_t_4184_){
_start:
{
lean_object* v_root_4185_; lean_object* v_tail_4186_; uint8_t v___x_4187_; 
v_root_4185_ = lean_ctor_get(v_t_4184_, 0);
v_tail_4186_ = lean_ctor_get(v_t_4184_, 1);
v___x_4187_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_Meta_Closure_mkValueTypeClosure_spec__0_spec__0(v_root_4185_);
if (v___x_4187_ == 0)
{
lean_object* v___x_4188_; lean_object* v___x_4189_; uint8_t v___x_4190_; 
v___x_4188_ = lean_unsigned_to_nat(0u);
v___x_4189_ = lean_array_get_size(v_tail_4186_);
v___x_4190_ = lean_nat_dec_lt(v___x_4188_, v___x_4189_);
if (v___x_4190_ == 0)
{
return v___x_4190_;
}
else
{
if (v___x_4190_ == 0)
{
return v___x_4190_;
}
else
{
size_t v___x_4191_; size_t v___x_4192_; uint8_t v___x_4193_; 
v___x_4191_ = ((size_t)0ULL);
v___x_4192_ = lean_usize_of_nat(v___x_4189_);
v___x_4193_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_Meta_Closure_mkValueTypeClosure_spec__0_spec__1(v_tail_4186_, v___x_4191_, v___x_4192_);
return v___x_4193_;
}
}
}
else
{
return v___x_4187_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___at___00Lean_Meta_Closure_mkValueTypeClosure_spec__0___boxed(lean_object* v_t_4194_){
_start:
{
uint8_t v_res_4195_; lean_object* v_r_4196_; 
v_res_4195_ = l_Lean_PersistentArray_anyM___at___00Lean_Meta_Closure_mkValueTypeClosure_spec__0(v_t_4194_);
lean_dec_ref(v_t_4194_);
v_r_4196_ = lean_box(v_res_4195_);
return v_r_4196_;
}
}
static lean_object* _init_l_Lean_Meta_Closure_mkValueTypeClosure___closed__0(void){
_start:
{
lean_object* v___x_4197_; lean_object* v___x_4198_; lean_object* v___x_4199_; 
v___x_4197_ = lean_box(0);
v___x_4198_ = lean_unsigned_to_nat(16u);
v___x_4199_ = lean_mk_array(v___x_4198_, v___x_4197_);
return v___x_4199_;
}
}
static lean_object* _init_l_Lean_Meta_Closure_mkValueTypeClosure___closed__1(void){
_start:
{
lean_object* v___x_4200_; lean_object* v___x_4201_; lean_object* v___x_4202_; 
v___x_4200_ = lean_obj_once(&l_Lean_Meta_Closure_mkValueTypeClosure___closed__0, &l_Lean_Meta_Closure_mkValueTypeClosure___closed__0_once, _init_l_Lean_Meta_Closure_mkValueTypeClosure___closed__0);
v___x_4201_ = lean_unsigned_to_nat(0u);
v___x_4202_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4202_, 0, v___x_4201_);
lean_ctor_set(v___x_4202_, 1, v___x_4200_);
return v___x_4202_;
}
}
static lean_object* _init_l_Lean_Meta_Closure_mkValueTypeClosure___closed__3(void){
_start:
{
lean_object* v___x_4205_; lean_object* v___x_4206_; lean_object* v___x_4207_; lean_object* v___x_4208_; 
v___x_4205_ = lean_unsigned_to_nat(1u);
v___x_4206_ = ((lean_object*)(l_Lean_Meta_Closure_mkValueTypeClosure___closed__2));
v___x_4207_ = lean_obj_once(&l_Lean_Meta_Closure_mkValueTypeClosure___closed__1, &l_Lean_Meta_Closure_mkValueTypeClosure___closed__1_once, _init_l_Lean_Meta_Closure_mkValueTypeClosure___closed__1);
v___x_4208_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_4208_, 0, v___x_4207_);
lean_ctor_set(v___x_4208_, 1, v___x_4207_);
lean_ctor_set(v___x_4208_, 2, v___x_4206_);
lean_ctor_set(v___x_4208_, 3, v___x_4205_);
lean_ctor_set(v___x_4208_, 4, v___x_4206_);
lean_ctor_set(v___x_4208_, 5, v___x_4206_);
lean_ctor_set(v___x_4208_, 6, v___x_4206_);
lean_ctor_set(v___x_4208_, 7, v___x_4206_);
lean_ctor_set(v___x_4208_, 8, v___x_4205_);
lean_ctor_set(v___x_4208_, 9, v___x_4206_);
lean_ctor_set(v___x_4208_, 10, v___x_4206_);
lean_ctor_set(v___x_4208_, 11, v___x_4206_);
return v___x_4208_;
}
}
static lean_object* _init_l_Lean_Meta_Closure_mkValueTypeClosure___closed__6(void){
_start:
{
lean_object* v___x_4211_; lean_object* v___x_4212_; lean_object* v___x_4213_; lean_object* v___x_4214_; lean_object* v___x_4215_; lean_object* v___x_4216_; 
v___x_4211_ = ((lean_object*)(l_Lean_Meta_Closure_mkValueTypeClosure___closed__5));
v___x_4212_ = lean_unsigned_to_nat(2u);
v___x_4213_ = lean_unsigned_to_nat(424u);
v___x_4214_ = ((lean_object*)(l_Lean_Meta_Closure_mkValueTypeClosure___closed__4));
v___x_4215_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__2));
v___x_4216_ = l_mkPanicMessageWithDecl(v___x_4215_, v___x_4214_, v___x_4213_, v___x_4212_, v___x_4211_);
return v___x_4216_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkValueTypeClosure(lean_object* v_type_4217_, lean_object* v_value_4218_, uint8_t v_zetaDelta_4219_, lean_object* v_a_4220_, lean_object* v_a_4221_, lean_object* v_a_4222_, lean_object* v_a_4223_){
_start:
{
lean_object* v_lctx_4225_; lean_object* v_decls_4226_; uint8_t v___x_4227_; lean_object* v___x_4228_; lean_object* v___x_4229_; lean_object* v___x_4230_; lean_object* v___x_4231_; 
v_lctx_4225_ = lean_ctor_get(v_a_4220_, 2);
v_decls_4226_ = lean_ctor_get(v_lctx_4225_, 1);
v___x_4227_ = l_Lean_PersistentArray_anyM___at___00Lean_Meta_Closure_mkValueTypeClosure_spec__0(v_decls_4226_);
v___x_4228_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_4228_, 0, v_zetaDelta_4219_);
lean_ctor_set_uint8(v___x_4228_, 1, v___x_4227_);
v___x_4229_ = lean_obj_once(&l_Lean_Meta_Closure_mkValueTypeClosure___closed__3, &l_Lean_Meta_Closure_mkValueTypeClosure___closed__3_once, _init_l_Lean_Meta_Closure_mkValueTypeClosure___closed__3);
v___x_4230_ = lean_st_mk_ref(v___x_4229_);
v___x_4231_ = l_Lean_Meta_Closure_mkValueTypeClosureAux(v_type_4217_, v_value_4218_, v___x_4228_, v___x_4230_, v_a_4220_, v_a_4221_, v_a_4222_, v_a_4223_);
lean_dec_ref_known(v___x_4228_, 0);
if (lean_obj_tag(v___x_4231_) == 0)
{
lean_object* v_a_4232_; lean_object* v___x_4233_; lean_object* v_fst_4234_; lean_object* v_snd_4235_; lean_object* v_levelParams_4236_; lean_object* v_levelArgs_4237_; lean_object* v_newLocalDecls_4238_; lean_object* v_newLocalDeclsForMVars_4239_; lean_object* v_newLetDecls_4240_; lean_object* v_exprMVarArgs_4241_; lean_object* v_exprFVarArgs_4242_; lean_object* v___x_4243_; lean_object* v___x_4244_; lean_object* v___x_4245_; 
v_a_4232_ = lean_ctor_get(v___x_4231_, 0);
lean_inc(v_a_4232_);
lean_dec_ref_known(v___x_4231_, 1);
v___x_4233_ = lean_st_ref_get(v___x_4230_);
lean_dec(v___x_4230_);
v_fst_4234_ = lean_ctor_get(v_a_4232_, 0);
lean_inc(v_fst_4234_);
v_snd_4235_ = lean_ctor_get(v_a_4232_, 1);
lean_inc(v_snd_4235_);
lean_dec(v_a_4232_);
v_levelParams_4236_ = lean_ctor_get(v___x_4233_, 2);
lean_inc_ref(v_levelParams_4236_);
v_levelArgs_4237_ = lean_ctor_get(v___x_4233_, 4);
lean_inc_ref(v_levelArgs_4237_);
v_newLocalDecls_4238_ = lean_ctor_get(v___x_4233_, 5);
lean_inc_ref(v_newLocalDecls_4238_);
v_newLocalDeclsForMVars_4239_ = lean_ctor_get(v___x_4233_, 6);
lean_inc_ref(v_newLocalDeclsForMVars_4239_);
v_newLetDecls_4240_ = lean_ctor_get(v___x_4233_, 7);
lean_inc_ref(v_newLetDecls_4240_);
v_exprMVarArgs_4241_ = lean_ctor_get(v___x_4233_, 9);
lean_inc_ref(v_exprMVarArgs_4241_);
v_exprFVarArgs_4242_ = lean_ctor_get(v___x_4233_, 10);
lean_inc_ref(v_exprFVarArgs_4242_);
lean_dec(v___x_4233_);
v___x_4243_ = l_Array_reverse___redArg(v_newLocalDecls_4238_);
v___x_4244_ = l_Array_reverse___redArg(v_exprFVarArgs_4242_);
v___x_4245_ = l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls(v___x_4243_, v___x_4244_, v_newLocalDeclsForMVars_4239_, v_exprMVarArgs_4241_, v_a_4222_, v_a_4223_);
lean_dec_ref(v_newLocalDeclsForMVars_4239_);
if (lean_obj_tag(v___x_4245_) == 0)
{
lean_object* v_a_4246_; lean_object* v___x_4248_; uint8_t v_isShared_4249_; uint8_t v_isSharedCheck_4264_; 
v_a_4246_ = lean_ctor_get(v___x_4245_, 0);
v_isSharedCheck_4264_ = !lean_is_exclusive(v___x_4245_);
if (v_isSharedCheck_4264_ == 0)
{
v___x_4248_ = v___x_4245_;
v_isShared_4249_ = v_isSharedCheck_4264_;
goto v_resetjp_4247_;
}
else
{
lean_inc(v_a_4246_);
lean_dec(v___x_4245_);
v___x_4248_ = lean_box(0);
v_isShared_4249_ = v_isSharedCheck_4264_;
goto v_resetjp_4247_;
}
v_resetjp_4247_:
{
lean_object* v_fst_4250_; lean_object* v_snd_4251_; lean_object* v___x_4252_; lean_object* v___x_4253_; lean_object* v___x_4254_; lean_object* v___x_4255_; lean_object* v___x_4256_; uint8_t v___x_4257_; 
v_fst_4250_ = lean_ctor_get(v_a_4246_, 0);
lean_inc_n(v_fst_4250_, 2);
v_snd_4251_ = lean_ctor_get(v_a_4246_, 1);
lean_inc(v_snd_4251_);
lean_dec(v_a_4246_);
v___x_4252_ = l_Array_reverse___redArg(v_newLetDecls_4240_);
lean_inc_ref(v___x_4252_);
v___x_4253_ = l_Lean_Meta_Closure_mkForall(v___x_4252_, v_fst_4234_);
lean_dec(v_fst_4234_);
v___x_4254_ = l_Lean_Meta_Closure_mkForall(v_fst_4250_, v___x_4253_);
lean_dec_ref(v___x_4253_);
v___x_4255_ = l_Lean_Meta_Closure_mkLambda(v___x_4252_, v_snd_4235_);
lean_dec(v_snd_4235_);
v___x_4256_ = l_Lean_Meta_Closure_mkLambda(v_fst_4250_, v___x_4255_);
lean_dec_ref(v___x_4255_);
v___x_4257_ = l_Lean_Expr_hasFVar(v___x_4256_);
if (v___x_4257_ == 0)
{
lean_object* v___x_4258_; lean_object* v___x_4260_; 
v___x_4258_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4258_, 0, v_levelParams_4236_);
lean_ctor_set(v___x_4258_, 1, v___x_4254_);
lean_ctor_set(v___x_4258_, 2, v___x_4256_);
lean_ctor_set(v___x_4258_, 3, v_levelArgs_4237_);
lean_ctor_set(v___x_4258_, 4, v_snd_4251_);
if (v_isShared_4249_ == 0)
{
lean_ctor_set(v___x_4248_, 0, v___x_4258_);
v___x_4260_ = v___x_4248_;
goto v_reusejp_4259_;
}
else
{
lean_object* v_reuseFailAlloc_4261_; 
v_reuseFailAlloc_4261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4261_, 0, v___x_4258_);
v___x_4260_ = v_reuseFailAlloc_4261_;
goto v_reusejp_4259_;
}
v_reusejp_4259_:
{
return v___x_4260_;
}
}
else
{
lean_object* v___x_4262_; lean_object* v___x_4263_; 
lean_dec_ref(v___x_4256_);
lean_dec_ref(v___x_4254_);
lean_dec(v_snd_4251_);
lean_del_object(v___x_4248_);
lean_dec_ref(v_levelArgs_4237_);
lean_dec_ref(v_levelParams_4236_);
v___x_4262_ = lean_obj_once(&l_Lean_Meta_Closure_mkValueTypeClosure___closed__6, &l_Lean_Meta_Closure_mkValueTypeClosure___closed__6_once, _init_l_Lean_Meta_Closure_mkValueTypeClosure___closed__6);
v___x_4263_ = l_panic___at___00Lean_Meta_Closure_mkValueTypeClosure_spec__1(v___x_4262_, v_a_4220_, v_a_4221_, v_a_4222_, v_a_4223_);
return v___x_4263_;
}
}
}
else
{
lean_object* v_a_4265_; lean_object* v___x_4267_; uint8_t v_isShared_4268_; uint8_t v_isSharedCheck_4272_; 
lean_dec_ref(v_newLetDecls_4240_);
lean_dec_ref(v_levelArgs_4237_);
lean_dec_ref(v_levelParams_4236_);
lean_dec(v_snd_4235_);
lean_dec(v_fst_4234_);
v_a_4265_ = lean_ctor_get(v___x_4245_, 0);
v_isSharedCheck_4272_ = !lean_is_exclusive(v___x_4245_);
if (v_isSharedCheck_4272_ == 0)
{
v___x_4267_ = v___x_4245_;
v_isShared_4268_ = v_isSharedCheck_4272_;
goto v_resetjp_4266_;
}
else
{
lean_inc(v_a_4265_);
lean_dec(v___x_4245_);
v___x_4267_ = lean_box(0);
v_isShared_4268_ = v_isSharedCheck_4272_;
goto v_resetjp_4266_;
}
v_resetjp_4266_:
{
lean_object* v___x_4270_; 
if (v_isShared_4268_ == 0)
{
v___x_4270_ = v___x_4267_;
goto v_reusejp_4269_;
}
else
{
lean_object* v_reuseFailAlloc_4271_; 
v_reuseFailAlloc_4271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4271_, 0, v_a_4265_);
v___x_4270_ = v_reuseFailAlloc_4271_;
goto v_reusejp_4269_;
}
v_reusejp_4269_:
{
return v___x_4270_;
}
}
}
}
else
{
lean_object* v_a_4273_; lean_object* v___x_4275_; uint8_t v_isShared_4276_; uint8_t v_isSharedCheck_4280_; 
lean_dec(v___x_4230_);
v_a_4273_ = lean_ctor_get(v___x_4231_, 0);
v_isSharedCheck_4280_ = !lean_is_exclusive(v___x_4231_);
if (v_isSharedCheck_4280_ == 0)
{
v___x_4275_ = v___x_4231_;
v_isShared_4276_ = v_isSharedCheck_4280_;
goto v_resetjp_4274_;
}
else
{
lean_inc(v_a_4273_);
lean_dec(v___x_4231_);
v___x_4275_ = lean_box(0);
v_isShared_4276_ = v_isSharedCheck_4280_;
goto v_resetjp_4274_;
}
v_resetjp_4274_:
{
lean_object* v___x_4278_; 
if (v_isShared_4276_ == 0)
{
v___x_4278_ = v___x_4275_;
goto v_reusejp_4277_;
}
else
{
lean_object* v_reuseFailAlloc_4279_; 
v_reuseFailAlloc_4279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4279_, 0, v_a_4273_);
v___x_4278_ = v_reuseFailAlloc_4279_;
goto v_reusejp_4277_;
}
v_reusejp_4277_:
{
return v___x_4278_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkValueTypeClosure___boxed(lean_object* v_type_4281_, lean_object* v_value_4282_, lean_object* v_zetaDelta_4283_, lean_object* v_a_4284_, lean_object* v_a_4285_, lean_object* v_a_4286_, lean_object* v_a_4287_, lean_object* v_a_4288_){
_start:
{
uint8_t v_zetaDelta_boxed_4289_; lean_object* v_res_4290_; 
v_zetaDelta_boxed_4289_ = lean_unbox(v_zetaDelta_4283_);
v_res_4290_ = l_Lean_Meta_Closure_mkValueTypeClosure(v_type_4281_, v_value_4282_, v_zetaDelta_boxed_4289_, v_a_4284_, v_a_4285_, v_a_4286_, v_a_4287_);
lean_dec(v_a_4287_);
lean_dec_ref(v_a_4286_);
lean_dec(v_a_4285_);
lean_dec_ref(v_a_4284_);
return v_res_4290_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkAuxDefinition_spec__0___redArg(lean_object* v_name_4291_, lean_object* v_levelParams_4292_, lean_object* v_type_4293_, lean_object* v_value_4294_, lean_object* v_hints_4295_, lean_object* v___y_4296_){
_start:
{
lean_object* v___x_4298_; uint8_t v___y_4300_; uint8_t v___y_4307_; lean_object* v_env_4310_; uint8_t v___x_4311_; 
v___x_4298_ = lean_st_ref_get(v___y_4296_);
v_env_4310_ = lean_ctor_get(v___x_4298_, 0);
lean_inc_ref_n(v_env_4310_, 2);
lean_dec(v___x_4298_);
v___x_4311_ = l_Lean_Environment_hasUnsafe(v_env_4310_, v_type_4293_);
if (v___x_4311_ == 0)
{
uint8_t v___x_4312_; 
v___x_4312_ = l_Lean_Environment_hasUnsafe(v_env_4310_, v_value_4294_);
v___y_4307_ = v___x_4312_;
goto v___jp_4306_;
}
else
{
lean_dec_ref(v_env_4310_);
v___y_4307_ = v___x_4311_;
goto v___jp_4306_;
}
v___jp_4299_:
{
lean_object* v___x_4301_; lean_object* v___x_4302_; lean_object* v___x_4303_; lean_object* v___x_4304_; lean_object* v___x_4305_; 
lean_inc(v_name_4291_);
v___x_4301_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4301_, 0, v_name_4291_);
lean_ctor_set(v___x_4301_, 1, v_levelParams_4292_);
lean_ctor_set(v___x_4301_, 2, v_type_4293_);
v___x_4302_ = lean_box(0);
v___x_4303_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4303_, 0, v_name_4291_);
lean_ctor_set(v___x_4303_, 1, v___x_4302_);
v___x_4304_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_4304_, 0, v___x_4301_);
lean_ctor_set(v___x_4304_, 1, v_value_4294_);
lean_ctor_set(v___x_4304_, 2, v_hints_4295_);
lean_ctor_set(v___x_4304_, 3, v___x_4303_);
lean_ctor_set_uint8(v___x_4304_, sizeof(void*)*4, v___y_4300_);
v___x_4305_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4305_, 0, v___x_4304_);
return v___x_4305_;
}
v___jp_4306_:
{
if (v___y_4307_ == 0)
{
uint8_t v___x_4308_; 
v___x_4308_ = 1;
v___y_4300_ = v___x_4308_;
goto v___jp_4299_;
}
else
{
uint8_t v___x_4309_; 
v___x_4309_ = 0;
v___y_4300_ = v___x_4309_;
goto v___jp_4299_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkAuxDefinition_spec__0___redArg___boxed(lean_object* v_name_4313_, lean_object* v_levelParams_4314_, lean_object* v_type_4315_, lean_object* v_value_4316_, lean_object* v_hints_4317_, lean_object* v___y_4318_, lean_object* v___y_4319_){
_start:
{
lean_object* v_res_4320_; 
v_res_4320_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkAuxDefinition_spec__0___redArg(v_name_4313_, v_levelParams_4314_, v_type_4315_, v_value_4316_, v_hints_4317_, v___y_4318_);
lean_dec(v___y_4318_);
return v_res_4320_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkAuxDefinition_spec__0(lean_object* v_name_4321_, lean_object* v_levelParams_4322_, lean_object* v_type_4323_, lean_object* v_value_4324_, lean_object* v_hints_4325_, lean_object* v___y_4326_, lean_object* v___y_4327_, lean_object* v___y_4328_, lean_object* v___y_4329_){
_start:
{
lean_object* v___x_4331_; 
v___x_4331_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkAuxDefinition_spec__0___redArg(v_name_4321_, v_levelParams_4322_, v_type_4323_, v_value_4324_, v_hints_4325_, v___y_4329_);
return v___x_4331_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkAuxDefinition_spec__0___boxed(lean_object* v_name_4332_, lean_object* v_levelParams_4333_, lean_object* v_type_4334_, lean_object* v_value_4335_, lean_object* v_hints_4336_, lean_object* v___y_4337_, lean_object* v___y_4338_, lean_object* v___y_4339_, lean_object* v___y_4340_, lean_object* v___y_4341_){
_start:
{
lean_object* v_res_4342_; 
v_res_4342_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkAuxDefinition_spec__0(v_name_4332_, v_levelParams_4333_, v_type_4334_, v_value_4335_, v_hints_4336_, v___y_4337_, v___y_4338_, v___y_4339_, v___y_4340_);
lean_dec(v___y_4340_);
lean_dec_ref(v___y_4339_);
lean_dec(v___y_4338_);
lean_dec_ref(v___y_4337_);
return v_res_4342_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAuxDefinition(lean_object* v_name_4343_, lean_object* v_type_4344_, lean_object* v_value_4345_, uint8_t v_zetaDelta_4346_, uint8_t v_compile_4347_, uint8_t v_logCompileErrors_4348_, lean_object* v_a_4349_, lean_object* v_a_4350_, lean_object* v_a_4351_, lean_object* v_a_4352_){
_start:
{
lean_object* v___x_4354_; 
v___x_4354_ = l_Lean_Meta_Closure_mkValueTypeClosure(v_type_4344_, v_value_4345_, v_zetaDelta_4346_, v_a_4349_, v_a_4350_, v_a_4351_, v_a_4352_);
if (lean_obj_tag(v___x_4354_) == 0)
{
lean_object* v_a_4355_; lean_object* v___x_4357_; uint8_t v_isShared_4358_; uint8_t v_isSharedCheck_4406_; 
v_a_4355_ = lean_ctor_get(v___x_4354_, 0);
v_isSharedCheck_4406_ = !lean_is_exclusive(v___x_4354_);
if (v_isSharedCheck_4406_ == 0)
{
v___x_4357_ = v___x_4354_;
v_isShared_4358_ = v_isSharedCheck_4406_;
goto v_resetjp_4356_;
}
else
{
lean_inc(v_a_4355_);
lean_dec(v___x_4354_);
v___x_4357_ = lean_box(0);
v_isShared_4358_ = v_isSharedCheck_4406_;
goto v_resetjp_4356_;
}
v_resetjp_4356_:
{
lean_object* v___x_4368_; lean_object* v_env_4369_; lean_object* v_levelParams_4370_; lean_object* v_type_4371_; lean_object* v_value_4372_; uint32_t v___x_4373_; uint32_t v___x_4374_; uint32_t v___x_4375_; lean_object* v___x_4376_; lean_object* v___x_4377_; lean_object* v___x_4378_; lean_object* v_a_4379_; lean_object* v___x_4381_; uint8_t v_isShared_4382_; uint8_t v_isSharedCheck_4405_; 
v___x_4368_ = lean_st_ref_get(v_a_4352_);
v_env_4369_ = lean_ctor_get(v___x_4368_, 0);
lean_inc_ref(v_env_4369_);
lean_dec(v___x_4368_);
v_levelParams_4370_ = lean_ctor_get(v_a_4355_, 0);
v_type_4371_ = lean_ctor_get(v_a_4355_, 1);
v_value_4372_ = lean_ctor_get(v_a_4355_, 2);
lean_inc_ref_n(v_value_4372_, 2);
v___x_4373_ = l_Lean_getMaxHeight(v_env_4369_, v_value_4372_);
v___x_4374_ = 1;
v___x_4375_ = lean_uint32_add(v___x_4373_, v___x_4374_);
v___x_4376_ = lean_alloc_ctor(2, 0, 4);
lean_ctor_set_uint32(v___x_4376_, 0, v___x_4375_);
lean_inc_ref(v_levelParams_4370_);
v___x_4377_ = lean_array_to_list(v_levelParams_4370_);
lean_inc_ref(v_type_4371_);
lean_inc(v_name_4343_);
v___x_4378_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkAuxDefinition_spec__0___redArg(v_name_4343_, v___x_4377_, v_type_4371_, v_value_4372_, v___x_4376_, v_a_4352_);
v_a_4379_ = lean_ctor_get(v___x_4378_, 0);
v_isSharedCheck_4405_ = !lean_is_exclusive(v___x_4378_);
if (v_isSharedCheck_4405_ == 0)
{
v___x_4381_ = v___x_4378_;
v_isShared_4382_ = v_isSharedCheck_4405_;
goto v_resetjp_4380_;
}
else
{
lean_inc(v_a_4379_);
lean_dec(v___x_4378_);
v___x_4381_ = lean_box(0);
v_isShared_4382_ = v_isSharedCheck_4405_;
goto v_resetjp_4380_;
}
v___jp_4359_:
{
lean_object* v_levelArgs_4360_; lean_object* v_exprArgs_4361_; lean_object* v___x_4362_; lean_object* v___x_4363_; lean_object* v___x_4364_; lean_object* v___x_4366_; 
v_levelArgs_4360_ = lean_ctor_get(v_a_4355_, 3);
lean_inc_ref(v_levelArgs_4360_);
v_exprArgs_4361_ = lean_ctor_get(v_a_4355_, 4);
lean_inc_ref(v_exprArgs_4361_);
lean_dec(v_a_4355_);
v___x_4362_ = lean_array_to_list(v_levelArgs_4360_);
v___x_4363_ = l_Lean_mkConst(v_name_4343_, v___x_4362_);
v___x_4364_ = l_Lean_mkAppN(v___x_4363_, v_exprArgs_4361_);
lean_dec_ref(v_exprArgs_4361_);
if (v_isShared_4358_ == 0)
{
lean_ctor_set(v___x_4357_, 0, v___x_4364_);
v___x_4366_ = v___x_4357_;
goto v_reusejp_4365_;
}
else
{
lean_object* v_reuseFailAlloc_4367_; 
v_reuseFailAlloc_4367_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4367_, 0, v___x_4364_);
v___x_4366_ = v_reuseFailAlloc_4367_;
goto v_reusejp_4365_;
}
v_reusejp_4365_:
{
return v___x_4366_;
}
}
v_resetjp_4380_:
{
lean_object* v___x_4384_; 
if (v_isShared_4382_ == 0)
{
lean_ctor_set_tag(v___x_4381_, 1);
v___x_4384_ = v___x_4381_;
goto v_reusejp_4383_;
}
else
{
lean_object* v_reuseFailAlloc_4404_; 
v_reuseFailAlloc_4404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4404_, 0, v_a_4379_);
v___x_4384_ = v_reuseFailAlloc_4404_;
goto v_reusejp_4383_;
}
v_reusejp_4383_:
{
uint8_t v___x_4385_; lean_object* v___x_4386_; 
v___x_4385_ = 0;
lean_inc_ref(v___x_4384_);
v___x_4386_ = l_Lean_addDecl(v___x_4384_, v___x_4385_, v_a_4351_, v_a_4352_);
if (lean_obj_tag(v___x_4386_) == 0)
{
lean_dec_ref_known(v___x_4386_, 1);
if (v_compile_4347_ == 0)
{
lean_dec_ref(v___x_4384_);
goto v___jp_4359_;
}
else
{
lean_object* v___x_4387_; 
v___x_4387_ = l_Lean_compileDecl(v___x_4384_, v_logCompileErrors_4348_, v_a_4351_, v_a_4352_);
if (lean_obj_tag(v___x_4387_) == 0)
{
lean_dec_ref_known(v___x_4387_, 1);
goto v___jp_4359_;
}
else
{
lean_object* v_a_4388_; lean_object* v___x_4390_; uint8_t v_isShared_4391_; uint8_t v_isSharedCheck_4395_; 
lean_del_object(v___x_4357_);
lean_dec(v_a_4355_);
lean_dec(v_name_4343_);
v_a_4388_ = lean_ctor_get(v___x_4387_, 0);
v_isSharedCheck_4395_ = !lean_is_exclusive(v___x_4387_);
if (v_isSharedCheck_4395_ == 0)
{
v___x_4390_ = v___x_4387_;
v_isShared_4391_ = v_isSharedCheck_4395_;
goto v_resetjp_4389_;
}
else
{
lean_inc(v_a_4388_);
lean_dec(v___x_4387_);
v___x_4390_ = lean_box(0);
v_isShared_4391_ = v_isSharedCheck_4395_;
goto v_resetjp_4389_;
}
v_resetjp_4389_:
{
lean_object* v___x_4393_; 
if (v_isShared_4391_ == 0)
{
v___x_4393_ = v___x_4390_;
goto v_reusejp_4392_;
}
else
{
lean_object* v_reuseFailAlloc_4394_; 
v_reuseFailAlloc_4394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4394_, 0, v_a_4388_);
v___x_4393_ = v_reuseFailAlloc_4394_;
goto v_reusejp_4392_;
}
v_reusejp_4392_:
{
return v___x_4393_;
}
}
}
}
}
else
{
lean_object* v_a_4396_; lean_object* v___x_4398_; uint8_t v_isShared_4399_; uint8_t v_isSharedCheck_4403_; 
lean_dec_ref(v___x_4384_);
lean_del_object(v___x_4357_);
lean_dec(v_a_4355_);
lean_dec(v_name_4343_);
v_a_4396_ = lean_ctor_get(v___x_4386_, 0);
v_isSharedCheck_4403_ = !lean_is_exclusive(v___x_4386_);
if (v_isSharedCheck_4403_ == 0)
{
v___x_4398_ = v___x_4386_;
v_isShared_4399_ = v_isSharedCheck_4403_;
goto v_resetjp_4397_;
}
else
{
lean_inc(v_a_4396_);
lean_dec(v___x_4386_);
v___x_4398_ = lean_box(0);
v_isShared_4399_ = v_isSharedCheck_4403_;
goto v_resetjp_4397_;
}
v_resetjp_4397_:
{
lean_object* v___x_4401_; 
if (v_isShared_4399_ == 0)
{
v___x_4401_ = v___x_4398_;
goto v_reusejp_4400_;
}
else
{
lean_object* v_reuseFailAlloc_4402_; 
v_reuseFailAlloc_4402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4402_, 0, v_a_4396_);
v___x_4401_ = v_reuseFailAlloc_4402_;
goto v_reusejp_4400_;
}
v_reusejp_4400_:
{
return v___x_4401_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4407_; lean_object* v___x_4409_; uint8_t v_isShared_4410_; uint8_t v_isSharedCheck_4414_; 
lean_dec(v_name_4343_);
v_a_4407_ = lean_ctor_get(v___x_4354_, 0);
v_isSharedCheck_4414_ = !lean_is_exclusive(v___x_4354_);
if (v_isSharedCheck_4414_ == 0)
{
v___x_4409_ = v___x_4354_;
v_isShared_4410_ = v_isSharedCheck_4414_;
goto v_resetjp_4408_;
}
else
{
lean_inc(v_a_4407_);
lean_dec(v___x_4354_);
v___x_4409_ = lean_box(0);
v_isShared_4410_ = v_isSharedCheck_4414_;
goto v_resetjp_4408_;
}
v_resetjp_4408_:
{
lean_object* v___x_4412_; 
if (v_isShared_4410_ == 0)
{
v___x_4412_ = v___x_4409_;
goto v_reusejp_4411_;
}
else
{
lean_object* v_reuseFailAlloc_4413_; 
v_reuseFailAlloc_4413_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4413_, 0, v_a_4407_);
v___x_4412_ = v_reuseFailAlloc_4413_;
goto v_reusejp_4411_;
}
v_reusejp_4411_:
{
return v___x_4412_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAuxDefinition___boxed(lean_object* v_name_4415_, lean_object* v_type_4416_, lean_object* v_value_4417_, lean_object* v_zetaDelta_4418_, lean_object* v_compile_4419_, lean_object* v_logCompileErrors_4420_, lean_object* v_a_4421_, lean_object* v_a_4422_, lean_object* v_a_4423_, lean_object* v_a_4424_, lean_object* v_a_4425_){
_start:
{
uint8_t v_zetaDelta_boxed_4426_; uint8_t v_compile_boxed_4427_; uint8_t v_logCompileErrors_boxed_4428_; lean_object* v_res_4429_; 
v_zetaDelta_boxed_4426_ = lean_unbox(v_zetaDelta_4418_);
v_compile_boxed_4427_ = lean_unbox(v_compile_4419_);
v_logCompileErrors_boxed_4428_ = lean_unbox(v_logCompileErrors_4420_);
v_res_4429_ = l_Lean_Meta_mkAuxDefinition(v_name_4415_, v_type_4416_, v_value_4417_, v_zetaDelta_boxed_4426_, v_compile_boxed_4427_, v_logCompileErrors_boxed_4428_, v_a_4421_, v_a_4422_, v_a_4423_, v_a_4424_);
lean_dec(v_a_4424_);
lean_dec_ref(v_a_4423_);
lean_dec(v_a_4422_);
lean_dec_ref(v_a_4421_);
return v_res_4429_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAuxDefinitionFor(lean_object* v_name_4430_, lean_object* v_value_4431_, uint8_t v_zetaDelta_4432_, uint8_t v_compile_4433_, uint8_t v_logCompileErrors_4434_, lean_object* v_a_4435_, lean_object* v_a_4436_, lean_object* v_a_4437_, lean_object* v_a_4438_){
_start:
{
lean_object* v___x_4440_; 
lean_inc(v_a_4438_);
lean_inc_ref(v_a_4437_);
lean_inc(v_a_4436_);
lean_inc_ref(v_a_4435_);
lean_inc_ref(v_value_4431_);
v___x_4440_ = lean_infer_type(v_value_4431_, v_a_4435_, v_a_4436_, v_a_4437_, v_a_4438_);
if (lean_obj_tag(v___x_4440_) == 0)
{
lean_object* v_a_4441_; lean_object* v___x_4442_; lean_object* v___x_4443_; 
v_a_4441_ = lean_ctor_get(v___x_4440_, 0);
lean_inc(v_a_4441_);
lean_dec_ref_known(v___x_4440_, 1);
v___x_4442_ = l_Lean_Expr_headBeta(v_a_4441_);
v___x_4443_ = l_Lean_Meta_mkAuxDefinition(v_name_4430_, v___x_4442_, v_value_4431_, v_zetaDelta_4432_, v_compile_4433_, v_logCompileErrors_4434_, v_a_4435_, v_a_4436_, v_a_4437_, v_a_4438_);
return v___x_4443_;
}
else
{
lean_dec_ref(v_value_4431_);
lean_dec(v_name_4430_);
return v___x_4440_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAuxDefinitionFor___boxed(lean_object* v_name_4444_, lean_object* v_value_4445_, lean_object* v_zetaDelta_4446_, lean_object* v_compile_4447_, lean_object* v_logCompileErrors_4448_, lean_object* v_a_4449_, lean_object* v_a_4450_, lean_object* v_a_4451_, lean_object* v_a_4452_, lean_object* v_a_4453_){
_start:
{
uint8_t v_zetaDelta_boxed_4454_; uint8_t v_compile_boxed_4455_; uint8_t v_logCompileErrors_boxed_4456_; lean_object* v_res_4457_; 
v_zetaDelta_boxed_4454_ = lean_unbox(v_zetaDelta_4446_);
v_compile_boxed_4455_ = lean_unbox(v_compile_4447_);
v_logCompileErrors_boxed_4456_ = lean_unbox(v_logCompileErrors_4448_);
v_res_4457_ = l_Lean_Meta_mkAuxDefinitionFor(v_name_4444_, v_value_4445_, v_zetaDelta_boxed_4454_, v_compile_boxed_4455_, v_logCompileErrors_boxed_4456_, v_a_4449_, v_a_4450_, v_a_4451_, v_a_4452_);
lean_dec(v_a_4452_);
lean_dec_ref(v_a_4451_);
lean_dec(v_a_4450_);
lean_dec_ref(v_a_4449_);
return v_res_4457_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAuxTheorem(lean_object* v_type_4458_, lean_object* v_value_4459_, uint8_t v_zetaDelta_4460_, lean_object* v_kind_x3f_4461_, uint8_t v_cache_4462_, lean_object* v_a_4463_, lean_object* v_a_4464_, lean_object* v_a_4465_, lean_object* v_a_4466_){
_start:
{
lean_object* v___x_4468_; 
v___x_4468_ = l_Lean_Meta_Closure_mkValueTypeClosure(v_type_4458_, v_value_4459_, v_zetaDelta_4460_, v_a_4463_, v_a_4464_, v_a_4465_, v_a_4466_);
if (lean_obj_tag(v___x_4468_) == 0)
{
lean_object* v_a_4469_; lean_object* v_levelParams_4470_; lean_object* v_type_4471_; lean_object* v_value_4472_; lean_object* v_levelArgs_4473_; lean_object* v_exprArgs_4474_; lean_object* v___x_4475_; uint8_t v___x_4476_; lean_object* v___x_4477_; 
v_a_4469_ = lean_ctor_get(v___x_4468_, 0);
lean_inc(v_a_4469_);
lean_dec_ref_known(v___x_4468_, 1);
v_levelParams_4470_ = lean_ctor_get(v_a_4469_, 0);
lean_inc_ref(v_levelParams_4470_);
v_type_4471_ = lean_ctor_get(v_a_4469_, 1);
lean_inc_ref(v_type_4471_);
v_value_4472_ = lean_ctor_get(v_a_4469_, 2);
lean_inc_ref(v_value_4472_);
v_levelArgs_4473_ = lean_ctor_get(v_a_4469_, 3);
lean_inc_ref(v_levelArgs_4473_);
v_exprArgs_4474_ = lean_ctor_get(v_a_4469_, 4);
lean_inc_ref(v_exprArgs_4474_);
lean_dec(v_a_4469_);
v___x_4475_ = lean_array_to_list(v_levelParams_4470_);
v___x_4476_ = 0;
v___x_4477_ = l_Lean_Meta_mkAuxLemma(v___x_4475_, v_type_4471_, v_value_4472_, v_kind_x3f_4461_, v_cache_4462_, v___x_4476_, v___x_4476_, v___x_4476_, v_a_4463_, v_a_4464_, v_a_4465_, v_a_4466_);
if (lean_obj_tag(v___x_4477_) == 0)
{
lean_object* v_a_4478_; lean_object* v___x_4480_; uint8_t v_isShared_4481_; uint8_t v_isSharedCheck_4488_; 
v_a_4478_ = lean_ctor_get(v___x_4477_, 0);
v_isSharedCheck_4488_ = !lean_is_exclusive(v___x_4477_);
if (v_isSharedCheck_4488_ == 0)
{
v___x_4480_ = v___x_4477_;
v_isShared_4481_ = v_isSharedCheck_4488_;
goto v_resetjp_4479_;
}
else
{
lean_inc(v_a_4478_);
lean_dec(v___x_4477_);
v___x_4480_ = lean_box(0);
v_isShared_4481_ = v_isSharedCheck_4488_;
goto v_resetjp_4479_;
}
v_resetjp_4479_:
{
lean_object* v___x_4482_; lean_object* v___x_4483_; lean_object* v___x_4484_; lean_object* v___x_4486_; 
v___x_4482_ = lean_array_to_list(v_levelArgs_4473_);
v___x_4483_ = l_Lean_mkConst(v_a_4478_, v___x_4482_);
v___x_4484_ = l_Lean_mkAppN(v___x_4483_, v_exprArgs_4474_);
lean_dec_ref(v_exprArgs_4474_);
if (v_isShared_4481_ == 0)
{
lean_ctor_set(v___x_4480_, 0, v___x_4484_);
v___x_4486_ = v___x_4480_;
goto v_reusejp_4485_;
}
else
{
lean_object* v_reuseFailAlloc_4487_; 
v_reuseFailAlloc_4487_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4487_, 0, v___x_4484_);
v___x_4486_ = v_reuseFailAlloc_4487_;
goto v_reusejp_4485_;
}
v_reusejp_4485_:
{
return v___x_4486_;
}
}
}
else
{
lean_object* v_a_4489_; lean_object* v___x_4491_; uint8_t v_isShared_4492_; uint8_t v_isSharedCheck_4496_; 
lean_dec_ref(v_exprArgs_4474_);
lean_dec_ref(v_levelArgs_4473_);
v_a_4489_ = lean_ctor_get(v___x_4477_, 0);
v_isSharedCheck_4496_ = !lean_is_exclusive(v___x_4477_);
if (v_isSharedCheck_4496_ == 0)
{
v___x_4491_ = v___x_4477_;
v_isShared_4492_ = v_isSharedCheck_4496_;
goto v_resetjp_4490_;
}
else
{
lean_inc(v_a_4489_);
lean_dec(v___x_4477_);
v___x_4491_ = lean_box(0);
v_isShared_4492_ = v_isSharedCheck_4496_;
goto v_resetjp_4490_;
}
v_resetjp_4490_:
{
lean_object* v___x_4494_; 
if (v_isShared_4492_ == 0)
{
v___x_4494_ = v___x_4491_;
goto v_reusejp_4493_;
}
else
{
lean_object* v_reuseFailAlloc_4495_; 
v_reuseFailAlloc_4495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4495_, 0, v_a_4489_);
v___x_4494_ = v_reuseFailAlloc_4495_;
goto v_reusejp_4493_;
}
v_reusejp_4493_:
{
return v___x_4494_;
}
}
}
}
else
{
lean_object* v_a_4497_; lean_object* v___x_4499_; uint8_t v_isShared_4500_; uint8_t v_isSharedCheck_4504_; 
lean_dec(v_kind_x3f_4461_);
v_a_4497_ = lean_ctor_get(v___x_4468_, 0);
v_isSharedCheck_4504_ = !lean_is_exclusive(v___x_4468_);
if (v_isSharedCheck_4504_ == 0)
{
v___x_4499_ = v___x_4468_;
v_isShared_4500_ = v_isSharedCheck_4504_;
goto v_resetjp_4498_;
}
else
{
lean_inc(v_a_4497_);
lean_dec(v___x_4468_);
v___x_4499_ = lean_box(0);
v_isShared_4500_ = v_isSharedCheck_4504_;
goto v_resetjp_4498_;
}
v_resetjp_4498_:
{
lean_object* v___x_4502_; 
if (v_isShared_4500_ == 0)
{
v___x_4502_ = v___x_4499_;
goto v_reusejp_4501_;
}
else
{
lean_object* v_reuseFailAlloc_4503_; 
v_reuseFailAlloc_4503_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4503_, 0, v_a_4497_);
v___x_4502_ = v_reuseFailAlloc_4503_;
goto v_reusejp_4501_;
}
v_reusejp_4501_:
{
return v___x_4502_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAuxTheorem___boxed(lean_object* v_type_4505_, lean_object* v_value_4506_, lean_object* v_zetaDelta_4507_, lean_object* v_kind_x3f_4508_, lean_object* v_cache_4509_, lean_object* v_a_4510_, lean_object* v_a_4511_, lean_object* v_a_4512_, lean_object* v_a_4513_, lean_object* v_a_4514_){
_start:
{
uint8_t v_zetaDelta_boxed_4515_; uint8_t v_cache_boxed_4516_; lean_object* v_res_4517_; 
v_zetaDelta_boxed_4515_ = lean_unbox(v_zetaDelta_4507_);
v_cache_boxed_4516_ = lean_unbox(v_cache_4509_);
v_res_4517_ = l_Lean_Meta_mkAuxTheorem(v_type_4505_, v_value_4506_, v_zetaDelta_boxed_4515_, v_kind_x3f_4508_, v_cache_boxed_4516_, v_a_4510_, v_a_4511_, v_a_4512_, v_a_4513_);
lean_dec(v_a_4513_);
lean_dec_ref(v_a_4512_);
lean_dec(v_a_4511_);
lean_dec_ref(v_a_4510_);
return v_res_4517_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_initFn_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4573_; uint8_t v___x_4574_; lean_object* v___x_4575_; lean_object* v___x_4576_; 
v___x_4573_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__10));
v___x_4574_ = 0;
v___x_4575_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2_));
v___x_4576_ = l_Lean_registerTraceClass(v___x_4573_, v___x_4574_, v___x_4575_);
return v___x_4576_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_initFn_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2____boxed(lean_object* v_a_4577_){
_start:
{
lean_object* v_res_4578_; 
v_res_4578_ = l___private_Lean_Meta_Closure_0__Lean_Meta_initFn_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2_();
return v_res_4578_;
}
}
lean_object* runtime_initialize_Lean_Meta_Check(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_AuxLemma(uint8_t builtin);
lean_object* runtime_initialize_Lean_Util_ForEachExpr(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Closure(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Check(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_AuxLemma(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Util_ForEachExpr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Closure_0__Lean_Meta_initFn_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Closure(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Check(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_AuxLemma(uint8_t builtin);
lean_object* initialize_Lean_Util_ForEachExpr(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Closure(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Check(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_AuxLemma(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_ForEachExpr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Closure(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Closure(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Closure(builtin);
}
#ifdef __cplusplus
}
#endif
