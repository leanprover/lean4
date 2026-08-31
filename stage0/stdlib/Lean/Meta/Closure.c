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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
uint8_t l_Lean_ExprStructEq_beq(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instInhabitedCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*);
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
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
uint64_t l_Lean_Expr_hash(lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t l_Lean_LocalDecl_isLet(lean_object*, uint8_t);
lean_object* l_instMonadEIO(lean_object*);
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
uint8_t lean_usize_dec_eq(size_t, size_t);
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
lean_object* l_Lean_MVarId_getDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Meta_instInhabitedMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_visitLevel(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_visitLevel___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Closure_visitExpr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_ExprStructEq_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Closure_visitExpr___closed__0 = (const lean_object*)&l_Lean_Meta_Closure_visitExpr___closed__0_value;
static const lean_closure_object l_Lean_Meta_Closure_visitExpr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_ExprStructEq_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Closure_visitExpr___closed__1 = (const lean_object*)&l_Lean_Meta_Closure_visitExpr___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_visitExpr(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_visitExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Closure_mkNewLevelParam___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "u"};
static const lean_object* l_Lean_Meta_Closure_mkNewLevelParam___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Closure_mkNewLevelParam___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Closure_mkNewLevelParam___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Closure_mkNewLevelParam___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(232, 178, 247, 241, 102, 42, 87, 174)}};
static const lean_object* l_Lean_Meta_Closure_mkNewLevelParam___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Closure_mkNewLevelParam___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkNewLevelParam___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkNewLevelParam___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkNewLevelParam(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectLevelAux(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectLevel(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectLevel___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Closure_preprocess_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Closure_preprocess_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Closure_preprocess_spec__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Closure_preprocess_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_preprocess(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_preprocess___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Closure_mkNextUserName___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_x"};
static const lean_object* l_Lean_Meta_Closure_mkNextUserName___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Closure_mkNextUserName___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Closure_mkNextUserName___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Closure_mkNextUserName___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(181, 1, 28, 251, 11, 9, 217, 106)}};
static const lean_object* l_Lean_Meta_Closure_mkNextUserName___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Closure_mkNextUserName___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkNextUserName___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkNextUserName___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkNextUserName(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkNextUserName___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushToProcess___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushToProcess___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushToProcess(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushToProcess___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__4(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Closure_collectExprAux_spec__5___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Closure_collectExprAux_spec__5___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Closure_collectExprAux_spec__5___redArg(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Closure_collectExprAux_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Closure_collectExprAux_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Closure_collectExprAux_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Closure_collectExprAux_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Closure_collectExprAux_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Closure_collectExprAux_spec__3_spec__7___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Closure_collectExprAux_spec__3_spec__7___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00Lean_Meta_Closure_collectExprAux_spec__3(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00Lean_Meta_Closure_collectExprAux_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectExprAux___lam__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectExprAux___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__3_spec__6_spec__10___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__3_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__3___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectExprAux(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectExprAux___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectExprAux___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectExprAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Closure_collectExprAux_spec__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Closure_collectExprAux_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Closure_collectExprAux_spec__3_spec__7(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Closure_collectExprAux_spec__3_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__3_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__3_spec__6_spec__10(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectExpr(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pickNextToProcessAux(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pickNextToProcess_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pickNextToProcess_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pickNextToProcess_x3f(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pickNextToProcess_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushFVarArg___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushFVarArg___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushFVarArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushFVarArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushLocalDecl(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushLocalDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Closure_process_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Closure_process_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Closure_process_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Closure_process_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_process(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkValueTypeClosureAux(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__5;
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
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instInhabitedCoreM___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
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
static const lean_closure_object l_panic___at___00Lean_Meta_Closure_mkValueTypeClosure_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instInhabitedMetaM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Meta_Closure_mkValueTypeClosure_spec__0___closed__0 = (const lean_object*)&l_panic___at___00Lean_Meta_Closure_mkValueTypeClosure_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Closure_mkValueTypeClosure_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Closure_mkValueTypeClosure_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_visitLevel(lean_object* v_f_7_, lean_object* v_u_8_, uint8_t v_a_9_, lean_object* v_a_10_, lean_object* v_a_11_, lean_object* v_a_12_, lean_object* v_a_13_, lean_object* v_a_14_){
_start:
{
lean_object* v___x_16_; lean_object* v___x_17_; uint8_t v___x_62_; 
v___x_16_ = ((lean_object*)(l_Lean_Meta_Closure_visitLevel___closed__0));
v___x_17_ = ((lean_object*)(l_Lean_Meta_Closure_visitLevel___closed__1));
v___x_62_ = l_Lean_Level_hasMVar(v_u_8_);
if (v___x_62_ == 0)
{
uint8_t v___x_63_; 
v___x_63_ = l_Lean_Level_hasParam(v_u_8_);
if (v___x_63_ == 0)
{
lean_object* v___x_64_; 
lean_dec_ref(v_f_7_);
v___x_64_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_64_, 0, v_u_8_);
return v___x_64_;
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
lean_object* v___x_22_; lean_object* v___x_23_; 
v___x_22_ = lean_box(v_a_9_);
lean_inc(v_a_14_);
lean_inc_ref(v_a_13_);
lean_inc(v_a_12_);
lean_inc_ref(v_a_11_);
lean_inc(v_a_10_);
lean_inc(v_u_8_);
v___x_23_ = lean_apply_8(v_f_7_, v_u_8_, v___x_22_, v_a_10_, v_a_11_, v_a_12_, v_a_13_, v_a_14_, lean_box(0));
if (lean_obj_tag(v___x_23_) == 0)
{
lean_object* v_a_24_; lean_object* v___x_26_; uint8_t v_isShared_27_; uint8_t v_isSharedCheck_53_; 
v_a_24_ = lean_ctor_get(v___x_23_, 0);
v_isSharedCheck_53_ = !lean_is_exclusive(v___x_23_);
if (v_isSharedCheck_53_ == 0)
{
v___x_26_ = v___x_23_;
v_isShared_27_ = v_isSharedCheck_53_;
goto v_resetjp_25_;
}
else
{
lean_inc(v_a_24_);
lean_dec(v___x_23_);
v___x_26_ = lean_box(0);
v_isShared_27_ = v_isSharedCheck_53_;
goto v_resetjp_25_;
}
v_resetjp_25_:
{
lean_object* v___x_28_; lean_object* v_visitedLevel_29_; lean_object* v_visitedExpr_30_; lean_object* v_levelParams_31_; lean_object* v_nextLevelIdx_32_; lean_object* v_levelArgs_33_; lean_object* v_newLocalDecls_34_; lean_object* v_newLocalDeclsForMVars_35_; lean_object* v_newLetDecls_36_; lean_object* v_nextExprIdx_37_; lean_object* v_exprMVarArgs_38_; lean_object* v_exprFVarArgs_39_; lean_object* v_toProcess_40_; lean_object* v___x_42_; uint8_t v_isShared_43_; uint8_t v_isSharedCheck_52_; 
v___x_28_ = lean_st_ref_take(v_a_10_);
v_visitedLevel_29_ = lean_ctor_get(v___x_28_, 0);
v_visitedExpr_30_ = lean_ctor_get(v___x_28_, 1);
v_levelParams_31_ = lean_ctor_get(v___x_28_, 2);
v_nextLevelIdx_32_ = lean_ctor_get(v___x_28_, 3);
v_levelArgs_33_ = lean_ctor_get(v___x_28_, 4);
v_newLocalDecls_34_ = lean_ctor_get(v___x_28_, 5);
v_newLocalDeclsForMVars_35_ = lean_ctor_get(v___x_28_, 6);
v_newLetDecls_36_ = lean_ctor_get(v___x_28_, 7);
v_nextExprIdx_37_ = lean_ctor_get(v___x_28_, 8);
v_exprMVarArgs_38_ = lean_ctor_get(v___x_28_, 9);
v_exprFVarArgs_39_ = lean_ctor_get(v___x_28_, 10);
v_toProcess_40_ = lean_ctor_get(v___x_28_, 11);
v_isSharedCheck_52_ = !lean_is_exclusive(v___x_28_);
if (v_isSharedCheck_52_ == 0)
{
v___x_42_ = v___x_28_;
v_isShared_43_ = v_isSharedCheck_52_;
goto v_resetjp_41_;
}
else
{
lean_inc(v_toProcess_40_);
lean_inc(v_exprFVarArgs_39_);
lean_inc(v_exprMVarArgs_38_);
lean_inc(v_nextExprIdx_37_);
lean_inc(v_newLetDecls_36_);
lean_inc(v_newLocalDeclsForMVars_35_);
lean_inc(v_newLocalDecls_34_);
lean_inc(v_levelArgs_33_);
lean_inc(v_nextLevelIdx_32_);
lean_inc(v_levelParams_31_);
lean_inc(v_visitedExpr_30_);
lean_inc(v_visitedLevel_29_);
lean_dec(v___x_28_);
v___x_42_ = lean_box(0);
v_isShared_43_ = v_isSharedCheck_52_;
goto v_resetjp_41_;
}
v_resetjp_41_:
{
lean_object* v___x_44_; lean_object* v___x_46_; 
lean_inc(v_a_24_);
v___x_44_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___x_16_, v___x_17_, v_visitedLevel_29_, v_u_8_, v_a_24_);
if (v_isShared_43_ == 0)
{
lean_ctor_set(v___x_42_, 0, v___x_44_);
v___x_46_ = v___x_42_;
goto v_reusejp_45_;
}
else
{
lean_object* v_reuseFailAlloc_51_; 
v_reuseFailAlloc_51_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_51_, 0, v___x_44_);
lean_ctor_set(v_reuseFailAlloc_51_, 1, v_visitedExpr_30_);
lean_ctor_set(v_reuseFailAlloc_51_, 2, v_levelParams_31_);
lean_ctor_set(v_reuseFailAlloc_51_, 3, v_nextLevelIdx_32_);
lean_ctor_set(v_reuseFailAlloc_51_, 4, v_levelArgs_33_);
lean_ctor_set(v_reuseFailAlloc_51_, 5, v_newLocalDecls_34_);
lean_ctor_set(v_reuseFailAlloc_51_, 6, v_newLocalDeclsForMVars_35_);
lean_ctor_set(v_reuseFailAlloc_51_, 7, v_newLetDecls_36_);
lean_ctor_set(v_reuseFailAlloc_51_, 8, v_nextExprIdx_37_);
lean_ctor_set(v_reuseFailAlloc_51_, 9, v_exprMVarArgs_38_);
lean_ctor_set(v_reuseFailAlloc_51_, 10, v_exprFVarArgs_39_);
lean_ctor_set(v_reuseFailAlloc_51_, 11, v_toProcess_40_);
v___x_46_ = v_reuseFailAlloc_51_;
goto v_reusejp_45_;
}
v_reusejp_45_:
{
lean_object* v___x_47_; lean_object* v___x_49_; 
v___x_47_ = lean_st_ref_put(v_a_10_, v___x_46_);
if (v_isShared_27_ == 0)
{
v___x_49_ = v___x_26_;
goto v_reusejp_48_;
}
else
{
lean_object* v_reuseFailAlloc_50_; 
v_reuseFailAlloc_50_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_50_, 0, v_a_24_);
v___x_49_ = v_reuseFailAlloc_50_;
goto v_reusejp_48_;
}
v_reusejp_48_:
{
return v___x_49_;
}
}
}
}
}
else
{
lean_dec(v_u_8_);
return v___x_23_;
}
}
else
{
lean_object* v_val_54_; lean_object* v___x_56_; uint8_t v_isShared_57_; uint8_t v_isSharedCheck_61_; 
lean_dec(v_u_8_);
lean_dec_ref(v_f_7_);
v_val_54_ = lean_ctor_get(v___x_21_, 0);
v_isSharedCheck_61_ = !lean_is_exclusive(v___x_21_);
if (v_isSharedCheck_61_ == 0)
{
v___x_56_ = v___x_21_;
v_isShared_57_ = v_isSharedCheck_61_;
goto v_resetjp_55_;
}
else
{
lean_inc(v_val_54_);
lean_dec(v___x_21_);
v___x_56_ = lean_box(0);
v_isShared_57_ = v_isSharedCheck_61_;
goto v_resetjp_55_;
}
v_resetjp_55_:
{
lean_object* v___x_59_; 
if (v_isShared_57_ == 0)
{
lean_ctor_set_tag(v___x_56_, 0);
v___x_59_ = v___x_56_;
goto v_reusejp_58_;
}
else
{
lean_object* v_reuseFailAlloc_60_; 
v_reuseFailAlloc_60_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_60_, 0, v_val_54_);
v___x_59_ = v_reuseFailAlloc_60_;
goto v_reusejp_58_;
}
v_reusejp_58_:
{
return v___x_59_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_visitLevel___boxed(lean_object* v_f_65_, lean_object* v_u_66_, lean_object* v_a_67_, lean_object* v_a_68_, lean_object* v_a_69_, lean_object* v_a_70_, lean_object* v_a_71_, lean_object* v_a_72_, lean_object* v_a_73_){
_start:
{
uint8_t v_a_boxed_74_; lean_object* v_res_75_; 
v_a_boxed_74_ = lean_unbox(v_a_67_);
v_res_75_ = l_Lean_Meta_Closure_visitLevel(v_f_65_, v_u_66_, v_a_boxed_74_, v_a_68_, v_a_69_, v_a_70_, v_a_71_, v_a_72_);
lean_dec(v_a_72_);
lean_dec_ref(v_a_71_);
lean_dec(v_a_70_);
lean_dec_ref(v_a_69_);
lean_dec(v_a_68_);
return v_res_75_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_visitExpr(lean_object* v_f_78_, lean_object* v_e_79_, uint8_t v_a_80_, lean_object* v_a_81_, lean_object* v_a_82_, lean_object* v_a_83_, lean_object* v_a_84_, lean_object* v_a_85_){
_start:
{
lean_object* v___x_87_; lean_object* v___x_88_; uint8_t v___x_133_; 
v___x_87_ = ((lean_object*)(l_Lean_Meta_Closure_visitExpr___closed__0));
v___x_88_ = ((lean_object*)(l_Lean_Meta_Closure_visitExpr___closed__1));
v___x_133_ = l_Lean_Expr_hasLevelParam(v_e_79_);
if (v___x_133_ == 0)
{
uint8_t v___x_134_; 
v___x_134_ = l_Lean_Expr_hasFVar(v_e_79_);
if (v___x_134_ == 0)
{
uint8_t v___x_135_; 
v___x_135_ = l_Lean_Expr_hasMVar(v_e_79_);
if (v___x_135_ == 0)
{
lean_object* v___x_136_; 
lean_dec_ref(v_f_78_);
v___x_136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_136_, 0, v_e_79_);
return v___x_136_;
}
else
{
goto v___jp_89_;
}
}
else
{
goto v___jp_89_;
}
}
else
{
goto v___jp_89_;
}
v___jp_89_:
{
lean_object* v___x_90_; lean_object* v_visitedExpr_91_; lean_object* v___x_92_; 
v___x_90_ = lean_st_ref_get(v_a_81_);
v_visitedExpr_91_ = lean_ctor_get(v___x_90_, 1);
lean_inc_ref(v_visitedExpr_91_);
lean_dec(v___x_90_);
lean_inc_ref(v_e_79_);
v___x_92_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v___x_87_, v___x_88_, v_visitedExpr_91_, v_e_79_);
lean_dec_ref(v_visitedExpr_91_);
if (lean_obj_tag(v___x_92_) == 0)
{
lean_object* v___x_93_; lean_object* v___x_94_; 
v___x_93_ = lean_box(v_a_80_);
lean_inc(v_a_85_);
lean_inc_ref(v_a_84_);
lean_inc(v_a_83_);
lean_inc_ref(v_a_82_);
lean_inc(v_a_81_);
lean_inc_ref(v_e_79_);
v___x_94_ = lean_apply_8(v_f_78_, v_e_79_, v___x_93_, v_a_81_, v_a_82_, v_a_83_, v_a_84_, v_a_85_, lean_box(0));
if (lean_obj_tag(v___x_94_) == 0)
{
lean_object* v_a_95_; lean_object* v___x_97_; uint8_t v_isShared_98_; uint8_t v_isSharedCheck_124_; 
v_a_95_ = lean_ctor_get(v___x_94_, 0);
v_isSharedCheck_124_ = !lean_is_exclusive(v___x_94_);
if (v_isSharedCheck_124_ == 0)
{
v___x_97_ = v___x_94_;
v_isShared_98_ = v_isSharedCheck_124_;
goto v_resetjp_96_;
}
else
{
lean_inc(v_a_95_);
lean_dec(v___x_94_);
v___x_97_ = lean_box(0);
v_isShared_98_ = v_isSharedCheck_124_;
goto v_resetjp_96_;
}
v_resetjp_96_:
{
lean_object* v___x_99_; lean_object* v_visitedLevel_100_; lean_object* v_visitedExpr_101_; lean_object* v_levelParams_102_; lean_object* v_nextLevelIdx_103_; lean_object* v_levelArgs_104_; lean_object* v_newLocalDecls_105_; lean_object* v_newLocalDeclsForMVars_106_; lean_object* v_newLetDecls_107_; lean_object* v_nextExprIdx_108_; lean_object* v_exprMVarArgs_109_; lean_object* v_exprFVarArgs_110_; lean_object* v_toProcess_111_; lean_object* v___x_113_; uint8_t v_isShared_114_; uint8_t v_isSharedCheck_123_; 
v___x_99_ = lean_st_ref_take(v_a_81_);
v_visitedLevel_100_ = lean_ctor_get(v___x_99_, 0);
v_visitedExpr_101_ = lean_ctor_get(v___x_99_, 1);
v_levelParams_102_ = lean_ctor_get(v___x_99_, 2);
v_nextLevelIdx_103_ = lean_ctor_get(v___x_99_, 3);
v_levelArgs_104_ = lean_ctor_get(v___x_99_, 4);
v_newLocalDecls_105_ = lean_ctor_get(v___x_99_, 5);
v_newLocalDeclsForMVars_106_ = lean_ctor_get(v___x_99_, 6);
v_newLetDecls_107_ = lean_ctor_get(v___x_99_, 7);
v_nextExprIdx_108_ = lean_ctor_get(v___x_99_, 8);
v_exprMVarArgs_109_ = lean_ctor_get(v___x_99_, 9);
v_exprFVarArgs_110_ = lean_ctor_get(v___x_99_, 10);
v_toProcess_111_ = lean_ctor_get(v___x_99_, 11);
v_isSharedCheck_123_ = !lean_is_exclusive(v___x_99_);
if (v_isSharedCheck_123_ == 0)
{
v___x_113_ = v___x_99_;
v_isShared_114_ = v_isSharedCheck_123_;
goto v_resetjp_112_;
}
else
{
lean_inc(v_toProcess_111_);
lean_inc(v_exprFVarArgs_110_);
lean_inc(v_exprMVarArgs_109_);
lean_inc(v_nextExprIdx_108_);
lean_inc(v_newLetDecls_107_);
lean_inc(v_newLocalDeclsForMVars_106_);
lean_inc(v_newLocalDecls_105_);
lean_inc(v_levelArgs_104_);
lean_inc(v_nextLevelIdx_103_);
lean_inc(v_levelParams_102_);
lean_inc(v_visitedExpr_101_);
lean_inc(v_visitedLevel_100_);
lean_dec(v___x_99_);
v___x_113_ = lean_box(0);
v_isShared_114_ = v_isSharedCheck_123_;
goto v_resetjp_112_;
}
v_resetjp_112_:
{
lean_object* v___x_115_; lean_object* v___x_117_; 
lean_inc(v_a_95_);
v___x_115_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___x_87_, v___x_88_, v_visitedExpr_101_, v_e_79_, v_a_95_);
if (v_isShared_114_ == 0)
{
lean_ctor_set(v___x_113_, 1, v___x_115_);
v___x_117_ = v___x_113_;
goto v_reusejp_116_;
}
else
{
lean_object* v_reuseFailAlloc_122_; 
v_reuseFailAlloc_122_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_122_, 0, v_visitedLevel_100_);
lean_ctor_set(v_reuseFailAlloc_122_, 1, v___x_115_);
lean_ctor_set(v_reuseFailAlloc_122_, 2, v_levelParams_102_);
lean_ctor_set(v_reuseFailAlloc_122_, 3, v_nextLevelIdx_103_);
lean_ctor_set(v_reuseFailAlloc_122_, 4, v_levelArgs_104_);
lean_ctor_set(v_reuseFailAlloc_122_, 5, v_newLocalDecls_105_);
lean_ctor_set(v_reuseFailAlloc_122_, 6, v_newLocalDeclsForMVars_106_);
lean_ctor_set(v_reuseFailAlloc_122_, 7, v_newLetDecls_107_);
lean_ctor_set(v_reuseFailAlloc_122_, 8, v_nextExprIdx_108_);
lean_ctor_set(v_reuseFailAlloc_122_, 9, v_exprMVarArgs_109_);
lean_ctor_set(v_reuseFailAlloc_122_, 10, v_exprFVarArgs_110_);
lean_ctor_set(v_reuseFailAlloc_122_, 11, v_toProcess_111_);
v___x_117_ = v_reuseFailAlloc_122_;
goto v_reusejp_116_;
}
v_reusejp_116_:
{
lean_object* v___x_118_; lean_object* v___x_120_; 
v___x_118_ = lean_st_ref_put(v_a_81_, v___x_117_);
if (v_isShared_98_ == 0)
{
v___x_120_ = v___x_97_;
goto v_reusejp_119_;
}
else
{
lean_object* v_reuseFailAlloc_121_; 
v_reuseFailAlloc_121_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_121_, 0, v_a_95_);
v___x_120_ = v_reuseFailAlloc_121_;
goto v_reusejp_119_;
}
v_reusejp_119_:
{
return v___x_120_;
}
}
}
}
}
else
{
lean_dec_ref(v_e_79_);
return v___x_94_;
}
}
else
{
lean_object* v_val_125_; lean_object* v___x_127_; uint8_t v_isShared_128_; uint8_t v_isSharedCheck_132_; 
lean_dec_ref(v_e_79_);
lean_dec_ref(v_f_78_);
v_val_125_ = lean_ctor_get(v___x_92_, 0);
v_isSharedCheck_132_ = !lean_is_exclusive(v___x_92_);
if (v_isSharedCheck_132_ == 0)
{
v___x_127_ = v___x_92_;
v_isShared_128_ = v_isSharedCheck_132_;
goto v_resetjp_126_;
}
else
{
lean_inc(v_val_125_);
lean_dec(v___x_92_);
v___x_127_ = lean_box(0);
v_isShared_128_ = v_isSharedCheck_132_;
goto v_resetjp_126_;
}
v_resetjp_126_:
{
lean_object* v___x_130_; 
if (v_isShared_128_ == 0)
{
lean_ctor_set_tag(v___x_127_, 0);
v___x_130_ = v___x_127_;
goto v_reusejp_129_;
}
else
{
lean_object* v_reuseFailAlloc_131_; 
v_reuseFailAlloc_131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_131_, 0, v_val_125_);
v___x_130_ = v_reuseFailAlloc_131_;
goto v_reusejp_129_;
}
v_reusejp_129_:
{
return v___x_130_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_visitExpr___boxed(lean_object* v_f_137_, lean_object* v_e_138_, lean_object* v_a_139_, lean_object* v_a_140_, lean_object* v_a_141_, lean_object* v_a_142_, lean_object* v_a_143_, lean_object* v_a_144_, lean_object* v_a_145_){
_start:
{
uint8_t v_a_boxed_146_; lean_object* v_res_147_; 
v_a_boxed_146_ = lean_unbox(v_a_139_);
v_res_147_ = l_Lean_Meta_Closure_visitExpr(v_f_137_, v_e_138_, v_a_boxed_146_, v_a_140_, v_a_141_, v_a_142_, v_a_143_, v_a_144_);
lean_dec(v_a_144_);
lean_dec_ref(v_a_143_);
lean_dec(v_a_142_);
lean_dec_ref(v_a_141_);
lean_dec(v_a_140_);
return v_res_147_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkNewLevelParam___redArg(lean_object* v_u_151_, lean_object* v_a_152_){
_start:
{
lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v_nextLevelIdx_156_; lean_object* v_visitedLevel_157_; lean_object* v_visitedExpr_158_; lean_object* v_levelParams_159_; lean_object* v_nextLevelIdx_160_; lean_object* v_levelArgs_161_; lean_object* v_newLocalDecls_162_; lean_object* v_newLocalDeclsForMVars_163_; lean_object* v_newLetDecls_164_; lean_object* v_nextExprIdx_165_; lean_object* v_exprMVarArgs_166_; lean_object* v_exprFVarArgs_167_; lean_object* v_toProcess_168_; lean_object* v___x_170_; uint8_t v_isShared_171_; uint8_t v_isSharedCheck_184_; 
v___x_154_ = lean_st_ref_get(v_a_152_);
v___x_155_ = lean_st_ref_take(v_a_152_);
v_nextLevelIdx_156_ = lean_ctor_get(v___x_154_, 3);
lean_inc(v_nextLevelIdx_156_);
lean_dec(v___x_154_);
v_visitedLevel_157_ = lean_ctor_get(v___x_155_, 0);
v_visitedExpr_158_ = lean_ctor_get(v___x_155_, 1);
v_levelParams_159_ = lean_ctor_get(v___x_155_, 2);
v_nextLevelIdx_160_ = lean_ctor_get(v___x_155_, 3);
v_levelArgs_161_ = lean_ctor_get(v___x_155_, 4);
v_newLocalDecls_162_ = lean_ctor_get(v___x_155_, 5);
v_newLocalDeclsForMVars_163_ = lean_ctor_get(v___x_155_, 6);
v_newLetDecls_164_ = lean_ctor_get(v___x_155_, 7);
v_nextExprIdx_165_ = lean_ctor_get(v___x_155_, 8);
v_exprMVarArgs_166_ = lean_ctor_get(v___x_155_, 9);
v_exprFVarArgs_167_ = lean_ctor_get(v___x_155_, 10);
v_toProcess_168_ = lean_ctor_get(v___x_155_, 11);
v_isSharedCheck_184_ = !lean_is_exclusive(v___x_155_);
if (v_isSharedCheck_184_ == 0)
{
v___x_170_ = v___x_155_;
v_isShared_171_ = v_isSharedCheck_184_;
goto v_resetjp_169_;
}
else
{
lean_inc(v_toProcess_168_);
lean_inc(v_exprFVarArgs_167_);
lean_inc(v_exprMVarArgs_166_);
lean_inc(v_nextExprIdx_165_);
lean_inc(v_newLetDecls_164_);
lean_inc(v_newLocalDeclsForMVars_163_);
lean_inc(v_newLocalDecls_162_);
lean_inc(v_levelArgs_161_);
lean_inc(v_nextLevelIdx_160_);
lean_inc(v_levelParams_159_);
lean_inc(v_visitedExpr_158_);
lean_inc(v_visitedLevel_157_);
lean_dec(v___x_155_);
v___x_170_ = lean_box(0);
v_isShared_171_ = v_isSharedCheck_184_;
goto v_resetjp_169_;
}
v_resetjp_169_:
{
lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_179_; 
v___x_172_ = ((lean_object*)(l_Lean_Meta_Closure_mkNewLevelParam___redArg___closed__1));
v___x_173_ = lean_name_append_index_after(v___x_172_, v_nextLevelIdx_156_);
lean_inc(v___x_173_);
v___x_174_ = lean_array_push(v_levelParams_159_, v___x_173_);
v___x_175_ = lean_unsigned_to_nat(1u);
v___x_176_ = lean_nat_add(v_nextLevelIdx_160_, v___x_175_);
lean_dec(v_nextLevelIdx_160_);
v___x_177_ = lean_array_push(v_levelArgs_161_, v_u_151_);
if (v_isShared_171_ == 0)
{
lean_ctor_set(v___x_170_, 4, v___x_177_);
lean_ctor_set(v___x_170_, 3, v___x_176_);
lean_ctor_set(v___x_170_, 2, v___x_174_);
v___x_179_ = v___x_170_;
goto v_reusejp_178_;
}
else
{
lean_object* v_reuseFailAlloc_183_; 
v_reuseFailAlloc_183_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_183_, 0, v_visitedLevel_157_);
lean_ctor_set(v_reuseFailAlloc_183_, 1, v_visitedExpr_158_);
lean_ctor_set(v_reuseFailAlloc_183_, 2, v___x_174_);
lean_ctor_set(v_reuseFailAlloc_183_, 3, v___x_176_);
lean_ctor_set(v_reuseFailAlloc_183_, 4, v___x_177_);
lean_ctor_set(v_reuseFailAlloc_183_, 5, v_newLocalDecls_162_);
lean_ctor_set(v_reuseFailAlloc_183_, 6, v_newLocalDeclsForMVars_163_);
lean_ctor_set(v_reuseFailAlloc_183_, 7, v_newLetDecls_164_);
lean_ctor_set(v_reuseFailAlloc_183_, 8, v_nextExprIdx_165_);
lean_ctor_set(v_reuseFailAlloc_183_, 9, v_exprMVarArgs_166_);
lean_ctor_set(v_reuseFailAlloc_183_, 10, v_exprFVarArgs_167_);
lean_ctor_set(v_reuseFailAlloc_183_, 11, v_toProcess_168_);
v___x_179_ = v_reuseFailAlloc_183_;
goto v_reusejp_178_;
}
v_reusejp_178_:
{
lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; 
v___x_180_ = lean_st_ref_put(v_a_152_, v___x_179_);
v___x_181_ = l_Lean_mkLevelParam(v___x_173_);
v___x_182_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_182_, 0, v___x_181_);
return v___x_182_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkNewLevelParam___redArg___boxed(lean_object* v_u_185_, lean_object* v_a_186_, lean_object* v_a_187_){
_start:
{
lean_object* v_res_188_; 
v_res_188_ = l_Lean_Meta_Closure_mkNewLevelParam___redArg(v_u_185_, v_a_186_);
lean_dec(v_a_186_);
return v_res_188_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkNewLevelParam(lean_object* v_u_189_, uint8_t v_a_190_, lean_object* v_a_191_, lean_object* v_a_192_, lean_object* v_a_193_, lean_object* v_a_194_, lean_object* v_a_195_){
_start:
{
lean_object* v___x_197_; 
v___x_197_ = l_Lean_Meta_Closure_mkNewLevelParam___redArg(v_u_189_, v_a_191_);
return v___x_197_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkNewLevelParam___boxed(lean_object* v_u_198_, lean_object* v_a_199_, lean_object* v_a_200_, lean_object* v_a_201_, lean_object* v_a_202_, lean_object* v_a_203_, lean_object* v_a_204_, lean_object* v_a_205_){
_start:
{
uint8_t v_a_boxed_206_; lean_object* v_res_207_; 
v_a_boxed_206_ = lean_unbox(v_a_199_);
v_res_207_ = l_Lean_Meta_Closure_mkNewLevelParam(v_u_198_, v_a_boxed_206_, v_a_200_, v_a_201_, v_a_202_, v_a_203_, v_a_204_);
lean_dec(v_a_204_);
lean_dec_ref(v_a_203_);
lean_dec(v_a_202_);
lean_dec_ref(v_a_201_);
lean_dec(v_a_200_);
return v_res_207_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Closure_collectLevelAux_spec__0(lean_object* v_msg_208_){
_start:
{
lean_object* v___x_209_; lean_object* v___x_210_; 
v___x_209_ = lean_box(0);
v___x_210_ = lean_panic_fn_borrowed(v___x_209_, v_msg_208_);
return v___x_210_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectLevelAux_spec__1_spec__1___redArg(lean_object* v_a_211_, lean_object* v_x_212_){
_start:
{
if (lean_obj_tag(v_x_212_) == 0)
{
lean_object* v___x_213_; 
v___x_213_ = lean_box(0);
return v___x_213_;
}
else
{
lean_object* v_key_214_; lean_object* v_value_215_; lean_object* v_tail_216_; uint8_t v___x_217_; 
v_key_214_ = lean_ctor_get(v_x_212_, 0);
v_value_215_ = lean_ctor_get(v_x_212_, 1);
v_tail_216_ = lean_ctor_get(v_x_212_, 2);
v___x_217_ = lean_level_eq(v_key_214_, v_a_211_);
if (v___x_217_ == 0)
{
v_x_212_ = v_tail_216_;
goto _start;
}
else
{
lean_object* v___x_219_; 
lean_inc(v_value_215_);
v___x_219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_219_, 0, v_value_215_);
return v___x_219_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectLevelAux_spec__1_spec__1___redArg___boxed(lean_object* v_a_220_, lean_object* v_x_221_){
_start:
{
lean_object* v_res_222_; 
v_res_222_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectLevelAux_spec__1_spec__1___redArg(v_a_220_, v_x_221_);
lean_dec(v_x_221_);
lean_dec(v_a_220_);
return v_res_222_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectLevelAux_spec__1___redArg(lean_object* v_m_223_, lean_object* v_a_224_){
_start:
{
lean_object* v_buckets_225_; lean_object* v___x_226_; uint64_t v___x_227_; uint64_t v___x_228_; uint64_t v___x_229_; uint64_t v_fold_230_; uint64_t v___x_231_; uint64_t v___x_232_; uint64_t v___x_233_; size_t v___x_234_; size_t v___x_235_; size_t v___x_236_; size_t v___x_237_; size_t v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; 
v_buckets_225_ = lean_ctor_get(v_m_223_, 1);
v___x_226_ = lean_array_get_size(v_buckets_225_);
v___x_227_ = l_Lean_Level_hash(v_a_224_);
v___x_228_ = 32ULL;
v___x_229_ = lean_uint64_shift_right(v___x_227_, v___x_228_);
v_fold_230_ = lean_uint64_xor(v___x_227_, v___x_229_);
v___x_231_ = 16ULL;
v___x_232_ = lean_uint64_shift_right(v_fold_230_, v___x_231_);
v___x_233_ = lean_uint64_xor(v_fold_230_, v___x_232_);
v___x_234_ = lean_uint64_to_usize(v___x_233_);
v___x_235_ = lean_usize_of_nat(v___x_226_);
v___x_236_ = ((size_t)1ULL);
v___x_237_ = lean_usize_sub(v___x_235_, v___x_236_);
v___x_238_ = lean_usize_land(v___x_234_, v___x_237_);
v___x_239_ = lean_array_uget_borrowed(v_buckets_225_, v___x_238_);
v___x_240_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectLevelAux_spec__1_spec__1___redArg(v_a_224_, v___x_239_);
return v___x_240_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectLevelAux_spec__1___redArg___boxed(lean_object* v_m_241_, lean_object* v_a_242_){
_start:
{
lean_object* v_res_243_; 
v_res_243_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectLevelAux_spec__1___redArg(v_m_241_, v_a_242_);
lean_dec(v_a_242_);
lean_dec_ref(v_m_241_);
return v_res_243_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__4_spec__5_spec__6___redArg(lean_object* v_x_244_, lean_object* v_x_245_){
_start:
{
if (lean_obj_tag(v_x_245_) == 0)
{
return v_x_244_;
}
else
{
lean_object* v_key_246_; lean_object* v_value_247_; lean_object* v_tail_248_; lean_object* v___x_250_; uint8_t v_isShared_251_; uint8_t v_isSharedCheck_271_; 
v_key_246_ = lean_ctor_get(v_x_245_, 0);
v_value_247_ = lean_ctor_get(v_x_245_, 1);
v_tail_248_ = lean_ctor_get(v_x_245_, 2);
v_isSharedCheck_271_ = !lean_is_exclusive(v_x_245_);
if (v_isSharedCheck_271_ == 0)
{
v___x_250_ = v_x_245_;
v_isShared_251_ = v_isSharedCheck_271_;
goto v_resetjp_249_;
}
else
{
lean_inc(v_tail_248_);
lean_inc(v_value_247_);
lean_inc(v_key_246_);
lean_dec(v_x_245_);
v___x_250_ = lean_box(0);
v_isShared_251_ = v_isSharedCheck_271_;
goto v_resetjp_249_;
}
v_resetjp_249_:
{
lean_object* v___x_252_; uint64_t v___x_253_; uint64_t v___x_254_; uint64_t v___x_255_; uint64_t v_fold_256_; uint64_t v___x_257_; uint64_t v___x_258_; uint64_t v___x_259_; size_t v___x_260_; size_t v___x_261_; size_t v___x_262_; size_t v___x_263_; size_t v___x_264_; lean_object* v___x_265_; lean_object* v___x_267_; 
v___x_252_ = lean_array_get_size(v_x_244_);
v___x_253_ = l_Lean_Level_hash(v_key_246_);
v___x_254_ = 32ULL;
v___x_255_ = lean_uint64_shift_right(v___x_253_, v___x_254_);
v_fold_256_ = lean_uint64_xor(v___x_253_, v___x_255_);
v___x_257_ = 16ULL;
v___x_258_ = lean_uint64_shift_right(v_fold_256_, v___x_257_);
v___x_259_ = lean_uint64_xor(v_fold_256_, v___x_258_);
v___x_260_ = lean_uint64_to_usize(v___x_259_);
v___x_261_ = lean_usize_of_nat(v___x_252_);
v___x_262_ = ((size_t)1ULL);
v___x_263_ = lean_usize_sub(v___x_261_, v___x_262_);
v___x_264_ = lean_usize_land(v___x_260_, v___x_263_);
v___x_265_ = lean_array_uget_borrowed(v_x_244_, v___x_264_);
lean_inc(v___x_265_);
if (v_isShared_251_ == 0)
{
lean_ctor_set(v___x_250_, 2, v___x_265_);
v___x_267_ = v___x_250_;
goto v_reusejp_266_;
}
else
{
lean_object* v_reuseFailAlloc_270_; 
v_reuseFailAlloc_270_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_270_, 0, v_key_246_);
lean_ctor_set(v_reuseFailAlloc_270_, 1, v_value_247_);
lean_ctor_set(v_reuseFailAlloc_270_, 2, v___x_265_);
v___x_267_ = v_reuseFailAlloc_270_;
goto v_reusejp_266_;
}
v_reusejp_266_:
{
lean_object* v___x_268_; 
v___x_268_ = lean_array_uset(v_x_244_, v___x_264_, v___x_267_);
v_x_244_ = v___x_268_;
v_x_245_ = v_tail_248_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__4_spec__5___redArg(lean_object* v_i_272_, lean_object* v_source_273_, lean_object* v_target_274_){
_start:
{
lean_object* v___x_275_; uint8_t v___x_276_; 
v___x_275_ = lean_array_get_size(v_source_273_);
v___x_276_ = lean_nat_dec_lt(v_i_272_, v___x_275_);
if (v___x_276_ == 0)
{
lean_dec_ref(v_source_273_);
lean_dec(v_i_272_);
return v_target_274_;
}
else
{
lean_object* v_es_277_; lean_object* v___x_278_; lean_object* v_source_279_; lean_object* v_target_280_; lean_object* v___x_281_; lean_object* v___x_282_; 
v_es_277_ = lean_array_fget(v_source_273_, v_i_272_);
v___x_278_ = lean_box(0);
v_source_279_ = lean_array_fset(v_source_273_, v_i_272_, v___x_278_);
v_target_280_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__4_spec__5_spec__6___redArg(v_target_274_, v_es_277_);
v___x_281_ = lean_unsigned_to_nat(1u);
v___x_282_ = lean_nat_add(v_i_272_, v___x_281_);
lean_dec(v_i_272_);
v_i_272_ = v___x_282_;
v_source_273_ = v_source_279_;
v_target_274_ = v_target_280_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__4___redArg(lean_object* v_data_284_){
_start:
{
lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v_nbuckets_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; 
v___x_285_ = lean_array_get_size(v_data_284_);
v___x_286_ = lean_unsigned_to_nat(2u);
v_nbuckets_287_ = lean_nat_mul(v___x_285_, v___x_286_);
v___x_288_ = lean_unsigned_to_nat(0u);
v___x_289_ = lean_box(0);
v___x_290_ = lean_mk_array(v_nbuckets_287_, v___x_289_);
v___x_291_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__4_spec__5___redArg(v___x_288_, v_data_284_, v___x_290_);
return v___x_291_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__3___redArg(lean_object* v_a_292_, lean_object* v_x_293_){
_start:
{
if (lean_obj_tag(v_x_293_) == 0)
{
uint8_t v___x_294_; 
v___x_294_ = 0;
return v___x_294_;
}
else
{
lean_object* v_key_295_; lean_object* v_tail_296_; uint8_t v___x_297_; 
v_key_295_ = lean_ctor_get(v_x_293_, 0);
v_tail_296_ = lean_ctor_get(v_x_293_, 2);
v___x_297_ = lean_level_eq(v_key_295_, v_a_292_);
if (v___x_297_ == 0)
{
v_x_293_ = v_tail_296_;
goto _start;
}
else
{
return v___x_297_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__3___redArg___boxed(lean_object* v_a_299_, lean_object* v_x_300_){
_start:
{
uint8_t v_res_301_; lean_object* v_r_302_; 
v_res_301_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__3___redArg(v_a_299_, v_x_300_);
lean_dec(v_x_300_);
lean_dec(v_a_299_);
v_r_302_ = lean_box(v_res_301_);
return v_r_302_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__5___redArg(lean_object* v_a_303_, lean_object* v_b_304_, lean_object* v_x_305_){
_start:
{
if (lean_obj_tag(v_x_305_) == 0)
{
lean_dec(v_b_304_);
lean_dec(v_a_303_);
return v_x_305_;
}
else
{
lean_object* v_key_306_; lean_object* v_value_307_; lean_object* v_tail_308_; lean_object* v___x_310_; uint8_t v_isShared_311_; uint8_t v_isSharedCheck_320_; 
v_key_306_ = lean_ctor_get(v_x_305_, 0);
v_value_307_ = lean_ctor_get(v_x_305_, 1);
v_tail_308_ = lean_ctor_get(v_x_305_, 2);
v_isSharedCheck_320_ = !lean_is_exclusive(v_x_305_);
if (v_isSharedCheck_320_ == 0)
{
v___x_310_ = v_x_305_;
v_isShared_311_ = v_isSharedCheck_320_;
goto v_resetjp_309_;
}
else
{
lean_inc(v_tail_308_);
lean_inc(v_value_307_);
lean_inc(v_key_306_);
lean_dec(v_x_305_);
v___x_310_ = lean_box(0);
v_isShared_311_ = v_isSharedCheck_320_;
goto v_resetjp_309_;
}
v_resetjp_309_:
{
uint8_t v___x_312_; 
v___x_312_ = lean_level_eq(v_key_306_, v_a_303_);
if (v___x_312_ == 0)
{
lean_object* v___x_313_; lean_object* v___x_315_; 
v___x_313_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__5___redArg(v_a_303_, v_b_304_, v_tail_308_);
if (v_isShared_311_ == 0)
{
lean_ctor_set(v___x_310_, 2, v___x_313_);
v___x_315_ = v___x_310_;
goto v_reusejp_314_;
}
else
{
lean_object* v_reuseFailAlloc_316_; 
v_reuseFailAlloc_316_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_316_, 0, v_key_306_);
lean_ctor_set(v_reuseFailAlloc_316_, 1, v_value_307_);
lean_ctor_set(v_reuseFailAlloc_316_, 2, v___x_313_);
v___x_315_ = v_reuseFailAlloc_316_;
goto v_reusejp_314_;
}
v_reusejp_314_:
{
return v___x_315_;
}
}
else
{
lean_object* v___x_318_; 
lean_dec(v_value_307_);
lean_dec(v_key_306_);
if (v_isShared_311_ == 0)
{
lean_ctor_set(v___x_310_, 1, v_b_304_);
lean_ctor_set(v___x_310_, 0, v_a_303_);
v___x_318_ = v___x_310_;
goto v_reusejp_317_;
}
else
{
lean_object* v_reuseFailAlloc_319_; 
v_reuseFailAlloc_319_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_319_, 0, v_a_303_);
lean_ctor_set(v_reuseFailAlloc_319_, 1, v_b_304_);
lean_ctor_set(v_reuseFailAlloc_319_, 2, v_tail_308_);
v___x_318_ = v_reuseFailAlloc_319_;
goto v_reusejp_317_;
}
v_reusejp_317_:
{
return v___x_318_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2___redArg(lean_object* v_m_321_, lean_object* v_a_322_, lean_object* v_b_323_){
_start:
{
lean_object* v_size_324_; lean_object* v_buckets_325_; lean_object* v___x_327_; uint8_t v_isShared_328_; uint8_t v_isSharedCheck_368_; 
v_size_324_ = lean_ctor_get(v_m_321_, 0);
v_buckets_325_ = lean_ctor_get(v_m_321_, 1);
v_isSharedCheck_368_ = !lean_is_exclusive(v_m_321_);
if (v_isSharedCheck_368_ == 0)
{
v___x_327_ = v_m_321_;
v_isShared_328_ = v_isSharedCheck_368_;
goto v_resetjp_326_;
}
else
{
lean_inc(v_buckets_325_);
lean_inc(v_size_324_);
lean_dec(v_m_321_);
v___x_327_ = lean_box(0);
v_isShared_328_ = v_isSharedCheck_368_;
goto v_resetjp_326_;
}
v_resetjp_326_:
{
lean_object* v___x_329_; uint64_t v___x_330_; uint64_t v___x_331_; uint64_t v___x_332_; uint64_t v_fold_333_; uint64_t v___x_334_; uint64_t v___x_335_; uint64_t v___x_336_; size_t v___x_337_; size_t v___x_338_; size_t v___x_339_; size_t v___x_340_; size_t v___x_341_; lean_object* v_bkt_342_; uint8_t v___x_343_; 
v___x_329_ = lean_array_get_size(v_buckets_325_);
v___x_330_ = l_Lean_Level_hash(v_a_322_);
v___x_331_ = 32ULL;
v___x_332_ = lean_uint64_shift_right(v___x_330_, v___x_331_);
v_fold_333_ = lean_uint64_xor(v___x_330_, v___x_332_);
v___x_334_ = 16ULL;
v___x_335_ = lean_uint64_shift_right(v_fold_333_, v___x_334_);
v___x_336_ = lean_uint64_xor(v_fold_333_, v___x_335_);
v___x_337_ = lean_uint64_to_usize(v___x_336_);
v___x_338_ = lean_usize_of_nat(v___x_329_);
v___x_339_ = ((size_t)1ULL);
v___x_340_ = lean_usize_sub(v___x_338_, v___x_339_);
v___x_341_ = lean_usize_land(v___x_337_, v___x_340_);
v_bkt_342_ = lean_array_uget_borrowed(v_buckets_325_, v___x_341_);
v___x_343_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__3___redArg(v_a_322_, v_bkt_342_);
if (v___x_343_ == 0)
{
lean_object* v___x_344_; lean_object* v_size_x27_345_; lean_object* v___x_346_; lean_object* v_buckets_x27_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; uint8_t v___x_353_; 
v___x_344_ = lean_unsigned_to_nat(1u);
v_size_x27_345_ = lean_nat_add(v_size_324_, v___x_344_);
lean_dec(v_size_324_);
lean_inc(v_bkt_342_);
v___x_346_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_346_, 0, v_a_322_);
lean_ctor_set(v___x_346_, 1, v_b_323_);
lean_ctor_set(v___x_346_, 2, v_bkt_342_);
v_buckets_x27_347_ = lean_array_uset(v_buckets_325_, v___x_341_, v___x_346_);
v___x_348_ = lean_unsigned_to_nat(4u);
v___x_349_ = lean_nat_mul(v_size_x27_345_, v___x_348_);
v___x_350_ = lean_unsigned_to_nat(3u);
v___x_351_ = lean_nat_div(v___x_349_, v___x_350_);
lean_dec(v___x_349_);
v___x_352_ = lean_array_get_size(v_buckets_x27_347_);
v___x_353_ = lean_nat_dec_le(v___x_351_, v___x_352_);
lean_dec(v___x_351_);
if (v___x_353_ == 0)
{
lean_object* v_val_354_; lean_object* v___x_356_; 
v_val_354_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__4___redArg(v_buckets_x27_347_);
if (v_isShared_328_ == 0)
{
lean_ctor_set(v___x_327_, 1, v_val_354_);
lean_ctor_set(v___x_327_, 0, v_size_x27_345_);
v___x_356_ = v___x_327_;
goto v_reusejp_355_;
}
else
{
lean_object* v_reuseFailAlloc_357_; 
v_reuseFailAlloc_357_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_357_, 0, v_size_x27_345_);
lean_ctor_set(v_reuseFailAlloc_357_, 1, v_val_354_);
v___x_356_ = v_reuseFailAlloc_357_;
goto v_reusejp_355_;
}
v_reusejp_355_:
{
return v___x_356_;
}
}
else
{
lean_object* v___x_359_; 
if (v_isShared_328_ == 0)
{
lean_ctor_set(v___x_327_, 1, v_buckets_x27_347_);
lean_ctor_set(v___x_327_, 0, v_size_x27_345_);
v___x_359_ = v___x_327_;
goto v_reusejp_358_;
}
else
{
lean_object* v_reuseFailAlloc_360_; 
v_reuseFailAlloc_360_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_360_, 0, v_size_x27_345_);
lean_ctor_set(v_reuseFailAlloc_360_, 1, v_buckets_x27_347_);
v___x_359_ = v_reuseFailAlloc_360_;
goto v_reusejp_358_;
}
v_reusejp_358_:
{
return v___x_359_;
}
}
}
else
{
lean_object* v___x_361_; lean_object* v_buckets_x27_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_366_; 
lean_inc(v_bkt_342_);
v___x_361_ = lean_box(0);
v_buckets_x27_362_ = lean_array_uset(v_buckets_325_, v___x_341_, v___x_361_);
v___x_363_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__5___redArg(v_a_322_, v_b_323_, v_bkt_342_);
v___x_364_ = lean_array_uset(v_buckets_x27_362_, v___x_341_, v___x_363_);
if (v_isShared_328_ == 0)
{
lean_ctor_set(v___x_327_, 1, v___x_364_);
v___x_366_ = v___x_327_;
goto v_reusejp_365_;
}
else
{
lean_object* v_reuseFailAlloc_367_; 
v_reuseFailAlloc_367_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_367_, 0, v_size_324_);
lean_ctor_set(v_reuseFailAlloc_367_, 1, v___x_364_);
v___x_366_ = v_reuseFailAlloc_367_;
goto v_reusejp_365_;
}
v_reusejp_365_:
{
return v___x_366_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectLevelAux___redArg(lean_object* v_x_369_, lean_object* v_a_370_){
_start:
{
switch(lean_obj_tag(v_x_369_))
{
case 0:
{
lean_object* v___x_372_; 
v___x_372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_372_, 0, v_x_369_);
return v___x_372_;
}
case 1:
{
lean_object* v_a_373_; lean_object* v_a_375_; uint8_t v___x_412_; 
v_a_373_ = lean_ctor_get(v_x_369_, 0);
v___x_412_ = l_Lean_Level_hasMVar(v_a_373_);
if (v___x_412_ == 0)
{
uint8_t v___x_413_; 
v___x_413_ = l_Lean_Level_hasParam(v_a_373_);
if (v___x_413_ == 0)
{
lean_inc(v_a_373_);
v_a_375_ = v_a_373_;
goto v___jp_374_;
}
else
{
goto v___jp_382_;
}
}
else
{
goto v___jp_382_;
}
v___jp_374_:
{
size_t v___x_376_; size_t v___x_377_; uint8_t v___x_378_; 
v___x_376_ = lean_ptr_addr(v_a_373_);
v___x_377_ = lean_ptr_addr(v_a_375_);
v___x_378_ = lean_usize_dec_eq(v___x_376_, v___x_377_);
if (v___x_378_ == 0)
{
lean_object* v___x_379_; lean_object* v___x_380_; 
lean_dec_ref_known(v_x_369_, 1);
v___x_379_ = l_Lean_Level_succ___override(v_a_375_);
v___x_380_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_380_, 0, v___x_379_);
return v___x_380_;
}
else
{
lean_object* v___x_381_; 
lean_dec(v_a_375_);
v___x_381_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_381_, 0, v_x_369_);
return v___x_381_;
}
}
v___jp_382_:
{
lean_object* v___x_383_; lean_object* v_visitedLevel_384_; lean_object* v___x_385_; 
v___x_383_ = lean_st_ref_get(v_a_370_);
v_visitedLevel_384_ = lean_ctor_get(v___x_383_, 0);
lean_inc_ref(v_visitedLevel_384_);
lean_dec(v___x_383_);
v___x_385_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectLevelAux_spec__1___redArg(v_visitedLevel_384_, v_a_373_);
lean_dec_ref(v_visitedLevel_384_);
if (lean_obj_tag(v___x_385_) == 0)
{
lean_object* v___x_386_; 
lean_inc(v_a_373_);
v___x_386_ = l_Lean_Meta_Closure_collectLevelAux___redArg(v_a_373_, v_a_370_);
if (lean_obj_tag(v___x_386_) == 0)
{
lean_object* v_a_387_; lean_object* v___x_388_; lean_object* v_visitedLevel_389_; lean_object* v_visitedExpr_390_; lean_object* v_levelParams_391_; lean_object* v_nextLevelIdx_392_; lean_object* v_levelArgs_393_; lean_object* v_newLocalDecls_394_; lean_object* v_newLocalDeclsForMVars_395_; lean_object* v_newLetDecls_396_; lean_object* v_nextExprIdx_397_; lean_object* v_exprMVarArgs_398_; lean_object* v_exprFVarArgs_399_; lean_object* v_toProcess_400_; lean_object* v___x_402_; uint8_t v_isShared_403_; uint8_t v_isSharedCheck_409_; 
v_a_387_ = lean_ctor_get(v___x_386_, 0);
lean_inc(v_a_387_);
lean_dec_ref_known(v___x_386_, 1);
v___x_388_ = lean_st_ref_take(v_a_370_);
v_visitedLevel_389_ = lean_ctor_get(v___x_388_, 0);
v_visitedExpr_390_ = lean_ctor_get(v___x_388_, 1);
v_levelParams_391_ = lean_ctor_get(v___x_388_, 2);
v_nextLevelIdx_392_ = lean_ctor_get(v___x_388_, 3);
v_levelArgs_393_ = lean_ctor_get(v___x_388_, 4);
v_newLocalDecls_394_ = lean_ctor_get(v___x_388_, 5);
v_newLocalDeclsForMVars_395_ = lean_ctor_get(v___x_388_, 6);
v_newLetDecls_396_ = lean_ctor_get(v___x_388_, 7);
v_nextExprIdx_397_ = lean_ctor_get(v___x_388_, 8);
v_exprMVarArgs_398_ = lean_ctor_get(v___x_388_, 9);
v_exprFVarArgs_399_ = lean_ctor_get(v___x_388_, 10);
v_toProcess_400_ = lean_ctor_get(v___x_388_, 11);
v_isSharedCheck_409_ = !lean_is_exclusive(v___x_388_);
if (v_isSharedCheck_409_ == 0)
{
v___x_402_ = v___x_388_;
v_isShared_403_ = v_isSharedCheck_409_;
goto v_resetjp_401_;
}
else
{
lean_inc(v_toProcess_400_);
lean_inc(v_exprFVarArgs_399_);
lean_inc(v_exprMVarArgs_398_);
lean_inc(v_nextExprIdx_397_);
lean_inc(v_newLetDecls_396_);
lean_inc(v_newLocalDeclsForMVars_395_);
lean_inc(v_newLocalDecls_394_);
lean_inc(v_levelArgs_393_);
lean_inc(v_nextLevelIdx_392_);
lean_inc(v_levelParams_391_);
lean_inc(v_visitedExpr_390_);
lean_inc(v_visitedLevel_389_);
lean_dec(v___x_388_);
v___x_402_ = lean_box(0);
v_isShared_403_ = v_isSharedCheck_409_;
goto v_resetjp_401_;
}
v_resetjp_401_:
{
lean_object* v___x_404_; lean_object* v___x_406_; 
lean_inc(v_a_387_);
lean_inc(v_a_373_);
v___x_404_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2___redArg(v_visitedLevel_389_, v_a_373_, v_a_387_);
if (v_isShared_403_ == 0)
{
lean_ctor_set(v___x_402_, 0, v___x_404_);
v___x_406_ = v___x_402_;
goto v_reusejp_405_;
}
else
{
lean_object* v_reuseFailAlloc_408_; 
v_reuseFailAlloc_408_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_408_, 0, v___x_404_);
lean_ctor_set(v_reuseFailAlloc_408_, 1, v_visitedExpr_390_);
lean_ctor_set(v_reuseFailAlloc_408_, 2, v_levelParams_391_);
lean_ctor_set(v_reuseFailAlloc_408_, 3, v_nextLevelIdx_392_);
lean_ctor_set(v_reuseFailAlloc_408_, 4, v_levelArgs_393_);
lean_ctor_set(v_reuseFailAlloc_408_, 5, v_newLocalDecls_394_);
lean_ctor_set(v_reuseFailAlloc_408_, 6, v_newLocalDeclsForMVars_395_);
lean_ctor_set(v_reuseFailAlloc_408_, 7, v_newLetDecls_396_);
lean_ctor_set(v_reuseFailAlloc_408_, 8, v_nextExprIdx_397_);
lean_ctor_set(v_reuseFailAlloc_408_, 9, v_exprMVarArgs_398_);
lean_ctor_set(v_reuseFailAlloc_408_, 10, v_exprFVarArgs_399_);
lean_ctor_set(v_reuseFailAlloc_408_, 11, v_toProcess_400_);
v___x_406_ = v_reuseFailAlloc_408_;
goto v_reusejp_405_;
}
v_reusejp_405_:
{
lean_object* v___x_407_; 
v___x_407_ = lean_st_ref_put(v_a_370_, v___x_406_);
v_a_375_ = v_a_387_;
goto v___jp_374_;
}
}
}
else
{
if (lean_obj_tag(v___x_386_) == 0)
{
lean_object* v_a_410_; 
v_a_410_ = lean_ctor_get(v___x_386_, 0);
lean_inc(v_a_410_);
lean_dec_ref_known(v___x_386_, 1);
v_a_375_ = v_a_410_;
goto v___jp_374_;
}
else
{
lean_dec_ref_known(v_x_369_, 1);
return v___x_386_;
}
}
}
else
{
lean_object* v_val_411_; 
v_val_411_ = lean_ctor_get(v___x_385_, 0);
lean_inc(v_val_411_);
lean_dec_ref_known(v___x_385_, 1);
v_a_375_ = v_val_411_;
goto v___jp_374_;
}
}
}
case 2:
{
lean_object* v_a_414_; lean_object* v_a_415_; lean_object* v___y_417_; lean_object* v_a_418_; lean_object* v___y_432_; lean_object* v_a_463_; uint8_t v___x_496_; 
v_a_414_ = lean_ctor_get(v_x_369_, 0);
v_a_415_ = lean_ctor_get(v_x_369_, 1);
v___x_496_ = l_Lean_Level_hasMVar(v_a_414_);
if (v___x_496_ == 0)
{
uint8_t v___x_497_; 
v___x_497_ = l_Lean_Level_hasParam(v_a_414_);
if (v___x_497_ == 0)
{
lean_inc(v_a_414_);
v_a_463_ = v_a_414_;
goto v___jp_462_;
}
else
{
goto v___jp_466_;
}
}
else
{
goto v___jp_466_;
}
v___jp_416_:
{
size_t v___x_419_; size_t v___x_420_; uint8_t v___x_421_; 
v___x_419_ = lean_ptr_addr(v_a_414_);
v___x_420_ = lean_ptr_addr(v___y_417_);
v___x_421_ = lean_usize_dec_eq(v___x_419_, v___x_420_);
if (v___x_421_ == 0)
{
lean_object* v___x_422_; lean_object* v___x_423_; 
lean_dec_ref_known(v_x_369_, 2);
v___x_422_ = l_Lean_mkLevelMax_x27(v___y_417_, v_a_418_);
v___x_423_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_423_, 0, v___x_422_);
return v___x_423_;
}
else
{
size_t v___x_424_; size_t v___x_425_; uint8_t v___x_426_; 
v___x_424_ = lean_ptr_addr(v_a_415_);
v___x_425_ = lean_ptr_addr(v_a_418_);
v___x_426_ = lean_usize_dec_eq(v___x_424_, v___x_425_);
if (v___x_426_ == 0)
{
lean_object* v___x_427_; lean_object* v___x_428_; 
lean_dec_ref_known(v_x_369_, 2);
v___x_427_ = l_Lean_mkLevelMax_x27(v___y_417_, v_a_418_);
v___x_428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_428_, 0, v___x_427_);
return v___x_428_;
}
else
{
lean_object* v___x_429_; lean_object* v___x_430_; 
v___x_429_ = l_Lean_simpLevelMax_x27(v___y_417_, v_a_418_, v_x_369_);
lean_dec_ref_known(v_x_369_, 2);
lean_dec(v_a_418_);
lean_dec(v___y_417_);
v___x_430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_430_, 0, v___x_429_);
return v___x_430_;
}
}
}
v___jp_431_:
{
lean_object* v___x_433_; lean_object* v_visitedLevel_434_; lean_object* v___x_435_; 
v___x_433_ = lean_st_ref_get(v_a_370_);
v_visitedLevel_434_ = lean_ctor_get(v___x_433_, 0);
lean_inc_ref(v_visitedLevel_434_);
lean_dec(v___x_433_);
v___x_435_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectLevelAux_spec__1___redArg(v_visitedLevel_434_, v_a_415_);
lean_dec_ref(v_visitedLevel_434_);
if (lean_obj_tag(v___x_435_) == 0)
{
lean_object* v___x_436_; 
lean_inc(v_a_415_);
v___x_436_ = l_Lean_Meta_Closure_collectLevelAux___redArg(v_a_415_, v_a_370_);
if (lean_obj_tag(v___x_436_) == 0)
{
lean_object* v_a_437_; lean_object* v___x_438_; lean_object* v_visitedLevel_439_; lean_object* v_visitedExpr_440_; lean_object* v_levelParams_441_; lean_object* v_nextLevelIdx_442_; lean_object* v_levelArgs_443_; lean_object* v_newLocalDecls_444_; lean_object* v_newLocalDeclsForMVars_445_; lean_object* v_newLetDecls_446_; lean_object* v_nextExprIdx_447_; lean_object* v_exprMVarArgs_448_; lean_object* v_exprFVarArgs_449_; lean_object* v_toProcess_450_; lean_object* v___x_452_; uint8_t v_isShared_453_; uint8_t v_isSharedCheck_459_; 
v_a_437_ = lean_ctor_get(v___x_436_, 0);
lean_inc(v_a_437_);
lean_dec_ref_known(v___x_436_, 1);
v___x_438_ = lean_st_ref_take(v_a_370_);
v_visitedLevel_439_ = lean_ctor_get(v___x_438_, 0);
v_visitedExpr_440_ = lean_ctor_get(v___x_438_, 1);
v_levelParams_441_ = lean_ctor_get(v___x_438_, 2);
v_nextLevelIdx_442_ = lean_ctor_get(v___x_438_, 3);
v_levelArgs_443_ = lean_ctor_get(v___x_438_, 4);
v_newLocalDecls_444_ = lean_ctor_get(v___x_438_, 5);
v_newLocalDeclsForMVars_445_ = lean_ctor_get(v___x_438_, 6);
v_newLetDecls_446_ = lean_ctor_get(v___x_438_, 7);
v_nextExprIdx_447_ = lean_ctor_get(v___x_438_, 8);
v_exprMVarArgs_448_ = lean_ctor_get(v___x_438_, 9);
v_exprFVarArgs_449_ = lean_ctor_get(v___x_438_, 10);
v_toProcess_450_ = lean_ctor_get(v___x_438_, 11);
v_isSharedCheck_459_ = !lean_is_exclusive(v___x_438_);
if (v_isSharedCheck_459_ == 0)
{
v___x_452_ = v___x_438_;
v_isShared_453_ = v_isSharedCheck_459_;
goto v_resetjp_451_;
}
else
{
lean_inc(v_toProcess_450_);
lean_inc(v_exprFVarArgs_449_);
lean_inc(v_exprMVarArgs_448_);
lean_inc(v_nextExprIdx_447_);
lean_inc(v_newLetDecls_446_);
lean_inc(v_newLocalDeclsForMVars_445_);
lean_inc(v_newLocalDecls_444_);
lean_inc(v_levelArgs_443_);
lean_inc(v_nextLevelIdx_442_);
lean_inc(v_levelParams_441_);
lean_inc(v_visitedExpr_440_);
lean_inc(v_visitedLevel_439_);
lean_dec(v___x_438_);
v___x_452_ = lean_box(0);
v_isShared_453_ = v_isSharedCheck_459_;
goto v_resetjp_451_;
}
v_resetjp_451_:
{
lean_object* v___x_454_; lean_object* v___x_456_; 
lean_inc(v_a_437_);
lean_inc(v_a_415_);
v___x_454_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2___redArg(v_visitedLevel_439_, v_a_415_, v_a_437_);
if (v_isShared_453_ == 0)
{
lean_ctor_set(v___x_452_, 0, v___x_454_);
v___x_456_ = v___x_452_;
goto v_reusejp_455_;
}
else
{
lean_object* v_reuseFailAlloc_458_; 
v_reuseFailAlloc_458_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_458_, 0, v___x_454_);
lean_ctor_set(v_reuseFailAlloc_458_, 1, v_visitedExpr_440_);
lean_ctor_set(v_reuseFailAlloc_458_, 2, v_levelParams_441_);
lean_ctor_set(v_reuseFailAlloc_458_, 3, v_nextLevelIdx_442_);
lean_ctor_set(v_reuseFailAlloc_458_, 4, v_levelArgs_443_);
lean_ctor_set(v_reuseFailAlloc_458_, 5, v_newLocalDecls_444_);
lean_ctor_set(v_reuseFailAlloc_458_, 6, v_newLocalDeclsForMVars_445_);
lean_ctor_set(v_reuseFailAlloc_458_, 7, v_newLetDecls_446_);
lean_ctor_set(v_reuseFailAlloc_458_, 8, v_nextExprIdx_447_);
lean_ctor_set(v_reuseFailAlloc_458_, 9, v_exprMVarArgs_448_);
lean_ctor_set(v_reuseFailAlloc_458_, 10, v_exprFVarArgs_449_);
lean_ctor_set(v_reuseFailAlloc_458_, 11, v_toProcess_450_);
v___x_456_ = v_reuseFailAlloc_458_;
goto v_reusejp_455_;
}
v_reusejp_455_:
{
lean_object* v___x_457_; 
v___x_457_ = lean_st_ref_put(v_a_370_, v___x_456_);
v___y_417_ = v___y_432_;
v_a_418_ = v_a_437_;
goto v___jp_416_;
}
}
}
else
{
if (lean_obj_tag(v___x_436_) == 0)
{
lean_object* v_a_460_; 
v_a_460_ = lean_ctor_get(v___x_436_, 0);
lean_inc(v_a_460_);
lean_dec_ref_known(v___x_436_, 1);
v___y_417_ = v___y_432_;
v_a_418_ = v_a_460_;
goto v___jp_416_;
}
else
{
lean_dec(v___y_432_);
lean_dec_ref_known(v_x_369_, 2);
return v___x_436_;
}
}
}
else
{
lean_object* v_val_461_; 
v_val_461_ = lean_ctor_get(v___x_435_, 0);
lean_inc(v_val_461_);
lean_dec_ref_known(v___x_435_, 1);
v___y_417_ = v___y_432_;
v_a_418_ = v_val_461_;
goto v___jp_416_;
}
}
v___jp_462_:
{
uint8_t v___x_464_; 
v___x_464_ = l_Lean_Level_hasMVar(v_a_415_);
if (v___x_464_ == 0)
{
uint8_t v___x_465_; 
v___x_465_ = l_Lean_Level_hasParam(v_a_415_);
if (v___x_465_ == 0)
{
lean_inc(v_a_415_);
v___y_417_ = v_a_463_;
v_a_418_ = v_a_415_;
goto v___jp_416_;
}
else
{
v___y_432_ = v_a_463_;
goto v___jp_431_;
}
}
else
{
v___y_432_ = v_a_463_;
goto v___jp_431_;
}
}
v___jp_466_:
{
lean_object* v___x_467_; lean_object* v_visitedLevel_468_; lean_object* v___x_469_; 
v___x_467_ = lean_st_ref_get(v_a_370_);
v_visitedLevel_468_ = lean_ctor_get(v___x_467_, 0);
lean_inc_ref(v_visitedLevel_468_);
lean_dec(v___x_467_);
v___x_469_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectLevelAux_spec__1___redArg(v_visitedLevel_468_, v_a_414_);
lean_dec_ref(v_visitedLevel_468_);
if (lean_obj_tag(v___x_469_) == 0)
{
lean_object* v___x_470_; 
lean_inc(v_a_414_);
v___x_470_ = l_Lean_Meta_Closure_collectLevelAux___redArg(v_a_414_, v_a_370_);
if (lean_obj_tag(v___x_470_) == 0)
{
lean_object* v_a_471_; lean_object* v___x_472_; lean_object* v_visitedLevel_473_; lean_object* v_visitedExpr_474_; lean_object* v_levelParams_475_; lean_object* v_nextLevelIdx_476_; lean_object* v_levelArgs_477_; lean_object* v_newLocalDecls_478_; lean_object* v_newLocalDeclsForMVars_479_; lean_object* v_newLetDecls_480_; lean_object* v_nextExprIdx_481_; lean_object* v_exprMVarArgs_482_; lean_object* v_exprFVarArgs_483_; lean_object* v_toProcess_484_; lean_object* v___x_486_; uint8_t v_isShared_487_; uint8_t v_isSharedCheck_493_; 
v_a_471_ = lean_ctor_get(v___x_470_, 0);
lean_inc(v_a_471_);
lean_dec_ref_known(v___x_470_, 1);
v___x_472_ = lean_st_ref_take(v_a_370_);
v_visitedLevel_473_ = lean_ctor_get(v___x_472_, 0);
v_visitedExpr_474_ = lean_ctor_get(v___x_472_, 1);
v_levelParams_475_ = lean_ctor_get(v___x_472_, 2);
v_nextLevelIdx_476_ = lean_ctor_get(v___x_472_, 3);
v_levelArgs_477_ = lean_ctor_get(v___x_472_, 4);
v_newLocalDecls_478_ = lean_ctor_get(v___x_472_, 5);
v_newLocalDeclsForMVars_479_ = lean_ctor_get(v___x_472_, 6);
v_newLetDecls_480_ = lean_ctor_get(v___x_472_, 7);
v_nextExprIdx_481_ = lean_ctor_get(v___x_472_, 8);
v_exprMVarArgs_482_ = lean_ctor_get(v___x_472_, 9);
v_exprFVarArgs_483_ = lean_ctor_get(v___x_472_, 10);
v_toProcess_484_ = lean_ctor_get(v___x_472_, 11);
v_isSharedCheck_493_ = !lean_is_exclusive(v___x_472_);
if (v_isSharedCheck_493_ == 0)
{
v___x_486_ = v___x_472_;
v_isShared_487_ = v_isSharedCheck_493_;
goto v_resetjp_485_;
}
else
{
lean_inc(v_toProcess_484_);
lean_inc(v_exprFVarArgs_483_);
lean_inc(v_exprMVarArgs_482_);
lean_inc(v_nextExprIdx_481_);
lean_inc(v_newLetDecls_480_);
lean_inc(v_newLocalDeclsForMVars_479_);
lean_inc(v_newLocalDecls_478_);
lean_inc(v_levelArgs_477_);
lean_inc(v_nextLevelIdx_476_);
lean_inc(v_levelParams_475_);
lean_inc(v_visitedExpr_474_);
lean_inc(v_visitedLevel_473_);
lean_dec(v___x_472_);
v___x_486_ = lean_box(0);
v_isShared_487_ = v_isSharedCheck_493_;
goto v_resetjp_485_;
}
v_resetjp_485_:
{
lean_object* v___x_488_; lean_object* v___x_490_; 
lean_inc(v_a_471_);
lean_inc(v_a_414_);
v___x_488_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2___redArg(v_visitedLevel_473_, v_a_414_, v_a_471_);
if (v_isShared_487_ == 0)
{
lean_ctor_set(v___x_486_, 0, v___x_488_);
v___x_490_ = v___x_486_;
goto v_reusejp_489_;
}
else
{
lean_object* v_reuseFailAlloc_492_; 
v_reuseFailAlloc_492_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_492_, 0, v___x_488_);
lean_ctor_set(v_reuseFailAlloc_492_, 1, v_visitedExpr_474_);
lean_ctor_set(v_reuseFailAlloc_492_, 2, v_levelParams_475_);
lean_ctor_set(v_reuseFailAlloc_492_, 3, v_nextLevelIdx_476_);
lean_ctor_set(v_reuseFailAlloc_492_, 4, v_levelArgs_477_);
lean_ctor_set(v_reuseFailAlloc_492_, 5, v_newLocalDecls_478_);
lean_ctor_set(v_reuseFailAlloc_492_, 6, v_newLocalDeclsForMVars_479_);
lean_ctor_set(v_reuseFailAlloc_492_, 7, v_newLetDecls_480_);
lean_ctor_set(v_reuseFailAlloc_492_, 8, v_nextExprIdx_481_);
lean_ctor_set(v_reuseFailAlloc_492_, 9, v_exprMVarArgs_482_);
lean_ctor_set(v_reuseFailAlloc_492_, 10, v_exprFVarArgs_483_);
lean_ctor_set(v_reuseFailAlloc_492_, 11, v_toProcess_484_);
v___x_490_ = v_reuseFailAlloc_492_;
goto v_reusejp_489_;
}
v_reusejp_489_:
{
lean_object* v___x_491_; 
v___x_491_ = lean_st_ref_put(v_a_370_, v___x_490_);
v_a_463_ = v_a_471_;
goto v___jp_462_;
}
}
}
else
{
if (lean_obj_tag(v___x_470_) == 0)
{
lean_object* v_a_494_; 
v_a_494_ = lean_ctor_get(v___x_470_, 0);
lean_inc(v_a_494_);
lean_dec_ref_known(v___x_470_, 1);
v_a_463_ = v_a_494_;
goto v___jp_462_;
}
else
{
lean_dec_ref_known(v_x_369_, 2);
return v___x_470_;
}
}
}
else
{
lean_object* v_val_495_; 
v_val_495_ = lean_ctor_get(v___x_469_, 0);
lean_inc(v_val_495_);
lean_dec_ref_known(v___x_469_, 1);
v_a_463_ = v_val_495_;
goto v___jp_462_;
}
}
}
case 3:
{
lean_object* v_a_498_; lean_object* v_a_499_; lean_object* v___y_501_; lean_object* v_a_502_; lean_object* v___y_516_; lean_object* v_a_547_; uint8_t v___x_580_; 
v_a_498_ = lean_ctor_get(v_x_369_, 0);
v_a_499_ = lean_ctor_get(v_x_369_, 1);
v___x_580_ = l_Lean_Level_hasMVar(v_a_498_);
if (v___x_580_ == 0)
{
uint8_t v___x_581_; 
v___x_581_ = l_Lean_Level_hasParam(v_a_498_);
if (v___x_581_ == 0)
{
lean_inc(v_a_498_);
v_a_547_ = v_a_498_;
goto v___jp_546_;
}
else
{
goto v___jp_550_;
}
}
else
{
goto v___jp_550_;
}
v___jp_500_:
{
size_t v___x_503_; size_t v___x_504_; uint8_t v___x_505_; 
v___x_503_ = lean_ptr_addr(v_a_498_);
v___x_504_ = lean_ptr_addr(v___y_501_);
v___x_505_ = lean_usize_dec_eq(v___x_503_, v___x_504_);
if (v___x_505_ == 0)
{
lean_object* v___x_506_; lean_object* v___x_507_; 
lean_dec_ref_known(v_x_369_, 2);
v___x_506_ = l_Lean_mkLevelIMax_x27(v___y_501_, v_a_502_);
v___x_507_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_507_, 0, v___x_506_);
return v___x_507_;
}
else
{
size_t v___x_508_; size_t v___x_509_; uint8_t v___x_510_; 
v___x_508_ = lean_ptr_addr(v_a_499_);
v___x_509_ = lean_ptr_addr(v_a_502_);
v___x_510_ = lean_usize_dec_eq(v___x_508_, v___x_509_);
if (v___x_510_ == 0)
{
lean_object* v___x_511_; lean_object* v___x_512_; 
lean_dec_ref_known(v_x_369_, 2);
v___x_511_ = l_Lean_mkLevelIMax_x27(v___y_501_, v_a_502_);
v___x_512_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_512_, 0, v___x_511_);
return v___x_512_;
}
else
{
lean_object* v___x_513_; lean_object* v___x_514_; 
v___x_513_ = l_Lean_simpLevelIMax_x27(v___y_501_, v_a_502_, v_x_369_);
lean_dec_ref_known(v_x_369_, 2);
v___x_514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_514_, 0, v___x_513_);
return v___x_514_;
}
}
}
v___jp_515_:
{
lean_object* v___x_517_; lean_object* v_visitedLevel_518_; lean_object* v___x_519_; 
v___x_517_ = lean_st_ref_get(v_a_370_);
v_visitedLevel_518_ = lean_ctor_get(v___x_517_, 0);
lean_inc_ref(v_visitedLevel_518_);
lean_dec(v___x_517_);
v___x_519_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectLevelAux_spec__1___redArg(v_visitedLevel_518_, v_a_499_);
lean_dec_ref(v_visitedLevel_518_);
if (lean_obj_tag(v___x_519_) == 0)
{
lean_object* v___x_520_; 
lean_inc(v_a_499_);
v___x_520_ = l_Lean_Meta_Closure_collectLevelAux___redArg(v_a_499_, v_a_370_);
if (lean_obj_tag(v___x_520_) == 0)
{
lean_object* v_a_521_; lean_object* v___x_522_; lean_object* v_visitedLevel_523_; lean_object* v_visitedExpr_524_; lean_object* v_levelParams_525_; lean_object* v_nextLevelIdx_526_; lean_object* v_levelArgs_527_; lean_object* v_newLocalDecls_528_; lean_object* v_newLocalDeclsForMVars_529_; lean_object* v_newLetDecls_530_; lean_object* v_nextExprIdx_531_; lean_object* v_exprMVarArgs_532_; lean_object* v_exprFVarArgs_533_; lean_object* v_toProcess_534_; lean_object* v___x_536_; uint8_t v_isShared_537_; uint8_t v_isSharedCheck_543_; 
v_a_521_ = lean_ctor_get(v___x_520_, 0);
lean_inc(v_a_521_);
lean_dec_ref_known(v___x_520_, 1);
v___x_522_ = lean_st_ref_take(v_a_370_);
v_visitedLevel_523_ = lean_ctor_get(v___x_522_, 0);
v_visitedExpr_524_ = lean_ctor_get(v___x_522_, 1);
v_levelParams_525_ = lean_ctor_get(v___x_522_, 2);
v_nextLevelIdx_526_ = lean_ctor_get(v___x_522_, 3);
v_levelArgs_527_ = lean_ctor_get(v___x_522_, 4);
v_newLocalDecls_528_ = lean_ctor_get(v___x_522_, 5);
v_newLocalDeclsForMVars_529_ = lean_ctor_get(v___x_522_, 6);
v_newLetDecls_530_ = lean_ctor_get(v___x_522_, 7);
v_nextExprIdx_531_ = lean_ctor_get(v___x_522_, 8);
v_exprMVarArgs_532_ = lean_ctor_get(v___x_522_, 9);
v_exprFVarArgs_533_ = lean_ctor_get(v___x_522_, 10);
v_toProcess_534_ = lean_ctor_get(v___x_522_, 11);
v_isSharedCheck_543_ = !lean_is_exclusive(v___x_522_);
if (v_isSharedCheck_543_ == 0)
{
v___x_536_ = v___x_522_;
v_isShared_537_ = v_isSharedCheck_543_;
goto v_resetjp_535_;
}
else
{
lean_inc(v_toProcess_534_);
lean_inc(v_exprFVarArgs_533_);
lean_inc(v_exprMVarArgs_532_);
lean_inc(v_nextExprIdx_531_);
lean_inc(v_newLetDecls_530_);
lean_inc(v_newLocalDeclsForMVars_529_);
lean_inc(v_newLocalDecls_528_);
lean_inc(v_levelArgs_527_);
lean_inc(v_nextLevelIdx_526_);
lean_inc(v_levelParams_525_);
lean_inc(v_visitedExpr_524_);
lean_inc(v_visitedLevel_523_);
lean_dec(v___x_522_);
v___x_536_ = lean_box(0);
v_isShared_537_ = v_isSharedCheck_543_;
goto v_resetjp_535_;
}
v_resetjp_535_:
{
lean_object* v___x_538_; lean_object* v___x_540_; 
lean_inc(v_a_521_);
lean_inc(v_a_499_);
v___x_538_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2___redArg(v_visitedLevel_523_, v_a_499_, v_a_521_);
if (v_isShared_537_ == 0)
{
lean_ctor_set(v___x_536_, 0, v___x_538_);
v___x_540_ = v___x_536_;
goto v_reusejp_539_;
}
else
{
lean_object* v_reuseFailAlloc_542_; 
v_reuseFailAlloc_542_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_542_, 0, v___x_538_);
lean_ctor_set(v_reuseFailAlloc_542_, 1, v_visitedExpr_524_);
lean_ctor_set(v_reuseFailAlloc_542_, 2, v_levelParams_525_);
lean_ctor_set(v_reuseFailAlloc_542_, 3, v_nextLevelIdx_526_);
lean_ctor_set(v_reuseFailAlloc_542_, 4, v_levelArgs_527_);
lean_ctor_set(v_reuseFailAlloc_542_, 5, v_newLocalDecls_528_);
lean_ctor_set(v_reuseFailAlloc_542_, 6, v_newLocalDeclsForMVars_529_);
lean_ctor_set(v_reuseFailAlloc_542_, 7, v_newLetDecls_530_);
lean_ctor_set(v_reuseFailAlloc_542_, 8, v_nextExprIdx_531_);
lean_ctor_set(v_reuseFailAlloc_542_, 9, v_exprMVarArgs_532_);
lean_ctor_set(v_reuseFailAlloc_542_, 10, v_exprFVarArgs_533_);
lean_ctor_set(v_reuseFailAlloc_542_, 11, v_toProcess_534_);
v___x_540_ = v_reuseFailAlloc_542_;
goto v_reusejp_539_;
}
v_reusejp_539_:
{
lean_object* v___x_541_; 
v___x_541_ = lean_st_ref_put(v_a_370_, v___x_540_);
v___y_501_ = v___y_516_;
v_a_502_ = v_a_521_;
goto v___jp_500_;
}
}
}
else
{
if (lean_obj_tag(v___x_520_) == 0)
{
lean_object* v_a_544_; 
v_a_544_ = lean_ctor_get(v___x_520_, 0);
lean_inc(v_a_544_);
lean_dec_ref_known(v___x_520_, 1);
v___y_501_ = v___y_516_;
v_a_502_ = v_a_544_;
goto v___jp_500_;
}
else
{
lean_dec(v___y_516_);
lean_dec_ref_known(v_x_369_, 2);
return v___x_520_;
}
}
}
else
{
lean_object* v_val_545_; 
v_val_545_ = lean_ctor_get(v___x_519_, 0);
lean_inc(v_val_545_);
lean_dec_ref_known(v___x_519_, 1);
v___y_501_ = v___y_516_;
v_a_502_ = v_val_545_;
goto v___jp_500_;
}
}
v___jp_546_:
{
uint8_t v___x_548_; 
v___x_548_ = l_Lean_Level_hasMVar(v_a_499_);
if (v___x_548_ == 0)
{
uint8_t v___x_549_; 
v___x_549_ = l_Lean_Level_hasParam(v_a_499_);
if (v___x_549_ == 0)
{
lean_inc(v_a_499_);
v___y_501_ = v_a_547_;
v_a_502_ = v_a_499_;
goto v___jp_500_;
}
else
{
v___y_516_ = v_a_547_;
goto v___jp_515_;
}
}
else
{
v___y_516_ = v_a_547_;
goto v___jp_515_;
}
}
v___jp_550_:
{
lean_object* v___x_551_; lean_object* v_visitedLevel_552_; lean_object* v___x_553_; 
v___x_551_ = lean_st_ref_get(v_a_370_);
v_visitedLevel_552_ = lean_ctor_get(v___x_551_, 0);
lean_inc_ref(v_visitedLevel_552_);
lean_dec(v___x_551_);
v___x_553_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectLevelAux_spec__1___redArg(v_visitedLevel_552_, v_a_498_);
lean_dec_ref(v_visitedLevel_552_);
if (lean_obj_tag(v___x_553_) == 0)
{
lean_object* v___x_554_; 
lean_inc(v_a_498_);
v___x_554_ = l_Lean_Meta_Closure_collectLevelAux___redArg(v_a_498_, v_a_370_);
if (lean_obj_tag(v___x_554_) == 0)
{
lean_object* v_a_555_; lean_object* v___x_556_; lean_object* v_visitedLevel_557_; lean_object* v_visitedExpr_558_; lean_object* v_levelParams_559_; lean_object* v_nextLevelIdx_560_; lean_object* v_levelArgs_561_; lean_object* v_newLocalDecls_562_; lean_object* v_newLocalDeclsForMVars_563_; lean_object* v_newLetDecls_564_; lean_object* v_nextExprIdx_565_; lean_object* v_exprMVarArgs_566_; lean_object* v_exprFVarArgs_567_; lean_object* v_toProcess_568_; lean_object* v___x_570_; uint8_t v_isShared_571_; uint8_t v_isSharedCheck_577_; 
v_a_555_ = lean_ctor_get(v___x_554_, 0);
lean_inc(v_a_555_);
lean_dec_ref_known(v___x_554_, 1);
v___x_556_ = lean_st_ref_take(v_a_370_);
v_visitedLevel_557_ = lean_ctor_get(v___x_556_, 0);
v_visitedExpr_558_ = lean_ctor_get(v___x_556_, 1);
v_levelParams_559_ = lean_ctor_get(v___x_556_, 2);
v_nextLevelIdx_560_ = lean_ctor_get(v___x_556_, 3);
v_levelArgs_561_ = lean_ctor_get(v___x_556_, 4);
v_newLocalDecls_562_ = lean_ctor_get(v___x_556_, 5);
v_newLocalDeclsForMVars_563_ = lean_ctor_get(v___x_556_, 6);
v_newLetDecls_564_ = lean_ctor_get(v___x_556_, 7);
v_nextExprIdx_565_ = lean_ctor_get(v___x_556_, 8);
v_exprMVarArgs_566_ = lean_ctor_get(v___x_556_, 9);
v_exprFVarArgs_567_ = lean_ctor_get(v___x_556_, 10);
v_toProcess_568_ = lean_ctor_get(v___x_556_, 11);
v_isSharedCheck_577_ = !lean_is_exclusive(v___x_556_);
if (v_isSharedCheck_577_ == 0)
{
v___x_570_ = v___x_556_;
v_isShared_571_ = v_isSharedCheck_577_;
goto v_resetjp_569_;
}
else
{
lean_inc(v_toProcess_568_);
lean_inc(v_exprFVarArgs_567_);
lean_inc(v_exprMVarArgs_566_);
lean_inc(v_nextExprIdx_565_);
lean_inc(v_newLetDecls_564_);
lean_inc(v_newLocalDeclsForMVars_563_);
lean_inc(v_newLocalDecls_562_);
lean_inc(v_levelArgs_561_);
lean_inc(v_nextLevelIdx_560_);
lean_inc(v_levelParams_559_);
lean_inc(v_visitedExpr_558_);
lean_inc(v_visitedLevel_557_);
lean_dec(v___x_556_);
v___x_570_ = lean_box(0);
v_isShared_571_ = v_isSharedCheck_577_;
goto v_resetjp_569_;
}
v_resetjp_569_:
{
lean_object* v___x_572_; lean_object* v___x_574_; 
lean_inc(v_a_555_);
lean_inc(v_a_498_);
v___x_572_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2___redArg(v_visitedLevel_557_, v_a_498_, v_a_555_);
if (v_isShared_571_ == 0)
{
lean_ctor_set(v___x_570_, 0, v___x_572_);
v___x_574_ = v___x_570_;
goto v_reusejp_573_;
}
else
{
lean_object* v_reuseFailAlloc_576_; 
v_reuseFailAlloc_576_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_576_, 0, v___x_572_);
lean_ctor_set(v_reuseFailAlloc_576_, 1, v_visitedExpr_558_);
lean_ctor_set(v_reuseFailAlloc_576_, 2, v_levelParams_559_);
lean_ctor_set(v_reuseFailAlloc_576_, 3, v_nextLevelIdx_560_);
lean_ctor_set(v_reuseFailAlloc_576_, 4, v_levelArgs_561_);
lean_ctor_set(v_reuseFailAlloc_576_, 5, v_newLocalDecls_562_);
lean_ctor_set(v_reuseFailAlloc_576_, 6, v_newLocalDeclsForMVars_563_);
lean_ctor_set(v_reuseFailAlloc_576_, 7, v_newLetDecls_564_);
lean_ctor_set(v_reuseFailAlloc_576_, 8, v_nextExprIdx_565_);
lean_ctor_set(v_reuseFailAlloc_576_, 9, v_exprMVarArgs_566_);
lean_ctor_set(v_reuseFailAlloc_576_, 10, v_exprFVarArgs_567_);
lean_ctor_set(v_reuseFailAlloc_576_, 11, v_toProcess_568_);
v___x_574_ = v_reuseFailAlloc_576_;
goto v_reusejp_573_;
}
v_reusejp_573_:
{
lean_object* v___x_575_; 
v___x_575_ = lean_st_ref_put(v_a_370_, v___x_574_);
v_a_547_ = v_a_555_;
goto v___jp_546_;
}
}
}
else
{
if (lean_obj_tag(v___x_554_) == 0)
{
lean_object* v_a_578_; 
v_a_578_ = lean_ctor_get(v___x_554_, 0);
lean_inc(v_a_578_);
lean_dec_ref_known(v___x_554_, 1);
v_a_547_ = v_a_578_;
goto v___jp_546_;
}
else
{
lean_dec_ref_known(v_x_369_, 2);
return v___x_554_;
}
}
}
else
{
lean_object* v_val_579_; 
v_val_579_ = lean_ctor_get(v___x_553_, 0);
lean_inc(v_val_579_);
lean_dec_ref_known(v___x_553_, 1);
v_a_547_ = v_val_579_;
goto v___jp_546_;
}
}
}
default: 
{
lean_object* v___x_582_; 
v___x_582_ = l_Lean_Meta_Closure_mkNewLevelParam___redArg(v_x_369_, v_a_370_);
return v___x_582_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectLevelAux___redArg___boxed(lean_object* v_x_583_, lean_object* v_a_584_, lean_object* v_a_585_){
_start:
{
lean_object* v_res_586_; 
v_res_586_ = l_Lean_Meta_Closure_collectLevelAux___redArg(v_x_583_, v_a_584_);
lean_dec(v_a_584_);
return v_res_586_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectLevelAux(lean_object* v_x_587_, uint8_t v_a_588_, lean_object* v_a_589_, lean_object* v_a_590_, lean_object* v_a_591_, lean_object* v_a_592_, lean_object* v_a_593_){
_start:
{
lean_object* v___x_595_; 
v___x_595_ = l_Lean_Meta_Closure_collectLevelAux___redArg(v_x_587_, v_a_589_);
return v___x_595_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectLevelAux___boxed(lean_object* v_x_596_, lean_object* v_a_597_, lean_object* v_a_598_, lean_object* v_a_599_, lean_object* v_a_600_, lean_object* v_a_601_, lean_object* v_a_602_, lean_object* v_a_603_){
_start:
{
uint8_t v_a_boxed_604_; lean_object* v_res_605_; 
v_a_boxed_604_ = lean_unbox(v_a_597_);
v_res_605_ = l_Lean_Meta_Closure_collectLevelAux(v_x_596_, v_a_boxed_604_, v_a_598_, v_a_599_, v_a_600_, v_a_601_, v_a_602_);
lean_dec(v_a_602_);
lean_dec_ref(v_a_601_);
lean_dec(v_a_600_);
lean_dec_ref(v_a_599_);
lean_dec(v_a_598_);
return v_res_605_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectLevelAux_spec__1(lean_object* v_00_u03b2_606_, lean_object* v_m_607_, lean_object* v_a_608_){
_start:
{
lean_object* v___x_609_; 
v___x_609_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectLevelAux_spec__1___redArg(v_m_607_, v_a_608_);
return v___x_609_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectLevelAux_spec__1___boxed(lean_object* v_00_u03b2_610_, lean_object* v_m_611_, lean_object* v_a_612_){
_start:
{
lean_object* v_res_613_; 
v_res_613_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectLevelAux_spec__1(v_00_u03b2_610_, v_m_611_, v_a_612_);
lean_dec(v_a_612_);
lean_dec_ref(v_m_611_);
return v_res_613_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2(lean_object* v_00_u03b2_614_, lean_object* v_m_615_, lean_object* v_a_616_, lean_object* v_b_617_){
_start:
{
lean_object* v___x_618_; 
v___x_618_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2___redArg(v_m_615_, v_a_616_, v_b_617_);
return v___x_618_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectLevelAux_spec__1_spec__1(lean_object* v_00_u03b2_619_, lean_object* v_a_620_, lean_object* v_x_621_){
_start:
{
lean_object* v___x_622_; 
v___x_622_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectLevelAux_spec__1_spec__1___redArg(v_a_620_, v_x_621_);
return v___x_622_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectLevelAux_spec__1_spec__1___boxed(lean_object* v_00_u03b2_623_, lean_object* v_a_624_, lean_object* v_x_625_){
_start:
{
lean_object* v_res_626_; 
v_res_626_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectLevelAux_spec__1_spec__1(v_00_u03b2_623_, v_a_624_, v_x_625_);
lean_dec(v_x_625_);
lean_dec(v_a_624_);
return v_res_626_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__3(lean_object* v_00_u03b2_627_, lean_object* v_a_628_, lean_object* v_x_629_){
_start:
{
uint8_t v___x_630_; 
v___x_630_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__3___redArg(v_a_628_, v_x_629_);
return v___x_630_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__3___boxed(lean_object* v_00_u03b2_631_, lean_object* v_a_632_, lean_object* v_x_633_){
_start:
{
uint8_t v_res_634_; lean_object* v_r_635_; 
v_res_634_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__3(v_00_u03b2_631_, v_a_632_, v_x_633_);
lean_dec(v_x_633_);
lean_dec(v_a_632_);
v_r_635_ = lean_box(v_res_634_);
return v_r_635_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__4(lean_object* v_00_u03b2_636_, lean_object* v_data_637_){
_start:
{
lean_object* v___x_638_; 
v___x_638_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__4___redArg(v_data_637_);
return v___x_638_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__5(lean_object* v_00_u03b2_639_, lean_object* v_a_640_, lean_object* v_b_641_, lean_object* v_x_642_){
_start:
{
lean_object* v___x_643_; 
v___x_643_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__5___redArg(v_a_640_, v_b_641_, v_x_642_);
return v___x_643_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_644_, lean_object* v_i_645_, lean_object* v_source_646_, lean_object* v_target_647_){
_start:
{
lean_object* v___x_648_; 
v___x_648_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__4_spec__5___redArg(v_i_645_, v_source_646_, v_target_647_);
return v___x_648_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__4_spec__5_spec__6(lean_object* v_00_u03b2_649_, lean_object* v_x_650_, lean_object* v_x_651_){
_start:
{
lean_object* v___x_652_; 
v___x_652_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__4_spec__5_spec__6___redArg(v_x_650_, v_x_651_);
return v___x_652_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectLevel___redArg(lean_object* v_u_653_, lean_object* v_a_654_){
_start:
{
uint8_t v___x_699_; 
v___x_699_ = l_Lean_Level_hasMVar(v_u_653_);
if (v___x_699_ == 0)
{
uint8_t v___x_700_; 
v___x_700_ = l_Lean_Level_hasParam(v_u_653_);
if (v___x_700_ == 0)
{
lean_object* v___x_701_; 
v___x_701_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_701_, 0, v_u_653_);
return v___x_701_;
}
else
{
goto v___jp_656_;
}
}
else
{
goto v___jp_656_;
}
v___jp_656_:
{
lean_object* v___x_657_; lean_object* v_visitedLevel_658_; lean_object* v___x_659_; 
v___x_657_ = lean_st_ref_get(v_a_654_);
v_visitedLevel_658_ = lean_ctor_get(v___x_657_, 0);
lean_inc_ref(v_visitedLevel_658_);
lean_dec(v___x_657_);
v___x_659_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectLevelAux_spec__1___redArg(v_visitedLevel_658_, v_u_653_);
lean_dec_ref(v_visitedLevel_658_);
if (lean_obj_tag(v___x_659_) == 0)
{
lean_object* v___x_660_; 
lean_inc(v_u_653_);
v___x_660_ = l_Lean_Meta_Closure_collectLevelAux___redArg(v_u_653_, v_a_654_);
if (lean_obj_tag(v___x_660_) == 0)
{
lean_object* v_a_661_; lean_object* v___x_663_; uint8_t v_isShared_664_; uint8_t v_isSharedCheck_690_; 
v_a_661_ = lean_ctor_get(v___x_660_, 0);
v_isSharedCheck_690_ = !lean_is_exclusive(v___x_660_);
if (v_isSharedCheck_690_ == 0)
{
v___x_663_ = v___x_660_;
v_isShared_664_ = v_isSharedCheck_690_;
goto v_resetjp_662_;
}
else
{
lean_inc(v_a_661_);
lean_dec(v___x_660_);
v___x_663_ = lean_box(0);
v_isShared_664_ = v_isSharedCheck_690_;
goto v_resetjp_662_;
}
v_resetjp_662_:
{
lean_object* v___x_665_; lean_object* v_visitedLevel_666_; lean_object* v_visitedExpr_667_; lean_object* v_levelParams_668_; lean_object* v_nextLevelIdx_669_; lean_object* v_levelArgs_670_; lean_object* v_newLocalDecls_671_; lean_object* v_newLocalDeclsForMVars_672_; lean_object* v_newLetDecls_673_; lean_object* v_nextExprIdx_674_; lean_object* v_exprMVarArgs_675_; lean_object* v_exprFVarArgs_676_; lean_object* v_toProcess_677_; lean_object* v___x_679_; uint8_t v_isShared_680_; uint8_t v_isSharedCheck_689_; 
v___x_665_ = lean_st_ref_take(v_a_654_);
v_visitedLevel_666_ = lean_ctor_get(v___x_665_, 0);
v_visitedExpr_667_ = lean_ctor_get(v___x_665_, 1);
v_levelParams_668_ = lean_ctor_get(v___x_665_, 2);
v_nextLevelIdx_669_ = lean_ctor_get(v___x_665_, 3);
v_levelArgs_670_ = lean_ctor_get(v___x_665_, 4);
v_newLocalDecls_671_ = lean_ctor_get(v___x_665_, 5);
v_newLocalDeclsForMVars_672_ = lean_ctor_get(v___x_665_, 6);
v_newLetDecls_673_ = lean_ctor_get(v___x_665_, 7);
v_nextExprIdx_674_ = lean_ctor_get(v___x_665_, 8);
v_exprMVarArgs_675_ = lean_ctor_get(v___x_665_, 9);
v_exprFVarArgs_676_ = lean_ctor_get(v___x_665_, 10);
v_toProcess_677_ = lean_ctor_get(v___x_665_, 11);
v_isSharedCheck_689_ = !lean_is_exclusive(v___x_665_);
if (v_isSharedCheck_689_ == 0)
{
v___x_679_ = v___x_665_;
v_isShared_680_ = v_isSharedCheck_689_;
goto v_resetjp_678_;
}
else
{
lean_inc(v_toProcess_677_);
lean_inc(v_exprFVarArgs_676_);
lean_inc(v_exprMVarArgs_675_);
lean_inc(v_nextExprIdx_674_);
lean_inc(v_newLetDecls_673_);
lean_inc(v_newLocalDeclsForMVars_672_);
lean_inc(v_newLocalDecls_671_);
lean_inc(v_levelArgs_670_);
lean_inc(v_nextLevelIdx_669_);
lean_inc(v_levelParams_668_);
lean_inc(v_visitedExpr_667_);
lean_inc(v_visitedLevel_666_);
lean_dec(v___x_665_);
v___x_679_ = lean_box(0);
v_isShared_680_ = v_isSharedCheck_689_;
goto v_resetjp_678_;
}
v_resetjp_678_:
{
lean_object* v___x_681_; lean_object* v___x_683_; 
lean_inc(v_a_661_);
v___x_681_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2___redArg(v_visitedLevel_666_, v_u_653_, v_a_661_);
if (v_isShared_680_ == 0)
{
lean_ctor_set(v___x_679_, 0, v___x_681_);
v___x_683_ = v___x_679_;
goto v_reusejp_682_;
}
else
{
lean_object* v_reuseFailAlloc_688_; 
v_reuseFailAlloc_688_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_688_, 0, v___x_681_);
lean_ctor_set(v_reuseFailAlloc_688_, 1, v_visitedExpr_667_);
lean_ctor_set(v_reuseFailAlloc_688_, 2, v_levelParams_668_);
lean_ctor_set(v_reuseFailAlloc_688_, 3, v_nextLevelIdx_669_);
lean_ctor_set(v_reuseFailAlloc_688_, 4, v_levelArgs_670_);
lean_ctor_set(v_reuseFailAlloc_688_, 5, v_newLocalDecls_671_);
lean_ctor_set(v_reuseFailAlloc_688_, 6, v_newLocalDeclsForMVars_672_);
lean_ctor_set(v_reuseFailAlloc_688_, 7, v_newLetDecls_673_);
lean_ctor_set(v_reuseFailAlloc_688_, 8, v_nextExprIdx_674_);
lean_ctor_set(v_reuseFailAlloc_688_, 9, v_exprMVarArgs_675_);
lean_ctor_set(v_reuseFailAlloc_688_, 10, v_exprFVarArgs_676_);
lean_ctor_set(v_reuseFailAlloc_688_, 11, v_toProcess_677_);
v___x_683_ = v_reuseFailAlloc_688_;
goto v_reusejp_682_;
}
v_reusejp_682_:
{
lean_object* v___x_684_; lean_object* v___x_686_; 
v___x_684_ = lean_st_ref_put(v_a_654_, v___x_683_);
if (v_isShared_664_ == 0)
{
v___x_686_ = v___x_663_;
goto v_reusejp_685_;
}
else
{
lean_object* v_reuseFailAlloc_687_; 
v_reuseFailAlloc_687_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_687_, 0, v_a_661_);
v___x_686_ = v_reuseFailAlloc_687_;
goto v_reusejp_685_;
}
v_reusejp_685_:
{
return v___x_686_;
}
}
}
}
}
else
{
lean_dec(v_u_653_);
return v___x_660_;
}
}
else
{
lean_object* v_val_691_; lean_object* v___x_693_; uint8_t v_isShared_694_; uint8_t v_isSharedCheck_698_; 
lean_dec(v_u_653_);
v_val_691_ = lean_ctor_get(v___x_659_, 0);
v_isSharedCheck_698_ = !lean_is_exclusive(v___x_659_);
if (v_isSharedCheck_698_ == 0)
{
v___x_693_ = v___x_659_;
v_isShared_694_ = v_isSharedCheck_698_;
goto v_resetjp_692_;
}
else
{
lean_inc(v_val_691_);
lean_dec(v___x_659_);
v___x_693_ = lean_box(0);
v_isShared_694_ = v_isSharedCheck_698_;
goto v_resetjp_692_;
}
v_resetjp_692_:
{
lean_object* v___x_696_; 
if (v_isShared_694_ == 0)
{
lean_ctor_set_tag(v___x_693_, 0);
v___x_696_ = v___x_693_;
goto v_reusejp_695_;
}
else
{
lean_object* v_reuseFailAlloc_697_; 
v_reuseFailAlloc_697_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_697_, 0, v_val_691_);
v___x_696_ = v_reuseFailAlloc_697_;
goto v_reusejp_695_;
}
v_reusejp_695_:
{
return v___x_696_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectLevel___redArg___boxed(lean_object* v_u_702_, lean_object* v_a_703_, lean_object* v_a_704_){
_start:
{
lean_object* v_res_705_; 
v_res_705_ = l_Lean_Meta_Closure_collectLevel___redArg(v_u_702_, v_a_703_);
lean_dec(v_a_703_);
return v_res_705_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectLevel(lean_object* v_u_706_, uint8_t v_a_707_, lean_object* v_a_708_, lean_object* v_a_709_, lean_object* v_a_710_, lean_object* v_a_711_, lean_object* v_a_712_){
_start:
{
lean_object* v___x_714_; 
v___x_714_ = l_Lean_Meta_Closure_collectLevel___redArg(v_u_706_, v_a_708_);
return v___x_714_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectLevel___boxed(lean_object* v_u_715_, lean_object* v_a_716_, lean_object* v_a_717_, lean_object* v_a_718_, lean_object* v_a_719_, lean_object* v_a_720_, lean_object* v_a_721_, lean_object* v_a_722_){
_start:
{
uint8_t v_a_boxed_723_; lean_object* v_res_724_; 
v_a_boxed_723_ = lean_unbox(v_a_716_);
v_res_724_ = l_Lean_Meta_Closure_collectLevel(v_u_715_, v_a_boxed_723_, v_a_717_, v_a_718_, v_a_719_, v_a_720_, v_a_721_);
lean_dec(v_a_721_);
lean_dec_ref(v_a_720_);
lean_dec(v_a_719_);
lean_dec_ref(v_a_718_);
lean_dec(v_a_717_);
return v_res_724_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Closure_preprocess_spec__0___redArg(lean_object* v_e_725_, lean_object* v___y_726_){
_start:
{
uint8_t v___x_728_; 
v___x_728_ = l_Lean_Expr_hasMVar(v_e_725_);
if (v___x_728_ == 0)
{
lean_object* v___x_729_; 
v___x_729_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_729_, 0, v_e_725_);
return v___x_729_;
}
else
{
lean_object* v___x_730_; lean_object* v_mctx_731_; lean_object* v___x_732_; lean_object* v_fst_733_; lean_object* v_snd_734_; lean_object* v___x_735_; lean_object* v_cache_736_; lean_object* v_zetaDeltaFVarIds_737_; lean_object* v_postponed_738_; lean_object* v_diag_739_; lean_object* v___x_741_; uint8_t v_isShared_742_; uint8_t v_isSharedCheck_748_; 
v___x_730_ = lean_st_ref_get(v___y_726_);
v_mctx_731_ = lean_ctor_get(v___x_730_, 0);
lean_inc_ref(v_mctx_731_);
lean_dec(v___x_730_);
v___x_732_ = l_Lean_instantiateMVarsCore(v_mctx_731_, v_e_725_);
v_fst_733_ = lean_ctor_get(v___x_732_, 0);
lean_inc(v_fst_733_);
v_snd_734_ = lean_ctor_get(v___x_732_, 1);
lean_inc(v_snd_734_);
lean_dec_ref(v___x_732_);
v___x_735_ = lean_st_ref_take(v___y_726_);
v_cache_736_ = lean_ctor_get(v___x_735_, 1);
v_zetaDeltaFVarIds_737_ = lean_ctor_get(v___x_735_, 2);
v_postponed_738_ = lean_ctor_get(v___x_735_, 3);
v_diag_739_ = lean_ctor_get(v___x_735_, 4);
v_isSharedCheck_748_ = !lean_is_exclusive(v___x_735_);
if (v_isSharedCheck_748_ == 0)
{
lean_object* v_unused_749_; 
v_unused_749_ = lean_ctor_get(v___x_735_, 0);
lean_dec(v_unused_749_);
v___x_741_ = v___x_735_;
v_isShared_742_ = v_isSharedCheck_748_;
goto v_resetjp_740_;
}
else
{
lean_inc(v_diag_739_);
lean_inc(v_postponed_738_);
lean_inc(v_zetaDeltaFVarIds_737_);
lean_inc(v_cache_736_);
lean_dec(v___x_735_);
v___x_741_ = lean_box(0);
v_isShared_742_ = v_isSharedCheck_748_;
goto v_resetjp_740_;
}
v_resetjp_740_:
{
lean_object* v___x_744_; 
if (v_isShared_742_ == 0)
{
lean_ctor_set(v___x_741_, 0, v_snd_734_);
v___x_744_ = v___x_741_;
goto v_reusejp_743_;
}
else
{
lean_object* v_reuseFailAlloc_747_; 
v_reuseFailAlloc_747_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_747_, 0, v_snd_734_);
lean_ctor_set(v_reuseFailAlloc_747_, 1, v_cache_736_);
lean_ctor_set(v_reuseFailAlloc_747_, 2, v_zetaDeltaFVarIds_737_);
lean_ctor_set(v_reuseFailAlloc_747_, 3, v_postponed_738_);
lean_ctor_set(v_reuseFailAlloc_747_, 4, v_diag_739_);
v___x_744_ = v_reuseFailAlloc_747_;
goto v_reusejp_743_;
}
v_reusejp_743_:
{
lean_object* v___x_745_; lean_object* v___x_746_; 
v___x_745_ = lean_st_ref_put(v___y_726_, v___x_744_);
v___x_746_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_746_, 0, v_fst_733_);
return v___x_746_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Closure_preprocess_spec__0___redArg___boxed(lean_object* v_e_750_, lean_object* v___y_751_, lean_object* v___y_752_){
_start:
{
lean_object* v_res_753_; 
v_res_753_ = l_Lean_instantiateMVars___at___00Lean_Meta_Closure_preprocess_spec__0___redArg(v_e_750_, v___y_751_);
lean_dec(v___y_751_);
return v_res_753_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Closure_preprocess_spec__0(lean_object* v_e_754_, uint8_t v___y_755_, lean_object* v___y_756_, lean_object* v___y_757_, lean_object* v___y_758_, lean_object* v___y_759_, lean_object* v___y_760_){
_start:
{
lean_object* v___x_762_; 
v___x_762_ = l_Lean_instantiateMVars___at___00Lean_Meta_Closure_preprocess_spec__0___redArg(v_e_754_, v___y_758_);
return v___x_762_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Closure_preprocess_spec__0___boxed(lean_object* v_e_763_, lean_object* v___y_764_, lean_object* v___y_765_, lean_object* v___y_766_, lean_object* v___y_767_, lean_object* v___y_768_, lean_object* v___y_769_, lean_object* v___y_770_){
_start:
{
uint8_t v___y_2276__boxed_771_; lean_object* v_res_772_; 
v___y_2276__boxed_771_ = lean_unbox(v___y_764_);
v_res_772_ = l_Lean_instantiateMVars___at___00Lean_Meta_Closure_preprocess_spec__0(v_e_763_, v___y_2276__boxed_771_, v___y_765_, v___y_766_, v___y_767_, v___y_768_, v___y_769_);
lean_dec(v___y_769_);
lean_dec_ref(v___y_768_);
lean_dec(v___y_767_);
lean_dec_ref(v___y_766_);
lean_dec(v___y_765_);
return v_res_772_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_preprocess(lean_object* v_e_773_, uint8_t v_a_774_, lean_object* v_a_775_, lean_object* v_a_776_, lean_object* v_a_777_, lean_object* v_a_778_, lean_object* v_a_779_){
_start:
{
lean_object* v___x_781_; 
v___x_781_ = l_Lean_instantiateMVars___at___00Lean_Meta_Closure_preprocess_spec__0___redArg(v_e_773_, v_a_777_);
if (v_a_774_ == 0)
{
lean_object* v_a_782_; uint8_t v___x_783_; lean_object* v___x_784_; 
v_a_782_ = lean_ctor_get(v___x_781_, 0);
lean_inc_n(v_a_782_, 2);
lean_dec_ref(v___x_781_);
v___x_783_ = 0;
v___x_784_ = l_Lean_Meta_check(v_a_782_, v___x_783_, v_a_776_, v_a_777_, v_a_778_, v_a_779_);
if (lean_obj_tag(v___x_784_) == 0)
{
lean_object* v___x_786_; uint8_t v_isShared_787_; uint8_t v_isSharedCheck_791_; 
v_isSharedCheck_791_ = !lean_is_exclusive(v___x_784_);
if (v_isSharedCheck_791_ == 0)
{
lean_object* v_unused_792_; 
v_unused_792_ = lean_ctor_get(v___x_784_, 0);
lean_dec(v_unused_792_);
v___x_786_ = v___x_784_;
v_isShared_787_ = v_isSharedCheck_791_;
goto v_resetjp_785_;
}
else
{
lean_dec(v___x_784_);
v___x_786_ = lean_box(0);
v_isShared_787_ = v_isSharedCheck_791_;
goto v_resetjp_785_;
}
v_resetjp_785_:
{
lean_object* v___x_789_; 
if (v_isShared_787_ == 0)
{
lean_ctor_set(v___x_786_, 0, v_a_782_);
v___x_789_ = v___x_786_;
goto v_reusejp_788_;
}
else
{
lean_object* v_reuseFailAlloc_790_; 
v_reuseFailAlloc_790_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_790_, 0, v_a_782_);
v___x_789_ = v_reuseFailAlloc_790_;
goto v_reusejp_788_;
}
v_reusejp_788_:
{
return v___x_789_;
}
}
}
else
{
lean_object* v_a_793_; lean_object* v___x_795_; uint8_t v_isShared_796_; uint8_t v_isSharedCheck_800_; 
lean_dec(v_a_782_);
v_a_793_ = lean_ctor_get(v___x_784_, 0);
v_isSharedCheck_800_ = !lean_is_exclusive(v___x_784_);
if (v_isSharedCheck_800_ == 0)
{
v___x_795_ = v___x_784_;
v_isShared_796_ = v_isSharedCheck_800_;
goto v_resetjp_794_;
}
else
{
lean_inc(v_a_793_);
lean_dec(v___x_784_);
v___x_795_ = lean_box(0);
v_isShared_796_ = v_isSharedCheck_800_;
goto v_resetjp_794_;
}
v_resetjp_794_:
{
lean_object* v___x_798_; 
if (v_isShared_796_ == 0)
{
v___x_798_ = v___x_795_;
goto v_reusejp_797_;
}
else
{
lean_object* v_reuseFailAlloc_799_; 
v_reuseFailAlloc_799_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_799_, 0, v_a_793_);
v___x_798_ = v_reuseFailAlloc_799_;
goto v_reusejp_797_;
}
v_reusejp_797_:
{
return v___x_798_;
}
}
}
}
else
{
return v___x_781_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_preprocess___boxed(lean_object* v_e_801_, lean_object* v_a_802_, lean_object* v_a_803_, lean_object* v_a_804_, lean_object* v_a_805_, lean_object* v_a_806_, lean_object* v_a_807_, lean_object* v_a_808_){
_start:
{
uint8_t v_a_boxed_809_; lean_object* v_res_810_; 
v_a_boxed_809_ = lean_unbox(v_a_802_);
v_res_810_ = l_Lean_Meta_Closure_preprocess(v_e_801_, v_a_boxed_809_, v_a_803_, v_a_804_, v_a_805_, v_a_806_, v_a_807_);
lean_dec(v_a_807_);
lean_dec_ref(v_a_806_);
lean_dec(v_a_805_);
lean_dec_ref(v_a_804_);
lean_dec(v_a_803_);
return v_res_810_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkNextUserName___redArg(lean_object* v_a_814_){
_start:
{
lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v_visitedLevel_818_; lean_object* v_visitedExpr_819_; lean_object* v_levelParams_820_; lean_object* v_nextLevelIdx_821_; lean_object* v_levelArgs_822_; lean_object* v_newLocalDecls_823_; lean_object* v_newLocalDeclsForMVars_824_; lean_object* v_newLetDecls_825_; lean_object* v_nextExprIdx_826_; lean_object* v_exprMVarArgs_827_; lean_object* v_exprFVarArgs_828_; lean_object* v_toProcess_829_; lean_object* v___x_831_; uint8_t v_isShared_832_; uint8_t v_isSharedCheck_843_; 
v___x_816_ = lean_st_ref_get(v_a_814_);
v___x_817_ = lean_st_ref_take(v_a_814_);
v_visitedLevel_818_ = lean_ctor_get(v___x_817_, 0);
v_visitedExpr_819_ = lean_ctor_get(v___x_817_, 1);
v_levelParams_820_ = lean_ctor_get(v___x_817_, 2);
v_nextLevelIdx_821_ = lean_ctor_get(v___x_817_, 3);
v_levelArgs_822_ = lean_ctor_get(v___x_817_, 4);
v_newLocalDecls_823_ = lean_ctor_get(v___x_817_, 5);
v_newLocalDeclsForMVars_824_ = lean_ctor_get(v___x_817_, 6);
v_newLetDecls_825_ = lean_ctor_get(v___x_817_, 7);
v_nextExprIdx_826_ = lean_ctor_get(v___x_817_, 8);
v_exprMVarArgs_827_ = lean_ctor_get(v___x_817_, 9);
v_exprFVarArgs_828_ = lean_ctor_get(v___x_817_, 10);
v_toProcess_829_ = lean_ctor_get(v___x_817_, 11);
v_isSharedCheck_843_ = !lean_is_exclusive(v___x_817_);
if (v_isSharedCheck_843_ == 0)
{
v___x_831_ = v___x_817_;
v_isShared_832_ = v_isSharedCheck_843_;
goto v_resetjp_830_;
}
else
{
lean_inc(v_toProcess_829_);
lean_inc(v_exprFVarArgs_828_);
lean_inc(v_exprMVarArgs_827_);
lean_inc(v_nextExprIdx_826_);
lean_inc(v_newLetDecls_825_);
lean_inc(v_newLocalDeclsForMVars_824_);
lean_inc(v_newLocalDecls_823_);
lean_inc(v_levelArgs_822_);
lean_inc(v_nextLevelIdx_821_);
lean_inc(v_levelParams_820_);
lean_inc(v_visitedExpr_819_);
lean_inc(v_visitedLevel_818_);
lean_dec(v___x_817_);
v___x_831_ = lean_box(0);
v_isShared_832_ = v_isSharedCheck_843_;
goto v_resetjp_830_;
}
v_resetjp_830_:
{
lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_836_; 
v___x_833_ = lean_unsigned_to_nat(1u);
v___x_834_ = lean_nat_add(v_nextExprIdx_826_, v___x_833_);
lean_dec(v_nextExprIdx_826_);
if (v_isShared_832_ == 0)
{
lean_ctor_set(v___x_831_, 8, v___x_834_);
v___x_836_ = v___x_831_;
goto v_reusejp_835_;
}
else
{
lean_object* v_reuseFailAlloc_842_; 
v_reuseFailAlloc_842_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_842_, 0, v_visitedLevel_818_);
lean_ctor_set(v_reuseFailAlloc_842_, 1, v_visitedExpr_819_);
lean_ctor_set(v_reuseFailAlloc_842_, 2, v_levelParams_820_);
lean_ctor_set(v_reuseFailAlloc_842_, 3, v_nextLevelIdx_821_);
lean_ctor_set(v_reuseFailAlloc_842_, 4, v_levelArgs_822_);
lean_ctor_set(v_reuseFailAlloc_842_, 5, v_newLocalDecls_823_);
lean_ctor_set(v_reuseFailAlloc_842_, 6, v_newLocalDeclsForMVars_824_);
lean_ctor_set(v_reuseFailAlloc_842_, 7, v_newLetDecls_825_);
lean_ctor_set(v_reuseFailAlloc_842_, 8, v___x_834_);
lean_ctor_set(v_reuseFailAlloc_842_, 9, v_exprMVarArgs_827_);
lean_ctor_set(v_reuseFailAlloc_842_, 10, v_exprFVarArgs_828_);
lean_ctor_set(v_reuseFailAlloc_842_, 11, v_toProcess_829_);
v___x_836_ = v_reuseFailAlloc_842_;
goto v_reusejp_835_;
}
v_reusejp_835_:
{
lean_object* v___x_837_; lean_object* v_nextExprIdx_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; 
v___x_837_ = lean_st_ref_put(v_a_814_, v___x_836_);
v_nextExprIdx_838_ = lean_ctor_get(v___x_816_, 8);
lean_inc(v_nextExprIdx_838_);
lean_dec(v___x_816_);
v___x_839_ = ((lean_object*)(l_Lean_Meta_Closure_mkNextUserName___redArg___closed__1));
v___x_840_ = lean_name_append_index_after(v___x_839_, v_nextExprIdx_838_);
v___x_841_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_841_, 0, v___x_840_);
return v___x_841_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkNextUserName___redArg___boxed(lean_object* v_a_844_, lean_object* v_a_845_){
_start:
{
lean_object* v_res_846_; 
v_res_846_ = l_Lean_Meta_Closure_mkNextUserName___redArg(v_a_844_);
lean_dec(v_a_844_);
return v_res_846_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkNextUserName(uint8_t v_a_847_, lean_object* v_a_848_, lean_object* v_a_849_, lean_object* v_a_850_, lean_object* v_a_851_, lean_object* v_a_852_){
_start:
{
lean_object* v___x_854_; 
v___x_854_ = l_Lean_Meta_Closure_mkNextUserName___redArg(v_a_848_);
return v___x_854_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkNextUserName___boxed(lean_object* v_a_855_, lean_object* v_a_856_, lean_object* v_a_857_, lean_object* v_a_858_, lean_object* v_a_859_, lean_object* v_a_860_, lean_object* v_a_861_){
_start:
{
uint8_t v_a_boxed_862_; lean_object* v_res_863_; 
v_a_boxed_862_ = lean_unbox(v_a_855_);
v_res_863_ = l_Lean_Meta_Closure_mkNextUserName(v_a_boxed_862_, v_a_856_, v_a_857_, v_a_858_, v_a_859_, v_a_860_);
lean_dec(v_a_860_);
lean_dec_ref(v_a_859_);
lean_dec(v_a_858_);
lean_dec_ref(v_a_857_);
lean_dec(v_a_856_);
return v_res_863_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushToProcess___redArg(lean_object* v_elem_864_, lean_object* v_a_865_){
_start:
{
lean_object* v___x_867_; lean_object* v_visitedLevel_868_; lean_object* v_visitedExpr_869_; lean_object* v_levelParams_870_; lean_object* v_nextLevelIdx_871_; lean_object* v_levelArgs_872_; lean_object* v_newLocalDecls_873_; lean_object* v_newLocalDeclsForMVars_874_; lean_object* v_newLetDecls_875_; lean_object* v_nextExprIdx_876_; lean_object* v_exprMVarArgs_877_; lean_object* v_exprFVarArgs_878_; lean_object* v_toProcess_879_; lean_object* v___x_881_; uint8_t v_isShared_882_; uint8_t v_isSharedCheck_890_; 
v___x_867_ = lean_st_ref_take(v_a_865_);
v_visitedLevel_868_ = lean_ctor_get(v___x_867_, 0);
v_visitedExpr_869_ = lean_ctor_get(v___x_867_, 1);
v_levelParams_870_ = lean_ctor_get(v___x_867_, 2);
v_nextLevelIdx_871_ = lean_ctor_get(v___x_867_, 3);
v_levelArgs_872_ = lean_ctor_get(v___x_867_, 4);
v_newLocalDecls_873_ = lean_ctor_get(v___x_867_, 5);
v_newLocalDeclsForMVars_874_ = lean_ctor_get(v___x_867_, 6);
v_newLetDecls_875_ = lean_ctor_get(v___x_867_, 7);
v_nextExprIdx_876_ = lean_ctor_get(v___x_867_, 8);
v_exprMVarArgs_877_ = lean_ctor_get(v___x_867_, 9);
v_exprFVarArgs_878_ = lean_ctor_get(v___x_867_, 10);
v_toProcess_879_ = lean_ctor_get(v___x_867_, 11);
v_isSharedCheck_890_ = !lean_is_exclusive(v___x_867_);
if (v_isSharedCheck_890_ == 0)
{
v___x_881_ = v___x_867_;
v_isShared_882_ = v_isSharedCheck_890_;
goto v_resetjp_880_;
}
else
{
lean_inc(v_toProcess_879_);
lean_inc(v_exprFVarArgs_878_);
lean_inc(v_exprMVarArgs_877_);
lean_inc(v_nextExprIdx_876_);
lean_inc(v_newLetDecls_875_);
lean_inc(v_newLocalDeclsForMVars_874_);
lean_inc(v_newLocalDecls_873_);
lean_inc(v_levelArgs_872_);
lean_inc(v_nextLevelIdx_871_);
lean_inc(v_levelParams_870_);
lean_inc(v_visitedExpr_869_);
lean_inc(v_visitedLevel_868_);
lean_dec(v___x_867_);
v___x_881_ = lean_box(0);
v_isShared_882_ = v_isSharedCheck_890_;
goto v_resetjp_880_;
}
v_resetjp_880_:
{
lean_object* v___x_883_; lean_object* v___x_885_; 
v___x_883_ = lean_array_push(v_toProcess_879_, v_elem_864_);
if (v_isShared_882_ == 0)
{
lean_ctor_set(v___x_881_, 11, v___x_883_);
v___x_885_ = v___x_881_;
goto v_reusejp_884_;
}
else
{
lean_object* v_reuseFailAlloc_889_; 
v_reuseFailAlloc_889_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_889_, 0, v_visitedLevel_868_);
lean_ctor_set(v_reuseFailAlloc_889_, 1, v_visitedExpr_869_);
lean_ctor_set(v_reuseFailAlloc_889_, 2, v_levelParams_870_);
lean_ctor_set(v_reuseFailAlloc_889_, 3, v_nextLevelIdx_871_);
lean_ctor_set(v_reuseFailAlloc_889_, 4, v_levelArgs_872_);
lean_ctor_set(v_reuseFailAlloc_889_, 5, v_newLocalDecls_873_);
lean_ctor_set(v_reuseFailAlloc_889_, 6, v_newLocalDeclsForMVars_874_);
lean_ctor_set(v_reuseFailAlloc_889_, 7, v_newLetDecls_875_);
lean_ctor_set(v_reuseFailAlloc_889_, 8, v_nextExprIdx_876_);
lean_ctor_set(v_reuseFailAlloc_889_, 9, v_exprMVarArgs_877_);
lean_ctor_set(v_reuseFailAlloc_889_, 10, v_exprFVarArgs_878_);
lean_ctor_set(v_reuseFailAlloc_889_, 11, v___x_883_);
v___x_885_ = v_reuseFailAlloc_889_;
goto v_reusejp_884_;
}
v_reusejp_884_:
{
lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; 
v___x_886_ = lean_st_ref_put(v_a_865_, v___x_885_);
v___x_887_ = lean_box(0);
v___x_888_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_888_, 0, v___x_887_);
return v___x_888_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushToProcess___redArg___boxed(lean_object* v_elem_891_, lean_object* v_a_892_, lean_object* v_a_893_){
_start:
{
lean_object* v_res_894_; 
v_res_894_ = l_Lean_Meta_Closure_pushToProcess___redArg(v_elem_891_, v_a_892_);
lean_dec(v_a_892_);
return v_res_894_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushToProcess(lean_object* v_elem_895_, uint8_t v_a_896_, lean_object* v_a_897_, lean_object* v_a_898_, lean_object* v_a_899_, lean_object* v_a_900_, lean_object* v_a_901_){
_start:
{
lean_object* v___x_903_; 
v___x_903_ = l_Lean_Meta_Closure_pushToProcess___redArg(v_elem_895_, v_a_897_);
return v___x_903_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushToProcess___boxed(lean_object* v_elem_904_, lean_object* v_a_905_, lean_object* v_a_906_, lean_object* v_a_907_, lean_object* v_a_908_, lean_object* v_a_909_, lean_object* v_a_910_, lean_object* v_a_911_){
_start:
{
uint8_t v_a_boxed_912_; lean_object* v_res_913_; 
v_a_boxed_912_ = lean_unbox(v_a_905_);
v_res_913_ = l_Lean_Meta_Closure_pushToProcess(v_elem_904_, v_a_boxed_912_, v_a_906_, v_a_907_, v_a_908_, v_a_909_, v_a_910_);
lean_dec(v_a_910_);
lean_dec_ref(v_a_909_);
lean_dec(v_a_908_);
lean_dec_ref(v_a_907_);
lean_dec(v_a_906_);
return v_res_913_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__4___redArg(lean_object* v_mvarId_914_, lean_object* v___y_915_){
_start:
{
lean_object* v___x_917_; lean_object* v_mctx_918_; lean_object* v___x_919_; lean_object* v___x_920_; 
v___x_917_ = lean_st_ref_get(v___y_915_);
v_mctx_918_ = lean_ctor_get(v___x_917_, 0);
lean_inc_ref(v_mctx_918_);
lean_dec(v___x_917_);
v___x_919_ = l_Lean_MetavarContext_getDelayedMVarAssignmentCore_x3f(v_mctx_918_, v_mvarId_914_);
lean_dec_ref(v_mctx_918_);
v___x_920_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_920_, 0, v___x_919_);
return v___x_920_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__4___redArg___boxed(lean_object* v_mvarId_921_, lean_object* v___y_922_, lean_object* v___y_923_){
_start:
{
lean_object* v_res_924_; 
v_res_924_ = l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__4___redArg(v_mvarId_921_, v___y_922_);
lean_dec(v___y_922_);
lean_dec(v_mvarId_921_);
return v_res_924_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__4(lean_object* v_mvarId_925_, uint8_t v___y_926_, lean_object* v___y_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_){
_start:
{
lean_object* v___x_933_; 
v___x_933_ = l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__4___redArg(v_mvarId_925_, v___y_929_);
return v___x_933_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__4___boxed(lean_object* v_mvarId_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_){
_start:
{
uint8_t v___y_18028__boxed_942_; lean_object* v_res_943_; 
v___y_18028__boxed_942_ = lean_unbox(v___y_935_);
v_res_943_ = l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__4(v_mvarId_934_, v___y_18028__boxed_942_, v___y_936_, v___y_937_, v___y_938_, v___y_939_, v___y_940_);
lean_dec(v___y_940_);
lean_dec_ref(v___y_939_);
lean_dec(v___y_938_);
lean_dec_ref(v___y_937_);
lean_dec(v___y_936_);
lean_dec(v_mvarId_934_);
return v_res_943_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Closure_collectExprAux_spec__5___redArg___lam__0(lean_object* v_k_944_, uint8_t v___y_945_, lean_object* v___y_946_, lean_object* v_b_947_, lean_object* v_c_948_, lean_object* v___y_949_, lean_object* v___y_950_, lean_object* v___y_951_, lean_object* v___y_952_){
_start:
{
lean_object* v___x_954_; lean_object* v___x_955_; 
v___x_954_ = lean_box(v___y_945_);
lean_inc(v___y_952_);
lean_inc_ref(v___y_951_);
lean_inc(v___y_950_);
lean_inc_ref(v___y_949_);
lean_inc(v___y_946_);
v___x_955_ = lean_apply_9(v_k_944_, v_b_947_, v_c_948_, v___x_954_, v___y_946_, v___y_949_, v___y_950_, v___y_951_, v___y_952_, lean_box(0));
return v___x_955_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Closure_collectExprAux_spec__5___redArg___lam__0___boxed(lean_object* v_k_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v_b_959_, lean_object* v_c_960_, lean_object* v___y_961_, lean_object* v___y_962_, lean_object* v___y_963_, lean_object* v___y_964_, lean_object* v___y_965_){
_start:
{
uint8_t v___y_18051__boxed_966_; lean_object* v_res_967_; 
v___y_18051__boxed_966_ = lean_unbox(v___y_957_);
v_res_967_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Closure_collectExprAux_spec__5___redArg___lam__0(v_k_956_, v___y_18051__boxed_966_, v___y_958_, v_b_959_, v_c_960_, v___y_961_, v___y_962_, v___y_963_, v___y_964_);
lean_dec(v___y_964_);
lean_dec_ref(v___y_963_);
lean_dec(v___y_962_);
lean_dec_ref(v___y_961_);
lean_dec(v___y_958_);
return v_res_967_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Closure_collectExprAux_spec__5___redArg(lean_object* v_type_968_, lean_object* v_maxFVars_x3f_969_, lean_object* v_k_970_, uint8_t v_cleanupAnnotations_971_, uint8_t v_whnfType_972_, uint8_t v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_, lean_object* v___y_976_, lean_object* v___y_977_, lean_object* v___y_978_){
_start:
{
lean_object* v___x_980_; lean_object* v___f_981_; lean_object* v___x_982_; 
v___x_980_ = lean_box(v___y_973_);
lean_inc(v___y_974_);
v___f_981_ = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Closure_collectExprAux_spec__5___redArg___lam__0___boxed), 10, 3);
lean_closure_set(v___f_981_, 0, v_k_970_);
lean_closure_set(v___f_981_, 1, v___x_980_);
lean_closure_set(v___f_981_, 2, v___y_974_);
v___x_982_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_968_, v_maxFVars_x3f_969_, v___f_981_, v_cleanupAnnotations_971_, v_whnfType_972_, v___y_975_, v___y_976_, v___y_977_, v___y_978_);
if (lean_obj_tag(v___x_982_) == 0)
{
return v___x_982_;
}
else
{
lean_object* v_a_983_; lean_object* v___x_985_; uint8_t v_isShared_986_; uint8_t v_isSharedCheck_990_; 
v_a_983_ = lean_ctor_get(v___x_982_, 0);
v_isSharedCheck_990_ = !lean_is_exclusive(v___x_982_);
if (v_isSharedCheck_990_ == 0)
{
v___x_985_ = v___x_982_;
v_isShared_986_ = v_isSharedCheck_990_;
goto v_resetjp_984_;
}
else
{
lean_inc(v_a_983_);
lean_dec(v___x_982_);
v___x_985_ = lean_box(0);
v_isShared_986_ = v_isSharedCheck_990_;
goto v_resetjp_984_;
}
v_resetjp_984_:
{
lean_object* v___x_988_; 
if (v_isShared_986_ == 0)
{
v___x_988_ = v___x_985_;
goto v_reusejp_987_;
}
else
{
lean_object* v_reuseFailAlloc_989_; 
v_reuseFailAlloc_989_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_989_, 0, v_a_983_);
v___x_988_ = v_reuseFailAlloc_989_;
goto v_reusejp_987_;
}
v_reusejp_987_:
{
return v___x_988_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Closure_collectExprAux_spec__5___redArg___boxed(lean_object* v_type_991_, lean_object* v_maxFVars_x3f_992_, lean_object* v_k_993_, lean_object* v_cleanupAnnotations_994_, lean_object* v_whnfType_995_, lean_object* v___y_996_, lean_object* v___y_997_, lean_object* v___y_998_, lean_object* v___y_999_, lean_object* v___y_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1003_; uint8_t v_whnfType_boxed_1004_; uint8_t v___y_18076__boxed_1005_; lean_object* v_res_1006_; 
v_cleanupAnnotations_boxed_1003_ = lean_unbox(v_cleanupAnnotations_994_);
v_whnfType_boxed_1004_ = lean_unbox(v_whnfType_995_);
v___y_18076__boxed_1005_ = lean_unbox(v___y_996_);
v_res_1006_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Closure_collectExprAux_spec__5___redArg(v_type_991_, v_maxFVars_x3f_992_, v_k_993_, v_cleanupAnnotations_boxed_1003_, v_whnfType_boxed_1004_, v___y_18076__boxed_1005_, v___y_997_, v___y_998_, v___y_999_, v___y_1000_, v___y_1001_);
lean_dec(v___y_1001_);
lean_dec_ref(v___y_1000_);
lean_dec(v___y_999_);
lean_dec_ref(v___y_998_);
lean_dec(v___y_997_);
return v_res_1006_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Closure_collectExprAux_spec__5(lean_object* v_00_u03b1_1007_, lean_object* v_type_1008_, lean_object* v_maxFVars_x3f_1009_, lean_object* v_k_1010_, uint8_t v_cleanupAnnotations_1011_, uint8_t v_whnfType_1012_, uint8_t v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_){
_start:
{
lean_object* v___x_1020_; 
v___x_1020_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Closure_collectExprAux_spec__5___redArg(v_type_1008_, v_maxFVars_x3f_1009_, v_k_1010_, v_cleanupAnnotations_1011_, v_whnfType_1012_, v___y_1013_, v___y_1014_, v___y_1015_, v___y_1016_, v___y_1017_, v___y_1018_);
return v___x_1020_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Closure_collectExprAux_spec__5___boxed(lean_object* v_00_u03b1_1021_, lean_object* v_type_1022_, lean_object* v_maxFVars_x3f_1023_, lean_object* v_k_1024_, lean_object* v_cleanupAnnotations_1025_, lean_object* v_whnfType_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1034_; uint8_t v_whnfType_boxed_1035_; uint8_t v___y_18120__boxed_1036_; lean_object* v_res_1037_; 
v_cleanupAnnotations_boxed_1034_ = lean_unbox(v_cleanupAnnotations_1025_);
v_whnfType_boxed_1035_ = lean_unbox(v_whnfType_1026_);
v___y_18120__boxed_1036_ = lean_unbox(v___y_1027_);
v_res_1037_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Closure_collectExprAux_spec__5(v_00_u03b1_1021_, v_type_1022_, v_maxFVars_x3f_1023_, v_k_1024_, v_cleanupAnnotations_boxed_1034_, v_whnfType_boxed_1035_, v___y_18120__boxed_1036_, v___y_1028_, v___y_1029_, v___y_1030_, v___y_1031_, v___y_1032_);
lean_dec(v___y_1032_);
lean_dec_ref(v___y_1031_);
lean_dec(v___y_1030_);
lean_dec_ref(v___y_1029_);
lean_dec(v___y_1028_);
return v_res_1037_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0_spec__0___redArg(lean_object* v_a_1038_, lean_object* v_x_1039_){
_start:
{
if (lean_obj_tag(v_x_1039_) == 0)
{
lean_object* v___x_1040_; 
v___x_1040_ = lean_box(0);
return v___x_1040_;
}
else
{
lean_object* v_key_1041_; lean_object* v_value_1042_; lean_object* v_tail_1043_; uint8_t v___x_1044_; 
v_key_1041_ = lean_ctor_get(v_x_1039_, 0);
v_value_1042_ = lean_ctor_get(v_x_1039_, 1);
v_tail_1043_ = lean_ctor_get(v_x_1039_, 2);
v___x_1044_ = l_Lean_ExprStructEq_beq(v_key_1041_, v_a_1038_);
if (v___x_1044_ == 0)
{
v_x_1039_ = v_tail_1043_;
goto _start;
}
else
{
lean_object* v___x_1046_; 
lean_inc(v_value_1042_);
v___x_1046_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1046_, 0, v_value_1042_);
return v___x_1046_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0_spec__0___redArg___boxed(lean_object* v_a_1047_, lean_object* v_x_1048_){
_start:
{
lean_object* v_res_1049_; 
v_res_1049_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0_spec__0___redArg(v_a_1047_, v_x_1048_);
lean_dec(v_x_1048_);
lean_dec_ref(v_a_1047_);
return v_res_1049_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0___redArg(lean_object* v_m_1050_, lean_object* v_a_1051_){
_start:
{
lean_object* v_buckets_1052_; lean_object* v___x_1053_; uint64_t v___x_1054_; uint64_t v___x_1055_; uint64_t v___x_1056_; uint64_t v_fold_1057_; uint64_t v___x_1058_; uint64_t v___x_1059_; uint64_t v___x_1060_; size_t v___x_1061_; size_t v___x_1062_; size_t v___x_1063_; size_t v___x_1064_; size_t v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; 
v_buckets_1052_ = lean_ctor_get(v_m_1050_, 1);
v___x_1053_ = lean_array_get_size(v_buckets_1052_);
v___x_1054_ = l_Lean_ExprStructEq_hash(v_a_1051_);
v___x_1055_ = 32ULL;
v___x_1056_ = lean_uint64_shift_right(v___x_1054_, v___x_1055_);
v_fold_1057_ = lean_uint64_xor(v___x_1054_, v___x_1056_);
v___x_1058_ = 16ULL;
v___x_1059_ = lean_uint64_shift_right(v_fold_1057_, v___x_1058_);
v___x_1060_ = lean_uint64_xor(v_fold_1057_, v___x_1059_);
v___x_1061_ = lean_uint64_to_usize(v___x_1060_);
v___x_1062_ = lean_usize_of_nat(v___x_1053_);
v___x_1063_ = ((size_t)1ULL);
v___x_1064_ = lean_usize_sub(v___x_1062_, v___x_1063_);
v___x_1065_ = lean_usize_land(v___x_1061_, v___x_1064_);
v___x_1066_ = lean_array_uget_borrowed(v_buckets_1052_, v___x_1065_);
v___x_1067_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0_spec__0___redArg(v_a_1051_, v___x_1066_);
return v___x_1067_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0___redArg___boxed(lean_object* v_m_1068_, lean_object* v_a_1069_){
_start:
{
lean_object* v_res_1070_; 
v_res_1070_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0___redArg(v_m_1068_, v_a_1069_);
lean_dec_ref(v_a_1069_);
lean_dec_ref(v_m_1068_);
return v_res_1070_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Closure_collectExprAux_spec__2___redArg(lean_object* v_x_1071_, lean_object* v_x_1072_, lean_object* v___y_1073_){
_start:
{
if (lean_obj_tag(v_x_1071_) == 0)
{
lean_object* v___x_1075_; lean_object* v___x_1076_; 
v___x_1075_ = l_List_reverse___redArg(v_x_1072_);
v___x_1076_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1076_, 0, v___x_1075_);
return v___x_1076_;
}
else
{
lean_object* v_head_1077_; lean_object* v_tail_1078_; lean_object* v___x_1080_; uint8_t v_isShared_1081_; uint8_t v_isSharedCheck_1096_; 
v_head_1077_ = lean_ctor_get(v_x_1071_, 0);
v_tail_1078_ = lean_ctor_get(v_x_1071_, 1);
v_isSharedCheck_1096_ = !lean_is_exclusive(v_x_1071_);
if (v_isSharedCheck_1096_ == 0)
{
v___x_1080_ = v_x_1071_;
v_isShared_1081_ = v_isSharedCheck_1096_;
goto v_resetjp_1079_;
}
else
{
lean_inc(v_tail_1078_);
lean_inc(v_head_1077_);
lean_dec(v_x_1071_);
v___x_1080_ = lean_box(0);
v_isShared_1081_ = v_isSharedCheck_1096_;
goto v_resetjp_1079_;
}
v_resetjp_1079_:
{
lean_object* v___x_1082_; 
v___x_1082_ = l_Lean_Meta_Closure_collectLevel___redArg(v_head_1077_, v___y_1073_);
if (lean_obj_tag(v___x_1082_) == 0)
{
lean_object* v_a_1083_; lean_object* v___x_1085_; 
v_a_1083_ = lean_ctor_get(v___x_1082_, 0);
lean_inc(v_a_1083_);
lean_dec_ref_known(v___x_1082_, 1);
if (v_isShared_1081_ == 0)
{
lean_ctor_set(v___x_1080_, 1, v_x_1072_);
lean_ctor_set(v___x_1080_, 0, v_a_1083_);
v___x_1085_ = v___x_1080_;
goto v_reusejp_1084_;
}
else
{
lean_object* v_reuseFailAlloc_1087_; 
v_reuseFailAlloc_1087_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1087_, 0, v_a_1083_);
lean_ctor_set(v_reuseFailAlloc_1087_, 1, v_x_1072_);
v___x_1085_ = v_reuseFailAlloc_1087_;
goto v_reusejp_1084_;
}
v_reusejp_1084_:
{
v_x_1071_ = v_tail_1078_;
v_x_1072_ = v___x_1085_;
goto _start;
}
}
else
{
lean_object* v_a_1088_; lean_object* v___x_1090_; uint8_t v_isShared_1091_; uint8_t v_isSharedCheck_1095_; 
lean_del_object(v___x_1080_);
lean_dec(v_tail_1078_);
lean_dec(v_x_1072_);
v_a_1088_ = lean_ctor_get(v___x_1082_, 0);
v_isSharedCheck_1095_ = !lean_is_exclusive(v___x_1082_);
if (v_isSharedCheck_1095_ == 0)
{
v___x_1090_ = v___x_1082_;
v_isShared_1091_ = v_isSharedCheck_1095_;
goto v_resetjp_1089_;
}
else
{
lean_inc(v_a_1088_);
lean_dec(v___x_1082_);
v___x_1090_ = lean_box(0);
v_isShared_1091_ = v_isSharedCheck_1095_;
goto v_resetjp_1089_;
}
v_resetjp_1089_:
{
lean_object* v___x_1093_; 
if (v_isShared_1091_ == 0)
{
v___x_1093_ = v___x_1090_;
goto v_reusejp_1092_;
}
else
{
lean_object* v_reuseFailAlloc_1094_; 
v_reuseFailAlloc_1094_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1094_, 0, v_a_1088_);
v___x_1093_ = v_reuseFailAlloc_1094_;
goto v_reusejp_1092_;
}
v_reusejp_1092_:
{
return v___x_1093_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Closure_collectExprAux_spec__2___redArg___boxed(lean_object* v_x_1097_, lean_object* v_x_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_){
_start:
{
lean_object* v_res_1101_; 
v_res_1101_ = l_List_mapM_loop___at___00Lean_Meta_Closure_collectExprAux_spec__2___redArg(v_x_1097_, v_x_1098_, v___y_1099_);
lean_dec(v___y_1099_);
return v_res_1101_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Closure_collectExprAux_spec__3_spec__7___redArg(lean_object* v___y_1102_){
_start:
{
lean_object* v___x_1104_; lean_object* v_ngen_1105_; lean_object* v_namePrefix_1106_; lean_object* v_idx_1107_; lean_object* v___x_1109_; uint8_t v_isShared_1110_; uint8_t v_isSharedCheck_1136_; 
v___x_1104_ = lean_st_ref_get(v___y_1102_);
v_ngen_1105_ = lean_ctor_get(v___x_1104_, 2);
lean_inc_ref(v_ngen_1105_);
lean_dec(v___x_1104_);
v_namePrefix_1106_ = lean_ctor_get(v_ngen_1105_, 0);
v_idx_1107_ = lean_ctor_get(v_ngen_1105_, 1);
v_isSharedCheck_1136_ = !lean_is_exclusive(v_ngen_1105_);
if (v_isSharedCheck_1136_ == 0)
{
v___x_1109_ = v_ngen_1105_;
v_isShared_1110_ = v_isSharedCheck_1136_;
goto v_resetjp_1108_;
}
else
{
lean_inc(v_idx_1107_);
lean_inc(v_namePrefix_1106_);
lean_dec(v_ngen_1105_);
v___x_1109_ = lean_box(0);
v_isShared_1110_ = v_isSharedCheck_1136_;
goto v_resetjp_1108_;
}
v_resetjp_1108_:
{
lean_object* v___x_1111_; lean_object* v_env_1112_; lean_object* v_nextMacroScope_1113_; lean_object* v_auxDeclNGen_1114_; lean_object* v_traceState_1115_; lean_object* v_cache_1116_; lean_object* v_messages_1117_; lean_object* v_infoState_1118_; lean_object* v_snapshotTasks_1119_; lean_object* v___x_1121_; uint8_t v_isShared_1122_; uint8_t v_isSharedCheck_1134_; 
v___x_1111_ = lean_st_ref_take(v___y_1102_);
v_env_1112_ = lean_ctor_get(v___x_1111_, 0);
v_nextMacroScope_1113_ = lean_ctor_get(v___x_1111_, 1);
v_auxDeclNGen_1114_ = lean_ctor_get(v___x_1111_, 3);
v_traceState_1115_ = lean_ctor_get(v___x_1111_, 4);
v_cache_1116_ = lean_ctor_get(v___x_1111_, 5);
v_messages_1117_ = lean_ctor_get(v___x_1111_, 6);
v_infoState_1118_ = lean_ctor_get(v___x_1111_, 7);
v_snapshotTasks_1119_ = lean_ctor_get(v___x_1111_, 8);
v_isSharedCheck_1134_ = !lean_is_exclusive(v___x_1111_);
if (v_isSharedCheck_1134_ == 0)
{
lean_object* v_unused_1135_; 
v_unused_1135_ = lean_ctor_get(v___x_1111_, 2);
lean_dec(v_unused_1135_);
v___x_1121_ = v___x_1111_;
v_isShared_1122_ = v_isSharedCheck_1134_;
goto v_resetjp_1120_;
}
else
{
lean_inc(v_snapshotTasks_1119_);
lean_inc(v_infoState_1118_);
lean_inc(v_messages_1117_);
lean_inc(v_cache_1116_);
lean_inc(v_traceState_1115_);
lean_inc(v_auxDeclNGen_1114_);
lean_inc(v_nextMacroScope_1113_);
lean_inc(v_env_1112_);
lean_dec(v___x_1111_);
v___x_1121_ = lean_box(0);
v_isShared_1122_ = v_isSharedCheck_1134_;
goto v_resetjp_1120_;
}
v_resetjp_1120_:
{
lean_object* v_r_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1127_; 
lean_inc(v_idx_1107_);
lean_inc(v_namePrefix_1106_);
v_r_1123_ = l_Lean_Name_num___override(v_namePrefix_1106_, v_idx_1107_);
v___x_1124_ = lean_unsigned_to_nat(1u);
v___x_1125_ = lean_nat_add(v_idx_1107_, v___x_1124_);
lean_dec(v_idx_1107_);
if (v_isShared_1110_ == 0)
{
lean_ctor_set(v___x_1109_, 1, v___x_1125_);
v___x_1127_ = v___x_1109_;
goto v_reusejp_1126_;
}
else
{
lean_object* v_reuseFailAlloc_1133_; 
v_reuseFailAlloc_1133_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1133_, 0, v_namePrefix_1106_);
lean_ctor_set(v_reuseFailAlloc_1133_, 1, v___x_1125_);
v___x_1127_ = v_reuseFailAlloc_1133_;
goto v_reusejp_1126_;
}
v_reusejp_1126_:
{
lean_object* v___x_1129_; 
if (v_isShared_1122_ == 0)
{
lean_ctor_set(v___x_1121_, 2, v___x_1127_);
v___x_1129_ = v___x_1121_;
goto v_reusejp_1128_;
}
else
{
lean_object* v_reuseFailAlloc_1132_; 
v_reuseFailAlloc_1132_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1132_, 0, v_env_1112_);
lean_ctor_set(v_reuseFailAlloc_1132_, 1, v_nextMacroScope_1113_);
lean_ctor_set(v_reuseFailAlloc_1132_, 2, v___x_1127_);
lean_ctor_set(v_reuseFailAlloc_1132_, 3, v_auxDeclNGen_1114_);
lean_ctor_set(v_reuseFailAlloc_1132_, 4, v_traceState_1115_);
lean_ctor_set(v_reuseFailAlloc_1132_, 5, v_cache_1116_);
lean_ctor_set(v_reuseFailAlloc_1132_, 6, v_messages_1117_);
lean_ctor_set(v_reuseFailAlloc_1132_, 7, v_infoState_1118_);
lean_ctor_set(v_reuseFailAlloc_1132_, 8, v_snapshotTasks_1119_);
v___x_1129_ = v_reuseFailAlloc_1132_;
goto v_reusejp_1128_;
}
v_reusejp_1128_:
{
lean_object* v___x_1130_; lean_object* v___x_1131_; 
v___x_1130_ = lean_st_ref_put(v___y_1102_, v___x_1129_);
v___x_1131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1131_, 0, v_r_1123_);
return v___x_1131_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Closure_collectExprAux_spec__3_spec__7___redArg___boxed(lean_object* v___y_1137_, lean_object* v___y_1138_){
_start:
{
lean_object* v_res_1139_; 
v_res_1139_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Closure_collectExprAux_spec__3_spec__7___redArg(v___y_1137_);
lean_dec(v___y_1137_);
return v_res_1139_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00Lean_Meta_Closure_collectExprAux_spec__3(uint8_t v___y_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_){
_start:
{
lean_object* v___x_1147_; lean_object* v_a_1148_; lean_object* v___x_1150_; uint8_t v_isShared_1151_; uint8_t v_isSharedCheck_1155_; 
v___x_1147_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Closure_collectExprAux_spec__3_spec__7___redArg(v___y_1145_);
v_a_1148_ = lean_ctor_get(v___x_1147_, 0);
v_isSharedCheck_1155_ = !lean_is_exclusive(v___x_1147_);
if (v_isSharedCheck_1155_ == 0)
{
v___x_1150_ = v___x_1147_;
v_isShared_1151_ = v_isSharedCheck_1155_;
goto v_resetjp_1149_;
}
else
{
lean_inc(v_a_1148_);
lean_dec(v___x_1147_);
v___x_1150_ = lean_box(0);
v_isShared_1151_ = v_isSharedCheck_1155_;
goto v_resetjp_1149_;
}
v_resetjp_1149_:
{
lean_object* v___x_1153_; 
if (v_isShared_1151_ == 0)
{
v___x_1153_ = v___x_1150_;
goto v_reusejp_1152_;
}
else
{
lean_object* v_reuseFailAlloc_1154_; 
v_reuseFailAlloc_1154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1154_, 0, v_a_1148_);
v___x_1153_ = v_reuseFailAlloc_1154_;
goto v_reusejp_1152_;
}
v_reusejp_1152_:
{
return v___x_1153_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00Lean_Meta_Closure_collectExprAux_spec__3___boxed(lean_object* v___y_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_){
_start:
{
uint8_t v___y_18295__boxed_1163_; lean_object* v_res_1164_; 
v___y_18295__boxed_1163_ = lean_unbox(v___y_1156_);
v_res_1164_ = l_Lean_mkFreshFVarId___at___00Lean_Meta_Closure_collectExprAux_spec__3(v___y_18295__boxed_1163_, v___y_1157_, v___y_1158_, v___y_1159_, v___y_1160_, v___y_1161_);
lean_dec(v___y_1161_);
lean_dec_ref(v___y_1160_);
lean_dec(v___y_1159_);
lean_dec_ref(v___y_1158_);
lean_dec(v___y_1157_);
return v_res_1164_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectExprAux___lam__1(lean_object* v_e_1165_, lean_object* v_args_1166_, lean_object* v_x_1167_, uint8_t v___y_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_){
_start:
{
lean_object* v___x_1175_; uint8_t v___x_1176_; uint8_t v___x_1177_; uint8_t v___x_1178_; lean_object* v___x_1179_; 
v___x_1175_ = l_Lean_mkAppN(v_e_1165_, v_args_1166_);
v___x_1176_ = 0;
v___x_1177_ = 1;
v___x_1178_ = 1;
v___x_1179_ = l_Lean_Meta_mkLambdaFVars(v_args_1166_, v___x_1175_, v___x_1176_, v___x_1177_, v___x_1176_, v___x_1177_, v___x_1178_, v___y_1170_, v___y_1171_, v___y_1172_, v___y_1173_);
return v___x_1179_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectExprAux___lam__1___boxed(lean_object* v_e_1180_, lean_object* v_args_1181_, lean_object* v_x_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_){
_start:
{
uint8_t v___y_18336__boxed_1190_; lean_object* v_res_1191_; 
v___y_18336__boxed_1190_ = lean_unbox(v___y_1183_);
v_res_1191_ = l_Lean_Meta_Closure_collectExprAux___lam__1(v_e_1180_, v_args_1181_, v_x_1182_, v___y_18336__boxed_1190_, v___y_1184_, v___y_1185_, v___y_1186_, v___y_1187_, v___y_1188_);
lean_dec(v___y_1188_);
lean_dec_ref(v___y_1187_);
lean_dec(v___y_1186_);
lean_dec_ref(v___y_1185_);
lean_dec(v___y_1184_);
lean_dec_ref(v_x_1182_);
lean_dec_ref(v_args_1181_);
return v_res_1191_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__3_spec__6_spec__10___redArg(lean_object* v_x_1192_, lean_object* v_x_1193_){
_start:
{
if (lean_obj_tag(v_x_1193_) == 0)
{
return v_x_1192_;
}
else
{
lean_object* v_key_1194_; lean_object* v_value_1195_; lean_object* v_tail_1196_; lean_object* v___x_1198_; uint8_t v_isShared_1199_; uint8_t v_isSharedCheck_1219_; 
v_key_1194_ = lean_ctor_get(v_x_1193_, 0);
v_value_1195_ = lean_ctor_get(v_x_1193_, 1);
v_tail_1196_ = lean_ctor_get(v_x_1193_, 2);
v_isSharedCheck_1219_ = !lean_is_exclusive(v_x_1193_);
if (v_isSharedCheck_1219_ == 0)
{
v___x_1198_ = v_x_1193_;
v_isShared_1199_ = v_isSharedCheck_1219_;
goto v_resetjp_1197_;
}
else
{
lean_inc(v_tail_1196_);
lean_inc(v_value_1195_);
lean_inc(v_key_1194_);
lean_dec(v_x_1193_);
v___x_1198_ = lean_box(0);
v_isShared_1199_ = v_isSharedCheck_1219_;
goto v_resetjp_1197_;
}
v_resetjp_1197_:
{
lean_object* v___x_1200_; uint64_t v___x_1201_; uint64_t v___x_1202_; uint64_t v___x_1203_; uint64_t v_fold_1204_; uint64_t v___x_1205_; uint64_t v___x_1206_; uint64_t v___x_1207_; size_t v___x_1208_; size_t v___x_1209_; size_t v___x_1210_; size_t v___x_1211_; size_t v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1215_; 
v___x_1200_ = lean_array_get_size(v_x_1192_);
v___x_1201_ = l_Lean_ExprStructEq_hash(v_key_1194_);
v___x_1202_ = 32ULL;
v___x_1203_ = lean_uint64_shift_right(v___x_1201_, v___x_1202_);
v_fold_1204_ = lean_uint64_xor(v___x_1201_, v___x_1203_);
v___x_1205_ = 16ULL;
v___x_1206_ = lean_uint64_shift_right(v_fold_1204_, v___x_1205_);
v___x_1207_ = lean_uint64_xor(v_fold_1204_, v___x_1206_);
v___x_1208_ = lean_uint64_to_usize(v___x_1207_);
v___x_1209_ = lean_usize_of_nat(v___x_1200_);
v___x_1210_ = ((size_t)1ULL);
v___x_1211_ = lean_usize_sub(v___x_1209_, v___x_1210_);
v___x_1212_ = lean_usize_land(v___x_1208_, v___x_1211_);
v___x_1213_ = lean_array_uget_borrowed(v_x_1192_, v___x_1212_);
lean_inc(v___x_1213_);
if (v_isShared_1199_ == 0)
{
lean_ctor_set(v___x_1198_, 2, v___x_1213_);
v___x_1215_ = v___x_1198_;
goto v_reusejp_1214_;
}
else
{
lean_object* v_reuseFailAlloc_1218_; 
v_reuseFailAlloc_1218_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1218_, 0, v_key_1194_);
lean_ctor_set(v_reuseFailAlloc_1218_, 1, v_value_1195_);
lean_ctor_set(v_reuseFailAlloc_1218_, 2, v___x_1213_);
v___x_1215_ = v_reuseFailAlloc_1218_;
goto v_reusejp_1214_;
}
v_reusejp_1214_:
{
lean_object* v___x_1216_; 
v___x_1216_ = lean_array_uset(v_x_1192_, v___x_1212_, v___x_1215_);
v_x_1192_ = v___x_1216_;
v_x_1193_ = v_tail_1196_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__3_spec__6___redArg(lean_object* v_i_1220_, lean_object* v_source_1221_, lean_object* v_target_1222_){
_start:
{
lean_object* v___x_1223_; uint8_t v___x_1224_; 
v___x_1223_ = lean_array_get_size(v_source_1221_);
v___x_1224_ = lean_nat_dec_lt(v_i_1220_, v___x_1223_);
if (v___x_1224_ == 0)
{
lean_dec_ref(v_source_1221_);
lean_dec(v_i_1220_);
return v_target_1222_;
}
else
{
lean_object* v_es_1225_; lean_object* v___x_1226_; lean_object* v_source_1227_; lean_object* v_target_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; 
v_es_1225_ = lean_array_fget(v_source_1221_, v_i_1220_);
v___x_1226_ = lean_box(0);
v_source_1227_ = lean_array_fset(v_source_1221_, v_i_1220_, v___x_1226_);
v_target_1228_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__3_spec__6_spec__10___redArg(v_target_1222_, v_es_1225_);
v___x_1229_ = lean_unsigned_to_nat(1u);
v___x_1230_ = lean_nat_add(v_i_1220_, v___x_1229_);
lean_dec(v_i_1220_);
v_i_1220_ = v___x_1230_;
v_source_1221_ = v_source_1227_;
v_target_1222_ = v_target_1228_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__3___redArg(lean_object* v_data_1232_){
_start:
{
lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v_nbuckets_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; 
v___x_1233_ = lean_array_get_size(v_data_1232_);
v___x_1234_ = lean_unsigned_to_nat(2u);
v_nbuckets_1235_ = lean_nat_mul(v___x_1233_, v___x_1234_);
v___x_1236_ = lean_unsigned_to_nat(0u);
v___x_1237_ = lean_box(0);
v___x_1238_ = lean_mk_array(v_nbuckets_1235_, v___x_1237_);
v___x_1239_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__3_spec__6___redArg(v___x_1236_, v_data_1232_, v___x_1238_);
return v___x_1239_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__4___redArg(lean_object* v_a_1240_, lean_object* v_b_1241_, lean_object* v_x_1242_){
_start:
{
if (lean_obj_tag(v_x_1242_) == 0)
{
lean_dec(v_b_1241_);
lean_dec_ref(v_a_1240_);
return v_x_1242_;
}
else
{
lean_object* v_key_1243_; lean_object* v_value_1244_; lean_object* v_tail_1245_; lean_object* v___x_1247_; uint8_t v_isShared_1248_; uint8_t v_isSharedCheck_1257_; 
v_key_1243_ = lean_ctor_get(v_x_1242_, 0);
v_value_1244_ = lean_ctor_get(v_x_1242_, 1);
v_tail_1245_ = lean_ctor_get(v_x_1242_, 2);
v_isSharedCheck_1257_ = !lean_is_exclusive(v_x_1242_);
if (v_isSharedCheck_1257_ == 0)
{
v___x_1247_ = v_x_1242_;
v_isShared_1248_ = v_isSharedCheck_1257_;
goto v_resetjp_1246_;
}
else
{
lean_inc(v_tail_1245_);
lean_inc(v_value_1244_);
lean_inc(v_key_1243_);
lean_dec(v_x_1242_);
v___x_1247_ = lean_box(0);
v_isShared_1248_ = v_isSharedCheck_1257_;
goto v_resetjp_1246_;
}
v_resetjp_1246_:
{
uint8_t v___x_1249_; 
v___x_1249_ = l_Lean_ExprStructEq_beq(v_key_1243_, v_a_1240_);
if (v___x_1249_ == 0)
{
lean_object* v___x_1250_; lean_object* v___x_1252_; 
v___x_1250_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__4___redArg(v_a_1240_, v_b_1241_, v_tail_1245_);
if (v_isShared_1248_ == 0)
{
lean_ctor_set(v___x_1247_, 2, v___x_1250_);
v___x_1252_ = v___x_1247_;
goto v_reusejp_1251_;
}
else
{
lean_object* v_reuseFailAlloc_1253_; 
v_reuseFailAlloc_1253_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1253_, 0, v_key_1243_);
lean_ctor_set(v_reuseFailAlloc_1253_, 1, v_value_1244_);
lean_ctor_set(v_reuseFailAlloc_1253_, 2, v___x_1250_);
v___x_1252_ = v_reuseFailAlloc_1253_;
goto v_reusejp_1251_;
}
v_reusejp_1251_:
{
return v___x_1252_;
}
}
else
{
lean_object* v___x_1255_; 
lean_dec(v_value_1244_);
lean_dec(v_key_1243_);
if (v_isShared_1248_ == 0)
{
lean_ctor_set(v___x_1247_, 1, v_b_1241_);
lean_ctor_set(v___x_1247_, 0, v_a_1240_);
v___x_1255_ = v___x_1247_;
goto v_reusejp_1254_;
}
else
{
lean_object* v_reuseFailAlloc_1256_; 
v_reuseFailAlloc_1256_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1256_, 0, v_a_1240_);
lean_ctor_set(v_reuseFailAlloc_1256_, 1, v_b_1241_);
lean_ctor_set(v_reuseFailAlloc_1256_, 2, v_tail_1245_);
v___x_1255_ = v_reuseFailAlloc_1256_;
goto v_reusejp_1254_;
}
v_reusejp_1254_:
{
return v___x_1255_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__2___redArg(lean_object* v_a_1258_, lean_object* v_x_1259_){
_start:
{
if (lean_obj_tag(v_x_1259_) == 0)
{
uint8_t v___x_1260_; 
v___x_1260_ = 0;
return v___x_1260_;
}
else
{
lean_object* v_key_1261_; lean_object* v_tail_1262_; uint8_t v___x_1263_; 
v_key_1261_ = lean_ctor_get(v_x_1259_, 0);
v_tail_1262_ = lean_ctor_get(v_x_1259_, 2);
v___x_1263_ = l_Lean_ExprStructEq_beq(v_key_1261_, v_a_1258_);
if (v___x_1263_ == 0)
{
v_x_1259_ = v_tail_1262_;
goto _start;
}
else
{
return v___x_1263_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__2___redArg___boxed(lean_object* v_a_1265_, lean_object* v_x_1266_){
_start:
{
uint8_t v_res_1267_; lean_object* v_r_1268_; 
v_res_1267_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__2___redArg(v_a_1265_, v_x_1266_);
lean_dec(v_x_1266_);
lean_dec_ref(v_a_1265_);
v_r_1268_ = lean_box(v_res_1267_);
return v_r_1268_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1___redArg(lean_object* v_m_1269_, lean_object* v_a_1270_, lean_object* v_b_1271_){
_start:
{
lean_object* v_size_1272_; lean_object* v_buckets_1273_; lean_object* v___x_1275_; uint8_t v_isShared_1276_; uint8_t v_isSharedCheck_1316_; 
v_size_1272_ = lean_ctor_get(v_m_1269_, 0);
v_buckets_1273_ = lean_ctor_get(v_m_1269_, 1);
v_isSharedCheck_1316_ = !lean_is_exclusive(v_m_1269_);
if (v_isSharedCheck_1316_ == 0)
{
v___x_1275_ = v_m_1269_;
v_isShared_1276_ = v_isSharedCheck_1316_;
goto v_resetjp_1274_;
}
else
{
lean_inc(v_buckets_1273_);
lean_inc(v_size_1272_);
lean_dec(v_m_1269_);
v___x_1275_ = lean_box(0);
v_isShared_1276_ = v_isSharedCheck_1316_;
goto v_resetjp_1274_;
}
v_resetjp_1274_:
{
lean_object* v___x_1277_; uint64_t v___x_1278_; uint64_t v___x_1279_; uint64_t v___x_1280_; uint64_t v_fold_1281_; uint64_t v___x_1282_; uint64_t v___x_1283_; uint64_t v___x_1284_; size_t v___x_1285_; size_t v___x_1286_; size_t v___x_1287_; size_t v___x_1288_; size_t v___x_1289_; lean_object* v_bkt_1290_; uint8_t v___x_1291_; 
v___x_1277_ = lean_array_get_size(v_buckets_1273_);
v___x_1278_ = l_Lean_ExprStructEq_hash(v_a_1270_);
v___x_1279_ = 32ULL;
v___x_1280_ = lean_uint64_shift_right(v___x_1278_, v___x_1279_);
v_fold_1281_ = lean_uint64_xor(v___x_1278_, v___x_1280_);
v___x_1282_ = 16ULL;
v___x_1283_ = lean_uint64_shift_right(v_fold_1281_, v___x_1282_);
v___x_1284_ = lean_uint64_xor(v_fold_1281_, v___x_1283_);
v___x_1285_ = lean_uint64_to_usize(v___x_1284_);
v___x_1286_ = lean_usize_of_nat(v___x_1277_);
v___x_1287_ = ((size_t)1ULL);
v___x_1288_ = lean_usize_sub(v___x_1286_, v___x_1287_);
v___x_1289_ = lean_usize_land(v___x_1285_, v___x_1288_);
v_bkt_1290_ = lean_array_uget_borrowed(v_buckets_1273_, v___x_1289_);
v___x_1291_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__2___redArg(v_a_1270_, v_bkt_1290_);
if (v___x_1291_ == 0)
{
lean_object* v___x_1292_; lean_object* v_size_x27_1293_; lean_object* v___x_1294_; lean_object* v_buckets_x27_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; uint8_t v___x_1301_; 
v___x_1292_ = lean_unsigned_to_nat(1u);
v_size_x27_1293_ = lean_nat_add(v_size_1272_, v___x_1292_);
lean_dec(v_size_1272_);
lean_inc(v_bkt_1290_);
v___x_1294_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1294_, 0, v_a_1270_);
lean_ctor_set(v___x_1294_, 1, v_b_1271_);
lean_ctor_set(v___x_1294_, 2, v_bkt_1290_);
v_buckets_x27_1295_ = lean_array_uset(v_buckets_1273_, v___x_1289_, v___x_1294_);
v___x_1296_ = lean_unsigned_to_nat(4u);
v___x_1297_ = lean_nat_mul(v_size_x27_1293_, v___x_1296_);
v___x_1298_ = lean_unsigned_to_nat(3u);
v___x_1299_ = lean_nat_div(v___x_1297_, v___x_1298_);
lean_dec(v___x_1297_);
v___x_1300_ = lean_array_get_size(v_buckets_x27_1295_);
v___x_1301_ = lean_nat_dec_le(v___x_1299_, v___x_1300_);
lean_dec(v___x_1299_);
if (v___x_1301_ == 0)
{
lean_object* v_val_1302_; lean_object* v___x_1304_; 
v_val_1302_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__3___redArg(v_buckets_x27_1295_);
if (v_isShared_1276_ == 0)
{
lean_ctor_set(v___x_1275_, 1, v_val_1302_);
lean_ctor_set(v___x_1275_, 0, v_size_x27_1293_);
v___x_1304_ = v___x_1275_;
goto v_reusejp_1303_;
}
else
{
lean_object* v_reuseFailAlloc_1305_; 
v_reuseFailAlloc_1305_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1305_, 0, v_size_x27_1293_);
lean_ctor_set(v_reuseFailAlloc_1305_, 1, v_val_1302_);
v___x_1304_ = v_reuseFailAlloc_1305_;
goto v_reusejp_1303_;
}
v_reusejp_1303_:
{
return v___x_1304_;
}
}
else
{
lean_object* v___x_1307_; 
if (v_isShared_1276_ == 0)
{
lean_ctor_set(v___x_1275_, 1, v_buckets_x27_1295_);
lean_ctor_set(v___x_1275_, 0, v_size_x27_1293_);
v___x_1307_ = v___x_1275_;
goto v_reusejp_1306_;
}
else
{
lean_object* v_reuseFailAlloc_1308_; 
v_reuseFailAlloc_1308_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1308_, 0, v_size_x27_1293_);
lean_ctor_set(v_reuseFailAlloc_1308_, 1, v_buckets_x27_1295_);
v___x_1307_ = v_reuseFailAlloc_1308_;
goto v_reusejp_1306_;
}
v_reusejp_1306_:
{
return v___x_1307_;
}
}
}
else
{
lean_object* v___x_1309_; lean_object* v_buckets_x27_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1314_; 
lean_inc(v_bkt_1290_);
v___x_1309_ = lean_box(0);
v_buckets_x27_1310_ = lean_array_uset(v_buckets_1273_, v___x_1289_, v___x_1309_);
v___x_1311_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__4___redArg(v_a_1270_, v_b_1271_, v_bkt_1290_);
v___x_1312_ = lean_array_uset(v_buckets_x27_1310_, v___x_1289_, v___x_1311_);
if (v_isShared_1276_ == 0)
{
lean_ctor_set(v___x_1275_, 1, v___x_1312_);
v___x_1314_ = v___x_1275_;
goto v_reusejp_1313_;
}
else
{
lean_object* v_reuseFailAlloc_1315_; 
v_reuseFailAlloc_1315_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1315_, 0, v_size_1272_);
lean_ctor_set(v_reuseFailAlloc_1315_, 1, v___x_1312_);
v___x_1314_ = v_reuseFailAlloc_1315_;
goto v_reusejp_1313_;
}
v_reusejp_1313_:
{
return v___x_1314_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectExprAux(lean_object* v_e_1317_, uint8_t v_a_1318_, lean_object* v_a_1319_, lean_object* v_a_1320_, lean_object* v_a_1321_, lean_object* v_a_1322_, lean_object* v_a_1323_){
_start:
{
switch(lean_obj_tag(v_e_1317_))
{
case 11:
{
lean_object* v_typeName_1325_; lean_object* v_idx_1326_; lean_object* v_struct_1327_; lean_object* v___x_1328_; 
v_typeName_1325_ = lean_ctor_get(v_e_1317_, 0);
v_idx_1326_ = lean_ctor_get(v_e_1317_, 1);
v_struct_1327_ = lean_ctor_get(v_e_1317_, 2);
lean_inc_ref(v_struct_1327_);
v___x_1328_ = l_Lean_Meta_Closure_collectExprAux___lam__0(v_struct_1327_, v_a_1318_, v_a_1319_, v_a_1320_, v_a_1321_, v_a_1322_, v_a_1323_);
if (lean_obj_tag(v___x_1328_) == 0)
{
lean_object* v_a_1329_; lean_object* v___x_1331_; uint8_t v_isShared_1332_; uint8_t v_isSharedCheck_1343_; 
v_a_1329_ = lean_ctor_get(v___x_1328_, 0);
v_isSharedCheck_1343_ = !lean_is_exclusive(v___x_1328_);
if (v_isSharedCheck_1343_ == 0)
{
v___x_1331_ = v___x_1328_;
v_isShared_1332_ = v_isSharedCheck_1343_;
goto v_resetjp_1330_;
}
else
{
lean_inc(v_a_1329_);
lean_dec(v___x_1328_);
v___x_1331_ = lean_box(0);
v_isShared_1332_ = v_isSharedCheck_1343_;
goto v_resetjp_1330_;
}
v_resetjp_1330_:
{
size_t v___x_1333_; size_t v___x_1334_; uint8_t v___x_1335_; 
v___x_1333_ = lean_ptr_addr(v_struct_1327_);
v___x_1334_ = lean_ptr_addr(v_a_1329_);
v___x_1335_ = lean_usize_dec_eq(v___x_1333_, v___x_1334_);
if (v___x_1335_ == 0)
{
lean_object* v___x_1336_; lean_object* v___x_1338_; 
lean_inc(v_idx_1326_);
lean_inc(v_typeName_1325_);
lean_dec_ref_known(v_e_1317_, 3);
v___x_1336_ = l_Lean_Expr_proj___override(v_typeName_1325_, v_idx_1326_, v_a_1329_);
if (v_isShared_1332_ == 0)
{
lean_ctor_set(v___x_1331_, 0, v___x_1336_);
v___x_1338_ = v___x_1331_;
goto v_reusejp_1337_;
}
else
{
lean_object* v_reuseFailAlloc_1339_; 
v_reuseFailAlloc_1339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1339_, 0, v___x_1336_);
v___x_1338_ = v_reuseFailAlloc_1339_;
goto v_reusejp_1337_;
}
v_reusejp_1337_:
{
return v___x_1338_;
}
}
else
{
lean_object* v___x_1341_; 
lean_dec(v_a_1329_);
if (v_isShared_1332_ == 0)
{
lean_ctor_set(v___x_1331_, 0, v_e_1317_);
v___x_1341_ = v___x_1331_;
goto v_reusejp_1340_;
}
else
{
lean_object* v_reuseFailAlloc_1342_; 
v_reuseFailAlloc_1342_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1342_, 0, v_e_1317_);
v___x_1341_ = v_reuseFailAlloc_1342_;
goto v_reusejp_1340_;
}
v_reusejp_1340_:
{
return v___x_1341_;
}
}
}
}
else
{
lean_dec_ref_known(v_e_1317_, 3);
return v___x_1328_;
}
}
case 7:
{
lean_object* v_binderName_1344_; lean_object* v_binderType_1345_; lean_object* v_body_1346_; uint8_t v_binderInfo_1347_; lean_object* v___x_1348_; 
v_binderName_1344_ = lean_ctor_get(v_e_1317_, 0);
v_binderType_1345_ = lean_ctor_get(v_e_1317_, 1);
v_body_1346_ = lean_ctor_get(v_e_1317_, 2);
v_binderInfo_1347_ = lean_ctor_get_uint8(v_e_1317_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_1345_);
v___x_1348_ = l_Lean_Meta_Closure_collectExprAux___lam__0(v_binderType_1345_, v_a_1318_, v_a_1319_, v_a_1320_, v_a_1321_, v_a_1322_, v_a_1323_);
if (lean_obj_tag(v___x_1348_) == 0)
{
lean_object* v_a_1349_; lean_object* v___x_1350_; 
v_a_1349_ = lean_ctor_get(v___x_1348_, 0);
lean_inc(v_a_1349_);
lean_dec_ref_known(v___x_1348_, 1);
lean_inc_ref(v_body_1346_);
v___x_1350_ = l_Lean_Meta_Closure_collectExprAux___lam__0(v_body_1346_, v_a_1318_, v_a_1319_, v_a_1320_, v_a_1321_, v_a_1322_, v_a_1323_);
if (lean_obj_tag(v___x_1350_) == 0)
{
lean_object* v_a_1351_; lean_object* v___x_1353_; uint8_t v_isShared_1354_; uint8_t v_isSharedCheck_1377_; 
v_a_1351_ = lean_ctor_get(v___x_1350_, 0);
v_isSharedCheck_1377_ = !lean_is_exclusive(v___x_1350_);
if (v_isSharedCheck_1377_ == 0)
{
v___x_1353_ = v___x_1350_;
v_isShared_1354_ = v_isSharedCheck_1377_;
goto v_resetjp_1352_;
}
else
{
lean_inc(v_a_1351_);
lean_dec(v___x_1350_);
v___x_1353_ = lean_box(0);
v_isShared_1354_ = v_isSharedCheck_1377_;
goto v_resetjp_1352_;
}
v_resetjp_1352_:
{
size_t v___x_1355_; size_t v___x_1356_; uint8_t v___x_1357_; 
v___x_1355_ = lean_ptr_addr(v_binderType_1345_);
v___x_1356_ = lean_ptr_addr(v_a_1349_);
v___x_1357_ = lean_usize_dec_eq(v___x_1355_, v___x_1356_);
if (v___x_1357_ == 0)
{
lean_object* v___x_1358_; lean_object* v___x_1360_; 
lean_inc(v_binderName_1344_);
lean_dec_ref_known(v_e_1317_, 3);
v___x_1358_ = l_Lean_Expr_forallE___override(v_binderName_1344_, v_a_1349_, v_a_1351_, v_binderInfo_1347_);
if (v_isShared_1354_ == 0)
{
lean_ctor_set(v___x_1353_, 0, v___x_1358_);
v___x_1360_ = v___x_1353_;
goto v_reusejp_1359_;
}
else
{
lean_object* v_reuseFailAlloc_1361_; 
v_reuseFailAlloc_1361_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1361_, 0, v___x_1358_);
v___x_1360_ = v_reuseFailAlloc_1361_;
goto v_reusejp_1359_;
}
v_reusejp_1359_:
{
return v___x_1360_;
}
}
else
{
size_t v___x_1362_; size_t v___x_1363_; uint8_t v___x_1364_; 
v___x_1362_ = lean_ptr_addr(v_body_1346_);
v___x_1363_ = lean_ptr_addr(v_a_1351_);
v___x_1364_ = lean_usize_dec_eq(v___x_1362_, v___x_1363_);
if (v___x_1364_ == 0)
{
lean_object* v___x_1365_; lean_object* v___x_1367_; 
lean_inc(v_binderName_1344_);
lean_dec_ref_known(v_e_1317_, 3);
v___x_1365_ = l_Lean_Expr_forallE___override(v_binderName_1344_, v_a_1349_, v_a_1351_, v_binderInfo_1347_);
if (v_isShared_1354_ == 0)
{
lean_ctor_set(v___x_1353_, 0, v___x_1365_);
v___x_1367_ = v___x_1353_;
goto v_reusejp_1366_;
}
else
{
lean_object* v_reuseFailAlloc_1368_; 
v_reuseFailAlloc_1368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1368_, 0, v___x_1365_);
v___x_1367_ = v_reuseFailAlloc_1368_;
goto v_reusejp_1366_;
}
v_reusejp_1366_:
{
return v___x_1367_;
}
}
else
{
uint8_t v___x_1369_; 
v___x_1369_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_1347_, v_binderInfo_1347_);
if (v___x_1369_ == 0)
{
lean_object* v___x_1370_; lean_object* v___x_1372_; 
lean_inc(v_binderName_1344_);
lean_dec_ref_known(v_e_1317_, 3);
v___x_1370_ = l_Lean_Expr_forallE___override(v_binderName_1344_, v_a_1349_, v_a_1351_, v_binderInfo_1347_);
if (v_isShared_1354_ == 0)
{
lean_ctor_set(v___x_1353_, 0, v___x_1370_);
v___x_1372_ = v___x_1353_;
goto v_reusejp_1371_;
}
else
{
lean_object* v_reuseFailAlloc_1373_; 
v_reuseFailAlloc_1373_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1373_, 0, v___x_1370_);
v___x_1372_ = v_reuseFailAlloc_1373_;
goto v_reusejp_1371_;
}
v_reusejp_1371_:
{
return v___x_1372_;
}
}
else
{
lean_object* v___x_1375_; 
lean_dec(v_a_1351_);
lean_dec(v_a_1349_);
if (v_isShared_1354_ == 0)
{
lean_ctor_set(v___x_1353_, 0, v_e_1317_);
v___x_1375_ = v___x_1353_;
goto v_reusejp_1374_;
}
else
{
lean_object* v_reuseFailAlloc_1376_; 
v_reuseFailAlloc_1376_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1376_, 0, v_e_1317_);
v___x_1375_ = v_reuseFailAlloc_1376_;
goto v_reusejp_1374_;
}
v_reusejp_1374_:
{
return v___x_1375_;
}
}
}
}
}
}
else
{
lean_dec(v_a_1349_);
lean_dec_ref_known(v_e_1317_, 3);
return v___x_1350_;
}
}
else
{
lean_dec_ref_known(v_e_1317_, 3);
return v___x_1348_;
}
}
case 6:
{
lean_object* v_binderName_1378_; lean_object* v_binderType_1379_; lean_object* v_body_1380_; uint8_t v_binderInfo_1381_; lean_object* v___x_1382_; 
v_binderName_1378_ = lean_ctor_get(v_e_1317_, 0);
v_binderType_1379_ = lean_ctor_get(v_e_1317_, 1);
v_body_1380_ = lean_ctor_get(v_e_1317_, 2);
v_binderInfo_1381_ = lean_ctor_get_uint8(v_e_1317_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_1379_);
v___x_1382_ = l_Lean_Meta_Closure_collectExprAux___lam__0(v_binderType_1379_, v_a_1318_, v_a_1319_, v_a_1320_, v_a_1321_, v_a_1322_, v_a_1323_);
if (lean_obj_tag(v___x_1382_) == 0)
{
lean_object* v_a_1383_; lean_object* v___x_1384_; 
v_a_1383_ = lean_ctor_get(v___x_1382_, 0);
lean_inc(v_a_1383_);
lean_dec_ref_known(v___x_1382_, 1);
lean_inc_ref(v_body_1380_);
v___x_1384_ = l_Lean_Meta_Closure_collectExprAux___lam__0(v_body_1380_, v_a_1318_, v_a_1319_, v_a_1320_, v_a_1321_, v_a_1322_, v_a_1323_);
if (lean_obj_tag(v___x_1384_) == 0)
{
lean_object* v_a_1385_; lean_object* v___x_1387_; uint8_t v_isShared_1388_; uint8_t v_isSharedCheck_1411_; 
v_a_1385_ = lean_ctor_get(v___x_1384_, 0);
v_isSharedCheck_1411_ = !lean_is_exclusive(v___x_1384_);
if (v_isSharedCheck_1411_ == 0)
{
v___x_1387_ = v___x_1384_;
v_isShared_1388_ = v_isSharedCheck_1411_;
goto v_resetjp_1386_;
}
else
{
lean_inc(v_a_1385_);
lean_dec(v___x_1384_);
v___x_1387_ = lean_box(0);
v_isShared_1388_ = v_isSharedCheck_1411_;
goto v_resetjp_1386_;
}
v_resetjp_1386_:
{
size_t v___x_1389_; size_t v___x_1390_; uint8_t v___x_1391_; 
v___x_1389_ = lean_ptr_addr(v_binderType_1379_);
v___x_1390_ = lean_ptr_addr(v_a_1383_);
v___x_1391_ = lean_usize_dec_eq(v___x_1389_, v___x_1390_);
if (v___x_1391_ == 0)
{
lean_object* v___x_1392_; lean_object* v___x_1394_; 
lean_inc(v_binderName_1378_);
lean_dec_ref_known(v_e_1317_, 3);
v___x_1392_ = l_Lean_Expr_lam___override(v_binderName_1378_, v_a_1383_, v_a_1385_, v_binderInfo_1381_);
if (v_isShared_1388_ == 0)
{
lean_ctor_set(v___x_1387_, 0, v___x_1392_);
v___x_1394_ = v___x_1387_;
goto v_reusejp_1393_;
}
else
{
lean_object* v_reuseFailAlloc_1395_; 
v_reuseFailAlloc_1395_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1395_, 0, v___x_1392_);
v___x_1394_ = v_reuseFailAlloc_1395_;
goto v_reusejp_1393_;
}
v_reusejp_1393_:
{
return v___x_1394_;
}
}
else
{
size_t v___x_1396_; size_t v___x_1397_; uint8_t v___x_1398_; 
v___x_1396_ = lean_ptr_addr(v_body_1380_);
v___x_1397_ = lean_ptr_addr(v_a_1385_);
v___x_1398_ = lean_usize_dec_eq(v___x_1396_, v___x_1397_);
if (v___x_1398_ == 0)
{
lean_object* v___x_1399_; lean_object* v___x_1401_; 
lean_inc(v_binderName_1378_);
lean_dec_ref_known(v_e_1317_, 3);
v___x_1399_ = l_Lean_Expr_lam___override(v_binderName_1378_, v_a_1383_, v_a_1385_, v_binderInfo_1381_);
if (v_isShared_1388_ == 0)
{
lean_ctor_set(v___x_1387_, 0, v___x_1399_);
v___x_1401_ = v___x_1387_;
goto v_reusejp_1400_;
}
else
{
lean_object* v_reuseFailAlloc_1402_; 
v_reuseFailAlloc_1402_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1402_, 0, v___x_1399_);
v___x_1401_ = v_reuseFailAlloc_1402_;
goto v_reusejp_1400_;
}
v_reusejp_1400_:
{
return v___x_1401_;
}
}
else
{
uint8_t v___x_1403_; 
v___x_1403_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_1381_, v_binderInfo_1381_);
if (v___x_1403_ == 0)
{
lean_object* v___x_1404_; lean_object* v___x_1406_; 
lean_inc(v_binderName_1378_);
lean_dec_ref_known(v_e_1317_, 3);
v___x_1404_ = l_Lean_Expr_lam___override(v_binderName_1378_, v_a_1383_, v_a_1385_, v_binderInfo_1381_);
if (v_isShared_1388_ == 0)
{
lean_ctor_set(v___x_1387_, 0, v___x_1404_);
v___x_1406_ = v___x_1387_;
goto v_reusejp_1405_;
}
else
{
lean_object* v_reuseFailAlloc_1407_; 
v_reuseFailAlloc_1407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1407_, 0, v___x_1404_);
v___x_1406_ = v_reuseFailAlloc_1407_;
goto v_reusejp_1405_;
}
v_reusejp_1405_:
{
return v___x_1406_;
}
}
else
{
lean_object* v___x_1409_; 
lean_dec(v_a_1385_);
lean_dec(v_a_1383_);
if (v_isShared_1388_ == 0)
{
lean_ctor_set(v___x_1387_, 0, v_e_1317_);
v___x_1409_ = v___x_1387_;
goto v_reusejp_1408_;
}
else
{
lean_object* v_reuseFailAlloc_1410_; 
v_reuseFailAlloc_1410_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1410_, 0, v_e_1317_);
v___x_1409_ = v_reuseFailAlloc_1410_;
goto v_reusejp_1408_;
}
v_reusejp_1408_:
{
return v___x_1409_;
}
}
}
}
}
}
else
{
lean_dec(v_a_1383_);
lean_dec_ref_known(v_e_1317_, 3);
return v___x_1384_;
}
}
else
{
lean_dec_ref_known(v_e_1317_, 3);
return v___x_1382_;
}
}
case 8:
{
lean_object* v_declName_1412_; lean_object* v_type_1413_; lean_object* v_value_1414_; lean_object* v_body_1415_; uint8_t v_nondep_1416_; lean_object* v___x_1417_; 
v_declName_1412_ = lean_ctor_get(v_e_1317_, 0);
v_type_1413_ = lean_ctor_get(v_e_1317_, 1);
v_value_1414_ = lean_ctor_get(v_e_1317_, 2);
v_body_1415_ = lean_ctor_get(v_e_1317_, 3);
v_nondep_1416_ = lean_ctor_get_uint8(v_e_1317_, sizeof(void*)*4 + 8);
lean_inc_ref(v_type_1413_);
v___x_1417_ = l_Lean_Meta_Closure_collectExprAux___lam__0(v_type_1413_, v_a_1318_, v_a_1319_, v_a_1320_, v_a_1321_, v_a_1322_, v_a_1323_);
if (lean_obj_tag(v___x_1417_) == 0)
{
lean_object* v_a_1418_; lean_object* v___x_1419_; 
v_a_1418_ = lean_ctor_get(v___x_1417_, 0);
lean_inc(v_a_1418_);
lean_dec_ref_known(v___x_1417_, 1);
lean_inc_ref(v_value_1414_);
v___x_1419_ = l_Lean_Meta_Closure_collectExprAux___lam__0(v_value_1414_, v_a_1318_, v_a_1319_, v_a_1320_, v_a_1321_, v_a_1322_, v_a_1323_);
if (lean_obj_tag(v___x_1419_) == 0)
{
lean_object* v_a_1420_; lean_object* v___x_1421_; 
v_a_1420_ = lean_ctor_get(v___x_1419_, 0);
lean_inc(v_a_1420_);
lean_dec_ref_known(v___x_1419_, 1);
lean_inc_ref(v_body_1415_);
v___x_1421_ = l_Lean_Meta_Closure_collectExprAux___lam__0(v_body_1415_, v_a_1318_, v_a_1319_, v_a_1320_, v_a_1321_, v_a_1322_, v_a_1323_);
if (lean_obj_tag(v___x_1421_) == 0)
{
lean_object* v_a_1422_; lean_object* v___x_1424_; uint8_t v_isShared_1425_; uint8_t v_isSharedCheck_1450_; 
v_a_1422_ = lean_ctor_get(v___x_1421_, 0);
v_isSharedCheck_1450_ = !lean_is_exclusive(v___x_1421_);
if (v_isSharedCheck_1450_ == 0)
{
v___x_1424_ = v___x_1421_;
v_isShared_1425_ = v_isSharedCheck_1450_;
goto v_resetjp_1423_;
}
else
{
lean_inc(v_a_1422_);
lean_dec(v___x_1421_);
v___x_1424_ = lean_box(0);
v_isShared_1425_ = v_isSharedCheck_1450_;
goto v_resetjp_1423_;
}
v_resetjp_1423_:
{
size_t v___x_1426_; size_t v___x_1427_; uint8_t v___x_1428_; 
v___x_1426_ = lean_ptr_addr(v_type_1413_);
v___x_1427_ = lean_ptr_addr(v_a_1418_);
v___x_1428_ = lean_usize_dec_eq(v___x_1426_, v___x_1427_);
if (v___x_1428_ == 0)
{
lean_object* v___x_1429_; lean_object* v___x_1431_; 
lean_inc(v_declName_1412_);
lean_dec_ref_known(v_e_1317_, 4);
v___x_1429_ = l_Lean_Expr_letE___override(v_declName_1412_, v_a_1418_, v_a_1420_, v_a_1422_, v_nondep_1416_);
if (v_isShared_1425_ == 0)
{
lean_ctor_set(v___x_1424_, 0, v___x_1429_);
v___x_1431_ = v___x_1424_;
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
size_t v___x_1433_; size_t v___x_1434_; uint8_t v___x_1435_; 
v___x_1433_ = lean_ptr_addr(v_value_1414_);
v___x_1434_ = lean_ptr_addr(v_a_1420_);
v___x_1435_ = lean_usize_dec_eq(v___x_1433_, v___x_1434_);
if (v___x_1435_ == 0)
{
lean_object* v___x_1436_; lean_object* v___x_1438_; 
lean_inc(v_declName_1412_);
lean_dec_ref_known(v_e_1317_, 4);
v___x_1436_ = l_Lean_Expr_letE___override(v_declName_1412_, v_a_1418_, v_a_1420_, v_a_1422_, v_nondep_1416_);
if (v_isShared_1425_ == 0)
{
lean_ctor_set(v___x_1424_, 0, v___x_1436_);
v___x_1438_ = v___x_1424_;
goto v_reusejp_1437_;
}
else
{
lean_object* v_reuseFailAlloc_1439_; 
v_reuseFailAlloc_1439_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1439_, 0, v___x_1436_);
v___x_1438_ = v_reuseFailAlloc_1439_;
goto v_reusejp_1437_;
}
v_reusejp_1437_:
{
return v___x_1438_;
}
}
else
{
size_t v___x_1440_; size_t v___x_1441_; uint8_t v___x_1442_; 
v___x_1440_ = lean_ptr_addr(v_body_1415_);
v___x_1441_ = lean_ptr_addr(v_a_1422_);
v___x_1442_ = lean_usize_dec_eq(v___x_1440_, v___x_1441_);
if (v___x_1442_ == 0)
{
lean_object* v___x_1443_; lean_object* v___x_1445_; 
lean_inc(v_declName_1412_);
lean_dec_ref_known(v_e_1317_, 4);
v___x_1443_ = l_Lean_Expr_letE___override(v_declName_1412_, v_a_1418_, v_a_1420_, v_a_1422_, v_nondep_1416_);
if (v_isShared_1425_ == 0)
{
lean_ctor_set(v___x_1424_, 0, v___x_1443_);
v___x_1445_ = v___x_1424_;
goto v_reusejp_1444_;
}
else
{
lean_object* v_reuseFailAlloc_1446_; 
v_reuseFailAlloc_1446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1446_, 0, v___x_1443_);
v___x_1445_ = v_reuseFailAlloc_1446_;
goto v_reusejp_1444_;
}
v_reusejp_1444_:
{
return v___x_1445_;
}
}
else
{
lean_object* v___x_1448_; 
lean_dec(v_a_1422_);
lean_dec(v_a_1420_);
lean_dec(v_a_1418_);
if (v_isShared_1425_ == 0)
{
lean_ctor_set(v___x_1424_, 0, v_e_1317_);
v___x_1448_ = v___x_1424_;
goto v_reusejp_1447_;
}
else
{
lean_object* v_reuseFailAlloc_1449_; 
v_reuseFailAlloc_1449_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1449_, 0, v_e_1317_);
v___x_1448_ = v_reuseFailAlloc_1449_;
goto v_reusejp_1447_;
}
v_reusejp_1447_:
{
return v___x_1448_;
}
}
}
}
}
}
else
{
lean_dec(v_a_1420_);
lean_dec(v_a_1418_);
lean_dec_ref_known(v_e_1317_, 4);
return v___x_1421_;
}
}
else
{
lean_dec(v_a_1418_);
lean_dec_ref_known(v_e_1317_, 4);
return v___x_1419_;
}
}
else
{
lean_dec_ref_known(v_e_1317_, 4);
return v___x_1417_;
}
}
case 5:
{
lean_object* v_fn_1451_; lean_object* v_arg_1452_; lean_object* v___x_1453_; 
v_fn_1451_ = lean_ctor_get(v_e_1317_, 0);
v_arg_1452_ = lean_ctor_get(v_e_1317_, 1);
lean_inc_ref(v_fn_1451_);
v___x_1453_ = l_Lean_Meta_Closure_collectExprAux___lam__0(v_fn_1451_, v_a_1318_, v_a_1319_, v_a_1320_, v_a_1321_, v_a_1322_, v_a_1323_);
if (lean_obj_tag(v___x_1453_) == 0)
{
lean_object* v_a_1454_; lean_object* v___x_1455_; 
v_a_1454_ = lean_ctor_get(v___x_1453_, 0);
lean_inc(v_a_1454_);
lean_dec_ref_known(v___x_1453_, 1);
lean_inc_ref(v_arg_1452_);
v___x_1455_ = l_Lean_Meta_Closure_collectExprAux___lam__0(v_arg_1452_, v_a_1318_, v_a_1319_, v_a_1320_, v_a_1321_, v_a_1322_, v_a_1323_);
if (lean_obj_tag(v___x_1455_) == 0)
{
lean_object* v_a_1456_; lean_object* v___x_1458_; uint8_t v_isShared_1459_; uint8_t v_isSharedCheck_1477_; 
v_a_1456_ = lean_ctor_get(v___x_1455_, 0);
v_isSharedCheck_1477_ = !lean_is_exclusive(v___x_1455_);
if (v_isSharedCheck_1477_ == 0)
{
v___x_1458_ = v___x_1455_;
v_isShared_1459_ = v_isSharedCheck_1477_;
goto v_resetjp_1457_;
}
else
{
lean_inc(v_a_1456_);
lean_dec(v___x_1455_);
v___x_1458_ = lean_box(0);
v_isShared_1459_ = v_isSharedCheck_1477_;
goto v_resetjp_1457_;
}
v_resetjp_1457_:
{
size_t v___x_1460_; size_t v___x_1461_; uint8_t v___x_1462_; 
v___x_1460_ = lean_ptr_addr(v_fn_1451_);
v___x_1461_ = lean_ptr_addr(v_a_1454_);
v___x_1462_ = lean_usize_dec_eq(v___x_1460_, v___x_1461_);
if (v___x_1462_ == 0)
{
lean_object* v___x_1463_; lean_object* v___x_1465_; 
lean_dec_ref_known(v_e_1317_, 2);
v___x_1463_ = l_Lean_Expr_app___override(v_a_1454_, v_a_1456_);
if (v_isShared_1459_ == 0)
{
lean_ctor_set(v___x_1458_, 0, v___x_1463_);
v___x_1465_ = v___x_1458_;
goto v_reusejp_1464_;
}
else
{
lean_object* v_reuseFailAlloc_1466_; 
v_reuseFailAlloc_1466_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1466_, 0, v___x_1463_);
v___x_1465_ = v_reuseFailAlloc_1466_;
goto v_reusejp_1464_;
}
v_reusejp_1464_:
{
return v___x_1465_;
}
}
else
{
size_t v___x_1467_; size_t v___x_1468_; uint8_t v___x_1469_; 
v___x_1467_ = lean_ptr_addr(v_arg_1452_);
v___x_1468_ = lean_ptr_addr(v_a_1456_);
v___x_1469_ = lean_usize_dec_eq(v___x_1467_, v___x_1468_);
if (v___x_1469_ == 0)
{
lean_object* v___x_1470_; lean_object* v___x_1472_; 
lean_dec_ref_known(v_e_1317_, 2);
v___x_1470_ = l_Lean_Expr_app___override(v_a_1454_, v_a_1456_);
if (v_isShared_1459_ == 0)
{
lean_ctor_set(v___x_1458_, 0, v___x_1470_);
v___x_1472_ = v___x_1458_;
goto v_reusejp_1471_;
}
else
{
lean_object* v_reuseFailAlloc_1473_; 
v_reuseFailAlloc_1473_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1473_, 0, v___x_1470_);
v___x_1472_ = v_reuseFailAlloc_1473_;
goto v_reusejp_1471_;
}
v_reusejp_1471_:
{
return v___x_1472_;
}
}
else
{
lean_object* v___x_1475_; 
lean_dec(v_a_1456_);
lean_dec(v_a_1454_);
if (v_isShared_1459_ == 0)
{
lean_ctor_set(v___x_1458_, 0, v_e_1317_);
v___x_1475_ = v___x_1458_;
goto v_reusejp_1474_;
}
else
{
lean_object* v_reuseFailAlloc_1476_; 
v_reuseFailAlloc_1476_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1476_, 0, v_e_1317_);
v___x_1475_ = v_reuseFailAlloc_1476_;
goto v_reusejp_1474_;
}
v_reusejp_1474_:
{
return v___x_1475_;
}
}
}
}
}
else
{
lean_dec(v_a_1454_);
lean_dec_ref_known(v_e_1317_, 2);
return v___x_1455_;
}
}
else
{
lean_dec_ref_known(v_e_1317_, 2);
return v___x_1453_;
}
}
case 10:
{
lean_object* v_data_1478_; lean_object* v_expr_1479_; lean_object* v___x_1480_; 
v_data_1478_ = lean_ctor_get(v_e_1317_, 0);
v_expr_1479_ = lean_ctor_get(v_e_1317_, 1);
lean_inc_ref(v_expr_1479_);
v___x_1480_ = l_Lean_Meta_Closure_collectExprAux___lam__0(v_expr_1479_, v_a_1318_, v_a_1319_, v_a_1320_, v_a_1321_, v_a_1322_, v_a_1323_);
if (lean_obj_tag(v___x_1480_) == 0)
{
lean_object* v_a_1481_; lean_object* v___x_1483_; uint8_t v_isShared_1484_; uint8_t v_isSharedCheck_1495_; 
v_a_1481_ = lean_ctor_get(v___x_1480_, 0);
v_isSharedCheck_1495_ = !lean_is_exclusive(v___x_1480_);
if (v_isSharedCheck_1495_ == 0)
{
v___x_1483_ = v___x_1480_;
v_isShared_1484_ = v_isSharedCheck_1495_;
goto v_resetjp_1482_;
}
else
{
lean_inc(v_a_1481_);
lean_dec(v___x_1480_);
v___x_1483_ = lean_box(0);
v_isShared_1484_ = v_isSharedCheck_1495_;
goto v_resetjp_1482_;
}
v_resetjp_1482_:
{
size_t v___x_1485_; size_t v___x_1486_; uint8_t v___x_1487_; 
v___x_1485_ = lean_ptr_addr(v_expr_1479_);
v___x_1486_ = lean_ptr_addr(v_a_1481_);
v___x_1487_ = lean_usize_dec_eq(v___x_1485_, v___x_1486_);
if (v___x_1487_ == 0)
{
lean_object* v___x_1488_; lean_object* v___x_1490_; 
lean_inc(v_data_1478_);
lean_dec_ref_known(v_e_1317_, 2);
v___x_1488_ = l_Lean_Expr_mdata___override(v_data_1478_, v_a_1481_);
if (v_isShared_1484_ == 0)
{
lean_ctor_set(v___x_1483_, 0, v___x_1488_);
v___x_1490_ = v___x_1483_;
goto v_reusejp_1489_;
}
else
{
lean_object* v_reuseFailAlloc_1491_; 
v_reuseFailAlloc_1491_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1491_, 0, v___x_1488_);
v___x_1490_ = v_reuseFailAlloc_1491_;
goto v_reusejp_1489_;
}
v_reusejp_1489_:
{
return v___x_1490_;
}
}
else
{
lean_object* v___x_1493_; 
lean_dec(v_a_1481_);
if (v_isShared_1484_ == 0)
{
lean_ctor_set(v___x_1483_, 0, v_e_1317_);
v___x_1493_ = v___x_1483_;
goto v_reusejp_1492_;
}
else
{
lean_object* v_reuseFailAlloc_1494_; 
v_reuseFailAlloc_1494_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1494_, 0, v_e_1317_);
v___x_1493_ = v_reuseFailAlloc_1494_;
goto v_reusejp_1492_;
}
v_reusejp_1492_:
{
return v___x_1493_;
}
}
}
}
else
{
lean_dec_ref_known(v_e_1317_, 2);
return v___x_1480_;
}
}
case 3:
{
lean_object* v_u_1496_; lean_object* v___x_1497_; 
v_u_1496_ = lean_ctor_get(v_e_1317_, 0);
lean_inc(v_u_1496_);
v___x_1497_ = l_Lean_Meta_Closure_collectLevel___redArg(v_u_1496_, v_a_1319_);
if (lean_obj_tag(v___x_1497_) == 0)
{
lean_object* v_a_1498_; lean_object* v___x_1500_; uint8_t v_isShared_1501_; uint8_t v_isSharedCheck_1512_; 
v_a_1498_ = lean_ctor_get(v___x_1497_, 0);
v_isSharedCheck_1512_ = !lean_is_exclusive(v___x_1497_);
if (v_isSharedCheck_1512_ == 0)
{
v___x_1500_ = v___x_1497_;
v_isShared_1501_ = v_isSharedCheck_1512_;
goto v_resetjp_1499_;
}
else
{
lean_inc(v_a_1498_);
lean_dec(v___x_1497_);
v___x_1500_ = lean_box(0);
v_isShared_1501_ = v_isSharedCheck_1512_;
goto v_resetjp_1499_;
}
v_resetjp_1499_:
{
size_t v___x_1502_; size_t v___x_1503_; uint8_t v___x_1504_; 
v___x_1502_ = lean_ptr_addr(v_u_1496_);
v___x_1503_ = lean_ptr_addr(v_a_1498_);
v___x_1504_ = lean_usize_dec_eq(v___x_1502_, v___x_1503_);
if (v___x_1504_ == 0)
{
lean_object* v___x_1505_; lean_object* v___x_1507_; 
lean_dec_ref_known(v_e_1317_, 1);
v___x_1505_ = l_Lean_Expr_sort___override(v_a_1498_);
if (v_isShared_1501_ == 0)
{
lean_ctor_set(v___x_1500_, 0, v___x_1505_);
v___x_1507_ = v___x_1500_;
goto v_reusejp_1506_;
}
else
{
lean_object* v_reuseFailAlloc_1508_; 
v_reuseFailAlloc_1508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1508_, 0, v___x_1505_);
v___x_1507_ = v_reuseFailAlloc_1508_;
goto v_reusejp_1506_;
}
v_reusejp_1506_:
{
return v___x_1507_;
}
}
else
{
lean_object* v___x_1510_; 
lean_dec(v_a_1498_);
if (v_isShared_1501_ == 0)
{
lean_ctor_set(v___x_1500_, 0, v_e_1317_);
v___x_1510_ = v___x_1500_;
goto v_reusejp_1509_;
}
else
{
lean_object* v_reuseFailAlloc_1511_; 
v_reuseFailAlloc_1511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1511_, 0, v_e_1317_);
v___x_1510_ = v_reuseFailAlloc_1511_;
goto v_reusejp_1509_;
}
v_reusejp_1509_:
{
return v___x_1510_;
}
}
}
}
else
{
lean_object* v_a_1513_; lean_object* v___x_1515_; uint8_t v_isShared_1516_; uint8_t v_isSharedCheck_1520_; 
lean_dec_ref_known(v_e_1317_, 1);
v_a_1513_ = lean_ctor_get(v___x_1497_, 0);
v_isSharedCheck_1520_ = !lean_is_exclusive(v___x_1497_);
if (v_isSharedCheck_1520_ == 0)
{
v___x_1515_ = v___x_1497_;
v_isShared_1516_ = v_isSharedCheck_1520_;
goto v_resetjp_1514_;
}
else
{
lean_inc(v_a_1513_);
lean_dec(v___x_1497_);
v___x_1515_ = lean_box(0);
v_isShared_1516_ = v_isSharedCheck_1520_;
goto v_resetjp_1514_;
}
v_resetjp_1514_:
{
lean_object* v___x_1518_; 
if (v_isShared_1516_ == 0)
{
v___x_1518_ = v___x_1515_;
goto v_reusejp_1517_;
}
else
{
lean_object* v_reuseFailAlloc_1519_; 
v_reuseFailAlloc_1519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1519_, 0, v_a_1513_);
v___x_1518_ = v_reuseFailAlloc_1519_;
goto v_reusejp_1517_;
}
v_reusejp_1517_:
{
return v___x_1518_;
}
}
}
}
case 4:
{
lean_object* v_declName_1521_; lean_object* v_us_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; 
v_declName_1521_ = lean_ctor_get(v_e_1317_, 0);
v_us_1522_ = lean_ctor_get(v_e_1317_, 1);
v___x_1523_ = lean_box(0);
lean_inc(v_us_1522_);
v___x_1524_ = l_List_mapM_loop___at___00Lean_Meta_Closure_collectExprAux_spec__2___redArg(v_us_1522_, v___x_1523_, v_a_1319_);
if (lean_obj_tag(v___x_1524_) == 0)
{
lean_object* v_a_1525_; lean_object* v___x_1527_; uint8_t v_isShared_1528_; uint8_t v_isSharedCheck_1537_; 
v_a_1525_ = lean_ctor_get(v___x_1524_, 0);
v_isSharedCheck_1537_ = !lean_is_exclusive(v___x_1524_);
if (v_isSharedCheck_1537_ == 0)
{
v___x_1527_ = v___x_1524_;
v_isShared_1528_ = v_isSharedCheck_1537_;
goto v_resetjp_1526_;
}
else
{
lean_inc(v_a_1525_);
lean_dec(v___x_1524_);
v___x_1527_ = lean_box(0);
v_isShared_1528_ = v_isSharedCheck_1537_;
goto v_resetjp_1526_;
}
v_resetjp_1526_:
{
uint8_t v___x_1529_; 
v___x_1529_ = l_ptrEqList___redArg(v_us_1522_, v_a_1525_);
if (v___x_1529_ == 0)
{
lean_object* v___x_1530_; lean_object* v___x_1532_; 
lean_inc(v_declName_1521_);
lean_dec_ref_known(v_e_1317_, 2);
v___x_1530_ = l_Lean_Expr_const___override(v_declName_1521_, v_a_1525_);
if (v_isShared_1528_ == 0)
{
lean_ctor_set(v___x_1527_, 0, v___x_1530_);
v___x_1532_ = v___x_1527_;
goto v_reusejp_1531_;
}
else
{
lean_object* v_reuseFailAlloc_1533_; 
v_reuseFailAlloc_1533_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1533_, 0, v___x_1530_);
v___x_1532_ = v_reuseFailAlloc_1533_;
goto v_reusejp_1531_;
}
v_reusejp_1531_:
{
return v___x_1532_;
}
}
else
{
lean_object* v___x_1535_; 
lean_dec(v_a_1525_);
if (v_isShared_1528_ == 0)
{
lean_ctor_set(v___x_1527_, 0, v_e_1317_);
v___x_1535_ = v___x_1527_;
goto v_reusejp_1534_;
}
else
{
lean_object* v_reuseFailAlloc_1536_; 
v_reuseFailAlloc_1536_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1536_, 0, v_e_1317_);
v___x_1535_ = v_reuseFailAlloc_1536_;
goto v_reusejp_1534_;
}
v_reusejp_1534_:
{
return v___x_1535_;
}
}
}
}
else
{
lean_object* v_a_1538_; lean_object* v___x_1540_; uint8_t v_isShared_1541_; uint8_t v_isSharedCheck_1545_; 
lean_dec_ref_known(v_e_1317_, 2);
v_a_1538_ = lean_ctor_get(v___x_1524_, 0);
v_isSharedCheck_1545_ = !lean_is_exclusive(v___x_1524_);
if (v_isSharedCheck_1545_ == 0)
{
v___x_1540_ = v___x_1524_;
v_isShared_1541_ = v_isSharedCheck_1545_;
goto v_resetjp_1539_;
}
else
{
lean_inc(v_a_1538_);
lean_dec(v___x_1524_);
v___x_1540_ = lean_box(0);
v_isShared_1541_ = v_isSharedCheck_1545_;
goto v_resetjp_1539_;
}
v_resetjp_1539_:
{
lean_object* v___x_1543_; 
if (v_isShared_1541_ == 0)
{
v___x_1543_ = v___x_1540_;
goto v_reusejp_1542_;
}
else
{
lean_object* v_reuseFailAlloc_1544_; 
v_reuseFailAlloc_1544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1544_, 0, v_a_1538_);
v___x_1543_ = v_reuseFailAlloc_1544_;
goto v_reusejp_1542_;
}
v_reusejp_1542_:
{
return v___x_1543_;
}
}
}
}
case 2:
{
lean_object* v_mvarId_1546_; lean_object* v___x_1547_; 
v_mvarId_1546_ = lean_ctor_get(v_e_1317_, 0);
lean_inc(v_mvarId_1546_);
v___x_1547_ = l_Lean_MVarId_getDecl(v_mvarId_1546_, v_a_1320_, v_a_1321_, v_a_1322_, v_a_1323_);
if (lean_obj_tag(v___x_1547_) == 0)
{
lean_object* v_a_1548_; lean_object* v_type_1549_; lean_object* v___x_1550_; 
v_a_1548_ = lean_ctor_get(v___x_1547_, 0);
lean_inc(v_a_1548_);
lean_dec_ref_known(v___x_1547_, 1);
v_type_1549_ = lean_ctor_get(v_a_1548_, 2);
lean_inc_ref_n(v_type_1549_, 2);
lean_dec(v_a_1548_);
v___x_1550_ = l_Lean_Meta_Closure_preprocess(v_type_1549_, v_a_1318_, v_a_1319_, v_a_1320_, v_a_1321_, v_a_1322_, v_a_1323_);
if (lean_obj_tag(v___x_1550_) == 0)
{
lean_object* v_a_1551_; lean_object* v___x_1552_; 
v_a_1551_ = lean_ctor_get(v___x_1550_, 0);
lean_inc(v_a_1551_);
lean_dec_ref_known(v___x_1550_, 1);
v___x_1552_ = l_Lean_Meta_Closure_collectExprAux___lam__0(v_a_1551_, v_a_1318_, v_a_1319_, v_a_1320_, v_a_1321_, v_a_1322_, v_a_1323_);
if (lean_obj_tag(v___x_1552_) == 0)
{
lean_object* v_a_1553_; lean_object* v___x_1554_; 
v_a_1553_ = lean_ctor_get(v___x_1552_, 0);
lean_inc(v_a_1553_);
lean_dec_ref_known(v___x_1552_, 1);
v___x_1554_ = l_Lean_mkFreshFVarId___at___00Lean_Meta_Closure_collectExprAux_spec__3(v_a_1318_, v_a_1319_, v_a_1320_, v_a_1321_, v_a_1322_, v_a_1323_);
if (lean_obj_tag(v___x_1554_) == 0)
{
lean_object* v_a_1555_; lean_object* v___x_1556_; 
v_a_1555_ = lean_ctor_get(v___x_1554_, 0);
lean_inc(v_a_1555_);
lean_dec_ref_known(v___x_1554_, 1);
v___x_1556_ = l_Lean_Meta_Closure_mkNextUserName___redArg(v_a_1319_);
if (lean_obj_tag(v___x_1556_) == 0)
{
lean_object* v_a_1557_; lean_object* v___x_1559_; uint8_t v_isShared_1560_; uint8_t v_isSharedCheck_1619_; 
v_a_1557_ = lean_ctor_get(v___x_1556_, 0);
v_isSharedCheck_1619_ = !lean_is_exclusive(v___x_1556_);
if (v_isSharedCheck_1619_ == 0)
{
v___x_1559_ = v___x_1556_;
v_isShared_1560_ = v_isSharedCheck_1619_;
goto v_resetjp_1558_;
}
else
{
lean_inc(v_a_1557_);
lean_dec(v___x_1556_);
v___x_1559_ = lean_box(0);
v_isShared_1560_ = v_isSharedCheck_1619_;
goto v_resetjp_1558_;
}
v_resetjp_1558_:
{
lean_object* v_e_x27_1562_; lean_object* v___y_1563_; lean_object* v___x_1595_; 
v___x_1595_ = l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__4___redArg(v_mvarId_1546_, v_a_1321_);
if (lean_obj_tag(v___x_1595_) == 0)
{
lean_object* v_a_1596_; 
v_a_1596_ = lean_ctor_get(v___x_1595_, 0);
lean_inc(v_a_1596_);
lean_dec_ref_known(v___x_1595_, 1);
if (lean_obj_tag(v_a_1596_) == 1)
{
lean_object* v_val_1597_; lean_object* v___x_1599_; uint8_t v_isShared_1600_; uint8_t v_isSharedCheck_1610_; 
v_val_1597_ = lean_ctor_get(v_a_1596_, 0);
v_isSharedCheck_1610_ = !lean_is_exclusive(v_a_1596_);
if (v_isSharedCheck_1610_ == 0)
{
v___x_1599_ = v_a_1596_;
v_isShared_1600_ = v_isSharedCheck_1610_;
goto v_resetjp_1598_;
}
else
{
lean_inc(v_val_1597_);
lean_dec(v_a_1596_);
v___x_1599_ = lean_box(0);
v_isShared_1600_ = v_isSharedCheck_1610_;
goto v_resetjp_1598_;
}
v_resetjp_1598_:
{
lean_object* v_fvars_1601_; lean_object* v___f_1602_; lean_object* v___x_1603_; lean_object* v___x_1605_; 
v_fvars_1601_ = lean_ctor_get(v_val_1597_, 0);
lean_inc_ref(v_fvars_1601_);
lean_dec(v_val_1597_);
v___f_1602_ = lean_alloc_closure((void*)(l_Lean_Meta_Closure_collectExprAux___lam__1___boxed), 10, 1);
lean_closure_set(v___f_1602_, 0, v_e_1317_);
v___x_1603_ = lean_array_get_size(v_fvars_1601_);
lean_dec_ref(v_fvars_1601_);
if (v_isShared_1600_ == 0)
{
lean_ctor_set(v___x_1599_, 0, v___x_1603_);
v___x_1605_ = v___x_1599_;
goto v_reusejp_1604_;
}
else
{
lean_object* v_reuseFailAlloc_1609_; 
v_reuseFailAlloc_1609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1609_, 0, v___x_1603_);
v___x_1605_ = v_reuseFailAlloc_1609_;
goto v_reusejp_1604_;
}
v_reusejp_1604_:
{
uint8_t v___x_1606_; lean_object* v___x_1607_; 
v___x_1606_ = 0;
v___x_1607_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Closure_collectExprAux_spec__5___redArg(v_type_1549_, v___x_1605_, v___f_1602_, v___x_1606_, v___x_1606_, v_a_1318_, v_a_1319_, v_a_1320_, v_a_1321_, v_a_1322_, v_a_1323_);
if (lean_obj_tag(v___x_1607_) == 0)
{
lean_object* v_a_1608_; 
v_a_1608_ = lean_ctor_get(v___x_1607_, 0);
lean_inc(v_a_1608_);
lean_dec_ref_known(v___x_1607_, 1);
v_e_x27_1562_ = v_a_1608_;
v___y_1563_ = v_a_1319_;
goto v___jp_1561_;
}
else
{
lean_del_object(v___x_1559_);
lean_dec(v_a_1557_);
lean_dec(v_a_1555_);
lean_dec(v_a_1553_);
return v___x_1607_;
}
}
}
}
else
{
lean_dec(v_a_1596_);
lean_dec_ref(v_type_1549_);
v_e_x27_1562_ = v_e_1317_;
v___y_1563_ = v_a_1319_;
goto v___jp_1561_;
}
}
else
{
lean_object* v_a_1611_; lean_object* v___x_1613_; uint8_t v_isShared_1614_; uint8_t v_isSharedCheck_1618_; 
lean_del_object(v___x_1559_);
lean_dec(v_a_1557_);
lean_dec(v_a_1555_);
lean_dec(v_a_1553_);
lean_dec_ref(v_type_1549_);
lean_dec_ref_known(v_e_1317_, 1);
v_a_1611_ = lean_ctor_get(v___x_1595_, 0);
v_isSharedCheck_1618_ = !lean_is_exclusive(v___x_1595_);
if (v_isSharedCheck_1618_ == 0)
{
v___x_1613_ = v___x_1595_;
v_isShared_1614_ = v_isSharedCheck_1618_;
goto v_resetjp_1612_;
}
else
{
lean_inc(v_a_1611_);
lean_dec(v___x_1595_);
v___x_1613_ = lean_box(0);
v_isShared_1614_ = v_isSharedCheck_1618_;
goto v_resetjp_1612_;
}
v_resetjp_1612_:
{
lean_object* v___x_1616_; 
if (v_isShared_1614_ == 0)
{
v___x_1616_ = v___x_1613_;
goto v_reusejp_1615_;
}
else
{
lean_object* v_reuseFailAlloc_1617_; 
v_reuseFailAlloc_1617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1617_, 0, v_a_1611_);
v___x_1616_ = v_reuseFailAlloc_1617_;
goto v_reusejp_1615_;
}
v_reusejp_1615_:
{
return v___x_1616_;
}
}
}
v___jp_1561_:
{
lean_object* v___x_1564_; lean_object* v_visitedLevel_1565_; lean_object* v_visitedExpr_1566_; lean_object* v_levelParams_1567_; lean_object* v_nextLevelIdx_1568_; lean_object* v_levelArgs_1569_; lean_object* v_newLocalDecls_1570_; lean_object* v_newLocalDeclsForMVars_1571_; lean_object* v_newLetDecls_1572_; lean_object* v_nextExprIdx_1573_; lean_object* v_exprMVarArgs_1574_; lean_object* v_exprFVarArgs_1575_; lean_object* v_toProcess_1576_; lean_object* v___x_1578_; uint8_t v_isShared_1579_; uint8_t v_isSharedCheck_1594_; 
v___x_1564_ = lean_st_ref_take(v___y_1563_);
v_visitedLevel_1565_ = lean_ctor_get(v___x_1564_, 0);
v_visitedExpr_1566_ = lean_ctor_get(v___x_1564_, 1);
v_levelParams_1567_ = lean_ctor_get(v___x_1564_, 2);
v_nextLevelIdx_1568_ = lean_ctor_get(v___x_1564_, 3);
v_levelArgs_1569_ = lean_ctor_get(v___x_1564_, 4);
v_newLocalDecls_1570_ = lean_ctor_get(v___x_1564_, 5);
v_newLocalDeclsForMVars_1571_ = lean_ctor_get(v___x_1564_, 6);
v_newLetDecls_1572_ = lean_ctor_get(v___x_1564_, 7);
v_nextExprIdx_1573_ = lean_ctor_get(v___x_1564_, 8);
v_exprMVarArgs_1574_ = lean_ctor_get(v___x_1564_, 9);
v_exprFVarArgs_1575_ = lean_ctor_get(v___x_1564_, 10);
v_toProcess_1576_ = lean_ctor_get(v___x_1564_, 11);
v_isSharedCheck_1594_ = !lean_is_exclusive(v___x_1564_);
if (v_isSharedCheck_1594_ == 0)
{
v___x_1578_ = v___x_1564_;
v_isShared_1579_ = v_isSharedCheck_1594_;
goto v_resetjp_1577_;
}
else
{
lean_inc(v_toProcess_1576_);
lean_inc(v_exprFVarArgs_1575_);
lean_inc(v_exprMVarArgs_1574_);
lean_inc(v_nextExprIdx_1573_);
lean_inc(v_newLetDecls_1572_);
lean_inc(v_newLocalDeclsForMVars_1571_);
lean_inc(v_newLocalDecls_1570_);
lean_inc(v_levelArgs_1569_);
lean_inc(v_nextLevelIdx_1568_);
lean_inc(v_levelParams_1567_);
lean_inc(v_visitedExpr_1566_);
lean_inc(v_visitedLevel_1565_);
lean_dec(v___x_1564_);
v___x_1578_ = lean_box(0);
v_isShared_1579_ = v_isSharedCheck_1594_;
goto v_resetjp_1577_;
}
v_resetjp_1577_:
{
lean_object* v___x_1580_; uint8_t v___x_1581_; uint8_t v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1587_; 
v___x_1580_ = lean_unsigned_to_nat(0u);
v___x_1581_ = 0;
v___x_1582_ = 0;
lean_inc(v_a_1555_);
v___x_1583_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_1583_, 0, v___x_1580_);
lean_ctor_set(v___x_1583_, 1, v_a_1555_);
lean_ctor_set(v___x_1583_, 2, v_a_1557_);
lean_ctor_set(v___x_1583_, 3, v_a_1553_);
lean_ctor_set_uint8(v___x_1583_, sizeof(void*)*4, v___x_1581_);
lean_ctor_set_uint8(v___x_1583_, sizeof(void*)*4 + 1, v___x_1582_);
v___x_1584_ = lean_array_push(v_newLocalDeclsForMVars_1571_, v___x_1583_);
v___x_1585_ = lean_array_push(v_exprMVarArgs_1574_, v_e_x27_1562_);
if (v_isShared_1579_ == 0)
{
lean_ctor_set(v___x_1578_, 9, v___x_1585_);
lean_ctor_set(v___x_1578_, 6, v___x_1584_);
v___x_1587_ = v___x_1578_;
goto v_reusejp_1586_;
}
else
{
lean_object* v_reuseFailAlloc_1593_; 
v_reuseFailAlloc_1593_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_1593_, 0, v_visitedLevel_1565_);
lean_ctor_set(v_reuseFailAlloc_1593_, 1, v_visitedExpr_1566_);
lean_ctor_set(v_reuseFailAlloc_1593_, 2, v_levelParams_1567_);
lean_ctor_set(v_reuseFailAlloc_1593_, 3, v_nextLevelIdx_1568_);
lean_ctor_set(v_reuseFailAlloc_1593_, 4, v_levelArgs_1569_);
lean_ctor_set(v_reuseFailAlloc_1593_, 5, v_newLocalDecls_1570_);
lean_ctor_set(v_reuseFailAlloc_1593_, 6, v___x_1584_);
lean_ctor_set(v_reuseFailAlloc_1593_, 7, v_newLetDecls_1572_);
lean_ctor_set(v_reuseFailAlloc_1593_, 8, v_nextExprIdx_1573_);
lean_ctor_set(v_reuseFailAlloc_1593_, 9, v___x_1585_);
lean_ctor_set(v_reuseFailAlloc_1593_, 10, v_exprFVarArgs_1575_);
lean_ctor_set(v_reuseFailAlloc_1593_, 11, v_toProcess_1576_);
v___x_1587_ = v_reuseFailAlloc_1593_;
goto v_reusejp_1586_;
}
v_reusejp_1586_:
{
lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1591_; 
v___x_1588_ = lean_st_ref_put(v___y_1563_, v___x_1587_);
v___x_1589_ = l_Lean_mkFVar(v_a_1555_);
if (v_isShared_1560_ == 0)
{
lean_ctor_set(v___x_1559_, 0, v___x_1589_);
v___x_1591_ = v___x_1559_;
goto v_reusejp_1590_;
}
else
{
lean_object* v_reuseFailAlloc_1592_; 
v_reuseFailAlloc_1592_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1592_, 0, v___x_1589_);
v___x_1591_ = v_reuseFailAlloc_1592_;
goto v_reusejp_1590_;
}
v_reusejp_1590_:
{
return v___x_1591_;
}
}
}
}
}
}
else
{
lean_object* v_a_1620_; lean_object* v___x_1622_; uint8_t v_isShared_1623_; uint8_t v_isSharedCheck_1627_; 
lean_dec(v_a_1555_);
lean_dec(v_a_1553_);
lean_dec_ref(v_type_1549_);
lean_dec_ref_known(v_e_1317_, 1);
v_a_1620_ = lean_ctor_get(v___x_1556_, 0);
v_isSharedCheck_1627_ = !lean_is_exclusive(v___x_1556_);
if (v_isSharedCheck_1627_ == 0)
{
v___x_1622_ = v___x_1556_;
v_isShared_1623_ = v_isSharedCheck_1627_;
goto v_resetjp_1621_;
}
else
{
lean_inc(v_a_1620_);
lean_dec(v___x_1556_);
v___x_1622_ = lean_box(0);
v_isShared_1623_ = v_isSharedCheck_1627_;
goto v_resetjp_1621_;
}
v_resetjp_1621_:
{
lean_object* v___x_1625_; 
if (v_isShared_1623_ == 0)
{
v___x_1625_ = v___x_1622_;
goto v_reusejp_1624_;
}
else
{
lean_object* v_reuseFailAlloc_1626_; 
v_reuseFailAlloc_1626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1626_, 0, v_a_1620_);
v___x_1625_ = v_reuseFailAlloc_1626_;
goto v_reusejp_1624_;
}
v_reusejp_1624_:
{
return v___x_1625_;
}
}
}
}
else
{
lean_object* v_a_1628_; lean_object* v___x_1630_; uint8_t v_isShared_1631_; uint8_t v_isSharedCheck_1635_; 
lean_dec(v_a_1553_);
lean_dec_ref(v_type_1549_);
lean_dec_ref_known(v_e_1317_, 1);
v_a_1628_ = lean_ctor_get(v___x_1554_, 0);
v_isSharedCheck_1635_ = !lean_is_exclusive(v___x_1554_);
if (v_isSharedCheck_1635_ == 0)
{
v___x_1630_ = v___x_1554_;
v_isShared_1631_ = v_isSharedCheck_1635_;
goto v_resetjp_1629_;
}
else
{
lean_inc(v_a_1628_);
lean_dec(v___x_1554_);
v___x_1630_ = lean_box(0);
v_isShared_1631_ = v_isSharedCheck_1635_;
goto v_resetjp_1629_;
}
v_resetjp_1629_:
{
lean_object* v___x_1633_; 
if (v_isShared_1631_ == 0)
{
v___x_1633_ = v___x_1630_;
goto v_reusejp_1632_;
}
else
{
lean_object* v_reuseFailAlloc_1634_; 
v_reuseFailAlloc_1634_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1634_, 0, v_a_1628_);
v___x_1633_ = v_reuseFailAlloc_1634_;
goto v_reusejp_1632_;
}
v_reusejp_1632_:
{
return v___x_1633_;
}
}
}
}
else
{
lean_dec_ref(v_type_1549_);
lean_dec_ref_known(v_e_1317_, 1);
return v___x_1552_;
}
}
else
{
lean_dec_ref(v_type_1549_);
lean_dec_ref_known(v_e_1317_, 1);
return v___x_1550_;
}
}
else
{
lean_object* v_a_1636_; lean_object* v___x_1638_; uint8_t v_isShared_1639_; uint8_t v_isSharedCheck_1643_; 
lean_dec_ref_known(v_e_1317_, 1);
v_a_1636_ = lean_ctor_get(v___x_1547_, 0);
v_isSharedCheck_1643_ = !lean_is_exclusive(v___x_1547_);
if (v_isSharedCheck_1643_ == 0)
{
v___x_1638_ = v___x_1547_;
v_isShared_1639_ = v_isSharedCheck_1643_;
goto v_resetjp_1637_;
}
else
{
lean_inc(v_a_1636_);
lean_dec(v___x_1547_);
v___x_1638_ = lean_box(0);
v_isShared_1639_ = v_isSharedCheck_1643_;
goto v_resetjp_1637_;
}
v_resetjp_1637_:
{
lean_object* v___x_1641_; 
if (v_isShared_1639_ == 0)
{
v___x_1641_ = v___x_1638_;
goto v_reusejp_1640_;
}
else
{
lean_object* v_reuseFailAlloc_1642_; 
v_reuseFailAlloc_1642_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1642_, 0, v_a_1636_);
v___x_1641_ = v_reuseFailAlloc_1642_;
goto v_reusejp_1640_;
}
v_reusejp_1640_:
{
return v___x_1641_;
}
}
}
}
case 1:
{
lean_object* v_fvarId_1644_; uint8_t v___x_1645_; lean_object* v___x_1646_; 
v_fvarId_1644_ = lean_ctor_get(v_e_1317_, 0);
lean_inc_n(v_fvarId_1644_, 2);
lean_dec_ref_known(v_e_1317_, 1);
v___x_1645_ = 0;
v___x_1646_ = l_Lean_FVarId_getValue_x3f___redArg(v_fvarId_1644_, v___x_1645_, v_a_1320_, v_a_1322_, v_a_1323_);
if (lean_obj_tag(v___x_1646_) == 0)
{
lean_object* v_a_1647_; uint8_t v___y_1649_; lean_object* v___y_1650_; lean_object* v___y_1651_; lean_object* v___y_1652_; lean_object* v___y_1653_; lean_object* v___y_1654_; 
v_a_1647_ = lean_ctor_get(v___x_1646_, 0);
lean_inc(v_a_1647_);
lean_dec_ref_known(v___x_1646_, 1);
if (v_a_1318_ == 1)
{
if (lean_obj_tag(v_a_1647_) == 1)
{
lean_object* v_val_1684_; lean_object* v___x_1685_; 
lean_dec(v_fvarId_1644_);
v_val_1684_ = lean_ctor_get(v_a_1647_, 0);
lean_inc(v_val_1684_);
lean_dec_ref_known(v_a_1647_, 1);
v___x_1685_ = l_Lean_Meta_Closure_preprocess(v_val_1684_, v_a_1318_, v_a_1319_, v_a_1320_, v_a_1321_, v_a_1322_, v_a_1323_);
if (lean_obj_tag(v___x_1685_) == 0)
{
lean_object* v_a_1686_; lean_object* v___x_1687_; 
v_a_1686_ = lean_ctor_get(v___x_1685_, 0);
lean_inc(v_a_1686_);
lean_dec_ref_known(v___x_1685_, 1);
v___x_1687_ = l_Lean_Meta_Closure_collectExprAux___lam__0(v_a_1686_, v_a_1318_, v_a_1319_, v_a_1320_, v_a_1321_, v_a_1322_, v_a_1323_);
return v___x_1687_;
}
else
{
return v___x_1685_;
}
}
else
{
lean_dec(v_a_1647_);
v___y_1649_ = v_a_1318_;
v___y_1650_ = v_a_1319_;
v___y_1651_ = v_a_1320_;
v___y_1652_ = v_a_1321_;
v___y_1653_ = v_a_1322_;
v___y_1654_ = v_a_1323_;
goto v___jp_1648_;
}
}
else
{
lean_dec(v_a_1647_);
v___y_1649_ = v_a_1318_;
v___y_1650_ = v_a_1319_;
v___y_1651_ = v_a_1320_;
v___y_1652_ = v_a_1321_;
v___y_1653_ = v_a_1322_;
v___y_1654_ = v_a_1323_;
goto v___jp_1648_;
}
v___jp_1648_:
{
lean_object* v___x_1655_; 
v___x_1655_ = l_Lean_mkFreshFVarId___at___00Lean_Meta_Closure_collectExprAux_spec__3(v___y_1649_, v___y_1650_, v___y_1651_, v___y_1652_, v___y_1653_, v___y_1654_);
if (lean_obj_tag(v___x_1655_) == 0)
{
lean_object* v_a_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; 
v_a_1656_ = lean_ctor_get(v___x_1655_, 0);
lean_inc_n(v_a_1656_, 2);
lean_dec_ref_known(v___x_1655_, 1);
v___x_1657_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1657_, 0, v_fvarId_1644_);
lean_ctor_set(v___x_1657_, 1, v_a_1656_);
v___x_1658_ = l_Lean_Meta_Closure_pushToProcess___redArg(v___x_1657_, v___y_1650_);
if (lean_obj_tag(v___x_1658_) == 0)
{
lean_object* v___x_1660_; uint8_t v_isShared_1661_; uint8_t v_isSharedCheck_1666_; 
v_isSharedCheck_1666_ = !lean_is_exclusive(v___x_1658_);
if (v_isSharedCheck_1666_ == 0)
{
lean_object* v_unused_1667_; 
v_unused_1667_ = lean_ctor_get(v___x_1658_, 0);
lean_dec(v_unused_1667_);
v___x_1660_ = v___x_1658_;
v_isShared_1661_ = v_isSharedCheck_1666_;
goto v_resetjp_1659_;
}
else
{
lean_dec(v___x_1658_);
v___x_1660_ = lean_box(0);
v_isShared_1661_ = v_isSharedCheck_1666_;
goto v_resetjp_1659_;
}
v_resetjp_1659_:
{
lean_object* v___x_1662_; lean_object* v___x_1664_; 
v___x_1662_ = l_Lean_mkFVar(v_a_1656_);
if (v_isShared_1661_ == 0)
{
lean_ctor_set(v___x_1660_, 0, v___x_1662_);
v___x_1664_ = v___x_1660_;
goto v_reusejp_1663_;
}
else
{
lean_object* v_reuseFailAlloc_1665_; 
v_reuseFailAlloc_1665_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1665_, 0, v___x_1662_);
v___x_1664_ = v_reuseFailAlloc_1665_;
goto v_reusejp_1663_;
}
v_reusejp_1663_:
{
return v___x_1664_;
}
}
}
else
{
lean_object* v_a_1668_; lean_object* v___x_1670_; uint8_t v_isShared_1671_; uint8_t v_isSharedCheck_1675_; 
lean_dec(v_a_1656_);
v_a_1668_ = lean_ctor_get(v___x_1658_, 0);
v_isSharedCheck_1675_ = !lean_is_exclusive(v___x_1658_);
if (v_isSharedCheck_1675_ == 0)
{
v___x_1670_ = v___x_1658_;
v_isShared_1671_ = v_isSharedCheck_1675_;
goto v_resetjp_1669_;
}
else
{
lean_inc(v_a_1668_);
lean_dec(v___x_1658_);
v___x_1670_ = lean_box(0);
v_isShared_1671_ = v_isSharedCheck_1675_;
goto v_resetjp_1669_;
}
v_resetjp_1669_:
{
lean_object* v___x_1673_; 
if (v_isShared_1671_ == 0)
{
v___x_1673_ = v___x_1670_;
goto v_reusejp_1672_;
}
else
{
lean_object* v_reuseFailAlloc_1674_; 
v_reuseFailAlloc_1674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1674_, 0, v_a_1668_);
v___x_1673_ = v_reuseFailAlloc_1674_;
goto v_reusejp_1672_;
}
v_reusejp_1672_:
{
return v___x_1673_;
}
}
}
}
else
{
lean_object* v_a_1676_; lean_object* v___x_1678_; uint8_t v_isShared_1679_; uint8_t v_isSharedCheck_1683_; 
lean_dec(v_fvarId_1644_);
v_a_1676_ = lean_ctor_get(v___x_1655_, 0);
v_isSharedCheck_1683_ = !lean_is_exclusive(v___x_1655_);
if (v_isSharedCheck_1683_ == 0)
{
v___x_1678_ = v___x_1655_;
v_isShared_1679_ = v_isSharedCheck_1683_;
goto v_resetjp_1677_;
}
else
{
lean_inc(v_a_1676_);
lean_dec(v___x_1655_);
v___x_1678_ = lean_box(0);
v_isShared_1679_ = v_isSharedCheck_1683_;
goto v_resetjp_1677_;
}
v_resetjp_1677_:
{
lean_object* v___x_1681_; 
if (v_isShared_1679_ == 0)
{
v___x_1681_ = v___x_1678_;
goto v_reusejp_1680_;
}
else
{
lean_object* v_reuseFailAlloc_1682_; 
v_reuseFailAlloc_1682_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1682_, 0, v_a_1676_);
v___x_1681_ = v_reuseFailAlloc_1682_;
goto v_reusejp_1680_;
}
v_reusejp_1680_:
{
return v___x_1681_;
}
}
}
}
}
else
{
lean_object* v_a_1688_; lean_object* v___x_1690_; uint8_t v_isShared_1691_; uint8_t v_isSharedCheck_1695_; 
lean_dec(v_fvarId_1644_);
v_a_1688_ = lean_ctor_get(v___x_1646_, 0);
v_isSharedCheck_1695_ = !lean_is_exclusive(v___x_1646_);
if (v_isSharedCheck_1695_ == 0)
{
v___x_1690_ = v___x_1646_;
v_isShared_1691_ = v_isSharedCheck_1695_;
goto v_resetjp_1689_;
}
else
{
lean_inc(v_a_1688_);
lean_dec(v___x_1646_);
v___x_1690_ = lean_box(0);
v_isShared_1691_ = v_isSharedCheck_1695_;
goto v_resetjp_1689_;
}
v_resetjp_1689_:
{
lean_object* v___x_1693_; 
if (v_isShared_1691_ == 0)
{
v___x_1693_ = v___x_1690_;
goto v_reusejp_1692_;
}
else
{
lean_object* v_reuseFailAlloc_1694_; 
v_reuseFailAlloc_1694_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1694_, 0, v_a_1688_);
v___x_1693_ = v_reuseFailAlloc_1694_;
goto v_reusejp_1692_;
}
v_reusejp_1692_:
{
return v___x_1693_;
}
}
}
}
default: 
{
lean_object* v___x_1696_; 
v___x_1696_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1696_, 0, v_e_1317_);
return v___x_1696_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectExprAux___lam__0(lean_object* v_e_1697_, uint8_t v___y_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_){
_start:
{
uint8_t v___x_1748_; 
v___x_1748_ = l_Lean_Expr_hasLevelParam(v_e_1697_);
if (v___x_1748_ == 0)
{
uint8_t v___x_1749_; 
v___x_1749_ = l_Lean_Expr_hasFVar(v_e_1697_);
if (v___x_1749_ == 0)
{
uint8_t v___x_1750_; 
v___x_1750_ = l_Lean_Expr_hasMVar(v_e_1697_);
if (v___x_1750_ == 0)
{
lean_object* v___x_1751_; 
v___x_1751_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1751_, 0, v_e_1697_);
return v___x_1751_;
}
else
{
goto v___jp_1705_;
}
}
else
{
goto v___jp_1705_;
}
}
else
{
goto v___jp_1705_;
}
v___jp_1705_:
{
lean_object* v___x_1706_; lean_object* v_visitedExpr_1707_; lean_object* v___x_1708_; 
v___x_1706_ = lean_st_ref_get(v___y_1699_);
v_visitedExpr_1707_ = lean_ctor_get(v___x_1706_, 1);
lean_inc_ref(v_visitedExpr_1707_);
lean_dec(v___x_1706_);
v___x_1708_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0___redArg(v_visitedExpr_1707_, v_e_1697_);
lean_dec_ref(v_visitedExpr_1707_);
if (lean_obj_tag(v___x_1708_) == 0)
{
lean_object* v___x_1709_; 
lean_inc_ref(v_e_1697_);
v___x_1709_ = l_Lean_Meta_Closure_collectExprAux(v_e_1697_, v___y_1698_, v___y_1699_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_);
if (lean_obj_tag(v___x_1709_) == 0)
{
lean_object* v_a_1710_; lean_object* v___x_1712_; uint8_t v_isShared_1713_; uint8_t v_isSharedCheck_1739_; 
v_a_1710_ = lean_ctor_get(v___x_1709_, 0);
v_isSharedCheck_1739_ = !lean_is_exclusive(v___x_1709_);
if (v_isSharedCheck_1739_ == 0)
{
v___x_1712_ = v___x_1709_;
v_isShared_1713_ = v_isSharedCheck_1739_;
goto v_resetjp_1711_;
}
else
{
lean_inc(v_a_1710_);
lean_dec(v___x_1709_);
v___x_1712_ = lean_box(0);
v_isShared_1713_ = v_isSharedCheck_1739_;
goto v_resetjp_1711_;
}
v_resetjp_1711_:
{
lean_object* v___x_1714_; lean_object* v_visitedLevel_1715_; lean_object* v_visitedExpr_1716_; lean_object* v_levelParams_1717_; lean_object* v_nextLevelIdx_1718_; lean_object* v_levelArgs_1719_; lean_object* v_newLocalDecls_1720_; lean_object* v_newLocalDeclsForMVars_1721_; lean_object* v_newLetDecls_1722_; lean_object* v_nextExprIdx_1723_; lean_object* v_exprMVarArgs_1724_; lean_object* v_exprFVarArgs_1725_; lean_object* v_toProcess_1726_; lean_object* v___x_1728_; uint8_t v_isShared_1729_; uint8_t v_isSharedCheck_1738_; 
v___x_1714_ = lean_st_ref_take(v___y_1699_);
v_visitedLevel_1715_ = lean_ctor_get(v___x_1714_, 0);
v_visitedExpr_1716_ = lean_ctor_get(v___x_1714_, 1);
v_levelParams_1717_ = lean_ctor_get(v___x_1714_, 2);
v_nextLevelIdx_1718_ = lean_ctor_get(v___x_1714_, 3);
v_levelArgs_1719_ = lean_ctor_get(v___x_1714_, 4);
v_newLocalDecls_1720_ = lean_ctor_get(v___x_1714_, 5);
v_newLocalDeclsForMVars_1721_ = lean_ctor_get(v___x_1714_, 6);
v_newLetDecls_1722_ = lean_ctor_get(v___x_1714_, 7);
v_nextExprIdx_1723_ = lean_ctor_get(v___x_1714_, 8);
v_exprMVarArgs_1724_ = lean_ctor_get(v___x_1714_, 9);
v_exprFVarArgs_1725_ = lean_ctor_get(v___x_1714_, 10);
v_toProcess_1726_ = lean_ctor_get(v___x_1714_, 11);
v_isSharedCheck_1738_ = !lean_is_exclusive(v___x_1714_);
if (v_isSharedCheck_1738_ == 0)
{
v___x_1728_ = v___x_1714_;
v_isShared_1729_ = v_isSharedCheck_1738_;
goto v_resetjp_1727_;
}
else
{
lean_inc(v_toProcess_1726_);
lean_inc(v_exprFVarArgs_1725_);
lean_inc(v_exprMVarArgs_1724_);
lean_inc(v_nextExprIdx_1723_);
lean_inc(v_newLetDecls_1722_);
lean_inc(v_newLocalDeclsForMVars_1721_);
lean_inc(v_newLocalDecls_1720_);
lean_inc(v_levelArgs_1719_);
lean_inc(v_nextLevelIdx_1718_);
lean_inc(v_levelParams_1717_);
lean_inc(v_visitedExpr_1716_);
lean_inc(v_visitedLevel_1715_);
lean_dec(v___x_1714_);
v___x_1728_ = lean_box(0);
v_isShared_1729_ = v_isSharedCheck_1738_;
goto v_resetjp_1727_;
}
v_resetjp_1727_:
{
lean_object* v___x_1730_; lean_object* v___x_1732_; 
lean_inc(v_a_1710_);
v___x_1730_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1___redArg(v_visitedExpr_1716_, v_e_1697_, v_a_1710_);
if (v_isShared_1729_ == 0)
{
lean_ctor_set(v___x_1728_, 1, v___x_1730_);
v___x_1732_ = v___x_1728_;
goto v_reusejp_1731_;
}
else
{
lean_object* v_reuseFailAlloc_1737_; 
v_reuseFailAlloc_1737_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_1737_, 0, v_visitedLevel_1715_);
lean_ctor_set(v_reuseFailAlloc_1737_, 1, v___x_1730_);
lean_ctor_set(v_reuseFailAlloc_1737_, 2, v_levelParams_1717_);
lean_ctor_set(v_reuseFailAlloc_1737_, 3, v_nextLevelIdx_1718_);
lean_ctor_set(v_reuseFailAlloc_1737_, 4, v_levelArgs_1719_);
lean_ctor_set(v_reuseFailAlloc_1737_, 5, v_newLocalDecls_1720_);
lean_ctor_set(v_reuseFailAlloc_1737_, 6, v_newLocalDeclsForMVars_1721_);
lean_ctor_set(v_reuseFailAlloc_1737_, 7, v_newLetDecls_1722_);
lean_ctor_set(v_reuseFailAlloc_1737_, 8, v_nextExprIdx_1723_);
lean_ctor_set(v_reuseFailAlloc_1737_, 9, v_exprMVarArgs_1724_);
lean_ctor_set(v_reuseFailAlloc_1737_, 10, v_exprFVarArgs_1725_);
lean_ctor_set(v_reuseFailAlloc_1737_, 11, v_toProcess_1726_);
v___x_1732_ = v_reuseFailAlloc_1737_;
goto v_reusejp_1731_;
}
v_reusejp_1731_:
{
lean_object* v___x_1733_; lean_object* v___x_1735_; 
v___x_1733_ = lean_st_ref_put(v___y_1699_, v___x_1732_);
if (v_isShared_1713_ == 0)
{
v___x_1735_ = v___x_1712_;
goto v_reusejp_1734_;
}
else
{
lean_object* v_reuseFailAlloc_1736_; 
v_reuseFailAlloc_1736_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1736_, 0, v_a_1710_);
v___x_1735_ = v_reuseFailAlloc_1736_;
goto v_reusejp_1734_;
}
v_reusejp_1734_:
{
return v___x_1735_;
}
}
}
}
}
else
{
lean_dec_ref(v_e_1697_);
return v___x_1709_;
}
}
else
{
lean_object* v_val_1740_; lean_object* v___x_1742_; uint8_t v_isShared_1743_; uint8_t v_isSharedCheck_1747_; 
lean_dec_ref(v_e_1697_);
v_val_1740_ = lean_ctor_get(v___x_1708_, 0);
v_isSharedCheck_1747_ = !lean_is_exclusive(v___x_1708_);
if (v_isSharedCheck_1747_ == 0)
{
v___x_1742_ = v___x_1708_;
v_isShared_1743_ = v_isSharedCheck_1747_;
goto v_resetjp_1741_;
}
else
{
lean_inc(v_val_1740_);
lean_dec(v___x_1708_);
v___x_1742_ = lean_box(0);
v_isShared_1743_ = v_isSharedCheck_1747_;
goto v_resetjp_1741_;
}
v_resetjp_1741_:
{
lean_object* v___x_1745_; 
if (v_isShared_1743_ == 0)
{
lean_ctor_set_tag(v___x_1742_, 0);
v___x_1745_ = v___x_1742_;
goto v_reusejp_1744_;
}
else
{
lean_object* v_reuseFailAlloc_1746_; 
v_reuseFailAlloc_1746_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1746_, 0, v_val_1740_);
v___x_1745_ = v_reuseFailAlloc_1746_;
goto v_reusejp_1744_;
}
v_reusejp_1744_:
{
return v___x_1745_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectExprAux___lam__0___boxed(lean_object* v_e_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_, lean_object* v___y_1759_){
_start:
{
uint8_t v___y_18573__boxed_1760_; lean_object* v_res_1761_; 
v___y_18573__boxed_1760_ = lean_unbox(v___y_1753_);
v_res_1761_ = l_Lean_Meta_Closure_collectExprAux___lam__0(v_e_1752_, v___y_18573__boxed_1760_, v___y_1754_, v___y_1755_, v___y_1756_, v___y_1757_, v___y_1758_);
lean_dec(v___y_1758_);
lean_dec_ref(v___y_1757_);
lean_dec(v___y_1756_);
lean_dec_ref(v___y_1755_);
lean_dec(v___y_1754_);
return v_res_1761_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectExprAux___boxed(lean_object* v_e_1762_, lean_object* v_a_1763_, lean_object* v_a_1764_, lean_object* v_a_1765_, lean_object* v_a_1766_, lean_object* v_a_1767_, lean_object* v_a_1768_, lean_object* v_a_1769_){
_start:
{
uint8_t v_a_boxed_1770_; lean_object* v_res_1771_; 
v_a_boxed_1770_ = lean_unbox(v_a_1763_);
v_res_1771_ = l_Lean_Meta_Closure_collectExprAux(v_e_1762_, v_a_boxed_1770_, v_a_1764_, v_a_1765_, v_a_1766_, v_a_1767_, v_a_1768_);
lean_dec(v_a_1768_);
lean_dec_ref(v_a_1767_);
lean_dec(v_a_1766_);
lean_dec_ref(v_a_1765_);
lean_dec(v_a_1764_);
return v_res_1771_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0(lean_object* v_00_u03b2_1772_, lean_object* v_m_1773_, lean_object* v_a_1774_){
_start:
{
lean_object* v___x_1775_; 
v___x_1775_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0___redArg(v_m_1773_, v_a_1774_);
return v___x_1775_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0___boxed(lean_object* v_00_u03b2_1776_, lean_object* v_m_1777_, lean_object* v_a_1778_){
_start:
{
lean_object* v_res_1779_; 
v_res_1779_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0(v_00_u03b2_1776_, v_m_1777_, v_a_1778_);
lean_dec_ref(v_a_1778_);
lean_dec_ref(v_m_1777_);
return v_res_1779_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1(lean_object* v_00_u03b2_1780_, lean_object* v_m_1781_, lean_object* v_a_1782_, lean_object* v_b_1783_){
_start:
{
lean_object* v___x_1784_; 
v___x_1784_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1___redArg(v_m_1781_, v_a_1782_, v_b_1783_);
return v___x_1784_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Closure_collectExprAux_spec__2(lean_object* v_x_1785_, lean_object* v_x_1786_, uint8_t v___y_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_){
_start:
{
lean_object* v___x_1794_; 
v___x_1794_ = l_List_mapM_loop___at___00Lean_Meta_Closure_collectExprAux_spec__2___redArg(v_x_1785_, v_x_1786_, v___y_1788_);
return v___x_1794_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Closure_collectExprAux_spec__2___boxed(lean_object* v_x_1795_, lean_object* v_x_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_){
_start:
{
uint8_t v___y_19405__boxed_1804_; lean_object* v_res_1805_; 
v___y_19405__boxed_1804_ = lean_unbox(v___y_1797_);
v_res_1805_ = l_List_mapM_loop___at___00Lean_Meta_Closure_collectExprAux_spec__2(v_x_1795_, v_x_1796_, v___y_19405__boxed_1804_, v___y_1798_, v___y_1799_, v___y_1800_, v___y_1801_, v___y_1802_);
lean_dec(v___y_1802_);
lean_dec_ref(v___y_1801_);
lean_dec(v___y_1800_);
lean_dec_ref(v___y_1799_);
lean_dec(v___y_1798_);
return v_res_1805_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Closure_collectExprAux_spec__3_spec__7(uint8_t v___y_1806_, lean_object* v___y_1807_, lean_object* v___y_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_){
_start:
{
lean_object* v___x_1813_; 
v___x_1813_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Closure_collectExprAux_spec__3_spec__7___redArg(v___y_1811_);
return v___x_1813_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Closure_collectExprAux_spec__3_spec__7___boxed(lean_object* v___y_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_){
_start:
{
uint8_t v___y_19432__boxed_1821_; lean_object* v_res_1822_; 
v___y_19432__boxed_1821_ = lean_unbox(v___y_1814_);
v_res_1822_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Closure_collectExprAux_spec__3_spec__7(v___y_19432__boxed_1821_, v___y_1815_, v___y_1816_, v___y_1817_, v___y_1818_, v___y_1819_);
lean_dec(v___y_1819_);
lean_dec_ref(v___y_1818_);
lean_dec(v___y_1817_);
lean_dec_ref(v___y_1816_);
lean_dec(v___y_1815_);
return v_res_1822_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0_spec__0(lean_object* v_00_u03b2_1823_, lean_object* v_a_1824_, lean_object* v_x_1825_){
_start:
{
lean_object* v___x_1826_; 
v___x_1826_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0_spec__0___redArg(v_a_1824_, v_x_1825_);
return v___x_1826_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1827_, lean_object* v_a_1828_, lean_object* v_x_1829_){
_start:
{
lean_object* v_res_1830_; 
v_res_1830_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0_spec__0(v_00_u03b2_1827_, v_a_1828_, v_x_1829_);
lean_dec(v_x_1829_);
lean_dec_ref(v_a_1828_);
return v_res_1830_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__2(lean_object* v_00_u03b2_1831_, lean_object* v_a_1832_, lean_object* v_x_1833_){
_start:
{
uint8_t v___x_1834_; 
v___x_1834_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__2___redArg(v_a_1832_, v_x_1833_);
return v___x_1834_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1835_, lean_object* v_a_1836_, lean_object* v_x_1837_){
_start:
{
uint8_t v_res_1838_; lean_object* v_r_1839_; 
v_res_1838_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__2(v_00_u03b2_1835_, v_a_1836_, v_x_1837_);
lean_dec(v_x_1837_);
lean_dec_ref(v_a_1836_);
v_r_1839_ = lean_box(v_res_1838_);
return v_r_1839_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__3(lean_object* v_00_u03b2_1840_, lean_object* v_data_1841_){
_start:
{
lean_object* v___x_1842_; 
v___x_1842_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__3___redArg(v_data_1841_);
return v___x_1842_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__4(lean_object* v_00_u03b2_1843_, lean_object* v_a_1844_, lean_object* v_b_1845_, lean_object* v_x_1846_){
_start:
{
lean_object* v___x_1847_; 
v___x_1847_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__4___redArg(v_a_1844_, v_b_1845_, v_x_1846_);
return v___x_1847_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__3_spec__6(lean_object* v_00_u03b2_1848_, lean_object* v_i_1849_, lean_object* v_source_1850_, lean_object* v_target_1851_){
_start:
{
lean_object* v___x_1852_; 
v___x_1852_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__3_spec__6___redArg(v_i_1849_, v_source_1850_, v_target_1851_);
return v___x_1852_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__3_spec__6_spec__10(lean_object* v_00_u03b2_1853_, lean_object* v_x_1854_, lean_object* v_x_1855_){
_start:
{
lean_object* v___x_1856_; 
v___x_1856_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__3_spec__6_spec__10___redArg(v_x_1854_, v_x_1855_);
return v___x_1856_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectExpr(lean_object* v_e_1857_, uint8_t v_a_1858_, lean_object* v_a_1859_, lean_object* v_a_1860_, lean_object* v_a_1861_, lean_object* v_a_1862_, lean_object* v_a_1863_){
_start:
{
lean_object* v___x_1865_; 
v___x_1865_ = l_Lean_Meta_Closure_preprocess(v_e_1857_, v_a_1858_, v_a_1859_, v_a_1860_, v_a_1861_, v_a_1862_, v_a_1863_);
if (lean_obj_tag(v___x_1865_) == 0)
{
lean_object* v_a_1866_; uint8_t v___x_1910_; 
v_a_1866_ = lean_ctor_get(v___x_1865_, 0);
lean_inc(v_a_1866_);
v___x_1910_ = l_Lean_Expr_hasLevelParam(v_a_1866_);
if (v___x_1910_ == 0)
{
uint8_t v___x_1911_; 
v___x_1911_ = l_Lean_Expr_hasFVar(v_a_1866_);
if (v___x_1911_ == 0)
{
uint8_t v___x_1912_; 
v___x_1912_ = l_Lean_Expr_hasMVar(v_a_1866_);
if (v___x_1912_ == 0)
{
lean_dec(v_a_1866_);
return v___x_1865_;
}
else
{
lean_dec_ref_known(v___x_1865_, 1);
goto v___jp_1867_;
}
}
else
{
lean_dec_ref_known(v___x_1865_, 1);
goto v___jp_1867_;
}
}
else
{
lean_dec_ref_known(v___x_1865_, 1);
goto v___jp_1867_;
}
v___jp_1867_:
{
lean_object* v___x_1868_; lean_object* v_visitedExpr_1869_; lean_object* v___x_1870_; 
v___x_1868_ = lean_st_ref_get(v_a_1859_);
v_visitedExpr_1869_ = lean_ctor_get(v___x_1868_, 1);
lean_inc_ref(v_visitedExpr_1869_);
lean_dec(v___x_1868_);
v___x_1870_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0___redArg(v_visitedExpr_1869_, v_a_1866_);
lean_dec_ref(v_visitedExpr_1869_);
if (lean_obj_tag(v___x_1870_) == 0)
{
lean_object* v___x_1871_; 
lean_inc(v_a_1866_);
v___x_1871_ = l_Lean_Meta_Closure_collectExprAux(v_a_1866_, v_a_1858_, v_a_1859_, v_a_1860_, v_a_1861_, v_a_1862_, v_a_1863_);
if (lean_obj_tag(v___x_1871_) == 0)
{
lean_object* v_a_1872_; lean_object* v___x_1874_; uint8_t v_isShared_1875_; uint8_t v_isSharedCheck_1901_; 
v_a_1872_ = lean_ctor_get(v___x_1871_, 0);
v_isSharedCheck_1901_ = !lean_is_exclusive(v___x_1871_);
if (v_isSharedCheck_1901_ == 0)
{
v___x_1874_ = v___x_1871_;
v_isShared_1875_ = v_isSharedCheck_1901_;
goto v_resetjp_1873_;
}
else
{
lean_inc(v_a_1872_);
lean_dec(v___x_1871_);
v___x_1874_ = lean_box(0);
v_isShared_1875_ = v_isSharedCheck_1901_;
goto v_resetjp_1873_;
}
v_resetjp_1873_:
{
lean_object* v___x_1876_; lean_object* v_visitedLevel_1877_; lean_object* v_visitedExpr_1878_; lean_object* v_levelParams_1879_; lean_object* v_nextLevelIdx_1880_; lean_object* v_levelArgs_1881_; lean_object* v_newLocalDecls_1882_; lean_object* v_newLocalDeclsForMVars_1883_; lean_object* v_newLetDecls_1884_; lean_object* v_nextExprIdx_1885_; lean_object* v_exprMVarArgs_1886_; lean_object* v_exprFVarArgs_1887_; lean_object* v_toProcess_1888_; lean_object* v___x_1890_; uint8_t v_isShared_1891_; uint8_t v_isSharedCheck_1900_; 
v___x_1876_ = lean_st_ref_take(v_a_1859_);
v_visitedLevel_1877_ = lean_ctor_get(v___x_1876_, 0);
v_visitedExpr_1878_ = lean_ctor_get(v___x_1876_, 1);
v_levelParams_1879_ = lean_ctor_get(v___x_1876_, 2);
v_nextLevelIdx_1880_ = lean_ctor_get(v___x_1876_, 3);
v_levelArgs_1881_ = lean_ctor_get(v___x_1876_, 4);
v_newLocalDecls_1882_ = lean_ctor_get(v___x_1876_, 5);
v_newLocalDeclsForMVars_1883_ = lean_ctor_get(v___x_1876_, 6);
v_newLetDecls_1884_ = lean_ctor_get(v___x_1876_, 7);
v_nextExprIdx_1885_ = lean_ctor_get(v___x_1876_, 8);
v_exprMVarArgs_1886_ = lean_ctor_get(v___x_1876_, 9);
v_exprFVarArgs_1887_ = lean_ctor_get(v___x_1876_, 10);
v_toProcess_1888_ = lean_ctor_get(v___x_1876_, 11);
v_isSharedCheck_1900_ = !lean_is_exclusive(v___x_1876_);
if (v_isSharedCheck_1900_ == 0)
{
v___x_1890_ = v___x_1876_;
v_isShared_1891_ = v_isSharedCheck_1900_;
goto v_resetjp_1889_;
}
else
{
lean_inc(v_toProcess_1888_);
lean_inc(v_exprFVarArgs_1887_);
lean_inc(v_exprMVarArgs_1886_);
lean_inc(v_nextExprIdx_1885_);
lean_inc(v_newLetDecls_1884_);
lean_inc(v_newLocalDeclsForMVars_1883_);
lean_inc(v_newLocalDecls_1882_);
lean_inc(v_levelArgs_1881_);
lean_inc(v_nextLevelIdx_1880_);
lean_inc(v_levelParams_1879_);
lean_inc(v_visitedExpr_1878_);
lean_inc(v_visitedLevel_1877_);
lean_dec(v___x_1876_);
v___x_1890_ = lean_box(0);
v_isShared_1891_ = v_isSharedCheck_1900_;
goto v_resetjp_1889_;
}
v_resetjp_1889_:
{
lean_object* v___x_1892_; lean_object* v___x_1894_; 
lean_inc(v_a_1872_);
v___x_1892_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1___redArg(v_visitedExpr_1878_, v_a_1866_, v_a_1872_);
if (v_isShared_1891_ == 0)
{
lean_ctor_set(v___x_1890_, 1, v___x_1892_);
v___x_1894_ = v___x_1890_;
goto v_reusejp_1893_;
}
else
{
lean_object* v_reuseFailAlloc_1899_; 
v_reuseFailAlloc_1899_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_1899_, 0, v_visitedLevel_1877_);
lean_ctor_set(v_reuseFailAlloc_1899_, 1, v___x_1892_);
lean_ctor_set(v_reuseFailAlloc_1899_, 2, v_levelParams_1879_);
lean_ctor_set(v_reuseFailAlloc_1899_, 3, v_nextLevelIdx_1880_);
lean_ctor_set(v_reuseFailAlloc_1899_, 4, v_levelArgs_1881_);
lean_ctor_set(v_reuseFailAlloc_1899_, 5, v_newLocalDecls_1882_);
lean_ctor_set(v_reuseFailAlloc_1899_, 6, v_newLocalDeclsForMVars_1883_);
lean_ctor_set(v_reuseFailAlloc_1899_, 7, v_newLetDecls_1884_);
lean_ctor_set(v_reuseFailAlloc_1899_, 8, v_nextExprIdx_1885_);
lean_ctor_set(v_reuseFailAlloc_1899_, 9, v_exprMVarArgs_1886_);
lean_ctor_set(v_reuseFailAlloc_1899_, 10, v_exprFVarArgs_1887_);
lean_ctor_set(v_reuseFailAlloc_1899_, 11, v_toProcess_1888_);
v___x_1894_ = v_reuseFailAlloc_1899_;
goto v_reusejp_1893_;
}
v_reusejp_1893_:
{
lean_object* v___x_1895_; lean_object* v___x_1897_; 
v___x_1895_ = lean_st_ref_put(v_a_1859_, v___x_1894_);
if (v_isShared_1875_ == 0)
{
v___x_1897_ = v___x_1874_;
goto v_reusejp_1896_;
}
else
{
lean_object* v_reuseFailAlloc_1898_; 
v_reuseFailAlloc_1898_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1898_, 0, v_a_1872_);
v___x_1897_ = v_reuseFailAlloc_1898_;
goto v_reusejp_1896_;
}
v_reusejp_1896_:
{
return v___x_1897_;
}
}
}
}
}
else
{
lean_dec(v_a_1866_);
return v___x_1871_;
}
}
else
{
lean_object* v_val_1902_; lean_object* v___x_1904_; uint8_t v_isShared_1905_; uint8_t v_isSharedCheck_1909_; 
lean_dec(v_a_1866_);
v_val_1902_ = lean_ctor_get(v___x_1870_, 0);
v_isSharedCheck_1909_ = !lean_is_exclusive(v___x_1870_);
if (v_isSharedCheck_1909_ == 0)
{
v___x_1904_ = v___x_1870_;
v_isShared_1905_ = v_isSharedCheck_1909_;
goto v_resetjp_1903_;
}
else
{
lean_inc(v_val_1902_);
lean_dec(v___x_1870_);
v___x_1904_ = lean_box(0);
v_isShared_1905_ = v_isSharedCheck_1909_;
goto v_resetjp_1903_;
}
v_resetjp_1903_:
{
lean_object* v___x_1907_; 
if (v_isShared_1905_ == 0)
{
lean_ctor_set_tag(v___x_1904_, 0);
v___x_1907_ = v___x_1904_;
goto v_reusejp_1906_;
}
else
{
lean_object* v_reuseFailAlloc_1908_; 
v_reuseFailAlloc_1908_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1908_, 0, v_val_1902_);
v___x_1907_ = v_reuseFailAlloc_1908_;
goto v_reusejp_1906_;
}
v_reusejp_1906_:
{
return v___x_1907_;
}
}
}
}
}
else
{
return v___x_1865_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectExpr___boxed(lean_object* v_e_1913_, lean_object* v_a_1914_, lean_object* v_a_1915_, lean_object* v_a_1916_, lean_object* v_a_1917_, lean_object* v_a_1918_, lean_object* v_a_1919_, lean_object* v_a_1920_){
_start:
{
uint8_t v_a_boxed_1921_; lean_object* v_res_1922_; 
v_a_boxed_1921_ = lean_unbox(v_a_1914_);
v_res_1922_ = l_Lean_Meta_Closure_collectExpr(v_e_1913_, v_a_boxed_1921_, v_a_1915_, v_a_1916_, v_a_1917_, v_a_1918_, v_a_1919_);
lean_dec(v_a_1919_);
lean_dec_ref(v_a_1918_);
lean_dec(v_a_1917_);
lean_dec_ref(v_a_1916_);
lean_dec(v_a_1915_);
return v_res_1922_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pickNextToProcessAux(lean_object* v_lctx_1923_, lean_object* v_i_1924_, lean_object* v_toProcess_1925_, lean_object* v_elem_1926_){
_start:
{
lean_object* v___x_1927_; uint8_t v___x_1928_; 
v___x_1927_ = lean_array_get_size(v_toProcess_1925_);
v___x_1928_ = lean_nat_dec_lt(v_i_1924_, v___x_1927_);
if (v___x_1928_ == 0)
{
lean_object* v___x_1929_; 
lean_dec(v_i_1924_);
lean_dec_ref(v_lctx_1923_);
v___x_1929_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1929_, 0, v_elem_1926_);
lean_ctor_set(v___x_1929_, 1, v_toProcess_1925_);
return v___x_1929_;
}
else
{
lean_object* v_fvarId_1930_; lean_object* v_elem_x27_1931_; lean_object* v_fvarId_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; uint8_t v___x_1937_; 
v_fvarId_1930_ = lean_ctor_get(v_elem_1926_, 0);
v_elem_x27_1931_ = lean_array_fget_borrowed(v_toProcess_1925_, v_i_1924_);
v_fvarId_1932_ = lean_ctor_get(v_elem_x27_1931_, 0);
lean_inc(v_fvarId_1930_);
lean_inc_ref_n(v_lctx_1923_, 2);
v___x_1933_ = l_Lean_LocalContext_get_x21(v_lctx_1923_, v_fvarId_1930_);
v___x_1934_ = l_Lean_LocalDecl_index(v___x_1933_);
lean_dec_ref(v___x_1933_);
lean_inc(v_fvarId_1932_);
v___x_1935_ = l_Lean_LocalContext_get_x21(v_lctx_1923_, v_fvarId_1932_);
v___x_1936_ = l_Lean_LocalDecl_index(v___x_1935_);
lean_dec_ref(v___x_1935_);
v___x_1937_ = lean_nat_dec_lt(v___x_1934_, v___x_1936_);
lean_dec(v___x_1936_);
lean_dec(v___x_1934_);
if (v___x_1937_ == 0)
{
lean_object* v___x_1938_; lean_object* v___x_1939_; 
v___x_1938_ = lean_unsigned_to_nat(1u);
v___x_1939_ = lean_nat_add(v_i_1924_, v___x_1938_);
lean_dec(v_i_1924_);
v_i_1924_ = v___x_1939_;
goto _start;
}
else
{
lean_object* v___x_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; 
lean_inc(v_elem_x27_1931_);
v___x_1941_ = lean_unsigned_to_nat(1u);
v___x_1942_ = lean_nat_add(v_i_1924_, v___x_1941_);
v___x_1943_ = lean_array_fset(v_toProcess_1925_, v_i_1924_, v_elem_1926_);
lean_dec(v_i_1924_);
v_i_1924_ = v___x_1942_;
v_toProcess_1925_ = v___x_1943_;
v_elem_1926_ = v_elem_x27_1931_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pickNextToProcess_x3f___redArg(lean_object* v_a_1945_, lean_object* v_a_1946_){
_start:
{
lean_object* v___x_1948_; lean_object* v_toProcess_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; uint8_t v___x_1952_; 
v___x_1948_ = lean_st_ref_get(v_a_1945_);
v_toProcess_1949_ = lean_ctor_get(v___x_1948_, 11);
lean_inc_ref(v_toProcess_1949_);
lean_dec(v___x_1948_);
v___x_1950_ = lean_array_get_size(v_toProcess_1949_);
lean_dec_ref(v_toProcess_1949_);
v___x_1951_ = lean_unsigned_to_nat(0u);
v___x_1952_ = lean_nat_dec_eq(v___x_1950_, v___x_1951_);
if (v___x_1952_ == 0)
{
lean_object* v___x_1953_; lean_object* v_lctx_1954_; lean_object* v_visitedLevel_1955_; lean_object* v_visitedExpr_1956_; lean_object* v_levelParams_1957_; lean_object* v_nextLevelIdx_1958_; lean_object* v_levelArgs_1959_; lean_object* v_newLocalDecls_1960_; lean_object* v_newLocalDeclsForMVars_1961_; lean_object* v_newLetDecls_1962_; lean_object* v_nextExprIdx_1963_; lean_object* v_exprMVarArgs_1964_; lean_object* v_exprFVarArgs_1965_; lean_object* v_toProcess_1966_; lean_object* v___x_1968_; uint8_t v_isShared_1969_; uint8_t v_isSharedCheck_1985_; 
v___x_1953_ = lean_st_ref_take(v_a_1945_);
v_lctx_1954_ = lean_ctor_get(v_a_1946_, 2);
v_visitedLevel_1955_ = lean_ctor_get(v___x_1953_, 0);
v_visitedExpr_1956_ = lean_ctor_get(v___x_1953_, 1);
v_levelParams_1957_ = lean_ctor_get(v___x_1953_, 2);
v_nextLevelIdx_1958_ = lean_ctor_get(v___x_1953_, 3);
v_levelArgs_1959_ = lean_ctor_get(v___x_1953_, 4);
v_newLocalDecls_1960_ = lean_ctor_get(v___x_1953_, 5);
v_newLocalDeclsForMVars_1961_ = lean_ctor_get(v___x_1953_, 6);
v_newLetDecls_1962_ = lean_ctor_get(v___x_1953_, 7);
v_nextExprIdx_1963_ = lean_ctor_get(v___x_1953_, 8);
v_exprMVarArgs_1964_ = lean_ctor_get(v___x_1953_, 9);
v_exprFVarArgs_1965_ = lean_ctor_get(v___x_1953_, 10);
v_toProcess_1966_ = lean_ctor_get(v___x_1953_, 11);
v_isSharedCheck_1985_ = !lean_is_exclusive(v___x_1953_);
if (v_isSharedCheck_1985_ == 0)
{
v___x_1968_ = v___x_1953_;
v_isShared_1969_ = v_isSharedCheck_1985_;
goto v_resetjp_1967_;
}
else
{
lean_inc(v_toProcess_1966_);
lean_inc(v_exprFVarArgs_1965_);
lean_inc(v_exprMVarArgs_1964_);
lean_inc(v_nextExprIdx_1963_);
lean_inc(v_newLetDecls_1962_);
lean_inc(v_newLocalDeclsForMVars_1961_);
lean_inc(v_newLocalDecls_1960_);
lean_inc(v_levelArgs_1959_);
lean_inc(v_nextLevelIdx_1958_);
lean_inc(v_levelParams_1957_);
lean_inc(v_visitedExpr_1956_);
lean_inc(v_visitedLevel_1955_);
lean_dec(v___x_1953_);
v___x_1968_ = lean_box(0);
v_isShared_1969_ = v_isSharedCheck_1985_;
goto v_resetjp_1967_;
}
v_resetjp_1967_:
{
lean_object* v___x_1970_; lean_object* v___x_1971_; lean_object* v___x_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; lean_object* v_fst_1977_; lean_object* v_snd_1978_; lean_object* v___x_1980_; 
v___x_1970_ = ((lean_object*)(l_Lean_Meta_Closure_instInhabitedToProcessElement_default));
v___x_1971_ = lean_array_get_size(v_toProcess_1966_);
v___x_1972_ = lean_unsigned_to_nat(1u);
v___x_1973_ = lean_nat_sub(v___x_1971_, v___x_1972_);
v___x_1974_ = lean_array_get(v___x_1970_, v_toProcess_1966_, v___x_1973_);
lean_dec(v___x_1973_);
v___x_1975_ = lean_array_pop(v_toProcess_1966_);
lean_inc_ref(v_lctx_1954_);
v___x_1976_ = l_Lean_Meta_Closure_pickNextToProcessAux(v_lctx_1954_, v___x_1951_, v___x_1975_, v___x_1974_);
v_fst_1977_ = lean_ctor_get(v___x_1976_, 0);
lean_inc(v_fst_1977_);
v_snd_1978_ = lean_ctor_get(v___x_1976_, 1);
lean_inc(v_snd_1978_);
lean_dec_ref(v___x_1976_);
if (v_isShared_1969_ == 0)
{
lean_ctor_set(v___x_1968_, 11, v_snd_1978_);
v___x_1980_ = v___x_1968_;
goto v_reusejp_1979_;
}
else
{
lean_object* v_reuseFailAlloc_1984_; 
v_reuseFailAlloc_1984_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_1984_, 0, v_visitedLevel_1955_);
lean_ctor_set(v_reuseFailAlloc_1984_, 1, v_visitedExpr_1956_);
lean_ctor_set(v_reuseFailAlloc_1984_, 2, v_levelParams_1957_);
lean_ctor_set(v_reuseFailAlloc_1984_, 3, v_nextLevelIdx_1958_);
lean_ctor_set(v_reuseFailAlloc_1984_, 4, v_levelArgs_1959_);
lean_ctor_set(v_reuseFailAlloc_1984_, 5, v_newLocalDecls_1960_);
lean_ctor_set(v_reuseFailAlloc_1984_, 6, v_newLocalDeclsForMVars_1961_);
lean_ctor_set(v_reuseFailAlloc_1984_, 7, v_newLetDecls_1962_);
lean_ctor_set(v_reuseFailAlloc_1984_, 8, v_nextExprIdx_1963_);
lean_ctor_set(v_reuseFailAlloc_1984_, 9, v_exprMVarArgs_1964_);
lean_ctor_set(v_reuseFailAlloc_1984_, 10, v_exprFVarArgs_1965_);
lean_ctor_set(v_reuseFailAlloc_1984_, 11, v_snd_1978_);
v___x_1980_ = v_reuseFailAlloc_1984_;
goto v_reusejp_1979_;
}
v_reusejp_1979_:
{
lean_object* v___x_1981_; lean_object* v___x_1982_; lean_object* v___x_1983_; 
v___x_1981_ = lean_st_ref_put(v_a_1945_, v___x_1980_);
v___x_1982_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1982_, 0, v_fst_1977_);
v___x_1983_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1983_, 0, v___x_1982_);
return v___x_1983_;
}
}
}
else
{
lean_object* v___x_1986_; lean_object* v___x_1987_; 
v___x_1986_ = lean_box(0);
v___x_1987_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1987_, 0, v___x_1986_);
return v___x_1987_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pickNextToProcess_x3f___redArg___boxed(lean_object* v_a_1988_, lean_object* v_a_1989_, lean_object* v_a_1990_){
_start:
{
lean_object* v_res_1991_; 
v_res_1991_ = l_Lean_Meta_Closure_pickNextToProcess_x3f___redArg(v_a_1988_, v_a_1989_);
lean_dec_ref(v_a_1989_);
lean_dec(v_a_1988_);
return v_res_1991_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pickNextToProcess_x3f(uint8_t v_a_1992_, lean_object* v_a_1993_, lean_object* v_a_1994_, lean_object* v_a_1995_, lean_object* v_a_1996_, lean_object* v_a_1997_){
_start:
{
lean_object* v___x_1999_; 
v___x_1999_ = l_Lean_Meta_Closure_pickNextToProcess_x3f___redArg(v_a_1993_, v_a_1994_);
return v___x_1999_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pickNextToProcess_x3f___boxed(lean_object* v_a_2000_, lean_object* v_a_2001_, lean_object* v_a_2002_, lean_object* v_a_2003_, lean_object* v_a_2004_, lean_object* v_a_2005_, lean_object* v_a_2006_){
_start:
{
uint8_t v_a_boxed_2007_; lean_object* v_res_2008_; 
v_a_boxed_2007_ = lean_unbox(v_a_2000_);
v_res_2008_ = l_Lean_Meta_Closure_pickNextToProcess_x3f(v_a_boxed_2007_, v_a_2001_, v_a_2002_, v_a_2003_, v_a_2004_, v_a_2005_);
lean_dec(v_a_2005_);
lean_dec_ref(v_a_2004_);
lean_dec(v_a_2003_);
lean_dec_ref(v_a_2002_);
lean_dec(v_a_2001_);
return v_res_2008_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushFVarArg___redArg(lean_object* v_e_2009_, lean_object* v_a_2010_){
_start:
{
lean_object* v___x_2012_; lean_object* v_visitedLevel_2013_; lean_object* v_visitedExpr_2014_; lean_object* v_levelParams_2015_; lean_object* v_nextLevelIdx_2016_; lean_object* v_levelArgs_2017_; lean_object* v_newLocalDecls_2018_; lean_object* v_newLocalDeclsForMVars_2019_; lean_object* v_newLetDecls_2020_; lean_object* v_nextExprIdx_2021_; lean_object* v_exprMVarArgs_2022_; lean_object* v_exprFVarArgs_2023_; lean_object* v_toProcess_2024_; lean_object* v___x_2026_; uint8_t v_isShared_2027_; uint8_t v_isSharedCheck_2035_; 
v___x_2012_ = lean_st_ref_take(v_a_2010_);
v_visitedLevel_2013_ = lean_ctor_get(v___x_2012_, 0);
v_visitedExpr_2014_ = lean_ctor_get(v___x_2012_, 1);
v_levelParams_2015_ = lean_ctor_get(v___x_2012_, 2);
v_nextLevelIdx_2016_ = lean_ctor_get(v___x_2012_, 3);
v_levelArgs_2017_ = lean_ctor_get(v___x_2012_, 4);
v_newLocalDecls_2018_ = lean_ctor_get(v___x_2012_, 5);
v_newLocalDeclsForMVars_2019_ = lean_ctor_get(v___x_2012_, 6);
v_newLetDecls_2020_ = lean_ctor_get(v___x_2012_, 7);
v_nextExprIdx_2021_ = lean_ctor_get(v___x_2012_, 8);
v_exprMVarArgs_2022_ = lean_ctor_get(v___x_2012_, 9);
v_exprFVarArgs_2023_ = lean_ctor_get(v___x_2012_, 10);
v_toProcess_2024_ = lean_ctor_get(v___x_2012_, 11);
v_isSharedCheck_2035_ = !lean_is_exclusive(v___x_2012_);
if (v_isSharedCheck_2035_ == 0)
{
v___x_2026_ = v___x_2012_;
v_isShared_2027_ = v_isSharedCheck_2035_;
goto v_resetjp_2025_;
}
else
{
lean_inc(v_toProcess_2024_);
lean_inc(v_exprFVarArgs_2023_);
lean_inc(v_exprMVarArgs_2022_);
lean_inc(v_nextExprIdx_2021_);
lean_inc(v_newLetDecls_2020_);
lean_inc(v_newLocalDeclsForMVars_2019_);
lean_inc(v_newLocalDecls_2018_);
lean_inc(v_levelArgs_2017_);
lean_inc(v_nextLevelIdx_2016_);
lean_inc(v_levelParams_2015_);
lean_inc(v_visitedExpr_2014_);
lean_inc(v_visitedLevel_2013_);
lean_dec(v___x_2012_);
v___x_2026_ = lean_box(0);
v_isShared_2027_ = v_isSharedCheck_2035_;
goto v_resetjp_2025_;
}
v_resetjp_2025_:
{
lean_object* v___x_2028_; lean_object* v___x_2030_; 
v___x_2028_ = lean_array_push(v_exprFVarArgs_2023_, v_e_2009_);
if (v_isShared_2027_ == 0)
{
lean_ctor_set(v___x_2026_, 10, v___x_2028_);
v___x_2030_ = v___x_2026_;
goto v_reusejp_2029_;
}
else
{
lean_object* v_reuseFailAlloc_2034_; 
v_reuseFailAlloc_2034_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_2034_, 0, v_visitedLevel_2013_);
lean_ctor_set(v_reuseFailAlloc_2034_, 1, v_visitedExpr_2014_);
lean_ctor_set(v_reuseFailAlloc_2034_, 2, v_levelParams_2015_);
lean_ctor_set(v_reuseFailAlloc_2034_, 3, v_nextLevelIdx_2016_);
lean_ctor_set(v_reuseFailAlloc_2034_, 4, v_levelArgs_2017_);
lean_ctor_set(v_reuseFailAlloc_2034_, 5, v_newLocalDecls_2018_);
lean_ctor_set(v_reuseFailAlloc_2034_, 6, v_newLocalDeclsForMVars_2019_);
lean_ctor_set(v_reuseFailAlloc_2034_, 7, v_newLetDecls_2020_);
lean_ctor_set(v_reuseFailAlloc_2034_, 8, v_nextExprIdx_2021_);
lean_ctor_set(v_reuseFailAlloc_2034_, 9, v_exprMVarArgs_2022_);
lean_ctor_set(v_reuseFailAlloc_2034_, 10, v___x_2028_);
lean_ctor_set(v_reuseFailAlloc_2034_, 11, v_toProcess_2024_);
v___x_2030_ = v_reuseFailAlloc_2034_;
goto v_reusejp_2029_;
}
v_reusejp_2029_:
{
lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; 
v___x_2031_ = lean_st_ref_put(v_a_2010_, v___x_2030_);
v___x_2032_ = lean_box(0);
v___x_2033_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2033_, 0, v___x_2032_);
return v___x_2033_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushFVarArg___redArg___boxed(lean_object* v_e_2036_, lean_object* v_a_2037_, lean_object* v_a_2038_){
_start:
{
lean_object* v_res_2039_; 
v_res_2039_ = l_Lean_Meta_Closure_pushFVarArg___redArg(v_e_2036_, v_a_2037_);
lean_dec(v_a_2037_);
return v_res_2039_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushFVarArg(lean_object* v_e_2040_, uint8_t v_a_2041_, lean_object* v_a_2042_, lean_object* v_a_2043_, lean_object* v_a_2044_, lean_object* v_a_2045_, lean_object* v_a_2046_){
_start:
{
lean_object* v___x_2048_; 
v___x_2048_ = l_Lean_Meta_Closure_pushFVarArg___redArg(v_e_2040_, v_a_2042_);
return v___x_2048_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushFVarArg___boxed(lean_object* v_e_2049_, lean_object* v_a_2050_, lean_object* v_a_2051_, lean_object* v_a_2052_, lean_object* v_a_2053_, lean_object* v_a_2054_, lean_object* v_a_2055_, lean_object* v_a_2056_){
_start:
{
uint8_t v_a_boxed_2057_; lean_object* v_res_2058_; 
v_a_boxed_2057_ = lean_unbox(v_a_2050_);
v_res_2058_ = l_Lean_Meta_Closure_pushFVarArg(v_e_2049_, v_a_boxed_2057_, v_a_2051_, v_a_2052_, v_a_2053_, v_a_2054_, v_a_2055_);
lean_dec(v_a_2055_);
lean_dec_ref(v_a_2054_);
lean_dec(v_a_2053_);
lean_dec_ref(v_a_2052_);
lean_dec(v_a_2051_);
return v_res_2058_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushLocalDecl(lean_object* v_newFVarId_2059_, lean_object* v_userName_2060_, lean_object* v_type_2061_, uint8_t v_bi_2062_, uint8_t v_a_2063_, lean_object* v_a_2064_, lean_object* v_a_2065_, lean_object* v_a_2066_, lean_object* v_a_2067_, lean_object* v_a_2068_){
_start:
{
lean_object* v___x_2070_; 
v___x_2070_ = l_Lean_Meta_Closure_collectExpr(v_type_2061_, v_a_2063_, v_a_2064_, v_a_2065_, v_a_2066_, v_a_2067_, v_a_2068_);
if (lean_obj_tag(v___x_2070_) == 0)
{
lean_object* v_a_2071_; lean_object* v___x_2073_; uint8_t v_isShared_2074_; uint8_t v_isSharedCheck_2104_; 
v_a_2071_ = lean_ctor_get(v___x_2070_, 0);
v_isSharedCheck_2104_ = !lean_is_exclusive(v___x_2070_);
if (v_isSharedCheck_2104_ == 0)
{
v___x_2073_ = v___x_2070_;
v_isShared_2074_ = v_isSharedCheck_2104_;
goto v_resetjp_2072_;
}
else
{
lean_inc(v_a_2071_);
lean_dec(v___x_2070_);
v___x_2073_ = lean_box(0);
v_isShared_2074_ = v_isSharedCheck_2104_;
goto v_resetjp_2072_;
}
v_resetjp_2072_:
{
lean_object* v___x_2075_; lean_object* v_visitedLevel_2076_; lean_object* v_visitedExpr_2077_; lean_object* v_levelParams_2078_; lean_object* v_nextLevelIdx_2079_; lean_object* v_levelArgs_2080_; lean_object* v_newLocalDecls_2081_; lean_object* v_newLocalDeclsForMVars_2082_; lean_object* v_newLetDecls_2083_; lean_object* v_nextExprIdx_2084_; lean_object* v_exprMVarArgs_2085_; lean_object* v_exprFVarArgs_2086_; lean_object* v_toProcess_2087_; lean_object* v___x_2089_; uint8_t v_isShared_2090_; uint8_t v_isSharedCheck_2103_; 
v___x_2075_ = lean_st_ref_take(v_a_2064_);
v_visitedLevel_2076_ = lean_ctor_get(v___x_2075_, 0);
v_visitedExpr_2077_ = lean_ctor_get(v___x_2075_, 1);
v_levelParams_2078_ = lean_ctor_get(v___x_2075_, 2);
v_nextLevelIdx_2079_ = lean_ctor_get(v___x_2075_, 3);
v_levelArgs_2080_ = lean_ctor_get(v___x_2075_, 4);
v_newLocalDecls_2081_ = lean_ctor_get(v___x_2075_, 5);
v_newLocalDeclsForMVars_2082_ = lean_ctor_get(v___x_2075_, 6);
v_newLetDecls_2083_ = lean_ctor_get(v___x_2075_, 7);
v_nextExprIdx_2084_ = lean_ctor_get(v___x_2075_, 8);
v_exprMVarArgs_2085_ = lean_ctor_get(v___x_2075_, 9);
v_exprFVarArgs_2086_ = lean_ctor_get(v___x_2075_, 10);
v_toProcess_2087_ = lean_ctor_get(v___x_2075_, 11);
v_isSharedCheck_2103_ = !lean_is_exclusive(v___x_2075_);
if (v_isSharedCheck_2103_ == 0)
{
v___x_2089_ = v___x_2075_;
v_isShared_2090_ = v_isSharedCheck_2103_;
goto v_resetjp_2088_;
}
else
{
lean_inc(v_toProcess_2087_);
lean_inc(v_exprFVarArgs_2086_);
lean_inc(v_exprMVarArgs_2085_);
lean_inc(v_nextExprIdx_2084_);
lean_inc(v_newLetDecls_2083_);
lean_inc(v_newLocalDeclsForMVars_2082_);
lean_inc(v_newLocalDecls_2081_);
lean_inc(v_levelArgs_2080_);
lean_inc(v_nextLevelIdx_2079_);
lean_inc(v_levelParams_2078_);
lean_inc(v_visitedExpr_2077_);
lean_inc(v_visitedLevel_2076_);
lean_dec(v___x_2075_);
v___x_2089_ = lean_box(0);
v_isShared_2090_ = v_isSharedCheck_2103_;
goto v_resetjp_2088_;
}
v_resetjp_2088_:
{
lean_object* v___x_2091_; uint8_t v___x_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; lean_object* v___x_2096_; 
v___x_2091_ = lean_unsigned_to_nat(0u);
v___x_2092_ = 0;
v___x_2093_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2093_, 0, v___x_2091_);
lean_ctor_set(v___x_2093_, 1, v_newFVarId_2059_);
lean_ctor_set(v___x_2093_, 2, v_userName_2060_);
lean_ctor_set(v___x_2093_, 3, v_a_2071_);
lean_ctor_set_uint8(v___x_2093_, sizeof(void*)*4, v_bi_2062_);
lean_ctor_set_uint8(v___x_2093_, sizeof(void*)*4 + 1, v___x_2092_);
v___x_2094_ = lean_array_push(v_newLocalDecls_2081_, v___x_2093_);
if (v_isShared_2090_ == 0)
{
lean_ctor_set(v___x_2089_, 5, v___x_2094_);
v___x_2096_ = v___x_2089_;
goto v_reusejp_2095_;
}
else
{
lean_object* v_reuseFailAlloc_2102_; 
v_reuseFailAlloc_2102_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_2102_, 0, v_visitedLevel_2076_);
lean_ctor_set(v_reuseFailAlloc_2102_, 1, v_visitedExpr_2077_);
lean_ctor_set(v_reuseFailAlloc_2102_, 2, v_levelParams_2078_);
lean_ctor_set(v_reuseFailAlloc_2102_, 3, v_nextLevelIdx_2079_);
lean_ctor_set(v_reuseFailAlloc_2102_, 4, v_levelArgs_2080_);
lean_ctor_set(v_reuseFailAlloc_2102_, 5, v___x_2094_);
lean_ctor_set(v_reuseFailAlloc_2102_, 6, v_newLocalDeclsForMVars_2082_);
lean_ctor_set(v_reuseFailAlloc_2102_, 7, v_newLetDecls_2083_);
lean_ctor_set(v_reuseFailAlloc_2102_, 8, v_nextExprIdx_2084_);
lean_ctor_set(v_reuseFailAlloc_2102_, 9, v_exprMVarArgs_2085_);
lean_ctor_set(v_reuseFailAlloc_2102_, 10, v_exprFVarArgs_2086_);
lean_ctor_set(v_reuseFailAlloc_2102_, 11, v_toProcess_2087_);
v___x_2096_ = v_reuseFailAlloc_2102_;
goto v_reusejp_2095_;
}
v_reusejp_2095_:
{
lean_object* v___x_2097_; lean_object* v___x_2098_; lean_object* v___x_2100_; 
v___x_2097_ = lean_st_ref_put(v_a_2064_, v___x_2096_);
v___x_2098_ = lean_box(0);
if (v_isShared_2074_ == 0)
{
lean_ctor_set(v___x_2073_, 0, v___x_2098_);
v___x_2100_ = v___x_2073_;
goto v_reusejp_2099_;
}
else
{
lean_object* v_reuseFailAlloc_2101_; 
v_reuseFailAlloc_2101_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2101_, 0, v___x_2098_);
v___x_2100_ = v_reuseFailAlloc_2101_;
goto v_reusejp_2099_;
}
v_reusejp_2099_:
{
return v___x_2100_;
}
}
}
}
}
else
{
lean_object* v_a_2105_; lean_object* v___x_2107_; uint8_t v_isShared_2108_; uint8_t v_isSharedCheck_2112_; 
lean_dec(v_userName_2060_);
lean_dec(v_newFVarId_2059_);
v_a_2105_ = lean_ctor_get(v___x_2070_, 0);
v_isSharedCheck_2112_ = !lean_is_exclusive(v___x_2070_);
if (v_isSharedCheck_2112_ == 0)
{
v___x_2107_ = v___x_2070_;
v_isShared_2108_ = v_isSharedCheck_2112_;
goto v_resetjp_2106_;
}
else
{
lean_inc(v_a_2105_);
lean_dec(v___x_2070_);
v___x_2107_ = lean_box(0);
v_isShared_2108_ = v_isSharedCheck_2112_;
goto v_resetjp_2106_;
}
v_resetjp_2106_:
{
lean_object* v___x_2110_; 
if (v_isShared_2108_ == 0)
{
v___x_2110_ = v___x_2107_;
goto v_reusejp_2109_;
}
else
{
lean_object* v_reuseFailAlloc_2111_; 
v_reuseFailAlloc_2111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2111_, 0, v_a_2105_);
v___x_2110_ = v_reuseFailAlloc_2111_;
goto v_reusejp_2109_;
}
v_reusejp_2109_:
{
return v___x_2110_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushLocalDecl___boxed(lean_object* v_newFVarId_2113_, lean_object* v_userName_2114_, lean_object* v_type_2115_, lean_object* v_bi_2116_, lean_object* v_a_2117_, lean_object* v_a_2118_, lean_object* v_a_2119_, lean_object* v_a_2120_, lean_object* v_a_2121_, lean_object* v_a_2122_, lean_object* v_a_2123_){
_start:
{
uint8_t v_bi_boxed_2124_; uint8_t v_a_boxed_2125_; lean_object* v_res_2126_; 
v_bi_boxed_2124_ = lean_unbox(v_bi_2116_);
v_a_boxed_2125_ = lean_unbox(v_a_2117_);
v_res_2126_ = l_Lean_Meta_Closure_pushLocalDecl(v_newFVarId_2113_, v_userName_2114_, v_type_2115_, v_bi_boxed_2124_, v_a_boxed_2125_, v_a_2118_, v_a_2119_, v_a_2120_, v_a_2121_, v_a_2122_);
lean_dec(v_a_2122_);
lean_dec_ref(v_a_2121_);
lean_dec(v_a_2120_);
lean_dec_ref(v_a_2119_);
lean_dec(v_a_2118_);
return v_res_2126_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Closure_process_spec__0___redArg(lean_object* v_k_2127_, lean_object* v_t_2128_){
_start:
{
if (lean_obj_tag(v_t_2128_) == 0)
{
lean_object* v_k_2129_; lean_object* v_l_2130_; lean_object* v_r_2131_; uint8_t v___x_2132_; 
v_k_2129_ = lean_ctor_get(v_t_2128_, 1);
v_l_2130_ = lean_ctor_get(v_t_2128_, 3);
v_r_2131_ = lean_ctor_get(v_t_2128_, 4);
v___x_2132_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_2127_, v_k_2129_);
switch(v___x_2132_)
{
case 0:
{
v_t_2128_ = v_l_2130_;
goto _start;
}
case 1:
{
uint8_t v___x_2134_; 
v___x_2134_ = 1;
return v___x_2134_;
}
default: 
{
v_t_2128_ = v_r_2131_;
goto _start;
}
}
}
else
{
uint8_t v___x_2136_; 
v___x_2136_ = 0;
return v___x_2136_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Closure_process_spec__0___redArg___boxed(lean_object* v_k_2137_, lean_object* v_t_2138_){
_start:
{
uint8_t v_res_2139_; lean_object* v_r_2140_; 
v_res_2139_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Closure_process_spec__0___redArg(v_k_2137_, v_t_2138_);
lean_dec(v_t_2138_);
lean_dec(v_k_2137_);
v_r_2140_ = lean_box(v_res_2139_);
return v_r_2140_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Closure_process_spec__1(lean_object* v_newFVarId_2141_, lean_object* v_a_2142_, size_t v_sz_2143_, size_t v_i_2144_, lean_object* v_bs_2145_){
_start:
{
uint8_t v___x_2146_; 
v___x_2146_ = lean_usize_dec_lt(v_i_2144_, v_sz_2143_);
if (v___x_2146_ == 0)
{
lean_dec(v_newFVarId_2141_);
return v_bs_2145_;
}
else
{
lean_object* v_v_2147_; lean_object* v___x_2148_; lean_object* v_bs_x27_2149_; lean_object* v___x_2150_; size_t v___x_2151_; size_t v___x_2152_; lean_object* v___x_2153_; 
v_v_2147_ = lean_array_uget(v_bs_2145_, v_i_2144_);
v___x_2148_ = lean_unsigned_to_nat(0u);
v_bs_x27_2149_ = lean_array_uset(v_bs_2145_, v_i_2144_, v___x_2148_);
lean_inc(v_newFVarId_2141_);
v___x_2150_ = l_Lean_LocalDecl_replaceFVarId(v_newFVarId_2141_, v_a_2142_, v_v_2147_);
v___x_2151_ = ((size_t)1ULL);
v___x_2152_ = lean_usize_add(v_i_2144_, v___x_2151_);
v___x_2153_ = lean_array_uset(v_bs_x27_2149_, v_i_2144_, v___x_2150_);
v_i_2144_ = v___x_2152_;
v_bs_2145_ = v___x_2153_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Closure_process_spec__1___boxed(lean_object* v_newFVarId_2155_, lean_object* v_a_2156_, lean_object* v_sz_2157_, lean_object* v_i_2158_, lean_object* v_bs_2159_){
_start:
{
size_t v_sz_boxed_2160_; size_t v_i_boxed_2161_; lean_object* v_res_2162_; 
v_sz_boxed_2160_ = lean_unbox_usize(v_sz_2157_);
lean_dec(v_sz_2157_);
v_i_boxed_2161_ = lean_unbox_usize(v_i_2158_);
lean_dec(v_i_2158_);
v_res_2162_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Closure_process_spec__1(v_newFVarId_2155_, v_a_2156_, v_sz_boxed_2160_, v_i_boxed_2161_, v_bs_2159_);
lean_dec_ref(v_a_2156_);
return v_res_2162_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_process(uint8_t v_a_2163_, lean_object* v_a_2164_, lean_object* v_a_2165_, lean_object* v_a_2166_, lean_object* v_a_2167_, lean_object* v_a_2168_){
_start:
{
lean_object* v___x_2170_; 
v___x_2170_ = l_Lean_Meta_Closure_pickNextToProcess_x3f___redArg(v_a_2164_, v_a_2165_);
if (lean_obj_tag(v___x_2170_) == 0)
{
lean_object* v_a_2171_; lean_object* v___x_2173_; uint8_t v_isShared_2174_; uint8_t v_isSharedCheck_2298_; 
v_a_2171_ = lean_ctor_get(v___x_2170_, 0);
v_isSharedCheck_2298_ = !lean_is_exclusive(v___x_2170_);
if (v_isSharedCheck_2298_ == 0)
{
v___x_2173_ = v___x_2170_;
v_isShared_2174_ = v_isSharedCheck_2298_;
goto v_resetjp_2172_;
}
else
{
lean_inc(v_a_2171_);
lean_dec(v___x_2170_);
v___x_2173_ = lean_box(0);
v_isShared_2174_ = v_isSharedCheck_2298_;
goto v_resetjp_2172_;
}
v_resetjp_2172_:
{
if (lean_obj_tag(v_a_2171_) == 0)
{
lean_object* v___x_2175_; lean_object* v___x_2177_; 
v___x_2175_ = lean_box(0);
if (v_isShared_2174_ == 0)
{
lean_ctor_set(v___x_2173_, 0, v___x_2175_);
v___x_2177_ = v___x_2173_;
goto v_reusejp_2176_;
}
else
{
lean_object* v_reuseFailAlloc_2178_; 
v_reuseFailAlloc_2178_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2178_, 0, v___x_2175_);
v___x_2177_ = v_reuseFailAlloc_2178_;
goto v_reusejp_2176_;
}
v_reusejp_2176_:
{
return v___x_2177_;
}
}
else
{
lean_object* v_val_2179_; lean_object* v_fvarId_2180_; lean_object* v_newFVarId_2181_; lean_object* v___x_2182_; 
lean_del_object(v___x_2173_);
v_val_2179_ = lean_ctor_get(v_a_2171_, 0);
lean_inc(v_val_2179_);
lean_dec_ref_known(v_a_2171_, 1);
v_fvarId_2180_ = lean_ctor_get(v_val_2179_, 0);
lean_inc_n(v_fvarId_2180_, 2);
v_newFVarId_2181_ = lean_ctor_get(v_val_2179_, 1);
lean_inc(v_newFVarId_2181_);
lean_dec(v_val_2179_);
v___x_2182_ = l_Lean_FVarId_getDecl___redArg(v_fvarId_2180_, v_a_2165_, v_a_2167_, v_a_2168_);
if (lean_obj_tag(v___x_2182_) == 0)
{
lean_object* v_a_2183_; 
v_a_2183_ = lean_ctor_get(v___x_2182_, 0);
lean_inc(v_a_2183_);
lean_dec_ref_known(v___x_2182_, 1);
if (lean_obj_tag(v_a_2183_) == 0)
{
lean_object* v_userName_2184_; lean_object* v_type_2185_; uint8_t v_bi_2186_; lean_object* v___x_2187_; 
v_userName_2184_ = lean_ctor_get(v_a_2183_, 2);
lean_inc(v_userName_2184_);
v_type_2185_ = lean_ctor_get(v_a_2183_, 3);
lean_inc_ref(v_type_2185_);
v_bi_2186_ = lean_ctor_get_uint8(v_a_2183_, sizeof(void*)*4);
lean_dec_ref_known(v_a_2183_, 4);
v___x_2187_ = l_Lean_Meta_Closure_pushLocalDecl(v_newFVarId_2181_, v_userName_2184_, v_type_2185_, v_bi_2186_, v_a_2163_, v_a_2164_, v_a_2165_, v_a_2166_, v_a_2167_, v_a_2168_);
if (lean_obj_tag(v___x_2187_) == 0)
{
lean_object* v___x_2188_; lean_object* v___x_2189_; 
lean_dec_ref_known(v___x_2187_, 1);
v___x_2188_ = l_Lean_mkFVar(v_fvarId_2180_);
v___x_2189_ = l_Lean_Meta_Closure_pushFVarArg___redArg(v___x_2188_, v_a_2164_);
if (lean_obj_tag(v___x_2189_) == 0)
{
lean_dec_ref_known(v___x_2189_, 1);
goto _start;
}
else
{
return v___x_2189_;
}
}
else
{
lean_dec(v_fvarId_2180_);
return v___x_2187_;
}
}
else
{
lean_object* v_userName_2191_; lean_object* v_type_2192_; lean_object* v_value_2193_; uint8_t v_nondep_2194_; lean_object* v___x_2196_; uint8_t v_isShared_2197_; uint8_t v_isSharedCheck_2287_; 
v_userName_2191_ = lean_ctor_get(v_a_2183_, 2);
v_type_2192_ = lean_ctor_get(v_a_2183_, 3);
v_value_2193_ = lean_ctor_get(v_a_2183_, 4);
v_nondep_2194_ = lean_ctor_get_uint8(v_a_2183_, sizeof(void*)*5);
v_isSharedCheck_2287_ = !lean_is_exclusive(v_a_2183_);
if (v_isSharedCheck_2287_ == 0)
{
lean_object* v_unused_2288_; lean_object* v_unused_2289_; 
v_unused_2288_ = lean_ctor_get(v_a_2183_, 1);
lean_dec(v_unused_2288_);
v_unused_2289_ = lean_ctor_get(v_a_2183_, 0);
lean_dec(v_unused_2289_);
v___x_2196_ = v_a_2183_;
v_isShared_2197_ = v_isSharedCheck_2287_;
goto v_resetjp_2195_;
}
else
{
lean_inc(v_value_2193_);
lean_inc(v_type_2192_);
lean_inc(v_userName_2191_);
lean_dec(v_a_2183_);
v___x_2196_ = lean_box(0);
v_isShared_2197_ = v_isSharedCheck_2287_;
goto v_resetjp_2195_;
}
v_resetjp_2195_:
{
lean_object* v___x_2198_; 
v___x_2198_ = l_Lean_Meta_getZetaDeltaFVarIds___redArg(v_a_2166_);
if (lean_obj_tag(v___x_2198_) == 0)
{
lean_object* v_a_2199_; 
v_a_2199_ = lean_ctor_get(v___x_2198_, 0);
lean_inc(v_a_2199_);
lean_dec_ref_known(v___x_2198_, 1);
if (v_nondep_2194_ == 0)
{
uint8_t v___x_2206_; 
v___x_2206_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Closure_process_spec__0___redArg(v_fvarId_2180_, v_a_2199_);
lean_dec(v_a_2199_);
if (v___x_2206_ == 0)
{
lean_del_object(v___x_2196_);
lean_dec_ref(v_value_2193_);
goto v___jp_2200_;
}
else
{
lean_object* v___x_2207_; 
lean_dec(v_fvarId_2180_);
v___x_2207_ = l_Lean_Meta_Closure_collectExpr(v_type_2192_, v_a_2163_, v_a_2164_, v_a_2165_, v_a_2166_, v_a_2167_, v_a_2168_);
if (lean_obj_tag(v___x_2207_) == 0)
{
lean_object* v_a_2208_; lean_object* v___x_2209_; 
v_a_2208_ = lean_ctor_get(v___x_2207_, 0);
lean_inc(v_a_2208_);
lean_dec_ref_known(v___x_2207_, 1);
v___x_2209_ = l_Lean_Meta_Closure_collectExpr(v_value_2193_, v_a_2163_, v_a_2164_, v_a_2165_, v_a_2166_, v_a_2167_, v_a_2168_);
if (lean_obj_tag(v___x_2209_) == 0)
{
lean_object* v_a_2210_; lean_object* v___x_2211_; lean_object* v_visitedLevel_2212_; lean_object* v_visitedExpr_2213_; lean_object* v_levelParams_2214_; lean_object* v_nextLevelIdx_2215_; lean_object* v_levelArgs_2216_; lean_object* v_newLocalDecls_2217_; lean_object* v_newLocalDeclsForMVars_2218_; lean_object* v_newLetDecls_2219_; lean_object* v_nextExprIdx_2220_; lean_object* v_exprMVarArgs_2221_; lean_object* v_exprFVarArgs_2222_; lean_object* v_toProcess_2223_; lean_object* v___x_2225_; uint8_t v_isShared_2226_; uint8_t v_isSharedCheck_2262_; 
v_a_2210_ = lean_ctor_get(v___x_2209_, 0);
lean_inc(v_a_2210_);
lean_dec_ref_known(v___x_2209_, 1);
v___x_2211_ = lean_st_ref_take(v_a_2164_);
v_visitedLevel_2212_ = lean_ctor_get(v___x_2211_, 0);
v_visitedExpr_2213_ = lean_ctor_get(v___x_2211_, 1);
v_levelParams_2214_ = lean_ctor_get(v___x_2211_, 2);
v_nextLevelIdx_2215_ = lean_ctor_get(v___x_2211_, 3);
v_levelArgs_2216_ = lean_ctor_get(v___x_2211_, 4);
v_newLocalDecls_2217_ = lean_ctor_get(v___x_2211_, 5);
v_newLocalDeclsForMVars_2218_ = lean_ctor_get(v___x_2211_, 6);
v_newLetDecls_2219_ = lean_ctor_get(v___x_2211_, 7);
v_nextExprIdx_2220_ = lean_ctor_get(v___x_2211_, 8);
v_exprMVarArgs_2221_ = lean_ctor_get(v___x_2211_, 9);
v_exprFVarArgs_2222_ = lean_ctor_get(v___x_2211_, 10);
v_toProcess_2223_ = lean_ctor_get(v___x_2211_, 11);
v_isSharedCheck_2262_ = !lean_is_exclusive(v___x_2211_);
if (v_isSharedCheck_2262_ == 0)
{
v___x_2225_ = v___x_2211_;
v_isShared_2226_ = v_isSharedCheck_2262_;
goto v_resetjp_2224_;
}
else
{
lean_inc(v_toProcess_2223_);
lean_inc(v_exprFVarArgs_2222_);
lean_inc(v_exprMVarArgs_2221_);
lean_inc(v_nextExprIdx_2220_);
lean_inc(v_newLetDecls_2219_);
lean_inc(v_newLocalDeclsForMVars_2218_);
lean_inc(v_newLocalDecls_2217_);
lean_inc(v_levelArgs_2216_);
lean_inc(v_nextLevelIdx_2215_);
lean_inc(v_levelParams_2214_);
lean_inc(v_visitedExpr_2213_);
lean_inc(v_visitedLevel_2212_);
lean_dec(v___x_2211_);
v___x_2225_ = lean_box(0);
v_isShared_2226_ = v_isSharedCheck_2262_;
goto v_resetjp_2224_;
}
v_resetjp_2224_:
{
lean_object* v___x_2227_; uint8_t v___x_2228_; lean_object* v___x_2230_; 
v___x_2227_ = lean_unsigned_to_nat(0u);
v___x_2228_ = 0;
lean_inc(v_a_2210_);
lean_inc(v_newFVarId_2181_);
if (v_isShared_2197_ == 0)
{
lean_ctor_set(v___x_2196_, 4, v_a_2210_);
lean_ctor_set(v___x_2196_, 3, v_a_2208_);
lean_ctor_set(v___x_2196_, 1, v_newFVarId_2181_);
lean_ctor_set(v___x_2196_, 0, v___x_2227_);
v___x_2230_ = v___x_2196_;
goto v_reusejp_2229_;
}
else
{
lean_object* v_reuseFailAlloc_2261_; 
v_reuseFailAlloc_2261_ = lean_alloc_ctor(1, 5, 2);
lean_ctor_set(v_reuseFailAlloc_2261_, 0, v___x_2227_);
lean_ctor_set(v_reuseFailAlloc_2261_, 1, v_newFVarId_2181_);
lean_ctor_set(v_reuseFailAlloc_2261_, 2, v_userName_2191_);
lean_ctor_set(v_reuseFailAlloc_2261_, 3, v_a_2208_);
lean_ctor_set(v_reuseFailAlloc_2261_, 4, v_a_2210_);
lean_ctor_set_uint8(v_reuseFailAlloc_2261_, sizeof(void*)*5, v_nondep_2194_);
v___x_2230_ = v_reuseFailAlloc_2261_;
goto v_reusejp_2229_;
}
v_reusejp_2229_:
{
lean_object* v___x_2231_; lean_object* v___x_2233_; 
lean_ctor_set_uint8(v___x_2230_, sizeof(void*)*5 + 1, v___x_2228_);
v___x_2231_ = lean_array_push(v_newLetDecls_2219_, v___x_2230_);
if (v_isShared_2226_ == 0)
{
lean_ctor_set(v___x_2225_, 7, v___x_2231_);
v___x_2233_ = v___x_2225_;
goto v_reusejp_2232_;
}
else
{
lean_object* v_reuseFailAlloc_2260_; 
v_reuseFailAlloc_2260_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_2260_, 0, v_visitedLevel_2212_);
lean_ctor_set(v_reuseFailAlloc_2260_, 1, v_visitedExpr_2213_);
lean_ctor_set(v_reuseFailAlloc_2260_, 2, v_levelParams_2214_);
lean_ctor_set(v_reuseFailAlloc_2260_, 3, v_nextLevelIdx_2215_);
lean_ctor_set(v_reuseFailAlloc_2260_, 4, v_levelArgs_2216_);
lean_ctor_set(v_reuseFailAlloc_2260_, 5, v_newLocalDecls_2217_);
lean_ctor_set(v_reuseFailAlloc_2260_, 6, v_newLocalDeclsForMVars_2218_);
lean_ctor_set(v_reuseFailAlloc_2260_, 7, v___x_2231_);
lean_ctor_set(v_reuseFailAlloc_2260_, 8, v_nextExprIdx_2220_);
lean_ctor_set(v_reuseFailAlloc_2260_, 9, v_exprMVarArgs_2221_);
lean_ctor_set(v_reuseFailAlloc_2260_, 10, v_exprFVarArgs_2222_);
lean_ctor_set(v_reuseFailAlloc_2260_, 11, v_toProcess_2223_);
v___x_2233_ = v_reuseFailAlloc_2260_;
goto v_reusejp_2232_;
}
v_reusejp_2232_:
{
lean_object* v___x_2234_; lean_object* v___x_2235_; lean_object* v_visitedLevel_2236_; lean_object* v_visitedExpr_2237_; lean_object* v_levelParams_2238_; lean_object* v_nextLevelIdx_2239_; lean_object* v_levelArgs_2240_; lean_object* v_newLocalDecls_2241_; lean_object* v_newLocalDeclsForMVars_2242_; lean_object* v_newLetDecls_2243_; lean_object* v_nextExprIdx_2244_; lean_object* v_exprMVarArgs_2245_; lean_object* v_exprFVarArgs_2246_; lean_object* v_toProcess_2247_; lean_object* v___x_2249_; uint8_t v_isShared_2250_; uint8_t v_isSharedCheck_2259_; 
v___x_2234_ = lean_st_ref_put(v_a_2164_, v___x_2233_);
v___x_2235_ = lean_st_ref_take(v_a_2164_);
v_visitedLevel_2236_ = lean_ctor_get(v___x_2235_, 0);
v_visitedExpr_2237_ = lean_ctor_get(v___x_2235_, 1);
v_levelParams_2238_ = lean_ctor_get(v___x_2235_, 2);
v_nextLevelIdx_2239_ = lean_ctor_get(v___x_2235_, 3);
v_levelArgs_2240_ = lean_ctor_get(v___x_2235_, 4);
v_newLocalDecls_2241_ = lean_ctor_get(v___x_2235_, 5);
v_newLocalDeclsForMVars_2242_ = lean_ctor_get(v___x_2235_, 6);
v_newLetDecls_2243_ = lean_ctor_get(v___x_2235_, 7);
v_nextExprIdx_2244_ = lean_ctor_get(v___x_2235_, 8);
v_exprMVarArgs_2245_ = lean_ctor_get(v___x_2235_, 9);
v_exprFVarArgs_2246_ = lean_ctor_get(v___x_2235_, 10);
v_toProcess_2247_ = lean_ctor_get(v___x_2235_, 11);
v_isSharedCheck_2259_ = !lean_is_exclusive(v___x_2235_);
if (v_isSharedCheck_2259_ == 0)
{
v___x_2249_ = v___x_2235_;
v_isShared_2250_ = v_isSharedCheck_2259_;
goto v_resetjp_2248_;
}
else
{
lean_inc(v_toProcess_2247_);
lean_inc(v_exprFVarArgs_2246_);
lean_inc(v_exprMVarArgs_2245_);
lean_inc(v_nextExprIdx_2244_);
lean_inc(v_newLetDecls_2243_);
lean_inc(v_newLocalDeclsForMVars_2242_);
lean_inc(v_newLocalDecls_2241_);
lean_inc(v_levelArgs_2240_);
lean_inc(v_nextLevelIdx_2239_);
lean_inc(v_levelParams_2238_);
lean_inc(v_visitedExpr_2237_);
lean_inc(v_visitedLevel_2236_);
lean_dec(v___x_2235_);
v___x_2249_ = lean_box(0);
v_isShared_2250_ = v_isSharedCheck_2259_;
goto v_resetjp_2248_;
}
v_resetjp_2248_:
{
size_t v_sz_2251_; size_t v___x_2252_; lean_object* v___x_2253_; lean_object* v___x_2255_; 
v_sz_2251_ = lean_array_size(v_newLocalDecls_2241_);
v___x_2252_ = ((size_t)0ULL);
v___x_2253_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Closure_process_spec__1(v_newFVarId_2181_, v_a_2210_, v_sz_2251_, v___x_2252_, v_newLocalDecls_2241_);
lean_dec(v_a_2210_);
if (v_isShared_2250_ == 0)
{
lean_ctor_set(v___x_2249_, 5, v___x_2253_);
v___x_2255_ = v___x_2249_;
goto v_reusejp_2254_;
}
else
{
lean_object* v_reuseFailAlloc_2258_; 
v_reuseFailAlloc_2258_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_2258_, 0, v_visitedLevel_2236_);
lean_ctor_set(v_reuseFailAlloc_2258_, 1, v_visitedExpr_2237_);
lean_ctor_set(v_reuseFailAlloc_2258_, 2, v_levelParams_2238_);
lean_ctor_set(v_reuseFailAlloc_2258_, 3, v_nextLevelIdx_2239_);
lean_ctor_set(v_reuseFailAlloc_2258_, 4, v_levelArgs_2240_);
lean_ctor_set(v_reuseFailAlloc_2258_, 5, v___x_2253_);
lean_ctor_set(v_reuseFailAlloc_2258_, 6, v_newLocalDeclsForMVars_2242_);
lean_ctor_set(v_reuseFailAlloc_2258_, 7, v_newLetDecls_2243_);
lean_ctor_set(v_reuseFailAlloc_2258_, 8, v_nextExprIdx_2244_);
lean_ctor_set(v_reuseFailAlloc_2258_, 9, v_exprMVarArgs_2245_);
lean_ctor_set(v_reuseFailAlloc_2258_, 10, v_exprFVarArgs_2246_);
lean_ctor_set(v_reuseFailAlloc_2258_, 11, v_toProcess_2247_);
v___x_2255_ = v_reuseFailAlloc_2258_;
goto v_reusejp_2254_;
}
v_reusejp_2254_:
{
lean_object* v___x_2256_; 
v___x_2256_ = lean_st_ref_put(v_a_2164_, v___x_2255_);
goto _start;
}
}
}
}
}
}
else
{
lean_object* v_a_2263_; lean_object* v___x_2265_; uint8_t v_isShared_2266_; uint8_t v_isSharedCheck_2270_; 
lean_dec(v_a_2208_);
lean_del_object(v___x_2196_);
lean_dec(v_userName_2191_);
lean_dec(v_newFVarId_2181_);
v_a_2263_ = lean_ctor_get(v___x_2209_, 0);
v_isSharedCheck_2270_ = !lean_is_exclusive(v___x_2209_);
if (v_isSharedCheck_2270_ == 0)
{
v___x_2265_ = v___x_2209_;
v_isShared_2266_ = v_isSharedCheck_2270_;
goto v_resetjp_2264_;
}
else
{
lean_inc(v_a_2263_);
lean_dec(v___x_2209_);
v___x_2265_ = lean_box(0);
v_isShared_2266_ = v_isSharedCheck_2270_;
goto v_resetjp_2264_;
}
v_resetjp_2264_:
{
lean_object* v___x_2268_; 
if (v_isShared_2266_ == 0)
{
v___x_2268_ = v___x_2265_;
goto v_reusejp_2267_;
}
else
{
lean_object* v_reuseFailAlloc_2269_; 
v_reuseFailAlloc_2269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2269_, 0, v_a_2263_);
v___x_2268_ = v_reuseFailAlloc_2269_;
goto v_reusejp_2267_;
}
v_reusejp_2267_:
{
return v___x_2268_;
}
}
}
}
else
{
lean_object* v_a_2271_; lean_object* v___x_2273_; uint8_t v_isShared_2274_; uint8_t v_isSharedCheck_2278_; 
lean_del_object(v___x_2196_);
lean_dec_ref(v_value_2193_);
lean_dec(v_userName_2191_);
lean_dec(v_newFVarId_2181_);
v_a_2271_ = lean_ctor_get(v___x_2207_, 0);
v_isSharedCheck_2278_ = !lean_is_exclusive(v___x_2207_);
if (v_isSharedCheck_2278_ == 0)
{
v___x_2273_ = v___x_2207_;
v_isShared_2274_ = v_isSharedCheck_2278_;
goto v_resetjp_2272_;
}
else
{
lean_inc(v_a_2271_);
lean_dec(v___x_2207_);
v___x_2273_ = lean_box(0);
v_isShared_2274_ = v_isSharedCheck_2278_;
goto v_resetjp_2272_;
}
v_resetjp_2272_:
{
lean_object* v___x_2276_; 
if (v_isShared_2274_ == 0)
{
v___x_2276_ = v___x_2273_;
goto v_reusejp_2275_;
}
else
{
lean_object* v_reuseFailAlloc_2277_; 
v_reuseFailAlloc_2277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2277_, 0, v_a_2271_);
v___x_2276_ = v_reuseFailAlloc_2277_;
goto v_reusejp_2275_;
}
v_reusejp_2275_:
{
return v___x_2276_;
}
}
}
}
}
else
{
lean_dec(v_a_2199_);
lean_del_object(v___x_2196_);
lean_dec_ref(v_value_2193_);
goto v___jp_2200_;
}
v___jp_2200_:
{
uint8_t v___x_2201_; lean_object* v___x_2202_; 
v___x_2201_ = 0;
v___x_2202_ = l_Lean_Meta_Closure_pushLocalDecl(v_newFVarId_2181_, v_userName_2191_, v_type_2192_, v___x_2201_, v_a_2163_, v_a_2164_, v_a_2165_, v_a_2166_, v_a_2167_, v_a_2168_);
if (lean_obj_tag(v___x_2202_) == 0)
{
lean_object* v___x_2203_; lean_object* v___x_2204_; 
lean_dec_ref_known(v___x_2202_, 1);
v___x_2203_ = l_Lean_mkFVar(v_fvarId_2180_);
v___x_2204_ = l_Lean_Meta_Closure_pushFVarArg___redArg(v___x_2203_, v_a_2164_);
if (lean_obj_tag(v___x_2204_) == 0)
{
lean_dec_ref_known(v___x_2204_, 1);
goto _start;
}
else
{
return v___x_2204_;
}
}
else
{
lean_dec(v_fvarId_2180_);
return v___x_2202_;
}
}
}
else
{
lean_object* v_a_2279_; lean_object* v___x_2281_; uint8_t v_isShared_2282_; uint8_t v_isSharedCheck_2286_; 
lean_del_object(v___x_2196_);
lean_dec_ref(v_value_2193_);
lean_dec_ref(v_type_2192_);
lean_dec(v_userName_2191_);
lean_dec(v_newFVarId_2181_);
lean_dec(v_fvarId_2180_);
v_a_2279_ = lean_ctor_get(v___x_2198_, 0);
v_isSharedCheck_2286_ = !lean_is_exclusive(v___x_2198_);
if (v_isSharedCheck_2286_ == 0)
{
v___x_2281_ = v___x_2198_;
v_isShared_2282_ = v_isSharedCheck_2286_;
goto v_resetjp_2280_;
}
else
{
lean_inc(v_a_2279_);
lean_dec(v___x_2198_);
v___x_2281_ = lean_box(0);
v_isShared_2282_ = v_isSharedCheck_2286_;
goto v_resetjp_2280_;
}
v_resetjp_2280_:
{
lean_object* v___x_2284_; 
if (v_isShared_2282_ == 0)
{
v___x_2284_ = v___x_2281_;
goto v_reusejp_2283_;
}
else
{
lean_object* v_reuseFailAlloc_2285_; 
v_reuseFailAlloc_2285_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2285_, 0, v_a_2279_);
v___x_2284_ = v_reuseFailAlloc_2285_;
goto v_reusejp_2283_;
}
v_reusejp_2283_:
{
return v___x_2284_;
}
}
}
}
}
}
else
{
lean_object* v_a_2290_; lean_object* v___x_2292_; uint8_t v_isShared_2293_; uint8_t v_isSharedCheck_2297_; 
lean_dec(v_newFVarId_2181_);
lean_dec(v_fvarId_2180_);
v_a_2290_ = lean_ctor_get(v___x_2182_, 0);
v_isSharedCheck_2297_ = !lean_is_exclusive(v___x_2182_);
if (v_isSharedCheck_2297_ == 0)
{
v___x_2292_ = v___x_2182_;
v_isShared_2293_ = v_isSharedCheck_2297_;
goto v_resetjp_2291_;
}
else
{
lean_inc(v_a_2290_);
lean_dec(v___x_2182_);
v___x_2292_ = lean_box(0);
v_isShared_2293_ = v_isSharedCheck_2297_;
goto v_resetjp_2291_;
}
v_resetjp_2291_:
{
lean_object* v___x_2295_; 
if (v_isShared_2293_ == 0)
{
v___x_2295_ = v___x_2292_;
goto v_reusejp_2294_;
}
else
{
lean_object* v_reuseFailAlloc_2296_; 
v_reuseFailAlloc_2296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2296_, 0, v_a_2290_);
v___x_2295_ = v_reuseFailAlloc_2296_;
goto v_reusejp_2294_;
}
v_reusejp_2294_:
{
return v___x_2295_;
}
}
}
}
}
}
else
{
lean_object* v_a_2299_; lean_object* v___x_2301_; uint8_t v_isShared_2302_; uint8_t v_isSharedCheck_2306_; 
v_a_2299_ = lean_ctor_get(v___x_2170_, 0);
v_isSharedCheck_2306_ = !lean_is_exclusive(v___x_2170_);
if (v_isSharedCheck_2306_ == 0)
{
v___x_2301_ = v___x_2170_;
v_isShared_2302_ = v_isSharedCheck_2306_;
goto v_resetjp_2300_;
}
else
{
lean_inc(v_a_2299_);
lean_dec(v___x_2170_);
v___x_2301_ = lean_box(0);
v_isShared_2302_ = v_isSharedCheck_2306_;
goto v_resetjp_2300_;
}
v_resetjp_2300_:
{
lean_object* v___x_2304_; 
if (v_isShared_2302_ == 0)
{
v___x_2304_ = v___x_2301_;
goto v_reusejp_2303_;
}
else
{
lean_object* v_reuseFailAlloc_2305_; 
v_reuseFailAlloc_2305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2305_, 0, v_a_2299_);
v___x_2304_ = v_reuseFailAlloc_2305_;
goto v_reusejp_2303_;
}
v_reusejp_2303_:
{
return v___x_2304_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_process___boxed(lean_object* v_a_2307_, lean_object* v_a_2308_, lean_object* v_a_2309_, lean_object* v_a_2310_, lean_object* v_a_2311_, lean_object* v_a_2312_, lean_object* v_a_2313_){
_start:
{
uint8_t v_a_boxed_2314_; lean_object* v_res_2315_; 
v_a_boxed_2314_ = lean_unbox(v_a_2307_);
v_res_2315_ = l_Lean_Meta_Closure_process(v_a_boxed_2314_, v_a_2308_, v_a_2309_, v_a_2310_, v_a_2311_, v_a_2312_);
lean_dec(v_a_2312_);
lean_dec_ref(v_a_2311_);
lean_dec(v_a_2310_);
lean_dec_ref(v_a_2309_);
lean_dec(v_a_2308_);
return v_res_2315_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Closure_process_spec__0(lean_object* v_00_u03b2_2316_, lean_object* v_k_2317_, lean_object* v_t_2318_){
_start:
{
uint8_t v___x_2319_; 
v___x_2319_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Closure_process_spec__0___redArg(v_k_2317_, v_t_2318_);
return v___x_2319_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Closure_process_spec__0___boxed(lean_object* v_00_u03b2_2320_, lean_object* v_k_2321_, lean_object* v_t_2322_){
_start:
{
uint8_t v_res_2323_; lean_object* v_r_2324_; 
v_res_2323_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Closure_process_spec__0(v_00_u03b2_2320_, v_k_2321_, v_t_2322_);
lean_dec(v_t_2322_);
lean_dec(v_k_2321_);
v_r_2324_ = lean_box(v_res_2323_);
return v_r_2324_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkBinding___lam__0(lean_object* v_decls_2325_, lean_object* v_xs_2326_, uint8_t v_isLambda_2327_, lean_object* v_i_2328_, lean_object* v_x_2329_, lean_object* v_b_2330_){
_start:
{
lean_object* v_decl_2331_; 
v_decl_2331_ = lean_array_fget_borrowed(v_decls_2325_, v_i_2328_);
if (lean_obj_tag(v_decl_2331_) == 0)
{
lean_object* v_userName_2332_; lean_object* v_type_2333_; uint8_t v_bi_2334_; lean_object* v_ty_2335_; 
v_userName_2332_ = lean_ctor_get(v_decl_2331_, 2);
v_type_2333_ = lean_ctor_get(v_decl_2331_, 3);
v_bi_2334_ = lean_ctor_get_uint8(v_decl_2331_, sizeof(void*)*4);
v_ty_2335_ = lean_expr_abstract_range(v_type_2333_, v_i_2328_, v_xs_2326_);
if (v_isLambda_2327_ == 0)
{
lean_object* v___x_2336_; 
lean_inc(v_userName_2332_);
v___x_2336_ = l_Lean_mkForall(v_userName_2332_, v_bi_2334_, v_ty_2335_, v_b_2330_);
return v___x_2336_;
}
else
{
lean_object* v___x_2337_; 
lean_inc(v_userName_2332_);
v___x_2337_ = l_Lean_mkLambda(v_userName_2332_, v_bi_2334_, v_ty_2335_, v_b_2330_);
return v___x_2337_;
}
}
else
{
lean_object* v_userName_2338_; lean_object* v_type_2339_; lean_object* v_value_2340_; uint8_t v_nondep_2341_; lean_object* v___x_2342_; uint8_t v___x_2343_; 
v_userName_2338_ = lean_ctor_get(v_decl_2331_, 2);
v_type_2339_ = lean_ctor_get(v_decl_2331_, 3);
v_value_2340_ = lean_ctor_get(v_decl_2331_, 4);
v_nondep_2341_ = lean_ctor_get_uint8(v_decl_2331_, sizeof(void*)*5);
v___x_2342_ = lean_unsigned_to_nat(0u);
v___x_2343_ = lean_expr_has_loose_bvar(v_b_2330_, v___x_2342_);
if (v___x_2343_ == 0)
{
lean_object* v___x_2344_; lean_object* v___x_2345_; 
v___x_2344_ = lean_unsigned_to_nat(1u);
v___x_2345_ = lean_expr_lower_loose_bvars(v_b_2330_, v___x_2344_, v___x_2344_);
lean_dec_ref(v_b_2330_);
return v___x_2345_;
}
else
{
lean_object* v_ty_2346_; lean_object* v_val_2347_; lean_object* v___x_2348_; 
v_ty_2346_ = lean_expr_abstract_range(v_type_2339_, v_i_2328_, v_xs_2326_);
v_val_2347_ = lean_expr_abstract_range(v_value_2340_, v_i_2328_, v_xs_2326_);
lean_inc(v_userName_2338_);
v___x_2348_ = l_Lean_Expr_letE___override(v_userName_2338_, v_ty_2346_, v_val_2347_, v_b_2330_, v_nondep_2341_);
return v___x_2348_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkBinding___lam__0___boxed(lean_object* v_decls_2349_, lean_object* v_xs_2350_, lean_object* v_isLambda_2351_, lean_object* v_i_2352_, lean_object* v_x_2353_, lean_object* v_b_2354_){
_start:
{
uint8_t v_isLambda_boxed_2355_; lean_object* v_res_2356_; 
v_isLambda_boxed_2355_ = lean_unbox(v_isLambda_2351_);
v_res_2356_ = l_Lean_Meta_Closure_mkBinding___lam__0(v_decls_2349_, v_xs_2350_, v_isLambda_boxed_2355_, v_i_2352_, v_x_2353_, v_b_2354_);
lean_dec(v_i_2352_);
lean_dec_ref(v_xs_2350_);
lean_dec_ref(v_decls_2349_);
return v_res_2356_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkBinding(uint8_t v_isLambda_2377_, lean_object* v_decls_2378_, lean_object* v_b_2379_){
_start:
{
lean_object* v___f_2380_; lean_object* v___x_2381_; size_t v_sz_2382_; size_t v___x_2383_; lean_object* v_xs_2384_; lean_object* v___x_2385_; lean_object* v___f_2386_; lean_object* v_b_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; 
v___f_2380_ = ((lean_object*)(l_Lean_Meta_Closure_mkBinding___closed__0));
v___x_2381_ = ((lean_object*)(l_Lean_Meta_Closure_mkBinding___closed__10));
v_sz_2382_ = lean_array_size(v_decls_2378_);
v___x_2383_ = ((size_t)0ULL);
lean_inc_ref_n(v_decls_2378_, 2);
v_xs_2384_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2381_, v___f_2380_, v_sz_2382_, v___x_2383_, v_decls_2378_);
v___x_2385_ = lean_box(v_isLambda_2377_);
lean_inc(v_xs_2384_);
v___f_2386_ = lean_alloc_closure((void*)(l_Lean_Meta_Closure_mkBinding___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2386_, 0, v_decls_2378_);
lean_closure_set(v___f_2386_, 1, v_xs_2384_);
lean_closure_set(v___f_2386_, 2, v___x_2385_);
v_b_2387_ = lean_expr_abstract(v_b_2379_, v_xs_2384_);
lean_dec(v_xs_2384_);
v___x_2388_ = lean_array_get_size(v_decls_2378_);
lean_dec_ref(v_decls_2378_);
v___x_2389_ = l_Nat_foldRev___redArg(v___x_2388_, v___f_2386_, v_b_2387_);
return v___x_2389_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkBinding___boxed(lean_object* v_isLambda_2390_, lean_object* v_decls_2391_, lean_object* v_b_2392_){
_start:
{
uint8_t v_isLambda_boxed_2393_; lean_object* v_res_2394_; 
v_isLambda_boxed_2393_ = lean_unbox(v_isLambda_2390_);
v_res_2394_ = l_Lean_Meta_Closure_mkBinding(v_isLambda_boxed_2393_, v_decls_2391_, v_b_2392_);
lean_dec_ref(v_b_2392_);
return v_res_2394_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Closure_mkLambda_spec__0(size_t v_sz_2395_, size_t v_i_2396_, lean_object* v_bs_2397_){
_start:
{
uint8_t v___x_2398_; 
v___x_2398_ = lean_usize_dec_lt(v_i_2396_, v_sz_2395_);
if (v___x_2398_ == 0)
{
return v_bs_2397_;
}
else
{
lean_object* v_v_2399_; lean_object* v___x_2400_; lean_object* v_bs_x27_2401_; lean_object* v___x_2402_; size_t v___x_2403_; size_t v___x_2404_; lean_object* v___x_2405_; 
v_v_2399_ = lean_array_uget(v_bs_2397_, v_i_2396_);
v___x_2400_ = lean_unsigned_to_nat(0u);
v_bs_x27_2401_ = lean_array_uset(v_bs_2397_, v_i_2396_, v___x_2400_);
v___x_2402_ = l_Lean_LocalDecl_toExpr(v_v_2399_);
v___x_2403_ = ((size_t)1ULL);
v___x_2404_ = lean_usize_add(v_i_2396_, v___x_2403_);
v___x_2405_ = lean_array_uset(v_bs_x27_2401_, v_i_2396_, v___x_2402_);
v_i_2396_ = v___x_2404_;
v_bs_2397_ = v___x_2405_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Closure_mkLambda_spec__0___boxed(lean_object* v_sz_2407_, lean_object* v_i_2408_, lean_object* v_bs_2409_){
_start:
{
size_t v_sz_boxed_2410_; size_t v_i_boxed_2411_; lean_object* v_res_2412_; 
v_sz_boxed_2410_ = lean_unbox_usize(v_sz_2407_);
lean_dec(v_sz_2407_);
v_i_boxed_2411_ = lean_unbox_usize(v_i_2408_);
lean_dec(v_i_2408_);
v_res_2412_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Closure_mkLambda_spec__0(v_sz_boxed_2410_, v_i_boxed_2411_, v_bs_2409_);
return v_res_2412_;
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_Meta_Closure_mkLambda_spec__1_spec__1(lean_object* v_decls_2413_, lean_object* v_xs_2414_, lean_object* v_x_2415_, lean_object* v_x_2416_){
_start:
{
lean_object* v_zero_2417_; uint8_t v_isZero_2418_; 
v_zero_2417_ = lean_unsigned_to_nat(0u);
v_isZero_2418_ = lean_nat_dec_eq(v_x_2415_, v_zero_2417_);
if (v_isZero_2418_ == 1)
{
lean_dec(v_x_2415_);
return v_x_2416_;
}
else
{
lean_object* v_one_2419_; lean_object* v_n_2420_; lean_object* v_decl_2421_; 
v_one_2419_ = lean_unsigned_to_nat(1u);
v_n_2420_ = lean_nat_sub(v_x_2415_, v_one_2419_);
lean_dec(v_x_2415_);
v_decl_2421_ = lean_array_fget_borrowed(v_decls_2413_, v_n_2420_);
if (lean_obj_tag(v_decl_2421_) == 0)
{
lean_object* v_userName_2422_; lean_object* v_type_2423_; uint8_t v_bi_2424_; lean_object* v_ty_2425_; lean_object* v___x_2426_; 
v_userName_2422_ = lean_ctor_get(v_decl_2421_, 2);
v_type_2423_ = lean_ctor_get(v_decl_2421_, 3);
v_bi_2424_ = lean_ctor_get_uint8(v_decl_2421_, sizeof(void*)*4);
v_ty_2425_ = lean_expr_abstract_range(v_type_2423_, v_n_2420_, v_xs_2414_);
lean_inc(v_userName_2422_);
v___x_2426_ = l_Lean_mkLambda(v_userName_2422_, v_bi_2424_, v_ty_2425_, v_x_2416_);
v_x_2415_ = v_n_2420_;
v_x_2416_ = v___x_2426_;
goto _start;
}
else
{
lean_object* v_userName_2428_; lean_object* v_type_2429_; lean_object* v_value_2430_; uint8_t v_nondep_2431_; uint8_t v___x_2432_; 
v_userName_2428_ = lean_ctor_get(v_decl_2421_, 2);
v_type_2429_ = lean_ctor_get(v_decl_2421_, 3);
v_value_2430_ = lean_ctor_get(v_decl_2421_, 4);
v_nondep_2431_ = lean_ctor_get_uint8(v_decl_2421_, sizeof(void*)*5);
v___x_2432_ = lean_expr_has_loose_bvar(v_x_2416_, v_zero_2417_);
if (v___x_2432_ == 0)
{
lean_object* v___x_2433_; 
v___x_2433_ = lean_expr_lower_loose_bvars(v_x_2416_, v_one_2419_, v_one_2419_);
lean_dec_ref(v_x_2416_);
v_x_2415_ = v_n_2420_;
v_x_2416_ = v___x_2433_;
goto _start;
}
else
{
lean_object* v_ty_2435_; lean_object* v_val_2436_; lean_object* v___x_2437_; 
v_ty_2435_ = lean_expr_abstract_range(v_type_2429_, v_n_2420_, v_xs_2414_);
v_val_2436_ = lean_expr_abstract_range(v_value_2430_, v_n_2420_, v_xs_2414_);
lean_inc(v_userName_2428_);
v___x_2437_ = l_Lean_Expr_letE___override(v_userName_2428_, v_ty_2435_, v_val_2436_, v_x_2416_, v_nondep_2431_);
v_x_2415_ = v_n_2420_;
v_x_2416_ = v___x_2437_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_Meta_Closure_mkLambda_spec__1_spec__1___boxed(lean_object* v_decls_2439_, lean_object* v_xs_2440_, lean_object* v_x_2441_, lean_object* v_x_2442_){
_start:
{
lean_object* v_res_2443_; 
v_res_2443_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_Meta_Closure_mkLambda_spec__1_spec__1(v_decls_2439_, v_xs_2440_, v_x_2441_, v_x_2442_);
lean_dec_ref(v_xs_2440_);
lean_dec_ref(v_decls_2439_);
return v_res_2443_;
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Lean_Meta_Closure_mkLambda_spec__1(lean_object* v_decls_2444_, lean_object* v_xs_2445_, lean_object* v_x_2446_, lean_object* v_x_2447_){
_start:
{
lean_object* v_zero_2448_; uint8_t v_isZero_2449_; 
v_zero_2448_ = lean_unsigned_to_nat(0u);
v_isZero_2449_ = lean_nat_dec_eq(v_x_2446_, v_zero_2448_);
if (v_isZero_2449_ == 1)
{
return v_x_2447_;
}
else
{
lean_object* v_one_2450_; lean_object* v_n_2451_; lean_object* v_decl_2452_; 
v_one_2450_ = lean_unsigned_to_nat(1u);
v_n_2451_ = lean_nat_sub(v_x_2446_, v_one_2450_);
v_decl_2452_ = lean_array_fget_borrowed(v_decls_2444_, v_n_2451_);
if (lean_obj_tag(v_decl_2452_) == 0)
{
lean_object* v_userName_2453_; lean_object* v_type_2454_; uint8_t v_bi_2455_; lean_object* v_ty_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; 
v_userName_2453_ = lean_ctor_get(v_decl_2452_, 2);
v_type_2454_ = lean_ctor_get(v_decl_2452_, 3);
v_bi_2455_ = lean_ctor_get_uint8(v_decl_2452_, sizeof(void*)*4);
v_ty_2456_ = lean_expr_abstract_range(v_type_2454_, v_n_2451_, v_xs_2445_);
lean_inc(v_userName_2453_);
v___x_2457_ = l_Lean_mkLambda(v_userName_2453_, v_bi_2455_, v_ty_2456_, v_x_2447_);
v___x_2458_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_Meta_Closure_mkLambda_spec__1_spec__1(v_decls_2444_, v_xs_2445_, v_n_2451_, v___x_2457_);
return v___x_2458_;
}
else
{
lean_object* v_userName_2459_; lean_object* v_type_2460_; lean_object* v_value_2461_; uint8_t v_nondep_2462_; uint8_t v___x_2463_; 
v_userName_2459_ = lean_ctor_get(v_decl_2452_, 2);
v_type_2460_ = lean_ctor_get(v_decl_2452_, 3);
v_value_2461_ = lean_ctor_get(v_decl_2452_, 4);
v_nondep_2462_ = lean_ctor_get_uint8(v_decl_2452_, sizeof(void*)*5);
v___x_2463_ = lean_expr_has_loose_bvar(v_x_2447_, v_zero_2448_);
if (v___x_2463_ == 0)
{
lean_object* v___x_2464_; lean_object* v___x_2465_; 
v___x_2464_ = lean_expr_lower_loose_bvars(v_x_2447_, v_one_2450_, v_one_2450_);
lean_dec_ref(v_x_2447_);
v___x_2465_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_Meta_Closure_mkLambda_spec__1_spec__1(v_decls_2444_, v_xs_2445_, v_n_2451_, v___x_2464_);
return v___x_2465_;
}
else
{
lean_object* v_ty_2466_; lean_object* v_val_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; 
v_ty_2466_ = lean_expr_abstract_range(v_type_2460_, v_n_2451_, v_xs_2445_);
v_val_2467_ = lean_expr_abstract_range(v_value_2461_, v_n_2451_, v_xs_2445_);
lean_inc(v_userName_2459_);
v___x_2468_ = l_Lean_Expr_letE___override(v_userName_2459_, v_ty_2466_, v_val_2467_, v_x_2447_, v_nondep_2462_);
v___x_2469_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_Meta_Closure_mkLambda_spec__1_spec__1(v_decls_2444_, v_xs_2445_, v_n_2451_, v___x_2468_);
return v___x_2469_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Lean_Meta_Closure_mkLambda_spec__1___boxed(lean_object* v_decls_2470_, lean_object* v_xs_2471_, lean_object* v_x_2472_, lean_object* v_x_2473_){
_start:
{
lean_object* v_res_2474_; 
v_res_2474_ = l_Nat_foldRev___at___00Lean_Meta_Closure_mkLambda_spec__1(v_decls_2470_, v_xs_2471_, v_x_2472_, v_x_2473_);
lean_dec(v_x_2472_);
lean_dec_ref(v_xs_2471_);
lean_dec_ref(v_decls_2470_);
return v_res_2474_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkLambda(lean_object* v_decls_2475_, lean_object* v_b_2476_){
_start:
{
size_t v_sz_2477_; size_t v___x_2478_; lean_object* v_xs_2479_; lean_object* v_b_2480_; lean_object* v___x_2481_; lean_object* v___x_2482_; 
v_sz_2477_ = lean_array_size(v_decls_2475_);
v___x_2478_ = ((size_t)0ULL);
lean_inc_ref(v_decls_2475_);
v_xs_2479_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Closure_mkLambda_spec__0(v_sz_2477_, v___x_2478_, v_decls_2475_);
v_b_2480_ = lean_expr_abstract(v_b_2476_, v_xs_2479_);
v___x_2481_ = lean_array_get_size(v_decls_2475_);
v___x_2482_ = l_Nat_foldRev___at___00Lean_Meta_Closure_mkLambda_spec__1(v_decls_2475_, v_xs_2479_, v___x_2481_, v_b_2480_);
lean_dec_ref(v_xs_2479_);
lean_dec_ref(v_decls_2475_);
return v___x_2482_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkLambda___boxed(lean_object* v_decls_2483_, lean_object* v_b_2484_){
_start:
{
lean_object* v_res_2485_; 
v_res_2485_ = l_Lean_Meta_Closure_mkLambda(v_decls_2483_, v_b_2484_);
lean_dec_ref(v_b_2484_);
return v_res_2485_;
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_Meta_Closure_mkForall_spec__0_spec__0(lean_object* v_decls_2486_, lean_object* v_xs_2487_, lean_object* v_x_2488_, lean_object* v_x_2489_){
_start:
{
lean_object* v_zero_2490_; uint8_t v_isZero_2491_; 
v_zero_2490_ = lean_unsigned_to_nat(0u);
v_isZero_2491_ = lean_nat_dec_eq(v_x_2488_, v_zero_2490_);
if (v_isZero_2491_ == 1)
{
lean_dec(v_x_2488_);
return v_x_2489_;
}
else
{
lean_object* v_one_2492_; lean_object* v_n_2493_; lean_object* v_decl_2494_; 
v_one_2492_ = lean_unsigned_to_nat(1u);
v_n_2493_ = lean_nat_sub(v_x_2488_, v_one_2492_);
lean_dec(v_x_2488_);
v_decl_2494_ = lean_array_fget_borrowed(v_decls_2486_, v_n_2493_);
if (lean_obj_tag(v_decl_2494_) == 0)
{
lean_object* v_userName_2495_; lean_object* v_type_2496_; uint8_t v_bi_2497_; lean_object* v_ty_2498_; lean_object* v___x_2499_; 
v_userName_2495_ = lean_ctor_get(v_decl_2494_, 2);
v_type_2496_ = lean_ctor_get(v_decl_2494_, 3);
v_bi_2497_ = lean_ctor_get_uint8(v_decl_2494_, sizeof(void*)*4);
v_ty_2498_ = lean_expr_abstract_range(v_type_2496_, v_n_2493_, v_xs_2487_);
lean_inc(v_userName_2495_);
v___x_2499_ = l_Lean_mkForall(v_userName_2495_, v_bi_2497_, v_ty_2498_, v_x_2489_);
v_x_2488_ = v_n_2493_;
v_x_2489_ = v___x_2499_;
goto _start;
}
else
{
lean_object* v_userName_2501_; lean_object* v_type_2502_; lean_object* v_value_2503_; uint8_t v_nondep_2504_; uint8_t v___x_2505_; 
v_userName_2501_ = lean_ctor_get(v_decl_2494_, 2);
v_type_2502_ = lean_ctor_get(v_decl_2494_, 3);
v_value_2503_ = lean_ctor_get(v_decl_2494_, 4);
v_nondep_2504_ = lean_ctor_get_uint8(v_decl_2494_, sizeof(void*)*5);
v___x_2505_ = lean_expr_has_loose_bvar(v_x_2489_, v_zero_2490_);
if (v___x_2505_ == 0)
{
lean_object* v___x_2506_; 
v___x_2506_ = lean_expr_lower_loose_bvars(v_x_2489_, v_one_2492_, v_one_2492_);
lean_dec_ref(v_x_2489_);
v_x_2488_ = v_n_2493_;
v_x_2489_ = v___x_2506_;
goto _start;
}
else
{
lean_object* v_ty_2508_; lean_object* v_val_2509_; lean_object* v___x_2510_; 
v_ty_2508_ = lean_expr_abstract_range(v_type_2502_, v_n_2493_, v_xs_2487_);
v_val_2509_ = lean_expr_abstract_range(v_value_2503_, v_n_2493_, v_xs_2487_);
lean_inc(v_userName_2501_);
v___x_2510_ = l_Lean_Expr_letE___override(v_userName_2501_, v_ty_2508_, v_val_2509_, v_x_2489_, v_nondep_2504_);
v_x_2488_ = v_n_2493_;
v_x_2489_ = v___x_2510_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_Meta_Closure_mkForall_spec__0_spec__0___boxed(lean_object* v_decls_2512_, lean_object* v_xs_2513_, lean_object* v_x_2514_, lean_object* v_x_2515_){
_start:
{
lean_object* v_res_2516_; 
v_res_2516_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_Meta_Closure_mkForall_spec__0_spec__0(v_decls_2512_, v_xs_2513_, v_x_2514_, v_x_2515_);
lean_dec_ref(v_xs_2513_);
lean_dec_ref(v_decls_2512_);
return v_res_2516_;
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Lean_Meta_Closure_mkForall_spec__0(lean_object* v_decls_2517_, lean_object* v_xs_2518_, lean_object* v_x_2519_, lean_object* v_x_2520_){
_start:
{
lean_object* v_zero_2521_; uint8_t v_isZero_2522_; 
v_zero_2521_ = lean_unsigned_to_nat(0u);
v_isZero_2522_ = lean_nat_dec_eq(v_x_2519_, v_zero_2521_);
if (v_isZero_2522_ == 1)
{
return v_x_2520_;
}
else
{
lean_object* v_one_2523_; lean_object* v_n_2524_; lean_object* v_decl_2525_; 
v_one_2523_ = lean_unsigned_to_nat(1u);
v_n_2524_ = lean_nat_sub(v_x_2519_, v_one_2523_);
v_decl_2525_ = lean_array_fget_borrowed(v_decls_2517_, v_n_2524_);
if (lean_obj_tag(v_decl_2525_) == 0)
{
lean_object* v_userName_2526_; lean_object* v_type_2527_; uint8_t v_bi_2528_; lean_object* v_ty_2529_; lean_object* v___x_2530_; lean_object* v___x_2531_; 
v_userName_2526_ = lean_ctor_get(v_decl_2525_, 2);
v_type_2527_ = lean_ctor_get(v_decl_2525_, 3);
v_bi_2528_ = lean_ctor_get_uint8(v_decl_2525_, sizeof(void*)*4);
v_ty_2529_ = lean_expr_abstract_range(v_type_2527_, v_n_2524_, v_xs_2518_);
lean_inc(v_userName_2526_);
v___x_2530_ = l_Lean_mkForall(v_userName_2526_, v_bi_2528_, v_ty_2529_, v_x_2520_);
v___x_2531_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_Meta_Closure_mkForall_spec__0_spec__0(v_decls_2517_, v_xs_2518_, v_n_2524_, v___x_2530_);
return v___x_2531_;
}
else
{
lean_object* v_userName_2532_; lean_object* v_type_2533_; lean_object* v_value_2534_; uint8_t v_nondep_2535_; uint8_t v___x_2536_; 
v_userName_2532_ = lean_ctor_get(v_decl_2525_, 2);
v_type_2533_ = lean_ctor_get(v_decl_2525_, 3);
v_value_2534_ = lean_ctor_get(v_decl_2525_, 4);
v_nondep_2535_ = lean_ctor_get_uint8(v_decl_2525_, sizeof(void*)*5);
v___x_2536_ = lean_expr_has_loose_bvar(v_x_2520_, v_zero_2521_);
if (v___x_2536_ == 0)
{
lean_object* v___x_2537_; lean_object* v___x_2538_; 
v___x_2537_ = lean_expr_lower_loose_bvars(v_x_2520_, v_one_2523_, v_one_2523_);
lean_dec_ref(v_x_2520_);
v___x_2538_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_Meta_Closure_mkForall_spec__0_spec__0(v_decls_2517_, v_xs_2518_, v_n_2524_, v___x_2537_);
return v___x_2538_;
}
else
{
lean_object* v_ty_2539_; lean_object* v_val_2540_; lean_object* v___x_2541_; lean_object* v___x_2542_; 
v_ty_2539_ = lean_expr_abstract_range(v_type_2533_, v_n_2524_, v_xs_2518_);
v_val_2540_ = lean_expr_abstract_range(v_value_2534_, v_n_2524_, v_xs_2518_);
lean_inc(v_userName_2532_);
v___x_2541_ = l_Lean_Expr_letE___override(v_userName_2532_, v_ty_2539_, v_val_2540_, v_x_2520_, v_nondep_2535_);
v___x_2542_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_Meta_Closure_mkForall_spec__0_spec__0(v_decls_2517_, v_xs_2518_, v_n_2524_, v___x_2541_);
return v___x_2542_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Lean_Meta_Closure_mkForall_spec__0___boxed(lean_object* v_decls_2543_, lean_object* v_xs_2544_, lean_object* v_x_2545_, lean_object* v_x_2546_){
_start:
{
lean_object* v_res_2547_; 
v_res_2547_ = l_Nat_foldRev___at___00Lean_Meta_Closure_mkForall_spec__0(v_decls_2543_, v_xs_2544_, v_x_2545_, v_x_2546_);
lean_dec(v_x_2545_);
lean_dec_ref(v_xs_2544_);
lean_dec_ref(v_decls_2543_);
return v_res_2547_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkForall(lean_object* v_decls_2548_, lean_object* v_b_2549_){
_start:
{
size_t v_sz_2550_; size_t v___x_2551_; lean_object* v_xs_2552_; lean_object* v_b_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; 
v_sz_2550_ = lean_array_size(v_decls_2548_);
v___x_2551_ = ((size_t)0ULL);
lean_inc_ref(v_decls_2548_);
v_xs_2552_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Closure_mkLambda_spec__0(v_sz_2550_, v___x_2551_, v_decls_2548_);
v_b_2553_ = lean_expr_abstract(v_b_2549_, v_xs_2552_);
v___x_2554_ = lean_array_get_size(v_decls_2548_);
v___x_2555_ = l_Nat_foldRev___at___00Lean_Meta_Closure_mkForall_spec__0(v_decls_2548_, v_xs_2552_, v___x_2554_, v_b_2553_);
lean_dec_ref(v_xs_2552_);
lean_dec_ref(v_decls_2548_);
return v___x_2555_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkForall___boxed(lean_object* v_decls_2556_, lean_object* v_b_2557_){
_start:
{
lean_object* v_res_2558_; 
v_res_2558_ = l_Lean_Meta_Closure_mkForall(v_decls_2556_, v_b_2557_);
lean_dec_ref(v_b_2557_);
return v_res_2558_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkValueTypeClosureAux___lam__0(lean_object* v_a_2559_, lean_object* v_zetaDeltaFVarIds_2560_, lean_object* v_a_x3f_2561_){
_start:
{
lean_object* v___x_2563_; lean_object* v_mctx_2564_; lean_object* v_cache_2565_; lean_object* v_postponed_2566_; lean_object* v_diag_2567_; lean_object* v___x_2569_; uint8_t v_isShared_2570_; uint8_t v_isSharedCheck_2577_; 
v___x_2563_ = lean_st_ref_take(v_a_2559_);
v_mctx_2564_ = lean_ctor_get(v___x_2563_, 0);
v_cache_2565_ = lean_ctor_get(v___x_2563_, 1);
v_postponed_2566_ = lean_ctor_get(v___x_2563_, 3);
v_diag_2567_ = lean_ctor_get(v___x_2563_, 4);
v_isSharedCheck_2577_ = !lean_is_exclusive(v___x_2563_);
if (v_isSharedCheck_2577_ == 0)
{
lean_object* v_unused_2578_; 
v_unused_2578_ = lean_ctor_get(v___x_2563_, 2);
lean_dec(v_unused_2578_);
v___x_2569_ = v___x_2563_;
v_isShared_2570_ = v_isSharedCheck_2577_;
goto v_resetjp_2568_;
}
else
{
lean_inc(v_diag_2567_);
lean_inc(v_postponed_2566_);
lean_inc(v_cache_2565_);
lean_inc(v_mctx_2564_);
lean_dec(v___x_2563_);
v___x_2569_ = lean_box(0);
v_isShared_2570_ = v_isSharedCheck_2577_;
goto v_resetjp_2568_;
}
v_resetjp_2568_:
{
lean_object* v___x_2572_; 
if (v_isShared_2570_ == 0)
{
lean_ctor_set(v___x_2569_, 2, v_zetaDeltaFVarIds_2560_);
v___x_2572_ = v___x_2569_;
goto v_reusejp_2571_;
}
else
{
lean_object* v_reuseFailAlloc_2576_; 
v_reuseFailAlloc_2576_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2576_, 0, v_mctx_2564_);
lean_ctor_set(v_reuseFailAlloc_2576_, 1, v_cache_2565_);
lean_ctor_set(v_reuseFailAlloc_2576_, 2, v_zetaDeltaFVarIds_2560_);
lean_ctor_set(v_reuseFailAlloc_2576_, 3, v_postponed_2566_);
lean_ctor_set(v_reuseFailAlloc_2576_, 4, v_diag_2567_);
v___x_2572_ = v_reuseFailAlloc_2576_;
goto v_reusejp_2571_;
}
v_reusejp_2571_:
{
lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; 
v___x_2573_ = lean_st_ref_put(v_a_2559_, v___x_2572_);
v___x_2574_ = lean_box(0);
v___x_2575_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2575_, 0, v___x_2574_);
return v___x_2575_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkValueTypeClosureAux___lam__0___boxed(lean_object* v_a_2579_, lean_object* v_zetaDeltaFVarIds_2580_, lean_object* v_a_x3f_2581_, lean_object* v___y_2582_){
_start:
{
lean_object* v_res_2583_; 
v_res_2583_ = l_Lean_Meta_Closure_mkValueTypeClosureAux___lam__0(v_a_2579_, v_zetaDeltaFVarIds_2580_, v_a_x3f_2581_);
lean_dec(v_a_x3f_2581_);
lean_dec(v_a_2579_);
return v_res_2583_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkValueTypeClosureAux___lam__1(lean_object* v_a_2584_, lean_object* v_cache_2585_, lean_object* v_a_x3f_2586_){
_start:
{
lean_object* v___x_2588_; lean_object* v_mctx_2589_; lean_object* v_zetaDeltaFVarIds_2590_; lean_object* v_postponed_2591_; lean_object* v_diag_2592_; lean_object* v___x_2594_; uint8_t v_isShared_2595_; uint8_t v_isSharedCheck_2602_; 
v___x_2588_ = lean_st_ref_take(v_a_2584_);
v_mctx_2589_ = lean_ctor_get(v___x_2588_, 0);
v_zetaDeltaFVarIds_2590_ = lean_ctor_get(v___x_2588_, 2);
v_postponed_2591_ = lean_ctor_get(v___x_2588_, 3);
v_diag_2592_ = lean_ctor_get(v___x_2588_, 4);
v_isSharedCheck_2602_ = !lean_is_exclusive(v___x_2588_);
if (v_isSharedCheck_2602_ == 0)
{
lean_object* v_unused_2603_; 
v_unused_2603_ = lean_ctor_get(v___x_2588_, 1);
lean_dec(v_unused_2603_);
v___x_2594_ = v___x_2588_;
v_isShared_2595_ = v_isSharedCheck_2602_;
goto v_resetjp_2593_;
}
else
{
lean_inc(v_diag_2592_);
lean_inc(v_postponed_2591_);
lean_inc(v_zetaDeltaFVarIds_2590_);
lean_inc(v_mctx_2589_);
lean_dec(v___x_2588_);
v___x_2594_ = lean_box(0);
v_isShared_2595_ = v_isSharedCheck_2602_;
goto v_resetjp_2593_;
}
v_resetjp_2593_:
{
lean_object* v___x_2597_; 
if (v_isShared_2595_ == 0)
{
lean_ctor_set(v___x_2594_, 1, v_cache_2585_);
v___x_2597_ = v___x_2594_;
goto v_reusejp_2596_;
}
else
{
lean_object* v_reuseFailAlloc_2601_; 
v_reuseFailAlloc_2601_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2601_, 0, v_mctx_2589_);
lean_ctor_set(v_reuseFailAlloc_2601_, 1, v_cache_2585_);
lean_ctor_set(v_reuseFailAlloc_2601_, 2, v_zetaDeltaFVarIds_2590_);
lean_ctor_set(v_reuseFailAlloc_2601_, 3, v_postponed_2591_);
lean_ctor_set(v_reuseFailAlloc_2601_, 4, v_diag_2592_);
v___x_2597_ = v_reuseFailAlloc_2601_;
goto v_reusejp_2596_;
}
v_reusejp_2596_:
{
lean_object* v___x_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; 
v___x_2598_ = lean_st_ref_put(v_a_2584_, v___x_2597_);
v___x_2599_ = lean_box(0);
v___x_2600_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2600_, 0, v___x_2599_);
return v___x_2600_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkValueTypeClosureAux___lam__1___boxed(lean_object* v_a_2604_, lean_object* v_cache_2605_, lean_object* v_a_x3f_2606_, lean_object* v___y_2607_){
_start:
{
lean_object* v_res_2608_; 
v_res_2608_ = l_Lean_Meta_Closure_mkValueTypeClosureAux___lam__1(v_a_2604_, v_cache_2605_, v_a_x3f_2606_);
lean_dec(v_a_x3f_2606_);
lean_dec(v_a_2604_);
return v_res_2608_;
}
}
static lean_object* _init_l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__0(void){
_start:
{
lean_object* v___x_2609_; 
v___x_2609_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2609_;
}
}
static lean_object* _init_l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__1(void){
_start:
{
lean_object* v___x_2610_; lean_object* v___x_2611_; 
v___x_2610_ = lean_obj_once(&l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__0, &l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__0_once, _init_l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__0);
v___x_2611_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2611_, 0, v___x_2610_);
return v___x_2611_;
}
}
static lean_object* _init_l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__2(void){
_start:
{
lean_object* v___x_2612_; lean_object* v___x_2613_; 
v___x_2612_ = lean_obj_once(&l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__1, &l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__1_once, _init_l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__1);
v___x_2613_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2613_, 0, v___x_2612_);
lean_ctor_set(v___x_2613_, 1, v___x_2612_);
lean_ctor_set(v___x_2613_, 2, v___x_2612_);
lean_ctor_set(v___x_2613_, 3, v___x_2612_);
lean_ctor_set(v___x_2613_, 4, v___x_2612_);
lean_ctor_set(v___x_2613_, 5, v___x_2612_);
return v___x_2613_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkValueTypeClosureAux(lean_object* v_type_2614_, lean_object* v_value_2615_, uint8_t v_a_2616_, lean_object* v_a_2617_, lean_object* v_a_2618_, lean_object* v_a_2619_, lean_object* v_a_2620_, lean_object* v_a_2621_){
_start:
{
lean_object* v___x_2623_; lean_object* v___x_2624_; lean_object* v_mctx_2625_; lean_object* v_zetaDeltaFVarIds_2626_; lean_object* v_postponed_2627_; lean_object* v_diag_2628_; lean_object* v___x_2630_; uint8_t v_isShared_2631_; uint8_t v_isSharedCheck_2708_; 
v___x_2623_ = lean_st_ref_get(v_a_2619_);
v___x_2624_ = lean_st_ref_take(v_a_2619_);
v_mctx_2625_ = lean_ctor_get(v___x_2624_, 0);
v_zetaDeltaFVarIds_2626_ = lean_ctor_get(v___x_2624_, 2);
v_postponed_2627_ = lean_ctor_get(v___x_2624_, 3);
v_diag_2628_ = lean_ctor_get(v___x_2624_, 4);
v_isSharedCheck_2708_ = !lean_is_exclusive(v___x_2624_);
if (v_isSharedCheck_2708_ == 0)
{
lean_object* v_unused_2709_; 
v_unused_2709_ = lean_ctor_get(v___x_2624_, 1);
lean_dec(v_unused_2709_);
v___x_2630_ = v___x_2624_;
v_isShared_2631_ = v_isSharedCheck_2708_;
goto v_resetjp_2629_;
}
else
{
lean_inc(v_diag_2628_);
lean_inc(v_postponed_2627_);
lean_inc(v_zetaDeltaFVarIds_2626_);
lean_inc(v_mctx_2625_);
lean_dec(v___x_2624_);
v___x_2630_ = lean_box(0);
v_isShared_2631_ = v_isSharedCheck_2708_;
goto v_resetjp_2629_;
}
v_resetjp_2629_:
{
lean_object* v___x_2632_; lean_object* v___x_2634_; 
v___x_2632_ = lean_obj_once(&l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__2, &l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__2_once, _init_l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__2);
if (v_isShared_2631_ == 0)
{
lean_ctor_set(v___x_2630_, 1, v___x_2632_);
v___x_2634_ = v___x_2630_;
goto v_reusejp_2633_;
}
else
{
lean_object* v_reuseFailAlloc_2707_; 
v_reuseFailAlloc_2707_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2707_, 0, v_mctx_2625_);
lean_ctor_set(v_reuseFailAlloc_2707_, 1, v___x_2632_);
lean_ctor_set(v_reuseFailAlloc_2707_, 2, v_zetaDeltaFVarIds_2626_);
lean_ctor_set(v_reuseFailAlloc_2707_, 3, v_postponed_2627_);
lean_ctor_set(v_reuseFailAlloc_2707_, 4, v_diag_2628_);
v___x_2634_ = v_reuseFailAlloc_2707_;
goto v_reusejp_2633_;
}
v_reusejp_2633_:
{
lean_object* v___x_2635_; lean_object* v___x_2636_; lean_object* v_mctx_2637_; lean_object* v_cache_2638_; lean_object* v_zetaDeltaFVarIds_2639_; lean_object* v_postponed_2640_; lean_object* v_diag_2641_; lean_object* v___x_2643_; uint8_t v_isShared_2644_; uint8_t v_isSharedCheck_2706_; 
v___x_2635_ = lean_st_ref_put(v_a_2619_, v___x_2634_);
v___x_2636_ = lean_st_ref_take(v_a_2619_);
v_mctx_2637_ = lean_ctor_get(v___x_2636_, 0);
v_cache_2638_ = lean_ctor_get(v___x_2636_, 1);
v_zetaDeltaFVarIds_2639_ = lean_ctor_get(v___x_2636_, 2);
v_postponed_2640_ = lean_ctor_get(v___x_2636_, 3);
v_diag_2641_ = lean_ctor_get(v___x_2636_, 4);
v_isSharedCheck_2706_ = !lean_is_exclusive(v___x_2636_);
if (v_isSharedCheck_2706_ == 0)
{
v___x_2643_ = v___x_2636_;
v_isShared_2644_ = v_isSharedCheck_2706_;
goto v_resetjp_2642_;
}
else
{
lean_inc(v_diag_2641_);
lean_inc(v_postponed_2640_);
lean_inc(v_zetaDeltaFVarIds_2639_);
lean_inc(v_cache_2638_);
lean_inc(v_mctx_2637_);
lean_dec(v___x_2636_);
v___x_2643_ = lean_box(0);
v_isShared_2644_ = v_isSharedCheck_2706_;
goto v_resetjp_2642_;
}
v_resetjp_2642_:
{
lean_object* v___x_2645_; lean_object* v___x_2647_; 
v___x_2645_ = lean_box(1);
if (v_isShared_2644_ == 0)
{
lean_ctor_set(v___x_2643_, 2, v___x_2645_);
v___x_2647_ = v___x_2643_;
goto v_reusejp_2646_;
}
else
{
lean_object* v_reuseFailAlloc_2705_; 
v_reuseFailAlloc_2705_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2705_, 0, v_mctx_2637_);
lean_ctor_set(v_reuseFailAlloc_2705_, 1, v_cache_2638_);
lean_ctor_set(v_reuseFailAlloc_2705_, 2, v___x_2645_);
lean_ctor_set(v_reuseFailAlloc_2705_, 3, v_postponed_2640_);
lean_ctor_set(v_reuseFailAlloc_2705_, 4, v_diag_2641_);
v___x_2647_ = v_reuseFailAlloc_2705_;
goto v_reusejp_2646_;
}
v_reusejp_2646_:
{
lean_object* v___x_2648_; lean_object* v_cache_2649_; lean_object* v_keyedConfig_2650_; lean_object* v_zetaDeltaSet_2651_; lean_object* v_lctx_2652_; lean_object* v_localInstances_2653_; lean_object* v_defEqCtx_x3f_2654_; lean_object* v_synthPendingDepth_2655_; lean_object* v_customCanUnfoldPredicate_x3f_2656_; uint8_t v_univApprox_2657_; uint8_t v_inTypeClassResolution_2658_; uint8_t v_cacheInferType_2659_; lean_object* v_a_2661_; lean_object* v_a_2673_; uint8_t v___x_2676_; lean_object* v___x_2677_; lean_object* v___x_2678_; 
v___x_2648_ = lean_st_ref_put(v_a_2619_, v___x_2647_);
v_cache_2649_ = lean_ctor_get(v___x_2623_, 1);
lean_inc_ref(v_cache_2649_);
lean_dec(v___x_2623_);
v_keyedConfig_2650_ = lean_ctor_get(v_a_2618_, 0);
v_zetaDeltaSet_2651_ = lean_ctor_get(v_a_2618_, 1);
v_lctx_2652_ = lean_ctor_get(v_a_2618_, 2);
v_localInstances_2653_ = lean_ctor_get(v_a_2618_, 3);
v_defEqCtx_x3f_2654_ = lean_ctor_get(v_a_2618_, 4);
v_synthPendingDepth_2655_ = lean_ctor_get(v_a_2618_, 5);
v_customCanUnfoldPredicate_x3f_2656_ = lean_ctor_get(v_a_2618_, 6);
v_univApprox_2657_ = lean_ctor_get_uint8(v_a_2618_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2658_ = lean_ctor_get_uint8(v_a_2618_, sizeof(void*)*7 + 2);
v_cacheInferType_2659_ = lean_ctor_get_uint8(v_a_2618_, sizeof(void*)*7 + 3);
v___x_2676_ = 1;
lean_inc(v_customCanUnfoldPredicate_x3f_2656_);
lean_inc(v_synthPendingDepth_2655_);
lean_inc(v_defEqCtx_x3f_2654_);
lean_inc_ref(v_localInstances_2653_);
lean_inc_ref(v_lctx_2652_);
lean_inc(v_zetaDeltaSet_2651_);
lean_inc_ref(v_keyedConfig_2650_);
v___x_2677_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2677_, 0, v_keyedConfig_2650_);
lean_ctor_set(v___x_2677_, 1, v_zetaDeltaSet_2651_);
lean_ctor_set(v___x_2677_, 2, v_lctx_2652_);
lean_ctor_set(v___x_2677_, 3, v_localInstances_2653_);
lean_ctor_set(v___x_2677_, 4, v_defEqCtx_x3f_2654_);
lean_ctor_set(v___x_2677_, 5, v_synthPendingDepth_2655_);
lean_ctor_set(v___x_2677_, 6, v_customCanUnfoldPredicate_x3f_2656_);
lean_ctor_set_uint8(v___x_2677_, sizeof(void*)*7, v___x_2676_);
lean_ctor_set_uint8(v___x_2677_, sizeof(void*)*7 + 1, v_univApprox_2657_);
lean_ctor_set_uint8(v___x_2677_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2658_);
lean_ctor_set_uint8(v___x_2677_, sizeof(void*)*7 + 3, v_cacheInferType_2659_);
v___x_2678_ = l_Lean_Meta_Closure_collectExpr(v_type_2614_, v_a_2616_, v_a_2617_, v___x_2677_, v_a_2619_, v_a_2620_, v_a_2621_);
if (lean_obj_tag(v___x_2678_) == 0)
{
lean_object* v_a_2679_; lean_object* v___x_2680_; 
v_a_2679_ = lean_ctor_get(v___x_2678_, 0);
lean_inc(v_a_2679_);
lean_dec_ref_known(v___x_2678_, 1);
v___x_2680_ = l_Lean_Meta_Closure_collectExpr(v_value_2615_, v_a_2616_, v_a_2617_, v___x_2677_, v_a_2619_, v_a_2620_, v_a_2621_);
if (lean_obj_tag(v___x_2680_) == 0)
{
lean_object* v_a_2681_; lean_object* v___x_2682_; 
v_a_2681_ = lean_ctor_get(v___x_2680_, 0);
lean_inc(v_a_2681_);
lean_dec_ref_known(v___x_2680_, 1);
v___x_2682_ = l_Lean_Meta_Closure_process(v_a_2616_, v_a_2617_, v___x_2677_, v_a_2619_, v_a_2620_, v_a_2621_);
lean_dec_ref_known(v___x_2677_, 7);
if (lean_obj_tag(v___x_2682_) == 0)
{
lean_object* v___x_2684_; uint8_t v_isShared_2685_; uint8_t v_isSharedCheck_2700_; 
v_isSharedCheck_2700_ = !lean_is_exclusive(v___x_2682_);
if (v_isSharedCheck_2700_ == 0)
{
lean_object* v_unused_2701_; 
v_unused_2701_ = lean_ctor_get(v___x_2682_, 0);
lean_dec(v_unused_2701_);
v___x_2684_ = v___x_2682_;
v_isShared_2685_ = v_isSharedCheck_2700_;
goto v_resetjp_2683_;
}
else
{
lean_dec(v___x_2682_);
v___x_2684_ = lean_box(0);
v_isShared_2685_ = v_isSharedCheck_2700_;
goto v_resetjp_2683_;
}
v_resetjp_2683_:
{
lean_object* v___x_2686_; lean_object* v___x_2688_; 
v___x_2686_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2686_, 0, v_a_2679_);
lean_ctor_set(v___x_2686_, 1, v_a_2681_);
lean_inc_ref(v___x_2686_);
if (v_isShared_2685_ == 0)
{
lean_ctor_set_tag(v___x_2684_, 1);
lean_ctor_set(v___x_2684_, 0, v___x_2686_);
v___x_2688_ = v___x_2684_;
goto v_reusejp_2687_;
}
else
{
lean_object* v_reuseFailAlloc_2699_; 
v_reuseFailAlloc_2699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2699_, 0, v___x_2686_);
v___x_2688_ = v_reuseFailAlloc_2699_;
goto v_reusejp_2687_;
}
v_reusejp_2687_:
{
lean_object* v___x_2689_; lean_object* v___x_2690_; lean_object* v___x_2692_; uint8_t v_isShared_2693_; uint8_t v_isSharedCheck_2697_; 
v___x_2689_ = l_Lean_Meta_Closure_mkValueTypeClosureAux___lam__0(v_a_2619_, v_zetaDeltaFVarIds_2639_, v___x_2688_);
lean_dec_ref(v___x_2689_);
v___x_2690_ = l_Lean_Meta_Closure_mkValueTypeClosureAux___lam__1(v_a_2619_, v_cache_2649_, v___x_2688_);
lean_dec_ref(v___x_2688_);
v_isSharedCheck_2697_ = !lean_is_exclusive(v___x_2690_);
if (v_isSharedCheck_2697_ == 0)
{
lean_object* v_unused_2698_; 
v_unused_2698_ = lean_ctor_get(v___x_2690_, 0);
lean_dec(v_unused_2698_);
v___x_2692_ = v___x_2690_;
v_isShared_2693_ = v_isSharedCheck_2697_;
goto v_resetjp_2691_;
}
else
{
lean_dec(v___x_2690_);
v___x_2692_ = lean_box(0);
v_isShared_2693_ = v_isSharedCheck_2697_;
goto v_resetjp_2691_;
}
v_resetjp_2691_:
{
lean_object* v___x_2695_; 
if (v_isShared_2693_ == 0)
{
lean_ctor_set(v___x_2692_, 0, v___x_2686_);
v___x_2695_ = v___x_2692_;
goto v_reusejp_2694_;
}
else
{
lean_object* v_reuseFailAlloc_2696_; 
v_reuseFailAlloc_2696_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2696_, 0, v___x_2686_);
v___x_2695_ = v_reuseFailAlloc_2696_;
goto v_reusejp_2694_;
}
v_reusejp_2694_:
{
return v___x_2695_;
}
}
}
}
}
else
{
lean_object* v_a_2702_; 
lean_dec(v_a_2681_);
lean_dec(v_a_2679_);
v_a_2702_ = lean_ctor_get(v___x_2682_, 0);
lean_inc(v_a_2702_);
lean_dec_ref_known(v___x_2682_, 1);
v_a_2673_ = v_a_2702_;
goto v___jp_2672_;
}
}
else
{
lean_object* v_a_2703_; 
lean_dec(v_a_2679_);
lean_dec_ref_known(v___x_2677_, 7);
v_a_2703_ = lean_ctor_get(v___x_2680_, 0);
lean_inc(v_a_2703_);
lean_dec_ref_known(v___x_2680_, 1);
v_a_2673_ = v_a_2703_;
goto v___jp_2672_;
}
}
else
{
lean_object* v_a_2704_; 
lean_dec_ref_known(v___x_2677_, 7);
lean_dec_ref(v_value_2615_);
v_a_2704_ = lean_ctor_get(v___x_2678_, 0);
lean_inc(v_a_2704_);
lean_dec_ref_known(v___x_2678_, 1);
v_a_2673_ = v_a_2704_;
goto v___jp_2672_;
}
v___jp_2660_:
{
lean_object* v___x_2662_; lean_object* v___x_2663_; lean_object* v___x_2665_; uint8_t v_isShared_2666_; uint8_t v_isSharedCheck_2670_; 
v___x_2662_ = lean_box(0);
v___x_2663_ = l_Lean_Meta_Closure_mkValueTypeClosureAux___lam__1(v_a_2619_, v_cache_2649_, v___x_2662_);
v_isSharedCheck_2670_ = !lean_is_exclusive(v___x_2663_);
if (v_isSharedCheck_2670_ == 0)
{
lean_object* v_unused_2671_; 
v_unused_2671_ = lean_ctor_get(v___x_2663_, 0);
lean_dec(v_unused_2671_);
v___x_2665_ = v___x_2663_;
v_isShared_2666_ = v_isSharedCheck_2670_;
goto v_resetjp_2664_;
}
else
{
lean_dec(v___x_2663_);
v___x_2665_ = lean_box(0);
v_isShared_2666_ = v_isSharedCheck_2670_;
goto v_resetjp_2664_;
}
v_resetjp_2664_:
{
lean_object* v___x_2668_; 
if (v_isShared_2666_ == 0)
{
lean_ctor_set_tag(v___x_2665_, 1);
lean_ctor_set(v___x_2665_, 0, v_a_2661_);
v___x_2668_ = v___x_2665_;
goto v_reusejp_2667_;
}
else
{
lean_object* v_reuseFailAlloc_2669_; 
v_reuseFailAlloc_2669_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2669_, 0, v_a_2661_);
v___x_2668_ = v_reuseFailAlloc_2669_;
goto v_reusejp_2667_;
}
v_reusejp_2667_:
{
return v___x_2668_;
}
}
}
v___jp_2672_:
{
lean_object* v___x_2674_; lean_object* v___x_2675_; 
v___x_2674_ = lean_box(0);
v___x_2675_ = l_Lean_Meta_Closure_mkValueTypeClosureAux___lam__0(v_a_2619_, v_zetaDeltaFVarIds_2639_, v___x_2674_);
lean_dec_ref(v___x_2675_);
v_a_2661_ = v_a_2673_;
goto v___jp_2660_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkValueTypeClosureAux___boxed(lean_object* v_type_2710_, lean_object* v_value_2711_, lean_object* v_a_2712_, lean_object* v_a_2713_, lean_object* v_a_2714_, lean_object* v_a_2715_, lean_object* v_a_2716_, lean_object* v_a_2717_, lean_object* v_a_2718_){
_start:
{
uint8_t v_a_boxed_2719_; lean_object* v_res_2720_; 
v_a_boxed_2719_ = lean_unbox(v_a_2712_);
v_res_2720_ = l_Lean_Meta_Closure_mkValueTypeClosureAux(v_type_2710_, v_value_2711_, v_a_boxed_2719_, v_a_2713_, v_a_2714_, v_a_2715_, v_a_2716_, v_a_2717_);
lean_dec(v_a_2717_);
lean_dec_ref(v_a_2716_);
lean_dec(v_a_2715_);
lean_dec_ref(v_a_2714_);
lean_dec(v_a_2713_);
return v_res_2720_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4___closed__0(void){
_start:
{
lean_object* v___x_2721_; 
v___x_2721_ = l_instMonadEIO(lean_box(0));
return v___x_2721_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4(lean_object* v_msg_2724_, lean_object* v___y_2725_, lean_object* v___y_2726_, lean_object* v___y_2727_){
_start:
{
lean_object* v___x_2729_; lean_object* v___x_2730_; lean_object* v_toApplicative_2731_; lean_object* v___x_2733_; uint8_t v_isShared_2734_; uint8_t v_isSharedCheck_2772_; 
v___x_2729_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4___closed__0, &l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4___closed__0);
v___x_2730_ = l_StateRefT_x27_instMonad___redArg(v___x_2729_);
v_toApplicative_2731_ = lean_ctor_get(v___x_2730_, 0);
v_isSharedCheck_2772_ = !lean_is_exclusive(v___x_2730_);
if (v_isSharedCheck_2772_ == 0)
{
lean_object* v_unused_2773_; 
v_unused_2773_ = lean_ctor_get(v___x_2730_, 1);
lean_dec(v_unused_2773_);
v___x_2733_ = v___x_2730_;
v_isShared_2734_ = v_isSharedCheck_2772_;
goto v_resetjp_2732_;
}
else
{
lean_inc(v_toApplicative_2731_);
lean_dec(v___x_2730_);
v___x_2733_ = lean_box(0);
v_isShared_2734_ = v_isSharedCheck_2772_;
goto v_resetjp_2732_;
}
v_resetjp_2732_:
{
lean_object* v_toFunctor_2735_; lean_object* v_toSeq_2736_; lean_object* v_toSeqLeft_2737_; lean_object* v_toSeqRight_2738_; lean_object* v___x_2740_; uint8_t v_isShared_2741_; uint8_t v_isSharedCheck_2770_; 
v_toFunctor_2735_ = lean_ctor_get(v_toApplicative_2731_, 0);
v_toSeq_2736_ = lean_ctor_get(v_toApplicative_2731_, 2);
v_toSeqLeft_2737_ = lean_ctor_get(v_toApplicative_2731_, 3);
v_toSeqRight_2738_ = lean_ctor_get(v_toApplicative_2731_, 4);
v_isSharedCheck_2770_ = !lean_is_exclusive(v_toApplicative_2731_);
if (v_isSharedCheck_2770_ == 0)
{
lean_object* v_unused_2771_; 
v_unused_2771_ = lean_ctor_get(v_toApplicative_2731_, 1);
lean_dec(v_unused_2771_);
v___x_2740_ = v_toApplicative_2731_;
v_isShared_2741_ = v_isSharedCheck_2770_;
goto v_resetjp_2739_;
}
else
{
lean_inc(v_toSeqRight_2738_);
lean_inc(v_toSeqLeft_2737_);
lean_inc(v_toSeq_2736_);
lean_inc(v_toFunctor_2735_);
lean_dec(v_toApplicative_2731_);
v___x_2740_ = lean_box(0);
v_isShared_2741_ = v_isSharedCheck_2770_;
goto v_resetjp_2739_;
}
v_resetjp_2739_:
{
lean_object* v___f_2742_; lean_object* v___f_2743_; lean_object* v___f_2744_; lean_object* v___f_2745_; lean_object* v___x_2746_; lean_object* v___f_2747_; lean_object* v___f_2748_; lean_object* v___f_2749_; lean_object* v___x_2751_; 
v___f_2742_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4___closed__1));
v___f_2743_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4___closed__2));
lean_inc_ref(v_toFunctor_2735_);
v___f_2744_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2744_, 0, v_toFunctor_2735_);
v___f_2745_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2745_, 0, v_toFunctor_2735_);
v___x_2746_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2746_, 0, v___f_2744_);
lean_ctor_set(v___x_2746_, 1, v___f_2745_);
v___f_2747_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2747_, 0, v_toSeqRight_2738_);
v___f_2748_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2748_, 0, v_toSeqLeft_2737_);
v___f_2749_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2749_, 0, v_toSeq_2736_);
if (v_isShared_2741_ == 0)
{
lean_ctor_set(v___x_2740_, 4, v___f_2747_);
lean_ctor_set(v___x_2740_, 3, v___f_2748_);
lean_ctor_set(v___x_2740_, 2, v___f_2749_);
lean_ctor_set(v___x_2740_, 1, v___f_2742_);
lean_ctor_set(v___x_2740_, 0, v___x_2746_);
v___x_2751_ = v___x_2740_;
goto v_reusejp_2750_;
}
else
{
lean_object* v_reuseFailAlloc_2769_; 
v_reuseFailAlloc_2769_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2769_, 0, v___x_2746_);
lean_ctor_set(v_reuseFailAlloc_2769_, 1, v___f_2742_);
lean_ctor_set(v_reuseFailAlloc_2769_, 2, v___f_2749_);
lean_ctor_set(v_reuseFailAlloc_2769_, 3, v___f_2748_);
lean_ctor_set(v_reuseFailAlloc_2769_, 4, v___f_2747_);
v___x_2751_ = v_reuseFailAlloc_2769_;
goto v_reusejp_2750_;
}
v_reusejp_2750_:
{
lean_object* v___x_2753_; 
if (v_isShared_2734_ == 0)
{
lean_ctor_set(v___x_2733_, 1, v___f_2743_);
lean_ctor_set(v___x_2733_, 0, v___x_2751_);
v___x_2753_ = v___x_2733_;
goto v_reusejp_2752_;
}
else
{
lean_object* v_reuseFailAlloc_2768_; 
v_reuseFailAlloc_2768_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2768_, 0, v___x_2751_);
lean_ctor_set(v_reuseFailAlloc_2768_, 1, v___f_2743_);
v___x_2753_ = v_reuseFailAlloc_2768_;
goto v_reusejp_2752_;
}
v_reusejp_2752_:
{
lean_object* v___f_2754_; lean_object* v___f_2755_; lean_object* v___f_2756_; lean_object* v___f_2757_; lean_object* v___x_2758_; lean_object* v___x_2759_; lean_object* v___x_2760_; lean_object* v___x_2761_; lean_object* v___x_2762_; lean_object* v___x_2763_; lean_object* v___x_2764_; lean_object* v___x_2765_; lean_object* v___x_12439__overap_2766_; lean_object* v___x_2767_; 
lean_inc_ref_n(v___x_2753_, 6);
v___f_2754_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2754_, 0, v___x_2753_);
v___f_2755_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2755_, 0, v___x_2753_);
v___f_2756_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_2756_, 0, v___x_2753_);
v___f_2757_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_2757_, 0, v___x_2753_);
v___x_2758_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_2758_, 0, lean_box(0));
lean_closure_set(v___x_2758_, 1, lean_box(0));
lean_closure_set(v___x_2758_, 2, v___x_2753_);
v___x_2759_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2759_, 0, v___x_2758_);
lean_ctor_set(v___x_2759_, 1, v___f_2754_);
v___x_2760_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_2760_, 0, lean_box(0));
lean_closure_set(v___x_2760_, 1, lean_box(0));
lean_closure_set(v___x_2760_, 2, v___x_2753_);
v___x_2761_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2761_, 0, v___x_2759_);
lean_ctor_set(v___x_2761_, 1, v___x_2760_);
lean_ctor_set(v___x_2761_, 2, v___f_2755_);
lean_ctor_set(v___x_2761_, 3, v___f_2756_);
lean_ctor_set(v___x_2761_, 4, v___f_2757_);
v___x_2762_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_2762_, 0, lean_box(0));
lean_closure_set(v___x_2762_, 1, lean_box(0));
lean_closure_set(v___x_2762_, 2, v___x_2753_);
v___x_2763_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2763_, 0, v___x_2761_);
lean_ctor_set(v___x_2763_, 1, v___x_2762_);
v___x_2764_ = lean_box(0);
v___x_2765_ = l_instInhabitedOfMonad___redArg(v___x_2763_, v___x_2764_);
v___x_12439__overap_2766_ = lean_panic_fn_borrowed(v___x_2765_, v_msg_2724_);
lean_dec(v___x_2765_);
lean_inc(v___y_2727_);
lean_inc_ref(v___y_2726_);
v___x_2767_ = lean_apply_4(v___x_12439__overap_2766_, v___y_2725_, v___y_2726_, v___y_2727_, lean_box(0));
return v___x_2767_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4___boxed(lean_object* v_msg_2774_, lean_object* v___y_2775_, lean_object* v___y_2776_, lean_object* v___y_2777_, lean_object* v___y_2778_){
_start:
{
lean_object* v_res_2779_; 
v_res_2779_ = l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4(v_msg_2774_, v___y_2775_, v___y_2776_, v___y_2777_);
lean_dec(v___y_2777_);
lean_dec_ref(v___y_2776_);
return v_res_2779_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1_spec__2___redArg(lean_object* v_a_2780_, lean_object* v_x_2781_){
_start:
{
if (lean_obj_tag(v_x_2781_) == 0)
{
uint8_t v___x_2782_; 
v___x_2782_ = 0;
return v___x_2782_;
}
else
{
lean_object* v_key_2783_; lean_object* v_tail_2784_; uint8_t v___x_2785_; 
v_key_2783_ = lean_ctor_get(v_x_2781_, 0);
v_tail_2784_ = lean_ctor_get(v_x_2781_, 2);
v___x_2785_ = l_Lean_instBEqFVarId_beq(v_key_2783_, v_a_2780_);
if (v___x_2785_ == 0)
{
v_x_2781_ = v_tail_2784_;
goto _start;
}
else
{
return v___x_2785_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1_spec__2___redArg___boxed(lean_object* v_a_2787_, lean_object* v_x_2788_){
_start:
{
uint8_t v_res_2789_; lean_object* v_r_2790_; 
v_res_2789_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1_spec__2___redArg(v_a_2787_, v_x_2788_);
lean_dec(v_x_2788_);
lean_dec(v_a_2787_);
v_r_2790_ = lean_box(v_res_2789_);
return v_r_2790_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__4_spec__6_spec__11___redArg(lean_object* v_x_2791_, lean_object* v_x_2792_){
_start:
{
if (lean_obj_tag(v_x_2792_) == 0)
{
return v_x_2791_;
}
else
{
lean_object* v_key_2793_; lean_object* v_value_2794_; lean_object* v_tail_2795_; lean_object* v___x_2797_; uint8_t v_isShared_2798_; uint8_t v_isSharedCheck_2818_; 
v_key_2793_ = lean_ctor_get(v_x_2792_, 0);
v_value_2794_ = lean_ctor_get(v_x_2792_, 1);
v_tail_2795_ = lean_ctor_get(v_x_2792_, 2);
v_isSharedCheck_2818_ = !lean_is_exclusive(v_x_2792_);
if (v_isSharedCheck_2818_ == 0)
{
v___x_2797_ = v_x_2792_;
v_isShared_2798_ = v_isSharedCheck_2818_;
goto v_resetjp_2796_;
}
else
{
lean_inc(v_tail_2795_);
lean_inc(v_value_2794_);
lean_inc(v_key_2793_);
lean_dec(v_x_2792_);
v___x_2797_ = lean_box(0);
v_isShared_2798_ = v_isSharedCheck_2818_;
goto v_resetjp_2796_;
}
v_resetjp_2796_:
{
lean_object* v___x_2799_; uint64_t v___x_2800_; uint64_t v___x_2801_; uint64_t v___x_2802_; uint64_t v_fold_2803_; uint64_t v___x_2804_; uint64_t v___x_2805_; uint64_t v___x_2806_; size_t v___x_2807_; size_t v___x_2808_; size_t v___x_2809_; size_t v___x_2810_; size_t v___x_2811_; lean_object* v___x_2812_; lean_object* v___x_2814_; 
v___x_2799_ = lean_array_get_size(v_x_2791_);
v___x_2800_ = l_Lean_instHashableFVarId_hash(v_key_2793_);
v___x_2801_ = 32ULL;
v___x_2802_ = lean_uint64_shift_right(v___x_2800_, v___x_2801_);
v_fold_2803_ = lean_uint64_xor(v___x_2800_, v___x_2802_);
v___x_2804_ = 16ULL;
v___x_2805_ = lean_uint64_shift_right(v_fold_2803_, v___x_2804_);
v___x_2806_ = lean_uint64_xor(v_fold_2803_, v___x_2805_);
v___x_2807_ = lean_uint64_to_usize(v___x_2806_);
v___x_2808_ = lean_usize_of_nat(v___x_2799_);
v___x_2809_ = ((size_t)1ULL);
v___x_2810_ = lean_usize_sub(v___x_2808_, v___x_2809_);
v___x_2811_ = lean_usize_land(v___x_2807_, v___x_2810_);
v___x_2812_ = lean_array_uget_borrowed(v_x_2791_, v___x_2811_);
lean_inc(v___x_2812_);
if (v_isShared_2798_ == 0)
{
lean_ctor_set(v___x_2797_, 2, v___x_2812_);
v___x_2814_ = v___x_2797_;
goto v_reusejp_2813_;
}
else
{
lean_object* v_reuseFailAlloc_2817_; 
v_reuseFailAlloc_2817_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2817_, 0, v_key_2793_);
lean_ctor_set(v_reuseFailAlloc_2817_, 1, v_value_2794_);
lean_ctor_set(v_reuseFailAlloc_2817_, 2, v___x_2812_);
v___x_2814_ = v_reuseFailAlloc_2817_;
goto v_reusejp_2813_;
}
v_reusejp_2813_:
{
lean_object* v___x_2815_; 
v___x_2815_ = lean_array_uset(v_x_2791_, v___x_2811_, v___x_2814_);
v_x_2791_ = v___x_2815_;
v_x_2792_ = v_tail_2795_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__4_spec__6___redArg(lean_object* v_i_2819_, lean_object* v_source_2820_, lean_object* v_target_2821_){
_start:
{
lean_object* v___x_2822_; uint8_t v___x_2823_; 
v___x_2822_ = lean_array_get_size(v_source_2820_);
v___x_2823_ = lean_nat_dec_lt(v_i_2819_, v___x_2822_);
if (v___x_2823_ == 0)
{
lean_dec_ref(v_source_2820_);
lean_dec(v_i_2819_);
return v_target_2821_;
}
else
{
lean_object* v_es_2824_; lean_object* v___x_2825_; lean_object* v_source_2826_; lean_object* v_target_2827_; lean_object* v___x_2828_; lean_object* v___x_2829_; 
v_es_2824_ = lean_array_fget(v_source_2820_, v_i_2819_);
v___x_2825_ = lean_box(0);
v_source_2826_ = lean_array_fset(v_source_2820_, v_i_2819_, v___x_2825_);
v_target_2827_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__4_spec__6_spec__11___redArg(v_target_2821_, v_es_2824_);
v___x_2828_ = lean_unsigned_to_nat(1u);
v___x_2829_ = lean_nat_add(v_i_2819_, v___x_2828_);
lean_dec(v_i_2819_);
v_i_2819_ = v___x_2829_;
v_source_2820_ = v_source_2826_;
v_target_2821_ = v_target_2827_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__4___redArg(lean_object* v_data_2831_){
_start:
{
lean_object* v___x_2832_; lean_object* v___x_2833_; lean_object* v_nbuckets_2834_; lean_object* v___x_2835_; lean_object* v___x_2836_; lean_object* v___x_2837_; lean_object* v___x_2838_; 
v___x_2832_ = lean_array_get_size(v_data_2831_);
v___x_2833_ = lean_unsigned_to_nat(2u);
v_nbuckets_2834_ = lean_nat_mul(v___x_2832_, v___x_2833_);
v___x_2835_ = lean_unsigned_to_nat(0u);
v___x_2836_ = lean_box(0);
v___x_2837_ = lean_mk_array(v_nbuckets_2834_, v___x_2836_);
v___x_2838_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__4_spec__6___redArg(v___x_2835_, v_data_2831_, v___x_2837_);
return v___x_2838_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2___redArg(lean_object* v_m_2839_, lean_object* v_a_2840_, lean_object* v_b_2841_){
_start:
{
lean_object* v_size_2842_; lean_object* v_buckets_2843_; lean_object* v___x_2844_; uint64_t v___x_2845_; uint64_t v___x_2846_; uint64_t v___x_2847_; uint64_t v_fold_2848_; uint64_t v___x_2849_; uint64_t v___x_2850_; uint64_t v___x_2851_; size_t v___x_2852_; size_t v___x_2853_; size_t v___x_2854_; size_t v___x_2855_; size_t v___x_2856_; lean_object* v_bkt_2857_; uint8_t v___x_2858_; 
v_size_2842_ = lean_ctor_get(v_m_2839_, 0);
v_buckets_2843_ = lean_ctor_get(v_m_2839_, 1);
v___x_2844_ = lean_array_get_size(v_buckets_2843_);
v___x_2845_ = l_Lean_instHashableFVarId_hash(v_a_2840_);
v___x_2846_ = 32ULL;
v___x_2847_ = lean_uint64_shift_right(v___x_2845_, v___x_2846_);
v_fold_2848_ = lean_uint64_xor(v___x_2845_, v___x_2847_);
v___x_2849_ = 16ULL;
v___x_2850_ = lean_uint64_shift_right(v_fold_2848_, v___x_2849_);
v___x_2851_ = lean_uint64_xor(v_fold_2848_, v___x_2850_);
v___x_2852_ = lean_uint64_to_usize(v___x_2851_);
v___x_2853_ = lean_usize_of_nat(v___x_2844_);
v___x_2854_ = ((size_t)1ULL);
v___x_2855_ = lean_usize_sub(v___x_2853_, v___x_2854_);
v___x_2856_ = lean_usize_land(v___x_2852_, v___x_2855_);
v_bkt_2857_ = lean_array_uget_borrowed(v_buckets_2843_, v___x_2856_);
v___x_2858_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1_spec__2___redArg(v_a_2840_, v_bkt_2857_);
if (v___x_2858_ == 0)
{
lean_object* v___x_2860_; uint8_t v_isShared_2861_; uint8_t v_isSharedCheck_2879_; 
lean_inc_ref(v_buckets_2843_);
lean_inc(v_size_2842_);
v_isSharedCheck_2879_ = !lean_is_exclusive(v_m_2839_);
if (v_isSharedCheck_2879_ == 0)
{
lean_object* v_unused_2880_; lean_object* v_unused_2881_; 
v_unused_2880_ = lean_ctor_get(v_m_2839_, 1);
lean_dec(v_unused_2880_);
v_unused_2881_ = lean_ctor_get(v_m_2839_, 0);
lean_dec(v_unused_2881_);
v___x_2860_ = v_m_2839_;
v_isShared_2861_ = v_isSharedCheck_2879_;
goto v_resetjp_2859_;
}
else
{
lean_dec(v_m_2839_);
v___x_2860_ = lean_box(0);
v_isShared_2861_ = v_isSharedCheck_2879_;
goto v_resetjp_2859_;
}
v_resetjp_2859_:
{
lean_object* v___x_2862_; lean_object* v_size_x27_2863_; lean_object* v___x_2864_; lean_object* v_buckets_x27_2865_; lean_object* v___x_2866_; lean_object* v___x_2867_; lean_object* v___x_2868_; lean_object* v___x_2869_; lean_object* v___x_2870_; uint8_t v___x_2871_; 
v___x_2862_ = lean_unsigned_to_nat(1u);
v_size_x27_2863_ = lean_nat_add(v_size_2842_, v___x_2862_);
lean_dec(v_size_2842_);
lean_inc(v_bkt_2857_);
v___x_2864_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2864_, 0, v_a_2840_);
lean_ctor_set(v___x_2864_, 1, v_b_2841_);
lean_ctor_set(v___x_2864_, 2, v_bkt_2857_);
v_buckets_x27_2865_ = lean_array_uset(v_buckets_2843_, v___x_2856_, v___x_2864_);
v___x_2866_ = lean_unsigned_to_nat(4u);
v___x_2867_ = lean_nat_mul(v_size_x27_2863_, v___x_2866_);
v___x_2868_ = lean_unsigned_to_nat(3u);
v___x_2869_ = lean_nat_div(v___x_2867_, v___x_2868_);
lean_dec(v___x_2867_);
v___x_2870_ = lean_array_get_size(v_buckets_x27_2865_);
v___x_2871_ = lean_nat_dec_le(v___x_2869_, v___x_2870_);
lean_dec(v___x_2869_);
if (v___x_2871_ == 0)
{
lean_object* v_val_2872_; lean_object* v___x_2874_; 
v_val_2872_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__4___redArg(v_buckets_x27_2865_);
if (v_isShared_2861_ == 0)
{
lean_ctor_set(v___x_2860_, 1, v_val_2872_);
lean_ctor_set(v___x_2860_, 0, v_size_x27_2863_);
v___x_2874_ = v___x_2860_;
goto v_reusejp_2873_;
}
else
{
lean_object* v_reuseFailAlloc_2875_; 
v_reuseFailAlloc_2875_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2875_, 0, v_size_x27_2863_);
lean_ctor_set(v_reuseFailAlloc_2875_, 1, v_val_2872_);
v___x_2874_ = v_reuseFailAlloc_2875_;
goto v_reusejp_2873_;
}
v_reusejp_2873_:
{
return v___x_2874_;
}
}
else
{
lean_object* v___x_2877_; 
if (v_isShared_2861_ == 0)
{
lean_ctor_set(v___x_2860_, 1, v_buckets_x27_2865_);
lean_ctor_set(v___x_2860_, 0, v_size_x27_2863_);
v___x_2877_ = v___x_2860_;
goto v_reusejp_2876_;
}
else
{
lean_object* v_reuseFailAlloc_2878_; 
v_reuseFailAlloc_2878_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2878_, 0, v_size_x27_2863_);
lean_ctor_set(v_reuseFailAlloc_2878_, 1, v_buckets_x27_2865_);
v___x_2877_ = v_reuseFailAlloc_2878_;
goto v_reusejp_2876_;
}
v_reusejp_2876_:
{
return v___x_2877_;
}
}
}
}
else
{
lean_dec(v_b_2841_);
lean_dec(v_a_2840_);
return v_m_2839_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1___redArg(lean_object* v_m_2882_, lean_object* v_a_2883_){
_start:
{
lean_object* v_buckets_2884_; lean_object* v___x_2885_; uint64_t v___x_2886_; uint64_t v___x_2887_; uint64_t v___x_2888_; uint64_t v_fold_2889_; uint64_t v___x_2890_; uint64_t v___x_2891_; uint64_t v___x_2892_; size_t v___x_2893_; size_t v___x_2894_; size_t v___x_2895_; size_t v___x_2896_; size_t v___x_2897_; lean_object* v___x_2898_; uint8_t v___x_2899_; 
v_buckets_2884_ = lean_ctor_get(v_m_2882_, 1);
v___x_2885_ = lean_array_get_size(v_buckets_2884_);
v___x_2886_ = l_Lean_instHashableFVarId_hash(v_a_2883_);
v___x_2887_ = 32ULL;
v___x_2888_ = lean_uint64_shift_right(v___x_2886_, v___x_2887_);
v_fold_2889_ = lean_uint64_xor(v___x_2886_, v___x_2888_);
v___x_2890_ = 16ULL;
v___x_2891_ = lean_uint64_shift_right(v_fold_2889_, v___x_2890_);
v___x_2892_ = lean_uint64_xor(v_fold_2889_, v___x_2891_);
v___x_2893_ = lean_uint64_to_usize(v___x_2892_);
v___x_2894_ = lean_usize_of_nat(v___x_2885_);
v___x_2895_ = ((size_t)1ULL);
v___x_2896_ = lean_usize_sub(v___x_2894_, v___x_2895_);
v___x_2897_ = lean_usize_land(v___x_2893_, v___x_2896_);
v___x_2898_ = lean_array_uget_borrowed(v_buckets_2884_, v___x_2897_);
v___x_2899_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1_spec__2___redArg(v_a_2883_, v___x_2898_);
return v___x_2899_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1___redArg___boxed(lean_object* v_m_2900_, lean_object* v_a_2901_){
_start:
{
uint8_t v_res_2902_; lean_object* v_r_2903_; 
v_res_2902_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1___redArg(v_m_2900_, v_a_2901_);
lean_dec(v_a_2901_);
lean_dec_ref(v_m_2900_);
v_r_2903_ = lean_box(v_res_2902_);
return v_r_2903_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__6_spec__9___redArg(lean_object* v_a_2904_, lean_object* v_x_2905_){
_start:
{
if (lean_obj_tag(v_x_2905_) == 0)
{
lean_object* v___x_2906_; 
v___x_2906_ = lean_box(0);
return v___x_2906_;
}
else
{
lean_object* v_key_2907_; lean_object* v_value_2908_; lean_object* v_tail_2909_; uint8_t v___x_2910_; 
v_key_2907_ = lean_ctor_get(v_x_2905_, 0);
v_value_2908_ = lean_ctor_get(v_x_2905_, 1);
v_tail_2909_ = lean_ctor_get(v_x_2905_, 2);
v___x_2910_ = lean_expr_eqv(v_key_2907_, v_a_2904_);
if (v___x_2910_ == 0)
{
v_x_2905_ = v_tail_2909_;
goto _start;
}
else
{
lean_object* v___x_2912_; 
lean_inc(v_value_2908_);
v___x_2912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2912_, 0, v_value_2908_);
return v___x_2912_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__6_spec__9___redArg___boxed(lean_object* v_a_2913_, lean_object* v_x_2914_){
_start:
{
lean_object* v_res_2915_; 
v_res_2915_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__6_spec__9___redArg(v_a_2913_, v_x_2914_);
lean_dec(v_x_2914_);
lean_dec_ref(v_a_2913_);
return v_res_2915_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__6___redArg(lean_object* v_m_2916_, lean_object* v_a_2917_){
_start:
{
lean_object* v_buckets_2918_; lean_object* v___x_2919_; uint64_t v___x_2920_; uint64_t v___x_2921_; uint64_t v___x_2922_; uint64_t v_fold_2923_; uint64_t v___x_2924_; uint64_t v___x_2925_; uint64_t v___x_2926_; size_t v___x_2927_; size_t v___x_2928_; size_t v___x_2929_; size_t v___x_2930_; size_t v___x_2931_; lean_object* v___x_2932_; lean_object* v___x_2933_; 
v_buckets_2918_ = lean_ctor_get(v_m_2916_, 1);
v___x_2919_ = lean_array_get_size(v_buckets_2918_);
v___x_2920_ = l_Lean_Expr_hash(v_a_2917_);
v___x_2921_ = 32ULL;
v___x_2922_ = lean_uint64_shift_right(v___x_2920_, v___x_2921_);
v_fold_2923_ = lean_uint64_xor(v___x_2920_, v___x_2922_);
v___x_2924_ = 16ULL;
v___x_2925_ = lean_uint64_shift_right(v_fold_2923_, v___x_2924_);
v___x_2926_ = lean_uint64_xor(v_fold_2923_, v___x_2925_);
v___x_2927_ = lean_uint64_to_usize(v___x_2926_);
v___x_2928_ = lean_usize_of_nat(v___x_2919_);
v___x_2929_ = ((size_t)1ULL);
v___x_2930_ = lean_usize_sub(v___x_2928_, v___x_2929_);
v___x_2931_ = lean_usize_land(v___x_2927_, v___x_2930_);
v___x_2932_ = lean_array_uget_borrowed(v_buckets_2918_, v___x_2931_);
v___x_2933_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__6_spec__9___redArg(v_a_2917_, v___x_2932_);
return v___x_2933_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__6___redArg___boxed(lean_object* v_m_2934_, lean_object* v_a_2935_){
_start:
{
lean_object* v_res_2936_; 
v_res_2936_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__6___redArg(v_m_2934_, v_a_2935_);
lean_dec_ref(v_a_2935_);
lean_dec_ref(v_m_2934_);
return v_res_2936_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__13___redArg(lean_object* v_a_2937_, lean_object* v_b_2938_, lean_object* v_x_2939_){
_start:
{
if (lean_obj_tag(v_x_2939_) == 0)
{
lean_dec(v_b_2938_);
lean_dec_ref(v_a_2937_);
return v_x_2939_;
}
else
{
lean_object* v_key_2940_; lean_object* v_value_2941_; lean_object* v_tail_2942_; lean_object* v___x_2944_; uint8_t v_isShared_2945_; uint8_t v_isSharedCheck_2954_; 
v_key_2940_ = lean_ctor_get(v_x_2939_, 0);
v_value_2941_ = lean_ctor_get(v_x_2939_, 1);
v_tail_2942_ = lean_ctor_get(v_x_2939_, 2);
v_isSharedCheck_2954_ = !lean_is_exclusive(v_x_2939_);
if (v_isSharedCheck_2954_ == 0)
{
v___x_2944_ = v_x_2939_;
v_isShared_2945_ = v_isSharedCheck_2954_;
goto v_resetjp_2943_;
}
else
{
lean_inc(v_tail_2942_);
lean_inc(v_value_2941_);
lean_inc(v_key_2940_);
lean_dec(v_x_2939_);
v___x_2944_ = lean_box(0);
v_isShared_2945_ = v_isSharedCheck_2954_;
goto v_resetjp_2943_;
}
v_resetjp_2943_:
{
uint8_t v___x_2946_; 
v___x_2946_ = lean_expr_eqv(v_key_2940_, v_a_2937_);
if (v___x_2946_ == 0)
{
lean_object* v___x_2947_; lean_object* v___x_2949_; 
v___x_2947_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__13___redArg(v_a_2937_, v_b_2938_, v_tail_2942_);
if (v_isShared_2945_ == 0)
{
lean_ctor_set(v___x_2944_, 2, v___x_2947_);
v___x_2949_ = v___x_2944_;
goto v_reusejp_2948_;
}
else
{
lean_object* v_reuseFailAlloc_2950_; 
v_reuseFailAlloc_2950_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2950_, 0, v_key_2940_);
lean_ctor_set(v_reuseFailAlloc_2950_, 1, v_value_2941_);
lean_ctor_set(v_reuseFailAlloc_2950_, 2, v___x_2947_);
v___x_2949_ = v_reuseFailAlloc_2950_;
goto v_reusejp_2948_;
}
v_reusejp_2948_:
{
return v___x_2949_;
}
}
else
{
lean_object* v___x_2952_; 
lean_dec(v_value_2941_);
lean_dec(v_key_2940_);
if (v_isShared_2945_ == 0)
{
lean_ctor_set(v___x_2944_, 1, v_b_2938_);
lean_ctor_set(v___x_2944_, 0, v_a_2937_);
v___x_2952_ = v___x_2944_;
goto v_reusejp_2951_;
}
else
{
lean_object* v_reuseFailAlloc_2953_; 
v_reuseFailAlloc_2953_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2953_, 0, v_a_2937_);
lean_ctor_set(v_reuseFailAlloc_2953_, 1, v_b_2938_);
lean_ctor_set(v_reuseFailAlloc_2953_, 2, v_tail_2942_);
v___x_2952_ = v_reuseFailAlloc_2953_;
goto v_reusejp_2951_;
}
v_reusejp_2951_:
{
return v___x_2952_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__12_spec__17_spec__18___redArg(lean_object* v_x_2955_, lean_object* v_x_2956_){
_start:
{
if (lean_obj_tag(v_x_2956_) == 0)
{
return v_x_2955_;
}
else
{
lean_object* v_key_2957_; lean_object* v_value_2958_; lean_object* v_tail_2959_; lean_object* v___x_2961_; uint8_t v_isShared_2962_; uint8_t v_isSharedCheck_2982_; 
v_key_2957_ = lean_ctor_get(v_x_2956_, 0);
v_value_2958_ = lean_ctor_get(v_x_2956_, 1);
v_tail_2959_ = lean_ctor_get(v_x_2956_, 2);
v_isSharedCheck_2982_ = !lean_is_exclusive(v_x_2956_);
if (v_isSharedCheck_2982_ == 0)
{
v___x_2961_ = v_x_2956_;
v_isShared_2962_ = v_isSharedCheck_2982_;
goto v_resetjp_2960_;
}
else
{
lean_inc(v_tail_2959_);
lean_inc(v_value_2958_);
lean_inc(v_key_2957_);
lean_dec(v_x_2956_);
v___x_2961_ = lean_box(0);
v_isShared_2962_ = v_isSharedCheck_2982_;
goto v_resetjp_2960_;
}
v_resetjp_2960_:
{
lean_object* v___x_2963_; uint64_t v___x_2964_; uint64_t v___x_2965_; uint64_t v___x_2966_; uint64_t v_fold_2967_; uint64_t v___x_2968_; uint64_t v___x_2969_; uint64_t v___x_2970_; size_t v___x_2971_; size_t v___x_2972_; size_t v___x_2973_; size_t v___x_2974_; size_t v___x_2975_; lean_object* v___x_2976_; lean_object* v___x_2978_; 
v___x_2963_ = lean_array_get_size(v_x_2955_);
v___x_2964_ = l_Lean_Expr_hash(v_key_2957_);
v___x_2965_ = 32ULL;
v___x_2966_ = lean_uint64_shift_right(v___x_2964_, v___x_2965_);
v_fold_2967_ = lean_uint64_xor(v___x_2964_, v___x_2966_);
v___x_2968_ = 16ULL;
v___x_2969_ = lean_uint64_shift_right(v_fold_2967_, v___x_2968_);
v___x_2970_ = lean_uint64_xor(v_fold_2967_, v___x_2969_);
v___x_2971_ = lean_uint64_to_usize(v___x_2970_);
v___x_2972_ = lean_usize_of_nat(v___x_2963_);
v___x_2973_ = ((size_t)1ULL);
v___x_2974_ = lean_usize_sub(v___x_2972_, v___x_2973_);
v___x_2975_ = lean_usize_land(v___x_2971_, v___x_2974_);
v___x_2976_ = lean_array_uget_borrowed(v_x_2955_, v___x_2975_);
lean_inc(v___x_2976_);
if (v_isShared_2962_ == 0)
{
lean_ctor_set(v___x_2961_, 2, v___x_2976_);
v___x_2978_ = v___x_2961_;
goto v_reusejp_2977_;
}
else
{
lean_object* v_reuseFailAlloc_2981_; 
v_reuseFailAlloc_2981_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2981_, 0, v_key_2957_);
lean_ctor_set(v_reuseFailAlloc_2981_, 1, v_value_2958_);
lean_ctor_set(v_reuseFailAlloc_2981_, 2, v___x_2976_);
v___x_2978_ = v_reuseFailAlloc_2981_;
goto v_reusejp_2977_;
}
v_reusejp_2977_:
{
lean_object* v___x_2979_; 
v___x_2979_ = lean_array_uset(v_x_2955_, v___x_2975_, v___x_2978_);
v_x_2955_ = v___x_2979_;
v_x_2956_ = v_tail_2959_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__12_spec__17___redArg(lean_object* v_i_2983_, lean_object* v_source_2984_, lean_object* v_target_2985_){
_start:
{
lean_object* v___x_2986_; uint8_t v___x_2987_; 
v___x_2986_ = lean_array_get_size(v_source_2984_);
v___x_2987_ = lean_nat_dec_lt(v_i_2983_, v___x_2986_);
if (v___x_2987_ == 0)
{
lean_dec_ref(v_source_2984_);
lean_dec(v_i_2983_);
return v_target_2985_;
}
else
{
lean_object* v_es_2988_; lean_object* v___x_2989_; lean_object* v_source_2990_; lean_object* v_target_2991_; lean_object* v___x_2992_; lean_object* v___x_2993_; 
v_es_2988_ = lean_array_fget(v_source_2984_, v_i_2983_);
v___x_2989_ = lean_box(0);
v_source_2990_ = lean_array_fset(v_source_2984_, v_i_2983_, v___x_2989_);
v_target_2991_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__12_spec__17_spec__18___redArg(v_target_2985_, v_es_2988_);
v___x_2992_ = lean_unsigned_to_nat(1u);
v___x_2993_ = lean_nat_add(v_i_2983_, v___x_2992_);
lean_dec(v_i_2983_);
v_i_2983_ = v___x_2993_;
v_source_2984_ = v_source_2990_;
v_target_2985_ = v_target_2991_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__12___redArg(lean_object* v_data_2995_){
_start:
{
lean_object* v___x_2996_; lean_object* v___x_2997_; lean_object* v_nbuckets_2998_; lean_object* v___x_2999_; lean_object* v___x_3000_; lean_object* v___x_3001_; lean_object* v___x_3002_; 
v___x_2996_ = lean_array_get_size(v_data_2995_);
v___x_2997_ = lean_unsigned_to_nat(2u);
v_nbuckets_2998_ = lean_nat_mul(v___x_2996_, v___x_2997_);
v___x_2999_ = lean_unsigned_to_nat(0u);
v___x_3000_ = lean_box(0);
v___x_3001_ = lean_mk_array(v_nbuckets_2998_, v___x_3000_);
v___x_3002_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__12_spec__17___redArg(v___x_2999_, v_data_2995_, v___x_3001_);
return v___x_3002_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__11___redArg(lean_object* v_a_3003_, lean_object* v_x_3004_){
_start:
{
if (lean_obj_tag(v_x_3004_) == 0)
{
uint8_t v___x_3005_; 
v___x_3005_ = 0;
return v___x_3005_;
}
else
{
lean_object* v_key_3006_; lean_object* v_tail_3007_; uint8_t v___x_3008_; 
v_key_3006_ = lean_ctor_get(v_x_3004_, 0);
v_tail_3007_ = lean_ctor_get(v_x_3004_, 2);
v___x_3008_ = lean_expr_eqv(v_key_3006_, v_a_3003_);
if (v___x_3008_ == 0)
{
v_x_3004_ = v_tail_3007_;
goto _start;
}
else
{
return v___x_3008_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__11___redArg___boxed(lean_object* v_a_3010_, lean_object* v_x_3011_){
_start:
{
uint8_t v_res_3012_; lean_object* v_r_3013_; 
v_res_3012_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__11___redArg(v_a_3010_, v_x_3011_);
lean_dec(v_x_3011_);
lean_dec_ref(v_a_3010_);
v_r_3013_ = lean_box(v_res_3012_);
return v_r_3013_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7___redArg(lean_object* v_m_3014_, lean_object* v_a_3015_, lean_object* v_b_3016_){
_start:
{
lean_object* v_size_3017_; lean_object* v_buckets_3018_; lean_object* v___x_3020_; uint8_t v_isShared_3021_; uint8_t v_isSharedCheck_3061_; 
v_size_3017_ = lean_ctor_get(v_m_3014_, 0);
v_buckets_3018_ = lean_ctor_get(v_m_3014_, 1);
v_isSharedCheck_3061_ = !lean_is_exclusive(v_m_3014_);
if (v_isSharedCheck_3061_ == 0)
{
v___x_3020_ = v_m_3014_;
v_isShared_3021_ = v_isSharedCheck_3061_;
goto v_resetjp_3019_;
}
else
{
lean_inc(v_buckets_3018_);
lean_inc(v_size_3017_);
lean_dec(v_m_3014_);
v___x_3020_ = lean_box(0);
v_isShared_3021_ = v_isSharedCheck_3061_;
goto v_resetjp_3019_;
}
v_resetjp_3019_:
{
lean_object* v___x_3022_; uint64_t v___x_3023_; uint64_t v___x_3024_; uint64_t v___x_3025_; uint64_t v_fold_3026_; uint64_t v___x_3027_; uint64_t v___x_3028_; uint64_t v___x_3029_; size_t v___x_3030_; size_t v___x_3031_; size_t v___x_3032_; size_t v___x_3033_; size_t v___x_3034_; lean_object* v_bkt_3035_; uint8_t v___x_3036_; 
v___x_3022_ = lean_array_get_size(v_buckets_3018_);
v___x_3023_ = l_Lean_Expr_hash(v_a_3015_);
v___x_3024_ = 32ULL;
v___x_3025_ = lean_uint64_shift_right(v___x_3023_, v___x_3024_);
v_fold_3026_ = lean_uint64_xor(v___x_3023_, v___x_3025_);
v___x_3027_ = 16ULL;
v___x_3028_ = lean_uint64_shift_right(v_fold_3026_, v___x_3027_);
v___x_3029_ = lean_uint64_xor(v_fold_3026_, v___x_3028_);
v___x_3030_ = lean_uint64_to_usize(v___x_3029_);
v___x_3031_ = lean_usize_of_nat(v___x_3022_);
v___x_3032_ = ((size_t)1ULL);
v___x_3033_ = lean_usize_sub(v___x_3031_, v___x_3032_);
v___x_3034_ = lean_usize_land(v___x_3030_, v___x_3033_);
v_bkt_3035_ = lean_array_uget_borrowed(v_buckets_3018_, v___x_3034_);
v___x_3036_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__11___redArg(v_a_3015_, v_bkt_3035_);
if (v___x_3036_ == 0)
{
lean_object* v___x_3037_; lean_object* v_size_x27_3038_; lean_object* v___x_3039_; lean_object* v_buckets_x27_3040_; lean_object* v___x_3041_; lean_object* v___x_3042_; lean_object* v___x_3043_; lean_object* v___x_3044_; lean_object* v___x_3045_; uint8_t v___x_3046_; 
v___x_3037_ = lean_unsigned_to_nat(1u);
v_size_x27_3038_ = lean_nat_add(v_size_3017_, v___x_3037_);
lean_dec(v_size_3017_);
lean_inc(v_bkt_3035_);
v___x_3039_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3039_, 0, v_a_3015_);
lean_ctor_set(v___x_3039_, 1, v_b_3016_);
lean_ctor_set(v___x_3039_, 2, v_bkt_3035_);
v_buckets_x27_3040_ = lean_array_uset(v_buckets_3018_, v___x_3034_, v___x_3039_);
v___x_3041_ = lean_unsigned_to_nat(4u);
v___x_3042_ = lean_nat_mul(v_size_x27_3038_, v___x_3041_);
v___x_3043_ = lean_unsigned_to_nat(3u);
v___x_3044_ = lean_nat_div(v___x_3042_, v___x_3043_);
lean_dec(v___x_3042_);
v___x_3045_ = lean_array_get_size(v_buckets_x27_3040_);
v___x_3046_ = lean_nat_dec_le(v___x_3044_, v___x_3045_);
lean_dec(v___x_3044_);
if (v___x_3046_ == 0)
{
lean_object* v_val_3047_; lean_object* v___x_3049_; 
v_val_3047_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__12___redArg(v_buckets_x27_3040_);
if (v_isShared_3021_ == 0)
{
lean_ctor_set(v___x_3020_, 1, v_val_3047_);
lean_ctor_set(v___x_3020_, 0, v_size_x27_3038_);
v___x_3049_ = v___x_3020_;
goto v_reusejp_3048_;
}
else
{
lean_object* v_reuseFailAlloc_3050_; 
v_reuseFailAlloc_3050_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3050_, 0, v_size_x27_3038_);
lean_ctor_set(v_reuseFailAlloc_3050_, 1, v_val_3047_);
v___x_3049_ = v_reuseFailAlloc_3050_;
goto v_reusejp_3048_;
}
v_reusejp_3048_:
{
return v___x_3049_;
}
}
else
{
lean_object* v___x_3052_; 
if (v_isShared_3021_ == 0)
{
lean_ctor_set(v___x_3020_, 1, v_buckets_x27_3040_);
lean_ctor_set(v___x_3020_, 0, v_size_x27_3038_);
v___x_3052_ = v___x_3020_;
goto v_reusejp_3051_;
}
else
{
lean_object* v_reuseFailAlloc_3053_; 
v_reuseFailAlloc_3053_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3053_, 0, v_size_x27_3038_);
lean_ctor_set(v_reuseFailAlloc_3053_, 1, v_buckets_x27_3040_);
v___x_3052_ = v_reuseFailAlloc_3053_;
goto v_reusejp_3051_;
}
v_reusejp_3051_:
{
return v___x_3052_;
}
}
}
else
{
lean_object* v___x_3054_; lean_object* v_buckets_x27_3055_; lean_object* v___x_3056_; lean_object* v___x_3057_; lean_object* v___x_3059_; 
lean_inc(v_bkt_3035_);
v___x_3054_ = lean_box(0);
v_buckets_x27_3055_ = lean_array_uset(v_buckets_3018_, v___x_3034_, v___x_3054_);
v___x_3056_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__13___redArg(v_a_3015_, v_b_3016_, v_bkt_3035_);
v___x_3057_ = lean_array_uset(v_buckets_x27_3055_, v___x_3034_, v___x_3056_);
if (v_isShared_3021_ == 0)
{
lean_ctor_set(v___x_3020_, 1, v___x_3057_);
v___x_3059_ = v___x_3020_;
goto v_reusejp_3058_;
}
else
{
lean_object* v_reuseFailAlloc_3060_; 
v_reuseFailAlloc_3060_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3060_, 0, v_size_3017_);
lean_ctor_set(v_reuseFailAlloc_3060_, 1, v___x_3057_);
v___x_3059_ = v_reuseFailAlloc_3060_;
goto v_reusejp_3058_;
}
v_reusejp_3058_:
{
return v___x_3059_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3(lean_object* v_g_3062_, lean_object* v_e_3063_, lean_object* v_a_3064_, lean_object* v___y_3065_, lean_object* v___y_3066_, lean_object* v___y_3067_){
_start:
{
lean_object* v_a_3070_; lean_object* v_fst_3071_; lean_object* v___y_3077_; lean_object* v___x_3080_; lean_object* v___x_3081_; 
v___x_3080_ = lean_st_ref_get(v_a_3064_);
v___x_3081_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__6___redArg(v___x_3080_, v_e_3063_);
lean_dec(v___x_3080_);
if (lean_obj_tag(v___x_3081_) == 0)
{
lean_object* v___x_3082_; 
lean_inc_ref(v_g_3062_);
lean_inc(v___y_3067_);
lean_inc_ref(v___y_3066_);
lean_inc_ref(v_e_3063_);
v___x_3082_ = lean_apply_5(v_g_3062_, v_e_3063_, v___y_3065_, v___y_3066_, v___y_3067_, lean_box(0));
if (lean_obj_tag(v___x_3082_) == 0)
{
lean_object* v_a_3083_; lean_object* v_fst_3084_; lean_object* v_snd_3085_; lean_object* v___x_3087_; uint8_t v_isShared_3088_; uint8_t v_isSharedCheck_3130_; 
v_a_3083_ = lean_ctor_get(v___x_3082_, 0);
lean_inc(v_a_3083_);
lean_dec_ref_known(v___x_3082_, 1);
v_fst_3084_ = lean_ctor_get(v_a_3083_, 0);
v_snd_3085_ = lean_ctor_get(v_a_3083_, 1);
v_isSharedCheck_3130_ = !lean_is_exclusive(v_a_3083_);
if (v_isSharedCheck_3130_ == 0)
{
v___x_3087_ = v_a_3083_;
v_isShared_3088_ = v_isSharedCheck_3130_;
goto v_resetjp_3086_;
}
else
{
lean_inc(v_snd_3085_);
lean_inc(v_fst_3084_);
lean_dec(v_a_3083_);
v___x_3087_ = lean_box(0);
v_isShared_3088_ = v_isSharedCheck_3130_;
goto v_resetjp_3086_;
}
v_resetjp_3086_:
{
lean_object* v_d_3090_; lean_object* v_b_3091_; lean_object* v___y_3092_; uint8_t v___x_3097_; 
v___x_3097_ = lean_unbox(v_fst_3084_);
lean_dec(v_fst_3084_);
if (v___x_3097_ == 0)
{
lean_object* v___x_3098_; lean_object* v___x_3100_; 
lean_dec_ref(v_g_3062_);
v___x_3098_ = lean_box(0);
if (v_isShared_3088_ == 0)
{
lean_ctor_set(v___x_3087_, 0, v___x_3098_);
v___x_3100_ = v___x_3087_;
goto v_reusejp_3099_;
}
else
{
lean_object* v_reuseFailAlloc_3101_; 
v_reuseFailAlloc_3101_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3101_, 0, v___x_3098_);
lean_ctor_set(v_reuseFailAlloc_3101_, 1, v_snd_3085_);
v___x_3100_ = v_reuseFailAlloc_3101_;
goto v_reusejp_3099_;
}
v_reusejp_3099_:
{
v_a_3070_ = v___x_3100_;
v_fst_3071_ = v___x_3098_;
goto v___jp_3069_;
}
}
else
{
switch(lean_obj_tag(v_e_3063_))
{
case 7:
{
lean_object* v_binderType_3102_; lean_object* v_body_3103_; 
lean_del_object(v___x_3087_);
v_binderType_3102_ = lean_ctor_get(v_e_3063_, 1);
v_body_3103_ = lean_ctor_get(v_e_3063_, 2);
lean_inc_ref(v_body_3103_);
lean_inc_ref(v_binderType_3102_);
v_d_3090_ = v_binderType_3102_;
v_b_3091_ = v_body_3103_;
v___y_3092_ = v_a_3064_;
goto v___jp_3089_;
}
case 6:
{
lean_object* v_binderType_3104_; lean_object* v_body_3105_; 
lean_del_object(v___x_3087_);
v_binderType_3104_ = lean_ctor_get(v_e_3063_, 1);
v_body_3105_ = lean_ctor_get(v_e_3063_, 2);
lean_inc_ref(v_body_3105_);
lean_inc_ref(v_binderType_3104_);
v_d_3090_ = v_binderType_3104_;
v_b_3091_ = v_body_3105_;
v___y_3092_ = v_a_3064_;
goto v___jp_3089_;
}
case 8:
{
lean_object* v_type_3106_; lean_object* v_value_3107_; lean_object* v_body_3108_; lean_object* v___x_3109_; 
lean_del_object(v___x_3087_);
v_type_3106_ = lean_ctor_get(v_e_3063_, 1);
v_value_3107_ = lean_ctor_get(v_e_3063_, 2);
v_body_3108_ = lean_ctor_get(v_e_3063_, 3);
lean_inc_ref(v_type_3106_);
lean_inc_ref(v_g_3062_);
v___x_3109_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3(v_g_3062_, v_type_3106_, v_a_3064_, v_snd_3085_, v___y_3066_, v___y_3067_);
if (lean_obj_tag(v___x_3109_) == 0)
{
lean_object* v_a_3110_; lean_object* v_snd_3111_; lean_object* v___x_3112_; 
v_a_3110_ = lean_ctor_get(v___x_3109_, 0);
lean_inc(v_a_3110_);
lean_dec_ref_known(v___x_3109_, 1);
v_snd_3111_ = lean_ctor_get(v_a_3110_, 1);
lean_inc(v_snd_3111_);
lean_dec(v_a_3110_);
lean_inc_ref(v_value_3107_);
lean_inc_ref(v_g_3062_);
v___x_3112_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3(v_g_3062_, v_value_3107_, v_a_3064_, v_snd_3111_, v___y_3066_, v___y_3067_);
if (lean_obj_tag(v___x_3112_) == 0)
{
lean_object* v_a_3113_; lean_object* v_snd_3114_; lean_object* v___x_3115_; 
v_a_3113_ = lean_ctor_get(v___x_3112_, 0);
lean_inc(v_a_3113_);
lean_dec_ref_known(v___x_3112_, 1);
v_snd_3114_ = lean_ctor_get(v_a_3113_, 1);
lean_inc(v_snd_3114_);
lean_dec(v_a_3113_);
lean_inc_ref(v_body_3108_);
v___x_3115_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3(v_g_3062_, v_body_3108_, v_a_3064_, v_snd_3114_, v___y_3066_, v___y_3067_);
v___y_3077_ = v___x_3115_;
goto v___jp_3076_;
}
else
{
lean_dec_ref(v_g_3062_);
v___y_3077_ = v___x_3112_;
goto v___jp_3076_;
}
}
else
{
lean_dec_ref(v_g_3062_);
v___y_3077_ = v___x_3109_;
goto v___jp_3076_;
}
}
case 5:
{
lean_object* v_fn_3116_; lean_object* v_arg_3117_; lean_object* v___x_3118_; 
lean_del_object(v___x_3087_);
v_fn_3116_ = lean_ctor_get(v_e_3063_, 0);
v_arg_3117_ = lean_ctor_get(v_e_3063_, 1);
lean_inc_ref(v_fn_3116_);
lean_inc_ref(v_g_3062_);
v___x_3118_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3(v_g_3062_, v_fn_3116_, v_a_3064_, v_snd_3085_, v___y_3066_, v___y_3067_);
if (lean_obj_tag(v___x_3118_) == 0)
{
lean_object* v_a_3119_; lean_object* v_snd_3120_; lean_object* v___x_3121_; 
v_a_3119_ = lean_ctor_get(v___x_3118_, 0);
lean_inc(v_a_3119_);
lean_dec_ref_known(v___x_3118_, 1);
v_snd_3120_ = lean_ctor_get(v_a_3119_, 1);
lean_inc(v_snd_3120_);
lean_dec(v_a_3119_);
lean_inc_ref(v_arg_3117_);
v___x_3121_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3(v_g_3062_, v_arg_3117_, v_a_3064_, v_snd_3120_, v___y_3066_, v___y_3067_);
v___y_3077_ = v___x_3121_;
goto v___jp_3076_;
}
else
{
lean_dec_ref(v_g_3062_);
v___y_3077_ = v___x_3118_;
goto v___jp_3076_;
}
}
case 10:
{
lean_object* v_expr_3122_; lean_object* v___x_3123_; 
lean_del_object(v___x_3087_);
v_expr_3122_ = lean_ctor_get(v_e_3063_, 1);
lean_inc_ref(v_expr_3122_);
v___x_3123_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3(v_g_3062_, v_expr_3122_, v_a_3064_, v_snd_3085_, v___y_3066_, v___y_3067_);
v___y_3077_ = v___x_3123_;
goto v___jp_3076_;
}
case 11:
{
lean_object* v_struct_3124_; lean_object* v___x_3125_; 
lean_del_object(v___x_3087_);
v_struct_3124_ = lean_ctor_get(v_e_3063_, 2);
lean_inc_ref(v_struct_3124_);
v___x_3125_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3(v_g_3062_, v_struct_3124_, v_a_3064_, v_snd_3085_, v___y_3066_, v___y_3067_);
v___y_3077_ = v___x_3125_;
goto v___jp_3076_;
}
default: 
{
lean_object* v___x_3126_; lean_object* v___x_3128_; 
lean_dec_ref(v_g_3062_);
v___x_3126_ = lean_box(0);
if (v_isShared_3088_ == 0)
{
lean_ctor_set(v___x_3087_, 0, v___x_3126_);
v___x_3128_ = v___x_3087_;
goto v_reusejp_3127_;
}
else
{
lean_object* v_reuseFailAlloc_3129_; 
v_reuseFailAlloc_3129_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3129_, 0, v___x_3126_);
lean_ctor_set(v_reuseFailAlloc_3129_, 1, v_snd_3085_);
v___x_3128_ = v_reuseFailAlloc_3129_;
goto v_reusejp_3127_;
}
v_reusejp_3127_:
{
v_a_3070_ = v___x_3128_;
v_fst_3071_ = v___x_3126_;
goto v___jp_3069_;
}
}
}
}
v___jp_3089_:
{
lean_object* v___x_3093_; 
lean_inc_ref(v_g_3062_);
v___x_3093_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3(v_g_3062_, v_d_3090_, v___y_3092_, v_snd_3085_, v___y_3066_, v___y_3067_);
if (lean_obj_tag(v___x_3093_) == 0)
{
lean_object* v_a_3094_; lean_object* v_snd_3095_; lean_object* v___x_3096_; 
v_a_3094_ = lean_ctor_get(v___x_3093_, 0);
lean_inc(v_a_3094_);
lean_dec_ref_known(v___x_3093_, 1);
v_snd_3095_ = lean_ctor_get(v_a_3094_, 1);
lean_inc(v_snd_3095_);
lean_dec(v_a_3094_);
v___x_3096_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3(v_g_3062_, v_b_3091_, v___y_3092_, v_snd_3095_, v___y_3066_, v___y_3067_);
v___y_3077_ = v___x_3096_;
goto v___jp_3076_;
}
else
{
lean_dec_ref(v_b_3091_);
lean_dec_ref(v_g_3062_);
v___y_3077_ = v___x_3093_;
goto v___jp_3076_;
}
}
}
}
else
{
lean_object* v_a_3131_; lean_object* v___x_3133_; uint8_t v_isShared_3134_; uint8_t v_isSharedCheck_3138_; 
lean_dec_ref(v_e_3063_);
lean_dec_ref(v_g_3062_);
v_a_3131_ = lean_ctor_get(v___x_3082_, 0);
v_isSharedCheck_3138_ = !lean_is_exclusive(v___x_3082_);
if (v_isSharedCheck_3138_ == 0)
{
v___x_3133_ = v___x_3082_;
v_isShared_3134_ = v_isSharedCheck_3138_;
goto v_resetjp_3132_;
}
else
{
lean_inc(v_a_3131_);
lean_dec(v___x_3082_);
v___x_3133_ = lean_box(0);
v_isShared_3134_ = v_isSharedCheck_3138_;
goto v_resetjp_3132_;
}
v_resetjp_3132_:
{
lean_object* v___x_3136_; 
if (v_isShared_3134_ == 0)
{
v___x_3136_ = v___x_3133_;
goto v_reusejp_3135_;
}
else
{
lean_object* v_reuseFailAlloc_3137_; 
v_reuseFailAlloc_3137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3137_, 0, v_a_3131_);
v___x_3136_ = v_reuseFailAlloc_3137_;
goto v_reusejp_3135_;
}
v_reusejp_3135_:
{
return v___x_3136_;
}
}
}
}
else
{
lean_object* v_val_3139_; lean_object* v___x_3141_; uint8_t v_isShared_3142_; uint8_t v_isSharedCheck_3147_; 
lean_dec_ref(v_e_3063_);
lean_dec_ref(v_g_3062_);
v_val_3139_ = lean_ctor_get(v___x_3081_, 0);
v_isSharedCheck_3147_ = !lean_is_exclusive(v___x_3081_);
if (v_isSharedCheck_3147_ == 0)
{
v___x_3141_ = v___x_3081_;
v_isShared_3142_ = v_isSharedCheck_3147_;
goto v_resetjp_3140_;
}
else
{
lean_inc(v_val_3139_);
lean_dec(v___x_3081_);
v___x_3141_ = lean_box(0);
v_isShared_3142_ = v_isSharedCheck_3147_;
goto v_resetjp_3140_;
}
v_resetjp_3140_:
{
lean_object* v___x_3143_; lean_object* v___x_3145_; 
v___x_3143_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3143_, 0, v_val_3139_);
lean_ctor_set(v___x_3143_, 1, v___y_3065_);
if (v_isShared_3142_ == 0)
{
lean_ctor_set_tag(v___x_3141_, 0);
lean_ctor_set(v___x_3141_, 0, v___x_3143_);
v___x_3145_ = v___x_3141_;
goto v_reusejp_3144_;
}
else
{
lean_object* v_reuseFailAlloc_3146_; 
v_reuseFailAlloc_3146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3146_, 0, v___x_3143_);
v___x_3145_ = v_reuseFailAlloc_3146_;
goto v_reusejp_3144_;
}
v_reusejp_3144_:
{
return v___x_3145_;
}
}
}
v___jp_3069_:
{
lean_object* v___x_3072_; lean_object* v___x_3073_; lean_object* v___x_3074_; lean_object* v___x_3075_; 
v___x_3072_ = lean_st_ref_take(v_a_3064_);
v___x_3073_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7___redArg(v___x_3072_, v_e_3063_, v_fst_3071_);
v___x_3074_ = lean_st_ref_put(v_a_3064_, v___x_3073_);
v___x_3075_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3075_, 0, v_a_3070_);
return v___x_3075_;
}
v___jp_3076_:
{
if (lean_obj_tag(v___y_3077_) == 0)
{
lean_object* v_a_3078_; lean_object* v_fst_3079_; 
v_a_3078_ = lean_ctor_get(v___y_3077_, 0);
lean_inc(v_a_3078_);
lean_dec_ref_known(v___y_3077_, 1);
v_fst_3079_ = lean_ctor_get(v_a_3078_, 0);
lean_inc(v_fst_3079_);
v_a_3070_ = v_a_3078_;
v_fst_3071_ = v_fst_3079_;
goto v___jp_3069_;
}
else
{
lean_dec_ref(v_e_3063_);
return v___y_3077_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3___boxed(lean_object* v_g_3148_, lean_object* v_e_3149_, lean_object* v_a_3150_, lean_object* v___y_3151_, lean_object* v___y_3152_, lean_object* v___y_3153_, lean_object* v___y_3154_){
_start:
{
lean_object* v_res_3155_; 
v_res_3155_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3(v_g_3148_, v_e_3149_, v_a_3150_, v___y_3151_, v___y_3152_, v___y_3153_);
lean_dec(v___y_3153_);
lean_dec_ref(v___y_3152_);
lean_dec(v_a_3150_);
return v_res_3155_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__0(void){
_start:
{
lean_object* v___x_3156_; 
v___x_3156_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_3156_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__1(void){
_start:
{
lean_object* v___x_3157_; lean_object* v___x_3158_; 
v___x_3157_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__0);
v___x_3158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3158_, 0, v___x_3157_);
return v___x_3158_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__2(void){
_start:
{
lean_object* v___x_3159_; lean_object* v___x_3160_; lean_object* v___x_3161_; 
v___x_3159_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__1);
v___x_3160_ = lean_unsigned_to_nat(0u);
v___x_3161_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_3161_, 0, v___x_3160_);
lean_ctor_set(v___x_3161_, 1, v___x_3160_);
lean_ctor_set(v___x_3161_, 2, v___x_3160_);
lean_ctor_set(v___x_3161_, 3, v___x_3160_);
lean_ctor_set(v___x_3161_, 4, v___x_3159_);
lean_ctor_set(v___x_3161_, 5, v___x_3159_);
lean_ctor_set(v___x_3161_, 6, v___x_3159_);
lean_ctor_set(v___x_3161_, 7, v___x_3159_);
lean_ctor_set(v___x_3161_, 8, v___x_3159_);
lean_ctor_set(v___x_3161_, 9, v___x_3159_);
lean_ctor_set(v___x_3161_, 10, v___x_3159_);
return v___x_3161_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__3(void){
_start:
{
lean_object* v___x_3162_; lean_object* v___x_3163_; lean_object* v___x_3164_; 
v___x_3162_ = lean_unsigned_to_nat(32u);
v___x_3163_ = lean_mk_empty_array_with_capacity(v___x_3162_);
v___x_3164_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3164_, 0, v___x_3163_);
return v___x_3164_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__4(void){
_start:
{
size_t v___x_3165_; lean_object* v___x_3166_; lean_object* v___x_3167_; lean_object* v___x_3168_; lean_object* v___x_3169_; lean_object* v___x_3170_; 
v___x_3165_ = ((size_t)5ULL);
v___x_3166_ = lean_unsigned_to_nat(0u);
v___x_3167_ = lean_unsigned_to_nat(32u);
v___x_3168_ = lean_mk_empty_array_with_capacity(v___x_3167_);
v___x_3169_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__3);
v___x_3170_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3170_, 0, v___x_3169_);
lean_ctor_set(v___x_3170_, 1, v___x_3168_);
lean_ctor_set(v___x_3170_, 2, v___x_3166_);
lean_ctor_set(v___x_3170_, 3, v___x_3166_);
lean_ctor_set_usize(v___x_3170_, 4, v___x_3165_);
return v___x_3170_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__5(void){
_start:
{
lean_object* v___x_3171_; lean_object* v___x_3172_; lean_object* v___x_3173_; lean_object* v___x_3174_; 
v___x_3171_ = lean_box(1);
v___x_3172_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__4);
v___x_3173_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__1);
v___x_3174_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3174_, 0, v___x_3173_);
lean_ctor_set(v___x_3174_, 1, v___x_3172_);
lean_ctor_set(v___x_3174_, 2, v___x_3171_);
return v___x_3174_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10(lean_object* v_msgData_3175_, lean_object* v___y_3176_, lean_object* v___y_3177_){
_start:
{
lean_object* v___x_3179_; lean_object* v_env_3180_; lean_object* v_options_3181_; lean_object* v___x_3182_; lean_object* v___x_3183_; lean_object* v___x_3184_; lean_object* v___x_3185_; lean_object* v___x_3186_; 
v___x_3179_ = lean_st_ref_get(v___y_3177_);
v_env_3180_ = lean_ctor_get(v___x_3179_, 0);
lean_inc_ref(v_env_3180_);
lean_dec(v___x_3179_);
v_options_3181_ = lean_ctor_get(v___y_3176_, 1);
v___x_3182_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__2);
v___x_3183_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__5);
lean_inc_ref(v_options_3181_);
v___x_3184_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3184_, 0, v_env_3180_);
lean_ctor_set(v___x_3184_, 1, v___x_3182_);
lean_ctor_set(v___x_3184_, 2, v___x_3183_);
lean_ctor_set(v___x_3184_, 3, v_options_3181_);
v___x_3185_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_3185_, 0, v___x_3184_);
lean_ctor_set(v___x_3185_, 1, v_msgData_3175_);
v___x_3186_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3186_, 0, v___x_3185_);
return v___x_3186_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___boxed(lean_object* v_msgData_3187_, lean_object* v___y_3188_, lean_object* v___y_3189_, lean_object* v___y_3190_){
_start:
{
lean_object* v_res_3191_; 
v_res_3191_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10(v_msgData_3187_, v___y_3188_, v___y_3189_);
lean_dec(v___y_3189_);
lean_dec_ref(v___y_3188_);
return v_res_3191_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5___redArg(lean_object* v_msg_3192_, lean_object* v___y_3193_, lean_object* v___y_3194_){
_start:
{
lean_object* v_ref_3196_; lean_object* v___x_3197_; lean_object* v_a_3198_; lean_object* v___x_3200_; uint8_t v_isShared_3201_; uint8_t v_isSharedCheck_3206_; 
v_ref_3196_ = lean_ctor_get(v___y_3193_, 4);
v___x_3197_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10(v_msg_3192_, v___y_3193_, v___y_3194_);
v_a_3198_ = lean_ctor_get(v___x_3197_, 0);
v_isSharedCheck_3206_ = !lean_is_exclusive(v___x_3197_);
if (v_isSharedCheck_3206_ == 0)
{
v___x_3200_ = v___x_3197_;
v_isShared_3201_ = v_isSharedCheck_3206_;
goto v_resetjp_3199_;
}
else
{
lean_inc(v_a_3198_);
lean_dec(v___x_3197_);
v___x_3200_ = lean_box(0);
v_isShared_3201_ = v_isSharedCheck_3206_;
goto v_resetjp_3199_;
}
v_resetjp_3199_:
{
lean_object* v___x_3202_; lean_object* v___x_3204_; 
lean_inc(v_ref_3196_);
v___x_3202_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3202_, 0, v_ref_3196_);
lean_ctor_set(v___x_3202_, 1, v_a_3198_);
if (v_isShared_3201_ == 0)
{
lean_ctor_set_tag(v___x_3200_, 1);
lean_ctor_set(v___x_3200_, 0, v___x_3202_);
v___x_3204_ = v___x_3200_;
goto v_reusejp_3203_;
}
else
{
lean_object* v_reuseFailAlloc_3205_; 
v_reuseFailAlloc_3205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3205_, 0, v___x_3202_);
v___x_3204_ = v_reuseFailAlloc_3205_;
goto v_reusejp_3203_;
}
v_reusejp_3203_:
{
return v___x_3204_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5___redArg___boxed(lean_object* v_msg_3207_, lean_object* v___y_3208_, lean_object* v___y_3209_, lean_object* v___y_3210_){
_start:
{
lean_object* v_res_3211_; 
v_res_3211_ = l_Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5___redArg(v_msg_3207_, v___y_3208_, v___y_3209_);
lean_dec(v___y_3209_);
lean_dec_ref(v___y_3208_);
return v_res_3211_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6___closed__0(void){
_start:
{
lean_object* v___x_3212_; double v___x_3213_; 
v___x_3212_ = lean_unsigned_to_nat(0u);
v___x_3213_ = lean_float_of_nat(v___x_3212_);
return v___x_3213_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6(lean_object* v_cls_3217_, lean_object* v_msg_3218_, lean_object* v___y_3219_, lean_object* v___y_3220_, lean_object* v___y_3221_){
_start:
{
lean_object* v_ref_3223_; lean_object* v___x_3224_; lean_object* v_a_3225_; lean_object* v___x_3227_; uint8_t v_isShared_3228_; uint8_t v_isSharedCheck_3270_; 
v_ref_3223_ = lean_ctor_get(v___y_3220_, 4);
v___x_3224_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10(v_msg_3218_, v___y_3220_, v___y_3221_);
v_a_3225_ = lean_ctor_get(v___x_3224_, 0);
v_isSharedCheck_3270_ = !lean_is_exclusive(v___x_3224_);
if (v_isSharedCheck_3270_ == 0)
{
v___x_3227_ = v___x_3224_;
v_isShared_3228_ = v_isSharedCheck_3270_;
goto v_resetjp_3226_;
}
else
{
lean_inc(v_a_3225_);
lean_dec(v___x_3224_);
v___x_3227_ = lean_box(0);
v_isShared_3228_ = v_isSharedCheck_3270_;
goto v_resetjp_3226_;
}
v_resetjp_3226_:
{
lean_object* v___x_3229_; lean_object* v_traceState_3230_; lean_object* v_env_3231_; lean_object* v_nextMacroScope_3232_; lean_object* v_ngen_3233_; lean_object* v_auxDeclNGen_3234_; lean_object* v_cache_3235_; lean_object* v_messages_3236_; lean_object* v_infoState_3237_; lean_object* v_snapshotTasks_3238_; lean_object* v___x_3240_; uint8_t v_isShared_3241_; uint8_t v_isSharedCheck_3269_; 
v___x_3229_ = lean_st_ref_take(v___y_3221_);
v_traceState_3230_ = lean_ctor_get(v___x_3229_, 4);
v_env_3231_ = lean_ctor_get(v___x_3229_, 0);
v_nextMacroScope_3232_ = lean_ctor_get(v___x_3229_, 1);
v_ngen_3233_ = lean_ctor_get(v___x_3229_, 2);
v_auxDeclNGen_3234_ = lean_ctor_get(v___x_3229_, 3);
v_cache_3235_ = lean_ctor_get(v___x_3229_, 5);
v_messages_3236_ = lean_ctor_get(v___x_3229_, 6);
v_infoState_3237_ = lean_ctor_get(v___x_3229_, 7);
v_snapshotTasks_3238_ = lean_ctor_get(v___x_3229_, 8);
v_isSharedCheck_3269_ = !lean_is_exclusive(v___x_3229_);
if (v_isSharedCheck_3269_ == 0)
{
v___x_3240_ = v___x_3229_;
v_isShared_3241_ = v_isSharedCheck_3269_;
goto v_resetjp_3239_;
}
else
{
lean_inc(v_snapshotTasks_3238_);
lean_inc(v_infoState_3237_);
lean_inc(v_messages_3236_);
lean_inc(v_cache_3235_);
lean_inc(v_traceState_3230_);
lean_inc(v_auxDeclNGen_3234_);
lean_inc(v_ngen_3233_);
lean_inc(v_nextMacroScope_3232_);
lean_inc(v_env_3231_);
lean_dec(v___x_3229_);
v___x_3240_ = lean_box(0);
v_isShared_3241_ = v_isSharedCheck_3269_;
goto v_resetjp_3239_;
}
v_resetjp_3239_:
{
uint64_t v_tid_3242_; lean_object* v_traces_3243_; lean_object* v___x_3245_; uint8_t v_isShared_3246_; uint8_t v_isSharedCheck_3268_; 
v_tid_3242_ = lean_ctor_get_uint64(v_traceState_3230_, sizeof(void*)*1);
v_traces_3243_ = lean_ctor_get(v_traceState_3230_, 0);
v_isSharedCheck_3268_ = !lean_is_exclusive(v_traceState_3230_);
if (v_isSharedCheck_3268_ == 0)
{
v___x_3245_ = v_traceState_3230_;
v_isShared_3246_ = v_isSharedCheck_3268_;
goto v_resetjp_3244_;
}
else
{
lean_inc(v_traces_3243_);
lean_dec(v_traceState_3230_);
v___x_3245_ = lean_box(0);
v_isShared_3246_ = v_isSharedCheck_3268_;
goto v_resetjp_3244_;
}
v_resetjp_3244_:
{
lean_object* v___x_3247_; double v___x_3248_; uint8_t v___x_3249_; lean_object* v___x_3250_; lean_object* v___x_3251_; lean_object* v___x_3252_; lean_object* v___x_3253_; lean_object* v___x_3254_; lean_object* v___x_3255_; lean_object* v___x_3257_; 
v___x_3247_ = lean_box(0);
v___x_3248_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6___closed__0);
v___x_3249_ = 0;
v___x_3250_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6___closed__1));
v___x_3251_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3251_, 0, v_cls_3217_);
lean_ctor_set(v___x_3251_, 1, v___x_3247_);
lean_ctor_set(v___x_3251_, 2, v___x_3250_);
lean_ctor_set_float(v___x_3251_, sizeof(void*)*3, v___x_3248_);
lean_ctor_set_float(v___x_3251_, sizeof(void*)*3 + 8, v___x_3248_);
lean_ctor_set_uint8(v___x_3251_, sizeof(void*)*3 + 16, v___x_3249_);
v___x_3252_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6___closed__2));
v___x_3253_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3253_, 0, v___x_3251_);
lean_ctor_set(v___x_3253_, 1, v_a_3225_);
lean_ctor_set(v___x_3253_, 2, v___x_3252_);
lean_inc(v_ref_3223_);
v___x_3254_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3254_, 0, v_ref_3223_);
lean_ctor_set(v___x_3254_, 1, v___x_3253_);
v___x_3255_ = l_Lean_PersistentArray_push___redArg(v_traces_3243_, v___x_3254_);
if (v_isShared_3246_ == 0)
{
lean_ctor_set(v___x_3245_, 0, v___x_3255_);
v___x_3257_ = v___x_3245_;
goto v_reusejp_3256_;
}
else
{
lean_object* v_reuseFailAlloc_3267_; 
v_reuseFailAlloc_3267_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3267_, 0, v___x_3255_);
lean_ctor_set_uint64(v_reuseFailAlloc_3267_, sizeof(void*)*1, v_tid_3242_);
v___x_3257_ = v_reuseFailAlloc_3267_;
goto v_reusejp_3256_;
}
v_reusejp_3256_:
{
lean_object* v___x_3259_; 
if (v_isShared_3241_ == 0)
{
lean_ctor_set(v___x_3240_, 4, v___x_3257_);
v___x_3259_ = v___x_3240_;
goto v_reusejp_3258_;
}
else
{
lean_object* v_reuseFailAlloc_3266_; 
v_reuseFailAlloc_3266_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3266_, 0, v_env_3231_);
lean_ctor_set(v_reuseFailAlloc_3266_, 1, v_nextMacroScope_3232_);
lean_ctor_set(v_reuseFailAlloc_3266_, 2, v_ngen_3233_);
lean_ctor_set(v_reuseFailAlloc_3266_, 3, v_auxDeclNGen_3234_);
lean_ctor_set(v_reuseFailAlloc_3266_, 4, v___x_3257_);
lean_ctor_set(v_reuseFailAlloc_3266_, 5, v_cache_3235_);
lean_ctor_set(v_reuseFailAlloc_3266_, 6, v_messages_3236_);
lean_ctor_set(v_reuseFailAlloc_3266_, 7, v_infoState_3237_);
lean_ctor_set(v_reuseFailAlloc_3266_, 8, v_snapshotTasks_3238_);
v___x_3259_ = v_reuseFailAlloc_3266_;
goto v_reusejp_3258_;
}
v_reusejp_3258_:
{
lean_object* v___x_3260_; lean_object* v___x_3261_; lean_object* v___x_3262_; lean_object* v___x_3264_; 
v___x_3260_ = lean_st_ref_put(v___y_3221_, v___x_3259_);
v___x_3261_ = lean_box(0);
v___x_3262_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3262_, 0, v___x_3261_);
lean_ctor_set(v___x_3262_, 1, v___y_3219_);
if (v_isShared_3228_ == 0)
{
lean_ctor_set(v___x_3227_, 0, v___x_3262_);
v___x_3264_ = v___x_3227_;
goto v_reusejp_3263_;
}
else
{
lean_object* v_reuseFailAlloc_3265_; 
v_reuseFailAlloc_3265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3265_, 0, v___x_3262_);
v___x_3264_ = v_reuseFailAlloc_3265_;
goto v_reusejp_3263_;
}
v_reusejp_3263_:
{
return v___x_3264_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6___boxed(lean_object* v_cls_3271_, lean_object* v_msg_3272_, lean_object* v___y_3273_, lean_object* v___y_3274_, lean_object* v___y_3275_, lean_object* v___y_3276_){
_start:
{
lean_object* v_res_3277_; 
v_res_3277_ = l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6(v_cls_3271_, v_msg_3272_, v___y_3273_, v___y_3274_, v___y_3275_);
lean_dec(v___y_3275_);
lean_dec_ref(v___y_3274_);
return v_res_3277_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0_spec__0___redArg(lean_object* v_a_3278_, lean_object* v_x_3279_){
_start:
{
if (lean_obj_tag(v_x_3279_) == 0)
{
lean_object* v___x_3280_; 
v___x_3280_ = lean_box(0);
return v___x_3280_;
}
else
{
lean_object* v_key_3281_; lean_object* v_value_3282_; lean_object* v_tail_3283_; uint8_t v___x_3284_; 
v_key_3281_ = lean_ctor_get(v_x_3279_, 0);
v_value_3282_ = lean_ctor_get(v_x_3279_, 1);
v_tail_3283_ = lean_ctor_get(v_x_3279_, 2);
v___x_3284_ = l_Lean_instBEqFVarId_beq(v_key_3281_, v_a_3278_);
if (v___x_3284_ == 0)
{
v_x_3279_ = v_tail_3283_;
goto _start;
}
else
{
lean_object* v___x_3286_; 
lean_inc(v_value_3282_);
v___x_3286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3286_, 0, v_value_3282_);
return v___x_3286_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0_spec__0___redArg___boxed(lean_object* v_a_3287_, lean_object* v_x_3288_){
_start:
{
lean_object* v_res_3289_; 
v_res_3289_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0_spec__0___redArg(v_a_3287_, v_x_3288_);
lean_dec(v_x_3288_);
lean_dec(v_a_3287_);
return v_res_3289_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0___redArg(lean_object* v_m_3290_, lean_object* v_a_3291_){
_start:
{
lean_object* v_buckets_3292_; lean_object* v___x_3293_; uint64_t v___x_3294_; uint64_t v___x_3295_; uint64_t v___x_3296_; uint64_t v_fold_3297_; uint64_t v___x_3298_; uint64_t v___x_3299_; uint64_t v___x_3300_; size_t v___x_3301_; size_t v___x_3302_; size_t v___x_3303_; size_t v___x_3304_; size_t v___x_3305_; lean_object* v___x_3306_; lean_object* v___x_3307_; 
v_buckets_3292_ = lean_ctor_get(v_m_3290_, 1);
v___x_3293_ = lean_array_get_size(v_buckets_3292_);
v___x_3294_ = l_Lean_instHashableFVarId_hash(v_a_3291_);
v___x_3295_ = 32ULL;
v___x_3296_ = lean_uint64_shift_right(v___x_3294_, v___x_3295_);
v_fold_3297_ = lean_uint64_xor(v___x_3294_, v___x_3296_);
v___x_3298_ = 16ULL;
v___x_3299_ = lean_uint64_shift_right(v_fold_3297_, v___x_3298_);
v___x_3300_ = lean_uint64_xor(v_fold_3297_, v___x_3299_);
v___x_3301_ = lean_uint64_to_usize(v___x_3300_);
v___x_3302_ = lean_usize_of_nat(v___x_3293_);
v___x_3303_ = ((size_t)1ULL);
v___x_3304_ = lean_usize_sub(v___x_3302_, v___x_3303_);
v___x_3305_ = lean_usize_land(v___x_3301_, v___x_3304_);
v___x_3306_ = lean_array_uget_borrowed(v_buckets_3292_, v___x_3305_);
v___x_3307_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0_spec__0___redArg(v_a_3291_, v___x_3306_);
return v___x_3307_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0___redArg___boxed(lean_object* v_m_3308_, lean_object* v_a_3309_){
_start:
{
lean_object* v_res_3310_; 
v_res_3310_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0___redArg(v_m_3308_, v_a_3309_);
lean_dec(v_a_3309_);
lean_dec_ref(v_m_3308_);
return v_res_3310_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___lam__0___boxed(lean_object* v___x_3311_, lean_object* v_m_3312_, lean_object* v_e_3313_, lean_object* v___y_3314_, lean_object* v___y_3315_, lean_object* v___y_3316_, lean_object* v___y_3317_){
_start:
{
uint8_t v___x_17647__boxed_3318_; lean_object* v_res_3319_; 
v___x_17647__boxed_3318_ = lean_unbox(v___x_3311_);
v_res_3319_ = l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___lam__0(v___x_17647__boxed_3318_, v_m_3312_, v_e_3313_, v___y_3314_, v___y_3315_, v___y_3316_);
lean_dec(v___y_3316_);
lean_dec_ref(v___y_3315_);
lean_dec_ref(v_e_3313_);
return v_res_3319_;
}
}
static lean_object* _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__0(void){
_start:
{
lean_object* v___x_3320_; lean_object* v___x_3321_; lean_object* v___x_3322_; 
v___x_3320_ = lean_box(0);
v___x_3321_ = lean_unsigned_to_nat(16u);
v___x_3322_ = lean_mk_array(v___x_3321_, v___x_3320_);
return v___x_3322_;
}
}
static lean_object* _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__1(void){
_start:
{
lean_object* v___x_3323_; lean_object* v___x_3324_; lean_object* v___x_3325_; 
v___x_3323_ = lean_obj_once(&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__0, &l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__0_once, _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__0);
v___x_3324_ = lean_unsigned_to_nat(0u);
v___x_3325_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3325_, 0, v___x_3324_);
lean_ctor_set(v___x_3325_, 1, v___x_3323_);
return v___x_3325_;
}
}
static lean_object* _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__5(void){
_start:
{
lean_object* v___x_3329_; lean_object* v___x_3330_; lean_object* v___x_3331_; lean_object* v___x_3332_; lean_object* v___x_3333_; lean_object* v___x_3334_; 
v___x_3329_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__4));
v___x_3330_ = lean_unsigned_to_nat(4u);
v___x_3331_ = lean_unsigned_to_nat(384u);
v___x_3332_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__3));
v___x_3333_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__2));
v___x_3334_ = l_mkPanicMessageWithDecl(v___x_3333_, v___x_3332_, v___x_3331_, v___x_3330_, v___x_3329_);
return v___x_3334_;
}
}
static lean_object* _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__7(void){
_start:
{
lean_object* v___x_3336_; lean_object* v___x_3337_; 
v___x_3336_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__6));
v___x_3337_ = l_Lean_stringToMessageData(v___x_3336_);
return v___x_3337_;
}
}
static lean_object* _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__13(void){
_start:
{
lean_object* v___x_3346_; lean_object* v___x_3347_; lean_object* v___x_3348_; 
v___x_3346_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__10));
v___x_3347_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__12));
v___x_3348_ = l_Lean_Name_append(v___x_3347_, v___x_3346_);
return v___x_3348_;
}
}
static lean_object* _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__15(void){
_start:
{
lean_object* v___x_3350_; lean_object* v___x_3351_; 
v___x_3350_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__14));
v___x_3351_ = l_Lean_stringToMessageData(v___x_3350_);
return v___x_3351_;
}
}
static lean_object* _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__17(void){
_start:
{
lean_object* v___x_3353_; lean_object* v___x_3354_; 
v___x_3353_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__16));
v___x_3354_ = l_Lean_stringToMessageData(v___x_3353_);
return v___x_3354_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit(lean_object* v_m_3355_, lean_object* v_fvarId_3356_, lean_object* v_a_3357_, lean_object* v_a_3358_, lean_object* v_a_3359_){
_start:
{
lean_object* v___x_3361_; 
v___x_3361_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0___redArg(v_m_3355_, v_fvarId_3356_);
if (lean_obj_tag(v___x_3361_) == 1)
{
lean_object* v_val_3362_; lean_object* v___x_3364_; uint8_t v_isShared_3365_; uint8_t v_isSharedCheck_3476_; 
v_val_3362_ = lean_ctor_get(v___x_3361_, 0);
v_isSharedCheck_3476_ = !lean_is_exclusive(v___x_3361_);
if (v_isSharedCheck_3476_ == 0)
{
v___x_3364_ = v___x_3361_;
v_isShared_3365_ = v_isSharedCheck_3476_;
goto v_resetjp_3363_;
}
else
{
lean_inc(v_val_3362_);
lean_dec(v___x_3361_);
v___x_3364_ = lean_box(0);
v_isShared_3365_ = v_isSharedCheck_3476_;
goto v_resetjp_3363_;
}
v_resetjp_3363_:
{
lean_object* v_fst_3366_; lean_object* v_snd_3367_; lean_object* v___x_3369_; uint8_t v_isShared_3370_; uint8_t v_isSharedCheck_3475_; 
v_fst_3366_ = lean_ctor_get(v_val_3362_, 0);
v_snd_3367_ = lean_ctor_get(v_val_3362_, 1);
v_isSharedCheck_3475_ = !lean_is_exclusive(v_val_3362_);
if (v_isSharedCheck_3475_ == 0)
{
v___x_3369_ = v_val_3362_;
v_isShared_3370_ = v_isSharedCheck_3475_;
goto v_resetjp_3368_;
}
else
{
lean_inc(v_snd_3367_);
lean_inc(v_fst_3366_);
lean_dec(v_val_3362_);
v___x_3369_ = lean_box(0);
v_isShared_3370_ = v_isSharedCheck_3475_;
goto v_resetjp_3368_;
}
v_resetjp_3368_:
{
lean_object* v_tempMark_3371_; lean_object* v_doneMark_3372_; lean_object* v___x_3373_; uint8_t v___x_3374_; 
v_tempMark_3371_ = lean_ctor_get(v_a_3357_, 0);
v_doneMark_3372_ = lean_ctor_get(v_a_3357_, 1);
v___x_3373_ = l_Lean_LocalDecl_fvarId(v_fst_3366_);
v___x_3374_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1___redArg(v_doneMark_3372_, v___x_3373_);
if (v___x_3374_ == 0)
{
lean_object* v_options_3375_; lean_object* v_toCold_3376_; uint8_t v_hasTrace_3377_; uint8_t v___x_3378_; lean_object* v___x_3379_; lean_object* v___f_3380_; lean_object* v___y_3382_; lean_object* v___y_3383_; lean_object* v___y_3384_; lean_object* v___y_3435_; lean_object* v___y_3436_; lean_object* v___y_3437_; lean_object* v___y_3442_; lean_object* v_tempMark_3443_; lean_object* v___y_3444_; lean_object* v___y_3445_; 
lean_del_object(v___x_3369_);
lean_del_object(v___x_3364_);
v_options_3375_ = lean_ctor_get(v_a_3358_, 1);
v_toCold_3376_ = lean_ctor_get(v_a_3358_, 0);
v_hasTrace_3377_ = lean_ctor_get_uint8(v_options_3375_, sizeof(void*)*1);
v___x_3378_ = 1;
v___x_3379_ = lean_box(v___x_3378_);
v___f_3380_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___lam__0___boxed), 7, 2);
lean_closure_set(v___f_3380_, 0, v___x_3379_);
lean_closure_set(v___f_3380_, 1, v_m_3355_);
if (v_hasTrace_3377_ == 0)
{
lean_inc_ref(v_tempMark_3371_);
v___y_3442_ = v_a_3357_;
v_tempMark_3443_ = v_tempMark_3371_;
v___y_3444_ = v_a_3358_;
v___y_3445_ = v_a_3359_;
goto v___jp_3441_;
}
else
{
lean_object* v_inheritedTraceOptions_3451_; lean_object* v___x_3452_; lean_object* v___x_3453_; uint8_t v___x_3454_; 
v_inheritedTraceOptions_3451_ = lean_ctor_get(v_toCold_3376_, 4);
v___x_3452_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__10));
v___x_3453_ = lean_obj_once(&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__13, &l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__13_once, _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__13);
v___x_3454_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3451_, v_options_3375_, v___x_3453_);
if (v___x_3454_ == 0)
{
lean_inc_ref(v_tempMark_3371_);
v___y_3442_ = v_a_3357_;
v_tempMark_3443_ = v_tempMark_3371_;
v___y_3444_ = v_a_3358_;
v___y_3445_ = v_a_3359_;
goto v___jp_3441_;
}
else
{
lean_object* v___x_3455_; lean_object* v___x_3456_; lean_object* v___x_3457_; lean_object* v___x_3458_; lean_object* v___x_3459_; lean_object* v___x_3460_; lean_object* v___x_3461_; lean_object* v___x_3462_; lean_object* v___x_3463_; lean_object* v___x_3464_; 
v___x_3455_ = lean_obj_once(&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__15, &l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__15_once, _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__15);
lean_inc(v___x_3373_);
v___x_3456_ = l_Lean_mkFVar(v___x_3373_);
v___x_3457_ = l_Lean_MessageData_ofExpr(v___x_3456_);
v___x_3458_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3458_, 0, v___x_3455_);
lean_ctor_set(v___x_3458_, 1, v___x_3457_);
v___x_3459_ = lean_obj_once(&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__17, &l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__17_once, _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__17);
v___x_3460_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3460_, 0, v___x_3458_);
lean_ctor_set(v___x_3460_, 1, v___x_3459_);
v___x_3461_ = l_Lean_LocalDecl_type(v_fst_3366_);
v___x_3462_ = l_Lean_MessageData_ofExpr(v___x_3461_);
v___x_3463_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3463_, 0, v___x_3460_);
lean_ctor_set(v___x_3463_, 1, v___x_3462_);
v___x_3464_ = l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6(v___x_3452_, v___x_3463_, v_a_3357_, v_a_3358_, v_a_3359_);
if (lean_obj_tag(v___x_3464_) == 0)
{
lean_object* v_a_3465_; lean_object* v_snd_3466_; lean_object* v_tempMark_3467_; 
v_a_3465_ = lean_ctor_get(v___x_3464_, 0);
lean_inc(v_a_3465_);
lean_dec_ref_known(v___x_3464_, 1);
v_snd_3466_ = lean_ctor_get(v_a_3465_, 1);
lean_inc(v_snd_3466_);
lean_dec(v_a_3465_);
v_tempMark_3467_ = lean_ctor_get(v_snd_3466_, 0);
lean_inc_ref(v_tempMark_3467_);
v___y_3442_ = v_snd_3466_;
v_tempMark_3443_ = v_tempMark_3467_;
v___y_3444_ = v_a_3358_;
v___y_3445_ = v_a_3359_;
goto v___jp_3441_;
}
else
{
lean_dec_ref(v___f_3380_);
lean_dec(v___x_3373_);
lean_dec(v_snd_3367_);
lean_dec(v_fst_3366_);
return v___x_3464_;
}
}
}
v___jp_3381_:
{
lean_object* v_tempMark_3385_; lean_object* v_doneMark_3386_; lean_object* v_newDecls_3387_; lean_object* v_newArgs_3388_; lean_object* v___x_3390_; uint8_t v_isShared_3391_; uint8_t v_isSharedCheck_3433_; 
v_tempMark_3385_ = lean_ctor_get(v___y_3382_, 0);
v_doneMark_3386_ = lean_ctor_get(v___y_3382_, 1);
v_newDecls_3387_ = lean_ctor_get(v___y_3382_, 2);
v_newArgs_3388_ = lean_ctor_get(v___y_3382_, 3);
v_isSharedCheck_3433_ = !lean_is_exclusive(v___y_3382_);
if (v_isSharedCheck_3433_ == 0)
{
v___x_3390_ = v___y_3382_;
v_isShared_3391_ = v_isSharedCheck_3433_;
goto v_resetjp_3389_;
}
else
{
lean_inc(v_newArgs_3388_);
lean_inc(v_newDecls_3387_);
lean_inc(v_doneMark_3386_);
lean_inc(v_tempMark_3385_);
lean_dec(v___y_3382_);
v___x_3390_ = lean_box(0);
v_isShared_3391_ = v_isSharedCheck_3433_;
goto v_resetjp_3389_;
}
v_resetjp_3389_:
{
lean_object* v___x_3392_; lean_object* v___x_3393_; lean_object* v___x_3394_; lean_object* v___x_3395_; lean_object* v___x_3397_; 
v___x_3392_ = lean_obj_once(&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__1, &l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__1_once, _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__1);
v___x_3393_ = lean_st_mk_ref(v___x_3392_);
v___x_3394_ = lean_box(0);
lean_inc(v___x_3373_);
v___x_3395_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2___redArg(v_tempMark_3385_, v___x_3373_, v___x_3394_);
if (v_isShared_3391_ == 0)
{
lean_ctor_set(v___x_3390_, 0, v___x_3395_);
v___x_3397_ = v___x_3390_;
goto v_reusejp_3396_;
}
else
{
lean_object* v_reuseFailAlloc_3432_; 
v_reuseFailAlloc_3432_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3432_, 0, v___x_3395_);
lean_ctor_set(v_reuseFailAlloc_3432_, 1, v_doneMark_3386_);
lean_ctor_set(v_reuseFailAlloc_3432_, 2, v_newDecls_3387_);
lean_ctor_set(v_reuseFailAlloc_3432_, 3, v_newArgs_3388_);
v___x_3397_ = v_reuseFailAlloc_3432_;
goto v_reusejp_3396_;
}
v_reusejp_3396_:
{
lean_object* v___x_3398_; lean_object* v___x_3399_; 
v___x_3398_ = l_Lean_LocalDecl_type(v_fst_3366_);
v___x_3399_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3(v___f_3380_, v___x_3398_, v___x_3393_, v___x_3397_, v___y_3384_, v___y_3383_);
if (lean_obj_tag(v___x_3399_) == 0)
{
lean_object* v_a_3400_; lean_object* v___x_3402_; uint8_t v_isShared_3403_; uint8_t v_isSharedCheck_3431_; 
v_a_3400_ = lean_ctor_get(v___x_3399_, 0);
v_isSharedCheck_3431_ = !lean_is_exclusive(v___x_3399_);
if (v_isSharedCheck_3431_ == 0)
{
v___x_3402_ = v___x_3399_;
v_isShared_3403_ = v_isSharedCheck_3431_;
goto v_resetjp_3401_;
}
else
{
lean_inc(v_a_3400_);
lean_dec(v___x_3399_);
v___x_3402_ = lean_box(0);
v_isShared_3403_ = v_isSharedCheck_3431_;
goto v_resetjp_3401_;
}
v_resetjp_3401_:
{
lean_object* v_snd_3404_; lean_object* v___x_3406_; uint8_t v_isShared_3407_; uint8_t v_isSharedCheck_3429_; 
v_snd_3404_ = lean_ctor_get(v_a_3400_, 1);
v_isSharedCheck_3429_ = !lean_is_exclusive(v_a_3400_);
if (v_isSharedCheck_3429_ == 0)
{
lean_object* v_unused_3430_; 
v_unused_3430_ = lean_ctor_get(v_a_3400_, 0);
lean_dec(v_unused_3430_);
v___x_3406_ = v_a_3400_;
v_isShared_3407_ = v_isSharedCheck_3429_;
goto v_resetjp_3405_;
}
else
{
lean_inc(v_snd_3404_);
lean_dec(v_a_3400_);
v___x_3406_ = lean_box(0);
v_isShared_3407_ = v_isSharedCheck_3429_;
goto v_resetjp_3405_;
}
v_resetjp_3405_:
{
lean_object* v___x_3408_; lean_object* v_tempMark_3409_; lean_object* v_doneMark_3410_; lean_object* v_newDecls_3411_; lean_object* v_newArgs_3412_; lean_object* v___x_3414_; uint8_t v_isShared_3415_; uint8_t v_isSharedCheck_3428_; 
v___x_3408_ = lean_st_ref_get(v___x_3393_);
lean_dec(v___x_3393_);
lean_dec(v___x_3408_);
v_tempMark_3409_ = lean_ctor_get(v_snd_3404_, 0);
v_doneMark_3410_ = lean_ctor_get(v_snd_3404_, 1);
v_newDecls_3411_ = lean_ctor_get(v_snd_3404_, 2);
v_newArgs_3412_ = lean_ctor_get(v_snd_3404_, 3);
v_isSharedCheck_3428_ = !lean_is_exclusive(v_snd_3404_);
if (v_isSharedCheck_3428_ == 0)
{
v___x_3414_ = v_snd_3404_;
v_isShared_3415_ = v_isSharedCheck_3428_;
goto v_resetjp_3413_;
}
else
{
lean_inc(v_newArgs_3412_);
lean_inc(v_newDecls_3411_);
lean_inc(v_doneMark_3410_);
lean_inc(v_tempMark_3409_);
lean_dec(v_snd_3404_);
v___x_3414_ = lean_box(0);
v_isShared_3415_ = v_isSharedCheck_3428_;
goto v_resetjp_3413_;
}
v_resetjp_3413_:
{
lean_object* v___x_3416_; lean_object* v___x_3417_; lean_object* v___x_3418_; lean_object* v___x_3420_; 
v___x_3416_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2___redArg(v_doneMark_3410_, v___x_3373_, v___x_3394_);
v___x_3417_ = lean_array_push(v_newDecls_3411_, v_fst_3366_);
v___x_3418_ = lean_array_push(v_newArgs_3412_, v_snd_3367_);
if (v_isShared_3415_ == 0)
{
lean_ctor_set(v___x_3414_, 3, v___x_3418_);
lean_ctor_set(v___x_3414_, 2, v___x_3417_);
lean_ctor_set(v___x_3414_, 1, v___x_3416_);
v___x_3420_ = v___x_3414_;
goto v_reusejp_3419_;
}
else
{
lean_object* v_reuseFailAlloc_3427_; 
v_reuseFailAlloc_3427_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3427_, 0, v_tempMark_3409_);
lean_ctor_set(v_reuseFailAlloc_3427_, 1, v___x_3416_);
lean_ctor_set(v_reuseFailAlloc_3427_, 2, v___x_3417_);
lean_ctor_set(v_reuseFailAlloc_3427_, 3, v___x_3418_);
v___x_3420_ = v_reuseFailAlloc_3427_;
goto v_reusejp_3419_;
}
v_reusejp_3419_:
{
lean_object* v___x_3422_; 
if (v_isShared_3407_ == 0)
{
lean_ctor_set(v___x_3406_, 1, v___x_3420_);
lean_ctor_set(v___x_3406_, 0, v___x_3394_);
v___x_3422_ = v___x_3406_;
goto v_reusejp_3421_;
}
else
{
lean_object* v_reuseFailAlloc_3426_; 
v_reuseFailAlloc_3426_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3426_, 0, v___x_3394_);
lean_ctor_set(v_reuseFailAlloc_3426_, 1, v___x_3420_);
v___x_3422_ = v_reuseFailAlloc_3426_;
goto v_reusejp_3421_;
}
v_reusejp_3421_:
{
lean_object* v___x_3424_; 
if (v_isShared_3403_ == 0)
{
lean_ctor_set(v___x_3402_, 0, v___x_3422_);
v___x_3424_ = v___x_3402_;
goto v_reusejp_3423_;
}
else
{
lean_object* v_reuseFailAlloc_3425_; 
v_reuseFailAlloc_3425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3425_, 0, v___x_3422_);
v___x_3424_ = v_reuseFailAlloc_3425_;
goto v_reusejp_3423_;
}
v_reusejp_3423_:
{
return v___x_3424_;
}
}
}
}
}
}
}
else
{
lean_dec(v___x_3393_);
lean_dec(v___x_3373_);
lean_dec(v_snd_3367_);
lean_dec(v_fst_3366_);
return v___x_3399_;
}
}
}
}
v___jp_3434_:
{
uint8_t v___x_3438_; 
v___x_3438_ = l_Lean_LocalDecl_isLet(v_fst_3366_, v___x_3378_);
if (v___x_3438_ == 0)
{
v___y_3382_ = v___y_3435_;
v___y_3383_ = v___y_3437_;
v___y_3384_ = v___y_3436_;
goto v___jp_3381_;
}
else
{
if (v___x_3374_ == 0)
{
lean_object* v___x_3439_; lean_object* v___x_3440_; 
lean_dec_ref(v___f_3380_);
lean_dec(v___x_3373_);
lean_dec(v_snd_3367_);
lean_dec(v_fst_3366_);
v___x_3439_ = lean_obj_once(&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__5, &l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__5_once, _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__5);
v___x_3440_ = l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4(v___x_3439_, v___y_3435_, v___y_3436_, v___y_3437_);
return v___x_3440_;
}
else
{
v___y_3382_ = v___y_3435_;
v___y_3383_ = v___y_3437_;
v___y_3384_ = v___y_3436_;
goto v___jp_3381_;
}
}
}
v___jp_3441_:
{
uint8_t v___x_3446_; 
v___x_3446_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1___redArg(v_tempMark_3443_, v___x_3373_);
lean_dec_ref(v_tempMark_3443_);
if (v___x_3446_ == 0)
{
v___y_3435_ = v___y_3442_;
v___y_3436_ = v___y_3444_;
v___y_3437_ = v___y_3445_;
goto v___jp_3434_;
}
else
{
lean_object* v___x_3447_; lean_object* v___x_3448_; 
lean_dec_ref(v___y_3442_);
v___x_3447_ = lean_obj_once(&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__7, &l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__7_once, _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__7);
v___x_3448_ = l_Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5___redArg(v___x_3447_, v___y_3444_, v___y_3445_);
if (lean_obj_tag(v___x_3448_) == 0)
{
lean_object* v_a_3449_; lean_object* v_snd_3450_; 
v_a_3449_ = lean_ctor_get(v___x_3448_, 0);
lean_inc(v_a_3449_);
lean_dec_ref_known(v___x_3448_, 1);
v_snd_3450_ = lean_ctor_get(v_a_3449_, 1);
lean_inc(v_snd_3450_);
lean_dec(v_a_3449_);
v___y_3435_ = v_snd_3450_;
v___y_3436_ = v___y_3444_;
v___y_3437_ = v___y_3445_;
goto v___jp_3434_;
}
else
{
lean_dec_ref(v___f_3380_);
lean_dec(v___x_3373_);
lean_dec(v_snd_3367_);
lean_dec(v_fst_3366_);
return v___x_3448_;
}
}
}
}
else
{
lean_object* v___x_3468_; lean_object* v___x_3470_; 
lean_dec(v___x_3373_);
lean_dec(v_snd_3367_);
lean_dec(v_fst_3366_);
lean_dec_ref(v_m_3355_);
v___x_3468_ = lean_box(0);
if (v_isShared_3370_ == 0)
{
lean_ctor_set(v___x_3369_, 1, v_a_3357_);
lean_ctor_set(v___x_3369_, 0, v___x_3468_);
v___x_3470_ = v___x_3369_;
goto v_reusejp_3469_;
}
else
{
lean_object* v_reuseFailAlloc_3474_; 
v_reuseFailAlloc_3474_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3474_, 0, v___x_3468_);
lean_ctor_set(v_reuseFailAlloc_3474_, 1, v_a_3357_);
v___x_3470_ = v_reuseFailAlloc_3474_;
goto v_reusejp_3469_;
}
v_reusejp_3469_:
{
lean_object* v___x_3472_; 
if (v_isShared_3365_ == 0)
{
lean_ctor_set_tag(v___x_3364_, 0);
lean_ctor_set(v___x_3364_, 0, v___x_3470_);
v___x_3472_ = v___x_3364_;
goto v_reusejp_3471_;
}
else
{
lean_object* v_reuseFailAlloc_3473_; 
v_reuseFailAlloc_3473_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3473_, 0, v___x_3470_);
v___x_3472_ = v_reuseFailAlloc_3473_;
goto v_reusejp_3471_;
}
v_reusejp_3471_:
{
return v___x_3472_;
}
}
}
}
}
}
else
{
lean_object* v___x_3477_; lean_object* v___x_3478_; lean_object* v___x_3479_; 
lean_dec(v___x_3361_);
lean_dec_ref(v_m_3355_);
v___x_3477_ = lean_box(0);
v___x_3478_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3478_, 0, v___x_3477_);
lean_ctor_set(v___x_3478_, 1, v_a_3357_);
v___x_3479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3479_, 0, v___x_3478_);
return v___x_3479_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___lam__0(uint8_t v___x_3480_, lean_object* v_m_3481_, lean_object* v_e_3482_, lean_object* v___y_3483_, lean_object* v___y_3484_, lean_object* v___y_3485_){
_start:
{
lean_object* v___y_3488_; uint8_t v___x_3492_; 
v___x_3492_ = l_Lean_Expr_hasFVar(v_e_3482_);
if (v___x_3492_ == 0)
{
lean_object* v___x_3493_; lean_object* v___x_3494_; lean_object* v___x_3495_; 
lean_dec_ref(v_m_3481_);
v___x_3493_ = lean_box(v___x_3492_);
v___x_3494_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3494_, 0, v___x_3493_);
lean_ctor_set(v___x_3494_, 1, v___y_3483_);
v___x_3495_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3495_, 0, v___x_3494_);
return v___x_3495_;
}
else
{
uint8_t v___x_3496_; 
v___x_3496_ = l_Lean_Expr_isFVar(v_e_3482_);
if (v___x_3496_ == 0)
{
lean_dec_ref(v_m_3481_);
v___y_3488_ = v___y_3483_;
goto v___jp_3487_;
}
else
{
lean_object* v___x_3497_; lean_object* v___x_3498_; 
v___x_3497_ = l_Lean_Expr_fvarId_x21(v_e_3482_);
v___x_3498_ = l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit(v_m_3481_, v___x_3497_, v___y_3483_, v___y_3484_, v___y_3485_);
lean_dec(v___x_3497_);
if (lean_obj_tag(v___x_3498_) == 0)
{
lean_object* v_a_3499_; lean_object* v_snd_3500_; 
v_a_3499_ = lean_ctor_get(v___x_3498_, 0);
lean_inc(v_a_3499_);
lean_dec_ref_known(v___x_3498_, 1);
v_snd_3500_ = lean_ctor_get(v_a_3499_, 1);
lean_inc(v_snd_3500_);
lean_dec(v_a_3499_);
v___y_3488_ = v_snd_3500_;
goto v___jp_3487_;
}
else
{
lean_object* v_a_3501_; lean_object* v___x_3503_; uint8_t v_isShared_3504_; uint8_t v_isSharedCheck_3508_; 
v_a_3501_ = lean_ctor_get(v___x_3498_, 0);
v_isSharedCheck_3508_ = !lean_is_exclusive(v___x_3498_);
if (v_isSharedCheck_3508_ == 0)
{
v___x_3503_ = v___x_3498_;
v_isShared_3504_ = v_isSharedCheck_3508_;
goto v_resetjp_3502_;
}
else
{
lean_inc(v_a_3501_);
lean_dec(v___x_3498_);
v___x_3503_ = lean_box(0);
v_isShared_3504_ = v_isSharedCheck_3508_;
goto v_resetjp_3502_;
}
v_resetjp_3502_:
{
lean_object* v___x_3506_; 
if (v_isShared_3504_ == 0)
{
v___x_3506_ = v___x_3503_;
goto v_reusejp_3505_;
}
else
{
lean_object* v_reuseFailAlloc_3507_; 
v_reuseFailAlloc_3507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3507_, 0, v_a_3501_);
v___x_3506_ = v_reuseFailAlloc_3507_;
goto v_reusejp_3505_;
}
v_reusejp_3505_:
{
return v___x_3506_;
}
}
}
}
}
v___jp_3487_:
{
lean_object* v___x_3489_; lean_object* v___x_3490_; lean_object* v___x_3491_; 
v___x_3489_ = lean_box(v___x_3480_);
v___x_3490_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3490_, 0, v___x_3489_);
lean_ctor_set(v___x_3490_, 1, v___y_3488_);
v___x_3491_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3491_, 0, v___x_3490_);
return v___x_3491_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___boxed(lean_object* v_m_3509_, lean_object* v_fvarId_3510_, lean_object* v_a_3511_, lean_object* v_a_3512_, lean_object* v_a_3513_, lean_object* v_a_3514_){
_start:
{
lean_object* v_res_3515_; 
v_res_3515_ = l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit(v_m_3509_, v_fvarId_3510_, v_a_3511_, v_a_3512_, v_a_3513_);
lean_dec(v_a_3513_);
lean_dec_ref(v_a_3512_);
lean_dec(v_fvarId_3510_);
return v_res_3515_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0(lean_object* v_00_u03b2_3516_, lean_object* v_m_3517_, lean_object* v_a_3518_){
_start:
{
lean_object* v___x_3519_; 
v___x_3519_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0___redArg(v_m_3517_, v_a_3518_);
return v___x_3519_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0___boxed(lean_object* v_00_u03b2_3520_, lean_object* v_m_3521_, lean_object* v_a_3522_){
_start:
{
lean_object* v_res_3523_; 
v_res_3523_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0(v_00_u03b2_3520_, v_m_3521_, v_a_3522_);
lean_dec(v_a_3522_);
lean_dec_ref(v_m_3521_);
return v_res_3523_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1(lean_object* v_00_u03b2_3524_, lean_object* v_m_3525_, lean_object* v_a_3526_){
_start:
{
uint8_t v___x_3527_; 
v___x_3527_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1___redArg(v_m_3525_, v_a_3526_);
return v___x_3527_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1___boxed(lean_object* v_00_u03b2_3528_, lean_object* v_m_3529_, lean_object* v_a_3530_){
_start:
{
uint8_t v_res_3531_; lean_object* v_r_3532_; 
v_res_3531_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1(v_00_u03b2_3528_, v_m_3529_, v_a_3530_);
lean_dec(v_a_3530_);
lean_dec_ref(v_m_3529_);
v_r_3532_ = lean_box(v_res_3531_);
return v_r_3532_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2(lean_object* v_00_u03b2_3533_, lean_object* v_m_3534_, lean_object* v_a_3535_, lean_object* v_b_3536_){
_start:
{
lean_object* v___x_3537_; 
v___x_3537_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2___redArg(v_m_3534_, v_a_3535_, v_b_3536_);
return v___x_3537_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5(lean_object* v_00_u03b1_3538_, lean_object* v_msg_3539_, lean_object* v___y_3540_, lean_object* v___y_3541_, lean_object* v___y_3542_){
_start:
{
lean_object* v___x_3544_; 
v___x_3544_ = l_Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5___redArg(v_msg_3539_, v___y_3541_, v___y_3542_);
return v___x_3544_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5___boxed(lean_object* v_00_u03b1_3545_, lean_object* v_msg_3546_, lean_object* v___y_3547_, lean_object* v___y_3548_, lean_object* v___y_3549_, lean_object* v___y_3550_){
_start:
{
lean_object* v_res_3551_; 
v_res_3551_ = l_Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5(v_00_u03b1_3545_, v_msg_3546_, v___y_3547_, v___y_3548_, v___y_3549_);
lean_dec(v___y_3549_);
lean_dec_ref(v___y_3548_);
lean_dec_ref(v___y_3547_);
return v_res_3551_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0_spec__0(lean_object* v_00_u03b2_3552_, lean_object* v_a_3553_, lean_object* v_x_3554_){
_start:
{
lean_object* v___x_3555_; 
v___x_3555_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0_spec__0___redArg(v_a_3553_, v_x_3554_);
return v___x_3555_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3556_, lean_object* v_a_3557_, lean_object* v_x_3558_){
_start:
{
lean_object* v_res_3559_; 
v_res_3559_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0_spec__0(v_00_u03b2_3556_, v_a_3557_, v_x_3558_);
lean_dec(v_x_3558_);
lean_dec(v_a_3557_);
return v_res_3559_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1_spec__2(lean_object* v_00_u03b2_3560_, lean_object* v_a_3561_, lean_object* v_x_3562_){
_start:
{
uint8_t v___x_3563_; 
v___x_3563_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1_spec__2___redArg(v_a_3561_, v_x_3562_);
return v___x_3563_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1_spec__2___boxed(lean_object* v_00_u03b2_3564_, lean_object* v_a_3565_, lean_object* v_x_3566_){
_start:
{
uint8_t v_res_3567_; lean_object* v_r_3568_; 
v_res_3567_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1_spec__2(v_00_u03b2_3564_, v_a_3565_, v_x_3566_);
lean_dec(v_x_3566_);
lean_dec(v_a_3565_);
v_r_3568_ = lean_box(v_res_3567_);
return v_r_3568_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__4(lean_object* v_00_u03b2_3569_, lean_object* v_data_3570_){
_start:
{
lean_object* v___x_3571_; 
v___x_3571_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__4___redArg(v_data_3570_);
return v___x_3571_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__6(lean_object* v_00_u03b2_3572_, lean_object* v_m_3573_, lean_object* v_a_3574_){
_start:
{
lean_object* v___x_3575_; 
v___x_3575_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__6___redArg(v_m_3573_, v_a_3574_);
return v___x_3575_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__6___boxed(lean_object* v_00_u03b2_3576_, lean_object* v_m_3577_, lean_object* v_a_3578_){
_start:
{
lean_object* v_res_3579_; 
v_res_3579_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__6(v_00_u03b2_3576_, v_m_3577_, v_a_3578_);
lean_dec_ref(v_a_3578_);
lean_dec_ref(v_m_3577_);
return v_res_3579_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7(lean_object* v_00_u03b2_3580_, lean_object* v_m_3581_, lean_object* v_a_3582_, lean_object* v_b_3583_){
_start:
{
lean_object* v___x_3584_; 
v___x_3584_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7___redArg(v_m_3581_, v_a_3582_, v_b_3583_);
return v___x_3584_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__4_spec__6(lean_object* v_00_u03b2_3585_, lean_object* v_i_3586_, lean_object* v_source_3587_, lean_object* v_target_3588_){
_start:
{
lean_object* v___x_3589_; 
v___x_3589_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__4_spec__6___redArg(v_i_3586_, v_source_3587_, v_target_3588_);
return v___x_3589_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__6_spec__9(lean_object* v_00_u03b2_3590_, lean_object* v_a_3591_, lean_object* v_x_3592_){
_start:
{
lean_object* v___x_3593_; 
v___x_3593_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__6_spec__9___redArg(v_a_3591_, v_x_3592_);
return v___x_3593_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__6_spec__9___boxed(lean_object* v_00_u03b2_3594_, lean_object* v_a_3595_, lean_object* v_x_3596_){
_start:
{
lean_object* v_res_3597_; 
v_res_3597_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__6_spec__9(v_00_u03b2_3594_, v_a_3595_, v_x_3596_);
lean_dec(v_x_3596_);
lean_dec_ref(v_a_3595_);
return v_res_3597_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__11(lean_object* v_00_u03b2_3598_, lean_object* v_a_3599_, lean_object* v_x_3600_){
_start:
{
uint8_t v___x_3601_; 
v___x_3601_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__11___redArg(v_a_3599_, v_x_3600_);
return v___x_3601_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__11___boxed(lean_object* v_00_u03b2_3602_, lean_object* v_a_3603_, lean_object* v_x_3604_){
_start:
{
uint8_t v_res_3605_; lean_object* v_r_3606_; 
v_res_3605_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__11(v_00_u03b2_3602_, v_a_3603_, v_x_3604_);
lean_dec(v_x_3604_);
lean_dec_ref(v_a_3603_);
v_r_3606_ = lean_box(v_res_3605_);
return v_r_3606_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__12(lean_object* v_00_u03b2_3607_, lean_object* v_data_3608_){
_start:
{
lean_object* v___x_3609_; 
v___x_3609_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__12___redArg(v_data_3608_);
return v___x_3609_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__13(lean_object* v_00_u03b2_3610_, lean_object* v_a_3611_, lean_object* v_b_3612_, lean_object* v_x_3613_){
_start:
{
lean_object* v___x_3614_; 
v___x_3614_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__13___redArg(v_a_3611_, v_b_3612_, v_x_3613_);
return v___x_3614_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__4_spec__6_spec__11(lean_object* v_00_u03b2_3615_, lean_object* v_x_3616_, lean_object* v_x_3617_){
_start:
{
lean_object* v___x_3618_; 
v___x_3618_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__4_spec__6_spec__11___redArg(v_x_3616_, v_x_3617_);
return v___x_3618_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__12_spec__17(lean_object* v_00_u03b2_3619_, lean_object* v_i_3620_, lean_object* v_source_3621_, lean_object* v_target_3622_){
_start:
{
lean_object* v___x_3623_; 
v___x_3623_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__12_spec__17___redArg(v_i_3620_, v_source_3621_, v_target_3622_);
return v___x_3623_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__12_spec__17_spec__18(lean_object* v_00_u03b2_3624_, lean_object* v_x_3625_, lean_object* v_x_3626_){
_start:
{
lean_object* v___x_3627_; 
v___x_3627_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__12_spec__17_spec__18___redArg(v_x_3625_, v_x_3626_);
return v___x_3627_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__1(lean_object* v_msg_3629_, lean_object* v___y_3630_, lean_object* v___y_3631_){
_start:
{
lean_object* v___f_3633_; lean_object* v___x_7343__overap_3634_; lean_object* v___x_3635_; 
v___f_3633_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__1___closed__0));
v___x_7343__overap_3634_ = lean_panic_fn_borrowed(v___f_3633_, v_msg_3629_);
lean_inc(v___y_3631_);
lean_inc_ref(v___y_3630_);
v___x_3635_ = lean_apply_3(v___x_7343__overap_3634_, v___y_3630_, v___y_3631_, lean_box(0));
return v___x_3635_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__1___boxed(lean_object* v_msg_3636_, lean_object* v___y_3637_, lean_object* v___y_3638_, lean_object* v___y_3639_){
_start:
{
lean_object* v_res_3640_; 
v_res_3640_ = l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__1(v_msg_3636_, v___y_3637_, v___y_3638_);
lean_dec(v___y_3638_);
lean_dec_ref(v___y_3637_);
return v_res_3640_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___lam__0(lean_object* v_newDecls_3641_, lean_object* v_newArgs_3642_, lean_object* v_____r_3643_, lean_object* v___y_3644_, lean_object* v___y_3645_, lean_object* v___y_3646_){
_start:
{
lean_object* v___x_3648_; lean_object* v___x_3649_; lean_object* v___x_3650_; 
v___x_3648_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3648_, 0, v_newDecls_3641_);
lean_ctor_set(v___x_3648_, 1, v_newArgs_3642_);
v___x_3649_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3649_, 0, v___x_3648_);
lean_ctor_set(v___x_3649_, 1, v___y_3644_);
v___x_3650_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3650_, 0, v___x_3649_);
return v___x_3650_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___lam__0___boxed(lean_object* v_newDecls_3651_, lean_object* v_newArgs_3652_, lean_object* v_____r_3653_, lean_object* v___y_3654_, lean_object* v___y_3655_, lean_object* v___y_3656_, lean_object* v___y_3657_){
_start:
{
lean_object* v_res_3658_; 
v_res_3658_ = l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___lam__0(v_newDecls_3651_, v_newArgs_3652_, v_____r_3653_, v___y_3654_, v___y_3655_, v___y_3656_);
lean_dec(v___y_3656_);
lean_dec_ref(v___y_3655_);
return v_res_3658_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__6(lean_object* v_cls_3659_, lean_object* v_msg_3660_, lean_object* v___y_3661_, lean_object* v___y_3662_){
_start:
{
lean_object* v_ref_3664_; lean_object* v___x_3665_; lean_object* v_a_3666_; lean_object* v___x_3668_; uint8_t v_isShared_3669_; uint8_t v_isSharedCheck_3710_; 
v_ref_3664_ = lean_ctor_get(v___y_3661_, 4);
v___x_3665_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10(v_msg_3660_, v___y_3661_, v___y_3662_);
v_a_3666_ = lean_ctor_get(v___x_3665_, 0);
v_isSharedCheck_3710_ = !lean_is_exclusive(v___x_3665_);
if (v_isSharedCheck_3710_ == 0)
{
v___x_3668_ = v___x_3665_;
v_isShared_3669_ = v_isSharedCheck_3710_;
goto v_resetjp_3667_;
}
else
{
lean_inc(v_a_3666_);
lean_dec(v___x_3665_);
v___x_3668_ = lean_box(0);
v_isShared_3669_ = v_isSharedCheck_3710_;
goto v_resetjp_3667_;
}
v_resetjp_3667_:
{
lean_object* v___x_3670_; lean_object* v_traceState_3671_; lean_object* v_env_3672_; lean_object* v_nextMacroScope_3673_; lean_object* v_ngen_3674_; lean_object* v_auxDeclNGen_3675_; lean_object* v_cache_3676_; lean_object* v_messages_3677_; lean_object* v_infoState_3678_; lean_object* v_snapshotTasks_3679_; lean_object* v___x_3681_; uint8_t v_isShared_3682_; uint8_t v_isSharedCheck_3709_; 
v___x_3670_ = lean_st_ref_take(v___y_3662_);
v_traceState_3671_ = lean_ctor_get(v___x_3670_, 4);
v_env_3672_ = lean_ctor_get(v___x_3670_, 0);
v_nextMacroScope_3673_ = lean_ctor_get(v___x_3670_, 1);
v_ngen_3674_ = lean_ctor_get(v___x_3670_, 2);
v_auxDeclNGen_3675_ = lean_ctor_get(v___x_3670_, 3);
v_cache_3676_ = lean_ctor_get(v___x_3670_, 5);
v_messages_3677_ = lean_ctor_get(v___x_3670_, 6);
v_infoState_3678_ = lean_ctor_get(v___x_3670_, 7);
v_snapshotTasks_3679_ = lean_ctor_get(v___x_3670_, 8);
v_isSharedCheck_3709_ = !lean_is_exclusive(v___x_3670_);
if (v_isSharedCheck_3709_ == 0)
{
v___x_3681_ = v___x_3670_;
v_isShared_3682_ = v_isSharedCheck_3709_;
goto v_resetjp_3680_;
}
else
{
lean_inc(v_snapshotTasks_3679_);
lean_inc(v_infoState_3678_);
lean_inc(v_messages_3677_);
lean_inc(v_cache_3676_);
lean_inc(v_traceState_3671_);
lean_inc(v_auxDeclNGen_3675_);
lean_inc(v_ngen_3674_);
lean_inc(v_nextMacroScope_3673_);
lean_inc(v_env_3672_);
lean_dec(v___x_3670_);
v___x_3681_ = lean_box(0);
v_isShared_3682_ = v_isSharedCheck_3709_;
goto v_resetjp_3680_;
}
v_resetjp_3680_:
{
uint64_t v_tid_3683_; lean_object* v_traces_3684_; lean_object* v___x_3686_; uint8_t v_isShared_3687_; uint8_t v_isSharedCheck_3708_; 
v_tid_3683_ = lean_ctor_get_uint64(v_traceState_3671_, sizeof(void*)*1);
v_traces_3684_ = lean_ctor_get(v_traceState_3671_, 0);
v_isSharedCheck_3708_ = !lean_is_exclusive(v_traceState_3671_);
if (v_isSharedCheck_3708_ == 0)
{
v___x_3686_ = v_traceState_3671_;
v_isShared_3687_ = v_isSharedCheck_3708_;
goto v_resetjp_3685_;
}
else
{
lean_inc(v_traces_3684_);
lean_dec(v_traceState_3671_);
v___x_3686_ = lean_box(0);
v_isShared_3687_ = v_isSharedCheck_3708_;
goto v_resetjp_3685_;
}
v_resetjp_3685_:
{
lean_object* v___x_3688_; double v___x_3689_; uint8_t v___x_3690_; lean_object* v___x_3691_; lean_object* v___x_3692_; lean_object* v___x_3693_; lean_object* v___x_3694_; lean_object* v___x_3695_; lean_object* v___x_3696_; lean_object* v___x_3698_; 
v___x_3688_ = lean_box(0);
v___x_3689_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6___closed__0);
v___x_3690_ = 0;
v___x_3691_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6___closed__1));
v___x_3692_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3692_, 0, v_cls_3659_);
lean_ctor_set(v___x_3692_, 1, v___x_3688_);
lean_ctor_set(v___x_3692_, 2, v___x_3691_);
lean_ctor_set_float(v___x_3692_, sizeof(void*)*3, v___x_3689_);
lean_ctor_set_float(v___x_3692_, sizeof(void*)*3 + 8, v___x_3689_);
lean_ctor_set_uint8(v___x_3692_, sizeof(void*)*3 + 16, v___x_3690_);
v___x_3693_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6___closed__2));
v___x_3694_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3694_, 0, v___x_3692_);
lean_ctor_set(v___x_3694_, 1, v_a_3666_);
lean_ctor_set(v___x_3694_, 2, v___x_3693_);
lean_inc(v_ref_3664_);
v___x_3695_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3695_, 0, v_ref_3664_);
lean_ctor_set(v___x_3695_, 1, v___x_3694_);
v___x_3696_ = l_Lean_PersistentArray_push___redArg(v_traces_3684_, v___x_3695_);
if (v_isShared_3687_ == 0)
{
lean_ctor_set(v___x_3686_, 0, v___x_3696_);
v___x_3698_ = v___x_3686_;
goto v_reusejp_3697_;
}
else
{
lean_object* v_reuseFailAlloc_3707_; 
v_reuseFailAlloc_3707_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3707_, 0, v___x_3696_);
lean_ctor_set_uint64(v_reuseFailAlloc_3707_, sizeof(void*)*1, v_tid_3683_);
v___x_3698_ = v_reuseFailAlloc_3707_;
goto v_reusejp_3697_;
}
v_reusejp_3697_:
{
lean_object* v___x_3700_; 
if (v_isShared_3682_ == 0)
{
lean_ctor_set(v___x_3681_, 4, v___x_3698_);
v___x_3700_ = v___x_3681_;
goto v_reusejp_3699_;
}
else
{
lean_object* v_reuseFailAlloc_3706_; 
v_reuseFailAlloc_3706_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3706_, 0, v_env_3672_);
lean_ctor_set(v_reuseFailAlloc_3706_, 1, v_nextMacroScope_3673_);
lean_ctor_set(v_reuseFailAlloc_3706_, 2, v_ngen_3674_);
lean_ctor_set(v_reuseFailAlloc_3706_, 3, v_auxDeclNGen_3675_);
lean_ctor_set(v_reuseFailAlloc_3706_, 4, v___x_3698_);
lean_ctor_set(v_reuseFailAlloc_3706_, 5, v_cache_3676_);
lean_ctor_set(v_reuseFailAlloc_3706_, 6, v_messages_3677_);
lean_ctor_set(v_reuseFailAlloc_3706_, 7, v_infoState_3678_);
lean_ctor_set(v_reuseFailAlloc_3706_, 8, v_snapshotTasks_3679_);
v___x_3700_ = v_reuseFailAlloc_3706_;
goto v_reusejp_3699_;
}
v_reusejp_3699_:
{
lean_object* v___x_3701_; lean_object* v___x_3702_; lean_object* v___x_3704_; 
v___x_3701_ = lean_st_ref_put(v___y_3662_, v___x_3700_);
v___x_3702_ = lean_box(0);
if (v_isShared_3669_ == 0)
{
lean_ctor_set(v___x_3668_, 0, v___x_3702_);
v___x_3704_ = v___x_3668_;
goto v_reusejp_3703_;
}
else
{
lean_object* v_reuseFailAlloc_3705_; 
v_reuseFailAlloc_3705_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3705_, 0, v___x_3702_);
v___x_3704_ = v_reuseFailAlloc_3705_;
goto v_reusejp_3703_;
}
v_reusejp_3703_:
{
return v___x_3704_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__6___boxed(lean_object* v_cls_3711_, lean_object* v_msg_3712_, lean_object* v___y_3713_, lean_object* v___y_3714_, lean_object* v___y_3715_){
_start:
{
lean_object* v_res_3716_; 
v_res_3716_ = l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__6(v_cls_3711_, v_msg_3712_, v___y_3713_, v___y_3714_);
lean_dec(v___y_3714_);
lean_dec_ref(v___y_3713_);
return v_res_3716_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__4(size_t v_sz_3717_, size_t v_i_3718_, lean_object* v_bs_3719_){
_start:
{
uint8_t v___x_3720_; 
v___x_3720_ = lean_usize_dec_lt(v_i_3718_, v_sz_3717_);
if (v___x_3720_ == 0)
{
return v_bs_3719_;
}
else
{
lean_object* v_v_3721_; lean_object* v___x_3722_; lean_object* v_bs_x27_3723_; lean_object* v___x_3724_; lean_object* v___x_3725_; size_t v___x_3726_; size_t v___x_3727_; lean_object* v___x_3728_; 
v_v_3721_ = lean_array_uget(v_bs_3719_, v_i_3718_);
v___x_3722_ = lean_unsigned_to_nat(0u);
v_bs_x27_3723_ = lean_array_uset(v_bs_3719_, v_i_3718_, v___x_3722_);
v___x_3724_ = l_Lean_LocalDecl_fvarId(v_v_3721_);
lean_dec(v_v_3721_);
v___x_3725_ = l_Lean_mkFVar(v___x_3724_);
v___x_3726_ = ((size_t)1ULL);
v___x_3727_ = lean_usize_add(v_i_3718_, v___x_3726_);
v___x_3728_ = lean_array_uset(v_bs_x27_3723_, v_i_3718_, v___x_3725_);
v_i_3718_ = v___x_3727_;
v_bs_3719_ = v___x_3728_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__4___boxed(lean_object* v_sz_3730_, lean_object* v_i_3731_, lean_object* v_bs_3732_){
_start:
{
size_t v_sz_boxed_3733_; size_t v_i_boxed_3734_; lean_object* v_res_3735_; 
v_sz_boxed_3733_ = lean_unbox_usize(v_sz_3730_);
lean_dec(v_sz_3730_);
v_i_boxed_3734_ = lean_unbox_usize(v_i_3731_);
lean_dec(v_i_3731_);
v_res_3735_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__4(v_sz_boxed_3733_, v_i_boxed_3734_, v_bs_3732_);
return v_res_3735_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__3(lean_object* v___x_3736_, lean_object* v_as_3737_, size_t v_sz_3738_, size_t v_i_3739_, lean_object* v_b_3740_, lean_object* v___y_3741_, lean_object* v___y_3742_, lean_object* v___y_3743_){
_start:
{
uint8_t v___x_3745_; 
v___x_3745_ = lean_usize_dec_lt(v_i_3739_, v_sz_3738_);
if (v___x_3745_ == 0)
{
lean_object* v___x_3746_; lean_object* v___x_3747_; 
lean_dec_ref(v___x_3736_);
v___x_3746_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3746_, 0, v_b_3740_);
lean_ctor_set(v___x_3746_, 1, v___y_3741_);
v___x_3747_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3747_, 0, v___x_3746_);
return v___x_3747_;
}
else
{
lean_object* v_a_3748_; lean_object* v___x_3749_; lean_object* v___x_3750_; 
v_a_3748_ = lean_array_uget_borrowed(v_as_3737_, v_i_3739_);
v___x_3749_ = l_Lean_LocalDecl_fvarId(v_a_3748_);
lean_inc_ref(v___x_3736_);
v___x_3750_ = l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit(v___x_3736_, v___x_3749_, v___y_3741_, v___y_3742_, v___y_3743_);
lean_dec(v___x_3749_);
if (lean_obj_tag(v___x_3750_) == 0)
{
lean_object* v_a_3751_; lean_object* v_snd_3752_; lean_object* v___x_3753_; size_t v___x_3754_; size_t v___x_3755_; 
v_a_3751_ = lean_ctor_get(v___x_3750_, 0);
lean_inc(v_a_3751_);
lean_dec_ref_known(v___x_3750_, 1);
v_snd_3752_ = lean_ctor_get(v_a_3751_, 1);
lean_inc(v_snd_3752_);
lean_dec(v_a_3751_);
v___x_3753_ = lean_box(0);
v___x_3754_ = ((size_t)1ULL);
v___x_3755_ = lean_usize_add(v_i_3739_, v___x_3754_);
v_i_3739_ = v___x_3755_;
v_b_3740_ = v___x_3753_;
v___y_3741_ = v_snd_3752_;
goto _start;
}
else
{
lean_dec_ref(v___x_3736_);
return v___x_3750_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__3___boxed(lean_object* v___x_3757_, lean_object* v_as_3758_, lean_object* v_sz_3759_, lean_object* v_i_3760_, lean_object* v_b_3761_, lean_object* v___y_3762_, lean_object* v___y_3763_, lean_object* v___y_3764_, lean_object* v___y_3765_){
_start:
{
size_t v_sz_boxed_3766_; size_t v_i_boxed_3767_; lean_object* v_res_3768_; 
v_sz_boxed_3766_ = lean_unbox_usize(v_sz_3759_);
lean_dec(v_sz_3759_);
v_i_boxed_3767_ = lean_unbox_usize(v_i_3760_);
lean_dec(v_i_3760_);
v_res_3768_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__3(v___x_3757_, v_as_3758_, v_sz_boxed_3766_, v_i_boxed_3767_, v_b_3761_, v___y_3762_, v___y_3763_, v___y_3764_);
lean_dec(v___y_3764_);
lean_dec_ref(v___y_3763_);
lean_dec_ref(v_as_3758_);
return v_res_3768_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__5(lean_object* v_a_3769_, lean_object* v_a_3770_){
_start:
{
if (lean_obj_tag(v_a_3769_) == 0)
{
lean_object* v___x_3771_; 
v___x_3771_ = l_List_reverse___redArg(v_a_3770_);
return v___x_3771_;
}
else
{
lean_object* v_head_3772_; lean_object* v_tail_3773_; lean_object* v___x_3775_; uint8_t v_isShared_3776_; uint8_t v_isSharedCheck_3782_; 
v_head_3772_ = lean_ctor_get(v_a_3769_, 0);
v_tail_3773_ = lean_ctor_get(v_a_3769_, 1);
v_isSharedCheck_3782_ = !lean_is_exclusive(v_a_3769_);
if (v_isSharedCheck_3782_ == 0)
{
v___x_3775_ = v_a_3769_;
v_isShared_3776_ = v_isSharedCheck_3782_;
goto v_resetjp_3774_;
}
else
{
lean_inc(v_tail_3773_);
lean_inc(v_head_3772_);
lean_dec(v_a_3769_);
v___x_3775_ = lean_box(0);
v_isShared_3776_ = v_isSharedCheck_3782_;
goto v_resetjp_3774_;
}
v_resetjp_3774_:
{
lean_object* v___x_3777_; lean_object* v___x_3779_; 
v___x_3777_ = l_Lean_MessageData_ofExpr(v_head_3772_);
if (v_isShared_3776_ == 0)
{
lean_ctor_set(v___x_3775_, 1, v_a_3770_);
lean_ctor_set(v___x_3775_, 0, v___x_3777_);
v___x_3779_ = v___x_3775_;
goto v_reusejp_3778_;
}
else
{
lean_object* v_reuseFailAlloc_3781_; 
v_reuseFailAlloc_3781_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3781_, 0, v___x_3777_);
lean_ctor_set(v_reuseFailAlloc_3781_, 1, v_a_3770_);
v___x_3779_ = v_reuseFailAlloc_3781_;
goto v_reusejp_3778_;
}
v_reusejp_3778_:
{
v_a_3769_ = v_tail_3773_;
v_a_3770_ = v___x_3779_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__0_spec__0___redArg(lean_object* v_a_3783_, lean_object* v_b_3784_, lean_object* v_x_3785_){
_start:
{
if (lean_obj_tag(v_x_3785_) == 0)
{
lean_dec(v_b_3784_);
lean_dec(v_a_3783_);
return v_x_3785_;
}
else
{
lean_object* v_key_3786_; lean_object* v_value_3787_; lean_object* v_tail_3788_; lean_object* v___x_3790_; uint8_t v_isShared_3791_; uint8_t v_isSharedCheck_3800_; 
v_key_3786_ = lean_ctor_get(v_x_3785_, 0);
v_value_3787_ = lean_ctor_get(v_x_3785_, 1);
v_tail_3788_ = lean_ctor_get(v_x_3785_, 2);
v_isSharedCheck_3800_ = !lean_is_exclusive(v_x_3785_);
if (v_isSharedCheck_3800_ == 0)
{
v___x_3790_ = v_x_3785_;
v_isShared_3791_ = v_isSharedCheck_3800_;
goto v_resetjp_3789_;
}
else
{
lean_inc(v_tail_3788_);
lean_inc(v_value_3787_);
lean_inc(v_key_3786_);
lean_dec(v_x_3785_);
v___x_3790_ = lean_box(0);
v_isShared_3791_ = v_isSharedCheck_3800_;
goto v_resetjp_3789_;
}
v_resetjp_3789_:
{
uint8_t v___x_3792_; 
v___x_3792_ = l_Lean_instBEqFVarId_beq(v_key_3786_, v_a_3783_);
if (v___x_3792_ == 0)
{
lean_object* v___x_3793_; lean_object* v___x_3795_; 
v___x_3793_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__0_spec__0___redArg(v_a_3783_, v_b_3784_, v_tail_3788_);
if (v_isShared_3791_ == 0)
{
lean_ctor_set(v___x_3790_, 2, v___x_3793_);
v___x_3795_ = v___x_3790_;
goto v_reusejp_3794_;
}
else
{
lean_object* v_reuseFailAlloc_3796_; 
v_reuseFailAlloc_3796_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3796_, 0, v_key_3786_);
lean_ctor_set(v_reuseFailAlloc_3796_, 1, v_value_3787_);
lean_ctor_set(v_reuseFailAlloc_3796_, 2, v___x_3793_);
v___x_3795_ = v_reuseFailAlloc_3796_;
goto v_reusejp_3794_;
}
v_reusejp_3794_:
{
return v___x_3795_;
}
}
else
{
lean_object* v___x_3798_; 
lean_dec(v_value_3787_);
lean_dec(v_key_3786_);
if (v_isShared_3791_ == 0)
{
lean_ctor_set(v___x_3790_, 1, v_b_3784_);
lean_ctor_set(v___x_3790_, 0, v_a_3783_);
v___x_3798_ = v___x_3790_;
goto v_reusejp_3797_;
}
else
{
lean_object* v_reuseFailAlloc_3799_; 
v_reuseFailAlloc_3799_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3799_, 0, v_a_3783_);
lean_ctor_set(v_reuseFailAlloc_3799_, 1, v_b_3784_);
lean_ctor_set(v_reuseFailAlloc_3799_, 2, v_tail_3788_);
v___x_3798_ = v_reuseFailAlloc_3799_;
goto v_reusejp_3797_;
}
v_reusejp_3797_:
{
return v___x_3798_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__0___redArg(lean_object* v_m_3801_, lean_object* v_a_3802_, lean_object* v_b_3803_){
_start:
{
lean_object* v_size_3804_; lean_object* v_buckets_3805_; lean_object* v___x_3807_; uint8_t v_isShared_3808_; uint8_t v_isSharedCheck_3848_; 
v_size_3804_ = lean_ctor_get(v_m_3801_, 0);
v_buckets_3805_ = lean_ctor_get(v_m_3801_, 1);
v_isSharedCheck_3848_ = !lean_is_exclusive(v_m_3801_);
if (v_isSharedCheck_3848_ == 0)
{
v___x_3807_ = v_m_3801_;
v_isShared_3808_ = v_isSharedCheck_3848_;
goto v_resetjp_3806_;
}
else
{
lean_inc(v_buckets_3805_);
lean_inc(v_size_3804_);
lean_dec(v_m_3801_);
v___x_3807_ = lean_box(0);
v_isShared_3808_ = v_isSharedCheck_3848_;
goto v_resetjp_3806_;
}
v_resetjp_3806_:
{
lean_object* v___x_3809_; uint64_t v___x_3810_; uint64_t v___x_3811_; uint64_t v___x_3812_; uint64_t v_fold_3813_; uint64_t v___x_3814_; uint64_t v___x_3815_; uint64_t v___x_3816_; size_t v___x_3817_; size_t v___x_3818_; size_t v___x_3819_; size_t v___x_3820_; size_t v___x_3821_; lean_object* v_bkt_3822_; uint8_t v___x_3823_; 
v___x_3809_ = lean_array_get_size(v_buckets_3805_);
v___x_3810_ = l_Lean_instHashableFVarId_hash(v_a_3802_);
v___x_3811_ = 32ULL;
v___x_3812_ = lean_uint64_shift_right(v___x_3810_, v___x_3811_);
v_fold_3813_ = lean_uint64_xor(v___x_3810_, v___x_3812_);
v___x_3814_ = 16ULL;
v___x_3815_ = lean_uint64_shift_right(v_fold_3813_, v___x_3814_);
v___x_3816_ = lean_uint64_xor(v_fold_3813_, v___x_3815_);
v___x_3817_ = lean_uint64_to_usize(v___x_3816_);
v___x_3818_ = lean_usize_of_nat(v___x_3809_);
v___x_3819_ = ((size_t)1ULL);
v___x_3820_ = lean_usize_sub(v___x_3818_, v___x_3819_);
v___x_3821_ = lean_usize_land(v___x_3817_, v___x_3820_);
v_bkt_3822_ = lean_array_uget_borrowed(v_buckets_3805_, v___x_3821_);
v___x_3823_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1_spec__2___redArg(v_a_3802_, v_bkt_3822_);
if (v___x_3823_ == 0)
{
lean_object* v___x_3824_; lean_object* v_size_x27_3825_; lean_object* v___x_3826_; lean_object* v_buckets_x27_3827_; lean_object* v___x_3828_; lean_object* v___x_3829_; lean_object* v___x_3830_; lean_object* v___x_3831_; lean_object* v___x_3832_; uint8_t v___x_3833_; 
v___x_3824_ = lean_unsigned_to_nat(1u);
v_size_x27_3825_ = lean_nat_add(v_size_3804_, v___x_3824_);
lean_dec(v_size_3804_);
lean_inc(v_bkt_3822_);
v___x_3826_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3826_, 0, v_a_3802_);
lean_ctor_set(v___x_3826_, 1, v_b_3803_);
lean_ctor_set(v___x_3826_, 2, v_bkt_3822_);
v_buckets_x27_3827_ = lean_array_uset(v_buckets_3805_, v___x_3821_, v___x_3826_);
v___x_3828_ = lean_unsigned_to_nat(4u);
v___x_3829_ = lean_nat_mul(v_size_x27_3825_, v___x_3828_);
v___x_3830_ = lean_unsigned_to_nat(3u);
v___x_3831_ = lean_nat_div(v___x_3829_, v___x_3830_);
lean_dec(v___x_3829_);
v___x_3832_ = lean_array_get_size(v_buckets_x27_3827_);
v___x_3833_ = lean_nat_dec_le(v___x_3831_, v___x_3832_);
lean_dec(v___x_3831_);
if (v___x_3833_ == 0)
{
lean_object* v_val_3834_; lean_object* v___x_3836_; 
v_val_3834_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__4___redArg(v_buckets_x27_3827_);
if (v_isShared_3808_ == 0)
{
lean_ctor_set(v___x_3807_, 1, v_val_3834_);
lean_ctor_set(v___x_3807_, 0, v_size_x27_3825_);
v___x_3836_ = v___x_3807_;
goto v_reusejp_3835_;
}
else
{
lean_object* v_reuseFailAlloc_3837_; 
v_reuseFailAlloc_3837_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3837_, 0, v_size_x27_3825_);
lean_ctor_set(v_reuseFailAlloc_3837_, 1, v_val_3834_);
v___x_3836_ = v_reuseFailAlloc_3837_;
goto v_reusejp_3835_;
}
v_reusejp_3835_:
{
return v___x_3836_;
}
}
else
{
lean_object* v___x_3839_; 
if (v_isShared_3808_ == 0)
{
lean_ctor_set(v___x_3807_, 1, v_buckets_x27_3827_);
lean_ctor_set(v___x_3807_, 0, v_size_x27_3825_);
v___x_3839_ = v___x_3807_;
goto v_reusejp_3838_;
}
else
{
lean_object* v_reuseFailAlloc_3840_; 
v_reuseFailAlloc_3840_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3840_, 0, v_size_x27_3825_);
lean_ctor_set(v_reuseFailAlloc_3840_, 1, v_buckets_x27_3827_);
v___x_3839_ = v_reuseFailAlloc_3840_;
goto v_reusejp_3838_;
}
v_reusejp_3838_:
{
return v___x_3839_;
}
}
}
else
{
lean_object* v___x_3841_; lean_object* v_buckets_x27_3842_; lean_object* v___x_3843_; lean_object* v___x_3844_; lean_object* v___x_3846_; 
lean_inc(v_bkt_3822_);
v___x_3841_ = lean_box(0);
v_buckets_x27_3842_ = lean_array_uset(v_buckets_3805_, v___x_3821_, v___x_3841_);
v___x_3843_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__0_spec__0___redArg(v_a_3802_, v_b_3803_, v_bkt_3822_);
v___x_3844_ = lean_array_uset(v_buckets_x27_3842_, v___x_3821_, v___x_3843_);
if (v_isShared_3808_ == 0)
{
lean_ctor_set(v___x_3807_, 1, v___x_3844_);
v___x_3846_ = v___x_3807_;
goto v_reusejp_3845_;
}
else
{
lean_object* v_reuseFailAlloc_3847_; 
v_reuseFailAlloc_3847_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3847_, 0, v_size_3804_);
lean_ctor_set(v_reuseFailAlloc_3847_, 1, v___x_3844_);
v___x_3846_ = v_reuseFailAlloc_3847_;
goto v_reusejp_3845_;
}
v_reusejp_3845_:
{
return v___x_3846_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__2___redArg(lean_object* v_as_3849_, size_t v_sz_3850_, size_t v_i_3851_, lean_object* v_b_3852_){
_start:
{
uint8_t v___x_3854_; 
v___x_3854_ = lean_usize_dec_lt(v_i_3851_, v_sz_3850_);
if (v___x_3854_ == 0)
{
lean_object* v___x_3855_; 
v___x_3855_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3855_, 0, v_b_3852_);
return v___x_3855_;
}
else
{
lean_object* v_snd_3856_; lean_object* v_fst_3857_; lean_object* v___x_3859_; uint8_t v_isShared_3860_; uint8_t v_isSharedCheck_3892_; 
v_snd_3856_ = lean_ctor_get(v_b_3852_, 1);
v_fst_3857_ = lean_ctor_get(v_b_3852_, 0);
v_isSharedCheck_3892_ = !lean_is_exclusive(v_b_3852_);
if (v_isSharedCheck_3892_ == 0)
{
v___x_3859_ = v_b_3852_;
v_isShared_3860_ = v_isSharedCheck_3892_;
goto v_resetjp_3858_;
}
else
{
lean_inc(v_snd_3856_);
lean_inc(v_fst_3857_);
lean_dec(v_b_3852_);
v___x_3859_ = lean_box(0);
v_isShared_3860_ = v_isSharedCheck_3892_;
goto v_resetjp_3858_;
}
v_resetjp_3858_:
{
lean_object* v_array_3861_; lean_object* v_start_3862_; lean_object* v_stop_3863_; uint8_t v___x_3864_; 
v_array_3861_ = lean_ctor_get(v_snd_3856_, 0);
v_start_3862_ = lean_ctor_get(v_snd_3856_, 1);
v_stop_3863_ = lean_ctor_get(v_snd_3856_, 2);
v___x_3864_ = lean_nat_dec_lt(v_start_3862_, v_stop_3863_);
if (v___x_3864_ == 0)
{
lean_object* v___x_3866_; 
if (v_isShared_3860_ == 0)
{
v___x_3866_ = v___x_3859_;
goto v_reusejp_3865_;
}
else
{
lean_object* v_reuseFailAlloc_3868_; 
v_reuseFailAlloc_3868_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3868_, 0, v_fst_3857_);
lean_ctor_set(v_reuseFailAlloc_3868_, 1, v_snd_3856_);
v___x_3866_ = v_reuseFailAlloc_3868_;
goto v_reusejp_3865_;
}
v_reusejp_3865_:
{
lean_object* v___x_3867_; 
v___x_3867_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3867_, 0, v___x_3866_);
return v___x_3867_;
}
}
else
{
lean_object* v___x_3870_; uint8_t v_isShared_3871_; uint8_t v_isSharedCheck_3888_; 
lean_inc(v_stop_3863_);
lean_inc(v_start_3862_);
lean_inc_ref(v_array_3861_);
v_isSharedCheck_3888_ = !lean_is_exclusive(v_snd_3856_);
if (v_isSharedCheck_3888_ == 0)
{
lean_object* v_unused_3889_; lean_object* v_unused_3890_; lean_object* v_unused_3891_; 
v_unused_3889_ = lean_ctor_get(v_snd_3856_, 2);
lean_dec(v_unused_3889_);
v_unused_3890_ = lean_ctor_get(v_snd_3856_, 1);
lean_dec(v_unused_3890_);
v_unused_3891_ = lean_ctor_get(v_snd_3856_, 0);
lean_dec(v_unused_3891_);
v___x_3870_ = v_snd_3856_;
v_isShared_3871_ = v_isSharedCheck_3888_;
goto v_resetjp_3869_;
}
else
{
lean_dec(v_snd_3856_);
v___x_3870_ = lean_box(0);
v_isShared_3871_ = v_isSharedCheck_3888_;
goto v_resetjp_3869_;
}
v_resetjp_3869_:
{
lean_object* v_a_3872_; lean_object* v___x_3873_; lean_object* v___x_3874_; lean_object* v___x_3875_; lean_object* v___x_3877_; 
v_a_3872_ = lean_array_uget_borrowed(v_as_3849_, v_i_3851_);
v___x_3873_ = lean_array_fget(v_array_3861_, v_start_3862_);
v___x_3874_ = lean_unsigned_to_nat(1u);
v___x_3875_ = lean_nat_add(v_start_3862_, v___x_3874_);
lean_dec(v_start_3862_);
if (v_isShared_3871_ == 0)
{
lean_ctor_set(v___x_3870_, 1, v___x_3875_);
v___x_3877_ = v___x_3870_;
goto v_reusejp_3876_;
}
else
{
lean_object* v_reuseFailAlloc_3887_; 
v_reuseFailAlloc_3887_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3887_, 0, v_array_3861_);
lean_ctor_set(v_reuseFailAlloc_3887_, 1, v___x_3875_);
lean_ctor_set(v_reuseFailAlloc_3887_, 2, v_stop_3863_);
v___x_3877_ = v_reuseFailAlloc_3887_;
goto v_reusejp_3876_;
}
v_reusejp_3876_:
{
lean_object* v___x_3878_; lean_object* v___x_3880_; 
v___x_3878_ = l_Lean_LocalDecl_fvarId(v_a_3872_);
lean_inc(v_a_3872_);
if (v_isShared_3860_ == 0)
{
lean_ctor_set(v___x_3859_, 1, v___x_3873_);
lean_ctor_set(v___x_3859_, 0, v_a_3872_);
v___x_3880_ = v___x_3859_;
goto v_reusejp_3879_;
}
else
{
lean_object* v_reuseFailAlloc_3886_; 
v_reuseFailAlloc_3886_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3886_, 0, v_a_3872_);
lean_ctor_set(v_reuseFailAlloc_3886_, 1, v___x_3873_);
v___x_3880_ = v_reuseFailAlloc_3886_;
goto v_reusejp_3879_;
}
v_reusejp_3879_:
{
lean_object* v___x_3881_; lean_object* v___x_3882_; size_t v___x_3883_; size_t v___x_3884_; 
v___x_3881_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__0___redArg(v_fst_3857_, v___x_3878_, v___x_3880_);
v___x_3882_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3882_, 0, v___x_3881_);
lean_ctor_set(v___x_3882_, 1, v___x_3877_);
v___x_3883_ = ((size_t)1ULL);
v___x_3884_ = lean_usize_add(v_i_3851_, v___x_3883_);
v_i_3851_ = v___x_3884_;
v_b_3852_ = v___x_3882_;
goto _start;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__2___redArg___boxed(lean_object* v_as_3893_, lean_object* v_sz_3894_, lean_object* v_i_3895_, lean_object* v_b_3896_, lean_object* v___y_3897_){
_start:
{
size_t v_sz_boxed_3898_; size_t v_i_boxed_3899_; lean_object* v_res_3900_; 
v_sz_boxed_3898_ = lean_unbox_usize(v_sz_3894_);
lean_dec(v_sz_3894_);
v_i_boxed_3899_ = lean_unbox_usize(v_i_3895_);
lean_dec(v_i_3895_);
v_res_3900_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__2___redArg(v_as_3893_, v_sz_boxed_3898_, v_i_boxed_3899_, v_b_3896_);
lean_dec_ref(v_as_3893_);
return v_res_3900_;
}
}
static lean_object* _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__2(void){
_start:
{
lean_object* v___x_3903_; lean_object* v___x_3904_; lean_object* v___x_3905_; lean_object* v___x_3906_; lean_object* v___x_3907_; lean_object* v___x_3908_; 
v___x_3903_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__1));
v___x_3904_ = lean_unsigned_to_nat(2u);
v___x_3905_ = lean_unsigned_to_nat(366u);
v___x_3906_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__0));
v___x_3907_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__2));
v___x_3908_ = l_mkPanicMessageWithDecl(v___x_3907_, v___x_3906_, v___x_3905_, v___x_3904_, v___x_3903_);
return v___x_3908_;
}
}
static lean_object* _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__4(void){
_start:
{
lean_object* v___x_3910_; lean_object* v___x_3911_; lean_object* v___x_3912_; lean_object* v___x_3913_; lean_object* v___x_3914_; lean_object* v___x_3915_; 
v___x_3910_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__3));
v___x_3911_ = lean_unsigned_to_nat(2u);
v___x_3912_ = lean_unsigned_to_nat(367u);
v___x_3913_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__0));
v___x_3914_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__2));
v___x_3915_ = l_mkPanicMessageWithDecl(v___x_3914_, v___x_3913_, v___x_3912_, v___x_3911_, v___x_3910_);
return v___x_3915_;
}
}
static lean_object* _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__5(void){
_start:
{
lean_object* v___x_3916_; lean_object* v___x_3917_; lean_object* v___x_3918_; 
v___x_3916_ = lean_box(0);
v___x_3917_ = lean_unsigned_to_nat(16u);
v___x_3918_ = lean_mk_array(v___x_3917_, v___x_3916_);
return v___x_3918_;
}
}
static lean_object* _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__6(void){
_start:
{
lean_object* v___x_3919_; lean_object* v___x_3920_; lean_object* v___x_3921_; 
v___x_3919_ = lean_obj_once(&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__5, &l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__5_once, _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__5);
v___x_3920_ = lean_unsigned_to_nat(0u);
v___x_3921_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3921_, 0, v___x_3920_);
lean_ctor_set(v___x_3921_, 1, v___x_3919_);
return v___x_3921_;
}
}
static lean_object* _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__8(void){
_start:
{
lean_object* v___x_3923_; lean_object* v___x_3924_; 
v___x_3923_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__7));
v___x_3924_ = l_Lean_stringToMessageData(v___x_3923_);
return v___x_3924_;
}
}
static lean_object* _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__10(void){
_start:
{
lean_object* v___x_3926_; lean_object* v___x_3927_; 
v___x_3926_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__9));
v___x_3927_ = l_Lean_stringToMessageData(v___x_3926_);
return v___x_3927_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls(lean_object* v_sortedDecls_3928_, lean_object* v_sortedArgs_3929_, lean_object* v_toSortDecls_3930_, lean_object* v_toSortArgs_3931_, lean_object* v_a_3932_, lean_object* v_a_3933_){
_start:
{
lean_object* v___y_3936_; lean_object* v___y_3955_; lean_object* v___y_3956_; lean_object* v___y_3957_; lean_object* v___y_3958_; lean_object* v_snd_3959_; lean_object* v___x_3961_; lean_object* v___x_3962_; uint8_t v___x_3963_; 
v___x_3961_ = lean_array_get_size(v_sortedDecls_3928_);
v___x_3962_ = lean_array_get_size(v_sortedArgs_3929_);
v___x_3963_ = lean_nat_dec_eq(v___x_3961_, v___x_3962_);
if (v___x_3963_ == 0)
{
lean_object* v___x_3964_; lean_object* v___x_3965_; 
lean_dec_ref(v_toSortArgs_3931_);
lean_dec_ref(v_sortedArgs_3929_);
lean_dec_ref(v_sortedDecls_3928_);
v___x_3964_ = lean_obj_once(&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__2, &l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__2_once, _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__2);
v___x_3965_ = l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__1(v___x_3964_, v_a_3932_, v_a_3933_);
return v___x_3965_;
}
else
{
lean_object* v___x_3966_; lean_object* v___x_3967_; uint8_t v___x_3968_; 
v___x_3966_ = lean_array_get_size(v_toSortDecls_3930_);
v___x_3967_ = lean_array_get_size(v_toSortArgs_3931_);
v___x_3968_ = lean_nat_dec_eq(v___x_3966_, v___x_3967_);
if (v___x_3968_ == 0)
{
lean_object* v___x_3969_; lean_object* v___x_3970_; 
lean_dec_ref(v_toSortArgs_3931_);
lean_dec_ref(v_sortedArgs_3929_);
lean_dec_ref(v_sortedDecls_3928_);
v___x_3969_ = lean_obj_once(&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__4, &l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__4_once, _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__4);
v___x_3970_ = l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__1(v___x_3969_, v_a_3932_, v_a_3933_);
return v___x_3970_;
}
else
{
lean_object* v___x_3971_; uint8_t v___x_3972_; 
v___x_3971_ = lean_unsigned_to_nat(0u);
v___x_3972_ = lean_nat_dec_eq(v___x_3966_, v___x_3971_);
if (v___x_3972_ == 0)
{
lean_object* v_options_3973_; lean_object* v_toCold_3974_; uint8_t v_hasTrace_3975_; lean_object* v___x_3976_; lean_object* v_cls_3977_; lean_object* v___y_3979_; lean_object* v___y_3980_; 
v_options_3973_ = lean_ctor_get(v_a_3932_, 1);
v_toCold_3974_ = lean_ctor_get(v_a_3932_, 0);
v_hasTrace_3975_ = lean_ctor_get_uint8(v_options_3973_, sizeof(void*)*1);
v___x_3976_ = l_Lean_instEmptyCollectionFVarIdHashSet;
v_cls_3977_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__10));
if (v_hasTrace_3975_ == 0)
{
v___y_3979_ = v_a_3932_;
v___y_3980_ = v_a_3933_;
goto v___jp_3978_;
}
else
{
lean_object* v_inheritedTraceOptions_4081_; lean_object* v___x_4082_; uint8_t v___x_4083_; 
v_inheritedTraceOptions_4081_ = lean_ctor_get(v_toCold_3974_, 4);
v___x_4082_ = lean_obj_once(&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__13, &l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__13_once, _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__13);
v___x_4083_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4081_, v_options_3973_, v___x_4082_);
if (v___x_4083_ == 0)
{
v___y_3979_ = v_a_3932_;
v___y_3980_ = v_a_3933_;
goto v___jp_3978_;
}
else
{
lean_object* v___x_4084_; lean_object* v___x_4085_; 
v___x_4084_ = lean_obj_once(&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__10, &l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__10_once, _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__10);
v___x_4085_ = l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__6(v_cls_3977_, v___x_4084_, v_a_3932_, v_a_3933_);
if (lean_obj_tag(v___x_4085_) == 0)
{
lean_dec_ref_known(v___x_4085_, 1);
v___y_3979_ = v_a_3932_;
v___y_3980_ = v_a_3933_;
goto v___jp_3978_;
}
else
{
lean_object* v_a_4086_; lean_object* v___x_4088_; uint8_t v_isShared_4089_; uint8_t v_isSharedCheck_4093_; 
lean_dec_ref(v_toSortArgs_3931_);
lean_dec_ref(v_sortedArgs_3929_);
lean_dec_ref(v_sortedDecls_3928_);
v_a_4086_ = lean_ctor_get(v___x_4085_, 0);
v_isSharedCheck_4093_ = !lean_is_exclusive(v___x_4085_);
if (v_isSharedCheck_4093_ == 0)
{
v___x_4088_ = v___x_4085_;
v_isShared_4089_ = v_isSharedCheck_4093_;
goto v_resetjp_4087_;
}
else
{
lean_inc(v_a_4086_);
lean_dec(v___x_4085_);
v___x_4088_ = lean_box(0);
v_isShared_4089_ = v_isSharedCheck_4093_;
goto v_resetjp_4087_;
}
v_resetjp_4087_:
{
lean_object* v___x_4091_; 
if (v_isShared_4089_ == 0)
{
v___x_4091_ = v___x_4088_;
goto v_reusejp_4090_;
}
else
{
lean_object* v_reuseFailAlloc_4092_; 
v_reuseFailAlloc_4092_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4092_, 0, v_a_4086_);
v___x_4091_ = v_reuseFailAlloc_4092_;
goto v_reusejp_4090_;
}
v_reusejp_4090_:
{
return v___x_4091_;
}
}
}
}
}
v___jp_3978_:
{
lean_object* v___x_3981_; lean_object* v___x_3982_; lean_object* v___x_3983_; size_t v_sz_3984_; size_t v___x_3985_; lean_object* v___x_3986_; 
v___x_3981_ = lean_obj_once(&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__6, &l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__6_once, _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__6);
v___x_3982_ = l_Array_toSubarray___redArg(v_sortedArgs_3929_, v___x_3971_, v___x_3962_);
v___x_3983_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3983_, 0, v___x_3981_);
lean_ctor_set(v___x_3983_, 1, v___x_3982_);
v_sz_3984_ = lean_array_size(v_sortedDecls_3928_);
v___x_3985_ = ((size_t)0ULL);
v___x_3986_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__2___redArg(v_sortedDecls_3928_, v_sz_3984_, v___x_3985_, v___x_3983_);
if (lean_obj_tag(v___x_3986_) == 0)
{
lean_object* v_a_3987_; lean_object* v_fst_3988_; lean_object* v___x_3990_; uint8_t v_isShared_3991_; uint8_t v_isSharedCheck_4071_; 
v_a_3987_ = lean_ctor_get(v___x_3986_, 0);
lean_inc(v_a_3987_);
lean_dec_ref_known(v___x_3986_, 1);
v_fst_3988_ = lean_ctor_get(v_a_3987_, 0);
v_isSharedCheck_4071_ = !lean_is_exclusive(v_a_3987_);
if (v_isSharedCheck_4071_ == 0)
{
lean_object* v_unused_4072_; 
v_unused_4072_ = lean_ctor_get(v_a_3987_, 1);
lean_dec(v_unused_4072_);
v___x_3990_ = v_a_3987_;
v_isShared_3991_ = v_isSharedCheck_4071_;
goto v_resetjp_3989_;
}
else
{
lean_inc(v_fst_3988_);
lean_dec(v_a_3987_);
v___x_3990_ = lean_box(0);
v_isShared_3991_ = v_isSharedCheck_4071_;
goto v_resetjp_3989_;
}
v_resetjp_3989_:
{
lean_object* v___x_3992_; lean_object* v___x_3994_; 
v___x_3992_ = l_Array_toSubarray___redArg(v_toSortArgs_3931_, v___x_3971_, v___x_3967_);
if (v_isShared_3991_ == 0)
{
lean_ctor_set(v___x_3990_, 1, v___x_3992_);
v___x_3994_ = v___x_3990_;
goto v_reusejp_3993_;
}
else
{
lean_object* v_reuseFailAlloc_4070_; 
v_reuseFailAlloc_4070_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4070_, 0, v_fst_3988_);
lean_ctor_set(v_reuseFailAlloc_4070_, 1, v___x_3992_);
v___x_3994_ = v_reuseFailAlloc_4070_;
goto v_reusejp_3993_;
}
v_reusejp_3993_:
{
size_t v_sz_3995_; lean_object* v___x_3996_; 
v_sz_3995_ = lean_array_size(v_toSortDecls_3930_);
v___x_3996_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__2___redArg(v_toSortDecls_3930_, v_sz_3995_, v___x_3985_, v___x_3994_);
if (lean_obj_tag(v___x_3996_) == 0)
{
lean_object* v_a_3997_; lean_object* v_fst_3998_; lean_object* v_size_3999_; lean_object* v___x_4000_; lean_object* v___x_4001_; lean_object* v___x_4002_; lean_object* v___x_4003_; 
v_a_3997_ = lean_ctor_get(v___x_3996_, 0);
lean_inc(v_a_3997_);
lean_dec_ref_known(v___x_3996_, 1);
v_fst_3998_ = lean_ctor_get(v_a_3997_, 0);
lean_inc_n(v_fst_3998_, 2);
lean_dec(v_a_3997_);
v_size_3999_ = lean_ctor_get(v_fst_3998_, 0);
v___x_4000_ = lean_mk_empty_array_with_capacity(v_size_3999_);
lean_inc_ref(v___x_4000_);
v___x_4001_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4001_, 0, v___x_3976_);
lean_ctor_set(v___x_4001_, 1, v___x_3976_);
lean_ctor_set(v___x_4001_, 2, v___x_4000_);
lean_ctor_set(v___x_4001_, 3, v___x_4000_);
v___x_4002_ = lean_box(0);
v___x_4003_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__3(v_fst_3998_, v_sortedDecls_3928_, v_sz_3984_, v___x_3985_, v___x_4002_, v___x_4001_, v___y_3979_, v___y_3980_);
lean_dec_ref(v_sortedDecls_3928_);
if (lean_obj_tag(v___x_4003_) == 0)
{
lean_object* v_a_4004_; lean_object* v_snd_4005_; lean_object* v___x_4006_; 
v_a_4004_ = lean_ctor_get(v___x_4003_, 0);
lean_inc(v_a_4004_);
lean_dec_ref_known(v___x_4003_, 1);
v_snd_4005_ = lean_ctor_get(v_a_4004_, 1);
lean_inc(v_snd_4005_);
lean_dec(v_a_4004_);
v___x_4006_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__3(v_fst_3998_, v_toSortDecls_3930_, v_sz_3995_, v___x_3985_, v___x_4002_, v_snd_4005_, v___y_3979_, v___y_3980_);
if (lean_obj_tag(v___x_4006_) == 0)
{
lean_object* v_a_4007_; lean_object* v_snd_4008_; lean_object* v___x_4010_; uint8_t v_isShared_4011_; uint8_t v_isSharedCheck_4044_; 
v_a_4007_ = lean_ctor_get(v___x_4006_, 0);
lean_inc(v_a_4007_);
lean_dec_ref_known(v___x_4006_, 1);
v_snd_4008_ = lean_ctor_get(v_a_4007_, 1);
v_isSharedCheck_4044_ = !lean_is_exclusive(v_a_4007_);
if (v_isSharedCheck_4044_ == 0)
{
lean_object* v_unused_4045_; 
v_unused_4045_ = lean_ctor_get(v_a_4007_, 0);
lean_dec(v_unused_4045_);
v___x_4010_ = v_a_4007_;
v_isShared_4011_ = v_isSharedCheck_4044_;
goto v_resetjp_4009_;
}
else
{
lean_inc(v_snd_4008_);
lean_dec(v_a_4007_);
v___x_4010_ = lean_box(0);
v_isShared_4011_ = v_isSharedCheck_4044_;
goto v_resetjp_4009_;
}
v_resetjp_4009_:
{
lean_object* v_options_4012_; lean_object* v_newDecls_4013_; lean_object* v_newArgs_4014_; lean_object* v_toCold_4015_; uint8_t v_hasTrace_4016_; lean_object* v___f_4017_; 
v_options_4012_ = lean_ctor_get(v___y_3979_, 1);
v_newDecls_4013_ = lean_ctor_get(v_snd_4008_, 2);
v_newArgs_4014_ = lean_ctor_get(v_snd_4008_, 3);
v_toCold_4015_ = lean_ctor_get(v___y_3979_, 0);
v_hasTrace_4016_ = lean_ctor_get_uint8(v_options_4012_, sizeof(void*)*1);
lean_inc_ref(v_newArgs_4014_);
lean_inc_ref(v_newDecls_4013_);
v___f_4017_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___lam__0___boxed), 7, 2);
lean_closure_set(v___f_4017_, 0, v_newDecls_4013_);
lean_closure_set(v___f_4017_, 1, v_newArgs_4014_);
if (v_hasTrace_4016_ == 0)
{
lean_del_object(v___x_4010_);
v___y_3955_ = v___y_3980_;
v___y_3956_ = v___y_3979_;
v___y_3957_ = v___f_4017_;
v___y_3958_ = v___x_4002_;
v_snd_3959_ = v_snd_4008_;
goto v___jp_3954_;
}
else
{
lean_object* v_inheritedTraceOptions_4018_; lean_object* v___x_4019_; uint8_t v___x_4020_; 
v_inheritedTraceOptions_4018_ = lean_ctor_get(v_toCold_4015_, 4);
v___x_4019_ = lean_obj_once(&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__13, &l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__13_once, _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__13);
v___x_4020_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4018_, v_options_4012_, v___x_4019_);
if (v___x_4020_ == 0)
{
lean_del_object(v___x_4010_);
v___y_3955_ = v___y_3980_;
v___y_3956_ = v___y_3979_;
v___y_3957_ = v___f_4017_;
v___y_3958_ = v___x_4002_;
v_snd_3959_ = v_snd_4008_;
goto v___jp_3954_;
}
else
{
lean_object* v___x_4021_; size_t v_sz_4022_; lean_object* v___x_4023_; lean_object* v___x_4024_; lean_object* v___x_4025_; lean_object* v___x_4026_; lean_object* v___x_4027_; lean_object* v___x_4029_; 
lean_inc_ref(v_newArgs_4014_);
lean_inc_ref_n(v_newDecls_4013_, 2);
lean_dec_ref(v___f_4017_);
v___x_4021_ = lean_obj_once(&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__8, &l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__8_once, _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__8);
v_sz_4022_ = lean_array_size(v_newDecls_4013_);
v___x_4023_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__4(v_sz_4022_, v___x_3985_, v_newDecls_4013_);
v___x_4024_ = lean_array_to_list(v___x_4023_);
v___x_4025_ = lean_box(0);
v___x_4026_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__5(v___x_4024_, v___x_4025_);
v___x_4027_ = l_Lean_MessageData_ofList(v___x_4026_);
if (v_isShared_4011_ == 0)
{
lean_ctor_set_tag(v___x_4010_, 7);
lean_ctor_set(v___x_4010_, 1, v___x_4027_);
lean_ctor_set(v___x_4010_, 0, v___x_4021_);
v___x_4029_ = v___x_4010_;
goto v_reusejp_4028_;
}
else
{
lean_object* v_reuseFailAlloc_4043_; 
v_reuseFailAlloc_4043_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4043_, 0, v___x_4021_);
lean_ctor_set(v_reuseFailAlloc_4043_, 1, v___x_4027_);
v___x_4029_ = v_reuseFailAlloc_4043_;
goto v_reusejp_4028_;
}
v_reusejp_4028_:
{
lean_object* v___x_4030_; 
v___x_4030_ = l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6(v_cls_3977_, v___x_4029_, v_snd_4008_, v___y_3979_, v___y_3980_);
if (lean_obj_tag(v___x_4030_) == 0)
{
lean_object* v_a_4031_; lean_object* v_fst_4032_; lean_object* v_snd_4033_; lean_object* v___x_4034_; 
v_a_4031_ = lean_ctor_get(v___x_4030_, 0);
lean_inc(v_a_4031_);
lean_dec_ref_known(v___x_4030_, 1);
v_fst_4032_ = lean_ctor_get(v_a_4031_, 0);
lean_inc(v_fst_4032_);
v_snd_4033_ = lean_ctor_get(v_a_4031_, 1);
lean_inc(v_snd_4033_);
lean_dec(v_a_4031_);
v___x_4034_ = l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___lam__0(v_newDecls_4013_, v_newArgs_4014_, v_fst_4032_, v_snd_4033_, v___y_3979_, v___y_3980_);
v___y_3936_ = v___x_4034_;
goto v___jp_3935_;
}
else
{
lean_object* v_a_4035_; lean_object* v___x_4037_; uint8_t v_isShared_4038_; uint8_t v_isSharedCheck_4042_; 
lean_dec_ref(v_newArgs_4014_);
lean_dec_ref(v_newDecls_4013_);
v_a_4035_ = lean_ctor_get(v___x_4030_, 0);
v_isSharedCheck_4042_ = !lean_is_exclusive(v___x_4030_);
if (v_isSharedCheck_4042_ == 0)
{
v___x_4037_ = v___x_4030_;
v_isShared_4038_ = v_isSharedCheck_4042_;
goto v_resetjp_4036_;
}
else
{
lean_inc(v_a_4035_);
lean_dec(v___x_4030_);
v___x_4037_ = lean_box(0);
v_isShared_4038_ = v_isSharedCheck_4042_;
goto v_resetjp_4036_;
}
v_resetjp_4036_:
{
lean_object* v___x_4040_; 
if (v_isShared_4038_ == 0)
{
v___x_4040_ = v___x_4037_;
goto v_reusejp_4039_;
}
else
{
lean_object* v_reuseFailAlloc_4041_; 
v_reuseFailAlloc_4041_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4041_, 0, v_a_4035_);
v___x_4040_ = v_reuseFailAlloc_4041_;
goto v_reusejp_4039_;
}
v_reusejp_4039_:
{
return v___x_4040_;
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
lean_object* v_a_4046_; lean_object* v___x_4048_; uint8_t v_isShared_4049_; uint8_t v_isSharedCheck_4053_; 
v_a_4046_ = lean_ctor_get(v___x_4006_, 0);
v_isSharedCheck_4053_ = !lean_is_exclusive(v___x_4006_);
if (v_isSharedCheck_4053_ == 0)
{
v___x_4048_ = v___x_4006_;
v_isShared_4049_ = v_isSharedCheck_4053_;
goto v_resetjp_4047_;
}
else
{
lean_inc(v_a_4046_);
lean_dec(v___x_4006_);
v___x_4048_ = lean_box(0);
v_isShared_4049_ = v_isSharedCheck_4053_;
goto v_resetjp_4047_;
}
v_resetjp_4047_:
{
lean_object* v___x_4051_; 
if (v_isShared_4049_ == 0)
{
v___x_4051_ = v___x_4048_;
goto v_reusejp_4050_;
}
else
{
lean_object* v_reuseFailAlloc_4052_; 
v_reuseFailAlloc_4052_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4052_, 0, v_a_4046_);
v___x_4051_ = v_reuseFailAlloc_4052_;
goto v_reusejp_4050_;
}
v_reusejp_4050_:
{
return v___x_4051_;
}
}
}
}
else
{
lean_object* v_a_4054_; lean_object* v___x_4056_; uint8_t v_isShared_4057_; uint8_t v_isSharedCheck_4061_; 
lean_dec(v_fst_3998_);
v_a_4054_ = lean_ctor_get(v___x_4003_, 0);
v_isSharedCheck_4061_ = !lean_is_exclusive(v___x_4003_);
if (v_isSharedCheck_4061_ == 0)
{
v___x_4056_ = v___x_4003_;
v_isShared_4057_ = v_isSharedCheck_4061_;
goto v_resetjp_4055_;
}
else
{
lean_inc(v_a_4054_);
lean_dec(v___x_4003_);
v___x_4056_ = lean_box(0);
v_isShared_4057_ = v_isSharedCheck_4061_;
goto v_resetjp_4055_;
}
v_resetjp_4055_:
{
lean_object* v___x_4059_; 
if (v_isShared_4057_ == 0)
{
v___x_4059_ = v___x_4056_;
goto v_reusejp_4058_;
}
else
{
lean_object* v_reuseFailAlloc_4060_; 
v_reuseFailAlloc_4060_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4060_, 0, v_a_4054_);
v___x_4059_ = v_reuseFailAlloc_4060_;
goto v_reusejp_4058_;
}
v_reusejp_4058_:
{
return v___x_4059_;
}
}
}
}
else
{
lean_object* v_a_4062_; lean_object* v___x_4064_; uint8_t v_isShared_4065_; uint8_t v_isSharedCheck_4069_; 
lean_dec_ref(v_sortedDecls_3928_);
v_a_4062_ = lean_ctor_get(v___x_3996_, 0);
v_isSharedCheck_4069_ = !lean_is_exclusive(v___x_3996_);
if (v_isSharedCheck_4069_ == 0)
{
v___x_4064_ = v___x_3996_;
v_isShared_4065_ = v_isSharedCheck_4069_;
goto v_resetjp_4063_;
}
else
{
lean_inc(v_a_4062_);
lean_dec(v___x_3996_);
v___x_4064_ = lean_box(0);
v_isShared_4065_ = v_isSharedCheck_4069_;
goto v_resetjp_4063_;
}
v_resetjp_4063_:
{
lean_object* v___x_4067_; 
if (v_isShared_4065_ == 0)
{
v___x_4067_ = v___x_4064_;
goto v_reusejp_4066_;
}
else
{
lean_object* v_reuseFailAlloc_4068_; 
v_reuseFailAlloc_4068_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4068_, 0, v_a_4062_);
v___x_4067_ = v_reuseFailAlloc_4068_;
goto v_reusejp_4066_;
}
v_reusejp_4066_:
{
return v___x_4067_;
}
}
}
}
}
}
else
{
lean_object* v_a_4073_; lean_object* v___x_4075_; uint8_t v_isShared_4076_; uint8_t v_isSharedCheck_4080_; 
lean_dec_ref(v_toSortArgs_3931_);
lean_dec_ref(v_sortedDecls_3928_);
v_a_4073_ = lean_ctor_get(v___x_3986_, 0);
v_isSharedCheck_4080_ = !lean_is_exclusive(v___x_3986_);
if (v_isSharedCheck_4080_ == 0)
{
v___x_4075_ = v___x_3986_;
v_isShared_4076_ = v_isSharedCheck_4080_;
goto v_resetjp_4074_;
}
else
{
lean_inc(v_a_4073_);
lean_dec(v___x_3986_);
v___x_4075_ = lean_box(0);
v_isShared_4076_ = v_isSharedCheck_4080_;
goto v_resetjp_4074_;
}
v_resetjp_4074_:
{
lean_object* v___x_4078_; 
if (v_isShared_4076_ == 0)
{
v___x_4078_ = v___x_4075_;
goto v_reusejp_4077_;
}
else
{
lean_object* v_reuseFailAlloc_4079_; 
v_reuseFailAlloc_4079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4079_, 0, v_a_4073_);
v___x_4078_ = v_reuseFailAlloc_4079_;
goto v_reusejp_4077_;
}
v_reusejp_4077_:
{
return v___x_4078_;
}
}
}
}
}
else
{
lean_object* v___x_4094_; lean_object* v___x_4095_; 
lean_dec_ref(v_toSortArgs_3931_);
v___x_4094_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4094_, 0, v_sortedDecls_3928_);
lean_ctor_set(v___x_4094_, 1, v_sortedArgs_3929_);
v___x_4095_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4095_, 0, v___x_4094_);
return v___x_4095_;
}
}
}
v___jp_3935_:
{
if (lean_obj_tag(v___y_3936_) == 0)
{
lean_object* v_a_3937_; lean_object* v___x_3939_; uint8_t v_isShared_3940_; uint8_t v_isSharedCheck_3945_; 
v_a_3937_ = lean_ctor_get(v___y_3936_, 0);
v_isSharedCheck_3945_ = !lean_is_exclusive(v___y_3936_);
if (v_isSharedCheck_3945_ == 0)
{
v___x_3939_ = v___y_3936_;
v_isShared_3940_ = v_isSharedCheck_3945_;
goto v_resetjp_3938_;
}
else
{
lean_inc(v_a_3937_);
lean_dec(v___y_3936_);
v___x_3939_ = lean_box(0);
v_isShared_3940_ = v_isSharedCheck_3945_;
goto v_resetjp_3938_;
}
v_resetjp_3938_:
{
lean_object* v_fst_3941_; lean_object* v___x_3943_; 
v_fst_3941_ = lean_ctor_get(v_a_3937_, 0);
lean_inc(v_fst_3941_);
lean_dec(v_a_3937_);
if (v_isShared_3940_ == 0)
{
lean_ctor_set(v___x_3939_, 0, v_fst_3941_);
v___x_3943_ = v___x_3939_;
goto v_reusejp_3942_;
}
else
{
lean_object* v_reuseFailAlloc_3944_; 
v_reuseFailAlloc_3944_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3944_, 0, v_fst_3941_);
v___x_3943_ = v_reuseFailAlloc_3944_;
goto v_reusejp_3942_;
}
v_reusejp_3942_:
{
return v___x_3943_;
}
}
}
else
{
lean_object* v_a_3946_; lean_object* v___x_3948_; uint8_t v_isShared_3949_; uint8_t v_isSharedCheck_3953_; 
v_a_3946_ = lean_ctor_get(v___y_3936_, 0);
v_isSharedCheck_3953_ = !lean_is_exclusive(v___y_3936_);
if (v_isSharedCheck_3953_ == 0)
{
v___x_3948_ = v___y_3936_;
v_isShared_3949_ = v_isSharedCheck_3953_;
goto v_resetjp_3947_;
}
else
{
lean_inc(v_a_3946_);
lean_dec(v___y_3936_);
v___x_3948_ = lean_box(0);
v_isShared_3949_ = v_isSharedCheck_3953_;
goto v_resetjp_3947_;
}
v_resetjp_3947_:
{
lean_object* v___x_3951_; 
if (v_isShared_3949_ == 0)
{
v___x_3951_ = v___x_3948_;
goto v_reusejp_3950_;
}
else
{
lean_object* v_reuseFailAlloc_3952_; 
v_reuseFailAlloc_3952_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3952_, 0, v_a_3946_);
v___x_3951_ = v_reuseFailAlloc_3952_;
goto v_reusejp_3950_;
}
v_reusejp_3950_:
{
return v___x_3951_;
}
}
}
}
v___jp_3954_:
{
lean_object* v___x_3960_; 
lean_inc(v___y_3955_);
lean_inc_ref(v___y_3956_);
v___x_3960_ = lean_apply_5(v___y_3957_, v___y_3958_, v_snd_3959_, v___y_3956_, v___y_3955_, lean_box(0));
v___y_3936_ = v___x_3960_;
goto v___jp_3935_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___boxed(lean_object* v_sortedDecls_4096_, lean_object* v_sortedArgs_4097_, lean_object* v_toSortDecls_4098_, lean_object* v_toSortArgs_4099_, lean_object* v_a_4100_, lean_object* v_a_4101_, lean_object* v_a_4102_){
_start:
{
lean_object* v_res_4103_; 
v_res_4103_ = l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls(v_sortedDecls_4096_, v_sortedArgs_4097_, v_toSortDecls_4098_, v_toSortArgs_4099_, v_a_4100_, v_a_4101_);
lean_dec(v_a_4101_);
lean_dec_ref(v_a_4100_);
lean_dec_ref(v_toSortDecls_4098_);
return v_res_4103_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__0(lean_object* v_00_u03b2_4104_, lean_object* v_m_4105_, lean_object* v_a_4106_, lean_object* v_b_4107_){
_start:
{
lean_object* v___x_4108_; 
v___x_4108_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__0___redArg(v_m_4105_, v_a_4106_, v_b_4107_);
return v___x_4108_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__2(lean_object* v_as_4109_, size_t v_sz_4110_, size_t v_i_4111_, lean_object* v_b_4112_, lean_object* v___y_4113_, lean_object* v___y_4114_){
_start:
{
lean_object* v___x_4116_; 
v___x_4116_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__2___redArg(v_as_4109_, v_sz_4110_, v_i_4111_, v_b_4112_);
return v___x_4116_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__2___boxed(lean_object* v_as_4117_, lean_object* v_sz_4118_, lean_object* v_i_4119_, lean_object* v_b_4120_, lean_object* v___y_4121_, lean_object* v___y_4122_, lean_object* v___y_4123_){
_start:
{
size_t v_sz_boxed_4124_; size_t v_i_boxed_4125_; lean_object* v_res_4126_; 
v_sz_boxed_4124_ = lean_unbox_usize(v_sz_4118_);
lean_dec(v_sz_4118_);
v_i_boxed_4125_ = lean_unbox_usize(v_i_4119_);
lean_dec(v_i_4119_);
v_res_4126_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__2(v_as_4117_, v_sz_boxed_4124_, v_i_boxed_4125_, v_b_4120_, v___y_4121_, v___y_4122_);
lean_dec(v___y_4122_);
lean_dec_ref(v___y_4121_);
lean_dec_ref(v_as_4117_);
return v_res_4126_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__0_spec__0(lean_object* v_00_u03b2_4127_, lean_object* v_a_4128_, lean_object* v_b_4129_, lean_object* v_x_4130_){
_start:
{
lean_object* v___x_4131_; 
v___x_4131_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__0_spec__0___redArg(v_a_4128_, v_b_4129_, v_x_4130_);
return v___x_4131_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Closure_mkValueTypeClosure_spec__0(lean_object* v_msg_4133_, lean_object* v___y_4134_, lean_object* v___y_4135_, lean_object* v___y_4136_, lean_object* v___y_4137_){
_start:
{
lean_object* v___f_4139_; lean_object* v___x_1240__overap_4140_; lean_object* v___x_4141_; 
v___f_4139_ = ((lean_object*)(l_panic___at___00Lean_Meta_Closure_mkValueTypeClosure_spec__0___closed__0));
v___x_1240__overap_4140_ = lean_panic_fn_borrowed(v___f_4139_, v_msg_4133_);
lean_inc(v___y_4137_);
lean_inc_ref(v___y_4136_);
lean_inc(v___y_4135_);
lean_inc_ref(v___y_4134_);
v___x_4141_ = lean_apply_5(v___x_1240__overap_4140_, v___y_4134_, v___y_4135_, v___y_4136_, v___y_4137_, lean_box(0));
return v___x_4141_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Closure_mkValueTypeClosure_spec__0___boxed(lean_object* v_msg_4142_, lean_object* v___y_4143_, lean_object* v___y_4144_, lean_object* v___y_4145_, lean_object* v___y_4146_, lean_object* v___y_4147_){
_start:
{
lean_object* v_res_4148_; 
v_res_4148_ = l_panic___at___00Lean_Meta_Closure_mkValueTypeClosure_spec__0(v_msg_4142_, v___y_4143_, v___y_4144_, v___y_4145_, v___y_4146_);
lean_dec(v___y_4146_);
lean_dec_ref(v___y_4145_);
lean_dec(v___y_4144_);
lean_dec_ref(v___y_4143_);
return v_res_4148_;
}
}
static lean_object* _init_l_Lean_Meta_Closure_mkValueTypeClosure___closed__0(void){
_start:
{
lean_object* v___x_4149_; lean_object* v___x_4150_; lean_object* v___x_4151_; 
v___x_4149_ = lean_box(0);
v___x_4150_ = lean_unsigned_to_nat(16u);
v___x_4151_ = lean_mk_array(v___x_4150_, v___x_4149_);
return v___x_4151_;
}
}
static lean_object* _init_l_Lean_Meta_Closure_mkValueTypeClosure___closed__1(void){
_start:
{
lean_object* v___x_4152_; lean_object* v___x_4153_; lean_object* v___x_4154_; 
v___x_4152_ = lean_obj_once(&l_Lean_Meta_Closure_mkValueTypeClosure___closed__0, &l_Lean_Meta_Closure_mkValueTypeClosure___closed__0_once, _init_l_Lean_Meta_Closure_mkValueTypeClosure___closed__0);
v___x_4153_ = lean_unsigned_to_nat(0u);
v___x_4154_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4154_, 0, v___x_4153_);
lean_ctor_set(v___x_4154_, 1, v___x_4152_);
return v___x_4154_;
}
}
static lean_object* _init_l_Lean_Meta_Closure_mkValueTypeClosure___closed__3(void){
_start:
{
lean_object* v___x_4157_; lean_object* v___x_4158_; lean_object* v___x_4159_; lean_object* v___x_4160_; 
v___x_4157_ = lean_unsigned_to_nat(1u);
v___x_4158_ = ((lean_object*)(l_Lean_Meta_Closure_mkValueTypeClosure___closed__2));
v___x_4159_ = lean_obj_once(&l_Lean_Meta_Closure_mkValueTypeClosure___closed__1, &l_Lean_Meta_Closure_mkValueTypeClosure___closed__1_once, _init_l_Lean_Meta_Closure_mkValueTypeClosure___closed__1);
v___x_4160_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_4160_, 0, v___x_4159_);
lean_ctor_set(v___x_4160_, 1, v___x_4159_);
lean_ctor_set(v___x_4160_, 2, v___x_4158_);
lean_ctor_set(v___x_4160_, 3, v___x_4157_);
lean_ctor_set(v___x_4160_, 4, v___x_4158_);
lean_ctor_set(v___x_4160_, 5, v___x_4158_);
lean_ctor_set(v___x_4160_, 6, v___x_4158_);
lean_ctor_set(v___x_4160_, 7, v___x_4158_);
lean_ctor_set(v___x_4160_, 8, v___x_4157_);
lean_ctor_set(v___x_4160_, 9, v___x_4158_);
lean_ctor_set(v___x_4160_, 10, v___x_4158_);
lean_ctor_set(v___x_4160_, 11, v___x_4158_);
return v___x_4160_;
}
}
static lean_object* _init_l_Lean_Meta_Closure_mkValueTypeClosure___closed__6(void){
_start:
{
lean_object* v___x_4163_; lean_object* v___x_4164_; lean_object* v___x_4165_; lean_object* v___x_4166_; lean_object* v___x_4167_; lean_object* v___x_4168_; 
v___x_4163_ = ((lean_object*)(l_Lean_Meta_Closure_mkValueTypeClosure___closed__5));
v___x_4164_ = lean_unsigned_to_nat(2u);
v___x_4165_ = lean_unsigned_to_nat(417u);
v___x_4166_ = ((lean_object*)(l_Lean_Meta_Closure_mkValueTypeClosure___closed__4));
v___x_4167_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__2));
v___x_4168_ = l_mkPanicMessageWithDecl(v___x_4167_, v___x_4166_, v___x_4165_, v___x_4164_, v___x_4163_);
return v___x_4168_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkValueTypeClosure(lean_object* v_type_4169_, lean_object* v_value_4170_, uint8_t v_zetaDelta_4171_, lean_object* v_a_4172_, lean_object* v_a_4173_, lean_object* v_a_4174_, lean_object* v_a_4175_){
_start:
{
lean_object* v___x_4177_; lean_object* v___x_4178_; lean_object* v___x_4179_; 
v___x_4177_ = lean_obj_once(&l_Lean_Meta_Closure_mkValueTypeClosure___closed__3, &l_Lean_Meta_Closure_mkValueTypeClosure___closed__3_once, _init_l_Lean_Meta_Closure_mkValueTypeClosure___closed__3);
v___x_4178_ = lean_st_mk_ref(v___x_4177_);
v___x_4179_ = l_Lean_Meta_Closure_mkValueTypeClosureAux(v_type_4169_, v_value_4170_, v_zetaDelta_4171_, v___x_4178_, v_a_4172_, v_a_4173_, v_a_4174_, v_a_4175_);
if (lean_obj_tag(v___x_4179_) == 0)
{
lean_object* v_a_4180_; lean_object* v___x_4181_; lean_object* v_fst_4182_; lean_object* v_snd_4183_; lean_object* v_levelParams_4184_; lean_object* v_levelArgs_4185_; lean_object* v_newLocalDecls_4186_; lean_object* v_newLocalDeclsForMVars_4187_; lean_object* v_newLetDecls_4188_; lean_object* v_exprMVarArgs_4189_; lean_object* v_exprFVarArgs_4190_; lean_object* v___x_4191_; lean_object* v___x_4192_; lean_object* v___x_4193_; 
v_a_4180_ = lean_ctor_get(v___x_4179_, 0);
lean_inc(v_a_4180_);
lean_dec_ref_known(v___x_4179_, 1);
v___x_4181_ = lean_st_ref_get(v___x_4178_);
lean_dec(v___x_4178_);
v_fst_4182_ = lean_ctor_get(v_a_4180_, 0);
lean_inc(v_fst_4182_);
v_snd_4183_ = lean_ctor_get(v_a_4180_, 1);
lean_inc(v_snd_4183_);
lean_dec(v_a_4180_);
v_levelParams_4184_ = lean_ctor_get(v___x_4181_, 2);
lean_inc_ref(v_levelParams_4184_);
v_levelArgs_4185_ = lean_ctor_get(v___x_4181_, 4);
lean_inc_ref(v_levelArgs_4185_);
v_newLocalDecls_4186_ = lean_ctor_get(v___x_4181_, 5);
lean_inc_ref(v_newLocalDecls_4186_);
v_newLocalDeclsForMVars_4187_ = lean_ctor_get(v___x_4181_, 6);
lean_inc_ref(v_newLocalDeclsForMVars_4187_);
v_newLetDecls_4188_ = lean_ctor_get(v___x_4181_, 7);
lean_inc_ref(v_newLetDecls_4188_);
v_exprMVarArgs_4189_ = lean_ctor_get(v___x_4181_, 9);
lean_inc_ref(v_exprMVarArgs_4189_);
v_exprFVarArgs_4190_ = lean_ctor_get(v___x_4181_, 10);
lean_inc_ref(v_exprFVarArgs_4190_);
lean_dec(v___x_4181_);
v___x_4191_ = l_Array_reverse___redArg(v_newLocalDecls_4186_);
v___x_4192_ = l_Array_reverse___redArg(v_exprFVarArgs_4190_);
v___x_4193_ = l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls(v___x_4191_, v___x_4192_, v_newLocalDeclsForMVars_4187_, v_exprMVarArgs_4189_, v_a_4174_, v_a_4175_);
lean_dec_ref(v_newLocalDeclsForMVars_4187_);
if (lean_obj_tag(v___x_4193_) == 0)
{
lean_object* v_a_4194_; lean_object* v___x_4196_; uint8_t v_isShared_4197_; uint8_t v_isSharedCheck_4212_; 
v_a_4194_ = lean_ctor_get(v___x_4193_, 0);
v_isSharedCheck_4212_ = !lean_is_exclusive(v___x_4193_);
if (v_isSharedCheck_4212_ == 0)
{
v___x_4196_ = v___x_4193_;
v_isShared_4197_ = v_isSharedCheck_4212_;
goto v_resetjp_4195_;
}
else
{
lean_inc(v_a_4194_);
lean_dec(v___x_4193_);
v___x_4196_ = lean_box(0);
v_isShared_4197_ = v_isSharedCheck_4212_;
goto v_resetjp_4195_;
}
v_resetjp_4195_:
{
lean_object* v_fst_4198_; lean_object* v_snd_4199_; lean_object* v___x_4200_; lean_object* v___x_4201_; lean_object* v___x_4202_; lean_object* v___x_4203_; lean_object* v___x_4204_; uint8_t v___x_4205_; 
v_fst_4198_ = lean_ctor_get(v_a_4194_, 0);
lean_inc_n(v_fst_4198_, 2);
v_snd_4199_ = lean_ctor_get(v_a_4194_, 1);
lean_inc(v_snd_4199_);
lean_dec(v_a_4194_);
v___x_4200_ = l_Array_reverse___redArg(v_newLetDecls_4188_);
lean_inc_ref(v___x_4200_);
v___x_4201_ = l_Lean_Meta_Closure_mkForall(v___x_4200_, v_fst_4182_);
lean_dec(v_fst_4182_);
v___x_4202_ = l_Lean_Meta_Closure_mkForall(v_fst_4198_, v___x_4201_);
lean_dec_ref(v___x_4201_);
v___x_4203_ = l_Lean_Meta_Closure_mkLambda(v___x_4200_, v_snd_4183_);
lean_dec(v_snd_4183_);
v___x_4204_ = l_Lean_Meta_Closure_mkLambda(v_fst_4198_, v___x_4203_);
lean_dec_ref(v___x_4203_);
v___x_4205_ = l_Lean_Expr_hasFVar(v___x_4204_);
if (v___x_4205_ == 0)
{
lean_object* v___x_4206_; lean_object* v___x_4208_; 
v___x_4206_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4206_, 0, v_levelParams_4184_);
lean_ctor_set(v___x_4206_, 1, v___x_4202_);
lean_ctor_set(v___x_4206_, 2, v___x_4204_);
lean_ctor_set(v___x_4206_, 3, v_levelArgs_4185_);
lean_ctor_set(v___x_4206_, 4, v_snd_4199_);
if (v_isShared_4197_ == 0)
{
lean_ctor_set(v___x_4196_, 0, v___x_4206_);
v___x_4208_ = v___x_4196_;
goto v_reusejp_4207_;
}
else
{
lean_object* v_reuseFailAlloc_4209_; 
v_reuseFailAlloc_4209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4209_, 0, v___x_4206_);
v___x_4208_ = v_reuseFailAlloc_4209_;
goto v_reusejp_4207_;
}
v_reusejp_4207_:
{
return v___x_4208_;
}
}
else
{
lean_object* v___x_4210_; lean_object* v___x_4211_; 
lean_dec_ref(v___x_4204_);
lean_dec_ref(v___x_4202_);
lean_dec(v_snd_4199_);
lean_del_object(v___x_4196_);
lean_dec_ref(v_levelArgs_4185_);
lean_dec_ref(v_levelParams_4184_);
v___x_4210_ = lean_obj_once(&l_Lean_Meta_Closure_mkValueTypeClosure___closed__6, &l_Lean_Meta_Closure_mkValueTypeClosure___closed__6_once, _init_l_Lean_Meta_Closure_mkValueTypeClosure___closed__6);
v___x_4211_ = l_panic___at___00Lean_Meta_Closure_mkValueTypeClosure_spec__0(v___x_4210_, v_a_4172_, v_a_4173_, v_a_4174_, v_a_4175_);
return v___x_4211_;
}
}
}
else
{
lean_object* v_a_4213_; lean_object* v___x_4215_; uint8_t v_isShared_4216_; uint8_t v_isSharedCheck_4220_; 
lean_dec_ref(v_newLetDecls_4188_);
lean_dec_ref(v_levelArgs_4185_);
lean_dec_ref(v_levelParams_4184_);
lean_dec(v_snd_4183_);
lean_dec(v_fst_4182_);
v_a_4213_ = lean_ctor_get(v___x_4193_, 0);
v_isSharedCheck_4220_ = !lean_is_exclusive(v___x_4193_);
if (v_isSharedCheck_4220_ == 0)
{
v___x_4215_ = v___x_4193_;
v_isShared_4216_ = v_isSharedCheck_4220_;
goto v_resetjp_4214_;
}
else
{
lean_inc(v_a_4213_);
lean_dec(v___x_4193_);
v___x_4215_ = lean_box(0);
v_isShared_4216_ = v_isSharedCheck_4220_;
goto v_resetjp_4214_;
}
v_resetjp_4214_:
{
lean_object* v___x_4218_; 
if (v_isShared_4216_ == 0)
{
v___x_4218_ = v___x_4215_;
goto v_reusejp_4217_;
}
else
{
lean_object* v_reuseFailAlloc_4219_; 
v_reuseFailAlloc_4219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4219_, 0, v_a_4213_);
v___x_4218_ = v_reuseFailAlloc_4219_;
goto v_reusejp_4217_;
}
v_reusejp_4217_:
{
return v___x_4218_;
}
}
}
}
else
{
lean_object* v_a_4221_; lean_object* v___x_4223_; uint8_t v_isShared_4224_; uint8_t v_isSharedCheck_4228_; 
lean_dec(v___x_4178_);
v_a_4221_ = lean_ctor_get(v___x_4179_, 0);
v_isSharedCheck_4228_ = !lean_is_exclusive(v___x_4179_);
if (v_isSharedCheck_4228_ == 0)
{
v___x_4223_ = v___x_4179_;
v_isShared_4224_ = v_isSharedCheck_4228_;
goto v_resetjp_4222_;
}
else
{
lean_inc(v_a_4221_);
lean_dec(v___x_4179_);
v___x_4223_ = lean_box(0);
v_isShared_4224_ = v_isSharedCheck_4228_;
goto v_resetjp_4222_;
}
v_resetjp_4222_:
{
lean_object* v___x_4226_; 
if (v_isShared_4224_ == 0)
{
v___x_4226_ = v___x_4223_;
goto v_reusejp_4225_;
}
else
{
lean_object* v_reuseFailAlloc_4227_; 
v_reuseFailAlloc_4227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4227_, 0, v_a_4221_);
v___x_4226_ = v_reuseFailAlloc_4227_;
goto v_reusejp_4225_;
}
v_reusejp_4225_:
{
return v___x_4226_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkValueTypeClosure___boxed(lean_object* v_type_4229_, lean_object* v_value_4230_, lean_object* v_zetaDelta_4231_, lean_object* v_a_4232_, lean_object* v_a_4233_, lean_object* v_a_4234_, lean_object* v_a_4235_, lean_object* v_a_4236_){
_start:
{
uint8_t v_zetaDelta_boxed_4237_; lean_object* v_res_4238_; 
v_zetaDelta_boxed_4237_ = lean_unbox(v_zetaDelta_4231_);
v_res_4238_ = l_Lean_Meta_Closure_mkValueTypeClosure(v_type_4229_, v_value_4230_, v_zetaDelta_boxed_4237_, v_a_4232_, v_a_4233_, v_a_4234_, v_a_4235_);
lean_dec(v_a_4235_);
lean_dec_ref(v_a_4234_);
lean_dec(v_a_4233_);
lean_dec_ref(v_a_4232_);
return v_res_4238_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkAuxDefinition_spec__0___redArg(lean_object* v_name_4239_, lean_object* v_levelParams_4240_, lean_object* v_type_4241_, lean_object* v_value_4242_, lean_object* v_hints_4243_, lean_object* v___y_4244_){
_start:
{
lean_object* v___x_4246_; uint8_t v___y_4248_; uint8_t v___y_4255_; lean_object* v_env_4258_; uint8_t v___x_4259_; 
v___x_4246_ = lean_st_ref_get(v___y_4244_);
v_env_4258_ = lean_ctor_get(v___x_4246_, 0);
lean_inc_ref_n(v_env_4258_, 2);
lean_dec(v___x_4246_);
v___x_4259_ = l_Lean_Environment_hasUnsafe(v_env_4258_, v_type_4241_);
if (v___x_4259_ == 0)
{
uint8_t v___x_4260_; 
v___x_4260_ = l_Lean_Environment_hasUnsafe(v_env_4258_, v_value_4242_);
v___y_4255_ = v___x_4260_;
goto v___jp_4254_;
}
else
{
lean_dec_ref(v_env_4258_);
v___y_4255_ = v___x_4259_;
goto v___jp_4254_;
}
v___jp_4247_:
{
lean_object* v___x_4249_; lean_object* v___x_4250_; lean_object* v___x_4251_; lean_object* v___x_4252_; lean_object* v___x_4253_; 
lean_inc(v_name_4239_);
v___x_4249_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4249_, 0, v_name_4239_);
lean_ctor_set(v___x_4249_, 1, v_levelParams_4240_);
lean_ctor_set(v___x_4249_, 2, v_type_4241_);
v___x_4250_ = lean_box(0);
v___x_4251_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4251_, 0, v_name_4239_);
lean_ctor_set(v___x_4251_, 1, v___x_4250_);
v___x_4252_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_4252_, 0, v___x_4249_);
lean_ctor_set(v___x_4252_, 1, v_value_4242_);
lean_ctor_set(v___x_4252_, 2, v_hints_4243_);
lean_ctor_set(v___x_4252_, 3, v___x_4251_);
lean_ctor_set_uint8(v___x_4252_, sizeof(void*)*4, v___y_4248_);
v___x_4253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4253_, 0, v___x_4252_);
return v___x_4253_;
}
v___jp_4254_:
{
if (v___y_4255_ == 0)
{
uint8_t v___x_4256_; 
v___x_4256_ = 1;
v___y_4248_ = v___x_4256_;
goto v___jp_4247_;
}
else
{
uint8_t v___x_4257_; 
v___x_4257_ = 0;
v___y_4248_ = v___x_4257_;
goto v___jp_4247_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkAuxDefinition_spec__0___redArg___boxed(lean_object* v_name_4261_, lean_object* v_levelParams_4262_, lean_object* v_type_4263_, lean_object* v_value_4264_, lean_object* v_hints_4265_, lean_object* v___y_4266_, lean_object* v___y_4267_){
_start:
{
lean_object* v_res_4268_; 
v_res_4268_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkAuxDefinition_spec__0___redArg(v_name_4261_, v_levelParams_4262_, v_type_4263_, v_value_4264_, v_hints_4265_, v___y_4266_);
lean_dec(v___y_4266_);
return v_res_4268_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkAuxDefinition_spec__0(lean_object* v_name_4269_, lean_object* v_levelParams_4270_, lean_object* v_type_4271_, lean_object* v_value_4272_, lean_object* v_hints_4273_, lean_object* v___y_4274_, lean_object* v___y_4275_, lean_object* v___y_4276_, lean_object* v___y_4277_){
_start:
{
lean_object* v___x_4279_; 
v___x_4279_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkAuxDefinition_spec__0___redArg(v_name_4269_, v_levelParams_4270_, v_type_4271_, v_value_4272_, v_hints_4273_, v___y_4277_);
return v___x_4279_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkAuxDefinition_spec__0___boxed(lean_object* v_name_4280_, lean_object* v_levelParams_4281_, lean_object* v_type_4282_, lean_object* v_value_4283_, lean_object* v_hints_4284_, lean_object* v___y_4285_, lean_object* v___y_4286_, lean_object* v___y_4287_, lean_object* v___y_4288_, lean_object* v___y_4289_){
_start:
{
lean_object* v_res_4290_; 
v_res_4290_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkAuxDefinition_spec__0(v_name_4280_, v_levelParams_4281_, v_type_4282_, v_value_4283_, v_hints_4284_, v___y_4285_, v___y_4286_, v___y_4287_, v___y_4288_);
lean_dec(v___y_4288_);
lean_dec_ref(v___y_4287_);
lean_dec(v___y_4286_);
lean_dec_ref(v___y_4285_);
return v_res_4290_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAuxDefinition(lean_object* v_name_4291_, lean_object* v_type_4292_, lean_object* v_value_4293_, uint8_t v_zetaDelta_4294_, uint8_t v_compile_4295_, uint8_t v_logCompileErrors_4296_, lean_object* v_a_4297_, lean_object* v_a_4298_, lean_object* v_a_4299_, lean_object* v_a_4300_){
_start:
{
lean_object* v___x_4302_; 
v___x_4302_ = l_Lean_Meta_Closure_mkValueTypeClosure(v_type_4292_, v_value_4293_, v_zetaDelta_4294_, v_a_4297_, v_a_4298_, v_a_4299_, v_a_4300_);
if (lean_obj_tag(v___x_4302_) == 0)
{
lean_object* v_a_4303_; lean_object* v___x_4305_; uint8_t v_isShared_4306_; uint8_t v_isSharedCheck_4354_; 
v_a_4303_ = lean_ctor_get(v___x_4302_, 0);
v_isSharedCheck_4354_ = !lean_is_exclusive(v___x_4302_);
if (v_isSharedCheck_4354_ == 0)
{
v___x_4305_ = v___x_4302_;
v_isShared_4306_ = v_isSharedCheck_4354_;
goto v_resetjp_4304_;
}
else
{
lean_inc(v_a_4303_);
lean_dec(v___x_4302_);
v___x_4305_ = lean_box(0);
v_isShared_4306_ = v_isSharedCheck_4354_;
goto v_resetjp_4304_;
}
v_resetjp_4304_:
{
lean_object* v___x_4307_; lean_object* v_env_4308_; lean_object* v_levelParams_4309_; lean_object* v_type_4310_; lean_object* v_value_4311_; lean_object* v_levelArgs_4312_; lean_object* v_exprArgs_4313_; uint32_t v___x_4321_; uint32_t v___x_4322_; uint32_t v___x_4323_; lean_object* v___x_4324_; lean_object* v___x_4325_; lean_object* v___x_4326_; lean_object* v_a_4327_; lean_object* v___x_4329_; uint8_t v_isShared_4330_; uint8_t v_isSharedCheck_4353_; 
v___x_4307_ = lean_st_ref_get(v_a_4300_);
v_env_4308_ = lean_ctor_get(v___x_4307_, 0);
lean_inc_ref(v_env_4308_);
lean_dec(v___x_4307_);
v_levelParams_4309_ = lean_ctor_get(v_a_4303_, 0);
lean_inc_ref(v_levelParams_4309_);
v_type_4310_ = lean_ctor_get(v_a_4303_, 1);
lean_inc_ref(v_type_4310_);
v_value_4311_ = lean_ctor_get(v_a_4303_, 2);
lean_inc_ref_n(v_value_4311_, 2);
v_levelArgs_4312_ = lean_ctor_get(v_a_4303_, 3);
lean_inc_ref(v_levelArgs_4312_);
v_exprArgs_4313_ = lean_ctor_get(v_a_4303_, 4);
lean_inc_ref(v_exprArgs_4313_);
lean_dec(v_a_4303_);
v___x_4321_ = l_Lean_getMaxHeight(v_env_4308_, v_value_4311_);
v___x_4322_ = 1;
v___x_4323_ = lean_uint32_add(v___x_4321_, v___x_4322_);
v___x_4324_ = lean_alloc_ctor(2, 0, 4);
lean_ctor_set_uint32(v___x_4324_, 0, v___x_4323_);
v___x_4325_ = lean_array_to_list(v_levelParams_4309_);
lean_inc(v_name_4291_);
v___x_4326_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkAuxDefinition_spec__0___redArg(v_name_4291_, v___x_4325_, v_type_4310_, v_value_4311_, v___x_4324_, v_a_4300_);
v_a_4327_ = lean_ctor_get(v___x_4326_, 0);
v_isSharedCheck_4353_ = !lean_is_exclusive(v___x_4326_);
if (v_isSharedCheck_4353_ == 0)
{
v___x_4329_ = v___x_4326_;
v_isShared_4330_ = v_isSharedCheck_4353_;
goto v_resetjp_4328_;
}
else
{
lean_inc(v_a_4327_);
lean_dec(v___x_4326_);
v___x_4329_ = lean_box(0);
v_isShared_4330_ = v_isSharedCheck_4353_;
goto v_resetjp_4328_;
}
v___jp_4314_:
{
lean_object* v___x_4315_; lean_object* v___x_4316_; lean_object* v___x_4317_; lean_object* v___x_4319_; 
v___x_4315_ = lean_array_to_list(v_levelArgs_4312_);
v___x_4316_ = l_Lean_mkConst(v_name_4291_, v___x_4315_);
v___x_4317_ = l_Lean_mkAppN(v___x_4316_, v_exprArgs_4313_);
lean_dec_ref(v_exprArgs_4313_);
if (v_isShared_4306_ == 0)
{
lean_ctor_set(v___x_4305_, 0, v___x_4317_);
v___x_4319_ = v___x_4305_;
goto v_reusejp_4318_;
}
else
{
lean_object* v_reuseFailAlloc_4320_; 
v_reuseFailAlloc_4320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4320_, 0, v___x_4317_);
v___x_4319_ = v_reuseFailAlloc_4320_;
goto v_reusejp_4318_;
}
v_reusejp_4318_:
{
return v___x_4319_;
}
}
v_resetjp_4328_:
{
lean_object* v___x_4332_; 
if (v_isShared_4330_ == 0)
{
lean_ctor_set_tag(v___x_4329_, 1);
v___x_4332_ = v___x_4329_;
goto v_reusejp_4331_;
}
else
{
lean_object* v_reuseFailAlloc_4352_; 
v_reuseFailAlloc_4352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4352_, 0, v_a_4327_);
v___x_4332_ = v_reuseFailAlloc_4352_;
goto v_reusejp_4331_;
}
v_reusejp_4331_:
{
uint8_t v___x_4333_; lean_object* v___x_4334_; 
v___x_4333_ = 0;
lean_inc_ref(v___x_4332_);
v___x_4334_ = l_Lean_addDecl(v___x_4332_, v___x_4333_, v_a_4299_, v_a_4300_);
if (lean_obj_tag(v___x_4334_) == 0)
{
lean_dec_ref_known(v___x_4334_, 1);
if (v_compile_4295_ == 0)
{
lean_dec_ref(v___x_4332_);
goto v___jp_4314_;
}
else
{
lean_object* v___x_4335_; 
v___x_4335_ = l_Lean_compileDecl(v___x_4332_, v_logCompileErrors_4296_, v_a_4299_, v_a_4300_);
if (lean_obj_tag(v___x_4335_) == 0)
{
lean_dec_ref_known(v___x_4335_, 1);
goto v___jp_4314_;
}
else
{
lean_object* v_a_4336_; lean_object* v___x_4338_; uint8_t v_isShared_4339_; uint8_t v_isSharedCheck_4343_; 
lean_dec_ref(v_exprArgs_4313_);
lean_dec_ref(v_levelArgs_4312_);
lean_del_object(v___x_4305_);
lean_dec(v_name_4291_);
v_a_4336_ = lean_ctor_get(v___x_4335_, 0);
v_isSharedCheck_4343_ = !lean_is_exclusive(v___x_4335_);
if (v_isSharedCheck_4343_ == 0)
{
v___x_4338_ = v___x_4335_;
v_isShared_4339_ = v_isSharedCheck_4343_;
goto v_resetjp_4337_;
}
else
{
lean_inc(v_a_4336_);
lean_dec(v___x_4335_);
v___x_4338_ = lean_box(0);
v_isShared_4339_ = v_isSharedCheck_4343_;
goto v_resetjp_4337_;
}
v_resetjp_4337_:
{
lean_object* v___x_4341_; 
if (v_isShared_4339_ == 0)
{
v___x_4341_ = v___x_4338_;
goto v_reusejp_4340_;
}
else
{
lean_object* v_reuseFailAlloc_4342_; 
v_reuseFailAlloc_4342_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4342_, 0, v_a_4336_);
v___x_4341_ = v_reuseFailAlloc_4342_;
goto v_reusejp_4340_;
}
v_reusejp_4340_:
{
return v___x_4341_;
}
}
}
}
}
else
{
lean_object* v_a_4344_; lean_object* v___x_4346_; uint8_t v_isShared_4347_; uint8_t v_isSharedCheck_4351_; 
lean_dec_ref(v___x_4332_);
lean_dec_ref(v_exprArgs_4313_);
lean_dec_ref(v_levelArgs_4312_);
lean_del_object(v___x_4305_);
lean_dec(v_name_4291_);
v_a_4344_ = lean_ctor_get(v___x_4334_, 0);
v_isSharedCheck_4351_ = !lean_is_exclusive(v___x_4334_);
if (v_isSharedCheck_4351_ == 0)
{
v___x_4346_ = v___x_4334_;
v_isShared_4347_ = v_isSharedCheck_4351_;
goto v_resetjp_4345_;
}
else
{
lean_inc(v_a_4344_);
lean_dec(v___x_4334_);
v___x_4346_ = lean_box(0);
v_isShared_4347_ = v_isSharedCheck_4351_;
goto v_resetjp_4345_;
}
v_resetjp_4345_:
{
lean_object* v___x_4349_; 
if (v_isShared_4347_ == 0)
{
v___x_4349_ = v___x_4346_;
goto v_reusejp_4348_;
}
else
{
lean_object* v_reuseFailAlloc_4350_; 
v_reuseFailAlloc_4350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4350_, 0, v_a_4344_);
v___x_4349_ = v_reuseFailAlloc_4350_;
goto v_reusejp_4348_;
}
v_reusejp_4348_:
{
return v___x_4349_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4355_; lean_object* v___x_4357_; uint8_t v_isShared_4358_; uint8_t v_isSharedCheck_4362_; 
lean_dec(v_name_4291_);
v_a_4355_ = lean_ctor_get(v___x_4302_, 0);
v_isSharedCheck_4362_ = !lean_is_exclusive(v___x_4302_);
if (v_isSharedCheck_4362_ == 0)
{
v___x_4357_ = v___x_4302_;
v_isShared_4358_ = v_isSharedCheck_4362_;
goto v_resetjp_4356_;
}
else
{
lean_inc(v_a_4355_);
lean_dec(v___x_4302_);
v___x_4357_ = lean_box(0);
v_isShared_4358_ = v_isSharedCheck_4362_;
goto v_resetjp_4356_;
}
v_resetjp_4356_:
{
lean_object* v___x_4360_; 
if (v_isShared_4358_ == 0)
{
v___x_4360_ = v___x_4357_;
goto v_reusejp_4359_;
}
else
{
lean_object* v_reuseFailAlloc_4361_; 
v_reuseFailAlloc_4361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4361_, 0, v_a_4355_);
v___x_4360_ = v_reuseFailAlloc_4361_;
goto v_reusejp_4359_;
}
v_reusejp_4359_:
{
return v___x_4360_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAuxDefinition___boxed(lean_object* v_name_4363_, lean_object* v_type_4364_, lean_object* v_value_4365_, lean_object* v_zetaDelta_4366_, lean_object* v_compile_4367_, lean_object* v_logCompileErrors_4368_, lean_object* v_a_4369_, lean_object* v_a_4370_, lean_object* v_a_4371_, lean_object* v_a_4372_, lean_object* v_a_4373_){
_start:
{
uint8_t v_zetaDelta_boxed_4374_; uint8_t v_compile_boxed_4375_; uint8_t v_logCompileErrors_boxed_4376_; lean_object* v_res_4377_; 
v_zetaDelta_boxed_4374_ = lean_unbox(v_zetaDelta_4366_);
v_compile_boxed_4375_ = lean_unbox(v_compile_4367_);
v_logCompileErrors_boxed_4376_ = lean_unbox(v_logCompileErrors_4368_);
v_res_4377_ = l_Lean_Meta_mkAuxDefinition(v_name_4363_, v_type_4364_, v_value_4365_, v_zetaDelta_boxed_4374_, v_compile_boxed_4375_, v_logCompileErrors_boxed_4376_, v_a_4369_, v_a_4370_, v_a_4371_, v_a_4372_);
lean_dec(v_a_4372_);
lean_dec_ref(v_a_4371_);
lean_dec(v_a_4370_);
lean_dec_ref(v_a_4369_);
return v_res_4377_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAuxDefinitionFor(lean_object* v_name_4378_, lean_object* v_value_4379_, uint8_t v_zetaDelta_4380_, uint8_t v_compile_4381_, uint8_t v_logCompileErrors_4382_, lean_object* v_a_4383_, lean_object* v_a_4384_, lean_object* v_a_4385_, lean_object* v_a_4386_){
_start:
{
lean_object* v___x_4388_; 
lean_inc(v_a_4386_);
lean_inc_ref(v_a_4385_);
lean_inc(v_a_4384_);
lean_inc_ref(v_a_4383_);
lean_inc_ref(v_value_4379_);
v___x_4388_ = lean_infer_type(v_value_4379_, v_a_4383_, v_a_4384_, v_a_4385_, v_a_4386_);
if (lean_obj_tag(v___x_4388_) == 0)
{
lean_object* v_a_4389_; lean_object* v___x_4390_; lean_object* v___x_4391_; 
v_a_4389_ = lean_ctor_get(v___x_4388_, 0);
lean_inc(v_a_4389_);
lean_dec_ref_known(v___x_4388_, 1);
v___x_4390_ = l_Lean_Expr_headBeta(v_a_4389_);
v___x_4391_ = l_Lean_Meta_mkAuxDefinition(v_name_4378_, v___x_4390_, v_value_4379_, v_zetaDelta_4380_, v_compile_4381_, v_logCompileErrors_4382_, v_a_4383_, v_a_4384_, v_a_4385_, v_a_4386_);
return v___x_4391_;
}
else
{
lean_dec_ref(v_value_4379_);
lean_dec(v_name_4378_);
return v___x_4388_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAuxDefinitionFor___boxed(lean_object* v_name_4392_, lean_object* v_value_4393_, lean_object* v_zetaDelta_4394_, lean_object* v_compile_4395_, lean_object* v_logCompileErrors_4396_, lean_object* v_a_4397_, lean_object* v_a_4398_, lean_object* v_a_4399_, lean_object* v_a_4400_, lean_object* v_a_4401_){
_start:
{
uint8_t v_zetaDelta_boxed_4402_; uint8_t v_compile_boxed_4403_; uint8_t v_logCompileErrors_boxed_4404_; lean_object* v_res_4405_; 
v_zetaDelta_boxed_4402_ = lean_unbox(v_zetaDelta_4394_);
v_compile_boxed_4403_ = lean_unbox(v_compile_4395_);
v_logCompileErrors_boxed_4404_ = lean_unbox(v_logCompileErrors_4396_);
v_res_4405_ = l_Lean_Meta_mkAuxDefinitionFor(v_name_4392_, v_value_4393_, v_zetaDelta_boxed_4402_, v_compile_boxed_4403_, v_logCompileErrors_boxed_4404_, v_a_4397_, v_a_4398_, v_a_4399_, v_a_4400_);
lean_dec(v_a_4400_);
lean_dec_ref(v_a_4399_);
lean_dec(v_a_4398_);
lean_dec_ref(v_a_4397_);
return v_res_4405_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAuxTheorem(lean_object* v_type_4406_, lean_object* v_value_4407_, uint8_t v_zetaDelta_4408_, lean_object* v_kind_x3f_4409_, uint8_t v_cache_4410_, lean_object* v_a_4411_, lean_object* v_a_4412_, lean_object* v_a_4413_, lean_object* v_a_4414_){
_start:
{
lean_object* v___x_4416_; 
v___x_4416_ = l_Lean_Meta_Closure_mkValueTypeClosure(v_type_4406_, v_value_4407_, v_zetaDelta_4408_, v_a_4411_, v_a_4412_, v_a_4413_, v_a_4414_);
if (lean_obj_tag(v___x_4416_) == 0)
{
lean_object* v_a_4417_; lean_object* v_levelParams_4418_; lean_object* v_type_4419_; lean_object* v_value_4420_; lean_object* v_levelArgs_4421_; lean_object* v_exprArgs_4422_; lean_object* v___x_4423_; uint8_t v___x_4424_; lean_object* v___x_4425_; 
v_a_4417_ = lean_ctor_get(v___x_4416_, 0);
lean_inc(v_a_4417_);
lean_dec_ref_known(v___x_4416_, 1);
v_levelParams_4418_ = lean_ctor_get(v_a_4417_, 0);
lean_inc_ref(v_levelParams_4418_);
v_type_4419_ = lean_ctor_get(v_a_4417_, 1);
lean_inc_ref(v_type_4419_);
v_value_4420_ = lean_ctor_get(v_a_4417_, 2);
lean_inc_ref(v_value_4420_);
v_levelArgs_4421_ = lean_ctor_get(v_a_4417_, 3);
lean_inc_ref(v_levelArgs_4421_);
v_exprArgs_4422_ = lean_ctor_get(v_a_4417_, 4);
lean_inc_ref(v_exprArgs_4422_);
lean_dec(v_a_4417_);
v___x_4423_ = lean_array_to_list(v_levelParams_4418_);
v___x_4424_ = 0;
v___x_4425_ = l_Lean_Meta_mkAuxLemma(v___x_4423_, v_type_4419_, v_value_4420_, v_kind_x3f_4409_, v_cache_4410_, v___x_4424_, v___x_4424_, v___x_4424_, v_a_4411_, v_a_4412_, v_a_4413_, v_a_4414_);
if (lean_obj_tag(v___x_4425_) == 0)
{
lean_object* v_a_4426_; lean_object* v___x_4428_; uint8_t v_isShared_4429_; uint8_t v_isSharedCheck_4436_; 
v_a_4426_ = lean_ctor_get(v___x_4425_, 0);
v_isSharedCheck_4436_ = !lean_is_exclusive(v___x_4425_);
if (v_isSharedCheck_4436_ == 0)
{
v___x_4428_ = v___x_4425_;
v_isShared_4429_ = v_isSharedCheck_4436_;
goto v_resetjp_4427_;
}
else
{
lean_inc(v_a_4426_);
lean_dec(v___x_4425_);
v___x_4428_ = lean_box(0);
v_isShared_4429_ = v_isSharedCheck_4436_;
goto v_resetjp_4427_;
}
v_resetjp_4427_:
{
lean_object* v___x_4430_; lean_object* v___x_4431_; lean_object* v___x_4432_; lean_object* v___x_4434_; 
v___x_4430_ = lean_array_to_list(v_levelArgs_4421_);
v___x_4431_ = l_Lean_mkConst(v_a_4426_, v___x_4430_);
v___x_4432_ = l_Lean_mkAppN(v___x_4431_, v_exprArgs_4422_);
lean_dec_ref(v_exprArgs_4422_);
if (v_isShared_4429_ == 0)
{
lean_ctor_set(v___x_4428_, 0, v___x_4432_);
v___x_4434_ = v___x_4428_;
goto v_reusejp_4433_;
}
else
{
lean_object* v_reuseFailAlloc_4435_; 
v_reuseFailAlloc_4435_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4435_, 0, v___x_4432_);
v___x_4434_ = v_reuseFailAlloc_4435_;
goto v_reusejp_4433_;
}
v_reusejp_4433_:
{
return v___x_4434_;
}
}
}
else
{
lean_object* v_a_4437_; lean_object* v___x_4439_; uint8_t v_isShared_4440_; uint8_t v_isSharedCheck_4444_; 
lean_dec_ref(v_exprArgs_4422_);
lean_dec_ref(v_levelArgs_4421_);
v_a_4437_ = lean_ctor_get(v___x_4425_, 0);
v_isSharedCheck_4444_ = !lean_is_exclusive(v___x_4425_);
if (v_isSharedCheck_4444_ == 0)
{
v___x_4439_ = v___x_4425_;
v_isShared_4440_ = v_isSharedCheck_4444_;
goto v_resetjp_4438_;
}
else
{
lean_inc(v_a_4437_);
lean_dec(v___x_4425_);
v___x_4439_ = lean_box(0);
v_isShared_4440_ = v_isSharedCheck_4444_;
goto v_resetjp_4438_;
}
v_resetjp_4438_:
{
lean_object* v___x_4442_; 
if (v_isShared_4440_ == 0)
{
v___x_4442_ = v___x_4439_;
goto v_reusejp_4441_;
}
else
{
lean_object* v_reuseFailAlloc_4443_; 
v_reuseFailAlloc_4443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4443_, 0, v_a_4437_);
v___x_4442_ = v_reuseFailAlloc_4443_;
goto v_reusejp_4441_;
}
v_reusejp_4441_:
{
return v___x_4442_;
}
}
}
}
else
{
lean_object* v_a_4445_; lean_object* v___x_4447_; uint8_t v_isShared_4448_; uint8_t v_isSharedCheck_4452_; 
lean_dec(v_kind_x3f_4409_);
v_a_4445_ = lean_ctor_get(v___x_4416_, 0);
v_isSharedCheck_4452_ = !lean_is_exclusive(v___x_4416_);
if (v_isSharedCheck_4452_ == 0)
{
v___x_4447_ = v___x_4416_;
v_isShared_4448_ = v_isSharedCheck_4452_;
goto v_resetjp_4446_;
}
else
{
lean_inc(v_a_4445_);
lean_dec(v___x_4416_);
v___x_4447_ = lean_box(0);
v_isShared_4448_ = v_isSharedCheck_4452_;
goto v_resetjp_4446_;
}
v_resetjp_4446_:
{
lean_object* v___x_4450_; 
if (v_isShared_4448_ == 0)
{
v___x_4450_ = v___x_4447_;
goto v_reusejp_4449_;
}
else
{
lean_object* v_reuseFailAlloc_4451_; 
v_reuseFailAlloc_4451_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4451_, 0, v_a_4445_);
v___x_4450_ = v_reuseFailAlloc_4451_;
goto v_reusejp_4449_;
}
v_reusejp_4449_:
{
return v___x_4450_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAuxTheorem___boxed(lean_object* v_type_4453_, lean_object* v_value_4454_, lean_object* v_zetaDelta_4455_, lean_object* v_kind_x3f_4456_, lean_object* v_cache_4457_, lean_object* v_a_4458_, lean_object* v_a_4459_, lean_object* v_a_4460_, lean_object* v_a_4461_, lean_object* v_a_4462_){
_start:
{
uint8_t v_zetaDelta_boxed_4463_; uint8_t v_cache_boxed_4464_; lean_object* v_res_4465_; 
v_zetaDelta_boxed_4463_ = lean_unbox(v_zetaDelta_4455_);
v_cache_boxed_4464_ = lean_unbox(v_cache_4457_);
v_res_4465_ = l_Lean_Meta_mkAuxTheorem(v_type_4453_, v_value_4454_, v_zetaDelta_boxed_4463_, v_kind_x3f_4456_, v_cache_boxed_4464_, v_a_4458_, v_a_4459_, v_a_4460_, v_a_4461_);
lean_dec(v_a_4461_);
lean_dec_ref(v_a_4460_);
lean_dec(v_a_4459_);
lean_dec_ref(v_a_4458_);
return v_res_4465_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_initFn_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4521_; uint8_t v___x_4522_; lean_object* v___x_4523_; lean_object* v___x_4524_; 
v___x_4521_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__10));
v___x_4522_ = 0;
v___x_4523_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2_));
v___x_4524_ = l_Lean_registerTraceClass(v___x_4521_, v___x_4522_, v___x_4523_);
return v___x_4524_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_initFn_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2____boxed(lean_object* v_a_4525_){
_start:
{
lean_object* v_res_4526_; 
v_res_4526_ = l___private_Lean_Meta_Closure_0__Lean_Meta_initFn_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2_();
return v_res_4526_;
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
