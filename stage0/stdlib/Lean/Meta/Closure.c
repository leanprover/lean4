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
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_instHashableFVarId_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
uint8_t l_Lean_ExprStructEq_beq(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instInhabitedCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_LocalDecl_fvarId(lean_object*);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
extern lean_object* l_Lean_instEmptyCollectionFVarIdHashSet;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
uint8_t l_Lean_LocalDecl_isLet(lean_object*, uint8_t);
uint8_t lean_bool_not(uint8_t);
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
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
uint64_t l_Lean_Expr_hash(lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
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
lean_object* l_Lean_mkLevelIMax_x27(lean_object*, lean_object*);
lean_object* l_Lean_simpLevelIMax_x27(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkLevelMax_x27(lean_object*, lean_object*);
lean_object* l_Lean_simpLevelMax_x27(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_succ___override(lean_object*);
uint8_t l_Lean_Level_hasMVar(lean_object*);
uint8_t l_Lean_Level_hasParam(lean_object*);
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
static lean_once_cell_t l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2___closed__0;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2___closed__1 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2___closed__1_value;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2___closed__2 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2___closed__2_value;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4_spec__8_spec__13___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4_spec__8_spec__12_spec__17_spec__18___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4_spec__8_spec__12_spec__17___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4_spec__8_spec__12___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4_spec__8_spec__11___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4_spec__8_spec__11___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4_spec__8___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4_spec__7_spec__9___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4_spec__7_spec__9___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4_spec__7___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4_spec__7___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1___redArg___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__5_spec__6_spec__11___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__5_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__5___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 84, .m_capacity = 84, .m_length = 83, .m_data = "assertion violation: !decl.isLet (allowNondep := true) -- should all be cdecls\n    "};
static const lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__2 = (const lean_object*)&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 63, .m_capacity = 63, .m_length = 62, .m_data = "_private.Lean.Meta.Closure.0.Lean.Meta.Closure.sortDecls.visit"};
static const lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__1 = (const lean_object*)&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "Lean.Meta.Closure"};
static const lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__0 = (const lean_object*)&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__3;
static lean_once_cell_t l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__4;
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4_spec__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4_spec__7___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4_spec__8(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__5_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4_spec__7_spec__9(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4_spec__7_spec__9___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4_spec__8_spec__11(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4_spec__8_spec__11___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4_spec__8_spec__12(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4_spec__8_spec__13(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__5_spec__6_spec__11(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4_spec__8_spec__12_spec__17(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4_spec__8_spec__12_spec__17_spec__18(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instInhabitedCoreM___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__0___closed__0 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__4(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__1___redArg(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
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
uint8_t v___y_17_; uint8_t v___x_64_; uint8_t v___x_65_; 
v___x_64_ = l_Lean_Level_hasMVar(v_u_8_);
v___x_65_ = lean_bool_not(v___x_64_);
if (v___x_65_ == 0)
{
v___y_17_ = v___x_65_;
goto v___jp_16_;
}
else
{
uint8_t v___x_66_; uint8_t v___x_67_; 
v___x_66_ = l_Lean_Level_hasParam(v_u_8_);
v___x_67_ = lean_bool_not(v___x_66_);
v___y_17_ = v___x_67_;
goto v___jp_16_;
}
v___jp_16_:
{
if (v___y_17_ == 0)
{
lean_object* v___x_18_; lean_object* v_visitedLevel_19_; lean_object* v___x_20_; lean_object* v___x_21_; lean_object* v___x_22_; 
v___x_18_ = lean_st_ref_get(v_a_10_);
v_visitedLevel_19_ = lean_ctor_get(v___x_18_, 0);
lean_inc_ref(v_visitedLevel_19_);
lean_dec(v___x_18_);
v___x_20_ = ((lean_object*)(l_Lean_Meta_Closure_visitLevel___closed__0));
v___x_21_ = ((lean_object*)(l_Lean_Meta_Closure_visitLevel___closed__1));
lean_inc(v_u_8_);
v___x_22_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v___x_20_, v___x_21_, v_visitedLevel_19_, v_u_8_);
lean_dec_ref(v_visitedLevel_19_);
if (lean_obj_tag(v___x_22_) == 0)
{
lean_object* v___x_23_; lean_object* v___x_24_; 
v___x_23_ = lean_box(v_a_9_);
lean_inc(v_a_14_);
lean_inc_ref(v_a_13_);
lean_inc(v_a_12_);
lean_inc_ref(v_a_11_);
lean_inc(v_a_10_);
lean_inc(v_u_8_);
v___x_24_ = lean_apply_8(v_f_7_, v_u_8_, v___x_23_, v_a_10_, v_a_11_, v_a_12_, v_a_13_, v_a_14_, lean_box(0));
if (lean_obj_tag(v___x_24_) == 0)
{
lean_object* v_a_25_; lean_object* v___x_27_; uint8_t v_isShared_28_; uint8_t v_isSharedCheck_54_; 
v_a_25_ = lean_ctor_get(v___x_24_, 0);
v_isSharedCheck_54_ = !lean_is_exclusive(v___x_24_);
if (v_isSharedCheck_54_ == 0)
{
v___x_27_ = v___x_24_;
v_isShared_28_ = v_isSharedCheck_54_;
goto v_resetjp_26_;
}
else
{
lean_inc(v_a_25_);
lean_dec(v___x_24_);
v___x_27_ = lean_box(0);
v_isShared_28_ = v_isSharedCheck_54_;
goto v_resetjp_26_;
}
v_resetjp_26_:
{
lean_object* v___x_29_; lean_object* v_visitedLevel_30_; lean_object* v_visitedExpr_31_; lean_object* v_levelParams_32_; lean_object* v_nextLevelIdx_33_; lean_object* v_levelArgs_34_; lean_object* v_newLocalDecls_35_; lean_object* v_newLocalDeclsForMVars_36_; lean_object* v_newLetDecls_37_; lean_object* v_nextExprIdx_38_; lean_object* v_exprMVarArgs_39_; lean_object* v_exprFVarArgs_40_; lean_object* v_toProcess_41_; lean_object* v___x_43_; uint8_t v_isShared_44_; uint8_t v_isSharedCheck_53_; 
v___x_29_ = lean_st_ref_take(v_a_10_);
v_visitedLevel_30_ = lean_ctor_get(v___x_29_, 0);
v_visitedExpr_31_ = lean_ctor_get(v___x_29_, 1);
v_levelParams_32_ = lean_ctor_get(v___x_29_, 2);
v_nextLevelIdx_33_ = lean_ctor_get(v___x_29_, 3);
v_levelArgs_34_ = lean_ctor_get(v___x_29_, 4);
v_newLocalDecls_35_ = lean_ctor_get(v___x_29_, 5);
v_newLocalDeclsForMVars_36_ = lean_ctor_get(v___x_29_, 6);
v_newLetDecls_37_ = lean_ctor_get(v___x_29_, 7);
v_nextExprIdx_38_ = lean_ctor_get(v___x_29_, 8);
v_exprMVarArgs_39_ = lean_ctor_get(v___x_29_, 9);
v_exprFVarArgs_40_ = lean_ctor_get(v___x_29_, 10);
v_toProcess_41_ = lean_ctor_get(v___x_29_, 11);
v_isSharedCheck_53_ = !lean_is_exclusive(v___x_29_);
if (v_isSharedCheck_53_ == 0)
{
v___x_43_ = v___x_29_;
v_isShared_44_ = v_isSharedCheck_53_;
goto v_resetjp_42_;
}
else
{
lean_inc(v_toProcess_41_);
lean_inc(v_exprFVarArgs_40_);
lean_inc(v_exprMVarArgs_39_);
lean_inc(v_nextExprIdx_38_);
lean_inc(v_newLetDecls_37_);
lean_inc(v_newLocalDeclsForMVars_36_);
lean_inc(v_newLocalDecls_35_);
lean_inc(v_levelArgs_34_);
lean_inc(v_nextLevelIdx_33_);
lean_inc(v_levelParams_32_);
lean_inc(v_visitedExpr_31_);
lean_inc(v_visitedLevel_30_);
lean_dec(v___x_29_);
v___x_43_ = lean_box(0);
v_isShared_44_ = v_isSharedCheck_53_;
goto v_resetjp_42_;
}
v_resetjp_42_:
{
lean_object* v___x_45_; lean_object* v___x_47_; 
lean_inc(v_a_25_);
v___x_45_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___x_20_, v___x_21_, v_visitedLevel_30_, v_u_8_, v_a_25_);
if (v_isShared_44_ == 0)
{
lean_ctor_set(v___x_43_, 0, v___x_45_);
v___x_47_ = v___x_43_;
goto v_reusejp_46_;
}
else
{
lean_object* v_reuseFailAlloc_52_; 
v_reuseFailAlloc_52_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_52_, 0, v___x_45_);
lean_ctor_set(v_reuseFailAlloc_52_, 1, v_visitedExpr_31_);
lean_ctor_set(v_reuseFailAlloc_52_, 2, v_levelParams_32_);
lean_ctor_set(v_reuseFailAlloc_52_, 3, v_nextLevelIdx_33_);
lean_ctor_set(v_reuseFailAlloc_52_, 4, v_levelArgs_34_);
lean_ctor_set(v_reuseFailAlloc_52_, 5, v_newLocalDecls_35_);
lean_ctor_set(v_reuseFailAlloc_52_, 6, v_newLocalDeclsForMVars_36_);
lean_ctor_set(v_reuseFailAlloc_52_, 7, v_newLetDecls_37_);
lean_ctor_set(v_reuseFailAlloc_52_, 8, v_nextExprIdx_38_);
lean_ctor_set(v_reuseFailAlloc_52_, 9, v_exprMVarArgs_39_);
lean_ctor_set(v_reuseFailAlloc_52_, 10, v_exprFVarArgs_40_);
lean_ctor_set(v_reuseFailAlloc_52_, 11, v_toProcess_41_);
v___x_47_ = v_reuseFailAlloc_52_;
goto v_reusejp_46_;
}
v_reusejp_46_:
{
lean_object* v___x_48_; lean_object* v___x_50_; 
v___x_48_ = lean_st_ref_set(v_a_10_, v___x_47_);
if (v_isShared_28_ == 0)
{
v___x_50_ = v___x_27_;
goto v_reusejp_49_;
}
else
{
lean_object* v_reuseFailAlloc_51_; 
v_reuseFailAlloc_51_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_51_, 0, v_a_25_);
v___x_50_ = v_reuseFailAlloc_51_;
goto v_reusejp_49_;
}
v_reusejp_49_:
{
return v___x_50_;
}
}
}
}
}
else
{
lean_dec(v_u_8_);
return v___x_24_;
}
}
else
{
lean_object* v_val_55_; lean_object* v___x_57_; uint8_t v_isShared_58_; uint8_t v_isSharedCheck_62_; 
lean_dec(v_u_8_);
lean_dec_ref(v_f_7_);
v_val_55_ = lean_ctor_get(v___x_22_, 0);
v_isSharedCheck_62_ = !lean_is_exclusive(v___x_22_);
if (v_isSharedCheck_62_ == 0)
{
v___x_57_ = v___x_22_;
v_isShared_58_ = v_isSharedCheck_62_;
goto v_resetjp_56_;
}
else
{
lean_inc(v_val_55_);
lean_dec(v___x_22_);
v___x_57_ = lean_box(0);
v_isShared_58_ = v_isSharedCheck_62_;
goto v_resetjp_56_;
}
v_resetjp_56_:
{
lean_object* v___x_60_; 
if (v_isShared_58_ == 0)
{
lean_ctor_set_tag(v___x_57_, 0);
v___x_60_ = v___x_57_;
goto v_reusejp_59_;
}
else
{
lean_object* v_reuseFailAlloc_61_; 
v_reuseFailAlloc_61_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_61_, 0, v_val_55_);
v___x_60_ = v_reuseFailAlloc_61_;
goto v_reusejp_59_;
}
v_reusejp_59_:
{
return v___x_60_;
}
}
}
}
else
{
lean_object* v___x_63_; 
lean_dec_ref(v_f_7_);
v___x_63_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_63_, 0, v_u_8_);
return v___x_63_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_visitLevel___boxed(lean_object* v_f_68_, lean_object* v_u_69_, lean_object* v_a_70_, lean_object* v_a_71_, lean_object* v_a_72_, lean_object* v_a_73_, lean_object* v_a_74_, lean_object* v_a_75_, lean_object* v_a_76_){
_start:
{
uint8_t v_a_boxed_77_; lean_object* v_res_78_; 
v_a_boxed_77_ = lean_unbox(v_a_70_);
v_res_78_ = l_Lean_Meta_Closure_visitLevel(v_f_68_, v_u_69_, v_a_boxed_77_, v_a_71_, v_a_72_, v_a_73_, v_a_74_, v_a_75_);
lean_dec(v_a_75_);
lean_dec_ref(v_a_74_);
lean_dec(v_a_73_);
lean_dec_ref(v_a_72_);
lean_dec(v_a_71_);
return v_res_78_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_visitExpr(lean_object* v_f_81_, lean_object* v_e_82_, uint8_t v_a_83_, lean_object* v_a_84_, lean_object* v_a_85_, lean_object* v_a_86_, lean_object* v_a_87_, lean_object* v_a_88_){
_start:
{
uint8_t v___y_137_; uint8_t v___x_141_; uint8_t v___x_142_; 
v___x_141_ = l_Lean_Expr_hasLevelParam(v_e_82_);
v___x_142_ = lean_bool_not(v___x_141_);
if (v___x_142_ == 0)
{
v___y_137_ = v___x_142_;
goto v___jp_136_;
}
else
{
uint8_t v___x_143_; uint8_t v___x_144_; 
v___x_143_ = l_Lean_Expr_hasFVar(v_e_82_);
v___x_144_ = lean_bool_not(v___x_143_);
v___y_137_ = v___x_144_;
goto v___jp_136_;
}
v___jp_90_:
{
lean_object* v___x_91_; lean_object* v_visitedExpr_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; 
v___x_91_ = lean_st_ref_get(v_a_84_);
v_visitedExpr_92_ = lean_ctor_get(v___x_91_, 1);
lean_inc_ref(v_visitedExpr_92_);
lean_dec(v___x_91_);
v___x_93_ = ((lean_object*)(l_Lean_Meta_Closure_visitExpr___closed__0));
v___x_94_ = ((lean_object*)(l_Lean_Meta_Closure_visitExpr___closed__1));
lean_inc_ref(v_e_82_);
v___x_95_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v___x_93_, v___x_94_, v_visitedExpr_92_, v_e_82_);
lean_dec_ref(v_visitedExpr_92_);
if (lean_obj_tag(v___x_95_) == 0)
{
lean_object* v___x_96_; lean_object* v___x_97_; 
v___x_96_ = lean_box(v_a_83_);
lean_inc(v_a_88_);
lean_inc_ref(v_a_87_);
lean_inc(v_a_86_);
lean_inc_ref(v_a_85_);
lean_inc(v_a_84_);
lean_inc_ref(v_e_82_);
v___x_97_ = lean_apply_8(v_f_81_, v_e_82_, v___x_96_, v_a_84_, v_a_85_, v_a_86_, v_a_87_, v_a_88_, lean_box(0));
if (lean_obj_tag(v___x_97_) == 0)
{
lean_object* v_a_98_; lean_object* v___x_100_; uint8_t v_isShared_101_; uint8_t v_isSharedCheck_127_; 
v_a_98_ = lean_ctor_get(v___x_97_, 0);
v_isSharedCheck_127_ = !lean_is_exclusive(v___x_97_);
if (v_isSharedCheck_127_ == 0)
{
v___x_100_ = v___x_97_;
v_isShared_101_ = v_isSharedCheck_127_;
goto v_resetjp_99_;
}
else
{
lean_inc(v_a_98_);
lean_dec(v___x_97_);
v___x_100_ = lean_box(0);
v_isShared_101_ = v_isSharedCheck_127_;
goto v_resetjp_99_;
}
v_resetjp_99_:
{
lean_object* v___x_102_; lean_object* v_visitedLevel_103_; lean_object* v_visitedExpr_104_; lean_object* v_levelParams_105_; lean_object* v_nextLevelIdx_106_; lean_object* v_levelArgs_107_; lean_object* v_newLocalDecls_108_; lean_object* v_newLocalDeclsForMVars_109_; lean_object* v_newLetDecls_110_; lean_object* v_nextExprIdx_111_; lean_object* v_exprMVarArgs_112_; lean_object* v_exprFVarArgs_113_; lean_object* v_toProcess_114_; lean_object* v___x_116_; uint8_t v_isShared_117_; uint8_t v_isSharedCheck_126_; 
v___x_102_ = lean_st_ref_take(v_a_84_);
v_visitedLevel_103_ = lean_ctor_get(v___x_102_, 0);
v_visitedExpr_104_ = lean_ctor_get(v___x_102_, 1);
v_levelParams_105_ = lean_ctor_get(v___x_102_, 2);
v_nextLevelIdx_106_ = lean_ctor_get(v___x_102_, 3);
v_levelArgs_107_ = lean_ctor_get(v___x_102_, 4);
v_newLocalDecls_108_ = lean_ctor_get(v___x_102_, 5);
v_newLocalDeclsForMVars_109_ = lean_ctor_get(v___x_102_, 6);
v_newLetDecls_110_ = lean_ctor_get(v___x_102_, 7);
v_nextExprIdx_111_ = lean_ctor_get(v___x_102_, 8);
v_exprMVarArgs_112_ = lean_ctor_get(v___x_102_, 9);
v_exprFVarArgs_113_ = lean_ctor_get(v___x_102_, 10);
v_toProcess_114_ = lean_ctor_get(v___x_102_, 11);
v_isSharedCheck_126_ = !lean_is_exclusive(v___x_102_);
if (v_isSharedCheck_126_ == 0)
{
v___x_116_ = v___x_102_;
v_isShared_117_ = v_isSharedCheck_126_;
goto v_resetjp_115_;
}
else
{
lean_inc(v_toProcess_114_);
lean_inc(v_exprFVarArgs_113_);
lean_inc(v_exprMVarArgs_112_);
lean_inc(v_nextExprIdx_111_);
lean_inc(v_newLetDecls_110_);
lean_inc(v_newLocalDeclsForMVars_109_);
lean_inc(v_newLocalDecls_108_);
lean_inc(v_levelArgs_107_);
lean_inc(v_nextLevelIdx_106_);
lean_inc(v_levelParams_105_);
lean_inc(v_visitedExpr_104_);
lean_inc(v_visitedLevel_103_);
lean_dec(v___x_102_);
v___x_116_ = lean_box(0);
v_isShared_117_ = v_isSharedCheck_126_;
goto v_resetjp_115_;
}
v_resetjp_115_:
{
lean_object* v___x_118_; lean_object* v___x_120_; 
lean_inc(v_a_98_);
v___x_118_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___x_93_, v___x_94_, v_visitedExpr_104_, v_e_82_, v_a_98_);
if (v_isShared_117_ == 0)
{
lean_ctor_set(v___x_116_, 1, v___x_118_);
v___x_120_ = v___x_116_;
goto v_reusejp_119_;
}
else
{
lean_object* v_reuseFailAlloc_125_; 
v_reuseFailAlloc_125_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_125_, 0, v_visitedLevel_103_);
lean_ctor_set(v_reuseFailAlloc_125_, 1, v___x_118_);
lean_ctor_set(v_reuseFailAlloc_125_, 2, v_levelParams_105_);
lean_ctor_set(v_reuseFailAlloc_125_, 3, v_nextLevelIdx_106_);
lean_ctor_set(v_reuseFailAlloc_125_, 4, v_levelArgs_107_);
lean_ctor_set(v_reuseFailAlloc_125_, 5, v_newLocalDecls_108_);
lean_ctor_set(v_reuseFailAlloc_125_, 6, v_newLocalDeclsForMVars_109_);
lean_ctor_set(v_reuseFailAlloc_125_, 7, v_newLetDecls_110_);
lean_ctor_set(v_reuseFailAlloc_125_, 8, v_nextExprIdx_111_);
lean_ctor_set(v_reuseFailAlloc_125_, 9, v_exprMVarArgs_112_);
lean_ctor_set(v_reuseFailAlloc_125_, 10, v_exprFVarArgs_113_);
lean_ctor_set(v_reuseFailAlloc_125_, 11, v_toProcess_114_);
v___x_120_ = v_reuseFailAlloc_125_;
goto v_reusejp_119_;
}
v_reusejp_119_:
{
lean_object* v___x_121_; lean_object* v___x_123_; 
v___x_121_ = lean_st_ref_set(v_a_84_, v___x_120_);
if (v_isShared_101_ == 0)
{
v___x_123_ = v___x_100_;
goto v_reusejp_122_;
}
else
{
lean_object* v_reuseFailAlloc_124_; 
v_reuseFailAlloc_124_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_124_, 0, v_a_98_);
v___x_123_ = v_reuseFailAlloc_124_;
goto v_reusejp_122_;
}
v_reusejp_122_:
{
return v___x_123_;
}
}
}
}
}
else
{
lean_dec_ref(v_e_82_);
return v___x_97_;
}
}
else
{
lean_object* v_val_128_; lean_object* v___x_130_; uint8_t v_isShared_131_; uint8_t v_isSharedCheck_135_; 
lean_dec_ref(v_e_82_);
lean_dec_ref(v_f_81_);
v_val_128_ = lean_ctor_get(v___x_95_, 0);
v_isSharedCheck_135_ = !lean_is_exclusive(v___x_95_);
if (v_isSharedCheck_135_ == 0)
{
v___x_130_ = v___x_95_;
v_isShared_131_ = v_isSharedCheck_135_;
goto v_resetjp_129_;
}
else
{
lean_inc(v_val_128_);
lean_dec(v___x_95_);
v___x_130_ = lean_box(0);
v_isShared_131_ = v_isSharedCheck_135_;
goto v_resetjp_129_;
}
v_resetjp_129_:
{
lean_object* v___x_133_; 
if (v_isShared_131_ == 0)
{
lean_ctor_set_tag(v___x_130_, 0);
v___x_133_ = v___x_130_;
goto v_reusejp_132_;
}
else
{
lean_object* v_reuseFailAlloc_134_; 
v_reuseFailAlloc_134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_134_, 0, v_val_128_);
v___x_133_ = v_reuseFailAlloc_134_;
goto v_reusejp_132_;
}
v_reusejp_132_:
{
return v___x_133_;
}
}
}
}
v___jp_136_:
{
if (v___y_137_ == 0)
{
goto v___jp_90_;
}
else
{
uint8_t v___x_138_; uint8_t v___x_139_; 
v___x_138_ = l_Lean_Expr_hasMVar(v_e_82_);
v___x_139_ = lean_bool_not(v___x_138_);
if (v___x_139_ == 0)
{
goto v___jp_90_;
}
else
{
lean_object* v___x_140_; 
lean_dec_ref(v_f_81_);
v___x_140_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_140_, 0, v_e_82_);
return v___x_140_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_visitExpr___boxed(lean_object* v_f_145_, lean_object* v_e_146_, lean_object* v_a_147_, lean_object* v_a_148_, lean_object* v_a_149_, lean_object* v_a_150_, lean_object* v_a_151_, lean_object* v_a_152_, lean_object* v_a_153_){
_start:
{
uint8_t v_a_boxed_154_; lean_object* v_res_155_; 
v_a_boxed_154_ = lean_unbox(v_a_147_);
v_res_155_ = l_Lean_Meta_Closure_visitExpr(v_f_145_, v_e_146_, v_a_boxed_154_, v_a_148_, v_a_149_, v_a_150_, v_a_151_, v_a_152_);
lean_dec(v_a_152_);
lean_dec_ref(v_a_151_);
lean_dec(v_a_150_);
lean_dec_ref(v_a_149_);
lean_dec(v_a_148_);
return v_res_155_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkNewLevelParam___redArg(lean_object* v_u_159_, lean_object* v_a_160_){
_start:
{
lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v_nextLevelIdx_164_; lean_object* v_visitedLevel_165_; lean_object* v_visitedExpr_166_; lean_object* v_levelParams_167_; lean_object* v_nextLevelIdx_168_; lean_object* v_levelArgs_169_; lean_object* v_newLocalDecls_170_; lean_object* v_newLocalDeclsForMVars_171_; lean_object* v_newLetDecls_172_; lean_object* v_nextExprIdx_173_; lean_object* v_exprMVarArgs_174_; lean_object* v_exprFVarArgs_175_; lean_object* v_toProcess_176_; lean_object* v___x_178_; uint8_t v_isShared_179_; uint8_t v_isSharedCheck_192_; 
v___x_162_ = lean_st_ref_get(v_a_160_);
v___x_163_ = lean_st_ref_take(v_a_160_);
v_nextLevelIdx_164_ = lean_ctor_get(v___x_162_, 3);
lean_inc(v_nextLevelIdx_164_);
lean_dec(v___x_162_);
v_visitedLevel_165_ = lean_ctor_get(v___x_163_, 0);
v_visitedExpr_166_ = lean_ctor_get(v___x_163_, 1);
v_levelParams_167_ = lean_ctor_get(v___x_163_, 2);
v_nextLevelIdx_168_ = lean_ctor_get(v___x_163_, 3);
v_levelArgs_169_ = lean_ctor_get(v___x_163_, 4);
v_newLocalDecls_170_ = lean_ctor_get(v___x_163_, 5);
v_newLocalDeclsForMVars_171_ = lean_ctor_get(v___x_163_, 6);
v_newLetDecls_172_ = lean_ctor_get(v___x_163_, 7);
v_nextExprIdx_173_ = lean_ctor_get(v___x_163_, 8);
v_exprMVarArgs_174_ = lean_ctor_get(v___x_163_, 9);
v_exprFVarArgs_175_ = lean_ctor_get(v___x_163_, 10);
v_toProcess_176_ = lean_ctor_get(v___x_163_, 11);
v_isSharedCheck_192_ = !lean_is_exclusive(v___x_163_);
if (v_isSharedCheck_192_ == 0)
{
v___x_178_ = v___x_163_;
v_isShared_179_ = v_isSharedCheck_192_;
goto v_resetjp_177_;
}
else
{
lean_inc(v_toProcess_176_);
lean_inc(v_exprFVarArgs_175_);
lean_inc(v_exprMVarArgs_174_);
lean_inc(v_nextExprIdx_173_);
lean_inc(v_newLetDecls_172_);
lean_inc(v_newLocalDeclsForMVars_171_);
lean_inc(v_newLocalDecls_170_);
lean_inc(v_levelArgs_169_);
lean_inc(v_nextLevelIdx_168_);
lean_inc(v_levelParams_167_);
lean_inc(v_visitedExpr_166_);
lean_inc(v_visitedLevel_165_);
lean_dec(v___x_163_);
v___x_178_ = lean_box(0);
v_isShared_179_ = v_isSharedCheck_192_;
goto v_resetjp_177_;
}
v_resetjp_177_:
{
lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_187_; 
v___x_180_ = ((lean_object*)(l_Lean_Meta_Closure_mkNewLevelParam___redArg___closed__1));
v___x_181_ = lean_name_append_index_after(v___x_180_, v_nextLevelIdx_164_);
lean_inc(v___x_181_);
v___x_182_ = lean_array_push(v_levelParams_167_, v___x_181_);
v___x_183_ = lean_unsigned_to_nat(1u);
v___x_184_ = lean_nat_add(v_nextLevelIdx_168_, v___x_183_);
lean_dec(v_nextLevelIdx_168_);
v___x_185_ = lean_array_push(v_levelArgs_169_, v_u_159_);
if (v_isShared_179_ == 0)
{
lean_ctor_set(v___x_178_, 4, v___x_185_);
lean_ctor_set(v___x_178_, 3, v___x_184_);
lean_ctor_set(v___x_178_, 2, v___x_182_);
v___x_187_ = v___x_178_;
goto v_reusejp_186_;
}
else
{
lean_object* v_reuseFailAlloc_191_; 
v_reuseFailAlloc_191_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_191_, 0, v_visitedLevel_165_);
lean_ctor_set(v_reuseFailAlloc_191_, 1, v_visitedExpr_166_);
lean_ctor_set(v_reuseFailAlloc_191_, 2, v___x_182_);
lean_ctor_set(v_reuseFailAlloc_191_, 3, v___x_184_);
lean_ctor_set(v_reuseFailAlloc_191_, 4, v___x_185_);
lean_ctor_set(v_reuseFailAlloc_191_, 5, v_newLocalDecls_170_);
lean_ctor_set(v_reuseFailAlloc_191_, 6, v_newLocalDeclsForMVars_171_);
lean_ctor_set(v_reuseFailAlloc_191_, 7, v_newLetDecls_172_);
lean_ctor_set(v_reuseFailAlloc_191_, 8, v_nextExprIdx_173_);
lean_ctor_set(v_reuseFailAlloc_191_, 9, v_exprMVarArgs_174_);
lean_ctor_set(v_reuseFailAlloc_191_, 10, v_exprFVarArgs_175_);
lean_ctor_set(v_reuseFailAlloc_191_, 11, v_toProcess_176_);
v___x_187_ = v_reuseFailAlloc_191_;
goto v_reusejp_186_;
}
v_reusejp_186_:
{
lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; 
v___x_188_ = lean_st_ref_set(v_a_160_, v___x_187_);
v___x_189_ = l_Lean_mkLevelParam(v___x_181_);
v___x_190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_190_, 0, v___x_189_);
return v___x_190_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkNewLevelParam___redArg___boxed(lean_object* v_u_193_, lean_object* v_a_194_, lean_object* v_a_195_){
_start:
{
lean_object* v_res_196_; 
v_res_196_ = l_Lean_Meta_Closure_mkNewLevelParam___redArg(v_u_193_, v_a_194_);
lean_dec(v_a_194_);
return v_res_196_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkNewLevelParam(lean_object* v_u_197_, uint8_t v_a_198_, lean_object* v_a_199_, lean_object* v_a_200_, lean_object* v_a_201_, lean_object* v_a_202_, lean_object* v_a_203_){
_start:
{
lean_object* v___x_205_; 
v___x_205_ = l_Lean_Meta_Closure_mkNewLevelParam___redArg(v_u_197_, v_a_199_);
return v___x_205_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkNewLevelParam___boxed(lean_object* v_u_206_, lean_object* v_a_207_, lean_object* v_a_208_, lean_object* v_a_209_, lean_object* v_a_210_, lean_object* v_a_211_, lean_object* v_a_212_, lean_object* v_a_213_){
_start:
{
uint8_t v_a_boxed_214_; lean_object* v_res_215_; 
v_a_boxed_214_ = lean_unbox(v_a_207_);
v_res_215_ = l_Lean_Meta_Closure_mkNewLevelParam(v_u_206_, v_a_boxed_214_, v_a_208_, v_a_209_, v_a_210_, v_a_211_, v_a_212_);
lean_dec(v_a_212_);
lean_dec_ref(v_a_211_);
lean_dec(v_a_210_);
lean_dec_ref(v_a_209_);
lean_dec(v_a_208_);
return v_res_215_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Closure_collectLevelAux_spec__0(lean_object* v_msg_216_){
_start:
{
lean_object* v___x_217_; lean_object* v___x_218_; 
v___x_217_ = lean_box(0);
v___x_218_ = lean_panic_fn_borrowed(v___x_217_, v_msg_216_);
return v___x_218_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectLevelAux_spec__1_spec__1___redArg(lean_object* v_a_219_, lean_object* v_x_220_){
_start:
{
if (lean_obj_tag(v_x_220_) == 0)
{
lean_object* v___x_221_; 
v___x_221_ = lean_box(0);
return v___x_221_;
}
else
{
lean_object* v_key_222_; lean_object* v_value_223_; lean_object* v_tail_224_; uint8_t v___x_225_; 
v_key_222_ = lean_ctor_get(v_x_220_, 0);
v_value_223_ = lean_ctor_get(v_x_220_, 1);
v_tail_224_ = lean_ctor_get(v_x_220_, 2);
v___x_225_ = lean_level_eq(v_key_222_, v_a_219_);
if (v___x_225_ == 0)
{
v_x_220_ = v_tail_224_;
goto _start;
}
else
{
lean_object* v___x_227_; 
lean_inc(v_value_223_);
v___x_227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_227_, 0, v_value_223_);
return v___x_227_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectLevelAux_spec__1_spec__1___redArg___boxed(lean_object* v_a_228_, lean_object* v_x_229_){
_start:
{
lean_object* v_res_230_; 
v_res_230_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectLevelAux_spec__1_spec__1___redArg(v_a_228_, v_x_229_);
lean_dec(v_x_229_);
lean_dec(v_a_228_);
return v_res_230_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectLevelAux_spec__1___redArg(lean_object* v_m_231_, lean_object* v_a_232_){
_start:
{
lean_object* v_buckets_233_; lean_object* v___x_234_; uint64_t v___x_235_; uint64_t v___x_236_; uint64_t v___x_237_; uint64_t v_fold_238_; uint64_t v___x_239_; uint64_t v___x_240_; uint64_t v___x_241_; size_t v___x_242_; size_t v___x_243_; size_t v___x_244_; size_t v___x_245_; size_t v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; 
v_buckets_233_ = lean_ctor_get(v_m_231_, 1);
v___x_234_ = lean_array_get_size(v_buckets_233_);
v___x_235_ = l_Lean_Level_hash(v_a_232_);
v___x_236_ = 32ULL;
v___x_237_ = lean_uint64_shift_right(v___x_235_, v___x_236_);
v_fold_238_ = lean_uint64_xor(v___x_235_, v___x_237_);
v___x_239_ = 16ULL;
v___x_240_ = lean_uint64_shift_right(v_fold_238_, v___x_239_);
v___x_241_ = lean_uint64_xor(v_fold_238_, v___x_240_);
v___x_242_ = lean_uint64_to_usize(v___x_241_);
v___x_243_ = lean_usize_of_nat(v___x_234_);
v___x_244_ = ((size_t)1ULL);
v___x_245_ = lean_usize_sub(v___x_243_, v___x_244_);
v___x_246_ = lean_usize_land(v___x_242_, v___x_245_);
v___x_247_ = lean_array_uget_borrowed(v_buckets_233_, v___x_246_);
v___x_248_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectLevelAux_spec__1_spec__1___redArg(v_a_232_, v___x_247_);
return v___x_248_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectLevelAux_spec__1___redArg___boxed(lean_object* v_m_249_, lean_object* v_a_250_){
_start:
{
lean_object* v_res_251_; 
v_res_251_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectLevelAux_spec__1___redArg(v_m_249_, v_a_250_);
lean_dec(v_a_250_);
lean_dec_ref(v_m_249_);
return v_res_251_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__4_spec__5_spec__6___redArg(lean_object* v_x_252_, lean_object* v_x_253_){
_start:
{
if (lean_obj_tag(v_x_253_) == 0)
{
return v_x_252_;
}
else
{
lean_object* v_key_254_; lean_object* v_value_255_; lean_object* v_tail_256_; lean_object* v___x_258_; uint8_t v_isShared_259_; uint8_t v_isSharedCheck_279_; 
v_key_254_ = lean_ctor_get(v_x_253_, 0);
v_value_255_ = lean_ctor_get(v_x_253_, 1);
v_tail_256_ = lean_ctor_get(v_x_253_, 2);
v_isSharedCheck_279_ = !lean_is_exclusive(v_x_253_);
if (v_isSharedCheck_279_ == 0)
{
v___x_258_ = v_x_253_;
v_isShared_259_ = v_isSharedCheck_279_;
goto v_resetjp_257_;
}
else
{
lean_inc(v_tail_256_);
lean_inc(v_value_255_);
lean_inc(v_key_254_);
lean_dec(v_x_253_);
v___x_258_ = lean_box(0);
v_isShared_259_ = v_isSharedCheck_279_;
goto v_resetjp_257_;
}
v_resetjp_257_:
{
lean_object* v___x_260_; uint64_t v___x_261_; uint64_t v___x_262_; uint64_t v___x_263_; uint64_t v_fold_264_; uint64_t v___x_265_; uint64_t v___x_266_; uint64_t v___x_267_; size_t v___x_268_; size_t v___x_269_; size_t v___x_270_; size_t v___x_271_; size_t v___x_272_; lean_object* v___x_273_; lean_object* v___x_275_; 
v___x_260_ = lean_array_get_size(v_x_252_);
v___x_261_ = l_Lean_Level_hash(v_key_254_);
v___x_262_ = 32ULL;
v___x_263_ = lean_uint64_shift_right(v___x_261_, v___x_262_);
v_fold_264_ = lean_uint64_xor(v___x_261_, v___x_263_);
v___x_265_ = 16ULL;
v___x_266_ = lean_uint64_shift_right(v_fold_264_, v___x_265_);
v___x_267_ = lean_uint64_xor(v_fold_264_, v___x_266_);
v___x_268_ = lean_uint64_to_usize(v___x_267_);
v___x_269_ = lean_usize_of_nat(v___x_260_);
v___x_270_ = ((size_t)1ULL);
v___x_271_ = lean_usize_sub(v___x_269_, v___x_270_);
v___x_272_ = lean_usize_land(v___x_268_, v___x_271_);
v___x_273_ = lean_array_uget_borrowed(v_x_252_, v___x_272_);
lean_inc(v___x_273_);
if (v_isShared_259_ == 0)
{
lean_ctor_set(v___x_258_, 2, v___x_273_);
v___x_275_ = v___x_258_;
goto v_reusejp_274_;
}
else
{
lean_object* v_reuseFailAlloc_278_; 
v_reuseFailAlloc_278_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_278_, 0, v_key_254_);
lean_ctor_set(v_reuseFailAlloc_278_, 1, v_value_255_);
lean_ctor_set(v_reuseFailAlloc_278_, 2, v___x_273_);
v___x_275_ = v_reuseFailAlloc_278_;
goto v_reusejp_274_;
}
v_reusejp_274_:
{
lean_object* v___x_276_; 
v___x_276_ = lean_array_uset(v_x_252_, v___x_272_, v___x_275_);
v_x_252_ = v___x_276_;
v_x_253_ = v_tail_256_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__4_spec__5___redArg(lean_object* v_i_280_, lean_object* v_source_281_, lean_object* v_target_282_){
_start:
{
lean_object* v___x_283_; uint8_t v___x_284_; 
v___x_283_ = lean_array_get_size(v_source_281_);
v___x_284_ = lean_nat_dec_lt(v_i_280_, v___x_283_);
if (v___x_284_ == 0)
{
lean_dec_ref(v_source_281_);
lean_dec(v_i_280_);
return v_target_282_;
}
else
{
lean_object* v_es_285_; lean_object* v___x_286_; lean_object* v_source_287_; lean_object* v_target_288_; lean_object* v___x_289_; lean_object* v___x_290_; 
v_es_285_ = lean_array_fget(v_source_281_, v_i_280_);
v___x_286_ = lean_box(0);
v_source_287_ = lean_array_fset(v_source_281_, v_i_280_, v___x_286_);
v_target_288_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__4_spec__5_spec__6___redArg(v_target_282_, v_es_285_);
v___x_289_ = lean_unsigned_to_nat(1u);
v___x_290_ = lean_nat_add(v_i_280_, v___x_289_);
lean_dec(v_i_280_);
v_i_280_ = v___x_290_;
v_source_281_ = v_source_287_;
v_target_282_ = v_target_288_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__4___redArg(lean_object* v_data_292_){
_start:
{
lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v_nbuckets_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; 
v___x_293_ = lean_array_get_size(v_data_292_);
v___x_294_ = lean_unsigned_to_nat(2u);
v_nbuckets_295_ = lean_nat_mul(v___x_293_, v___x_294_);
v___x_296_ = lean_unsigned_to_nat(0u);
v___x_297_ = lean_box(0);
v___x_298_ = lean_mk_array(v_nbuckets_295_, v___x_297_);
v___x_299_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__4_spec__5___redArg(v___x_296_, v_data_292_, v___x_298_);
return v___x_299_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__3___redArg(lean_object* v_a_300_, lean_object* v_x_301_){
_start:
{
if (lean_obj_tag(v_x_301_) == 0)
{
uint8_t v___x_302_; 
v___x_302_ = 0;
return v___x_302_;
}
else
{
lean_object* v_key_303_; lean_object* v_tail_304_; uint8_t v___x_305_; 
v_key_303_ = lean_ctor_get(v_x_301_, 0);
v_tail_304_ = lean_ctor_get(v_x_301_, 2);
v___x_305_ = lean_level_eq(v_key_303_, v_a_300_);
if (v___x_305_ == 0)
{
v_x_301_ = v_tail_304_;
goto _start;
}
else
{
return v___x_305_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__3___redArg___boxed(lean_object* v_a_307_, lean_object* v_x_308_){
_start:
{
uint8_t v_res_309_; lean_object* v_r_310_; 
v_res_309_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__3___redArg(v_a_307_, v_x_308_);
lean_dec(v_x_308_);
lean_dec(v_a_307_);
v_r_310_ = lean_box(v_res_309_);
return v_r_310_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__5___redArg(lean_object* v_a_311_, lean_object* v_b_312_, lean_object* v_x_313_){
_start:
{
if (lean_obj_tag(v_x_313_) == 0)
{
lean_dec(v_b_312_);
lean_dec(v_a_311_);
return v_x_313_;
}
else
{
lean_object* v_key_314_; lean_object* v_value_315_; lean_object* v_tail_316_; lean_object* v___x_318_; uint8_t v_isShared_319_; uint8_t v_isSharedCheck_328_; 
v_key_314_ = lean_ctor_get(v_x_313_, 0);
v_value_315_ = lean_ctor_get(v_x_313_, 1);
v_tail_316_ = lean_ctor_get(v_x_313_, 2);
v_isSharedCheck_328_ = !lean_is_exclusive(v_x_313_);
if (v_isSharedCheck_328_ == 0)
{
v___x_318_ = v_x_313_;
v_isShared_319_ = v_isSharedCheck_328_;
goto v_resetjp_317_;
}
else
{
lean_inc(v_tail_316_);
lean_inc(v_value_315_);
lean_inc(v_key_314_);
lean_dec(v_x_313_);
v___x_318_ = lean_box(0);
v_isShared_319_ = v_isSharedCheck_328_;
goto v_resetjp_317_;
}
v_resetjp_317_:
{
uint8_t v___x_320_; 
v___x_320_ = lean_level_eq(v_key_314_, v_a_311_);
if (v___x_320_ == 0)
{
lean_object* v___x_321_; lean_object* v___x_323_; 
v___x_321_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__5___redArg(v_a_311_, v_b_312_, v_tail_316_);
if (v_isShared_319_ == 0)
{
lean_ctor_set(v___x_318_, 2, v___x_321_);
v___x_323_ = v___x_318_;
goto v_reusejp_322_;
}
else
{
lean_object* v_reuseFailAlloc_324_; 
v_reuseFailAlloc_324_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_324_, 0, v_key_314_);
lean_ctor_set(v_reuseFailAlloc_324_, 1, v_value_315_);
lean_ctor_set(v_reuseFailAlloc_324_, 2, v___x_321_);
v___x_323_ = v_reuseFailAlloc_324_;
goto v_reusejp_322_;
}
v_reusejp_322_:
{
return v___x_323_;
}
}
else
{
lean_object* v___x_326_; 
lean_dec(v_value_315_);
lean_dec(v_key_314_);
if (v_isShared_319_ == 0)
{
lean_ctor_set(v___x_318_, 1, v_b_312_);
lean_ctor_set(v___x_318_, 0, v_a_311_);
v___x_326_ = v___x_318_;
goto v_reusejp_325_;
}
else
{
lean_object* v_reuseFailAlloc_327_; 
v_reuseFailAlloc_327_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_327_, 0, v_a_311_);
lean_ctor_set(v_reuseFailAlloc_327_, 1, v_b_312_);
lean_ctor_set(v_reuseFailAlloc_327_, 2, v_tail_316_);
v___x_326_ = v_reuseFailAlloc_327_;
goto v_reusejp_325_;
}
v_reusejp_325_:
{
return v___x_326_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2___redArg(lean_object* v_m_329_, lean_object* v_a_330_, lean_object* v_b_331_){
_start:
{
lean_object* v_size_332_; lean_object* v_buckets_333_; lean_object* v___x_335_; uint8_t v_isShared_336_; uint8_t v_isSharedCheck_376_; 
v_size_332_ = lean_ctor_get(v_m_329_, 0);
v_buckets_333_ = lean_ctor_get(v_m_329_, 1);
v_isSharedCheck_376_ = !lean_is_exclusive(v_m_329_);
if (v_isSharedCheck_376_ == 0)
{
v___x_335_ = v_m_329_;
v_isShared_336_ = v_isSharedCheck_376_;
goto v_resetjp_334_;
}
else
{
lean_inc(v_buckets_333_);
lean_inc(v_size_332_);
lean_dec(v_m_329_);
v___x_335_ = lean_box(0);
v_isShared_336_ = v_isSharedCheck_376_;
goto v_resetjp_334_;
}
v_resetjp_334_:
{
lean_object* v___x_337_; uint64_t v___x_338_; uint64_t v___x_339_; uint64_t v___x_340_; uint64_t v_fold_341_; uint64_t v___x_342_; uint64_t v___x_343_; uint64_t v___x_344_; size_t v___x_345_; size_t v___x_346_; size_t v___x_347_; size_t v___x_348_; size_t v___x_349_; lean_object* v_bkt_350_; uint8_t v___x_351_; 
v___x_337_ = lean_array_get_size(v_buckets_333_);
v___x_338_ = l_Lean_Level_hash(v_a_330_);
v___x_339_ = 32ULL;
v___x_340_ = lean_uint64_shift_right(v___x_338_, v___x_339_);
v_fold_341_ = lean_uint64_xor(v___x_338_, v___x_340_);
v___x_342_ = 16ULL;
v___x_343_ = lean_uint64_shift_right(v_fold_341_, v___x_342_);
v___x_344_ = lean_uint64_xor(v_fold_341_, v___x_343_);
v___x_345_ = lean_uint64_to_usize(v___x_344_);
v___x_346_ = lean_usize_of_nat(v___x_337_);
v___x_347_ = ((size_t)1ULL);
v___x_348_ = lean_usize_sub(v___x_346_, v___x_347_);
v___x_349_ = lean_usize_land(v___x_345_, v___x_348_);
v_bkt_350_ = lean_array_uget_borrowed(v_buckets_333_, v___x_349_);
v___x_351_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__3___redArg(v_a_330_, v_bkt_350_);
if (v___x_351_ == 0)
{
lean_object* v___x_352_; lean_object* v_size_x27_353_; lean_object* v___x_354_; lean_object* v_buckets_x27_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; uint8_t v___x_361_; 
v___x_352_ = lean_unsigned_to_nat(1u);
v_size_x27_353_ = lean_nat_add(v_size_332_, v___x_352_);
lean_dec(v_size_332_);
lean_inc(v_bkt_350_);
v___x_354_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_354_, 0, v_a_330_);
lean_ctor_set(v___x_354_, 1, v_b_331_);
lean_ctor_set(v___x_354_, 2, v_bkt_350_);
v_buckets_x27_355_ = lean_array_uset(v_buckets_333_, v___x_349_, v___x_354_);
v___x_356_ = lean_unsigned_to_nat(4u);
v___x_357_ = lean_nat_mul(v_size_x27_353_, v___x_356_);
v___x_358_ = lean_unsigned_to_nat(3u);
v___x_359_ = lean_nat_div(v___x_357_, v___x_358_);
lean_dec(v___x_357_);
v___x_360_ = lean_array_get_size(v_buckets_x27_355_);
v___x_361_ = lean_nat_dec_le(v___x_359_, v___x_360_);
lean_dec(v___x_359_);
if (v___x_361_ == 0)
{
lean_object* v_val_362_; lean_object* v___x_364_; 
v_val_362_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__4___redArg(v_buckets_x27_355_);
if (v_isShared_336_ == 0)
{
lean_ctor_set(v___x_335_, 1, v_val_362_);
lean_ctor_set(v___x_335_, 0, v_size_x27_353_);
v___x_364_ = v___x_335_;
goto v_reusejp_363_;
}
else
{
lean_object* v_reuseFailAlloc_365_; 
v_reuseFailAlloc_365_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_365_, 0, v_size_x27_353_);
lean_ctor_set(v_reuseFailAlloc_365_, 1, v_val_362_);
v___x_364_ = v_reuseFailAlloc_365_;
goto v_reusejp_363_;
}
v_reusejp_363_:
{
return v___x_364_;
}
}
else
{
lean_object* v___x_367_; 
if (v_isShared_336_ == 0)
{
lean_ctor_set(v___x_335_, 1, v_buckets_x27_355_);
lean_ctor_set(v___x_335_, 0, v_size_x27_353_);
v___x_367_ = v___x_335_;
goto v_reusejp_366_;
}
else
{
lean_object* v_reuseFailAlloc_368_; 
v_reuseFailAlloc_368_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_368_, 0, v_size_x27_353_);
lean_ctor_set(v_reuseFailAlloc_368_, 1, v_buckets_x27_355_);
v___x_367_ = v_reuseFailAlloc_368_;
goto v_reusejp_366_;
}
v_reusejp_366_:
{
return v___x_367_;
}
}
}
else
{
lean_object* v___x_369_; lean_object* v_buckets_x27_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_374_; 
lean_inc(v_bkt_350_);
v___x_369_ = lean_box(0);
v_buckets_x27_370_ = lean_array_uset(v_buckets_333_, v___x_349_, v___x_369_);
v___x_371_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__5___redArg(v_a_330_, v_b_331_, v_bkt_350_);
v___x_372_ = lean_array_uset(v_buckets_x27_370_, v___x_349_, v___x_371_);
if (v_isShared_336_ == 0)
{
lean_ctor_set(v___x_335_, 1, v___x_372_);
v___x_374_ = v___x_335_;
goto v_reusejp_373_;
}
else
{
lean_object* v_reuseFailAlloc_375_; 
v_reuseFailAlloc_375_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_375_, 0, v_size_332_);
lean_ctor_set(v_reuseFailAlloc_375_, 1, v___x_372_);
v___x_374_ = v_reuseFailAlloc_375_;
goto v_reusejp_373_;
}
v_reusejp_373_:
{
return v___x_374_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectLevelAux___redArg(lean_object* v_x_377_, lean_object* v_a_378_){
_start:
{
lean_object* v___y_381_; lean_object* v___y_382_; uint8_t v___y_383_; lean_object* v___y_389_; lean_object* v___y_390_; uint8_t v___y_391_; 
switch(lean_obj_tag(v_x_377_))
{
case 0:
{
lean_object* v___x_396_; 
v___x_396_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_396_, 0, v_x_377_);
return v___x_396_;
}
case 1:
{
lean_object* v_a_397_; lean_object* v_a_399_; uint8_t v___y_407_; uint8_t v___x_437_; uint8_t v___x_438_; 
v_a_397_ = lean_ctor_get(v_x_377_, 0);
v___x_437_ = l_Lean_Level_hasMVar(v_a_397_);
v___x_438_ = lean_bool_not(v___x_437_);
if (v___x_438_ == 0)
{
v___y_407_ = v___x_438_;
goto v___jp_406_;
}
else
{
uint8_t v___x_439_; uint8_t v___x_440_; 
v___x_439_ = l_Lean_Level_hasParam(v_a_397_);
v___x_440_ = lean_bool_not(v___x_439_);
v___y_407_ = v___x_440_;
goto v___jp_406_;
}
v___jp_398_:
{
size_t v___x_400_; size_t v___x_401_; uint8_t v___x_402_; 
v___x_400_ = lean_ptr_addr(v_a_397_);
v___x_401_ = lean_ptr_addr(v_a_399_);
v___x_402_ = lean_usize_dec_eq(v___x_400_, v___x_401_);
if (v___x_402_ == 0)
{
lean_object* v___x_403_; lean_object* v___x_404_; 
lean_dec_ref_known(v_x_377_, 1);
v___x_403_ = l_Lean_Level_succ___override(v_a_399_);
v___x_404_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_404_, 0, v___x_403_);
return v___x_404_;
}
else
{
lean_object* v___x_405_; 
lean_dec(v_a_399_);
v___x_405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_405_, 0, v_x_377_);
return v___x_405_;
}
}
v___jp_406_:
{
if (v___y_407_ == 0)
{
lean_object* v___x_408_; lean_object* v_visitedLevel_409_; lean_object* v___x_410_; 
v___x_408_ = lean_st_ref_get(v_a_378_);
v_visitedLevel_409_ = lean_ctor_get(v___x_408_, 0);
lean_inc_ref(v_visitedLevel_409_);
lean_dec(v___x_408_);
v___x_410_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectLevelAux_spec__1___redArg(v_visitedLevel_409_, v_a_397_);
lean_dec_ref(v_visitedLevel_409_);
if (lean_obj_tag(v___x_410_) == 0)
{
lean_object* v___x_411_; 
lean_inc(v_a_397_);
v___x_411_ = l_Lean_Meta_Closure_collectLevelAux___redArg(v_a_397_, v_a_378_);
if (lean_obj_tag(v___x_411_) == 0)
{
lean_object* v_a_412_; lean_object* v___x_413_; lean_object* v_visitedLevel_414_; lean_object* v_visitedExpr_415_; lean_object* v_levelParams_416_; lean_object* v_nextLevelIdx_417_; lean_object* v_levelArgs_418_; lean_object* v_newLocalDecls_419_; lean_object* v_newLocalDeclsForMVars_420_; lean_object* v_newLetDecls_421_; lean_object* v_nextExprIdx_422_; lean_object* v_exprMVarArgs_423_; lean_object* v_exprFVarArgs_424_; lean_object* v_toProcess_425_; lean_object* v___x_427_; uint8_t v_isShared_428_; uint8_t v_isSharedCheck_434_; 
v_a_412_ = lean_ctor_get(v___x_411_, 0);
lean_inc(v_a_412_);
lean_dec_ref_known(v___x_411_, 1);
v___x_413_ = lean_st_ref_take(v_a_378_);
v_visitedLevel_414_ = lean_ctor_get(v___x_413_, 0);
v_visitedExpr_415_ = lean_ctor_get(v___x_413_, 1);
v_levelParams_416_ = lean_ctor_get(v___x_413_, 2);
v_nextLevelIdx_417_ = lean_ctor_get(v___x_413_, 3);
v_levelArgs_418_ = lean_ctor_get(v___x_413_, 4);
v_newLocalDecls_419_ = lean_ctor_get(v___x_413_, 5);
v_newLocalDeclsForMVars_420_ = lean_ctor_get(v___x_413_, 6);
v_newLetDecls_421_ = lean_ctor_get(v___x_413_, 7);
v_nextExprIdx_422_ = lean_ctor_get(v___x_413_, 8);
v_exprMVarArgs_423_ = lean_ctor_get(v___x_413_, 9);
v_exprFVarArgs_424_ = lean_ctor_get(v___x_413_, 10);
v_toProcess_425_ = lean_ctor_get(v___x_413_, 11);
v_isSharedCheck_434_ = !lean_is_exclusive(v___x_413_);
if (v_isSharedCheck_434_ == 0)
{
v___x_427_ = v___x_413_;
v_isShared_428_ = v_isSharedCheck_434_;
goto v_resetjp_426_;
}
else
{
lean_inc(v_toProcess_425_);
lean_inc(v_exprFVarArgs_424_);
lean_inc(v_exprMVarArgs_423_);
lean_inc(v_nextExprIdx_422_);
lean_inc(v_newLetDecls_421_);
lean_inc(v_newLocalDeclsForMVars_420_);
lean_inc(v_newLocalDecls_419_);
lean_inc(v_levelArgs_418_);
lean_inc(v_nextLevelIdx_417_);
lean_inc(v_levelParams_416_);
lean_inc(v_visitedExpr_415_);
lean_inc(v_visitedLevel_414_);
lean_dec(v___x_413_);
v___x_427_ = lean_box(0);
v_isShared_428_ = v_isSharedCheck_434_;
goto v_resetjp_426_;
}
v_resetjp_426_:
{
lean_object* v___x_429_; lean_object* v___x_431_; 
lean_inc(v_a_412_);
lean_inc(v_a_397_);
v___x_429_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2___redArg(v_visitedLevel_414_, v_a_397_, v_a_412_);
if (v_isShared_428_ == 0)
{
lean_ctor_set(v___x_427_, 0, v___x_429_);
v___x_431_ = v___x_427_;
goto v_reusejp_430_;
}
else
{
lean_object* v_reuseFailAlloc_433_; 
v_reuseFailAlloc_433_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_433_, 0, v___x_429_);
lean_ctor_set(v_reuseFailAlloc_433_, 1, v_visitedExpr_415_);
lean_ctor_set(v_reuseFailAlloc_433_, 2, v_levelParams_416_);
lean_ctor_set(v_reuseFailAlloc_433_, 3, v_nextLevelIdx_417_);
lean_ctor_set(v_reuseFailAlloc_433_, 4, v_levelArgs_418_);
lean_ctor_set(v_reuseFailAlloc_433_, 5, v_newLocalDecls_419_);
lean_ctor_set(v_reuseFailAlloc_433_, 6, v_newLocalDeclsForMVars_420_);
lean_ctor_set(v_reuseFailAlloc_433_, 7, v_newLetDecls_421_);
lean_ctor_set(v_reuseFailAlloc_433_, 8, v_nextExprIdx_422_);
lean_ctor_set(v_reuseFailAlloc_433_, 9, v_exprMVarArgs_423_);
lean_ctor_set(v_reuseFailAlloc_433_, 10, v_exprFVarArgs_424_);
lean_ctor_set(v_reuseFailAlloc_433_, 11, v_toProcess_425_);
v___x_431_ = v_reuseFailAlloc_433_;
goto v_reusejp_430_;
}
v_reusejp_430_:
{
lean_object* v___x_432_; 
v___x_432_ = lean_st_ref_set(v_a_378_, v___x_431_);
v_a_399_ = v_a_412_;
goto v___jp_398_;
}
}
}
else
{
if (lean_obj_tag(v___x_411_) == 0)
{
lean_object* v_a_435_; 
v_a_435_ = lean_ctor_get(v___x_411_, 0);
lean_inc(v_a_435_);
lean_dec_ref_known(v___x_411_, 1);
v_a_399_ = v_a_435_;
goto v___jp_398_;
}
else
{
lean_dec_ref_known(v_x_377_, 1);
return v___x_411_;
}
}
}
else
{
lean_object* v_val_436_; 
v_val_436_ = lean_ctor_get(v___x_410_, 0);
lean_inc(v_val_436_);
lean_dec_ref_known(v___x_410_, 1);
v_a_399_ = v_val_436_;
goto v___jp_398_;
}
}
else
{
lean_inc(v_a_397_);
v_a_399_ = v_a_397_;
goto v___jp_398_;
}
}
}
case 2:
{
lean_object* v_a_441_; lean_object* v_a_442_; lean_object* v___y_444_; lean_object* v_a_445_; lean_object* v___y_453_; uint8_t v___y_454_; lean_object* v_a_485_; uint8_t v___y_491_; uint8_t v___x_521_; uint8_t v___x_522_; 
v_a_441_ = lean_ctor_get(v_x_377_, 0);
v_a_442_ = lean_ctor_get(v_x_377_, 1);
v___x_521_ = l_Lean_Level_hasMVar(v_a_441_);
v___x_522_ = lean_bool_not(v___x_521_);
if (v___x_522_ == 0)
{
v___y_491_ = v___x_522_;
goto v___jp_490_;
}
else
{
uint8_t v___x_523_; uint8_t v___x_524_; 
v___x_523_ = l_Lean_Level_hasParam(v_a_441_);
v___x_524_ = lean_bool_not(v___x_523_);
v___y_491_ = v___x_524_;
goto v___jp_490_;
}
v___jp_443_:
{
size_t v___x_446_; size_t v___x_447_; uint8_t v___x_448_; 
v___x_446_ = lean_ptr_addr(v_a_441_);
v___x_447_ = lean_ptr_addr(v___y_444_);
v___x_448_ = lean_usize_dec_eq(v___x_446_, v___x_447_);
if (v___x_448_ == 0)
{
v___y_389_ = v_a_445_;
v___y_390_ = v___y_444_;
v___y_391_ = v___x_448_;
goto v___jp_388_;
}
else
{
size_t v___x_449_; size_t v___x_450_; uint8_t v___x_451_; 
v___x_449_ = lean_ptr_addr(v_a_442_);
v___x_450_ = lean_ptr_addr(v_a_445_);
v___x_451_ = lean_usize_dec_eq(v___x_449_, v___x_450_);
v___y_389_ = v_a_445_;
v___y_390_ = v___y_444_;
v___y_391_ = v___x_451_;
goto v___jp_388_;
}
}
v___jp_452_:
{
if (v___y_454_ == 0)
{
lean_object* v___x_455_; lean_object* v_visitedLevel_456_; lean_object* v___x_457_; 
v___x_455_ = lean_st_ref_get(v_a_378_);
v_visitedLevel_456_ = lean_ctor_get(v___x_455_, 0);
lean_inc_ref(v_visitedLevel_456_);
lean_dec(v___x_455_);
v___x_457_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectLevelAux_spec__1___redArg(v_visitedLevel_456_, v_a_442_);
lean_dec_ref(v_visitedLevel_456_);
if (lean_obj_tag(v___x_457_) == 0)
{
lean_object* v___x_458_; 
lean_inc(v_a_442_);
v___x_458_ = l_Lean_Meta_Closure_collectLevelAux___redArg(v_a_442_, v_a_378_);
if (lean_obj_tag(v___x_458_) == 0)
{
lean_object* v_a_459_; lean_object* v___x_460_; lean_object* v_visitedLevel_461_; lean_object* v_visitedExpr_462_; lean_object* v_levelParams_463_; lean_object* v_nextLevelIdx_464_; lean_object* v_levelArgs_465_; lean_object* v_newLocalDecls_466_; lean_object* v_newLocalDeclsForMVars_467_; lean_object* v_newLetDecls_468_; lean_object* v_nextExprIdx_469_; lean_object* v_exprMVarArgs_470_; lean_object* v_exprFVarArgs_471_; lean_object* v_toProcess_472_; lean_object* v___x_474_; uint8_t v_isShared_475_; uint8_t v_isSharedCheck_481_; 
v_a_459_ = lean_ctor_get(v___x_458_, 0);
lean_inc(v_a_459_);
lean_dec_ref_known(v___x_458_, 1);
v___x_460_ = lean_st_ref_take(v_a_378_);
v_visitedLevel_461_ = lean_ctor_get(v___x_460_, 0);
v_visitedExpr_462_ = lean_ctor_get(v___x_460_, 1);
v_levelParams_463_ = lean_ctor_get(v___x_460_, 2);
v_nextLevelIdx_464_ = lean_ctor_get(v___x_460_, 3);
v_levelArgs_465_ = lean_ctor_get(v___x_460_, 4);
v_newLocalDecls_466_ = lean_ctor_get(v___x_460_, 5);
v_newLocalDeclsForMVars_467_ = lean_ctor_get(v___x_460_, 6);
v_newLetDecls_468_ = lean_ctor_get(v___x_460_, 7);
v_nextExprIdx_469_ = lean_ctor_get(v___x_460_, 8);
v_exprMVarArgs_470_ = lean_ctor_get(v___x_460_, 9);
v_exprFVarArgs_471_ = lean_ctor_get(v___x_460_, 10);
v_toProcess_472_ = lean_ctor_get(v___x_460_, 11);
v_isSharedCheck_481_ = !lean_is_exclusive(v___x_460_);
if (v_isSharedCheck_481_ == 0)
{
v___x_474_ = v___x_460_;
v_isShared_475_ = v_isSharedCheck_481_;
goto v_resetjp_473_;
}
else
{
lean_inc(v_toProcess_472_);
lean_inc(v_exprFVarArgs_471_);
lean_inc(v_exprMVarArgs_470_);
lean_inc(v_nextExprIdx_469_);
lean_inc(v_newLetDecls_468_);
lean_inc(v_newLocalDeclsForMVars_467_);
lean_inc(v_newLocalDecls_466_);
lean_inc(v_levelArgs_465_);
lean_inc(v_nextLevelIdx_464_);
lean_inc(v_levelParams_463_);
lean_inc(v_visitedExpr_462_);
lean_inc(v_visitedLevel_461_);
lean_dec(v___x_460_);
v___x_474_ = lean_box(0);
v_isShared_475_ = v_isSharedCheck_481_;
goto v_resetjp_473_;
}
v_resetjp_473_:
{
lean_object* v___x_476_; lean_object* v___x_478_; 
lean_inc(v_a_459_);
lean_inc(v_a_442_);
v___x_476_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2___redArg(v_visitedLevel_461_, v_a_442_, v_a_459_);
if (v_isShared_475_ == 0)
{
lean_ctor_set(v___x_474_, 0, v___x_476_);
v___x_478_ = v___x_474_;
goto v_reusejp_477_;
}
else
{
lean_object* v_reuseFailAlloc_480_; 
v_reuseFailAlloc_480_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_480_, 0, v___x_476_);
lean_ctor_set(v_reuseFailAlloc_480_, 1, v_visitedExpr_462_);
lean_ctor_set(v_reuseFailAlloc_480_, 2, v_levelParams_463_);
lean_ctor_set(v_reuseFailAlloc_480_, 3, v_nextLevelIdx_464_);
lean_ctor_set(v_reuseFailAlloc_480_, 4, v_levelArgs_465_);
lean_ctor_set(v_reuseFailAlloc_480_, 5, v_newLocalDecls_466_);
lean_ctor_set(v_reuseFailAlloc_480_, 6, v_newLocalDeclsForMVars_467_);
lean_ctor_set(v_reuseFailAlloc_480_, 7, v_newLetDecls_468_);
lean_ctor_set(v_reuseFailAlloc_480_, 8, v_nextExprIdx_469_);
lean_ctor_set(v_reuseFailAlloc_480_, 9, v_exprMVarArgs_470_);
lean_ctor_set(v_reuseFailAlloc_480_, 10, v_exprFVarArgs_471_);
lean_ctor_set(v_reuseFailAlloc_480_, 11, v_toProcess_472_);
v___x_478_ = v_reuseFailAlloc_480_;
goto v_reusejp_477_;
}
v_reusejp_477_:
{
lean_object* v___x_479_; 
v___x_479_ = lean_st_ref_set(v_a_378_, v___x_478_);
v___y_444_ = v___y_453_;
v_a_445_ = v_a_459_;
goto v___jp_443_;
}
}
}
else
{
if (lean_obj_tag(v___x_458_) == 0)
{
lean_object* v_a_482_; 
v_a_482_ = lean_ctor_get(v___x_458_, 0);
lean_inc(v_a_482_);
lean_dec_ref_known(v___x_458_, 1);
v___y_444_ = v___y_453_;
v_a_445_ = v_a_482_;
goto v___jp_443_;
}
else
{
lean_dec(v___y_453_);
lean_dec_ref_known(v_x_377_, 2);
return v___x_458_;
}
}
}
else
{
lean_object* v_val_483_; 
v_val_483_ = lean_ctor_get(v___x_457_, 0);
lean_inc(v_val_483_);
lean_dec_ref_known(v___x_457_, 1);
v___y_444_ = v___y_453_;
v_a_445_ = v_val_483_;
goto v___jp_443_;
}
}
else
{
lean_inc(v_a_442_);
v___y_444_ = v___y_453_;
v_a_445_ = v_a_442_;
goto v___jp_443_;
}
}
v___jp_484_:
{
uint8_t v___x_486_; uint8_t v___x_487_; 
v___x_486_ = l_Lean_Level_hasMVar(v_a_442_);
v___x_487_ = lean_bool_not(v___x_486_);
if (v___x_487_ == 0)
{
v___y_453_ = v_a_485_;
v___y_454_ = v___x_487_;
goto v___jp_452_;
}
else
{
uint8_t v___x_488_; uint8_t v___x_489_; 
v___x_488_ = l_Lean_Level_hasParam(v_a_442_);
v___x_489_ = lean_bool_not(v___x_488_);
v___y_453_ = v_a_485_;
v___y_454_ = v___x_489_;
goto v___jp_452_;
}
}
v___jp_490_:
{
if (v___y_491_ == 0)
{
lean_object* v___x_492_; lean_object* v_visitedLevel_493_; lean_object* v___x_494_; 
v___x_492_ = lean_st_ref_get(v_a_378_);
v_visitedLevel_493_ = lean_ctor_get(v___x_492_, 0);
lean_inc_ref(v_visitedLevel_493_);
lean_dec(v___x_492_);
v___x_494_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectLevelAux_spec__1___redArg(v_visitedLevel_493_, v_a_441_);
lean_dec_ref(v_visitedLevel_493_);
if (lean_obj_tag(v___x_494_) == 0)
{
lean_object* v___x_495_; 
lean_inc(v_a_441_);
v___x_495_ = l_Lean_Meta_Closure_collectLevelAux___redArg(v_a_441_, v_a_378_);
if (lean_obj_tag(v___x_495_) == 0)
{
lean_object* v_a_496_; lean_object* v___x_497_; lean_object* v_visitedLevel_498_; lean_object* v_visitedExpr_499_; lean_object* v_levelParams_500_; lean_object* v_nextLevelIdx_501_; lean_object* v_levelArgs_502_; lean_object* v_newLocalDecls_503_; lean_object* v_newLocalDeclsForMVars_504_; lean_object* v_newLetDecls_505_; lean_object* v_nextExprIdx_506_; lean_object* v_exprMVarArgs_507_; lean_object* v_exprFVarArgs_508_; lean_object* v_toProcess_509_; lean_object* v___x_511_; uint8_t v_isShared_512_; uint8_t v_isSharedCheck_518_; 
v_a_496_ = lean_ctor_get(v___x_495_, 0);
lean_inc(v_a_496_);
lean_dec_ref_known(v___x_495_, 1);
v___x_497_ = lean_st_ref_take(v_a_378_);
v_visitedLevel_498_ = lean_ctor_get(v___x_497_, 0);
v_visitedExpr_499_ = lean_ctor_get(v___x_497_, 1);
v_levelParams_500_ = lean_ctor_get(v___x_497_, 2);
v_nextLevelIdx_501_ = lean_ctor_get(v___x_497_, 3);
v_levelArgs_502_ = lean_ctor_get(v___x_497_, 4);
v_newLocalDecls_503_ = lean_ctor_get(v___x_497_, 5);
v_newLocalDeclsForMVars_504_ = lean_ctor_get(v___x_497_, 6);
v_newLetDecls_505_ = lean_ctor_get(v___x_497_, 7);
v_nextExprIdx_506_ = lean_ctor_get(v___x_497_, 8);
v_exprMVarArgs_507_ = lean_ctor_get(v___x_497_, 9);
v_exprFVarArgs_508_ = lean_ctor_get(v___x_497_, 10);
v_toProcess_509_ = lean_ctor_get(v___x_497_, 11);
v_isSharedCheck_518_ = !lean_is_exclusive(v___x_497_);
if (v_isSharedCheck_518_ == 0)
{
v___x_511_ = v___x_497_;
v_isShared_512_ = v_isSharedCheck_518_;
goto v_resetjp_510_;
}
else
{
lean_inc(v_toProcess_509_);
lean_inc(v_exprFVarArgs_508_);
lean_inc(v_exprMVarArgs_507_);
lean_inc(v_nextExprIdx_506_);
lean_inc(v_newLetDecls_505_);
lean_inc(v_newLocalDeclsForMVars_504_);
lean_inc(v_newLocalDecls_503_);
lean_inc(v_levelArgs_502_);
lean_inc(v_nextLevelIdx_501_);
lean_inc(v_levelParams_500_);
lean_inc(v_visitedExpr_499_);
lean_inc(v_visitedLevel_498_);
lean_dec(v___x_497_);
v___x_511_ = lean_box(0);
v_isShared_512_ = v_isSharedCheck_518_;
goto v_resetjp_510_;
}
v_resetjp_510_:
{
lean_object* v___x_513_; lean_object* v___x_515_; 
lean_inc(v_a_496_);
lean_inc(v_a_441_);
v___x_513_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2___redArg(v_visitedLevel_498_, v_a_441_, v_a_496_);
if (v_isShared_512_ == 0)
{
lean_ctor_set(v___x_511_, 0, v___x_513_);
v___x_515_ = v___x_511_;
goto v_reusejp_514_;
}
else
{
lean_object* v_reuseFailAlloc_517_; 
v_reuseFailAlloc_517_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_517_, 0, v___x_513_);
lean_ctor_set(v_reuseFailAlloc_517_, 1, v_visitedExpr_499_);
lean_ctor_set(v_reuseFailAlloc_517_, 2, v_levelParams_500_);
lean_ctor_set(v_reuseFailAlloc_517_, 3, v_nextLevelIdx_501_);
lean_ctor_set(v_reuseFailAlloc_517_, 4, v_levelArgs_502_);
lean_ctor_set(v_reuseFailAlloc_517_, 5, v_newLocalDecls_503_);
lean_ctor_set(v_reuseFailAlloc_517_, 6, v_newLocalDeclsForMVars_504_);
lean_ctor_set(v_reuseFailAlloc_517_, 7, v_newLetDecls_505_);
lean_ctor_set(v_reuseFailAlloc_517_, 8, v_nextExprIdx_506_);
lean_ctor_set(v_reuseFailAlloc_517_, 9, v_exprMVarArgs_507_);
lean_ctor_set(v_reuseFailAlloc_517_, 10, v_exprFVarArgs_508_);
lean_ctor_set(v_reuseFailAlloc_517_, 11, v_toProcess_509_);
v___x_515_ = v_reuseFailAlloc_517_;
goto v_reusejp_514_;
}
v_reusejp_514_:
{
lean_object* v___x_516_; 
v___x_516_ = lean_st_ref_set(v_a_378_, v___x_515_);
v_a_485_ = v_a_496_;
goto v___jp_484_;
}
}
}
else
{
if (lean_obj_tag(v___x_495_) == 0)
{
lean_object* v_a_519_; 
v_a_519_ = lean_ctor_get(v___x_495_, 0);
lean_inc(v_a_519_);
lean_dec_ref_known(v___x_495_, 1);
v_a_485_ = v_a_519_;
goto v___jp_484_;
}
else
{
lean_dec_ref_known(v_x_377_, 2);
return v___x_495_;
}
}
}
else
{
lean_object* v_val_520_; 
v_val_520_ = lean_ctor_get(v___x_494_, 0);
lean_inc(v_val_520_);
lean_dec_ref_known(v___x_494_, 1);
v_a_485_ = v_val_520_;
goto v___jp_484_;
}
}
else
{
lean_inc(v_a_441_);
v_a_485_ = v_a_441_;
goto v___jp_484_;
}
}
}
case 3:
{
lean_object* v_a_525_; lean_object* v_a_526_; lean_object* v___y_528_; lean_object* v_a_529_; lean_object* v___y_537_; uint8_t v___y_538_; lean_object* v_a_569_; uint8_t v___y_575_; uint8_t v___x_605_; uint8_t v___x_606_; 
v_a_525_ = lean_ctor_get(v_x_377_, 0);
v_a_526_ = lean_ctor_get(v_x_377_, 1);
v___x_605_ = l_Lean_Level_hasMVar(v_a_525_);
v___x_606_ = lean_bool_not(v___x_605_);
if (v___x_606_ == 0)
{
v___y_575_ = v___x_606_;
goto v___jp_574_;
}
else
{
uint8_t v___x_607_; uint8_t v___x_608_; 
v___x_607_ = l_Lean_Level_hasParam(v_a_525_);
v___x_608_ = lean_bool_not(v___x_607_);
v___y_575_ = v___x_608_;
goto v___jp_574_;
}
v___jp_527_:
{
size_t v___x_530_; size_t v___x_531_; uint8_t v___x_532_; 
v___x_530_ = lean_ptr_addr(v_a_525_);
v___x_531_ = lean_ptr_addr(v___y_528_);
v___x_532_ = lean_usize_dec_eq(v___x_530_, v___x_531_);
if (v___x_532_ == 0)
{
v___y_381_ = v_a_529_;
v___y_382_ = v___y_528_;
v___y_383_ = v___x_532_;
goto v___jp_380_;
}
else
{
size_t v___x_533_; size_t v___x_534_; uint8_t v___x_535_; 
v___x_533_ = lean_ptr_addr(v_a_526_);
v___x_534_ = lean_ptr_addr(v_a_529_);
v___x_535_ = lean_usize_dec_eq(v___x_533_, v___x_534_);
v___y_381_ = v_a_529_;
v___y_382_ = v___y_528_;
v___y_383_ = v___x_535_;
goto v___jp_380_;
}
}
v___jp_536_:
{
if (v___y_538_ == 0)
{
lean_object* v___x_539_; lean_object* v_visitedLevel_540_; lean_object* v___x_541_; 
v___x_539_ = lean_st_ref_get(v_a_378_);
v_visitedLevel_540_ = lean_ctor_get(v___x_539_, 0);
lean_inc_ref(v_visitedLevel_540_);
lean_dec(v___x_539_);
v___x_541_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectLevelAux_spec__1___redArg(v_visitedLevel_540_, v_a_526_);
lean_dec_ref(v_visitedLevel_540_);
if (lean_obj_tag(v___x_541_) == 0)
{
lean_object* v___x_542_; 
lean_inc(v_a_526_);
v___x_542_ = l_Lean_Meta_Closure_collectLevelAux___redArg(v_a_526_, v_a_378_);
if (lean_obj_tag(v___x_542_) == 0)
{
lean_object* v_a_543_; lean_object* v___x_544_; lean_object* v_visitedLevel_545_; lean_object* v_visitedExpr_546_; lean_object* v_levelParams_547_; lean_object* v_nextLevelIdx_548_; lean_object* v_levelArgs_549_; lean_object* v_newLocalDecls_550_; lean_object* v_newLocalDeclsForMVars_551_; lean_object* v_newLetDecls_552_; lean_object* v_nextExprIdx_553_; lean_object* v_exprMVarArgs_554_; lean_object* v_exprFVarArgs_555_; lean_object* v_toProcess_556_; lean_object* v___x_558_; uint8_t v_isShared_559_; uint8_t v_isSharedCheck_565_; 
v_a_543_ = lean_ctor_get(v___x_542_, 0);
lean_inc(v_a_543_);
lean_dec_ref_known(v___x_542_, 1);
v___x_544_ = lean_st_ref_take(v_a_378_);
v_visitedLevel_545_ = lean_ctor_get(v___x_544_, 0);
v_visitedExpr_546_ = lean_ctor_get(v___x_544_, 1);
v_levelParams_547_ = lean_ctor_get(v___x_544_, 2);
v_nextLevelIdx_548_ = lean_ctor_get(v___x_544_, 3);
v_levelArgs_549_ = lean_ctor_get(v___x_544_, 4);
v_newLocalDecls_550_ = lean_ctor_get(v___x_544_, 5);
v_newLocalDeclsForMVars_551_ = lean_ctor_get(v___x_544_, 6);
v_newLetDecls_552_ = lean_ctor_get(v___x_544_, 7);
v_nextExprIdx_553_ = lean_ctor_get(v___x_544_, 8);
v_exprMVarArgs_554_ = lean_ctor_get(v___x_544_, 9);
v_exprFVarArgs_555_ = lean_ctor_get(v___x_544_, 10);
v_toProcess_556_ = lean_ctor_get(v___x_544_, 11);
v_isSharedCheck_565_ = !lean_is_exclusive(v___x_544_);
if (v_isSharedCheck_565_ == 0)
{
v___x_558_ = v___x_544_;
v_isShared_559_ = v_isSharedCheck_565_;
goto v_resetjp_557_;
}
else
{
lean_inc(v_toProcess_556_);
lean_inc(v_exprFVarArgs_555_);
lean_inc(v_exprMVarArgs_554_);
lean_inc(v_nextExprIdx_553_);
lean_inc(v_newLetDecls_552_);
lean_inc(v_newLocalDeclsForMVars_551_);
lean_inc(v_newLocalDecls_550_);
lean_inc(v_levelArgs_549_);
lean_inc(v_nextLevelIdx_548_);
lean_inc(v_levelParams_547_);
lean_inc(v_visitedExpr_546_);
lean_inc(v_visitedLevel_545_);
lean_dec(v___x_544_);
v___x_558_ = lean_box(0);
v_isShared_559_ = v_isSharedCheck_565_;
goto v_resetjp_557_;
}
v_resetjp_557_:
{
lean_object* v___x_560_; lean_object* v___x_562_; 
lean_inc(v_a_543_);
lean_inc(v_a_526_);
v___x_560_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2___redArg(v_visitedLevel_545_, v_a_526_, v_a_543_);
if (v_isShared_559_ == 0)
{
lean_ctor_set(v___x_558_, 0, v___x_560_);
v___x_562_ = v___x_558_;
goto v_reusejp_561_;
}
else
{
lean_object* v_reuseFailAlloc_564_; 
v_reuseFailAlloc_564_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_564_, 0, v___x_560_);
lean_ctor_set(v_reuseFailAlloc_564_, 1, v_visitedExpr_546_);
lean_ctor_set(v_reuseFailAlloc_564_, 2, v_levelParams_547_);
lean_ctor_set(v_reuseFailAlloc_564_, 3, v_nextLevelIdx_548_);
lean_ctor_set(v_reuseFailAlloc_564_, 4, v_levelArgs_549_);
lean_ctor_set(v_reuseFailAlloc_564_, 5, v_newLocalDecls_550_);
lean_ctor_set(v_reuseFailAlloc_564_, 6, v_newLocalDeclsForMVars_551_);
lean_ctor_set(v_reuseFailAlloc_564_, 7, v_newLetDecls_552_);
lean_ctor_set(v_reuseFailAlloc_564_, 8, v_nextExprIdx_553_);
lean_ctor_set(v_reuseFailAlloc_564_, 9, v_exprMVarArgs_554_);
lean_ctor_set(v_reuseFailAlloc_564_, 10, v_exprFVarArgs_555_);
lean_ctor_set(v_reuseFailAlloc_564_, 11, v_toProcess_556_);
v___x_562_ = v_reuseFailAlloc_564_;
goto v_reusejp_561_;
}
v_reusejp_561_:
{
lean_object* v___x_563_; 
v___x_563_ = lean_st_ref_set(v_a_378_, v___x_562_);
v___y_528_ = v___y_537_;
v_a_529_ = v_a_543_;
goto v___jp_527_;
}
}
}
else
{
if (lean_obj_tag(v___x_542_) == 0)
{
lean_object* v_a_566_; 
v_a_566_ = lean_ctor_get(v___x_542_, 0);
lean_inc(v_a_566_);
lean_dec_ref_known(v___x_542_, 1);
v___y_528_ = v___y_537_;
v_a_529_ = v_a_566_;
goto v___jp_527_;
}
else
{
lean_dec(v___y_537_);
lean_dec_ref_known(v_x_377_, 2);
return v___x_542_;
}
}
}
else
{
lean_object* v_val_567_; 
v_val_567_ = lean_ctor_get(v___x_541_, 0);
lean_inc(v_val_567_);
lean_dec_ref_known(v___x_541_, 1);
v___y_528_ = v___y_537_;
v_a_529_ = v_val_567_;
goto v___jp_527_;
}
}
else
{
lean_inc(v_a_526_);
v___y_528_ = v___y_537_;
v_a_529_ = v_a_526_;
goto v___jp_527_;
}
}
v___jp_568_:
{
uint8_t v___x_570_; uint8_t v___x_571_; 
v___x_570_ = l_Lean_Level_hasMVar(v_a_526_);
v___x_571_ = lean_bool_not(v___x_570_);
if (v___x_571_ == 0)
{
v___y_537_ = v_a_569_;
v___y_538_ = v___x_571_;
goto v___jp_536_;
}
else
{
uint8_t v___x_572_; uint8_t v___x_573_; 
v___x_572_ = l_Lean_Level_hasParam(v_a_526_);
v___x_573_ = lean_bool_not(v___x_572_);
v___y_537_ = v_a_569_;
v___y_538_ = v___x_573_;
goto v___jp_536_;
}
}
v___jp_574_:
{
if (v___y_575_ == 0)
{
lean_object* v___x_576_; lean_object* v_visitedLevel_577_; lean_object* v___x_578_; 
v___x_576_ = lean_st_ref_get(v_a_378_);
v_visitedLevel_577_ = lean_ctor_get(v___x_576_, 0);
lean_inc_ref(v_visitedLevel_577_);
lean_dec(v___x_576_);
v___x_578_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectLevelAux_spec__1___redArg(v_visitedLevel_577_, v_a_525_);
lean_dec_ref(v_visitedLevel_577_);
if (lean_obj_tag(v___x_578_) == 0)
{
lean_object* v___x_579_; 
lean_inc(v_a_525_);
v___x_579_ = l_Lean_Meta_Closure_collectLevelAux___redArg(v_a_525_, v_a_378_);
if (lean_obj_tag(v___x_579_) == 0)
{
lean_object* v_a_580_; lean_object* v___x_581_; lean_object* v_visitedLevel_582_; lean_object* v_visitedExpr_583_; lean_object* v_levelParams_584_; lean_object* v_nextLevelIdx_585_; lean_object* v_levelArgs_586_; lean_object* v_newLocalDecls_587_; lean_object* v_newLocalDeclsForMVars_588_; lean_object* v_newLetDecls_589_; lean_object* v_nextExprIdx_590_; lean_object* v_exprMVarArgs_591_; lean_object* v_exprFVarArgs_592_; lean_object* v_toProcess_593_; lean_object* v___x_595_; uint8_t v_isShared_596_; uint8_t v_isSharedCheck_602_; 
v_a_580_ = lean_ctor_get(v___x_579_, 0);
lean_inc(v_a_580_);
lean_dec_ref_known(v___x_579_, 1);
v___x_581_ = lean_st_ref_take(v_a_378_);
v_visitedLevel_582_ = lean_ctor_get(v___x_581_, 0);
v_visitedExpr_583_ = lean_ctor_get(v___x_581_, 1);
v_levelParams_584_ = lean_ctor_get(v___x_581_, 2);
v_nextLevelIdx_585_ = lean_ctor_get(v___x_581_, 3);
v_levelArgs_586_ = lean_ctor_get(v___x_581_, 4);
v_newLocalDecls_587_ = lean_ctor_get(v___x_581_, 5);
v_newLocalDeclsForMVars_588_ = lean_ctor_get(v___x_581_, 6);
v_newLetDecls_589_ = lean_ctor_get(v___x_581_, 7);
v_nextExprIdx_590_ = lean_ctor_get(v___x_581_, 8);
v_exprMVarArgs_591_ = lean_ctor_get(v___x_581_, 9);
v_exprFVarArgs_592_ = lean_ctor_get(v___x_581_, 10);
v_toProcess_593_ = lean_ctor_get(v___x_581_, 11);
v_isSharedCheck_602_ = !lean_is_exclusive(v___x_581_);
if (v_isSharedCheck_602_ == 0)
{
v___x_595_ = v___x_581_;
v_isShared_596_ = v_isSharedCheck_602_;
goto v_resetjp_594_;
}
else
{
lean_inc(v_toProcess_593_);
lean_inc(v_exprFVarArgs_592_);
lean_inc(v_exprMVarArgs_591_);
lean_inc(v_nextExprIdx_590_);
lean_inc(v_newLetDecls_589_);
lean_inc(v_newLocalDeclsForMVars_588_);
lean_inc(v_newLocalDecls_587_);
lean_inc(v_levelArgs_586_);
lean_inc(v_nextLevelIdx_585_);
lean_inc(v_levelParams_584_);
lean_inc(v_visitedExpr_583_);
lean_inc(v_visitedLevel_582_);
lean_dec(v___x_581_);
v___x_595_ = lean_box(0);
v_isShared_596_ = v_isSharedCheck_602_;
goto v_resetjp_594_;
}
v_resetjp_594_:
{
lean_object* v___x_597_; lean_object* v___x_599_; 
lean_inc(v_a_580_);
lean_inc(v_a_525_);
v___x_597_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2___redArg(v_visitedLevel_582_, v_a_525_, v_a_580_);
if (v_isShared_596_ == 0)
{
lean_ctor_set(v___x_595_, 0, v___x_597_);
v___x_599_ = v___x_595_;
goto v_reusejp_598_;
}
else
{
lean_object* v_reuseFailAlloc_601_; 
v_reuseFailAlloc_601_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_601_, 0, v___x_597_);
lean_ctor_set(v_reuseFailAlloc_601_, 1, v_visitedExpr_583_);
lean_ctor_set(v_reuseFailAlloc_601_, 2, v_levelParams_584_);
lean_ctor_set(v_reuseFailAlloc_601_, 3, v_nextLevelIdx_585_);
lean_ctor_set(v_reuseFailAlloc_601_, 4, v_levelArgs_586_);
lean_ctor_set(v_reuseFailAlloc_601_, 5, v_newLocalDecls_587_);
lean_ctor_set(v_reuseFailAlloc_601_, 6, v_newLocalDeclsForMVars_588_);
lean_ctor_set(v_reuseFailAlloc_601_, 7, v_newLetDecls_589_);
lean_ctor_set(v_reuseFailAlloc_601_, 8, v_nextExprIdx_590_);
lean_ctor_set(v_reuseFailAlloc_601_, 9, v_exprMVarArgs_591_);
lean_ctor_set(v_reuseFailAlloc_601_, 10, v_exprFVarArgs_592_);
lean_ctor_set(v_reuseFailAlloc_601_, 11, v_toProcess_593_);
v___x_599_ = v_reuseFailAlloc_601_;
goto v_reusejp_598_;
}
v_reusejp_598_:
{
lean_object* v___x_600_; 
v___x_600_ = lean_st_ref_set(v_a_378_, v___x_599_);
v_a_569_ = v_a_580_;
goto v___jp_568_;
}
}
}
else
{
if (lean_obj_tag(v___x_579_) == 0)
{
lean_object* v_a_603_; 
v_a_603_ = lean_ctor_get(v___x_579_, 0);
lean_inc(v_a_603_);
lean_dec_ref_known(v___x_579_, 1);
v_a_569_ = v_a_603_;
goto v___jp_568_;
}
else
{
lean_dec_ref_known(v_x_377_, 2);
return v___x_579_;
}
}
}
else
{
lean_object* v_val_604_; 
v_val_604_ = lean_ctor_get(v___x_578_, 0);
lean_inc(v_val_604_);
lean_dec_ref_known(v___x_578_, 1);
v_a_569_ = v_val_604_;
goto v___jp_568_;
}
}
else
{
lean_inc(v_a_525_);
v_a_569_ = v_a_525_;
goto v___jp_568_;
}
}
}
default: 
{
lean_object* v___x_609_; 
v___x_609_ = l_Lean_Meta_Closure_mkNewLevelParam___redArg(v_x_377_, v_a_378_);
return v___x_609_;
}
}
v___jp_380_:
{
if (v___y_383_ == 0)
{
lean_object* v___x_384_; lean_object* v___x_385_; 
lean_dec(v_x_377_);
v___x_384_ = l_Lean_mkLevelIMax_x27(v___y_382_, v___y_381_);
v___x_385_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_385_, 0, v___x_384_);
return v___x_385_;
}
else
{
lean_object* v___x_386_; lean_object* v___x_387_; 
v___x_386_ = l_Lean_simpLevelIMax_x27(v___y_382_, v___y_381_, v_x_377_);
lean_dec(v_x_377_);
v___x_387_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_387_, 0, v___x_386_);
return v___x_387_;
}
}
v___jp_388_:
{
if (v___y_391_ == 0)
{
lean_object* v___x_392_; lean_object* v___x_393_; 
lean_dec(v_x_377_);
v___x_392_ = l_Lean_mkLevelMax_x27(v___y_390_, v___y_389_);
v___x_393_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_393_, 0, v___x_392_);
return v___x_393_;
}
else
{
lean_object* v___x_394_; lean_object* v___x_395_; 
v___x_394_ = l_Lean_simpLevelMax_x27(v___y_390_, v___y_389_, v_x_377_);
lean_dec(v_x_377_);
lean_dec(v___y_389_);
lean_dec(v___y_390_);
v___x_395_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_395_, 0, v___x_394_);
return v___x_395_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectLevelAux___redArg___boxed(lean_object* v_x_610_, lean_object* v_a_611_, lean_object* v_a_612_){
_start:
{
lean_object* v_res_613_; 
v_res_613_ = l_Lean_Meta_Closure_collectLevelAux___redArg(v_x_610_, v_a_611_);
lean_dec(v_a_611_);
return v_res_613_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectLevelAux(lean_object* v_x_614_, uint8_t v_a_615_, lean_object* v_a_616_, lean_object* v_a_617_, lean_object* v_a_618_, lean_object* v_a_619_, lean_object* v_a_620_){
_start:
{
lean_object* v___x_622_; 
v___x_622_ = l_Lean_Meta_Closure_collectLevelAux___redArg(v_x_614_, v_a_616_);
return v___x_622_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectLevelAux___boxed(lean_object* v_x_623_, lean_object* v_a_624_, lean_object* v_a_625_, lean_object* v_a_626_, lean_object* v_a_627_, lean_object* v_a_628_, lean_object* v_a_629_, lean_object* v_a_630_){
_start:
{
uint8_t v_a_boxed_631_; lean_object* v_res_632_; 
v_a_boxed_631_ = lean_unbox(v_a_624_);
v_res_632_ = l_Lean_Meta_Closure_collectLevelAux(v_x_623_, v_a_boxed_631_, v_a_625_, v_a_626_, v_a_627_, v_a_628_, v_a_629_);
lean_dec(v_a_629_);
lean_dec_ref(v_a_628_);
lean_dec(v_a_627_);
lean_dec_ref(v_a_626_);
lean_dec(v_a_625_);
return v_res_632_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectLevelAux_spec__1(lean_object* v_00_u03b2_633_, lean_object* v_m_634_, lean_object* v_a_635_){
_start:
{
lean_object* v___x_636_; 
v___x_636_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectLevelAux_spec__1___redArg(v_m_634_, v_a_635_);
return v___x_636_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectLevelAux_spec__1___boxed(lean_object* v_00_u03b2_637_, lean_object* v_m_638_, lean_object* v_a_639_){
_start:
{
lean_object* v_res_640_; 
v_res_640_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectLevelAux_spec__1(v_00_u03b2_637_, v_m_638_, v_a_639_);
lean_dec(v_a_639_);
lean_dec_ref(v_m_638_);
return v_res_640_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2(lean_object* v_00_u03b2_641_, lean_object* v_m_642_, lean_object* v_a_643_, lean_object* v_b_644_){
_start:
{
lean_object* v___x_645_; 
v___x_645_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2___redArg(v_m_642_, v_a_643_, v_b_644_);
return v___x_645_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectLevelAux_spec__1_spec__1(lean_object* v_00_u03b2_646_, lean_object* v_a_647_, lean_object* v_x_648_){
_start:
{
lean_object* v___x_649_; 
v___x_649_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectLevelAux_spec__1_spec__1___redArg(v_a_647_, v_x_648_);
return v___x_649_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectLevelAux_spec__1_spec__1___boxed(lean_object* v_00_u03b2_650_, lean_object* v_a_651_, lean_object* v_x_652_){
_start:
{
lean_object* v_res_653_; 
v_res_653_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectLevelAux_spec__1_spec__1(v_00_u03b2_650_, v_a_651_, v_x_652_);
lean_dec(v_x_652_);
lean_dec(v_a_651_);
return v_res_653_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__3(lean_object* v_00_u03b2_654_, lean_object* v_a_655_, lean_object* v_x_656_){
_start:
{
uint8_t v___x_657_; 
v___x_657_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__3___redArg(v_a_655_, v_x_656_);
return v___x_657_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__3___boxed(lean_object* v_00_u03b2_658_, lean_object* v_a_659_, lean_object* v_x_660_){
_start:
{
uint8_t v_res_661_; lean_object* v_r_662_; 
v_res_661_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__3(v_00_u03b2_658_, v_a_659_, v_x_660_);
lean_dec(v_x_660_);
lean_dec(v_a_659_);
v_r_662_ = lean_box(v_res_661_);
return v_r_662_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__4(lean_object* v_00_u03b2_663_, lean_object* v_data_664_){
_start:
{
lean_object* v___x_665_; 
v___x_665_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__4___redArg(v_data_664_);
return v___x_665_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__5(lean_object* v_00_u03b2_666_, lean_object* v_a_667_, lean_object* v_b_668_, lean_object* v_x_669_){
_start:
{
lean_object* v___x_670_; 
v___x_670_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__5___redArg(v_a_667_, v_b_668_, v_x_669_);
return v___x_670_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_671_, lean_object* v_i_672_, lean_object* v_source_673_, lean_object* v_target_674_){
_start:
{
lean_object* v___x_675_; 
v___x_675_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__4_spec__5___redArg(v_i_672_, v_source_673_, v_target_674_);
return v___x_675_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__4_spec__5_spec__6(lean_object* v_00_u03b2_676_, lean_object* v_x_677_, lean_object* v_x_678_){
_start:
{
lean_object* v___x_679_; 
v___x_679_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__4_spec__5_spec__6___redArg(v_x_677_, v_x_678_);
return v___x_679_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectLevel___redArg(lean_object* v_u_680_, lean_object* v_a_681_){
_start:
{
uint8_t v___y_684_; uint8_t v___x_728_; uint8_t v___x_729_; 
v___x_728_ = l_Lean_Level_hasMVar(v_u_680_);
v___x_729_ = lean_bool_not(v___x_728_);
if (v___x_729_ == 0)
{
v___y_684_ = v___x_729_;
goto v___jp_683_;
}
else
{
uint8_t v___x_730_; uint8_t v___x_731_; 
v___x_730_ = l_Lean_Level_hasParam(v_u_680_);
v___x_731_ = lean_bool_not(v___x_730_);
v___y_684_ = v___x_731_;
goto v___jp_683_;
}
v___jp_683_:
{
if (v___y_684_ == 0)
{
lean_object* v___x_685_; lean_object* v_visitedLevel_686_; lean_object* v___x_687_; 
v___x_685_ = lean_st_ref_get(v_a_681_);
v_visitedLevel_686_ = lean_ctor_get(v___x_685_, 0);
lean_inc_ref(v_visitedLevel_686_);
lean_dec(v___x_685_);
v___x_687_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectLevelAux_spec__1___redArg(v_visitedLevel_686_, v_u_680_);
lean_dec_ref(v_visitedLevel_686_);
if (lean_obj_tag(v___x_687_) == 0)
{
lean_object* v___x_688_; 
lean_inc(v_u_680_);
v___x_688_ = l_Lean_Meta_Closure_collectLevelAux___redArg(v_u_680_, v_a_681_);
if (lean_obj_tag(v___x_688_) == 0)
{
lean_object* v_a_689_; lean_object* v___x_691_; uint8_t v_isShared_692_; uint8_t v_isSharedCheck_718_; 
v_a_689_ = lean_ctor_get(v___x_688_, 0);
v_isSharedCheck_718_ = !lean_is_exclusive(v___x_688_);
if (v_isSharedCheck_718_ == 0)
{
v___x_691_ = v___x_688_;
v_isShared_692_ = v_isSharedCheck_718_;
goto v_resetjp_690_;
}
else
{
lean_inc(v_a_689_);
lean_dec(v___x_688_);
v___x_691_ = lean_box(0);
v_isShared_692_ = v_isSharedCheck_718_;
goto v_resetjp_690_;
}
v_resetjp_690_:
{
lean_object* v___x_693_; lean_object* v_visitedLevel_694_; lean_object* v_visitedExpr_695_; lean_object* v_levelParams_696_; lean_object* v_nextLevelIdx_697_; lean_object* v_levelArgs_698_; lean_object* v_newLocalDecls_699_; lean_object* v_newLocalDeclsForMVars_700_; lean_object* v_newLetDecls_701_; lean_object* v_nextExprIdx_702_; lean_object* v_exprMVarArgs_703_; lean_object* v_exprFVarArgs_704_; lean_object* v_toProcess_705_; lean_object* v___x_707_; uint8_t v_isShared_708_; uint8_t v_isSharedCheck_717_; 
v___x_693_ = lean_st_ref_take(v_a_681_);
v_visitedLevel_694_ = lean_ctor_get(v___x_693_, 0);
v_visitedExpr_695_ = lean_ctor_get(v___x_693_, 1);
v_levelParams_696_ = lean_ctor_get(v___x_693_, 2);
v_nextLevelIdx_697_ = lean_ctor_get(v___x_693_, 3);
v_levelArgs_698_ = lean_ctor_get(v___x_693_, 4);
v_newLocalDecls_699_ = lean_ctor_get(v___x_693_, 5);
v_newLocalDeclsForMVars_700_ = lean_ctor_get(v___x_693_, 6);
v_newLetDecls_701_ = lean_ctor_get(v___x_693_, 7);
v_nextExprIdx_702_ = lean_ctor_get(v___x_693_, 8);
v_exprMVarArgs_703_ = lean_ctor_get(v___x_693_, 9);
v_exprFVarArgs_704_ = lean_ctor_get(v___x_693_, 10);
v_toProcess_705_ = lean_ctor_get(v___x_693_, 11);
v_isSharedCheck_717_ = !lean_is_exclusive(v___x_693_);
if (v_isSharedCheck_717_ == 0)
{
v___x_707_ = v___x_693_;
v_isShared_708_ = v_isSharedCheck_717_;
goto v_resetjp_706_;
}
else
{
lean_inc(v_toProcess_705_);
lean_inc(v_exprFVarArgs_704_);
lean_inc(v_exprMVarArgs_703_);
lean_inc(v_nextExprIdx_702_);
lean_inc(v_newLetDecls_701_);
lean_inc(v_newLocalDeclsForMVars_700_);
lean_inc(v_newLocalDecls_699_);
lean_inc(v_levelArgs_698_);
lean_inc(v_nextLevelIdx_697_);
lean_inc(v_levelParams_696_);
lean_inc(v_visitedExpr_695_);
lean_inc(v_visitedLevel_694_);
lean_dec(v___x_693_);
v___x_707_ = lean_box(0);
v_isShared_708_ = v_isSharedCheck_717_;
goto v_resetjp_706_;
}
v_resetjp_706_:
{
lean_object* v___x_709_; lean_object* v___x_711_; 
lean_inc(v_a_689_);
v___x_709_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2___redArg(v_visitedLevel_694_, v_u_680_, v_a_689_);
if (v_isShared_708_ == 0)
{
lean_ctor_set(v___x_707_, 0, v___x_709_);
v___x_711_ = v___x_707_;
goto v_reusejp_710_;
}
else
{
lean_object* v_reuseFailAlloc_716_; 
v_reuseFailAlloc_716_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_716_, 0, v___x_709_);
lean_ctor_set(v_reuseFailAlloc_716_, 1, v_visitedExpr_695_);
lean_ctor_set(v_reuseFailAlloc_716_, 2, v_levelParams_696_);
lean_ctor_set(v_reuseFailAlloc_716_, 3, v_nextLevelIdx_697_);
lean_ctor_set(v_reuseFailAlloc_716_, 4, v_levelArgs_698_);
lean_ctor_set(v_reuseFailAlloc_716_, 5, v_newLocalDecls_699_);
lean_ctor_set(v_reuseFailAlloc_716_, 6, v_newLocalDeclsForMVars_700_);
lean_ctor_set(v_reuseFailAlloc_716_, 7, v_newLetDecls_701_);
lean_ctor_set(v_reuseFailAlloc_716_, 8, v_nextExprIdx_702_);
lean_ctor_set(v_reuseFailAlloc_716_, 9, v_exprMVarArgs_703_);
lean_ctor_set(v_reuseFailAlloc_716_, 10, v_exprFVarArgs_704_);
lean_ctor_set(v_reuseFailAlloc_716_, 11, v_toProcess_705_);
v___x_711_ = v_reuseFailAlloc_716_;
goto v_reusejp_710_;
}
v_reusejp_710_:
{
lean_object* v___x_712_; lean_object* v___x_714_; 
v___x_712_ = lean_st_ref_set(v_a_681_, v___x_711_);
if (v_isShared_692_ == 0)
{
v___x_714_ = v___x_691_;
goto v_reusejp_713_;
}
else
{
lean_object* v_reuseFailAlloc_715_; 
v_reuseFailAlloc_715_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_715_, 0, v_a_689_);
v___x_714_ = v_reuseFailAlloc_715_;
goto v_reusejp_713_;
}
v_reusejp_713_:
{
return v___x_714_;
}
}
}
}
}
else
{
lean_dec(v_u_680_);
return v___x_688_;
}
}
else
{
lean_object* v_val_719_; lean_object* v___x_721_; uint8_t v_isShared_722_; uint8_t v_isSharedCheck_726_; 
lean_dec(v_u_680_);
v_val_719_ = lean_ctor_get(v___x_687_, 0);
v_isSharedCheck_726_ = !lean_is_exclusive(v___x_687_);
if (v_isSharedCheck_726_ == 0)
{
v___x_721_ = v___x_687_;
v_isShared_722_ = v_isSharedCheck_726_;
goto v_resetjp_720_;
}
else
{
lean_inc(v_val_719_);
lean_dec(v___x_687_);
v___x_721_ = lean_box(0);
v_isShared_722_ = v_isSharedCheck_726_;
goto v_resetjp_720_;
}
v_resetjp_720_:
{
lean_object* v___x_724_; 
if (v_isShared_722_ == 0)
{
lean_ctor_set_tag(v___x_721_, 0);
v___x_724_ = v___x_721_;
goto v_reusejp_723_;
}
else
{
lean_object* v_reuseFailAlloc_725_; 
v_reuseFailAlloc_725_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_725_, 0, v_val_719_);
v___x_724_ = v_reuseFailAlloc_725_;
goto v_reusejp_723_;
}
v_reusejp_723_:
{
return v___x_724_;
}
}
}
}
else
{
lean_object* v___x_727_; 
v___x_727_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_727_, 0, v_u_680_);
return v___x_727_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectLevel___redArg___boxed(lean_object* v_u_732_, lean_object* v_a_733_, lean_object* v_a_734_){
_start:
{
lean_object* v_res_735_; 
v_res_735_ = l_Lean_Meta_Closure_collectLevel___redArg(v_u_732_, v_a_733_);
lean_dec(v_a_733_);
return v_res_735_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectLevel(lean_object* v_u_736_, uint8_t v_a_737_, lean_object* v_a_738_, lean_object* v_a_739_, lean_object* v_a_740_, lean_object* v_a_741_, lean_object* v_a_742_){
_start:
{
lean_object* v___x_744_; 
v___x_744_ = l_Lean_Meta_Closure_collectLevel___redArg(v_u_736_, v_a_738_);
return v___x_744_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectLevel___boxed(lean_object* v_u_745_, lean_object* v_a_746_, lean_object* v_a_747_, lean_object* v_a_748_, lean_object* v_a_749_, lean_object* v_a_750_, lean_object* v_a_751_, lean_object* v_a_752_){
_start:
{
uint8_t v_a_boxed_753_; lean_object* v_res_754_; 
v_a_boxed_753_ = lean_unbox(v_a_746_);
v_res_754_ = l_Lean_Meta_Closure_collectLevel(v_u_745_, v_a_boxed_753_, v_a_747_, v_a_748_, v_a_749_, v_a_750_, v_a_751_);
lean_dec(v_a_751_);
lean_dec_ref(v_a_750_);
lean_dec(v_a_749_);
lean_dec_ref(v_a_748_);
lean_dec(v_a_747_);
return v_res_754_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Closure_preprocess_spec__0___redArg(lean_object* v_e_755_, lean_object* v___y_756_){
_start:
{
uint8_t v___x_758_; uint8_t v___x_759_; 
v___x_758_ = l_Lean_Expr_hasMVar(v_e_755_);
v___x_759_ = lean_bool_not(v___x_758_);
if (v___x_759_ == 0)
{
lean_object* v___x_760_; lean_object* v_mctx_761_; lean_object* v___x_762_; lean_object* v_fst_763_; lean_object* v_snd_764_; lean_object* v___x_765_; lean_object* v_cache_766_; lean_object* v_zetaDeltaFVarIds_767_; lean_object* v_postponed_768_; lean_object* v_diag_769_; lean_object* v___x_771_; uint8_t v_isShared_772_; uint8_t v_isSharedCheck_778_; 
v___x_760_ = lean_st_ref_get(v___y_756_);
v_mctx_761_ = lean_ctor_get(v___x_760_, 0);
lean_inc_ref(v_mctx_761_);
lean_dec(v___x_760_);
v___x_762_ = l_Lean_instantiateMVarsCore(v_mctx_761_, v_e_755_);
v_fst_763_ = lean_ctor_get(v___x_762_, 0);
lean_inc(v_fst_763_);
v_snd_764_ = lean_ctor_get(v___x_762_, 1);
lean_inc(v_snd_764_);
lean_dec_ref(v___x_762_);
v___x_765_ = lean_st_ref_take(v___y_756_);
v_cache_766_ = lean_ctor_get(v___x_765_, 1);
v_zetaDeltaFVarIds_767_ = lean_ctor_get(v___x_765_, 2);
v_postponed_768_ = lean_ctor_get(v___x_765_, 3);
v_diag_769_ = lean_ctor_get(v___x_765_, 4);
v_isSharedCheck_778_ = !lean_is_exclusive(v___x_765_);
if (v_isSharedCheck_778_ == 0)
{
lean_object* v_unused_779_; 
v_unused_779_ = lean_ctor_get(v___x_765_, 0);
lean_dec(v_unused_779_);
v___x_771_ = v___x_765_;
v_isShared_772_ = v_isSharedCheck_778_;
goto v_resetjp_770_;
}
else
{
lean_inc(v_diag_769_);
lean_inc(v_postponed_768_);
lean_inc(v_zetaDeltaFVarIds_767_);
lean_inc(v_cache_766_);
lean_dec(v___x_765_);
v___x_771_ = lean_box(0);
v_isShared_772_ = v_isSharedCheck_778_;
goto v_resetjp_770_;
}
v_resetjp_770_:
{
lean_object* v___x_774_; 
if (v_isShared_772_ == 0)
{
lean_ctor_set(v___x_771_, 0, v_snd_764_);
v___x_774_ = v___x_771_;
goto v_reusejp_773_;
}
else
{
lean_object* v_reuseFailAlloc_777_; 
v_reuseFailAlloc_777_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_777_, 0, v_snd_764_);
lean_ctor_set(v_reuseFailAlloc_777_, 1, v_cache_766_);
lean_ctor_set(v_reuseFailAlloc_777_, 2, v_zetaDeltaFVarIds_767_);
lean_ctor_set(v_reuseFailAlloc_777_, 3, v_postponed_768_);
lean_ctor_set(v_reuseFailAlloc_777_, 4, v_diag_769_);
v___x_774_ = v_reuseFailAlloc_777_;
goto v_reusejp_773_;
}
v_reusejp_773_:
{
lean_object* v___x_775_; lean_object* v___x_776_; 
v___x_775_ = lean_st_ref_set(v___y_756_, v___x_774_);
v___x_776_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_776_, 0, v_fst_763_);
return v___x_776_;
}
}
}
else
{
lean_object* v___x_780_; 
v___x_780_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_780_, 0, v_e_755_);
return v___x_780_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Closure_preprocess_spec__0___redArg___boxed(lean_object* v_e_781_, lean_object* v___y_782_, lean_object* v___y_783_){
_start:
{
lean_object* v_res_784_; 
v_res_784_ = l_Lean_instantiateMVars___at___00Lean_Meta_Closure_preprocess_spec__0___redArg(v_e_781_, v___y_782_);
lean_dec(v___y_782_);
return v_res_784_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Closure_preprocess_spec__0(lean_object* v_e_785_, uint8_t v___y_786_, lean_object* v___y_787_, lean_object* v___y_788_, lean_object* v___y_789_, lean_object* v___y_790_, lean_object* v___y_791_){
_start:
{
lean_object* v___x_793_; 
v___x_793_ = l_Lean_instantiateMVars___at___00Lean_Meta_Closure_preprocess_spec__0___redArg(v_e_785_, v___y_789_);
return v___x_793_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Closure_preprocess_spec__0___boxed(lean_object* v_e_794_, lean_object* v___y_795_, lean_object* v___y_796_, lean_object* v___y_797_, lean_object* v___y_798_, lean_object* v___y_799_, lean_object* v___y_800_, lean_object* v___y_801_){
_start:
{
uint8_t v___y_2205__boxed_802_; lean_object* v_res_803_; 
v___y_2205__boxed_802_ = lean_unbox(v___y_795_);
v_res_803_ = l_Lean_instantiateMVars___at___00Lean_Meta_Closure_preprocess_spec__0(v_e_794_, v___y_2205__boxed_802_, v___y_796_, v___y_797_, v___y_798_, v___y_799_, v___y_800_);
lean_dec(v___y_800_);
lean_dec_ref(v___y_799_);
lean_dec(v___y_798_);
lean_dec_ref(v___y_797_);
lean_dec(v___y_796_);
return v_res_803_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_preprocess(lean_object* v_e_804_, uint8_t v_a_805_, lean_object* v_a_806_, lean_object* v_a_807_, lean_object* v_a_808_, lean_object* v_a_809_, lean_object* v_a_810_){
_start:
{
lean_object* v___x_812_; lean_object* v_a_813_; uint8_t v___x_814_; 
v___x_812_ = l_Lean_instantiateMVars___at___00Lean_Meta_Closure_preprocess_spec__0___redArg(v_e_804_, v_a_808_);
v_a_813_ = lean_ctor_get(v___x_812_, 0);
lean_inc(v_a_813_);
v___x_814_ = lean_bool_not(v_a_805_);
if (v___x_814_ == 0)
{
lean_dec(v_a_813_);
return v___x_812_;
}
else
{
uint8_t v___x_815_; lean_object* v___x_816_; 
lean_dec_ref(v___x_812_);
v___x_815_ = 0;
lean_inc(v_a_813_);
v___x_816_ = l_Lean_Meta_check(v_a_813_, v___x_815_, v_a_807_, v_a_808_, v_a_809_, v_a_810_);
if (lean_obj_tag(v___x_816_) == 0)
{
lean_object* v___x_818_; uint8_t v_isShared_819_; uint8_t v_isSharedCheck_823_; 
v_isSharedCheck_823_ = !lean_is_exclusive(v___x_816_);
if (v_isSharedCheck_823_ == 0)
{
lean_object* v_unused_824_; 
v_unused_824_ = lean_ctor_get(v___x_816_, 0);
lean_dec(v_unused_824_);
v___x_818_ = v___x_816_;
v_isShared_819_ = v_isSharedCheck_823_;
goto v_resetjp_817_;
}
else
{
lean_dec(v___x_816_);
v___x_818_ = lean_box(0);
v_isShared_819_ = v_isSharedCheck_823_;
goto v_resetjp_817_;
}
v_resetjp_817_:
{
lean_object* v___x_821_; 
if (v_isShared_819_ == 0)
{
lean_ctor_set(v___x_818_, 0, v_a_813_);
v___x_821_ = v___x_818_;
goto v_reusejp_820_;
}
else
{
lean_object* v_reuseFailAlloc_822_; 
v_reuseFailAlloc_822_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_822_, 0, v_a_813_);
v___x_821_ = v_reuseFailAlloc_822_;
goto v_reusejp_820_;
}
v_reusejp_820_:
{
return v___x_821_;
}
}
}
else
{
lean_object* v_a_825_; lean_object* v___x_827_; uint8_t v_isShared_828_; uint8_t v_isSharedCheck_832_; 
lean_dec(v_a_813_);
v_a_825_ = lean_ctor_get(v___x_816_, 0);
v_isSharedCheck_832_ = !lean_is_exclusive(v___x_816_);
if (v_isSharedCheck_832_ == 0)
{
v___x_827_ = v___x_816_;
v_isShared_828_ = v_isSharedCheck_832_;
goto v_resetjp_826_;
}
else
{
lean_inc(v_a_825_);
lean_dec(v___x_816_);
v___x_827_ = lean_box(0);
v_isShared_828_ = v_isSharedCheck_832_;
goto v_resetjp_826_;
}
v_resetjp_826_:
{
lean_object* v___x_830_; 
if (v_isShared_828_ == 0)
{
v___x_830_ = v___x_827_;
goto v_reusejp_829_;
}
else
{
lean_object* v_reuseFailAlloc_831_; 
v_reuseFailAlloc_831_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_831_, 0, v_a_825_);
v___x_830_ = v_reuseFailAlloc_831_;
goto v_reusejp_829_;
}
v_reusejp_829_:
{
return v___x_830_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_preprocess___boxed(lean_object* v_e_833_, lean_object* v_a_834_, lean_object* v_a_835_, lean_object* v_a_836_, lean_object* v_a_837_, lean_object* v_a_838_, lean_object* v_a_839_, lean_object* v_a_840_){
_start:
{
uint8_t v_a_boxed_841_; lean_object* v_res_842_; 
v_a_boxed_841_ = lean_unbox(v_a_834_);
v_res_842_ = l_Lean_Meta_Closure_preprocess(v_e_833_, v_a_boxed_841_, v_a_835_, v_a_836_, v_a_837_, v_a_838_, v_a_839_);
lean_dec(v_a_839_);
lean_dec_ref(v_a_838_);
lean_dec(v_a_837_);
lean_dec_ref(v_a_836_);
lean_dec(v_a_835_);
return v_res_842_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkNextUserName___redArg(lean_object* v_a_846_){
_start:
{
lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v_visitedLevel_850_; lean_object* v_visitedExpr_851_; lean_object* v_levelParams_852_; lean_object* v_nextLevelIdx_853_; lean_object* v_levelArgs_854_; lean_object* v_newLocalDecls_855_; lean_object* v_newLocalDeclsForMVars_856_; lean_object* v_newLetDecls_857_; lean_object* v_nextExprIdx_858_; lean_object* v_exprMVarArgs_859_; lean_object* v_exprFVarArgs_860_; lean_object* v_toProcess_861_; lean_object* v___x_863_; uint8_t v_isShared_864_; uint8_t v_isSharedCheck_875_; 
v___x_848_ = lean_st_ref_get(v_a_846_);
v___x_849_ = lean_st_ref_take(v_a_846_);
v_visitedLevel_850_ = lean_ctor_get(v___x_849_, 0);
v_visitedExpr_851_ = lean_ctor_get(v___x_849_, 1);
v_levelParams_852_ = lean_ctor_get(v___x_849_, 2);
v_nextLevelIdx_853_ = lean_ctor_get(v___x_849_, 3);
v_levelArgs_854_ = lean_ctor_get(v___x_849_, 4);
v_newLocalDecls_855_ = lean_ctor_get(v___x_849_, 5);
v_newLocalDeclsForMVars_856_ = lean_ctor_get(v___x_849_, 6);
v_newLetDecls_857_ = lean_ctor_get(v___x_849_, 7);
v_nextExprIdx_858_ = lean_ctor_get(v___x_849_, 8);
v_exprMVarArgs_859_ = lean_ctor_get(v___x_849_, 9);
v_exprFVarArgs_860_ = lean_ctor_get(v___x_849_, 10);
v_toProcess_861_ = lean_ctor_get(v___x_849_, 11);
v_isSharedCheck_875_ = !lean_is_exclusive(v___x_849_);
if (v_isSharedCheck_875_ == 0)
{
v___x_863_ = v___x_849_;
v_isShared_864_ = v_isSharedCheck_875_;
goto v_resetjp_862_;
}
else
{
lean_inc(v_toProcess_861_);
lean_inc(v_exprFVarArgs_860_);
lean_inc(v_exprMVarArgs_859_);
lean_inc(v_nextExprIdx_858_);
lean_inc(v_newLetDecls_857_);
lean_inc(v_newLocalDeclsForMVars_856_);
lean_inc(v_newLocalDecls_855_);
lean_inc(v_levelArgs_854_);
lean_inc(v_nextLevelIdx_853_);
lean_inc(v_levelParams_852_);
lean_inc(v_visitedExpr_851_);
lean_inc(v_visitedLevel_850_);
lean_dec(v___x_849_);
v___x_863_ = lean_box(0);
v_isShared_864_ = v_isSharedCheck_875_;
goto v_resetjp_862_;
}
v_resetjp_862_:
{
lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_868_; 
v___x_865_ = lean_unsigned_to_nat(1u);
v___x_866_ = lean_nat_add(v_nextExprIdx_858_, v___x_865_);
lean_dec(v_nextExprIdx_858_);
if (v_isShared_864_ == 0)
{
lean_ctor_set(v___x_863_, 8, v___x_866_);
v___x_868_ = v___x_863_;
goto v_reusejp_867_;
}
else
{
lean_object* v_reuseFailAlloc_874_; 
v_reuseFailAlloc_874_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_874_, 0, v_visitedLevel_850_);
lean_ctor_set(v_reuseFailAlloc_874_, 1, v_visitedExpr_851_);
lean_ctor_set(v_reuseFailAlloc_874_, 2, v_levelParams_852_);
lean_ctor_set(v_reuseFailAlloc_874_, 3, v_nextLevelIdx_853_);
lean_ctor_set(v_reuseFailAlloc_874_, 4, v_levelArgs_854_);
lean_ctor_set(v_reuseFailAlloc_874_, 5, v_newLocalDecls_855_);
lean_ctor_set(v_reuseFailAlloc_874_, 6, v_newLocalDeclsForMVars_856_);
lean_ctor_set(v_reuseFailAlloc_874_, 7, v_newLetDecls_857_);
lean_ctor_set(v_reuseFailAlloc_874_, 8, v___x_866_);
lean_ctor_set(v_reuseFailAlloc_874_, 9, v_exprMVarArgs_859_);
lean_ctor_set(v_reuseFailAlloc_874_, 10, v_exprFVarArgs_860_);
lean_ctor_set(v_reuseFailAlloc_874_, 11, v_toProcess_861_);
v___x_868_ = v_reuseFailAlloc_874_;
goto v_reusejp_867_;
}
v_reusejp_867_:
{
lean_object* v___x_869_; lean_object* v_nextExprIdx_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; 
v___x_869_ = lean_st_ref_set(v_a_846_, v___x_868_);
v_nextExprIdx_870_ = lean_ctor_get(v___x_848_, 8);
lean_inc(v_nextExprIdx_870_);
lean_dec(v___x_848_);
v___x_871_ = ((lean_object*)(l_Lean_Meta_Closure_mkNextUserName___redArg___closed__1));
v___x_872_ = lean_name_append_index_after(v___x_871_, v_nextExprIdx_870_);
v___x_873_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_873_, 0, v___x_872_);
return v___x_873_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkNextUserName___redArg___boxed(lean_object* v_a_876_, lean_object* v_a_877_){
_start:
{
lean_object* v_res_878_; 
v_res_878_ = l_Lean_Meta_Closure_mkNextUserName___redArg(v_a_876_);
lean_dec(v_a_876_);
return v_res_878_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkNextUserName(uint8_t v_a_879_, lean_object* v_a_880_, lean_object* v_a_881_, lean_object* v_a_882_, lean_object* v_a_883_, lean_object* v_a_884_){
_start:
{
lean_object* v___x_886_; 
v___x_886_ = l_Lean_Meta_Closure_mkNextUserName___redArg(v_a_880_);
return v___x_886_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkNextUserName___boxed(lean_object* v_a_887_, lean_object* v_a_888_, lean_object* v_a_889_, lean_object* v_a_890_, lean_object* v_a_891_, lean_object* v_a_892_, lean_object* v_a_893_){
_start:
{
uint8_t v_a_boxed_894_; lean_object* v_res_895_; 
v_a_boxed_894_ = lean_unbox(v_a_887_);
v_res_895_ = l_Lean_Meta_Closure_mkNextUserName(v_a_boxed_894_, v_a_888_, v_a_889_, v_a_890_, v_a_891_, v_a_892_);
lean_dec(v_a_892_);
lean_dec_ref(v_a_891_);
lean_dec(v_a_890_);
lean_dec_ref(v_a_889_);
lean_dec(v_a_888_);
return v_res_895_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushToProcess___redArg(lean_object* v_elem_896_, lean_object* v_a_897_){
_start:
{
lean_object* v___x_899_; lean_object* v_visitedLevel_900_; lean_object* v_visitedExpr_901_; lean_object* v_levelParams_902_; lean_object* v_nextLevelIdx_903_; lean_object* v_levelArgs_904_; lean_object* v_newLocalDecls_905_; lean_object* v_newLocalDeclsForMVars_906_; lean_object* v_newLetDecls_907_; lean_object* v_nextExprIdx_908_; lean_object* v_exprMVarArgs_909_; lean_object* v_exprFVarArgs_910_; lean_object* v_toProcess_911_; lean_object* v___x_913_; uint8_t v_isShared_914_; uint8_t v_isSharedCheck_922_; 
v___x_899_ = lean_st_ref_take(v_a_897_);
v_visitedLevel_900_ = lean_ctor_get(v___x_899_, 0);
v_visitedExpr_901_ = lean_ctor_get(v___x_899_, 1);
v_levelParams_902_ = lean_ctor_get(v___x_899_, 2);
v_nextLevelIdx_903_ = lean_ctor_get(v___x_899_, 3);
v_levelArgs_904_ = lean_ctor_get(v___x_899_, 4);
v_newLocalDecls_905_ = lean_ctor_get(v___x_899_, 5);
v_newLocalDeclsForMVars_906_ = lean_ctor_get(v___x_899_, 6);
v_newLetDecls_907_ = lean_ctor_get(v___x_899_, 7);
v_nextExprIdx_908_ = lean_ctor_get(v___x_899_, 8);
v_exprMVarArgs_909_ = lean_ctor_get(v___x_899_, 9);
v_exprFVarArgs_910_ = lean_ctor_get(v___x_899_, 10);
v_toProcess_911_ = lean_ctor_get(v___x_899_, 11);
v_isSharedCheck_922_ = !lean_is_exclusive(v___x_899_);
if (v_isSharedCheck_922_ == 0)
{
v___x_913_ = v___x_899_;
v_isShared_914_ = v_isSharedCheck_922_;
goto v_resetjp_912_;
}
else
{
lean_inc(v_toProcess_911_);
lean_inc(v_exprFVarArgs_910_);
lean_inc(v_exprMVarArgs_909_);
lean_inc(v_nextExprIdx_908_);
lean_inc(v_newLetDecls_907_);
lean_inc(v_newLocalDeclsForMVars_906_);
lean_inc(v_newLocalDecls_905_);
lean_inc(v_levelArgs_904_);
lean_inc(v_nextLevelIdx_903_);
lean_inc(v_levelParams_902_);
lean_inc(v_visitedExpr_901_);
lean_inc(v_visitedLevel_900_);
lean_dec(v___x_899_);
v___x_913_ = lean_box(0);
v_isShared_914_ = v_isSharedCheck_922_;
goto v_resetjp_912_;
}
v_resetjp_912_:
{
lean_object* v___x_915_; lean_object* v___x_917_; 
v___x_915_ = lean_array_push(v_toProcess_911_, v_elem_896_);
if (v_isShared_914_ == 0)
{
lean_ctor_set(v___x_913_, 11, v___x_915_);
v___x_917_ = v___x_913_;
goto v_reusejp_916_;
}
else
{
lean_object* v_reuseFailAlloc_921_; 
v_reuseFailAlloc_921_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_921_, 0, v_visitedLevel_900_);
lean_ctor_set(v_reuseFailAlloc_921_, 1, v_visitedExpr_901_);
lean_ctor_set(v_reuseFailAlloc_921_, 2, v_levelParams_902_);
lean_ctor_set(v_reuseFailAlloc_921_, 3, v_nextLevelIdx_903_);
lean_ctor_set(v_reuseFailAlloc_921_, 4, v_levelArgs_904_);
lean_ctor_set(v_reuseFailAlloc_921_, 5, v_newLocalDecls_905_);
lean_ctor_set(v_reuseFailAlloc_921_, 6, v_newLocalDeclsForMVars_906_);
lean_ctor_set(v_reuseFailAlloc_921_, 7, v_newLetDecls_907_);
lean_ctor_set(v_reuseFailAlloc_921_, 8, v_nextExprIdx_908_);
lean_ctor_set(v_reuseFailAlloc_921_, 9, v_exprMVarArgs_909_);
lean_ctor_set(v_reuseFailAlloc_921_, 10, v_exprFVarArgs_910_);
lean_ctor_set(v_reuseFailAlloc_921_, 11, v___x_915_);
v___x_917_ = v_reuseFailAlloc_921_;
goto v_reusejp_916_;
}
v_reusejp_916_:
{
lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; 
v___x_918_ = lean_st_ref_set(v_a_897_, v___x_917_);
v___x_919_ = lean_box(0);
v___x_920_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_920_, 0, v___x_919_);
return v___x_920_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushToProcess___redArg___boxed(lean_object* v_elem_923_, lean_object* v_a_924_, lean_object* v_a_925_){
_start:
{
lean_object* v_res_926_; 
v_res_926_ = l_Lean_Meta_Closure_pushToProcess___redArg(v_elem_923_, v_a_924_);
lean_dec(v_a_924_);
return v_res_926_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushToProcess(lean_object* v_elem_927_, uint8_t v_a_928_, lean_object* v_a_929_, lean_object* v_a_930_, lean_object* v_a_931_, lean_object* v_a_932_, lean_object* v_a_933_){
_start:
{
lean_object* v___x_935_; 
v___x_935_ = l_Lean_Meta_Closure_pushToProcess___redArg(v_elem_927_, v_a_929_);
return v___x_935_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushToProcess___boxed(lean_object* v_elem_936_, lean_object* v_a_937_, lean_object* v_a_938_, lean_object* v_a_939_, lean_object* v_a_940_, lean_object* v_a_941_, lean_object* v_a_942_, lean_object* v_a_943_){
_start:
{
uint8_t v_a_boxed_944_; lean_object* v_res_945_; 
v_a_boxed_944_ = lean_unbox(v_a_937_);
v_res_945_ = l_Lean_Meta_Closure_pushToProcess(v_elem_936_, v_a_boxed_944_, v_a_938_, v_a_939_, v_a_940_, v_a_941_, v_a_942_);
lean_dec(v_a_942_);
lean_dec_ref(v_a_941_);
lean_dec(v_a_940_);
lean_dec_ref(v_a_939_);
lean_dec(v_a_938_);
return v_res_945_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__4___redArg(lean_object* v_mvarId_946_, lean_object* v___y_947_){
_start:
{
lean_object* v___x_949_; lean_object* v_mctx_950_; lean_object* v___x_951_; lean_object* v___x_952_; 
v___x_949_ = lean_st_ref_get(v___y_947_);
v_mctx_950_ = lean_ctor_get(v___x_949_, 0);
lean_inc_ref(v_mctx_950_);
lean_dec(v___x_949_);
v___x_951_ = l_Lean_MetavarContext_getDelayedMVarAssignmentCore_x3f(v_mctx_950_, v_mvarId_946_);
lean_dec_ref(v_mctx_950_);
v___x_952_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_952_, 0, v___x_951_);
return v___x_952_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__4___redArg___boxed(lean_object* v_mvarId_953_, lean_object* v___y_954_, lean_object* v___y_955_){
_start:
{
lean_object* v_res_956_; 
v_res_956_ = l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__4___redArg(v_mvarId_953_, v___y_954_);
lean_dec(v___y_954_);
lean_dec(v_mvarId_953_);
return v_res_956_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__4(lean_object* v_mvarId_957_, uint8_t v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v___y_961_, lean_object* v___y_962_, lean_object* v___y_963_){
_start:
{
lean_object* v___x_965_; 
v___x_965_ = l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__4___redArg(v_mvarId_957_, v___y_961_);
return v___x_965_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__4___boxed(lean_object* v_mvarId_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_){
_start:
{
uint8_t v___y_17881__boxed_974_; lean_object* v_res_975_; 
v___y_17881__boxed_974_ = lean_unbox(v___y_967_);
v_res_975_ = l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__4(v_mvarId_966_, v___y_17881__boxed_974_, v___y_968_, v___y_969_, v___y_970_, v___y_971_, v___y_972_);
lean_dec(v___y_972_);
lean_dec_ref(v___y_971_);
lean_dec(v___y_970_);
lean_dec_ref(v___y_969_);
lean_dec(v___y_968_);
lean_dec(v_mvarId_966_);
return v_res_975_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Closure_collectExprAux_spec__5___redArg___lam__0(lean_object* v_k_976_, uint8_t v___y_977_, lean_object* v___y_978_, lean_object* v_b_979_, lean_object* v_c_980_, lean_object* v___y_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_){
_start:
{
lean_object* v___x_986_; lean_object* v___x_987_; 
v___x_986_ = lean_box(v___y_977_);
lean_inc(v___y_984_);
lean_inc_ref(v___y_983_);
lean_inc(v___y_982_);
lean_inc_ref(v___y_981_);
lean_inc(v___y_978_);
v___x_987_ = lean_apply_9(v_k_976_, v_b_979_, v_c_980_, v___x_986_, v___y_978_, v___y_981_, v___y_982_, v___y_983_, v___y_984_, lean_box(0));
return v___x_987_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Closure_collectExprAux_spec__5___redArg___lam__0___boxed(lean_object* v_k_988_, lean_object* v___y_989_, lean_object* v___y_990_, lean_object* v_b_991_, lean_object* v_c_992_, lean_object* v___y_993_, lean_object* v___y_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_){
_start:
{
uint8_t v___y_17904__boxed_998_; lean_object* v_res_999_; 
v___y_17904__boxed_998_ = lean_unbox(v___y_989_);
v_res_999_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Closure_collectExprAux_spec__5___redArg___lam__0(v_k_988_, v___y_17904__boxed_998_, v___y_990_, v_b_991_, v_c_992_, v___y_993_, v___y_994_, v___y_995_, v___y_996_);
lean_dec(v___y_996_);
lean_dec_ref(v___y_995_);
lean_dec(v___y_994_);
lean_dec_ref(v___y_993_);
lean_dec(v___y_990_);
return v_res_999_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Closure_collectExprAux_spec__5___redArg(lean_object* v_type_1000_, lean_object* v_maxFVars_x3f_1001_, lean_object* v_k_1002_, uint8_t v_cleanupAnnotations_1003_, uint8_t v_whnfType_1004_, uint8_t v___y_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_){
_start:
{
lean_object* v___x_1012_; lean_object* v___f_1013_; lean_object* v___x_1014_; 
v___x_1012_ = lean_box(v___y_1005_);
lean_inc(v___y_1006_);
v___f_1013_ = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Closure_collectExprAux_spec__5___redArg___lam__0___boxed), 10, 3);
lean_closure_set(v___f_1013_, 0, v_k_1002_);
lean_closure_set(v___f_1013_, 1, v___x_1012_);
lean_closure_set(v___f_1013_, 2, v___y_1006_);
v___x_1014_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_1000_, v_maxFVars_x3f_1001_, v___f_1013_, v_cleanupAnnotations_1003_, v_whnfType_1004_, v___y_1007_, v___y_1008_, v___y_1009_, v___y_1010_);
if (lean_obj_tag(v___x_1014_) == 0)
{
return v___x_1014_;
}
else
{
lean_object* v_a_1015_; lean_object* v___x_1017_; uint8_t v_isShared_1018_; uint8_t v_isSharedCheck_1022_; 
v_a_1015_ = lean_ctor_get(v___x_1014_, 0);
v_isSharedCheck_1022_ = !lean_is_exclusive(v___x_1014_);
if (v_isSharedCheck_1022_ == 0)
{
v___x_1017_ = v___x_1014_;
v_isShared_1018_ = v_isSharedCheck_1022_;
goto v_resetjp_1016_;
}
else
{
lean_inc(v_a_1015_);
lean_dec(v___x_1014_);
v___x_1017_ = lean_box(0);
v_isShared_1018_ = v_isSharedCheck_1022_;
goto v_resetjp_1016_;
}
v_resetjp_1016_:
{
lean_object* v___x_1020_; 
if (v_isShared_1018_ == 0)
{
v___x_1020_ = v___x_1017_;
goto v_reusejp_1019_;
}
else
{
lean_object* v_reuseFailAlloc_1021_; 
v_reuseFailAlloc_1021_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1021_, 0, v_a_1015_);
v___x_1020_ = v_reuseFailAlloc_1021_;
goto v_reusejp_1019_;
}
v_reusejp_1019_:
{
return v___x_1020_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Closure_collectExprAux_spec__5___redArg___boxed(lean_object* v_type_1023_, lean_object* v_maxFVars_x3f_1024_, lean_object* v_k_1025_, lean_object* v_cleanupAnnotations_1026_, lean_object* v_whnfType_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1035_; uint8_t v_whnfType_boxed_1036_; uint8_t v___y_17929__boxed_1037_; lean_object* v_res_1038_; 
v_cleanupAnnotations_boxed_1035_ = lean_unbox(v_cleanupAnnotations_1026_);
v_whnfType_boxed_1036_ = lean_unbox(v_whnfType_1027_);
v___y_17929__boxed_1037_ = lean_unbox(v___y_1028_);
v_res_1038_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Closure_collectExprAux_spec__5___redArg(v_type_1023_, v_maxFVars_x3f_1024_, v_k_1025_, v_cleanupAnnotations_boxed_1035_, v_whnfType_boxed_1036_, v___y_17929__boxed_1037_, v___y_1029_, v___y_1030_, v___y_1031_, v___y_1032_, v___y_1033_);
lean_dec(v___y_1033_);
lean_dec_ref(v___y_1032_);
lean_dec(v___y_1031_);
lean_dec_ref(v___y_1030_);
lean_dec(v___y_1029_);
return v_res_1038_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Closure_collectExprAux_spec__5(lean_object* v_00_u03b1_1039_, lean_object* v_type_1040_, lean_object* v_maxFVars_x3f_1041_, lean_object* v_k_1042_, uint8_t v_cleanupAnnotations_1043_, uint8_t v_whnfType_1044_, uint8_t v___y_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_){
_start:
{
lean_object* v___x_1052_; 
v___x_1052_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Closure_collectExprAux_spec__5___redArg(v_type_1040_, v_maxFVars_x3f_1041_, v_k_1042_, v_cleanupAnnotations_1043_, v_whnfType_1044_, v___y_1045_, v___y_1046_, v___y_1047_, v___y_1048_, v___y_1049_, v___y_1050_);
return v___x_1052_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Closure_collectExprAux_spec__5___boxed(lean_object* v_00_u03b1_1053_, lean_object* v_type_1054_, lean_object* v_maxFVars_x3f_1055_, lean_object* v_k_1056_, lean_object* v_cleanupAnnotations_1057_, lean_object* v_whnfType_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1066_; uint8_t v_whnfType_boxed_1067_; uint8_t v___y_17973__boxed_1068_; lean_object* v_res_1069_; 
v_cleanupAnnotations_boxed_1066_ = lean_unbox(v_cleanupAnnotations_1057_);
v_whnfType_boxed_1067_ = lean_unbox(v_whnfType_1058_);
v___y_17973__boxed_1068_ = lean_unbox(v___y_1059_);
v_res_1069_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Closure_collectExprAux_spec__5(v_00_u03b1_1053_, v_type_1054_, v_maxFVars_x3f_1055_, v_k_1056_, v_cleanupAnnotations_boxed_1066_, v_whnfType_boxed_1067_, v___y_17973__boxed_1068_, v___y_1060_, v___y_1061_, v___y_1062_, v___y_1063_, v___y_1064_);
lean_dec(v___y_1064_);
lean_dec_ref(v___y_1063_);
lean_dec(v___y_1062_);
lean_dec_ref(v___y_1061_);
lean_dec(v___y_1060_);
return v_res_1069_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0_spec__0___redArg(lean_object* v_a_1070_, lean_object* v_x_1071_){
_start:
{
if (lean_obj_tag(v_x_1071_) == 0)
{
lean_object* v___x_1072_; 
v___x_1072_ = lean_box(0);
return v___x_1072_;
}
else
{
lean_object* v_key_1073_; lean_object* v_value_1074_; lean_object* v_tail_1075_; uint8_t v___x_1076_; 
v_key_1073_ = lean_ctor_get(v_x_1071_, 0);
v_value_1074_ = lean_ctor_get(v_x_1071_, 1);
v_tail_1075_ = lean_ctor_get(v_x_1071_, 2);
v___x_1076_ = l_Lean_ExprStructEq_beq(v_key_1073_, v_a_1070_);
if (v___x_1076_ == 0)
{
v_x_1071_ = v_tail_1075_;
goto _start;
}
else
{
lean_object* v___x_1078_; 
lean_inc(v_value_1074_);
v___x_1078_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1078_, 0, v_value_1074_);
return v___x_1078_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0_spec__0___redArg___boxed(lean_object* v_a_1079_, lean_object* v_x_1080_){
_start:
{
lean_object* v_res_1081_; 
v_res_1081_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0_spec__0___redArg(v_a_1079_, v_x_1080_);
lean_dec(v_x_1080_);
lean_dec_ref(v_a_1079_);
return v_res_1081_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0___redArg(lean_object* v_m_1082_, lean_object* v_a_1083_){
_start:
{
lean_object* v_buckets_1084_; lean_object* v___x_1085_; uint64_t v___x_1086_; uint64_t v___x_1087_; uint64_t v___x_1088_; uint64_t v_fold_1089_; uint64_t v___x_1090_; uint64_t v___x_1091_; uint64_t v___x_1092_; size_t v___x_1093_; size_t v___x_1094_; size_t v___x_1095_; size_t v___x_1096_; size_t v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; 
v_buckets_1084_ = lean_ctor_get(v_m_1082_, 1);
v___x_1085_ = lean_array_get_size(v_buckets_1084_);
v___x_1086_ = l_Lean_ExprStructEq_hash(v_a_1083_);
v___x_1087_ = 32ULL;
v___x_1088_ = lean_uint64_shift_right(v___x_1086_, v___x_1087_);
v_fold_1089_ = lean_uint64_xor(v___x_1086_, v___x_1088_);
v___x_1090_ = 16ULL;
v___x_1091_ = lean_uint64_shift_right(v_fold_1089_, v___x_1090_);
v___x_1092_ = lean_uint64_xor(v_fold_1089_, v___x_1091_);
v___x_1093_ = lean_uint64_to_usize(v___x_1092_);
v___x_1094_ = lean_usize_of_nat(v___x_1085_);
v___x_1095_ = ((size_t)1ULL);
v___x_1096_ = lean_usize_sub(v___x_1094_, v___x_1095_);
v___x_1097_ = lean_usize_land(v___x_1093_, v___x_1096_);
v___x_1098_ = lean_array_uget_borrowed(v_buckets_1084_, v___x_1097_);
v___x_1099_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0_spec__0___redArg(v_a_1083_, v___x_1098_);
return v___x_1099_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0___redArg___boxed(lean_object* v_m_1100_, lean_object* v_a_1101_){
_start:
{
lean_object* v_res_1102_; 
v_res_1102_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0___redArg(v_m_1100_, v_a_1101_);
lean_dec_ref(v_a_1101_);
lean_dec_ref(v_m_1100_);
return v_res_1102_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Closure_collectExprAux_spec__2___redArg(lean_object* v_x_1103_, lean_object* v_x_1104_, lean_object* v___y_1105_){
_start:
{
if (lean_obj_tag(v_x_1103_) == 0)
{
lean_object* v___x_1107_; lean_object* v___x_1108_; 
v___x_1107_ = l_List_reverse___redArg(v_x_1104_);
v___x_1108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1108_, 0, v___x_1107_);
return v___x_1108_;
}
else
{
lean_object* v_head_1109_; lean_object* v_tail_1110_; lean_object* v___x_1112_; uint8_t v_isShared_1113_; uint8_t v_isSharedCheck_1128_; 
v_head_1109_ = lean_ctor_get(v_x_1103_, 0);
v_tail_1110_ = lean_ctor_get(v_x_1103_, 1);
v_isSharedCheck_1128_ = !lean_is_exclusive(v_x_1103_);
if (v_isSharedCheck_1128_ == 0)
{
v___x_1112_ = v_x_1103_;
v_isShared_1113_ = v_isSharedCheck_1128_;
goto v_resetjp_1111_;
}
else
{
lean_inc(v_tail_1110_);
lean_inc(v_head_1109_);
lean_dec(v_x_1103_);
v___x_1112_ = lean_box(0);
v_isShared_1113_ = v_isSharedCheck_1128_;
goto v_resetjp_1111_;
}
v_resetjp_1111_:
{
lean_object* v___x_1114_; 
v___x_1114_ = l_Lean_Meta_Closure_collectLevel___redArg(v_head_1109_, v___y_1105_);
if (lean_obj_tag(v___x_1114_) == 0)
{
lean_object* v_a_1115_; lean_object* v___x_1117_; 
v_a_1115_ = lean_ctor_get(v___x_1114_, 0);
lean_inc(v_a_1115_);
lean_dec_ref_known(v___x_1114_, 1);
if (v_isShared_1113_ == 0)
{
lean_ctor_set(v___x_1112_, 1, v_x_1104_);
lean_ctor_set(v___x_1112_, 0, v_a_1115_);
v___x_1117_ = v___x_1112_;
goto v_reusejp_1116_;
}
else
{
lean_object* v_reuseFailAlloc_1119_; 
v_reuseFailAlloc_1119_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1119_, 0, v_a_1115_);
lean_ctor_set(v_reuseFailAlloc_1119_, 1, v_x_1104_);
v___x_1117_ = v_reuseFailAlloc_1119_;
goto v_reusejp_1116_;
}
v_reusejp_1116_:
{
v_x_1103_ = v_tail_1110_;
v_x_1104_ = v___x_1117_;
goto _start;
}
}
else
{
lean_object* v_a_1120_; lean_object* v___x_1122_; uint8_t v_isShared_1123_; uint8_t v_isSharedCheck_1127_; 
lean_del_object(v___x_1112_);
lean_dec(v_tail_1110_);
lean_dec(v_x_1104_);
v_a_1120_ = lean_ctor_get(v___x_1114_, 0);
v_isSharedCheck_1127_ = !lean_is_exclusive(v___x_1114_);
if (v_isSharedCheck_1127_ == 0)
{
v___x_1122_ = v___x_1114_;
v_isShared_1123_ = v_isSharedCheck_1127_;
goto v_resetjp_1121_;
}
else
{
lean_inc(v_a_1120_);
lean_dec(v___x_1114_);
v___x_1122_ = lean_box(0);
v_isShared_1123_ = v_isSharedCheck_1127_;
goto v_resetjp_1121_;
}
v_resetjp_1121_:
{
lean_object* v___x_1125_; 
if (v_isShared_1123_ == 0)
{
v___x_1125_ = v___x_1122_;
goto v_reusejp_1124_;
}
else
{
lean_object* v_reuseFailAlloc_1126_; 
v_reuseFailAlloc_1126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1126_, 0, v_a_1120_);
v___x_1125_ = v_reuseFailAlloc_1126_;
goto v_reusejp_1124_;
}
v_reusejp_1124_:
{
return v___x_1125_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Closure_collectExprAux_spec__2___redArg___boxed(lean_object* v_x_1129_, lean_object* v_x_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_){
_start:
{
lean_object* v_res_1133_; 
v_res_1133_ = l_List_mapM_loop___at___00Lean_Meta_Closure_collectExprAux_spec__2___redArg(v_x_1129_, v_x_1130_, v___y_1131_);
lean_dec(v___y_1131_);
return v_res_1133_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Closure_collectExprAux_spec__3_spec__7___redArg(lean_object* v___y_1134_){
_start:
{
lean_object* v___x_1136_; lean_object* v_ngen_1137_; lean_object* v_namePrefix_1138_; lean_object* v_idx_1139_; lean_object* v___x_1141_; uint8_t v_isShared_1142_; uint8_t v_isSharedCheck_1168_; 
v___x_1136_ = lean_st_ref_get(v___y_1134_);
v_ngen_1137_ = lean_ctor_get(v___x_1136_, 2);
lean_inc_ref(v_ngen_1137_);
lean_dec(v___x_1136_);
v_namePrefix_1138_ = lean_ctor_get(v_ngen_1137_, 0);
v_idx_1139_ = lean_ctor_get(v_ngen_1137_, 1);
v_isSharedCheck_1168_ = !lean_is_exclusive(v_ngen_1137_);
if (v_isSharedCheck_1168_ == 0)
{
v___x_1141_ = v_ngen_1137_;
v_isShared_1142_ = v_isSharedCheck_1168_;
goto v_resetjp_1140_;
}
else
{
lean_inc(v_idx_1139_);
lean_inc(v_namePrefix_1138_);
lean_dec(v_ngen_1137_);
v___x_1141_ = lean_box(0);
v_isShared_1142_ = v_isSharedCheck_1168_;
goto v_resetjp_1140_;
}
v_resetjp_1140_:
{
lean_object* v___x_1143_; lean_object* v_env_1144_; lean_object* v_nextMacroScope_1145_; lean_object* v_auxDeclNGen_1146_; lean_object* v_traceState_1147_; lean_object* v_cache_1148_; lean_object* v_messages_1149_; lean_object* v_infoState_1150_; lean_object* v_snapshotTasks_1151_; lean_object* v___x_1153_; uint8_t v_isShared_1154_; uint8_t v_isSharedCheck_1166_; 
v___x_1143_ = lean_st_ref_take(v___y_1134_);
v_env_1144_ = lean_ctor_get(v___x_1143_, 0);
v_nextMacroScope_1145_ = lean_ctor_get(v___x_1143_, 1);
v_auxDeclNGen_1146_ = lean_ctor_get(v___x_1143_, 3);
v_traceState_1147_ = lean_ctor_get(v___x_1143_, 4);
v_cache_1148_ = lean_ctor_get(v___x_1143_, 5);
v_messages_1149_ = lean_ctor_get(v___x_1143_, 6);
v_infoState_1150_ = lean_ctor_get(v___x_1143_, 7);
v_snapshotTasks_1151_ = lean_ctor_get(v___x_1143_, 8);
v_isSharedCheck_1166_ = !lean_is_exclusive(v___x_1143_);
if (v_isSharedCheck_1166_ == 0)
{
lean_object* v_unused_1167_; 
v_unused_1167_ = lean_ctor_get(v___x_1143_, 2);
lean_dec(v_unused_1167_);
v___x_1153_ = v___x_1143_;
v_isShared_1154_ = v_isSharedCheck_1166_;
goto v_resetjp_1152_;
}
else
{
lean_inc(v_snapshotTasks_1151_);
lean_inc(v_infoState_1150_);
lean_inc(v_messages_1149_);
lean_inc(v_cache_1148_);
lean_inc(v_traceState_1147_);
lean_inc(v_auxDeclNGen_1146_);
lean_inc(v_nextMacroScope_1145_);
lean_inc(v_env_1144_);
lean_dec(v___x_1143_);
v___x_1153_ = lean_box(0);
v_isShared_1154_ = v_isSharedCheck_1166_;
goto v_resetjp_1152_;
}
v_resetjp_1152_:
{
lean_object* v_r_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1159_; 
lean_inc(v_idx_1139_);
lean_inc(v_namePrefix_1138_);
v_r_1155_ = l_Lean_Name_num___override(v_namePrefix_1138_, v_idx_1139_);
v___x_1156_ = lean_unsigned_to_nat(1u);
v___x_1157_ = lean_nat_add(v_idx_1139_, v___x_1156_);
lean_dec(v_idx_1139_);
if (v_isShared_1142_ == 0)
{
lean_ctor_set(v___x_1141_, 1, v___x_1157_);
v___x_1159_ = v___x_1141_;
goto v_reusejp_1158_;
}
else
{
lean_object* v_reuseFailAlloc_1165_; 
v_reuseFailAlloc_1165_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1165_, 0, v_namePrefix_1138_);
lean_ctor_set(v_reuseFailAlloc_1165_, 1, v___x_1157_);
v___x_1159_ = v_reuseFailAlloc_1165_;
goto v_reusejp_1158_;
}
v_reusejp_1158_:
{
lean_object* v___x_1161_; 
if (v_isShared_1154_ == 0)
{
lean_ctor_set(v___x_1153_, 2, v___x_1159_);
v___x_1161_ = v___x_1153_;
goto v_reusejp_1160_;
}
else
{
lean_object* v_reuseFailAlloc_1164_; 
v_reuseFailAlloc_1164_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1164_, 0, v_env_1144_);
lean_ctor_set(v_reuseFailAlloc_1164_, 1, v_nextMacroScope_1145_);
lean_ctor_set(v_reuseFailAlloc_1164_, 2, v___x_1159_);
lean_ctor_set(v_reuseFailAlloc_1164_, 3, v_auxDeclNGen_1146_);
lean_ctor_set(v_reuseFailAlloc_1164_, 4, v_traceState_1147_);
lean_ctor_set(v_reuseFailAlloc_1164_, 5, v_cache_1148_);
lean_ctor_set(v_reuseFailAlloc_1164_, 6, v_messages_1149_);
lean_ctor_set(v_reuseFailAlloc_1164_, 7, v_infoState_1150_);
lean_ctor_set(v_reuseFailAlloc_1164_, 8, v_snapshotTasks_1151_);
v___x_1161_ = v_reuseFailAlloc_1164_;
goto v_reusejp_1160_;
}
v_reusejp_1160_:
{
lean_object* v___x_1162_; lean_object* v___x_1163_; 
v___x_1162_ = lean_st_ref_set(v___y_1134_, v___x_1161_);
v___x_1163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1163_, 0, v_r_1155_);
return v___x_1163_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Closure_collectExprAux_spec__3_spec__7___redArg___boxed(lean_object* v___y_1169_, lean_object* v___y_1170_){
_start:
{
lean_object* v_res_1171_; 
v_res_1171_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Closure_collectExprAux_spec__3_spec__7___redArg(v___y_1169_);
lean_dec(v___y_1169_);
return v_res_1171_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00Lean_Meta_Closure_collectExprAux_spec__3(uint8_t v___y_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_){
_start:
{
lean_object* v___x_1179_; lean_object* v_a_1180_; lean_object* v___x_1182_; uint8_t v_isShared_1183_; uint8_t v_isSharedCheck_1187_; 
v___x_1179_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Closure_collectExprAux_spec__3_spec__7___redArg(v___y_1177_);
v_a_1180_ = lean_ctor_get(v___x_1179_, 0);
v_isSharedCheck_1187_ = !lean_is_exclusive(v___x_1179_);
if (v_isSharedCheck_1187_ == 0)
{
v___x_1182_ = v___x_1179_;
v_isShared_1183_ = v_isSharedCheck_1187_;
goto v_resetjp_1181_;
}
else
{
lean_inc(v_a_1180_);
lean_dec(v___x_1179_);
v___x_1182_ = lean_box(0);
v_isShared_1183_ = v_isSharedCheck_1187_;
goto v_resetjp_1181_;
}
v_resetjp_1181_:
{
lean_object* v___x_1185_; 
if (v_isShared_1183_ == 0)
{
v___x_1185_ = v___x_1182_;
goto v_reusejp_1184_;
}
else
{
lean_object* v_reuseFailAlloc_1186_; 
v_reuseFailAlloc_1186_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1186_, 0, v_a_1180_);
v___x_1185_ = v_reuseFailAlloc_1186_;
goto v_reusejp_1184_;
}
v_reusejp_1184_:
{
return v___x_1185_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00Lean_Meta_Closure_collectExprAux_spec__3___boxed(lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_){
_start:
{
uint8_t v___y_18148__boxed_1195_; lean_object* v_res_1196_; 
v___y_18148__boxed_1195_ = lean_unbox(v___y_1188_);
v_res_1196_ = l_Lean_mkFreshFVarId___at___00Lean_Meta_Closure_collectExprAux_spec__3(v___y_18148__boxed_1195_, v___y_1189_, v___y_1190_, v___y_1191_, v___y_1192_, v___y_1193_);
lean_dec(v___y_1193_);
lean_dec_ref(v___y_1192_);
lean_dec(v___y_1191_);
lean_dec_ref(v___y_1190_);
lean_dec(v___y_1189_);
return v_res_1196_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectExprAux___lam__1(lean_object* v_e_1197_, lean_object* v_args_1198_, lean_object* v_x_1199_, uint8_t v___y_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_){
_start:
{
lean_object* v___x_1207_; uint8_t v___x_1208_; uint8_t v___x_1209_; uint8_t v___x_1210_; lean_object* v___x_1211_; 
v___x_1207_ = l_Lean_mkAppN(v_e_1197_, v_args_1198_);
v___x_1208_ = 0;
v___x_1209_ = 1;
v___x_1210_ = 1;
v___x_1211_ = l_Lean_Meta_mkLambdaFVars(v_args_1198_, v___x_1207_, v___x_1208_, v___x_1209_, v___x_1208_, v___x_1209_, v___x_1210_, v___y_1202_, v___y_1203_, v___y_1204_, v___y_1205_);
return v___x_1211_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectExprAux___lam__1___boxed(lean_object* v_e_1212_, lean_object* v_args_1213_, lean_object* v_x_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_){
_start:
{
uint8_t v___y_18189__boxed_1222_; lean_object* v_res_1223_; 
v___y_18189__boxed_1222_ = lean_unbox(v___y_1215_);
v_res_1223_ = l_Lean_Meta_Closure_collectExprAux___lam__1(v_e_1212_, v_args_1213_, v_x_1214_, v___y_18189__boxed_1222_, v___y_1216_, v___y_1217_, v___y_1218_, v___y_1219_, v___y_1220_);
lean_dec(v___y_1220_);
lean_dec_ref(v___y_1219_);
lean_dec(v___y_1218_);
lean_dec_ref(v___y_1217_);
lean_dec(v___y_1216_);
lean_dec_ref(v_x_1214_);
lean_dec_ref(v_args_1213_);
return v_res_1223_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__3_spec__6_spec__10___redArg(lean_object* v_x_1224_, lean_object* v_x_1225_){
_start:
{
if (lean_obj_tag(v_x_1225_) == 0)
{
return v_x_1224_;
}
else
{
lean_object* v_key_1226_; lean_object* v_value_1227_; lean_object* v_tail_1228_; lean_object* v___x_1230_; uint8_t v_isShared_1231_; uint8_t v_isSharedCheck_1251_; 
v_key_1226_ = lean_ctor_get(v_x_1225_, 0);
v_value_1227_ = lean_ctor_get(v_x_1225_, 1);
v_tail_1228_ = lean_ctor_get(v_x_1225_, 2);
v_isSharedCheck_1251_ = !lean_is_exclusive(v_x_1225_);
if (v_isSharedCheck_1251_ == 0)
{
v___x_1230_ = v_x_1225_;
v_isShared_1231_ = v_isSharedCheck_1251_;
goto v_resetjp_1229_;
}
else
{
lean_inc(v_tail_1228_);
lean_inc(v_value_1227_);
lean_inc(v_key_1226_);
lean_dec(v_x_1225_);
v___x_1230_ = lean_box(0);
v_isShared_1231_ = v_isSharedCheck_1251_;
goto v_resetjp_1229_;
}
v_resetjp_1229_:
{
lean_object* v___x_1232_; uint64_t v___x_1233_; uint64_t v___x_1234_; uint64_t v___x_1235_; uint64_t v_fold_1236_; uint64_t v___x_1237_; uint64_t v___x_1238_; uint64_t v___x_1239_; size_t v___x_1240_; size_t v___x_1241_; size_t v___x_1242_; size_t v___x_1243_; size_t v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1247_; 
v___x_1232_ = lean_array_get_size(v_x_1224_);
v___x_1233_ = l_Lean_ExprStructEq_hash(v_key_1226_);
v___x_1234_ = 32ULL;
v___x_1235_ = lean_uint64_shift_right(v___x_1233_, v___x_1234_);
v_fold_1236_ = lean_uint64_xor(v___x_1233_, v___x_1235_);
v___x_1237_ = 16ULL;
v___x_1238_ = lean_uint64_shift_right(v_fold_1236_, v___x_1237_);
v___x_1239_ = lean_uint64_xor(v_fold_1236_, v___x_1238_);
v___x_1240_ = lean_uint64_to_usize(v___x_1239_);
v___x_1241_ = lean_usize_of_nat(v___x_1232_);
v___x_1242_ = ((size_t)1ULL);
v___x_1243_ = lean_usize_sub(v___x_1241_, v___x_1242_);
v___x_1244_ = lean_usize_land(v___x_1240_, v___x_1243_);
v___x_1245_ = lean_array_uget_borrowed(v_x_1224_, v___x_1244_);
lean_inc(v___x_1245_);
if (v_isShared_1231_ == 0)
{
lean_ctor_set(v___x_1230_, 2, v___x_1245_);
v___x_1247_ = v___x_1230_;
goto v_reusejp_1246_;
}
else
{
lean_object* v_reuseFailAlloc_1250_; 
v_reuseFailAlloc_1250_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1250_, 0, v_key_1226_);
lean_ctor_set(v_reuseFailAlloc_1250_, 1, v_value_1227_);
lean_ctor_set(v_reuseFailAlloc_1250_, 2, v___x_1245_);
v___x_1247_ = v_reuseFailAlloc_1250_;
goto v_reusejp_1246_;
}
v_reusejp_1246_:
{
lean_object* v___x_1248_; 
v___x_1248_ = lean_array_uset(v_x_1224_, v___x_1244_, v___x_1247_);
v_x_1224_ = v___x_1248_;
v_x_1225_ = v_tail_1228_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__3_spec__6___redArg(lean_object* v_i_1252_, lean_object* v_source_1253_, lean_object* v_target_1254_){
_start:
{
lean_object* v___x_1255_; uint8_t v___x_1256_; 
v___x_1255_ = lean_array_get_size(v_source_1253_);
v___x_1256_ = lean_nat_dec_lt(v_i_1252_, v___x_1255_);
if (v___x_1256_ == 0)
{
lean_dec_ref(v_source_1253_);
lean_dec(v_i_1252_);
return v_target_1254_;
}
else
{
lean_object* v_es_1257_; lean_object* v___x_1258_; lean_object* v_source_1259_; lean_object* v_target_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; 
v_es_1257_ = lean_array_fget(v_source_1253_, v_i_1252_);
v___x_1258_ = lean_box(0);
v_source_1259_ = lean_array_fset(v_source_1253_, v_i_1252_, v___x_1258_);
v_target_1260_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__3_spec__6_spec__10___redArg(v_target_1254_, v_es_1257_);
v___x_1261_ = lean_unsigned_to_nat(1u);
v___x_1262_ = lean_nat_add(v_i_1252_, v___x_1261_);
lean_dec(v_i_1252_);
v_i_1252_ = v___x_1262_;
v_source_1253_ = v_source_1259_;
v_target_1254_ = v_target_1260_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__3___redArg(lean_object* v_data_1264_){
_start:
{
lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v_nbuckets_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; 
v___x_1265_ = lean_array_get_size(v_data_1264_);
v___x_1266_ = lean_unsigned_to_nat(2u);
v_nbuckets_1267_ = lean_nat_mul(v___x_1265_, v___x_1266_);
v___x_1268_ = lean_unsigned_to_nat(0u);
v___x_1269_ = lean_box(0);
v___x_1270_ = lean_mk_array(v_nbuckets_1267_, v___x_1269_);
v___x_1271_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__3_spec__6___redArg(v___x_1268_, v_data_1264_, v___x_1270_);
return v___x_1271_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__4___redArg(lean_object* v_a_1272_, lean_object* v_b_1273_, lean_object* v_x_1274_){
_start:
{
if (lean_obj_tag(v_x_1274_) == 0)
{
lean_dec(v_b_1273_);
lean_dec_ref(v_a_1272_);
return v_x_1274_;
}
else
{
lean_object* v_key_1275_; lean_object* v_value_1276_; lean_object* v_tail_1277_; lean_object* v___x_1279_; uint8_t v_isShared_1280_; uint8_t v_isSharedCheck_1289_; 
v_key_1275_ = lean_ctor_get(v_x_1274_, 0);
v_value_1276_ = lean_ctor_get(v_x_1274_, 1);
v_tail_1277_ = lean_ctor_get(v_x_1274_, 2);
v_isSharedCheck_1289_ = !lean_is_exclusive(v_x_1274_);
if (v_isSharedCheck_1289_ == 0)
{
v___x_1279_ = v_x_1274_;
v_isShared_1280_ = v_isSharedCheck_1289_;
goto v_resetjp_1278_;
}
else
{
lean_inc(v_tail_1277_);
lean_inc(v_value_1276_);
lean_inc(v_key_1275_);
lean_dec(v_x_1274_);
v___x_1279_ = lean_box(0);
v_isShared_1280_ = v_isSharedCheck_1289_;
goto v_resetjp_1278_;
}
v_resetjp_1278_:
{
uint8_t v___x_1281_; 
v___x_1281_ = l_Lean_ExprStructEq_beq(v_key_1275_, v_a_1272_);
if (v___x_1281_ == 0)
{
lean_object* v___x_1282_; lean_object* v___x_1284_; 
v___x_1282_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__4___redArg(v_a_1272_, v_b_1273_, v_tail_1277_);
if (v_isShared_1280_ == 0)
{
lean_ctor_set(v___x_1279_, 2, v___x_1282_);
v___x_1284_ = v___x_1279_;
goto v_reusejp_1283_;
}
else
{
lean_object* v_reuseFailAlloc_1285_; 
v_reuseFailAlloc_1285_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1285_, 0, v_key_1275_);
lean_ctor_set(v_reuseFailAlloc_1285_, 1, v_value_1276_);
lean_ctor_set(v_reuseFailAlloc_1285_, 2, v___x_1282_);
v___x_1284_ = v_reuseFailAlloc_1285_;
goto v_reusejp_1283_;
}
v_reusejp_1283_:
{
return v___x_1284_;
}
}
else
{
lean_object* v___x_1287_; 
lean_dec(v_value_1276_);
lean_dec(v_key_1275_);
if (v_isShared_1280_ == 0)
{
lean_ctor_set(v___x_1279_, 1, v_b_1273_);
lean_ctor_set(v___x_1279_, 0, v_a_1272_);
v___x_1287_ = v___x_1279_;
goto v_reusejp_1286_;
}
else
{
lean_object* v_reuseFailAlloc_1288_; 
v_reuseFailAlloc_1288_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1288_, 0, v_a_1272_);
lean_ctor_set(v_reuseFailAlloc_1288_, 1, v_b_1273_);
lean_ctor_set(v_reuseFailAlloc_1288_, 2, v_tail_1277_);
v___x_1287_ = v_reuseFailAlloc_1288_;
goto v_reusejp_1286_;
}
v_reusejp_1286_:
{
return v___x_1287_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__2___redArg(lean_object* v_a_1290_, lean_object* v_x_1291_){
_start:
{
if (lean_obj_tag(v_x_1291_) == 0)
{
uint8_t v___x_1292_; 
v___x_1292_ = 0;
return v___x_1292_;
}
else
{
lean_object* v_key_1293_; lean_object* v_tail_1294_; uint8_t v___x_1295_; 
v_key_1293_ = lean_ctor_get(v_x_1291_, 0);
v_tail_1294_ = lean_ctor_get(v_x_1291_, 2);
v___x_1295_ = l_Lean_ExprStructEq_beq(v_key_1293_, v_a_1290_);
if (v___x_1295_ == 0)
{
v_x_1291_ = v_tail_1294_;
goto _start;
}
else
{
return v___x_1295_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__2___redArg___boxed(lean_object* v_a_1297_, lean_object* v_x_1298_){
_start:
{
uint8_t v_res_1299_; lean_object* v_r_1300_; 
v_res_1299_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__2___redArg(v_a_1297_, v_x_1298_);
lean_dec(v_x_1298_);
lean_dec_ref(v_a_1297_);
v_r_1300_ = lean_box(v_res_1299_);
return v_r_1300_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1___redArg(lean_object* v_m_1301_, lean_object* v_a_1302_, lean_object* v_b_1303_){
_start:
{
lean_object* v_size_1304_; lean_object* v_buckets_1305_; lean_object* v___x_1307_; uint8_t v_isShared_1308_; uint8_t v_isSharedCheck_1348_; 
v_size_1304_ = lean_ctor_get(v_m_1301_, 0);
v_buckets_1305_ = lean_ctor_get(v_m_1301_, 1);
v_isSharedCheck_1348_ = !lean_is_exclusive(v_m_1301_);
if (v_isSharedCheck_1348_ == 0)
{
v___x_1307_ = v_m_1301_;
v_isShared_1308_ = v_isSharedCheck_1348_;
goto v_resetjp_1306_;
}
else
{
lean_inc(v_buckets_1305_);
lean_inc(v_size_1304_);
lean_dec(v_m_1301_);
v___x_1307_ = lean_box(0);
v_isShared_1308_ = v_isSharedCheck_1348_;
goto v_resetjp_1306_;
}
v_resetjp_1306_:
{
lean_object* v___x_1309_; uint64_t v___x_1310_; uint64_t v___x_1311_; uint64_t v___x_1312_; uint64_t v_fold_1313_; uint64_t v___x_1314_; uint64_t v___x_1315_; uint64_t v___x_1316_; size_t v___x_1317_; size_t v___x_1318_; size_t v___x_1319_; size_t v___x_1320_; size_t v___x_1321_; lean_object* v_bkt_1322_; uint8_t v___x_1323_; 
v___x_1309_ = lean_array_get_size(v_buckets_1305_);
v___x_1310_ = l_Lean_ExprStructEq_hash(v_a_1302_);
v___x_1311_ = 32ULL;
v___x_1312_ = lean_uint64_shift_right(v___x_1310_, v___x_1311_);
v_fold_1313_ = lean_uint64_xor(v___x_1310_, v___x_1312_);
v___x_1314_ = 16ULL;
v___x_1315_ = lean_uint64_shift_right(v_fold_1313_, v___x_1314_);
v___x_1316_ = lean_uint64_xor(v_fold_1313_, v___x_1315_);
v___x_1317_ = lean_uint64_to_usize(v___x_1316_);
v___x_1318_ = lean_usize_of_nat(v___x_1309_);
v___x_1319_ = ((size_t)1ULL);
v___x_1320_ = lean_usize_sub(v___x_1318_, v___x_1319_);
v___x_1321_ = lean_usize_land(v___x_1317_, v___x_1320_);
v_bkt_1322_ = lean_array_uget_borrowed(v_buckets_1305_, v___x_1321_);
v___x_1323_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__2___redArg(v_a_1302_, v_bkt_1322_);
if (v___x_1323_ == 0)
{
lean_object* v___x_1324_; lean_object* v_size_x27_1325_; lean_object* v___x_1326_; lean_object* v_buckets_x27_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; uint8_t v___x_1333_; 
v___x_1324_ = lean_unsigned_to_nat(1u);
v_size_x27_1325_ = lean_nat_add(v_size_1304_, v___x_1324_);
lean_dec(v_size_1304_);
lean_inc(v_bkt_1322_);
v___x_1326_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1326_, 0, v_a_1302_);
lean_ctor_set(v___x_1326_, 1, v_b_1303_);
lean_ctor_set(v___x_1326_, 2, v_bkt_1322_);
v_buckets_x27_1327_ = lean_array_uset(v_buckets_1305_, v___x_1321_, v___x_1326_);
v___x_1328_ = lean_unsigned_to_nat(4u);
v___x_1329_ = lean_nat_mul(v_size_x27_1325_, v___x_1328_);
v___x_1330_ = lean_unsigned_to_nat(3u);
v___x_1331_ = lean_nat_div(v___x_1329_, v___x_1330_);
lean_dec(v___x_1329_);
v___x_1332_ = lean_array_get_size(v_buckets_x27_1327_);
v___x_1333_ = lean_nat_dec_le(v___x_1331_, v___x_1332_);
lean_dec(v___x_1331_);
if (v___x_1333_ == 0)
{
lean_object* v_val_1334_; lean_object* v___x_1336_; 
v_val_1334_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__3___redArg(v_buckets_x27_1327_);
if (v_isShared_1308_ == 0)
{
lean_ctor_set(v___x_1307_, 1, v_val_1334_);
lean_ctor_set(v___x_1307_, 0, v_size_x27_1325_);
v___x_1336_ = v___x_1307_;
goto v_reusejp_1335_;
}
else
{
lean_object* v_reuseFailAlloc_1337_; 
v_reuseFailAlloc_1337_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1337_, 0, v_size_x27_1325_);
lean_ctor_set(v_reuseFailAlloc_1337_, 1, v_val_1334_);
v___x_1336_ = v_reuseFailAlloc_1337_;
goto v_reusejp_1335_;
}
v_reusejp_1335_:
{
return v___x_1336_;
}
}
else
{
lean_object* v___x_1339_; 
if (v_isShared_1308_ == 0)
{
lean_ctor_set(v___x_1307_, 1, v_buckets_x27_1327_);
lean_ctor_set(v___x_1307_, 0, v_size_x27_1325_);
v___x_1339_ = v___x_1307_;
goto v_reusejp_1338_;
}
else
{
lean_object* v_reuseFailAlloc_1340_; 
v_reuseFailAlloc_1340_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1340_, 0, v_size_x27_1325_);
lean_ctor_set(v_reuseFailAlloc_1340_, 1, v_buckets_x27_1327_);
v___x_1339_ = v_reuseFailAlloc_1340_;
goto v_reusejp_1338_;
}
v_reusejp_1338_:
{
return v___x_1339_;
}
}
}
else
{
lean_object* v___x_1341_; lean_object* v_buckets_x27_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1346_; 
lean_inc(v_bkt_1322_);
v___x_1341_ = lean_box(0);
v_buckets_x27_1342_ = lean_array_uset(v_buckets_1305_, v___x_1321_, v___x_1341_);
v___x_1343_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__4___redArg(v_a_1302_, v_b_1303_, v_bkt_1322_);
v___x_1344_ = lean_array_uset(v_buckets_x27_1342_, v___x_1321_, v___x_1343_);
if (v_isShared_1308_ == 0)
{
lean_ctor_set(v___x_1307_, 1, v___x_1344_);
v___x_1346_ = v___x_1307_;
goto v_reusejp_1345_;
}
else
{
lean_object* v_reuseFailAlloc_1347_; 
v_reuseFailAlloc_1347_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1347_, 0, v_size_1304_);
lean_ctor_set(v_reuseFailAlloc_1347_, 1, v___x_1344_);
v___x_1346_ = v_reuseFailAlloc_1347_;
goto v_reusejp_1345_;
}
v_reusejp_1345_:
{
return v___x_1346_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectExprAux(lean_object* v_e_1349_, uint8_t v_a_1350_, lean_object* v_a_1351_, lean_object* v_a_1352_, lean_object* v_a_1353_, lean_object* v_a_1354_, lean_object* v_a_1355_){
_start:
{
switch(lean_obj_tag(v_e_1349_))
{
case 11:
{
lean_object* v_typeName_1357_; lean_object* v_idx_1358_; lean_object* v_struct_1359_; lean_object* v___x_1360_; 
v_typeName_1357_ = lean_ctor_get(v_e_1349_, 0);
v_idx_1358_ = lean_ctor_get(v_e_1349_, 1);
v_struct_1359_ = lean_ctor_get(v_e_1349_, 2);
lean_inc_ref(v_struct_1359_);
v___x_1360_ = l_Lean_Meta_Closure_collectExprAux___lam__0(v_struct_1359_, v_a_1350_, v_a_1351_, v_a_1352_, v_a_1353_, v_a_1354_, v_a_1355_);
if (lean_obj_tag(v___x_1360_) == 0)
{
lean_object* v_a_1361_; lean_object* v___x_1363_; uint8_t v_isShared_1364_; uint8_t v_isSharedCheck_1375_; 
v_a_1361_ = lean_ctor_get(v___x_1360_, 0);
v_isSharedCheck_1375_ = !lean_is_exclusive(v___x_1360_);
if (v_isSharedCheck_1375_ == 0)
{
v___x_1363_ = v___x_1360_;
v_isShared_1364_ = v_isSharedCheck_1375_;
goto v_resetjp_1362_;
}
else
{
lean_inc(v_a_1361_);
lean_dec(v___x_1360_);
v___x_1363_ = lean_box(0);
v_isShared_1364_ = v_isSharedCheck_1375_;
goto v_resetjp_1362_;
}
v_resetjp_1362_:
{
size_t v___x_1365_; size_t v___x_1366_; uint8_t v___x_1367_; 
v___x_1365_ = lean_ptr_addr(v_struct_1359_);
v___x_1366_ = lean_ptr_addr(v_a_1361_);
v___x_1367_ = lean_usize_dec_eq(v___x_1365_, v___x_1366_);
if (v___x_1367_ == 0)
{
lean_object* v___x_1368_; lean_object* v___x_1370_; 
lean_inc(v_idx_1358_);
lean_inc(v_typeName_1357_);
lean_dec_ref_known(v_e_1349_, 3);
v___x_1368_ = l_Lean_Expr_proj___override(v_typeName_1357_, v_idx_1358_, v_a_1361_);
if (v_isShared_1364_ == 0)
{
lean_ctor_set(v___x_1363_, 0, v___x_1368_);
v___x_1370_ = v___x_1363_;
goto v_reusejp_1369_;
}
else
{
lean_object* v_reuseFailAlloc_1371_; 
v_reuseFailAlloc_1371_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1371_, 0, v___x_1368_);
v___x_1370_ = v_reuseFailAlloc_1371_;
goto v_reusejp_1369_;
}
v_reusejp_1369_:
{
return v___x_1370_;
}
}
else
{
lean_object* v___x_1373_; 
lean_dec(v_a_1361_);
if (v_isShared_1364_ == 0)
{
lean_ctor_set(v___x_1363_, 0, v_e_1349_);
v___x_1373_ = v___x_1363_;
goto v_reusejp_1372_;
}
else
{
lean_object* v_reuseFailAlloc_1374_; 
v_reuseFailAlloc_1374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1374_, 0, v_e_1349_);
v___x_1373_ = v_reuseFailAlloc_1374_;
goto v_reusejp_1372_;
}
v_reusejp_1372_:
{
return v___x_1373_;
}
}
}
}
else
{
lean_dec_ref_known(v_e_1349_, 3);
return v___x_1360_;
}
}
case 7:
{
lean_object* v_binderName_1376_; lean_object* v_binderType_1377_; lean_object* v_body_1378_; uint8_t v_binderInfo_1379_; lean_object* v___x_1380_; 
v_binderName_1376_ = lean_ctor_get(v_e_1349_, 0);
v_binderType_1377_ = lean_ctor_get(v_e_1349_, 1);
v_body_1378_ = lean_ctor_get(v_e_1349_, 2);
v_binderInfo_1379_ = lean_ctor_get_uint8(v_e_1349_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_1377_);
v___x_1380_ = l_Lean_Meta_Closure_collectExprAux___lam__0(v_binderType_1377_, v_a_1350_, v_a_1351_, v_a_1352_, v_a_1353_, v_a_1354_, v_a_1355_);
if (lean_obj_tag(v___x_1380_) == 0)
{
lean_object* v_a_1381_; lean_object* v___x_1382_; 
v_a_1381_ = lean_ctor_get(v___x_1380_, 0);
lean_inc(v_a_1381_);
lean_dec_ref_known(v___x_1380_, 1);
lean_inc_ref(v_body_1378_);
v___x_1382_ = l_Lean_Meta_Closure_collectExprAux___lam__0(v_body_1378_, v_a_1350_, v_a_1351_, v_a_1352_, v_a_1353_, v_a_1354_, v_a_1355_);
if (lean_obj_tag(v___x_1382_) == 0)
{
lean_object* v_a_1383_; lean_object* v___x_1385_; uint8_t v_isShared_1386_; uint8_t v_isSharedCheck_1407_; 
v_a_1383_ = lean_ctor_get(v___x_1382_, 0);
v_isSharedCheck_1407_ = !lean_is_exclusive(v___x_1382_);
if (v_isSharedCheck_1407_ == 0)
{
v___x_1385_ = v___x_1382_;
v_isShared_1386_ = v_isSharedCheck_1407_;
goto v_resetjp_1384_;
}
else
{
lean_inc(v_a_1383_);
lean_dec(v___x_1382_);
v___x_1385_ = lean_box(0);
v_isShared_1386_ = v_isSharedCheck_1407_;
goto v_resetjp_1384_;
}
v_resetjp_1384_:
{
uint8_t v___y_1388_; size_t v___x_1401_; size_t v___x_1402_; uint8_t v___x_1403_; 
v___x_1401_ = lean_ptr_addr(v_binderType_1377_);
v___x_1402_ = lean_ptr_addr(v_a_1381_);
v___x_1403_ = lean_usize_dec_eq(v___x_1401_, v___x_1402_);
if (v___x_1403_ == 0)
{
v___y_1388_ = v___x_1403_;
goto v___jp_1387_;
}
else
{
size_t v___x_1404_; size_t v___x_1405_; uint8_t v___x_1406_; 
v___x_1404_ = lean_ptr_addr(v_body_1378_);
v___x_1405_ = lean_ptr_addr(v_a_1383_);
v___x_1406_ = lean_usize_dec_eq(v___x_1404_, v___x_1405_);
v___y_1388_ = v___x_1406_;
goto v___jp_1387_;
}
v___jp_1387_:
{
if (v___y_1388_ == 0)
{
lean_object* v___x_1389_; lean_object* v___x_1391_; 
lean_inc(v_binderName_1376_);
lean_dec_ref_known(v_e_1349_, 3);
v___x_1389_ = l_Lean_Expr_forallE___override(v_binderName_1376_, v_a_1381_, v_a_1383_, v_binderInfo_1379_);
if (v_isShared_1386_ == 0)
{
lean_ctor_set(v___x_1385_, 0, v___x_1389_);
v___x_1391_ = v___x_1385_;
goto v_reusejp_1390_;
}
else
{
lean_object* v_reuseFailAlloc_1392_; 
v_reuseFailAlloc_1392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1392_, 0, v___x_1389_);
v___x_1391_ = v_reuseFailAlloc_1392_;
goto v_reusejp_1390_;
}
v_reusejp_1390_:
{
return v___x_1391_;
}
}
else
{
uint8_t v___x_1393_; 
v___x_1393_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_1379_, v_binderInfo_1379_);
if (v___x_1393_ == 0)
{
lean_object* v___x_1394_; lean_object* v___x_1396_; 
lean_inc(v_binderName_1376_);
lean_dec_ref_known(v_e_1349_, 3);
v___x_1394_ = l_Lean_Expr_forallE___override(v_binderName_1376_, v_a_1381_, v_a_1383_, v_binderInfo_1379_);
if (v_isShared_1386_ == 0)
{
lean_ctor_set(v___x_1385_, 0, v___x_1394_);
v___x_1396_ = v___x_1385_;
goto v_reusejp_1395_;
}
else
{
lean_object* v_reuseFailAlloc_1397_; 
v_reuseFailAlloc_1397_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1397_, 0, v___x_1394_);
v___x_1396_ = v_reuseFailAlloc_1397_;
goto v_reusejp_1395_;
}
v_reusejp_1395_:
{
return v___x_1396_;
}
}
else
{
lean_object* v___x_1399_; 
lean_dec(v_a_1383_);
lean_dec(v_a_1381_);
if (v_isShared_1386_ == 0)
{
lean_ctor_set(v___x_1385_, 0, v_e_1349_);
v___x_1399_ = v___x_1385_;
goto v_reusejp_1398_;
}
else
{
lean_object* v_reuseFailAlloc_1400_; 
v_reuseFailAlloc_1400_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1400_, 0, v_e_1349_);
v___x_1399_ = v_reuseFailAlloc_1400_;
goto v_reusejp_1398_;
}
v_reusejp_1398_:
{
return v___x_1399_;
}
}
}
}
}
}
else
{
lean_dec(v_a_1381_);
lean_dec_ref_known(v_e_1349_, 3);
return v___x_1382_;
}
}
else
{
lean_dec_ref_known(v_e_1349_, 3);
return v___x_1380_;
}
}
case 6:
{
lean_object* v_binderName_1408_; lean_object* v_binderType_1409_; lean_object* v_body_1410_; uint8_t v_binderInfo_1411_; lean_object* v___x_1412_; 
v_binderName_1408_ = lean_ctor_get(v_e_1349_, 0);
v_binderType_1409_ = lean_ctor_get(v_e_1349_, 1);
v_body_1410_ = lean_ctor_get(v_e_1349_, 2);
v_binderInfo_1411_ = lean_ctor_get_uint8(v_e_1349_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_1409_);
v___x_1412_ = l_Lean_Meta_Closure_collectExprAux___lam__0(v_binderType_1409_, v_a_1350_, v_a_1351_, v_a_1352_, v_a_1353_, v_a_1354_, v_a_1355_);
if (lean_obj_tag(v___x_1412_) == 0)
{
lean_object* v_a_1413_; lean_object* v___x_1414_; 
v_a_1413_ = lean_ctor_get(v___x_1412_, 0);
lean_inc(v_a_1413_);
lean_dec_ref_known(v___x_1412_, 1);
lean_inc_ref(v_body_1410_);
v___x_1414_ = l_Lean_Meta_Closure_collectExprAux___lam__0(v_body_1410_, v_a_1350_, v_a_1351_, v_a_1352_, v_a_1353_, v_a_1354_, v_a_1355_);
if (lean_obj_tag(v___x_1414_) == 0)
{
lean_object* v_a_1415_; lean_object* v___x_1417_; uint8_t v_isShared_1418_; uint8_t v_isSharedCheck_1439_; 
v_a_1415_ = lean_ctor_get(v___x_1414_, 0);
v_isSharedCheck_1439_ = !lean_is_exclusive(v___x_1414_);
if (v_isSharedCheck_1439_ == 0)
{
v___x_1417_ = v___x_1414_;
v_isShared_1418_ = v_isSharedCheck_1439_;
goto v_resetjp_1416_;
}
else
{
lean_inc(v_a_1415_);
lean_dec(v___x_1414_);
v___x_1417_ = lean_box(0);
v_isShared_1418_ = v_isSharedCheck_1439_;
goto v_resetjp_1416_;
}
v_resetjp_1416_:
{
uint8_t v___y_1420_; size_t v___x_1433_; size_t v___x_1434_; uint8_t v___x_1435_; 
v___x_1433_ = lean_ptr_addr(v_binderType_1409_);
v___x_1434_ = lean_ptr_addr(v_a_1413_);
v___x_1435_ = lean_usize_dec_eq(v___x_1433_, v___x_1434_);
if (v___x_1435_ == 0)
{
v___y_1420_ = v___x_1435_;
goto v___jp_1419_;
}
else
{
size_t v___x_1436_; size_t v___x_1437_; uint8_t v___x_1438_; 
v___x_1436_ = lean_ptr_addr(v_body_1410_);
v___x_1437_ = lean_ptr_addr(v_a_1415_);
v___x_1438_ = lean_usize_dec_eq(v___x_1436_, v___x_1437_);
v___y_1420_ = v___x_1438_;
goto v___jp_1419_;
}
v___jp_1419_:
{
if (v___y_1420_ == 0)
{
lean_object* v___x_1421_; lean_object* v___x_1423_; 
lean_inc(v_binderName_1408_);
lean_dec_ref_known(v_e_1349_, 3);
v___x_1421_ = l_Lean_Expr_lam___override(v_binderName_1408_, v_a_1413_, v_a_1415_, v_binderInfo_1411_);
if (v_isShared_1418_ == 0)
{
lean_ctor_set(v___x_1417_, 0, v___x_1421_);
v___x_1423_ = v___x_1417_;
goto v_reusejp_1422_;
}
else
{
lean_object* v_reuseFailAlloc_1424_; 
v_reuseFailAlloc_1424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1424_, 0, v___x_1421_);
v___x_1423_ = v_reuseFailAlloc_1424_;
goto v_reusejp_1422_;
}
v_reusejp_1422_:
{
return v___x_1423_;
}
}
else
{
uint8_t v___x_1425_; 
v___x_1425_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_1411_, v_binderInfo_1411_);
if (v___x_1425_ == 0)
{
lean_object* v___x_1426_; lean_object* v___x_1428_; 
lean_inc(v_binderName_1408_);
lean_dec_ref_known(v_e_1349_, 3);
v___x_1426_ = l_Lean_Expr_lam___override(v_binderName_1408_, v_a_1413_, v_a_1415_, v_binderInfo_1411_);
if (v_isShared_1418_ == 0)
{
lean_ctor_set(v___x_1417_, 0, v___x_1426_);
v___x_1428_ = v___x_1417_;
goto v_reusejp_1427_;
}
else
{
lean_object* v_reuseFailAlloc_1429_; 
v_reuseFailAlloc_1429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1429_, 0, v___x_1426_);
v___x_1428_ = v_reuseFailAlloc_1429_;
goto v_reusejp_1427_;
}
v_reusejp_1427_:
{
return v___x_1428_;
}
}
else
{
lean_object* v___x_1431_; 
lean_dec(v_a_1415_);
lean_dec(v_a_1413_);
if (v_isShared_1418_ == 0)
{
lean_ctor_set(v___x_1417_, 0, v_e_1349_);
v___x_1431_ = v___x_1417_;
goto v_reusejp_1430_;
}
else
{
lean_object* v_reuseFailAlloc_1432_; 
v_reuseFailAlloc_1432_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1432_, 0, v_e_1349_);
v___x_1431_ = v_reuseFailAlloc_1432_;
goto v_reusejp_1430_;
}
v_reusejp_1430_:
{
return v___x_1431_;
}
}
}
}
}
}
else
{
lean_dec(v_a_1413_);
lean_dec_ref_known(v_e_1349_, 3);
return v___x_1414_;
}
}
else
{
lean_dec_ref_known(v_e_1349_, 3);
return v___x_1412_;
}
}
case 8:
{
lean_object* v_declName_1440_; lean_object* v_type_1441_; lean_object* v_value_1442_; lean_object* v_body_1443_; uint8_t v_nondep_1444_; lean_object* v___x_1445_; 
v_declName_1440_ = lean_ctor_get(v_e_1349_, 0);
v_type_1441_ = lean_ctor_get(v_e_1349_, 1);
v_value_1442_ = lean_ctor_get(v_e_1349_, 2);
v_body_1443_ = lean_ctor_get(v_e_1349_, 3);
v_nondep_1444_ = lean_ctor_get_uint8(v_e_1349_, sizeof(void*)*4 + 8);
lean_inc_ref(v_type_1441_);
v___x_1445_ = l_Lean_Meta_Closure_collectExprAux___lam__0(v_type_1441_, v_a_1350_, v_a_1351_, v_a_1352_, v_a_1353_, v_a_1354_, v_a_1355_);
if (lean_obj_tag(v___x_1445_) == 0)
{
lean_object* v_a_1446_; lean_object* v___x_1447_; 
v_a_1446_ = lean_ctor_get(v___x_1445_, 0);
lean_inc(v_a_1446_);
lean_dec_ref_known(v___x_1445_, 1);
lean_inc_ref(v_value_1442_);
v___x_1447_ = l_Lean_Meta_Closure_collectExprAux___lam__0(v_value_1442_, v_a_1350_, v_a_1351_, v_a_1352_, v_a_1353_, v_a_1354_, v_a_1355_);
if (lean_obj_tag(v___x_1447_) == 0)
{
lean_object* v_a_1448_; lean_object* v___x_1449_; 
v_a_1448_ = lean_ctor_get(v___x_1447_, 0);
lean_inc(v_a_1448_);
lean_dec_ref_known(v___x_1447_, 1);
lean_inc_ref(v_body_1443_);
v___x_1449_ = l_Lean_Meta_Closure_collectExprAux___lam__0(v_body_1443_, v_a_1350_, v_a_1351_, v_a_1352_, v_a_1353_, v_a_1354_, v_a_1355_);
if (lean_obj_tag(v___x_1449_) == 0)
{
lean_object* v_a_1450_; lean_object* v___x_1452_; uint8_t v_isShared_1453_; uint8_t v_isSharedCheck_1476_; 
v_a_1450_ = lean_ctor_get(v___x_1449_, 0);
v_isSharedCheck_1476_ = !lean_is_exclusive(v___x_1449_);
if (v_isSharedCheck_1476_ == 0)
{
v___x_1452_ = v___x_1449_;
v_isShared_1453_ = v_isSharedCheck_1476_;
goto v_resetjp_1451_;
}
else
{
lean_inc(v_a_1450_);
lean_dec(v___x_1449_);
v___x_1452_ = lean_box(0);
v_isShared_1453_ = v_isSharedCheck_1476_;
goto v_resetjp_1451_;
}
v_resetjp_1451_:
{
uint8_t v___y_1455_; size_t v___x_1470_; size_t v___x_1471_; uint8_t v___x_1472_; 
v___x_1470_ = lean_ptr_addr(v_type_1441_);
v___x_1471_ = lean_ptr_addr(v_a_1446_);
v___x_1472_ = lean_usize_dec_eq(v___x_1470_, v___x_1471_);
if (v___x_1472_ == 0)
{
v___y_1455_ = v___x_1472_;
goto v___jp_1454_;
}
else
{
size_t v___x_1473_; size_t v___x_1474_; uint8_t v___x_1475_; 
v___x_1473_ = lean_ptr_addr(v_value_1442_);
v___x_1474_ = lean_ptr_addr(v_a_1448_);
v___x_1475_ = lean_usize_dec_eq(v___x_1473_, v___x_1474_);
v___y_1455_ = v___x_1475_;
goto v___jp_1454_;
}
v___jp_1454_:
{
if (v___y_1455_ == 0)
{
lean_object* v___x_1456_; lean_object* v___x_1458_; 
lean_inc(v_declName_1440_);
lean_dec_ref_known(v_e_1349_, 4);
v___x_1456_ = l_Lean_Expr_letE___override(v_declName_1440_, v_a_1446_, v_a_1448_, v_a_1450_, v_nondep_1444_);
if (v_isShared_1453_ == 0)
{
lean_ctor_set(v___x_1452_, 0, v___x_1456_);
v___x_1458_ = v___x_1452_;
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
size_t v___x_1460_; size_t v___x_1461_; uint8_t v___x_1462_; 
v___x_1460_ = lean_ptr_addr(v_body_1443_);
v___x_1461_ = lean_ptr_addr(v_a_1450_);
v___x_1462_ = lean_usize_dec_eq(v___x_1460_, v___x_1461_);
if (v___x_1462_ == 0)
{
lean_object* v___x_1463_; lean_object* v___x_1465_; 
lean_inc(v_declName_1440_);
lean_dec_ref_known(v_e_1349_, 4);
v___x_1463_ = l_Lean_Expr_letE___override(v_declName_1440_, v_a_1446_, v_a_1448_, v_a_1450_, v_nondep_1444_);
if (v_isShared_1453_ == 0)
{
lean_ctor_set(v___x_1452_, 0, v___x_1463_);
v___x_1465_ = v___x_1452_;
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
lean_object* v___x_1468_; 
lean_dec(v_a_1450_);
lean_dec(v_a_1448_);
lean_dec(v_a_1446_);
if (v_isShared_1453_ == 0)
{
lean_ctor_set(v___x_1452_, 0, v_e_1349_);
v___x_1468_ = v___x_1452_;
goto v_reusejp_1467_;
}
else
{
lean_object* v_reuseFailAlloc_1469_; 
v_reuseFailAlloc_1469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1469_, 0, v_e_1349_);
v___x_1468_ = v_reuseFailAlloc_1469_;
goto v_reusejp_1467_;
}
v_reusejp_1467_:
{
return v___x_1468_;
}
}
}
}
}
}
else
{
lean_dec(v_a_1448_);
lean_dec(v_a_1446_);
lean_dec_ref_known(v_e_1349_, 4);
return v___x_1449_;
}
}
else
{
lean_dec(v_a_1446_);
lean_dec_ref_known(v_e_1349_, 4);
return v___x_1447_;
}
}
else
{
lean_dec_ref_known(v_e_1349_, 4);
return v___x_1445_;
}
}
case 5:
{
lean_object* v_fn_1477_; lean_object* v_arg_1478_; lean_object* v___x_1479_; 
v_fn_1477_ = lean_ctor_get(v_e_1349_, 0);
v_arg_1478_ = lean_ctor_get(v_e_1349_, 1);
lean_inc_ref(v_fn_1477_);
v___x_1479_ = l_Lean_Meta_Closure_collectExprAux___lam__0(v_fn_1477_, v_a_1350_, v_a_1351_, v_a_1352_, v_a_1353_, v_a_1354_, v_a_1355_);
if (lean_obj_tag(v___x_1479_) == 0)
{
lean_object* v_a_1480_; lean_object* v___x_1481_; 
v_a_1480_ = lean_ctor_get(v___x_1479_, 0);
lean_inc(v_a_1480_);
lean_dec_ref_known(v___x_1479_, 1);
lean_inc_ref(v_arg_1478_);
v___x_1481_ = l_Lean_Meta_Closure_collectExprAux___lam__0(v_arg_1478_, v_a_1350_, v_a_1351_, v_a_1352_, v_a_1353_, v_a_1354_, v_a_1355_);
if (lean_obj_tag(v___x_1481_) == 0)
{
lean_object* v_a_1482_; lean_object* v___x_1484_; uint8_t v_isShared_1485_; uint8_t v_isSharedCheck_1501_; 
v_a_1482_ = lean_ctor_get(v___x_1481_, 0);
v_isSharedCheck_1501_ = !lean_is_exclusive(v___x_1481_);
if (v_isSharedCheck_1501_ == 0)
{
v___x_1484_ = v___x_1481_;
v_isShared_1485_ = v_isSharedCheck_1501_;
goto v_resetjp_1483_;
}
else
{
lean_inc(v_a_1482_);
lean_dec(v___x_1481_);
v___x_1484_ = lean_box(0);
v_isShared_1485_ = v_isSharedCheck_1501_;
goto v_resetjp_1483_;
}
v_resetjp_1483_:
{
uint8_t v___y_1487_; size_t v___x_1495_; size_t v___x_1496_; uint8_t v___x_1497_; 
v___x_1495_ = lean_ptr_addr(v_fn_1477_);
v___x_1496_ = lean_ptr_addr(v_a_1480_);
v___x_1497_ = lean_usize_dec_eq(v___x_1495_, v___x_1496_);
if (v___x_1497_ == 0)
{
v___y_1487_ = v___x_1497_;
goto v___jp_1486_;
}
else
{
size_t v___x_1498_; size_t v___x_1499_; uint8_t v___x_1500_; 
v___x_1498_ = lean_ptr_addr(v_arg_1478_);
v___x_1499_ = lean_ptr_addr(v_a_1482_);
v___x_1500_ = lean_usize_dec_eq(v___x_1498_, v___x_1499_);
v___y_1487_ = v___x_1500_;
goto v___jp_1486_;
}
v___jp_1486_:
{
if (v___y_1487_ == 0)
{
lean_object* v___x_1488_; lean_object* v___x_1490_; 
lean_dec_ref_known(v_e_1349_, 2);
v___x_1488_ = l_Lean_Expr_app___override(v_a_1480_, v_a_1482_);
if (v_isShared_1485_ == 0)
{
lean_ctor_set(v___x_1484_, 0, v___x_1488_);
v___x_1490_ = v___x_1484_;
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
lean_dec(v_a_1482_);
lean_dec(v_a_1480_);
if (v_isShared_1485_ == 0)
{
lean_ctor_set(v___x_1484_, 0, v_e_1349_);
v___x_1493_ = v___x_1484_;
goto v_reusejp_1492_;
}
else
{
lean_object* v_reuseFailAlloc_1494_; 
v_reuseFailAlloc_1494_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1494_, 0, v_e_1349_);
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
}
else
{
lean_dec(v_a_1480_);
lean_dec_ref_known(v_e_1349_, 2);
return v___x_1481_;
}
}
else
{
lean_dec_ref_known(v_e_1349_, 2);
return v___x_1479_;
}
}
case 10:
{
lean_object* v_data_1502_; lean_object* v_expr_1503_; lean_object* v___x_1504_; 
v_data_1502_ = lean_ctor_get(v_e_1349_, 0);
v_expr_1503_ = lean_ctor_get(v_e_1349_, 1);
lean_inc_ref(v_expr_1503_);
v___x_1504_ = l_Lean_Meta_Closure_collectExprAux___lam__0(v_expr_1503_, v_a_1350_, v_a_1351_, v_a_1352_, v_a_1353_, v_a_1354_, v_a_1355_);
if (lean_obj_tag(v___x_1504_) == 0)
{
lean_object* v_a_1505_; lean_object* v___x_1507_; uint8_t v_isShared_1508_; uint8_t v_isSharedCheck_1519_; 
v_a_1505_ = lean_ctor_get(v___x_1504_, 0);
v_isSharedCheck_1519_ = !lean_is_exclusive(v___x_1504_);
if (v_isSharedCheck_1519_ == 0)
{
v___x_1507_ = v___x_1504_;
v_isShared_1508_ = v_isSharedCheck_1519_;
goto v_resetjp_1506_;
}
else
{
lean_inc(v_a_1505_);
lean_dec(v___x_1504_);
v___x_1507_ = lean_box(0);
v_isShared_1508_ = v_isSharedCheck_1519_;
goto v_resetjp_1506_;
}
v_resetjp_1506_:
{
size_t v___x_1509_; size_t v___x_1510_; uint8_t v___x_1511_; 
v___x_1509_ = lean_ptr_addr(v_expr_1503_);
v___x_1510_ = lean_ptr_addr(v_a_1505_);
v___x_1511_ = lean_usize_dec_eq(v___x_1509_, v___x_1510_);
if (v___x_1511_ == 0)
{
lean_object* v___x_1512_; lean_object* v___x_1514_; 
lean_inc(v_data_1502_);
lean_dec_ref_known(v_e_1349_, 2);
v___x_1512_ = l_Lean_Expr_mdata___override(v_data_1502_, v_a_1505_);
if (v_isShared_1508_ == 0)
{
lean_ctor_set(v___x_1507_, 0, v___x_1512_);
v___x_1514_ = v___x_1507_;
goto v_reusejp_1513_;
}
else
{
lean_object* v_reuseFailAlloc_1515_; 
v_reuseFailAlloc_1515_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1515_, 0, v___x_1512_);
v___x_1514_ = v_reuseFailAlloc_1515_;
goto v_reusejp_1513_;
}
v_reusejp_1513_:
{
return v___x_1514_;
}
}
else
{
lean_object* v___x_1517_; 
lean_dec(v_a_1505_);
if (v_isShared_1508_ == 0)
{
lean_ctor_set(v___x_1507_, 0, v_e_1349_);
v___x_1517_ = v___x_1507_;
goto v_reusejp_1516_;
}
else
{
lean_object* v_reuseFailAlloc_1518_; 
v_reuseFailAlloc_1518_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1518_, 0, v_e_1349_);
v___x_1517_ = v_reuseFailAlloc_1518_;
goto v_reusejp_1516_;
}
v_reusejp_1516_:
{
return v___x_1517_;
}
}
}
}
else
{
lean_dec_ref_known(v_e_1349_, 2);
return v___x_1504_;
}
}
case 3:
{
lean_object* v_u_1520_; lean_object* v___x_1521_; 
v_u_1520_ = lean_ctor_get(v_e_1349_, 0);
lean_inc(v_u_1520_);
v___x_1521_ = l_Lean_Meta_Closure_collectLevel___redArg(v_u_1520_, v_a_1351_);
if (lean_obj_tag(v___x_1521_) == 0)
{
lean_object* v_a_1522_; lean_object* v___x_1524_; uint8_t v_isShared_1525_; uint8_t v_isSharedCheck_1536_; 
v_a_1522_ = lean_ctor_get(v___x_1521_, 0);
v_isSharedCheck_1536_ = !lean_is_exclusive(v___x_1521_);
if (v_isSharedCheck_1536_ == 0)
{
v___x_1524_ = v___x_1521_;
v_isShared_1525_ = v_isSharedCheck_1536_;
goto v_resetjp_1523_;
}
else
{
lean_inc(v_a_1522_);
lean_dec(v___x_1521_);
v___x_1524_ = lean_box(0);
v_isShared_1525_ = v_isSharedCheck_1536_;
goto v_resetjp_1523_;
}
v_resetjp_1523_:
{
size_t v___x_1526_; size_t v___x_1527_; uint8_t v___x_1528_; 
v___x_1526_ = lean_ptr_addr(v_u_1520_);
v___x_1527_ = lean_ptr_addr(v_a_1522_);
v___x_1528_ = lean_usize_dec_eq(v___x_1526_, v___x_1527_);
if (v___x_1528_ == 0)
{
lean_object* v___x_1529_; lean_object* v___x_1531_; 
lean_dec_ref_known(v_e_1349_, 1);
v___x_1529_ = l_Lean_Expr_sort___override(v_a_1522_);
if (v_isShared_1525_ == 0)
{
lean_ctor_set(v___x_1524_, 0, v___x_1529_);
v___x_1531_ = v___x_1524_;
goto v_reusejp_1530_;
}
else
{
lean_object* v_reuseFailAlloc_1532_; 
v_reuseFailAlloc_1532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1532_, 0, v___x_1529_);
v___x_1531_ = v_reuseFailAlloc_1532_;
goto v_reusejp_1530_;
}
v_reusejp_1530_:
{
return v___x_1531_;
}
}
else
{
lean_object* v___x_1534_; 
lean_dec(v_a_1522_);
if (v_isShared_1525_ == 0)
{
lean_ctor_set(v___x_1524_, 0, v_e_1349_);
v___x_1534_ = v___x_1524_;
goto v_reusejp_1533_;
}
else
{
lean_object* v_reuseFailAlloc_1535_; 
v_reuseFailAlloc_1535_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1535_, 0, v_e_1349_);
v___x_1534_ = v_reuseFailAlloc_1535_;
goto v_reusejp_1533_;
}
v_reusejp_1533_:
{
return v___x_1534_;
}
}
}
}
else
{
lean_object* v_a_1537_; lean_object* v___x_1539_; uint8_t v_isShared_1540_; uint8_t v_isSharedCheck_1544_; 
lean_dec_ref_known(v_e_1349_, 1);
v_a_1537_ = lean_ctor_get(v___x_1521_, 0);
v_isSharedCheck_1544_ = !lean_is_exclusive(v___x_1521_);
if (v_isSharedCheck_1544_ == 0)
{
v___x_1539_ = v___x_1521_;
v_isShared_1540_ = v_isSharedCheck_1544_;
goto v_resetjp_1538_;
}
else
{
lean_inc(v_a_1537_);
lean_dec(v___x_1521_);
v___x_1539_ = lean_box(0);
v_isShared_1540_ = v_isSharedCheck_1544_;
goto v_resetjp_1538_;
}
v_resetjp_1538_:
{
lean_object* v___x_1542_; 
if (v_isShared_1540_ == 0)
{
v___x_1542_ = v___x_1539_;
goto v_reusejp_1541_;
}
else
{
lean_object* v_reuseFailAlloc_1543_; 
v_reuseFailAlloc_1543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1543_, 0, v_a_1537_);
v___x_1542_ = v_reuseFailAlloc_1543_;
goto v_reusejp_1541_;
}
v_reusejp_1541_:
{
return v___x_1542_;
}
}
}
}
case 4:
{
lean_object* v_declName_1545_; lean_object* v_us_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; 
v_declName_1545_ = lean_ctor_get(v_e_1349_, 0);
v_us_1546_ = lean_ctor_get(v_e_1349_, 1);
v___x_1547_ = lean_box(0);
lean_inc(v_us_1546_);
v___x_1548_ = l_List_mapM_loop___at___00Lean_Meta_Closure_collectExprAux_spec__2___redArg(v_us_1546_, v___x_1547_, v_a_1351_);
if (lean_obj_tag(v___x_1548_) == 0)
{
lean_object* v_a_1549_; lean_object* v___x_1551_; uint8_t v_isShared_1552_; uint8_t v_isSharedCheck_1561_; 
v_a_1549_ = lean_ctor_get(v___x_1548_, 0);
v_isSharedCheck_1561_ = !lean_is_exclusive(v___x_1548_);
if (v_isSharedCheck_1561_ == 0)
{
v___x_1551_ = v___x_1548_;
v_isShared_1552_ = v_isSharedCheck_1561_;
goto v_resetjp_1550_;
}
else
{
lean_inc(v_a_1549_);
lean_dec(v___x_1548_);
v___x_1551_ = lean_box(0);
v_isShared_1552_ = v_isSharedCheck_1561_;
goto v_resetjp_1550_;
}
v_resetjp_1550_:
{
uint8_t v___x_1553_; 
v___x_1553_ = l_ptrEqList___redArg(v_us_1546_, v_a_1549_);
if (v___x_1553_ == 0)
{
lean_object* v___x_1554_; lean_object* v___x_1556_; 
lean_inc(v_declName_1545_);
lean_dec_ref_known(v_e_1349_, 2);
v___x_1554_ = l_Lean_Expr_const___override(v_declName_1545_, v_a_1549_);
if (v_isShared_1552_ == 0)
{
lean_ctor_set(v___x_1551_, 0, v___x_1554_);
v___x_1556_ = v___x_1551_;
goto v_reusejp_1555_;
}
else
{
lean_object* v_reuseFailAlloc_1557_; 
v_reuseFailAlloc_1557_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1557_, 0, v___x_1554_);
v___x_1556_ = v_reuseFailAlloc_1557_;
goto v_reusejp_1555_;
}
v_reusejp_1555_:
{
return v___x_1556_;
}
}
else
{
lean_object* v___x_1559_; 
lean_dec(v_a_1549_);
if (v_isShared_1552_ == 0)
{
lean_ctor_set(v___x_1551_, 0, v_e_1349_);
v___x_1559_ = v___x_1551_;
goto v_reusejp_1558_;
}
else
{
lean_object* v_reuseFailAlloc_1560_; 
v_reuseFailAlloc_1560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1560_, 0, v_e_1349_);
v___x_1559_ = v_reuseFailAlloc_1560_;
goto v_reusejp_1558_;
}
v_reusejp_1558_:
{
return v___x_1559_;
}
}
}
}
else
{
lean_object* v_a_1562_; lean_object* v___x_1564_; uint8_t v_isShared_1565_; uint8_t v_isSharedCheck_1569_; 
lean_dec_ref_known(v_e_1349_, 2);
v_a_1562_ = lean_ctor_get(v___x_1548_, 0);
v_isSharedCheck_1569_ = !lean_is_exclusive(v___x_1548_);
if (v_isSharedCheck_1569_ == 0)
{
v___x_1564_ = v___x_1548_;
v_isShared_1565_ = v_isSharedCheck_1569_;
goto v_resetjp_1563_;
}
else
{
lean_inc(v_a_1562_);
lean_dec(v___x_1548_);
v___x_1564_ = lean_box(0);
v_isShared_1565_ = v_isSharedCheck_1569_;
goto v_resetjp_1563_;
}
v_resetjp_1563_:
{
lean_object* v___x_1567_; 
if (v_isShared_1565_ == 0)
{
v___x_1567_ = v___x_1564_;
goto v_reusejp_1566_;
}
else
{
lean_object* v_reuseFailAlloc_1568_; 
v_reuseFailAlloc_1568_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1568_, 0, v_a_1562_);
v___x_1567_ = v_reuseFailAlloc_1568_;
goto v_reusejp_1566_;
}
v_reusejp_1566_:
{
return v___x_1567_;
}
}
}
}
case 2:
{
lean_object* v_mvarId_1570_; lean_object* v___x_1571_; 
v_mvarId_1570_ = lean_ctor_get(v_e_1349_, 0);
lean_inc(v_mvarId_1570_);
v___x_1571_ = l_Lean_MVarId_getDecl(v_mvarId_1570_, v_a_1352_, v_a_1353_, v_a_1354_, v_a_1355_);
if (lean_obj_tag(v___x_1571_) == 0)
{
lean_object* v_a_1572_; lean_object* v_type_1573_; lean_object* v___x_1574_; 
v_a_1572_ = lean_ctor_get(v___x_1571_, 0);
lean_inc(v_a_1572_);
lean_dec_ref_known(v___x_1571_, 1);
v_type_1573_ = lean_ctor_get(v_a_1572_, 2);
lean_inc_ref_n(v_type_1573_, 2);
lean_dec(v_a_1572_);
v___x_1574_ = l_Lean_Meta_Closure_preprocess(v_type_1573_, v_a_1350_, v_a_1351_, v_a_1352_, v_a_1353_, v_a_1354_, v_a_1355_);
if (lean_obj_tag(v___x_1574_) == 0)
{
lean_object* v_a_1575_; lean_object* v___x_1576_; 
v_a_1575_ = lean_ctor_get(v___x_1574_, 0);
lean_inc(v_a_1575_);
lean_dec_ref_known(v___x_1574_, 1);
v___x_1576_ = l_Lean_Meta_Closure_collectExprAux___lam__0(v_a_1575_, v_a_1350_, v_a_1351_, v_a_1352_, v_a_1353_, v_a_1354_, v_a_1355_);
if (lean_obj_tag(v___x_1576_) == 0)
{
lean_object* v_a_1577_; lean_object* v___x_1578_; 
v_a_1577_ = lean_ctor_get(v___x_1576_, 0);
lean_inc(v_a_1577_);
lean_dec_ref_known(v___x_1576_, 1);
v___x_1578_ = l_Lean_mkFreshFVarId___at___00Lean_Meta_Closure_collectExprAux_spec__3(v_a_1350_, v_a_1351_, v_a_1352_, v_a_1353_, v_a_1354_, v_a_1355_);
if (lean_obj_tag(v___x_1578_) == 0)
{
lean_object* v_a_1579_; lean_object* v___x_1580_; 
v_a_1579_ = lean_ctor_get(v___x_1578_, 0);
lean_inc(v_a_1579_);
lean_dec_ref_known(v___x_1578_, 1);
v___x_1580_ = l_Lean_Meta_Closure_mkNextUserName___redArg(v_a_1351_);
if (lean_obj_tag(v___x_1580_) == 0)
{
lean_object* v_a_1581_; lean_object* v___x_1583_; uint8_t v_isShared_1584_; uint8_t v_isSharedCheck_1643_; 
v_a_1581_ = lean_ctor_get(v___x_1580_, 0);
v_isSharedCheck_1643_ = !lean_is_exclusive(v___x_1580_);
if (v_isSharedCheck_1643_ == 0)
{
v___x_1583_ = v___x_1580_;
v_isShared_1584_ = v_isSharedCheck_1643_;
goto v_resetjp_1582_;
}
else
{
lean_inc(v_a_1581_);
lean_dec(v___x_1580_);
v___x_1583_ = lean_box(0);
v_isShared_1584_ = v_isSharedCheck_1643_;
goto v_resetjp_1582_;
}
v_resetjp_1582_:
{
lean_object* v_e_x27_1586_; lean_object* v___y_1587_; lean_object* v___x_1619_; 
v___x_1619_ = l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__4___redArg(v_mvarId_1570_, v_a_1353_);
if (lean_obj_tag(v___x_1619_) == 0)
{
lean_object* v_a_1620_; 
v_a_1620_ = lean_ctor_get(v___x_1619_, 0);
lean_inc(v_a_1620_);
lean_dec_ref_known(v___x_1619_, 1);
if (lean_obj_tag(v_a_1620_) == 1)
{
lean_object* v_val_1621_; lean_object* v___x_1623_; uint8_t v_isShared_1624_; uint8_t v_isSharedCheck_1634_; 
v_val_1621_ = lean_ctor_get(v_a_1620_, 0);
v_isSharedCheck_1634_ = !lean_is_exclusive(v_a_1620_);
if (v_isSharedCheck_1634_ == 0)
{
v___x_1623_ = v_a_1620_;
v_isShared_1624_ = v_isSharedCheck_1634_;
goto v_resetjp_1622_;
}
else
{
lean_inc(v_val_1621_);
lean_dec(v_a_1620_);
v___x_1623_ = lean_box(0);
v_isShared_1624_ = v_isSharedCheck_1634_;
goto v_resetjp_1622_;
}
v_resetjp_1622_:
{
lean_object* v_fvars_1625_; lean_object* v___f_1626_; lean_object* v___x_1627_; lean_object* v___x_1629_; 
v_fvars_1625_ = lean_ctor_get(v_val_1621_, 0);
lean_inc_ref(v_fvars_1625_);
lean_dec(v_val_1621_);
v___f_1626_ = lean_alloc_closure((void*)(l_Lean_Meta_Closure_collectExprAux___lam__1___boxed), 10, 1);
lean_closure_set(v___f_1626_, 0, v_e_1349_);
v___x_1627_ = lean_array_get_size(v_fvars_1625_);
lean_dec_ref(v_fvars_1625_);
if (v_isShared_1624_ == 0)
{
lean_ctor_set(v___x_1623_, 0, v___x_1627_);
v___x_1629_ = v___x_1623_;
goto v_reusejp_1628_;
}
else
{
lean_object* v_reuseFailAlloc_1633_; 
v_reuseFailAlloc_1633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1633_, 0, v___x_1627_);
v___x_1629_ = v_reuseFailAlloc_1633_;
goto v_reusejp_1628_;
}
v_reusejp_1628_:
{
uint8_t v___x_1630_; lean_object* v___x_1631_; 
v___x_1630_ = 0;
v___x_1631_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Closure_collectExprAux_spec__5___redArg(v_type_1573_, v___x_1629_, v___f_1626_, v___x_1630_, v___x_1630_, v_a_1350_, v_a_1351_, v_a_1352_, v_a_1353_, v_a_1354_, v_a_1355_);
if (lean_obj_tag(v___x_1631_) == 0)
{
lean_object* v_a_1632_; 
v_a_1632_ = lean_ctor_get(v___x_1631_, 0);
lean_inc(v_a_1632_);
lean_dec_ref_known(v___x_1631_, 1);
v_e_x27_1586_ = v_a_1632_;
v___y_1587_ = v_a_1351_;
goto v___jp_1585_;
}
else
{
lean_del_object(v___x_1583_);
lean_dec(v_a_1581_);
lean_dec(v_a_1579_);
lean_dec(v_a_1577_);
return v___x_1631_;
}
}
}
}
else
{
lean_dec(v_a_1620_);
lean_dec_ref(v_type_1573_);
v_e_x27_1586_ = v_e_1349_;
v___y_1587_ = v_a_1351_;
goto v___jp_1585_;
}
}
else
{
lean_object* v_a_1635_; lean_object* v___x_1637_; uint8_t v_isShared_1638_; uint8_t v_isSharedCheck_1642_; 
lean_del_object(v___x_1583_);
lean_dec(v_a_1581_);
lean_dec(v_a_1579_);
lean_dec(v_a_1577_);
lean_dec_ref(v_type_1573_);
lean_dec_ref_known(v_e_1349_, 1);
v_a_1635_ = lean_ctor_get(v___x_1619_, 0);
v_isSharedCheck_1642_ = !lean_is_exclusive(v___x_1619_);
if (v_isSharedCheck_1642_ == 0)
{
v___x_1637_ = v___x_1619_;
v_isShared_1638_ = v_isSharedCheck_1642_;
goto v_resetjp_1636_;
}
else
{
lean_inc(v_a_1635_);
lean_dec(v___x_1619_);
v___x_1637_ = lean_box(0);
v_isShared_1638_ = v_isSharedCheck_1642_;
goto v_resetjp_1636_;
}
v_resetjp_1636_:
{
lean_object* v___x_1640_; 
if (v_isShared_1638_ == 0)
{
v___x_1640_ = v___x_1637_;
goto v_reusejp_1639_;
}
else
{
lean_object* v_reuseFailAlloc_1641_; 
v_reuseFailAlloc_1641_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1641_, 0, v_a_1635_);
v___x_1640_ = v_reuseFailAlloc_1641_;
goto v_reusejp_1639_;
}
v_reusejp_1639_:
{
return v___x_1640_;
}
}
}
v___jp_1585_:
{
lean_object* v___x_1588_; lean_object* v_visitedLevel_1589_; lean_object* v_visitedExpr_1590_; lean_object* v_levelParams_1591_; lean_object* v_nextLevelIdx_1592_; lean_object* v_levelArgs_1593_; lean_object* v_newLocalDecls_1594_; lean_object* v_newLocalDeclsForMVars_1595_; lean_object* v_newLetDecls_1596_; lean_object* v_nextExprIdx_1597_; lean_object* v_exprMVarArgs_1598_; lean_object* v_exprFVarArgs_1599_; lean_object* v_toProcess_1600_; lean_object* v___x_1602_; uint8_t v_isShared_1603_; uint8_t v_isSharedCheck_1618_; 
v___x_1588_ = lean_st_ref_take(v___y_1587_);
v_visitedLevel_1589_ = lean_ctor_get(v___x_1588_, 0);
v_visitedExpr_1590_ = lean_ctor_get(v___x_1588_, 1);
v_levelParams_1591_ = lean_ctor_get(v___x_1588_, 2);
v_nextLevelIdx_1592_ = lean_ctor_get(v___x_1588_, 3);
v_levelArgs_1593_ = lean_ctor_get(v___x_1588_, 4);
v_newLocalDecls_1594_ = lean_ctor_get(v___x_1588_, 5);
v_newLocalDeclsForMVars_1595_ = lean_ctor_get(v___x_1588_, 6);
v_newLetDecls_1596_ = lean_ctor_get(v___x_1588_, 7);
v_nextExprIdx_1597_ = lean_ctor_get(v___x_1588_, 8);
v_exprMVarArgs_1598_ = lean_ctor_get(v___x_1588_, 9);
v_exprFVarArgs_1599_ = lean_ctor_get(v___x_1588_, 10);
v_toProcess_1600_ = lean_ctor_get(v___x_1588_, 11);
v_isSharedCheck_1618_ = !lean_is_exclusive(v___x_1588_);
if (v_isSharedCheck_1618_ == 0)
{
v___x_1602_ = v___x_1588_;
v_isShared_1603_ = v_isSharedCheck_1618_;
goto v_resetjp_1601_;
}
else
{
lean_inc(v_toProcess_1600_);
lean_inc(v_exprFVarArgs_1599_);
lean_inc(v_exprMVarArgs_1598_);
lean_inc(v_nextExprIdx_1597_);
lean_inc(v_newLetDecls_1596_);
lean_inc(v_newLocalDeclsForMVars_1595_);
lean_inc(v_newLocalDecls_1594_);
lean_inc(v_levelArgs_1593_);
lean_inc(v_nextLevelIdx_1592_);
lean_inc(v_levelParams_1591_);
lean_inc(v_visitedExpr_1590_);
lean_inc(v_visitedLevel_1589_);
lean_dec(v___x_1588_);
v___x_1602_ = lean_box(0);
v_isShared_1603_ = v_isSharedCheck_1618_;
goto v_resetjp_1601_;
}
v_resetjp_1601_:
{
lean_object* v___x_1604_; uint8_t v___x_1605_; uint8_t v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1611_; 
v___x_1604_ = lean_unsigned_to_nat(0u);
v___x_1605_ = 0;
v___x_1606_ = 0;
lean_inc(v_a_1579_);
v___x_1607_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_1607_, 0, v___x_1604_);
lean_ctor_set(v___x_1607_, 1, v_a_1579_);
lean_ctor_set(v___x_1607_, 2, v_a_1581_);
lean_ctor_set(v___x_1607_, 3, v_a_1577_);
lean_ctor_set_uint8(v___x_1607_, sizeof(void*)*4, v___x_1605_);
lean_ctor_set_uint8(v___x_1607_, sizeof(void*)*4 + 1, v___x_1606_);
v___x_1608_ = lean_array_push(v_newLocalDeclsForMVars_1595_, v___x_1607_);
v___x_1609_ = lean_array_push(v_exprMVarArgs_1598_, v_e_x27_1586_);
if (v_isShared_1603_ == 0)
{
lean_ctor_set(v___x_1602_, 9, v___x_1609_);
lean_ctor_set(v___x_1602_, 6, v___x_1608_);
v___x_1611_ = v___x_1602_;
goto v_reusejp_1610_;
}
else
{
lean_object* v_reuseFailAlloc_1617_; 
v_reuseFailAlloc_1617_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_1617_, 0, v_visitedLevel_1589_);
lean_ctor_set(v_reuseFailAlloc_1617_, 1, v_visitedExpr_1590_);
lean_ctor_set(v_reuseFailAlloc_1617_, 2, v_levelParams_1591_);
lean_ctor_set(v_reuseFailAlloc_1617_, 3, v_nextLevelIdx_1592_);
lean_ctor_set(v_reuseFailAlloc_1617_, 4, v_levelArgs_1593_);
lean_ctor_set(v_reuseFailAlloc_1617_, 5, v_newLocalDecls_1594_);
lean_ctor_set(v_reuseFailAlloc_1617_, 6, v___x_1608_);
lean_ctor_set(v_reuseFailAlloc_1617_, 7, v_newLetDecls_1596_);
lean_ctor_set(v_reuseFailAlloc_1617_, 8, v_nextExprIdx_1597_);
lean_ctor_set(v_reuseFailAlloc_1617_, 9, v___x_1609_);
lean_ctor_set(v_reuseFailAlloc_1617_, 10, v_exprFVarArgs_1599_);
lean_ctor_set(v_reuseFailAlloc_1617_, 11, v_toProcess_1600_);
v___x_1611_ = v_reuseFailAlloc_1617_;
goto v_reusejp_1610_;
}
v_reusejp_1610_:
{
lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1615_; 
v___x_1612_ = lean_st_ref_set(v___y_1587_, v___x_1611_);
v___x_1613_ = l_Lean_mkFVar(v_a_1579_);
if (v_isShared_1584_ == 0)
{
lean_ctor_set(v___x_1583_, 0, v___x_1613_);
v___x_1615_ = v___x_1583_;
goto v_reusejp_1614_;
}
else
{
lean_object* v_reuseFailAlloc_1616_; 
v_reuseFailAlloc_1616_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1616_, 0, v___x_1613_);
v___x_1615_ = v_reuseFailAlloc_1616_;
goto v_reusejp_1614_;
}
v_reusejp_1614_:
{
return v___x_1615_;
}
}
}
}
}
}
else
{
lean_object* v_a_1644_; lean_object* v___x_1646_; uint8_t v_isShared_1647_; uint8_t v_isSharedCheck_1651_; 
lean_dec(v_a_1579_);
lean_dec(v_a_1577_);
lean_dec_ref(v_type_1573_);
lean_dec_ref_known(v_e_1349_, 1);
v_a_1644_ = lean_ctor_get(v___x_1580_, 0);
v_isSharedCheck_1651_ = !lean_is_exclusive(v___x_1580_);
if (v_isSharedCheck_1651_ == 0)
{
v___x_1646_ = v___x_1580_;
v_isShared_1647_ = v_isSharedCheck_1651_;
goto v_resetjp_1645_;
}
else
{
lean_inc(v_a_1644_);
lean_dec(v___x_1580_);
v___x_1646_ = lean_box(0);
v_isShared_1647_ = v_isSharedCheck_1651_;
goto v_resetjp_1645_;
}
v_resetjp_1645_:
{
lean_object* v___x_1649_; 
if (v_isShared_1647_ == 0)
{
v___x_1649_ = v___x_1646_;
goto v_reusejp_1648_;
}
else
{
lean_object* v_reuseFailAlloc_1650_; 
v_reuseFailAlloc_1650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1650_, 0, v_a_1644_);
v___x_1649_ = v_reuseFailAlloc_1650_;
goto v_reusejp_1648_;
}
v_reusejp_1648_:
{
return v___x_1649_;
}
}
}
}
else
{
lean_object* v_a_1652_; lean_object* v___x_1654_; uint8_t v_isShared_1655_; uint8_t v_isSharedCheck_1659_; 
lean_dec(v_a_1577_);
lean_dec_ref(v_type_1573_);
lean_dec_ref_known(v_e_1349_, 1);
v_a_1652_ = lean_ctor_get(v___x_1578_, 0);
v_isSharedCheck_1659_ = !lean_is_exclusive(v___x_1578_);
if (v_isSharedCheck_1659_ == 0)
{
v___x_1654_ = v___x_1578_;
v_isShared_1655_ = v_isSharedCheck_1659_;
goto v_resetjp_1653_;
}
else
{
lean_inc(v_a_1652_);
lean_dec(v___x_1578_);
v___x_1654_ = lean_box(0);
v_isShared_1655_ = v_isSharedCheck_1659_;
goto v_resetjp_1653_;
}
v_resetjp_1653_:
{
lean_object* v___x_1657_; 
if (v_isShared_1655_ == 0)
{
v___x_1657_ = v___x_1654_;
goto v_reusejp_1656_;
}
else
{
lean_object* v_reuseFailAlloc_1658_; 
v_reuseFailAlloc_1658_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1658_, 0, v_a_1652_);
v___x_1657_ = v_reuseFailAlloc_1658_;
goto v_reusejp_1656_;
}
v_reusejp_1656_:
{
return v___x_1657_;
}
}
}
}
else
{
lean_dec_ref(v_type_1573_);
lean_dec_ref_known(v_e_1349_, 1);
return v___x_1576_;
}
}
else
{
lean_dec_ref(v_type_1573_);
lean_dec_ref_known(v_e_1349_, 1);
return v___x_1574_;
}
}
else
{
lean_object* v_a_1660_; lean_object* v___x_1662_; uint8_t v_isShared_1663_; uint8_t v_isSharedCheck_1667_; 
lean_dec_ref_known(v_e_1349_, 1);
v_a_1660_ = lean_ctor_get(v___x_1571_, 0);
v_isSharedCheck_1667_ = !lean_is_exclusive(v___x_1571_);
if (v_isSharedCheck_1667_ == 0)
{
v___x_1662_ = v___x_1571_;
v_isShared_1663_ = v_isSharedCheck_1667_;
goto v_resetjp_1661_;
}
else
{
lean_inc(v_a_1660_);
lean_dec(v___x_1571_);
v___x_1662_ = lean_box(0);
v_isShared_1663_ = v_isSharedCheck_1667_;
goto v_resetjp_1661_;
}
v_resetjp_1661_:
{
lean_object* v___x_1665_; 
if (v_isShared_1663_ == 0)
{
v___x_1665_ = v___x_1662_;
goto v_reusejp_1664_;
}
else
{
lean_object* v_reuseFailAlloc_1666_; 
v_reuseFailAlloc_1666_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1666_, 0, v_a_1660_);
v___x_1665_ = v_reuseFailAlloc_1666_;
goto v_reusejp_1664_;
}
v_reusejp_1664_:
{
return v___x_1665_;
}
}
}
}
case 1:
{
lean_object* v_fvarId_1668_; uint8_t v___x_1669_; lean_object* v___x_1670_; 
v_fvarId_1668_ = lean_ctor_get(v_e_1349_, 0);
lean_inc_n(v_fvarId_1668_, 2);
lean_dec_ref_known(v_e_1349_, 1);
v___x_1669_ = 0;
v___x_1670_ = l_Lean_FVarId_getValue_x3f___redArg(v_fvarId_1668_, v___x_1669_, v_a_1352_, v_a_1354_, v_a_1355_);
if (lean_obj_tag(v___x_1670_) == 0)
{
lean_object* v_a_1671_; uint8_t v___y_1673_; lean_object* v___y_1674_; lean_object* v___y_1675_; lean_object* v___y_1676_; lean_object* v___y_1677_; lean_object* v___y_1678_; 
v_a_1671_ = lean_ctor_get(v___x_1670_, 0);
lean_inc(v_a_1671_);
lean_dec_ref_known(v___x_1670_, 1);
if (v_a_1350_ == 1)
{
if (lean_obj_tag(v_a_1671_) == 1)
{
lean_object* v_val_1708_; lean_object* v___x_1709_; 
lean_dec(v_fvarId_1668_);
v_val_1708_ = lean_ctor_get(v_a_1671_, 0);
lean_inc(v_val_1708_);
lean_dec_ref_known(v_a_1671_, 1);
v___x_1709_ = l_Lean_Meta_Closure_preprocess(v_val_1708_, v_a_1350_, v_a_1351_, v_a_1352_, v_a_1353_, v_a_1354_, v_a_1355_);
if (lean_obj_tag(v___x_1709_) == 0)
{
lean_object* v_a_1710_; lean_object* v___x_1711_; 
v_a_1710_ = lean_ctor_get(v___x_1709_, 0);
lean_inc(v_a_1710_);
lean_dec_ref_known(v___x_1709_, 1);
v___x_1711_ = l_Lean_Meta_Closure_collectExprAux___lam__0(v_a_1710_, v_a_1350_, v_a_1351_, v_a_1352_, v_a_1353_, v_a_1354_, v_a_1355_);
return v___x_1711_;
}
else
{
return v___x_1709_;
}
}
else
{
lean_dec(v_a_1671_);
v___y_1673_ = v_a_1350_;
v___y_1674_ = v_a_1351_;
v___y_1675_ = v_a_1352_;
v___y_1676_ = v_a_1353_;
v___y_1677_ = v_a_1354_;
v___y_1678_ = v_a_1355_;
goto v___jp_1672_;
}
}
else
{
lean_dec(v_a_1671_);
v___y_1673_ = v_a_1350_;
v___y_1674_ = v_a_1351_;
v___y_1675_ = v_a_1352_;
v___y_1676_ = v_a_1353_;
v___y_1677_ = v_a_1354_;
v___y_1678_ = v_a_1355_;
goto v___jp_1672_;
}
v___jp_1672_:
{
lean_object* v___x_1679_; 
v___x_1679_ = l_Lean_mkFreshFVarId___at___00Lean_Meta_Closure_collectExprAux_spec__3(v___y_1673_, v___y_1674_, v___y_1675_, v___y_1676_, v___y_1677_, v___y_1678_);
if (lean_obj_tag(v___x_1679_) == 0)
{
lean_object* v_a_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; 
v_a_1680_ = lean_ctor_get(v___x_1679_, 0);
lean_inc_n(v_a_1680_, 2);
lean_dec_ref_known(v___x_1679_, 1);
v___x_1681_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1681_, 0, v_fvarId_1668_);
lean_ctor_set(v___x_1681_, 1, v_a_1680_);
v___x_1682_ = l_Lean_Meta_Closure_pushToProcess___redArg(v___x_1681_, v___y_1674_);
if (lean_obj_tag(v___x_1682_) == 0)
{
lean_object* v___x_1684_; uint8_t v_isShared_1685_; uint8_t v_isSharedCheck_1690_; 
v_isSharedCheck_1690_ = !lean_is_exclusive(v___x_1682_);
if (v_isSharedCheck_1690_ == 0)
{
lean_object* v_unused_1691_; 
v_unused_1691_ = lean_ctor_get(v___x_1682_, 0);
lean_dec(v_unused_1691_);
v___x_1684_ = v___x_1682_;
v_isShared_1685_ = v_isSharedCheck_1690_;
goto v_resetjp_1683_;
}
else
{
lean_dec(v___x_1682_);
v___x_1684_ = lean_box(0);
v_isShared_1685_ = v_isSharedCheck_1690_;
goto v_resetjp_1683_;
}
v_resetjp_1683_:
{
lean_object* v___x_1686_; lean_object* v___x_1688_; 
v___x_1686_ = l_Lean_mkFVar(v_a_1680_);
if (v_isShared_1685_ == 0)
{
lean_ctor_set(v___x_1684_, 0, v___x_1686_);
v___x_1688_ = v___x_1684_;
goto v_reusejp_1687_;
}
else
{
lean_object* v_reuseFailAlloc_1689_; 
v_reuseFailAlloc_1689_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1689_, 0, v___x_1686_);
v___x_1688_ = v_reuseFailAlloc_1689_;
goto v_reusejp_1687_;
}
v_reusejp_1687_:
{
return v___x_1688_;
}
}
}
else
{
lean_object* v_a_1692_; lean_object* v___x_1694_; uint8_t v_isShared_1695_; uint8_t v_isSharedCheck_1699_; 
lean_dec(v_a_1680_);
v_a_1692_ = lean_ctor_get(v___x_1682_, 0);
v_isSharedCheck_1699_ = !lean_is_exclusive(v___x_1682_);
if (v_isSharedCheck_1699_ == 0)
{
v___x_1694_ = v___x_1682_;
v_isShared_1695_ = v_isSharedCheck_1699_;
goto v_resetjp_1693_;
}
else
{
lean_inc(v_a_1692_);
lean_dec(v___x_1682_);
v___x_1694_ = lean_box(0);
v_isShared_1695_ = v_isSharedCheck_1699_;
goto v_resetjp_1693_;
}
v_resetjp_1693_:
{
lean_object* v___x_1697_; 
if (v_isShared_1695_ == 0)
{
v___x_1697_ = v___x_1694_;
goto v_reusejp_1696_;
}
else
{
lean_object* v_reuseFailAlloc_1698_; 
v_reuseFailAlloc_1698_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1698_, 0, v_a_1692_);
v___x_1697_ = v_reuseFailAlloc_1698_;
goto v_reusejp_1696_;
}
v_reusejp_1696_:
{
return v___x_1697_;
}
}
}
}
else
{
lean_object* v_a_1700_; lean_object* v___x_1702_; uint8_t v_isShared_1703_; uint8_t v_isSharedCheck_1707_; 
lean_dec(v_fvarId_1668_);
v_a_1700_ = lean_ctor_get(v___x_1679_, 0);
v_isSharedCheck_1707_ = !lean_is_exclusive(v___x_1679_);
if (v_isSharedCheck_1707_ == 0)
{
v___x_1702_ = v___x_1679_;
v_isShared_1703_ = v_isSharedCheck_1707_;
goto v_resetjp_1701_;
}
else
{
lean_inc(v_a_1700_);
lean_dec(v___x_1679_);
v___x_1702_ = lean_box(0);
v_isShared_1703_ = v_isSharedCheck_1707_;
goto v_resetjp_1701_;
}
v_resetjp_1701_:
{
lean_object* v___x_1705_; 
if (v_isShared_1703_ == 0)
{
v___x_1705_ = v___x_1702_;
goto v_reusejp_1704_;
}
else
{
lean_object* v_reuseFailAlloc_1706_; 
v_reuseFailAlloc_1706_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1706_, 0, v_a_1700_);
v___x_1705_ = v_reuseFailAlloc_1706_;
goto v_reusejp_1704_;
}
v_reusejp_1704_:
{
return v___x_1705_;
}
}
}
}
}
else
{
lean_object* v_a_1712_; lean_object* v___x_1714_; uint8_t v_isShared_1715_; uint8_t v_isSharedCheck_1719_; 
lean_dec(v_fvarId_1668_);
v_a_1712_ = lean_ctor_get(v___x_1670_, 0);
v_isSharedCheck_1719_ = !lean_is_exclusive(v___x_1670_);
if (v_isSharedCheck_1719_ == 0)
{
v___x_1714_ = v___x_1670_;
v_isShared_1715_ = v_isSharedCheck_1719_;
goto v_resetjp_1713_;
}
else
{
lean_inc(v_a_1712_);
lean_dec(v___x_1670_);
v___x_1714_ = lean_box(0);
v_isShared_1715_ = v_isSharedCheck_1719_;
goto v_resetjp_1713_;
}
v_resetjp_1713_:
{
lean_object* v___x_1717_; 
if (v_isShared_1715_ == 0)
{
v___x_1717_ = v___x_1714_;
goto v_reusejp_1716_;
}
else
{
lean_object* v_reuseFailAlloc_1718_; 
v_reuseFailAlloc_1718_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1718_, 0, v_a_1712_);
v___x_1717_ = v_reuseFailAlloc_1718_;
goto v_reusejp_1716_;
}
v_reusejp_1716_:
{
return v___x_1717_;
}
}
}
}
default: 
{
lean_object* v___x_1720_; 
v___x_1720_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1720_, 0, v_e_1349_);
return v___x_1720_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectExprAux___lam__0(lean_object* v_e_1721_, uint8_t v___y_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_){
_start:
{
uint8_t v___y_1773_; uint8_t v___x_1777_; uint8_t v___x_1778_; 
v___x_1777_ = l_Lean_Expr_hasLevelParam(v_e_1721_);
v___x_1778_ = lean_bool_not(v___x_1777_);
if (v___x_1778_ == 0)
{
v___y_1773_ = v___x_1778_;
goto v___jp_1772_;
}
else
{
uint8_t v___x_1779_; uint8_t v___x_1780_; 
v___x_1779_ = l_Lean_Expr_hasFVar(v_e_1721_);
v___x_1780_ = lean_bool_not(v___x_1779_);
v___y_1773_ = v___x_1780_;
goto v___jp_1772_;
}
v___jp_1729_:
{
lean_object* v___x_1730_; lean_object* v_visitedExpr_1731_; lean_object* v___x_1732_; 
v___x_1730_ = lean_st_ref_get(v___y_1723_);
v_visitedExpr_1731_ = lean_ctor_get(v___x_1730_, 1);
lean_inc_ref(v_visitedExpr_1731_);
lean_dec(v___x_1730_);
v___x_1732_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0___redArg(v_visitedExpr_1731_, v_e_1721_);
lean_dec_ref(v_visitedExpr_1731_);
if (lean_obj_tag(v___x_1732_) == 0)
{
lean_object* v___x_1733_; 
lean_inc_ref(v_e_1721_);
v___x_1733_ = l_Lean_Meta_Closure_collectExprAux(v_e_1721_, v___y_1722_, v___y_1723_, v___y_1724_, v___y_1725_, v___y_1726_, v___y_1727_);
if (lean_obj_tag(v___x_1733_) == 0)
{
lean_object* v_a_1734_; lean_object* v___x_1736_; uint8_t v_isShared_1737_; uint8_t v_isSharedCheck_1763_; 
v_a_1734_ = lean_ctor_get(v___x_1733_, 0);
v_isSharedCheck_1763_ = !lean_is_exclusive(v___x_1733_);
if (v_isSharedCheck_1763_ == 0)
{
v___x_1736_ = v___x_1733_;
v_isShared_1737_ = v_isSharedCheck_1763_;
goto v_resetjp_1735_;
}
else
{
lean_inc(v_a_1734_);
lean_dec(v___x_1733_);
v___x_1736_ = lean_box(0);
v_isShared_1737_ = v_isSharedCheck_1763_;
goto v_resetjp_1735_;
}
v_resetjp_1735_:
{
lean_object* v___x_1738_; lean_object* v_visitedLevel_1739_; lean_object* v_visitedExpr_1740_; lean_object* v_levelParams_1741_; lean_object* v_nextLevelIdx_1742_; lean_object* v_levelArgs_1743_; lean_object* v_newLocalDecls_1744_; lean_object* v_newLocalDeclsForMVars_1745_; lean_object* v_newLetDecls_1746_; lean_object* v_nextExprIdx_1747_; lean_object* v_exprMVarArgs_1748_; lean_object* v_exprFVarArgs_1749_; lean_object* v_toProcess_1750_; lean_object* v___x_1752_; uint8_t v_isShared_1753_; uint8_t v_isSharedCheck_1762_; 
v___x_1738_ = lean_st_ref_take(v___y_1723_);
v_visitedLevel_1739_ = lean_ctor_get(v___x_1738_, 0);
v_visitedExpr_1740_ = lean_ctor_get(v___x_1738_, 1);
v_levelParams_1741_ = lean_ctor_get(v___x_1738_, 2);
v_nextLevelIdx_1742_ = lean_ctor_get(v___x_1738_, 3);
v_levelArgs_1743_ = lean_ctor_get(v___x_1738_, 4);
v_newLocalDecls_1744_ = lean_ctor_get(v___x_1738_, 5);
v_newLocalDeclsForMVars_1745_ = lean_ctor_get(v___x_1738_, 6);
v_newLetDecls_1746_ = lean_ctor_get(v___x_1738_, 7);
v_nextExprIdx_1747_ = lean_ctor_get(v___x_1738_, 8);
v_exprMVarArgs_1748_ = lean_ctor_get(v___x_1738_, 9);
v_exprFVarArgs_1749_ = lean_ctor_get(v___x_1738_, 10);
v_toProcess_1750_ = lean_ctor_get(v___x_1738_, 11);
v_isSharedCheck_1762_ = !lean_is_exclusive(v___x_1738_);
if (v_isSharedCheck_1762_ == 0)
{
v___x_1752_ = v___x_1738_;
v_isShared_1753_ = v_isSharedCheck_1762_;
goto v_resetjp_1751_;
}
else
{
lean_inc(v_toProcess_1750_);
lean_inc(v_exprFVarArgs_1749_);
lean_inc(v_exprMVarArgs_1748_);
lean_inc(v_nextExprIdx_1747_);
lean_inc(v_newLetDecls_1746_);
lean_inc(v_newLocalDeclsForMVars_1745_);
lean_inc(v_newLocalDecls_1744_);
lean_inc(v_levelArgs_1743_);
lean_inc(v_nextLevelIdx_1742_);
lean_inc(v_levelParams_1741_);
lean_inc(v_visitedExpr_1740_);
lean_inc(v_visitedLevel_1739_);
lean_dec(v___x_1738_);
v___x_1752_ = lean_box(0);
v_isShared_1753_ = v_isSharedCheck_1762_;
goto v_resetjp_1751_;
}
v_resetjp_1751_:
{
lean_object* v___x_1754_; lean_object* v___x_1756_; 
lean_inc(v_a_1734_);
v___x_1754_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1___redArg(v_visitedExpr_1740_, v_e_1721_, v_a_1734_);
if (v_isShared_1753_ == 0)
{
lean_ctor_set(v___x_1752_, 1, v___x_1754_);
v___x_1756_ = v___x_1752_;
goto v_reusejp_1755_;
}
else
{
lean_object* v_reuseFailAlloc_1761_; 
v_reuseFailAlloc_1761_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_1761_, 0, v_visitedLevel_1739_);
lean_ctor_set(v_reuseFailAlloc_1761_, 1, v___x_1754_);
lean_ctor_set(v_reuseFailAlloc_1761_, 2, v_levelParams_1741_);
lean_ctor_set(v_reuseFailAlloc_1761_, 3, v_nextLevelIdx_1742_);
lean_ctor_set(v_reuseFailAlloc_1761_, 4, v_levelArgs_1743_);
lean_ctor_set(v_reuseFailAlloc_1761_, 5, v_newLocalDecls_1744_);
lean_ctor_set(v_reuseFailAlloc_1761_, 6, v_newLocalDeclsForMVars_1745_);
lean_ctor_set(v_reuseFailAlloc_1761_, 7, v_newLetDecls_1746_);
lean_ctor_set(v_reuseFailAlloc_1761_, 8, v_nextExprIdx_1747_);
lean_ctor_set(v_reuseFailAlloc_1761_, 9, v_exprMVarArgs_1748_);
lean_ctor_set(v_reuseFailAlloc_1761_, 10, v_exprFVarArgs_1749_);
lean_ctor_set(v_reuseFailAlloc_1761_, 11, v_toProcess_1750_);
v___x_1756_ = v_reuseFailAlloc_1761_;
goto v_reusejp_1755_;
}
v_reusejp_1755_:
{
lean_object* v___x_1757_; lean_object* v___x_1759_; 
v___x_1757_ = lean_st_ref_set(v___y_1723_, v___x_1756_);
if (v_isShared_1737_ == 0)
{
v___x_1759_ = v___x_1736_;
goto v_reusejp_1758_;
}
else
{
lean_object* v_reuseFailAlloc_1760_; 
v_reuseFailAlloc_1760_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1760_, 0, v_a_1734_);
v___x_1759_ = v_reuseFailAlloc_1760_;
goto v_reusejp_1758_;
}
v_reusejp_1758_:
{
return v___x_1759_;
}
}
}
}
}
else
{
lean_dec_ref(v_e_1721_);
return v___x_1733_;
}
}
else
{
lean_object* v_val_1764_; lean_object* v___x_1766_; uint8_t v_isShared_1767_; uint8_t v_isSharedCheck_1771_; 
lean_dec_ref(v_e_1721_);
v_val_1764_ = lean_ctor_get(v___x_1732_, 0);
v_isSharedCheck_1771_ = !lean_is_exclusive(v___x_1732_);
if (v_isSharedCheck_1771_ == 0)
{
v___x_1766_ = v___x_1732_;
v_isShared_1767_ = v_isSharedCheck_1771_;
goto v_resetjp_1765_;
}
else
{
lean_inc(v_val_1764_);
lean_dec(v___x_1732_);
v___x_1766_ = lean_box(0);
v_isShared_1767_ = v_isSharedCheck_1771_;
goto v_resetjp_1765_;
}
v_resetjp_1765_:
{
lean_object* v___x_1769_; 
if (v_isShared_1767_ == 0)
{
lean_ctor_set_tag(v___x_1766_, 0);
v___x_1769_ = v___x_1766_;
goto v_reusejp_1768_;
}
else
{
lean_object* v_reuseFailAlloc_1770_; 
v_reuseFailAlloc_1770_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1770_, 0, v_val_1764_);
v___x_1769_ = v_reuseFailAlloc_1770_;
goto v_reusejp_1768_;
}
v_reusejp_1768_:
{
return v___x_1769_;
}
}
}
}
v___jp_1772_:
{
if (v___y_1773_ == 0)
{
goto v___jp_1729_;
}
else
{
uint8_t v___x_1774_; uint8_t v___x_1775_; 
v___x_1774_ = l_Lean_Expr_hasMVar(v_e_1721_);
v___x_1775_ = lean_bool_not(v___x_1774_);
if (v___x_1775_ == 0)
{
goto v___jp_1729_;
}
else
{
lean_object* v___x_1776_; 
v___x_1776_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1776_, 0, v_e_1721_);
return v___x_1776_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectExprAux___lam__0___boxed(lean_object* v_e_1781_, lean_object* v___y_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_){
_start:
{
uint8_t v___y_18426__boxed_1789_; lean_object* v_res_1790_; 
v___y_18426__boxed_1789_ = lean_unbox(v___y_1782_);
v_res_1790_ = l_Lean_Meta_Closure_collectExprAux___lam__0(v_e_1781_, v___y_18426__boxed_1789_, v___y_1783_, v___y_1784_, v___y_1785_, v___y_1786_, v___y_1787_);
lean_dec(v___y_1787_);
lean_dec_ref(v___y_1786_);
lean_dec(v___y_1785_);
lean_dec_ref(v___y_1784_);
lean_dec(v___y_1783_);
return v_res_1790_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectExprAux___boxed(lean_object* v_e_1791_, lean_object* v_a_1792_, lean_object* v_a_1793_, lean_object* v_a_1794_, lean_object* v_a_1795_, lean_object* v_a_1796_, lean_object* v_a_1797_, lean_object* v_a_1798_){
_start:
{
uint8_t v_a_boxed_1799_; lean_object* v_res_1800_; 
v_a_boxed_1799_ = lean_unbox(v_a_1792_);
v_res_1800_ = l_Lean_Meta_Closure_collectExprAux(v_e_1791_, v_a_boxed_1799_, v_a_1793_, v_a_1794_, v_a_1795_, v_a_1796_, v_a_1797_);
lean_dec(v_a_1797_);
lean_dec_ref(v_a_1796_);
lean_dec(v_a_1795_);
lean_dec_ref(v_a_1794_);
lean_dec(v_a_1793_);
return v_res_1800_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0(lean_object* v_00_u03b2_1801_, lean_object* v_m_1802_, lean_object* v_a_1803_){
_start:
{
lean_object* v___x_1804_; 
v___x_1804_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0___redArg(v_m_1802_, v_a_1803_);
return v___x_1804_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0___boxed(lean_object* v_00_u03b2_1805_, lean_object* v_m_1806_, lean_object* v_a_1807_){
_start:
{
lean_object* v_res_1808_; 
v_res_1808_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0(v_00_u03b2_1805_, v_m_1806_, v_a_1807_);
lean_dec_ref(v_a_1807_);
lean_dec_ref(v_m_1806_);
return v_res_1808_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1(lean_object* v_00_u03b2_1809_, lean_object* v_m_1810_, lean_object* v_a_1811_, lean_object* v_b_1812_){
_start:
{
lean_object* v___x_1813_; 
v___x_1813_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1___redArg(v_m_1810_, v_a_1811_, v_b_1812_);
return v___x_1813_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Closure_collectExprAux_spec__2(lean_object* v_x_1814_, lean_object* v_x_1815_, uint8_t v___y_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_){
_start:
{
lean_object* v___x_1823_; 
v___x_1823_ = l_List_mapM_loop___at___00Lean_Meta_Closure_collectExprAux_spec__2___redArg(v_x_1814_, v_x_1815_, v___y_1817_);
return v___x_1823_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Closure_collectExprAux_spec__2___boxed(lean_object* v_x_1824_, lean_object* v_x_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_){
_start:
{
uint8_t v___y_19252__boxed_1833_; lean_object* v_res_1834_; 
v___y_19252__boxed_1833_ = lean_unbox(v___y_1826_);
v_res_1834_ = l_List_mapM_loop___at___00Lean_Meta_Closure_collectExprAux_spec__2(v_x_1824_, v_x_1825_, v___y_19252__boxed_1833_, v___y_1827_, v___y_1828_, v___y_1829_, v___y_1830_, v___y_1831_);
lean_dec(v___y_1831_);
lean_dec_ref(v___y_1830_);
lean_dec(v___y_1829_);
lean_dec_ref(v___y_1828_);
lean_dec(v___y_1827_);
return v_res_1834_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Closure_collectExprAux_spec__3_spec__7(uint8_t v___y_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_){
_start:
{
lean_object* v___x_1842_; 
v___x_1842_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Closure_collectExprAux_spec__3_spec__7___redArg(v___y_1840_);
return v___x_1842_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Closure_collectExprAux_spec__3_spec__7___boxed(lean_object* v___y_1843_, lean_object* v___y_1844_, lean_object* v___y_1845_, lean_object* v___y_1846_, lean_object* v___y_1847_, lean_object* v___y_1848_, lean_object* v___y_1849_){
_start:
{
uint8_t v___y_19279__boxed_1850_; lean_object* v_res_1851_; 
v___y_19279__boxed_1850_ = lean_unbox(v___y_1843_);
v_res_1851_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Closure_collectExprAux_spec__3_spec__7(v___y_19279__boxed_1850_, v___y_1844_, v___y_1845_, v___y_1846_, v___y_1847_, v___y_1848_);
lean_dec(v___y_1848_);
lean_dec_ref(v___y_1847_);
lean_dec(v___y_1846_);
lean_dec_ref(v___y_1845_);
lean_dec(v___y_1844_);
return v_res_1851_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0_spec__0(lean_object* v_00_u03b2_1852_, lean_object* v_a_1853_, lean_object* v_x_1854_){
_start:
{
lean_object* v___x_1855_; 
v___x_1855_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0_spec__0___redArg(v_a_1853_, v_x_1854_);
return v___x_1855_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1856_, lean_object* v_a_1857_, lean_object* v_x_1858_){
_start:
{
lean_object* v_res_1859_; 
v_res_1859_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0_spec__0(v_00_u03b2_1856_, v_a_1857_, v_x_1858_);
lean_dec(v_x_1858_);
lean_dec_ref(v_a_1857_);
return v_res_1859_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__2(lean_object* v_00_u03b2_1860_, lean_object* v_a_1861_, lean_object* v_x_1862_){
_start:
{
uint8_t v___x_1863_; 
v___x_1863_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__2___redArg(v_a_1861_, v_x_1862_);
return v___x_1863_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1864_, lean_object* v_a_1865_, lean_object* v_x_1866_){
_start:
{
uint8_t v_res_1867_; lean_object* v_r_1868_; 
v_res_1867_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__2(v_00_u03b2_1864_, v_a_1865_, v_x_1866_);
lean_dec(v_x_1866_);
lean_dec_ref(v_a_1865_);
v_r_1868_ = lean_box(v_res_1867_);
return v_r_1868_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__3(lean_object* v_00_u03b2_1869_, lean_object* v_data_1870_){
_start:
{
lean_object* v___x_1871_; 
v___x_1871_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__3___redArg(v_data_1870_);
return v___x_1871_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__4(lean_object* v_00_u03b2_1872_, lean_object* v_a_1873_, lean_object* v_b_1874_, lean_object* v_x_1875_){
_start:
{
lean_object* v___x_1876_; 
v___x_1876_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__4___redArg(v_a_1873_, v_b_1874_, v_x_1875_);
return v___x_1876_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__3_spec__6(lean_object* v_00_u03b2_1877_, lean_object* v_i_1878_, lean_object* v_source_1879_, lean_object* v_target_1880_){
_start:
{
lean_object* v___x_1881_; 
v___x_1881_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__3_spec__6___redArg(v_i_1878_, v_source_1879_, v_target_1880_);
return v___x_1881_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__3_spec__6_spec__10(lean_object* v_00_u03b2_1882_, lean_object* v_x_1883_, lean_object* v_x_1884_){
_start:
{
lean_object* v___x_1885_; 
v___x_1885_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__3_spec__6_spec__10___redArg(v_x_1883_, v_x_1884_);
return v___x_1885_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectExpr(lean_object* v_e_1886_, uint8_t v_a_1887_, lean_object* v_a_1888_, lean_object* v_a_1889_, lean_object* v_a_1890_, lean_object* v_a_1891_, lean_object* v_a_1892_){
_start:
{
lean_object* v___x_1894_; 
v___x_1894_ = l_Lean_Meta_Closure_preprocess(v_e_1886_, v_a_1887_, v_a_1888_, v_a_1889_, v_a_1890_, v_a_1891_, v_a_1892_);
if (lean_obj_tag(v___x_1894_) == 0)
{
lean_object* v_a_1895_; uint8_t v___y_1940_; uint8_t v___x_1943_; uint8_t v___x_1944_; 
v_a_1895_ = lean_ctor_get(v___x_1894_, 0);
lean_inc(v_a_1895_);
v___x_1943_ = l_Lean_Expr_hasLevelParam(v_a_1895_);
v___x_1944_ = lean_bool_not(v___x_1943_);
if (v___x_1944_ == 0)
{
v___y_1940_ = v___x_1944_;
goto v___jp_1939_;
}
else
{
uint8_t v___x_1945_; uint8_t v___x_1946_; 
v___x_1945_ = l_Lean_Expr_hasFVar(v_a_1895_);
v___x_1946_ = lean_bool_not(v___x_1945_);
v___y_1940_ = v___x_1946_;
goto v___jp_1939_;
}
v___jp_1896_:
{
lean_object* v___x_1897_; lean_object* v_visitedExpr_1898_; lean_object* v___x_1899_; 
v___x_1897_ = lean_st_ref_get(v_a_1888_);
v_visitedExpr_1898_ = lean_ctor_get(v___x_1897_, 1);
lean_inc_ref(v_visitedExpr_1898_);
lean_dec(v___x_1897_);
v___x_1899_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0___redArg(v_visitedExpr_1898_, v_a_1895_);
lean_dec_ref(v_visitedExpr_1898_);
if (lean_obj_tag(v___x_1899_) == 0)
{
lean_object* v___x_1900_; 
lean_inc(v_a_1895_);
v___x_1900_ = l_Lean_Meta_Closure_collectExprAux(v_a_1895_, v_a_1887_, v_a_1888_, v_a_1889_, v_a_1890_, v_a_1891_, v_a_1892_);
if (lean_obj_tag(v___x_1900_) == 0)
{
lean_object* v_a_1901_; lean_object* v___x_1903_; uint8_t v_isShared_1904_; uint8_t v_isSharedCheck_1930_; 
v_a_1901_ = lean_ctor_get(v___x_1900_, 0);
v_isSharedCheck_1930_ = !lean_is_exclusive(v___x_1900_);
if (v_isSharedCheck_1930_ == 0)
{
v___x_1903_ = v___x_1900_;
v_isShared_1904_ = v_isSharedCheck_1930_;
goto v_resetjp_1902_;
}
else
{
lean_inc(v_a_1901_);
lean_dec(v___x_1900_);
v___x_1903_ = lean_box(0);
v_isShared_1904_ = v_isSharedCheck_1930_;
goto v_resetjp_1902_;
}
v_resetjp_1902_:
{
lean_object* v___x_1905_; lean_object* v_visitedLevel_1906_; lean_object* v_visitedExpr_1907_; lean_object* v_levelParams_1908_; lean_object* v_nextLevelIdx_1909_; lean_object* v_levelArgs_1910_; lean_object* v_newLocalDecls_1911_; lean_object* v_newLocalDeclsForMVars_1912_; lean_object* v_newLetDecls_1913_; lean_object* v_nextExprIdx_1914_; lean_object* v_exprMVarArgs_1915_; lean_object* v_exprFVarArgs_1916_; lean_object* v_toProcess_1917_; lean_object* v___x_1919_; uint8_t v_isShared_1920_; uint8_t v_isSharedCheck_1929_; 
v___x_1905_ = lean_st_ref_take(v_a_1888_);
v_visitedLevel_1906_ = lean_ctor_get(v___x_1905_, 0);
v_visitedExpr_1907_ = lean_ctor_get(v___x_1905_, 1);
v_levelParams_1908_ = lean_ctor_get(v___x_1905_, 2);
v_nextLevelIdx_1909_ = lean_ctor_get(v___x_1905_, 3);
v_levelArgs_1910_ = lean_ctor_get(v___x_1905_, 4);
v_newLocalDecls_1911_ = lean_ctor_get(v___x_1905_, 5);
v_newLocalDeclsForMVars_1912_ = lean_ctor_get(v___x_1905_, 6);
v_newLetDecls_1913_ = lean_ctor_get(v___x_1905_, 7);
v_nextExprIdx_1914_ = lean_ctor_get(v___x_1905_, 8);
v_exprMVarArgs_1915_ = lean_ctor_get(v___x_1905_, 9);
v_exprFVarArgs_1916_ = lean_ctor_get(v___x_1905_, 10);
v_toProcess_1917_ = lean_ctor_get(v___x_1905_, 11);
v_isSharedCheck_1929_ = !lean_is_exclusive(v___x_1905_);
if (v_isSharedCheck_1929_ == 0)
{
v___x_1919_ = v___x_1905_;
v_isShared_1920_ = v_isSharedCheck_1929_;
goto v_resetjp_1918_;
}
else
{
lean_inc(v_toProcess_1917_);
lean_inc(v_exprFVarArgs_1916_);
lean_inc(v_exprMVarArgs_1915_);
lean_inc(v_nextExprIdx_1914_);
lean_inc(v_newLetDecls_1913_);
lean_inc(v_newLocalDeclsForMVars_1912_);
lean_inc(v_newLocalDecls_1911_);
lean_inc(v_levelArgs_1910_);
lean_inc(v_nextLevelIdx_1909_);
lean_inc(v_levelParams_1908_);
lean_inc(v_visitedExpr_1907_);
lean_inc(v_visitedLevel_1906_);
lean_dec(v___x_1905_);
v___x_1919_ = lean_box(0);
v_isShared_1920_ = v_isSharedCheck_1929_;
goto v_resetjp_1918_;
}
v_resetjp_1918_:
{
lean_object* v___x_1921_; lean_object* v___x_1923_; 
lean_inc(v_a_1901_);
v___x_1921_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1___redArg(v_visitedExpr_1907_, v_a_1895_, v_a_1901_);
if (v_isShared_1920_ == 0)
{
lean_ctor_set(v___x_1919_, 1, v___x_1921_);
v___x_1923_ = v___x_1919_;
goto v_reusejp_1922_;
}
else
{
lean_object* v_reuseFailAlloc_1928_; 
v_reuseFailAlloc_1928_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_1928_, 0, v_visitedLevel_1906_);
lean_ctor_set(v_reuseFailAlloc_1928_, 1, v___x_1921_);
lean_ctor_set(v_reuseFailAlloc_1928_, 2, v_levelParams_1908_);
lean_ctor_set(v_reuseFailAlloc_1928_, 3, v_nextLevelIdx_1909_);
lean_ctor_set(v_reuseFailAlloc_1928_, 4, v_levelArgs_1910_);
lean_ctor_set(v_reuseFailAlloc_1928_, 5, v_newLocalDecls_1911_);
lean_ctor_set(v_reuseFailAlloc_1928_, 6, v_newLocalDeclsForMVars_1912_);
lean_ctor_set(v_reuseFailAlloc_1928_, 7, v_newLetDecls_1913_);
lean_ctor_set(v_reuseFailAlloc_1928_, 8, v_nextExprIdx_1914_);
lean_ctor_set(v_reuseFailAlloc_1928_, 9, v_exprMVarArgs_1915_);
lean_ctor_set(v_reuseFailAlloc_1928_, 10, v_exprFVarArgs_1916_);
lean_ctor_set(v_reuseFailAlloc_1928_, 11, v_toProcess_1917_);
v___x_1923_ = v_reuseFailAlloc_1928_;
goto v_reusejp_1922_;
}
v_reusejp_1922_:
{
lean_object* v___x_1924_; lean_object* v___x_1926_; 
v___x_1924_ = lean_st_ref_set(v_a_1888_, v___x_1923_);
if (v_isShared_1904_ == 0)
{
v___x_1926_ = v___x_1903_;
goto v_reusejp_1925_;
}
else
{
lean_object* v_reuseFailAlloc_1927_; 
v_reuseFailAlloc_1927_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1927_, 0, v_a_1901_);
v___x_1926_ = v_reuseFailAlloc_1927_;
goto v_reusejp_1925_;
}
v_reusejp_1925_:
{
return v___x_1926_;
}
}
}
}
}
else
{
lean_dec(v_a_1895_);
return v___x_1900_;
}
}
else
{
lean_object* v_val_1931_; lean_object* v___x_1933_; uint8_t v_isShared_1934_; uint8_t v_isSharedCheck_1938_; 
lean_dec(v_a_1895_);
v_val_1931_ = lean_ctor_get(v___x_1899_, 0);
v_isSharedCheck_1938_ = !lean_is_exclusive(v___x_1899_);
if (v_isSharedCheck_1938_ == 0)
{
v___x_1933_ = v___x_1899_;
v_isShared_1934_ = v_isSharedCheck_1938_;
goto v_resetjp_1932_;
}
else
{
lean_inc(v_val_1931_);
lean_dec(v___x_1899_);
v___x_1933_ = lean_box(0);
v_isShared_1934_ = v_isSharedCheck_1938_;
goto v_resetjp_1932_;
}
v_resetjp_1932_:
{
lean_object* v___x_1936_; 
if (v_isShared_1934_ == 0)
{
lean_ctor_set_tag(v___x_1933_, 0);
v___x_1936_ = v___x_1933_;
goto v_reusejp_1935_;
}
else
{
lean_object* v_reuseFailAlloc_1937_; 
v_reuseFailAlloc_1937_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1937_, 0, v_val_1931_);
v___x_1936_ = v_reuseFailAlloc_1937_;
goto v_reusejp_1935_;
}
v_reusejp_1935_:
{
return v___x_1936_;
}
}
}
}
v___jp_1939_:
{
if (v___y_1940_ == 0)
{
lean_dec_ref_known(v___x_1894_, 1);
goto v___jp_1896_;
}
else
{
uint8_t v___x_1941_; uint8_t v___x_1942_; 
v___x_1941_ = l_Lean_Expr_hasMVar(v_a_1895_);
v___x_1942_ = lean_bool_not(v___x_1941_);
if (v___x_1942_ == 0)
{
lean_dec_ref_known(v___x_1894_, 1);
goto v___jp_1896_;
}
else
{
lean_dec(v_a_1895_);
return v___x_1894_;
}
}
}
}
else
{
return v___x_1894_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectExpr___boxed(lean_object* v_e_1947_, lean_object* v_a_1948_, lean_object* v_a_1949_, lean_object* v_a_1950_, lean_object* v_a_1951_, lean_object* v_a_1952_, lean_object* v_a_1953_, lean_object* v_a_1954_){
_start:
{
uint8_t v_a_boxed_1955_; lean_object* v_res_1956_; 
v_a_boxed_1955_ = lean_unbox(v_a_1948_);
v_res_1956_ = l_Lean_Meta_Closure_collectExpr(v_e_1947_, v_a_boxed_1955_, v_a_1949_, v_a_1950_, v_a_1951_, v_a_1952_, v_a_1953_);
lean_dec(v_a_1953_);
lean_dec_ref(v_a_1952_);
lean_dec(v_a_1951_);
lean_dec_ref(v_a_1950_);
lean_dec(v_a_1949_);
return v_res_1956_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pickNextToProcessAux(lean_object* v_lctx_1957_, lean_object* v_i_1958_, lean_object* v_toProcess_1959_, lean_object* v_elem_1960_){
_start:
{
lean_object* v___x_1961_; uint8_t v___x_1962_; 
v___x_1961_ = lean_array_get_size(v_toProcess_1959_);
v___x_1962_ = lean_nat_dec_lt(v_i_1958_, v___x_1961_);
if (v___x_1962_ == 0)
{
lean_object* v___x_1963_; 
lean_dec(v_i_1958_);
lean_dec_ref(v_lctx_1957_);
v___x_1963_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1963_, 0, v_elem_1960_);
lean_ctor_set(v___x_1963_, 1, v_toProcess_1959_);
return v___x_1963_;
}
else
{
lean_object* v_fvarId_1964_; lean_object* v_elem_x27_1965_; lean_object* v_fvarId_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; lean_object* v___x_1970_; uint8_t v___x_1971_; 
v_fvarId_1964_ = lean_ctor_get(v_elem_1960_, 0);
v_elem_x27_1965_ = lean_array_fget_borrowed(v_toProcess_1959_, v_i_1958_);
v_fvarId_1966_ = lean_ctor_get(v_elem_x27_1965_, 0);
lean_inc(v_fvarId_1964_);
lean_inc_ref_n(v_lctx_1957_, 2);
v___x_1967_ = l_Lean_LocalContext_get_x21(v_lctx_1957_, v_fvarId_1964_);
v___x_1968_ = l_Lean_LocalDecl_index(v___x_1967_);
lean_dec_ref(v___x_1967_);
lean_inc(v_fvarId_1966_);
v___x_1969_ = l_Lean_LocalContext_get_x21(v_lctx_1957_, v_fvarId_1966_);
v___x_1970_ = l_Lean_LocalDecl_index(v___x_1969_);
lean_dec_ref(v___x_1969_);
v___x_1971_ = lean_nat_dec_lt(v___x_1968_, v___x_1970_);
lean_dec(v___x_1970_);
lean_dec(v___x_1968_);
if (v___x_1971_ == 0)
{
lean_object* v___x_1972_; lean_object* v___x_1973_; 
v___x_1972_ = lean_unsigned_to_nat(1u);
v___x_1973_ = lean_nat_add(v_i_1958_, v___x_1972_);
lean_dec(v_i_1958_);
v_i_1958_ = v___x_1973_;
goto _start;
}
else
{
lean_object* v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; 
lean_inc(v_elem_x27_1965_);
v___x_1975_ = lean_unsigned_to_nat(1u);
v___x_1976_ = lean_nat_add(v_i_1958_, v___x_1975_);
v___x_1977_ = lean_array_fset(v_toProcess_1959_, v_i_1958_, v_elem_1960_);
lean_dec(v_i_1958_);
v_i_1958_ = v___x_1976_;
v_toProcess_1959_ = v___x_1977_;
v_elem_1960_ = v_elem_x27_1965_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pickNextToProcess_x3f___redArg(lean_object* v_a_1979_, lean_object* v_a_1980_){
_start:
{
lean_object* v___x_1982_; lean_object* v_toProcess_1983_; lean_object* v___x_1984_; lean_object* v___x_1985_; uint8_t v___x_1986_; 
v___x_1982_ = lean_st_ref_get(v_a_1979_);
v_toProcess_1983_ = lean_ctor_get(v___x_1982_, 11);
lean_inc_ref(v_toProcess_1983_);
lean_dec(v___x_1982_);
v___x_1984_ = lean_array_get_size(v_toProcess_1983_);
lean_dec_ref(v_toProcess_1983_);
v___x_1985_ = lean_unsigned_to_nat(0u);
v___x_1986_ = lean_nat_dec_eq(v___x_1984_, v___x_1985_);
if (v___x_1986_ == 0)
{
lean_object* v___x_1987_; lean_object* v_lctx_1988_; lean_object* v_visitedLevel_1989_; lean_object* v_visitedExpr_1990_; lean_object* v_levelParams_1991_; lean_object* v_nextLevelIdx_1992_; lean_object* v_levelArgs_1993_; lean_object* v_newLocalDecls_1994_; lean_object* v_newLocalDeclsForMVars_1995_; lean_object* v_newLetDecls_1996_; lean_object* v_nextExprIdx_1997_; lean_object* v_exprMVarArgs_1998_; lean_object* v_exprFVarArgs_1999_; lean_object* v_toProcess_2000_; lean_object* v___x_2002_; uint8_t v_isShared_2003_; uint8_t v_isSharedCheck_2019_; 
v___x_1987_ = lean_st_ref_take(v_a_1979_);
v_lctx_1988_ = lean_ctor_get(v_a_1980_, 2);
v_visitedLevel_1989_ = lean_ctor_get(v___x_1987_, 0);
v_visitedExpr_1990_ = lean_ctor_get(v___x_1987_, 1);
v_levelParams_1991_ = lean_ctor_get(v___x_1987_, 2);
v_nextLevelIdx_1992_ = lean_ctor_get(v___x_1987_, 3);
v_levelArgs_1993_ = lean_ctor_get(v___x_1987_, 4);
v_newLocalDecls_1994_ = lean_ctor_get(v___x_1987_, 5);
v_newLocalDeclsForMVars_1995_ = lean_ctor_get(v___x_1987_, 6);
v_newLetDecls_1996_ = lean_ctor_get(v___x_1987_, 7);
v_nextExprIdx_1997_ = lean_ctor_get(v___x_1987_, 8);
v_exprMVarArgs_1998_ = lean_ctor_get(v___x_1987_, 9);
v_exprFVarArgs_1999_ = lean_ctor_get(v___x_1987_, 10);
v_toProcess_2000_ = lean_ctor_get(v___x_1987_, 11);
v_isSharedCheck_2019_ = !lean_is_exclusive(v___x_1987_);
if (v_isSharedCheck_2019_ == 0)
{
v___x_2002_ = v___x_1987_;
v_isShared_2003_ = v_isSharedCheck_2019_;
goto v_resetjp_2001_;
}
else
{
lean_inc(v_toProcess_2000_);
lean_inc(v_exprFVarArgs_1999_);
lean_inc(v_exprMVarArgs_1998_);
lean_inc(v_nextExprIdx_1997_);
lean_inc(v_newLetDecls_1996_);
lean_inc(v_newLocalDeclsForMVars_1995_);
lean_inc(v_newLocalDecls_1994_);
lean_inc(v_levelArgs_1993_);
lean_inc(v_nextLevelIdx_1992_);
lean_inc(v_levelParams_1991_);
lean_inc(v_visitedExpr_1990_);
lean_inc(v_visitedLevel_1989_);
lean_dec(v___x_1987_);
v___x_2002_ = lean_box(0);
v_isShared_2003_ = v_isSharedCheck_2019_;
goto v_resetjp_2001_;
}
v_resetjp_2001_:
{
lean_object* v___x_2004_; lean_object* v___x_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; lean_object* v_fst_2011_; lean_object* v_snd_2012_; lean_object* v___x_2014_; 
v___x_2004_ = ((lean_object*)(l_Lean_Meta_Closure_instInhabitedToProcessElement_default));
v___x_2005_ = lean_array_get_size(v_toProcess_2000_);
v___x_2006_ = lean_unsigned_to_nat(1u);
v___x_2007_ = lean_nat_sub(v___x_2005_, v___x_2006_);
v___x_2008_ = lean_array_get(v___x_2004_, v_toProcess_2000_, v___x_2007_);
lean_dec(v___x_2007_);
v___x_2009_ = lean_array_pop(v_toProcess_2000_);
lean_inc_ref(v_lctx_1988_);
v___x_2010_ = l_Lean_Meta_Closure_pickNextToProcessAux(v_lctx_1988_, v___x_1985_, v___x_2009_, v___x_2008_);
v_fst_2011_ = lean_ctor_get(v___x_2010_, 0);
lean_inc(v_fst_2011_);
v_snd_2012_ = lean_ctor_get(v___x_2010_, 1);
lean_inc(v_snd_2012_);
lean_dec_ref(v___x_2010_);
if (v_isShared_2003_ == 0)
{
lean_ctor_set(v___x_2002_, 11, v_snd_2012_);
v___x_2014_ = v___x_2002_;
goto v_reusejp_2013_;
}
else
{
lean_object* v_reuseFailAlloc_2018_; 
v_reuseFailAlloc_2018_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_2018_, 0, v_visitedLevel_1989_);
lean_ctor_set(v_reuseFailAlloc_2018_, 1, v_visitedExpr_1990_);
lean_ctor_set(v_reuseFailAlloc_2018_, 2, v_levelParams_1991_);
lean_ctor_set(v_reuseFailAlloc_2018_, 3, v_nextLevelIdx_1992_);
lean_ctor_set(v_reuseFailAlloc_2018_, 4, v_levelArgs_1993_);
lean_ctor_set(v_reuseFailAlloc_2018_, 5, v_newLocalDecls_1994_);
lean_ctor_set(v_reuseFailAlloc_2018_, 6, v_newLocalDeclsForMVars_1995_);
lean_ctor_set(v_reuseFailAlloc_2018_, 7, v_newLetDecls_1996_);
lean_ctor_set(v_reuseFailAlloc_2018_, 8, v_nextExprIdx_1997_);
lean_ctor_set(v_reuseFailAlloc_2018_, 9, v_exprMVarArgs_1998_);
lean_ctor_set(v_reuseFailAlloc_2018_, 10, v_exprFVarArgs_1999_);
lean_ctor_set(v_reuseFailAlloc_2018_, 11, v_snd_2012_);
v___x_2014_ = v_reuseFailAlloc_2018_;
goto v_reusejp_2013_;
}
v_reusejp_2013_:
{
lean_object* v___x_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; 
v___x_2015_ = lean_st_ref_set(v_a_1979_, v___x_2014_);
v___x_2016_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2016_, 0, v_fst_2011_);
v___x_2017_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2017_, 0, v___x_2016_);
return v___x_2017_;
}
}
}
else
{
lean_object* v___x_2020_; lean_object* v___x_2021_; 
v___x_2020_ = lean_box(0);
v___x_2021_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2021_, 0, v___x_2020_);
return v___x_2021_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pickNextToProcess_x3f___redArg___boxed(lean_object* v_a_2022_, lean_object* v_a_2023_, lean_object* v_a_2024_){
_start:
{
lean_object* v_res_2025_; 
v_res_2025_ = l_Lean_Meta_Closure_pickNextToProcess_x3f___redArg(v_a_2022_, v_a_2023_);
lean_dec_ref(v_a_2023_);
lean_dec(v_a_2022_);
return v_res_2025_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pickNextToProcess_x3f(uint8_t v_a_2026_, lean_object* v_a_2027_, lean_object* v_a_2028_, lean_object* v_a_2029_, lean_object* v_a_2030_, lean_object* v_a_2031_){
_start:
{
lean_object* v___x_2033_; 
v___x_2033_ = l_Lean_Meta_Closure_pickNextToProcess_x3f___redArg(v_a_2027_, v_a_2028_);
return v___x_2033_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pickNextToProcess_x3f___boxed(lean_object* v_a_2034_, lean_object* v_a_2035_, lean_object* v_a_2036_, lean_object* v_a_2037_, lean_object* v_a_2038_, lean_object* v_a_2039_, lean_object* v_a_2040_){
_start:
{
uint8_t v_a_boxed_2041_; lean_object* v_res_2042_; 
v_a_boxed_2041_ = lean_unbox(v_a_2034_);
v_res_2042_ = l_Lean_Meta_Closure_pickNextToProcess_x3f(v_a_boxed_2041_, v_a_2035_, v_a_2036_, v_a_2037_, v_a_2038_, v_a_2039_);
lean_dec(v_a_2039_);
lean_dec_ref(v_a_2038_);
lean_dec(v_a_2037_);
lean_dec_ref(v_a_2036_);
lean_dec(v_a_2035_);
return v_res_2042_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushFVarArg___redArg(lean_object* v_e_2043_, lean_object* v_a_2044_){
_start:
{
lean_object* v___x_2046_; lean_object* v_visitedLevel_2047_; lean_object* v_visitedExpr_2048_; lean_object* v_levelParams_2049_; lean_object* v_nextLevelIdx_2050_; lean_object* v_levelArgs_2051_; lean_object* v_newLocalDecls_2052_; lean_object* v_newLocalDeclsForMVars_2053_; lean_object* v_newLetDecls_2054_; lean_object* v_nextExprIdx_2055_; lean_object* v_exprMVarArgs_2056_; lean_object* v_exprFVarArgs_2057_; lean_object* v_toProcess_2058_; lean_object* v___x_2060_; uint8_t v_isShared_2061_; uint8_t v_isSharedCheck_2069_; 
v___x_2046_ = lean_st_ref_take(v_a_2044_);
v_visitedLevel_2047_ = lean_ctor_get(v___x_2046_, 0);
v_visitedExpr_2048_ = lean_ctor_get(v___x_2046_, 1);
v_levelParams_2049_ = lean_ctor_get(v___x_2046_, 2);
v_nextLevelIdx_2050_ = lean_ctor_get(v___x_2046_, 3);
v_levelArgs_2051_ = lean_ctor_get(v___x_2046_, 4);
v_newLocalDecls_2052_ = lean_ctor_get(v___x_2046_, 5);
v_newLocalDeclsForMVars_2053_ = lean_ctor_get(v___x_2046_, 6);
v_newLetDecls_2054_ = lean_ctor_get(v___x_2046_, 7);
v_nextExprIdx_2055_ = lean_ctor_get(v___x_2046_, 8);
v_exprMVarArgs_2056_ = lean_ctor_get(v___x_2046_, 9);
v_exprFVarArgs_2057_ = lean_ctor_get(v___x_2046_, 10);
v_toProcess_2058_ = lean_ctor_get(v___x_2046_, 11);
v_isSharedCheck_2069_ = !lean_is_exclusive(v___x_2046_);
if (v_isSharedCheck_2069_ == 0)
{
v___x_2060_ = v___x_2046_;
v_isShared_2061_ = v_isSharedCheck_2069_;
goto v_resetjp_2059_;
}
else
{
lean_inc(v_toProcess_2058_);
lean_inc(v_exprFVarArgs_2057_);
lean_inc(v_exprMVarArgs_2056_);
lean_inc(v_nextExprIdx_2055_);
lean_inc(v_newLetDecls_2054_);
lean_inc(v_newLocalDeclsForMVars_2053_);
lean_inc(v_newLocalDecls_2052_);
lean_inc(v_levelArgs_2051_);
lean_inc(v_nextLevelIdx_2050_);
lean_inc(v_levelParams_2049_);
lean_inc(v_visitedExpr_2048_);
lean_inc(v_visitedLevel_2047_);
lean_dec(v___x_2046_);
v___x_2060_ = lean_box(0);
v_isShared_2061_ = v_isSharedCheck_2069_;
goto v_resetjp_2059_;
}
v_resetjp_2059_:
{
lean_object* v___x_2062_; lean_object* v___x_2064_; 
v___x_2062_ = lean_array_push(v_exprFVarArgs_2057_, v_e_2043_);
if (v_isShared_2061_ == 0)
{
lean_ctor_set(v___x_2060_, 10, v___x_2062_);
v___x_2064_ = v___x_2060_;
goto v_reusejp_2063_;
}
else
{
lean_object* v_reuseFailAlloc_2068_; 
v_reuseFailAlloc_2068_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_2068_, 0, v_visitedLevel_2047_);
lean_ctor_set(v_reuseFailAlloc_2068_, 1, v_visitedExpr_2048_);
lean_ctor_set(v_reuseFailAlloc_2068_, 2, v_levelParams_2049_);
lean_ctor_set(v_reuseFailAlloc_2068_, 3, v_nextLevelIdx_2050_);
lean_ctor_set(v_reuseFailAlloc_2068_, 4, v_levelArgs_2051_);
lean_ctor_set(v_reuseFailAlloc_2068_, 5, v_newLocalDecls_2052_);
lean_ctor_set(v_reuseFailAlloc_2068_, 6, v_newLocalDeclsForMVars_2053_);
lean_ctor_set(v_reuseFailAlloc_2068_, 7, v_newLetDecls_2054_);
lean_ctor_set(v_reuseFailAlloc_2068_, 8, v_nextExprIdx_2055_);
lean_ctor_set(v_reuseFailAlloc_2068_, 9, v_exprMVarArgs_2056_);
lean_ctor_set(v_reuseFailAlloc_2068_, 10, v___x_2062_);
lean_ctor_set(v_reuseFailAlloc_2068_, 11, v_toProcess_2058_);
v___x_2064_ = v_reuseFailAlloc_2068_;
goto v_reusejp_2063_;
}
v_reusejp_2063_:
{
lean_object* v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; 
v___x_2065_ = lean_st_ref_set(v_a_2044_, v___x_2064_);
v___x_2066_ = lean_box(0);
v___x_2067_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2067_, 0, v___x_2066_);
return v___x_2067_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushFVarArg___redArg___boxed(lean_object* v_e_2070_, lean_object* v_a_2071_, lean_object* v_a_2072_){
_start:
{
lean_object* v_res_2073_; 
v_res_2073_ = l_Lean_Meta_Closure_pushFVarArg___redArg(v_e_2070_, v_a_2071_);
lean_dec(v_a_2071_);
return v_res_2073_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushFVarArg(lean_object* v_e_2074_, uint8_t v_a_2075_, lean_object* v_a_2076_, lean_object* v_a_2077_, lean_object* v_a_2078_, lean_object* v_a_2079_, lean_object* v_a_2080_){
_start:
{
lean_object* v___x_2082_; 
v___x_2082_ = l_Lean_Meta_Closure_pushFVarArg___redArg(v_e_2074_, v_a_2076_);
return v___x_2082_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushFVarArg___boxed(lean_object* v_e_2083_, lean_object* v_a_2084_, lean_object* v_a_2085_, lean_object* v_a_2086_, lean_object* v_a_2087_, lean_object* v_a_2088_, lean_object* v_a_2089_, lean_object* v_a_2090_){
_start:
{
uint8_t v_a_boxed_2091_; lean_object* v_res_2092_; 
v_a_boxed_2091_ = lean_unbox(v_a_2084_);
v_res_2092_ = l_Lean_Meta_Closure_pushFVarArg(v_e_2083_, v_a_boxed_2091_, v_a_2085_, v_a_2086_, v_a_2087_, v_a_2088_, v_a_2089_);
lean_dec(v_a_2089_);
lean_dec_ref(v_a_2088_);
lean_dec(v_a_2087_);
lean_dec_ref(v_a_2086_);
lean_dec(v_a_2085_);
return v_res_2092_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushLocalDecl(lean_object* v_newFVarId_2093_, lean_object* v_userName_2094_, lean_object* v_type_2095_, uint8_t v_bi_2096_, uint8_t v_a_2097_, lean_object* v_a_2098_, lean_object* v_a_2099_, lean_object* v_a_2100_, lean_object* v_a_2101_, lean_object* v_a_2102_){
_start:
{
lean_object* v___x_2104_; 
v___x_2104_ = l_Lean_Meta_Closure_collectExpr(v_type_2095_, v_a_2097_, v_a_2098_, v_a_2099_, v_a_2100_, v_a_2101_, v_a_2102_);
if (lean_obj_tag(v___x_2104_) == 0)
{
lean_object* v_a_2105_; lean_object* v___x_2107_; uint8_t v_isShared_2108_; uint8_t v_isSharedCheck_2138_; 
v_a_2105_ = lean_ctor_get(v___x_2104_, 0);
v_isSharedCheck_2138_ = !lean_is_exclusive(v___x_2104_);
if (v_isSharedCheck_2138_ == 0)
{
v___x_2107_ = v___x_2104_;
v_isShared_2108_ = v_isSharedCheck_2138_;
goto v_resetjp_2106_;
}
else
{
lean_inc(v_a_2105_);
lean_dec(v___x_2104_);
v___x_2107_ = lean_box(0);
v_isShared_2108_ = v_isSharedCheck_2138_;
goto v_resetjp_2106_;
}
v_resetjp_2106_:
{
lean_object* v___x_2109_; lean_object* v_visitedLevel_2110_; lean_object* v_visitedExpr_2111_; lean_object* v_levelParams_2112_; lean_object* v_nextLevelIdx_2113_; lean_object* v_levelArgs_2114_; lean_object* v_newLocalDecls_2115_; lean_object* v_newLocalDeclsForMVars_2116_; lean_object* v_newLetDecls_2117_; lean_object* v_nextExprIdx_2118_; lean_object* v_exprMVarArgs_2119_; lean_object* v_exprFVarArgs_2120_; lean_object* v_toProcess_2121_; lean_object* v___x_2123_; uint8_t v_isShared_2124_; uint8_t v_isSharedCheck_2137_; 
v___x_2109_ = lean_st_ref_take(v_a_2098_);
v_visitedLevel_2110_ = lean_ctor_get(v___x_2109_, 0);
v_visitedExpr_2111_ = lean_ctor_get(v___x_2109_, 1);
v_levelParams_2112_ = lean_ctor_get(v___x_2109_, 2);
v_nextLevelIdx_2113_ = lean_ctor_get(v___x_2109_, 3);
v_levelArgs_2114_ = lean_ctor_get(v___x_2109_, 4);
v_newLocalDecls_2115_ = lean_ctor_get(v___x_2109_, 5);
v_newLocalDeclsForMVars_2116_ = lean_ctor_get(v___x_2109_, 6);
v_newLetDecls_2117_ = lean_ctor_get(v___x_2109_, 7);
v_nextExprIdx_2118_ = lean_ctor_get(v___x_2109_, 8);
v_exprMVarArgs_2119_ = lean_ctor_get(v___x_2109_, 9);
v_exprFVarArgs_2120_ = lean_ctor_get(v___x_2109_, 10);
v_toProcess_2121_ = lean_ctor_get(v___x_2109_, 11);
v_isSharedCheck_2137_ = !lean_is_exclusive(v___x_2109_);
if (v_isSharedCheck_2137_ == 0)
{
v___x_2123_ = v___x_2109_;
v_isShared_2124_ = v_isSharedCheck_2137_;
goto v_resetjp_2122_;
}
else
{
lean_inc(v_toProcess_2121_);
lean_inc(v_exprFVarArgs_2120_);
lean_inc(v_exprMVarArgs_2119_);
lean_inc(v_nextExprIdx_2118_);
lean_inc(v_newLetDecls_2117_);
lean_inc(v_newLocalDeclsForMVars_2116_);
lean_inc(v_newLocalDecls_2115_);
lean_inc(v_levelArgs_2114_);
lean_inc(v_nextLevelIdx_2113_);
lean_inc(v_levelParams_2112_);
lean_inc(v_visitedExpr_2111_);
lean_inc(v_visitedLevel_2110_);
lean_dec(v___x_2109_);
v___x_2123_ = lean_box(0);
v_isShared_2124_ = v_isSharedCheck_2137_;
goto v_resetjp_2122_;
}
v_resetjp_2122_:
{
lean_object* v___x_2125_; uint8_t v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2130_; 
v___x_2125_ = lean_unsigned_to_nat(0u);
v___x_2126_ = 0;
v___x_2127_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2127_, 0, v___x_2125_);
lean_ctor_set(v___x_2127_, 1, v_newFVarId_2093_);
lean_ctor_set(v___x_2127_, 2, v_userName_2094_);
lean_ctor_set(v___x_2127_, 3, v_a_2105_);
lean_ctor_set_uint8(v___x_2127_, sizeof(void*)*4, v_bi_2096_);
lean_ctor_set_uint8(v___x_2127_, sizeof(void*)*4 + 1, v___x_2126_);
v___x_2128_ = lean_array_push(v_newLocalDecls_2115_, v___x_2127_);
if (v_isShared_2124_ == 0)
{
lean_ctor_set(v___x_2123_, 5, v___x_2128_);
v___x_2130_ = v___x_2123_;
goto v_reusejp_2129_;
}
else
{
lean_object* v_reuseFailAlloc_2136_; 
v_reuseFailAlloc_2136_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_2136_, 0, v_visitedLevel_2110_);
lean_ctor_set(v_reuseFailAlloc_2136_, 1, v_visitedExpr_2111_);
lean_ctor_set(v_reuseFailAlloc_2136_, 2, v_levelParams_2112_);
lean_ctor_set(v_reuseFailAlloc_2136_, 3, v_nextLevelIdx_2113_);
lean_ctor_set(v_reuseFailAlloc_2136_, 4, v_levelArgs_2114_);
lean_ctor_set(v_reuseFailAlloc_2136_, 5, v___x_2128_);
lean_ctor_set(v_reuseFailAlloc_2136_, 6, v_newLocalDeclsForMVars_2116_);
lean_ctor_set(v_reuseFailAlloc_2136_, 7, v_newLetDecls_2117_);
lean_ctor_set(v_reuseFailAlloc_2136_, 8, v_nextExprIdx_2118_);
lean_ctor_set(v_reuseFailAlloc_2136_, 9, v_exprMVarArgs_2119_);
lean_ctor_set(v_reuseFailAlloc_2136_, 10, v_exprFVarArgs_2120_);
lean_ctor_set(v_reuseFailAlloc_2136_, 11, v_toProcess_2121_);
v___x_2130_ = v_reuseFailAlloc_2136_;
goto v_reusejp_2129_;
}
v_reusejp_2129_:
{
lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2134_; 
v___x_2131_ = lean_st_ref_set(v_a_2098_, v___x_2130_);
v___x_2132_ = lean_box(0);
if (v_isShared_2108_ == 0)
{
lean_ctor_set(v___x_2107_, 0, v___x_2132_);
v___x_2134_ = v___x_2107_;
goto v_reusejp_2133_;
}
else
{
lean_object* v_reuseFailAlloc_2135_; 
v_reuseFailAlloc_2135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2135_, 0, v___x_2132_);
v___x_2134_ = v_reuseFailAlloc_2135_;
goto v_reusejp_2133_;
}
v_reusejp_2133_:
{
return v___x_2134_;
}
}
}
}
}
else
{
lean_object* v_a_2139_; lean_object* v___x_2141_; uint8_t v_isShared_2142_; uint8_t v_isSharedCheck_2146_; 
lean_dec(v_userName_2094_);
lean_dec(v_newFVarId_2093_);
v_a_2139_ = lean_ctor_get(v___x_2104_, 0);
v_isSharedCheck_2146_ = !lean_is_exclusive(v___x_2104_);
if (v_isSharedCheck_2146_ == 0)
{
v___x_2141_ = v___x_2104_;
v_isShared_2142_ = v_isSharedCheck_2146_;
goto v_resetjp_2140_;
}
else
{
lean_inc(v_a_2139_);
lean_dec(v___x_2104_);
v___x_2141_ = lean_box(0);
v_isShared_2142_ = v_isSharedCheck_2146_;
goto v_resetjp_2140_;
}
v_resetjp_2140_:
{
lean_object* v___x_2144_; 
if (v_isShared_2142_ == 0)
{
v___x_2144_ = v___x_2141_;
goto v_reusejp_2143_;
}
else
{
lean_object* v_reuseFailAlloc_2145_; 
v_reuseFailAlloc_2145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2145_, 0, v_a_2139_);
v___x_2144_ = v_reuseFailAlloc_2145_;
goto v_reusejp_2143_;
}
v_reusejp_2143_:
{
return v___x_2144_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushLocalDecl___boxed(lean_object* v_newFVarId_2147_, lean_object* v_userName_2148_, lean_object* v_type_2149_, lean_object* v_bi_2150_, lean_object* v_a_2151_, lean_object* v_a_2152_, lean_object* v_a_2153_, lean_object* v_a_2154_, lean_object* v_a_2155_, lean_object* v_a_2156_, lean_object* v_a_2157_){
_start:
{
uint8_t v_bi_boxed_2158_; uint8_t v_a_boxed_2159_; lean_object* v_res_2160_; 
v_bi_boxed_2158_ = lean_unbox(v_bi_2150_);
v_a_boxed_2159_ = lean_unbox(v_a_2151_);
v_res_2160_ = l_Lean_Meta_Closure_pushLocalDecl(v_newFVarId_2147_, v_userName_2148_, v_type_2149_, v_bi_boxed_2158_, v_a_boxed_2159_, v_a_2152_, v_a_2153_, v_a_2154_, v_a_2155_, v_a_2156_);
lean_dec(v_a_2156_);
lean_dec_ref(v_a_2155_);
lean_dec(v_a_2154_);
lean_dec_ref(v_a_2153_);
lean_dec(v_a_2152_);
return v_res_2160_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Closure_process_spec__0___redArg(lean_object* v_k_2161_, lean_object* v_t_2162_){
_start:
{
if (lean_obj_tag(v_t_2162_) == 0)
{
lean_object* v_k_2163_; lean_object* v_l_2164_; lean_object* v_r_2165_; uint8_t v___x_2166_; 
v_k_2163_ = lean_ctor_get(v_t_2162_, 1);
v_l_2164_ = lean_ctor_get(v_t_2162_, 3);
v_r_2165_ = lean_ctor_get(v_t_2162_, 4);
v___x_2166_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_2161_, v_k_2163_);
switch(v___x_2166_)
{
case 0:
{
v_t_2162_ = v_l_2164_;
goto _start;
}
case 1:
{
uint8_t v___x_2168_; 
v___x_2168_ = 1;
return v___x_2168_;
}
default: 
{
v_t_2162_ = v_r_2165_;
goto _start;
}
}
}
else
{
uint8_t v___x_2170_; 
v___x_2170_ = 0;
return v___x_2170_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Closure_process_spec__0___redArg___boxed(lean_object* v_k_2171_, lean_object* v_t_2172_){
_start:
{
uint8_t v_res_2173_; lean_object* v_r_2174_; 
v_res_2173_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Closure_process_spec__0___redArg(v_k_2171_, v_t_2172_);
lean_dec(v_t_2172_);
lean_dec(v_k_2171_);
v_r_2174_ = lean_box(v_res_2173_);
return v_r_2174_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Closure_process_spec__1(lean_object* v_newFVarId_2175_, lean_object* v_a_2176_, size_t v_sz_2177_, size_t v_i_2178_, lean_object* v_bs_2179_){
_start:
{
uint8_t v___x_2180_; 
v___x_2180_ = lean_usize_dec_lt(v_i_2178_, v_sz_2177_);
if (v___x_2180_ == 0)
{
lean_dec(v_newFVarId_2175_);
return v_bs_2179_;
}
else
{
lean_object* v_v_2181_; lean_object* v___x_2182_; lean_object* v_bs_x27_2183_; lean_object* v___x_2184_; size_t v___x_2185_; size_t v___x_2186_; lean_object* v___x_2187_; 
v_v_2181_ = lean_array_uget(v_bs_2179_, v_i_2178_);
v___x_2182_ = lean_unsigned_to_nat(0u);
v_bs_x27_2183_ = lean_array_uset(v_bs_2179_, v_i_2178_, v___x_2182_);
lean_inc(v_newFVarId_2175_);
v___x_2184_ = l_Lean_LocalDecl_replaceFVarId(v_newFVarId_2175_, v_a_2176_, v_v_2181_);
v___x_2185_ = ((size_t)1ULL);
v___x_2186_ = lean_usize_add(v_i_2178_, v___x_2185_);
v___x_2187_ = lean_array_uset(v_bs_x27_2183_, v_i_2178_, v___x_2184_);
v_i_2178_ = v___x_2186_;
v_bs_2179_ = v___x_2187_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Closure_process_spec__1___boxed(lean_object* v_newFVarId_2189_, lean_object* v_a_2190_, lean_object* v_sz_2191_, lean_object* v_i_2192_, lean_object* v_bs_2193_){
_start:
{
size_t v_sz_boxed_2194_; size_t v_i_boxed_2195_; lean_object* v_res_2196_; 
v_sz_boxed_2194_ = lean_unbox_usize(v_sz_2191_);
lean_dec(v_sz_2191_);
v_i_boxed_2195_ = lean_unbox_usize(v_i_2192_);
lean_dec(v_i_2192_);
v_res_2196_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Closure_process_spec__1(v_newFVarId_2189_, v_a_2190_, v_sz_boxed_2194_, v_i_boxed_2195_, v_bs_2193_);
lean_dec_ref(v_a_2190_);
return v_res_2196_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_process(uint8_t v_a_2197_, lean_object* v_a_2198_, lean_object* v_a_2199_, lean_object* v_a_2200_, lean_object* v_a_2201_, lean_object* v_a_2202_){
_start:
{
lean_object* v___x_2204_; 
v___x_2204_ = l_Lean_Meta_Closure_pickNextToProcess_x3f___redArg(v_a_2198_, v_a_2199_);
if (lean_obj_tag(v___x_2204_) == 0)
{
lean_object* v_a_2205_; lean_object* v___x_2207_; uint8_t v_isShared_2208_; uint8_t v_isSharedCheck_2333_; 
v_a_2205_ = lean_ctor_get(v___x_2204_, 0);
v_isSharedCheck_2333_ = !lean_is_exclusive(v___x_2204_);
if (v_isSharedCheck_2333_ == 0)
{
v___x_2207_ = v___x_2204_;
v_isShared_2208_ = v_isSharedCheck_2333_;
goto v_resetjp_2206_;
}
else
{
lean_inc(v_a_2205_);
lean_dec(v___x_2204_);
v___x_2207_ = lean_box(0);
v_isShared_2208_ = v_isSharedCheck_2333_;
goto v_resetjp_2206_;
}
v_resetjp_2206_:
{
if (lean_obj_tag(v_a_2205_) == 0)
{
lean_object* v___x_2209_; lean_object* v___x_2211_; 
v___x_2209_ = lean_box(0);
if (v_isShared_2208_ == 0)
{
lean_ctor_set(v___x_2207_, 0, v___x_2209_);
v___x_2211_ = v___x_2207_;
goto v_reusejp_2210_;
}
else
{
lean_object* v_reuseFailAlloc_2212_; 
v_reuseFailAlloc_2212_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2212_, 0, v___x_2209_);
v___x_2211_ = v_reuseFailAlloc_2212_;
goto v_reusejp_2210_;
}
v_reusejp_2210_:
{
return v___x_2211_;
}
}
else
{
lean_object* v_val_2213_; lean_object* v_fvarId_2214_; lean_object* v_newFVarId_2215_; lean_object* v___x_2216_; 
lean_del_object(v___x_2207_);
v_val_2213_ = lean_ctor_get(v_a_2205_, 0);
lean_inc(v_val_2213_);
lean_dec_ref_known(v_a_2205_, 1);
v_fvarId_2214_ = lean_ctor_get(v_val_2213_, 0);
lean_inc_n(v_fvarId_2214_, 2);
v_newFVarId_2215_ = lean_ctor_get(v_val_2213_, 1);
lean_inc(v_newFVarId_2215_);
lean_dec(v_val_2213_);
v___x_2216_ = l_Lean_FVarId_getDecl___redArg(v_fvarId_2214_, v_a_2199_, v_a_2201_, v_a_2202_);
if (lean_obj_tag(v___x_2216_) == 0)
{
lean_object* v_a_2217_; 
v_a_2217_ = lean_ctor_get(v___x_2216_, 0);
lean_inc(v_a_2217_);
lean_dec_ref_known(v___x_2216_, 1);
if (lean_obj_tag(v_a_2217_) == 0)
{
lean_object* v_userName_2218_; lean_object* v_type_2219_; uint8_t v_bi_2220_; lean_object* v___x_2221_; 
v_userName_2218_ = lean_ctor_get(v_a_2217_, 2);
lean_inc(v_userName_2218_);
v_type_2219_ = lean_ctor_get(v_a_2217_, 3);
lean_inc_ref(v_type_2219_);
v_bi_2220_ = lean_ctor_get_uint8(v_a_2217_, sizeof(void*)*4);
lean_dec_ref_known(v_a_2217_, 4);
v___x_2221_ = l_Lean_Meta_Closure_pushLocalDecl(v_newFVarId_2215_, v_userName_2218_, v_type_2219_, v_bi_2220_, v_a_2197_, v_a_2198_, v_a_2199_, v_a_2200_, v_a_2201_, v_a_2202_);
if (lean_obj_tag(v___x_2221_) == 0)
{
lean_object* v___x_2222_; lean_object* v___x_2223_; 
lean_dec_ref_known(v___x_2221_, 1);
v___x_2222_ = l_Lean_mkFVar(v_fvarId_2214_);
v___x_2223_ = l_Lean_Meta_Closure_pushFVarArg___redArg(v___x_2222_, v_a_2198_);
if (lean_obj_tag(v___x_2223_) == 0)
{
lean_dec_ref_known(v___x_2223_, 1);
goto _start;
}
else
{
return v___x_2223_;
}
}
else
{
lean_dec(v_fvarId_2214_);
return v___x_2221_;
}
}
else
{
lean_object* v_userName_2225_; lean_object* v_type_2226_; lean_object* v_value_2227_; uint8_t v_nondep_2228_; lean_object* v___x_2230_; uint8_t v_isShared_2231_; uint8_t v_isSharedCheck_2322_; 
v_userName_2225_ = lean_ctor_get(v_a_2217_, 2);
v_type_2226_ = lean_ctor_get(v_a_2217_, 3);
v_value_2227_ = lean_ctor_get(v_a_2217_, 4);
v_nondep_2228_ = lean_ctor_get_uint8(v_a_2217_, sizeof(void*)*5);
v_isSharedCheck_2322_ = !lean_is_exclusive(v_a_2217_);
if (v_isSharedCheck_2322_ == 0)
{
lean_object* v_unused_2323_; lean_object* v_unused_2324_; 
v_unused_2323_ = lean_ctor_get(v_a_2217_, 1);
lean_dec(v_unused_2323_);
v_unused_2324_ = lean_ctor_get(v_a_2217_, 0);
lean_dec(v_unused_2324_);
v___x_2230_ = v_a_2217_;
v_isShared_2231_ = v_isSharedCheck_2322_;
goto v_resetjp_2229_;
}
else
{
lean_inc(v_value_2227_);
lean_inc(v_type_2226_);
lean_inc(v_userName_2225_);
lean_dec(v_a_2217_);
v___x_2230_ = lean_box(0);
v_isShared_2231_ = v_isSharedCheck_2322_;
goto v_resetjp_2229_;
}
v_resetjp_2229_:
{
lean_object* v___x_2232_; 
v___x_2232_ = l_Lean_Meta_getZetaDeltaFVarIds___redArg(v_a_2200_);
if (lean_obj_tag(v___x_2232_) == 0)
{
lean_object* v_a_2233_; 
v_a_2233_ = lean_ctor_get(v___x_2232_, 0);
lean_inc(v_a_2233_);
lean_dec_ref_known(v___x_2232_, 1);
if (v_nondep_2228_ == 0)
{
uint8_t v___x_2240_; uint8_t v___x_2241_; 
v___x_2240_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Closure_process_spec__0___redArg(v_fvarId_2214_, v_a_2233_);
lean_dec(v_a_2233_);
v___x_2241_ = lean_bool_not(v___x_2240_);
if (v___x_2241_ == 0)
{
lean_object* v___x_2242_; 
lean_dec(v_fvarId_2214_);
v___x_2242_ = l_Lean_Meta_Closure_collectExpr(v_type_2226_, v_a_2197_, v_a_2198_, v_a_2199_, v_a_2200_, v_a_2201_, v_a_2202_);
if (lean_obj_tag(v___x_2242_) == 0)
{
lean_object* v_a_2243_; lean_object* v___x_2244_; 
v_a_2243_ = lean_ctor_get(v___x_2242_, 0);
lean_inc(v_a_2243_);
lean_dec_ref_known(v___x_2242_, 1);
v___x_2244_ = l_Lean_Meta_Closure_collectExpr(v_value_2227_, v_a_2197_, v_a_2198_, v_a_2199_, v_a_2200_, v_a_2201_, v_a_2202_);
if (lean_obj_tag(v___x_2244_) == 0)
{
lean_object* v_a_2245_; lean_object* v___x_2246_; lean_object* v_visitedLevel_2247_; lean_object* v_visitedExpr_2248_; lean_object* v_levelParams_2249_; lean_object* v_nextLevelIdx_2250_; lean_object* v_levelArgs_2251_; lean_object* v_newLocalDecls_2252_; lean_object* v_newLocalDeclsForMVars_2253_; lean_object* v_newLetDecls_2254_; lean_object* v_nextExprIdx_2255_; lean_object* v_exprMVarArgs_2256_; lean_object* v_exprFVarArgs_2257_; lean_object* v_toProcess_2258_; lean_object* v___x_2260_; uint8_t v_isShared_2261_; uint8_t v_isSharedCheck_2297_; 
v_a_2245_ = lean_ctor_get(v___x_2244_, 0);
lean_inc(v_a_2245_);
lean_dec_ref_known(v___x_2244_, 1);
v___x_2246_ = lean_st_ref_take(v_a_2198_);
v_visitedLevel_2247_ = lean_ctor_get(v___x_2246_, 0);
v_visitedExpr_2248_ = lean_ctor_get(v___x_2246_, 1);
v_levelParams_2249_ = lean_ctor_get(v___x_2246_, 2);
v_nextLevelIdx_2250_ = lean_ctor_get(v___x_2246_, 3);
v_levelArgs_2251_ = lean_ctor_get(v___x_2246_, 4);
v_newLocalDecls_2252_ = lean_ctor_get(v___x_2246_, 5);
v_newLocalDeclsForMVars_2253_ = lean_ctor_get(v___x_2246_, 6);
v_newLetDecls_2254_ = lean_ctor_get(v___x_2246_, 7);
v_nextExprIdx_2255_ = lean_ctor_get(v___x_2246_, 8);
v_exprMVarArgs_2256_ = lean_ctor_get(v___x_2246_, 9);
v_exprFVarArgs_2257_ = lean_ctor_get(v___x_2246_, 10);
v_toProcess_2258_ = lean_ctor_get(v___x_2246_, 11);
v_isSharedCheck_2297_ = !lean_is_exclusive(v___x_2246_);
if (v_isSharedCheck_2297_ == 0)
{
v___x_2260_ = v___x_2246_;
v_isShared_2261_ = v_isSharedCheck_2297_;
goto v_resetjp_2259_;
}
else
{
lean_inc(v_toProcess_2258_);
lean_inc(v_exprFVarArgs_2257_);
lean_inc(v_exprMVarArgs_2256_);
lean_inc(v_nextExprIdx_2255_);
lean_inc(v_newLetDecls_2254_);
lean_inc(v_newLocalDeclsForMVars_2253_);
lean_inc(v_newLocalDecls_2252_);
lean_inc(v_levelArgs_2251_);
lean_inc(v_nextLevelIdx_2250_);
lean_inc(v_levelParams_2249_);
lean_inc(v_visitedExpr_2248_);
lean_inc(v_visitedLevel_2247_);
lean_dec(v___x_2246_);
v___x_2260_ = lean_box(0);
v_isShared_2261_ = v_isSharedCheck_2297_;
goto v_resetjp_2259_;
}
v_resetjp_2259_:
{
lean_object* v___x_2262_; uint8_t v___x_2263_; lean_object* v___x_2265_; 
v___x_2262_ = lean_unsigned_to_nat(0u);
v___x_2263_ = 0;
lean_inc(v_a_2245_);
lean_inc(v_newFVarId_2215_);
if (v_isShared_2231_ == 0)
{
lean_ctor_set(v___x_2230_, 4, v_a_2245_);
lean_ctor_set(v___x_2230_, 3, v_a_2243_);
lean_ctor_set(v___x_2230_, 1, v_newFVarId_2215_);
lean_ctor_set(v___x_2230_, 0, v___x_2262_);
v___x_2265_ = v___x_2230_;
goto v_reusejp_2264_;
}
else
{
lean_object* v_reuseFailAlloc_2296_; 
v_reuseFailAlloc_2296_ = lean_alloc_ctor(1, 5, 2);
lean_ctor_set(v_reuseFailAlloc_2296_, 0, v___x_2262_);
lean_ctor_set(v_reuseFailAlloc_2296_, 1, v_newFVarId_2215_);
lean_ctor_set(v_reuseFailAlloc_2296_, 2, v_userName_2225_);
lean_ctor_set(v_reuseFailAlloc_2296_, 3, v_a_2243_);
lean_ctor_set(v_reuseFailAlloc_2296_, 4, v_a_2245_);
v___x_2265_ = v_reuseFailAlloc_2296_;
goto v_reusejp_2264_;
}
v_reusejp_2264_:
{
lean_object* v___x_2266_; lean_object* v___x_2268_; 
lean_ctor_set_uint8(v___x_2265_, sizeof(void*)*5, v___x_2241_);
lean_ctor_set_uint8(v___x_2265_, sizeof(void*)*5 + 1, v___x_2263_);
v___x_2266_ = lean_array_push(v_newLetDecls_2254_, v___x_2265_);
if (v_isShared_2261_ == 0)
{
lean_ctor_set(v___x_2260_, 7, v___x_2266_);
v___x_2268_ = v___x_2260_;
goto v_reusejp_2267_;
}
else
{
lean_object* v_reuseFailAlloc_2295_; 
v_reuseFailAlloc_2295_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_2295_, 0, v_visitedLevel_2247_);
lean_ctor_set(v_reuseFailAlloc_2295_, 1, v_visitedExpr_2248_);
lean_ctor_set(v_reuseFailAlloc_2295_, 2, v_levelParams_2249_);
lean_ctor_set(v_reuseFailAlloc_2295_, 3, v_nextLevelIdx_2250_);
lean_ctor_set(v_reuseFailAlloc_2295_, 4, v_levelArgs_2251_);
lean_ctor_set(v_reuseFailAlloc_2295_, 5, v_newLocalDecls_2252_);
lean_ctor_set(v_reuseFailAlloc_2295_, 6, v_newLocalDeclsForMVars_2253_);
lean_ctor_set(v_reuseFailAlloc_2295_, 7, v___x_2266_);
lean_ctor_set(v_reuseFailAlloc_2295_, 8, v_nextExprIdx_2255_);
lean_ctor_set(v_reuseFailAlloc_2295_, 9, v_exprMVarArgs_2256_);
lean_ctor_set(v_reuseFailAlloc_2295_, 10, v_exprFVarArgs_2257_);
lean_ctor_set(v_reuseFailAlloc_2295_, 11, v_toProcess_2258_);
v___x_2268_ = v_reuseFailAlloc_2295_;
goto v_reusejp_2267_;
}
v_reusejp_2267_:
{
lean_object* v___x_2269_; lean_object* v___x_2270_; lean_object* v_visitedLevel_2271_; lean_object* v_visitedExpr_2272_; lean_object* v_levelParams_2273_; lean_object* v_nextLevelIdx_2274_; lean_object* v_levelArgs_2275_; lean_object* v_newLocalDecls_2276_; lean_object* v_newLocalDeclsForMVars_2277_; lean_object* v_newLetDecls_2278_; lean_object* v_nextExprIdx_2279_; lean_object* v_exprMVarArgs_2280_; lean_object* v_exprFVarArgs_2281_; lean_object* v_toProcess_2282_; lean_object* v___x_2284_; uint8_t v_isShared_2285_; uint8_t v_isSharedCheck_2294_; 
v___x_2269_ = lean_st_ref_set(v_a_2198_, v___x_2268_);
v___x_2270_ = lean_st_ref_take(v_a_2198_);
v_visitedLevel_2271_ = lean_ctor_get(v___x_2270_, 0);
v_visitedExpr_2272_ = lean_ctor_get(v___x_2270_, 1);
v_levelParams_2273_ = lean_ctor_get(v___x_2270_, 2);
v_nextLevelIdx_2274_ = lean_ctor_get(v___x_2270_, 3);
v_levelArgs_2275_ = lean_ctor_get(v___x_2270_, 4);
v_newLocalDecls_2276_ = lean_ctor_get(v___x_2270_, 5);
v_newLocalDeclsForMVars_2277_ = lean_ctor_get(v___x_2270_, 6);
v_newLetDecls_2278_ = lean_ctor_get(v___x_2270_, 7);
v_nextExprIdx_2279_ = lean_ctor_get(v___x_2270_, 8);
v_exprMVarArgs_2280_ = lean_ctor_get(v___x_2270_, 9);
v_exprFVarArgs_2281_ = lean_ctor_get(v___x_2270_, 10);
v_toProcess_2282_ = lean_ctor_get(v___x_2270_, 11);
v_isSharedCheck_2294_ = !lean_is_exclusive(v___x_2270_);
if (v_isSharedCheck_2294_ == 0)
{
v___x_2284_ = v___x_2270_;
v_isShared_2285_ = v_isSharedCheck_2294_;
goto v_resetjp_2283_;
}
else
{
lean_inc(v_toProcess_2282_);
lean_inc(v_exprFVarArgs_2281_);
lean_inc(v_exprMVarArgs_2280_);
lean_inc(v_nextExprIdx_2279_);
lean_inc(v_newLetDecls_2278_);
lean_inc(v_newLocalDeclsForMVars_2277_);
lean_inc(v_newLocalDecls_2276_);
lean_inc(v_levelArgs_2275_);
lean_inc(v_nextLevelIdx_2274_);
lean_inc(v_levelParams_2273_);
lean_inc(v_visitedExpr_2272_);
lean_inc(v_visitedLevel_2271_);
lean_dec(v___x_2270_);
v___x_2284_ = lean_box(0);
v_isShared_2285_ = v_isSharedCheck_2294_;
goto v_resetjp_2283_;
}
v_resetjp_2283_:
{
size_t v_sz_2286_; size_t v___x_2287_; lean_object* v___x_2288_; lean_object* v___x_2290_; 
v_sz_2286_ = lean_array_size(v_newLocalDecls_2276_);
v___x_2287_ = ((size_t)0ULL);
v___x_2288_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Closure_process_spec__1(v_newFVarId_2215_, v_a_2245_, v_sz_2286_, v___x_2287_, v_newLocalDecls_2276_);
lean_dec(v_a_2245_);
if (v_isShared_2285_ == 0)
{
lean_ctor_set(v___x_2284_, 5, v___x_2288_);
v___x_2290_ = v___x_2284_;
goto v_reusejp_2289_;
}
else
{
lean_object* v_reuseFailAlloc_2293_; 
v_reuseFailAlloc_2293_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_2293_, 0, v_visitedLevel_2271_);
lean_ctor_set(v_reuseFailAlloc_2293_, 1, v_visitedExpr_2272_);
lean_ctor_set(v_reuseFailAlloc_2293_, 2, v_levelParams_2273_);
lean_ctor_set(v_reuseFailAlloc_2293_, 3, v_nextLevelIdx_2274_);
lean_ctor_set(v_reuseFailAlloc_2293_, 4, v_levelArgs_2275_);
lean_ctor_set(v_reuseFailAlloc_2293_, 5, v___x_2288_);
lean_ctor_set(v_reuseFailAlloc_2293_, 6, v_newLocalDeclsForMVars_2277_);
lean_ctor_set(v_reuseFailAlloc_2293_, 7, v_newLetDecls_2278_);
lean_ctor_set(v_reuseFailAlloc_2293_, 8, v_nextExprIdx_2279_);
lean_ctor_set(v_reuseFailAlloc_2293_, 9, v_exprMVarArgs_2280_);
lean_ctor_set(v_reuseFailAlloc_2293_, 10, v_exprFVarArgs_2281_);
lean_ctor_set(v_reuseFailAlloc_2293_, 11, v_toProcess_2282_);
v___x_2290_ = v_reuseFailAlloc_2293_;
goto v_reusejp_2289_;
}
v_reusejp_2289_:
{
lean_object* v___x_2291_; 
v___x_2291_ = lean_st_ref_set(v_a_2198_, v___x_2290_);
goto _start;
}
}
}
}
}
}
else
{
lean_object* v_a_2298_; lean_object* v___x_2300_; uint8_t v_isShared_2301_; uint8_t v_isSharedCheck_2305_; 
lean_dec(v_a_2243_);
lean_del_object(v___x_2230_);
lean_dec(v_userName_2225_);
lean_dec(v_newFVarId_2215_);
v_a_2298_ = lean_ctor_get(v___x_2244_, 0);
v_isSharedCheck_2305_ = !lean_is_exclusive(v___x_2244_);
if (v_isSharedCheck_2305_ == 0)
{
v___x_2300_ = v___x_2244_;
v_isShared_2301_ = v_isSharedCheck_2305_;
goto v_resetjp_2299_;
}
else
{
lean_inc(v_a_2298_);
lean_dec(v___x_2244_);
v___x_2300_ = lean_box(0);
v_isShared_2301_ = v_isSharedCheck_2305_;
goto v_resetjp_2299_;
}
v_resetjp_2299_:
{
lean_object* v___x_2303_; 
if (v_isShared_2301_ == 0)
{
v___x_2303_ = v___x_2300_;
goto v_reusejp_2302_;
}
else
{
lean_object* v_reuseFailAlloc_2304_; 
v_reuseFailAlloc_2304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2304_, 0, v_a_2298_);
v___x_2303_ = v_reuseFailAlloc_2304_;
goto v_reusejp_2302_;
}
v_reusejp_2302_:
{
return v___x_2303_;
}
}
}
}
else
{
lean_object* v_a_2306_; lean_object* v___x_2308_; uint8_t v_isShared_2309_; uint8_t v_isSharedCheck_2313_; 
lean_del_object(v___x_2230_);
lean_dec_ref(v_value_2227_);
lean_dec(v_userName_2225_);
lean_dec(v_newFVarId_2215_);
v_a_2306_ = lean_ctor_get(v___x_2242_, 0);
v_isSharedCheck_2313_ = !lean_is_exclusive(v___x_2242_);
if (v_isSharedCheck_2313_ == 0)
{
v___x_2308_ = v___x_2242_;
v_isShared_2309_ = v_isSharedCheck_2313_;
goto v_resetjp_2307_;
}
else
{
lean_inc(v_a_2306_);
lean_dec(v___x_2242_);
v___x_2308_ = lean_box(0);
v_isShared_2309_ = v_isSharedCheck_2313_;
goto v_resetjp_2307_;
}
v_resetjp_2307_:
{
lean_object* v___x_2311_; 
if (v_isShared_2309_ == 0)
{
v___x_2311_ = v___x_2308_;
goto v_reusejp_2310_;
}
else
{
lean_object* v_reuseFailAlloc_2312_; 
v_reuseFailAlloc_2312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2312_, 0, v_a_2306_);
v___x_2311_ = v_reuseFailAlloc_2312_;
goto v_reusejp_2310_;
}
v_reusejp_2310_:
{
return v___x_2311_;
}
}
}
}
else
{
lean_del_object(v___x_2230_);
lean_dec_ref(v_value_2227_);
goto v___jp_2234_;
}
}
else
{
lean_dec(v_a_2233_);
lean_del_object(v___x_2230_);
lean_dec_ref(v_value_2227_);
goto v___jp_2234_;
}
v___jp_2234_:
{
uint8_t v___x_2235_; lean_object* v___x_2236_; 
v___x_2235_ = 0;
v___x_2236_ = l_Lean_Meta_Closure_pushLocalDecl(v_newFVarId_2215_, v_userName_2225_, v_type_2226_, v___x_2235_, v_a_2197_, v_a_2198_, v_a_2199_, v_a_2200_, v_a_2201_, v_a_2202_);
if (lean_obj_tag(v___x_2236_) == 0)
{
lean_object* v___x_2237_; lean_object* v___x_2238_; 
lean_dec_ref_known(v___x_2236_, 1);
v___x_2237_ = l_Lean_mkFVar(v_fvarId_2214_);
v___x_2238_ = l_Lean_Meta_Closure_pushFVarArg___redArg(v___x_2237_, v_a_2198_);
if (lean_obj_tag(v___x_2238_) == 0)
{
lean_dec_ref_known(v___x_2238_, 1);
goto _start;
}
else
{
return v___x_2238_;
}
}
else
{
lean_dec(v_fvarId_2214_);
return v___x_2236_;
}
}
}
else
{
lean_object* v_a_2314_; lean_object* v___x_2316_; uint8_t v_isShared_2317_; uint8_t v_isSharedCheck_2321_; 
lean_del_object(v___x_2230_);
lean_dec_ref(v_value_2227_);
lean_dec_ref(v_type_2226_);
lean_dec(v_userName_2225_);
lean_dec(v_newFVarId_2215_);
lean_dec(v_fvarId_2214_);
v_a_2314_ = lean_ctor_get(v___x_2232_, 0);
v_isSharedCheck_2321_ = !lean_is_exclusive(v___x_2232_);
if (v_isSharedCheck_2321_ == 0)
{
v___x_2316_ = v___x_2232_;
v_isShared_2317_ = v_isSharedCheck_2321_;
goto v_resetjp_2315_;
}
else
{
lean_inc(v_a_2314_);
lean_dec(v___x_2232_);
v___x_2316_ = lean_box(0);
v_isShared_2317_ = v_isSharedCheck_2321_;
goto v_resetjp_2315_;
}
v_resetjp_2315_:
{
lean_object* v___x_2319_; 
if (v_isShared_2317_ == 0)
{
v___x_2319_ = v___x_2316_;
goto v_reusejp_2318_;
}
else
{
lean_object* v_reuseFailAlloc_2320_; 
v_reuseFailAlloc_2320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2320_, 0, v_a_2314_);
v___x_2319_ = v_reuseFailAlloc_2320_;
goto v_reusejp_2318_;
}
v_reusejp_2318_:
{
return v___x_2319_;
}
}
}
}
}
}
else
{
lean_object* v_a_2325_; lean_object* v___x_2327_; uint8_t v_isShared_2328_; uint8_t v_isSharedCheck_2332_; 
lean_dec(v_newFVarId_2215_);
lean_dec(v_fvarId_2214_);
v_a_2325_ = lean_ctor_get(v___x_2216_, 0);
v_isSharedCheck_2332_ = !lean_is_exclusive(v___x_2216_);
if (v_isSharedCheck_2332_ == 0)
{
v___x_2327_ = v___x_2216_;
v_isShared_2328_ = v_isSharedCheck_2332_;
goto v_resetjp_2326_;
}
else
{
lean_inc(v_a_2325_);
lean_dec(v___x_2216_);
v___x_2327_ = lean_box(0);
v_isShared_2328_ = v_isSharedCheck_2332_;
goto v_resetjp_2326_;
}
v_resetjp_2326_:
{
lean_object* v___x_2330_; 
if (v_isShared_2328_ == 0)
{
v___x_2330_ = v___x_2327_;
goto v_reusejp_2329_;
}
else
{
lean_object* v_reuseFailAlloc_2331_; 
v_reuseFailAlloc_2331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2331_, 0, v_a_2325_);
v___x_2330_ = v_reuseFailAlloc_2331_;
goto v_reusejp_2329_;
}
v_reusejp_2329_:
{
return v___x_2330_;
}
}
}
}
}
}
else
{
lean_object* v_a_2334_; lean_object* v___x_2336_; uint8_t v_isShared_2337_; uint8_t v_isSharedCheck_2341_; 
v_a_2334_ = lean_ctor_get(v___x_2204_, 0);
v_isSharedCheck_2341_ = !lean_is_exclusive(v___x_2204_);
if (v_isSharedCheck_2341_ == 0)
{
v___x_2336_ = v___x_2204_;
v_isShared_2337_ = v_isSharedCheck_2341_;
goto v_resetjp_2335_;
}
else
{
lean_inc(v_a_2334_);
lean_dec(v___x_2204_);
v___x_2336_ = lean_box(0);
v_isShared_2337_ = v_isSharedCheck_2341_;
goto v_resetjp_2335_;
}
v_resetjp_2335_:
{
lean_object* v___x_2339_; 
if (v_isShared_2337_ == 0)
{
v___x_2339_ = v___x_2336_;
goto v_reusejp_2338_;
}
else
{
lean_object* v_reuseFailAlloc_2340_; 
v_reuseFailAlloc_2340_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2340_, 0, v_a_2334_);
v___x_2339_ = v_reuseFailAlloc_2340_;
goto v_reusejp_2338_;
}
v_reusejp_2338_:
{
return v___x_2339_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_process___boxed(lean_object* v_a_2342_, lean_object* v_a_2343_, lean_object* v_a_2344_, lean_object* v_a_2345_, lean_object* v_a_2346_, lean_object* v_a_2347_, lean_object* v_a_2348_){
_start:
{
uint8_t v_a_boxed_2349_; lean_object* v_res_2350_; 
v_a_boxed_2349_ = lean_unbox(v_a_2342_);
v_res_2350_ = l_Lean_Meta_Closure_process(v_a_boxed_2349_, v_a_2343_, v_a_2344_, v_a_2345_, v_a_2346_, v_a_2347_);
lean_dec(v_a_2347_);
lean_dec_ref(v_a_2346_);
lean_dec(v_a_2345_);
lean_dec_ref(v_a_2344_);
lean_dec(v_a_2343_);
return v_res_2350_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Closure_process_spec__0(lean_object* v_00_u03b2_2351_, lean_object* v_k_2352_, lean_object* v_t_2353_){
_start:
{
uint8_t v___x_2354_; 
v___x_2354_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Closure_process_spec__0___redArg(v_k_2352_, v_t_2353_);
return v___x_2354_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Closure_process_spec__0___boxed(lean_object* v_00_u03b2_2355_, lean_object* v_k_2356_, lean_object* v_t_2357_){
_start:
{
uint8_t v_res_2358_; lean_object* v_r_2359_; 
v_res_2358_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Closure_process_spec__0(v_00_u03b2_2355_, v_k_2356_, v_t_2357_);
lean_dec(v_t_2357_);
lean_dec(v_k_2356_);
v_r_2359_ = lean_box(v_res_2358_);
return v_r_2359_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkBinding___lam__0(lean_object* v_decls_2360_, lean_object* v_xs_2361_, uint8_t v_isLambda_2362_, lean_object* v_i_2363_, lean_object* v_x_2364_, lean_object* v_b_2365_){
_start:
{
lean_object* v_decl_2366_; 
v_decl_2366_ = lean_array_fget_borrowed(v_decls_2360_, v_i_2363_);
if (lean_obj_tag(v_decl_2366_) == 0)
{
lean_object* v_userName_2367_; lean_object* v_type_2368_; uint8_t v_bi_2369_; lean_object* v_ty_2370_; 
v_userName_2367_ = lean_ctor_get(v_decl_2366_, 2);
v_type_2368_ = lean_ctor_get(v_decl_2366_, 3);
v_bi_2369_ = lean_ctor_get_uint8(v_decl_2366_, sizeof(void*)*4);
v_ty_2370_ = lean_expr_abstract_range(v_type_2368_, v_i_2363_, v_xs_2361_);
if (v_isLambda_2362_ == 0)
{
lean_object* v___x_2371_; 
lean_inc(v_userName_2367_);
v___x_2371_ = l_Lean_mkForall(v_userName_2367_, v_bi_2369_, v_ty_2370_, v_b_2365_);
return v___x_2371_;
}
else
{
lean_object* v___x_2372_; 
lean_inc(v_userName_2367_);
v___x_2372_ = l_Lean_mkLambda(v_userName_2367_, v_bi_2369_, v_ty_2370_, v_b_2365_);
return v___x_2372_;
}
}
else
{
lean_object* v_userName_2373_; lean_object* v_type_2374_; lean_object* v_value_2375_; uint8_t v_nondep_2376_; lean_object* v___x_2377_; uint8_t v___x_2378_; 
v_userName_2373_ = lean_ctor_get(v_decl_2366_, 2);
v_type_2374_ = lean_ctor_get(v_decl_2366_, 3);
v_value_2375_ = lean_ctor_get(v_decl_2366_, 4);
v_nondep_2376_ = lean_ctor_get_uint8(v_decl_2366_, sizeof(void*)*5);
v___x_2377_ = lean_unsigned_to_nat(0u);
v___x_2378_ = lean_expr_has_loose_bvar(v_b_2365_, v___x_2377_);
if (v___x_2378_ == 0)
{
lean_object* v___x_2379_; lean_object* v___x_2380_; 
v___x_2379_ = lean_unsigned_to_nat(1u);
v___x_2380_ = lean_expr_lower_loose_bvars(v_b_2365_, v___x_2379_, v___x_2379_);
lean_dec_ref(v_b_2365_);
return v___x_2380_;
}
else
{
lean_object* v_ty_2381_; lean_object* v_val_2382_; lean_object* v___x_2383_; 
v_ty_2381_ = lean_expr_abstract_range(v_type_2374_, v_i_2363_, v_xs_2361_);
v_val_2382_ = lean_expr_abstract_range(v_value_2375_, v_i_2363_, v_xs_2361_);
lean_inc(v_userName_2373_);
v___x_2383_ = l_Lean_Expr_letE___override(v_userName_2373_, v_ty_2381_, v_val_2382_, v_b_2365_, v_nondep_2376_);
return v___x_2383_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkBinding___lam__0___boxed(lean_object* v_decls_2384_, lean_object* v_xs_2385_, lean_object* v_isLambda_2386_, lean_object* v_i_2387_, lean_object* v_x_2388_, lean_object* v_b_2389_){
_start:
{
uint8_t v_isLambda_boxed_2390_; lean_object* v_res_2391_; 
v_isLambda_boxed_2390_ = lean_unbox(v_isLambda_2386_);
v_res_2391_ = l_Lean_Meta_Closure_mkBinding___lam__0(v_decls_2384_, v_xs_2385_, v_isLambda_boxed_2390_, v_i_2387_, v_x_2388_, v_b_2389_);
lean_dec(v_i_2387_);
lean_dec_ref(v_xs_2385_);
lean_dec_ref(v_decls_2384_);
return v_res_2391_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkBinding(uint8_t v_isLambda_2412_, lean_object* v_decls_2413_, lean_object* v_b_2414_){
_start:
{
lean_object* v___f_2415_; lean_object* v___x_2416_; size_t v_sz_2417_; size_t v___x_2418_; lean_object* v_xs_2419_; lean_object* v___x_2420_; lean_object* v___f_2421_; lean_object* v_b_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; 
v___f_2415_ = ((lean_object*)(l_Lean_Meta_Closure_mkBinding___closed__0));
v___x_2416_ = ((lean_object*)(l_Lean_Meta_Closure_mkBinding___closed__10));
v_sz_2417_ = lean_array_size(v_decls_2413_);
v___x_2418_ = ((size_t)0ULL);
lean_inc_ref_n(v_decls_2413_, 2);
v_xs_2419_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2416_, v___f_2415_, v_sz_2417_, v___x_2418_, v_decls_2413_);
v___x_2420_ = lean_box(v_isLambda_2412_);
lean_inc(v_xs_2419_);
v___f_2421_ = lean_alloc_closure((void*)(l_Lean_Meta_Closure_mkBinding___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2421_, 0, v_decls_2413_);
lean_closure_set(v___f_2421_, 1, v_xs_2419_);
lean_closure_set(v___f_2421_, 2, v___x_2420_);
v_b_2422_ = lean_expr_abstract(v_b_2414_, v_xs_2419_);
lean_dec(v_xs_2419_);
v___x_2423_ = lean_array_get_size(v_decls_2413_);
lean_dec_ref(v_decls_2413_);
v___x_2424_ = l_Nat_foldRev___redArg(v___x_2423_, v___f_2421_, v_b_2422_);
return v___x_2424_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkBinding___boxed(lean_object* v_isLambda_2425_, lean_object* v_decls_2426_, lean_object* v_b_2427_){
_start:
{
uint8_t v_isLambda_boxed_2428_; lean_object* v_res_2429_; 
v_isLambda_boxed_2428_ = lean_unbox(v_isLambda_2425_);
v_res_2429_ = l_Lean_Meta_Closure_mkBinding(v_isLambda_boxed_2428_, v_decls_2426_, v_b_2427_);
lean_dec_ref(v_b_2427_);
return v_res_2429_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Closure_mkLambda_spec__0(size_t v_sz_2430_, size_t v_i_2431_, lean_object* v_bs_2432_){
_start:
{
uint8_t v___x_2433_; 
v___x_2433_ = lean_usize_dec_lt(v_i_2431_, v_sz_2430_);
if (v___x_2433_ == 0)
{
return v_bs_2432_;
}
else
{
lean_object* v_v_2434_; lean_object* v___x_2435_; lean_object* v_bs_x27_2436_; lean_object* v___x_2437_; size_t v___x_2438_; size_t v___x_2439_; lean_object* v___x_2440_; 
v_v_2434_ = lean_array_uget(v_bs_2432_, v_i_2431_);
v___x_2435_ = lean_unsigned_to_nat(0u);
v_bs_x27_2436_ = lean_array_uset(v_bs_2432_, v_i_2431_, v___x_2435_);
v___x_2437_ = l_Lean_LocalDecl_toExpr(v_v_2434_);
v___x_2438_ = ((size_t)1ULL);
v___x_2439_ = lean_usize_add(v_i_2431_, v___x_2438_);
v___x_2440_ = lean_array_uset(v_bs_x27_2436_, v_i_2431_, v___x_2437_);
v_i_2431_ = v___x_2439_;
v_bs_2432_ = v___x_2440_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Closure_mkLambda_spec__0___boxed(lean_object* v_sz_2442_, lean_object* v_i_2443_, lean_object* v_bs_2444_){
_start:
{
size_t v_sz_boxed_2445_; size_t v_i_boxed_2446_; lean_object* v_res_2447_; 
v_sz_boxed_2445_ = lean_unbox_usize(v_sz_2442_);
lean_dec(v_sz_2442_);
v_i_boxed_2446_ = lean_unbox_usize(v_i_2443_);
lean_dec(v_i_2443_);
v_res_2447_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Closure_mkLambda_spec__0(v_sz_boxed_2445_, v_i_boxed_2446_, v_bs_2444_);
return v_res_2447_;
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_Meta_Closure_mkLambda_spec__1_spec__1(lean_object* v_decls_2448_, lean_object* v_xs_2449_, lean_object* v_x_2450_, lean_object* v_x_2451_){
_start:
{
lean_object* v_zero_2452_; uint8_t v_isZero_2453_; 
v_zero_2452_ = lean_unsigned_to_nat(0u);
v_isZero_2453_ = lean_nat_dec_eq(v_x_2450_, v_zero_2452_);
if (v_isZero_2453_ == 1)
{
lean_dec(v_x_2450_);
return v_x_2451_;
}
else
{
lean_object* v_one_2454_; lean_object* v_n_2455_; lean_object* v_decl_2456_; 
v_one_2454_ = lean_unsigned_to_nat(1u);
v_n_2455_ = lean_nat_sub(v_x_2450_, v_one_2454_);
lean_dec(v_x_2450_);
v_decl_2456_ = lean_array_fget_borrowed(v_decls_2448_, v_n_2455_);
if (lean_obj_tag(v_decl_2456_) == 0)
{
lean_object* v_userName_2457_; lean_object* v_type_2458_; uint8_t v_bi_2459_; lean_object* v_ty_2460_; lean_object* v___x_2461_; 
v_userName_2457_ = lean_ctor_get(v_decl_2456_, 2);
v_type_2458_ = lean_ctor_get(v_decl_2456_, 3);
v_bi_2459_ = lean_ctor_get_uint8(v_decl_2456_, sizeof(void*)*4);
v_ty_2460_ = lean_expr_abstract_range(v_type_2458_, v_n_2455_, v_xs_2449_);
lean_inc(v_userName_2457_);
v___x_2461_ = l_Lean_mkLambda(v_userName_2457_, v_bi_2459_, v_ty_2460_, v_x_2451_);
v_x_2450_ = v_n_2455_;
v_x_2451_ = v___x_2461_;
goto _start;
}
else
{
lean_object* v_userName_2463_; lean_object* v_type_2464_; lean_object* v_value_2465_; uint8_t v_nondep_2466_; uint8_t v___x_2467_; 
v_userName_2463_ = lean_ctor_get(v_decl_2456_, 2);
v_type_2464_ = lean_ctor_get(v_decl_2456_, 3);
v_value_2465_ = lean_ctor_get(v_decl_2456_, 4);
v_nondep_2466_ = lean_ctor_get_uint8(v_decl_2456_, sizeof(void*)*5);
v___x_2467_ = lean_expr_has_loose_bvar(v_x_2451_, v_zero_2452_);
if (v___x_2467_ == 0)
{
lean_object* v___x_2468_; 
v___x_2468_ = lean_expr_lower_loose_bvars(v_x_2451_, v_one_2454_, v_one_2454_);
lean_dec_ref(v_x_2451_);
v_x_2450_ = v_n_2455_;
v_x_2451_ = v___x_2468_;
goto _start;
}
else
{
lean_object* v_ty_2470_; lean_object* v_val_2471_; lean_object* v___x_2472_; 
v_ty_2470_ = lean_expr_abstract_range(v_type_2464_, v_n_2455_, v_xs_2449_);
v_val_2471_ = lean_expr_abstract_range(v_value_2465_, v_n_2455_, v_xs_2449_);
lean_inc(v_userName_2463_);
v___x_2472_ = l_Lean_Expr_letE___override(v_userName_2463_, v_ty_2470_, v_val_2471_, v_x_2451_, v_nondep_2466_);
v_x_2450_ = v_n_2455_;
v_x_2451_ = v___x_2472_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_Meta_Closure_mkLambda_spec__1_spec__1___boxed(lean_object* v_decls_2474_, lean_object* v_xs_2475_, lean_object* v_x_2476_, lean_object* v_x_2477_){
_start:
{
lean_object* v_res_2478_; 
v_res_2478_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_Meta_Closure_mkLambda_spec__1_spec__1(v_decls_2474_, v_xs_2475_, v_x_2476_, v_x_2477_);
lean_dec_ref(v_xs_2475_);
lean_dec_ref(v_decls_2474_);
return v_res_2478_;
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Lean_Meta_Closure_mkLambda_spec__1(lean_object* v_decls_2479_, lean_object* v_xs_2480_, lean_object* v_x_2481_, lean_object* v_x_2482_){
_start:
{
lean_object* v_zero_2483_; uint8_t v_isZero_2484_; 
v_zero_2483_ = lean_unsigned_to_nat(0u);
v_isZero_2484_ = lean_nat_dec_eq(v_x_2481_, v_zero_2483_);
if (v_isZero_2484_ == 1)
{
return v_x_2482_;
}
else
{
lean_object* v_one_2485_; lean_object* v_n_2486_; lean_object* v_decl_2487_; 
v_one_2485_ = lean_unsigned_to_nat(1u);
v_n_2486_ = lean_nat_sub(v_x_2481_, v_one_2485_);
v_decl_2487_ = lean_array_fget_borrowed(v_decls_2479_, v_n_2486_);
if (lean_obj_tag(v_decl_2487_) == 0)
{
lean_object* v_userName_2488_; lean_object* v_type_2489_; uint8_t v_bi_2490_; lean_object* v_ty_2491_; lean_object* v___x_2492_; lean_object* v___x_2493_; 
v_userName_2488_ = lean_ctor_get(v_decl_2487_, 2);
v_type_2489_ = lean_ctor_get(v_decl_2487_, 3);
v_bi_2490_ = lean_ctor_get_uint8(v_decl_2487_, sizeof(void*)*4);
v_ty_2491_ = lean_expr_abstract_range(v_type_2489_, v_n_2486_, v_xs_2480_);
lean_inc(v_userName_2488_);
v___x_2492_ = l_Lean_mkLambda(v_userName_2488_, v_bi_2490_, v_ty_2491_, v_x_2482_);
v___x_2493_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_Meta_Closure_mkLambda_spec__1_spec__1(v_decls_2479_, v_xs_2480_, v_n_2486_, v___x_2492_);
return v___x_2493_;
}
else
{
lean_object* v_userName_2494_; lean_object* v_type_2495_; lean_object* v_value_2496_; uint8_t v_nondep_2497_; uint8_t v___x_2498_; 
v_userName_2494_ = lean_ctor_get(v_decl_2487_, 2);
v_type_2495_ = lean_ctor_get(v_decl_2487_, 3);
v_value_2496_ = lean_ctor_get(v_decl_2487_, 4);
v_nondep_2497_ = lean_ctor_get_uint8(v_decl_2487_, sizeof(void*)*5);
v___x_2498_ = lean_expr_has_loose_bvar(v_x_2482_, v_zero_2483_);
if (v___x_2498_ == 0)
{
lean_object* v___x_2499_; lean_object* v___x_2500_; 
v___x_2499_ = lean_expr_lower_loose_bvars(v_x_2482_, v_one_2485_, v_one_2485_);
lean_dec_ref(v_x_2482_);
v___x_2500_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_Meta_Closure_mkLambda_spec__1_spec__1(v_decls_2479_, v_xs_2480_, v_n_2486_, v___x_2499_);
return v___x_2500_;
}
else
{
lean_object* v_ty_2501_; lean_object* v_val_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; 
v_ty_2501_ = lean_expr_abstract_range(v_type_2495_, v_n_2486_, v_xs_2480_);
v_val_2502_ = lean_expr_abstract_range(v_value_2496_, v_n_2486_, v_xs_2480_);
lean_inc(v_userName_2494_);
v___x_2503_ = l_Lean_Expr_letE___override(v_userName_2494_, v_ty_2501_, v_val_2502_, v_x_2482_, v_nondep_2497_);
v___x_2504_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_Meta_Closure_mkLambda_spec__1_spec__1(v_decls_2479_, v_xs_2480_, v_n_2486_, v___x_2503_);
return v___x_2504_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Lean_Meta_Closure_mkLambda_spec__1___boxed(lean_object* v_decls_2505_, lean_object* v_xs_2506_, lean_object* v_x_2507_, lean_object* v_x_2508_){
_start:
{
lean_object* v_res_2509_; 
v_res_2509_ = l_Nat_foldRev___at___00Lean_Meta_Closure_mkLambda_spec__1(v_decls_2505_, v_xs_2506_, v_x_2507_, v_x_2508_);
lean_dec(v_x_2507_);
lean_dec_ref(v_xs_2506_);
lean_dec_ref(v_decls_2505_);
return v_res_2509_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkLambda(lean_object* v_decls_2510_, lean_object* v_b_2511_){
_start:
{
size_t v_sz_2512_; size_t v___x_2513_; lean_object* v_xs_2514_; lean_object* v_b_2515_; lean_object* v___x_2516_; lean_object* v___x_2517_; 
v_sz_2512_ = lean_array_size(v_decls_2510_);
v___x_2513_ = ((size_t)0ULL);
lean_inc_ref(v_decls_2510_);
v_xs_2514_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Closure_mkLambda_spec__0(v_sz_2512_, v___x_2513_, v_decls_2510_);
v_b_2515_ = lean_expr_abstract(v_b_2511_, v_xs_2514_);
v___x_2516_ = lean_array_get_size(v_decls_2510_);
v___x_2517_ = l_Nat_foldRev___at___00Lean_Meta_Closure_mkLambda_spec__1(v_decls_2510_, v_xs_2514_, v___x_2516_, v_b_2515_);
lean_dec_ref(v_xs_2514_);
lean_dec_ref(v_decls_2510_);
return v___x_2517_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkLambda___boxed(lean_object* v_decls_2518_, lean_object* v_b_2519_){
_start:
{
lean_object* v_res_2520_; 
v_res_2520_ = l_Lean_Meta_Closure_mkLambda(v_decls_2518_, v_b_2519_);
lean_dec_ref(v_b_2519_);
return v_res_2520_;
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_Meta_Closure_mkForall_spec__0_spec__0(lean_object* v_decls_2521_, lean_object* v_xs_2522_, lean_object* v_x_2523_, lean_object* v_x_2524_){
_start:
{
lean_object* v_zero_2525_; uint8_t v_isZero_2526_; 
v_zero_2525_ = lean_unsigned_to_nat(0u);
v_isZero_2526_ = lean_nat_dec_eq(v_x_2523_, v_zero_2525_);
if (v_isZero_2526_ == 1)
{
lean_dec(v_x_2523_);
return v_x_2524_;
}
else
{
lean_object* v_one_2527_; lean_object* v_n_2528_; lean_object* v_decl_2529_; 
v_one_2527_ = lean_unsigned_to_nat(1u);
v_n_2528_ = lean_nat_sub(v_x_2523_, v_one_2527_);
lean_dec(v_x_2523_);
v_decl_2529_ = lean_array_fget_borrowed(v_decls_2521_, v_n_2528_);
if (lean_obj_tag(v_decl_2529_) == 0)
{
lean_object* v_userName_2530_; lean_object* v_type_2531_; uint8_t v_bi_2532_; lean_object* v_ty_2533_; lean_object* v___x_2534_; 
v_userName_2530_ = lean_ctor_get(v_decl_2529_, 2);
v_type_2531_ = lean_ctor_get(v_decl_2529_, 3);
v_bi_2532_ = lean_ctor_get_uint8(v_decl_2529_, sizeof(void*)*4);
v_ty_2533_ = lean_expr_abstract_range(v_type_2531_, v_n_2528_, v_xs_2522_);
lean_inc(v_userName_2530_);
v___x_2534_ = l_Lean_mkForall(v_userName_2530_, v_bi_2532_, v_ty_2533_, v_x_2524_);
v_x_2523_ = v_n_2528_;
v_x_2524_ = v___x_2534_;
goto _start;
}
else
{
lean_object* v_userName_2536_; lean_object* v_type_2537_; lean_object* v_value_2538_; uint8_t v_nondep_2539_; uint8_t v___x_2540_; 
v_userName_2536_ = lean_ctor_get(v_decl_2529_, 2);
v_type_2537_ = lean_ctor_get(v_decl_2529_, 3);
v_value_2538_ = lean_ctor_get(v_decl_2529_, 4);
v_nondep_2539_ = lean_ctor_get_uint8(v_decl_2529_, sizeof(void*)*5);
v___x_2540_ = lean_expr_has_loose_bvar(v_x_2524_, v_zero_2525_);
if (v___x_2540_ == 0)
{
lean_object* v___x_2541_; 
v___x_2541_ = lean_expr_lower_loose_bvars(v_x_2524_, v_one_2527_, v_one_2527_);
lean_dec_ref(v_x_2524_);
v_x_2523_ = v_n_2528_;
v_x_2524_ = v___x_2541_;
goto _start;
}
else
{
lean_object* v_ty_2543_; lean_object* v_val_2544_; lean_object* v___x_2545_; 
v_ty_2543_ = lean_expr_abstract_range(v_type_2537_, v_n_2528_, v_xs_2522_);
v_val_2544_ = lean_expr_abstract_range(v_value_2538_, v_n_2528_, v_xs_2522_);
lean_inc(v_userName_2536_);
v___x_2545_ = l_Lean_Expr_letE___override(v_userName_2536_, v_ty_2543_, v_val_2544_, v_x_2524_, v_nondep_2539_);
v_x_2523_ = v_n_2528_;
v_x_2524_ = v___x_2545_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_Meta_Closure_mkForall_spec__0_spec__0___boxed(lean_object* v_decls_2547_, lean_object* v_xs_2548_, lean_object* v_x_2549_, lean_object* v_x_2550_){
_start:
{
lean_object* v_res_2551_; 
v_res_2551_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_Meta_Closure_mkForall_spec__0_spec__0(v_decls_2547_, v_xs_2548_, v_x_2549_, v_x_2550_);
lean_dec_ref(v_xs_2548_);
lean_dec_ref(v_decls_2547_);
return v_res_2551_;
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Lean_Meta_Closure_mkForall_spec__0(lean_object* v_decls_2552_, lean_object* v_xs_2553_, lean_object* v_x_2554_, lean_object* v_x_2555_){
_start:
{
lean_object* v_zero_2556_; uint8_t v_isZero_2557_; 
v_zero_2556_ = lean_unsigned_to_nat(0u);
v_isZero_2557_ = lean_nat_dec_eq(v_x_2554_, v_zero_2556_);
if (v_isZero_2557_ == 1)
{
return v_x_2555_;
}
else
{
lean_object* v_one_2558_; lean_object* v_n_2559_; lean_object* v_decl_2560_; 
v_one_2558_ = lean_unsigned_to_nat(1u);
v_n_2559_ = lean_nat_sub(v_x_2554_, v_one_2558_);
v_decl_2560_ = lean_array_fget_borrowed(v_decls_2552_, v_n_2559_);
if (lean_obj_tag(v_decl_2560_) == 0)
{
lean_object* v_userName_2561_; lean_object* v_type_2562_; uint8_t v_bi_2563_; lean_object* v_ty_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; 
v_userName_2561_ = lean_ctor_get(v_decl_2560_, 2);
v_type_2562_ = lean_ctor_get(v_decl_2560_, 3);
v_bi_2563_ = lean_ctor_get_uint8(v_decl_2560_, sizeof(void*)*4);
v_ty_2564_ = lean_expr_abstract_range(v_type_2562_, v_n_2559_, v_xs_2553_);
lean_inc(v_userName_2561_);
v___x_2565_ = l_Lean_mkForall(v_userName_2561_, v_bi_2563_, v_ty_2564_, v_x_2555_);
v___x_2566_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_Meta_Closure_mkForall_spec__0_spec__0(v_decls_2552_, v_xs_2553_, v_n_2559_, v___x_2565_);
return v___x_2566_;
}
else
{
lean_object* v_userName_2567_; lean_object* v_type_2568_; lean_object* v_value_2569_; uint8_t v_nondep_2570_; uint8_t v___x_2571_; 
v_userName_2567_ = lean_ctor_get(v_decl_2560_, 2);
v_type_2568_ = lean_ctor_get(v_decl_2560_, 3);
v_value_2569_ = lean_ctor_get(v_decl_2560_, 4);
v_nondep_2570_ = lean_ctor_get_uint8(v_decl_2560_, sizeof(void*)*5);
v___x_2571_ = lean_expr_has_loose_bvar(v_x_2555_, v_zero_2556_);
if (v___x_2571_ == 0)
{
lean_object* v___x_2572_; lean_object* v___x_2573_; 
v___x_2572_ = lean_expr_lower_loose_bvars(v_x_2555_, v_one_2558_, v_one_2558_);
lean_dec_ref(v_x_2555_);
v___x_2573_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_Meta_Closure_mkForall_spec__0_spec__0(v_decls_2552_, v_xs_2553_, v_n_2559_, v___x_2572_);
return v___x_2573_;
}
else
{
lean_object* v_ty_2574_; lean_object* v_val_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; 
v_ty_2574_ = lean_expr_abstract_range(v_type_2568_, v_n_2559_, v_xs_2553_);
v_val_2575_ = lean_expr_abstract_range(v_value_2569_, v_n_2559_, v_xs_2553_);
lean_inc(v_userName_2567_);
v___x_2576_ = l_Lean_Expr_letE___override(v_userName_2567_, v_ty_2574_, v_val_2575_, v_x_2555_, v_nondep_2570_);
v___x_2577_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_Meta_Closure_mkForall_spec__0_spec__0(v_decls_2552_, v_xs_2553_, v_n_2559_, v___x_2576_);
return v___x_2577_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Lean_Meta_Closure_mkForall_spec__0___boxed(lean_object* v_decls_2578_, lean_object* v_xs_2579_, lean_object* v_x_2580_, lean_object* v_x_2581_){
_start:
{
lean_object* v_res_2582_; 
v_res_2582_ = l_Nat_foldRev___at___00Lean_Meta_Closure_mkForall_spec__0(v_decls_2578_, v_xs_2579_, v_x_2580_, v_x_2581_);
lean_dec(v_x_2580_);
lean_dec_ref(v_xs_2579_);
lean_dec_ref(v_decls_2578_);
return v_res_2582_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkForall(lean_object* v_decls_2583_, lean_object* v_b_2584_){
_start:
{
size_t v_sz_2585_; size_t v___x_2586_; lean_object* v_xs_2587_; lean_object* v_b_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; 
v_sz_2585_ = lean_array_size(v_decls_2583_);
v___x_2586_ = ((size_t)0ULL);
lean_inc_ref(v_decls_2583_);
v_xs_2587_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Closure_mkLambda_spec__0(v_sz_2585_, v___x_2586_, v_decls_2583_);
v_b_2588_ = lean_expr_abstract(v_b_2584_, v_xs_2587_);
v___x_2589_ = lean_array_get_size(v_decls_2583_);
v___x_2590_ = l_Nat_foldRev___at___00Lean_Meta_Closure_mkForall_spec__0(v_decls_2583_, v_xs_2587_, v___x_2589_, v_b_2588_);
lean_dec_ref(v_xs_2587_);
lean_dec_ref(v_decls_2583_);
return v___x_2590_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkForall___boxed(lean_object* v_decls_2591_, lean_object* v_b_2592_){
_start:
{
lean_object* v_res_2593_; 
v_res_2593_ = l_Lean_Meta_Closure_mkForall(v_decls_2591_, v_b_2592_);
lean_dec_ref(v_b_2592_);
return v_res_2593_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkValueTypeClosureAux___lam__0(lean_object* v_a_2594_, lean_object* v_zetaDeltaFVarIds_2595_, lean_object* v_a_x3f_2596_){
_start:
{
lean_object* v___x_2598_; lean_object* v_mctx_2599_; lean_object* v_cache_2600_; lean_object* v_postponed_2601_; lean_object* v_diag_2602_; lean_object* v___x_2604_; uint8_t v_isShared_2605_; uint8_t v_isSharedCheck_2612_; 
v___x_2598_ = lean_st_ref_take(v_a_2594_);
v_mctx_2599_ = lean_ctor_get(v___x_2598_, 0);
v_cache_2600_ = lean_ctor_get(v___x_2598_, 1);
v_postponed_2601_ = lean_ctor_get(v___x_2598_, 3);
v_diag_2602_ = lean_ctor_get(v___x_2598_, 4);
v_isSharedCheck_2612_ = !lean_is_exclusive(v___x_2598_);
if (v_isSharedCheck_2612_ == 0)
{
lean_object* v_unused_2613_; 
v_unused_2613_ = lean_ctor_get(v___x_2598_, 2);
lean_dec(v_unused_2613_);
v___x_2604_ = v___x_2598_;
v_isShared_2605_ = v_isSharedCheck_2612_;
goto v_resetjp_2603_;
}
else
{
lean_inc(v_diag_2602_);
lean_inc(v_postponed_2601_);
lean_inc(v_cache_2600_);
lean_inc(v_mctx_2599_);
lean_dec(v___x_2598_);
v___x_2604_ = lean_box(0);
v_isShared_2605_ = v_isSharedCheck_2612_;
goto v_resetjp_2603_;
}
v_resetjp_2603_:
{
lean_object* v___x_2607_; 
if (v_isShared_2605_ == 0)
{
lean_ctor_set(v___x_2604_, 2, v_zetaDeltaFVarIds_2595_);
v___x_2607_ = v___x_2604_;
goto v_reusejp_2606_;
}
else
{
lean_object* v_reuseFailAlloc_2611_; 
v_reuseFailAlloc_2611_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2611_, 0, v_mctx_2599_);
lean_ctor_set(v_reuseFailAlloc_2611_, 1, v_cache_2600_);
lean_ctor_set(v_reuseFailAlloc_2611_, 2, v_zetaDeltaFVarIds_2595_);
lean_ctor_set(v_reuseFailAlloc_2611_, 3, v_postponed_2601_);
lean_ctor_set(v_reuseFailAlloc_2611_, 4, v_diag_2602_);
v___x_2607_ = v_reuseFailAlloc_2611_;
goto v_reusejp_2606_;
}
v_reusejp_2606_:
{
lean_object* v___x_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; 
v___x_2608_ = lean_st_ref_set(v_a_2594_, v___x_2607_);
v___x_2609_ = lean_box(0);
v___x_2610_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2610_, 0, v___x_2609_);
return v___x_2610_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkValueTypeClosureAux___lam__0___boxed(lean_object* v_a_2614_, lean_object* v_zetaDeltaFVarIds_2615_, lean_object* v_a_x3f_2616_, lean_object* v___y_2617_){
_start:
{
lean_object* v_res_2618_; 
v_res_2618_ = l_Lean_Meta_Closure_mkValueTypeClosureAux___lam__0(v_a_2614_, v_zetaDeltaFVarIds_2615_, v_a_x3f_2616_);
lean_dec(v_a_x3f_2616_);
lean_dec(v_a_2614_);
return v_res_2618_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkValueTypeClosureAux___lam__1(lean_object* v_a_2619_, lean_object* v_cache_2620_, lean_object* v_a_x3f_2621_){
_start:
{
lean_object* v___x_2623_; lean_object* v_mctx_2624_; lean_object* v_zetaDeltaFVarIds_2625_; lean_object* v_postponed_2626_; lean_object* v_diag_2627_; lean_object* v___x_2629_; uint8_t v_isShared_2630_; uint8_t v_isSharedCheck_2637_; 
v___x_2623_ = lean_st_ref_take(v_a_2619_);
v_mctx_2624_ = lean_ctor_get(v___x_2623_, 0);
v_zetaDeltaFVarIds_2625_ = lean_ctor_get(v___x_2623_, 2);
v_postponed_2626_ = lean_ctor_get(v___x_2623_, 3);
v_diag_2627_ = lean_ctor_get(v___x_2623_, 4);
v_isSharedCheck_2637_ = !lean_is_exclusive(v___x_2623_);
if (v_isSharedCheck_2637_ == 0)
{
lean_object* v_unused_2638_; 
v_unused_2638_ = lean_ctor_get(v___x_2623_, 1);
lean_dec(v_unused_2638_);
v___x_2629_ = v___x_2623_;
v_isShared_2630_ = v_isSharedCheck_2637_;
goto v_resetjp_2628_;
}
else
{
lean_inc(v_diag_2627_);
lean_inc(v_postponed_2626_);
lean_inc(v_zetaDeltaFVarIds_2625_);
lean_inc(v_mctx_2624_);
lean_dec(v___x_2623_);
v___x_2629_ = lean_box(0);
v_isShared_2630_ = v_isSharedCheck_2637_;
goto v_resetjp_2628_;
}
v_resetjp_2628_:
{
lean_object* v___x_2632_; 
if (v_isShared_2630_ == 0)
{
lean_ctor_set(v___x_2629_, 1, v_cache_2620_);
v___x_2632_ = v___x_2629_;
goto v_reusejp_2631_;
}
else
{
lean_object* v_reuseFailAlloc_2636_; 
v_reuseFailAlloc_2636_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2636_, 0, v_mctx_2624_);
lean_ctor_set(v_reuseFailAlloc_2636_, 1, v_cache_2620_);
lean_ctor_set(v_reuseFailAlloc_2636_, 2, v_zetaDeltaFVarIds_2625_);
lean_ctor_set(v_reuseFailAlloc_2636_, 3, v_postponed_2626_);
lean_ctor_set(v_reuseFailAlloc_2636_, 4, v_diag_2627_);
v___x_2632_ = v_reuseFailAlloc_2636_;
goto v_reusejp_2631_;
}
v_reusejp_2631_:
{
lean_object* v___x_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; 
v___x_2633_ = lean_st_ref_set(v_a_2619_, v___x_2632_);
v___x_2634_ = lean_box(0);
v___x_2635_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2635_, 0, v___x_2634_);
return v___x_2635_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkValueTypeClosureAux___lam__1___boxed(lean_object* v_a_2639_, lean_object* v_cache_2640_, lean_object* v_a_x3f_2641_, lean_object* v___y_2642_){
_start:
{
lean_object* v_res_2643_; 
v_res_2643_ = l_Lean_Meta_Closure_mkValueTypeClosureAux___lam__1(v_a_2639_, v_cache_2640_, v_a_x3f_2641_);
lean_dec(v_a_x3f_2641_);
lean_dec(v_a_2639_);
return v_res_2643_;
}
}
static lean_object* _init_l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__0(void){
_start:
{
lean_object* v___x_2644_; 
v___x_2644_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2644_;
}
}
static lean_object* _init_l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__1(void){
_start:
{
lean_object* v___x_2645_; lean_object* v___x_2646_; 
v___x_2645_ = lean_obj_once(&l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__0, &l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__0_once, _init_l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__0);
v___x_2646_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2646_, 0, v___x_2645_);
return v___x_2646_;
}
}
static lean_object* _init_l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__2(void){
_start:
{
lean_object* v___x_2647_; lean_object* v___x_2648_; 
v___x_2647_ = lean_obj_once(&l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__1, &l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__1_once, _init_l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__1);
v___x_2648_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2648_, 0, v___x_2647_);
lean_ctor_set(v___x_2648_, 1, v___x_2647_);
lean_ctor_set(v___x_2648_, 2, v___x_2647_);
lean_ctor_set(v___x_2648_, 3, v___x_2647_);
lean_ctor_set(v___x_2648_, 4, v___x_2647_);
lean_ctor_set(v___x_2648_, 5, v___x_2647_);
return v___x_2648_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkValueTypeClosureAux(lean_object* v_type_2649_, lean_object* v_value_2650_, uint8_t v_a_2651_, lean_object* v_a_2652_, lean_object* v_a_2653_, lean_object* v_a_2654_, lean_object* v_a_2655_, lean_object* v_a_2656_){
_start:
{
lean_object* v___x_2658_; lean_object* v___x_2659_; lean_object* v_mctx_2660_; lean_object* v_zetaDeltaFVarIds_2661_; lean_object* v_postponed_2662_; lean_object* v_diag_2663_; lean_object* v___x_2665_; uint8_t v_isShared_2666_; uint8_t v_isSharedCheck_2743_; 
v___x_2658_ = lean_st_ref_get(v_a_2654_);
v___x_2659_ = lean_st_ref_take(v_a_2654_);
v_mctx_2660_ = lean_ctor_get(v___x_2659_, 0);
v_zetaDeltaFVarIds_2661_ = lean_ctor_get(v___x_2659_, 2);
v_postponed_2662_ = lean_ctor_get(v___x_2659_, 3);
v_diag_2663_ = lean_ctor_get(v___x_2659_, 4);
v_isSharedCheck_2743_ = !lean_is_exclusive(v___x_2659_);
if (v_isSharedCheck_2743_ == 0)
{
lean_object* v_unused_2744_; 
v_unused_2744_ = lean_ctor_get(v___x_2659_, 1);
lean_dec(v_unused_2744_);
v___x_2665_ = v___x_2659_;
v_isShared_2666_ = v_isSharedCheck_2743_;
goto v_resetjp_2664_;
}
else
{
lean_inc(v_diag_2663_);
lean_inc(v_postponed_2662_);
lean_inc(v_zetaDeltaFVarIds_2661_);
lean_inc(v_mctx_2660_);
lean_dec(v___x_2659_);
v___x_2665_ = lean_box(0);
v_isShared_2666_ = v_isSharedCheck_2743_;
goto v_resetjp_2664_;
}
v_resetjp_2664_:
{
lean_object* v___x_2667_; lean_object* v___x_2669_; 
v___x_2667_ = lean_obj_once(&l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__2, &l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__2_once, _init_l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__2);
if (v_isShared_2666_ == 0)
{
lean_ctor_set(v___x_2665_, 1, v___x_2667_);
v___x_2669_ = v___x_2665_;
goto v_reusejp_2668_;
}
else
{
lean_object* v_reuseFailAlloc_2742_; 
v_reuseFailAlloc_2742_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2742_, 0, v_mctx_2660_);
lean_ctor_set(v_reuseFailAlloc_2742_, 1, v___x_2667_);
lean_ctor_set(v_reuseFailAlloc_2742_, 2, v_zetaDeltaFVarIds_2661_);
lean_ctor_set(v_reuseFailAlloc_2742_, 3, v_postponed_2662_);
lean_ctor_set(v_reuseFailAlloc_2742_, 4, v_diag_2663_);
v___x_2669_ = v_reuseFailAlloc_2742_;
goto v_reusejp_2668_;
}
v_reusejp_2668_:
{
lean_object* v___x_2670_; lean_object* v___x_2671_; lean_object* v_mctx_2672_; lean_object* v_cache_2673_; lean_object* v_zetaDeltaFVarIds_2674_; lean_object* v_postponed_2675_; lean_object* v_diag_2676_; lean_object* v___x_2678_; uint8_t v_isShared_2679_; uint8_t v_isSharedCheck_2741_; 
v___x_2670_ = lean_st_ref_set(v_a_2654_, v___x_2669_);
v___x_2671_ = lean_st_ref_take(v_a_2654_);
v_mctx_2672_ = lean_ctor_get(v___x_2671_, 0);
v_cache_2673_ = lean_ctor_get(v___x_2671_, 1);
v_zetaDeltaFVarIds_2674_ = lean_ctor_get(v___x_2671_, 2);
v_postponed_2675_ = lean_ctor_get(v___x_2671_, 3);
v_diag_2676_ = lean_ctor_get(v___x_2671_, 4);
v_isSharedCheck_2741_ = !lean_is_exclusive(v___x_2671_);
if (v_isSharedCheck_2741_ == 0)
{
v___x_2678_ = v___x_2671_;
v_isShared_2679_ = v_isSharedCheck_2741_;
goto v_resetjp_2677_;
}
else
{
lean_inc(v_diag_2676_);
lean_inc(v_postponed_2675_);
lean_inc(v_zetaDeltaFVarIds_2674_);
lean_inc(v_cache_2673_);
lean_inc(v_mctx_2672_);
lean_dec(v___x_2671_);
v___x_2678_ = lean_box(0);
v_isShared_2679_ = v_isSharedCheck_2741_;
goto v_resetjp_2677_;
}
v_resetjp_2677_:
{
lean_object* v___x_2680_; lean_object* v___x_2682_; 
v___x_2680_ = lean_box(1);
if (v_isShared_2679_ == 0)
{
lean_ctor_set(v___x_2678_, 2, v___x_2680_);
v___x_2682_ = v___x_2678_;
goto v_reusejp_2681_;
}
else
{
lean_object* v_reuseFailAlloc_2740_; 
v_reuseFailAlloc_2740_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2740_, 0, v_mctx_2672_);
lean_ctor_set(v_reuseFailAlloc_2740_, 1, v_cache_2673_);
lean_ctor_set(v_reuseFailAlloc_2740_, 2, v___x_2680_);
lean_ctor_set(v_reuseFailAlloc_2740_, 3, v_postponed_2675_);
lean_ctor_set(v_reuseFailAlloc_2740_, 4, v_diag_2676_);
v___x_2682_ = v_reuseFailAlloc_2740_;
goto v_reusejp_2681_;
}
v_reusejp_2681_:
{
lean_object* v___x_2683_; lean_object* v_cache_2684_; lean_object* v_keyedConfig_2685_; lean_object* v_zetaDeltaSet_2686_; lean_object* v_lctx_2687_; lean_object* v_localInstances_2688_; lean_object* v_defEqCtx_x3f_2689_; lean_object* v_synthPendingDepth_2690_; lean_object* v_canUnfold_x3f_2691_; uint8_t v_univApprox_2692_; uint8_t v_inTypeClassResolution_2693_; uint8_t v_cacheInferType_2694_; lean_object* v_a_2696_; lean_object* v_a_2708_; uint8_t v___x_2711_; lean_object* v___x_2712_; lean_object* v___x_2713_; 
v___x_2683_ = lean_st_ref_set(v_a_2654_, v___x_2682_);
v_cache_2684_ = lean_ctor_get(v___x_2658_, 1);
lean_inc_ref(v_cache_2684_);
lean_dec(v___x_2658_);
v_keyedConfig_2685_ = lean_ctor_get(v_a_2653_, 0);
v_zetaDeltaSet_2686_ = lean_ctor_get(v_a_2653_, 1);
v_lctx_2687_ = lean_ctor_get(v_a_2653_, 2);
v_localInstances_2688_ = lean_ctor_get(v_a_2653_, 3);
v_defEqCtx_x3f_2689_ = lean_ctor_get(v_a_2653_, 4);
v_synthPendingDepth_2690_ = lean_ctor_get(v_a_2653_, 5);
v_canUnfold_x3f_2691_ = lean_ctor_get(v_a_2653_, 6);
v_univApprox_2692_ = lean_ctor_get_uint8(v_a_2653_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2693_ = lean_ctor_get_uint8(v_a_2653_, sizeof(void*)*7 + 2);
v_cacheInferType_2694_ = lean_ctor_get_uint8(v_a_2653_, sizeof(void*)*7 + 3);
v___x_2711_ = 1;
lean_inc(v_canUnfold_x3f_2691_);
lean_inc(v_synthPendingDepth_2690_);
lean_inc(v_defEqCtx_x3f_2689_);
lean_inc_ref(v_localInstances_2688_);
lean_inc_ref(v_lctx_2687_);
lean_inc(v_zetaDeltaSet_2686_);
lean_inc_ref(v_keyedConfig_2685_);
v___x_2712_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2712_, 0, v_keyedConfig_2685_);
lean_ctor_set(v___x_2712_, 1, v_zetaDeltaSet_2686_);
lean_ctor_set(v___x_2712_, 2, v_lctx_2687_);
lean_ctor_set(v___x_2712_, 3, v_localInstances_2688_);
lean_ctor_set(v___x_2712_, 4, v_defEqCtx_x3f_2689_);
lean_ctor_set(v___x_2712_, 5, v_synthPendingDepth_2690_);
lean_ctor_set(v___x_2712_, 6, v_canUnfold_x3f_2691_);
lean_ctor_set_uint8(v___x_2712_, sizeof(void*)*7, v___x_2711_);
lean_ctor_set_uint8(v___x_2712_, sizeof(void*)*7 + 1, v_univApprox_2692_);
lean_ctor_set_uint8(v___x_2712_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2693_);
lean_ctor_set_uint8(v___x_2712_, sizeof(void*)*7 + 3, v_cacheInferType_2694_);
v___x_2713_ = l_Lean_Meta_Closure_collectExpr(v_type_2649_, v_a_2651_, v_a_2652_, v___x_2712_, v_a_2654_, v_a_2655_, v_a_2656_);
if (lean_obj_tag(v___x_2713_) == 0)
{
lean_object* v_a_2714_; lean_object* v___x_2715_; 
v_a_2714_ = lean_ctor_get(v___x_2713_, 0);
lean_inc(v_a_2714_);
lean_dec_ref_known(v___x_2713_, 1);
v___x_2715_ = l_Lean_Meta_Closure_collectExpr(v_value_2650_, v_a_2651_, v_a_2652_, v___x_2712_, v_a_2654_, v_a_2655_, v_a_2656_);
if (lean_obj_tag(v___x_2715_) == 0)
{
lean_object* v_a_2716_; lean_object* v___x_2717_; 
v_a_2716_ = lean_ctor_get(v___x_2715_, 0);
lean_inc(v_a_2716_);
lean_dec_ref_known(v___x_2715_, 1);
v___x_2717_ = l_Lean_Meta_Closure_process(v_a_2651_, v_a_2652_, v___x_2712_, v_a_2654_, v_a_2655_, v_a_2656_);
lean_dec_ref_known(v___x_2712_, 7);
if (lean_obj_tag(v___x_2717_) == 0)
{
lean_object* v___x_2719_; uint8_t v_isShared_2720_; uint8_t v_isSharedCheck_2735_; 
v_isSharedCheck_2735_ = !lean_is_exclusive(v___x_2717_);
if (v_isSharedCheck_2735_ == 0)
{
lean_object* v_unused_2736_; 
v_unused_2736_ = lean_ctor_get(v___x_2717_, 0);
lean_dec(v_unused_2736_);
v___x_2719_ = v___x_2717_;
v_isShared_2720_ = v_isSharedCheck_2735_;
goto v_resetjp_2718_;
}
else
{
lean_dec(v___x_2717_);
v___x_2719_ = lean_box(0);
v_isShared_2720_ = v_isSharedCheck_2735_;
goto v_resetjp_2718_;
}
v_resetjp_2718_:
{
lean_object* v___x_2721_; lean_object* v___x_2723_; 
v___x_2721_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2721_, 0, v_a_2714_);
lean_ctor_set(v___x_2721_, 1, v_a_2716_);
lean_inc_ref(v___x_2721_);
if (v_isShared_2720_ == 0)
{
lean_ctor_set_tag(v___x_2719_, 1);
lean_ctor_set(v___x_2719_, 0, v___x_2721_);
v___x_2723_ = v___x_2719_;
goto v_reusejp_2722_;
}
else
{
lean_object* v_reuseFailAlloc_2734_; 
v_reuseFailAlloc_2734_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2734_, 0, v___x_2721_);
v___x_2723_ = v_reuseFailAlloc_2734_;
goto v_reusejp_2722_;
}
v_reusejp_2722_:
{
lean_object* v___x_2724_; lean_object* v___x_2725_; lean_object* v___x_2727_; uint8_t v_isShared_2728_; uint8_t v_isSharedCheck_2732_; 
v___x_2724_ = l_Lean_Meta_Closure_mkValueTypeClosureAux___lam__0(v_a_2654_, v_zetaDeltaFVarIds_2674_, v___x_2723_);
lean_dec_ref(v___x_2724_);
v___x_2725_ = l_Lean_Meta_Closure_mkValueTypeClosureAux___lam__1(v_a_2654_, v_cache_2684_, v___x_2723_);
lean_dec_ref(v___x_2723_);
v_isSharedCheck_2732_ = !lean_is_exclusive(v___x_2725_);
if (v_isSharedCheck_2732_ == 0)
{
lean_object* v_unused_2733_; 
v_unused_2733_ = lean_ctor_get(v___x_2725_, 0);
lean_dec(v_unused_2733_);
v___x_2727_ = v___x_2725_;
v_isShared_2728_ = v_isSharedCheck_2732_;
goto v_resetjp_2726_;
}
else
{
lean_dec(v___x_2725_);
v___x_2727_ = lean_box(0);
v_isShared_2728_ = v_isSharedCheck_2732_;
goto v_resetjp_2726_;
}
v_resetjp_2726_:
{
lean_object* v___x_2730_; 
if (v_isShared_2728_ == 0)
{
lean_ctor_set(v___x_2727_, 0, v___x_2721_);
v___x_2730_ = v___x_2727_;
goto v_reusejp_2729_;
}
else
{
lean_object* v_reuseFailAlloc_2731_; 
v_reuseFailAlloc_2731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2731_, 0, v___x_2721_);
v___x_2730_ = v_reuseFailAlloc_2731_;
goto v_reusejp_2729_;
}
v_reusejp_2729_:
{
return v___x_2730_;
}
}
}
}
}
else
{
lean_object* v_a_2737_; 
lean_dec(v_a_2716_);
lean_dec(v_a_2714_);
v_a_2737_ = lean_ctor_get(v___x_2717_, 0);
lean_inc(v_a_2737_);
lean_dec_ref_known(v___x_2717_, 1);
v_a_2708_ = v_a_2737_;
goto v___jp_2707_;
}
}
else
{
lean_object* v_a_2738_; 
lean_dec(v_a_2714_);
lean_dec_ref_known(v___x_2712_, 7);
v_a_2738_ = lean_ctor_get(v___x_2715_, 0);
lean_inc(v_a_2738_);
lean_dec_ref_known(v___x_2715_, 1);
v_a_2708_ = v_a_2738_;
goto v___jp_2707_;
}
}
else
{
lean_object* v_a_2739_; 
lean_dec_ref_known(v___x_2712_, 7);
lean_dec_ref(v_value_2650_);
v_a_2739_ = lean_ctor_get(v___x_2713_, 0);
lean_inc(v_a_2739_);
lean_dec_ref_known(v___x_2713_, 1);
v_a_2708_ = v_a_2739_;
goto v___jp_2707_;
}
v___jp_2695_:
{
lean_object* v___x_2697_; lean_object* v___x_2698_; lean_object* v___x_2700_; uint8_t v_isShared_2701_; uint8_t v_isSharedCheck_2705_; 
v___x_2697_ = lean_box(0);
v___x_2698_ = l_Lean_Meta_Closure_mkValueTypeClosureAux___lam__1(v_a_2654_, v_cache_2684_, v___x_2697_);
v_isSharedCheck_2705_ = !lean_is_exclusive(v___x_2698_);
if (v_isSharedCheck_2705_ == 0)
{
lean_object* v_unused_2706_; 
v_unused_2706_ = lean_ctor_get(v___x_2698_, 0);
lean_dec(v_unused_2706_);
v___x_2700_ = v___x_2698_;
v_isShared_2701_ = v_isSharedCheck_2705_;
goto v_resetjp_2699_;
}
else
{
lean_dec(v___x_2698_);
v___x_2700_ = lean_box(0);
v_isShared_2701_ = v_isSharedCheck_2705_;
goto v_resetjp_2699_;
}
v_resetjp_2699_:
{
lean_object* v___x_2703_; 
if (v_isShared_2701_ == 0)
{
lean_ctor_set_tag(v___x_2700_, 1);
lean_ctor_set(v___x_2700_, 0, v_a_2696_);
v___x_2703_ = v___x_2700_;
goto v_reusejp_2702_;
}
else
{
lean_object* v_reuseFailAlloc_2704_; 
v_reuseFailAlloc_2704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2704_, 0, v_a_2696_);
v___x_2703_ = v_reuseFailAlloc_2704_;
goto v_reusejp_2702_;
}
v_reusejp_2702_:
{
return v___x_2703_;
}
}
}
v___jp_2707_:
{
lean_object* v___x_2709_; lean_object* v___x_2710_; 
v___x_2709_ = lean_box(0);
v___x_2710_ = l_Lean_Meta_Closure_mkValueTypeClosureAux___lam__0(v_a_2654_, v_zetaDeltaFVarIds_2674_, v___x_2709_);
lean_dec_ref(v___x_2710_);
v_a_2696_ = v_a_2708_;
goto v___jp_2695_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkValueTypeClosureAux___boxed(lean_object* v_type_2745_, lean_object* v_value_2746_, lean_object* v_a_2747_, lean_object* v_a_2748_, lean_object* v_a_2749_, lean_object* v_a_2750_, lean_object* v_a_2751_, lean_object* v_a_2752_, lean_object* v_a_2753_){
_start:
{
uint8_t v_a_boxed_2754_; lean_object* v_res_2755_; 
v_a_boxed_2754_ = lean_unbox(v_a_2747_);
v_res_2755_ = l_Lean_Meta_Closure_mkValueTypeClosureAux(v_type_2745_, v_value_2746_, v_a_boxed_2754_, v_a_2748_, v_a_2749_, v_a_2750_, v_a_2751_, v_a_2752_);
lean_dec(v_a_2752_);
lean_dec_ref(v_a_2751_);
lean_dec(v_a_2750_);
lean_dec_ref(v_a_2749_);
lean_dec(v_a_2748_);
return v_res_2755_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2___closed__0(void){
_start:
{
lean_object* v___x_2756_; 
v___x_2756_ = l_instMonadEIO(lean_box(0));
return v___x_2756_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2(lean_object* v_msg_2759_, lean_object* v___y_2760_, lean_object* v___y_2761_, lean_object* v___y_2762_){
_start:
{
lean_object* v___x_2764_; lean_object* v___x_2765_; lean_object* v_toApplicative_2766_; lean_object* v___x_2768_; uint8_t v_isShared_2769_; uint8_t v_isSharedCheck_2807_; 
v___x_2764_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2___closed__0, &l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2___closed__0);
v___x_2765_ = l_StateRefT_x27_instMonad___redArg(v___x_2764_);
v_toApplicative_2766_ = lean_ctor_get(v___x_2765_, 0);
v_isSharedCheck_2807_ = !lean_is_exclusive(v___x_2765_);
if (v_isSharedCheck_2807_ == 0)
{
lean_object* v_unused_2808_; 
v_unused_2808_ = lean_ctor_get(v___x_2765_, 1);
lean_dec(v_unused_2808_);
v___x_2768_ = v___x_2765_;
v_isShared_2769_ = v_isSharedCheck_2807_;
goto v_resetjp_2767_;
}
else
{
lean_inc(v_toApplicative_2766_);
lean_dec(v___x_2765_);
v___x_2768_ = lean_box(0);
v_isShared_2769_ = v_isSharedCheck_2807_;
goto v_resetjp_2767_;
}
v_resetjp_2767_:
{
lean_object* v_toFunctor_2770_; lean_object* v_toSeq_2771_; lean_object* v_toSeqLeft_2772_; lean_object* v_toSeqRight_2773_; lean_object* v___x_2775_; uint8_t v_isShared_2776_; uint8_t v_isSharedCheck_2805_; 
v_toFunctor_2770_ = lean_ctor_get(v_toApplicative_2766_, 0);
v_toSeq_2771_ = lean_ctor_get(v_toApplicative_2766_, 2);
v_toSeqLeft_2772_ = lean_ctor_get(v_toApplicative_2766_, 3);
v_toSeqRight_2773_ = lean_ctor_get(v_toApplicative_2766_, 4);
v_isSharedCheck_2805_ = !lean_is_exclusive(v_toApplicative_2766_);
if (v_isSharedCheck_2805_ == 0)
{
lean_object* v_unused_2806_; 
v_unused_2806_ = lean_ctor_get(v_toApplicative_2766_, 1);
lean_dec(v_unused_2806_);
v___x_2775_ = v_toApplicative_2766_;
v_isShared_2776_ = v_isSharedCheck_2805_;
goto v_resetjp_2774_;
}
else
{
lean_inc(v_toSeqRight_2773_);
lean_inc(v_toSeqLeft_2772_);
lean_inc(v_toSeq_2771_);
lean_inc(v_toFunctor_2770_);
lean_dec(v_toApplicative_2766_);
v___x_2775_ = lean_box(0);
v_isShared_2776_ = v_isSharedCheck_2805_;
goto v_resetjp_2774_;
}
v_resetjp_2774_:
{
lean_object* v___f_2777_; lean_object* v___f_2778_; lean_object* v___f_2779_; lean_object* v___f_2780_; lean_object* v___x_2781_; lean_object* v___f_2782_; lean_object* v___f_2783_; lean_object* v___f_2784_; lean_object* v___x_2786_; 
v___f_2777_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2___closed__1));
v___f_2778_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2___closed__2));
lean_inc_ref(v_toFunctor_2770_);
v___f_2779_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2779_, 0, v_toFunctor_2770_);
v___f_2780_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2780_, 0, v_toFunctor_2770_);
v___x_2781_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2781_, 0, v___f_2779_);
lean_ctor_set(v___x_2781_, 1, v___f_2780_);
v___f_2782_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2782_, 0, v_toSeqRight_2773_);
v___f_2783_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2783_, 0, v_toSeqLeft_2772_);
v___f_2784_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2784_, 0, v_toSeq_2771_);
if (v_isShared_2776_ == 0)
{
lean_ctor_set(v___x_2775_, 4, v___f_2782_);
lean_ctor_set(v___x_2775_, 3, v___f_2783_);
lean_ctor_set(v___x_2775_, 2, v___f_2784_);
lean_ctor_set(v___x_2775_, 1, v___f_2777_);
lean_ctor_set(v___x_2775_, 0, v___x_2781_);
v___x_2786_ = v___x_2775_;
goto v_reusejp_2785_;
}
else
{
lean_object* v_reuseFailAlloc_2804_; 
v_reuseFailAlloc_2804_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2804_, 0, v___x_2781_);
lean_ctor_set(v_reuseFailAlloc_2804_, 1, v___f_2777_);
lean_ctor_set(v_reuseFailAlloc_2804_, 2, v___f_2784_);
lean_ctor_set(v_reuseFailAlloc_2804_, 3, v___f_2783_);
lean_ctor_set(v_reuseFailAlloc_2804_, 4, v___f_2782_);
v___x_2786_ = v_reuseFailAlloc_2804_;
goto v_reusejp_2785_;
}
v_reusejp_2785_:
{
lean_object* v___x_2788_; 
if (v_isShared_2769_ == 0)
{
lean_ctor_set(v___x_2768_, 1, v___f_2778_);
lean_ctor_set(v___x_2768_, 0, v___x_2786_);
v___x_2788_ = v___x_2768_;
goto v_reusejp_2787_;
}
else
{
lean_object* v_reuseFailAlloc_2803_; 
v_reuseFailAlloc_2803_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2803_, 0, v___x_2786_);
lean_ctor_set(v_reuseFailAlloc_2803_, 1, v___f_2778_);
v___x_2788_ = v_reuseFailAlloc_2803_;
goto v_reusejp_2787_;
}
v_reusejp_2787_:
{
lean_object* v___f_2789_; lean_object* v___f_2790_; lean_object* v___f_2791_; lean_object* v___f_2792_; lean_object* v___x_2793_; lean_object* v___x_2794_; lean_object* v___x_2795_; lean_object* v___x_2796_; lean_object* v___x_2797_; lean_object* v___x_2798_; lean_object* v___x_2799_; lean_object* v___x_2800_; lean_object* v___x_10455__overap_2801_; lean_object* v___x_2802_; 
lean_inc_ref_n(v___x_2788_, 6);
v___f_2789_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2789_, 0, v___x_2788_);
v___f_2790_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2790_, 0, v___x_2788_);
v___f_2791_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_2791_, 0, v___x_2788_);
v___f_2792_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_2792_, 0, v___x_2788_);
v___x_2793_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_2793_, 0, lean_box(0));
lean_closure_set(v___x_2793_, 1, lean_box(0));
lean_closure_set(v___x_2793_, 2, v___x_2788_);
v___x_2794_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2794_, 0, v___x_2793_);
lean_ctor_set(v___x_2794_, 1, v___f_2789_);
v___x_2795_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_2795_, 0, lean_box(0));
lean_closure_set(v___x_2795_, 1, lean_box(0));
lean_closure_set(v___x_2795_, 2, v___x_2788_);
v___x_2796_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2796_, 0, v___x_2794_);
lean_ctor_set(v___x_2796_, 1, v___x_2795_);
lean_ctor_set(v___x_2796_, 2, v___f_2790_);
lean_ctor_set(v___x_2796_, 3, v___f_2791_);
lean_ctor_set(v___x_2796_, 4, v___f_2792_);
v___x_2797_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_2797_, 0, lean_box(0));
lean_closure_set(v___x_2797_, 1, lean_box(0));
lean_closure_set(v___x_2797_, 2, v___x_2788_);
v___x_2798_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2798_, 0, v___x_2796_);
lean_ctor_set(v___x_2798_, 1, v___x_2797_);
v___x_2799_ = lean_box(0);
v___x_2800_ = l_instInhabitedOfMonad___redArg(v___x_2798_, v___x_2799_);
v___x_10455__overap_2801_ = lean_panic_fn_borrowed(v___x_2800_, v_msg_2759_);
lean_dec(v___x_2800_);
lean_inc(v___y_2762_);
lean_inc_ref(v___y_2761_);
v___x_2802_ = lean_apply_4(v___x_10455__overap_2801_, v___y_2760_, v___y_2761_, v___y_2762_, lean_box(0));
return v___x_2802_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2___boxed(lean_object* v_msg_2809_, lean_object* v___y_2810_, lean_object* v___y_2811_, lean_object* v___y_2812_, lean_object* v___y_2813_){
_start:
{
lean_object* v_res_2814_; 
v_res_2814_ = l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2(v_msg_2809_, v___y_2810_, v___y_2811_, v___y_2812_);
lean_dec(v___y_2812_);
lean_dec_ref(v___y_2811_);
return v_res_2814_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4_spec__8_spec__13___redArg(lean_object* v_a_2815_, lean_object* v_b_2816_, lean_object* v_x_2817_){
_start:
{
if (lean_obj_tag(v_x_2817_) == 0)
{
lean_dec(v_b_2816_);
lean_dec_ref(v_a_2815_);
return v_x_2817_;
}
else
{
lean_object* v_key_2818_; lean_object* v_value_2819_; lean_object* v_tail_2820_; lean_object* v___x_2822_; uint8_t v_isShared_2823_; uint8_t v_isSharedCheck_2832_; 
v_key_2818_ = lean_ctor_get(v_x_2817_, 0);
v_value_2819_ = lean_ctor_get(v_x_2817_, 1);
v_tail_2820_ = lean_ctor_get(v_x_2817_, 2);
v_isSharedCheck_2832_ = !lean_is_exclusive(v_x_2817_);
if (v_isSharedCheck_2832_ == 0)
{
v___x_2822_ = v_x_2817_;
v_isShared_2823_ = v_isSharedCheck_2832_;
goto v_resetjp_2821_;
}
else
{
lean_inc(v_tail_2820_);
lean_inc(v_value_2819_);
lean_inc(v_key_2818_);
lean_dec(v_x_2817_);
v___x_2822_ = lean_box(0);
v_isShared_2823_ = v_isSharedCheck_2832_;
goto v_resetjp_2821_;
}
v_resetjp_2821_:
{
uint8_t v___x_2824_; 
v___x_2824_ = lean_expr_eqv(v_key_2818_, v_a_2815_);
if (v___x_2824_ == 0)
{
lean_object* v___x_2825_; lean_object* v___x_2827_; 
v___x_2825_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4_spec__8_spec__13___redArg(v_a_2815_, v_b_2816_, v_tail_2820_);
if (v_isShared_2823_ == 0)
{
lean_ctor_set(v___x_2822_, 2, v___x_2825_);
v___x_2827_ = v___x_2822_;
goto v_reusejp_2826_;
}
else
{
lean_object* v_reuseFailAlloc_2828_; 
v_reuseFailAlloc_2828_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2828_, 0, v_key_2818_);
lean_ctor_set(v_reuseFailAlloc_2828_, 1, v_value_2819_);
lean_ctor_set(v_reuseFailAlloc_2828_, 2, v___x_2825_);
v___x_2827_ = v_reuseFailAlloc_2828_;
goto v_reusejp_2826_;
}
v_reusejp_2826_:
{
return v___x_2827_;
}
}
else
{
lean_object* v___x_2830_; 
lean_dec(v_value_2819_);
lean_dec(v_key_2818_);
if (v_isShared_2823_ == 0)
{
lean_ctor_set(v___x_2822_, 1, v_b_2816_);
lean_ctor_set(v___x_2822_, 0, v_a_2815_);
v___x_2830_ = v___x_2822_;
goto v_reusejp_2829_;
}
else
{
lean_object* v_reuseFailAlloc_2831_; 
v_reuseFailAlloc_2831_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2831_, 0, v_a_2815_);
lean_ctor_set(v_reuseFailAlloc_2831_, 1, v_b_2816_);
lean_ctor_set(v_reuseFailAlloc_2831_, 2, v_tail_2820_);
v___x_2830_ = v_reuseFailAlloc_2831_;
goto v_reusejp_2829_;
}
v_reusejp_2829_:
{
return v___x_2830_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4_spec__8_spec__12_spec__17_spec__18___redArg(lean_object* v_x_2833_, lean_object* v_x_2834_){
_start:
{
if (lean_obj_tag(v_x_2834_) == 0)
{
return v_x_2833_;
}
else
{
lean_object* v_key_2835_; lean_object* v_value_2836_; lean_object* v_tail_2837_; lean_object* v___x_2839_; uint8_t v_isShared_2840_; uint8_t v_isSharedCheck_2860_; 
v_key_2835_ = lean_ctor_get(v_x_2834_, 0);
v_value_2836_ = lean_ctor_get(v_x_2834_, 1);
v_tail_2837_ = lean_ctor_get(v_x_2834_, 2);
v_isSharedCheck_2860_ = !lean_is_exclusive(v_x_2834_);
if (v_isSharedCheck_2860_ == 0)
{
v___x_2839_ = v_x_2834_;
v_isShared_2840_ = v_isSharedCheck_2860_;
goto v_resetjp_2838_;
}
else
{
lean_inc(v_tail_2837_);
lean_inc(v_value_2836_);
lean_inc(v_key_2835_);
lean_dec(v_x_2834_);
v___x_2839_ = lean_box(0);
v_isShared_2840_ = v_isSharedCheck_2860_;
goto v_resetjp_2838_;
}
v_resetjp_2838_:
{
lean_object* v___x_2841_; uint64_t v___x_2842_; uint64_t v___x_2843_; uint64_t v___x_2844_; uint64_t v_fold_2845_; uint64_t v___x_2846_; uint64_t v___x_2847_; uint64_t v___x_2848_; size_t v___x_2849_; size_t v___x_2850_; size_t v___x_2851_; size_t v___x_2852_; size_t v___x_2853_; lean_object* v___x_2854_; lean_object* v___x_2856_; 
v___x_2841_ = lean_array_get_size(v_x_2833_);
v___x_2842_ = l_Lean_Expr_hash(v_key_2835_);
v___x_2843_ = 32ULL;
v___x_2844_ = lean_uint64_shift_right(v___x_2842_, v___x_2843_);
v_fold_2845_ = lean_uint64_xor(v___x_2842_, v___x_2844_);
v___x_2846_ = 16ULL;
v___x_2847_ = lean_uint64_shift_right(v_fold_2845_, v___x_2846_);
v___x_2848_ = lean_uint64_xor(v_fold_2845_, v___x_2847_);
v___x_2849_ = lean_uint64_to_usize(v___x_2848_);
v___x_2850_ = lean_usize_of_nat(v___x_2841_);
v___x_2851_ = ((size_t)1ULL);
v___x_2852_ = lean_usize_sub(v___x_2850_, v___x_2851_);
v___x_2853_ = lean_usize_land(v___x_2849_, v___x_2852_);
v___x_2854_ = lean_array_uget_borrowed(v_x_2833_, v___x_2853_);
lean_inc(v___x_2854_);
if (v_isShared_2840_ == 0)
{
lean_ctor_set(v___x_2839_, 2, v___x_2854_);
v___x_2856_ = v___x_2839_;
goto v_reusejp_2855_;
}
else
{
lean_object* v_reuseFailAlloc_2859_; 
v_reuseFailAlloc_2859_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2859_, 0, v_key_2835_);
lean_ctor_set(v_reuseFailAlloc_2859_, 1, v_value_2836_);
lean_ctor_set(v_reuseFailAlloc_2859_, 2, v___x_2854_);
v___x_2856_ = v_reuseFailAlloc_2859_;
goto v_reusejp_2855_;
}
v_reusejp_2855_:
{
lean_object* v___x_2857_; 
v___x_2857_ = lean_array_uset(v_x_2833_, v___x_2853_, v___x_2856_);
v_x_2833_ = v___x_2857_;
v_x_2834_ = v_tail_2837_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4_spec__8_spec__12_spec__17___redArg(lean_object* v_i_2861_, lean_object* v_source_2862_, lean_object* v_target_2863_){
_start:
{
lean_object* v___x_2864_; uint8_t v___x_2865_; 
v___x_2864_ = lean_array_get_size(v_source_2862_);
v___x_2865_ = lean_nat_dec_lt(v_i_2861_, v___x_2864_);
if (v___x_2865_ == 0)
{
lean_dec_ref(v_source_2862_);
lean_dec(v_i_2861_);
return v_target_2863_;
}
else
{
lean_object* v_es_2866_; lean_object* v___x_2867_; lean_object* v_source_2868_; lean_object* v_target_2869_; lean_object* v___x_2870_; lean_object* v___x_2871_; 
v_es_2866_ = lean_array_fget(v_source_2862_, v_i_2861_);
v___x_2867_ = lean_box(0);
v_source_2868_ = lean_array_fset(v_source_2862_, v_i_2861_, v___x_2867_);
v_target_2869_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4_spec__8_spec__12_spec__17_spec__18___redArg(v_target_2863_, v_es_2866_);
v___x_2870_ = lean_unsigned_to_nat(1u);
v___x_2871_ = lean_nat_add(v_i_2861_, v___x_2870_);
lean_dec(v_i_2861_);
v_i_2861_ = v___x_2871_;
v_source_2862_ = v_source_2868_;
v_target_2863_ = v_target_2869_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4_spec__8_spec__12___redArg(lean_object* v_data_2873_){
_start:
{
lean_object* v___x_2874_; lean_object* v___x_2875_; lean_object* v_nbuckets_2876_; lean_object* v___x_2877_; lean_object* v___x_2878_; lean_object* v___x_2879_; lean_object* v___x_2880_; 
v___x_2874_ = lean_array_get_size(v_data_2873_);
v___x_2875_ = lean_unsigned_to_nat(2u);
v_nbuckets_2876_ = lean_nat_mul(v___x_2874_, v___x_2875_);
v___x_2877_ = lean_unsigned_to_nat(0u);
v___x_2878_ = lean_box(0);
v___x_2879_ = lean_mk_array(v_nbuckets_2876_, v___x_2878_);
v___x_2880_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4_spec__8_spec__12_spec__17___redArg(v___x_2877_, v_data_2873_, v___x_2879_);
return v___x_2880_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4_spec__8_spec__11___redArg(lean_object* v_a_2881_, lean_object* v_x_2882_){
_start:
{
if (lean_obj_tag(v_x_2882_) == 0)
{
uint8_t v___x_2883_; 
v___x_2883_ = 0;
return v___x_2883_;
}
else
{
lean_object* v_key_2884_; lean_object* v_tail_2885_; uint8_t v___x_2886_; 
v_key_2884_ = lean_ctor_get(v_x_2882_, 0);
v_tail_2885_ = lean_ctor_get(v_x_2882_, 2);
v___x_2886_ = lean_expr_eqv(v_key_2884_, v_a_2881_);
if (v___x_2886_ == 0)
{
v_x_2882_ = v_tail_2885_;
goto _start;
}
else
{
return v___x_2886_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4_spec__8_spec__11___redArg___boxed(lean_object* v_a_2888_, lean_object* v_x_2889_){
_start:
{
uint8_t v_res_2890_; lean_object* v_r_2891_; 
v_res_2890_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4_spec__8_spec__11___redArg(v_a_2888_, v_x_2889_);
lean_dec(v_x_2889_);
lean_dec_ref(v_a_2888_);
v_r_2891_ = lean_box(v_res_2890_);
return v_r_2891_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4_spec__8___redArg(lean_object* v_m_2892_, lean_object* v_a_2893_, lean_object* v_b_2894_){
_start:
{
lean_object* v_size_2895_; lean_object* v_buckets_2896_; lean_object* v___x_2898_; uint8_t v_isShared_2899_; uint8_t v_isSharedCheck_2939_; 
v_size_2895_ = lean_ctor_get(v_m_2892_, 0);
v_buckets_2896_ = lean_ctor_get(v_m_2892_, 1);
v_isSharedCheck_2939_ = !lean_is_exclusive(v_m_2892_);
if (v_isSharedCheck_2939_ == 0)
{
v___x_2898_ = v_m_2892_;
v_isShared_2899_ = v_isSharedCheck_2939_;
goto v_resetjp_2897_;
}
else
{
lean_inc(v_buckets_2896_);
lean_inc(v_size_2895_);
lean_dec(v_m_2892_);
v___x_2898_ = lean_box(0);
v_isShared_2899_ = v_isSharedCheck_2939_;
goto v_resetjp_2897_;
}
v_resetjp_2897_:
{
lean_object* v___x_2900_; uint64_t v___x_2901_; uint64_t v___x_2902_; uint64_t v___x_2903_; uint64_t v_fold_2904_; uint64_t v___x_2905_; uint64_t v___x_2906_; uint64_t v___x_2907_; size_t v___x_2908_; size_t v___x_2909_; size_t v___x_2910_; size_t v___x_2911_; size_t v___x_2912_; lean_object* v_bkt_2913_; uint8_t v___x_2914_; 
v___x_2900_ = lean_array_get_size(v_buckets_2896_);
v___x_2901_ = l_Lean_Expr_hash(v_a_2893_);
v___x_2902_ = 32ULL;
v___x_2903_ = lean_uint64_shift_right(v___x_2901_, v___x_2902_);
v_fold_2904_ = lean_uint64_xor(v___x_2901_, v___x_2903_);
v___x_2905_ = 16ULL;
v___x_2906_ = lean_uint64_shift_right(v_fold_2904_, v___x_2905_);
v___x_2907_ = lean_uint64_xor(v_fold_2904_, v___x_2906_);
v___x_2908_ = lean_uint64_to_usize(v___x_2907_);
v___x_2909_ = lean_usize_of_nat(v___x_2900_);
v___x_2910_ = ((size_t)1ULL);
v___x_2911_ = lean_usize_sub(v___x_2909_, v___x_2910_);
v___x_2912_ = lean_usize_land(v___x_2908_, v___x_2911_);
v_bkt_2913_ = lean_array_uget_borrowed(v_buckets_2896_, v___x_2912_);
v___x_2914_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4_spec__8_spec__11___redArg(v_a_2893_, v_bkt_2913_);
if (v___x_2914_ == 0)
{
lean_object* v___x_2915_; lean_object* v_size_x27_2916_; lean_object* v___x_2917_; lean_object* v_buckets_x27_2918_; lean_object* v___x_2919_; lean_object* v___x_2920_; lean_object* v___x_2921_; lean_object* v___x_2922_; lean_object* v___x_2923_; uint8_t v___x_2924_; 
v___x_2915_ = lean_unsigned_to_nat(1u);
v_size_x27_2916_ = lean_nat_add(v_size_2895_, v___x_2915_);
lean_dec(v_size_2895_);
lean_inc(v_bkt_2913_);
v___x_2917_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2917_, 0, v_a_2893_);
lean_ctor_set(v___x_2917_, 1, v_b_2894_);
lean_ctor_set(v___x_2917_, 2, v_bkt_2913_);
v_buckets_x27_2918_ = lean_array_uset(v_buckets_2896_, v___x_2912_, v___x_2917_);
v___x_2919_ = lean_unsigned_to_nat(4u);
v___x_2920_ = lean_nat_mul(v_size_x27_2916_, v___x_2919_);
v___x_2921_ = lean_unsigned_to_nat(3u);
v___x_2922_ = lean_nat_div(v___x_2920_, v___x_2921_);
lean_dec(v___x_2920_);
v___x_2923_ = lean_array_get_size(v_buckets_x27_2918_);
v___x_2924_ = lean_nat_dec_le(v___x_2922_, v___x_2923_);
lean_dec(v___x_2922_);
if (v___x_2924_ == 0)
{
lean_object* v_val_2925_; lean_object* v___x_2927_; 
v_val_2925_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4_spec__8_spec__12___redArg(v_buckets_x27_2918_);
if (v_isShared_2899_ == 0)
{
lean_ctor_set(v___x_2898_, 1, v_val_2925_);
lean_ctor_set(v___x_2898_, 0, v_size_x27_2916_);
v___x_2927_ = v___x_2898_;
goto v_reusejp_2926_;
}
else
{
lean_object* v_reuseFailAlloc_2928_; 
v_reuseFailAlloc_2928_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2928_, 0, v_size_x27_2916_);
lean_ctor_set(v_reuseFailAlloc_2928_, 1, v_val_2925_);
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
if (v_isShared_2899_ == 0)
{
lean_ctor_set(v___x_2898_, 1, v_buckets_x27_2918_);
lean_ctor_set(v___x_2898_, 0, v_size_x27_2916_);
v___x_2930_ = v___x_2898_;
goto v_reusejp_2929_;
}
else
{
lean_object* v_reuseFailAlloc_2931_; 
v_reuseFailAlloc_2931_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2931_, 0, v_size_x27_2916_);
lean_ctor_set(v_reuseFailAlloc_2931_, 1, v_buckets_x27_2918_);
v___x_2930_ = v_reuseFailAlloc_2931_;
goto v_reusejp_2929_;
}
v_reusejp_2929_:
{
return v___x_2930_;
}
}
}
else
{
lean_object* v___x_2932_; lean_object* v_buckets_x27_2933_; lean_object* v___x_2934_; lean_object* v___x_2935_; lean_object* v___x_2937_; 
lean_inc(v_bkt_2913_);
v___x_2932_ = lean_box(0);
v_buckets_x27_2933_ = lean_array_uset(v_buckets_2896_, v___x_2912_, v___x_2932_);
v___x_2934_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4_spec__8_spec__13___redArg(v_a_2893_, v_b_2894_, v_bkt_2913_);
v___x_2935_ = lean_array_uset(v_buckets_x27_2933_, v___x_2912_, v___x_2934_);
if (v_isShared_2899_ == 0)
{
lean_ctor_set(v___x_2898_, 1, v___x_2935_);
v___x_2937_ = v___x_2898_;
goto v_reusejp_2936_;
}
else
{
lean_object* v_reuseFailAlloc_2938_; 
v_reuseFailAlloc_2938_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2938_, 0, v_size_2895_);
lean_ctor_set(v_reuseFailAlloc_2938_, 1, v___x_2935_);
v___x_2937_ = v_reuseFailAlloc_2938_;
goto v_reusejp_2936_;
}
v_reusejp_2936_:
{
return v___x_2937_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4_spec__7_spec__9___redArg(lean_object* v_a_2940_, lean_object* v_x_2941_){
_start:
{
if (lean_obj_tag(v_x_2941_) == 0)
{
lean_object* v___x_2942_; 
v___x_2942_ = lean_box(0);
return v___x_2942_;
}
else
{
lean_object* v_key_2943_; lean_object* v_value_2944_; lean_object* v_tail_2945_; uint8_t v___x_2946_; 
v_key_2943_ = lean_ctor_get(v_x_2941_, 0);
v_value_2944_ = lean_ctor_get(v_x_2941_, 1);
v_tail_2945_ = lean_ctor_get(v_x_2941_, 2);
v___x_2946_ = lean_expr_eqv(v_key_2943_, v_a_2940_);
if (v___x_2946_ == 0)
{
v_x_2941_ = v_tail_2945_;
goto _start;
}
else
{
lean_object* v___x_2948_; 
lean_inc(v_value_2944_);
v___x_2948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2948_, 0, v_value_2944_);
return v___x_2948_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4_spec__7_spec__9___redArg___boxed(lean_object* v_a_2949_, lean_object* v_x_2950_){
_start:
{
lean_object* v_res_2951_; 
v_res_2951_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4_spec__7_spec__9___redArg(v_a_2949_, v_x_2950_);
lean_dec(v_x_2950_);
lean_dec_ref(v_a_2949_);
return v_res_2951_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4_spec__7___redArg(lean_object* v_m_2952_, lean_object* v_a_2953_){
_start:
{
lean_object* v_buckets_2954_; lean_object* v___x_2955_; uint64_t v___x_2956_; uint64_t v___x_2957_; uint64_t v___x_2958_; uint64_t v_fold_2959_; uint64_t v___x_2960_; uint64_t v___x_2961_; uint64_t v___x_2962_; size_t v___x_2963_; size_t v___x_2964_; size_t v___x_2965_; size_t v___x_2966_; size_t v___x_2967_; lean_object* v___x_2968_; lean_object* v___x_2969_; 
v_buckets_2954_ = lean_ctor_get(v_m_2952_, 1);
v___x_2955_ = lean_array_get_size(v_buckets_2954_);
v___x_2956_ = l_Lean_Expr_hash(v_a_2953_);
v___x_2957_ = 32ULL;
v___x_2958_ = lean_uint64_shift_right(v___x_2956_, v___x_2957_);
v_fold_2959_ = lean_uint64_xor(v___x_2956_, v___x_2958_);
v___x_2960_ = 16ULL;
v___x_2961_ = lean_uint64_shift_right(v_fold_2959_, v___x_2960_);
v___x_2962_ = lean_uint64_xor(v_fold_2959_, v___x_2961_);
v___x_2963_ = lean_uint64_to_usize(v___x_2962_);
v___x_2964_ = lean_usize_of_nat(v___x_2955_);
v___x_2965_ = ((size_t)1ULL);
v___x_2966_ = lean_usize_sub(v___x_2964_, v___x_2965_);
v___x_2967_ = lean_usize_land(v___x_2963_, v___x_2966_);
v___x_2968_ = lean_array_uget_borrowed(v_buckets_2954_, v___x_2967_);
v___x_2969_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4_spec__7_spec__9___redArg(v_a_2953_, v___x_2968_);
return v___x_2969_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4_spec__7___redArg___boxed(lean_object* v_m_2970_, lean_object* v_a_2971_){
_start:
{
lean_object* v_res_2972_; 
v_res_2972_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4_spec__7___redArg(v_m_2970_, v_a_2971_);
lean_dec_ref(v_a_2971_);
lean_dec_ref(v_m_2970_);
return v_res_2972_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4(lean_object* v_g_2973_, lean_object* v_e_2974_, lean_object* v_a_2975_, lean_object* v___y_2976_, lean_object* v___y_2977_, lean_object* v___y_2978_){
_start:
{
lean_object* v_a_2981_; lean_object* v_fst_2982_; lean_object* v___y_2988_; lean_object* v___x_2991_; lean_object* v___x_2992_; 
v___x_2991_ = lean_st_ref_get(v_a_2975_);
v___x_2992_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4_spec__7___redArg(v___x_2991_, v_e_2974_);
lean_dec(v___x_2991_);
if (lean_obj_tag(v___x_2992_) == 0)
{
lean_object* v___x_2993_; 
lean_inc_ref(v_g_2973_);
lean_inc(v___y_2978_);
lean_inc_ref(v___y_2977_);
lean_inc_ref(v_e_2974_);
v___x_2993_ = lean_apply_5(v_g_2973_, v_e_2974_, v___y_2976_, v___y_2977_, v___y_2978_, lean_box(0));
if (lean_obj_tag(v___x_2993_) == 0)
{
lean_object* v_a_2994_; lean_object* v_fst_2995_; lean_object* v_snd_2996_; lean_object* v___x_2998_; uint8_t v_isShared_2999_; uint8_t v_isSharedCheck_3041_; 
v_a_2994_ = lean_ctor_get(v___x_2993_, 0);
lean_inc(v_a_2994_);
lean_dec_ref_known(v___x_2993_, 1);
v_fst_2995_ = lean_ctor_get(v_a_2994_, 0);
v_snd_2996_ = lean_ctor_get(v_a_2994_, 1);
v_isSharedCheck_3041_ = !lean_is_exclusive(v_a_2994_);
if (v_isSharedCheck_3041_ == 0)
{
v___x_2998_ = v_a_2994_;
v_isShared_2999_ = v_isSharedCheck_3041_;
goto v_resetjp_2997_;
}
else
{
lean_inc(v_snd_2996_);
lean_inc(v_fst_2995_);
lean_dec(v_a_2994_);
v___x_2998_ = lean_box(0);
v_isShared_2999_ = v_isSharedCheck_3041_;
goto v_resetjp_2997_;
}
v_resetjp_2997_:
{
lean_object* v_d_3001_; lean_object* v_b_3002_; lean_object* v___y_3003_; uint8_t v___x_3008_; 
v___x_3008_ = lean_unbox(v_fst_2995_);
lean_dec(v_fst_2995_);
if (v___x_3008_ == 0)
{
lean_object* v___x_3009_; lean_object* v___x_3011_; 
lean_dec_ref(v_g_2973_);
v___x_3009_ = lean_box(0);
if (v_isShared_2999_ == 0)
{
lean_ctor_set(v___x_2998_, 0, v___x_3009_);
v___x_3011_ = v___x_2998_;
goto v_reusejp_3010_;
}
else
{
lean_object* v_reuseFailAlloc_3012_; 
v_reuseFailAlloc_3012_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3012_, 0, v___x_3009_);
lean_ctor_set(v_reuseFailAlloc_3012_, 1, v_snd_2996_);
v___x_3011_ = v_reuseFailAlloc_3012_;
goto v_reusejp_3010_;
}
v_reusejp_3010_:
{
v_a_2981_ = v___x_3011_;
v_fst_2982_ = v___x_3009_;
goto v___jp_2980_;
}
}
else
{
switch(lean_obj_tag(v_e_2974_))
{
case 7:
{
lean_object* v_binderType_3013_; lean_object* v_body_3014_; 
lean_del_object(v___x_2998_);
v_binderType_3013_ = lean_ctor_get(v_e_2974_, 1);
v_body_3014_ = lean_ctor_get(v_e_2974_, 2);
lean_inc_ref(v_body_3014_);
lean_inc_ref(v_binderType_3013_);
v_d_3001_ = v_binderType_3013_;
v_b_3002_ = v_body_3014_;
v___y_3003_ = v_a_2975_;
goto v___jp_3000_;
}
case 6:
{
lean_object* v_binderType_3015_; lean_object* v_body_3016_; 
lean_del_object(v___x_2998_);
v_binderType_3015_ = lean_ctor_get(v_e_2974_, 1);
v_body_3016_ = lean_ctor_get(v_e_2974_, 2);
lean_inc_ref(v_body_3016_);
lean_inc_ref(v_binderType_3015_);
v_d_3001_ = v_binderType_3015_;
v_b_3002_ = v_body_3016_;
v___y_3003_ = v_a_2975_;
goto v___jp_3000_;
}
case 8:
{
lean_object* v_type_3017_; lean_object* v_value_3018_; lean_object* v_body_3019_; lean_object* v___x_3020_; 
lean_del_object(v___x_2998_);
v_type_3017_ = lean_ctor_get(v_e_2974_, 1);
v_value_3018_ = lean_ctor_get(v_e_2974_, 2);
v_body_3019_ = lean_ctor_get(v_e_2974_, 3);
lean_inc_ref(v_type_3017_);
lean_inc_ref(v_g_2973_);
v___x_3020_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4(v_g_2973_, v_type_3017_, v_a_2975_, v_snd_2996_, v___y_2977_, v___y_2978_);
if (lean_obj_tag(v___x_3020_) == 0)
{
lean_object* v_a_3021_; lean_object* v_snd_3022_; lean_object* v___x_3023_; 
v_a_3021_ = lean_ctor_get(v___x_3020_, 0);
lean_inc(v_a_3021_);
lean_dec_ref_known(v___x_3020_, 1);
v_snd_3022_ = lean_ctor_get(v_a_3021_, 1);
lean_inc(v_snd_3022_);
lean_dec(v_a_3021_);
lean_inc_ref(v_value_3018_);
lean_inc_ref(v_g_2973_);
v___x_3023_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4(v_g_2973_, v_value_3018_, v_a_2975_, v_snd_3022_, v___y_2977_, v___y_2978_);
if (lean_obj_tag(v___x_3023_) == 0)
{
lean_object* v_a_3024_; lean_object* v_snd_3025_; lean_object* v___x_3026_; 
v_a_3024_ = lean_ctor_get(v___x_3023_, 0);
lean_inc(v_a_3024_);
lean_dec_ref_known(v___x_3023_, 1);
v_snd_3025_ = lean_ctor_get(v_a_3024_, 1);
lean_inc(v_snd_3025_);
lean_dec(v_a_3024_);
lean_inc_ref(v_body_3019_);
v___x_3026_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4(v_g_2973_, v_body_3019_, v_a_2975_, v_snd_3025_, v___y_2977_, v___y_2978_);
v___y_2988_ = v___x_3026_;
goto v___jp_2987_;
}
else
{
lean_dec_ref(v_g_2973_);
v___y_2988_ = v___x_3023_;
goto v___jp_2987_;
}
}
else
{
lean_dec_ref(v_g_2973_);
v___y_2988_ = v___x_3020_;
goto v___jp_2987_;
}
}
case 5:
{
lean_object* v_fn_3027_; lean_object* v_arg_3028_; lean_object* v___x_3029_; 
lean_del_object(v___x_2998_);
v_fn_3027_ = lean_ctor_get(v_e_2974_, 0);
v_arg_3028_ = lean_ctor_get(v_e_2974_, 1);
lean_inc_ref(v_fn_3027_);
lean_inc_ref(v_g_2973_);
v___x_3029_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4(v_g_2973_, v_fn_3027_, v_a_2975_, v_snd_2996_, v___y_2977_, v___y_2978_);
if (lean_obj_tag(v___x_3029_) == 0)
{
lean_object* v_a_3030_; lean_object* v_snd_3031_; lean_object* v___x_3032_; 
v_a_3030_ = lean_ctor_get(v___x_3029_, 0);
lean_inc(v_a_3030_);
lean_dec_ref_known(v___x_3029_, 1);
v_snd_3031_ = lean_ctor_get(v_a_3030_, 1);
lean_inc(v_snd_3031_);
lean_dec(v_a_3030_);
lean_inc_ref(v_arg_3028_);
v___x_3032_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4(v_g_2973_, v_arg_3028_, v_a_2975_, v_snd_3031_, v___y_2977_, v___y_2978_);
v___y_2988_ = v___x_3032_;
goto v___jp_2987_;
}
else
{
lean_dec_ref(v_g_2973_);
v___y_2988_ = v___x_3029_;
goto v___jp_2987_;
}
}
case 10:
{
lean_object* v_expr_3033_; lean_object* v___x_3034_; 
lean_del_object(v___x_2998_);
v_expr_3033_ = lean_ctor_get(v_e_2974_, 1);
lean_inc_ref(v_expr_3033_);
v___x_3034_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4(v_g_2973_, v_expr_3033_, v_a_2975_, v_snd_2996_, v___y_2977_, v___y_2978_);
v___y_2988_ = v___x_3034_;
goto v___jp_2987_;
}
case 11:
{
lean_object* v_struct_3035_; lean_object* v___x_3036_; 
lean_del_object(v___x_2998_);
v_struct_3035_ = lean_ctor_get(v_e_2974_, 2);
lean_inc_ref(v_struct_3035_);
v___x_3036_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4(v_g_2973_, v_struct_3035_, v_a_2975_, v_snd_2996_, v___y_2977_, v___y_2978_);
v___y_2988_ = v___x_3036_;
goto v___jp_2987_;
}
default: 
{
lean_object* v___x_3037_; lean_object* v___x_3039_; 
lean_dec_ref(v_g_2973_);
v___x_3037_ = lean_box(0);
if (v_isShared_2999_ == 0)
{
lean_ctor_set(v___x_2998_, 0, v___x_3037_);
v___x_3039_ = v___x_2998_;
goto v_reusejp_3038_;
}
else
{
lean_object* v_reuseFailAlloc_3040_; 
v_reuseFailAlloc_3040_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3040_, 0, v___x_3037_);
lean_ctor_set(v_reuseFailAlloc_3040_, 1, v_snd_2996_);
v___x_3039_ = v_reuseFailAlloc_3040_;
goto v_reusejp_3038_;
}
v_reusejp_3038_:
{
v_a_2981_ = v___x_3039_;
v_fst_2982_ = v___x_3037_;
goto v___jp_2980_;
}
}
}
}
v___jp_3000_:
{
lean_object* v___x_3004_; 
lean_inc_ref(v_g_2973_);
v___x_3004_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4(v_g_2973_, v_d_3001_, v___y_3003_, v_snd_2996_, v___y_2977_, v___y_2978_);
if (lean_obj_tag(v___x_3004_) == 0)
{
lean_object* v_a_3005_; lean_object* v_snd_3006_; lean_object* v___x_3007_; 
v_a_3005_ = lean_ctor_get(v___x_3004_, 0);
lean_inc(v_a_3005_);
lean_dec_ref_known(v___x_3004_, 1);
v_snd_3006_ = lean_ctor_get(v_a_3005_, 1);
lean_inc(v_snd_3006_);
lean_dec(v_a_3005_);
v___x_3007_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4(v_g_2973_, v_b_3002_, v___y_3003_, v_snd_3006_, v___y_2977_, v___y_2978_);
v___y_2988_ = v___x_3007_;
goto v___jp_2987_;
}
else
{
lean_dec_ref(v_b_3002_);
lean_dec_ref(v_g_2973_);
v___y_2988_ = v___x_3004_;
goto v___jp_2987_;
}
}
}
}
else
{
lean_object* v_a_3042_; lean_object* v___x_3044_; uint8_t v_isShared_3045_; uint8_t v_isSharedCheck_3049_; 
lean_dec_ref(v_e_2974_);
lean_dec_ref(v_g_2973_);
v_a_3042_ = lean_ctor_get(v___x_2993_, 0);
v_isSharedCheck_3049_ = !lean_is_exclusive(v___x_2993_);
if (v_isSharedCheck_3049_ == 0)
{
v___x_3044_ = v___x_2993_;
v_isShared_3045_ = v_isSharedCheck_3049_;
goto v_resetjp_3043_;
}
else
{
lean_inc(v_a_3042_);
lean_dec(v___x_2993_);
v___x_3044_ = lean_box(0);
v_isShared_3045_ = v_isSharedCheck_3049_;
goto v_resetjp_3043_;
}
v_resetjp_3043_:
{
lean_object* v___x_3047_; 
if (v_isShared_3045_ == 0)
{
v___x_3047_ = v___x_3044_;
goto v_reusejp_3046_;
}
else
{
lean_object* v_reuseFailAlloc_3048_; 
v_reuseFailAlloc_3048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3048_, 0, v_a_3042_);
v___x_3047_ = v_reuseFailAlloc_3048_;
goto v_reusejp_3046_;
}
v_reusejp_3046_:
{
return v___x_3047_;
}
}
}
}
else
{
lean_object* v_val_3050_; lean_object* v___x_3052_; uint8_t v_isShared_3053_; uint8_t v_isSharedCheck_3058_; 
lean_dec_ref(v_e_2974_);
lean_dec_ref(v_g_2973_);
v_val_3050_ = lean_ctor_get(v___x_2992_, 0);
v_isSharedCheck_3058_ = !lean_is_exclusive(v___x_2992_);
if (v_isSharedCheck_3058_ == 0)
{
v___x_3052_ = v___x_2992_;
v_isShared_3053_ = v_isSharedCheck_3058_;
goto v_resetjp_3051_;
}
else
{
lean_inc(v_val_3050_);
lean_dec(v___x_2992_);
v___x_3052_ = lean_box(0);
v_isShared_3053_ = v_isSharedCheck_3058_;
goto v_resetjp_3051_;
}
v_resetjp_3051_:
{
lean_object* v___x_3054_; lean_object* v___x_3056_; 
v___x_3054_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3054_, 0, v_val_3050_);
lean_ctor_set(v___x_3054_, 1, v___y_2976_);
if (v_isShared_3053_ == 0)
{
lean_ctor_set_tag(v___x_3052_, 0);
lean_ctor_set(v___x_3052_, 0, v___x_3054_);
v___x_3056_ = v___x_3052_;
goto v_reusejp_3055_;
}
else
{
lean_object* v_reuseFailAlloc_3057_; 
v_reuseFailAlloc_3057_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3057_, 0, v___x_3054_);
v___x_3056_ = v_reuseFailAlloc_3057_;
goto v_reusejp_3055_;
}
v_reusejp_3055_:
{
return v___x_3056_;
}
}
}
v___jp_2980_:
{
lean_object* v___x_2983_; lean_object* v___x_2984_; lean_object* v___x_2985_; lean_object* v___x_2986_; 
v___x_2983_ = lean_st_ref_take(v_a_2975_);
v___x_2984_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4_spec__8___redArg(v___x_2983_, v_e_2974_, v_fst_2982_);
v___x_2985_ = lean_st_ref_set(v_a_2975_, v___x_2984_);
v___x_2986_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2986_, 0, v_a_2981_);
return v___x_2986_;
}
v___jp_2987_:
{
if (lean_obj_tag(v___y_2988_) == 0)
{
lean_object* v_a_2989_; lean_object* v_fst_2990_; 
v_a_2989_ = lean_ctor_get(v___y_2988_, 0);
lean_inc(v_a_2989_);
lean_dec_ref_known(v___y_2988_, 1);
v_fst_2990_ = lean_ctor_get(v_a_2989_, 0);
lean_inc(v_fst_2990_);
v_a_2981_ = v_a_2989_;
v_fst_2982_ = v_fst_2990_;
goto v___jp_2980_;
}
else
{
lean_dec_ref(v_e_2974_);
return v___y_2988_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4___boxed(lean_object* v_g_3059_, lean_object* v_e_3060_, lean_object* v_a_3061_, lean_object* v___y_3062_, lean_object* v___y_3063_, lean_object* v___y_3064_, lean_object* v___y_3065_){
_start:
{
lean_object* v_res_3066_; 
v_res_3066_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4(v_g_3059_, v_e_3060_, v_a_3061_, v___y_3062_, v___y_3063_, v___y_3064_);
lean_dec(v___y_3064_);
lean_dec_ref(v___y_3063_);
lean_dec(v_a_3061_);
return v_res_3066_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1_spec__2___redArg(lean_object* v_a_3067_, lean_object* v_x_3068_){
_start:
{
if (lean_obj_tag(v_x_3068_) == 0)
{
uint8_t v___x_3069_; 
v___x_3069_ = 0;
return v___x_3069_;
}
else
{
lean_object* v_key_3070_; lean_object* v_tail_3071_; uint8_t v___x_3072_; 
v_key_3070_ = lean_ctor_get(v_x_3068_, 0);
v_tail_3071_ = lean_ctor_get(v_x_3068_, 2);
v___x_3072_ = l_Lean_instBEqFVarId_beq(v_key_3070_, v_a_3067_);
if (v___x_3072_ == 0)
{
v_x_3068_ = v_tail_3071_;
goto _start;
}
else
{
return v___x_3072_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1_spec__2___redArg___boxed(lean_object* v_a_3074_, lean_object* v_x_3075_){
_start:
{
uint8_t v_res_3076_; lean_object* v_r_3077_; 
v_res_3076_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1_spec__2___redArg(v_a_3074_, v_x_3075_);
lean_dec(v_x_3075_);
lean_dec(v_a_3074_);
v_r_3077_ = lean_box(v_res_3076_);
return v_r_3077_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1___redArg(lean_object* v_m_3078_, lean_object* v_a_3079_){
_start:
{
lean_object* v_buckets_3080_; lean_object* v___x_3081_; uint64_t v___x_3082_; uint64_t v___x_3083_; uint64_t v___x_3084_; uint64_t v_fold_3085_; uint64_t v___x_3086_; uint64_t v___x_3087_; uint64_t v___x_3088_; size_t v___x_3089_; size_t v___x_3090_; size_t v___x_3091_; size_t v___x_3092_; size_t v___x_3093_; lean_object* v___x_3094_; uint8_t v___x_3095_; 
v_buckets_3080_ = lean_ctor_get(v_m_3078_, 1);
v___x_3081_ = lean_array_get_size(v_buckets_3080_);
v___x_3082_ = l_Lean_instHashableFVarId_hash(v_a_3079_);
v___x_3083_ = 32ULL;
v___x_3084_ = lean_uint64_shift_right(v___x_3082_, v___x_3083_);
v_fold_3085_ = lean_uint64_xor(v___x_3082_, v___x_3084_);
v___x_3086_ = 16ULL;
v___x_3087_ = lean_uint64_shift_right(v_fold_3085_, v___x_3086_);
v___x_3088_ = lean_uint64_xor(v_fold_3085_, v___x_3087_);
v___x_3089_ = lean_uint64_to_usize(v___x_3088_);
v___x_3090_ = lean_usize_of_nat(v___x_3081_);
v___x_3091_ = ((size_t)1ULL);
v___x_3092_ = lean_usize_sub(v___x_3090_, v___x_3091_);
v___x_3093_ = lean_usize_land(v___x_3089_, v___x_3092_);
v___x_3094_ = lean_array_uget_borrowed(v_buckets_3080_, v___x_3093_);
v___x_3095_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1_spec__2___redArg(v_a_3079_, v___x_3094_);
return v___x_3095_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1___redArg___boxed(lean_object* v_m_3096_, lean_object* v_a_3097_){
_start:
{
uint8_t v_res_3098_; lean_object* v_r_3099_; 
v_res_3098_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1___redArg(v_m_3096_, v_a_3097_);
lean_dec(v_a_3097_);
lean_dec_ref(v_m_3096_);
v_r_3099_ = lean_box(v_res_3098_);
return v_r_3099_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__0(void){
_start:
{
lean_object* v___x_3100_; 
v___x_3100_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_3100_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__1(void){
_start:
{
lean_object* v___x_3101_; lean_object* v___x_3102_; 
v___x_3101_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__0);
v___x_3102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3102_, 0, v___x_3101_);
return v___x_3102_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__2(void){
_start:
{
lean_object* v___x_3103_; lean_object* v___x_3104_; lean_object* v___x_3105_; 
v___x_3103_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__1);
v___x_3104_ = lean_unsigned_to_nat(0u);
v___x_3105_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_3105_, 0, v___x_3104_);
lean_ctor_set(v___x_3105_, 1, v___x_3104_);
lean_ctor_set(v___x_3105_, 2, v___x_3104_);
lean_ctor_set(v___x_3105_, 3, v___x_3104_);
lean_ctor_set(v___x_3105_, 4, v___x_3103_);
lean_ctor_set(v___x_3105_, 5, v___x_3103_);
lean_ctor_set(v___x_3105_, 6, v___x_3103_);
lean_ctor_set(v___x_3105_, 7, v___x_3103_);
lean_ctor_set(v___x_3105_, 8, v___x_3103_);
lean_ctor_set(v___x_3105_, 9, v___x_3103_);
return v___x_3105_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__3(void){
_start:
{
lean_object* v___x_3106_; lean_object* v___x_3107_; lean_object* v___x_3108_; 
v___x_3106_ = lean_unsigned_to_nat(32u);
v___x_3107_ = lean_mk_empty_array_with_capacity(v___x_3106_);
v___x_3108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3108_, 0, v___x_3107_);
return v___x_3108_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__4(void){
_start:
{
size_t v___x_3109_; lean_object* v___x_3110_; lean_object* v___x_3111_; lean_object* v___x_3112_; lean_object* v___x_3113_; lean_object* v___x_3114_; 
v___x_3109_ = ((size_t)5ULL);
v___x_3110_ = lean_unsigned_to_nat(0u);
v___x_3111_ = lean_unsigned_to_nat(32u);
v___x_3112_ = lean_mk_empty_array_with_capacity(v___x_3111_);
v___x_3113_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__3);
v___x_3114_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3114_, 0, v___x_3113_);
lean_ctor_set(v___x_3114_, 1, v___x_3112_);
lean_ctor_set(v___x_3114_, 2, v___x_3110_);
lean_ctor_set(v___x_3114_, 3, v___x_3110_);
lean_ctor_set_usize(v___x_3114_, 4, v___x_3109_);
return v___x_3114_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__5(void){
_start:
{
lean_object* v___x_3115_; lean_object* v___x_3116_; lean_object* v___x_3117_; lean_object* v___x_3118_; 
v___x_3115_ = lean_box(1);
v___x_3116_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__4);
v___x_3117_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__1);
v___x_3118_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3118_, 0, v___x_3117_);
lean_ctor_set(v___x_3118_, 1, v___x_3116_);
lean_ctor_set(v___x_3118_, 2, v___x_3115_);
return v___x_3118_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10(lean_object* v_msgData_3119_, lean_object* v___y_3120_, lean_object* v___y_3121_){
_start:
{
lean_object* v___x_3123_; lean_object* v_env_3124_; lean_object* v_options_3125_; lean_object* v___x_3126_; lean_object* v___x_3127_; lean_object* v___x_3128_; lean_object* v___x_3129_; lean_object* v___x_3130_; 
v___x_3123_ = lean_st_ref_get(v___y_3121_);
v_env_3124_ = lean_ctor_get(v___x_3123_, 0);
lean_inc_ref(v_env_3124_);
lean_dec(v___x_3123_);
v_options_3125_ = lean_ctor_get(v___y_3120_, 2);
v___x_3126_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__2);
v___x_3127_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__5);
lean_inc_ref(v_options_3125_);
v___x_3128_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3128_, 0, v_env_3124_);
lean_ctor_set(v___x_3128_, 1, v___x_3126_);
lean_ctor_set(v___x_3128_, 2, v___x_3127_);
lean_ctor_set(v___x_3128_, 3, v_options_3125_);
v___x_3129_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_3129_, 0, v___x_3128_);
lean_ctor_set(v___x_3129_, 1, v_msgData_3119_);
v___x_3130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3130_, 0, v___x_3129_);
return v___x_3130_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___boxed(lean_object* v_msgData_3131_, lean_object* v___y_3132_, lean_object* v___y_3133_, lean_object* v___y_3134_){
_start:
{
lean_object* v_res_3135_; 
v_res_3135_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10(v_msgData_3131_, v___y_3132_, v___y_3133_);
lean_dec(v___y_3133_);
lean_dec_ref(v___y_3132_);
return v_res_3135_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5___redArg(lean_object* v_msg_3136_, lean_object* v___y_3137_, lean_object* v___y_3138_){
_start:
{
lean_object* v_ref_3140_; lean_object* v___x_3141_; lean_object* v_a_3142_; lean_object* v___x_3144_; uint8_t v_isShared_3145_; uint8_t v_isSharedCheck_3150_; 
v_ref_3140_ = lean_ctor_get(v___y_3137_, 5);
v___x_3141_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10(v_msg_3136_, v___y_3137_, v___y_3138_);
v_a_3142_ = lean_ctor_get(v___x_3141_, 0);
v_isSharedCheck_3150_ = !lean_is_exclusive(v___x_3141_);
if (v_isSharedCheck_3150_ == 0)
{
v___x_3144_ = v___x_3141_;
v_isShared_3145_ = v_isSharedCheck_3150_;
goto v_resetjp_3143_;
}
else
{
lean_inc(v_a_3142_);
lean_dec(v___x_3141_);
v___x_3144_ = lean_box(0);
v_isShared_3145_ = v_isSharedCheck_3150_;
goto v_resetjp_3143_;
}
v_resetjp_3143_:
{
lean_object* v___x_3146_; lean_object* v___x_3148_; 
lean_inc(v_ref_3140_);
v___x_3146_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3146_, 0, v_ref_3140_);
lean_ctor_set(v___x_3146_, 1, v_a_3142_);
if (v_isShared_3145_ == 0)
{
lean_ctor_set_tag(v___x_3144_, 1);
lean_ctor_set(v___x_3144_, 0, v___x_3146_);
v___x_3148_ = v___x_3144_;
goto v_reusejp_3147_;
}
else
{
lean_object* v_reuseFailAlloc_3149_; 
v_reuseFailAlloc_3149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3149_, 0, v___x_3146_);
v___x_3148_ = v_reuseFailAlloc_3149_;
goto v_reusejp_3147_;
}
v_reusejp_3147_:
{
return v___x_3148_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5___redArg___boxed(lean_object* v_msg_3151_, lean_object* v___y_3152_, lean_object* v___y_3153_, lean_object* v___y_3154_){
_start:
{
lean_object* v_res_3155_; 
v_res_3155_ = l_Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5___redArg(v_msg_3151_, v___y_3152_, v___y_3153_);
lean_dec(v___y_3153_);
lean_dec_ref(v___y_3152_);
return v_res_3155_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6___closed__0(void){
_start:
{
lean_object* v___x_3156_; double v___x_3157_; 
v___x_3156_ = lean_unsigned_to_nat(0u);
v___x_3157_ = lean_float_of_nat(v___x_3156_);
return v___x_3157_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6(lean_object* v_cls_3161_, lean_object* v_msg_3162_, lean_object* v___y_3163_, lean_object* v___y_3164_, lean_object* v___y_3165_){
_start:
{
lean_object* v_ref_3167_; lean_object* v___x_3168_; lean_object* v_a_3169_; lean_object* v___x_3171_; uint8_t v_isShared_3172_; uint8_t v_isSharedCheck_3214_; 
v_ref_3167_ = lean_ctor_get(v___y_3164_, 5);
v___x_3168_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10(v_msg_3162_, v___y_3164_, v___y_3165_);
v_a_3169_ = lean_ctor_get(v___x_3168_, 0);
v_isSharedCheck_3214_ = !lean_is_exclusive(v___x_3168_);
if (v_isSharedCheck_3214_ == 0)
{
v___x_3171_ = v___x_3168_;
v_isShared_3172_ = v_isSharedCheck_3214_;
goto v_resetjp_3170_;
}
else
{
lean_inc(v_a_3169_);
lean_dec(v___x_3168_);
v___x_3171_ = lean_box(0);
v_isShared_3172_ = v_isSharedCheck_3214_;
goto v_resetjp_3170_;
}
v_resetjp_3170_:
{
lean_object* v___x_3173_; lean_object* v_traceState_3174_; lean_object* v_env_3175_; lean_object* v_nextMacroScope_3176_; lean_object* v_ngen_3177_; lean_object* v_auxDeclNGen_3178_; lean_object* v_cache_3179_; lean_object* v_messages_3180_; lean_object* v_infoState_3181_; lean_object* v_snapshotTasks_3182_; lean_object* v___x_3184_; uint8_t v_isShared_3185_; uint8_t v_isSharedCheck_3213_; 
v___x_3173_ = lean_st_ref_take(v___y_3165_);
v_traceState_3174_ = lean_ctor_get(v___x_3173_, 4);
v_env_3175_ = lean_ctor_get(v___x_3173_, 0);
v_nextMacroScope_3176_ = lean_ctor_get(v___x_3173_, 1);
v_ngen_3177_ = lean_ctor_get(v___x_3173_, 2);
v_auxDeclNGen_3178_ = lean_ctor_get(v___x_3173_, 3);
v_cache_3179_ = lean_ctor_get(v___x_3173_, 5);
v_messages_3180_ = lean_ctor_get(v___x_3173_, 6);
v_infoState_3181_ = lean_ctor_get(v___x_3173_, 7);
v_snapshotTasks_3182_ = lean_ctor_get(v___x_3173_, 8);
v_isSharedCheck_3213_ = !lean_is_exclusive(v___x_3173_);
if (v_isSharedCheck_3213_ == 0)
{
v___x_3184_ = v___x_3173_;
v_isShared_3185_ = v_isSharedCheck_3213_;
goto v_resetjp_3183_;
}
else
{
lean_inc(v_snapshotTasks_3182_);
lean_inc(v_infoState_3181_);
lean_inc(v_messages_3180_);
lean_inc(v_cache_3179_);
lean_inc(v_traceState_3174_);
lean_inc(v_auxDeclNGen_3178_);
lean_inc(v_ngen_3177_);
lean_inc(v_nextMacroScope_3176_);
lean_inc(v_env_3175_);
lean_dec(v___x_3173_);
v___x_3184_ = lean_box(0);
v_isShared_3185_ = v_isSharedCheck_3213_;
goto v_resetjp_3183_;
}
v_resetjp_3183_:
{
uint64_t v_tid_3186_; lean_object* v_traces_3187_; lean_object* v___x_3189_; uint8_t v_isShared_3190_; uint8_t v_isSharedCheck_3212_; 
v_tid_3186_ = lean_ctor_get_uint64(v_traceState_3174_, sizeof(void*)*1);
v_traces_3187_ = lean_ctor_get(v_traceState_3174_, 0);
v_isSharedCheck_3212_ = !lean_is_exclusive(v_traceState_3174_);
if (v_isSharedCheck_3212_ == 0)
{
v___x_3189_ = v_traceState_3174_;
v_isShared_3190_ = v_isSharedCheck_3212_;
goto v_resetjp_3188_;
}
else
{
lean_inc(v_traces_3187_);
lean_dec(v_traceState_3174_);
v___x_3189_ = lean_box(0);
v_isShared_3190_ = v_isSharedCheck_3212_;
goto v_resetjp_3188_;
}
v_resetjp_3188_:
{
lean_object* v___x_3191_; double v___x_3192_; uint8_t v___x_3193_; lean_object* v___x_3194_; lean_object* v___x_3195_; lean_object* v___x_3196_; lean_object* v___x_3197_; lean_object* v___x_3198_; lean_object* v___x_3199_; lean_object* v___x_3201_; 
v___x_3191_ = lean_box(0);
v___x_3192_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6___closed__0);
v___x_3193_ = 0;
v___x_3194_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6___closed__1));
v___x_3195_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3195_, 0, v_cls_3161_);
lean_ctor_set(v___x_3195_, 1, v___x_3191_);
lean_ctor_set(v___x_3195_, 2, v___x_3194_);
lean_ctor_set_float(v___x_3195_, sizeof(void*)*3, v___x_3192_);
lean_ctor_set_float(v___x_3195_, sizeof(void*)*3 + 8, v___x_3192_);
lean_ctor_set_uint8(v___x_3195_, sizeof(void*)*3 + 16, v___x_3193_);
v___x_3196_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6___closed__2));
v___x_3197_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3197_, 0, v___x_3195_);
lean_ctor_set(v___x_3197_, 1, v_a_3169_);
lean_ctor_set(v___x_3197_, 2, v___x_3196_);
lean_inc(v_ref_3167_);
v___x_3198_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3198_, 0, v_ref_3167_);
lean_ctor_set(v___x_3198_, 1, v___x_3197_);
v___x_3199_ = l_Lean_PersistentArray_push___redArg(v_traces_3187_, v___x_3198_);
if (v_isShared_3190_ == 0)
{
lean_ctor_set(v___x_3189_, 0, v___x_3199_);
v___x_3201_ = v___x_3189_;
goto v_reusejp_3200_;
}
else
{
lean_object* v_reuseFailAlloc_3211_; 
v_reuseFailAlloc_3211_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3211_, 0, v___x_3199_);
lean_ctor_set_uint64(v_reuseFailAlloc_3211_, sizeof(void*)*1, v_tid_3186_);
v___x_3201_ = v_reuseFailAlloc_3211_;
goto v_reusejp_3200_;
}
v_reusejp_3200_:
{
lean_object* v___x_3203_; 
if (v_isShared_3185_ == 0)
{
lean_ctor_set(v___x_3184_, 4, v___x_3201_);
v___x_3203_ = v___x_3184_;
goto v_reusejp_3202_;
}
else
{
lean_object* v_reuseFailAlloc_3210_; 
v_reuseFailAlloc_3210_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3210_, 0, v_env_3175_);
lean_ctor_set(v_reuseFailAlloc_3210_, 1, v_nextMacroScope_3176_);
lean_ctor_set(v_reuseFailAlloc_3210_, 2, v_ngen_3177_);
lean_ctor_set(v_reuseFailAlloc_3210_, 3, v_auxDeclNGen_3178_);
lean_ctor_set(v_reuseFailAlloc_3210_, 4, v___x_3201_);
lean_ctor_set(v_reuseFailAlloc_3210_, 5, v_cache_3179_);
lean_ctor_set(v_reuseFailAlloc_3210_, 6, v_messages_3180_);
lean_ctor_set(v_reuseFailAlloc_3210_, 7, v_infoState_3181_);
lean_ctor_set(v_reuseFailAlloc_3210_, 8, v_snapshotTasks_3182_);
v___x_3203_ = v_reuseFailAlloc_3210_;
goto v_reusejp_3202_;
}
v_reusejp_3202_:
{
lean_object* v___x_3204_; lean_object* v___x_3205_; lean_object* v___x_3206_; lean_object* v___x_3208_; 
v___x_3204_ = lean_st_ref_set(v___y_3165_, v___x_3203_);
v___x_3205_ = lean_box(0);
v___x_3206_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3206_, 0, v___x_3205_);
lean_ctor_set(v___x_3206_, 1, v___y_3163_);
if (v_isShared_3172_ == 0)
{
lean_ctor_set(v___x_3171_, 0, v___x_3206_);
v___x_3208_ = v___x_3171_;
goto v_reusejp_3207_;
}
else
{
lean_object* v_reuseFailAlloc_3209_; 
v_reuseFailAlloc_3209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3209_, 0, v___x_3206_);
v___x_3208_ = v_reuseFailAlloc_3209_;
goto v_reusejp_3207_;
}
v_reusejp_3207_:
{
return v___x_3208_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6___boxed(lean_object* v_cls_3215_, lean_object* v_msg_3216_, lean_object* v___y_3217_, lean_object* v___y_3218_, lean_object* v___y_3219_, lean_object* v___y_3220_){
_start:
{
lean_object* v_res_3221_; 
v_res_3221_ = l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6(v_cls_3215_, v_msg_3216_, v___y_3217_, v___y_3218_, v___y_3219_);
lean_dec(v___y_3219_);
lean_dec_ref(v___y_3218_);
return v_res_3221_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__5_spec__6_spec__11___redArg(lean_object* v_x_3222_, lean_object* v_x_3223_){
_start:
{
if (lean_obj_tag(v_x_3223_) == 0)
{
return v_x_3222_;
}
else
{
lean_object* v_key_3224_; lean_object* v_value_3225_; lean_object* v_tail_3226_; lean_object* v___x_3228_; uint8_t v_isShared_3229_; uint8_t v_isSharedCheck_3249_; 
v_key_3224_ = lean_ctor_get(v_x_3223_, 0);
v_value_3225_ = lean_ctor_get(v_x_3223_, 1);
v_tail_3226_ = lean_ctor_get(v_x_3223_, 2);
v_isSharedCheck_3249_ = !lean_is_exclusive(v_x_3223_);
if (v_isSharedCheck_3249_ == 0)
{
v___x_3228_ = v_x_3223_;
v_isShared_3229_ = v_isSharedCheck_3249_;
goto v_resetjp_3227_;
}
else
{
lean_inc(v_tail_3226_);
lean_inc(v_value_3225_);
lean_inc(v_key_3224_);
lean_dec(v_x_3223_);
v___x_3228_ = lean_box(0);
v_isShared_3229_ = v_isSharedCheck_3249_;
goto v_resetjp_3227_;
}
v_resetjp_3227_:
{
lean_object* v___x_3230_; uint64_t v___x_3231_; uint64_t v___x_3232_; uint64_t v___x_3233_; uint64_t v_fold_3234_; uint64_t v___x_3235_; uint64_t v___x_3236_; uint64_t v___x_3237_; size_t v___x_3238_; size_t v___x_3239_; size_t v___x_3240_; size_t v___x_3241_; size_t v___x_3242_; lean_object* v___x_3243_; lean_object* v___x_3245_; 
v___x_3230_ = lean_array_get_size(v_x_3222_);
v___x_3231_ = l_Lean_instHashableFVarId_hash(v_key_3224_);
v___x_3232_ = 32ULL;
v___x_3233_ = lean_uint64_shift_right(v___x_3231_, v___x_3232_);
v_fold_3234_ = lean_uint64_xor(v___x_3231_, v___x_3233_);
v___x_3235_ = 16ULL;
v___x_3236_ = lean_uint64_shift_right(v_fold_3234_, v___x_3235_);
v___x_3237_ = lean_uint64_xor(v_fold_3234_, v___x_3236_);
v___x_3238_ = lean_uint64_to_usize(v___x_3237_);
v___x_3239_ = lean_usize_of_nat(v___x_3230_);
v___x_3240_ = ((size_t)1ULL);
v___x_3241_ = lean_usize_sub(v___x_3239_, v___x_3240_);
v___x_3242_ = lean_usize_land(v___x_3238_, v___x_3241_);
v___x_3243_ = lean_array_uget_borrowed(v_x_3222_, v___x_3242_);
lean_inc(v___x_3243_);
if (v_isShared_3229_ == 0)
{
lean_ctor_set(v___x_3228_, 2, v___x_3243_);
v___x_3245_ = v___x_3228_;
goto v_reusejp_3244_;
}
else
{
lean_object* v_reuseFailAlloc_3248_; 
v_reuseFailAlloc_3248_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3248_, 0, v_key_3224_);
lean_ctor_set(v_reuseFailAlloc_3248_, 1, v_value_3225_);
lean_ctor_set(v_reuseFailAlloc_3248_, 2, v___x_3243_);
v___x_3245_ = v_reuseFailAlloc_3248_;
goto v_reusejp_3244_;
}
v_reusejp_3244_:
{
lean_object* v___x_3246_; 
v___x_3246_ = lean_array_uset(v_x_3222_, v___x_3242_, v___x_3245_);
v_x_3222_ = v___x_3246_;
v_x_3223_ = v_tail_3226_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__5_spec__6___redArg(lean_object* v_i_3250_, lean_object* v_source_3251_, lean_object* v_target_3252_){
_start:
{
lean_object* v___x_3253_; uint8_t v___x_3254_; 
v___x_3253_ = lean_array_get_size(v_source_3251_);
v___x_3254_ = lean_nat_dec_lt(v_i_3250_, v___x_3253_);
if (v___x_3254_ == 0)
{
lean_dec_ref(v_source_3251_);
lean_dec(v_i_3250_);
return v_target_3252_;
}
else
{
lean_object* v_es_3255_; lean_object* v___x_3256_; lean_object* v_source_3257_; lean_object* v_target_3258_; lean_object* v___x_3259_; lean_object* v___x_3260_; 
v_es_3255_ = lean_array_fget(v_source_3251_, v_i_3250_);
v___x_3256_ = lean_box(0);
v_source_3257_ = lean_array_fset(v_source_3251_, v_i_3250_, v___x_3256_);
v_target_3258_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__5_spec__6_spec__11___redArg(v_target_3252_, v_es_3255_);
v___x_3259_ = lean_unsigned_to_nat(1u);
v___x_3260_ = lean_nat_add(v_i_3250_, v___x_3259_);
lean_dec(v_i_3250_);
v_i_3250_ = v___x_3260_;
v_source_3251_ = v_source_3257_;
v_target_3252_ = v_target_3258_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__5___redArg(lean_object* v_data_3262_){
_start:
{
lean_object* v___x_3263_; lean_object* v___x_3264_; lean_object* v_nbuckets_3265_; lean_object* v___x_3266_; lean_object* v___x_3267_; lean_object* v___x_3268_; lean_object* v___x_3269_; 
v___x_3263_ = lean_array_get_size(v_data_3262_);
v___x_3264_ = lean_unsigned_to_nat(2u);
v_nbuckets_3265_ = lean_nat_mul(v___x_3263_, v___x_3264_);
v___x_3266_ = lean_unsigned_to_nat(0u);
v___x_3267_ = lean_box(0);
v___x_3268_ = lean_mk_array(v_nbuckets_3265_, v___x_3267_);
v___x_3269_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__5_spec__6___redArg(v___x_3266_, v_data_3262_, v___x_3268_);
return v___x_3269_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3___redArg(lean_object* v_m_3270_, lean_object* v_a_3271_, lean_object* v_b_3272_){
_start:
{
lean_object* v_size_3273_; lean_object* v_buckets_3274_; lean_object* v___x_3275_; uint64_t v___x_3276_; uint64_t v___x_3277_; uint64_t v___x_3278_; uint64_t v_fold_3279_; uint64_t v___x_3280_; uint64_t v___x_3281_; uint64_t v___x_3282_; size_t v___x_3283_; size_t v___x_3284_; size_t v___x_3285_; size_t v___x_3286_; size_t v___x_3287_; lean_object* v_bkt_3288_; uint8_t v___x_3289_; 
v_size_3273_ = lean_ctor_get(v_m_3270_, 0);
v_buckets_3274_ = lean_ctor_get(v_m_3270_, 1);
v___x_3275_ = lean_array_get_size(v_buckets_3274_);
v___x_3276_ = l_Lean_instHashableFVarId_hash(v_a_3271_);
v___x_3277_ = 32ULL;
v___x_3278_ = lean_uint64_shift_right(v___x_3276_, v___x_3277_);
v_fold_3279_ = lean_uint64_xor(v___x_3276_, v___x_3278_);
v___x_3280_ = 16ULL;
v___x_3281_ = lean_uint64_shift_right(v_fold_3279_, v___x_3280_);
v___x_3282_ = lean_uint64_xor(v_fold_3279_, v___x_3281_);
v___x_3283_ = lean_uint64_to_usize(v___x_3282_);
v___x_3284_ = lean_usize_of_nat(v___x_3275_);
v___x_3285_ = ((size_t)1ULL);
v___x_3286_ = lean_usize_sub(v___x_3284_, v___x_3285_);
v___x_3287_ = lean_usize_land(v___x_3283_, v___x_3286_);
v_bkt_3288_ = lean_array_uget_borrowed(v_buckets_3274_, v___x_3287_);
v___x_3289_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1_spec__2___redArg(v_a_3271_, v_bkt_3288_);
if (v___x_3289_ == 0)
{
lean_object* v___x_3291_; uint8_t v_isShared_3292_; uint8_t v_isSharedCheck_3310_; 
lean_inc_ref(v_buckets_3274_);
lean_inc(v_size_3273_);
v_isSharedCheck_3310_ = !lean_is_exclusive(v_m_3270_);
if (v_isSharedCheck_3310_ == 0)
{
lean_object* v_unused_3311_; lean_object* v_unused_3312_; 
v_unused_3311_ = lean_ctor_get(v_m_3270_, 1);
lean_dec(v_unused_3311_);
v_unused_3312_ = lean_ctor_get(v_m_3270_, 0);
lean_dec(v_unused_3312_);
v___x_3291_ = v_m_3270_;
v_isShared_3292_ = v_isSharedCheck_3310_;
goto v_resetjp_3290_;
}
else
{
lean_dec(v_m_3270_);
v___x_3291_ = lean_box(0);
v_isShared_3292_ = v_isSharedCheck_3310_;
goto v_resetjp_3290_;
}
v_resetjp_3290_:
{
lean_object* v___x_3293_; lean_object* v_size_x27_3294_; lean_object* v___x_3295_; lean_object* v_buckets_x27_3296_; lean_object* v___x_3297_; lean_object* v___x_3298_; lean_object* v___x_3299_; lean_object* v___x_3300_; lean_object* v___x_3301_; uint8_t v___x_3302_; 
v___x_3293_ = lean_unsigned_to_nat(1u);
v_size_x27_3294_ = lean_nat_add(v_size_3273_, v___x_3293_);
lean_dec(v_size_3273_);
lean_inc(v_bkt_3288_);
v___x_3295_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3295_, 0, v_a_3271_);
lean_ctor_set(v___x_3295_, 1, v_b_3272_);
lean_ctor_set(v___x_3295_, 2, v_bkt_3288_);
v_buckets_x27_3296_ = lean_array_uset(v_buckets_3274_, v___x_3287_, v___x_3295_);
v___x_3297_ = lean_unsigned_to_nat(4u);
v___x_3298_ = lean_nat_mul(v_size_x27_3294_, v___x_3297_);
v___x_3299_ = lean_unsigned_to_nat(3u);
v___x_3300_ = lean_nat_div(v___x_3298_, v___x_3299_);
lean_dec(v___x_3298_);
v___x_3301_ = lean_array_get_size(v_buckets_x27_3296_);
v___x_3302_ = lean_nat_dec_le(v___x_3300_, v___x_3301_);
lean_dec(v___x_3300_);
if (v___x_3302_ == 0)
{
lean_object* v_val_3303_; lean_object* v___x_3305_; 
v_val_3303_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__5___redArg(v_buckets_x27_3296_);
if (v_isShared_3292_ == 0)
{
lean_ctor_set(v___x_3291_, 1, v_val_3303_);
lean_ctor_set(v___x_3291_, 0, v_size_x27_3294_);
v___x_3305_ = v___x_3291_;
goto v_reusejp_3304_;
}
else
{
lean_object* v_reuseFailAlloc_3306_; 
v_reuseFailAlloc_3306_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3306_, 0, v_size_x27_3294_);
lean_ctor_set(v_reuseFailAlloc_3306_, 1, v_val_3303_);
v___x_3305_ = v_reuseFailAlloc_3306_;
goto v_reusejp_3304_;
}
v_reusejp_3304_:
{
return v___x_3305_;
}
}
else
{
lean_object* v___x_3308_; 
if (v_isShared_3292_ == 0)
{
lean_ctor_set(v___x_3291_, 1, v_buckets_x27_3296_);
lean_ctor_set(v___x_3291_, 0, v_size_x27_3294_);
v___x_3308_ = v___x_3291_;
goto v_reusejp_3307_;
}
else
{
lean_object* v_reuseFailAlloc_3309_; 
v_reuseFailAlloc_3309_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3309_, 0, v_size_x27_3294_);
lean_ctor_set(v_reuseFailAlloc_3309_, 1, v_buckets_x27_3296_);
v___x_3308_ = v_reuseFailAlloc_3309_;
goto v_reusejp_3307_;
}
v_reusejp_3307_:
{
return v___x_3308_;
}
}
}
}
else
{
lean_dec(v_b_3272_);
lean_dec(v_a_3271_);
return v_m_3270_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0_spec__0___redArg(lean_object* v_a_3313_, lean_object* v_x_3314_){
_start:
{
if (lean_obj_tag(v_x_3314_) == 0)
{
lean_object* v___x_3315_; 
v___x_3315_ = lean_box(0);
return v___x_3315_;
}
else
{
lean_object* v_key_3316_; lean_object* v_value_3317_; lean_object* v_tail_3318_; uint8_t v___x_3319_; 
v_key_3316_ = lean_ctor_get(v_x_3314_, 0);
v_value_3317_ = lean_ctor_get(v_x_3314_, 1);
v_tail_3318_ = lean_ctor_get(v_x_3314_, 2);
v___x_3319_ = l_Lean_instBEqFVarId_beq(v_key_3316_, v_a_3313_);
if (v___x_3319_ == 0)
{
v_x_3314_ = v_tail_3318_;
goto _start;
}
else
{
lean_object* v___x_3321_; 
lean_inc(v_value_3317_);
v___x_3321_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3321_, 0, v_value_3317_);
return v___x_3321_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0_spec__0___redArg___boxed(lean_object* v_a_3322_, lean_object* v_x_3323_){
_start:
{
lean_object* v_res_3324_; 
v_res_3324_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0_spec__0___redArg(v_a_3322_, v_x_3323_);
lean_dec(v_x_3323_);
lean_dec(v_a_3322_);
return v_res_3324_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0___redArg(lean_object* v_m_3325_, lean_object* v_a_3326_){
_start:
{
lean_object* v_buckets_3327_; lean_object* v___x_3328_; uint64_t v___x_3329_; uint64_t v___x_3330_; uint64_t v___x_3331_; uint64_t v_fold_3332_; uint64_t v___x_3333_; uint64_t v___x_3334_; uint64_t v___x_3335_; size_t v___x_3336_; size_t v___x_3337_; size_t v___x_3338_; size_t v___x_3339_; size_t v___x_3340_; lean_object* v___x_3341_; lean_object* v___x_3342_; 
v_buckets_3327_ = lean_ctor_get(v_m_3325_, 1);
v___x_3328_ = lean_array_get_size(v_buckets_3327_);
v___x_3329_ = l_Lean_instHashableFVarId_hash(v_a_3326_);
v___x_3330_ = 32ULL;
v___x_3331_ = lean_uint64_shift_right(v___x_3329_, v___x_3330_);
v_fold_3332_ = lean_uint64_xor(v___x_3329_, v___x_3331_);
v___x_3333_ = 16ULL;
v___x_3334_ = lean_uint64_shift_right(v_fold_3332_, v___x_3333_);
v___x_3335_ = lean_uint64_xor(v_fold_3332_, v___x_3334_);
v___x_3336_ = lean_uint64_to_usize(v___x_3335_);
v___x_3337_ = lean_usize_of_nat(v___x_3328_);
v___x_3338_ = ((size_t)1ULL);
v___x_3339_ = lean_usize_sub(v___x_3337_, v___x_3338_);
v___x_3340_ = lean_usize_land(v___x_3336_, v___x_3339_);
v___x_3341_ = lean_array_uget_borrowed(v_buckets_3327_, v___x_3340_);
v___x_3342_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0_spec__0___redArg(v_a_3326_, v___x_3341_);
return v___x_3342_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0___redArg___boxed(lean_object* v_m_3343_, lean_object* v_a_3344_){
_start:
{
lean_object* v_res_3345_; 
v_res_3345_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0___redArg(v_m_3343_, v_a_3344_);
lean_dec(v_a_3344_);
lean_dec_ref(v_m_3343_);
return v_res_3345_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___lam__0___boxed(lean_object* v___x_3346_, lean_object* v_m_3347_, lean_object* v_e_3348_, lean_object* v___y_3349_, lean_object* v___y_3350_, lean_object* v___y_3351_, lean_object* v___y_3352_){
_start:
{
uint8_t v___x_19579__boxed_3353_; lean_object* v_res_3354_; 
v___x_19579__boxed_3353_ = lean_unbox(v___x_3346_);
v_res_3354_ = l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___lam__0(v___x_19579__boxed_3353_, v_m_3347_, v_e_3348_, v___y_3349_, v___y_3350_, v___y_3351_);
lean_dec(v___y_3351_);
lean_dec_ref(v___y_3350_);
lean_dec_ref(v_e_3348_);
return v_res_3354_;
}
}
static lean_object* _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__3(void){
_start:
{
lean_object* v___x_3358_; lean_object* v___x_3359_; lean_object* v___x_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; lean_object* v___x_3363_; 
v___x_3358_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__2));
v___x_3359_ = lean_unsigned_to_nat(4u);
v___x_3360_ = lean_unsigned_to_nat(384u);
v___x_3361_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__1));
v___x_3362_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__0));
v___x_3363_ = l_mkPanicMessageWithDecl(v___x_3362_, v___x_3361_, v___x_3360_, v___x_3359_, v___x_3358_);
return v___x_3363_;
}
}
static lean_object* _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__4(void){
_start:
{
lean_object* v___x_3364_; lean_object* v___x_3365_; lean_object* v___x_3366_; 
v___x_3364_ = lean_box(0);
v___x_3365_ = lean_unsigned_to_nat(16u);
v___x_3366_ = lean_mk_array(v___x_3365_, v___x_3364_);
return v___x_3366_;
}
}
static lean_object* _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__5(void){
_start:
{
lean_object* v___x_3367_; lean_object* v___x_3368_; lean_object* v___x_3369_; 
v___x_3367_ = lean_obj_once(&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__4, &l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__4_once, _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__4);
v___x_3368_ = lean_unsigned_to_nat(0u);
v___x_3369_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3369_, 0, v___x_3368_);
lean_ctor_set(v___x_3369_, 1, v___x_3367_);
return v___x_3369_;
}
}
static lean_object* _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__7(void){
_start:
{
lean_object* v___x_3371_; lean_object* v___x_3372_; 
v___x_3371_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__6));
v___x_3372_ = l_Lean_stringToMessageData(v___x_3371_);
return v___x_3372_;
}
}
static lean_object* _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__13(void){
_start:
{
lean_object* v___x_3381_; lean_object* v___x_3382_; lean_object* v___x_3383_; 
v___x_3381_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__10));
v___x_3382_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__12));
v___x_3383_ = l_Lean_Name_append(v___x_3382_, v___x_3381_);
return v___x_3383_;
}
}
static lean_object* _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__15(void){
_start:
{
lean_object* v___x_3385_; lean_object* v___x_3386_; 
v___x_3385_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__14));
v___x_3386_ = l_Lean_stringToMessageData(v___x_3385_);
return v___x_3386_;
}
}
static lean_object* _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__17(void){
_start:
{
lean_object* v___x_3388_; lean_object* v___x_3389_; 
v___x_3388_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__16));
v___x_3389_ = l_Lean_stringToMessageData(v___x_3388_);
return v___x_3389_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit(lean_object* v_m_3390_, lean_object* v_fvarId_3391_, lean_object* v_a_3392_, lean_object* v_a_3393_, lean_object* v_a_3394_){
_start:
{
lean_object* v___x_3396_; 
v___x_3396_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0___redArg(v_m_3390_, v_fvarId_3391_);
if (lean_obj_tag(v___x_3396_) == 1)
{
lean_object* v_val_3397_; lean_object* v___x_3399_; uint8_t v_isShared_3400_; uint8_t v_isSharedCheck_3507_; 
v_val_3397_ = lean_ctor_get(v___x_3396_, 0);
v_isSharedCheck_3507_ = !lean_is_exclusive(v___x_3396_);
if (v_isSharedCheck_3507_ == 0)
{
v___x_3399_ = v___x_3396_;
v_isShared_3400_ = v_isSharedCheck_3507_;
goto v_resetjp_3398_;
}
else
{
lean_inc(v_val_3397_);
lean_dec(v___x_3396_);
v___x_3399_ = lean_box(0);
v_isShared_3400_ = v_isSharedCheck_3507_;
goto v_resetjp_3398_;
}
v_resetjp_3398_:
{
lean_object* v_fst_3401_; lean_object* v_snd_3402_; lean_object* v___x_3404_; uint8_t v_isShared_3405_; uint8_t v_isSharedCheck_3506_; 
v_fst_3401_ = lean_ctor_get(v_val_3397_, 0);
v_snd_3402_ = lean_ctor_get(v_val_3397_, 1);
v_isSharedCheck_3506_ = !lean_is_exclusive(v_val_3397_);
if (v_isSharedCheck_3506_ == 0)
{
v___x_3404_ = v_val_3397_;
v_isShared_3405_ = v_isSharedCheck_3506_;
goto v_resetjp_3403_;
}
else
{
lean_inc(v_snd_3402_);
lean_inc(v_fst_3401_);
lean_dec(v_val_3397_);
v___x_3404_ = lean_box(0);
v_isShared_3405_ = v_isSharedCheck_3506_;
goto v_resetjp_3403_;
}
v_resetjp_3403_:
{
lean_object* v_tempMark_3406_; lean_object* v_doneMark_3407_; lean_object* v___x_3408_; uint8_t v___x_3409_; 
v_tempMark_3406_ = lean_ctor_get(v_a_3392_, 0);
v_doneMark_3407_ = lean_ctor_get(v_a_3392_, 1);
v___x_3408_ = l_Lean_LocalDecl_fvarId(v_fst_3401_);
v___x_3409_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1___redArg(v_doneMark_3407_, v___x_3408_);
if (v___x_3409_ == 0)
{
lean_object* v_options_3410_; lean_object* v_inheritedTraceOptions_3411_; uint8_t v_hasTrace_3412_; uint8_t v___x_3413_; lean_object* v___x_3414_; lean_object* v___f_3415_; lean_object* v___y_3417_; lean_object* v___y_3418_; lean_object* v___y_3419_; lean_object* v___y_3474_; lean_object* v_tempMark_3475_; lean_object* v___y_3476_; lean_object* v___y_3477_; 
lean_del_object(v___x_3404_);
lean_del_object(v___x_3399_);
v_options_3410_ = lean_ctor_get(v_a_3393_, 2);
v_inheritedTraceOptions_3411_ = lean_ctor_get(v_a_3393_, 13);
v_hasTrace_3412_ = lean_ctor_get_uint8(v_options_3410_, sizeof(void*)*1);
v___x_3413_ = 1;
v___x_3414_ = lean_box(v___x_3413_);
v___f_3415_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___lam__0___boxed), 7, 2);
lean_closure_set(v___f_3415_, 0, v___x_3414_);
lean_closure_set(v___f_3415_, 1, v_m_3390_);
if (v_hasTrace_3412_ == 0)
{
lean_inc_ref(v_tempMark_3406_);
v___y_3474_ = v_a_3392_;
v_tempMark_3475_ = v_tempMark_3406_;
v___y_3476_ = v_a_3393_;
v___y_3477_ = v_a_3394_;
goto v___jp_3473_;
}
else
{
lean_object* v___x_3483_; lean_object* v___x_3484_; uint8_t v___x_3485_; 
v___x_3483_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__10));
v___x_3484_ = lean_obj_once(&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__13, &l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__13_once, _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__13);
v___x_3485_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3411_, v_options_3410_, v___x_3484_);
if (v___x_3485_ == 0)
{
lean_inc_ref(v_tempMark_3406_);
v___y_3474_ = v_a_3392_;
v_tempMark_3475_ = v_tempMark_3406_;
v___y_3476_ = v_a_3393_;
v___y_3477_ = v_a_3394_;
goto v___jp_3473_;
}
else
{
lean_object* v___x_3486_; lean_object* v___x_3487_; lean_object* v___x_3488_; lean_object* v___x_3489_; lean_object* v___x_3490_; lean_object* v___x_3491_; lean_object* v___x_3492_; lean_object* v___x_3493_; lean_object* v___x_3494_; lean_object* v___x_3495_; 
v___x_3486_ = lean_obj_once(&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__15, &l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__15_once, _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__15);
lean_inc(v___x_3408_);
v___x_3487_ = l_Lean_mkFVar(v___x_3408_);
v___x_3488_ = l_Lean_MessageData_ofExpr(v___x_3487_);
v___x_3489_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3489_, 0, v___x_3486_);
lean_ctor_set(v___x_3489_, 1, v___x_3488_);
v___x_3490_ = lean_obj_once(&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__17, &l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__17_once, _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__17);
v___x_3491_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3491_, 0, v___x_3489_);
lean_ctor_set(v___x_3491_, 1, v___x_3490_);
v___x_3492_ = l_Lean_LocalDecl_type(v_fst_3401_);
v___x_3493_ = l_Lean_MessageData_ofExpr(v___x_3492_);
v___x_3494_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3494_, 0, v___x_3491_);
lean_ctor_set(v___x_3494_, 1, v___x_3493_);
v___x_3495_ = l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6(v___x_3483_, v___x_3494_, v_a_3392_, v_a_3393_, v_a_3394_);
if (lean_obj_tag(v___x_3495_) == 0)
{
lean_object* v_a_3496_; lean_object* v_snd_3497_; lean_object* v_tempMark_3498_; 
v_a_3496_ = lean_ctor_get(v___x_3495_, 0);
lean_inc(v_a_3496_);
lean_dec_ref_known(v___x_3495_, 1);
v_snd_3497_ = lean_ctor_get(v_a_3496_, 1);
lean_inc(v_snd_3497_);
lean_dec(v_a_3496_);
v_tempMark_3498_ = lean_ctor_get(v_snd_3497_, 0);
lean_inc_ref(v_tempMark_3498_);
v___y_3474_ = v_snd_3497_;
v_tempMark_3475_ = v_tempMark_3498_;
v___y_3476_ = v_a_3393_;
v___y_3477_ = v_a_3394_;
goto v___jp_3473_;
}
else
{
lean_dec_ref(v___f_3415_);
lean_dec(v___x_3408_);
lean_dec(v_snd_3402_);
lean_dec(v_fst_3401_);
return v___x_3495_;
}
}
}
v___jp_3416_:
{
uint8_t v___x_3420_; uint8_t v___x_3421_; 
v___x_3420_ = l_Lean_LocalDecl_isLet(v_fst_3401_, v___x_3413_);
v___x_3421_ = lean_bool_not(v___x_3420_);
if (v___x_3421_ == 0)
{
lean_object* v___x_3422_; lean_object* v___x_3423_; 
lean_dec_ref(v___f_3415_);
lean_dec(v___x_3408_);
lean_dec(v_snd_3402_);
lean_dec(v_fst_3401_);
v___x_3422_ = lean_obj_once(&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__3, &l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__3_once, _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__3);
v___x_3423_ = l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2(v___x_3422_, v___y_3417_, v___y_3418_, v___y_3419_);
return v___x_3423_;
}
else
{
lean_object* v_tempMark_3424_; lean_object* v_doneMark_3425_; lean_object* v_newDecls_3426_; lean_object* v_newArgs_3427_; lean_object* v___x_3429_; uint8_t v_isShared_3430_; uint8_t v_isSharedCheck_3472_; 
v_tempMark_3424_ = lean_ctor_get(v___y_3417_, 0);
v_doneMark_3425_ = lean_ctor_get(v___y_3417_, 1);
v_newDecls_3426_ = lean_ctor_get(v___y_3417_, 2);
v_newArgs_3427_ = lean_ctor_get(v___y_3417_, 3);
v_isSharedCheck_3472_ = !lean_is_exclusive(v___y_3417_);
if (v_isSharedCheck_3472_ == 0)
{
v___x_3429_ = v___y_3417_;
v_isShared_3430_ = v_isSharedCheck_3472_;
goto v_resetjp_3428_;
}
else
{
lean_inc(v_newArgs_3427_);
lean_inc(v_newDecls_3426_);
lean_inc(v_doneMark_3425_);
lean_inc(v_tempMark_3424_);
lean_dec(v___y_3417_);
v___x_3429_ = lean_box(0);
v_isShared_3430_ = v_isSharedCheck_3472_;
goto v_resetjp_3428_;
}
v_resetjp_3428_:
{
lean_object* v___x_3431_; lean_object* v___x_3432_; lean_object* v___x_3433_; lean_object* v___x_3434_; lean_object* v___x_3436_; 
v___x_3431_ = lean_obj_once(&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__5, &l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__5_once, _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__5);
v___x_3432_ = lean_st_mk_ref(v___x_3431_);
v___x_3433_ = lean_box(0);
lean_inc(v___x_3408_);
v___x_3434_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3___redArg(v_tempMark_3424_, v___x_3408_, v___x_3433_);
if (v_isShared_3430_ == 0)
{
lean_ctor_set(v___x_3429_, 0, v___x_3434_);
v___x_3436_ = v___x_3429_;
goto v_reusejp_3435_;
}
else
{
lean_object* v_reuseFailAlloc_3471_; 
v_reuseFailAlloc_3471_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3471_, 0, v___x_3434_);
lean_ctor_set(v_reuseFailAlloc_3471_, 1, v_doneMark_3425_);
lean_ctor_set(v_reuseFailAlloc_3471_, 2, v_newDecls_3426_);
lean_ctor_set(v_reuseFailAlloc_3471_, 3, v_newArgs_3427_);
v___x_3436_ = v_reuseFailAlloc_3471_;
goto v_reusejp_3435_;
}
v_reusejp_3435_:
{
lean_object* v___x_3437_; lean_object* v___x_3438_; 
v___x_3437_ = l_Lean_LocalDecl_type(v_fst_3401_);
v___x_3438_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4(v___f_3415_, v___x_3437_, v___x_3432_, v___x_3436_, v___y_3418_, v___y_3419_);
if (lean_obj_tag(v___x_3438_) == 0)
{
lean_object* v_a_3439_; lean_object* v___x_3441_; uint8_t v_isShared_3442_; uint8_t v_isSharedCheck_3470_; 
v_a_3439_ = lean_ctor_get(v___x_3438_, 0);
v_isSharedCheck_3470_ = !lean_is_exclusive(v___x_3438_);
if (v_isSharedCheck_3470_ == 0)
{
v___x_3441_ = v___x_3438_;
v_isShared_3442_ = v_isSharedCheck_3470_;
goto v_resetjp_3440_;
}
else
{
lean_inc(v_a_3439_);
lean_dec(v___x_3438_);
v___x_3441_ = lean_box(0);
v_isShared_3442_ = v_isSharedCheck_3470_;
goto v_resetjp_3440_;
}
v_resetjp_3440_:
{
lean_object* v_snd_3443_; lean_object* v___x_3445_; uint8_t v_isShared_3446_; uint8_t v_isSharedCheck_3468_; 
v_snd_3443_ = lean_ctor_get(v_a_3439_, 1);
v_isSharedCheck_3468_ = !lean_is_exclusive(v_a_3439_);
if (v_isSharedCheck_3468_ == 0)
{
lean_object* v_unused_3469_; 
v_unused_3469_ = lean_ctor_get(v_a_3439_, 0);
lean_dec(v_unused_3469_);
v___x_3445_ = v_a_3439_;
v_isShared_3446_ = v_isSharedCheck_3468_;
goto v_resetjp_3444_;
}
else
{
lean_inc(v_snd_3443_);
lean_dec(v_a_3439_);
v___x_3445_ = lean_box(0);
v_isShared_3446_ = v_isSharedCheck_3468_;
goto v_resetjp_3444_;
}
v_resetjp_3444_:
{
lean_object* v___x_3447_; lean_object* v_tempMark_3448_; lean_object* v_doneMark_3449_; lean_object* v_newDecls_3450_; lean_object* v_newArgs_3451_; lean_object* v___x_3453_; uint8_t v_isShared_3454_; uint8_t v_isSharedCheck_3467_; 
v___x_3447_ = lean_st_ref_get(v___x_3432_);
lean_dec(v___x_3432_);
lean_dec(v___x_3447_);
v_tempMark_3448_ = lean_ctor_get(v_snd_3443_, 0);
v_doneMark_3449_ = lean_ctor_get(v_snd_3443_, 1);
v_newDecls_3450_ = lean_ctor_get(v_snd_3443_, 2);
v_newArgs_3451_ = lean_ctor_get(v_snd_3443_, 3);
v_isSharedCheck_3467_ = !lean_is_exclusive(v_snd_3443_);
if (v_isSharedCheck_3467_ == 0)
{
v___x_3453_ = v_snd_3443_;
v_isShared_3454_ = v_isSharedCheck_3467_;
goto v_resetjp_3452_;
}
else
{
lean_inc(v_newArgs_3451_);
lean_inc(v_newDecls_3450_);
lean_inc(v_doneMark_3449_);
lean_inc(v_tempMark_3448_);
lean_dec(v_snd_3443_);
v___x_3453_ = lean_box(0);
v_isShared_3454_ = v_isSharedCheck_3467_;
goto v_resetjp_3452_;
}
v_resetjp_3452_:
{
lean_object* v___x_3455_; lean_object* v___x_3456_; lean_object* v___x_3457_; lean_object* v___x_3459_; 
v___x_3455_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3___redArg(v_doneMark_3449_, v___x_3408_, v___x_3433_);
v___x_3456_ = lean_array_push(v_newDecls_3450_, v_fst_3401_);
v___x_3457_ = lean_array_push(v_newArgs_3451_, v_snd_3402_);
if (v_isShared_3454_ == 0)
{
lean_ctor_set(v___x_3453_, 3, v___x_3457_);
lean_ctor_set(v___x_3453_, 2, v___x_3456_);
lean_ctor_set(v___x_3453_, 1, v___x_3455_);
v___x_3459_ = v___x_3453_;
goto v_reusejp_3458_;
}
else
{
lean_object* v_reuseFailAlloc_3466_; 
v_reuseFailAlloc_3466_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3466_, 0, v_tempMark_3448_);
lean_ctor_set(v_reuseFailAlloc_3466_, 1, v___x_3455_);
lean_ctor_set(v_reuseFailAlloc_3466_, 2, v___x_3456_);
lean_ctor_set(v_reuseFailAlloc_3466_, 3, v___x_3457_);
v___x_3459_ = v_reuseFailAlloc_3466_;
goto v_reusejp_3458_;
}
v_reusejp_3458_:
{
lean_object* v___x_3461_; 
if (v_isShared_3446_ == 0)
{
lean_ctor_set(v___x_3445_, 1, v___x_3459_);
lean_ctor_set(v___x_3445_, 0, v___x_3433_);
v___x_3461_ = v___x_3445_;
goto v_reusejp_3460_;
}
else
{
lean_object* v_reuseFailAlloc_3465_; 
v_reuseFailAlloc_3465_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3465_, 0, v___x_3433_);
lean_ctor_set(v_reuseFailAlloc_3465_, 1, v___x_3459_);
v___x_3461_ = v_reuseFailAlloc_3465_;
goto v_reusejp_3460_;
}
v_reusejp_3460_:
{
lean_object* v___x_3463_; 
if (v_isShared_3442_ == 0)
{
lean_ctor_set(v___x_3441_, 0, v___x_3461_);
v___x_3463_ = v___x_3441_;
goto v_reusejp_3462_;
}
else
{
lean_object* v_reuseFailAlloc_3464_; 
v_reuseFailAlloc_3464_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3464_, 0, v___x_3461_);
v___x_3463_ = v_reuseFailAlloc_3464_;
goto v_reusejp_3462_;
}
v_reusejp_3462_:
{
return v___x_3463_;
}
}
}
}
}
}
}
else
{
lean_dec(v___x_3432_);
lean_dec(v___x_3408_);
lean_dec(v_snd_3402_);
lean_dec(v_fst_3401_);
return v___x_3438_;
}
}
}
}
}
v___jp_3473_:
{
uint8_t v___x_3478_; 
v___x_3478_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1___redArg(v_tempMark_3475_, v___x_3408_);
lean_dec_ref(v_tempMark_3475_);
if (v___x_3478_ == 0)
{
v___y_3417_ = v___y_3474_;
v___y_3418_ = v___y_3476_;
v___y_3419_ = v___y_3477_;
goto v___jp_3416_;
}
else
{
lean_object* v___x_3479_; lean_object* v___x_3480_; 
lean_dec_ref(v___y_3474_);
v___x_3479_ = lean_obj_once(&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__7, &l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__7_once, _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__7);
v___x_3480_ = l_Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5___redArg(v___x_3479_, v___y_3476_, v___y_3477_);
if (lean_obj_tag(v___x_3480_) == 0)
{
lean_object* v_a_3481_; lean_object* v_snd_3482_; 
v_a_3481_ = lean_ctor_get(v___x_3480_, 0);
lean_inc(v_a_3481_);
lean_dec_ref_known(v___x_3480_, 1);
v_snd_3482_ = lean_ctor_get(v_a_3481_, 1);
lean_inc(v_snd_3482_);
lean_dec(v_a_3481_);
v___y_3417_ = v_snd_3482_;
v___y_3418_ = v___y_3476_;
v___y_3419_ = v___y_3477_;
goto v___jp_3416_;
}
else
{
lean_dec_ref(v___f_3415_);
lean_dec(v___x_3408_);
lean_dec(v_snd_3402_);
lean_dec(v_fst_3401_);
return v___x_3480_;
}
}
}
}
else
{
lean_object* v___x_3499_; lean_object* v___x_3501_; 
lean_dec(v___x_3408_);
lean_dec(v_snd_3402_);
lean_dec(v_fst_3401_);
lean_dec_ref(v_m_3390_);
v___x_3499_ = lean_box(0);
if (v_isShared_3405_ == 0)
{
lean_ctor_set(v___x_3404_, 1, v_a_3392_);
lean_ctor_set(v___x_3404_, 0, v___x_3499_);
v___x_3501_ = v___x_3404_;
goto v_reusejp_3500_;
}
else
{
lean_object* v_reuseFailAlloc_3505_; 
v_reuseFailAlloc_3505_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3505_, 0, v___x_3499_);
lean_ctor_set(v_reuseFailAlloc_3505_, 1, v_a_3392_);
v___x_3501_ = v_reuseFailAlloc_3505_;
goto v_reusejp_3500_;
}
v_reusejp_3500_:
{
lean_object* v___x_3503_; 
if (v_isShared_3400_ == 0)
{
lean_ctor_set_tag(v___x_3399_, 0);
lean_ctor_set(v___x_3399_, 0, v___x_3501_);
v___x_3503_ = v___x_3399_;
goto v_reusejp_3502_;
}
else
{
lean_object* v_reuseFailAlloc_3504_; 
v_reuseFailAlloc_3504_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3504_, 0, v___x_3501_);
v___x_3503_ = v_reuseFailAlloc_3504_;
goto v_reusejp_3502_;
}
v_reusejp_3502_:
{
return v___x_3503_;
}
}
}
}
}
}
else
{
lean_object* v___x_3508_; lean_object* v___x_3509_; lean_object* v___x_3510_; 
lean_dec(v___x_3396_);
lean_dec_ref(v_m_3390_);
v___x_3508_ = lean_box(0);
v___x_3509_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3509_, 0, v___x_3508_);
lean_ctor_set(v___x_3509_, 1, v_a_3392_);
v___x_3510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3510_, 0, v___x_3509_);
return v___x_3510_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___lam__0(uint8_t v___x_3511_, lean_object* v_m_3512_, lean_object* v_e_3513_, lean_object* v___y_3514_, lean_object* v___y_3515_, lean_object* v___y_3516_){
_start:
{
lean_object* v___y_3519_; uint8_t v___x_3523_; 
v___x_3523_ = l_Lean_Expr_hasFVar(v_e_3513_);
if (v___x_3523_ == 0)
{
lean_object* v___x_3524_; lean_object* v___x_3525_; lean_object* v___x_3526_; 
lean_dec_ref(v_m_3512_);
v___x_3524_ = lean_box(v___x_3523_);
v___x_3525_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3525_, 0, v___x_3524_);
lean_ctor_set(v___x_3525_, 1, v___y_3514_);
v___x_3526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3526_, 0, v___x_3525_);
return v___x_3526_;
}
else
{
uint8_t v___x_3527_; 
v___x_3527_ = l_Lean_Expr_isFVar(v_e_3513_);
if (v___x_3527_ == 0)
{
lean_dec_ref(v_m_3512_);
v___y_3519_ = v___y_3514_;
goto v___jp_3518_;
}
else
{
lean_object* v___x_3528_; lean_object* v___x_3529_; 
v___x_3528_ = l_Lean_Expr_fvarId_x21(v_e_3513_);
v___x_3529_ = l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit(v_m_3512_, v___x_3528_, v___y_3514_, v___y_3515_, v___y_3516_);
lean_dec(v___x_3528_);
if (lean_obj_tag(v___x_3529_) == 0)
{
lean_object* v_a_3530_; lean_object* v_snd_3531_; 
v_a_3530_ = lean_ctor_get(v___x_3529_, 0);
lean_inc(v_a_3530_);
lean_dec_ref_known(v___x_3529_, 1);
v_snd_3531_ = lean_ctor_get(v_a_3530_, 1);
lean_inc(v_snd_3531_);
lean_dec(v_a_3530_);
v___y_3519_ = v_snd_3531_;
goto v___jp_3518_;
}
else
{
lean_object* v_a_3532_; lean_object* v___x_3534_; uint8_t v_isShared_3535_; uint8_t v_isSharedCheck_3539_; 
v_a_3532_ = lean_ctor_get(v___x_3529_, 0);
v_isSharedCheck_3539_ = !lean_is_exclusive(v___x_3529_);
if (v_isSharedCheck_3539_ == 0)
{
v___x_3534_ = v___x_3529_;
v_isShared_3535_ = v_isSharedCheck_3539_;
goto v_resetjp_3533_;
}
else
{
lean_inc(v_a_3532_);
lean_dec(v___x_3529_);
v___x_3534_ = lean_box(0);
v_isShared_3535_ = v_isSharedCheck_3539_;
goto v_resetjp_3533_;
}
v_resetjp_3533_:
{
lean_object* v___x_3537_; 
if (v_isShared_3535_ == 0)
{
v___x_3537_ = v___x_3534_;
goto v_reusejp_3536_;
}
else
{
lean_object* v_reuseFailAlloc_3538_; 
v_reuseFailAlloc_3538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3538_, 0, v_a_3532_);
v___x_3537_ = v_reuseFailAlloc_3538_;
goto v_reusejp_3536_;
}
v_reusejp_3536_:
{
return v___x_3537_;
}
}
}
}
}
v___jp_3518_:
{
lean_object* v___x_3520_; lean_object* v___x_3521_; lean_object* v___x_3522_; 
v___x_3520_ = lean_box(v___x_3511_);
v___x_3521_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3521_, 0, v___x_3520_);
lean_ctor_set(v___x_3521_, 1, v___y_3519_);
v___x_3522_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3522_, 0, v___x_3521_);
return v___x_3522_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___boxed(lean_object* v_m_3540_, lean_object* v_fvarId_3541_, lean_object* v_a_3542_, lean_object* v_a_3543_, lean_object* v_a_3544_, lean_object* v_a_3545_){
_start:
{
lean_object* v_res_3546_; 
v_res_3546_ = l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit(v_m_3540_, v_fvarId_3541_, v_a_3542_, v_a_3543_, v_a_3544_);
lean_dec(v_a_3544_);
lean_dec_ref(v_a_3543_);
lean_dec(v_fvarId_3541_);
return v_res_3546_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0(lean_object* v_00_u03b2_3547_, lean_object* v_m_3548_, lean_object* v_a_3549_){
_start:
{
lean_object* v___x_3550_; 
v___x_3550_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0___redArg(v_m_3548_, v_a_3549_);
return v___x_3550_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0___boxed(lean_object* v_00_u03b2_3551_, lean_object* v_m_3552_, lean_object* v_a_3553_){
_start:
{
lean_object* v_res_3554_; 
v_res_3554_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0(v_00_u03b2_3551_, v_m_3552_, v_a_3553_);
lean_dec(v_a_3553_);
lean_dec_ref(v_m_3552_);
return v_res_3554_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1(lean_object* v_00_u03b2_3555_, lean_object* v_m_3556_, lean_object* v_a_3557_){
_start:
{
uint8_t v___x_3558_; 
v___x_3558_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1___redArg(v_m_3556_, v_a_3557_);
return v___x_3558_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1___boxed(lean_object* v_00_u03b2_3559_, lean_object* v_m_3560_, lean_object* v_a_3561_){
_start:
{
uint8_t v_res_3562_; lean_object* v_r_3563_; 
v_res_3562_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1(v_00_u03b2_3559_, v_m_3560_, v_a_3561_);
lean_dec(v_a_3561_);
lean_dec_ref(v_m_3560_);
v_r_3563_ = lean_box(v_res_3562_);
return v_r_3563_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3(lean_object* v_00_u03b2_3564_, lean_object* v_m_3565_, lean_object* v_a_3566_, lean_object* v_b_3567_){
_start:
{
lean_object* v___x_3568_; 
v___x_3568_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3___redArg(v_m_3565_, v_a_3566_, v_b_3567_);
return v___x_3568_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5(lean_object* v_00_u03b1_3569_, lean_object* v_msg_3570_, lean_object* v___y_3571_, lean_object* v___y_3572_, lean_object* v___y_3573_){
_start:
{
lean_object* v___x_3575_; 
v___x_3575_ = l_Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5___redArg(v_msg_3570_, v___y_3572_, v___y_3573_);
return v___x_3575_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5___boxed(lean_object* v_00_u03b1_3576_, lean_object* v_msg_3577_, lean_object* v___y_3578_, lean_object* v___y_3579_, lean_object* v___y_3580_, lean_object* v___y_3581_){
_start:
{
lean_object* v_res_3582_; 
v_res_3582_ = l_Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5(v_00_u03b1_3576_, v_msg_3577_, v___y_3578_, v___y_3579_, v___y_3580_);
lean_dec(v___y_3580_);
lean_dec_ref(v___y_3579_);
lean_dec_ref(v___y_3578_);
return v_res_3582_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0_spec__0(lean_object* v_00_u03b2_3583_, lean_object* v_a_3584_, lean_object* v_x_3585_){
_start:
{
lean_object* v___x_3586_; 
v___x_3586_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0_spec__0___redArg(v_a_3584_, v_x_3585_);
return v___x_3586_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3587_, lean_object* v_a_3588_, lean_object* v_x_3589_){
_start:
{
lean_object* v_res_3590_; 
v_res_3590_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0_spec__0(v_00_u03b2_3587_, v_a_3588_, v_x_3589_);
lean_dec(v_x_3589_);
lean_dec(v_a_3588_);
return v_res_3590_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1_spec__2(lean_object* v_00_u03b2_3591_, lean_object* v_a_3592_, lean_object* v_x_3593_){
_start:
{
uint8_t v___x_3594_; 
v___x_3594_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1_spec__2___redArg(v_a_3592_, v_x_3593_);
return v___x_3594_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1_spec__2___boxed(lean_object* v_00_u03b2_3595_, lean_object* v_a_3596_, lean_object* v_x_3597_){
_start:
{
uint8_t v_res_3598_; lean_object* v_r_3599_; 
v_res_3598_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1_spec__2(v_00_u03b2_3595_, v_a_3596_, v_x_3597_);
lean_dec(v_x_3597_);
lean_dec(v_a_3596_);
v_r_3599_ = lean_box(v_res_3598_);
return v_r_3599_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__5(lean_object* v_00_u03b2_3600_, lean_object* v_data_3601_){
_start:
{
lean_object* v___x_3602_; 
v___x_3602_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__5___redArg(v_data_3601_);
return v___x_3602_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4_spec__7(lean_object* v_00_u03b2_3603_, lean_object* v_m_3604_, lean_object* v_a_3605_){
_start:
{
lean_object* v___x_3606_; 
v___x_3606_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4_spec__7___redArg(v_m_3604_, v_a_3605_);
return v___x_3606_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4_spec__7___boxed(lean_object* v_00_u03b2_3607_, lean_object* v_m_3608_, lean_object* v_a_3609_){
_start:
{
lean_object* v_res_3610_; 
v_res_3610_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4_spec__7(v_00_u03b2_3607_, v_m_3608_, v_a_3609_);
lean_dec_ref(v_a_3609_);
lean_dec_ref(v_m_3608_);
return v_res_3610_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4_spec__8(lean_object* v_00_u03b2_3611_, lean_object* v_m_3612_, lean_object* v_a_3613_, lean_object* v_b_3614_){
_start:
{
lean_object* v___x_3615_; 
v___x_3615_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4_spec__8___redArg(v_m_3612_, v_a_3613_, v_b_3614_);
return v___x_3615_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__5_spec__6(lean_object* v_00_u03b2_3616_, lean_object* v_i_3617_, lean_object* v_source_3618_, lean_object* v_target_3619_){
_start:
{
lean_object* v___x_3620_; 
v___x_3620_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__5_spec__6___redArg(v_i_3617_, v_source_3618_, v_target_3619_);
return v___x_3620_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4_spec__7_spec__9(lean_object* v_00_u03b2_3621_, lean_object* v_a_3622_, lean_object* v_x_3623_){
_start:
{
lean_object* v___x_3624_; 
v___x_3624_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4_spec__7_spec__9___redArg(v_a_3622_, v_x_3623_);
return v___x_3624_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4_spec__7_spec__9___boxed(lean_object* v_00_u03b2_3625_, lean_object* v_a_3626_, lean_object* v_x_3627_){
_start:
{
lean_object* v_res_3628_; 
v_res_3628_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4_spec__7_spec__9(v_00_u03b2_3625_, v_a_3626_, v_x_3627_);
lean_dec(v_x_3627_);
lean_dec_ref(v_a_3626_);
return v_res_3628_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4_spec__8_spec__11(lean_object* v_00_u03b2_3629_, lean_object* v_a_3630_, lean_object* v_x_3631_){
_start:
{
uint8_t v___x_3632_; 
v___x_3632_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4_spec__8_spec__11___redArg(v_a_3630_, v_x_3631_);
return v___x_3632_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4_spec__8_spec__11___boxed(lean_object* v_00_u03b2_3633_, lean_object* v_a_3634_, lean_object* v_x_3635_){
_start:
{
uint8_t v_res_3636_; lean_object* v_r_3637_; 
v_res_3636_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4_spec__8_spec__11(v_00_u03b2_3633_, v_a_3634_, v_x_3635_);
lean_dec(v_x_3635_);
lean_dec_ref(v_a_3634_);
v_r_3637_ = lean_box(v_res_3636_);
return v_r_3637_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4_spec__8_spec__12(lean_object* v_00_u03b2_3638_, lean_object* v_data_3639_){
_start:
{
lean_object* v___x_3640_; 
v___x_3640_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4_spec__8_spec__12___redArg(v_data_3639_);
return v___x_3640_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4_spec__8_spec__13(lean_object* v_00_u03b2_3641_, lean_object* v_a_3642_, lean_object* v_b_3643_, lean_object* v_x_3644_){
_start:
{
lean_object* v___x_3645_; 
v___x_3645_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4_spec__8_spec__13___redArg(v_a_3642_, v_b_3643_, v_x_3644_);
return v___x_3645_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__5_spec__6_spec__11(lean_object* v_00_u03b2_3646_, lean_object* v_x_3647_, lean_object* v_x_3648_){
_start:
{
lean_object* v___x_3649_; 
v___x_3649_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__5_spec__6_spec__11___redArg(v_x_3647_, v_x_3648_);
return v___x_3649_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4_spec__8_spec__12_spec__17(lean_object* v_00_u03b2_3650_, lean_object* v_i_3651_, lean_object* v_source_3652_, lean_object* v_target_3653_){
_start:
{
lean_object* v___x_3654_; 
v___x_3654_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4_spec__8_spec__12_spec__17___redArg(v_i_3651_, v_source_3652_, v_target_3653_);
return v___x_3654_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4_spec__8_spec__12_spec__17_spec__18(lean_object* v_00_u03b2_3655_, lean_object* v_x_3656_, lean_object* v_x_3657_){
_start:
{
lean_object* v___x_3658_; 
v___x_3658_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4_spec__8_spec__12_spec__17_spec__18___redArg(v_x_3656_, v_x_3657_);
return v___x_3658_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__0(lean_object* v_msg_3660_, lean_object* v___y_3661_, lean_object* v___y_3662_){
_start:
{
lean_object* v___f_3664_; lean_object* v___x_8561__overap_3665_; lean_object* v___x_3666_; 
v___f_3664_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__0___closed__0));
v___x_8561__overap_3665_ = lean_panic_fn_borrowed(v___f_3664_, v_msg_3660_);
lean_inc(v___y_3662_);
lean_inc_ref(v___y_3661_);
v___x_3666_ = lean_apply_3(v___x_8561__overap_3665_, v___y_3661_, v___y_3662_, lean_box(0));
return v___x_3666_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__0___boxed(lean_object* v_msg_3667_, lean_object* v___y_3668_, lean_object* v___y_3669_, lean_object* v___y_3670_){
_start:
{
lean_object* v_res_3671_; 
v_res_3671_ = l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__0(v_msg_3667_, v___y_3668_, v___y_3669_);
lean_dec(v___y_3669_);
lean_dec_ref(v___y_3668_);
return v_res_3671_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___lam__0(lean_object* v_newDecls_3672_, lean_object* v_newArgs_3673_, lean_object* v_____r_3674_, lean_object* v___y_3675_, lean_object* v___y_3676_, lean_object* v___y_3677_){
_start:
{
lean_object* v___x_3679_; lean_object* v___x_3680_; lean_object* v___x_3681_; 
v___x_3679_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3679_, 0, v_newDecls_3672_);
lean_ctor_set(v___x_3679_, 1, v_newArgs_3673_);
v___x_3680_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3680_, 0, v___x_3679_);
lean_ctor_set(v___x_3680_, 1, v___y_3675_);
v___x_3681_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3681_, 0, v___x_3680_);
return v___x_3681_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___lam__0___boxed(lean_object* v_newDecls_3682_, lean_object* v_newArgs_3683_, lean_object* v_____r_3684_, lean_object* v___y_3685_, lean_object* v___y_3686_, lean_object* v___y_3687_, lean_object* v___y_3688_){
_start:
{
lean_object* v_res_3689_; 
v_res_3689_ = l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___lam__0(v_newDecls_3682_, v_newArgs_3683_, v_____r_3684_, v___y_3685_, v___y_3686_, v___y_3687_);
lean_dec(v___y_3687_);
lean_dec_ref(v___y_3686_);
return v_res_3689_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__6(lean_object* v_cls_3690_, lean_object* v_msg_3691_, lean_object* v___y_3692_, lean_object* v___y_3693_){
_start:
{
lean_object* v_ref_3695_; lean_object* v___x_3696_; lean_object* v_a_3697_; lean_object* v___x_3699_; uint8_t v_isShared_3700_; uint8_t v_isSharedCheck_3741_; 
v_ref_3695_ = lean_ctor_get(v___y_3692_, 5);
v___x_3696_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10(v_msg_3691_, v___y_3692_, v___y_3693_);
v_a_3697_ = lean_ctor_get(v___x_3696_, 0);
v_isSharedCheck_3741_ = !lean_is_exclusive(v___x_3696_);
if (v_isSharedCheck_3741_ == 0)
{
v___x_3699_ = v___x_3696_;
v_isShared_3700_ = v_isSharedCheck_3741_;
goto v_resetjp_3698_;
}
else
{
lean_inc(v_a_3697_);
lean_dec(v___x_3696_);
v___x_3699_ = lean_box(0);
v_isShared_3700_ = v_isSharedCheck_3741_;
goto v_resetjp_3698_;
}
v_resetjp_3698_:
{
lean_object* v___x_3701_; lean_object* v_traceState_3702_; lean_object* v_env_3703_; lean_object* v_nextMacroScope_3704_; lean_object* v_ngen_3705_; lean_object* v_auxDeclNGen_3706_; lean_object* v_cache_3707_; lean_object* v_messages_3708_; lean_object* v_infoState_3709_; lean_object* v_snapshotTasks_3710_; lean_object* v___x_3712_; uint8_t v_isShared_3713_; uint8_t v_isSharedCheck_3740_; 
v___x_3701_ = lean_st_ref_take(v___y_3693_);
v_traceState_3702_ = lean_ctor_get(v___x_3701_, 4);
v_env_3703_ = lean_ctor_get(v___x_3701_, 0);
v_nextMacroScope_3704_ = lean_ctor_get(v___x_3701_, 1);
v_ngen_3705_ = lean_ctor_get(v___x_3701_, 2);
v_auxDeclNGen_3706_ = lean_ctor_get(v___x_3701_, 3);
v_cache_3707_ = lean_ctor_get(v___x_3701_, 5);
v_messages_3708_ = lean_ctor_get(v___x_3701_, 6);
v_infoState_3709_ = lean_ctor_get(v___x_3701_, 7);
v_snapshotTasks_3710_ = lean_ctor_get(v___x_3701_, 8);
v_isSharedCheck_3740_ = !lean_is_exclusive(v___x_3701_);
if (v_isSharedCheck_3740_ == 0)
{
v___x_3712_ = v___x_3701_;
v_isShared_3713_ = v_isSharedCheck_3740_;
goto v_resetjp_3711_;
}
else
{
lean_inc(v_snapshotTasks_3710_);
lean_inc(v_infoState_3709_);
lean_inc(v_messages_3708_);
lean_inc(v_cache_3707_);
lean_inc(v_traceState_3702_);
lean_inc(v_auxDeclNGen_3706_);
lean_inc(v_ngen_3705_);
lean_inc(v_nextMacroScope_3704_);
lean_inc(v_env_3703_);
lean_dec(v___x_3701_);
v___x_3712_ = lean_box(0);
v_isShared_3713_ = v_isSharedCheck_3740_;
goto v_resetjp_3711_;
}
v_resetjp_3711_:
{
uint64_t v_tid_3714_; lean_object* v_traces_3715_; lean_object* v___x_3717_; uint8_t v_isShared_3718_; uint8_t v_isSharedCheck_3739_; 
v_tid_3714_ = lean_ctor_get_uint64(v_traceState_3702_, sizeof(void*)*1);
v_traces_3715_ = lean_ctor_get(v_traceState_3702_, 0);
v_isSharedCheck_3739_ = !lean_is_exclusive(v_traceState_3702_);
if (v_isSharedCheck_3739_ == 0)
{
v___x_3717_ = v_traceState_3702_;
v_isShared_3718_ = v_isSharedCheck_3739_;
goto v_resetjp_3716_;
}
else
{
lean_inc(v_traces_3715_);
lean_dec(v_traceState_3702_);
v___x_3717_ = lean_box(0);
v_isShared_3718_ = v_isSharedCheck_3739_;
goto v_resetjp_3716_;
}
v_resetjp_3716_:
{
lean_object* v___x_3719_; double v___x_3720_; uint8_t v___x_3721_; lean_object* v___x_3722_; lean_object* v___x_3723_; lean_object* v___x_3724_; lean_object* v___x_3725_; lean_object* v___x_3726_; lean_object* v___x_3727_; lean_object* v___x_3729_; 
v___x_3719_ = lean_box(0);
v___x_3720_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6___closed__0);
v___x_3721_ = 0;
v___x_3722_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6___closed__1));
v___x_3723_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3723_, 0, v_cls_3690_);
lean_ctor_set(v___x_3723_, 1, v___x_3719_);
lean_ctor_set(v___x_3723_, 2, v___x_3722_);
lean_ctor_set_float(v___x_3723_, sizeof(void*)*3, v___x_3720_);
lean_ctor_set_float(v___x_3723_, sizeof(void*)*3 + 8, v___x_3720_);
lean_ctor_set_uint8(v___x_3723_, sizeof(void*)*3 + 16, v___x_3721_);
v___x_3724_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6___closed__2));
v___x_3725_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3725_, 0, v___x_3723_);
lean_ctor_set(v___x_3725_, 1, v_a_3697_);
lean_ctor_set(v___x_3725_, 2, v___x_3724_);
lean_inc(v_ref_3695_);
v___x_3726_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3726_, 0, v_ref_3695_);
lean_ctor_set(v___x_3726_, 1, v___x_3725_);
v___x_3727_ = l_Lean_PersistentArray_push___redArg(v_traces_3715_, v___x_3726_);
if (v_isShared_3718_ == 0)
{
lean_ctor_set(v___x_3717_, 0, v___x_3727_);
v___x_3729_ = v___x_3717_;
goto v_reusejp_3728_;
}
else
{
lean_object* v_reuseFailAlloc_3738_; 
v_reuseFailAlloc_3738_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3738_, 0, v___x_3727_);
lean_ctor_set_uint64(v_reuseFailAlloc_3738_, sizeof(void*)*1, v_tid_3714_);
v___x_3729_ = v_reuseFailAlloc_3738_;
goto v_reusejp_3728_;
}
v_reusejp_3728_:
{
lean_object* v___x_3731_; 
if (v_isShared_3713_ == 0)
{
lean_ctor_set(v___x_3712_, 4, v___x_3729_);
v___x_3731_ = v___x_3712_;
goto v_reusejp_3730_;
}
else
{
lean_object* v_reuseFailAlloc_3737_; 
v_reuseFailAlloc_3737_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3737_, 0, v_env_3703_);
lean_ctor_set(v_reuseFailAlloc_3737_, 1, v_nextMacroScope_3704_);
lean_ctor_set(v_reuseFailAlloc_3737_, 2, v_ngen_3705_);
lean_ctor_set(v_reuseFailAlloc_3737_, 3, v_auxDeclNGen_3706_);
lean_ctor_set(v_reuseFailAlloc_3737_, 4, v___x_3729_);
lean_ctor_set(v_reuseFailAlloc_3737_, 5, v_cache_3707_);
lean_ctor_set(v_reuseFailAlloc_3737_, 6, v_messages_3708_);
lean_ctor_set(v_reuseFailAlloc_3737_, 7, v_infoState_3709_);
lean_ctor_set(v_reuseFailAlloc_3737_, 8, v_snapshotTasks_3710_);
v___x_3731_ = v_reuseFailAlloc_3737_;
goto v_reusejp_3730_;
}
v_reusejp_3730_:
{
lean_object* v___x_3732_; lean_object* v___x_3733_; lean_object* v___x_3735_; 
v___x_3732_ = lean_st_ref_set(v___y_3693_, v___x_3731_);
v___x_3733_ = lean_box(0);
if (v_isShared_3700_ == 0)
{
lean_ctor_set(v___x_3699_, 0, v___x_3733_);
v___x_3735_ = v___x_3699_;
goto v_reusejp_3734_;
}
else
{
lean_object* v_reuseFailAlloc_3736_; 
v_reuseFailAlloc_3736_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3736_, 0, v___x_3733_);
v___x_3735_ = v_reuseFailAlloc_3736_;
goto v_reusejp_3734_;
}
v_reusejp_3734_:
{
return v___x_3735_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__6___boxed(lean_object* v_cls_3742_, lean_object* v_msg_3743_, lean_object* v___y_3744_, lean_object* v___y_3745_, lean_object* v___y_3746_){
_start:
{
lean_object* v_res_3747_; 
v_res_3747_ = l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__6(v_cls_3742_, v_msg_3743_, v___y_3744_, v___y_3745_);
lean_dec(v___y_3745_);
lean_dec_ref(v___y_3744_);
return v_res_3747_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__4(size_t v_sz_3748_, size_t v_i_3749_, lean_object* v_bs_3750_){
_start:
{
uint8_t v___x_3751_; 
v___x_3751_ = lean_usize_dec_lt(v_i_3749_, v_sz_3748_);
if (v___x_3751_ == 0)
{
return v_bs_3750_;
}
else
{
lean_object* v_v_3752_; lean_object* v___x_3753_; lean_object* v_bs_x27_3754_; lean_object* v___x_3755_; lean_object* v___x_3756_; size_t v___x_3757_; size_t v___x_3758_; lean_object* v___x_3759_; 
v_v_3752_ = lean_array_uget(v_bs_3750_, v_i_3749_);
v___x_3753_ = lean_unsigned_to_nat(0u);
v_bs_x27_3754_ = lean_array_uset(v_bs_3750_, v_i_3749_, v___x_3753_);
v___x_3755_ = l_Lean_LocalDecl_fvarId(v_v_3752_);
lean_dec(v_v_3752_);
v___x_3756_ = l_Lean_mkFVar(v___x_3755_);
v___x_3757_ = ((size_t)1ULL);
v___x_3758_ = lean_usize_add(v_i_3749_, v___x_3757_);
v___x_3759_ = lean_array_uset(v_bs_x27_3754_, v_i_3749_, v___x_3756_);
v_i_3749_ = v___x_3758_;
v_bs_3750_ = v___x_3759_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__4___boxed(lean_object* v_sz_3761_, lean_object* v_i_3762_, lean_object* v_bs_3763_){
_start:
{
size_t v_sz_boxed_3764_; size_t v_i_boxed_3765_; lean_object* v_res_3766_; 
v_sz_boxed_3764_ = lean_unbox_usize(v_sz_3761_);
lean_dec(v_sz_3761_);
v_i_boxed_3765_ = lean_unbox_usize(v_i_3762_);
lean_dec(v_i_3762_);
v_res_3766_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__4(v_sz_boxed_3764_, v_i_boxed_3765_, v_bs_3763_);
return v_res_3766_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__3(lean_object* v___x_3767_, lean_object* v_as_3768_, size_t v_sz_3769_, size_t v_i_3770_, lean_object* v_b_3771_, lean_object* v___y_3772_, lean_object* v___y_3773_, lean_object* v___y_3774_){
_start:
{
uint8_t v___x_3776_; 
v___x_3776_ = lean_usize_dec_lt(v_i_3770_, v_sz_3769_);
if (v___x_3776_ == 0)
{
lean_object* v___x_3777_; lean_object* v___x_3778_; 
lean_dec_ref(v___x_3767_);
v___x_3777_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3777_, 0, v_b_3771_);
lean_ctor_set(v___x_3777_, 1, v___y_3772_);
v___x_3778_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3778_, 0, v___x_3777_);
return v___x_3778_;
}
else
{
lean_object* v_a_3779_; lean_object* v___x_3780_; lean_object* v___x_3781_; 
v_a_3779_ = lean_array_uget_borrowed(v_as_3768_, v_i_3770_);
v___x_3780_ = l_Lean_LocalDecl_fvarId(v_a_3779_);
lean_inc_ref(v___x_3767_);
v___x_3781_ = l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit(v___x_3767_, v___x_3780_, v___y_3772_, v___y_3773_, v___y_3774_);
lean_dec(v___x_3780_);
if (lean_obj_tag(v___x_3781_) == 0)
{
lean_object* v_a_3782_; lean_object* v_snd_3783_; lean_object* v___x_3784_; size_t v___x_3785_; size_t v___x_3786_; 
v_a_3782_ = lean_ctor_get(v___x_3781_, 0);
lean_inc(v_a_3782_);
lean_dec_ref_known(v___x_3781_, 1);
v_snd_3783_ = lean_ctor_get(v_a_3782_, 1);
lean_inc(v_snd_3783_);
lean_dec(v_a_3782_);
v___x_3784_ = lean_box(0);
v___x_3785_ = ((size_t)1ULL);
v___x_3786_ = lean_usize_add(v_i_3770_, v___x_3785_);
v_i_3770_ = v___x_3786_;
v_b_3771_ = v___x_3784_;
v___y_3772_ = v_snd_3783_;
goto _start;
}
else
{
lean_dec_ref(v___x_3767_);
return v___x_3781_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__3___boxed(lean_object* v___x_3788_, lean_object* v_as_3789_, lean_object* v_sz_3790_, lean_object* v_i_3791_, lean_object* v_b_3792_, lean_object* v___y_3793_, lean_object* v___y_3794_, lean_object* v___y_3795_, lean_object* v___y_3796_){
_start:
{
size_t v_sz_boxed_3797_; size_t v_i_boxed_3798_; lean_object* v_res_3799_; 
v_sz_boxed_3797_ = lean_unbox_usize(v_sz_3790_);
lean_dec(v_sz_3790_);
v_i_boxed_3798_ = lean_unbox_usize(v_i_3791_);
lean_dec(v_i_3791_);
v_res_3799_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__3(v___x_3788_, v_as_3789_, v_sz_boxed_3797_, v_i_boxed_3798_, v_b_3792_, v___y_3793_, v___y_3794_, v___y_3795_);
lean_dec(v___y_3795_);
lean_dec_ref(v___y_3794_);
lean_dec_ref(v_as_3789_);
return v_res_3799_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__5(lean_object* v_a_3800_, lean_object* v_a_3801_){
_start:
{
if (lean_obj_tag(v_a_3800_) == 0)
{
lean_object* v___x_3802_; 
v___x_3802_ = l_List_reverse___redArg(v_a_3801_);
return v___x_3802_;
}
else
{
lean_object* v_head_3803_; lean_object* v_tail_3804_; lean_object* v___x_3806_; uint8_t v_isShared_3807_; uint8_t v_isSharedCheck_3813_; 
v_head_3803_ = lean_ctor_get(v_a_3800_, 0);
v_tail_3804_ = lean_ctor_get(v_a_3800_, 1);
v_isSharedCheck_3813_ = !lean_is_exclusive(v_a_3800_);
if (v_isSharedCheck_3813_ == 0)
{
v___x_3806_ = v_a_3800_;
v_isShared_3807_ = v_isSharedCheck_3813_;
goto v_resetjp_3805_;
}
else
{
lean_inc(v_tail_3804_);
lean_inc(v_head_3803_);
lean_dec(v_a_3800_);
v___x_3806_ = lean_box(0);
v_isShared_3807_ = v_isSharedCheck_3813_;
goto v_resetjp_3805_;
}
v_resetjp_3805_:
{
lean_object* v___x_3808_; lean_object* v___x_3810_; 
v___x_3808_ = l_Lean_MessageData_ofExpr(v_head_3803_);
if (v_isShared_3807_ == 0)
{
lean_ctor_set(v___x_3806_, 1, v_a_3801_);
lean_ctor_set(v___x_3806_, 0, v___x_3808_);
v___x_3810_ = v___x_3806_;
goto v_reusejp_3809_;
}
else
{
lean_object* v_reuseFailAlloc_3812_; 
v_reuseFailAlloc_3812_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3812_, 0, v___x_3808_);
lean_ctor_set(v_reuseFailAlloc_3812_, 1, v_a_3801_);
v___x_3810_ = v_reuseFailAlloc_3812_;
goto v_reusejp_3809_;
}
v_reusejp_3809_:
{
v_a_3800_ = v_tail_3804_;
v_a_3801_ = v___x_3810_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__1_spec__1___redArg(lean_object* v_a_3814_, lean_object* v_b_3815_, lean_object* v_x_3816_){
_start:
{
if (lean_obj_tag(v_x_3816_) == 0)
{
lean_dec(v_b_3815_);
lean_dec(v_a_3814_);
return v_x_3816_;
}
else
{
lean_object* v_key_3817_; lean_object* v_value_3818_; lean_object* v_tail_3819_; lean_object* v___x_3821_; uint8_t v_isShared_3822_; uint8_t v_isSharedCheck_3831_; 
v_key_3817_ = lean_ctor_get(v_x_3816_, 0);
v_value_3818_ = lean_ctor_get(v_x_3816_, 1);
v_tail_3819_ = lean_ctor_get(v_x_3816_, 2);
v_isSharedCheck_3831_ = !lean_is_exclusive(v_x_3816_);
if (v_isSharedCheck_3831_ == 0)
{
v___x_3821_ = v_x_3816_;
v_isShared_3822_ = v_isSharedCheck_3831_;
goto v_resetjp_3820_;
}
else
{
lean_inc(v_tail_3819_);
lean_inc(v_value_3818_);
lean_inc(v_key_3817_);
lean_dec(v_x_3816_);
v___x_3821_ = lean_box(0);
v_isShared_3822_ = v_isSharedCheck_3831_;
goto v_resetjp_3820_;
}
v_resetjp_3820_:
{
uint8_t v___x_3823_; 
v___x_3823_ = l_Lean_instBEqFVarId_beq(v_key_3817_, v_a_3814_);
if (v___x_3823_ == 0)
{
lean_object* v___x_3824_; lean_object* v___x_3826_; 
v___x_3824_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__1_spec__1___redArg(v_a_3814_, v_b_3815_, v_tail_3819_);
if (v_isShared_3822_ == 0)
{
lean_ctor_set(v___x_3821_, 2, v___x_3824_);
v___x_3826_ = v___x_3821_;
goto v_reusejp_3825_;
}
else
{
lean_object* v_reuseFailAlloc_3827_; 
v_reuseFailAlloc_3827_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3827_, 0, v_key_3817_);
lean_ctor_set(v_reuseFailAlloc_3827_, 1, v_value_3818_);
lean_ctor_set(v_reuseFailAlloc_3827_, 2, v___x_3824_);
v___x_3826_ = v_reuseFailAlloc_3827_;
goto v_reusejp_3825_;
}
v_reusejp_3825_:
{
return v___x_3826_;
}
}
else
{
lean_object* v___x_3829_; 
lean_dec(v_value_3818_);
lean_dec(v_key_3817_);
if (v_isShared_3822_ == 0)
{
lean_ctor_set(v___x_3821_, 1, v_b_3815_);
lean_ctor_set(v___x_3821_, 0, v_a_3814_);
v___x_3829_ = v___x_3821_;
goto v_reusejp_3828_;
}
else
{
lean_object* v_reuseFailAlloc_3830_; 
v_reuseFailAlloc_3830_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3830_, 0, v_a_3814_);
lean_ctor_set(v_reuseFailAlloc_3830_, 1, v_b_3815_);
lean_ctor_set(v_reuseFailAlloc_3830_, 2, v_tail_3819_);
v___x_3829_ = v_reuseFailAlloc_3830_;
goto v_reusejp_3828_;
}
v_reusejp_3828_:
{
return v___x_3829_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__1___redArg(lean_object* v_m_3832_, lean_object* v_a_3833_, lean_object* v_b_3834_){
_start:
{
lean_object* v_size_3835_; lean_object* v_buckets_3836_; lean_object* v___x_3838_; uint8_t v_isShared_3839_; uint8_t v_isSharedCheck_3879_; 
v_size_3835_ = lean_ctor_get(v_m_3832_, 0);
v_buckets_3836_ = lean_ctor_get(v_m_3832_, 1);
v_isSharedCheck_3879_ = !lean_is_exclusive(v_m_3832_);
if (v_isSharedCheck_3879_ == 0)
{
v___x_3838_ = v_m_3832_;
v_isShared_3839_ = v_isSharedCheck_3879_;
goto v_resetjp_3837_;
}
else
{
lean_inc(v_buckets_3836_);
lean_inc(v_size_3835_);
lean_dec(v_m_3832_);
v___x_3838_ = lean_box(0);
v_isShared_3839_ = v_isSharedCheck_3879_;
goto v_resetjp_3837_;
}
v_resetjp_3837_:
{
lean_object* v___x_3840_; uint64_t v___x_3841_; uint64_t v___x_3842_; uint64_t v___x_3843_; uint64_t v_fold_3844_; uint64_t v___x_3845_; uint64_t v___x_3846_; uint64_t v___x_3847_; size_t v___x_3848_; size_t v___x_3849_; size_t v___x_3850_; size_t v___x_3851_; size_t v___x_3852_; lean_object* v_bkt_3853_; uint8_t v___x_3854_; 
v___x_3840_ = lean_array_get_size(v_buckets_3836_);
v___x_3841_ = l_Lean_instHashableFVarId_hash(v_a_3833_);
v___x_3842_ = 32ULL;
v___x_3843_ = lean_uint64_shift_right(v___x_3841_, v___x_3842_);
v_fold_3844_ = lean_uint64_xor(v___x_3841_, v___x_3843_);
v___x_3845_ = 16ULL;
v___x_3846_ = lean_uint64_shift_right(v_fold_3844_, v___x_3845_);
v___x_3847_ = lean_uint64_xor(v_fold_3844_, v___x_3846_);
v___x_3848_ = lean_uint64_to_usize(v___x_3847_);
v___x_3849_ = lean_usize_of_nat(v___x_3840_);
v___x_3850_ = ((size_t)1ULL);
v___x_3851_ = lean_usize_sub(v___x_3849_, v___x_3850_);
v___x_3852_ = lean_usize_land(v___x_3848_, v___x_3851_);
v_bkt_3853_ = lean_array_uget_borrowed(v_buckets_3836_, v___x_3852_);
v___x_3854_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1_spec__2___redArg(v_a_3833_, v_bkt_3853_);
if (v___x_3854_ == 0)
{
lean_object* v___x_3855_; lean_object* v_size_x27_3856_; lean_object* v___x_3857_; lean_object* v_buckets_x27_3858_; lean_object* v___x_3859_; lean_object* v___x_3860_; lean_object* v___x_3861_; lean_object* v___x_3862_; lean_object* v___x_3863_; uint8_t v___x_3864_; 
v___x_3855_ = lean_unsigned_to_nat(1u);
v_size_x27_3856_ = lean_nat_add(v_size_3835_, v___x_3855_);
lean_dec(v_size_3835_);
lean_inc(v_bkt_3853_);
v___x_3857_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3857_, 0, v_a_3833_);
lean_ctor_set(v___x_3857_, 1, v_b_3834_);
lean_ctor_set(v___x_3857_, 2, v_bkt_3853_);
v_buckets_x27_3858_ = lean_array_uset(v_buckets_3836_, v___x_3852_, v___x_3857_);
v___x_3859_ = lean_unsigned_to_nat(4u);
v___x_3860_ = lean_nat_mul(v_size_x27_3856_, v___x_3859_);
v___x_3861_ = lean_unsigned_to_nat(3u);
v___x_3862_ = lean_nat_div(v___x_3860_, v___x_3861_);
lean_dec(v___x_3860_);
v___x_3863_ = lean_array_get_size(v_buckets_x27_3858_);
v___x_3864_ = lean_nat_dec_le(v___x_3862_, v___x_3863_);
lean_dec(v___x_3862_);
if (v___x_3864_ == 0)
{
lean_object* v_val_3865_; lean_object* v___x_3867_; 
v_val_3865_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__5___redArg(v_buckets_x27_3858_);
if (v_isShared_3839_ == 0)
{
lean_ctor_set(v___x_3838_, 1, v_val_3865_);
lean_ctor_set(v___x_3838_, 0, v_size_x27_3856_);
v___x_3867_ = v___x_3838_;
goto v_reusejp_3866_;
}
else
{
lean_object* v_reuseFailAlloc_3868_; 
v_reuseFailAlloc_3868_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3868_, 0, v_size_x27_3856_);
lean_ctor_set(v_reuseFailAlloc_3868_, 1, v_val_3865_);
v___x_3867_ = v_reuseFailAlloc_3868_;
goto v_reusejp_3866_;
}
v_reusejp_3866_:
{
return v___x_3867_;
}
}
else
{
lean_object* v___x_3870_; 
if (v_isShared_3839_ == 0)
{
lean_ctor_set(v___x_3838_, 1, v_buckets_x27_3858_);
lean_ctor_set(v___x_3838_, 0, v_size_x27_3856_);
v___x_3870_ = v___x_3838_;
goto v_reusejp_3869_;
}
else
{
lean_object* v_reuseFailAlloc_3871_; 
v_reuseFailAlloc_3871_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3871_, 0, v_size_x27_3856_);
lean_ctor_set(v_reuseFailAlloc_3871_, 1, v_buckets_x27_3858_);
v___x_3870_ = v_reuseFailAlloc_3871_;
goto v_reusejp_3869_;
}
v_reusejp_3869_:
{
return v___x_3870_;
}
}
}
else
{
lean_object* v___x_3872_; lean_object* v_buckets_x27_3873_; lean_object* v___x_3874_; lean_object* v___x_3875_; lean_object* v___x_3877_; 
lean_inc(v_bkt_3853_);
v___x_3872_ = lean_box(0);
v_buckets_x27_3873_ = lean_array_uset(v_buckets_3836_, v___x_3852_, v___x_3872_);
v___x_3874_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__1_spec__1___redArg(v_a_3833_, v_b_3834_, v_bkt_3853_);
v___x_3875_ = lean_array_uset(v_buckets_x27_3873_, v___x_3852_, v___x_3874_);
if (v_isShared_3839_ == 0)
{
lean_ctor_set(v___x_3838_, 1, v___x_3875_);
v___x_3877_ = v___x_3838_;
goto v_reusejp_3876_;
}
else
{
lean_object* v_reuseFailAlloc_3878_; 
v_reuseFailAlloc_3878_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3878_, 0, v_size_3835_);
lean_ctor_set(v_reuseFailAlloc_3878_, 1, v___x_3875_);
v___x_3877_ = v_reuseFailAlloc_3878_;
goto v_reusejp_3876_;
}
v_reusejp_3876_:
{
return v___x_3877_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__2___redArg(lean_object* v_as_3880_, size_t v_sz_3881_, size_t v_i_3882_, lean_object* v_b_3883_){
_start:
{
uint8_t v___x_3885_; 
v___x_3885_ = lean_usize_dec_lt(v_i_3882_, v_sz_3881_);
if (v___x_3885_ == 0)
{
lean_object* v___x_3886_; 
v___x_3886_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3886_, 0, v_b_3883_);
return v___x_3886_;
}
else
{
lean_object* v_snd_3887_; lean_object* v_fst_3888_; lean_object* v___x_3890_; uint8_t v_isShared_3891_; uint8_t v_isSharedCheck_3923_; 
v_snd_3887_ = lean_ctor_get(v_b_3883_, 1);
v_fst_3888_ = lean_ctor_get(v_b_3883_, 0);
v_isSharedCheck_3923_ = !lean_is_exclusive(v_b_3883_);
if (v_isSharedCheck_3923_ == 0)
{
v___x_3890_ = v_b_3883_;
v_isShared_3891_ = v_isSharedCheck_3923_;
goto v_resetjp_3889_;
}
else
{
lean_inc(v_snd_3887_);
lean_inc(v_fst_3888_);
lean_dec(v_b_3883_);
v___x_3890_ = lean_box(0);
v_isShared_3891_ = v_isSharedCheck_3923_;
goto v_resetjp_3889_;
}
v_resetjp_3889_:
{
lean_object* v_array_3892_; lean_object* v_start_3893_; lean_object* v_stop_3894_; uint8_t v___x_3895_; 
v_array_3892_ = lean_ctor_get(v_snd_3887_, 0);
v_start_3893_ = lean_ctor_get(v_snd_3887_, 1);
v_stop_3894_ = lean_ctor_get(v_snd_3887_, 2);
v___x_3895_ = lean_nat_dec_lt(v_start_3893_, v_stop_3894_);
if (v___x_3895_ == 0)
{
lean_object* v___x_3897_; 
if (v_isShared_3891_ == 0)
{
v___x_3897_ = v___x_3890_;
goto v_reusejp_3896_;
}
else
{
lean_object* v_reuseFailAlloc_3899_; 
v_reuseFailAlloc_3899_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3899_, 0, v_fst_3888_);
lean_ctor_set(v_reuseFailAlloc_3899_, 1, v_snd_3887_);
v___x_3897_ = v_reuseFailAlloc_3899_;
goto v_reusejp_3896_;
}
v_reusejp_3896_:
{
lean_object* v___x_3898_; 
v___x_3898_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3898_, 0, v___x_3897_);
return v___x_3898_;
}
}
else
{
lean_object* v___x_3901_; uint8_t v_isShared_3902_; uint8_t v_isSharedCheck_3919_; 
lean_inc(v_stop_3894_);
lean_inc(v_start_3893_);
lean_inc_ref(v_array_3892_);
v_isSharedCheck_3919_ = !lean_is_exclusive(v_snd_3887_);
if (v_isSharedCheck_3919_ == 0)
{
lean_object* v_unused_3920_; lean_object* v_unused_3921_; lean_object* v_unused_3922_; 
v_unused_3920_ = lean_ctor_get(v_snd_3887_, 2);
lean_dec(v_unused_3920_);
v_unused_3921_ = lean_ctor_get(v_snd_3887_, 1);
lean_dec(v_unused_3921_);
v_unused_3922_ = lean_ctor_get(v_snd_3887_, 0);
lean_dec(v_unused_3922_);
v___x_3901_ = v_snd_3887_;
v_isShared_3902_ = v_isSharedCheck_3919_;
goto v_resetjp_3900_;
}
else
{
lean_dec(v_snd_3887_);
v___x_3901_ = lean_box(0);
v_isShared_3902_ = v_isSharedCheck_3919_;
goto v_resetjp_3900_;
}
v_resetjp_3900_:
{
lean_object* v_a_3903_; lean_object* v___x_3904_; lean_object* v___x_3905_; lean_object* v___x_3906_; lean_object* v___x_3908_; 
v_a_3903_ = lean_array_uget_borrowed(v_as_3880_, v_i_3882_);
v___x_3904_ = lean_array_fget(v_array_3892_, v_start_3893_);
v___x_3905_ = lean_unsigned_to_nat(1u);
v___x_3906_ = lean_nat_add(v_start_3893_, v___x_3905_);
lean_dec(v_start_3893_);
if (v_isShared_3902_ == 0)
{
lean_ctor_set(v___x_3901_, 1, v___x_3906_);
v___x_3908_ = v___x_3901_;
goto v_reusejp_3907_;
}
else
{
lean_object* v_reuseFailAlloc_3918_; 
v_reuseFailAlloc_3918_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3918_, 0, v_array_3892_);
lean_ctor_set(v_reuseFailAlloc_3918_, 1, v___x_3906_);
lean_ctor_set(v_reuseFailAlloc_3918_, 2, v_stop_3894_);
v___x_3908_ = v_reuseFailAlloc_3918_;
goto v_reusejp_3907_;
}
v_reusejp_3907_:
{
lean_object* v___x_3909_; lean_object* v___x_3911_; 
v___x_3909_ = l_Lean_LocalDecl_fvarId(v_a_3903_);
lean_inc(v_a_3903_);
if (v_isShared_3891_ == 0)
{
lean_ctor_set(v___x_3890_, 1, v___x_3904_);
lean_ctor_set(v___x_3890_, 0, v_a_3903_);
v___x_3911_ = v___x_3890_;
goto v_reusejp_3910_;
}
else
{
lean_object* v_reuseFailAlloc_3917_; 
v_reuseFailAlloc_3917_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3917_, 0, v_a_3903_);
lean_ctor_set(v_reuseFailAlloc_3917_, 1, v___x_3904_);
v___x_3911_ = v_reuseFailAlloc_3917_;
goto v_reusejp_3910_;
}
v_reusejp_3910_:
{
lean_object* v___x_3912_; lean_object* v___x_3913_; size_t v___x_3914_; size_t v___x_3915_; 
v___x_3912_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__1___redArg(v_fst_3888_, v___x_3909_, v___x_3911_);
v___x_3913_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3913_, 0, v___x_3912_);
lean_ctor_set(v___x_3913_, 1, v___x_3908_);
v___x_3914_ = ((size_t)1ULL);
v___x_3915_ = lean_usize_add(v_i_3882_, v___x_3914_);
v_i_3882_ = v___x_3915_;
v_b_3883_ = v___x_3913_;
goto _start;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__2___redArg___boxed(lean_object* v_as_3924_, lean_object* v_sz_3925_, lean_object* v_i_3926_, lean_object* v_b_3927_, lean_object* v___y_3928_){
_start:
{
size_t v_sz_boxed_3929_; size_t v_i_boxed_3930_; lean_object* v_res_3931_; 
v_sz_boxed_3929_ = lean_unbox_usize(v_sz_3925_);
lean_dec(v_sz_3925_);
v_i_boxed_3930_ = lean_unbox_usize(v_i_3926_);
lean_dec(v_i_3926_);
v_res_3931_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__2___redArg(v_as_3924_, v_sz_boxed_3929_, v_i_boxed_3930_, v_b_3927_);
lean_dec_ref(v_as_3924_);
return v_res_3931_;
}
}
static lean_object* _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__2(void){
_start:
{
lean_object* v___x_3934_; lean_object* v___x_3935_; lean_object* v___x_3936_; lean_object* v___x_3937_; lean_object* v___x_3938_; lean_object* v___x_3939_; 
v___x_3934_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__1));
v___x_3935_ = lean_unsigned_to_nat(2u);
v___x_3936_ = lean_unsigned_to_nat(366u);
v___x_3937_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__0));
v___x_3938_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__0));
v___x_3939_ = l_mkPanicMessageWithDecl(v___x_3938_, v___x_3937_, v___x_3936_, v___x_3935_, v___x_3934_);
return v___x_3939_;
}
}
static lean_object* _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__4(void){
_start:
{
lean_object* v___x_3941_; lean_object* v___x_3942_; lean_object* v___x_3943_; lean_object* v___x_3944_; lean_object* v___x_3945_; lean_object* v___x_3946_; 
v___x_3941_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__3));
v___x_3942_ = lean_unsigned_to_nat(2u);
v___x_3943_ = lean_unsigned_to_nat(367u);
v___x_3944_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__0));
v___x_3945_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__0));
v___x_3946_ = l_mkPanicMessageWithDecl(v___x_3945_, v___x_3944_, v___x_3943_, v___x_3942_, v___x_3941_);
return v___x_3946_;
}
}
static lean_object* _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__5(void){
_start:
{
lean_object* v___x_3947_; lean_object* v___x_3948_; lean_object* v___x_3949_; 
v___x_3947_ = lean_box(0);
v___x_3948_ = lean_unsigned_to_nat(16u);
v___x_3949_ = lean_mk_array(v___x_3948_, v___x_3947_);
return v___x_3949_;
}
}
static lean_object* _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__6(void){
_start:
{
lean_object* v___x_3950_; lean_object* v___x_3951_; lean_object* v___x_3952_; 
v___x_3950_ = lean_obj_once(&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__5, &l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__5_once, _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__5);
v___x_3951_ = lean_unsigned_to_nat(0u);
v___x_3952_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3952_, 0, v___x_3951_);
lean_ctor_set(v___x_3952_, 1, v___x_3950_);
return v___x_3952_;
}
}
static lean_object* _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__8(void){
_start:
{
lean_object* v___x_3954_; lean_object* v___x_3955_; 
v___x_3954_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__7));
v___x_3955_ = l_Lean_stringToMessageData(v___x_3954_);
return v___x_3955_;
}
}
static lean_object* _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__10(void){
_start:
{
lean_object* v___x_3957_; lean_object* v___x_3958_; 
v___x_3957_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__9));
v___x_3958_ = l_Lean_stringToMessageData(v___x_3957_);
return v___x_3958_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls(lean_object* v_sortedDecls_3959_, lean_object* v_sortedArgs_3960_, lean_object* v_toSortDecls_3961_, lean_object* v_toSortArgs_3962_, lean_object* v_a_3963_, lean_object* v_a_3964_){
_start:
{
lean_object* v___y_3967_; lean_object* v___y_3986_; lean_object* v___y_3987_; lean_object* v___y_3988_; lean_object* v___y_3989_; lean_object* v_snd_3990_; lean_object* v___x_3992_; lean_object* v___x_3993_; uint8_t v___x_3994_; 
v___x_3992_ = lean_array_get_size(v_sortedDecls_3959_);
v___x_3993_ = lean_array_get_size(v_sortedArgs_3960_);
v___x_3994_ = lean_nat_dec_eq(v___x_3992_, v___x_3993_);
if (v___x_3994_ == 0)
{
lean_object* v___x_3995_; lean_object* v___x_3996_; 
lean_dec_ref(v_toSortArgs_3962_);
lean_dec_ref(v_sortedArgs_3960_);
lean_dec_ref(v_sortedDecls_3959_);
v___x_3995_ = lean_obj_once(&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__2, &l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__2_once, _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__2);
v___x_3996_ = l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__0(v___x_3995_, v_a_3963_, v_a_3964_);
return v___x_3996_;
}
else
{
lean_object* v___x_3997_; lean_object* v___x_3998_; uint8_t v___x_3999_; 
v___x_3997_ = lean_array_get_size(v_toSortDecls_3961_);
v___x_3998_ = lean_array_get_size(v_toSortArgs_3962_);
v___x_3999_ = lean_nat_dec_eq(v___x_3997_, v___x_3998_);
if (v___x_3999_ == 0)
{
lean_object* v___x_4000_; lean_object* v___x_4001_; 
lean_dec_ref(v_toSortArgs_3962_);
lean_dec_ref(v_sortedArgs_3960_);
lean_dec_ref(v_sortedDecls_3959_);
v___x_4000_ = lean_obj_once(&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__4, &l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__4_once, _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__4);
v___x_4001_ = l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__0(v___x_4000_, v_a_3963_, v_a_3964_);
return v___x_4001_;
}
else
{
lean_object* v___x_4002_; uint8_t v___x_4003_; 
v___x_4002_ = lean_unsigned_to_nat(0u);
v___x_4003_ = lean_nat_dec_eq(v___x_3997_, v___x_4002_);
if (v___x_4003_ == 0)
{
lean_object* v_options_4004_; lean_object* v_inheritedTraceOptions_4005_; uint8_t v_hasTrace_4006_; lean_object* v_cls_4007_; lean_object* v___y_4009_; lean_object* v___y_4010_; 
v_options_4004_ = lean_ctor_get(v_a_3963_, 2);
v_inheritedTraceOptions_4005_ = lean_ctor_get(v_a_3963_, 13);
v_hasTrace_4006_ = lean_ctor_get_uint8(v_options_4004_, sizeof(void*)*1);
v_cls_4007_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__10));
if (v_hasTrace_4006_ == 0)
{
v___y_4009_ = v_a_3963_;
v___y_4010_ = v_a_3964_;
goto v___jp_4008_;
}
else
{
lean_object* v___x_4111_; uint8_t v___x_4112_; 
v___x_4111_ = lean_obj_once(&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__13, &l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__13_once, _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__13);
v___x_4112_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4005_, v_options_4004_, v___x_4111_);
if (v___x_4112_ == 0)
{
v___y_4009_ = v_a_3963_;
v___y_4010_ = v_a_3964_;
goto v___jp_4008_;
}
else
{
lean_object* v___x_4113_; lean_object* v___x_4114_; 
v___x_4113_ = lean_obj_once(&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__10, &l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__10_once, _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__10);
v___x_4114_ = l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__6(v_cls_4007_, v___x_4113_, v_a_3963_, v_a_3964_);
if (lean_obj_tag(v___x_4114_) == 0)
{
lean_dec_ref_known(v___x_4114_, 1);
v___y_4009_ = v_a_3963_;
v___y_4010_ = v_a_3964_;
goto v___jp_4008_;
}
else
{
lean_object* v_a_4115_; lean_object* v___x_4117_; uint8_t v_isShared_4118_; uint8_t v_isSharedCheck_4122_; 
lean_dec_ref(v_toSortArgs_3962_);
lean_dec_ref(v_sortedArgs_3960_);
lean_dec_ref(v_sortedDecls_3959_);
v_a_4115_ = lean_ctor_get(v___x_4114_, 0);
v_isSharedCheck_4122_ = !lean_is_exclusive(v___x_4114_);
if (v_isSharedCheck_4122_ == 0)
{
v___x_4117_ = v___x_4114_;
v_isShared_4118_ = v_isSharedCheck_4122_;
goto v_resetjp_4116_;
}
else
{
lean_inc(v_a_4115_);
lean_dec(v___x_4114_);
v___x_4117_ = lean_box(0);
v_isShared_4118_ = v_isSharedCheck_4122_;
goto v_resetjp_4116_;
}
v_resetjp_4116_:
{
lean_object* v___x_4120_; 
if (v_isShared_4118_ == 0)
{
v___x_4120_ = v___x_4117_;
goto v_reusejp_4119_;
}
else
{
lean_object* v_reuseFailAlloc_4121_; 
v_reuseFailAlloc_4121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4121_, 0, v_a_4115_);
v___x_4120_ = v_reuseFailAlloc_4121_;
goto v_reusejp_4119_;
}
v_reusejp_4119_:
{
return v___x_4120_;
}
}
}
}
}
v___jp_4008_:
{
lean_object* v___x_4011_; lean_object* v___x_4012_; lean_object* v___x_4013_; size_t v_sz_4014_; size_t v___x_4015_; lean_object* v___x_4016_; 
v___x_4011_ = lean_obj_once(&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__6, &l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__6_once, _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__6);
v___x_4012_ = l_Array_toSubarray___redArg(v_sortedArgs_3960_, v___x_4002_, v___x_3993_);
v___x_4013_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4013_, 0, v___x_4011_);
lean_ctor_set(v___x_4013_, 1, v___x_4012_);
v_sz_4014_ = lean_array_size(v_sortedDecls_3959_);
v___x_4015_ = ((size_t)0ULL);
v___x_4016_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__2___redArg(v_sortedDecls_3959_, v_sz_4014_, v___x_4015_, v___x_4013_);
if (lean_obj_tag(v___x_4016_) == 0)
{
lean_object* v_a_4017_; lean_object* v_fst_4018_; lean_object* v___x_4020_; uint8_t v_isShared_4021_; uint8_t v_isSharedCheck_4101_; 
v_a_4017_ = lean_ctor_get(v___x_4016_, 0);
lean_inc(v_a_4017_);
lean_dec_ref_known(v___x_4016_, 1);
v_fst_4018_ = lean_ctor_get(v_a_4017_, 0);
v_isSharedCheck_4101_ = !lean_is_exclusive(v_a_4017_);
if (v_isSharedCheck_4101_ == 0)
{
lean_object* v_unused_4102_; 
v_unused_4102_ = lean_ctor_get(v_a_4017_, 1);
lean_dec(v_unused_4102_);
v___x_4020_ = v_a_4017_;
v_isShared_4021_ = v_isSharedCheck_4101_;
goto v_resetjp_4019_;
}
else
{
lean_inc(v_fst_4018_);
lean_dec(v_a_4017_);
v___x_4020_ = lean_box(0);
v_isShared_4021_ = v_isSharedCheck_4101_;
goto v_resetjp_4019_;
}
v_resetjp_4019_:
{
lean_object* v___x_4022_; lean_object* v___x_4024_; 
v___x_4022_ = l_Array_toSubarray___redArg(v_toSortArgs_3962_, v___x_4002_, v___x_3998_);
if (v_isShared_4021_ == 0)
{
lean_ctor_set(v___x_4020_, 1, v___x_4022_);
v___x_4024_ = v___x_4020_;
goto v_reusejp_4023_;
}
else
{
lean_object* v_reuseFailAlloc_4100_; 
v_reuseFailAlloc_4100_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4100_, 0, v_fst_4018_);
lean_ctor_set(v_reuseFailAlloc_4100_, 1, v___x_4022_);
v___x_4024_ = v_reuseFailAlloc_4100_;
goto v_reusejp_4023_;
}
v_reusejp_4023_:
{
size_t v_sz_4025_; lean_object* v___x_4026_; 
v_sz_4025_ = lean_array_size(v_toSortDecls_3961_);
v___x_4026_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__2___redArg(v_toSortDecls_3961_, v_sz_4025_, v___x_4015_, v___x_4024_);
if (lean_obj_tag(v___x_4026_) == 0)
{
lean_object* v_a_4027_; lean_object* v_fst_4028_; lean_object* v_size_4029_; lean_object* v___x_4030_; lean_object* v___x_4031_; lean_object* v___x_4032_; lean_object* v___x_4033_; lean_object* v___x_4034_; 
v_a_4027_ = lean_ctor_get(v___x_4026_, 0);
lean_inc(v_a_4027_);
lean_dec_ref_known(v___x_4026_, 1);
v_fst_4028_ = lean_ctor_get(v_a_4027_, 0);
lean_inc_n(v_fst_4028_, 2);
lean_dec(v_a_4027_);
v_size_4029_ = lean_ctor_get(v_fst_4028_, 0);
v___x_4030_ = l_Lean_instEmptyCollectionFVarIdHashSet;
v___x_4031_ = lean_mk_empty_array_with_capacity(v_size_4029_);
lean_inc_ref(v___x_4031_);
v___x_4032_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4032_, 0, v___x_4030_);
lean_ctor_set(v___x_4032_, 1, v___x_4030_);
lean_ctor_set(v___x_4032_, 2, v___x_4031_);
lean_ctor_set(v___x_4032_, 3, v___x_4031_);
v___x_4033_ = lean_box(0);
v___x_4034_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__3(v_fst_4028_, v_sortedDecls_3959_, v_sz_4014_, v___x_4015_, v___x_4033_, v___x_4032_, v___y_4009_, v___y_4010_);
lean_dec_ref(v_sortedDecls_3959_);
if (lean_obj_tag(v___x_4034_) == 0)
{
lean_object* v_a_4035_; lean_object* v_snd_4036_; lean_object* v___x_4037_; 
v_a_4035_ = lean_ctor_get(v___x_4034_, 0);
lean_inc(v_a_4035_);
lean_dec_ref_known(v___x_4034_, 1);
v_snd_4036_ = lean_ctor_get(v_a_4035_, 1);
lean_inc(v_snd_4036_);
lean_dec(v_a_4035_);
v___x_4037_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__3(v_fst_4028_, v_toSortDecls_3961_, v_sz_4025_, v___x_4015_, v___x_4033_, v_snd_4036_, v___y_4009_, v___y_4010_);
if (lean_obj_tag(v___x_4037_) == 0)
{
lean_object* v_a_4038_; lean_object* v_snd_4039_; lean_object* v___x_4041_; uint8_t v_isShared_4042_; uint8_t v_isSharedCheck_4074_; 
v_a_4038_ = lean_ctor_get(v___x_4037_, 0);
lean_inc(v_a_4038_);
lean_dec_ref_known(v___x_4037_, 1);
v_snd_4039_ = lean_ctor_get(v_a_4038_, 1);
v_isSharedCheck_4074_ = !lean_is_exclusive(v_a_4038_);
if (v_isSharedCheck_4074_ == 0)
{
lean_object* v_unused_4075_; 
v_unused_4075_ = lean_ctor_get(v_a_4038_, 0);
lean_dec(v_unused_4075_);
v___x_4041_ = v_a_4038_;
v_isShared_4042_ = v_isSharedCheck_4074_;
goto v_resetjp_4040_;
}
else
{
lean_inc(v_snd_4039_);
lean_dec(v_a_4038_);
v___x_4041_ = lean_box(0);
v_isShared_4042_ = v_isSharedCheck_4074_;
goto v_resetjp_4040_;
}
v_resetjp_4040_:
{
lean_object* v_options_4043_; lean_object* v_newDecls_4044_; lean_object* v_newArgs_4045_; lean_object* v_inheritedTraceOptions_4046_; uint8_t v_hasTrace_4047_; lean_object* v___f_4048_; 
v_options_4043_ = lean_ctor_get(v___y_4009_, 2);
v_newDecls_4044_ = lean_ctor_get(v_snd_4039_, 2);
v_newArgs_4045_ = lean_ctor_get(v_snd_4039_, 3);
v_inheritedTraceOptions_4046_ = lean_ctor_get(v___y_4009_, 13);
v_hasTrace_4047_ = lean_ctor_get_uint8(v_options_4043_, sizeof(void*)*1);
lean_inc_ref(v_newArgs_4045_);
lean_inc_ref(v_newDecls_4044_);
v___f_4048_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___lam__0___boxed), 7, 2);
lean_closure_set(v___f_4048_, 0, v_newDecls_4044_);
lean_closure_set(v___f_4048_, 1, v_newArgs_4045_);
if (v_hasTrace_4047_ == 0)
{
lean_del_object(v___x_4041_);
v___y_3986_ = v___y_4009_;
v___y_3987_ = v___x_4033_;
v___y_3988_ = v___y_4010_;
v___y_3989_ = v___f_4048_;
v_snd_3990_ = v_snd_4039_;
goto v___jp_3985_;
}
else
{
lean_object* v___x_4049_; uint8_t v___x_4050_; 
v___x_4049_ = lean_obj_once(&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__13, &l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__13_once, _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__13);
v___x_4050_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4046_, v_options_4043_, v___x_4049_);
if (v___x_4050_ == 0)
{
lean_del_object(v___x_4041_);
v___y_3986_ = v___y_4009_;
v___y_3987_ = v___x_4033_;
v___y_3988_ = v___y_4010_;
v___y_3989_ = v___f_4048_;
v_snd_3990_ = v_snd_4039_;
goto v___jp_3985_;
}
else
{
lean_object* v___x_4051_; size_t v_sz_4052_; lean_object* v___x_4053_; lean_object* v___x_4054_; lean_object* v___x_4055_; lean_object* v___x_4056_; lean_object* v___x_4057_; lean_object* v___x_4059_; 
lean_inc_ref(v_newArgs_4045_);
lean_inc_ref_n(v_newDecls_4044_, 2);
lean_dec_ref(v___f_4048_);
v___x_4051_ = lean_obj_once(&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__8, &l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__8_once, _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__8);
v_sz_4052_ = lean_array_size(v_newDecls_4044_);
v___x_4053_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__4(v_sz_4052_, v___x_4015_, v_newDecls_4044_);
v___x_4054_ = lean_array_to_list(v___x_4053_);
v___x_4055_ = lean_box(0);
v___x_4056_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__5(v___x_4054_, v___x_4055_);
v___x_4057_ = l_Lean_MessageData_ofList(v___x_4056_);
if (v_isShared_4042_ == 0)
{
lean_ctor_set_tag(v___x_4041_, 7);
lean_ctor_set(v___x_4041_, 1, v___x_4057_);
lean_ctor_set(v___x_4041_, 0, v___x_4051_);
v___x_4059_ = v___x_4041_;
goto v_reusejp_4058_;
}
else
{
lean_object* v_reuseFailAlloc_4073_; 
v_reuseFailAlloc_4073_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4073_, 0, v___x_4051_);
lean_ctor_set(v_reuseFailAlloc_4073_, 1, v___x_4057_);
v___x_4059_ = v_reuseFailAlloc_4073_;
goto v_reusejp_4058_;
}
v_reusejp_4058_:
{
lean_object* v___x_4060_; 
v___x_4060_ = l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6(v_cls_4007_, v___x_4059_, v_snd_4039_, v___y_4009_, v___y_4010_);
if (lean_obj_tag(v___x_4060_) == 0)
{
lean_object* v_a_4061_; lean_object* v_fst_4062_; lean_object* v_snd_4063_; lean_object* v___x_4064_; 
v_a_4061_ = lean_ctor_get(v___x_4060_, 0);
lean_inc(v_a_4061_);
lean_dec_ref_known(v___x_4060_, 1);
v_fst_4062_ = lean_ctor_get(v_a_4061_, 0);
lean_inc(v_fst_4062_);
v_snd_4063_ = lean_ctor_get(v_a_4061_, 1);
lean_inc(v_snd_4063_);
lean_dec(v_a_4061_);
v___x_4064_ = l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___lam__0(v_newDecls_4044_, v_newArgs_4045_, v_fst_4062_, v_snd_4063_, v___y_4009_, v___y_4010_);
v___y_3967_ = v___x_4064_;
goto v___jp_3966_;
}
else
{
lean_object* v_a_4065_; lean_object* v___x_4067_; uint8_t v_isShared_4068_; uint8_t v_isSharedCheck_4072_; 
lean_dec_ref(v_newArgs_4045_);
lean_dec_ref(v_newDecls_4044_);
v_a_4065_ = lean_ctor_get(v___x_4060_, 0);
v_isSharedCheck_4072_ = !lean_is_exclusive(v___x_4060_);
if (v_isSharedCheck_4072_ == 0)
{
v___x_4067_ = v___x_4060_;
v_isShared_4068_ = v_isSharedCheck_4072_;
goto v_resetjp_4066_;
}
else
{
lean_inc(v_a_4065_);
lean_dec(v___x_4060_);
v___x_4067_ = lean_box(0);
v_isShared_4068_ = v_isSharedCheck_4072_;
goto v_resetjp_4066_;
}
v_resetjp_4066_:
{
lean_object* v___x_4070_; 
if (v_isShared_4068_ == 0)
{
v___x_4070_ = v___x_4067_;
goto v_reusejp_4069_;
}
else
{
lean_object* v_reuseFailAlloc_4071_; 
v_reuseFailAlloc_4071_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4071_, 0, v_a_4065_);
v___x_4070_ = v_reuseFailAlloc_4071_;
goto v_reusejp_4069_;
}
v_reusejp_4069_:
{
return v___x_4070_;
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
lean_object* v_a_4076_; lean_object* v___x_4078_; uint8_t v_isShared_4079_; uint8_t v_isSharedCheck_4083_; 
v_a_4076_ = lean_ctor_get(v___x_4037_, 0);
v_isSharedCheck_4083_ = !lean_is_exclusive(v___x_4037_);
if (v_isSharedCheck_4083_ == 0)
{
v___x_4078_ = v___x_4037_;
v_isShared_4079_ = v_isSharedCheck_4083_;
goto v_resetjp_4077_;
}
else
{
lean_inc(v_a_4076_);
lean_dec(v___x_4037_);
v___x_4078_ = lean_box(0);
v_isShared_4079_ = v_isSharedCheck_4083_;
goto v_resetjp_4077_;
}
v_resetjp_4077_:
{
lean_object* v___x_4081_; 
if (v_isShared_4079_ == 0)
{
v___x_4081_ = v___x_4078_;
goto v_reusejp_4080_;
}
else
{
lean_object* v_reuseFailAlloc_4082_; 
v_reuseFailAlloc_4082_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4082_, 0, v_a_4076_);
v___x_4081_ = v_reuseFailAlloc_4082_;
goto v_reusejp_4080_;
}
v_reusejp_4080_:
{
return v___x_4081_;
}
}
}
}
else
{
lean_object* v_a_4084_; lean_object* v___x_4086_; uint8_t v_isShared_4087_; uint8_t v_isSharedCheck_4091_; 
lean_dec(v_fst_4028_);
v_a_4084_ = lean_ctor_get(v___x_4034_, 0);
v_isSharedCheck_4091_ = !lean_is_exclusive(v___x_4034_);
if (v_isSharedCheck_4091_ == 0)
{
v___x_4086_ = v___x_4034_;
v_isShared_4087_ = v_isSharedCheck_4091_;
goto v_resetjp_4085_;
}
else
{
lean_inc(v_a_4084_);
lean_dec(v___x_4034_);
v___x_4086_ = lean_box(0);
v_isShared_4087_ = v_isSharedCheck_4091_;
goto v_resetjp_4085_;
}
v_resetjp_4085_:
{
lean_object* v___x_4089_; 
if (v_isShared_4087_ == 0)
{
v___x_4089_ = v___x_4086_;
goto v_reusejp_4088_;
}
else
{
lean_object* v_reuseFailAlloc_4090_; 
v_reuseFailAlloc_4090_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4090_, 0, v_a_4084_);
v___x_4089_ = v_reuseFailAlloc_4090_;
goto v_reusejp_4088_;
}
v_reusejp_4088_:
{
return v___x_4089_;
}
}
}
}
else
{
lean_object* v_a_4092_; lean_object* v___x_4094_; uint8_t v_isShared_4095_; uint8_t v_isSharedCheck_4099_; 
lean_dec_ref(v_sortedDecls_3959_);
v_a_4092_ = lean_ctor_get(v___x_4026_, 0);
v_isSharedCheck_4099_ = !lean_is_exclusive(v___x_4026_);
if (v_isSharedCheck_4099_ == 0)
{
v___x_4094_ = v___x_4026_;
v_isShared_4095_ = v_isSharedCheck_4099_;
goto v_resetjp_4093_;
}
else
{
lean_inc(v_a_4092_);
lean_dec(v___x_4026_);
v___x_4094_ = lean_box(0);
v_isShared_4095_ = v_isSharedCheck_4099_;
goto v_resetjp_4093_;
}
v_resetjp_4093_:
{
lean_object* v___x_4097_; 
if (v_isShared_4095_ == 0)
{
v___x_4097_ = v___x_4094_;
goto v_reusejp_4096_;
}
else
{
lean_object* v_reuseFailAlloc_4098_; 
v_reuseFailAlloc_4098_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4098_, 0, v_a_4092_);
v___x_4097_ = v_reuseFailAlloc_4098_;
goto v_reusejp_4096_;
}
v_reusejp_4096_:
{
return v___x_4097_;
}
}
}
}
}
}
else
{
lean_object* v_a_4103_; lean_object* v___x_4105_; uint8_t v_isShared_4106_; uint8_t v_isSharedCheck_4110_; 
lean_dec_ref(v_toSortArgs_3962_);
lean_dec_ref(v_sortedDecls_3959_);
v_a_4103_ = lean_ctor_get(v___x_4016_, 0);
v_isSharedCheck_4110_ = !lean_is_exclusive(v___x_4016_);
if (v_isSharedCheck_4110_ == 0)
{
v___x_4105_ = v___x_4016_;
v_isShared_4106_ = v_isSharedCheck_4110_;
goto v_resetjp_4104_;
}
else
{
lean_inc(v_a_4103_);
lean_dec(v___x_4016_);
v___x_4105_ = lean_box(0);
v_isShared_4106_ = v_isSharedCheck_4110_;
goto v_resetjp_4104_;
}
v_resetjp_4104_:
{
lean_object* v___x_4108_; 
if (v_isShared_4106_ == 0)
{
v___x_4108_ = v___x_4105_;
goto v_reusejp_4107_;
}
else
{
lean_object* v_reuseFailAlloc_4109_; 
v_reuseFailAlloc_4109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4109_, 0, v_a_4103_);
v___x_4108_ = v_reuseFailAlloc_4109_;
goto v_reusejp_4107_;
}
v_reusejp_4107_:
{
return v___x_4108_;
}
}
}
}
}
else
{
lean_object* v___x_4123_; lean_object* v___x_4124_; 
lean_dec_ref(v_toSortArgs_3962_);
v___x_4123_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4123_, 0, v_sortedDecls_3959_);
lean_ctor_set(v___x_4123_, 1, v_sortedArgs_3960_);
v___x_4124_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4124_, 0, v___x_4123_);
return v___x_4124_;
}
}
}
v___jp_3966_:
{
if (lean_obj_tag(v___y_3967_) == 0)
{
lean_object* v_a_3968_; lean_object* v___x_3970_; uint8_t v_isShared_3971_; uint8_t v_isSharedCheck_3976_; 
v_a_3968_ = lean_ctor_get(v___y_3967_, 0);
v_isSharedCheck_3976_ = !lean_is_exclusive(v___y_3967_);
if (v_isSharedCheck_3976_ == 0)
{
v___x_3970_ = v___y_3967_;
v_isShared_3971_ = v_isSharedCheck_3976_;
goto v_resetjp_3969_;
}
else
{
lean_inc(v_a_3968_);
lean_dec(v___y_3967_);
v___x_3970_ = lean_box(0);
v_isShared_3971_ = v_isSharedCheck_3976_;
goto v_resetjp_3969_;
}
v_resetjp_3969_:
{
lean_object* v_fst_3972_; lean_object* v___x_3974_; 
v_fst_3972_ = lean_ctor_get(v_a_3968_, 0);
lean_inc(v_fst_3972_);
lean_dec(v_a_3968_);
if (v_isShared_3971_ == 0)
{
lean_ctor_set(v___x_3970_, 0, v_fst_3972_);
v___x_3974_ = v___x_3970_;
goto v_reusejp_3973_;
}
else
{
lean_object* v_reuseFailAlloc_3975_; 
v_reuseFailAlloc_3975_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3975_, 0, v_fst_3972_);
v___x_3974_ = v_reuseFailAlloc_3975_;
goto v_reusejp_3973_;
}
v_reusejp_3973_:
{
return v___x_3974_;
}
}
}
else
{
lean_object* v_a_3977_; lean_object* v___x_3979_; uint8_t v_isShared_3980_; uint8_t v_isSharedCheck_3984_; 
v_a_3977_ = lean_ctor_get(v___y_3967_, 0);
v_isSharedCheck_3984_ = !lean_is_exclusive(v___y_3967_);
if (v_isSharedCheck_3984_ == 0)
{
v___x_3979_ = v___y_3967_;
v_isShared_3980_ = v_isSharedCheck_3984_;
goto v_resetjp_3978_;
}
else
{
lean_inc(v_a_3977_);
lean_dec(v___y_3967_);
v___x_3979_ = lean_box(0);
v_isShared_3980_ = v_isSharedCheck_3984_;
goto v_resetjp_3978_;
}
v_resetjp_3978_:
{
lean_object* v___x_3982_; 
if (v_isShared_3980_ == 0)
{
v___x_3982_ = v___x_3979_;
goto v_reusejp_3981_;
}
else
{
lean_object* v_reuseFailAlloc_3983_; 
v_reuseFailAlloc_3983_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3983_, 0, v_a_3977_);
v___x_3982_ = v_reuseFailAlloc_3983_;
goto v_reusejp_3981_;
}
v_reusejp_3981_:
{
return v___x_3982_;
}
}
}
}
v___jp_3985_:
{
lean_object* v___x_3991_; 
lean_inc(v___y_3988_);
lean_inc_ref(v___y_3986_);
v___x_3991_ = lean_apply_5(v___y_3989_, v___y_3987_, v_snd_3990_, v___y_3986_, v___y_3988_, lean_box(0));
v___y_3967_ = v___x_3991_;
goto v___jp_3966_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___boxed(lean_object* v_sortedDecls_4125_, lean_object* v_sortedArgs_4126_, lean_object* v_toSortDecls_4127_, lean_object* v_toSortArgs_4128_, lean_object* v_a_4129_, lean_object* v_a_4130_, lean_object* v_a_4131_){
_start:
{
lean_object* v_res_4132_; 
v_res_4132_ = l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls(v_sortedDecls_4125_, v_sortedArgs_4126_, v_toSortDecls_4127_, v_toSortArgs_4128_, v_a_4129_, v_a_4130_);
lean_dec(v_a_4130_);
lean_dec_ref(v_a_4129_);
lean_dec_ref(v_toSortDecls_4127_);
return v_res_4132_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__1(lean_object* v_00_u03b2_4133_, lean_object* v_m_4134_, lean_object* v_a_4135_, lean_object* v_b_4136_){
_start:
{
lean_object* v___x_4137_; 
v___x_4137_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__1___redArg(v_m_4134_, v_a_4135_, v_b_4136_);
return v___x_4137_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__2(lean_object* v_as_4138_, size_t v_sz_4139_, size_t v_i_4140_, lean_object* v_b_4141_, lean_object* v___y_4142_, lean_object* v___y_4143_){
_start:
{
lean_object* v___x_4145_; 
v___x_4145_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__2___redArg(v_as_4138_, v_sz_4139_, v_i_4140_, v_b_4141_);
return v___x_4145_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__2___boxed(lean_object* v_as_4146_, lean_object* v_sz_4147_, lean_object* v_i_4148_, lean_object* v_b_4149_, lean_object* v___y_4150_, lean_object* v___y_4151_, lean_object* v___y_4152_){
_start:
{
size_t v_sz_boxed_4153_; size_t v_i_boxed_4154_; lean_object* v_res_4155_; 
v_sz_boxed_4153_ = lean_unbox_usize(v_sz_4147_);
lean_dec(v_sz_4147_);
v_i_boxed_4154_ = lean_unbox_usize(v_i_4148_);
lean_dec(v_i_4148_);
v_res_4155_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__2(v_as_4146_, v_sz_boxed_4153_, v_i_boxed_4154_, v_b_4149_, v___y_4150_, v___y_4151_);
lean_dec(v___y_4151_);
lean_dec_ref(v___y_4150_);
lean_dec_ref(v_as_4146_);
return v_res_4155_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__1_spec__1(lean_object* v_00_u03b2_4156_, lean_object* v_a_4157_, lean_object* v_b_4158_, lean_object* v_x_4159_){
_start:
{
lean_object* v___x_4160_; 
v___x_4160_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__1_spec__1___redArg(v_a_4157_, v_b_4158_, v_x_4159_);
return v___x_4160_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Closure_mkValueTypeClosure_spec__0(lean_object* v_msg_4162_, lean_object* v___y_4163_, lean_object* v___y_4164_, lean_object* v___y_4165_, lean_object* v___y_4166_){
_start:
{
lean_object* v___f_4168_; lean_object* v___x_1273__overap_4169_; lean_object* v___x_4170_; 
v___f_4168_ = ((lean_object*)(l_panic___at___00Lean_Meta_Closure_mkValueTypeClosure_spec__0___closed__0));
v___x_1273__overap_4169_ = lean_panic_fn_borrowed(v___f_4168_, v_msg_4162_);
lean_inc(v___y_4166_);
lean_inc_ref(v___y_4165_);
lean_inc(v___y_4164_);
lean_inc_ref(v___y_4163_);
v___x_4170_ = lean_apply_5(v___x_1273__overap_4169_, v___y_4163_, v___y_4164_, v___y_4165_, v___y_4166_, lean_box(0));
return v___x_4170_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Closure_mkValueTypeClosure_spec__0___boxed(lean_object* v_msg_4171_, lean_object* v___y_4172_, lean_object* v___y_4173_, lean_object* v___y_4174_, lean_object* v___y_4175_, lean_object* v___y_4176_){
_start:
{
lean_object* v_res_4177_; 
v_res_4177_ = l_panic___at___00Lean_Meta_Closure_mkValueTypeClosure_spec__0(v_msg_4171_, v___y_4172_, v___y_4173_, v___y_4174_, v___y_4175_);
lean_dec(v___y_4175_);
lean_dec_ref(v___y_4174_);
lean_dec(v___y_4173_);
lean_dec_ref(v___y_4172_);
return v_res_4177_;
}
}
static lean_object* _init_l_Lean_Meta_Closure_mkValueTypeClosure___closed__0(void){
_start:
{
lean_object* v___x_4178_; lean_object* v___x_4179_; lean_object* v___x_4180_; 
v___x_4178_ = lean_box(0);
v___x_4179_ = lean_unsigned_to_nat(16u);
v___x_4180_ = lean_mk_array(v___x_4179_, v___x_4178_);
return v___x_4180_;
}
}
static lean_object* _init_l_Lean_Meta_Closure_mkValueTypeClosure___closed__1(void){
_start:
{
lean_object* v___x_4181_; lean_object* v___x_4182_; lean_object* v___x_4183_; 
v___x_4181_ = lean_obj_once(&l_Lean_Meta_Closure_mkValueTypeClosure___closed__0, &l_Lean_Meta_Closure_mkValueTypeClosure___closed__0_once, _init_l_Lean_Meta_Closure_mkValueTypeClosure___closed__0);
v___x_4182_ = lean_unsigned_to_nat(0u);
v___x_4183_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4183_, 0, v___x_4182_);
lean_ctor_set(v___x_4183_, 1, v___x_4181_);
return v___x_4183_;
}
}
static lean_object* _init_l_Lean_Meta_Closure_mkValueTypeClosure___closed__3(void){
_start:
{
lean_object* v___x_4186_; lean_object* v___x_4187_; lean_object* v___x_4188_; lean_object* v___x_4189_; 
v___x_4186_ = lean_unsigned_to_nat(1u);
v___x_4187_ = ((lean_object*)(l_Lean_Meta_Closure_mkValueTypeClosure___closed__2));
v___x_4188_ = lean_obj_once(&l_Lean_Meta_Closure_mkValueTypeClosure___closed__1, &l_Lean_Meta_Closure_mkValueTypeClosure___closed__1_once, _init_l_Lean_Meta_Closure_mkValueTypeClosure___closed__1);
v___x_4189_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_4189_, 0, v___x_4188_);
lean_ctor_set(v___x_4189_, 1, v___x_4188_);
lean_ctor_set(v___x_4189_, 2, v___x_4187_);
lean_ctor_set(v___x_4189_, 3, v___x_4186_);
lean_ctor_set(v___x_4189_, 4, v___x_4187_);
lean_ctor_set(v___x_4189_, 5, v___x_4187_);
lean_ctor_set(v___x_4189_, 6, v___x_4187_);
lean_ctor_set(v___x_4189_, 7, v___x_4187_);
lean_ctor_set(v___x_4189_, 8, v___x_4186_);
lean_ctor_set(v___x_4189_, 9, v___x_4187_);
lean_ctor_set(v___x_4189_, 10, v___x_4187_);
lean_ctor_set(v___x_4189_, 11, v___x_4187_);
return v___x_4189_;
}
}
static lean_object* _init_l_Lean_Meta_Closure_mkValueTypeClosure___closed__6(void){
_start:
{
lean_object* v___x_4192_; lean_object* v___x_4193_; lean_object* v___x_4194_; lean_object* v___x_4195_; lean_object* v___x_4196_; lean_object* v___x_4197_; 
v___x_4192_ = ((lean_object*)(l_Lean_Meta_Closure_mkValueTypeClosure___closed__5));
v___x_4193_ = lean_unsigned_to_nat(2u);
v___x_4194_ = lean_unsigned_to_nat(417u);
v___x_4195_ = ((lean_object*)(l_Lean_Meta_Closure_mkValueTypeClosure___closed__4));
v___x_4196_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__0));
v___x_4197_ = l_mkPanicMessageWithDecl(v___x_4196_, v___x_4195_, v___x_4194_, v___x_4193_, v___x_4192_);
return v___x_4197_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkValueTypeClosure(lean_object* v_type_4198_, lean_object* v_value_4199_, uint8_t v_zetaDelta_4200_, lean_object* v_a_4201_, lean_object* v_a_4202_, lean_object* v_a_4203_, lean_object* v_a_4204_){
_start:
{
lean_object* v___x_4206_; lean_object* v___x_4207_; lean_object* v___x_4208_; 
v___x_4206_ = lean_obj_once(&l_Lean_Meta_Closure_mkValueTypeClosure___closed__3, &l_Lean_Meta_Closure_mkValueTypeClosure___closed__3_once, _init_l_Lean_Meta_Closure_mkValueTypeClosure___closed__3);
v___x_4207_ = lean_st_mk_ref(v___x_4206_);
v___x_4208_ = l_Lean_Meta_Closure_mkValueTypeClosureAux(v_type_4198_, v_value_4199_, v_zetaDelta_4200_, v___x_4207_, v_a_4201_, v_a_4202_, v_a_4203_, v_a_4204_);
if (lean_obj_tag(v___x_4208_) == 0)
{
lean_object* v_a_4209_; lean_object* v___x_4210_; lean_object* v_fst_4211_; lean_object* v_snd_4212_; lean_object* v_levelParams_4213_; lean_object* v_levelArgs_4214_; lean_object* v_newLocalDecls_4215_; lean_object* v_newLocalDeclsForMVars_4216_; lean_object* v_newLetDecls_4217_; lean_object* v_exprMVarArgs_4218_; lean_object* v_exprFVarArgs_4219_; lean_object* v___x_4220_; lean_object* v___x_4221_; lean_object* v___x_4222_; 
v_a_4209_ = lean_ctor_get(v___x_4208_, 0);
lean_inc(v_a_4209_);
lean_dec_ref_known(v___x_4208_, 1);
v___x_4210_ = lean_st_ref_get(v___x_4207_);
lean_dec(v___x_4207_);
v_fst_4211_ = lean_ctor_get(v_a_4209_, 0);
lean_inc(v_fst_4211_);
v_snd_4212_ = lean_ctor_get(v_a_4209_, 1);
lean_inc(v_snd_4212_);
lean_dec(v_a_4209_);
v_levelParams_4213_ = lean_ctor_get(v___x_4210_, 2);
lean_inc_ref(v_levelParams_4213_);
v_levelArgs_4214_ = lean_ctor_get(v___x_4210_, 4);
lean_inc_ref(v_levelArgs_4214_);
v_newLocalDecls_4215_ = lean_ctor_get(v___x_4210_, 5);
lean_inc_ref(v_newLocalDecls_4215_);
v_newLocalDeclsForMVars_4216_ = lean_ctor_get(v___x_4210_, 6);
lean_inc_ref(v_newLocalDeclsForMVars_4216_);
v_newLetDecls_4217_ = lean_ctor_get(v___x_4210_, 7);
lean_inc_ref(v_newLetDecls_4217_);
v_exprMVarArgs_4218_ = lean_ctor_get(v___x_4210_, 9);
lean_inc_ref(v_exprMVarArgs_4218_);
v_exprFVarArgs_4219_ = lean_ctor_get(v___x_4210_, 10);
lean_inc_ref(v_exprFVarArgs_4219_);
lean_dec(v___x_4210_);
v___x_4220_ = l_Array_reverse___redArg(v_newLocalDecls_4215_);
v___x_4221_ = l_Array_reverse___redArg(v_exprFVarArgs_4219_);
v___x_4222_ = l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls(v___x_4220_, v___x_4221_, v_newLocalDeclsForMVars_4216_, v_exprMVarArgs_4218_, v_a_4203_, v_a_4204_);
lean_dec_ref(v_newLocalDeclsForMVars_4216_);
if (lean_obj_tag(v___x_4222_) == 0)
{
lean_object* v_a_4223_; lean_object* v___x_4225_; uint8_t v_isShared_4226_; uint8_t v_isSharedCheck_4242_; 
v_a_4223_ = lean_ctor_get(v___x_4222_, 0);
v_isSharedCheck_4242_ = !lean_is_exclusive(v___x_4222_);
if (v_isSharedCheck_4242_ == 0)
{
v___x_4225_ = v___x_4222_;
v_isShared_4226_ = v_isSharedCheck_4242_;
goto v_resetjp_4224_;
}
else
{
lean_inc(v_a_4223_);
lean_dec(v___x_4222_);
v___x_4225_ = lean_box(0);
v_isShared_4226_ = v_isSharedCheck_4242_;
goto v_resetjp_4224_;
}
v_resetjp_4224_:
{
lean_object* v_fst_4227_; lean_object* v_snd_4228_; lean_object* v___x_4229_; lean_object* v___x_4230_; lean_object* v___x_4231_; lean_object* v___x_4232_; lean_object* v___x_4233_; uint8_t v___x_4234_; uint8_t v___x_4235_; 
v_fst_4227_ = lean_ctor_get(v_a_4223_, 0);
lean_inc_n(v_fst_4227_, 2);
v_snd_4228_ = lean_ctor_get(v_a_4223_, 1);
lean_inc(v_snd_4228_);
lean_dec(v_a_4223_);
v___x_4229_ = l_Array_reverse___redArg(v_newLetDecls_4217_);
lean_inc_ref(v___x_4229_);
v___x_4230_ = l_Lean_Meta_Closure_mkForall(v___x_4229_, v_fst_4211_);
lean_dec(v_fst_4211_);
v___x_4231_ = l_Lean_Meta_Closure_mkForall(v_fst_4227_, v___x_4230_);
lean_dec_ref(v___x_4230_);
v___x_4232_ = l_Lean_Meta_Closure_mkLambda(v___x_4229_, v_snd_4212_);
lean_dec(v_snd_4212_);
v___x_4233_ = l_Lean_Meta_Closure_mkLambda(v_fst_4227_, v___x_4232_);
lean_dec_ref(v___x_4232_);
v___x_4234_ = l_Lean_Expr_hasFVar(v___x_4233_);
v___x_4235_ = lean_bool_not(v___x_4234_);
if (v___x_4235_ == 0)
{
lean_object* v___x_4236_; lean_object* v___x_4237_; 
lean_dec_ref(v___x_4233_);
lean_dec_ref(v___x_4231_);
lean_dec(v_snd_4228_);
lean_del_object(v___x_4225_);
lean_dec_ref(v_levelArgs_4214_);
lean_dec_ref(v_levelParams_4213_);
v___x_4236_ = lean_obj_once(&l_Lean_Meta_Closure_mkValueTypeClosure___closed__6, &l_Lean_Meta_Closure_mkValueTypeClosure___closed__6_once, _init_l_Lean_Meta_Closure_mkValueTypeClosure___closed__6);
v___x_4237_ = l_panic___at___00Lean_Meta_Closure_mkValueTypeClosure_spec__0(v___x_4236_, v_a_4201_, v_a_4202_, v_a_4203_, v_a_4204_);
return v___x_4237_;
}
else
{
lean_object* v___x_4238_; lean_object* v___x_4240_; 
v___x_4238_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4238_, 0, v_levelParams_4213_);
lean_ctor_set(v___x_4238_, 1, v___x_4231_);
lean_ctor_set(v___x_4238_, 2, v___x_4233_);
lean_ctor_set(v___x_4238_, 3, v_levelArgs_4214_);
lean_ctor_set(v___x_4238_, 4, v_snd_4228_);
if (v_isShared_4226_ == 0)
{
lean_ctor_set(v___x_4225_, 0, v___x_4238_);
v___x_4240_ = v___x_4225_;
goto v_reusejp_4239_;
}
else
{
lean_object* v_reuseFailAlloc_4241_; 
v_reuseFailAlloc_4241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4241_, 0, v___x_4238_);
v___x_4240_ = v_reuseFailAlloc_4241_;
goto v_reusejp_4239_;
}
v_reusejp_4239_:
{
return v___x_4240_;
}
}
}
}
else
{
lean_object* v_a_4243_; lean_object* v___x_4245_; uint8_t v_isShared_4246_; uint8_t v_isSharedCheck_4250_; 
lean_dec_ref(v_newLetDecls_4217_);
lean_dec_ref(v_levelArgs_4214_);
lean_dec_ref(v_levelParams_4213_);
lean_dec(v_snd_4212_);
lean_dec(v_fst_4211_);
v_a_4243_ = lean_ctor_get(v___x_4222_, 0);
v_isSharedCheck_4250_ = !lean_is_exclusive(v___x_4222_);
if (v_isSharedCheck_4250_ == 0)
{
v___x_4245_ = v___x_4222_;
v_isShared_4246_ = v_isSharedCheck_4250_;
goto v_resetjp_4244_;
}
else
{
lean_inc(v_a_4243_);
lean_dec(v___x_4222_);
v___x_4245_ = lean_box(0);
v_isShared_4246_ = v_isSharedCheck_4250_;
goto v_resetjp_4244_;
}
v_resetjp_4244_:
{
lean_object* v___x_4248_; 
if (v_isShared_4246_ == 0)
{
v___x_4248_ = v___x_4245_;
goto v_reusejp_4247_;
}
else
{
lean_object* v_reuseFailAlloc_4249_; 
v_reuseFailAlloc_4249_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4249_, 0, v_a_4243_);
v___x_4248_ = v_reuseFailAlloc_4249_;
goto v_reusejp_4247_;
}
v_reusejp_4247_:
{
return v___x_4248_;
}
}
}
}
else
{
lean_object* v_a_4251_; lean_object* v___x_4253_; uint8_t v_isShared_4254_; uint8_t v_isSharedCheck_4258_; 
lean_dec(v___x_4207_);
v_a_4251_ = lean_ctor_get(v___x_4208_, 0);
v_isSharedCheck_4258_ = !lean_is_exclusive(v___x_4208_);
if (v_isSharedCheck_4258_ == 0)
{
v___x_4253_ = v___x_4208_;
v_isShared_4254_ = v_isSharedCheck_4258_;
goto v_resetjp_4252_;
}
else
{
lean_inc(v_a_4251_);
lean_dec(v___x_4208_);
v___x_4253_ = lean_box(0);
v_isShared_4254_ = v_isSharedCheck_4258_;
goto v_resetjp_4252_;
}
v_resetjp_4252_:
{
lean_object* v___x_4256_; 
if (v_isShared_4254_ == 0)
{
v___x_4256_ = v___x_4253_;
goto v_reusejp_4255_;
}
else
{
lean_object* v_reuseFailAlloc_4257_; 
v_reuseFailAlloc_4257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4257_, 0, v_a_4251_);
v___x_4256_ = v_reuseFailAlloc_4257_;
goto v_reusejp_4255_;
}
v_reusejp_4255_:
{
return v___x_4256_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkValueTypeClosure___boxed(lean_object* v_type_4259_, lean_object* v_value_4260_, lean_object* v_zetaDelta_4261_, lean_object* v_a_4262_, lean_object* v_a_4263_, lean_object* v_a_4264_, lean_object* v_a_4265_, lean_object* v_a_4266_){
_start:
{
uint8_t v_zetaDelta_boxed_4267_; lean_object* v_res_4268_; 
v_zetaDelta_boxed_4267_ = lean_unbox(v_zetaDelta_4261_);
v_res_4268_ = l_Lean_Meta_Closure_mkValueTypeClosure(v_type_4259_, v_value_4260_, v_zetaDelta_boxed_4267_, v_a_4262_, v_a_4263_, v_a_4264_, v_a_4265_);
lean_dec(v_a_4265_);
lean_dec_ref(v_a_4264_);
lean_dec(v_a_4263_);
lean_dec_ref(v_a_4262_);
return v_res_4268_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkAuxDefinition_spec__0___redArg(lean_object* v_name_4269_, lean_object* v_levelParams_4270_, lean_object* v_type_4271_, lean_object* v_value_4272_, lean_object* v_hints_4273_, lean_object* v___y_4274_){
_start:
{
lean_object* v___x_4276_; uint8_t v___y_4278_; uint8_t v___y_4285_; lean_object* v_env_4288_; uint8_t v___x_4289_; 
v___x_4276_ = lean_st_ref_get(v___y_4274_);
v_env_4288_ = lean_ctor_get(v___x_4276_, 0);
lean_inc_ref_n(v_env_4288_, 2);
lean_dec(v___x_4276_);
v___x_4289_ = l_Lean_Environment_hasUnsafe(v_env_4288_, v_type_4271_);
if (v___x_4289_ == 0)
{
uint8_t v___x_4290_; 
v___x_4290_ = l_Lean_Environment_hasUnsafe(v_env_4288_, v_value_4272_);
v___y_4285_ = v___x_4290_;
goto v___jp_4284_;
}
else
{
lean_dec_ref(v_env_4288_);
v___y_4285_ = v___x_4289_;
goto v___jp_4284_;
}
v___jp_4277_:
{
lean_object* v___x_4279_; lean_object* v___x_4280_; lean_object* v___x_4281_; lean_object* v___x_4282_; lean_object* v___x_4283_; 
lean_inc(v_name_4269_);
v___x_4279_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4279_, 0, v_name_4269_);
lean_ctor_set(v___x_4279_, 1, v_levelParams_4270_);
lean_ctor_set(v___x_4279_, 2, v_type_4271_);
v___x_4280_ = lean_box(0);
v___x_4281_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4281_, 0, v_name_4269_);
lean_ctor_set(v___x_4281_, 1, v___x_4280_);
v___x_4282_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_4282_, 0, v___x_4279_);
lean_ctor_set(v___x_4282_, 1, v_value_4272_);
lean_ctor_set(v___x_4282_, 2, v_hints_4273_);
lean_ctor_set(v___x_4282_, 3, v___x_4281_);
lean_ctor_set_uint8(v___x_4282_, sizeof(void*)*4, v___y_4278_);
v___x_4283_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4283_, 0, v___x_4282_);
return v___x_4283_;
}
v___jp_4284_:
{
if (v___y_4285_ == 0)
{
uint8_t v___x_4286_; 
v___x_4286_ = 1;
v___y_4278_ = v___x_4286_;
goto v___jp_4277_;
}
else
{
uint8_t v___x_4287_; 
v___x_4287_ = 0;
v___y_4278_ = v___x_4287_;
goto v___jp_4277_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkAuxDefinition_spec__0___redArg___boxed(lean_object* v_name_4291_, lean_object* v_levelParams_4292_, lean_object* v_type_4293_, lean_object* v_value_4294_, lean_object* v_hints_4295_, lean_object* v___y_4296_, lean_object* v___y_4297_){
_start:
{
lean_object* v_res_4298_; 
v_res_4298_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkAuxDefinition_spec__0___redArg(v_name_4291_, v_levelParams_4292_, v_type_4293_, v_value_4294_, v_hints_4295_, v___y_4296_);
lean_dec(v___y_4296_);
return v_res_4298_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkAuxDefinition_spec__0(lean_object* v_name_4299_, lean_object* v_levelParams_4300_, lean_object* v_type_4301_, lean_object* v_value_4302_, lean_object* v_hints_4303_, lean_object* v___y_4304_, lean_object* v___y_4305_, lean_object* v___y_4306_, lean_object* v___y_4307_){
_start:
{
lean_object* v___x_4309_; 
v___x_4309_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkAuxDefinition_spec__0___redArg(v_name_4299_, v_levelParams_4300_, v_type_4301_, v_value_4302_, v_hints_4303_, v___y_4307_);
return v___x_4309_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkAuxDefinition_spec__0___boxed(lean_object* v_name_4310_, lean_object* v_levelParams_4311_, lean_object* v_type_4312_, lean_object* v_value_4313_, lean_object* v_hints_4314_, lean_object* v___y_4315_, lean_object* v___y_4316_, lean_object* v___y_4317_, lean_object* v___y_4318_, lean_object* v___y_4319_){
_start:
{
lean_object* v_res_4320_; 
v_res_4320_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkAuxDefinition_spec__0(v_name_4310_, v_levelParams_4311_, v_type_4312_, v_value_4313_, v_hints_4314_, v___y_4315_, v___y_4316_, v___y_4317_, v___y_4318_);
lean_dec(v___y_4318_);
lean_dec_ref(v___y_4317_);
lean_dec(v___y_4316_);
lean_dec_ref(v___y_4315_);
return v_res_4320_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAuxDefinition(lean_object* v_name_4321_, lean_object* v_type_4322_, lean_object* v_value_4323_, uint8_t v_zetaDelta_4324_, uint8_t v_compile_4325_, uint8_t v_logCompileErrors_4326_, lean_object* v_a_4327_, lean_object* v_a_4328_, lean_object* v_a_4329_, lean_object* v_a_4330_){
_start:
{
lean_object* v___x_4332_; 
v___x_4332_ = l_Lean_Meta_Closure_mkValueTypeClosure(v_type_4322_, v_value_4323_, v_zetaDelta_4324_, v_a_4327_, v_a_4328_, v_a_4329_, v_a_4330_);
if (lean_obj_tag(v___x_4332_) == 0)
{
lean_object* v_a_4333_; lean_object* v___x_4335_; uint8_t v_isShared_4336_; uint8_t v_isSharedCheck_4384_; 
v_a_4333_ = lean_ctor_get(v___x_4332_, 0);
v_isSharedCheck_4384_ = !lean_is_exclusive(v___x_4332_);
if (v_isSharedCheck_4384_ == 0)
{
v___x_4335_ = v___x_4332_;
v_isShared_4336_ = v_isSharedCheck_4384_;
goto v_resetjp_4334_;
}
else
{
lean_inc(v_a_4333_);
lean_dec(v___x_4332_);
v___x_4335_ = lean_box(0);
v_isShared_4336_ = v_isSharedCheck_4384_;
goto v_resetjp_4334_;
}
v_resetjp_4334_:
{
lean_object* v___x_4337_; lean_object* v_env_4338_; lean_object* v_levelParams_4339_; lean_object* v_type_4340_; lean_object* v_value_4341_; lean_object* v_levelArgs_4342_; lean_object* v_exprArgs_4343_; uint32_t v___x_4351_; uint32_t v___x_4352_; uint32_t v___x_4353_; lean_object* v___x_4354_; lean_object* v___x_4355_; lean_object* v___x_4356_; lean_object* v_a_4357_; lean_object* v___x_4359_; uint8_t v_isShared_4360_; uint8_t v_isSharedCheck_4383_; 
v___x_4337_ = lean_st_ref_get(v_a_4330_);
v_env_4338_ = lean_ctor_get(v___x_4337_, 0);
lean_inc_ref(v_env_4338_);
lean_dec(v___x_4337_);
v_levelParams_4339_ = lean_ctor_get(v_a_4333_, 0);
lean_inc_ref(v_levelParams_4339_);
v_type_4340_ = lean_ctor_get(v_a_4333_, 1);
lean_inc_ref(v_type_4340_);
v_value_4341_ = lean_ctor_get(v_a_4333_, 2);
lean_inc_ref_n(v_value_4341_, 2);
v_levelArgs_4342_ = lean_ctor_get(v_a_4333_, 3);
lean_inc_ref(v_levelArgs_4342_);
v_exprArgs_4343_ = lean_ctor_get(v_a_4333_, 4);
lean_inc_ref(v_exprArgs_4343_);
lean_dec(v_a_4333_);
v___x_4351_ = l_Lean_getMaxHeight(v_env_4338_, v_value_4341_);
v___x_4352_ = 1;
v___x_4353_ = lean_uint32_add(v___x_4351_, v___x_4352_);
v___x_4354_ = lean_alloc_ctor(2, 0, 4);
lean_ctor_set_uint32(v___x_4354_, 0, v___x_4353_);
v___x_4355_ = lean_array_to_list(v_levelParams_4339_);
lean_inc(v_name_4321_);
v___x_4356_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkAuxDefinition_spec__0___redArg(v_name_4321_, v___x_4355_, v_type_4340_, v_value_4341_, v___x_4354_, v_a_4330_);
v_a_4357_ = lean_ctor_get(v___x_4356_, 0);
v_isSharedCheck_4383_ = !lean_is_exclusive(v___x_4356_);
if (v_isSharedCheck_4383_ == 0)
{
v___x_4359_ = v___x_4356_;
v_isShared_4360_ = v_isSharedCheck_4383_;
goto v_resetjp_4358_;
}
else
{
lean_inc(v_a_4357_);
lean_dec(v___x_4356_);
v___x_4359_ = lean_box(0);
v_isShared_4360_ = v_isSharedCheck_4383_;
goto v_resetjp_4358_;
}
v___jp_4344_:
{
lean_object* v___x_4345_; lean_object* v___x_4346_; lean_object* v___x_4347_; lean_object* v___x_4349_; 
v___x_4345_ = lean_array_to_list(v_levelArgs_4342_);
v___x_4346_ = l_Lean_mkConst(v_name_4321_, v___x_4345_);
v___x_4347_ = l_Lean_mkAppN(v___x_4346_, v_exprArgs_4343_);
lean_dec_ref(v_exprArgs_4343_);
if (v_isShared_4336_ == 0)
{
lean_ctor_set(v___x_4335_, 0, v___x_4347_);
v___x_4349_ = v___x_4335_;
goto v_reusejp_4348_;
}
else
{
lean_object* v_reuseFailAlloc_4350_; 
v_reuseFailAlloc_4350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4350_, 0, v___x_4347_);
v___x_4349_ = v_reuseFailAlloc_4350_;
goto v_reusejp_4348_;
}
v_reusejp_4348_:
{
return v___x_4349_;
}
}
v_resetjp_4358_:
{
lean_object* v___x_4362_; 
if (v_isShared_4360_ == 0)
{
lean_ctor_set_tag(v___x_4359_, 1);
v___x_4362_ = v___x_4359_;
goto v_reusejp_4361_;
}
else
{
lean_object* v_reuseFailAlloc_4382_; 
v_reuseFailAlloc_4382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4382_, 0, v_a_4357_);
v___x_4362_ = v_reuseFailAlloc_4382_;
goto v_reusejp_4361_;
}
v_reusejp_4361_:
{
uint8_t v___x_4363_; lean_object* v___x_4364_; 
v___x_4363_ = 0;
lean_inc_ref(v___x_4362_);
v___x_4364_ = l_Lean_addDecl(v___x_4362_, v___x_4363_, v_a_4329_, v_a_4330_);
if (lean_obj_tag(v___x_4364_) == 0)
{
lean_dec_ref_known(v___x_4364_, 1);
if (v_compile_4325_ == 0)
{
lean_dec_ref(v___x_4362_);
goto v___jp_4344_;
}
else
{
lean_object* v___x_4365_; 
v___x_4365_ = l_Lean_compileDecl(v___x_4362_, v_logCompileErrors_4326_, v_a_4329_, v_a_4330_);
if (lean_obj_tag(v___x_4365_) == 0)
{
lean_dec_ref_known(v___x_4365_, 1);
goto v___jp_4344_;
}
else
{
lean_object* v_a_4366_; lean_object* v___x_4368_; uint8_t v_isShared_4369_; uint8_t v_isSharedCheck_4373_; 
lean_dec_ref(v_exprArgs_4343_);
lean_dec_ref(v_levelArgs_4342_);
lean_del_object(v___x_4335_);
lean_dec(v_name_4321_);
v_a_4366_ = lean_ctor_get(v___x_4365_, 0);
v_isSharedCheck_4373_ = !lean_is_exclusive(v___x_4365_);
if (v_isSharedCheck_4373_ == 0)
{
v___x_4368_ = v___x_4365_;
v_isShared_4369_ = v_isSharedCheck_4373_;
goto v_resetjp_4367_;
}
else
{
lean_inc(v_a_4366_);
lean_dec(v___x_4365_);
v___x_4368_ = lean_box(0);
v_isShared_4369_ = v_isSharedCheck_4373_;
goto v_resetjp_4367_;
}
v_resetjp_4367_:
{
lean_object* v___x_4371_; 
if (v_isShared_4369_ == 0)
{
v___x_4371_ = v___x_4368_;
goto v_reusejp_4370_;
}
else
{
lean_object* v_reuseFailAlloc_4372_; 
v_reuseFailAlloc_4372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4372_, 0, v_a_4366_);
v___x_4371_ = v_reuseFailAlloc_4372_;
goto v_reusejp_4370_;
}
v_reusejp_4370_:
{
return v___x_4371_;
}
}
}
}
}
else
{
lean_object* v_a_4374_; lean_object* v___x_4376_; uint8_t v_isShared_4377_; uint8_t v_isSharedCheck_4381_; 
lean_dec_ref(v___x_4362_);
lean_dec_ref(v_exprArgs_4343_);
lean_dec_ref(v_levelArgs_4342_);
lean_del_object(v___x_4335_);
lean_dec(v_name_4321_);
v_a_4374_ = lean_ctor_get(v___x_4364_, 0);
v_isSharedCheck_4381_ = !lean_is_exclusive(v___x_4364_);
if (v_isSharedCheck_4381_ == 0)
{
v___x_4376_ = v___x_4364_;
v_isShared_4377_ = v_isSharedCheck_4381_;
goto v_resetjp_4375_;
}
else
{
lean_inc(v_a_4374_);
lean_dec(v___x_4364_);
v___x_4376_ = lean_box(0);
v_isShared_4377_ = v_isSharedCheck_4381_;
goto v_resetjp_4375_;
}
v_resetjp_4375_:
{
lean_object* v___x_4379_; 
if (v_isShared_4377_ == 0)
{
v___x_4379_ = v___x_4376_;
goto v_reusejp_4378_;
}
else
{
lean_object* v_reuseFailAlloc_4380_; 
v_reuseFailAlloc_4380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4380_, 0, v_a_4374_);
v___x_4379_ = v_reuseFailAlloc_4380_;
goto v_reusejp_4378_;
}
v_reusejp_4378_:
{
return v___x_4379_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4385_; lean_object* v___x_4387_; uint8_t v_isShared_4388_; uint8_t v_isSharedCheck_4392_; 
lean_dec(v_name_4321_);
v_a_4385_ = lean_ctor_get(v___x_4332_, 0);
v_isSharedCheck_4392_ = !lean_is_exclusive(v___x_4332_);
if (v_isSharedCheck_4392_ == 0)
{
v___x_4387_ = v___x_4332_;
v_isShared_4388_ = v_isSharedCheck_4392_;
goto v_resetjp_4386_;
}
else
{
lean_inc(v_a_4385_);
lean_dec(v___x_4332_);
v___x_4387_ = lean_box(0);
v_isShared_4388_ = v_isSharedCheck_4392_;
goto v_resetjp_4386_;
}
v_resetjp_4386_:
{
lean_object* v___x_4390_; 
if (v_isShared_4388_ == 0)
{
v___x_4390_ = v___x_4387_;
goto v_reusejp_4389_;
}
else
{
lean_object* v_reuseFailAlloc_4391_; 
v_reuseFailAlloc_4391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4391_, 0, v_a_4385_);
v___x_4390_ = v_reuseFailAlloc_4391_;
goto v_reusejp_4389_;
}
v_reusejp_4389_:
{
return v___x_4390_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAuxDefinition___boxed(lean_object* v_name_4393_, lean_object* v_type_4394_, lean_object* v_value_4395_, lean_object* v_zetaDelta_4396_, lean_object* v_compile_4397_, lean_object* v_logCompileErrors_4398_, lean_object* v_a_4399_, lean_object* v_a_4400_, lean_object* v_a_4401_, lean_object* v_a_4402_, lean_object* v_a_4403_){
_start:
{
uint8_t v_zetaDelta_boxed_4404_; uint8_t v_compile_boxed_4405_; uint8_t v_logCompileErrors_boxed_4406_; lean_object* v_res_4407_; 
v_zetaDelta_boxed_4404_ = lean_unbox(v_zetaDelta_4396_);
v_compile_boxed_4405_ = lean_unbox(v_compile_4397_);
v_logCompileErrors_boxed_4406_ = lean_unbox(v_logCompileErrors_4398_);
v_res_4407_ = l_Lean_Meta_mkAuxDefinition(v_name_4393_, v_type_4394_, v_value_4395_, v_zetaDelta_boxed_4404_, v_compile_boxed_4405_, v_logCompileErrors_boxed_4406_, v_a_4399_, v_a_4400_, v_a_4401_, v_a_4402_);
lean_dec(v_a_4402_);
lean_dec_ref(v_a_4401_);
lean_dec(v_a_4400_);
lean_dec_ref(v_a_4399_);
return v_res_4407_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAuxDefinitionFor(lean_object* v_name_4408_, lean_object* v_value_4409_, uint8_t v_zetaDelta_4410_, uint8_t v_compile_4411_, uint8_t v_logCompileErrors_4412_, lean_object* v_a_4413_, lean_object* v_a_4414_, lean_object* v_a_4415_, lean_object* v_a_4416_){
_start:
{
lean_object* v___x_4418_; 
lean_inc(v_a_4416_);
lean_inc_ref(v_a_4415_);
lean_inc(v_a_4414_);
lean_inc_ref(v_a_4413_);
lean_inc_ref(v_value_4409_);
v___x_4418_ = lean_infer_type(v_value_4409_, v_a_4413_, v_a_4414_, v_a_4415_, v_a_4416_);
if (lean_obj_tag(v___x_4418_) == 0)
{
lean_object* v_a_4419_; lean_object* v___x_4420_; lean_object* v___x_4421_; 
v_a_4419_ = lean_ctor_get(v___x_4418_, 0);
lean_inc(v_a_4419_);
lean_dec_ref_known(v___x_4418_, 1);
v___x_4420_ = l_Lean_Expr_headBeta(v_a_4419_);
v___x_4421_ = l_Lean_Meta_mkAuxDefinition(v_name_4408_, v___x_4420_, v_value_4409_, v_zetaDelta_4410_, v_compile_4411_, v_logCompileErrors_4412_, v_a_4413_, v_a_4414_, v_a_4415_, v_a_4416_);
return v___x_4421_;
}
else
{
lean_dec_ref(v_value_4409_);
lean_dec(v_name_4408_);
return v___x_4418_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAuxDefinitionFor___boxed(lean_object* v_name_4422_, lean_object* v_value_4423_, lean_object* v_zetaDelta_4424_, lean_object* v_compile_4425_, lean_object* v_logCompileErrors_4426_, lean_object* v_a_4427_, lean_object* v_a_4428_, lean_object* v_a_4429_, lean_object* v_a_4430_, lean_object* v_a_4431_){
_start:
{
uint8_t v_zetaDelta_boxed_4432_; uint8_t v_compile_boxed_4433_; uint8_t v_logCompileErrors_boxed_4434_; lean_object* v_res_4435_; 
v_zetaDelta_boxed_4432_ = lean_unbox(v_zetaDelta_4424_);
v_compile_boxed_4433_ = lean_unbox(v_compile_4425_);
v_logCompileErrors_boxed_4434_ = lean_unbox(v_logCompileErrors_4426_);
v_res_4435_ = l_Lean_Meta_mkAuxDefinitionFor(v_name_4422_, v_value_4423_, v_zetaDelta_boxed_4432_, v_compile_boxed_4433_, v_logCompileErrors_boxed_4434_, v_a_4427_, v_a_4428_, v_a_4429_, v_a_4430_);
lean_dec(v_a_4430_);
lean_dec_ref(v_a_4429_);
lean_dec(v_a_4428_);
lean_dec_ref(v_a_4427_);
return v_res_4435_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAuxTheorem(lean_object* v_type_4436_, lean_object* v_value_4437_, uint8_t v_zetaDelta_4438_, lean_object* v_kind_x3f_4439_, uint8_t v_cache_4440_, lean_object* v_a_4441_, lean_object* v_a_4442_, lean_object* v_a_4443_, lean_object* v_a_4444_){
_start:
{
lean_object* v___x_4446_; 
v___x_4446_ = l_Lean_Meta_Closure_mkValueTypeClosure(v_type_4436_, v_value_4437_, v_zetaDelta_4438_, v_a_4441_, v_a_4442_, v_a_4443_, v_a_4444_);
if (lean_obj_tag(v___x_4446_) == 0)
{
lean_object* v_a_4447_; lean_object* v_levelParams_4448_; lean_object* v_type_4449_; lean_object* v_value_4450_; lean_object* v_levelArgs_4451_; lean_object* v_exprArgs_4452_; lean_object* v___x_4453_; uint8_t v___x_4454_; lean_object* v___x_4455_; 
v_a_4447_ = lean_ctor_get(v___x_4446_, 0);
lean_inc(v_a_4447_);
lean_dec_ref_known(v___x_4446_, 1);
v_levelParams_4448_ = lean_ctor_get(v_a_4447_, 0);
lean_inc_ref(v_levelParams_4448_);
v_type_4449_ = lean_ctor_get(v_a_4447_, 1);
lean_inc_ref(v_type_4449_);
v_value_4450_ = lean_ctor_get(v_a_4447_, 2);
lean_inc_ref(v_value_4450_);
v_levelArgs_4451_ = lean_ctor_get(v_a_4447_, 3);
lean_inc_ref(v_levelArgs_4451_);
v_exprArgs_4452_ = lean_ctor_get(v_a_4447_, 4);
lean_inc_ref(v_exprArgs_4452_);
lean_dec(v_a_4447_);
v___x_4453_ = lean_array_to_list(v_levelParams_4448_);
v___x_4454_ = 0;
v___x_4455_ = l_Lean_Meta_mkAuxLemma(v___x_4453_, v_type_4449_, v_value_4450_, v_kind_x3f_4439_, v_cache_4440_, v___x_4454_, v___x_4454_, v___x_4454_, v_a_4441_, v_a_4442_, v_a_4443_, v_a_4444_);
if (lean_obj_tag(v___x_4455_) == 0)
{
lean_object* v_a_4456_; lean_object* v___x_4458_; uint8_t v_isShared_4459_; uint8_t v_isSharedCheck_4466_; 
v_a_4456_ = lean_ctor_get(v___x_4455_, 0);
v_isSharedCheck_4466_ = !lean_is_exclusive(v___x_4455_);
if (v_isSharedCheck_4466_ == 0)
{
v___x_4458_ = v___x_4455_;
v_isShared_4459_ = v_isSharedCheck_4466_;
goto v_resetjp_4457_;
}
else
{
lean_inc(v_a_4456_);
lean_dec(v___x_4455_);
v___x_4458_ = lean_box(0);
v_isShared_4459_ = v_isSharedCheck_4466_;
goto v_resetjp_4457_;
}
v_resetjp_4457_:
{
lean_object* v___x_4460_; lean_object* v___x_4461_; lean_object* v___x_4462_; lean_object* v___x_4464_; 
v___x_4460_ = lean_array_to_list(v_levelArgs_4451_);
v___x_4461_ = l_Lean_mkConst(v_a_4456_, v___x_4460_);
v___x_4462_ = l_Lean_mkAppN(v___x_4461_, v_exprArgs_4452_);
lean_dec_ref(v_exprArgs_4452_);
if (v_isShared_4459_ == 0)
{
lean_ctor_set(v___x_4458_, 0, v___x_4462_);
v___x_4464_ = v___x_4458_;
goto v_reusejp_4463_;
}
else
{
lean_object* v_reuseFailAlloc_4465_; 
v_reuseFailAlloc_4465_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4465_, 0, v___x_4462_);
v___x_4464_ = v_reuseFailAlloc_4465_;
goto v_reusejp_4463_;
}
v_reusejp_4463_:
{
return v___x_4464_;
}
}
}
else
{
lean_object* v_a_4467_; lean_object* v___x_4469_; uint8_t v_isShared_4470_; uint8_t v_isSharedCheck_4474_; 
lean_dec_ref(v_exprArgs_4452_);
lean_dec_ref(v_levelArgs_4451_);
v_a_4467_ = lean_ctor_get(v___x_4455_, 0);
v_isSharedCheck_4474_ = !lean_is_exclusive(v___x_4455_);
if (v_isSharedCheck_4474_ == 0)
{
v___x_4469_ = v___x_4455_;
v_isShared_4470_ = v_isSharedCheck_4474_;
goto v_resetjp_4468_;
}
else
{
lean_inc(v_a_4467_);
lean_dec(v___x_4455_);
v___x_4469_ = lean_box(0);
v_isShared_4470_ = v_isSharedCheck_4474_;
goto v_resetjp_4468_;
}
v_resetjp_4468_:
{
lean_object* v___x_4472_; 
if (v_isShared_4470_ == 0)
{
v___x_4472_ = v___x_4469_;
goto v_reusejp_4471_;
}
else
{
lean_object* v_reuseFailAlloc_4473_; 
v_reuseFailAlloc_4473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4473_, 0, v_a_4467_);
v___x_4472_ = v_reuseFailAlloc_4473_;
goto v_reusejp_4471_;
}
v_reusejp_4471_:
{
return v___x_4472_;
}
}
}
}
else
{
lean_object* v_a_4475_; lean_object* v___x_4477_; uint8_t v_isShared_4478_; uint8_t v_isSharedCheck_4482_; 
lean_dec(v_kind_x3f_4439_);
v_a_4475_ = lean_ctor_get(v___x_4446_, 0);
v_isSharedCheck_4482_ = !lean_is_exclusive(v___x_4446_);
if (v_isSharedCheck_4482_ == 0)
{
v___x_4477_ = v___x_4446_;
v_isShared_4478_ = v_isSharedCheck_4482_;
goto v_resetjp_4476_;
}
else
{
lean_inc(v_a_4475_);
lean_dec(v___x_4446_);
v___x_4477_ = lean_box(0);
v_isShared_4478_ = v_isSharedCheck_4482_;
goto v_resetjp_4476_;
}
v_resetjp_4476_:
{
lean_object* v___x_4480_; 
if (v_isShared_4478_ == 0)
{
v___x_4480_ = v___x_4477_;
goto v_reusejp_4479_;
}
else
{
lean_object* v_reuseFailAlloc_4481_; 
v_reuseFailAlloc_4481_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4481_, 0, v_a_4475_);
v___x_4480_ = v_reuseFailAlloc_4481_;
goto v_reusejp_4479_;
}
v_reusejp_4479_:
{
return v___x_4480_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAuxTheorem___boxed(lean_object* v_type_4483_, lean_object* v_value_4484_, lean_object* v_zetaDelta_4485_, lean_object* v_kind_x3f_4486_, lean_object* v_cache_4487_, lean_object* v_a_4488_, lean_object* v_a_4489_, lean_object* v_a_4490_, lean_object* v_a_4491_, lean_object* v_a_4492_){
_start:
{
uint8_t v_zetaDelta_boxed_4493_; uint8_t v_cache_boxed_4494_; lean_object* v_res_4495_; 
v_zetaDelta_boxed_4493_ = lean_unbox(v_zetaDelta_4485_);
v_cache_boxed_4494_ = lean_unbox(v_cache_4487_);
v_res_4495_ = l_Lean_Meta_mkAuxTheorem(v_type_4483_, v_value_4484_, v_zetaDelta_boxed_4493_, v_kind_x3f_4486_, v_cache_boxed_4494_, v_a_4488_, v_a_4489_, v_a_4490_, v_a_4491_);
lean_dec(v_a_4491_);
lean_dec_ref(v_a_4490_);
lean_dec(v_a_4489_);
lean_dec_ref(v_a_4488_);
return v_res_4495_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_initFn_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4551_; uint8_t v___x_4552_; lean_object* v___x_4553_; lean_object* v___x_4554_; 
v___x_4551_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__10));
v___x_4552_ = 0;
v___x_4553_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2_));
v___x_4554_ = l_Lean_registerTraceClass(v___x_4551_, v___x_4552_, v___x_4553_);
return v___x_4554_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_initFn_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2____boxed(lean_object* v_a_4555_){
_start:
{
lean_object* v_res_4556_; 
v_res_4556_ = l___private_Lean_Meta_Closure_0__Lean_Meta_initFn_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2_();
return v_res_4556_;
}
}
lean_object* runtime_initialize_Lean_Meta_Check(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_AuxLemma(uint8_t builtin);
lean_object* runtime_initialize_Lean_Util_ForEachExpr(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Closure(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
