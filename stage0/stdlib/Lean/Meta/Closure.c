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
uint8_t l_Lean_ExprStructEq_beq(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instInhabitedCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
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
extern lean_object* l_Lean_instEmptyCollectionFVarIdHashSet;
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
lean_object* l_Lean_Meta_check(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_mkLevelMax_x27(lean_object*, lean_object*);
lean_object* l_Lean_simpLevelMax_x27(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkLevelIMax_x27(lean_object*, lean_object*);
lean_object* l_Lean_simpLevelIMax_x27(lean_object*, lean_object*, lean_object*);
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
uint8_t v___x_62_; 
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
goto v___jp_16_;
}
}
else
{
goto v___jp_16_;
}
v___jp_16_:
{
lean_object* v___x_17_; lean_object* v_visitedLevel_18_; lean_object* v___x_19_; lean_object* v___x_20_; lean_object* v___x_21_; 
v___x_17_ = lean_st_ref_get(v_a_10_);
v_visitedLevel_18_ = lean_ctor_get(v___x_17_, 0);
lean_inc_ref(v_visitedLevel_18_);
lean_dec(v___x_17_);
v___x_19_ = ((lean_object*)(l_Lean_Meta_Closure_visitLevel___closed__0));
v___x_20_ = ((lean_object*)(l_Lean_Meta_Closure_visitLevel___closed__1));
lean_inc(v_u_8_);
v___x_21_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v___x_19_, v___x_20_, v_visitedLevel_18_, v_u_8_);
lean_dec_ref(v_visitedLevel_18_);
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
v___x_44_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___x_19_, v___x_20_, v_visitedLevel_29_, v_u_8_, v_a_24_);
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
v___x_47_ = lean_st_ref_set(v_a_10_, v___x_46_);
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
uint8_t v___x_133_; 
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
lean_object* v___x_88_; lean_object* v_visitedExpr_89_; lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; 
v___x_88_ = lean_st_ref_get(v_a_81_);
v_visitedExpr_89_ = lean_ctor_get(v___x_88_, 1);
lean_inc_ref(v_visitedExpr_89_);
lean_dec(v___x_88_);
v___x_90_ = ((lean_object*)(l_Lean_Meta_Closure_visitExpr___closed__0));
v___x_91_ = ((lean_object*)(l_Lean_Meta_Closure_visitExpr___closed__1));
lean_inc_ref(v_e_79_);
v___x_92_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v___x_90_, v___x_91_, v_visitedExpr_89_, v_e_79_);
lean_dec_ref(v_visitedExpr_89_);
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
v___x_115_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___x_90_, v___x_91_, v_visitedExpr_101_, v_e_79_, v_a_95_);
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
v___x_118_ = lean_st_ref_set(v_a_81_, v___x_117_);
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
v___x_180_ = lean_st_ref_set(v_a_152_, v___x_179_);
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
lean_object* v___y_373_; lean_object* v___y_374_; uint8_t v___y_375_; lean_object* v___y_381_; lean_object* v___y_382_; uint8_t v___y_383_; 
switch(lean_obj_tag(v_x_369_))
{
case 0:
{
lean_object* v___x_388_; 
v___x_388_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_388_, 0, v_x_369_);
return v___x_388_;
}
case 1:
{
lean_object* v_a_389_; lean_object* v_a_391_; uint8_t v___x_428_; 
v_a_389_ = lean_ctor_get(v_x_369_, 0);
v___x_428_ = l_Lean_Level_hasMVar(v_a_389_);
if (v___x_428_ == 0)
{
uint8_t v___x_429_; 
v___x_429_ = l_Lean_Level_hasParam(v_a_389_);
if (v___x_429_ == 0)
{
lean_inc(v_a_389_);
v_a_391_ = v_a_389_;
goto v___jp_390_;
}
else
{
goto v___jp_398_;
}
}
else
{
goto v___jp_398_;
}
v___jp_390_:
{
size_t v___x_392_; size_t v___x_393_; uint8_t v___x_394_; 
v___x_392_ = lean_ptr_addr(v_a_389_);
v___x_393_ = lean_ptr_addr(v_a_391_);
v___x_394_ = lean_usize_dec_eq(v___x_392_, v___x_393_);
if (v___x_394_ == 0)
{
lean_object* v___x_395_; lean_object* v___x_396_; 
lean_dec_ref(v_x_369_);
v___x_395_ = l_Lean_Level_succ___override(v_a_391_);
v___x_396_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_396_, 0, v___x_395_);
return v___x_396_;
}
else
{
lean_object* v___x_397_; 
lean_dec(v_a_391_);
v___x_397_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_397_, 0, v_x_369_);
return v___x_397_;
}
}
v___jp_398_:
{
lean_object* v___x_399_; lean_object* v_visitedLevel_400_; lean_object* v___x_401_; 
v___x_399_ = lean_st_ref_get(v_a_370_);
v_visitedLevel_400_ = lean_ctor_get(v___x_399_, 0);
lean_inc_ref(v_visitedLevel_400_);
lean_dec(v___x_399_);
v___x_401_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectLevelAux_spec__1___redArg(v_visitedLevel_400_, v_a_389_);
lean_dec_ref(v_visitedLevel_400_);
if (lean_obj_tag(v___x_401_) == 0)
{
lean_object* v___x_402_; 
lean_inc(v_a_389_);
v___x_402_ = l_Lean_Meta_Closure_collectLevelAux___redArg(v_a_389_, v_a_370_);
if (lean_obj_tag(v___x_402_) == 0)
{
lean_object* v_a_403_; lean_object* v___x_404_; lean_object* v_visitedLevel_405_; lean_object* v_visitedExpr_406_; lean_object* v_levelParams_407_; lean_object* v_nextLevelIdx_408_; lean_object* v_levelArgs_409_; lean_object* v_newLocalDecls_410_; lean_object* v_newLocalDeclsForMVars_411_; lean_object* v_newLetDecls_412_; lean_object* v_nextExprIdx_413_; lean_object* v_exprMVarArgs_414_; lean_object* v_exprFVarArgs_415_; lean_object* v_toProcess_416_; lean_object* v___x_418_; uint8_t v_isShared_419_; uint8_t v_isSharedCheck_425_; 
v_a_403_ = lean_ctor_get(v___x_402_, 0);
lean_inc(v_a_403_);
lean_dec_ref(v___x_402_);
v___x_404_ = lean_st_ref_take(v_a_370_);
v_visitedLevel_405_ = lean_ctor_get(v___x_404_, 0);
v_visitedExpr_406_ = lean_ctor_get(v___x_404_, 1);
v_levelParams_407_ = lean_ctor_get(v___x_404_, 2);
v_nextLevelIdx_408_ = lean_ctor_get(v___x_404_, 3);
v_levelArgs_409_ = lean_ctor_get(v___x_404_, 4);
v_newLocalDecls_410_ = lean_ctor_get(v___x_404_, 5);
v_newLocalDeclsForMVars_411_ = lean_ctor_get(v___x_404_, 6);
v_newLetDecls_412_ = lean_ctor_get(v___x_404_, 7);
v_nextExprIdx_413_ = lean_ctor_get(v___x_404_, 8);
v_exprMVarArgs_414_ = lean_ctor_get(v___x_404_, 9);
v_exprFVarArgs_415_ = lean_ctor_get(v___x_404_, 10);
v_toProcess_416_ = lean_ctor_get(v___x_404_, 11);
v_isSharedCheck_425_ = !lean_is_exclusive(v___x_404_);
if (v_isSharedCheck_425_ == 0)
{
v___x_418_ = v___x_404_;
v_isShared_419_ = v_isSharedCheck_425_;
goto v_resetjp_417_;
}
else
{
lean_inc(v_toProcess_416_);
lean_inc(v_exprFVarArgs_415_);
lean_inc(v_exprMVarArgs_414_);
lean_inc(v_nextExprIdx_413_);
lean_inc(v_newLetDecls_412_);
lean_inc(v_newLocalDeclsForMVars_411_);
lean_inc(v_newLocalDecls_410_);
lean_inc(v_levelArgs_409_);
lean_inc(v_nextLevelIdx_408_);
lean_inc(v_levelParams_407_);
lean_inc(v_visitedExpr_406_);
lean_inc(v_visitedLevel_405_);
lean_dec(v___x_404_);
v___x_418_ = lean_box(0);
v_isShared_419_ = v_isSharedCheck_425_;
goto v_resetjp_417_;
}
v_resetjp_417_:
{
lean_object* v___x_420_; lean_object* v___x_422_; 
lean_inc(v_a_403_);
lean_inc(v_a_389_);
v___x_420_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2___redArg(v_visitedLevel_405_, v_a_389_, v_a_403_);
if (v_isShared_419_ == 0)
{
lean_ctor_set(v___x_418_, 0, v___x_420_);
v___x_422_ = v___x_418_;
goto v_reusejp_421_;
}
else
{
lean_object* v_reuseFailAlloc_424_; 
v_reuseFailAlloc_424_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_424_, 0, v___x_420_);
lean_ctor_set(v_reuseFailAlloc_424_, 1, v_visitedExpr_406_);
lean_ctor_set(v_reuseFailAlloc_424_, 2, v_levelParams_407_);
lean_ctor_set(v_reuseFailAlloc_424_, 3, v_nextLevelIdx_408_);
lean_ctor_set(v_reuseFailAlloc_424_, 4, v_levelArgs_409_);
lean_ctor_set(v_reuseFailAlloc_424_, 5, v_newLocalDecls_410_);
lean_ctor_set(v_reuseFailAlloc_424_, 6, v_newLocalDeclsForMVars_411_);
lean_ctor_set(v_reuseFailAlloc_424_, 7, v_newLetDecls_412_);
lean_ctor_set(v_reuseFailAlloc_424_, 8, v_nextExprIdx_413_);
lean_ctor_set(v_reuseFailAlloc_424_, 9, v_exprMVarArgs_414_);
lean_ctor_set(v_reuseFailAlloc_424_, 10, v_exprFVarArgs_415_);
lean_ctor_set(v_reuseFailAlloc_424_, 11, v_toProcess_416_);
v___x_422_ = v_reuseFailAlloc_424_;
goto v_reusejp_421_;
}
v_reusejp_421_:
{
lean_object* v___x_423_; 
v___x_423_ = lean_st_ref_set(v_a_370_, v___x_422_);
v_a_391_ = v_a_403_;
goto v___jp_390_;
}
}
}
else
{
if (lean_obj_tag(v___x_402_) == 0)
{
lean_object* v_a_426_; 
v_a_426_ = lean_ctor_get(v___x_402_, 0);
lean_inc(v_a_426_);
lean_dec_ref(v___x_402_);
v_a_391_ = v_a_426_;
goto v___jp_390_;
}
else
{
lean_dec_ref(v_x_369_);
return v___x_402_;
}
}
}
else
{
lean_object* v_val_427_; 
v_val_427_ = lean_ctor_get(v___x_401_, 0);
lean_inc(v_val_427_);
lean_dec_ref(v___x_401_);
v_a_391_ = v_val_427_;
goto v___jp_390_;
}
}
}
case 2:
{
lean_object* v_a_430_; lean_object* v_a_431_; lean_object* v___y_433_; lean_object* v_a_434_; lean_object* v___y_442_; lean_object* v_a_473_; uint8_t v___x_506_; 
v_a_430_ = lean_ctor_get(v_x_369_, 0);
v_a_431_ = lean_ctor_get(v_x_369_, 1);
v___x_506_ = l_Lean_Level_hasMVar(v_a_430_);
if (v___x_506_ == 0)
{
uint8_t v___x_507_; 
v___x_507_ = l_Lean_Level_hasParam(v_a_430_);
if (v___x_507_ == 0)
{
lean_inc(v_a_430_);
v_a_473_ = v_a_430_;
goto v___jp_472_;
}
else
{
goto v___jp_476_;
}
}
else
{
goto v___jp_476_;
}
v___jp_432_:
{
size_t v___x_435_; size_t v___x_436_; uint8_t v___x_437_; 
v___x_435_ = lean_ptr_addr(v_a_430_);
v___x_436_ = lean_ptr_addr(v___y_433_);
v___x_437_ = lean_usize_dec_eq(v___x_435_, v___x_436_);
if (v___x_437_ == 0)
{
v___y_373_ = v___y_433_;
v___y_374_ = v_a_434_;
v___y_375_ = v___x_437_;
goto v___jp_372_;
}
else
{
size_t v___x_438_; size_t v___x_439_; uint8_t v___x_440_; 
v___x_438_ = lean_ptr_addr(v_a_431_);
v___x_439_ = lean_ptr_addr(v_a_434_);
v___x_440_ = lean_usize_dec_eq(v___x_438_, v___x_439_);
v___y_373_ = v___y_433_;
v___y_374_ = v_a_434_;
v___y_375_ = v___x_440_;
goto v___jp_372_;
}
}
v___jp_441_:
{
lean_object* v___x_443_; lean_object* v_visitedLevel_444_; lean_object* v___x_445_; 
v___x_443_ = lean_st_ref_get(v_a_370_);
v_visitedLevel_444_ = lean_ctor_get(v___x_443_, 0);
lean_inc_ref(v_visitedLevel_444_);
lean_dec(v___x_443_);
v___x_445_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectLevelAux_spec__1___redArg(v_visitedLevel_444_, v_a_431_);
lean_dec_ref(v_visitedLevel_444_);
if (lean_obj_tag(v___x_445_) == 0)
{
lean_object* v___x_446_; 
lean_inc(v_a_431_);
v___x_446_ = l_Lean_Meta_Closure_collectLevelAux___redArg(v_a_431_, v_a_370_);
if (lean_obj_tag(v___x_446_) == 0)
{
lean_object* v_a_447_; lean_object* v___x_448_; lean_object* v_visitedLevel_449_; lean_object* v_visitedExpr_450_; lean_object* v_levelParams_451_; lean_object* v_nextLevelIdx_452_; lean_object* v_levelArgs_453_; lean_object* v_newLocalDecls_454_; lean_object* v_newLocalDeclsForMVars_455_; lean_object* v_newLetDecls_456_; lean_object* v_nextExprIdx_457_; lean_object* v_exprMVarArgs_458_; lean_object* v_exprFVarArgs_459_; lean_object* v_toProcess_460_; lean_object* v___x_462_; uint8_t v_isShared_463_; uint8_t v_isSharedCheck_469_; 
v_a_447_ = lean_ctor_get(v___x_446_, 0);
lean_inc(v_a_447_);
lean_dec_ref(v___x_446_);
v___x_448_ = lean_st_ref_take(v_a_370_);
v_visitedLevel_449_ = lean_ctor_get(v___x_448_, 0);
v_visitedExpr_450_ = lean_ctor_get(v___x_448_, 1);
v_levelParams_451_ = lean_ctor_get(v___x_448_, 2);
v_nextLevelIdx_452_ = lean_ctor_get(v___x_448_, 3);
v_levelArgs_453_ = lean_ctor_get(v___x_448_, 4);
v_newLocalDecls_454_ = lean_ctor_get(v___x_448_, 5);
v_newLocalDeclsForMVars_455_ = lean_ctor_get(v___x_448_, 6);
v_newLetDecls_456_ = lean_ctor_get(v___x_448_, 7);
v_nextExprIdx_457_ = lean_ctor_get(v___x_448_, 8);
v_exprMVarArgs_458_ = lean_ctor_get(v___x_448_, 9);
v_exprFVarArgs_459_ = lean_ctor_get(v___x_448_, 10);
v_toProcess_460_ = lean_ctor_get(v___x_448_, 11);
v_isSharedCheck_469_ = !lean_is_exclusive(v___x_448_);
if (v_isSharedCheck_469_ == 0)
{
v___x_462_ = v___x_448_;
v_isShared_463_ = v_isSharedCheck_469_;
goto v_resetjp_461_;
}
else
{
lean_inc(v_toProcess_460_);
lean_inc(v_exprFVarArgs_459_);
lean_inc(v_exprMVarArgs_458_);
lean_inc(v_nextExprIdx_457_);
lean_inc(v_newLetDecls_456_);
lean_inc(v_newLocalDeclsForMVars_455_);
lean_inc(v_newLocalDecls_454_);
lean_inc(v_levelArgs_453_);
lean_inc(v_nextLevelIdx_452_);
lean_inc(v_levelParams_451_);
lean_inc(v_visitedExpr_450_);
lean_inc(v_visitedLevel_449_);
lean_dec(v___x_448_);
v___x_462_ = lean_box(0);
v_isShared_463_ = v_isSharedCheck_469_;
goto v_resetjp_461_;
}
v_resetjp_461_:
{
lean_object* v___x_464_; lean_object* v___x_466_; 
lean_inc(v_a_447_);
lean_inc(v_a_431_);
v___x_464_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2___redArg(v_visitedLevel_449_, v_a_431_, v_a_447_);
if (v_isShared_463_ == 0)
{
lean_ctor_set(v___x_462_, 0, v___x_464_);
v___x_466_ = v___x_462_;
goto v_reusejp_465_;
}
else
{
lean_object* v_reuseFailAlloc_468_; 
v_reuseFailAlloc_468_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_468_, 0, v___x_464_);
lean_ctor_set(v_reuseFailAlloc_468_, 1, v_visitedExpr_450_);
lean_ctor_set(v_reuseFailAlloc_468_, 2, v_levelParams_451_);
lean_ctor_set(v_reuseFailAlloc_468_, 3, v_nextLevelIdx_452_);
lean_ctor_set(v_reuseFailAlloc_468_, 4, v_levelArgs_453_);
lean_ctor_set(v_reuseFailAlloc_468_, 5, v_newLocalDecls_454_);
lean_ctor_set(v_reuseFailAlloc_468_, 6, v_newLocalDeclsForMVars_455_);
lean_ctor_set(v_reuseFailAlloc_468_, 7, v_newLetDecls_456_);
lean_ctor_set(v_reuseFailAlloc_468_, 8, v_nextExprIdx_457_);
lean_ctor_set(v_reuseFailAlloc_468_, 9, v_exprMVarArgs_458_);
lean_ctor_set(v_reuseFailAlloc_468_, 10, v_exprFVarArgs_459_);
lean_ctor_set(v_reuseFailAlloc_468_, 11, v_toProcess_460_);
v___x_466_ = v_reuseFailAlloc_468_;
goto v_reusejp_465_;
}
v_reusejp_465_:
{
lean_object* v___x_467_; 
v___x_467_ = lean_st_ref_set(v_a_370_, v___x_466_);
v___y_433_ = v___y_442_;
v_a_434_ = v_a_447_;
goto v___jp_432_;
}
}
}
else
{
if (lean_obj_tag(v___x_446_) == 0)
{
lean_object* v_a_470_; 
v_a_470_ = lean_ctor_get(v___x_446_, 0);
lean_inc(v_a_470_);
lean_dec_ref(v___x_446_);
v___y_433_ = v___y_442_;
v_a_434_ = v_a_470_;
goto v___jp_432_;
}
else
{
lean_dec(v___y_442_);
lean_dec_ref(v_x_369_);
return v___x_446_;
}
}
}
else
{
lean_object* v_val_471_; 
v_val_471_ = lean_ctor_get(v___x_445_, 0);
lean_inc(v_val_471_);
lean_dec_ref(v___x_445_);
v___y_433_ = v___y_442_;
v_a_434_ = v_val_471_;
goto v___jp_432_;
}
}
v___jp_472_:
{
uint8_t v___x_474_; 
v___x_474_ = l_Lean_Level_hasMVar(v_a_431_);
if (v___x_474_ == 0)
{
uint8_t v___x_475_; 
v___x_475_ = l_Lean_Level_hasParam(v_a_431_);
if (v___x_475_ == 0)
{
lean_inc(v_a_431_);
v___y_433_ = v_a_473_;
v_a_434_ = v_a_431_;
goto v___jp_432_;
}
else
{
v___y_442_ = v_a_473_;
goto v___jp_441_;
}
}
else
{
v___y_442_ = v_a_473_;
goto v___jp_441_;
}
}
v___jp_476_:
{
lean_object* v___x_477_; lean_object* v_visitedLevel_478_; lean_object* v___x_479_; 
v___x_477_ = lean_st_ref_get(v_a_370_);
v_visitedLevel_478_ = lean_ctor_get(v___x_477_, 0);
lean_inc_ref(v_visitedLevel_478_);
lean_dec(v___x_477_);
v___x_479_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectLevelAux_spec__1___redArg(v_visitedLevel_478_, v_a_430_);
lean_dec_ref(v_visitedLevel_478_);
if (lean_obj_tag(v___x_479_) == 0)
{
lean_object* v___x_480_; 
lean_inc(v_a_430_);
v___x_480_ = l_Lean_Meta_Closure_collectLevelAux___redArg(v_a_430_, v_a_370_);
if (lean_obj_tag(v___x_480_) == 0)
{
lean_object* v_a_481_; lean_object* v___x_482_; lean_object* v_visitedLevel_483_; lean_object* v_visitedExpr_484_; lean_object* v_levelParams_485_; lean_object* v_nextLevelIdx_486_; lean_object* v_levelArgs_487_; lean_object* v_newLocalDecls_488_; lean_object* v_newLocalDeclsForMVars_489_; lean_object* v_newLetDecls_490_; lean_object* v_nextExprIdx_491_; lean_object* v_exprMVarArgs_492_; lean_object* v_exprFVarArgs_493_; lean_object* v_toProcess_494_; lean_object* v___x_496_; uint8_t v_isShared_497_; uint8_t v_isSharedCheck_503_; 
v_a_481_ = lean_ctor_get(v___x_480_, 0);
lean_inc(v_a_481_);
lean_dec_ref(v___x_480_);
v___x_482_ = lean_st_ref_take(v_a_370_);
v_visitedLevel_483_ = lean_ctor_get(v___x_482_, 0);
v_visitedExpr_484_ = lean_ctor_get(v___x_482_, 1);
v_levelParams_485_ = lean_ctor_get(v___x_482_, 2);
v_nextLevelIdx_486_ = lean_ctor_get(v___x_482_, 3);
v_levelArgs_487_ = lean_ctor_get(v___x_482_, 4);
v_newLocalDecls_488_ = lean_ctor_get(v___x_482_, 5);
v_newLocalDeclsForMVars_489_ = lean_ctor_get(v___x_482_, 6);
v_newLetDecls_490_ = lean_ctor_get(v___x_482_, 7);
v_nextExprIdx_491_ = lean_ctor_get(v___x_482_, 8);
v_exprMVarArgs_492_ = lean_ctor_get(v___x_482_, 9);
v_exprFVarArgs_493_ = lean_ctor_get(v___x_482_, 10);
v_toProcess_494_ = lean_ctor_get(v___x_482_, 11);
v_isSharedCheck_503_ = !lean_is_exclusive(v___x_482_);
if (v_isSharedCheck_503_ == 0)
{
v___x_496_ = v___x_482_;
v_isShared_497_ = v_isSharedCheck_503_;
goto v_resetjp_495_;
}
else
{
lean_inc(v_toProcess_494_);
lean_inc(v_exprFVarArgs_493_);
lean_inc(v_exprMVarArgs_492_);
lean_inc(v_nextExprIdx_491_);
lean_inc(v_newLetDecls_490_);
lean_inc(v_newLocalDeclsForMVars_489_);
lean_inc(v_newLocalDecls_488_);
lean_inc(v_levelArgs_487_);
lean_inc(v_nextLevelIdx_486_);
lean_inc(v_levelParams_485_);
lean_inc(v_visitedExpr_484_);
lean_inc(v_visitedLevel_483_);
lean_dec(v___x_482_);
v___x_496_ = lean_box(0);
v_isShared_497_ = v_isSharedCheck_503_;
goto v_resetjp_495_;
}
v_resetjp_495_:
{
lean_object* v___x_498_; lean_object* v___x_500_; 
lean_inc(v_a_481_);
lean_inc(v_a_430_);
v___x_498_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2___redArg(v_visitedLevel_483_, v_a_430_, v_a_481_);
if (v_isShared_497_ == 0)
{
lean_ctor_set(v___x_496_, 0, v___x_498_);
v___x_500_ = v___x_496_;
goto v_reusejp_499_;
}
else
{
lean_object* v_reuseFailAlloc_502_; 
v_reuseFailAlloc_502_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_502_, 0, v___x_498_);
lean_ctor_set(v_reuseFailAlloc_502_, 1, v_visitedExpr_484_);
lean_ctor_set(v_reuseFailAlloc_502_, 2, v_levelParams_485_);
lean_ctor_set(v_reuseFailAlloc_502_, 3, v_nextLevelIdx_486_);
lean_ctor_set(v_reuseFailAlloc_502_, 4, v_levelArgs_487_);
lean_ctor_set(v_reuseFailAlloc_502_, 5, v_newLocalDecls_488_);
lean_ctor_set(v_reuseFailAlloc_502_, 6, v_newLocalDeclsForMVars_489_);
lean_ctor_set(v_reuseFailAlloc_502_, 7, v_newLetDecls_490_);
lean_ctor_set(v_reuseFailAlloc_502_, 8, v_nextExprIdx_491_);
lean_ctor_set(v_reuseFailAlloc_502_, 9, v_exprMVarArgs_492_);
lean_ctor_set(v_reuseFailAlloc_502_, 10, v_exprFVarArgs_493_);
lean_ctor_set(v_reuseFailAlloc_502_, 11, v_toProcess_494_);
v___x_500_ = v_reuseFailAlloc_502_;
goto v_reusejp_499_;
}
v_reusejp_499_:
{
lean_object* v___x_501_; 
v___x_501_ = lean_st_ref_set(v_a_370_, v___x_500_);
v_a_473_ = v_a_481_;
goto v___jp_472_;
}
}
}
else
{
if (lean_obj_tag(v___x_480_) == 0)
{
lean_object* v_a_504_; 
v_a_504_ = lean_ctor_get(v___x_480_, 0);
lean_inc(v_a_504_);
lean_dec_ref(v___x_480_);
v_a_473_ = v_a_504_;
goto v___jp_472_;
}
else
{
lean_dec_ref(v_x_369_);
return v___x_480_;
}
}
}
else
{
lean_object* v_val_505_; 
v_val_505_ = lean_ctor_get(v___x_479_, 0);
lean_inc(v_val_505_);
lean_dec_ref(v___x_479_);
v_a_473_ = v_val_505_;
goto v___jp_472_;
}
}
}
case 3:
{
lean_object* v_a_508_; lean_object* v_a_509_; lean_object* v___y_511_; lean_object* v_a_512_; lean_object* v___y_520_; lean_object* v_a_551_; uint8_t v___x_584_; 
v_a_508_ = lean_ctor_get(v_x_369_, 0);
v_a_509_ = lean_ctor_get(v_x_369_, 1);
v___x_584_ = l_Lean_Level_hasMVar(v_a_508_);
if (v___x_584_ == 0)
{
uint8_t v___x_585_; 
v___x_585_ = l_Lean_Level_hasParam(v_a_508_);
if (v___x_585_ == 0)
{
lean_inc(v_a_508_);
v_a_551_ = v_a_508_;
goto v___jp_550_;
}
else
{
goto v___jp_554_;
}
}
else
{
goto v___jp_554_;
}
v___jp_510_:
{
size_t v___x_513_; size_t v___x_514_; uint8_t v___x_515_; 
v___x_513_ = lean_ptr_addr(v_a_508_);
v___x_514_ = lean_ptr_addr(v___y_511_);
v___x_515_ = lean_usize_dec_eq(v___x_513_, v___x_514_);
if (v___x_515_ == 0)
{
v___y_381_ = v_a_512_;
v___y_382_ = v___y_511_;
v___y_383_ = v___x_515_;
goto v___jp_380_;
}
else
{
size_t v___x_516_; size_t v___x_517_; uint8_t v___x_518_; 
v___x_516_ = lean_ptr_addr(v_a_509_);
v___x_517_ = lean_ptr_addr(v_a_512_);
v___x_518_ = lean_usize_dec_eq(v___x_516_, v___x_517_);
v___y_381_ = v_a_512_;
v___y_382_ = v___y_511_;
v___y_383_ = v___x_518_;
goto v___jp_380_;
}
}
v___jp_519_:
{
lean_object* v___x_521_; lean_object* v_visitedLevel_522_; lean_object* v___x_523_; 
v___x_521_ = lean_st_ref_get(v_a_370_);
v_visitedLevel_522_ = lean_ctor_get(v___x_521_, 0);
lean_inc_ref(v_visitedLevel_522_);
lean_dec(v___x_521_);
v___x_523_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectLevelAux_spec__1___redArg(v_visitedLevel_522_, v_a_509_);
lean_dec_ref(v_visitedLevel_522_);
if (lean_obj_tag(v___x_523_) == 0)
{
lean_object* v___x_524_; 
lean_inc(v_a_509_);
v___x_524_ = l_Lean_Meta_Closure_collectLevelAux___redArg(v_a_509_, v_a_370_);
if (lean_obj_tag(v___x_524_) == 0)
{
lean_object* v_a_525_; lean_object* v___x_526_; lean_object* v_visitedLevel_527_; lean_object* v_visitedExpr_528_; lean_object* v_levelParams_529_; lean_object* v_nextLevelIdx_530_; lean_object* v_levelArgs_531_; lean_object* v_newLocalDecls_532_; lean_object* v_newLocalDeclsForMVars_533_; lean_object* v_newLetDecls_534_; lean_object* v_nextExprIdx_535_; lean_object* v_exprMVarArgs_536_; lean_object* v_exprFVarArgs_537_; lean_object* v_toProcess_538_; lean_object* v___x_540_; uint8_t v_isShared_541_; uint8_t v_isSharedCheck_547_; 
v_a_525_ = lean_ctor_get(v___x_524_, 0);
lean_inc(v_a_525_);
lean_dec_ref(v___x_524_);
v___x_526_ = lean_st_ref_take(v_a_370_);
v_visitedLevel_527_ = lean_ctor_get(v___x_526_, 0);
v_visitedExpr_528_ = lean_ctor_get(v___x_526_, 1);
v_levelParams_529_ = lean_ctor_get(v___x_526_, 2);
v_nextLevelIdx_530_ = lean_ctor_get(v___x_526_, 3);
v_levelArgs_531_ = lean_ctor_get(v___x_526_, 4);
v_newLocalDecls_532_ = lean_ctor_get(v___x_526_, 5);
v_newLocalDeclsForMVars_533_ = lean_ctor_get(v___x_526_, 6);
v_newLetDecls_534_ = lean_ctor_get(v___x_526_, 7);
v_nextExprIdx_535_ = lean_ctor_get(v___x_526_, 8);
v_exprMVarArgs_536_ = lean_ctor_get(v___x_526_, 9);
v_exprFVarArgs_537_ = lean_ctor_get(v___x_526_, 10);
v_toProcess_538_ = lean_ctor_get(v___x_526_, 11);
v_isSharedCheck_547_ = !lean_is_exclusive(v___x_526_);
if (v_isSharedCheck_547_ == 0)
{
v___x_540_ = v___x_526_;
v_isShared_541_ = v_isSharedCheck_547_;
goto v_resetjp_539_;
}
else
{
lean_inc(v_toProcess_538_);
lean_inc(v_exprFVarArgs_537_);
lean_inc(v_exprMVarArgs_536_);
lean_inc(v_nextExprIdx_535_);
lean_inc(v_newLetDecls_534_);
lean_inc(v_newLocalDeclsForMVars_533_);
lean_inc(v_newLocalDecls_532_);
lean_inc(v_levelArgs_531_);
lean_inc(v_nextLevelIdx_530_);
lean_inc(v_levelParams_529_);
lean_inc(v_visitedExpr_528_);
lean_inc(v_visitedLevel_527_);
lean_dec(v___x_526_);
v___x_540_ = lean_box(0);
v_isShared_541_ = v_isSharedCheck_547_;
goto v_resetjp_539_;
}
v_resetjp_539_:
{
lean_object* v___x_542_; lean_object* v___x_544_; 
lean_inc(v_a_525_);
lean_inc(v_a_509_);
v___x_542_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2___redArg(v_visitedLevel_527_, v_a_509_, v_a_525_);
if (v_isShared_541_ == 0)
{
lean_ctor_set(v___x_540_, 0, v___x_542_);
v___x_544_ = v___x_540_;
goto v_reusejp_543_;
}
else
{
lean_object* v_reuseFailAlloc_546_; 
v_reuseFailAlloc_546_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_546_, 0, v___x_542_);
lean_ctor_set(v_reuseFailAlloc_546_, 1, v_visitedExpr_528_);
lean_ctor_set(v_reuseFailAlloc_546_, 2, v_levelParams_529_);
lean_ctor_set(v_reuseFailAlloc_546_, 3, v_nextLevelIdx_530_);
lean_ctor_set(v_reuseFailAlloc_546_, 4, v_levelArgs_531_);
lean_ctor_set(v_reuseFailAlloc_546_, 5, v_newLocalDecls_532_);
lean_ctor_set(v_reuseFailAlloc_546_, 6, v_newLocalDeclsForMVars_533_);
lean_ctor_set(v_reuseFailAlloc_546_, 7, v_newLetDecls_534_);
lean_ctor_set(v_reuseFailAlloc_546_, 8, v_nextExprIdx_535_);
lean_ctor_set(v_reuseFailAlloc_546_, 9, v_exprMVarArgs_536_);
lean_ctor_set(v_reuseFailAlloc_546_, 10, v_exprFVarArgs_537_);
lean_ctor_set(v_reuseFailAlloc_546_, 11, v_toProcess_538_);
v___x_544_ = v_reuseFailAlloc_546_;
goto v_reusejp_543_;
}
v_reusejp_543_:
{
lean_object* v___x_545_; 
v___x_545_ = lean_st_ref_set(v_a_370_, v___x_544_);
v___y_511_ = v___y_520_;
v_a_512_ = v_a_525_;
goto v___jp_510_;
}
}
}
else
{
if (lean_obj_tag(v___x_524_) == 0)
{
lean_object* v_a_548_; 
v_a_548_ = lean_ctor_get(v___x_524_, 0);
lean_inc(v_a_548_);
lean_dec_ref(v___x_524_);
v___y_511_ = v___y_520_;
v_a_512_ = v_a_548_;
goto v___jp_510_;
}
else
{
lean_dec(v___y_520_);
lean_dec_ref(v_x_369_);
return v___x_524_;
}
}
}
else
{
lean_object* v_val_549_; 
v_val_549_ = lean_ctor_get(v___x_523_, 0);
lean_inc(v_val_549_);
lean_dec_ref(v___x_523_);
v___y_511_ = v___y_520_;
v_a_512_ = v_val_549_;
goto v___jp_510_;
}
}
v___jp_550_:
{
uint8_t v___x_552_; 
v___x_552_ = l_Lean_Level_hasMVar(v_a_509_);
if (v___x_552_ == 0)
{
uint8_t v___x_553_; 
v___x_553_ = l_Lean_Level_hasParam(v_a_509_);
if (v___x_553_ == 0)
{
lean_inc(v_a_509_);
v___y_511_ = v_a_551_;
v_a_512_ = v_a_509_;
goto v___jp_510_;
}
else
{
v___y_520_ = v_a_551_;
goto v___jp_519_;
}
}
else
{
v___y_520_ = v_a_551_;
goto v___jp_519_;
}
}
v___jp_554_:
{
lean_object* v___x_555_; lean_object* v_visitedLevel_556_; lean_object* v___x_557_; 
v___x_555_ = lean_st_ref_get(v_a_370_);
v_visitedLevel_556_ = lean_ctor_get(v___x_555_, 0);
lean_inc_ref(v_visitedLevel_556_);
lean_dec(v___x_555_);
v___x_557_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectLevelAux_spec__1___redArg(v_visitedLevel_556_, v_a_508_);
lean_dec_ref(v_visitedLevel_556_);
if (lean_obj_tag(v___x_557_) == 0)
{
lean_object* v___x_558_; 
lean_inc(v_a_508_);
v___x_558_ = l_Lean_Meta_Closure_collectLevelAux___redArg(v_a_508_, v_a_370_);
if (lean_obj_tag(v___x_558_) == 0)
{
lean_object* v_a_559_; lean_object* v___x_560_; lean_object* v_visitedLevel_561_; lean_object* v_visitedExpr_562_; lean_object* v_levelParams_563_; lean_object* v_nextLevelIdx_564_; lean_object* v_levelArgs_565_; lean_object* v_newLocalDecls_566_; lean_object* v_newLocalDeclsForMVars_567_; lean_object* v_newLetDecls_568_; lean_object* v_nextExprIdx_569_; lean_object* v_exprMVarArgs_570_; lean_object* v_exprFVarArgs_571_; lean_object* v_toProcess_572_; lean_object* v___x_574_; uint8_t v_isShared_575_; uint8_t v_isSharedCheck_581_; 
v_a_559_ = lean_ctor_get(v___x_558_, 0);
lean_inc(v_a_559_);
lean_dec_ref(v___x_558_);
v___x_560_ = lean_st_ref_take(v_a_370_);
v_visitedLevel_561_ = lean_ctor_get(v___x_560_, 0);
v_visitedExpr_562_ = lean_ctor_get(v___x_560_, 1);
v_levelParams_563_ = lean_ctor_get(v___x_560_, 2);
v_nextLevelIdx_564_ = lean_ctor_get(v___x_560_, 3);
v_levelArgs_565_ = lean_ctor_get(v___x_560_, 4);
v_newLocalDecls_566_ = lean_ctor_get(v___x_560_, 5);
v_newLocalDeclsForMVars_567_ = lean_ctor_get(v___x_560_, 6);
v_newLetDecls_568_ = lean_ctor_get(v___x_560_, 7);
v_nextExprIdx_569_ = lean_ctor_get(v___x_560_, 8);
v_exprMVarArgs_570_ = lean_ctor_get(v___x_560_, 9);
v_exprFVarArgs_571_ = lean_ctor_get(v___x_560_, 10);
v_toProcess_572_ = lean_ctor_get(v___x_560_, 11);
v_isSharedCheck_581_ = !lean_is_exclusive(v___x_560_);
if (v_isSharedCheck_581_ == 0)
{
v___x_574_ = v___x_560_;
v_isShared_575_ = v_isSharedCheck_581_;
goto v_resetjp_573_;
}
else
{
lean_inc(v_toProcess_572_);
lean_inc(v_exprFVarArgs_571_);
lean_inc(v_exprMVarArgs_570_);
lean_inc(v_nextExprIdx_569_);
lean_inc(v_newLetDecls_568_);
lean_inc(v_newLocalDeclsForMVars_567_);
lean_inc(v_newLocalDecls_566_);
lean_inc(v_levelArgs_565_);
lean_inc(v_nextLevelIdx_564_);
lean_inc(v_levelParams_563_);
lean_inc(v_visitedExpr_562_);
lean_inc(v_visitedLevel_561_);
lean_dec(v___x_560_);
v___x_574_ = lean_box(0);
v_isShared_575_ = v_isSharedCheck_581_;
goto v_resetjp_573_;
}
v_resetjp_573_:
{
lean_object* v___x_576_; lean_object* v___x_578_; 
lean_inc(v_a_559_);
lean_inc(v_a_508_);
v___x_576_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2___redArg(v_visitedLevel_561_, v_a_508_, v_a_559_);
if (v_isShared_575_ == 0)
{
lean_ctor_set(v___x_574_, 0, v___x_576_);
v___x_578_ = v___x_574_;
goto v_reusejp_577_;
}
else
{
lean_object* v_reuseFailAlloc_580_; 
v_reuseFailAlloc_580_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_580_, 0, v___x_576_);
lean_ctor_set(v_reuseFailAlloc_580_, 1, v_visitedExpr_562_);
lean_ctor_set(v_reuseFailAlloc_580_, 2, v_levelParams_563_);
lean_ctor_set(v_reuseFailAlloc_580_, 3, v_nextLevelIdx_564_);
lean_ctor_set(v_reuseFailAlloc_580_, 4, v_levelArgs_565_);
lean_ctor_set(v_reuseFailAlloc_580_, 5, v_newLocalDecls_566_);
lean_ctor_set(v_reuseFailAlloc_580_, 6, v_newLocalDeclsForMVars_567_);
lean_ctor_set(v_reuseFailAlloc_580_, 7, v_newLetDecls_568_);
lean_ctor_set(v_reuseFailAlloc_580_, 8, v_nextExprIdx_569_);
lean_ctor_set(v_reuseFailAlloc_580_, 9, v_exprMVarArgs_570_);
lean_ctor_set(v_reuseFailAlloc_580_, 10, v_exprFVarArgs_571_);
lean_ctor_set(v_reuseFailAlloc_580_, 11, v_toProcess_572_);
v___x_578_ = v_reuseFailAlloc_580_;
goto v_reusejp_577_;
}
v_reusejp_577_:
{
lean_object* v___x_579_; 
v___x_579_ = lean_st_ref_set(v_a_370_, v___x_578_);
v_a_551_ = v_a_559_;
goto v___jp_550_;
}
}
}
else
{
if (lean_obj_tag(v___x_558_) == 0)
{
lean_object* v_a_582_; 
v_a_582_ = lean_ctor_get(v___x_558_, 0);
lean_inc(v_a_582_);
lean_dec_ref(v___x_558_);
v_a_551_ = v_a_582_;
goto v___jp_550_;
}
else
{
lean_dec_ref(v_x_369_);
return v___x_558_;
}
}
}
else
{
lean_object* v_val_583_; 
v_val_583_ = lean_ctor_get(v___x_557_, 0);
lean_inc(v_val_583_);
lean_dec_ref(v___x_557_);
v_a_551_ = v_val_583_;
goto v___jp_550_;
}
}
}
default: 
{
lean_object* v___x_586_; 
v___x_586_ = l_Lean_Meta_Closure_mkNewLevelParam___redArg(v_x_369_, v_a_370_);
return v___x_586_;
}
}
v___jp_372_:
{
if (v___y_375_ == 0)
{
lean_object* v___x_376_; lean_object* v___x_377_; 
lean_dec(v_x_369_);
v___x_376_ = l_Lean_mkLevelMax_x27(v___y_373_, v___y_374_);
v___x_377_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_377_, 0, v___x_376_);
return v___x_377_;
}
else
{
lean_object* v___x_378_; lean_object* v___x_379_; 
v___x_378_ = l_Lean_simpLevelMax_x27(v___y_373_, v___y_374_, v_x_369_);
lean_dec(v_x_369_);
lean_dec(v___y_374_);
lean_dec(v___y_373_);
v___x_379_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_379_, 0, v___x_378_);
return v___x_379_;
}
}
v___jp_380_:
{
if (v___y_383_ == 0)
{
lean_object* v___x_384_; lean_object* v___x_385_; 
lean_dec(v_x_369_);
v___x_384_ = l_Lean_mkLevelIMax_x27(v___y_382_, v___y_381_);
v___x_385_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_385_, 0, v___x_384_);
return v___x_385_;
}
else
{
lean_object* v___x_386_; lean_object* v___x_387_; 
v___x_386_ = l_Lean_simpLevelIMax_x27(v___y_382_, v___y_381_, v_x_369_);
lean_dec(v_x_369_);
v___x_387_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_387_, 0, v___x_386_);
return v___x_387_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectLevelAux___redArg___boxed(lean_object* v_x_587_, lean_object* v_a_588_, lean_object* v_a_589_){
_start:
{
lean_object* v_res_590_; 
v_res_590_ = l_Lean_Meta_Closure_collectLevelAux___redArg(v_x_587_, v_a_588_);
lean_dec(v_a_588_);
return v_res_590_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectLevelAux(lean_object* v_x_591_, uint8_t v_a_592_, lean_object* v_a_593_, lean_object* v_a_594_, lean_object* v_a_595_, lean_object* v_a_596_, lean_object* v_a_597_){
_start:
{
lean_object* v___x_599_; 
v___x_599_ = l_Lean_Meta_Closure_collectLevelAux___redArg(v_x_591_, v_a_593_);
return v___x_599_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectLevelAux___boxed(lean_object* v_x_600_, lean_object* v_a_601_, lean_object* v_a_602_, lean_object* v_a_603_, lean_object* v_a_604_, lean_object* v_a_605_, lean_object* v_a_606_, lean_object* v_a_607_){
_start:
{
uint8_t v_a_boxed_608_; lean_object* v_res_609_; 
v_a_boxed_608_ = lean_unbox(v_a_601_);
v_res_609_ = l_Lean_Meta_Closure_collectLevelAux(v_x_600_, v_a_boxed_608_, v_a_602_, v_a_603_, v_a_604_, v_a_605_, v_a_606_);
lean_dec(v_a_606_);
lean_dec_ref(v_a_605_);
lean_dec(v_a_604_);
lean_dec_ref(v_a_603_);
lean_dec(v_a_602_);
return v_res_609_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectLevelAux_spec__1(lean_object* v_00_u03b2_610_, lean_object* v_m_611_, lean_object* v_a_612_){
_start:
{
lean_object* v___x_613_; 
v___x_613_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectLevelAux_spec__1___redArg(v_m_611_, v_a_612_);
return v___x_613_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectLevelAux_spec__1___boxed(lean_object* v_00_u03b2_614_, lean_object* v_m_615_, lean_object* v_a_616_){
_start:
{
lean_object* v_res_617_; 
v_res_617_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectLevelAux_spec__1(v_00_u03b2_614_, v_m_615_, v_a_616_);
lean_dec(v_a_616_);
lean_dec_ref(v_m_615_);
return v_res_617_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2(lean_object* v_00_u03b2_618_, lean_object* v_m_619_, lean_object* v_a_620_, lean_object* v_b_621_){
_start:
{
lean_object* v___x_622_; 
v___x_622_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2___redArg(v_m_619_, v_a_620_, v_b_621_);
return v___x_622_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectLevelAux_spec__1_spec__1(lean_object* v_00_u03b2_623_, lean_object* v_a_624_, lean_object* v_x_625_){
_start:
{
lean_object* v___x_626_; 
v___x_626_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectLevelAux_spec__1_spec__1___redArg(v_a_624_, v_x_625_);
return v___x_626_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectLevelAux_spec__1_spec__1___boxed(lean_object* v_00_u03b2_627_, lean_object* v_a_628_, lean_object* v_x_629_){
_start:
{
lean_object* v_res_630_; 
v_res_630_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectLevelAux_spec__1_spec__1(v_00_u03b2_627_, v_a_628_, v_x_629_);
lean_dec(v_x_629_);
lean_dec(v_a_628_);
return v_res_630_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__3(lean_object* v_00_u03b2_631_, lean_object* v_a_632_, lean_object* v_x_633_){
_start:
{
uint8_t v___x_634_; 
v___x_634_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__3___redArg(v_a_632_, v_x_633_);
return v___x_634_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__3___boxed(lean_object* v_00_u03b2_635_, lean_object* v_a_636_, lean_object* v_x_637_){
_start:
{
uint8_t v_res_638_; lean_object* v_r_639_; 
v_res_638_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__3(v_00_u03b2_635_, v_a_636_, v_x_637_);
lean_dec(v_x_637_);
lean_dec(v_a_636_);
v_r_639_ = lean_box(v_res_638_);
return v_r_639_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__4(lean_object* v_00_u03b2_640_, lean_object* v_data_641_){
_start:
{
lean_object* v___x_642_; 
v___x_642_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__4___redArg(v_data_641_);
return v___x_642_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__5(lean_object* v_00_u03b2_643_, lean_object* v_a_644_, lean_object* v_b_645_, lean_object* v_x_646_){
_start:
{
lean_object* v___x_647_; 
v___x_647_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__5___redArg(v_a_644_, v_b_645_, v_x_646_);
return v___x_647_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_648_, lean_object* v_i_649_, lean_object* v_source_650_, lean_object* v_target_651_){
_start:
{
lean_object* v___x_652_; 
v___x_652_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__4_spec__5___redArg(v_i_649_, v_source_650_, v_target_651_);
return v___x_652_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__4_spec__5_spec__6(lean_object* v_00_u03b2_653_, lean_object* v_x_654_, lean_object* v_x_655_){
_start:
{
lean_object* v___x_656_; 
v___x_656_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__4_spec__5_spec__6___redArg(v_x_654_, v_x_655_);
return v___x_656_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectLevel___redArg(lean_object* v_u_657_, lean_object* v_a_658_){
_start:
{
uint8_t v___x_703_; 
v___x_703_ = l_Lean_Level_hasMVar(v_u_657_);
if (v___x_703_ == 0)
{
uint8_t v___x_704_; 
v___x_704_ = l_Lean_Level_hasParam(v_u_657_);
if (v___x_704_ == 0)
{
lean_object* v___x_705_; 
v___x_705_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_705_, 0, v_u_657_);
return v___x_705_;
}
else
{
goto v___jp_660_;
}
}
else
{
goto v___jp_660_;
}
v___jp_660_:
{
lean_object* v___x_661_; lean_object* v_visitedLevel_662_; lean_object* v___x_663_; 
v___x_661_ = lean_st_ref_get(v_a_658_);
v_visitedLevel_662_ = lean_ctor_get(v___x_661_, 0);
lean_inc_ref(v_visitedLevel_662_);
lean_dec(v___x_661_);
v___x_663_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectLevelAux_spec__1___redArg(v_visitedLevel_662_, v_u_657_);
lean_dec_ref(v_visitedLevel_662_);
if (lean_obj_tag(v___x_663_) == 0)
{
lean_object* v___x_664_; 
lean_inc(v_u_657_);
v___x_664_ = l_Lean_Meta_Closure_collectLevelAux___redArg(v_u_657_, v_a_658_);
if (lean_obj_tag(v___x_664_) == 0)
{
lean_object* v_a_665_; lean_object* v___x_667_; uint8_t v_isShared_668_; uint8_t v_isSharedCheck_694_; 
v_a_665_ = lean_ctor_get(v___x_664_, 0);
v_isSharedCheck_694_ = !lean_is_exclusive(v___x_664_);
if (v_isSharedCheck_694_ == 0)
{
v___x_667_ = v___x_664_;
v_isShared_668_ = v_isSharedCheck_694_;
goto v_resetjp_666_;
}
else
{
lean_inc(v_a_665_);
lean_dec(v___x_664_);
v___x_667_ = lean_box(0);
v_isShared_668_ = v_isSharedCheck_694_;
goto v_resetjp_666_;
}
v_resetjp_666_:
{
lean_object* v___x_669_; lean_object* v_visitedLevel_670_; lean_object* v_visitedExpr_671_; lean_object* v_levelParams_672_; lean_object* v_nextLevelIdx_673_; lean_object* v_levelArgs_674_; lean_object* v_newLocalDecls_675_; lean_object* v_newLocalDeclsForMVars_676_; lean_object* v_newLetDecls_677_; lean_object* v_nextExprIdx_678_; lean_object* v_exprMVarArgs_679_; lean_object* v_exprFVarArgs_680_; lean_object* v_toProcess_681_; lean_object* v___x_683_; uint8_t v_isShared_684_; uint8_t v_isSharedCheck_693_; 
v___x_669_ = lean_st_ref_take(v_a_658_);
v_visitedLevel_670_ = lean_ctor_get(v___x_669_, 0);
v_visitedExpr_671_ = lean_ctor_get(v___x_669_, 1);
v_levelParams_672_ = lean_ctor_get(v___x_669_, 2);
v_nextLevelIdx_673_ = lean_ctor_get(v___x_669_, 3);
v_levelArgs_674_ = lean_ctor_get(v___x_669_, 4);
v_newLocalDecls_675_ = lean_ctor_get(v___x_669_, 5);
v_newLocalDeclsForMVars_676_ = lean_ctor_get(v___x_669_, 6);
v_newLetDecls_677_ = lean_ctor_get(v___x_669_, 7);
v_nextExprIdx_678_ = lean_ctor_get(v___x_669_, 8);
v_exprMVarArgs_679_ = lean_ctor_get(v___x_669_, 9);
v_exprFVarArgs_680_ = lean_ctor_get(v___x_669_, 10);
v_toProcess_681_ = lean_ctor_get(v___x_669_, 11);
v_isSharedCheck_693_ = !lean_is_exclusive(v___x_669_);
if (v_isSharedCheck_693_ == 0)
{
v___x_683_ = v___x_669_;
v_isShared_684_ = v_isSharedCheck_693_;
goto v_resetjp_682_;
}
else
{
lean_inc(v_toProcess_681_);
lean_inc(v_exprFVarArgs_680_);
lean_inc(v_exprMVarArgs_679_);
lean_inc(v_nextExprIdx_678_);
lean_inc(v_newLetDecls_677_);
lean_inc(v_newLocalDeclsForMVars_676_);
lean_inc(v_newLocalDecls_675_);
lean_inc(v_levelArgs_674_);
lean_inc(v_nextLevelIdx_673_);
lean_inc(v_levelParams_672_);
lean_inc(v_visitedExpr_671_);
lean_inc(v_visitedLevel_670_);
lean_dec(v___x_669_);
v___x_683_ = lean_box(0);
v_isShared_684_ = v_isSharedCheck_693_;
goto v_resetjp_682_;
}
v_resetjp_682_:
{
lean_object* v___x_685_; lean_object* v___x_687_; 
lean_inc(v_a_665_);
v___x_685_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2___redArg(v_visitedLevel_670_, v_u_657_, v_a_665_);
if (v_isShared_684_ == 0)
{
lean_ctor_set(v___x_683_, 0, v___x_685_);
v___x_687_ = v___x_683_;
goto v_reusejp_686_;
}
else
{
lean_object* v_reuseFailAlloc_692_; 
v_reuseFailAlloc_692_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_692_, 0, v___x_685_);
lean_ctor_set(v_reuseFailAlloc_692_, 1, v_visitedExpr_671_);
lean_ctor_set(v_reuseFailAlloc_692_, 2, v_levelParams_672_);
lean_ctor_set(v_reuseFailAlloc_692_, 3, v_nextLevelIdx_673_);
lean_ctor_set(v_reuseFailAlloc_692_, 4, v_levelArgs_674_);
lean_ctor_set(v_reuseFailAlloc_692_, 5, v_newLocalDecls_675_);
lean_ctor_set(v_reuseFailAlloc_692_, 6, v_newLocalDeclsForMVars_676_);
lean_ctor_set(v_reuseFailAlloc_692_, 7, v_newLetDecls_677_);
lean_ctor_set(v_reuseFailAlloc_692_, 8, v_nextExprIdx_678_);
lean_ctor_set(v_reuseFailAlloc_692_, 9, v_exprMVarArgs_679_);
lean_ctor_set(v_reuseFailAlloc_692_, 10, v_exprFVarArgs_680_);
lean_ctor_set(v_reuseFailAlloc_692_, 11, v_toProcess_681_);
v___x_687_ = v_reuseFailAlloc_692_;
goto v_reusejp_686_;
}
v_reusejp_686_:
{
lean_object* v___x_688_; lean_object* v___x_690_; 
v___x_688_ = lean_st_ref_set(v_a_658_, v___x_687_);
if (v_isShared_668_ == 0)
{
v___x_690_ = v___x_667_;
goto v_reusejp_689_;
}
else
{
lean_object* v_reuseFailAlloc_691_; 
v_reuseFailAlloc_691_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_691_, 0, v_a_665_);
v___x_690_ = v_reuseFailAlloc_691_;
goto v_reusejp_689_;
}
v_reusejp_689_:
{
return v___x_690_;
}
}
}
}
}
else
{
lean_dec(v_u_657_);
return v___x_664_;
}
}
else
{
lean_object* v_val_695_; lean_object* v___x_697_; uint8_t v_isShared_698_; uint8_t v_isSharedCheck_702_; 
lean_dec(v_u_657_);
v_val_695_ = lean_ctor_get(v___x_663_, 0);
v_isSharedCheck_702_ = !lean_is_exclusive(v___x_663_);
if (v_isSharedCheck_702_ == 0)
{
v___x_697_ = v___x_663_;
v_isShared_698_ = v_isSharedCheck_702_;
goto v_resetjp_696_;
}
else
{
lean_inc(v_val_695_);
lean_dec(v___x_663_);
v___x_697_ = lean_box(0);
v_isShared_698_ = v_isSharedCheck_702_;
goto v_resetjp_696_;
}
v_resetjp_696_:
{
lean_object* v___x_700_; 
if (v_isShared_698_ == 0)
{
lean_ctor_set_tag(v___x_697_, 0);
v___x_700_ = v___x_697_;
goto v_reusejp_699_;
}
else
{
lean_object* v_reuseFailAlloc_701_; 
v_reuseFailAlloc_701_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_701_, 0, v_val_695_);
v___x_700_ = v_reuseFailAlloc_701_;
goto v_reusejp_699_;
}
v_reusejp_699_:
{
return v___x_700_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectLevel___redArg___boxed(lean_object* v_u_706_, lean_object* v_a_707_, lean_object* v_a_708_){
_start:
{
lean_object* v_res_709_; 
v_res_709_ = l_Lean_Meta_Closure_collectLevel___redArg(v_u_706_, v_a_707_);
lean_dec(v_a_707_);
return v_res_709_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectLevel(lean_object* v_u_710_, uint8_t v_a_711_, lean_object* v_a_712_, lean_object* v_a_713_, lean_object* v_a_714_, lean_object* v_a_715_, lean_object* v_a_716_){
_start:
{
lean_object* v___x_718_; 
v___x_718_ = l_Lean_Meta_Closure_collectLevel___redArg(v_u_710_, v_a_712_);
return v___x_718_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectLevel___boxed(lean_object* v_u_719_, lean_object* v_a_720_, lean_object* v_a_721_, lean_object* v_a_722_, lean_object* v_a_723_, lean_object* v_a_724_, lean_object* v_a_725_, lean_object* v_a_726_){
_start:
{
uint8_t v_a_boxed_727_; lean_object* v_res_728_; 
v_a_boxed_727_ = lean_unbox(v_a_720_);
v_res_728_ = l_Lean_Meta_Closure_collectLevel(v_u_719_, v_a_boxed_727_, v_a_721_, v_a_722_, v_a_723_, v_a_724_, v_a_725_);
lean_dec(v_a_725_);
lean_dec_ref(v_a_724_);
lean_dec(v_a_723_);
lean_dec_ref(v_a_722_);
lean_dec(v_a_721_);
return v_res_728_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Closure_preprocess_spec__0___redArg(lean_object* v_e_729_, lean_object* v___y_730_){
_start:
{
uint8_t v___x_732_; 
v___x_732_ = l_Lean_Expr_hasMVar(v_e_729_);
if (v___x_732_ == 0)
{
lean_object* v___x_733_; 
v___x_733_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_733_, 0, v_e_729_);
return v___x_733_;
}
else
{
lean_object* v___x_734_; lean_object* v_mctx_735_; lean_object* v___x_736_; lean_object* v_fst_737_; lean_object* v_snd_738_; lean_object* v___x_739_; lean_object* v_cache_740_; lean_object* v_zetaDeltaFVarIds_741_; lean_object* v_postponed_742_; lean_object* v_diag_743_; lean_object* v___x_745_; uint8_t v_isShared_746_; uint8_t v_isSharedCheck_752_; 
v___x_734_ = lean_st_ref_get(v___y_730_);
v_mctx_735_ = lean_ctor_get(v___x_734_, 0);
lean_inc_ref(v_mctx_735_);
lean_dec(v___x_734_);
v___x_736_ = l_Lean_instantiateMVarsCore(v_mctx_735_, v_e_729_);
v_fst_737_ = lean_ctor_get(v___x_736_, 0);
lean_inc(v_fst_737_);
v_snd_738_ = lean_ctor_get(v___x_736_, 1);
lean_inc(v_snd_738_);
lean_dec_ref(v___x_736_);
v___x_739_ = lean_st_ref_take(v___y_730_);
v_cache_740_ = lean_ctor_get(v___x_739_, 1);
v_zetaDeltaFVarIds_741_ = lean_ctor_get(v___x_739_, 2);
v_postponed_742_ = lean_ctor_get(v___x_739_, 3);
v_diag_743_ = lean_ctor_get(v___x_739_, 4);
v_isSharedCheck_752_ = !lean_is_exclusive(v___x_739_);
if (v_isSharedCheck_752_ == 0)
{
lean_object* v_unused_753_; 
v_unused_753_ = lean_ctor_get(v___x_739_, 0);
lean_dec(v_unused_753_);
v___x_745_ = v___x_739_;
v_isShared_746_ = v_isSharedCheck_752_;
goto v_resetjp_744_;
}
else
{
lean_inc(v_diag_743_);
lean_inc(v_postponed_742_);
lean_inc(v_zetaDeltaFVarIds_741_);
lean_inc(v_cache_740_);
lean_dec(v___x_739_);
v___x_745_ = lean_box(0);
v_isShared_746_ = v_isSharedCheck_752_;
goto v_resetjp_744_;
}
v_resetjp_744_:
{
lean_object* v___x_748_; 
if (v_isShared_746_ == 0)
{
lean_ctor_set(v___x_745_, 0, v_snd_738_);
v___x_748_ = v___x_745_;
goto v_reusejp_747_;
}
else
{
lean_object* v_reuseFailAlloc_751_; 
v_reuseFailAlloc_751_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_751_, 0, v_snd_738_);
lean_ctor_set(v_reuseFailAlloc_751_, 1, v_cache_740_);
lean_ctor_set(v_reuseFailAlloc_751_, 2, v_zetaDeltaFVarIds_741_);
lean_ctor_set(v_reuseFailAlloc_751_, 3, v_postponed_742_);
lean_ctor_set(v_reuseFailAlloc_751_, 4, v_diag_743_);
v___x_748_ = v_reuseFailAlloc_751_;
goto v_reusejp_747_;
}
v_reusejp_747_:
{
lean_object* v___x_749_; lean_object* v___x_750_; 
v___x_749_ = lean_st_ref_set(v___y_730_, v___x_748_);
v___x_750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_750_, 0, v_fst_737_);
return v___x_750_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Closure_preprocess_spec__0___redArg___boxed(lean_object* v_e_754_, lean_object* v___y_755_, lean_object* v___y_756_){
_start:
{
lean_object* v_res_757_; 
v_res_757_ = l_Lean_instantiateMVars___at___00Lean_Meta_Closure_preprocess_spec__0___redArg(v_e_754_, v___y_755_);
lean_dec(v___y_755_);
return v_res_757_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Closure_preprocess_spec__0(lean_object* v_e_758_, uint8_t v___y_759_, lean_object* v___y_760_, lean_object* v___y_761_, lean_object* v___y_762_, lean_object* v___y_763_, lean_object* v___y_764_){
_start:
{
lean_object* v___x_766_; 
v___x_766_ = l_Lean_instantiateMVars___at___00Lean_Meta_Closure_preprocess_spec__0___redArg(v_e_758_, v___y_762_);
return v___x_766_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Closure_preprocess_spec__0___boxed(lean_object* v_e_767_, lean_object* v___y_768_, lean_object* v___y_769_, lean_object* v___y_770_, lean_object* v___y_771_, lean_object* v___y_772_, lean_object* v___y_773_, lean_object* v___y_774_){
_start:
{
uint8_t v___y_2247__boxed_775_; lean_object* v_res_776_; 
v___y_2247__boxed_775_ = lean_unbox(v___y_768_);
v_res_776_ = l_Lean_instantiateMVars___at___00Lean_Meta_Closure_preprocess_spec__0(v_e_767_, v___y_2247__boxed_775_, v___y_769_, v___y_770_, v___y_771_, v___y_772_, v___y_773_);
lean_dec(v___y_773_);
lean_dec_ref(v___y_772_);
lean_dec(v___y_771_);
lean_dec_ref(v___y_770_);
lean_dec(v___y_769_);
return v_res_776_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_preprocess(lean_object* v_e_777_, uint8_t v_a_778_, lean_object* v_a_779_, lean_object* v_a_780_, lean_object* v_a_781_, lean_object* v_a_782_, lean_object* v_a_783_){
_start:
{
lean_object* v___x_785_; 
v___x_785_ = l_Lean_instantiateMVars___at___00Lean_Meta_Closure_preprocess_spec__0___redArg(v_e_777_, v_a_781_);
if (v_a_778_ == 0)
{
lean_object* v_a_786_; lean_object* v___x_787_; 
v_a_786_ = lean_ctor_get(v___x_785_, 0);
lean_inc_n(v_a_786_, 2);
lean_dec_ref(v___x_785_);
v___x_787_ = l_Lean_Meta_check(v_a_786_, v_a_780_, v_a_781_, v_a_782_, v_a_783_);
if (lean_obj_tag(v___x_787_) == 0)
{
lean_object* v___x_789_; uint8_t v_isShared_790_; uint8_t v_isSharedCheck_794_; 
v_isSharedCheck_794_ = !lean_is_exclusive(v___x_787_);
if (v_isSharedCheck_794_ == 0)
{
lean_object* v_unused_795_; 
v_unused_795_ = lean_ctor_get(v___x_787_, 0);
lean_dec(v_unused_795_);
v___x_789_ = v___x_787_;
v_isShared_790_ = v_isSharedCheck_794_;
goto v_resetjp_788_;
}
else
{
lean_dec(v___x_787_);
v___x_789_ = lean_box(0);
v_isShared_790_ = v_isSharedCheck_794_;
goto v_resetjp_788_;
}
v_resetjp_788_:
{
lean_object* v___x_792_; 
if (v_isShared_790_ == 0)
{
lean_ctor_set(v___x_789_, 0, v_a_786_);
v___x_792_ = v___x_789_;
goto v_reusejp_791_;
}
else
{
lean_object* v_reuseFailAlloc_793_; 
v_reuseFailAlloc_793_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_793_, 0, v_a_786_);
v___x_792_ = v_reuseFailAlloc_793_;
goto v_reusejp_791_;
}
v_reusejp_791_:
{
return v___x_792_;
}
}
}
else
{
lean_object* v_a_796_; lean_object* v___x_798_; uint8_t v_isShared_799_; uint8_t v_isSharedCheck_803_; 
lean_dec(v_a_786_);
v_a_796_ = lean_ctor_get(v___x_787_, 0);
v_isSharedCheck_803_ = !lean_is_exclusive(v___x_787_);
if (v_isSharedCheck_803_ == 0)
{
v___x_798_ = v___x_787_;
v_isShared_799_ = v_isSharedCheck_803_;
goto v_resetjp_797_;
}
else
{
lean_inc(v_a_796_);
lean_dec(v___x_787_);
v___x_798_ = lean_box(0);
v_isShared_799_ = v_isSharedCheck_803_;
goto v_resetjp_797_;
}
v_resetjp_797_:
{
lean_object* v___x_801_; 
if (v_isShared_799_ == 0)
{
v___x_801_ = v___x_798_;
goto v_reusejp_800_;
}
else
{
lean_object* v_reuseFailAlloc_802_; 
v_reuseFailAlloc_802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_802_, 0, v_a_796_);
v___x_801_ = v_reuseFailAlloc_802_;
goto v_reusejp_800_;
}
v_reusejp_800_:
{
return v___x_801_;
}
}
}
}
else
{
return v___x_785_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_preprocess___boxed(lean_object* v_e_804_, lean_object* v_a_805_, lean_object* v_a_806_, lean_object* v_a_807_, lean_object* v_a_808_, lean_object* v_a_809_, lean_object* v_a_810_, lean_object* v_a_811_){
_start:
{
uint8_t v_a_boxed_812_; lean_object* v_res_813_; 
v_a_boxed_812_ = lean_unbox(v_a_805_);
v_res_813_ = l_Lean_Meta_Closure_preprocess(v_e_804_, v_a_boxed_812_, v_a_806_, v_a_807_, v_a_808_, v_a_809_, v_a_810_);
lean_dec(v_a_810_);
lean_dec_ref(v_a_809_);
lean_dec(v_a_808_);
lean_dec_ref(v_a_807_);
lean_dec(v_a_806_);
return v_res_813_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkNextUserName___redArg(lean_object* v_a_817_){
_start:
{
lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v_visitedLevel_821_; lean_object* v_visitedExpr_822_; lean_object* v_levelParams_823_; lean_object* v_nextLevelIdx_824_; lean_object* v_levelArgs_825_; lean_object* v_newLocalDecls_826_; lean_object* v_newLocalDeclsForMVars_827_; lean_object* v_newLetDecls_828_; lean_object* v_nextExprIdx_829_; lean_object* v_exprMVarArgs_830_; lean_object* v_exprFVarArgs_831_; lean_object* v_toProcess_832_; lean_object* v___x_834_; uint8_t v_isShared_835_; uint8_t v_isSharedCheck_846_; 
v___x_819_ = lean_st_ref_get(v_a_817_);
v___x_820_ = lean_st_ref_take(v_a_817_);
v_visitedLevel_821_ = lean_ctor_get(v___x_820_, 0);
v_visitedExpr_822_ = lean_ctor_get(v___x_820_, 1);
v_levelParams_823_ = lean_ctor_get(v___x_820_, 2);
v_nextLevelIdx_824_ = lean_ctor_get(v___x_820_, 3);
v_levelArgs_825_ = lean_ctor_get(v___x_820_, 4);
v_newLocalDecls_826_ = lean_ctor_get(v___x_820_, 5);
v_newLocalDeclsForMVars_827_ = lean_ctor_get(v___x_820_, 6);
v_newLetDecls_828_ = lean_ctor_get(v___x_820_, 7);
v_nextExprIdx_829_ = lean_ctor_get(v___x_820_, 8);
v_exprMVarArgs_830_ = lean_ctor_get(v___x_820_, 9);
v_exprFVarArgs_831_ = lean_ctor_get(v___x_820_, 10);
v_toProcess_832_ = lean_ctor_get(v___x_820_, 11);
v_isSharedCheck_846_ = !lean_is_exclusive(v___x_820_);
if (v_isSharedCheck_846_ == 0)
{
v___x_834_ = v___x_820_;
v_isShared_835_ = v_isSharedCheck_846_;
goto v_resetjp_833_;
}
else
{
lean_inc(v_toProcess_832_);
lean_inc(v_exprFVarArgs_831_);
lean_inc(v_exprMVarArgs_830_);
lean_inc(v_nextExprIdx_829_);
lean_inc(v_newLetDecls_828_);
lean_inc(v_newLocalDeclsForMVars_827_);
lean_inc(v_newLocalDecls_826_);
lean_inc(v_levelArgs_825_);
lean_inc(v_nextLevelIdx_824_);
lean_inc(v_levelParams_823_);
lean_inc(v_visitedExpr_822_);
lean_inc(v_visitedLevel_821_);
lean_dec(v___x_820_);
v___x_834_ = lean_box(0);
v_isShared_835_ = v_isSharedCheck_846_;
goto v_resetjp_833_;
}
v_resetjp_833_:
{
lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_839_; 
v___x_836_ = lean_unsigned_to_nat(1u);
v___x_837_ = lean_nat_add(v_nextExprIdx_829_, v___x_836_);
lean_dec(v_nextExprIdx_829_);
if (v_isShared_835_ == 0)
{
lean_ctor_set(v___x_834_, 8, v___x_837_);
v___x_839_ = v___x_834_;
goto v_reusejp_838_;
}
else
{
lean_object* v_reuseFailAlloc_845_; 
v_reuseFailAlloc_845_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_845_, 0, v_visitedLevel_821_);
lean_ctor_set(v_reuseFailAlloc_845_, 1, v_visitedExpr_822_);
lean_ctor_set(v_reuseFailAlloc_845_, 2, v_levelParams_823_);
lean_ctor_set(v_reuseFailAlloc_845_, 3, v_nextLevelIdx_824_);
lean_ctor_set(v_reuseFailAlloc_845_, 4, v_levelArgs_825_);
lean_ctor_set(v_reuseFailAlloc_845_, 5, v_newLocalDecls_826_);
lean_ctor_set(v_reuseFailAlloc_845_, 6, v_newLocalDeclsForMVars_827_);
lean_ctor_set(v_reuseFailAlloc_845_, 7, v_newLetDecls_828_);
lean_ctor_set(v_reuseFailAlloc_845_, 8, v___x_837_);
lean_ctor_set(v_reuseFailAlloc_845_, 9, v_exprMVarArgs_830_);
lean_ctor_set(v_reuseFailAlloc_845_, 10, v_exprFVarArgs_831_);
lean_ctor_set(v_reuseFailAlloc_845_, 11, v_toProcess_832_);
v___x_839_ = v_reuseFailAlloc_845_;
goto v_reusejp_838_;
}
v_reusejp_838_:
{
lean_object* v___x_840_; lean_object* v_nextExprIdx_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; 
v___x_840_ = lean_st_ref_set(v_a_817_, v___x_839_);
v_nextExprIdx_841_ = lean_ctor_get(v___x_819_, 8);
lean_inc(v_nextExprIdx_841_);
lean_dec(v___x_819_);
v___x_842_ = ((lean_object*)(l_Lean_Meta_Closure_mkNextUserName___redArg___closed__1));
v___x_843_ = lean_name_append_index_after(v___x_842_, v_nextExprIdx_841_);
v___x_844_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_844_, 0, v___x_843_);
return v___x_844_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkNextUserName___redArg___boxed(lean_object* v_a_847_, lean_object* v_a_848_){
_start:
{
lean_object* v_res_849_; 
v_res_849_ = l_Lean_Meta_Closure_mkNextUserName___redArg(v_a_847_);
lean_dec(v_a_847_);
return v_res_849_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkNextUserName(uint8_t v_a_850_, lean_object* v_a_851_, lean_object* v_a_852_, lean_object* v_a_853_, lean_object* v_a_854_, lean_object* v_a_855_){
_start:
{
lean_object* v___x_857_; 
v___x_857_ = l_Lean_Meta_Closure_mkNextUserName___redArg(v_a_851_);
return v___x_857_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkNextUserName___boxed(lean_object* v_a_858_, lean_object* v_a_859_, lean_object* v_a_860_, lean_object* v_a_861_, lean_object* v_a_862_, lean_object* v_a_863_, lean_object* v_a_864_){
_start:
{
uint8_t v_a_boxed_865_; lean_object* v_res_866_; 
v_a_boxed_865_ = lean_unbox(v_a_858_);
v_res_866_ = l_Lean_Meta_Closure_mkNextUserName(v_a_boxed_865_, v_a_859_, v_a_860_, v_a_861_, v_a_862_, v_a_863_);
lean_dec(v_a_863_);
lean_dec_ref(v_a_862_);
lean_dec(v_a_861_);
lean_dec_ref(v_a_860_);
lean_dec(v_a_859_);
return v_res_866_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushToProcess___redArg(lean_object* v_elem_867_, lean_object* v_a_868_){
_start:
{
lean_object* v___x_870_; lean_object* v_visitedLevel_871_; lean_object* v_visitedExpr_872_; lean_object* v_levelParams_873_; lean_object* v_nextLevelIdx_874_; lean_object* v_levelArgs_875_; lean_object* v_newLocalDecls_876_; lean_object* v_newLocalDeclsForMVars_877_; lean_object* v_newLetDecls_878_; lean_object* v_nextExprIdx_879_; lean_object* v_exprMVarArgs_880_; lean_object* v_exprFVarArgs_881_; lean_object* v_toProcess_882_; lean_object* v___x_884_; uint8_t v_isShared_885_; uint8_t v_isSharedCheck_893_; 
v___x_870_ = lean_st_ref_take(v_a_868_);
v_visitedLevel_871_ = lean_ctor_get(v___x_870_, 0);
v_visitedExpr_872_ = lean_ctor_get(v___x_870_, 1);
v_levelParams_873_ = lean_ctor_get(v___x_870_, 2);
v_nextLevelIdx_874_ = lean_ctor_get(v___x_870_, 3);
v_levelArgs_875_ = lean_ctor_get(v___x_870_, 4);
v_newLocalDecls_876_ = lean_ctor_get(v___x_870_, 5);
v_newLocalDeclsForMVars_877_ = lean_ctor_get(v___x_870_, 6);
v_newLetDecls_878_ = lean_ctor_get(v___x_870_, 7);
v_nextExprIdx_879_ = lean_ctor_get(v___x_870_, 8);
v_exprMVarArgs_880_ = lean_ctor_get(v___x_870_, 9);
v_exprFVarArgs_881_ = lean_ctor_get(v___x_870_, 10);
v_toProcess_882_ = lean_ctor_get(v___x_870_, 11);
v_isSharedCheck_893_ = !lean_is_exclusive(v___x_870_);
if (v_isSharedCheck_893_ == 0)
{
v___x_884_ = v___x_870_;
v_isShared_885_ = v_isSharedCheck_893_;
goto v_resetjp_883_;
}
else
{
lean_inc(v_toProcess_882_);
lean_inc(v_exprFVarArgs_881_);
lean_inc(v_exprMVarArgs_880_);
lean_inc(v_nextExprIdx_879_);
lean_inc(v_newLetDecls_878_);
lean_inc(v_newLocalDeclsForMVars_877_);
lean_inc(v_newLocalDecls_876_);
lean_inc(v_levelArgs_875_);
lean_inc(v_nextLevelIdx_874_);
lean_inc(v_levelParams_873_);
lean_inc(v_visitedExpr_872_);
lean_inc(v_visitedLevel_871_);
lean_dec(v___x_870_);
v___x_884_ = lean_box(0);
v_isShared_885_ = v_isSharedCheck_893_;
goto v_resetjp_883_;
}
v_resetjp_883_:
{
lean_object* v___x_886_; lean_object* v___x_888_; 
v___x_886_ = lean_array_push(v_toProcess_882_, v_elem_867_);
if (v_isShared_885_ == 0)
{
lean_ctor_set(v___x_884_, 11, v___x_886_);
v___x_888_ = v___x_884_;
goto v_reusejp_887_;
}
else
{
lean_object* v_reuseFailAlloc_892_; 
v_reuseFailAlloc_892_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_892_, 0, v_visitedLevel_871_);
lean_ctor_set(v_reuseFailAlloc_892_, 1, v_visitedExpr_872_);
lean_ctor_set(v_reuseFailAlloc_892_, 2, v_levelParams_873_);
lean_ctor_set(v_reuseFailAlloc_892_, 3, v_nextLevelIdx_874_);
lean_ctor_set(v_reuseFailAlloc_892_, 4, v_levelArgs_875_);
lean_ctor_set(v_reuseFailAlloc_892_, 5, v_newLocalDecls_876_);
lean_ctor_set(v_reuseFailAlloc_892_, 6, v_newLocalDeclsForMVars_877_);
lean_ctor_set(v_reuseFailAlloc_892_, 7, v_newLetDecls_878_);
lean_ctor_set(v_reuseFailAlloc_892_, 8, v_nextExprIdx_879_);
lean_ctor_set(v_reuseFailAlloc_892_, 9, v_exprMVarArgs_880_);
lean_ctor_set(v_reuseFailAlloc_892_, 10, v_exprFVarArgs_881_);
lean_ctor_set(v_reuseFailAlloc_892_, 11, v___x_886_);
v___x_888_ = v_reuseFailAlloc_892_;
goto v_reusejp_887_;
}
v_reusejp_887_:
{
lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; 
v___x_889_ = lean_st_ref_set(v_a_868_, v___x_888_);
v___x_890_ = lean_box(0);
v___x_891_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_891_, 0, v___x_890_);
return v___x_891_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushToProcess___redArg___boxed(lean_object* v_elem_894_, lean_object* v_a_895_, lean_object* v_a_896_){
_start:
{
lean_object* v_res_897_; 
v_res_897_ = l_Lean_Meta_Closure_pushToProcess___redArg(v_elem_894_, v_a_895_);
lean_dec(v_a_895_);
return v_res_897_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushToProcess(lean_object* v_elem_898_, uint8_t v_a_899_, lean_object* v_a_900_, lean_object* v_a_901_, lean_object* v_a_902_, lean_object* v_a_903_, lean_object* v_a_904_){
_start:
{
lean_object* v___x_906_; 
v___x_906_ = l_Lean_Meta_Closure_pushToProcess___redArg(v_elem_898_, v_a_900_);
return v___x_906_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushToProcess___boxed(lean_object* v_elem_907_, lean_object* v_a_908_, lean_object* v_a_909_, lean_object* v_a_910_, lean_object* v_a_911_, lean_object* v_a_912_, lean_object* v_a_913_, lean_object* v_a_914_){
_start:
{
uint8_t v_a_boxed_915_; lean_object* v_res_916_; 
v_a_boxed_915_ = lean_unbox(v_a_908_);
v_res_916_ = l_Lean_Meta_Closure_pushToProcess(v_elem_907_, v_a_boxed_915_, v_a_909_, v_a_910_, v_a_911_, v_a_912_, v_a_913_);
lean_dec(v_a_913_);
lean_dec_ref(v_a_912_);
lean_dec(v_a_911_);
lean_dec_ref(v_a_910_);
lean_dec(v_a_909_);
return v_res_916_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__4___redArg(lean_object* v_mvarId_917_, lean_object* v___y_918_){
_start:
{
lean_object* v___x_920_; lean_object* v_mctx_921_; lean_object* v___x_922_; lean_object* v___x_923_; 
v___x_920_ = lean_st_ref_get(v___y_918_);
v_mctx_921_ = lean_ctor_get(v___x_920_, 0);
lean_inc_ref(v_mctx_921_);
lean_dec(v___x_920_);
v___x_922_ = l_Lean_MetavarContext_getDelayedMVarAssignmentCore_x3f(v_mctx_921_, v_mvarId_917_);
lean_dec_ref(v_mctx_921_);
v___x_923_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_923_, 0, v___x_922_);
return v___x_923_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__4___redArg___boxed(lean_object* v_mvarId_924_, lean_object* v___y_925_, lean_object* v___y_926_){
_start:
{
lean_object* v_res_927_; 
v_res_927_ = l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__4___redArg(v_mvarId_924_, v___y_925_);
lean_dec(v___y_925_);
lean_dec(v_mvarId_924_);
return v_res_927_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__4(lean_object* v_mvarId_928_, uint8_t v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_){
_start:
{
lean_object* v___x_936_; 
v___x_936_ = l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__4___redArg(v_mvarId_928_, v___y_932_);
return v___x_936_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__4___boxed(lean_object* v_mvarId_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_, lean_object* v___y_943_, lean_object* v___y_944_){
_start:
{
uint8_t v___y_17871__boxed_945_; lean_object* v_res_946_; 
v___y_17871__boxed_945_ = lean_unbox(v___y_938_);
v_res_946_ = l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__4(v_mvarId_937_, v___y_17871__boxed_945_, v___y_939_, v___y_940_, v___y_941_, v___y_942_, v___y_943_);
lean_dec(v___y_943_);
lean_dec_ref(v___y_942_);
lean_dec(v___y_941_);
lean_dec_ref(v___y_940_);
lean_dec(v___y_939_);
lean_dec(v_mvarId_937_);
return v_res_946_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Closure_collectExprAux_spec__5___redArg___lam__0(lean_object* v_k_947_, uint8_t v___y_948_, lean_object* v___y_949_, lean_object* v_b_950_, lean_object* v_c_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_){
_start:
{
lean_object* v___x_957_; lean_object* v___x_958_; 
v___x_957_ = lean_box(v___y_948_);
lean_inc(v___y_955_);
lean_inc_ref(v___y_954_);
lean_inc(v___y_953_);
lean_inc_ref(v___y_952_);
lean_inc(v___y_949_);
v___x_958_ = lean_apply_9(v_k_947_, v_b_950_, v_c_951_, v___x_957_, v___y_949_, v___y_952_, v___y_953_, v___y_954_, v___y_955_, lean_box(0));
return v___x_958_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Closure_collectExprAux_spec__5___redArg___lam__0___boxed(lean_object* v_k_959_, lean_object* v___y_960_, lean_object* v___y_961_, lean_object* v_b_962_, lean_object* v_c_963_, lean_object* v___y_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_){
_start:
{
uint8_t v___y_17894__boxed_969_; lean_object* v_res_970_; 
v___y_17894__boxed_969_ = lean_unbox(v___y_960_);
v_res_970_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Closure_collectExprAux_spec__5___redArg___lam__0(v_k_959_, v___y_17894__boxed_969_, v___y_961_, v_b_962_, v_c_963_, v___y_964_, v___y_965_, v___y_966_, v___y_967_);
lean_dec(v___y_967_);
lean_dec_ref(v___y_966_);
lean_dec(v___y_965_);
lean_dec_ref(v___y_964_);
lean_dec(v___y_961_);
return v_res_970_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Closure_collectExprAux_spec__5___redArg(lean_object* v_type_971_, lean_object* v_maxFVars_x3f_972_, lean_object* v_k_973_, uint8_t v_cleanupAnnotations_974_, uint8_t v_whnfType_975_, uint8_t v___y_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_, lean_object* v___y_980_, lean_object* v___y_981_){
_start:
{
lean_object* v___x_983_; lean_object* v___f_984_; lean_object* v___x_985_; 
v___x_983_ = lean_box(v___y_976_);
lean_inc(v___y_977_);
v___f_984_ = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Closure_collectExprAux_spec__5___redArg___lam__0___boxed), 10, 3);
lean_closure_set(v___f_984_, 0, v_k_973_);
lean_closure_set(v___f_984_, 1, v___x_983_);
lean_closure_set(v___f_984_, 2, v___y_977_);
v___x_985_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_971_, v_maxFVars_x3f_972_, v___f_984_, v_cleanupAnnotations_974_, v_whnfType_975_, v___y_978_, v___y_979_, v___y_980_, v___y_981_);
if (lean_obj_tag(v___x_985_) == 0)
{
return v___x_985_;
}
else
{
lean_object* v_a_986_; lean_object* v___x_988_; uint8_t v_isShared_989_; uint8_t v_isSharedCheck_993_; 
v_a_986_ = lean_ctor_get(v___x_985_, 0);
v_isSharedCheck_993_ = !lean_is_exclusive(v___x_985_);
if (v_isSharedCheck_993_ == 0)
{
v___x_988_ = v___x_985_;
v_isShared_989_ = v_isSharedCheck_993_;
goto v_resetjp_987_;
}
else
{
lean_inc(v_a_986_);
lean_dec(v___x_985_);
v___x_988_ = lean_box(0);
v_isShared_989_ = v_isSharedCheck_993_;
goto v_resetjp_987_;
}
v_resetjp_987_:
{
lean_object* v___x_991_; 
if (v_isShared_989_ == 0)
{
v___x_991_ = v___x_988_;
goto v_reusejp_990_;
}
else
{
lean_object* v_reuseFailAlloc_992_; 
v_reuseFailAlloc_992_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_992_, 0, v_a_986_);
v___x_991_ = v_reuseFailAlloc_992_;
goto v_reusejp_990_;
}
v_reusejp_990_:
{
return v___x_991_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Closure_collectExprAux_spec__5___redArg___boxed(lean_object* v_type_994_, lean_object* v_maxFVars_x3f_995_, lean_object* v_k_996_, lean_object* v_cleanupAnnotations_997_, lean_object* v_whnfType_998_, lean_object* v___y_999_, lean_object* v___y_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1006_; uint8_t v_whnfType_boxed_1007_; uint8_t v___y_17919__boxed_1008_; lean_object* v_res_1009_; 
v_cleanupAnnotations_boxed_1006_ = lean_unbox(v_cleanupAnnotations_997_);
v_whnfType_boxed_1007_ = lean_unbox(v_whnfType_998_);
v___y_17919__boxed_1008_ = lean_unbox(v___y_999_);
v_res_1009_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Closure_collectExprAux_spec__5___redArg(v_type_994_, v_maxFVars_x3f_995_, v_k_996_, v_cleanupAnnotations_boxed_1006_, v_whnfType_boxed_1007_, v___y_17919__boxed_1008_, v___y_1000_, v___y_1001_, v___y_1002_, v___y_1003_, v___y_1004_);
lean_dec(v___y_1004_);
lean_dec_ref(v___y_1003_);
lean_dec(v___y_1002_);
lean_dec_ref(v___y_1001_);
lean_dec(v___y_1000_);
return v_res_1009_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Closure_collectExprAux_spec__5(lean_object* v_00_u03b1_1010_, lean_object* v_type_1011_, lean_object* v_maxFVars_x3f_1012_, lean_object* v_k_1013_, uint8_t v_cleanupAnnotations_1014_, uint8_t v_whnfType_1015_, uint8_t v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_){
_start:
{
lean_object* v___x_1023_; 
v___x_1023_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Closure_collectExprAux_spec__5___redArg(v_type_1011_, v_maxFVars_x3f_1012_, v_k_1013_, v_cleanupAnnotations_1014_, v_whnfType_1015_, v___y_1016_, v___y_1017_, v___y_1018_, v___y_1019_, v___y_1020_, v___y_1021_);
return v___x_1023_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Closure_collectExprAux_spec__5___boxed(lean_object* v_00_u03b1_1024_, lean_object* v_type_1025_, lean_object* v_maxFVars_x3f_1026_, lean_object* v_k_1027_, lean_object* v_cleanupAnnotations_1028_, lean_object* v_whnfType_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1037_; uint8_t v_whnfType_boxed_1038_; uint8_t v___y_17963__boxed_1039_; lean_object* v_res_1040_; 
v_cleanupAnnotations_boxed_1037_ = lean_unbox(v_cleanupAnnotations_1028_);
v_whnfType_boxed_1038_ = lean_unbox(v_whnfType_1029_);
v___y_17963__boxed_1039_ = lean_unbox(v___y_1030_);
v_res_1040_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Closure_collectExprAux_spec__5(v_00_u03b1_1024_, v_type_1025_, v_maxFVars_x3f_1026_, v_k_1027_, v_cleanupAnnotations_boxed_1037_, v_whnfType_boxed_1038_, v___y_17963__boxed_1039_, v___y_1031_, v___y_1032_, v___y_1033_, v___y_1034_, v___y_1035_);
lean_dec(v___y_1035_);
lean_dec_ref(v___y_1034_);
lean_dec(v___y_1033_);
lean_dec_ref(v___y_1032_);
lean_dec(v___y_1031_);
return v_res_1040_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0_spec__0___redArg(lean_object* v_a_1041_, lean_object* v_x_1042_){
_start:
{
if (lean_obj_tag(v_x_1042_) == 0)
{
lean_object* v___x_1043_; 
v___x_1043_ = lean_box(0);
return v___x_1043_;
}
else
{
lean_object* v_key_1044_; lean_object* v_value_1045_; lean_object* v_tail_1046_; uint8_t v___x_1047_; 
v_key_1044_ = lean_ctor_get(v_x_1042_, 0);
v_value_1045_ = lean_ctor_get(v_x_1042_, 1);
v_tail_1046_ = lean_ctor_get(v_x_1042_, 2);
v___x_1047_ = l_Lean_ExprStructEq_beq(v_key_1044_, v_a_1041_);
if (v___x_1047_ == 0)
{
v_x_1042_ = v_tail_1046_;
goto _start;
}
else
{
lean_object* v___x_1049_; 
lean_inc(v_value_1045_);
v___x_1049_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1049_, 0, v_value_1045_);
return v___x_1049_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0_spec__0___redArg___boxed(lean_object* v_a_1050_, lean_object* v_x_1051_){
_start:
{
lean_object* v_res_1052_; 
v_res_1052_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0_spec__0___redArg(v_a_1050_, v_x_1051_);
lean_dec(v_x_1051_);
lean_dec_ref(v_a_1050_);
return v_res_1052_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0___redArg(lean_object* v_m_1053_, lean_object* v_a_1054_){
_start:
{
lean_object* v_buckets_1055_; lean_object* v___x_1056_; uint64_t v___x_1057_; uint64_t v___x_1058_; uint64_t v___x_1059_; uint64_t v_fold_1060_; uint64_t v___x_1061_; uint64_t v___x_1062_; uint64_t v___x_1063_; size_t v___x_1064_; size_t v___x_1065_; size_t v___x_1066_; size_t v___x_1067_; size_t v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; 
v_buckets_1055_ = lean_ctor_get(v_m_1053_, 1);
v___x_1056_ = lean_array_get_size(v_buckets_1055_);
v___x_1057_ = l_Lean_ExprStructEq_hash(v_a_1054_);
v___x_1058_ = 32ULL;
v___x_1059_ = lean_uint64_shift_right(v___x_1057_, v___x_1058_);
v_fold_1060_ = lean_uint64_xor(v___x_1057_, v___x_1059_);
v___x_1061_ = 16ULL;
v___x_1062_ = lean_uint64_shift_right(v_fold_1060_, v___x_1061_);
v___x_1063_ = lean_uint64_xor(v_fold_1060_, v___x_1062_);
v___x_1064_ = lean_uint64_to_usize(v___x_1063_);
v___x_1065_ = lean_usize_of_nat(v___x_1056_);
v___x_1066_ = ((size_t)1ULL);
v___x_1067_ = lean_usize_sub(v___x_1065_, v___x_1066_);
v___x_1068_ = lean_usize_land(v___x_1064_, v___x_1067_);
v___x_1069_ = lean_array_uget_borrowed(v_buckets_1055_, v___x_1068_);
v___x_1070_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0_spec__0___redArg(v_a_1054_, v___x_1069_);
return v___x_1070_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0___redArg___boxed(lean_object* v_m_1071_, lean_object* v_a_1072_){
_start:
{
lean_object* v_res_1073_; 
v_res_1073_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0___redArg(v_m_1071_, v_a_1072_);
lean_dec_ref(v_a_1072_);
lean_dec_ref(v_m_1071_);
return v_res_1073_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Closure_collectExprAux_spec__2___redArg(lean_object* v_x_1074_, lean_object* v_x_1075_, lean_object* v___y_1076_){
_start:
{
if (lean_obj_tag(v_x_1074_) == 0)
{
lean_object* v___x_1078_; lean_object* v___x_1079_; 
v___x_1078_ = l_List_reverse___redArg(v_x_1075_);
v___x_1079_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1079_, 0, v___x_1078_);
return v___x_1079_;
}
else
{
lean_object* v_head_1080_; lean_object* v_tail_1081_; lean_object* v___x_1083_; uint8_t v_isShared_1084_; uint8_t v_isSharedCheck_1099_; 
v_head_1080_ = lean_ctor_get(v_x_1074_, 0);
v_tail_1081_ = lean_ctor_get(v_x_1074_, 1);
v_isSharedCheck_1099_ = !lean_is_exclusive(v_x_1074_);
if (v_isSharedCheck_1099_ == 0)
{
v___x_1083_ = v_x_1074_;
v_isShared_1084_ = v_isSharedCheck_1099_;
goto v_resetjp_1082_;
}
else
{
lean_inc(v_tail_1081_);
lean_inc(v_head_1080_);
lean_dec(v_x_1074_);
v___x_1083_ = lean_box(0);
v_isShared_1084_ = v_isSharedCheck_1099_;
goto v_resetjp_1082_;
}
v_resetjp_1082_:
{
lean_object* v___x_1085_; 
v___x_1085_ = l_Lean_Meta_Closure_collectLevel___redArg(v_head_1080_, v___y_1076_);
if (lean_obj_tag(v___x_1085_) == 0)
{
lean_object* v_a_1086_; lean_object* v___x_1088_; 
v_a_1086_ = lean_ctor_get(v___x_1085_, 0);
lean_inc(v_a_1086_);
lean_dec_ref(v___x_1085_);
if (v_isShared_1084_ == 0)
{
lean_ctor_set(v___x_1083_, 1, v_x_1075_);
lean_ctor_set(v___x_1083_, 0, v_a_1086_);
v___x_1088_ = v___x_1083_;
goto v_reusejp_1087_;
}
else
{
lean_object* v_reuseFailAlloc_1090_; 
v_reuseFailAlloc_1090_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1090_, 0, v_a_1086_);
lean_ctor_set(v_reuseFailAlloc_1090_, 1, v_x_1075_);
v___x_1088_ = v_reuseFailAlloc_1090_;
goto v_reusejp_1087_;
}
v_reusejp_1087_:
{
v_x_1074_ = v_tail_1081_;
v_x_1075_ = v___x_1088_;
goto _start;
}
}
else
{
lean_object* v_a_1091_; lean_object* v___x_1093_; uint8_t v_isShared_1094_; uint8_t v_isSharedCheck_1098_; 
lean_del_object(v___x_1083_);
lean_dec(v_tail_1081_);
lean_dec(v_x_1075_);
v_a_1091_ = lean_ctor_get(v___x_1085_, 0);
v_isSharedCheck_1098_ = !lean_is_exclusive(v___x_1085_);
if (v_isSharedCheck_1098_ == 0)
{
v___x_1093_ = v___x_1085_;
v_isShared_1094_ = v_isSharedCheck_1098_;
goto v_resetjp_1092_;
}
else
{
lean_inc(v_a_1091_);
lean_dec(v___x_1085_);
v___x_1093_ = lean_box(0);
v_isShared_1094_ = v_isSharedCheck_1098_;
goto v_resetjp_1092_;
}
v_resetjp_1092_:
{
lean_object* v___x_1096_; 
if (v_isShared_1094_ == 0)
{
v___x_1096_ = v___x_1093_;
goto v_reusejp_1095_;
}
else
{
lean_object* v_reuseFailAlloc_1097_; 
v_reuseFailAlloc_1097_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1097_, 0, v_a_1091_);
v___x_1096_ = v_reuseFailAlloc_1097_;
goto v_reusejp_1095_;
}
v_reusejp_1095_:
{
return v___x_1096_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Closure_collectExprAux_spec__2___redArg___boxed(lean_object* v_x_1100_, lean_object* v_x_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_){
_start:
{
lean_object* v_res_1104_; 
v_res_1104_ = l_List_mapM_loop___at___00Lean_Meta_Closure_collectExprAux_spec__2___redArg(v_x_1100_, v_x_1101_, v___y_1102_);
lean_dec(v___y_1102_);
return v_res_1104_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Closure_collectExprAux_spec__3_spec__7___redArg(lean_object* v___y_1105_){
_start:
{
lean_object* v___x_1107_; lean_object* v_ngen_1108_; lean_object* v_namePrefix_1109_; lean_object* v_idx_1110_; lean_object* v___x_1112_; uint8_t v_isShared_1113_; uint8_t v_isSharedCheck_1139_; 
v___x_1107_ = lean_st_ref_get(v___y_1105_);
v_ngen_1108_ = lean_ctor_get(v___x_1107_, 2);
lean_inc_ref(v_ngen_1108_);
lean_dec(v___x_1107_);
v_namePrefix_1109_ = lean_ctor_get(v_ngen_1108_, 0);
v_idx_1110_ = lean_ctor_get(v_ngen_1108_, 1);
v_isSharedCheck_1139_ = !lean_is_exclusive(v_ngen_1108_);
if (v_isSharedCheck_1139_ == 0)
{
v___x_1112_ = v_ngen_1108_;
v_isShared_1113_ = v_isSharedCheck_1139_;
goto v_resetjp_1111_;
}
else
{
lean_inc(v_idx_1110_);
lean_inc(v_namePrefix_1109_);
lean_dec(v_ngen_1108_);
v___x_1112_ = lean_box(0);
v_isShared_1113_ = v_isSharedCheck_1139_;
goto v_resetjp_1111_;
}
v_resetjp_1111_:
{
lean_object* v___x_1114_; lean_object* v_env_1115_; lean_object* v_nextMacroScope_1116_; lean_object* v_auxDeclNGen_1117_; lean_object* v_traceState_1118_; lean_object* v_cache_1119_; lean_object* v_messages_1120_; lean_object* v_infoState_1121_; lean_object* v_snapshotTasks_1122_; lean_object* v___x_1124_; uint8_t v_isShared_1125_; uint8_t v_isSharedCheck_1137_; 
v___x_1114_ = lean_st_ref_take(v___y_1105_);
v_env_1115_ = lean_ctor_get(v___x_1114_, 0);
v_nextMacroScope_1116_ = lean_ctor_get(v___x_1114_, 1);
v_auxDeclNGen_1117_ = lean_ctor_get(v___x_1114_, 3);
v_traceState_1118_ = lean_ctor_get(v___x_1114_, 4);
v_cache_1119_ = lean_ctor_get(v___x_1114_, 5);
v_messages_1120_ = lean_ctor_get(v___x_1114_, 6);
v_infoState_1121_ = lean_ctor_get(v___x_1114_, 7);
v_snapshotTasks_1122_ = lean_ctor_get(v___x_1114_, 8);
v_isSharedCheck_1137_ = !lean_is_exclusive(v___x_1114_);
if (v_isSharedCheck_1137_ == 0)
{
lean_object* v_unused_1138_; 
v_unused_1138_ = lean_ctor_get(v___x_1114_, 2);
lean_dec(v_unused_1138_);
v___x_1124_ = v___x_1114_;
v_isShared_1125_ = v_isSharedCheck_1137_;
goto v_resetjp_1123_;
}
else
{
lean_inc(v_snapshotTasks_1122_);
lean_inc(v_infoState_1121_);
lean_inc(v_messages_1120_);
lean_inc(v_cache_1119_);
lean_inc(v_traceState_1118_);
lean_inc(v_auxDeclNGen_1117_);
lean_inc(v_nextMacroScope_1116_);
lean_inc(v_env_1115_);
lean_dec(v___x_1114_);
v___x_1124_ = lean_box(0);
v_isShared_1125_ = v_isSharedCheck_1137_;
goto v_resetjp_1123_;
}
v_resetjp_1123_:
{
lean_object* v_r_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1130_; 
lean_inc(v_idx_1110_);
lean_inc(v_namePrefix_1109_);
v_r_1126_ = l_Lean_Name_num___override(v_namePrefix_1109_, v_idx_1110_);
v___x_1127_ = lean_unsigned_to_nat(1u);
v___x_1128_ = lean_nat_add(v_idx_1110_, v___x_1127_);
lean_dec(v_idx_1110_);
if (v_isShared_1113_ == 0)
{
lean_ctor_set(v___x_1112_, 1, v___x_1128_);
v___x_1130_ = v___x_1112_;
goto v_reusejp_1129_;
}
else
{
lean_object* v_reuseFailAlloc_1136_; 
v_reuseFailAlloc_1136_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1136_, 0, v_namePrefix_1109_);
lean_ctor_set(v_reuseFailAlloc_1136_, 1, v___x_1128_);
v___x_1130_ = v_reuseFailAlloc_1136_;
goto v_reusejp_1129_;
}
v_reusejp_1129_:
{
lean_object* v___x_1132_; 
if (v_isShared_1125_ == 0)
{
lean_ctor_set(v___x_1124_, 2, v___x_1130_);
v___x_1132_ = v___x_1124_;
goto v_reusejp_1131_;
}
else
{
lean_object* v_reuseFailAlloc_1135_; 
v_reuseFailAlloc_1135_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1135_, 0, v_env_1115_);
lean_ctor_set(v_reuseFailAlloc_1135_, 1, v_nextMacroScope_1116_);
lean_ctor_set(v_reuseFailAlloc_1135_, 2, v___x_1130_);
lean_ctor_set(v_reuseFailAlloc_1135_, 3, v_auxDeclNGen_1117_);
lean_ctor_set(v_reuseFailAlloc_1135_, 4, v_traceState_1118_);
lean_ctor_set(v_reuseFailAlloc_1135_, 5, v_cache_1119_);
lean_ctor_set(v_reuseFailAlloc_1135_, 6, v_messages_1120_);
lean_ctor_set(v_reuseFailAlloc_1135_, 7, v_infoState_1121_);
lean_ctor_set(v_reuseFailAlloc_1135_, 8, v_snapshotTasks_1122_);
v___x_1132_ = v_reuseFailAlloc_1135_;
goto v_reusejp_1131_;
}
v_reusejp_1131_:
{
lean_object* v___x_1133_; lean_object* v___x_1134_; 
v___x_1133_ = lean_st_ref_set(v___y_1105_, v___x_1132_);
v___x_1134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1134_, 0, v_r_1126_);
return v___x_1134_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Closure_collectExprAux_spec__3_spec__7___redArg___boxed(lean_object* v___y_1140_, lean_object* v___y_1141_){
_start:
{
lean_object* v_res_1142_; 
v_res_1142_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Closure_collectExprAux_spec__3_spec__7___redArg(v___y_1140_);
lean_dec(v___y_1140_);
return v_res_1142_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00Lean_Meta_Closure_collectExprAux_spec__3(uint8_t v___y_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_){
_start:
{
lean_object* v___x_1150_; lean_object* v_a_1151_; lean_object* v___x_1153_; uint8_t v_isShared_1154_; uint8_t v_isSharedCheck_1158_; 
v___x_1150_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Closure_collectExprAux_spec__3_spec__7___redArg(v___y_1148_);
v_a_1151_ = lean_ctor_get(v___x_1150_, 0);
v_isSharedCheck_1158_ = !lean_is_exclusive(v___x_1150_);
if (v_isSharedCheck_1158_ == 0)
{
v___x_1153_ = v___x_1150_;
v_isShared_1154_ = v_isSharedCheck_1158_;
goto v_resetjp_1152_;
}
else
{
lean_inc(v_a_1151_);
lean_dec(v___x_1150_);
v___x_1153_ = lean_box(0);
v_isShared_1154_ = v_isSharedCheck_1158_;
goto v_resetjp_1152_;
}
v_resetjp_1152_:
{
lean_object* v___x_1156_; 
if (v_isShared_1154_ == 0)
{
v___x_1156_ = v___x_1153_;
goto v_reusejp_1155_;
}
else
{
lean_object* v_reuseFailAlloc_1157_; 
v_reuseFailAlloc_1157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1157_, 0, v_a_1151_);
v___x_1156_ = v_reuseFailAlloc_1157_;
goto v_reusejp_1155_;
}
v_reusejp_1155_:
{
return v___x_1156_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00Lean_Meta_Closure_collectExprAux_spec__3___boxed(lean_object* v___y_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_){
_start:
{
uint8_t v___y_18138__boxed_1166_; lean_object* v_res_1167_; 
v___y_18138__boxed_1166_ = lean_unbox(v___y_1159_);
v_res_1167_ = l_Lean_mkFreshFVarId___at___00Lean_Meta_Closure_collectExprAux_spec__3(v___y_18138__boxed_1166_, v___y_1160_, v___y_1161_, v___y_1162_, v___y_1163_, v___y_1164_);
lean_dec(v___y_1164_);
lean_dec_ref(v___y_1163_);
lean_dec(v___y_1162_);
lean_dec_ref(v___y_1161_);
lean_dec(v___y_1160_);
return v_res_1167_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectExprAux___lam__1(lean_object* v_e_1168_, lean_object* v_args_1169_, lean_object* v_x_1170_, uint8_t v___y_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_){
_start:
{
lean_object* v___x_1178_; uint8_t v___x_1179_; uint8_t v___x_1180_; uint8_t v___x_1181_; lean_object* v___x_1182_; 
v___x_1178_ = l_Lean_mkAppN(v_e_1168_, v_args_1169_);
v___x_1179_ = 0;
v___x_1180_ = 1;
v___x_1181_ = 1;
v___x_1182_ = l_Lean_Meta_mkLambdaFVars(v_args_1169_, v___x_1178_, v___x_1179_, v___x_1180_, v___x_1179_, v___x_1180_, v___x_1181_, v___y_1173_, v___y_1174_, v___y_1175_, v___y_1176_);
return v___x_1182_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectExprAux___lam__1___boxed(lean_object* v_e_1183_, lean_object* v_args_1184_, lean_object* v_x_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_){
_start:
{
uint8_t v___y_18179__boxed_1193_; lean_object* v_res_1194_; 
v___y_18179__boxed_1193_ = lean_unbox(v___y_1186_);
v_res_1194_ = l_Lean_Meta_Closure_collectExprAux___lam__1(v_e_1183_, v_args_1184_, v_x_1185_, v___y_18179__boxed_1193_, v___y_1187_, v___y_1188_, v___y_1189_, v___y_1190_, v___y_1191_);
lean_dec(v___y_1191_);
lean_dec_ref(v___y_1190_);
lean_dec(v___y_1189_);
lean_dec_ref(v___y_1188_);
lean_dec(v___y_1187_);
lean_dec_ref(v_x_1185_);
lean_dec_ref(v_args_1184_);
return v_res_1194_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__3_spec__6_spec__10___redArg(lean_object* v_x_1195_, lean_object* v_x_1196_){
_start:
{
if (lean_obj_tag(v_x_1196_) == 0)
{
return v_x_1195_;
}
else
{
lean_object* v_key_1197_; lean_object* v_value_1198_; lean_object* v_tail_1199_; lean_object* v___x_1201_; uint8_t v_isShared_1202_; uint8_t v_isSharedCheck_1222_; 
v_key_1197_ = lean_ctor_get(v_x_1196_, 0);
v_value_1198_ = lean_ctor_get(v_x_1196_, 1);
v_tail_1199_ = lean_ctor_get(v_x_1196_, 2);
v_isSharedCheck_1222_ = !lean_is_exclusive(v_x_1196_);
if (v_isSharedCheck_1222_ == 0)
{
v___x_1201_ = v_x_1196_;
v_isShared_1202_ = v_isSharedCheck_1222_;
goto v_resetjp_1200_;
}
else
{
lean_inc(v_tail_1199_);
lean_inc(v_value_1198_);
lean_inc(v_key_1197_);
lean_dec(v_x_1196_);
v___x_1201_ = lean_box(0);
v_isShared_1202_ = v_isSharedCheck_1222_;
goto v_resetjp_1200_;
}
v_resetjp_1200_:
{
lean_object* v___x_1203_; uint64_t v___x_1204_; uint64_t v___x_1205_; uint64_t v___x_1206_; uint64_t v_fold_1207_; uint64_t v___x_1208_; uint64_t v___x_1209_; uint64_t v___x_1210_; size_t v___x_1211_; size_t v___x_1212_; size_t v___x_1213_; size_t v___x_1214_; size_t v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1218_; 
v___x_1203_ = lean_array_get_size(v_x_1195_);
v___x_1204_ = l_Lean_ExprStructEq_hash(v_key_1197_);
v___x_1205_ = 32ULL;
v___x_1206_ = lean_uint64_shift_right(v___x_1204_, v___x_1205_);
v_fold_1207_ = lean_uint64_xor(v___x_1204_, v___x_1206_);
v___x_1208_ = 16ULL;
v___x_1209_ = lean_uint64_shift_right(v_fold_1207_, v___x_1208_);
v___x_1210_ = lean_uint64_xor(v_fold_1207_, v___x_1209_);
v___x_1211_ = lean_uint64_to_usize(v___x_1210_);
v___x_1212_ = lean_usize_of_nat(v___x_1203_);
v___x_1213_ = ((size_t)1ULL);
v___x_1214_ = lean_usize_sub(v___x_1212_, v___x_1213_);
v___x_1215_ = lean_usize_land(v___x_1211_, v___x_1214_);
v___x_1216_ = lean_array_uget_borrowed(v_x_1195_, v___x_1215_);
lean_inc(v___x_1216_);
if (v_isShared_1202_ == 0)
{
lean_ctor_set(v___x_1201_, 2, v___x_1216_);
v___x_1218_ = v___x_1201_;
goto v_reusejp_1217_;
}
else
{
lean_object* v_reuseFailAlloc_1221_; 
v_reuseFailAlloc_1221_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1221_, 0, v_key_1197_);
lean_ctor_set(v_reuseFailAlloc_1221_, 1, v_value_1198_);
lean_ctor_set(v_reuseFailAlloc_1221_, 2, v___x_1216_);
v___x_1218_ = v_reuseFailAlloc_1221_;
goto v_reusejp_1217_;
}
v_reusejp_1217_:
{
lean_object* v___x_1219_; 
v___x_1219_ = lean_array_uset(v_x_1195_, v___x_1215_, v___x_1218_);
v_x_1195_ = v___x_1219_;
v_x_1196_ = v_tail_1199_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__3_spec__6___redArg(lean_object* v_i_1223_, lean_object* v_source_1224_, lean_object* v_target_1225_){
_start:
{
lean_object* v___x_1226_; uint8_t v___x_1227_; 
v___x_1226_ = lean_array_get_size(v_source_1224_);
v___x_1227_ = lean_nat_dec_lt(v_i_1223_, v___x_1226_);
if (v___x_1227_ == 0)
{
lean_dec_ref(v_source_1224_);
lean_dec(v_i_1223_);
return v_target_1225_;
}
else
{
lean_object* v_es_1228_; lean_object* v___x_1229_; lean_object* v_source_1230_; lean_object* v_target_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; 
v_es_1228_ = lean_array_fget(v_source_1224_, v_i_1223_);
v___x_1229_ = lean_box(0);
v_source_1230_ = lean_array_fset(v_source_1224_, v_i_1223_, v___x_1229_);
v_target_1231_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__3_spec__6_spec__10___redArg(v_target_1225_, v_es_1228_);
v___x_1232_ = lean_unsigned_to_nat(1u);
v___x_1233_ = lean_nat_add(v_i_1223_, v___x_1232_);
lean_dec(v_i_1223_);
v_i_1223_ = v___x_1233_;
v_source_1224_ = v_source_1230_;
v_target_1225_ = v_target_1231_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__3___redArg(lean_object* v_data_1235_){
_start:
{
lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v_nbuckets_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; 
v___x_1236_ = lean_array_get_size(v_data_1235_);
v___x_1237_ = lean_unsigned_to_nat(2u);
v_nbuckets_1238_ = lean_nat_mul(v___x_1236_, v___x_1237_);
v___x_1239_ = lean_unsigned_to_nat(0u);
v___x_1240_ = lean_box(0);
v___x_1241_ = lean_mk_array(v_nbuckets_1238_, v___x_1240_);
v___x_1242_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__3_spec__6___redArg(v___x_1239_, v_data_1235_, v___x_1241_);
return v___x_1242_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__4___redArg(lean_object* v_a_1243_, lean_object* v_b_1244_, lean_object* v_x_1245_){
_start:
{
if (lean_obj_tag(v_x_1245_) == 0)
{
lean_dec(v_b_1244_);
lean_dec_ref(v_a_1243_);
return v_x_1245_;
}
else
{
lean_object* v_key_1246_; lean_object* v_value_1247_; lean_object* v_tail_1248_; lean_object* v___x_1250_; uint8_t v_isShared_1251_; uint8_t v_isSharedCheck_1260_; 
v_key_1246_ = lean_ctor_get(v_x_1245_, 0);
v_value_1247_ = lean_ctor_get(v_x_1245_, 1);
v_tail_1248_ = lean_ctor_get(v_x_1245_, 2);
v_isSharedCheck_1260_ = !lean_is_exclusive(v_x_1245_);
if (v_isSharedCheck_1260_ == 0)
{
v___x_1250_ = v_x_1245_;
v_isShared_1251_ = v_isSharedCheck_1260_;
goto v_resetjp_1249_;
}
else
{
lean_inc(v_tail_1248_);
lean_inc(v_value_1247_);
lean_inc(v_key_1246_);
lean_dec(v_x_1245_);
v___x_1250_ = lean_box(0);
v_isShared_1251_ = v_isSharedCheck_1260_;
goto v_resetjp_1249_;
}
v_resetjp_1249_:
{
uint8_t v___x_1252_; 
v___x_1252_ = l_Lean_ExprStructEq_beq(v_key_1246_, v_a_1243_);
if (v___x_1252_ == 0)
{
lean_object* v___x_1253_; lean_object* v___x_1255_; 
v___x_1253_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__4___redArg(v_a_1243_, v_b_1244_, v_tail_1248_);
if (v_isShared_1251_ == 0)
{
lean_ctor_set(v___x_1250_, 2, v___x_1253_);
v___x_1255_ = v___x_1250_;
goto v_reusejp_1254_;
}
else
{
lean_object* v_reuseFailAlloc_1256_; 
v_reuseFailAlloc_1256_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1256_, 0, v_key_1246_);
lean_ctor_set(v_reuseFailAlloc_1256_, 1, v_value_1247_);
lean_ctor_set(v_reuseFailAlloc_1256_, 2, v___x_1253_);
v___x_1255_ = v_reuseFailAlloc_1256_;
goto v_reusejp_1254_;
}
v_reusejp_1254_:
{
return v___x_1255_;
}
}
else
{
lean_object* v___x_1258_; 
lean_dec(v_value_1247_);
lean_dec(v_key_1246_);
if (v_isShared_1251_ == 0)
{
lean_ctor_set(v___x_1250_, 1, v_b_1244_);
lean_ctor_set(v___x_1250_, 0, v_a_1243_);
v___x_1258_ = v___x_1250_;
goto v_reusejp_1257_;
}
else
{
lean_object* v_reuseFailAlloc_1259_; 
v_reuseFailAlloc_1259_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1259_, 0, v_a_1243_);
lean_ctor_set(v_reuseFailAlloc_1259_, 1, v_b_1244_);
lean_ctor_set(v_reuseFailAlloc_1259_, 2, v_tail_1248_);
v___x_1258_ = v_reuseFailAlloc_1259_;
goto v_reusejp_1257_;
}
v_reusejp_1257_:
{
return v___x_1258_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__2___redArg(lean_object* v_a_1261_, lean_object* v_x_1262_){
_start:
{
if (lean_obj_tag(v_x_1262_) == 0)
{
uint8_t v___x_1263_; 
v___x_1263_ = 0;
return v___x_1263_;
}
else
{
lean_object* v_key_1264_; lean_object* v_tail_1265_; uint8_t v___x_1266_; 
v_key_1264_ = lean_ctor_get(v_x_1262_, 0);
v_tail_1265_ = lean_ctor_get(v_x_1262_, 2);
v___x_1266_ = l_Lean_ExprStructEq_beq(v_key_1264_, v_a_1261_);
if (v___x_1266_ == 0)
{
v_x_1262_ = v_tail_1265_;
goto _start;
}
else
{
return v___x_1266_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__2___redArg___boxed(lean_object* v_a_1268_, lean_object* v_x_1269_){
_start:
{
uint8_t v_res_1270_; lean_object* v_r_1271_; 
v_res_1270_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__2___redArg(v_a_1268_, v_x_1269_);
lean_dec(v_x_1269_);
lean_dec_ref(v_a_1268_);
v_r_1271_ = lean_box(v_res_1270_);
return v_r_1271_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1___redArg(lean_object* v_m_1272_, lean_object* v_a_1273_, lean_object* v_b_1274_){
_start:
{
lean_object* v_size_1275_; lean_object* v_buckets_1276_; lean_object* v___x_1278_; uint8_t v_isShared_1279_; uint8_t v_isSharedCheck_1319_; 
v_size_1275_ = lean_ctor_get(v_m_1272_, 0);
v_buckets_1276_ = lean_ctor_get(v_m_1272_, 1);
v_isSharedCheck_1319_ = !lean_is_exclusive(v_m_1272_);
if (v_isSharedCheck_1319_ == 0)
{
v___x_1278_ = v_m_1272_;
v_isShared_1279_ = v_isSharedCheck_1319_;
goto v_resetjp_1277_;
}
else
{
lean_inc(v_buckets_1276_);
lean_inc(v_size_1275_);
lean_dec(v_m_1272_);
v___x_1278_ = lean_box(0);
v_isShared_1279_ = v_isSharedCheck_1319_;
goto v_resetjp_1277_;
}
v_resetjp_1277_:
{
lean_object* v___x_1280_; uint64_t v___x_1281_; uint64_t v___x_1282_; uint64_t v___x_1283_; uint64_t v_fold_1284_; uint64_t v___x_1285_; uint64_t v___x_1286_; uint64_t v___x_1287_; size_t v___x_1288_; size_t v___x_1289_; size_t v___x_1290_; size_t v___x_1291_; size_t v___x_1292_; lean_object* v_bkt_1293_; uint8_t v___x_1294_; 
v___x_1280_ = lean_array_get_size(v_buckets_1276_);
v___x_1281_ = l_Lean_ExprStructEq_hash(v_a_1273_);
v___x_1282_ = 32ULL;
v___x_1283_ = lean_uint64_shift_right(v___x_1281_, v___x_1282_);
v_fold_1284_ = lean_uint64_xor(v___x_1281_, v___x_1283_);
v___x_1285_ = 16ULL;
v___x_1286_ = lean_uint64_shift_right(v_fold_1284_, v___x_1285_);
v___x_1287_ = lean_uint64_xor(v_fold_1284_, v___x_1286_);
v___x_1288_ = lean_uint64_to_usize(v___x_1287_);
v___x_1289_ = lean_usize_of_nat(v___x_1280_);
v___x_1290_ = ((size_t)1ULL);
v___x_1291_ = lean_usize_sub(v___x_1289_, v___x_1290_);
v___x_1292_ = lean_usize_land(v___x_1288_, v___x_1291_);
v_bkt_1293_ = lean_array_uget_borrowed(v_buckets_1276_, v___x_1292_);
v___x_1294_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__2___redArg(v_a_1273_, v_bkt_1293_);
if (v___x_1294_ == 0)
{
lean_object* v___x_1295_; lean_object* v_size_x27_1296_; lean_object* v___x_1297_; lean_object* v_buckets_x27_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; uint8_t v___x_1304_; 
v___x_1295_ = lean_unsigned_to_nat(1u);
v_size_x27_1296_ = lean_nat_add(v_size_1275_, v___x_1295_);
lean_dec(v_size_1275_);
lean_inc(v_bkt_1293_);
v___x_1297_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1297_, 0, v_a_1273_);
lean_ctor_set(v___x_1297_, 1, v_b_1274_);
lean_ctor_set(v___x_1297_, 2, v_bkt_1293_);
v_buckets_x27_1298_ = lean_array_uset(v_buckets_1276_, v___x_1292_, v___x_1297_);
v___x_1299_ = lean_unsigned_to_nat(4u);
v___x_1300_ = lean_nat_mul(v_size_x27_1296_, v___x_1299_);
v___x_1301_ = lean_unsigned_to_nat(3u);
v___x_1302_ = lean_nat_div(v___x_1300_, v___x_1301_);
lean_dec(v___x_1300_);
v___x_1303_ = lean_array_get_size(v_buckets_x27_1298_);
v___x_1304_ = lean_nat_dec_le(v___x_1302_, v___x_1303_);
lean_dec(v___x_1302_);
if (v___x_1304_ == 0)
{
lean_object* v_val_1305_; lean_object* v___x_1307_; 
v_val_1305_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__3___redArg(v_buckets_x27_1298_);
if (v_isShared_1279_ == 0)
{
lean_ctor_set(v___x_1278_, 1, v_val_1305_);
lean_ctor_set(v___x_1278_, 0, v_size_x27_1296_);
v___x_1307_ = v___x_1278_;
goto v_reusejp_1306_;
}
else
{
lean_object* v_reuseFailAlloc_1308_; 
v_reuseFailAlloc_1308_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1308_, 0, v_size_x27_1296_);
lean_ctor_set(v_reuseFailAlloc_1308_, 1, v_val_1305_);
v___x_1307_ = v_reuseFailAlloc_1308_;
goto v_reusejp_1306_;
}
v_reusejp_1306_:
{
return v___x_1307_;
}
}
else
{
lean_object* v___x_1310_; 
if (v_isShared_1279_ == 0)
{
lean_ctor_set(v___x_1278_, 1, v_buckets_x27_1298_);
lean_ctor_set(v___x_1278_, 0, v_size_x27_1296_);
v___x_1310_ = v___x_1278_;
goto v_reusejp_1309_;
}
else
{
lean_object* v_reuseFailAlloc_1311_; 
v_reuseFailAlloc_1311_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1311_, 0, v_size_x27_1296_);
lean_ctor_set(v_reuseFailAlloc_1311_, 1, v_buckets_x27_1298_);
v___x_1310_ = v_reuseFailAlloc_1311_;
goto v_reusejp_1309_;
}
v_reusejp_1309_:
{
return v___x_1310_;
}
}
}
else
{
lean_object* v___x_1312_; lean_object* v_buckets_x27_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1317_; 
lean_inc(v_bkt_1293_);
v___x_1312_ = lean_box(0);
v_buckets_x27_1313_ = lean_array_uset(v_buckets_1276_, v___x_1292_, v___x_1312_);
v___x_1314_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__4___redArg(v_a_1273_, v_b_1274_, v_bkt_1293_);
v___x_1315_ = lean_array_uset(v_buckets_x27_1313_, v___x_1292_, v___x_1314_);
if (v_isShared_1279_ == 0)
{
lean_ctor_set(v___x_1278_, 1, v___x_1315_);
v___x_1317_ = v___x_1278_;
goto v_reusejp_1316_;
}
else
{
lean_object* v_reuseFailAlloc_1318_; 
v_reuseFailAlloc_1318_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1318_, 0, v_size_1275_);
lean_ctor_set(v_reuseFailAlloc_1318_, 1, v___x_1315_);
v___x_1317_ = v_reuseFailAlloc_1318_;
goto v_reusejp_1316_;
}
v_reusejp_1316_:
{
return v___x_1317_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectExprAux(lean_object* v_e_1320_, uint8_t v_a_1321_, lean_object* v_a_1322_, lean_object* v_a_1323_, lean_object* v_a_1324_, lean_object* v_a_1325_, lean_object* v_a_1326_){
_start:
{
switch(lean_obj_tag(v_e_1320_))
{
case 11:
{
lean_object* v_typeName_1328_; lean_object* v_idx_1329_; lean_object* v_struct_1330_; lean_object* v___x_1331_; 
v_typeName_1328_ = lean_ctor_get(v_e_1320_, 0);
v_idx_1329_ = lean_ctor_get(v_e_1320_, 1);
v_struct_1330_ = lean_ctor_get(v_e_1320_, 2);
lean_inc_ref(v_struct_1330_);
v___x_1331_ = l_Lean_Meta_Closure_collectExprAux___lam__0(v_struct_1330_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_, v_a_1325_, v_a_1326_);
if (lean_obj_tag(v___x_1331_) == 0)
{
lean_object* v_a_1332_; lean_object* v___x_1334_; uint8_t v_isShared_1335_; uint8_t v_isSharedCheck_1346_; 
v_a_1332_ = lean_ctor_get(v___x_1331_, 0);
v_isSharedCheck_1346_ = !lean_is_exclusive(v___x_1331_);
if (v_isSharedCheck_1346_ == 0)
{
v___x_1334_ = v___x_1331_;
v_isShared_1335_ = v_isSharedCheck_1346_;
goto v_resetjp_1333_;
}
else
{
lean_inc(v_a_1332_);
lean_dec(v___x_1331_);
v___x_1334_ = lean_box(0);
v_isShared_1335_ = v_isSharedCheck_1346_;
goto v_resetjp_1333_;
}
v_resetjp_1333_:
{
size_t v___x_1336_; size_t v___x_1337_; uint8_t v___x_1338_; 
v___x_1336_ = lean_ptr_addr(v_struct_1330_);
v___x_1337_ = lean_ptr_addr(v_a_1332_);
v___x_1338_ = lean_usize_dec_eq(v___x_1336_, v___x_1337_);
if (v___x_1338_ == 0)
{
lean_object* v___x_1339_; lean_object* v___x_1341_; 
lean_inc(v_idx_1329_);
lean_inc(v_typeName_1328_);
lean_dec_ref(v_e_1320_);
v___x_1339_ = l_Lean_Expr_proj___override(v_typeName_1328_, v_idx_1329_, v_a_1332_);
if (v_isShared_1335_ == 0)
{
lean_ctor_set(v___x_1334_, 0, v___x_1339_);
v___x_1341_ = v___x_1334_;
goto v_reusejp_1340_;
}
else
{
lean_object* v_reuseFailAlloc_1342_; 
v_reuseFailAlloc_1342_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1342_, 0, v___x_1339_);
v___x_1341_ = v_reuseFailAlloc_1342_;
goto v_reusejp_1340_;
}
v_reusejp_1340_:
{
return v___x_1341_;
}
}
else
{
lean_object* v___x_1344_; 
lean_dec(v_a_1332_);
if (v_isShared_1335_ == 0)
{
lean_ctor_set(v___x_1334_, 0, v_e_1320_);
v___x_1344_ = v___x_1334_;
goto v_reusejp_1343_;
}
else
{
lean_object* v_reuseFailAlloc_1345_; 
v_reuseFailAlloc_1345_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1345_, 0, v_e_1320_);
v___x_1344_ = v_reuseFailAlloc_1345_;
goto v_reusejp_1343_;
}
v_reusejp_1343_:
{
return v___x_1344_;
}
}
}
}
else
{
lean_dec_ref(v_e_1320_);
return v___x_1331_;
}
}
case 7:
{
lean_object* v_binderName_1347_; lean_object* v_binderType_1348_; lean_object* v_body_1349_; uint8_t v_binderInfo_1350_; lean_object* v___x_1351_; 
v_binderName_1347_ = lean_ctor_get(v_e_1320_, 0);
v_binderType_1348_ = lean_ctor_get(v_e_1320_, 1);
v_body_1349_ = lean_ctor_get(v_e_1320_, 2);
v_binderInfo_1350_ = lean_ctor_get_uint8(v_e_1320_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_1348_);
v___x_1351_ = l_Lean_Meta_Closure_collectExprAux___lam__0(v_binderType_1348_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_, v_a_1325_, v_a_1326_);
if (lean_obj_tag(v___x_1351_) == 0)
{
lean_object* v_a_1352_; lean_object* v___x_1353_; 
v_a_1352_ = lean_ctor_get(v___x_1351_, 0);
lean_inc(v_a_1352_);
lean_dec_ref(v___x_1351_);
lean_inc_ref(v_body_1349_);
v___x_1353_ = l_Lean_Meta_Closure_collectExprAux___lam__0(v_body_1349_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_, v_a_1325_, v_a_1326_);
if (lean_obj_tag(v___x_1353_) == 0)
{
lean_object* v_a_1354_; lean_object* v___x_1356_; uint8_t v_isShared_1357_; uint8_t v_isSharedCheck_1378_; 
v_a_1354_ = lean_ctor_get(v___x_1353_, 0);
v_isSharedCheck_1378_ = !lean_is_exclusive(v___x_1353_);
if (v_isSharedCheck_1378_ == 0)
{
v___x_1356_ = v___x_1353_;
v_isShared_1357_ = v_isSharedCheck_1378_;
goto v_resetjp_1355_;
}
else
{
lean_inc(v_a_1354_);
lean_dec(v___x_1353_);
v___x_1356_ = lean_box(0);
v_isShared_1357_ = v_isSharedCheck_1378_;
goto v_resetjp_1355_;
}
v_resetjp_1355_:
{
uint8_t v___y_1359_; size_t v___x_1372_; size_t v___x_1373_; uint8_t v___x_1374_; 
v___x_1372_ = lean_ptr_addr(v_binderType_1348_);
v___x_1373_ = lean_ptr_addr(v_a_1352_);
v___x_1374_ = lean_usize_dec_eq(v___x_1372_, v___x_1373_);
if (v___x_1374_ == 0)
{
v___y_1359_ = v___x_1374_;
goto v___jp_1358_;
}
else
{
size_t v___x_1375_; size_t v___x_1376_; uint8_t v___x_1377_; 
v___x_1375_ = lean_ptr_addr(v_body_1349_);
v___x_1376_ = lean_ptr_addr(v_a_1354_);
v___x_1377_ = lean_usize_dec_eq(v___x_1375_, v___x_1376_);
v___y_1359_ = v___x_1377_;
goto v___jp_1358_;
}
v___jp_1358_:
{
if (v___y_1359_ == 0)
{
lean_object* v___x_1360_; lean_object* v___x_1362_; 
lean_inc(v_binderName_1347_);
lean_dec_ref(v_e_1320_);
v___x_1360_ = l_Lean_Expr_forallE___override(v_binderName_1347_, v_a_1352_, v_a_1354_, v_binderInfo_1350_);
if (v_isShared_1357_ == 0)
{
lean_ctor_set(v___x_1356_, 0, v___x_1360_);
v___x_1362_ = v___x_1356_;
goto v_reusejp_1361_;
}
else
{
lean_object* v_reuseFailAlloc_1363_; 
v_reuseFailAlloc_1363_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1363_, 0, v___x_1360_);
v___x_1362_ = v_reuseFailAlloc_1363_;
goto v_reusejp_1361_;
}
v_reusejp_1361_:
{
return v___x_1362_;
}
}
else
{
uint8_t v___x_1364_; 
v___x_1364_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_1350_, v_binderInfo_1350_);
if (v___x_1364_ == 0)
{
lean_object* v___x_1365_; lean_object* v___x_1367_; 
lean_inc(v_binderName_1347_);
lean_dec_ref(v_e_1320_);
v___x_1365_ = l_Lean_Expr_forallE___override(v_binderName_1347_, v_a_1352_, v_a_1354_, v_binderInfo_1350_);
if (v_isShared_1357_ == 0)
{
lean_ctor_set(v___x_1356_, 0, v___x_1365_);
v___x_1367_ = v___x_1356_;
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
lean_object* v___x_1370_; 
lean_dec(v_a_1354_);
lean_dec(v_a_1352_);
if (v_isShared_1357_ == 0)
{
lean_ctor_set(v___x_1356_, 0, v_e_1320_);
v___x_1370_ = v___x_1356_;
goto v_reusejp_1369_;
}
else
{
lean_object* v_reuseFailAlloc_1371_; 
v_reuseFailAlloc_1371_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1371_, 0, v_e_1320_);
v___x_1370_ = v_reuseFailAlloc_1371_;
goto v_reusejp_1369_;
}
v_reusejp_1369_:
{
return v___x_1370_;
}
}
}
}
}
}
else
{
lean_dec(v_a_1352_);
lean_dec_ref(v_e_1320_);
return v___x_1353_;
}
}
else
{
lean_dec_ref(v_e_1320_);
return v___x_1351_;
}
}
case 6:
{
lean_object* v_binderName_1379_; lean_object* v_binderType_1380_; lean_object* v_body_1381_; uint8_t v_binderInfo_1382_; lean_object* v___x_1383_; 
v_binderName_1379_ = lean_ctor_get(v_e_1320_, 0);
v_binderType_1380_ = lean_ctor_get(v_e_1320_, 1);
v_body_1381_ = lean_ctor_get(v_e_1320_, 2);
v_binderInfo_1382_ = lean_ctor_get_uint8(v_e_1320_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_1380_);
v___x_1383_ = l_Lean_Meta_Closure_collectExprAux___lam__0(v_binderType_1380_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_, v_a_1325_, v_a_1326_);
if (lean_obj_tag(v___x_1383_) == 0)
{
lean_object* v_a_1384_; lean_object* v___x_1385_; 
v_a_1384_ = lean_ctor_get(v___x_1383_, 0);
lean_inc(v_a_1384_);
lean_dec_ref(v___x_1383_);
lean_inc_ref(v_body_1381_);
v___x_1385_ = l_Lean_Meta_Closure_collectExprAux___lam__0(v_body_1381_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_, v_a_1325_, v_a_1326_);
if (lean_obj_tag(v___x_1385_) == 0)
{
lean_object* v_a_1386_; lean_object* v___x_1388_; uint8_t v_isShared_1389_; uint8_t v_isSharedCheck_1410_; 
v_a_1386_ = lean_ctor_get(v___x_1385_, 0);
v_isSharedCheck_1410_ = !lean_is_exclusive(v___x_1385_);
if (v_isSharedCheck_1410_ == 0)
{
v___x_1388_ = v___x_1385_;
v_isShared_1389_ = v_isSharedCheck_1410_;
goto v_resetjp_1387_;
}
else
{
lean_inc(v_a_1386_);
lean_dec(v___x_1385_);
v___x_1388_ = lean_box(0);
v_isShared_1389_ = v_isSharedCheck_1410_;
goto v_resetjp_1387_;
}
v_resetjp_1387_:
{
uint8_t v___y_1391_; size_t v___x_1404_; size_t v___x_1405_; uint8_t v___x_1406_; 
v___x_1404_ = lean_ptr_addr(v_binderType_1380_);
v___x_1405_ = lean_ptr_addr(v_a_1384_);
v___x_1406_ = lean_usize_dec_eq(v___x_1404_, v___x_1405_);
if (v___x_1406_ == 0)
{
v___y_1391_ = v___x_1406_;
goto v___jp_1390_;
}
else
{
size_t v___x_1407_; size_t v___x_1408_; uint8_t v___x_1409_; 
v___x_1407_ = lean_ptr_addr(v_body_1381_);
v___x_1408_ = lean_ptr_addr(v_a_1386_);
v___x_1409_ = lean_usize_dec_eq(v___x_1407_, v___x_1408_);
v___y_1391_ = v___x_1409_;
goto v___jp_1390_;
}
v___jp_1390_:
{
if (v___y_1391_ == 0)
{
lean_object* v___x_1392_; lean_object* v___x_1394_; 
lean_inc(v_binderName_1379_);
lean_dec_ref(v_e_1320_);
v___x_1392_ = l_Lean_Expr_lam___override(v_binderName_1379_, v_a_1384_, v_a_1386_, v_binderInfo_1382_);
if (v_isShared_1389_ == 0)
{
lean_ctor_set(v___x_1388_, 0, v___x_1392_);
v___x_1394_ = v___x_1388_;
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
uint8_t v___x_1396_; 
v___x_1396_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_1382_, v_binderInfo_1382_);
if (v___x_1396_ == 0)
{
lean_object* v___x_1397_; lean_object* v___x_1399_; 
lean_inc(v_binderName_1379_);
lean_dec_ref(v_e_1320_);
v___x_1397_ = l_Lean_Expr_lam___override(v_binderName_1379_, v_a_1384_, v_a_1386_, v_binderInfo_1382_);
if (v_isShared_1389_ == 0)
{
lean_ctor_set(v___x_1388_, 0, v___x_1397_);
v___x_1399_ = v___x_1388_;
goto v_reusejp_1398_;
}
else
{
lean_object* v_reuseFailAlloc_1400_; 
v_reuseFailAlloc_1400_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1400_, 0, v___x_1397_);
v___x_1399_ = v_reuseFailAlloc_1400_;
goto v_reusejp_1398_;
}
v_reusejp_1398_:
{
return v___x_1399_;
}
}
else
{
lean_object* v___x_1402_; 
lean_dec(v_a_1386_);
lean_dec(v_a_1384_);
if (v_isShared_1389_ == 0)
{
lean_ctor_set(v___x_1388_, 0, v_e_1320_);
v___x_1402_ = v___x_1388_;
goto v_reusejp_1401_;
}
else
{
lean_object* v_reuseFailAlloc_1403_; 
v_reuseFailAlloc_1403_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1403_, 0, v_e_1320_);
v___x_1402_ = v_reuseFailAlloc_1403_;
goto v_reusejp_1401_;
}
v_reusejp_1401_:
{
return v___x_1402_;
}
}
}
}
}
}
else
{
lean_dec(v_a_1384_);
lean_dec_ref(v_e_1320_);
return v___x_1385_;
}
}
else
{
lean_dec_ref(v_e_1320_);
return v___x_1383_;
}
}
case 8:
{
lean_object* v_declName_1411_; lean_object* v_type_1412_; lean_object* v_value_1413_; lean_object* v_body_1414_; uint8_t v_nondep_1415_; lean_object* v___x_1416_; 
v_declName_1411_ = lean_ctor_get(v_e_1320_, 0);
v_type_1412_ = lean_ctor_get(v_e_1320_, 1);
v_value_1413_ = lean_ctor_get(v_e_1320_, 2);
v_body_1414_ = lean_ctor_get(v_e_1320_, 3);
v_nondep_1415_ = lean_ctor_get_uint8(v_e_1320_, sizeof(void*)*4 + 8);
lean_inc_ref(v_type_1412_);
v___x_1416_ = l_Lean_Meta_Closure_collectExprAux___lam__0(v_type_1412_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_, v_a_1325_, v_a_1326_);
if (lean_obj_tag(v___x_1416_) == 0)
{
lean_object* v_a_1417_; lean_object* v___x_1418_; 
v_a_1417_ = lean_ctor_get(v___x_1416_, 0);
lean_inc(v_a_1417_);
lean_dec_ref(v___x_1416_);
lean_inc_ref(v_value_1413_);
v___x_1418_ = l_Lean_Meta_Closure_collectExprAux___lam__0(v_value_1413_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_, v_a_1325_, v_a_1326_);
if (lean_obj_tag(v___x_1418_) == 0)
{
lean_object* v_a_1419_; lean_object* v___x_1420_; 
v_a_1419_ = lean_ctor_get(v___x_1418_, 0);
lean_inc(v_a_1419_);
lean_dec_ref(v___x_1418_);
lean_inc_ref(v_body_1414_);
v___x_1420_ = l_Lean_Meta_Closure_collectExprAux___lam__0(v_body_1414_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_, v_a_1325_, v_a_1326_);
if (lean_obj_tag(v___x_1420_) == 0)
{
lean_object* v_a_1421_; lean_object* v___x_1423_; uint8_t v_isShared_1424_; uint8_t v_isSharedCheck_1447_; 
v_a_1421_ = lean_ctor_get(v___x_1420_, 0);
v_isSharedCheck_1447_ = !lean_is_exclusive(v___x_1420_);
if (v_isSharedCheck_1447_ == 0)
{
v___x_1423_ = v___x_1420_;
v_isShared_1424_ = v_isSharedCheck_1447_;
goto v_resetjp_1422_;
}
else
{
lean_inc(v_a_1421_);
lean_dec(v___x_1420_);
v___x_1423_ = lean_box(0);
v_isShared_1424_ = v_isSharedCheck_1447_;
goto v_resetjp_1422_;
}
v_resetjp_1422_:
{
uint8_t v___y_1426_; size_t v___x_1441_; size_t v___x_1442_; uint8_t v___x_1443_; 
v___x_1441_ = lean_ptr_addr(v_type_1412_);
v___x_1442_ = lean_ptr_addr(v_a_1417_);
v___x_1443_ = lean_usize_dec_eq(v___x_1441_, v___x_1442_);
if (v___x_1443_ == 0)
{
v___y_1426_ = v___x_1443_;
goto v___jp_1425_;
}
else
{
size_t v___x_1444_; size_t v___x_1445_; uint8_t v___x_1446_; 
v___x_1444_ = lean_ptr_addr(v_value_1413_);
v___x_1445_ = lean_ptr_addr(v_a_1419_);
v___x_1446_ = lean_usize_dec_eq(v___x_1444_, v___x_1445_);
v___y_1426_ = v___x_1446_;
goto v___jp_1425_;
}
v___jp_1425_:
{
if (v___y_1426_ == 0)
{
lean_object* v___x_1427_; lean_object* v___x_1429_; 
lean_inc(v_declName_1411_);
lean_dec_ref(v_e_1320_);
v___x_1427_ = l_Lean_Expr_letE___override(v_declName_1411_, v_a_1417_, v_a_1419_, v_a_1421_, v_nondep_1415_);
if (v_isShared_1424_ == 0)
{
lean_ctor_set(v___x_1423_, 0, v___x_1427_);
v___x_1429_ = v___x_1423_;
goto v_reusejp_1428_;
}
else
{
lean_object* v_reuseFailAlloc_1430_; 
v_reuseFailAlloc_1430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1430_, 0, v___x_1427_);
v___x_1429_ = v_reuseFailAlloc_1430_;
goto v_reusejp_1428_;
}
v_reusejp_1428_:
{
return v___x_1429_;
}
}
else
{
size_t v___x_1431_; size_t v___x_1432_; uint8_t v___x_1433_; 
v___x_1431_ = lean_ptr_addr(v_body_1414_);
v___x_1432_ = lean_ptr_addr(v_a_1421_);
v___x_1433_ = lean_usize_dec_eq(v___x_1431_, v___x_1432_);
if (v___x_1433_ == 0)
{
lean_object* v___x_1434_; lean_object* v___x_1436_; 
lean_inc(v_declName_1411_);
lean_dec_ref(v_e_1320_);
v___x_1434_ = l_Lean_Expr_letE___override(v_declName_1411_, v_a_1417_, v_a_1419_, v_a_1421_, v_nondep_1415_);
if (v_isShared_1424_ == 0)
{
lean_ctor_set(v___x_1423_, 0, v___x_1434_);
v___x_1436_ = v___x_1423_;
goto v_reusejp_1435_;
}
else
{
lean_object* v_reuseFailAlloc_1437_; 
v_reuseFailAlloc_1437_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1437_, 0, v___x_1434_);
v___x_1436_ = v_reuseFailAlloc_1437_;
goto v_reusejp_1435_;
}
v_reusejp_1435_:
{
return v___x_1436_;
}
}
else
{
lean_object* v___x_1439_; 
lean_dec(v_a_1421_);
lean_dec(v_a_1419_);
lean_dec(v_a_1417_);
if (v_isShared_1424_ == 0)
{
lean_ctor_set(v___x_1423_, 0, v_e_1320_);
v___x_1439_ = v___x_1423_;
goto v_reusejp_1438_;
}
else
{
lean_object* v_reuseFailAlloc_1440_; 
v_reuseFailAlloc_1440_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1440_, 0, v_e_1320_);
v___x_1439_ = v_reuseFailAlloc_1440_;
goto v_reusejp_1438_;
}
v_reusejp_1438_:
{
return v___x_1439_;
}
}
}
}
}
}
else
{
lean_dec(v_a_1419_);
lean_dec(v_a_1417_);
lean_dec_ref(v_e_1320_);
return v___x_1420_;
}
}
else
{
lean_dec(v_a_1417_);
lean_dec_ref(v_e_1320_);
return v___x_1418_;
}
}
else
{
lean_dec_ref(v_e_1320_);
return v___x_1416_;
}
}
case 5:
{
lean_object* v_fn_1448_; lean_object* v_arg_1449_; lean_object* v___x_1450_; 
v_fn_1448_ = lean_ctor_get(v_e_1320_, 0);
v_arg_1449_ = lean_ctor_get(v_e_1320_, 1);
lean_inc_ref(v_fn_1448_);
v___x_1450_ = l_Lean_Meta_Closure_collectExprAux___lam__0(v_fn_1448_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_, v_a_1325_, v_a_1326_);
if (lean_obj_tag(v___x_1450_) == 0)
{
lean_object* v_a_1451_; lean_object* v___x_1452_; 
v_a_1451_ = lean_ctor_get(v___x_1450_, 0);
lean_inc(v_a_1451_);
lean_dec_ref(v___x_1450_);
lean_inc_ref(v_arg_1449_);
v___x_1452_ = l_Lean_Meta_Closure_collectExprAux___lam__0(v_arg_1449_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_, v_a_1325_, v_a_1326_);
if (lean_obj_tag(v___x_1452_) == 0)
{
lean_object* v_a_1453_; lean_object* v___x_1455_; uint8_t v_isShared_1456_; uint8_t v_isSharedCheck_1472_; 
v_a_1453_ = lean_ctor_get(v___x_1452_, 0);
v_isSharedCheck_1472_ = !lean_is_exclusive(v___x_1452_);
if (v_isSharedCheck_1472_ == 0)
{
v___x_1455_ = v___x_1452_;
v_isShared_1456_ = v_isSharedCheck_1472_;
goto v_resetjp_1454_;
}
else
{
lean_inc(v_a_1453_);
lean_dec(v___x_1452_);
v___x_1455_ = lean_box(0);
v_isShared_1456_ = v_isSharedCheck_1472_;
goto v_resetjp_1454_;
}
v_resetjp_1454_:
{
uint8_t v___y_1458_; size_t v___x_1466_; size_t v___x_1467_; uint8_t v___x_1468_; 
v___x_1466_ = lean_ptr_addr(v_fn_1448_);
v___x_1467_ = lean_ptr_addr(v_a_1451_);
v___x_1468_ = lean_usize_dec_eq(v___x_1466_, v___x_1467_);
if (v___x_1468_ == 0)
{
v___y_1458_ = v___x_1468_;
goto v___jp_1457_;
}
else
{
size_t v___x_1469_; size_t v___x_1470_; uint8_t v___x_1471_; 
v___x_1469_ = lean_ptr_addr(v_arg_1449_);
v___x_1470_ = lean_ptr_addr(v_a_1453_);
v___x_1471_ = lean_usize_dec_eq(v___x_1469_, v___x_1470_);
v___y_1458_ = v___x_1471_;
goto v___jp_1457_;
}
v___jp_1457_:
{
if (v___y_1458_ == 0)
{
lean_object* v___x_1459_; lean_object* v___x_1461_; 
lean_dec_ref(v_e_1320_);
v___x_1459_ = l_Lean_Expr_app___override(v_a_1451_, v_a_1453_);
if (v_isShared_1456_ == 0)
{
lean_ctor_set(v___x_1455_, 0, v___x_1459_);
v___x_1461_ = v___x_1455_;
goto v_reusejp_1460_;
}
else
{
lean_object* v_reuseFailAlloc_1462_; 
v_reuseFailAlloc_1462_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1462_, 0, v___x_1459_);
v___x_1461_ = v_reuseFailAlloc_1462_;
goto v_reusejp_1460_;
}
v_reusejp_1460_:
{
return v___x_1461_;
}
}
else
{
lean_object* v___x_1464_; 
lean_dec(v_a_1453_);
lean_dec(v_a_1451_);
if (v_isShared_1456_ == 0)
{
lean_ctor_set(v___x_1455_, 0, v_e_1320_);
v___x_1464_ = v___x_1455_;
goto v_reusejp_1463_;
}
else
{
lean_object* v_reuseFailAlloc_1465_; 
v_reuseFailAlloc_1465_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1465_, 0, v_e_1320_);
v___x_1464_ = v_reuseFailAlloc_1465_;
goto v_reusejp_1463_;
}
v_reusejp_1463_:
{
return v___x_1464_;
}
}
}
}
}
else
{
lean_dec(v_a_1451_);
lean_dec_ref(v_e_1320_);
return v___x_1452_;
}
}
else
{
lean_dec_ref(v_e_1320_);
return v___x_1450_;
}
}
case 10:
{
lean_object* v_data_1473_; lean_object* v_expr_1474_; lean_object* v___x_1475_; 
v_data_1473_ = lean_ctor_get(v_e_1320_, 0);
v_expr_1474_ = lean_ctor_get(v_e_1320_, 1);
lean_inc_ref(v_expr_1474_);
v___x_1475_ = l_Lean_Meta_Closure_collectExprAux___lam__0(v_expr_1474_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_, v_a_1325_, v_a_1326_);
if (lean_obj_tag(v___x_1475_) == 0)
{
lean_object* v_a_1476_; lean_object* v___x_1478_; uint8_t v_isShared_1479_; uint8_t v_isSharedCheck_1490_; 
v_a_1476_ = lean_ctor_get(v___x_1475_, 0);
v_isSharedCheck_1490_ = !lean_is_exclusive(v___x_1475_);
if (v_isSharedCheck_1490_ == 0)
{
v___x_1478_ = v___x_1475_;
v_isShared_1479_ = v_isSharedCheck_1490_;
goto v_resetjp_1477_;
}
else
{
lean_inc(v_a_1476_);
lean_dec(v___x_1475_);
v___x_1478_ = lean_box(0);
v_isShared_1479_ = v_isSharedCheck_1490_;
goto v_resetjp_1477_;
}
v_resetjp_1477_:
{
size_t v___x_1480_; size_t v___x_1481_; uint8_t v___x_1482_; 
v___x_1480_ = lean_ptr_addr(v_expr_1474_);
v___x_1481_ = lean_ptr_addr(v_a_1476_);
v___x_1482_ = lean_usize_dec_eq(v___x_1480_, v___x_1481_);
if (v___x_1482_ == 0)
{
lean_object* v___x_1483_; lean_object* v___x_1485_; 
lean_inc(v_data_1473_);
lean_dec_ref(v_e_1320_);
v___x_1483_ = l_Lean_Expr_mdata___override(v_data_1473_, v_a_1476_);
if (v_isShared_1479_ == 0)
{
lean_ctor_set(v___x_1478_, 0, v___x_1483_);
v___x_1485_ = v___x_1478_;
goto v_reusejp_1484_;
}
else
{
lean_object* v_reuseFailAlloc_1486_; 
v_reuseFailAlloc_1486_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1486_, 0, v___x_1483_);
v___x_1485_ = v_reuseFailAlloc_1486_;
goto v_reusejp_1484_;
}
v_reusejp_1484_:
{
return v___x_1485_;
}
}
else
{
lean_object* v___x_1488_; 
lean_dec(v_a_1476_);
if (v_isShared_1479_ == 0)
{
lean_ctor_set(v___x_1478_, 0, v_e_1320_);
v___x_1488_ = v___x_1478_;
goto v_reusejp_1487_;
}
else
{
lean_object* v_reuseFailAlloc_1489_; 
v_reuseFailAlloc_1489_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1489_, 0, v_e_1320_);
v___x_1488_ = v_reuseFailAlloc_1489_;
goto v_reusejp_1487_;
}
v_reusejp_1487_:
{
return v___x_1488_;
}
}
}
}
else
{
lean_dec_ref(v_e_1320_);
return v___x_1475_;
}
}
case 3:
{
lean_object* v_u_1491_; lean_object* v___x_1492_; 
v_u_1491_ = lean_ctor_get(v_e_1320_, 0);
lean_inc(v_u_1491_);
v___x_1492_ = l_Lean_Meta_Closure_collectLevel___redArg(v_u_1491_, v_a_1322_);
if (lean_obj_tag(v___x_1492_) == 0)
{
lean_object* v_a_1493_; lean_object* v___x_1495_; uint8_t v_isShared_1496_; uint8_t v_isSharedCheck_1507_; 
v_a_1493_ = lean_ctor_get(v___x_1492_, 0);
v_isSharedCheck_1507_ = !lean_is_exclusive(v___x_1492_);
if (v_isSharedCheck_1507_ == 0)
{
v___x_1495_ = v___x_1492_;
v_isShared_1496_ = v_isSharedCheck_1507_;
goto v_resetjp_1494_;
}
else
{
lean_inc(v_a_1493_);
lean_dec(v___x_1492_);
v___x_1495_ = lean_box(0);
v_isShared_1496_ = v_isSharedCheck_1507_;
goto v_resetjp_1494_;
}
v_resetjp_1494_:
{
size_t v___x_1497_; size_t v___x_1498_; uint8_t v___x_1499_; 
v___x_1497_ = lean_ptr_addr(v_u_1491_);
v___x_1498_ = lean_ptr_addr(v_a_1493_);
v___x_1499_ = lean_usize_dec_eq(v___x_1497_, v___x_1498_);
if (v___x_1499_ == 0)
{
lean_object* v___x_1500_; lean_object* v___x_1502_; 
lean_dec_ref(v_e_1320_);
v___x_1500_ = l_Lean_Expr_sort___override(v_a_1493_);
if (v_isShared_1496_ == 0)
{
lean_ctor_set(v___x_1495_, 0, v___x_1500_);
v___x_1502_ = v___x_1495_;
goto v_reusejp_1501_;
}
else
{
lean_object* v_reuseFailAlloc_1503_; 
v_reuseFailAlloc_1503_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1503_, 0, v___x_1500_);
v___x_1502_ = v_reuseFailAlloc_1503_;
goto v_reusejp_1501_;
}
v_reusejp_1501_:
{
return v___x_1502_;
}
}
else
{
lean_object* v___x_1505_; 
lean_dec(v_a_1493_);
if (v_isShared_1496_ == 0)
{
lean_ctor_set(v___x_1495_, 0, v_e_1320_);
v___x_1505_ = v___x_1495_;
goto v_reusejp_1504_;
}
else
{
lean_object* v_reuseFailAlloc_1506_; 
v_reuseFailAlloc_1506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1506_, 0, v_e_1320_);
v___x_1505_ = v_reuseFailAlloc_1506_;
goto v_reusejp_1504_;
}
v_reusejp_1504_:
{
return v___x_1505_;
}
}
}
}
else
{
lean_object* v_a_1508_; lean_object* v___x_1510_; uint8_t v_isShared_1511_; uint8_t v_isSharedCheck_1515_; 
lean_dec_ref(v_e_1320_);
v_a_1508_ = lean_ctor_get(v___x_1492_, 0);
v_isSharedCheck_1515_ = !lean_is_exclusive(v___x_1492_);
if (v_isSharedCheck_1515_ == 0)
{
v___x_1510_ = v___x_1492_;
v_isShared_1511_ = v_isSharedCheck_1515_;
goto v_resetjp_1509_;
}
else
{
lean_inc(v_a_1508_);
lean_dec(v___x_1492_);
v___x_1510_ = lean_box(0);
v_isShared_1511_ = v_isSharedCheck_1515_;
goto v_resetjp_1509_;
}
v_resetjp_1509_:
{
lean_object* v___x_1513_; 
if (v_isShared_1511_ == 0)
{
v___x_1513_ = v___x_1510_;
goto v_reusejp_1512_;
}
else
{
lean_object* v_reuseFailAlloc_1514_; 
v_reuseFailAlloc_1514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1514_, 0, v_a_1508_);
v___x_1513_ = v_reuseFailAlloc_1514_;
goto v_reusejp_1512_;
}
v_reusejp_1512_:
{
return v___x_1513_;
}
}
}
}
case 4:
{
lean_object* v_declName_1516_; lean_object* v_us_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; 
v_declName_1516_ = lean_ctor_get(v_e_1320_, 0);
v_us_1517_ = lean_ctor_get(v_e_1320_, 1);
v___x_1518_ = lean_box(0);
lean_inc(v_us_1517_);
v___x_1519_ = l_List_mapM_loop___at___00Lean_Meta_Closure_collectExprAux_spec__2___redArg(v_us_1517_, v___x_1518_, v_a_1322_);
if (lean_obj_tag(v___x_1519_) == 0)
{
lean_object* v_a_1520_; lean_object* v___x_1522_; uint8_t v_isShared_1523_; uint8_t v_isSharedCheck_1532_; 
v_a_1520_ = lean_ctor_get(v___x_1519_, 0);
v_isSharedCheck_1532_ = !lean_is_exclusive(v___x_1519_);
if (v_isSharedCheck_1532_ == 0)
{
v___x_1522_ = v___x_1519_;
v_isShared_1523_ = v_isSharedCheck_1532_;
goto v_resetjp_1521_;
}
else
{
lean_inc(v_a_1520_);
lean_dec(v___x_1519_);
v___x_1522_ = lean_box(0);
v_isShared_1523_ = v_isSharedCheck_1532_;
goto v_resetjp_1521_;
}
v_resetjp_1521_:
{
uint8_t v___x_1524_; 
v___x_1524_ = l_ptrEqList___redArg(v_us_1517_, v_a_1520_);
if (v___x_1524_ == 0)
{
lean_object* v___x_1525_; lean_object* v___x_1527_; 
lean_inc(v_declName_1516_);
lean_dec_ref(v_e_1320_);
v___x_1525_ = l_Lean_Expr_const___override(v_declName_1516_, v_a_1520_);
if (v_isShared_1523_ == 0)
{
lean_ctor_set(v___x_1522_, 0, v___x_1525_);
v___x_1527_ = v___x_1522_;
goto v_reusejp_1526_;
}
else
{
lean_object* v_reuseFailAlloc_1528_; 
v_reuseFailAlloc_1528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1528_, 0, v___x_1525_);
v___x_1527_ = v_reuseFailAlloc_1528_;
goto v_reusejp_1526_;
}
v_reusejp_1526_:
{
return v___x_1527_;
}
}
else
{
lean_object* v___x_1530_; 
lean_dec(v_a_1520_);
if (v_isShared_1523_ == 0)
{
lean_ctor_set(v___x_1522_, 0, v_e_1320_);
v___x_1530_ = v___x_1522_;
goto v_reusejp_1529_;
}
else
{
lean_object* v_reuseFailAlloc_1531_; 
v_reuseFailAlloc_1531_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1531_, 0, v_e_1320_);
v___x_1530_ = v_reuseFailAlloc_1531_;
goto v_reusejp_1529_;
}
v_reusejp_1529_:
{
return v___x_1530_;
}
}
}
}
else
{
lean_object* v_a_1533_; lean_object* v___x_1535_; uint8_t v_isShared_1536_; uint8_t v_isSharedCheck_1540_; 
lean_dec_ref(v_e_1320_);
v_a_1533_ = lean_ctor_get(v___x_1519_, 0);
v_isSharedCheck_1540_ = !lean_is_exclusive(v___x_1519_);
if (v_isSharedCheck_1540_ == 0)
{
v___x_1535_ = v___x_1519_;
v_isShared_1536_ = v_isSharedCheck_1540_;
goto v_resetjp_1534_;
}
else
{
lean_inc(v_a_1533_);
lean_dec(v___x_1519_);
v___x_1535_ = lean_box(0);
v_isShared_1536_ = v_isSharedCheck_1540_;
goto v_resetjp_1534_;
}
v_resetjp_1534_:
{
lean_object* v___x_1538_; 
if (v_isShared_1536_ == 0)
{
v___x_1538_ = v___x_1535_;
goto v_reusejp_1537_;
}
else
{
lean_object* v_reuseFailAlloc_1539_; 
v_reuseFailAlloc_1539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1539_, 0, v_a_1533_);
v___x_1538_ = v_reuseFailAlloc_1539_;
goto v_reusejp_1537_;
}
v_reusejp_1537_:
{
return v___x_1538_;
}
}
}
}
case 2:
{
lean_object* v_mvarId_1541_; lean_object* v___x_1542_; 
v_mvarId_1541_ = lean_ctor_get(v_e_1320_, 0);
lean_inc(v_mvarId_1541_);
v___x_1542_ = l_Lean_MVarId_getDecl(v_mvarId_1541_, v_a_1323_, v_a_1324_, v_a_1325_, v_a_1326_);
if (lean_obj_tag(v___x_1542_) == 0)
{
lean_object* v_a_1543_; lean_object* v_type_1544_; lean_object* v___x_1545_; 
v_a_1543_ = lean_ctor_get(v___x_1542_, 0);
lean_inc(v_a_1543_);
lean_dec_ref(v___x_1542_);
v_type_1544_ = lean_ctor_get(v_a_1543_, 2);
lean_inc_ref_n(v_type_1544_, 2);
lean_dec(v_a_1543_);
v___x_1545_ = l_Lean_Meta_Closure_preprocess(v_type_1544_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_, v_a_1325_, v_a_1326_);
if (lean_obj_tag(v___x_1545_) == 0)
{
lean_object* v_a_1546_; lean_object* v___x_1547_; 
v_a_1546_ = lean_ctor_get(v___x_1545_, 0);
lean_inc(v_a_1546_);
lean_dec_ref(v___x_1545_);
v___x_1547_ = l_Lean_Meta_Closure_collectExprAux___lam__0(v_a_1546_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_, v_a_1325_, v_a_1326_);
if (lean_obj_tag(v___x_1547_) == 0)
{
lean_object* v_a_1548_; lean_object* v___x_1549_; 
v_a_1548_ = lean_ctor_get(v___x_1547_, 0);
lean_inc(v_a_1548_);
lean_dec_ref(v___x_1547_);
v___x_1549_ = l_Lean_mkFreshFVarId___at___00Lean_Meta_Closure_collectExprAux_spec__3(v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_, v_a_1325_, v_a_1326_);
if (lean_obj_tag(v___x_1549_) == 0)
{
lean_object* v_a_1550_; lean_object* v___x_1551_; 
v_a_1550_ = lean_ctor_get(v___x_1549_, 0);
lean_inc(v_a_1550_);
lean_dec_ref(v___x_1549_);
v___x_1551_ = l_Lean_Meta_Closure_mkNextUserName___redArg(v_a_1322_);
if (lean_obj_tag(v___x_1551_) == 0)
{
lean_object* v_a_1552_; lean_object* v___x_1554_; uint8_t v_isShared_1555_; uint8_t v_isSharedCheck_1614_; 
v_a_1552_ = lean_ctor_get(v___x_1551_, 0);
v_isSharedCheck_1614_ = !lean_is_exclusive(v___x_1551_);
if (v_isSharedCheck_1614_ == 0)
{
v___x_1554_ = v___x_1551_;
v_isShared_1555_ = v_isSharedCheck_1614_;
goto v_resetjp_1553_;
}
else
{
lean_inc(v_a_1552_);
lean_dec(v___x_1551_);
v___x_1554_ = lean_box(0);
v_isShared_1555_ = v_isSharedCheck_1614_;
goto v_resetjp_1553_;
}
v_resetjp_1553_:
{
lean_object* v_e_x27_1557_; lean_object* v___y_1558_; lean_object* v___x_1590_; 
v___x_1590_ = l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__4___redArg(v_mvarId_1541_, v_a_1324_);
if (lean_obj_tag(v___x_1590_) == 0)
{
lean_object* v_a_1591_; 
v_a_1591_ = lean_ctor_get(v___x_1590_, 0);
lean_inc(v_a_1591_);
lean_dec_ref(v___x_1590_);
if (lean_obj_tag(v_a_1591_) == 1)
{
lean_object* v_val_1592_; lean_object* v___x_1594_; uint8_t v_isShared_1595_; uint8_t v_isSharedCheck_1605_; 
v_val_1592_ = lean_ctor_get(v_a_1591_, 0);
v_isSharedCheck_1605_ = !lean_is_exclusive(v_a_1591_);
if (v_isSharedCheck_1605_ == 0)
{
v___x_1594_ = v_a_1591_;
v_isShared_1595_ = v_isSharedCheck_1605_;
goto v_resetjp_1593_;
}
else
{
lean_inc(v_val_1592_);
lean_dec(v_a_1591_);
v___x_1594_ = lean_box(0);
v_isShared_1595_ = v_isSharedCheck_1605_;
goto v_resetjp_1593_;
}
v_resetjp_1593_:
{
lean_object* v_fvars_1596_; lean_object* v___f_1597_; lean_object* v___x_1598_; lean_object* v___x_1600_; 
v_fvars_1596_ = lean_ctor_get(v_val_1592_, 0);
lean_inc_ref(v_fvars_1596_);
lean_dec(v_val_1592_);
v___f_1597_ = lean_alloc_closure((void*)(l_Lean_Meta_Closure_collectExprAux___lam__1___boxed), 10, 1);
lean_closure_set(v___f_1597_, 0, v_e_1320_);
v___x_1598_ = lean_array_get_size(v_fvars_1596_);
lean_dec_ref(v_fvars_1596_);
if (v_isShared_1595_ == 0)
{
lean_ctor_set(v___x_1594_, 0, v___x_1598_);
v___x_1600_ = v___x_1594_;
goto v_reusejp_1599_;
}
else
{
lean_object* v_reuseFailAlloc_1604_; 
v_reuseFailAlloc_1604_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1604_, 0, v___x_1598_);
v___x_1600_ = v_reuseFailAlloc_1604_;
goto v_reusejp_1599_;
}
v_reusejp_1599_:
{
uint8_t v___x_1601_; lean_object* v___x_1602_; 
v___x_1601_ = 0;
v___x_1602_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Closure_collectExprAux_spec__5___redArg(v_type_1544_, v___x_1600_, v___f_1597_, v___x_1601_, v___x_1601_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_, v_a_1325_, v_a_1326_);
if (lean_obj_tag(v___x_1602_) == 0)
{
lean_object* v_a_1603_; 
v_a_1603_ = lean_ctor_get(v___x_1602_, 0);
lean_inc(v_a_1603_);
lean_dec_ref(v___x_1602_);
v_e_x27_1557_ = v_a_1603_;
v___y_1558_ = v_a_1322_;
goto v___jp_1556_;
}
else
{
lean_del_object(v___x_1554_);
lean_dec(v_a_1552_);
lean_dec(v_a_1550_);
lean_dec(v_a_1548_);
return v___x_1602_;
}
}
}
}
else
{
lean_dec(v_a_1591_);
lean_dec_ref(v_type_1544_);
v_e_x27_1557_ = v_e_1320_;
v___y_1558_ = v_a_1322_;
goto v___jp_1556_;
}
}
else
{
lean_object* v_a_1606_; lean_object* v___x_1608_; uint8_t v_isShared_1609_; uint8_t v_isSharedCheck_1613_; 
lean_del_object(v___x_1554_);
lean_dec(v_a_1552_);
lean_dec(v_a_1550_);
lean_dec(v_a_1548_);
lean_dec_ref(v_type_1544_);
lean_dec_ref(v_e_1320_);
v_a_1606_ = lean_ctor_get(v___x_1590_, 0);
v_isSharedCheck_1613_ = !lean_is_exclusive(v___x_1590_);
if (v_isSharedCheck_1613_ == 0)
{
v___x_1608_ = v___x_1590_;
v_isShared_1609_ = v_isSharedCheck_1613_;
goto v_resetjp_1607_;
}
else
{
lean_inc(v_a_1606_);
lean_dec(v___x_1590_);
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
v___jp_1556_:
{
lean_object* v___x_1559_; lean_object* v_visitedLevel_1560_; lean_object* v_visitedExpr_1561_; lean_object* v_levelParams_1562_; lean_object* v_nextLevelIdx_1563_; lean_object* v_levelArgs_1564_; lean_object* v_newLocalDecls_1565_; lean_object* v_newLocalDeclsForMVars_1566_; lean_object* v_newLetDecls_1567_; lean_object* v_nextExprIdx_1568_; lean_object* v_exprMVarArgs_1569_; lean_object* v_exprFVarArgs_1570_; lean_object* v_toProcess_1571_; lean_object* v___x_1573_; uint8_t v_isShared_1574_; uint8_t v_isSharedCheck_1589_; 
v___x_1559_ = lean_st_ref_take(v___y_1558_);
v_visitedLevel_1560_ = lean_ctor_get(v___x_1559_, 0);
v_visitedExpr_1561_ = lean_ctor_get(v___x_1559_, 1);
v_levelParams_1562_ = lean_ctor_get(v___x_1559_, 2);
v_nextLevelIdx_1563_ = lean_ctor_get(v___x_1559_, 3);
v_levelArgs_1564_ = lean_ctor_get(v___x_1559_, 4);
v_newLocalDecls_1565_ = lean_ctor_get(v___x_1559_, 5);
v_newLocalDeclsForMVars_1566_ = lean_ctor_get(v___x_1559_, 6);
v_newLetDecls_1567_ = lean_ctor_get(v___x_1559_, 7);
v_nextExprIdx_1568_ = lean_ctor_get(v___x_1559_, 8);
v_exprMVarArgs_1569_ = lean_ctor_get(v___x_1559_, 9);
v_exprFVarArgs_1570_ = lean_ctor_get(v___x_1559_, 10);
v_toProcess_1571_ = lean_ctor_get(v___x_1559_, 11);
v_isSharedCheck_1589_ = !lean_is_exclusive(v___x_1559_);
if (v_isSharedCheck_1589_ == 0)
{
v___x_1573_ = v___x_1559_;
v_isShared_1574_ = v_isSharedCheck_1589_;
goto v_resetjp_1572_;
}
else
{
lean_inc(v_toProcess_1571_);
lean_inc(v_exprFVarArgs_1570_);
lean_inc(v_exprMVarArgs_1569_);
lean_inc(v_nextExprIdx_1568_);
lean_inc(v_newLetDecls_1567_);
lean_inc(v_newLocalDeclsForMVars_1566_);
lean_inc(v_newLocalDecls_1565_);
lean_inc(v_levelArgs_1564_);
lean_inc(v_nextLevelIdx_1563_);
lean_inc(v_levelParams_1562_);
lean_inc(v_visitedExpr_1561_);
lean_inc(v_visitedLevel_1560_);
lean_dec(v___x_1559_);
v___x_1573_ = lean_box(0);
v_isShared_1574_ = v_isSharedCheck_1589_;
goto v_resetjp_1572_;
}
v_resetjp_1572_:
{
lean_object* v___x_1575_; uint8_t v___x_1576_; uint8_t v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1582_; 
v___x_1575_ = lean_unsigned_to_nat(0u);
v___x_1576_ = 0;
v___x_1577_ = 0;
lean_inc(v_a_1550_);
v___x_1578_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_1578_, 0, v___x_1575_);
lean_ctor_set(v___x_1578_, 1, v_a_1550_);
lean_ctor_set(v___x_1578_, 2, v_a_1552_);
lean_ctor_set(v___x_1578_, 3, v_a_1548_);
lean_ctor_set_uint8(v___x_1578_, sizeof(void*)*4, v___x_1576_);
lean_ctor_set_uint8(v___x_1578_, sizeof(void*)*4 + 1, v___x_1577_);
v___x_1579_ = lean_array_push(v_newLocalDeclsForMVars_1566_, v___x_1578_);
v___x_1580_ = lean_array_push(v_exprMVarArgs_1569_, v_e_x27_1557_);
if (v_isShared_1574_ == 0)
{
lean_ctor_set(v___x_1573_, 9, v___x_1580_);
lean_ctor_set(v___x_1573_, 6, v___x_1579_);
v___x_1582_ = v___x_1573_;
goto v_reusejp_1581_;
}
else
{
lean_object* v_reuseFailAlloc_1588_; 
v_reuseFailAlloc_1588_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_1588_, 0, v_visitedLevel_1560_);
lean_ctor_set(v_reuseFailAlloc_1588_, 1, v_visitedExpr_1561_);
lean_ctor_set(v_reuseFailAlloc_1588_, 2, v_levelParams_1562_);
lean_ctor_set(v_reuseFailAlloc_1588_, 3, v_nextLevelIdx_1563_);
lean_ctor_set(v_reuseFailAlloc_1588_, 4, v_levelArgs_1564_);
lean_ctor_set(v_reuseFailAlloc_1588_, 5, v_newLocalDecls_1565_);
lean_ctor_set(v_reuseFailAlloc_1588_, 6, v___x_1579_);
lean_ctor_set(v_reuseFailAlloc_1588_, 7, v_newLetDecls_1567_);
lean_ctor_set(v_reuseFailAlloc_1588_, 8, v_nextExprIdx_1568_);
lean_ctor_set(v_reuseFailAlloc_1588_, 9, v___x_1580_);
lean_ctor_set(v_reuseFailAlloc_1588_, 10, v_exprFVarArgs_1570_);
lean_ctor_set(v_reuseFailAlloc_1588_, 11, v_toProcess_1571_);
v___x_1582_ = v_reuseFailAlloc_1588_;
goto v_reusejp_1581_;
}
v_reusejp_1581_:
{
lean_object* v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1586_; 
v___x_1583_ = lean_st_ref_set(v___y_1558_, v___x_1582_);
v___x_1584_ = l_Lean_mkFVar(v_a_1550_);
if (v_isShared_1555_ == 0)
{
lean_ctor_set(v___x_1554_, 0, v___x_1584_);
v___x_1586_ = v___x_1554_;
goto v_reusejp_1585_;
}
else
{
lean_object* v_reuseFailAlloc_1587_; 
v_reuseFailAlloc_1587_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1587_, 0, v___x_1584_);
v___x_1586_ = v_reuseFailAlloc_1587_;
goto v_reusejp_1585_;
}
v_reusejp_1585_:
{
return v___x_1586_;
}
}
}
}
}
}
else
{
lean_object* v_a_1615_; lean_object* v___x_1617_; uint8_t v_isShared_1618_; uint8_t v_isSharedCheck_1622_; 
lean_dec(v_a_1550_);
lean_dec(v_a_1548_);
lean_dec_ref(v_type_1544_);
lean_dec_ref(v_e_1320_);
v_a_1615_ = lean_ctor_get(v___x_1551_, 0);
v_isSharedCheck_1622_ = !lean_is_exclusive(v___x_1551_);
if (v_isSharedCheck_1622_ == 0)
{
v___x_1617_ = v___x_1551_;
v_isShared_1618_ = v_isSharedCheck_1622_;
goto v_resetjp_1616_;
}
else
{
lean_inc(v_a_1615_);
lean_dec(v___x_1551_);
v___x_1617_ = lean_box(0);
v_isShared_1618_ = v_isSharedCheck_1622_;
goto v_resetjp_1616_;
}
v_resetjp_1616_:
{
lean_object* v___x_1620_; 
if (v_isShared_1618_ == 0)
{
v___x_1620_ = v___x_1617_;
goto v_reusejp_1619_;
}
else
{
lean_object* v_reuseFailAlloc_1621_; 
v_reuseFailAlloc_1621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1621_, 0, v_a_1615_);
v___x_1620_ = v_reuseFailAlloc_1621_;
goto v_reusejp_1619_;
}
v_reusejp_1619_:
{
return v___x_1620_;
}
}
}
}
else
{
lean_object* v_a_1623_; lean_object* v___x_1625_; uint8_t v_isShared_1626_; uint8_t v_isSharedCheck_1630_; 
lean_dec(v_a_1548_);
lean_dec_ref(v_type_1544_);
lean_dec_ref(v_e_1320_);
v_a_1623_ = lean_ctor_get(v___x_1549_, 0);
v_isSharedCheck_1630_ = !lean_is_exclusive(v___x_1549_);
if (v_isSharedCheck_1630_ == 0)
{
v___x_1625_ = v___x_1549_;
v_isShared_1626_ = v_isSharedCheck_1630_;
goto v_resetjp_1624_;
}
else
{
lean_inc(v_a_1623_);
lean_dec(v___x_1549_);
v___x_1625_ = lean_box(0);
v_isShared_1626_ = v_isSharedCheck_1630_;
goto v_resetjp_1624_;
}
v_resetjp_1624_:
{
lean_object* v___x_1628_; 
if (v_isShared_1626_ == 0)
{
v___x_1628_ = v___x_1625_;
goto v_reusejp_1627_;
}
else
{
lean_object* v_reuseFailAlloc_1629_; 
v_reuseFailAlloc_1629_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1629_, 0, v_a_1623_);
v___x_1628_ = v_reuseFailAlloc_1629_;
goto v_reusejp_1627_;
}
v_reusejp_1627_:
{
return v___x_1628_;
}
}
}
}
else
{
lean_dec_ref(v_type_1544_);
lean_dec_ref(v_e_1320_);
return v___x_1547_;
}
}
else
{
lean_dec_ref(v_type_1544_);
lean_dec_ref(v_e_1320_);
return v___x_1545_;
}
}
else
{
lean_object* v_a_1631_; lean_object* v___x_1633_; uint8_t v_isShared_1634_; uint8_t v_isSharedCheck_1638_; 
lean_dec_ref(v_e_1320_);
v_a_1631_ = lean_ctor_get(v___x_1542_, 0);
v_isSharedCheck_1638_ = !lean_is_exclusive(v___x_1542_);
if (v_isSharedCheck_1638_ == 0)
{
v___x_1633_ = v___x_1542_;
v_isShared_1634_ = v_isSharedCheck_1638_;
goto v_resetjp_1632_;
}
else
{
lean_inc(v_a_1631_);
lean_dec(v___x_1542_);
v___x_1633_ = lean_box(0);
v_isShared_1634_ = v_isSharedCheck_1638_;
goto v_resetjp_1632_;
}
v_resetjp_1632_:
{
lean_object* v___x_1636_; 
if (v_isShared_1634_ == 0)
{
v___x_1636_ = v___x_1633_;
goto v_reusejp_1635_;
}
else
{
lean_object* v_reuseFailAlloc_1637_; 
v_reuseFailAlloc_1637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1637_, 0, v_a_1631_);
v___x_1636_ = v_reuseFailAlloc_1637_;
goto v_reusejp_1635_;
}
v_reusejp_1635_:
{
return v___x_1636_;
}
}
}
}
case 1:
{
lean_object* v_fvarId_1639_; uint8_t v___x_1640_; lean_object* v___x_1641_; 
v_fvarId_1639_ = lean_ctor_get(v_e_1320_, 0);
lean_inc_n(v_fvarId_1639_, 2);
lean_dec_ref(v_e_1320_);
v___x_1640_ = 0;
v___x_1641_ = l_Lean_FVarId_getValue_x3f___redArg(v_fvarId_1639_, v___x_1640_, v_a_1323_, v_a_1325_, v_a_1326_);
if (lean_obj_tag(v___x_1641_) == 0)
{
lean_object* v_a_1642_; uint8_t v___y_1644_; lean_object* v___y_1645_; lean_object* v___y_1646_; lean_object* v___y_1647_; lean_object* v___y_1648_; lean_object* v___y_1649_; 
v_a_1642_ = lean_ctor_get(v___x_1641_, 0);
lean_inc(v_a_1642_);
lean_dec_ref(v___x_1641_);
if (v_a_1321_ == 1)
{
if (lean_obj_tag(v_a_1642_) == 1)
{
lean_object* v_val_1679_; lean_object* v___x_1680_; 
lean_dec(v_fvarId_1639_);
v_val_1679_ = lean_ctor_get(v_a_1642_, 0);
lean_inc(v_val_1679_);
lean_dec_ref(v_a_1642_);
v___x_1680_ = l_Lean_Meta_Closure_preprocess(v_val_1679_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_, v_a_1325_, v_a_1326_);
if (lean_obj_tag(v___x_1680_) == 0)
{
lean_object* v_a_1681_; lean_object* v___x_1682_; 
v_a_1681_ = lean_ctor_get(v___x_1680_, 0);
lean_inc(v_a_1681_);
lean_dec_ref(v___x_1680_);
v___x_1682_ = l_Lean_Meta_Closure_collectExprAux___lam__0(v_a_1681_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_, v_a_1325_, v_a_1326_);
return v___x_1682_;
}
else
{
return v___x_1680_;
}
}
else
{
lean_dec(v_a_1642_);
v___y_1644_ = v_a_1321_;
v___y_1645_ = v_a_1322_;
v___y_1646_ = v_a_1323_;
v___y_1647_ = v_a_1324_;
v___y_1648_ = v_a_1325_;
v___y_1649_ = v_a_1326_;
goto v___jp_1643_;
}
}
else
{
lean_dec(v_a_1642_);
v___y_1644_ = v_a_1321_;
v___y_1645_ = v_a_1322_;
v___y_1646_ = v_a_1323_;
v___y_1647_ = v_a_1324_;
v___y_1648_ = v_a_1325_;
v___y_1649_ = v_a_1326_;
goto v___jp_1643_;
}
v___jp_1643_:
{
lean_object* v___x_1650_; 
v___x_1650_ = l_Lean_mkFreshFVarId___at___00Lean_Meta_Closure_collectExprAux_spec__3(v___y_1644_, v___y_1645_, v___y_1646_, v___y_1647_, v___y_1648_, v___y_1649_);
if (lean_obj_tag(v___x_1650_) == 0)
{
lean_object* v_a_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; 
v_a_1651_ = lean_ctor_get(v___x_1650_, 0);
lean_inc_n(v_a_1651_, 2);
lean_dec_ref(v___x_1650_);
v___x_1652_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1652_, 0, v_fvarId_1639_);
lean_ctor_set(v___x_1652_, 1, v_a_1651_);
v___x_1653_ = l_Lean_Meta_Closure_pushToProcess___redArg(v___x_1652_, v___y_1645_);
if (lean_obj_tag(v___x_1653_) == 0)
{
lean_object* v___x_1655_; uint8_t v_isShared_1656_; uint8_t v_isSharedCheck_1661_; 
v_isSharedCheck_1661_ = !lean_is_exclusive(v___x_1653_);
if (v_isSharedCheck_1661_ == 0)
{
lean_object* v_unused_1662_; 
v_unused_1662_ = lean_ctor_get(v___x_1653_, 0);
lean_dec(v_unused_1662_);
v___x_1655_ = v___x_1653_;
v_isShared_1656_ = v_isSharedCheck_1661_;
goto v_resetjp_1654_;
}
else
{
lean_dec(v___x_1653_);
v___x_1655_ = lean_box(0);
v_isShared_1656_ = v_isSharedCheck_1661_;
goto v_resetjp_1654_;
}
v_resetjp_1654_:
{
lean_object* v___x_1657_; lean_object* v___x_1659_; 
v___x_1657_ = l_Lean_mkFVar(v_a_1651_);
if (v_isShared_1656_ == 0)
{
lean_ctor_set(v___x_1655_, 0, v___x_1657_);
v___x_1659_ = v___x_1655_;
goto v_reusejp_1658_;
}
else
{
lean_object* v_reuseFailAlloc_1660_; 
v_reuseFailAlloc_1660_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1660_, 0, v___x_1657_);
v___x_1659_ = v_reuseFailAlloc_1660_;
goto v_reusejp_1658_;
}
v_reusejp_1658_:
{
return v___x_1659_;
}
}
}
else
{
lean_object* v_a_1663_; lean_object* v___x_1665_; uint8_t v_isShared_1666_; uint8_t v_isSharedCheck_1670_; 
lean_dec(v_a_1651_);
v_a_1663_ = lean_ctor_get(v___x_1653_, 0);
v_isSharedCheck_1670_ = !lean_is_exclusive(v___x_1653_);
if (v_isSharedCheck_1670_ == 0)
{
v___x_1665_ = v___x_1653_;
v_isShared_1666_ = v_isSharedCheck_1670_;
goto v_resetjp_1664_;
}
else
{
lean_inc(v_a_1663_);
lean_dec(v___x_1653_);
v___x_1665_ = lean_box(0);
v_isShared_1666_ = v_isSharedCheck_1670_;
goto v_resetjp_1664_;
}
v_resetjp_1664_:
{
lean_object* v___x_1668_; 
if (v_isShared_1666_ == 0)
{
v___x_1668_ = v___x_1665_;
goto v_reusejp_1667_;
}
else
{
lean_object* v_reuseFailAlloc_1669_; 
v_reuseFailAlloc_1669_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1669_, 0, v_a_1663_);
v___x_1668_ = v_reuseFailAlloc_1669_;
goto v_reusejp_1667_;
}
v_reusejp_1667_:
{
return v___x_1668_;
}
}
}
}
else
{
lean_object* v_a_1671_; lean_object* v___x_1673_; uint8_t v_isShared_1674_; uint8_t v_isSharedCheck_1678_; 
lean_dec(v_fvarId_1639_);
v_a_1671_ = lean_ctor_get(v___x_1650_, 0);
v_isSharedCheck_1678_ = !lean_is_exclusive(v___x_1650_);
if (v_isSharedCheck_1678_ == 0)
{
v___x_1673_ = v___x_1650_;
v_isShared_1674_ = v_isSharedCheck_1678_;
goto v_resetjp_1672_;
}
else
{
lean_inc(v_a_1671_);
lean_dec(v___x_1650_);
v___x_1673_ = lean_box(0);
v_isShared_1674_ = v_isSharedCheck_1678_;
goto v_resetjp_1672_;
}
v_resetjp_1672_:
{
lean_object* v___x_1676_; 
if (v_isShared_1674_ == 0)
{
v___x_1676_ = v___x_1673_;
goto v_reusejp_1675_;
}
else
{
lean_object* v_reuseFailAlloc_1677_; 
v_reuseFailAlloc_1677_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1677_, 0, v_a_1671_);
v___x_1676_ = v_reuseFailAlloc_1677_;
goto v_reusejp_1675_;
}
v_reusejp_1675_:
{
return v___x_1676_;
}
}
}
}
}
else
{
lean_object* v_a_1683_; lean_object* v___x_1685_; uint8_t v_isShared_1686_; uint8_t v_isSharedCheck_1690_; 
lean_dec(v_fvarId_1639_);
v_a_1683_ = lean_ctor_get(v___x_1641_, 0);
v_isSharedCheck_1690_ = !lean_is_exclusive(v___x_1641_);
if (v_isSharedCheck_1690_ == 0)
{
v___x_1685_ = v___x_1641_;
v_isShared_1686_ = v_isSharedCheck_1690_;
goto v_resetjp_1684_;
}
else
{
lean_inc(v_a_1683_);
lean_dec(v___x_1641_);
v___x_1685_ = lean_box(0);
v_isShared_1686_ = v_isSharedCheck_1690_;
goto v_resetjp_1684_;
}
v_resetjp_1684_:
{
lean_object* v___x_1688_; 
if (v_isShared_1686_ == 0)
{
v___x_1688_ = v___x_1685_;
goto v_reusejp_1687_;
}
else
{
lean_object* v_reuseFailAlloc_1689_; 
v_reuseFailAlloc_1689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1689_, 0, v_a_1683_);
v___x_1688_ = v_reuseFailAlloc_1689_;
goto v_reusejp_1687_;
}
v_reusejp_1687_:
{
return v___x_1688_;
}
}
}
}
default: 
{
lean_object* v___x_1691_; 
v___x_1691_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1691_, 0, v_e_1320_);
return v___x_1691_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectExprAux___lam__0(lean_object* v_e_1692_, uint8_t v___y_1693_, lean_object* v___y_1694_, lean_object* v___y_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_){
_start:
{
uint8_t v___x_1743_; 
v___x_1743_ = l_Lean_Expr_hasLevelParam(v_e_1692_);
if (v___x_1743_ == 0)
{
uint8_t v___x_1744_; 
v___x_1744_ = l_Lean_Expr_hasFVar(v_e_1692_);
if (v___x_1744_ == 0)
{
uint8_t v___x_1745_; 
v___x_1745_ = l_Lean_Expr_hasMVar(v_e_1692_);
if (v___x_1745_ == 0)
{
lean_object* v___x_1746_; 
v___x_1746_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1746_, 0, v_e_1692_);
return v___x_1746_;
}
else
{
goto v___jp_1700_;
}
}
else
{
goto v___jp_1700_;
}
}
else
{
goto v___jp_1700_;
}
v___jp_1700_:
{
lean_object* v___x_1701_; lean_object* v_visitedExpr_1702_; lean_object* v___x_1703_; 
v___x_1701_ = lean_st_ref_get(v___y_1694_);
v_visitedExpr_1702_ = lean_ctor_get(v___x_1701_, 1);
lean_inc_ref(v_visitedExpr_1702_);
lean_dec(v___x_1701_);
v___x_1703_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0___redArg(v_visitedExpr_1702_, v_e_1692_);
lean_dec_ref(v_visitedExpr_1702_);
if (lean_obj_tag(v___x_1703_) == 0)
{
lean_object* v___x_1704_; 
lean_inc_ref(v_e_1692_);
v___x_1704_ = l_Lean_Meta_Closure_collectExprAux(v_e_1692_, v___y_1693_, v___y_1694_, v___y_1695_, v___y_1696_, v___y_1697_, v___y_1698_);
if (lean_obj_tag(v___x_1704_) == 0)
{
lean_object* v_a_1705_; lean_object* v___x_1707_; uint8_t v_isShared_1708_; uint8_t v_isSharedCheck_1734_; 
v_a_1705_ = lean_ctor_get(v___x_1704_, 0);
v_isSharedCheck_1734_ = !lean_is_exclusive(v___x_1704_);
if (v_isSharedCheck_1734_ == 0)
{
v___x_1707_ = v___x_1704_;
v_isShared_1708_ = v_isSharedCheck_1734_;
goto v_resetjp_1706_;
}
else
{
lean_inc(v_a_1705_);
lean_dec(v___x_1704_);
v___x_1707_ = lean_box(0);
v_isShared_1708_ = v_isSharedCheck_1734_;
goto v_resetjp_1706_;
}
v_resetjp_1706_:
{
lean_object* v___x_1709_; lean_object* v_visitedLevel_1710_; lean_object* v_visitedExpr_1711_; lean_object* v_levelParams_1712_; lean_object* v_nextLevelIdx_1713_; lean_object* v_levelArgs_1714_; lean_object* v_newLocalDecls_1715_; lean_object* v_newLocalDeclsForMVars_1716_; lean_object* v_newLetDecls_1717_; lean_object* v_nextExprIdx_1718_; lean_object* v_exprMVarArgs_1719_; lean_object* v_exprFVarArgs_1720_; lean_object* v_toProcess_1721_; lean_object* v___x_1723_; uint8_t v_isShared_1724_; uint8_t v_isSharedCheck_1733_; 
v___x_1709_ = lean_st_ref_take(v___y_1694_);
v_visitedLevel_1710_ = lean_ctor_get(v___x_1709_, 0);
v_visitedExpr_1711_ = lean_ctor_get(v___x_1709_, 1);
v_levelParams_1712_ = lean_ctor_get(v___x_1709_, 2);
v_nextLevelIdx_1713_ = lean_ctor_get(v___x_1709_, 3);
v_levelArgs_1714_ = lean_ctor_get(v___x_1709_, 4);
v_newLocalDecls_1715_ = lean_ctor_get(v___x_1709_, 5);
v_newLocalDeclsForMVars_1716_ = lean_ctor_get(v___x_1709_, 6);
v_newLetDecls_1717_ = lean_ctor_get(v___x_1709_, 7);
v_nextExprIdx_1718_ = lean_ctor_get(v___x_1709_, 8);
v_exprMVarArgs_1719_ = lean_ctor_get(v___x_1709_, 9);
v_exprFVarArgs_1720_ = lean_ctor_get(v___x_1709_, 10);
v_toProcess_1721_ = lean_ctor_get(v___x_1709_, 11);
v_isSharedCheck_1733_ = !lean_is_exclusive(v___x_1709_);
if (v_isSharedCheck_1733_ == 0)
{
v___x_1723_ = v___x_1709_;
v_isShared_1724_ = v_isSharedCheck_1733_;
goto v_resetjp_1722_;
}
else
{
lean_inc(v_toProcess_1721_);
lean_inc(v_exprFVarArgs_1720_);
lean_inc(v_exprMVarArgs_1719_);
lean_inc(v_nextExprIdx_1718_);
lean_inc(v_newLetDecls_1717_);
lean_inc(v_newLocalDeclsForMVars_1716_);
lean_inc(v_newLocalDecls_1715_);
lean_inc(v_levelArgs_1714_);
lean_inc(v_nextLevelIdx_1713_);
lean_inc(v_levelParams_1712_);
lean_inc(v_visitedExpr_1711_);
lean_inc(v_visitedLevel_1710_);
lean_dec(v___x_1709_);
v___x_1723_ = lean_box(0);
v_isShared_1724_ = v_isSharedCheck_1733_;
goto v_resetjp_1722_;
}
v_resetjp_1722_:
{
lean_object* v___x_1725_; lean_object* v___x_1727_; 
lean_inc(v_a_1705_);
v___x_1725_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1___redArg(v_visitedExpr_1711_, v_e_1692_, v_a_1705_);
if (v_isShared_1724_ == 0)
{
lean_ctor_set(v___x_1723_, 1, v___x_1725_);
v___x_1727_ = v___x_1723_;
goto v_reusejp_1726_;
}
else
{
lean_object* v_reuseFailAlloc_1732_; 
v_reuseFailAlloc_1732_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_1732_, 0, v_visitedLevel_1710_);
lean_ctor_set(v_reuseFailAlloc_1732_, 1, v___x_1725_);
lean_ctor_set(v_reuseFailAlloc_1732_, 2, v_levelParams_1712_);
lean_ctor_set(v_reuseFailAlloc_1732_, 3, v_nextLevelIdx_1713_);
lean_ctor_set(v_reuseFailAlloc_1732_, 4, v_levelArgs_1714_);
lean_ctor_set(v_reuseFailAlloc_1732_, 5, v_newLocalDecls_1715_);
lean_ctor_set(v_reuseFailAlloc_1732_, 6, v_newLocalDeclsForMVars_1716_);
lean_ctor_set(v_reuseFailAlloc_1732_, 7, v_newLetDecls_1717_);
lean_ctor_set(v_reuseFailAlloc_1732_, 8, v_nextExprIdx_1718_);
lean_ctor_set(v_reuseFailAlloc_1732_, 9, v_exprMVarArgs_1719_);
lean_ctor_set(v_reuseFailAlloc_1732_, 10, v_exprFVarArgs_1720_);
lean_ctor_set(v_reuseFailAlloc_1732_, 11, v_toProcess_1721_);
v___x_1727_ = v_reuseFailAlloc_1732_;
goto v_reusejp_1726_;
}
v_reusejp_1726_:
{
lean_object* v___x_1728_; lean_object* v___x_1730_; 
v___x_1728_ = lean_st_ref_set(v___y_1694_, v___x_1727_);
if (v_isShared_1708_ == 0)
{
v___x_1730_ = v___x_1707_;
goto v_reusejp_1729_;
}
else
{
lean_object* v_reuseFailAlloc_1731_; 
v_reuseFailAlloc_1731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1731_, 0, v_a_1705_);
v___x_1730_ = v_reuseFailAlloc_1731_;
goto v_reusejp_1729_;
}
v_reusejp_1729_:
{
return v___x_1730_;
}
}
}
}
}
else
{
lean_dec_ref(v_e_1692_);
return v___x_1704_;
}
}
else
{
lean_object* v_val_1735_; lean_object* v___x_1737_; uint8_t v_isShared_1738_; uint8_t v_isSharedCheck_1742_; 
lean_dec_ref(v_e_1692_);
v_val_1735_ = lean_ctor_get(v___x_1703_, 0);
v_isSharedCheck_1742_ = !lean_is_exclusive(v___x_1703_);
if (v_isSharedCheck_1742_ == 0)
{
v___x_1737_ = v___x_1703_;
v_isShared_1738_ = v_isSharedCheck_1742_;
goto v_resetjp_1736_;
}
else
{
lean_inc(v_val_1735_);
lean_dec(v___x_1703_);
v___x_1737_ = lean_box(0);
v_isShared_1738_ = v_isSharedCheck_1742_;
goto v_resetjp_1736_;
}
v_resetjp_1736_:
{
lean_object* v___x_1740_; 
if (v_isShared_1738_ == 0)
{
lean_ctor_set_tag(v___x_1737_, 0);
v___x_1740_ = v___x_1737_;
goto v_reusejp_1739_;
}
else
{
lean_object* v_reuseFailAlloc_1741_; 
v_reuseFailAlloc_1741_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1741_, 0, v_val_1735_);
v___x_1740_ = v_reuseFailAlloc_1741_;
goto v_reusejp_1739_;
}
v_reusejp_1739_:
{
return v___x_1740_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectExprAux___lam__0___boxed(lean_object* v_e_1747_, lean_object* v___y_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_){
_start:
{
uint8_t v___y_18416__boxed_1755_; lean_object* v_res_1756_; 
v___y_18416__boxed_1755_ = lean_unbox(v___y_1748_);
v_res_1756_ = l_Lean_Meta_Closure_collectExprAux___lam__0(v_e_1747_, v___y_18416__boxed_1755_, v___y_1749_, v___y_1750_, v___y_1751_, v___y_1752_, v___y_1753_);
lean_dec(v___y_1753_);
lean_dec_ref(v___y_1752_);
lean_dec(v___y_1751_);
lean_dec_ref(v___y_1750_);
lean_dec(v___y_1749_);
return v_res_1756_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectExprAux___boxed(lean_object* v_e_1757_, lean_object* v_a_1758_, lean_object* v_a_1759_, lean_object* v_a_1760_, lean_object* v_a_1761_, lean_object* v_a_1762_, lean_object* v_a_1763_, lean_object* v_a_1764_){
_start:
{
uint8_t v_a_boxed_1765_; lean_object* v_res_1766_; 
v_a_boxed_1765_ = lean_unbox(v_a_1758_);
v_res_1766_ = l_Lean_Meta_Closure_collectExprAux(v_e_1757_, v_a_boxed_1765_, v_a_1759_, v_a_1760_, v_a_1761_, v_a_1762_, v_a_1763_);
lean_dec(v_a_1763_);
lean_dec_ref(v_a_1762_);
lean_dec(v_a_1761_);
lean_dec_ref(v_a_1760_);
lean_dec(v_a_1759_);
return v_res_1766_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0(lean_object* v_00_u03b2_1767_, lean_object* v_m_1768_, lean_object* v_a_1769_){
_start:
{
lean_object* v___x_1770_; 
v___x_1770_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0___redArg(v_m_1768_, v_a_1769_);
return v___x_1770_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0___boxed(lean_object* v_00_u03b2_1771_, lean_object* v_m_1772_, lean_object* v_a_1773_){
_start:
{
lean_object* v_res_1774_; 
v_res_1774_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0(v_00_u03b2_1771_, v_m_1772_, v_a_1773_);
lean_dec_ref(v_a_1773_);
lean_dec_ref(v_m_1772_);
return v_res_1774_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1(lean_object* v_00_u03b2_1775_, lean_object* v_m_1776_, lean_object* v_a_1777_, lean_object* v_b_1778_){
_start:
{
lean_object* v___x_1779_; 
v___x_1779_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1___redArg(v_m_1776_, v_a_1777_, v_b_1778_);
return v___x_1779_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Closure_collectExprAux_spec__2(lean_object* v_x_1780_, lean_object* v_x_1781_, uint8_t v___y_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_){
_start:
{
lean_object* v___x_1789_; 
v___x_1789_ = l_List_mapM_loop___at___00Lean_Meta_Closure_collectExprAux_spec__2___redArg(v_x_1780_, v_x_1781_, v___y_1783_);
return v___x_1789_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Closure_collectExprAux_spec__2___boxed(lean_object* v_x_1790_, lean_object* v_x_1791_, lean_object* v___y_1792_, lean_object* v___y_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_){
_start:
{
uint8_t v___y_19232__boxed_1799_; lean_object* v_res_1800_; 
v___y_19232__boxed_1799_ = lean_unbox(v___y_1792_);
v_res_1800_ = l_List_mapM_loop___at___00Lean_Meta_Closure_collectExprAux_spec__2(v_x_1790_, v_x_1791_, v___y_19232__boxed_1799_, v___y_1793_, v___y_1794_, v___y_1795_, v___y_1796_, v___y_1797_);
lean_dec(v___y_1797_);
lean_dec_ref(v___y_1796_);
lean_dec(v___y_1795_);
lean_dec_ref(v___y_1794_);
lean_dec(v___y_1793_);
return v_res_1800_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Closure_collectExprAux_spec__3_spec__7(uint8_t v___y_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_){
_start:
{
lean_object* v___x_1808_; 
v___x_1808_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Closure_collectExprAux_spec__3_spec__7___redArg(v___y_1806_);
return v___x_1808_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Closure_collectExprAux_spec__3_spec__7___boxed(lean_object* v___y_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_){
_start:
{
uint8_t v___y_19259__boxed_1816_; lean_object* v_res_1817_; 
v___y_19259__boxed_1816_ = lean_unbox(v___y_1809_);
v_res_1817_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Closure_collectExprAux_spec__3_spec__7(v___y_19259__boxed_1816_, v___y_1810_, v___y_1811_, v___y_1812_, v___y_1813_, v___y_1814_);
lean_dec(v___y_1814_);
lean_dec_ref(v___y_1813_);
lean_dec(v___y_1812_);
lean_dec_ref(v___y_1811_);
lean_dec(v___y_1810_);
return v_res_1817_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0_spec__0(lean_object* v_00_u03b2_1818_, lean_object* v_a_1819_, lean_object* v_x_1820_){
_start:
{
lean_object* v___x_1821_; 
v___x_1821_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0_spec__0___redArg(v_a_1819_, v_x_1820_);
return v___x_1821_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1822_, lean_object* v_a_1823_, lean_object* v_x_1824_){
_start:
{
lean_object* v_res_1825_; 
v_res_1825_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0_spec__0(v_00_u03b2_1822_, v_a_1823_, v_x_1824_);
lean_dec(v_x_1824_);
lean_dec_ref(v_a_1823_);
return v_res_1825_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__2(lean_object* v_00_u03b2_1826_, lean_object* v_a_1827_, lean_object* v_x_1828_){
_start:
{
uint8_t v___x_1829_; 
v___x_1829_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__2___redArg(v_a_1827_, v_x_1828_);
return v___x_1829_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1830_, lean_object* v_a_1831_, lean_object* v_x_1832_){
_start:
{
uint8_t v_res_1833_; lean_object* v_r_1834_; 
v_res_1833_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__2(v_00_u03b2_1830_, v_a_1831_, v_x_1832_);
lean_dec(v_x_1832_);
lean_dec_ref(v_a_1831_);
v_r_1834_ = lean_box(v_res_1833_);
return v_r_1834_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__3(lean_object* v_00_u03b2_1835_, lean_object* v_data_1836_){
_start:
{
lean_object* v___x_1837_; 
v___x_1837_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__3___redArg(v_data_1836_);
return v___x_1837_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__4(lean_object* v_00_u03b2_1838_, lean_object* v_a_1839_, lean_object* v_b_1840_, lean_object* v_x_1841_){
_start:
{
lean_object* v___x_1842_; 
v___x_1842_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__4___redArg(v_a_1839_, v_b_1840_, v_x_1841_);
return v___x_1842_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__3_spec__6(lean_object* v_00_u03b2_1843_, lean_object* v_i_1844_, lean_object* v_source_1845_, lean_object* v_target_1846_){
_start:
{
lean_object* v___x_1847_; 
v___x_1847_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__3_spec__6___redArg(v_i_1844_, v_source_1845_, v_target_1846_);
return v___x_1847_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__3_spec__6_spec__10(lean_object* v_00_u03b2_1848_, lean_object* v_x_1849_, lean_object* v_x_1850_){
_start:
{
lean_object* v___x_1851_; 
v___x_1851_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__3_spec__6_spec__10___redArg(v_x_1849_, v_x_1850_);
return v___x_1851_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectExpr(lean_object* v_e_1852_, uint8_t v_a_1853_, lean_object* v_a_1854_, lean_object* v_a_1855_, lean_object* v_a_1856_, lean_object* v_a_1857_, lean_object* v_a_1858_){
_start:
{
lean_object* v___x_1860_; 
v___x_1860_ = l_Lean_Meta_Closure_preprocess(v_e_1852_, v_a_1853_, v_a_1854_, v_a_1855_, v_a_1856_, v_a_1857_, v_a_1858_);
if (lean_obj_tag(v___x_1860_) == 0)
{
lean_object* v_a_1861_; uint8_t v___x_1905_; 
v_a_1861_ = lean_ctor_get(v___x_1860_, 0);
lean_inc(v_a_1861_);
v___x_1905_ = l_Lean_Expr_hasLevelParam(v_a_1861_);
if (v___x_1905_ == 0)
{
uint8_t v___x_1906_; 
v___x_1906_ = l_Lean_Expr_hasFVar(v_a_1861_);
if (v___x_1906_ == 0)
{
uint8_t v___x_1907_; 
v___x_1907_ = l_Lean_Expr_hasMVar(v_a_1861_);
if (v___x_1907_ == 0)
{
lean_dec(v_a_1861_);
return v___x_1860_;
}
else
{
lean_dec_ref(v___x_1860_);
goto v___jp_1862_;
}
}
else
{
lean_dec_ref(v___x_1860_);
goto v___jp_1862_;
}
}
else
{
lean_dec_ref(v___x_1860_);
goto v___jp_1862_;
}
v___jp_1862_:
{
lean_object* v___x_1863_; lean_object* v_visitedExpr_1864_; lean_object* v___x_1865_; 
v___x_1863_ = lean_st_ref_get(v_a_1854_);
v_visitedExpr_1864_ = lean_ctor_get(v___x_1863_, 1);
lean_inc_ref(v_visitedExpr_1864_);
lean_dec(v___x_1863_);
v___x_1865_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0___redArg(v_visitedExpr_1864_, v_a_1861_);
lean_dec_ref(v_visitedExpr_1864_);
if (lean_obj_tag(v___x_1865_) == 0)
{
lean_object* v___x_1866_; 
lean_inc(v_a_1861_);
v___x_1866_ = l_Lean_Meta_Closure_collectExprAux(v_a_1861_, v_a_1853_, v_a_1854_, v_a_1855_, v_a_1856_, v_a_1857_, v_a_1858_);
if (lean_obj_tag(v___x_1866_) == 0)
{
lean_object* v_a_1867_; lean_object* v___x_1869_; uint8_t v_isShared_1870_; uint8_t v_isSharedCheck_1896_; 
v_a_1867_ = lean_ctor_get(v___x_1866_, 0);
v_isSharedCheck_1896_ = !lean_is_exclusive(v___x_1866_);
if (v_isSharedCheck_1896_ == 0)
{
v___x_1869_ = v___x_1866_;
v_isShared_1870_ = v_isSharedCheck_1896_;
goto v_resetjp_1868_;
}
else
{
lean_inc(v_a_1867_);
lean_dec(v___x_1866_);
v___x_1869_ = lean_box(0);
v_isShared_1870_ = v_isSharedCheck_1896_;
goto v_resetjp_1868_;
}
v_resetjp_1868_:
{
lean_object* v___x_1871_; lean_object* v_visitedLevel_1872_; lean_object* v_visitedExpr_1873_; lean_object* v_levelParams_1874_; lean_object* v_nextLevelIdx_1875_; lean_object* v_levelArgs_1876_; lean_object* v_newLocalDecls_1877_; lean_object* v_newLocalDeclsForMVars_1878_; lean_object* v_newLetDecls_1879_; lean_object* v_nextExprIdx_1880_; lean_object* v_exprMVarArgs_1881_; lean_object* v_exprFVarArgs_1882_; lean_object* v_toProcess_1883_; lean_object* v___x_1885_; uint8_t v_isShared_1886_; uint8_t v_isSharedCheck_1895_; 
v___x_1871_ = lean_st_ref_take(v_a_1854_);
v_visitedLevel_1872_ = lean_ctor_get(v___x_1871_, 0);
v_visitedExpr_1873_ = lean_ctor_get(v___x_1871_, 1);
v_levelParams_1874_ = lean_ctor_get(v___x_1871_, 2);
v_nextLevelIdx_1875_ = lean_ctor_get(v___x_1871_, 3);
v_levelArgs_1876_ = lean_ctor_get(v___x_1871_, 4);
v_newLocalDecls_1877_ = lean_ctor_get(v___x_1871_, 5);
v_newLocalDeclsForMVars_1878_ = lean_ctor_get(v___x_1871_, 6);
v_newLetDecls_1879_ = lean_ctor_get(v___x_1871_, 7);
v_nextExprIdx_1880_ = lean_ctor_get(v___x_1871_, 8);
v_exprMVarArgs_1881_ = lean_ctor_get(v___x_1871_, 9);
v_exprFVarArgs_1882_ = lean_ctor_get(v___x_1871_, 10);
v_toProcess_1883_ = lean_ctor_get(v___x_1871_, 11);
v_isSharedCheck_1895_ = !lean_is_exclusive(v___x_1871_);
if (v_isSharedCheck_1895_ == 0)
{
v___x_1885_ = v___x_1871_;
v_isShared_1886_ = v_isSharedCheck_1895_;
goto v_resetjp_1884_;
}
else
{
lean_inc(v_toProcess_1883_);
lean_inc(v_exprFVarArgs_1882_);
lean_inc(v_exprMVarArgs_1881_);
lean_inc(v_nextExprIdx_1880_);
lean_inc(v_newLetDecls_1879_);
lean_inc(v_newLocalDeclsForMVars_1878_);
lean_inc(v_newLocalDecls_1877_);
lean_inc(v_levelArgs_1876_);
lean_inc(v_nextLevelIdx_1875_);
lean_inc(v_levelParams_1874_);
lean_inc(v_visitedExpr_1873_);
lean_inc(v_visitedLevel_1872_);
lean_dec(v___x_1871_);
v___x_1885_ = lean_box(0);
v_isShared_1886_ = v_isSharedCheck_1895_;
goto v_resetjp_1884_;
}
v_resetjp_1884_:
{
lean_object* v___x_1887_; lean_object* v___x_1889_; 
lean_inc(v_a_1867_);
v___x_1887_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1___redArg(v_visitedExpr_1873_, v_a_1861_, v_a_1867_);
if (v_isShared_1886_ == 0)
{
lean_ctor_set(v___x_1885_, 1, v___x_1887_);
v___x_1889_ = v___x_1885_;
goto v_reusejp_1888_;
}
else
{
lean_object* v_reuseFailAlloc_1894_; 
v_reuseFailAlloc_1894_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_1894_, 0, v_visitedLevel_1872_);
lean_ctor_set(v_reuseFailAlloc_1894_, 1, v___x_1887_);
lean_ctor_set(v_reuseFailAlloc_1894_, 2, v_levelParams_1874_);
lean_ctor_set(v_reuseFailAlloc_1894_, 3, v_nextLevelIdx_1875_);
lean_ctor_set(v_reuseFailAlloc_1894_, 4, v_levelArgs_1876_);
lean_ctor_set(v_reuseFailAlloc_1894_, 5, v_newLocalDecls_1877_);
lean_ctor_set(v_reuseFailAlloc_1894_, 6, v_newLocalDeclsForMVars_1878_);
lean_ctor_set(v_reuseFailAlloc_1894_, 7, v_newLetDecls_1879_);
lean_ctor_set(v_reuseFailAlloc_1894_, 8, v_nextExprIdx_1880_);
lean_ctor_set(v_reuseFailAlloc_1894_, 9, v_exprMVarArgs_1881_);
lean_ctor_set(v_reuseFailAlloc_1894_, 10, v_exprFVarArgs_1882_);
lean_ctor_set(v_reuseFailAlloc_1894_, 11, v_toProcess_1883_);
v___x_1889_ = v_reuseFailAlloc_1894_;
goto v_reusejp_1888_;
}
v_reusejp_1888_:
{
lean_object* v___x_1890_; lean_object* v___x_1892_; 
v___x_1890_ = lean_st_ref_set(v_a_1854_, v___x_1889_);
if (v_isShared_1870_ == 0)
{
v___x_1892_ = v___x_1869_;
goto v_reusejp_1891_;
}
else
{
lean_object* v_reuseFailAlloc_1893_; 
v_reuseFailAlloc_1893_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1893_, 0, v_a_1867_);
v___x_1892_ = v_reuseFailAlloc_1893_;
goto v_reusejp_1891_;
}
v_reusejp_1891_:
{
return v___x_1892_;
}
}
}
}
}
else
{
lean_dec(v_a_1861_);
return v___x_1866_;
}
}
else
{
lean_object* v_val_1897_; lean_object* v___x_1899_; uint8_t v_isShared_1900_; uint8_t v_isSharedCheck_1904_; 
lean_dec(v_a_1861_);
v_val_1897_ = lean_ctor_get(v___x_1865_, 0);
v_isSharedCheck_1904_ = !lean_is_exclusive(v___x_1865_);
if (v_isSharedCheck_1904_ == 0)
{
v___x_1899_ = v___x_1865_;
v_isShared_1900_ = v_isSharedCheck_1904_;
goto v_resetjp_1898_;
}
else
{
lean_inc(v_val_1897_);
lean_dec(v___x_1865_);
v___x_1899_ = lean_box(0);
v_isShared_1900_ = v_isSharedCheck_1904_;
goto v_resetjp_1898_;
}
v_resetjp_1898_:
{
lean_object* v___x_1902_; 
if (v_isShared_1900_ == 0)
{
lean_ctor_set_tag(v___x_1899_, 0);
v___x_1902_ = v___x_1899_;
goto v_reusejp_1901_;
}
else
{
lean_object* v_reuseFailAlloc_1903_; 
v_reuseFailAlloc_1903_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1903_, 0, v_val_1897_);
v___x_1902_ = v_reuseFailAlloc_1903_;
goto v_reusejp_1901_;
}
v_reusejp_1901_:
{
return v___x_1902_;
}
}
}
}
}
else
{
return v___x_1860_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectExpr___boxed(lean_object* v_e_1908_, lean_object* v_a_1909_, lean_object* v_a_1910_, lean_object* v_a_1911_, lean_object* v_a_1912_, lean_object* v_a_1913_, lean_object* v_a_1914_, lean_object* v_a_1915_){
_start:
{
uint8_t v_a_boxed_1916_; lean_object* v_res_1917_; 
v_a_boxed_1916_ = lean_unbox(v_a_1909_);
v_res_1917_ = l_Lean_Meta_Closure_collectExpr(v_e_1908_, v_a_boxed_1916_, v_a_1910_, v_a_1911_, v_a_1912_, v_a_1913_, v_a_1914_);
lean_dec(v_a_1914_);
lean_dec_ref(v_a_1913_);
lean_dec(v_a_1912_);
lean_dec_ref(v_a_1911_);
lean_dec(v_a_1910_);
return v_res_1917_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pickNextToProcessAux(lean_object* v_lctx_1918_, lean_object* v_i_1919_, lean_object* v_toProcess_1920_, lean_object* v_elem_1921_){
_start:
{
lean_object* v___x_1922_; uint8_t v___x_1923_; 
v___x_1922_ = lean_array_get_size(v_toProcess_1920_);
v___x_1923_ = lean_nat_dec_lt(v_i_1919_, v___x_1922_);
if (v___x_1923_ == 0)
{
lean_object* v___x_1924_; 
lean_dec(v_i_1919_);
lean_dec_ref(v_lctx_1918_);
v___x_1924_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1924_, 0, v_elem_1921_);
lean_ctor_set(v___x_1924_, 1, v_toProcess_1920_);
return v___x_1924_;
}
else
{
lean_object* v_fvarId_1925_; lean_object* v_elem_x27_1926_; lean_object* v_fvarId_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; uint8_t v___x_1932_; 
v_fvarId_1925_ = lean_ctor_get(v_elem_1921_, 0);
v_elem_x27_1926_ = lean_array_fget_borrowed(v_toProcess_1920_, v_i_1919_);
v_fvarId_1927_ = lean_ctor_get(v_elem_x27_1926_, 0);
lean_inc(v_fvarId_1925_);
lean_inc_ref_n(v_lctx_1918_, 2);
v___x_1928_ = l_Lean_LocalContext_get_x21(v_lctx_1918_, v_fvarId_1925_);
v___x_1929_ = l_Lean_LocalDecl_index(v___x_1928_);
lean_dec_ref(v___x_1928_);
lean_inc(v_fvarId_1927_);
v___x_1930_ = l_Lean_LocalContext_get_x21(v_lctx_1918_, v_fvarId_1927_);
v___x_1931_ = l_Lean_LocalDecl_index(v___x_1930_);
lean_dec_ref(v___x_1930_);
v___x_1932_ = lean_nat_dec_lt(v___x_1929_, v___x_1931_);
lean_dec(v___x_1931_);
lean_dec(v___x_1929_);
if (v___x_1932_ == 0)
{
lean_object* v___x_1933_; lean_object* v___x_1934_; 
v___x_1933_ = lean_unsigned_to_nat(1u);
v___x_1934_ = lean_nat_add(v_i_1919_, v___x_1933_);
lean_dec(v_i_1919_);
v_i_1919_ = v___x_1934_;
goto _start;
}
else
{
lean_object* v___x_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; 
lean_inc(v_elem_x27_1926_);
v___x_1936_ = lean_unsigned_to_nat(1u);
v___x_1937_ = lean_nat_add(v_i_1919_, v___x_1936_);
v___x_1938_ = lean_array_fset(v_toProcess_1920_, v_i_1919_, v_elem_1921_);
lean_dec(v_i_1919_);
v_i_1919_ = v___x_1937_;
v_toProcess_1920_ = v___x_1938_;
v_elem_1921_ = v_elem_x27_1926_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pickNextToProcess_x3f___redArg(lean_object* v_a_1940_, lean_object* v_a_1941_){
_start:
{
lean_object* v___x_1943_; lean_object* v_toProcess_1944_; lean_object* v___x_1945_; lean_object* v___x_1946_; uint8_t v___x_1947_; 
v___x_1943_ = lean_st_ref_get(v_a_1940_);
v_toProcess_1944_ = lean_ctor_get(v___x_1943_, 11);
lean_inc_ref(v_toProcess_1944_);
lean_dec(v___x_1943_);
v___x_1945_ = lean_array_get_size(v_toProcess_1944_);
lean_dec_ref(v_toProcess_1944_);
v___x_1946_ = lean_unsigned_to_nat(0u);
v___x_1947_ = lean_nat_dec_eq(v___x_1945_, v___x_1946_);
if (v___x_1947_ == 0)
{
lean_object* v___x_1948_; lean_object* v_lctx_1949_; lean_object* v_visitedLevel_1950_; lean_object* v_visitedExpr_1951_; lean_object* v_levelParams_1952_; lean_object* v_nextLevelIdx_1953_; lean_object* v_levelArgs_1954_; lean_object* v_newLocalDecls_1955_; lean_object* v_newLocalDeclsForMVars_1956_; lean_object* v_newLetDecls_1957_; lean_object* v_nextExprIdx_1958_; lean_object* v_exprMVarArgs_1959_; lean_object* v_exprFVarArgs_1960_; lean_object* v_toProcess_1961_; lean_object* v___x_1963_; uint8_t v_isShared_1964_; uint8_t v_isSharedCheck_1980_; 
v___x_1948_ = lean_st_ref_take(v_a_1940_);
v_lctx_1949_ = lean_ctor_get(v_a_1941_, 2);
v_visitedLevel_1950_ = lean_ctor_get(v___x_1948_, 0);
v_visitedExpr_1951_ = lean_ctor_get(v___x_1948_, 1);
v_levelParams_1952_ = lean_ctor_get(v___x_1948_, 2);
v_nextLevelIdx_1953_ = lean_ctor_get(v___x_1948_, 3);
v_levelArgs_1954_ = lean_ctor_get(v___x_1948_, 4);
v_newLocalDecls_1955_ = lean_ctor_get(v___x_1948_, 5);
v_newLocalDeclsForMVars_1956_ = lean_ctor_get(v___x_1948_, 6);
v_newLetDecls_1957_ = lean_ctor_get(v___x_1948_, 7);
v_nextExprIdx_1958_ = lean_ctor_get(v___x_1948_, 8);
v_exprMVarArgs_1959_ = lean_ctor_get(v___x_1948_, 9);
v_exprFVarArgs_1960_ = lean_ctor_get(v___x_1948_, 10);
v_toProcess_1961_ = lean_ctor_get(v___x_1948_, 11);
v_isSharedCheck_1980_ = !lean_is_exclusive(v___x_1948_);
if (v_isSharedCheck_1980_ == 0)
{
v___x_1963_ = v___x_1948_;
v_isShared_1964_ = v_isSharedCheck_1980_;
goto v_resetjp_1962_;
}
else
{
lean_inc(v_toProcess_1961_);
lean_inc(v_exprFVarArgs_1960_);
lean_inc(v_exprMVarArgs_1959_);
lean_inc(v_nextExprIdx_1958_);
lean_inc(v_newLetDecls_1957_);
lean_inc(v_newLocalDeclsForMVars_1956_);
lean_inc(v_newLocalDecls_1955_);
lean_inc(v_levelArgs_1954_);
lean_inc(v_nextLevelIdx_1953_);
lean_inc(v_levelParams_1952_);
lean_inc(v_visitedExpr_1951_);
lean_inc(v_visitedLevel_1950_);
lean_dec(v___x_1948_);
v___x_1963_ = lean_box(0);
v_isShared_1964_ = v_isSharedCheck_1980_;
goto v_resetjp_1962_;
}
v_resetjp_1962_:
{
lean_object* v___x_1965_; lean_object* v___x_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; lean_object* v_fst_1972_; lean_object* v_snd_1973_; lean_object* v___x_1975_; 
v___x_1965_ = ((lean_object*)(l_Lean_Meta_Closure_instInhabitedToProcessElement_default));
v___x_1966_ = lean_array_get_size(v_toProcess_1961_);
v___x_1967_ = lean_unsigned_to_nat(1u);
v___x_1968_ = lean_nat_sub(v___x_1966_, v___x_1967_);
v___x_1969_ = lean_array_get(v___x_1965_, v_toProcess_1961_, v___x_1968_);
lean_dec(v___x_1968_);
v___x_1970_ = lean_array_pop(v_toProcess_1961_);
lean_inc_ref(v_lctx_1949_);
v___x_1971_ = l_Lean_Meta_Closure_pickNextToProcessAux(v_lctx_1949_, v___x_1946_, v___x_1970_, v___x_1969_);
v_fst_1972_ = lean_ctor_get(v___x_1971_, 0);
lean_inc(v_fst_1972_);
v_snd_1973_ = lean_ctor_get(v___x_1971_, 1);
lean_inc(v_snd_1973_);
lean_dec_ref(v___x_1971_);
if (v_isShared_1964_ == 0)
{
lean_ctor_set(v___x_1963_, 11, v_snd_1973_);
v___x_1975_ = v___x_1963_;
goto v_reusejp_1974_;
}
else
{
lean_object* v_reuseFailAlloc_1979_; 
v_reuseFailAlloc_1979_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_1979_, 0, v_visitedLevel_1950_);
lean_ctor_set(v_reuseFailAlloc_1979_, 1, v_visitedExpr_1951_);
lean_ctor_set(v_reuseFailAlloc_1979_, 2, v_levelParams_1952_);
lean_ctor_set(v_reuseFailAlloc_1979_, 3, v_nextLevelIdx_1953_);
lean_ctor_set(v_reuseFailAlloc_1979_, 4, v_levelArgs_1954_);
lean_ctor_set(v_reuseFailAlloc_1979_, 5, v_newLocalDecls_1955_);
lean_ctor_set(v_reuseFailAlloc_1979_, 6, v_newLocalDeclsForMVars_1956_);
lean_ctor_set(v_reuseFailAlloc_1979_, 7, v_newLetDecls_1957_);
lean_ctor_set(v_reuseFailAlloc_1979_, 8, v_nextExprIdx_1958_);
lean_ctor_set(v_reuseFailAlloc_1979_, 9, v_exprMVarArgs_1959_);
lean_ctor_set(v_reuseFailAlloc_1979_, 10, v_exprFVarArgs_1960_);
lean_ctor_set(v_reuseFailAlloc_1979_, 11, v_snd_1973_);
v___x_1975_ = v_reuseFailAlloc_1979_;
goto v_reusejp_1974_;
}
v_reusejp_1974_:
{
lean_object* v___x_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; 
v___x_1976_ = lean_st_ref_set(v_a_1940_, v___x_1975_);
v___x_1977_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1977_, 0, v_fst_1972_);
v___x_1978_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1978_, 0, v___x_1977_);
return v___x_1978_;
}
}
}
else
{
lean_object* v___x_1981_; lean_object* v___x_1982_; 
v___x_1981_ = lean_box(0);
v___x_1982_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1982_, 0, v___x_1981_);
return v___x_1982_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pickNextToProcess_x3f___redArg___boxed(lean_object* v_a_1983_, lean_object* v_a_1984_, lean_object* v_a_1985_){
_start:
{
lean_object* v_res_1986_; 
v_res_1986_ = l_Lean_Meta_Closure_pickNextToProcess_x3f___redArg(v_a_1983_, v_a_1984_);
lean_dec_ref(v_a_1984_);
lean_dec(v_a_1983_);
return v_res_1986_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pickNextToProcess_x3f(uint8_t v_a_1987_, lean_object* v_a_1988_, lean_object* v_a_1989_, lean_object* v_a_1990_, lean_object* v_a_1991_, lean_object* v_a_1992_){
_start:
{
lean_object* v___x_1994_; 
v___x_1994_ = l_Lean_Meta_Closure_pickNextToProcess_x3f___redArg(v_a_1988_, v_a_1989_);
return v___x_1994_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pickNextToProcess_x3f___boxed(lean_object* v_a_1995_, lean_object* v_a_1996_, lean_object* v_a_1997_, lean_object* v_a_1998_, lean_object* v_a_1999_, lean_object* v_a_2000_, lean_object* v_a_2001_){
_start:
{
uint8_t v_a_boxed_2002_; lean_object* v_res_2003_; 
v_a_boxed_2002_ = lean_unbox(v_a_1995_);
v_res_2003_ = l_Lean_Meta_Closure_pickNextToProcess_x3f(v_a_boxed_2002_, v_a_1996_, v_a_1997_, v_a_1998_, v_a_1999_, v_a_2000_);
lean_dec(v_a_2000_);
lean_dec_ref(v_a_1999_);
lean_dec(v_a_1998_);
lean_dec_ref(v_a_1997_);
lean_dec(v_a_1996_);
return v_res_2003_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushFVarArg___redArg(lean_object* v_e_2004_, lean_object* v_a_2005_){
_start:
{
lean_object* v___x_2007_; lean_object* v_visitedLevel_2008_; lean_object* v_visitedExpr_2009_; lean_object* v_levelParams_2010_; lean_object* v_nextLevelIdx_2011_; lean_object* v_levelArgs_2012_; lean_object* v_newLocalDecls_2013_; lean_object* v_newLocalDeclsForMVars_2014_; lean_object* v_newLetDecls_2015_; lean_object* v_nextExprIdx_2016_; lean_object* v_exprMVarArgs_2017_; lean_object* v_exprFVarArgs_2018_; lean_object* v_toProcess_2019_; lean_object* v___x_2021_; uint8_t v_isShared_2022_; uint8_t v_isSharedCheck_2030_; 
v___x_2007_ = lean_st_ref_take(v_a_2005_);
v_visitedLevel_2008_ = lean_ctor_get(v___x_2007_, 0);
v_visitedExpr_2009_ = lean_ctor_get(v___x_2007_, 1);
v_levelParams_2010_ = lean_ctor_get(v___x_2007_, 2);
v_nextLevelIdx_2011_ = lean_ctor_get(v___x_2007_, 3);
v_levelArgs_2012_ = lean_ctor_get(v___x_2007_, 4);
v_newLocalDecls_2013_ = lean_ctor_get(v___x_2007_, 5);
v_newLocalDeclsForMVars_2014_ = lean_ctor_get(v___x_2007_, 6);
v_newLetDecls_2015_ = lean_ctor_get(v___x_2007_, 7);
v_nextExprIdx_2016_ = lean_ctor_get(v___x_2007_, 8);
v_exprMVarArgs_2017_ = lean_ctor_get(v___x_2007_, 9);
v_exprFVarArgs_2018_ = lean_ctor_get(v___x_2007_, 10);
v_toProcess_2019_ = lean_ctor_get(v___x_2007_, 11);
v_isSharedCheck_2030_ = !lean_is_exclusive(v___x_2007_);
if (v_isSharedCheck_2030_ == 0)
{
v___x_2021_ = v___x_2007_;
v_isShared_2022_ = v_isSharedCheck_2030_;
goto v_resetjp_2020_;
}
else
{
lean_inc(v_toProcess_2019_);
lean_inc(v_exprFVarArgs_2018_);
lean_inc(v_exprMVarArgs_2017_);
lean_inc(v_nextExprIdx_2016_);
lean_inc(v_newLetDecls_2015_);
lean_inc(v_newLocalDeclsForMVars_2014_);
lean_inc(v_newLocalDecls_2013_);
lean_inc(v_levelArgs_2012_);
lean_inc(v_nextLevelIdx_2011_);
lean_inc(v_levelParams_2010_);
lean_inc(v_visitedExpr_2009_);
lean_inc(v_visitedLevel_2008_);
lean_dec(v___x_2007_);
v___x_2021_ = lean_box(0);
v_isShared_2022_ = v_isSharedCheck_2030_;
goto v_resetjp_2020_;
}
v_resetjp_2020_:
{
lean_object* v___x_2023_; lean_object* v___x_2025_; 
v___x_2023_ = lean_array_push(v_exprFVarArgs_2018_, v_e_2004_);
if (v_isShared_2022_ == 0)
{
lean_ctor_set(v___x_2021_, 10, v___x_2023_);
v___x_2025_ = v___x_2021_;
goto v_reusejp_2024_;
}
else
{
lean_object* v_reuseFailAlloc_2029_; 
v_reuseFailAlloc_2029_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_2029_, 0, v_visitedLevel_2008_);
lean_ctor_set(v_reuseFailAlloc_2029_, 1, v_visitedExpr_2009_);
lean_ctor_set(v_reuseFailAlloc_2029_, 2, v_levelParams_2010_);
lean_ctor_set(v_reuseFailAlloc_2029_, 3, v_nextLevelIdx_2011_);
lean_ctor_set(v_reuseFailAlloc_2029_, 4, v_levelArgs_2012_);
lean_ctor_set(v_reuseFailAlloc_2029_, 5, v_newLocalDecls_2013_);
lean_ctor_set(v_reuseFailAlloc_2029_, 6, v_newLocalDeclsForMVars_2014_);
lean_ctor_set(v_reuseFailAlloc_2029_, 7, v_newLetDecls_2015_);
lean_ctor_set(v_reuseFailAlloc_2029_, 8, v_nextExprIdx_2016_);
lean_ctor_set(v_reuseFailAlloc_2029_, 9, v_exprMVarArgs_2017_);
lean_ctor_set(v_reuseFailAlloc_2029_, 10, v___x_2023_);
lean_ctor_set(v_reuseFailAlloc_2029_, 11, v_toProcess_2019_);
v___x_2025_ = v_reuseFailAlloc_2029_;
goto v_reusejp_2024_;
}
v_reusejp_2024_:
{
lean_object* v___x_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; 
v___x_2026_ = lean_st_ref_set(v_a_2005_, v___x_2025_);
v___x_2027_ = lean_box(0);
v___x_2028_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2028_, 0, v___x_2027_);
return v___x_2028_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushFVarArg___redArg___boxed(lean_object* v_e_2031_, lean_object* v_a_2032_, lean_object* v_a_2033_){
_start:
{
lean_object* v_res_2034_; 
v_res_2034_ = l_Lean_Meta_Closure_pushFVarArg___redArg(v_e_2031_, v_a_2032_);
lean_dec(v_a_2032_);
return v_res_2034_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushFVarArg(lean_object* v_e_2035_, uint8_t v_a_2036_, lean_object* v_a_2037_, lean_object* v_a_2038_, lean_object* v_a_2039_, lean_object* v_a_2040_, lean_object* v_a_2041_){
_start:
{
lean_object* v___x_2043_; 
v___x_2043_ = l_Lean_Meta_Closure_pushFVarArg___redArg(v_e_2035_, v_a_2037_);
return v___x_2043_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushFVarArg___boxed(lean_object* v_e_2044_, lean_object* v_a_2045_, lean_object* v_a_2046_, lean_object* v_a_2047_, lean_object* v_a_2048_, lean_object* v_a_2049_, lean_object* v_a_2050_, lean_object* v_a_2051_){
_start:
{
uint8_t v_a_boxed_2052_; lean_object* v_res_2053_; 
v_a_boxed_2052_ = lean_unbox(v_a_2045_);
v_res_2053_ = l_Lean_Meta_Closure_pushFVarArg(v_e_2044_, v_a_boxed_2052_, v_a_2046_, v_a_2047_, v_a_2048_, v_a_2049_, v_a_2050_);
lean_dec(v_a_2050_);
lean_dec_ref(v_a_2049_);
lean_dec(v_a_2048_);
lean_dec_ref(v_a_2047_);
lean_dec(v_a_2046_);
return v_res_2053_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushLocalDecl(lean_object* v_newFVarId_2054_, lean_object* v_userName_2055_, lean_object* v_type_2056_, uint8_t v_bi_2057_, uint8_t v_a_2058_, lean_object* v_a_2059_, lean_object* v_a_2060_, lean_object* v_a_2061_, lean_object* v_a_2062_, lean_object* v_a_2063_){
_start:
{
lean_object* v___x_2065_; 
v___x_2065_ = l_Lean_Meta_Closure_collectExpr(v_type_2056_, v_a_2058_, v_a_2059_, v_a_2060_, v_a_2061_, v_a_2062_, v_a_2063_);
if (lean_obj_tag(v___x_2065_) == 0)
{
lean_object* v_a_2066_; lean_object* v___x_2068_; uint8_t v_isShared_2069_; uint8_t v_isSharedCheck_2099_; 
v_a_2066_ = lean_ctor_get(v___x_2065_, 0);
v_isSharedCheck_2099_ = !lean_is_exclusive(v___x_2065_);
if (v_isSharedCheck_2099_ == 0)
{
v___x_2068_ = v___x_2065_;
v_isShared_2069_ = v_isSharedCheck_2099_;
goto v_resetjp_2067_;
}
else
{
lean_inc(v_a_2066_);
lean_dec(v___x_2065_);
v___x_2068_ = lean_box(0);
v_isShared_2069_ = v_isSharedCheck_2099_;
goto v_resetjp_2067_;
}
v_resetjp_2067_:
{
lean_object* v___x_2070_; lean_object* v_visitedLevel_2071_; lean_object* v_visitedExpr_2072_; lean_object* v_levelParams_2073_; lean_object* v_nextLevelIdx_2074_; lean_object* v_levelArgs_2075_; lean_object* v_newLocalDecls_2076_; lean_object* v_newLocalDeclsForMVars_2077_; lean_object* v_newLetDecls_2078_; lean_object* v_nextExprIdx_2079_; lean_object* v_exprMVarArgs_2080_; lean_object* v_exprFVarArgs_2081_; lean_object* v_toProcess_2082_; lean_object* v___x_2084_; uint8_t v_isShared_2085_; uint8_t v_isSharedCheck_2098_; 
v___x_2070_ = lean_st_ref_take(v_a_2059_);
v_visitedLevel_2071_ = lean_ctor_get(v___x_2070_, 0);
v_visitedExpr_2072_ = lean_ctor_get(v___x_2070_, 1);
v_levelParams_2073_ = lean_ctor_get(v___x_2070_, 2);
v_nextLevelIdx_2074_ = lean_ctor_get(v___x_2070_, 3);
v_levelArgs_2075_ = lean_ctor_get(v___x_2070_, 4);
v_newLocalDecls_2076_ = lean_ctor_get(v___x_2070_, 5);
v_newLocalDeclsForMVars_2077_ = lean_ctor_get(v___x_2070_, 6);
v_newLetDecls_2078_ = lean_ctor_get(v___x_2070_, 7);
v_nextExprIdx_2079_ = lean_ctor_get(v___x_2070_, 8);
v_exprMVarArgs_2080_ = lean_ctor_get(v___x_2070_, 9);
v_exprFVarArgs_2081_ = lean_ctor_get(v___x_2070_, 10);
v_toProcess_2082_ = lean_ctor_get(v___x_2070_, 11);
v_isSharedCheck_2098_ = !lean_is_exclusive(v___x_2070_);
if (v_isSharedCheck_2098_ == 0)
{
v___x_2084_ = v___x_2070_;
v_isShared_2085_ = v_isSharedCheck_2098_;
goto v_resetjp_2083_;
}
else
{
lean_inc(v_toProcess_2082_);
lean_inc(v_exprFVarArgs_2081_);
lean_inc(v_exprMVarArgs_2080_);
lean_inc(v_nextExprIdx_2079_);
lean_inc(v_newLetDecls_2078_);
lean_inc(v_newLocalDeclsForMVars_2077_);
lean_inc(v_newLocalDecls_2076_);
lean_inc(v_levelArgs_2075_);
lean_inc(v_nextLevelIdx_2074_);
lean_inc(v_levelParams_2073_);
lean_inc(v_visitedExpr_2072_);
lean_inc(v_visitedLevel_2071_);
lean_dec(v___x_2070_);
v___x_2084_ = lean_box(0);
v_isShared_2085_ = v_isSharedCheck_2098_;
goto v_resetjp_2083_;
}
v_resetjp_2083_:
{
lean_object* v___x_2086_; uint8_t v___x_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v___x_2091_; 
v___x_2086_ = lean_unsigned_to_nat(0u);
v___x_2087_ = 0;
v___x_2088_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2088_, 0, v___x_2086_);
lean_ctor_set(v___x_2088_, 1, v_newFVarId_2054_);
lean_ctor_set(v___x_2088_, 2, v_userName_2055_);
lean_ctor_set(v___x_2088_, 3, v_a_2066_);
lean_ctor_set_uint8(v___x_2088_, sizeof(void*)*4, v_bi_2057_);
lean_ctor_set_uint8(v___x_2088_, sizeof(void*)*4 + 1, v___x_2087_);
v___x_2089_ = lean_array_push(v_newLocalDecls_2076_, v___x_2088_);
if (v_isShared_2085_ == 0)
{
lean_ctor_set(v___x_2084_, 5, v___x_2089_);
v___x_2091_ = v___x_2084_;
goto v_reusejp_2090_;
}
else
{
lean_object* v_reuseFailAlloc_2097_; 
v_reuseFailAlloc_2097_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_2097_, 0, v_visitedLevel_2071_);
lean_ctor_set(v_reuseFailAlloc_2097_, 1, v_visitedExpr_2072_);
lean_ctor_set(v_reuseFailAlloc_2097_, 2, v_levelParams_2073_);
lean_ctor_set(v_reuseFailAlloc_2097_, 3, v_nextLevelIdx_2074_);
lean_ctor_set(v_reuseFailAlloc_2097_, 4, v_levelArgs_2075_);
lean_ctor_set(v_reuseFailAlloc_2097_, 5, v___x_2089_);
lean_ctor_set(v_reuseFailAlloc_2097_, 6, v_newLocalDeclsForMVars_2077_);
lean_ctor_set(v_reuseFailAlloc_2097_, 7, v_newLetDecls_2078_);
lean_ctor_set(v_reuseFailAlloc_2097_, 8, v_nextExprIdx_2079_);
lean_ctor_set(v_reuseFailAlloc_2097_, 9, v_exprMVarArgs_2080_);
lean_ctor_set(v_reuseFailAlloc_2097_, 10, v_exprFVarArgs_2081_);
lean_ctor_set(v_reuseFailAlloc_2097_, 11, v_toProcess_2082_);
v___x_2091_ = v_reuseFailAlloc_2097_;
goto v_reusejp_2090_;
}
v_reusejp_2090_:
{
lean_object* v___x_2092_; lean_object* v___x_2093_; lean_object* v___x_2095_; 
v___x_2092_ = lean_st_ref_set(v_a_2059_, v___x_2091_);
v___x_2093_ = lean_box(0);
if (v_isShared_2069_ == 0)
{
lean_ctor_set(v___x_2068_, 0, v___x_2093_);
v___x_2095_ = v___x_2068_;
goto v_reusejp_2094_;
}
else
{
lean_object* v_reuseFailAlloc_2096_; 
v_reuseFailAlloc_2096_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2096_, 0, v___x_2093_);
v___x_2095_ = v_reuseFailAlloc_2096_;
goto v_reusejp_2094_;
}
v_reusejp_2094_:
{
return v___x_2095_;
}
}
}
}
}
else
{
lean_object* v_a_2100_; lean_object* v___x_2102_; uint8_t v_isShared_2103_; uint8_t v_isSharedCheck_2107_; 
lean_dec(v_userName_2055_);
lean_dec(v_newFVarId_2054_);
v_a_2100_ = lean_ctor_get(v___x_2065_, 0);
v_isSharedCheck_2107_ = !lean_is_exclusive(v___x_2065_);
if (v_isSharedCheck_2107_ == 0)
{
v___x_2102_ = v___x_2065_;
v_isShared_2103_ = v_isSharedCheck_2107_;
goto v_resetjp_2101_;
}
else
{
lean_inc(v_a_2100_);
lean_dec(v___x_2065_);
v___x_2102_ = lean_box(0);
v_isShared_2103_ = v_isSharedCheck_2107_;
goto v_resetjp_2101_;
}
v_resetjp_2101_:
{
lean_object* v___x_2105_; 
if (v_isShared_2103_ == 0)
{
v___x_2105_ = v___x_2102_;
goto v_reusejp_2104_;
}
else
{
lean_object* v_reuseFailAlloc_2106_; 
v_reuseFailAlloc_2106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2106_, 0, v_a_2100_);
v___x_2105_ = v_reuseFailAlloc_2106_;
goto v_reusejp_2104_;
}
v_reusejp_2104_:
{
return v___x_2105_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushLocalDecl___boxed(lean_object* v_newFVarId_2108_, lean_object* v_userName_2109_, lean_object* v_type_2110_, lean_object* v_bi_2111_, lean_object* v_a_2112_, lean_object* v_a_2113_, lean_object* v_a_2114_, lean_object* v_a_2115_, lean_object* v_a_2116_, lean_object* v_a_2117_, lean_object* v_a_2118_){
_start:
{
uint8_t v_bi_boxed_2119_; uint8_t v_a_boxed_2120_; lean_object* v_res_2121_; 
v_bi_boxed_2119_ = lean_unbox(v_bi_2111_);
v_a_boxed_2120_ = lean_unbox(v_a_2112_);
v_res_2121_ = l_Lean_Meta_Closure_pushLocalDecl(v_newFVarId_2108_, v_userName_2109_, v_type_2110_, v_bi_boxed_2119_, v_a_boxed_2120_, v_a_2113_, v_a_2114_, v_a_2115_, v_a_2116_, v_a_2117_);
lean_dec(v_a_2117_);
lean_dec_ref(v_a_2116_);
lean_dec(v_a_2115_);
lean_dec_ref(v_a_2114_);
lean_dec(v_a_2113_);
return v_res_2121_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Closure_process_spec__0___redArg(lean_object* v_k_2122_, lean_object* v_t_2123_){
_start:
{
if (lean_obj_tag(v_t_2123_) == 0)
{
lean_object* v_k_2124_; lean_object* v_l_2125_; lean_object* v_r_2126_; uint8_t v___x_2127_; 
v_k_2124_ = lean_ctor_get(v_t_2123_, 1);
v_l_2125_ = lean_ctor_get(v_t_2123_, 3);
v_r_2126_ = lean_ctor_get(v_t_2123_, 4);
v___x_2127_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_2122_, v_k_2124_);
switch(v___x_2127_)
{
case 0:
{
v_t_2123_ = v_l_2125_;
goto _start;
}
case 1:
{
uint8_t v___x_2129_; 
v___x_2129_ = 1;
return v___x_2129_;
}
default: 
{
v_t_2123_ = v_r_2126_;
goto _start;
}
}
}
else
{
uint8_t v___x_2131_; 
v___x_2131_ = 0;
return v___x_2131_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Closure_process_spec__0___redArg___boxed(lean_object* v_k_2132_, lean_object* v_t_2133_){
_start:
{
uint8_t v_res_2134_; lean_object* v_r_2135_; 
v_res_2134_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Closure_process_spec__0___redArg(v_k_2132_, v_t_2133_);
lean_dec(v_t_2133_);
lean_dec(v_k_2132_);
v_r_2135_ = lean_box(v_res_2134_);
return v_r_2135_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Closure_process_spec__1(lean_object* v_newFVarId_2136_, lean_object* v_a_2137_, size_t v_sz_2138_, size_t v_i_2139_, lean_object* v_bs_2140_){
_start:
{
uint8_t v___x_2141_; 
v___x_2141_ = lean_usize_dec_lt(v_i_2139_, v_sz_2138_);
if (v___x_2141_ == 0)
{
lean_dec(v_newFVarId_2136_);
return v_bs_2140_;
}
else
{
lean_object* v_v_2142_; lean_object* v___x_2143_; lean_object* v_bs_x27_2144_; lean_object* v___x_2145_; size_t v___x_2146_; size_t v___x_2147_; lean_object* v___x_2148_; 
v_v_2142_ = lean_array_uget(v_bs_2140_, v_i_2139_);
v___x_2143_ = lean_unsigned_to_nat(0u);
v_bs_x27_2144_ = lean_array_uset(v_bs_2140_, v_i_2139_, v___x_2143_);
lean_inc(v_newFVarId_2136_);
v___x_2145_ = l_Lean_LocalDecl_replaceFVarId(v_newFVarId_2136_, v_a_2137_, v_v_2142_);
v___x_2146_ = ((size_t)1ULL);
v___x_2147_ = lean_usize_add(v_i_2139_, v___x_2146_);
v___x_2148_ = lean_array_uset(v_bs_x27_2144_, v_i_2139_, v___x_2145_);
v_i_2139_ = v___x_2147_;
v_bs_2140_ = v___x_2148_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Closure_process_spec__1___boxed(lean_object* v_newFVarId_2150_, lean_object* v_a_2151_, lean_object* v_sz_2152_, lean_object* v_i_2153_, lean_object* v_bs_2154_){
_start:
{
size_t v_sz_boxed_2155_; size_t v_i_boxed_2156_; lean_object* v_res_2157_; 
v_sz_boxed_2155_ = lean_unbox_usize(v_sz_2152_);
lean_dec(v_sz_2152_);
v_i_boxed_2156_ = lean_unbox_usize(v_i_2153_);
lean_dec(v_i_2153_);
v_res_2157_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Closure_process_spec__1(v_newFVarId_2150_, v_a_2151_, v_sz_boxed_2155_, v_i_boxed_2156_, v_bs_2154_);
lean_dec_ref(v_a_2151_);
return v_res_2157_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_process(uint8_t v_a_2158_, lean_object* v_a_2159_, lean_object* v_a_2160_, lean_object* v_a_2161_, lean_object* v_a_2162_, lean_object* v_a_2163_){
_start:
{
lean_object* v___x_2165_; 
v___x_2165_ = l_Lean_Meta_Closure_pickNextToProcess_x3f___redArg(v_a_2159_, v_a_2160_);
if (lean_obj_tag(v___x_2165_) == 0)
{
lean_object* v_a_2166_; lean_object* v___x_2168_; uint8_t v_isShared_2169_; uint8_t v_isSharedCheck_2293_; 
v_a_2166_ = lean_ctor_get(v___x_2165_, 0);
v_isSharedCheck_2293_ = !lean_is_exclusive(v___x_2165_);
if (v_isSharedCheck_2293_ == 0)
{
v___x_2168_ = v___x_2165_;
v_isShared_2169_ = v_isSharedCheck_2293_;
goto v_resetjp_2167_;
}
else
{
lean_inc(v_a_2166_);
lean_dec(v___x_2165_);
v___x_2168_ = lean_box(0);
v_isShared_2169_ = v_isSharedCheck_2293_;
goto v_resetjp_2167_;
}
v_resetjp_2167_:
{
if (lean_obj_tag(v_a_2166_) == 0)
{
lean_object* v___x_2170_; lean_object* v___x_2172_; 
v___x_2170_ = lean_box(0);
if (v_isShared_2169_ == 0)
{
lean_ctor_set(v___x_2168_, 0, v___x_2170_);
v___x_2172_ = v___x_2168_;
goto v_reusejp_2171_;
}
else
{
lean_object* v_reuseFailAlloc_2173_; 
v_reuseFailAlloc_2173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2173_, 0, v___x_2170_);
v___x_2172_ = v_reuseFailAlloc_2173_;
goto v_reusejp_2171_;
}
v_reusejp_2171_:
{
return v___x_2172_;
}
}
else
{
lean_object* v_val_2174_; lean_object* v_fvarId_2175_; lean_object* v_newFVarId_2176_; lean_object* v___x_2177_; 
lean_del_object(v___x_2168_);
v_val_2174_ = lean_ctor_get(v_a_2166_, 0);
lean_inc(v_val_2174_);
lean_dec_ref(v_a_2166_);
v_fvarId_2175_ = lean_ctor_get(v_val_2174_, 0);
lean_inc_n(v_fvarId_2175_, 2);
v_newFVarId_2176_ = lean_ctor_get(v_val_2174_, 1);
lean_inc(v_newFVarId_2176_);
lean_dec(v_val_2174_);
v___x_2177_ = l_Lean_FVarId_getDecl___redArg(v_fvarId_2175_, v_a_2160_, v_a_2162_, v_a_2163_);
if (lean_obj_tag(v___x_2177_) == 0)
{
lean_object* v_a_2178_; 
v_a_2178_ = lean_ctor_get(v___x_2177_, 0);
lean_inc(v_a_2178_);
lean_dec_ref(v___x_2177_);
if (lean_obj_tag(v_a_2178_) == 0)
{
lean_object* v_userName_2179_; lean_object* v_type_2180_; uint8_t v_bi_2181_; lean_object* v___x_2182_; 
v_userName_2179_ = lean_ctor_get(v_a_2178_, 2);
lean_inc(v_userName_2179_);
v_type_2180_ = lean_ctor_get(v_a_2178_, 3);
lean_inc_ref(v_type_2180_);
v_bi_2181_ = lean_ctor_get_uint8(v_a_2178_, sizeof(void*)*4);
lean_dec_ref(v_a_2178_);
v___x_2182_ = l_Lean_Meta_Closure_pushLocalDecl(v_newFVarId_2176_, v_userName_2179_, v_type_2180_, v_bi_2181_, v_a_2158_, v_a_2159_, v_a_2160_, v_a_2161_, v_a_2162_, v_a_2163_);
if (lean_obj_tag(v___x_2182_) == 0)
{
lean_object* v___x_2183_; lean_object* v___x_2184_; 
lean_dec_ref(v___x_2182_);
v___x_2183_ = l_Lean_mkFVar(v_fvarId_2175_);
v___x_2184_ = l_Lean_Meta_Closure_pushFVarArg___redArg(v___x_2183_, v_a_2159_);
if (lean_obj_tag(v___x_2184_) == 0)
{
lean_dec_ref(v___x_2184_);
goto _start;
}
else
{
return v___x_2184_;
}
}
else
{
lean_dec(v_fvarId_2175_);
return v___x_2182_;
}
}
else
{
lean_object* v_userName_2186_; lean_object* v_type_2187_; lean_object* v_value_2188_; uint8_t v_nondep_2189_; lean_object* v___x_2191_; uint8_t v_isShared_2192_; uint8_t v_isSharedCheck_2282_; 
v_userName_2186_ = lean_ctor_get(v_a_2178_, 2);
v_type_2187_ = lean_ctor_get(v_a_2178_, 3);
v_value_2188_ = lean_ctor_get(v_a_2178_, 4);
v_nondep_2189_ = lean_ctor_get_uint8(v_a_2178_, sizeof(void*)*5);
v_isSharedCheck_2282_ = !lean_is_exclusive(v_a_2178_);
if (v_isSharedCheck_2282_ == 0)
{
lean_object* v_unused_2283_; lean_object* v_unused_2284_; 
v_unused_2283_ = lean_ctor_get(v_a_2178_, 1);
lean_dec(v_unused_2283_);
v_unused_2284_ = lean_ctor_get(v_a_2178_, 0);
lean_dec(v_unused_2284_);
v___x_2191_ = v_a_2178_;
v_isShared_2192_ = v_isSharedCheck_2282_;
goto v_resetjp_2190_;
}
else
{
lean_inc(v_value_2188_);
lean_inc(v_type_2187_);
lean_inc(v_userName_2186_);
lean_dec(v_a_2178_);
v___x_2191_ = lean_box(0);
v_isShared_2192_ = v_isSharedCheck_2282_;
goto v_resetjp_2190_;
}
v_resetjp_2190_:
{
lean_object* v___x_2193_; 
v___x_2193_ = l_Lean_Meta_getZetaDeltaFVarIds___redArg(v_a_2161_);
if (lean_obj_tag(v___x_2193_) == 0)
{
lean_object* v_a_2194_; 
v_a_2194_ = lean_ctor_get(v___x_2193_, 0);
lean_inc(v_a_2194_);
lean_dec_ref(v___x_2193_);
if (v_nondep_2189_ == 0)
{
uint8_t v___x_2201_; 
v___x_2201_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Closure_process_spec__0___redArg(v_fvarId_2175_, v_a_2194_);
lean_dec(v_a_2194_);
if (v___x_2201_ == 0)
{
lean_del_object(v___x_2191_);
lean_dec_ref(v_value_2188_);
goto v___jp_2195_;
}
else
{
lean_object* v___x_2202_; 
lean_dec(v_fvarId_2175_);
v___x_2202_ = l_Lean_Meta_Closure_collectExpr(v_type_2187_, v_a_2158_, v_a_2159_, v_a_2160_, v_a_2161_, v_a_2162_, v_a_2163_);
if (lean_obj_tag(v___x_2202_) == 0)
{
lean_object* v_a_2203_; lean_object* v___x_2204_; 
v_a_2203_ = lean_ctor_get(v___x_2202_, 0);
lean_inc(v_a_2203_);
lean_dec_ref(v___x_2202_);
v___x_2204_ = l_Lean_Meta_Closure_collectExpr(v_value_2188_, v_a_2158_, v_a_2159_, v_a_2160_, v_a_2161_, v_a_2162_, v_a_2163_);
if (lean_obj_tag(v___x_2204_) == 0)
{
lean_object* v_a_2205_; lean_object* v___x_2206_; lean_object* v_visitedLevel_2207_; lean_object* v_visitedExpr_2208_; lean_object* v_levelParams_2209_; lean_object* v_nextLevelIdx_2210_; lean_object* v_levelArgs_2211_; lean_object* v_newLocalDecls_2212_; lean_object* v_newLocalDeclsForMVars_2213_; lean_object* v_newLetDecls_2214_; lean_object* v_nextExprIdx_2215_; lean_object* v_exprMVarArgs_2216_; lean_object* v_exprFVarArgs_2217_; lean_object* v_toProcess_2218_; lean_object* v___x_2220_; uint8_t v_isShared_2221_; uint8_t v_isSharedCheck_2257_; 
v_a_2205_ = lean_ctor_get(v___x_2204_, 0);
lean_inc(v_a_2205_);
lean_dec_ref(v___x_2204_);
v___x_2206_ = lean_st_ref_take(v_a_2159_);
v_visitedLevel_2207_ = lean_ctor_get(v___x_2206_, 0);
v_visitedExpr_2208_ = lean_ctor_get(v___x_2206_, 1);
v_levelParams_2209_ = lean_ctor_get(v___x_2206_, 2);
v_nextLevelIdx_2210_ = lean_ctor_get(v___x_2206_, 3);
v_levelArgs_2211_ = lean_ctor_get(v___x_2206_, 4);
v_newLocalDecls_2212_ = lean_ctor_get(v___x_2206_, 5);
v_newLocalDeclsForMVars_2213_ = lean_ctor_get(v___x_2206_, 6);
v_newLetDecls_2214_ = lean_ctor_get(v___x_2206_, 7);
v_nextExprIdx_2215_ = lean_ctor_get(v___x_2206_, 8);
v_exprMVarArgs_2216_ = lean_ctor_get(v___x_2206_, 9);
v_exprFVarArgs_2217_ = lean_ctor_get(v___x_2206_, 10);
v_toProcess_2218_ = lean_ctor_get(v___x_2206_, 11);
v_isSharedCheck_2257_ = !lean_is_exclusive(v___x_2206_);
if (v_isSharedCheck_2257_ == 0)
{
v___x_2220_ = v___x_2206_;
v_isShared_2221_ = v_isSharedCheck_2257_;
goto v_resetjp_2219_;
}
else
{
lean_inc(v_toProcess_2218_);
lean_inc(v_exprFVarArgs_2217_);
lean_inc(v_exprMVarArgs_2216_);
lean_inc(v_nextExprIdx_2215_);
lean_inc(v_newLetDecls_2214_);
lean_inc(v_newLocalDeclsForMVars_2213_);
lean_inc(v_newLocalDecls_2212_);
lean_inc(v_levelArgs_2211_);
lean_inc(v_nextLevelIdx_2210_);
lean_inc(v_levelParams_2209_);
lean_inc(v_visitedExpr_2208_);
lean_inc(v_visitedLevel_2207_);
lean_dec(v___x_2206_);
v___x_2220_ = lean_box(0);
v_isShared_2221_ = v_isSharedCheck_2257_;
goto v_resetjp_2219_;
}
v_resetjp_2219_:
{
lean_object* v___x_2222_; uint8_t v___x_2223_; lean_object* v___x_2225_; 
v___x_2222_ = lean_unsigned_to_nat(0u);
v___x_2223_ = 0;
lean_inc(v_a_2205_);
lean_inc(v_newFVarId_2176_);
if (v_isShared_2192_ == 0)
{
lean_ctor_set(v___x_2191_, 4, v_a_2205_);
lean_ctor_set(v___x_2191_, 3, v_a_2203_);
lean_ctor_set(v___x_2191_, 1, v_newFVarId_2176_);
lean_ctor_set(v___x_2191_, 0, v___x_2222_);
v___x_2225_ = v___x_2191_;
goto v_reusejp_2224_;
}
else
{
lean_object* v_reuseFailAlloc_2256_; 
v_reuseFailAlloc_2256_ = lean_alloc_ctor(1, 5, 2);
lean_ctor_set(v_reuseFailAlloc_2256_, 0, v___x_2222_);
lean_ctor_set(v_reuseFailAlloc_2256_, 1, v_newFVarId_2176_);
lean_ctor_set(v_reuseFailAlloc_2256_, 2, v_userName_2186_);
lean_ctor_set(v_reuseFailAlloc_2256_, 3, v_a_2203_);
lean_ctor_set(v_reuseFailAlloc_2256_, 4, v_a_2205_);
lean_ctor_set_uint8(v_reuseFailAlloc_2256_, sizeof(void*)*5, v_nondep_2189_);
v___x_2225_ = v_reuseFailAlloc_2256_;
goto v_reusejp_2224_;
}
v_reusejp_2224_:
{
lean_object* v___x_2226_; lean_object* v___x_2228_; 
lean_ctor_set_uint8(v___x_2225_, sizeof(void*)*5 + 1, v___x_2223_);
v___x_2226_ = lean_array_push(v_newLetDecls_2214_, v___x_2225_);
if (v_isShared_2221_ == 0)
{
lean_ctor_set(v___x_2220_, 7, v___x_2226_);
v___x_2228_ = v___x_2220_;
goto v_reusejp_2227_;
}
else
{
lean_object* v_reuseFailAlloc_2255_; 
v_reuseFailAlloc_2255_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_2255_, 0, v_visitedLevel_2207_);
lean_ctor_set(v_reuseFailAlloc_2255_, 1, v_visitedExpr_2208_);
lean_ctor_set(v_reuseFailAlloc_2255_, 2, v_levelParams_2209_);
lean_ctor_set(v_reuseFailAlloc_2255_, 3, v_nextLevelIdx_2210_);
lean_ctor_set(v_reuseFailAlloc_2255_, 4, v_levelArgs_2211_);
lean_ctor_set(v_reuseFailAlloc_2255_, 5, v_newLocalDecls_2212_);
lean_ctor_set(v_reuseFailAlloc_2255_, 6, v_newLocalDeclsForMVars_2213_);
lean_ctor_set(v_reuseFailAlloc_2255_, 7, v___x_2226_);
lean_ctor_set(v_reuseFailAlloc_2255_, 8, v_nextExprIdx_2215_);
lean_ctor_set(v_reuseFailAlloc_2255_, 9, v_exprMVarArgs_2216_);
lean_ctor_set(v_reuseFailAlloc_2255_, 10, v_exprFVarArgs_2217_);
lean_ctor_set(v_reuseFailAlloc_2255_, 11, v_toProcess_2218_);
v___x_2228_ = v_reuseFailAlloc_2255_;
goto v_reusejp_2227_;
}
v_reusejp_2227_:
{
lean_object* v___x_2229_; lean_object* v___x_2230_; lean_object* v_visitedLevel_2231_; lean_object* v_visitedExpr_2232_; lean_object* v_levelParams_2233_; lean_object* v_nextLevelIdx_2234_; lean_object* v_levelArgs_2235_; lean_object* v_newLocalDecls_2236_; lean_object* v_newLocalDeclsForMVars_2237_; lean_object* v_newLetDecls_2238_; lean_object* v_nextExprIdx_2239_; lean_object* v_exprMVarArgs_2240_; lean_object* v_exprFVarArgs_2241_; lean_object* v_toProcess_2242_; lean_object* v___x_2244_; uint8_t v_isShared_2245_; uint8_t v_isSharedCheck_2254_; 
v___x_2229_ = lean_st_ref_set(v_a_2159_, v___x_2228_);
v___x_2230_ = lean_st_ref_take(v_a_2159_);
v_visitedLevel_2231_ = lean_ctor_get(v___x_2230_, 0);
v_visitedExpr_2232_ = lean_ctor_get(v___x_2230_, 1);
v_levelParams_2233_ = lean_ctor_get(v___x_2230_, 2);
v_nextLevelIdx_2234_ = lean_ctor_get(v___x_2230_, 3);
v_levelArgs_2235_ = lean_ctor_get(v___x_2230_, 4);
v_newLocalDecls_2236_ = lean_ctor_get(v___x_2230_, 5);
v_newLocalDeclsForMVars_2237_ = lean_ctor_get(v___x_2230_, 6);
v_newLetDecls_2238_ = lean_ctor_get(v___x_2230_, 7);
v_nextExprIdx_2239_ = lean_ctor_get(v___x_2230_, 8);
v_exprMVarArgs_2240_ = lean_ctor_get(v___x_2230_, 9);
v_exprFVarArgs_2241_ = lean_ctor_get(v___x_2230_, 10);
v_toProcess_2242_ = lean_ctor_get(v___x_2230_, 11);
v_isSharedCheck_2254_ = !lean_is_exclusive(v___x_2230_);
if (v_isSharedCheck_2254_ == 0)
{
v___x_2244_ = v___x_2230_;
v_isShared_2245_ = v_isSharedCheck_2254_;
goto v_resetjp_2243_;
}
else
{
lean_inc(v_toProcess_2242_);
lean_inc(v_exprFVarArgs_2241_);
lean_inc(v_exprMVarArgs_2240_);
lean_inc(v_nextExprIdx_2239_);
lean_inc(v_newLetDecls_2238_);
lean_inc(v_newLocalDeclsForMVars_2237_);
lean_inc(v_newLocalDecls_2236_);
lean_inc(v_levelArgs_2235_);
lean_inc(v_nextLevelIdx_2234_);
lean_inc(v_levelParams_2233_);
lean_inc(v_visitedExpr_2232_);
lean_inc(v_visitedLevel_2231_);
lean_dec(v___x_2230_);
v___x_2244_ = lean_box(0);
v_isShared_2245_ = v_isSharedCheck_2254_;
goto v_resetjp_2243_;
}
v_resetjp_2243_:
{
size_t v_sz_2246_; size_t v___x_2247_; lean_object* v___x_2248_; lean_object* v___x_2250_; 
v_sz_2246_ = lean_array_size(v_newLocalDecls_2236_);
v___x_2247_ = ((size_t)0ULL);
v___x_2248_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Closure_process_spec__1(v_newFVarId_2176_, v_a_2205_, v_sz_2246_, v___x_2247_, v_newLocalDecls_2236_);
lean_dec(v_a_2205_);
if (v_isShared_2245_ == 0)
{
lean_ctor_set(v___x_2244_, 5, v___x_2248_);
v___x_2250_ = v___x_2244_;
goto v_reusejp_2249_;
}
else
{
lean_object* v_reuseFailAlloc_2253_; 
v_reuseFailAlloc_2253_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_2253_, 0, v_visitedLevel_2231_);
lean_ctor_set(v_reuseFailAlloc_2253_, 1, v_visitedExpr_2232_);
lean_ctor_set(v_reuseFailAlloc_2253_, 2, v_levelParams_2233_);
lean_ctor_set(v_reuseFailAlloc_2253_, 3, v_nextLevelIdx_2234_);
lean_ctor_set(v_reuseFailAlloc_2253_, 4, v_levelArgs_2235_);
lean_ctor_set(v_reuseFailAlloc_2253_, 5, v___x_2248_);
lean_ctor_set(v_reuseFailAlloc_2253_, 6, v_newLocalDeclsForMVars_2237_);
lean_ctor_set(v_reuseFailAlloc_2253_, 7, v_newLetDecls_2238_);
lean_ctor_set(v_reuseFailAlloc_2253_, 8, v_nextExprIdx_2239_);
lean_ctor_set(v_reuseFailAlloc_2253_, 9, v_exprMVarArgs_2240_);
lean_ctor_set(v_reuseFailAlloc_2253_, 10, v_exprFVarArgs_2241_);
lean_ctor_set(v_reuseFailAlloc_2253_, 11, v_toProcess_2242_);
v___x_2250_ = v_reuseFailAlloc_2253_;
goto v_reusejp_2249_;
}
v_reusejp_2249_:
{
lean_object* v___x_2251_; 
v___x_2251_ = lean_st_ref_set(v_a_2159_, v___x_2250_);
goto _start;
}
}
}
}
}
}
else
{
lean_object* v_a_2258_; lean_object* v___x_2260_; uint8_t v_isShared_2261_; uint8_t v_isSharedCheck_2265_; 
lean_dec(v_a_2203_);
lean_del_object(v___x_2191_);
lean_dec(v_userName_2186_);
lean_dec(v_newFVarId_2176_);
v_a_2258_ = lean_ctor_get(v___x_2204_, 0);
v_isSharedCheck_2265_ = !lean_is_exclusive(v___x_2204_);
if (v_isSharedCheck_2265_ == 0)
{
v___x_2260_ = v___x_2204_;
v_isShared_2261_ = v_isSharedCheck_2265_;
goto v_resetjp_2259_;
}
else
{
lean_inc(v_a_2258_);
lean_dec(v___x_2204_);
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
else
{
lean_object* v_a_2266_; lean_object* v___x_2268_; uint8_t v_isShared_2269_; uint8_t v_isSharedCheck_2273_; 
lean_del_object(v___x_2191_);
lean_dec_ref(v_value_2188_);
lean_dec(v_userName_2186_);
lean_dec(v_newFVarId_2176_);
v_a_2266_ = lean_ctor_get(v___x_2202_, 0);
v_isSharedCheck_2273_ = !lean_is_exclusive(v___x_2202_);
if (v_isSharedCheck_2273_ == 0)
{
v___x_2268_ = v___x_2202_;
v_isShared_2269_ = v_isSharedCheck_2273_;
goto v_resetjp_2267_;
}
else
{
lean_inc(v_a_2266_);
lean_dec(v___x_2202_);
v___x_2268_ = lean_box(0);
v_isShared_2269_ = v_isSharedCheck_2273_;
goto v_resetjp_2267_;
}
v_resetjp_2267_:
{
lean_object* v___x_2271_; 
if (v_isShared_2269_ == 0)
{
v___x_2271_ = v___x_2268_;
goto v_reusejp_2270_;
}
else
{
lean_object* v_reuseFailAlloc_2272_; 
v_reuseFailAlloc_2272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2272_, 0, v_a_2266_);
v___x_2271_ = v_reuseFailAlloc_2272_;
goto v_reusejp_2270_;
}
v_reusejp_2270_:
{
return v___x_2271_;
}
}
}
}
}
else
{
lean_dec(v_a_2194_);
lean_del_object(v___x_2191_);
lean_dec_ref(v_value_2188_);
goto v___jp_2195_;
}
v___jp_2195_:
{
uint8_t v___x_2196_; lean_object* v___x_2197_; 
v___x_2196_ = 0;
v___x_2197_ = l_Lean_Meta_Closure_pushLocalDecl(v_newFVarId_2176_, v_userName_2186_, v_type_2187_, v___x_2196_, v_a_2158_, v_a_2159_, v_a_2160_, v_a_2161_, v_a_2162_, v_a_2163_);
if (lean_obj_tag(v___x_2197_) == 0)
{
lean_object* v___x_2198_; lean_object* v___x_2199_; 
lean_dec_ref(v___x_2197_);
v___x_2198_ = l_Lean_mkFVar(v_fvarId_2175_);
v___x_2199_ = l_Lean_Meta_Closure_pushFVarArg___redArg(v___x_2198_, v_a_2159_);
if (lean_obj_tag(v___x_2199_) == 0)
{
lean_dec_ref(v___x_2199_);
goto _start;
}
else
{
return v___x_2199_;
}
}
else
{
lean_dec(v_fvarId_2175_);
return v___x_2197_;
}
}
}
else
{
lean_object* v_a_2274_; lean_object* v___x_2276_; uint8_t v_isShared_2277_; uint8_t v_isSharedCheck_2281_; 
lean_del_object(v___x_2191_);
lean_dec_ref(v_value_2188_);
lean_dec_ref(v_type_2187_);
lean_dec(v_userName_2186_);
lean_dec(v_newFVarId_2176_);
lean_dec(v_fvarId_2175_);
v_a_2274_ = lean_ctor_get(v___x_2193_, 0);
v_isSharedCheck_2281_ = !lean_is_exclusive(v___x_2193_);
if (v_isSharedCheck_2281_ == 0)
{
v___x_2276_ = v___x_2193_;
v_isShared_2277_ = v_isSharedCheck_2281_;
goto v_resetjp_2275_;
}
else
{
lean_inc(v_a_2274_);
lean_dec(v___x_2193_);
v___x_2276_ = lean_box(0);
v_isShared_2277_ = v_isSharedCheck_2281_;
goto v_resetjp_2275_;
}
v_resetjp_2275_:
{
lean_object* v___x_2279_; 
if (v_isShared_2277_ == 0)
{
v___x_2279_ = v___x_2276_;
goto v_reusejp_2278_;
}
else
{
lean_object* v_reuseFailAlloc_2280_; 
v_reuseFailAlloc_2280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2280_, 0, v_a_2274_);
v___x_2279_ = v_reuseFailAlloc_2280_;
goto v_reusejp_2278_;
}
v_reusejp_2278_:
{
return v___x_2279_;
}
}
}
}
}
}
else
{
lean_object* v_a_2285_; lean_object* v___x_2287_; uint8_t v_isShared_2288_; uint8_t v_isSharedCheck_2292_; 
lean_dec(v_newFVarId_2176_);
lean_dec(v_fvarId_2175_);
v_a_2285_ = lean_ctor_get(v___x_2177_, 0);
v_isSharedCheck_2292_ = !lean_is_exclusive(v___x_2177_);
if (v_isSharedCheck_2292_ == 0)
{
v___x_2287_ = v___x_2177_;
v_isShared_2288_ = v_isSharedCheck_2292_;
goto v_resetjp_2286_;
}
else
{
lean_inc(v_a_2285_);
lean_dec(v___x_2177_);
v___x_2287_ = lean_box(0);
v_isShared_2288_ = v_isSharedCheck_2292_;
goto v_resetjp_2286_;
}
v_resetjp_2286_:
{
lean_object* v___x_2290_; 
if (v_isShared_2288_ == 0)
{
v___x_2290_ = v___x_2287_;
goto v_reusejp_2289_;
}
else
{
lean_object* v_reuseFailAlloc_2291_; 
v_reuseFailAlloc_2291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2291_, 0, v_a_2285_);
v___x_2290_ = v_reuseFailAlloc_2291_;
goto v_reusejp_2289_;
}
v_reusejp_2289_:
{
return v___x_2290_;
}
}
}
}
}
}
else
{
lean_object* v_a_2294_; lean_object* v___x_2296_; uint8_t v_isShared_2297_; uint8_t v_isSharedCheck_2301_; 
v_a_2294_ = lean_ctor_get(v___x_2165_, 0);
v_isSharedCheck_2301_ = !lean_is_exclusive(v___x_2165_);
if (v_isSharedCheck_2301_ == 0)
{
v___x_2296_ = v___x_2165_;
v_isShared_2297_ = v_isSharedCheck_2301_;
goto v_resetjp_2295_;
}
else
{
lean_inc(v_a_2294_);
lean_dec(v___x_2165_);
v___x_2296_ = lean_box(0);
v_isShared_2297_ = v_isSharedCheck_2301_;
goto v_resetjp_2295_;
}
v_resetjp_2295_:
{
lean_object* v___x_2299_; 
if (v_isShared_2297_ == 0)
{
v___x_2299_ = v___x_2296_;
goto v_reusejp_2298_;
}
else
{
lean_object* v_reuseFailAlloc_2300_; 
v_reuseFailAlloc_2300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2300_, 0, v_a_2294_);
v___x_2299_ = v_reuseFailAlloc_2300_;
goto v_reusejp_2298_;
}
v_reusejp_2298_:
{
return v___x_2299_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_process___boxed(lean_object* v_a_2302_, lean_object* v_a_2303_, lean_object* v_a_2304_, lean_object* v_a_2305_, lean_object* v_a_2306_, lean_object* v_a_2307_, lean_object* v_a_2308_){
_start:
{
uint8_t v_a_boxed_2309_; lean_object* v_res_2310_; 
v_a_boxed_2309_ = lean_unbox(v_a_2302_);
v_res_2310_ = l_Lean_Meta_Closure_process(v_a_boxed_2309_, v_a_2303_, v_a_2304_, v_a_2305_, v_a_2306_, v_a_2307_);
lean_dec(v_a_2307_);
lean_dec_ref(v_a_2306_);
lean_dec(v_a_2305_);
lean_dec_ref(v_a_2304_);
lean_dec(v_a_2303_);
return v_res_2310_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Closure_process_spec__0(lean_object* v_00_u03b2_2311_, lean_object* v_k_2312_, lean_object* v_t_2313_){
_start:
{
uint8_t v___x_2314_; 
v___x_2314_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Closure_process_spec__0___redArg(v_k_2312_, v_t_2313_);
return v___x_2314_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Closure_process_spec__0___boxed(lean_object* v_00_u03b2_2315_, lean_object* v_k_2316_, lean_object* v_t_2317_){
_start:
{
uint8_t v_res_2318_; lean_object* v_r_2319_; 
v_res_2318_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Closure_process_spec__0(v_00_u03b2_2315_, v_k_2316_, v_t_2317_);
lean_dec(v_t_2317_);
lean_dec(v_k_2316_);
v_r_2319_ = lean_box(v_res_2318_);
return v_r_2319_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkBinding___lam__0(lean_object* v_decls_2320_, lean_object* v_xs_2321_, uint8_t v_isLambda_2322_, lean_object* v_i_2323_, lean_object* v_x_2324_, lean_object* v_b_2325_){
_start:
{
lean_object* v_decl_2326_; 
v_decl_2326_ = lean_array_fget_borrowed(v_decls_2320_, v_i_2323_);
if (lean_obj_tag(v_decl_2326_) == 0)
{
lean_object* v_userName_2327_; lean_object* v_type_2328_; uint8_t v_bi_2329_; lean_object* v_ty_2330_; 
v_userName_2327_ = lean_ctor_get(v_decl_2326_, 2);
v_type_2328_ = lean_ctor_get(v_decl_2326_, 3);
v_bi_2329_ = lean_ctor_get_uint8(v_decl_2326_, sizeof(void*)*4);
v_ty_2330_ = lean_expr_abstract_range(v_type_2328_, v_i_2323_, v_xs_2321_);
if (v_isLambda_2322_ == 0)
{
lean_object* v___x_2331_; 
lean_inc(v_userName_2327_);
v___x_2331_ = l_Lean_mkForall(v_userName_2327_, v_bi_2329_, v_ty_2330_, v_b_2325_);
return v___x_2331_;
}
else
{
lean_object* v___x_2332_; 
lean_inc(v_userName_2327_);
v___x_2332_ = l_Lean_mkLambda(v_userName_2327_, v_bi_2329_, v_ty_2330_, v_b_2325_);
return v___x_2332_;
}
}
else
{
lean_object* v_userName_2333_; lean_object* v_type_2334_; lean_object* v_value_2335_; uint8_t v_nondep_2336_; lean_object* v___x_2337_; uint8_t v___x_2338_; 
v_userName_2333_ = lean_ctor_get(v_decl_2326_, 2);
v_type_2334_ = lean_ctor_get(v_decl_2326_, 3);
v_value_2335_ = lean_ctor_get(v_decl_2326_, 4);
v_nondep_2336_ = lean_ctor_get_uint8(v_decl_2326_, sizeof(void*)*5);
v___x_2337_ = lean_unsigned_to_nat(0u);
v___x_2338_ = lean_expr_has_loose_bvar(v_b_2325_, v___x_2337_);
if (v___x_2338_ == 0)
{
lean_object* v___x_2339_; lean_object* v___x_2340_; 
v___x_2339_ = lean_unsigned_to_nat(1u);
v___x_2340_ = lean_expr_lower_loose_bvars(v_b_2325_, v___x_2339_, v___x_2339_);
lean_dec_ref(v_b_2325_);
return v___x_2340_;
}
else
{
lean_object* v_ty_2341_; lean_object* v_val_2342_; lean_object* v___x_2343_; 
v_ty_2341_ = lean_expr_abstract_range(v_type_2334_, v_i_2323_, v_xs_2321_);
v_val_2342_ = lean_expr_abstract_range(v_value_2335_, v_i_2323_, v_xs_2321_);
lean_inc(v_userName_2333_);
v___x_2343_ = l_Lean_Expr_letE___override(v_userName_2333_, v_ty_2341_, v_val_2342_, v_b_2325_, v_nondep_2336_);
return v___x_2343_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkBinding___lam__0___boxed(lean_object* v_decls_2344_, lean_object* v_xs_2345_, lean_object* v_isLambda_2346_, lean_object* v_i_2347_, lean_object* v_x_2348_, lean_object* v_b_2349_){
_start:
{
uint8_t v_isLambda_boxed_2350_; lean_object* v_res_2351_; 
v_isLambda_boxed_2350_ = lean_unbox(v_isLambda_2346_);
v_res_2351_ = l_Lean_Meta_Closure_mkBinding___lam__0(v_decls_2344_, v_xs_2345_, v_isLambda_boxed_2350_, v_i_2347_, v_x_2348_, v_b_2349_);
lean_dec(v_i_2347_);
lean_dec_ref(v_xs_2345_);
lean_dec_ref(v_decls_2344_);
return v_res_2351_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkBinding(uint8_t v_isLambda_2372_, lean_object* v_decls_2373_, lean_object* v_b_2374_){
_start:
{
lean_object* v___f_2375_; lean_object* v___x_2376_; size_t v_sz_2377_; size_t v___x_2378_; lean_object* v_xs_2379_; lean_object* v___x_2380_; lean_object* v___f_2381_; lean_object* v_b_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; 
v___f_2375_ = ((lean_object*)(l_Lean_Meta_Closure_mkBinding___closed__0));
v___x_2376_ = ((lean_object*)(l_Lean_Meta_Closure_mkBinding___closed__10));
v_sz_2377_ = lean_array_size(v_decls_2373_);
v___x_2378_ = ((size_t)0ULL);
lean_inc_ref_n(v_decls_2373_, 2);
v_xs_2379_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2376_, v___f_2375_, v_sz_2377_, v___x_2378_, v_decls_2373_);
v___x_2380_ = lean_box(v_isLambda_2372_);
lean_inc(v_xs_2379_);
v___f_2381_ = lean_alloc_closure((void*)(l_Lean_Meta_Closure_mkBinding___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2381_, 0, v_decls_2373_);
lean_closure_set(v___f_2381_, 1, v_xs_2379_);
lean_closure_set(v___f_2381_, 2, v___x_2380_);
v_b_2382_ = lean_expr_abstract(v_b_2374_, v_xs_2379_);
lean_dec(v_xs_2379_);
v___x_2383_ = lean_array_get_size(v_decls_2373_);
lean_dec_ref(v_decls_2373_);
v___x_2384_ = l_Nat_foldRev___redArg(v___x_2383_, v___f_2381_, v_b_2382_);
return v___x_2384_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkBinding___boxed(lean_object* v_isLambda_2385_, lean_object* v_decls_2386_, lean_object* v_b_2387_){
_start:
{
uint8_t v_isLambda_boxed_2388_; lean_object* v_res_2389_; 
v_isLambda_boxed_2388_ = lean_unbox(v_isLambda_2385_);
v_res_2389_ = l_Lean_Meta_Closure_mkBinding(v_isLambda_boxed_2388_, v_decls_2386_, v_b_2387_);
lean_dec_ref(v_b_2387_);
return v_res_2389_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Closure_mkLambda_spec__0(size_t v_sz_2390_, size_t v_i_2391_, lean_object* v_bs_2392_){
_start:
{
uint8_t v___x_2393_; 
v___x_2393_ = lean_usize_dec_lt(v_i_2391_, v_sz_2390_);
if (v___x_2393_ == 0)
{
return v_bs_2392_;
}
else
{
lean_object* v_v_2394_; lean_object* v___x_2395_; lean_object* v_bs_x27_2396_; lean_object* v___x_2397_; size_t v___x_2398_; size_t v___x_2399_; lean_object* v___x_2400_; 
v_v_2394_ = lean_array_uget(v_bs_2392_, v_i_2391_);
v___x_2395_ = lean_unsigned_to_nat(0u);
v_bs_x27_2396_ = lean_array_uset(v_bs_2392_, v_i_2391_, v___x_2395_);
v___x_2397_ = l_Lean_LocalDecl_toExpr(v_v_2394_);
v___x_2398_ = ((size_t)1ULL);
v___x_2399_ = lean_usize_add(v_i_2391_, v___x_2398_);
v___x_2400_ = lean_array_uset(v_bs_x27_2396_, v_i_2391_, v___x_2397_);
v_i_2391_ = v___x_2399_;
v_bs_2392_ = v___x_2400_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Closure_mkLambda_spec__0___boxed(lean_object* v_sz_2402_, lean_object* v_i_2403_, lean_object* v_bs_2404_){
_start:
{
size_t v_sz_boxed_2405_; size_t v_i_boxed_2406_; lean_object* v_res_2407_; 
v_sz_boxed_2405_ = lean_unbox_usize(v_sz_2402_);
lean_dec(v_sz_2402_);
v_i_boxed_2406_ = lean_unbox_usize(v_i_2403_);
lean_dec(v_i_2403_);
v_res_2407_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Closure_mkLambda_spec__0(v_sz_boxed_2405_, v_i_boxed_2406_, v_bs_2404_);
return v_res_2407_;
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_Meta_Closure_mkLambda_spec__1_spec__1(lean_object* v_decls_2408_, lean_object* v_xs_2409_, lean_object* v_x_2410_, lean_object* v_x_2411_){
_start:
{
lean_object* v_zero_2412_; uint8_t v_isZero_2413_; 
v_zero_2412_ = lean_unsigned_to_nat(0u);
v_isZero_2413_ = lean_nat_dec_eq(v_x_2410_, v_zero_2412_);
if (v_isZero_2413_ == 1)
{
lean_dec(v_x_2410_);
return v_x_2411_;
}
else
{
lean_object* v_one_2414_; lean_object* v_n_2415_; lean_object* v_decl_2416_; 
v_one_2414_ = lean_unsigned_to_nat(1u);
v_n_2415_ = lean_nat_sub(v_x_2410_, v_one_2414_);
lean_dec(v_x_2410_);
v_decl_2416_ = lean_array_fget_borrowed(v_decls_2408_, v_n_2415_);
if (lean_obj_tag(v_decl_2416_) == 0)
{
lean_object* v_userName_2417_; lean_object* v_type_2418_; uint8_t v_bi_2419_; lean_object* v_ty_2420_; lean_object* v___x_2421_; 
v_userName_2417_ = lean_ctor_get(v_decl_2416_, 2);
v_type_2418_ = lean_ctor_get(v_decl_2416_, 3);
v_bi_2419_ = lean_ctor_get_uint8(v_decl_2416_, sizeof(void*)*4);
v_ty_2420_ = lean_expr_abstract_range(v_type_2418_, v_n_2415_, v_xs_2409_);
lean_inc(v_userName_2417_);
v___x_2421_ = l_Lean_mkLambda(v_userName_2417_, v_bi_2419_, v_ty_2420_, v_x_2411_);
v_x_2410_ = v_n_2415_;
v_x_2411_ = v___x_2421_;
goto _start;
}
else
{
lean_object* v_userName_2423_; lean_object* v_type_2424_; lean_object* v_value_2425_; uint8_t v_nondep_2426_; uint8_t v___x_2427_; 
v_userName_2423_ = lean_ctor_get(v_decl_2416_, 2);
v_type_2424_ = lean_ctor_get(v_decl_2416_, 3);
v_value_2425_ = lean_ctor_get(v_decl_2416_, 4);
v_nondep_2426_ = lean_ctor_get_uint8(v_decl_2416_, sizeof(void*)*5);
v___x_2427_ = lean_expr_has_loose_bvar(v_x_2411_, v_zero_2412_);
if (v___x_2427_ == 0)
{
lean_object* v___x_2428_; 
v___x_2428_ = lean_expr_lower_loose_bvars(v_x_2411_, v_one_2414_, v_one_2414_);
lean_dec_ref(v_x_2411_);
v_x_2410_ = v_n_2415_;
v_x_2411_ = v___x_2428_;
goto _start;
}
else
{
lean_object* v_ty_2430_; lean_object* v_val_2431_; lean_object* v___x_2432_; 
v_ty_2430_ = lean_expr_abstract_range(v_type_2424_, v_n_2415_, v_xs_2409_);
v_val_2431_ = lean_expr_abstract_range(v_value_2425_, v_n_2415_, v_xs_2409_);
lean_inc(v_userName_2423_);
v___x_2432_ = l_Lean_Expr_letE___override(v_userName_2423_, v_ty_2430_, v_val_2431_, v_x_2411_, v_nondep_2426_);
v_x_2410_ = v_n_2415_;
v_x_2411_ = v___x_2432_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_Meta_Closure_mkLambda_spec__1_spec__1___boxed(lean_object* v_decls_2434_, lean_object* v_xs_2435_, lean_object* v_x_2436_, lean_object* v_x_2437_){
_start:
{
lean_object* v_res_2438_; 
v_res_2438_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_Meta_Closure_mkLambda_spec__1_spec__1(v_decls_2434_, v_xs_2435_, v_x_2436_, v_x_2437_);
lean_dec_ref(v_xs_2435_);
lean_dec_ref(v_decls_2434_);
return v_res_2438_;
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Lean_Meta_Closure_mkLambda_spec__1(lean_object* v_decls_2439_, lean_object* v_xs_2440_, lean_object* v_x_2441_, lean_object* v_x_2442_){
_start:
{
lean_object* v_zero_2443_; uint8_t v_isZero_2444_; 
v_zero_2443_ = lean_unsigned_to_nat(0u);
v_isZero_2444_ = lean_nat_dec_eq(v_x_2441_, v_zero_2443_);
if (v_isZero_2444_ == 1)
{
return v_x_2442_;
}
else
{
lean_object* v_one_2445_; lean_object* v_n_2446_; lean_object* v_decl_2447_; 
v_one_2445_ = lean_unsigned_to_nat(1u);
v_n_2446_ = lean_nat_sub(v_x_2441_, v_one_2445_);
v_decl_2447_ = lean_array_fget_borrowed(v_decls_2439_, v_n_2446_);
if (lean_obj_tag(v_decl_2447_) == 0)
{
lean_object* v_userName_2448_; lean_object* v_type_2449_; uint8_t v_bi_2450_; lean_object* v_ty_2451_; lean_object* v___x_2452_; lean_object* v___x_2453_; 
v_userName_2448_ = lean_ctor_get(v_decl_2447_, 2);
v_type_2449_ = lean_ctor_get(v_decl_2447_, 3);
v_bi_2450_ = lean_ctor_get_uint8(v_decl_2447_, sizeof(void*)*4);
v_ty_2451_ = lean_expr_abstract_range(v_type_2449_, v_n_2446_, v_xs_2440_);
lean_inc(v_userName_2448_);
v___x_2452_ = l_Lean_mkLambda(v_userName_2448_, v_bi_2450_, v_ty_2451_, v_x_2442_);
v___x_2453_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_Meta_Closure_mkLambda_spec__1_spec__1(v_decls_2439_, v_xs_2440_, v_n_2446_, v___x_2452_);
return v___x_2453_;
}
else
{
lean_object* v_userName_2454_; lean_object* v_type_2455_; lean_object* v_value_2456_; uint8_t v_nondep_2457_; uint8_t v___x_2458_; 
v_userName_2454_ = lean_ctor_get(v_decl_2447_, 2);
v_type_2455_ = lean_ctor_get(v_decl_2447_, 3);
v_value_2456_ = lean_ctor_get(v_decl_2447_, 4);
v_nondep_2457_ = lean_ctor_get_uint8(v_decl_2447_, sizeof(void*)*5);
v___x_2458_ = lean_expr_has_loose_bvar(v_x_2442_, v_zero_2443_);
if (v___x_2458_ == 0)
{
lean_object* v___x_2459_; lean_object* v___x_2460_; 
v___x_2459_ = lean_expr_lower_loose_bvars(v_x_2442_, v_one_2445_, v_one_2445_);
lean_dec_ref(v_x_2442_);
v___x_2460_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_Meta_Closure_mkLambda_spec__1_spec__1(v_decls_2439_, v_xs_2440_, v_n_2446_, v___x_2459_);
return v___x_2460_;
}
else
{
lean_object* v_ty_2461_; lean_object* v_val_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; 
v_ty_2461_ = lean_expr_abstract_range(v_type_2455_, v_n_2446_, v_xs_2440_);
v_val_2462_ = lean_expr_abstract_range(v_value_2456_, v_n_2446_, v_xs_2440_);
lean_inc(v_userName_2454_);
v___x_2463_ = l_Lean_Expr_letE___override(v_userName_2454_, v_ty_2461_, v_val_2462_, v_x_2442_, v_nondep_2457_);
v___x_2464_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_Meta_Closure_mkLambda_spec__1_spec__1(v_decls_2439_, v_xs_2440_, v_n_2446_, v___x_2463_);
return v___x_2464_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Lean_Meta_Closure_mkLambda_spec__1___boxed(lean_object* v_decls_2465_, lean_object* v_xs_2466_, lean_object* v_x_2467_, lean_object* v_x_2468_){
_start:
{
lean_object* v_res_2469_; 
v_res_2469_ = l_Nat_foldRev___at___00Lean_Meta_Closure_mkLambda_spec__1(v_decls_2465_, v_xs_2466_, v_x_2467_, v_x_2468_);
lean_dec(v_x_2467_);
lean_dec_ref(v_xs_2466_);
lean_dec_ref(v_decls_2465_);
return v_res_2469_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkLambda(lean_object* v_decls_2470_, lean_object* v_b_2471_){
_start:
{
size_t v_sz_2472_; size_t v___x_2473_; lean_object* v_xs_2474_; lean_object* v_b_2475_; lean_object* v___x_2476_; lean_object* v___x_2477_; 
v_sz_2472_ = lean_array_size(v_decls_2470_);
v___x_2473_ = ((size_t)0ULL);
lean_inc_ref(v_decls_2470_);
v_xs_2474_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Closure_mkLambda_spec__0(v_sz_2472_, v___x_2473_, v_decls_2470_);
v_b_2475_ = lean_expr_abstract(v_b_2471_, v_xs_2474_);
v___x_2476_ = lean_array_get_size(v_decls_2470_);
v___x_2477_ = l_Nat_foldRev___at___00Lean_Meta_Closure_mkLambda_spec__1(v_decls_2470_, v_xs_2474_, v___x_2476_, v_b_2475_);
lean_dec_ref(v_xs_2474_);
lean_dec_ref(v_decls_2470_);
return v___x_2477_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkLambda___boxed(lean_object* v_decls_2478_, lean_object* v_b_2479_){
_start:
{
lean_object* v_res_2480_; 
v_res_2480_ = l_Lean_Meta_Closure_mkLambda(v_decls_2478_, v_b_2479_);
lean_dec_ref(v_b_2479_);
return v_res_2480_;
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_Meta_Closure_mkForall_spec__0_spec__0(lean_object* v_decls_2481_, lean_object* v_xs_2482_, lean_object* v_x_2483_, lean_object* v_x_2484_){
_start:
{
lean_object* v_zero_2485_; uint8_t v_isZero_2486_; 
v_zero_2485_ = lean_unsigned_to_nat(0u);
v_isZero_2486_ = lean_nat_dec_eq(v_x_2483_, v_zero_2485_);
if (v_isZero_2486_ == 1)
{
lean_dec(v_x_2483_);
return v_x_2484_;
}
else
{
lean_object* v_one_2487_; lean_object* v_n_2488_; lean_object* v_decl_2489_; 
v_one_2487_ = lean_unsigned_to_nat(1u);
v_n_2488_ = lean_nat_sub(v_x_2483_, v_one_2487_);
lean_dec(v_x_2483_);
v_decl_2489_ = lean_array_fget_borrowed(v_decls_2481_, v_n_2488_);
if (lean_obj_tag(v_decl_2489_) == 0)
{
lean_object* v_userName_2490_; lean_object* v_type_2491_; uint8_t v_bi_2492_; lean_object* v_ty_2493_; lean_object* v___x_2494_; 
v_userName_2490_ = lean_ctor_get(v_decl_2489_, 2);
v_type_2491_ = lean_ctor_get(v_decl_2489_, 3);
v_bi_2492_ = lean_ctor_get_uint8(v_decl_2489_, sizeof(void*)*4);
v_ty_2493_ = lean_expr_abstract_range(v_type_2491_, v_n_2488_, v_xs_2482_);
lean_inc(v_userName_2490_);
v___x_2494_ = l_Lean_mkForall(v_userName_2490_, v_bi_2492_, v_ty_2493_, v_x_2484_);
v_x_2483_ = v_n_2488_;
v_x_2484_ = v___x_2494_;
goto _start;
}
else
{
lean_object* v_userName_2496_; lean_object* v_type_2497_; lean_object* v_value_2498_; uint8_t v_nondep_2499_; uint8_t v___x_2500_; 
v_userName_2496_ = lean_ctor_get(v_decl_2489_, 2);
v_type_2497_ = lean_ctor_get(v_decl_2489_, 3);
v_value_2498_ = lean_ctor_get(v_decl_2489_, 4);
v_nondep_2499_ = lean_ctor_get_uint8(v_decl_2489_, sizeof(void*)*5);
v___x_2500_ = lean_expr_has_loose_bvar(v_x_2484_, v_zero_2485_);
if (v___x_2500_ == 0)
{
lean_object* v___x_2501_; 
v___x_2501_ = lean_expr_lower_loose_bvars(v_x_2484_, v_one_2487_, v_one_2487_);
lean_dec_ref(v_x_2484_);
v_x_2483_ = v_n_2488_;
v_x_2484_ = v___x_2501_;
goto _start;
}
else
{
lean_object* v_ty_2503_; lean_object* v_val_2504_; lean_object* v___x_2505_; 
v_ty_2503_ = lean_expr_abstract_range(v_type_2497_, v_n_2488_, v_xs_2482_);
v_val_2504_ = lean_expr_abstract_range(v_value_2498_, v_n_2488_, v_xs_2482_);
lean_inc(v_userName_2496_);
v___x_2505_ = l_Lean_Expr_letE___override(v_userName_2496_, v_ty_2503_, v_val_2504_, v_x_2484_, v_nondep_2499_);
v_x_2483_ = v_n_2488_;
v_x_2484_ = v___x_2505_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_Meta_Closure_mkForall_spec__0_spec__0___boxed(lean_object* v_decls_2507_, lean_object* v_xs_2508_, lean_object* v_x_2509_, lean_object* v_x_2510_){
_start:
{
lean_object* v_res_2511_; 
v_res_2511_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_Meta_Closure_mkForall_spec__0_spec__0(v_decls_2507_, v_xs_2508_, v_x_2509_, v_x_2510_);
lean_dec_ref(v_xs_2508_);
lean_dec_ref(v_decls_2507_);
return v_res_2511_;
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Lean_Meta_Closure_mkForall_spec__0(lean_object* v_decls_2512_, lean_object* v_xs_2513_, lean_object* v_x_2514_, lean_object* v_x_2515_){
_start:
{
lean_object* v_zero_2516_; uint8_t v_isZero_2517_; 
v_zero_2516_ = lean_unsigned_to_nat(0u);
v_isZero_2517_ = lean_nat_dec_eq(v_x_2514_, v_zero_2516_);
if (v_isZero_2517_ == 1)
{
return v_x_2515_;
}
else
{
lean_object* v_one_2518_; lean_object* v_n_2519_; lean_object* v_decl_2520_; 
v_one_2518_ = lean_unsigned_to_nat(1u);
v_n_2519_ = lean_nat_sub(v_x_2514_, v_one_2518_);
v_decl_2520_ = lean_array_fget_borrowed(v_decls_2512_, v_n_2519_);
if (lean_obj_tag(v_decl_2520_) == 0)
{
lean_object* v_userName_2521_; lean_object* v_type_2522_; uint8_t v_bi_2523_; lean_object* v_ty_2524_; lean_object* v___x_2525_; lean_object* v___x_2526_; 
v_userName_2521_ = lean_ctor_get(v_decl_2520_, 2);
v_type_2522_ = lean_ctor_get(v_decl_2520_, 3);
v_bi_2523_ = lean_ctor_get_uint8(v_decl_2520_, sizeof(void*)*4);
v_ty_2524_ = lean_expr_abstract_range(v_type_2522_, v_n_2519_, v_xs_2513_);
lean_inc(v_userName_2521_);
v___x_2525_ = l_Lean_mkForall(v_userName_2521_, v_bi_2523_, v_ty_2524_, v_x_2515_);
v___x_2526_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_Meta_Closure_mkForall_spec__0_spec__0(v_decls_2512_, v_xs_2513_, v_n_2519_, v___x_2525_);
return v___x_2526_;
}
else
{
lean_object* v_userName_2527_; lean_object* v_type_2528_; lean_object* v_value_2529_; uint8_t v_nondep_2530_; uint8_t v___x_2531_; 
v_userName_2527_ = lean_ctor_get(v_decl_2520_, 2);
v_type_2528_ = lean_ctor_get(v_decl_2520_, 3);
v_value_2529_ = lean_ctor_get(v_decl_2520_, 4);
v_nondep_2530_ = lean_ctor_get_uint8(v_decl_2520_, sizeof(void*)*5);
v___x_2531_ = lean_expr_has_loose_bvar(v_x_2515_, v_zero_2516_);
if (v___x_2531_ == 0)
{
lean_object* v___x_2532_; lean_object* v___x_2533_; 
v___x_2532_ = lean_expr_lower_loose_bvars(v_x_2515_, v_one_2518_, v_one_2518_);
lean_dec_ref(v_x_2515_);
v___x_2533_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_Meta_Closure_mkForall_spec__0_spec__0(v_decls_2512_, v_xs_2513_, v_n_2519_, v___x_2532_);
return v___x_2533_;
}
else
{
lean_object* v_ty_2534_; lean_object* v_val_2535_; lean_object* v___x_2536_; lean_object* v___x_2537_; 
v_ty_2534_ = lean_expr_abstract_range(v_type_2528_, v_n_2519_, v_xs_2513_);
v_val_2535_ = lean_expr_abstract_range(v_value_2529_, v_n_2519_, v_xs_2513_);
lean_inc(v_userName_2527_);
v___x_2536_ = l_Lean_Expr_letE___override(v_userName_2527_, v_ty_2534_, v_val_2535_, v_x_2515_, v_nondep_2530_);
v___x_2537_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_Meta_Closure_mkForall_spec__0_spec__0(v_decls_2512_, v_xs_2513_, v_n_2519_, v___x_2536_);
return v___x_2537_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Lean_Meta_Closure_mkForall_spec__0___boxed(lean_object* v_decls_2538_, lean_object* v_xs_2539_, lean_object* v_x_2540_, lean_object* v_x_2541_){
_start:
{
lean_object* v_res_2542_; 
v_res_2542_ = l_Nat_foldRev___at___00Lean_Meta_Closure_mkForall_spec__0(v_decls_2538_, v_xs_2539_, v_x_2540_, v_x_2541_);
lean_dec(v_x_2540_);
lean_dec_ref(v_xs_2539_);
lean_dec_ref(v_decls_2538_);
return v_res_2542_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkForall(lean_object* v_decls_2543_, lean_object* v_b_2544_){
_start:
{
size_t v_sz_2545_; size_t v___x_2546_; lean_object* v_xs_2547_; lean_object* v_b_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; 
v_sz_2545_ = lean_array_size(v_decls_2543_);
v___x_2546_ = ((size_t)0ULL);
lean_inc_ref(v_decls_2543_);
v_xs_2547_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Closure_mkLambda_spec__0(v_sz_2545_, v___x_2546_, v_decls_2543_);
v_b_2548_ = lean_expr_abstract(v_b_2544_, v_xs_2547_);
v___x_2549_ = lean_array_get_size(v_decls_2543_);
v___x_2550_ = l_Nat_foldRev___at___00Lean_Meta_Closure_mkForall_spec__0(v_decls_2543_, v_xs_2547_, v___x_2549_, v_b_2548_);
lean_dec_ref(v_xs_2547_);
lean_dec_ref(v_decls_2543_);
return v___x_2550_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkForall___boxed(lean_object* v_decls_2551_, lean_object* v_b_2552_){
_start:
{
lean_object* v_res_2553_; 
v_res_2553_ = l_Lean_Meta_Closure_mkForall(v_decls_2551_, v_b_2552_);
lean_dec_ref(v_b_2552_);
return v_res_2553_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkValueTypeClosureAux___lam__0(lean_object* v_a_2554_, lean_object* v_zetaDeltaFVarIds_2555_, lean_object* v_a_x3f_2556_){
_start:
{
lean_object* v___x_2558_; lean_object* v_mctx_2559_; lean_object* v_cache_2560_; lean_object* v_postponed_2561_; lean_object* v_diag_2562_; lean_object* v___x_2564_; uint8_t v_isShared_2565_; uint8_t v_isSharedCheck_2572_; 
v___x_2558_ = lean_st_ref_take(v_a_2554_);
v_mctx_2559_ = lean_ctor_get(v___x_2558_, 0);
v_cache_2560_ = lean_ctor_get(v___x_2558_, 1);
v_postponed_2561_ = lean_ctor_get(v___x_2558_, 3);
v_diag_2562_ = lean_ctor_get(v___x_2558_, 4);
v_isSharedCheck_2572_ = !lean_is_exclusive(v___x_2558_);
if (v_isSharedCheck_2572_ == 0)
{
lean_object* v_unused_2573_; 
v_unused_2573_ = lean_ctor_get(v___x_2558_, 2);
lean_dec(v_unused_2573_);
v___x_2564_ = v___x_2558_;
v_isShared_2565_ = v_isSharedCheck_2572_;
goto v_resetjp_2563_;
}
else
{
lean_inc(v_diag_2562_);
lean_inc(v_postponed_2561_);
lean_inc(v_cache_2560_);
lean_inc(v_mctx_2559_);
lean_dec(v___x_2558_);
v___x_2564_ = lean_box(0);
v_isShared_2565_ = v_isSharedCheck_2572_;
goto v_resetjp_2563_;
}
v_resetjp_2563_:
{
lean_object* v___x_2567_; 
if (v_isShared_2565_ == 0)
{
lean_ctor_set(v___x_2564_, 2, v_zetaDeltaFVarIds_2555_);
v___x_2567_ = v___x_2564_;
goto v_reusejp_2566_;
}
else
{
lean_object* v_reuseFailAlloc_2571_; 
v_reuseFailAlloc_2571_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2571_, 0, v_mctx_2559_);
lean_ctor_set(v_reuseFailAlloc_2571_, 1, v_cache_2560_);
lean_ctor_set(v_reuseFailAlloc_2571_, 2, v_zetaDeltaFVarIds_2555_);
lean_ctor_set(v_reuseFailAlloc_2571_, 3, v_postponed_2561_);
lean_ctor_set(v_reuseFailAlloc_2571_, 4, v_diag_2562_);
v___x_2567_ = v_reuseFailAlloc_2571_;
goto v_reusejp_2566_;
}
v_reusejp_2566_:
{
lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; 
v___x_2568_ = lean_st_ref_set(v_a_2554_, v___x_2567_);
v___x_2569_ = lean_box(0);
v___x_2570_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2570_, 0, v___x_2569_);
return v___x_2570_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkValueTypeClosureAux___lam__0___boxed(lean_object* v_a_2574_, lean_object* v_zetaDeltaFVarIds_2575_, lean_object* v_a_x3f_2576_, lean_object* v___y_2577_){
_start:
{
lean_object* v_res_2578_; 
v_res_2578_ = l_Lean_Meta_Closure_mkValueTypeClosureAux___lam__0(v_a_2574_, v_zetaDeltaFVarIds_2575_, v_a_x3f_2576_);
lean_dec(v_a_x3f_2576_);
lean_dec(v_a_2574_);
return v_res_2578_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkValueTypeClosureAux___lam__1(lean_object* v_a_2579_, lean_object* v_cache_2580_, lean_object* v_a_x3f_2581_){
_start:
{
lean_object* v___x_2583_; lean_object* v_mctx_2584_; lean_object* v_zetaDeltaFVarIds_2585_; lean_object* v_postponed_2586_; lean_object* v_diag_2587_; lean_object* v___x_2589_; uint8_t v_isShared_2590_; uint8_t v_isSharedCheck_2597_; 
v___x_2583_ = lean_st_ref_take(v_a_2579_);
v_mctx_2584_ = lean_ctor_get(v___x_2583_, 0);
v_zetaDeltaFVarIds_2585_ = lean_ctor_get(v___x_2583_, 2);
v_postponed_2586_ = lean_ctor_get(v___x_2583_, 3);
v_diag_2587_ = lean_ctor_get(v___x_2583_, 4);
v_isSharedCheck_2597_ = !lean_is_exclusive(v___x_2583_);
if (v_isSharedCheck_2597_ == 0)
{
lean_object* v_unused_2598_; 
v_unused_2598_ = lean_ctor_get(v___x_2583_, 1);
lean_dec(v_unused_2598_);
v___x_2589_ = v___x_2583_;
v_isShared_2590_ = v_isSharedCheck_2597_;
goto v_resetjp_2588_;
}
else
{
lean_inc(v_diag_2587_);
lean_inc(v_postponed_2586_);
lean_inc(v_zetaDeltaFVarIds_2585_);
lean_inc(v_mctx_2584_);
lean_dec(v___x_2583_);
v___x_2589_ = lean_box(0);
v_isShared_2590_ = v_isSharedCheck_2597_;
goto v_resetjp_2588_;
}
v_resetjp_2588_:
{
lean_object* v___x_2592_; 
if (v_isShared_2590_ == 0)
{
lean_ctor_set(v___x_2589_, 1, v_cache_2580_);
v___x_2592_ = v___x_2589_;
goto v_reusejp_2591_;
}
else
{
lean_object* v_reuseFailAlloc_2596_; 
v_reuseFailAlloc_2596_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2596_, 0, v_mctx_2584_);
lean_ctor_set(v_reuseFailAlloc_2596_, 1, v_cache_2580_);
lean_ctor_set(v_reuseFailAlloc_2596_, 2, v_zetaDeltaFVarIds_2585_);
lean_ctor_set(v_reuseFailAlloc_2596_, 3, v_postponed_2586_);
lean_ctor_set(v_reuseFailAlloc_2596_, 4, v_diag_2587_);
v___x_2592_ = v_reuseFailAlloc_2596_;
goto v_reusejp_2591_;
}
v_reusejp_2591_:
{
lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; 
v___x_2593_ = lean_st_ref_set(v_a_2579_, v___x_2592_);
v___x_2594_ = lean_box(0);
v___x_2595_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2595_, 0, v___x_2594_);
return v___x_2595_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkValueTypeClosureAux___lam__1___boxed(lean_object* v_a_2599_, lean_object* v_cache_2600_, lean_object* v_a_x3f_2601_, lean_object* v___y_2602_){
_start:
{
lean_object* v_res_2603_; 
v_res_2603_ = l_Lean_Meta_Closure_mkValueTypeClosureAux___lam__1(v_a_2599_, v_cache_2600_, v_a_x3f_2601_);
lean_dec(v_a_x3f_2601_);
lean_dec(v_a_2599_);
return v_res_2603_;
}
}
static lean_object* _init_l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__0(void){
_start:
{
lean_object* v___x_2604_; 
v___x_2604_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2604_;
}
}
static lean_object* _init_l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__1(void){
_start:
{
lean_object* v___x_2605_; lean_object* v___x_2606_; 
v___x_2605_ = lean_obj_once(&l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__0, &l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__0_once, _init_l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__0);
v___x_2606_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2606_, 0, v___x_2605_);
return v___x_2606_;
}
}
static lean_object* _init_l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__2(void){
_start:
{
lean_object* v___x_2607_; lean_object* v___x_2608_; 
v___x_2607_ = lean_obj_once(&l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__1, &l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__1_once, _init_l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__1);
v___x_2608_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2608_, 0, v___x_2607_);
lean_ctor_set(v___x_2608_, 1, v___x_2607_);
lean_ctor_set(v___x_2608_, 2, v___x_2607_);
lean_ctor_set(v___x_2608_, 3, v___x_2607_);
lean_ctor_set(v___x_2608_, 4, v___x_2607_);
lean_ctor_set(v___x_2608_, 5, v___x_2607_);
return v___x_2608_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkValueTypeClosureAux(lean_object* v_type_2609_, lean_object* v_value_2610_, uint8_t v_a_2611_, lean_object* v_a_2612_, lean_object* v_a_2613_, lean_object* v_a_2614_, lean_object* v_a_2615_, lean_object* v_a_2616_){
_start:
{
lean_object* v___x_2618_; lean_object* v___x_2619_; lean_object* v_mctx_2620_; lean_object* v_zetaDeltaFVarIds_2621_; lean_object* v_postponed_2622_; lean_object* v_diag_2623_; lean_object* v___x_2625_; uint8_t v_isShared_2626_; uint8_t v_isSharedCheck_2703_; 
v___x_2618_ = lean_st_ref_get(v_a_2614_);
v___x_2619_ = lean_st_ref_take(v_a_2614_);
v_mctx_2620_ = lean_ctor_get(v___x_2619_, 0);
v_zetaDeltaFVarIds_2621_ = lean_ctor_get(v___x_2619_, 2);
v_postponed_2622_ = lean_ctor_get(v___x_2619_, 3);
v_diag_2623_ = lean_ctor_get(v___x_2619_, 4);
v_isSharedCheck_2703_ = !lean_is_exclusive(v___x_2619_);
if (v_isSharedCheck_2703_ == 0)
{
lean_object* v_unused_2704_; 
v_unused_2704_ = lean_ctor_get(v___x_2619_, 1);
lean_dec(v_unused_2704_);
v___x_2625_ = v___x_2619_;
v_isShared_2626_ = v_isSharedCheck_2703_;
goto v_resetjp_2624_;
}
else
{
lean_inc(v_diag_2623_);
lean_inc(v_postponed_2622_);
lean_inc(v_zetaDeltaFVarIds_2621_);
lean_inc(v_mctx_2620_);
lean_dec(v___x_2619_);
v___x_2625_ = lean_box(0);
v_isShared_2626_ = v_isSharedCheck_2703_;
goto v_resetjp_2624_;
}
v_resetjp_2624_:
{
lean_object* v___x_2627_; lean_object* v___x_2629_; 
v___x_2627_ = lean_obj_once(&l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__2, &l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__2_once, _init_l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__2);
if (v_isShared_2626_ == 0)
{
lean_ctor_set(v___x_2625_, 1, v___x_2627_);
v___x_2629_ = v___x_2625_;
goto v_reusejp_2628_;
}
else
{
lean_object* v_reuseFailAlloc_2702_; 
v_reuseFailAlloc_2702_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2702_, 0, v_mctx_2620_);
lean_ctor_set(v_reuseFailAlloc_2702_, 1, v___x_2627_);
lean_ctor_set(v_reuseFailAlloc_2702_, 2, v_zetaDeltaFVarIds_2621_);
lean_ctor_set(v_reuseFailAlloc_2702_, 3, v_postponed_2622_);
lean_ctor_set(v_reuseFailAlloc_2702_, 4, v_diag_2623_);
v___x_2629_ = v_reuseFailAlloc_2702_;
goto v_reusejp_2628_;
}
v_reusejp_2628_:
{
lean_object* v___x_2630_; lean_object* v___x_2631_; lean_object* v_mctx_2632_; lean_object* v_cache_2633_; lean_object* v_zetaDeltaFVarIds_2634_; lean_object* v_postponed_2635_; lean_object* v_diag_2636_; lean_object* v___x_2638_; uint8_t v_isShared_2639_; uint8_t v_isSharedCheck_2701_; 
v___x_2630_ = lean_st_ref_set(v_a_2614_, v___x_2629_);
v___x_2631_ = lean_st_ref_take(v_a_2614_);
v_mctx_2632_ = lean_ctor_get(v___x_2631_, 0);
v_cache_2633_ = lean_ctor_get(v___x_2631_, 1);
v_zetaDeltaFVarIds_2634_ = lean_ctor_get(v___x_2631_, 2);
v_postponed_2635_ = lean_ctor_get(v___x_2631_, 3);
v_diag_2636_ = lean_ctor_get(v___x_2631_, 4);
v_isSharedCheck_2701_ = !lean_is_exclusive(v___x_2631_);
if (v_isSharedCheck_2701_ == 0)
{
v___x_2638_ = v___x_2631_;
v_isShared_2639_ = v_isSharedCheck_2701_;
goto v_resetjp_2637_;
}
else
{
lean_inc(v_diag_2636_);
lean_inc(v_postponed_2635_);
lean_inc(v_zetaDeltaFVarIds_2634_);
lean_inc(v_cache_2633_);
lean_inc(v_mctx_2632_);
lean_dec(v___x_2631_);
v___x_2638_ = lean_box(0);
v_isShared_2639_ = v_isSharedCheck_2701_;
goto v_resetjp_2637_;
}
v_resetjp_2637_:
{
lean_object* v___x_2640_; lean_object* v___x_2642_; 
v___x_2640_ = lean_box(1);
if (v_isShared_2639_ == 0)
{
lean_ctor_set(v___x_2638_, 2, v___x_2640_);
v___x_2642_ = v___x_2638_;
goto v_reusejp_2641_;
}
else
{
lean_object* v_reuseFailAlloc_2700_; 
v_reuseFailAlloc_2700_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2700_, 0, v_mctx_2632_);
lean_ctor_set(v_reuseFailAlloc_2700_, 1, v_cache_2633_);
lean_ctor_set(v_reuseFailAlloc_2700_, 2, v___x_2640_);
lean_ctor_set(v_reuseFailAlloc_2700_, 3, v_postponed_2635_);
lean_ctor_set(v_reuseFailAlloc_2700_, 4, v_diag_2636_);
v___x_2642_ = v_reuseFailAlloc_2700_;
goto v_reusejp_2641_;
}
v_reusejp_2641_:
{
lean_object* v___x_2643_; lean_object* v_cache_2644_; lean_object* v_keyedConfig_2645_; lean_object* v_zetaDeltaSet_2646_; lean_object* v_lctx_2647_; lean_object* v_localInstances_2648_; lean_object* v_defEqCtx_x3f_2649_; lean_object* v_synthPendingDepth_2650_; lean_object* v_canUnfold_x3f_2651_; uint8_t v_univApprox_2652_; uint8_t v_inTypeClassResolution_2653_; uint8_t v_cacheInferType_2654_; lean_object* v_a_2656_; lean_object* v_a_2668_; uint8_t v___x_2671_; lean_object* v___x_2672_; lean_object* v___x_2673_; 
v___x_2643_ = lean_st_ref_set(v_a_2614_, v___x_2642_);
v_cache_2644_ = lean_ctor_get(v___x_2618_, 1);
lean_inc_ref(v_cache_2644_);
lean_dec(v___x_2618_);
v_keyedConfig_2645_ = lean_ctor_get(v_a_2613_, 0);
v_zetaDeltaSet_2646_ = lean_ctor_get(v_a_2613_, 1);
v_lctx_2647_ = lean_ctor_get(v_a_2613_, 2);
v_localInstances_2648_ = lean_ctor_get(v_a_2613_, 3);
v_defEqCtx_x3f_2649_ = lean_ctor_get(v_a_2613_, 4);
v_synthPendingDepth_2650_ = lean_ctor_get(v_a_2613_, 5);
v_canUnfold_x3f_2651_ = lean_ctor_get(v_a_2613_, 6);
v_univApprox_2652_ = lean_ctor_get_uint8(v_a_2613_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2653_ = lean_ctor_get_uint8(v_a_2613_, sizeof(void*)*7 + 2);
v_cacheInferType_2654_ = lean_ctor_get_uint8(v_a_2613_, sizeof(void*)*7 + 3);
v___x_2671_ = 1;
lean_inc(v_canUnfold_x3f_2651_);
lean_inc(v_synthPendingDepth_2650_);
lean_inc(v_defEqCtx_x3f_2649_);
lean_inc_ref(v_localInstances_2648_);
lean_inc_ref(v_lctx_2647_);
lean_inc(v_zetaDeltaSet_2646_);
lean_inc_ref(v_keyedConfig_2645_);
v___x_2672_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2672_, 0, v_keyedConfig_2645_);
lean_ctor_set(v___x_2672_, 1, v_zetaDeltaSet_2646_);
lean_ctor_set(v___x_2672_, 2, v_lctx_2647_);
lean_ctor_set(v___x_2672_, 3, v_localInstances_2648_);
lean_ctor_set(v___x_2672_, 4, v_defEqCtx_x3f_2649_);
lean_ctor_set(v___x_2672_, 5, v_synthPendingDepth_2650_);
lean_ctor_set(v___x_2672_, 6, v_canUnfold_x3f_2651_);
lean_ctor_set_uint8(v___x_2672_, sizeof(void*)*7, v___x_2671_);
lean_ctor_set_uint8(v___x_2672_, sizeof(void*)*7 + 1, v_univApprox_2652_);
lean_ctor_set_uint8(v___x_2672_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2653_);
lean_ctor_set_uint8(v___x_2672_, sizeof(void*)*7 + 3, v_cacheInferType_2654_);
v___x_2673_ = l_Lean_Meta_Closure_collectExpr(v_type_2609_, v_a_2611_, v_a_2612_, v___x_2672_, v_a_2614_, v_a_2615_, v_a_2616_);
if (lean_obj_tag(v___x_2673_) == 0)
{
lean_object* v_a_2674_; lean_object* v___x_2675_; 
v_a_2674_ = lean_ctor_get(v___x_2673_, 0);
lean_inc(v_a_2674_);
lean_dec_ref(v___x_2673_);
v___x_2675_ = l_Lean_Meta_Closure_collectExpr(v_value_2610_, v_a_2611_, v_a_2612_, v___x_2672_, v_a_2614_, v_a_2615_, v_a_2616_);
if (lean_obj_tag(v___x_2675_) == 0)
{
lean_object* v_a_2676_; lean_object* v___x_2677_; 
v_a_2676_ = lean_ctor_get(v___x_2675_, 0);
lean_inc(v_a_2676_);
lean_dec_ref(v___x_2675_);
v___x_2677_ = l_Lean_Meta_Closure_process(v_a_2611_, v_a_2612_, v___x_2672_, v_a_2614_, v_a_2615_, v_a_2616_);
lean_dec_ref(v___x_2672_);
if (lean_obj_tag(v___x_2677_) == 0)
{
lean_object* v___x_2679_; uint8_t v_isShared_2680_; uint8_t v_isSharedCheck_2695_; 
v_isSharedCheck_2695_ = !lean_is_exclusive(v___x_2677_);
if (v_isSharedCheck_2695_ == 0)
{
lean_object* v_unused_2696_; 
v_unused_2696_ = lean_ctor_get(v___x_2677_, 0);
lean_dec(v_unused_2696_);
v___x_2679_ = v___x_2677_;
v_isShared_2680_ = v_isSharedCheck_2695_;
goto v_resetjp_2678_;
}
else
{
lean_dec(v___x_2677_);
v___x_2679_ = lean_box(0);
v_isShared_2680_ = v_isSharedCheck_2695_;
goto v_resetjp_2678_;
}
v_resetjp_2678_:
{
lean_object* v___x_2681_; lean_object* v___x_2683_; 
v___x_2681_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2681_, 0, v_a_2674_);
lean_ctor_set(v___x_2681_, 1, v_a_2676_);
lean_inc_ref(v___x_2681_);
if (v_isShared_2680_ == 0)
{
lean_ctor_set_tag(v___x_2679_, 1);
lean_ctor_set(v___x_2679_, 0, v___x_2681_);
v___x_2683_ = v___x_2679_;
goto v_reusejp_2682_;
}
else
{
lean_object* v_reuseFailAlloc_2694_; 
v_reuseFailAlloc_2694_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2694_, 0, v___x_2681_);
v___x_2683_ = v_reuseFailAlloc_2694_;
goto v_reusejp_2682_;
}
v_reusejp_2682_:
{
lean_object* v___x_2684_; lean_object* v___x_2685_; lean_object* v___x_2687_; uint8_t v_isShared_2688_; uint8_t v_isSharedCheck_2692_; 
v___x_2684_ = l_Lean_Meta_Closure_mkValueTypeClosureAux___lam__0(v_a_2614_, v_zetaDeltaFVarIds_2634_, v___x_2683_);
lean_dec_ref(v___x_2684_);
v___x_2685_ = l_Lean_Meta_Closure_mkValueTypeClosureAux___lam__1(v_a_2614_, v_cache_2644_, v___x_2683_);
lean_dec_ref(v___x_2683_);
v_isSharedCheck_2692_ = !lean_is_exclusive(v___x_2685_);
if (v_isSharedCheck_2692_ == 0)
{
lean_object* v_unused_2693_; 
v_unused_2693_ = lean_ctor_get(v___x_2685_, 0);
lean_dec(v_unused_2693_);
v___x_2687_ = v___x_2685_;
v_isShared_2688_ = v_isSharedCheck_2692_;
goto v_resetjp_2686_;
}
else
{
lean_dec(v___x_2685_);
v___x_2687_ = lean_box(0);
v_isShared_2688_ = v_isSharedCheck_2692_;
goto v_resetjp_2686_;
}
v_resetjp_2686_:
{
lean_object* v___x_2690_; 
if (v_isShared_2688_ == 0)
{
lean_ctor_set(v___x_2687_, 0, v___x_2681_);
v___x_2690_ = v___x_2687_;
goto v_reusejp_2689_;
}
else
{
lean_object* v_reuseFailAlloc_2691_; 
v_reuseFailAlloc_2691_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2691_, 0, v___x_2681_);
v___x_2690_ = v_reuseFailAlloc_2691_;
goto v_reusejp_2689_;
}
v_reusejp_2689_:
{
return v___x_2690_;
}
}
}
}
}
else
{
lean_object* v_a_2697_; 
lean_dec(v_a_2676_);
lean_dec(v_a_2674_);
v_a_2697_ = lean_ctor_get(v___x_2677_, 0);
lean_inc(v_a_2697_);
lean_dec_ref(v___x_2677_);
v_a_2668_ = v_a_2697_;
goto v___jp_2667_;
}
}
else
{
lean_object* v_a_2698_; 
lean_dec(v_a_2674_);
lean_dec_ref(v___x_2672_);
v_a_2698_ = lean_ctor_get(v___x_2675_, 0);
lean_inc(v_a_2698_);
lean_dec_ref(v___x_2675_);
v_a_2668_ = v_a_2698_;
goto v___jp_2667_;
}
}
else
{
lean_object* v_a_2699_; 
lean_dec_ref(v___x_2672_);
lean_dec_ref(v_value_2610_);
v_a_2699_ = lean_ctor_get(v___x_2673_, 0);
lean_inc(v_a_2699_);
lean_dec_ref(v___x_2673_);
v_a_2668_ = v_a_2699_;
goto v___jp_2667_;
}
v___jp_2655_:
{
lean_object* v___x_2657_; lean_object* v___x_2658_; lean_object* v___x_2660_; uint8_t v_isShared_2661_; uint8_t v_isSharedCheck_2665_; 
v___x_2657_ = lean_box(0);
v___x_2658_ = l_Lean_Meta_Closure_mkValueTypeClosureAux___lam__1(v_a_2614_, v_cache_2644_, v___x_2657_);
v_isSharedCheck_2665_ = !lean_is_exclusive(v___x_2658_);
if (v_isSharedCheck_2665_ == 0)
{
lean_object* v_unused_2666_; 
v_unused_2666_ = lean_ctor_get(v___x_2658_, 0);
lean_dec(v_unused_2666_);
v___x_2660_ = v___x_2658_;
v_isShared_2661_ = v_isSharedCheck_2665_;
goto v_resetjp_2659_;
}
else
{
lean_dec(v___x_2658_);
v___x_2660_ = lean_box(0);
v_isShared_2661_ = v_isSharedCheck_2665_;
goto v_resetjp_2659_;
}
v_resetjp_2659_:
{
lean_object* v___x_2663_; 
if (v_isShared_2661_ == 0)
{
lean_ctor_set_tag(v___x_2660_, 1);
lean_ctor_set(v___x_2660_, 0, v_a_2656_);
v___x_2663_ = v___x_2660_;
goto v_reusejp_2662_;
}
else
{
lean_object* v_reuseFailAlloc_2664_; 
v_reuseFailAlloc_2664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2664_, 0, v_a_2656_);
v___x_2663_ = v_reuseFailAlloc_2664_;
goto v_reusejp_2662_;
}
v_reusejp_2662_:
{
return v___x_2663_;
}
}
}
v___jp_2667_:
{
lean_object* v___x_2669_; lean_object* v___x_2670_; 
v___x_2669_ = lean_box(0);
v___x_2670_ = l_Lean_Meta_Closure_mkValueTypeClosureAux___lam__0(v_a_2614_, v_zetaDeltaFVarIds_2634_, v___x_2669_);
lean_dec_ref(v___x_2670_);
v_a_2656_ = v_a_2668_;
goto v___jp_2655_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkValueTypeClosureAux___boxed(lean_object* v_type_2705_, lean_object* v_value_2706_, lean_object* v_a_2707_, lean_object* v_a_2708_, lean_object* v_a_2709_, lean_object* v_a_2710_, lean_object* v_a_2711_, lean_object* v_a_2712_, lean_object* v_a_2713_){
_start:
{
uint8_t v_a_boxed_2714_; lean_object* v_res_2715_; 
v_a_boxed_2714_ = lean_unbox(v_a_2707_);
v_res_2715_ = l_Lean_Meta_Closure_mkValueTypeClosureAux(v_type_2705_, v_value_2706_, v_a_boxed_2714_, v_a_2708_, v_a_2709_, v_a_2710_, v_a_2711_, v_a_2712_);
lean_dec(v_a_2712_);
lean_dec_ref(v_a_2711_);
lean_dec(v_a_2710_);
lean_dec_ref(v_a_2709_);
lean_dec(v_a_2708_);
return v_res_2715_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4___closed__0(void){
_start:
{
lean_object* v___x_2716_; 
v___x_2716_ = l_instMonadEIO(lean_box(0));
return v___x_2716_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4(lean_object* v_msg_2719_, lean_object* v___y_2720_, lean_object* v___y_2721_, lean_object* v___y_2722_){
_start:
{
lean_object* v___x_2724_; lean_object* v___x_2725_; lean_object* v_toApplicative_2726_; lean_object* v___x_2728_; uint8_t v_isShared_2729_; uint8_t v_isSharedCheck_2767_; 
v___x_2724_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4___closed__0, &l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4___closed__0);
v___x_2725_ = l_StateRefT_x27_instMonad___redArg(v___x_2724_);
v_toApplicative_2726_ = lean_ctor_get(v___x_2725_, 0);
v_isSharedCheck_2767_ = !lean_is_exclusive(v___x_2725_);
if (v_isSharedCheck_2767_ == 0)
{
lean_object* v_unused_2768_; 
v_unused_2768_ = lean_ctor_get(v___x_2725_, 1);
lean_dec(v_unused_2768_);
v___x_2728_ = v___x_2725_;
v_isShared_2729_ = v_isSharedCheck_2767_;
goto v_resetjp_2727_;
}
else
{
lean_inc(v_toApplicative_2726_);
lean_dec(v___x_2725_);
v___x_2728_ = lean_box(0);
v_isShared_2729_ = v_isSharedCheck_2767_;
goto v_resetjp_2727_;
}
v_resetjp_2727_:
{
lean_object* v_toFunctor_2730_; lean_object* v_toSeq_2731_; lean_object* v_toSeqLeft_2732_; lean_object* v_toSeqRight_2733_; lean_object* v___x_2735_; uint8_t v_isShared_2736_; uint8_t v_isSharedCheck_2765_; 
v_toFunctor_2730_ = lean_ctor_get(v_toApplicative_2726_, 0);
v_toSeq_2731_ = lean_ctor_get(v_toApplicative_2726_, 2);
v_toSeqLeft_2732_ = lean_ctor_get(v_toApplicative_2726_, 3);
v_toSeqRight_2733_ = lean_ctor_get(v_toApplicative_2726_, 4);
v_isSharedCheck_2765_ = !lean_is_exclusive(v_toApplicative_2726_);
if (v_isSharedCheck_2765_ == 0)
{
lean_object* v_unused_2766_; 
v_unused_2766_ = lean_ctor_get(v_toApplicative_2726_, 1);
lean_dec(v_unused_2766_);
v___x_2735_ = v_toApplicative_2726_;
v_isShared_2736_ = v_isSharedCheck_2765_;
goto v_resetjp_2734_;
}
else
{
lean_inc(v_toSeqRight_2733_);
lean_inc(v_toSeqLeft_2732_);
lean_inc(v_toSeq_2731_);
lean_inc(v_toFunctor_2730_);
lean_dec(v_toApplicative_2726_);
v___x_2735_ = lean_box(0);
v_isShared_2736_ = v_isSharedCheck_2765_;
goto v_resetjp_2734_;
}
v_resetjp_2734_:
{
lean_object* v___f_2737_; lean_object* v___f_2738_; lean_object* v___f_2739_; lean_object* v___f_2740_; lean_object* v___x_2741_; lean_object* v___f_2742_; lean_object* v___f_2743_; lean_object* v___f_2744_; lean_object* v___x_2746_; 
v___f_2737_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4___closed__1));
v___f_2738_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4___closed__2));
lean_inc_ref(v_toFunctor_2730_);
v___f_2739_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2739_, 0, v_toFunctor_2730_);
v___f_2740_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2740_, 0, v_toFunctor_2730_);
v___x_2741_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2741_, 0, v___f_2739_);
lean_ctor_set(v___x_2741_, 1, v___f_2740_);
v___f_2742_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2742_, 0, v_toSeqRight_2733_);
v___f_2743_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2743_, 0, v_toSeqLeft_2732_);
v___f_2744_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2744_, 0, v_toSeq_2731_);
if (v_isShared_2736_ == 0)
{
lean_ctor_set(v___x_2735_, 4, v___f_2742_);
lean_ctor_set(v___x_2735_, 3, v___f_2743_);
lean_ctor_set(v___x_2735_, 2, v___f_2744_);
lean_ctor_set(v___x_2735_, 1, v___f_2737_);
lean_ctor_set(v___x_2735_, 0, v___x_2741_);
v___x_2746_ = v___x_2735_;
goto v_reusejp_2745_;
}
else
{
lean_object* v_reuseFailAlloc_2764_; 
v_reuseFailAlloc_2764_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2764_, 0, v___x_2741_);
lean_ctor_set(v_reuseFailAlloc_2764_, 1, v___f_2737_);
lean_ctor_set(v_reuseFailAlloc_2764_, 2, v___f_2744_);
lean_ctor_set(v_reuseFailAlloc_2764_, 3, v___f_2743_);
lean_ctor_set(v_reuseFailAlloc_2764_, 4, v___f_2742_);
v___x_2746_ = v_reuseFailAlloc_2764_;
goto v_reusejp_2745_;
}
v_reusejp_2745_:
{
lean_object* v___x_2748_; 
if (v_isShared_2729_ == 0)
{
lean_ctor_set(v___x_2728_, 1, v___f_2738_);
lean_ctor_set(v___x_2728_, 0, v___x_2746_);
v___x_2748_ = v___x_2728_;
goto v_reusejp_2747_;
}
else
{
lean_object* v_reuseFailAlloc_2763_; 
v_reuseFailAlloc_2763_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2763_, 0, v___x_2746_);
lean_ctor_set(v_reuseFailAlloc_2763_, 1, v___f_2738_);
v___x_2748_ = v_reuseFailAlloc_2763_;
goto v_reusejp_2747_;
}
v_reusejp_2747_:
{
lean_object* v___f_2749_; lean_object* v___f_2750_; lean_object* v___f_2751_; lean_object* v___f_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; lean_object* v___x_2756_; lean_object* v___x_2757_; lean_object* v___x_2758_; lean_object* v___x_2759_; lean_object* v___x_2760_; lean_object* v___x_14557__overap_2761_; lean_object* v___x_2762_; 
lean_inc_ref_n(v___x_2748_, 6);
v___f_2749_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2749_, 0, v___x_2748_);
v___f_2750_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2750_, 0, v___x_2748_);
v___f_2751_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_2751_, 0, v___x_2748_);
v___f_2752_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_2752_, 0, v___x_2748_);
v___x_2753_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_2753_, 0, lean_box(0));
lean_closure_set(v___x_2753_, 1, lean_box(0));
lean_closure_set(v___x_2753_, 2, v___x_2748_);
v___x_2754_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2754_, 0, v___x_2753_);
lean_ctor_set(v___x_2754_, 1, v___f_2749_);
v___x_2755_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_2755_, 0, lean_box(0));
lean_closure_set(v___x_2755_, 1, lean_box(0));
lean_closure_set(v___x_2755_, 2, v___x_2748_);
v___x_2756_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2756_, 0, v___x_2754_);
lean_ctor_set(v___x_2756_, 1, v___x_2755_);
lean_ctor_set(v___x_2756_, 2, v___f_2750_);
lean_ctor_set(v___x_2756_, 3, v___f_2751_);
lean_ctor_set(v___x_2756_, 4, v___f_2752_);
v___x_2757_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_2757_, 0, lean_box(0));
lean_closure_set(v___x_2757_, 1, lean_box(0));
lean_closure_set(v___x_2757_, 2, v___x_2748_);
v___x_2758_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2758_, 0, v___x_2756_);
lean_ctor_set(v___x_2758_, 1, v___x_2757_);
v___x_2759_ = lean_box(0);
v___x_2760_ = l_instInhabitedOfMonad___redArg(v___x_2758_, v___x_2759_);
v___x_14557__overap_2761_ = lean_panic_fn_borrowed(v___x_2760_, v_msg_2719_);
lean_dec(v___x_2760_);
lean_inc(v___y_2722_);
lean_inc_ref(v___y_2721_);
v___x_2762_ = lean_apply_4(v___x_14557__overap_2761_, v___y_2720_, v___y_2721_, v___y_2722_, lean_box(0));
return v___x_2762_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4___boxed(lean_object* v_msg_2769_, lean_object* v___y_2770_, lean_object* v___y_2771_, lean_object* v___y_2772_, lean_object* v___y_2773_){
_start:
{
lean_object* v_res_2774_; 
v_res_2774_ = l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4(v_msg_2769_, v___y_2770_, v___y_2771_, v___y_2772_);
lean_dec(v___y_2772_);
lean_dec_ref(v___y_2771_);
return v_res_2774_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1_spec__2___redArg(lean_object* v_a_2775_, lean_object* v_x_2776_){
_start:
{
if (lean_obj_tag(v_x_2776_) == 0)
{
uint8_t v___x_2777_; 
v___x_2777_ = 0;
return v___x_2777_;
}
else
{
lean_object* v_key_2778_; lean_object* v_tail_2779_; uint8_t v___x_2780_; 
v_key_2778_ = lean_ctor_get(v_x_2776_, 0);
v_tail_2779_ = lean_ctor_get(v_x_2776_, 2);
v___x_2780_ = l_Lean_instBEqFVarId_beq(v_key_2778_, v_a_2775_);
if (v___x_2780_ == 0)
{
v_x_2776_ = v_tail_2779_;
goto _start;
}
else
{
return v___x_2780_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1_spec__2___redArg___boxed(lean_object* v_a_2782_, lean_object* v_x_2783_){
_start:
{
uint8_t v_res_2784_; lean_object* v_r_2785_; 
v_res_2784_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1_spec__2___redArg(v_a_2782_, v_x_2783_);
lean_dec(v_x_2783_);
lean_dec(v_a_2782_);
v_r_2785_ = lean_box(v_res_2784_);
return v_r_2785_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__4_spec__6_spec__11___redArg(lean_object* v_x_2786_, lean_object* v_x_2787_){
_start:
{
if (lean_obj_tag(v_x_2787_) == 0)
{
return v_x_2786_;
}
else
{
lean_object* v_key_2788_; lean_object* v_value_2789_; lean_object* v_tail_2790_; lean_object* v___x_2792_; uint8_t v_isShared_2793_; uint8_t v_isSharedCheck_2813_; 
v_key_2788_ = lean_ctor_get(v_x_2787_, 0);
v_value_2789_ = lean_ctor_get(v_x_2787_, 1);
v_tail_2790_ = lean_ctor_get(v_x_2787_, 2);
v_isSharedCheck_2813_ = !lean_is_exclusive(v_x_2787_);
if (v_isSharedCheck_2813_ == 0)
{
v___x_2792_ = v_x_2787_;
v_isShared_2793_ = v_isSharedCheck_2813_;
goto v_resetjp_2791_;
}
else
{
lean_inc(v_tail_2790_);
lean_inc(v_value_2789_);
lean_inc(v_key_2788_);
lean_dec(v_x_2787_);
v___x_2792_ = lean_box(0);
v_isShared_2793_ = v_isSharedCheck_2813_;
goto v_resetjp_2791_;
}
v_resetjp_2791_:
{
lean_object* v___x_2794_; uint64_t v___x_2795_; uint64_t v___x_2796_; uint64_t v___x_2797_; uint64_t v_fold_2798_; uint64_t v___x_2799_; uint64_t v___x_2800_; uint64_t v___x_2801_; size_t v___x_2802_; size_t v___x_2803_; size_t v___x_2804_; size_t v___x_2805_; size_t v___x_2806_; lean_object* v___x_2807_; lean_object* v___x_2809_; 
v___x_2794_ = lean_array_get_size(v_x_2786_);
v___x_2795_ = l_Lean_instHashableFVarId_hash(v_key_2788_);
v___x_2796_ = 32ULL;
v___x_2797_ = lean_uint64_shift_right(v___x_2795_, v___x_2796_);
v_fold_2798_ = lean_uint64_xor(v___x_2795_, v___x_2797_);
v___x_2799_ = 16ULL;
v___x_2800_ = lean_uint64_shift_right(v_fold_2798_, v___x_2799_);
v___x_2801_ = lean_uint64_xor(v_fold_2798_, v___x_2800_);
v___x_2802_ = lean_uint64_to_usize(v___x_2801_);
v___x_2803_ = lean_usize_of_nat(v___x_2794_);
v___x_2804_ = ((size_t)1ULL);
v___x_2805_ = lean_usize_sub(v___x_2803_, v___x_2804_);
v___x_2806_ = lean_usize_land(v___x_2802_, v___x_2805_);
v___x_2807_ = lean_array_uget_borrowed(v_x_2786_, v___x_2806_);
lean_inc(v___x_2807_);
if (v_isShared_2793_ == 0)
{
lean_ctor_set(v___x_2792_, 2, v___x_2807_);
v___x_2809_ = v___x_2792_;
goto v_reusejp_2808_;
}
else
{
lean_object* v_reuseFailAlloc_2812_; 
v_reuseFailAlloc_2812_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2812_, 0, v_key_2788_);
lean_ctor_set(v_reuseFailAlloc_2812_, 1, v_value_2789_);
lean_ctor_set(v_reuseFailAlloc_2812_, 2, v___x_2807_);
v___x_2809_ = v_reuseFailAlloc_2812_;
goto v_reusejp_2808_;
}
v_reusejp_2808_:
{
lean_object* v___x_2810_; 
v___x_2810_ = lean_array_uset(v_x_2786_, v___x_2806_, v___x_2809_);
v_x_2786_ = v___x_2810_;
v_x_2787_ = v_tail_2790_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__4_spec__6___redArg(lean_object* v_i_2814_, lean_object* v_source_2815_, lean_object* v_target_2816_){
_start:
{
lean_object* v___x_2817_; uint8_t v___x_2818_; 
v___x_2817_ = lean_array_get_size(v_source_2815_);
v___x_2818_ = lean_nat_dec_lt(v_i_2814_, v___x_2817_);
if (v___x_2818_ == 0)
{
lean_dec_ref(v_source_2815_);
lean_dec(v_i_2814_);
return v_target_2816_;
}
else
{
lean_object* v_es_2819_; lean_object* v___x_2820_; lean_object* v_source_2821_; lean_object* v_target_2822_; lean_object* v___x_2823_; lean_object* v___x_2824_; 
v_es_2819_ = lean_array_fget(v_source_2815_, v_i_2814_);
v___x_2820_ = lean_box(0);
v_source_2821_ = lean_array_fset(v_source_2815_, v_i_2814_, v___x_2820_);
v_target_2822_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__4_spec__6_spec__11___redArg(v_target_2816_, v_es_2819_);
v___x_2823_ = lean_unsigned_to_nat(1u);
v___x_2824_ = lean_nat_add(v_i_2814_, v___x_2823_);
lean_dec(v_i_2814_);
v_i_2814_ = v___x_2824_;
v_source_2815_ = v_source_2821_;
v_target_2816_ = v_target_2822_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__4___redArg(lean_object* v_data_2826_){
_start:
{
lean_object* v___x_2827_; lean_object* v___x_2828_; lean_object* v_nbuckets_2829_; lean_object* v___x_2830_; lean_object* v___x_2831_; lean_object* v___x_2832_; lean_object* v___x_2833_; 
v___x_2827_ = lean_array_get_size(v_data_2826_);
v___x_2828_ = lean_unsigned_to_nat(2u);
v_nbuckets_2829_ = lean_nat_mul(v___x_2827_, v___x_2828_);
v___x_2830_ = lean_unsigned_to_nat(0u);
v___x_2831_ = lean_box(0);
v___x_2832_ = lean_mk_array(v_nbuckets_2829_, v___x_2831_);
v___x_2833_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__4_spec__6___redArg(v___x_2830_, v_data_2826_, v___x_2832_);
return v___x_2833_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2___redArg(lean_object* v_m_2834_, lean_object* v_a_2835_, lean_object* v_b_2836_){
_start:
{
lean_object* v_size_2837_; lean_object* v_buckets_2838_; lean_object* v___x_2839_; uint64_t v___x_2840_; uint64_t v___x_2841_; uint64_t v___x_2842_; uint64_t v_fold_2843_; uint64_t v___x_2844_; uint64_t v___x_2845_; uint64_t v___x_2846_; size_t v___x_2847_; size_t v___x_2848_; size_t v___x_2849_; size_t v___x_2850_; size_t v___x_2851_; lean_object* v_bkt_2852_; uint8_t v___x_2853_; 
v_size_2837_ = lean_ctor_get(v_m_2834_, 0);
v_buckets_2838_ = lean_ctor_get(v_m_2834_, 1);
v___x_2839_ = lean_array_get_size(v_buckets_2838_);
v___x_2840_ = l_Lean_instHashableFVarId_hash(v_a_2835_);
v___x_2841_ = 32ULL;
v___x_2842_ = lean_uint64_shift_right(v___x_2840_, v___x_2841_);
v_fold_2843_ = lean_uint64_xor(v___x_2840_, v___x_2842_);
v___x_2844_ = 16ULL;
v___x_2845_ = lean_uint64_shift_right(v_fold_2843_, v___x_2844_);
v___x_2846_ = lean_uint64_xor(v_fold_2843_, v___x_2845_);
v___x_2847_ = lean_uint64_to_usize(v___x_2846_);
v___x_2848_ = lean_usize_of_nat(v___x_2839_);
v___x_2849_ = ((size_t)1ULL);
v___x_2850_ = lean_usize_sub(v___x_2848_, v___x_2849_);
v___x_2851_ = lean_usize_land(v___x_2847_, v___x_2850_);
v_bkt_2852_ = lean_array_uget_borrowed(v_buckets_2838_, v___x_2851_);
v___x_2853_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1_spec__2___redArg(v_a_2835_, v_bkt_2852_);
if (v___x_2853_ == 0)
{
lean_object* v___x_2855_; uint8_t v_isShared_2856_; uint8_t v_isSharedCheck_2874_; 
lean_inc_ref(v_buckets_2838_);
lean_inc(v_size_2837_);
v_isSharedCheck_2874_ = !lean_is_exclusive(v_m_2834_);
if (v_isSharedCheck_2874_ == 0)
{
lean_object* v_unused_2875_; lean_object* v_unused_2876_; 
v_unused_2875_ = lean_ctor_get(v_m_2834_, 1);
lean_dec(v_unused_2875_);
v_unused_2876_ = lean_ctor_get(v_m_2834_, 0);
lean_dec(v_unused_2876_);
v___x_2855_ = v_m_2834_;
v_isShared_2856_ = v_isSharedCheck_2874_;
goto v_resetjp_2854_;
}
else
{
lean_dec(v_m_2834_);
v___x_2855_ = lean_box(0);
v_isShared_2856_ = v_isSharedCheck_2874_;
goto v_resetjp_2854_;
}
v_resetjp_2854_:
{
lean_object* v___x_2857_; lean_object* v_size_x27_2858_; lean_object* v___x_2859_; lean_object* v_buckets_x27_2860_; lean_object* v___x_2861_; lean_object* v___x_2862_; lean_object* v___x_2863_; lean_object* v___x_2864_; lean_object* v___x_2865_; uint8_t v___x_2866_; 
v___x_2857_ = lean_unsigned_to_nat(1u);
v_size_x27_2858_ = lean_nat_add(v_size_2837_, v___x_2857_);
lean_dec(v_size_2837_);
lean_inc(v_bkt_2852_);
v___x_2859_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2859_, 0, v_a_2835_);
lean_ctor_set(v___x_2859_, 1, v_b_2836_);
lean_ctor_set(v___x_2859_, 2, v_bkt_2852_);
v_buckets_x27_2860_ = lean_array_uset(v_buckets_2838_, v___x_2851_, v___x_2859_);
v___x_2861_ = lean_unsigned_to_nat(4u);
v___x_2862_ = lean_nat_mul(v_size_x27_2858_, v___x_2861_);
v___x_2863_ = lean_unsigned_to_nat(3u);
v___x_2864_ = lean_nat_div(v___x_2862_, v___x_2863_);
lean_dec(v___x_2862_);
v___x_2865_ = lean_array_get_size(v_buckets_x27_2860_);
v___x_2866_ = lean_nat_dec_le(v___x_2864_, v___x_2865_);
lean_dec(v___x_2864_);
if (v___x_2866_ == 0)
{
lean_object* v_val_2867_; lean_object* v___x_2869_; 
v_val_2867_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__4___redArg(v_buckets_x27_2860_);
if (v_isShared_2856_ == 0)
{
lean_ctor_set(v___x_2855_, 1, v_val_2867_);
lean_ctor_set(v___x_2855_, 0, v_size_x27_2858_);
v___x_2869_ = v___x_2855_;
goto v_reusejp_2868_;
}
else
{
lean_object* v_reuseFailAlloc_2870_; 
v_reuseFailAlloc_2870_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2870_, 0, v_size_x27_2858_);
lean_ctor_set(v_reuseFailAlloc_2870_, 1, v_val_2867_);
v___x_2869_ = v_reuseFailAlloc_2870_;
goto v_reusejp_2868_;
}
v_reusejp_2868_:
{
return v___x_2869_;
}
}
else
{
lean_object* v___x_2872_; 
if (v_isShared_2856_ == 0)
{
lean_ctor_set(v___x_2855_, 1, v_buckets_x27_2860_);
lean_ctor_set(v___x_2855_, 0, v_size_x27_2858_);
v___x_2872_ = v___x_2855_;
goto v_reusejp_2871_;
}
else
{
lean_object* v_reuseFailAlloc_2873_; 
v_reuseFailAlloc_2873_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2873_, 0, v_size_x27_2858_);
lean_ctor_set(v_reuseFailAlloc_2873_, 1, v_buckets_x27_2860_);
v___x_2872_ = v_reuseFailAlloc_2873_;
goto v_reusejp_2871_;
}
v_reusejp_2871_:
{
return v___x_2872_;
}
}
}
}
else
{
lean_dec(v_b_2836_);
lean_dec(v_a_2835_);
return v_m_2834_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1___redArg(lean_object* v_m_2877_, lean_object* v_a_2878_){
_start:
{
lean_object* v_buckets_2879_; lean_object* v___x_2880_; uint64_t v___x_2881_; uint64_t v___x_2882_; uint64_t v___x_2883_; uint64_t v_fold_2884_; uint64_t v___x_2885_; uint64_t v___x_2886_; uint64_t v___x_2887_; size_t v___x_2888_; size_t v___x_2889_; size_t v___x_2890_; size_t v___x_2891_; size_t v___x_2892_; lean_object* v___x_2893_; uint8_t v___x_2894_; 
v_buckets_2879_ = lean_ctor_get(v_m_2877_, 1);
v___x_2880_ = lean_array_get_size(v_buckets_2879_);
v___x_2881_ = l_Lean_instHashableFVarId_hash(v_a_2878_);
v___x_2882_ = 32ULL;
v___x_2883_ = lean_uint64_shift_right(v___x_2881_, v___x_2882_);
v_fold_2884_ = lean_uint64_xor(v___x_2881_, v___x_2883_);
v___x_2885_ = 16ULL;
v___x_2886_ = lean_uint64_shift_right(v_fold_2884_, v___x_2885_);
v___x_2887_ = lean_uint64_xor(v_fold_2884_, v___x_2886_);
v___x_2888_ = lean_uint64_to_usize(v___x_2887_);
v___x_2889_ = lean_usize_of_nat(v___x_2880_);
v___x_2890_ = ((size_t)1ULL);
v___x_2891_ = lean_usize_sub(v___x_2889_, v___x_2890_);
v___x_2892_ = lean_usize_land(v___x_2888_, v___x_2891_);
v___x_2893_ = lean_array_uget_borrowed(v_buckets_2879_, v___x_2892_);
v___x_2894_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1_spec__2___redArg(v_a_2878_, v___x_2893_);
return v___x_2894_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1___redArg___boxed(lean_object* v_m_2895_, lean_object* v_a_2896_){
_start:
{
uint8_t v_res_2897_; lean_object* v_r_2898_; 
v_res_2897_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1___redArg(v_m_2895_, v_a_2896_);
lean_dec(v_a_2896_);
lean_dec_ref(v_m_2895_);
v_r_2898_ = lean_box(v_res_2897_);
return v_r_2898_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__6_spec__9___redArg(lean_object* v_a_2899_, lean_object* v_x_2900_){
_start:
{
if (lean_obj_tag(v_x_2900_) == 0)
{
lean_object* v___x_2901_; 
v___x_2901_ = lean_box(0);
return v___x_2901_;
}
else
{
lean_object* v_key_2902_; lean_object* v_value_2903_; lean_object* v_tail_2904_; uint8_t v___x_2905_; 
v_key_2902_ = lean_ctor_get(v_x_2900_, 0);
v_value_2903_ = lean_ctor_get(v_x_2900_, 1);
v_tail_2904_ = lean_ctor_get(v_x_2900_, 2);
v___x_2905_ = lean_expr_eqv(v_key_2902_, v_a_2899_);
if (v___x_2905_ == 0)
{
v_x_2900_ = v_tail_2904_;
goto _start;
}
else
{
lean_object* v___x_2907_; 
lean_inc(v_value_2903_);
v___x_2907_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2907_, 0, v_value_2903_);
return v___x_2907_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__6_spec__9___redArg___boxed(lean_object* v_a_2908_, lean_object* v_x_2909_){
_start:
{
lean_object* v_res_2910_; 
v_res_2910_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__6_spec__9___redArg(v_a_2908_, v_x_2909_);
lean_dec(v_x_2909_);
lean_dec_ref(v_a_2908_);
return v_res_2910_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__6___redArg(lean_object* v_m_2911_, lean_object* v_a_2912_){
_start:
{
lean_object* v_buckets_2913_; lean_object* v___x_2914_; uint64_t v___x_2915_; uint64_t v___x_2916_; uint64_t v___x_2917_; uint64_t v_fold_2918_; uint64_t v___x_2919_; uint64_t v___x_2920_; uint64_t v___x_2921_; size_t v___x_2922_; size_t v___x_2923_; size_t v___x_2924_; size_t v___x_2925_; size_t v___x_2926_; lean_object* v___x_2927_; lean_object* v___x_2928_; 
v_buckets_2913_ = lean_ctor_get(v_m_2911_, 1);
v___x_2914_ = lean_array_get_size(v_buckets_2913_);
v___x_2915_ = l_Lean_Expr_hash(v_a_2912_);
v___x_2916_ = 32ULL;
v___x_2917_ = lean_uint64_shift_right(v___x_2915_, v___x_2916_);
v_fold_2918_ = lean_uint64_xor(v___x_2915_, v___x_2917_);
v___x_2919_ = 16ULL;
v___x_2920_ = lean_uint64_shift_right(v_fold_2918_, v___x_2919_);
v___x_2921_ = lean_uint64_xor(v_fold_2918_, v___x_2920_);
v___x_2922_ = lean_uint64_to_usize(v___x_2921_);
v___x_2923_ = lean_usize_of_nat(v___x_2914_);
v___x_2924_ = ((size_t)1ULL);
v___x_2925_ = lean_usize_sub(v___x_2923_, v___x_2924_);
v___x_2926_ = lean_usize_land(v___x_2922_, v___x_2925_);
v___x_2927_ = lean_array_uget_borrowed(v_buckets_2913_, v___x_2926_);
v___x_2928_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__6_spec__9___redArg(v_a_2912_, v___x_2927_);
return v___x_2928_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__6___redArg___boxed(lean_object* v_m_2929_, lean_object* v_a_2930_){
_start:
{
lean_object* v_res_2931_; 
v_res_2931_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__6___redArg(v_m_2929_, v_a_2930_);
lean_dec_ref(v_a_2930_);
lean_dec_ref(v_m_2929_);
return v_res_2931_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__13___redArg(lean_object* v_a_2932_, lean_object* v_b_2933_, lean_object* v_x_2934_){
_start:
{
if (lean_obj_tag(v_x_2934_) == 0)
{
lean_dec(v_b_2933_);
lean_dec_ref(v_a_2932_);
return v_x_2934_;
}
else
{
lean_object* v_key_2935_; lean_object* v_value_2936_; lean_object* v_tail_2937_; lean_object* v___x_2939_; uint8_t v_isShared_2940_; uint8_t v_isSharedCheck_2949_; 
v_key_2935_ = lean_ctor_get(v_x_2934_, 0);
v_value_2936_ = lean_ctor_get(v_x_2934_, 1);
v_tail_2937_ = lean_ctor_get(v_x_2934_, 2);
v_isSharedCheck_2949_ = !lean_is_exclusive(v_x_2934_);
if (v_isSharedCheck_2949_ == 0)
{
v___x_2939_ = v_x_2934_;
v_isShared_2940_ = v_isSharedCheck_2949_;
goto v_resetjp_2938_;
}
else
{
lean_inc(v_tail_2937_);
lean_inc(v_value_2936_);
lean_inc(v_key_2935_);
lean_dec(v_x_2934_);
v___x_2939_ = lean_box(0);
v_isShared_2940_ = v_isSharedCheck_2949_;
goto v_resetjp_2938_;
}
v_resetjp_2938_:
{
uint8_t v___x_2941_; 
v___x_2941_ = lean_expr_eqv(v_key_2935_, v_a_2932_);
if (v___x_2941_ == 0)
{
lean_object* v___x_2942_; lean_object* v___x_2944_; 
v___x_2942_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__13___redArg(v_a_2932_, v_b_2933_, v_tail_2937_);
if (v_isShared_2940_ == 0)
{
lean_ctor_set(v___x_2939_, 2, v___x_2942_);
v___x_2944_ = v___x_2939_;
goto v_reusejp_2943_;
}
else
{
lean_object* v_reuseFailAlloc_2945_; 
v_reuseFailAlloc_2945_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2945_, 0, v_key_2935_);
lean_ctor_set(v_reuseFailAlloc_2945_, 1, v_value_2936_);
lean_ctor_set(v_reuseFailAlloc_2945_, 2, v___x_2942_);
v___x_2944_ = v_reuseFailAlloc_2945_;
goto v_reusejp_2943_;
}
v_reusejp_2943_:
{
return v___x_2944_;
}
}
else
{
lean_object* v___x_2947_; 
lean_dec(v_value_2936_);
lean_dec(v_key_2935_);
if (v_isShared_2940_ == 0)
{
lean_ctor_set(v___x_2939_, 1, v_b_2933_);
lean_ctor_set(v___x_2939_, 0, v_a_2932_);
v___x_2947_ = v___x_2939_;
goto v_reusejp_2946_;
}
else
{
lean_object* v_reuseFailAlloc_2948_; 
v_reuseFailAlloc_2948_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2948_, 0, v_a_2932_);
lean_ctor_set(v_reuseFailAlloc_2948_, 1, v_b_2933_);
lean_ctor_set(v_reuseFailAlloc_2948_, 2, v_tail_2937_);
v___x_2947_ = v_reuseFailAlloc_2948_;
goto v_reusejp_2946_;
}
v_reusejp_2946_:
{
return v___x_2947_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__12_spec__17_spec__18___redArg(lean_object* v_x_2950_, lean_object* v_x_2951_){
_start:
{
if (lean_obj_tag(v_x_2951_) == 0)
{
return v_x_2950_;
}
else
{
lean_object* v_key_2952_; lean_object* v_value_2953_; lean_object* v_tail_2954_; lean_object* v___x_2956_; uint8_t v_isShared_2957_; uint8_t v_isSharedCheck_2977_; 
v_key_2952_ = lean_ctor_get(v_x_2951_, 0);
v_value_2953_ = lean_ctor_get(v_x_2951_, 1);
v_tail_2954_ = lean_ctor_get(v_x_2951_, 2);
v_isSharedCheck_2977_ = !lean_is_exclusive(v_x_2951_);
if (v_isSharedCheck_2977_ == 0)
{
v___x_2956_ = v_x_2951_;
v_isShared_2957_ = v_isSharedCheck_2977_;
goto v_resetjp_2955_;
}
else
{
lean_inc(v_tail_2954_);
lean_inc(v_value_2953_);
lean_inc(v_key_2952_);
lean_dec(v_x_2951_);
v___x_2956_ = lean_box(0);
v_isShared_2957_ = v_isSharedCheck_2977_;
goto v_resetjp_2955_;
}
v_resetjp_2955_:
{
lean_object* v___x_2958_; uint64_t v___x_2959_; uint64_t v___x_2960_; uint64_t v___x_2961_; uint64_t v_fold_2962_; uint64_t v___x_2963_; uint64_t v___x_2964_; uint64_t v___x_2965_; size_t v___x_2966_; size_t v___x_2967_; size_t v___x_2968_; size_t v___x_2969_; size_t v___x_2970_; lean_object* v___x_2971_; lean_object* v___x_2973_; 
v___x_2958_ = lean_array_get_size(v_x_2950_);
v___x_2959_ = l_Lean_Expr_hash(v_key_2952_);
v___x_2960_ = 32ULL;
v___x_2961_ = lean_uint64_shift_right(v___x_2959_, v___x_2960_);
v_fold_2962_ = lean_uint64_xor(v___x_2959_, v___x_2961_);
v___x_2963_ = 16ULL;
v___x_2964_ = lean_uint64_shift_right(v_fold_2962_, v___x_2963_);
v___x_2965_ = lean_uint64_xor(v_fold_2962_, v___x_2964_);
v___x_2966_ = lean_uint64_to_usize(v___x_2965_);
v___x_2967_ = lean_usize_of_nat(v___x_2958_);
v___x_2968_ = ((size_t)1ULL);
v___x_2969_ = lean_usize_sub(v___x_2967_, v___x_2968_);
v___x_2970_ = lean_usize_land(v___x_2966_, v___x_2969_);
v___x_2971_ = lean_array_uget_borrowed(v_x_2950_, v___x_2970_);
lean_inc(v___x_2971_);
if (v_isShared_2957_ == 0)
{
lean_ctor_set(v___x_2956_, 2, v___x_2971_);
v___x_2973_ = v___x_2956_;
goto v_reusejp_2972_;
}
else
{
lean_object* v_reuseFailAlloc_2976_; 
v_reuseFailAlloc_2976_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2976_, 0, v_key_2952_);
lean_ctor_set(v_reuseFailAlloc_2976_, 1, v_value_2953_);
lean_ctor_set(v_reuseFailAlloc_2976_, 2, v___x_2971_);
v___x_2973_ = v_reuseFailAlloc_2976_;
goto v_reusejp_2972_;
}
v_reusejp_2972_:
{
lean_object* v___x_2974_; 
v___x_2974_ = lean_array_uset(v_x_2950_, v___x_2970_, v___x_2973_);
v_x_2950_ = v___x_2974_;
v_x_2951_ = v_tail_2954_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__12_spec__17___redArg(lean_object* v_i_2978_, lean_object* v_source_2979_, lean_object* v_target_2980_){
_start:
{
lean_object* v___x_2981_; uint8_t v___x_2982_; 
v___x_2981_ = lean_array_get_size(v_source_2979_);
v___x_2982_ = lean_nat_dec_lt(v_i_2978_, v___x_2981_);
if (v___x_2982_ == 0)
{
lean_dec_ref(v_source_2979_);
lean_dec(v_i_2978_);
return v_target_2980_;
}
else
{
lean_object* v_es_2983_; lean_object* v___x_2984_; lean_object* v_source_2985_; lean_object* v_target_2986_; lean_object* v___x_2987_; lean_object* v___x_2988_; 
v_es_2983_ = lean_array_fget(v_source_2979_, v_i_2978_);
v___x_2984_ = lean_box(0);
v_source_2985_ = lean_array_fset(v_source_2979_, v_i_2978_, v___x_2984_);
v_target_2986_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__12_spec__17_spec__18___redArg(v_target_2980_, v_es_2983_);
v___x_2987_ = lean_unsigned_to_nat(1u);
v___x_2988_ = lean_nat_add(v_i_2978_, v___x_2987_);
lean_dec(v_i_2978_);
v_i_2978_ = v___x_2988_;
v_source_2979_ = v_source_2985_;
v_target_2980_ = v_target_2986_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__12___redArg(lean_object* v_data_2990_){
_start:
{
lean_object* v___x_2991_; lean_object* v___x_2992_; lean_object* v_nbuckets_2993_; lean_object* v___x_2994_; lean_object* v___x_2995_; lean_object* v___x_2996_; lean_object* v___x_2997_; 
v___x_2991_ = lean_array_get_size(v_data_2990_);
v___x_2992_ = lean_unsigned_to_nat(2u);
v_nbuckets_2993_ = lean_nat_mul(v___x_2991_, v___x_2992_);
v___x_2994_ = lean_unsigned_to_nat(0u);
v___x_2995_ = lean_box(0);
v___x_2996_ = lean_mk_array(v_nbuckets_2993_, v___x_2995_);
v___x_2997_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__12_spec__17___redArg(v___x_2994_, v_data_2990_, v___x_2996_);
return v___x_2997_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__11___redArg(lean_object* v_a_2998_, lean_object* v_x_2999_){
_start:
{
if (lean_obj_tag(v_x_2999_) == 0)
{
uint8_t v___x_3000_; 
v___x_3000_ = 0;
return v___x_3000_;
}
else
{
lean_object* v_key_3001_; lean_object* v_tail_3002_; uint8_t v___x_3003_; 
v_key_3001_ = lean_ctor_get(v_x_2999_, 0);
v_tail_3002_ = lean_ctor_get(v_x_2999_, 2);
v___x_3003_ = lean_expr_eqv(v_key_3001_, v_a_2998_);
if (v___x_3003_ == 0)
{
v_x_2999_ = v_tail_3002_;
goto _start;
}
else
{
return v___x_3003_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__11___redArg___boxed(lean_object* v_a_3005_, lean_object* v_x_3006_){
_start:
{
uint8_t v_res_3007_; lean_object* v_r_3008_; 
v_res_3007_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__11___redArg(v_a_3005_, v_x_3006_);
lean_dec(v_x_3006_);
lean_dec_ref(v_a_3005_);
v_r_3008_ = lean_box(v_res_3007_);
return v_r_3008_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7___redArg(lean_object* v_m_3009_, lean_object* v_a_3010_, lean_object* v_b_3011_){
_start:
{
lean_object* v_size_3012_; lean_object* v_buckets_3013_; lean_object* v___x_3015_; uint8_t v_isShared_3016_; uint8_t v_isSharedCheck_3056_; 
v_size_3012_ = lean_ctor_get(v_m_3009_, 0);
v_buckets_3013_ = lean_ctor_get(v_m_3009_, 1);
v_isSharedCheck_3056_ = !lean_is_exclusive(v_m_3009_);
if (v_isSharedCheck_3056_ == 0)
{
v___x_3015_ = v_m_3009_;
v_isShared_3016_ = v_isSharedCheck_3056_;
goto v_resetjp_3014_;
}
else
{
lean_inc(v_buckets_3013_);
lean_inc(v_size_3012_);
lean_dec(v_m_3009_);
v___x_3015_ = lean_box(0);
v_isShared_3016_ = v_isSharedCheck_3056_;
goto v_resetjp_3014_;
}
v_resetjp_3014_:
{
lean_object* v___x_3017_; uint64_t v___x_3018_; uint64_t v___x_3019_; uint64_t v___x_3020_; uint64_t v_fold_3021_; uint64_t v___x_3022_; uint64_t v___x_3023_; uint64_t v___x_3024_; size_t v___x_3025_; size_t v___x_3026_; size_t v___x_3027_; size_t v___x_3028_; size_t v___x_3029_; lean_object* v_bkt_3030_; uint8_t v___x_3031_; 
v___x_3017_ = lean_array_get_size(v_buckets_3013_);
v___x_3018_ = l_Lean_Expr_hash(v_a_3010_);
v___x_3019_ = 32ULL;
v___x_3020_ = lean_uint64_shift_right(v___x_3018_, v___x_3019_);
v_fold_3021_ = lean_uint64_xor(v___x_3018_, v___x_3020_);
v___x_3022_ = 16ULL;
v___x_3023_ = lean_uint64_shift_right(v_fold_3021_, v___x_3022_);
v___x_3024_ = lean_uint64_xor(v_fold_3021_, v___x_3023_);
v___x_3025_ = lean_uint64_to_usize(v___x_3024_);
v___x_3026_ = lean_usize_of_nat(v___x_3017_);
v___x_3027_ = ((size_t)1ULL);
v___x_3028_ = lean_usize_sub(v___x_3026_, v___x_3027_);
v___x_3029_ = lean_usize_land(v___x_3025_, v___x_3028_);
v_bkt_3030_ = lean_array_uget_borrowed(v_buckets_3013_, v___x_3029_);
v___x_3031_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__11___redArg(v_a_3010_, v_bkt_3030_);
if (v___x_3031_ == 0)
{
lean_object* v___x_3032_; lean_object* v_size_x27_3033_; lean_object* v___x_3034_; lean_object* v_buckets_x27_3035_; lean_object* v___x_3036_; lean_object* v___x_3037_; lean_object* v___x_3038_; lean_object* v___x_3039_; lean_object* v___x_3040_; uint8_t v___x_3041_; 
v___x_3032_ = lean_unsigned_to_nat(1u);
v_size_x27_3033_ = lean_nat_add(v_size_3012_, v___x_3032_);
lean_dec(v_size_3012_);
lean_inc(v_bkt_3030_);
v___x_3034_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3034_, 0, v_a_3010_);
lean_ctor_set(v___x_3034_, 1, v_b_3011_);
lean_ctor_set(v___x_3034_, 2, v_bkt_3030_);
v_buckets_x27_3035_ = lean_array_uset(v_buckets_3013_, v___x_3029_, v___x_3034_);
v___x_3036_ = lean_unsigned_to_nat(4u);
v___x_3037_ = lean_nat_mul(v_size_x27_3033_, v___x_3036_);
v___x_3038_ = lean_unsigned_to_nat(3u);
v___x_3039_ = lean_nat_div(v___x_3037_, v___x_3038_);
lean_dec(v___x_3037_);
v___x_3040_ = lean_array_get_size(v_buckets_x27_3035_);
v___x_3041_ = lean_nat_dec_le(v___x_3039_, v___x_3040_);
lean_dec(v___x_3039_);
if (v___x_3041_ == 0)
{
lean_object* v_val_3042_; lean_object* v___x_3044_; 
v_val_3042_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__12___redArg(v_buckets_x27_3035_);
if (v_isShared_3016_ == 0)
{
lean_ctor_set(v___x_3015_, 1, v_val_3042_);
lean_ctor_set(v___x_3015_, 0, v_size_x27_3033_);
v___x_3044_ = v___x_3015_;
goto v_reusejp_3043_;
}
else
{
lean_object* v_reuseFailAlloc_3045_; 
v_reuseFailAlloc_3045_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3045_, 0, v_size_x27_3033_);
lean_ctor_set(v_reuseFailAlloc_3045_, 1, v_val_3042_);
v___x_3044_ = v_reuseFailAlloc_3045_;
goto v_reusejp_3043_;
}
v_reusejp_3043_:
{
return v___x_3044_;
}
}
else
{
lean_object* v___x_3047_; 
if (v_isShared_3016_ == 0)
{
lean_ctor_set(v___x_3015_, 1, v_buckets_x27_3035_);
lean_ctor_set(v___x_3015_, 0, v_size_x27_3033_);
v___x_3047_ = v___x_3015_;
goto v_reusejp_3046_;
}
else
{
lean_object* v_reuseFailAlloc_3048_; 
v_reuseFailAlloc_3048_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3048_, 0, v_size_x27_3033_);
lean_ctor_set(v_reuseFailAlloc_3048_, 1, v_buckets_x27_3035_);
v___x_3047_ = v_reuseFailAlloc_3048_;
goto v_reusejp_3046_;
}
v_reusejp_3046_:
{
return v___x_3047_;
}
}
}
else
{
lean_object* v___x_3049_; lean_object* v_buckets_x27_3050_; lean_object* v___x_3051_; lean_object* v___x_3052_; lean_object* v___x_3054_; 
lean_inc(v_bkt_3030_);
v___x_3049_ = lean_box(0);
v_buckets_x27_3050_ = lean_array_uset(v_buckets_3013_, v___x_3029_, v___x_3049_);
v___x_3051_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__13___redArg(v_a_3010_, v_b_3011_, v_bkt_3030_);
v___x_3052_ = lean_array_uset(v_buckets_x27_3050_, v___x_3029_, v___x_3051_);
if (v_isShared_3016_ == 0)
{
lean_ctor_set(v___x_3015_, 1, v___x_3052_);
v___x_3054_ = v___x_3015_;
goto v_reusejp_3053_;
}
else
{
lean_object* v_reuseFailAlloc_3055_; 
v_reuseFailAlloc_3055_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3055_, 0, v_size_3012_);
lean_ctor_set(v_reuseFailAlloc_3055_, 1, v___x_3052_);
v___x_3054_ = v_reuseFailAlloc_3055_;
goto v_reusejp_3053_;
}
v_reusejp_3053_:
{
return v___x_3054_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3(lean_object* v_g_3057_, lean_object* v_e_3058_, lean_object* v_a_3059_, lean_object* v___y_3060_, lean_object* v___y_3061_, lean_object* v___y_3062_){
_start:
{
lean_object* v_a_3065_; lean_object* v_fst_3066_; lean_object* v___y_3072_; lean_object* v___x_3075_; lean_object* v___x_3076_; 
v___x_3075_ = lean_st_ref_get(v_a_3059_);
v___x_3076_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__6___redArg(v___x_3075_, v_e_3058_);
lean_dec(v___x_3075_);
if (lean_obj_tag(v___x_3076_) == 0)
{
lean_object* v___x_3077_; 
lean_inc_ref(v_g_3057_);
lean_inc(v___y_3062_);
lean_inc_ref(v___y_3061_);
lean_inc_ref(v_e_3058_);
v___x_3077_ = lean_apply_5(v_g_3057_, v_e_3058_, v___y_3060_, v___y_3061_, v___y_3062_, lean_box(0));
if (lean_obj_tag(v___x_3077_) == 0)
{
lean_object* v_a_3078_; lean_object* v_fst_3079_; lean_object* v_snd_3080_; lean_object* v___x_3082_; uint8_t v_isShared_3083_; uint8_t v_isSharedCheck_3125_; 
v_a_3078_ = lean_ctor_get(v___x_3077_, 0);
lean_inc(v_a_3078_);
lean_dec_ref(v___x_3077_);
v_fst_3079_ = lean_ctor_get(v_a_3078_, 0);
v_snd_3080_ = lean_ctor_get(v_a_3078_, 1);
v_isSharedCheck_3125_ = !lean_is_exclusive(v_a_3078_);
if (v_isSharedCheck_3125_ == 0)
{
v___x_3082_ = v_a_3078_;
v_isShared_3083_ = v_isSharedCheck_3125_;
goto v_resetjp_3081_;
}
else
{
lean_inc(v_snd_3080_);
lean_inc(v_fst_3079_);
lean_dec(v_a_3078_);
v___x_3082_ = lean_box(0);
v_isShared_3083_ = v_isSharedCheck_3125_;
goto v_resetjp_3081_;
}
v_resetjp_3081_:
{
lean_object* v_d_3085_; lean_object* v_b_3086_; lean_object* v___y_3087_; uint8_t v___x_3092_; 
v___x_3092_ = lean_unbox(v_fst_3079_);
lean_dec(v_fst_3079_);
if (v___x_3092_ == 0)
{
lean_object* v___x_3093_; lean_object* v___x_3095_; 
lean_dec_ref(v_g_3057_);
v___x_3093_ = lean_box(0);
if (v_isShared_3083_ == 0)
{
lean_ctor_set(v___x_3082_, 0, v___x_3093_);
v___x_3095_ = v___x_3082_;
goto v_reusejp_3094_;
}
else
{
lean_object* v_reuseFailAlloc_3096_; 
v_reuseFailAlloc_3096_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3096_, 0, v___x_3093_);
lean_ctor_set(v_reuseFailAlloc_3096_, 1, v_snd_3080_);
v___x_3095_ = v_reuseFailAlloc_3096_;
goto v_reusejp_3094_;
}
v_reusejp_3094_:
{
v_a_3065_ = v___x_3095_;
v_fst_3066_ = v___x_3093_;
goto v___jp_3064_;
}
}
else
{
switch(lean_obj_tag(v_e_3058_))
{
case 7:
{
lean_object* v_binderType_3097_; lean_object* v_body_3098_; 
lean_del_object(v___x_3082_);
v_binderType_3097_ = lean_ctor_get(v_e_3058_, 1);
v_body_3098_ = lean_ctor_get(v_e_3058_, 2);
lean_inc_ref(v_body_3098_);
lean_inc_ref(v_binderType_3097_);
v_d_3085_ = v_binderType_3097_;
v_b_3086_ = v_body_3098_;
v___y_3087_ = v_a_3059_;
goto v___jp_3084_;
}
case 6:
{
lean_object* v_binderType_3099_; lean_object* v_body_3100_; 
lean_del_object(v___x_3082_);
v_binderType_3099_ = lean_ctor_get(v_e_3058_, 1);
v_body_3100_ = lean_ctor_get(v_e_3058_, 2);
lean_inc_ref(v_body_3100_);
lean_inc_ref(v_binderType_3099_);
v_d_3085_ = v_binderType_3099_;
v_b_3086_ = v_body_3100_;
v___y_3087_ = v_a_3059_;
goto v___jp_3084_;
}
case 8:
{
lean_object* v_type_3101_; lean_object* v_value_3102_; lean_object* v_body_3103_; lean_object* v___x_3104_; 
lean_del_object(v___x_3082_);
v_type_3101_ = lean_ctor_get(v_e_3058_, 1);
v_value_3102_ = lean_ctor_get(v_e_3058_, 2);
v_body_3103_ = lean_ctor_get(v_e_3058_, 3);
lean_inc_ref(v_type_3101_);
lean_inc_ref(v_g_3057_);
v___x_3104_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3(v_g_3057_, v_type_3101_, v_a_3059_, v_snd_3080_, v___y_3061_, v___y_3062_);
if (lean_obj_tag(v___x_3104_) == 0)
{
lean_object* v_a_3105_; lean_object* v_snd_3106_; lean_object* v___x_3107_; 
v_a_3105_ = lean_ctor_get(v___x_3104_, 0);
lean_inc(v_a_3105_);
lean_dec_ref(v___x_3104_);
v_snd_3106_ = lean_ctor_get(v_a_3105_, 1);
lean_inc(v_snd_3106_);
lean_dec(v_a_3105_);
lean_inc_ref(v_value_3102_);
lean_inc_ref(v_g_3057_);
v___x_3107_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3(v_g_3057_, v_value_3102_, v_a_3059_, v_snd_3106_, v___y_3061_, v___y_3062_);
if (lean_obj_tag(v___x_3107_) == 0)
{
lean_object* v_a_3108_; lean_object* v_snd_3109_; lean_object* v___x_3110_; 
v_a_3108_ = lean_ctor_get(v___x_3107_, 0);
lean_inc(v_a_3108_);
lean_dec_ref(v___x_3107_);
v_snd_3109_ = lean_ctor_get(v_a_3108_, 1);
lean_inc(v_snd_3109_);
lean_dec(v_a_3108_);
lean_inc_ref(v_body_3103_);
v___x_3110_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3(v_g_3057_, v_body_3103_, v_a_3059_, v_snd_3109_, v___y_3061_, v___y_3062_);
v___y_3072_ = v___x_3110_;
goto v___jp_3071_;
}
else
{
lean_dec_ref(v_g_3057_);
v___y_3072_ = v___x_3107_;
goto v___jp_3071_;
}
}
else
{
lean_dec_ref(v_g_3057_);
v___y_3072_ = v___x_3104_;
goto v___jp_3071_;
}
}
case 5:
{
lean_object* v_fn_3111_; lean_object* v_arg_3112_; lean_object* v___x_3113_; 
lean_del_object(v___x_3082_);
v_fn_3111_ = lean_ctor_get(v_e_3058_, 0);
v_arg_3112_ = lean_ctor_get(v_e_3058_, 1);
lean_inc_ref(v_fn_3111_);
lean_inc_ref(v_g_3057_);
v___x_3113_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3(v_g_3057_, v_fn_3111_, v_a_3059_, v_snd_3080_, v___y_3061_, v___y_3062_);
if (lean_obj_tag(v___x_3113_) == 0)
{
lean_object* v_a_3114_; lean_object* v_snd_3115_; lean_object* v___x_3116_; 
v_a_3114_ = lean_ctor_get(v___x_3113_, 0);
lean_inc(v_a_3114_);
lean_dec_ref(v___x_3113_);
v_snd_3115_ = lean_ctor_get(v_a_3114_, 1);
lean_inc(v_snd_3115_);
lean_dec(v_a_3114_);
lean_inc_ref(v_arg_3112_);
v___x_3116_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3(v_g_3057_, v_arg_3112_, v_a_3059_, v_snd_3115_, v___y_3061_, v___y_3062_);
v___y_3072_ = v___x_3116_;
goto v___jp_3071_;
}
else
{
lean_dec_ref(v_g_3057_);
v___y_3072_ = v___x_3113_;
goto v___jp_3071_;
}
}
case 10:
{
lean_object* v_expr_3117_; lean_object* v___x_3118_; 
lean_del_object(v___x_3082_);
v_expr_3117_ = lean_ctor_get(v_e_3058_, 1);
lean_inc_ref(v_expr_3117_);
v___x_3118_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3(v_g_3057_, v_expr_3117_, v_a_3059_, v_snd_3080_, v___y_3061_, v___y_3062_);
v___y_3072_ = v___x_3118_;
goto v___jp_3071_;
}
case 11:
{
lean_object* v_struct_3119_; lean_object* v___x_3120_; 
lean_del_object(v___x_3082_);
v_struct_3119_ = lean_ctor_get(v_e_3058_, 2);
lean_inc_ref(v_struct_3119_);
v___x_3120_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3(v_g_3057_, v_struct_3119_, v_a_3059_, v_snd_3080_, v___y_3061_, v___y_3062_);
v___y_3072_ = v___x_3120_;
goto v___jp_3071_;
}
default: 
{
lean_object* v___x_3121_; lean_object* v___x_3123_; 
lean_dec_ref(v_g_3057_);
v___x_3121_ = lean_box(0);
if (v_isShared_3083_ == 0)
{
lean_ctor_set(v___x_3082_, 0, v___x_3121_);
v___x_3123_ = v___x_3082_;
goto v_reusejp_3122_;
}
else
{
lean_object* v_reuseFailAlloc_3124_; 
v_reuseFailAlloc_3124_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3124_, 0, v___x_3121_);
lean_ctor_set(v_reuseFailAlloc_3124_, 1, v_snd_3080_);
v___x_3123_ = v_reuseFailAlloc_3124_;
goto v_reusejp_3122_;
}
v_reusejp_3122_:
{
v_a_3065_ = v___x_3123_;
v_fst_3066_ = v___x_3121_;
goto v___jp_3064_;
}
}
}
}
v___jp_3084_:
{
lean_object* v___x_3088_; 
lean_inc_ref(v_g_3057_);
v___x_3088_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3(v_g_3057_, v_d_3085_, v___y_3087_, v_snd_3080_, v___y_3061_, v___y_3062_);
if (lean_obj_tag(v___x_3088_) == 0)
{
lean_object* v_a_3089_; lean_object* v_snd_3090_; lean_object* v___x_3091_; 
v_a_3089_ = lean_ctor_get(v___x_3088_, 0);
lean_inc(v_a_3089_);
lean_dec_ref(v___x_3088_);
v_snd_3090_ = lean_ctor_get(v_a_3089_, 1);
lean_inc(v_snd_3090_);
lean_dec(v_a_3089_);
v___x_3091_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3(v_g_3057_, v_b_3086_, v___y_3087_, v_snd_3090_, v___y_3061_, v___y_3062_);
v___y_3072_ = v___x_3091_;
goto v___jp_3071_;
}
else
{
lean_dec_ref(v_b_3086_);
lean_dec_ref(v_g_3057_);
v___y_3072_ = v___x_3088_;
goto v___jp_3071_;
}
}
}
}
else
{
lean_object* v_a_3126_; lean_object* v___x_3128_; uint8_t v_isShared_3129_; uint8_t v_isSharedCheck_3133_; 
lean_dec_ref(v_e_3058_);
lean_dec_ref(v_g_3057_);
v_a_3126_ = lean_ctor_get(v___x_3077_, 0);
v_isSharedCheck_3133_ = !lean_is_exclusive(v___x_3077_);
if (v_isSharedCheck_3133_ == 0)
{
v___x_3128_ = v___x_3077_;
v_isShared_3129_ = v_isSharedCheck_3133_;
goto v_resetjp_3127_;
}
else
{
lean_inc(v_a_3126_);
lean_dec(v___x_3077_);
v___x_3128_ = lean_box(0);
v_isShared_3129_ = v_isSharedCheck_3133_;
goto v_resetjp_3127_;
}
v_resetjp_3127_:
{
lean_object* v___x_3131_; 
if (v_isShared_3129_ == 0)
{
v___x_3131_ = v___x_3128_;
goto v_reusejp_3130_;
}
else
{
lean_object* v_reuseFailAlloc_3132_; 
v_reuseFailAlloc_3132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3132_, 0, v_a_3126_);
v___x_3131_ = v_reuseFailAlloc_3132_;
goto v_reusejp_3130_;
}
v_reusejp_3130_:
{
return v___x_3131_;
}
}
}
}
else
{
lean_object* v_val_3134_; lean_object* v___x_3136_; uint8_t v_isShared_3137_; uint8_t v_isSharedCheck_3142_; 
lean_dec_ref(v_e_3058_);
lean_dec_ref(v_g_3057_);
v_val_3134_ = lean_ctor_get(v___x_3076_, 0);
v_isSharedCheck_3142_ = !lean_is_exclusive(v___x_3076_);
if (v_isSharedCheck_3142_ == 0)
{
v___x_3136_ = v___x_3076_;
v_isShared_3137_ = v_isSharedCheck_3142_;
goto v_resetjp_3135_;
}
else
{
lean_inc(v_val_3134_);
lean_dec(v___x_3076_);
v___x_3136_ = lean_box(0);
v_isShared_3137_ = v_isSharedCheck_3142_;
goto v_resetjp_3135_;
}
v_resetjp_3135_:
{
lean_object* v___x_3138_; lean_object* v___x_3140_; 
v___x_3138_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3138_, 0, v_val_3134_);
lean_ctor_set(v___x_3138_, 1, v___y_3060_);
if (v_isShared_3137_ == 0)
{
lean_ctor_set_tag(v___x_3136_, 0);
lean_ctor_set(v___x_3136_, 0, v___x_3138_);
v___x_3140_ = v___x_3136_;
goto v_reusejp_3139_;
}
else
{
lean_object* v_reuseFailAlloc_3141_; 
v_reuseFailAlloc_3141_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3141_, 0, v___x_3138_);
v___x_3140_ = v_reuseFailAlloc_3141_;
goto v_reusejp_3139_;
}
v_reusejp_3139_:
{
return v___x_3140_;
}
}
}
v___jp_3064_:
{
lean_object* v___x_3067_; lean_object* v___x_3068_; lean_object* v___x_3069_; lean_object* v___x_3070_; 
v___x_3067_ = lean_st_ref_take(v_a_3059_);
v___x_3068_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7___redArg(v___x_3067_, v_e_3058_, v_fst_3066_);
v___x_3069_ = lean_st_ref_set(v_a_3059_, v___x_3068_);
v___x_3070_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3070_, 0, v_a_3065_);
return v___x_3070_;
}
v___jp_3071_:
{
if (lean_obj_tag(v___y_3072_) == 0)
{
lean_object* v_a_3073_; lean_object* v_fst_3074_; 
v_a_3073_ = lean_ctor_get(v___y_3072_, 0);
lean_inc(v_a_3073_);
lean_dec_ref(v___y_3072_);
v_fst_3074_ = lean_ctor_get(v_a_3073_, 0);
lean_inc(v_fst_3074_);
v_a_3065_ = v_a_3073_;
v_fst_3066_ = v_fst_3074_;
goto v___jp_3064_;
}
else
{
lean_dec_ref(v_e_3058_);
return v___y_3072_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3___boxed(lean_object* v_g_3143_, lean_object* v_e_3144_, lean_object* v_a_3145_, lean_object* v___y_3146_, lean_object* v___y_3147_, lean_object* v___y_3148_, lean_object* v___y_3149_){
_start:
{
lean_object* v_res_3150_; 
v_res_3150_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3(v_g_3143_, v_e_3144_, v_a_3145_, v___y_3146_, v___y_3147_, v___y_3148_);
lean_dec(v___y_3148_);
lean_dec_ref(v___y_3147_);
lean_dec(v_a_3145_);
return v_res_3150_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__0(void){
_start:
{
lean_object* v___x_3151_; 
v___x_3151_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_3151_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__1(void){
_start:
{
lean_object* v___x_3152_; lean_object* v___x_3153_; 
v___x_3152_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__0);
v___x_3153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3153_, 0, v___x_3152_);
return v___x_3153_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__2(void){
_start:
{
lean_object* v___x_3154_; lean_object* v___x_3155_; lean_object* v___x_3156_; 
v___x_3154_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__1);
v___x_3155_ = lean_unsigned_to_nat(0u);
v___x_3156_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_3156_, 0, v___x_3155_);
lean_ctor_set(v___x_3156_, 1, v___x_3155_);
lean_ctor_set(v___x_3156_, 2, v___x_3155_);
lean_ctor_set(v___x_3156_, 3, v___x_3155_);
lean_ctor_set(v___x_3156_, 4, v___x_3154_);
lean_ctor_set(v___x_3156_, 5, v___x_3154_);
lean_ctor_set(v___x_3156_, 6, v___x_3154_);
lean_ctor_set(v___x_3156_, 7, v___x_3154_);
lean_ctor_set(v___x_3156_, 8, v___x_3154_);
lean_ctor_set(v___x_3156_, 9, v___x_3154_);
return v___x_3156_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__3(void){
_start:
{
lean_object* v___x_3157_; lean_object* v___x_3158_; lean_object* v___x_3159_; 
v___x_3157_ = lean_unsigned_to_nat(32u);
v___x_3158_ = lean_mk_empty_array_with_capacity(v___x_3157_);
v___x_3159_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3159_, 0, v___x_3158_);
return v___x_3159_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__4(void){
_start:
{
size_t v___x_3160_; lean_object* v___x_3161_; lean_object* v___x_3162_; lean_object* v___x_3163_; lean_object* v___x_3164_; lean_object* v___x_3165_; 
v___x_3160_ = ((size_t)5ULL);
v___x_3161_ = lean_unsigned_to_nat(0u);
v___x_3162_ = lean_unsigned_to_nat(32u);
v___x_3163_ = lean_mk_empty_array_with_capacity(v___x_3162_);
v___x_3164_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__3);
v___x_3165_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3165_, 0, v___x_3164_);
lean_ctor_set(v___x_3165_, 1, v___x_3163_);
lean_ctor_set(v___x_3165_, 2, v___x_3161_);
lean_ctor_set(v___x_3165_, 3, v___x_3161_);
lean_ctor_set_usize(v___x_3165_, 4, v___x_3160_);
return v___x_3165_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__5(void){
_start:
{
lean_object* v___x_3166_; lean_object* v___x_3167_; lean_object* v___x_3168_; lean_object* v___x_3169_; 
v___x_3166_ = lean_box(1);
v___x_3167_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__4);
v___x_3168_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__1);
v___x_3169_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3169_, 0, v___x_3168_);
lean_ctor_set(v___x_3169_, 1, v___x_3167_);
lean_ctor_set(v___x_3169_, 2, v___x_3166_);
return v___x_3169_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10(lean_object* v_msgData_3170_, lean_object* v___y_3171_, lean_object* v___y_3172_){
_start:
{
lean_object* v___x_3174_; lean_object* v_env_3175_; lean_object* v_options_3176_; lean_object* v___x_3177_; lean_object* v___x_3178_; lean_object* v___x_3179_; lean_object* v___x_3180_; lean_object* v___x_3181_; 
v___x_3174_ = lean_st_ref_get(v___y_3172_);
v_env_3175_ = lean_ctor_get(v___x_3174_, 0);
lean_inc_ref(v_env_3175_);
lean_dec(v___x_3174_);
v_options_3176_ = lean_ctor_get(v___y_3171_, 2);
v___x_3177_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__2);
v___x_3178_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__5);
lean_inc_ref(v_options_3176_);
v___x_3179_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3179_, 0, v_env_3175_);
lean_ctor_set(v___x_3179_, 1, v___x_3177_);
lean_ctor_set(v___x_3179_, 2, v___x_3178_);
lean_ctor_set(v___x_3179_, 3, v_options_3176_);
v___x_3180_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_3180_, 0, v___x_3179_);
lean_ctor_set(v___x_3180_, 1, v_msgData_3170_);
v___x_3181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3181_, 0, v___x_3180_);
return v___x_3181_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___boxed(lean_object* v_msgData_3182_, lean_object* v___y_3183_, lean_object* v___y_3184_, lean_object* v___y_3185_){
_start:
{
lean_object* v_res_3186_; 
v_res_3186_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10(v_msgData_3182_, v___y_3183_, v___y_3184_);
lean_dec(v___y_3184_);
lean_dec_ref(v___y_3183_);
return v_res_3186_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5___redArg(lean_object* v_msg_3187_, lean_object* v___y_3188_, lean_object* v___y_3189_){
_start:
{
lean_object* v_ref_3191_; lean_object* v___x_3192_; lean_object* v_a_3193_; lean_object* v___x_3195_; uint8_t v_isShared_3196_; uint8_t v_isSharedCheck_3201_; 
v_ref_3191_ = lean_ctor_get(v___y_3188_, 5);
v___x_3192_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10(v_msg_3187_, v___y_3188_, v___y_3189_);
v_a_3193_ = lean_ctor_get(v___x_3192_, 0);
v_isSharedCheck_3201_ = !lean_is_exclusive(v___x_3192_);
if (v_isSharedCheck_3201_ == 0)
{
v___x_3195_ = v___x_3192_;
v_isShared_3196_ = v_isSharedCheck_3201_;
goto v_resetjp_3194_;
}
else
{
lean_inc(v_a_3193_);
lean_dec(v___x_3192_);
v___x_3195_ = lean_box(0);
v_isShared_3196_ = v_isSharedCheck_3201_;
goto v_resetjp_3194_;
}
v_resetjp_3194_:
{
lean_object* v___x_3197_; lean_object* v___x_3199_; 
lean_inc(v_ref_3191_);
v___x_3197_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3197_, 0, v_ref_3191_);
lean_ctor_set(v___x_3197_, 1, v_a_3193_);
if (v_isShared_3196_ == 0)
{
lean_ctor_set_tag(v___x_3195_, 1);
lean_ctor_set(v___x_3195_, 0, v___x_3197_);
v___x_3199_ = v___x_3195_;
goto v_reusejp_3198_;
}
else
{
lean_object* v_reuseFailAlloc_3200_; 
v_reuseFailAlloc_3200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3200_, 0, v___x_3197_);
v___x_3199_ = v_reuseFailAlloc_3200_;
goto v_reusejp_3198_;
}
v_reusejp_3198_:
{
return v___x_3199_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5___redArg___boxed(lean_object* v_msg_3202_, lean_object* v___y_3203_, lean_object* v___y_3204_, lean_object* v___y_3205_){
_start:
{
lean_object* v_res_3206_; 
v_res_3206_ = l_Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5___redArg(v_msg_3202_, v___y_3203_, v___y_3204_);
lean_dec(v___y_3204_);
lean_dec_ref(v___y_3203_);
return v_res_3206_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6___closed__0(void){
_start:
{
lean_object* v___x_3207_; double v___x_3208_; 
v___x_3207_ = lean_unsigned_to_nat(0u);
v___x_3208_ = lean_float_of_nat(v___x_3207_);
return v___x_3208_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6(lean_object* v_cls_3212_, lean_object* v_msg_3213_, lean_object* v___y_3214_, lean_object* v___y_3215_, lean_object* v___y_3216_){
_start:
{
lean_object* v_ref_3218_; lean_object* v___x_3219_; lean_object* v_a_3220_; lean_object* v___x_3222_; uint8_t v_isShared_3223_; uint8_t v_isSharedCheck_3265_; 
v_ref_3218_ = lean_ctor_get(v___y_3215_, 5);
v___x_3219_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10(v_msg_3213_, v___y_3215_, v___y_3216_);
v_a_3220_ = lean_ctor_get(v___x_3219_, 0);
v_isSharedCheck_3265_ = !lean_is_exclusive(v___x_3219_);
if (v_isSharedCheck_3265_ == 0)
{
v___x_3222_ = v___x_3219_;
v_isShared_3223_ = v_isSharedCheck_3265_;
goto v_resetjp_3221_;
}
else
{
lean_inc(v_a_3220_);
lean_dec(v___x_3219_);
v___x_3222_ = lean_box(0);
v_isShared_3223_ = v_isSharedCheck_3265_;
goto v_resetjp_3221_;
}
v_resetjp_3221_:
{
lean_object* v___x_3224_; lean_object* v_traceState_3225_; lean_object* v_env_3226_; lean_object* v_nextMacroScope_3227_; lean_object* v_ngen_3228_; lean_object* v_auxDeclNGen_3229_; lean_object* v_cache_3230_; lean_object* v_messages_3231_; lean_object* v_infoState_3232_; lean_object* v_snapshotTasks_3233_; lean_object* v___x_3235_; uint8_t v_isShared_3236_; uint8_t v_isSharedCheck_3264_; 
v___x_3224_ = lean_st_ref_take(v___y_3216_);
v_traceState_3225_ = lean_ctor_get(v___x_3224_, 4);
v_env_3226_ = lean_ctor_get(v___x_3224_, 0);
v_nextMacroScope_3227_ = lean_ctor_get(v___x_3224_, 1);
v_ngen_3228_ = lean_ctor_get(v___x_3224_, 2);
v_auxDeclNGen_3229_ = lean_ctor_get(v___x_3224_, 3);
v_cache_3230_ = lean_ctor_get(v___x_3224_, 5);
v_messages_3231_ = lean_ctor_get(v___x_3224_, 6);
v_infoState_3232_ = lean_ctor_get(v___x_3224_, 7);
v_snapshotTasks_3233_ = lean_ctor_get(v___x_3224_, 8);
v_isSharedCheck_3264_ = !lean_is_exclusive(v___x_3224_);
if (v_isSharedCheck_3264_ == 0)
{
v___x_3235_ = v___x_3224_;
v_isShared_3236_ = v_isSharedCheck_3264_;
goto v_resetjp_3234_;
}
else
{
lean_inc(v_snapshotTasks_3233_);
lean_inc(v_infoState_3232_);
lean_inc(v_messages_3231_);
lean_inc(v_cache_3230_);
lean_inc(v_traceState_3225_);
lean_inc(v_auxDeclNGen_3229_);
lean_inc(v_ngen_3228_);
lean_inc(v_nextMacroScope_3227_);
lean_inc(v_env_3226_);
lean_dec(v___x_3224_);
v___x_3235_ = lean_box(0);
v_isShared_3236_ = v_isSharedCheck_3264_;
goto v_resetjp_3234_;
}
v_resetjp_3234_:
{
uint64_t v_tid_3237_; lean_object* v_traces_3238_; lean_object* v___x_3240_; uint8_t v_isShared_3241_; uint8_t v_isSharedCheck_3263_; 
v_tid_3237_ = lean_ctor_get_uint64(v_traceState_3225_, sizeof(void*)*1);
v_traces_3238_ = lean_ctor_get(v_traceState_3225_, 0);
v_isSharedCheck_3263_ = !lean_is_exclusive(v_traceState_3225_);
if (v_isSharedCheck_3263_ == 0)
{
v___x_3240_ = v_traceState_3225_;
v_isShared_3241_ = v_isSharedCheck_3263_;
goto v_resetjp_3239_;
}
else
{
lean_inc(v_traces_3238_);
lean_dec(v_traceState_3225_);
v___x_3240_ = lean_box(0);
v_isShared_3241_ = v_isSharedCheck_3263_;
goto v_resetjp_3239_;
}
v_resetjp_3239_:
{
lean_object* v___x_3242_; double v___x_3243_; uint8_t v___x_3244_; lean_object* v___x_3245_; lean_object* v___x_3246_; lean_object* v___x_3247_; lean_object* v___x_3248_; lean_object* v___x_3249_; lean_object* v___x_3250_; lean_object* v___x_3252_; 
v___x_3242_ = lean_box(0);
v___x_3243_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6___closed__0);
v___x_3244_ = 0;
v___x_3245_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6___closed__1));
v___x_3246_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3246_, 0, v_cls_3212_);
lean_ctor_set(v___x_3246_, 1, v___x_3242_);
lean_ctor_set(v___x_3246_, 2, v___x_3245_);
lean_ctor_set_float(v___x_3246_, sizeof(void*)*3, v___x_3243_);
lean_ctor_set_float(v___x_3246_, sizeof(void*)*3 + 8, v___x_3243_);
lean_ctor_set_uint8(v___x_3246_, sizeof(void*)*3 + 16, v___x_3244_);
v___x_3247_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6___closed__2));
v___x_3248_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3248_, 0, v___x_3246_);
lean_ctor_set(v___x_3248_, 1, v_a_3220_);
lean_ctor_set(v___x_3248_, 2, v___x_3247_);
lean_inc(v_ref_3218_);
v___x_3249_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3249_, 0, v_ref_3218_);
lean_ctor_set(v___x_3249_, 1, v___x_3248_);
v___x_3250_ = l_Lean_PersistentArray_push___redArg(v_traces_3238_, v___x_3249_);
if (v_isShared_3241_ == 0)
{
lean_ctor_set(v___x_3240_, 0, v___x_3250_);
v___x_3252_ = v___x_3240_;
goto v_reusejp_3251_;
}
else
{
lean_object* v_reuseFailAlloc_3262_; 
v_reuseFailAlloc_3262_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3262_, 0, v___x_3250_);
lean_ctor_set_uint64(v_reuseFailAlloc_3262_, sizeof(void*)*1, v_tid_3237_);
v___x_3252_ = v_reuseFailAlloc_3262_;
goto v_reusejp_3251_;
}
v_reusejp_3251_:
{
lean_object* v___x_3254_; 
if (v_isShared_3236_ == 0)
{
lean_ctor_set(v___x_3235_, 4, v___x_3252_);
v___x_3254_ = v___x_3235_;
goto v_reusejp_3253_;
}
else
{
lean_object* v_reuseFailAlloc_3261_; 
v_reuseFailAlloc_3261_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3261_, 0, v_env_3226_);
lean_ctor_set(v_reuseFailAlloc_3261_, 1, v_nextMacroScope_3227_);
lean_ctor_set(v_reuseFailAlloc_3261_, 2, v_ngen_3228_);
lean_ctor_set(v_reuseFailAlloc_3261_, 3, v_auxDeclNGen_3229_);
lean_ctor_set(v_reuseFailAlloc_3261_, 4, v___x_3252_);
lean_ctor_set(v_reuseFailAlloc_3261_, 5, v_cache_3230_);
lean_ctor_set(v_reuseFailAlloc_3261_, 6, v_messages_3231_);
lean_ctor_set(v_reuseFailAlloc_3261_, 7, v_infoState_3232_);
lean_ctor_set(v_reuseFailAlloc_3261_, 8, v_snapshotTasks_3233_);
v___x_3254_ = v_reuseFailAlloc_3261_;
goto v_reusejp_3253_;
}
v_reusejp_3253_:
{
lean_object* v___x_3255_; lean_object* v___x_3256_; lean_object* v___x_3257_; lean_object* v___x_3259_; 
v___x_3255_ = lean_st_ref_set(v___y_3216_, v___x_3254_);
v___x_3256_ = lean_box(0);
v___x_3257_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3257_, 0, v___x_3256_);
lean_ctor_set(v___x_3257_, 1, v___y_3214_);
if (v_isShared_3223_ == 0)
{
lean_ctor_set(v___x_3222_, 0, v___x_3257_);
v___x_3259_ = v___x_3222_;
goto v_reusejp_3258_;
}
else
{
lean_object* v_reuseFailAlloc_3260_; 
v_reuseFailAlloc_3260_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3260_, 0, v___x_3257_);
v___x_3259_ = v_reuseFailAlloc_3260_;
goto v_reusejp_3258_;
}
v_reusejp_3258_:
{
return v___x_3259_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6___boxed(lean_object* v_cls_3266_, lean_object* v_msg_3267_, lean_object* v___y_3268_, lean_object* v___y_3269_, lean_object* v___y_3270_, lean_object* v___y_3271_){
_start:
{
lean_object* v_res_3272_; 
v_res_3272_ = l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6(v_cls_3266_, v_msg_3267_, v___y_3268_, v___y_3269_, v___y_3270_);
lean_dec(v___y_3270_);
lean_dec_ref(v___y_3269_);
return v_res_3272_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0_spec__0___redArg(lean_object* v_a_3273_, lean_object* v_x_3274_){
_start:
{
if (lean_obj_tag(v_x_3274_) == 0)
{
lean_object* v___x_3275_; 
v___x_3275_ = lean_box(0);
return v___x_3275_;
}
else
{
lean_object* v_key_3276_; lean_object* v_value_3277_; lean_object* v_tail_3278_; uint8_t v___x_3279_; 
v_key_3276_ = lean_ctor_get(v_x_3274_, 0);
v_value_3277_ = lean_ctor_get(v_x_3274_, 1);
v_tail_3278_ = lean_ctor_get(v_x_3274_, 2);
v___x_3279_ = l_Lean_instBEqFVarId_beq(v_key_3276_, v_a_3273_);
if (v___x_3279_ == 0)
{
v_x_3274_ = v_tail_3278_;
goto _start;
}
else
{
lean_object* v___x_3281_; 
lean_inc(v_value_3277_);
v___x_3281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3281_, 0, v_value_3277_);
return v___x_3281_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0_spec__0___redArg___boxed(lean_object* v_a_3282_, lean_object* v_x_3283_){
_start:
{
lean_object* v_res_3284_; 
v_res_3284_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0_spec__0___redArg(v_a_3282_, v_x_3283_);
lean_dec(v_x_3283_);
lean_dec(v_a_3282_);
return v_res_3284_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0___redArg(lean_object* v_m_3285_, lean_object* v_a_3286_){
_start:
{
lean_object* v_buckets_3287_; lean_object* v___x_3288_; uint64_t v___x_3289_; uint64_t v___x_3290_; uint64_t v___x_3291_; uint64_t v_fold_3292_; uint64_t v___x_3293_; uint64_t v___x_3294_; uint64_t v___x_3295_; size_t v___x_3296_; size_t v___x_3297_; size_t v___x_3298_; size_t v___x_3299_; size_t v___x_3300_; lean_object* v___x_3301_; lean_object* v___x_3302_; 
v_buckets_3287_ = lean_ctor_get(v_m_3285_, 1);
v___x_3288_ = lean_array_get_size(v_buckets_3287_);
v___x_3289_ = l_Lean_instHashableFVarId_hash(v_a_3286_);
v___x_3290_ = 32ULL;
v___x_3291_ = lean_uint64_shift_right(v___x_3289_, v___x_3290_);
v_fold_3292_ = lean_uint64_xor(v___x_3289_, v___x_3291_);
v___x_3293_ = 16ULL;
v___x_3294_ = lean_uint64_shift_right(v_fold_3292_, v___x_3293_);
v___x_3295_ = lean_uint64_xor(v_fold_3292_, v___x_3294_);
v___x_3296_ = lean_uint64_to_usize(v___x_3295_);
v___x_3297_ = lean_usize_of_nat(v___x_3288_);
v___x_3298_ = ((size_t)1ULL);
v___x_3299_ = lean_usize_sub(v___x_3297_, v___x_3298_);
v___x_3300_ = lean_usize_land(v___x_3296_, v___x_3299_);
v___x_3301_ = lean_array_uget_borrowed(v_buckets_3287_, v___x_3300_);
v___x_3302_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0_spec__0___redArg(v_a_3286_, v___x_3301_);
return v___x_3302_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0___redArg___boxed(lean_object* v_m_3303_, lean_object* v_a_3304_){
_start:
{
lean_object* v_res_3305_; 
v_res_3305_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0___redArg(v_m_3303_, v_a_3304_);
lean_dec(v_a_3304_);
lean_dec_ref(v_m_3303_);
return v_res_3305_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___lam__0___boxed(lean_object* v___x_3306_, lean_object* v_m_3307_, lean_object* v_e_3308_, lean_object* v___y_3309_, lean_object* v___y_3310_, lean_object* v___y_3311_, lean_object* v___y_3312_){
_start:
{
uint8_t v___x_19748__boxed_3313_; lean_object* v_res_3314_; 
v___x_19748__boxed_3313_ = lean_unbox(v___x_3306_);
v_res_3314_ = l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___lam__0(v___x_19748__boxed_3313_, v_m_3307_, v_e_3308_, v___y_3309_, v___y_3310_, v___y_3311_);
lean_dec(v___y_3311_);
lean_dec_ref(v___y_3310_);
lean_dec_ref(v_e_3308_);
return v_res_3314_;
}
}
static lean_object* _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__0(void){
_start:
{
lean_object* v___x_3315_; lean_object* v___x_3316_; lean_object* v___x_3317_; 
v___x_3315_ = lean_box(0);
v___x_3316_ = lean_unsigned_to_nat(16u);
v___x_3317_ = lean_mk_array(v___x_3316_, v___x_3315_);
return v___x_3317_;
}
}
static lean_object* _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__1(void){
_start:
{
lean_object* v___x_3318_; lean_object* v___x_3319_; lean_object* v___x_3320_; 
v___x_3318_ = lean_obj_once(&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__0, &l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__0_once, _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__0);
v___x_3319_ = lean_unsigned_to_nat(0u);
v___x_3320_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3320_, 0, v___x_3319_);
lean_ctor_set(v___x_3320_, 1, v___x_3318_);
return v___x_3320_;
}
}
static lean_object* _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__5(void){
_start:
{
lean_object* v___x_3324_; lean_object* v___x_3325_; lean_object* v___x_3326_; lean_object* v___x_3327_; lean_object* v___x_3328_; lean_object* v___x_3329_; 
v___x_3324_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__4));
v___x_3325_ = lean_unsigned_to_nat(4u);
v___x_3326_ = lean_unsigned_to_nat(384u);
v___x_3327_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__3));
v___x_3328_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__2));
v___x_3329_ = l_mkPanicMessageWithDecl(v___x_3328_, v___x_3327_, v___x_3326_, v___x_3325_, v___x_3324_);
return v___x_3329_;
}
}
static lean_object* _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__7(void){
_start:
{
lean_object* v___x_3331_; lean_object* v___x_3332_; 
v___x_3331_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__6));
v___x_3332_ = l_Lean_stringToMessageData(v___x_3331_);
return v___x_3332_;
}
}
static lean_object* _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__13(void){
_start:
{
lean_object* v___x_3341_; lean_object* v___x_3342_; lean_object* v___x_3343_; 
v___x_3341_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__10));
v___x_3342_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__12));
v___x_3343_ = l_Lean_Name_append(v___x_3342_, v___x_3341_);
return v___x_3343_;
}
}
static lean_object* _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__15(void){
_start:
{
lean_object* v___x_3345_; lean_object* v___x_3346_; 
v___x_3345_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__14));
v___x_3346_ = l_Lean_stringToMessageData(v___x_3345_);
return v___x_3346_;
}
}
static lean_object* _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__17(void){
_start:
{
lean_object* v___x_3348_; lean_object* v___x_3349_; 
v___x_3348_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__16));
v___x_3349_ = l_Lean_stringToMessageData(v___x_3348_);
return v___x_3349_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit(lean_object* v_m_3350_, lean_object* v_fvarId_3351_, lean_object* v_a_3352_, lean_object* v_a_3353_, lean_object* v_a_3354_){
_start:
{
lean_object* v___x_3356_; 
v___x_3356_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0___redArg(v_m_3350_, v_fvarId_3351_);
if (lean_obj_tag(v___x_3356_) == 1)
{
lean_object* v_val_3357_; lean_object* v___x_3359_; uint8_t v_isShared_3360_; uint8_t v_isSharedCheck_3470_; 
v_val_3357_ = lean_ctor_get(v___x_3356_, 0);
v_isSharedCheck_3470_ = !lean_is_exclusive(v___x_3356_);
if (v_isSharedCheck_3470_ == 0)
{
v___x_3359_ = v___x_3356_;
v_isShared_3360_ = v_isSharedCheck_3470_;
goto v_resetjp_3358_;
}
else
{
lean_inc(v_val_3357_);
lean_dec(v___x_3356_);
v___x_3359_ = lean_box(0);
v_isShared_3360_ = v_isSharedCheck_3470_;
goto v_resetjp_3358_;
}
v_resetjp_3358_:
{
lean_object* v_fst_3361_; lean_object* v_snd_3362_; lean_object* v___x_3364_; uint8_t v_isShared_3365_; uint8_t v_isSharedCheck_3469_; 
v_fst_3361_ = lean_ctor_get(v_val_3357_, 0);
v_snd_3362_ = lean_ctor_get(v_val_3357_, 1);
v_isSharedCheck_3469_ = !lean_is_exclusive(v_val_3357_);
if (v_isSharedCheck_3469_ == 0)
{
v___x_3364_ = v_val_3357_;
v_isShared_3365_ = v_isSharedCheck_3469_;
goto v_resetjp_3363_;
}
else
{
lean_inc(v_snd_3362_);
lean_inc(v_fst_3361_);
lean_dec(v_val_3357_);
v___x_3364_ = lean_box(0);
v_isShared_3365_ = v_isSharedCheck_3469_;
goto v_resetjp_3363_;
}
v_resetjp_3363_:
{
lean_object* v_tempMark_3366_; lean_object* v_doneMark_3367_; lean_object* v___x_3368_; uint8_t v___x_3369_; 
v_tempMark_3366_ = lean_ctor_get(v_a_3352_, 0);
v_doneMark_3367_ = lean_ctor_get(v_a_3352_, 1);
v___x_3368_ = l_Lean_LocalDecl_fvarId(v_fst_3361_);
v___x_3369_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1___redArg(v_doneMark_3367_, v___x_3368_);
if (v___x_3369_ == 0)
{
lean_object* v_options_3370_; lean_object* v_inheritedTraceOptions_3371_; uint8_t v_hasTrace_3372_; uint8_t v___x_3373_; lean_object* v___x_3374_; lean_object* v___f_3375_; lean_object* v___y_3377_; lean_object* v___y_3378_; lean_object* v___y_3379_; lean_object* v___y_3430_; lean_object* v___y_3431_; lean_object* v___y_3432_; lean_object* v___y_3437_; lean_object* v_tempMark_3438_; lean_object* v___y_3439_; lean_object* v___y_3440_; 
lean_del_object(v___x_3364_);
lean_del_object(v___x_3359_);
v_options_3370_ = lean_ctor_get(v_a_3353_, 2);
v_inheritedTraceOptions_3371_ = lean_ctor_get(v_a_3353_, 13);
v_hasTrace_3372_ = lean_ctor_get_uint8(v_options_3370_, sizeof(void*)*1);
v___x_3373_ = 1;
v___x_3374_ = lean_box(v___x_3373_);
v___f_3375_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___lam__0___boxed), 7, 2);
lean_closure_set(v___f_3375_, 0, v___x_3374_);
lean_closure_set(v___f_3375_, 1, v_m_3350_);
if (v_hasTrace_3372_ == 0)
{
lean_inc_ref(v_tempMark_3366_);
v___y_3437_ = v_a_3352_;
v_tempMark_3438_ = v_tempMark_3366_;
v___y_3439_ = v_a_3353_;
v___y_3440_ = v_a_3354_;
goto v___jp_3436_;
}
else
{
lean_object* v___x_3446_; lean_object* v___x_3447_; uint8_t v___x_3448_; 
v___x_3446_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__10));
v___x_3447_ = lean_obj_once(&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__13, &l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__13_once, _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__13);
v___x_3448_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3371_, v_options_3370_, v___x_3447_);
if (v___x_3448_ == 0)
{
lean_inc_ref(v_tempMark_3366_);
v___y_3437_ = v_a_3352_;
v_tempMark_3438_ = v_tempMark_3366_;
v___y_3439_ = v_a_3353_;
v___y_3440_ = v_a_3354_;
goto v___jp_3436_;
}
else
{
lean_object* v___x_3449_; lean_object* v___x_3450_; lean_object* v___x_3451_; lean_object* v___x_3452_; lean_object* v___x_3453_; lean_object* v___x_3454_; lean_object* v___x_3455_; lean_object* v___x_3456_; lean_object* v___x_3457_; lean_object* v___x_3458_; 
v___x_3449_ = lean_obj_once(&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__15, &l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__15_once, _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__15);
lean_inc(v___x_3368_);
v___x_3450_ = l_Lean_mkFVar(v___x_3368_);
v___x_3451_ = l_Lean_MessageData_ofExpr(v___x_3450_);
v___x_3452_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3452_, 0, v___x_3449_);
lean_ctor_set(v___x_3452_, 1, v___x_3451_);
v___x_3453_ = lean_obj_once(&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__17, &l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__17_once, _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__17);
v___x_3454_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3454_, 0, v___x_3452_);
lean_ctor_set(v___x_3454_, 1, v___x_3453_);
v___x_3455_ = l_Lean_LocalDecl_type(v_fst_3361_);
v___x_3456_ = l_Lean_MessageData_ofExpr(v___x_3455_);
v___x_3457_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3457_, 0, v___x_3454_);
lean_ctor_set(v___x_3457_, 1, v___x_3456_);
v___x_3458_ = l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6(v___x_3446_, v___x_3457_, v_a_3352_, v_a_3353_, v_a_3354_);
if (lean_obj_tag(v___x_3458_) == 0)
{
lean_object* v_a_3459_; lean_object* v_snd_3460_; lean_object* v_tempMark_3461_; 
v_a_3459_ = lean_ctor_get(v___x_3458_, 0);
lean_inc(v_a_3459_);
lean_dec_ref(v___x_3458_);
v_snd_3460_ = lean_ctor_get(v_a_3459_, 1);
lean_inc(v_snd_3460_);
lean_dec(v_a_3459_);
v_tempMark_3461_ = lean_ctor_get(v_snd_3460_, 0);
lean_inc_ref(v_tempMark_3461_);
v___y_3437_ = v_snd_3460_;
v_tempMark_3438_ = v_tempMark_3461_;
v___y_3439_ = v_a_3353_;
v___y_3440_ = v_a_3354_;
goto v___jp_3436_;
}
else
{
lean_dec_ref(v___f_3375_);
lean_dec(v___x_3368_);
lean_dec(v_snd_3362_);
lean_dec(v_fst_3361_);
return v___x_3458_;
}
}
}
v___jp_3376_:
{
lean_object* v_tempMark_3380_; lean_object* v_doneMark_3381_; lean_object* v_newDecls_3382_; lean_object* v_newArgs_3383_; lean_object* v___x_3385_; uint8_t v_isShared_3386_; uint8_t v_isSharedCheck_3428_; 
v_tempMark_3380_ = lean_ctor_get(v___y_3378_, 0);
v_doneMark_3381_ = lean_ctor_get(v___y_3378_, 1);
v_newDecls_3382_ = lean_ctor_get(v___y_3378_, 2);
v_newArgs_3383_ = lean_ctor_get(v___y_3378_, 3);
v_isSharedCheck_3428_ = !lean_is_exclusive(v___y_3378_);
if (v_isSharedCheck_3428_ == 0)
{
v___x_3385_ = v___y_3378_;
v_isShared_3386_ = v_isSharedCheck_3428_;
goto v_resetjp_3384_;
}
else
{
lean_inc(v_newArgs_3383_);
lean_inc(v_newDecls_3382_);
lean_inc(v_doneMark_3381_);
lean_inc(v_tempMark_3380_);
lean_dec(v___y_3378_);
v___x_3385_ = lean_box(0);
v_isShared_3386_ = v_isSharedCheck_3428_;
goto v_resetjp_3384_;
}
v_resetjp_3384_:
{
lean_object* v___x_3387_; lean_object* v___x_3388_; lean_object* v___x_3389_; lean_object* v___x_3390_; lean_object* v___x_3392_; 
v___x_3387_ = lean_obj_once(&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__1, &l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__1_once, _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__1);
v___x_3388_ = lean_st_mk_ref(v___x_3387_);
v___x_3389_ = lean_box(0);
lean_inc(v___x_3368_);
v___x_3390_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2___redArg(v_tempMark_3380_, v___x_3368_, v___x_3389_);
if (v_isShared_3386_ == 0)
{
lean_ctor_set(v___x_3385_, 0, v___x_3390_);
v___x_3392_ = v___x_3385_;
goto v_reusejp_3391_;
}
else
{
lean_object* v_reuseFailAlloc_3427_; 
v_reuseFailAlloc_3427_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3427_, 0, v___x_3390_);
lean_ctor_set(v_reuseFailAlloc_3427_, 1, v_doneMark_3381_);
lean_ctor_set(v_reuseFailAlloc_3427_, 2, v_newDecls_3382_);
lean_ctor_set(v_reuseFailAlloc_3427_, 3, v_newArgs_3383_);
v___x_3392_ = v_reuseFailAlloc_3427_;
goto v_reusejp_3391_;
}
v_reusejp_3391_:
{
lean_object* v___x_3393_; lean_object* v___x_3394_; 
v___x_3393_ = l_Lean_LocalDecl_type(v_fst_3361_);
v___x_3394_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3(v___f_3375_, v___x_3393_, v___x_3388_, v___x_3392_, v___y_3379_, v___y_3377_);
if (lean_obj_tag(v___x_3394_) == 0)
{
lean_object* v_a_3395_; lean_object* v___x_3397_; uint8_t v_isShared_3398_; uint8_t v_isSharedCheck_3426_; 
v_a_3395_ = lean_ctor_get(v___x_3394_, 0);
v_isSharedCheck_3426_ = !lean_is_exclusive(v___x_3394_);
if (v_isSharedCheck_3426_ == 0)
{
v___x_3397_ = v___x_3394_;
v_isShared_3398_ = v_isSharedCheck_3426_;
goto v_resetjp_3396_;
}
else
{
lean_inc(v_a_3395_);
lean_dec(v___x_3394_);
v___x_3397_ = lean_box(0);
v_isShared_3398_ = v_isSharedCheck_3426_;
goto v_resetjp_3396_;
}
v_resetjp_3396_:
{
lean_object* v_snd_3399_; lean_object* v___x_3401_; uint8_t v_isShared_3402_; uint8_t v_isSharedCheck_3424_; 
v_snd_3399_ = lean_ctor_get(v_a_3395_, 1);
v_isSharedCheck_3424_ = !lean_is_exclusive(v_a_3395_);
if (v_isSharedCheck_3424_ == 0)
{
lean_object* v_unused_3425_; 
v_unused_3425_ = lean_ctor_get(v_a_3395_, 0);
lean_dec(v_unused_3425_);
v___x_3401_ = v_a_3395_;
v_isShared_3402_ = v_isSharedCheck_3424_;
goto v_resetjp_3400_;
}
else
{
lean_inc(v_snd_3399_);
lean_dec(v_a_3395_);
v___x_3401_ = lean_box(0);
v_isShared_3402_ = v_isSharedCheck_3424_;
goto v_resetjp_3400_;
}
v_resetjp_3400_:
{
lean_object* v___x_3403_; lean_object* v_tempMark_3404_; lean_object* v_doneMark_3405_; lean_object* v_newDecls_3406_; lean_object* v_newArgs_3407_; lean_object* v___x_3409_; uint8_t v_isShared_3410_; uint8_t v_isSharedCheck_3423_; 
v___x_3403_ = lean_st_ref_get(v___x_3388_);
lean_dec(v___x_3388_);
lean_dec(v___x_3403_);
v_tempMark_3404_ = lean_ctor_get(v_snd_3399_, 0);
v_doneMark_3405_ = lean_ctor_get(v_snd_3399_, 1);
v_newDecls_3406_ = lean_ctor_get(v_snd_3399_, 2);
v_newArgs_3407_ = lean_ctor_get(v_snd_3399_, 3);
v_isSharedCheck_3423_ = !lean_is_exclusive(v_snd_3399_);
if (v_isSharedCheck_3423_ == 0)
{
v___x_3409_ = v_snd_3399_;
v_isShared_3410_ = v_isSharedCheck_3423_;
goto v_resetjp_3408_;
}
else
{
lean_inc(v_newArgs_3407_);
lean_inc(v_newDecls_3406_);
lean_inc(v_doneMark_3405_);
lean_inc(v_tempMark_3404_);
lean_dec(v_snd_3399_);
v___x_3409_ = lean_box(0);
v_isShared_3410_ = v_isSharedCheck_3423_;
goto v_resetjp_3408_;
}
v_resetjp_3408_:
{
lean_object* v___x_3411_; lean_object* v___x_3412_; lean_object* v___x_3413_; lean_object* v___x_3415_; 
v___x_3411_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2___redArg(v_doneMark_3405_, v___x_3368_, v___x_3389_);
v___x_3412_ = lean_array_push(v_newDecls_3406_, v_fst_3361_);
v___x_3413_ = lean_array_push(v_newArgs_3407_, v_snd_3362_);
if (v_isShared_3410_ == 0)
{
lean_ctor_set(v___x_3409_, 3, v___x_3413_);
lean_ctor_set(v___x_3409_, 2, v___x_3412_);
lean_ctor_set(v___x_3409_, 1, v___x_3411_);
v___x_3415_ = v___x_3409_;
goto v_reusejp_3414_;
}
else
{
lean_object* v_reuseFailAlloc_3422_; 
v_reuseFailAlloc_3422_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3422_, 0, v_tempMark_3404_);
lean_ctor_set(v_reuseFailAlloc_3422_, 1, v___x_3411_);
lean_ctor_set(v_reuseFailAlloc_3422_, 2, v___x_3412_);
lean_ctor_set(v_reuseFailAlloc_3422_, 3, v___x_3413_);
v___x_3415_ = v_reuseFailAlloc_3422_;
goto v_reusejp_3414_;
}
v_reusejp_3414_:
{
lean_object* v___x_3417_; 
if (v_isShared_3402_ == 0)
{
lean_ctor_set(v___x_3401_, 1, v___x_3415_);
lean_ctor_set(v___x_3401_, 0, v___x_3389_);
v___x_3417_ = v___x_3401_;
goto v_reusejp_3416_;
}
else
{
lean_object* v_reuseFailAlloc_3421_; 
v_reuseFailAlloc_3421_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3421_, 0, v___x_3389_);
lean_ctor_set(v_reuseFailAlloc_3421_, 1, v___x_3415_);
v___x_3417_ = v_reuseFailAlloc_3421_;
goto v_reusejp_3416_;
}
v_reusejp_3416_:
{
lean_object* v___x_3419_; 
if (v_isShared_3398_ == 0)
{
lean_ctor_set(v___x_3397_, 0, v___x_3417_);
v___x_3419_ = v___x_3397_;
goto v_reusejp_3418_;
}
else
{
lean_object* v_reuseFailAlloc_3420_; 
v_reuseFailAlloc_3420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3420_, 0, v___x_3417_);
v___x_3419_ = v_reuseFailAlloc_3420_;
goto v_reusejp_3418_;
}
v_reusejp_3418_:
{
return v___x_3419_;
}
}
}
}
}
}
}
else
{
lean_dec(v___x_3388_);
lean_dec(v___x_3368_);
lean_dec(v_snd_3362_);
lean_dec(v_fst_3361_);
return v___x_3394_;
}
}
}
}
v___jp_3429_:
{
uint8_t v___x_3433_; 
v___x_3433_ = l_Lean_LocalDecl_isLet(v_fst_3361_, v___x_3373_);
if (v___x_3433_ == 0)
{
v___y_3377_ = v___y_3432_;
v___y_3378_ = v___y_3430_;
v___y_3379_ = v___y_3431_;
goto v___jp_3376_;
}
else
{
if (v___x_3369_ == 0)
{
lean_object* v___x_3434_; lean_object* v___x_3435_; 
lean_dec_ref(v___f_3375_);
lean_dec(v___x_3368_);
lean_dec(v_snd_3362_);
lean_dec(v_fst_3361_);
v___x_3434_ = lean_obj_once(&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__5, &l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__5_once, _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__5);
v___x_3435_ = l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4(v___x_3434_, v___y_3430_, v___y_3431_, v___y_3432_);
return v___x_3435_;
}
else
{
v___y_3377_ = v___y_3432_;
v___y_3378_ = v___y_3430_;
v___y_3379_ = v___y_3431_;
goto v___jp_3376_;
}
}
}
v___jp_3436_:
{
uint8_t v___x_3441_; 
v___x_3441_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1___redArg(v_tempMark_3438_, v___x_3368_);
lean_dec_ref(v_tempMark_3438_);
if (v___x_3441_ == 0)
{
v___y_3430_ = v___y_3437_;
v___y_3431_ = v___y_3439_;
v___y_3432_ = v___y_3440_;
goto v___jp_3429_;
}
else
{
lean_object* v___x_3442_; lean_object* v___x_3443_; 
lean_dec_ref(v___y_3437_);
v___x_3442_ = lean_obj_once(&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__7, &l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__7_once, _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__7);
v___x_3443_ = l_Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5___redArg(v___x_3442_, v___y_3439_, v___y_3440_);
if (lean_obj_tag(v___x_3443_) == 0)
{
lean_object* v_a_3444_; lean_object* v_snd_3445_; 
v_a_3444_ = lean_ctor_get(v___x_3443_, 0);
lean_inc(v_a_3444_);
lean_dec_ref(v___x_3443_);
v_snd_3445_ = lean_ctor_get(v_a_3444_, 1);
lean_inc(v_snd_3445_);
lean_dec(v_a_3444_);
v___y_3430_ = v_snd_3445_;
v___y_3431_ = v___y_3439_;
v___y_3432_ = v___y_3440_;
goto v___jp_3429_;
}
else
{
lean_dec_ref(v___f_3375_);
lean_dec(v___x_3368_);
lean_dec(v_snd_3362_);
lean_dec(v_fst_3361_);
return v___x_3443_;
}
}
}
}
else
{
lean_object* v___x_3462_; lean_object* v___x_3464_; 
lean_dec(v___x_3368_);
lean_dec(v_snd_3362_);
lean_dec(v_fst_3361_);
lean_dec_ref(v_m_3350_);
v___x_3462_ = lean_box(0);
if (v_isShared_3365_ == 0)
{
lean_ctor_set(v___x_3364_, 1, v_a_3352_);
lean_ctor_set(v___x_3364_, 0, v___x_3462_);
v___x_3464_ = v___x_3364_;
goto v_reusejp_3463_;
}
else
{
lean_object* v_reuseFailAlloc_3468_; 
v_reuseFailAlloc_3468_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3468_, 0, v___x_3462_);
lean_ctor_set(v_reuseFailAlloc_3468_, 1, v_a_3352_);
v___x_3464_ = v_reuseFailAlloc_3468_;
goto v_reusejp_3463_;
}
v_reusejp_3463_:
{
lean_object* v___x_3466_; 
if (v_isShared_3360_ == 0)
{
lean_ctor_set_tag(v___x_3359_, 0);
lean_ctor_set(v___x_3359_, 0, v___x_3464_);
v___x_3466_ = v___x_3359_;
goto v_reusejp_3465_;
}
else
{
lean_object* v_reuseFailAlloc_3467_; 
v_reuseFailAlloc_3467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3467_, 0, v___x_3464_);
v___x_3466_ = v_reuseFailAlloc_3467_;
goto v_reusejp_3465_;
}
v_reusejp_3465_:
{
return v___x_3466_;
}
}
}
}
}
}
else
{
lean_object* v___x_3471_; lean_object* v___x_3472_; lean_object* v___x_3473_; 
lean_dec(v___x_3356_);
lean_dec_ref(v_m_3350_);
v___x_3471_ = lean_box(0);
v___x_3472_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3472_, 0, v___x_3471_);
lean_ctor_set(v___x_3472_, 1, v_a_3352_);
v___x_3473_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3473_, 0, v___x_3472_);
return v___x_3473_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___lam__0(uint8_t v___x_3474_, lean_object* v_m_3475_, lean_object* v_e_3476_, lean_object* v___y_3477_, lean_object* v___y_3478_, lean_object* v___y_3479_){
_start:
{
lean_object* v___y_3482_; uint8_t v___x_3486_; 
v___x_3486_ = l_Lean_Expr_hasFVar(v_e_3476_);
if (v___x_3486_ == 0)
{
lean_object* v___x_3487_; lean_object* v___x_3488_; lean_object* v___x_3489_; 
lean_dec_ref(v_m_3475_);
v___x_3487_ = lean_box(v___x_3486_);
v___x_3488_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3488_, 0, v___x_3487_);
lean_ctor_set(v___x_3488_, 1, v___y_3477_);
v___x_3489_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3489_, 0, v___x_3488_);
return v___x_3489_;
}
else
{
uint8_t v___x_3490_; 
v___x_3490_ = l_Lean_Expr_isFVar(v_e_3476_);
if (v___x_3490_ == 0)
{
lean_dec_ref(v_m_3475_);
v___y_3482_ = v___y_3477_;
goto v___jp_3481_;
}
else
{
lean_object* v___x_3491_; lean_object* v___x_3492_; 
v___x_3491_ = l_Lean_Expr_fvarId_x21(v_e_3476_);
v___x_3492_ = l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit(v_m_3475_, v___x_3491_, v___y_3477_, v___y_3478_, v___y_3479_);
lean_dec(v___x_3491_);
if (lean_obj_tag(v___x_3492_) == 0)
{
lean_object* v_a_3493_; lean_object* v_snd_3494_; 
v_a_3493_ = lean_ctor_get(v___x_3492_, 0);
lean_inc(v_a_3493_);
lean_dec_ref(v___x_3492_);
v_snd_3494_ = lean_ctor_get(v_a_3493_, 1);
lean_inc(v_snd_3494_);
lean_dec(v_a_3493_);
v___y_3482_ = v_snd_3494_;
goto v___jp_3481_;
}
else
{
lean_object* v_a_3495_; lean_object* v___x_3497_; uint8_t v_isShared_3498_; uint8_t v_isSharedCheck_3502_; 
v_a_3495_ = lean_ctor_get(v___x_3492_, 0);
v_isSharedCheck_3502_ = !lean_is_exclusive(v___x_3492_);
if (v_isSharedCheck_3502_ == 0)
{
v___x_3497_ = v___x_3492_;
v_isShared_3498_ = v_isSharedCheck_3502_;
goto v_resetjp_3496_;
}
else
{
lean_inc(v_a_3495_);
lean_dec(v___x_3492_);
v___x_3497_ = lean_box(0);
v_isShared_3498_ = v_isSharedCheck_3502_;
goto v_resetjp_3496_;
}
v_resetjp_3496_:
{
lean_object* v___x_3500_; 
if (v_isShared_3498_ == 0)
{
v___x_3500_ = v___x_3497_;
goto v_reusejp_3499_;
}
else
{
lean_object* v_reuseFailAlloc_3501_; 
v_reuseFailAlloc_3501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3501_, 0, v_a_3495_);
v___x_3500_ = v_reuseFailAlloc_3501_;
goto v_reusejp_3499_;
}
v_reusejp_3499_:
{
return v___x_3500_;
}
}
}
}
}
v___jp_3481_:
{
lean_object* v___x_3483_; lean_object* v___x_3484_; lean_object* v___x_3485_; 
v___x_3483_ = lean_box(v___x_3474_);
v___x_3484_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3484_, 0, v___x_3483_);
lean_ctor_set(v___x_3484_, 1, v___y_3482_);
v___x_3485_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3485_, 0, v___x_3484_);
return v___x_3485_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___boxed(lean_object* v_m_3503_, lean_object* v_fvarId_3504_, lean_object* v_a_3505_, lean_object* v_a_3506_, lean_object* v_a_3507_, lean_object* v_a_3508_){
_start:
{
lean_object* v_res_3509_; 
v_res_3509_ = l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit(v_m_3503_, v_fvarId_3504_, v_a_3505_, v_a_3506_, v_a_3507_);
lean_dec(v_a_3507_);
lean_dec_ref(v_a_3506_);
lean_dec(v_fvarId_3504_);
return v_res_3509_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0(lean_object* v_00_u03b2_3510_, lean_object* v_m_3511_, lean_object* v_a_3512_){
_start:
{
lean_object* v___x_3513_; 
v___x_3513_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0___redArg(v_m_3511_, v_a_3512_);
return v___x_3513_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0___boxed(lean_object* v_00_u03b2_3514_, lean_object* v_m_3515_, lean_object* v_a_3516_){
_start:
{
lean_object* v_res_3517_; 
v_res_3517_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0(v_00_u03b2_3514_, v_m_3515_, v_a_3516_);
lean_dec(v_a_3516_);
lean_dec_ref(v_m_3515_);
return v_res_3517_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1(lean_object* v_00_u03b2_3518_, lean_object* v_m_3519_, lean_object* v_a_3520_){
_start:
{
uint8_t v___x_3521_; 
v___x_3521_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1___redArg(v_m_3519_, v_a_3520_);
return v___x_3521_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1___boxed(lean_object* v_00_u03b2_3522_, lean_object* v_m_3523_, lean_object* v_a_3524_){
_start:
{
uint8_t v_res_3525_; lean_object* v_r_3526_; 
v_res_3525_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1(v_00_u03b2_3522_, v_m_3523_, v_a_3524_);
lean_dec(v_a_3524_);
lean_dec_ref(v_m_3523_);
v_r_3526_ = lean_box(v_res_3525_);
return v_r_3526_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2(lean_object* v_00_u03b2_3527_, lean_object* v_m_3528_, lean_object* v_a_3529_, lean_object* v_b_3530_){
_start:
{
lean_object* v___x_3531_; 
v___x_3531_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2___redArg(v_m_3528_, v_a_3529_, v_b_3530_);
return v___x_3531_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5(lean_object* v_00_u03b1_3532_, lean_object* v_msg_3533_, lean_object* v___y_3534_, lean_object* v___y_3535_, lean_object* v___y_3536_){
_start:
{
lean_object* v___x_3538_; 
v___x_3538_ = l_Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5___redArg(v_msg_3533_, v___y_3535_, v___y_3536_);
return v___x_3538_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5___boxed(lean_object* v_00_u03b1_3539_, lean_object* v_msg_3540_, lean_object* v___y_3541_, lean_object* v___y_3542_, lean_object* v___y_3543_, lean_object* v___y_3544_){
_start:
{
lean_object* v_res_3545_; 
v_res_3545_ = l_Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5(v_00_u03b1_3539_, v_msg_3540_, v___y_3541_, v___y_3542_, v___y_3543_);
lean_dec(v___y_3543_);
lean_dec_ref(v___y_3542_);
lean_dec_ref(v___y_3541_);
return v_res_3545_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0_spec__0(lean_object* v_00_u03b2_3546_, lean_object* v_a_3547_, lean_object* v_x_3548_){
_start:
{
lean_object* v___x_3549_; 
v___x_3549_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0_spec__0___redArg(v_a_3547_, v_x_3548_);
return v___x_3549_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3550_, lean_object* v_a_3551_, lean_object* v_x_3552_){
_start:
{
lean_object* v_res_3553_; 
v_res_3553_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0_spec__0(v_00_u03b2_3550_, v_a_3551_, v_x_3552_);
lean_dec(v_x_3552_);
lean_dec(v_a_3551_);
return v_res_3553_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1_spec__2(lean_object* v_00_u03b2_3554_, lean_object* v_a_3555_, lean_object* v_x_3556_){
_start:
{
uint8_t v___x_3557_; 
v___x_3557_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1_spec__2___redArg(v_a_3555_, v_x_3556_);
return v___x_3557_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1_spec__2___boxed(lean_object* v_00_u03b2_3558_, lean_object* v_a_3559_, lean_object* v_x_3560_){
_start:
{
uint8_t v_res_3561_; lean_object* v_r_3562_; 
v_res_3561_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1_spec__2(v_00_u03b2_3558_, v_a_3559_, v_x_3560_);
lean_dec(v_x_3560_);
lean_dec(v_a_3559_);
v_r_3562_ = lean_box(v_res_3561_);
return v_r_3562_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__4(lean_object* v_00_u03b2_3563_, lean_object* v_data_3564_){
_start:
{
lean_object* v___x_3565_; 
v___x_3565_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__4___redArg(v_data_3564_);
return v___x_3565_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__6(lean_object* v_00_u03b2_3566_, lean_object* v_m_3567_, lean_object* v_a_3568_){
_start:
{
lean_object* v___x_3569_; 
v___x_3569_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__6___redArg(v_m_3567_, v_a_3568_);
return v___x_3569_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__6___boxed(lean_object* v_00_u03b2_3570_, lean_object* v_m_3571_, lean_object* v_a_3572_){
_start:
{
lean_object* v_res_3573_; 
v_res_3573_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__6(v_00_u03b2_3570_, v_m_3571_, v_a_3572_);
lean_dec_ref(v_a_3572_);
lean_dec_ref(v_m_3571_);
return v_res_3573_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7(lean_object* v_00_u03b2_3574_, lean_object* v_m_3575_, lean_object* v_a_3576_, lean_object* v_b_3577_){
_start:
{
lean_object* v___x_3578_; 
v___x_3578_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7___redArg(v_m_3575_, v_a_3576_, v_b_3577_);
return v___x_3578_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__4_spec__6(lean_object* v_00_u03b2_3579_, lean_object* v_i_3580_, lean_object* v_source_3581_, lean_object* v_target_3582_){
_start:
{
lean_object* v___x_3583_; 
v___x_3583_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__4_spec__6___redArg(v_i_3580_, v_source_3581_, v_target_3582_);
return v___x_3583_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__6_spec__9(lean_object* v_00_u03b2_3584_, lean_object* v_a_3585_, lean_object* v_x_3586_){
_start:
{
lean_object* v___x_3587_; 
v___x_3587_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__6_spec__9___redArg(v_a_3585_, v_x_3586_);
return v___x_3587_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__6_spec__9___boxed(lean_object* v_00_u03b2_3588_, lean_object* v_a_3589_, lean_object* v_x_3590_){
_start:
{
lean_object* v_res_3591_; 
v_res_3591_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__6_spec__9(v_00_u03b2_3588_, v_a_3589_, v_x_3590_);
lean_dec(v_x_3590_);
lean_dec_ref(v_a_3589_);
return v_res_3591_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__11(lean_object* v_00_u03b2_3592_, lean_object* v_a_3593_, lean_object* v_x_3594_){
_start:
{
uint8_t v___x_3595_; 
v___x_3595_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__11___redArg(v_a_3593_, v_x_3594_);
return v___x_3595_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__11___boxed(lean_object* v_00_u03b2_3596_, lean_object* v_a_3597_, lean_object* v_x_3598_){
_start:
{
uint8_t v_res_3599_; lean_object* v_r_3600_; 
v_res_3599_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__11(v_00_u03b2_3596_, v_a_3597_, v_x_3598_);
lean_dec(v_x_3598_);
lean_dec_ref(v_a_3597_);
v_r_3600_ = lean_box(v_res_3599_);
return v_r_3600_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__12(lean_object* v_00_u03b2_3601_, lean_object* v_data_3602_){
_start:
{
lean_object* v___x_3603_; 
v___x_3603_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__12___redArg(v_data_3602_);
return v___x_3603_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__13(lean_object* v_00_u03b2_3604_, lean_object* v_a_3605_, lean_object* v_b_3606_, lean_object* v_x_3607_){
_start:
{
lean_object* v___x_3608_; 
v___x_3608_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__13___redArg(v_a_3605_, v_b_3606_, v_x_3607_);
return v___x_3608_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__4_spec__6_spec__11(lean_object* v_00_u03b2_3609_, lean_object* v_x_3610_, lean_object* v_x_3611_){
_start:
{
lean_object* v___x_3612_; 
v___x_3612_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__4_spec__6_spec__11___redArg(v_x_3610_, v_x_3611_);
return v___x_3612_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__12_spec__17(lean_object* v_00_u03b2_3613_, lean_object* v_i_3614_, lean_object* v_source_3615_, lean_object* v_target_3616_){
_start:
{
lean_object* v___x_3617_; 
v___x_3617_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__12_spec__17___redArg(v_i_3614_, v_source_3615_, v_target_3616_);
return v___x_3617_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__12_spec__17_spec__18(lean_object* v_00_u03b2_3618_, lean_object* v_x_3619_, lean_object* v_x_3620_){
_start:
{
lean_object* v___x_3621_; 
v___x_3621_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__12_spec__17_spec__18___redArg(v_x_3619_, v_x_3620_);
return v___x_3621_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__0(lean_object* v_msg_3623_, lean_object* v___y_3624_, lean_object* v___y_3625_){
_start:
{
lean_object* v___f_3627_; lean_object* v___x_8561__overap_3628_; lean_object* v___x_3629_; 
v___f_3627_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__0___closed__0));
v___x_8561__overap_3628_ = lean_panic_fn_borrowed(v___f_3627_, v_msg_3623_);
lean_inc(v___y_3625_);
lean_inc_ref(v___y_3624_);
v___x_3629_ = lean_apply_3(v___x_8561__overap_3628_, v___y_3624_, v___y_3625_, lean_box(0));
return v___x_3629_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__0___boxed(lean_object* v_msg_3630_, lean_object* v___y_3631_, lean_object* v___y_3632_, lean_object* v___y_3633_){
_start:
{
lean_object* v_res_3634_; 
v_res_3634_ = l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__0(v_msg_3630_, v___y_3631_, v___y_3632_);
lean_dec(v___y_3632_);
lean_dec_ref(v___y_3631_);
return v_res_3634_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___lam__0(lean_object* v_newDecls_3635_, lean_object* v_newArgs_3636_, lean_object* v_____r_3637_, lean_object* v___y_3638_, lean_object* v___y_3639_, lean_object* v___y_3640_){
_start:
{
lean_object* v___x_3642_; lean_object* v___x_3643_; lean_object* v___x_3644_; 
v___x_3642_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3642_, 0, v_newDecls_3635_);
lean_ctor_set(v___x_3642_, 1, v_newArgs_3636_);
v___x_3643_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3643_, 0, v___x_3642_);
lean_ctor_set(v___x_3643_, 1, v___y_3638_);
v___x_3644_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3644_, 0, v___x_3643_);
return v___x_3644_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___lam__0___boxed(lean_object* v_newDecls_3645_, lean_object* v_newArgs_3646_, lean_object* v_____r_3647_, lean_object* v___y_3648_, lean_object* v___y_3649_, lean_object* v___y_3650_, lean_object* v___y_3651_){
_start:
{
lean_object* v_res_3652_; 
v_res_3652_ = l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___lam__0(v_newDecls_3645_, v_newArgs_3646_, v_____r_3647_, v___y_3648_, v___y_3649_, v___y_3650_);
lean_dec(v___y_3650_);
lean_dec_ref(v___y_3649_);
return v_res_3652_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__6(lean_object* v_cls_3653_, lean_object* v_msg_3654_, lean_object* v___y_3655_, lean_object* v___y_3656_){
_start:
{
lean_object* v_ref_3658_; lean_object* v___x_3659_; lean_object* v_a_3660_; lean_object* v___x_3662_; uint8_t v_isShared_3663_; uint8_t v_isSharedCheck_3704_; 
v_ref_3658_ = lean_ctor_get(v___y_3655_, 5);
v___x_3659_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10(v_msg_3654_, v___y_3655_, v___y_3656_);
v_a_3660_ = lean_ctor_get(v___x_3659_, 0);
v_isSharedCheck_3704_ = !lean_is_exclusive(v___x_3659_);
if (v_isSharedCheck_3704_ == 0)
{
v___x_3662_ = v___x_3659_;
v_isShared_3663_ = v_isSharedCheck_3704_;
goto v_resetjp_3661_;
}
else
{
lean_inc(v_a_3660_);
lean_dec(v___x_3659_);
v___x_3662_ = lean_box(0);
v_isShared_3663_ = v_isSharedCheck_3704_;
goto v_resetjp_3661_;
}
v_resetjp_3661_:
{
lean_object* v___x_3664_; lean_object* v_traceState_3665_; lean_object* v_env_3666_; lean_object* v_nextMacroScope_3667_; lean_object* v_ngen_3668_; lean_object* v_auxDeclNGen_3669_; lean_object* v_cache_3670_; lean_object* v_messages_3671_; lean_object* v_infoState_3672_; lean_object* v_snapshotTasks_3673_; lean_object* v___x_3675_; uint8_t v_isShared_3676_; uint8_t v_isSharedCheck_3703_; 
v___x_3664_ = lean_st_ref_take(v___y_3656_);
v_traceState_3665_ = lean_ctor_get(v___x_3664_, 4);
v_env_3666_ = lean_ctor_get(v___x_3664_, 0);
v_nextMacroScope_3667_ = lean_ctor_get(v___x_3664_, 1);
v_ngen_3668_ = lean_ctor_get(v___x_3664_, 2);
v_auxDeclNGen_3669_ = lean_ctor_get(v___x_3664_, 3);
v_cache_3670_ = lean_ctor_get(v___x_3664_, 5);
v_messages_3671_ = lean_ctor_get(v___x_3664_, 6);
v_infoState_3672_ = lean_ctor_get(v___x_3664_, 7);
v_snapshotTasks_3673_ = lean_ctor_get(v___x_3664_, 8);
v_isSharedCheck_3703_ = !lean_is_exclusive(v___x_3664_);
if (v_isSharedCheck_3703_ == 0)
{
v___x_3675_ = v___x_3664_;
v_isShared_3676_ = v_isSharedCheck_3703_;
goto v_resetjp_3674_;
}
else
{
lean_inc(v_snapshotTasks_3673_);
lean_inc(v_infoState_3672_);
lean_inc(v_messages_3671_);
lean_inc(v_cache_3670_);
lean_inc(v_traceState_3665_);
lean_inc(v_auxDeclNGen_3669_);
lean_inc(v_ngen_3668_);
lean_inc(v_nextMacroScope_3667_);
lean_inc(v_env_3666_);
lean_dec(v___x_3664_);
v___x_3675_ = lean_box(0);
v_isShared_3676_ = v_isSharedCheck_3703_;
goto v_resetjp_3674_;
}
v_resetjp_3674_:
{
uint64_t v_tid_3677_; lean_object* v_traces_3678_; lean_object* v___x_3680_; uint8_t v_isShared_3681_; uint8_t v_isSharedCheck_3702_; 
v_tid_3677_ = lean_ctor_get_uint64(v_traceState_3665_, sizeof(void*)*1);
v_traces_3678_ = lean_ctor_get(v_traceState_3665_, 0);
v_isSharedCheck_3702_ = !lean_is_exclusive(v_traceState_3665_);
if (v_isSharedCheck_3702_ == 0)
{
v___x_3680_ = v_traceState_3665_;
v_isShared_3681_ = v_isSharedCheck_3702_;
goto v_resetjp_3679_;
}
else
{
lean_inc(v_traces_3678_);
lean_dec(v_traceState_3665_);
v___x_3680_ = lean_box(0);
v_isShared_3681_ = v_isSharedCheck_3702_;
goto v_resetjp_3679_;
}
v_resetjp_3679_:
{
lean_object* v___x_3682_; double v___x_3683_; uint8_t v___x_3684_; lean_object* v___x_3685_; lean_object* v___x_3686_; lean_object* v___x_3687_; lean_object* v___x_3688_; lean_object* v___x_3689_; lean_object* v___x_3690_; lean_object* v___x_3692_; 
v___x_3682_ = lean_box(0);
v___x_3683_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6___closed__0);
v___x_3684_ = 0;
v___x_3685_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6___closed__1));
v___x_3686_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3686_, 0, v_cls_3653_);
lean_ctor_set(v___x_3686_, 1, v___x_3682_);
lean_ctor_set(v___x_3686_, 2, v___x_3685_);
lean_ctor_set_float(v___x_3686_, sizeof(void*)*3, v___x_3683_);
lean_ctor_set_float(v___x_3686_, sizeof(void*)*3 + 8, v___x_3683_);
lean_ctor_set_uint8(v___x_3686_, sizeof(void*)*3 + 16, v___x_3684_);
v___x_3687_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6___closed__2));
v___x_3688_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3688_, 0, v___x_3686_);
lean_ctor_set(v___x_3688_, 1, v_a_3660_);
lean_ctor_set(v___x_3688_, 2, v___x_3687_);
lean_inc(v_ref_3658_);
v___x_3689_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3689_, 0, v_ref_3658_);
lean_ctor_set(v___x_3689_, 1, v___x_3688_);
v___x_3690_ = l_Lean_PersistentArray_push___redArg(v_traces_3678_, v___x_3689_);
if (v_isShared_3681_ == 0)
{
lean_ctor_set(v___x_3680_, 0, v___x_3690_);
v___x_3692_ = v___x_3680_;
goto v_reusejp_3691_;
}
else
{
lean_object* v_reuseFailAlloc_3701_; 
v_reuseFailAlloc_3701_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3701_, 0, v___x_3690_);
lean_ctor_set_uint64(v_reuseFailAlloc_3701_, sizeof(void*)*1, v_tid_3677_);
v___x_3692_ = v_reuseFailAlloc_3701_;
goto v_reusejp_3691_;
}
v_reusejp_3691_:
{
lean_object* v___x_3694_; 
if (v_isShared_3676_ == 0)
{
lean_ctor_set(v___x_3675_, 4, v___x_3692_);
v___x_3694_ = v___x_3675_;
goto v_reusejp_3693_;
}
else
{
lean_object* v_reuseFailAlloc_3700_; 
v_reuseFailAlloc_3700_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3700_, 0, v_env_3666_);
lean_ctor_set(v_reuseFailAlloc_3700_, 1, v_nextMacroScope_3667_);
lean_ctor_set(v_reuseFailAlloc_3700_, 2, v_ngen_3668_);
lean_ctor_set(v_reuseFailAlloc_3700_, 3, v_auxDeclNGen_3669_);
lean_ctor_set(v_reuseFailAlloc_3700_, 4, v___x_3692_);
lean_ctor_set(v_reuseFailAlloc_3700_, 5, v_cache_3670_);
lean_ctor_set(v_reuseFailAlloc_3700_, 6, v_messages_3671_);
lean_ctor_set(v_reuseFailAlloc_3700_, 7, v_infoState_3672_);
lean_ctor_set(v_reuseFailAlloc_3700_, 8, v_snapshotTasks_3673_);
v___x_3694_ = v_reuseFailAlloc_3700_;
goto v_reusejp_3693_;
}
v_reusejp_3693_:
{
lean_object* v___x_3695_; lean_object* v___x_3696_; lean_object* v___x_3698_; 
v___x_3695_ = lean_st_ref_set(v___y_3656_, v___x_3694_);
v___x_3696_ = lean_box(0);
if (v_isShared_3663_ == 0)
{
lean_ctor_set(v___x_3662_, 0, v___x_3696_);
v___x_3698_ = v___x_3662_;
goto v_reusejp_3697_;
}
else
{
lean_object* v_reuseFailAlloc_3699_; 
v_reuseFailAlloc_3699_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3699_, 0, v___x_3696_);
v___x_3698_ = v_reuseFailAlloc_3699_;
goto v_reusejp_3697_;
}
v_reusejp_3697_:
{
return v___x_3698_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__6___boxed(lean_object* v_cls_3705_, lean_object* v_msg_3706_, lean_object* v___y_3707_, lean_object* v___y_3708_, lean_object* v___y_3709_){
_start:
{
lean_object* v_res_3710_; 
v_res_3710_ = l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__6(v_cls_3705_, v_msg_3706_, v___y_3707_, v___y_3708_);
lean_dec(v___y_3708_);
lean_dec_ref(v___y_3707_);
return v_res_3710_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__4(size_t v_sz_3711_, size_t v_i_3712_, lean_object* v_bs_3713_){
_start:
{
uint8_t v___x_3714_; 
v___x_3714_ = lean_usize_dec_lt(v_i_3712_, v_sz_3711_);
if (v___x_3714_ == 0)
{
return v_bs_3713_;
}
else
{
lean_object* v_v_3715_; lean_object* v___x_3716_; lean_object* v_bs_x27_3717_; lean_object* v___x_3718_; lean_object* v___x_3719_; size_t v___x_3720_; size_t v___x_3721_; lean_object* v___x_3722_; 
v_v_3715_ = lean_array_uget(v_bs_3713_, v_i_3712_);
v___x_3716_ = lean_unsigned_to_nat(0u);
v_bs_x27_3717_ = lean_array_uset(v_bs_3713_, v_i_3712_, v___x_3716_);
v___x_3718_ = l_Lean_LocalDecl_fvarId(v_v_3715_);
lean_dec(v_v_3715_);
v___x_3719_ = l_Lean_mkFVar(v___x_3718_);
v___x_3720_ = ((size_t)1ULL);
v___x_3721_ = lean_usize_add(v_i_3712_, v___x_3720_);
v___x_3722_ = lean_array_uset(v_bs_x27_3717_, v_i_3712_, v___x_3719_);
v_i_3712_ = v___x_3721_;
v_bs_3713_ = v___x_3722_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__4___boxed(lean_object* v_sz_3724_, lean_object* v_i_3725_, lean_object* v_bs_3726_){
_start:
{
size_t v_sz_boxed_3727_; size_t v_i_boxed_3728_; lean_object* v_res_3729_; 
v_sz_boxed_3727_ = lean_unbox_usize(v_sz_3724_);
lean_dec(v_sz_3724_);
v_i_boxed_3728_ = lean_unbox_usize(v_i_3725_);
lean_dec(v_i_3725_);
v_res_3729_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__4(v_sz_boxed_3727_, v_i_boxed_3728_, v_bs_3726_);
return v_res_3729_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__3(lean_object* v___x_3730_, lean_object* v_as_3731_, size_t v_sz_3732_, size_t v_i_3733_, lean_object* v_b_3734_, lean_object* v___y_3735_, lean_object* v___y_3736_, lean_object* v___y_3737_){
_start:
{
uint8_t v___x_3739_; 
v___x_3739_ = lean_usize_dec_lt(v_i_3733_, v_sz_3732_);
if (v___x_3739_ == 0)
{
lean_object* v___x_3740_; lean_object* v___x_3741_; 
lean_dec_ref(v___x_3730_);
v___x_3740_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3740_, 0, v_b_3734_);
lean_ctor_set(v___x_3740_, 1, v___y_3735_);
v___x_3741_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3741_, 0, v___x_3740_);
return v___x_3741_;
}
else
{
lean_object* v_a_3742_; lean_object* v___x_3743_; lean_object* v___x_3744_; 
v_a_3742_ = lean_array_uget_borrowed(v_as_3731_, v_i_3733_);
v___x_3743_ = l_Lean_LocalDecl_fvarId(v_a_3742_);
lean_inc_ref(v___x_3730_);
v___x_3744_ = l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit(v___x_3730_, v___x_3743_, v___y_3735_, v___y_3736_, v___y_3737_);
lean_dec(v___x_3743_);
if (lean_obj_tag(v___x_3744_) == 0)
{
lean_object* v_a_3745_; lean_object* v_snd_3746_; lean_object* v___x_3747_; size_t v___x_3748_; size_t v___x_3749_; 
v_a_3745_ = lean_ctor_get(v___x_3744_, 0);
lean_inc(v_a_3745_);
lean_dec_ref(v___x_3744_);
v_snd_3746_ = lean_ctor_get(v_a_3745_, 1);
lean_inc(v_snd_3746_);
lean_dec(v_a_3745_);
v___x_3747_ = lean_box(0);
v___x_3748_ = ((size_t)1ULL);
v___x_3749_ = lean_usize_add(v_i_3733_, v___x_3748_);
v_i_3733_ = v___x_3749_;
v_b_3734_ = v___x_3747_;
v___y_3735_ = v_snd_3746_;
goto _start;
}
else
{
lean_dec_ref(v___x_3730_);
return v___x_3744_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__3___boxed(lean_object* v___x_3751_, lean_object* v_as_3752_, lean_object* v_sz_3753_, lean_object* v_i_3754_, lean_object* v_b_3755_, lean_object* v___y_3756_, lean_object* v___y_3757_, lean_object* v___y_3758_, lean_object* v___y_3759_){
_start:
{
size_t v_sz_boxed_3760_; size_t v_i_boxed_3761_; lean_object* v_res_3762_; 
v_sz_boxed_3760_ = lean_unbox_usize(v_sz_3753_);
lean_dec(v_sz_3753_);
v_i_boxed_3761_ = lean_unbox_usize(v_i_3754_);
lean_dec(v_i_3754_);
v_res_3762_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__3(v___x_3751_, v_as_3752_, v_sz_boxed_3760_, v_i_boxed_3761_, v_b_3755_, v___y_3756_, v___y_3757_, v___y_3758_);
lean_dec(v___y_3758_);
lean_dec_ref(v___y_3757_);
lean_dec_ref(v_as_3752_);
return v_res_3762_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__5(lean_object* v_a_3763_, lean_object* v_a_3764_){
_start:
{
if (lean_obj_tag(v_a_3763_) == 0)
{
lean_object* v___x_3765_; 
v___x_3765_ = l_List_reverse___redArg(v_a_3764_);
return v___x_3765_;
}
else
{
lean_object* v_head_3766_; lean_object* v_tail_3767_; lean_object* v___x_3769_; uint8_t v_isShared_3770_; uint8_t v_isSharedCheck_3776_; 
v_head_3766_ = lean_ctor_get(v_a_3763_, 0);
v_tail_3767_ = lean_ctor_get(v_a_3763_, 1);
v_isSharedCheck_3776_ = !lean_is_exclusive(v_a_3763_);
if (v_isSharedCheck_3776_ == 0)
{
v___x_3769_ = v_a_3763_;
v_isShared_3770_ = v_isSharedCheck_3776_;
goto v_resetjp_3768_;
}
else
{
lean_inc(v_tail_3767_);
lean_inc(v_head_3766_);
lean_dec(v_a_3763_);
v___x_3769_ = lean_box(0);
v_isShared_3770_ = v_isSharedCheck_3776_;
goto v_resetjp_3768_;
}
v_resetjp_3768_:
{
lean_object* v___x_3771_; lean_object* v___x_3773_; 
v___x_3771_ = l_Lean_MessageData_ofExpr(v_head_3766_);
if (v_isShared_3770_ == 0)
{
lean_ctor_set(v___x_3769_, 1, v_a_3764_);
lean_ctor_set(v___x_3769_, 0, v___x_3771_);
v___x_3773_ = v___x_3769_;
goto v_reusejp_3772_;
}
else
{
lean_object* v_reuseFailAlloc_3775_; 
v_reuseFailAlloc_3775_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3775_, 0, v___x_3771_);
lean_ctor_set(v_reuseFailAlloc_3775_, 1, v_a_3764_);
v___x_3773_ = v_reuseFailAlloc_3775_;
goto v_reusejp_3772_;
}
v_reusejp_3772_:
{
v_a_3763_ = v_tail_3767_;
v_a_3764_ = v___x_3773_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__1_spec__1___redArg(lean_object* v_a_3777_, lean_object* v_b_3778_, lean_object* v_x_3779_){
_start:
{
if (lean_obj_tag(v_x_3779_) == 0)
{
lean_dec(v_b_3778_);
lean_dec(v_a_3777_);
return v_x_3779_;
}
else
{
lean_object* v_key_3780_; lean_object* v_value_3781_; lean_object* v_tail_3782_; lean_object* v___x_3784_; uint8_t v_isShared_3785_; uint8_t v_isSharedCheck_3794_; 
v_key_3780_ = lean_ctor_get(v_x_3779_, 0);
v_value_3781_ = lean_ctor_get(v_x_3779_, 1);
v_tail_3782_ = lean_ctor_get(v_x_3779_, 2);
v_isSharedCheck_3794_ = !lean_is_exclusive(v_x_3779_);
if (v_isSharedCheck_3794_ == 0)
{
v___x_3784_ = v_x_3779_;
v_isShared_3785_ = v_isSharedCheck_3794_;
goto v_resetjp_3783_;
}
else
{
lean_inc(v_tail_3782_);
lean_inc(v_value_3781_);
lean_inc(v_key_3780_);
lean_dec(v_x_3779_);
v___x_3784_ = lean_box(0);
v_isShared_3785_ = v_isSharedCheck_3794_;
goto v_resetjp_3783_;
}
v_resetjp_3783_:
{
uint8_t v___x_3786_; 
v___x_3786_ = l_Lean_instBEqFVarId_beq(v_key_3780_, v_a_3777_);
if (v___x_3786_ == 0)
{
lean_object* v___x_3787_; lean_object* v___x_3789_; 
v___x_3787_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__1_spec__1___redArg(v_a_3777_, v_b_3778_, v_tail_3782_);
if (v_isShared_3785_ == 0)
{
lean_ctor_set(v___x_3784_, 2, v___x_3787_);
v___x_3789_ = v___x_3784_;
goto v_reusejp_3788_;
}
else
{
lean_object* v_reuseFailAlloc_3790_; 
v_reuseFailAlloc_3790_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3790_, 0, v_key_3780_);
lean_ctor_set(v_reuseFailAlloc_3790_, 1, v_value_3781_);
lean_ctor_set(v_reuseFailAlloc_3790_, 2, v___x_3787_);
v___x_3789_ = v_reuseFailAlloc_3790_;
goto v_reusejp_3788_;
}
v_reusejp_3788_:
{
return v___x_3789_;
}
}
else
{
lean_object* v___x_3792_; 
lean_dec(v_value_3781_);
lean_dec(v_key_3780_);
if (v_isShared_3785_ == 0)
{
lean_ctor_set(v___x_3784_, 1, v_b_3778_);
lean_ctor_set(v___x_3784_, 0, v_a_3777_);
v___x_3792_ = v___x_3784_;
goto v_reusejp_3791_;
}
else
{
lean_object* v_reuseFailAlloc_3793_; 
v_reuseFailAlloc_3793_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3793_, 0, v_a_3777_);
lean_ctor_set(v_reuseFailAlloc_3793_, 1, v_b_3778_);
lean_ctor_set(v_reuseFailAlloc_3793_, 2, v_tail_3782_);
v___x_3792_ = v_reuseFailAlloc_3793_;
goto v_reusejp_3791_;
}
v_reusejp_3791_:
{
return v___x_3792_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__1___redArg(lean_object* v_m_3795_, lean_object* v_a_3796_, lean_object* v_b_3797_){
_start:
{
lean_object* v_size_3798_; lean_object* v_buckets_3799_; lean_object* v___x_3801_; uint8_t v_isShared_3802_; uint8_t v_isSharedCheck_3842_; 
v_size_3798_ = lean_ctor_get(v_m_3795_, 0);
v_buckets_3799_ = lean_ctor_get(v_m_3795_, 1);
v_isSharedCheck_3842_ = !lean_is_exclusive(v_m_3795_);
if (v_isSharedCheck_3842_ == 0)
{
v___x_3801_ = v_m_3795_;
v_isShared_3802_ = v_isSharedCheck_3842_;
goto v_resetjp_3800_;
}
else
{
lean_inc(v_buckets_3799_);
lean_inc(v_size_3798_);
lean_dec(v_m_3795_);
v___x_3801_ = lean_box(0);
v_isShared_3802_ = v_isSharedCheck_3842_;
goto v_resetjp_3800_;
}
v_resetjp_3800_:
{
lean_object* v___x_3803_; uint64_t v___x_3804_; uint64_t v___x_3805_; uint64_t v___x_3806_; uint64_t v_fold_3807_; uint64_t v___x_3808_; uint64_t v___x_3809_; uint64_t v___x_3810_; size_t v___x_3811_; size_t v___x_3812_; size_t v___x_3813_; size_t v___x_3814_; size_t v___x_3815_; lean_object* v_bkt_3816_; uint8_t v___x_3817_; 
v___x_3803_ = lean_array_get_size(v_buckets_3799_);
v___x_3804_ = l_Lean_instHashableFVarId_hash(v_a_3796_);
v___x_3805_ = 32ULL;
v___x_3806_ = lean_uint64_shift_right(v___x_3804_, v___x_3805_);
v_fold_3807_ = lean_uint64_xor(v___x_3804_, v___x_3806_);
v___x_3808_ = 16ULL;
v___x_3809_ = lean_uint64_shift_right(v_fold_3807_, v___x_3808_);
v___x_3810_ = lean_uint64_xor(v_fold_3807_, v___x_3809_);
v___x_3811_ = lean_uint64_to_usize(v___x_3810_);
v___x_3812_ = lean_usize_of_nat(v___x_3803_);
v___x_3813_ = ((size_t)1ULL);
v___x_3814_ = lean_usize_sub(v___x_3812_, v___x_3813_);
v___x_3815_ = lean_usize_land(v___x_3811_, v___x_3814_);
v_bkt_3816_ = lean_array_uget_borrowed(v_buckets_3799_, v___x_3815_);
v___x_3817_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1_spec__2___redArg(v_a_3796_, v_bkt_3816_);
if (v___x_3817_ == 0)
{
lean_object* v___x_3818_; lean_object* v_size_x27_3819_; lean_object* v___x_3820_; lean_object* v_buckets_x27_3821_; lean_object* v___x_3822_; lean_object* v___x_3823_; lean_object* v___x_3824_; lean_object* v___x_3825_; lean_object* v___x_3826_; uint8_t v___x_3827_; 
v___x_3818_ = lean_unsigned_to_nat(1u);
v_size_x27_3819_ = lean_nat_add(v_size_3798_, v___x_3818_);
lean_dec(v_size_3798_);
lean_inc(v_bkt_3816_);
v___x_3820_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3820_, 0, v_a_3796_);
lean_ctor_set(v___x_3820_, 1, v_b_3797_);
lean_ctor_set(v___x_3820_, 2, v_bkt_3816_);
v_buckets_x27_3821_ = lean_array_uset(v_buckets_3799_, v___x_3815_, v___x_3820_);
v___x_3822_ = lean_unsigned_to_nat(4u);
v___x_3823_ = lean_nat_mul(v_size_x27_3819_, v___x_3822_);
v___x_3824_ = lean_unsigned_to_nat(3u);
v___x_3825_ = lean_nat_div(v___x_3823_, v___x_3824_);
lean_dec(v___x_3823_);
v___x_3826_ = lean_array_get_size(v_buckets_x27_3821_);
v___x_3827_ = lean_nat_dec_le(v___x_3825_, v___x_3826_);
lean_dec(v___x_3825_);
if (v___x_3827_ == 0)
{
lean_object* v_val_3828_; lean_object* v___x_3830_; 
v_val_3828_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__4___redArg(v_buckets_x27_3821_);
if (v_isShared_3802_ == 0)
{
lean_ctor_set(v___x_3801_, 1, v_val_3828_);
lean_ctor_set(v___x_3801_, 0, v_size_x27_3819_);
v___x_3830_ = v___x_3801_;
goto v_reusejp_3829_;
}
else
{
lean_object* v_reuseFailAlloc_3831_; 
v_reuseFailAlloc_3831_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3831_, 0, v_size_x27_3819_);
lean_ctor_set(v_reuseFailAlloc_3831_, 1, v_val_3828_);
v___x_3830_ = v_reuseFailAlloc_3831_;
goto v_reusejp_3829_;
}
v_reusejp_3829_:
{
return v___x_3830_;
}
}
else
{
lean_object* v___x_3833_; 
if (v_isShared_3802_ == 0)
{
lean_ctor_set(v___x_3801_, 1, v_buckets_x27_3821_);
lean_ctor_set(v___x_3801_, 0, v_size_x27_3819_);
v___x_3833_ = v___x_3801_;
goto v_reusejp_3832_;
}
else
{
lean_object* v_reuseFailAlloc_3834_; 
v_reuseFailAlloc_3834_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3834_, 0, v_size_x27_3819_);
lean_ctor_set(v_reuseFailAlloc_3834_, 1, v_buckets_x27_3821_);
v___x_3833_ = v_reuseFailAlloc_3834_;
goto v_reusejp_3832_;
}
v_reusejp_3832_:
{
return v___x_3833_;
}
}
}
else
{
lean_object* v___x_3835_; lean_object* v_buckets_x27_3836_; lean_object* v___x_3837_; lean_object* v___x_3838_; lean_object* v___x_3840_; 
lean_inc(v_bkt_3816_);
v___x_3835_ = lean_box(0);
v_buckets_x27_3836_ = lean_array_uset(v_buckets_3799_, v___x_3815_, v___x_3835_);
v___x_3837_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__1_spec__1___redArg(v_a_3796_, v_b_3797_, v_bkt_3816_);
v___x_3838_ = lean_array_uset(v_buckets_x27_3836_, v___x_3815_, v___x_3837_);
if (v_isShared_3802_ == 0)
{
lean_ctor_set(v___x_3801_, 1, v___x_3838_);
v___x_3840_ = v___x_3801_;
goto v_reusejp_3839_;
}
else
{
lean_object* v_reuseFailAlloc_3841_; 
v_reuseFailAlloc_3841_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3841_, 0, v_size_3798_);
lean_ctor_set(v_reuseFailAlloc_3841_, 1, v___x_3838_);
v___x_3840_ = v_reuseFailAlloc_3841_;
goto v_reusejp_3839_;
}
v_reusejp_3839_:
{
return v___x_3840_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__2___redArg(lean_object* v_as_3843_, size_t v_sz_3844_, size_t v_i_3845_, lean_object* v_b_3846_){
_start:
{
uint8_t v___x_3848_; 
v___x_3848_ = lean_usize_dec_lt(v_i_3845_, v_sz_3844_);
if (v___x_3848_ == 0)
{
lean_object* v___x_3849_; 
v___x_3849_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3849_, 0, v_b_3846_);
return v___x_3849_;
}
else
{
lean_object* v_snd_3850_; lean_object* v_fst_3851_; lean_object* v___x_3853_; uint8_t v_isShared_3854_; uint8_t v_isSharedCheck_3886_; 
v_snd_3850_ = lean_ctor_get(v_b_3846_, 1);
v_fst_3851_ = lean_ctor_get(v_b_3846_, 0);
v_isSharedCheck_3886_ = !lean_is_exclusive(v_b_3846_);
if (v_isSharedCheck_3886_ == 0)
{
v___x_3853_ = v_b_3846_;
v_isShared_3854_ = v_isSharedCheck_3886_;
goto v_resetjp_3852_;
}
else
{
lean_inc(v_snd_3850_);
lean_inc(v_fst_3851_);
lean_dec(v_b_3846_);
v___x_3853_ = lean_box(0);
v_isShared_3854_ = v_isSharedCheck_3886_;
goto v_resetjp_3852_;
}
v_resetjp_3852_:
{
lean_object* v_array_3855_; lean_object* v_start_3856_; lean_object* v_stop_3857_; uint8_t v___x_3858_; 
v_array_3855_ = lean_ctor_get(v_snd_3850_, 0);
v_start_3856_ = lean_ctor_get(v_snd_3850_, 1);
v_stop_3857_ = lean_ctor_get(v_snd_3850_, 2);
v___x_3858_ = lean_nat_dec_lt(v_start_3856_, v_stop_3857_);
if (v___x_3858_ == 0)
{
lean_object* v___x_3860_; 
if (v_isShared_3854_ == 0)
{
v___x_3860_ = v___x_3853_;
goto v_reusejp_3859_;
}
else
{
lean_object* v_reuseFailAlloc_3862_; 
v_reuseFailAlloc_3862_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3862_, 0, v_fst_3851_);
lean_ctor_set(v_reuseFailAlloc_3862_, 1, v_snd_3850_);
v___x_3860_ = v_reuseFailAlloc_3862_;
goto v_reusejp_3859_;
}
v_reusejp_3859_:
{
lean_object* v___x_3861_; 
v___x_3861_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3861_, 0, v___x_3860_);
return v___x_3861_;
}
}
else
{
lean_object* v___x_3864_; uint8_t v_isShared_3865_; uint8_t v_isSharedCheck_3882_; 
lean_inc(v_stop_3857_);
lean_inc(v_start_3856_);
lean_inc_ref(v_array_3855_);
v_isSharedCheck_3882_ = !lean_is_exclusive(v_snd_3850_);
if (v_isSharedCheck_3882_ == 0)
{
lean_object* v_unused_3883_; lean_object* v_unused_3884_; lean_object* v_unused_3885_; 
v_unused_3883_ = lean_ctor_get(v_snd_3850_, 2);
lean_dec(v_unused_3883_);
v_unused_3884_ = lean_ctor_get(v_snd_3850_, 1);
lean_dec(v_unused_3884_);
v_unused_3885_ = lean_ctor_get(v_snd_3850_, 0);
lean_dec(v_unused_3885_);
v___x_3864_ = v_snd_3850_;
v_isShared_3865_ = v_isSharedCheck_3882_;
goto v_resetjp_3863_;
}
else
{
lean_dec(v_snd_3850_);
v___x_3864_ = lean_box(0);
v_isShared_3865_ = v_isSharedCheck_3882_;
goto v_resetjp_3863_;
}
v_resetjp_3863_:
{
lean_object* v_a_3866_; lean_object* v___x_3867_; lean_object* v___x_3868_; lean_object* v___x_3869_; lean_object* v___x_3871_; 
v_a_3866_ = lean_array_uget_borrowed(v_as_3843_, v_i_3845_);
v___x_3867_ = lean_array_fget(v_array_3855_, v_start_3856_);
v___x_3868_ = lean_unsigned_to_nat(1u);
v___x_3869_ = lean_nat_add(v_start_3856_, v___x_3868_);
lean_dec(v_start_3856_);
if (v_isShared_3865_ == 0)
{
lean_ctor_set(v___x_3864_, 1, v___x_3869_);
v___x_3871_ = v___x_3864_;
goto v_reusejp_3870_;
}
else
{
lean_object* v_reuseFailAlloc_3881_; 
v_reuseFailAlloc_3881_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3881_, 0, v_array_3855_);
lean_ctor_set(v_reuseFailAlloc_3881_, 1, v___x_3869_);
lean_ctor_set(v_reuseFailAlloc_3881_, 2, v_stop_3857_);
v___x_3871_ = v_reuseFailAlloc_3881_;
goto v_reusejp_3870_;
}
v_reusejp_3870_:
{
lean_object* v___x_3872_; lean_object* v___x_3874_; 
v___x_3872_ = l_Lean_LocalDecl_fvarId(v_a_3866_);
lean_inc(v_a_3866_);
if (v_isShared_3854_ == 0)
{
lean_ctor_set(v___x_3853_, 1, v___x_3867_);
lean_ctor_set(v___x_3853_, 0, v_a_3866_);
v___x_3874_ = v___x_3853_;
goto v_reusejp_3873_;
}
else
{
lean_object* v_reuseFailAlloc_3880_; 
v_reuseFailAlloc_3880_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3880_, 0, v_a_3866_);
lean_ctor_set(v_reuseFailAlloc_3880_, 1, v___x_3867_);
v___x_3874_ = v_reuseFailAlloc_3880_;
goto v_reusejp_3873_;
}
v_reusejp_3873_:
{
lean_object* v___x_3875_; lean_object* v___x_3876_; size_t v___x_3877_; size_t v___x_3878_; 
v___x_3875_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__1___redArg(v_fst_3851_, v___x_3872_, v___x_3874_);
v___x_3876_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3876_, 0, v___x_3875_);
lean_ctor_set(v___x_3876_, 1, v___x_3871_);
v___x_3877_ = ((size_t)1ULL);
v___x_3878_ = lean_usize_add(v_i_3845_, v___x_3877_);
v_i_3845_ = v___x_3878_;
v_b_3846_ = v___x_3876_;
goto _start;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__2___redArg___boxed(lean_object* v_as_3887_, lean_object* v_sz_3888_, lean_object* v_i_3889_, lean_object* v_b_3890_, lean_object* v___y_3891_){
_start:
{
size_t v_sz_boxed_3892_; size_t v_i_boxed_3893_; lean_object* v_res_3894_; 
v_sz_boxed_3892_ = lean_unbox_usize(v_sz_3888_);
lean_dec(v_sz_3888_);
v_i_boxed_3893_ = lean_unbox_usize(v_i_3889_);
lean_dec(v_i_3889_);
v_res_3894_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__2___redArg(v_as_3887_, v_sz_boxed_3892_, v_i_boxed_3893_, v_b_3890_);
lean_dec_ref(v_as_3887_);
return v_res_3894_;
}
}
static lean_object* _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__2(void){
_start:
{
lean_object* v___x_3897_; lean_object* v___x_3898_; lean_object* v___x_3899_; lean_object* v___x_3900_; lean_object* v___x_3901_; lean_object* v___x_3902_; 
v___x_3897_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__1));
v___x_3898_ = lean_unsigned_to_nat(2u);
v___x_3899_ = lean_unsigned_to_nat(366u);
v___x_3900_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__0));
v___x_3901_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__2));
v___x_3902_ = l_mkPanicMessageWithDecl(v___x_3901_, v___x_3900_, v___x_3899_, v___x_3898_, v___x_3897_);
return v___x_3902_;
}
}
static lean_object* _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__4(void){
_start:
{
lean_object* v___x_3904_; lean_object* v___x_3905_; lean_object* v___x_3906_; lean_object* v___x_3907_; lean_object* v___x_3908_; lean_object* v___x_3909_; 
v___x_3904_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__3));
v___x_3905_ = lean_unsigned_to_nat(2u);
v___x_3906_ = lean_unsigned_to_nat(367u);
v___x_3907_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__0));
v___x_3908_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__2));
v___x_3909_ = l_mkPanicMessageWithDecl(v___x_3908_, v___x_3907_, v___x_3906_, v___x_3905_, v___x_3904_);
return v___x_3909_;
}
}
static lean_object* _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__5(void){
_start:
{
lean_object* v___x_3910_; lean_object* v___x_3911_; lean_object* v___x_3912_; 
v___x_3910_ = lean_box(0);
v___x_3911_ = lean_unsigned_to_nat(16u);
v___x_3912_ = lean_mk_array(v___x_3911_, v___x_3910_);
return v___x_3912_;
}
}
static lean_object* _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__6(void){
_start:
{
lean_object* v___x_3913_; lean_object* v___x_3914_; lean_object* v___x_3915_; 
v___x_3913_ = lean_obj_once(&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__5, &l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__5_once, _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__5);
v___x_3914_ = lean_unsigned_to_nat(0u);
v___x_3915_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3915_, 0, v___x_3914_);
lean_ctor_set(v___x_3915_, 1, v___x_3913_);
return v___x_3915_;
}
}
static lean_object* _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__8(void){
_start:
{
lean_object* v___x_3917_; lean_object* v___x_3918_; 
v___x_3917_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__7));
v___x_3918_ = l_Lean_stringToMessageData(v___x_3917_);
return v___x_3918_;
}
}
static lean_object* _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__10(void){
_start:
{
lean_object* v___x_3920_; lean_object* v___x_3921_; 
v___x_3920_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__9));
v___x_3921_ = l_Lean_stringToMessageData(v___x_3920_);
return v___x_3921_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls(lean_object* v_sortedDecls_3922_, lean_object* v_sortedArgs_3923_, lean_object* v_toSortDecls_3924_, lean_object* v_toSortArgs_3925_, lean_object* v_a_3926_, lean_object* v_a_3927_){
_start:
{
lean_object* v___y_3930_; lean_object* v___y_3949_; lean_object* v___y_3950_; lean_object* v___y_3951_; lean_object* v___y_3952_; lean_object* v_snd_3953_; lean_object* v___x_3955_; lean_object* v___x_3956_; uint8_t v___x_3957_; 
v___x_3955_ = lean_array_get_size(v_sortedDecls_3922_);
v___x_3956_ = lean_array_get_size(v_sortedArgs_3923_);
v___x_3957_ = lean_nat_dec_eq(v___x_3955_, v___x_3956_);
if (v___x_3957_ == 0)
{
lean_object* v___x_3958_; lean_object* v___x_3959_; 
lean_dec_ref(v_toSortArgs_3925_);
lean_dec_ref(v_sortedArgs_3923_);
lean_dec_ref(v_sortedDecls_3922_);
v___x_3958_ = lean_obj_once(&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__2, &l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__2_once, _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__2);
v___x_3959_ = l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__0(v___x_3958_, v_a_3926_, v_a_3927_);
return v___x_3959_;
}
else
{
lean_object* v___x_3960_; lean_object* v___x_3961_; uint8_t v___x_3962_; 
v___x_3960_ = lean_array_get_size(v_toSortDecls_3924_);
v___x_3961_ = lean_array_get_size(v_toSortArgs_3925_);
v___x_3962_ = lean_nat_dec_eq(v___x_3960_, v___x_3961_);
if (v___x_3962_ == 0)
{
lean_object* v___x_3963_; lean_object* v___x_3964_; 
lean_dec_ref(v_toSortArgs_3925_);
lean_dec_ref(v_sortedArgs_3923_);
lean_dec_ref(v_sortedDecls_3922_);
v___x_3963_ = lean_obj_once(&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__4, &l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__4_once, _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__4);
v___x_3964_ = l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__0(v___x_3963_, v_a_3926_, v_a_3927_);
return v___x_3964_;
}
else
{
lean_object* v___x_3965_; uint8_t v___x_3966_; 
v___x_3965_ = lean_unsigned_to_nat(0u);
v___x_3966_ = lean_nat_dec_eq(v___x_3960_, v___x_3965_);
if (v___x_3966_ == 0)
{
lean_object* v_options_3967_; lean_object* v_inheritedTraceOptions_3968_; uint8_t v_hasTrace_3969_; lean_object* v_cls_3970_; lean_object* v___y_3972_; lean_object* v___y_3973_; 
v_options_3967_ = lean_ctor_get(v_a_3926_, 2);
v_inheritedTraceOptions_3968_ = lean_ctor_get(v_a_3926_, 13);
v_hasTrace_3969_ = lean_ctor_get_uint8(v_options_3967_, sizeof(void*)*1);
v_cls_3970_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__10));
if (v_hasTrace_3969_ == 0)
{
v___y_3972_ = v_a_3926_;
v___y_3973_ = v_a_3927_;
goto v___jp_3971_;
}
else
{
lean_object* v___x_4074_; uint8_t v___x_4075_; 
v___x_4074_ = lean_obj_once(&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__13, &l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__13_once, _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__13);
v___x_4075_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3968_, v_options_3967_, v___x_4074_);
if (v___x_4075_ == 0)
{
v___y_3972_ = v_a_3926_;
v___y_3973_ = v_a_3927_;
goto v___jp_3971_;
}
else
{
lean_object* v___x_4076_; lean_object* v___x_4077_; 
v___x_4076_ = lean_obj_once(&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__10, &l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__10_once, _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__10);
v___x_4077_ = l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__6(v_cls_3970_, v___x_4076_, v_a_3926_, v_a_3927_);
if (lean_obj_tag(v___x_4077_) == 0)
{
lean_dec_ref(v___x_4077_);
v___y_3972_ = v_a_3926_;
v___y_3973_ = v_a_3927_;
goto v___jp_3971_;
}
else
{
lean_object* v_a_4078_; lean_object* v___x_4080_; uint8_t v_isShared_4081_; uint8_t v_isSharedCheck_4085_; 
lean_dec_ref(v_toSortArgs_3925_);
lean_dec_ref(v_sortedArgs_3923_);
lean_dec_ref(v_sortedDecls_3922_);
v_a_4078_ = lean_ctor_get(v___x_4077_, 0);
v_isSharedCheck_4085_ = !lean_is_exclusive(v___x_4077_);
if (v_isSharedCheck_4085_ == 0)
{
v___x_4080_ = v___x_4077_;
v_isShared_4081_ = v_isSharedCheck_4085_;
goto v_resetjp_4079_;
}
else
{
lean_inc(v_a_4078_);
lean_dec(v___x_4077_);
v___x_4080_ = lean_box(0);
v_isShared_4081_ = v_isSharedCheck_4085_;
goto v_resetjp_4079_;
}
v_resetjp_4079_:
{
lean_object* v___x_4083_; 
if (v_isShared_4081_ == 0)
{
v___x_4083_ = v___x_4080_;
goto v_reusejp_4082_;
}
else
{
lean_object* v_reuseFailAlloc_4084_; 
v_reuseFailAlloc_4084_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4084_, 0, v_a_4078_);
v___x_4083_ = v_reuseFailAlloc_4084_;
goto v_reusejp_4082_;
}
v_reusejp_4082_:
{
return v___x_4083_;
}
}
}
}
}
v___jp_3971_:
{
lean_object* v___x_3974_; lean_object* v___x_3975_; lean_object* v___x_3976_; size_t v_sz_3977_; size_t v___x_3978_; lean_object* v___x_3979_; 
v___x_3974_ = lean_obj_once(&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__6, &l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__6_once, _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__6);
v___x_3975_ = l_Array_toSubarray___redArg(v_sortedArgs_3923_, v___x_3965_, v___x_3956_);
v___x_3976_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3976_, 0, v___x_3974_);
lean_ctor_set(v___x_3976_, 1, v___x_3975_);
v_sz_3977_ = lean_array_size(v_sortedDecls_3922_);
v___x_3978_ = ((size_t)0ULL);
v___x_3979_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__2___redArg(v_sortedDecls_3922_, v_sz_3977_, v___x_3978_, v___x_3976_);
if (lean_obj_tag(v___x_3979_) == 0)
{
lean_object* v_a_3980_; lean_object* v_fst_3981_; lean_object* v___x_3983_; uint8_t v_isShared_3984_; uint8_t v_isSharedCheck_4064_; 
v_a_3980_ = lean_ctor_get(v___x_3979_, 0);
lean_inc(v_a_3980_);
lean_dec_ref(v___x_3979_);
v_fst_3981_ = lean_ctor_get(v_a_3980_, 0);
v_isSharedCheck_4064_ = !lean_is_exclusive(v_a_3980_);
if (v_isSharedCheck_4064_ == 0)
{
lean_object* v_unused_4065_; 
v_unused_4065_ = lean_ctor_get(v_a_3980_, 1);
lean_dec(v_unused_4065_);
v___x_3983_ = v_a_3980_;
v_isShared_3984_ = v_isSharedCheck_4064_;
goto v_resetjp_3982_;
}
else
{
lean_inc(v_fst_3981_);
lean_dec(v_a_3980_);
v___x_3983_ = lean_box(0);
v_isShared_3984_ = v_isSharedCheck_4064_;
goto v_resetjp_3982_;
}
v_resetjp_3982_:
{
lean_object* v___x_3985_; lean_object* v___x_3987_; 
v___x_3985_ = l_Array_toSubarray___redArg(v_toSortArgs_3925_, v___x_3965_, v___x_3961_);
if (v_isShared_3984_ == 0)
{
lean_ctor_set(v___x_3983_, 1, v___x_3985_);
v___x_3987_ = v___x_3983_;
goto v_reusejp_3986_;
}
else
{
lean_object* v_reuseFailAlloc_4063_; 
v_reuseFailAlloc_4063_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4063_, 0, v_fst_3981_);
lean_ctor_set(v_reuseFailAlloc_4063_, 1, v___x_3985_);
v___x_3987_ = v_reuseFailAlloc_4063_;
goto v_reusejp_3986_;
}
v_reusejp_3986_:
{
size_t v_sz_3988_; lean_object* v___x_3989_; 
v_sz_3988_ = lean_array_size(v_toSortDecls_3924_);
v___x_3989_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__2___redArg(v_toSortDecls_3924_, v_sz_3988_, v___x_3978_, v___x_3987_);
if (lean_obj_tag(v___x_3989_) == 0)
{
lean_object* v_a_3990_; lean_object* v_fst_3991_; lean_object* v_size_3992_; lean_object* v___x_3993_; lean_object* v___x_3994_; lean_object* v___x_3995_; lean_object* v___x_3996_; lean_object* v___x_3997_; 
v_a_3990_ = lean_ctor_get(v___x_3989_, 0);
lean_inc(v_a_3990_);
lean_dec_ref(v___x_3989_);
v_fst_3991_ = lean_ctor_get(v_a_3990_, 0);
lean_inc_n(v_fst_3991_, 2);
lean_dec(v_a_3990_);
v_size_3992_ = lean_ctor_get(v_fst_3991_, 0);
v___x_3993_ = l_Lean_instEmptyCollectionFVarIdHashSet;
v___x_3994_ = lean_mk_empty_array_with_capacity(v_size_3992_);
lean_inc_ref(v___x_3994_);
v___x_3995_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3995_, 0, v___x_3993_);
lean_ctor_set(v___x_3995_, 1, v___x_3993_);
lean_ctor_set(v___x_3995_, 2, v___x_3994_);
lean_ctor_set(v___x_3995_, 3, v___x_3994_);
v___x_3996_ = lean_box(0);
v___x_3997_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__3(v_fst_3991_, v_sortedDecls_3922_, v_sz_3977_, v___x_3978_, v___x_3996_, v___x_3995_, v___y_3972_, v___y_3973_);
lean_dec_ref(v_sortedDecls_3922_);
if (lean_obj_tag(v___x_3997_) == 0)
{
lean_object* v_a_3998_; lean_object* v_snd_3999_; lean_object* v___x_4000_; 
v_a_3998_ = lean_ctor_get(v___x_3997_, 0);
lean_inc(v_a_3998_);
lean_dec_ref(v___x_3997_);
v_snd_3999_ = lean_ctor_get(v_a_3998_, 1);
lean_inc(v_snd_3999_);
lean_dec(v_a_3998_);
v___x_4000_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__3(v_fst_3991_, v_toSortDecls_3924_, v_sz_3988_, v___x_3978_, v___x_3996_, v_snd_3999_, v___y_3972_, v___y_3973_);
if (lean_obj_tag(v___x_4000_) == 0)
{
lean_object* v_a_4001_; lean_object* v_snd_4002_; lean_object* v___x_4004_; uint8_t v_isShared_4005_; uint8_t v_isSharedCheck_4037_; 
v_a_4001_ = lean_ctor_get(v___x_4000_, 0);
lean_inc(v_a_4001_);
lean_dec_ref(v___x_4000_);
v_snd_4002_ = lean_ctor_get(v_a_4001_, 1);
v_isSharedCheck_4037_ = !lean_is_exclusive(v_a_4001_);
if (v_isSharedCheck_4037_ == 0)
{
lean_object* v_unused_4038_; 
v_unused_4038_ = lean_ctor_get(v_a_4001_, 0);
lean_dec(v_unused_4038_);
v___x_4004_ = v_a_4001_;
v_isShared_4005_ = v_isSharedCheck_4037_;
goto v_resetjp_4003_;
}
else
{
lean_inc(v_snd_4002_);
lean_dec(v_a_4001_);
v___x_4004_ = lean_box(0);
v_isShared_4005_ = v_isSharedCheck_4037_;
goto v_resetjp_4003_;
}
v_resetjp_4003_:
{
lean_object* v_options_4006_; lean_object* v_newDecls_4007_; lean_object* v_newArgs_4008_; lean_object* v_inheritedTraceOptions_4009_; uint8_t v_hasTrace_4010_; lean_object* v___f_4011_; 
v_options_4006_ = lean_ctor_get(v___y_3972_, 2);
v_newDecls_4007_ = lean_ctor_get(v_snd_4002_, 2);
v_newArgs_4008_ = lean_ctor_get(v_snd_4002_, 3);
v_inheritedTraceOptions_4009_ = lean_ctor_get(v___y_3972_, 13);
v_hasTrace_4010_ = lean_ctor_get_uint8(v_options_4006_, sizeof(void*)*1);
lean_inc_ref(v_newArgs_4008_);
lean_inc_ref(v_newDecls_4007_);
v___f_4011_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___lam__0___boxed), 7, 2);
lean_closure_set(v___f_4011_, 0, v_newDecls_4007_);
lean_closure_set(v___f_4011_, 1, v_newArgs_4008_);
if (v_hasTrace_4010_ == 0)
{
lean_del_object(v___x_4004_);
v___y_3949_ = v___x_3996_;
v___y_3950_ = v___y_3972_;
v___y_3951_ = v___f_4011_;
v___y_3952_ = v___y_3973_;
v_snd_3953_ = v_snd_4002_;
goto v___jp_3948_;
}
else
{
lean_object* v___x_4012_; uint8_t v___x_4013_; 
v___x_4012_ = lean_obj_once(&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__13, &l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__13_once, _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__13);
v___x_4013_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4009_, v_options_4006_, v___x_4012_);
if (v___x_4013_ == 0)
{
lean_del_object(v___x_4004_);
v___y_3949_ = v___x_3996_;
v___y_3950_ = v___y_3972_;
v___y_3951_ = v___f_4011_;
v___y_3952_ = v___y_3973_;
v_snd_3953_ = v_snd_4002_;
goto v___jp_3948_;
}
else
{
lean_object* v___x_4014_; size_t v_sz_4015_; lean_object* v___x_4016_; lean_object* v___x_4017_; lean_object* v___x_4018_; lean_object* v___x_4019_; lean_object* v___x_4020_; lean_object* v___x_4022_; 
lean_inc_ref(v_newArgs_4008_);
lean_inc_ref_n(v_newDecls_4007_, 2);
lean_dec_ref(v___f_4011_);
v___x_4014_ = lean_obj_once(&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__8, &l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__8_once, _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__8);
v_sz_4015_ = lean_array_size(v_newDecls_4007_);
v___x_4016_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__4(v_sz_4015_, v___x_3978_, v_newDecls_4007_);
v___x_4017_ = lean_array_to_list(v___x_4016_);
v___x_4018_ = lean_box(0);
v___x_4019_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__5(v___x_4017_, v___x_4018_);
v___x_4020_ = l_Lean_MessageData_ofList(v___x_4019_);
if (v_isShared_4005_ == 0)
{
lean_ctor_set_tag(v___x_4004_, 7);
lean_ctor_set(v___x_4004_, 1, v___x_4020_);
lean_ctor_set(v___x_4004_, 0, v___x_4014_);
v___x_4022_ = v___x_4004_;
goto v_reusejp_4021_;
}
else
{
lean_object* v_reuseFailAlloc_4036_; 
v_reuseFailAlloc_4036_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4036_, 0, v___x_4014_);
lean_ctor_set(v_reuseFailAlloc_4036_, 1, v___x_4020_);
v___x_4022_ = v_reuseFailAlloc_4036_;
goto v_reusejp_4021_;
}
v_reusejp_4021_:
{
lean_object* v___x_4023_; 
v___x_4023_ = l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6(v_cls_3970_, v___x_4022_, v_snd_4002_, v___y_3972_, v___y_3973_);
if (lean_obj_tag(v___x_4023_) == 0)
{
lean_object* v_a_4024_; lean_object* v_fst_4025_; lean_object* v_snd_4026_; lean_object* v___x_4027_; 
v_a_4024_ = lean_ctor_get(v___x_4023_, 0);
lean_inc(v_a_4024_);
lean_dec_ref(v___x_4023_);
v_fst_4025_ = lean_ctor_get(v_a_4024_, 0);
lean_inc(v_fst_4025_);
v_snd_4026_ = lean_ctor_get(v_a_4024_, 1);
lean_inc(v_snd_4026_);
lean_dec(v_a_4024_);
v___x_4027_ = l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___lam__0(v_newDecls_4007_, v_newArgs_4008_, v_fst_4025_, v_snd_4026_, v___y_3972_, v___y_3973_);
v___y_3930_ = v___x_4027_;
goto v___jp_3929_;
}
else
{
lean_object* v_a_4028_; lean_object* v___x_4030_; uint8_t v_isShared_4031_; uint8_t v_isSharedCheck_4035_; 
lean_dec_ref(v_newArgs_4008_);
lean_dec_ref(v_newDecls_4007_);
v_a_4028_ = lean_ctor_get(v___x_4023_, 0);
v_isSharedCheck_4035_ = !lean_is_exclusive(v___x_4023_);
if (v_isSharedCheck_4035_ == 0)
{
v___x_4030_ = v___x_4023_;
v_isShared_4031_ = v_isSharedCheck_4035_;
goto v_resetjp_4029_;
}
else
{
lean_inc(v_a_4028_);
lean_dec(v___x_4023_);
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
}
}
}
}
else
{
lean_object* v_a_4039_; lean_object* v___x_4041_; uint8_t v_isShared_4042_; uint8_t v_isSharedCheck_4046_; 
v_a_4039_ = lean_ctor_get(v___x_4000_, 0);
v_isSharedCheck_4046_ = !lean_is_exclusive(v___x_4000_);
if (v_isSharedCheck_4046_ == 0)
{
v___x_4041_ = v___x_4000_;
v_isShared_4042_ = v_isSharedCheck_4046_;
goto v_resetjp_4040_;
}
else
{
lean_inc(v_a_4039_);
lean_dec(v___x_4000_);
v___x_4041_ = lean_box(0);
v_isShared_4042_ = v_isSharedCheck_4046_;
goto v_resetjp_4040_;
}
v_resetjp_4040_:
{
lean_object* v___x_4044_; 
if (v_isShared_4042_ == 0)
{
v___x_4044_ = v___x_4041_;
goto v_reusejp_4043_;
}
else
{
lean_object* v_reuseFailAlloc_4045_; 
v_reuseFailAlloc_4045_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4045_, 0, v_a_4039_);
v___x_4044_ = v_reuseFailAlloc_4045_;
goto v_reusejp_4043_;
}
v_reusejp_4043_:
{
return v___x_4044_;
}
}
}
}
else
{
lean_object* v_a_4047_; lean_object* v___x_4049_; uint8_t v_isShared_4050_; uint8_t v_isSharedCheck_4054_; 
lean_dec(v_fst_3991_);
v_a_4047_ = lean_ctor_get(v___x_3997_, 0);
v_isSharedCheck_4054_ = !lean_is_exclusive(v___x_3997_);
if (v_isSharedCheck_4054_ == 0)
{
v___x_4049_ = v___x_3997_;
v_isShared_4050_ = v_isSharedCheck_4054_;
goto v_resetjp_4048_;
}
else
{
lean_inc(v_a_4047_);
lean_dec(v___x_3997_);
v___x_4049_ = lean_box(0);
v_isShared_4050_ = v_isSharedCheck_4054_;
goto v_resetjp_4048_;
}
v_resetjp_4048_:
{
lean_object* v___x_4052_; 
if (v_isShared_4050_ == 0)
{
v___x_4052_ = v___x_4049_;
goto v_reusejp_4051_;
}
else
{
lean_object* v_reuseFailAlloc_4053_; 
v_reuseFailAlloc_4053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4053_, 0, v_a_4047_);
v___x_4052_ = v_reuseFailAlloc_4053_;
goto v_reusejp_4051_;
}
v_reusejp_4051_:
{
return v___x_4052_;
}
}
}
}
else
{
lean_object* v_a_4055_; lean_object* v___x_4057_; uint8_t v_isShared_4058_; uint8_t v_isSharedCheck_4062_; 
lean_dec_ref(v_sortedDecls_3922_);
v_a_4055_ = lean_ctor_get(v___x_3989_, 0);
v_isSharedCheck_4062_ = !lean_is_exclusive(v___x_3989_);
if (v_isSharedCheck_4062_ == 0)
{
v___x_4057_ = v___x_3989_;
v_isShared_4058_ = v_isSharedCheck_4062_;
goto v_resetjp_4056_;
}
else
{
lean_inc(v_a_4055_);
lean_dec(v___x_3989_);
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
}
else
{
lean_object* v_a_4066_; lean_object* v___x_4068_; uint8_t v_isShared_4069_; uint8_t v_isSharedCheck_4073_; 
lean_dec_ref(v_toSortArgs_3925_);
lean_dec_ref(v_sortedDecls_3922_);
v_a_4066_ = lean_ctor_get(v___x_3979_, 0);
v_isSharedCheck_4073_ = !lean_is_exclusive(v___x_3979_);
if (v_isSharedCheck_4073_ == 0)
{
v___x_4068_ = v___x_3979_;
v_isShared_4069_ = v_isSharedCheck_4073_;
goto v_resetjp_4067_;
}
else
{
lean_inc(v_a_4066_);
lean_dec(v___x_3979_);
v___x_4068_ = lean_box(0);
v_isShared_4069_ = v_isSharedCheck_4073_;
goto v_resetjp_4067_;
}
v_resetjp_4067_:
{
lean_object* v___x_4071_; 
if (v_isShared_4069_ == 0)
{
v___x_4071_ = v___x_4068_;
goto v_reusejp_4070_;
}
else
{
lean_object* v_reuseFailAlloc_4072_; 
v_reuseFailAlloc_4072_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4072_, 0, v_a_4066_);
v___x_4071_ = v_reuseFailAlloc_4072_;
goto v_reusejp_4070_;
}
v_reusejp_4070_:
{
return v___x_4071_;
}
}
}
}
}
else
{
lean_object* v___x_4086_; lean_object* v___x_4087_; 
lean_dec_ref(v_toSortArgs_3925_);
v___x_4086_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4086_, 0, v_sortedDecls_3922_);
lean_ctor_set(v___x_4086_, 1, v_sortedArgs_3923_);
v___x_4087_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4087_, 0, v___x_4086_);
return v___x_4087_;
}
}
}
v___jp_3929_:
{
if (lean_obj_tag(v___y_3930_) == 0)
{
lean_object* v_a_3931_; lean_object* v___x_3933_; uint8_t v_isShared_3934_; uint8_t v_isSharedCheck_3939_; 
v_a_3931_ = lean_ctor_get(v___y_3930_, 0);
v_isSharedCheck_3939_ = !lean_is_exclusive(v___y_3930_);
if (v_isSharedCheck_3939_ == 0)
{
v___x_3933_ = v___y_3930_;
v_isShared_3934_ = v_isSharedCheck_3939_;
goto v_resetjp_3932_;
}
else
{
lean_inc(v_a_3931_);
lean_dec(v___y_3930_);
v___x_3933_ = lean_box(0);
v_isShared_3934_ = v_isSharedCheck_3939_;
goto v_resetjp_3932_;
}
v_resetjp_3932_:
{
lean_object* v_fst_3935_; lean_object* v___x_3937_; 
v_fst_3935_ = lean_ctor_get(v_a_3931_, 0);
lean_inc(v_fst_3935_);
lean_dec(v_a_3931_);
if (v_isShared_3934_ == 0)
{
lean_ctor_set(v___x_3933_, 0, v_fst_3935_);
v___x_3937_ = v___x_3933_;
goto v_reusejp_3936_;
}
else
{
lean_object* v_reuseFailAlloc_3938_; 
v_reuseFailAlloc_3938_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3938_, 0, v_fst_3935_);
v___x_3937_ = v_reuseFailAlloc_3938_;
goto v_reusejp_3936_;
}
v_reusejp_3936_:
{
return v___x_3937_;
}
}
}
else
{
lean_object* v_a_3940_; lean_object* v___x_3942_; uint8_t v_isShared_3943_; uint8_t v_isSharedCheck_3947_; 
v_a_3940_ = lean_ctor_get(v___y_3930_, 0);
v_isSharedCheck_3947_ = !lean_is_exclusive(v___y_3930_);
if (v_isSharedCheck_3947_ == 0)
{
v___x_3942_ = v___y_3930_;
v_isShared_3943_ = v_isSharedCheck_3947_;
goto v_resetjp_3941_;
}
else
{
lean_inc(v_a_3940_);
lean_dec(v___y_3930_);
v___x_3942_ = lean_box(0);
v_isShared_3943_ = v_isSharedCheck_3947_;
goto v_resetjp_3941_;
}
v_resetjp_3941_:
{
lean_object* v___x_3945_; 
if (v_isShared_3943_ == 0)
{
v___x_3945_ = v___x_3942_;
goto v_reusejp_3944_;
}
else
{
lean_object* v_reuseFailAlloc_3946_; 
v_reuseFailAlloc_3946_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3946_, 0, v_a_3940_);
v___x_3945_ = v_reuseFailAlloc_3946_;
goto v_reusejp_3944_;
}
v_reusejp_3944_:
{
return v___x_3945_;
}
}
}
}
v___jp_3948_:
{
lean_object* v___x_3954_; 
lean_inc(v___y_3952_);
lean_inc_ref(v___y_3950_);
v___x_3954_ = lean_apply_5(v___y_3951_, v___y_3949_, v_snd_3953_, v___y_3950_, v___y_3952_, lean_box(0));
v___y_3930_ = v___x_3954_;
goto v___jp_3929_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___boxed(lean_object* v_sortedDecls_4088_, lean_object* v_sortedArgs_4089_, lean_object* v_toSortDecls_4090_, lean_object* v_toSortArgs_4091_, lean_object* v_a_4092_, lean_object* v_a_4093_, lean_object* v_a_4094_){
_start:
{
lean_object* v_res_4095_; 
v_res_4095_ = l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls(v_sortedDecls_4088_, v_sortedArgs_4089_, v_toSortDecls_4090_, v_toSortArgs_4091_, v_a_4092_, v_a_4093_);
lean_dec(v_a_4093_);
lean_dec_ref(v_a_4092_);
lean_dec_ref(v_toSortDecls_4090_);
return v_res_4095_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__1(lean_object* v_00_u03b2_4096_, lean_object* v_m_4097_, lean_object* v_a_4098_, lean_object* v_b_4099_){
_start:
{
lean_object* v___x_4100_; 
v___x_4100_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__1___redArg(v_m_4097_, v_a_4098_, v_b_4099_);
return v___x_4100_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__2(lean_object* v_as_4101_, size_t v_sz_4102_, size_t v_i_4103_, lean_object* v_b_4104_, lean_object* v___y_4105_, lean_object* v___y_4106_){
_start:
{
lean_object* v___x_4108_; 
v___x_4108_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__2___redArg(v_as_4101_, v_sz_4102_, v_i_4103_, v_b_4104_);
return v___x_4108_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__2___boxed(lean_object* v_as_4109_, lean_object* v_sz_4110_, lean_object* v_i_4111_, lean_object* v_b_4112_, lean_object* v___y_4113_, lean_object* v___y_4114_, lean_object* v___y_4115_){
_start:
{
size_t v_sz_boxed_4116_; size_t v_i_boxed_4117_; lean_object* v_res_4118_; 
v_sz_boxed_4116_ = lean_unbox_usize(v_sz_4110_);
lean_dec(v_sz_4110_);
v_i_boxed_4117_ = lean_unbox_usize(v_i_4111_);
lean_dec(v_i_4111_);
v_res_4118_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__2(v_as_4109_, v_sz_boxed_4116_, v_i_boxed_4117_, v_b_4112_, v___y_4113_, v___y_4114_);
lean_dec(v___y_4114_);
lean_dec_ref(v___y_4113_);
lean_dec_ref(v_as_4109_);
return v_res_4118_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__1_spec__1(lean_object* v_00_u03b2_4119_, lean_object* v_a_4120_, lean_object* v_b_4121_, lean_object* v_x_4122_){
_start:
{
lean_object* v___x_4123_; 
v___x_4123_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__1_spec__1___redArg(v_a_4120_, v_b_4121_, v_x_4122_);
return v___x_4123_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Closure_mkValueTypeClosure_spec__0(lean_object* v_msg_4125_, lean_object* v___y_4126_, lean_object* v___y_4127_, lean_object* v___y_4128_, lean_object* v___y_4129_){
_start:
{
lean_object* v___f_4131_; lean_object* v___x_1329__overap_4132_; lean_object* v___x_4133_; 
v___f_4131_ = ((lean_object*)(l_panic___at___00Lean_Meta_Closure_mkValueTypeClosure_spec__0___closed__0));
v___x_1329__overap_4132_ = lean_panic_fn_borrowed(v___f_4131_, v_msg_4125_);
lean_inc(v___y_4129_);
lean_inc_ref(v___y_4128_);
lean_inc(v___y_4127_);
lean_inc_ref(v___y_4126_);
v___x_4133_ = lean_apply_5(v___x_1329__overap_4132_, v___y_4126_, v___y_4127_, v___y_4128_, v___y_4129_, lean_box(0));
return v___x_4133_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Closure_mkValueTypeClosure_spec__0___boxed(lean_object* v_msg_4134_, lean_object* v___y_4135_, lean_object* v___y_4136_, lean_object* v___y_4137_, lean_object* v___y_4138_, lean_object* v___y_4139_){
_start:
{
lean_object* v_res_4140_; 
v_res_4140_ = l_panic___at___00Lean_Meta_Closure_mkValueTypeClosure_spec__0(v_msg_4134_, v___y_4135_, v___y_4136_, v___y_4137_, v___y_4138_);
lean_dec(v___y_4138_);
lean_dec_ref(v___y_4137_);
lean_dec(v___y_4136_);
lean_dec_ref(v___y_4135_);
return v_res_4140_;
}
}
static lean_object* _init_l_Lean_Meta_Closure_mkValueTypeClosure___closed__0(void){
_start:
{
lean_object* v___x_4141_; lean_object* v___x_4142_; lean_object* v___x_4143_; 
v___x_4141_ = lean_box(0);
v___x_4142_ = lean_unsigned_to_nat(16u);
v___x_4143_ = lean_mk_array(v___x_4142_, v___x_4141_);
return v___x_4143_;
}
}
static lean_object* _init_l_Lean_Meta_Closure_mkValueTypeClosure___closed__1(void){
_start:
{
lean_object* v___x_4144_; lean_object* v___x_4145_; lean_object* v___x_4146_; 
v___x_4144_ = lean_obj_once(&l_Lean_Meta_Closure_mkValueTypeClosure___closed__0, &l_Lean_Meta_Closure_mkValueTypeClosure___closed__0_once, _init_l_Lean_Meta_Closure_mkValueTypeClosure___closed__0);
v___x_4145_ = lean_unsigned_to_nat(0u);
v___x_4146_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4146_, 0, v___x_4145_);
lean_ctor_set(v___x_4146_, 1, v___x_4144_);
return v___x_4146_;
}
}
static lean_object* _init_l_Lean_Meta_Closure_mkValueTypeClosure___closed__3(void){
_start:
{
lean_object* v___x_4149_; lean_object* v___x_4150_; lean_object* v___x_4151_; lean_object* v___x_4152_; 
v___x_4149_ = lean_unsigned_to_nat(1u);
v___x_4150_ = ((lean_object*)(l_Lean_Meta_Closure_mkValueTypeClosure___closed__2));
v___x_4151_ = lean_obj_once(&l_Lean_Meta_Closure_mkValueTypeClosure___closed__1, &l_Lean_Meta_Closure_mkValueTypeClosure___closed__1_once, _init_l_Lean_Meta_Closure_mkValueTypeClosure___closed__1);
v___x_4152_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_4152_, 0, v___x_4151_);
lean_ctor_set(v___x_4152_, 1, v___x_4151_);
lean_ctor_set(v___x_4152_, 2, v___x_4150_);
lean_ctor_set(v___x_4152_, 3, v___x_4149_);
lean_ctor_set(v___x_4152_, 4, v___x_4150_);
lean_ctor_set(v___x_4152_, 5, v___x_4150_);
lean_ctor_set(v___x_4152_, 6, v___x_4150_);
lean_ctor_set(v___x_4152_, 7, v___x_4150_);
lean_ctor_set(v___x_4152_, 8, v___x_4149_);
lean_ctor_set(v___x_4152_, 9, v___x_4150_);
lean_ctor_set(v___x_4152_, 10, v___x_4150_);
lean_ctor_set(v___x_4152_, 11, v___x_4150_);
return v___x_4152_;
}
}
static lean_object* _init_l_Lean_Meta_Closure_mkValueTypeClosure___closed__6(void){
_start:
{
lean_object* v___x_4155_; lean_object* v___x_4156_; lean_object* v___x_4157_; lean_object* v___x_4158_; lean_object* v___x_4159_; lean_object* v___x_4160_; 
v___x_4155_ = ((lean_object*)(l_Lean_Meta_Closure_mkValueTypeClosure___closed__5));
v___x_4156_ = lean_unsigned_to_nat(2u);
v___x_4157_ = lean_unsigned_to_nat(417u);
v___x_4158_ = ((lean_object*)(l_Lean_Meta_Closure_mkValueTypeClosure___closed__4));
v___x_4159_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__2));
v___x_4160_ = l_mkPanicMessageWithDecl(v___x_4159_, v___x_4158_, v___x_4157_, v___x_4156_, v___x_4155_);
return v___x_4160_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkValueTypeClosure(lean_object* v_type_4161_, lean_object* v_value_4162_, uint8_t v_zetaDelta_4163_, lean_object* v_a_4164_, lean_object* v_a_4165_, lean_object* v_a_4166_, lean_object* v_a_4167_){
_start:
{
lean_object* v___x_4169_; lean_object* v___x_4170_; lean_object* v___x_4171_; 
v___x_4169_ = lean_obj_once(&l_Lean_Meta_Closure_mkValueTypeClosure___closed__3, &l_Lean_Meta_Closure_mkValueTypeClosure___closed__3_once, _init_l_Lean_Meta_Closure_mkValueTypeClosure___closed__3);
v___x_4170_ = lean_st_mk_ref(v___x_4169_);
v___x_4171_ = l_Lean_Meta_Closure_mkValueTypeClosureAux(v_type_4161_, v_value_4162_, v_zetaDelta_4163_, v___x_4170_, v_a_4164_, v_a_4165_, v_a_4166_, v_a_4167_);
if (lean_obj_tag(v___x_4171_) == 0)
{
lean_object* v_a_4172_; lean_object* v___x_4173_; lean_object* v_fst_4174_; lean_object* v_snd_4175_; lean_object* v_levelParams_4176_; lean_object* v_levelArgs_4177_; lean_object* v_newLocalDecls_4178_; lean_object* v_newLocalDeclsForMVars_4179_; lean_object* v_newLetDecls_4180_; lean_object* v_exprMVarArgs_4181_; lean_object* v_exprFVarArgs_4182_; lean_object* v___x_4183_; lean_object* v___x_4184_; lean_object* v___x_4185_; 
v_a_4172_ = lean_ctor_get(v___x_4171_, 0);
lean_inc(v_a_4172_);
lean_dec_ref(v___x_4171_);
v___x_4173_ = lean_st_ref_get(v___x_4170_);
lean_dec(v___x_4170_);
v_fst_4174_ = lean_ctor_get(v_a_4172_, 0);
lean_inc(v_fst_4174_);
v_snd_4175_ = lean_ctor_get(v_a_4172_, 1);
lean_inc(v_snd_4175_);
lean_dec(v_a_4172_);
v_levelParams_4176_ = lean_ctor_get(v___x_4173_, 2);
lean_inc_ref(v_levelParams_4176_);
v_levelArgs_4177_ = lean_ctor_get(v___x_4173_, 4);
lean_inc_ref(v_levelArgs_4177_);
v_newLocalDecls_4178_ = lean_ctor_get(v___x_4173_, 5);
lean_inc_ref(v_newLocalDecls_4178_);
v_newLocalDeclsForMVars_4179_ = lean_ctor_get(v___x_4173_, 6);
lean_inc_ref(v_newLocalDeclsForMVars_4179_);
v_newLetDecls_4180_ = lean_ctor_get(v___x_4173_, 7);
lean_inc_ref(v_newLetDecls_4180_);
v_exprMVarArgs_4181_ = lean_ctor_get(v___x_4173_, 9);
lean_inc_ref(v_exprMVarArgs_4181_);
v_exprFVarArgs_4182_ = lean_ctor_get(v___x_4173_, 10);
lean_inc_ref(v_exprFVarArgs_4182_);
lean_dec(v___x_4173_);
v___x_4183_ = l_Array_reverse___redArg(v_newLocalDecls_4178_);
v___x_4184_ = l_Array_reverse___redArg(v_exprFVarArgs_4182_);
v___x_4185_ = l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls(v___x_4183_, v___x_4184_, v_newLocalDeclsForMVars_4179_, v_exprMVarArgs_4181_, v_a_4166_, v_a_4167_);
lean_dec_ref(v_newLocalDeclsForMVars_4179_);
if (lean_obj_tag(v___x_4185_) == 0)
{
lean_object* v_a_4186_; lean_object* v___x_4188_; uint8_t v_isShared_4189_; uint8_t v_isSharedCheck_4204_; 
v_a_4186_ = lean_ctor_get(v___x_4185_, 0);
v_isSharedCheck_4204_ = !lean_is_exclusive(v___x_4185_);
if (v_isSharedCheck_4204_ == 0)
{
v___x_4188_ = v___x_4185_;
v_isShared_4189_ = v_isSharedCheck_4204_;
goto v_resetjp_4187_;
}
else
{
lean_inc(v_a_4186_);
lean_dec(v___x_4185_);
v___x_4188_ = lean_box(0);
v_isShared_4189_ = v_isSharedCheck_4204_;
goto v_resetjp_4187_;
}
v_resetjp_4187_:
{
lean_object* v_fst_4190_; lean_object* v_snd_4191_; lean_object* v___x_4192_; lean_object* v___x_4193_; lean_object* v___x_4194_; lean_object* v___x_4195_; lean_object* v___x_4196_; uint8_t v___x_4197_; 
v_fst_4190_ = lean_ctor_get(v_a_4186_, 0);
lean_inc_n(v_fst_4190_, 2);
v_snd_4191_ = lean_ctor_get(v_a_4186_, 1);
lean_inc(v_snd_4191_);
lean_dec(v_a_4186_);
v___x_4192_ = l_Array_reverse___redArg(v_newLetDecls_4180_);
lean_inc_ref(v___x_4192_);
v___x_4193_ = l_Lean_Meta_Closure_mkForall(v___x_4192_, v_fst_4174_);
lean_dec(v_fst_4174_);
v___x_4194_ = l_Lean_Meta_Closure_mkForall(v_fst_4190_, v___x_4193_);
lean_dec_ref(v___x_4193_);
v___x_4195_ = l_Lean_Meta_Closure_mkLambda(v___x_4192_, v_snd_4175_);
lean_dec(v_snd_4175_);
v___x_4196_ = l_Lean_Meta_Closure_mkLambda(v_fst_4190_, v___x_4195_);
lean_dec_ref(v___x_4195_);
v___x_4197_ = l_Lean_Expr_hasFVar(v___x_4196_);
if (v___x_4197_ == 0)
{
lean_object* v___x_4198_; lean_object* v___x_4200_; 
v___x_4198_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4198_, 0, v_levelParams_4176_);
lean_ctor_set(v___x_4198_, 1, v___x_4194_);
lean_ctor_set(v___x_4198_, 2, v___x_4196_);
lean_ctor_set(v___x_4198_, 3, v_levelArgs_4177_);
lean_ctor_set(v___x_4198_, 4, v_snd_4191_);
if (v_isShared_4189_ == 0)
{
lean_ctor_set(v___x_4188_, 0, v___x_4198_);
v___x_4200_ = v___x_4188_;
goto v_reusejp_4199_;
}
else
{
lean_object* v_reuseFailAlloc_4201_; 
v_reuseFailAlloc_4201_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4201_, 0, v___x_4198_);
v___x_4200_ = v_reuseFailAlloc_4201_;
goto v_reusejp_4199_;
}
v_reusejp_4199_:
{
return v___x_4200_;
}
}
else
{
lean_object* v___x_4202_; lean_object* v___x_4203_; 
lean_dec_ref(v___x_4196_);
lean_dec_ref(v___x_4194_);
lean_dec(v_snd_4191_);
lean_del_object(v___x_4188_);
lean_dec_ref(v_levelArgs_4177_);
lean_dec_ref(v_levelParams_4176_);
v___x_4202_ = lean_obj_once(&l_Lean_Meta_Closure_mkValueTypeClosure___closed__6, &l_Lean_Meta_Closure_mkValueTypeClosure___closed__6_once, _init_l_Lean_Meta_Closure_mkValueTypeClosure___closed__6);
v___x_4203_ = l_panic___at___00Lean_Meta_Closure_mkValueTypeClosure_spec__0(v___x_4202_, v_a_4164_, v_a_4165_, v_a_4166_, v_a_4167_);
return v___x_4203_;
}
}
}
else
{
lean_object* v_a_4205_; lean_object* v___x_4207_; uint8_t v_isShared_4208_; uint8_t v_isSharedCheck_4212_; 
lean_dec_ref(v_newLetDecls_4180_);
lean_dec_ref(v_levelArgs_4177_);
lean_dec_ref(v_levelParams_4176_);
lean_dec(v_snd_4175_);
lean_dec(v_fst_4174_);
v_a_4205_ = lean_ctor_get(v___x_4185_, 0);
v_isSharedCheck_4212_ = !lean_is_exclusive(v___x_4185_);
if (v_isSharedCheck_4212_ == 0)
{
v___x_4207_ = v___x_4185_;
v_isShared_4208_ = v_isSharedCheck_4212_;
goto v_resetjp_4206_;
}
else
{
lean_inc(v_a_4205_);
lean_dec(v___x_4185_);
v___x_4207_ = lean_box(0);
v_isShared_4208_ = v_isSharedCheck_4212_;
goto v_resetjp_4206_;
}
v_resetjp_4206_:
{
lean_object* v___x_4210_; 
if (v_isShared_4208_ == 0)
{
v___x_4210_ = v___x_4207_;
goto v_reusejp_4209_;
}
else
{
lean_object* v_reuseFailAlloc_4211_; 
v_reuseFailAlloc_4211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4211_, 0, v_a_4205_);
v___x_4210_ = v_reuseFailAlloc_4211_;
goto v_reusejp_4209_;
}
v_reusejp_4209_:
{
return v___x_4210_;
}
}
}
}
else
{
lean_object* v_a_4213_; lean_object* v___x_4215_; uint8_t v_isShared_4216_; uint8_t v_isSharedCheck_4220_; 
lean_dec(v___x_4170_);
v_a_4213_ = lean_ctor_get(v___x_4171_, 0);
v_isSharedCheck_4220_ = !lean_is_exclusive(v___x_4171_);
if (v_isSharedCheck_4220_ == 0)
{
v___x_4215_ = v___x_4171_;
v_isShared_4216_ = v_isSharedCheck_4220_;
goto v_resetjp_4214_;
}
else
{
lean_inc(v_a_4213_);
lean_dec(v___x_4171_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkValueTypeClosure___boxed(lean_object* v_type_4221_, lean_object* v_value_4222_, lean_object* v_zetaDelta_4223_, lean_object* v_a_4224_, lean_object* v_a_4225_, lean_object* v_a_4226_, lean_object* v_a_4227_, lean_object* v_a_4228_){
_start:
{
uint8_t v_zetaDelta_boxed_4229_; lean_object* v_res_4230_; 
v_zetaDelta_boxed_4229_ = lean_unbox(v_zetaDelta_4223_);
v_res_4230_ = l_Lean_Meta_Closure_mkValueTypeClosure(v_type_4221_, v_value_4222_, v_zetaDelta_boxed_4229_, v_a_4224_, v_a_4225_, v_a_4226_, v_a_4227_);
lean_dec(v_a_4227_);
lean_dec_ref(v_a_4226_);
lean_dec(v_a_4225_);
lean_dec_ref(v_a_4224_);
return v_res_4230_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkAuxDefinition_spec__0___redArg(lean_object* v_name_4231_, lean_object* v_levelParams_4232_, lean_object* v_type_4233_, lean_object* v_value_4234_, lean_object* v_hints_4235_, lean_object* v___y_4236_){
_start:
{
lean_object* v___x_4238_; uint8_t v___y_4240_; uint8_t v___y_4247_; lean_object* v_env_4250_; uint8_t v___x_4251_; 
v___x_4238_ = lean_st_ref_get(v___y_4236_);
v_env_4250_ = lean_ctor_get(v___x_4238_, 0);
lean_inc_ref_n(v_env_4250_, 2);
lean_dec(v___x_4238_);
v___x_4251_ = l_Lean_Environment_hasUnsafe(v_env_4250_, v_type_4233_);
if (v___x_4251_ == 0)
{
uint8_t v___x_4252_; 
v___x_4252_ = l_Lean_Environment_hasUnsafe(v_env_4250_, v_value_4234_);
v___y_4247_ = v___x_4252_;
goto v___jp_4246_;
}
else
{
lean_dec_ref(v_env_4250_);
v___y_4247_ = v___x_4251_;
goto v___jp_4246_;
}
v___jp_4239_:
{
lean_object* v___x_4241_; lean_object* v___x_4242_; lean_object* v___x_4243_; lean_object* v___x_4244_; lean_object* v___x_4245_; 
lean_inc(v_name_4231_);
v___x_4241_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4241_, 0, v_name_4231_);
lean_ctor_set(v___x_4241_, 1, v_levelParams_4232_);
lean_ctor_set(v___x_4241_, 2, v_type_4233_);
v___x_4242_ = lean_box(0);
v___x_4243_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4243_, 0, v_name_4231_);
lean_ctor_set(v___x_4243_, 1, v___x_4242_);
v___x_4244_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_4244_, 0, v___x_4241_);
lean_ctor_set(v___x_4244_, 1, v_value_4234_);
lean_ctor_set(v___x_4244_, 2, v_hints_4235_);
lean_ctor_set(v___x_4244_, 3, v___x_4243_);
lean_ctor_set_uint8(v___x_4244_, sizeof(void*)*4, v___y_4240_);
v___x_4245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4245_, 0, v___x_4244_);
return v___x_4245_;
}
v___jp_4246_:
{
if (v___y_4247_ == 0)
{
uint8_t v___x_4248_; 
v___x_4248_ = 1;
v___y_4240_ = v___x_4248_;
goto v___jp_4239_;
}
else
{
uint8_t v___x_4249_; 
v___x_4249_ = 0;
v___y_4240_ = v___x_4249_;
goto v___jp_4239_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkAuxDefinition_spec__0___redArg___boxed(lean_object* v_name_4253_, lean_object* v_levelParams_4254_, lean_object* v_type_4255_, lean_object* v_value_4256_, lean_object* v_hints_4257_, lean_object* v___y_4258_, lean_object* v___y_4259_){
_start:
{
lean_object* v_res_4260_; 
v_res_4260_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkAuxDefinition_spec__0___redArg(v_name_4253_, v_levelParams_4254_, v_type_4255_, v_value_4256_, v_hints_4257_, v___y_4258_);
lean_dec(v___y_4258_);
return v_res_4260_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkAuxDefinition_spec__0(lean_object* v_name_4261_, lean_object* v_levelParams_4262_, lean_object* v_type_4263_, lean_object* v_value_4264_, lean_object* v_hints_4265_, lean_object* v___y_4266_, lean_object* v___y_4267_, lean_object* v___y_4268_, lean_object* v___y_4269_){
_start:
{
lean_object* v___x_4271_; 
v___x_4271_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkAuxDefinition_spec__0___redArg(v_name_4261_, v_levelParams_4262_, v_type_4263_, v_value_4264_, v_hints_4265_, v___y_4269_);
return v___x_4271_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkAuxDefinition_spec__0___boxed(lean_object* v_name_4272_, lean_object* v_levelParams_4273_, lean_object* v_type_4274_, lean_object* v_value_4275_, lean_object* v_hints_4276_, lean_object* v___y_4277_, lean_object* v___y_4278_, lean_object* v___y_4279_, lean_object* v___y_4280_, lean_object* v___y_4281_){
_start:
{
lean_object* v_res_4282_; 
v_res_4282_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkAuxDefinition_spec__0(v_name_4272_, v_levelParams_4273_, v_type_4274_, v_value_4275_, v_hints_4276_, v___y_4277_, v___y_4278_, v___y_4279_, v___y_4280_);
lean_dec(v___y_4280_);
lean_dec_ref(v___y_4279_);
lean_dec(v___y_4278_);
lean_dec_ref(v___y_4277_);
return v_res_4282_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAuxDefinition(lean_object* v_name_4283_, lean_object* v_type_4284_, lean_object* v_value_4285_, uint8_t v_zetaDelta_4286_, uint8_t v_compile_4287_, uint8_t v_logCompileErrors_4288_, lean_object* v_a_4289_, lean_object* v_a_4290_, lean_object* v_a_4291_, lean_object* v_a_4292_){
_start:
{
lean_object* v___x_4294_; 
v___x_4294_ = l_Lean_Meta_Closure_mkValueTypeClosure(v_type_4284_, v_value_4285_, v_zetaDelta_4286_, v_a_4289_, v_a_4290_, v_a_4291_, v_a_4292_);
if (lean_obj_tag(v___x_4294_) == 0)
{
lean_object* v_a_4295_; lean_object* v___x_4297_; uint8_t v_isShared_4298_; uint8_t v_isSharedCheck_4346_; 
v_a_4295_ = lean_ctor_get(v___x_4294_, 0);
v_isSharedCheck_4346_ = !lean_is_exclusive(v___x_4294_);
if (v_isSharedCheck_4346_ == 0)
{
v___x_4297_ = v___x_4294_;
v_isShared_4298_ = v_isSharedCheck_4346_;
goto v_resetjp_4296_;
}
else
{
lean_inc(v_a_4295_);
lean_dec(v___x_4294_);
v___x_4297_ = lean_box(0);
v_isShared_4298_ = v_isSharedCheck_4346_;
goto v_resetjp_4296_;
}
v_resetjp_4296_:
{
lean_object* v___x_4299_; lean_object* v_env_4300_; lean_object* v_levelParams_4301_; lean_object* v_type_4302_; lean_object* v_value_4303_; lean_object* v_levelArgs_4304_; lean_object* v_exprArgs_4305_; uint32_t v___x_4313_; uint32_t v___x_4314_; uint32_t v___x_4315_; lean_object* v___x_4316_; lean_object* v___x_4317_; lean_object* v___x_4318_; lean_object* v_a_4319_; lean_object* v___x_4321_; uint8_t v_isShared_4322_; uint8_t v_isSharedCheck_4345_; 
v___x_4299_ = lean_st_ref_get(v_a_4292_);
v_env_4300_ = lean_ctor_get(v___x_4299_, 0);
lean_inc_ref(v_env_4300_);
lean_dec(v___x_4299_);
v_levelParams_4301_ = lean_ctor_get(v_a_4295_, 0);
lean_inc_ref(v_levelParams_4301_);
v_type_4302_ = lean_ctor_get(v_a_4295_, 1);
lean_inc_ref(v_type_4302_);
v_value_4303_ = lean_ctor_get(v_a_4295_, 2);
lean_inc_ref_n(v_value_4303_, 2);
v_levelArgs_4304_ = lean_ctor_get(v_a_4295_, 3);
lean_inc_ref(v_levelArgs_4304_);
v_exprArgs_4305_ = lean_ctor_get(v_a_4295_, 4);
lean_inc_ref(v_exprArgs_4305_);
lean_dec(v_a_4295_);
v___x_4313_ = l_Lean_getMaxHeight(v_env_4300_, v_value_4303_);
v___x_4314_ = 1;
v___x_4315_ = lean_uint32_add(v___x_4313_, v___x_4314_);
v___x_4316_ = lean_alloc_ctor(2, 0, 4);
lean_ctor_set_uint32(v___x_4316_, 0, v___x_4315_);
v___x_4317_ = lean_array_to_list(v_levelParams_4301_);
lean_inc(v_name_4283_);
v___x_4318_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkAuxDefinition_spec__0___redArg(v_name_4283_, v___x_4317_, v_type_4302_, v_value_4303_, v___x_4316_, v_a_4292_);
v_a_4319_ = lean_ctor_get(v___x_4318_, 0);
v_isSharedCheck_4345_ = !lean_is_exclusive(v___x_4318_);
if (v_isSharedCheck_4345_ == 0)
{
v___x_4321_ = v___x_4318_;
v_isShared_4322_ = v_isSharedCheck_4345_;
goto v_resetjp_4320_;
}
else
{
lean_inc(v_a_4319_);
lean_dec(v___x_4318_);
v___x_4321_ = lean_box(0);
v_isShared_4322_ = v_isSharedCheck_4345_;
goto v_resetjp_4320_;
}
v___jp_4306_:
{
lean_object* v___x_4307_; lean_object* v___x_4308_; lean_object* v___x_4309_; lean_object* v___x_4311_; 
v___x_4307_ = lean_array_to_list(v_levelArgs_4304_);
v___x_4308_ = l_Lean_mkConst(v_name_4283_, v___x_4307_);
v___x_4309_ = l_Lean_mkAppN(v___x_4308_, v_exprArgs_4305_);
lean_dec_ref(v_exprArgs_4305_);
if (v_isShared_4298_ == 0)
{
lean_ctor_set(v___x_4297_, 0, v___x_4309_);
v___x_4311_ = v___x_4297_;
goto v_reusejp_4310_;
}
else
{
lean_object* v_reuseFailAlloc_4312_; 
v_reuseFailAlloc_4312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4312_, 0, v___x_4309_);
v___x_4311_ = v_reuseFailAlloc_4312_;
goto v_reusejp_4310_;
}
v_reusejp_4310_:
{
return v___x_4311_;
}
}
v_resetjp_4320_:
{
lean_object* v___x_4324_; 
if (v_isShared_4322_ == 0)
{
lean_ctor_set_tag(v___x_4321_, 1);
v___x_4324_ = v___x_4321_;
goto v_reusejp_4323_;
}
else
{
lean_object* v_reuseFailAlloc_4344_; 
v_reuseFailAlloc_4344_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4344_, 0, v_a_4319_);
v___x_4324_ = v_reuseFailAlloc_4344_;
goto v_reusejp_4323_;
}
v_reusejp_4323_:
{
uint8_t v___x_4325_; lean_object* v___x_4326_; 
v___x_4325_ = 0;
lean_inc_ref(v___x_4324_);
v___x_4326_ = l_Lean_addDecl(v___x_4324_, v___x_4325_, v_a_4291_, v_a_4292_);
if (lean_obj_tag(v___x_4326_) == 0)
{
lean_dec_ref(v___x_4326_);
if (v_compile_4287_ == 0)
{
lean_dec_ref(v___x_4324_);
goto v___jp_4306_;
}
else
{
lean_object* v___x_4327_; 
v___x_4327_ = l_Lean_compileDecl(v___x_4324_, v_logCompileErrors_4288_, v_a_4291_, v_a_4292_);
if (lean_obj_tag(v___x_4327_) == 0)
{
lean_dec_ref(v___x_4327_);
goto v___jp_4306_;
}
else
{
lean_object* v_a_4328_; lean_object* v___x_4330_; uint8_t v_isShared_4331_; uint8_t v_isSharedCheck_4335_; 
lean_dec_ref(v_exprArgs_4305_);
lean_dec_ref(v_levelArgs_4304_);
lean_del_object(v___x_4297_);
lean_dec(v_name_4283_);
v_a_4328_ = lean_ctor_get(v___x_4327_, 0);
v_isSharedCheck_4335_ = !lean_is_exclusive(v___x_4327_);
if (v_isSharedCheck_4335_ == 0)
{
v___x_4330_ = v___x_4327_;
v_isShared_4331_ = v_isSharedCheck_4335_;
goto v_resetjp_4329_;
}
else
{
lean_inc(v_a_4328_);
lean_dec(v___x_4327_);
v___x_4330_ = lean_box(0);
v_isShared_4331_ = v_isSharedCheck_4335_;
goto v_resetjp_4329_;
}
v_resetjp_4329_:
{
lean_object* v___x_4333_; 
if (v_isShared_4331_ == 0)
{
v___x_4333_ = v___x_4330_;
goto v_reusejp_4332_;
}
else
{
lean_object* v_reuseFailAlloc_4334_; 
v_reuseFailAlloc_4334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4334_, 0, v_a_4328_);
v___x_4333_ = v_reuseFailAlloc_4334_;
goto v_reusejp_4332_;
}
v_reusejp_4332_:
{
return v___x_4333_;
}
}
}
}
}
else
{
lean_object* v_a_4336_; lean_object* v___x_4338_; uint8_t v_isShared_4339_; uint8_t v_isSharedCheck_4343_; 
lean_dec_ref(v___x_4324_);
lean_dec_ref(v_exprArgs_4305_);
lean_dec_ref(v_levelArgs_4304_);
lean_del_object(v___x_4297_);
lean_dec(v_name_4283_);
v_a_4336_ = lean_ctor_get(v___x_4326_, 0);
v_isSharedCheck_4343_ = !lean_is_exclusive(v___x_4326_);
if (v_isSharedCheck_4343_ == 0)
{
v___x_4338_ = v___x_4326_;
v_isShared_4339_ = v_isSharedCheck_4343_;
goto v_resetjp_4337_;
}
else
{
lean_inc(v_a_4336_);
lean_dec(v___x_4326_);
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
}
}
else
{
lean_object* v_a_4347_; lean_object* v___x_4349_; uint8_t v_isShared_4350_; uint8_t v_isSharedCheck_4354_; 
lean_dec(v_name_4283_);
v_a_4347_ = lean_ctor_get(v___x_4294_, 0);
v_isSharedCheck_4354_ = !lean_is_exclusive(v___x_4294_);
if (v_isSharedCheck_4354_ == 0)
{
v___x_4349_ = v___x_4294_;
v_isShared_4350_ = v_isSharedCheck_4354_;
goto v_resetjp_4348_;
}
else
{
lean_inc(v_a_4347_);
lean_dec(v___x_4294_);
v___x_4349_ = lean_box(0);
v_isShared_4350_ = v_isSharedCheck_4354_;
goto v_resetjp_4348_;
}
v_resetjp_4348_:
{
lean_object* v___x_4352_; 
if (v_isShared_4350_ == 0)
{
v___x_4352_ = v___x_4349_;
goto v_reusejp_4351_;
}
else
{
lean_object* v_reuseFailAlloc_4353_; 
v_reuseFailAlloc_4353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4353_, 0, v_a_4347_);
v___x_4352_ = v_reuseFailAlloc_4353_;
goto v_reusejp_4351_;
}
v_reusejp_4351_:
{
return v___x_4352_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAuxDefinition___boxed(lean_object* v_name_4355_, lean_object* v_type_4356_, lean_object* v_value_4357_, lean_object* v_zetaDelta_4358_, lean_object* v_compile_4359_, lean_object* v_logCompileErrors_4360_, lean_object* v_a_4361_, lean_object* v_a_4362_, lean_object* v_a_4363_, lean_object* v_a_4364_, lean_object* v_a_4365_){
_start:
{
uint8_t v_zetaDelta_boxed_4366_; uint8_t v_compile_boxed_4367_; uint8_t v_logCompileErrors_boxed_4368_; lean_object* v_res_4369_; 
v_zetaDelta_boxed_4366_ = lean_unbox(v_zetaDelta_4358_);
v_compile_boxed_4367_ = lean_unbox(v_compile_4359_);
v_logCompileErrors_boxed_4368_ = lean_unbox(v_logCompileErrors_4360_);
v_res_4369_ = l_Lean_Meta_mkAuxDefinition(v_name_4355_, v_type_4356_, v_value_4357_, v_zetaDelta_boxed_4366_, v_compile_boxed_4367_, v_logCompileErrors_boxed_4368_, v_a_4361_, v_a_4362_, v_a_4363_, v_a_4364_);
lean_dec(v_a_4364_);
lean_dec_ref(v_a_4363_);
lean_dec(v_a_4362_);
lean_dec_ref(v_a_4361_);
return v_res_4369_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAuxDefinitionFor(lean_object* v_name_4370_, lean_object* v_value_4371_, uint8_t v_zetaDelta_4372_, uint8_t v_compile_4373_, uint8_t v_logCompileErrors_4374_, lean_object* v_a_4375_, lean_object* v_a_4376_, lean_object* v_a_4377_, lean_object* v_a_4378_){
_start:
{
lean_object* v___x_4380_; 
lean_inc(v_a_4378_);
lean_inc_ref(v_a_4377_);
lean_inc(v_a_4376_);
lean_inc_ref(v_a_4375_);
lean_inc_ref(v_value_4371_);
v___x_4380_ = lean_infer_type(v_value_4371_, v_a_4375_, v_a_4376_, v_a_4377_, v_a_4378_);
if (lean_obj_tag(v___x_4380_) == 0)
{
lean_object* v_a_4381_; lean_object* v___x_4382_; lean_object* v___x_4383_; 
v_a_4381_ = lean_ctor_get(v___x_4380_, 0);
lean_inc(v_a_4381_);
lean_dec_ref(v___x_4380_);
v___x_4382_ = l_Lean_Expr_headBeta(v_a_4381_);
v___x_4383_ = l_Lean_Meta_mkAuxDefinition(v_name_4370_, v___x_4382_, v_value_4371_, v_zetaDelta_4372_, v_compile_4373_, v_logCompileErrors_4374_, v_a_4375_, v_a_4376_, v_a_4377_, v_a_4378_);
return v___x_4383_;
}
else
{
lean_dec_ref(v_value_4371_);
lean_dec(v_name_4370_);
return v___x_4380_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAuxDefinitionFor___boxed(lean_object* v_name_4384_, lean_object* v_value_4385_, lean_object* v_zetaDelta_4386_, lean_object* v_compile_4387_, lean_object* v_logCompileErrors_4388_, lean_object* v_a_4389_, lean_object* v_a_4390_, lean_object* v_a_4391_, lean_object* v_a_4392_, lean_object* v_a_4393_){
_start:
{
uint8_t v_zetaDelta_boxed_4394_; uint8_t v_compile_boxed_4395_; uint8_t v_logCompileErrors_boxed_4396_; lean_object* v_res_4397_; 
v_zetaDelta_boxed_4394_ = lean_unbox(v_zetaDelta_4386_);
v_compile_boxed_4395_ = lean_unbox(v_compile_4387_);
v_logCompileErrors_boxed_4396_ = lean_unbox(v_logCompileErrors_4388_);
v_res_4397_ = l_Lean_Meta_mkAuxDefinitionFor(v_name_4384_, v_value_4385_, v_zetaDelta_boxed_4394_, v_compile_boxed_4395_, v_logCompileErrors_boxed_4396_, v_a_4389_, v_a_4390_, v_a_4391_, v_a_4392_);
lean_dec(v_a_4392_);
lean_dec_ref(v_a_4391_);
lean_dec(v_a_4390_);
lean_dec_ref(v_a_4389_);
return v_res_4397_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAuxTheorem(lean_object* v_type_4398_, lean_object* v_value_4399_, uint8_t v_zetaDelta_4400_, lean_object* v_kind_x3f_4401_, uint8_t v_cache_4402_, lean_object* v_a_4403_, lean_object* v_a_4404_, lean_object* v_a_4405_, lean_object* v_a_4406_){
_start:
{
lean_object* v___x_4408_; 
v___x_4408_ = l_Lean_Meta_Closure_mkValueTypeClosure(v_type_4398_, v_value_4399_, v_zetaDelta_4400_, v_a_4403_, v_a_4404_, v_a_4405_, v_a_4406_);
if (lean_obj_tag(v___x_4408_) == 0)
{
lean_object* v_a_4409_; lean_object* v_levelParams_4410_; lean_object* v_type_4411_; lean_object* v_value_4412_; lean_object* v_levelArgs_4413_; lean_object* v_exprArgs_4414_; lean_object* v___x_4415_; uint8_t v___x_4416_; lean_object* v___x_4417_; 
v_a_4409_ = lean_ctor_get(v___x_4408_, 0);
lean_inc(v_a_4409_);
lean_dec_ref(v___x_4408_);
v_levelParams_4410_ = lean_ctor_get(v_a_4409_, 0);
lean_inc_ref(v_levelParams_4410_);
v_type_4411_ = lean_ctor_get(v_a_4409_, 1);
lean_inc_ref(v_type_4411_);
v_value_4412_ = lean_ctor_get(v_a_4409_, 2);
lean_inc_ref(v_value_4412_);
v_levelArgs_4413_ = lean_ctor_get(v_a_4409_, 3);
lean_inc_ref(v_levelArgs_4413_);
v_exprArgs_4414_ = lean_ctor_get(v_a_4409_, 4);
lean_inc_ref(v_exprArgs_4414_);
lean_dec(v_a_4409_);
v___x_4415_ = lean_array_to_list(v_levelParams_4410_);
v___x_4416_ = 0;
v___x_4417_ = l_Lean_Meta_mkAuxLemma(v___x_4415_, v_type_4411_, v_value_4412_, v_kind_x3f_4401_, v_cache_4402_, v___x_4416_, v___x_4416_, v___x_4416_, v_a_4403_, v_a_4404_, v_a_4405_, v_a_4406_);
if (lean_obj_tag(v___x_4417_) == 0)
{
lean_object* v_a_4418_; lean_object* v___x_4420_; uint8_t v_isShared_4421_; uint8_t v_isSharedCheck_4428_; 
v_a_4418_ = lean_ctor_get(v___x_4417_, 0);
v_isSharedCheck_4428_ = !lean_is_exclusive(v___x_4417_);
if (v_isSharedCheck_4428_ == 0)
{
v___x_4420_ = v___x_4417_;
v_isShared_4421_ = v_isSharedCheck_4428_;
goto v_resetjp_4419_;
}
else
{
lean_inc(v_a_4418_);
lean_dec(v___x_4417_);
v___x_4420_ = lean_box(0);
v_isShared_4421_ = v_isSharedCheck_4428_;
goto v_resetjp_4419_;
}
v_resetjp_4419_:
{
lean_object* v___x_4422_; lean_object* v___x_4423_; lean_object* v___x_4424_; lean_object* v___x_4426_; 
v___x_4422_ = lean_array_to_list(v_levelArgs_4413_);
v___x_4423_ = l_Lean_mkConst(v_a_4418_, v___x_4422_);
v___x_4424_ = l_Lean_mkAppN(v___x_4423_, v_exprArgs_4414_);
lean_dec_ref(v_exprArgs_4414_);
if (v_isShared_4421_ == 0)
{
lean_ctor_set(v___x_4420_, 0, v___x_4424_);
v___x_4426_ = v___x_4420_;
goto v_reusejp_4425_;
}
else
{
lean_object* v_reuseFailAlloc_4427_; 
v_reuseFailAlloc_4427_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4427_, 0, v___x_4424_);
v___x_4426_ = v_reuseFailAlloc_4427_;
goto v_reusejp_4425_;
}
v_reusejp_4425_:
{
return v___x_4426_;
}
}
}
else
{
lean_object* v_a_4429_; lean_object* v___x_4431_; uint8_t v_isShared_4432_; uint8_t v_isSharedCheck_4436_; 
lean_dec_ref(v_exprArgs_4414_);
lean_dec_ref(v_levelArgs_4413_);
v_a_4429_ = lean_ctor_get(v___x_4417_, 0);
v_isSharedCheck_4436_ = !lean_is_exclusive(v___x_4417_);
if (v_isSharedCheck_4436_ == 0)
{
v___x_4431_ = v___x_4417_;
v_isShared_4432_ = v_isSharedCheck_4436_;
goto v_resetjp_4430_;
}
else
{
lean_inc(v_a_4429_);
lean_dec(v___x_4417_);
v___x_4431_ = lean_box(0);
v_isShared_4432_ = v_isSharedCheck_4436_;
goto v_resetjp_4430_;
}
v_resetjp_4430_:
{
lean_object* v___x_4434_; 
if (v_isShared_4432_ == 0)
{
v___x_4434_ = v___x_4431_;
goto v_reusejp_4433_;
}
else
{
lean_object* v_reuseFailAlloc_4435_; 
v_reuseFailAlloc_4435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4435_, 0, v_a_4429_);
v___x_4434_ = v_reuseFailAlloc_4435_;
goto v_reusejp_4433_;
}
v_reusejp_4433_:
{
return v___x_4434_;
}
}
}
}
else
{
lean_object* v_a_4437_; lean_object* v___x_4439_; uint8_t v_isShared_4440_; uint8_t v_isSharedCheck_4444_; 
lean_dec(v_kind_x3f_4401_);
v_a_4437_ = lean_ctor_get(v___x_4408_, 0);
v_isSharedCheck_4444_ = !lean_is_exclusive(v___x_4408_);
if (v_isSharedCheck_4444_ == 0)
{
v___x_4439_ = v___x_4408_;
v_isShared_4440_ = v_isSharedCheck_4444_;
goto v_resetjp_4438_;
}
else
{
lean_inc(v_a_4437_);
lean_dec(v___x_4408_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAuxTheorem___boxed(lean_object* v_type_4445_, lean_object* v_value_4446_, lean_object* v_zetaDelta_4447_, lean_object* v_kind_x3f_4448_, lean_object* v_cache_4449_, lean_object* v_a_4450_, lean_object* v_a_4451_, lean_object* v_a_4452_, lean_object* v_a_4453_, lean_object* v_a_4454_){
_start:
{
uint8_t v_zetaDelta_boxed_4455_; uint8_t v_cache_boxed_4456_; lean_object* v_res_4457_; 
v_zetaDelta_boxed_4455_ = lean_unbox(v_zetaDelta_4447_);
v_cache_boxed_4456_ = lean_unbox(v_cache_4449_);
v_res_4457_ = l_Lean_Meta_mkAuxTheorem(v_type_4445_, v_value_4446_, v_zetaDelta_boxed_4455_, v_kind_x3f_4448_, v_cache_boxed_4456_, v_a_4450_, v_a_4451_, v_a_4452_, v_a_4453_);
lean_dec(v_a_4453_);
lean_dec_ref(v_a_4452_);
lean_dec(v_a_4451_);
lean_dec_ref(v_a_4450_);
return v_res_4457_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_initFn_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4513_; uint8_t v___x_4514_; lean_object* v___x_4515_; lean_object* v___x_4516_; 
v___x_4513_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__10));
v___x_4514_ = 0;
v___x_4515_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2_));
v___x_4516_ = l_Lean_registerTraceClass(v___x_4513_, v___x_4514_, v___x_4515_);
return v___x_4516_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_initFn_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2____boxed(lean_object* v_a_4517_){
_start:
{
lean_object* v_res_4518_; 
v_res_4518_ = l___private_Lean_Meta_Closure_0__Lean_Meta_initFn_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2_();
return v_res_4518_;
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
