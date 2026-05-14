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
v___y_373_ = v_a_434_;
v___y_374_ = v___y_433_;
v___y_375_ = v___x_437_;
goto v___jp_372_;
}
else
{
size_t v___x_438_; size_t v___x_439_; uint8_t v___x_440_; 
v___x_438_ = lean_ptr_addr(v_a_431_);
v___x_439_ = lean_ptr_addr(v_a_434_);
v___x_440_ = lean_usize_dec_eq(v___x_438_, v___x_439_);
v___y_373_ = v_a_434_;
v___y_374_ = v___y_433_;
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
v___x_376_ = l_Lean_mkLevelMax_x27(v___y_374_, v___y_373_);
v___x_377_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_377_, 0, v___x_376_);
return v___x_377_;
}
else
{
lean_object* v___x_378_; lean_object* v___x_379_; 
v___x_378_ = l_Lean_simpLevelMax_x27(v___y_374_, v___y_373_, v_x_369_);
lean_dec(v_x_369_);
lean_dec(v___y_373_);
lean_dec(v___y_374_);
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
uint8_t v___y_2268__boxed_775_; lean_object* v_res_776_; 
v___y_2268__boxed_775_ = lean_unbox(v___y_768_);
v_res_776_ = l_Lean_instantiateMVars___at___00Lean_Meta_Closure_preprocess_spec__0(v_e_767_, v___y_2268__boxed_775_, v___y_769_, v___y_770_, v___y_771_, v___y_772_, v___y_773_);
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
lean_object* v_a_786_; uint8_t v___x_787_; lean_object* v___x_788_; 
v_a_786_ = lean_ctor_get(v___x_785_, 0);
lean_inc_n(v_a_786_, 2);
lean_dec_ref(v___x_785_);
v___x_787_ = 0;
v___x_788_ = l_Lean_Meta_check(v_a_786_, v___x_787_, v_a_780_, v_a_781_, v_a_782_, v_a_783_);
if (lean_obj_tag(v___x_788_) == 0)
{
lean_object* v___x_790_; uint8_t v_isShared_791_; uint8_t v_isSharedCheck_795_; 
v_isSharedCheck_795_ = !lean_is_exclusive(v___x_788_);
if (v_isSharedCheck_795_ == 0)
{
lean_object* v_unused_796_; 
v_unused_796_ = lean_ctor_get(v___x_788_, 0);
lean_dec(v_unused_796_);
v___x_790_ = v___x_788_;
v_isShared_791_ = v_isSharedCheck_795_;
goto v_resetjp_789_;
}
else
{
lean_dec(v___x_788_);
v___x_790_ = lean_box(0);
v_isShared_791_ = v_isSharedCheck_795_;
goto v_resetjp_789_;
}
v_resetjp_789_:
{
lean_object* v___x_793_; 
if (v_isShared_791_ == 0)
{
lean_ctor_set(v___x_790_, 0, v_a_786_);
v___x_793_ = v___x_790_;
goto v_reusejp_792_;
}
else
{
lean_object* v_reuseFailAlloc_794_; 
v_reuseFailAlloc_794_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_794_, 0, v_a_786_);
v___x_793_ = v_reuseFailAlloc_794_;
goto v_reusejp_792_;
}
v_reusejp_792_:
{
return v___x_793_;
}
}
}
else
{
lean_object* v_a_797_; lean_object* v___x_799_; uint8_t v_isShared_800_; uint8_t v_isSharedCheck_804_; 
lean_dec(v_a_786_);
v_a_797_ = lean_ctor_get(v___x_788_, 0);
v_isSharedCheck_804_ = !lean_is_exclusive(v___x_788_);
if (v_isSharedCheck_804_ == 0)
{
v___x_799_ = v___x_788_;
v_isShared_800_ = v_isSharedCheck_804_;
goto v_resetjp_798_;
}
else
{
lean_inc(v_a_797_);
lean_dec(v___x_788_);
v___x_799_ = lean_box(0);
v_isShared_800_ = v_isSharedCheck_804_;
goto v_resetjp_798_;
}
v_resetjp_798_:
{
lean_object* v___x_802_; 
if (v_isShared_800_ == 0)
{
v___x_802_ = v___x_799_;
goto v_reusejp_801_;
}
else
{
lean_object* v_reuseFailAlloc_803_; 
v_reuseFailAlloc_803_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_803_, 0, v_a_797_);
v___x_802_ = v_reuseFailAlloc_803_;
goto v_reusejp_801_;
}
v_reusejp_801_:
{
return v___x_802_;
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
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_preprocess___boxed(lean_object* v_e_805_, lean_object* v_a_806_, lean_object* v_a_807_, lean_object* v_a_808_, lean_object* v_a_809_, lean_object* v_a_810_, lean_object* v_a_811_, lean_object* v_a_812_){
_start:
{
uint8_t v_a_boxed_813_; lean_object* v_res_814_; 
v_a_boxed_813_ = lean_unbox(v_a_806_);
v_res_814_ = l_Lean_Meta_Closure_preprocess(v_e_805_, v_a_boxed_813_, v_a_807_, v_a_808_, v_a_809_, v_a_810_, v_a_811_);
lean_dec(v_a_811_);
lean_dec_ref(v_a_810_);
lean_dec(v_a_809_);
lean_dec_ref(v_a_808_);
lean_dec(v_a_807_);
return v_res_814_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkNextUserName___redArg(lean_object* v_a_818_){
_start:
{
lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v_visitedLevel_822_; lean_object* v_visitedExpr_823_; lean_object* v_levelParams_824_; lean_object* v_nextLevelIdx_825_; lean_object* v_levelArgs_826_; lean_object* v_newLocalDecls_827_; lean_object* v_newLocalDeclsForMVars_828_; lean_object* v_newLetDecls_829_; lean_object* v_nextExprIdx_830_; lean_object* v_exprMVarArgs_831_; lean_object* v_exprFVarArgs_832_; lean_object* v_toProcess_833_; lean_object* v___x_835_; uint8_t v_isShared_836_; uint8_t v_isSharedCheck_847_; 
v___x_820_ = lean_st_ref_get(v_a_818_);
v___x_821_ = lean_st_ref_take(v_a_818_);
v_visitedLevel_822_ = lean_ctor_get(v___x_821_, 0);
v_visitedExpr_823_ = lean_ctor_get(v___x_821_, 1);
v_levelParams_824_ = lean_ctor_get(v___x_821_, 2);
v_nextLevelIdx_825_ = lean_ctor_get(v___x_821_, 3);
v_levelArgs_826_ = lean_ctor_get(v___x_821_, 4);
v_newLocalDecls_827_ = lean_ctor_get(v___x_821_, 5);
v_newLocalDeclsForMVars_828_ = lean_ctor_get(v___x_821_, 6);
v_newLetDecls_829_ = lean_ctor_get(v___x_821_, 7);
v_nextExprIdx_830_ = lean_ctor_get(v___x_821_, 8);
v_exprMVarArgs_831_ = lean_ctor_get(v___x_821_, 9);
v_exprFVarArgs_832_ = lean_ctor_get(v___x_821_, 10);
v_toProcess_833_ = lean_ctor_get(v___x_821_, 11);
v_isSharedCheck_847_ = !lean_is_exclusive(v___x_821_);
if (v_isSharedCheck_847_ == 0)
{
v___x_835_ = v___x_821_;
v_isShared_836_ = v_isSharedCheck_847_;
goto v_resetjp_834_;
}
else
{
lean_inc(v_toProcess_833_);
lean_inc(v_exprFVarArgs_832_);
lean_inc(v_exprMVarArgs_831_);
lean_inc(v_nextExprIdx_830_);
lean_inc(v_newLetDecls_829_);
lean_inc(v_newLocalDeclsForMVars_828_);
lean_inc(v_newLocalDecls_827_);
lean_inc(v_levelArgs_826_);
lean_inc(v_nextLevelIdx_825_);
lean_inc(v_levelParams_824_);
lean_inc(v_visitedExpr_823_);
lean_inc(v_visitedLevel_822_);
lean_dec(v___x_821_);
v___x_835_ = lean_box(0);
v_isShared_836_ = v_isSharedCheck_847_;
goto v_resetjp_834_;
}
v_resetjp_834_:
{
lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_840_; 
v___x_837_ = lean_unsigned_to_nat(1u);
v___x_838_ = lean_nat_add(v_nextExprIdx_830_, v___x_837_);
lean_dec(v_nextExprIdx_830_);
if (v_isShared_836_ == 0)
{
lean_ctor_set(v___x_835_, 8, v___x_838_);
v___x_840_ = v___x_835_;
goto v_reusejp_839_;
}
else
{
lean_object* v_reuseFailAlloc_846_; 
v_reuseFailAlloc_846_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_846_, 0, v_visitedLevel_822_);
lean_ctor_set(v_reuseFailAlloc_846_, 1, v_visitedExpr_823_);
lean_ctor_set(v_reuseFailAlloc_846_, 2, v_levelParams_824_);
lean_ctor_set(v_reuseFailAlloc_846_, 3, v_nextLevelIdx_825_);
lean_ctor_set(v_reuseFailAlloc_846_, 4, v_levelArgs_826_);
lean_ctor_set(v_reuseFailAlloc_846_, 5, v_newLocalDecls_827_);
lean_ctor_set(v_reuseFailAlloc_846_, 6, v_newLocalDeclsForMVars_828_);
lean_ctor_set(v_reuseFailAlloc_846_, 7, v_newLetDecls_829_);
lean_ctor_set(v_reuseFailAlloc_846_, 8, v___x_838_);
lean_ctor_set(v_reuseFailAlloc_846_, 9, v_exprMVarArgs_831_);
lean_ctor_set(v_reuseFailAlloc_846_, 10, v_exprFVarArgs_832_);
lean_ctor_set(v_reuseFailAlloc_846_, 11, v_toProcess_833_);
v___x_840_ = v_reuseFailAlloc_846_;
goto v_reusejp_839_;
}
v_reusejp_839_:
{
lean_object* v___x_841_; lean_object* v_nextExprIdx_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; 
v___x_841_ = lean_st_ref_set(v_a_818_, v___x_840_);
v_nextExprIdx_842_ = lean_ctor_get(v___x_820_, 8);
lean_inc(v_nextExprIdx_842_);
lean_dec(v___x_820_);
v___x_843_ = ((lean_object*)(l_Lean_Meta_Closure_mkNextUserName___redArg___closed__1));
v___x_844_ = lean_name_append_index_after(v___x_843_, v_nextExprIdx_842_);
v___x_845_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_845_, 0, v___x_844_);
return v___x_845_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkNextUserName___redArg___boxed(lean_object* v_a_848_, lean_object* v_a_849_){
_start:
{
lean_object* v_res_850_; 
v_res_850_ = l_Lean_Meta_Closure_mkNextUserName___redArg(v_a_848_);
lean_dec(v_a_848_);
return v_res_850_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkNextUserName(uint8_t v_a_851_, lean_object* v_a_852_, lean_object* v_a_853_, lean_object* v_a_854_, lean_object* v_a_855_, lean_object* v_a_856_){
_start:
{
lean_object* v___x_858_; 
v___x_858_ = l_Lean_Meta_Closure_mkNextUserName___redArg(v_a_852_);
return v___x_858_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkNextUserName___boxed(lean_object* v_a_859_, lean_object* v_a_860_, lean_object* v_a_861_, lean_object* v_a_862_, lean_object* v_a_863_, lean_object* v_a_864_, lean_object* v_a_865_){
_start:
{
uint8_t v_a_boxed_866_; lean_object* v_res_867_; 
v_a_boxed_866_ = lean_unbox(v_a_859_);
v_res_867_ = l_Lean_Meta_Closure_mkNextUserName(v_a_boxed_866_, v_a_860_, v_a_861_, v_a_862_, v_a_863_, v_a_864_);
lean_dec(v_a_864_);
lean_dec_ref(v_a_863_);
lean_dec(v_a_862_);
lean_dec_ref(v_a_861_);
lean_dec(v_a_860_);
return v_res_867_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushToProcess___redArg(lean_object* v_elem_868_, lean_object* v_a_869_){
_start:
{
lean_object* v___x_871_; lean_object* v_visitedLevel_872_; lean_object* v_visitedExpr_873_; lean_object* v_levelParams_874_; lean_object* v_nextLevelIdx_875_; lean_object* v_levelArgs_876_; lean_object* v_newLocalDecls_877_; lean_object* v_newLocalDeclsForMVars_878_; lean_object* v_newLetDecls_879_; lean_object* v_nextExprIdx_880_; lean_object* v_exprMVarArgs_881_; lean_object* v_exprFVarArgs_882_; lean_object* v_toProcess_883_; lean_object* v___x_885_; uint8_t v_isShared_886_; uint8_t v_isSharedCheck_894_; 
v___x_871_ = lean_st_ref_take(v_a_869_);
v_visitedLevel_872_ = lean_ctor_get(v___x_871_, 0);
v_visitedExpr_873_ = lean_ctor_get(v___x_871_, 1);
v_levelParams_874_ = lean_ctor_get(v___x_871_, 2);
v_nextLevelIdx_875_ = lean_ctor_get(v___x_871_, 3);
v_levelArgs_876_ = lean_ctor_get(v___x_871_, 4);
v_newLocalDecls_877_ = lean_ctor_get(v___x_871_, 5);
v_newLocalDeclsForMVars_878_ = lean_ctor_get(v___x_871_, 6);
v_newLetDecls_879_ = lean_ctor_get(v___x_871_, 7);
v_nextExprIdx_880_ = lean_ctor_get(v___x_871_, 8);
v_exprMVarArgs_881_ = lean_ctor_get(v___x_871_, 9);
v_exprFVarArgs_882_ = lean_ctor_get(v___x_871_, 10);
v_toProcess_883_ = lean_ctor_get(v___x_871_, 11);
v_isSharedCheck_894_ = !lean_is_exclusive(v___x_871_);
if (v_isSharedCheck_894_ == 0)
{
v___x_885_ = v___x_871_;
v_isShared_886_ = v_isSharedCheck_894_;
goto v_resetjp_884_;
}
else
{
lean_inc(v_toProcess_883_);
lean_inc(v_exprFVarArgs_882_);
lean_inc(v_exprMVarArgs_881_);
lean_inc(v_nextExprIdx_880_);
lean_inc(v_newLetDecls_879_);
lean_inc(v_newLocalDeclsForMVars_878_);
lean_inc(v_newLocalDecls_877_);
lean_inc(v_levelArgs_876_);
lean_inc(v_nextLevelIdx_875_);
lean_inc(v_levelParams_874_);
lean_inc(v_visitedExpr_873_);
lean_inc(v_visitedLevel_872_);
lean_dec(v___x_871_);
v___x_885_ = lean_box(0);
v_isShared_886_ = v_isSharedCheck_894_;
goto v_resetjp_884_;
}
v_resetjp_884_:
{
lean_object* v___x_887_; lean_object* v___x_889_; 
v___x_887_ = lean_array_push(v_toProcess_883_, v_elem_868_);
if (v_isShared_886_ == 0)
{
lean_ctor_set(v___x_885_, 11, v___x_887_);
v___x_889_ = v___x_885_;
goto v_reusejp_888_;
}
else
{
lean_object* v_reuseFailAlloc_893_; 
v_reuseFailAlloc_893_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_893_, 0, v_visitedLevel_872_);
lean_ctor_set(v_reuseFailAlloc_893_, 1, v_visitedExpr_873_);
lean_ctor_set(v_reuseFailAlloc_893_, 2, v_levelParams_874_);
lean_ctor_set(v_reuseFailAlloc_893_, 3, v_nextLevelIdx_875_);
lean_ctor_set(v_reuseFailAlloc_893_, 4, v_levelArgs_876_);
lean_ctor_set(v_reuseFailAlloc_893_, 5, v_newLocalDecls_877_);
lean_ctor_set(v_reuseFailAlloc_893_, 6, v_newLocalDeclsForMVars_878_);
lean_ctor_set(v_reuseFailAlloc_893_, 7, v_newLetDecls_879_);
lean_ctor_set(v_reuseFailAlloc_893_, 8, v_nextExprIdx_880_);
lean_ctor_set(v_reuseFailAlloc_893_, 9, v_exprMVarArgs_881_);
lean_ctor_set(v_reuseFailAlloc_893_, 10, v_exprFVarArgs_882_);
lean_ctor_set(v_reuseFailAlloc_893_, 11, v___x_887_);
v___x_889_ = v_reuseFailAlloc_893_;
goto v_reusejp_888_;
}
v_reusejp_888_:
{
lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; 
v___x_890_ = lean_st_ref_set(v_a_869_, v___x_889_);
v___x_891_ = lean_box(0);
v___x_892_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_892_, 0, v___x_891_);
return v___x_892_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushToProcess___redArg___boxed(lean_object* v_elem_895_, lean_object* v_a_896_, lean_object* v_a_897_){
_start:
{
lean_object* v_res_898_; 
v_res_898_ = l_Lean_Meta_Closure_pushToProcess___redArg(v_elem_895_, v_a_896_);
lean_dec(v_a_896_);
return v_res_898_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushToProcess(lean_object* v_elem_899_, uint8_t v_a_900_, lean_object* v_a_901_, lean_object* v_a_902_, lean_object* v_a_903_, lean_object* v_a_904_, lean_object* v_a_905_){
_start:
{
lean_object* v___x_907_; 
v___x_907_ = l_Lean_Meta_Closure_pushToProcess___redArg(v_elem_899_, v_a_901_);
return v___x_907_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushToProcess___boxed(lean_object* v_elem_908_, lean_object* v_a_909_, lean_object* v_a_910_, lean_object* v_a_911_, lean_object* v_a_912_, lean_object* v_a_913_, lean_object* v_a_914_, lean_object* v_a_915_){
_start:
{
uint8_t v_a_boxed_916_; lean_object* v_res_917_; 
v_a_boxed_916_ = lean_unbox(v_a_909_);
v_res_917_ = l_Lean_Meta_Closure_pushToProcess(v_elem_908_, v_a_boxed_916_, v_a_910_, v_a_911_, v_a_912_, v_a_913_, v_a_914_);
lean_dec(v_a_914_);
lean_dec_ref(v_a_913_);
lean_dec(v_a_912_);
lean_dec_ref(v_a_911_);
lean_dec(v_a_910_);
return v_res_917_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__4___redArg(lean_object* v_mvarId_918_, lean_object* v___y_919_){
_start:
{
lean_object* v___x_921_; lean_object* v_mctx_922_; lean_object* v___x_923_; lean_object* v___x_924_; 
v___x_921_ = lean_st_ref_get(v___y_919_);
v_mctx_922_ = lean_ctor_get(v___x_921_, 0);
lean_inc_ref(v_mctx_922_);
lean_dec(v___x_921_);
v___x_923_ = l_Lean_MetavarContext_getDelayedMVarAssignmentCore_x3f(v_mctx_922_, v_mvarId_918_);
lean_dec_ref(v_mctx_922_);
v___x_924_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_924_, 0, v___x_923_);
return v___x_924_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__4___redArg___boxed(lean_object* v_mvarId_925_, lean_object* v___y_926_, lean_object* v___y_927_){
_start:
{
lean_object* v_res_928_; 
v_res_928_ = l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__4___redArg(v_mvarId_925_, v___y_926_);
lean_dec(v___y_926_);
lean_dec(v_mvarId_925_);
return v_res_928_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__4(lean_object* v_mvarId_929_, uint8_t v___y_930_, lean_object* v___y_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_){
_start:
{
lean_object* v___x_937_; 
v___x_937_ = l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__4___redArg(v_mvarId_929_, v___y_933_);
return v___x_937_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__4___boxed(lean_object* v_mvarId_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_, lean_object* v___y_943_, lean_object* v___y_944_, lean_object* v___y_945_){
_start:
{
uint8_t v___y_17892__boxed_946_; lean_object* v_res_947_; 
v___y_17892__boxed_946_ = lean_unbox(v___y_939_);
v_res_947_ = l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__4(v_mvarId_938_, v___y_17892__boxed_946_, v___y_940_, v___y_941_, v___y_942_, v___y_943_, v___y_944_);
lean_dec(v___y_944_);
lean_dec_ref(v___y_943_);
lean_dec(v___y_942_);
lean_dec_ref(v___y_941_);
lean_dec(v___y_940_);
lean_dec(v_mvarId_938_);
return v_res_947_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Closure_collectExprAux_spec__5___redArg___lam__0(lean_object* v_k_948_, uint8_t v___y_949_, lean_object* v___y_950_, lean_object* v_b_951_, lean_object* v_c_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_){
_start:
{
lean_object* v___x_958_; lean_object* v___x_959_; 
v___x_958_ = lean_box(v___y_949_);
lean_inc(v___y_956_);
lean_inc_ref(v___y_955_);
lean_inc(v___y_954_);
lean_inc_ref(v___y_953_);
lean_inc(v___y_950_);
v___x_959_ = lean_apply_9(v_k_948_, v_b_951_, v_c_952_, v___x_958_, v___y_950_, v___y_953_, v___y_954_, v___y_955_, v___y_956_, lean_box(0));
return v___x_959_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Closure_collectExprAux_spec__5___redArg___lam__0___boxed(lean_object* v_k_960_, lean_object* v___y_961_, lean_object* v___y_962_, lean_object* v_b_963_, lean_object* v_c_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_){
_start:
{
uint8_t v___y_17915__boxed_970_; lean_object* v_res_971_; 
v___y_17915__boxed_970_ = lean_unbox(v___y_961_);
v_res_971_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Closure_collectExprAux_spec__5___redArg___lam__0(v_k_960_, v___y_17915__boxed_970_, v___y_962_, v_b_963_, v_c_964_, v___y_965_, v___y_966_, v___y_967_, v___y_968_);
lean_dec(v___y_968_);
lean_dec_ref(v___y_967_);
lean_dec(v___y_966_);
lean_dec_ref(v___y_965_);
lean_dec(v___y_962_);
return v_res_971_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Closure_collectExprAux_spec__5___redArg(lean_object* v_type_972_, lean_object* v_maxFVars_x3f_973_, lean_object* v_k_974_, uint8_t v_cleanupAnnotations_975_, uint8_t v_whnfType_976_, uint8_t v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_, lean_object* v___y_980_, lean_object* v___y_981_, lean_object* v___y_982_){
_start:
{
lean_object* v___x_984_; lean_object* v___f_985_; lean_object* v___x_986_; 
v___x_984_ = lean_box(v___y_977_);
lean_inc(v___y_978_);
v___f_985_ = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Closure_collectExprAux_spec__5___redArg___lam__0___boxed), 10, 3);
lean_closure_set(v___f_985_, 0, v_k_974_);
lean_closure_set(v___f_985_, 1, v___x_984_);
lean_closure_set(v___f_985_, 2, v___y_978_);
v___x_986_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_972_, v_maxFVars_x3f_973_, v___f_985_, v_cleanupAnnotations_975_, v_whnfType_976_, v___y_979_, v___y_980_, v___y_981_, v___y_982_);
if (lean_obj_tag(v___x_986_) == 0)
{
return v___x_986_;
}
else
{
lean_object* v_a_987_; lean_object* v___x_989_; uint8_t v_isShared_990_; uint8_t v_isSharedCheck_994_; 
v_a_987_ = lean_ctor_get(v___x_986_, 0);
v_isSharedCheck_994_ = !lean_is_exclusive(v___x_986_);
if (v_isSharedCheck_994_ == 0)
{
v___x_989_ = v___x_986_;
v_isShared_990_ = v_isSharedCheck_994_;
goto v_resetjp_988_;
}
else
{
lean_inc(v_a_987_);
lean_dec(v___x_986_);
v___x_989_ = lean_box(0);
v_isShared_990_ = v_isSharedCheck_994_;
goto v_resetjp_988_;
}
v_resetjp_988_:
{
lean_object* v___x_992_; 
if (v_isShared_990_ == 0)
{
v___x_992_ = v___x_989_;
goto v_reusejp_991_;
}
else
{
lean_object* v_reuseFailAlloc_993_; 
v_reuseFailAlloc_993_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_993_, 0, v_a_987_);
v___x_992_ = v_reuseFailAlloc_993_;
goto v_reusejp_991_;
}
v_reusejp_991_:
{
return v___x_992_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Closure_collectExprAux_spec__5___redArg___boxed(lean_object* v_type_995_, lean_object* v_maxFVars_x3f_996_, lean_object* v_k_997_, lean_object* v_cleanupAnnotations_998_, lean_object* v_whnfType_999_, lean_object* v___y_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1007_; uint8_t v_whnfType_boxed_1008_; uint8_t v___y_17940__boxed_1009_; lean_object* v_res_1010_; 
v_cleanupAnnotations_boxed_1007_ = lean_unbox(v_cleanupAnnotations_998_);
v_whnfType_boxed_1008_ = lean_unbox(v_whnfType_999_);
v___y_17940__boxed_1009_ = lean_unbox(v___y_1000_);
v_res_1010_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Closure_collectExprAux_spec__5___redArg(v_type_995_, v_maxFVars_x3f_996_, v_k_997_, v_cleanupAnnotations_boxed_1007_, v_whnfType_boxed_1008_, v___y_17940__boxed_1009_, v___y_1001_, v___y_1002_, v___y_1003_, v___y_1004_, v___y_1005_);
lean_dec(v___y_1005_);
lean_dec_ref(v___y_1004_);
lean_dec(v___y_1003_);
lean_dec_ref(v___y_1002_);
lean_dec(v___y_1001_);
return v_res_1010_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Closure_collectExprAux_spec__5(lean_object* v_00_u03b1_1011_, lean_object* v_type_1012_, lean_object* v_maxFVars_x3f_1013_, lean_object* v_k_1014_, uint8_t v_cleanupAnnotations_1015_, uint8_t v_whnfType_1016_, uint8_t v___y_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_){
_start:
{
lean_object* v___x_1024_; 
v___x_1024_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Closure_collectExprAux_spec__5___redArg(v_type_1012_, v_maxFVars_x3f_1013_, v_k_1014_, v_cleanupAnnotations_1015_, v_whnfType_1016_, v___y_1017_, v___y_1018_, v___y_1019_, v___y_1020_, v___y_1021_, v___y_1022_);
return v___x_1024_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Closure_collectExprAux_spec__5___boxed(lean_object* v_00_u03b1_1025_, lean_object* v_type_1026_, lean_object* v_maxFVars_x3f_1027_, lean_object* v_k_1028_, lean_object* v_cleanupAnnotations_1029_, lean_object* v_whnfType_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1038_; uint8_t v_whnfType_boxed_1039_; uint8_t v___y_17984__boxed_1040_; lean_object* v_res_1041_; 
v_cleanupAnnotations_boxed_1038_ = lean_unbox(v_cleanupAnnotations_1029_);
v_whnfType_boxed_1039_ = lean_unbox(v_whnfType_1030_);
v___y_17984__boxed_1040_ = lean_unbox(v___y_1031_);
v_res_1041_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Closure_collectExprAux_spec__5(v_00_u03b1_1025_, v_type_1026_, v_maxFVars_x3f_1027_, v_k_1028_, v_cleanupAnnotations_boxed_1038_, v_whnfType_boxed_1039_, v___y_17984__boxed_1040_, v___y_1032_, v___y_1033_, v___y_1034_, v___y_1035_, v___y_1036_);
lean_dec(v___y_1036_);
lean_dec_ref(v___y_1035_);
lean_dec(v___y_1034_);
lean_dec_ref(v___y_1033_);
lean_dec(v___y_1032_);
return v_res_1041_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0_spec__0___redArg(lean_object* v_a_1042_, lean_object* v_x_1043_){
_start:
{
if (lean_obj_tag(v_x_1043_) == 0)
{
lean_object* v___x_1044_; 
v___x_1044_ = lean_box(0);
return v___x_1044_;
}
else
{
lean_object* v_key_1045_; lean_object* v_value_1046_; lean_object* v_tail_1047_; uint8_t v___x_1048_; 
v_key_1045_ = lean_ctor_get(v_x_1043_, 0);
v_value_1046_ = lean_ctor_get(v_x_1043_, 1);
v_tail_1047_ = lean_ctor_get(v_x_1043_, 2);
v___x_1048_ = l_Lean_ExprStructEq_beq(v_key_1045_, v_a_1042_);
if (v___x_1048_ == 0)
{
v_x_1043_ = v_tail_1047_;
goto _start;
}
else
{
lean_object* v___x_1050_; 
lean_inc(v_value_1046_);
v___x_1050_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1050_, 0, v_value_1046_);
return v___x_1050_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0_spec__0___redArg___boxed(lean_object* v_a_1051_, lean_object* v_x_1052_){
_start:
{
lean_object* v_res_1053_; 
v_res_1053_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0_spec__0___redArg(v_a_1051_, v_x_1052_);
lean_dec(v_x_1052_);
lean_dec_ref(v_a_1051_);
return v_res_1053_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0___redArg(lean_object* v_m_1054_, lean_object* v_a_1055_){
_start:
{
lean_object* v_buckets_1056_; lean_object* v___x_1057_; uint64_t v___x_1058_; uint64_t v___x_1059_; uint64_t v___x_1060_; uint64_t v_fold_1061_; uint64_t v___x_1062_; uint64_t v___x_1063_; uint64_t v___x_1064_; size_t v___x_1065_; size_t v___x_1066_; size_t v___x_1067_; size_t v___x_1068_; size_t v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; 
v_buckets_1056_ = lean_ctor_get(v_m_1054_, 1);
v___x_1057_ = lean_array_get_size(v_buckets_1056_);
v___x_1058_ = l_Lean_ExprStructEq_hash(v_a_1055_);
v___x_1059_ = 32ULL;
v___x_1060_ = lean_uint64_shift_right(v___x_1058_, v___x_1059_);
v_fold_1061_ = lean_uint64_xor(v___x_1058_, v___x_1060_);
v___x_1062_ = 16ULL;
v___x_1063_ = lean_uint64_shift_right(v_fold_1061_, v___x_1062_);
v___x_1064_ = lean_uint64_xor(v_fold_1061_, v___x_1063_);
v___x_1065_ = lean_uint64_to_usize(v___x_1064_);
v___x_1066_ = lean_usize_of_nat(v___x_1057_);
v___x_1067_ = ((size_t)1ULL);
v___x_1068_ = lean_usize_sub(v___x_1066_, v___x_1067_);
v___x_1069_ = lean_usize_land(v___x_1065_, v___x_1068_);
v___x_1070_ = lean_array_uget_borrowed(v_buckets_1056_, v___x_1069_);
v___x_1071_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0_spec__0___redArg(v_a_1055_, v___x_1070_);
return v___x_1071_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0___redArg___boxed(lean_object* v_m_1072_, lean_object* v_a_1073_){
_start:
{
lean_object* v_res_1074_; 
v_res_1074_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0___redArg(v_m_1072_, v_a_1073_);
lean_dec_ref(v_a_1073_);
lean_dec_ref(v_m_1072_);
return v_res_1074_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Closure_collectExprAux_spec__2___redArg(lean_object* v_x_1075_, lean_object* v_x_1076_, lean_object* v___y_1077_){
_start:
{
if (lean_obj_tag(v_x_1075_) == 0)
{
lean_object* v___x_1079_; lean_object* v___x_1080_; 
v___x_1079_ = l_List_reverse___redArg(v_x_1076_);
v___x_1080_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1080_, 0, v___x_1079_);
return v___x_1080_;
}
else
{
lean_object* v_head_1081_; lean_object* v_tail_1082_; lean_object* v___x_1084_; uint8_t v_isShared_1085_; uint8_t v_isSharedCheck_1100_; 
v_head_1081_ = lean_ctor_get(v_x_1075_, 0);
v_tail_1082_ = lean_ctor_get(v_x_1075_, 1);
v_isSharedCheck_1100_ = !lean_is_exclusive(v_x_1075_);
if (v_isSharedCheck_1100_ == 0)
{
v___x_1084_ = v_x_1075_;
v_isShared_1085_ = v_isSharedCheck_1100_;
goto v_resetjp_1083_;
}
else
{
lean_inc(v_tail_1082_);
lean_inc(v_head_1081_);
lean_dec(v_x_1075_);
v___x_1084_ = lean_box(0);
v_isShared_1085_ = v_isSharedCheck_1100_;
goto v_resetjp_1083_;
}
v_resetjp_1083_:
{
lean_object* v___x_1086_; 
v___x_1086_ = l_Lean_Meta_Closure_collectLevel___redArg(v_head_1081_, v___y_1077_);
if (lean_obj_tag(v___x_1086_) == 0)
{
lean_object* v_a_1087_; lean_object* v___x_1089_; 
v_a_1087_ = lean_ctor_get(v___x_1086_, 0);
lean_inc(v_a_1087_);
lean_dec_ref(v___x_1086_);
if (v_isShared_1085_ == 0)
{
lean_ctor_set(v___x_1084_, 1, v_x_1076_);
lean_ctor_set(v___x_1084_, 0, v_a_1087_);
v___x_1089_ = v___x_1084_;
goto v_reusejp_1088_;
}
else
{
lean_object* v_reuseFailAlloc_1091_; 
v_reuseFailAlloc_1091_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1091_, 0, v_a_1087_);
lean_ctor_set(v_reuseFailAlloc_1091_, 1, v_x_1076_);
v___x_1089_ = v_reuseFailAlloc_1091_;
goto v_reusejp_1088_;
}
v_reusejp_1088_:
{
v_x_1075_ = v_tail_1082_;
v_x_1076_ = v___x_1089_;
goto _start;
}
}
else
{
lean_object* v_a_1092_; lean_object* v___x_1094_; uint8_t v_isShared_1095_; uint8_t v_isSharedCheck_1099_; 
lean_del_object(v___x_1084_);
lean_dec(v_tail_1082_);
lean_dec(v_x_1076_);
v_a_1092_ = lean_ctor_get(v___x_1086_, 0);
v_isSharedCheck_1099_ = !lean_is_exclusive(v___x_1086_);
if (v_isSharedCheck_1099_ == 0)
{
v___x_1094_ = v___x_1086_;
v_isShared_1095_ = v_isSharedCheck_1099_;
goto v_resetjp_1093_;
}
else
{
lean_inc(v_a_1092_);
lean_dec(v___x_1086_);
v___x_1094_ = lean_box(0);
v_isShared_1095_ = v_isSharedCheck_1099_;
goto v_resetjp_1093_;
}
v_resetjp_1093_:
{
lean_object* v___x_1097_; 
if (v_isShared_1095_ == 0)
{
v___x_1097_ = v___x_1094_;
goto v_reusejp_1096_;
}
else
{
lean_object* v_reuseFailAlloc_1098_; 
v_reuseFailAlloc_1098_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1098_, 0, v_a_1092_);
v___x_1097_ = v_reuseFailAlloc_1098_;
goto v_reusejp_1096_;
}
v_reusejp_1096_:
{
return v___x_1097_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Closure_collectExprAux_spec__2___redArg___boxed(lean_object* v_x_1101_, lean_object* v_x_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_){
_start:
{
lean_object* v_res_1105_; 
v_res_1105_ = l_List_mapM_loop___at___00Lean_Meta_Closure_collectExprAux_spec__2___redArg(v_x_1101_, v_x_1102_, v___y_1103_);
lean_dec(v___y_1103_);
return v_res_1105_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Closure_collectExprAux_spec__3_spec__7___redArg(lean_object* v___y_1106_){
_start:
{
lean_object* v___x_1108_; lean_object* v_ngen_1109_; lean_object* v_namePrefix_1110_; lean_object* v_idx_1111_; lean_object* v___x_1113_; uint8_t v_isShared_1114_; uint8_t v_isSharedCheck_1141_; 
v___x_1108_ = lean_st_ref_get(v___y_1106_);
v_ngen_1109_ = lean_ctor_get(v___x_1108_, 2);
lean_inc_ref(v_ngen_1109_);
lean_dec(v___x_1108_);
v_namePrefix_1110_ = lean_ctor_get(v_ngen_1109_, 0);
v_idx_1111_ = lean_ctor_get(v_ngen_1109_, 1);
v_isSharedCheck_1141_ = !lean_is_exclusive(v_ngen_1109_);
if (v_isSharedCheck_1141_ == 0)
{
v___x_1113_ = v_ngen_1109_;
v_isShared_1114_ = v_isSharedCheck_1141_;
goto v_resetjp_1112_;
}
else
{
lean_inc(v_idx_1111_);
lean_inc(v_namePrefix_1110_);
lean_dec(v_ngen_1109_);
v___x_1113_ = lean_box(0);
v_isShared_1114_ = v_isSharedCheck_1141_;
goto v_resetjp_1112_;
}
v_resetjp_1112_:
{
lean_object* v___x_1115_; lean_object* v_env_1116_; lean_object* v_nextMacroScope_1117_; lean_object* v_auxDeclNGen_1118_; lean_object* v_traceState_1119_; lean_object* v_cache_1120_; lean_object* v_messages_1121_; lean_object* v_infoState_1122_; lean_object* v_snapshotTasks_1123_; lean_object* v_newDecls_1124_; lean_object* v___x_1126_; uint8_t v_isShared_1127_; uint8_t v_isSharedCheck_1139_; 
v___x_1115_ = lean_st_ref_take(v___y_1106_);
v_env_1116_ = lean_ctor_get(v___x_1115_, 0);
v_nextMacroScope_1117_ = lean_ctor_get(v___x_1115_, 1);
v_auxDeclNGen_1118_ = lean_ctor_get(v___x_1115_, 3);
v_traceState_1119_ = lean_ctor_get(v___x_1115_, 4);
v_cache_1120_ = lean_ctor_get(v___x_1115_, 5);
v_messages_1121_ = lean_ctor_get(v___x_1115_, 6);
v_infoState_1122_ = lean_ctor_get(v___x_1115_, 7);
v_snapshotTasks_1123_ = lean_ctor_get(v___x_1115_, 8);
v_newDecls_1124_ = lean_ctor_get(v___x_1115_, 9);
v_isSharedCheck_1139_ = !lean_is_exclusive(v___x_1115_);
if (v_isSharedCheck_1139_ == 0)
{
lean_object* v_unused_1140_; 
v_unused_1140_ = lean_ctor_get(v___x_1115_, 2);
lean_dec(v_unused_1140_);
v___x_1126_ = v___x_1115_;
v_isShared_1127_ = v_isSharedCheck_1139_;
goto v_resetjp_1125_;
}
else
{
lean_inc(v_newDecls_1124_);
lean_inc(v_snapshotTasks_1123_);
lean_inc(v_infoState_1122_);
lean_inc(v_messages_1121_);
lean_inc(v_cache_1120_);
lean_inc(v_traceState_1119_);
lean_inc(v_auxDeclNGen_1118_);
lean_inc(v_nextMacroScope_1117_);
lean_inc(v_env_1116_);
lean_dec(v___x_1115_);
v___x_1126_ = lean_box(0);
v_isShared_1127_ = v_isSharedCheck_1139_;
goto v_resetjp_1125_;
}
v_resetjp_1125_:
{
lean_object* v_r_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1132_; 
lean_inc(v_idx_1111_);
lean_inc(v_namePrefix_1110_);
v_r_1128_ = l_Lean_Name_num___override(v_namePrefix_1110_, v_idx_1111_);
v___x_1129_ = lean_unsigned_to_nat(1u);
v___x_1130_ = lean_nat_add(v_idx_1111_, v___x_1129_);
lean_dec(v_idx_1111_);
if (v_isShared_1114_ == 0)
{
lean_ctor_set(v___x_1113_, 1, v___x_1130_);
v___x_1132_ = v___x_1113_;
goto v_reusejp_1131_;
}
else
{
lean_object* v_reuseFailAlloc_1138_; 
v_reuseFailAlloc_1138_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1138_, 0, v_namePrefix_1110_);
lean_ctor_set(v_reuseFailAlloc_1138_, 1, v___x_1130_);
v___x_1132_ = v_reuseFailAlloc_1138_;
goto v_reusejp_1131_;
}
v_reusejp_1131_:
{
lean_object* v___x_1134_; 
if (v_isShared_1127_ == 0)
{
lean_ctor_set(v___x_1126_, 2, v___x_1132_);
v___x_1134_ = v___x_1126_;
goto v_reusejp_1133_;
}
else
{
lean_object* v_reuseFailAlloc_1137_; 
v_reuseFailAlloc_1137_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1137_, 0, v_env_1116_);
lean_ctor_set(v_reuseFailAlloc_1137_, 1, v_nextMacroScope_1117_);
lean_ctor_set(v_reuseFailAlloc_1137_, 2, v___x_1132_);
lean_ctor_set(v_reuseFailAlloc_1137_, 3, v_auxDeclNGen_1118_);
lean_ctor_set(v_reuseFailAlloc_1137_, 4, v_traceState_1119_);
lean_ctor_set(v_reuseFailAlloc_1137_, 5, v_cache_1120_);
lean_ctor_set(v_reuseFailAlloc_1137_, 6, v_messages_1121_);
lean_ctor_set(v_reuseFailAlloc_1137_, 7, v_infoState_1122_);
lean_ctor_set(v_reuseFailAlloc_1137_, 8, v_snapshotTasks_1123_);
lean_ctor_set(v_reuseFailAlloc_1137_, 9, v_newDecls_1124_);
v___x_1134_ = v_reuseFailAlloc_1137_;
goto v_reusejp_1133_;
}
v_reusejp_1133_:
{
lean_object* v___x_1135_; lean_object* v___x_1136_; 
v___x_1135_ = lean_st_ref_set(v___y_1106_, v___x_1134_);
v___x_1136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1136_, 0, v_r_1128_);
return v___x_1136_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Closure_collectExprAux_spec__3_spec__7___redArg___boxed(lean_object* v___y_1142_, lean_object* v___y_1143_){
_start:
{
lean_object* v_res_1144_; 
v_res_1144_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Closure_collectExprAux_spec__3_spec__7___redArg(v___y_1142_);
lean_dec(v___y_1142_);
return v_res_1144_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00Lean_Meta_Closure_collectExprAux_spec__3(uint8_t v___y_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_){
_start:
{
lean_object* v___x_1152_; lean_object* v_a_1153_; lean_object* v___x_1155_; uint8_t v_isShared_1156_; uint8_t v_isSharedCheck_1160_; 
v___x_1152_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Closure_collectExprAux_spec__3_spec__7___redArg(v___y_1150_);
v_a_1153_ = lean_ctor_get(v___x_1152_, 0);
v_isSharedCheck_1160_ = !lean_is_exclusive(v___x_1152_);
if (v_isSharedCheck_1160_ == 0)
{
v___x_1155_ = v___x_1152_;
v_isShared_1156_ = v_isSharedCheck_1160_;
goto v_resetjp_1154_;
}
else
{
lean_inc(v_a_1153_);
lean_dec(v___x_1152_);
v___x_1155_ = lean_box(0);
v_isShared_1156_ = v_isSharedCheck_1160_;
goto v_resetjp_1154_;
}
v_resetjp_1154_:
{
lean_object* v___x_1158_; 
if (v_isShared_1156_ == 0)
{
v___x_1158_ = v___x_1155_;
goto v_reusejp_1157_;
}
else
{
lean_object* v_reuseFailAlloc_1159_; 
v_reuseFailAlloc_1159_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1159_, 0, v_a_1153_);
v___x_1158_ = v_reuseFailAlloc_1159_;
goto v_reusejp_1157_;
}
v_reusejp_1157_:
{
return v___x_1158_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00Lean_Meta_Closure_collectExprAux_spec__3___boxed(lean_object* v___y_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_){
_start:
{
uint8_t v___y_18159__boxed_1168_; lean_object* v_res_1169_; 
v___y_18159__boxed_1168_ = lean_unbox(v___y_1161_);
v_res_1169_ = l_Lean_mkFreshFVarId___at___00Lean_Meta_Closure_collectExprAux_spec__3(v___y_18159__boxed_1168_, v___y_1162_, v___y_1163_, v___y_1164_, v___y_1165_, v___y_1166_);
lean_dec(v___y_1166_);
lean_dec_ref(v___y_1165_);
lean_dec(v___y_1164_);
lean_dec_ref(v___y_1163_);
lean_dec(v___y_1162_);
return v_res_1169_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectExprAux___lam__1(lean_object* v_e_1170_, lean_object* v_args_1171_, lean_object* v_x_1172_, uint8_t v___y_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_){
_start:
{
lean_object* v___x_1180_; uint8_t v___x_1181_; uint8_t v___x_1182_; uint8_t v___x_1183_; lean_object* v___x_1184_; 
v___x_1180_ = l_Lean_mkAppN(v_e_1170_, v_args_1171_);
v___x_1181_ = 0;
v___x_1182_ = 1;
v___x_1183_ = 1;
v___x_1184_ = l_Lean_Meta_mkLambdaFVars(v_args_1171_, v___x_1180_, v___x_1181_, v___x_1182_, v___x_1181_, v___x_1182_, v___x_1183_, v___y_1175_, v___y_1176_, v___y_1177_, v___y_1178_);
return v___x_1184_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectExprAux___lam__1___boxed(lean_object* v_e_1185_, lean_object* v_args_1186_, lean_object* v_x_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_){
_start:
{
uint8_t v___y_18200__boxed_1195_; lean_object* v_res_1196_; 
v___y_18200__boxed_1195_ = lean_unbox(v___y_1188_);
v_res_1196_ = l_Lean_Meta_Closure_collectExprAux___lam__1(v_e_1185_, v_args_1186_, v_x_1187_, v___y_18200__boxed_1195_, v___y_1189_, v___y_1190_, v___y_1191_, v___y_1192_, v___y_1193_);
lean_dec(v___y_1193_);
lean_dec_ref(v___y_1192_);
lean_dec(v___y_1191_);
lean_dec_ref(v___y_1190_);
lean_dec(v___y_1189_);
lean_dec_ref(v_x_1187_);
lean_dec_ref(v_args_1186_);
return v_res_1196_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__3_spec__6_spec__10___redArg(lean_object* v_x_1197_, lean_object* v_x_1198_){
_start:
{
if (lean_obj_tag(v_x_1198_) == 0)
{
return v_x_1197_;
}
else
{
lean_object* v_key_1199_; lean_object* v_value_1200_; lean_object* v_tail_1201_; lean_object* v___x_1203_; uint8_t v_isShared_1204_; uint8_t v_isSharedCheck_1224_; 
v_key_1199_ = lean_ctor_get(v_x_1198_, 0);
v_value_1200_ = lean_ctor_get(v_x_1198_, 1);
v_tail_1201_ = lean_ctor_get(v_x_1198_, 2);
v_isSharedCheck_1224_ = !lean_is_exclusive(v_x_1198_);
if (v_isSharedCheck_1224_ == 0)
{
v___x_1203_ = v_x_1198_;
v_isShared_1204_ = v_isSharedCheck_1224_;
goto v_resetjp_1202_;
}
else
{
lean_inc(v_tail_1201_);
lean_inc(v_value_1200_);
lean_inc(v_key_1199_);
lean_dec(v_x_1198_);
v___x_1203_ = lean_box(0);
v_isShared_1204_ = v_isSharedCheck_1224_;
goto v_resetjp_1202_;
}
v_resetjp_1202_:
{
lean_object* v___x_1205_; uint64_t v___x_1206_; uint64_t v___x_1207_; uint64_t v___x_1208_; uint64_t v_fold_1209_; uint64_t v___x_1210_; uint64_t v___x_1211_; uint64_t v___x_1212_; size_t v___x_1213_; size_t v___x_1214_; size_t v___x_1215_; size_t v___x_1216_; size_t v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1220_; 
v___x_1205_ = lean_array_get_size(v_x_1197_);
v___x_1206_ = l_Lean_ExprStructEq_hash(v_key_1199_);
v___x_1207_ = 32ULL;
v___x_1208_ = lean_uint64_shift_right(v___x_1206_, v___x_1207_);
v_fold_1209_ = lean_uint64_xor(v___x_1206_, v___x_1208_);
v___x_1210_ = 16ULL;
v___x_1211_ = lean_uint64_shift_right(v_fold_1209_, v___x_1210_);
v___x_1212_ = lean_uint64_xor(v_fold_1209_, v___x_1211_);
v___x_1213_ = lean_uint64_to_usize(v___x_1212_);
v___x_1214_ = lean_usize_of_nat(v___x_1205_);
v___x_1215_ = ((size_t)1ULL);
v___x_1216_ = lean_usize_sub(v___x_1214_, v___x_1215_);
v___x_1217_ = lean_usize_land(v___x_1213_, v___x_1216_);
v___x_1218_ = lean_array_uget_borrowed(v_x_1197_, v___x_1217_);
lean_inc(v___x_1218_);
if (v_isShared_1204_ == 0)
{
lean_ctor_set(v___x_1203_, 2, v___x_1218_);
v___x_1220_ = v___x_1203_;
goto v_reusejp_1219_;
}
else
{
lean_object* v_reuseFailAlloc_1223_; 
v_reuseFailAlloc_1223_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1223_, 0, v_key_1199_);
lean_ctor_set(v_reuseFailAlloc_1223_, 1, v_value_1200_);
lean_ctor_set(v_reuseFailAlloc_1223_, 2, v___x_1218_);
v___x_1220_ = v_reuseFailAlloc_1223_;
goto v_reusejp_1219_;
}
v_reusejp_1219_:
{
lean_object* v___x_1221_; 
v___x_1221_ = lean_array_uset(v_x_1197_, v___x_1217_, v___x_1220_);
v_x_1197_ = v___x_1221_;
v_x_1198_ = v_tail_1201_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__3_spec__6___redArg(lean_object* v_i_1225_, lean_object* v_source_1226_, lean_object* v_target_1227_){
_start:
{
lean_object* v___x_1228_; uint8_t v___x_1229_; 
v___x_1228_ = lean_array_get_size(v_source_1226_);
v___x_1229_ = lean_nat_dec_lt(v_i_1225_, v___x_1228_);
if (v___x_1229_ == 0)
{
lean_dec_ref(v_source_1226_);
lean_dec(v_i_1225_);
return v_target_1227_;
}
else
{
lean_object* v_es_1230_; lean_object* v___x_1231_; lean_object* v_source_1232_; lean_object* v_target_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; 
v_es_1230_ = lean_array_fget(v_source_1226_, v_i_1225_);
v___x_1231_ = lean_box(0);
v_source_1232_ = lean_array_fset(v_source_1226_, v_i_1225_, v___x_1231_);
v_target_1233_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__3_spec__6_spec__10___redArg(v_target_1227_, v_es_1230_);
v___x_1234_ = lean_unsigned_to_nat(1u);
v___x_1235_ = lean_nat_add(v_i_1225_, v___x_1234_);
lean_dec(v_i_1225_);
v_i_1225_ = v___x_1235_;
v_source_1226_ = v_source_1232_;
v_target_1227_ = v_target_1233_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__3___redArg(lean_object* v_data_1237_){
_start:
{
lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v_nbuckets_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; 
v___x_1238_ = lean_array_get_size(v_data_1237_);
v___x_1239_ = lean_unsigned_to_nat(2u);
v_nbuckets_1240_ = lean_nat_mul(v___x_1238_, v___x_1239_);
v___x_1241_ = lean_unsigned_to_nat(0u);
v___x_1242_ = lean_box(0);
v___x_1243_ = lean_mk_array(v_nbuckets_1240_, v___x_1242_);
v___x_1244_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__3_spec__6___redArg(v___x_1241_, v_data_1237_, v___x_1243_);
return v___x_1244_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__4___redArg(lean_object* v_a_1245_, lean_object* v_b_1246_, lean_object* v_x_1247_){
_start:
{
if (lean_obj_tag(v_x_1247_) == 0)
{
lean_dec(v_b_1246_);
lean_dec_ref(v_a_1245_);
return v_x_1247_;
}
else
{
lean_object* v_key_1248_; lean_object* v_value_1249_; lean_object* v_tail_1250_; lean_object* v___x_1252_; uint8_t v_isShared_1253_; uint8_t v_isSharedCheck_1262_; 
v_key_1248_ = lean_ctor_get(v_x_1247_, 0);
v_value_1249_ = lean_ctor_get(v_x_1247_, 1);
v_tail_1250_ = lean_ctor_get(v_x_1247_, 2);
v_isSharedCheck_1262_ = !lean_is_exclusive(v_x_1247_);
if (v_isSharedCheck_1262_ == 0)
{
v___x_1252_ = v_x_1247_;
v_isShared_1253_ = v_isSharedCheck_1262_;
goto v_resetjp_1251_;
}
else
{
lean_inc(v_tail_1250_);
lean_inc(v_value_1249_);
lean_inc(v_key_1248_);
lean_dec(v_x_1247_);
v___x_1252_ = lean_box(0);
v_isShared_1253_ = v_isSharedCheck_1262_;
goto v_resetjp_1251_;
}
v_resetjp_1251_:
{
uint8_t v___x_1254_; 
v___x_1254_ = l_Lean_ExprStructEq_beq(v_key_1248_, v_a_1245_);
if (v___x_1254_ == 0)
{
lean_object* v___x_1255_; lean_object* v___x_1257_; 
v___x_1255_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__4___redArg(v_a_1245_, v_b_1246_, v_tail_1250_);
if (v_isShared_1253_ == 0)
{
lean_ctor_set(v___x_1252_, 2, v___x_1255_);
v___x_1257_ = v___x_1252_;
goto v_reusejp_1256_;
}
else
{
lean_object* v_reuseFailAlloc_1258_; 
v_reuseFailAlloc_1258_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1258_, 0, v_key_1248_);
lean_ctor_set(v_reuseFailAlloc_1258_, 1, v_value_1249_);
lean_ctor_set(v_reuseFailAlloc_1258_, 2, v___x_1255_);
v___x_1257_ = v_reuseFailAlloc_1258_;
goto v_reusejp_1256_;
}
v_reusejp_1256_:
{
return v___x_1257_;
}
}
else
{
lean_object* v___x_1260_; 
lean_dec(v_value_1249_);
lean_dec(v_key_1248_);
if (v_isShared_1253_ == 0)
{
lean_ctor_set(v___x_1252_, 1, v_b_1246_);
lean_ctor_set(v___x_1252_, 0, v_a_1245_);
v___x_1260_ = v___x_1252_;
goto v_reusejp_1259_;
}
else
{
lean_object* v_reuseFailAlloc_1261_; 
v_reuseFailAlloc_1261_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1261_, 0, v_a_1245_);
lean_ctor_set(v_reuseFailAlloc_1261_, 1, v_b_1246_);
lean_ctor_set(v_reuseFailAlloc_1261_, 2, v_tail_1250_);
v___x_1260_ = v_reuseFailAlloc_1261_;
goto v_reusejp_1259_;
}
v_reusejp_1259_:
{
return v___x_1260_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__2___redArg(lean_object* v_a_1263_, lean_object* v_x_1264_){
_start:
{
if (lean_obj_tag(v_x_1264_) == 0)
{
uint8_t v___x_1265_; 
v___x_1265_ = 0;
return v___x_1265_;
}
else
{
lean_object* v_key_1266_; lean_object* v_tail_1267_; uint8_t v___x_1268_; 
v_key_1266_ = lean_ctor_get(v_x_1264_, 0);
v_tail_1267_ = lean_ctor_get(v_x_1264_, 2);
v___x_1268_ = l_Lean_ExprStructEq_beq(v_key_1266_, v_a_1263_);
if (v___x_1268_ == 0)
{
v_x_1264_ = v_tail_1267_;
goto _start;
}
else
{
return v___x_1268_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__2___redArg___boxed(lean_object* v_a_1270_, lean_object* v_x_1271_){
_start:
{
uint8_t v_res_1272_; lean_object* v_r_1273_; 
v_res_1272_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__2___redArg(v_a_1270_, v_x_1271_);
lean_dec(v_x_1271_);
lean_dec_ref(v_a_1270_);
v_r_1273_ = lean_box(v_res_1272_);
return v_r_1273_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1___redArg(lean_object* v_m_1274_, lean_object* v_a_1275_, lean_object* v_b_1276_){
_start:
{
lean_object* v_size_1277_; lean_object* v_buckets_1278_; lean_object* v___x_1280_; uint8_t v_isShared_1281_; uint8_t v_isSharedCheck_1321_; 
v_size_1277_ = lean_ctor_get(v_m_1274_, 0);
v_buckets_1278_ = lean_ctor_get(v_m_1274_, 1);
v_isSharedCheck_1321_ = !lean_is_exclusive(v_m_1274_);
if (v_isSharedCheck_1321_ == 0)
{
v___x_1280_ = v_m_1274_;
v_isShared_1281_ = v_isSharedCheck_1321_;
goto v_resetjp_1279_;
}
else
{
lean_inc(v_buckets_1278_);
lean_inc(v_size_1277_);
lean_dec(v_m_1274_);
v___x_1280_ = lean_box(0);
v_isShared_1281_ = v_isSharedCheck_1321_;
goto v_resetjp_1279_;
}
v_resetjp_1279_:
{
lean_object* v___x_1282_; uint64_t v___x_1283_; uint64_t v___x_1284_; uint64_t v___x_1285_; uint64_t v_fold_1286_; uint64_t v___x_1287_; uint64_t v___x_1288_; uint64_t v___x_1289_; size_t v___x_1290_; size_t v___x_1291_; size_t v___x_1292_; size_t v___x_1293_; size_t v___x_1294_; lean_object* v_bkt_1295_; uint8_t v___x_1296_; 
v___x_1282_ = lean_array_get_size(v_buckets_1278_);
v___x_1283_ = l_Lean_ExprStructEq_hash(v_a_1275_);
v___x_1284_ = 32ULL;
v___x_1285_ = lean_uint64_shift_right(v___x_1283_, v___x_1284_);
v_fold_1286_ = lean_uint64_xor(v___x_1283_, v___x_1285_);
v___x_1287_ = 16ULL;
v___x_1288_ = lean_uint64_shift_right(v_fold_1286_, v___x_1287_);
v___x_1289_ = lean_uint64_xor(v_fold_1286_, v___x_1288_);
v___x_1290_ = lean_uint64_to_usize(v___x_1289_);
v___x_1291_ = lean_usize_of_nat(v___x_1282_);
v___x_1292_ = ((size_t)1ULL);
v___x_1293_ = lean_usize_sub(v___x_1291_, v___x_1292_);
v___x_1294_ = lean_usize_land(v___x_1290_, v___x_1293_);
v_bkt_1295_ = lean_array_uget_borrowed(v_buckets_1278_, v___x_1294_);
v___x_1296_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__2___redArg(v_a_1275_, v_bkt_1295_);
if (v___x_1296_ == 0)
{
lean_object* v___x_1297_; lean_object* v_size_x27_1298_; lean_object* v___x_1299_; lean_object* v_buckets_x27_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; uint8_t v___x_1306_; 
v___x_1297_ = lean_unsigned_to_nat(1u);
v_size_x27_1298_ = lean_nat_add(v_size_1277_, v___x_1297_);
lean_dec(v_size_1277_);
lean_inc(v_bkt_1295_);
v___x_1299_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1299_, 0, v_a_1275_);
lean_ctor_set(v___x_1299_, 1, v_b_1276_);
lean_ctor_set(v___x_1299_, 2, v_bkt_1295_);
v_buckets_x27_1300_ = lean_array_uset(v_buckets_1278_, v___x_1294_, v___x_1299_);
v___x_1301_ = lean_unsigned_to_nat(4u);
v___x_1302_ = lean_nat_mul(v_size_x27_1298_, v___x_1301_);
v___x_1303_ = lean_unsigned_to_nat(3u);
v___x_1304_ = lean_nat_div(v___x_1302_, v___x_1303_);
lean_dec(v___x_1302_);
v___x_1305_ = lean_array_get_size(v_buckets_x27_1300_);
v___x_1306_ = lean_nat_dec_le(v___x_1304_, v___x_1305_);
lean_dec(v___x_1304_);
if (v___x_1306_ == 0)
{
lean_object* v_val_1307_; lean_object* v___x_1309_; 
v_val_1307_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__3___redArg(v_buckets_x27_1300_);
if (v_isShared_1281_ == 0)
{
lean_ctor_set(v___x_1280_, 1, v_val_1307_);
lean_ctor_set(v___x_1280_, 0, v_size_x27_1298_);
v___x_1309_ = v___x_1280_;
goto v_reusejp_1308_;
}
else
{
lean_object* v_reuseFailAlloc_1310_; 
v_reuseFailAlloc_1310_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1310_, 0, v_size_x27_1298_);
lean_ctor_set(v_reuseFailAlloc_1310_, 1, v_val_1307_);
v___x_1309_ = v_reuseFailAlloc_1310_;
goto v_reusejp_1308_;
}
v_reusejp_1308_:
{
return v___x_1309_;
}
}
else
{
lean_object* v___x_1312_; 
if (v_isShared_1281_ == 0)
{
lean_ctor_set(v___x_1280_, 1, v_buckets_x27_1300_);
lean_ctor_set(v___x_1280_, 0, v_size_x27_1298_);
v___x_1312_ = v___x_1280_;
goto v_reusejp_1311_;
}
else
{
lean_object* v_reuseFailAlloc_1313_; 
v_reuseFailAlloc_1313_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1313_, 0, v_size_x27_1298_);
lean_ctor_set(v_reuseFailAlloc_1313_, 1, v_buckets_x27_1300_);
v___x_1312_ = v_reuseFailAlloc_1313_;
goto v_reusejp_1311_;
}
v_reusejp_1311_:
{
return v___x_1312_;
}
}
}
else
{
lean_object* v___x_1314_; lean_object* v_buckets_x27_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1319_; 
lean_inc(v_bkt_1295_);
v___x_1314_ = lean_box(0);
v_buckets_x27_1315_ = lean_array_uset(v_buckets_1278_, v___x_1294_, v___x_1314_);
v___x_1316_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__4___redArg(v_a_1275_, v_b_1276_, v_bkt_1295_);
v___x_1317_ = lean_array_uset(v_buckets_x27_1315_, v___x_1294_, v___x_1316_);
if (v_isShared_1281_ == 0)
{
lean_ctor_set(v___x_1280_, 1, v___x_1317_);
v___x_1319_ = v___x_1280_;
goto v_reusejp_1318_;
}
else
{
lean_object* v_reuseFailAlloc_1320_; 
v_reuseFailAlloc_1320_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1320_, 0, v_size_1277_);
lean_ctor_set(v_reuseFailAlloc_1320_, 1, v___x_1317_);
v___x_1319_ = v_reuseFailAlloc_1320_;
goto v_reusejp_1318_;
}
v_reusejp_1318_:
{
return v___x_1319_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectExprAux(lean_object* v_e_1322_, uint8_t v_a_1323_, lean_object* v_a_1324_, lean_object* v_a_1325_, lean_object* v_a_1326_, lean_object* v_a_1327_, lean_object* v_a_1328_){
_start:
{
switch(lean_obj_tag(v_e_1322_))
{
case 11:
{
lean_object* v_typeName_1330_; lean_object* v_idx_1331_; lean_object* v_struct_1332_; lean_object* v___x_1333_; 
v_typeName_1330_ = lean_ctor_get(v_e_1322_, 0);
v_idx_1331_ = lean_ctor_get(v_e_1322_, 1);
v_struct_1332_ = lean_ctor_get(v_e_1322_, 2);
lean_inc_ref(v_struct_1332_);
v___x_1333_ = l_Lean_Meta_Closure_collectExprAux___lam__0(v_struct_1332_, v_a_1323_, v_a_1324_, v_a_1325_, v_a_1326_, v_a_1327_, v_a_1328_);
if (lean_obj_tag(v___x_1333_) == 0)
{
lean_object* v_a_1334_; lean_object* v___x_1336_; uint8_t v_isShared_1337_; uint8_t v_isSharedCheck_1348_; 
v_a_1334_ = lean_ctor_get(v___x_1333_, 0);
v_isSharedCheck_1348_ = !lean_is_exclusive(v___x_1333_);
if (v_isSharedCheck_1348_ == 0)
{
v___x_1336_ = v___x_1333_;
v_isShared_1337_ = v_isSharedCheck_1348_;
goto v_resetjp_1335_;
}
else
{
lean_inc(v_a_1334_);
lean_dec(v___x_1333_);
v___x_1336_ = lean_box(0);
v_isShared_1337_ = v_isSharedCheck_1348_;
goto v_resetjp_1335_;
}
v_resetjp_1335_:
{
size_t v___x_1338_; size_t v___x_1339_; uint8_t v___x_1340_; 
v___x_1338_ = lean_ptr_addr(v_struct_1332_);
v___x_1339_ = lean_ptr_addr(v_a_1334_);
v___x_1340_ = lean_usize_dec_eq(v___x_1338_, v___x_1339_);
if (v___x_1340_ == 0)
{
lean_object* v___x_1341_; lean_object* v___x_1343_; 
lean_inc(v_idx_1331_);
lean_inc(v_typeName_1330_);
lean_dec_ref(v_e_1322_);
v___x_1341_ = l_Lean_Expr_proj___override(v_typeName_1330_, v_idx_1331_, v_a_1334_);
if (v_isShared_1337_ == 0)
{
lean_ctor_set(v___x_1336_, 0, v___x_1341_);
v___x_1343_ = v___x_1336_;
goto v_reusejp_1342_;
}
else
{
lean_object* v_reuseFailAlloc_1344_; 
v_reuseFailAlloc_1344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1344_, 0, v___x_1341_);
v___x_1343_ = v_reuseFailAlloc_1344_;
goto v_reusejp_1342_;
}
v_reusejp_1342_:
{
return v___x_1343_;
}
}
else
{
lean_object* v___x_1346_; 
lean_dec(v_a_1334_);
if (v_isShared_1337_ == 0)
{
lean_ctor_set(v___x_1336_, 0, v_e_1322_);
v___x_1346_ = v___x_1336_;
goto v_reusejp_1345_;
}
else
{
lean_object* v_reuseFailAlloc_1347_; 
v_reuseFailAlloc_1347_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1347_, 0, v_e_1322_);
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
else
{
lean_dec_ref(v_e_1322_);
return v___x_1333_;
}
}
case 7:
{
lean_object* v_binderName_1349_; lean_object* v_binderType_1350_; lean_object* v_body_1351_; uint8_t v_binderInfo_1352_; lean_object* v___x_1353_; 
v_binderName_1349_ = lean_ctor_get(v_e_1322_, 0);
v_binderType_1350_ = lean_ctor_get(v_e_1322_, 1);
v_body_1351_ = lean_ctor_get(v_e_1322_, 2);
v_binderInfo_1352_ = lean_ctor_get_uint8(v_e_1322_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_1350_);
v___x_1353_ = l_Lean_Meta_Closure_collectExprAux___lam__0(v_binderType_1350_, v_a_1323_, v_a_1324_, v_a_1325_, v_a_1326_, v_a_1327_, v_a_1328_);
if (lean_obj_tag(v___x_1353_) == 0)
{
lean_object* v_a_1354_; lean_object* v___x_1355_; 
v_a_1354_ = lean_ctor_get(v___x_1353_, 0);
lean_inc(v_a_1354_);
lean_dec_ref(v___x_1353_);
lean_inc_ref(v_body_1351_);
v___x_1355_ = l_Lean_Meta_Closure_collectExprAux___lam__0(v_body_1351_, v_a_1323_, v_a_1324_, v_a_1325_, v_a_1326_, v_a_1327_, v_a_1328_);
if (lean_obj_tag(v___x_1355_) == 0)
{
lean_object* v_a_1356_; lean_object* v___x_1358_; uint8_t v_isShared_1359_; uint8_t v_isSharedCheck_1380_; 
v_a_1356_ = lean_ctor_get(v___x_1355_, 0);
v_isSharedCheck_1380_ = !lean_is_exclusive(v___x_1355_);
if (v_isSharedCheck_1380_ == 0)
{
v___x_1358_ = v___x_1355_;
v_isShared_1359_ = v_isSharedCheck_1380_;
goto v_resetjp_1357_;
}
else
{
lean_inc(v_a_1356_);
lean_dec(v___x_1355_);
v___x_1358_ = lean_box(0);
v_isShared_1359_ = v_isSharedCheck_1380_;
goto v_resetjp_1357_;
}
v_resetjp_1357_:
{
uint8_t v___y_1361_; size_t v___x_1374_; size_t v___x_1375_; uint8_t v___x_1376_; 
v___x_1374_ = lean_ptr_addr(v_binderType_1350_);
v___x_1375_ = lean_ptr_addr(v_a_1354_);
v___x_1376_ = lean_usize_dec_eq(v___x_1374_, v___x_1375_);
if (v___x_1376_ == 0)
{
v___y_1361_ = v___x_1376_;
goto v___jp_1360_;
}
else
{
size_t v___x_1377_; size_t v___x_1378_; uint8_t v___x_1379_; 
v___x_1377_ = lean_ptr_addr(v_body_1351_);
v___x_1378_ = lean_ptr_addr(v_a_1356_);
v___x_1379_ = lean_usize_dec_eq(v___x_1377_, v___x_1378_);
v___y_1361_ = v___x_1379_;
goto v___jp_1360_;
}
v___jp_1360_:
{
if (v___y_1361_ == 0)
{
lean_object* v___x_1362_; lean_object* v___x_1364_; 
lean_inc(v_binderName_1349_);
lean_dec_ref(v_e_1322_);
v___x_1362_ = l_Lean_Expr_forallE___override(v_binderName_1349_, v_a_1354_, v_a_1356_, v_binderInfo_1352_);
if (v_isShared_1359_ == 0)
{
lean_ctor_set(v___x_1358_, 0, v___x_1362_);
v___x_1364_ = v___x_1358_;
goto v_reusejp_1363_;
}
else
{
lean_object* v_reuseFailAlloc_1365_; 
v_reuseFailAlloc_1365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1365_, 0, v___x_1362_);
v___x_1364_ = v_reuseFailAlloc_1365_;
goto v_reusejp_1363_;
}
v_reusejp_1363_:
{
return v___x_1364_;
}
}
else
{
uint8_t v___x_1366_; 
v___x_1366_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_1352_, v_binderInfo_1352_);
if (v___x_1366_ == 0)
{
lean_object* v___x_1367_; lean_object* v___x_1369_; 
lean_inc(v_binderName_1349_);
lean_dec_ref(v_e_1322_);
v___x_1367_ = l_Lean_Expr_forallE___override(v_binderName_1349_, v_a_1354_, v_a_1356_, v_binderInfo_1352_);
if (v_isShared_1359_ == 0)
{
lean_ctor_set(v___x_1358_, 0, v___x_1367_);
v___x_1369_ = v___x_1358_;
goto v_reusejp_1368_;
}
else
{
lean_object* v_reuseFailAlloc_1370_; 
v_reuseFailAlloc_1370_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1370_, 0, v___x_1367_);
v___x_1369_ = v_reuseFailAlloc_1370_;
goto v_reusejp_1368_;
}
v_reusejp_1368_:
{
return v___x_1369_;
}
}
else
{
lean_object* v___x_1372_; 
lean_dec(v_a_1356_);
lean_dec(v_a_1354_);
if (v_isShared_1359_ == 0)
{
lean_ctor_set(v___x_1358_, 0, v_e_1322_);
v___x_1372_ = v___x_1358_;
goto v_reusejp_1371_;
}
else
{
lean_object* v_reuseFailAlloc_1373_; 
v_reuseFailAlloc_1373_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1373_, 0, v_e_1322_);
v___x_1372_ = v_reuseFailAlloc_1373_;
goto v_reusejp_1371_;
}
v_reusejp_1371_:
{
return v___x_1372_;
}
}
}
}
}
}
else
{
lean_dec(v_a_1354_);
lean_dec_ref(v_e_1322_);
return v___x_1355_;
}
}
else
{
lean_dec_ref(v_e_1322_);
return v___x_1353_;
}
}
case 6:
{
lean_object* v_binderName_1381_; lean_object* v_binderType_1382_; lean_object* v_body_1383_; uint8_t v_binderInfo_1384_; lean_object* v___x_1385_; 
v_binderName_1381_ = lean_ctor_get(v_e_1322_, 0);
v_binderType_1382_ = lean_ctor_get(v_e_1322_, 1);
v_body_1383_ = lean_ctor_get(v_e_1322_, 2);
v_binderInfo_1384_ = lean_ctor_get_uint8(v_e_1322_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_1382_);
v___x_1385_ = l_Lean_Meta_Closure_collectExprAux___lam__0(v_binderType_1382_, v_a_1323_, v_a_1324_, v_a_1325_, v_a_1326_, v_a_1327_, v_a_1328_);
if (lean_obj_tag(v___x_1385_) == 0)
{
lean_object* v_a_1386_; lean_object* v___x_1387_; 
v_a_1386_ = lean_ctor_get(v___x_1385_, 0);
lean_inc(v_a_1386_);
lean_dec_ref(v___x_1385_);
lean_inc_ref(v_body_1383_);
v___x_1387_ = l_Lean_Meta_Closure_collectExprAux___lam__0(v_body_1383_, v_a_1323_, v_a_1324_, v_a_1325_, v_a_1326_, v_a_1327_, v_a_1328_);
if (lean_obj_tag(v___x_1387_) == 0)
{
lean_object* v_a_1388_; lean_object* v___x_1390_; uint8_t v_isShared_1391_; uint8_t v_isSharedCheck_1412_; 
v_a_1388_ = lean_ctor_get(v___x_1387_, 0);
v_isSharedCheck_1412_ = !lean_is_exclusive(v___x_1387_);
if (v_isSharedCheck_1412_ == 0)
{
v___x_1390_ = v___x_1387_;
v_isShared_1391_ = v_isSharedCheck_1412_;
goto v_resetjp_1389_;
}
else
{
lean_inc(v_a_1388_);
lean_dec(v___x_1387_);
v___x_1390_ = lean_box(0);
v_isShared_1391_ = v_isSharedCheck_1412_;
goto v_resetjp_1389_;
}
v_resetjp_1389_:
{
uint8_t v___y_1393_; size_t v___x_1406_; size_t v___x_1407_; uint8_t v___x_1408_; 
v___x_1406_ = lean_ptr_addr(v_binderType_1382_);
v___x_1407_ = lean_ptr_addr(v_a_1386_);
v___x_1408_ = lean_usize_dec_eq(v___x_1406_, v___x_1407_);
if (v___x_1408_ == 0)
{
v___y_1393_ = v___x_1408_;
goto v___jp_1392_;
}
else
{
size_t v___x_1409_; size_t v___x_1410_; uint8_t v___x_1411_; 
v___x_1409_ = lean_ptr_addr(v_body_1383_);
v___x_1410_ = lean_ptr_addr(v_a_1388_);
v___x_1411_ = lean_usize_dec_eq(v___x_1409_, v___x_1410_);
v___y_1393_ = v___x_1411_;
goto v___jp_1392_;
}
v___jp_1392_:
{
if (v___y_1393_ == 0)
{
lean_object* v___x_1394_; lean_object* v___x_1396_; 
lean_inc(v_binderName_1381_);
lean_dec_ref(v_e_1322_);
v___x_1394_ = l_Lean_Expr_lam___override(v_binderName_1381_, v_a_1386_, v_a_1388_, v_binderInfo_1384_);
if (v_isShared_1391_ == 0)
{
lean_ctor_set(v___x_1390_, 0, v___x_1394_);
v___x_1396_ = v___x_1390_;
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
uint8_t v___x_1398_; 
v___x_1398_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_1384_, v_binderInfo_1384_);
if (v___x_1398_ == 0)
{
lean_object* v___x_1399_; lean_object* v___x_1401_; 
lean_inc(v_binderName_1381_);
lean_dec_ref(v_e_1322_);
v___x_1399_ = l_Lean_Expr_lam___override(v_binderName_1381_, v_a_1386_, v_a_1388_, v_binderInfo_1384_);
if (v_isShared_1391_ == 0)
{
lean_ctor_set(v___x_1390_, 0, v___x_1399_);
v___x_1401_ = v___x_1390_;
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
lean_object* v___x_1404_; 
lean_dec(v_a_1388_);
lean_dec(v_a_1386_);
if (v_isShared_1391_ == 0)
{
lean_ctor_set(v___x_1390_, 0, v_e_1322_);
v___x_1404_ = v___x_1390_;
goto v_reusejp_1403_;
}
else
{
lean_object* v_reuseFailAlloc_1405_; 
v_reuseFailAlloc_1405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1405_, 0, v_e_1322_);
v___x_1404_ = v_reuseFailAlloc_1405_;
goto v_reusejp_1403_;
}
v_reusejp_1403_:
{
return v___x_1404_;
}
}
}
}
}
}
else
{
lean_dec(v_a_1386_);
lean_dec_ref(v_e_1322_);
return v___x_1387_;
}
}
else
{
lean_dec_ref(v_e_1322_);
return v___x_1385_;
}
}
case 8:
{
lean_object* v_declName_1413_; lean_object* v_type_1414_; lean_object* v_value_1415_; lean_object* v_body_1416_; uint8_t v_nondep_1417_; lean_object* v___x_1418_; 
v_declName_1413_ = lean_ctor_get(v_e_1322_, 0);
v_type_1414_ = lean_ctor_get(v_e_1322_, 1);
v_value_1415_ = lean_ctor_get(v_e_1322_, 2);
v_body_1416_ = lean_ctor_get(v_e_1322_, 3);
v_nondep_1417_ = lean_ctor_get_uint8(v_e_1322_, sizeof(void*)*4 + 8);
lean_inc_ref(v_type_1414_);
v___x_1418_ = l_Lean_Meta_Closure_collectExprAux___lam__0(v_type_1414_, v_a_1323_, v_a_1324_, v_a_1325_, v_a_1326_, v_a_1327_, v_a_1328_);
if (lean_obj_tag(v___x_1418_) == 0)
{
lean_object* v_a_1419_; lean_object* v___x_1420_; 
v_a_1419_ = lean_ctor_get(v___x_1418_, 0);
lean_inc(v_a_1419_);
lean_dec_ref(v___x_1418_);
lean_inc_ref(v_value_1415_);
v___x_1420_ = l_Lean_Meta_Closure_collectExprAux___lam__0(v_value_1415_, v_a_1323_, v_a_1324_, v_a_1325_, v_a_1326_, v_a_1327_, v_a_1328_);
if (lean_obj_tag(v___x_1420_) == 0)
{
lean_object* v_a_1421_; lean_object* v___x_1422_; 
v_a_1421_ = lean_ctor_get(v___x_1420_, 0);
lean_inc(v_a_1421_);
lean_dec_ref(v___x_1420_);
lean_inc_ref(v_body_1416_);
v___x_1422_ = l_Lean_Meta_Closure_collectExprAux___lam__0(v_body_1416_, v_a_1323_, v_a_1324_, v_a_1325_, v_a_1326_, v_a_1327_, v_a_1328_);
if (lean_obj_tag(v___x_1422_) == 0)
{
lean_object* v_a_1423_; lean_object* v___x_1425_; uint8_t v_isShared_1426_; uint8_t v_isSharedCheck_1449_; 
v_a_1423_ = lean_ctor_get(v___x_1422_, 0);
v_isSharedCheck_1449_ = !lean_is_exclusive(v___x_1422_);
if (v_isSharedCheck_1449_ == 0)
{
v___x_1425_ = v___x_1422_;
v_isShared_1426_ = v_isSharedCheck_1449_;
goto v_resetjp_1424_;
}
else
{
lean_inc(v_a_1423_);
lean_dec(v___x_1422_);
v___x_1425_ = lean_box(0);
v_isShared_1426_ = v_isSharedCheck_1449_;
goto v_resetjp_1424_;
}
v_resetjp_1424_:
{
uint8_t v___y_1428_; size_t v___x_1443_; size_t v___x_1444_; uint8_t v___x_1445_; 
v___x_1443_ = lean_ptr_addr(v_type_1414_);
v___x_1444_ = lean_ptr_addr(v_a_1419_);
v___x_1445_ = lean_usize_dec_eq(v___x_1443_, v___x_1444_);
if (v___x_1445_ == 0)
{
v___y_1428_ = v___x_1445_;
goto v___jp_1427_;
}
else
{
size_t v___x_1446_; size_t v___x_1447_; uint8_t v___x_1448_; 
v___x_1446_ = lean_ptr_addr(v_value_1415_);
v___x_1447_ = lean_ptr_addr(v_a_1421_);
v___x_1448_ = lean_usize_dec_eq(v___x_1446_, v___x_1447_);
v___y_1428_ = v___x_1448_;
goto v___jp_1427_;
}
v___jp_1427_:
{
if (v___y_1428_ == 0)
{
lean_object* v___x_1429_; lean_object* v___x_1431_; 
lean_inc(v_declName_1413_);
lean_dec_ref(v_e_1322_);
v___x_1429_ = l_Lean_Expr_letE___override(v_declName_1413_, v_a_1419_, v_a_1421_, v_a_1423_, v_nondep_1417_);
if (v_isShared_1426_ == 0)
{
lean_ctor_set(v___x_1425_, 0, v___x_1429_);
v___x_1431_ = v___x_1425_;
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
v___x_1433_ = lean_ptr_addr(v_body_1416_);
v___x_1434_ = lean_ptr_addr(v_a_1423_);
v___x_1435_ = lean_usize_dec_eq(v___x_1433_, v___x_1434_);
if (v___x_1435_ == 0)
{
lean_object* v___x_1436_; lean_object* v___x_1438_; 
lean_inc(v_declName_1413_);
lean_dec_ref(v_e_1322_);
v___x_1436_ = l_Lean_Expr_letE___override(v_declName_1413_, v_a_1419_, v_a_1421_, v_a_1423_, v_nondep_1417_);
if (v_isShared_1426_ == 0)
{
lean_ctor_set(v___x_1425_, 0, v___x_1436_);
v___x_1438_ = v___x_1425_;
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
lean_object* v___x_1441_; 
lean_dec(v_a_1423_);
lean_dec(v_a_1421_);
lean_dec(v_a_1419_);
if (v_isShared_1426_ == 0)
{
lean_ctor_set(v___x_1425_, 0, v_e_1322_);
v___x_1441_ = v___x_1425_;
goto v_reusejp_1440_;
}
else
{
lean_object* v_reuseFailAlloc_1442_; 
v_reuseFailAlloc_1442_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1442_, 0, v_e_1322_);
v___x_1441_ = v_reuseFailAlloc_1442_;
goto v_reusejp_1440_;
}
v_reusejp_1440_:
{
return v___x_1441_;
}
}
}
}
}
}
else
{
lean_dec(v_a_1421_);
lean_dec(v_a_1419_);
lean_dec_ref(v_e_1322_);
return v___x_1422_;
}
}
else
{
lean_dec(v_a_1419_);
lean_dec_ref(v_e_1322_);
return v___x_1420_;
}
}
else
{
lean_dec_ref(v_e_1322_);
return v___x_1418_;
}
}
case 5:
{
lean_object* v_fn_1450_; lean_object* v_arg_1451_; lean_object* v___x_1452_; 
v_fn_1450_ = lean_ctor_get(v_e_1322_, 0);
v_arg_1451_ = lean_ctor_get(v_e_1322_, 1);
lean_inc_ref(v_fn_1450_);
v___x_1452_ = l_Lean_Meta_Closure_collectExprAux___lam__0(v_fn_1450_, v_a_1323_, v_a_1324_, v_a_1325_, v_a_1326_, v_a_1327_, v_a_1328_);
if (lean_obj_tag(v___x_1452_) == 0)
{
lean_object* v_a_1453_; lean_object* v___x_1454_; 
v_a_1453_ = lean_ctor_get(v___x_1452_, 0);
lean_inc(v_a_1453_);
lean_dec_ref(v___x_1452_);
lean_inc_ref(v_arg_1451_);
v___x_1454_ = l_Lean_Meta_Closure_collectExprAux___lam__0(v_arg_1451_, v_a_1323_, v_a_1324_, v_a_1325_, v_a_1326_, v_a_1327_, v_a_1328_);
if (lean_obj_tag(v___x_1454_) == 0)
{
lean_object* v_a_1455_; lean_object* v___x_1457_; uint8_t v_isShared_1458_; uint8_t v_isSharedCheck_1474_; 
v_a_1455_ = lean_ctor_get(v___x_1454_, 0);
v_isSharedCheck_1474_ = !lean_is_exclusive(v___x_1454_);
if (v_isSharedCheck_1474_ == 0)
{
v___x_1457_ = v___x_1454_;
v_isShared_1458_ = v_isSharedCheck_1474_;
goto v_resetjp_1456_;
}
else
{
lean_inc(v_a_1455_);
lean_dec(v___x_1454_);
v___x_1457_ = lean_box(0);
v_isShared_1458_ = v_isSharedCheck_1474_;
goto v_resetjp_1456_;
}
v_resetjp_1456_:
{
uint8_t v___y_1460_; size_t v___x_1468_; size_t v___x_1469_; uint8_t v___x_1470_; 
v___x_1468_ = lean_ptr_addr(v_fn_1450_);
v___x_1469_ = lean_ptr_addr(v_a_1453_);
v___x_1470_ = lean_usize_dec_eq(v___x_1468_, v___x_1469_);
if (v___x_1470_ == 0)
{
v___y_1460_ = v___x_1470_;
goto v___jp_1459_;
}
else
{
size_t v___x_1471_; size_t v___x_1472_; uint8_t v___x_1473_; 
v___x_1471_ = lean_ptr_addr(v_arg_1451_);
v___x_1472_ = lean_ptr_addr(v_a_1455_);
v___x_1473_ = lean_usize_dec_eq(v___x_1471_, v___x_1472_);
v___y_1460_ = v___x_1473_;
goto v___jp_1459_;
}
v___jp_1459_:
{
if (v___y_1460_ == 0)
{
lean_object* v___x_1461_; lean_object* v___x_1463_; 
lean_dec_ref(v_e_1322_);
v___x_1461_ = l_Lean_Expr_app___override(v_a_1453_, v_a_1455_);
if (v_isShared_1458_ == 0)
{
lean_ctor_set(v___x_1457_, 0, v___x_1461_);
v___x_1463_ = v___x_1457_;
goto v_reusejp_1462_;
}
else
{
lean_object* v_reuseFailAlloc_1464_; 
v_reuseFailAlloc_1464_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1464_, 0, v___x_1461_);
v___x_1463_ = v_reuseFailAlloc_1464_;
goto v_reusejp_1462_;
}
v_reusejp_1462_:
{
return v___x_1463_;
}
}
else
{
lean_object* v___x_1466_; 
lean_dec(v_a_1455_);
lean_dec(v_a_1453_);
if (v_isShared_1458_ == 0)
{
lean_ctor_set(v___x_1457_, 0, v_e_1322_);
v___x_1466_ = v___x_1457_;
goto v_reusejp_1465_;
}
else
{
lean_object* v_reuseFailAlloc_1467_; 
v_reuseFailAlloc_1467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1467_, 0, v_e_1322_);
v___x_1466_ = v_reuseFailAlloc_1467_;
goto v_reusejp_1465_;
}
v_reusejp_1465_:
{
return v___x_1466_;
}
}
}
}
}
else
{
lean_dec(v_a_1453_);
lean_dec_ref(v_e_1322_);
return v___x_1454_;
}
}
else
{
lean_dec_ref(v_e_1322_);
return v___x_1452_;
}
}
case 10:
{
lean_object* v_data_1475_; lean_object* v_expr_1476_; lean_object* v___x_1477_; 
v_data_1475_ = lean_ctor_get(v_e_1322_, 0);
v_expr_1476_ = lean_ctor_get(v_e_1322_, 1);
lean_inc_ref(v_expr_1476_);
v___x_1477_ = l_Lean_Meta_Closure_collectExprAux___lam__0(v_expr_1476_, v_a_1323_, v_a_1324_, v_a_1325_, v_a_1326_, v_a_1327_, v_a_1328_);
if (lean_obj_tag(v___x_1477_) == 0)
{
lean_object* v_a_1478_; lean_object* v___x_1480_; uint8_t v_isShared_1481_; uint8_t v_isSharedCheck_1492_; 
v_a_1478_ = lean_ctor_get(v___x_1477_, 0);
v_isSharedCheck_1492_ = !lean_is_exclusive(v___x_1477_);
if (v_isSharedCheck_1492_ == 0)
{
v___x_1480_ = v___x_1477_;
v_isShared_1481_ = v_isSharedCheck_1492_;
goto v_resetjp_1479_;
}
else
{
lean_inc(v_a_1478_);
lean_dec(v___x_1477_);
v___x_1480_ = lean_box(0);
v_isShared_1481_ = v_isSharedCheck_1492_;
goto v_resetjp_1479_;
}
v_resetjp_1479_:
{
size_t v___x_1482_; size_t v___x_1483_; uint8_t v___x_1484_; 
v___x_1482_ = lean_ptr_addr(v_expr_1476_);
v___x_1483_ = lean_ptr_addr(v_a_1478_);
v___x_1484_ = lean_usize_dec_eq(v___x_1482_, v___x_1483_);
if (v___x_1484_ == 0)
{
lean_object* v___x_1485_; lean_object* v___x_1487_; 
lean_inc(v_data_1475_);
lean_dec_ref(v_e_1322_);
v___x_1485_ = l_Lean_Expr_mdata___override(v_data_1475_, v_a_1478_);
if (v_isShared_1481_ == 0)
{
lean_ctor_set(v___x_1480_, 0, v___x_1485_);
v___x_1487_ = v___x_1480_;
goto v_reusejp_1486_;
}
else
{
lean_object* v_reuseFailAlloc_1488_; 
v_reuseFailAlloc_1488_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1488_, 0, v___x_1485_);
v___x_1487_ = v_reuseFailAlloc_1488_;
goto v_reusejp_1486_;
}
v_reusejp_1486_:
{
return v___x_1487_;
}
}
else
{
lean_object* v___x_1490_; 
lean_dec(v_a_1478_);
if (v_isShared_1481_ == 0)
{
lean_ctor_set(v___x_1480_, 0, v_e_1322_);
v___x_1490_ = v___x_1480_;
goto v_reusejp_1489_;
}
else
{
lean_object* v_reuseFailAlloc_1491_; 
v_reuseFailAlloc_1491_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1491_, 0, v_e_1322_);
v___x_1490_ = v_reuseFailAlloc_1491_;
goto v_reusejp_1489_;
}
v_reusejp_1489_:
{
return v___x_1490_;
}
}
}
}
else
{
lean_dec_ref(v_e_1322_);
return v___x_1477_;
}
}
case 3:
{
lean_object* v_u_1493_; lean_object* v___x_1494_; 
v_u_1493_ = lean_ctor_get(v_e_1322_, 0);
lean_inc(v_u_1493_);
v___x_1494_ = l_Lean_Meta_Closure_collectLevel___redArg(v_u_1493_, v_a_1324_);
if (lean_obj_tag(v___x_1494_) == 0)
{
lean_object* v_a_1495_; lean_object* v___x_1497_; uint8_t v_isShared_1498_; uint8_t v_isSharedCheck_1509_; 
v_a_1495_ = lean_ctor_get(v___x_1494_, 0);
v_isSharedCheck_1509_ = !lean_is_exclusive(v___x_1494_);
if (v_isSharedCheck_1509_ == 0)
{
v___x_1497_ = v___x_1494_;
v_isShared_1498_ = v_isSharedCheck_1509_;
goto v_resetjp_1496_;
}
else
{
lean_inc(v_a_1495_);
lean_dec(v___x_1494_);
v___x_1497_ = lean_box(0);
v_isShared_1498_ = v_isSharedCheck_1509_;
goto v_resetjp_1496_;
}
v_resetjp_1496_:
{
size_t v___x_1499_; size_t v___x_1500_; uint8_t v___x_1501_; 
v___x_1499_ = lean_ptr_addr(v_u_1493_);
v___x_1500_ = lean_ptr_addr(v_a_1495_);
v___x_1501_ = lean_usize_dec_eq(v___x_1499_, v___x_1500_);
if (v___x_1501_ == 0)
{
lean_object* v___x_1502_; lean_object* v___x_1504_; 
lean_dec_ref(v_e_1322_);
v___x_1502_ = l_Lean_Expr_sort___override(v_a_1495_);
if (v_isShared_1498_ == 0)
{
lean_ctor_set(v___x_1497_, 0, v___x_1502_);
v___x_1504_ = v___x_1497_;
goto v_reusejp_1503_;
}
else
{
lean_object* v_reuseFailAlloc_1505_; 
v_reuseFailAlloc_1505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1505_, 0, v___x_1502_);
v___x_1504_ = v_reuseFailAlloc_1505_;
goto v_reusejp_1503_;
}
v_reusejp_1503_:
{
return v___x_1504_;
}
}
else
{
lean_object* v___x_1507_; 
lean_dec(v_a_1495_);
if (v_isShared_1498_ == 0)
{
lean_ctor_set(v___x_1497_, 0, v_e_1322_);
v___x_1507_ = v___x_1497_;
goto v_reusejp_1506_;
}
else
{
lean_object* v_reuseFailAlloc_1508_; 
v_reuseFailAlloc_1508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1508_, 0, v_e_1322_);
v___x_1507_ = v_reuseFailAlloc_1508_;
goto v_reusejp_1506_;
}
v_reusejp_1506_:
{
return v___x_1507_;
}
}
}
}
else
{
lean_object* v_a_1510_; lean_object* v___x_1512_; uint8_t v_isShared_1513_; uint8_t v_isSharedCheck_1517_; 
lean_dec_ref(v_e_1322_);
v_a_1510_ = lean_ctor_get(v___x_1494_, 0);
v_isSharedCheck_1517_ = !lean_is_exclusive(v___x_1494_);
if (v_isSharedCheck_1517_ == 0)
{
v___x_1512_ = v___x_1494_;
v_isShared_1513_ = v_isSharedCheck_1517_;
goto v_resetjp_1511_;
}
else
{
lean_inc(v_a_1510_);
lean_dec(v___x_1494_);
v___x_1512_ = lean_box(0);
v_isShared_1513_ = v_isSharedCheck_1517_;
goto v_resetjp_1511_;
}
v_resetjp_1511_:
{
lean_object* v___x_1515_; 
if (v_isShared_1513_ == 0)
{
v___x_1515_ = v___x_1512_;
goto v_reusejp_1514_;
}
else
{
lean_object* v_reuseFailAlloc_1516_; 
v_reuseFailAlloc_1516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1516_, 0, v_a_1510_);
v___x_1515_ = v_reuseFailAlloc_1516_;
goto v_reusejp_1514_;
}
v_reusejp_1514_:
{
return v___x_1515_;
}
}
}
}
case 4:
{
lean_object* v_declName_1518_; lean_object* v_us_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; 
v_declName_1518_ = lean_ctor_get(v_e_1322_, 0);
v_us_1519_ = lean_ctor_get(v_e_1322_, 1);
v___x_1520_ = lean_box(0);
lean_inc(v_us_1519_);
v___x_1521_ = l_List_mapM_loop___at___00Lean_Meta_Closure_collectExprAux_spec__2___redArg(v_us_1519_, v___x_1520_, v_a_1324_);
if (lean_obj_tag(v___x_1521_) == 0)
{
lean_object* v_a_1522_; lean_object* v___x_1524_; uint8_t v_isShared_1525_; uint8_t v_isSharedCheck_1534_; 
v_a_1522_ = lean_ctor_get(v___x_1521_, 0);
v_isSharedCheck_1534_ = !lean_is_exclusive(v___x_1521_);
if (v_isSharedCheck_1534_ == 0)
{
v___x_1524_ = v___x_1521_;
v_isShared_1525_ = v_isSharedCheck_1534_;
goto v_resetjp_1523_;
}
else
{
lean_inc(v_a_1522_);
lean_dec(v___x_1521_);
v___x_1524_ = lean_box(0);
v_isShared_1525_ = v_isSharedCheck_1534_;
goto v_resetjp_1523_;
}
v_resetjp_1523_:
{
uint8_t v___x_1526_; 
v___x_1526_ = l_ptrEqList___redArg(v_us_1519_, v_a_1522_);
if (v___x_1526_ == 0)
{
lean_object* v___x_1527_; lean_object* v___x_1529_; 
lean_inc(v_declName_1518_);
lean_dec_ref(v_e_1322_);
v___x_1527_ = l_Lean_Expr_const___override(v_declName_1518_, v_a_1522_);
if (v_isShared_1525_ == 0)
{
lean_ctor_set(v___x_1524_, 0, v___x_1527_);
v___x_1529_ = v___x_1524_;
goto v_reusejp_1528_;
}
else
{
lean_object* v_reuseFailAlloc_1530_; 
v_reuseFailAlloc_1530_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1530_, 0, v___x_1527_);
v___x_1529_ = v_reuseFailAlloc_1530_;
goto v_reusejp_1528_;
}
v_reusejp_1528_:
{
return v___x_1529_;
}
}
else
{
lean_object* v___x_1532_; 
lean_dec(v_a_1522_);
if (v_isShared_1525_ == 0)
{
lean_ctor_set(v___x_1524_, 0, v_e_1322_);
v___x_1532_ = v___x_1524_;
goto v_reusejp_1531_;
}
else
{
lean_object* v_reuseFailAlloc_1533_; 
v_reuseFailAlloc_1533_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1533_, 0, v_e_1322_);
v___x_1532_ = v_reuseFailAlloc_1533_;
goto v_reusejp_1531_;
}
v_reusejp_1531_:
{
return v___x_1532_;
}
}
}
}
else
{
lean_object* v_a_1535_; lean_object* v___x_1537_; uint8_t v_isShared_1538_; uint8_t v_isSharedCheck_1542_; 
lean_dec_ref(v_e_1322_);
v_a_1535_ = lean_ctor_get(v___x_1521_, 0);
v_isSharedCheck_1542_ = !lean_is_exclusive(v___x_1521_);
if (v_isSharedCheck_1542_ == 0)
{
v___x_1537_ = v___x_1521_;
v_isShared_1538_ = v_isSharedCheck_1542_;
goto v_resetjp_1536_;
}
else
{
lean_inc(v_a_1535_);
lean_dec(v___x_1521_);
v___x_1537_ = lean_box(0);
v_isShared_1538_ = v_isSharedCheck_1542_;
goto v_resetjp_1536_;
}
v_resetjp_1536_:
{
lean_object* v___x_1540_; 
if (v_isShared_1538_ == 0)
{
v___x_1540_ = v___x_1537_;
goto v_reusejp_1539_;
}
else
{
lean_object* v_reuseFailAlloc_1541_; 
v_reuseFailAlloc_1541_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1541_, 0, v_a_1535_);
v___x_1540_ = v_reuseFailAlloc_1541_;
goto v_reusejp_1539_;
}
v_reusejp_1539_:
{
return v___x_1540_;
}
}
}
}
case 2:
{
lean_object* v_mvarId_1543_; lean_object* v___x_1544_; 
v_mvarId_1543_ = lean_ctor_get(v_e_1322_, 0);
lean_inc(v_mvarId_1543_);
v___x_1544_ = l_Lean_MVarId_getDecl(v_mvarId_1543_, v_a_1325_, v_a_1326_, v_a_1327_, v_a_1328_);
if (lean_obj_tag(v___x_1544_) == 0)
{
lean_object* v_a_1545_; lean_object* v_type_1546_; lean_object* v___x_1547_; 
v_a_1545_ = lean_ctor_get(v___x_1544_, 0);
lean_inc(v_a_1545_);
lean_dec_ref(v___x_1544_);
v_type_1546_ = lean_ctor_get(v_a_1545_, 2);
lean_inc_ref_n(v_type_1546_, 2);
lean_dec(v_a_1545_);
v___x_1547_ = l_Lean_Meta_Closure_preprocess(v_type_1546_, v_a_1323_, v_a_1324_, v_a_1325_, v_a_1326_, v_a_1327_, v_a_1328_);
if (lean_obj_tag(v___x_1547_) == 0)
{
lean_object* v_a_1548_; lean_object* v___x_1549_; 
v_a_1548_ = lean_ctor_get(v___x_1547_, 0);
lean_inc(v_a_1548_);
lean_dec_ref(v___x_1547_);
v___x_1549_ = l_Lean_Meta_Closure_collectExprAux___lam__0(v_a_1548_, v_a_1323_, v_a_1324_, v_a_1325_, v_a_1326_, v_a_1327_, v_a_1328_);
if (lean_obj_tag(v___x_1549_) == 0)
{
lean_object* v_a_1550_; lean_object* v___x_1551_; 
v_a_1550_ = lean_ctor_get(v___x_1549_, 0);
lean_inc(v_a_1550_);
lean_dec_ref(v___x_1549_);
v___x_1551_ = l_Lean_mkFreshFVarId___at___00Lean_Meta_Closure_collectExprAux_spec__3(v_a_1323_, v_a_1324_, v_a_1325_, v_a_1326_, v_a_1327_, v_a_1328_);
if (lean_obj_tag(v___x_1551_) == 0)
{
lean_object* v_a_1552_; lean_object* v___x_1553_; 
v_a_1552_ = lean_ctor_get(v___x_1551_, 0);
lean_inc(v_a_1552_);
lean_dec_ref(v___x_1551_);
v___x_1553_ = l_Lean_Meta_Closure_mkNextUserName___redArg(v_a_1324_);
if (lean_obj_tag(v___x_1553_) == 0)
{
lean_object* v_a_1554_; lean_object* v___x_1556_; uint8_t v_isShared_1557_; uint8_t v_isSharedCheck_1616_; 
v_a_1554_ = lean_ctor_get(v___x_1553_, 0);
v_isSharedCheck_1616_ = !lean_is_exclusive(v___x_1553_);
if (v_isSharedCheck_1616_ == 0)
{
v___x_1556_ = v___x_1553_;
v_isShared_1557_ = v_isSharedCheck_1616_;
goto v_resetjp_1555_;
}
else
{
lean_inc(v_a_1554_);
lean_dec(v___x_1553_);
v___x_1556_ = lean_box(0);
v_isShared_1557_ = v_isSharedCheck_1616_;
goto v_resetjp_1555_;
}
v_resetjp_1555_:
{
lean_object* v_e_x27_1559_; lean_object* v___y_1560_; lean_object* v___x_1592_; 
v___x_1592_ = l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__4___redArg(v_mvarId_1543_, v_a_1326_);
if (lean_obj_tag(v___x_1592_) == 0)
{
lean_object* v_a_1593_; 
v_a_1593_ = lean_ctor_get(v___x_1592_, 0);
lean_inc(v_a_1593_);
lean_dec_ref(v___x_1592_);
if (lean_obj_tag(v_a_1593_) == 1)
{
lean_object* v_val_1594_; lean_object* v___x_1596_; uint8_t v_isShared_1597_; uint8_t v_isSharedCheck_1607_; 
v_val_1594_ = lean_ctor_get(v_a_1593_, 0);
v_isSharedCheck_1607_ = !lean_is_exclusive(v_a_1593_);
if (v_isSharedCheck_1607_ == 0)
{
v___x_1596_ = v_a_1593_;
v_isShared_1597_ = v_isSharedCheck_1607_;
goto v_resetjp_1595_;
}
else
{
lean_inc(v_val_1594_);
lean_dec(v_a_1593_);
v___x_1596_ = lean_box(0);
v_isShared_1597_ = v_isSharedCheck_1607_;
goto v_resetjp_1595_;
}
v_resetjp_1595_:
{
lean_object* v_fvars_1598_; lean_object* v___f_1599_; lean_object* v___x_1600_; lean_object* v___x_1602_; 
v_fvars_1598_ = lean_ctor_get(v_val_1594_, 0);
lean_inc_ref(v_fvars_1598_);
lean_dec(v_val_1594_);
v___f_1599_ = lean_alloc_closure((void*)(l_Lean_Meta_Closure_collectExprAux___lam__1___boxed), 10, 1);
lean_closure_set(v___f_1599_, 0, v_e_1322_);
v___x_1600_ = lean_array_get_size(v_fvars_1598_);
lean_dec_ref(v_fvars_1598_);
if (v_isShared_1597_ == 0)
{
lean_ctor_set(v___x_1596_, 0, v___x_1600_);
v___x_1602_ = v___x_1596_;
goto v_reusejp_1601_;
}
else
{
lean_object* v_reuseFailAlloc_1606_; 
v_reuseFailAlloc_1606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1606_, 0, v___x_1600_);
v___x_1602_ = v_reuseFailAlloc_1606_;
goto v_reusejp_1601_;
}
v_reusejp_1601_:
{
uint8_t v___x_1603_; lean_object* v___x_1604_; 
v___x_1603_ = 0;
v___x_1604_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Closure_collectExprAux_spec__5___redArg(v_type_1546_, v___x_1602_, v___f_1599_, v___x_1603_, v___x_1603_, v_a_1323_, v_a_1324_, v_a_1325_, v_a_1326_, v_a_1327_, v_a_1328_);
if (lean_obj_tag(v___x_1604_) == 0)
{
lean_object* v_a_1605_; 
v_a_1605_ = lean_ctor_get(v___x_1604_, 0);
lean_inc(v_a_1605_);
lean_dec_ref(v___x_1604_);
v_e_x27_1559_ = v_a_1605_;
v___y_1560_ = v_a_1324_;
goto v___jp_1558_;
}
else
{
lean_del_object(v___x_1556_);
lean_dec(v_a_1554_);
lean_dec(v_a_1552_);
lean_dec(v_a_1550_);
return v___x_1604_;
}
}
}
}
else
{
lean_dec(v_a_1593_);
lean_dec_ref(v_type_1546_);
v_e_x27_1559_ = v_e_1322_;
v___y_1560_ = v_a_1324_;
goto v___jp_1558_;
}
}
else
{
lean_object* v_a_1608_; lean_object* v___x_1610_; uint8_t v_isShared_1611_; uint8_t v_isSharedCheck_1615_; 
lean_del_object(v___x_1556_);
lean_dec(v_a_1554_);
lean_dec(v_a_1552_);
lean_dec(v_a_1550_);
lean_dec_ref(v_type_1546_);
lean_dec_ref(v_e_1322_);
v_a_1608_ = lean_ctor_get(v___x_1592_, 0);
v_isSharedCheck_1615_ = !lean_is_exclusive(v___x_1592_);
if (v_isSharedCheck_1615_ == 0)
{
v___x_1610_ = v___x_1592_;
v_isShared_1611_ = v_isSharedCheck_1615_;
goto v_resetjp_1609_;
}
else
{
lean_inc(v_a_1608_);
lean_dec(v___x_1592_);
v___x_1610_ = lean_box(0);
v_isShared_1611_ = v_isSharedCheck_1615_;
goto v_resetjp_1609_;
}
v_resetjp_1609_:
{
lean_object* v___x_1613_; 
if (v_isShared_1611_ == 0)
{
v___x_1613_ = v___x_1610_;
goto v_reusejp_1612_;
}
else
{
lean_object* v_reuseFailAlloc_1614_; 
v_reuseFailAlloc_1614_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1614_, 0, v_a_1608_);
v___x_1613_ = v_reuseFailAlloc_1614_;
goto v_reusejp_1612_;
}
v_reusejp_1612_:
{
return v___x_1613_;
}
}
}
v___jp_1558_:
{
lean_object* v___x_1561_; lean_object* v_visitedLevel_1562_; lean_object* v_visitedExpr_1563_; lean_object* v_levelParams_1564_; lean_object* v_nextLevelIdx_1565_; lean_object* v_levelArgs_1566_; lean_object* v_newLocalDecls_1567_; lean_object* v_newLocalDeclsForMVars_1568_; lean_object* v_newLetDecls_1569_; lean_object* v_nextExprIdx_1570_; lean_object* v_exprMVarArgs_1571_; lean_object* v_exprFVarArgs_1572_; lean_object* v_toProcess_1573_; lean_object* v___x_1575_; uint8_t v_isShared_1576_; uint8_t v_isSharedCheck_1591_; 
v___x_1561_ = lean_st_ref_take(v___y_1560_);
v_visitedLevel_1562_ = lean_ctor_get(v___x_1561_, 0);
v_visitedExpr_1563_ = lean_ctor_get(v___x_1561_, 1);
v_levelParams_1564_ = lean_ctor_get(v___x_1561_, 2);
v_nextLevelIdx_1565_ = lean_ctor_get(v___x_1561_, 3);
v_levelArgs_1566_ = lean_ctor_get(v___x_1561_, 4);
v_newLocalDecls_1567_ = lean_ctor_get(v___x_1561_, 5);
v_newLocalDeclsForMVars_1568_ = lean_ctor_get(v___x_1561_, 6);
v_newLetDecls_1569_ = lean_ctor_get(v___x_1561_, 7);
v_nextExprIdx_1570_ = lean_ctor_get(v___x_1561_, 8);
v_exprMVarArgs_1571_ = lean_ctor_get(v___x_1561_, 9);
v_exprFVarArgs_1572_ = lean_ctor_get(v___x_1561_, 10);
v_toProcess_1573_ = lean_ctor_get(v___x_1561_, 11);
v_isSharedCheck_1591_ = !lean_is_exclusive(v___x_1561_);
if (v_isSharedCheck_1591_ == 0)
{
v___x_1575_ = v___x_1561_;
v_isShared_1576_ = v_isSharedCheck_1591_;
goto v_resetjp_1574_;
}
else
{
lean_inc(v_toProcess_1573_);
lean_inc(v_exprFVarArgs_1572_);
lean_inc(v_exprMVarArgs_1571_);
lean_inc(v_nextExprIdx_1570_);
lean_inc(v_newLetDecls_1569_);
lean_inc(v_newLocalDeclsForMVars_1568_);
lean_inc(v_newLocalDecls_1567_);
lean_inc(v_levelArgs_1566_);
lean_inc(v_nextLevelIdx_1565_);
lean_inc(v_levelParams_1564_);
lean_inc(v_visitedExpr_1563_);
lean_inc(v_visitedLevel_1562_);
lean_dec(v___x_1561_);
v___x_1575_ = lean_box(0);
v_isShared_1576_ = v_isSharedCheck_1591_;
goto v_resetjp_1574_;
}
v_resetjp_1574_:
{
lean_object* v___x_1577_; uint8_t v___x_1578_; uint8_t v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1584_; 
v___x_1577_ = lean_unsigned_to_nat(0u);
v___x_1578_ = 0;
v___x_1579_ = 0;
lean_inc(v_a_1552_);
v___x_1580_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_1580_, 0, v___x_1577_);
lean_ctor_set(v___x_1580_, 1, v_a_1552_);
lean_ctor_set(v___x_1580_, 2, v_a_1554_);
lean_ctor_set(v___x_1580_, 3, v_a_1550_);
lean_ctor_set_uint8(v___x_1580_, sizeof(void*)*4, v___x_1578_);
lean_ctor_set_uint8(v___x_1580_, sizeof(void*)*4 + 1, v___x_1579_);
v___x_1581_ = lean_array_push(v_newLocalDeclsForMVars_1568_, v___x_1580_);
v___x_1582_ = lean_array_push(v_exprMVarArgs_1571_, v_e_x27_1559_);
if (v_isShared_1576_ == 0)
{
lean_ctor_set(v___x_1575_, 9, v___x_1582_);
lean_ctor_set(v___x_1575_, 6, v___x_1581_);
v___x_1584_ = v___x_1575_;
goto v_reusejp_1583_;
}
else
{
lean_object* v_reuseFailAlloc_1590_; 
v_reuseFailAlloc_1590_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_1590_, 0, v_visitedLevel_1562_);
lean_ctor_set(v_reuseFailAlloc_1590_, 1, v_visitedExpr_1563_);
lean_ctor_set(v_reuseFailAlloc_1590_, 2, v_levelParams_1564_);
lean_ctor_set(v_reuseFailAlloc_1590_, 3, v_nextLevelIdx_1565_);
lean_ctor_set(v_reuseFailAlloc_1590_, 4, v_levelArgs_1566_);
lean_ctor_set(v_reuseFailAlloc_1590_, 5, v_newLocalDecls_1567_);
lean_ctor_set(v_reuseFailAlloc_1590_, 6, v___x_1581_);
lean_ctor_set(v_reuseFailAlloc_1590_, 7, v_newLetDecls_1569_);
lean_ctor_set(v_reuseFailAlloc_1590_, 8, v_nextExprIdx_1570_);
lean_ctor_set(v_reuseFailAlloc_1590_, 9, v___x_1582_);
lean_ctor_set(v_reuseFailAlloc_1590_, 10, v_exprFVarArgs_1572_);
lean_ctor_set(v_reuseFailAlloc_1590_, 11, v_toProcess_1573_);
v___x_1584_ = v_reuseFailAlloc_1590_;
goto v_reusejp_1583_;
}
v_reusejp_1583_:
{
lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1588_; 
v___x_1585_ = lean_st_ref_set(v___y_1560_, v___x_1584_);
v___x_1586_ = l_Lean_mkFVar(v_a_1552_);
if (v_isShared_1557_ == 0)
{
lean_ctor_set(v___x_1556_, 0, v___x_1586_);
v___x_1588_ = v___x_1556_;
goto v_reusejp_1587_;
}
else
{
lean_object* v_reuseFailAlloc_1589_; 
v_reuseFailAlloc_1589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1589_, 0, v___x_1586_);
v___x_1588_ = v_reuseFailAlloc_1589_;
goto v_reusejp_1587_;
}
v_reusejp_1587_:
{
return v___x_1588_;
}
}
}
}
}
}
else
{
lean_object* v_a_1617_; lean_object* v___x_1619_; uint8_t v_isShared_1620_; uint8_t v_isSharedCheck_1624_; 
lean_dec(v_a_1552_);
lean_dec(v_a_1550_);
lean_dec_ref(v_type_1546_);
lean_dec_ref(v_e_1322_);
v_a_1617_ = lean_ctor_get(v___x_1553_, 0);
v_isSharedCheck_1624_ = !lean_is_exclusive(v___x_1553_);
if (v_isSharedCheck_1624_ == 0)
{
v___x_1619_ = v___x_1553_;
v_isShared_1620_ = v_isSharedCheck_1624_;
goto v_resetjp_1618_;
}
else
{
lean_inc(v_a_1617_);
lean_dec(v___x_1553_);
v___x_1619_ = lean_box(0);
v_isShared_1620_ = v_isSharedCheck_1624_;
goto v_resetjp_1618_;
}
v_resetjp_1618_:
{
lean_object* v___x_1622_; 
if (v_isShared_1620_ == 0)
{
v___x_1622_ = v___x_1619_;
goto v_reusejp_1621_;
}
else
{
lean_object* v_reuseFailAlloc_1623_; 
v_reuseFailAlloc_1623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1623_, 0, v_a_1617_);
v___x_1622_ = v_reuseFailAlloc_1623_;
goto v_reusejp_1621_;
}
v_reusejp_1621_:
{
return v___x_1622_;
}
}
}
}
else
{
lean_object* v_a_1625_; lean_object* v___x_1627_; uint8_t v_isShared_1628_; uint8_t v_isSharedCheck_1632_; 
lean_dec(v_a_1550_);
lean_dec_ref(v_type_1546_);
lean_dec_ref(v_e_1322_);
v_a_1625_ = lean_ctor_get(v___x_1551_, 0);
v_isSharedCheck_1632_ = !lean_is_exclusive(v___x_1551_);
if (v_isSharedCheck_1632_ == 0)
{
v___x_1627_ = v___x_1551_;
v_isShared_1628_ = v_isSharedCheck_1632_;
goto v_resetjp_1626_;
}
else
{
lean_inc(v_a_1625_);
lean_dec(v___x_1551_);
v___x_1627_ = lean_box(0);
v_isShared_1628_ = v_isSharedCheck_1632_;
goto v_resetjp_1626_;
}
v_resetjp_1626_:
{
lean_object* v___x_1630_; 
if (v_isShared_1628_ == 0)
{
v___x_1630_ = v___x_1627_;
goto v_reusejp_1629_;
}
else
{
lean_object* v_reuseFailAlloc_1631_; 
v_reuseFailAlloc_1631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1631_, 0, v_a_1625_);
v___x_1630_ = v_reuseFailAlloc_1631_;
goto v_reusejp_1629_;
}
v_reusejp_1629_:
{
return v___x_1630_;
}
}
}
}
else
{
lean_dec_ref(v_type_1546_);
lean_dec_ref(v_e_1322_);
return v___x_1549_;
}
}
else
{
lean_dec_ref(v_type_1546_);
lean_dec_ref(v_e_1322_);
return v___x_1547_;
}
}
else
{
lean_object* v_a_1633_; lean_object* v___x_1635_; uint8_t v_isShared_1636_; uint8_t v_isSharedCheck_1640_; 
lean_dec_ref(v_e_1322_);
v_a_1633_ = lean_ctor_get(v___x_1544_, 0);
v_isSharedCheck_1640_ = !lean_is_exclusive(v___x_1544_);
if (v_isSharedCheck_1640_ == 0)
{
v___x_1635_ = v___x_1544_;
v_isShared_1636_ = v_isSharedCheck_1640_;
goto v_resetjp_1634_;
}
else
{
lean_inc(v_a_1633_);
lean_dec(v___x_1544_);
v___x_1635_ = lean_box(0);
v_isShared_1636_ = v_isSharedCheck_1640_;
goto v_resetjp_1634_;
}
v_resetjp_1634_:
{
lean_object* v___x_1638_; 
if (v_isShared_1636_ == 0)
{
v___x_1638_ = v___x_1635_;
goto v_reusejp_1637_;
}
else
{
lean_object* v_reuseFailAlloc_1639_; 
v_reuseFailAlloc_1639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1639_, 0, v_a_1633_);
v___x_1638_ = v_reuseFailAlloc_1639_;
goto v_reusejp_1637_;
}
v_reusejp_1637_:
{
return v___x_1638_;
}
}
}
}
case 1:
{
lean_object* v_fvarId_1641_; uint8_t v___x_1642_; lean_object* v___x_1643_; 
v_fvarId_1641_ = lean_ctor_get(v_e_1322_, 0);
lean_inc_n(v_fvarId_1641_, 2);
lean_dec_ref(v_e_1322_);
v___x_1642_ = 0;
v___x_1643_ = l_Lean_FVarId_getValue_x3f___redArg(v_fvarId_1641_, v___x_1642_, v_a_1325_, v_a_1327_, v_a_1328_);
if (lean_obj_tag(v___x_1643_) == 0)
{
lean_object* v_a_1644_; uint8_t v___y_1646_; lean_object* v___y_1647_; lean_object* v___y_1648_; lean_object* v___y_1649_; lean_object* v___y_1650_; lean_object* v___y_1651_; 
v_a_1644_ = lean_ctor_get(v___x_1643_, 0);
lean_inc(v_a_1644_);
lean_dec_ref(v___x_1643_);
if (v_a_1323_ == 1)
{
if (lean_obj_tag(v_a_1644_) == 1)
{
lean_object* v_val_1681_; lean_object* v___x_1682_; 
lean_dec(v_fvarId_1641_);
v_val_1681_ = lean_ctor_get(v_a_1644_, 0);
lean_inc(v_val_1681_);
lean_dec_ref(v_a_1644_);
v___x_1682_ = l_Lean_Meta_Closure_preprocess(v_val_1681_, v_a_1323_, v_a_1324_, v_a_1325_, v_a_1326_, v_a_1327_, v_a_1328_);
if (lean_obj_tag(v___x_1682_) == 0)
{
lean_object* v_a_1683_; lean_object* v___x_1684_; 
v_a_1683_ = lean_ctor_get(v___x_1682_, 0);
lean_inc(v_a_1683_);
lean_dec_ref(v___x_1682_);
v___x_1684_ = l_Lean_Meta_Closure_collectExprAux___lam__0(v_a_1683_, v_a_1323_, v_a_1324_, v_a_1325_, v_a_1326_, v_a_1327_, v_a_1328_);
return v___x_1684_;
}
else
{
return v___x_1682_;
}
}
else
{
lean_dec(v_a_1644_);
v___y_1646_ = v_a_1323_;
v___y_1647_ = v_a_1324_;
v___y_1648_ = v_a_1325_;
v___y_1649_ = v_a_1326_;
v___y_1650_ = v_a_1327_;
v___y_1651_ = v_a_1328_;
goto v___jp_1645_;
}
}
else
{
lean_dec(v_a_1644_);
v___y_1646_ = v_a_1323_;
v___y_1647_ = v_a_1324_;
v___y_1648_ = v_a_1325_;
v___y_1649_ = v_a_1326_;
v___y_1650_ = v_a_1327_;
v___y_1651_ = v_a_1328_;
goto v___jp_1645_;
}
v___jp_1645_:
{
lean_object* v___x_1652_; 
v___x_1652_ = l_Lean_mkFreshFVarId___at___00Lean_Meta_Closure_collectExprAux_spec__3(v___y_1646_, v___y_1647_, v___y_1648_, v___y_1649_, v___y_1650_, v___y_1651_);
if (lean_obj_tag(v___x_1652_) == 0)
{
lean_object* v_a_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; 
v_a_1653_ = lean_ctor_get(v___x_1652_, 0);
lean_inc_n(v_a_1653_, 2);
lean_dec_ref(v___x_1652_);
v___x_1654_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1654_, 0, v_fvarId_1641_);
lean_ctor_set(v___x_1654_, 1, v_a_1653_);
v___x_1655_ = l_Lean_Meta_Closure_pushToProcess___redArg(v___x_1654_, v___y_1647_);
if (lean_obj_tag(v___x_1655_) == 0)
{
lean_object* v___x_1657_; uint8_t v_isShared_1658_; uint8_t v_isSharedCheck_1663_; 
v_isSharedCheck_1663_ = !lean_is_exclusive(v___x_1655_);
if (v_isSharedCheck_1663_ == 0)
{
lean_object* v_unused_1664_; 
v_unused_1664_ = lean_ctor_get(v___x_1655_, 0);
lean_dec(v_unused_1664_);
v___x_1657_ = v___x_1655_;
v_isShared_1658_ = v_isSharedCheck_1663_;
goto v_resetjp_1656_;
}
else
{
lean_dec(v___x_1655_);
v___x_1657_ = lean_box(0);
v_isShared_1658_ = v_isSharedCheck_1663_;
goto v_resetjp_1656_;
}
v_resetjp_1656_:
{
lean_object* v___x_1659_; lean_object* v___x_1661_; 
v___x_1659_ = l_Lean_mkFVar(v_a_1653_);
if (v_isShared_1658_ == 0)
{
lean_ctor_set(v___x_1657_, 0, v___x_1659_);
v___x_1661_ = v___x_1657_;
goto v_reusejp_1660_;
}
else
{
lean_object* v_reuseFailAlloc_1662_; 
v_reuseFailAlloc_1662_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1662_, 0, v___x_1659_);
v___x_1661_ = v_reuseFailAlloc_1662_;
goto v_reusejp_1660_;
}
v_reusejp_1660_:
{
return v___x_1661_;
}
}
}
else
{
lean_object* v_a_1665_; lean_object* v___x_1667_; uint8_t v_isShared_1668_; uint8_t v_isSharedCheck_1672_; 
lean_dec(v_a_1653_);
v_a_1665_ = lean_ctor_get(v___x_1655_, 0);
v_isSharedCheck_1672_ = !lean_is_exclusive(v___x_1655_);
if (v_isSharedCheck_1672_ == 0)
{
v___x_1667_ = v___x_1655_;
v_isShared_1668_ = v_isSharedCheck_1672_;
goto v_resetjp_1666_;
}
else
{
lean_inc(v_a_1665_);
lean_dec(v___x_1655_);
v___x_1667_ = lean_box(0);
v_isShared_1668_ = v_isSharedCheck_1672_;
goto v_resetjp_1666_;
}
v_resetjp_1666_:
{
lean_object* v___x_1670_; 
if (v_isShared_1668_ == 0)
{
v___x_1670_ = v___x_1667_;
goto v_reusejp_1669_;
}
else
{
lean_object* v_reuseFailAlloc_1671_; 
v_reuseFailAlloc_1671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1671_, 0, v_a_1665_);
v___x_1670_ = v_reuseFailAlloc_1671_;
goto v_reusejp_1669_;
}
v_reusejp_1669_:
{
return v___x_1670_;
}
}
}
}
else
{
lean_object* v_a_1673_; lean_object* v___x_1675_; uint8_t v_isShared_1676_; uint8_t v_isSharedCheck_1680_; 
lean_dec(v_fvarId_1641_);
v_a_1673_ = lean_ctor_get(v___x_1652_, 0);
v_isSharedCheck_1680_ = !lean_is_exclusive(v___x_1652_);
if (v_isSharedCheck_1680_ == 0)
{
v___x_1675_ = v___x_1652_;
v_isShared_1676_ = v_isSharedCheck_1680_;
goto v_resetjp_1674_;
}
else
{
lean_inc(v_a_1673_);
lean_dec(v___x_1652_);
v___x_1675_ = lean_box(0);
v_isShared_1676_ = v_isSharedCheck_1680_;
goto v_resetjp_1674_;
}
v_resetjp_1674_:
{
lean_object* v___x_1678_; 
if (v_isShared_1676_ == 0)
{
v___x_1678_ = v___x_1675_;
goto v_reusejp_1677_;
}
else
{
lean_object* v_reuseFailAlloc_1679_; 
v_reuseFailAlloc_1679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1679_, 0, v_a_1673_);
v___x_1678_ = v_reuseFailAlloc_1679_;
goto v_reusejp_1677_;
}
v_reusejp_1677_:
{
return v___x_1678_;
}
}
}
}
}
else
{
lean_object* v_a_1685_; lean_object* v___x_1687_; uint8_t v_isShared_1688_; uint8_t v_isSharedCheck_1692_; 
lean_dec(v_fvarId_1641_);
v_a_1685_ = lean_ctor_get(v___x_1643_, 0);
v_isSharedCheck_1692_ = !lean_is_exclusive(v___x_1643_);
if (v_isSharedCheck_1692_ == 0)
{
v___x_1687_ = v___x_1643_;
v_isShared_1688_ = v_isSharedCheck_1692_;
goto v_resetjp_1686_;
}
else
{
lean_inc(v_a_1685_);
lean_dec(v___x_1643_);
v___x_1687_ = lean_box(0);
v_isShared_1688_ = v_isSharedCheck_1692_;
goto v_resetjp_1686_;
}
v_resetjp_1686_:
{
lean_object* v___x_1690_; 
if (v_isShared_1688_ == 0)
{
v___x_1690_ = v___x_1687_;
goto v_reusejp_1689_;
}
else
{
lean_object* v_reuseFailAlloc_1691_; 
v_reuseFailAlloc_1691_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1691_, 0, v_a_1685_);
v___x_1690_ = v_reuseFailAlloc_1691_;
goto v_reusejp_1689_;
}
v_reusejp_1689_:
{
return v___x_1690_;
}
}
}
}
default: 
{
lean_object* v___x_1693_; 
v___x_1693_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1693_, 0, v_e_1322_);
return v___x_1693_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectExprAux___lam__0(lean_object* v_e_1694_, uint8_t v___y_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_){
_start:
{
uint8_t v___x_1745_; 
v___x_1745_ = l_Lean_Expr_hasLevelParam(v_e_1694_);
if (v___x_1745_ == 0)
{
uint8_t v___x_1746_; 
v___x_1746_ = l_Lean_Expr_hasFVar(v_e_1694_);
if (v___x_1746_ == 0)
{
uint8_t v___x_1747_; 
v___x_1747_ = l_Lean_Expr_hasMVar(v_e_1694_);
if (v___x_1747_ == 0)
{
lean_object* v___x_1748_; 
v___x_1748_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1748_, 0, v_e_1694_);
return v___x_1748_;
}
else
{
goto v___jp_1702_;
}
}
else
{
goto v___jp_1702_;
}
}
else
{
goto v___jp_1702_;
}
v___jp_1702_:
{
lean_object* v___x_1703_; lean_object* v_visitedExpr_1704_; lean_object* v___x_1705_; 
v___x_1703_ = lean_st_ref_get(v___y_1696_);
v_visitedExpr_1704_ = lean_ctor_get(v___x_1703_, 1);
lean_inc_ref(v_visitedExpr_1704_);
lean_dec(v___x_1703_);
v___x_1705_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0___redArg(v_visitedExpr_1704_, v_e_1694_);
lean_dec_ref(v_visitedExpr_1704_);
if (lean_obj_tag(v___x_1705_) == 0)
{
lean_object* v___x_1706_; 
lean_inc_ref(v_e_1694_);
v___x_1706_ = l_Lean_Meta_Closure_collectExprAux(v_e_1694_, v___y_1695_, v___y_1696_, v___y_1697_, v___y_1698_, v___y_1699_, v___y_1700_);
if (lean_obj_tag(v___x_1706_) == 0)
{
lean_object* v_a_1707_; lean_object* v___x_1709_; uint8_t v_isShared_1710_; uint8_t v_isSharedCheck_1736_; 
v_a_1707_ = lean_ctor_get(v___x_1706_, 0);
v_isSharedCheck_1736_ = !lean_is_exclusive(v___x_1706_);
if (v_isSharedCheck_1736_ == 0)
{
v___x_1709_ = v___x_1706_;
v_isShared_1710_ = v_isSharedCheck_1736_;
goto v_resetjp_1708_;
}
else
{
lean_inc(v_a_1707_);
lean_dec(v___x_1706_);
v___x_1709_ = lean_box(0);
v_isShared_1710_ = v_isSharedCheck_1736_;
goto v_resetjp_1708_;
}
v_resetjp_1708_:
{
lean_object* v___x_1711_; lean_object* v_visitedLevel_1712_; lean_object* v_visitedExpr_1713_; lean_object* v_levelParams_1714_; lean_object* v_nextLevelIdx_1715_; lean_object* v_levelArgs_1716_; lean_object* v_newLocalDecls_1717_; lean_object* v_newLocalDeclsForMVars_1718_; lean_object* v_newLetDecls_1719_; lean_object* v_nextExprIdx_1720_; lean_object* v_exprMVarArgs_1721_; lean_object* v_exprFVarArgs_1722_; lean_object* v_toProcess_1723_; lean_object* v___x_1725_; uint8_t v_isShared_1726_; uint8_t v_isSharedCheck_1735_; 
v___x_1711_ = lean_st_ref_take(v___y_1696_);
v_visitedLevel_1712_ = lean_ctor_get(v___x_1711_, 0);
v_visitedExpr_1713_ = lean_ctor_get(v___x_1711_, 1);
v_levelParams_1714_ = lean_ctor_get(v___x_1711_, 2);
v_nextLevelIdx_1715_ = lean_ctor_get(v___x_1711_, 3);
v_levelArgs_1716_ = lean_ctor_get(v___x_1711_, 4);
v_newLocalDecls_1717_ = lean_ctor_get(v___x_1711_, 5);
v_newLocalDeclsForMVars_1718_ = lean_ctor_get(v___x_1711_, 6);
v_newLetDecls_1719_ = lean_ctor_get(v___x_1711_, 7);
v_nextExprIdx_1720_ = lean_ctor_get(v___x_1711_, 8);
v_exprMVarArgs_1721_ = lean_ctor_get(v___x_1711_, 9);
v_exprFVarArgs_1722_ = lean_ctor_get(v___x_1711_, 10);
v_toProcess_1723_ = lean_ctor_get(v___x_1711_, 11);
v_isSharedCheck_1735_ = !lean_is_exclusive(v___x_1711_);
if (v_isSharedCheck_1735_ == 0)
{
v___x_1725_ = v___x_1711_;
v_isShared_1726_ = v_isSharedCheck_1735_;
goto v_resetjp_1724_;
}
else
{
lean_inc(v_toProcess_1723_);
lean_inc(v_exprFVarArgs_1722_);
lean_inc(v_exprMVarArgs_1721_);
lean_inc(v_nextExprIdx_1720_);
lean_inc(v_newLetDecls_1719_);
lean_inc(v_newLocalDeclsForMVars_1718_);
lean_inc(v_newLocalDecls_1717_);
lean_inc(v_levelArgs_1716_);
lean_inc(v_nextLevelIdx_1715_);
lean_inc(v_levelParams_1714_);
lean_inc(v_visitedExpr_1713_);
lean_inc(v_visitedLevel_1712_);
lean_dec(v___x_1711_);
v___x_1725_ = lean_box(0);
v_isShared_1726_ = v_isSharedCheck_1735_;
goto v_resetjp_1724_;
}
v_resetjp_1724_:
{
lean_object* v___x_1727_; lean_object* v___x_1729_; 
lean_inc(v_a_1707_);
v___x_1727_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1___redArg(v_visitedExpr_1713_, v_e_1694_, v_a_1707_);
if (v_isShared_1726_ == 0)
{
lean_ctor_set(v___x_1725_, 1, v___x_1727_);
v___x_1729_ = v___x_1725_;
goto v_reusejp_1728_;
}
else
{
lean_object* v_reuseFailAlloc_1734_; 
v_reuseFailAlloc_1734_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_1734_, 0, v_visitedLevel_1712_);
lean_ctor_set(v_reuseFailAlloc_1734_, 1, v___x_1727_);
lean_ctor_set(v_reuseFailAlloc_1734_, 2, v_levelParams_1714_);
lean_ctor_set(v_reuseFailAlloc_1734_, 3, v_nextLevelIdx_1715_);
lean_ctor_set(v_reuseFailAlloc_1734_, 4, v_levelArgs_1716_);
lean_ctor_set(v_reuseFailAlloc_1734_, 5, v_newLocalDecls_1717_);
lean_ctor_set(v_reuseFailAlloc_1734_, 6, v_newLocalDeclsForMVars_1718_);
lean_ctor_set(v_reuseFailAlloc_1734_, 7, v_newLetDecls_1719_);
lean_ctor_set(v_reuseFailAlloc_1734_, 8, v_nextExprIdx_1720_);
lean_ctor_set(v_reuseFailAlloc_1734_, 9, v_exprMVarArgs_1721_);
lean_ctor_set(v_reuseFailAlloc_1734_, 10, v_exprFVarArgs_1722_);
lean_ctor_set(v_reuseFailAlloc_1734_, 11, v_toProcess_1723_);
v___x_1729_ = v_reuseFailAlloc_1734_;
goto v_reusejp_1728_;
}
v_reusejp_1728_:
{
lean_object* v___x_1730_; lean_object* v___x_1732_; 
v___x_1730_ = lean_st_ref_set(v___y_1696_, v___x_1729_);
if (v_isShared_1710_ == 0)
{
v___x_1732_ = v___x_1709_;
goto v_reusejp_1731_;
}
else
{
lean_object* v_reuseFailAlloc_1733_; 
v_reuseFailAlloc_1733_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1733_, 0, v_a_1707_);
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
else
{
lean_dec_ref(v_e_1694_);
return v___x_1706_;
}
}
else
{
lean_object* v_val_1737_; lean_object* v___x_1739_; uint8_t v_isShared_1740_; uint8_t v_isSharedCheck_1744_; 
lean_dec_ref(v_e_1694_);
v_val_1737_ = lean_ctor_get(v___x_1705_, 0);
v_isSharedCheck_1744_ = !lean_is_exclusive(v___x_1705_);
if (v_isSharedCheck_1744_ == 0)
{
v___x_1739_ = v___x_1705_;
v_isShared_1740_ = v_isSharedCheck_1744_;
goto v_resetjp_1738_;
}
else
{
lean_inc(v_val_1737_);
lean_dec(v___x_1705_);
v___x_1739_ = lean_box(0);
v_isShared_1740_ = v_isSharedCheck_1744_;
goto v_resetjp_1738_;
}
v_resetjp_1738_:
{
lean_object* v___x_1742_; 
if (v_isShared_1740_ == 0)
{
lean_ctor_set_tag(v___x_1739_, 0);
v___x_1742_ = v___x_1739_;
goto v_reusejp_1741_;
}
else
{
lean_object* v_reuseFailAlloc_1743_; 
v_reuseFailAlloc_1743_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1743_, 0, v_val_1737_);
v___x_1742_ = v_reuseFailAlloc_1743_;
goto v_reusejp_1741_;
}
v_reusejp_1741_:
{
return v___x_1742_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectExprAux___lam__0___boxed(lean_object* v_e_1749_, lean_object* v___y_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_){
_start:
{
uint8_t v___y_18437__boxed_1757_; lean_object* v_res_1758_; 
v___y_18437__boxed_1757_ = lean_unbox(v___y_1750_);
v_res_1758_ = l_Lean_Meta_Closure_collectExprAux___lam__0(v_e_1749_, v___y_18437__boxed_1757_, v___y_1751_, v___y_1752_, v___y_1753_, v___y_1754_, v___y_1755_);
lean_dec(v___y_1755_);
lean_dec_ref(v___y_1754_);
lean_dec(v___y_1753_);
lean_dec_ref(v___y_1752_);
lean_dec(v___y_1751_);
return v_res_1758_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectExprAux___boxed(lean_object* v_e_1759_, lean_object* v_a_1760_, lean_object* v_a_1761_, lean_object* v_a_1762_, lean_object* v_a_1763_, lean_object* v_a_1764_, lean_object* v_a_1765_, lean_object* v_a_1766_){
_start:
{
uint8_t v_a_boxed_1767_; lean_object* v_res_1768_; 
v_a_boxed_1767_ = lean_unbox(v_a_1760_);
v_res_1768_ = l_Lean_Meta_Closure_collectExprAux(v_e_1759_, v_a_boxed_1767_, v_a_1761_, v_a_1762_, v_a_1763_, v_a_1764_, v_a_1765_);
lean_dec(v_a_1765_);
lean_dec_ref(v_a_1764_);
lean_dec(v_a_1763_);
lean_dec_ref(v_a_1762_);
lean_dec(v_a_1761_);
return v_res_1768_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0(lean_object* v_00_u03b2_1769_, lean_object* v_m_1770_, lean_object* v_a_1771_){
_start:
{
lean_object* v___x_1772_; 
v___x_1772_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0___redArg(v_m_1770_, v_a_1771_);
return v___x_1772_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0___boxed(lean_object* v_00_u03b2_1773_, lean_object* v_m_1774_, lean_object* v_a_1775_){
_start:
{
lean_object* v_res_1776_; 
v_res_1776_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0(v_00_u03b2_1773_, v_m_1774_, v_a_1775_);
lean_dec_ref(v_a_1775_);
lean_dec_ref(v_m_1774_);
return v_res_1776_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1(lean_object* v_00_u03b2_1777_, lean_object* v_m_1778_, lean_object* v_a_1779_, lean_object* v_b_1780_){
_start:
{
lean_object* v___x_1781_; 
v___x_1781_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1___redArg(v_m_1778_, v_a_1779_, v_b_1780_);
return v___x_1781_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Closure_collectExprAux_spec__2(lean_object* v_x_1782_, lean_object* v_x_1783_, uint8_t v___y_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_){
_start:
{
lean_object* v___x_1791_; 
v___x_1791_ = l_List_mapM_loop___at___00Lean_Meta_Closure_collectExprAux_spec__2___redArg(v_x_1782_, v_x_1783_, v___y_1785_);
return v___x_1791_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Closure_collectExprAux_spec__2___boxed(lean_object* v_x_1792_, lean_object* v_x_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_){
_start:
{
uint8_t v___y_19253__boxed_1801_; lean_object* v_res_1802_; 
v___y_19253__boxed_1801_ = lean_unbox(v___y_1794_);
v_res_1802_ = l_List_mapM_loop___at___00Lean_Meta_Closure_collectExprAux_spec__2(v_x_1792_, v_x_1793_, v___y_19253__boxed_1801_, v___y_1795_, v___y_1796_, v___y_1797_, v___y_1798_, v___y_1799_);
lean_dec(v___y_1799_);
lean_dec_ref(v___y_1798_);
lean_dec(v___y_1797_);
lean_dec_ref(v___y_1796_);
lean_dec(v___y_1795_);
return v_res_1802_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Closure_collectExprAux_spec__3_spec__7(uint8_t v___y_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_, lean_object* v___y_1808_){
_start:
{
lean_object* v___x_1810_; 
v___x_1810_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Closure_collectExprAux_spec__3_spec__7___redArg(v___y_1808_);
return v___x_1810_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Closure_collectExprAux_spec__3_spec__7___boxed(lean_object* v___y_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_){
_start:
{
uint8_t v___y_19280__boxed_1818_; lean_object* v_res_1819_; 
v___y_19280__boxed_1818_ = lean_unbox(v___y_1811_);
v_res_1819_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Closure_collectExprAux_spec__3_spec__7(v___y_19280__boxed_1818_, v___y_1812_, v___y_1813_, v___y_1814_, v___y_1815_, v___y_1816_);
lean_dec(v___y_1816_);
lean_dec_ref(v___y_1815_);
lean_dec(v___y_1814_);
lean_dec_ref(v___y_1813_);
lean_dec(v___y_1812_);
return v_res_1819_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0_spec__0(lean_object* v_00_u03b2_1820_, lean_object* v_a_1821_, lean_object* v_x_1822_){
_start:
{
lean_object* v___x_1823_; 
v___x_1823_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0_spec__0___redArg(v_a_1821_, v_x_1822_);
return v___x_1823_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1824_, lean_object* v_a_1825_, lean_object* v_x_1826_){
_start:
{
lean_object* v_res_1827_; 
v_res_1827_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0_spec__0(v_00_u03b2_1824_, v_a_1825_, v_x_1826_);
lean_dec(v_x_1826_);
lean_dec_ref(v_a_1825_);
return v_res_1827_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__2(lean_object* v_00_u03b2_1828_, lean_object* v_a_1829_, lean_object* v_x_1830_){
_start:
{
uint8_t v___x_1831_; 
v___x_1831_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__2___redArg(v_a_1829_, v_x_1830_);
return v___x_1831_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1832_, lean_object* v_a_1833_, lean_object* v_x_1834_){
_start:
{
uint8_t v_res_1835_; lean_object* v_r_1836_; 
v_res_1835_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__2(v_00_u03b2_1832_, v_a_1833_, v_x_1834_);
lean_dec(v_x_1834_);
lean_dec_ref(v_a_1833_);
v_r_1836_ = lean_box(v_res_1835_);
return v_r_1836_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__3(lean_object* v_00_u03b2_1837_, lean_object* v_data_1838_){
_start:
{
lean_object* v___x_1839_; 
v___x_1839_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__3___redArg(v_data_1838_);
return v___x_1839_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__4(lean_object* v_00_u03b2_1840_, lean_object* v_a_1841_, lean_object* v_b_1842_, lean_object* v_x_1843_){
_start:
{
lean_object* v___x_1844_; 
v___x_1844_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__4___redArg(v_a_1841_, v_b_1842_, v_x_1843_);
return v___x_1844_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__3_spec__6(lean_object* v_00_u03b2_1845_, lean_object* v_i_1846_, lean_object* v_source_1847_, lean_object* v_target_1848_){
_start:
{
lean_object* v___x_1849_; 
v___x_1849_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__3_spec__6___redArg(v_i_1846_, v_source_1847_, v_target_1848_);
return v___x_1849_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__3_spec__6_spec__10(lean_object* v_00_u03b2_1850_, lean_object* v_x_1851_, lean_object* v_x_1852_){
_start:
{
lean_object* v___x_1853_; 
v___x_1853_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__3_spec__6_spec__10___redArg(v_x_1851_, v_x_1852_);
return v___x_1853_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectExpr(lean_object* v_e_1854_, uint8_t v_a_1855_, lean_object* v_a_1856_, lean_object* v_a_1857_, lean_object* v_a_1858_, lean_object* v_a_1859_, lean_object* v_a_1860_){
_start:
{
lean_object* v___x_1862_; 
v___x_1862_ = l_Lean_Meta_Closure_preprocess(v_e_1854_, v_a_1855_, v_a_1856_, v_a_1857_, v_a_1858_, v_a_1859_, v_a_1860_);
if (lean_obj_tag(v___x_1862_) == 0)
{
lean_object* v_a_1863_; uint8_t v___x_1907_; 
v_a_1863_ = lean_ctor_get(v___x_1862_, 0);
lean_inc(v_a_1863_);
v___x_1907_ = l_Lean_Expr_hasLevelParam(v_a_1863_);
if (v___x_1907_ == 0)
{
uint8_t v___x_1908_; 
v___x_1908_ = l_Lean_Expr_hasFVar(v_a_1863_);
if (v___x_1908_ == 0)
{
uint8_t v___x_1909_; 
v___x_1909_ = l_Lean_Expr_hasMVar(v_a_1863_);
if (v___x_1909_ == 0)
{
lean_dec(v_a_1863_);
return v___x_1862_;
}
else
{
lean_dec_ref(v___x_1862_);
goto v___jp_1864_;
}
}
else
{
lean_dec_ref(v___x_1862_);
goto v___jp_1864_;
}
}
else
{
lean_dec_ref(v___x_1862_);
goto v___jp_1864_;
}
v___jp_1864_:
{
lean_object* v___x_1865_; lean_object* v_visitedExpr_1866_; lean_object* v___x_1867_; 
v___x_1865_ = lean_st_ref_get(v_a_1856_);
v_visitedExpr_1866_ = lean_ctor_get(v___x_1865_, 1);
lean_inc_ref(v_visitedExpr_1866_);
lean_dec(v___x_1865_);
v___x_1867_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0___redArg(v_visitedExpr_1866_, v_a_1863_);
lean_dec_ref(v_visitedExpr_1866_);
if (lean_obj_tag(v___x_1867_) == 0)
{
lean_object* v___x_1868_; 
lean_inc(v_a_1863_);
v___x_1868_ = l_Lean_Meta_Closure_collectExprAux(v_a_1863_, v_a_1855_, v_a_1856_, v_a_1857_, v_a_1858_, v_a_1859_, v_a_1860_);
if (lean_obj_tag(v___x_1868_) == 0)
{
lean_object* v_a_1869_; lean_object* v___x_1871_; uint8_t v_isShared_1872_; uint8_t v_isSharedCheck_1898_; 
v_a_1869_ = lean_ctor_get(v___x_1868_, 0);
v_isSharedCheck_1898_ = !lean_is_exclusive(v___x_1868_);
if (v_isSharedCheck_1898_ == 0)
{
v___x_1871_ = v___x_1868_;
v_isShared_1872_ = v_isSharedCheck_1898_;
goto v_resetjp_1870_;
}
else
{
lean_inc(v_a_1869_);
lean_dec(v___x_1868_);
v___x_1871_ = lean_box(0);
v_isShared_1872_ = v_isSharedCheck_1898_;
goto v_resetjp_1870_;
}
v_resetjp_1870_:
{
lean_object* v___x_1873_; lean_object* v_visitedLevel_1874_; lean_object* v_visitedExpr_1875_; lean_object* v_levelParams_1876_; lean_object* v_nextLevelIdx_1877_; lean_object* v_levelArgs_1878_; lean_object* v_newLocalDecls_1879_; lean_object* v_newLocalDeclsForMVars_1880_; lean_object* v_newLetDecls_1881_; lean_object* v_nextExprIdx_1882_; lean_object* v_exprMVarArgs_1883_; lean_object* v_exprFVarArgs_1884_; lean_object* v_toProcess_1885_; lean_object* v___x_1887_; uint8_t v_isShared_1888_; uint8_t v_isSharedCheck_1897_; 
v___x_1873_ = lean_st_ref_take(v_a_1856_);
v_visitedLevel_1874_ = lean_ctor_get(v___x_1873_, 0);
v_visitedExpr_1875_ = lean_ctor_get(v___x_1873_, 1);
v_levelParams_1876_ = lean_ctor_get(v___x_1873_, 2);
v_nextLevelIdx_1877_ = lean_ctor_get(v___x_1873_, 3);
v_levelArgs_1878_ = lean_ctor_get(v___x_1873_, 4);
v_newLocalDecls_1879_ = lean_ctor_get(v___x_1873_, 5);
v_newLocalDeclsForMVars_1880_ = lean_ctor_get(v___x_1873_, 6);
v_newLetDecls_1881_ = lean_ctor_get(v___x_1873_, 7);
v_nextExprIdx_1882_ = lean_ctor_get(v___x_1873_, 8);
v_exprMVarArgs_1883_ = lean_ctor_get(v___x_1873_, 9);
v_exprFVarArgs_1884_ = lean_ctor_get(v___x_1873_, 10);
v_toProcess_1885_ = lean_ctor_get(v___x_1873_, 11);
v_isSharedCheck_1897_ = !lean_is_exclusive(v___x_1873_);
if (v_isSharedCheck_1897_ == 0)
{
v___x_1887_ = v___x_1873_;
v_isShared_1888_ = v_isSharedCheck_1897_;
goto v_resetjp_1886_;
}
else
{
lean_inc(v_toProcess_1885_);
lean_inc(v_exprFVarArgs_1884_);
lean_inc(v_exprMVarArgs_1883_);
lean_inc(v_nextExprIdx_1882_);
lean_inc(v_newLetDecls_1881_);
lean_inc(v_newLocalDeclsForMVars_1880_);
lean_inc(v_newLocalDecls_1879_);
lean_inc(v_levelArgs_1878_);
lean_inc(v_nextLevelIdx_1877_);
lean_inc(v_levelParams_1876_);
lean_inc(v_visitedExpr_1875_);
lean_inc(v_visitedLevel_1874_);
lean_dec(v___x_1873_);
v___x_1887_ = lean_box(0);
v_isShared_1888_ = v_isSharedCheck_1897_;
goto v_resetjp_1886_;
}
v_resetjp_1886_:
{
lean_object* v___x_1889_; lean_object* v___x_1891_; 
lean_inc(v_a_1869_);
v___x_1889_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1___redArg(v_visitedExpr_1875_, v_a_1863_, v_a_1869_);
if (v_isShared_1888_ == 0)
{
lean_ctor_set(v___x_1887_, 1, v___x_1889_);
v___x_1891_ = v___x_1887_;
goto v_reusejp_1890_;
}
else
{
lean_object* v_reuseFailAlloc_1896_; 
v_reuseFailAlloc_1896_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_1896_, 0, v_visitedLevel_1874_);
lean_ctor_set(v_reuseFailAlloc_1896_, 1, v___x_1889_);
lean_ctor_set(v_reuseFailAlloc_1896_, 2, v_levelParams_1876_);
lean_ctor_set(v_reuseFailAlloc_1896_, 3, v_nextLevelIdx_1877_);
lean_ctor_set(v_reuseFailAlloc_1896_, 4, v_levelArgs_1878_);
lean_ctor_set(v_reuseFailAlloc_1896_, 5, v_newLocalDecls_1879_);
lean_ctor_set(v_reuseFailAlloc_1896_, 6, v_newLocalDeclsForMVars_1880_);
lean_ctor_set(v_reuseFailAlloc_1896_, 7, v_newLetDecls_1881_);
lean_ctor_set(v_reuseFailAlloc_1896_, 8, v_nextExprIdx_1882_);
lean_ctor_set(v_reuseFailAlloc_1896_, 9, v_exprMVarArgs_1883_);
lean_ctor_set(v_reuseFailAlloc_1896_, 10, v_exprFVarArgs_1884_);
lean_ctor_set(v_reuseFailAlloc_1896_, 11, v_toProcess_1885_);
v___x_1891_ = v_reuseFailAlloc_1896_;
goto v_reusejp_1890_;
}
v_reusejp_1890_:
{
lean_object* v___x_1892_; lean_object* v___x_1894_; 
v___x_1892_ = lean_st_ref_set(v_a_1856_, v___x_1891_);
if (v_isShared_1872_ == 0)
{
v___x_1894_ = v___x_1871_;
goto v_reusejp_1893_;
}
else
{
lean_object* v_reuseFailAlloc_1895_; 
v_reuseFailAlloc_1895_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1895_, 0, v_a_1869_);
v___x_1894_ = v_reuseFailAlloc_1895_;
goto v_reusejp_1893_;
}
v_reusejp_1893_:
{
return v___x_1894_;
}
}
}
}
}
else
{
lean_dec(v_a_1863_);
return v___x_1868_;
}
}
else
{
lean_object* v_val_1899_; lean_object* v___x_1901_; uint8_t v_isShared_1902_; uint8_t v_isSharedCheck_1906_; 
lean_dec(v_a_1863_);
v_val_1899_ = lean_ctor_get(v___x_1867_, 0);
v_isSharedCheck_1906_ = !lean_is_exclusive(v___x_1867_);
if (v_isSharedCheck_1906_ == 0)
{
v___x_1901_ = v___x_1867_;
v_isShared_1902_ = v_isSharedCheck_1906_;
goto v_resetjp_1900_;
}
else
{
lean_inc(v_val_1899_);
lean_dec(v___x_1867_);
v___x_1901_ = lean_box(0);
v_isShared_1902_ = v_isSharedCheck_1906_;
goto v_resetjp_1900_;
}
v_resetjp_1900_:
{
lean_object* v___x_1904_; 
if (v_isShared_1902_ == 0)
{
lean_ctor_set_tag(v___x_1901_, 0);
v___x_1904_ = v___x_1901_;
goto v_reusejp_1903_;
}
else
{
lean_object* v_reuseFailAlloc_1905_; 
v_reuseFailAlloc_1905_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1905_, 0, v_val_1899_);
v___x_1904_ = v_reuseFailAlloc_1905_;
goto v_reusejp_1903_;
}
v_reusejp_1903_:
{
return v___x_1904_;
}
}
}
}
}
else
{
return v___x_1862_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectExpr___boxed(lean_object* v_e_1910_, lean_object* v_a_1911_, lean_object* v_a_1912_, lean_object* v_a_1913_, lean_object* v_a_1914_, lean_object* v_a_1915_, lean_object* v_a_1916_, lean_object* v_a_1917_){
_start:
{
uint8_t v_a_boxed_1918_; lean_object* v_res_1919_; 
v_a_boxed_1918_ = lean_unbox(v_a_1911_);
v_res_1919_ = l_Lean_Meta_Closure_collectExpr(v_e_1910_, v_a_boxed_1918_, v_a_1912_, v_a_1913_, v_a_1914_, v_a_1915_, v_a_1916_);
lean_dec(v_a_1916_);
lean_dec_ref(v_a_1915_);
lean_dec(v_a_1914_);
lean_dec_ref(v_a_1913_);
lean_dec(v_a_1912_);
return v_res_1919_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pickNextToProcessAux(lean_object* v_lctx_1920_, lean_object* v_i_1921_, lean_object* v_toProcess_1922_, lean_object* v_elem_1923_){
_start:
{
lean_object* v___x_1924_; uint8_t v___x_1925_; 
v___x_1924_ = lean_array_get_size(v_toProcess_1922_);
v___x_1925_ = lean_nat_dec_lt(v_i_1921_, v___x_1924_);
if (v___x_1925_ == 0)
{
lean_object* v___x_1926_; 
lean_dec(v_i_1921_);
lean_dec_ref(v_lctx_1920_);
v___x_1926_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1926_, 0, v_elem_1923_);
lean_ctor_set(v___x_1926_, 1, v_toProcess_1922_);
return v___x_1926_;
}
else
{
lean_object* v_fvarId_1927_; lean_object* v_elem_x27_1928_; lean_object* v_fvarId_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; uint8_t v___x_1934_; 
v_fvarId_1927_ = lean_ctor_get(v_elem_1923_, 0);
v_elem_x27_1928_ = lean_array_fget_borrowed(v_toProcess_1922_, v_i_1921_);
v_fvarId_1929_ = lean_ctor_get(v_elem_x27_1928_, 0);
lean_inc(v_fvarId_1927_);
lean_inc_ref_n(v_lctx_1920_, 2);
v___x_1930_ = l_Lean_LocalContext_get_x21(v_lctx_1920_, v_fvarId_1927_);
v___x_1931_ = l_Lean_LocalDecl_index(v___x_1930_);
lean_dec_ref(v___x_1930_);
lean_inc(v_fvarId_1929_);
v___x_1932_ = l_Lean_LocalContext_get_x21(v_lctx_1920_, v_fvarId_1929_);
v___x_1933_ = l_Lean_LocalDecl_index(v___x_1932_);
lean_dec_ref(v___x_1932_);
v___x_1934_ = lean_nat_dec_lt(v___x_1931_, v___x_1933_);
lean_dec(v___x_1933_);
lean_dec(v___x_1931_);
if (v___x_1934_ == 0)
{
lean_object* v___x_1935_; lean_object* v___x_1936_; 
v___x_1935_ = lean_unsigned_to_nat(1u);
v___x_1936_ = lean_nat_add(v_i_1921_, v___x_1935_);
lean_dec(v_i_1921_);
v_i_1921_ = v___x_1936_;
goto _start;
}
else
{
lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; 
lean_inc(v_elem_x27_1928_);
v___x_1938_ = lean_unsigned_to_nat(1u);
v___x_1939_ = lean_nat_add(v_i_1921_, v___x_1938_);
v___x_1940_ = lean_array_fset(v_toProcess_1922_, v_i_1921_, v_elem_1923_);
lean_dec(v_i_1921_);
v_i_1921_ = v___x_1939_;
v_toProcess_1922_ = v___x_1940_;
v_elem_1923_ = v_elem_x27_1928_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pickNextToProcess_x3f___redArg(lean_object* v_a_1942_, lean_object* v_a_1943_){
_start:
{
lean_object* v___x_1945_; lean_object* v_toProcess_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; uint8_t v___x_1949_; 
v___x_1945_ = lean_st_ref_get(v_a_1942_);
v_toProcess_1946_ = lean_ctor_get(v___x_1945_, 11);
lean_inc_ref(v_toProcess_1946_);
lean_dec(v___x_1945_);
v___x_1947_ = lean_array_get_size(v_toProcess_1946_);
lean_dec_ref(v_toProcess_1946_);
v___x_1948_ = lean_unsigned_to_nat(0u);
v___x_1949_ = lean_nat_dec_eq(v___x_1947_, v___x_1948_);
if (v___x_1949_ == 0)
{
lean_object* v___x_1950_; lean_object* v_lctx_1951_; lean_object* v_visitedLevel_1952_; lean_object* v_visitedExpr_1953_; lean_object* v_levelParams_1954_; lean_object* v_nextLevelIdx_1955_; lean_object* v_levelArgs_1956_; lean_object* v_newLocalDecls_1957_; lean_object* v_newLocalDeclsForMVars_1958_; lean_object* v_newLetDecls_1959_; lean_object* v_nextExprIdx_1960_; lean_object* v_exprMVarArgs_1961_; lean_object* v_exprFVarArgs_1962_; lean_object* v_toProcess_1963_; lean_object* v___x_1965_; uint8_t v_isShared_1966_; uint8_t v_isSharedCheck_1982_; 
v___x_1950_ = lean_st_ref_take(v_a_1942_);
v_lctx_1951_ = lean_ctor_get(v_a_1943_, 2);
v_visitedLevel_1952_ = lean_ctor_get(v___x_1950_, 0);
v_visitedExpr_1953_ = lean_ctor_get(v___x_1950_, 1);
v_levelParams_1954_ = lean_ctor_get(v___x_1950_, 2);
v_nextLevelIdx_1955_ = lean_ctor_get(v___x_1950_, 3);
v_levelArgs_1956_ = lean_ctor_get(v___x_1950_, 4);
v_newLocalDecls_1957_ = lean_ctor_get(v___x_1950_, 5);
v_newLocalDeclsForMVars_1958_ = lean_ctor_get(v___x_1950_, 6);
v_newLetDecls_1959_ = lean_ctor_get(v___x_1950_, 7);
v_nextExprIdx_1960_ = lean_ctor_get(v___x_1950_, 8);
v_exprMVarArgs_1961_ = lean_ctor_get(v___x_1950_, 9);
v_exprFVarArgs_1962_ = lean_ctor_get(v___x_1950_, 10);
v_toProcess_1963_ = lean_ctor_get(v___x_1950_, 11);
v_isSharedCheck_1982_ = !lean_is_exclusive(v___x_1950_);
if (v_isSharedCheck_1982_ == 0)
{
v___x_1965_ = v___x_1950_;
v_isShared_1966_ = v_isSharedCheck_1982_;
goto v_resetjp_1964_;
}
else
{
lean_inc(v_toProcess_1963_);
lean_inc(v_exprFVarArgs_1962_);
lean_inc(v_exprMVarArgs_1961_);
lean_inc(v_nextExprIdx_1960_);
lean_inc(v_newLetDecls_1959_);
lean_inc(v_newLocalDeclsForMVars_1958_);
lean_inc(v_newLocalDecls_1957_);
lean_inc(v_levelArgs_1956_);
lean_inc(v_nextLevelIdx_1955_);
lean_inc(v_levelParams_1954_);
lean_inc(v_visitedExpr_1953_);
lean_inc(v_visitedLevel_1952_);
lean_dec(v___x_1950_);
v___x_1965_ = lean_box(0);
v_isShared_1966_ = v_isSharedCheck_1982_;
goto v_resetjp_1964_;
}
v_resetjp_1964_:
{
lean_object* v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; lean_object* v___x_1972_; lean_object* v___x_1973_; lean_object* v_fst_1974_; lean_object* v_snd_1975_; lean_object* v___x_1977_; 
v___x_1967_ = ((lean_object*)(l_Lean_Meta_Closure_instInhabitedToProcessElement_default));
v___x_1968_ = lean_array_get_size(v_toProcess_1963_);
v___x_1969_ = lean_unsigned_to_nat(1u);
v___x_1970_ = lean_nat_sub(v___x_1968_, v___x_1969_);
v___x_1971_ = lean_array_get(v___x_1967_, v_toProcess_1963_, v___x_1970_);
lean_dec(v___x_1970_);
v___x_1972_ = lean_array_pop(v_toProcess_1963_);
lean_inc_ref(v_lctx_1951_);
v___x_1973_ = l_Lean_Meta_Closure_pickNextToProcessAux(v_lctx_1951_, v___x_1948_, v___x_1972_, v___x_1971_);
v_fst_1974_ = lean_ctor_get(v___x_1973_, 0);
lean_inc(v_fst_1974_);
v_snd_1975_ = lean_ctor_get(v___x_1973_, 1);
lean_inc(v_snd_1975_);
lean_dec_ref(v___x_1973_);
if (v_isShared_1966_ == 0)
{
lean_ctor_set(v___x_1965_, 11, v_snd_1975_);
v___x_1977_ = v___x_1965_;
goto v_reusejp_1976_;
}
else
{
lean_object* v_reuseFailAlloc_1981_; 
v_reuseFailAlloc_1981_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_1981_, 0, v_visitedLevel_1952_);
lean_ctor_set(v_reuseFailAlloc_1981_, 1, v_visitedExpr_1953_);
lean_ctor_set(v_reuseFailAlloc_1981_, 2, v_levelParams_1954_);
lean_ctor_set(v_reuseFailAlloc_1981_, 3, v_nextLevelIdx_1955_);
lean_ctor_set(v_reuseFailAlloc_1981_, 4, v_levelArgs_1956_);
lean_ctor_set(v_reuseFailAlloc_1981_, 5, v_newLocalDecls_1957_);
lean_ctor_set(v_reuseFailAlloc_1981_, 6, v_newLocalDeclsForMVars_1958_);
lean_ctor_set(v_reuseFailAlloc_1981_, 7, v_newLetDecls_1959_);
lean_ctor_set(v_reuseFailAlloc_1981_, 8, v_nextExprIdx_1960_);
lean_ctor_set(v_reuseFailAlloc_1981_, 9, v_exprMVarArgs_1961_);
lean_ctor_set(v_reuseFailAlloc_1981_, 10, v_exprFVarArgs_1962_);
lean_ctor_set(v_reuseFailAlloc_1981_, 11, v_snd_1975_);
v___x_1977_ = v_reuseFailAlloc_1981_;
goto v_reusejp_1976_;
}
v_reusejp_1976_:
{
lean_object* v___x_1978_; lean_object* v___x_1979_; lean_object* v___x_1980_; 
v___x_1978_ = lean_st_ref_set(v_a_1942_, v___x_1977_);
v___x_1979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1979_, 0, v_fst_1974_);
v___x_1980_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1980_, 0, v___x_1979_);
return v___x_1980_;
}
}
}
else
{
lean_object* v___x_1983_; lean_object* v___x_1984_; 
v___x_1983_ = lean_box(0);
v___x_1984_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1984_, 0, v___x_1983_);
return v___x_1984_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pickNextToProcess_x3f___redArg___boxed(lean_object* v_a_1985_, lean_object* v_a_1986_, lean_object* v_a_1987_){
_start:
{
lean_object* v_res_1988_; 
v_res_1988_ = l_Lean_Meta_Closure_pickNextToProcess_x3f___redArg(v_a_1985_, v_a_1986_);
lean_dec_ref(v_a_1986_);
lean_dec(v_a_1985_);
return v_res_1988_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pickNextToProcess_x3f(uint8_t v_a_1989_, lean_object* v_a_1990_, lean_object* v_a_1991_, lean_object* v_a_1992_, lean_object* v_a_1993_, lean_object* v_a_1994_){
_start:
{
lean_object* v___x_1996_; 
v___x_1996_ = l_Lean_Meta_Closure_pickNextToProcess_x3f___redArg(v_a_1990_, v_a_1991_);
return v___x_1996_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pickNextToProcess_x3f___boxed(lean_object* v_a_1997_, lean_object* v_a_1998_, lean_object* v_a_1999_, lean_object* v_a_2000_, lean_object* v_a_2001_, lean_object* v_a_2002_, lean_object* v_a_2003_){
_start:
{
uint8_t v_a_boxed_2004_; lean_object* v_res_2005_; 
v_a_boxed_2004_ = lean_unbox(v_a_1997_);
v_res_2005_ = l_Lean_Meta_Closure_pickNextToProcess_x3f(v_a_boxed_2004_, v_a_1998_, v_a_1999_, v_a_2000_, v_a_2001_, v_a_2002_);
lean_dec(v_a_2002_);
lean_dec_ref(v_a_2001_);
lean_dec(v_a_2000_);
lean_dec_ref(v_a_1999_);
lean_dec(v_a_1998_);
return v_res_2005_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushFVarArg___redArg(lean_object* v_e_2006_, lean_object* v_a_2007_){
_start:
{
lean_object* v___x_2009_; lean_object* v_visitedLevel_2010_; lean_object* v_visitedExpr_2011_; lean_object* v_levelParams_2012_; lean_object* v_nextLevelIdx_2013_; lean_object* v_levelArgs_2014_; lean_object* v_newLocalDecls_2015_; lean_object* v_newLocalDeclsForMVars_2016_; lean_object* v_newLetDecls_2017_; lean_object* v_nextExprIdx_2018_; lean_object* v_exprMVarArgs_2019_; lean_object* v_exprFVarArgs_2020_; lean_object* v_toProcess_2021_; lean_object* v___x_2023_; uint8_t v_isShared_2024_; uint8_t v_isSharedCheck_2032_; 
v___x_2009_ = lean_st_ref_take(v_a_2007_);
v_visitedLevel_2010_ = lean_ctor_get(v___x_2009_, 0);
v_visitedExpr_2011_ = lean_ctor_get(v___x_2009_, 1);
v_levelParams_2012_ = lean_ctor_get(v___x_2009_, 2);
v_nextLevelIdx_2013_ = lean_ctor_get(v___x_2009_, 3);
v_levelArgs_2014_ = lean_ctor_get(v___x_2009_, 4);
v_newLocalDecls_2015_ = lean_ctor_get(v___x_2009_, 5);
v_newLocalDeclsForMVars_2016_ = lean_ctor_get(v___x_2009_, 6);
v_newLetDecls_2017_ = lean_ctor_get(v___x_2009_, 7);
v_nextExprIdx_2018_ = lean_ctor_get(v___x_2009_, 8);
v_exprMVarArgs_2019_ = lean_ctor_get(v___x_2009_, 9);
v_exprFVarArgs_2020_ = lean_ctor_get(v___x_2009_, 10);
v_toProcess_2021_ = lean_ctor_get(v___x_2009_, 11);
v_isSharedCheck_2032_ = !lean_is_exclusive(v___x_2009_);
if (v_isSharedCheck_2032_ == 0)
{
v___x_2023_ = v___x_2009_;
v_isShared_2024_ = v_isSharedCheck_2032_;
goto v_resetjp_2022_;
}
else
{
lean_inc(v_toProcess_2021_);
lean_inc(v_exprFVarArgs_2020_);
lean_inc(v_exprMVarArgs_2019_);
lean_inc(v_nextExprIdx_2018_);
lean_inc(v_newLetDecls_2017_);
lean_inc(v_newLocalDeclsForMVars_2016_);
lean_inc(v_newLocalDecls_2015_);
lean_inc(v_levelArgs_2014_);
lean_inc(v_nextLevelIdx_2013_);
lean_inc(v_levelParams_2012_);
lean_inc(v_visitedExpr_2011_);
lean_inc(v_visitedLevel_2010_);
lean_dec(v___x_2009_);
v___x_2023_ = lean_box(0);
v_isShared_2024_ = v_isSharedCheck_2032_;
goto v_resetjp_2022_;
}
v_resetjp_2022_:
{
lean_object* v___x_2025_; lean_object* v___x_2027_; 
v___x_2025_ = lean_array_push(v_exprFVarArgs_2020_, v_e_2006_);
if (v_isShared_2024_ == 0)
{
lean_ctor_set(v___x_2023_, 10, v___x_2025_);
v___x_2027_ = v___x_2023_;
goto v_reusejp_2026_;
}
else
{
lean_object* v_reuseFailAlloc_2031_; 
v_reuseFailAlloc_2031_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_2031_, 0, v_visitedLevel_2010_);
lean_ctor_set(v_reuseFailAlloc_2031_, 1, v_visitedExpr_2011_);
lean_ctor_set(v_reuseFailAlloc_2031_, 2, v_levelParams_2012_);
lean_ctor_set(v_reuseFailAlloc_2031_, 3, v_nextLevelIdx_2013_);
lean_ctor_set(v_reuseFailAlloc_2031_, 4, v_levelArgs_2014_);
lean_ctor_set(v_reuseFailAlloc_2031_, 5, v_newLocalDecls_2015_);
lean_ctor_set(v_reuseFailAlloc_2031_, 6, v_newLocalDeclsForMVars_2016_);
lean_ctor_set(v_reuseFailAlloc_2031_, 7, v_newLetDecls_2017_);
lean_ctor_set(v_reuseFailAlloc_2031_, 8, v_nextExprIdx_2018_);
lean_ctor_set(v_reuseFailAlloc_2031_, 9, v_exprMVarArgs_2019_);
lean_ctor_set(v_reuseFailAlloc_2031_, 10, v___x_2025_);
lean_ctor_set(v_reuseFailAlloc_2031_, 11, v_toProcess_2021_);
v___x_2027_ = v_reuseFailAlloc_2031_;
goto v_reusejp_2026_;
}
v_reusejp_2026_:
{
lean_object* v___x_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; 
v___x_2028_ = lean_st_ref_set(v_a_2007_, v___x_2027_);
v___x_2029_ = lean_box(0);
v___x_2030_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2030_, 0, v___x_2029_);
return v___x_2030_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushFVarArg___redArg___boxed(lean_object* v_e_2033_, lean_object* v_a_2034_, lean_object* v_a_2035_){
_start:
{
lean_object* v_res_2036_; 
v_res_2036_ = l_Lean_Meta_Closure_pushFVarArg___redArg(v_e_2033_, v_a_2034_);
lean_dec(v_a_2034_);
return v_res_2036_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushFVarArg(lean_object* v_e_2037_, uint8_t v_a_2038_, lean_object* v_a_2039_, lean_object* v_a_2040_, lean_object* v_a_2041_, lean_object* v_a_2042_, lean_object* v_a_2043_){
_start:
{
lean_object* v___x_2045_; 
v___x_2045_ = l_Lean_Meta_Closure_pushFVarArg___redArg(v_e_2037_, v_a_2039_);
return v___x_2045_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushFVarArg___boxed(lean_object* v_e_2046_, lean_object* v_a_2047_, lean_object* v_a_2048_, lean_object* v_a_2049_, lean_object* v_a_2050_, lean_object* v_a_2051_, lean_object* v_a_2052_, lean_object* v_a_2053_){
_start:
{
uint8_t v_a_boxed_2054_; lean_object* v_res_2055_; 
v_a_boxed_2054_ = lean_unbox(v_a_2047_);
v_res_2055_ = l_Lean_Meta_Closure_pushFVarArg(v_e_2046_, v_a_boxed_2054_, v_a_2048_, v_a_2049_, v_a_2050_, v_a_2051_, v_a_2052_);
lean_dec(v_a_2052_);
lean_dec_ref(v_a_2051_);
lean_dec(v_a_2050_);
lean_dec_ref(v_a_2049_);
lean_dec(v_a_2048_);
return v_res_2055_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushLocalDecl(lean_object* v_newFVarId_2056_, lean_object* v_userName_2057_, lean_object* v_type_2058_, uint8_t v_bi_2059_, uint8_t v_a_2060_, lean_object* v_a_2061_, lean_object* v_a_2062_, lean_object* v_a_2063_, lean_object* v_a_2064_, lean_object* v_a_2065_){
_start:
{
lean_object* v___x_2067_; 
v___x_2067_ = l_Lean_Meta_Closure_collectExpr(v_type_2058_, v_a_2060_, v_a_2061_, v_a_2062_, v_a_2063_, v_a_2064_, v_a_2065_);
if (lean_obj_tag(v___x_2067_) == 0)
{
lean_object* v_a_2068_; lean_object* v___x_2070_; uint8_t v_isShared_2071_; uint8_t v_isSharedCheck_2101_; 
v_a_2068_ = lean_ctor_get(v___x_2067_, 0);
v_isSharedCheck_2101_ = !lean_is_exclusive(v___x_2067_);
if (v_isSharedCheck_2101_ == 0)
{
v___x_2070_ = v___x_2067_;
v_isShared_2071_ = v_isSharedCheck_2101_;
goto v_resetjp_2069_;
}
else
{
lean_inc(v_a_2068_);
lean_dec(v___x_2067_);
v___x_2070_ = lean_box(0);
v_isShared_2071_ = v_isSharedCheck_2101_;
goto v_resetjp_2069_;
}
v_resetjp_2069_:
{
lean_object* v___x_2072_; lean_object* v_visitedLevel_2073_; lean_object* v_visitedExpr_2074_; lean_object* v_levelParams_2075_; lean_object* v_nextLevelIdx_2076_; lean_object* v_levelArgs_2077_; lean_object* v_newLocalDecls_2078_; lean_object* v_newLocalDeclsForMVars_2079_; lean_object* v_newLetDecls_2080_; lean_object* v_nextExprIdx_2081_; lean_object* v_exprMVarArgs_2082_; lean_object* v_exprFVarArgs_2083_; lean_object* v_toProcess_2084_; lean_object* v___x_2086_; uint8_t v_isShared_2087_; uint8_t v_isSharedCheck_2100_; 
v___x_2072_ = lean_st_ref_take(v_a_2061_);
v_visitedLevel_2073_ = lean_ctor_get(v___x_2072_, 0);
v_visitedExpr_2074_ = lean_ctor_get(v___x_2072_, 1);
v_levelParams_2075_ = lean_ctor_get(v___x_2072_, 2);
v_nextLevelIdx_2076_ = lean_ctor_get(v___x_2072_, 3);
v_levelArgs_2077_ = lean_ctor_get(v___x_2072_, 4);
v_newLocalDecls_2078_ = lean_ctor_get(v___x_2072_, 5);
v_newLocalDeclsForMVars_2079_ = lean_ctor_get(v___x_2072_, 6);
v_newLetDecls_2080_ = lean_ctor_get(v___x_2072_, 7);
v_nextExprIdx_2081_ = lean_ctor_get(v___x_2072_, 8);
v_exprMVarArgs_2082_ = lean_ctor_get(v___x_2072_, 9);
v_exprFVarArgs_2083_ = lean_ctor_get(v___x_2072_, 10);
v_toProcess_2084_ = lean_ctor_get(v___x_2072_, 11);
v_isSharedCheck_2100_ = !lean_is_exclusive(v___x_2072_);
if (v_isSharedCheck_2100_ == 0)
{
v___x_2086_ = v___x_2072_;
v_isShared_2087_ = v_isSharedCheck_2100_;
goto v_resetjp_2085_;
}
else
{
lean_inc(v_toProcess_2084_);
lean_inc(v_exprFVarArgs_2083_);
lean_inc(v_exprMVarArgs_2082_);
lean_inc(v_nextExprIdx_2081_);
lean_inc(v_newLetDecls_2080_);
lean_inc(v_newLocalDeclsForMVars_2079_);
lean_inc(v_newLocalDecls_2078_);
lean_inc(v_levelArgs_2077_);
lean_inc(v_nextLevelIdx_2076_);
lean_inc(v_levelParams_2075_);
lean_inc(v_visitedExpr_2074_);
lean_inc(v_visitedLevel_2073_);
lean_dec(v___x_2072_);
v___x_2086_ = lean_box(0);
v_isShared_2087_ = v_isSharedCheck_2100_;
goto v_resetjp_2085_;
}
v_resetjp_2085_:
{
lean_object* v___x_2088_; uint8_t v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v___x_2093_; 
v___x_2088_ = lean_unsigned_to_nat(0u);
v___x_2089_ = 0;
v___x_2090_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2090_, 0, v___x_2088_);
lean_ctor_set(v___x_2090_, 1, v_newFVarId_2056_);
lean_ctor_set(v___x_2090_, 2, v_userName_2057_);
lean_ctor_set(v___x_2090_, 3, v_a_2068_);
lean_ctor_set_uint8(v___x_2090_, sizeof(void*)*4, v_bi_2059_);
lean_ctor_set_uint8(v___x_2090_, sizeof(void*)*4 + 1, v___x_2089_);
v___x_2091_ = lean_array_push(v_newLocalDecls_2078_, v___x_2090_);
if (v_isShared_2087_ == 0)
{
lean_ctor_set(v___x_2086_, 5, v___x_2091_);
v___x_2093_ = v___x_2086_;
goto v_reusejp_2092_;
}
else
{
lean_object* v_reuseFailAlloc_2099_; 
v_reuseFailAlloc_2099_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_2099_, 0, v_visitedLevel_2073_);
lean_ctor_set(v_reuseFailAlloc_2099_, 1, v_visitedExpr_2074_);
lean_ctor_set(v_reuseFailAlloc_2099_, 2, v_levelParams_2075_);
lean_ctor_set(v_reuseFailAlloc_2099_, 3, v_nextLevelIdx_2076_);
lean_ctor_set(v_reuseFailAlloc_2099_, 4, v_levelArgs_2077_);
lean_ctor_set(v_reuseFailAlloc_2099_, 5, v___x_2091_);
lean_ctor_set(v_reuseFailAlloc_2099_, 6, v_newLocalDeclsForMVars_2079_);
lean_ctor_set(v_reuseFailAlloc_2099_, 7, v_newLetDecls_2080_);
lean_ctor_set(v_reuseFailAlloc_2099_, 8, v_nextExprIdx_2081_);
lean_ctor_set(v_reuseFailAlloc_2099_, 9, v_exprMVarArgs_2082_);
lean_ctor_set(v_reuseFailAlloc_2099_, 10, v_exprFVarArgs_2083_);
lean_ctor_set(v_reuseFailAlloc_2099_, 11, v_toProcess_2084_);
v___x_2093_ = v_reuseFailAlloc_2099_;
goto v_reusejp_2092_;
}
v_reusejp_2092_:
{
lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2097_; 
v___x_2094_ = lean_st_ref_set(v_a_2061_, v___x_2093_);
v___x_2095_ = lean_box(0);
if (v_isShared_2071_ == 0)
{
lean_ctor_set(v___x_2070_, 0, v___x_2095_);
v___x_2097_ = v___x_2070_;
goto v_reusejp_2096_;
}
else
{
lean_object* v_reuseFailAlloc_2098_; 
v_reuseFailAlloc_2098_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2098_, 0, v___x_2095_);
v___x_2097_ = v_reuseFailAlloc_2098_;
goto v_reusejp_2096_;
}
v_reusejp_2096_:
{
return v___x_2097_;
}
}
}
}
}
else
{
lean_object* v_a_2102_; lean_object* v___x_2104_; uint8_t v_isShared_2105_; uint8_t v_isSharedCheck_2109_; 
lean_dec(v_userName_2057_);
lean_dec(v_newFVarId_2056_);
v_a_2102_ = lean_ctor_get(v___x_2067_, 0);
v_isSharedCheck_2109_ = !lean_is_exclusive(v___x_2067_);
if (v_isSharedCheck_2109_ == 0)
{
v___x_2104_ = v___x_2067_;
v_isShared_2105_ = v_isSharedCheck_2109_;
goto v_resetjp_2103_;
}
else
{
lean_inc(v_a_2102_);
lean_dec(v___x_2067_);
v___x_2104_ = lean_box(0);
v_isShared_2105_ = v_isSharedCheck_2109_;
goto v_resetjp_2103_;
}
v_resetjp_2103_:
{
lean_object* v___x_2107_; 
if (v_isShared_2105_ == 0)
{
v___x_2107_ = v___x_2104_;
goto v_reusejp_2106_;
}
else
{
lean_object* v_reuseFailAlloc_2108_; 
v_reuseFailAlloc_2108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2108_, 0, v_a_2102_);
v___x_2107_ = v_reuseFailAlloc_2108_;
goto v_reusejp_2106_;
}
v_reusejp_2106_:
{
return v___x_2107_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushLocalDecl___boxed(lean_object* v_newFVarId_2110_, lean_object* v_userName_2111_, lean_object* v_type_2112_, lean_object* v_bi_2113_, lean_object* v_a_2114_, lean_object* v_a_2115_, lean_object* v_a_2116_, lean_object* v_a_2117_, lean_object* v_a_2118_, lean_object* v_a_2119_, lean_object* v_a_2120_){
_start:
{
uint8_t v_bi_boxed_2121_; uint8_t v_a_boxed_2122_; lean_object* v_res_2123_; 
v_bi_boxed_2121_ = lean_unbox(v_bi_2113_);
v_a_boxed_2122_ = lean_unbox(v_a_2114_);
v_res_2123_ = l_Lean_Meta_Closure_pushLocalDecl(v_newFVarId_2110_, v_userName_2111_, v_type_2112_, v_bi_boxed_2121_, v_a_boxed_2122_, v_a_2115_, v_a_2116_, v_a_2117_, v_a_2118_, v_a_2119_);
lean_dec(v_a_2119_);
lean_dec_ref(v_a_2118_);
lean_dec(v_a_2117_);
lean_dec_ref(v_a_2116_);
lean_dec(v_a_2115_);
return v_res_2123_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Closure_process_spec__0___redArg(lean_object* v_k_2124_, lean_object* v_t_2125_){
_start:
{
if (lean_obj_tag(v_t_2125_) == 0)
{
lean_object* v_k_2126_; lean_object* v_l_2127_; lean_object* v_r_2128_; uint8_t v___x_2129_; 
v_k_2126_ = lean_ctor_get(v_t_2125_, 1);
v_l_2127_ = lean_ctor_get(v_t_2125_, 3);
v_r_2128_ = lean_ctor_get(v_t_2125_, 4);
v___x_2129_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_2124_, v_k_2126_);
switch(v___x_2129_)
{
case 0:
{
v_t_2125_ = v_l_2127_;
goto _start;
}
case 1:
{
uint8_t v___x_2131_; 
v___x_2131_ = 1;
return v___x_2131_;
}
default: 
{
v_t_2125_ = v_r_2128_;
goto _start;
}
}
}
else
{
uint8_t v___x_2133_; 
v___x_2133_ = 0;
return v___x_2133_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Closure_process_spec__0___redArg___boxed(lean_object* v_k_2134_, lean_object* v_t_2135_){
_start:
{
uint8_t v_res_2136_; lean_object* v_r_2137_; 
v_res_2136_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Closure_process_spec__0___redArg(v_k_2134_, v_t_2135_);
lean_dec(v_t_2135_);
lean_dec(v_k_2134_);
v_r_2137_ = lean_box(v_res_2136_);
return v_r_2137_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Closure_process_spec__1(lean_object* v_newFVarId_2138_, lean_object* v_a_2139_, size_t v_sz_2140_, size_t v_i_2141_, lean_object* v_bs_2142_){
_start:
{
uint8_t v___x_2143_; 
v___x_2143_ = lean_usize_dec_lt(v_i_2141_, v_sz_2140_);
if (v___x_2143_ == 0)
{
lean_dec(v_newFVarId_2138_);
return v_bs_2142_;
}
else
{
lean_object* v_v_2144_; lean_object* v___x_2145_; lean_object* v_bs_x27_2146_; lean_object* v___x_2147_; size_t v___x_2148_; size_t v___x_2149_; lean_object* v___x_2150_; 
v_v_2144_ = lean_array_uget(v_bs_2142_, v_i_2141_);
v___x_2145_ = lean_unsigned_to_nat(0u);
v_bs_x27_2146_ = lean_array_uset(v_bs_2142_, v_i_2141_, v___x_2145_);
lean_inc(v_newFVarId_2138_);
v___x_2147_ = l_Lean_LocalDecl_replaceFVarId(v_newFVarId_2138_, v_a_2139_, v_v_2144_);
v___x_2148_ = ((size_t)1ULL);
v___x_2149_ = lean_usize_add(v_i_2141_, v___x_2148_);
v___x_2150_ = lean_array_uset(v_bs_x27_2146_, v_i_2141_, v___x_2147_);
v_i_2141_ = v___x_2149_;
v_bs_2142_ = v___x_2150_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Closure_process_spec__1___boxed(lean_object* v_newFVarId_2152_, lean_object* v_a_2153_, lean_object* v_sz_2154_, lean_object* v_i_2155_, lean_object* v_bs_2156_){
_start:
{
size_t v_sz_boxed_2157_; size_t v_i_boxed_2158_; lean_object* v_res_2159_; 
v_sz_boxed_2157_ = lean_unbox_usize(v_sz_2154_);
lean_dec(v_sz_2154_);
v_i_boxed_2158_ = lean_unbox_usize(v_i_2155_);
lean_dec(v_i_2155_);
v_res_2159_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Closure_process_spec__1(v_newFVarId_2152_, v_a_2153_, v_sz_boxed_2157_, v_i_boxed_2158_, v_bs_2156_);
lean_dec_ref(v_a_2153_);
return v_res_2159_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_process(uint8_t v_a_2160_, lean_object* v_a_2161_, lean_object* v_a_2162_, lean_object* v_a_2163_, lean_object* v_a_2164_, lean_object* v_a_2165_){
_start:
{
lean_object* v___x_2167_; 
v___x_2167_ = l_Lean_Meta_Closure_pickNextToProcess_x3f___redArg(v_a_2161_, v_a_2162_);
if (lean_obj_tag(v___x_2167_) == 0)
{
lean_object* v_a_2168_; lean_object* v___x_2170_; uint8_t v_isShared_2171_; uint8_t v_isSharedCheck_2295_; 
v_a_2168_ = lean_ctor_get(v___x_2167_, 0);
v_isSharedCheck_2295_ = !lean_is_exclusive(v___x_2167_);
if (v_isSharedCheck_2295_ == 0)
{
v___x_2170_ = v___x_2167_;
v_isShared_2171_ = v_isSharedCheck_2295_;
goto v_resetjp_2169_;
}
else
{
lean_inc(v_a_2168_);
lean_dec(v___x_2167_);
v___x_2170_ = lean_box(0);
v_isShared_2171_ = v_isSharedCheck_2295_;
goto v_resetjp_2169_;
}
v_resetjp_2169_:
{
if (lean_obj_tag(v_a_2168_) == 0)
{
lean_object* v___x_2172_; lean_object* v___x_2174_; 
v___x_2172_ = lean_box(0);
if (v_isShared_2171_ == 0)
{
lean_ctor_set(v___x_2170_, 0, v___x_2172_);
v___x_2174_ = v___x_2170_;
goto v_reusejp_2173_;
}
else
{
lean_object* v_reuseFailAlloc_2175_; 
v_reuseFailAlloc_2175_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2175_, 0, v___x_2172_);
v___x_2174_ = v_reuseFailAlloc_2175_;
goto v_reusejp_2173_;
}
v_reusejp_2173_:
{
return v___x_2174_;
}
}
else
{
lean_object* v_val_2176_; lean_object* v_fvarId_2177_; lean_object* v_newFVarId_2178_; lean_object* v___x_2179_; 
lean_del_object(v___x_2170_);
v_val_2176_ = lean_ctor_get(v_a_2168_, 0);
lean_inc(v_val_2176_);
lean_dec_ref(v_a_2168_);
v_fvarId_2177_ = lean_ctor_get(v_val_2176_, 0);
lean_inc_n(v_fvarId_2177_, 2);
v_newFVarId_2178_ = lean_ctor_get(v_val_2176_, 1);
lean_inc(v_newFVarId_2178_);
lean_dec(v_val_2176_);
v___x_2179_ = l_Lean_FVarId_getDecl___redArg(v_fvarId_2177_, v_a_2162_, v_a_2164_, v_a_2165_);
if (lean_obj_tag(v___x_2179_) == 0)
{
lean_object* v_a_2180_; 
v_a_2180_ = lean_ctor_get(v___x_2179_, 0);
lean_inc(v_a_2180_);
lean_dec_ref(v___x_2179_);
if (lean_obj_tag(v_a_2180_) == 0)
{
lean_object* v_userName_2181_; lean_object* v_type_2182_; uint8_t v_bi_2183_; lean_object* v___x_2184_; 
v_userName_2181_ = lean_ctor_get(v_a_2180_, 2);
lean_inc(v_userName_2181_);
v_type_2182_ = lean_ctor_get(v_a_2180_, 3);
lean_inc_ref(v_type_2182_);
v_bi_2183_ = lean_ctor_get_uint8(v_a_2180_, sizeof(void*)*4);
lean_dec_ref(v_a_2180_);
v___x_2184_ = l_Lean_Meta_Closure_pushLocalDecl(v_newFVarId_2178_, v_userName_2181_, v_type_2182_, v_bi_2183_, v_a_2160_, v_a_2161_, v_a_2162_, v_a_2163_, v_a_2164_, v_a_2165_);
if (lean_obj_tag(v___x_2184_) == 0)
{
lean_object* v___x_2185_; lean_object* v___x_2186_; 
lean_dec_ref(v___x_2184_);
v___x_2185_ = l_Lean_mkFVar(v_fvarId_2177_);
v___x_2186_ = l_Lean_Meta_Closure_pushFVarArg___redArg(v___x_2185_, v_a_2161_);
if (lean_obj_tag(v___x_2186_) == 0)
{
lean_dec_ref(v___x_2186_);
goto _start;
}
else
{
return v___x_2186_;
}
}
else
{
lean_dec(v_fvarId_2177_);
return v___x_2184_;
}
}
else
{
lean_object* v_userName_2188_; lean_object* v_type_2189_; lean_object* v_value_2190_; uint8_t v_nondep_2191_; lean_object* v___x_2193_; uint8_t v_isShared_2194_; uint8_t v_isSharedCheck_2284_; 
v_userName_2188_ = lean_ctor_get(v_a_2180_, 2);
v_type_2189_ = lean_ctor_get(v_a_2180_, 3);
v_value_2190_ = lean_ctor_get(v_a_2180_, 4);
v_nondep_2191_ = lean_ctor_get_uint8(v_a_2180_, sizeof(void*)*5);
v_isSharedCheck_2284_ = !lean_is_exclusive(v_a_2180_);
if (v_isSharedCheck_2284_ == 0)
{
lean_object* v_unused_2285_; lean_object* v_unused_2286_; 
v_unused_2285_ = lean_ctor_get(v_a_2180_, 1);
lean_dec(v_unused_2285_);
v_unused_2286_ = lean_ctor_get(v_a_2180_, 0);
lean_dec(v_unused_2286_);
v___x_2193_ = v_a_2180_;
v_isShared_2194_ = v_isSharedCheck_2284_;
goto v_resetjp_2192_;
}
else
{
lean_inc(v_value_2190_);
lean_inc(v_type_2189_);
lean_inc(v_userName_2188_);
lean_dec(v_a_2180_);
v___x_2193_ = lean_box(0);
v_isShared_2194_ = v_isSharedCheck_2284_;
goto v_resetjp_2192_;
}
v_resetjp_2192_:
{
lean_object* v___x_2195_; 
v___x_2195_ = l_Lean_Meta_getZetaDeltaFVarIds___redArg(v_a_2163_);
if (lean_obj_tag(v___x_2195_) == 0)
{
lean_object* v_a_2196_; 
v_a_2196_ = lean_ctor_get(v___x_2195_, 0);
lean_inc(v_a_2196_);
lean_dec_ref(v___x_2195_);
if (v_nondep_2191_ == 0)
{
uint8_t v___x_2203_; 
v___x_2203_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Closure_process_spec__0___redArg(v_fvarId_2177_, v_a_2196_);
lean_dec(v_a_2196_);
if (v___x_2203_ == 0)
{
lean_del_object(v___x_2193_);
lean_dec_ref(v_value_2190_);
goto v___jp_2197_;
}
else
{
lean_object* v___x_2204_; 
lean_dec(v_fvarId_2177_);
v___x_2204_ = l_Lean_Meta_Closure_collectExpr(v_type_2189_, v_a_2160_, v_a_2161_, v_a_2162_, v_a_2163_, v_a_2164_, v_a_2165_);
if (lean_obj_tag(v___x_2204_) == 0)
{
lean_object* v_a_2205_; lean_object* v___x_2206_; 
v_a_2205_ = lean_ctor_get(v___x_2204_, 0);
lean_inc(v_a_2205_);
lean_dec_ref(v___x_2204_);
v___x_2206_ = l_Lean_Meta_Closure_collectExpr(v_value_2190_, v_a_2160_, v_a_2161_, v_a_2162_, v_a_2163_, v_a_2164_, v_a_2165_);
if (lean_obj_tag(v___x_2206_) == 0)
{
lean_object* v_a_2207_; lean_object* v___x_2208_; lean_object* v_visitedLevel_2209_; lean_object* v_visitedExpr_2210_; lean_object* v_levelParams_2211_; lean_object* v_nextLevelIdx_2212_; lean_object* v_levelArgs_2213_; lean_object* v_newLocalDecls_2214_; lean_object* v_newLocalDeclsForMVars_2215_; lean_object* v_newLetDecls_2216_; lean_object* v_nextExprIdx_2217_; lean_object* v_exprMVarArgs_2218_; lean_object* v_exprFVarArgs_2219_; lean_object* v_toProcess_2220_; lean_object* v___x_2222_; uint8_t v_isShared_2223_; uint8_t v_isSharedCheck_2259_; 
v_a_2207_ = lean_ctor_get(v___x_2206_, 0);
lean_inc(v_a_2207_);
lean_dec_ref(v___x_2206_);
v___x_2208_ = lean_st_ref_take(v_a_2161_);
v_visitedLevel_2209_ = lean_ctor_get(v___x_2208_, 0);
v_visitedExpr_2210_ = lean_ctor_get(v___x_2208_, 1);
v_levelParams_2211_ = lean_ctor_get(v___x_2208_, 2);
v_nextLevelIdx_2212_ = lean_ctor_get(v___x_2208_, 3);
v_levelArgs_2213_ = lean_ctor_get(v___x_2208_, 4);
v_newLocalDecls_2214_ = lean_ctor_get(v___x_2208_, 5);
v_newLocalDeclsForMVars_2215_ = lean_ctor_get(v___x_2208_, 6);
v_newLetDecls_2216_ = lean_ctor_get(v___x_2208_, 7);
v_nextExprIdx_2217_ = lean_ctor_get(v___x_2208_, 8);
v_exprMVarArgs_2218_ = lean_ctor_get(v___x_2208_, 9);
v_exprFVarArgs_2219_ = lean_ctor_get(v___x_2208_, 10);
v_toProcess_2220_ = lean_ctor_get(v___x_2208_, 11);
v_isSharedCheck_2259_ = !lean_is_exclusive(v___x_2208_);
if (v_isSharedCheck_2259_ == 0)
{
v___x_2222_ = v___x_2208_;
v_isShared_2223_ = v_isSharedCheck_2259_;
goto v_resetjp_2221_;
}
else
{
lean_inc(v_toProcess_2220_);
lean_inc(v_exprFVarArgs_2219_);
lean_inc(v_exprMVarArgs_2218_);
lean_inc(v_nextExprIdx_2217_);
lean_inc(v_newLetDecls_2216_);
lean_inc(v_newLocalDeclsForMVars_2215_);
lean_inc(v_newLocalDecls_2214_);
lean_inc(v_levelArgs_2213_);
lean_inc(v_nextLevelIdx_2212_);
lean_inc(v_levelParams_2211_);
lean_inc(v_visitedExpr_2210_);
lean_inc(v_visitedLevel_2209_);
lean_dec(v___x_2208_);
v___x_2222_ = lean_box(0);
v_isShared_2223_ = v_isSharedCheck_2259_;
goto v_resetjp_2221_;
}
v_resetjp_2221_:
{
lean_object* v___x_2224_; uint8_t v___x_2225_; lean_object* v___x_2227_; 
v___x_2224_ = lean_unsigned_to_nat(0u);
v___x_2225_ = 0;
lean_inc(v_a_2207_);
lean_inc(v_newFVarId_2178_);
if (v_isShared_2194_ == 0)
{
lean_ctor_set(v___x_2193_, 4, v_a_2207_);
lean_ctor_set(v___x_2193_, 3, v_a_2205_);
lean_ctor_set(v___x_2193_, 1, v_newFVarId_2178_);
lean_ctor_set(v___x_2193_, 0, v___x_2224_);
v___x_2227_ = v___x_2193_;
goto v_reusejp_2226_;
}
else
{
lean_object* v_reuseFailAlloc_2258_; 
v_reuseFailAlloc_2258_ = lean_alloc_ctor(1, 5, 2);
lean_ctor_set(v_reuseFailAlloc_2258_, 0, v___x_2224_);
lean_ctor_set(v_reuseFailAlloc_2258_, 1, v_newFVarId_2178_);
lean_ctor_set(v_reuseFailAlloc_2258_, 2, v_userName_2188_);
lean_ctor_set(v_reuseFailAlloc_2258_, 3, v_a_2205_);
lean_ctor_set(v_reuseFailAlloc_2258_, 4, v_a_2207_);
lean_ctor_set_uint8(v_reuseFailAlloc_2258_, sizeof(void*)*5, v_nondep_2191_);
v___x_2227_ = v_reuseFailAlloc_2258_;
goto v_reusejp_2226_;
}
v_reusejp_2226_:
{
lean_object* v___x_2228_; lean_object* v___x_2230_; 
lean_ctor_set_uint8(v___x_2227_, sizeof(void*)*5 + 1, v___x_2225_);
v___x_2228_ = lean_array_push(v_newLetDecls_2216_, v___x_2227_);
if (v_isShared_2223_ == 0)
{
lean_ctor_set(v___x_2222_, 7, v___x_2228_);
v___x_2230_ = v___x_2222_;
goto v_reusejp_2229_;
}
else
{
lean_object* v_reuseFailAlloc_2257_; 
v_reuseFailAlloc_2257_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_2257_, 0, v_visitedLevel_2209_);
lean_ctor_set(v_reuseFailAlloc_2257_, 1, v_visitedExpr_2210_);
lean_ctor_set(v_reuseFailAlloc_2257_, 2, v_levelParams_2211_);
lean_ctor_set(v_reuseFailAlloc_2257_, 3, v_nextLevelIdx_2212_);
lean_ctor_set(v_reuseFailAlloc_2257_, 4, v_levelArgs_2213_);
lean_ctor_set(v_reuseFailAlloc_2257_, 5, v_newLocalDecls_2214_);
lean_ctor_set(v_reuseFailAlloc_2257_, 6, v_newLocalDeclsForMVars_2215_);
lean_ctor_set(v_reuseFailAlloc_2257_, 7, v___x_2228_);
lean_ctor_set(v_reuseFailAlloc_2257_, 8, v_nextExprIdx_2217_);
lean_ctor_set(v_reuseFailAlloc_2257_, 9, v_exprMVarArgs_2218_);
lean_ctor_set(v_reuseFailAlloc_2257_, 10, v_exprFVarArgs_2219_);
lean_ctor_set(v_reuseFailAlloc_2257_, 11, v_toProcess_2220_);
v___x_2230_ = v_reuseFailAlloc_2257_;
goto v_reusejp_2229_;
}
v_reusejp_2229_:
{
lean_object* v___x_2231_; lean_object* v___x_2232_; lean_object* v_visitedLevel_2233_; lean_object* v_visitedExpr_2234_; lean_object* v_levelParams_2235_; lean_object* v_nextLevelIdx_2236_; lean_object* v_levelArgs_2237_; lean_object* v_newLocalDecls_2238_; lean_object* v_newLocalDeclsForMVars_2239_; lean_object* v_newLetDecls_2240_; lean_object* v_nextExprIdx_2241_; lean_object* v_exprMVarArgs_2242_; lean_object* v_exprFVarArgs_2243_; lean_object* v_toProcess_2244_; lean_object* v___x_2246_; uint8_t v_isShared_2247_; uint8_t v_isSharedCheck_2256_; 
v___x_2231_ = lean_st_ref_set(v_a_2161_, v___x_2230_);
v___x_2232_ = lean_st_ref_take(v_a_2161_);
v_visitedLevel_2233_ = lean_ctor_get(v___x_2232_, 0);
v_visitedExpr_2234_ = lean_ctor_get(v___x_2232_, 1);
v_levelParams_2235_ = lean_ctor_get(v___x_2232_, 2);
v_nextLevelIdx_2236_ = lean_ctor_get(v___x_2232_, 3);
v_levelArgs_2237_ = lean_ctor_get(v___x_2232_, 4);
v_newLocalDecls_2238_ = lean_ctor_get(v___x_2232_, 5);
v_newLocalDeclsForMVars_2239_ = lean_ctor_get(v___x_2232_, 6);
v_newLetDecls_2240_ = lean_ctor_get(v___x_2232_, 7);
v_nextExprIdx_2241_ = lean_ctor_get(v___x_2232_, 8);
v_exprMVarArgs_2242_ = lean_ctor_get(v___x_2232_, 9);
v_exprFVarArgs_2243_ = lean_ctor_get(v___x_2232_, 10);
v_toProcess_2244_ = lean_ctor_get(v___x_2232_, 11);
v_isSharedCheck_2256_ = !lean_is_exclusive(v___x_2232_);
if (v_isSharedCheck_2256_ == 0)
{
v___x_2246_ = v___x_2232_;
v_isShared_2247_ = v_isSharedCheck_2256_;
goto v_resetjp_2245_;
}
else
{
lean_inc(v_toProcess_2244_);
lean_inc(v_exprFVarArgs_2243_);
lean_inc(v_exprMVarArgs_2242_);
lean_inc(v_nextExprIdx_2241_);
lean_inc(v_newLetDecls_2240_);
lean_inc(v_newLocalDeclsForMVars_2239_);
lean_inc(v_newLocalDecls_2238_);
lean_inc(v_levelArgs_2237_);
lean_inc(v_nextLevelIdx_2236_);
lean_inc(v_levelParams_2235_);
lean_inc(v_visitedExpr_2234_);
lean_inc(v_visitedLevel_2233_);
lean_dec(v___x_2232_);
v___x_2246_ = lean_box(0);
v_isShared_2247_ = v_isSharedCheck_2256_;
goto v_resetjp_2245_;
}
v_resetjp_2245_:
{
size_t v_sz_2248_; size_t v___x_2249_; lean_object* v___x_2250_; lean_object* v___x_2252_; 
v_sz_2248_ = lean_array_size(v_newLocalDecls_2238_);
v___x_2249_ = ((size_t)0ULL);
v___x_2250_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Closure_process_spec__1(v_newFVarId_2178_, v_a_2207_, v_sz_2248_, v___x_2249_, v_newLocalDecls_2238_);
lean_dec(v_a_2207_);
if (v_isShared_2247_ == 0)
{
lean_ctor_set(v___x_2246_, 5, v___x_2250_);
v___x_2252_ = v___x_2246_;
goto v_reusejp_2251_;
}
else
{
lean_object* v_reuseFailAlloc_2255_; 
v_reuseFailAlloc_2255_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_2255_, 0, v_visitedLevel_2233_);
lean_ctor_set(v_reuseFailAlloc_2255_, 1, v_visitedExpr_2234_);
lean_ctor_set(v_reuseFailAlloc_2255_, 2, v_levelParams_2235_);
lean_ctor_set(v_reuseFailAlloc_2255_, 3, v_nextLevelIdx_2236_);
lean_ctor_set(v_reuseFailAlloc_2255_, 4, v_levelArgs_2237_);
lean_ctor_set(v_reuseFailAlloc_2255_, 5, v___x_2250_);
lean_ctor_set(v_reuseFailAlloc_2255_, 6, v_newLocalDeclsForMVars_2239_);
lean_ctor_set(v_reuseFailAlloc_2255_, 7, v_newLetDecls_2240_);
lean_ctor_set(v_reuseFailAlloc_2255_, 8, v_nextExprIdx_2241_);
lean_ctor_set(v_reuseFailAlloc_2255_, 9, v_exprMVarArgs_2242_);
lean_ctor_set(v_reuseFailAlloc_2255_, 10, v_exprFVarArgs_2243_);
lean_ctor_set(v_reuseFailAlloc_2255_, 11, v_toProcess_2244_);
v___x_2252_ = v_reuseFailAlloc_2255_;
goto v_reusejp_2251_;
}
v_reusejp_2251_:
{
lean_object* v___x_2253_; 
v___x_2253_ = lean_st_ref_set(v_a_2161_, v___x_2252_);
goto _start;
}
}
}
}
}
}
else
{
lean_object* v_a_2260_; lean_object* v___x_2262_; uint8_t v_isShared_2263_; uint8_t v_isSharedCheck_2267_; 
lean_dec(v_a_2205_);
lean_del_object(v___x_2193_);
lean_dec(v_userName_2188_);
lean_dec(v_newFVarId_2178_);
v_a_2260_ = lean_ctor_get(v___x_2206_, 0);
v_isSharedCheck_2267_ = !lean_is_exclusive(v___x_2206_);
if (v_isSharedCheck_2267_ == 0)
{
v___x_2262_ = v___x_2206_;
v_isShared_2263_ = v_isSharedCheck_2267_;
goto v_resetjp_2261_;
}
else
{
lean_inc(v_a_2260_);
lean_dec(v___x_2206_);
v___x_2262_ = lean_box(0);
v_isShared_2263_ = v_isSharedCheck_2267_;
goto v_resetjp_2261_;
}
v_resetjp_2261_:
{
lean_object* v___x_2265_; 
if (v_isShared_2263_ == 0)
{
v___x_2265_ = v___x_2262_;
goto v_reusejp_2264_;
}
else
{
lean_object* v_reuseFailAlloc_2266_; 
v_reuseFailAlloc_2266_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2266_, 0, v_a_2260_);
v___x_2265_ = v_reuseFailAlloc_2266_;
goto v_reusejp_2264_;
}
v_reusejp_2264_:
{
return v___x_2265_;
}
}
}
}
else
{
lean_object* v_a_2268_; lean_object* v___x_2270_; uint8_t v_isShared_2271_; uint8_t v_isSharedCheck_2275_; 
lean_del_object(v___x_2193_);
lean_dec_ref(v_value_2190_);
lean_dec(v_userName_2188_);
lean_dec(v_newFVarId_2178_);
v_a_2268_ = lean_ctor_get(v___x_2204_, 0);
v_isSharedCheck_2275_ = !lean_is_exclusive(v___x_2204_);
if (v_isSharedCheck_2275_ == 0)
{
v___x_2270_ = v___x_2204_;
v_isShared_2271_ = v_isSharedCheck_2275_;
goto v_resetjp_2269_;
}
else
{
lean_inc(v_a_2268_);
lean_dec(v___x_2204_);
v___x_2270_ = lean_box(0);
v_isShared_2271_ = v_isSharedCheck_2275_;
goto v_resetjp_2269_;
}
v_resetjp_2269_:
{
lean_object* v___x_2273_; 
if (v_isShared_2271_ == 0)
{
v___x_2273_ = v___x_2270_;
goto v_reusejp_2272_;
}
else
{
lean_object* v_reuseFailAlloc_2274_; 
v_reuseFailAlloc_2274_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2274_, 0, v_a_2268_);
v___x_2273_ = v_reuseFailAlloc_2274_;
goto v_reusejp_2272_;
}
v_reusejp_2272_:
{
return v___x_2273_;
}
}
}
}
}
else
{
lean_dec(v_a_2196_);
lean_del_object(v___x_2193_);
lean_dec_ref(v_value_2190_);
goto v___jp_2197_;
}
v___jp_2197_:
{
uint8_t v___x_2198_; lean_object* v___x_2199_; 
v___x_2198_ = 0;
v___x_2199_ = l_Lean_Meta_Closure_pushLocalDecl(v_newFVarId_2178_, v_userName_2188_, v_type_2189_, v___x_2198_, v_a_2160_, v_a_2161_, v_a_2162_, v_a_2163_, v_a_2164_, v_a_2165_);
if (lean_obj_tag(v___x_2199_) == 0)
{
lean_object* v___x_2200_; lean_object* v___x_2201_; 
lean_dec_ref(v___x_2199_);
v___x_2200_ = l_Lean_mkFVar(v_fvarId_2177_);
v___x_2201_ = l_Lean_Meta_Closure_pushFVarArg___redArg(v___x_2200_, v_a_2161_);
if (lean_obj_tag(v___x_2201_) == 0)
{
lean_dec_ref(v___x_2201_);
goto _start;
}
else
{
return v___x_2201_;
}
}
else
{
lean_dec(v_fvarId_2177_);
return v___x_2199_;
}
}
}
else
{
lean_object* v_a_2276_; lean_object* v___x_2278_; uint8_t v_isShared_2279_; uint8_t v_isSharedCheck_2283_; 
lean_del_object(v___x_2193_);
lean_dec_ref(v_value_2190_);
lean_dec_ref(v_type_2189_);
lean_dec(v_userName_2188_);
lean_dec(v_newFVarId_2178_);
lean_dec(v_fvarId_2177_);
v_a_2276_ = lean_ctor_get(v___x_2195_, 0);
v_isSharedCheck_2283_ = !lean_is_exclusive(v___x_2195_);
if (v_isSharedCheck_2283_ == 0)
{
v___x_2278_ = v___x_2195_;
v_isShared_2279_ = v_isSharedCheck_2283_;
goto v_resetjp_2277_;
}
else
{
lean_inc(v_a_2276_);
lean_dec(v___x_2195_);
v___x_2278_ = lean_box(0);
v_isShared_2279_ = v_isSharedCheck_2283_;
goto v_resetjp_2277_;
}
v_resetjp_2277_:
{
lean_object* v___x_2281_; 
if (v_isShared_2279_ == 0)
{
v___x_2281_ = v___x_2278_;
goto v_reusejp_2280_;
}
else
{
lean_object* v_reuseFailAlloc_2282_; 
v_reuseFailAlloc_2282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2282_, 0, v_a_2276_);
v___x_2281_ = v_reuseFailAlloc_2282_;
goto v_reusejp_2280_;
}
v_reusejp_2280_:
{
return v___x_2281_;
}
}
}
}
}
}
else
{
lean_object* v_a_2287_; lean_object* v___x_2289_; uint8_t v_isShared_2290_; uint8_t v_isSharedCheck_2294_; 
lean_dec(v_newFVarId_2178_);
lean_dec(v_fvarId_2177_);
v_a_2287_ = lean_ctor_get(v___x_2179_, 0);
v_isSharedCheck_2294_ = !lean_is_exclusive(v___x_2179_);
if (v_isSharedCheck_2294_ == 0)
{
v___x_2289_ = v___x_2179_;
v_isShared_2290_ = v_isSharedCheck_2294_;
goto v_resetjp_2288_;
}
else
{
lean_inc(v_a_2287_);
lean_dec(v___x_2179_);
v___x_2289_ = lean_box(0);
v_isShared_2290_ = v_isSharedCheck_2294_;
goto v_resetjp_2288_;
}
v_resetjp_2288_:
{
lean_object* v___x_2292_; 
if (v_isShared_2290_ == 0)
{
v___x_2292_ = v___x_2289_;
goto v_reusejp_2291_;
}
else
{
lean_object* v_reuseFailAlloc_2293_; 
v_reuseFailAlloc_2293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2293_, 0, v_a_2287_);
v___x_2292_ = v_reuseFailAlloc_2293_;
goto v_reusejp_2291_;
}
v_reusejp_2291_:
{
return v___x_2292_;
}
}
}
}
}
}
else
{
lean_object* v_a_2296_; lean_object* v___x_2298_; uint8_t v_isShared_2299_; uint8_t v_isSharedCheck_2303_; 
v_a_2296_ = lean_ctor_get(v___x_2167_, 0);
v_isSharedCheck_2303_ = !lean_is_exclusive(v___x_2167_);
if (v_isSharedCheck_2303_ == 0)
{
v___x_2298_ = v___x_2167_;
v_isShared_2299_ = v_isSharedCheck_2303_;
goto v_resetjp_2297_;
}
else
{
lean_inc(v_a_2296_);
lean_dec(v___x_2167_);
v___x_2298_ = lean_box(0);
v_isShared_2299_ = v_isSharedCheck_2303_;
goto v_resetjp_2297_;
}
v_resetjp_2297_:
{
lean_object* v___x_2301_; 
if (v_isShared_2299_ == 0)
{
v___x_2301_ = v___x_2298_;
goto v_reusejp_2300_;
}
else
{
lean_object* v_reuseFailAlloc_2302_; 
v_reuseFailAlloc_2302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2302_, 0, v_a_2296_);
v___x_2301_ = v_reuseFailAlloc_2302_;
goto v_reusejp_2300_;
}
v_reusejp_2300_:
{
return v___x_2301_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_process___boxed(lean_object* v_a_2304_, lean_object* v_a_2305_, lean_object* v_a_2306_, lean_object* v_a_2307_, lean_object* v_a_2308_, lean_object* v_a_2309_, lean_object* v_a_2310_){
_start:
{
uint8_t v_a_boxed_2311_; lean_object* v_res_2312_; 
v_a_boxed_2311_ = lean_unbox(v_a_2304_);
v_res_2312_ = l_Lean_Meta_Closure_process(v_a_boxed_2311_, v_a_2305_, v_a_2306_, v_a_2307_, v_a_2308_, v_a_2309_);
lean_dec(v_a_2309_);
lean_dec_ref(v_a_2308_);
lean_dec(v_a_2307_);
lean_dec_ref(v_a_2306_);
lean_dec(v_a_2305_);
return v_res_2312_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Closure_process_spec__0(lean_object* v_00_u03b2_2313_, lean_object* v_k_2314_, lean_object* v_t_2315_){
_start:
{
uint8_t v___x_2316_; 
v___x_2316_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Closure_process_spec__0___redArg(v_k_2314_, v_t_2315_);
return v___x_2316_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Closure_process_spec__0___boxed(lean_object* v_00_u03b2_2317_, lean_object* v_k_2318_, lean_object* v_t_2319_){
_start:
{
uint8_t v_res_2320_; lean_object* v_r_2321_; 
v_res_2320_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Closure_process_spec__0(v_00_u03b2_2317_, v_k_2318_, v_t_2319_);
lean_dec(v_t_2319_);
lean_dec(v_k_2318_);
v_r_2321_ = lean_box(v_res_2320_);
return v_r_2321_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkBinding___lam__0(lean_object* v_decls_2322_, lean_object* v_xs_2323_, uint8_t v_isLambda_2324_, lean_object* v_i_2325_, lean_object* v_x_2326_, lean_object* v_b_2327_){
_start:
{
lean_object* v_decl_2328_; 
v_decl_2328_ = lean_array_fget_borrowed(v_decls_2322_, v_i_2325_);
if (lean_obj_tag(v_decl_2328_) == 0)
{
lean_object* v_userName_2329_; lean_object* v_type_2330_; uint8_t v_bi_2331_; lean_object* v_ty_2332_; 
v_userName_2329_ = lean_ctor_get(v_decl_2328_, 2);
v_type_2330_ = lean_ctor_get(v_decl_2328_, 3);
v_bi_2331_ = lean_ctor_get_uint8(v_decl_2328_, sizeof(void*)*4);
v_ty_2332_ = lean_expr_abstract_range(v_type_2330_, v_i_2325_, v_xs_2323_);
if (v_isLambda_2324_ == 0)
{
lean_object* v___x_2333_; 
lean_inc(v_userName_2329_);
v___x_2333_ = l_Lean_mkForall(v_userName_2329_, v_bi_2331_, v_ty_2332_, v_b_2327_);
return v___x_2333_;
}
else
{
lean_object* v___x_2334_; 
lean_inc(v_userName_2329_);
v___x_2334_ = l_Lean_mkLambda(v_userName_2329_, v_bi_2331_, v_ty_2332_, v_b_2327_);
return v___x_2334_;
}
}
else
{
lean_object* v_userName_2335_; lean_object* v_type_2336_; lean_object* v_value_2337_; uint8_t v_nondep_2338_; lean_object* v___x_2339_; uint8_t v___x_2340_; 
v_userName_2335_ = lean_ctor_get(v_decl_2328_, 2);
v_type_2336_ = lean_ctor_get(v_decl_2328_, 3);
v_value_2337_ = lean_ctor_get(v_decl_2328_, 4);
v_nondep_2338_ = lean_ctor_get_uint8(v_decl_2328_, sizeof(void*)*5);
v___x_2339_ = lean_unsigned_to_nat(0u);
v___x_2340_ = lean_expr_has_loose_bvar(v_b_2327_, v___x_2339_);
if (v___x_2340_ == 0)
{
lean_object* v___x_2341_; lean_object* v___x_2342_; 
v___x_2341_ = lean_unsigned_to_nat(1u);
v___x_2342_ = lean_expr_lower_loose_bvars(v_b_2327_, v___x_2341_, v___x_2341_);
lean_dec_ref(v_b_2327_);
return v___x_2342_;
}
else
{
lean_object* v_ty_2343_; lean_object* v_val_2344_; lean_object* v___x_2345_; 
v_ty_2343_ = lean_expr_abstract_range(v_type_2336_, v_i_2325_, v_xs_2323_);
v_val_2344_ = lean_expr_abstract_range(v_value_2337_, v_i_2325_, v_xs_2323_);
lean_inc(v_userName_2335_);
v___x_2345_ = l_Lean_Expr_letE___override(v_userName_2335_, v_ty_2343_, v_val_2344_, v_b_2327_, v_nondep_2338_);
return v___x_2345_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkBinding___lam__0___boxed(lean_object* v_decls_2346_, lean_object* v_xs_2347_, lean_object* v_isLambda_2348_, lean_object* v_i_2349_, lean_object* v_x_2350_, lean_object* v_b_2351_){
_start:
{
uint8_t v_isLambda_boxed_2352_; lean_object* v_res_2353_; 
v_isLambda_boxed_2352_ = lean_unbox(v_isLambda_2348_);
v_res_2353_ = l_Lean_Meta_Closure_mkBinding___lam__0(v_decls_2346_, v_xs_2347_, v_isLambda_boxed_2352_, v_i_2349_, v_x_2350_, v_b_2351_);
lean_dec(v_i_2349_);
lean_dec_ref(v_xs_2347_);
lean_dec_ref(v_decls_2346_);
return v_res_2353_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkBinding(uint8_t v_isLambda_2374_, lean_object* v_decls_2375_, lean_object* v_b_2376_){
_start:
{
lean_object* v___f_2377_; lean_object* v___x_2378_; size_t v_sz_2379_; size_t v___x_2380_; lean_object* v_xs_2381_; lean_object* v___x_2382_; lean_object* v___f_2383_; lean_object* v_b_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; 
v___f_2377_ = ((lean_object*)(l_Lean_Meta_Closure_mkBinding___closed__0));
v___x_2378_ = ((lean_object*)(l_Lean_Meta_Closure_mkBinding___closed__10));
v_sz_2379_ = lean_array_size(v_decls_2375_);
v___x_2380_ = ((size_t)0ULL);
lean_inc_ref_n(v_decls_2375_, 2);
v_xs_2381_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2378_, v___f_2377_, v_sz_2379_, v___x_2380_, v_decls_2375_);
v___x_2382_ = lean_box(v_isLambda_2374_);
lean_inc(v_xs_2381_);
v___f_2383_ = lean_alloc_closure((void*)(l_Lean_Meta_Closure_mkBinding___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2383_, 0, v_decls_2375_);
lean_closure_set(v___f_2383_, 1, v_xs_2381_);
lean_closure_set(v___f_2383_, 2, v___x_2382_);
v_b_2384_ = lean_expr_abstract(v_b_2376_, v_xs_2381_);
lean_dec(v_xs_2381_);
v___x_2385_ = lean_array_get_size(v_decls_2375_);
lean_dec_ref(v_decls_2375_);
v___x_2386_ = l_Nat_foldRev___redArg(v___x_2385_, v___f_2383_, v_b_2384_);
return v___x_2386_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkBinding___boxed(lean_object* v_isLambda_2387_, lean_object* v_decls_2388_, lean_object* v_b_2389_){
_start:
{
uint8_t v_isLambda_boxed_2390_; lean_object* v_res_2391_; 
v_isLambda_boxed_2390_ = lean_unbox(v_isLambda_2387_);
v_res_2391_ = l_Lean_Meta_Closure_mkBinding(v_isLambda_boxed_2390_, v_decls_2388_, v_b_2389_);
lean_dec_ref(v_b_2389_);
return v_res_2391_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Closure_mkLambda_spec__0(size_t v_sz_2392_, size_t v_i_2393_, lean_object* v_bs_2394_){
_start:
{
uint8_t v___x_2395_; 
v___x_2395_ = lean_usize_dec_lt(v_i_2393_, v_sz_2392_);
if (v___x_2395_ == 0)
{
return v_bs_2394_;
}
else
{
lean_object* v_v_2396_; lean_object* v___x_2397_; lean_object* v_bs_x27_2398_; lean_object* v___x_2399_; size_t v___x_2400_; size_t v___x_2401_; lean_object* v___x_2402_; 
v_v_2396_ = lean_array_uget(v_bs_2394_, v_i_2393_);
v___x_2397_ = lean_unsigned_to_nat(0u);
v_bs_x27_2398_ = lean_array_uset(v_bs_2394_, v_i_2393_, v___x_2397_);
v___x_2399_ = l_Lean_LocalDecl_toExpr(v_v_2396_);
v___x_2400_ = ((size_t)1ULL);
v___x_2401_ = lean_usize_add(v_i_2393_, v___x_2400_);
v___x_2402_ = lean_array_uset(v_bs_x27_2398_, v_i_2393_, v___x_2399_);
v_i_2393_ = v___x_2401_;
v_bs_2394_ = v___x_2402_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Closure_mkLambda_spec__0___boxed(lean_object* v_sz_2404_, lean_object* v_i_2405_, lean_object* v_bs_2406_){
_start:
{
size_t v_sz_boxed_2407_; size_t v_i_boxed_2408_; lean_object* v_res_2409_; 
v_sz_boxed_2407_ = lean_unbox_usize(v_sz_2404_);
lean_dec(v_sz_2404_);
v_i_boxed_2408_ = lean_unbox_usize(v_i_2405_);
lean_dec(v_i_2405_);
v_res_2409_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Closure_mkLambda_spec__0(v_sz_boxed_2407_, v_i_boxed_2408_, v_bs_2406_);
return v_res_2409_;
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_Meta_Closure_mkLambda_spec__1_spec__1(lean_object* v_decls_2410_, lean_object* v_xs_2411_, lean_object* v_x_2412_, lean_object* v_x_2413_){
_start:
{
lean_object* v_zero_2414_; uint8_t v_isZero_2415_; 
v_zero_2414_ = lean_unsigned_to_nat(0u);
v_isZero_2415_ = lean_nat_dec_eq(v_x_2412_, v_zero_2414_);
if (v_isZero_2415_ == 1)
{
lean_dec(v_x_2412_);
return v_x_2413_;
}
else
{
lean_object* v_one_2416_; lean_object* v_n_2417_; lean_object* v_decl_2418_; 
v_one_2416_ = lean_unsigned_to_nat(1u);
v_n_2417_ = lean_nat_sub(v_x_2412_, v_one_2416_);
lean_dec(v_x_2412_);
v_decl_2418_ = lean_array_fget_borrowed(v_decls_2410_, v_n_2417_);
if (lean_obj_tag(v_decl_2418_) == 0)
{
lean_object* v_userName_2419_; lean_object* v_type_2420_; uint8_t v_bi_2421_; lean_object* v_ty_2422_; lean_object* v___x_2423_; 
v_userName_2419_ = lean_ctor_get(v_decl_2418_, 2);
v_type_2420_ = lean_ctor_get(v_decl_2418_, 3);
v_bi_2421_ = lean_ctor_get_uint8(v_decl_2418_, sizeof(void*)*4);
v_ty_2422_ = lean_expr_abstract_range(v_type_2420_, v_n_2417_, v_xs_2411_);
lean_inc(v_userName_2419_);
v___x_2423_ = l_Lean_mkLambda(v_userName_2419_, v_bi_2421_, v_ty_2422_, v_x_2413_);
v_x_2412_ = v_n_2417_;
v_x_2413_ = v___x_2423_;
goto _start;
}
else
{
lean_object* v_userName_2425_; lean_object* v_type_2426_; lean_object* v_value_2427_; uint8_t v_nondep_2428_; uint8_t v___x_2429_; 
v_userName_2425_ = lean_ctor_get(v_decl_2418_, 2);
v_type_2426_ = lean_ctor_get(v_decl_2418_, 3);
v_value_2427_ = lean_ctor_get(v_decl_2418_, 4);
v_nondep_2428_ = lean_ctor_get_uint8(v_decl_2418_, sizeof(void*)*5);
v___x_2429_ = lean_expr_has_loose_bvar(v_x_2413_, v_zero_2414_);
if (v___x_2429_ == 0)
{
lean_object* v___x_2430_; 
v___x_2430_ = lean_expr_lower_loose_bvars(v_x_2413_, v_one_2416_, v_one_2416_);
lean_dec_ref(v_x_2413_);
v_x_2412_ = v_n_2417_;
v_x_2413_ = v___x_2430_;
goto _start;
}
else
{
lean_object* v_ty_2432_; lean_object* v_val_2433_; lean_object* v___x_2434_; 
v_ty_2432_ = lean_expr_abstract_range(v_type_2426_, v_n_2417_, v_xs_2411_);
v_val_2433_ = lean_expr_abstract_range(v_value_2427_, v_n_2417_, v_xs_2411_);
lean_inc(v_userName_2425_);
v___x_2434_ = l_Lean_Expr_letE___override(v_userName_2425_, v_ty_2432_, v_val_2433_, v_x_2413_, v_nondep_2428_);
v_x_2412_ = v_n_2417_;
v_x_2413_ = v___x_2434_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_Meta_Closure_mkLambda_spec__1_spec__1___boxed(lean_object* v_decls_2436_, lean_object* v_xs_2437_, lean_object* v_x_2438_, lean_object* v_x_2439_){
_start:
{
lean_object* v_res_2440_; 
v_res_2440_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_Meta_Closure_mkLambda_spec__1_spec__1(v_decls_2436_, v_xs_2437_, v_x_2438_, v_x_2439_);
lean_dec_ref(v_xs_2437_);
lean_dec_ref(v_decls_2436_);
return v_res_2440_;
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Lean_Meta_Closure_mkLambda_spec__1(lean_object* v_decls_2441_, lean_object* v_xs_2442_, lean_object* v_x_2443_, lean_object* v_x_2444_){
_start:
{
lean_object* v_zero_2445_; uint8_t v_isZero_2446_; 
v_zero_2445_ = lean_unsigned_to_nat(0u);
v_isZero_2446_ = lean_nat_dec_eq(v_x_2443_, v_zero_2445_);
if (v_isZero_2446_ == 1)
{
return v_x_2444_;
}
else
{
lean_object* v_one_2447_; lean_object* v_n_2448_; lean_object* v_decl_2449_; 
v_one_2447_ = lean_unsigned_to_nat(1u);
v_n_2448_ = lean_nat_sub(v_x_2443_, v_one_2447_);
v_decl_2449_ = lean_array_fget_borrowed(v_decls_2441_, v_n_2448_);
if (lean_obj_tag(v_decl_2449_) == 0)
{
lean_object* v_userName_2450_; lean_object* v_type_2451_; uint8_t v_bi_2452_; lean_object* v_ty_2453_; lean_object* v___x_2454_; lean_object* v___x_2455_; 
v_userName_2450_ = lean_ctor_get(v_decl_2449_, 2);
v_type_2451_ = lean_ctor_get(v_decl_2449_, 3);
v_bi_2452_ = lean_ctor_get_uint8(v_decl_2449_, sizeof(void*)*4);
v_ty_2453_ = lean_expr_abstract_range(v_type_2451_, v_n_2448_, v_xs_2442_);
lean_inc(v_userName_2450_);
v___x_2454_ = l_Lean_mkLambda(v_userName_2450_, v_bi_2452_, v_ty_2453_, v_x_2444_);
v___x_2455_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_Meta_Closure_mkLambda_spec__1_spec__1(v_decls_2441_, v_xs_2442_, v_n_2448_, v___x_2454_);
return v___x_2455_;
}
else
{
lean_object* v_userName_2456_; lean_object* v_type_2457_; lean_object* v_value_2458_; uint8_t v_nondep_2459_; uint8_t v___x_2460_; 
v_userName_2456_ = lean_ctor_get(v_decl_2449_, 2);
v_type_2457_ = lean_ctor_get(v_decl_2449_, 3);
v_value_2458_ = lean_ctor_get(v_decl_2449_, 4);
v_nondep_2459_ = lean_ctor_get_uint8(v_decl_2449_, sizeof(void*)*5);
v___x_2460_ = lean_expr_has_loose_bvar(v_x_2444_, v_zero_2445_);
if (v___x_2460_ == 0)
{
lean_object* v___x_2461_; lean_object* v___x_2462_; 
v___x_2461_ = lean_expr_lower_loose_bvars(v_x_2444_, v_one_2447_, v_one_2447_);
lean_dec_ref(v_x_2444_);
v___x_2462_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_Meta_Closure_mkLambda_spec__1_spec__1(v_decls_2441_, v_xs_2442_, v_n_2448_, v___x_2461_);
return v___x_2462_;
}
else
{
lean_object* v_ty_2463_; lean_object* v_val_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; 
v_ty_2463_ = lean_expr_abstract_range(v_type_2457_, v_n_2448_, v_xs_2442_);
v_val_2464_ = lean_expr_abstract_range(v_value_2458_, v_n_2448_, v_xs_2442_);
lean_inc(v_userName_2456_);
v___x_2465_ = l_Lean_Expr_letE___override(v_userName_2456_, v_ty_2463_, v_val_2464_, v_x_2444_, v_nondep_2459_);
v___x_2466_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_Meta_Closure_mkLambda_spec__1_spec__1(v_decls_2441_, v_xs_2442_, v_n_2448_, v___x_2465_);
return v___x_2466_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Lean_Meta_Closure_mkLambda_spec__1___boxed(lean_object* v_decls_2467_, lean_object* v_xs_2468_, lean_object* v_x_2469_, lean_object* v_x_2470_){
_start:
{
lean_object* v_res_2471_; 
v_res_2471_ = l_Nat_foldRev___at___00Lean_Meta_Closure_mkLambda_spec__1(v_decls_2467_, v_xs_2468_, v_x_2469_, v_x_2470_);
lean_dec(v_x_2469_);
lean_dec_ref(v_xs_2468_);
lean_dec_ref(v_decls_2467_);
return v_res_2471_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkLambda(lean_object* v_decls_2472_, lean_object* v_b_2473_){
_start:
{
size_t v_sz_2474_; size_t v___x_2475_; lean_object* v_xs_2476_; lean_object* v_b_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; 
v_sz_2474_ = lean_array_size(v_decls_2472_);
v___x_2475_ = ((size_t)0ULL);
lean_inc_ref(v_decls_2472_);
v_xs_2476_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Closure_mkLambda_spec__0(v_sz_2474_, v___x_2475_, v_decls_2472_);
v_b_2477_ = lean_expr_abstract(v_b_2473_, v_xs_2476_);
v___x_2478_ = lean_array_get_size(v_decls_2472_);
v___x_2479_ = l_Nat_foldRev___at___00Lean_Meta_Closure_mkLambda_spec__1(v_decls_2472_, v_xs_2476_, v___x_2478_, v_b_2477_);
lean_dec_ref(v_xs_2476_);
lean_dec_ref(v_decls_2472_);
return v___x_2479_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkLambda___boxed(lean_object* v_decls_2480_, lean_object* v_b_2481_){
_start:
{
lean_object* v_res_2482_; 
v_res_2482_ = l_Lean_Meta_Closure_mkLambda(v_decls_2480_, v_b_2481_);
lean_dec_ref(v_b_2481_);
return v_res_2482_;
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_Meta_Closure_mkForall_spec__0_spec__0(lean_object* v_decls_2483_, lean_object* v_xs_2484_, lean_object* v_x_2485_, lean_object* v_x_2486_){
_start:
{
lean_object* v_zero_2487_; uint8_t v_isZero_2488_; 
v_zero_2487_ = lean_unsigned_to_nat(0u);
v_isZero_2488_ = lean_nat_dec_eq(v_x_2485_, v_zero_2487_);
if (v_isZero_2488_ == 1)
{
lean_dec(v_x_2485_);
return v_x_2486_;
}
else
{
lean_object* v_one_2489_; lean_object* v_n_2490_; lean_object* v_decl_2491_; 
v_one_2489_ = lean_unsigned_to_nat(1u);
v_n_2490_ = lean_nat_sub(v_x_2485_, v_one_2489_);
lean_dec(v_x_2485_);
v_decl_2491_ = lean_array_fget_borrowed(v_decls_2483_, v_n_2490_);
if (lean_obj_tag(v_decl_2491_) == 0)
{
lean_object* v_userName_2492_; lean_object* v_type_2493_; uint8_t v_bi_2494_; lean_object* v_ty_2495_; lean_object* v___x_2496_; 
v_userName_2492_ = lean_ctor_get(v_decl_2491_, 2);
v_type_2493_ = lean_ctor_get(v_decl_2491_, 3);
v_bi_2494_ = lean_ctor_get_uint8(v_decl_2491_, sizeof(void*)*4);
v_ty_2495_ = lean_expr_abstract_range(v_type_2493_, v_n_2490_, v_xs_2484_);
lean_inc(v_userName_2492_);
v___x_2496_ = l_Lean_mkForall(v_userName_2492_, v_bi_2494_, v_ty_2495_, v_x_2486_);
v_x_2485_ = v_n_2490_;
v_x_2486_ = v___x_2496_;
goto _start;
}
else
{
lean_object* v_userName_2498_; lean_object* v_type_2499_; lean_object* v_value_2500_; uint8_t v_nondep_2501_; uint8_t v___x_2502_; 
v_userName_2498_ = lean_ctor_get(v_decl_2491_, 2);
v_type_2499_ = lean_ctor_get(v_decl_2491_, 3);
v_value_2500_ = lean_ctor_get(v_decl_2491_, 4);
v_nondep_2501_ = lean_ctor_get_uint8(v_decl_2491_, sizeof(void*)*5);
v___x_2502_ = lean_expr_has_loose_bvar(v_x_2486_, v_zero_2487_);
if (v___x_2502_ == 0)
{
lean_object* v___x_2503_; 
v___x_2503_ = lean_expr_lower_loose_bvars(v_x_2486_, v_one_2489_, v_one_2489_);
lean_dec_ref(v_x_2486_);
v_x_2485_ = v_n_2490_;
v_x_2486_ = v___x_2503_;
goto _start;
}
else
{
lean_object* v_ty_2505_; lean_object* v_val_2506_; lean_object* v___x_2507_; 
v_ty_2505_ = lean_expr_abstract_range(v_type_2499_, v_n_2490_, v_xs_2484_);
v_val_2506_ = lean_expr_abstract_range(v_value_2500_, v_n_2490_, v_xs_2484_);
lean_inc(v_userName_2498_);
v___x_2507_ = l_Lean_Expr_letE___override(v_userName_2498_, v_ty_2505_, v_val_2506_, v_x_2486_, v_nondep_2501_);
v_x_2485_ = v_n_2490_;
v_x_2486_ = v___x_2507_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_Meta_Closure_mkForall_spec__0_spec__0___boxed(lean_object* v_decls_2509_, lean_object* v_xs_2510_, lean_object* v_x_2511_, lean_object* v_x_2512_){
_start:
{
lean_object* v_res_2513_; 
v_res_2513_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_Meta_Closure_mkForall_spec__0_spec__0(v_decls_2509_, v_xs_2510_, v_x_2511_, v_x_2512_);
lean_dec_ref(v_xs_2510_);
lean_dec_ref(v_decls_2509_);
return v_res_2513_;
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Lean_Meta_Closure_mkForall_spec__0(lean_object* v_decls_2514_, lean_object* v_xs_2515_, lean_object* v_x_2516_, lean_object* v_x_2517_){
_start:
{
lean_object* v_zero_2518_; uint8_t v_isZero_2519_; 
v_zero_2518_ = lean_unsigned_to_nat(0u);
v_isZero_2519_ = lean_nat_dec_eq(v_x_2516_, v_zero_2518_);
if (v_isZero_2519_ == 1)
{
return v_x_2517_;
}
else
{
lean_object* v_one_2520_; lean_object* v_n_2521_; lean_object* v_decl_2522_; 
v_one_2520_ = lean_unsigned_to_nat(1u);
v_n_2521_ = lean_nat_sub(v_x_2516_, v_one_2520_);
v_decl_2522_ = lean_array_fget_borrowed(v_decls_2514_, v_n_2521_);
if (lean_obj_tag(v_decl_2522_) == 0)
{
lean_object* v_userName_2523_; lean_object* v_type_2524_; uint8_t v_bi_2525_; lean_object* v_ty_2526_; lean_object* v___x_2527_; lean_object* v___x_2528_; 
v_userName_2523_ = lean_ctor_get(v_decl_2522_, 2);
v_type_2524_ = lean_ctor_get(v_decl_2522_, 3);
v_bi_2525_ = lean_ctor_get_uint8(v_decl_2522_, sizeof(void*)*4);
v_ty_2526_ = lean_expr_abstract_range(v_type_2524_, v_n_2521_, v_xs_2515_);
lean_inc(v_userName_2523_);
v___x_2527_ = l_Lean_mkForall(v_userName_2523_, v_bi_2525_, v_ty_2526_, v_x_2517_);
v___x_2528_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_Meta_Closure_mkForall_spec__0_spec__0(v_decls_2514_, v_xs_2515_, v_n_2521_, v___x_2527_);
return v___x_2528_;
}
else
{
lean_object* v_userName_2529_; lean_object* v_type_2530_; lean_object* v_value_2531_; uint8_t v_nondep_2532_; uint8_t v___x_2533_; 
v_userName_2529_ = lean_ctor_get(v_decl_2522_, 2);
v_type_2530_ = lean_ctor_get(v_decl_2522_, 3);
v_value_2531_ = lean_ctor_get(v_decl_2522_, 4);
v_nondep_2532_ = lean_ctor_get_uint8(v_decl_2522_, sizeof(void*)*5);
v___x_2533_ = lean_expr_has_loose_bvar(v_x_2517_, v_zero_2518_);
if (v___x_2533_ == 0)
{
lean_object* v___x_2534_; lean_object* v___x_2535_; 
v___x_2534_ = lean_expr_lower_loose_bvars(v_x_2517_, v_one_2520_, v_one_2520_);
lean_dec_ref(v_x_2517_);
v___x_2535_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_Meta_Closure_mkForall_spec__0_spec__0(v_decls_2514_, v_xs_2515_, v_n_2521_, v___x_2534_);
return v___x_2535_;
}
else
{
lean_object* v_ty_2536_; lean_object* v_val_2537_; lean_object* v___x_2538_; lean_object* v___x_2539_; 
v_ty_2536_ = lean_expr_abstract_range(v_type_2530_, v_n_2521_, v_xs_2515_);
v_val_2537_ = lean_expr_abstract_range(v_value_2531_, v_n_2521_, v_xs_2515_);
lean_inc(v_userName_2529_);
v___x_2538_ = l_Lean_Expr_letE___override(v_userName_2529_, v_ty_2536_, v_val_2537_, v_x_2517_, v_nondep_2532_);
v___x_2539_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_Meta_Closure_mkForall_spec__0_spec__0(v_decls_2514_, v_xs_2515_, v_n_2521_, v___x_2538_);
return v___x_2539_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Lean_Meta_Closure_mkForall_spec__0___boxed(lean_object* v_decls_2540_, lean_object* v_xs_2541_, lean_object* v_x_2542_, lean_object* v_x_2543_){
_start:
{
lean_object* v_res_2544_; 
v_res_2544_ = l_Nat_foldRev___at___00Lean_Meta_Closure_mkForall_spec__0(v_decls_2540_, v_xs_2541_, v_x_2542_, v_x_2543_);
lean_dec(v_x_2542_);
lean_dec_ref(v_xs_2541_);
lean_dec_ref(v_decls_2540_);
return v_res_2544_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkForall(lean_object* v_decls_2545_, lean_object* v_b_2546_){
_start:
{
size_t v_sz_2547_; size_t v___x_2548_; lean_object* v_xs_2549_; lean_object* v_b_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; 
v_sz_2547_ = lean_array_size(v_decls_2545_);
v___x_2548_ = ((size_t)0ULL);
lean_inc_ref(v_decls_2545_);
v_xs_2549_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Closure_mkLambda_spec__0(v_sz_2547_, v___x_2548_, v_decls_2545_);
v_b_2550_ = lean_expr_abstract(v_b_2546_, v_xs_2549_);
v___x_2551_ = lean_array_get_size(v_decls_2545_);
v___x_2552_ = l_Nat_foldRev___at___00Lean_Meta_Closure_mkForall_spec__0(v_decls_2545_, v_xs_2549_, v___x_2551_, v_b_2550_);
lean_dec_ref(v_xs_2549_);
lean_dec_ref(v_decls_2545_);
return v___x_2552_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkForall___boxed(lean_object* v_decls_2553_, lean_object* v_b_2554_){
_start:
{
lean_object* v_res_2555_; 
v_res_2555_ = l_Lean_Meta_Closure_mkForall(v_decls_2553_, v_b_2554_);
lean_dec_ref(v_b_2554_);
return v_res_2555_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkValueTypeClosureAux___lam__0(lean_object* v_a_2556_, lean_object* v_zetaDeltaFVarIds_2557_, lean_object* v_a_x3f_2558_){
_start:
{
lean_object* v___x_2560_; lean_object* v_mctx_2561_; lean_object* v_cache_2562_; lean_object* v_postponed_2563_; lean_object* v_diag_2564_; lean_object* v___x_2566_; uint8_t v_isShared_2567_; uint8_t v_isSharedCheck_2574_; 
v___x_2560_ = lean_st_ref_take(v_a_2556_);
v_mctx_2561_ = lean_ctor_get(v___x_2560_, 0);
v_cache_2562_ = lean_ctor_get(v___x_2560_, 1);
v_postponed_2563_ = lean_ctor_get(v___x_2560_, 3);
v_diag_2564_ = lean_ctor_get(v___x_2560_, 4);
v_isSharedCheck_2574_ = !lean_is_exclusive(v___x_2560_);
if (v_isSharedCheck_2574_ == 0)
{
lean_object* v_unused_2575_; 
v_unused_2575_ = lean_ctor_get(v___x_2560_, 2);
lean_dec(v_unused_2575_);
v___x_2566_ = v___x_2560_;
v_isShared_2567_ = v_isSharedCheck_2574_;
goto v_resetjp_2565_;
}
else
{
lean_inc(v_diag_2564_);
lean_inc(v_postponed_2563_);
lean_inc(v_cache_2562_);
lean_inc(v_mctx_2561_);
lean_dec(v___x_2560_);
v___x_2566_ = lean_box(0);
v_isShared_2567_ = v_isSharedCheck_2574_;
goto v_resetjp_2565_;
}
v_resetjp_2565_:
{
lean_object* v___x_2569_; 
if (v_isShared_2567_ == 0)
{
lean_ctor_set(v___x_2566_, 2, v_zetaDeltaFVarIds_2557_);
v___x_2569_ = v___x_2566_;
goto v_reusejp_2568_;
}
else
{
lean_object* v_reuseFailAlloc_2573_; 
v_reuseFailAlloc_2573_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2573_, 0, v_mctx_2561_);
lean_ctor_set(v_reuseFailAlloc_2573_, 1, v_cache_2562_);
lean_ctor_set(v_reuseFailAlloc_2573_, 2, v_zetaDeltaFVarIds_2557_);
lean_ctor_set(v_reuseFailAlloc_2573_, 3, v_postponed_2563_);
lean_ctor_set(v_reuseFailAlloc_2573_, 4, v_diag_2564_);
v___x_2569_ = v_reuseFailAlloc_2573_;
goto v_reusejp_2568_;
}
v_reusejp_2568_:
{
lean_object* v___x_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; 
v___x_2570_ = lean_st_ref_set(v_a_2556_, v___x_2569_);
v___x_2571_ = lean_box(0);
v___x_2572_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2572_, 0, v___x_2571_);
return v___x_2572_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkValueTypeClosureAux___lam__0___boxed(lean_object* v_a_2576_, lean_object* v_zetaDeltaFVarIds_2577_, lean_object* v_a_x3f_2578_, lean_object* v___y_2579_){
_start:
{
lean_object* v_res_2580_; 
v_res_2580_ = l_Lean_Meta_Closure_mkValueTypeClosureAux___lam__0(v_a_2576_, v_zetaDeltaFVarIds_2577_, v_a_x3f_2578_);
lean_dec(v_a_x3f_2578_);
lean_dec(v_a_2576_);
return v_res_2580_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkValueTypeClosureAux___lam__1(lean_object* v_a_2581_, lean_object* v_cache_2582_, lean_object* v_a_x3f_2583_){
_start:
{
lean_object* v___x_2585_; lean_object* v_mctx_2586_; lean_object* v_zetaDeltaFVarIds_2587_; lean_object* v_postponed_2588_; lean_object* v_diag_2589_; lean_object* v___x_2591_; uint8_t v_isShared_2592_; uint8_t v_isSharedCheck_2599_; 
v___x_2585_ = lean_st_ref_take(v_a_2581_);
v_mctx_2586_ = lean_ctor_get(v___x_2585_, 0);
v_zetaDeltaFVarIds_2587_ = lean_ctor_get(v___x_2585_, 2);
v_postponed_2588_ = lean_ctor_get(v___x_2585_, 3);
v_diag_2589_ = lean_ctor_get(v___x_2585_, 4);
v_isSharedCheck_2599_ = !lean_is_exclusive(v___x_2585_);
if (v_isSharedCheck_2599_ == 0)
{
lean_object* v_unused_2600_; 
v_unused_2600_ = lean_ctor_get(v___x_2585_, 1);
lean_dec(v_unused_2600_);
v___x_2591_ = v___x_2585_;
v_isShared_2592_ = v_isSharedCheck_2599_;
goto v_resetjp_2590_;
}
else
{
lean_inc(v_diag_2589_);
lean_inc(v_postponed_2588_);
lean_inc(v_zetaDeltaFVarIds_2587_);
lean_inc(v_mctx_2586_);
lean_dec(v___x_2585_);
v___x_2591_ = lean_box(0);
v_isShared_2592_ = v_isSharedCheck_2599_;
goto v_resetjp_2590_;
}
v_resetjp_2590_:
{
lean_object* v___x_2594_; 
if (v_isShared_2592_ == 0)
{
lean_ctor_set(v___x_2591_, 1, v_cache_2582_);
v___x_2594_ = v___x_2591_;
goto v_reusejp_2593_;
}
else
{
lean_object* v_reuseFailAlloc_2598_; 
v_reuseFailAlloc_2598_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2598_, 0, v_mctx_2586_);
lean_ctor_set(v_reuseFailAlloc_2598_, 1, v_cache_2582_);
lean_ctor_set(v_reuseFailAlloc_2598_, 2, v_zetaDeltaFVarIds_2587_);
lean_ctor_set(v_reuseFailAlloc_2598_, 3, v_postponed_2588_);
lean_ctor_set(v_reuseFailAlloc_2598_, 4, v_diag_2589_);
v___x_2594_ = v_reuseFailAlloc_2598_;
goto v_reusejp_2593_;
}
v_reusejp_2593_:
{
lean_object* v___x_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; 
v___x_2595_ = lean_st_ref_set(v_a_2581_, v___x_2594_);
v___x_2596_ = lean_box(0);
v___x_2597_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2597_, 0, v___x_2596_);
return v___x_2597_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkValueTypeClosureAux___lam__1___boxed(lean_object* v_a_2601_, lean_object* v_cache_2602_, lean_object* v_a_x3f_2603_, lean_object* v___y_2604_){
_start:
{
lean_object* v_res_2605_; 
v_res_2605_ = l_Lean_Meta_Closure_mkValueTypeClosureAux___lam__1(v_a_2601_, v_cache_2602_, v_a_x3f_2603_);
lean_dec(v_a_x3f_2603_);
lean_dec(v_a_2601_);
return v_res_2605_;
}
}
static lean_object* _init_l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__0(void){
_start:
{
lean_object* v___x_2606_; 
v___x_2606_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2606_;
}
}
static lean_object* _init_l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__1(void){
_start:
{
lean_object* v___x_2607_; lean_object* v___x_2608_; 
v___x_2607_ = lean_obj_once(&l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__0, &l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__0_once, _init_l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__0);
v___x_2608_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2608_, 0, v___x_2607_);
return v___x_2608_;
}
}
static lean_object* _init_l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__2(void){
_start:
{
lean_object* v___x_2609_; lean_object* v___x_2610_; 
v___x_2609_ = lean_obj_once(&l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__1, &l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__1_once, _init_l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__1);
v___x_2610_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2610_, 0, v___x_2609_);
lean_ctor_set(v___x_2610_, 1, v___x_2609_);
lean_ctor_set(v___x_2610_, 2, v___x_2609_);
lean_ctor_set(v___x_2610_, 3, v___x_2609_);
lean_ctor_set(v___x_2610_, 4, v___x_2609_);
lean_ctor_set(v___x_2610_, 5, v___x_2609_);
return v___x_2610_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkValueTypeClosureAux(lean_object* v_type_2611_, lean_object* v_value_2612_, uint8_t v_a_2613_, lean_object* v_a_2614_, lean_object* v_a_2615_, lean_object* v_a_2616_, lean_object* v_a_2617_, lean_object* v_a_2618_){
_start:
{
lean_object* v___x_2620_; lean_object* v___x_2621_; lean_object* v_mctx_2622_; lean_object* v_zetaDeltaFVarIds_2623_; lean_object* v_postponed_2624_; lean_object* v_diag_2625_; lean_object* v___x_2627_; uint8_t v_isShared_2628_; uint8_t v_isSharedCheck_2705_; 
v___x_2620_ = lean_st_ref_get(v_a_2616_);
v___x_2621_ = lean_st_ref_take(v_a_2616_);
v_mctx_2622_ = lean_ctor_get(v___x_2621_, 0);
v_zetaDeltaFVarIds_2623_ = lean_ctor_get(v___x_2621_, 2);
v_postponed_2624_ = lean_ctor_get(v___x_2621_, 3);
v_diag_2625_ = lean_ctor_get(v___x_2621_, 4);
v_isSharedCheck_2705_ = !lean_is_exclusive(v___x_2621_);
if (v_isSharedCheck_2705_ == 0)
{
lean_object* v_unused_2706_; 
v_unused_2706_ = lean_ctor_get(v___x_2621_, 1);
lean_dec(v_unused_2706_);
v___x_2627_ = v___x_2621_;
v_isShared_2628_ = v_isSharedCheck_2705_;
goto v_resetjp_2626_;
}
else
{
lean_inc(v_diag_2625_);
lean_inc(v_postponed_2624_);
lean_inc(v_zetaDeltaFVarIds_2623_);
lean_inc(v_mctx_2622_);
lean_dec(v___x_2621_);
v___x_2627_ = lean_box(0);
v_isShared_2628_ = v_isSharedCheck_2705_;
goto v_resetjp_2626_;
}
v_resetjp_2626_:
{
lean_object* v___x_2629_; lean_object* v___x_2631_; 
v___x_2629_ = lean_obj_once(&l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__2, &l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__2_once, _init_l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__2);
if (v_isShared_2628_ == 0)
{
lean_ctor_set(v___x_2627_, 1, v___x_2629_);
v___x_2631_ = v___x_2627_;
goto v_reusejp_2630_;
}
else
{
lean_object* v_reuseFailAlloc_2704_; 
v_reuseFailAlloc_2704_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2704_, 0, v_mctx_2622_);
lean_ctor_set(v_reuseFailAlloc_2704_, 1, v___x_2629_);
lean_ctor_set(v_reuseFailAlloc_2704_, 2, v_zetaDeltaFVarIds_2623_);
lean_ctor_set(v_reuseFailAlloc_2704_, 3, v_postponed_2624_);
lean_ctor_set(v_reuseFailAlloc_2704_, 4, v_diag_2625_);
v___x_2631_ = v_reuseFailAlloc_2704_;
goto v_reusejp_2630_;
}
v_reusejp_2630_:
{
lean_object* v___x_2632_; lean_object* v___x_2633_; lean_object* v_mctx_2634_; lean_object* v_cache_2635_; lean_object* v_zetaDeltaFVarIds_2636_; lean_object* v_postponed_2637_; lean_object* v_diag_2638_; lean_object* v___x_2640_; uint8_t v_isShared_2641_; uint8_t v_isSharedCheck_2703_; 
v___x_2632_ = lean_st_ref_set(v_a_2616_, v___x_2631_);
v___x_2633_ = lean_st_ref_take(v_a_2616_);
v_mctx_2634_ = lean_ctor_get(v___x_2633_, 0);
v_cache_2635_ = lean_ctor_get(v___x_2633_, 1);
v_zetaDeltaFVarIds_2636_ = lean_ctor_get(v___x_2633_, 2);
v_postponed_2637_ = lean_ctor_get(v___x_2633_, 3);
v_diag_2638_ = lean_ctor_get(v___x_2633_, 4);
v_isSharedCheck_2703_ = !lean_is_exclusive(v___x_2633_);
if (v_isSharedCheck_2703_ == 0)
{
v___x_2640_ = v___x_2633_;
v_isShared_2641_ = v_isSharedCheck_2703_;
goto v_resetjp_2639_;
}
else
{
lean_inc(v_diag_2638_);
lean_inc(v_postponed_2637_);
lean_inc(v_zetaDeltaFVarIds_2636_);
lean_inc(v_cache_2635_);
lean_inc(v_mctx_2634_);
lean_dec(v___x_2633_);
v___x_2640_ = lean_box(0);
v_isShared_2641_ = v_isSharedCheck_2703_;
goto v_resetjp_2639_;
}
v_resetjp_2639_:
{
lean_object* v___x_2642_; lean_object* v___x_2644_; 
v___x_2642_ = lean_box(1);
if (v_isShared_2641_ == 0)
{
lean_ctor_set(v___x_2640_, 2, v___x_2642_);
v___x_2644_ = v___x_2640_;
goto v_reusejp_2643_;
}
else
{
lean_object* v_reuseFailAlloc_2702_; 
v_reuseFailAlloc_2702_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2702_, 0, v_mctx_2634_);
lean_ctor_set(v_reuseFailAlloc_2702_, 1, v_cache_2635_);
lean_ctor_set(v_reuseFailAlloc_2702_, 2, v___x_2642_);
lean_ctor_set(v_reuseFailAlloc_2702_, 3, v_postponed_2637_);
lean_ctor_set(v_reuseFailAlloc_2702_, 4, v_diag_2638_);
v___x_2644_ = v_reuseFailAlloc_2702_;
goto v_reusejp_2643_;
}
v_reusejp_2643_:
{
lean_object* v___x_2645_; lean_object* v_cache_2646_; lean_object* v_keyedConfig_2647_; lean_object* v_zetaDeltaSet_2648_; lean_object* v_lctx_2649_; lean_object* v_localInstances_2650_; lean_object* v_defEqCtx_x3f_2651_; lean_object* v_synthPendingDepth_2652_; lean_object* v_canUnfold_x3f_2653_; uint8_t v_univApprox_2654_; uint8_t v_inTypeClassResolution_2655_; uint8_t v_cacheInferType_2656_; lean_object* v_a_2658_; lean_object* v_a_2670_; uint8_t v___x_2673_; lean_object* v___x_2674_; lean_object* v___x_2675_; 
v___x_2645_ = lean_st_ref_set(v_a_2616_, v___x_2644_);
v_cache_2646_ = lean_ctor_get(v___x_2620_, 1);
lean_inc_ref(v_cache_2646_);
lean_dec(v___x_2620_);
v_keyedConfig_2647_ = lean_ctor_get(v_a_2615_, 0);
v_zetaDeltaSet_2648_ = lean_ctor_get(v_a_2615_, 1);
v_lctx_2649_ = lean_ctor_get(v_a_2615_, 2);
v_localInstances_2650_ = lean_ctor_get(v_a_2615_, 3);
v_defEqCtx_x3f_2651_ = lean_ctor_get(v_a_2615_, 4);
v_synthPendingDepth_2652_ = lean_ctor_get(v_a_2615_, 5);
v_canUnfold_x3f_2653_ = lean_ctor_get(v_a_2615_, 6);
v_univApprox_2654_ = lean_ctor_get_uint8(v_a_2615_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2655_ = lean_ctor_get_uint8(v_a_2615_, sizeof(void*)*7 + 2);
v_cacheInferType_2656_ = lean_ctor_get_uint8(v_a_2615_, sizeof(void*)*7 + 3);
v___x_2673_ = 1;
lean_inc(v_canUnfold_x3f_2653_);
lean_inc(v_synthPendingDepth_2652_);
lean_inc(v_defEqCtx_x3f_2651_);
lean_inc_ref(v_localInstances_2650_);
lean_inc_ref(v_lctx_2649_);
lean_inc(v_zetaDeltaSet_2648_);
lean_inc_ref(v_keyedConfig_2647_);
v___x_2674_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2674_, 0, v_keyedConfig_2647_);
lean_ctor_set(v___x_2674_, 1, v_zetaDeltaSet_2648_);
lean_ctor_set(v___x_2674_, 2, v_lctx_2649_);
lean_ctor_set(v___x_2674_, 3, v_localInstances_2650_);
lean_ctor_set(v___x_2674_, 4, v_defEqCtx_x3f_2651_);
lean_ctor_set(v___x_2674_, 5, v_synthPendingDepth_2652_);
lean_ctor_set(v___x_2674_, 6, v_canUnfold_x3f_2653_);
lean_ctor_set_uint8(v___x_2674_, sizeof(void*)*7, v___x_2673_);
lean_ctor_set_uint8(v___x_2674_, sizeof(void*)*7 + 1, v_univApprox_2654_);
lean_ctor_set_uint8(v___x_2674_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2655_);
lean_ctor_set_uint8(v___x_2674_, sizeof(void*)*7 + 3, v_cacheInferType_2656_);
v___x_2675_ = l_Lean_Meta_Closure_collectExpr(v_type_2611_, v_a_2613_, v_a_2614_, v___x_2674_, v_a_2616_, v_a_2617_, v_a_2618_);
if (lean_obj_tag(v___x_2675_) == 0)
{
lean_object* v_a_2676_; lean_object* v___x_2677_; 
v_a_2676_ = lean_ctor_get(v___x_2675_, 0);
lean_inc(v_a_2676_);
lean_dec_ref(v___x_2675_);
v___x_2677_ = l_Lean_Meta_Closure_collectExpr(v_value_2612_, v_a_2613_, v_a_2614_, v___x_2674_, v_a_2616_, v_a_2617_, v_a_2618_);
if (lean_obj_tag(v___x_2677_) == 0)
{
lean_object* v_a_2678_; lean_object* v___x_2679_; 
v_a_2678_ = lean_ctor_get(v___x_2677_, 0);
lean_inc(v_a_2678_);
lean_dec_ref(v___x_2677_);
v___x_2679_ = l_Lean_Meta_Closure_process(v_a_2613_, v_a_2614_, v___x_2674_, v_a_2616_, v_a_2617_, v_a_2618_);
lean_dec_ref(v___x_2674_);
if (lean_obj_tag(v___x_2679_) == 0)
{
lean_object* v___x_2681_; uint8_t v_isShared_2682_; uint8_t v_isSharedCheck_2697_; 
v_isSharedCheck_2697_ = !lean_is_exclusive(v___x_2679_);
if (v_isSharedCheck_2697_ == 0)
{
lean_object* v_unused_2698_; 
v_unused_2698_ = lean_ctor_get(v___x_2679_, 0);
lean_dec(v_unused_2698_);
v___x_2681_ = v___x_2679_;
v_isShared_2682_ = v_isSharedCheck_2697_;
goto v_resetjp_2680_;
}
else
{
lean_dec(v___x_2679_);
v___x_2681_ = lean_box(0);
v_isShared_2682_ = v_isSharedCheck_2697_;
goto v_resetjp_2680_;
}
v_resetjp_2680_:
{
lean_object* v___x_2683_; lean_object* v___x_2685_; 
v___x_2683_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2683_, 0, v_a_2676_);
lean_ctor_set(v___x_2683_, 1, v_a_2678_);
lean_inc_ref(v___x_2683_);
if (v_isShared_2682_ == 0)
{
lean_ctor_set_tag(v___x_2681_, 1);
lean_ctor_set(v___x_2681_, 0, v___x_2683_);
v___x_2685_ = v___x_2681_;
goto v_reusejp_2684_;
}
else
{
lean_object* v_reuseFailAlloc_2696_; 
v_reuseFailAlloc_2696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2696_, 0, v___x_2683_);
v___x_2685_ = v_reuseFailAlloc_2696_;
goto v_reusejp_2684_;
}
v_reusejp_2684_:
{
lean_object* v___x_2686_; lean_object* v___x_2687_; lean_object* v___x_2689_; uint8_t v_isShared_2690_; uint8_t v_isSharedCheck_2694_; 
v___x_2686_ = l_Lean_Meta_Closure_mkValueTypeClosureAux___lam__0(v_a_2616_, v_zetaDeltaFVarIds_2636_, v___x_2685_);
lean_dec_ref(v___x_2686_);
v___x_2687_ = l_Lean_Meta_Closure_mkValueTypeClosureAux___lam__1(v_a_2616_, v_cache_2646_, v___x_2685_);
lean_dec_ref(v___x_2685_);
v_isSharedCheck_2694_ = !lean_is_exclusive(v___x_2687_);
if (v_isSharedCheck_2694_ == 0)
{
lean_object* v_unused_2695_; 
v_unused_2695_ = lean_ctor_get(v___x_2687_, 0);
lean_dec(v_unused_2695_);
v___x_2689_ = v___x_2687_;
v_isShared_2690_ = v_isSharedCheck_2694_;
goto v_resetjp_2688_;
}
else
{
lean_dec(v___x_2687_);
v___x_2689_ = lean_box(0);
v_isShared_2690_ = v_isSharedCheck_2694_;
goto v_resetjp_2688_;
}
v_resetjp_2688_:
{
lean_object* v___x_2692_; 
if (v_isShared_2690_ == 0)
{
lean_ctor_set(v___x_2689_, 0, v___x_2683_);
v___x_2692_ = v___x_2689_;
goto v_reusejp_2691_;
}
else
{
lean_object* v_reuseFailAlloc_2693_; 
v_reuseFailAlloc_2693_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2693_, 0, v___x_2683_);
v___x_2692_ = v_reuseFailAlloc_2693_;
goto v_reusejp_2691_;
}
v_reusejp_2691_:
{
return v___x_2692_;
}
}
}
}
}
else
{
lean_object* v_a_2699_; 
lean_dec(v_a_2678_);
lean_dec(v_a_2676_);
v_a_2699_ = lean_ctor_get(v___x_2679_, 0);
lean_inc(v_a_2699_);
lean_dec_ref(v___x_2679_);
v_a_2670_ = v_a_2699_;
goto v___jp_2669_;
}
}
else
{
lean_object* v_a_2700_; 
lean_dec(v_a_2676_);
lean_dec_ref(v___x_2674_);
v_a_2700_ = lean_ctor_get(v___x_2677_, 0);
lean_inc(v_a_2700_);
lean_dec_ref(v___x_2677_);
v_a_2670_ = v_a_2700_;
goto v___jp_2669_;
}
}
else
{
lean_object* v_a_2701_; 
lean_dec_ref(v___x_2674_);
lean_dec_ref(v_value_2612_);
v_a_2701_ = lean_ctor_get(v___x_2675_, 0);
lean_inc(v_a_2701_);
lean_dec_ref(v___x_2675_);
v_a_2670_ = v_a_2701_;
goto v___jp_2669_;
}
v___jp_2657_:
{
lean_object* v___x_2659_; lean_object* v___x_2660_; lean_object* v___x_2662_; uint8_t v_isShared_2663_; uint8_t v_isSharedCheck_2667_; 
v___x_2659_ = lean_box(0);
v___x_2660_ = l_Lean_Meta_Closure_mkValueTypeClosureAux___lam__1(v_a_2616_, v_cache_2646_, v___x_2659_);
v_isSharedCheck_2667_ = !lean_is_exclusive(v___x_2660_);
if (v_isSharedCheck_2667_ == 0)
{
lean_object* v_unused_2668_; 
v_unused_2668_ = lean_ctor_get(v___x_2660_, 0);
lean_dec(v_unused_2668_);
v___x_2662_ = v___x_2660_;
v_isShared_2663_ = v_isSharedCheck_2667_;
goto v_resetjp_2661_;
}
else
{
lean_dec(v___x_2660_);
v___x_2662_ = lean_box(0);
v_isShared_2663_ = v_isSharedCheck_2667_;
goto v_resetjp_2661_;
}
v_resetjp_2661_:
{
lean_object* v___x_2665_; 
if (v_isShared_2663_ == 0)
{
lean_ctor_set_tag(v___x_2662_, 1);
lean_ctor_set(v___x_2662_, 0, v_a_2658_);
v___x_2665_ = v___x_2662_;
goto v_reusejp_2664_;
}
else
{
lean_object* v_reuseFailAlloc_2666_; 
v_reuseFailAlloc_2666_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2666_, 0, v_a_2658_);
v___x_2665_ = v_reuseFailAlloc_2666_;
goto v_reusejp_2664_;
}
v_reusejp_2664_:
{
return v___x_2665_;
}
}
}
v___jp_2669_:
{
lean_object* v___x_2671_; lean_object* v___x_2672_; 
v___x_2671_ = lean_box(0);
v___x_2672_ = l_Lean_Meta_Closure_mkValueTypeClosureAux___lam__0(v_a_2616_, v_zetaDeltaFVarIds_2636_, v___x_2671_);
lean_dec_ref(v___x_2672_);
v_a_2658_ = v_a_2670_;
goto v___jp_2657_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkValueTypeClosureAux___boxed(lean_object* v_type_2707_, lean_object* v_value_2708_, lean_object* v_a_2709_, lean_object* v_a_2710_, lean_object* v_a_2711_, lean_object* v_a_2712_, lean_object* v_a_2713_, lean_object* v_a_2714_, lean_object* v_a_2715_){
_start:
{
uint8_t v_a_boxed_2716_; lean_object* v_res_2717_; 
v_a_boxed_2716_ = lean_unbox(v_a_2709_);
v_res_2717_ = l_Lean_Meta_Closure_mkValueTypeClosureAux(v_type_2707_, v_value_2708_, v_a_boxed_2716_, v_a_2710_, v_a_2711_, v_a_2712_, v_a_2713_, v_a_2714_);
lean_dec(v_a_2714_);
lean_dec_ref(v_a_2713_);
lean_dec(v_a_2712_);
lean_dec_ref(v_a_2711_);
lean_dec(v_a_2710_);
return v_res_2717_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4___closed__0(void){
_start:
{
lean_object* v___x_2718_; 
v___x_2718_ = l_instMonadEIO(lean_box(0));
return v___x_2718_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4(lean_object* v_msg_2721_, lean_object* v___y_2722_, lean_object* v___y_2723_, lean_object* v___y_2724_){
_start:
{
lean_object* v___x_2726_; lean_object* v___x_2727_; lean_object* v_toApplicative_2728_; lean_object* v___x_2730_; uint8_t v_isShared_2731_; uint8_t v_isSharedCheck_2769_; 
v___x_2726_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4___closed__0, &l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4___closed__0);
v___x_2727_ = l_StateRefT_x27_instMonad___redArg(v___x_2726_);
v_toApplicative_2728_ = lean_ctor_get(v___x_2727_, 0);
v_isSharedCheck_2769_ = !lean_is_exclusive(v___x_2727_);
if (v_isSharedCheck_2769_ == 0)
{
lean_object* v_unused_2770_; 
v_unused_2770_ = lean_ctor_get(v___x_2727_, 1);
lean_dec(v_unused_2770_);
v___x_2730_ = v___x_2727_;
v_isShared_2731_ = v_isSharedCheck_2769_;
goto v_resetjp_2729_;
}
else
{
lean_inc(v_toApplicative_2728_);
lean_dec(v___x_2727_);
v___x_2730_ = lean_box(0);
v_isShared_2731_ = v_isSharedCheck_2769_;
goto v_resetjp_2729_;
}
v_resetjp_2729_:
{
lean_object* v_toFunctor_2732_; lean_object* v_toSeq_2733_; lean_object* v_toSeqLeft_2734_; lean_object* v_toSeqRight_2735_; lean_object* v___x_2737_; uint8_t v_isShared_2738_; uint8_t v_isSharedCheck_2767_; 
v_toFunctor_2732_ = lean_ctor_get(v_toApplicative_2728_, 0);
v_toSeq_2733_ = lean_ctor_get(v_toApplicative_2728_, 2);
v_toSeqLeft_2734_ = lean_ctor_get(v_toApplicative_2728_, 3);
v_toSeqRight_2735_ = lean_ctor_get(v_toApplicative_2728_, 4);
v_isSharedCheck_2767_ = !lean_is_exclusive(v_toApplicative_2728_);
if (v_isSharedCheck_2767_ == 0)
{
lean_object* v_unused_2768_; 
v_unused_2768_ = lean_ctor_get(v_toApplicative_2728_, 1);
lean_dec(v_unused_2768_);
v___x_2737_ = v_toApplicative_2728_;
v_isShared_2738_ = v_isSharedCheck_2767_;
goto v_resetjp_2736_;
}
else
{
lean_inc(v_toSeqRight_2735_);
lean_inc(v_toSeqLeft_2734_);
lean_inc(v_toSeq_2733_);
lean_inc(v_toFunctor_2732_);
lean_dec(v_toApplicative_2728_);
v___x_2737_ = lean_box(0);
v_isShared_2738_ = v_isSharedCheck_2767_;
goto v_resetjp_2736_;
}
v_resetjp_2736_:
{
lean_object* v___f_2739_; lean_object* v___f_2740_; lean_object* v___f_2741_; lean_object* v___f_2742_; lean_object* v___x_2743_; lean_object* v___f_2744_; lean_object* v___f_2745_; lean_object* v___f_2746_; lean_object* v___x_2748_; 
v___f_2739_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4___closed__1));
v___f_2740_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4___closed__2));
lean_inc_ref(v_toFunctor_2732_);
v___f_2741_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2741_, 0, v_toFunctor_2732_);
v___f_2742_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2742_, 0, v_toFunctor_2732_);
v___x_2743_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2743_, 0, v___f_2741_);
lean_ctor_set(v___x_2743_, 1, v___f_2742_);
v___f_2744_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2744_, 0, v_toSeqRight_2735_);
v___f_2745_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2745_, 0, v_toSeqLeft_2734_);
v___f_2746_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2746_, 0, v_toSeq_2733_);
if (v_isShared_2738_ == 0)
{
lean_ctor_set(v___x_2737_, 4, v___f_2744_);
lean_ctor_set(v___x_2737_, 3, v___f_2745_);
lean_ctor_set(v___x_2737_, 2, v___f_2746_);
lean_ctor_set(v___x_2737_, 1, v___f_2739_);
lean_ctor_set(v___x_2737_, 0, v___x_2743_);
v___x_2748_ = v___x_2737_;
goto v_reusejp_2747_;
}
else
{
lean_object* v_reuseFailAlloc_2766_; 
v_reuseFailAlloc_2766_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2766_, 0, v___x_2743_);
lean_ctor_set(v_reuseFailAlloc_2766_, 1, v___f_2739_);
lean_ctor_set(v_reuseFailAlloc_2766_, 2, v___f_2746_);
lean_ctor_set(v_reuseFailAlloc_2766_, 3, v___f_2745_);
lean_ctor_set(v_reuseFailAlloc_2766_, 4, v___f_2744_);
v___x_2748_ = v_reuseFailAlloc_2766_;
goto v_reusejp_2747_;
}
v_reusejp_2747_:
{
lean_object* v___x_2750_; 
if (v_isShared_2731_ == 0)
{
lean_ctor_set(v___x_2730_, 1, v___f_2740_);
lean_ctor_set(v___x_2730_, 0, v___x_2748_);
v___x_2750_ = v___x_2730_;
goto v_reusejp_2749_;
}
else
{
lean_object* v_reuseFailAlloc_2765_; 
v_reuseFailAlloc_2765_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2765_, 0, v___x_2748_);
lean_ctor_set(v_reuseFailAlloc_2765_, 1, v___f_2740_);
v___x_2750_ = v_reuseFailAlloc_2765_;
goto v_reusejp_2749_;
}
v_reusejp_2749_:
{
lean_object* v___f_2751_; lean_object* v___f_2752_; lean_object* v___f_2753_; lean_object* v___f_2754_; lean_object* v___x_2755_; lean_object* v___x_2756_; lean_object* v___x_2757_; lean_object* v___x_2758_; lean_object* v___x_2759_; lean_object* v___x_2760_; lean_object* v___x_2761_; lean_object* v___x_2762_; lean_object* v___x_14558__overap_2763_; lean_object* v___x_2764_; 
lean_inc_ref_n(v___x_2750_, 6);
v___f_2751_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2751_, 0, v___x_2750_);
v___f_2752_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2752_, 0, v___x_2750_);
v___f_2753_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_2753_, 0, v___x_2750_);
v___f_2754_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_2754_, 0, v___x_2750_);
v___x_2755_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_2755_, 0, lean_box(0));
lean_closure_set(v___x_2755_, 1, lean_box(0));
lean_closure_set(v___x_2755_, 2, v___x_2750_);
v___x_2756_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2756_, 0, v___x_2755_);
lean_ctor_set(v___x_2756_, 1, v___f_2751_);
v___x_2757_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_2757_, 0, lean_box(0));
lean_closure_set(v___x_2757_, 1, lean_box(0));
lean_closure_set(v___x_2757_, 2, v___x_2750_);
v___x_2758_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2758_, 0, v___x_2756_);
lean_ctor_set(v___x_2758_, 1, v___x_2757_);
lean_ctor_set(v___x_2758_, 2, v___f_2752_);
lean_ctor_set(v___x_2758_, 3, v___f_2753_);
lean_ctor_set(v___x_2758_, 4, v___f_2754_);
v___x_2759_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_2759_, 0, lean_box(0));
lean_closure_set(v___x_2759_, 1, lean_box(0));
lean_closure_set(v___x_2759_, 2, v___x_2750_);
v___x_2760_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2760_, 0, v___x_2758_);
lean_ctor_set(v___x_2760_, 1, v___x_2759_);
v___x_2761_ = lean_box(0);
v___x_2762_ = l_instInhabitedOfMonad___redArg(v___x_2760_, v___x_2761_);
v___x_14558__overap_2763_ = lean_panic_fn_borrowed(v___x_2762_, v_msg_2721_);
lean_dec(v___x_2762_);
lean_inc(v___y_2724_);
lean_inc_ref(v___y_2723_);
v___x_2764_ = lean_apply_4(v___x_14558__overap_2763_, v___y_2722_, v___y_2723_, v___y_2724_, lean_box(0));
return v___x_2764_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4___boxed(lean_object* v_msg_2771_, lean_object* v___y_2772_, lean_object* v___y_2773_, lean_object* v___y_2774_, lean_object* v___y_2775_){
_start:
{
lean_object* v_res_2776_; 
v_res_2776_ = l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4(v_msg_2771_, v___y_2772_, v___y_2773_, v___y_2774_);
lean_dec(v___y_2774_);
lean_dec_ref(v___y_2773_);
return v_res_2776_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1_spec__2___redArg(lean_object* v_a_2777_, lean_object* v_x_2778_){
_start:
{
if (lean_obj_tag(v_x_2778_) == 0)
{
uint8_t v___x_2779_; 
v___x_2779_ = 0;
return v___x_2779_;
}
else
{
lean_object* v_key_2780_; lean_object* v_tail_2781_; uint8_t v___x_2782_; 
v_key_2780_ = lean_ctor_get(v_x_2778_, 0);
v_tail_2781_ = lean_ctor_get(v_x_2778_, 2);
v___x_2782_ = l_Lean_instBEqFVarId_beq(v_key_2780_, v_a_2777_);
if (v___x_2782_ == 0)
{
v_x_2778_ = v_tail_2781_;
goto _start;
}
else
{
return v___x_2782_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1_spec__2___redArg___boxed(lean_object* v_a_2784_, lean_object* v_x_2785_){
_start:
{
uint8_t v_res_2786_; lean_object* v_r_2787_; 
v_res_2786_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1_spec__2___redArg(v_a_2784_, v_x_2785_);
lean_dec(v_x_2785_);
lean_dec(v_a_2784_);
v_r_2787_ = lean_box(v_res_2786_);
return v_r_2787_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__4_spec__6_spec__11___redArg(lean_object* v_x_2788_, lean_object* v_x_2789_){
_start:
{
if (lean_obj_tag(v_x_2789_) == 0)
{
return v_x_2788_;
}
else
{
lean_object* v_key_2790_; lean_object* v_value_2791_; lean_object* v_tail_2792_; lean_object* v___x_2794_; uint8_t v_isShared_2795_; uint8_t v_isSharedCheck_2815_; 
v_key_2790_ = lean_ctor_get(v_x_2789_, 0);
v_value_2791_ = lean_ctor_get(v_x_2789_, 1);
v_tail_2792_ = lean_ctor_get(v_x_2789_, 2);
v_isSharedCheck_2815_ = !lean_is_exclusive(v_x_2789_);
if (v_isSharedCheck_2815_ == 0)
{
v___x_2794_ = v_x_2789_;
v_isShared_2795_ = v_isSharedCheck_2815_;
goto v_resetjp_2793_;
}
else
{
lean_inc(v_tail_2792_);
lean_inc(v_value_2791_);
lean_inc(v_key_2790_);
lean_dec(v_x_2789_);
v___x_2794_ = lean_box(0);
v_isShared_2795_ = v_isSharedCheck_2815_;
goto v_resetjp_2793_;
}
v_resetjp_2793_:
{
lean_object* v___x_2796_; uint64_t v___x_2797_; uint64_t v___x_2798_; uint64_t v___x_2799_; uint64_t v_fold_2800_; uint64_t v___x_2801_; uint64_t v___x_2802_; uint64_t v___x_2803_; size_t v___x_2804_; size_t v___x_2805_; size_t v___x_2806_; size_t v___x_2807_; size_t v___x_2808_; lean_object* v___x_2809_; lean_object* v___x_2811_; 
v___x_2796_ = lean_array_get_size(v_x_2788_);
v___x_2797_ = l_Lean_instHashableFVarId_hash(v_key_2790_);
v___x_2798_ = 32ULL;
v___x_2799_ = lean_uint64_shift_right(v___x_2797_, v___x_2798_);
v_fold_2800_ = lean_uint64_xor(v___x_2797_, v___x_2799_);
v___x_2801_ = 16ULL;
v___x_2802_ = lean_uint64_shift_right(v_fold_2800_, v___x_2801_);
v___x_2803_ = lean_uint64_xor(v_fold_2800_, v___x_2802_);
v___x_2804_ = lean_uint64_to_usize(v___x_2803_);
v___x_2805_ = lean_usize_of_nat(v___x_2796_);
v___x_2806_ = ((size_t)1ULL);
v___x_2807_ = lean_usize_sub(v___x_2805_, v___x_2806_);
v___x_2808_ = lean_usize_land(v___x_2804_, v___x_2807_);
v___x_2809_ = lean_array_uget_borrowed(v_x_2788_, v___x_2808_);
lean_inc(v___x_2809_);
if (v_isShared_2795_ == 0)
{
lean_ctor_set(v___x_2794_, 2, v___x_2809_);
v___x_2811_ = v___x_2794_;
goto v_reusejp_2810_;
}
else
{
lean_object* v_reuseFailAlloc_2814_; 
v_reuseFailAlloc_2814_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2814_, 0, v_key_2790_);
lean_ctor_set(v_reuseFailAlloc_2814_, 1, v_value_2791_);
lean_ctor_set(v_reuseFailAlloc_2814_, 2, v___x_2809_);
v___x_2811_ = v_reuseFailAlloc_2814_;
goto v_reusejp_2810_;
}
v_reusejp_2810_:
{
lean_object* v___x_2812_; 
v___x_2812_ = lean_array_uset(v_x_2788_, v___x_2808_, v___x_2811_);
v_x_2788_ = v___x_2812_;
v_x_2789_ = v_tail_2792_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__4_spec__6___redArg(lean_object* v_i_2816_, lean_object* v_source_2817_, lean_object* v_target_2818_){
_start:
{
lean_object* v___x_2819_; uint8_t v___x_2820_; 
v___x_2819_ = lean_array_get_size(v_source_2817_);
v___x_2820_ = lean_nat_dec_lt(v_i_2816_, v___x_2819_);
if (v___x_2820_ == 0)
{
lean_dec_ref(v_source_2817_);
lean_dec(v_i_2816_);
return v_target_2818_;
}
else
{
lean_object* v_es_2821_; lean_object* v___x_2822_; lean_object* v_source_2823_; lean_object* v_target_2824_; lean_object* v___x_2825_; lean_object* v___x_2826_; 
v_es_2821_ = lean_array_fget(v_source_2817_, v_i_2816_);
v___x_2822_ = lean_box(0);
v_source_2823_ = lean_array_fset(v_source_2817_, v_i_2816_, v___x_2822_);
v_target_2824_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__4_spec__6_spec__11___redArg(v_target_2818_, v_es_2821_);
v___x_2825_ = lean_unsigned_to_nat(1u);
v___x_2826_ = lean_nat_add(v_i_2816_, v___x_2825_);
lean_dec(v_i_2816_);
v_i_2816_ = v___x_2826_;
v_source_2817_ = v_source_2823_;
v_target_2818_ = v_target_2824_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__4___redArg(lean_object* v_data_2828_){
_start:
{
lean_object* v___x_2829_; lean_object* v___x_2830_; lean_object* v_nbuckets_2831_; lean_object* v___x_2832_; lean_object* v___x_2833_; lean_object* v___x_2834_; lean_object* v___x_2835_; 
v___x_2829_ = lean_array_get_size(v_data_2828_);
v___x_2830_ = lean_unsigned_to_nat(2u);
v_nbuckets_2831_ = lean_nat_mul(v___x_2829_, v___x_2830_);
v___x_2832_ = lean_unsigned_to_nat(0u);
v___x_2833_ = lean_box(0);
v___x_2834_ = lean_mk_array(v_nbuckets_2831_, v___x_2833_);
v___x_2835_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__4_spec__6___redArg(v___x_2832_, v_data_2828_, v___x_2834_);
return v___x_2835_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2___redArg(lean_object* v_m_2836_, lean_object* v_a_2837_, lean_object* v_b_2838_){
_start:
{
lean_object* v_size_2839_; lean_object* v_buckets_2840_; lean_object* v___x_2841_; uint64_t v___x_2842_; uint64_t v___x_2843_; uint64_t v___x_2844_; uint64_t v_fold_2845_; uint64_t v___x_2846_; uint64_t v___x_2847_; uint64_t v___x_2848_; size_t v___x_2849_; size_t v___x_2850_; size_t v___x_2851_; size_t v___x_2852_; size_t v___x_2853_; lean_object* v_bkt_2854_; uint8_t v___x_2855_; 
v_size_2839_ = lean_ctor_get(v_m_2836_, 0);
v_buckets_2840_ = lean_ctor_get(v_m_2836_, 1);
v___x_2841_ = lean_array_get_size(v_buckets_2840_);
v___x_2842_ = l_Lean_instHashableFVarId_hash(v_a_2837_);
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
v_bkt_2854_ = lean_array_uget_borrowed(v_buckets_2840_, v___x_2853_);
v___x_2855_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1_spec__2___redArg(v_a_2837_, v_bkt_2854_);
if (v___x_2855_ == 0)
{
lean_object* v___x_2857_; uint8_t v_isShared_2858_; uint8_t v_isSharedCheck_2876_; 
lean_inc_ref(v_buckets_2840_);
lean_inc(v_size_2839_);
v_isSharedCheck_2876_ = !lean_is_exclusive(v_m_2836_);
if (v_isSharedCheck_2876_ == 0)
{
lean_object* v_unused_2877_; lean_object* v_unused_2878_; 
v_unused_2877_ = lean_ctor_get(v_m_2836_, 1);
lean_dec(v_unused_2877_);
v_unused_2878_ = lean_ctor_get(v_m_2836_, 0);
lean_dec(v_unused_2878_);
v___x_2857_ = v_m_2836_;
v_isShared_2858_ = v_isSharedCheck_2876_;
goto v_resetjp_2856_;
}
else
{
lean_dec(v_m_2836_);
v___x_2857_ = lean_box(0);
v_isShared_2858_ = v_isSharedCheck_2876_;
goto v_resetjp_2856_;
}
v_resetjp_2856_:
{
lean_object* v___x_2859_; lean_object* v_size_x27_2860_; lean_object* v___x_2861_; lean_object* v_buckets_x27_2862_; lean_object* v___x_2863_; lean_object* v___x_2864_; lean_object* v___x_2865_; lean_object* v___x_2866_; lean_object* v___x_2867_; uint8_t v___x_2868_; 
v___x_2859_ = lean_unsigned_to_nat(1u);
v_size_x27_2860_ = lean_nat_add(v_size_2839_, v___x_2859_);
lean_dec(v_size_2839_);
lean_inc(v_bkt_2854_);
v___x_2861_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2861_, 0, v_a_2837_);
lean_ctor_set(v___x_2861_, 1, v_b_2838_);
lean_ctor_set(v___x_2861_, 2, v_bkt_2854_);
v_buckets_x27_2862_ = lean_array_uset(v_buckets_2840_, v___x_2853_, v___x_2861_);
v___x_2863_ = lean_unsigned_to_nat(4u);
v___x_2864_ = lean_nat_mul(v_size_x27_2860_, v___x_2863_);
v___x_2865_ = lean_unsigned_to_nat(3u);
v___x_2866_ = lean_nat_div(v___x_2864_, v___x_2865_);
lean_dec(v___x_2864_);
v___x_2867_ = lean_array_get_size(v_buckets_x27_2862_);
v___x_2868_ = lean_nat_dec_le(v___x_2866_, v___x_2867_);
lean_dec(v___x_2866_);
if (v___x_2868_ == 0)
{
lean_object* v_val_2869_; lean_object* v___x_2871_; 
v_val_2869_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__4___redArg(v_buckets_x27_2862_);
if (v_isShared_2858_ == 0)
{
lean_ctor_set(v___x_2857_, 1, v_val_2869_);
lean_ctor_set(v___x_2857_, 0, v_size_x27_2860_);
v___x_2871_ = v___x_2857_;
goto v_reusejp_2870_;
}
else
{
lean_object* v_reuseFailAlloc_2872_; 
v_reuseFailAlloc_2872_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2872_, 0, v_size_x27_2860_);
lean_ctor_set(v_reuseFailAlloc_2872_, 1, v_val_2869_);
v___x_2871_ = v_reuseFailAlloc_2872_;
goto v_reusejp_2870_;
}
v_reusejp_2870_:
{
return v___x_2871_;
}
}
else
{
lean_object* v___x_2874_; 
if (v_isShared_2858_ == 0)
{
lean_ctor_set(v___x_2857_, 1, v_buckets_x27_2862_);
lean_ctor_set(v___x_2857_, 0, v_size_x27_2860_);
v___x_2874_ = v___x_2857_;
goto v_reusejp_2873_;
}
else
{
lean_object* v_reuseFailAlloc_2875_; 
v_reuseFailAlloc_2875_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2875_, 0, v_size_x27_2860_);
lean_ctor_set(v_reuseFailAlloc_2875_, 1, v_buckets_x27_2862_);
v___x_2874_ = v_reuseFailAlloc_2875_;
goto v_reusejp_2873_;
}
v_reusejp_2873_:
{
return v___x_2874_;
}
}
}
}
else
{
lean_dec(v_b_2838_);
lean_dec(v_a_2837_);
return v_m_2836_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1___redArg(lean_object* v_m_2879_, lean_object* v_a_2880_){
_start:
{
lean_object* v_buckets_2881_; lean_object* v___x_2882_; uint64_t v___x_2883_; uint64_t v___x_2884_; uint64_t v___x_2885_; uint64_t v_fold_2886_; uint64_t v___x_2887_; uint64_t v___x_2888_; uint64_t v___x_2889_; size_t v___x_2890_; size_t v___x_2891_; size_t v___x_2892_; size_t v___x_2893_; size_t v___x_2894_; lean_object* v___x_2895_; uint8_t v___x_2896_; 
v_buckets_2881_ = lean_ctor_get(v_m_2879_, 1);
v___x_2882_ = lean_array_get_size(v_buckets_2881_);
v___x_2883_ = l_Lean_instHashableFVarId_hash(v_a_2880_);
v___x_2884_ = 32ULL;
v___x_2885_ = lean_uint64_shift_right(v___x_2883_, v___x_2884_);
v_fold_2886_ = lean_uint64_xor(v___x_2883_, v___x_2885_);
v___x_2887_ = 16ULL;
v___x_2888_ = lean_uint64_shift_right(v_fold_2886_, v___x_2887_);
v___x_2889_ = lean_uint64_xor(v_fold_2886_, v___x_2888_);
v___x_2890_ = lean_uint64_to_usize(v___x_2889_);
v___x_2891_ = lean_usize_of_nat(v___x_2882_);
v___x_2892_ = ((size_t)1ULL);
v___x_2893_ = lean_usize_sub(v___x_2891_, v___x_2892_);
v___x_2894_ = lean_usize_land(v___x_2890_, v___x_2893_);
v___x_2895_ = lean_array_uget_borrowed(v_buckets_2881_, v___x_2894_);
v___x_2896_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1_spec__2___redArg(v_a_2880_, v___x_2895_);
return v___x_2896_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1___redArg___boxed(lean_object* v_m_2897_, lean_object* v_a_2898_){
_start:
{
uint8_t v_res_2899_; lean_object* v_r_2900_; 
v_res_2899_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1___redArg(v_m_2897_, v_a_2898_);
lean_dec(v_a_2898_);
lean_dec_ref(v_m_2897_);
v_r_2900_ = lean_box(v_res_2899_);
return v_r_2900_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__6_spec__9___redArg(lean_object* v_a_2901_, lean_object* v_x_2902_){
_start:
{
if (lean_obj_tag(v_x_2902_) == 0)
{
lean_object* v___x_2903_; 
v___x_2903_ = lean_box(0);
return v___x_2903_;
}
else
{
lean_object* v_key_2904_; lean_object* v_value_2905_; lean_object* v_tail_2906_; uint8_t v___x_2907_; 
v_key_2904_ = lean_ctor_get(v_x_2902_, 0);
v_value_2905_ = lean_ctor_get(v_x_2902_, 1);
v_tail_2906_ = lean_ctor_get(v_x_2902_, 2);
v___x_2907_ = lean_expr_eqv(v_key_2904_, v_a_2901_);
if (v___x_2907_ == 0)
{
v_x_2902_ = v_tail_2906_;
goto _start;
}
else
{
lean_object* v___x_2909_; 
lean_inc(v_value_2905_);
v___x_2909_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2909_, 0, v_value_2905_);
return v___x_2909_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__6_spec__9___redArg___boxed(lean_object* v_a_2910_, lean_object* v_x_2911_){
_start:
{
lean_object* v_res_2912_; 
v_res_2912_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__6_spec__9___redArg(v_a_2910_, v_x_2911_);
lean_dec(v_x_2911_);
lean_dec_ref(v_a_2910_);
return v_res_2912_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__6___redArg(lean_object* v_m_2913_, lean_object* v_a_2914_){
_start:
{
lean_object* v_buckets_2915_; lean_object* v___x_2916_; uint64_t v___x_2917_; uint64_t v___x_2918_; uint64_t v___x_2919_; uint64_t v_fold_2920_; uint64_t v___x_2921_; uint64_t v___x_2922_; uint64_t v___x_2923_; size_t v___x_2924_; size_t v___x_2925_; size_t v___x_2926_; size_t v___x_2927_; size_t v___x_2928_; lean_object* v___x_2929_; lean_object* v___x_2930_; 
v_buckets_2915_ = lean_ctor_get(v_m_2913_, 1);
v___x_2916_ = lean_array_get_size(v_buckets_2915_);
v___x_2917_ = l_Lean_Expr_hash(v_a_2914_);
v___x_2918_ = 32ULL;
v___x_2919_ = lean_uint64_shift_right(v___x_2917_, v___x_2918_);
v_fold_2920_ = lean_uint64_xor(v___x_2917_, v___x_2919_);
v___x_2921_ = 16ULL;
v___x_2922_ = lean_uint64_shift_right(v_fold_2920_, v___x_2921_);
v___x_2923_ = lean_uint64_xor(v_fold_2920_, v___x_2922_);
v___x_2924_ = lean_uint64_to_usize(v___x_2923_);
v___x_2925_ = lean_usize_of_nat(v___x_2916_);
v___x_2926_ = ((size_t)1ULL);
v___x_2927_ = lean_usize_sub(v___x_2925_, v___x_2926_);
v___x_2928_ = lean_usize_land(v___x_2924_, v___x_2927_);
v___x_2929_ = lean_array_uget_borrowed(v_buckets_2915_, v___x_2928_);
v___x_2930_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__6_spec__9___redArg(v_a_2914_, v___x_2929_);
return v___x_2930_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__6___redArg___boxed(lean_object* v_m_2931_, lean_object* v_a_2932_){
_start:
{
lean_object* v_res_2933_; 
v_res_2933_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__6___redArg(v_m_2931_, v_a_2932_);
lean_dec_ref(v_a_2932_);
lean_dec_ref(v_m_2931_);
return v_res_2933_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__13___redArg(lean_object* v_a_2934_, lean_object* v_b_2935_, lean_object* v_x_2936_){
_start:
{
if (lean_obj_tag(v_x_2936_) == 0)
{
lean_dec(v_b_2935_);
lean_dec_ref(v_a_2934_);
return v_x_2936_;
}
else
{
lean_object* v_key_2937_; lean_object* v_value_2938_; lean_object* v_tail_2939_; lean_object* v___x_2941_; uint8_t v_isShared_2942_; uint8_t v_isSharedCheck_2951_; 
v_key_2937_ = lean_ctor_get(v_x_2936_, 0);
v_value_2938_ = lean_ctor_get(v_x_2936_, 1);
v_tail_2939_ = lean_ctor_get(v_x_2936_, 2);
v_isSharedCheck_2951_ = !lean_is_exclusive(v_x_2936_);
if (v_isSharedCheck_2951_ == 0)
{
v___x_2941_ = v_x_2936_;
v_isShared_2942_ = v_isSharedCheck_2951_;
goto v_resetjp_2940_;
}
else
{
lean_inc(v_tail_2939_);
lean_inc(v_value_2938_);
lean_inc(v_key_2937_);
lean_dec(v_x_2936_);
v___x_2941_ = lean_box(0);
v_isShared_2942_ = v_isSharedCheck_2951_;
goto v_resetjp_2940_;
}
v_resetjp_2940_:
{
uint8_t v___x_2943_; 
v___x_2943_ = lean_expr_eqv(v_key_2937_, v_a_2934_);
if (v___x_2943_ == 0)
{
lean_object* v___x_2944_; lean_object* v___x_2946_; 
v___x_2944_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__13___redArg(v_a_2934_, v_b_2935_, v_tail_2939_);
if (v_isShared_2942_ == 0)
{
lean_ctor_set(v___x_2941_, 2, v___x_2944_);
v___x_2946_ = v___x_2941_;
goto v_reusejp_2945_;
}
else
{
lean_object* v_reuseFailAlloc_2947_; 
v_reuseFailAlloc_2947_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2947_, 0, v_key_2937_);
lean_ctor_set(v_reuseFailAlloc_2947_, 1, v_value_2938_);
lean_ctor_set(v_reuseFailAlloc_2947_, 2, v___x_2944_);
v___x_2946_ = v_reuseFailAlloc_2947_;
goto v_reusejp_2945_;
}
v_reusejp_2945_:
{
return v___x_2946_;
}
}
else
{
lean_object* v___x_2949_; 
lean_dec(v_value_2938_);
lean_dec(v_key_2937_);
if (v_isShared_2942_ == 0)
{
lean_ctor_set(v___x_2941_, 1, v_b_2935_);
lean_ctor_set(v___x_2941_, 0, v_a_2934_);
v___x_2949_ = v___x_2941_;
goto v_reusejp_2948_;
}
else
{
lean_object* v_reuseFailAlloc_2950_; 
v_reuseFailAlloc_2950_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2950_, 0, v_a_2934_);
lean_ctor_set(v_reuseFailAlloc_2950_, 1, v_b_2935_);
lean_ctor_set(v_reuseFailAlloc_2950_, 2, v_tail_2939_);
v___x_2949_ = v_reuseFailAlloc_2950_;
goto v_reusejp_2948_;
}
v_reusejp_2948_:
{
return v___x_2949_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__12_spec__17_spec__18___redArg(lean_object* v_x_2952_, lean_object* v_x_2953_){
_start:
{
if (lean_obj_tag(v_x_2953_) == 0)
{
return v_x_2952_;
}
else
{
lean_object* v_key_2954_; lean_object* v_value_2955_; lean_object* v_tail_2956_; lean_object* v___x_2958_; uint8_t v_isShared_2959_; uint8_t v_isSharedCheck_2979_; 
v_key_2954_ = lean_ctor_get(v_x_2953_, 0);
v_value_2955_ = lean_ctor_get(v_x_2953_, 1);
v_tail_2956_ = lean_ctor_get(v_x_2953_, 2);
v_isSharedCheck_2979_ = !lean_is_exclusive(v_x_2953_);
if (v_isSharedCheck_2979_ == 0)
{
v___x_2958_ = v_x_2953_;
v_isShared_2959_ = v_isSharedCheck_2979_;
goto v_resetjp_2957_;
}
else
{
lean_inc(v_tail_2956_);
lean_inc(v_value_2955_);
lean_inc(v_key_2954_);
lean_dec(v_x_2953_);
v___x_2958_ = lean_box(0);
v_isShared_2959_ = v_isSharedCheck_2979_;
goto v_resetjp_2957_;
}
v_resetjp_2957_:
{
lean_object* v___x_2960_; uint64_t v___x_2961_; uint64_t v___x_2962_; uint64_t v___x_2963_; uint64_t v_fold_2964_; uint64_t v___x_2965_; uint64_t v___x_2966_; uint64_t v___x_2967_; size_t v___x_2968_; size_t v___x_2969_; size_t v___x_2970_; size_t v___x_2971_; size_t v___x_2972_; lean_object* v___x_2973_; lean_object* v___x_2975_; 
v___x_2960_ = lean_array_get_size(v_x_2952_);
v___x_2961_ = l_Lean_Expr_hash(v_key_2954_);
v___x_2962_ = 32ULL;
v___x_2963_ = lean_uint64_shift_right(v___x_2961_, v___x_2962_);
v_fold_2964_ = lean_uint64_xor(v___x_2961_, v___x_2963_);
v___x_2965_ = 16ULL;
v___x_2966_ = lean_uint64_shift_right(v_fold_2964_, v___x_2965_);
v___x_2967_ = lean_uint64_xor(v_fold_2964_, v___x_2966_);
v___x_2968_ = lean_uint64_to_usize(v___x_2967_);
v___x_2969_ = lean_usize_of_nat(v___x_2960_);
v___x_2970_ = ((size_t)1ULL);
v___x_2971_ = lean_usize_sub(v___x_2969_, v___x_2970_);
v___x_2972_ = lean_usize_land(v___x_2968_, v___x_2971_);
v___x_2973_ = lean_array_uget_borrowed(v_x_2952_, v___x_2972_);
lean_inc(v___x_2973_);
if (v_isShared_2959_ == 0)
{
lean_ctor_set(v___x_2958_, 2, v___x_2973_);
v___x_2975_ = v___x_2958_;
goto v_reusejp_2974_;
}
else
{
lean_object* v_reuseFailAlloc_2978_; 
v_reuseFailAlloc_2978_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2978_, 0, v_key_2954_);
lean_ctor_set(v_reuseFailAlloc_2978_, 1, v_value_2955_);
lean_ctor_set(v_reuseFailAlloc_2978_, 2, v___x_2973_);
v___x_2975_ = v_reuseFailAlloc_2978_;
goto v_reusejp_2974_;
}
v_reusejp_2974_:
{
lean_object* v___x_2976_; 
v___x_2976_ = lean_array_uset(v_x_2952_, v___x_2972_, v___x_2975_);
v_x_2952_ = v___x_2976_;
v_x_2953_ = v_tail_2956_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__12_spec__17___redArg(lean_object* v_i_2980_, lean_object* v_source_2981_, lean_object* v_target_2982_){
_start:
{
lean_object* v___x_2983_; uint8_t v___x_2984_; 
v___x_2983_ = lean_array_get_size(v_source_2981_);
v___x_2984_ = lean_nat_dec_lt(v_i_2980_, v___x_2983_);
if (v___x_2984_ == 0)
{
lean_dec_ref(v_source_2981_);
lean_dec(v_i_2980_);
return v_target_2982_;
}
else
{
lean_object* v_es_2985_; lean_object* v___x_2986_; lean_object* v_source_2987_; lean_object* v_target_2988_; lean_object* v___x_2989_; lean_object* v___x_2990_; 
v_es_2985_ = lean_array_fget(v_source_2981_, v_i_2980_);
v___x_2986_ = lean_box(0);
v_source_2987_ = lean_array_fset(v_source_2981_, v_i_2980_, v___x_2986_);
v_target_2988_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__12_spec__17_spec__18___redArg(v_target_2982_, v_es_2985_);
v___x_2989_ = lean_unsigned_to_nat(1u);
v___x_2990_ = lean_nat_add(v_i_2980_, v___x_2989_);
lean_dec(v_i_2980_);
v_i_2980_ = v___x_2990_;
v_source_2981_ = v_source_2987_;
v_target_2982_ = v_target_2988_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__12___redArg(lean_object* v_data_2992_){
_start:
{
lean_object* v___x_2993_; lean_object* v___x_2994_; lean_object* v_nbuckets_2995_; lean_object* v___x_2996_; lean_object* v___x_2997_; lean_object* v___x_2998_; lean_object* v___x_2999_; 
v___x_2993_ = lean_array_get_size(v_data_2992_);
v___x_2994_ = lean_unsigned_to_nat(2u);
v_nbuckets_2995_ = lean_nat_mul(v___x_2993_, v___x_2994_);
v___x_2996_ = lean_unsigned_to_nat(0u);
v___x_2997_ = lean_box(0);
v___x_2998_ = lean_mk_array(v_nbuckets_2995_, v___x_2997_);
v___x_2999_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__12_spec__17___redArg(v___x_2996_, v_data_2992_, v___x_2998_);
return v___x_2999_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__11___redArg(lean_object* v_a_3000_, lean_object* v_x_3001_){
_start:
{
if (lean_obj_tag(v_x_3001_) == 0)
{
uint8_t v___x_3002_; 
v___x_3002_ = 0;
return v___x_3002_;
}
else
{
lean_object* v_key_3003_; lean_object* v_tail_3004_; uint8_t v___x_3005_; 
v_key_3003_ = lean_ctor_get(v_x_3001_, 0);
v_tail_3004_ = lean_ctor_get(v_x_3001_, 2);
v___x_3005_ = lean_expr_eqv(v_key_3003_, v_a_3000_);
if (v___x_3005_ == 0)
{
v_x_3001_ = v_tail_3004_;
goto _start;
}
else
{
return v___x_3005_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__11___redArg___boxed(lean_object* v_a_3007_, lean_object* v_x_3008_){
_start:
{
uint8_t v_res_3009_; lean_object* v_r_3010_; 
v_res_3009_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__11___redArg(v_a_3007_, v_x_3008_);
lean_dec(v_x_3008_);
lean_dec_ref(v_a_3007_);
v_r_3010_ = lean_box(v_res_3009_);
return v_r_3010_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7___redArg(lean_object* v_m_3011_, lean_object* v_a_3012_, lean_object* v_b_3013_){
_start:
{
lean_object* v_size_3014_; lean_object* v_buckets_3015_; lean_object* v___x_3017_; uint8_t v_isShared_3018_; uint8_t v_isSharedCheck_3058_; 
v_size_3014_ = lean_ctor_get(v_m_3011_, 0);
v_buckets_3015_ = lean_ctor_get(v_m_3011_, 1);
v_isSharedCheck_3058_ = !lean_is_exclusive(v_m_3011_);
if (v_isSharedCheck_3058_ == 0)
{
v___x_3017_ = v_m_3011_;
v_isShared_3018_ = v_isSharedCheck_3058_;
goto v_resetjp_3016_;
}
else
{
lean_inc(v_buckets_3015_);
lean_inc(v_size_3014_);
lean_dec(v_m_3011_);
v___x_3017_ = lean_box(0);
v_isShared_3018_ = v_isSharedCheck_3058_;
goto v_resetjp_3016_;
}
v_resetjp_3016_:
{
lean_object* v___x_3019_; uint64_t v___x_3020_; uint64_t v___x_3021_; uint64_t v___x_3022_; uint64_t v_fold_3023_; uint64_t v___x_3024_; uint64_t v___x_3025_; uint64_t v___x_3026_; size_t v___x_3027_; size_t v___x_3028_; size_t v___x_3029_; size_t v___x_3030_; size_t v___x_3031_; lean_object* v_bkt_3032_; uint8_t v___x_3033_; 
v___x_3019_ = lean_array_get_size(v_buckets_3015_);
v___x_3020_ = l_Lean_Expr_hash(v_a_3012_);
v___x_3021_ = 32ULL;
v___x_3022_ = lean_uint64_shift_right(v___x_3020_, v___x_3021_);
v_fold_3023_ = lean_uint64_xor(v___x_3020_, v___x_3022_);
v___x_3024_ = 16ULL;
v___x_3025_ = lean_uint64_shift_right(v_fold_3023_, v___x_3024_);
v___x_3026_ = lean_uint64_xor(v_fold_3023_, v___x_3025_);
v___x_3027_ = lean_uint64_to_usize(v___x_3026_);
v___x_3028_ = lean_usize_of_nat(v___x_3019_);
v___x_3029_ = ((size_t)1ULL);
v___x_3030_ = lean_usize_sub(v___x_3028_, v___x_3029_);
v___x_3031_ = lean_usize_land(v___x_3027_, v___x_3030_);
v_bkt_3032_ = lean_array_uget_borrowed(v_buckets_3015_, v___x_3031_);
v___x_3033_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__11___redArg(v_a_3012_, v_bkt_3032_);
if (v___x_3033_ == 0)
{
lean_object* v___x_3034_; lean_object* v_size_x27_3035_; lean_object* v___x_3036_; lean_object* v_buckets_x27_3037_; lean_object* v___x_3038_; lean_object* v___x_3039_; lean_object* v___x_3040_; lean_object* v___x_3041_; lean_object* v___x_3042_; uint8_t v___x_3043_; 
v___x_3034_ = lean_unsigned_to_nat(1u);
v_size_x27_3035_ = lean_nat_add(v_size_3014_, v___x_3034_);
lean_dec(v_size_3014_);
lean_inc(v_bkt_3032_);
v___x_3036_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3036_, 0, v_a_3012_);
lean_ctor_set(v___x_3036_, 1, v_b_3013_);
lean_ctor_set(v___x_3036_, 2, v_bkt_3032_);
v_buckets_x27_3037_ = lean_array_uset(v_buckets_3015_, v___x_3031_, v___x_3036_);
v___x_3038_ = lean_unsigned_to_nat(4u);
v___x_3039_ = lean_nat_mul(v_size_x27_3035_, v___x_3038_);
v___x_3040_ = lean_unsigned_to_nat(3u);
v___x_3041_ = lean_nat_div(v___x_3039_, v___x_3040_);
lean_dec(v___x_3039_);
v___x_3042_ = lean_array_get_size(v_buckets_x27_3037_);
v___x_3043_ = lean_nat_dec_le(v___x_3041_, v___x_3042_);
lean_dec(v___x_3041_);
if (v___x_3043_ == 0)
{
lean_object* v_val_3044_; lean_object* v___x_3046_; 
v_val_3044_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__12___redArg(v_buckets_x27_3037_);
if (v_isShared_3018_ == 0)
{
lean_ctor_set(v___x_3017_, 1, v_val_3044_);
lean_ctor_set(v___x_3017_, 0, v_size_x27_3035_);
v___x_3046_ = v___x_3017_;
goto v_reusejp_3045_;
}
else
{
lean_object* v_reuseFailAlloc_3047_; 
v_reuseFailAlloc_3047_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3047_, 0, v_size_x27_3035_);
lean_ctor_set(v_reuseFailAlloc_3047_, 1, v_val_3044_);
v___x_3046_ = v_reuseFailAlloc_3047_;
goto v_reusejp_3045_;
}
v_reusejp_3045_:
{
return v___x_3046_;
}
}
else
{
lean_object* v___x_3049_; 
if (v_isShared_3018_ == 0)
{
lean_ctor_set(v___x_3017_, 1, v_buckets_x27_3037_);
lean_ctor_set(v___x_3017_, 0, v_size_x27_3035_);
v___x_3049_ = v___x_3017_;
goto v_reusejp_3048_;
}
else
{
lean_object* v_reuseFailAlloc_3050_; 
v_reuseFailAlloc_3050_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3050_, 0, v_size_x27_3035_);
lean_ctor_set(v_reuseFailAlloc_3050_, 1, v_buckets_x27_3037_);
v___x_3049_ = v_reuseFailAlloc_3050_;
goto v_reusejp_3048_;
}
v_reusejp_3048_:
{
return v___x_3049_;
}
}
}
else
{
lean_object* v___x_3051_; lean_object* v_buckets_x27_3052_; lean_object* v___x_3053_; lean_object* v___x_3054_; lean_object* v___x_3056_; 
lean_inc(v_bkt_3032_);
v___x_3051_ = lean_box(0);
v_buckets_x27_3052_ = lean_array_uset(v_buckets_3015_, v___x_3031_, v___x_3051_);
v___x_3053_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__13___redArg(v_a_3012_, v_b_3013_, v_bkt_3032_);
v___x_3054_ = lean_array_uset(v_buckets_x27_3052_, v___x_3031_, v___x_3053_);
if (v_isShared_3018_ == 0)
{
lean_ctor_set(v___x_3017_, 1, v___x_3054_);
v___x_3056_ = v___x_3017_;
goto v_reusejp_3055_;
}
else
{
lean_object* v_reuseFailAlloc_3057_; 
v_reuseFailAlloc_3057_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3057_, 0, v_size_3014_);
lean_ctor_set(v_reuseFailAlloc_3057_, 1, v___x_3054_);
v___x_3056_ = v_reuseFailAlloc_3057_;
goto v_reusejp_3055_;
}
v_reusejp_3055_:
{
return v___x_3056_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3(lean_object* v_g_3059_, lean_object* v_e_3060_, lean_object* v_a_3061_, lean_object* v___y_3062_, lean_object* v___y_3063_, lean_object* v___y_3064_){
_start:
{
lean_object* v_a_3067_; lean_object* v_fst_3068_; lean_object* v___y_3074_; lean_object* v___x_3077_; lean_object* v___x_3078_; 
v___x_3077_ = lean_st_ref_get(v_a_3061_);
v___x_3078_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__6___redArg(v___x_3077_, v_e_3060_);
lean_dec(v___x_3077_);
if (lean_obj_tag(v___x_3078_) == 0)
{
lean_object* v___x_3079_; 
lean_inc_ref(v_g_3059_);
lean_inc(v___y_3064_);
lean_inc_ref(v___y_3063_);
lean_inc_ref(v_e_3060_);
v___x_3079_ = lean_apply_5(v_g_3059_, v_e_3060_, v___y_3062_, v___y_3063_, v___y_3064_, lean_box(0));
if (lean_obj_tag(v___x_3079_) == 0)
{
lean_object* v_a_3080_; lean_object* v_fst_3081_; lean_object* v_snd_3082_; lean_object* v___x_3084_; uint8_t v_isShared_3085_; uint8_t v_isSharedCheck_3127_; 
v_a_3080_ = lean_ctor_get(v___x_3079_, 0);
lean_inc(v_a_3080_);
lean_dec_ref(v___x_3079_);
v_fst_3081_ = lean_ctor_get(v_a_3080_, 0);
v_snd_3082_ = lean_ctor_get(v_a_3080_, 1);
v_isSharedCheck_3127_ = !lean_is_exclusive(v_a_3080_);
if (v_isSharedCheck_3127_ == 0)
{
v___x_3084_ = v_a_3080_;
v_isShared_3085_ = v_isSharedCheck_3127_;
goto v_resetjp_3083_;
}
else
{
lean_inc(v_snd_3082_);
lean_inc(v_fst_3081_);
lean_dec(v_a_3080_);
v___x_3084_ = lean_box(0);
v_isShared_3085_ = v_isSharedCheck_3127_;
goto v_resetjp_3083_;
}
v_resetjp_3083_:
{
lean_object* v_d_3087_; lean_object* v_b_3088_; lean_object* v___y_3089_; uint8_t v___x_3094_; 
v___x_3094_ = lean_unbox(v_fst_3081_);
lean_dec(v_fst_3081_);
if (v___x_3094_ == 0)
{
lean_object* v___x_3095_; lean_object* v___x_3097_; 
lean_dec_ref(v_g_3059_);
v___x_3095_ = lean_box(0);
if (v_isShared_3085_ == 0)
{
lean_ctor_set(v___x_3084_, 0, v___x_3095_);
v___x_3097_ = v___x_3084_;
goto v_reusejp_3096_;
}
else
{
lean_object* v_reuseFailAlloc_3098_; 
v_reuseFailAlloc_3098_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3098_, 0, v___x_3095_);
lean_ctor_set(v_reuseFailAlloc_3098_, 1, v_snd_3082_);
v___x_3097_ = v_reuseFailAlloc_3098_;
goto v_reusejp_3096_;
}
v_reusejp_3096_:
{
v_a_3067_ = v___x_3097_;
v_fst_3068_ = v___x_3095_;
goto v___jp_3066_;
}
}
else
{
switch(lean_obj_tag(v_e_3060_))
{
case 7:
{
lean_object* v_binderType_3099_; lean_object* v_body_3100_; 
lean_del_object(v___x_3084_);
v_binderType_3099_ = lean_ctor_get(v_e_3060_, 1);
v_body_3100_ = lean_ctor_get(v_e_3060_, 2);
lean_inc_ref(v_body_3100_);
lean_inc_ref(v_binderType_3099_);
v_d_3087_ = v_binderType_3099_;
v_b_3088_ = v_body_3100_;
v___y_3089_ = v_a_3061_;
goto v___jp_3086_;
}
case 6:
{
lean_object* v_binderType_3101_; lean_object* v_body_3102_; 
lean_del_object(v___x_3084_);
v_binderType_3101_ = lean_ctor_get(v_e_3060_, 1);
v_body_3102_ = lean_ctor_get(v_e_3060_, 2);
lean_inc_ref(v_body_3102_);
lean_inc_ref(v_binderType_3101_);
v_d_3087_ = v_binderType_3101_;
v_b_3088_ = v_body_3102_;
v___y_3089_ = v_a_3061_;
goto v___jp_3086_;
}
case 8:
{
lean_object* v_type_3103_; lean_object* v_value_3104_; lean_object* v_body_3105_; lean_object* v___x_3106_; 
lean_del_object(v___x_3084_);
v_type_3103_ = lean_ctor_get(v_e_3060_, 1);
v_value_3104_ = lean_ctor_get(v_e_3060_, 2);
v_body_3105_ = lean_ctor_get(v_e_3060_, 3);
lean_inc_ref(v_type_3103_);
lean_inc_ref(v_g_3059_);
v___x_3106_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3(v_g_3059_, v_type_3103_, v_a_3061_, v_snd_3082_, v___y_3063_, v___y_3064_);
if (lean_obj_tag(v___x_3106_) == 0)
{
lean_object* v_a_3107_; lean_object* v_snd_3108_; lean_object* v___x_3109_; 
v_a_3107_ = lean_ctor_get(v___x_3106_, 0);
lean_inc(v_a_3107_);
lean_dec_ref(v___x_3106_);
v_snd_3108_ = lean_ctor_get(v_a_3107_, 1);
lean_inc(v_snd_3108_);
lean_dec(v_a_3107_);
lean_inc_ref(v_value_3104_);
lean_inc_ref(v_g_3059_);
v___x_3109_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3(v_g_3059_, v_value_3104_, v_a_3061_, v_snd_3108_, v___y_3063_, v___y_3064_);
if (lean_obj_tag(v___x_3109_) == 0)
{
lean_object* v_a_3110_; lean_object* v_snd_3111_; lean_object* v___x_3112_; 
v_a_3110_ = lean_ctor_get(v___x_3109_, 0);
lean_inc(v_a_3110_);
lean_dec_ref(v___x_3109_);
v_snd_3111_ = lean_ctor_get(v_a_3110_, 1);
lean_inc(v_snd_3111_);
lean_dec(v_a_3110_);
lean_inc_ref(v_body_3105_);
v___x_3112_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3(v_g_3059_, v_body_3105_, v_a_3061_, v_snd_3111_, v___y_3063_, v___y_3064_);
v___y_3074_ = v___x_3112_;
goto v___jp_3073_;
}
else
{
lean_dec_ref(v_g_3059_);
v___y_3074_ = v___x_3109_;
goto v___jp_3073_;
}
}
else
{
lean_dec_ref(v_g_3059_);
v___y_3074_ = v___x_3106_;
goto v___jp_3073_;
}
}
case 5:
{
lean_object* v_fn_3113_; lean_object* v_arg_3114_; lean_object* v___x_3115_; 
lean_del_object(v___x_3084_);
v_fn_3113_ = lean_ctor_get(v_e_3060_, 0);
v_arg_3114_ = lean_ctor_get(v_e_3060_, 1);
lean_inc_ref(v_fn_3113_);
lean_inc_ref(v_g_3059_);
v___x_3115_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3(v_g_3059_, v_fn_3113_, v_a_3061_, v_snd_3082_, v___y_3063_, v___y_3064_);
if (lean_obj_tag(v___x_3115_) == 0)
{
lean_object* v_a_3116_; lean_object* v_snd_3117_; lean_object* v___x_3118_; 
v_a_3116_ = lean_ctor_get(v___x_3115_, 0);
lean_inc(v_a_3116_);
lean_dec_ref(v___x_3115_);
v_snd_3117_ = lean_ctor_get(v_a_3116_, 1);
lean_inc(v_snd_3117_);
lean_dec(v_a_3116_);
lean_inc_ref(v_arg_3114_);
v___x_3118_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3(v_g_3059_, v_arg_3114_, v_a_3061_, v_snd_3117_, v___y_3063_, v___y_3064_);
v___y_3074_ = v___x_3118_;
goto v___jp_3073_;
}
else
{
lean_dec_ref(v_g_3059_);
v___y_3074_ = v___x_3115_;
goto v___jp_3073_;
}
}
case 10:
{
lean_object* v_expr_3119_; lean_object* v___x_3120_; 
lean_del_object(v___x_3084_);
v_expr_3119_ = lean_ctor_get(v_e_3060_, 1);
lean_inc_ref(v_expr_3119_);
v___x_3120_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3(v_g_3059_, v_expr_3119_, v_a_3061_, v_snd_3082_, v___y_3063_, v___y_3064_);
v___y_3074_ = v___x_3120_;
goto v___jp_3073_;
}
case 11:
{
lean_object* v_struct_3121_; lean_object* v___x_3122_; 
lean_del_object(v___x_3084_);
v_struct_3121_ = lean_ctor_get(v_e_3060_, 2);
lean_inc_ref(v_struct_3121_);
v___x_3122_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3(v_g_3059_, v_struct_3121_, v_a_3061_, v_snd_3082_, v___y_3063_, v___y_3064_);
v___y_3074_ = v___x_3122_;
goto v___jp_3073_;
}
default: 
{
lean_object* v___x_3123_; lean_object* v___x_3125_; 
lean_dec_ref(v_g_3059_);
v___x_3123_ = lean_box(0);
if (v_isShared_3085_ == 0)
{
lean_ctor_set(v___x_3084_, 0, v___x_3123_);
v___x_3125_ = v___x_3084_;
goto v_reusejp_3124_;
}
else
{
lean_object* v_reuseFailAlloc_3126_; 
v_reuseFailAlloc_3126_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3126_, 0, v___x_3123_);
lean_ctor_set(v_reuseFailAlloc_3126_, 1, v_snd_3082_);
v___x_3125_ = v_reuseFailAlloc_3126_;
goto v_reusejp_3124_;
}
v_reusejp_3124_:
{
v_a_3067_ = v___x_3125_;
v_fst_3068_ = v___x_3123_;
goto v___jp_3066_;
}
}
}
}
v___jp_3086_:
{
lean_object* v___x_3090_; 
lean_inc_ref(v_g_3059_);
v___x_3090_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3(v_g_3059_, v_d_3087_, v___y_3089_, v_snd_3082_, v___y_3063_, v___y_3064_);
if (lean_obj_tag(v___x_3090_) == 0)
{
lean_object* v_a_3091_; lean_object* v_snd_3092_; lean_object* v___x_3093_; 
v_a_3091_ = lean_ctor_get(v___x_3090_, 0);
lean_inc(v_a_3091_);
lean_dec_ref(v___x_3090_);
v_snd_3092_ = lean_ctor_get(v_a_3091_, 1);
lean_inc(v_snd_3092_);
lean_dec(v_a_3091_);
v___x_3093_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3(v_g_3059_, v_b_3088_, v___y_3089_, v_snd_3092_, v___y_3063_, v___y_3064_);
v___y_3074_ = v___x_3093_;
goto v___jp_3073_;
}
else
{
lean_dec_ref(v_b_3088_);
lean_dec_ref(v_g_3059_);
v___y_3074_ = v___x_3090_;
goto v___jp_3073_;
}
}
}
}
else
{
lean_object* v_a_3128_; lean_object* v___x_3130_; uint8_t v_isShared_3131_; uint8_t v_isSharedCheck_3135_; 
lean_dec_ref(v_e_3060_);
lean_dec_ref(v_g_3059_);
v_a_3128_ = lean_ctor_get(v___x_3079_, 0);
v_isSharedCheck_3135_ = !lean_is_exclusive(v___x_3079_);
if (v_isSharedCheck_3135_ == 0)
{
v___x_3130_ = v___x_3079_;
v_isShared_3131_ = v_isSharedCheck_3135_;
goto v_resetjp_3129_;
}
else
{
lean_inc(v_a_3128_);
lean_dec(v___x_3079_);
v___x_3130_ = lean_box(0);
v_isShared_3131_ = v_isSharedCheck_3135_;
goto v_resetjp_3129_;
}
v_resetjp_3129_:
{
lean_object* v___x_3133_; 
if (v_isShared_3131_ == 0)
{
v___x_3133_ = v___x_3130_;
goto v_reusejp_3132_;
}
else
{
lean_object* v_reuseFailAlloc_3134_; 
v_reuseFailAlloc_3134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3134_, 0, v_a_3128_);
v___x_3133_ = v_reuseFailAlloc_3134_;
goto v_reusejp_3132_;
}
v_reusejp_3132_:
{
return v___x_3133_;
}
}
}
}
else
{
lean_object* v_val_3136_; lean_object* v___x_3138_; uint8_t v_isShared_3139_; uint8_t v_isSharedCheck_3144_; 
lean_dec_ref(v_e_3060_);
lean_dec_ref(v_g_3059_);
v_val_3136_ = lean_ctor_get(v___x_3078_, 0);
v_isSharedCheck_3144_ = !lean_is_exclusive(v___x_3078_);
if (v_isSharedCheck_3144_ == 0)
{
v___x_3138_ = v___x_3078_;
v_isShared_3139_ = v_isSharedCheck_3144_;
goto v_resetjp_3137_;
}
else
{
lean_inc(v_val_3136_);
lean_dec(v___x_3078_);
v___x_3138_ = lean_box(0);
v_isShared_3139_ = v_isSharedCheck_3144_;
goto v_resetjp_3137_;
}
v_resetjp_3137_:
{
lean_object* v___x_3140_; lean_object* v___x_3142_; 
v___x_3140_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3140_, 0, v_val_3136_);
lean_ctor_set(v___x_3140_, 1, v___y_3062_);
if (v_isShared_3139_ == 0)
{
lean_ctor_set_tag(v___x_3138_, 0);
lean_ctor_set(v___x_3138_, 0, v___x_3140_);
v___x_3142_ = v___x_3138_;
goto v_reusejp_3141_;
}
else
{
lean_object* v_reuseFailAlloc_3143_; 
v_reuseFailAlloc_3143_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3143_, 0, v___x_3140_);
v___x_3142_ = v_reuseFailAlloc_3143_;
goto v_reusejp_3141_;
}
v_reusejp_3141_:
{
return v___x_3142_;
}
}
}
v___jp_3066_:
{
lean_object* v___x_3069_; lean_object* v___x_3070_; lean_object* v___x_3071_; lean_object* v___x_3072_; 
v___x_3069_ = lean_st_ref_take(v_a_3061_);
v___x_3070_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7___redArg(v___x_3069_, v_e_3060_, v_fst_3068_);
v___x_3071_ = lean_st_ref_set(v_a_3061_, v___x_3070_);
v___x_3072_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3072_, 0, v_a_3067_);
return v___x_3072_;
}
v___jp_3073_:
{
if (lean_obj_tag(v___y_3074_) == 0)
{
lean_object* v_a_3075_; lean_object* v_fst_3076_; 
v_a_3075_ = lean_ctor_get(v___y_3074_, 0);
lean_inc(v_a_3075_);
lean_dec_ref(v___y_3074_);
v_fst_3076_ = lean_ctor_get(v_a_3075_, 0);
lean_inc(v_fst_3076_);
v_a_3067_ = v_a_3075_;
v_fst_3068_ = v_fst_3076_;
goto v___jp_3066_;
}
else
{
lean_dec_ref(v_e_3060_);
return v___y_3074_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3___boxed(lean_object* v_g_3145_, lean_object* v_e_3146_, lean_object* v_a_3147_, lean_object* v___y_3148_, lean_object* v___y_3149_, lean_object* v___y_3150_, lean_object* v___y_3151_){
_start:
{
lean_object* v_res_3152_; 
v_res_3152_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3(v_g_3145_, v_e_3146_, v_a_3147_, v___y_3148_, v___y_3149_, v___y_3150_);
lean_dec(v___y_3150_);
lean_dec_ref(v___y_3149_);
lean_dec(v_a_3147_);
return v_res_3152_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__0(void){
_start:
{
lean_object* v___x_3153_; 
v___x_3153_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_3153_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__1(void){
_start:
{
lean_object* v___x_3154_; lean_object* v___x_3155_; 
v___x_3154_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__0);
v___x_3155_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3155_, 0, v___x_3154_);
return v___x_3155_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__2(void){
_start:
{
lean_object* v___x_3156_; lean_object* v___x_3157_; lean_object* v___x_3158_; 
v___x_3156_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__1);
v___x_3157_ = lean_unsigned_to_nat(0u);
v___x_3158_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_3158_, 0, v___x_3157_);
lean_ctor_set(v___x_3158_, 1, v___x_3157_);
lean_ctor_set(v___x_3158_, 2, v___x_3157_);
lean_ctor_set(v___x_3158_, 3, v___x_3157_);
lean_ctor_set(v___x_3158_, 4, v___x_3156_);
lean_ctor_set(v___x_3158_, 5, v___x_3156_);
lean_ctor_set(v___x_3158_, 6, v___x_3156_);
lean_ctor_set(v___x_3158_, 7, v___x_3156_);
lean_ctor_set(v___x_3158_, 8, v___x_3156_);
lean_ctor_set(v___x_3158_, 9, v___x_3156_);
return v___x_3158_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__3(void){
_start:
{
lean_object* v___x_3159_; lean_object* v___x_3160_; lean_object* v___x_3161_; 
v___x_3159_ = lean_unsigned_to_nat(32u);
v___x_3160_ = lean_mk_empty_array_with_capacity(v___x_3159_);
v___x_3161_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3161_, 0, v___x_3160_);
return v___x_3161_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__4(void){
_start:
{
size_t v___x_3162_; lean_object* v___x_3163_; lean_object* v___x_3164_; lean_object* v___x_3165_; lean_object* v___x_3166_; lean_object* v___x_3167_; 
v___x_3162_ = ((size_t)5ULL);
v___x_3163_ = lean_unsigned_to_nat(0u);
v___x_3164_ = lean_unsigned_to_nat(32u);
v___x_3165_ = lean_mk_empty_array_with_capacity(v___x_3164_);
v___x_3166_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__3);
v___x_3167_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3167_, 0, v___x_3166_);
lean_ctor_set(v___x_3167_, 1, v___x_3165_);
lean_ctor_set(v___x_3167_, 2, v___x_3163_);
lean_ctor_set(v___x_3167_, 3, v___x_3163_);
lean_ctor_set_usize(v___x_3167_, 4, v___x_3162_);
return v___x_3167_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__5(void){
_start:
{
lean_object* v___x_3168_; lean_object* v___x_3169_; lean_object* v___x_3170_; lean_object* v___x_3171_; 
v___x_3168_ = lean_box(1);
v___x_3169_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__4);
v___x_3170_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__1);
v___x_3171_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3171_, 0, v___x_3170_);
lean_ctor_set(v___x_3171_, 1, v___x_3169_);
lean_ctor_set(v___x_3171_, 2, v___x_3168_);
return v___x_3171_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10(lean_object* v_msgData_3172_, lean_object* v___y_3173_, lean_object* v___y_3174_){
_start:
{
lean_object* v___x_3176_; lean_object* v_env_3177_; lean_object* v_options_3178_; lean_object* v___x_3179_; lean_object* v___x_3180_; lean_object* v___x_3181_; lean_object* v___x_3182_; lean_object* v___x_3183_; 
v___x_3176_ = lean_st_ref_get(v___y_3174_);
v_env_3177_ = lean_ctor_get(v___x_3176_, 0);
lean_inc_ref(v_env_3177_);
lean_dec(v___x_3176_);
v_options_3178_ = lean_ctor_get(v___y_3173_, 2);
v___x_3179_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__2);
v___x_3180_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__5);
lean_inc_ref(v_options_3178_);
v___x_3181_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3181_, 0, v_env_3177_);
lean_ctor_set(v___x_3181_, 1, v___x_3179_);
lean_ctor_set(v___x_3181_, 2, v___x_3180_);
lean_ctor_set(v___x_3181_, 3, v_options_3178_);
v___x_3182_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_3182_, 0, v___x_3181_);
lean_ctor_set(v___x_3182_, 1, v_msgData_3172_);
v___x_3183_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3183_, 0, v___x_3182_);
return v___x_3183_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___boxed(lean_object* v_msgData_3184_, lean_object* v___y_3185_, lean_object* v___y_3186_, lean_object* v___y_3187_){
_start:
{
lean_object* v_res_3188_; 
v_res_3188_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10(v_msgData_3184_, v___y_3185_, v___y_3186_);
lean_dec(v___y_3186_);
lean_dec_ref(v___y_3185_);
return v_res_3188_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5___redArg(lean_object* v_msg_3189_, lean_object* v___y_3190_, lean_object* v___y_3191_){
_start:
{
lean_object* v_ref_3193_; lean_object* v___x_3194_; lean_object* v_a_3195_; lean_object* v___x_3197_; uint8_t v_isShared_3198_; uint8_t v_isSharedCheck_3203_; 
v_ref_3193_ = lean_ctor_get(v___y_3190_, 5);
v___x_3194_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10(v_msg_3189_, v___y_3190_, v___y_3191_);
v_a_3195_ = lean_ctor_get(v___x_3194_, 0);
v_isSharedCheck_3203_ = !lean_is_exclusive(v___x_3194_);
if (v_isSharedCheck_3203_ == 0)
{
v___x_3197_ = v___x_3194_;
v_isShared_3198_ = v_isSharedCheck_3203_;
goto v_resetjp_3196_;
}
else
{
lean_inc(v_a_3195_);
lean_dec(v___x_3194_);
v___x_3197_ = lean_box(0);
v_isShared_3198_ = v_isSharedCheck_3203_;
goto v_resetjp_3196_;
}
v_resetjp_3196_:
{
lean_object* v___x_3199_; lean_object* v___x_3201_; 
lean_inc(v_ref_3193_);
v___x_3199_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3199_, 0, v_ref_3193_);
lean_ctor_set(v___x_3199_, 1, v_a_3195_);
if (v_isShared_3198_ == 0)
{
lean_ctor_set_tag(v___x_3197_, 1);
lean_ctor_set(v___x_3197_, 0, v___x_3199_);
v___x_3201_ = v___x_3197_;
goto v_reusejp_3200_;
}
else
{
lean_object* v_reuseFailAlloc_3202_; 
v_reuseFailAlloc_3202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3202_, 0, v___x_3199_);
v___x_3201_ = v_reuseFailAlloc_3202_;
goto v_reusejp_3200_;
}
v_reusejp_3200_:
{
return v___x_3201_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5___redArg___boxed(lean_object* v_msg_3204_, lean_object* v___y_3205_, lean_object* v___y_3206_, lean_object* v___y_3207_){
_start:
{
lean_object* v_res_3208_; 
v_res_3208_ = l_Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5___redArg(v_msg_3204_, v___y_3205_, v___y_3206_);
lean_dec(v___y_3206_);
lean_dec_ref(v___y_3205_);
return v_res_3208_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6___closed__0(void){
_start:
{
lean_object* v___x_3209_; double v___x_3210_; 
v___x_3209_ = lean_unsigned_to_nat(0u);
v___x_3210_ = lean_float_of_nat(v___x_3209_);
return v___x_3210_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6(lean_object* v_cls_3214_, lean_object* v_msg_3215_, lean_object* v___y_3216_, lean_object* v___y_3217_, lean_object* v___y_3218_){
_start:
{
lean_object* v_ref_3220_; lean_object* v___x_3221_; lean_object* v_a_3222_; lean_object* v___x_3224_; uint8_t v_isShared_3225_; uint8_t v_isSharedCheck_3268_; 
v_ref_3220_ = lean_ctor_get(v___y_3217_, 5);
v___x_3221_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10(v_msg_3215_, v___y_3217_, v___y_3218_);
v_a_3222_ = lean_ctor_get(v___x_3221_, 0);
v_isSharedCheck_3268_ = !lean_is_exclusive(v___x_3221_);
if (v_isSharedCheck_3268_ == 0)
{
v___x_3224_ = v___x_3221_;
v_isShared_3225_ = v_isSharedCheck_3268_;
goto v_resetjp_3223_;
}
else
{
lean_inc(v_a_3222_);
lean_dec(v___x_3221_);
v___x_3224_ = lean_box(0);
v_isShared_3225_ = v_isSharedCheck_3268_;
goto v_resetjp_3223_;
}
v_resetjp_3223_:
{
lean_object* v___x_3226_; lean_object* v_traceState_3227_; lean_object* v_env_3228_; lean_object* v_nextMacroScope_3229_; lean_object* v_ngen_3230_; lean_object* v_auxDeclNGen_3231_; lean_object* v_cache_3232_; lean_object* v_messages_3233_; lean_object* v_infoState_3234_; lean_object* v_snapshotTasks_3235_; lean_object* v_newDecls_3236_; lean_object* v___x_3238_; uint8_t v_isShared_3239_; uint8_t v_isSharedCheck_3267_; 
v___x_3226_ = lean_st_ref_take(v___y_3218_);
v_traceState_3227_ = lean_ctor_get(v___x_3226_, 4);
v_env_3228_ = lean_ctor_get(v___x_3226_, 0);
v_nextMacroScope_3229_ = lean_ctor_get(v___x_3226_, 1);
v_ngen_3230_ = lean_ctor_get(v___x_3226_, 2);
v_auxDeclNGen_3231_ = lean_ctor_get(v___x_3226_, 3);
v_cache_3232_ = lean_ctor_get(v___x_3226_, 5);
v_messages_3233_ = lean_ctor_get(v___x_3226_, 6);
v_infoState_3234_ = lean_ctor_get(v___x_3226_, 7);
v_snapshotTasks_3235_ = lean_ctor_get(v___x_3226_, 8);
v_newDecls_3236_ = lean_ctor_get(v___x_3226_, 9);
v_isSharedCheck_3267_ = !lean_is_exclusive(v___x_3226_);
if (v_isSharedCheck_3267_ == 0)
{
v___x_3238_ = v___x_3226_;
v_isShared_3239_ = v_isSharedCheck_3267_;
goto v_resetjp_3237_;
}
else
{
lean_inc(v_newDecls_3236_);
lean_inc(v_snapshotTasks_3235_);
lean_inc(v_infoState_3234_);
lean_inc(v_messages_3233_);
lean_inc(v_cache_3232_);
lean_inc(v_traceState_3227_);
lean_inc(v_auxDeclNGen_3231_);
lean_inc(v_ngen_3230_);
lean_inc(v_nextMacroScope_3229_);
lean_inc(v_env_3228_);
lean_dec(v___x_3226_);
v___x_3238_ = lean_box(0);
v_isShared_3239_ = v_isSharedCheck_3267_;
goto v_resetjp_3237_;
}
v_resetjp_3237_:
{
uint64_t v_tid_3240_; lean_object* v_traces_3241_; lean_object* v___x_3243_; uint8_t v_isShared_3244_; uint8_t v_isSharedCheck_3266_; 
v_tid_3240_ = lean_ctor_get_uint64(v_traceState_3227_, sizeof(void*)*1);
v_traces_3241_ = lean_ctor_get(v_traceState_3227_, 0);
v_isSharedCheck_3266_ = !lean_is_exclusive(v_traceState_3227_);
if (v_isSharedCheck_3266_ == 0)
{
v___x_3243_ = v_traceState_3227_;
v_isShared_3244_ = v_isSharedCheck_3266_;
goto v_resetjp_3242_;
}
else
{
lean_inc(v_traces_3241_);
lean_dec(v_traceState_3227_);
v___x_3243_ = lean_box(0);
v_isShared_3244_ = v_isSharedCheck_3266_;
goto v_resetjp_3242_;
}
v_resetjp_3242_:
{
lean_object* v___x_3245_; double v___x_3246_; uint8_t v___x_3247_; lean_object* v___x_3248_; lean_object* v___x_3249_; lean_object* v___x_3250_; lean_object* v___x_3251_; lean_object* v___x_3252_; lean_object* v___x_3253_; lean_object* v___x_3255_; 
v___x_3245_ = lean_box(0);
v___x_3246_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6___closed__0);
v___x_3247_ = 0;
v___x_3248_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6___closed__1));
v___x_3249_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3249_, 0, v_cls_3214_);
lean_ctor_set(v___x_3249_, 1, v___x_3245_);
lean_ctor_set(v___x_3249_, 2, v___x_3248_);
lean_ctor_set_float(v___x_3249_, sizeof(void*)*3, v___x_3246_);
lean_ctor_set_float(v___x_3249_, sizeof(void*)*3 + 8, v___x_3246_);
lean_ctor_set_uint8(v___x_3249_, sizeof(void*)*3 + 16, v___x_3247_);
v___x_3250_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6___closed__2));
v___x_3251_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3251_, 0, v___x_3249_);
lean_ctor_set(v___x_3251_, 1, v_a_3222_);
lean_ctor_set(v___x_3251_, 2, v___x_3250_);
lean_inc(v_ref_3220_);
v___x_3252_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3252_, 0, v_ref_3220_);
lean_ctor_set(v___x_3252_, 1, v___x_3251_);
v___x_3253_ = l_Lean_PersistentArray_push___redArg(v_traces_3241_, v___x_3252_);
if (v_isShared_3244_ == 0)
{
lean_ctor_set(v___x_3243_, 0, v___x_3253_);
v___x_3255_ = v___x_3243_;
goto v_reusejp_3254_;
}
else
{
lean_object* v_reuseFailAlloc_3265_; 
v_reuseFailAlloc_3265_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3265_, 0, v___x_3253_);
lean_ctor_set_uint64(v_reuseFailAlloc_3265_, sizeof(void*)*1, v_tid_3240_);
v___x_3255_ = v_reuseFailAlloc_3265_;
goto v_reusejp_3254_;
}
v_reusejp_3254_:
{
lean_object* v___x_3257_; 
if (v_isShared_3239_ == 0)
{
lean_ctor_set(v___x_3238_, 4, v___x_3255_);
v___x_3257_ = v___x_3238_;
goto v_reusejp_3256_;
}
else
{
lean_object* v_reuseFailAlloc_3264_; 
v_reuseFailAlloc_3264_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3264_, 0, v_env_3228_);
lean_ctor_set(v_reuseFailAlloc_3264_, 1, v_nextMacroScope_3229_);
lean_ctor_set(v_reuseFailAlloc_3264_, 2, v_ngen_3230_);
lean_ctor_set(v_reuseFailAlloc_3264_, 3, v_auxDeclNGen_3231_);
lean_ctor_set(v_reuseFailAlloc_3264_, 4, v___x_3255_);
lean_ctor_set(v_reuseFailAlloc_3264_, 5, v_cache_3232_);
lean_ctor_set(v_reuseFailAlloc_3264_, 6, v_messages_3233_);
lean_ctor_set(v_reuseFailAlloc_3264_, 7, v_infoState_3234_);
lean_ctor_set(v_reuseFailAlloc_3264_, 8, v_snapshotTasks_3235_);
lean_ctor_set(v_reuseFailAlloc_3264_, 9, v_newDecls_3236_);
v___x_3257_ = v_reuseFailAlloc_3264_;
goto v_reusejp_3256_;
}
v_reusejp_3256_:
{
lean_object* v___x_3258_; lean_object* v___x_3259_; lean_object* v___x_3260_; lean_object* v___x_3262_; 
v___x_3258_ = lean_st_ref_set(v___y_3218_, v___x_3257_);
v___x_3259_ = lean_box(0);
v___x_3260_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3260_, 0, v___x_3259_);
lean_ctor_set(v___x_3260_, 1, v___y_3216_);
if (v_isShared_3225_ == 0)
{
lean_ctor_set(v___x_3224_, 0, v___x_3260_);
v___x_3262_ = v___x_3224_;
goto v_reusejp_3261_;
}
else
{
lean_object* v_reuseFailAlloc_3263_; 
v_reuseFailAlloc_3263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3263_, 0, v___x_3260_);
v___x_3262_ = v_reuseFailAlloc_3263_;
goto v_reusejp_3261_;
}
v_reusejp_3261_:
{
return v___x_3262_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6___boxed(lean_object* v_cls_3269_, lean_object* v_msg_3270_, lean_object* v___y_3271_, lean_object* v___y_3272_, lean_object* v___y_3273_, lean_object* v___y_3274_){
_start:
{
lean_object* v_res_3275_; 
v_res_3275_ = l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6(v_cls_3269_, v_msg_3270_, v___y_3271_, v___y_3272_, v___y_3273_);
lean_dec(v___y_3273_);
lean_dec_ref(v___y_3272_);
return v_res_3275_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0_spec__0___redArg(lean_object* v_a_3276_, lean_object* v_x_3277_){
_start:
{
if (lean_obj_tag(v_x_3277_) == 0)
{
lean_object* v___x_3278_; 
v___x_3278_ = lean_box(0);
return v___x_3278_;
}
else
{
lean_object* v_key_3279_; lean_object* v_value_3280_; lean_object* v_tail_3281_; uint8_t v___x_3282_; 
v_key_3279_ = lean_ctor_get(v_x_3277_, 0);
v_value_3280_ = lean_ctor_get(v_x_3277_, 1);
v_tail_3281_ = lean_ctor_get(v_x_3277_, 2);
v___x_3282_ = l_Lean_instBEqFVarId_beq(v_key_3279_, v_a_3276_);
if (v___x_3282_ == 0)
{
v_x_3277_ = v_tail_3281_;
goto _start;
}
else
{
lean_object* v___x_3284_; 
lean_inc(v_value_3280_);
v___x_3284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3284_, 0, v_value_3280_);
return v___x_3284_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0_spec__0___redArg___boxed(lean_object* v_a_3285_, lean_object* v_x_3286_){
_start:
{
lean_object* v_res_3287_; 
v_res_3287_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0_spec__0___redArg(v_a_3285_, v_x_3286_);
lean_dec(v_x_3286_);
lean_dec(v_a_3285_);
return v_res_3287_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0___redArg(lean_object* v_m_3288_, lean_object* v_a_3289_){
_start:
{
lean_object* v_buckets_3290_; lean_object* v___x_3291_; uint64_t v___x_3292_; uint64_t v___x_3293_; uint64_t v___x_3294_; uint64_t v_fold_3295_; uint64_t v___x_3296_; uint64_t v___x_3297_; uint64_t v___x_3298_; size_t v___x_3299_; size_t v___x_3300_; size_t v___x_3301_; size_t v___x_3302_; size_t v___x_3303_; lean_object* v___x_3304_; lean_object* v___x_3305_; 
v_buckets_3290_ = lean_ctor_get(v_m_3288_, 1);
v___x_3291_ = lean_array_get_size(v_buckets_3290_);
v___x_3292_ = l_Lean_instHashableFVarId_hash(v_a_3289_);
v___x_3293_ = 32ULL;
v___x_3294_ = lean_uint64_shift_right(v___x_3292_, v___x_3293_);
v_fold_3295_ = lean_uint64_xor(v___x_3292_, v___x_3294_);
v___x_3296_ = 16ULL;
v___x_3297_ = lean_uint64_shift_right(v_fold_3295_, v___x_3296_);
v___x_3298_ = lean_uint64_xor(v_fold_3295_, v___x_3297_);
v___x_3299_ = lean_uint64_to_usize(v___x_3298_);
v___x_3300_ = lean_usize_of_nat(v___x_3291_);
v___x_3301_ = ((size_t)1ULL);
v___x_3302_ = lean_usize_sub(v___x_3300_, v___x_3301_);
v___x_3303_ = lean_usize_land(v___x_3299_, v___x_3302_);
v___x_3304_ = lean_array_uget_borrowed(v_buckets_3290_, v___x_3303_);
v___x_3305_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0_spec__0___redArg(v_a_3289_, v___x_3304_);
return v___x_3305_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0___redArg___boxed(lean_object* v_m_3306_, lean_object* v_a_3307_){
_start:
{
lean_object* v_res_3308_; 
v_res_3308_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0___redArg(v_m_3306_, v_a_3307_);
lean_dec(v_a_3307_);
lean_dec_ref(v_m_3306_);
return v_res_3308_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___lam__0___boxed(lean_object* v___x_3309_, lean_object* v_m_3310_, lean_object* v_e_3311_, lean_object* v___y_3312_, lean_object* v___y_3313_, lean_object* v___y_3314_, lean_object* v___y_3315_){
_start:
{
uint8_t v___x_19766__boxed_3316_; lean_object* v_res_3317_; 
v___x_19766__boxed_3316_ = lean_unbox(v___x_3309_);
v_res_3317_ = l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___lam__0(v___x_19766__boxed_3316_, v_m_3310_, v_e_3311_, v___y_3312_, v___y_3313_, v___y_3314_);
lean_dec(v___y_3314_);
lean_dec_ref(v___y_3313_);
lean_dec_ref(v_e_3311_);
return v_res_3317_;
}
}
static lean_object* _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__0(void){
_start:
{
lean_object* v___x_3318_; lean_object* v___x_3319_; lean_object* v___x_3320_; 
v___x_3318_ = lean_box(0);
v___x_3319_ = lean_unsigned_to_nat(16u);
v___x_3320_ = lean_mk_array(v___x_3319_, v___x_3318_);
return v___x_3320_;
}
}
static lean_object* _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__1(void){
_start:
{
lean_object* v___x_3321_; lean_object* v___x_3322_; lean_object* v___x_3323_; 
v___x_3321_ = lean_obj_once(&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__0, &l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__0_once, _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__0);
v___x_3322_ = lean_unsigned_to_nat(0u);
v___x_3323_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3323_, 0, v___x_3322_);
lean_ctor_set(v___x_3323_, 1, v___x_3321_);
return v___x_3323_;
}
}
static lean_object* _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__5(void){
_start:
{
lean_object* v___x_3327_; lean_object* v___x_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; lean_object* v___x_3331_; lean_object* v___x_3332_; 
v___x_3327_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__4));
v___x_3328_ = lean_unsigned_to_nat(4u);
v___x_3329_ = lean_unsigned_to_nat(384u);
v___x_3330_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__3));
v___x_3331_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__2));
v___x_3332_ = l_mkPanicMessageWithDecl(v___x_3331_, v___x_3330_, v___x_3329_, v___x_3328_, v___x_3327_);
return v___x_3332_;
}
}
static lean_object* _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__7(void){
_start:
{
lean_object* v___x_3334_; lean_object* v___x_3335_; 
v___x_3334_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__6));
v___x_3335_ = l_Lean_stringToMessageData(v___x_3334_);
return v___x_3335_;
}
}
static lean_object* _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__13(void){
_start:
{
lean_object* v___x_3344_; lean_object* v___x_3345_; lean_object* v___x_3346_; 
v___x_3344_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__10));
v___x_3345_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__12));
v___x_3346_ = l_Lean_Name_append(v___x_3345_, v___x_3344_);
return v___x_3346_;
}
}
static lean_object* _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__15(void){
_start:
{
lean_object* v___x_3348_; lean_object* v___x_3349_; 
v___x_3348_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__14));
v___x_3349_ = l_Lean_stringToMessageData(v___x_3348_);
return v___x_3349_;
}
}
static lean_object* _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__17(void){
_start:
{
lean_object* v___x_3351_; lean_object* v___x_3352_; 
v___x_3351_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__16));
v___x_3352_ = l_Lean_stringToMessageData(v___x_3351_);
return v___x_3352_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit(lean_object* v_m_3353_, lean_object* v_fvarId_3354_, lean_object* v_a_3355_, lean_object* v_a_3356_, lean_object* v_a_3357_){
_start:
{
lean_object* v___x_3359_; 
v___x_3359_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0___redArg(v_m_3353_, v_fvarId_3354_);
if (lean_obj_tag(v___x_3359_) == 1)
{
lean_object* v_val_3360_; lean_object* v___x_3362_; uint8_t v_isShared_3363_; uint8_t v_isSharedCheck_3473_; 
v_val_3360_ = lean_ctor_get(v___x_3359_, 0);
v_isSharedCheck_3473_ = !lean_is_exclusive(v___x_3359_);
if (v_isSharedCheck_3473_ == 0)
{
v___x_3362_ = v___x_3359_;
v_isShared_3363_ = v_isSharedCheck_3473_;
goto v_resetjp_3361_;
}
else
{
lean_inc(v_val_3360_);
lean_dec(v___x_3359_);
v___x_3362_ = lean_box(0);
v_isShared_3363_ = v_isSharedCheck_3473_;
goto v_resetjp_3361_;
}
v_resetjp_3361_:
{
lean_object* v_fst_3364_; lean_object* v_snd_3365_; lean_object* v___x_3367_; uint8_t v_isShared_3368_; uint8_t v_isSharedCheck_3472_; 
v_fst_3364_ = lean_ctor_get(v_val_3360_, 0);
v_snd_3365_ = lean_ctor_get(v_val_3360_, 1);
v_isSharedCheck_3472_ = !lean_is_exclusive(v_val_3360_);
if (v_isSharedCheck_3472_ == 0)
{
v___x_3367_ = v_val_3360_;
v_isShared_3368_ = v_isSharedCheck_3472_;
goto v_resetjp_3366_;
}
else
{
lean_inc(v_snd_3365_);
lean_inc(v_fst_3364_);
lean_dec(v_val_3360_);
v___x_3367_ = lean_box(0);
v_isShared_3368_ = v_isSharedCheck_3472_;
goto v_resetjp_3366_;
}
v_resetjp_3366_:
{
lean_object* v_tempMark_3369_; lean_object* v_doneMark_3370_; lean_object* v___x_3371_; uint8_t v___x_3372_; 
v_tempMark_3369_ = lean_ctor_get(v_a_3355_, 0);
v_doneMark_3370_ = lean_ctor_get(v_a_3355_, 1);
v___x_3371_ = l_Lean_LocalDecl_fvarId(v_fst_3364_);
v___x_3372_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1___redArg(v_doneMark_3370_, v___x_3371_);
if (v___x_3372_ == 0)
{
lean_object* v_options_3373_; lean_object* v_inheritedTraceOptions_3374_; uint8_t v_hasTrace_3375_; uint8_t v___x_3376_; lean_object* v___x_3377_; lean_object* v___f_3378_; lean_object* v___y_3380_; lean_object* v___y_3381_; lean_object* v___y_3382_; lean_object* v___y_3433_; lean_object* v___y_3434_; lean_object* v___y_3435_; lean_object* v___y_3440_; lean_object* v_tempMark_3441_; lean_object* v___y_3442_; lean_object* v___y_3443_; 
lean_del_object(v___x_3367_);
lean_del_object(v___x_3362_);
v_options_3373_ = lean_ctor_get(v_a_3356_, 2);
v_inheritedTraceOptions_3374_ = lean_ctor_get(v_a_3356_, 13);
v_hasTrace_3375_ = lean_ctor_get_uint8(v_options_3373_, sizeof(void*)*1);
v___x_3376_ = 1;
v___x_3377_ = lean_box(v___x_3376_);
v___f_3378_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___lam__0___boxed), 7, 2);
lean_closure_set(v___f_3378_, 0, v___x_3377_);
lean_closure_set(v___f_3378_, 1, v_m_3353_);
if (v_hasTrace_3375_ == 0)
{
lean_inc_ref(v_tempMark_3369_);
v___y_3440_ = v_a_3355_;
v_tempMark_3441_ = v_tempMark_3369_;
v___y_3442_ = v_a_3356_;
v___y_3443_ = v_a_3357_;
goto v___jp_3439_;
}
else
{
lean_object* v___x_3449_; lean_object* v___x_3450_; uint8_t v___x_3451_; 
v___x_3449_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__10));
v___x_3450_ = lean_obj_once(&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__13, &l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__13_once, _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__13);
v___x_3451_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3374_, v_options_3373_, v___x_3450_);
if (v___x_3451_ == 0)
{
lean_inc_ref(v_tempMark_3369_);
v___y_3440_ = v_a_3355_;
v_tempMark_3441_ = v_tempMark_3369_;
v___y_3442_ = v_a_3356_;
v___y_3443_ = v_a_3357_;
goto v___jp_3439_;
}
else
{
lean_object* v___x_3452_; lean_object* v___x_3453_; lean_object* v___x_3454_; lean_object* v___x_3455_; lean_object* v___x_3456_; lean_object* v___x_3457_; lean_object* v___x_3458_; lean_object* v___x_3459_; lean_object* v___x_3460_; lean_object* v___x_3461_; 
v___x_3452_ = lean_obj_once(&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__15, &l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__15_once, _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__15);
lean_inc(v___x_3371_);
v___x_3453_ = l_Lean_mkFVar(v___x_3371_);
v___x_3454_ = l_Lean_MessageData_ofExpr(v___x_3453_);
v___x_3455_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3455_, 0, v___x_3452_);
lean_ctor_set(v___x_3455_, 1, v___x_3454_);
v___x_3456_ = lean_obj_once(&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__17, &l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__17_once, _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__17);
v___x_3457_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3457_, 0, v___x_3455_);
lean_ctor_set(v___x_3457_, 1, v___x_3456_);
v___x_3458_ = l_Lean_LocalDecl_type(v_fst_3364_);
v___x_3459_ = l_Lean_MessageData_ofExpr(v___x_3458_);
v___x_3460_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3460_, 0, v___x_3457_);
lean_ctor_set(v___x_3460_, 1, v___x_3459_);
v___x_3461_ = l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6(v___x_3449_, v___x_3460_, v_a_3355_, v_a_3356_, v_a_3357_);
if (lean_obj_tag(v___x_3461_) == 0)
{
lean_object* v_a_3462_; lean_object* v_snd_3463_; lean_object* v_tempMark_3464_; 
v_a_3462_ = lean_ctor_get(v___x_3461_, 0);
lean_inc(v_a_3462_);
lean_dec_ref(v___x_3461_);
v_snd_3463_ = lean_ctor_get(v_a_3462_, 1);
lean_inc(v_snd_3463_);
lean_dec(v_a_3462_);
v_tempMark_3464_ = lean_ctor_get(v_snd_3463_, 0);
lean_inc_ref(v_tempMark_3464_);
v___y_3440_ = v_snd_3463_;
v_tempMark_3441_ = v_tempMark_3464_;
v___y_3442_ = v_a_3356_;
v___y_3443_ = v_a_3357_;
goto v___jp_3439_;
}
else
{
lean_dec_ref(v___f_3378_);
lean_dec(v___x_3371_);
lean_dec(v_snd_3365_);
lean_dec(v_fst_3364_);
return v___x_3461_;
}
}
}
v___jp_3379_:
{
lean_object* v_tempMark_3383_; lean_object* v_doneMark_3384_; lean_object* v_newDecls_3385_; lean_object* v_newArgs_3386_; lean_object* v___x_3388_; uint8_t v_isShared_3389_; uint8_t v_isSharedCheck_3431_; 
v_tempMark_3383_ = lean_ctor_get(v___y_3380_, 0);
v_doneMark_3384_ = lean_ctor_get(v___y_3380_, 1);
v_newDecls_3385_ = lean_ctor_get(v___y_3380_, 2);
v_newArgs_3386_ = lean_ctor_get(v___y_3380_, 3);
v_isSharedCheck_3431_ = !lean_is_exclusive(v___y_3380_);
if (v_isSharedCheck_3431_ == 0)
{
v___x_3388_ = v___y_3380_;
v_isShared_3389_ = v_isSharedCheck_3431_;
goto v_resetjp_3387_;
}
else
{
lean_inc(v_newArgs_3386_);
lean_inc(v_newDecls_3385_);
lean_inc(v_doneMark_3384_);
lean_inc(v_tempMark_3383_);
lean_dec(v___y_3380_);
v___x_3388_ = lean_box(0);
v_isShared_3389_ = v_isSharedCheck_3431_;
goto v_resetjp_3387_;
}
v_resetjp_3387_:
{
lean_object* v___x_3390_; lean_object* v___x_3391_; lean_object* v___x_3392_; lean_object* v___x_3393_; lean_object* v___x_3395_; 
v___x_3390_ = lean_obj_once(&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__1, &l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__1_once, _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__1);
v___x_3391_ = lean_st_mk_ref(v___x_3390_);
v___x_3392_ = lean_box(0);
lean_inc(v___x_3371_);
v___x_3393_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2___redArg(v_tempMark_3383_, v___x_3371_, v___x_3392_);
if (v_isShared_3389_ == 0)
{
lean_ctor_set(v___x_3388_, 0, v___x_3393_);
v___x_3395_ = v___x_3388_;
goto v_reusejp_3394_;
}
else
{
lean_object* v_reuseFailAlloc_3430_; 
v_reuseFailAlloc_3430_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3430_, 0, v___x_3393_);
lean_ctor_set(v_reuseFailAlloc_3430_, 1, v_doneMark_3384_);
lean_ctor_set(v_reuseFailAlloc_3430_, 2, v_newDecls_3385_);
lean_ctor_set(v_reuseFailAlloc_3430_, 3, v_newArgs_3386_);
v___x_3395_ = v_reuseFailAlloc_3430_;
goto v_reusejp_3394_;
}
v_reusejp_3394_:
{
lean_object* v___x_3396_; lean_object* v___x_3397_; 
v___x_3396_ = l_Lean_LocalDecl_type(v_fst_3364_);
v___x_3397_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3(v___f_3378_, v___x_3396_, v___x_3391_, v___x_3395_, v___y_3381_, v___y_3382_);
if (lean_obj_tag(v___x_3397_) == 0)
{
lean_object* v_a_3398_; lean_object* v___x_3400_; uint8_t v_isShared_3401_; uint8_t v_isSharedCheck_3429_; 
v_a_3398_ = lean_ctor_get(v___x_3397_, 0);
v_isSharedCheck_3429_ = !lean_is_exclusive(v___x_3397_);
if (v_isSharedCheck_3429_ == 0)
{
v___x_3400_ = v___x_3397_;
v_isShared_3401_ = v_isSharedCheck_3429_;
goto v_resetjp_3399_;
}
else
{
lean_inc(v_a_3398_);
lean_dec(v___x_3397_);
v___x_3400_ = lean_box(0);
v_isShared_3401_ = v_isSharedCheck_3429_;
goto v_resetjp_3399_;
}
v_resetjp_3399_:
{
lean_object* v_snd_3402_; lean_object* v___x_3404_; uint8_t v_isShared_3405_; uint8_t v_isSharedCheck_3427_; 
v_snd_3402_ = lean_ctor_get(v_a_3398_, 1);
v_isSharedCheck_3427_ = !lean_is_exclusive(v_a_3398_);
if (v_isSharedCheck_3427_ == 0)
{
lean_object* v_unused_3428_; 
v_unused_3428_ = lean_ctor_get(v_a_3398_, 0);
lean_dec(v_unused_3428_);
v___x_3404_ = v_a_3398_;
v_isShared_3405_ = v_isSharedCheck_3427_;
goto v_resetjp_3403_;
}
else
{
lean_inc(v_snd_3402_);
lean_dec(v_a_3398_);
v___x_3404_ = lean_box(0);
v_isShared_3405_ = v_isSharedCheck_3427_;
goto v_resetjp_3403_;
}
v_resetjp_3403_:
{
lean_object* v___x_3406_; lean_object* v_tempMark_3407_; lean_object* v_doneMark_3408_; lean_object* v_newDecls_3409_; lean_object* v_newArgs_3410_; lean_object* v___x_3412_; uint8_t v_isShared_3413_; uint8_t v_isSharedCheck_3426_; 
v___x_3406_ = lean_st_ref_get(v___x_3391_);
lean_dec(v___x_3391_);
lean_dec(v___x_3406_);
v_tempMark_3407_ = lean_ctor_get(v_snd_3402_, 0);
v_doneMark_3408_ = lean_ctor_get(v_snd_3402_, 1);
v_newDecls_3409_ = lean_ctor_get(v_snd_3402_, 2);
v_newArgs_3410_ = lean_ctor_get(v_snd_3402_, 3);
v_isSharedCheck_3426_ = !lean_is_exclusive(v_snd_3402_);
if (v_isSharedCheck_3426_ == 0)
{
v___x_3412_ = v_snd_3402_;
v_isShared_3413_ = v_isSharedCheck_3426_;
goto v_resetjp_3411_;
}
else
{
lean_inc(v_newArgs_3410_);
lean_inc(v_newDecls_3409_);
lean_inc(v_doneMark_3408_);
lean_inc(v_tempMark_3407_);
lean_dec(v_snd_3402_);
v___x_3412_ = lean_box(0);
v_isShared_3413_ = v_isSharedCheck_3426_;
goto v_resetjp_3411_;
}
v_resetjp_3411_:
{
lean_object* v___x_3414_; lean_object* v___x_3415_; lean_object* v___x_3416_; lean_object* v___x_3418_; 
v___x_3414_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2___redArg(v_doneMark_3408_, v___x_3371_, v___x_3392_);
v___x_3415_ = lean_array_push(v_newDecls_3409_, v_fst_3364_);
v___x_3416_ = lean_array_push(v_newArgs_3410_, v_snd_3365_);
if (v_isShared_3413_ == 0)
{
lean_ctor_set(v___x_3412_, 3, v___x_3416_);
lean_ctor_set(v___x_3412_, 2, v___x_3415_);
lean_ctor_set(v___x_3412_, 1, v___x_3414_);
v___x_3418_ = v___x_3412_;
goto v_reusejp_3417_;
}
else
{
lean_object* v_reuseFailAlloc_3425_; 
v_reuseFailAlloc_3425_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3425_, 0, v_tempMark_3407_);
lean_ctor_set(v_reuseFailAlloc_3425_, 1, v___x_3414_);
lean_ctor_set(v_reuseFailAlloc_3425_, 2, v___x_3415_);
lean_ctor_set(v_reuseFailAlloc_3425_, 3, v___x_3416_);
v___x_3418_ = v_reuseFailAlloc_3425_;
goto v_reusejp_3417_;
}
v_reusejp_3417_:
{
lean_object* v___x_3420_; 
if (v_isShared_3405_ == 0)
{
lean_ctor_set(v___x_3404_, 1, v___x_3418_);
lean_ctor_set(v___x_3404_, 0, v___x_3392_);
v___x_3420_ = v___x_3404_;
goto v_reusejp_3419_;
}
else
{
lean_object* v_reuseFailAlloc_3424_; 
v_reuseFailAlloc_3424_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3424_, 0, v___x_3392_);
lean_ctor_set(v_reuseFailAlloc_3424_, 1, v___x_3418_);
v___x_3420_ = v_reuseFailAlloc_3424_;
goto v_reusejp_3419_;
}
v_reusejp_3419_:
{
lean_object* v___x_3422_; 
if (v_isShared_3401_ == 0)
{
lean_ctor_set(v___x_3400_, 0, v___x_3420_);
v___x_3422_ = v___x_3400_;
goto v_reusejp_3421_;
}
else
{
lean_object* v_reuseFailAlloc_3423_; 
v_reuseFailAlloc_3423_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3423_, 0, v___x_3420_);
v___x_3422_ = v_reuseFailAlloc_3423_;
goto v_reusejp_3421_;
}
v_reusejp_3421_:
{
return v___x_3422_;
}
}
}
}
}
}
}
else
{
lean_dec(v___x_3391_);
lean_dec(v___x_3371_);
lean_dec(v_snd_3365_);
lean_dec(v_fst_3364_);
return v___x_3397_;
}
}
}
}
v___jp_3432_:
{
uint8_t v___x_3436_; 
v___x_3436_ = l_Lean_LocalDecl_isLet(v_fst_3364_, v___x_3376_);
if (v___x_3436_ == 0)
{
v___y_3380_ = v___y_3433_;
v___y_3381_ = v___y_3434_;
v___y_3382_ = v___y_3435_;
goto v___jp_3379_;
}
else
{
if (v___x_3372_ == 0)
{
lean_object* v___x_3437_; lean_object* v___x_3438_; 
lean_dec_ref(v___f_3378_);
lean_dec(v___x_3371_);
lean_dec(v_snd_3365_);
lean_dec(v_fst_3364_);
v___x_3437_ = lean_obj_once(&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__5, &l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__5_once, _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__5);
v___x_3438_ = l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4(v___x_3437_, v___y_3433_, v___y_3434_, v___y_3435_);
return v___x_3438_;
}
else
{
v___y_3380_ = v___y_3433_;
v___y_3381_ = v___y_3434_;
v___y_3382_ = v___y_3435_;
goto v___jp_3379_;
}
}
}
v___jp_3439_:
{
uint8_t v___x_3444_; 
v___x_3444_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1___redArg(v_tempMark_3441_, v___x_3371_);
lean_dec_ref(v_tempMark_3441_);
if (v___x_3444_ == 0)
{
v___y_3433_ = v___y_3440_;
v___y_3434_ = v___y_3442_;
v___y_3435_ = v___y_3443_;
goto v___jp_3432_;
}
else
{
lean_object* v___x_3445_; lean_object* v___x_3446_; 
lean_dec_ref(v___y_3440_);
v___x_3445_ = lean_obj_once(&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__7, &l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__7_once, _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__7);
v___x_3446_ = l_Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5___redArg(v___x_3445_, v___y_3442_, v___y_3443_);
if (lean_obj_tag(v___x_3446_) == 0)
{
lean_object* v_a_3447_; lean_object* v_snd_3448_; 
v_a_3447_ = lean_ctor_get(v___x_3446_, 0);
lean_inc(v_a_3447_);
lean_dec_ref(v___x_3446_);
v_snd_3448_ = lean_ctor_get(v_a_3447_, 1);
lean_inc(v_snd_3448_);
lean_dec(v_a_3447_);
v___y_3433_ = v_snd_3448_;
v___y_3434_ = v___y_3442_;
v___y_3435_ = v___y_3443_;
goto v___jp_3432_;
}
else
{
lean_dec_ref(v___f_3378_);
lean_dec(v___x_3371_);
lean_dec(v_snd_3365_);
lean_dec(v_fst_3364_);
return v___x_3446_;
}
}
}
}
else
{
lean_object* v___x_3465_; lean_object* v___x_3467_; 
lean_dec(v___x_3371_);
lean_dec(v_snd_3365_);
lean_dec(v_fst_3364_);
lean_dec_ref(v_m_3353_);
v___x_3465_ = lean_box(0);
if (v_isShared_3368_ == 0)
{
lean_ctor_set(v___x_3367_, 1, v_a_3355_);
lean_ctor_set(v___x_3367_, 0, v___x_3465_);
v___x_3467_ = v___x_3367_;
goto v_reusejp_3466_;
}
else
{
lean_object* v_reuseFailAlloc_3471_; 
v_reuseFailAlloc_3471_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3471_, 0, v___x_3465_);
lean_ctor_set(v_reuseFailAlloc_3471_, 1, v_a_3355_);
v___x_3467_ = v_reuseFailAlloc_3471_;
goto v_reusejp_3466_;
}
v_reusejp_3466_:
{
lean_object* v___x_3469_; 
if (v_isShared_3363_ == 0)
{
lean_ctor_set_tag(v___x_3362_, 0);
lean_ctor_set(v___x_3362_, 0, v___x_3467_);
v___x_3469_ = v___x_3362_;
goto v_reusejp_3468_;
}
else
{
lean_object* v_reuseFailAlloc_3470_; 
v_reuseFailAlloc_3470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3470_, 0, v___x_3467_);
v___x_3469_ = v_reuseFailAlloc_3470_;
goto v_reusejp_3468_;
}
v_reusejp_3468_:
{
return v___x_3469_;
}
}
}
}
}
}
else
{
lean_object* v___x_3474_; lean_object* v___x_3475_; lean_object* v___x_3476_; 
lean_dec(v___x_3359_);
lean_dec_ref(v_m_3353_);
v___x_3474_ = lean_box(0);
v___x_3475_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3475_, 0, v___x_3474_);
lean_ctor_set(v___x_3475_, 1, v_a_3355_);
v___x_3476_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3476_, 0, v___x_3475_);
return v___x_3476_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___lam__0(uint8_t v___x_3477_, lean_object* v_m_3478_, lean_object* v_e_3479_, lean_object* v___y_3480_, lean_object* v___y_3481_, lean_object* v___y_3482_){
_start:
{
lean_object* v___y_3485_; uint8_t v___x_3489_; 
v___x_3489_ = l_Lean_Expr_hasFVar(v_e_3479_);
if (v___x_3489_ == 0)
{
lean_object* v___x_3490_; lean_object* v___x_3491_; lean_object* v___x_3492_; 
lean_dec_ref(v_m_3478_);
v___x_3490_ = lean_box(v___x_3489_);
v___x_3491_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3491_, 0, v___x_3490_);
lean_ctor_set(v___x_3491_, 1, v___y_3480_);
v___x_3492_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3492_, 0, v___x_3491_);
return v___x_3492_;
}
else
{
uint8_t v___x_3493_; 
v___x_3493_ = l_Lean_Expr_isFVar(v_e_3479_);
if (v___x_3493_ == 0)
{
lean_dec_ref(v_m_3478_);
v___y_3485_ = v___y_3480_;
goto v___jp_3484_;
}
else
{
lean_object* v___x_3494_; lean_object* v___x_3495_; 
v___x_3494_ = l_Lean_Expr_fvarId_x21(v_e_3479_);
v___x_3495_ = l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit(v_m_3478_, v___x_3494_, v___y_3480_, v___y_3481_, v___y_3482_);
lean_dec(v___x_3494_);
if (lean_obj_tag(v___x_3495_) == 0)
{
lean_object* v_a_3496_; lean_object* v_snd_3497_; 
v_a_3496_ = lean_ctor_get(v___x_3495_, 0);
lean_inc(v_a_3496_);
lean_dec_ref(v___x_3495_);
v_snd_3497_ = lean_ctor_get(v_a_3496_, 1);
lean_inc(v_snd_3497_);
lean_dec(v_a_3496_);
v___y_3485_ = v_snd_3497_;
goto v___jp_3484_;
}
else
{
lean_object* v_a_3498_; lean_object* v___x_3500_; uint8_t v_isShared_3501_; uint8_t v_isSharedCheck_3505_; 
v_a_3498_ = lean_ctor_get(v___x_3495_, 0);
v_isSharedCheck_3505_ = !lean_is_exclusive(v___x_3495_);
if (v_isSharedCheck_3505_ == 0)
{
v___x_3500_ = v___x_3495_;
v_isShared_3501_ = v_isSharedCheck_3505_;
goto v_resetjp_3499_;
}
else
{
lean_inc(v_a_3498_);
lean_dec(v___x_3495_);
v___x_3500_ = lean_box(0);
v_isShared_3501_ = v_isSharedCheck_3505_;
goto v_resetjp_3499_;
}
v_resetjp_3499_:
{
lean_object* v___x_3503_; 
if (v_isShared_3501_ == 0)
{
v___x_3503_ = v___x_3500_;
goto v_reusejp_3502_;
}
else
{
lean_object* v_reuseFailAlloc_3504_; 
v_reuseFailAlloc_3504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3504_, 0, v_a_3498_);
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
v___jp_3484_:
{
lean_object* v___x_3486_; lean_object* v___x_3487_; lean_object* v___x_3488_; 
v___x_3486_ = lean_box(v___x_3477_);
v___x_3487_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3487_, 0, v___x_3486_);
lean_ctor_set(v___x_3487_, 1, v___y_3485_);
v___x_3488_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3488_, 0, v___x_3487_);
return v___x_3488_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___boxed(lean_object* v_m_3506_, lean_object* v_fvarId_3507_, lean_object* v_a_3508_, lean_object* v_a_3509_, lean_object* v_a_3510_, lean_object* v_a_3511_){
_start:
{
lean_object* v_res_3512_; 
v_res_3512_ = l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit(v_m_3506_, v_fvarId_3507_, v_a_3508_, v_a_3509_, v_a_3510_);
lean_dec(v_a_3510_);
lean_dec_ref(v_a_3509_);
lean_dec(v_fvarId_3507_);
return v_res_3512_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0(lean_object* v_00_u03b2_3513_, lean_object* v_m_3514_, lean_object* v_a_3515_){
_start:
{
lean_object* v___x_3516_; 
v___x_3516_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0___redArg(v_m_3514_, v_a_3515_);
return v___x_3516_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0___boxed(lean_object* v_00_u03b2_3517_, lean_object* v_m_3518_, lean_object* v_a_3519_){
_start:
{
lean_object* v_res_3520_; 
v_res_3520_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0(v_00_u03b2_3517_, v_m_3518_, v_a_3519_);
lean_dec(v_a_3519_);
lean_dec_ref(v_m_3518_);
return v_res_3520_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1(lean_object* v_00_u03b2_3521_, lean_object* v_m_3522_, lean_object* v_a_3523_){
_start:
{
uint8_t v___x_3524_; 
v___x_3524_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1___redArg(v_m_3522_, v_a_3523_);
return v___x_3524_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1___boxed(lean_object* v_00_u03b2_3525_, lean_object* v_m_3526_, lean_object* v_a_3527_){
_start:
{
uint8_t v_res_3528_; lean_object* v_r_3529_; 
v_res_3528_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1(v_00_u03b2_3525_, v_m_3526_, v_a_3527_);
lean_dec(v_a_3527_);
lean_dec_ref(v_m_3526_);
v_r_3529_ = lean_box(v_res_3528_);
return v_r_3529_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2(lean_object* v_00_u03b2_3530_, lean_object* v_m_3531_, lean_object* v_a_3532_, lean_object* v_b_3533_){
_start:
{
lean_object* v___x_3534_; 
v___x_3534_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2___redArg(v_m_3531_, v_a_3532_, v_b_3533_);
return v___x_3534_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5(lean_object* v_00_u03b1_3535_, lean_object* v_msg_3536_, lean_object* v___y_3537_, lean_object* v___y_3538_, lean_object* v___y_3539_){
_start:
{
lean_object* v___x_3541_; 
v___x_3541_ = l_Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5___redArg(v_msg_3536_, v___y_3538_, v___y_3539_);
return v___x_3541_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5___boxed(lean_object* v_00_u03b1_3542_, lean_object* v_msg_3543_, lean_object* v___y_3544_, lean_object* v___y_3545_, lean_object* v___y_3546_, lean_object* v___y_3547_){
_start:
{
lean_object* v_res_3548_; 
v_res_3548_ = l_Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5(v_00_u03b1_3542_, v_msg_3543_, v___y_3544_, v___y_3545_, v___y_3546_);
lean_dec(v___y_3546_);
lean_dec_ref(v___y_3545_);
lean_dec_ref(v___y_3544_);
return v_res_3548_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0_spec__0(lean_object* v_00_u03b2_3549_, lean_object* v_a_3550_, lean_object* v_x_3551_){
_start:
{
lean_object* v___x_3552_; 
v___x_3552_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0_spec__0___redArg(v_a_3550_, v_x_3551_);
return v___x_3552_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3553_, lean_object* v_a_3554_, lean_object* v_x_3555_){
_start:
{
lean_object* v_res_3556_; 
v_res_3556_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0_spec__0(v_00_u03b2_3553_, v_a_3554_, v_x_3555_);
lean_dec(v_x_3555_);
lean_dec(v_a_3554_);
return v_res_3556_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1_spec__2(lean_object* v_00_u03b2_3557_, lean_object* v_a_3558_, lean_object* v_x_3559_){
_start:
{
uint8_t v___x_3560_; 
v___x_3560_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1_spec__2___redArg(v_a_3558_, v_x_3559_);
return v___x_3560_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1_spec__2___boxed(lean_object* v_00_u03b2_3561_, lean_object* v_a_3562_, lean_object* v_x_3563_){
_start:
{
uint8_t v_res_3564_; lean_object* v_r_3565_; 
v_res_3564_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1_spec__2(v_00_u03b2_3561_, v_a_3562_, v_x_3563_);
lean_dec(v_x_3563_);
lean_dec(v_a_3562_);
v_r_3565_ = lean_box(v_res_3564_);
return v_r_3565_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__4(lean_object* v_00_u03b2_3566_, lean_object* v_data_3567_){
_start:
{
lean_object* v___x_3568_; 
v___x_3568_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__4___redArg(v_data_3567_);
return v___x_3568_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__6(lean_object* v_00_u03b2_3569_, lean_object* v_m_3570_, lean_object* v_a_3571_){
_start:
{
lean_object* v___x_3572_; 
v___x_3572_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__6___redArg(v_m_3570_, v_a_3571_);
return v___x_3572_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__6___boxed(lean_object* v_00_u03b2_3573_, lean_object* v_m_3574_, lean_object* v_a_3575_){
_start:
{
lean_object* v_res_3576_; 
v_res_3576_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__6(v_00_u03b2_3573_, v_m_3574_, v_a_3575_);
lean_dec_ref(v_a_3575_);
lean_dec_ref(v_m_3574_);
return v_res_3576_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7(lean_object* v_00_u03b2_3577_, lean_object* v_m_3578_, lean_object* v_a_3579_, lean_object* v_b_3580_){
_start:
{
lean_object* v___x_3581_; 
v___x_3581_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7___redArg(v_m_3578_, v_a_3579_, v_b_3580_);
return v___x_3581_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__4_spec__6(lean_object* v_00_u03b2_3582_, lean_object* v_i_3583_, lean_object* v_source_3584_, lean_object* v_target_3585_){
_start:
{
lean_object* v___x_3586_; 
v___x_3586_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__4_spec__6___redArg(v_i_3583_, v_source_3584_, v_target_3585_);
return v___x_3586_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__6_spec__9(lean_object* v_00_u03b2_3587_, lean_object* v_a_3588_, lean_object* v_x_3589_){
_start:
{
lean_object* v___x_3590_; 
v___x_3590_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__6_spec__9___redArg(v_a_3588_, v_x_3589_);
return v___x_3590_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__6_spec__9___boxed(lean_object* v_00_u03b2_3591_, lean_object* v_a_3592_, lean_object* v_x_3593_){
_start:
{
lean_object* v_res_3594_; 
v_res_3594_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__6_spec__9(v_00_u03b2_3591_, v_a_3592_, v_x_3593_);
lean_dec(v_x_3593_);
lean_dec_ref(v_a_3592_);
return v_res_3594_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__11(lean_object* v_00_u03b2_3595_, lean_object* v_a_3596_, lean_object* v_x_3597_){
_start:
{
uint8_t v___x_3598_; 
v___x_3598_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__11___redArg(v_a_3596_, v_x_3597_);
return v___x_3598_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__11___boxed(lean_object* v_00_u03b2_3599_, lean_object* v_a_3600_, lean_object* v_x_3601_){
_start:
{
uint8_t v_res_3602_; lean_object* v_r_3603_; 
v_res_3602_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__11(v_00_u03b2_3599_, v_a_3600_, v_x_3601_);
lean_dec(v_x_3601_);
lean_dec_ref(v_a_3600_);
v_r_3603_ = lean_box(v_res_3602_);
return v_r_3603_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__12(lean_object* v_00_u03b2_3604_, lean_object* v_data_3605_){
_start:
{
lean_object* v___x_3606_; 
v___x_3606_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__12___redArg(v_data_3605_);
return v___x_3606_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__13(lean_object* v_00_u03b2_3607_, lean_object* v_a_3608_, lean_object* v_b_3609_, lean_object* v_x_3610_){
_start:
{
lean_object* v___x_3611_; 
v___x_3611_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__13___redArg(v_a_3608_, v_b_3609_, v_x_3610_);
return v___x_3611_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__4_spec__6_spec__11(lean_object* v_00_u03b2_3612_, lean_object* v_x_3613_, lean_object* v_x_3614_){
_start:
{
lean_object* v___x_3615_; 
v___x_3615_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__4_spec__6_spec__11___redArg(v_x_3613_, v_x_3614_);
return v___x_3615_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__12_spec__17(lean_object* v_00_u03b2_3616_, lean_object* v_i_3617_, lean_object* v_source_3618_, lean_object* v_target_3619_){
_start:
{
lean_object* v___x_3620_; 
v___x_3620_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__12_spec__17___redArg(v_i_3617_, v_source_3618_, v_target_3619_);
return v___x_3620_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__12_spec__17_spec__18(lean_object* v_00_u03b2_3621_, lean_object* v_x_3622_, lean_object* v_x_3623_){
_start:
{
lean_object* v___x_3624_; 
v___x_3624_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__12_spec__17_spec__18___redArg(v_x_3622_, v_x_3623_);
return v___x_3624_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__0(lean_object* v_msg_3626_, lean_object* v___y_3627_, lean_object* v___y_3628_){
_start:
{
lean_object* v___f_3630_; lean_object* v___x_8563__overap_3631_; lean_object* v___x_3632_; 
v___f_3630_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__0___closed__0));
v___x_8563__overap_3631_ = lean_panic_fn_borrowed(v___f_3630_, v_msg_3626_);
lean_inc(v___y_3628_);
lean_inc_ref(v___y_3627_);
v___x_3632_ = lean_apply_3(v___x_8563__overap_3631_, v___y_3627_, v___y_3628_, lean_box(0));
return v___x_3632_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__0___boxed(lean_object* v_msg_3633_, lean_object* v___y_3634_, lean_object* v___y_3635_, lean_object* v___y_3636_){
_start:
{
lean_object* v_res_3637_; 
v_res_3637_ = l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__0(v_msg_3633_, v___y_3634_, v___y_3635_);
lean_dec(v___y_3635_);
lean_dec_ref(v___y_3634_);
return v_res_3637_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___lam__0(lean_object* v_newDecls_3638_, lean_object* v_newArgs_3639_, lean_object* v_____r_3640_, lean_object* v___y_3641_, lean_object* v___y_3642_, lean_object* v___y_3643_){
_start:
{
lean_object* v___x_3645_; lean_object* v___x_3646_; lean_object* v___x_3647_; 
v___x_3645_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3645_, 0, v_newDecls_3638_);
lean_ctor_set(v___x_3645_, 1, v_newArgs_3639_);
v___x_3646_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3646_, 0, v___x_3645_);
lean_ctor_set(v___x_3646_, 1, v___y_3641_);
v___x_3647_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3647_, 0, v___x_3646_);
return v___x_3647_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___lam__0___boxed(lean_object* v_newDecls_3648_, lean_object* v_newArgs_3649_, lean_object* v_____r_3650_, lean_object* v___y_3651_, lean_object* v___y_3652_, lean_object* v___y_3653_, lean_object* v___y_3654_){
_start:
{
lean_object* v_res_3655_; 
v_res_3655_ = l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___lam__0(v_newDecls_3648_, v_newArgs_3649_, v_____r_3650_, v___y_3651_, v___y_3652_, v___y_3653_);
lean_dec(v___y_3653_);
lean_dec_ref(v___y_3652_);
return v_res_3655_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__6(lean_object* v_cls_3656_, lean_object* v_msg_3657_, lean_object* v___y_3658_, lean_object* v___y_3659_){
_start:
{
lean_object* v_ref_3661_; lean_object* v___x_3662_; lean_object* v_a_3663_; lean_object* v___x_3665_; uint8_t v_isShared_3666_; uint8_t v_isSharedCheck_3708_; 
v_ref_3661_ = lean_ctor_get(v___y_3658_, 5);
v___x_3662_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10(v_msg_3657_, v___y_3658_, v___y_3659_);
v_a_3663_ = lean_ctor_get(v___x_3662_, 0);
v_isSharedCheck_3708_ = !lean_is_exclusive(v___x_3662_);
if (v_isSharedCheck_3708_ == 0)
{
v___x_3665_ = v___x_3662_;
v_isShared_3666_ = v_isSharedCheck_3708_;
goto v_resetjp_3664_;
}
else
{
lean_inc(v_a_3663_);
lean_dec(v___x_3662_);
v___x_3665_ = lean_box(0);
v_isShared_3666_ = v_isSharedCheck_3708_;
goto v_resetjp_3664_;
}
v_resetjp_3664_:
{
lean_object* v___x_3667_; lean_object* v_traceState_3668_; lean_object* v_env_3669_; lean_object* v_nextMacroScope_3670_; lean_object* v_ngen_3671_; lean_object* v_auxDeclNGen_3672_; lean_object* v_cache_3673_; lean_object* v_messages_3674_; lean_object* v_infoState_3675_; lean_object* v_snapshotTasks_3676_; lean_object* v_newDecls_3677_; lean_object* v___x_3679_; uint8_t v_isShared_3680_; uint8_t v_isSharedCheck_3707_; 
v___x_3667_ = lean_st_ref_take(v___y_3659_);
v_traceState_3668_ = lean_ctor_get(v___x_3667_, 4);
v_env_3669_ = lean_ctor_get(v___x_3667_, 0);
v_nextMacroScope_3670_ = lean_ctor_get(v___x_3667_, 1);
v_ngen_3671_ = lean_ctor_get(v___x_3667_, 2);
v_auxDeclNGen_3672_ = lean_ctor_get(v___x_3667_, 3);
v_cache_3673_ = lean_ctor_get(v___x_3667_, 5);
v_messages_3674_ = lean_ctor_get(v___x_3667_, 6);
v_infoState_3675_ = lean_ctor_get(v___x_3667_, 7);
v_snapshotTasks_3676_ = lean_ctor_get(v___x_3667_, 8);
v_newDecls_3677_ = lean_ctor_get(v___x_3667_, 9);
v_isSharedCheck_3707_ = !lean_is_exclusive(v___x_3667_);
if (v_isSharedCheck_3707_ == 0)
{
v___x_3679_ = v___x_3667_;
v_isShared_3680_ = v_isSharedCheck_3707_;
goto v_resetjp_3678_;
}
else
{
lean_inc(v_newDecls_3677_);
lean_inc(v_snapshotTasks_3676_);
lean_inc(v_infoState_3675_);
lean_inc(v_messages_3674_);
lean_inc(v_cache_3673_);
lean_inc(v_traceState_3668_);
lean_inc(v_auxDeclNGen_3672_);
lean_inc(v_ngen_3671_);
lean_inc(v_nextMacroScope_3670_);
lean_inc(v_env_3669_);
lean_dec(v___x_3667_);
v___x_3679_ = lean_box(0);
v_isShared_3680_ = v_isSharedCheck_3707_;
goto v_resetjp_3678_;
}
v_resetjp_3678_:
{
uint64_t v_tid_3681_; lean_object* v_traces_3682_; lean_object* v___x_3684_; uint8_t v_isShared_3685_; uint8_t v_isSharedCheck_3706_; 
v_tid_3681_ = lean_ctor_get_uint64(v_traceState_3668_, sizeof(void*)*1);
v_traces_3682_ = lean_ctor_get(v_traceState_3668_, 0);
v_isSharedCheck_3706_ = !lean_is_exclusive(v_traceState_3668_);
if (v_isSharedCheck_3706_ == 0)
{
v___x_3684_ = v_traceState_3668_;
v_isShared_3685_ = v_isSharedCheck_3706_;
goto v_resetjp_3683_;
}
else
{
lean_inc(v_traces_3682_);
lean_dec(v_traceState_3668_);
v___x_3684_ = lean_box(0);
v_isShared_3685_ = v_isSharedCheck_3706_;
goto v_resetjp_3683_;
}
v_resetjp_3683_:
{
lean_object* v___x_3686_; double v___x_3687_; uint8_t v___x_3688_; lean_object* v___x_3689_; lean_object* v___x_3690_; lean_object* v___x_3691_; lean_object* v___x_3692_; lean_object* v___x_3693_; lean_object* v___x_3694_; lean_object* v___x_3696_; 
v___x_3686_ = lean_box(0);
v___x_3687_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6___closed__0);
v___x_3688_ = 0;
v___x_3689_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6___closed__1));
v___x_3690_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3690_, 0, v_cls_3656_);
lean_ctor_set(v___x_3690_, 1, v___x_3686_);
lean_ctor_set(v___x_3690_, 2, v___x_3689_);
lean_ctor_set_float(v___x_3690_, sizeof(void*)*3, v___x_3687_);
lean_ctor_set_float(v___x_3690_, sizeof(void*)*3 + 8, v___x_3687_);
lean_ctor_set_uint8(v___x_3690_, sizeof(void*)*3 + 16, v___x_3688_);
v___x_3691_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6___closed__2));
v___x_3692_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3692_, 0, v___x_3690_);
lean_ctor_set(v___x_3692_, 1, v_a_3663_);
lean_ctor_set(v___x_3692_, 2, v___x_3691_);
lean_inc(v_ref_3661_);
v___x_3693_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3693_, 0, v_ref_3661_);
lean_ctor_set(v___x_3693_, 1, v___x_3692_);
v___x_3694_ = l_Lean_PersistentArray_push___redArg(v_traces_3682_, v___x_3693_);
if (v_isShared_3685_ == 0)
{
lean_ctor_set(v___x_3684_, 0, v___x_3694_);
v___x_3696_ = v___x_3684_;
goto v_reusejp_3695_;
}
else
{
lean_object* v_reuseFailAlloc_3705_; 
v_reuseFailAlloc_3705_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3705_, 0, v___x_3694_);
lean_ctor_set_uint64(v_reuseFailAlloc_3705_, sizeof(void*)*1, v_tid_3681_);
v___x_3696_ = v_reuseFailAlloc_3705_;
goto v_reusejp_3695_;
}
v_reusejp_3695_:
{
lean_object* v___x_3698_; 
if (v_isShared_3680_ == 0)
{
lean_ctor_set(v___x_3679_, 4, v___x_3696_);
v___x_3698_ = v___x_3679_;
goto v_reusejp_3697_;
}
else
{
lean_object* v_reuseFailAlloc_3704_; 
v_reuseFailAlloc_3704_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3704_, 0, v_env_3669_);
lean_ctor_set(v_reuseFailAlloc_3704_, 1, v_nextMacroScope_3670_);
lean_ctor_set(v_reuseFailAlloc_3704_, 2, v_ngen_3671_);
lean_ctor_set(v_reuseFailAlloc_3704_, 3, v_auxDeclNGen_3672_);
lean_ctor_set(v_reuseFailAlloc_3704_, 4, v___x_3696_);
lean_ctor_set(v_reuseFailAlloc_3704_, 5, v_cache_3673_);
lean_ctor_set(v_reuseFailAlloc_3704_, 6, v_messages_3674_);
lean_ctor_set(v_reuseFailAlloc_3704_, 7, v_infoState_3675_);
lean_ctor_set(v_reuseFailAlloc_3704_, 8, v_snapshotTasks_3676_);
lean_ctor_set(v_reuseFailAlloc_3704_, 9, v_newDecls_3677_);
v___x_3698_ = v_reuseFailAlloc_3704_;
goto v_reusejp_3697_;
}
v_reusejp_3697_:
{
lean_object* v___x_3699_; lean_object* v___x_3700_; lean_object* v___x_3702_; 
v___x_3699_ = lean_st_ref_set(v___y_3659_, v___x_3698_);
v___x_3700_ = lean_box(0);
if (v_isShared_3666_ == 0)
{
lean_ctor_set(v___x_3665_, 0, v___x_3700_);
v___x_3702_ = v___x_3665_;
goto v_reusejp_3701_;
}
else
{
lean_object* v_reuseFailAlloc_3703_; 
v_reuseFailAlloc_3703_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3703_, 0, v___x_3700_);
v___x_3702_ = v_reuseFailAlloc_3703_;
goto v_reusejp_3701_;
}
v_reusejp_3701_:
{
return v___x_3702_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__6___boxed(lean_object* v_cls_3709_, lean_object* v_msg_3710_, lean_object* v___y_3711_, lean_object* v___y_3712_, lean_object* v___y_3713_){
_start:
{
lean_object* v_res_3714_; 
v_res_3714_ = l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__6(v_cls_3709_, v_msg_3710_, v___y_3711_, v___y_3712_);
lean_dec(v___y_3712_);
lean_dec_ref(v___y_3711_);
return v_res_3714_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__4(size_t v_sz_3715_, size_t v_i_3716_, lean_object* v_bs_3717_){
_start:
{
uint8_t v___x_3718_; 
v___x_3718_ = lean_usize_dec_lt(v_i_3716_, v_sz_3715_);
if (v___x_3718_ == 0)
{
return v_bs_3717_;
}
else
{
lean_object* v_v_3719_; lean_object* v___x_3720_; lean_object* v_bs_x27_3721_; lean_object* v___x_3722_; lean_object* v___x_3723_; size_t v___x_3724_; size_t v___x_3725_; lean_object* v___x_3726_; 
v_v_3719_ = lean_array_uget(v_bs_3717_, v_i_3716_);
v___x_3720_ = lean_unsigned_to_nat(0u);
v_bs_x27_3721_ = lean_array_uset(v_bs_3717_, v_i_3716_, v___x_3720_);
v___x_3722_ = l_Lean_LocalDecl_fvarId(v_v_3719_);
lean_dec(v_v_3719_);
v___x_3723_ = l_Lean_mkFVar(v___x_3722_);
v___x_3724_ = ((size_t)1ULL);
v___x_3725_ = lean_usize_add(v_i_3716_, v___x_3724_);
v___x_3726_ = lean_array_uset(v_bs_x27_3721_, v_i_3716_, v___x_3723_);
v_i_3716_ = v___x_3725_;
v_bs_3717_ = v___x_3726_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__4___boxed(lean_object* v_sz_3728_, lean_object* v_i_3729_, lean_object* v_bs_3730_){
_start:
{
size_t v_sz_boxed_3731_; size_t v_i_boxed_3732_; lean_object* v_res_3733_; 
v_sz_boxed_3731_ = lean_unbox_usize(v_sz_3728_);
lean_dec(v_sz_3728_);
v_i_boxed_3732_ = lean_unbox_usize(v_i_3729_);
lean_dec(v_i_3729_);
v_res_3733_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__4(v_sz_boxed_3731_, v_i_boxed_3732_, v_bs_3730_);
return v_res_3733_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__3(lean_object* v___x_3734_, lean_object* v_as_3735_, size_t v_sz_3736_, size_t v_i_3737_, lean_object* v_b_3738_, lean_object* v___y_3739_, lean_object* v___y_3740_, lean_object* v___y_3741_){
_start:
{
uint8_t v___x_3743_; 
v___x_3743_ = lean_usize_dec_lt(v_i_3737_, v_sz_3736_);
if (v___x_3743_ == 0)
{
lean_object* v___x_3744_; lean_object* v___x_3745_; 
lean_dec_ref(v___x_3734_);
v___x_3744_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3744_, 0, v_b_3738_);
lean_ctor_set(v___x_3744_, 1, v___y_3739_);
v___x_3745_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3745_, 0, v___x_3744_);
return v___x_3745_;
}
else
{
lean_object* v_a_3746_; lean_object* v___x_3747_; lean_object* v___x_3748_; 
v_a_3746_ = lean_array_uget_borrowed(v_as_3735_, v_i_3737_);
v___x_3747_ = l_Lean_LocalDecl_fvarId(v_a_3746_);
lean_inc_ref(v___x_3734_);
v___x_3748_ = l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit(v___x_3734_, v___x_3747_, v___y_3739_, v___y_3740_, v___y_3741_);
lean_dec(v___x_3747_);
if (lean_obj_tag(v___x_3748_) == 0)
{
lean_object* v_a_3749_; lean_object* v_snd_3750_; lean_object* v___x_3751_; size_t v___x_3752_; size_t v___x_3753_; 
v_a_3749_ = lean_ctor_get(v___x_3748_, 0);
lean_inc(v_a_3749_);
lean_dec_ref(v___x_3748_);
v_snd_3750_ = lean_ctor_get(v_a_3749_, 1);
lean_inc(v_snd_3750_);
lean_dec(v_a_3749_);
v___x_3751_ = lean_box(0);
v___x_3752_ = ((size_t)1ULL);
v___x_3753_ = lean_usize_add(v_i_3737_, v___x_3752_);
v_i_3737_ = v___x_3753_;
v_b_3738_ = v___x_3751_;
v___y_3739_ = v_snd_3750_;
goto _start;
}
else
{
lean_dec_ref(v___x_3734_);
return v___x_3748_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__3___boxed(lean_object* v___x_3755_, lean_object* v_as_3756_, lean_object* v_sz_3757_, lean_object* v_i_3758_, lean_object* v_b_3759_, lean_object* v___y_3760_, lean_object* v___y_3761_, lean_object* v___y_3762_, lean_object* v___y_3763_){
_start:
{
size_t v_sz_boxed_3764_; size_t v_i_boxed_3765_; lean_object* v_res_3766_; 
v_sz_boxed_3764_ = lean_unbox_usize(v_sz_3757_);
lean_dec(v_sz_3757_);
v_i_boxed_3765_ = lean_unbox_usize(v_i_3758_);
lean_dec(v_i_3758_);
v_res_3766_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__3(v___x_3755_, v_as_3756_, v_sz_boxed_3764_, v_i_boxed_3765_, v_b_3759_, v___y_3760_, v___y_3761_, v___y_3762_);
lean_dec(v___y_3762_);
lean_dec_ref(v___y_3761_);
lean_dec_ref(v_as_3756_);
return v_res_3766_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__5(lean_object* v_a_3767_, lean_object* v_a_3768_){
_start:
{
if (lean_obj_tag(v_a_3767_) == 0)
{
lean_object* v___x_3769_; 
v___x_3769_ = l_List_reverse___redArg(v_a_3768_);
return v___x_3769_;
}
else
{
lean_object* v_head_3770_; lean_object* v_tail_3771_; lean_object* v___x_3773_; uint8_t v_isShared_3774_; uint8_t v_isSharedCheck_3780_; 
v_head_3770_ = lean_ctor_get(v_a_3767_, 0);
v_tail_3771_ = lean_ctor_get(v_a_3767_, 1);
v_isSharedCheck_3780_ = !lean_is_exclusive(v_a_3767_);
if (v_isSharedCheck_3780_ == 0)
{
v___x_3773_ = v_a_3767_;
v_isShared_3774_ = v_isSharedCheck_3780_;
goto v_resetjp_3772_;
}
else
{
lean_inc(v_tail_3771_);
lean_inc(v_head_3770_);
lean_dec(v_a_3767_);
v___x_3773_ = lean_box(0);
v_isShared_3774_ = v_isSharedCheck_3780_;
goto v_resetjp_3772_;
}
v_resetjp_3772_:
{
lean_object* v___x_3775_; lean_object* v___x_3777_; 
v___x_3775_ = l_Lean_MessageData_ofExpr(v_head_3770_);
if (v_isShared_3774_ == 0)
{
lean_ctor_set(v___x_3773_, 1, v_a_3768_);
lean_ctor_set(v___x_3773_, 0, v___x_3775_);
v___x_3777_ = v___x_3773_;
goto v_reusejp_3776_;
}
else
{
lean_object* v_reuseFailAlloc_3779_; 
v_reuseFailAlloc_3779_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3779_, 0, v___x_3775_);
lean_ctor_set(v_reuseFailAlloc_3779_, 1, v_a_3768_);
v___x_3777_ = v_reuseFailAlloc_3779_;
goto v_reusejp_3776_;
}
v_reusejp_3776_:
{
v_a_3767_ = v_tail_3771_;
v_a_3768_ = v___x_3777_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__1_spec__1___redArg(lean_object* v_a_3781_, lean_object* v_b_3782_, lean_object* v_x_3783_){
_start:
{
if (lean_obj_tag(v_x_3783_) == 0)
{
lean_dec(v_b_3782_);
lean_dec(v_a_3781_);
return v_x_3783_;
}
else
{
lean_object* v_key_3784_; lean_object* v_value_3785_; lean_object* v_tail_3786_; lean_object* v___x_3788_; uint8_t v_isShared_3789_; uint8_t v_isSharedCheck_3798_; 
v_key_3784_ = lean_ctor_get(v_x_3783_, 0);
v_value_3785_ = lean_ctor_get(v_x_3783_, 1);
v_tail_3786_ = lean_ctor_get(v_x_3783_, 2);
v_isSharedCheck_3798_ = !lean_is_exclusive(v_x_3783_);
if (v_isSharedCheck_3798_ == 0)
{
v___x_3788_ = v_x_3783_;
v_isShared_3789_ = v_isSharedCheck_3798_;
goto v_resetjp_3787_;
}
else
{
lean_inc(v_tail_3786_);
lean_inc(v_value_3785_);
lean_inc(v_key_3784_);
lean_dec(v_x_3783_);
v___x_3788_ = lean_box(0);
v_isShared_3789_ = v_isSharedCheck_3798_;
goto v_resetjp_3787_;
}
v_resetjp_3787_:
{
uint8_t v___x_3790_; 
v___x_3790_ = l_Lean_instBEqFVarId_beq(v_key_3784_, v_a_3781_);
if (v___x_3790_ == 0)
{
lean_object* v___x_3791_; lean_object* v___x_3793_; 
v___x_3791_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__1_spec__1___redArg(v_a_3781_, v_b_3782_, v_tail_3786_);
if (v_isShared_3789_ == 0)
{
lean_ctor_set(v___x_3788_, 2, v___x_3791_);
v___x_3793_ = v___x_3788_;
goto v_reusejp_3792_;
}
else
{
lean_object* v_reuseFailAlloc_3794_; 
v_reuseFailAlloc_3794_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3794_, 0, v_key_3784_);
lean_ctor_set(v_reuseFailAlloc_3794_, 1, v_value_3785_);
lean_ctor_set(v_reuseFailAlloc_3794_, 2, v___x_3791_);
v___x_3793_ = v_reuseFailAlloc_3794_;
goto v_reusejp_3792_;
}
v_reusejp_3792_:
{
return v___x_3793_;
}
}
else
{
lean_object* v___x_3796_; 
lean_dec(v_value_3785_);
lean_dec(v_key_3784_);
if (v_isShared_3789_ == 0)
{
lean_ctor_set(v___x_3788_, 1, v_b_3782_);
lean_ctor_set(v___x_3788_, 0, v_a_3781_);
v___x_3796_ = v___x_3788_;
goto v_reusejp_3795_;
}
else
{
lean_object* v_reuseFailAlloc_3797_; 
v_reuseFailAlloc_3797_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3797_, 0, v_a_3781_);
lean_ctor_set(v_reuseFailAlloc_3797_, 1, v_b_3782_);
lean_ctor_set(v_reuseFailAlloc_3797_, 2, v_tail_3786_);
v___x_3796_ = v_reuseFailAlloc_3797_;
goto v_reusejp_3795_;
}
v_reusejp_3795_:
{
return v___x_3796_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__1___redArg(lean_object* v_m_3799_, lean_object* v_a_3800_, lean_object* v_b_3801_){
_start:
{
lean_object* v_size_3802_; lean_object* v_buckets_3803_; lean_object* v___x_3805_; uint8_t v_isShared_3806_; uint8_t v_isSharedCheck_3846_; 
v_size_3802_ = lean_ctor_get(v_m_3799_, 0);
v_buckets_3803_ = lean_ctor_get(v_m_3799_, 1);
v_isSharedCheck_3846_ = !lean_is_exclusive(v_m_3799_);
if (v_isSharedCheck_3846_ == 0)
{
v___x_3805_ = v_m_3799_;
v_isShared_3806_ = v_isSharedCheck_3846_;
goto v_resetjp_3804_;
}
else
{
lean_inc(v_buckets_3803_);
lean_inc(v_size_3802_);
lean_dec(v_m_3799_);
v___x_3805_ = lean_box(0);
v_isShared_3806_ = v_isSharedCheck_3846_;
goto v_resetjp_3804_;
}
v_resetjp_3804_:
{
lean_object* v___x_3807_; uint64_t v___x_3808_; uint64_t v___x_3809_; uint64_t v___x_3810_; uint64_t v_fold_3811_; uint64_t v___x_3812_; uint64_t v___x_3813_; uint64_t v___x_3814_; size_t v___x_3815_; size_t v___x_3816_; size_t v___x_3817_; size_t v___x_3818_; size_t v___x_3819_; lean_object* v_bkt_3820_; uint8_t v___x_3821_; 
v___x_3807_ = lean_array_get_size(v_buckets_3803_);
v___x_3808_ = l_Lean_instHashableFVarId_hash(v_a_3800_);
v___x_3809_ = 32ULL;
v___x_3810_ = lean_uint64_shift_right(v___x_3808_, v___x_3809_);
v_fold_3811_ = lean_uint64_xor(v___x_3808_, v___x_3810_);
v___x_3812_ = 16ULL;
v___x_3813_ = lean_uint64_shift_right(v_fold_3811_, v___x_3812_);
v___x_3814_ = lean_uint64_xor(v_fold_3811_, v___x_3813_);
v___x_3815_ = lean_uint64_to_usize(v___x_3814_);
v___x_3816_ = lean_usize_of_nat(v___x_3807_);
v___x_3817_ = ((size_t)1ULL);
v___x_3818_ = lean_usize_sub(v___x_3816_, v___x_3817_);
v___x_3819_ = lean_usize_land(v___x_3815_, v___x_3818_);
v_bkt_3820_ = lean_array_uget_borrowed(v_buckets_3803_, v___x_3819_);
v___x_3821_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1_spec__2___redArg(v_a_3800_, v_bkt_3820_);
if (v___x_3821_ == 0)
{
lean_object* v___x_3822_; lean_object* v_size_x27_3823_; lean_object* v___x_3824_; lean_object* v_buckets_x27_3825_; lean_object* v___x_3826_; lean_object* v___x_3827_; lean_object* v___x_3828_; lean_object* v___x_3829_; lean_object* v___x_3830_; uint8_t v___x_3831_; 
v___x_3822_ = lean_unsigned_to_nat(1u);
v_size_x27_3823_ = lean_nat_add(v_size_3802_, v___x_3822_);
lean_dec(v_size_3802_);
lean_inc(v_bkt_3820_);
v___x_3824_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3824_, 0, v_a_3800_);
lean_ctor_set(v___x_3824_, 1, v_b_3801_);
lean_ctor_set(v___x_3824_, 2, v_bkt_3820_);
v_buckets_x27_3825_ = lean_array_uset(v_buckets_3803_, v___x_3819_, v___x_3824_);
v___x_3826_ = lean_unsigned_to_nat(4u);
v___x_3827_ = lean_nat_mul(v_size_x27_3823_, v___x_3826_);
v___x_3828_ = lean_unsigned_to_nat(3u);
v___x_3829_ = lean_nat_div(v___x_3827_, v___x_3828_);
lean_dec(v___x_3827_);
v___x_3830_ = lean_array_get_size(v_buckets_x27_3825_);
v___x_3831_ = lean_nat_dec_le(v___x_3829_, v___x_3830_);
lean_dec(v___x_3829_);
if (v___x_3831_ == 0)
{
lean_object* v_val_3832_; lean_object* v___x_3834_; 
v_val_3832_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__4___redArg(v_buckets_x27_3825_);
if (v_isShared_3806_ == 0)
{
lean_ctor_set(v___x_3805_, 1, v_val_3832_);
lean_ctor_set(v___x_3805_, 0, v_size_x27_3823_);
v___x_3834_ = v___x_3805_;
goto v_reusejp_3833_;
}
else
{
lean_object* v_reuseFailAlloc_3835_; 
v_reuseFailAlloc_3835_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3835_, 0, v_size_x27_3823_);
lean_ctor_set(v_reuseFailAlloc_3835_, 1, v_val_3832_);
v___x_3834_ = v_reuseFailAlloc_3835_;
goto v_reusejp_3833_;
}
v_reusejp_3833_:
{
return v___x_3834_;
}
}
else
{
lean_object* v___x_3837_; 
if (v_isShared_3806_ == 0)
{
lean_ctor_set(v___x_3805_, 1, v_buckets_x27_3825_);
lean_ctor_set(v___x_3805_, 0, v_size_x27_3823_);
v___x_3837_ = v___x_3805_;
goto v_reusejp_3836_;
}
else
{
lean_object* v_reuseFailAlloc_3838_; 
v_reuseFailAlloc_3838_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3838_, 0, v_size_x27_3823_);
lean_ctor_set(v_reuseFailAlloc_3838_, 1, v_buckets_x27_3825_);
v___x_3837_ = v_reuseFailAlloc_3838_;
goto v_reusejp_3836_;
}
v_reusejp_3836_:
{
return v___x_3837_;
}
}
}
else
{
lean_object* v___x_3839_; lean_object* v_buckets_x27_3840_; lean_object* v___x_3841_; lean_object* v___x_3842_; lean_object* v___x_3844_; 
lean_inc(v_bkt_3820_);
v___x_3839_ = lean_box(0);
v_buckets_x27_3840_ = lean_array_uset(v_buckets_3803_, v___x_3819_, v___x_3839_);
v___x_3841_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__1_spec__1___redArg(v_a_3800_, v_b_3801_, v_bkt_3820_);
v___x_3842_ = lean_array_uset(v_buckets_x27_3840_, v___x_3819_, v___x_3841_);
if (v_isShared_3806_ == 0)
{
lean_ctor_set(v___x_3805_, 1, v___x_3842_);
v___x_3844_ = v___x_3805_;
goto v_reusejp_3843_;
}
else
{
lean_object* v_reuseFailAlloc_3845_; 
v_reuseFailAlloc_3845_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3845_, 0, v_size_3802_);
lean_ctor_set(v_reuseFailAlloc_3845_, 1, v___x_3842_);
v___x_3844_ = v_reuseFailAlloc_3845_;
goto v_reusejp_3843_;
}
v_reusejp_3843_:
{
return v___x_3844_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__2___redArg(lean_object* v_as_3847_, size_t v_sz_3848_, size_t v_i_3849_, lean_object* v_b_3850_){
_start:
{
uint8_t v___x_3852_; 
v___x_3852_ = lean_usize_dec_lt(v_i_3849_, v_sz_3848_);
if (v___x_3852_ == 0)
{
lean_object* v___x_3853_; 
v___x_3853_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3853_, 0, v_b_3850_);
return v___x_3853_;
}
else
{
lean_object* v_snd_3854_; lean_object* v_fst_3855_; lean_object* v___x_3857_; uint8_t v_isShared_3858_; uint8_t v_isSharedCheck_3890_; 
v_snd_3854_ = lean_ctor_get(v_b_3850_, 1);
v_fst_3855_ = lean_ctor_get(v_b_3850_, 0);
v_isSharedCheck_3890_ = !lean_is_exclusive(v_b_3850_);
if (v_isSharedCheck_3890_ == 0)
{
v___x_3857_ = v_b_3850_;
v_isShared_3858_ = v_isSharedCheck_3890_;
goto v_resetjp_3856_;
}
else
{
lean_inc(v_snd_3854_);
lean_inc(v_fst_3855_);
lean_dec(v_b_3850_);
v___x_3857_ = lean_box(0);
v_isShared_3858_ = v_isSharedCheck_3890_;
goto v_resetjp_3856_;
}
v_resetjp_3856_:
{
lean_object* v_array_3859_; lean_object* v_start_3860_; lean_object* v_stop_3861_; uint8_t v___x_3862_; 
v_array_3859_ = lean_ctor_get(v_snd_3854_, 0);
v_start_3860_ = lean_ctor_get(v_snd_3854_, 1);
v_stop_3861_ = lean_ctor_get(v_snd_3854_, 2);
v___x_3862_ = lean_nat_dec_lt(v_start_3860_, v_stop_3861_);
if (v___x_3862_ == 0)
{
lean_object* v___x_3864_; 
if (v_isShared_3858_ == 0)
{
v___x_3864_ = v___x_3857_;
goto v_reusejp_3863_;
}
else
{
lean_object* v_reuseFailAlloc_3866_; 
v_reuseFailAlloc_3866_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3866_, 0, v_fst_3855_);
lean_ctor_set(v_reuseFailAlloc_3866_, 1, v_snd_3854_);
v___x_3864_ = v_reuseFailAlloc_3866_;
goto v_reusejp_3863_;
}
v_reusejp_3863_:
{
lean_object* v___x_3865_; 
v___x_3865_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3865_, 0, v___x_3864_);
return v___x_3865_;
}
}
else
{
lean_object* v___x_3868_; uint8_t v_isShared_3869_; uint8_t v_isSharedCheck_3886_; 
lean_inc(v_stop_3861_);
lean_inc(v_start_3860_);
lean_inc_ref(v_array_3859_);
v_isSharedCheck_3886_ = !lean_is_exclusive(v_snd_3854_);
if (v_isSharedCheck_3886_ == 0)
{
lean_object* v_unused_3887_; lean_object* v_unused_3888_; lean_object* v_unused_3889_; 
v_unused_3887_ = lean_ctor_get(v_snd_3854_, 2);
lean_dec(v_unused_3887_);
v_unused_3888_ = lean_ctor_get(v_snd_3854_, 1);
lean_dec(v_unused_3888_);
v_unused_3889_ = lean_ctor_get(v_snd_3854_, 0);
lean_dec(v_unused_3889_);
v___x_3868_ = v_snd_3854_;
v_isShared_3869_ = v_isSharedCheck_3886_;
goto v_resetjp_3867_;
}
else
{
lean_dec(v_snd_3854_);
v___x_3868_ = lean_box(0);
v_isShared_3869_ = v_isSharedCheck_3886_;
goto v_resetjp_3867_;
}
v_resetjp_3867_:
{
lean_object* v_a_3870_; lean_object* v___x_3871_; lean_object* v___x_3872_; lean_object* v___x_3873_; lean_object* v___x_3875_; 
v_a_3870_ = lean_array_uget_borrowed(v_as_3847_, v_i_3849_);
v___x_3871_ = lean_array_fget(v_array_3859_, v_start_3860_);
v___x_3872_ = lean_unsigned_to_nat(1u);
v___x_3873_ = lean_nat_add(v_start_3860_, v___x_3872_);
lean_dec(v_start_3860_);
if (v_isShared_3869_ == 0)
{
lean_ctor_set(v___x_3868_, 1, v___x_3873_);
v___x_3875_ = v___x_3868_;
goto v_reusejp_3874_;
}
else
{
lean_object* v_reuseFailAlloc_3885_; 
v_reuseFailAlloc_3885_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3885_, 0, v_array_3859_);
lean_ctor_set(v_reuseFailAlloc_3885_, 1, v___x_3873_);
lean_ctor_set(v_reuseFailAlloc_3885_, 2, v_stop_3861_);
v___x_3875_ = v_reuseFailAlloc_3885_;
goto v_reusejp_3874_;
}
v_reusejp_3874_:
{
lean_object* v___x_3876_; lean_object* v___x_3878_; 
v___x_3876_ = l_Lean_LocalDecl_fvarId(v_a_3870_);
lean_inc(v_a_3870_);
if (v_isShared_3858_ == 0)
{
lean_ctor_set(v___x_3857_, 1, v___x_3871_);
lean_ctor_set(v___x_3857_, 0, v_a_3870_);
v___x_3878_ = v___x_3857_;
goto v_reusejp_3877_;
}
else
{
lean_object* v_reuseFailAlloc_3884_; 
v_reuseFailAlloc_3884_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3884_, 0, v_a_3870_);
lean_ctor_set(v_reuseFailAlloc_3884_, 1, v___x_3871_);
v___x_3878_ = v_reuseFailAlloc_3884_;
goto v_reusejp_3877_;
}
v_reusejp_3877_:
{
lean_object* v___x_3879_; lean_object* v___x_3880_; size_t v___x_3881_; size_t v___x_3882_; 
v___x_3879_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__1___redArg(v_fst_3855_, v___x_3876_, v___x_3878_);
v___x_3880_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3880_, 0, v___x_3879_);
lean_ctor_set(v___x_3880_, 1, v___x_3875_);
v___x_3881_ = ((size_t)1ULL);
v___x_3882_ = lean_usize_add(v_i_3849_, v___x_3881_);
v_i_3849_ = v___x_3882_;
v_b_3850_ = v___x_3880_;
goto _start;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__2___redArg___boxed(lean_object* v_as_3891_, lean_object* v_sz_3892_, lean_object* v_i_3893_, lean_object* v_b_3894_, lean_object* v___y_3895_){
_start:
{
size_t v_sz_boxed_3896_; size_t v_i_boxed_3897_; lean_object* v_res_3898_; 
v_sz_boxed_3896_ = lean_unbox_usize(v_sz_3892_);
lean_dec(v_sz_3892_);
v_i_boxed_3897_ = lean_unbox_usize(v_i_3893_);
lean_dec(v_i_3893_);
v_res_3898_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__2___redArg(v_as_3891_, v_sz_boxed_3896_, v_i_boxed_3897_, v_b_3894_);
lean_dec_ref(v_as_3891_);
return v_res_3898_;
}
}
static lean_object* _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__2(void){
_start:
{
lean_object* v___x_3901_; lean_object* v___x_3902_; lean_object* v___x_3903_; lean_object* v___x_3904_; lean_object* v___x_3905_; lean_object* v___x_3906_; 
v___x_3901_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__1));
v___x_3902_ = lean_unsigned_to_nat(2u);
v___x_3903_ = lean_unsigned_to_nat(366u);
v___x_3904_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__0));
v___x_3905_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__2));
v___x_3906_ = l_mkPanicMessageWithDecl(v___x_3905_, v___x_3904_, v___x_3903_, v___x_3902_, v___x_3901_);
return v___x_3906_;
}
}
static lean_object* _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__4(void){
_start:
{
lean_object* v___x_3908_; lean_object* v___x_3909_; lean_object* v___x_3910_; lean_object* v___x_3911_; lean_object* v___x_3912_; lean_object* v___x_3913_; 
v___x_3908_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__3));
v___x_3909_ = lean_unsigned_to_nat(2u);
v___x_3910_ = lean_unsigned_to_nat(367u);
v___x_3911_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__0));
v___x_3912_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__2));
v___x_3913_ = l_mkPanicMessageWithDecl(v___x_3912_, v___x_3911_, v___x_3910_, v___x_3909_, v___x_3908_);
return v___x_3913_;
}
}
static lean_object* _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__5(void){
_start:
{
lean_object* v___x_3914_; lean_object* v___x_3915_; lean_object* v___x_3916_; 
v___x_3914_ = lean_box(0);
v___x_3915_ = lean_unsigned_to_nat(16u);
v___x_3916_ = lean_mk_array(v___x_3915_, v___x_3914_);
return v___x_3916_;
}
}
static lean_object* _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__6(void){
_start:
{
lean_object* v___x_3917_; lean_object* v___x_3918_; lean_object* v___x_3919_; 
v___x_3917_ = lean_obj_once(&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__5, &l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__5_once, _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__5);
v___x_3918_ = lean_unsigned_to_nat(0u);
v___x_3919_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3919_, 0, v___x_3918_);
lean_ctor_set(v___x_3919_, 1, v___x_3917_);
return v___x_3919_;
}
}
static lean_object* _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__8(void){
_start:
{
lean_object* v___x_3921_; lean_object* v___x_3922_; 
v___x_3921_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__7));
v___x_3922_ = l_Lean_stringToMessageData(v___x_3921_);
return v___x_3922_;
}
}
static lean_object* _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__10(void){
_start:
{
lean_object* v___x_3924_; lean_object* v___x_3925_; 
v___x_3924_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__9));
v___x_3925_ = l_Lean_stringToMessageData(v___x_3924_);
return v___x_3925_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls(lean_object* v_sortedDecls_3926_, lean_object* v_sortedArgs_3927_, lean_object* v_toSortDecls_3928_, lean_object* v_toSortArgs_3929_, lean_object* v_a_3930_, lean_object* v_a_3931_){
_start:
{
lean_object* v___y_3934_; lean_object* v___y_3953_; lean_object* v___y_3954_; lean_object* v___y_3955_; lean_object* v___y_3956_; lean_object* v_snd_3957_; lean_object* v___x_3959_; lean_object* v___x_3960_; uint8_t v___x_3961_; 
v___x_3959_ = lean_array_get_size(v_sortedDecls_3926_);
v___x_3960_ = lean_array_get_size(v_sortedArgs_3927_);
v___x_3961_ = lean_nat_dec_eq(v___x_3959_, v___x_3960_);
if (v___x_3961_ == 0)
{
lean_object* v___x_3962_; lean_object* v___x_3963_; 
lean_dec_ref(v_toSortArgs_3929_);
lean_dec_ref(v_sortedArgs_3927_);
lean_dec_ref(v_sortedDecls_3926_);
v___x_3962_ = lean_obj_once(&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__2, &l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__2_once, _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__2);
v___x_3963_ = l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__0(v___x_3962_, v_a_3930_, v_a_3931_);
return v___x_3963_;
}
else
{
lean_object* v___x_3964_; lean_object* v___x_3965_; uint8_t v___x_3966_; 
v___x_3964_ = lean_array_get_size(v_toSortDecls_3928_);
v___x_3965_ = lean_array_get_size(v_toSortArgs_3929_);
v___x_3966_ = lean_nat_dec_eq(v___x_3964_, v___x_3965_);
if (v___x_3966_ == 0)
{
lean_object* v___x_3967_; lean_object* v___x_3968_; 
lean_dec_ref(v_toSortArgs_3929_);
lean_dec_ref(v_sortedArgs_3927_);
lean_dec_ref(v_sortedDecls_3926_);
v___x_3967_ = lean_obj_once(&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__4, &l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__4_once, _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__4);
v___x_3968_ = l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__0(v___x_3967_, v_a_3930_, v_a_3931_);
return v___x_3968_;
}
else
{
lean_object* v___x_3969_; uint8_t v___x_3970_; 
v___x_3969_ = lean_unsigned_to_nat(0u);
v___x_3970_ = lean_nat_dec_eq(v___x_3964_, v___x_3969_);
if (v___x_3970_ == 0)
{
lean_object* v_options_3971_; lean_object* v_inheritedTraceOptions_3972_; uint8_t v_hasTrace_3973_; lean_object* v_cls_3974_; lean_object* v___y_3976_; lean_object* v___y_3977_; 
v_options_3971_ = lean_ctor_get(v_a_3930_, 2);
v_inheritedTraceOptions_3972_ = lean_ctor_get(v_a_3930_, 13);
v_hasTrace_3973_ = lean_ctor_get_uint8(v_options_3971_, sizeof(void*)*1);
v_cls_3974_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__10));
if (v_hasTrace_3973_ == 0)
{
v___y_3976_ = v_a_3930_;
v___y_3977_ = v_a_3931_;
goto v___jp_3975_;
}
else
{
lean_object* v___x_4078_; uint8_t v___x_4079_; 
v___x_4078_ = lean_obj_once(&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__13, &l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__13_once, _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__13);
v___x_4079_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3972_, v_options_3971_, v___x_4078_);
if (v___x_4079_ == 0)
{
v___y_3976_ = v_a_3930_;
v___y_3977_ = v_a_3931_;
goto v___jp_3975_;
}
else
{
lean_object* v___x_4080_; lean_object* v___x_4081_; 
v___x_4080_ = lean_obj_once(&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__10, &l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__10_once, _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__10);
v___x_4081_ = l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__6(v_cls_3974_, v___x_4080_, v_a_3930_, v_a_3931_);
if (lean_obj_tag(v___x_4081_) == 0)
{
lean_dec_ref(v___x_4081_);
v___y_3976_ = v_a_3930_;
v___y_3977_ = v_a_3931_;
goto v___jp_3975_;
}
else
{
lean_object* v_a_4082_; lean_object* v___x_4084_; uint8_t v_isShared_4085_; uint8_t v_isSharedCheck_4089_; 
lean_dec_ref(v_toSortArgs_3929_);
lean_dec_ref(v_sortedArgs_3927_);
lean_dec_ref(v_sortedDecls_3926_);
v_a_4082_ = lean_ctor_get(v___x_4081_, 0);
v_isSharedCheck_4089_ = !lean_is_exclusive(v___x_4081_);
if (v_isSharedCheck_4089_ == 0)
{
v___x_4084_ = v___x_4081_;
v_isShared_4085_ = v_isSharedCheck_4089_;
goto v_resetjp_4083_;
}
else
{
lean_inc(v_a_4082_);
lean_dec(v___x_4081_);
v___x_4084_ = lean_box(0);
v_isShared_4085_ = v_isSharedCheck_4089_;
goto v_resetjp_4083_;
}
v_resetjp_4083_:
{
lean_object* v___x_4087_; 
if (v_isShared_4085_ == 0)
{
v___x_4087_ = v___x_4084_;
goto v_reusejp_4086_;
}
else
{
lean_object* v_reuseFailAlloc_4088_; 
v_reuseFailAlloc_4088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4088_, 0, v_a_4082_);
v___x_4087_ = v_reuseFailAlloc_4088_;
goto v_reusejp_4086_;
}
v_reusejp_4086_:
{
return v___x_4087_;
}
}
}
}
}
v___jp_3975_:
{
lean_object* v___x_3978_; lean_object* v___x_3979_; lean_object* v___x_3980_; size_t v_sz_3981_; size_t v___x_3982_; lean_object* v___x_3983_; 
v___x_3978_ = lean_obj_once(&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__6, &l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__6_once, _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__6);
v___x_3979_ = l_Array_toSubarray___redArg(v_sortedArgs_3927_, v___x_3969_, v___x_3960_);
v___x_3980_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3980_, 0, v___x_3978_);
lean_ctor_set(v___x_3980_, 1, v___x_3979_);
v_sz_3981_ = lean_array_size(v_sortedDecls_3926_);
v___x_3982_ = ((size_t)0ULL);
v___x_3983_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__2___redArg(v_sortedDecls_3926_, v_sz_3981_, v___x_3982_, v___x_3980_);
if (lean_obj_tag(v___x_3983_) == 0)
{
lean_object* v_a_3984_; lean_object* v_fst_3985_; lean_object* v___x_3987_; uint8_t v_isShared_3988_; uint8_t v_isSharedCheck_4068_; 
v_a_3984_ = lean_ctor_get(v___x_3983_, 0);
lean_inc(v_a_3984_);
lean_dec_ref(v___x_3983_);
v_fst_3985_ = lean_ctor_get(v_a_3984_, 0);
v_isSharedCheck_4068_ = !lean_is_exclusive(v_a_3984_);
if (v_isSharedCheck_4068_ == 0)
{
lean_object* v_unused_4069_; 
v_unused_4069_ = lean_ctor_get(v_a_3984_, 1);
lean_dec(v_unused_4069_);
v___x_3987_ = v_a_3984_;
v_isShared_3988_ = v_isSharedCheck_4068_;
goto v_resetjp_3986_;
}
else
{
lean_inc(v_fst_3985_);
lean_dec(v_a_3984_);
v___x_3987_ = lean_box(0);
v_isShared_3988_ = v_isSharedCheck_4068_;
goto v_resetjp_3986_;
}
v_resetjp_3986_:
{
lean_object* v___x_3989_; lean_object* v___x_3991_; 
v___x_3989_ = l_Array_toSubarray___redArg(v_toSortArgs_3929_, v___x_3969_, v___x_3965_);
if (v_isShared_3988_ == 0)
{
lean_ctor_set(v___x_3987_, 1, v___x_3989_);
v___x_3991_ = v___x_3987_;
goto v_reusejp_3990_;
}
else
{
lean_object* v_reuseFailAlloc_4067_; 
v_reuseFailAlloc_4067_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4067_, 0, v_fst_3985_);
lean_ctor_set(v_reuseFailAlloc_4067_, 1, v___x_3989_);
v___x_3991_ = v_reuseFailAlloc_4067_;
goto v_reusejp_3990_;
}
v_reusejp_3990_:
{
size_t v_sz_3992_; lean_object* v___x_3993_; 
v_sz_3992_ = lean_array_size(v_toSortDecls_3928_);
v___x_3993_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__2___redArg(v_toSortDecls_3928_, v_sz_3992_, v___x_3982_, v___x_3991_);
if (lean_obj_tag(v___x_3993_) == 0)
{
lean_object* v_a_3994_; lean_object* v_fst_3995_; lean_object* v_size_3996_; lean_object* v___x_3997_; lean_object* v___x_3998_; lean_object* v___x_3999_; lean_object* v___x_4000_; lean_object* v___x_4001_; 
v_a_3994_ = lean_ctor_get(v___x_3993_, 0);
lean_inc(v_a_3994_);
lean_dec_ref(v___x_3993_);
v_fst_3995_ = lean_ctor_get(v_a_3994_, 0);
lean_inc_n(v_fst_3995_, 2);
lean_dec(v_a_3994_);
v_size_3996_ = lean_ctor_get(v_fst_3995_, 0);
v___x_3997_ = l_Lean_instEmptyCollectionFVarIdHashSet;
v___x_3998_ = lean_mk_empty_array_with_capacity(v_size_3996_);
lean_inc_ref(v___x_3998_);
v___x_3999_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3999_, 0, v___x_3997_);
lean_ctor_set(v___x_3999_, 1, v___x_3997_);
lean_ctor_set(v___x_3999_, 2, v___x_3998_);
lean_ctor_set(v___x_3999_, 3, v___x_3998_);
v___x_4000_ = lean_box(0);
v___x_4001_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__3(v_fst_3995_, v_sortedDecls_3926_, v_sz_3981_, v___x_3982_, v___x_4000_, v___x_3999_, v___y_3976_, v___y_3977_);
lean_dec_ref(v_sortedDecls_3926_);
if (lean_obj_tag(v___x_4001_) == 0)
{
lean_object* v_a_4002_; lean_object* v_snd_4003_; lean_object* v___x_4004_; 
v_a_4002_ = lean_ctor_get(v___x_4001_, 0);
lean_inc(v_a_4002_);
lean_dec_ref(v___x_4001_);
v_snd_4003_ = lean_ctor_get(v_a_4002_, 1);
lean_inc(v_snd_4003_);
lean_dec(v_a_4002_);
v___x_4004_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__3(v_fst_3995_, v_toSortDecls_3928_, v_sz_3992_, v___x_3982_, v___x_4000_, v_snd_4003_, v___y_3976_, v___y_3977_);
if (lean_obj_tag(v___x_4004_) == 0)
{
lean_object* v_a_4005_; lean_object* v_snd_4006_; lean_object* v___x_4008_; uint8_t v_isShared_4009_; uint8_t v_isSharedCheck_4041_; 
v_a_4005_ = lean_ctor_get(v___x_4004_, 0);
lean_inc(v_a_4005_);
lean_dec_ref(v___x_4004_);
v_snd_4006_ = lean_ctor_get(v_a_4005_, 1);
v_isSharedCheck_4041_ = !lean_is_exclusive(v_a_4005_);
if (v_isSharedCheck_4041_ == 0)
{
lean_object* v_unused_4042_; 
v_unused_4042_ = lean_ctor_get(v_a_4005_, 0);
lean_dec(v_unused_4042_);
v___x_4008_ = v_a_4005_;
v_isShared_4009_ = v_isSharedCheck_4041_;
goto v_resetjp_4007_;
}
else
{
lean_inc(v_snd_4006_);
lean_dec(v_a_4005_);
v___x_4008_ = lean_box(0);
v_isShared_4009_ = v_isSharedCheck_4041_;
goto v_resetjp_4007_;
}
v_resetjp_4007_:
{
lean_object* v_options_4010_; lean_object* v_newDecls_4011_; lean_object* v_newArgs_4012_; lean_object* v_inheritedTraceOptions_4013_; uint8_t v_hasTrace_4014_; lean_object* v___f_4015_; 
v_options_4010_ = lean_ctor_get(v___y_3976_, 2);
v_newDecls_4011_ = lean_ctor_get(v_snd_4006_, 2);
v_newArgs_4012_ = lean_ctor_get(v_snd_4006_, 3);
v_inheritedTraceOptions_4013_ = lean_ctor_get(v___y_3976_, 13);
v_hasTrace_4014_ = lean_ctor_get_uint8(v_options_4010_, sizeof(void*)*1);
lean_inc_ref(v_newArgs_4012_);
lean_inc_ref(v_newDecls_4011_);
v___f_4015_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___lam__0___boxed), 7, 2);
lean_closure_set(v___f_4015_, 0, v_newDecls_4011_);
lean_closure_set(v___f_4015_, 1, v_newArgs_4012_);
if (v_hasTrace_4014_ == 0)
{
lean_del_object(v___x_4008_);
v___y_3953_ = v___y_3976_;
v___y_3954_ = v___x_4000_;
v___y_3955_ = v___y_3977_;
v___y_3956_ = v___f_4015_;
v_snd_3957_ = v_snd_4006_;
goto v___jp_3952_;
}
else
{
lean_object* v___x_4016_; uint8_t v___x_4017_; 
v___x_4016_ = lean_obj_once(&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__13, &l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__13_once, _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__13);
v___x_4017_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4013_, v_options_4010_, v___x_4016_);
if (v___x_4017_ == 0)
{
lean_del_object(v___x_4008_);
v___y_3953_ = v___y_3976_;
v___y_3954_ = v___x_4000_;
v___y_3955_ = v___y_3977_;
v___y_3956_ = v___f_4015_;
v_snd_3957_ = v_snd_4006_;
goto v___jp_3952_;
}
else
{
lean_object* v___x_4018_; size_t v_sz_4019_; lean_object* v___x_4020_; lean_object* v___x_4021_; lean_object* v___x_4022_; lean_object* v___x_4023_; lean_object* v___x_4024_; lean_object* v___x_4026_; 
lean_inc_ref(v_newArgs_4012_);
lean_inc_ref_n(v_newDecls_4011_, 2);
lean_dec_ref(v___f_4015_);
v___x_4018_ = lean_obj_once(&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__8, &l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__8_once, _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__8);
v_sz_4019_ = lean_array_size(v_newDecls_4011_);
v___x_4020_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__4(v_sz_4019_, v___x_3982_, v_newDecls_4011_);
v___x_4021_ = lean_array_to_list(v___x_4020_);
v___x_4022_ = lean_box(0);
v___x_4023_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__5(v___x_4021_, v___x_4022_);
v___x_4024_ = l_Lean_MessageData_ofList(v___x_4023_);
if (v_isShared_4009_ == 0)
{
lean_ctor_set_tag(v___x_4008_, 7);
lean_ctor_set(v___x_4008_, 1, v___x_4024_);
lean_ctor_set(v___x_4008_, 0, v___x_4018_);
v___x_4026_ = v___x_4008_;
goto v_reusejp_4025_;
}
else
{
lean_object* v_reuseFailAlloc_4040_; 
v_reuseFailAlloc_4040_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4040_, 0, v___x_4018_);
lean_ctor_set(v_reuseFailAlloc_4040_, 1, v___x_4024_);
v___x_4026_ = v_reuseFailAlloc_4040_;
goto v_reusejp_4025_;
}
v_reusejp_4025_:
{
lean_object* v___x_4027_; 
v___x_4027_ = l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6(v_cls_3974_, v___x_4026_, v_snd_4006_, v___y_3976_, v___y_3977_);
if (lean_obj_tag(v___x_4027_) == 0)
{
lean_object* v_a_4028_; lean_object* v_fst_4029_; lean_object* v_snd_4030_; lean_object* v___x_4031_; 
v_a_4028_ = lean_ctor_get(v___x_4027_, 0);
lean_inc(v_a_4028_);
lean_dec_ref(v___x_4027_);
v_fst_4029_ = lean_ctor_get(v_a_4028_, 0);
lean_inc(v_fst_4029_);
v_snd_4030_ = lean_ctor_get(v_a_4028_, 1);
lean_inc(v_snd_4030_);
lean_dec(v_a_4028_);
v___x_4031_ = l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___lam__0(v_newDecls_4011_, v_newArgs_4012_, v_fst_4029_, v_snd_4030_, v___y_3976_, v___y_3977_);
v___y_3934_ = v___x_4031_;
goto v___jp_3933_;
}
else
{
lean_object* v_a_4032_; lean_object* v___x_4034_; uint8_t v_isShared_4035_; uint8_t v_isSharedCheck_4039_; 
lean_dec_ref(v_newArgs_4012_);
lean_dec_ref(v_newDecls_4011_);
v_a_4032_ = lean_ctor_get(v___x_4027_, 0);
v_isSharedCheck_4039_ = !lean_is_exclusive(v___x_4027_);
if (v_isSharedCheck_4039_ == 0)
{
v___x_4034_ = v___x_4027_;
v_isShared_4035_ = v_isSharedCheck_4039_;
goto v_resetjp_4033_;
}
else
{
lean_inc(v_a_4032_);
lean_dec(v___x_4027_);
v___x_4034_ = lean_box(0);
v_isShared_4035_ = v_isSharedCheck_4039_;
goto v_resetjp_4033_;
}
v_resetjp_4033_:
{
lean_object* v___x_4037_; 
if (v_isShared_4035_ == 0)
{
v___x_4037_ = v___x_4034_;
goto v_reusejp_4036_;
}
else
{
lean_object* v_reuseFailAlloc_4038_; 
v_reuseFailAlloc_4038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4038_, 0, v_a_4032_);
v___x_4037_ = v_reuseFailAlloc_4038_;
goto v_reusejp_4036_;
}
v_reusejp_4036_:
{
return v___x_4037_;
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
lean_object* v_a_4043_; lean_object* v___x_4045_; uint8_t v_isShared_4046_; uint8_t v_isSharedCheck_4050_; 
v_a_4043_ = lean_ctor_get(v___x_4004_, 0);
v_isSharedCheck_4050_ = !lean_is_exclusive(v___x_4004_);
if (v_isSharedCheck_4050_ == 0)
{
v___x_4045_ = v___x_4004_;
v_isShared_4046_ = v_isSharedCheck_4050_;
goto v_resetjp_4044_;
}
else
{
lean_inc(v_a_4043_);
lean_dec(v___x_4004_);
v___x_4045_ = lean_box(0);
v_isShared_4046_ = v_isSharedCheck_4050_;
goto v_resetjp_4044_;
}
v_resetjp_4044_:
{
lean_object* v___x_4048_; 
if (v_isShared_4046_ == 0)
{
v___x_4048_ = v___x_4045_;
goto v_reusejp_4047_;
}
else
{
lean_object* v_reuseFailAlloc_4049_; 
v_reuseFailAlloc_4049_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4049_, 0, v_a_4043_);
v___x_4048_ = v_reuseFailAlloc_4049_;
goto v_reusejp_4047_;
}
v_reusejp_4047_:
{
return v___x_4048_;
}
}
}
}
else
{
lean_object* v_a_4051_; lean_object* v___x_4053_; uint8_t v_isShared_4054_; uint8_t v_isSharedCheck_4058_; 
lean_dec(v_fst_3995_);
v_a_4051_ = lean_ctor_get(v___x_4001_, 0);
v_isSharedCheck_4058_ = !lean_is_exclusive(v___x_4001_);
if (v_isSharedCheck_4058_ == 0)
{
v___x_4053_ = v___x_4001_;
v_isShared_4054_ = v_isSharedCheck_4058_;
goto v_resetjp_4052_;
}
else
{
lean_inc(v_a_4051_);
lean_dec(v___x_4001_);
v___x_4053_ = lean_box(0);
v_isShared_4054_ = v_isSharedCheck_4058_;
goto v_resetjp_4052_;
}
v_resetjp_4052_:
{
lean_object* v___x_4056_; 
if (v_isShared_4054_ == 0)
{
v___x_4056_ = v___x_4053_;
goto v_reusejp_4055_;
}
else
{
lean_object* v_reuseFailAlloc_4057_; 
v_reuseFailAlloc_4057_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4057_, 0, v_a_4051_);
v___x_4056_ = v_reuseFailAlloc_4057_;
goto v_reusejp_4055_;
}
v_reusejp_4055_:
{
return v___x_4056_;
}
}
}
}
else
{
lean_object* v_a_4059_; lean_object* v___x_4061_; uint8_t v_isShared_4062_; uint8_t v_isSharedCheck_4066_; 
lean_dec_ref(v_sortedDecls_3926_);
v_a_4059_ = lean_ctor_get(v___x_3993_, 0);
v_isSharedCheck_4066_ = !lean_is_exclusive(v___x_3993_);
if (v_isSharedCheck_4066_ == 0)
{
v___x_4061_ = v___x_3993_;
v_isShared_4062_ = v_isSharedCheck_4066_;
goto v_resetjp_4060_;
}
else
{
lean_inc(v_a_4059_);
lean_dec(v___x_3993_);
v___x_4061_ = lean_box(0);
v_isShared_4062_ = v_isSharedCheck_4066_;
goto v_resetjp_4060_;
}
v_resetjp_4060_:
{
lean_object* v___x_4064_; 
if (v_isShared_4062_ == 0)
{
v___x_4064_ = v___x_4061_;
goto v_reusejp_4063_;
}
else
{
lean_object* v_reuseFailAlloc_4065_; 
v_reuseFailAlloc_4065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4065_, 0, v_a_4059_);
v___x_4064_ = v_reuseFailAlloc_4065_;
goto v_reusejp_4063_;
}
v_reusejp_4063_:
{
return v___x_4064_;
}
}
}
}
}
}
else
{
lean_object* v_a_4070_; lean_object* v___x_4072_; uint8_t v_isShared_4073_; uint8_t v_isSharedCheck_4077_; 
lean_dec_ref(v_toSortArgs_3929_);
lean_dec_ref(v_sortedDecls_3926_);
v_a_4070_ = lean_ctor_get(v___x_3983_, 0);
v_isSharedCheck_4077_ = !lean_is_exclusive(v___x_3983_);
if (v_isSharedCheck_4077_ == 0)
{
v___x_4072_ = v___x_3983_;
v_isShared_4073_ = v_isSharedCheck_4077_;
goto v_resetjp_4071_;
}
else
{
lean_inc(v_a_4070_);
lean_dec(v___x_3983_);
v___x_4072_ = lean_box(0);
v_isShared_4073_ = v_isSharedCheck_4077_;
goto v_resetjp_4071_;
}
v_resetjp_4071_:
{
lean_object* v___x_4075_; 
if (v_isShared_4073_ == 0)
{
v___x_4075_ = v___x_4072_;
goto v_reusejp_4074_;
}
else
{
lean_object* v_reuseFailAlloc_4076_; 
v_reuseFailAlloc_4076_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4076_, 0, v_a_4070_);
v___x_4075_ = v_reuseFailAlloc_4076_;
goto v_reusejp_4074_;
}
v_reusejp_4074_:
{
return v___x_4075_;
}
}
}
}
}
else
{
lean_object* v___x_4090_; lean_object* v___x_4091_; 
lean_dec_ref(v_toSortArgs_3929_);
v___x_4090_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4090_, 0, v_sortedDecls_3926_);
lean_ctor_set(v___x_4090_, 1, v_sortedArgs_3927_);
v___x_4091_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4091_, 0, v___x_4090_);
return v___x_4091_;
}
}
}
v___jp_3933_:
{
if (lean_obj_tag(v___y_3934_) == 0)
{
lean_object* v_a_3935_; lean_object* v___x_3937_; uint8_t v_isShared_3938_; uint8_t v_isSharedCheck_3943_; 
v_a_3935_ = lean_ctor_get(v___y_3934_, 0);
v_isSharedCheck_3943_ = !lean_is_exclusive(v___y_3934_);
if (v_isSharedCheck_3943_ == 0)
{
v___x_3937_ = v___y_3934_;
v_isShared_3938_ = v_isSharedCheck_3943_;
goto v_resetjp_3936_;
}
else
{
lean_inc(v_a_3935_);
lean_dec(v___y_3934_);
v___x_3937_ = lean_box(0);
v_isShared_3938_ = v_isSharedCheck_3943_;
goto v_resetjp_3936_;
}
v_resetjp_3936_:
{
lean_object* v_fst_3939_; lean_object* v___x_3941_; 
v_fst_3939_ = lean_ctor_get(v_a_3935_, 0);
lean_inc(v_fst_3939_);
lean_dec(v_a_3935_);
if (v_isShared_3938_ == 0)
{
lean_ctor_set(v___x_3937_, 0, v_fst_3939_);
v___x_3941_ = v___x_3937_;
goto v_reusejp_3940_;
}
else
{
lean_object* v_reuseFailAlloc_3942_; 
v_reuseFailAlloc_3942_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3942_, 0, v_fst_3939_);
v___x_3941_ = v_reuseFailAlloc_3942_;
goto v_reusejp_3940_;
}
v_reusejp_3940_:
{
return v___x_3941_;
}
}
}
else
{
lean_object* v_a_3944_; lean_object* v___x_3946_; uint8_t v_isShared_3947_; uint8_t v_isSharedCheck_3951_; 
v_a_3944_ = lean_ctor_get(v___y_3934_, 0);
v_isSharedCheck_3951_ = !lean_is_exclusive(v___y_3934_);
if (v_isSharedCheck_3951_ == 0)
{
v___x_3946_ = v___y_3934_;
v_isShared_3947_ = v_isSharedCheck_3951_;
goto v_resetjp_3945_;
}
else
{
lean_inc(v_a_3944_);
lean_dec(v___y_3934_);
v___x_3946_ = lean_box(0);
v_isShared_3947_ = v_isSharedCheck_3951_;
goto v_resetjp_3945_;
}
v_resetjp_3945_:
{
lean_object* v___x_3949_; 
if (v_isShared_3947_ == 0)
{
v___x_3949_ = v___x_3946_;
goto v_reusejp_3948_;
}
else
{
lean_object* v_reuseFailAlloc_3950_; 
v_reuseFailAlloc_3950_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3950_, 0, v_a_3944_);
v___x_3949_ = v_reuseFailAlloc_3950_;
goto v_reusejp_3948_;
}
v_reusejp_3948_:
{
return v___x_3949_;
}
}
}
}
v___jp_3952_:
{
lean_object* v___x_3958_; 
lean_inc(v___y_3955_);
lean_inc_ref(v___y_3953_);
v___x_3958_ = lean_apply_5(v___y_3956_, v___y_3954_, v_snd_3957_, v___y_3953_, v___y_3955_, lean_box(0));
v___y_3934_ = v___x_3958_;
goto v___jp_3933_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___boxed(lean_object* v_sortedDecls_4092_, lean_object* v_sortedArgs_4093_, lean_object* v_toSortDecls_4094_, lean_object* v_toSortArgs_4095_, lean_object* v_a_4096_, lean_object* v_a_4097_, lean_object* v_a_4098_){
_start:
{
lean_object* v_res_4099_; 
v_res_4099_ = l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls(v_sortedDecls_4092_, v_sortedArgs_4093_, v_toSortDecls_4094_, v_toSortArgs_4095_, v_a_4096_, v_a_4097_);
lean_dec(v_a_4097_);
lean_dec_ref(v_a_4096_);
lean_dec_ref(v_toSortDecls_4094_);
return v_res_4099_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__1(lean_object* v_00_u03b2_4100_, lean_object* v_m_4101_, lean_object* v_a_4102_, lean_object* v_b_4103_){
_start:
{
lean_object* v___x_4104_; 
v___x_4104_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__1___redArg(v_m_4101_, v_a_4102_, v_b_4103_);
return v___x_4104_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__2(lean_object* v_as_4105_, size_t v_sz_4106_, size_t v_i_4107_, lean_object* v_b_4108_, lean_object* v___y_4109_, lean_object* v___y_4110_){
_start:
{
lean_object* v___x_4112_; 
v___x_4112_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__2___redArg(v_as_4105_, v_sz_4106_, v_i_4107_, v_b_4108_);
return v___x_4112_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__2___boxed(lean_object* v_as_4113_, lean_object* v_sz_4114_, lean_object* v_i_4115_, lean_object* v_b_4116_, lean_object* v___y_4117_, lean_object* v___y_4118_, lean_object* v___y_4119_){
_start:
{
size_t v_sz_boxed_4120_; size_t v_i_boxed_4121_; lean_object* v_res_4122_; 
v_sz_boxed_4120_ = lean_unbox_usize(v_sz_4114_);
lean_dec(v_sz_4114_);
v_i_boxed_4121_ = lean_unbox_usize(v_i_4115_);
lean_dec(v_i_4115_);
v_res_4122_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__2(v_as_4113_, v_sz_boxed_4120_, v_i_boxed_4121_, v_b_4116_, v___y_4117_, v___y_4118_);
lean_dec(v___y_4118_);
lean_dec_ref(v___y_4117_);
lean_dec_ref(v_as_4113_);
return v_res_4122_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__1_spec__1(lean_object* v_00_u03b2_4123_, lean_object* v_a_4124_, lean_object* v_b_4125_, lean_object* v_x_4126_){
_start:
{
lean_object* v___x_4127_; 
v___x_4127_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__1_spec__1___redArg(v_a_4124_, v_b_4125_, v_x_4126_);
return v___x_4127_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Closure_mkValueTypeClosure_spec__0(lean_object* v_msg_4129_, lean_object* v___y_4130_, lean_object* v___y_4131_, lean_object* v___y_4132_, lean_object* v___y_4133_){
_start:
{
lean_object* v___f_4135_; lean_object* v___x_1329__overap_4136_; lean_object* v___x_4137_; 
v___f_4135_ = ((lean_object*)(l_panic___at___00Lean_Meta_Closure_mkValueTypeClosure_spec__0___closed__0));
v___x_1329__overap_4136_ = lean_panic_fn_borrowed(v___f_4135_, v_msg_4129_);
lean_inc(v___y_4133_);
lean_inc_ref(v___y_4132_);
lean_inc(v___y_4131_);
lean_inc_ref(v___y_4130_);
v___x_4137_ = lean_apply_5(v___x_1329__overap_4136_, v___y_4130_, v___y_4131_, v___y_4132_, v___y_4133_, lean_box(0));
return v___x_4137_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Closure_mkValueTypeClosure_spec__0___boxed(lean_object* v_msg_4138_, lean_object* v___y_4139_, lean_object* v___y_4140_, lean_object* v___y_4141_, lean_object* v___y_4142_, lean_object* v___y_4143_){
_start:
{
lean_object* v_res_4144_; 
v_res_4144_ = l_panic___at___00Lean_Meta_Closure_mkValueTypeClosure_spec__0(v_msg_4138_, v___y_4139_, v___y_4140_, v___y_4141_, v___y_4142_);
lean_dec(v___y_4142_);
lean_dec_ref(v___y_4141_);
lean_dec(v___y_4140_);
lean_dec_ref(v___y_4139_);
return v_res_4144_;
}
}
static lean_object* _init_l_Lean_Meta_Closure_mkValueTypeClosure___closed__0(void){
_start:
{
lean_object* v___x_4145_; lean_object* v___x_4146_; lean_object* v___x_4147_; 
v___x_4145_ = lean_box(0);
v___x_4146_ = lean_unsigned_to_nat(16u);
v___x_4147_ = lean_mk_array(v___x_4146_, v___x_4145_);
return v___x_4147_;
}
}
static lean_object* _init_l_Lean_Meta_Closure_mkValueTypeClosure___closed__1(void){
_start:
{
lean_object* v___x_4148_; lean_object* v___x_4149_; lean_object* v___x_4150_; 
v___x_4148_ = lean_obj_once(&l_Lean_Meta_Closure_mkValueTypeClosure___closed__0, &l_Lean_Meta_Closure_mkValueTypeClosure___closed__0_once, _init_l_Lean_Meta_Closure_mkValueTypeClosure___closed__0);
v___x_4149_ = lean_unsigned_to_nat(0u);
v___x_4150_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4150_, 0, v___x_4149_);
lean_ctor_set(v___x_4150_, 1, v___x_4148_);
return v___x_4150_;
}
}
static lean_object* _init_l_Lean_Meta_Closure_mkValueTypeClosure___closed__3(void){
_start:
{
lean_object* v___x_4153_; lean_object* v___x_4154_; lean_object* v___x_4155_; lean_object* v___x_4156_; 
v___x_4153_ = lean_unsigned_to_nat(1u);
v___x_4154_ = ((lean_object*)(l_Lean_Meta_Closure_mkValueTypeClosure___closed__2));
v___x_4155_ = lean_obj_once(&l_Lean_Meta_Closure_mkValueTypeClosure___closed__1, &l_Lean_Meta_Closure_mkValueTypeClosure___closed__1_once, _init_l_Lean_Meta_Closure_mkValueTypeClosure___closed__1);
v___x_4156_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_4156_, 0, v___x_4155_);
lean_ctor_set(v___x_4156_, 1, v___x_4155_);
lean_ctor_set(v___x_4156_, 2, v___x_4154_);
lean_ctor_set(v___x_4156_, 3, v___x_4153_);
lean_ctor_set(v___x_4156_, 4, v___x_4154_);
lean_ctor_set(v___x_4156_, 5, v___x_4154_);
lean_ctor_set(v___x_4156_, 6, v___x_4154_);
lean_ctor_set(v___x_4156_, 7, v___x_4154_);
lean_ctor_set(v___x_4156_, 8, v___x_4153_);
lean_ctor_set(v___x_4156_, 9, v___x_4154_);
lean_ctor_set(v___x_4156_, 10, v___x_4154_);
lean_ctor_set(v___x_4156_, 11, v___x_4154_);
return v___x_4156_;
}
}
static lean_object* _init_l_Lean_Meta_Closure_mkValueTypeClosure___closed__6(void){
_start:
{
lean_object* v___x_4159_; lean_object* v___x_4160_; lean_object* v___x_4161_; lean_object* v___x_4162_; lean_object* v___x_4163_; lean_object* v___x_4164_; 
v___x_4159_ = ((lean_object*)(l_Lean_Meta_Closure_mkValueTypeClosure___closed__5));
v___x_4160_ = lean_unsigned_to_nat(2u);
v___x_4161_ = lean_unsigned_to_nat(417u);
v___x_4162_ = ((lean_object*)(l_Lean_Meta_Closure_mkValueTypeClosure___closed__4));
v___x_4163_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__2));
v___x_4164_ = l_mkPanicMessageWithDecl(v___x_4163_, v___x_4162_, v___x_4161_, v___x_4160_, v___x_4159_);
return v___x_4164_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkValueTypeClosure(lean_object* v_type_4165_, lean_object* v_value_4166_, uint8_t v_zetaDelta_4167_, lean_object* v_a_4168_, lean_object* v_a_4169_, lean_object* v_a_4170_, lean_object* v_a_4171_){
_start:
{
lean_object* v___x_4173_; lean_object* v___x_4174_; lean_object* v___x_4175_; 
v___x_4173_ = lean_obj_once(&l_Lean_Meta_Closure_mkValueTypeClosure___closed__3, &l_Lean_Meta_Closure_mkValueTypeClosure___closed__3_once, _init_l_Lean_Meta_Closure_mkValueTypeClosure___closed__3);
v___x_4174_ = lean_st_mk_ref(v___x_4173_);
v___x_4175_ = l_Lean_Meta_Closure_mkValueTypeClosureAux(v_type_4165_, v_value_4166_, v_zetaDelta_4167_, v___x_4174_, v_a_4168_, v_a_4169_, v_a_4170_, v_a_4171_);
if (lean_obj_tag(v___x_4175_) == 0)
{
lean_object* v_a_4176_; lean_object* v___x_4177_; lean_object* v_fst_4178_; lean_object* v_snd_4179_; lean_object* v_levelParams_4180_; lean_object* v_levelArgs_4181_; lean_object* v_newLocalDecls_4182_; lean_object* v_newLocalDeclsForMVars_4183_; lean_object* v_newLetDecls_4184_; lean_object* v_exprMVarArgs_4185_; lean_object* v_exprFVarArgs_4186_; lean_object* v___x_4187_; lean_object* v___x_4188_; lean_object* v___x_4189_; 
v_a_4176_ = lean_ctor_get(v___x_4175_, 0);
lean_inc(v_a_4176_);
lean_dec_ref(v___x_4175_);
v___x_4177_ = lean_st_ref_get(v___x_4174_);
lean_dec(v___x_4174_);
v_fst_4178_ = lean_ctor_get(v_a_4176_, 0);
lean_inc(v_fst_4178_);
v_snd_4179_ = lean_ctor_get(v_a_4176_, 1);
lean_inc(v_snd_4179_);
lean_dec(v_a_4176_);
v_levelParams_4180_ = lean_ctor_get(v___x_4177_, 2);
lean_inc_ref(v_levelParams_4180_);
v_levelArgs_4181_ = lean_ctor_get(v___x_4177_, 4);
lean_inc_ref(v_levelArgs_4181_);
v_newLocalDecls_4182_ = lean_ctor_get(v___x_4177_, 5);
lean_inc_ref(v_newLocalDecls_4182_);
v_newLocalDeclsForMVars_4183_ = lean_ctor_get(v___x_4177_, 6);
lean_inc_ref(v_newLocalDeclsForMVars_4183_);
v_newLetDecls_4184_ = lean_ctor_get(v___x_4177_, 7);
lean_inc_ref(v_newLetDecls_4184_);
v_exprMVarArgs_4185_ = lean_ctor_get(v___x_4177_, 9);
lean_inc_ref(v_exprMVarArgs_4185_);
v_exprFVarArgs_4186_ = lean_ctor_get(v___x_4177_, 10);
lean_inc_ref(v_exprFVarArgs_4186_);
lean_dec(v___x_4177_);
v___x_4187_ = l_Array_reverse___redArg(v_newLocalDecls_4182_);
v___x_4188_ = l_Array_reverse___redArg(v_exprFVarArgs_4186_);
v___x_4189_ = l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls(v___x_4187_, v___x_4188_, v_newLocalDeclsForMVars_4183_, v_exprMVarArgs_4185_, v_a_4170_, v_a_4171_);
lean_dec_ref(v_newLocalDeclsForMVars_4183_);
if (lean_obj_tag(v___x_4189_) == 0)
{
lean_object* v_a_4190_; lean_object* v___x_4192_; uint8_t v_isShared_4193_; uint8_t v_isSharedCheck_4208_; 
v_a_4190_ = lean_ctor_get(v___x_4189_, 0);
v_isSharedCheck_4208_ = !lean_is_exclusive(v___x_4189_);
if (v_isSharedCheck_4208_ == 0)
{
v___x_4192_ = v___x_4189_;
v_isShared_4193_ = v_isSharedCheck_4208_;
goto v_resetjp_4191_;
}
else
{
lean_inc(v_a_4190_);
lean_dec(v___x_4189_);
v___x_4192_ = lean_box(0);
v_isShared_4193_ = v_isSharedCheck_4208_;
goto v_resetjp_4191_;
}
v_resetjp_4191_:
{
lean_object* v_fst_4194_; lean_object* v_snd_4195_; lean_object* v___x_4196_; lean_object* v___x_4197_; lean_object* v___x_4198_; lean_object* v___x_4199_; lean_object* v___x_4200_; uint8_t v___x_4201_; 
v_fst_4194_ = lean_ctor_get(v_a_4190_, 0);
lean_inc_n(v_fst_4194_, 2);
v_snd_4195_ = lean_ctor_get(v_a_4190_, 1);
lean_inc(v_snd_4195_);
lean_dec(v_a_4190_);
v___x_4196_ = l_Array_reverse___redArg(v_newLetDecls_4184_);
lean_inc_ref(v___x_4196_);
v___x_4197_ = l_Lean_Meta_Closure_mkForall(v___x_4196_, v_fst_4178_);
lean_dec(v_fst_4178_);
v___x_4198_ = l_Lean_Meta_Closure_mkForall(v_fst_4194_, v___x_4197_);
lean_dec_ref(v___x_4197_);
v___x_4199_ = l_Lean_Meta_Closure_mkLambda(v___x_4196_, v_snd_4179_);
lean_dec(v_snd_4179_);
v___x_4200_ = l_Lean_Meta_Closure_mkLambda(v_fst_4194_, v___x_4199_);
lean_dec_ref(v___x_4199_);
v___x_4201_ = l_Lean_Expr_hasFVar(v___x_4200_);
if (v___x_4201_ == 0)
{
lean_object* v___x_4202_; lean_object* v___x_4204_; 
v___x_4202_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4202_, 0, v_levelParams_4180_);
lean_ctor_set(v___x_4202_, 1, v___x_4198_);
lean_ctor_set(v___x_4202_, 2, v___x_4200_);
lean_ctor_set(v___x_4202_, 3, v_levelArgs_4181_);
lean_ctor_set(v___x_4202_, 4, v_snd_4195_);
if (v_isShared_4193_ == 0)
{
lean_ctor_set(v___x_4192_, 0, v___x_4202_);
v___x_4204_ = v___x_4192_;
goto v_reusejp_4203_;
}
else
{
lean_object* v_reuseFailAlloc_4205_; 
v_reuseFailAlloc_4205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4205_, 0, v___x_4202_);
v___x_4204_ = v_reuseFailAlloc_4205_;
goto v_reusejp_4203_;
}
v_reusejp_4203_:
{
return v___x_4204_;
}
}
else
{
lean_object* v___x_4206_; lean_object* v___x_4207_; 
lean_dec_ref(v___x_4200_);
lean_dec_ref(v___x_4198_);
lean_dec(v_snd_4195_);
lean_del_object(v___x_4192_);
lean_dec_ref(v_levelArgs_4181_);
lean_dec_ref(v_levelParams_4180_);
v___x_4206_ = lean_obj_once(&l_Lean_Meta_Closure_mkValueTypeClosure___closed__6, &l_Lean_Meta_Closure_mkValueTypeClosure___closed__6_once, _init_l_Lean_Meta_Closure_mkValueTypeClosure___closed__6);
v___x_4207_ = l_panic___at___00Lean_Meta_Closure_mkValueTypeClosure_spec__0(v___x_4206_, v_a_4168_, v_a_4169_, v_a_4170_, v_a_4171_);
return v___x_4207_;
}
}
}
else
{
lean_object* v_a_4209_; lean_object* v___x_4211_; uint8_t v_isShared_4212_; uint8_t v_isSharedCheck_4216_; 
lean_dec_ref(v_newLetDecls_4184_);
lean_dec_ref(v_levelArgs_4181_);
lean_dec_ref(v_levelParams_4180_);
lean_dec(v_snd_4179_);
lean_dec(v_fst_4178_);
v_a_4209_ = lean_ctor_get(v___x_4189_, 0);
v_isSharedCheck_4216_ = !lean_is_exclusive(v___x_4189_);
if (v_isSharedCheck_4216_ == 0)
{
v___x_4211_ = v___x_4189_;
v_isShared_4212_ = v_isSharedCheck_4216_;
goto v_resetjp_4210_;
}
else
{
lean_inc(v_a_4209_);
lean_dec(v___x_4189_);
v___x_4211_ = lean_box(0);
v_isShared_4212_ = v_isSharedCheck_4216_;
goto v_resetjp_4210_;
}
v_resetjp_4210_:
{
lean_object* v___x_4214_; 
if (v_isShared_4212_ == 0)
{
v___x_4214_ = v___x_4211_;
goto v_reusejp_4213_;
}
else
{
lean_object* v_reuseFailAlloc_4215_; 
v_reuseFailAlloc_4215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4215_, 0, v_a_4209_);
v___x_4214_ = v_reuseFailAlloc_4215_;
goto v_reusejp_4213_;
}
v_reusejp_4213_:
{
return v___x_4214_;
}
}
}
}
else
{
lean_object* v_a_4217_; lean_object* v___x_4219_; uint8_t v_isShared_4220_; uint8_t v_isSharedCheck_4224_; 
lean_dec(v___x_4174_);
v_a_4217_ = lean_ctor_get(v___x_4175_, 0);
v_isSharedCheck_4224_ = !lean_is_exclusive(v___x_4175_);
if (v_isSharedCheck_4224_ == 0)
{
v___x_4219_ = v___x_4175_;
v_isShared_4220_ = v_isSharedCheck_4224_;
goto v_resetjp_4218_;
}
else
{
lean_inc(v_a_4217_);
lean_dec(v___x_4175_);
v___x_4219_ = lean_box(0);
v_isShared_4220_ = v_isSharedCheck_4224_;
goto v_resetjp_4218_;
}
v_resetjp_4218_:
{
lean_object* v___x_4222_; 
if (v_isShared_4220_ == 0)
{
v___x_4222_ = v___x_4219_;
goto v_reusejp_4221_;
}
else
{
lean_object* v_reuseFailAlloc_4223_; 
v_reuseFailAlloc_4223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4223_, 0, v_a_4217_);
v___x_4222_ = v_reuseFailAlloc_4223_;
goto v_reusejp_4221_;
}
v_reusejp_4221_:
{
return v___x_4222_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkValueTypeClosure___boxed(lean_object* v_type_4225_, lean_object* v_value_4226_, lean_object* v_zetaDelta_4227_, lean_object* v_a_4228_, lean_object* v_a_4229_, lean_object* v_a_4230_, lean_object* v_a_4231_, lean_object* v_a_4232_){
_start:
{
uint8_t v_zetaDelta_boxed_4233_; lean_object* v_res_4234_; 
v_zetaDelta_boxed_4233_ = lean_unbox(v_zetaDelta_4227_);
v_res_4234_ = l_Lean_Meta_Closure_mkValueTypeClosure(v_type_4225_, v_value_4226_, v_zetaDelta_boxed_4233_, v_a_4228_, v_a_4229_, v_a_4230_, v_a_4231_);
lean_dec(v_a_4231_);
lean_dec_ref(v_a_4230_);
lean_dec(v_a_4229_);
lean_dec_ref(v_a_4228_);
return v_res_4234_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkAuxDefinition_spec__0___redArg(lean_object* v_name_4235_, lean_object* v_levelParams_4236_, lean_object* v_type_4237_, lean_object* v_value_4238_, lean_object* v_hints_4239_, lean_object* v___y_4240_){
_start:
{
lean_object* v___x_4242_; uint8_t v___y_4244_; uint8_t v___y_4251_; lean_object* v_env_4254_; uint8_t v___x_4255_; 
v___x_4242_ = lean_st_ref_get(v___y_4240_);
v_env_4254_ = lean_ctor_get(v___x_4242_, 0);
lean_inc_ref_n(v_env_4254_, 2);
lean_dec(v___x_4242_);
v___x_4255_ = l_Lean_Environment_hasUnsafe(v_env_4254_, v_type_4237_);
if (v___x_4255_ == 0)
{
uint8_t v___x_4256_; 
v___x_4256_ = l_Lean_Environment_hasUnsafe(v_env_4254_, v_value_4238_);
v___y_4251_ = v___x_4256_;
goto v___jp_4250_;
}
else
{
lean_dec_ref(v_env_4254_);
v___y_4251_ = v___x_4255_;
goto v___jp_4250_;
}
v___jp_4243_:
{
lean_object* v___x_4245_; lean_object* v___x_4246_; lean_object* v___x_4247_; lean_object* v___x_4248_; lean_object* v___x_4249_; 
lean_inc(v_name_4235_);
v___x_4245_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4245_, 0, v_name_4235_);
lean_ctor_set(v___x_4245_, 1, v_levelParams_4236_);
lean_ctor_set(v___x_4245_, 2, v_type_4237_);
v___x_4246_ = lean_box(0);
v___x_4247_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4247_, 0, v_name_4235_);
lean_ctor_set(v___x_4247_, 1, v___x_4246_);
v___x_4248_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_4248_, 0, v___x_4245_);
lean_ctor_set(v___x_4248_, 1, v_value_4238_);
lean_ctor_set(v___x_4248_, 2, v_hints_4239_);
lean_ctor_set(v___x_4248_, 3, v___x_4247_);
lean_ctor_set_uint8(v___x_4248_, sizeof(void*)*4, v___y_4244_);
v___x_4249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4249_, 0, v___x_4248_);
return v___x_4249_;
}
v___jp_4250_:
{
if (v___y_4251_ == 0)
{
uint8_t v___x_4252_; 
v___x_4252_ = 1;
v___y_4244_ = v___x_4252_;
goto v___jp_4243_;
}
else
{
uint8_t v___x_4253_; 
v___x_4253_ = 0;
v___y_4244_ = v___x_4253_;
goto v___jp_4243_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkAuxDefinition_spec__0___redArg___boxed(lean_object* v_name_4257_, lean_object* v_levelParams_4258_, lean_object* v_type_4259_, lean_object* v_value_4260_, lean_object* v_hints_4261_, lean_object* v___y_4262_, lean_object* v___y_4263_){
_start:
{
lean_object* v_res_4264_; 
v_res_4264_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkAuxDefinition_spec__0___redArg(v_name_4257_, v_levelParams_4258_, v_type_4259_, v_value_4260_, v_hints_4261_, v___y_4262_);
lean_dec(v___y_4262_);
return v_res_4264_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkAuxDefinition_spec__0(lean_object* v_name_4265_, lean_object* v_levelParams_4266_, lean_object* v_type_4267_, lean_object* v_value_4268_, lean_object* v_hints_4269_, lean_object* v___y_4270_, lean_object* v___y_4271_, lean_object* v___y_4272_, lean_object* v___y_4273_){
_start:
{
lean_object* v___x_4275_; 
v___x_4275_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkAuxDefinition_spec__0___redArg(v_name_4265_, v_levelParams_4266_, v_type_4267_, v_value_4268_, v_hints_4269_, v___y_4273_);
return v___x_4275_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkAuxDefinition_spec__0___boxed(lean_object* v_name_4276_, lean_object* v_levelParams_4277_, lean_object* v_type_4278_, lean_object* v_value_4279_, lean_object* v_hints_4280_, lean_object* v___y_4281_, lean_object* v___y_4282_, lean_object* v___y_4283_, lean_object* v___y_4284_, lean_object* v___y_4285_){
_start:
{
lean_object* v_res_4286_; 
v_res_4286_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkAuxDefinition_spec__0(v_name_4276_, v_levelParams_4277_, v_type_4278_, v_value_4279_, v_hints_4280_, v___y_4281_, v___y_4282_, v___y_4283_, v___y_4284_);
lean_dec(v___y_4284_);
lean_dec_ref(v___y_4283_);
lean_dec(v___y_4282_);
lean_dec_ref(v___y_4281_);
return v_res_4286_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAuxDefinition(lean_object* v_name_4287_, lean_object* v_type_4288_, lean_object* v_value_4289_, uint8_t v_zetaDelta_4290_, uint8_t v_compile_4291_, uint8_t v_logCompileErrors_4292_, lean_object* v_a_4293_, lean_object* v_a_4294_, lean_object* v_a_4295_, lean_object* v_a_4296_){
_start:
{
lean_object* v___x_4298_; 
v___x_4298_ = l_Lean_Meta_Closure_mkValueTypeClosure(v_type_4288_, v_value_4289_, v_zetaDelta_4290_, v_a_4293_, v_a_4294_, v_a_4295_, v_a_4296_);
if (lean_obj_tag(v___x_4298_) == 0)
{
lean_object* v_a_4299_; lean_object* v___x_4301_; uint8_t v_isShared_4302_; uint8_t v_isSharedCheck_4350_; 
v_a_4299_ = lean_ctor_get(v___x_4298_, 0);
v_isSharedCheck_4350_ = !lean_is_exclusive(v___x_4298_);
if (v_isSharedCheck_4350_ == 0)
{
v___x_4301_ = v___x_4298_;
v_isShared_4302_ = v_isSharedCheck_4350_;
goto v_resetjp_4300_;
}
else
{
lean_inc(v_a_4299_);
lean_dec(v___x_4298_);
v___x_4301_ = lean_box(0);
v_isShared_4302_ = v_isSharedCheck_4350_;
goto v_resetjp_4300_;
}
v_resetjp_4300_:
{
lean_object* v___x_4303_; lean_object* v_env_4304_; lean_object* v_levelParams_4305_; lean_object* v_type_4306_; lean_object* v_value_4307_; lean_object* v_levelArgs_4308_; lean_object* v_exprArgs_4309_; uint32_t v___x_4317_; uint32_t v___x_4318_; uint32_t v___x_4319_; lean_object* v___x_4320_; lean_object* v___x_4321_; lean_object* v___x_4322_; lean_object* v_a_4323_; lean_object* v___x_4325_; uint8_t v_isShared_4326_; uint8_t v_isSharedCheck_4349_; 
v___x_4303_ = lean_st_ref_get(v_a_4296_);
v_env_4304_ = lean_ctor_get(v___x_4303_, 0);
lean_inc_ref(v_env_4304_);
lean_dec(v___x_4303_);
v_levelParams_4305_ = lean_ctor_get(v_a_4299_, 0);
lean_inc_ref(v_levelParams_4305_);
v_type_4306_ = lean_ctor_get(v_a_4299_, 1);
lean_inc_ref(v_type_4306_);
v_value_4307_ = lean_ctor_get(v_a_4299_, 2);
lean_inc_ref_n(v_value_4307_, 2);
v_levelArgs_4308_ = lean_ctor_get(v_a_4299_, 3);
lean_inc_ref(v_levelArgs_4308_);
v_exprArgs_4309_ = lean_ctor_get(v_a_4299_, 4);
lean_inc_ref(v_exprArgs_4309_);
lean_dec(v_a_4299_);
v___x_4317_ = l_Lean_getMaxHeight(v_env_4304_, v_value_4307_);
v___x_4318_ = 1;
v___x_4319_ = lean_uint32_add(v___x_4317_, v___x_4318_);
v___x_4320_ = lean_alloc_ctor(2, 0, 4);
lean_ctor_set_uint32(v___x_4320_, 0, v___x_4319_);
v___x_4321_ = lean_array_to_list(v_levelParams_4305_);
lean_inc(v_name_4287_);
v___x_4322_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkAuxDefinition_spec__0___redArg(v_name_4287_, v___x_4321_, v_type_4306_, v_value_4307_, v___x_4320_, v_a_4296_);
v_a_4323_ = lean_ctor_get(v___x_4322_, 0);
v_isSharedCheck_4349_ = !lean_is_exclusive(v___x_4322_);
if (v_isSharedCheck_4349_ == 0)
{
v___x_4325_ = v___x_4322_;
v_isShared_4326_ = v_isSharedCheck_4349_;
goto v_resetjp_4324_;
}
else
{
lean_inc(v_a_4323_);
lean_dec(v___x_4322_);
v___x_4325_ = lean_box(0);
v_isShared_4326_ = v_isSharedCheck_4349_;
goto v_resetjp_4324_;
}
v___jp_4310_:
{
lean_object* v___x_4311_; lean_object* v___x_4312_; lean_object* v___x_4313_; lean_object* v___x_4315_; 
v___x_4311_ = lean_array_to_list(v_levelArgs_4308_);
v___x_4312_ = l_Lean_mkConst(v_name_4287_, v___x_4311_);
v___x_4313_ = l_Lean_mkAppN(v___x_4312_, v_exprArgs_4309_);
lean_dec_ref(v_exprArgs_4309_);
if (v_isShared_4302_ == 0)
{
lean_ctor_set(v___x_4301_, 0, v___x_4313_);
v___x_4315_ = v___x_4301_;
goto v_reusejp_4314_;
}
else
{
lean_object* v_reuseFailAlloc_4316_; 
v_reuseFailAlloc_4316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4316_, 0, v___x_4313_);
v___x_4315_ = v_reuseFailAlloc_4316_;
goto v_reusejp_4314_;
}
v_reusejp_4314_:
{
return v___x_4315_;
}
}
v_resetjp_4324_:
{
lean_object* v___x_4328_; 
if (v_isShared_4326_ == 0)
{
lean_ctor_set_tag(v___x_4325_, 1);
v___x_4328_ = v___x_4325_;
goto v_reusejp_4327_;
}
else
{
lean_object* v_reuseFailAlloc_4348_; 
v_reuseFailAlloc_4348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4348_, 0, v_a_4323_);
v___x_4328_ = v_reuseFailAlloc_4348_;
goto v_reusejp_4327_;
}
v_reusejp_4327_:
{
uint8_t v___x_4329_; lean_object* v___x_4330_; 
v___x_4329_ = 0;
lean_inc_ref(v___x_4328_);
v___x_4330_ = l_Lean_addDecl(v___x_4328_, v___x_4329_, v_a_4295_, v_a_4296_);
if (lean_obj_tag(v___x_4330_) == 0)
{
lean_dec_ref(v___x_4330_);
if (v_compile_4291_ == 0)
{
lean_dec_ref(v___x_4328_);
goto v___jp_4310_;
}
else
{
lean_object* v___x_4331_; 
v___x_4331_ = l_Lean_compileDecl(v___x_4328_, v_logCompileErrors_4292_, v_a_4295_, v_a_4296_);
if (lean_obj_tag(v___x_4331_) == 0)
{
lean_dec_ref(v___x_4331_);
goto v___jp_4310_;
}
else
{
lean_object* v_a_4332_; lean_object* v___x_4334_; uint8_t v_isShared_4335_; uint8_t v_isSharedCheck_4339_; 
lean_dec_ref(v_exprArgs_4309_);
lean_dec_ref(v_levelArgs_4308_);
lean_del_object(v___x_4301_);
lean_dec(v_name_4287_);
v_a_4332_ = lean_ctor_get(v___x_4331_, 0);
v_isSharedCheck_4339_ = !lean_is_exclusive(v___x_4331_);
if (v_isSharedCheck_4339_ == 0)
{
v___x_4334_ = v___x_4331_;
v_isShared_4335_ = v_isSharedCheck_4339_;
goto v_resetjp_4333_;
}
else
{
lean_inc(v_a_4332_);
lean_dec(v___x_4331_);
v___x_4334_ = lean_box(0);
v_isShared_4335_ = v_isSharedCheck_4339_;
goto v_resetjp_4333_;
}
v_resetjp_4333_:
{
lean_object* v___x_4337_; 
if (v_isShared_4335_ == 0)
{
v___x_4337_ = v___x_4334_;
goto v_reusejp_4336_;
}
else
{
lean_object* v_reuseFailAlloc_4338_; 
v_reuseFailAlloc_4338_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4338_, 0, v_a_4332_);
v___x_4337_ = v_reuseFailAlloc_4338_;
goto v_reusejp_4336_;
}
v_reusejp_4336_:
{
return v___x_4337_;
}
}
}
}
}
else
{
lean_object* v_a_4340_; lean_object* v___x_4342_; uint8_t v_isShared_4343_; uint8_t v_isSharedCheck_4347_; 
lean_dec_ref(v___x_4328_);
lean_dec_ref(v_exprArgs_4309_);
lean_dec_ref(v_levelArgs_4308_);
lean_del_object(v___x_4301_);
lean_dec(v_name_4287_);
v_a_4340_ = lean_ctor_get(v___x_4330_, 0);
v_isSharedCheck_4347_ = !lean_is_exclusive(v___x_4330_);
if (v_isSharedCheck_4347_ == 0)
{
v___x_4342_ = v___x_4330_;
v_isShared_4343_ = v_isSharedCheck_4347_;
goto v_resetjp_4341_;
}
else
{
lean_inc(v_a_4340_);
lean_dec(v___x_4330_);
v___x_4342_ = lean_box(0);
v_isShared_4343_ = v_isSharedCheck_4347_;
goto v_resetjp_4341_;
}
v_resetjp_4341_:
{
lean_object* v___x_4345_; 
if (v_isShared_4343_ == 0)
{
v___x_4345_ = v___x_4342_;
goto v_reusejp_4344_;
}
else
{
lean_object* v_reuseFailAlloc_4346_; 
v_reuseFailAlloc_4346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4346_, 0, v_a_4340_);
v___x_4345_ = v_reuseFailAlloc_4346_;
goto v_reusejp_4344_;
}
v_reusejp_4344_:
{
return v___x_4345_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4351_; lean_object* v___x_4353_; uint8_t v_isShared_4354_; uint8_t v_isSharedCheck_4358_; 
lean_dec(v_name_4287_);
v_a_4351_ = lean_ctor_get(v___x_4298_, 0);
v_isSharedCheck_4358_ = !lean_is_exclusive(v___x_4298_);
if (v_isSharedCheck_4358_ == 0)
{
v___x_4353_ = v___x_4298_;
v_isShared_4354_ = v_isSharedCheck_4358_;
goto v_resetjp_4352_;
}
else
{
lean_inc(v_a_4351_);
lean_dec(v___x_4298_);
v___x_4353_ = lean_box(0);
v_isShared_4354_ = v_isSharedCheck_4358_;
goto v_resetjp_4352_;
}
v_resetjp_4352_:
{
lean_object* v___x_4356_; 
if (v_isShared_4354_ == 0)
{
v___x_4356_ = v___x_4353_;
goto v_reusejp_4355_;
}
else
{
lean_object* v_reuseFailAlloc_4357_; 
v_reuseFailAlloc_4357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4357_, 0, v_a_4351_);
v___x_4356_ = v_reuseFailAlloc_4357_;
goto v_reusejp_4355_;
}
v_reusejp_4355_:
{
return v___x_4356_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAuxDefinition___boxed(lean_object* v_name_4359_, lean_object* v_type_4360_, lean_object* v_value_4361_, lean_object* v_zetaDelta_4362_, lean_object* v_compile_4363_, lean_object* v_logCompileErrors_4364_, lean_object* v_a_4365_, lean_object* v_a_4366_, lean_object* v_a_4367_, lean_object* v_a_4368_, lean_object* v_a_4369_){
_start:
{
uint8_t v_zetaDelta_boxed_4370_; uint8_t v_compile_boxed_4371_; uint8_t v_logCompileErrors_boxed_4372_; lean_object* v_res_4373_; 
v_zetaDelta_boxed_4370_ = lean_unbox(v_zetaDelta_4362_);
v_compile_boxed_4371_ = lean_unbox(v_compile_4363_);
v_logCompileErrors_boxed_4372_ = lean_unbox(v_logCompileErrors_4364_);
v_res_4373_ = l_Lean_Meta_mkAuxDefinition(v_name_4359_, v_type_4360_, v_value_4361_, v_zetaDelta_boxed_4370_, v_compile_boxed_4371_, v_logCompileErrors_boxed_4372_, v_a_4365_, v_a_4366_, v_a_4367_, v_a_4368_);
lean_dec(v_a_4368_);
lean_dec_ref(v_a_4367_);
lean_dec(v_a_4366_);
lean_dec_ref(v_a_4365_);
return v_res_4373_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAuxDefinitionFor(lean_object* v_name_4374_, lean_object* v_value_4375_, uint8_t v_zetaDelta_4376_, uint8_t v_compile_4377_, uint8_t v_logCompileErrors_4378_, lean_object* v_a_4379_, lean_object* v_a_4380_, lean_object* v_a_4381_, lean_object* v_a_4382_){
_start:
{
lean_object* v___x_4384_; 
lean_inc(v_a_4382_);
lean_inc_ref(v_a_4381_);
lean_inc(v_a_4380_);
lean_inc_ref(v_a_4379_);
lean_inc_ref(v_value_4375_);
v___x_4384_ = lean_infer_type(v_value_4375_, v_a_4379_, v_a_4380_, v_a_4381_, v_a_4382_);
if (lean_obj_tag(v___x_4384_) == 0)
{
lean_object* v_a_4385_; lean_object* v___x_4386_; lean_object* v___x_4387_; 
v_a_4385_ = lean_ctor_get(v___x_4384_, 0);
lean_inc(v_a_4385_);
lean_dec_ref(v___x_4384_);
v___x_4386_ = l_Lean_Expr_headBeta(v_a_4385_);
v___x_4387_ = l_Lean_Meta_mkAuxDefinition(v_name_4374_, v___x_4386_, v_value_4375_, v_zetaDelta_4376_, v_compile_4377_, v_logCompileErrors_4378_, v_a_4379_, v_a_4380_, v_a_4381_, v_a_4382_);
return v___x_4387_;
}
else
{
lean_dec_ref(v_value_4375_);
lean_dec(v_name_4374_);
return v___x_4384_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAuxDefinitionFor___boxed(lean_object* v_name_4388_, lean_object* v_value_4389_, lean_object* v_zetaDelta_4390_, lean_object* v_compile_4391_, lean_object* v_logCompileErrors_4392_, lean_object* v_a_4393_, lean_object* v_a_4394_, lean_object* v_a_4395_, lean_object* v_a_4396_, lean_object* v_a_4397_){
_start:
{
uint8_t v_zetaDelta_boxed_4398_; uint8_t v_compile_boxed_4399_; uint8_t v_logCompileErrors_boxed_4400_; lean_object* v_res_4401_; 
v_zetaDelta_boxed_4398_ = lean_unbox(v_zetaDelta_4390_);
v_compile_boxed_4399_ = lean_unbox(v_compile_4391_);
v_logCompileErrors_boxed_4400_ = lean_unbox(v_logCompileErrors_4392_);
v_res_4401_ = l_Lean_Meta_mkAuxDefinitionFor(v_name_4388_, v_value_4389_, v_zetaDelta_boxed_4398_, v_compile_boxed_4399_, v_logCompileErrors_boxed_4400_, v_a_4393_, v_a_4394_, v_a_4395_, v_a_4396_);
lean_dec(v_a_4396_);
lean_dec_ref(v_a_4395_);
lean_dec(v_a_4394_);
lean_dec_ref(v_a_4393_);
return v_res_4401_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAuxTheorem(lean_object* v_type_4402_, lean_object* v_value_4403_, uint8_t v_zetaDelta_4404_, lean_object* v_kind_x3f_4405_, uint8_t v_cache_4406_, lean_object* v_a_4407_, lean_object* v_a_4408_, lean_object* v_a_4409_, lean_object* v_a_4410_){
_start:
{
lean_object* v___x_4412_; 
v___x_4412_ = l_Lean_Meta_Closure_mkValueTypeClosure(v_type_4402_, v_value_4403_, v_zetaDelta_4404_, v_a_4407_, v_a_4408_, v_a_4409_, v_a_4410_);
if (lean_obj_tag(v___x_4412_) == 0)
{
lean_object* v_a_4413_; lean_object* v_levelParams_4414_; lean_object* v_type_4415_; lean_object* v_value_4416_; lean_object* v_levelArgs_4417_; lean_object* v_exprArgs_4418_; lean_object* v___x_4419_; uint8_t v___x_4420_; lean_object* v___x_4421_; 
v_a_4413_ = lean_ctor_get(v___x_4412_, 0);
lean_inc(v_a_4413_);
lean_dec_ref(v___x_4412_);
v_levelParams_4414_ = lean_ctor_get(v_a_4413_, 0);
lean_inc_ref(v_levelParams_4414_);
v_type_4415_ = lean_ctor_get(v_a_4413_, 1);
lean_inc_ref(v_type_4415_);
v_value_4416_ = lean_ctor_get(v_a_4413_, 2);
lean_inc_ref(v_value_4416_);
v_levelArgs_4417_ = lean_ctor_get(v_a_4413_, 3);
lean_inc_ref(v_levelArgs_4417_);
v_exprArgs_4418_ = lean_ctor_get(v_a_4413_, 4);
lean_inc_ref(v_exprArgs_4418_);
lean_dec(v_a_4413_);
v___x_4419_ = lean_array_to_list(v_levelParams_4414_);
v___x_4420_ = 0;
v___x_4421_ = l_Lean_Meta_mkAuxLemma(v___x_4419_, v_type_4415_, v_value_4416_, v_kind_x3f_4405_, v_cache_4406_, v___x_4420_, v___x_4420_, v___x_4420_, v_a_4407_, v_a_4408_, v_a_4409_, v_a_4410_);
if (lean_obj_tag(v___x_4421_) == 0)
{
lean_object* v_a_4422_; lean_object* v___x_4424_; uint8_t v_isShared_4425_; uint8_t v_isSharedCheck_4432_; 
v_a_4422_ = lean_ctor_get(v___x_4421_, 0);
v_isSharedCheck_4432_ = !lean_is_exclusive(v___x_4421_);
if (v_isSharedCheck_4432_ == 0)
{
v___x_4424_ = v___x_4421_;
v_isShared_4425_ = v_isSharedCheck_4432_;
goto v_resetjp_4423_;
}
else
{
lean_inc(v_a_4422_);
lean_dec(v___x_4421_);
v___x_4424_ = lean_box(0);
v_isShared_4425_ = v_isSharedCheck_4432_;
goto v_resetjp_4423_;
}
v_resetjp_4423_:
{
lean_object* v___x_4426_; lean_object* v___x_4427_; lean_object* v___x_4428_; lean_object* v___x_4430_; 
v___x_4426_ = lean_array_to_list(v_levelArgs_4417_);
v___x_4427_ = l_Lean_mkConst(v_a_4422_, v___x_4426_);
v___x_4428_ = l_Lean_mkAppN(v___x_4427_, v_exprArgs_4418_);
lean_dec_ref(v_exprArgs_4418_);
if (v_isShared_4425_ == 0)
{
lean_ctor_set(v___x_4424_, 0, v___x_4428_);
v___x_4430_ = v___x_4424_;
goto v_reusejp_4429_;
}
else
{
lean_object* v_reuseFailAlloc_4431_; 
v_reuseFailAlloc_4431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4431_, 0, v___x_4428_);
v___x_4430_ = v_reuseFailAlloc_4431_;
goto v_reusejp_4429_;
}
v_reusejp_4429_:
{
return v___x_4430_;
}
}
}
else
{
lean_object* v_a_4433_; lean_object* v___x_4435_; uint8_t v_isShared_4436_; uint8_t v_isSharedCheck_4440_; 
lean_dec_ref(v_exprArgs_4418_);
lean_dec_ref(v_levelArgs_4417_);
v_a_4433_ = lean_ctor_get(v___x_4421_, 0);
v_isSharedCheck_4440_ = !lean_is_exclusive(v___x_4421_);
if (v_isSharedCheck_4440_ == 0)
{
v___x_4435_ = v___x_4421_;
v_isShared_4436_ = v_isSharedCheck_4440_;
goto v_resetjp_4434_;
}
else
{
lean_inc(v_a_4433_);
lean_dec(v___x_4421_);
v___x_4435_ = lean_box(0);
v_isShared_4436_ = v_isSharedCheck_4440_;
goto v_resetjp_4434_;
}
v_resetjp_4434_:
{
lean_object* v___x_4438_; 
if (v_isShared_4436_ == 0)
{
v___x_4438_ = v___x_4435_;
goto v_reusejp_4437_;
}
else
{
lean_object* v_reuseFailAlloc_4439_; 
v_reuseFailAlloc_4439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4439_, 0, v_a_4433_);
v___x_4438_ = v_reuseFailAlloc_4439_;
goto v_reusejp_4437_;
}
v_reusejp_4437_:
{
return v___x_4438_;
}
}
}
}
else
{
lean_object* v_a_4441_; lean_object* v___x_4443_; uint8_t v_isShared_4444_; uint8_t v_isSharedCheck_4448_; 
lean_dec(v_kind_x3f_4405_);
v_a_4441_ = lean_ctor_get(v___x_4412_, 0);
v_isSharedCheck_4448_ = !lean_is_exclusive(v___x_4412_);
if (v_isSharedCheck_4448_ == 0)
{
v___x_4443_ = v___x_4412_;
v_isShared_4444_ = v_isSharedCheck_4448_;
goto v_resetjp_4442_;
}
else
{
lean_inc(v_a_4441_);
lean_dec(v___x_4412_);
v___x_4443_ = lean_box(0);
v_isShared_4444_ = v_isSharedCheck_4448_;
goto v_resetjp_4442_;
}
v_resetjp_4442_:
{
lean_object* v___x_4446_; 
if (v_isShared_4444_ == 0)
{
v___x_4446_ = v___x_4443_;
goto v_reusejp_4445_;
}
else
{
lean_object* v_reuseFailAlloc_4447_; 
v_reuseFailAlloc_4447_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4447_, 0, v_a_4441_);
v___x_4446_ = v_reuseFailAlloc_4447_;
goto v_reusejp_4445_;
}
v_reusejp_4445_:
{
return v___x_4446_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAuxTheorem___boxed(lean_object* v_type_4449_, lean_object* v_value_4450_, lean_object* v_zetaDelta_4451_, lean_object* v_kind_x3f_4452_, lean_object* v_cache_4453_, lean_object* v_a_4454_, lean_object* v_a_4455_, lean_object* v_a_4456_, lean_object* v_a_4457_, lean_object* v_a_4458_){
_start:
{
uint8_t v_zetaDelta_boxed_4459_; uint8_t v_cache_boxed_4460_; lean_object* v_res_4461_; 
v_zetaDelta_boxed_4459_ = lean_unbox(v_zetaDelta_4451_);
v_cache_boxed_4460_ = lean_unbox(v_cache_4453_);
v_res_4461_ = l_Lean_Meta_mkAuxTheorem(v_type_4449_, v_value_4450_, v_zetaDelta_boxed_4459_, v_kind_x3f_4452_, v_cache_boxed_4460_, v_a_4454_, v_a_4455_, v_a_4456_, v_a_4457_);
lean_dec(v_a_4457_);
lean_dec_ref(v_a_4456_);
lean_dec(v_a_4455_);
lean_dec_ref(v_a_4454_);
return v_res_4461_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_initFn_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4517_; uint8_t v___x_4518_; lean_object* v___x_4519_; lean_object* v___x_4520_; 
v___x_4517_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__10));
v___x_4518_ = 0;
v___x_4519_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2_));
v___x_4520_ = l_Lean_registerTraceClass(v___x_4517_, v___x_4518_, v___x_4519_);
return v___x_4520_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_initFn_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2____boxed(lean_object* v_a_4521_){
_start:
{
lean_object* v_res_4522_; 
v_res_4522_ = l___private_Lean_Meta_Closure_0__Lean_Meta_initFn_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2_();
return v_res_4522_;
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
