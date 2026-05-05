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
uint8_t v___y_17871__boxed_946_; lean_object* v_res_947_; 
v___y_17871__boxed_946_ = lean_unbox(v___y_939_);
v_res_947_ = l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__4(v_mvarId_938_, v___y_17871__boxed_946_, v___y_940_, v___y_941_, v___y_942_, v___y_943_, v___y_944_);
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
uint8_t v___y_17894__boxed_970_; lean_object* v_res_971_; 
v___y_17894__boxed_970_ = lean_unbox(v___y_961_);
v_res_971_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Closure_collectExprAux_spec__5___redArg___lam__0(v_k_960_, v___y_17894__boxed_970_, v___y_962_, v_b_963_, v_c_964_, v___y_965_, v___y_966_, v___y_967_, v___y_968_);
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
uint8_t v_cleanupAnnotations_boxed_1007_; uint8_t v_whnfType_boxed_1008_; uint8_t v___y_17919__boxed_1009_; lean_object* v_res_1010_; 
v_cleanupAnnotations_boxed_1007_ = lean_unbox(v_cleanupAnnotations_998_);
v_whnfType_boxed_1008_ = lean_unbox(v_whnfType_999_);
v___y_17919__boxed_1009_ = lean_unbox(v___y_1000_);
v_res_1010_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Closure_collectExprAux_spec__5___redArg(v_type_995_, v_maxFVars_x3f_996_, v_k_997_, v_cleanupAnnotations_boxed_1007_, v_whnfType_boxed_1008_, v___y_17919__boxed_1009_, v___y_1001_, v___y_1002_, v___y_1003_, v___y_1004_, v___y_1005_);
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
uint8_t v_cleanupAnnotations_boxed_1038_; uint8_t v_whnfType_boxed_1039_; uint8_t v___y_17963__boxed_1040_; lean_object* v_res_1041_; 
v_cleanupAnnotations_boxed_1038_ = lean_unbox(v_cleanupAnnotations_1029_);
v_whnfType_boxed_1039_ = lean_unbox(v_whnfType_1030_);
v___y_17963__boxed_1040_ = lean_unbox(v___y_1031_);
v_res_1041_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Closure_collectExprAux_spec__5(v_00_u03b1_1025_, v_type_1026_, v_maxFVars_x3f_1027_, v_k_1028_, v_cleanupAnnotations_boxed_1038_, v_whnfType_boxed_1039_, v___y_17963__boxed_1040_, v___y_1032_, v___y_1033_, v___y_1034_, v___y_1035_, v___y_1036_);
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
lean_object* v___x_1108_; lean_object* v_ngen_1109_; lean_object* v_namePrefix_1110_; lean_object* v_idx_1111_; lean_object* v___x_1113_; uint8_t v_isShared_1114_; uint8_t v_isSharedCheck_1140_; 
v___x_1108_ = lean_st_ref_get(v___y_1106_);
v_ngen_1109_ = lean_ctor_get(v___x_1108_, 2);
lean_inc_ref(v_ngen_1109_);
lean_dec(v___x_1108_);
v_namePrefix_1110_ = lean_ctor_get(v_ngen_1109_, 0);
v_idx_1111_ = lean_ctor_get(v_ngen_1109_, 1);
v_isSharedCheck_1140_ = !lean_is_exclusive(v_ngen_1109_);
if (v_isSharedCheck_1140_ == 0)
{
v___x_1113_ = v_ngen_1109_;
v_isShared_1114_ = v_isSharedCheck_1140_;
goto v_resetjp_1112_;
}
else
{
lean_inc(v_idx_1111_);
lean_inc(v_namePrefix_1110_);
lean_dec(v_ngen_1109_);
v___x_1113_ = lean_box(0);
v_isShared_1114_ = v_isSharedCheck_1140_;
goto v_resetjp_1112_;
}
v_resetjp_1112_:
{
lean_object* v___x_1115_; lean_object* v_env_1116_; lean_object* v_nextMacroScope_1117_; lean_object* v_auxDeclNGen_1118_; lean_object* v_traceState_1119_; lean_object* v_cache_1120_; lean_object* v_messages_1121_; lean_object* v_infoState_1122_; lean_object* v_snapshotTasks_1123_; lean_object* v___x_1125_; uint8_t v_isShared_1126_; uint8_t v_isSharedCheck_1138_; 
v___x_1115_ = lean_st_ref_take(v___y_1106_);
v_env_1116_ = lean_ctor_get(v___x_1115_, 0);
v_nextMacroScope_1117_ = lean_ctor_get(v___x_1115_, 1);
v_auxDeclNGen_1118_ = lean_ctor_get(v___x_1115_, 3);
v_traceState_1119_ = lean_ctor_get(v___x_1115_, 4);
v_cache_1120_ = lean_ctor_get(v___x_1115_, 5);
v_messages_1121_ = lean_ctor_get(v___x_1115_, 6);
v_infoState_1122_ = lean_ctor_get(v___x_1115_, 7);
v_snapshotTasks_1123_ = lean_ctor_get(v___x_1115_, 8);
v_isSharedCheck_1138_ = !lean_is_exclusive(v___x_1115_);
if (v_isSharedCheck_1138_ == 0)
{
lean_object* v_unused_1139_; 
v_unused_1139_ = lean_ctor_get(v___x_1115_, 2);
lean_dec(v_unused_1139_);
v___x_1125_ = v___x_1115_;
v_isShared_1126_ = v_isSharedCheck_1138_;
goto v_resetjp_1124_;
}
else
{
lean_inc(v_snapshotTasks_1123_);
lean_inc(v_infoState_1122_);
lean_inc(v_messages_1121_);
lean_inc(v_cache_1120_);
lean_inc(v_traceState_1119_);
lean_inc(v_auxDeclNGen_1118_);
lean_inc(v_nextMacroScope_1117_);
lean_inc(v_env_1116_);
lean_dec(v___x_1115_);
v___x_1125_ = lean_box(0);
v_isShared_1126_ = v_isSharedCheck_1138_;
goto v_resetjp_1124_;
}
v_resetjp_1124_:
{
lean_object* v_r_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1131_; 
lean_inc(v_idx_1111_);
lean_inc(v_namePrefix_1110_);
v_r_1127_ = l_Lean_Name_num___override(v_namePrefix_1110_, v_idx_1111_);
v___x_1128_ = lean_unsigned_to_nat(1u);
v___x_1129_ = lean_nat_add(v_idx_1111_, v___x_1128_);
lean_dec(v_idx_1111_);
if (v_isShared_1114_ == 0)
{
lean_ctor_set(v___x_1113_, 1, v___x_1129_);
v___x_1131_ = v___x_1113_;
goto v_reusejp_1130_;
}
else
{
lean_object* v_reuseFailAlloc_1137_; 
v_reuseFailAlloc_1137_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1137_, 0, v_namePrefix_1110_);
lean_ctor_set(v_reuseFailAlloc_1137_, 1, v___x_1129_);
v___x_1131_ = v_reuseFailAlloc_1137_;
goto v_reusejp_1130_;
}
v_reusejp_1130_:
{
lean_object* v___x_1133_; 
if (v_isShared_1126_ == 0)
{
lean_ctor_set(v___x_1125_, 2, v___x_1131_);
v___x_1133_ = v___x_1125_;
goto v_reusejp_1132_;
}
else
{
lean_object* v_reuseFailAlloc_1136_; 
v_reuseFailAlloc_1136_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1136_, 0, v_env_1116_);
lean_ctor_set(v_reuseFailAlloc_1136_, 1, v_nextMacroScope_1117_);
lean_ctor_set(v_reuseFailAlloc_1136_, 2, v___x_1131_);
lean_ctor_set(v_reuseFailAlloc_1136_, 3, v_auxDeclNGen_1118_);
lean_ctor_set(v_reuseFailAlloc_1136_, 4, v_traceState_1119_);
lean_ctor_set(v_reuseFailAlloc_1136_, 5, v_cache_1120_);
lean_ctor_set(v_reuseFailAlloc_1136_, 6, v_messages_1121_);
lean_ctor_set(v_reuseFailAlloc_1136_, 7, v_infoState_1122_);
lean_ctor_set(v_reuseFailAlloc_1136_, 8, v_snapshotTasks_1123_);
v___x_1133_ = v_reuseFailAlloc_1136_;
goto v_reusejp_1132_;
}
v_reusejp_1132_:
{
lean_object* v___x_1134_; lean_object* v___x_1135_; 
v___x_1134_ = lean_st_ref_set(v___y_1106_, v___x_1133_);
v___x_1135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1135_, 0, v_r_1127_);
return v___x_1135_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Closure_collectExprAux_spec__3_spec__7___redArg___boxed(lean_object* v___y_1141_, lean_object* v___y_1142_){
_start:
{
lean_object* v_res_1143_; 
v_res_1143_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Closure_collectExprAux_spec__3_spec__7___redArg(v___y_1141_);
lean_dec(v___y_1141_);
return v_res_1143_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00Lean_Meta_Closure_collectExprAux_spec__3(uint8_t v___y_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_){
_start:
{
lean_object* v___x_1151_; lean_object* v_a_1152_; lean_object* v___x_1154_; uint8_t v_isShared_1155_; uint8_t v_isSharedCheck_1159_; 
v___x_1151_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Closure_collectExprAux_spec__3_spec__7___redArg(v___y_1149_);
v_a_1152_ = lean_ctor_get(v___x_1151_, 0);
v_isSharedCheck_1159_ = !lean_is_exclusive(v___x_1151_);
if (v_isSharedCheck_1159_ == 0)
{
v___x_1154_ = v___x_1151_;
v_isShared_1155_ = v_isSharedCheck_1159_;
goto v_resetjp_1153_;
}
else
{
lean_inc(v_a_1152_);
lean_dec(v___x_1151_);
v___x_1154_ = lean_box(0);
v_isShared_1155_ = v_isSharedCheck_1159_;
goto v_resetjp_1153_;
}
v_resetjp_1153_:
{
lean_object* v___x_1157_; 
if (v_isShared_1155_ == 0)
{
v___x_1157_ = v___x_1154_;
goto v_reusejp_1156_;
}
else
{
lean_object* v_reuseFailAlloc_1158_; 
v_reuseFailAlloc_1158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1158_, 0, v_a_1152_);
v___x_1157_ = v_reuseFailAlloc_1158_;
goto v_reusejp_1156_;
}
v_reusejp_1156_:
{
return v___x_1157_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00Lean_Meta_Closure_collectExprAux_spec__3___boxed(lean_object* v___y_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_){
_start:
{
uint8_t v___y_18138__boxed_1167_; lean_object* v_res_1168_; 
v___y_18138__boxed_1167_ = lean_unbox(v___y_1160_);
v_res_1168_ = l_Lean_mkFreshFVarId___at___00Lean_Meta_Closure_collectExprAux_spec__3(v___y_18138__boxed_1167_, v___y_1161_, v___y_1162_, v___y_1163_, v___y_1164_, v___y_1165_);
lean_dec(v___y_1165_);
lean_dec_ref(v___y_1164_);
lean_dec(v___y_1163_);
lean_dec_ref(v___y_1162_);
lean_dec(v___y_1161_);
return v_res_1168_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectExprAux___lam__1(lean_object* v_e_1169_, lean_object* v_args_1170_, lean_object* v_x_1171_, uint8_t v___y_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_){
_start:
{
lean_object* v___x_1179_; uint8_t v___x_1180_; uint8_t v___x_1181_; uint8_t v___x_1182_; lean_object* v___x_1183_; 
v___x_1179_ = l_Lean_mkAppN(v_e_1169_, v_args_1170_);
v___x_1180_ = 0;
v___x_1181_ = 1;
v___x_1182_ = 1;
v___x_1183_ = l_Lean_Meta_mkLambdaFVars(v_args_1170_, v___x_1179_, v___x_1180_, v___x_1181_, v___x_1180_, v___x_1181_, v___x_1182_, v___y_1174_, v___y_1175_, v___y_1176_, v___y_1177_);
return v___x_1183_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectExprAux___lam__1___boxed(lean_object* v_e_1184_, lean_object* v_args_1185_, lean_object* v_x_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_){
_start:
{
uint8_t v___y_18179__boxed_1194_; lean_object* v_res_1195_; 
v___y_18179__boxed_1194_ = lean_unbox(v___y_1187_);
v_res_1195_ = l_Lean_Meta_Closure_collectExprAux___lam__1(v_e_1184_, v_args_1185_, v_x_1186_, v___y_18179__boxed_1194_, v___y_1188_, v___y_1189_, v___y_1190_, v___y_1191_, v___y_1192_);
lean_dec(v___y_1192_);
lean_dec_ref(v___y_1191_);
lean_dec(v___y_1190_);
lean_dec_ref(v___y_1189_);
lean_dec(v___y_1188_);
lean_dec_ref(v_x_1186_);
lean_dec_ref(v_args_1185_);
return v_res_1195_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__3_spec__6_spec__10___redArg(lean_object* v_x_1196_, lean_object* v_x_1197_){
_start:
{
if (lean_obj_tag(v_x_1197_) == 0)
{
return v_x_1196_;
}
else
{
lean_object* v_key_1198_; lean_object* v_value_1199_; lean_object* v_tail_1200_; lean_object* v___x_1202_; uint8_t v_isShared_1203_; uint8_t v_isSharedCheck_1223_; 
v_key_1198_ = lean_ctor_get(v_x_1197_, 0);
v_value_1199_ = lean_ctor_get(v_x_1197_, 1);
v_tail_1200_ = lean_ctor_get(v_x_1197_, 2);
v_isSharedCheck_1223_ = !lean_is_exclusive(v_x_1197_);
if (v_isSharedCheck_1223_ == 0)
{
v___x_1202_ = v_x_1197_;
v_isShared_1203_ = v_isSharedCheck_1223_;
goto v_resetjp_1201_;
}
else
{
lean_inc(v_tail_1200_);
lean_inc(v_value_1199_);
lean_inc(v_key_1198_);
lean_dec(v_x_1197_);
v___x_1202_ = lean_box(0);
v_isShared_1203_ = v_isSharedCheck_1223_;
goto v_resetjp_1201_;
}
v_resetjp_1201_:
{
lean_object* v___x_1204_; uint64_t v___x_1205_; uint64_t v___x_1206_; uint64_t v___x_1207_; uint64_t v_fold_1208_; uint64_t v___x_1209_; uint64_t v___x_1210_; uint64_t v___x_1211_; size_t v___x_1212_; size_t v___x_1213_; size_t v___x_1214_; size_t v___x_1215_; size_t v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1219_; 
v___x_1204_ = lean_array_get_size(v_x_1196_);
v___x_1205_ = l_Lean_ExprStructEq_hash(v_key_1198_);
v___x_1206_ = 32ULL;
v___x_1207_ = lean_uint64_shift_right(v___x_1205_, v___x_1206_);
v_fold_1208_ = lean_uint64_xor(v___x_1205_, v___x_1207_);
v___x_1209_ = 16ULL;
v___x_1210_ = lean_uint64_shift_right(v_fold_1208_, v___x_1209_);
v___x_1211_ = lean_uint64_xor(v_fold_1208_, v___x_1210_);
v___x_1212_ = lean_uint64_to_usize(v___x_1211_);
v___x_1213_ = lean_usize_of_nat(v___x_1204_);
v___x_1214_ = ((size_t)1ULL);
v___x_1215_ = lean_usize_sub(v___x_1213_, v___x_1214_);
v___x_1216_ = lean_usize_land(v___x_1212_, v___x_1215_);
v___x_1217_ = lean_array_uget_borrowed(v_x_1196_, v___x_1216_);
lean_inc(v___x_1217_);
if (v_isShared_1203_ == 0)
{
lean_ctor_set(v___x_1202_, 2, v___x_1217_);
v___x_1219_ = v___x_1202_;
goto v_reusejp_1218_;
}
else
{
lean_object* v_reuseFailAlloc_1222_; 
v_reuseFailAlloc_1222_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1222_, 0, v_key_1198_);
lean_ctor_set(v_reuseFailAlloc_1222_, 1, v_value_1199_);
lean_ctor_set(v_reuseFailAlloc_1222_, 2, v___x_1217_);
v___x_1219_ = v_reuseFailAlloc_1222_;
goto v_reusejp_1218_;
}
v_reusejp_1218_:
{
lean_object* v___x_1220_; 
v___x_1220_ = lean_array_uset(v_x_1196_, v___x_1216_, v___x_1219_);
v_x_1196_ = v___x_1220_;
v_x_1197_ = v_tail_1200_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__3_spec__6___redArg(lean_object* v_i_1224_, lean_object* v_source_1225_, lean_object* v_target_1226_){
_start:
{
lean_object* v___x_1227_; uint8_t v___x_1228_; 
v___x_1227_ = lean_array_get_size(v_source_1225_);
v___x_1228_ = lean_nat_dec_lt(v_i_1224_, v___x_1227_);
if (v___x_1228_ == 0)
{
lean_dec_ref(v_source_1225_);
lean_dec(v_i_1224_);
return v_target_1226_;
}
else
{
lean_object* v_es_1229_; lean_object* v___x_1230_; lean_object* v_source_1231_; lean_object* v_target_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; 
v_es_1229_ = lean_array_fget(v_source_1225_, v_i_1224_);
v___x_1230_ = lean_box(0);
v_source_1231_ = lean_array_fset(v_source_1225_, v_i_1224_, v___x_1230_);
v_target_1232_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__3_spec__6_spec__10___redArg(v_target_1226_, v_es_1229_);
v___x_1233_ = lean_unsigned_to_nat(1u);
v___x_1234_ = lean_nat_add(v_i_1224_, v___x_1233_);
lean_dec(v_i_1224_);
v_i_1224_ = v___x_1234_;
v_source_1225_ = v_source_1231_;
v_target_1226_ = v_target_1232_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__3___redArg(lean_object* v_data_1236_){
_start:
{
lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v_nbuckets_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; 
v___x_1237_ = lean_array_get_size(v_data_1236_);
v___x_1238_ = lean_unsigned_to_nat(2u);
v_nbuckets_1239_ = lean_nat_mul(v___x_1237_, v___x_1238_);
v___x_1240_ = lean_unsigned_to_nat(0u);
v___x_1241_ = lean_box(0);
v___x_1242_ = lean_mk_array(v_nbuckets_1239_, v___x_1241_);
v___x_1243_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__3_spec__6___redArg(v___x_1240_, v_data_1236_, v___x_1242_);
return v___x_1243_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__4___redArg(lean_object* v_a_1244_, lean_object* v_b_1245_, lean_object* v_x_1246_){
_start:
{
if (lean_obj_tag(v_x_1246_) == 0)
{
lean_dec(v_b_1245_);
lean_dec_ref(v_a_1244_);
return v_x_1246_;
}
else
{
lean_object* v_key_1247_; lean_object* v_value_1248_; lean_object* v_tail_1249_; lean_object* v___x_1251_; uint8_t v_isShared_1252_; uint8_t v_isSharedCheck_1261_; 
v_key_1247_ = lean_ctor_get(v_x_1246_, 0);
v_value_1248_ = lean_ctor_get(v_x_1246_, 1);
v_tail_1249_ = lean_ctor_get(v_x_1246_, 2);
v_isSharedCheck_1261_ = !lean_is_exclusive(v_x_1246_);
if (v_isSharedCheck_1261_ == 0)
{
v___x_1251_ = v_x_1246_;
v_isShared_1252_ = v_isSharedCheck_1261_;
goto v_resetjp_1250_;
}
else
{
lean_inc(v_tail_1249_);
lean_inc(v_value_1248_);
lean_inc(v_key_1247_);
lean_dec(v_x_1246_);
v___x_1251_ = lean_box(0);
v_isShared_1252_ = v_isSharedCheck_1261_;
goto v_resetjp_1250_;
}
v_resetjp_1250_:
{
uint8_t v___x_1253_; 
v___x_1253_ = l_Lean_ExprStructEq_beq(v_key_1247_, v_a_1244_);
if (v___x_1253_ == 0)
{
lean_object* v___x_1254_; lean_object* v___x_1256_; 
v___x_1254_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__4___redArg(v_a_1244_, v_b_1245_, v_tail_1249_);
if (v_isShared_1252_ == 0)
{
lean_ctor_set(v___x_1251_, 2, v___x_1254_);
v___x_1256_ = v___x_1251_;
goto v_reusejp_1255_;
}
else
{
lean_object* v_reuseFailAlloc_1257_; 
v_reuseFailAlloc_1257_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1257_, 0, v_key_1247_);
lean_ctor_set(v_reuseFailAlloc_1257_, 1, v_value_1248_);
lean_ctor_set(v_reuseFailAlloc_1257_, 2, v___x_1254_);
v___x_1256_ = v_reuseFailAlloc_1257_;
goto v_reusejp_1255_;
}
v_reusejp_1255_:
{
return v___x_1256_;
}
}
else
{
lean_object* v___x_1259_; 
lean_dec(v_value_1248_);
lean_dec(v_key_1247_);
if (v_isShared_1252_ == 0)
{
lean_ctor_set(v___x_1251_, 1, v_b_1245_);
lean_ctor_set(v___x_1251_, 0, v_a_1244_);
v___x_1259_ = v___x_1251_;
goto v_reusejp_1258_;
}
else
{
lean_object* v_reuseFailAlloc_1260_; 
v_reuseFailAlloc_1260_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1260_, 0, v_a_1244_);
lean_ctor_set(v_reuseFailAlloc_1260_, 1, v_b_1245_);
lean_ctor_set(v_reuseFailAlloc_1260_, 2, v_tail_1249_);
v___x_1259_ = v_reuseFailAlloc_1260_;
goto v_reusejp_1258_;
}
v_reusejp_1258_:
{
return v___x_1259_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__2___redArg(lean_object* v_a_1262_, lean_object* v_x_1263_){
_start:
{
if (lean_obj_tag(v_x_1263_) == 0)
{
uint8_t v___x_1264_; 
v___x_1264_ = 0;
return v___x_1264_;
}
else
{
lean_object* v_key_1265_; lean_object* v_tail_1266_; uint8_t v___x_1267_; 
v_key_1265_ = lean_ctor_get(v_x_1263_, 0);
v_tail_1266_ = lean_ctor_get(v_x_1263_, 2);
v___x_1267_ = l_Lean_ExprStructEq_beq(v_key_1265_, v_a_1262_);
if (v___x_1267_ == 0)
{
v_x_1263_ = v_tail_1266_;
goto _start;
}
else
{
return v___x_1267_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__2___redArg___boxed(lean_object* v_a_1269_, lean_object* v_x_1270_){
_start:
{
uint8_t v_res_1271_; lean_object* v_r_1272_; 
v_res_1271_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__2___redArg(v_a_1269_, v_x_1270_);
lean_dec(v_x_1270_);
lean_dec_ref(v_a_1269_);
v_r_1272_ = lean_box(v_res_1271_);
return v_r_1272_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1___redArg(lean_object* v_m_1273_, lean_object* v_a_1274_, lean_object* v_b_1275_){
_start:
{
lean_object* v_size_1276_; lean_object* v_buckets_1277_; lean_object* v___x_1279_; uint8_t v_isShared_1280_; uint8_t v_isSharedCheck_1320_; 
v_size_1276_ = lean_ctor_get(v_m_1273_, 0);
v_buckets_1277_ = lean_ctor_get(v_m_1273_, 1);
v_isSharedCheck_1320_ = !lean_is_exclusive(v_m_1273_);
if (v_isSharedCheck_1320_ == 0)
{
v___x_1279_ = v_m_1273_;
v_isShared_1280_ = v_isSharedCheck_1320_;
goto v_resetjp_1278_;
}
else
{
lean_inc(v_buckets_1277_);
lean_inc(v_size_1276_);
lean_dec(v_m_1273_);
v___x_1279_ = lean_box(0);
v_isShared_1280_ = v_isSharedCheck_1320_;
goto v_resetjp_1278_;
}
v_resetjp_1278_:
{
lean_object* v___x_1281_; uint64_t v___x_1282_; uint64_t v___x_1283_; uint64_t v___x_1284_; uint64_t v_fold_1285_; uint64_t v___x_1286_; uint64_t v___x_1287_; uint64_t v___x_1288_; size_t v___x_1289_; size_t v___x_1290_; size_t v___x_1291_; size_t v___x_1292_; size_t v___x_1293_; lean_object* v_bkt_1294_; uint8_t v___x_1295_; 
v___x_1281_ = lean_array_get_size(v_buckets_1277_);
v___x_1282_ = l_Lean_ExprStructEq_hash(v_a_1274_);
v___x_1283_ = 32ULL;
v___x_1284_ = lean_uint64_shift_right(v___x_1282_, v___x_1283_);
v_fold_1285_ = lean_uint64_xor(v___x_1282_, v___x_1284_);
v___x_1286_ = 16ULL;
v___x_1287_ = lean_uint64_shift_right(v_fold_1285_, v___x_1286_);
v___x_1288_ = lean_uint64_xor(v_fold_1285_, v___x_1287_);
v___x_1289_ = lean_uint64_to_usize(v___x_1288_);
v___x_1290_ = lean_usize_of_nat(v___x_1281_);
v___x_1291_ = ((size_t)1ULL);
v___x_1292_ = lean_usize_sub(v___x_1290_, v___x_1291_);
v___x_1293_ = lean_usize_land(v___x_1289_, v___x_1292_);
v_bkt_1294_ = lean_array_uget_borrowed(v_buckets_1277_, v___x_1293_);
v___x_1295_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__2___redArg(v_a_1274_, v_bkt_1294_);
if (v___x_1295_ == 0)
{
lean_object* v___x_1296_; lean_object* v_size_x27_1297_; lean_object* v___x_1298_; lean_object* v_buckets_x27_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; uint8_t v___x_1305_; 
v___x_1296_ = lean_unsigned_to_nat(1u);
v_size_x27_1297_ = lean_nat_add(v_size_1276_, v___x_1296_);
lean_dec(v_size_1276_);
lean_inc(v_bkt_1294_);
v___x_1298_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1298_, 0, v_a_1274_);
lean_ctor_set(v___x_1298_, 1, v_b_1275_);
lean_ctor_set(v___x_1298_, 2, v_bkt_1294_);
v_buckets_x27_1299_ = lean_array_uset(v_buckets_1277_, v___x_1293_, v___x_1298_);
v___x_1300_ = lean_unsigned_to_nat(4u);
v___x_1301_ = lean_nat_mul(v_size_x27_1297_, v___x_1300_);
v___x_1302_ = lean_unsigned_to_nat(3u);
v___x_1303_ = lean_nat_div(v___x_1301_, v___x_1302_);
lean_dec(v___x_1301_);
v___x_1304_ = lean_array_get_size(v_buckets_x27_1299_);
v___x_1305_ = lean_nat_dec_le(v___x_1303_, v___x_1304_);
lean_dec(v___x_1303_);
if (v___x_1305_ == 0)
{
lean_object* v_val_1306_; lean_object* v___x_1308_; 
v_val_1306_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__3___redArg(v_buckets_x27_1299_);
if (v_isShared_1280_ == 0)
{
lean_ctor_set(v___x_1279_, 1, v_val_1306_);
lean_ctor_set(v___x_1279_, 0, v_size_x27_1297_);
v___x_1308_ = v___x_1279_;
goto v_reusejp_1307_;
}
else
{
lean_object* v_reuseFailAlloc_1309_; 
v_reuseFailAlloc_1309_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1309_, 0, v_size_x27_1297_);
lean_ctor_set(v_reuseFailAlloc_1309_, 1, v_val_1306_);
v___x_1308_ = v_reuseFailAlloc_1309_;
goto v_reusejp_1307_;
}
v_reusejp_1307_:
{
return v___x_1308_;
}
}
else
{
lean_object* v___x_1311_; 
if (v_isShared_1280_ == 0)
{
lean_ctor_set(v___x_1279_, 1, v_buckets_x27_1299_);
lean_ctor_set(v___x_1279_, 0, v_size_x27_1297_);
v___x_1311_ = v___x_1279_;
goto v_reusejp_1310_;
}
else
{
lean_object* v_reuseFailAlloc_1312_; 
v_reuseFailAlloc_1312_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1312_, 0, v_size_x27_1297_);
lean_ctor_set(v_reuseFailAlloc_1312_, 1, v_buckets_x27_1299_);
v___x_1311_ = v_reuseFailAlloc_1312_;
goto v_reusejp_1310_;
}
v_reusejp_1310_:
{
return v___x_1311_;
}
}
}
else
{
lean_object* v___x_1313_; lean_object* v_buckets_x27_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1318_; 
lean_inc(v_bkt_1294_);
v___x_1313_ = lean_box(0);
v_buckets_x27_1314_ = lean_array_uset(v_buckets_1277_, v___x_1293_, v___x_1313_);
v___x_1315_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__4___redArg(v_a_1274_, v_b_1275_, v_bkt_1294_);
v___x_1316_ = lean_array_uset(v_buckets_x27_1314_, v___x_1293_, v___x_1315_);
if (v_isShared_1280_ == 0)
{
lean_ctor_set(v___x_1279_, 1, v___x_1316_);
v___x_1318_ = v___x_1279_;
goto v_reusejp_1317_;
}
else
{
lean_object* v_reuseFailAlloc_1319_; 
v_reuseFailAlloc_1319_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1319_, 0, v_size_1276_);
lean_ctor_set(v_reuseFailAlloc_1319_, 1, v___x_1316_);
v___x_1318_ = v_reuseFailAlloc_1319_;
goto v_reusejp_1317_;
}
v_reusejp_1317_:
{
return v___x_1318_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectExprAux(lean_object* v_e_1321_, uint8_t v_a_1322_, lean_object* v_a_1323_, lean_object* v_a_1324_, lean_object* v_a_1325_, lean_object* v_a_1326_, lean_object* v_a_1327_){
_start:
{
switch(lean_obj_tag(v_e_1321_))
{
case 11:
{
lean_object* v_typeName_1329_; lean_object* v_idx_1330_; lean_object* v_struct_1331_; lean_object* v___x_1332_; 
v_typeName_1329_ = lean_ctor_get(v_e_1321_, 0);
v_idx_1330_ = lean_ctor_get(v_e_1321_, 1);
v_struct_1331_ = lean_ctor_get(v_e_1321_, 2);
lean_inc_ref(v_struct_1331_);
v___x_1332_ = l_Lean_Meta_Closure_collectExprAux___lam__0(v_struct_1331_, v_a_1322_, v_a_1323_, v_a_1324_, v_a_1325_, v_a_1326_, v_a_1327_);
if (lean_obj_tag(v___x_1332_) == 0)
{
lean_object* v_a_1333_; lean_object* v___x_1335_; uint8_t v_isShared_1336_; uint8_t v_isSharedCheck_1347_; 
v_a_1333_ = lean_ctor_get(v___x_1332_, 0);
v_isSharedCheck_1347_ = !lean_is_exclusive(v___x_1332_);
if (v_isSharedCheck_1347_ == 0)
{
v___x_1335_ = v___x_1332_;
v_isShared_1336_ = v_isSharedCheck_1347_;
goto v_resetjp_1334_;
}
else
{
lean_inc(v_a_1333_);
lean_dec(v___x_1332_);
v___x_1335_ = lean_box(0);
v_isShared_1336_ = v_isSharedCheck_1347_;
goto v_resetjp_1334_;
}
v_resetjp_1334_:
{
size_t v___x_1337_; size_t v___x_1338_; uint8_t v___x_1339_; 
v___x_1337_ = lean_ptr_addr(v_struct_1331_);
v___x_1338_ = lean_ptr_addr(v_a_1333_);
v___x_1339_ = lean_usize_dec_eq(v___x_1337_, v___x_1338_);
if (v___x_1339_ == 0)
{
lean_object* v___x_1340_; lean_object* v___x_1342_; 
lean_inc(v_idx_1330_);
lean_inc(v_typeName_1329_);
lean_dec_ref(v_e_1321_);
v___x_1340_ = l_Lean_Expr_proj___override(v_typeName_1329_, v_idx_1330_, v_a_1333_);
if (v_isShared_1336_ == 0)
{
lean_ctor_set(v___x_1335_, 0, v___x_1340_);
v___x_1342_ = v___x_1335_;
goto v_reusejp_1341_;
}
else
{
lean_object* v_reuseFailAlloc_1343_; 
v_reuseFailAlloc_1343_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1343_, 0, v___x_1340_);
v___x_1342_ = v_reuseFailAlloc_1343_;
goto v_reusejp_1341_;
}
v_reusejp_1341_:
{
return v___x_1342_;
}
}
else
{
lean_object* v___x_1345_; 
lean_dec(v_a_1333_);
if (v_isShared_1336_ == 0)
{
lean_ctor_set(v___x_1335_, 0, v_e_1321_);
v___x_1345_ = v___x_1335_;
goto v_reusejp_1344_;
}
else
{
lean_object* v_reuseFailAlloc_1346_; 
v_reuseFailAlloc_1346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1346_, 0, v_e_1321_);
v___x_1345_ = v_reuseFailAlloc_1346_;
goto v_reusejp_1344_;
}
v_reusejp_1344_:
{
return v___x_1345_;
}
}
}
}
else
{
lean_dec_ref(v_e_1321_);
return v___x_1332_;
}
}
case 7:
{
lean_object* v_binderName_1348_; lean_object* v_binderType_1349_; lean_object* v_body_1350_; uint8_t v_binderInfo_1351_; lean_object* v___x_1352_; 
v_binderName_1348_ = lean_ctor_get(v_e_1321_, 0);
v_binderType_1349_ = lean_ctor_get(v_e_1321_, 1);
v_body_1350_ = lean_ctor_get(v_e_1321_, 2);
v_binderInfo_1351_ = lean_ctor_get_uint8(v_e_1321_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_1349_);
v___x_1352_ = l_Lean_Meta_Closure_collectExprAux___lam__0(v_binderType_1349_, v_a_1322_, v_a_1323_, v_a_1324_, v_a_1325_, v_a_1326_, v_a_1327_);
if (lean_obj_tag(v___x_1352_) == 0)
{
lean_object* v_a_1353_; lean_object* v___x_1354_; 
v_a_1353_ = lean_ctor_get(v___x_1352_, 0);
lean_inc(v_a_1353_);
lean_dec_ref(v___x_1352_);
lean_inc_ref(v_body_1350_);
v___x_1354_ = l_Lean_Meta_Closure_collectExprAux___lam__0(v_body_1350_, v_a_1322_, v_a_1323_, v_a_1324_, v_a_1325_, v_a_1326_, v_a_1327_);
if (lean_obj_tag(v___x_1354_) == 0)
{
lean_object* v_a_1355_; lean_object* v___x_1357_; uint8_t v_isShared_1358_; uint8_t v_isSharedCheck_1379_; 
v_a_1355_ = lean_ctor_get(v___x_1354_, 0);
v_isSharedCheck_1379_ = !lean_is_exclusive(v___x_1354_);
if (v_isSharedCheck_1379_ == 0)
{
v___x_1357_ = v___x_1354_;
v_isShared_1358_ = v_isSharedCheck_1379_;
goto v_resetjp_1356_;
}
else
{
lean_inc(v_a_1355_);
lean_dec(v___x_1354_);
v___x_1357_ = lean_box(0);
v_isShared_1358_ = v_isSharedCheck_1379_;
goto v_resetjp_1356_;
}
v_resetjp_1356_:
{
uint8_t v___y_1360_; size_t v___x_1373_; size_t v___x_1374_; uint8_t v___x_1375_; 
v___x_1373_ = lean_ptr_addr(v_binderType_1349_);
v___x_1374_ = lean_ptr_addr(v_a_1353_);
v___x_1375_ = lean_usize_dec_eq(v___x_1373_, v___x_1374_);
if (v___x_1375_ == 0)
{
v___y_1360_ = v___x_1375_;
goto v___jp_1359_;
}
else
{
size_t v___x_1376_; size_t v___x_1377_; uint8_t v___x_1378_; 
v___x_1376_ = lean_ptr_addr(v_body_1350_);
v___x_1377_ = lean_ptr_addr(v_a_1355_);
v___x_1378_ = lean_usize_dec_eq(v___x_1376_, v___x_1377_);
v___y_1360_ = v___x_1378_;
goto v___jp_1359_;
}
v___jp_1359_:
{
if (v___y_1360_ == 0)
{
lean_object* v___x_1361_; lean_object* v___x_1363_; 
lean_inc(v_binderName_1348_);
lean_dec_ref(v_e_1321_);
v___x_1361_ = l_Lean_Expr_forallE___override(v_binderName_1348_, v_a_1353_, v_a_1355_, v_binderInfo_1351_);
if (v_isShared_1358_ == 0)
{
lean_ctor_set(v___x_1357_, 0, v___x_1361_);
v___x_1363_ = v___x_1357_;
goto v_reusejp_1362_;
}
else
{
lean_object* v_reuseFailAlloc_1364_; 
v_reuseFailAlloc_1364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1364_, 0, v___x_1361_);
v___x_1363_ = v_reuseFailAlloc_1364_;
goto v_reusejp_1362_;
}
v_reusejp_1362_:
{
return v___x_1363_;
}
}
else
{
uint8_t v___x_1365_; 
v___x_1365_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_1351_, v_binderInfo_1351_);
if (v___x_1365_ == 0)
{
lean_object* v___x_1366_; lean_object* v___x_1368_; 
lean_inc(v_binderName_1348_);
lean_dec_ref(v_e_1321_);
v___x_1366_ = l_Lean_Expr_forallE___override(v_binderName_1348_, v_a_1353_, v_a_1355_, v_binderInfo_1351_);
if (v_isShared_1358_ == 0)
{
lean_ctor_set(v___x_1357_, 0, v___x_1366_);
v___x_1368_ = v___x_1357_;
goto v_reusejp_1367_;
}
else
{
lean_object* v_reuseFailAlloc_1369_; 
v_reuseFailAlloc_1369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1369_, 0, v___x_1366_);
v___x_1368_ = v_reuseFailAlloc_1369_;
goto v_reusejp_1367_;
}
v_reusejp_1367_:
{
return v___x_1368_;
}
}
else
{
lean_object* v___x_1371_; 
lean_dec(v_a_1355_);
lean_dec(v_a_1353_);
if (v_isShared_1358_ == 0)
{
lean_ctor_set(v___x_1357_, 0, v_e_1321_);
v___x_1371_ = v___x_1357_;
goto v_reusejp_1370_;
}
else
{
lean_object* v_reuseFailAlloc_1372_; 
v_reuseFailAlloc_1372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1372_, 0, v_e_1321_);
v___x_1371_ = v_reuseFailAlloc_1372_;
goto v_reusejp_1370_;
}
v_reusejp_1370_:
{
return v___x_1371_;
}
}
}
}
}
}
else
{
lean_dec(v_a_1353_);
lean_dec_ref(v_e_1321_);
return v___x_1354_;
}
}
else
{
lean_dec_ref(v_e_1321_);
return v___x_1352_;
}
}
case 6:
{
lean_object* v_binderName_1380_; lean_object* v_binderType_1381_; lean_object* v_body_1382_; uint8_t v_binderInfo_1383_; lean_object* v___x_1384_; 
v_binderName_1380_ = lean_ctor_get(v_e_1321_, 0);
v_binderType_1381_ = lean_ctor_get(v_e_1321_, 1);
v_body_1382_ = lean_ctor_get(v_e_1321_, 2);
v_binderInfo_1383_ = lean_ctor_get_uint8(v_e_1321_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_1381_);
v___x_1384_ = l_Lean_Meta_Closure_collectExprAux___lam__0(v_binderType_1381_, v_a_1322_, v_a_1323_, v_a_1324_, v_a_1325_, v_a_1326_, v_a_1327_);
if (lean_obj_tag(v___x_1384_) == 0)
{
lean_object* v_a_1385_; lean_object* v___x_1386_; 
v_a_1385_ = lean_ctor_get(v___x_1384_, 0);
lean_inc(v_a_1385_);
lean_dec_ref(v___x_1384_);
lean_inc_ref(v_body_1382_);
v___x_1386_ = l_Lean_Meta_Closure_collectExprAux___lam__0(v_body_1382_, v_a_1322_, v_a_1323_, v_a_1324_, v_a_1325_, v_a_1326_, v_a_1327_);
if (lean_obj_tag(v___x_1386_) == 0)
{
lean_object* v_a_1387_; lean_object* v___x_1389_; uint8_t v_isShared_1390_; uint8_t v_isSharedCheck_1411_; 
v_a_1387_ = lean_ctor_get(v___x_1386_, 0);
v_isSharedCheck_1411_ = !lean_is_exclusive(v___x_1386_);
if (v_isSharedCheck_1411_ == 0)
{
v___x_1389_ = v___x_1386_;
v_isShared_1390_ = v_isSharedCheck_1411_;
goto v_resetjp_1388_;
}
else
{
lean_inc(v_a_1387_);
lean_dec(v___x_1386_);
v___x_1389_ = lean_box(0);
v_isShared_1390_ = v_isSharedCheck_1411_;
goto v_resetjp_1388_;
}
v_resetjp_1388_:
{
uint8_t v___y_1392_; size_t v___x_1405_; size_t v___x_1406_; uint8_t v___x_1407_; 
v___x_1405_ = lean_ptr_addr(v_binderType_1381_);
v___x_1406_ = lean_ptr_addr(v_a_1385_);
v___x_1407_ = lean_usize_dec_eq(v___x_1405_, v___x_1406_);
if (v___x_1407_ == 0)
{
v___y_1392_ = v___x_1407_;
goto v___jp_1391_;
}
else
{
size_t v___x_1408_; size_t v___x_1409_; uint8_t v___x_1410_; 
v___x_1408_ = lean_ptr_addr(v_body_1382_);
v___x_1409_ = lean_ptr_addr(v_a_1387_);
v___x_1410_ = lean_usize_dec_eq(v___x_1408_, v___x_1409_);
v___y_1392_ = v___x_1410_;
goto v___jp_1391_;
}
v___jp_1391_:
{
if (v___y_1392_ == 0)
{
lean_object* v___x_1393_; lean_object* v___x_1395_; 
lean_inc(v_binderName_1380_);
lean_dec_ref(v_e_1321_);
v___x_1393_ = l_Lean_Expr_lam___override(v_binderName_1380_, v_a_1385_, v_a_1387_, v_binderInfo_1383_);
if (v_isShared_1390_ == 0)
{
lean_ctor_set(v___x_1389_, 0, v___x_1393_);
v___x_1395_ = v___x_1389_;
goto v_reusejp_1394_;
}
else
{
lean_object* v_reuseFailAlloc_1396_; 
v_reuseFailAlloc_1396_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1396_, 0, v___x_1393_);
v___x_1395_ = v_reuseFailAlloc_1396_;
goto v_reusejp_1394_;
}
v_reusejp_1394_:
{
return v___x_1395_;
}
}
else
{
uint8_t v___x_1397_; 
v___x_1397_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_1383_, v_binderInfo_1383_);
if (v___x_1397_ == 0)
{
lean_object* v___x_1398_; lean_object* v___x_1400_; 
lean_inc(v_binderName_1380_);
lean_dec_ref(v_e_1321_);
v___x_1398_ = l_Lean_Expr_lam___override(v_binderName_1380_, v_a_1385_, v_a_1387_, v_binderInfo_1383_);
if (v_isShared_1390_ == 0)
{
lean_ctor_set(v___x_1389_, 0, v___x_1398_);
v___x_1400_ = v___x_1389_;
goto v_reusejp_1399_;
}
else
{
lean_object* v_reuseFailAlloc_1401_; 
v_reuseFailAlloc_1401_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1401_, 0, v___x_1398_);
v___x_1400_ = v_reuseFailAlloc_1401_;
goto v_reusejp_1399_;
}
v_reusejp_1399_:
{
return v___x_1400_;
}
}
else
{
lean_object* v___x_1403_; 
lean_dec(v_a_1387_);
lean_dec(v_a_1385_);
if (v_isShared_1390_ == 0)
{
lean_ctor_set(v___x_1389_, 0, v_e_1321_);
v___x_1403_ = v___x_1389_;
goto v_reusejp_1402_;
}
else
{
lean_object* v_reuseFailAlloc_1404_; 
v_reuseFailAlloc_1404_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1404_, 0, v_e_1321_);
v___x_1403_ = v_reuseFailAlloc_1404_;
goto v_reusejp_1402_;
}
v_reusejp_1402_:
{
return v___x_1403_;
}
}
}
}
}
}
else
{
lean_dec(v_a_1385_);
lean_dec_ref(v_e_1321_);
return v___x_1386_;
}
}
else
{
lean_dec_ref(v_e_1321_);
return v___x_1384_;
}
}
case 8:
{
lean_object* v_declName_1412_; lean_object* v_type_1413_; lean_object* v_value_1414_; lean_object* v_body_1415_; uint8_t v_nondep_1416_; lean_object* v___x_1417_; 
v_declName_1412_ = lean_ctor_get(v_e_1321_, 0);
v_type_1413_ = lean_ctor_get(v_e_1321_, 1);
v_value_1414_ = lean_ctor_get(v_e_1321_, 2);
v_body_1415_ = lean_ctor_get(v_e_1321_, 3);
v_nondep_1416_ = lean_ctor_get_uint8(v_e_1321_, sizeof(void*)*4 + 8);
lean_inc_ref(v_type_1413_);
v___x_1417_ = l_Lean_Meta_Closure_collectExprAux___lam__0(v_type_1413_, v_a_1322_, v_a_1323_, v_a_1324_, v_a_1325_, v_a_1326_, v_a_1327_);
if (lean_obj_tag(v___x_1417_) == 0)
{
lean_object* v_a_1418_; lean_object* v___x_1419_; 
v_a_1418_ = lean_ctor_get(v___x_1417_, 0);
lean_inc(v_a_1418_);
lean_dec_ref(v___x_1417_);
lean_inc_ref(v_value_1414_);
v___x_1419_ = l_Lean_Meta_Closure_collectExprAux___lam__0(v_value_1414_, v_a_1322_, v_a_1323_, v_a_1324_, v_a_1325_, v_a_1326_, v_a_1327_);
if (lean_obj_tag(v___x_1419_) == 0)
{
lean_object* v_a_1420_; lean_object* v___x_1421_; 
v_a_1420_ = lean_ctor_get(v___x_1419_, 0);
lean_inc(v_a_1420_);
lean_dec_ref(v___x_1419_);
lean_inc_ref(v_body_1415_);
v___x_1421_ = l_Lean_Meta_Closure_collectExprAux___lam__0(v_body_1415_, v_a_1322_, v_a_1323_, v_a_1324_, v_a_1325_, v_a_1326_, v_a_1327_);
if (lean_obj_tag(v___x_1421_) == 0)
{
lean_object* v_a_1422_; lean_object* v___x_1424_; uint8_t v_isShared_1425_; uint8_t v_isSharedCheck_1448_; 
v_a_1422_ = lean_ctor_get(v___x_1421_, 0);
v_isSharedCheck_1448_ = !lean_is_exclusive(v___x_1421_);
if (v_isSharedCheck_1448_ == 0)
{
v___x_1424_ = v___x_1421_;
v_isShared_1425_ = v_isSharedCheck_1448_;
goto v_resetjp_1423_;
}
else
{
lean_inc(v_a_1422_);
lean_dec(v___x_1421_);
v___x_1424_ = lean_box(0);
v_isShared_1425_ = v_isSharedCheck_1448_;
goto v_resetjp_1423_;
}
v_resetjp_1423_:
{
uint8_t v___y_1427_; size_t v___x_1442_; size_t v___x_1443_; uint8_t v___x_1444_; 
v___x_1442_ = lean_ptr_addr(v_type_1413_);
v___x_1443_ = lean_ptr_addr(v_a_1418_);
v___x_1444_ = lean_usize_dec_eq(v___x_1442_, v___x_1443_);
if (v___x_1444_ == 0)
{
v___y_1427_ = v___x_1444_;
goto v___jp_1426_;
}
else
{
size_t v___x_1445_; size_t v___x_1446_; uint8_t v___x_1447_; 
v___x_1445_ = lean_ptr_addr(v_value_1414_);
v___x_1446_ = lean_ptr_addr(v_a_1420_);
v___x_1447_ = lean_usize_dec_eq(v___x_1445_, v___x_1446_);
v___y_1427_ = v___x_1447_;
goto v___jp_1426_;
}
v___jp_1426_:
{
if (v___y_1427_ == 0)
{
lean_object* v___x_1428_; lean_object* v___x_1430_; 
lean_inc(v_declName_1412_);
lean_dec_ref(v_e_1321_);
v___x_1428_ = l_Lean_Expr_letE___override(v_declName_1412_, v_a_1418_, v_a_1420_, v_a_1422_, v_nondep_1416_);
if (v_isShared_1425_ == 0)
{
lean_ctor_set(v___x_1424_, 0, v___x_1428_);
v___x_1430_ = v___x_1424_;
goto v_reusejp_1429_;
}
else
{
lean_object* v_reuseFailAlloc_1431_; 
v_reuseFailAlloc_1431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1431_, 0, v___x_1428_);
v___x_1430_ = v_reuseFailAlloc_1431_;
goto v_reusejp_1429_;
}
v_reusejp_1429_:
{
return v___x_1430_;
}
}
else
{
size_t v___x_1432_; size_t v___x_1433_; uint8_t v___x_1434_; 
v___x_1432_ = lean_ptr_addr(v_body_1415_);
v___x_1433_ = lean_ptr_addr(v_a_1422_);
v___x_1434_ = lean_usize_dec_eq(v___x_1432_, v___x_1433_);
if (v___x_1434_ == 0)
{
lean_object* v___x_1435_; lean_object* v___x_1437_; 
lean_inc(v_declName_1412_);
lean_dec_ref(v_e_1321_);
v___x_1435_ = l_Lean_Expr_letE___override(v_declName_1412_, v_a_1418_, v_a_1420_, v_a_1422_, v_nondep_1416_);
if (v_isShared_1425_ == 0)
{
lean_ctor_set(v___x_1424_, 0, v___x_1435_);
v___x_1437_ = v___x_1424_;
goto v_reusejp_1436_;
}
else
{
lean_object* v_reuseFailAlloc_1438_; 
v_reuseFailAlloc_1438_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1438_, 0, v___x_1435_);
v___x_1437_ = v_reuseFailAlloc_1438_;
goto v_reusejp_1436_;
}
v_reusejp_1436_:
{
return v___x_1437_;
}
}
else
{
lean_object* v___x_1440_; 
lean_dec(v_a_1422_);
lean_dec(v_a_1420_);
lean_dec(v_a_1418_);
if (v_isShared_1425_ == 0)
{
lean_ctor_set(v___x_1424_, 0, v_e_1321_);
v___x_1440_ = v___x_1424_;
goto v_reusejp_1439_;
}
else
{
lean_object* v_reuseFailAlloc_1441_; 
v_reuseFailAlloc_1441_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1441_, 0, v_e_1321_);
v___x_1440_ = v_reuseFailAlloc_1441_;
goto v_reusejp_1439_;
}
v_reusejp_1439_:
{
return v___x_1440_;
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
lean_dec_ref(v_e_1321_);
return v___x_1421_;
}
}
else
{
lean_dec(v_a_1418_);
lean_dec_ref(v_e_1321_);
return v___x_1419_;
}
}
else
{
lean_dec_ref(v_e_1321_);
return v___x_1417_;
}
}
case 5:
{
lean_object* v_fn_1449_; lean_object* v_arg_1450_; lean_object* v___x_1451_; 
v_fn_1449_ = lean_ctor_get(v_e_1321_, 0);
v_arg_1450_ = lean_ctor_get(v_e_1321_, 1);
lean_inc_ref(v_fn_1449_);
v___x_1451_ = l_Lean_Meta_Closure_collectExprAux___lam__0(v_fn_1449_, v_a_1322_, v_a_1323_, v_a_1324_, v_a_1325_, v_a_1326_, v_a_1327_);
if (lean_obj_tag(v___x_1451_) == 0)
{
lean_object* v_a_1452_; lean_object* v___x_1453_; 
v_a_1452_ = lean_ctor_get(v___x_1451_, 0);
lean_inc(v_a_1452_);
lean_dec_ref(v___x_1451_);
lean_inc_ref(v_arg_1450_);
v___x_1453_ = l_Lean_Meta_Closure_collectExprAux___lam__0(v_arg_1450_, v_a_1322_, v_a_1323_, v_a_1324_, v_a_1325_, v_a_1326_, v_a_1327_);
if (lean_obj_tag(v___x_1453_) == 0)
{
lean_object* v_a_1454_; lean_object* v___x_1456_; uint8_t v_isShared_1457_; uint8_t v_isSharedCheck_1473_; 
v_a_1454_ = lean_ctor_get(v___x_1453_, 0);
v_isSharedCheck_1473_ = !lean_is_exclusive(v___x_1453_);
if (v_isSharedCheck_1473_ == 0)
{
v___x_1456_ = v___x_1453_;
v_isShared_1457_ = v_isSharedCheck_1473_;
goto v_resetjp_1455_;
}
else
{
lean_inc(v_a_1454_);
lean_dec(v___x_1453_);
v___x_1456_ = lean_box(0);
v_isShared_1457_ = v_isSharedCheck_1473_;
goto v_resetjp_1455_;
}
v_resetjp_1455_:
{
uint8_t v___y_1459_; size_t v___x_1467_; size_t v___x_1468_; uint8_t v___x_1469_; 
v___x_1467_ = lean_ptr_addr(v_fn_1449_);
v___x_1468_ = lean_ptr_addr(v_a_1452_);
v___x_1469_ = lean_usize_dec_eq(v___x_1467_, v___x_1468_);
if (v___x_1469_ == 0)
{
v___y_1459_ = v___x_1469_;
goto v___jp_1458_;
}
else
{
size_t v___x_1470_; size_t v___x_1471_; uint8_t v___x_1472_; 
v___x_1470_ = lean_ptr_addr(v_arg_1450_);
v___x_1471_ = lean_ptr_addr(v_a_1454_);
v___x_1472_ = lean_usize_dec_eq(v___x_1470_, v___x_1471_);
v___y_1459_ = v___x_1472_;
goto v___jp_1458_;
}
v___jp_1458_:
{
if (v___y_1459_ == 0)
{
lean_object* v___x_1460_; lean_object* v___x_1462_; 
lean_dec_ref(v_e_1321_);
v___x_1460_ = l_Lean_Expr_app___override(v_a_1452_, v_a_1454_);
if (v_isShared_1457_ == 0)
{
lean_ctor_set(v___x_1456_, 0, v___x_1460_);
v___x_1462_ = v___x_1456_;
goto v_reusejp_1461_;
}
else
{
lean_object* v_reuseFailAlloc_1463_; 
v_reuseFailAlloc_1463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1463_, 0, v___x_1460_);
v___x_1462_ = v_reuseFailAlloc_1463_;
goto v_reusejp_1461_;
}
v_reusejp_1461_:
{
return v___x_1462_;
}
}
else
{
lean_object* v___x_1465_; 
lean_dec(v_a_1454_);
lean_dec(v_a_1452_);
if (v_isShared_1457_ == 0)
{
lean_ctor_set(v___x_1456_, 0, v_e_1321_);
v___x_1465_ = v___x_1456_;
goto v_reusejp_1464_;
}
else
{
lean_object* v_reuseFailAlloc_1466_; 
v_reuseFailAlloc_1466_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1466_, 0, v_e_1321_);
v___x_1465_ = v_reuseFailAlloc_1466_;
goto v_reusejp_1464_;
}
v_reusejp_1464_:
{
return v___x_1465_;
}
}
}
}
}
else
{
lean_dec(v_a_1452_);
lean_dec_ref(v_e_1321_);
return v___x_1453_;
}
}
else
{
lean_dec_ref(v_e_1321_);
return v___x_1451_;
}
}
case 10:
{
lean_object* v_data_1474_; lean_object* v_expr_1475_; lean_object* v___x_1476_; 
v_data_1474_ = lean_ctor_get(v_e_1321_, 0);
v_expr_1475_ = lean_ctor_get(v_e_1321_, 1);
lean_inc_ref(v_expr_1475_);
v___x_1476_ = l_Lean_Meta_Closure_collectExprAux___lam__0(v_expr_1475_, v_a_1322_, v_a_1323_, v_a_1324_, v_a_1325_, v_a_1326_, v_a_1327_);
if (lean_obj_tag(v___x_1476_) == 0)
{
lean_object* v_a_1477_; lean_object* v___x_1479_; uint8_t v_isShared_1480_; uint8_t v_isSharedCheck_1491_; 
v_a_1477_ = lean_ctor_get(v___x_1476_, 0);
v_isSharedCheck_1491_ = !lean_is_exclusive(v___x_1476_);
if (v_isSharedCheck_1491_ == 0)
{
v___x_1479_ = v___x_1476_;
v_isShared_1480_ = v_isSharedCheck_1491_;
goto v_resetjp_1478_;
}
else
{
lean_inc(v_a_1477_);
lean_dec(v___x_1476_);
v___x_1479_ = lean_box(0);
v_isShared_1480_ = v_isSharedCheck_1491_;
goto v_resetjp_1478_;
}
v_resetjp_1478_:
{
size_t v___x_1481_; size_t v___x_1482_; uint8_t v___x_1483_; 
v___x_1481_ = lean_ptr_addr(v_expr_1475_);
v___x_1482_ = lean_ptr_addr(v_a_1477_);
v___x_1483_ = lean_usize_dec_eq(v___x_1481_, v___x_1482_);
if (v___x_1483_ == 0)
{
lean_object* v___x_1484_; lean_object* v___x_1486_; 
lean_inc(v_data_1474_);
lean_dec_ref(v_e_1321_);
v___x_1484_ = l_Lean_Expr_mdata___override(v_data_1474_, v_a_1477_);
if (v_isShared_1480_ == 0)
{
lean_ctor_set(v___x_1479_, 0, v___x_1484_);
v___x_1486_ = v___x_1479_;
goto v_reusejp_1485_;
}
else
{
lean_object* v_reuseFailAlloc_1487_; 
v_reuseFailAlloc_1487_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1487_, 0, v___x_1484_);
v___x_1486_ = v_reuseFailAlloc_1487_;
goto v_reusejp_1485_;
}
v_reusejp_1485_:
{
return v___x_1486_;
}
}
else
{
lean_object* v___x_1489_; 
lean_dec(v_a_1477_);
if (v_isShared_1480_ == 0)
{
lean_ctor_set(v___x_1479_, 0, v_e_1321_);
v___x_1489_ = v___x_1479_;
goto v_reusejp_1488_;
}
else
{
lean_object* v_reuseFailAlloc_1490_; 
v_reuseFailAlloc_1490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1490_, 0, v_e_1321_);
v___x_1489_ = v_reuseFailAlloc_1490_;
goto v_reusejp_1488_;
}
v_reusejp_1488_:
{
return v___x_1489_;
}
}
}
}
else
{
lean_dec_ref(v_e_1321_);
return v___x_1476_;
}
}
case 3:
{
lean_object* v_u_1492_; lean_object* v___x_1493_; 
v_u_1492_ = lean_ctor_get(v_e_1321_, 0);
lean_inc(v_u_1492_);
v___x_1493_ = l_Lean_Meta_Closure_collectLevel___redArg(v_u_1492_, v_a_1323_);
if (lean_obj_tag(v___x_1493_) == 0)
{
lean_object* v_a_1494_; lean_object* v___x_1496_; uint8_t v_isShared_1497_; uint8_t v_isSharedCheck_1508_; 
v_a_1494_ = lean_ctor_get(v___x_1493_, 0);
v_isSharedCheck_1508_ = !lean_is_exclusive(v___x_1493_);
if (v_isSharedCheck_1508_ == 0)
{
v___x_1496_ = v___x_1493_;
v_isShared_1497_ = v_isSharedCheck_1508_;
goto v_resetjp_1495_;
}
else
{
lean_inc(v_a_1494_);
lean_dec(v___x_1493_);
v___x_1496_ = lean_box(0);
v_isShared_1497_ = v_isSharedCheck_1508_;
goto v_resetjp_1495_;
}
v_resetjp_1495_:
{
size_t v___x_1498_; size_t v___x_1499_; uint8_t v___x_1500_; 
v___x_1498_ = lean_ptr_addr(v_u_1492_);
v___x_1499_ = lean_ptr_addr(v_a_1494_);
v___x_1500_ = lean_usize_dec_eq(v___x_1498_, v___x_1499_);
if (v___x_1500_ == 0)
{
lean_object* v___x_1501_; lean_object* v___x_1503_; 
lean_dec_ref(v_e_1321_);
v___x_1501_ = l_Lean_Expr_sort___override(v_a_1494_);
if (v_isShared_1497_ == 0)
{
lean_ctor_set(v___x_1496_, 0, v___x_1501_);
v___x_1503_ = v___x_1496_;
goto v_reusejp_1502_;
}
else
{
lean_object* v_reuseFailAlloc_1504_; 
v_reuseFailAlloc_1504_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1504_, 0, v___x_1501_);
v___x_1503_ = v_reuseFailAlloc_1504_;
goto v_reusejp_1502_;
}
v_reusejp_1502_:
{
return v___x_1503_;
}
}
else
{
lean_object* v___x_1506_; 
lean_dec(v_a_1494_);
if (v_isShared_1497_ == 0)
{
lean_ctor_set(v___x_1496_, 0, v_e_1321_);
v___x_1506_ = v___x_1496_;
goto v_reusejp_1505_;
}
else
{
lean_object* v_reuseFailAlloc_1507_; 
v_reuseFailAlloc_1507_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1507_, 0, v_e_1321_);
v___x_1506_ = v_reuseFailAlloc_1507_;
goto v_reusejp_1505_;
}
v_reusejp_1505_:
{
return v___x_1506_;
}
}
}
}
else
{
lean_object* v_a_1509_; lean_object* v___x_1511_; uint8_t v_isShared_1512_; uint8_t v_isSharedCheck_1516_; 
lean_dec_ref(v_e_1321_);
v_a_1509_ = lean_ctor_get(v___x_1493_, 0);
v_isSharedCheck_1516_ = !lean_is_exclusive(v___x_1493_);
if (v_isSharedCheck_1516_ == 0)
{
v___x_1511_ = v___x_1493_;
v_isShared_1512_ = v_isSharedCheck_1516_;
goto v_resetjp_1510_;
}
else
{
lean_inc(v_a_1509_);
lean_dec(v___x_1493_);
v___x_1511_ = lean_box(0);
v_isShared_1512_ = v_isSharedCheck_1516_;
goto v_resetjp_1510_;
}
v_resetjp_1510_:
{
lean_object* v___x_1514_; 
if (v_isShared_1512_ == 0)
{
v___x_1514_ = v___x_1511_;
goto v_reusejp_1513_;
}
else
{
lean_object* v_reuseFailAlloc_1515_; 
v_reuseFailAlloc_1515_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1515_, 0, v_a_1509_);
v___x_1514_ = v_reuseFailAlloc_1515_;
goto v_reusejp_1513_;
}
v_reusejp_1513_:
{
return v___x_1514_;
}
}
}
}
case 4:
{
lean_object* v_declName_1517_; lean_object* v_us_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; 
v_declName_1517_ = lean_ctor_get(v_e_1321_, 0);
v_us_1518_ = lean_ctor_get(v_e_1321_, 1);
v___x_1519_ = lean_box(0);
lean_inc(v_us_1518_);
v___x_1520_ = l_List_mapM_loop___at___00Lean_Meta_Closure_collectExprAux_spec__2___redArg(v_us_1518_, v___x_1519_, v_a_1323_);
if (lean_obj_tag(v___x_1520_) == 0)
{
lean_object* v_a_1521_; lean_object* v___x_1523_; uint8_t v_isShared_1524_; uint8_t v_isSharedCheck_1533_; 
v_a_1521_ = lean_ctor_get(v___x_1520_, 0);
v_isSharedCheck_1533_ = !lean_is_exclusive(v___x_1520_);
if (v_isSharedCheck_1533_ == 0)
{
v___x_1523_ = v___x_1520_;
v_isShared_1524_ = v_isSharedCheck_1533_;
goto v_resetjp_1522_;
}
else
{
lean_inc(v_a_1521_);
lean_dec(v___x_1520_);
v___x_1523_ = lean_box(0);
v_isShared_1524_ = v_isSharedCheck_1533_;
goto v_resetjp_1522_;
}
v_resetjp_1522_:
{
uint8_t v___x_1525_; 
v___x_1525_ = l_ptrEqList___redArg(v_us_1518_, v_a_1521_);
if (v___x_1525_ == 0)
{
lean_object* v___x_1526_; lean_object* v___x_1528_; 
lean_inc(v_declName_1517_);
lean_dec_ref(v_e_1321_);
v___x_1526_ = l_Lean_Expr_const___override(v_declName_1517_, v_a_1521_);
if (v_isShared_1524_ == 0)
{
lean_ctor_set(v___x_1523_, 0, v___x_1526_);
v___x_1528_ = v___x_1523_;
goto v_reusejp_1527_;
}
else
{
lean_object* v_reuseFailAlloc_1529_; 
v_reuseFailAlloc_1529_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1529_, 0, v___x_1526_);
v___x_1528_ = v_reuseFailAlloc_1529_;
goto v_reusejp_1527_;
}
v_reusejp_1527_:
{
return v___x_1528_;
}
}
else
{
lean_object* v___x_1531_; 
lean_dec(v_a_1521_);
if (v_isShared_1524_ == 0)
{
lean_ctor_set(v___x_1523_, 0, v_e_1321_);
v___x_1531_ = v___x_1523_;
goto v_reusejp_1530_;
}
else
{
lean_object* v_reuseFailAlloc_1532_; 
v_reuseFailAlloc_1532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1532_, 0, v_e_1321_);
v___x_1531_ = v_reuseFailAlloc_1532_;
goto v_reusejp_1530_;
}
v_reusejp_1530_:
{
return v___x_1531_;
}
}
}
}
else
{
lean_object* v_a_1534_; lean_object* v___x_1536_; uint8_t v_isShared_1537_; uint8_t v_isSharedCheck_1541_; 
lean_dec_ref(v_e_1321_);
v_a_1534_ = lean_ctor_get(v___x_1520_, 0);
v_isSharedCheck_1541_ = !lean_is_exclusive(v___x_1520_);
if (v_isSharedCheck_1541_ == 0)
{
v___x_1536_ = v___x_1520_;
v_isShared_1537_ = v_isSharedCheck_1541_;
goto v_resetjp_1535_;
}
else
{
lean_inc(v_a_1534_);
lean_dec(v___x_1520_);
v___x_1536_ = lean_box(0);
v_isShared_1537_ = v_isSharedCheck_1541_;
goto v_resetjp_1535_;
}
v_resetjp_1535_:
{
lean_object* v___x_1539_; 
if (v_isShared_1537_ == 0)
{
v___x_1539_ = v___x_1536_;
goto v_reusejp_1538_;
}
else
{
lean_object* v_reuseFailAlloc_1540_; 
v_reuseFailAlloc_1540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1540_, 0, v_a_1534_);
v___x_1539_ = v_reuseFailAlloc_1540_;
goto v_reusejp_1538_;
}
v_reusejp_1538_:
{
return v___x_1539_;
}
}
}
}
case 2:
{
lean_object* v_mvarId_1542_; lean_object* v___x_1543_; 
v_mvarId_1542_ = lean_ctor_get(v_e_1321_, 0);
lean_inc(v_mvarId_1542_);
v___x_1543_ = l_Lean_MVarId_getDecl(v_mvarId_1542_, v_a_1324_, v_a_1325_, v_a_1326_, v_a_1327_);
if (lean_obj_tag(v___x_1543_) == 0)
{
lean_object* v_a_1544_; lean_object* v_type_1545_; lean_object* v___x_1546_; 
v_a_1544_ = lean_ctor_get(v___x_1543_, 0);
lean_inc(v_a_1544_);
lean_dec_ref(v___x_1543_);
v_type_1545_ = lean_ctor_get(v_a_1544_, 2);
lean_inc_ref_n(v_type_1545_, 2);
lean_dec(v_a_1544_);
v___x_1546_ = l_Lean_Meta_Closure_preprocess(v_type_1545_, v_a_1322_, v_a_1323_, v_a_1324_, v_a_1325_, v_a_1326_, v_a_1327_);
if (lean_obj_tag(v___x_1546_) == 0)
{
lean_object* v_a_1547_; lean_object* v___x_1548_; 
v_a_1547_ = lean_ctor_get(v___x_1546_, 0);
lean_inc(v_a_1547_);
lean_dec_ref(v___x_1546_);
v___x_1548_ = l_Lean_Meta_Closure_collectExprAux___lam__0(v_a_1547_, v_a_1322_, v_a_1323_, v_a_1324_, v_a_1325_, v_a_1326_, v_a_1327_);
if (lean_obj_tag(v___x_1548_) == 0)
{
lean_object* v_a_1549_; lean_object* v___x_1550_; 
v_a_1549_ = lean_ctor_get(v___x_1548_, 0);
lean_inc(v_a_1549_);
lean_dec_ref(v___x_1548_);
v___x_1550_ = l_Lean_mkFreshFVarId___at___00Lean_Meta_Closure_collectExprAux_spec__3(v_a_1322_, v_a_1323_, v_a_1324_, v_a_1325_, v_a_1326_, v_a_1327_);
if (lean_obj_tag(v___x_1550_) == 0)
{
lean_object* v_a_1551_; lean_object* v___x_1552_; 
v_a_1551_ = lean_ctor_get(v___x_1550_, 0);
lean_inc(v_a_1551_);
lean_dec_ref(v___x_1550_);
v___x_1552_ = l_Lean_Meta_Closure_mkNextUserName___redArg(v_a_1323_);
if (lean_obj_tag(v___x_1552_) == 0)
{
lean_object* v_a_1553_; lean_object* v___x_1555_; uint8_t v_isShared_1556_; uint8_t v_isSharedCheck_1615_; 
v_a_1553_ = lean_ctor_get(v___x_1552_, 0);
v_isSharedCheck_1615_ = !lean_is_exclusive(v___x_1552_);
if (v_isSharedCheck_1615_ == 0)
{
v___x_1555_ = v___x_1552_;
v_isShared_1556_ = v_isSharedCheck_1615_;
goto v_resetjp_1554_;
}
else
{
lean_inc(v_a_1553_);
lean_dec(v___x_1552_);
v___x_1555_ = lean_box(0);
v_isShared_1556_ = v_isSharedCheck_1615_;
goto v_resetjp_1554_;
}
v_resetjp_1554_:
{
lean_object* v_e_x27_1558_; lean_object* v___y_1559_; lean_object* v___x_1591_; 
v___x_1591_ = l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__4___redArg(v_mvarId_1542_, v_a_1325_);
if (lean_obj_tag(v___x_1591_) == 0)
{
lean_object* v_a_1592_; 
v_a_1592_ = lean_ctor_get(v___x_1591_, 0);
lean_inc(v_a_1592_);
lean_dec_ref(v___x_1591_);
if (lean_obj_tag(v_a_1592_) == 1)
{
lean_object* v_val_1593_; lean_object* v___x_1595_; uint8_t v_isShared_1596_; uint8_t v_isSharedCheck_1606_; 
v_val_1593_ = lean_ctor_get(v_a_1592_, 0);
v_isSharedCheck_1606_ = !lean_is_exclusive(v_a_1592_);
if (v_isSharedCheck_1606_ == 0)
{
v___x_1595_ = v_a_1592_;
v_isShared_1596_ = v_isSharedCheck_1606_;
goto v_resetjp_1594_;
}
else
{
lean_inc(v_val_1593_);
lean_dec(v_a_1592_);
v___x_1595_ = lean_box(0);
v_isShared_1596_ = v_isSharedCheck_1606_;
goto v_resetjp_1594_;
}
v_resetjp_1594_:
{
lean_object* v_fvars_1597_; lean_object* v___f_1598_; lean_object* v___x_1599_; lean_object* v___x_1601_; 
v_fvars_1597_ = lean_ctor_get(v_val_1593_, 0);
lean_inc_ref(v_fvars_1597_);
lean_dec(v_val_1593_);
v___f_1598_ = lean_alloc_closure((void*)(l_Lean_Meta_Closure_collectExprAux___lam__1___boxed), 10, 1);
lean_closure_set(v___f_1598_, 0, v_e_1321_);
v___x_1599_ = lean_array_get_size(v_fvars_1597_);
lean_dec_ref(v_fvars_1597_);
if (v_isShared_1596_ == 0)
{
lean_ctor_set(v___x_1595_, 0, v___x_1599_);
v___x_1601_ = v___x_1595_;
goto v_reusejp_1600_;
}
else
{
lean_object* v_reuseFailAlloc_1605_; 
v_reuseFailAlloc_1605_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1605_, 0, v___x_1599_);
v___x_1601_ = v_reuseFailAlloc_1605_;
goto v_reusejp_1600_;
}
v_reusejp_1600_:
{
uint8_t v___x_1602_; lean_object* v___x_1603_; 
v___x_1602_ = 0;
v___x_1603_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Closure_collectExprAux_spec__5___redArg(v_type_1545_, v___x_1601_, v___f_1598_, v___x_1602_, v___x_1602_, v_a_1322_, v_a_1323_, v_a_1324_, v_a_1325_, v_a_1326_, v_a_1327_);
if (lean_obj_tag(v___x_1603_) == 0)
{
lean_object* v_a_1604_; 
v_a_1604_ = lean_ctor_get(v___x_1603_, 0);
lean_inc(v_a_1604_);
lean_dec_ref(v___x_1603_);
v_e_x27_1558_ = v_a_1604_;
v___y_1559_ = v_a_1323_;
goto v___jp_1557_;
}
else
{
lean_del_object(v___x_1555_);
lean_dec(v_a_1553_);
lean_dec(v_a_1551_);
lean_dec(v_a_1549_);
return v___x_1603_;
}
}
}
}
else
{
lean_dec(v_a_1592_);
lean_dec_ref(v_type_1545_);
v_e_x27_1558_ = v_e_1321_;
v___y_1559_ = v_a_1323_;
goto v___jp_1557_;
}
}
else
{
lean_object* v_a_1607_; lean_object* v___x_1609_; uint8_t v_isShared_1610_; uint8_t v_isSharedCheck_1614_; 
lean_del_object(v___x_1555_);
lean_dec(v_a_1553_);
lean_dec(v_a_1551_);
lean_dec(v_a_1549_);
lean_dec_ref(v_type_1545_);
lean_dec_ref(v_e_1321_);
v_a_1607_ = lean_ctor_get(v___x_1591_, 0);
v_isSharedCheck_1614_ = !lean_is_exclusive(v___x_1591_);
if (v_isSharedCheck_1614_ == 0)
{
v___x_1609_ = v___x_1591_;
v_isShared_1610_ = v_isSharedCheck_1614_;
goto v_resetjp_1608_;
}
else
{
lean_inc(v_a_1607_);
lean_dec(v___x_1591_);
v___x_1609_ = lean_box(0);
v_isShared_1610_ = v_isSharedCheck_1614_;
goto v_resetjp_1608_;
}
v_resetjp_1608_:
{
lean_object* v___x_1612_; 
if (v_isShared_1610_ == 0)
{
v___x_1612_ = v___x_1609_;
goto v_reusejp_1611_;
}
else
{
lean_object* v_reuseFailAlloc_1613_; 
v_reuseFailAlloc_1613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1613_, 0, v_a_1607_);
v___x_1612_ = v_reuseFailAlloc_1613_;
goto v_reusejp_1611_;
}
v_reusejp_1611_:
{
return v___x_1612_;
}
}
}
v___jp_1557_:
{
lean_object* v___x_1560_; lean_object* v_visitedLevel_1561_; lean_object* v_visitedExpr_1562_; lean_object* v_levelParams_1563_; lean_object* v_nextLevelIdx_1564_; lean_object* v_levelArgs_1565_; lean_object* v_newLocalDecls_1566_; lean_object* v_newLocalDeclsForMVars_1567_; lean_object* v_newLetDecls_1568_; lean_object* v_nextExprIdx_1569_; lean_object* v_exprMVarArgs_1570_; lean_object* v_exprFVarArgs_1571_; lean_object* v_toProcess_1572_; lean_object* v___x_1574_; uint8_t v_isShared_1575_; uint8_t v_isSharedCheck_1590_; 
v___x_1560_ = lean_st_ref_take(v___y_1559_);
v_visitedLevel_1561_ = lean_ctor_get(v___x_1560_, 0);
v_visitedExpr_1562_ = lean_ctor_get(v___x_1560_, 1);
v_levelParams_1563_ = lean_ctor_get(v___x_1560_, 2);
v_nextLevelIdx_1564_ = lean_ctor_get(v___x_1560_, 3);
v_levelArgs_1565_ = lean_ctor_get(v___x_1560_, 4);
v_newLocalDecls_1566_ = lean_ctor_get(v___x_1560_, 5);
v_newLocalDeclsForMVars_1567_ = lean_ctor_get(v___x_1560_, 6);
v_newLetDecls_1568_ = lean_ctor_get(v___x_1560_, 7);
v_nextExprIdx_1569_ = lean_ctor_get(v___x_1560_, 8);
v_exprMVarArgs_1570_ = lean_ctor_get(v___x_1560_, 9);
v_exprFVarArgs_1571_ = lean_ctor_get(v___x_1560_, 10);
v_toProcess_1572_ = lean_ctor_get(v___x_1560_, 11);
v_isSharedCheck_1590_ = !lean_is_exclusive(v___x_1560_);
if (v_isSharedCheck_1590_ == 0)
{
v___x_1574_ = v___x_1560_;
v_isShared_1575_ = v_isSharedCheck_1590_;
goto v_resetjp_1573_;
}
else
{
lean_inc(v_toProcess_1572_);
lean_inc(v_exprFVarArgs_1571_);
lean_inc(v_exprMVarArgs_1570_);
lean_inc(v_nextExprIdx_1569_);
lean_inc(v_newLetDecls_1568_);
lean_inc(v_newLocalDeclsForMVars_1567_);
lean_inc(v_newLocalDecls_1566_);
lean_inc(v_levelArgs_1565_);
lean_inc(v_nextLevelIdx_1564_);
lean_inc(v_levelParams_1563_);
lean_inc(v_visitedExpr_1562_);
lean_inc(v_visitedLevel_1561_);
lean_dec(v___x_1560_);
v___x_1574_ = lean_box(0);
v_isShared_1575_ = v_isSharedCheck_1590_;
goto v_resetjp_1573_;
}
v_resetjp_1573_:
{
lean_object* v___x_1576_; uint8_t v___x_1577_; uint8_t v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1583_; 
v___x_1576_ = lean_unsigned_to_nat(0u);
v___x_1577_ = 0;
v___x_1578_ = 0;
lean_inc(v_a_1551_);
v___x_1579_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_1579_, 0, v___x_1576_);
lean_ctor_set(v___x_1579_, 1, v_a_1551_);
lean_ctor_set(v___x_1579_, 2, v_a_1553_);
lean_ctor_set(v___x_1579_, 3, v_a_1549_);
lean_ctor_set_uint8(v___x_1579_, sizeof(void*)*4, v___x_1577_);
lean_ctor_set_uint8(v___x_1579_, sizeof(void*)*4 + 1, v___x_1578_);
v___x_1580_ = lean_array_push(v_newLocalDeclsForMVars_1567_, v___x_1579_);
v___x_1581_ = lean_array_push(v_exprMVarArgs_1570_, v_e_x27_1558_);
if (v_isShared_1575_ == 0)
{
lean_ctor_set(v___x_1574_, 9, v___x_1581_);
lean_ctor_set(v___x_1574_, 6, v___x_1580_);
v___x_1583_ = v___x_1574_;
goto v_reusejp_1582_;
}
else
{
lean_object* v_reuseFailAlloc_1589_; 
v_reuseFailAlloc_1589_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_1589_, 0, v_visitedLevel_1561_);
lean_ctor_set(v_reuseFailAlloc_1589_, 1, v_visitedExpr_1562_);
lean_ctor_set(v_reuseFailAlloc_1589_, 2, v_levelParams_1563_);
lean_ctor_set(v_reuseFailAlloc_1589_, 3, v_nextLevelIdx_1564_);
lean_ctor_set(v_reuseFailAlloc_1589_, 4, v_levelArgs_1565_);
lean_ctor_set(v_reuseFailAlloc_1589_, 5, v_newLocalDecls_1566_);
lean_ctor_set(v_reuseFailAlloc_1589_, 6, v___x_1580_);
lean_ctor_set(v_reuseFailAlloc_1589_, 7, v_newLetDecls_1568_);
lean_ctor_set(v_reuseFailAlloc_1589_, 8, v_nextExprIdx_1569_);
lean_ctor_set(v_reuseFailAlloc_1589_, 9, v___x_1581_);
lean_ctor_set(v_reuseFailAlloc_1589_, 10, v_exprFVarArgs_1571_);
lean_ctor_set(v_reuseFailAlloc_1589_, 11, v_toProcess_1572_);
v___x_1583_ = v_reuseFailAlloc_1589_;
goto v_reusejp_1582_;
}
v_reusejp_1582_:
{
lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1587_; 
v___x_1584_ = lean_st_ref_set(v___y_1559_, v___x_1583_);
v___x_1585_ = l_Lean_mkFVar(v_a_1551_);
if (v_isShared_1556_ == 0)
{
lean_ctor_set(v___x_1555_, 0, v___x_1585_);
v___x_1587_ = v___x_1555_;
goto v_reusejp_1586_;
}
else
{
lean_object* v_reuseFailAlloc_1588_; 
v_reuseFailAlloc_1588_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1588_, 0, v___x_1585_);
v___x_1587_ = v_reuseFailAlloc_1588_;
goto v_reusejp_1586_;
}
v_reusejp_1586_:
{
return v___x_1587_;
}
}
}
}
}
}
else
{
lean_object* v_a_1616_; lean_object* v___x_1618_; uint8_t v_isShared_1619_; uint8_t v_isSharedCheck_1623_; 
lean_dec(v_a_1551_);
lean_dec(v_a_1549_);
lean_dec_ref(v_type_1545_);
lean_dec_ref(v_e_1321_);
v_a_1616_ = lean_ctor_get(v___x_1552_, 0);
v_isSharedCheck_1623_ = !lean_is_exclusive(v___x_1552_);
if (v_isSharedCheck_1623_ == 0)
{
v___x_1618_ = v___x_1552_;
v_isShared_1619_ = v_isSharedCheck_1623_;
goto v_resetjp_1617_;
}
else
{
lean_inc(v_a_1616_);
lean_dec(v___x_1552_);
v___x_1618_ = lean_box(0);
v_isShared_1619_ = v_isSharedCheck_1623_;
goto v_resetjp_1617_;
}
v_resetjp_1617_:
{
lean_object* v___x_1621_; 
if (v_isShared_1619_ == 0)
{
v___x_1621_ = v___x_1618_;
goto v_reusejp_1620_;
}
else
{
lean_object* v_reuseFailAlloc_1622_; 
v_reuseFailAlloc_1622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1622_, 0, v_a_1616_);
v___x_1621_ = v_reuseFailAlloc_1622_;
goto v_reusejp_1620_;
}
v_reusejp_1620_:
{
return v___x_1621_;
}
}
}
}
else
{
lean_object* v_a_1624_; lean_object* v___x_1626_; uint8_t v_isShared_1627_; uint8_t v_isSharedCheck_1631_; 
lean_dec(v_a_1549_);
lean_dec_ref(v_type_1545_);
lean_dec_ref(v_e_1321_);
v_a_1624_ = lean_ctor_get(v___x_1550_, 0);
v_isSharedCheck_1631_ = !lean_is_exclusive(v___x_1550_);
if (v_isSharedCheck_1631_ == 0)
{
v___x_1626_ = v___x_1550_;
v_isShared_1627_ = v_isSharedCheck_1631_;
goto v_resetjp_1625_;
}
else
{
lean_inc(v_a_1624_);
lean_dec(v___x_1550_);
v___x_1626_ = lean_box(0);
v_isShared_1627_ = v_isSharedCheck_1631_;
goto v_resetjp_1625_;
}
v_resetjp_1625_:
{
lean_object* v___x_1629_; 
if (v_isShared_1627_ == 0)
{
v___x_1629_ = v___x_1626_;
goto v_reusejp_1628_;
}
else
{
lean_object* v_reuseFailAlloc_1630_; 
v_reuseFailAlloc_1630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1630_, 0, v_a_1624_);
v___x_1629_ = v_reuseFailAlloc_1630_;
goto v_reusejp_1628_;
}
v_reusejp_1628_:
{
return v___x_1629_;
}
}
}
}
else
{
lean_dec_ref(v_type_1545_);
lean_dec_ref(v_e_1321_);
return v___x_1548_;
}
}
else
{
lean_dec_ref(v_type_1545_);
lean_dec_ref(v_e_1321_);
return v___x_1546_;
}
}
else
{
lean_object* v_a_1632_; lean_object* v___x_1634_; uint8_t v_isShared_1635_; uint8_t v_isSharedCheck_1639_; 
lean_dec_ref(v_e_1321_);
v_a_1632_ = lean_ctor_get(v___x_1543_, 0);
v_isSharedCheck_1639_ = !lean_is_exclusive(v___x_1543_);
if (v_isSharedCheck_1639_ == 0)
{
v___x_1634_ = v___x_1543_;
v_isShared_1635_ = v_isSharedCheck_1639_;
goto v_resetjp_1633_;
}
else
{
lean_inc(v_a_1632_);
lean_dec(v___x_1543_);
v___x_1634_ = lean_box(0);
v_isShared_1635_ = v_isSharedCheck_1639_;
goto v_resetjp_1633_;
}
v_resetjp_1633_:
{
lean_object* v___x_1637_; 
if (v_isShared_1635_ == 0)
{
v___x_1637_ = v___x_1634_;
goto v_reusejp_1636_;
}
else
{
lean_object* v_reuseFailAlloc_1638_; 
v_reuseFailAlloc_1638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1638_, 0, v_a_1632_);
v___x_1637_ = v_reuseFailAlloc_1638_;
goto v_reusejp_1636_;
}
v_reusejp_1636_:
{
return v___x_1637_;
}
}
}
}
case 1:
{
lean_object* v_fvarId_1640_; uint8_t v___x_1641_; lean_object* v___x_1642_; 
v_fvarId_1640_ = lean_ctor_get(v_e_1321_, 0);
lean_inc_n(v_fvarId_1640_, 2);
lean_dec_ref(v_e_1321_);
v___x_1641_ = 0;
v___x_1642_ = l_Lean_FVarId_getValue_x3f___redArg(v_fvarId_1640_, v___x_1641_, v_a_1324_, v_a_1326_, v_a_1327_);
if (lean_obj_tag(v___x_1642_) == 0)
{
lean_object* v_a_1643_; uint8_t v___y_1645_; lean_object* v___y_1646_; lean_object* v___y_1647_; lean_object* v___y_1648_; lean_object* v___y_1649_; lean_object* v___y_1650_; 
v_a_1643_ = lean_ctor_get(v___x_1642_, 0);
lean_inc(v_a_1643_);
lean_dec_ref(v___x_1642_);
if (v_a_1322_ == 1)
{
if (lean_obj_tag(v_a_1643_) == 1)
{
lean_object* v_val_1680_; lean_object* v___x_1681_; 
lean_dec(v_fvarId_1640_);
v_val_1680_ = lean_ctor_get(v_a_1643_, 0);
lean_inc(v_val_1680_);
lean_dec_ref(v_a_1643_);
v___x_1681_ = l_Lean_Meta_Closure_preprocess(v_val_1680_, v_a_1322_, v_a_1323_, v_a_1324_, v_a_1325_, v_a_1326_, v_a_1327_);
if (lean_obj_tag(v___x_1681_) == 0)
{
lean_object* v_a_1682_; lean_object* v___x_1683_; 
v_a_1682_ = lean_ctor_get(v___x_1681_, 0);
lean_inc(v_a_1682_);
lean_dec_ref(v___x_1681_);
v___x_1683_ = l_Lean_Meta_Closure_collectExprAux___lam__0(v_a_1682_, v_a_1322_, v_a_1323_, v_a_1324_, v_a_1325_, v_a_1326_, v_a_1327_);
return v___x_1683_;
}
else
{
return v___x_1681_;
}
}
else
{
lean_dec(v_a_1643_);
v___y_1645_ = v_a_1322_;
v___y_1646_ = v_a_1323_;
v___y_1647_ = v_a_1324_;
v___y_1648_ = v_a_1325_;
v___y_1649_ = v_a_1326_;
v___y_1650_ = v_a_1327_;
goto v___jp_1644_;
}
}
else
{
lean_dec(v_a_1643_);
v___y_1645_ = v_a_1322_;
v___y_1646_ = v_a_1323_;
v___y_1647_ = v_a_1324_;
v___y_1648_ = v_a_1325_;
v___y_1649_ = v_a_1326_;
v___y_1650_ = v_a_1327_;
goto v___jp_1644_;
}
v___jp_1644_:
{
lean_object* v___x_1651_; 
v___x_1651_ = l_Lean_mkFreshFVarId___at___00Lean_Meta_Closure_collectExprAux_spec__3(v___y_1645_, v___y_1646_, v___y_1647_, v___y_1648_, v___y_1649_, v___y_1650_);
if (lean_obj_tag(v___x_1651_) == 0)
{
lean_object* v_a_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; 
v_a_1652_ = lean_ctor_get(v___x_1651_, 0);
lean_inc_n(v_a_1652_, 2);
lean_dec_ref(v___x_1651_);
v___x_1653_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1653_, 0, v_fvarId_1640_);
lean_ctor_set(v___x_1653_, 1, v_a_1652_);
v___x_1654_ = l_Lean_Meta_Closure_pushToProcess___redArg(v___x_1653_, v___y_1646_);
if (lean_obj_tag(v___x_1654_) == 0)
{
lean_object* v___x_1656_; uint8_t v_isShared_1657_; uint8_t v_isSharedCheck_1662_; 
v_isSharedCheck_1662_ = !lean_is_exclusive(v___x_1654_);
if (v_isSharedCheck_1662_ == 0)
{
lean_object* v_unused_1663_; 
v_unused_1663_ = lean_ctor_get(v___x_1654_, 0);
lean_dec(v_unused_1663_);
v___x_1656_ = v___x_1654_;
v_isShared_1657_ = v_isSharedCheck_1662_;
goto v_resetjp_1655_;
}
else
{
lean_dec(v___x_1654_);
v___x_1656_ = lean_box(0);
v_isShared_1657_ = v_isSharedCheck_1662_;
goto v_resetjp_1655_;
}
v_resetjp_1655_:
{
lean_object* v___x_1658_; lean_object* v___x_1660_; 
v___x_1658_ = l_Lean_mkFVar(v_a_1652_);
if (v_isShared_1657_ == 0)
{
lean_ctor_set(v___x_1656_, 0, v___x_1658_);
v___x_1660_ = v___x_1656_;
goto v_reusejp_1659_;
}
else
{
lean_object* v_reuseFailAlloc_1661_; 
v_reuseFailAlloc_1661_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1661_, 0, v___x_1658_);
v___x_1660_ = v_reuseFailAlloc_1661_;
goto v_reusejp_1659_;
}
v_reusejp_1659_:
{
return v___x_1660_;
}
}
}
else
{
lean_object* v_a_1664_; lean_object* v___x_1666_; uint8_t v_isShared_1667_; uint8_t v_isSharedCheck_1671_; 
lean_dec(v_a_1652_);
v_a_1664_ = lean_ctor_get(v___x_1654_, 0);
v_isSharedCheck_1671_ = !lean_is_exclusive(v___x_1654_);
if (v_isSharedCheck_1671_ == 0)
{
v___x_1666_ = v___x_1654_;
v_isShared_1667_ = v_isSharedCheck_1671_;
goto v_resetjp_1665_;
}
else
{
lean_inc(v_a_1664_);
lean_dec(v___x_1654_);
v___x_1666_ = lean_box(0);
v_isShared_1667_ = v_isSharedCheck_1671_;
goto v_resetjp_1665_;
}
v_resetjp_1665_:
{
lean_object* v___x_1669_; 
if (v_isShared_1667_ == 0)
{
v___x_1669_ = v___x_1666_;
goto v_reusejp_1668_;
}
else
{
lean_object* v_reuseFailAlloc_1670_; 
v_reuseFailAlloc_1670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1670_, 0, v_a_1664_);
v___x_1669_ = v_reuseFailAlloc_1670_;
goto v_reusejp_1668_;
}
v_reusejp_1668_:
{
return v___x_1669_;
}
}
}
}
else
{
lean_object* v_a_1672_; lean_object* v___x_1674_; uint8_t v_isShared_1675_; uint8_t v_isSharedCheck_1679_; 
lean_dec(v_fvarId_1640_);
v_a_1672_ = lean_ctor_get(v___x_1651_, 0);
v_isSharedCheck_1679_ = !lean_is_exclusive(v___x_1651_);
if (v_isSharedCheck_1679_ == 0)
{
v___x_1674_ = v___x_1651_;
v_isShared_1675_ = v_isSharedCheck_1679_;
goto v_resetjp_1673_;
}
else
{
lean_inc(v_a_1672_);
lean_dec(v___x_1651_);
v___x_1674_ = lean_box(0);
v_isShared_1675_ = v_isSharedCheck_1679_;
goto v_resetjp_1673_;
}
v_resetjp_1673_:
{
lean_object* v___x_1677_; 
if (v_isShared_1675_ == 0)
{
v___x_1677_ = v___x_1674_;
goto v_reusejp_1676_;
}
else
{
lean_object* v_reuseFailAlloc_1678_; 
v_reuseFailAlloc_1678_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1678_, 0, v_a_1672_);
v___x_1677_ = v_reuseFailAlloc_1678_;
goto v_reusejp_1676_;
}
v_reusejp_1676_:
{
return v___x_1677_;
}
}
}
}
}
else
{
lean_object* v_a_1684_; lean_object* v___x_1686_; uint8_t v_isShared_1687_; uint8_t v_isSharedCheck_1691_; 
lean_dec(v_fvarId_1640_);
v_a_1684_ = lean_ctor_get(v___x_1642_, 0);
v_isSharedCheck_1691_ = !lean_is_exclusive(v___x_1642_);
if (v_isSharedCheck_1691_ == 0)
{
v___x_1686_ = v___x_1642_;
v_isShared_1687_ = v_isSharedCheck_1691_;
goto v_resetjp_1685_;
}
else
{
lean_inc(v_a_1684_);
lean_dec(v___x_1642_);
v___x_1686_ = lean_box(0);
v_isShared_1687_ = v_isSharedCheck_1691_;
goto v_resetjp_1685_;
}
v_resetjp_1685_:
{
lean_object* v___x_1689_; 
if (v_isShared_1687_ == 0)
{
v___x_1689_ = v___x_1686_;
goto v_reusejp_1688_;
}
else
{
lean_object* v_reuseFailAlloc_1690_; 
v_reuseFailAlloc_1690_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1690_, 0, v_a_1684_);
v___x_1689_ = v_reuseFailAlloc_1690_;
goto v_reusejp_1688_;
}
v_reusejp_1688_:
{
return v___x_1689_;
}
}
}
}
default: 
{
lean_object* v___x_1692_; 
v___x_1692_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1692_, 0, v_e_1321_);
return v___x_1692_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectExprAux___lam__0(lean_object* v_e_1693_, uint8_t v___y_1694_, lean_object* v___y_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_){
_start:
{
uint8_t v___x_1744_; 
v___x_1744_ = l_Lean_Expr_hasLevelParam(v_e_1693_);
if (v___x_1744_ == 0)
{
uint8_t v___x_1745_; 
v___x_1745_ = l_Lean_Expr_hasFVar(v_e_1693_);
if (v___x_1745_ == 0)
{
uint8_t v___x_1746_; 
v___x_1746_ = l_Lean_Expr_hasMVar(v_e_1693_);
if (v___x_1746_ == 0)
{
lean_object* v___x_1747_; 
v___x_1747_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1747_, 0, v_e_1693_);
return v___x_1747_;
}
else
{
goto v___jp_1701_;
}
}
else
{
goto v___jp_1701_;
}
}
else
{
goto v___jp_1701_;
}
v___jp_1701_:
{
lean_object* v___x_1702_; lean_object* v_visitedExpr_1703_; lean_object* v___x_1704_; 
v___x_1702_ = lean_st_ref_get(v___y_1695_);
v_visitedExpr_1703_ = lean_ctor_get(v___x_1702_, 1);
lean_inc_ref(v_visitedExpr_1703_);
lean_dec(v___x_1702_);
v___x_1704_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0___redArg(v_visitedExpr_1703_, v_e_1693_);
lean_dec_ref(v_visitedExpr_1703_);
if (lean_obj_tag(v___x_1704_) == 0)
{
lean_object* v___x_1705_; 
lean_inc_ref(v_e_1693_);
v___x_1705_ = l_Lean_Meta_Closure_collectExprAux(v_e_1693_, v___y_1694_, v___y_1695_, v___y_1696_, v___y_1697_, v___y_1698_, v___y_1699_);
if (lean_obj_tag(v___x_1705_) == 0)
{
lean_object* v_a_1706_; lean_object* v___x_1708_; uint8_t v_isShared_1709_; uint8_t v_isSharedCheck_1735_; 
v_a_1706_ = lean_ctor_get(v___x_1705_, 0);
v_isSharedCheck_1735_ = !lean_is_exclusive(v___x_1705_);
if (v_isSharedCheck_1735_ == 0)
{
v___x_1708_ = v___x_1705_;
v_isShared_1709_ = v_isSharedCheck_1735_;
goto v_resetjp_1707_;
}
else
{
lean_inc(v_a_1706_);
lean_dec(v___x_1705_);
v___x_1708_ = lean_box(0);
v_isShared_1709_ = v_isSharedCheck_1735_;
goto v_resetjp_1707_;
}
v_resetjp_1707_:
{
lean_object* v___x_1710_; lean_object* v_visitedLevel_1711_; lean_object* v_visitedExpr_1712_; lean_object* v_levelParams_1713_; lean_object* v_nextLevelIdx_1714_; lean_object* v_levelArgs_1715_; lean_object* v_newLocalDecls_1716_; lean_object* v_newLocalDeclsForMVars_1717_; lean_object* v_newLetDecls_1718_; lean_object* v_nextExprIdx_1719_; lean_object* v_exprMVarArgs_1720_; lean_object* v_exprFVarArgs_1721_; lean_object* v_toProcess_1722_; lean_object* v___x_1724_; uint8_t v_isShared_1725_; uint8_t v_isSharedCheck_1734_; 
v___x_1710_ = lean_st_ref_take(v___y_1695_);
v_visitedLevel_1711_ = lean_ctor_get(v___x_1710_, 0);
v_visitedExpr_1712_ = lean_ctor_get(v___x_1710_, 1);
v_levelParams_1713_ = lean_ctor_get(v___x_1710_, 2);
v_nextLevelIdx_1714_ = lean_ctor_get(v___x_1710_, 3);
v_levelArgs_1715_ = lean_ctor_get(v___x_1710_, 4);
v_newLocalDecls_1716_ = lean_ctor_get(v___x_1710_, 5);
v_newLocalDeclsForMVars_1717_ = lean_ctor_get(v___x_1710_, 6);
v_newLetDecls_1718_ = lean_ctor_get(v___x_1710_, 7);
v_nextExprIdx_1719_ = lean_ctor_get(v___x_1710_, 8);
v_exprMVarArgs_1720_ = lean_ctor_get(v___x_1710_, 9);
v_exprFVarArgs_1721_ = lean_ctor_get(v___x_1710_, 10);
v_toProcess_1722_ = lean_ctor_get(v___x_1710_, 11);
v_isSharedCheck_1734_ = !lean_is_exclusive(v___x_1710_);
if (v_isSharedCheck_1734_ == 0)
{
v___x_1724_ = v___x_1710_;
v_isShared_1725_ = v_isSharedCheck_1734_;
goto v_resetjp_1723_;
}
else
{
lean_inc(v_toProcess_1722_);
lean_inc(v_exprFVarArgs_1721_);
lean_inc(v_exprMVarArgs_1720_);
lean_inc(v_nextExprIdx_1719_);
lean_inc(v_newLetDecls_1718_);
lean_inc(v_newLocalDeclsForMVars_1717_);
lean_inc(v_newLocalDecls_1716_);
lean_inc(v_levelArgs_1715_);
lean_inc(v_nextLevelIdx_1714_);
lean_inc(v_levelParams_1713_);
lean_inc(v_visitedExpr_1712_);
lean_inc(v_visitedLevel_1711_);
lean_dec(v___x_1710_);
v___x_1724_ = lean_box(0);
v_isShared_1725_ = v_isSharedCheck_1734_;
goto v_resetjp_1723_;
}
v_resetjp_1723_:
{
lean_object* v___x_1726_; lean_object* v___x_1728_; 
lean_inc(v_a_1706_);
v___x_1726_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1___redArg(v_visitedExpr_1712_, v_e_1693_, v_a_1706_);
if (v_isShared_1725_ == 0)
{
lean_ctor_set(v___x_1724_, 1, v___x_1726_);
v___x_1728_ = v___x_1724_;
goto v_reusejp_1727_;
}
else
{
lean_object* v_reuseFailAlloc_1733_; 
v_reuseFailAlloc_1733_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_1733_, 0, v_visitedLevel_1711_);
lean_ctor_set(v_reuseFailAlloc_1733_, 1, v___x_1726_);
lean_ctor_set(v_reuseFailAlloc_1733_, 2, v_levelParams_1713_);
lean_ctor_set(v_reuseFailAlloc_1733_, 3, v_nextLevelIdx_1714_);
lean_ctor_set(v_reuseFailAlloc_1733_, 4, v_levelArgs_1715_);
lean_ctor_set(v_reuseFailAlloc_1733_, 5, v_newLocalDecls_1716_);
lean_ctor_set(v_reuseFailAlloc_1733_, 6, v_newLocalDeclsForMVars_1717_);
lean_ctor_set(v_reuseFailAlloc_1733_, 7, v_newLetDecls_1718_);
lean_ctor_set(v_reuseFailAlloc_1733_, 8, v_nextExprIdx_1719_);
lean_ctor_set(v_reuseFailAlloc_1733_, 9, v_exprMVarArgs_1720_);
lean_ctor_set(v_reuseFailAlloc_1733_, 10, v_exprFVarArgs_1721_);
lean_ctor_set(v_reuseFailAlloc_1733_, 11, v_toProcess_1722_);
v___x_1728_ = v_reuseFailAlloc_1733_;
goto v_reusejp_1727_;
}
v_reusejp_1727_:
{
lean_object* v___x_1729_; lean_object* v___x_1731_; 
v___x_1729_ = lean_st_ref_set(v___y_1695_, v___x_1728_);
if (v_isShared_1709_ == 0)
{
v___x_1731_ = v___x_1708_;
goto v_reusejp_1730_;
}
else
{
lean_object* v_reuseFailAlloc_1732_; 
v_reuseFailAlloc_1732_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1732_, 0, v_a_1706_);
v___x_1731_ = v_reuseFailAlloc_1732_;
goto v_reusejp_1730_;
}
v_reusejp_1730_:
{
return v___x_1731_;
}
}
}
}
}
else
{
lean_dec_ref(v_e_1693_);
return v___x_1705_;
}
}
else
{
lean_object* v_val_1736_; lean_object* v___x_1738_; uint8_t v_isShared_1739_; uint8_t v_isSharedCheck_1743_; 
lean_dec_ref(v_e_1693_);
v_val_1736_ = lean_ctor_get(v___x_1704_, 0);
v_isSharedCheck_1743_ = !lean_is_exclusive(v___x_1704_);
if (v_isSharedCheck_1743_ == 0)
{
v___x_1738_ = v___x_1704_;
v_isShared_1739_ = v_isSharedCheck_1743_;
goto v_resetjp_1737_;
}
else
{
lean_inc(v_val_1736_);
lean_dec(v___x_1704_);
v___x_1738_ = lean_box(0);
v_isShared_1739_ = v_isSharedCheck_1743_;
goto v_resetjp_1737_;
}
v_resetjp_1737_:
{
lean_object* v___x_1741_; 
if (v_isShared_1739_ == 0)
{
lean_ctor_set_tag(v___x_1738_, 0);
v___x_1741_ = v___x_1738_;
goto v_reusejp_1740_;
}
else
{
lean_object* v_reuseFailAlloc_1742_; 
v_reuseFailAlloc_1742_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1742_, 0, v_val_1736_);
v___x_1741_ = v_reuseFailAlloc_1742_;
goto v_reusejp_1740_;
}
v_reusejp_1740_:
{
return v___x_1741_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectExprAux___lam__0___boxed(lean_object* v_e_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_){
_start:
{
uint8_t v___y_18416__boxed_1756_; lean_object* v_res_1757_; 
v___y_18416__boxed_1756_ = lean_unbox(v___y_1749_);
v_res_1757_ = l_Lean_Meta_Closure_collectExprAux___lam__0(v_e_1748_, v___y_18416__boxed_1756_, v___y_1750_, v___y_1751_, v___y_1752_, v___y_1753_, v___y_1754_);
lean_dec(v___y_1754_);
lean_dec_ref(v___y_1753_);
lean_dec(v___y_1752_);
lean_dec_ref(v___y_1751_);
lean_dec(v___y_1750_);
return v_res_1757_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectExprAux___boxed(lean_object* v_e_1758_, lean_object* v_a_1759_, lean_object* v_a_1760_, lean_object* v_a_1761_, lean_object* v_a_1762_, lean_object* v_a_1763_, lean_object* v_a_1764_, lean_object* v_a_1765_){
_start:
{
uint8_t v_a_boxed_1766_; lean_object* v_res_1767_; 
v_a_boxed_1766_ = lean_unbox(v_a_1759_);
v_res_1767_ = l_Lean_Meta_Closure_collectExprAux(v_e_1758_, v_a_boxed_1766_, v_a_1760_, v_a_1761_, v_a_1762_, v_a_1763_, v_a_1764_);
lean_dec(v_a_1764_);
lean_dec_ref(v_a_1763_);
lean_dec(v_a_1762_);
lean_dec_ref(v_a_1761_);
lean_dec(v_a_1760_);
return v_res_1767_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0(lean_object* v_00_u03b2_1768_, lean_object* v_m_1769_, lean_object* v_a_1770_){
_start:
{
lean_object* v___x_1771_; 
v___x_1771_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0___redArg(v_m_1769_, v_a_1770_);
return v___x_1771_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0___boxed(lean_object* v_00_u03b2_1772_, lean_object* v_m_1773_, lean_object* v_a_1774_){
_start:
{
lean_object* v_res_1775_; 
v_res_1775_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0(v_00_u03b2_1772_, v_m_1773_, v_a_1774_);
lean_dec_ref(v_a_1774_);
lean_dec_ref(v_m_1773_);
return v_res_1775_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1(lean_object* v_00_u03b2_1776_, lean_object* v_m_1777_, lean_object* v_a_1778_, lean_object* v_b_1779_){
_start:
{
lean_object* v___x_1780_; 
v___x_1780_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1___redArg(v_m_1777_, v_a_1778_, v_b_1779_);
return v___x_1780_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Closure_collectExprAux_spec__2(lean_object* v_x_1781_, lean_object* v_x_1782_, uint8_t v___y_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_){
_start:
{
lean_object* v___x_1790_; 
v___x_1790_ = l_List_mapM_loop___at___00Lean_Meta_Closure_collectExprAux_spec__2___redArg(v_x_1781_, v_x_1782_, v___y_1784_);
return v___x_1790_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Closure_collectExprAux_spec__2___boxed(lean_object* v_x_1791_, lean_object* v_x_1792_, lean_object* v___y_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_){
_start:
{
uint8_t v___y_19232__boxed_1800_; lean_object* v_res_1801_; 
v___y_19232__boxed_1800_ = lean_unbox(v___y_1793_);
v_res_1801_ = l_List_mapM_loop___at___00Lean_Meta_Closure_collectExprAux_spec__2(v_x_1791_, v_x_1792_, v___y_19232__boxed_1800_, v___y_1794_, v___y_1795_, v___y_1796_, v___y_1797_, v___y_1798_);
lean_dec(v___y_1798_);
lean_dec_ref(v___y_1797_);
lean_dec(v___y_1796_);
lean_dec_ref(v___y_1795_);
lean_dec(v___y_1794_);
return v_res_1801_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Closure_collectExprAux_spec__3_spec__7(uint8_t v___y_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_){
_start:
{
lean_object* v___x_1809_; 
v___x_1809_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Closure_collectExprAux_spec__3_spec__7___redArg(v___y_1807_);
return v___x_1809_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Closure_collectExprAux_spec__3_spec__7___boxed(lean_object* v___y_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_){
_start:
{
uint8_t v___y_19259__boxed_1817_; lean_object* v_res_1818_; 
v___y_19259__boxed_1817_ = lean_unbox(v___y_1810_);
v_res_1818_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Closure_collectExprAux_spec__3_spec__7(v___y_19259__boxed_1817_, v___y_1811_, v___y_1812_, v___y_1813_, v___y_1814_, v___y_1815_);
lean_dec(v___y_1815_);
lean_dec_ref(v___y_1814_);
lean_dec(v___y_1813_);
lean_dec_ref(v___y_1812_);
lean_dec(v___y_1811_);
return v_res_1818_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0_spec__0(lean_object* v_00_u03b2_1819_, lean_object* v_a_1820_, lean_object* v_x_1821_){
_start:
{
lean_object* v___x_1822_; 
v___x_1822_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0_spec__0___redArg(v_a_1820_, v_x_1821_);
return v___x_1822_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1823_, lean_object* v_a_1824_, lean_object* v_x_1825_){
_start:
{
lean_object* v_res_1826_; 
v_res_1826_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0_spec__0(v_00_u03b2_1823_, v_a_1824_, v_x_1825_);
lean_dec(v_x_1825_);
lean_dec_ref(v_a_1824_);
return v_res_1826_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__2(lean_object* v_00_u03b2_1827_, lean_object* v_a_1828_, lean_object* v_x_1829_){
_start:
{
uint8_t v___x_1830_; 
v___x_1830_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__2___redArg(v_a_1828_, v_x_1829_);
return v___x_1830_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1831_, lean_object* v_a_1832_, lean_object* v_x_1833_){
_start:
{
uint8_t v_res_1834_; lean_object* v_r_1835_; 
v_res_1834_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__2(v_00_u03b2_1831_, v_a_1832_, v_x_1833_);
lean_dec(v_x_1833_);
lean_dec_ref(v_a_1832_);
v_r_1835_ = lean_box(v_res_1834_);
return v_r_1835_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__3(lean_object* v_00_u03b2_1836_, lean_object* v_data_1837_){
_start:
{
lean_object* v___x_1838_; 
v___x_1838_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__3___redArg(v_data_1837_);
return v___x_1838_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__4(lean_object* v_00_u03b2_1839_, lean_object* v_a_1840_, lean_object* v_b_1841_, lean_object* v_x_1842_){
_start:
{
lean_object* v___x_1843_; 
v___x_1843_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__4___redArg(v_a_1840_, v_b_1841_, v_x_1842_);
return v___x_1843_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__3_spec__6(lean_object* v_00_u03b2_1844_, lean_object* v_i_1845_, lean_object* v_source_1846_, lean_object* v_target_1847_){
_start:
{
lean_object* v___x_1848_; 
v___x_1848_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__3_spec__6___redArg(v_i_1845_, v_source_1846_, v_target_1847_);
return v___x_1848_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__3_spec__6_spec__10(lean_object* v_00_u03b2_1849_, lean_object* v_x_1850_, lean_object* v_x_1851_){
_start:
{
lean_object* v___x_1852_; 
v___x_1852_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__3_spec__6_spec__10___redArg(v_x_1850_, v_x_1851_);
return v___x_1852_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectExpr(lean_object* v_e_1853_, uint8_t v_a_1854_, lean_object* v_a_1855_, lean_object* v_a_1856_, lean_object* v_a_1857_, lean_object* v_a_1858_, lean_object* v_a_1859_){
_start:
{
lean_object* v___x_1861_; 
v___x_1861_ = l_Lean_Meta_Closure_preprocess(v_e_1853_, v_a_1854_, v_a_1855_, v_a_1856_, v_a_1857_, v_a_1858_, v_a_1859_);
if (lean_obj_tag(v___x_1861_) == 0)
{
lean_object* v_a_1862_; uint8_t v___x_1906_; 
v_a_1862_ = lean_ctor_get(v___x_1861_, 0);
lean_inc(v_a_1862_);
v___x_1906_ = l_Lean_Expr_hasLevelParam(v_a_1862_);
if (v___x_1906_ == 0)
{
uint8_t v___x_1907_; 
v___x_1907_ = l_Lean_Expr_hasFVar(v_a_1862_);
if (v___x_1907_ == 0)
{
uint8_t v___x_1908_; 
v___x_1908_ = l_Lean_Expr_hasMVar(v_a_1862_);
if (v___x_1908_ == 0)
{
lean_dec(v_a_1862_);
return v___x_1861_;
}
else
{
lean_dec_ref(v___x_1861_);
goto v___jp_1863_;
}
}
else
{
lean_dec_ref(v___x_1861_);
goto v___jp_1863_;
}
}
else
{
lean_dec_ref(v___x_1861_);
goto v___jp_1863_;
}
v___jp_1863_:
{
lean_object* v___x_1864_; lean_object* v_visitedExpr_1865_; lean_object* v___x_1866_; 
v___x_1864_ = lean_st_ref_get(v_a_1855_);
v_visitedExpr_1865_ = lean_ctor_get(v___x_1864_, 1);
lean_inc_ref(v_visitedExpr_1865_);
lean_dec(v___x_1864_);
v___x_1866_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0___redArg(v_visitedExpr_1865_, v_a_1862_);
lean_dec_ref(v_visitedExpr_1865_);
if (lean_obj_tag(v___x_1866_) == 0)
{
lean_object* v___x_1867_; 
lean_inc(v_a_1862_);
v___x_1867_ = l_Lean_Meta_Closure_collectExprAux(v_a_1862_, v_a_1854_, v_a_1855_, v_a_1856_, v_a_1857_, v_a_1858_, v_a_1859_);
if (lean_obj_tag(v___x_1867_) == 0)
{
lean_object* v_a_1868_; lean_object* v___x_1870_; uint8_t v_isShared_1871_; uint8_t v_isSharedCheck_1897_; 
v_a_1868_ = lean_ctor_get(v___x_1867_, 0);
v_isSharedCheck_1897_ = !lean_is_exclusive(v___x_1867_);
if (v_isSharedCheck_1897_ == 0)
{
v___x_1870_ = v___x_1867_;
v_isShared_1871_ = v_isSharedCheck_1897_;
goto v_resetjp_1869_;
}
else
{
lean_inc(v_a_1868_);
lean_dec(v___x_1867_);
v___x_1870_ = lean_box(0);
v_isShared_1871_ = v_isSharedCheck_1897_;
goto v_resetjp_1869_;
}
v_resetjp_1869_:
{
lean_object* v___x_1872_; lean_object* v_visitedLevel_1873_; lean_object* v_visitedExpr_1874_; lean_object* v_levelParams_1875_; lean_object* v_nextLevelIdx_1876_; lean_object* v_levelArgs_1877_; lean_object* v_newLocalDecls_1878_; lean_object* v_newLocalDeclsForMVars_1879_; lean_object* v_newLetDecls_1880_; lean_object* v_nextExprIdx_1881_; lean_object* v_exprMVarArgs_1882_; lean_object* v_exprFVarArgs_1883_; lean_object* v_toProcess_1884_; lean_object* v___x_1886_; uint8_t v_isShared_1887_; uint8_t v_isSharedCheck_1896_; 
v___x_1872_ = lean_st_ref_take(v_a_1855_);
v_visitedLevel_1873_ = lean_ctor_get(v___x_1872_, 0);
v_visitedExpr_1874_ = lean_ctor_get(v___x_1872_, 1);
v_levelParams_1875_ = lean_ctor_get(v___x_1872_, 2);
v_nextLevelIdx_1876_ = lean_ctor_get(v___x_1872_, 3);
v_levelArgs_1877_ = lean_ctor_get(v___x_1872_, 4);
v_newLocalDecls_1878_ = lean_ctor_get(v___x_1872_, 5);
v_newLocalDeclsForMVars_1879_ = lean_ctor_get(v___x_1872_, 6);
v_newLetDecls_1880_ = lean_ctor_get(v___x_1872_, 7);
v_nextExprIdx_1881_ = lean_ctor_get(v___x_1872_, 8);
v_exprMVarArgs_1882_ = lean_ctor_get(v___x_1872_, 9);
v_exprFVarArgs_1883_ = lean_ctor_get(v___x_1872_, 10);
v_toProcess_1884_ = lean_ctor_get(v___x_1872_, 11);
v_isSharedCheck_1896_ = !lean_is_exclusive(v___x_1872_);
if (v_isSharedCheck_1896_ == 0)
{
v___x_1886_ = v___x_1872_;
v_isShared_1887_ = v_isSharedCheck_1896_;
goto v_resetjp_1885_;
}
else
{
lean_inc(v_toProcess_1884_);
lean_inc(v_exprFVarArgs_1883_);
lean_inc(v_exprMVarArgs_1882_);
lean_inc(v_nextExprIdx_1881_);
lean_inc(v_newLetDecls_1880_);
lean_inc(v_newLocalDeclsForMVars_1879_);
lean_inc(v_newLocalDecls_1878_);
lean_inc(v_levelArgs_1877_);
lean_inc(v_nextLevelIdx_1876_);
lean_inc(v_levelParams_1875_);
lean_inc(v_visitedExpr_1874_);
lean_inc(v_visitedLevel_1873_);
lean_dec(v___x_1872_);
v___x_1886_ = lean_box(0);
v_isShared_1887_ = v_isSharedCheck_1896_;
goto v_resetjp_1885_;
}
v_resetjp_1885_:
{
lean_object* v___x_1888_; lean_object* v___x_1890_; 
lean_inc(v_a_1868_);
v___x_1888_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1___redArg(v_visitedExpr_1874_, v_a_1862_, v_a_1868_);
if (v_isShared_1887_ == 0)
{
lean_ctor_set(v___x_1886_, 1, v___x_1888_);
v___x_1890_ = v___x_1886_;
goto v_reusejp_1889_;
}
else
{
lean_object* v_reuseFailAlloc_1895_; 
v_reuseFailAlloc_1895_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_1895_, 0, v_visitedLevel_1873_);
lean_ctor_set(v_reuseFailAlloc_1895_, 1, v___x_1888_);
lean_ctor_set(v_reuseFailAlloc_1895_, 2, v_levelParams_1875_);
lean_ctor_set(v_reuseFailAlloc_1895_, 3, v_nextLevelIdx_1876_);
lean_ctor_set(v_reuseFailAlloc_1895_, 4, v_levelArgs_1877_);
lean_ctor_set(v_reuseFailAlloc_1895_, 5, v_newLocalDecls_1878_);
lean_ctor_set(v_reuseFailAlloc_1895_, 6, v_newLocalDeclsForMVars_1879_);
lean_ctor_set(v_reuseFailAlloc_1895_, 7, v_newLetDecls_1880_);
lean_ctor_set(v_reuseFailAlloc_1895_, 8, v_nextExprIdx_1881_);
lean_ctor_set(v_reuseFailAlloc_1895_, 9, v_exprMVarArgs_1882_);
lean_ctor_set(v_reuseFailAlloc_1895_, 10, v_exprFVarArgs_1883_);
lean_ctor_set(v_reuseFailAlloc_1895_, 11, v_toProcess_1884_);
v___x_1890_ = v_reuseFailAlloc_1895_;
goto v_reusejp_1889_;
}
v_reusejp_1889_:
{
lean_object* v___x_1891_; lean_object* v___x_1893_; 
v___x_1891_ = lean_st_ref_set(v_a_1855_, v___x_1890_);
if (v_isShared_1871_ == 0)
{
v___x_1893_ = v___x_1870_;
goto v_reusejp_1892_;
}
else
{
lean_object* v_reuseFailAlloc_1894_; 
v_reuseFailAlloc_1894_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1894_, 0, v_a_1868_);
v___x_1893_ = v_reuseFailAlloc_1894_;
goto v_reusejp_1892_;
}
v_reusejp_1892_:
{
return v___x_1893_;
}
}
}
}
}
else
{
lean_dec(v_a_1862_);
return v___x_1867_;
}
}
else
{
lean_object* v_val_1898_; lean_object* v___x_1900_; uint8_t v_isShared_1901_; uint8_t v_isSharedCheck_1905_; 
lean_dec(v_a_1862_);
v_val_1898_ = lean_ctor_get(v___x_1866_, 0);
v_isSharedCheck_1905_ = !lean_is_exclusive(v___x_1866_);
if (v_isSharedCheck_1905_ == 0)
{
v___x_1900_ = v___x_1866_;
v_isShared_1901_ = v_isSharedCheck_1905_;
goto v_resetjp_1899_;
}
else
{
lean_inc(v_val_1898_);
lean_dec(v___x_1866_);
v___x_1900_ = lean_box(0);
v_isShared_1901_ = v_isSharedCheck_1905_;
goto v_resetjp_1899_;
}
v_resetjp_1899_:
{
lean_object* v___x_1903_; 
if (v_isShared_1901_ == 0)
{
lean_ctor_set_tag(v___x_1900_, 0);
v___x_1903_ = v___x_1900_;
goto v_reusejp_1902_;
}
else
{
lean_object* v_reuseFailAlloc_1904_; 
v_reuseFailAlloc_1904_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1904_, 0, v_val_1898_);
v___x_1903_ = v_reuseFailAlloc_1904_;
goto v_reusejp_1902_;
}
v_reusejp_1902_:
{
return v___x_1903_;
}
}
}
}
}
else
{
return v___x_1861_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectExpr___boxed(lean_object* v_e_1909_, lean_object* v_a_1910_, lean_object* v_a_1911_, lean_object* v_a_1912_, lean_object* v_a_1913_, lean_object* v_a_1914_, lean_object* v_a_1915_, lean_object* v_a_1916_){
_start:
{
uint8_t v_a_boxed_1917_; lean_object* v_res_1918_; 
v_a_boxed_1917_ = lean_unbox(v_a_1910_);
v_res_1918_ = l_Lean_Meta_Closure_collectExpr(v_e_1909_, v_a_boxed_1917_, v_a_1911_, v_a_1912_, v_a_1913_, v_a_1914_, v_a_1915_);
lean_dec(v_a_1915_);
lean_dec_ref(v_a_1914_);
lean_dec(v_a_1913_);
lean_dec_ref(v_a_1912_);
lean_dec(v_a_1911_);
return v_res_1918_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pickNextToProcessAux(lean_object* v_lctx_1919_, lean_object* v_i_1920_, lean_object* v_toProcess_1921_, lean_object* v_elem_1922_){
_start:
{
lean_object* v___x_1923_; uint8_t v___x_1924_; 
v___x_1923_ = lean_array_get_size(v_toProcess_1921_);
v___x_1924_ = lean_nat_dec_lt(v_i_1920_, v___x_1923_);
if (v___x_1924_ == 0)
{
lean_object* v___x_1925_; 
lean_dec(v_i_1920_);
lean_dec_ref(v_lctx_1919_);
v___x_1925_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1925_, 0, v_elem_1922_);
lean_ctor_set(v___x_1925_, 1, v_toProcess_1921_);
return v___x_1925_;
}
else
{
lean_object* v_fvarId_1926_; lean_object* v_elem_x27_1927_; lean_object* v_fvarId_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; uint8_t v___x_1933_; 
v_fvarId_1926_ = lean_ctor_get(v_elem_1922_, 0);
v_elem_x27_1927_ = lean_array_fget_borrowed(v_toProcess_1921_, v_i_1920_);
v_fvarId_1928_ = lean_ctor_get(v_elem_x27_1927_, 0);
lean_inc(v_fvarId_1926_);
lean_inc_ref_n(v_lctx_1919_, 2);
v___x_1929_ = l_Lean_LocalContext_get_x21(v_lctx_1919_, v_fvarId_1926_);
v___x_1930_ = l_Lean_LocalDecl_index(v___x_1929_);
lean_dec_ref(v___x_1929_);
lean_inc(v_fvarId_1928_);
v___x_1931_ = l_Lean_LocalContext_get_x21(v_lctx_1919_, v_fvarId_1928_);
v___x_1932_ = l_Lean_LocalDecl_index(v___x_1931_);
lean_dec_ref(v___x_1931_);
v___x_1933_ = lean_nat_dec_lt(v___x_1930_, v___x_1932_);
lean_dec(v___x_1932_);
lean_dec(v___x_1930_);
if (v___x_1933_ == 0)
{
lean_object* v___x_1934_; lean_object* v___x_1935_; 
v___x_1934_ = lean_unsigned_to_nat(1u);
v___x_1935_ = lean_nat_add(v_i_1920_, v___x_1934_);
lean_dec(v_i_1920_);
v_i_1920_ = v___x_1935_;
goto _start;
}
else
{
lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; 
lean_inc(v_elem_x27_1927_);
v___x_1937_ = lean_unsigned_to_nat(1u);
v___x_1938_ = lean_nat_add(v_i_1920_, v___x_1937_);
v___x_1939_ = lean_array_fset(v_toProcess_1921_, v_i_1920_, v_elem_1922_);
lean_dec(v_i_1920_);
v_i_1920_ = v___x_1938_;
v_toProcess_1921_ = v___x_1939_;
v_elem_1922_ = v_elem_x27_1927_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pickNextToProcess_x3f___redArg(lean_object* v_a_1941_, lean_object* v_a_1942_){
_start:
{
lean_object* v___x_1944_; lean_object* v_toProcess_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; uint8_t v___x_1948_; 
v___x_1944_ = lean_st_ref_get(v_a_1941_);
v_toProcess_1945_ = lean_ctor_get(v___x_1944_, 11);
lean_inc_ref(v_toProcess_1945_);
lean_dec(v___x_1944_);
v___x_1946_ = lean_array_get_size(v_toProcess_1945_);
lean_dec_ref(v_toProcess_1945_);
v___x_1947_ = lean_unsigned_to_nat(0u);
v___x_1948_ = lean_nat_dec_eq(v___x_1946_, v___x_1947_);
if (v___x_1948_ == 0)
{
lean_object* v___x_1949_; lean_object* v_lctx_1950_; lean_object* v_visitedLevel_1951_; lean_object* v_visitedExpr_1952_; lean_object* v_levelParams_1953_; lean_object* v_nextLevelIdx_1954_; lean_object* v_levelArgs_1955_; lean_object* v_newLocalDecls_1956_; lean_object* v_newLocalDeclsForMVars_1957_; lean_object* v_newLetDecls_1958_; lean_object* v_nextExprIdx_1959_; lean_object* v_exprMVarArgs_1960_; lean_object* v_exprFVarArgs_1961_; lean_object* v_toProcess_1962_; lean_object* v___x_1964_; uint8_t v_isShared_1965_; uint8_t v_isSharedCheck_1981_; 
v___x_1949_ = lean_st_ref_take(v_a_1941_);
v_lctx_1950_ = lean_ctor_get(v_a_1942_, 2);
v_visitedLevel_1951_ = lean_ctor_get(v___x_1949_, 0);
v_visitedExpr_1952_ = lean_ctor_get(v___x_1949_, 1);
v_levelParams_1953_ = lean_ctor_get(v___x_1949_, 2);
v_nextLevelIdx_1954_ = lean_ctor_get(v___x_1949_, 3);
v_levelArgs_1955_ = lean_ctor_get(v___x_1949_, 4);
v_newLocalDecls_1956_ = lean_ctor_get(v___x_1949_, 5);
v_newLocalDeclsForMVars_1957_ = lean_ctor_get(v___x_1949_, 6);
v_newLetDecls_1958_ = lean_ctor_get(v___x_1949_, 7);
v_nextExprIdx_1959_ = lean_ctor_get(v___x_1949_, 8);
v_exprMVarArgs_1960_ = lean_ctor_get(v___x_1949_, 9);
v_exprFVarArgs_1961_ = lean_ctor_get(v___x_1949_, 10);
v_toProcess_1962_ = lean_ctor_get(v___x_1949_, 11);
v_isSharedCheck_1981_ = !lean_is_exclusive(v___x_1949_);
if (v_isSharedCheck_1981_ == 0)
{
v___x_1964_ = v___x_1949_;
v_isShared_1965_ = v_isSharedCheck_1981_;
goto v_resetjp_1963_;
}
else
{
lean_inc(v_toProcess_1962_);
lean_inc(v_exprFVarArgs_1961_);
lean_inc(v_exprMVarArgs_1960_);
lean_inc(v_nextExprIdx_1959_);
lean_inc(v_newLetDecls_1958_);
lean_inc(v_newLocalDeclsForMVars_1957_);
lean_inc(v_newLocalDecls_1956_);
lean_inc(v_levelArgs_1955_);
lean_inc(v_nextLevelIdx_1954_);
lean_inc(v_levelParams_1953_);
lean_inc(v_visitedExpr_1952_);
lean_inc(v_visitedLevel_1951_);
lean_dec(v___x_1949_);
v___x_1964_ = lean_box(0);
v_isShared_1965_ = v_isSharedCheck_1981_;
goto v_resetjp_1963_;
}
v_resetjp_1963_:
{
lean_object* v___x_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; lean_object* v___x_1972_; lean_object* v_fst_1973_; lean_object* v_snd_1974_; lean_object* v___x_1976_; 
v___x_1966_ = ((lean_object*)(l_Lean_Meta_Closure_instInhabitedToProcessElement_default));
v___x_1967_ = lean_array_get_size(v_toProcess_1962_);
v___x_1968_ = lean_unsigned_to_nat(1u);
v___x_1969_ = lean_nat_sub(v___x_1967_, v___x_1968_);
v___x_1970_ = lean_array_get(v___x_1966_, v_toProcess_1962_, v___x_1969_);
lean_dec(v___x_1969_);
v___x_1971_ = lean_array_pop(v_toProcess_1962_);
lean_inc_ref(v_lctx_1950_);
v___x_1972_ = l_Lean_Meta_Closure_pickNextToProcessAux(v_lctx_1950_, v___x_1947_, v___x_1971_, v___x_1970_);
v_fst_1973_ = lean_ctor_get(v___x_1972_, 0);
lean_inc(v_fst_1973_);
v_snd_1974_ = lean_ctor_get(v___x_1972_, 1);
lean_inc(v_snd_1974_);
lean_dec_ref(v___x_1972_);
if (v_isShared_1965_ == 0)
{
lean_ctor_set(v___x_1964_, 11, v_snd_1974_);
v___x_1976_ = v___x_1964_;
goto v_reusejp_1975_;
}
else
{
lean_object* v_reuseFailAlloc_1980_; 
v_reuseFailAlloc_1980_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_1980_, 0, v_visitedLevel_1951_);
lean_ctor_set(v_reuseFailAlloc_1980_, 1, v_visitedExpr_1952_);
lean_ctor_set(v_reuseFailAlloc_1980_, 2, v_levelParams_1953_);
lean_ctor_set(v_reuseFailAlloc_1980_, 3, v_nextLevelIdx_1954_);
lean_ctor_set(v_reuseFailAlloc_1980_, 4, v_levelArgs_1955_);
lean_ctor_set(v_reuseFailAlloc_1980_, 5, v_newLocalDecls_1956_);
lean_ctor_set(v_reuseFailAlloc_1980_, 6, v_newLocalDeclsForMVars_1957_);
lean_ctor_set(v_reuseFailAlloc_1980_, 7, v_newLetDecls_1958_);
lean_ctor_set(v_reuseFailAlloc_1980_, 8, v_nextExprIdx_1959_);
lean_ctor_set(v_reuseFailAlloc_1980_, 9, v_exprMVarArgs_1960_);
lean_ctor_set(v_reuseFailAlloc_1980_, 10, v_exprFVarArgs_1961_);
lean_ctor_set(v_reuseFailAlloc_1980_, 11, v_snd_1974_);
v___x_1976_ = v_reuseFailAlloc_1980_;
goto v_reusejp_1975_;
}
v_reusejp_1975_:
{
lean_object* v___x_1977_; lean_object* v___x_1978_; lean_object* v___x_1979_; 
v___x_1977_ = lean_st_ref_set(v_a_1941_, v___x_1976_);
v___x_1978_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1978_, 0, v_fst_1973_);
v___x_1979_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1979_, 0, v___x_1978_);
return v___x_1979_;
}
}
}
else
{
lean_object* v___x_1982_; lean_object* v___x_1983_; 
v___x_1982_ = lean_box(0);
v___x_1983_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1983_, 0, v___x_1982_);
return v___x_1983_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pickNextToProcess_x3f___redArg___boxed(lean_object* v_a_1984_, lean_object* v_a_1985_, lean_object* v_a_1986_){
_start:
{
lean_object* v_res_1987_; 
v_res_1987_ = l_Lean_Meta_Closure_pickNextToProcess_x3f___redArg(v_a_1984_, v_a_1985_);
lean_dec_ref(v_a_1985_);
lean_dec(v_a_1984_);
return v_res_1987_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pickNextToProcess_x3f(uint8_t v_a_1988_, lean_object* v_a_1989_, lean_object* v_a_1990_, lean_object* v_a_1991_, lean_object* v_a_1992_, lean_object* v_a_1993_){
_start:
{
lean_object* v___x_1995_; 
v___x_1995_ = l_Lean_Meta_Closure_pickNextToProcess_x3f___redArg(v_a_1989_, v_a_1990_);
return v___x_1995_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pickNextToProcess_x3f___boxed(lean_object* v_a_1996_, lean_object* v_a_1997_, lean_object* v_a_1998_, lean_object* v_a_1999_, lean_object* v_a_2000_, lean_object* v_a_2001_, lean_object* v_a_2002_){
_start:
{
uint8_t v_a_boxed_2003_; lean_object* v_res_2004_; 
v_a_boxed_2003_ = lean_unbox(v_a_1996_);
v_res_2004_ = l_Lean_Meta_Closure_pickNextToProcess_x3f(v_a_boxed_2003_, v_a_1997_, v_a_1998_, v_a_1999_, v_a_2000_, v_a_2001_);
lean_dec(v_a_2001_);
lean_dec_ref(v_a_2000_);
lean_dec(v_a_1999_);
lean_dec_ref(v_a_1998_);
lean_dec(v_a_1997_);
return v_res_2004_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushFVarArg___redArg(lean_object* v_e_2005_, lean_object* v_a_2006_){
_start:
{
lean_object* v___x_2008_; lean_object* v_visitedLevel_2009_; lean_object* v_visitedExpr_2010_; lean_object* v_levelParams_2011_; lean_object* v_nextLevelIdx_2012_; lean_object* v_levelArgs_2013_; lean_object* v_newLocalDecls_2014_; lean_object* v_newLocalDeclsForMVars_2015_; lean_object* v_newLetDecls_2016_; lean_object* v_nextExprIdx_2017_; lean_object* v_exprMVarArgs_2018_; lean_object* v_exprFVarArgs_2019_; lean_object* v_toProcess_2020_; lean_object* v___x_2022_; uint8_t v_isShared_2023_; uint8_t v_isSharedCheck_2031_; 
v___x_2008_ = lean_st_ref_take(v_a_2006_);
v_visitedLevel_2009_ = lean_ctor_get(v___x_2008_, 0);
v_visitedExpr_2010_ = lean_ctor_get(v___x_2008_, 1);
v_levelParams_2011_ = lean_ctor_get(v___x_2008_, 2);
v_nextLevelIdx_2012_ = lean_ctor_get(v___x_2008_, 3);
v_levelArgs_2013_ = lean_ctor_get(v___x_2008_, 4);
v_newLocalDecls_2014_ = lean_ctor_get(v___x_2008_, 5);
v_newLocalDeclsForMVars_2015_ = lean_ctor_get(v___x_2008_, 6);
v_newLetDecls_2016_ = lean_ctor_get(v___x_2008_, 7);
v_nextExprIdx_2017_ = lean_ctor_get(v___x_2008_, 8);
v_exprMVarArgs_2018_ = lean_ctor_get(v___x_2008_, 9);
v_exprFVarArgs_2019_ = lean_ctor_get(v___x_2008_, 10);
v_toProcess_2020_ = lean_ctor_get(v___x_2008_, 11);
v_isSharedCheck_2031_ = !lean_is_exclusive(v___x_2008_);
if (v_isSharedCheck_2031_ == 0)
{
v___x_2022_ = v___x_2008_;
v_isShared_2023_ = v_isSharedCheck_2031_;
goto v_resetjp_2021_;
}
else
{
lean_inc(v_toProcess_2020_);
lean_inc(v_exprFVarArgs_2019_);
lean_inc(v_exprMVarArgs_2018_);
lean_inc(v_nextExprIdx_2017_);
lean_inc(v_newLetDecls_2016_);
lean_inc(v_newLocalDeclsForMVars_2015_);
lean_inc(v_newLocalDecls_2014_);
lean_inc(v_levelArgs_2013_);
lean_inc(v_nextLevelIdx_2012_);
lean_inc(v_levelParams_2011_);
lean_inc(v_visitedExpr_2010_);
lean_inc(v_visitedLevel_2009_);
lean_dec(v___x_2008_);
v___x_2022_ = lean_box(0);
v_isShared_2023_ = v_isSharedCheck_2031_;
goto v_resetjp_2021_;
}
v_resetjp_2021_:
{
lean_object* v___x_2024_; lean_object* v___x_2026_; 
v___x_2024_ = lean_array_push(v_exprFVarArgs_2019_, v_e_2005_);
if (v_isShared_2023_ == 0)
{
lean_ctor_set(v___x_2022_, 10, v___x_2024_);
v___x_2026_ = v___x_2022_;
goto v_reusejp_2025_;
}
else
{
lean_object* v_reuseFailAlloc_2030_; 
v_reuseFailAlloc_2030_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_2030_, 0, v_visitedLevel_2009_);
lean_ctor_set(v_reuseFailAlloc_2030_, 1, v_visitedExpr_2010_);
lean_ctor_set(v_reuseFailAlloc_2030_, 2, v_levelParams_2011_);
lean_ctor_set(v_reuseFailAlloc_2030_, 3, v_nextLevelIdx_2012_);
lean_ctor_set(v_reuseFailAlloc_2030_, 4, v_levelArgs_2013_);
lean_ctor_set(v_reuseFailAlloc_2030_, 5, v_newLocalDecls_2014_);
lean_ctor_set(v_reuseFailAlloc_2030_, 6, v_newLocalDeclsForMVars_2015_);
lean_ctor_set(v_reuseFailAlloc_2030_, 7, v_newLetDecls_2016_);
lean_ctor_set(v_reuseFailAlloc_2030_, 8, v_nextExprIdx_2017_);
lean_ctor_set(v_reuseFailAlloc_2030_, 9, v_exprMVarArgs_2018_);
lean_ctor_set(v_reuseFailAlloc_2030_, 10, v___x_2024_);
lean_ctor_set(v_reuseFailAlloc_2030_, 11, v_toProcess_2020_);
v___x_2026_ = v_reuseFailAlloc_2030_;
goto v_reusejp_2025_;
}
v_reusejp_2025_:
{
lean_object* v___x_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; 
v___x_2027_ = lean_st_ref_set(v_a_2006_, v___x_2026_);
v___x_2028_ = lean_box(0);
v___x_2029_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2029_, 0, v___x_2028_);
return v___x_2029_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushFVarArg___redArg___boxed(lean_object* v_e_2032_, lean_object* v_a_2033_, lean_object* v_a_2034_){
_start:
{
lean_object* v_res_2035_; 
v_res_2035_ = l_Lean_Meta_Closure_pushFVarArg___redArg(v_e_2032_, v_a_2033_);
lean_dec(v_a_2033_);
return v_res_2035_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushFVarArg(lean_object* v_e_2036_, uint8_t v_a_2037_, lean_object* v_a_2038_, lean_object* v_a_2039_, lean_object* v_a_2040_, lean_object* v_a_2041_, lean_object* v_a_2042_){
_start:
{
lean_object* v___x_2044_; 
v___x_2044_ = l_Lean_Meta_Closure_pushFVarArg___redArg(v_e_2036_, v_a_2038_);
return v___x_2044_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushFVarArg___boxed(lean_object* v_e_2045_, lean_object* v_a_2046_, lean_object* v_a_2047_, lean_object* v_a_2048_, lean_object* v_a_2049_, lean_object* v_a_2050_, lean_object* v_a_2051_, lean_object* v_a_2052_){
_start:
{
uint8_t v_a_boxed_2053_; lean_object* v_res_2054_; 
v_a_boxed_2053_ = lean_unbox(v_a_2046_);
v_res_2054_ = l_Lean_Meta_Closure_pushFVarArg(v_e_2045_, v_a_boxed_2053_, v_a_2047_, v_a_2048_, v_a_2049_, v_a_2050_, v_a_2051_);
lean_dec(v_a_2051_);
lean_dec_ref(v_a_2050_);
lean_dec(v_a_2049_);
lean_dec_ref(v_a_2048_);
lean_dec(v_a_2047_);
return v_res_2054_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushLocalDecl(lean_object* v_newFVarId_2055_, lean_object* v_userName_2056_, lean_object* v_type_2057_, uint8_t v_bi_2058_, uint8_t v_a_2059_, lean_object* v_a_2060_, lean_object* v_a_2061_, lean_object* v_a_2062_, lean_object* v_a_2063_, lean_object* v_a_2064_){
_start:
{
lean_object* v___x_2066_; 
v___x_2066_ = l_Lean_Meta_Closure_collectExpr(v_type_2057_, v_a_2059_, v_a_2060_, v_a_2061_, v_a_2062_, v_a_2063_, v_a_2064_);
if (lean_obj_tag(v___x_2066_) == 0)
{
lean_object* v_a_2067_; lean_object* v___x_2069_; uint8_t v_isShared_2070_; uint8_t v_isSharedCheck_2100_; 
v_a_2067_ = lean_ctor_get(v___x_2066_, 0);
v_isSharedCheck_2100_ = !lean_is_exclusive(v___x_2066_);
if (v_isSharedCheck_2100_ == 0)
{
v___x_2069_ = v___x_2066_;
v_isShared_2070_ = v_isSharedCheck_2100_;
goto v_resetjp_2068_;
}
else
{
lean_inc(v_a_2067_);
lean_dec(v___x_2066_);
v___x_2069_ = lean_box(0);
v_isShared_2070_ = v_isSharedCheck_2100_;
goto v_resetjp_2068_;
}
v_resetjp_2068_:
{
lean_object* v___x_2071_; lean_object* v_visitedLevel_2072_; lean_object* v_visitedExpr_2073_; lean_object* v_levelParams_2074_; lean_object* v_nextLevelIdx_2075_; lean_object* v_levelArgs_2076_; lean_object* v_newLocalDecls_2077_; lean_object* v_newLocalDeclsForMVars_2078_; lean_object* v_newLetDecls_2079_; lean_object* v_nextExprIdx_2080_; lean_object* v_exprMVarArgs_2081_; lean_object* v_exprFVarArgs_2082_; lean_object* v_toProcess_2083_; lean_object* v___x_2085_; uint8_t v_isShared_2086_; uint8_t v_isSharedCheck_2099_; 
v___x_2071_ = lean_st_ref_take(v_a_2060_);
v_visitedLevel_2072_ = lean_ctor_get(v___x_2071_, 0);
v_visitedExpr_2073_ = lean_ctor_get(v___x_2071_, 1);
v_levelParams_2074_ = lean_ctor_get(v___x_2071_, 2);
v_nextLevelIdx_2075_ = lean_ctor_get(v___x_2071_, 3);
v_levelArgs_2076_ = lean_ctor_get(v___x_2071_, 4);
v_newLocalDecls_2077_ = lean_ctor_get(v___x_2071_, 5);
v_newLocalDeclsForMVars_2078_ = lean_ctor_get(v___x_2071_, 6);
v_newLetDecls_2079_ = lean_ctor_get(v___x_2071_, 7);
v_nextExprIdx_2080_ = lean_ctor_get(v___x_2071_, 8);
v_exprMVarArgs_2081_ = lean_ctor_get(v___x_2071_, 9);
v_exprFVarArgs_2082_ = lean_ctor_get(v___x_2071_, 10);
v_toProcess_2083_ = lean_ctor_get(v___x_2071_, 11);
v_isSharedCheck_2099_ = !lean_is_exclusive(v___x_2071_);
if (v_isSharedCheck_2099_ == 0)
{
v___x_2085_ = v___x_2071_;
v_isShared_2086_ = v_isSharedCheck_2099_;
goto v_resetjp_2084_;
}
else
{
lean_inc(v_toProcess_2083_);
lean_inc(v_exprFVarArgs_2082_);
lean_inc(v_exprMVarArgs_2081_);
lean_inc(v_nextExprIdx_2080_);
lean_inc(v_newLetDecls_2079_);
lean_inc(v_newLocalDeclsForMVars_2078_);
lean_inc(v_newLocalDecls_2077_);
lean_inc(v_levelArgs_2076_);
lean_inc(v_nextLevelIdx_2075_);
lean_inc(v_levelParams_2074_);
lean_inc(v_visitedExpr_2073_);
lean_inc(v_visitedLevel_2072_);
lean_dec(v___x_2071_);
v___x_2085_ = lean_box(0);
v_isShared_2086_ = v_isSharedCheck_2099_;
goto v_resetjp_2084_;
}
v_resetjp_2084_:
{
lean_object* v___x_2087_; uint8_t v___x_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2092_; 
v___x_2087_ = lean_unsigned_to_nat(0u);
v___x_2088_ = 0;
v___x_2089_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2089_, 0, v___x_2087_);
lean_ctor_set(v___x_2089_, 1, v_newFVarId_2055_);
lean_ctor_set(v___x_2089_, 2, v_userName_2056_);
lean_ctor_set(v___x_2089_, 3, v_a_2067_);
lean_ctor_set_uint8(v___x_2089_, sizeof(void*)*4, v_bi_2058_);
lean_ctor_set_uint8(v___x_2089_, sizeof(void*)*4 + 1, v___x_2088_);
v___x_2090_ = lean_array_push(v_newLocalDecls_2077_, v___x_2089_);
if (v_isShared_2086_ == 0)
{
lean_ctor_set(v___x_2085_, 5, v___x_2090_);
v___x_2092_ = v___x_2085_;
goto v_reusejp_2091_;
}
else
{
lean_object* v_reuseFailAlloc_2098_; 
v_reuseFailAlloc_2098_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_2098_, 0, v_visitedLevel_2072_);
lean_ctor_set(v_reuseFailAlloc_2098_, 1, v_visitedExpr_2073_);
lean_ctor_set(v_reuseFailAlloc_2098_, 2, v_levelParams_2074_);
lean_ctor_set(v_reuseFailAlloc_2098_, 3, v_nextLevelIdx_2075_);
lean_ctor_set(v_reuseFailAlloc_2098_, 4, v_levelArgs_2076_);
lean_ctor_set(v_reuseFailAlloc_2098_, 5, v___x_2090_);
lean_ctor_set(v_reuseFailAlloc_2098_, 6, v_newLocalDeclsForMVars_2078_);
lean_ctor_set(v_reuseFailAlloc_2098_, 7, v_newLetDecls_2079_);
lean_ctor_set(v_reuseFailAlloc_2098_, 8, v_nextExprIdx_2080_);
lean_ctor_set(v_reuseFailAlloc_2098_, 9, v_exprMVarArgs_2081_);
lean_ctor_set(v_reuseFailAlloc_2098_, 10, v_exprFVarArgs_2082_);
lean_ctor_set(v_reuseFailAlloc_2098_, 11, v_toProcess_2083_);
v___x_2092_ = v_reuseFailAlloc_2098_;
goto v_reusejp_2091_;
}
v_reusejp_2091_:
{
lean_object* v___x_2093_; lean_object* v___x_2094_; lean_object* v___x_2096_; 
v___x_2093_ = lean_st_ref_set(v_a_2060_, v___x_2092_);
v___x_2094_ = lean_box(0);
if (v_isShared_2070_ == 0)
{
lean_ctor_set(v___x_2069_, 0, v___x_2094_);
v___x_2096_ = v___x_2069_;
goto v_reusejp_2095_;
}
else
{
lean_object* v_reuseFailAlloc_2097_; 
v_reuseFailAlloc_2097_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2097_, 0, v___x_2094_);
v___x_2096_ = v_reuseFailAlloc_2097_;
goto v_reusejp_2095_;
}
v_reusejp_2095_:
{
return v___x_2096_;
}
}
}
}
}
else
{
lean_object* v_a_2101_; lean_object* v___x_2103_; uint8_t v_isShared_2104_; uint8_t v_isSharedCheck_2108_; 
lean_dec(v_userName_2056_);
lean_dec(v_newFVarId_2055_);
v_a_2101_ = lean_ctor_get(v___x_2066_, 0);
v_isSharedCheck_2108_ = !lean_is_exclusive(v___x_2066_);
if (v_isSharedCheck_2108_ == 0)
{
v___x_2103_ = v___x_2066_;
v_isShared_2104_ = v_isSharedCheck_2108_;
goto v_resetjp_2102_;
}
else
{
lean_inc(v_a_2101_);
lean_dec(v___x_2066_);
v___x_2103_ = lean_box(0);
v_isShared_2104_ = v_isSharedCheck_2108_;
goto v_resetjp_2102_;
}
v_resetjp_2102_:
{
lean_object* v___x_2106_; 
if (v_isShared_2104_ == 0)
{
v___x_2106_ = v___x_2103_;
goto v_reusejp_2105_;
}
else
{
lean_object* v_reuseFailAlloc_2107_; 
v_reuseFailAlloc_2107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2107_, 0, v_a_2101_);
v___x_2106_ = v_reuseFailAlloc_2107_;
goto v_reusejp_2105_;
}
v_reusejp_2105_:
{
return v___x_2106_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushLocalDecl___boxed(lean_object* v_newFVarId_2109_, lean_object* v_userName_2110_, lean_object* v_type_2111_, lean_object* v_bi_2112_, lean_object* v_a_2113_, lean_object* v_a_2114_, lean_object* v_a_2115_, lean_object* v_a_2116_, lean_object* v_a_2117_, lean_object* v_a_2118_, lean_object* v_a_2119_){
_start:
{
uint8_t v_bi_boxed_2120_; uint8_t v_a_boxed_2121_; lean_object* v_res_2122_; 
v_bi_boxed_2120_ = lean_unbox(v_bi_2112_);
v_a_boxed_2121_ = lean_unbox(v_a_2113_);
v_res_2122_ = l_Lean_Meta_Closure_pushLocalDecl(v_newFVarId_2109_, v_userName_2110_, v_type_2111_, v_bi_boxed_2120_, v_a_boxed_2121_, v_a_2114_, v_a_2115_, v_a_2116_, v_a_2117_, v_a_2118_);
lean_dec(v_a_2118_);
lean_dec_ref(v_a_2117_);
lean_dec(v_a_2116_);
lean_dec_ref(v_a_2115_);
lean_dec(v_a_2114_);
return v_res_2122_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Closure_process_spec__0___redArg(lean_object* v_k_2123_, lean_object* v_t_2124_){
_start:
{
if (lean_obj_tag(v_t_2124_) == 0)
{
lean_object* v_k_2125_; lean_object* v_l_2126_; lean_object* v_r_2127_; uint8_t v___x_2128_; 
v_k_2125_ = lean_ctor_get(v_t_2124_, 1);
v_l_2126_ = lean_ctor_get(v_t_2124_, 3);
v_r_2127_ = lean_ctor_get(v_t_2124_, 4);
v___x_2128_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_2123_, v_k_2125_);
switch(v___x_2128_)
{
case 0:
{
v_t_2124_ = v_l_2126_;
goto _start;
}
case 1:
{
uint8_t v___x_2130_; 
v___x_2130_ = 1;
return v___x_2130_;
}
default: 
{
v_t_2124_ = v_r_2127_;
goto _start;
}
}
}
else
{
uint8_t v___x_2132_; 
v___x_2132_ = 0;
return v___x_2132_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Closure_process_spec__0___redArg___boxed(lean_object* v_k_2133_, lean_object* v_t_2134_){
_start:
{
uint8_t v_res_2135_; lean_object* v_r_2136_; 
v_res_2135_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Closure_process_spec__0___redArg(v_k_2133_, v_t_2134_);
lean_dec(v_t_2134_);
lean_dec(v_k_2133_);
v_r_2136_ = lean_box(v_res_2135_);
return v_r_2136_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Closure_process_spec__1(lean_object* v_newFVarId_2137_, lean_object* v_a_2138_, size_t v_sz_2139_, size_t v_i_2140_, lean_object* v_bs_2141_){
_start:
{
uint8_t v___x_2142_; 
v___x_2142_ = lean_usize_dec_lt(v_i_2140_, v_sz_2139_);
if (v___x_2142_ == 0)
{
lean_dec(v_newFVarId_2137_);
return v_bs_2141_;
}
else
{
lean_object* v_v_2143_; lean_object* v___x_2144_; lean_object* v_bs_x27_2145_; lean_object* v___x_2146_; size_t v___x_2147_; size_t v___x_2148_; lean_object* v___x_2149_; 
v_v_2143_ = lean_array_uget(v_bs_2141_, v_i_2140_);
v___x_2144_ = lean_unsigned_to_nat(0u);
v_bs_x27_2145_ = lean_array_uset(v_bs_2141_, v_i_2140_, v___x_2144_);
lean_inc(v_newFVarId_2137_);
v___x_2146_ = l_Lean_LocalDecl_replaceFVarId(v_newFVarId_2137_, v_a_2138_, v_v_2143_);
v___x_2147_ = ((size_t)1ULL);
v___x_2148_ = lean_usize_add(v_i_2140_, v___x_2147_);
v___x_2149_ = lean_array_uset(v_bs_x27_2145_, v_i_2140_, v___x_2146_);
v_i_2140_ = v___x_2148_;
v_bs_2141_ = v___x_2149_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Closure_process_spec__1___boxed(lean_object* v_newFVarId_2151_, lean_object* v_a_2152_, lean_object* v_sz_2153_, lean_object* v_i_2154_, lean_object* v_bs_2155_){
_start:
{
size_t v_sz_boxed_2156_; size_t v_i_boxed_2157_; lean_object* v_res_2158_; 
v_sz_boxed_2156_ = lean_unbox_usize(v_sz_2153_);
lean_dec(v_sz_2153_);
v_i_boxed_2157_ = lean_unbox_usize(v_i_2154_);
lean_dec(v_i_2154_);
v_res_2158_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Closure_process_spec__1(v_newFVarId_2151_, v_a_2152_, v_sz_boxed_2156_, v_i_boxed_2157_, v_bs_2155_);
lean_dec_ref(v_a_2152_);
return v_res_2158_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_process(uint8_t v_a_2159_, lean_object* v_a_2160_, lean_object* v_a_2161_, lean_object* v_a_2162_, lean_object* v_a_2163_, lean_object* v_a_2164_){
_start:
{
lean_object* v___x_2166_; 
v___x_2166_ = l_Lean_Meta_Closure_pickNextToProcess_x3f___redArg(v_a_2160_, v_a_2161_);
if (lean_obj_tag(v___x_2166_) == 0)
{
lean_object* v_a_2167_; lean_object* v___x_2169_; uint8_t v_isShared_2170_; uint8_t v_isSharedCheck_2294_; 
v_a_2167_ = lean_ctor_get(v___x_2166_, 0);
v_isSharedCheck_2294_ = !lean_is_exclusive(v___x_2166_);
if (v_isSharedCheck_2294_ == 0)
{
v___x_2169_ = v___x_2166_;
v_isShared_2170_ = v_isSharedCheck_2294_;
goto v_resetjp_2168_;
}
else
{
lean_inc(v_a_2167_);
lean_dec(v___x_2166_);
v___x_2169_ = lean_box(0);
v_isShared_2170_ = v_isSharedCheck_2294_;
goto v_resetjp_2168_;
}
v_resetjp_2168_:
{
if (lean_obj_tag(v_a_2167_) == 0)
{
lean_object* v___x_2171_; lean_object* v___x_2173_; 
v___x_2171_ = lean_box(0);
if (v_isShared_2170_ == 0)
{
lean_ctor_set(v___x_2169_, 0, v___x_2171_);
v___x_2173_ = v___x_2169_;
goto v_reusejp_2172_;
}
else
{
lean_object* v_reuseFailAlloc_2174_; 
v_reuseFailAlloc_2174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2174_, 0, v___x_2171_);
v___x_2173_ = v_reuseFailAlloc_2174_;
goto v_reusejp_2172_;
}
v_reusejp_2172_:
{
return v___x_2173_;
}
}
else
{
lean_object* v_val_2175_; lean_object* v_fvarId_2176_; lean_object* v_newFVarId_2177_; lean_object* v___x_2178_; 
lean_del_object(v___x_2169_);
v_val_2175_ = lean_ctor_get(v_a_2167_, 0);
lean_inc(v_val_2175_);
lean_dec_ref(v_a_2167_);
v_fvarId_2176_ = lean_ctor_get(v_val_2175_, 0);
lean_inc_n(v_fvarId_2176_, 2);
v_newFVarId_2177_ = lean_ctor_get(v_val_2175_, 1);
lean_inc(v_newFVarId_2177_);
lean_dec(v_val_2175_);
v___x_2178_ = l_Lean_FVarId_getDecl___redArg(v_fvarId_2176_, v_a_2161_, v_a_2163_, v_a_2164_);
if (lean_obj_tag(v___x_2178_) == 0)
{
lean_object* v_a_2179_; 
v_a_2179_ = lean_ctor_get(v___x_2178_, 0);
lean_inc(v_a_2179_);
lean_dec_ref(v___x_2178_);
if (lean_obj_tag(v_a_2179_) == 0)
{
lean_object* v_userName_2180_; lean_object* v_type_2181_; uint8_t v_bi_2182_; lean_object* v___x_2183_; 
v_userName_2180_ = lean_ctor_get(v_a_2179_, 2);
lean_inc(v_userName_2180_);
v_type_2181_ = lean_ctor_get(v_a_2179_, 3);
lean_inc_ref(v_type_2181_);
v_bi_2182_ = lean_ctor_get_uint8(v_a_2179_, sizeof(void*)*4);
lean_dec_ref(v_a_2179_);
v___x_2183_ = l_Lean_Meta_Closure_pushLocalDecl(v_newFVarId_2177_, v_userName_2180_, v_type_2181_, v_bi_2182_, v_a_2159_, v_a_2160_, v_a_2161_, v_a_2162_, v_a_2163_, v_a_2164_);
if (lean_obj_tag(v___x_2183_) == 0)
{
lean_object* v___x_2184_; lean_object* v___x_2185_; 
lean_dec_ref(v___x_2183_);
v___x_2184_ = l_Lean_mkFVar(v_fvarId_2176_);
v___x_2185_ = l_Lean_Meta_Closure_pushFVarArg___redArg(v___x_2184_, v_a_2160_);
if (lean_obj_tag(v___x_2185_) == 0)
{
lean_dec_ref(v___x_2185_);
goto _start;
}
else
{
return v___x_2185_;
}
}
else
{
lean_dec(v_fvarId_2176_);
return v___x_2183_;
}
}
else
{
lean_object* v_userName_2187_; lean_object* v_type_2188_; lean_object* v_value_2189_; uint8_t v_nondep_2190_; lean_object* v___x_2192_; uint8_t v_isShared_2193_; uint8_t v_isSharedCheck_2283_; 
v_userName_2187_ = lean_ctor_get(v_a_2179_, 2);
v_type_2188_ = lean_ctor_get(v_a_2179_, 3);
v_value_2189_ = lean_ctor_get(v_a_2179_, 4);
v_nondep_2190_ = lean_ctor_get_uint8(v_a_2179_, sizeof(void*)*5);
v_isSharedCheck_2283_ = !lean_is_exclusive(v_a_2179_);
if (v_isSharedCheck_2283_ == 0)
{
lean_object* v_unused_2284_; lean_object* v_unused_2285_; 
v_unused_2284_ = lean_ctor_get(v_a_2179_, 1);
lean_dec(v_unused_2284_);
v_unused_2285_ = lean_ctor_get(v_a_2179_, 0);
lean_dec(v_unused_2285_);
v___x_2192_ = v_a_2179_;
v_isShared_2193_ = v_isSharedCheck_2283_;
goto v_resetjp_2191_;
}
else
{
lean_inc(v_value_2189_);
lean_inc(v_type_2188_);
lean_inc(v_userName_2187_);
lean_dec(v_a_2179_);
v___x_2192_ = lean_box(0);
v_isShared_2193_ = v_isSharedCheck_2283_;
goto v_resetjp_2191_;
}
v_resetjp_2191_:
{
lean_object* v___x_2194_; 
v___x_2194_ = l_Lean_Meta_getZetaDeltaFVarIds___redArg(v_a_2162_);
if (lean_obj_tag(v___x_2194_) == 0)
{
lean_object* v_a_2195_; 
v_a_2195_ = lean_ctor_get(v___x_2194_, 0);
lean_inc(v_a_2195_);
lean_dec_ref(v___x_2194_);
if (v_nondep_2190_ == 0)
{
uint8_t v___x_2202_; 
v___x_2202_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Closure_process_spec__0___redArg(v_fvarId_2176_, v_a_2195_);
lean_dec(v_a_2195_);
if (v___x_2202_ == 0)
{
lean_del_object(v___x_2192_);
lean_dec_ref(v_value_2189_);
goto v___jp_2196_;
}
else
{
lean_object* v___x_2203_; 
lean_dec(v_fvarId_2176_);
v___x_2203_ = l_Lean_Meta_Closure_collectExpr(v_type_2188_, v_a_2159_, v_a_2160_, v_a_2161_, v_a_2162_, v_a_2163_, v_a_2164_);
if (lean_obj_tag(v___x_2203_) == 0)
{
lean_object* v_a_2204_; lean_object* v___x_2205_; 
v_a_2204_ = lean_ctor_get(v___x_2203_, 0);
lean_inc(v_a_2204_);
lean_dec_ref(v___x_2203_);
v___x_2205_ = l_Lean_Meta_Closure_collectExpr(v_value_2189_, v_a_2159_, v_a_2160_, v_a_2161_, v_a_2162_, v_a_2163_, v_a_2164_);
if (lean_obj_tag(v___x_2205_) == 0)
{
lean_object* v_a_2206_; lean_object* v___x_2207_; lean_object* v_visitedLevel_2208_; lean_object* v_visitedExpr_2209_; lean_object* v_levelParams_2210_; lean_object* v_nextLevelIdx_2211_; lean_object* v_levelArgs_2212_; lean_object* v_newLocalDecls_2213_; lean_object* v_newLocalDeclsForMVars_2214_; lean_object* v_newLetDecls_2215_; lean_object* v_nextExprIdx_2216_; lean_object* v_exprMVarArgs_2217_; lean_object* v_exprFVarArgs_2218_; lean_object* v_toProcess_2219_; lean_object* v___x_2221_; uint8_t v_isShared_2222_; uint8_t v_isSharedCheck_2258_; 
v_a_2206_ = lean_ctor_get(v___x_2205_, 0);
lean_inc(v_a_2206_);
lean_dec_ref(v___x_2205_);
v___x_2207_ = lean_st_ref_take(v_a_2160_);
v_visitedLevel_2208_ = lean_ctor_get(v___x_2207_, 0);
v_visitedExpr_2209_ = lean_ctor_get(v___x_2207_, 1);
v_levelParams_2210_ = lean_ctor_get(v___x_2207_, 2);
v_nextLevelIdx_2211_ = lean_ctor_get(v___x_2207_, 3);
v_levelArgs_2212_ = lean_ctor_get(v___x_2207_, 4);
v_newLocalDecls_2213_ = lean_ctor_get(v___x_2207_, 5);
v_newLocalDeclsForMVars_2214_ = lean_ctor_get(v___x_2207_, 6);
v_newLetDecls_2215_ = lean_ctor_get(v___x_2207_, 7);
v_nextExprIdx_2216_ = lean_ctor_get(v___x_2207_, 8);
v_exprMVarArgs_2217_ = lean_ctor_get(v___x_2207_, 9);
v_exprFVarArgs_2218_ = lean_ctor_get(v___x_2207_, 10);
v_toProcess_2219_ = lean_ctor_get(v___x_2207_, 11);
v_isSharedCheck_2258_ = !lean_is_exclusive(v___x_2207_);
if (v_isSharedCheck_2258_ == 0)
{
v___x_2221_ = v___x_2207_;
v_isShared_2222_ = v_isSharedCheck_2258_;
goto v_resetjp_2220_;
}
else
{
lean_inc(v_toProcess_2219_);
lean_inc(v_exprFVarArgs_2218_);
lean_inc(v_exprMVarArgs_2217_);
lean_inc(v_nextExprIdx_2216_);
lean_inc(v_newLetDecls_2215_);
lean_inc(v_newLocalDeclsForMVars_2214_);
lean_inc(v_newLocalDecls_2213_);
lean_inc(v_levelArgs_2212_);
lean_inc(v_nextLevelIdx_2211_);
lean_inc(v_levelParams_2210_);
lean_inc(v_visitedExpr_2209_);
lean_inc(v_visitedLevel_2208_);
lean_dec(v___x_2207_);
v___x_2221_ = lean_box(0);
v_isShared_2222_ = v_isSharedCheck_2258_;
goto v_resetjp_2220_;
}
v_resetjp_2220_:
{
lean_object* v___x_2223_; uint8_t v___x_2224_; lean_object* v___x_2226_; 
v___x_2223_ = lean_unsigned_to_nat(0u);
v___x_2224_ = 0;
lean_inc(v_a_2206_);
lean_inc(v_newFVarId_2177_);
if (v_isShared_2193_ == 0)
{
lean_ctor_set(v___x_2192_, 4, v_a_2206_);
lean_ctor_set(v___x_2192_, 3, v_a_2204_);
lean_ctor_set(v___x_2192_, 1, v_newFVarId_2177_);
lean_ctor_set(v___x_2192_, 0, v___x_2223_);
v___x_2226_ = v___x_2192_;
goto v_reusejp_2225_;
}
else
{
lean_object* v_reuseFailAlloc_2257_; 
v_reuseFailAlloc_2257_ = lean_alloc_ctor(1, 5, 2);
lean_ctor_set(v_reuseFailAlloc_2257_, 0, v___x_2223_);
lean_ctor_set(v_reuseFailAlloc_2257_, 1, v_newFVarId_2177_);
lean_ctor_set(v_reuseFailAlloc_2257_, 2, v_userName_2187_);
lean_ctor_set(v_reuseFailAlloc_2257_, 3, v_a_2204_);
lean_ctor_set(v_reuseFailAlloc_2257_, 4, v_a_2206_);
lean_ctor_set_uint8(v_reuseFailAlloc_2257_, sizeof(void*)*5, v_nondep_2190_);
v___x_2226_ = v_reuseFailAlloc_2257_;
goto v_reusejp_2225_;
}
v_reusejp_2225_:
{
lean_object* v___x_2227_; lean_object* v___x_2229_; 
lean_ctor_set_uint8(v___x_2226_, sizeof(void*)*5 + 1, v___x_2224_);
v___x_2227_ = lean_array_push(v_newLetDecls_2215_, v___x_2226_);
if (v_isShared_2222_ == 0)
{
lean_ctor_set(v___x_2221_, 7, v___x_2227_);
v___x_2229_ = v___x_2221_;
goto v_reusejp_2228_;
}
else
{
lean_object* v_reuseFailAlloc_2256_; 
v_reuseFailAlloc_2256_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_2256_, 0, v_visitedLevel_2208_);
lean_ctor_set(v_reuseFailAlloc_2256_, 1, v_visitedExpr_2209_);
lean_ctor_set(v_reuseFailAlloc_2256_, 2, v_levelParams_2210_);
lean_ctor_set(v_reuseFailAlloc_2256_, 3, v_nextLevelIdx_2211_);
lean_ctor_set(v_reuseFailAlloc_2256_, 4, v_levelArgs_2212_);
lean_ctor_set(v_reuseFailAlloc_2256_, 5, v_newLocalDecls_2213_);
lean_ctor_set(v_reuseFailAlloc_2256_, 6, v_newLocalDeclsForMVars_2214_);
lean_ctor_set(v_reuseFailAlloc_2256_, 7, v___x_2227_);
lean_ctor_set(v_reuseFailAlloc_2256_, 8, v_nextExprIdx_2216_);
lean_ctor_set(v_reuseFailAlloc_2256_, 9, v_exprMVarArgs_2217_);
lean_ctor_set(v_reuseFailAlloc_2256_, 10, v_exprFVarArgs_2218_);
lean_ctor_set(v_reuseFailAlloc_2256_, 11, v_toProcess_2219_);
v___x_2229_ = v_reuseFailAlloc_2256_;
goto v_reusejp_2228_;
}
v_reusejp_2228_:
{
lean_object* v___x_2230_; lean_object* v___x_2231_; lean_object* v_visitedLevel_2232_; lean_object* v_visitedExpr_2233_; lean_object* v_levelParams_2234_; lean_object* v_nextLevelIdx_2235_; lean_object* v_levelArgs_2236_; lean_object* v_newLocalDecls_2237_; lean_object* v_newLocalDeclsForMVars_2238_; lean_object* v_newLetDecls_2239_; lean_object* v_nextExprIdx_2240_; lean_object* v_exprMVarArgs_2241_; lean_object* v_exprFVarArgs_2242_; lean_object* v_toProcess_2243_; lean_object* v___x_2245_; uint8_t v_isShared_2246_; uint8_t v_isSharedCheck_2255_; 
v___x_2230_ = lean_st_ref_set(v_a_2160_, v___x_2229_);
v___x_2231_ = lean_st_ref_take(v_a_2160_);
v_visitedLevel_2232_ = lean_ctor_get(v___x_2231_, 0);
v_visitedExpr_2233_ = lean_ctor_get(v___x_2231_, 1);
v_levelParams_2234_ = lean_ctor_get(v___x_2231_, 2);
v_nextLevelIdx_2235_ = lean_ctor_get(v___x_2231_, 3);
v_levelArgs_2236_ = lean_ctor_get(v___x_2231_, 4);
v_newLocalDecls_2237_ = lean_ctor_get(v___x_2231_, 5);
v_newLocalDeclsForMVars_2238_ = lean_ctor_get(v___x_2231_, 6);
v_newLetDecls_2239_ = lean_ctor_get(v___x_2231_, 7);
v_nextExprIdx_2240_ = lean_ctor_get(v___x_2231_, 8);
v_exprMVarArgs_2241_ = lean_ctor_get(v___x_2231_, 9);
v_exprFVarArgs_2242_ = lean_ctor_get(v___x_2231_, 10);
v_toProcess_2243_ = lean_ctor_get(v___x_2231_, 11);
v_isSharedCheck_2255_ = !lean_is_exclusive(v___x_2231_);
if (v_isSharedCheck_2255_ == 0)
{
v___x_2245_ = v___x_2231_;
v_isShared_2246_ = v_isSharedCheck_2255_;
goto v_resetjp_2244_;
}
else
{
lean_inc(v_toProcess_2243_);
lean_inc(v_exprFVarArgs_2242_);
lean_inc(v_exprMVarArgs_2241_);
lean_inc(v_nextExprIdx_2240_);
lean_inc(v_newLetDecls_2239_);
lean_inc(v_newLocalDeclsForMVars_2238_);
lean_inc(v_newLocalDecls_2237_);
lean_inc(v_levelArgs_2236_);
lean_inc(v_nextLevelIdx_2235_);
lean_inc(v_levelParams_2234_);
lean_inc(v_visitedExpr_2233_);
lean_inc(v_visitedLevel_2232_);
lean_dec(v___x_2231_);
v___x_2245_ = lean_box(0);
v_isShared_2246_ = v_isSharedCheck_2255_;
goto v_resetjp_2244_;
}
v_resetjp_2244_:
{
size_t v_sz_2247_; size_t v___x_2248_; lean_object* v___x_2249_; lean_object* v___x_2251_; 
v_sz_2247_ = lean_array_size(v_newLocalDecls_2237_);
v___x_2248_ = ((size_t)0ULL);
v___x_2249_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Closure_process_spec__1(v_newFVarId_2177_, v_a_2206_, v_sz_2247_, v___x_2248_, v_newLocalDecls_2237_);
lean_dec(v_a_2206_);
if (v_isShared_2246_ == 0)
{
lean_ctor_set(v___x_2245_, 5, v___x_2249_);
v___x_2251_ = v___x_2245_;
goto v_reusejp_2250_;
}
else
{
lean_object* v_reuseFailAlloc_2254_; 
v_reuseFailAlloc_2254_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_2254_, 0, v_visitedLevel_2232_);
lean_ctor_set(v_reuseFailAlloc_2254_, 1, v_visitedExpr_2233_);
lean_ctor_set(v_reuseFailAlloc_2254_, 2, v_levelParams_2234_);
lean_ctor_set(v_reuseFailAlloc_2254_, 3, v_nextLevelIdx_2235_);
lean_ctor_set(v_reuseFailAlloc_2254_, 4, v_levelArgs_2236_);
lean_ctor_set(v_reuseFailAlloc_2254_, 5, v___x_2249_);
lean_ctor_set(v_reuseFailAlloc_2254_, 6, v_newLocalDeclsForMVars_2238_);
lean_ctor_set(v_reuseFailAlloc_2254_, 7, v_newLetDecls_2239_);
lean_ctor_set(v_reuseFailAlloc_2254_, 8, v_nextExprIdx_2240_);
lean_ctor_set(v_reuseFailAlloc_2254_, 9, v_exprMVarArgs_2241_);
lean_ctor_set(v_reuseFailAlloc_2254_, 10, v_exprFVarArgs_2242_);
lean_ctor_set(v_reuseFailAlloc_2254_, 11, v_toProcess_2243_);
v___x_2251_ = v_reuseFailAlloc_2254_;
goto v_reusejp_2250_;
}
v_reusejp_2250_:
{
lean_object* v___x_2252_; 
v___x_2252_ = lean_st_ref_set(v_a_2160_, v___x_2251_);
goto _start;
}
}
}
}
}
}
else
{
lean_object* v_a_2259_; lean_object* v___x_2261_; uint8_t v_isShared_2262_; uint8_t v_isSharedCheck_2266_; 
lean_dec(v_a_2204_);
lean_del_object(v___x_2192_);
lean_dec(v_userName_2187_);
lean_dec(v_newFVarId_2177_);
v_a_2259_ = lean_ctor_get(v___x_2205_, 0);
v_isSharedCheck_2266_ = !lean_is_exclusive(v___x_2205_);
if (v_isSharedCheck_2266_ == 0)
{
v___x_2261_ = v___x_2205_;
v_isShared_2262_ = v_isSharedCheck_2266_;
goto v_resetjp_2260_;
}
else
{
lean_inc(v_a_2259_);
lean_dec(v___x_2205_);
v___x_2261_ = lean_box(0);
v_isShared_2262_ = v_isSharedCheck_2266_;
goto v_resetjp_2260_;
}
v_resetjp_2260_:
{
lean_object* v___x_2264_; 
if (v_isShared_2262_ == 0)
{
v___x_2264_ = v___x_2261_;
goto v_reusejp_2263_;
}
else
{
lean_object* v_reuseFailAlloc_2265_; 
v_reuseFailAlloc_2265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2265_, 0, v_a_2259_);
v___x_2264_ = v_reuseFailAlloc_2265_;
goto v_reusejp_2263_;
}
v_reusejp_2263_:
{
return v___x_2264_;
}
}
}
}
else
{
lean_object* v_a_2267_; lean_object* v___x_2269_; uint8_t v_isShared_2270_; uint8_t v_isSharedCheck_2274_; 
lean_del_object(v___x_2192_);
lean_dec_ref(v_value_2189_);
lean_dec(v_userName_2187_);
lean_dec(v_newFVarId_2177_);
v_a_2267_ = lean_ctor_get(v___x_2203_, 0);
v_isSharedCheck_2274_ = !lean_is_exclusive(v___x_2203_);
if (v_isSharedCheck_2274_ == 0)
{
v___x_2269_ = v___x_2203_;
v_isShared_2270_ = v_isSharedCheck_2274_;
goto v_resetjp_2268_;
}
else
{
lean_inc(v_a_2267_);
lean_dec(v___x_2203_);
v___x_2269_ = lean_box(0);
v_isShared_2270_ = v_isSharedCheck_2274_;
goto v_resetjp_2268_;
}
v_resetjp_2268_:
{
lean_object* v___x_2272_; 
if (v_isShared_2270_ == 0)
{
v___x_2272_ = v___x_2269_;
goto v_reusejp_2271_;
}
else
{
lean_object* v_reuseFailAlloc_2273_; 
v_reuseFailAlloc_2273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2273_, 0, v_a_2267_);
v___x_2272_ = v_reuseFailAlloc_2273_;
goto v_reusejp_2271_;
}
v_reusejp_2271_:
{
return v___x_2272_;
}
}
}
}
}
else
{
lean_dec(v_a_2195_);
lean_del_object(v___x_2192_);
lean_dec_ref(v_value_2189_);
goto v___jp_2196_;
}
v___jp_2196_:
{
uint8_t v___x_2197_; lean_object* v___x_2198_; 
v___x_2197_ = 0;
v___x_2198_ = l_Lean_Meta_Closure_pushLocalDecl(v_newFVarId_2177_, v_userName_2187_, v_type_2188_, v___x_2197_, v_a_2159_, v_a_2160_, v_a_2161_, v_a_2162_, v_a_2163_, v_a_2164_);
if (lean_obj_tag(v___x_2198_) == 0)
{
lean_object* v___x_2199_; lean_object* v___x_2200_; 
lean_dec_ref(v___x_2198_);
v___x_2199_ = l_Lean_mkFVar(v_fvarId_2176_);
v___x_2200_ = l_Lean_Meta_Closure_pushFVarArg___redArg(v___x_2199_, v_a_2160_);
if (lean_obj_tag(v___x_2200_) == 0)
{
lean_dec_ref(v___x_2200_);
goto _start;
}
else
{
return v___x_2200_;
}
}
else
{
lean_dec(v_fvarId_2176_);
return v___x_2198_;
}
}
}
else
{
lean_object* v_a_2275_; lean_object* v___x_2277_; uint8_t v_isShared_2278_; uint8_t v_isSharedCheck_2282_; 
lean_del_object(v___x_2192_);
lean_dec_ref(v_value_2189_);
lean_dec_ref(v_type_2188_);
lean_dec(v_userName_2187_);
lean_dec(v_newFVarId_2177_);
lean_dec(v_fvarId_2176_);
v_a_2275_ = lean_ctor_get(v___x_2194_, 0);
v_isSharedCheck_2282_ = !lean_is_exclusive(v___x_2194_);
if (v_isSharedCheck_2282_ == 0)
{
v___x_2277_ = v___x_2194_;
v_isShared_2278_ = v_isSharedCheck_2282_;
goto v_resetjp_2276_;
}
else
{
lean_inc(v_a_2275_);
lean_dec(v___x_2194_);
v___x_2277_ = lean_box(0);
v_isShared_2278_ = v_isSharedCheck_2282_;
goto v_resetjp_2276_;
}
v_resetjp_2276_:
{
lean_object* v___x_2280_; 
if (v_isShared_2278_ == 0)
{
v___x_2280_ = v___x_2277_;
goto v_reusejp_2279_;
}
else
{
lean_object* v_reuseFailAlloc_2281_; 
v_reuseFailAlloc_2281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2281_, 0, v_a_2275_);
v___x_2280_ = v_reuseFailAlloc_2281_;
goto v_reusejp_2279_;
}
v_reusejp_2279_:
{
return v___x_2280_;
}
}
}
}
}
}
else
{
lean_object* v_a_2286_; lean_object* v___x_2288_; uint8_t v_isShared_2289_; uint8_t v_isSharedCheck_2293_; 
lean_dec(v_newFVarId_2177_);
lean_dec(v_fvarId_2176_);
v_a_2286_ = lean_ctor_get(v___x_2178_, 0);
v_isSharedCheck_2293_ = !lean_is_exclusive(v___x_2178_);
if (v_isSharedCheck_2293_ == 0)
{
v___x_2288_ = v___x_2178_;
v_isShared_2289_ = v_isSharedCheck_2293_;
goto v_resetjp_2287_;
}
else
{
lean_inc(v_a_2286_);
lean_dec(v___x_2178_);
v___x_2288_ = lean_box(0);
v_isShared_2289_ = v_isSharedCheck_2293_;
goto v_resetjp_2287_;
}
v_resetjp_2287_:
{
lean_object* v___x_2291_; 
if (v_isShared_2289_ == 0)
{
v___x_2291_ = v___x_2288_;
goto v_reusejp_2290_;
}
else
{
lean_object* v_reuseFailAlloc_2292_; 
v_reuseFailAlloc_2292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2292_, 0, v_a_2286_);
v___x_2291_ = v_reuseFailAlloc_2292_;
goto v_reusejp_2290_;
}
v_reusejp_2290_:
{
return v___x_2291_;
}
}
}
}
}
}
else
{
lean_object* v_a_2295_; lean_object* v___x_2297_; uint8_t v_isShared_2298_; uint8_t v_isSharedCheck_2302_; 
v_a_2295_ = lean_ctor_get(v___x_2166_, 0);
v_isSharedCheck_2302_ = !lean_is_exclusive(v___x_2166_);
if (v_isSharedCheck_2302_ == 0)
{
v___x_2297_ = v___x_2166_;
v_isShared_2298_ = v_isSharedCheck_2302_;
goto v_resetjp_2296_;
}
else
{
lean_inc(v_a_2295_);
lean_dec(v___x_2166_);
v___x_2297_ = lean_box(0);
v_isShared_2298_ = v_isSharedCheck_2302_;
goto v_resetjp_2296_;
}
v_resetjp_2296_:
{
lean_object* v___x_2300_; 
if (v_isShared_2298_ == 0)
{
v___x_2300_ = v___x_2297_;
goto v_reusejp_2299_;
}
else
{
lean_object* v_reuseFailAlloc_2301_; 
v_reuseFailAlloc_2301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2301_, 0, v_a_2295_);
v___x_2300_ = v_reuseFailAlloc_2301_;
goto v_reusejp_2299_;
}
v_reusejp_2299_:
{
return v___x_2300_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_process___boxed(lean_object* v_a_2303_, lean_object* v_a_2304_, lean_object* v_a_2305_, lean_object* v_a_2306_, lean_object* v_a_2307_, lean_object* v_a_2308_, lean_object* v_a_2309_){
_start:
{
uint8_t v_a_boxed_2310_; lean_object* v_res_2311_; 
v_a_boxed_2310_ = lean_unbox(v_a_2303_);
v_res_2311_ = l_Lean_Meta_Closure_process(v_a_boxed_2310_, v_a_2304_, v_a_2305_, v_a_2306_, v_a_2307_, v_a_2308_);
lean_dec(v_a_2308_);
lean_dec_ref(v_a_2307_);
lean_dec(v_a_2306_);
lean_dec_ref(v_a_2305_);
lean_dec(v_a_2304_);
return v_res_2311_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Closure_process_spec__0(lean_object* v_00_u03b2_2312_, lean_object* v_k_2313_, lean_object* v_t_2314_){
_start:
{
uint8_t v___x_2315_; 
v___x_2315_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Closure_process_spec__0___redArg(v_k_2313_, v_t_2314_);
return v___x_2315_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Closure_process_spec__0___boxed(lean_object* v_00_u03b2_2316_, lean_object* v_k_2317_, lean_object* v_t_2318_){
_start:
{
uint8_t v_res_2319_; lean_object* v_r_2320_; 
v_res_2319_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Closure_process_spec__0(v_00_u03b2_2316_, v_k_2317_, v_t_2318_);
lean_dec(v_t_2318_);
lean_dec(v_k_2317_);
v_r_2320_ = lean_box(v_res_2319_);
return v_r_2320_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkBinding___lam__0(lean_object* v_decls_2321_, lean_object* v_xs_2322_, uint8_t v_isLambda_2323_, lean_object* v_i_2324_, lean_object* v_x_2325_, lean_object* v_b_2326_){
_start:
{
lean_object* v_decl_2327_; 
v_decl_2327_ = lean_array_fget_borrowed(v_decls_2321_, v_i_2324_);
if (lean_obj_tag(v_decl_2327_) == 0)
{
lean_object* v_userName_2328_; lean_object* v_type_2329_; uint8_t v_bi_2330_; lean_object* v_ty_2331_; 
v_userName_2328_ = lean_ctor_get(v_decl_2327_, 2);
v_type_2329_ = lean_ctor_get(v_decl_2327_, 3);
v_bi_2330_ = lean_ctor_get_uint8(v_decl_2327_, sizeof(void*)*4);
v_ty_2331_ = lean_expr_abstract_range(v_type_2329_, v_i_2324_, v_xs_2322_);
if (v_isLambda_2323_ == 0)
{
lean_object* v___x_2332_; 
lean_inc(v_userName_2328_);
v___x_2332_ = l_Lean_mkForall(v_userName_2328_, v_bi_2330_, v_ty_2331_, v_b_2326_);
return v___x_2332_;
}
else
{
lean_object* v___x_2333_; 
lean_inc(v_userName_2328_);
v___x_2333_ = l_Lean_mkLambda(v_userName_2328_, v_bi_2330_, v_ty_2331_, v_b_2326_);
return v___x_2333_;
}
}
else
{
lean_object* v_userName_2334_; lean_object* v_type_2335_; lean_object* v_value_2336_; uint8_t v_nondep_2337_; lean_object* v___x_2338_; uint8_t v___x_2339_; 
v_userName_2334_ = lean_ctor_get(v_decl_2327_, 2);
v_type_2335_ = lean_ctor_get(v_decl_2327_, 3);
v_value_2336_ = lean_ctor_get(v_decl_2327_, 4);
v_nondep_2337_ = lean_ctor_get_uint8(v_decl_2327_, sizeof(void*)*5);
v___x_2338_ = lean_unsigned_to_nat(0u);
v___x_2339_ = lean_expr_has_loose_bvar(v_b_2326_, v___x_2338_);
if (v___x_2339_ == 0)
{
lean_object* v___x_2340_; lean_object* v___x_2341_; 
v___x_2340_ = lean_unsigned_to_nat(1u);
v___x_2341_ = lean_expr_lower_loose_bvars(v_b_2326_, v___x_2340_, v___x_2340_);
lean_dec_ref(v_b_2326_);
return v___x_2341_;
}
else
{
lean_object* v_ty_2342_; lean_object* v_val_2343_; lean_object* v___x_2344_; 
v_ty_2342_ = lean_expr_abstract_range(v_type_2335_, v_i_2324_, v_xs_2322_);
v_val_2343_ = lean_expr_abstract_range(v_value_2336_, v_i_2324_, v_xs_2322_);
lean_inc(v_userName_2334_);
v___x_2344_ = l_Lean_Expr_letE___override(v_userName_2334_, v_ty_2342_, v_val_2343_, v_b_2326_, v_nondep_2337_);
return v___x_2344_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkBinding___lam__0___boxed(lean_object* v_decls_2345_, lean_object* v_xs_2346_, lean_object* v_isLambda_2347_, lean_object* v_i_2348_, lean_object* v_x_2349_, lean_object* v_b_2350_){
_start:
{
uint8_t v_isLambda_boxed_2351_; lean_object* v_res_2352_; 
v_isLambda_boxed_2351_ = lean_unbox(v_isLambda_2347_);
v_res_2352_ = l_Lean_Meta_Closure_mkBinding___lam__0(v_decls_2345_, v_xs_2346_, v_isLambda_boxed_2351_, v_i_2348_, v_x_2349_, v_b_2350_);
lean_dec(v_i_2348_);
lean_dec_ref(v_xs_2346_);
lean_dec_ref(v_decls_2345_);
return v_res_2352_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkBinding(uint8_t v_isLambda_2373_, lean_object* v_decls_2374_, lean_object* v_b_2375_){
_start:
{
lean_object* v___f_2376_; lean_object* v___x_2377_; size_t v_sz_2378_; size_t v___x_2379_; lean_object* v_xs_2380_; lean_object* v___x_2381_; lean_object* v___f_2382_; lean_object* v_b_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; 
v___f_2376_ = ((lean_object*)(l_Lean_Meta_Closure_mkBinding___closed__0));
v___x_2377_ = ((lean_object*)(l_Lean_Meta_Closure_mkBinding___closed__10));
v_sz_2378_ = lean_array_size(v_decls_2374_);
v___x_2379_ = ((size_t)0ULL);
lean_inc_ref_n(v_decls_2374_, 2);
v_xs_2380_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2377_, v___f_2376_, v_sz_2378_, v___x_2379_, v_decls_2374_);
v___x_2381_ = lean_box(v_isLambda_2373_);
lean_inc(v_xs_2380_);
v___f_2382_ = lean_alloc_closure((void*)(l_Lean_Meta_Closure_mkBinding___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2382_, 0, v_decls_2374_);
lean_closure_set(v___f_2382_, 1, v_xs_2380_);
lean_closure_set(v___f_2382_, 2, v___x_2381_);
v_b_2383_ = lean_expr_abstract(v_b_2375_, v_xs_2380_);
lean_dec(v_xs_2380_);
v___x_2384_ = lean_array_get_size(v_decls_2374_);
lean_dec_ref(v_decls_2374_);
v___x_2385_ = l_Nat_foldRev___redArg(v___x_2384_, v___f_2382_, v_b_2383_);
return v___x_2385_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkBinding___boxed(lean_object* v_isLambda_2386_, lean_object* v_decls_2387_, lean_object* v_b_2388_){
_start:
{
uint8_t v_isLambda_boxed_2389_; lean_object* v_res_2390_; 
v_isLambda_boxed_2389_ = lean_unbox(v_isLambda_2386_);
v_res_2390_ = l_Lean_Meta_Closure_mkBinding(v_isLambda_boxed_2389_, v_decls_2387_, v_b_2388_);
lean_dec_ref(v_b_2388_);
return v_res_2390_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Closure_mkLambda_spec__0(size_t v_sz_2391_, size_t v_i_2392_, lean_object* v_bs_2393_){
_start:
{
uint8_t v___x_2394_; 
v___x_2394_ = lean_usize_dec_lt(v_i_2392_, v_sz_2391_);
if (v___x_2394_ == 0)
{
return v_bs_2393_;
}
else
{
lean_object* v_v_2395_; lean_object* v___x_2396_; lean_object* v_bs_x27_2397_; lean_object* v___x_2398_; size_t v___x_2399_; size_t v___x_2400_; lean_object* v___x_2401_; 
v_v_2395_ = lean_array_uget(v_bs_2393_, v_i_2392_);
v___x_2396_ = lean_unsigned_to_nat(0u);
v_bs_x27_2397_ = lean_array_uset(v_bs_2393_, v_i_2392_, v___x_2396_);
v___x_2398_ = l_Lean_LocalDecl_toExpr(v_v_2395_);
v___x_2399_ = ((size_t)1ULL);
v___x_2400_ = lean_usize_add(v_i_2392_, v___x_2399_);
v___x_2401_ = lean_array_uset(v_bs_x27_2397_, v_i_2392_, v___x_2398_);
v_i_2392_ = v___x_2400_;
v_bs_2393_ = v___x_2401_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Closure_mkLambda_spec__0___boxed(lean_object* v_sz_2403_, lean_object* v_i_2404_, lean_object* v_bs_2405_){
_start:
{
size_t v_sz_boxed_2406_; size_t v_i_boxed_2407_; lean_object* v_res_2408_; 
v_sz_boxed_2406_ = lean_unbox_usize(v_sz_2403_);
lean_dec(v_sz_2403_);
v_i_boxed_2407_ = lean_unbox_usize(v_i_2404_);
lean_dec(v_i_2404_);
v_res_2408_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Closure_mkLambda_spec__0(v_sz_boxed_2406_, v_i_boxed_2407_, v_bs_2405_);
return v_res_2408_;
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_Meta_Closure_mkLambda_spec__1_spec__1(lean_object* v_decls_2409_, lean_object* v_xs_2410_, lean_object* v_x_2411_, lean_object* v_x_2412_){
_start:
{
lean_object* v_zero_2413_; uint8_t v_isZero_2414_; 
v_zero_2413_ = lean_unsigned_to_nat(0u);
v_isZero_2414_ = lean_nat_dec_eq(v_x_2411_, v_zero_2413_);
if (v_isZero_2414_ == 1)
{
lean_dec(v_x_2411_);
return v_x_2412_;
}
else
{
lean_object* v_one_2415_; lean_object* v_n_2416_; lean_object* v_decl_2417_; 
v_one_2415_ = lean_unsigned_to_nat(1u);
v_n_2416_ = lean_nat_sub(v_x_2411_, v_one_2415_);
lean_dec(v_x_2411_);
v_decl_2417_ = lean_array_fget_borrowed(v_decls_2409_, v_n_2416_);
if (lean_obj_tag(v_decl_2417_) == 0)
{
lean_object* v_userName_2418_; lean_object* v_type_2419_; uint8_t v_bi_2420_; lean_object* v_ty_2421_; lean_object* v___x_2422_; 
v_userName_2418_ = lean_ctor_get(v_decl_2417_, 2);
v_type_2419_ = lean_ctor_get(v_decl_2417_, 3);
v_bi_2420_ = lean_ctor_get_uint8(v_decl_2417_, sizeof(void*)*4);
v_ty_2421_ = lean_expr_abstract_range(v_type_2419_, v_n_2416_, v_xs_2410_);
lean_inc(v_userName_2418_);
v___x_2422_ = l_Lean_mkLambda(v_userName_2418_, v_bi_2420_, v_ty_2421_, v_x_2412_);
v_x_2411_ = v_n_2416_;
v_x_2412_ = v___x_2422_;
goto _start;
}
else
{
lean_object* v_userName_2424_; lean_object* v_type_2425_; lean_object* v_value_2426_; uint8_t v_nondep_2427_; uint8_t v___x_2428_; 
v_userName_2424_ = lean_ctor_get(v_decl_2417_, 2);
v_type_2425_ = lean_ctor_get(v_decl_2417_, 3);
v_value_2426_ = lean_ctor_get(v_decl_2417_, 4);
v_nondep_2427_ = lean_ctor_get_uint8(v_decl_2417_, sizeof(void*)*5);
v___x_2428_ = lean_expr_has_loose_bvar(v_x_2412_, v_zero_2413_);
if (v___x_2428_ == 0)
{
lean_object* v___x_2429_; 
v___x_2429_ = lean_expr_lower_loose_bvars(v_x_2412_, v_one_2415_, v_one_2415_);
lean_dec_ref(v_x_2412_);
v_x_2411_ = v_n_2416_;
v_x_2412_ = v___x_2429_;
goto _start;
}
else
{
lean_object* v_ty_2431_; lean_object* v_val_2432_; lean_object* v___x_2433_; 
v_ty_2431_ = lean_expr_abstract_range(v_type_2425_, v_n_2416_, v_xs_2410_);
v_val_2432_ = lean_expr_abstract_range(v_value_2426_, v_n_2416_, v_xs_2410_);
lean_inc(v_userName_2424_);
v___x_2433_ = l_Lean_Expr_letE___override(v_userName_2424_, v_ty_2431_, v_val_2432_, v_x_2412_, v_nondep_2427_);
v_x_2411_ = v_n_2416_;
v_x_2412_ = v___x_2433_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_Meta_Closure_mkLambda_spec__1_spec__1___boxed(lean_object* v_decls_2435_, lean_object* v_xs_2436_, lean_object* v_x_2437_, lean_object* v_x_2438_){
_start:
{
lean_object* v_res_2439_; 
v_res_2439_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_Meta_Closure_mkLambda_spec__1_spec__1(v_decls_2435_, v_xs_2436_, v_x_2437_, v_x_2438_);
lean_dec_ref(v_xs_2436_);
lean_dec_ref(v_decls_2435_);
return v_res_2439_;
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Lean_Meta_Closure_mkLambda_spec__1(lean_object* v_decls_2440_, lean_object* v_xs_2441_, lean_object* v_x_2442_, lean_object* v_x_2443_){
_start:
{
lean_object* v_zero_2444_; uint8_t v_isZero_2445_; 
v_zero_2444_ = lean_unsigned_to_nat(0u);
v_isZero_2445_ = lean_nat_dec_eq(v_x_2442_, v_zero_2444_);
if (v_isZero_2445_ == 1)
{
return v_x_2443_;
}
else
{
lean_object* v_one_2446_; lean_object* v_n_2447_; lean_object* v_decl_2448_; 
v_one_2446_ = lean_unsigned_to_nat(1u);
v_n_2447_ = lean_nat_sub(v_x_2442_, v_one_2446_);
v_decl_2448_ = lean_array_fget_borrowed(v_decls_2440_, v_n_2447_);
if (lean_obj_tag(v_decl_2448_) == 0)
{
lean_object* v_userName_2449_; lean_object* v_type_2450_; uint8_t v_bi_2451_; lean_object* v_ty_2452_; lean_object* v___x_2453_; lean_object* v___x_2454_; 
v_userName_2449_ = lean_ctor_get(v_decl_2448_, 2);
v_type_2450_ = lean_ctor_get(v_decl_2448_, 3);
v_bi_2451_ = lean_ctor_get_uint8(v_decl_2448_, sizeof(void*)*4);
v_ty_2452_ = lean_expr_abstract_range(v_type_2450_, v_n_2447_, v_xs_2441_);
lean_inc(v_userName_2449_);
v___x_2453_ = l_Lean_mkLambda(v_userName_2449_, v_bi_2451_, v_ty_2452_, v_x_2443_);
v___x_2454_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_Meta_Closure_mkLambda_spec__1_spec__1(v_decls_2440_, v_xs_2441_, v_n_2447_, v___x_2453_);
return v___x_2454_;
}
else
{
lean_object* v_userName_2455_; lean_object* v_type_2456_; lean_object* v_value_2457_; uint8_t v_nondep_2458_; uint8_t v___x_2459_; 
v_userName_2455_ = lean_ctor_get(v_decl_2448_, 2);
v_type_2456_ = lean_ctor_get(v_decl_2448_, 3);
v_value_2457_ = lean_ctor_get(v_decl_2448_, 4);
v_nondep_2458_ = lean_ctor_get_uint8(v_decl_2448_, sizeof(void*)*5);
v___x_2459_ = lean_expr_has_loose_bvar(v_x_2443_, v_zero_2444_);
if (v___x_2459_ == 0)
{
lean_object* v___x_2460_; lean_object* v___x_2461_; 
v___x_2460_ = lean_expr_lower_loose_bvars(v_x_2443_, v_one_2446_, v_one_2446_);
lean_dec_ref(v_x_2443_);
v___x_2461_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_Meta_Closure_mkLambda_spec__1_spec__1(v_decls_2440_, v_xs_2441_, v_n_2447_, v___x_2460_);
return v___x_2461_;
}
else
{
lean_object* v_ty_2462_; lean_object* v_val_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; 
v_ty_2462_ = lean_expr_abstract_range(v_type_2456_, v_n_2447_, v_xs_2441_);
v_val_2463_ = lean_expr_abstract_range(v_value_2457_, v_n_2447_, v_xs_2441_);
lean_inc(v_userName_2455_);
v___x_2464_ = l_Lean_Expr_letE___override(v_userName_2455_, v_ty_2462_, v_val_2463_, v_x_2443_, v_nondep_2458_);
v___x_2465_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_Meta_Closure_mkLambda_spec__1_spec__1(v_decls_2440_, v_xs_2441_, v_n_2447_, v___x_2464_);
return v___x_2465_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Lean_Meta_Closure_mkLambda_spec__1___boxed(lean_object* v_decls_2466_, lean_object* v_xs_2467_, lean_object* v_x_2468_, lean_object* v_x_2469_){
_start:
{
lean_object* v_res_2470_; 
v_res_2470_ = l_Nat_foldRev___at___00Lean_Meta_Closure_mkLambda_spec__1(v_decls_2466_, v_xs_2467_, v_x_2468_, v_x_2469_);
lean_dec(v_x_2468_);
lean_dec_ref(v_xs_2467_);
lean_dec_ref(v_decls_2466_);
return v_res_2470_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkLambda(lean_object* v_decls_2471_, lean_object* v_b_2472_){
_start:
{
size_t v_sz_2473_; size_t v___x_2474_; lean_object* v_xs_2475_; lean_object* v_b_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; 
v_sz_2473_ = lean_array_size(v_decls_2471_);
v___x_2474_ = ((size_t)0ULL);
lean_inc_ref(v_decls_2471_);
v_xs_2475_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Closure_mkLambda_spec__0(v_sz_2473_, v___x_2474_, v_decls_2471_);
v_b_2476_ = lean_expr_abstract(v_b_2472_, v_xs_2475_);
v___x_2477_ = lean_array_get_size(v_decls_2471_);
v___x_2478_ = l_Nat_foldRev___at___00Lean_Meta_Closure_mkLambda_spec__1(v_decls_2471_, v_xs_2475_, v___x_2477_, v_b_2476_);
lean_dec_ref(v_xs_2475_);
lean_dec_ref(v_decls_2471_);
return v___x_2478_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkLambda___boxed(lean_object* v_decls_2479_, lean_object* v_b_2480_){
_start:
{
lean_object* v_res_2481_; 
v_res_2481_ = l_Lean_Meta_Closure_mkLambda(v_decls_2479_, v_b_2480_);
lean_dec_ref(v_b_2480_);
return v_res_2481_;
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_Meta_Closure_mkForall_spec__0_spec__0(lean_object* v_decls_2482_, lean_object* v_xs_2483_, lean_object* v_x_2484_, lean_object* v_x_2485_){
_start:
{
lean_object* v_zero_2486_; uint8_t v_isZero_2487_; 
v_zero_2486_ = lean_unsigned_to_nat(0u);
v_isZero_2487_ = lean_nat_dec_eq(v_x_2484_, v_zero_2486_);
if (v_isZero_2487_ == 1)
{
lean_dec(v_x_2484_);
return v_x_2485_;
}
else
{
lean_object* v_one_2488_; lean_object* v_n_2489_; lean_object* v_decl_2490_; 
v_one_2488_ = lean_unsigned_to_nat(1u);
v_n_2489_ = lean_nat_sub(v_x_2484_, v_one_2488_);
lean_dec(v_x_2484_);
v_decl_2490_ = lean_array_fget_borrowed(v_decls_2482_, v_n_2489_);
if (lean_obj_tag(v_decl_2490_) == 0)
{
lean_object* v_userName_2491_; lean_object* v_type_2492_; uint8_t v_bi_2493_; lean_object* v_ty_2494_; lean_object* v___x_2495_; 
v_userName_2491_ = lean_ctor_get(v_decl_2490_, 2);
v_type_2492_ = lean_ctor_get(v_decl_2490_, 3);
v_bi_2493_ = lean_ctor_get_uint8(v_decl_2490_, sizeof(void*)*4);
v_ty_2494_ = lean_expr_abstract_range(v_type_2492_, v_n_2489_, v_xs_2483_);
lean_inc(v_userName_2491_);
v___x_2495_ = l_Lean_mkForall(v_userName_2491_, v_bi_2493_, v_ty_2494_, v_x_2485_);
v_x_2484_ = v_n_2489_;
v_x_2485_ = v___x_2495_;
goto _start;
}
else
{
lean_object* v_userName_2497_; lean_object* v_type_2498_; lean_object* v_value_2499_; uint8_t v_nondep_2500_; uint8_t v___x_2501_; 
v_userName_2497_ = lean_ctor_get(v_decl_2490_, 2);
v_type_2498_ = lean_ctor_get(v_decl_2490_, 3);
v_value_2499_ = lean_ctor_get(v_decl_2490_, 4);
v_nondep_2500_ = lean_ctor_get_uint8(v_decl_2490_, sizeof(void*)*5);
v___x_2501_ = lean_expr_has_loose_bvar(v_x_2485_, v_zero_2486_);
if (v___x_2501_ == 0)
{
lean_object* v___x_2502_; 
v___x_2502_ = lean_expr_lower_loose_bvars(v_x_2485_, v_one_2488_, v_one_2488_);
lean_dec_ref(v_x_2485_);
v_x_2484_ = v_n_2489_;
v_x_2485_ = v___x_2502_;
goto _start;
}
else
{
lean_object* v_ty_2504_; lean_object* v_val_2505_; lean_object* v___x_2506_; 
v_ty_2504_ = lean_expr_abstract_range(v_type_2498_, v_n_2489_, v_xs_2483_);
v_val_2505_ = lean_expr_abstract_range(v_value_2499_, v_n_2489_, v_xs_2483_);
lean_inc(v_userName_2497_);
v___x_2506_ = l_Lean_Expr_letE___override(v_userName_2497_, v_ty_2504_, v_val_2505_, v_x_2485_, v_nondep_2500_);
v_x_2484_ = v_n_2489_;
v_x_2485_ = v___x_2506_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_Meta_Closure_mkForall_spec__0_spec__0___boxed(lean_object* v_decls_2508_, lean_object* v_xs_2509_, lean_object* v_x_2510_, lean_object* v_x_2511_){
_start:
{
lean_object* v_res_2512_; 
v_res_2512_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_Meta_Closure_mkForall_spec__0_spec__0(v_decls_2508_, v_xs_2509_, v_x_2510_, v_x_2511_);
lean_dec_ref(v_xs_2509_);
lean_dec_ref(v_decls_2508_);
return v_res_2512_;
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Lean_Meta_Closure_mkForall_spec__0(lean_object* v_decls_2513_, lean_object* v_xs_2514_, lean_object* v_x_2515_, lean_object* v_x_2516_){
_start:
{
lean_object* v_zero_2517_; uint8_t v_isZero_2518_; 
v_zero_2517_ = lean_unsigned_to_nat(0u);
v_isZero_2518_ = lean_nat_dec_eq(v_x_2515_, v_zero_2517_);
if (v_isZero_2518_ == 1)
{
return v_x_2516_;
}
else
{
lean_object* v_one_2519_; lean_object* v_n_2520_; lean_object* v_decl_2521_; 
v_one_2519_ = lean_unsigned_to_nat(1u);
v_n_2520_ = lean_nat_sub(v_x_2515_, v_one_2519_);
v_decl_2521_ = lean_array_fget_borrowed(v_decls_2513_, v_n_2520_);
if (lean_obj_tag(v_decl_2521_) == 0)
{
lean_object* v_userName_2522_; lean_object* v_type_2523_; uint8_t v_bi_2524_; lean_object* v_ty_2525_; lean_object* v___x_2526_; lean_object* v___x_2527_; 
v_userName_2522_ = lean_ctor_get(v_decl_2521_, 2);
v_type_2523_ = lean_ctor_get(v_decl_2521_, 3);
v_bi_2524_ = lean_ctor_get_uint8(v_decl_2521_, sizeof(void*)*4);
v_ty_2525_ = lean_expr_abstract_range(v_type_2523_, v_n_2520_, v_xs_2514_);
lean_inc(v_userName_2522_);
v___x_2526_ = l_Lean_mkForall(v_userName_2522_, v_bi_2524_, v_ty_2525_, v_x_2516_);
v___x_2527_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_Meta_Closure_mkForall_spec__0_spec__0(v_decls_2513_, v_xs_2514_, v_n_2520_, v___x_2526_);
return v___x_2527_;
}
else
{
lean_object* v_userName_2528_; lean_object* v_type_2529_; lean_object* v_value_2530_; uint8_t v_nondep_2531_; uint8_t v___x_2532_; 
v_userName_2528_ = lean_ctor_get(v_decl_2521_, 2);
v_type_2529_ = lean_ctor_get(v_decl_2521_, 3);
v_value_2530_ = lean_ctor_get(v_decl_2521_, 4);
v_nondep_2531_ = lean_ctor_get_uint8(v_decl_2521_, sizeof(void*)*5);
v___x_2532_ = lean_expr_has_loose_bvar(v_x_2516_, v_zero_2517_);
if (v___x_2532_ == 0)
{
lean_object* v___x_2533_; lean_object* v___x_2534_; 
v___x_2533_ = lean_expr_lower_loose_bvars(v_x_2516_, v_one_2519_, v_one_2519_);
lean_dec_ref(v_x_2516_);
v___x_2534_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_Meta_Closure_mkForall_spec__0_spec__0(v_decls_2513_, v_xs_2514_, v_n_2520_, v___x_2533_);
return v___x_2534_;
}
else
{
lean_object* v_ty_2535_; lean_object* v_val_2536_; lean_object* v___x_2537_; lean_object* v___x_2538_; 
v_ty_2535_ = lean_expr_abstract_range(v_type_2529_, v_n_2520_, v_xs_2514_);
v_val_2536_ = lean_expr_abstract_range(v_value_2530_, v_n_2520_, v_xs_2514_);
lean_inc(v_userName_2528_);
v___x_2537_ = l_Lean_Expr_letE___override(v_userName_2528_, v_ty_2535_, v_val_2536_, v_x_2516_, v_nondep_2531_);
v___x_2538_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_Meta_Closure_mkForall_spec__0_spec__0(v_decls_2513_, v_xs_2514_, v_n_2520_, v___x_2537_);
return v___x_2538_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Lean_Meta_Closure_mkForall_spec__0___boxed(lean_object* v_decls_2539_, lean_object* v_xs_2540_, lean_object* v_x_2541_, lean_object* v_x_2542_){
_start:
{
lean_object* v_res_2543_; 
v_res_2543_ = l_Nat_foldRev___at___00Lean_Meta_Closure_mkForall_spec__0(v_decls_2539_, v_xs_2540_, v_x_2541_, v_x_2542_);
lean_dec(v_x_2541_);
lean_dec_ref(v_xs_2540_);
lean_dec_ref(v_decls_2539_);
return v_res_2543_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkForall(lean_object* v_decls_2544_, lean_object* v_b_2545_){
_start:
{
size_t v_sz_2546_; size_t v___x_2547_; lean_object* v_xs_2548_; lean_object* v_b_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; 
v_sz_2546_ = lean_array_size(v_decls_2544_);
v___x_2547_ = ((size_t)0ULL);
lean_inc_ref(v_decls_2544_);
v_xs_2548_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Closure_mkLambda_spec__0(v_sz_2546_, v___x_2547_, v_decls_2544_);
v_b_2549_ = lean_expr_abstract(v_b_2545_, v_xs_2548_);
v___x_2550_ = lean_array_get_size(v_decls_2544_);
v___x_2551_ = l_Nat_foldRev___at___00Lean_Meta_Closure_mkForall_spec__0(v_decls_2544_, v_xs_2548_, v___x_2550_, v_b_2549_);
lean_dec_ref(v_xs_2548_);
lean_dec_ref(v_decls_2544_);
return v___x_2551_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkForall___boxed(lean_object* v_decls_2552_, lean_object* v_b_2553_){
_start:
{
lean_object* v_res_2554_; 
v_res_2554_ = l_Lean_Meta_Closure_mkForall(v_decls_2552_, v_b_2553_);
lean_dec_ref(v_b_2553_);
return v_res_2554_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkValueTypeClosureAux___lam__0(lean_object* v_a_2555_, lean_object* v_zetaDeltaFVarIds_2556_, lean_object* v_a_x3f_2557_){
_start:
{
lean_object* v___x_2559_; lean_object* v_mctx_2560_; lean_object* v_cache_2561_; lean_object* v_postponed_2562_; lean_object* v_diag_2563_; lean_object* v___x_2565_; uint8_t v_isShared_2566_; uint8_t v_isSharedCheck_2573_; 
v___x_2559_ = lean_st_ref_take(v_a_2555_);
v_mctx_2560_ = lean_ctor_get(v___x_2559_, 0);
v_cache_2561_ = lean_ctor_get(v___x_2559_, 1);
v_postponed_2562_ = lean_ctor_get(v___x_2559_, 3);
v_diag_2563_ = lean_ctor_get(v___x_2559_, 4);
v_isSharedCheck_2573_ = !lean_is_exclusive(v___x_2559_);
if (v_isSharedCheck_2573_ == 0)
{
lean_object* v_unused_2574_; 
v_unused_2574_ = lean_ctor_get(v___x_2559_, 2);
lean_dec(v_unused_2574_);
v___x_2565_ = v___x_2559_;
v_isShared_2566_ = v_isSharedCheck_2573_;
goto v_resetjp_2564_;
}
else
{
lean_inc(v_diag_2563_);
lean_inc(v_postponed_2562_);
lean_inc(v_cache_2561_);
lean_inc(v_mctx_2560_);
lean_dec(v___x_2559_);
v___x_2565_ = lean_box(0);
v_isShared_2566_ = v_isSharedCheck_2573_;
goto v_resetjp_2564_;
}
v_resetjp_2564_:
{
lean_object* v___x_2568_; 
if (v_isShared_2566_ == 0)
{
lean_ctor_set(v___x_2565_, 2, v_zetaDeltaFVarIds_2556_);
v___x_2568_ = v___x_2565_;
goto v_reusejp_2567_;
}
else
{
lean_object* v_reuseFailAlloc_2572_; 
v_reuseFailAlloc_2572_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2572_, 0, v_mctx_2560_);
lean_ctor_set(v_reuseFailAlloc_2572_, 1, v_cache_2561_);
lean_ctor_set(v_reuseFailAlloc_2572_, 2, v_zetaDeltaFVarIds_2556_);
lean_ctor_set(v_reuseFailAlloc_2572_, 3, v_postponed_2562_);
lean_ctor_set(v_reuseFailAlloc_2572_, 4, v_diag_2563_);
v___x_2568_ = v_reuseFailAlloc_2572_;
goto v_reusejp_2567_;
}
v_reusejp_2567_:
{
lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; 
v___x_2569_ = lean_st_ref_set(v_a_2555_, v___x_2568_);
v___x_2570_ = lean_box(0);
v___x_2571_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2571_, 0, v___x_2570_);
return v___x_2571_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkValueTypeClosureAux___lam__0___boxed(lean_object* v_a_2575_, lean_object* v_zetaDeltaFVarIds_2576_, lean_object* v_a_x3f_2577_, lean_object* v___y_2578_){
_start:
{
lean_object* v_res_2579_; 
v_res_2579_ = l_Lean_Meta_Closure_mkValueTypeClosureAux___lam__0(v_a_2575_, v_zetaDeltaFVarIds_2576_, v_a_x3f_2577_);
lean_dec(v_a_x3f_2577_);
lean_dec(v_a_2575_);
return v_res_2579_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkValueTypeClosureAux___lam__1(lean_object* v_a_2580_, lean_object* v_cache_2581_, lean_object* v_a_x3f_2582_){
_start:
{
lean_object* v___x_2584_; lean_object* v_mctx_2585_; lean_object* v_zetaDeltaFVarIds_2586_; lean_object* v_postponed_2587_; lean_object* v_diag_2588_; lean_object* v___x_2590_; uint8_t v_isShared_2591_; uint8_t v_isSharedCheck_2598_; 
v___x_2584_ = lean_st_ref_take(v_a_2580_);
v_mctx_2585_ = lean_ctor_get(v___x_2584_, 0);
v_zetaDeltaFVarIds_2586_ = lean_ctor_get(v___x_2584_, 2);
v_postponed_2587_ = lean_ctor_get(v___x_2584_, 3);
v_diag_2588_ = lean_ctor_get(v___x_2584_, 4);
v_isSharedCheck_2598_ = !lean_is_exclusive(v___x_2584_);
if (v_isSharedCheck_2598_ == 0)
{
lean_object* v_unused_2599_; 
v_unused_2599_ = lean_ctor_get(v___x_2584_, 1);
lean_dec(v_unused_2599_);
v___x_2590_ = v___x_2584_;
v_isShared_2591_ = v_isSharedCheck_2598_;
goto v_resetjp_2589_;
}
else
{
lean_inc(v_diag_2588_);
lean_inc(v_postponed_2587_);
lean_inc(v_zetaDeltaFVarIds_2586_);
lean_inc(v_mctx_2585_);
lean_dec(v___x_2584_);
v___x_2590_ = lean_box(0);
v_isShared_2591_ = v_isSharedCheck_2598_;
goto v_resetjp_2589_;
}
v_resetjp_2589_:
{
lean_object* v___x_2593_; 
if (v_isShared_2591_ == 0)
{
lean_ctor_set(v___x_2590_, 1, v_cache_2581_);
v___x_2593_ = v___x_2590_;
goto v_reusejp_2592_;
}
else
{
lean_object* v_reuseFailAlloc_2597_; 
v_reuseFailAlloc_2597_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2597_, 0, v_mctx_2585_);
lean_ctor_set(v_reuseFailAlloc_2597_, 1, v_cache_2581_);
lean_ctor_set(v_reuseFailAlloc_2597_, 2, v_zetaDeltaFVarIds_2586_);
lean_ctor_set(v_reuseFailAlloc_2597_, 3, v_postponed_2587_);
lean_ctor_set(v_reuseFailAlloc_2597_, 4, v_diag_2588_);
v___x_2593_ = v_reuseFailAlloc_2597_;
goto v_reusejp_2592_;
}
v_reusejp_2592_:
{
lean_object* v___x_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; 
v___x_2594_ = lean_st_ref_set(v_a_2580_, v___x_2593_);
v___x_2595_ = lean_box(0);
v___x_2596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2596_, 0, v___x_2595_);
return v___x_2596_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkValueTypeClosureAux___lam__1___boxed(lean_object* v_a_2600_, lean_object* v_cache_2601_, lean_object* v_a_x3f_2602_, lean_object* v___y_2603_){
_start:
{
lean_object* v_res_2604_; 
v_res_2604_ = l_Lean_Meta_Closure_mkValueTypeClosureAux___lam__1(v_a_2600_, v_cache_2601_, v_a_x3f_2602_);
lean_dec(v_a_x3f_2602_);
lean_dec(v_a_2600_);
return v_res_2604_;
}
}
static lean_object* _init_l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__0(void){
_start:
{
lean_object* v___x_2605_; 
v___x_2605_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2605_;
}
}
static lean_object* _init_l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__1(void){
_start:
{
lean_object* v___x_2606_; lean_object* v___x_2607_; 
v___x_2606_ = lean_obj_once(&l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__0, &l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__0_once, _init_l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__0);
v___x_2607_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2607_, 0, v___x_2606_);
return v___x_2607_;
}
}
static lean_object* _init_l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__2(void){
_start:
{
lean_object* v___x_2608_; lean_object* v___x_2609_; 
v___x_2608_ = lean_obj_once(&l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__1, &l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__1_once, _init_l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__1);
v___x_2609_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2609_, 0, v___x_2608_);
lean_ctor_set(v___x_2609_, 1, v___x_2608_);
lean_ctor_set(v___x_2609_, 2, v___x_2608_);
lean_ctor_set(v___x_2609_, 3, v___x_2608_);
lean_ctor_set(v___x_2609_, 4, v___x_2608_);
lean_ctor_set(v___x_2609_, 5, v___x_2608_);
return v___x_2609_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkValueTypeClosureAux(lean_object* v_type_2610_, lean_object* v_value_2611_, uint8_t v_a_2612_, lean_object* v_a_2613_, lean_object* v_a_2614_, lean_object* v_a_2615_, lean_object* v_a_2616_, lean_object* v_a_2617_){
_start:
{
lean_object* v___x_2619_; lean_object* v___x_2620_; lean_object* v_mctx_2621_; lean_object* v_zetaDeltaFVarIds_2622_; lean_object* v_postponed_2623_; lean_object* v_diag_2624_; lean_object* v___x_2626_; uint8_t v_isShared_2627_; uint8_t v_isSharedCheck_2704_; 
v___x_2619_ = lean_st_ref_get(v_a_2615_);
v___x_2620_ = lean_st_ref_take(v_a_2615_);
v_mctx_2621_ = lean_ctor_get(v___x_2620_, 0);
v_zetaDeltaFVarIds_2622_ = lean_ctor_get(v___x_2620_, 2);
v_postponed_2623_ = lean_ctor_get(v___x_2620_, 3);
v_diag_2624_ = lean_ctor_get(v___x_2620_, 4);
v_isSharedCheck_2704_ = !lean_is_exclusive(v___x_2620_);
if (v_isSharedCheck_2704_ == 0)
{
lean_object* v_unused_2705_; 
v_unused_2705_ = lean_ctor_get(v___x_2620_, 1);
lean_dec(v_unused_2705_);
v___x_2626_ = v___x_2620_;
v_isShared_2627_ = v_isSharedCheck_2704_;
goto v_resetjp_2625_;
}
else
{
lean_inc(v_diag_2624_);
lean_inc(v_postponed_2623_);
lean_inc(v_zetaDeltaFVarIds_2622_);
lean_inc(v_mctx_2621_);
lean_dec(v___x_2620_);
v___x_2626_ = lean_box(0);
v_isShared_2627_ = v_isSharedCheck_2704_;
goto v_resetjp_2625_;
}
v_resetjp_2625_:
{
lean_object* v___x_2628_; lean_object* v___x_2630_; 
v___x_2628_ = lean_obj_once(&l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__2, &l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__2_once, _init_l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__2);
if (v_isShared_2627_ == 0)
{
lean_ctor_set(v___x_2626_, 1, v___x_2628_);
v___x_2630_ = v___x_2626_;
goto v_reusejp_2629_;
}
else
{
lean_object* v_reuseFailAlloc_2703_; 
v_reuseFailAlloc_2703_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2703_, 0, v_mctx_2621_);
lean_ctor_set(v_reuseFailAlloc_2703_, 1, v___x_2628_);
lean_ctor_set(v_reuseFailAlloc_2703_, 2, v_zetaDeltaFVarIds_2622_);
lean_ctor_set(v_reuseFailAlloc_2703_, 3, v_postponed_2623_);
lean_ctor_set(v_reuseFailAlloc_2703_, 4, v_diag_2624_);
v___x_2630_ = v_reuseFailAlloc_2703_;
goto v_reusejp_2629_;
}
v_reusejp_2629_:
{
lean_object* v___x_2631_; lean_object* v___x_2632_; lean_object* v_mctx_2633_; lean_object* v_cache_2634_; lean_object* v_zetaDeltaFVarIds_2635_; lean_object* v_postponed_2636_; lean_object* v_diag_2637_; lean_object* v___x_2639_; uint8_t v_isShared_2640_; uint8_t v_isSharedCheck_2702_; 
v___x_2631_ = lean_st_ref_set(v_a_2615_, v___x_2630_);
v___x_2632_ = lean_st_ref_take(v_a_2615_);
v_mctx_2633_ = lean_ctor_get(v___x_2632_, 0);
v_cache_2634_ = lean_ctor_get(v___x_2632_, 1);
v_zetaDeltaFVarIds_2635_ = lean_ctor_get(v___x_2632_, 2);
v_postponed_2636_ = lean_ctor_get(v___x_2632_, 3);
v_diag_2637_ = lean_ctor_get(v___x_2632_, 4);
v_isSharedCheck_2702_ = !lean_is_exclusive(v___x_2632_);
if (v_isSharedCheck_2702_ == 0)
{
v___x_2639_ = v___x_2632_;
v_isShared_2640_ = v_isSharedCheck_2702_;
goto v_resetjp_2638_;
}
else
{
lean_inc(v_diag_2637_);
lean_inc(v_postponed_2636_);
lean_inc(v_zetaDeltaFVarIds_2635_);
lean_inc(v_cache_2634_);
lean_inc(v_mctx_2633_);
lean_dec(v___x_2632_);
v___x_2639_ = lean_box(0);
v_isShared_2640_ = v_isSharedCheck_2702_;
goto v_resetjp_2638_;
}
v_resetjp_2638_:
{
lean_object* v___x_2641_; lean_object* v___x_2643_; 
v___x_2641_ = lean_box(1);
if (v_isShared_2640_ == 0)
{
lean_ctor_set(v___x_2639_, 2, v___x_2641_);
v___x_2643_ = v___x_2639_;
goto v_reusejp_2642_;
}
else
{
lean_object* v_reuseFailAlloc_2701_; 
v_reuseFailAlloc_2701_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2701_, 0, v_mctx_2633_);
lean_ctor_set(v_reuseFailAlloc_2701_, 1, v_cache_2634_);
lean_ctor_set(v_reuseFailAlloc_2701_, 2, v___x_2641_);
lean_ctor_set(v_reuseFailAlloc_2701_, 3, v_postponed_2636_);
lean_ctor_set(v_reuseFailAlloc_2701_, 4, v_diag_2637_);
v___x_2643_ = v_reuseFailAlloc_2701_;
goto v_reusejp_2642_;
}
v_reusejp_2642_:
{
lean_object* v___x_2644_; lean_object* v_cache_2645_; lean_object* v_keyedConfig_2646_; lean_object* v_zetaDeltaSet_2647_; lean_object* v_lctx_2648_; lean_object* v_localInstances_2649_; lean_object* v_defEqCtx_x3f_2650_; lean_object* v_synthPendingDepth_2651_; lean_object* v_canUnfold_x3f_2652_; uint8_t v_univApprox_2653_; uint8_t v_inTypeClassResolution_2654_; uint8_t v_cacheInferType_2655_; lean_object* v_a_2657_; lean_object* v_a_2669_; uint8_t v___x_2672_; lean_object* v___x_2673_; lean_object* v___x_2674_; 
v___x_2644_ = lean_st_ref_set(v_a_2615_, v___x_2643_);
v_cache_2645_ = lean_ctor_get(v___x_2619_, 1);
lean_inc_ref(v_cache_2645_);
lean_dec(v___x_2619_);
v_keyedConfig_2646_ = lean_ctor_get(v_a_2614_, 0);
v_zetaDeltaSet_2647_ = lean_ctor_get(v_a_2614_, 1);
v_lctx_2648_ = lean_ctor_get(v_a_2614_, 2);
v_localInstances_2649_ = lean_ctor_get(v_a_2614_, 3);
v_defEqCtx_x3f_2650_ = lean_ctor_get(v_a_2614_, 4);
v_synthPendingDepth_2651_ = lean_ctor_get(v_a_2614_, 5);
v_canUnfold_x3f_2652_ = lean_ctor_get(v_a_2614_, 6);
v_univApprox_2653_ = lean_ctor_get_uint8(v_a_2614_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2654_ = lean_ctor_get_uint8(v_a_2614_, sizeof(void*)*7 + 2);
v_cacheInferType_2655_ = lean_ctor_get_uint8(v_a_2614_, sizeof(void*)*7 + 3);
v___x_2672_ = 1;
lean_inc(v_canUnfold_x3f_2652_);
lean_inc(v_synthPendingDepth_2651_);
lean_inc(v_defEqCtx_x3f_2650_);
lean_inc_ref(v_localInstances_2649_);
lean_inc_ref(v_lctx_2648_);
lean_inc(v_zetaDeltaSet_2647_);
lean_inc_ref(v_keyedConfig_2646_);
v___x_2673_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2673_, 0, v_keyedConfig_2646_);
lean_ctor_set(v___x_2673_, 1, v_zetaDeltaSet_2647_);
lean_ctor_set(v___x_2673_, 2, v_lctx_2648_);
lean_ctor_set(v___x_2673_, 3, v_localInstances_2649_);
lean_ctor_set(v___x_2673_, 4, v_defEqCtx_x3f_2650_);
lean_ctor_set(v___x_2673_, 5, v_synthPendingDepth_2651_);
lean_ctor_set(v___x_2673_, 6, v_canUnfold_x3f_2652_);
lean_ctor_set_uint8(v___x_2673_, sizeof(void*)*7, v___x_2672_);
lean_ctor_set_uint8(v___x_2673_, sizeof(void*)*7 + 1, v_univApprox_2653_);
lean_ctor_set_uint8(v___x_2673_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2654_);
lean_ctor_set_uint8(v___x_2673_, sizeof(void*)*7 + 3, v_cacheInferType_2655_);
v___x_2674_ = l_Lean_Meta_Closure_collectExpr(v_type_2610_, v_a_2612_, v_a_2613_, v___x_2673_, v_a_2615_, v_a_2616_, v_a_2617_);
if (lean_obj_tag(v___x_2674_) == 0)
{
lean_object* v_a_2675_; lean_object* v___x_2676_; 
v_a_2675_ = lean_ctor_get(v___x_2674_, 0);
lean_inc(v_a_2675_);
lean_dec_ref(v___x_2674_);
v___x_2676_ = l_Lean_Meta_Closure_collectExpr(v_value_2611_, v_a_2612_, v_a_2613_, v___x_2673_, v_a_2615_, v_a_2616_, v_a_2617_);
if (lean_obj_tag(v___x_2676_) == 0)
{
lean_object* v_a_2677_; lean_object* v___x_2678_; 
v_a_2677_ = lean_ctor_get(v___x_2676_, 0);
lean_inc(v_a_2677_);
lean_dec_ref(v___x_2676_);
v___x_2678_ = l_Lean_Meta_Closure_process(v_a_2612_, v_a_2613_, v___x_2673_, v_a_2615_, v_a_2616_, v_a_2617_);
lean_dec_ref(v___x_2673_);
if (lean_obj_tag(v___x_2678_) == 0)
{
lean_object* v___x_2680_; uint8_t v_isShared_2681_; uint8_t v_isSharedCheck_2696_; 
v_isSharedCheck_2696_ = !lean_is_exclusive(v___x_2678_);
if (v_isSharedCheck_2696_ == 0)
{
lean_object* v_unused_2697_; 
v_unused_2697_ = lean_ctor_get(v___x_2678_, 0);
lean_dec(v_unused_2697_);
v___x_2680_ = v___x_2678_;
v_isShared_2681_ = v_isSharedCheck_2696_;
goto v_resetjp_2679_;
}
else
{
lean_dec(v___x_2678_);
v___x_2680_ = lean_box(0);
v_isShared_2681_ = v_isSharedCheck_2696_;
goto v_resetjp_2679_;
}
v_resetjp_2679_:
{
lean_object* v___x_2682_; lean_object* v___x_2684_; 
v___x_2682_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2682_, 0, v_a_2675_);
lean_ctor_set(v___x_2682_, 1, v_a_2677_);
lean_inc_ref(v___x_2682_);
if (v_isShared_2681_ == 0)
{
lean_ctor_set_tag(v___x_2680_, 1);
lean_ctor_set(v___x_2680_, 0, v___x_2682_);
v___x_2684_ = v___x_2680_;
goto v_reusejp_2683_;
}
else
{
lean_object* v_reuseFailAlloc_2695_; 
v_reuseFailAlloc_2695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2695_, 0, v___x_2682_);
v___x_2684_ = v_reuseFailAlloc_2695_;
goto v_reusejp_2683_;
}
v_reusejp_2683_:
{
lean_object* v___x_2685_; lean_object* v___x_2686_; lean_object* v___x_2688_; uint8_t v_isShared_2689_; uint8_t v_isSharedCheck_2693_; 
v___x_2685_ = l_Lean_Meta_Closure_mkValueTypeClosureAux___lam__0(v_a_2615_, v_zetaDeltaFVarIds_2635_, v___x_2684_);
lean_dec_ref(v___x_2685_);
v___x_2686_ = l_Lean_Meta_Closure_mkValueTypeClosureAux___lam__1(v_a_2615_, v_cache_2645_, v___x_2684_);
lean_dec_ref(v___x_2684_);
v_isSharedCheck_2693_ = !lean_is_exclusive(v___x_2686_);
if (v_isSharedCheck_2693_ == 0)
{
lean_object* v_unused_2694_; 
v_unused_2694_ = lean_ctor_get(v___x_2686_, 0);
lean_dec(v_unused_2694_);
v___x_2688_ = v___x_2686_;
v_isShared_2689_ = v_isSharedCheck_2693_;
goto v_resetjp_2687_;
}
else
{
lean_dec(v___x_2686_);
v___x_2688_ = lean_box(0);
v_isShared_2689_ = v_isSharedCheck_2693_;
goto v_resetjp_2687_;
}
v_resetjp_2687_:
{
lean_object* v___x_2691_; 
if (v_isShared_2689_ == 0)
{
lean_ctor_set(v___x_2688_, 0, v___x_2682_);
v___x_2691_ = v___x_2688_;
goto v_reusejp_2690_;
}
else
{
lean_object* v_reuseFailAlloc_2692_; 
v_reuseFailAlloc_2692_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2692_, 0, v___x_2682_);
v___x_2691_ = v_reuseFailAlloc_2692_;
goto v_reusejp_2690_;
}
v_reusejp_2690_:
{
return v___x_2691_;
}
}
}
}
}
else
{
lean_object* v_a_2698_; 
lean_dec(v_a_2677_);
lean_dec(v_a_2675_);
v_a_2698_ = lean_ctor_get(v___x_2678_, 0);
lean_inc(v_a_2698_);
lean_dec_ref(v___x_2678_);
v_a_2669_ = v_a_2698_;
goto v___jp_2668_;
}
}
else
{
lean_object* v_a_2699_; 
lean_dec(v_a_2675_);
lean_dec_ref(v___x_2673_);
v_a_2699_ = lean_ctor_get(v___x_2676_, 0);
lean_inc(v_a_2699_);
lean_dec_ref(v___x_2676_);
v_a_2669_ = v_a_2699_;
goto v___jp_2668_;
}
}
else
{
lean_object* v_a_2700_; 
lean_dec_ref(v___x_2673_);
lean_dec_ref(v_value_2611_);
v_a_2700_ = lean_ctor_get(v___x_2674_, 0);
lean_inc(v_a_2700_);
lean_dec_ref(v___x_2674_);
v_a_2669_ = v_a_2700_;
goto v___jp_2668_;
}
v___jp_2656_:
{
lean_object* v___x_2658_; lean_object* v___x_2659_; lean_object* v___x_2661_; uint8_t v_isShared_2662_; uint8_t v_isSharedCheck_2666_; 
v___x_2658_ = lean_box(0);
v___x_2659_ = l_Lean_Meta_Closure_mkValueTypeClosureAux___lam__1(v_a_2615_, v_cache_2645_, v___x_2658_);
v_isSharedCheck_2666_ = !lean_is_exclusive(v___x_2659_);
if (v_isSharedCheck_2666_ == 0)
{
lean_object* v_unused_2667_; 
v_unused_2667_ = lean_ctor_get(v___x_2659_, 0);
lean_dec(v_unused_2667_);
v___x_2661_ = v___x_2659_;
v_isShared_2662_ = v_isSharedCheck_2666_;
goto v_resetjp_2660_;
}
else
{
lean_dec(v___x_2659_);
v___x_2661_ = lean_box(0);
v_isShared_2662_ = v_isSharedCheck_2666_;
goto v_resetjp_2660_;
}
v_resetjp_2660_:
{
lean_object* v___x_2664_; 
if (v_isShared_2662_ == 0)
{
lean_ctor_set_tag(v___x_2661_, 1);
lean_ctor_set(v___x_2661_, 0, v_a_2657_);
v___x_2664_ = v___x_2661_;
goto v_reusejp_2663_;
}
else
{
lean_object* v_reuseFailAlloc_2665_; 
v_reuseFailAlloc_2665_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2665_, 0, v_a_2657_);
v___x_2664_ = v_reuseFailAlloc_2665_;
goto v_reusejp_2663_;
}
v_reusejp_2663_:
{
return v___x_2664_;
}
}
}
v___jp_2668_:
{
lean_object* v___x_2670_; lean_object* v___x_2671_; 
v___x_2670_ = lean_box(0);
v___x_2671_ = l_Lean_Meta_Closure_mkValueTypeClosureAux___lam__0(v_a_2615_, v_zetaDeltaFVarIds_2635_, v___x_2670_);
lean_dec_ref(v___x_2671_);
v_a_2657_ = v_a_2669_;
goto v___jp_2656_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkValueTypeClosureAux___boxed(lean_object* v_type_2706_, lean_object* v_value_2707_, lean_object* v_a_2708_, lean_object* v_a_2709_, lean_object* v_a_2710_, lean_object* v_a_2711_, lean_object* v_a_2712_, lean_object* v_a_2713_, lean_object* v_a_2714_){
_start:
{
uint8_t v_a_boxed_2715_; lean_object* v_res_2716_; 
v_a_boxed_2715_ = lean_unbox(v_a_2708_);
v_res_2716_ = l_Lean_Meta_Closure_mkValueTypeClosureAux(v_type_2706_, v_value_2707_, v_a_boxed_2715_, v_a_2709_, v_a_2710_, v_a_2711_, v_a_2712_, v_a_2713_);
lean_dec(v_a_2713_);
lean_dec_ref(v_a_2712_);
lean_dec(v_a_2711_);
lean_dec_ref(v_a_2710_);
lean_dec(v_a_2709_);
return v_res_2716_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4___closed__0(void){
_start:
{
lean_object* v___x_2717_; 
v___x_2717_ = l_instMonadEIO(lean_box(0));
return v___x_2717_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4(lean_object* v_msg_2720_, lean_object* v___y_2721_, lean_object* v___y_2722_, lean_object* v___y_2723_){
_start:
{
lean_object* v___x_2725_; lean_object* v___x_2726_; lean_object* v_toApplicative_2727_; lean_object* v___x_2729_; uint8_t v_isShared_2730_; uint8_t v_isSharedCheck_2768_; 
v___x_2725_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4___closed__0, &l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4___closed__0);
v___x_2726_ = l_StateRefT_x27_instMonad___redArg(v___x_2725_);
v_toApplicative_2727_ = lean_ctor_get(v___x_2726_, 0);
v_isSharedCheck_2768_ = !lean_is_exclusive(v___x_2726_);
if (v_isSharedCheck_2768_ == 0)
{
lean_object* v_unused_2769_; 
v_unused_2769_ = lean_ctor_get(v___x_2726_, 1);
lean_dec(v_unused_2769_);
v___x_2729_ = v___x_2726_;
v_isShared_2730_ = v_isSharedCheck_2768_;
goto v_resetjp_2728_;
}
else
{
lean_inc(v_toApplicative_2727_);
lean_dec(v___x_2726_);
v___x_2729_ = lean_box(0);
v_isShared_2730_ = v_isSharedCheck_2768_;
goto v_resetjp_2728_;
}
v_resetjp_2728_:
{
lean_object* v_toFunctor_2731_; lean_object* v_toSeq_2732_; lean_object* v_toSeqLeft_2733_; lean_object* v_toSeqRight_2734_; lean_object* v___x_2736_; uint8_t v_isShared_2737_; uint8_t v_isSharedCheck_2766_; 
v_toFunctor_2731_ = lean_ctor_get(v_toApplicative_2727_, 0);
v_toSeq_2732_ = lean_ctor_get(v_toApplicative_2727_, 2);
v_toSeqLeft_2733_ = lean_ctor_get(v_toApplicative_2727_, 3);
v_toSeqRight_2734_ = lean_ctor_get(v_toApplicative_2727_, 4);
v_isSharedCheck_2766_ = !lean_is_exclusive(v_toApplicative_2727_);
if (v_isSharedCheck_2766_ == 0)
{
lean_object* v_unused_2767_; 
v_unused_2767_ = lean_ctor_get(v_toApplicative_2727_, 1);
lean_dec(v_unused_2767_);
v___x_2736_ = v_toApplicative_2727_;
v_isShared_2737_ = v_isSharedCheck_2766_;
goto v_resetjp_2735_;
}
else
{
lean_inc(v_toSeqRight_2734_);
lean_inc(v_toSeqLeft_2733_);
lean_inc(v_toSeq_2732_);
lean_inc(v_toFunctor_2731_);
lean_dec(v_toApplicative_2727_);
v___x_2736_ = lean_box(0);
v_isShared_2737_ = v_isSharedCheck_2766_;
goto v_resetjp_2735_;
}
v_resetjp_2735_:
{
lean_object* v___f_2738_; lean_object* v___f_2739_; lean_object* v___f_2740_; lean_object* v___f_2741_; lean_object* v___x_2742_; lean_object* v___f_2743_; lean_object* v___f_2744_; lean_object* v___f_2745_; lean_object* v___x_2747_; 
v___f_2738_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4___closed__1));
v___f_2739_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4___closed__2));
lean_inc_ref(v_toFunctor_2731_);
v___f_2740_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2740_, 0, v_toFunctor_2731_);
v___f_2741_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2741_, 0, v_toFunctor_2731_);
v___x_2742_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2742_, 0, v___f_2740_);
lean_ctor_set(v___x_2742_, 1, v___f_2741_);
v___f_2743_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2743_, 0, v_toSeqRight_2734_);
v___f_2744_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2744_, 0, v_toSeqLeft_2733_);
v___f_2745_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2745_, 0, v_toSeq_2732_);
if (v_isShared_2737_ == 0)
{
lean_ctor_set(v___x_2736_, 4, v___f_2743_);
lean_ctor_set(v___x_2736_, 3, v___f_2744_);
lean_ctor_set(v___x_2736_, 2, v___f_2745_);
lean_ctor_set(v___x_2736_, 1, v___f_2738_);
lean_ctor_set(v___x_2736_, 0, v___x_2742_);
v___x_2747_ = v___x_2736_;
goto v_reusejp_2746_;
}
else
{
lean_object* v_reuseFailAlloc_2765_; 
v_reuseFailAlloc_2765_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2765_, 0, v___x_2742_);
lean_ctor_set(v_reuseFailAlloc_2765_, 1, v___f_2738_);
lean_ctor_set(v_reuseFailAlloc_2765_, 2, v___f_2745_);
lean_ctor_set(v_reuseFailAlloc_2765_, 3, v___f_2744_);
lean_ctor_set(v_reuseFailAlloc_2765_, 4, v___f_2743_);
v___x_2747_ = v_reuseFailAlloc_2765_;
goto v_reusejp_2746_;
}
v_reusejp_2746_:
{
lean_object* v___x_2749_; 
if (v_isShared_2730_ == 0)
{
lean_ctor_set(v___x_2729_, 1, v___f_2739_);
lean_ctor_set(v___x_2729_, 0, v___x_2747_);
v___x_2749_ = v___x_2729_;
goto v_reusejp_2748_;
}
else
{
lean_object* v_reuseFailAlloc_2764_; 
v_reuseFailAlloc_2764_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2764_, 0, v___x_2747_);
lean_ctor_set(v_reuseFailAlloc_2764_, 1, v___f_2739_);
v___x_2749_ = v_reuseFailAlloc_2764_;
goto v_reusejp_2748_;
}
v_reusejp_2748_:
{
lean_object* v___f_2750_; lean_object* v___f_2751_; lean_object* v___f_2752_; lean_object* v___f_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; lean_object* v___x_2756_; lean_object* v___x_2757_; lean_object* v___x_2758_; lean_object* v___x_2759_; lean_object* v___x_2760_; lean_object* v___x_2761_; lean_object* v___x_14557__overap_2762_; lean_object* v___x_2763_; 
lean_inc_ref_n(v___x_2749_, 6);
v___f_2750_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2750_, 0, v___x_2749_);
v___f_2751_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2751_, 0, v___x_2749_);
v___f_2752_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_2752_, 0, v___x_2749_);
v___f_2753_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_2753_, 0, v___x_2749_);
v___x_2754_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_2754_, 0, lean_box(0));
lean_closure_set(v___x_2754_, 1, lean_box(0));
lean_closure_set(v___x_2754_, 2, v___x_2749_);
v___x_2755_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2755_, 0, v___x_2754_);
lean_ctor_set(v___x_2755_, 1, v___f_2750_);
v___x_2756_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_2756_, 0, lean_box(0));
lean_closure_set(v___x_2756_, 1, lean_box(0));
lean_closure_set(v___x_2756_, 2, v___x_2749_);
v___x_2757_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2757_, 0, v___x_2755_);
lean_ctor_set(v___x_2757_, 1, v___x_2756_);
lean_ctor_set(v___x_2757_, 2, v___f_2751_);
lean_ctor_set(v___x_2757_, 3, v___f_2752_);
lean_ctor_set(v___x_2757_, 4, v___f_2753_);
v___x_2758_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_2758_, 0, lean_box(0));
lean_closure_set(v___x_2758_, 1, lean_box(0));
lean_closure_set(v___x_2758_, 2, v___x_2749_);
v___x_2759_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2759_, 0, v___x_2757_);
lean_ctor_set(v___x_2759_, 1, v___x_2758_);
v___x_2760_ = lean_box(0);
v___x_2761_ = l_instInhabitedOfMonad___redArg(v___x_2759_, v___x_2760_);
v___x_14557__overap_2762_ = lean_panic_fn_borrowed(v___x_2761_, v_msg_2720_);
lean_dec(v___x_2761_);
lean_inc(v___y_2723_);
lean_inc_ref(v___y_2722_);
v___x_2763_ = lean_apply_4(v___x_14557__overap_2762_, v___y_2721_, v___y_2722_, v___y_2723_, lean_box(0));
return v___x_2763_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4___boxed(lean_object* v_msg_2770_, lean_object* v___y_2771_, lean_object* v___y_2772_, lean_object* v___y_2773_, lean_object* v___y_2774_){
_start:
{
lean_object* v_res_2775_; 
v_res_2775_ = l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4(v_msg_2770_, v___y_2771_, v___y_2772_, v___y_2773_);
lean_dec(v___y_2773_);
lean_dec_ref(v___y_2772_);
return v_res_2775_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1_spec__2___redArg(lean_object* v_a_2776_, lean_object* v_x_2777_){
_start:
{
if (lean_obj_tag(v_x_2777_) == 0)
{
uint8_t v___x_2778_; 
v___x_2778_ = 0;
return v___x_2778_;
}
else
{
lean_object* v_key_2779_; lean_object* v_tail_2780_; uint8_t v___x_2781_; 
v_key_2779_ = lean_ctor_get(v_x_2777_, 0);
v_tail_2780_ = lean_ctor_get(v_x_2777_, 2);
v___x_2781_ = l_Lean_instBEqFVarId_beq(v_key_2779_, v_a_2776_);
if (v___x_2781_ == 0)
{
v_x_2777_ = v_tail_2780_;
goto _start;
}
else
{
return v___x_2781_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1_spec__2___redArg___boxed(lean_object* v_a_2783_, lean_object* v_x_2784_){
_start:
{
uint8_t v_res_2785_; lean_object* v_r_2786_; 
v_res_2785_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1_spec__2___redArg(v_a_2783_, v_x_2784_);
lean_dec(v_x_2784_);
lean_dec(v_a_2783_);
v_r_2786_ = lean_box(v_res_2785_);
return v_r_2786_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__4_spec__6_spec__11___redArg(lean_object* v_x_2787_, lean_object* v_x_2788_){
_start:
{
if (lean_obj_tag(v_x_2788_) == 0)
{
return v_x_2787_;
}
else
{
lean_object* v_key_2789_; lean_object* v_value_2790_; lean_object* v_tail_2791_; lean_object* v___x_2793_; uint8_t v_isShared_2794_; uint8_t v_isSharedCheck_2814_; 
v_key_2789_ = lean_ctor_get(v_x_2788_, 0);
v_value_2790_ = lean_ctor_get(v_x_2788_, 1);
v_tail_2791_ = lean_ctor_get(v_x_2788_, 2);
v_isSharedCheck_2814_ = !lean_is_exclusive(v_x_2788_);
if (v_isSharedCheck_2814_ == 0)
{
v___x_2793_ = v_x_2788_;
v_isShared_2794_ = v_isSharedCheck_2814_;
goto v_resetjp_2792_;
}
else
{
lean_inc(v_tail_2791_);
lean_inc(v_value_2790_);
lean_inc(v_key_2789_);
lean_dec(v_x_2788_);
v___x_2793_ = lean_box(0);
v_isShared_2794_ = v_isSharedCheck_2814_;
goto v_resetjp_2792_;
}
v_resetjp_2792_:
{
lean_object* v___x_2795_; uint64_t v___x_2796_; uint64_t v___x_2797_; uint64_t v___x_2798_; uint64_t v_fold_2799_; uint64_t v___x_2800_; uint64_t v___x_2801_; uint64_t v___x_2802_; size_t v___x_2803_; size_t v___x_2804_; size_t v___x_2805_; size_t v___x_2806_; size_t v___x_2807_; lean_object* v___x_2808_; lean_object* v___x_2810_; 
v___x_2795_ = lean_array_get_size(v_x_2787_);
v___x_2796_ = l_Lean_instHashableFVarId_hash(v_key_2789_);
v___x_2797_ = 32ULL;
v___x_2798_ = lean_uint64_shift_right(v___x_2796_, v___x_2797_);
v_fold_2799_ = lean_uint64_xor(v___x_2796_, v___x_2798_);
v___x_2800_ = 16ULL;
v___x_2801_ = lean_uint64_shift_right(v_fold_2799_, v___x_2800_);
v___x_2802_ = lean_uint64_xor(v_fold_2799_, v___x_2801_);
v___x_2803_ = lean_uint64_to_usize(v___x_2802_);
v___x_2804_ = lean_usize_of_nat(v___x_2795_);
v___x_2805_ = ((size_t)1ULL);
v___x_2806_ = lean_usize_sub(v___x_2804_, v___x_2805_);
v___x_2807_ = lean_usize_land(v___x_2803_, v___x_2806_);
v___x_2808_ = lean_array_uget_borrowed(v_x_2787_, v___x_2807_);
lean_inc(v___x_2808_);
if (v_isShared_2794_ == 0)
{
lean_ctor_set(v___x_2793_, 2, v___x_2808_);
v___x_2810_ = v___x_2793_;
goto v_reusejp_2809_;
}
else
{
lean_object* v_reuseFailAlloc_2813_; 
v_reuseFailAlloc_2813_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2813_, 0, v_key_2789_);
lean_ctor_set(v_reuseFailAlloc_2813_, 1, v_value_2790_);
lean_ctor_set(v_reuseFailAlloc_2813_, 2, v___x_2808_);
v___x_2810_ = v_reuseFailAlloc_2813_;
goto v_reusejp_2809_;
}
v_reusejp_2809_:
{
lean_object* v___x_2811_; 
v___x_2811_ = lean_array_uset(v_x_2787_, v___x_2807_, v___x_2810_);
v_x_2787_ = v___x_2811_;
v_x_2788_ = v_tail_2791_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__4_spec__6___redArg(lean_object* v_i_2815_, lean_object* v_source_2816_, lean_object* v_target_2817_){
_start:
{
lean_object* v___x_2818_; uint8_t v___x_2819_; 
v___x_2818_ = lean_array_get_size(v_source_2816_);
v___x_2819_ = lean_nat_dec_lt(v_i_2815_, v___x_2818_);
if (v___x_2819_ == 0)
{
lean_dec_ref(v_source_2816_);
lean_dec(v_i_2815_);
return v_target_2817_;
}
else
{
lean_object* v_es_2820_; lean_object* v___x_2821_; lean_object* v_source_2822_; lean_object* v_target_2823_; lean_object* v___x_2824_; lean_object* v___x_2825_; 
v_es_2820_ = lean_array_fget(v_source_2816_, v_i_2815_);
v___x_2821_ = lean_box(0);
v_source_2822_ = lean_array_fset(v_source_2816_, v_i_2815_, v___x_2821_);
v_target_2823_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__4_spec__6_spec__11___redArg(v_target_2817_, v_es_2820_);
v___x_2824_ = lean_unsigned_to_nat(1u);
v___x_2825_ = lean_nat_add(v_i_2815_, v___x_2824_);
lean_dec(v_i_2815_);
v_i_2815_ = v___x_2825_;
v_source_2816_ = v_source_2822_;
v_target_2817_ = v_target_2823_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__4___redArg(lean_object* v_data_2827_){
_start:
{
lean_object* v___x_2828_; lean_object* v___x_2829_; lean_object* v_nbuckets_2830_; lean_object* v___x_2831_; lean_object* v___x_2832_; lean_object* v___x_2833_; lean_object* v___x_2834_; 
v___x_2828_ = lean_array_get_size(v_data_2827_);
v___x_2829_ = lean_unsigned_to_nat(2u);
v_nbuckets_2830_ = lean_nat_mul(v___x_2828_, v___x_2829_);
v___x_2831_ = lean_unsigned_to_nat(0u);
v___x_2832_ = lean_box(0);
v___x_2833_ = lean_mk_array(v_nbuckets_2830_, v___x_2832_);
v___x_2834_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__4_spec__6___redArg(v___x_2831_, v_data_2827_, v___x_2833_);
return v___x_2834_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2___redArg(lean_object* v_m_2835_, lean_object* v_a_2836_, lean_object* v_b_2837_){
_start:
{
lean_object* v_size_2838_; lean_object* v_buckets_2839_; lean_object* v___x_2840_; uint64_t v___x_2841_; uint64_t v___x_2842_; uint64_t v___x_2843_; uint64_t v_fold_2844_; uint64_t v___x_2845_; uint64_t v___x_2846_; uint64_t v___x_2847_; size_t v___x_2848_; size_t v___x_2849_; size_t v___x_2850_; size_t v___x_2851_; size_t v___x_2852_; lean_object* v_bkt_2853_; uint8_t v___x_2854_; 
v_size_2838_ = lean_ctor_get(v_m_2835_, 0);
v_buckets_2839_ = lean_ctor_get(v_m_2835_, 1);
v___x_2840_ = lean_array_get_size(v_buckets_2839_);
v___x_2841_ = l_Lean_instHashableFVarId_hash(v_a_2836_);
v___x_2842_ = 32ULL;
v___x_2843_ = lean_uint64_shift_right(v___x_2841_, v___x_2842_);
v_fold_2844_ = lean_uint64_xor(v___x_2841_, v___x_2843_);
v___x_2845_ = 16ULL;
v___x_2846_ = lean_uint64_shift_right(v_fold_2844_, v___x_2845_);
v___x_2847_ = lean_uint64_xor(v_fold_2844_, v___x_2846_);
v___x_2848_ = lean_uint64_to_usize(v___x_2847_);
v___x_2849_ = lean_usize_of_nat(v___x_2840_);
v___x_2850_ = ((size_t)1ULL);
v___x_2851_ = lean_usize_sub(v___x_2849_, v___x_2850_);
v___x_2852_ = lean_usize_land(v___x_2848_, v___x_2851_);
v_bkt_2853_ = lean_array_uget_borrowed(v_buckets_2839_, v___x_2852_);
v___x_2854_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1_spec__2___redArg(v_a_2836_, v_bkt_2853_);
if (v___x_2854_ == 0)
{
lean_object* v___x_2856_; uint8_t v_isShared_2857_; uint8_t v_isSharedCheck_2875_; 
lean_inc_ref(v_buckets_2839_);
lean_inc(v_size_2838_);
v_isSharedCheck_2875_ = !lean_is_exclusive(v_m_2835_);
if (v_isSharedCheck_2875_ == 0)
{
lean_object* v_unused_2876_; lean_object* v_unused_2877_; 
v_unused_2876_ = lean_ctor_get(v_m_2835_, 1);
lean_dec(v_unused_2876_);
v_unused_2877_ = lean_ctor_get(v_m_2835_, 0);
lean_dec(v_unused_2877_);
v___x_2856_ = v_m_2835_;
v_isShared_2857_ = v_isSharedCheck_2875_;
goto v_resetjp_2855_;
}
else
{
lean_dec(v_m_2835_);
v___x_2856_ = lean_box(0);
v_isShared_2857_ = v_isSharedCheck_2875_;
goto v_resetjp_2855_;
}
v_resetjp_2855_:
{
lean_object* v___x_2858_; lean_object* v_size_x27_2859_; lean_object* v___x_2860_; lean_object* v_buckets_x27_2861_; lean_object* v___x_2862_; lean_object* v___x_2863_; lean_object* v___x_2864_; lean_object* v___x_2865_; lean_object* v___x_2866_; uint8_t v___x_2867_; 
v___x_2858_ = lean_unsigned_to_nat(1u);
v_size_x27_2859_ = lean_nat_add(v_size_2838_, v___x_2858_);
lean_dec(v_size_2838_);
lean_inc(v_bkt_2853_);
v___x_2860_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2860_, 0, v_a_2836_);
lean_ctor_set(v___x_2860_, 1, v_b_2837_);
lean_ctor_set(v___x_2860_, 2, v_bkt_2853_);
v_buckets_x27_2861_ = lean_array_uset(v_buckets_2839_, v___x_2852_, v___x_2860_);
v___x_2862_ = lean_unsigned_to_nat(4u);
v___x_2863_ = lean_nat_mul(v_size_x27_2859_, v___x_2862_);
v___x_2864_ = lean_unsigned_to_nat(3u);
v___x_2865_ = lean_nat_div(v___x_2863_, v___x_2864_);
lean_dec(v___x_2863_);
v___x_2866_ = lean_array_get_size(v_buckets_x27_2861_);
v___x_2867_ = lean_nat_dec_le(v___x_2865_, v___x_2866_);
lean_dec(v___x_2865_);
if (v___x_2867_ == 0)
{
lean_object* v_val_2868_; lean_object* v___x_2870_; 
v_val_2868_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__4___redArg(v_buckets_x27_2861_);
if (v_isShared_2857_ == 0)
{
lean_ctor_set(v___x_2856_, 1, v_val_2868_);
lean_ctor_set(v___x_2856_, 0, v_size_x27_2859_);
v___x_2870_ = v___x_2856_;
goto v_reusejp_2869_;
}
else
{
lean_object* v_reuseFailAlloc_2871_; 
v_reuseFailAlloc_2871_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2871_, 0, v_size_x27_2859_);
lean_ctor_set(v_reuseFailAlloc_2871_, 1, v_val_2868_);
v___x_2870_ = v_reuseFailAlloc_2871_;
goto v_reusejp_2869_;
}
v_reusejp_2869_:
{
return v___x_2870_;
}
}
else
{
lean_object* v___x_2873_; 
if (v_isShared_2857_ == 0)
{
lean_ctor_set(v___x_2856_, 1, v_buckets_x27_2861_);
lean_ctor_set(v___x_2856_, 0, v_size_x27_2859_);
v___x_2873_ = v___x_2856_;
goto v_reusejp_2872_;
}
else
{
lean_object* v_reuseFailAlloc_2874_; 
v_reuseFailAlloc_2874_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2874_, 0, v_size_x27_2859_);
lean_ctor_set(v_reuseFailAlloc_2874_, 1, v_buckets_x27_2861_);
v___x_2873_ = v_reuseFailAlloc_2874_;
goto v_reusejp_2872_;
}
v_reusejp_2872_:
{
return v___x_2873_;
}
}
}
}
else
{
lean_dec(v_b_2837_);
lean_dec(v_a_2836_);
return v_m_2835_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1___redArg(lean_object* v_m_2878_, lean_object* v_a_2879_){
_start:
{
lean_object* v_buckets_2880_; lean_object* v___x_2881_; uint64_t v___x_2882_; uint64_t v___x_2883_; uint64_t v___x_2884_; uint64_t v_fold_2885_; uint64_t v___x_2886_; uint64_t v___x_2887_; uint64_t v___x_2888_; size_t v___x_2889_; size_t v___x_2890_; size_t v___x_2891_; size_t v___x_2892_; size_t v___x_2893_; lean_object* v___x_2894_; uint8_t v___x_2895_; 
v_buckets_2880_ = lean_ctor_get(v_m_2878_, 1);
v___x_2881_ = lean_array_get_size(v_buckets_2880_);
v___x_2882_ = l_Lean_instHashableFVarId_hash(v_a_2879_);
v___x_2883_ = 32ULL;
v___x_2884_ = lean_uint64_shift_right(v___x_2882_, v___x_2883_);
v_fold_2885_ = lean_uint64_xor(v___x_2882_, v___x_2884_);
v___x_2886_ = 16ULL;
v___x_2887_ = lean_uint64_shift_right(v_fold_2885_, v___x_2886_);
v___x_2888_ = lean_uint64_xor(v_fold_2885_, v___x_2887_);
v___x_2889_ = lean_uint64_to_usize(v___x_2888_);
v___x_2890_ = lean_usize_of_nat(v___x_2881_);
v___x_2891_ = ((size_t)1ULL);
v___x_2892_ = lean_usize_sub(v___x_2890_, v___x_2891_);
v___x_2893_ = lean_usize_land(v___x_2889_, v___x_2892_);
v___x_2894_ = lean_array_uget_borrowed(v_buckets_2880_, v___x_2893_);
v___x_2895_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1_spec__2___redArg(v_a_2879_, v___x_2894_);
return v___x_2895_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1___redArg___boxed(lean_object* v_m_2896_, lean_object* v_a_2897_){
_start:
{
uint8_t v_res_2898_; lean_object* v_r_2899_; 
v_res_2898_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1___redArg(v_m_2896_, v_a_2897_);
lean_dec(v_a_2897_);
lean_dec_ref(v_m_2896_);
v_r_2899_ = lean_box(v_res_2898_);
return v_r_2899_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__6_spec__9___redArg(lean_object* v_a_2900_, lean_object* v_x_2901_){
_start:
{
if (lean_obj_tag(v_x_2901_) == 0)
{
lean_object* v___x_2902_; 
v___x_2902_ = lean_box(0);
return v___x_2902_;
}
else
{
lean_object* v_key_2903_; lean_object* v_value_2904_; lean_object* v_tail_2905_; uint8_t v___x_2906_; 
v_key_2903_ = lean_ctor_get(v_x_2901_, 0);
v_value_2904_ = lean_ctor_get(v_x_2901_, 1);
v_tail_2905_ = lean_ctor_get(v_x_2901_, 2);
v___x_2906_ = lean_expr_eqv(v_key_2903_, v_a_2900_);
if (v___x_2906_ == 0)
{
v_x_2901_ = v_tail_2905_;
goto _start;
}
else
{
lean_object* v___x_2908_; 
lean_inc(v_value_2904_);
v___x_2908_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2908_, 0, v_value_2904_);
return v___x_2908_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__6_spec__9___redArg___boxed(lean_object* v_a_2909_, lean_object* v_x_2910_){
_start:
{
lean_object* v_res_2911_; 
v_res_2911_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__6_spec__9___redArg(v_a_2909_, v_x_2910_);
lean_dec(v_x_2910_);
lean_dec_ref(v_a_2909_);
return v_res_2911_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__6___redArg(lean_object* v_m_2912_, lean_object* v_a_2913_){
_start:
{
lean_object* v_buckets_2914_; lean_object* v___x_2915_; uint64_t v___x_2916_; uint64_t v___x_2917_; uint64_t v___x_2918_; uint64_t v_fold_2919_; uint64_t v___x_2920_; uint64_t v___x_2921_; uint64_t v___x_2922_; size_t v___x_2923_; size_t v___x_2924_; size_t v___x_2925_; size_t v___x_2926_; size_t v___x_2927_; lean_object* v___x_2928_; lean_object* v___x_2929_; 
v_buckets_2914_ = lean_ctor_get(v_m_2912_, 1);
v___x_2915_ = lean_array_get_size(v_buckets_2914_);
v___x_2916_ = l_Lean_Expr_hash(v_a_2913_);
v___x_2917_ = 32ULL;
v___x_2918_ = lean_uint64_shift_right(v___x_2916_, v___x_2917_);
v_fold_2919_ = lean_uint64_xor(v___x_2916_, v___x_2918_);
v___x_2920_ = 16ULL;
v___x_2921_ = lean_uint64_shift_right(v_fold_2919_, v___x_2920_);
v___x_2922_ = lean_uint64_xor(v_fold_2919_, v___x_2921_);
v___x_2923_ = lean_uint64_to_usize(v___x_2922_);
v___x_2924_ = lean_usize_of_nat(v___x_2915_);
v___x_2925_ = ((size_t)1ULL);
v___x_2926_ = lean_usize_sub(v___x_2924_, v___x_2925_);
v___x_2927_ = lean_usize_land(v___x_2923_, v___x_2926_);
v___x_2928_ = lean_array_uget_borrowed(v_buckets_2914_, v___x_2927_);
v___x_2929_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__6_spec__9___redArg(v_a_2913_, v___x_2928_);
return v___x_2929_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__6___redArg___boxed(lean_object* v_m_2930_, lean_object* v_a_2931_){
_start:
{
lean_object* v_res_2932_; 
v_res_2932_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__6___redArg(v_m_2930_, v_a_2931_);
lean_dec_ref(v_a_2931_);
lean_dec_ref(v_m_2930_);
return v_res_2932_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__13___redArg(lean_object* v_a_2933_, lean_object* v_b_2934_, lean_object* v_x_2935_){
_start:
{
if (lean_obj_tag(v_x_2935_) == 0)
{
lean_dec(v_b_2934_);
lean_dec_ref(v_a_2933_);
return v_x_2935_;
}
else
{
lean_object* v_key_2936_; lean_object* v_value_2937_; lean_object* v_tail_2938_; lean_object* v___x_2940_; uint8_t v_isShared_2941_; uint8_t v_isSharedCheck_2950_; 
v_key_2936_ = lean_ctor_get(v_x_2935_, 0);
v_value_2937_ = lean_ctor_get(v_x_2935_, 1);
v_tail_2938_ = lean_ctor_get(v_x_2935_, 2);
v_isSharedCheck_2950_ = !lean_is_exclusive(v_x_2935_);
if (v_isSharedCheck_2950_ == 0)
{
v___x_2940_ = v_x_2935_;
v_isShared_2941_ = v_isSharedCheck_2950_;
goto v_resetjp_2939_;
}
else
{
lean_inc(v_tail_2938_);
lean_inc(v_value_2937_);
lean_inc(v_key_2936_);
lean_dec(v_x_2935_);
v___x_2940_ = lean_box(0);
v_isShared_2941_ = v_isSharedCheck_2950_;
goto v_resetjp_2939_;
}
v_resetjp_2939_:
{
uint8_t v___x_2942_; 
v___x_2942_ = lean_expr_eqv(v_key_2936_, v_a_2933_);
if (v___x_2942_ == 0)
{
lean_object* v___x_2943_; lean_object* v___x_2945_; 
v___x_2943_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__13___redArg(v_a_2933_, v_b_2934_, v_tail_2938_);
if (v_isShared_2941_ == 0)
{
lean_ctor_set(v___x_2940_, 2, v___x_2943_);
v___x_2945_ = v___x_2940_;
goto v_reusejp_2944_;
}
else
{
lean_object* v_reuseFailAlloc_2946_; 
v_reuseFailAlloc_2946_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2946_, 0, v_key_2936_);
lean_ctor_set(v_reuseFailAlloc_2946_, 1, v_value_2937_);
lean_ctor_set(v_reuseFailAlloc_2946_, 2, v___x_2943_);
v___x_2945_ = v_reuseFailAlloc_2946_;
goto v_reusejp_2944_;
}
v_reusejp_2944_:
{
return v___x_2945_;
}
}
else
{
lean_object* v___x_2948_; 
lean_dec(v_value_2937_);
lean_dec(v_key_2936_);
if (v_isShared_2941_ == 0)
{
lean_ctor_set(v___x_2940_, 1, v_b_2934_);
lean_ctor_set(v___x_2940_, 0, v_a_2933_);
v___x_2948_ = v___x_2940_;
goto v_reusejp_2947_;
}
else
{
lean_object* v_reuseFailAlloc_2949_; 
v_reuseFailAlloc_2949_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2949_, 0, v_a_2933_);
lean_ctor_set(v_reuseFailAlloc_2949_, 1, v_b_2934_);
lean_ctor_set(v_reuseFailAlloc_2949_, 2, v_tail_2938_);
v___x_2948_ = v_reuseFailAlloc_2949_;
goto v_reusejp_2947_;
}
v_reusejp_2947_:
{
return v___x_2948_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__12_spec__17_spec__18___redArg(lean_object* v_x_2951_, lean_object* v_x_2952_){
_start:
{
if (lean_obj_tag(v_x_2952_) == 0)
{
return v_x_2951_;
}
else
{
lean_object* v_key_2953_; lean_object* v_value_2954_; lean_object* v_tail_2955_; lean_object* v___x_2957_; uint8_t v_isShared_2958_; uint8_t v_isSharedCheck_2978_; 
v_key_2953_ = lean_ctor_get(v_x_2952_, 0);
v_value_2954_ = lean_ctor_get(v_x_2952_, 1);
v_tail_2955_ = lean_ctor_get(v_x_2952_, 2);
v_isSharedCheck_2978_ = !lean_is_exclusive(v_x_2952_);
if (v_isSharedCheck_2978_ == 0)
{
v___x_2957_ = v_x_2952_;
v_isShared_2958_ = v_isSharedCheck_2978_;
goto v_resetjp_2956_;
}
else
{
lean_inc(v_tail_2955_);
lean_inc(v_value_2954_);
lean_inc(v_key_2953_);
lean_dec(v_x_2952_);
v___x_2957_ = lean_box(0);
v_isShared_2958_ = v_isSharedCheck_2978_;
goto v_resetjp_2956_;
}
v_resetjp_2956_:
{
lean_object* v___x_2959_; uint64_t v___x_2960_; uint64_t v___x_2961_; uint64_t v___x_2962_; uint64_t v_fold_2963_; uint64_t v___x_2964_; uint64_t v___x_2965_; uint64_t v___x_2966_; size_t v___x_2967_; size_t v___x_2968_; size_t v___x_2969_; size_t v___x_2970_; size_t v___x_2971_; lean_object* v___x_2972_; lean_object* v___x_2974_; 
v___x_2959_ = lean_array_get_size(v_x_2951_);
v___x_2960_ = l_Lean_Expr_hash(v_key_2953_);
v___x_2961_ = 32ULL;
v___x_2962_ = lean_uint64_shift_right(v___x_2960_, v___x_2961_);
v_fold_2963_ = lean_uint64_xor(v___x_2960_, v___x_2962_);
v___x_2964_ = 16ULL;
v___x_2965_ = lean_uint64_shift_right(v_fold_2963_, v___x_2964_);
v___x_2966_ = lean_uint64_xor(v_fold_2963_, v___x_2965_);
v___x_2967_ = lean_uint64_to_usize(v___x_2966_);
v___x_2968_ = lean_usize_of_nat(v___x_2959_);
v___x_2969_ = ((size_t)1ULL);
v___x_2970_ = lean_usize_sub(v___x_2968_, v___x_2969_);
v___x_2971_ = lean_usize_land(v___x_2967_, v___x_2970_);
v___x_2972_ = lean_array_uget_borrowed(v_x_2951_, v___x_2971_);
lean_inc(v___x_2972_);
if (v_isShared_2958_ == 0)
{
lean_ctor_set(v___x_2957_, 2, v___x_2972_);
v___x_2974_ = v___x_2957_;
goto v_reusejp_2973_;
}
else
{
lean_object* v_reuseFailAlloc_2977_; 
v_reuseFailAlloc_2977_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2977_, 0, v_key_2953_);
lean_ctor_set(v_reuseFailAlloc_2977_, 1, v_value_2954_);
lean_ctor_set(v_reuseFailAlloc_2977_, 2, v___x_2972_);
v___x_2974_ = v_reuseFailAlloc_2977_;
goto v_reusejp_2973_;
}
v_reusejp_2973_:
{
lean_object* v___x_2975_; 
v___x_2975_ = lean_array_uset(v_x_2951_, v___x_2971_, v___x_2974_);
v_x_2951_ = v___x_2975_;
v_x_2952_ = v_tail_2955_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__12_spec__17___redArg(lean_object* v_i_2979_, lean_object* v_source_2980_, lean_object* v_target_2981_){
_start:
{
lean_object* v___x_2982_; uint8_t v___x_2983_; 
v___x_2982_ = lean_array_get_size(v_source_2980_);
v___x_2983_ = lean_nat_dec_lt(v_i_2979_, v___x_2982_);
if (v___x_2983_ == 0)
{
lean_dec_ref(v_source_2980_);
lean_dec(v_i_2979_);
return v_target_2981_;
}
else
{
lean_object* v_es_2984_; lean_object* v___x_2985_; lean_object* v_source_2986_; lean_object* v_target_2987_; lean_object* v___x_2988_; lean_object* v___x_2989_; 
v_es_2984_ = lean_array_fget(v_source_2980_, v_i_2979_);
v___x_2985_ = lean_box(0);
v_source_2986_ = lean_array_fset(v_source_2980_, v_i_2979_, v___x_2985_);
v_target_2987_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__12_spec__17_spec__18___redArg(v_target_2981_, v_es_2984_);
v___x_2988_ = lean_unsigned_to_nat(1u);
v___x_2989_ = lean_nat_add(v_i_2979_, v___x_2988_);
lean_dec(v_i_2979_);
v_i_2979_ = v___x_2989_;
v_source_2980_ = v_source_2986_;
v_target_2981_ = v_target_2987_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__12___redArg(lean_object* v_data_2991_){
_start:
{
lean_object* v___x_2992_; lean_object* v___x_2993_; lean_object* v_nbuckets_2994_; lean_object* v___x_2995_; lean_object* v___x_2996_; lean_object* v___x_2997_; lean_object* v___x_2998_; 
v___x_2992_ = lean_array_get_size(v_data_2991_);
v___x_2993_ = lean_unsigned_to_nat(2u);
v_nbuckets_2994_ = lean_nat_mul(v___x_2992_, v___x_2993_);
v___x_2995_ = lean_unsigned_to_nat(0u);
v___x_2996_ = lean_box(0);
v___x_2997_ = lean_mk_array(v_nbuckets_2994_, v___x_2996_);
v___x_2998_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__12_spec__17___redArg(v___x_2995_, v_data_2991_, v___x_2997_);
return v___x_2998_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__11___redArg(lean_object* v_a_2999_, lean_object* v_x_3000_){
_start:
{
if (lean_obj_tag(v_x_3000_) == 0)
{
uint8_t v___x_3001_; 
v___x_3001_ = 0;
return v___x_3001_;
}
else
{
lean_object* v_key_3002_; lean_object* v_tail_3003_; uint8_t v___x_3004_; 
v_key_3002_ = lean_ctor_get(v_x_3000_, 0);
v_tail_3003_ = lean_ctor_get(v_x_3000_, 2);
v___x_3004_ = lean_expr_eqv(v_key_3002_, v_a_2999_);
if (v___x_3004_ == 0)
{
v_x_3000_ = v_tail_3003_;
goto _start;
}
else
{
return v___x_3004_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__11___redArg___boxed(lean_object* v_a_3006_, lean_object* v_x_3007_){
_start:
{
uint8_t v_res_3008_; lean_object* v_r_3009_; 
v_res_3008_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__11___redArg(v_a_3006_, v_x_3007_);
lean_dec(v_x_3007_);
lean_dec_ref(v_a_3006_);
v_r_3009_ = lean_box(v_res_3008_);
return v_r_3009_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7___redArg(lean_object* v_m_3010_, lean_object* v_a_3011_, lean_object* v_b_3012_){
_start:
{
lean_object* v_size_3013_; lean_object* v_buckets_3014_; lean_object* v___x_3016_; uint8_t v_isShared_3017_; uint8_t v_isSharedCheck_3057_; 
v_size_3013_ = lean_ctor_get(v_m_3010_, 0);
v_buckets_3014_ = lean_ctor_get(v_m_3010_, 1);
v_isSharedCheck_3057_ = !lean_is_exclusive(v_m_3010_);
if (v_isSharedCheck_3057_ == 0)
{
v___x_3016_ = v_m_3010_;
v_isShared_3017_ = v_isSharedCheck_3057_;
goto v_resetjp_3015_;
}
else
{
lean_inc(v_buckets_3014_);
lean_inc(v_size_3013_);
lean_dec(v_m_3010_);
v___x_3016_ = lean_box(0);
v_isShared_3017_ = v_isSharedCheck_3057_;
goto v_resetjp_3015_;
}
v_resetjp_3015_:
{
lean_object* v___x_3018_; uint64_t v___x_3019_; uint64_t v___x_3020_; uint64_t v___x_3021_; uint64_t v_fold_3022_; uint64_t v___x_3023_; uint64_t v___x_3024_; uint64_t v___x_3025_; size_t v___x_3026_; size_t v___x_3027_; size_t v___x_3028_; size_t v___x_3029_; size_t v___x_3030_; lean_object* v_bkt_3031_; uint8_t v___x_3032_; 
v___x_3018_ = lean_array_get_size(v_buckets_3014_);
v___x_3019_ = l_Lean_Expr_hash(v_a_3011_);
v___x_3020_ = 32ULL;
v___x_3021_ = lean_uint64_shift_right(v___x_3019_, v___x_3020_);
v_fold_3022_ = lean_uint64_xor(v___x_3019_, v___x_3021_);
v___x_3023_ = 16ULL;
v___x_3024_ = lean_uint64_shift_right(v_fold_3022_, v___x_3023_);
v___x_3025_ = lean_uint64_xor(v_fold_3022_, v___x_3024_);
v___x_3026_ = lean_uint64_to_usize(v___x_3025_);
v___x_3027_ = lean_usize_of_nat(v___x_3018_);
v___x_3028_ = ((size_t)1ULL);
v___x_3029_ = lean_usize_sub(v___x_3027_, v___x_3028_);
v___x_3030_ = lean_usize_land(v___x_3026_, v___x_3029_);
v_bkt_3031_ = lean_array_uget_borrowed(v_buckets_3014_, v___x_3030_);
v___x_3032_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__11___redArg(v_a_3011_, v_bkt_3031_);
if (v___x_3032_ == 0)
{
lean_object* v___x_3033_; lean_object* v_size_x27_3034_; lean_object* v___x_3035_; lean_object* v_buckets_x27_3036_; lean_object* v___x_3037_; lean_object* v___x_3038_; lean_object* v___x_3039_; lean_object* v___x_3040_; lean_object* v___x_3041_; uint8_t v___x_3042_; 
v___x_3033_ = lean_unsigned_to_nat(1u);
v_size_x27_3034_ = lean_nat_add(v_size_3013_, v___x_3033_);
lean_dec(v_size_3013_);
lean_inc(v_bkt_3031_);
v___x_3035_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3035_, 0, v_a_3011_);
lean_ctor_set(v___x_3035_, 1, v_b_3012_);
lean_ctor_set(v___x_3035_, 2, v_bkt_3031_);
v_buckets_x27_3036_ = lean_array_uset(v_buckets_3014_, v___x_3030_, v___x_3035_);
v___x_3037_ = lean_unsigned_to_nat(4u);
v___x_3038_ = lean_nat_mul(v_size_x27_3034_, v___x_3037_);
v___x_3039_ = lean_unsigned_to_nat(3u);
v___x_3040_ = lean_nat_div(v___x_3038_, v___x_3039_);
lean_dec(v___x_3038_);
v___x_3041_ = lean_array_get_size(v_buckets_x27_3036_);
v___x_3042_ = lean_nat_dec_le(v___x_3040_, v___x_3041_);
lean_dec(v___x_3040_);
if (v___x_3042_ == 0)
{
lean_object* v_val_3043_; lean_object* v___x_3045_; 
v_val_3043_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__12___redArg(v_buckets_x27_3036_);
if (v_isShared_3017_ == 0)
{
lean_ctor_set(v___x_3016_, 1, v_val_3043_);
lean_ctor_set(v___x_3016_, 0, v_size_x27_3034_);
v___x_3045_ = v___x_3016_;
goto v_reusejp_3044_;
}
else
{
lean_object* v_reuseFailAlloc_3046_; 
v_reuseFailAlloc_3046_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3046_, 0, v_size_x27_3034_);
lean_ctor_set(v_reuseFailAlloc_3046_, 1, v_val_3043_);
v___x_3045_ = v_reuseFailAlloc_3046_;
goto v_reusejp_3044_;
}
v_reusejp_3044_:
{
return v___x_3045_;
}
}
else
{
lean_object* v___x_3048_; 
if (v_isShared_3017_ == 0)
{
lean_ctor_set(v___x_3016_, 1, v_buckets_x27_3036_);
lean_ctor_set(v___x_3016_, 0, v_size_x27_3034_);
v___x_3048_ = v___x_3016_;
goto v_reusejp_3047_;
}
else
{
lean_object* v_reuseFailAlloc_3049_; 
v_reuseFailAlloc_3049_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3049_, 0, v_size_x27_3034_);
lean_ctor_set(v_reuseFailAlloc_3049_, 1, v_buckets_x27_3036_);
v___x_3048_ = v_reuseFailAlloc_3049_;
goto v_reusejp_3047_;
}
v_reusejp_3047_:
{
return v___x_3048_;
}
}
}
else
{
lean_object* v___x_3050_; lean_object* v_buckets_x27_3051_; lean_object* v___x_3052_; lean_object* v___x_3053_; lean_object* v___x_3055_; 
lean_inc(v_bkt_3031_);
v___x_3050_ = lean_box(0);
v_buckets_x27_3051_ = lean_array_uset(v_buckets_3014_, v___x_3030_, v___x_3050_);
v___x_3052_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__13___redArg(v_a_3011_, v_b_3012_, v_bkt_3031_);
v___x_3053_ = lean_array_uset(v_buckets_x27_3051_, v___x_3030_, v___x_3052_);
if (v_isShared_3017_ == 0)
{
lean_ctor_set(v___x_3016_, 1, v___x_3053_);
v___x_3055_ = v___x_3016_;
goto v_reusejp_3054_;
}
else
{
lean_object* v_reuseFailAlloc_3056_; 
v_reuseFailAlloc_3056_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3056_, 0, v_size_3013_);
lean_ctor_set(v_reuseFailAlloc_3056_, 1, v___x_3053_);
v___x_3055_ = v_reuseFailAlloc_3056_;
goto v_reusejp_3054_;
}
v_reusejp_3054_:
{
return v___x_3055_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3(lean_object* v_g_3058_, lean_object* v_e_3059_, lean_object* v_a_3060_, lean_object* v___y_3061_, lean_object* v___y_3062_, lean_object* v___y_3063_){
_start:
{
lean_object* v_a_3066_; lean_object* v_fst_3067_; lean_object* v___y_3073_; lean_object* v___x_3076_; lean_object* v___x_3077_; 
v___x_3076_ = lean_st_ref_get(v_a_3060_);
v___x_3077_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__6___redArg(v___x_3076_, v_e_3059_);
lean_dec(v___x_3076_);
if (lean_obj_tag(v___x_3077_) == 0)
{
lean_object* v___x_3078_; 
lean_inc_ref(v_g_3058_);
lean_inc(v___y_3063_);
lean_inc_ref(v___y_3062_);
lean_inc_ref(v_e_3059_);
v___x_3078_ = lean_apply_5(v_g_3058_, v_e_3059_, v___y_3061_, v___y_3062_, v___y_3063_, lean_box(0));
if (lean_obj_tag(v___x_3078_) == 0)
{
lean_object* v_a_3079_; lean_object* v_fst_3080_; lean_object* v_snd_3081_; lean_object* v___x_3083_; uint8_t v_isShared_3084_; uint8_t v_isSharedCheck_3126_; 
v_a_3079_ = lean_ctor_get(v___x_3078_, 0);
lean_inc(v_a_3079_);
lean_dec_ref(v___x_3078_);
v_fst_3080_ = lean_ctor_get(v_a_3079_, 0);
v_snd_3081_ = lean_ctor_get(v_a_3079_, 1);
v_isSharedCheck_3126_ = !lean_is_exclusive(v_a_3079_);
if (v_isSharedCheck_3126_ == 0)
{
v___x_3083_ = v_a_3079_;
v_isShared_3084_ = v_isSharedCheck_3126_;
goto v_resetjp_3082_;
}
else
{
lean_inc(v_snd_3081_);
lean_inc(v_fst_3080_);
lean_dec(v_a_3079_);
v___x_3083_ = lean_box(0);
v_isShared_3084_ = v_isSharedCheck_3126_;
goto v_resetjp_3082_;
}
v_resetjp_3082_:
{
lean_object* v_d_3086_; lean_object* v_b_3087_; lean_object* v___y_3088_; uint8_t v___x_3093_; 
v___x_3093_ = lean_unbox(v_fst_3080_);
lean_dec(v_fst_3080_);
if (v___x_3093_ == 0)
{
lean_object* v___x_3094_; lean_object* v___x_3096_; 
lean_dec_ref(v_g_3058_);
v___x_3094_ = lean_box(0);
if (v_isShared_3084_ == 0)
{
lean_ctor_set(v___x_3083_, 0, v___x_3094_);
v___x_3096_ = v___x_3083_;
goto v_reusejp_3095_;
}
else
{
lean_object* v_reuseFailAlloc_3097_; 
v_reuseFailAlloc_3097_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3097_, 0, v___x_3094_);
lean_ctor_set(v_reuseFailAlloc_3097_, 1, v_snd_3081_);
v___x_3096_ = v_reuseFailAlloc_3097_;
goto v_reusejp_3095_;
}
v_reusejp_3095_:
{
v_a_3066_ = v___x_3096_;
v_fst_3067_ = v___x_3094_;
goto v___jp_3065_;
}
}
else
{
switch(lean_obj_tag(v_e_3059_))
{
case 7:
{
lean_object* v_binderType_3098_; lean_object* v_body_3099_; 
lean_del_object(v___x_3083_);
v_binderType_3098_ = lean_ctor_get(v_e_3059_, 1);
v_body_3099_ = lean_ctor_get(v_e_3059_, 2);
lean_inc_ref(v_body_3099_);
lean_inc_ref(v_binderType_3098_);
v_d_3086_ = v_binderType_3098_;
v_b_3087_ = v_body_3099_;
v___y_3088_ = v_a_3060_;
goto v___jp_3085_;
}
case 6:
{
lean_object* v_binderType_3100_; lean_object* v_body_3101_; 
lean_del_object(v___x_3083_);
v_binderType_3100_ = lean_ctor_get(v_e_3059_, 1);
v_body_3101_ = lean_ctor_get(v_e_3059_, 2);
lean_inc_ref(v_body_3101_);
lean_inc_ref(v_binderType_3100_);
v_d_3086_ = v_binderType_3100_;
v_b_3087_ = v_body_3101_;
v___y_3088_ = v_a_3060_;
goto v___jp_3085_;
}
case 8:
{
lean_object* v_type_3102_; lean_object* v_value_3103_; lean_object* v_body_3104_; lean_object* v___x_3105_; 
lean_del_object(v___x_3083_);
v_type_3102_ = lean_ctor_get(v_e_3059_, 1);
v_value_3103_ = lean_ctor_get(v_e_3059_, 2);
v_body_3104_ = lean_ctor_get(v_e_3059_, 3);
lean_inc_ref(v_type_3102_);
lean_inc_ref(v_g_3058_);
v___x_3105_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3(v_g_3058_, v_type_3102_, v_a_3060_, v_snd_3081_, v___y_3062_, v___y_3063_);
if (lean_obj_tag(v___x_3105_) == 0)
{
lean_object* v_a_3106_; lean_object* v_snd_3107_; lean_object* v___x_3108_; 
v_a_3106_ = lean_ctor_get(v___x_3105_, 0);
lean_inc(v_a_3106_);
lean_dec_ref(v___x_3105_);
v_snd_3107_ = lean_ctor_get(v_a_3106_, 1);
lean_inc(v_snd_3107_);
lean_dec(v_a_3106_);
lean_inc_ref(v_value_3103_);
lean_inc_ref(v_g_3058_);
v___x_3108_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3(v_g_3058_, v_value_3103_, v_a_3060_, v_snd_3107_, v___y_3062_, v___y_3063_);
if (lean_obj_tag(v___x_3108_) == 0)
{
lean_object* v_a_3109_; lean_object* v_snd_3110_; lean_object* v___x_3111_; 
v_a_3109_ = lean_ctor_get(v___x_3108_, 0);
lean_inc(v_a_3109_);
lean_dec_ref(v___x_3108_);
v_snd_3110_ = lean_ctor_get(v_a_3109_, 1);
lean_inc(v_snd_3110_);
lean_dec(v_a_3109_);
lean_inc_ref(v_body_3104_);
v___x_3111_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3(v_g_3058_, v_body_3104_, v_a_3060_, v_snd_3110_, v___y_3062_, v___y_3063_);
v___y_3073_ = v___x_3111_;
goto v___jp_3072_;
}
else
{
lean_dec_ref(v_g_3058_);
v___y_3073_ = v___x_3108_;
goto v___jp_3072_;
}
}
else
{
lean_dec_ref(v_g_3058_);
v___y_3073_ = v___x_3105_;
goto v___jp_3072_;
}
}
case 5:
{
lean_object* v_fn_3112_; lean_object* v_arg_3113_; lean_object* v___x_3114_; 
lean_del_object(v___x_3083_);
v_fn_3112_ = lean_ctor_get(v_e_3059_, 0);
v_arg_3113_ = lean_ctor_get(v_e_3059_, 1);
lean_inc_ref(v_fn_3112_);
lean_inc_ref(v_g_3058_);
v___x_3114_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3(v_g_3058_, v_fn_3112_, v_a_3060_, v_snd_3081_, v___y_3062_, v___y_3063_);
if (lean_obj_tag(v___x_3114_) == 0)
{
lean_object* v_a_3115_; lean_object* v_snd_3116_; lean_object* v___x_3117_; 
v_a_3115_ = lean_ctor_get(v___x_3114_, 0);
lean_inc(v_a_3115_);
lean_dec_ref(v___x_3114_);
v_snd_3116_ = lean_ctor_get(v_a_3115_, 1);
lean_inc(v_snd_3116_);
lean_dec(v_a_3115_);
lean_inc_ref(v_arg_3113_);
v___x_3117_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3(v_g_3058_, v_arg_3113_, v_a_3060_, v_snd_3116_, v___y_3062_, v___y_3063_);
v___y_3073_ = v___x_3117_;
goto v___jp_3072_;
}
else
{
lean_dec_ref(v_g_3058_);
v___y_3073_ = v___x_3114_;
goto v___jp_3072_;
}
}
case 10:
{
lean_object* v_expr_3118_; lean_object* v___x_3119_; 
lean_del_object(v___x_3083_);
v_expr_3118_ = lean_ctor_get(v_e_3059_, 1);
lean_inc_ref(v_expr_3118_);
v___x_3119_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3(v_g_3058_, v_expr_3118_, v_a_3060_, v_snd_3081_, v___y_3062_, v___y_3063_);
v___y_3073_ = v___x_3119_;
goto v___jp_3072_;
}
case 11:
{
lean_object* v_struct_3120_; lean_object* v___x_3121_; 
lean_del_object(v___x_3083_);
v_struct_3120_ = lean_ctor_get(v_e_3059_, 2);
lean_inc_ref(v_struct_3120_);
v___x_3121_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3(v_g_3058_, v_struct_3120_, v_a_3060_, v_snd_3081_, v___y_3062_, v___y_3063_);
v___y_3073_ = v___x_3121_;
goto v___jp_3072_;
}
default: 
{
lean_object* v___x_3122_; lean_object* v___x_3124_; 
lean_dec_ref(v_g_3058_);
v___x_3122_ = lean_box(0);
if (v_isShared_3084_ == 0)
{
lean_ctor_set(v___x_3083_, 0, v___x_3122_);
v___x_3124_ = v___x_3083_;
goto v_reusejp_3123_;
}
else
{
lean_object* v_reuseFailAlloc_3125_; 
v_reuseFailAlloc_3125_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3125_, 0, v___x_3122_);
lean_ctor_set(v_reuseFailAlloc_3125_, 1, v_snd_3081_);
v___x_3124_ = v_reuseFailAlloc_3125_;
goto v_reusejp_3123_;
}
v_reusejp_3123_:
{
v_a_3066_ = v___x_3124_;
v_fst_3067_ = v___x_3122_;
goto v___jp_3065_;
}
}
}
}
v___jp_3085_:
{
lean_object* v___x_3089_; 
lean_inc_ref(v_g_3058_);
v___x_3089_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3(v_g_3058_, v_d_3086_, v___y_3088_, v_snd_3081_, v___y_3062_, v___y_3063_);
if (lean_obj_tag(v___x_3089_) == 0)
{
lean_object* v_a_3090_; lean_object* v_snd_3091_; lean_object* v___x_3092_; 
v_a_3090_ = lean_ctor_get(v___x_3089_, 0);
lean_inc(v_a_3090_);
lean_dec_ref(v___x_3089_);
v_snd_3091_ = lean_ctor_get(v_a_3090_, 1);
lean_inc(v_snd_3091_);
lean_dec(v_a_3090_);
v___x_3092_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3(v_g_3058_, v_b_3087_, v___y_3088_, v_snd_3091_, v___y_3062_, v___y_3063_);
v___y_3073_ = v___x_3092_;
goto v___jp_3072_;
}
else
{
lean_dec_ref(v_b_3087_);
lean_dec_ref(v_g_3058_);
v___y_3073_ = v___x_3089_;
goto v___jp_3072_;
}
}
}
}
else
{
lean_object* v_a_3127_; lean_object* v___x_3129_; uint8_t v_isShared_3130_; uint8_t v_isSharedCheck_3134_; 
lean_dec_ref(v_e_3059_);
lean_dec_ref(v_g_3058_);
v_a_3127_ = lean_ctor_get(v___x_3078_, 0);
v_isSharedCheck_3134_ = !lean_is_exclusive(v___x_3078_);
if (v_isSharedCheck_3134_ == 0)
{
v___x_3129_ = v___x_3078_;
v_isShared_3130_ = v_isSharedCheck_3134_;
goto v_resetjp_3128_;
}
else
{
lean_inc(v_a_3127_);
lean_dec(v___x_3078_);
v___x_3129_ = lean_box(0);
v_isShared_3130_ = v_isSharedCheck_3134_;
goto v_resetjp_3128_;
}
v_resetjp_3128_:
{
lean_object* v___x_3132_; 
if (v_isShared_3130_ == 0)
{
v___x_3132_ = v___x_3129_;
goto v_reusejp_3131_;
}
else
{
lean_object* v_reuseFailAlloc_3133_; 
v_reuseFailAlloc_3133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3133_, 0, v_a_3127_);
v___x_3132_ = v_reuseFailAlloc_3133_;
goto v_reusejp_3131_;
}
v_reusejp_3131_:
{
return v___x_3132_;
}
}
}
}
else
{
lean_object* v_val_3135_; lean_object* v___x_3137_; uint8_t v_isShared_3138_; uint8_t v_isSharedCheck_3143_; 
lean_dec_ref(v_e_3059_);
lean_dec_ref(v_g_3058_);
v_val_3135_ = lean_ctor_get(v___x_3077_, 0);
v_isSharedCheck_3143_ = !lean_is_exclusive(v___x_3077_);
if (v_isSharedCheck_3143_ == 0)
{
v___x_3137_ = v___x_3077_;
v_isShared_3138_ = v_isSharedCheck_3143_;
goto v_resetjp_3136_;
}
else
{
lean_inc(v_val_3135_);
lean_dec(v___x_3077_);
v___x_3137_ = lean_box(0);
v_isShared_3138_ = v_isSharedCheck_3143_;
goto v_resetjp_3136_;
}
v_resetjp_3136_:
{
lean_object* v___x_3139_; lean_object* v___x_3141_; 
v___x_3139_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3139_, 0, v_val_3135_);
lean_ctor_set(v___x_3139_, 1, v___y_3061_);
if (v_isShared_3138_ == 0)
{
lean_ctor_set_tag(v___x_3137_, 0);
lean_ctor_set(v___x_3137_, 0, v___x_3139_);
v___x_3141_ = v___x_3137_;
goto v_reusejp_3140_;
}
else
{
lean_object* v_reuseFailAlloc_3142_; 
v_reuseFailAlloc_3142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3142_, 0, v___x_3139_);
v___x_3141_ = v_reuseFailAlloc_3142_;
goto v_reusejp_3140_;
}
v_reusejp_3140_:
{
return v___x_3141_;
}
}
}
v___jp_3065_:
{
lean_object* v___x_3068_; lean_object* v___x_3069_; lean_object* v___x_3070_; lean_object* v___x_3071_; 
v___x_3068_ = lean_st_ref_take(v_a_3060_);
v___x_3069_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7___redArg(v___x_3068_, v_e_3059_, v_fst_3067_);
v___x_3070_ = lean_st_ref_set(v_a_3060_, v___x_3069_);
v___x_3071_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3071_, 0, v_a_3066_);
return v___x_3071_;
}
v___jp_3072_:
{
if (lean_obj_tag(v___y_3073_) == 0)
{
lean_object* v_a_3074_; lean_object* v_fst_3075_; 
v_a_3074_ = lean_ctor_get(v___y_3073_, 0);
lean_inc(v_a_3074_);
lean_dec_ref(v___y_3073_);
v_fst_3075_ = lean_ctor_get(v_a_3074_, 0);
lean_inc(v_fst_3075_);
v_a_3066_ = v_a_3074_;
v_fst_3067_ = v_fst_3075_;
goto v___jp_3065_;
}
else
{
lean_dec_ref(v_e_3059_);
return v___y_3073_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3___boxed(lean_object* v_g_3144_, lean_object* v_e_3145_, lean_object* v_a_3146_, lean_object* v___y_3147_, lean_object* v___y_3148_, lean_object* v___y_3149_, lean_object* v___y_3150_){
_start:
{
lean_object* v_res_3151_; 
v_res_3151_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3(v_g_3144_, v_e_3145_, v_a_3146_, v___y_3147_, v___y_3148_, v___y_3149_);
lean_dec(v___y_3149_);
lean_dec_ref(v___y_3148_);
lean_dec(v_a_3146_);
return v_res_3151_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__0(void){
_start:
{
lean_object* v___x_3152_; 
v___x_3152_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_3152_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__1(void){
_start:
{
lean_object* v___x_3153_; lean_object* v___x_3154_; 
v___x_3153_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__0);
v___x_3154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3154_, 0, v___x_3153_);
return v___x_3154_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__2(void){
_start:
{
lean_object* v___x_3155_; lean_object* v___x_3156_; lean_object* v___x_3157_; 
v___x_3155_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__1);
v___x_3156_ = lean_unsigned_to_nat(0u);
v___x_3157_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_3157_, 0, v___x_3156_);
lean_ctor_set(v___x_3157_, 1, v___x_3156_);
lean_ctor_set(v___x_3157_, 2, v___x_3156_);
lean_ctor_set(v___x_3157_, 3, v___x_3156_);
lean_ctor_set(v___x_3157_, 4, v___x_3155_);
lean_ctor_set(v___x_3157_, 5, v___x_3155_);
lean_ctor_set(v___x_3157_, 6, v___x_3155_);
lean_ctor_set(v___x_3157_, 7, v___x_3155_);
lean_ctor_set(v___x_3157_, 8, v___x_3155_);
lean_ctor_set(v___x_3157_, 9, v___x_3155_);
return v___x_3157_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__3(void){
_start:
{
lean_object* v___x_3158_; lean_object* v___x_3159_; lean_object* v___x_3160_; 
v___x_3158_ = lean_unsigned_to_nat(32u);
v___x_3159_ = lean_mk_empty_array_with_capacity(v___x_3158_);
v___x_3160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3160_, 0, v___x_3159_);
return v___x_3160_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__4(void){
_start:
{
size_t v___x_3161_; lean_object* v___x_3162_; lean_object* v___x_3163_; lean_object* v___x_3164_; lean_object* v___x_3165_; lean_object* v___x_3166_; 
v___x_3161_ = ((size_t)5ULL);
v___x_3162_ = lean_unsigned_to_nat(0u);
v___x_3163_ = lean_unsigned_to_nat(32u);
v___x_3164_ = lean_mk_empty_array_with_capacity(v___x_3163_);
v___x_3165_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__3);
v___x_3166_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3166_, 0, v___x_3165_);
lean_ctor_set(v___x_3166_, 1, v___x_3164_);
lean_ctor_set(v___x_3166_, 2, v___x_3162_);
lean_ctor_set(v___x_3166_, 3, v___x_3162_);
lean_ctor_set_usize(v___x_3166_, 4, v___x_3161_);
return v___x_3166_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__5(void){
_start:
{
lean_object* v___x_3167_; lean_object* v___x_3168_; lean_object* v___x_3169_; lean_object* v___x_3170_; 
v___x_3167_ = lean_box(1);
v___x_3168_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__4);
v___x_3169_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__1);
v___x_3170_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3170_, 0, v___x_3169_);
lean_ctor_set(v___x_3170_, 1, v___x_3168_);
lean_ctor_set(v___x_3170_, 2, v___x_3167_);
return v___x_3170_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10(lean_object* v_msgData_3171_, lean_object* v___y_3172_, lean_object* v___y_3173_){
_start:
{
lean_object* v___x_3175_; lean_object* v_env_3176_; lean_object* v_options_3177_; lean_object* v___x_3178_; lean_object* v___x_3179_; lean_object* v___x_3180_; lean_object* v___x_3181_; lean_object* v___x_3182_; 
v___x_3175_ = lean_st_ref_get(v___y_3173_);
v_env_3176_ = lean_ctor_get(v___x_3175_, 0);
lean_inc_ref(v_env_3176_);
lean_dec(v___x_3175_);
v_options_3177_ = lean_ctor_get(v___y_3172_, 2);
v___x_3178_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__2);
v___x_3179_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__5);
lean_inc_ref(v_options_3177_);
v___x_3180_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3180_, 0, v_env_3176_);
lean_ctor_set(v___x_3180_, 1, v___x_3178_);
lean_ctor_set(v___x_3180_, 2, v___x_3179_);
lean_ctor_set(v___x_3180_, 3, v_options_3177_);
v___x_3181_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_3181_, 0, v___x_3180_);
lean_ctor_set(v___x_3181_, 1, v_msgData_3171_);
v___x_3182_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3182_, 0, v___x_3181_);
return v___x_3182_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___boxed(lean_object* v_msgData_3183_, lean_object* v___y_3184_, lean_object* v___y_3185_, lean_object* v___y_3186_){
_start:
{
lean_object* v_res_3187_; 
v_res_3187_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10(v_msgData_3183_, v___y_3184_, v___y_3185_);
lean_dec(v___y_3185_);
lean_dec_ref(v___y_3184_);
return v_res_3187_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5___redArg(lean_object* v_msg_3188_, lean_object* v___y_3189_, lean_object* v___y_3190_){
_start:
{
lean_object* v_ref_3192_; lean_object* v___x_3193_; lean_object* v_a_3194_; lean_object* v___x_3196_; uint8_t v_isShared_3197_; uint8_t v_isSharedCheck_3202_; 
v_ref_3192_ = lean_ctor_get(v___y_3189_, 5);
v___x_3193_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10(v_msg_3188_, v___y_3189_, v___y_3190_);
v_a_3194_ = lean_ctor_get(v___x_3193_, 0);
v_isSharedCheck_3202_ = !lean_is_exclusive(v___x_3193_);
if (v_isSharedCheck_3202_ == 0)
{
v___x_3196_ = v___x_3193_;
v_isShared_3197_ = v_isSharedCheck_3202_;
goto v_resetjp_3195_;
}
else
{
lean_inc(v_a_3194_);
lean_dec(v___x_3193_);
v___x_3196_ = lean_box(0);
v_isShared_3197_ = v_isSharedCheck_3202_;
goto v_resetjp_3195_;
}
v_resetjp_3195_:
{
lean_object* v___x_3198_; lean_object* v___x_3200_; 
lean_inc(v_ref_3192_);
v___x_3198_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3198_, 0, v_ref_3192_);
lean_ctor_set(v___x_3198_, 1, v_a_3194_);
if (v_isShared_3197_ == 0)
{
lean_ctor_set_tag(v___x_3196_, 1);
lean_ctor_set(v___x_3196_, 0, v___x_3198_);
v___x_3200_ = v___x_3196_;
goto v_reusejp_3199_;
}
else
{
lean_object* v_reuseFailAlloc_3201_; 
v_reuseFailAlloc_3201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3201_, 0, v___x_3198_);
v___x_3200_ = v_reuseFailAlloc_3201_;
goto v_reusejp_3199_;
}
v_reusejp_3199_:
{
return v___x_3200_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5___redArg___boxed(lean_object* v_msg_3203_, lean_object* v___y_3204_, lean_object* v___y_3205_, lean_object* v___y_3206_){
_start:
{
lean_object* v_res_3207_; 
v_res_3207_ = l_Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5___redArg(v_msg_3203_, v___y_3204_, v___y_3205_);
lean_dec(v___y_3205_);
lean_dec_ref(v___y_3204_);
return v_res_3207_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6___closed__0(void){
_start:
{
lean_object* v___x_3208_; double v___x_3209_; 
v___x_3208_ = lean_unsigned_to_nat(0u);
v___x_3209_ = lean_float_of_nat(v___x_3208_);
return v___x_3209_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6(lean_object* v_cls_3213_, lean_object* v_msg_3214_, lean_object* v___y_3215_, lean_object* v___y_3216_, lean_object* v___y_3217_){
_start:
{
lean_object* v_ref_3219_; lean_object* v___x_3220_; lean_object* v_a_3221_; lean_object* v___x_3223_; uint8_t v_isShared_3224_; uint8_t v_isSharedCheck_3266_; 
v_ref_3219_ = lean_ctor_get(v___y_3216_, 5);
v___x_3220_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10(v_msg_3214_, v___y_3216_, v___y_3217_);
v_a_3221_ = lean_ctor_get(v___x_3220_, 0);
v_isSharedCheck_3266_ = !lean_is_exclusive(v___x_3220_);
if (v_isSharedCheck_3266_ == 0)
{
v___x_3223_ = v___x_3220_;
v_isShared_3224_ = v_isSharedCheck_3266_;
goto v_resetjp_3222_;
}
else
{
lean_inc(v_a_3221_);
lean_dec(v___x_3220_);
v___x_3223_ = lean_box(0);
v_isShared_3224_ = v_isSharedCheck_3266_;
goto v_resetjp_3222_;
}
v_resetjp_3222_:
{
lean_object* v___x_3225_; lean_object* v_traceState_3226_; lean_object* v_env_3227_; lean_object* v_nextMacroScope_3228_; lean_object* v_ngen_3229_; lean_object* v_auxDeclNGen_3230_; lean_object* v_cache_3231_; lean_object* v_messages_3232_; lean_object* v_infoState_3233_; lean_object* v_snapshotTasks_3234_; lean_object* v___x_3236_; uint8_t v_isShared_3237_; uint8_t v_isSharedCheck_3265_; 
v___x_3225_ = lean_st_ref_take(v___y_3217_);
v_traceState_3226_ = lean_ctor_get(v___x_3225_, 4);
v_env_3227_ = lean_ctor_get(v___x_3225_, 0);
v_nextMacroScope_3228_ = lean_ctor_get(v___x_3225_, 1);
v_ngen_3229_ = lean_ctor_get(v___x_3225_, 2);
v_auxDeclNGen_3230_ = lean_ctor_get(v___x_3225_, 3);
v_cache_3231_ = lean_ctor_get(v___x_3225_, 5);
v_messages_3232_ = lean_ctor_get(v___x_3225_, 6);
v_infoState_3233_ = lean_ctor_get(v___x_3225_, 7);
v_snapshotTasks_3234_ = lean_ctor_get(v___x_3225_, 8);
v_isSharedCheck_3265_ = !lean_is_exclusive(v___x_3225_);
if (v_isSharedCheck_3265_ == 0)
{
v___x_3236_ = v___x_3225_;
v_isShared_3237_ = v_isSharedCheck_3265_;
goto v_resetjp_3235_;
}
else
{
lean_inc(v_snapshotTasks_3234_);
lean_inc(v_infoState_3233_);
lean_inc(v_messages_3232_);
lean_inc(v_cache_3231_);
lean_inc(v_traceState_3226_);
lean_inc(v_auxDeclNGen_3230_);
lean_inc(v_ngen_3229_);
lean_inc(v_nextMacroScope_3228_);
lean_inc(v_env_3227_);
lean_dec(v___x_3225_);
v___x_3236_ = lean_box(0);
v_isShared_3237_ = v_isSharedCheck_3265_;
goto v_resetjp_3235_;
}
v_resetjp_3235_:
{
uint64_t v_tid_3238_; lean_object* v_traces_3239_; lean_object* v___x_3241_; uint8_t v_isShared_3242_; uint8_t v_isSharedCheck_3264_; 
v_tid_3238_ = lean_ctor_get_uint64(v_traceState_3226_, sizeof(void*)*1);
v_traces_3239_ = lean_ctor_get(v_traceState_3226_, 0);
v_isSharedCheck_3264_ = !lean_is_exclusive(v_traceState_3226_);
if (v_isSharedCheck_3264_ == 0)
{
v___x_3241_ = v_traceState_3226_;
v_isShared_3242_ = v_isSharedCheck_3264_;
goto v_resetjp_3240_;
}
else
{
lean_inc(v_traces_3239_);
lean_dec(v_traceState_3226_);
v___x_3241_ = lean_box(0);
v_isShared_3242_ = v_isSharedCheck_3264_;
goto v_resetjp_3240_;
}
v_resetjp_3240_:
{
lean_object* v___x_3243_; double v___x_3244_; uint8_t v___x_3245_; lean_object* v___x_3246_; lean_object* v___x_3247_; lean_object* v___x_3248_; lean_object* v___x_3249_; lean_object* v___x_3250_; lean_object* v___x_3251_; lean_object* v___x_3253_; 
v___x_3243_ = lean_box(0);
v___x_3244_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6___closed__0);
v___x_3245_ = 0;
v___x_3246_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6___closed__1));
v___x_3247_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3247_, 0, v_cls_3213_);
lean_ctor_set(v___x_3247_, 1, v___x_3243_);
lean_ctor_set(v___x_3247_, 2, v___x_3246_);
lean_ctor_set_float(v___x_3247_, sizeof(void*)*3, v___x_3244_);
lean_ctor_set_float(v___x_3247_, sizeof(void*)*3 + 8, v___x_3244_);
lean_ctor_set_uint8(v___x_3247_, sizeof(void*)*3 + 16, v___x_3245_);
v___x_3248_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6___closed__2));
v___x_3249_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3249_, 0, v___x_3247_);
lean_ctor_set(v___x_3249_, 1, v_a_3221_);
lean_ctor_set(v___x_3249_, 2, v___x_3248_);
lean_inc(v_ref_3219_);
v___x_3250_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3250_, 0, v_ref_3219_);
lean_ctor_set(v___x_3250_, 1, v___x_3249_);
v___x_3251_ = l_Lean_PersistentArray_push___redArg(v_traces_3239_, v___x_3250_);
if (v_isShared_3242_ == 0)
{
lean_ctor_set(v___x_3241_, 0, v___x_3251_);
v___x_3253_ = v___x_3241_;
goto v_reusejp_3252_;
}
else
{
lean_object* v_reuseFailAlloc_3263_; 
v_reuseFailAlloc_3263_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3263_, 0, v___x_3251_);
lean_ctor_set_uint64(v_reuseFailAlloc_3263_, sizeof(void*)*1, v_tid_3238_);
v___x_3253_ = v_reuseFailAlloc_3263_;
goto v_reusejp_3252_;
}
v_reusejp_3252_:
{
lean_object* v___x_3255_; 
if (v_isShared_3237_ == 0)
{
lean_ctor_set(v___x_3236_, 4, v___x_3253_);
v___x_3255_ = v___x_3236_;
goto v_reusejp_3254_;
}
else
{
lean_object* v_reuseFailAlloc_3262_; 
v_reuseFailAlloc_3262_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3262_, 0, v_env_3227_);
lean_ctor_set(v_reuseFailAlloc_3262_, 1, v_nextMacroScope_3228_);
lean_ctor_set(v_reuseFailAlloc_3262_, 2, v_ngen_3229_);
lean_ctor_set(v_reuseFailAlloc_3262_, 3, v_auxDeclNGen_3230_);
lean_ctor_set(v_reuseFailAlloc_3262_, 4, v___x_3253_);
lean_ctor_set(v_reuseFailAlloc_3262_, 5, v_cache_3231_);
lean_ctor_set(v_reuseFailAlloc_3262_, 6, v_messages_3232_);
lean_ctor_set(v_reuseFailAlloc_3262_, 7, v_infoState_3233_);
lean_ctor_set(v_reuseFailAlloc_3262_, 8, v_snapshotTasks_3234_);
v___x_3255_ = v_reuseFailAlloc_3262_;
goto v_reusejp_3254_;
}
v_reusejp_3254_:
{
lean_object* v___x_3256_; lean_object* v___x_3257_; lean_object* v___x_3258_; lean_object* v___x_3260_; 
v___x_3256_ = lean_st_ref_set(v___y_3217_, v___x_3255_);
v___x_3257_ = lean_box(0);
v___x_3258_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3258_, 0, v___x_3257_);
lean_ctor_set(v___x_3258_, 1, v___y_3215_);
if (v_isShared_3224_ == 0)
{
lean_ctor_set(v___x_3223_, 0, v___x_3258_);
v___x_3260_ = v___x_3223_;
goto v_reusejp_3259_;
}
else
{
lean_object* v_reuseFailAlloc_3261_; 
v_reuseFailAlloc_3261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3261_, 0, v___x_3258_);
v___x_3260_ = v_reuseFailAlloc_3261_;
goto v_reusejp_3259_;
}
v_reusejp_3259_:
{
return v___x_3260_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6___boxed(lean_object* v_cls_3267_, lean_object* v_msg_3268_, lean_object* v___y_3269_, lean_object* v___y_3270_, lean_object* v___y_3271_, lean_object* v___y_3272_){
_start:
{
lean_object* v_res_3273_; 
v_res_3273_ = l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6(v_cls_3267_, v_msg_3268_, v___y_3269_, v___y_3270_, v___y_3271_);
lean_dec(v___y_3271_);
lean_dec_ref(v___y_3270_);
return v_res_3273_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0_spec__0___redArg(lean_object* v_a_3274_, lean_object* v_x_3275_){
_start:
{
if (lean_obj_tag(v_x_3275_) == 0)
{
lean_object* v___x_3276_; 
v___x_3276_ = lean_box(0);
return v___x_3276_;
}
else
{
lean_object* v_key_3277_; lean_object* v_value_3278_; lean_object* v_tail_3279_; uint8_t v___x_3280_; 
v_key_3277_ = lean_ctor_get(v_x_3275_, 0);
v_value_3278_ = lean_ctor_get(v_x_3275_, 1);
v_tail_3279_ = lean_ctor_get(v_x_3275_, 2);
v___x_3280_ = l_Lean_instBEqFVarId_beq(v_key_3277_, v_a_3274_);
if (v___x_3280_ == 0)
{
v_x_3275_ = v_tail_3279_;
goto _start;
}
else
{
lean_object* v___x_3282_; 
lean_inc(v_value_3278_);
v___x_3282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3282_, 0, v_value_3278_);
return v___x_3282_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0_spec__0___redArg___boxed(lean_object* v_a_3283_, lean_object* v_x_3284_){
_start:
{
lean_object* v_res_3285_; 
v_res_3285_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0_spec__0___redArg(v_a_3283_, v_x_3284_);
lean_dec(v_x_3284_);
lean_dec(v_a_3283_);
return v_res_3285_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0___redArg(lean_object* v_m_3286_, lean_object* v_a_3287_){
_start:
{
lean_object* v_buckets_3288_; lean_object* v___x_3289_; uint64_t v___x_3290_; uint64_t v___x_3291_; uint64_t v___x_3292_; uint64_t v_fold_3293_; uint64_t v___x_3294_; uint64_t v___x_3295_; uint64_t v___x_3296_; size_t v___x_3297_; size_t v___x_3298_; size_t v___x_3299_; size_t v___x_3300_; size_t v___x_3301_; lean_object* v___x_3302_; lean_object* v___x_3303_; 
v_buckets_3288_ = lean_ctor_get(v_m_3286_, 1);
v___x_3289_ = lean_array_get_size(v_buckets_3288_);
v___x_3290_ = l_Lean_instHashableFVarId_hash(v_a_3287_);
v___x_3291_ = 32ULL;
v___x_3292_ = lean_uint64_shift_right(v___x_3290_, v___x_3291_);
v_fold_3293_ = lean_uint64_xor(v___x_3290_, v___x_3292_);
v___x_3294_ = 16ULL;
v___x_3295_ = lean_uint64_shift_right(v_fold_3293_, v___x_3294_);
v___x_3296_ = lean_uint64_xor(v_fold_3293_, v___x_3295_);
v___x_3297_ = lean_uint64_to_usize(v___x_3296_);
v___x_3298_ = lean_usize_of_nat(v___x_3289_);
v___x_3299_ = ((size_t)1ULL);
v___x_3300_ = lean_usize_sub(v___x_3298_, v___x_3299_);
v___x_3301_ = lean_usize_land(v___x_3297_, v___x_3300_);
v___x_3302_ = lean_array_uget_borrowed(v_buckets_3288_, v___x_3301_);
v___x_3303_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0_spec__0___redArg(v_a_3287_, v___x_3302_);
return v___x_3303_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0___redArg___boxed(lean_object* v_m_3304_, lean_object* v_a_3305_){
_start:
{
lean_object* v_res_3306_; 
v_res_3306_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0___redArg(v_m_3304_, v_a_3305_);
lean_dec(v_a_3305_);
lean_dec_ref(v_m_3304_);
return v_res_3306_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___lam__0___boxed(lean_object* v___x_3307_, lean_object* v_m_3308_, lean_object* v_e_3309_, lean_object* v___y_3310_, lean_object* v___y_3311_, lean_object* v___y_3312_, lean_object* v___y_3313_){
_start:
{
uint8_t v___x_19748__boxed_3314_; lean_object* v_res_3315_; 
v___x_19748__boxed_3314_ = lean_unbox(v___x_3307_);
v_res_3315_ = l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___lam__0(v___x_19748__boxed_3314_, v_m_3308_, v_e_3309_, v___y_3310_, v___y_3311_, v___y_3312_);
lean_dec(v___y_3312_);
lean_dec_ref(v___y_3311_);
lean_dec_ref(v_e_3309_);
return v_res_3315_;
}
}
static lean_object* _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__0(void){
_start:
{
lean_object* v___x_3316_; lean_object* v___x_3317_; lean_object* v___x_3318_; 
v___x_3316_ = lean_box(0);
v___x_3317_ = lean_unsigned_to_nat(16u);
v___x_3318_ = lean_mk_array(v___x_3317_, v___x_3316_);
return v___x_3318_;
}
}
static lean_object* _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__1(void){
_start:
{
lean_object* v___x_3319_; lean_object* v___x_3320_; lean_object* v___x_3321_; 
v___x_3319_ = lean_obj_once(&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__0, &l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__0_once, _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__0);
v___x_3320_ = lean_unsigned_to_nat(0u);
v___x_3321_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3321_, 0, v___x_3320_);
lean_ctor_set(v___x_3321_, 1, v___x_3319_);
return v___x_3321_;
}
}
static lean_object* _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__5(void){
_start:
{
lean_object* v___x_3325_; lean_object* v___x_3326_; lean_object* v___x_3327_; lean_object* v___x_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; 
v___x_3325_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__4));
v___x_3326_ = lean_unsigned_to_nat(4u);
v___x_3327_ = lean_unsigned_to_nat(384u);
v___x_3328_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__3));
v___x_3329_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__2));
v___x_3330_ = l_mkPanicMessageWithDecl(v___x_3329_, v___x_3328_, v___x_3327_, v___x_3326_, v___x_3325_);
return v___x_3330_;
}
}
static lean_object* _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__7(void){
_start:
{
lean_object* v___x_3332_; lean_object* v___x_3333_; 
v___x_3332_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__6));
v___x_3333_ = l_Lean_stringToMessageData(v___x_3332_);
return v___x_3333_;
}
}
static lean_object* _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__13(void){
_start:
{
lean_object* v___x_3342_; lean_object* v___x_3343_; lean_object* v___x_3344_; 
v___x_3342_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__10));
v___x_3343_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__12));
v___x_3344_ = l_Lean_Name_append(v___x_3343_, v___x_3342_);
return v___x_3344_;
}
}
static lean_object* _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__15(void){
_start:
{
lean_object* v___x_3346_; lean_object* v___x_3347_; 
v___x_3346_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__14));
v___x_3347_ = l_Lean_stringToMessageData(v___x_3346_);
return v___x_3347_;
}
}
static lean_object* _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__17(void){
_start:
{
lean_object* v___x_3349_; lean_object* v___x_3350_; 
v___x_3349_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__16));
v___x_3350_ = l_Lean_stringToMessageData(v___x_3349_);
return v___x_3350_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit(lean_object* v_m_3351_, lean_object* v_fvarId_3352_, lean_object* v_a_3353_, lean_object* v_a_3354_, lean_object* v_a_3355_){
_start:
{
lean_object* v___x_3357_; 
v___x_3357_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0___redArg(v_m_3351_, v_fvarId_3352_);
if (lean_obj_tag(v___x_3357_) == 1)
{
lean_object* v_val_3358_; lean_object* v___x_3360_; uint8_t v_isShared_3361_; uint8_t v_isSharedCheck_3471_; 
v_val_3358_ = lean_ctor_get(v___x_3357_, 0);
v_isSharedCheck_3471_ = !lean_is_exclusive(v___x_3357_);
if (v_isSharedCheck_3471_ == 0)
{
v___x_3360_ = v___x_3357_;
v_isShared_3361_ = v_isSharedCheck_3471_;
goto v_resetjp_3359_;
}
else
{
lean_inc(v_val_3358_);
lean_dec(v___x_3357_);
v___x_3360_ = lean_box(0);
v_isShared_3361_ = v_isSharedCheck_3471_;
goto v_resetjp_3359_;
}
v_resetjp_3359_:
{
lean_object* v_fst_3362_; lean_object* v_snd_3363_; lean_object* v___x_3365_; uint8_t v_isShared_3366_; uint8_t v_isSharedCheck_3470_; 
v_fst_3362_ = lean_ctor_get(v_val_3358_, 0);
v_snd_3363_ = lean_ctor_get(v_val_3358_, 1);
v_isSharedCheck_3470_ = !lean_is_exclusive(v_val_3358_);
if (v_isSharedCheck_3470_ == 0)
{
v___x_3365_ = v_val_3358_;
v_isShared_3366_ = v_isSharedCheck_3470_;
goto v_resetjp_3364_;
}
else
{
lean_inc(v_snd_3363_);
lean_inc(v_fst_3362_);
lean_dec(v_val_3358_);
v___x_3365_ = lean_box(0);
v_isShared_3366_ = v_isSharedCheck_3470_;
goto v_resetjp_3364_;
}
v_resetjp_3364_:
{
lean_object* v_tempMark_3367_; lean_object* v_doneMark_3368_; lean_object* v___x_3369_; uint8_t v___x_3370_; 
v_tempMark_3367_ = lean_ctor_get(v_a_3353_, 0);
v_doneMark_3368_ = lean_ctor_get(v_a_3353_, 1);
v___x_3369_ = l_Lean_LocalDecl_fvarId(v_fst_3362_);
v___x_3370_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1___redArg(v_doneMark_3368_, v___x_3369_);
if (v___x_3370_ == 0)
{
lean_object* v_options_3371_; lean_object* v_inheritedTraceOptions_3372_; uint8_t v_hasTrace_3373_; uint8_t v___x_3374_; lean_object* v___x_3375_; lean_object* v___f_3376_; lean_object* v___y_3378_; lean_object* v___y_3379_; lean_object* v___y_3380_; lean_object* v___y_3431_; lean_object* v___y_3432_; lean_object* v___y_3433_; lean_object* v___y_3438_; lean_object* v_tempMark_3439_; lean_object* v___y_3440_; lean_object* v___y_3441_; 
lean_del_object(v___x_3365_);
lean_del_object(v___x_3360_);
v_options_3371_ = lean_ctor_get(v_a_3354_, 2);
v_inheritedTraceOptions_3372_ = lean_ctor_get(v_a_3354_, 13);
v_hasTrace_3373_ = lean_ctor_get_uint8(v_options_3371_, sizeof(void*)*1);
v___x_3374_ = 1;
v___x_3375_ = lean_box(v___x_3374_);
v___f_3376_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___lam__0___boxed), 7, 2);
lean_closure_set(v___f_3376_, 0, v___x_3375_);
lean_closure_set(v___f_3376_, 1, v_m_3351_);
if (v_hasTrace_3373_ == 0)
{
lean_inc_ref(v_tempMark_3367_);
v___y_3438_ = v_a_3353_;
v_tempMark_3439_ = v_tempMark_3367_;
v___y_3440_ = v_a_3354_;
v___y_3441_ = v_a_3355_;
goto v___jp_3437_;
}
else
{
lean_object* v___x_3447_; lean_object* v___x_3448_; uint8_t v___x_3449_; 
v___x_3447_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__10));
v___x_3448_ = lean_obj_once(&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__13, &l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__13_once, _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__13);
v___x_3449_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3372_, v_options_3371_, v___x_3448_);
if (v___x_3449_ == 0)
{
lean_inc_ref(v_tempMark_3367_);
v___y_3438_ = v_a_3353_;
v_tempMark_3439_ = v_tempMark_3367_;
v___y_3440_ = v_a_3354_;
v___y_3441_ = v_a_3355_;
goto v___jp_3437_;
}
else
{
lean_object* v___x_3450_; lean_object* v___x_3451_; lean_object* v___x_3452_; lean_object* v___x_3453_; lean_object* v___x_3454_; lean_object* v___x_3455_; lean_object* v___x_3456_; lean_object* v___x_3457_; lean_object* v___x_3458_; lean_object* v___x_3459_; 
v___x_3450_ = lean_obj_once(&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__15, &l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__15_once, _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__15);
lean_inc(v___x_3369_);
v___x_3451_ = l_Lean_mkFVar(v___x_3369_);
v___x_3452_ = l_Lean_MessageData_ofExpr(v___x_3451_);
v___x_3453_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3453_, 0, v___x_3450_);
lean_ctor_set(v___x_3453_, 1, v___x_3452_);
v___x_3454_ = lean_obj_once(&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__17, &l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__17_once, _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__17);
v___x_3455_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3455_, 0, v___x_3453_);
lean_ctor_set(v___x_3455_, 1, v___x_3454_);
v___x_3456_ = l_Lean_LocalDecl_type(v_fst_3362_);
v___x_3457_ = l_Lean_MessageData_ofExpr(v___x_3456_);
v___x_3458_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3458_, 0, v___x_3455_);
lean_ctor_set(v___x_3458_, 1, v___x_3457_);
v___x_3459_ = l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6(v___x_3447_, v___x_3458_, v_a_3353_, v_a_3354_, v_a_3355_);
if (lean_obj_tag(v___x_3459_) == 0)
{
lean_object* v_a_3460_; lean_object* v_snd_3461_; lean_object* v_tempMark_3462_; 
v_a_3460_ = lean_ctor_get(v___x_3459_, 0);
lean_inc(v_a_3460_);
lean_dec_ref(v___x_3459_);
v_snd_3461_ = lean_ctor_get(v_a_3460_, 1);
lean_inc(v_snd_3461_);
lean_dec(v_a_3460_);
v_tempMark_3462_ = lean_ctor_get(v_snd_3461_, 0);
lean_inc_ref(v_tempMark_3462_);
v___y_3438_ = v_snd_3461_;
v_tempMark_3439_ = v_tempMark_3462_;
v___y_3440_ = v_a_3354_;
v___y_3441_ = v_a_3355_;
goto v___jp_3437_;
}
else
{
lean_dec_ref(v___f_3376_);
lean_dec(v___x_3369_);
lean_dec(v_snd_3363_);
lean_dec(v_fst_3362_);
return v___x_3459_;
}
}
}
v___jp_3377_:
{
lean_object* v_tempMark_3381_; lean_object* v_doneMark_3382_; lean_object* v_newDecls_3383_; lean_object* v_newArgs_3384_; lean_object* v___x_3386_; uint8_t v_isShared_3387_; uint8_t v_isSharedCheck_3429_; 
v_tempMark_3381_ = lean_ctor_get(v___y_3379_, 0);
v_doneMark_3382_ = lean_ctor_get(v___y_3379_, 1);
v_newDecls_3383_ = lean_ctor_get(v___y_3379_, 2);
v_newArgs_3384_ = lean_ctor_get(v___y_3379_, 3);
v_isSharedCheck_3429_ = !lean_is_exclusive(v___y_3379_);
if (v_isSharedCheck_3429_ == 0)
{
v___x_3386_ = v___y_3379_;
v_isShared_3387_ = v_isSharedCheck_3429_;
goto v_resetjp_3385_;
}
else
{
lean_inc(v_newArgs_3384_);
lean_inc(v_newDecls_3383_);
lean_inc(v_doneMark_3382_);
lean_inc(v_tempMark_3381_);
lean_dec(v___y_3379_);
v___x_3386_ = lean_box(0);
v_isShared_3387_ = v_isSharedCheck_3429_;
goto v_resetjp_3385_;
}
v_resetjp_3385_:
{
lean_object* v___x_3388_; lean_object* v___x_3389_; lean_object* v___x_3390_; lean_object* v___x_3391_; lean_object* v___x_3393_; 
v___x_3388_ = lean_obj_once(&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__1, &l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__1_once, _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__1);
v___x_3389_ = lean_st_mk_ref(v___x_3388_);
v___x_3390_ = lean_box(0);
lean_inc(v___x_3369_);
v___x_3391_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2___redArg(v_tempMark_3381_, v___x_3369_, v___x_3390_);
if (v_isShared_3387_ == 0)
{
lean_ctor_set(v___x_3386_, 0, v___x_3391_);
v___x_3393_ = v___x_3386_;
goto v_reusejp_3392_;
}
else
{
lean_object* v_reuseFailAlloc_3428_; 
v_reuseFailAlloc_3428_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3428_, 0, v___x_3391_);
lean_ctor_set(v_reuseFailAlloc_3428_, 1, v_doneMark_3382_);
lean_ctor_set(v_reuseFailAlloc_3428_, 2, v_newDecls_3383_);
lean_ctor_set(v_reuseFailAlloc_3428_, 3, v_newArgs_3384_);
v___x_3393_ = v_reuseFailAlloc_3428_;
goto v_reusejp_3392_;
}
v_reusejp_3392_:
{
lean_object* v___x_3394_; lean_object* v___x_3395_; 
v___x_3394_ = l_Lean_LocalDecl_type(v_fst_3362_);
v___x_3395_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3(v___f_3376_, v___x_3394_, v___x_3389_, v___x_3393_, v___y_3380_, v___y_3378_);
if (lean_obj_tag(v___x_3395_) == 0)
{
lean_object* v_a_3396_; lean_object* v___x_3398_; uint8_t v_isShared_3399_; uint8_t v_isSharedCheck_3427_; 
v_a_3396_ = lean_ctor_get(v___x_3395_, 0);
v_isSharedCheck_3427_ = !lean_is_exclusive(v___x_3395_);
if (v_isSharedCheck_3427_ == 0)
{
v___x_3398_ = v___x_3395_;
v_isShared_3399_ = v_isSharedCheck_3427_;
goto v_resetjp_3397_;
}
else
{
lean_inc(v_a_3396_);
lean_dec(v___x_3395_);
v___x_3398_ = lean_box(0);
v_isShared_3399_ = v_isSharedCheck_3427_;
goto v_resetjp_3397_;
}
v_resetjp_3397_:
{
lean_object* v_snd_3400_; lean_object* v___x_3402_; uint8_t v_isShared_3403_; uint8_t v_isSharedCheck_3425_; 
v_snd_3400_ = lean_ctor_get(v_a_3396_, 1);
v_isSharedCheck_3425_ = !lean_is_exclusive(v_a_3396_);
if (v_isSharedCheck_3425_ == 0)
{
lean_object* v_unused_3426_; 
v_unused_3426_ = lean_ctor_get(v_a_3396_, 0);
lean_dec(v_unused_3426_);
v___x_3402_ = v_a_3396_;
v_isShared_3403_ = v_isSharedCheck_3425_;
goto v_resetjp_3401_;
}
else
{
lean_inc(v_snd_3400_);
lean_dec(v_a_3396_);
v___x_3402_ = lean_box(0);
v_isShared_3403_ = v_isSharedCheck_3425_;
goto v_resetjp_3401_;
}
v_resetjp_3401_:
{
lean_object* v___x_3404_; lean_object* v_tempMark_3405_; lean_object* v_doneMark_3406_; lean_object* v_newDecls_3407_; lean_object* v_newArgs_3408_; lean_object* v___x_3410_; uint8_t v_isShared_3411_; uint8_t v_isSharedCheck_3424_; 
v___x_3404_ = lean_st_ref_get(v___x_3389_);
lean_dec(v___x_3389_);
lean_dec(v___x_3404_);
v_tempMark_3405_ = lean_ctor_get(v_snd_3400_, 0);
v_doneMark_3406_ = lean_ctor_get(v_snd_3400_, 1);
v_newDecls_3407_ = lean_ctor_get(v_snd_3400_, 2);
v_newArgs_3408_ = lean_ctor_get(v_snd_3400_, 3);
v_isSharedCheck_3424_ = !lean_is_exclusive(v_snd_3400_);
if (v_isSharedCheck_3424_ == 0)
{
v___x_3410_ = v_snd_3400_;
v_isShared_3411_ = v_isSharedCheck_3424_;
goto v_resetjp_3409_;
}
else
{
lean_inc(v_newArgs_3408_);
lean_inc(v_newDecls_3407_);
lean_inc(v_doneMark_3406_);
lean_inc(v_tempMark_3405_);
lean_dec(v_snd_3400_);
v___x_3410_ = lean_box(0);
v_isShared_3411_ = v_isSharedCheck_3424_;
goto v_resetjp_3409_;
}
v_resetjp_3409_:
{
lean_object* v___x_3412_; lean_object* v___x_3413_; lean_object* v___x_3414_; lean_object* v___x_3416_; 
v___x_3412_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2___redArg(v_doneMark_3406_, v___x_3369_, v___x_3390_);
v___x_3413_ = lean_array_push(v_newDecls_3407_, v_fst_3362_);
v___x_3414_ = lean_array_push(v_newArgs_3408_, v_snd_3363_);
if (v_isShared_3411_ == 0)
{
lean_ctor_set(v___x_3410_, 3, v___x_3414_);
lean_ctor_set(v___x_3410_, 2, v___x_3413_);
lean_ctor_set(v___x_3410_, 1, v___x_3412_);
v___x_3416_ = v___x_3410_;
goto v_reusejp_3415_;
}
else
{
lean_object* v_reuseFailAlloc_3423_; 
v_reuseFailAlloc_3423_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3423_, 0, v_tempMark_3405_);
lean_ctor_set(v_reuseFailAlloc_3423_, 1, v___x_3412_);
lean_ctor_set(v_reuseFailAlloc_3423_, 2, v___x_3413_);
lean_ctor_set(v_reuseFailAlloc_3423_, 3, v___x_3414_);
v___x_3416_ = v_reuseFailAlloc_3423_;
goto v_reusejp_3415_;
}
v_reusejp_3415_:
{
lean_object* v___x_3418_; 
if (v_isShared_3403_ == 0)
{
lean_ctor_set(v___x_3402_, 1, v___x_3416_);
lean_ctor_set(v___x_3402_, 0, v___x_3390_);
v___x_3418_ = v___x_3402_;
goto v_reusejp_3417_;
}
else
{
lean_object* v_reuseFailAlloc_3422_; 
v_reuseFailAlloc_3422_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3422_, 0, v___x_3390_);
lean_ctor_set(v_reuseFailAlloc_3422_, 1, v___x_3416_);
v___x_3418_ = v_reuseFailAlloc_3422_;
goto v_reusejp_3417_;
}
v_reusejp_3417_:
{
lean_object* v___x_3420_; 
if (v_isShared_3399_ == 0)
{
lean_ctor_set(v___x_3398_, 0, v___x_3418_);
v___x_3420_ = v___x_3398_;
goto v_reusejp_3419_;
}
else
{
lean_object* v_reuseFailAlloc_3421_; 
v_reuseFailAlloc_3421_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3421_, 0, v___x_3418_);
v___x_3420_ = v_reuseFailAlloc_3421_;
goto v_reusejp_3419_;
}
v_reusejp_3419_:
{
return v___x_3420_;
}
}
}
}
}
}
}
else
{
lean_dec(v___x_3389_);
lean_dec(v___x_3369_);
lean_dec(v_snd_3363_);
lean_dec(v_fst_3362_);
return v___x_3395_;
}
}
}
}
v___jp_3430_:
{
uint8_t v___x_3434_; 
v___x_3434_ = l_Lean_LocalDecl_isLet(v_fst_3362_, v___x_3374_);
if (v___x_3434_ == 0)
{
v___y_3378_ = v___y_3433_;
v___y_3379_ = v___y_3431_;
v___y_3380_ = v___y_3432_;
goto v___jp_3377_;
}
else
{
if (v___x_3370_ == 0)
{
lean_object* v___x_3435_; lean_object* v___x_3436_; 
lean_dec_ref(v___f_3376_);
lean_dec(v___x_3369_);
lean_dec(v_snd_3363_);
lean_dec(v_fst_3362_);
v___x_3435_ = lean_obj_once(&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__5, &l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__5_once, _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__5);
v___x_3436_ = l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4(v___x_3435_, v___y_3431_, v___y_3432_, v___y_3433_);
return v___x_3436_;
}
else
{
v___y_3378_ = v___y_3433_;
v___y_3379_ = v___y_3431_;
v___y_3380_ = v___y_3432_;
goto v___jp_3377_;
}
}
}
v___jp_3437_:
{
uint8_t v___x_3442_; 
v___x_3442_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1___redArg(v_tempMark_3439_, v___x_3369_);
lean_dec_ref(v_tempMark_3439_);
if (v___x_3442_ == 0)
{
v___y_3431_ = v___y_3438_;
v___y_3432_ = v___y_3440_;
v___y_3433_ = v___y_3441_;
goto v___jp_3430_;
}
else
{
lean_object* v___x_3443_; lean_object* v___x_3444_; 
lean_dec_ref(v___y_3438_);
v___x_3443_ = lean_obj_once(&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__7, &l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__7_once, _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__7);
v___x_3444_ = l_Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5___redArg(v___x_3443_, v___y_3440_, v___y_3441_);
if (lean_obj_tag(v___x_3444_) == 0)
{
lean_object* v_a_3445_; lean_object* v_snd_3446_; 
v_a_3445_ = lean_ctor_get(v___x_3444_, 0);
lean_inc(v_a_3445_);
lean_dec_ref(v___x_3444_);
v_snd_3446_ = lean_ctor_get(v_a_3445_, 1);
lean_inc(v_snd_3446_);
lean_dec(v_a_3445_);
v___y_3431_ = v_snd_3446_;
v___y_3432_ = v___y_3440_;
v___y_3433_ = v___y_3441_;
goto v___jp_3430_;
}
else
{
lean_dec_ref(v___f_3376_);
lean_dec(v___x_3369_);
lean_dec(v_snd_3363_);
lean_dec(v_fst_3362_);
return v___x_3444_;
}
}
}
}
else
{
lean_object* v___x_3463_; lean_object* v___x_3465_; 
lean_dec(v___x_3369_);
lean_dec(v_snd_3363_);
lean_dec(v_fst_3362_);
lean_dec_ref(v_m_3351_);
v___x_3463_ = lean_box(0);
if (v_isShared_3366_ == 0)
{
lean_ctor_set(v___x_3365_, 1, v_a_3353_);
lean_ctor_set(v___x_3365_, 0, v___x_3463_);
v___x_3465_ = v___x_3365_;
goto v_reusejp_3464_;
}
else
{
lean_object* v_reuseFailAlloc_3469_; 
v_reuseFailAlloc_3469_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3469_, 0, v___x_3463_);
lean_ctor_set(v_reuseFailAlloc_3469_, 1, v_a_3353_);
v___x_3465_ = v_reuseFailAlloc_3469_;
goto v_reusejp_3464_;
}
v_reusejp_3464_:
{
lean_object* v___x_3467_; 
if (v_isShared_3361_ == 0)
{
lean_ctor_set_tag(v___x_3360_, 0);
lean_ctor_set(v___x_3360_, 0, v___x_3465_);
v___x_3467_ = v___x_3360_;
goto v_reusejp_3466_;
}
else
{
lean_object* v_reuseFailAlloc_3468_; 
v_reuseFailAlloc_3468_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3468_, 0, v___x_3465_);
v___x_3467_ = v_reuseFailAlloc_3468_;
goto v_reusejp_3466_;
}
v_reusejp_3466_:
{
return v___x_3467_;
}
}
}
}
}
}
else
{
lean_object* v___x_3472_; lean_object* v___x_3473_; lean_object* v___x_3474_; 
lean_dec(v___x_3357_);
lean_dec_ref(v_m_3351_);
v___x_3472_ = lean_box(0);
v___x_3473_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3473_, 0, v___x_3472_);
lean_ctor_set(v___x_3473_, 1, v_a_3353_);
v___x_3474_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3474_, 0, v___x_3473_);
return v___x_3474_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___lam__0(uint8_t v___x_3475_, lean_object* v_m_3476_, lean_object* v_e_3477_, lean_object* v___y_3478_, lean_object* v___y_3479_, lean_object* v___y_3480_){
_start:
{
lean_object* v___y_3483_; uint8_t v___x_3487_; 
v___x_3487_ = l_Lean_Expr_hasFVar(v_e_3477_);
if (v___x_3487_ == 0)
{
lean_object* v___x_3488_; lean_object* v___x_3489_; lean_object* v___x_3490_; 
lean_dec_ref(v_m_3476_);
v___x_3488_ = lean_box(v___x_3487_);
v___x_3489_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3489_, 0, v___x_3488_);
lean_ctor_set(v___x_3489_, 1, v___y_3478_);
v___x_3490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3490_, 0, v___x_3489_);
return v___x_3490_;
}
else
{
uint8_t v___x_3491_; 
v___x_3491_ = l_Lean_Expr_isFVar(v_e_3477_);
if (v___x_3491_ == 0)
{
lean_dec_ref(v_m_3476_);
v___y_3483_ = v___y_3478_;
goto v___jp_3482_;
}
else
{
lean_object* v___x_3492_; lean_object* v___x_3493_; 
v___x_3492_ = l_Lean_Expr_fvarId_x21(v_e_3477_);
v___x_3493_ = l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit(v_m_3476_, v___x_3492_, v___y_3478_, v___y_3479_, v___y_3480_);
lean_dec(v___x_3492_);
if (lean_obj_tag(v___x_3493_) == 0)
{
lean_object* v_a_3494_; lean_object* v_snd_3495_; 
v_a_3494_ = lean_ctor_get(v___x_3493_, 0);
lean_inc(v_a_3494_);
lean_dec_ref(v___x_3493_);
v_snd_3495_ = lean_ctor_get(v_a_3494_, 1);
lean_inc(v_snd_3495_);
lean_dec(v_a_3494_);
v___y_3483_ = v_snd_3495_;
goto v___jp_3482_;
}
else
{
lean_object* v_a_3496_; lean_object* v___x_3498_; uint8_t v_isShared_3499_; uint8_t v_isSharedCheck_3503_; 
v_a_3496_ = lean_ctor_get(v___x_3493_, 0);
v_isSharedCheck_3503_ = !lean_is_exclusive(v___x_3493_);
if (v_isSharedCheck_3503_ == 0)
{
v___x_3498_ = v___x_3493_;
v_isShared_3499_ = v_isSharedCheck_3503_;
goto v_resetjp_3497_;
}
else
{
lean_inc(v_a_3496_);
lean_dec(v___x_3493_);
v___x_3498_ = lean_box(0);
v_isShared_3499_ = v_isSharedCheck_3503_;
goto v_resetjp_3497_;
}
v_resetjp_3497_:
{
lean_object* v___x_3501_; 
if (v_isShared_3499_ == 0)
{
v___x_3501_ = v___x_3498_;
goto v_reusejp_3500_;
}
else
{
lean_object* v_reuseFailAlloc_3502_; 
v_reuseFailAlloc_3502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3502_, 0, v_a_3496_);
v___x_3501_ = v_reuseFailAlloc_3502_;
goto v_reusejp_3500_;
}
v_reusejp_3500_:
{
return v___x_3501_;
}
}
}
}
}
v___jp_3482_:
{
lean_object* v___x_3484_; lean_object* v___x_3485_; lean_object* v___x_3486_; 
v___x_3484_ = lean_box(v___x_3475_);
v___x_3485_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3485_, 0, v___x_3484_);
lean_ctor_set(v___x_3485_, 1, v___y_3483_);
v___x_3486_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3486_, 0, v___x_3485_);
return v___x_3486_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___boxed(lean_object* v_m_3504_, lean_object* v_fvarId_3505_, lean_object* v_a_3506_, lean_object* v_a_3507_, lean_object* v_a_3508_, lean_object* v_a_3509_){
_start:
{
lean_object* v_res_3510_; 
v_res_3510_ = l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit(v_m_3504_, v_fvarId_3505_, v_a_3506_, v_a_3507_, v_a_3508_);
lean_dec(v_a_3508_);
lean_dec_ref(v_a_3507_);
lean_dec(v_fvarId_3505_);
return v_res_3510_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0(lean_object* v_00_u03b2_3511_, lean_object* v_m_3512_, lean_object* v_a_3513_){
_start:
{
lean_object* v___x_3514_; 
v___x_3514_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0___redArg(v_m_3512_, v_a_3513_);
return v___x_3514_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0___boxed(lean_object* v_00_u03b2_3515_, lean_object* v_m_3516_, lean_object* v_a_3517_){
_start:
{
lean_object* v_res_3518_; 
v_res_3518_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0(v_00_u03b2_3515_, v_m_3516_, v_a_3517_);
lean_dec(v_a_3517_);
lean_dec_ref(v_m_3516_);
return v_res_3518_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1(lean_object* v_00_u03b2_3519_, lean_object* v_m_3520_, lean_object* v_a_3521_){
_start:
{
uint8_t v___x_3522_; 
v___x_3522_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1___redArg(v_m_3520_, v_a_3521_);
return v___x_3522_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1___boxed(lean_object* v_00_u03b2_3523_, lean_object* v_m_3524_, lean_object* v_a_3525_){
_start:
{
uint8_t v_res_3526_; lean_object* v_r_3527_; 
v_res_3526_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1(v_00_u03b2_3523_, v_m_3524_, v_a_3525_);
lean_dec(v_a_3525_);
lean_dec_ref(v_m_3524_);
v_r_3527_ = lean_box(v_res_3526_);
return v_r_3527_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2(lean_object* v_00_u03b2_3528_, lean_object* v_m_3529_, lean_object* v_a_3530_, lean_object* v_b_3531_){
_start:
{
lean_object* v___x_3532_; 
v___x_3532_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2___redArg(v_m_3529_, v_a_3530_, v_b_3531_);
return v___x_3532_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5(lean_object* v_00_u03b1_3533_, lean_object* v_msg_3534_, lean_object* v___y_3535_, lean_object* v___y_3536_, lean_object* v___y_3537_){
_start:
{
lean_object* v___x_3539_; 
v___x_3539_ = l_Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5___redArg(v_msg_3534_, v___y_3536_, v___y_3537_);
return v___x_3539_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5___boxed(lean_object* v_00_u03b1_3540_, lean_object* v_msg_3541_, lean_object* v___y_3542_, lean_object* v___y_3543_, lean_object* v___y_3544_, lean_object* v___y_3545_){
_start:
{
lean_object* v_res_3546_; 
v_res_3546_ = l_Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5(v_00_u03b1_3540_, v_msg_3541_, v___y_3542_, v___y_3543_, v___y_3544_);
lean_dec(v___y_3544_);
lean_dec_ref(v___y_3543_);
lean_dec_ref(v___y_3542_);
return v_res_3546_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0_spec__0(lean_object* v_00_u03b2_3547_, lean_object* v_a_3548_, lean_object* v_x_3549_){
_start:
{
lean_object* v___x_3550_; 
v___x_3550_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0_spec__0___redArg(v_a_3548_, v_x_3549_);
return v___x_3550_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3551_, lean_object* v_a_3552_, lean_object* v_x_3553_){
_start:
{
lean_object* v_res_3554_; 
v_res_3554_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0_spec__0(v_00_u03b2_3551_, v_a_3552_, v_x_3553_);
lean_dec(v_x_3553_);
lean_dec(v_a_3552_);
return v_res_3554_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1_spec__2(lean_object* v_00_u03b2_3555_, lean_object* v_a_3556_, lean_object* v_x_3557_){
_start:
{
uint8_t v___x_3558_; 
v___x_3558_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1_spec__2___redArg(v_a_3556_, v_x_3557_);
return v___x_3558_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1_spec__2___boxed(lean_object* v_00_u03b2_3559_, lean_object* v_a_3560_, lean_object* v_x_3561_){
_start:
{
uint8_t v_res_3562_; lean_object* v_r_3563_; 
v_res_3562_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1_spec__2(v_00_u03b2_3559_, v_a_3560_, v_x_3561_);
lean_dec(v_x_3561_);
lean_dec(v_a_3560_);
v_r_3563_ = lean_box(v_res_3562_);
return v_r_3563_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__4(lean_object* v_00_u03b2_3564_, lean_object* v_data_3565_){
_start:
{
lean_object* v___x_3566_; 
v___x_3566_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__4___redArg(v_data_3565_);
return v___x_3566_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__6(lean_object* v_00_u03b2_3567_, lean_object* v_m_3568_, lean_object* v_a_3569_){
_start:
{
lean_object* v___x_3570_; 
v___x_3570_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__6___redArg(v_m_3568_, v_a_3569_);
return v___x_3570_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__6___boxed(lean_object* v_00_u03b2_3571_, lean_object* v_m_3572_, lean_object* v_a_3573_){
_start:
{
lean_object* v_res_3574_; 
v_res_3574_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__6(v_00_u03b2_3571_, v_m_3572_, v_a_3573_);
lean_dec_ref(v_a_3573_);
lean_dec_ref(v_m_3572_);
return v_res_3574_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7(lean_object* v_00_u03b2_3575_, lean_object* v_m_3576_, lean_object* v_a_3577_, lean_object* v_b_3578_){
_start:
{
lean_object* v___x_3579_; 
v___x_3579_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7___redArg(v_m_3576_, v_a_3577_, v_b_3578_);
return v___x_3579_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__4_spec__6(lean_object* v_00_u03b2_3580_, lean_object* v_i_3581_, lean_object* v_source_3582_, lean_object* v_target_3583_){
_start:
{
lean_object* v___x_3584_; 
v___x_3584_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__4_spec__6___redArg(v_i_3581_, v_source_3582_, v_target_3583_);
return v___x_3584_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__6_spec__9(lean_object* v_00_u03b2_3585_, lean_object* v_a_3586_, lean_object* v_x_3587_){
_start:
{
lean_object* v___x_3588_; 
v___x_3588_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__6_spec__9___redArg(v_a_3586_, v_x_3587_);
return v___x_3588_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__6_spec__9___boxed(lean_object* v_00_u03b2_3589_, lean_object* v_a_3590_, lean_object* v_x_3591_){
_start:
{
lean_object* v_res_3592_; 
v_res_3592_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__6_spec__9(v_00_u03b2_3589_, v_a_3590_, v_x_3591_);
lean_dec(v_x_3591_);
lean_dec_ref(v_a_3590_);
return v_res_3592_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__11(lean_object* v_00_u03b2_3593_, lean_object* v_a_3594_, lean_object* v_x_3595_){
_start:
{
uint8_t v___x_3596_; 
v___x_3596_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__11___redArg(v_a_3594_, v_x_3595_);
return v___x_3596_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__11___boxed(lean_object* v_00_u03b2_3597_, lean_object* v_a_3598_, lean_object* v_x_3599_){
_start:
{
uint8_t v_res_3600_; lean_object* v_r_3601_; 
v_res_3600_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__11(v_00_u03b2_3597_, v_a_3598_, v_x_3599_);
lean_dec(v_x_3599_);
lean_dec_ref(v_a_3598_);
v_r_3601_ = lean_box(v_res_3600_);
return v_r_3601_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__12(lean_object* v_00_u03b2_3602_, lean_object* v_data_3603_){
_start:
{
lean_object* v___x_3604_; 
v___x_3604_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__12___redArg(v_data_3603_);
return v___x_3604_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__13(lean_object* v_00_u03b2_3605_, lean_object* v_a_3606_, lean_object* v_b_3607_, lean_object* v_x_3608_){
_start:
{
lean_object* v___x_3609_; 
v___x_3609_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__13___redArg(v_a_3606_, v_b_3607_, v_x_3608_);
return v___x_3609_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__4_spec__6_spec__11(lean_object* v_00_u03b2_3610_, lean_object* v_x_3611_, lean_object* v_x_3612_){
_start:
{
lean_object* v___x_3613_; 
v___x_3613_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__4_spec__6_spec__11___redArg(v_x_3611_, v_x_3612_);
return v___x_3613_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__12_spec__17(lean_object* v_00_u03b2_3614_, lean_object* v_i_3615_, lean_object* v_source_3616_, lean_object* v_target_3617_){
_start:
{
lean_object* v___x_3618_; 
v___x_3618_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__12_spec__17___redArg(v_i_3615_, v_source_3616_, v_target_3617_);
return v___x_3618_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__12_spec__17_spec__18(lean_object* v_00_u03b2_3619_, lean_object* v_x_3620_, lean_object* v_x_3621_){
_start:
{
lean_object* v___x_3622_; 
v___x_3622_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__12_spec__17_spec__18___redArg(v_x_3620_, v_x_3621_);
return v___x_3622_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__0(lean_object* v_msg_3624_, lean_object* v___y_3625_, lean_object* v___y_3626_){
_start:
{
lean_object* v___f_3628_; lean_object* v___x_8561__overap_3629_; lean_object* v___x_3630_; 
v___f_3628_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__0___closed__0));
v___x_8561__overap_3629_ = lean_panic_fn_borrowed(v___f_3628_, v_msg_3624_);
lean_inc(v___y_3626_);
lean_inc_ref(v___y_3625_);
v___x_3630_ = lean_apply_3(v___x_8561__overap_3629_, v___y_3625_, v___y_3626_, lean_box(0));
return v___x_3630_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__0___boxed(lean_object* v_msg_3631_, lean_object* v___y_3632_, lean_object* v___y_3633_, lean_object* v___y_3634_){
_start:
{
lean_object* v_res_3635_; 
v_res_3635_ = l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__0(v_msg_3631_, v___y_3632_, v___y_3633_);
lean_dec(v___y_3633_);
lean_dec_ref(v___y_3632_);
return v_res_3635_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___lam__0(lean_object* v_newDecls_3636_, lean_object* v_newArgs_3637_, lean_object* v_____r_3638_, lean_object* v___y_3639_, lean_object* v___y_3640_, lean_object* v___y_3641_){
_start:
{
lean_object* v___x_3643_; lean_object* v___x_3644_; lean_object* v___x_3645_; 
v___x_3643_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3643_, 0, v_newDecls_3636_);
lean_ctor_set(v___x_3643_, 1, v_newArgs_3637_);
v___x_3644_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3644_, 0, v___x_3643_);
lean_ctor_set(v___x_3644_, 1, v___y_3639_);
v___x_3645_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3645_, 0, v___x_3644_);
return v___x_3645_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___lam__0___boxed(lean_object* v_newDecls_3646_, lean_object* v_newArgs_3647_, lean_object* v_____r_3648_, lean_object* v___y_3649_, lean_object* v___y_3650_, lean_object* v___y_3651_, lean_object* v___y_3652_){
_start:
{
lean_object* v_res_3653_; 
v_res_3653_ = l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___lam__0(v_newDecls_3646_, v_newArgs_3647_, v_____r_3648_, v___y_3649_, v___y_3650_, v___y_3651_);
lean_dec(v___y_3651_);
lean_dec_ref(v___y_3650_);
return v_res_3653_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__6(lean_object* v_cls_3654_, lean_object* v_msg_3655_, lean_object* v___y_3656_, lean_object* v___y_3657_){
_start:
{
lean_object* v_ref_3659_; lean_object* v___x_3660_; lean_object* v_a_3661_; lean_object* v___x_3663_; uint8_t v_isShared_3664_; uint8_t v_isSharedCheck_3705_; 
v_ref_3659_ = lean_ctor_get(v___y_3656_, 5);
v___x_3660_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10(v_msg_3655_, v___y_3656_, v___y_3657_);
v_a_3661_ = lean_ctor_get(v___x_3660_, 0);
v_isSharedCheck_3705_ = !lean_is_exclusive(v___x_3660_);
if (v_isSharedCheck_3705_ == 0)
{
v___x_3663_ = v___x_3660_;
v_isShared_3664_ = v_isSharedCheck_3705_;
goto v_resetjp_3662_;
}
else
{
lean_inc(v_a_3661_);
lean_dec(v___x_3660_);
v___x_3663_ = lean_box(0);
v_isShared_3664_ = v_isSharedCheck_3705_;
goto v_resetjp_3662_;
}
v_resetjp_3662_:
{
lean_object* v___x_3665_; lean_object* v_traceState_3666_; lean_object* v_env_3667_; lean_object* v_nextMacroScope_3668_; lean_object* v_ngen_3669_; lean_object* v_auxDeclNGen_3670_; lean_object* v_cache_3671_; lean_object* v_messages_3672_; lean_object* v_infoState_3673_; lean_object* v_snapshotTasks_3674_; lean_object* v___x_3676_; uint8_t v_isShared_3677_; uint8_t v_isSharedCheck_3704_; 
v___x_3665_ = lean_st_ref_take(v___y_3657_);
v_traceState_3666_ = lean_ctor_get(v___x_3665_, 4);
v_env_3667_ = lean_ctor_get(v___x_3665_, 0);
v_nextMacroScope_3668_ = lean_ctor_get(v___x_3665_, 1);
v_ngen_3669_ = lean_ctor_get(v___x_3665_, 2);
v_auxDeclNGen_3670_ = lean_ctor_get(v___x_3665_, 3);
v_cache_3671_ = lean_ctor_get(v___x_3665_, 5);
v_messages_3672_ = lean_ctor_get(v___x_3665_, 6);
v_infoState_3673_ = lean_ctor_get(v___x_3665_, 7);
v_snapshotTasks_3674_ = lean_ctor_get(v___x_3665_, 8);
v_isSharedCheck_3704_ = !lean_is_exclusive(v___x_3665_);
if (v_isSharedCheck_3704_ == 0)
{
v___x_3676_ = v___x_3665_;
v_isShared_3677_ = v_isSharedCheck_3704_;
goto v_resetjp_3675_;
}
else
{
lean_inc(v_snapshotTasks_3674_);
lean_inc(v_infoState_3673_);
lean_inc(v_messages_3672_);
lean_inc(v_cache_3671_);
lean_inc(v_traceState_3666_);
lean_inc(v_auxDeclNGen_3670_);
lean_inc(v_ngen_3669_);
lean_inc(v_nextMacroScope_3668_);
lean_inc(v_env_3667_);
lean_dec(v___x_3665_);
v___x_3676_ = lean_box(0);
v_isShared_3677_ = v_isSharedCheck_3704_;
goto v_resetjp_3675_;
}
v_resetjp_3675_:
{
uint64_t v_tid_3678_; lean_object* v_traces_3679_; lean_object* v___x_3681_; uint8_t v_isShared_3682_; uint8_t v_isSharedCheck_3703_; 
v_tid_3678_ = lean_ctor_get_uint64(v_traceState_3666_, sizeof(void*)*1);
v_traces_3679_ = lean_ctor_get(v_traceState_3666_, 0);
v_isSharedCheck_3703_ = !lean_is_exclusive(v_traceState_3666_);
if (v_isSharedCheck_3703_ == 0)
{
v___x_3681_ = v_traceState_3666_;
v_isShared_3682_ = v_isSharedCheck_3703_;
goto v_resetjp_3680_;
}
else
{
lean_inc(v_traces_3679_);
lean_dec(v_traceState_3666_);
v___x_3681_ = lean_box(0);
v_isShared_3682_ = v_isSharedCheck_3703_;
goto v_resetjp_3680_;
}
v_resetjp_3680_:
{
lean_object* v___x_3683_; double v___x_3684_; uint8_t v___x_3685_; lean_object* v___x_3686_; lean_object* v___x_3687_; lean_object* v___x_3688_; lean_object* v___x_3689_; lean_object* v___x_3690_; lean_object* v___x_3691_; lean_object* v___x_3693_; 
v___x_3683_ = lean_box(0);
v___x_3684_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6___closed__0);
v___x_3685_ = 0;
v___x_3686_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6___closed__1));
v___x_3687_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3687_, 0, v_cls_3654_);
lean_ctor_set(v___x_3687_, 1, v___x_3683_);
lean_ctor_set(v___x_3687_, 2, v___x_3686_);
lean_ctor_set_float(v___x_3687_, sizeof(void*)*3, v___x_3684_);
lean_ctor_set_float(v___x_3687_, sizeof(void*)*3 + 8, v___x_3684_);
lean_ctor_set_uint8(v___x_3687_, sizeof(void*)*3 + 16, v___x_3685_);
v___x_3688_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6___closed__2));
v___x_3689_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3689_, 0, v___x_3687_);
lean_ctor_set(v___x_3689_, 1, v_a_3661_);
lean_ctor_set(v___x_3689_, 2, v___x_3688_);
lean_inc(v_ref_3659_);
v___x_3690_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3690_, 0, v_ref_3659_);
lean_ctor_set(v___x_3690_, 1, v___x_3689_);
v___x_3691_ = l_Lean_PersistentArray_push___redArg(v_traces_3679_, v___x_3690_);
if (v_isShared_3682_ == 0)
{
lean_ctor_set(v___x_3681_, 0, v___x_3691_);
v___x_3693_ = v___x_3681_;
goto v_reusejp_3692_;
}
else
{
lean_object* v_reuseFailAlloc_3702_; 
v_reuseFailAlloc_3702_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3702_, 0, v___x_3691_);
lean_ctor_set_uint64(v_reuseFailAlloc_3702_, sizeof(void*)*1, v_tid_3678_);
v___x_3693_ = v_reuseFailAlloc_3702_;
goto v_reusejp_3692_;
}
v_reusejp_3692_:
{
lean_object* v___x_3695_; 
if (v_isShared_3677_ == 0)
{
lean_ctor_set(v___x_3676_, 4, v___x_3693_);
v___x_3695_ = v___x_3676_;
goto v_reusejp_3694_;
}
else
{
lean_object* v_reuseFailAlloc_3701_; 
v_reuseFailAlloc_3701_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3701_, 0, v_env_3667_);
lean_ctor_set(v_reuseFailAlloc_3701_, 1, v_nextMacroScope_3668_);
lean_ctor_set(v_reuseFailAlloc_3701_, 2, v_ngen_3669_);
lean_ctor_set(v_reuseFailAlloc_3701_, 3, v_auxDeclNGen_3670_);
lean_ctor_set(v_reuseFailAlloc_3701_, 4, v___x_3693_);
lean_ctor_set(v_reuseFailAlloc_3701_, 5, v_cache_3671_);
lean_ctor_set(v_reuseFailAlloc_3701_, 6, v_messages_3672_);
lean_ctor_set(v_reuseFailAlloc_3701_, 7, v_infoState_3673_);
lean_ctor_set(v_reuseFailAlloc_3701_, 8, v_snapshotTasks_3674_);
v___x_3695_ = v_reuseFailAlloc_3701_;
goto v_reusejp_3694_;
}
v_reusejp_3694_:
{
lean_object* v___x_3696_; lean_object* v___x_3697_; lean_object* v___x_3699_; 
v___x_3696_ = lean_st_ref_set(v___y_3657_, v___x_3695_);
v___x_3697_ = lean_box(0);
if (v_isShared_3664_ == 0)
{
lean_ctor_set(v___x_3663_, 0, v___x_3697_);
v___x_3699_ = v___x_3663_;
goto v_reusejp_3698_;
}
else
{
lean_object* v_reuseFailAlloc_3700_; 
v_reuseFailAlloc_3700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3700_, 0, v___x_3697_);
v___x_3699_ = v_reuseFailAlloc_3700_;
goto v_reusejp_3698_;
}
v_reusejp_3698_:
{
return v___x_3699_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__6___boxed(lean_object* v_cls_3706_, lean_object* v_msg_3707_, lean_object* v___y_3708_, lean_object* v___y_3709_, lean_object* v___y_3710_){
_start:
{
lean_object* v_res_3711_; 
v_res_3711_ = l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__6(v_cls_3706_, v_msg_3707_, v___y_3708_, v___y_3709_);
lean_dec(v___y_3709_);
lean_dec_ref(v___y_3708_);
return v_res_3711_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__4(size_t v_sz_3712_, size_t v_i_3713_, lean_object* v_bs_3714_){
_start:
{
uint8_t v___x_3715_; 
v___x_3715_ = lean_usize_dec_lt(v_i_3713_, v_sz_3712_);
if (v___x_3715_ == 0)
{
return v_bs_3714_;
}
else
{
lean_object* v_v_3716_; lean_object* v___x_3717_; lean_object* v_bs_x27_3718_; lean_object* v___x_3719_; lean_object* v___x_3720_; size_t v___x_3721_; size_t v___x_3722_; lean_object* v___x_3723_; 
v_v_3716_ = lean_array_uget(v_bs_3714_, v_i_3713_);
v___x_3717_ = lean_unsigned_to_nat(0u);
v_bs_x27_3718_ = lean_array_uset(v_bs_3714_, v_i_3713_, v___x_3717_);
v___x_3719_ = l_Lean_LocalDecl_fvarId(v_v_3716_);
lean_dec(v_v_3716_);
v___x_3720_ = l_Lean_mkFVar(v___x_3719_);
v___x_3721_ = ((size_t)1ULL);
v___x_3722_ = lean_usize_add(v_i_3713_, v___x_3721_);
v___x_3723_ = lean_array_uset(v_bs_x27_3718_, v_i_3713_, v___x_3720_);
v_i_3713_ = v___x_3722_;
v_bs_3714_ = v___x_3723_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__4___boxed(lean_object* v_sz_3725_, lean_object* v_i_3726_, lean_object* v_bs_3727_){
_start:
{
size_t v_sz_boxed_3728_; size_t v_i_boxed_3729_; lean_object* v_res_3730_; 
v_sz_boxed_3728_ = lean_unbox_usize(v_sz_3725_);
lean_dec(v_sz_3725_);
v_i_boxed_3729_ = lean_unbox_usize(v_i_3726_);
lean_dec(v_i_3726_);
v_res_3730_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__4(v_sz_boxed_3728_, v_i_boxed_3729_, v_bs_3727_);
return v_res_3730_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__3(lean_object* v___x_3731_, lean_object* v_as_3732_, size_t v_sz_3733_, size_t v_i_3734_, lean_object* v_b_3735_, lean_object* v___y_3736_, lean_object* v___y_3737_, lean_object* v___y_3738_){
_start:
{
uint8_t v___x_3740_; 
v___x_3740_ = lean_usize_dec_lt(v_i_3734_, v_sz_3733_);
if (v___x_3740_ == 0)
{
lean_object* v___x_3741_; lean_object* v___x_3742_; 
lean_dec_ref(v___x_3731_);
v___x_3741_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3741_, 0, v_b_3735_);
lean_ctor_set(v___x_3741_, 1, v___y_3736_);
v___x_3742_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3742_, 0, v___x_3741_);
return v___x_3742_;
}
else
{
lean_object* v_a_3743_; lean_object* v___x_3744_; lean_object* v___x_3745_; 
v_a_3743_ = lean_array_uget_borrowed(v_as_3732_, v_i_3734_);
v___x_3744_ = l_Lean_LocalDecl_fvarId(v_a_3743_);
lean_inc_ref(v___x_3731_);
v___x_3745_ = l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit(v___x_3731_, v___x_3744_, v___y_3736_, v___y_3737_, v___y_3738_);
lean_dec(v___x_3744_);
if (lean_obj_tag(v___x_3745_) == 0)
{
lean_object* v_a_3746_; lean_object* v_snd_3747_; lean_object* v___x_3748_; size_t v___x_3749_; size_t v___x_3750_; 
v_a_3746_ = lean_ctor_get(v___x_3745_, 0);
lean_inc(v_a_3746_);
lean_dec_ref(v___x_3745_);
v_snd_3747_ = lean_ctor_get(v_a_3746_, 1);
lean_inc(v_snd_3747_);
lean_dec(v_a_3746_);
v___x_3748_ = lean_box(0);
v___x_3749_ = ((size_t)1ULL);
v___x_3750_ = lean_usize_add(v_i_3734_, v___x_3749_);
v_i_3734_ = v___x_3750_;
v_b_3735_ = v___x_3748_;
v___y_3736_ = v_snd_3747_;
goto _start;
}
else
{
lean_dec_ref(v___x_3731_);
return v___x_3745_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__3___boxed(lean_object* v___x_3752_, lean_object* v_as_3753_, lean_object* v_sz_3754_, lean_object* v_i_3755_, lean_object* v_b_3756_, lean_object* v___y_3757_, lean_object* v___y_3758_, lean_object* v___y_3759_, lean_object* v___y_3760_){
_start:
{
size_t v_sz_boxed_3761_; size_t v_i_boxed_3762_; lean_object* v_res_3763_; 
v_sz_boxed_3761_ = lean_unbox_usize(v_sz_3754_);
lean_dec(v_sz_3754_);
v_i_boxed_3762_ = lean_unbox_usize(v_i_3755_);
lean_dec(v_i_3755_);
v_res_3763_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__3(v___x_3752_, v_as_3753_, v_sz_boxed_3761_, v_i_boxed_3762_, v_b_3756_, v___y_3757_, v___y_3758_, v___y_3759_);
lean_dec(v___y_3759_);
lean_dec_ref(v___y_3758_);
lean_dec_ref(v_as_3753_);
return v_res_3763_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__5(lean_object* v_a_3764_, lean_object* v_a_3765_){
_start:
{
if (lean_obj_tag(v_a_3764_) == 0)
{
lean_object* v___x_3766_; 
v___x_3766_ = l_List_reverse___redArg(v_a_3765_);
return v___x_3766_;
}
else
{
lean_object* v_head_3767_; lean_object* v_tail_3768_; lean_object* v___x_3770_; uint8_t v_isShared_3771_; uint8_t v_isSharedCheck_3777_; 
v_head_3767_ = lean_ctor_get(v_a_3764_, 0);
v_tail_3768_ = lean_ctor_get(v_a_3764_, 1);
v_isSharedCheck_3777_ = !lean_is_exclusive(v_a_3764_);
if (v_isSharedCheck_3777_ == 0)
{
v___x_3770_ = v_a_3764_;
v_isShared_3771_ = v_isSharedCheck_3777_;
goto v_resetjp_3769_;
}
else
{
lean_inc(v_tail_3768_);
lean_inc(v_head_3767_);
lean_dec(v_a_3764_);
v___x_3770_ = lean_box(0);
v_isShared_3771_ = v_isSharedCheck_3777_;
goto v_resetjp_3769_;
}
v_resetjp_3769_:
{
lean_object* v___x_3772_; lean_object* v___x_3774_; 
v___x_3772_ = l_Lean_MessageData_ofExpr(v_head_3767_);
if (v_isShared_3771_ == 0)
{
lean_ctor_set(v___x_3770_, 1, v_a_3765_);
lean_ctor_set(v___x_3770_, 0, v___x_3772_);
v___x_3774_ = v___x_3770_;
goto v_reusejp_3773_;
}
else
{
lean_object* v_reuseFailAlloc_3776_; 
v_reuseFailAlloc_3776_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3776_, 0, v___x_3772_);
lean_ctor_set(v_reuseFailAlloc_3776_, 1, v_a_3765_);
v___x_3774_ = v_reuseFailAlloc_3776_;
goto v_reusejp_3773_;
}
v_reusejp_3773_:
{
v_a_3764_ = v_tail_3768_;
v_a_3765_ = v___x_3774_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__1_spec__1___redArg(lean_object* v_a_3778_, lean_object* v_b_3779_, lean_object* v_x_3780_){
_start:
{
if (lean_obj_tag(v_x_3780_) == 0)
{
lean_dec(v_b_3779_);
lean_dec(v_a_3778_);
return v_x_3780_;
}
else
{
lean_object* v_key_3781_; lean_object* v_value_3782_; lean_object* v_tail_3783_; lean_object* v___x_3785_; uint8_t v_isShared_3786_; uint8_t v_isSharedCheck_3795_; 
v_key_3781_ = lean_ctor_get(v_x_3780_, 0);
v_value_3782_ = lean_ctor_get(v_x_3780_, 1);
v_tail_3783_ = lean_ctor_get(v_x_3780_, 2);
v_isSharedCheck_3795_ = !lean_is_exclusive(v_x_3780_);
if (v_isSharedCheck_3795_ == 0)
{
v___x_3785_ = v_x_3780_;
v_isShared_3786_ = v_isSharedCheck_3795_;
goto v_resetjp_3784_;
}
else
{
lean_inc(v_tail_3783_);
lean_inc(v_value_3782_);
lean_inc(v_key_3781_);
lean_dec(v_x_3780_);
v___x_3785_ = lean_box(0);
v_isShared_3786_ = v_isSharedCheck_3795_;
goto v_resetjp_3784_;
}
v_resetjp_3784_:
{
uint8_t v___x_3787_; 
v___x_3787_ = l_Lean_instBEqFVarId_beq(v_key_3781_, v_a_3778_);
if (v___x_3787_ == 0)
{
lean_object* v___x_3788_; lean_object* v___x_3790_; 
v___x_3788_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__1_spec__1___redArg(v_a_3778_, v_b_3779_, v_tail_3783_);
if (v_isShared_3786_ == 0)
{
lean_ctor_set(v___x_3785_, 2, v___x_3788_);
v___x_3790_ = v___x_3785_;
goto v_reusejp_3789_;
}
else
{
lean_object* v_reuseFailAlloc_3791_; 
v_reuseFailAlloc_3791_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3791_, 0, v_key_3781_);
lean_ctor_set(v_reuseFailAlloc_3791_, 1, v_value_3782_);
lean_ctor_set(v_reuseFailAlloc_3791_, 2, v___x_3788_);
v___x_3790_ = v_reuseFailAlloc_3791_;
goto v_reusejp_3789_;
}
v_reusejp_3789_:
{
return v___x_3790_;
}
}
else
{
lean_object* v___x_3793_; 
lean_dec(v_value_3782_);
lean_dec(v_key_3781_);
if (v_isShared_3786_ == 0)
{
lean_ctor_set(v___x_3785_, 1, v_b_3779_);
lean_ctor_set(v___x_3785_, 0, v_a_3778_);
v___x_3793_ = v___x_3785_;
goto v_reusejp_3792_;
}
else
{
lean_object* v_reuseFailAlloc_3794_; 
v_reuseFailAlloc_3794_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3794_, 0, v_a_3778_);
lean_ctor_set(v_reuseFailAlloc_3794_, 1, v_b_3779_);
lean_ctor_set(v_reuseFailAlloc_3794_, 2, v_tail_3783_);
v___x_3793_ = v_reuseFailAlloc_3794_;
goto v_reusejp_3792_;
}
v_reusejp_3792_:
{
return v___x_3793_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__1___redArg(lean_object* v_m_3796_, lean_object* v_a_3797_, lean_object* v_b_3798_){
_start:
{
lean_object* v_size_3799_; lean_object* v_buckets_3800_; lean_object* v___x_3802_; uint8_t v_isShared_3803_; uint8_t v_isSharedCheck_3843_; 
v_size_3799_ = lean_ctor_get(v_m_3796_, 0);
v_buckets_3800_ = lean_ctor_get(v_m_3796_, 1);
v_isSharedCheck_3843_ = !lean_is_exclusive(v_m_3796_);
if (v_isSharedCheck_3843_ == 0)
{
v___x_3802_ = v_m_3796_;
v_isShared_3803_ = v_isSharedCheck_3843_;
goto v_resetjp_3801_;
}
else
{
lean_inc(v_buckets_3800_);
lean_inc(v_size_3799_);
lean_dec(v_m_3796_);
v___x_3802_ = lean_box(0);
v_isShared_3803_ = v_isSharedCheck_3843_;
goto v_resetjp_3801_;
}
v_resetjp_3801_:
{
lean_object* v___x_3804_; uint64_t v___x_3805_; uint64_t v___x_3806_; uint64_t v___x_3807_; uint64_t v_fold_3808_; uint64_t v___x_3809_; uint64_t v___x_3810_; uint64_t v___x_3811_; size_t v___x_3812_; size_t v___x_3813_; size_t v___x_3814_; size_t v___x_3815_; size_t v___x_3816_; lean_object* v_bkt_3817_; uint8_t v___x_3818_; 
v___x_3804_ = lean_array_get_size(v_buckets_3800_);
v___x_3805_ = l_Lean_instHashableFVarId_hash(v_a_3797_);
v___x_3806_ = 32ULL;
v___x_3807_ = lean_uint64_shift_right(v___x_3805_, v___x_3806_);
v_fold_3808_ = lean_uint64_xor(v___x_3805_, v___x_3807_);
v___x_3809_ = 16ULL;
v___x_3810_ = lean_uint64_shift_right(v_fold_3808_, v___x_3809_);
v___x_3811_ = lean_uint64_xor(v_fold_3808_, v___x_3810_);
v___x_3812_ = lean_uint64_to_usize(v___x_3811_);
v___x_3813_ = lean_usize_of_nat(v___x_3804_);
v___x_3814_ = ((size_t)1ULL);
v___x_3815_ = lean_usize_sub(v___x_3813_, v___x_3814_);
v___x_3816_ = lean_usize_land(v___x_3812_, v___x_3815_);
v_bkt_3817_ = lean_array_uget_borrowed(v_buckets_3800_, v___x_3816_);
v___x_3818_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1_spec__2___redArg(v_a_3797_, v_bkt_3817_);
if (v___x_3818_ == 0)
{
lean_object* v___x_3819_; lean_object* v_size_x27_3820_; lean_object* v___x_3821_; lean_object* v_buckets_x27_3822_; lean_object* v___x_3823_; lean_object* v___x_3824_; lean_object* v___x_3825_; lean_object* v___x_3826_; lean_object* v___x_3827_; uint8_t v___x_3828_; 
v___x_3819_ = lean_unsigned_to_nat(1u);
v_size_x27_3820_ = lean_nat_add(v_size_3799_, v___x_3819_);
lean_dec(v_size_3799_);
lean_inc(v_bkt_3817_);
v___x_3821_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3821_, 0, v_a_3797_);
lean_ctor_set(v___x_3821_, 1, v_b_3798_);
lean_ctor_set(v___x_3821_, 2, v_bkt_3817_);
v_buckets_x27_3822_ = lean_array_uset(v_buckets_3800_, v___x_3816_, v___x_3821_);
v___x_3823_ = lean_unsigned_to_nat(4u);
v___x_3824_ = lean_nat_mul(v_size_x27_3820_, v___x_3823_);
v___x_3825_ = lean_unsigned_to_nat(3u);
v___x_3826_ = lean_nat_div(v___x_3824_, v___x_3825_);
lean_dec(v___x_3824_);
v___x_3827_ = lean_array_get_size(v_buckets_x27_3822_);
v___x_3828_ = lean_nat_dec_le(v___x_3826_, v___x_3827_);
lean_dec(v___x_3826_);
if (v___x_3828_ == 0)
{
lean_object* v_val_3829_; lean_object* v___x_3831_; 
v_val_3829_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__4___redArg(v_buckets_x27_3822_);
if (v_isShared_3803_ == 0)
{
lean_ctor_set(v___x_3802_, 1, v_val_3829_);
lean_ctor_set(v___x_3802_, 0, v_size_x27_3820_);
v___x_3831_ = v___x_3802_;
goto v_reusejp_3830_;
}
else
{
lean_object* v_reuseFailAlloc_3832_; 
v_reuseFailAlloc_3832_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3832_, 0, v_size_x27_3820_);
lean_ctor_set(v_reuseFailAlloc_3832_, 1, v_val_3829_);
v___x_3831_ = v_reuseFailAlloc_3832_;
goto v_reusejp_3830_;
}
v_reusejp_3830_:
{
return v___x_3831_;
}
}
else
{
lean_object* v___x_3834_; 
if (v_isShared_3803_ == 0)
{
lean_ctor_set(v___x_3802_, 1, v_buckets_x27_3822_);
lean_ctor_set(v___x_3802_, 0, v_size_x27_3820_);
v___x_3834_ = v___x_3802_;
goto v_reusejp_3833_;
}
else
{
lean_object* v_reuseFailAlloc_3835_; 
v_reuseFailAlloc_3835_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3835_, 0, v_size_x27_3820_);
lean_ctor_set(v_reuseFailAlloc_3835_, 1, v_buckets_x27_3822_);
v___x_3834_ = v_reuseFailAlloc_3835_;
goto v_reusejp_3833_;
}
v_reusejp_3833_:
{
return v___x_3834_;
}
}
}
else
{
lean_object* v___x_3836_; lean_object* v_buckets_x27_3837_; lean_object* v___x_3838_; lean_object* v___x_3839_; lean_object* v___x_3841_; 
lean_inc(v_bkt_3817_);
v___x_3836_ = lean_box(0);
v_buckets_x27_3837_ = lean_array_uset(v_buckets_3800_, v___x_3816_, v___x_3836_);
v___x_3838_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__1_spec__1___redArg(v_a_3797_, v_b_3798_, v_bkt_3817_);
v___x_3839_ = lean_array_uset(v_buckets_x27_3837_, v___x_3816_, v___x_3838_);
if (v_isShared_3803_ == 0)
{
lean_ctor_set(v___x_3802_, 1, v___x_3839_);
v___x_3841_ = v___x_3802_;
goto v_reusejp_3840_;
}
else
{
lean_object* v_reuseFailAlloc_3842_; 
v_reuseFailAlloc_3842_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3842_, 0, v_size_3799_);
lean_ctor_set(v_reuseFailAlloc_3842_, 1, v___x_3839_);
v___x_3841_ = v_reuseFailAlloc_3842_;
goto v_reusejp_3840_;
}
v_reusejp_3840_:
{
return v___x_3841_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__2___redArg(lean_object* v_as_3844_, size_t v_sz_3845_, size_t v_i_3846_, lean_object* v_b_3847_){
_start:
{
uint8_t v___x_3849_; 
v___x_3849_ = lean_usize_dec_lt(v_i_3846_, v_sz_3845_);
if (v___x_3849_ == 0)
{
lean_object* v___x_3850_; 
v___x_3850_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3850_, 0, v_b_3847_);
return v___x_3850_;
}
else
{
lean_object* v_snd_3851_; lean_object* v_fst_3852_; lean_object* v___x_3854_; uint8_t v_isShared_3855_; uint8_t v_isSharedCheck_3887_; 
v_snd_3851_ = lean_ctor_get(v_b_3847_, 1);
v_fst_3852_ = lean_ctor_get(v_b_3847_, 0);
v_isSharedCheck_3887_ = !lean_is_exclusive(v_b_3847_);
if (v_isSharedCheck_3887_ == 0)
{
v___x_3854_ = v_b_3847_;
v_isShared_3855_ = v_isSharedCheck_3887_;
goto v_resetjp_3853_;
}
else
{
lean_inc(v_snd_3851_);
lean_inc(v_fst_3852_);
lean_dec(v_b_3847_);
v___x_3854_ = lean_box(0);
v_isShared_3855_ = v_isSharedCheck_3887_;
goto v_resetjp_3853_;
}
v_resetjp_3853_:
{
lean_object* v_array_3856_; lean_object* v_start_3857_; lean_object* v_stop_3858_; uint8_t v___x_3859_; 
v_array_3856_ = lean_ctor_get(v_snd_3851_, 0);
v_start_3857_ = lean_ctor_get(v_snd_3851_, 1);
v_stop_3858_ = lean_ctor_get(v_snd_3851_, 2);
v___x_3859_ = lean_nat_dec_lt(v_start_3857_, v_stop_3858_);
if (v___x_3859_ == 0)
{
lean_object* v___x_3861_; 
if (v_isShared_3855_ == 0)
{
v___x_3861_ = v___x_3854_;
goto v_reusejp_3860_;
}
else
{
lean_object* v_reuseFailAlloc_3863_; 
v_reuseFailAlloc_3863_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3863_, 0, v_fst_3852_);
lean_ctor_set(v_reuseFailAlloc_3863_, 1, v_snd_3851_);
v___x_3861_ = v_reuseFailAlloc_3863_;
goto v_reusejp_3860_;
}
v_reusejp_3860_:
{
lean_object* v___x_3862_; 
v___x_3862_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3862_, 0, v___x_3861_);
return v___x_3862_;
}
}
else
{
lean_object* v___x_3865_; uint8_t v_isShared_3866_; uint8_t v_isSharedCheck_3883_; 
lean_inc(v_stop_3858_);
lean_inc(v_start_3857_);
lean_inc_ref(v_array_3856_);
v_isSharedCheck_3883_ = !lean_is_exclusive(v_snd_3851_);
if (v_isSharedCheck_3883_ == 0)
{
lean_object* v_unused_3884_; lean_object* v_unused_3885_; lean_object* v_unused_3886_; 
v_unused_3884_ = lean_ctor_get(v_snd_3851_, 2);
lean_dec(v_unused_3884_);
v_unused_3885_ = lean_ctor_get(v_snd_3851_, 1);
lean_dec(v_unused_3885_);
v_unused_3886_ = lean_ctor_get(v_snd_3851_, 0);
lean_dec(v_unused_3886_);
v___x_3865_ = v_snd_3851_;
v_isShared_3866_ = v_isSharedCheck_3883_;
goto v_resetjp_3864_;
}
else
{
lean_dec(v_snd_3851_);
v___x_3865_ = lean_box(0);
v_isShared_3866_ = v_isSharedCheck_3883_;
goto v_resetjp_3864_;
}
v_resetjp_3864_:
{
lean_object* v_a_3867_; lean_object* v___x_3868_; lean_object* v___x_3869_; lean_object* v___x_3870_; lean_object* v___x_3872_; 
v_a_3867_ = lean_array_uget_borrowed(v_as_3844_, v_i_3846_);
v___x_3868_ = lean_array_fget(v_array_3856_, v_start_3857_);
v___x_3869_ = lean_unsigned_to_nat(1u);
v___x_3870_ = lean_nat_add(v_start_3857_, v___x_3869_);
lean_dec(v_start_3857_);
if (v_isShared_3866_ == 0)
{
lean_ctor_set(v___x_3865_, 1, v___x_3870_);
v___x_3872_ = v___x_3865_;
goto v_reusejp_3871_;
}
else
{
lean_object* v_reuseFailAlloc_3882_; 
v_reuseFailAlloc_3882_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3882_, 0, v_array_3856_);
lean_ctor_set(v_reuseFailAlloc_3882_, 1, v___x_3870_);
lean_ctor_set(v_reuseFailAlloc_3882_, 2, v_stop_3858_);
v___x_3872_ = v_reuseFailAlloc_3882_;
goto v_reusejp_3871_;
}
v_reusejp_3871_:
{
lean_object* v___x_3873_; lean_object* v___x_3875_; 
v___x_3873_ = l_Lean_LocalDecl_fvarId(v_a_3867_);
lean_inc(v_a_3867_);
if (v_isShared_3855_ == 0)
{
lean_ctor_set(v___x_3854_, 1, v___x_3868_);
lean_ctor_set(v___x_3854_, 0, v_a_3867_);
v___x_3875_ = v___x_3854_;
goto v_reusejp_3874_;
}
else
{
lean_object* v_reuseFailAlloc_3881_; 
v_reuseFailAlloc_3881_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3881_, 0, v_a_3867_);
lean_ctor_set(v_reuseFailAlloc_3881_, 1, v___x_3868_);
v___x_3875_ = v_reuseFailAlloc_3881_;
goto v_reusejp_3874_;
}
v_reusejp_3874_:
{
lean_object* v___x_3876_; lean_object* v___x_3877_; size_t v___x_3878_; size_t v___x_3879_; 
v___x_3876_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__1___redArg(v_fst_3852_, v___x_3873_, v___x_3875_);
v___x_3877_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3877_, 0, v___x_3876_);
lean_ctor_set(v___x_3877_, 1, v___x_3872_);
v___x_3878_ = ((size_t)1ULL);
v___x_3879_ = lean_usize_add(v_i_3846_, v___x_3878_);
v_i_3846_ = v___x_3879_;
v_b_3847_ = v___x_3877_;
goto _start;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__2___redArg___boxed(lean_object* v_as_3888_, lean_object* v_sz_3889_, lean_object* v_i_3890_, lean_object* v_b_3891_, lean_object* v___y_3892_){
_start:
{
size_t v_sz_boxed_3893_; size_t v_i_boxed_3894_; lean_object* v_res_3895_; 
v_sz_boxed_3893_ = lean_unbox_usize(v_sz_3889_);
lean_dec(v_sz_3889_);
v_i_boxed_3894_ = lean_unbox_usize(v_i_3890_);
lean_dec(v_i_3890_);
v_res_3895_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__2___redArg(v_as_3888_, v_sz_boxed_3893_, v_i_boxed_3894_, v_b_3891_);
lean_dec_ref(v_as_3888_);
return v_res_3895_;
}
}
static lean_object* _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__2(void){
_start:
{
lean_object* v___x_3898_; lean_object* v___x_3899_; lean_object* v___x_3900_; lean_object* v___x_3901_; lean_object* v___x_3902_; lean_object* v___x_3903_; 
v___x_3898_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__1));
v___x_3899_ = lean_unsigned_to_nat(2u);
v___x_3900_ = lean_unsigned_to_nat(366u);
v___x_3901_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__0));
v___x_3902_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__2));
v___x_3903_ = l_mkPanicMessageWithDecl(v___x_3902_, v___x_3901_, v___x_3900_, v___x_3899_, v___x_3898_);
return v___x_3903_;
}
}
static lean_object* _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__4(void){
_start:
{
lean_object* v___x_3905_; lean_object* v___x_3906_; lean_object* v___x_3907_; lean_object* v___x_3908_; lean_object* v___x_3909_; lean_object* v___x_3910_; 
v___x_3905_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__3));
v___x_3906_ = lean_unsigned_to_nat(2u);
v___x_3907_ = lean_unsigned_to_nat(367u);
v___x_3908_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__0));
v___x_3909_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__2));
v___x_3910_ = l_mkPanicMessageWithDecl(v___x_3909_, v___x_3908_, v___x_3907_, v___x_3906_, v___x_3905_);
return v___x_3910_;
}
}
static lean_object* _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__5(void){
_start:
{
lean_object* v___x_3911_; lean_object* v___x_3912_; lean_object* v___x_3913_; 
v___x_3911_ = lean_box(0);
v___x_3912_ = lean_unsigned_to_nat(16u);
v___x_3913_ = lean_mk_array(v___x_3912_, v___x_3911_);
return v___x_3913_;
}
}
static lean_object* _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__6(void){
_start:
{
lean_object* v___x_3914_; lean_object* v___x_3915_; lean_object* v___x_3916_; 
v___x_3914_ = lean_obj_once(&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__5, &l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__5_once, _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__5);
v___x_3915_ = lean_unsigned_to_nat(0u);
v___x_3916_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3916_, 0, v___x_3915_);
lean_ctor_set(v___x_3916_, 1, v___x_3914_);
return v___x_3916_;
}
}
static lean_object* _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__8(void){
_start:
{
lean_object* v___x_3918_; lean_object* v___x_3919_; 
v___x_3918_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__7));
v___x_3919_ = l_Lean_stringToMessageData(v___x_3918_);
return v___x_3919_;
}
}
static lean_object* _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__10(void){
_start:
{
lean_object* v___x_3921_; lean_object* v___x_3922_; 
v___x_3921_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__9));
v___x_3922_ = l_Lean_stringToMessageData(v___x_3921_);
return v___x_3922_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls(lean_object* v_sortedDecls_3923_, lean_object* v_sortedArgs_3924_, lean_object* v_toSortDecls_3925_, lean_object* v_toSortArgs_3926_, lean_object* v_a_3927_, lean_object* v_a_3928_){
_start:
{
lean_object* v___y_3931_; lean_object* v___y_3950_; lean_object* v___y_3951_; lean_object* v___y_3952_; lean_object* v___y_3953_; lean_object* v_snd_3954_; lean_object* v___x_3956_; lean_object* v___x_3957_; uint8_t v___x_3958_; 
v___x_3956_ = lean_array_get_size(v_sortedDecls_3923_);
v___x_3957_ = lean_array_get_size(v_sortedArgs_3924_);
v___x_3958_ = lean_nat_dec_eq(v___x_3956_, v___x_3957_);
if (v___x_3958_ == 0)
{
lean_object* v___x_3959_; lean_object* v___x_3960_; 
lean_dec_ref(v_toSortArgs_3926_);
lean_dec_ref(v_sortedArgs_3924_);
lean_dec_ref(v_sortedDecls_3923_);
v___x_3959_ = lean_obj_once(&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__2, &l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__2_once, _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__2);
v___x_3960_ = l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__0(v___x_3959_, v_a_3927_, v_a_3928_);
return v___x_3960_;
}
else
{
lean_object* v___x_3961_; lean_object* v___x_3962_; uint8_t v___x_3963_; 
v___x_3961_ = lean_array_get_size(v_toSortDecls_3925_);
v___x_3962_ = lean_array_get_size(v_toSortArgs_3926_);
v___x_3963_ = lean_nat_dec_eq(v___x_3961_, v___x_3962_);
if (v___x_3963_ == 0)
{
lean_object* v___x_3964_; lean_object* v___x_3965_; 
lean_dec_ref(v_toSortArgs_3926_);
lean_dec_ref(v_sortedArgs_3924_);
lean_dec_ref(v_sortedDecls_3923_);
v___x_3964_ = lean_obj_once(&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__4, &l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__4_once, _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__4);
v___x_3965_ = l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__0(v___x_3964_, v_a_3927_, v_a_3928_);
return v___x_3965_;
}
else
{
lean_object* v___x_3966_; uint8_t v___x_3967_; 
v___x_3966_ = lean_unsigned_to_nat(0u);
v___x_3967_ = lean_nat_dec_eq(v___x_3961_, v___x_3966_);
if (v___x_3967_ == 0)
{
lean_object* v_options_3968_; lean_object* v_inheritedTraceOptions_3969_; uint8_t v_hasTrace_3970_; lean_object* v_cls_3971_; lean_object* v___y_3973_; lean_object* v___y_3974_; 
v_options_3968_ = lean_ctor_get(v_a_3927_, 2);
v_inheritedTraceOptions_3969_ = lean_ctor_get(v_a_3927_, 13);
v_hasTrace_3970_ = lean_ctor_get_uint8(v_options_3968_, sizeof(void*)*1);
v_cls_3971_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__10));
if (v_hasTrace_3970_ == 0)
{
v___y_3973_ = v_a_3927_;
v___y_3974_ = v_a_3928_;
goto v___jp_3972_;
}
else
{
lean_object* v___x_4075_; uint8_t v___x_4076_; 
v___x_4075_ = lean_obj_once(&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__13, &l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__13_once, _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__13);
v___x_4076_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3969_, v_options_3968_, v___x_4075_);
if (v___x_4076_ == 0)
{
v___y_3973_ = v_a_3927_;
v___y_3974_ = v_a_3928_;
goto v___jp_3972_;
}
else
{
lean_object* v___x_4077_; lean_object* v___x_4078_; 
v___x_4077_ = lean_obj_once(&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__10, &l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__10_once, _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__10);
v___x_4078_ = l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__6(v_cls_3971_, v___x_4077_, v_a_3927_, v_a_3928_);
if (lean_obj_tag(v___x_4078_) == 0)
{
lean_dec_ref(v___x_4078_);
v___y_3973_ = v_a_3927_;
v___y_3974_ = v_a_3928_;
goto v___jp_3972_;
}
else
{
lean_object* v_a_4079_; lean_object* v___x_4081_; uint8_t v_isShared_4082_; uint8_t v_isSharedCheck_4086_; 
lean_dec_ref(v_toSortArgs_3926_);
lean_dec_ref(v_sortedArgs_3924_);
lean_dec_ref(v_sortedDecls_3923_);
v_a_4079_ = lean_ctor_get(v___x_4078_, 0);
v_isSharedCheck_4086_ = !lean_is_exclusive(v___x_4078_);
if (v_isSharedCheck_4086_ == 0)
{
v___x_4081_ = v___x_4078_;
v_isShared_4082_ = v_isSharedCheck_4086_;
goto v_resetjp_4080_;
}
else
{
lean_inc(v_a_4079_);
lean_dec(v___x_4078_);
v___x_4081_ = lean_box(0);
v_isShared_4082_ = v_isSharedCheck_4086_;
goto v_resetjp_4080_;
}
v_resetjp_4080_:
{
lean_object* v___x_4084_; 
if (v_isShared_4082_ == 0)
{
v___x_4084_ = v___x_4081_;
goto v_reusejp_4083_;
}
else
{
lean_object* v_reuseFailAlloc_4085_; 
v_reuseFailAlloc_4085_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4085_, 0, v_a_4079_);
v___x_4084_ = v_reuseFailAlloc_4085_;
goto v_reusejp_4083_;
}
v_reusejp_4083_:
{
return v___x_4084_;
}
}
}
}
}
v___jp_3972_:
{
lean_object* v___x_3975_; lean_object* v___x_3976_; lean_object* v___x_3977_; size_t v_sz_3978_; size_t v___x_3979_; lean_object* v___x_3980_; 
v___x_3975_ = lean_obj_once(&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__6, &l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__6_once, _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__6);
v___x_3976_ = l_Array_toSubarray___redArg(v_sortedArgs_3924_, v___x_3966_, v___x_3957_);
v___x_3977_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3977_, 0, v___x_3975_);
lean_ctor_set(v___x_3977_, 1, v___x_3976_);
v_sz_3978_ = lean_array_size(v_sortedDecls_3923_);
v___x_3979_ = ((size_t)0ULL);
v___x_3980_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__2___redArg(v_sortedDecls_3923_, v_sz_3978_, v___x_3979_, v___x_3977_);
if (lean_obj_tag(v___x_3980_) == 0)
{
lean_object* v_a_3981_; lean_object* v_fst_3982_; lean_object* v___x_3984_; uint8_t v_isShared_3985_; uint8_t v_isSharedCheck_4065_; 
v_a_3981_ = lean_ctor_get(v___x_3980_, 0);
lean_inc(v_a_3981_);
lean_dec_ref(v___x_3980_);
v_fst_3982_ = lean_ctor_get(v_a_3981_, 0);
v_isSharedCheck_4065_ = !lean_is_exclusive(v_a_3981_);
if (v_isSharedCheck_4065_ == 0)
{
lean_object* v_unused_4066_; 
v_unused_4066_ = lean_ctor_get(v_a_3981_, 1);
lean_dec(v_unused_4066_);
v___x_3984_ = v_a_3981_;
v_isShared_3985_ = v_isSharedCheck_4065_;
goto v_resetjp_3983_;
}
else
{
lean_inc(v_fst_3982_);
lean_dec(v_a_3981_);
v___x_3984_ = lean_box(0);
v_isShared_3985_ = v_isSharedCheck_4065_;
goto v_resetjp_3983_;
}
v_resetjp_3983_:
{
lean_object* v___x_3986_; lean_object* v___x_3988_; 
v___x_3986_ = l_Array_toSubarray___redArg(v_toSortArgs_3926_, v___x_3966_, v___x_3962_);
if (v_isShared_3985_ == 0)
{
lean_ctor_set(v___x_3984_, 1, v___x_3986_);
v___x_3988_ = v___x_3984_;
goto v_reusejp_3987_;
}
else
{
lean_object* v_reuseFailAlloc_4064_; 
v_reuseFailAlloc_4064_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4064_, 0, v_fst_3982_);
lean_ctor_set(v_reuseFailAlloc_4064_, 1, v___x_3986_);
v___x_3988_ = v_reuseFailAlloc_4064_;
goto v_reusejp_3987_;
}
v_reusejp_3987_:
{
size_t v_sz_3989_; lean_object* v___x_3990_; 
v_sz_3989_ = lean_array_size(v_toSortDecls_3925_);
v___x_3990_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__2___redArg(v_toSortDecls_3925_, v_sz_3989_, v___x_3979_, v___x_3988_);
if (lean_obj_tag(v___x_3990_) == 0)
{
lean_object* v_a_3991_; lean_object* v_fst_3992_; lean_object* v_size_3993_; lean_object* v___x_3994_; lean_object* v___x_3995_; lean_object* v___x_3996_; lean_object* v___x_3997_; lean_object* v___x_3998_; 
v_a_3991_ = lean_ctor_get(v___x_3990_, 0);
lean_inc(v_a_3991_);
lean_dec_ref(v___x_3990_);
v_fst_3992_ = lean_ctor_get(v_a_3991_, 0);
lean_inc_n(v_fst_3992_, 2);
lean_dec(v_a_3991_);
v_size_3993_ = lean_ctor_get(v_fst_3992_, 0);
v___x_3994_ = l_Lean_instEmptyCollectionFVarIdHashSet;
v___x_3995_ = lean_mk_empty_array_with_capacity(v_size_3993_);
lean_inc_ref(v___x_3995_);
v___x_3996_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3996_, 0, v___x_3994_);
lean_ctor_set(v___x_3996_, 1, v___x_3994_);
lean_ctor_set(v___x_3996_, 2, v___x_3995_);
lean_ctor_set(v___x_3996_, 3, v___x_3995_);
v___x_3997_ = lean_box(0);
v___x_3998_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__3(v_fst_3992_, v_sortedDecls_3923_, v_sz_3978_, v___x_3979_, v___x_3997_, v___x_3996_, v___y_3973_, v___y_3974_);
lean_dec_ref(v_sortedDecls_3923_);
if (lean_obj_tag(v___x_3998_) == 0)
{
lean_object* v_a_3999_; lean_object* v_snd_4000_; lean_object* v___x_4001_; 
v_a_3999_ = lean_ctor_get(v___x_3998_, 0);
lean_inc(v_a_3999_);
lean_dec_ref(v___x_3998_);
v_snd_4000_ = lean_ctor_get(v_a_3999_, 1);
lean_inc(v_snd_4000_);
lean_dec(v_a_3999_);
v___x_4001_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__3(v_fst_3992_, v_toSortDecls_3925_, v_sz_3989_, v___x_3979_, v___x_3997_, v_snd_4000_, v___y_3973_, v___y_3974_);
if (lean_obj_tag(v___x_4001_) == 0)
{
lean_object* v_a_4002_; lean_object* v_snd_4003_; lean_object* v___x_4005_; uint8_t v_isShared_4006_; uint8_t v_isSharedCheck_4038_; 
v_a_4002_ = lean_ctor_get(v___x_4001_, 0);
lean_inc(v_a_4002_);
lean_dec_ref(v___x_4001_);
v_snd_4003_ = lean_ctor_get(v_a_4002_, 1);
v_isSharedCheck_4038_ = !lean_is_exclusive(v_a_4002_);
if (v_isSharedCheck_4038_ == 0)
{
lean_object* v_unused_4039_; 
v_unused_4039_ = lean_ctor_get(v_a_4002_, 0);
lean_dec(v_unused_4039_);
v___x_4005_ = v_a_4002_;
v_isShared_4006_ = v_isSharedCheck_4038_;
goto v_resetjp_4004_;
}
else
{
lean_inc(v_snd_4003_);
lean_dec(v_a_4002_);
v___x_4005_ = lean_box(0);
v_isShared_4006_ = v_isSharedCheck_4038_;
goto v_resetjp_4004_;
}
v_resetjp_4004_:
{
lean_object* v_options_4007_; lean_object* v_newDecls_4008_; lean_object* v_newArgs_4009_; lean_object* v_inheritedTraceOptions_4010_; uint8_t v_hasTrace_4011_; lean_object* v___f_4012_; 
v_options_4007_ = lean_ctor_get(v___y_3973_, 2);
v_newDecls_4008_ = lean_ctor_get(v_snd_4003_, 2);
v_newArgs_4009_ = lean_ctor_get(v_snd_4003_, 3);
v_inheritedTraceOptions_4010_ = lean_ctor_get(v___y_3973_, 13);
v_hasTrace_4011_ = lean_ctor_get_uint8(v_options_4007_, sizeof(void*)*1);
lean_inc_ref(v_newArgs_4009_);
lean_inc_ref(v_newDecls_4008_);
v___f_4012_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___lam__0___boxed), 7, 2);
lean_closure_set(v___f_4012_, 0, v_newDecls_4008_);
lean_closure_set(v___f_4012_, 1, v_newArgs_4009_);
if (v_hasTrace_4011_ == 0)
{
lean_del_object(v___x_4005_);
v___y_3950_ = v___x_3997_;
v___y_3951_ = v___y_3973_;
v___y_3952_ = v___f_4012_;
v___y_3953_ = v___y_3974_;
v_snd_3954_ = v_snd_4003_;
goto v___jp_3949_;
}
else
{
lean_object* v___x_4013_; uint8_t v___x_4014_; 
v___x_4013_ = lean_obj_once(&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__13, &l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__13_once, _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__13);
v___x_4014_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4010_, v_options_4007_, v___x_4013_);
if (v___x_4014_ == 0)
{
lean_del_object(v___x_4005_);
v___y_3950_ = v___x_3997_;
v___y_3951_ = v___y_3973_;
v___y_3952_ = v___f_4012_;
v___y_3953_ = v___y_3974_;
v_snd_3954_ = v_snd_4003_;
goto v___jp_3949_;
}
else
{
lean_object* v___x_4015_; size_t v_sz_4016_; lean_object* v___x_4017_; lean_object* v___x_4018_; lean_object* v___x_4019_; lean_object* v___x_4020_; lean_object* v___x_4021_; lean_object* v___x_4023_; 
lean_inc_ref(v_newArgs_4009_);
lean_inc_ref_n(v_newDecls_4008_, 2);
lean_dec_ref(v___f_4012_);
v___x_4015_ = lean_obj_once(&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__8, &l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__8_once, _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__8);
v_sz_4016_ = lean_array_size(v_newDecls_4008_);
v___x_4017_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__4(v_sz_4016_, v___x_3979_, v_newDecls_4008_);
v___x_4018_ = lean_array_to_list(v___x_4017_);
v___x_4019_ = lean_box(0);
v___x_4020_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__5(v___x_4018_, v___x_4019_);
v___x_4021_ = l_Lean_MessageData_ofList(v___x_4020_);
if (v_isShared_4006_ == 0)
{
lean_ctor_set_tag(v___x_4005_, 7);
lean_ctor_set(v___x_4005_, 1, v___x_4021_);
lean_ctor_set(v___x_4005_, 0, v___x_4015_);
v___x_4023_ = v___x_4005_;
goto v_reusejp_4022_;
}
else
{
lean_object* v_reuseFailAlloc_4037_; 
v_reuseFailAlloc_4037_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4037_, 0, v___x_4015_);
lean_ctor_set(v_reuseFailAlloc_4037_, 1, v___x_4021_);
v___x_4023_ = v_reuseFailAlloc_4037_;
goto v_reusejp_4022_;
}
v_reusejp_4022_:
{
lean_object* v___x_4024_; 
v___x_4024_ = l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6(v_cls_3971_, v___x_4023_, v_snd_4003_, v___y_3973_, v___y_3974_);
if (lean_obj_tag(v___x_4024_) == 0)
{
lean_object* v_a_4025_; lean_object* v_fst_4026_; lean_object* v_snd_4027_; lean_object* v___x_4028_; 
v_a_4025_ = lean_ctor_get(v___x_4024_, 0);
lean_inc(v_a_4025_);
lean_dec_ref(v___x_4024_);
v_fst_4026_ = lean_ctor_get(v_a_4025_, 0);
lean_inc(v_fst_4026_);
v_snd_4027_ = lean_ctor_get(v_a_4025_, 1);
lean_inc(v_snd_4027_);
lean_dec(v_a_4025_);
v___x_4028_ = l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___lam__0(v_newDecls_4008_, v_newArgs_4009_, v_fst_4026_, v_snd_4027_, v___y_3973_, v___y_3974_);
v___y_3931_ = v___x_4028_;
goto v___jp_3930_;
}
else
{
lean_object* v_a_4029_; lean_object* v___x_4031_; uint8_t v_isShared_4032_; uint8_t v_isSharedCheck_4036_; 
lean_dec_ref(v_newArgs_4009_);
lean_dec_ref(v_newDecls_4008_);
v_a_4029_ = lean_ctor_get(v___x_4024_, 0);
v_isSharedCheck_4036_ = !lean_is_exclusive(v___x_4024_);
if (v_isSharedCheck_4036_ == 0)
{
v___x_4031_ = v___x_4024_;
v_isShared_4032_ = v_isSharedCheck_4036_;
goto v_resetjp_4030_;
}
else
{
lean_inc(v_a_4029_);
lean_dec(v___x_4024_);
v___x_4031_ = lean_box(0);
v_isShared_4032_ = v_isSharedCheck_4036_;
goto v_resetjp_4030_;
}
v_resetjp_4030_:
{
lean_object* v___x_4034_; 
if (v_isShared_4032_ == 0)
{
v___x_4034_ = v___x_4031_;
goto v_reusejp_4033_;
}
else
{
lean_object* v_reuseFailAlloc_4035_; 
v_reuseFailAlloc_4035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4035_, 0, v_a_4029_);
v___x_4034_ = v_reuseFailAlloc_4035_;
goto v_reusejp_4033_;
}
v_reusejp_4033_:
{
return v___x_4034_;
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
lean_object* v_a_4040_; lean_object* v___x_4042_; uint8_t v_isShared_4043_; uint8_t v_isSharedCheck_4047_; 
v_a_4040_ = lean_ctor_get(v___x_4001_, 0);
v_isSharedCheck_4047_ = !lean_is_exclusive(v___x_4001_);
if (v_isSharedCheck_4047_ == 0)
{
v___x_4042_ = v___x_4001_;
v_isShared_4043_ = v_isSharedCheck_4047_;
goto v_resetjp_4041_;
}
else
{
lean_inc(v_a_4040_);
lean_dec(v___x_4001_);
v___x_4042_ = lean_box(0);
v_isShared_4043_ = v_isSharedCheck_4047_;
goto v_resetjp_4041_;
}
v_resetjp_4041_:
{
lean_object* v___x_4045_; 
if (v_isShared_4043_ == 0)
{
v___x_4045_ = v___x_4042_;
goto v_reusejp_4044_;
}
else
{
lean_object* v_reuseFailAlloc_4046_; 
v_reuseFailAlloc_4046_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4046_, 0, v_a_4040_);
v___x_4045_ = v_reuseFailAlloc_4046_;
goto v_reusejp_4044_;
}
v_reusejp_4044_:
{
return v___x_4045_;
}
}
}
}
else
{
lean_object* v_a_4048_; lean_object* v___x_4050_; uint8_t v_isShared_4051_; uint8_t v_isSharedCheck_4055_; 
lean_dec(v_fst_3992_);
v_a_4048_ = lean_ctor_get(v___x_3998_, 0);
v_isSharedCheck_4055_ = !lean_is_exclusive(v___x_3998_);
if (v_isSharedCheck_4055_ == 0)
{
v___x_4050_ = v___x_3998_;
v_isShared_4051_ = v_isSharedCheck_4055_;
goto v_resetjp_4049_;
}
else
{
lean_inc(v_a_4048_);
lean_dec(v___x_3998_);
v___x_4050_ = lean_box(0);
v_isShared_4051_ = v_isSharedCheck_4055_;
goto v_resetjp_4049_;
}
v_resetjp_4049_:
{
lean_object* v___x_4053_; 
if (v_isShared_4051_ == 0)
{
v___x_4053_ = v___x_4050_;
goto v_reusejp_4052_;
}
else
{
lean_object* v_reuseFailAlloc_4054_; 
v_reuseFailAlloc_4054_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4054_, 0, v_a_4048_);
v___x_4053_ = v_reuseFailAlloc_4054_;
goto v_reusejp_4052_;
}
v_reusejp_4052_:
{
return v___x_4053_;
}
}
}
}
else
{
lean_object* v_a_4056_; lean_object* v___x_4058_; uint8_t v_isShared_4059_; uint8_t v_isSharedCheck_4063_; 
lean_dec_ref(v_sortedDecls_3923_);
v_a_4056_ = lean_ctor_get(v___x_3990_, 0);
v_isSharedCheck_4063_ = !lean_is_exclusive(v___x_3990_);
if (v_isSharedCheck_4063_ == 0)
{
v___x_4058_ = v___x_3990_;
v_isShared_4059_ = v_isSharedCheck_4063_;
goto v_resetjp_4057_;
}
else
{
lean_inc(v_a_4056_);
lean_dec(v___x_3990_);
v___x_4058_ = lean_box(0);
v_isShared_4059_ = v_isSharedCheck_4063_;
goto v_resetjp_4057_;
}
v_resetjp_4057_:
{
lean_object* v___x_4061_; 
if (v_isShared_4059_ == 0)
{
v___x_4061_ = v___x_4058_;
goto v_reusejp_4060_;
}
else
{
lean_object* v_reuseFailAlloc_4062_; 
v_reuseFailAlloc_4062_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4062_, 0, v_a_4056_);
v___x_4061_ = v_reuseFailAlloc_4062_;
goto v_reusejp_4060_;
}
v_reusejp_4060_:
{
return v___x_4061_;
}
}
}
}
}
}
else
{
lean_object* v_a_4067_; lean_object* v___x_4069_; uint8_t v_isShared_4070_; uint8_t v_isSharedCheck_4074_; 
lean_dec_ref(v_toSortArgs_3926_);
lean_dec_ref(v_sortedDecls_3923_);
v_a_4067_ = lean_ctor_get(v___x_3980_, 0);
v_isSharedCheck_4074_ = !lean_is_exclusive(v___x_3980_);
if (v_isSharedCheck_4074_ == 0)
{
v___x_4069_ = v___x_3980_;
v_isShared_4070_ = v_isSharedCheck_4074_;
goto v_resetjp_4068_;
}
else
{
lean_inc(v_a_4067_);
lean_dec(v___x_3980_);
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
else
{
lean_object* v___x_4087_; lean_object* v___x_4088_; 
lean_dec_ref(v_toSortArgs_3926_);
v___x_4087_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4087_, 0, v_sortedDecls_3923_);
lean_ctor_set(v___x_4087_, 1, v_sortedArgs_3924_);
v___x_4088_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4088_, 0, v___x_4087_);
return v___x_4088_;
}
}
}
v___jp_3930_:
{
if (lean_obj_tag(v___y_3931_) == 0)
{
lean_object* v_a_3932_; lean_object* v___x_3934_; uint8_t v_isShared_3935_; uint8_t v_isSharedCheck_3940_; 
v_a_3932_ = lean_ctor_get(v___y_3931_, 0);
v_isSharedCheck_3940_ = !lean_is_exclusive(v___y_3931_);
if (v_isSharedCheck_3940_ == 0)
{
v___x_3934_ = v___y_3931_;
v_isShared_3935_ = v_isSharedCheck_3940_;
goto v_resetjp_3933_;
}
else
{
lean_inc(v_a_3932_);
lean_dec(v___y_3931_);
v___x_3934_ = lean_box(0);
v_isShared_3935_ = v_isSharedCheck_3940_;
goto v_resetjp_3933_;
}
v_resetjp_3933_:
{
lean_object* v_fst_3936_; lean_object* v___x_3938_; 
v_fst_3936_ = lean_ctor_get(v_a_3932_, 0);
lean_inc(v_fst_3936_);
lean_dec(v_a_3932_);
if (v_isShared_3935_ == 0)
{
lean_ctor_set(v___x_3934_, 0, v_fst_3936_);
v___x_3938_ = v___x_3934_;
goto v_reusejp_3937_;
}
else
{
lean_object* v_reuseFailAlloc_3939_; 
v_reuseFailAlloc_3939_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3939_, 0, v_fst_3936_);
v___x_3938_ = v_reuseFailAlloc_3939_;
goto v_reusejp_3937_;
}
v_reusejp_3937_:
{
return v___x_3938_;
}
}
}
else
{
lean_object* v_a_3941_; lean_object* v___x_3943_; uint8_t v_isShared_3944_; uint8_t v_isSharedCheck_3948_; 
v_a_3941_ = lean_ctor_get(v___y_3931_, 0);
v_isSharedCheck_3948_ = !lean_is_exclusive(v___y_3931_);
if (v_isSharedCheck_3948_ == 0)
{
v___x_3943_ = v___y_3931_;
v_isShared_3944_ = v_isSharedCheck_3948_;
goto v_resetjp_3942_;
}
else
{
lean_inc(v_a_3941_);
lean_dec(v___y_3931_);
v___x_3943_ = lean_box(0);
v_isShared_3944_ = v_isSharedCheck_3948_;
goto v_resetjp_3942_;
}
v_resetjp_3942_:
{
lean_object* v___x_3946_; 
if (v_isShared_3944_ == 0)
{
v___x_3946_ = v___x_3943_;
goto v_reusejp_3945_;
}
else
{
lean_object* v_reuseFailAlloc_3947_; 
v_reuseFailAlloc_3947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3947_, 0, v_a_3941_);
v___x_3946_ = v_reuseFailAlloc_3947_;
goto v_reusejp_3945_;
}
v_reusejp_3945_:
{
return v___x_3946_;
}
}
}
}
v___jp_3949_:
{
lean_object* v___x_3955_; 
lean_inc(v___y_3953_);
lean_inc_ref(v___y_3951_);
v___x_3955_ = lean_apply_5(v___y_3952_, v___y_3950_, v_snd_3954_, v___y_3951_, v___y_3953_, lean_box(0));
v___y_3931_ = v___x_3955_;
goto v___jp_3930_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___boxed(lean_object* v_sortedDecls_4089_, lean_object* v_sortedArgs_4090_, lean_object* v_toSortDecls_4091_, lean_object* v_toSortArgs_4092_, lean_object* v_a_4093_, lean_object* v_a_4094_, lean_object* v_a_4095_){
_start:
{
lean_object* v_res_4096_; 
v_res_4096_ = l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls(v_sortedDecls_4089_, v_sortedArgs_4090_, v_toSortDecls_4091_, v_toSortArgs_4092_, v_a_4093_, v_a_4094_);
lean_dec(v_a_4094_);
lean_dec_ref(v_a_4093_);
lean_dec_ref(v_toSortDecls_4091_);
return v_res_4096_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__1(lean_object* v_00_u03b2_4097_, lean_object* v_m_4098_, lean_object* v_a_4099_, lean_object* v_b_4100_){
_start:
{
lean_object* v___x_4101_; 
v___x_4101_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__1___redArg(v_m_4098_, v_a_4099_, v_b_4100_);
return v___x_4101_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__2(lean_object* v_as_4102_, size_t v_sz_4103_, size_t v_i_4104_, lean_object* v_b_4105_, lean_object* v___y_4106_, lean_object* v___y_4107_){
_start:
{
lean_object* v___x_4109_; 
v___x_4109_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__2___redArg(v_as_4102_, v_sz_4103_, v_i_4104_, v_b_4105_);
return v___x_4109_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__2___boxed(lean_object* v_as_4110_, lean_object* v_sz_4111_, lean_object* v_i_4112_, lean_object* v_b_4113_, lean_object* v___y_4114_, lean_object* v___y_4115_, lean_object* v___y_4116_){
_start:
{
size_t v_sz_boxed_4117_; size_t v_i_boxed_4118_; lean_object* v_res_4119_; 
v_sz_boxed_4117_ = lean_unbox_usize(v_sz_4111_);
lean_dec(v_sz_4111_);
v_i_boxed_4118_ = lean_unbox_usize(v_i_4112_);
lean_dec(v_i_4112_);
v_res_4119_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__2(v_as_4110_, v_sz_boxed_4117_, v_i_boxed_4118_, v_b_4113_, v___y_4114_, v___y_4115_);
lean_dec(v___y_4115_);
lean_dec_ref(v___y_4114_);
lean_dec_ref(v_as_4110_);
return v_res_4119_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__1_spec__1(lean_object* v_00_u03b2_4120_, lean_object* v_a_4121_, lean_object* v_b_4122_, lean_object* v_x_4123_){
_start:
{
lean_object* v___x_4124_; 
v___x_4124_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__1_spec__1___redArg(v_a_4121_, v_b_4122_, v_x_4123_);
return v___x_4124_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Closure_mkValueTypeClosure_spec__0(lean_object* v_msg_4126_, lean_object* v___y_4127_, lean_object* v___y_4128_, lean_object* v___y_4129_, lean_object* v___y_4130_){
_start:
{
lean_object* v___f_4132_; lean_object* v___x_1329__overap_4133_; lean_object* v___x_4134_; 
v___f_4132_ = ((lean_object*)(l_panic___at___00Lean_Meta_Closure_mkValueTypeClosure_spec__0___closed__0));
v___x_1329__overap_4133_ = lean_panic_fn_borrowed(v___f_4132_, v_msg_4126_);
lean_inc(v___y_4130_);
lean_inc_ref(v___y_4129_);
lean_inc(v___y_4128_);
lean_inc_ref(v___y_4127_);
v___x_4134_ = lean_apply_5(v___x_1329__overap_4133_, v___y_4127_, v___y_4128_, v___y_4129_, v___y_4130_, lean_box(0));
return v___x_4134_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Closure_mkValueTypeClosure_spec__0___boxed(lean_object* v_msg_4135_, lean_object* v___y_4136_, lean_object* v___y_4137_, lean_object* v___y_4138_, lean_object* v___y_4139_, lean_object* v___y_4140_){
_start:
{
lean_object* v_res_4141_; 
v_res_4141_ = l_panic___at___00Lean_Meta_Closure_mkValueTypeClosure_spec__0(v_msg_4135_, v___y_4136_, v___y_4137_, v___y_4138_, v___y_4139_);
lean_dec(v___y_4139_);
lean_dec_ref(v___y_4138_);
lean_dec(v___y_4137_);
lean_dec_ref(v___y_4136_);
return v_res_4141_;
}
}
static lean_object* _init_l_Lean_Meta_Closure_mkValueTypeClosure___closed__0(void){
_start:
{
lean_object* v___x_4142_; lean_object* v___x_4143_; lean_object* v___x_4144_; 
v___x_4142_ = lean_box(0);
v___x_4143_ = lean_unsigned_to_nat(16u);
v___x_4144_ = lean_mk_array(v___x_4143_, v___x_4142_);
return v___x_4144_;
}
}
static lean_object* _init_l_Lean_Meta_Closure_mkValueTypeClosure___closed__1(void){
_start:
{
lean_object* v___x_4145_; lean_object* v___x_4146_; lean_object* v___x_4147_; 
v___x_4145_ = lean_obj_once(&l_Lean_Meta_Closure_mkValueTypeClosure___closed__0, &l_Lean_Meta_Closure_mkValueTypeClosure___closed__0_once, _init_l_Lean_Meta_Closure_mkValueTypeClosure___closed__0);
v___x_4146_ = lean_unsigned_to_nat(0u);
v___x_4147_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4147_, 0, v___x_4146_);
lean_ctor_set(v___x_4147_, 1, v___x_4145_);
return v___x_4147_;
}
}
static lean_object* _init_l_Lean_Meta_Closure_mkValueTypeClosure___closed__3(void){
_start:
{
lean_object* v___x_4150_; lean_object* v___x_4151_; lean_object* v___x_4152_; lean_object* v___x_4153_; 
v___x_4150_ = lean_unsigned_to_nat(1u);
v___x_4151_ = ((lean_object*)(l_Lean_Meta_Closure_mkValueTypeClosure___closed__2));
v___x_4152_ = lean_obj_once(&l_Lean_Meta_Closure_mkValueTypeClosure___closed__1, &l_Lean_Meta_Closure_mkValueTypeClosure___closed__1_once, _init_l_Lean_Meta_Closure_mkValueTypeClosure___closed__1);
v___x_4153_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_4153_, 0, v___x_4152_);
lean_ctor_set(v___x_4153_, 1, v___x_4152_);
lean_ctor_set(v___x_4153_, 2, v___x_4151_);
lean_ctor_set(v___x_4153_, 3, v___x_4150_);
lean_ctor_set(v___x_4153_, 4, v___x_4151_);
lean_ctor_set(v___x_4153_, 5, v___x_4151_);
lean_ctor_set(v___x_4153_, 6, v___x_4151_);
lean_ctor_set(v___x_4153_, 7, v___x_4151_);
lean_ctor_set(v___x_4153_, 8, v___x_4150_);
lean_ctor_set(v___x_4153_, 9, v___x_4151_);
lean_ctor_set(v___x_4153_, 10, v___x_4151_);
lean_ctor_set(v___x_4153_, 11, v___x_4151_);
return v___x_4153_;
}
}
static lean_object* _init_l_Lean_Meta_Closure_mkValueTypeClosure___closed__6(void){
_start:
{
lean_object* v___x_4156_; lean_object* v___x_4157_; lean_object* v___x_4158_; lean_object* v___x_4159_; lean_object* v___x_4160_; lean_object* v___x_4161_; 
v___x_4156_ = ((lean_object*)(l_Lean_Meta_Closure_mkValueTypeClosure___closed__5));
v___x_4157_ = lean_unsigned_to_nat(2u);
v___x_4158_ = lean_unsigned_to_nat(417u);
v___x_4159_ = ((lean_object*)(l_Lean_Meta_Closure_mkValueTypeClosure___closed__4));
v___x_4160_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__2));
v___x_4161_ = l_mkPanicMessageWithDecl(v___x_4160_, v___x_4159_, v___x_4158_, v___x_4157_, v___x_4156_);
return v___x_4161_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkValueTypeClosure(lean_object* v_type_4162_, lean_object* v_value_4163_, uint8_t v_zetaDelta_4164_, lean_object* v_a_4165_, lean_object* v_a_4166_, lean_object* v_a_4167_, lean_object* v_a_4168_){
_start:
{
lean_object* v___x_4170_; lean_object* v___x_4171_; lean_object* v___x_4172_; 
v___x_4170_ = lean_obj_once(&l_Lean_Meta_Closure_mkValueTypeClosure___closed__3, &l_Lean_Meta_Closure_mkValueTypeClosure___closed__3_once, _init_l_Lean_Meta_Closure_mkValueTypeClosure___closed__3);
v___x_4171_ = lean_st_mk_ref(v___x_4170_);
v___x_4172_ = l_Lean_Meta_Closure_mkValueTypeClosureAux(v_type_4162_, v_value_4163_, v_zetaDelta_4164_, v___x_4171_, v_a_4165_, v_a_4166_, v_a_4167_, v_a_4168_);
if (lean_obj_tag(v___x_4172_) == 0)
{
lean_object* v_a_4173_; lean_object* v___x_4174_; lean_object* v_fst_4175_; lean_object* v_snd_4176_; lean_object* v_levelParams_4177_; lean_object* v_levelArgs_4178_; lean_object* v_newLocalDecls_4179_; lean_object* v_newLocalDeclsForMVars_4180_; lean_object* v_newLetDecls_4181_; lean_object* v_exprMVarArgs_4182_; lean_object* v_exprFVarArgs_4183_; lean_object* v___x_4184_; lean_object* v___x_4185_; lean_object* v___x_4186_; 
v_a_4173_ = lean_ctor_get(v___x_4172_, 0);
lean_inc(v_a_4173_);
lean_dec_ref(v___x_4172_);
v___x_4174_ = lean_st_ref_get(v___x_4171_);
lean_dec(v___x_4171_);
v_fst_4175_ = lean_ctor_get(v_a_4173_, 0);
lean_inc(v_fst_4175_);
v_snd_4176_ = lean_ctor_get(v_a_4173_, 1);
lean_inc(v_snd_4176_);
lean_dec(v_a_4173_);
v_levelParams_4177_ = lean_ctor_get(v___x_4174_, 2);
lean_inc_ref(v_levelParams_4177_);
v_levelArgs_4178_ = lean_ctor_get(v___x_4174_, 4);
lean_inc_ref(v_levelArgs_4178_);
v_newLocalDecls_4179_ = lean_ctor_get(v___x_4174_, 5);
lean_inc_ref(v_newLocalDecls_4179_);
v_newLocalDeclsForMVars_4180_ = lean_ctor_get(v___x_4174_, 6);
lean_inc_ref(v_newLocalDeclsForMVars_4180_);
v_newLetDecls_4181_ = lean_ctor_get(v___x_4174_, 7);
lean_inc_ref(v_newLetDecls_4181_);
v_exprMVarArgs_4182_ = lean_ctor_get(v___x_4174_, 9);
lean_inc_ref(v_exprMVarArgs_4182_);
v_exprFVarArgs_4183_ = lean_ctor_get(v___x_4174_, 10);
lean_inc_ref(v_exprFVarArgs_4183_);
lean_dec(v___x_4174_);
v___x_4184_ = l_Array_reverse___redArg(v_newLocalDecls_4179_);
v___x_4185_ = l_Array_reverse___redArg(v_exprFVarArgs_4183_);
v___x_4186_ = l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls(v___x_4184_, v___x_4185_, v_newLocalDeclsForMVars_4180_, v_exprMVarArgs_4182_, v_a_4167_, v_a_4168_);
lean_dec_ref(v_newLocalDeclsForMVars_4180_);
if (lean_obj_tag(v___x_4186_) == 0)
{
lean_object* v_a_4187_; lean_object* v___x_4189_; uint8_t v_isShared_4190_; uint8_t v_isSharedCheck_4205_; 
v_a_4187_ = lean_ctor_get(v___x_4186_, 0);
v_isSharedCheck_4205_ = !lean_is_exclusive(v___x_4186_);
if (v_isSharedCheck_4205_ == 0)
{
v___x_4189_ = v___x_4186_;
v_isShared_4190_ = v_isSharedCheck_4205_;
goto v_resetjp_4188_;
}
else
{
lean_inc(v_a_4187_);
lean_dec(v___x_4186_);
v___x_4189_ = lean_box(0);
v_isShared_4190_ = v_isSharedCheck_4205_;
goto v_resetjp_4188_;
}
v_resetjp_4188_:
{
lean_object* v_fst_4191_; lean_object* v_snd_4192_; lean_object* v___x_4193_; lean_object* v___x_4194_; lean_object* v___x_4195_; lean_object* v___x_4196_; lean_object* v___x_4197_; uint8_t v___x_4198_; 
v_fst_4191_ = lean_ctor_get(v_a_4187_, 0);
lean_inc_n(v_fst_4191_, 2);
v_snd_4192_ = lean_ctor_get(v_a_4187_, 1);
lean_inc(v_snd_4192_);
lean_dec(v_a_4187_);
v___x_4193_ = l_Array_reverse___redArg(v_newLetDecls_4181_);
lean_inc_ref(v___x_4193_);
v___x_4194_ = l_Lean_Meta_Closure_mkForall(v___x_4193_, v_fst_4175_);
lean_dec(v_fst_4175_);
v___x_4195_ = l_Lean_Meta_Closure_mkForall(v_fst_4191_, v___x_4194_);
lean_dec_ref(v___x_4194_);
v___x_4196_ = l_Lean_Meta_Closure_mkLambda(v___x_4193_, v_snd_4176_);
lean_dec(v_snd_4176_);
v___x_4197_ = l_Lean_Meta_Closure_mkLambda(v_fst_4191_, v___x_4196_);
lean_dec_ref(v___x_4196_);
v___x_4198_ = l_Lean_Expr_hasFVar(v___x_4197_);
if (v___x_4198_ == 0)
{
lean_object* v___x_4199_; lean_object* v___x_4201_; 
v___x_4199_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4199_, 0, v_levelParams_4177_);
lean_ctor_set(v___x_4199_, 1, v___x_4195_);
lean_ctor_set(v___x_4199_, 2, v___x_4197_);
lean_ctor_set(v___x_4199_, 3, v_levelArgs_4178_);
lean_ctor_set(v___x_4199_, 4, v_snd_4192_);
if (v_isShared_4190_ == 0)
{
lean_ctor_set(v___x_4189_, 0, v___x_4199_);
v___x_4201_ = v___x_4189_;
goto v_reusejp_4200_;
}
else
{
lean_object* v_reuseFailAlloc_4202_; 
v_reuseFailAlloc_4202_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4202_, 0, v___x_4199_);
v___x_4201_ = v_reuseFailAlloc_4202_;
goto v_reusejp_4200_;
}
v_reusejp_4200_:
{
return v___x_4201_;
}
}
else
{
lean_object* v___x_4203_; lean_object* v___x_4204_; 
lean_dec_ref(v___x_4197_);
lean_dec_ref(v___x_4195_);
lean_dec(v_snd_4192_);
lean_del_object(v___x_4189_);
lean_dec_ref(v_levelArgs_4178_);
lean_dec_ref(v_levelParams_4177_);
v___x_4203_ = lean_obj_once(&l_Lean_Meta_Closure_mkValueTypeClosure___closed__6, &l_Lean_Meta_Closure_mkValueTypeClosure___closed__6_once, _init_l_Lean_Meta_Closure_mkValueTypeClosure___closed__6);
v___x_4204_ = l_panic___at___00Lean_Meta_Closure_mkValueTypeClosure_spec__0(v___x_4203_, v_a_4165_, v_a_4166_, v_a_4167_, v_a_4168_);
return v___x_4204_;
}
}
}
else
{
lean_object* v_a_4206_; lean_object* v___x_4208_; uint8_t v_isShared_4209_; uint8_t v_isSharedCheck_4213_; 
lean_dec_ref(v_newLetDecls_4181_);
lean_dec_ref(v_levelArgs_4178_);
lean_dec_ref(v_levelParams_4177_);
lean_dec(v_snd_4176_);
lean_dec(v_fst_4175_);
v_a_4206_ = lean_ctor_get(v___x_4186_, 0);
v_isSharedCheck_4213_ = !lean_is_exclusive(v___x_4186_);
if (v_isSharedCheck_4213_ == 0)
{
v___x_4208_ = v___x_4186_;
v_isShared_4209_ = v_isSharedCheck_4213_;
goto v_resetjp_4207_;
}
else
{
lean_inc(v_a_4206_);
lean_dec(v___x_4186_);
v___x_4208_ = lean_box(0);
v_isShared_4209_ = v_isSharedCheck_4213_;
goto v_resetjp_4207_;
}
v_resetjp_4207_:
{
lean_object* v___x_4211_; 
if (v_isShared_4209_ == 0)
{
v___x_4211_ = v___x_4208_;
goto v_reusejp_4210_;
}
else
{
lean_object* v_reuseFailAlloc_4212_; 
v_reuseFailAlloc_4212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4212_, 0, v_a_4206_);
v___x_4211_ = v_reuseFailAlloc_4212_;
goto v_reusejp_4210_;
}
v_reusejp_4210_:
{
return v___x_4211_;
}
}
}
}
else
{
lean_object* v_a_4214_; lean_object* v___x_4216_; uint8_t v_isShared_4217_; uint8_t v_isSharedCheck_4221_; 
lean_dec(v___x_4171_);
v_a_4214_ = lean_ctor_get(v___x_4172_, 0);
v_isSharedCheck_4221_ = !lean_is_exclusive(v___x_4172_);
if (v_isSharedCheck_4221_ == 0)
{
v___x_4216_ = v___x_4172_;
v_isShared_4217_ = v_isSharedCheck_4221_;
goto v_resetjp_4215_;
}
else
{
lean_inc(v_a_4214_);
lean_dec(v___x_4172_);
v___x_4216_ = lean_box(0);
v_isShared_4217_ = v_isSharedCheck_4221_;
goto v_resetjp_4215_;
}
v_resetjp_4215_:
{
lean_object* v___x_4219_; 
if (v_isShared_4217_ == 0)
{
v___x_4219_ = v___x_4216_;
goto v_reusejp_4218_;
}
else
{
lean_object* v_reuseFailAlloc_4220_; 
v_reuseFailAlloc_4220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4220_, 0, v_a_4214_);
v___x_4219_ = v_reuseFailAlloc_4220_;
goto v_reusejp_4218_;
}
v_reusejp_4218_:
{
return v___x_4219_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkValueTypeClosure___boxed(lean_object* v_type_4222_, lean_object* v_value_4223_, lean_object* v_zetaDelta_4224_, lean_object* v_a_4225_, lean_object* v_a_4226_, lean_object* v_a_4227_, lean_object* v_a_4228_, lean_object* v_a_4229_){
_start:
{
uint8_t v_zetaDelta_boxed_4230_; lean_object* v_res_4231_; 
v_zetaDelta_boxed_4230_ = lean_unbox(v_zetaDelta_4224_);
v_res_4231_ = l_Lean_Meta_Closure_mkValueTypeClosure(v_type_4222_, v_value_4223_, v_zetaDelta_boxed_4230_, v_a_4225_, v_a_4226_, v_a_4227_, v_a_4228_);
lean_dec(v_a_4228_);
lean_dec_ref(v_a_4227_);
lean_dec(v_a_4226_);
lean_dec_ref(v_a_4225_);
return v_res_4231_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkAuxDefinition_spec__0___redArg(lean_object* v_name_4232_, lean_object* v_levelParams_4233_, lean_object* v_type_4234_, lean_object* v_value_4235_, lean_object* v_hints_4236_, lean_object* v___y_4237_){
_start:
{
lean_object* v___x_4239_; uint8_t v___y_4241_; uint8_t v___y_4248_; lean_object* v_env_4251_; uint8_t v___x_4252_; 
v___x_4239_ = lean_st_ref_get(v___y_4237_);
v_env_4251_ = lean_ctor_get(v___x_4239_, 0);
lean_inc_ref_n(v_env_4251_, 2);
lean_dec(v___x_4239_);
v___x_4252_ = l_Lean_Environment_hasUnsafe(v_env_4251_, v_type_4234_);
if (v___x_4252_ == 0)
{
uint8_t v___x_4253_; 
v___x_4253_ = l_Lean_Environment_hasUnsafe(v_env_4251_, v_value_4235_);
v___y_4248_ = v___x_4253_;
goto v___jp_4247_;
}
else
{
lean_dec_ref(v_env_4251_);
v___y_4248_ = v___x_4252_;
goto v___jp_4247_;
}
v___jp_4240_:
{
lean_object* v___x_4242_; lean_object* v___x_4243_; lean_object* v___x_4244_; lean_object* v___x_4245_; lean_object* v___x_4246_; 
lean_inc(v_name_4232_);
v___x_4242_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4242_, 0, v_name_4232_);
lean_ctor_set(v___x_4242_, 1, v_levelParams_4233_);
lean_ctor_set(v___x_4242_, 2, v_type_4234_);
v___x_4243_ = lean_box(0);
v___x_4244_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4244_, 0, v_name_4232_);
lean_ctor_set(v___x_4244_, 1, v___x_4243_);
v___x_4245_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_4245_, 0, v___x_4242_);
lean_ctor_set(v___x_4245_, 1, v_value_4235_);
lean_ctor_set(v___x_4245_, 2, v_hints_4236_);
lean_ctor_set(v___x_4245_, 3, v___x_4244_);
lean_ctor_set_uint8(v___x_4245_, sizeof(void*)*4, v___y_4241_);
v___x_4246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4246_, 0, v___x_4245_);
return v___x_4246_;
}
v___jp_4247_:
{
if (v___y_4248_ == 0)
{
uint8_t v___x_4249_; 
v___x_4249_ = 1;
v___y_4241_ = v___x_4249_;
goto v___jp_4240_;
}
else
{
uint8_t v___x_4250_; 
v___x_4250_ = 0;
v___y_4241_ = v___x_4250_;
goto v___jp_4240_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkAuxDefinition_spec__0___redArg___boxed(lean_object* v_name_4254_, lean_object* v_levelParams_4255_, lean_object* v_type_4256_, lean_object* v_value_4257_, lean_object* v_hints_4258_, lean_object* v___y_4259_, lean_object* v___y_4260_){
_start:
{
lean_object* v_res_4261_; 
v_res_4261_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkAuxDefinition_spec__0___redArg(v_name_4254_, v_levelParams_4255_, v_type_4256_, v_value_4257_, v_hints_4258_, v___y_4259_);
lean_dec(v___y_4259_);
return v_res_4261_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkAuxDefinition_spec__0(lean_object* v_name_4262_, lean_object* v_levelParams_4263_, lean_object* v_type_4264_, lean_object* v_value_4265_, lean_object* v_hints_4266_, lean_object* v___y_4267_, lean_object* v___y_4268_, lean_object* v___y_4269_, lean_object* v___y_4270_){
_start:
{
lean_object* v___x_4272_; 
v___x_4272_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkAuxDefinition_spec__0___redArg(v_name_4262_, v_levelParams_4263_, v_type_4264_, v_value_4265_, v_hints_4266_, v___y_4270_);
return v___x_4272_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkAuxDefinition_spec__0___boxed(lean_object* v_name_4273_, lean_object* v_levelParams_4274_, lean_object* v_type_4275_, lean_object* v_value_4276_, lean_object* v_hints_4277_, lean_object* v___y_4278_, lean_object* v___y_4279_, lean_object* v___y_4280_, lean_object* v___y_4281_, lean_object* v___y_4282_){
_start:
{
lean_object* v_res_4283_; 
v_res_4283_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkAuxDefinition_spec__0(v_name_4273_, v_levelParams_4274_, v_type_4275_, v_value_4276_, v_hints_4277_, v___y_4278_, v___y_4279_, v___y_4280_, v___y_4281_);
lean_dec(v___y_4281_);
lean_dec_ref(v___y_4280_);
lean_dec(v___y_4279_);
lean_dec_ref(v___y_4278_);
return v_res_4283_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAuxDefinition(lean_object* v_name_4284_, lean_object* v_type_4285_, lean_object* v_value_4286_, uint8_t v_zetaDelta_4287_, uint8_t v_compile_4288_, uint8_t v_logCompileErrors_4289_, lean_object* v_a_4290_, lean_object* v_a_4291_, lean_object* v_a_4292_, lean_object* v_a_4293_){
_start:
{
lean_object* v___x_4295_; 
v___x_4295_ = l_Lean_Meta_Closure_mkValueTypeClosure(v_type_4285_, v_value_4286_, v_zetaDelta_4287_, v_a_4290_, v_a_4291_, v_a_4292_, v_a_4293_);
if (lean_obj_tag(v___x_4295_) == 0)
{
lean_object* v_a_4296_; lean_object* v___x_4298_; uint8_t v_isShared_4299_; uint8_t v_isSharedCheck_4347_; 
v_a_4296_ = lean_ctor_get(v___x_4295_, 0);
v_isSharedCheck_4347_ = !lean_is_exclusive(v___x_4295_);
if (v_isSharedCheck_4347_ == 0)
{
v___x_4298_ = v___x_4295_;
v_isShared_4299_ = v_isSharedCheck_4347_;
goto v_resetjp_4297_;
}
else
{
lean_inc(v_a_4296_);
lean_dec(v___x_4295_);
v___x_4298_ = lean_box(0);
v_isShared_4299_ = v_isSharedCheck_4347_;
goto v_resetjp_4297_;
}
v_resetjp_4297_:
{
lean_object* v___x_4300_; lean_object* v_env_4301_; lean_object* v_levelParams_4302_; lean_object* v_type_4303_; lean_object* v_value_4304_; lean_object* v_levelArgs_4305_; lean_object* v_exprArgs_4306_; uint32_t v___x_4314_; uint32_t v___x_4315_; uint32_t v___x_4316_; lean_object* v___x_4317_; lean_object* v___x_4318_; lean_object* v___x_4319_; lean_object* v_a_4320_; lean_object* v___x_4322_; uint8_t v_isShared_4323_; uint8_t v_isSharedCheck_4346_; 
v___x_4300_ = lean_st_ref_get(v_a_4293_);
v_env_4301_ = lean_ctor_get(v___x_4300_, 0);
lean_inc_ref(v_env_4301_);
lean_dec(v___x_4300_);
v_levelParams_4302_ = lean_ctor_get(v_a_4296_, 0);
lean_inc_ref(v_levelParams_4302_);
v_type_4303_ = lean_ctor_get(v_a_4296_, 1);
lean_inc_ref(v_type_4303_);
v_value_4304_ = lean_ctor_get(v_a_4296_, 2);
lean_inc_ref_n(v_value_4304_, 2);
v_levelArgs_4305_ = lean_ctor_get(v_a_4296_, 3);
lean_inc_ref(v_levelArgs_4305_);
v_exprArgs_4306_ = lean_ctor_get(v_a_4296_, 4);
lean_inc_ref(v_exprArgs_4306_);
lean_dec(v_a_4296_);
v___x_4314_ = l_Lean_getMaxHeight(v_env_4301_, v_value_4304_);
v___x_4315_ = 1;
v___x_4316_ = lean_uint32_add(v___x_4314_, v___x_4315_);
v___x_4317_ = lean_alloc_ctor(2, 0, 4);
lean_ctor_set_uint32(v___x_4317_, 0, v___x_4316_);
v___x_4318_ = lean_array_to_list(v_levelParams_4302_);
lean_inc(v_name_4284_);
v___x_4319_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkAuxDefinition_spec__0___redArg(v_name_4284_, v___x_4318_, v_type_4303_, v_value_4304_, v___x_4317_, v_a_4293_);
v_a_4320_ = lean_ctor_get(v___x_4319_, 0);
v_isSharedCheck_4346_ = !lean_is_exclusive(v___x_4319_);
if (v_isSharedCheck_4346_ == 0)
{
v___x_4322_ = v___x_4319_;
v_isShared_4323_ = v_isSharedCheck_4346_;
goto v_resetjp_4321_;
}
else
{
lean_inc(v_a_4320_);
lean_dec(v___x_4319_);
v___x_4322_ = lean_box(0);
v_isShared_4323_ = v_isSharedCheck_4346_;
goto v_resetjp_4321_;
}
v___jp_4307_:
{
lean_object* v___x_4308_; lean_object* v___x_4309_; lean_object* v___x_4310_; lean_object* v___x_4312_; 
v___x_4308_ = lean_array_to_list(v_levelArgs_4305_);
v___x_4309_ = l_Lean_mkConst(v_name_4284_, v___x_4308_);
v___x_4310_ = l_Lean_mkAppN(v___x_4309_, v_exprArgs_4306_);
lean_dec_ref(v_exprArgs_4306_);
if (v_isShared_4299_ == 0)
{
lean_ctor_set(v___x_4298_, 0, v___x_4310_);
v___x_4312_ = v___x_4298_;
goto v_reusejp_4311_;
}
else
{
lean_object* v_reuseFailAlloc_4313_; 
v_reuseFailAlloc_4313_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4313_, 0, v___x_4310_);
v___x_4312_ = v_reuseFailAlloc_4313_;
goto v_reusejp_4311_;
}
v_reusejp_4311_:
{
return v___x_4312_;
}
}
v_resetjp_4321_:
{
lean_object* v___x_4325_; 
if (v_isShared_4323_ == 0)
{
lean_ctor_set_tag(v___x_4322_, 1);
v___x_4325_ = v___x_4322_;
goto v_reusejp_4324_;
}
else
{
lean_object* v_reuseFailAlloc_4345_; 
v_reuseFailAlloc_4345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4345_, 0, v_a_4320_);
v___x_4325_ = v_reuseFailAlloc_4345_;
goto v_reusejp_4324_;
}
v_reusejp_4324_:
{
uint8_t v___x_4326_; lean_object* v___x_4327_; 
v___x_4326_ = 0;
lean_inc_ref(v___x_4325_);
v___x_4327_ = l_Lean_addDecl(v___x_4325_, v___x_4326_, v_a_4292_, v_a_4293_);
if (lean_obj_tag(v___x_4327_) == 0)
{
lean_dec_ref(v___x_4327_);
if (v_compile_4288_ == 0)
{
lean_dec_ref(v___x_4325_);
goto v___jp_4307_;
}
else
{
lean_object* v___x_4328_; 
v___x_4328_ = l_Lean_compileDecl(v___x_4325_, v_logCompileErrors_4289_, v_a_4292_, v_a_4293_);
if (lean_obj_tag(v___x_4328_) == 0)
{
lean_dec_ref(v___x_4328_);
goto v___jp_4307_;
}
else
{
lean_object* v_a_4329_; lean_object* v___x_4331_; uint8_t v_isShared_4332_; uint8_t v_isSharedCheck_4336_; 
lean_dec_ref(v_exprArgs_4306_);
lean_dec_ref(v_levelArgs_4305_);
lean_del_object(v___x_4298_);
lean_dec(v_name_4284_);
v_a_4329_ = lean_ctor_get(v___x_4328_, 0);
v_isSharedCheck_4336_ = !lean_is_exclusive(v___x_4328_);
if (v_isSharedCheck_4336_ == 0)
{
v___x_4331_ = v___x_4328_;
v_isShared_4332_ = v_isSharedCheck_4336_;
goto v_resetjp_4330_;
}
else
{
lean_inc(v_a_4329_);
lean_dec(v___x_4328_);
v___x_4331_ = lean_box(0);
v_isShared_4332_ = v_isSharedCheck_4336_;
goto v_resetjp_4330_;
}
v_resetjp_4330_:
{
lean_object* v___x_4334_; 
if (v_isShared_4332_ == 0)
{
v___x_4334_ = v___x_4331_;
goto v_reusejp_4333_;
}
else
{
lean_object* v_reuseFailAlloc_4335_; 
v_reuseFailAlloc_4335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4335_, 0, v_a_4329_);
v___x_4334_ = v_reuseFailAlloc_4335_;
goto v_reusejp_4333_;
}
v_reusejp_4333_:
{
return v___x_4334_;
}
}
}
}
}
else
{
lean_object* v_a_4337_; lean_object* v___x_4339_; uint8_t v_isShared_4340_; uint8_t v_isSharedCheck_4344_; 
lean_dec_ref(v___x_4325_);
lean_dec_ref(v_exprArgs_4306_);
lean_dec_ref(v_levelArgs_4305_);
lean_del_object(v___x_4298_);
lean_dec(v_name_4284_);
v_a_4337_ = lean_ctor_get(v___x_4327_, 0);
v_isSharedCheck_4344_ = !lean_is_exclusive(v___x_4327_);
if (v_isSharedCheck_4344_ == 0)
{
v___x_4339_ = v___x_4327_;
v_isShared_4340_ = v_isSharedCheck_4344_;
goto v_resetjp_4338_;
}
else
{
lean_inc(v_a_4337_);
lean_dec(v___x_4327_);
v___x_4339_ = lean_box(0);
v_isShared_4340_ = v_isSharedCheck_4344_;
goto v_resetjp_4338_;
}
v_resetjp_4338_:
{
lean_object* v___x_4342_; 
if (v_isShared_4340_ == 0)
{
v___x_4342_ = v___x_4339_;
goto v_reusejp_4341_;
}
else
{
lean_object* v_reuseFailAlloc_4343_; 
v_reuseFailAlloc_4343_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4343_, 0, v_a_4337_);
v___x_4342_ = v_reuseFailAlloc_4343_;
goto v_reusejp_4341_;
}
v_reusejp_4341_:
{
return v___x_4342_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4348_; lean_object* v___x_4350_; uint8_t v_isShared_4351_; uint8_t v_isSharedCheck_4355_; 
lean_dec(v_name_4284_);
v_a_4348_ = lean_ctor_get(v___x_4295_, 0);
v_isSharedCheck_4355_ = !lean_is_exclusive(v___x_4295_);
if (v_isSharedCheck_4355_ == 0)
{
v___x_4350_ = v___x_4295_;
v_isShared_4351_ = v_isSharedCheck_4355_;
goto v_resetjp_4349_;
}
else
{
lean_inc(v_a_4348_);
lean_dec(v___x_4295_);
v___x_4350_ = lean_box(0);
v_isShared_4351_ = v_isSharedCheck_4355_;
goto v_resetjp_4349_;
}
v_resetjp_4349_:
{
lean_object* v___x_4353_; 
if (v_isShared_4351_ == 0)
{
v___x_4353_ = v___x_4350_;
goto v_reusejp_4352_;
}
else
{
lean_object* v_reuseFailAlloc_4354_; 
v_reuseFailAlloc_4354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4354_, 0, v_a_4348_);
v___x_4353_ = v_reuseFailAlloc_4354_;
goto v_reusejp_4352_;
}
v_reusejp_4352_:
{
return v___x_4353_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAuxDefinition___boxed(lean_object* v_name_4356_, lean_object* v_type_4357_, lean_object* v_value_4358_, lean_object* v_zetaDelta_4359_, lean_object* v_compile_4360_, lean_object* v_logCompileErrors_4361_, lean_object* v_a_4362_, lean_object* v_a_4363_, lean_object* v_a_4364_, lean_object* v_a_4365_, lean_object* v_a_4366_){
_start:
{
uint8_t v_zetaDelta_boxed_4367_; uint8_t v_compile_boxed_4368_; uint8_t v_logCompileErrors_boxed_4369_; lean_object* v_res_4370_; 
v_zetaDelta_boxed_4367_ = lean_unbox(v_zetaDelta_4359_);
v_compile_boxed_4368_ = lean_unbox(v_compile_4360_);
v_logCompileErrors_boxed_4369_ = lean_unbox(v_logCompileErrors_4361_);
v_res_4370_ = l_Lean_Meta_mkAuxDefinition(v_name_4356_, v_type_4357_, v_value_4358_, v_zetaDelta_boxed_4367_, v_compile_boxed_4368_, v_logCompileErrors_boxed_4369_, v_a_4362_, v_a_4363_, v_a_4364_, v_a_4365_);
lean_dec(v_a_4365_);
lean_dec_ref(v_a_4364_);
lean_dec(v_a_4363_);
lean_dec_ref(v_a_4362_);
return v_res_4370_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAuxDefinitionFor(lean_object* v_name_4371_, lean_object* v_value_4372_, uint8_t v_zetaDelta_4373_, uint8_t v_compile_4374_, uint8_t v_logCompileErrors_4375_, lean_object* v_a_4376_, lean_object* v_a_4377_, lean_object* v_a_4378_, lean_object* v_a_4379_){
_start:
{
lean_object* v___x_4381_; 
lean_inc(v_a_4379_);
lean_inc_ref(v_a_4378_);
lean_inc(v_a_4377_);
lean_inc_ref(v_a_4376_);
lean_inc_ref(v_value_4372_);
v___x_4381_ = lean_infer_type(v_value_4372_, v_a_4376_, v_a_4377_, v_a_4378_, v_a_4379_);
if (lean_obj_tag(v___x_4381_) == 0)
{
lean_object* v_a_4382_; lean_object* v___x_4383_; lean_object* v___x_4384_; 
v_a_4382_ = lean_ctor_get(v___x_4381_, 0);
lean_inc(v_a_4382_);
lean_dec_ref(v___x_4381_);
v___x_4383_ = l_Lean_Expr_headBeta(v_a_4382_);
v___x_4384_ = l_Lean_Meta_mkAuxDefinition(v_name_4371_, v___x_4383_, v_value_4372_, v_zetaDelta_4373_, v_compile_4374_, v_logCompileErrors_4375_, v_a_4376_, v_a_4377_, v_a_4378_, v_a_4379_);
return v___x_4384_;
}
else
{
lean_dec_ref(v_value_4372_);
lean_dec(v_name_4371_);
return v___x_4381_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAuxDefinitionFor___boxed(lean_object* v_name_4385_, lean_object* v_value_4386_, lean_object* v_zetaDelta_4387_, lean_object* v_compile_4388_, lean_object* v_logCompileErrors_4389_, lean_object* v_a_4390_, lean_object* v_a_4391_, lean_object* v_a_4392_, lean_object* v_a_4393_, lean_object* v_a_4394_){
_start:
{
uint8_t v_zetaDelta_boxed_4395_; uint8_t v_compile_boxed_4396_; uint8_t v_logCompileErrors_boxed_4397_; lean_object* v_res_4398_; 
v_zetaDelta_boxed_4395_ = lean_unbox(v_zetaDelta_4387_);
v_compile_boxed_4396_ = lean_unbox(v_compile_4388_);
v_logCompileErrors_boxed_4397_ = lean_unbox(v_logCompileErrors_4389_);
v_res_4398_ = l_Lean_Meta_mkAuxDefinitionFor(v_name_4385_, v_value_4386_, v_zetaDelta_boxed_4395_, v_compile_boxed_4396_, v_logCompileErrors_boxed_4397_, v_a_4390_, v_a_4391_, v_a_4392_, v_a_4393_);
lean_dec(v_a_4393_);
lean_dec_ref(v_a_4392_);
lean_dec(v_a_4391_);
lean_dec_ref(v_a_4390_);
return v_res_4398_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAuxTheorem(lean_object* v_type_4399_, lean_object* v_value_4400_, uint8_t v_zetaDelta_4401_, lean_object* v_kind_x3f_4402_, uint8_t v_cache_4403_, lean_object* v_a_4404_, lean_object* v_a_4405_, lean_object* v_a_4406_, lean_object* v_a_4407_){
_start:
{
lean_object* v___x_4409_; 
v___x_4409_ = l_Lean_Meta_Closure_mkValueTypeClosure(v_type_4399_, v_value_4400_, v_zetaDelta_4401_, v_a_4404_, v_a_4405_, v_a_4406_, v_a_4407_);
if (lean_obj_tag(v___x_4409_) == 0)
{
lean_object* v_a_4410_; lean_object* v_levelParams_4411_; lean_object* v_type_4412_; lean_object* v_value_4413_; lean_object* v_levelArgs_4414_; lean_object* v_exprArgs_4415_; lean_object* v___x_4416_; uint8_t v___x_4417_; lean_object* v___x_4418_; 
v_a_4410_ = lean_ctor_get(v___x_4409_, 0);
lean_inc(v_a_4410_);
lean_dec_ref(v___x_4409_);
v_levelParams_4411_ = lean_ctor_get(v_a_4410_, 0);
lean_inc_ref(v_levelParams_4411_);
v_type_4412_ = lean_ctor_get(v_a_4410_, 1);
lean_inc_ref(v_type_4412_);
v_value_4413_ = lean_ctor_get(v_a_4410_, 2);
lean_inc_ref(v_value_4413_);
v_levelArgs_4414_ = lean_ctor_get(v_a_4410_, 3);
lean_inc_ref(v_levelArgs_4414_);
v_exprArgs_4415_ = lean_ctor_get(v_a_4410_, 4);
lean_inc_ref(v_exprArgs_4415_);
lean_dec(v_a_4410_);
v___x_4416_ = lean_array_to_list(v_levelParams_4411_);
v___x_4417_ = 0;
v___x_4418_ = l_Lean_Meta_mkAuxLemma(v___x_4416_, v_type_4412_, v_value_4413_, v_kind_x3f_4402_, v_cache_4403_, v___x_4417_, v___x_4417_, v___x_4417_, v_a_4404_, v_a_4405_, v_a_4406_, v_a_4407_);
if (lean_obj_tag(v___x_4418_) == 0)
{
lean_object* v_a_4419_; lean_object* v___x_4421_; uint8_t v_isShared_4422_; uint8_t v_isSharedCheck_4429_; 
v_a_4419_ = lean_ctor_get(v___x_4418_, 0);
v_isSharedCheck_4429_ = !lean_is_exclusive(v___x_4418_);
if (v_isSharedCheck_4429_ == 0)
{
v___x_4421_ = v___x_4418_;
v_isShared_4422_ = v_isSharedCheck_4429_;
goto v_resetjp_4420_;
}
else
{
lean_inc(v_a_4419_);
lean_dec(v___x_4418_);
v___x_4421_ = lean_box(0);
v_isShared_4422_ = v_isSharedCheck_4429_;
goto v_resetjp_4420_;
}
v_resetjp_4420_:
{
lean_object* v___x_4423_; lean_object* v___x_4424_; lean_object* v___x_4425_; lean_object* v___x_4427_; 
v___x_4423_ = lean_array_to_list(v_levelArgs_4414_);
v___x_4424_ = l_Lean_mkConst(v_a_4419_, v___x_4423_);
v___x_4425_ = l_Lean_mkAppN(v___x_4424_, v_exprArgs_4415_);
lean_dec_ref(v_exprArgs_4415_);
if (v_isShared_4422_ == 0)
{
lean_ctor_set(v___x_4421_, 0, v___x_4425_);
v___x_4427_ = v___x_4421_;
goto v_reusejp_4426_;
}
else
{
lean_object* v_reuseFailAlloc_4428_; 
v_reuseFailAlloc_4428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4428_, 0, v___x_4425_);
v___x_4427_ = v_reuseFailAlloc_4428_;
goto v_reusejp_4426_;
}
v_reusejp_4426_:
{
return v___x_4427_;
}
}
}
else
{
lean_object* v_a_4430_; lean_object* v___x_4432_; uint8_t v_isShared_4433_; uint8_t v_isSharedCheck_4437_; 
lean_dec_ref(v_exprArgs_4415_);
lean_dec_ref(v_levelArgs_4414_);
v_a_4430_ = lean_ctor_get(v___x_4418_, 0);
v_isSharedCheck_4437_ = !lean_is_exclusive(v___x_4418_);
if (v_isSharedCheck_4437_ == 0)
{
v___x_4432_ = v___x_4418_;
v_isShared_4433_ = v_isSharedCheck_4437_;
goto v_resetjp_4431_;
}
else
{
lean_inc(v_a_4430_);
lean_dec(v___x_4418_);
v___x_4432_ = lean_box(0);
v_isShared_4433_ = v_isSharedCheck_4437_;
goto v_resetjp_4431_;
}
v_resetjp_4431_:
{
lean_object* v___x_4435_; 
if (v_isShared_4433_ == 0)
{
v___x_4435_ = v___x_4432_;
goto v_reusejp_4434_;
}
else
{
lean_object* v_reuseFailAlloc_4436_; 
v_reuseFailAlloc_4436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4436_, 0, v_a_4430_);
v___x_4435_ = v_reuseFailAlloc_4436_;
goto v_reusejp_4434_;
}
v_reusejp_4434_:
{
return v___x_4435_;
}
}
}
}
else
{
lean_object* v_a_4438_; lean_object* v___x_4440_; uint8_t v_isShared_4441_; uint8_t v_isSharedCheck_4445_; 
lean_dec(v_kind_x3f_4402_);
v_a_4438_ = lean_ctor_get(v___x_4409_, 0);
v_isSharedCheck_4445_ = !lean_is_exclusive(v___x_4409_);
if (v_isSharedCheck_4445_ == 0)
{
v___x_4440_ = v___x_4409_;
v_isShared_4441_ = v_isSharedCheck_4445_;
goto v_resetjp_4439_;
}
else
{
lean_inc(v_a_4438_);
lean_dec(v___x_4409_);
v___x_4440_ = lean_box(0);
v_isShared_4441_ = v_isSharedCheck_4445_;
goto v_resetjp_4439_;
}
v_resetjp_4439_:
{
lean_object* v___x_4443_; 
if (v_isShared_4441_ == 0)
{
v___x_4443_ = v___x_4440_;
goto v_reusejp_4442_;
}
else
{
lean_object* v_reuseFailAlloc_4444_; 
v_reuseFailAlloc_4444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4444_, 0, v_a_4438_);
v___x_4443_ = v_reuseFailAlloc_4444_;
goto v_reusejp_4442_;
}
v_reusejp_4442_:
{
return v___x_4443_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAuxTheorem___boxed(lean_object* v_type_4446_, lean_object* v_value_4447_, lean_object* v_zetaDelta_4448_, lean_object* v_kind_x3f_4449_, lean_object* v_cache_4450_, lean_object* v_a_4451_, lean_object* v_a_4452_, lean_object* v_a_4453_, lean_object* v_a_4454_, lean_object* v_a_4455_){
_start:
{
uint8_t v_zetaDelta_boxed_4456_; uint8_t v_cache_boxed_4457_; lean_object* v_res_4458_; 
v_zetaDelta_boxed_4456_ = lean_unbox(v_zetaDelta_4448_);
v_cache_boxed_4457_ = lean_unbox(v_cache_4450_);
v_res_4458_ = l_Lean_Meta_mkAuxTheorem(v_type_4446_, v_value_4447_, v_zetaDelta_boxed_4456_, v_kind_x3f_4449_, v_cache_boxed_4457_, v_a_4451_, v_a_4452_, v_a_4453_, v_a_4454_);
lean_dec(v_a_4454_);
lean_dec_ref(v_a_4453_);
lean_dec(v_a_4452_);
lean_dec_ref(v_a_4451_);
return v_res_4458_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_initFn_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4514_; uint8_t v___x_4515_; lean_object* v___x_4516_; lean_object* v___x_4517_; 
v___x_4514_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__10));
v___x_4515_ = 0;
v___x_4516_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2_));
v___x_4517_ = l_Lean_registerTraceClass(v___x_4514_, v___x_4515_, v___x_4516_);
return v___x_4517_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_initFn_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2____boxed(lean_object* v_a_4518_){
_start:
{
lean_object* v_res_4519_; 
v_res_4519_ = l___private_Lean_Meta_Closure_0__Lean_Meta_initFn_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2_();
return v_res_4519_;
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
